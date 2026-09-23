/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Batch8Emit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer

/-!
# Lane-wise 32-bit programs through the scalar front, widened eight ways by `batch8`

Straight-line programs over 32-bit words that apply the same arithmetic to many
independent values, and the lattice-coefficient kernels written as such
programs. A program is a list of statements `dst := a op b` over named 32-bit
slots, written once for one 32-bit lane. It is lowered by the width-32 scalar
front: the statement sequencer `ScalarSetSeqSequencer.seqProg` builds the
`Com catCryptDialect`, and `DialectToJasminCom.cryptoDialectToJasminCom` lowers it
to `Com jasminDialect`. `batch8` (`Optimizer.Batch8`) widens every op of that
program to the packed YMM op computing it on eight lanes, and
`batch8ToLprogPhysAbi` takes the result through the owned backend. Correctness of
the widening is `Batch8.batch8_denote`, which holds for every program in the
covered fragment; `laneCom_covered` places every lane program there.

The input context is `List.replicate (m + 1) (.sword 32)`. Input `i ≤ m` is the
slot named `inName i`, at context position `i`, so it sits at argument slot
`m - i` of the exported function. The names `inName 0 … inName (m - 1)` are bound
explicitly and every other name reads input `m`. Results are read by the export's
last-`N` convention: the final `N` bindings are stored, in binding order, to the
targets of the `OutStoreMap`. Every statement lowers to exactly one binding.

A 256-bit constant is not an immediate operand, and the export lowers
`regConst` to a move of an immediate, so constants enter as inputs loaded from a
table of pre-broadcast words at a second pointer.

## Main definitions

* `LStmt`, `laneProg`, `laneCom`: lane statements and their front lowering.
* `laneCom_covered`: every lane program is in `batch8`'s covered fragment.
* `polyAddCom`, `polySubCom`, `polyReduceCom`, `polyCaddqCom`: the ML-DSA
  coefficient kernels over `groups` YMM words of eight coefficients each.
* `polyDecomposeCom`, `polyMakeHintCom`, `polyChknormCom`, `polyUseHintCom`: the
  signing decisions, branch-free.
* `laneAsm`, `polyAsm`: the owned AT&T text of one kernel.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneWiseEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer
open CatCrypt.Crypto.Jasmin.LowCT (SExpr)
open CatCrypt.Crypto.Optimizer.Batch8 (Batch8Covered CoveredExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (InLoadMap OutStoreMap)
open CatCrypt.Crypto.Optimizer.Batch8Emit (batch8ToLprogPhysAbi)

/-! ## 1. Lane statements -/

/-- A binary word operation of a lane statement. -/
inductive LBin where
  | add | sub | mul | and | xor
  deriving Repr

/-- One statement of a lane program: a single 32-bit word operation whose
    operands are named slots. -/
inductive LStmt where
  /-- `dst := a op b`. -/
  | bin (op : LBin) (dst a b : String)
  /-- `dst := a >>> k`, the logical shift right by the immediate `k`. -/
  | shr (dst a : String) (k : Nat)
  /-- `dst := a >>ₛ k`, the arithmetic shift right by the immediate `k`. -/
  | sar (dst a : String) (k : Nat)
  deriving Repr

/-- The slot a statement writes. -/
def LStmt.dst : LStmt → String
  | .bin _ d _ _ => d
  | .shr d _ _ => d
  | .sar d _ _ => d

/-- The front expression a statement computes. -/
def LStmt.rhs : LStmt → SExpr
  | .bin .add _ a b => .SAdd (.SVar a) (.SVar b)
  | .bin .sub _ a b => .SSub (.SVar a) (.SVar b)
  | .bin .mul _ a b => .SMul (.SVar a) (.SVar b)
  | .bin .and _ a b => .SAnd (.SVar a) (.SVar b)
  | .bin .xor _ a b => .SXor (.SVar a) (.SVar b)
  | .shr _ a k => .SShr (.SVar a) (.SLit k)
  | .sar _ a k => .SAsr (.SVar a) (.SLit k)

/-- A statement as an entry of the sequencer's statement list. -/
def LStmt.toFront (s : LStmt) : String × SExpr := (s.dst, s.rhs)

/-- `dst := a | b`, as `(a ^ b) ^ (a & b)` through the slots `dst ++ "^"` and
    `dst ++ "&"` (`or_eq_xor_xor_and`). -/
def orStmts (dst a b : String) : List LStmt :=
  [.bin .xor (dst ++ "^") a b, .bin .and (dst ++ "&") a b,
   .bin .xor dst (dst ++ "^") (dst ++ "&")]

/-- `dst := ~a & b`, as `b ^ (a & b)` through the slot `dst ++ "&"`
    (`andn_eq_xor_and`). -/
def andnStmts (dst a b : String) : List LStmt :=
  [.bin .and (dst ++ "&") a b, .bin .xor dst b (dst ++ "&")]

theorem or_eq_xor_xor_and (a b : BitVec 32) : a ||| b = (a ^^^ b) ^^^ (a &&& b) := by
  ext i; simp; cases a[i] <;> cases b[i] <;> rfl

theorem andn_eq_xor_and (a b : BitVec 32) : ~~~a &&& b = b ^^^ (a &&& b) := by
  ext i; simp; cases a[i] <;> cases b[i] <;> rfl

/-! ## 2. The front lowering -/

/-- `n` 32-bit input slots. -/
abbrev laneΓ (n : Nat) : Ctx := List.replicate n (.sword 32)

/-- The name of input `i`. -/
def inName (i : Nat) : String := s!"x{i}"

/-- The input names over `m + 1` slots: `inName (base + j)` is slot `j` for
    `j < m`, and every other name is the last slot. -/
def laneVM : (m : Nat) → Nat → VarMap (laneΓ (m + 1))
  | 0, _ => { lookup := fun _ => some ⟨.sword 32, .here⟩ }
  | m + 1, base => VarMap.bind (t := .sword 32) (laneVM m (base + 1)) (inName base)

/-- The front lowering of a lane program over `m + 1` inputs returning the slot
    `fin`: the sequencer's `Com catCryptDialect`, lowered to `Com jasminDialect`. -/
def laneProg (m : Nat) (stmts : List LStmt) (fin : String) :=
  (seqProg 32 (laneVM m 0) (stmts.map LStmt.toFront) fin).bind
    DialectToJasminCom.cryptoDialectToJasminCom

/-! ## 3. Every lane program lowers into `batch8`'s covered fragment

The input names are total (`laneVM_total`): every name reads a 32-bit slot. Each
statement lowers to one binding of an op whose jasmin lowering is covered
(`stmt_lower`), and totality is kept by the binding and by the sequencer's
alias. The whole program then lowers and is covered, by induction over the
statement list (`seq_lower`) and over the `Com` (`ComB8.lower`), for every
statement list. -/

/-- Every name is bound to a 32-bit slot. -/
def Total32 {Γ : Ctx} (vm : VarMap Γ) : Prop :=
  ∀ n, ∃ v, vm.lookup n = some ⟨.sword 32, v⟩

theorem Total32.bind {Γ : Ctx} {vm : VarMap Γ} (h : Total32 vm) (nm : String) :
    Total32 (VarMap.bind (t := .sword 32) vm nm) := by
  intro n
  unfold VarMap.bind
  by_cases hn : n = nm
  · exact ⟨.here, by simp [hn]⟩
  · obtain ⟨v, hv⟩ := h n
    exact ⟨v.there, by simp [hn, hv]⟩

theorem laneVM_total : ∀ (m base : Nat), Total32 (laneVM m base)
  | 0, _ => fun _ => ⟨_, rfl⟩
  | m + 1, base => (laneVM_total m (base + 1)).bind _

theorem Total32.alias {Γ : Ctx} {vm : VarMap Γ} (h : Total32 vm) (dst src : String) :
    Total32 (aliasBind vm dst src) := by
  intro n
  unfold aliasBind
  by_cases hn : n = dst
  · simpa [hn] using h src
  · simpa [hn] using h n

theorem Total32.lookupUW {Γ : Ctx} {vm : VarMap Γ} (h : Total32 vm) (n : String) :
    ∃ v, Dialects.ScalarSExprWidth32Prototype.lookupUW 32 vm n = some v := by
  obtain ⟨v, hv⟩ := h n
  exact ⟨v, by simp [Dialects.ScalarSExprWidth32Prototype.lookupUW, hv]⟩

/-- Every node lowers to a jasmin expression in `batch8`'s covered fragment. -/
inductive ComB8 : {Γ : Ctx} → {t : CryptoTy} → Com catCryptDialect Γ t → Prop where
  | ret {Γ : Ctx} {t : CryptoTy} (v : Ctxt.Var Γ t) : ComB8 (Com.ret v)
  | var {Γ : Ctx} {t s : CryptoTy} (e : Expr catCryptDialect Γ t)
      (body : Com catCryptDialect (t :: Γ) s)
      (he : ∃ e', DialectToJasminCom.toJExprD e = some e' ∧ CoveredExpr e')
      (hb : ComB8 body) : ComB8 (Com.var e body)

/-- A `ComB8` program lowers to a `batch8`-covered jasmin program. -/
theorem ComB8.lower {Γ : Ctx} {t : CryptoTy} {com : Com catCryptDialect Γ t} (h : ComB8 com) :
    ∃ c, DialectToJasminCom.cryptoDialectToJasminCom com = some c ∧ Batch8Covered c := by
  induction h with
  | ret v => exact ⟨_, rfl, trivial⟩
  | var e body he hb ih =>
      obtain ⟨e', he', hc⟩ := he
      obtain ⟨b', hb', hbc⟩ := ih
      refine ⟨.var e' b', ?_, hc, hbc⟩
      unfold DialectToJasminCom.cryptoDialectToJasminCom
      rw [he', hb']

/-- A prefix that sends every `ComB8` body to a `ComB8` program. -/
def ContB8 {Γ Γ' : Ctx} (f : ComCont Γ Γ') : Prop :=
  ∀ {t : CryptoTy} (body : Com catCryptDialect Γ' t),
    ComB8 body → ∃ com, f body = some com ∧ ComB8 com

theorem ContB8.id {Γ : Ctx} : ContB8 (ComCont.id (Γ := Γ)) :=
  fun body hb => ⟨body, rfl, hb⟩

theorem ContB8.varBind {Γ : Ctx} {s : CryptoTy} (e : Expr catCryptDialect Γ s)
    (he : ∃ e', DialectToJasminCom.toJExprD e = some e' ∧ CoveredExpr e') :
    ContB8 (ComCont.varBind e) :=
  fun body hb => ⟨Com.var e body, rfl, ComB8.var e body he hb⟩

theorem ContB8.comp {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    (hf : ContB8 f) (hg : ContB8 g) : ContB8 (ComCont.comp f g) := by
  intro t body hb
  obtain ⟨b', hb', hlb'⟩ := hg body hb
  obtain ⟨c', hc', hlc'⟩ := hf b' hlb'
  refine ⟨c', ?_, hlc'⟩
  show ComCont.comp f g body = some c'
  unfold ComCont.comp
  rw [hb']; exact hc'

/-- One statement lowers, over total names, to a covered prefix, and leaves the
    names total. -/
theorem stmt_lower (s : LStmt) {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) (hv : Total32 vm) :
    ∃ r resName cnt', Dialects.ScalarSExprWidth32Prototype.lowerSExprW 32 vm cnt s.rhs =
      some (r, resName, cnt') ∧ Total32 r.vm ∧ ContB8 r.cont := by
  cases s with
  | bin op dst a b =>
      obtain ⟨va, ha⟩ := hv.lookupUW a
      obtain ⟨vb, hb⟩ := hv.lookupUW b
      cases op <;>
      · simp only [LStmt.rhs, Dialects.ScalarSExprWidth32Prototype.lowerSExprW, ha, hb]
        exact ⟨_, _, _, rfl, hv.bind _,
          ContB8.comp (ContB8.comp ContB8.id ContB8.id)
            (ContB8.varBind _ (by exact ⟨_, rfl, rfl⟩))⟩
  | shr dst a k =>
      obtain ⟨va, ha⟩ := hv.lookupUW a
      simp only [LStmt.rhs, Dialects.ScalarSExprWidth32Prototype.lowerSExprW, ha]
      exact ⟨_, _, _, rfl, hv.bind _,
        ContB8.comp ContB8.id (ContB8.varBind _ (by exact ⟨_, rfl, rfl⟩))⟩
  | sar dst a k =>
      obtain ⟨va, ha⟩ := hv.lookupUW a
      simp only [LStmt.rhs, Dialects.ScalarSExprWidth32Prototype.lowerSExprW, ha]
      exact ⟨_, _, _, rfl, hv.bind _,
        ContB8.comp ContB8.id (ContB8.varBind _ (by exact ⟨_, rfl, rfl⟩))⟩

/-- A statement list lowers through the sequencer, over total names, to a
    covered prefix. -/
theorem seq_lower (stmts : List LStmt) : ∀ {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat), Total32 vm →
    ∃ out cntf, lowerScalarSetSeqW 32 vm cnt (stmts.map LStmt.toFront) = some (out, cntf) ∧
      Total32 out.vm ∧ ContB8 out.cont := by
  induction stmts with
  | nil => intro Γ vm cnt hv; exact ⟨_, _, rfl, hv, ContB8.id⟩
  | cons s rest ih =>
      intro Γ vm cnt hv
      obtain ⟨r, resName, cnt', hhead, hrv, hrc⟩ := stmt_lower s vm cnt hv
      obtain ⟨tail, cntf, htl, htv, htc⟩ := ih (aliasBind r.vm s.dst resName) cnt' (hrv.alias _ _)
      refine ⟨Dialects.TranslateDialectDirectArms.seqOut
        { r with vm := aliasBind r.vm s.dst resName } tail, cntf, ?_, htv, ContB8.comp hrc htc⟩
      simp only [List.map, LStmt.toFront]
      unfold lowerScalarSetSeqW
      rw [hhead]
      dsimp only []
      rw [htl]

theorem seqProg_lane (m : Nat) (stmts : List LStmt) (fin : String) :
    ∃ com, seqProg 32 (laneVM m 0) (stmts.map LStmt.toFront) fin = some com ∧ ComB8 com := by
  obtain ⟨out, cntf, hlo, hv, hc⟩ := seq_lower stmts (laneVM m 0) 0 (laneVM_total m 0)
  obtain ⟨v, hfin⟩ := hv fin
  obtain ⟨com, hcom, hb⟩ := hc (Com.ret (toVIRVar v)) (ComB8.ret _)
  refine ⟨com, ?_, hb⟩
  unfold seqProg
  rw [hlo]
  dsimp only []
  rw [hfin]
  simpa using hcom

/-- **Every lane program lowers, and its lowering is covered by `batch8`**, for
    every statement list, number of inputs and returned slot. -/
theorem laneProg_covered (m : Nat) (stmts : List LStmt) (fin : String) :
    ∃ c, laneProg m stmts fin = some c ∧ Batch8Covered c := by
  obtain ⟨com, h1, h2⟩ := seqProg_lane m stmts fin
  obtain ⟨c, h3, h4⟩ := h2.lower
  exact ⟨c, by simp [laneProg, h1, h3], h4⟩

theorem laneProg_isSome (m : Nat) (stmts : List LStmt) (fin : String) :
    (laneProg m stmts fin).isSome := by
  obtain ⟨c, h, -⟩ := laneProg_covered m stmts fin
  rw [h]; rfl

/-- The front-generated jasmin program of a lane program. -/
def laneCom (m : Nat) (stmts : List LStmt) (fin : String) :
    Com jasminDialect (CryptoToJasminCom.mapCtx (laneΓ (m + 1))) (.reg 32) :=
  (laneProg m stmts fin).get (laneProg_isSome m stmts fin)

/-- **Every lane program is in `batch8`'s covered fragment**, so
    `Batch8.batch8_denote` applies to it. -/
theorem laneCom_covered (m : Nat) (stmts : List LStmt) (fin : String) :
    Batch8Covered (laneCom m stmts fin) := by
  obtain ⟨c, h, hc⟩ := laneProg_covered m stmts fin
  have : laneCom m stmts fin = c := Option.get_of_mem _ h
  rw [this]; exact hc

/-! ## 4. ML-DSA coefficient kernels

Each kernel works on `groups` YMM words of eight 32-bit coefficients. Results
are the slots `outSlot g`; the kernels whose result needs intermediate steps
compute every intermediate first and the results last, so the final `groups`
bindings are the results in group order. -/

/-- FIPS 204 modulus. -/
def dsaQ : Nat := 8380417

/-- ML-DSA-65 `γ₂ = (Q - 1) / 32`. -/
def dsaGamma2 : Nat := 261888

/-- The result slot of group `g`. -/
def outSlot (g : Nat) : String := s!"r{g}"

/-- The `k`-th intermediate slot of group `g`. -/
def tmpSlot (k g : Nat) : String := s!"t{k}_{g}"

/-- The statements `f g` for each group `g < groups`, in group order. -/
def perGroup (groups : Nat) (f : Nat → List LStmt) : List LStmt :=
  (List.range groups).flatMap f

/-- `a[i] := a[i] + b[i]`: inputs `0 .. groups-1` are `a` and the next `groups`
    are `b`. Input `2·groups` is unused. -/
def polyAddStmts (groups : Nat) : List LStmt :=
  perGroup groups fun g => [.bin .add (outSlot g) (inName g) (inName (groups + g))]

/-- `a[i] := a[i] - b[i]`, with the input layout of `polyAddStmts`. -/
def polySubStmts (groups : Nat) : List LStmt :=
  perGroup groups fun g => [.bin .sub (outSlot g) (inName g) (inName (groups + g))]

/-- PQClean `reduce32`: `t := (a + 2²²) >>ₛ 23; a := a - t·Q`. Inputs `0 ..
    groups-1` are `a`; input `groups` is `2²²` and input `groups + 1` is `Q`,
    each broadcast. -/
def polyReduceStmts (groups : Nat) : List LStmt :=
  let c22 := inName groups
  let cq := inName (groups + 1)
  perGroup groups (fun g =>
    [.bin .add (tmpSlot 0 g) (inName g) c22,
     .sar (tmpSlot 1 g) (tmpSlot 0 g) 23,
     .bin .mul (tmpSlot 2 g) (tmpSlot 1 g) cq]) ++
  perGroup groups (fun g => [.bin .sub (outSlot g) (inName g) (tmpSlot 2 g)])

/-- PQClean `caddq`: `a := a + ((a >>ₛ 31) & Q)`. Input `groups` is `Q`. -/
def polyCaddqStmts (groups : Nat) : List LStmt :=
  let cq := inName groups
  perGroup groups (fun g =>
    [.sar (tmpSlot 0 g) (inName g) 31, .bin .and (tmpSlot 1 g) (tmpSlot 0 g) cq]) ++
  perGroup groups (fun g => [.bin .add (outSlot g) (inName g) (tmpSlot 1 g)])

/-- The front-generated `a[i] + b[i]` program. -/
def polyAddCom (groups : Nat) := laneCom (2 * groups) (polyAddStmts groups) (outSlot (groups - 1))

/-- The front-generated `a[i] - b[i]` program. -/
def polySubCom (groups : Nat) := laneCom (2 * groups) (polySubStmts groups) (outSlot (groups - 1))

/-- The front-generated `reduce32` program. -/
def polyReduceCom (groups : Nat) :=
  laneCom (groups + 1) (polyReduceStmts groups) (outSlot (groups - 1))

/-- The front-generated `caddq` program. -/
def polyCaddqCom (groups : Nat) := laneCom groups (polyCaddqStmts groups) (outSlot (groups - 1))

/-! ### Rounding and norm checks

The three signing decisions, written without branches: every comparison is the
sign bit of a difference, taken by a logical shift right by 31. -/

/-- PQClean `decompose` for `γ₂ = (Q - 1) / 32`, on `a ∈ [0, Q)`:
    `a₁ := ((((a + 127) >>ₛ 7) · 1025 + 2²¹) >>ₛ 22) & 15` and
    `a₀ := a - 2γ₂·a₁`, less `Q` when `a₀ > (Q - 1) / 2`.
    Inputs `0 .. groups-1` are `a`; inputs `groups .. groups+6` are the broadcast
    constants `127, 1025, 2²¹, 15, 2γ₂, (Q - 1) / 2, Q`. The final `2·groups`
    bindings are `a₁` of each group and then `a₀` of each group. -/
def polyDecomposeStmts (groups : Nat) : List LStmt :=
  let c127 := inName groups
  let c1025 := inName (groups + 1)
  let c21 := inName (groups + 2)
  let c15 := inName (groups + 3)
  let c2g2 := inName (groups + 4)
  let chalf := inName (groups + 5)
  let cq := inName (groups + 6)
  perGroup groups (fun g =>
    [.bin .add (tmpSlot 0 g) (inName g) c127,
     .sar (tmpSlot 1 g) (tmpSlot 0 g) 7,
     .bin .mul (tmpSlot 2 g) (tmpSlot 1 g) c1025,
     .bin .add (tmpSlot 3 g) (tmpSlot 2 g) c21,
     .sar (tmpSlot 4 g) (tmpSlot 3 g) 22,
     .bin .and (tmpSlot 5 g) (tmpSlot 4 g) c15,
     .bin .mul (tmpSlot 6 g) (tmpSlot 5 g) c2g2,
     .bin .sub (tmpSlot 7 g) (inName g) (tmpSlot 6 g),
     .bin .sub (tmpSlot 8 g) chalf (tmpSlot 7 g),
     .sar (tmpSlot 9 g) (tmpSlot 8 g) 31,
     .bin .and (tmpSlot 10 g) (tmpSlot 9 g) cq]) ++
  perGroup groups (fun g => [.bin .and (outSlot g) (tmpSlot 4 g) c15]) ++
  perGroup groups (fun g => [.bin .sub (outSlot (groups + g)) (tmpSlot 7 g) (tmpSlot 10 g)])

/-- PQClean `make_hint`: `h := 1` when `a₀ > γ₂`, `a₀ < -γ₂`, or `a₀ = -γ₂`
    and `a₁ ≠ 0`; else `0`. With `y := a₀ + γ₂`, the three tests are the sign
    bits of `γ₂ - a₀` and of `y`, and `¬(y ≠ 0) ∧ a₁ ≠ 0`, where `x ≠ 0` is the
    sign bit of `x | (0 - x)`. Every `|` is `orStmts` and the and-not is
    `andnStmts`; the two slots of the final `|` of each group are computed with
    the intermediates, so the final `groups` bindings are the hints. Inputs `0 ..
    groups-1` are `a₀`, the next `groups` are `a₁`, and inputs `2·groups`,
    `2·groups + 1` are the broadcast constants `γ₂` and `0`. -/
def polyMakeHintStmts (groups : Nat) : List LStmt :=
  let cg2 := inName (2 * groups)
  let c0 := inName (2 * groups + 1)
  perGroup groups (fun g =>
    [.bin .sub (tmpSlot 0 g) cg2 (inName g),
     .shr (tmpSlot 1 g) (tmpSlot 0 g) 31,
     .bin .add (tmpSlot 2 g) (inName g) cg2,
     .shr (tmpSlot 3 g) (tmpSlot 2 g) 31,
     .bin .sub (tmpSlot 4 g) c0 (tmpSlot 2 g)] ++
    orStmts (tmpSlot 5 g) (tmpSlot 2 g) (tmpSlot 4 g) ++
    [.shr (tmpSlot 6 g) (tmpSlot 5 g) 31,
     .bin .sub (tmpSlot 7 g) c0 (inName (groups + g))] ++
    orStmts (tmpSlot 8 g) (inName (groups + g)) (tmpSlot 7 g) ++
    [.shr (tmpSlot 9 g) (tmpSlot 8 g) 31] ++
    andnStmts (tmpSlot 10 g) (tmpSlot 6 g) (tmpSlot 9 g) ++
    orStmts (tmpSlot 11 g) (tmpSlot 1 g) (tmpSlot 3 g) ++
    [.bin .xor (outSlot g ++ "^") (tmpSlot 11 g) (tmpSlot 10 g),
     .bin .and (outSlot g ++ "&") (tmpSlot 11 g) (tmpSlot 10 g)]) ++
  perGroup groups (fun g => [.bin .xor (outSlot g) (outSlot g ++ "^") (outSlot g ++ "&")])

/-- PQClean `poly_chknorm` over `groups` words, accumulated: with
    `|a| := a - ((a >>ₛ 31) & 2a)`, the flag `|a| ≥ B` is the sign bit of
    `(B - 1) - |a|`, and the result is the accumulator or-ed (`orStmts`) with
    every flag. Inputs `0 .. groups-1` are `a`, input `groups` is the accumulator
    and input `groups + 1` is the broadcast `B - 1`. The final binding is the new
    accumulator; a lane is nonzero exactly when some coefficient it saw has
    `|a| ≥ B`. -/
def polyChknormStmts (groups : Nat) : List LStmt :=
  let cacc := inName groups
  let cb := inName (groups + 1)
  perGroup groups (fun g =>
    [.sar (tmpSlot 0 g) (inName g) 31,
     .bin .add (tmpSlot 1 g) (inName g) (inName g),
     .bin .and (tmpSlot 2 g) (tmpSlot 0 g) (tmpSlot 1 g),
     .bin .sub (tmpSlot 3 g) (inName g) (tmpSlot 2 g),
     .bin .sub (tmpSlot 4 g) cb (tmpSlot 3 g),
     .shr (tmpSlot 5 g) (tmpSlot 4 g) 31]) ++
  perGroup groups (fun g =>
    orStmts (outSlot 0) (if g = 0 then cacc else outSlot 0) (tmpSlot 5 g))

/-- PQClean `use_hint`: `a₁` of `decompose a`, moved one step when the hint is
    set — up when `a₀ > 0` and down otherwise — and reduced mod 16. The step is
    `1 + 2·((a₀ - 1) >>ₛ 31)`, which is `1` when `a₀ > 0` and `-1` when
    `a₀ ≤ 0`, multiplied by the hint. Inputs `0 .. groups-1` are `a`, the next
    `groups` are the hints, each `0` or `1`, and inputs `2·groups .. 2·groups+7` are the
    broadcast constants `127, 1025, 2²¹, 15, 2γ₂, (Q - 1) / 2, Q, 1`. The final
    `groups` bindings are the corrected `a₁` of each group. -/
def polyUseHintStmts (groups : Nat) : List LStmt :=
  let c127 := inName (2 * groups)
  let c1025 := inName (2 * groups + 1)
  let c21 := inName (2 * groups + 2)
  let c15 := inName (2 * groups + 3)
  let c2g2 := inName (2 * groups + 4)
  let chalf := inName (2 * groups + 5)
  let cq := inName (2 * groups + 6)
  let c1 := inName (2 * groups + 7)
  perGroup groups (fun g =>
    [.bin .add (tmpSlot 0 g) (inName g) c127,
     .sar (tmpSlot 1 g) (tmpSlot 0 g) 7,
     .bin .mul (tmpSlot 2 g) (tmpSlot 1 g) c1025,
     .bin .add (tmpSlot 3 g) (tmpSlot 2 g) c21,
     .sar (tmpSlot 4 g) (tmpSlot 3 g) 22,
     .bin .and (tmpSlot 5 g) (tmpSlot 4 g) c15,
     .bin .mul (tmpSlot 6 g) (tmpSlot 5 g) c2g2,
     .bin .sub (tmpSlot 7 g) (inName g) (tmpSlot 6 g),
     .bin .sub (tmpSlot 8 g) chalf (tmpSlot 7 g),
     .sar (tmpSlot 9 g) (tmpSlot 8 g) 31,
     .bin .and (tmpSlot 10 g) (tmpSlot 9 g) cq,
     .bin .sub (tmpSlot 11 g) (tmpSlot 7 g) (tmpSlot 10 g),
     .bin .sub (tmpSlot 12 g) (tmpSlot 11 g) c1,
     .sar (tmpSlot 13 g) (tmpSlot 12 g) 31,
     .bin .add (tmpSlot 14 g) (tmpSlot 13 g) (tmpSlot 13 g),
     .bin .add (tmpSlot 15 g) c1 (tmpSlot 14 g),
     .bin .mul (tmpSlot 16 g) (tmpSlot 15 g) (inName (groups + g)),
     .bin .add (tmpSlot 17 g) (tmpSlot 5 g) (tmpSlot 16 g)]) ++
  perGroup groups (fun g => [.bin .and (outSlot g) (tmpSlot 17 g) c15])

/-- The front-generated `decompose` program. -/
def polyDecomposeCom (groups : Nat) :=
  laneCom (groups + 6) (polyDecomposeStmts groups) (outSlot (2 * groups - 1))

/-- The front-generated `make_hint` program. -/
def polyMakeHintCom (groups : Nat) :=
  laneCom (2 * groups + 1) (polyMakeHintStmts groups) (outSlot (groups - 1))

/-- The front-generated `chknorm` program. -/
def polyChknormCom (groups : Nat) :=
  laneCom (groups + 1) (polyChknormStmts groups) (outSlot 0)

/-- The front-generated `use_hint` program. -/
def polyUseHintCom (groups : Nat) :=
  laneCom (2 * groups + 7) (polyUseHintStmts groups) (outSlot (groups - 1))

/-- **Coefficient add is covered**, for every number of groups. -/
theorem polyAdd_covered (groups : Nat) : Batch8Covered (polyAddCom groups) :=
  laneCom_covered _ _ _

/-- **Coefficient subtract is covered**, for every number of groups. -/
theorem polySub_covered (groups : Nat) : Batch8Covered (polySubCom groups) :=
  laneCom_covered _ _ _

/-- **`reduce32` is covered**, for every number of groups. -/
theorem polyReduce_covered (groups : Nat) : Batch8Covered (polyReduceCom groups) :=
  laneCom_covered _ _ _

/-- **`caddq` is covered**, for every number of groups. -/
theorem polyCaddq_covered (groups : Nat) : Batch8Covered (polyCaddqCom groups) :=
  laneCom_covered _ _ _

/-- **`decompose` is covered**, for every number of groups. -/
theorem polyDecompose_covered (groups : Nat) : Batch8Covered (polyDecomposeCom groups) :=
  laneCom_covered _ _ _

/-- **`make_hint` is covered**, for every number of groups. -/
theorem polyMakeHint_covered (groups : Nat) : Batch8Covered (polyMakeHintCom groups) :=
  laneCom_covered _ _ _

/-- **`chknorm` is covered**, for every number of groups. -/
theorem polyChknorm_covered (groups : Nat) : Batch8Covered (polyChknormCom groups) :=
  laneCom_covered _ _ _

/-- **`use_hint` is covered**, for every number of groups. -/
theorem polyUseHint_covered (groups : Nat) : Batch8Covered (polyUseHintCom groups) :=
  laneCom_covered _ _ _

/-! ## 5. ABI maps and the owned render

`RDI` points at the 256 coefficients, read and written in place; `RSI` points at
the second operand (add, sub) or at the pre-broadcast constant table (reduce,
caddq). Every YMM word is 32 bytes. -/

/-- Load map for a two-array kernel over `groups` words, whose context has
    `2·groups + 1` inputs: input `i < groups` from `RDI`, input `groups + j` from
    `RSI`, and the unused last input not loaded. -/
def twoArrayIn (groups : Nat) : InLoadMap := fun slot =>
  let i := 2 * groups - slot
  if i < groups then some ("RDI", 32 * i)
  else if i < 2 * groups then some ("RSI", 32 * (i - groups))
  else none

/-- Load map for a one-array kernel with `nConst` broadcast constants. -/
def oneArrayIn (groups nConst : Nat) : InLoadMap := fun slot =>
  let i := groups + nConst - 1 - slot
  if i < groups then some ("RDI", 32 * i) else some ("RSI", 32 * (i - groups))

/-- The results, group `g` to `RDI + 32·g`. -/
def storeOut (groups : Nat) : OutStoreMap := (List.range groups).map (fun g => ("RDI", 32 * g))

/-- Load map for `make_hint`, whose context has `2·groups + 2` inputs: `a₀` from
    `RDI`, `a₁` from `RDI + 32·groups`, and the two constants from `RSI`. -/
def hintIn (groups : Nat) : InLoadMap := fun slot =>
  let i := 2 * groups + 1 - slot
  if i < 2 * groups then some ("RDI", 32 * i) else some ("RSI", 32 * (i - 2 * groups))

/-- Load map for `use_hint`, whose context has `2·groups + 8` inputs: `a` from
    `RDI`, the hints from `RDI + 32·groups`, and the eight constants from
    `RSI`. -/
def useHintIn (groups : Nat) : InLoadMap := fun slot =>
  let i := 2 * groups + 7 - slot
  if i < 2 * groups then some ("RDI", 32 * i) else some ("RSI", 32 * (i - 2 * groups))

/-- Load map for `chknorm`, whose context has `groups + 2` inputs: the
    coefficients from `RSI`, the accumulator from `RDI` and `B - 1` from
    `RDI + 32`. -/
def chknormIn (groups : Nat) : InLoadMap := fun slot =>
  let i := groups + 1 - slot
  if i < groups then some ("RSI", 32 * i) else some ("RDI", 32 * (i - groups))

/-- The `decompose` results: `a₁` of group `g` to `RDI + 32·g` and `a₀` of
    group `g` to `RDI + 32·(groups + g)`. -/
def decomposeOut (groups : Nat) : OutStoreMap :=
  storeOut groups ++ (List.range groups).map (fun g => ("RDI", 32 * (groups + g)))

/-- The owned AT&T text of a widened lane-wise program with the store map `out`. -/
def laneAsm {Γ : Ctxt jasminDialect} (com : Com jasminDialect Γ (.reg 32)) (name : String)
    (inMap : InLoadMap) (out : OutStoreMap) : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwnedReserveVecScratch
    (batch8ToLprogPhysAbi com name (fun _ => none) (fun _ => none) inMap out (abiW := 256))

/-- The owned AT&T text of a widened lane-wise program storing `groups` words
    in place at `RDI`. -/
def polyAsm {Γ : Ctxt jasminDialect} (com : Com jasminDialect Γ (.reg 32)) (name : String)
    (inMap : InLoadMap) (groups : Nat) : String :=
  laneAsm com name inMap (storeOut groups)

/-- YMM words per call: 4 words are 32 coefficients, and a polynomial is 8 calls.
    The export loads every input in the prologue and stores every result in the
    epilogue, so a call keeps its inputs and results live at once; four words
    keep that under the fifteen allocatable vector registers. -/
def dsaGroups : Nat := 4

/-- The eight kernels, with their symbol names. -/
def dsaPolyKernels : List (String × String) :=
  [ ("mldsa_poly_add_x8", polyAsm (polyAddCom dsaGroups) "mldsa_poly_add_x8"
        (twoArrayIn dsaGroups) dsaGroups)
  , ("mldsa_poly_sub_x8", polyAsm (polySubCom dsaGroups) "mldsa_poly_sub_x8"
        (twoArrayIn dsaGroups) dsaGroups)
  , ("mldsa_poly_reduce_x8", polyAsm (polyReduceCom dsaGroups) "mldsa_poly_reduce_x8"
        (oneArrayIn dsaGroups 2) dsaGroups)
  , ("mldsa_poly_caddq_x8", polyAsm (polyCaddqCom dsaGroups) "mldsa_poly_caddq_x8"
        (oneArrayIn dsaGroups 1) dsaGroups)
  , ("mldsa_decompose_x8", laneAsm (polyDecomposeCom dsaGroups) "mldsa_decompose_x8"
        (oneArrayIn dsaGroups 7) (decomposeOut dsaGroups))
  , ("mldsa_make_hint_x8", polyAsm (polyMakeHintCom dsaGroups) "mldsa_make_hint_x8"
        (hintIn dsaGroups) dsaGroups)
  , ("mldsa_chknorm_x8", laneAsm (polyChknormCom dsaGroups) "mldsa_chknorm_x8"
        (chknormIn dsaGroups) [("RDI", 0)])
  , ("mldsa_use_hint_x8", polyAsm (polyUseHintCom dsaGroups) "mldsa_use_hint_x8"
        (useHintIn dsaGroups) dsaGroups) ]

end CatCrypt.Crypto.SecureCompilation.VIR.LaneWiseEmit
