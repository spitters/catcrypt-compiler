/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedAsm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedAsm
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
public import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold

/-!
# Ed25519 comb-window constant-time select, generated through the front

The fixed-base comb reads one entry of a precomputed table per window. This
module states that lookup as `LowCT` source and compiles it through
`translateDialectControl` and `cryptoDialectToJasminCom` to the owned x86
backend, under the C signature

```c
void f(const u64 *tbl, u64 d, u64 *out);   // tbl = RDI, d = RSI, out = RDX
```

with `tbl` holding `N` entries of four little-endian words (entry `j`, limb `k`
at byte `32·j + 8·k`) and `out` receiving the four words of entry `d`.

The source is the masked linear scan of `Secp256k1PointOpLoopBody.scanSelect`
at four limbs: for every entry `e` it computes a mask that is all-ones exactly
when `d = e`, loads the entry's four cells, ANDs them with the mask and XORs
them into four running limbs. Every entry is read on every call and the index
`d` enters only scalar word operations.

## Main results

* `combSelectSrc N`: the `N`-entry scan as `LowCT`.
* `combSelectSrc_transTotal`, `combSelectFront_isSome`,
  `combSelectLowered_isSome`: the front and the jasmin lowering succeed, by the
  reads-bound judgment `TranslateDialectTotality.TransTotal`.
* `combSelectSrc_run`: the scalar waist semantics `semScalar` of the source
  writes `out[k] = tbl[4·d + k]` when `d < N` and `0` otherwise.
* `combSelectFront_denote`: the denotation of the front output, obtained from
  `translateDialectControl_denote`.
* `combSelectFrontAsm`, `combSelect5FrontAsm`, `combSelect6FrontAsm`: the owned
  AT&T renderings at `N = 16, 32, 64`.
* `combSelectFrontFoldedAsm`, `combSelect5FrontFoldedAsm`,
  `combSelect6FrontFoldedAsm`: the same renderings after
  `ConstIndexFold.constIndexFold`, which turns every table access into a
  fixed-displacement access.
* `combSelectFoldCovers`: the Boolean hypothesis of
  `ConstIndexFold.constIndexFoldBody_lcmdDirect` on the exported bodies.

## Addressing

`RArrLoad` and `RArrStore` at a constant index lower to `stackLoad` /
`stackStore` with the index held in a register, which the Lprog export renders
as a base-plus-index memory operand whose index register holds a literal. The
exported body is therefore outside `AllocCTPreservation.lcmdDirect`, and the
constant-time theorem `toLprogPhysAbi_gather_constant_time` does not apply to
it. The folded renderings apply `ConstIndexFold.constIndexFold` to the exported
`Lprog`; when `combSelectFoldCovers N` is `some true`, the folded body is
`lcmdDirect` and `ConstIndexFold.gatherPrinted_constIndexFoldBody_constant_time`
applies to it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
  (semLowerSExpr_off_tmp srcClean_vars_not_tmp)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType)

/-! ## 1. The source -/

/-- Sequence a command list as a right-nested `RSeq` chain ending in `RSkip`. -/
def seqL : List LowCT → LowCT
  | [] => .RSkip
  | c :: cs => .RSeq c (seqL cs)

/-- The running selected limb `k`. -/
def accName : Fin 4 → String
  | 0 => "s0" | 1 => "s1" | 2 => "s2" | 3 => "s3"

/-- The masked candidate limb `k` of the current entry. -/
def candName : Fin 4 → String
  | 0 => "t0" | 1 => "t1" | 2 => "t2" | 3 => "t3"

/-- A scalar assignment. -/
abbrev setE (x : String) (e : SExpr) : LowCT := .RScalarSetExpr x e

/-- Zero the four running limbs. -/
def selInit : List LowCT :=
  [setE "s0" (.SLit 0), setE "s1" (.SLit 0), setE "s2" (.SLit 0), setE "s3" (.SLit 0)]

/-- The equality mask of entry `e`, bound as `m`: with `q = d ⊕ e` and
    `n = 0 − q`, `(q ⊕ n) ⊕ (q ∧ n)` is `q ∨ n`, whose top bit is set exactly
    when `q ≠ 0`; the shifted bit minus one is all-ones exactly when `d = e`. -/
def maskCmds (e : Nat) : List LowCT :=
  [ setE "q" (.SXor (.SVar "d") (.SLit e))
  , setE "n" (.SSub (.SLit 0) (.SVar "q"))
  , setE "o" (.SXor (.SXor (.SVar "q") (.SVar "n")) (.SAnd (.SVar "q") (.SVar "n")))
  , setE "b" (.SShr (.SVar "o") (.SLit 63))
  , setE "m" (.SSub (.SVar "b") (.SLit 1)) ]

/-- Load table cell `4·e + k` from `tbl` (a `tw`-byte buffer) and mask it into
    candidate `k`. -/
def cellCmds (tw e : Nat) (k : Fin 4) : List LowCT :=
  [ setE "i" (.SLit (4 * e + k.val))
  , .RArrLoad ⟨"l", .TU64⟩ ⟨"tbl", .TBytes tw⟩ "i"
  , setE (candName k) (.SAnd (.SVar "l") (.SVar "m")) ]

/-- Fold candidate `k` into running limb `k`. -/
def foldCmd (k : Fin 4) : LowCT :=
  setE (accName k) (.SXor (.SVar (accName k)) (.SVar (candName k)))

/-- One entry of the scan: its mask, its four masked cells, the four folds. -/
def entryCmds (tw e : Nat) : List LowCT :=
  maskCmds e ++ (cellCmds tw e 0 ++ (cellCmds tw e 1 ++ (cellCmds tw e 2 ++
    (cellCmds tw e 3 ++ [foldCmd 0, foldCmd 1, foldCmd 2, foldCmd 3]))))

/-- The scan over entries `0 … N−1`. -/
def scanCmds (tw : Nat) : Nat → List LowCT
  | 0 => []
  | N + 1 => scanCmds tw N ++ entryCmds tw N

/-- Store running limb `k` to `out[k]`. -/
def storeCmds (k : Fin 4) : List LowCT :=
  [ setE "i" (.SLit k.val)
  , .RArrStore ⟨"out", .TBytes 32⟩ "i" ⟨accName k, .TU64⟩ ]

/-- The four stores. -/
def storeAll : List LowCT :=
  storeCmds 0 ++ (storeCmds 1 ++ (storeCmds 2 ++ storeCmds 3))

/-- The constant-time `N`-entry comb select as `LowCT` source over the arguments
    `tbl` (`4N` little-endian words), `d` (the secret index) and `out` (four
    words): every entry is read on every call and combined under its equality
    mask. -/
def combSelectSrc (N : Nat) : LowCT :=
  seqL (selInit ++ (scanCmds (32 * N) N ++ storeAll))

/-! ## 2. The front and the lowering -/

/-- The argument context, head first: `out` (RDX), `d` (RSI), `tbl` (RDI). -/
def selCtx (N : Nat) : Ctx := [.memref 4, .sword 64, .memref (4 * N)]

/-- The argument `VarMap`: `tbl` bound deepest, then `d`, then `out`. -/
def selVM (N : Nat) : VarMap (selCtx N) :=
  ((VarMap.empty.bind (t := .memref (4 * N)) "tbl").bind (t := .sword 64) "d").bind
    (t := .memref 4) "out"

/-- The front output: `translateDialectControl` on the source, closed by
    returning `out`. -/
def combSelectFront (N : Nat) : Option (Com catCryptDialect (selCtx N) (.memref 4)) :=
  match translateDialectControl (selVM N) (combSelectSrc N) with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front output lowered to `Com jasminDialect`. -/
def combSelectLowered (N : Nat) :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match combSelectFront N with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-- The owned AT&T rendering under `f(tbl = RDI, d = RSI, out = RDX)`. -/
def combSelectFrontAsmN (name : String) (N : Nat) : Option String :=
  OwnedAsm.ownedAsm name ["RDI", "RSI", "RDX"] (combSelectLowered N)

/-- The 16-entry (4-bit window) select, `ed25519_comb_select_x86_from_lean`. -/
def combSelectFrontAsm : Option String :=
  combSelectFrontAsmN "ed25519_comb_select_x86_from_lean" 16

/-- The 32-entry (5-bit window) select, `ed25519_comb5_select_x86_from_lean`. -/
def combSelect5FrontAsm : Option String :=
  combSelectFrontAsmN "ed25519_comb5_select_x86_from_lean" 32

/-- The 64-entry (6-bit window) select, `ed25519_comb6_select_x86_from_lean`. -/
def combSelect6FrontAsm : Option String :=
  combSelectFrontAsmN "ed25519_comb6_select_x86_from_lean" 64

/-- The exported `Lprog` of the lowered select under `f(tbl = RDI, d = RSI,
    out = RDX)`, with the export arguments of `OwnedAsm.ownedAsm`. -/
def combSelectLprog (name : String) (N : Nat) : Option JasminLprogExport.Lprog :=
  (combSelectLowered N).map (fun s =>
    JasminLprogExport.Com.toLprogPhysAbi s.2.2 name
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T rendering of the select after `ConstIndexFold.constIndexFold`,
    with the folded accesses spelled as `mem.<base>.<off>` operands. -/
def combSelectFrontFoldedAsmN (name : String) (N : Nat) : Option String :=
  (combSelectLprog name N).map (fun lp =>
    LprogOptPipeline.renderOwned
      (ConstIndexFold.spellLprog (ConstIndexFold.constIndexFold lp)))

/-- The folded 16-entry select, `ed25519_comb_select_x86_from_lean`. -/
def combSelectFrontFoldedAsm : Option String :=
  combSelectFrontFoldedAsmN "ed25519_comb_select_x86_from_lean" 16

/-- The folded 32-entry select, `ed25519_comb5_select_x86_from_lean`. -/
def combSelect5FrontFoldedAsm : Option String :=
  combSelectFrontFoldedAsmN "ed25519_comb5_select_x86_from_lean" 32

/-- The folded 64-entry select, `ed25519_comb6_select_x86_from_lean`. -/
def combSelect6FrontFoldedAsm : Option String :=
  combSelectFrontFoldedAsmN "ed25519_comb6_select_x86_from_lean" 64

/-- For every function of the exported `N`-entry select: every register-indexed
    instruction is folded (`ConstIndexFold.covers`) and the fold keeps the frame
    parameters. `some true` discharges both hypotheses of
    `ConstIndexFold.constIndexFoldBody_lcmdDirect`. -/
def combSelectFoldCovers (N : Nat) : Option Bool :=
  (combSelectLprog "ed25519_comb_select_x86_from_lean" N).map (fun lp =>
    lp.lp_funcs.all (fun f =>
      let b := f.2.lfd_body
      let p := ConstIndexFold.bodyParams b
      ConstIndexFold.covers p [] b
        && ConstIndexFold.bodyParams (ConstIndexFold.foldCore p [] b) == p))

/-! ## 3. Names outside the front's temporary namespace -/

theorem notTmp_of_head {s : String} (h : (s.toList.headD '_' != '_') = true) :
    ¬ isTmpName s := by
  cases hs : s.toList with
  | nil => simp [hs] at h
  | cons c t =>
      refine notTmp_of_headNe hs ?_
      simpa [hs] using h

theorem accName_notTmp (k : Fin 4) : ¬ isTmpName (accName k) := by
  match k with
  | 0 | 1 | 2 | 3 => exact notTmp_of_head (by decide)

theorem candName_notTmp (k : Fin 4) : ¬ isTmpName (candName k) := by
  match k with
  | 0 | 1 | 2 | 3 => exact notTmp_of_head (by decide)

/-! ## 4. The equality mask -/

/-- The value of the equality mask of entry `e` against index `D`. -/
def eqMask (D : BitVec 64) (e : Nat) : BitVec 64 :=
  if D = BitVec.ofNat 64 e then BitVec.allOnes 64 else 0

theorem xor_xor_and_eq_or (x y : BitVec 64) : x ^^^ y ^^^ (x &&& y) = x ||| y := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> rfl

theorem or_neg_shr_63 (q : BitVec 64) :
    (q ||| (0 - q)) >>> 63 = if q = 0 then 0 else 1 := by
  by_cases hq : q = 0
  · subst hq; rfl
  · rw [if_neg hq]
    apply BitVec.eq_of_toNat_eq
    have hq' : q.toNat ≠ 0 := fun h => hq (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlt := q.isLt
    have hneg : (0 - q).toNat = 2 ^ 64 - q.toNat := by
      rw [BitVec.toNat_sub]
      have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
      rw [h0, Nat.add_zero]
      exact Nat.mod_eq_of_lt (by omega)
    have h1 : q.toNat ≤ (q ||| (0 - q)).toNat := by
      rw [BitVec.toNat_or]; exact Nat.left_le_or
    have h2 : (0 - q).toNat ≤ (q ||| (0 - q)).toNat := by
      rw [BitVec.toNat_or]; exact Nat.right_le_or
    rw [hneg] at h2
    have h3 := (q ||| (0 - q)).isLt
    have h4 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
    have hp : (2 : Nat) ^ 64 = 2 ^ 63 * 2 := by norm_num
    rw [BitVec.toNat_ushiftRight, h4, Nat.shiftRight_eq_div_pow]
    rw [hp] at h2 h3 hlt
    omega

/-- The mask chain of `maskCmds e` evaluates to `eqMask D e`. -/
theorem maskChain_eq (D : BitVec 64) (e : Nat) :
    (((D ^^^ BitVec.ofNat 64 e) ^^^ (BitVec.ofNat 64 0 - (D ^^^ BitVec.ofNat 64 e))
        ^^^ ((D ^^^ BitVec.ofNat 64 e) &&& (BitVec.ofNat 64 0 - (D ^^^ BitVec.ofNat 64 e))))
        >>> (BitVec.ofNat 64 63).toNat) - BitVec.ofNat 64 1 = eqMask D e := by
  have h63 : (BitVec.ofNat 64 63).toNat = 63 := rfl
  have h0 : BitVec.ofNat 64 0 = 0 := rfl
  rw [h63, h0, xor_xor_and_eq_or, or_neg_shr_63, eqMask]
  by_cases hq : D ^^^ BitVec.ofNat 64 e = 0
  · rw [if_pos hq, if_pos (BitVec.xor_eq_zero_iff.mp hq)]; rfl
  · rw [if_neg hq, if_neg (fun h => hq (BitVec.xor_eq_zero_iff.mpr h))]; rfl

/-! ## 5. Single-command steps of the waist semantics -/

theorem semScalar_seqL_cons {c : LowCT} {cs : List LowCT} {env env₁ : SEnvScalar}
    (h : semScalar c env = some env₁) :
    semScalar (seqL (c :: cs)) env = semScalar (seqL cs) env₁ := by
  simp only [seqL, semScalar, h, Option.bind_some]

theorem semScalar_seqL_nil (env : SEnvScalar) : semScalar (seqL []) env = some env := by
  simp only [seqL, semScalar]

theorem semScalar_seqL_append (a b : List LowCT) (env : SEnvScalar) :
    semScalar (seqL (a ++ b)) env = (semScalar (seqL a) env).bind (semScalar (seqL b)) := by
  induction a generalizing env with
  | nil => simp only [List.nil_append, semScalar_seqL_nil, Option.bind_some]
  | cons c cs ih =>
      simp only [List.cons_append, seqL, semScalar]
      cases semScalar c env with
      | none => rfl
      | some e => simp only [Option.bind_some, ih]

theorem binNode_progress {env : SEnvScalar} {na nb : String} {cnt : Nat}
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (ha : (envReadU64 env na).isSome) (hb : (envReadU64 env nb).isSome) :
    ∃ (env' : SEnvScalar) (nm : String) (cnt' : Nat),
      binNode env na nb cnt f = some (env', nm, cnt') ∧ cnt' = cnt + 1
        ∧ OnlyTmpBelow env env' cnt ∧ ResultOK nm cnt' ∧ (envReadU64 env' nm).isSome := by
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp hb
  refine ⟨env.upd (tmpName cnt) (t := .sword 64) (f va vb),
    tmpName cnt, cnt + 1, ?_, rfl,
    onlyTmpBelow_upd (onlyTmpBelow_refl env cnt) (le_refl _),
    Or.inr ⟨cnt, Nat.lt_succ_self _, rfl⟩, ?_⟩
  · simp only [binNode, hva, hvb]
  · rw [envReadU64_upd_self]; rfl

/-- The `SExpr` lowering mirror makes progress when every variable it reads is
    bound at 64-bit word type. -/
theorem semLowerSExpr_progress :
    ∀ (e : SExpr) (env : SEnvScalar) (cnt : Nat), srcClean e →
      (∀ s ∈ sexprVars e, (envReadU64 env s).isSome) →
      ∃ (env₂ : SEnvScalar) (nm : String) (cnt' : Nat),
        semLowerSExpr env cnt e = some (env₂, nm, cnt') ∧ cnt ≤ cnt'
          ∧ OnlyTmpBelow env env₂ cnt ∧ ResultOK nm cnt'
          ∧ (envReadU64 env₂ nm).isSome := by
  intro e
  induction e with
  | SVar x =>
      intro env cnt hcl hb
      have hread := hb x (by simp [sexprVars])
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hread
      refine ⟨env, x, cnt, ?_, le_refl _, onlyTmpBelow_refl env cnt, Or.inl hcl, hread⟩
      simp only [semLowerSExpr, hv]
  | SLit n =>
      intro env cnt _ _
      refine ⟨env.upd (tmpName cnt) (t := .sword 64)
        (BitVec.ofNat 64 n), tmpName cnt,
        cnt + 1, rfl, Nat.le_succ _,
        onlyTmpBelow_upd (onlyTmpBelow_refl env cnt) (le_refl _),
        Or.inr ⟨cnt, Nat.lt_succ_self _, rfl⟩, ?_⟩
      rw [envReadU64_upd_self]; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro env cnt hcl hb
      obtain ⟨env1, na, c1, hA, hleA, hotbA, hrokA, hreadA⟩ :=
        iha env cnt hcl.1
          (fun s hs => hb s (by simp only [sexprVars, List.mem_append]; exact Or.inl hs))
      have hb1 : ∀ s ∈ sexprVars b, (envReadU64 env1 s).isSome := by
        intro s hs
        rw [readU64_stable hotbA (Or.inl (srcClean_vars_not_tmp b hcl.2 s hs))]
        exact hb s (by simp only [sexprVars, List.mem_append]; exact Or.inr hs)
      obtain ⟨env2, nb, c2, hB, hleB, hotbB, hrokB, hreadB⟩ := ihb env1 c1 hcl.2 hb1
      have hna2 : (envReadU64 env2 na).isSome := by
        rw [readU64_stable hotbB hrokA]; exact hreadA
      obtain ⟨env3, nm, c3, hbn, hc3, hotb3, hrok3, hread3⟩ :=
        binNode_progress (cnt := c2) _ hna2 hreadB
      refine ⟨env3, nm, c3, ?_, by omega, ?_, hrok3, hread3⟩
      · simp only [semLowerSExpr, hA, hB]; exact hbn
      · exact onlyTmpBelow_trans (onlyTmpBelow_trans hotbA hotbB hleA) hotb3
          (le_trans hleA hleB)
  | SLt a b _ _ => intro _ _ hcl; exact hcl.elim
  | SAsr a b _ _ => intro _ _ hcl; exact hcl.elim
  | SMulS a b _ _ => intro _ _ hcl; exact hcl.elim
  | SMulHiS a b _ _ => intro _ _ hcl; exact hcl.elim
  | SLimb v i => intro _ _ hcl; exact hcl.elim

/-- One scalar assignment: the destination holds the word value of the
    expression, and every other source name keeps its binding. -/
theorem setE_run {x : String} {e : SExpr} {env : SEnvScalar} (hcl : srcClean e)
    (hv : ∀ s ∈ sexprVars e, (envReadU64 env s).isSome) :
    ∃ env', semScalar (setE x e) env = some env'
      ∧ env' x = some ⟨.sword 64, e.evalBV (envReader env)⟩
      ∧ ∀ s, ¬ isTmpName s → s ≠ x → env' s = env s := by
  obtain ⟨env2, nm, c, h, -⟩ := semLowerSExpr_progress e env 0 hcl hv
  refine ⟨env2.upd x (t := .sword 64) (e.evalBV (envReader env)), ?_, ?_, ?_⟩
  · simp only [semScalar, h]
  · simp [SEnvScalar.upd]
  · intro s hs hne
    simp only [SEnvScalar.upd, if_neg hne]
    exact semLowerSExpr_off_tmp e env env2 0 c nm s h hs

/-- A dynamic-index load of a word out of a bound memref. -/
theorem arrLoad_eq {dstN arrN idxN : String} {tw : TowerType} {n : Nat}
    {a : Fin n → BitVec 64} {i : BitVec 64} {env : SEnvScalar}
    (ha : env arrN = some ⟨.memref n, a⟩) (hi : env idxN = some ⟨.sword 64, i⟩) :
    semScalar (.RArrLoad ⟨dstN, .TU64⟩ ⟨arrN, tw⟩ idxN) env
      = some (env.upd dstN (t := .sword 64) (memGetDyn a i.toNat)) := by
  simp only [semScalar, ha, hi]

/-- A dynamic-index store of a word into a bound four-word memref. -/
theorem arrStore_eq {arrN idxN srcN : String} {a : Fin 4 → BitVec 64}
    {i v : BitVec 64} {env : SEnvScalar}
    (ha : env arrN = some ⟨.memref 4, a⟩) (hi : env idxN = some ⟨.sword 64, i⟩)
    (hv : env srcN = some ⟨.sword 64, v⟩) :
    semScalar (.RArrStore ⟨arrN, .TBytes 32⟩ idxN ⟨srcN, .TU64⟩) env
      = some (env.upd arrN (t := .memref 4) (memSetDyn a i.toNat v)) := by
  have hty : encodeTy (Located.mk arrN (TowerType.TBytes 32)).locDst = CryptoTy.memref 4 :=
    rfl
  simp only [semScalar, ha, hi, hv, dif_pos hty]
  rfl

theorem litClean {n : Nat} (h : n < 2 ^ 64) : srcClean (.SLit n) := h

theorem upd_ne' {t : CryptoTy} {env : SEnvScalar} {y : String} {v : ⟦t⟧} {x : String}
    (h : x ≠ y) : (env.upd y v) x = env x := by
  simp only [SEnvScalar.upd, if_neg h]

theorem readU64_of {env : SEnvScalar} {s : String} {w : BitVec 64}
    (h : env s = some ⟨.sword 64, w⟩) : (envReadU64 env s).isSome := by
  simp only [envReadU64, h, Option.isSome_some]

theorem reader_of {env : SEnvScalar} {s : String} {w : BitVec 64}
    (h : env s = some ⟨.sword 64, w⟩) : envReader env s = w := by
  simp only [envReader, h]

/-! ## 6. The scan invariant and the blocks of the source -/

/-- The environment binds the table `T`, the index `D`, the output buffer `O`
    and the four running limbs `a`. -/
structure SelInv (N : Nat) (T : Fin (4 * N) → BitVec 64) (D : BitVec 64)
    (O : Fin 4 → BitVec 64) (a : Fin 4 → BitVec 64) (env : SEnvScalar) : Prop where
  tbl : env "tbl" = some ⟨.memref (4 * N), T⟩
  d : env "d" = some ⟨.sword 64, D⟩
  out : env "out" = some ⟨.memref 4, O⟩
  acc : ∀ k, env (accName k) = some ⟨.sword 64, a k⟩

/-- The names `SelInv` reads. -/
def isProtected (x : String) : Bool :=
  x == "tbl" || x == "d" || x == "out" || x == "s0" || x == "s1" || x == "s2" || x == "s3"

theorem SelInv.frame {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env env' : SEnvScalar} {x : String}
    (h : SelInv N T D O a env) (hf : ∀ s, ¬ isTmpName s → s ≠ x → env' s = env s)
    (hx : isProtected x = false) : SelInv N T D O a env' := by
  simp only [isProtected, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h1)]; exact h.tbl
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h2)]; exact h.d
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h3)]; exact h.out
  · intro k
    have hk : accName k ≠ x := by
      match k with
      | 0 => exact Ne.symm h4
      | 1 => exact Ne.symm h5
      | 2 => exact Ne.symm h6
      | 3 => exact Ne.symm h7
    rw [hf _ (accName_notTmp k) hk]; exact h.acc k

/-- The mask block binds `m` to `eqMask D e`. -/
theorem maskCmds_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar}
    (h : SelInv N T D O a env) (e : Nat) (he : e < 2 ^ 64) :
    ∃ env', semScalar (seqL (maskCmds e)) env = some env' ∧ SelInv N T D O a env'
      ∧ env' "m" = some ⟨.sword 64, eqMask D e⟩ := by
  have nq : ¬ isTmpName "q" := notTmp_of_head (by decide)
  have nn : ¬ isTmpName "n" := notTmp_of_head (by decide)
  have no : ¬ isTmpName "o" := notTmp_of_head (by decide)
  have nb : ¬ isTmpName "b" := notTmp_of_head (by decide)
  have nd : ¬ isTmpName "d" := notTmp_of_head (by decide)
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "q") (e := .SXor (.SVar "d") (.SLit e))
    (env := env) ⟨nd, he⟩ (by simp [sexprVars, readU64_of h.d])
  have h1 := h.frame f1 rfl
  obtain ⟨e2, s2, v2, f2⟩ := setE_run (x := "n") (e := .SSub (.SLit 0) (.SVar "q"))
    (env := e1) ⟨litClean (by norm_num), nq⟩ (by simp [sexprVars, readU64_of v1])
  have h2 := h1.frame f2 rfl
  have q2 := (f2 "q" nq (by decide)).trans v1
  obtain ⟨e3, s3, v3, f3⟩ := setE_run (x := "o")
    (e := .SXor (.SXor (.SVar "q") (.SVar "n")) (.SAnd (.SVar "q") (.SVar "n")))
    (env := e2) ⟨⟨nq, nn⟩, ⟨nq, nn⟩⟩ (by simp [sexprVars, readU64_of q2, readU64_of v2])
  have h3 := h2.frame f3 rfl
  obtain ⟨e4, s4, v4, f4⟩ := setE_run (x := "b") (e := .SShr (.SVar "o") (.SLit 63))
    (env := e3) ⟨no, litClean (by norm_num)⟩ (by simp [sexprVars, readU64_of v3])
  have h4 := h3.frame f4 rfl
  obtain ⟨e5, s5, v5, f5⟩ := setE_run (x := "m") (e := .SSub (.SVar "b") (.SLit 1))
    (env := e4) ⟨nb, litClean (by norm_num)⟩ (by simp [sexprVars, readU64_of v4])
  have h5 := h4.frame f5 rfl
  refine ⟨e5, ?_, h5, ?_⟩
  · rw [maskCmds, semScalar_seqL_cons s1, semScalar_seqL_cons s2, semScalar_seqL_cons s3,
      semScalar_seqL_cons s4, semScalar_seqL_cons s5, semScalar_seqL_nil]
  · rw [v5, ← maskChain_eq]
    simp only [SExpr.evalBV, reader_of v4, reader_of v3, reader_of v2, reader_of q2,
      reader_of v1, reader_of h.d]

theorem candName_ne {j k : Fin 4} (h : j ≠ k) : candName j ≠ candName k := by
  match j, k with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 => exact absurd rfl h
  | 0, 1 | 0, 2 | 0, 3 | 1, 0 | 1, 2 | 1, 3 | 2, 0 | 2, 1 | 2, 3 | 3, 0 | 3, 1 | 3, 2 =>
    decide

theorem candName_prot (k : Fin 4) : isProtected (candName k) = false := by
  match k with
  | 0 | 1 | 2 | 3 => rfl

theorem candName_ne_m (k : Fin 4) : candName k ≠ "m" := by
  match k with
  | 0 | 1 | 2 | 3 => decide

theorem candName_ne_i (k : Fin 4) : candName k ≠ "i" := by
  match k with
  | 0 | 1 | 2 | 3 => decide

theorem candName_ne_l (k : Fin 4) : candName k ≠ "l" := by
  match k with
  | 0 | 1 | 2 | 3 => decide

/-- One cell block binds candidate `k` to the masked table cell and keeps the
    mask and the other candidates. -/
theorem cellCmds_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar} {M : BitVec 64}
    (h : SelInv N T D O a env) (hm : env "m" = some ⟨.sword 64, M⟩)
    (tw e : Nat) (k : Fin 4) (hi : 4 * e + k.val < 2 ^ 64) :
    ∃ env', semScalar (seqL (cellCmds tw e k)) env = some env' ∧ SelInv N T D O a env'
      ∧ env' "m" = some ⟨.sword 64, M⟩
      ∧ env' (candName k) = some ⟨.sword 64, memGetDyn T (4 * e + k.val) &&& M⟩
      ∧ ∀ j, j ≠ k → env' (candName j) = env (candName j) := by
  have ni : ¬ isTmpName "i" := notTmp_of_head (by decide)
  have nl : ¬ isTmpName "l" := notTmp_of_head (by decide)
  have nm : ¬ isTmpName "m" := notTmp_of_head (by decide)
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "i") (e := .SLit (4 * e + k.val))
    (env := env) (litClean hi) (by simp [sexprVars])
  have h1 := h.frame f1 rfl
  have m1 := (f1 "m" nm (by decide)).trans hm
  have s2 := arrLoad_eq (dstN := "l") (tw := .TBytes tw) h1.tbl v1
  set e2 := e1.upd "l" (t := .sword 64) (memGetDyn T (SExpr.evalBV (envReader env)
    (.SLit (4 * e + k.val))).toNat) with he2
  have f2 : ∀ s, ¬ isTmpName s → s ≠ "l" → e2 s = e1 s := fun s _ hs => upd_ne' hs
  have v2 : e2 "l" = some ⟨.sword 64, memGetDyn T (4 * e + k.val)⟩ := by
    rw [he2, SEnvScalar.upd, if_pos rfl]
    simp only [SExpr.evalBV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
  have h2 := h1.frame f2 rfl
  have m2 := (f2 "m" nm (by decide)).trans m1
  obtain ⟨e3, s3, v3, f3⟩ := setE_run (x := candName k) (e := .SAnd (.SVar "l") (.SVar "m"))
    (env := e2) ⟨nl, nm⟩ (by simp [sexprVars, readU64_of v2, readU64_of m2])
  have h3 := h2.frame f3 (candName_prot k)
  refine ⟨e3, ?_, h3, (f3 "m" nm (Ne.symm (candName_ne_m k))).trans m2, ?_, ?_⟩
  · rw [cellCmds, semScalar_seqL_cons s1, semScalar_seqL_cons s2, semScalar_seqL_cons s3,
      semScalar_seqL_nil]
  · rw [v3]
    simp only [SExpr.evalBV, reader_of v2, reader_of m2]
  · intro j hj
    rw [f3 _ (candName_notTmp j) (candName_ne hj), f2 _ (candName_notTmp j) (candName_ne_l j),
      f1 _ (candName_notTmp j) (candName_ne_i j)]

theorem accName_ne {j k : Fin 4} (h : j ≠ k) : accName j ≠ accName k := by
  match j, k with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 => exact absurd rfl h
  | 0, 1 | 0, 2 | 0, 3 | 1, 0 | 1, 2 | 1, 3 | 2, 0 | 2, 1 | 2, 3 | 3, 0 | 3, 1 | 3, 2 =>
    decide

theorem candName_ne_acc (j k : Fin 4) : candName j ≠ accName k := by
  match j, k with
  | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 1, 0 | 1, 1 | 1, 2 | 1, 3
  | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 3, 0 | 3, 1 | 3, 2 | 3, 3 => decide

theorem accName_ne_tbl (k : Fin 4) : accName k ≠ "tbl" := by
  match k with
  | 0 | 1 | 2 | 3 => decide

theorem accName_ne_d (k : Fin 4) : accName k ≠ "d" := by
  match k with
  | 0 | 1 | 2 | 3 => decide

theorem accName_ne_out (k : Fin 4) : accName k ≠ "out" := by
  match k with
  | 0 | 1 | 2 | 3 => decide

/-- Replace limb `k` of `a` by `v`. -/
def setLimb (a : Fin 4 → BitVec 64) (k : Fin 4) (v : BitVec 64) : Fin 4 → BitVec 64 :=
  fun j => if j = k then v else a j

/-- A fold XORs candidate `k` into running limb `k` and keeps every candidate. -/
theorem foldCmd_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar} {c : BitVec 64} (k : Fin 4)
    (h : SelInv N T D O a env) (hc : env (candName k) = some ⟨.sword 64, c⟩) :
    ∃ env', semScalar (foldCmd k) env = some env'
      ∧ SelInv N T D O (setLimb a k (a k ^^^ c)) env'
      ∧ ∀ j, env' (candName j) = env (candName j) := by
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := accName k)
    (e := .SXor (.SVar (accName k)) (.SVar (candName k))) (env := env)
    ⟨accName_notTmp k, candName_notTmp k⟩
    (by simp [sexprVars, readU64_of (h.acc k), readU64_of hc])
  refine ⟨e1, s1, ⟨?_, ?_, ?_, ?_⟩, fun j => f1 _ (candName_notTmp j) (candName_ne_acc j k)⟩
  · rw [f1 _ (notTmp_of_head (by decide)) (Ne.symm (accName_ne_tbl k))]; exact h.tbl
  · rw [f1 _ (notTmp_of_head (by decide)) (Ne.symm (accName_ne_d k))]; exact h.d
  · rw [f1 _ (notTmp_of_head (by decide)) (Ne.symm (accName_ne_out k))]; exact h.out
  · intro j
    by_cases hj : j = k
    · subst hj
      rw [v1]
      simp [setLimb, SExpr.evalBV, reader_of (h.acc j), reader_of hc]
    · rw [f1 _ (accName_notTmp j) (accName_ne hj)]
      simp only [setLimb, if_neg hj]
      exact h.acc j

/-- The limbs after one entry: `a k ⊕ (T[4e + k] ∧ eqMask D e)`. -/
def entryVal {N : Nat} (T : Fin (4 * N) → BitVec 64) (D : BitVec 64) (e : Nat)
    (a : Fin 4 → BitVec 64) : Fin 4 → BitVec 64 :=
  fun k => a k ^^^ (memGetDyn T (4 * e + k.val) &&& eqMask D e)

/-- One entry of the scan folds the masked entry into the running limbs. -/
theorem entryCmds_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar}
    (h : SelInv N T D O a env) (tw e : Nat) (he : 4 * e + 4 ≤ 2 ^ 64) :
    ∃ env', semScalar (seqL (entryCmds tw e)) env = some env'
      ∧ SelInv N T D O (entryVal T D e a) env' := by
  obtain ⟨e0, s0, h0, m0⟩ := maskCmds_run h e (by omega)
  obtain ⟨e1, s1, h1, m1, c1, r1⟩ := cellCmds_run h0 m0 tw e 0 (by simp; omega)
  obtain ⟨e2, s2, h2, m2, c2, r2⟩ := cellCmds_run h1 m1 tw e 1 (by simp; omega)
  obtain ⟨e3, s3, h3, m3, c3, r3⟩ := cellCmds_run h2 m2 tw e 2 (by simp; omega)
  obtain ⟨e4, s4, h4, -, c4, r4⟩ := cellCmds_run h3 m3 tw e 3 (by simp; omega)
  have c1' := ((r4 0 (by decide)).trans ((r3 0 (by decide)).trans (r2 0 (by decide)))).trans c1
  have c2' := ((r4 1 (by decide)).trans (r3 1 (by decide))).trans c2
  have c3' := (r4 2 (by decide)).trans c3
  obtain ⟨f1, t1, g1, q1⟩ := foldCmd_run 0 h4 c1'
  obtain ⟨f2, t2, g2, q2⟩ := foldCmd_run 1 g1 ((q1 1).trans c2')
  obtain ⟨f3, t3, g3, q3⟩ := foldCmd_run 2 g2 ((q2 2).trans ((q1 2).trans c3'))
  obtain ⟨f4, t4, g4, -⟩ := foldCmd_run 3 g3 ((q3 3).trans ((q2 3).trans ((q1 3).trans c4)))
  refine ⟨f4, ?_, ?_⟩
  · rw [entryCmds, semScalar_seqL_append, s0, Option.bind_some, semScalar_seqL_append, s1,
      Option.bind_some, semScalar_seqL_append, s2, Option.bind_some, semScalar_seqL_append,
      s3, Option.bind_some, semScalar_seqL_append, s4, Option.bind_some,
      semScalar_seqL_cons t1, semScalar_seqL_cons t2, semScalar_seqL_cons t3,
      semScalar_seqL_cons t4, semScalar_seqL_nil]
  · convert g4 using 2
    funext j
    match j with
    | 0 | 1 | 2 | 3 => simp [setLimb, entryVal]

/-- Running limb `k` after the first `n` entries of the scan. -/
def scanVal {N : Nat} (T : Fin (4 * N) → BitVec 64) (D : BitVec 64) (k : Fin 4) :
    Nat → BitVec 64
  | 0 => 0
  | n + 1 => scanVal T D k n ^^^ (memGetDyn T (4 * n + k.val) &&& eqMask D n)

/-- The scan over `n` entries leaves `scanVal` in the running limbs. -/
theorem scanCmds_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O : Fin 4 → BitVec 64} (tw : Nat) :
    ∀ (n : Nat) (env : SEnvScalar), 4 * n ≤ 2 ^ 64 →
      SelInv N T D O (fun _ => 0) env →
      ∃ env', semScalar (seqL (scanCmds tw n)) env = some env'
        ∧ SelInv N T D O (fun k => scanVal T D k n) env'
  | 0, env, _, h => ⟨env, semScalar_seqL_nil env, h⟩
  | n + 1, env, hn, h => by
      obtain ⟨e1, s1, h1⟩ := scanCmds_run tw n env (by omega) h
      obtain ⟨e2, s2, h2⟩ := entryCmds_run h1 tw n (by omega)
      exact ⟨e2, by rw [scanCmds, semScalar_seqL_append, s1, Option.bind_some, s2], h2⟩

/-- `scanVal` is the entry at the index when the index is in range, `0`
    otherwise. -/
theorem scanVal_eq {N : Nat} (T : Fin (4 * N) → BitVec 64) (D : BitVec 64) (k : Fin 4) :
    ∀ n, n ≤ 2 ^ 64 →
      scanVal T D k n = if D.toNat < n then memGetDyn T (4 * D.toNat + k.val) else 0
  | 0, _ => by simp [scanVal]
  | n + 1, hn => by
      have ih := scanVal_eq T D k n (by omega)
      have h64 : n < 2 ^ 64 := by omega
      have hiff : D = BitVec.ofNat 64 n ↔ D.toNat = n := by
        constructor
        · rintro rfl; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
        · intro h
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]; exact h
      rw [scanVal, ih, eqMask]
      by_cases hlt : D.toNat < n
      · have hne : ¬ D = BitVec.ofNat 64 n := fun h => by have := hiff.mp h; omega
        simp [hlt, hne, show D.toNat < n + 1 by omega]
      · by_cases heq : D.toNat = n
        · subst heq
          rw [if_neg hlt, if_pos (hiff.mpr rfl), if_pos (Nat.lt_succ_self _)]
          simp only [BitVec.and_allOnes]; exact BitVec.zero_xor
        · have hne : ¬ D = BitVec.ofNat 64 n := fun h => heq (hiff.mp h)
          simp [hlt, hne, show ¬ D.toNat < n + 1 by omega]

/-- The initialisation zeroes the four running limbs. -/
theorem selInit_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O : Fin 4 → BitVec 64} {env : SEnvScalar}
    (ht : env "tbl" = some ⟨.memref (4 * N), T⟩) (hd : env "d" = some ⟨.sword 64, D⟩)
    (ho : env "out" = some ⟨.memref 4, O⟩) :
    ∃ env', semScalar (seqL selInit) env = some env'
      ∧ SelInv N T D O (fun _ => 0) env' := by
  have z : srcClean (.SLit 0) := litClean (by norm_num)
  have nz : ∀ s ∈ sexprVars (.SLit 0), (envReadU64 env s).isSome := by simp [sexprVars]
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "s0") (env := env) z nz
  obtain ⟨e2, s2, v2, f2⟩ := setE_run (x := "s1") (env := e1) z (by simp [sexprVars])
  obtain ⟨e3, s3, v3, f3⟩ := setE_run (x := "s2") (env := e2) z (by simp [sexprVars])
  obtain ⟨e4, s4, v4, f4⟩ := setE_run (x := "s3") (env := e3) z (by simp [sexprVars])
  have keep : ∀ s, ¬ isTmpName s → s ≠ "s0" → s ≠ "s1" → s ≠ "s2" → s ≠ "s3" →
      e4 s = env s := fun s hs h0 h1 h2 h3 =>
    (f4 s hs h3).trans ((f3 s hs h2).trans ((f2 s hs h1).trans (f1 s hs h0)))
  have n0 : ¬ isTmpName "s0" := accName_notTmp 0
  have n1 : ¬ isTmpName "s1" := accName_notTmp 1
  have n2 : ¬ isTmpName "s2" := accName_notTmp 2
  refine ⟨e4, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [selInit, semScalar_seqL_cons s1, semScalar_seqL_cons s2, semScalar_seqL_cons s3,
      semScalar_seqL_cons s4, semScalar_seqL_nil]
  · rw [keep _ (notTmp_of_head (by decide)) (by decide) (by decide) (by decide) (by decide)]
    exact ht
  · rw [keep _ (notTmp_of_head (by decide)) (by decide) (by decide) (by decide) (by decide)]
    exact hd
  · rw [keep _ (notTmp_of_head (by decide)) (by decide) (by decide) (by decide) (by decide)]
    exact ho
  · intro k
    match k with
    | 0 =>
        show e4 "s0" = _
        rw [f4 _ n0 (by decide), f3 _ n0 (by decide), f2 _ n0 (by decide), v1]; rfl
    | 1 =>
        show e4 "s1" = _
        rw [f4 _ n1 (by decide), f3 _ n1 (by decide), v2]; rfl
    | 2 =>
        show e4 "s2" = _
        rw [f4 _ n2 (by decide), v3]; rfl
    | 3 =>
        show e4 "s3" = _
        rw [v4]; rfl

/-- One store writes running limb `k` to `out[k]`. -/
theorem storeCmds_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar} (k : Fin 4)
    (h : SelInv N T D O a env) :
    ∃ env', semScalar (seqL (storeCmds k)) env = some env'
      ∧ SelInv N T D (memSetDyn O k.val (a k)) a env' := by
  have ni : ¬ isTmpName "i" := notTmp_of_head (by decide)
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "i") (e := .SLit k.val) (env := env)
    (litClean (by omega)) (by simp [sexprVars])
  have h1 := h.frame f1 rfl
  have v1' : e1 "i" = some ⟨.sword 64, BitVec.ofNat 64 k.val⟩ := v1
  have s2 := arrStore_eq (arrN := "out") (srcN := accName k) h1.out v1' (h1.acc k)
  have hk : (BitVec.ofNat 64 k.val).toNat = k.val := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨e1.upd "out" (t := .memref 4) (memSetDyn O (BitVec.ofNat 64 k.val).toNat (a k)),
    ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [storeCmds, semScalar_seqL_cons s1, semScalar_seqL_cons s2, semScalar_seqL_nil]
  · rw [upd_ne' (by decide)]; exact h1.tbl
  · rw [upd_ne' (by decide)]; exact h1.d
  · rw [hk]
    simp [SEnvScalar.upd]
  · intro j
    rw [upd_ne' (accName_ne_out j)]; exact h1.acc j

/-- Four stores write the running limbs to `out`. -/
theorem storeAll_run {N : Nat} {T : Fin (4 * N) → BitVec 64} {D : BitVec 64}
    {O a : Fin 4 → BitVec 64} {env : SEnvScalar}
    (h : SelInv N T D O a env) :
    ∃ env', semScalar (seqL storeAll) env = some env' ∧ SelInv N T D a a env' := by
  obtain ⟨e1, s1, h1⟩ := storeCmds_run 0 h
  obtain ⟨e2, s2, h2⟩ := storeCmds_run 1 h1
  obtain ⟨e3, s3, h3⟩ := storeCmds_run 2 h2
  obtain ⟨e4, s4, h4⟩ := storeCmds_run 3 h3
  refine ⟨e4, ?_, ?_⟩
  · rw [storeAll, semScalar_seqL_append, s1, Option.bind_some, semScalar_seqL_append, s2,
      Option.bind_some, semScalar_seqL_append, s3, Option.bind_some, s4]
  · convert h4 using 2
    funext j
    match j with
    | 0 | 1 | 2 | 3 => simp [memSetDyn]

/-- **Waist semantics of the source.** From an environment binding the table
    `T`, the index `D` and the output buffer, the source runs to completion and
    leaves `out[k] = T[4·D + k]` when `D < N`, and `out[k] = 0` otherwise. -/
theorem combSelectSrc_run (N : Nat) (hN : 4 * N ≤ 2 ^ 64) {T : Fin (4 * N) → BitVec 64}
    {D : BitVec 64} {O : Fin 4 → BitVec 64} {env : SEnvScalar}
    (ht : env "tbl" = some ⟨.memref (4 * N), T⟩) (hd : env "d" = some ⟨.sword 64, D⟩)
    (ho : env "out" = some ⟨.memref 4, O⟩) :
    ∃ env', semScalar (combSelectSrc N) env = some env'
      ∧ env' "out" = some ⟨.memref 4, fun k =>
          if D.toNat < N then memGetDyn T (4 * D.toNat + k.val) else 0⟩ := by
  obtain ⟨e1, s1, h1⟩ := selInit_run ht hd ho
  obtain ⟨e2, s2, h2⟩ := scanCmds_run (32 * N) N e1 hN h1
  obtain ⟨e3, s3, h3⟩ := storeAll_run h2
  refine ⟨e3, ?_, ?_⟩
  · rw [combSelectSrc, semScalar_seqL_append, s1, Option.bind_some, semScalar_seqL_append,
      s2, Option.bind_some, s3]
  · rw [h3.out]
    congr
    funext k
    exact scanVal_eq T D k N (by omega)

/-! ## 7. The reads-bound judgment on the source -/

/-- The name-to-type map binds the arguments and the four running limbs. -/
structure TyInv (N : Nat) (σ : NameTys) : Prop where
  tbl : σ "tbl" = some (.memref (4 * N))
  d : σ "d" = some (.sword 64)
  out : σ "out" = some (.memref 4)
  acc : ∀ k, σ (accName k) = some (.sword 64)

theorem nameTys_upd_self (σ : NameTys) (x : String) (t : CryptoTy) : σ.upd x t x = some t := by
  simp [NameTys.upd]

theorem nameTys_upd_ne {σ : NameTys} {x y : String} {t : CryptoTy} (h : y ≠ x) :
    σ.upd x t y = σ y := by
  simp [NameTys.upd, h]

theorem TyInv.upd {N : Nat} {σ : NameTys} (h : TyInv N σ) {x : String} (t : CryptoTy)
    (hx : isProtected x = false) : TyInv N (σ.upd x t) := by
  simp only [isProtected, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nameTys_upd_ne (Ne.symm h1)]; exact h.tbl
  · rw [nameTys_upd_ne (Ne.symm h2)]; exact h.d
  · rw [nameTys_upd_ne (Ne.symm h3)]; exact h.out
  · intro k
    have hk : accName k ≠ x := by
      match k with
      | 0 => exact Ne.symm h4
      | 1 => exact Ne.symm h5
      | 2 => exact Ne.symm h6
      | 3 => exact Ne.symm h7
    rw [nameTys_upd_ne hk]; exact h.acc k

theorem TyInv.updAcc {N : Nat} {σ : NameTys} (h : TyInv N σ) (k : Fin 4) :
    TyInv N (σ.upd (accName k) (.sword 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nameTys_upd_ne (Ne.symm (accName_ne_tbl k))]; exact h.tbl
  · rw [nameTys_upd_ne (Ne.symm (accName_ne_d k))]; exact h.d
  · rw [nameTys_upd_ne (Ne.symm (accName_ne_out k))]; exact h.out
  · intro j
    by_cases hj : j = k
    · subst hj; exact nameTys_upd_self _ _ _
    · rw [nameTys_upd_ne (accName_ne hj)]; exact h.acc j

theorem transTotal_seqL_append {a b : List LowCT} :
    ∀ {σ σ₁ σ₂ : NameTys}, TransTotal σ (seqL a) σ₁ → TransTotal σ₁ (seqL b) σ₂ →
      TransTotal σ (seqL (a ++ b)) σ₂ := by
  induction a with
  | nil =>
      intro σ σ₁ σ₂ h1 h2
      cases h1
      exact h2
  | cons c cs ih =>
      intro σ σ₁ σ₂ h1 h2
      cases h1 with
      | rSeq hc hcs => exact .rSeq hc (ih hcs h2)

theorem maskCmds_tt {N : Nat} {σ : NameTys} (h : TyInv N σ) (e : Nat) (he : e < 2 ^ 64) :
    ∃ σ', TransTotal σ (seqL (maskCmds e)) σ' ∧ TyInv N σ' ∧ σ' "m" = some (.sword 64) := by
  have nq : ¬ isTmpName "q" := notTmp_of_head (by decide)
  have nn : ¬ isTmpName "n" := notTmp_of_head (by decide)
  have no : ¬ isTmpName "o" := notTmp_of_head (by decide)
  have nb : ¬ isTmpName "b" := notTmp_of_head (by decide)
  have nm : ¬ isTmpName "m" := notTmp_of_head (by decide)
  have nd : ¬ isTmpName "d" := notTmp_of_head (by decide)
  have h1 := h.upd (x := "q") (.sword 64) rfl
  have h2 := h1.upd (x := "n") (.sword 64) rfl
  have h3 := h2.upd (x := "o") (.sword 64) rfl
  have h4 := h3.upd (x := "b") (.sword 64) rfl
  have h5 := h4.upd (x := "m") (.sword 64) rfl
  refine ⟨_, .rSeq (.rScalarSetExpr "q" _ nq ⟨nd, he⟩ ?_)
    (.rSeq (.rScalarSetExpr "n" _ nn ⟨litClean (by norm_num), nq⟩ ?_)
    (.rSeq (.rScalarSetExpr "o" _ no ⟨⟨nq, nn⟩, ⟨nq, nn⟩⟩ ?_)
    (.rSeq (.rScalarSetExpr "b" _ nb ⟨no, litClean (by norm_num)⟩ ?_)
    (.rSeq (.rScalarSetExpr "m" _ nm ⟨nb, litClean (by norm_num)⟩ ?_) .rSkip)))),
    h5, nameTys_upd_self _ _ _⟩
  · simp [sexprVars, h.d]
  · simp [sexprVars, nameTys_upd_self]
  · simp [sexprVars, nameTys_upd_self, nameTys_upd_ne]
  · simp [sexprVars, nameTys_upd_self]
  · simp [sexprVars, nameTys_upd_self]

theorem cellCmds_tt {N : Nat} {σ : NameTys} (h : TyInv N σ) (hm : σ "m" = some (.sword 64))
    (tw e : Nat) (k : Fin 4) (hi : 4 * e + k.val < 2 ^ 64) :
    ∃ σ', TransTotal σ (seqL (cellCmds tw e k)) σ' ∧ TyInv N σ'
      ∧ σ' "m" = some (.sword 64) ∧ σ' (candName k) = some (.sword 64)
      ∧ ∀ j, j ≠ k → σ' (candName j) = σ (candName j) := by
  have ni : ¬ isTmpName "i" := notTmp_of_head (by decide)
  have nl : ¬ isTmpName "l" := notTmp_of_head (by decide)
  have nm : ¬ isTmpName "m" := notTmp_of_head (by decide)
  have h1 := h.upd (x := "i") (.sword 64) rfl
  have h2 := h1.upd (x := "l") (encodeTy .TU64) rfl
  have h3 := h2.upd (x := candName k) (.sword 64) (candName_prot k)
  have m2 : (σ.upd "i" (.sword 64)).upd "l" (encodeTy .TU64) "m" = some (.sword 64) := by
    rw [nameTys_upd_ne (by decide), nameTys_upd_ne (by decide)]; exact hm
  refine ⟨_, .rSeq (.rScalarSetExpr "i" _ ni (litClean hi) (by simp [sexprVars]))
    (.rSeq (.rArrLoad ⟨"l", .TU64⟩ ⟨"tbl", .TBytes tw⟩ "i" nl
      (by simp [nameTys_upd_ne, h.tbl]) (by simp [nameTys_upd_self]))
    (.rSeq (.rScalarSetExpr (candName k) (.SAnd (.SVar "l") (.SVar "m")) (candName_notTmp k)
      ⟨nl, nm⟩ ?_) .rSkip)), h3, ?_, nameTys_upd_self _ _ _, ?_⟩
  · simp only [sexprVars, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨nameTys_upd_self _ _ _, m2⟩
  · rw [nameTys_upd_ne (Ne.symm (candName_ne_m k))]; exact m2
  · intro j hj
    rw [nameTys_upd_ne (candName_ne hj), nameTys_upd_ne (candName_ne_l j),
      nameTys_upd_ne (candName_ne_i j)]

theorem foldCmd_tt {N : Nat} {σ : NameTys} (h : TyInv N σ) (k : Fin 4)
    (hc : σ (candName k) = some (.sword 64)) :
    TransTotal σ (foldCmd k) (σ.upd (accName k) (.sword 64)) := by
  refine .rScalarSetExpr _ _ (accName_notTmp k) ⟨accName_notTmp k, candName_notTmp k⟩ ?_
  simp only [sexprVars, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.acc k, hc⟩

theorem entryCmds_tt {N : Nat} {σ : NameTys} (h : TyInv N σ) (tw e : Nat)
    (he : 4 * e + 4 ≤ 2 ^ 64) :
    ∃ σ', TransTotal σ (seqL (entryCmds tw e)) σ' ∧ TyInv N σ' := by
  obtain ⟨σ0, t0, h0, m0⟩ := maskCmds_tt h e (by omega)
  obtain ⟨σ1, t1, h1, m1, c1, r1⟩ := cellCmds_tt h0 m0 tw e 0 (by simp; omega)
  obtain ⟨σ2, t2, h2, m2, c2, r2⟩ := cellCmds_tt h1 m1 tw e 1 (by simp; omega)
  obtain ⟨σ3, t3, h3, m3, c3, r3⟩ := cellCmds_tt h2 m2 tw e 2 (by simp; omega)
  obtain ⟨σ4, t4, h4, -, c4, r4⟩ := cellCmds_tt h3 m3 tw e 3 (by simp; omega)
  have c1' := ((r4 0 (by decide)).trans ((r3 0 (by decide)).trans (r2 0 (by decide)))).trans c1
  have c2' := ((r4 1 (by decide)).trans (r3 1 (by decide))).trans c2
  have c3' := (r4 2 (by decide)).trans c3
  have g1 := h4.updAcc 0
  have g2 := g1.updAcc 1
  have g3 := g2.updAcc 2
  have g4 := g3.updAcc 3
  have k1 : σ4.upd (accName 0) (.sword 64) (candName 1) = some (.sword 64) := by
    rw [nameTys_upd_ne (candName_ne_acc 1 0)]; exact c2'
  have k2 : (σ4.upd (accName 0) (.sword 64)).upd (accName 1) (.sword 64) (candName 2)
      = some (.sword 64) := by
    rw [nameTys_upd_ne (candName_ne_acc 2 1), nameTys_upd_ne (candName_ne_acc 2 0)]; exact c3'
  have k3 : ((σ4.upd (accName 0) (.sword 64)).upd (accName 1) (.sword 64)).upd (accName 2)
      (.sword 64) (candName 3) = some (.sword 64) := by
    rw [nameTys_upd_ne (candName_ne_acc 3 2), nameTys_upd_ne (candName_ne_acc 3 1),
      nameTys_upd_ne (candName_ne_acc 3 0)]; exact c4
  refine ⟨_, ?_, g4⟩
  refine transTotal_seqL_append t0 (transTotal_seqL_append t1 (transTotal_seqL_append t2
    (transTotal_seqL_append t3 (transTotal_seqL_append t4 ?_))))
  exact .rSeq (foldCmd_tt h4 0 c1') (.rSeq (foldCmd_tt g1 1 k1)
    (.rSeq (foldCmd_tt g2 2 k2) (.rSeq (foldCmd_tt g3 3 k3) .rSkip)))

theorem scanCmds_tt {N : Nat} (tw : Nat) :
    ∀ (n : Nat) {σ : NameTys}, 4 * n ≤ 2 ^ 64 → TyInv N σ →
      ∃ σ', TransTotal σ (seqL (scanCmds tw n)) σ' ∧ TyInv N σ'
  | 0, σ, _, h => ⟨σ, .rSkip, h⟩
  | n + 1, σ, hn, h => by
      obtain ⟨σ1, t1, h1⟩ := scanCmds_tt tw n (by omega) h
      obtain ⟨σ2, t2, h2⟩ := entryCmds_tt h1 tw n (by omega)
      exact ⟨σ2, by rw [scanCmds]; exact transTotal_seqL_append t1 t2, h2⟩

theorem storeCmds_tt {N : Nat} {σ : NameTys} (h : TyInv N σ) (k : Fin 4) :
    ∃ σ', TransTotal σ (seqL (storeCmds k)) σ' ∧ TyInv N σ' := by
  have ni : ¬ isTmpName "i" := notTmp_of_head (by decide)
  have h1 := h.upd (x := "i") (.sword 64) rfl
  refine ⟨_, .rSeq (.rScalarSetExpr "i" _ ni (litClean (by omega)) (by simp [sexprVars]))
    (.rSeq (.rArrStore ⟨"out", .TBytes 32⟩ "i" ⟨accName k, .TU64⟩
      (notTmp_of_head (by decide)) (by simp [h1.out]) (by simp [h1.acc k])
      (by simp [nameTys_upd_self])) .rSkip), ?_⟩
  refine ⟨?_, ?_, nameTys_upd_self _ _ _, ?_⟩
  · rw [nameTys_upd_ne (by decide)]; exact h1.tbl
  · rw [nameTys_upd_ne (by decide)]; exact h1.d
  · intro j
    rw [nameTys_upd_ne (accName_ne_out j)]; exact h1.acc j

/-- The entry name-to-type map: the three arguments at their context types. -/
def selTys (N : Nat) : NameTys := fun s =>
  if s = "out" then some (.memref 4)
  else if s = "d" then some (.sword 64)
  else if s = "tbl" then some (.memref (4 * N))
  else none

theorem selInit_tt (N : Nat) :
    ∃ σ', TransTotal (selTys N) (seqL selInit) σ' ∧ TyInv N σ' := by
  have z : srcClean (.SLit 0) := litClean (by norm_num)
  refine ⟨_, .rSeq (.rScalarSetExpr "s0" _ (accName_notTmp 0) z (by simp [sexprVars]))
    (.rSeq (.rScalarSetExpr "s1" _ (accName_notTmp 1) z (by simp [sexprVars]))
    (.rSeq (.rScalarSetExpr "s2" _ (accName_notTmp 2) z (by simp [sexprVars]))
    (.rSeq (.rScalarSetExpr "s3" _ (accName_notTmp 3) z (by simp [sexprVars])) .rSkip))), ?_⟩
  refine ⟨by simp [NameTys.upd, selTys], by simp [NameTys.upd, selTys],
    by simp [NameTys.upd, selTys], ?_⟩
  intro k
  match k with
  | 0 | 1 | 2 | 3 => simp [NameTys.upd, accName]

/-- **The source is in the reads-bound covered fragment.** -/
theorem combSelectSrc_transTotal (N : Nat) (hN : 4 * N ≤ 2 ^ 64) :
    ∃ σ', TransTotal (selTys N) (combSelectSrc N) σ' ∧ TyInv N σ' := by
  obtain ⟨σ1, t1, h1⟩ := selInit_tt N
  obtain ⟨σ2, t2, h2⟩ := scanCmds_tt (N := N) (32 * N) N hN h1
  obtain ⟨σ3, t3, h3⟩ := storeCmds_tt h2 0
  obtain ⟨σ4, t4, h4⟩ := storeCmds_tt h3 1
  obtain ⟨σ5, t5, h5⟩ := storeCmds_tt h4 2
  obtain ⟨σ6, t6, h6⟩ := storeCmds_tt h5 3
  exact ⟨σ6, transTotal_seqL_append t1 (transTotal_seqL_append t2
    (transTotal_seqL_append t3 (transTotal_seqL_append t4 (transTotal_seqL_append t5 t6)))),
    h6⟩

/-! ## 8. The front output and its denotation -/

theorem selTys_srcTys (N : Nat) : SrcTys (selTys N) := by
  intro x hx
  simp only [selTys] at hx
  by_cases h1 : x = "out"
  · subst h1; exact notTmp_of_head (by decide)
  · by_cases h2 : x = "d"
    · subst h2; exact notTmp_of_head (by decide)
    · by_cases h3 : x = "tbl"
      · subst h3; exact notTmp_of_head (by decide)
      · simp [h1, h2, h3] at hx

theorem selTys_vmApprox (N : Nat) : VmApprox (selTys N) (selVM N) := by
  intro x t hx
  simp only [selTys] at hx
  by_cases h1 : x = "out"
  · subst h1
    simp only [if_true, Option.some.injEq] at hx
    subst hx
    exact ⟨.here, by simp [selVM, VarMap.bind]; rfl⟩
  · by_cases h2 : x = "d"
    · subst h2
      simp only [if_neg h1, if_true, Option.some.injEq] at hx
      subst hx
      exact ⟨.there .here, by simp [selVM, VarMap.bind]; rfl⟩
    · by_cases h3 : x = "tbl"
      · subst h3
        simp only [if_neg h1, if_neg h2, if_true, Option.some.injEq] at hx
        subst hx
        exact ⟨.there (.there .here), by simp [selVM, VarMap.bind, VarMap.empty]; rfl⟩
      · simp [h1, h2, h3] at hx

/-- The front translates the source and the result lowers to `Com jasminDialect`. -/
theorem combSelectFront_spec (N : Nat) (hN : 4 * N ≤ 2 ^ 64) :
    ∃ (o : DTransOut (selCtx N)) (v : CVar o.Γ' (.memref 4))
      (com : Com catCryptDialect (selCtx N) (.memref 4)),
      translateDialectControl (selVM N) (combSelectSrc N) = some o
      ∧ o.vm.lookup "out" = some ⟨.memref 4, v⟩
      ∧ o.cont (Com.ret (toVIRVar v)) = some com
      ∧ combSelectFront N = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome := by
  obtain ⟨σ', htt, hinv⟩ := combSelectSrc_transTotal N hN
  obtain ⟨o, htr, happ, hcont⟩ :=
    translateDialectControl_total htt (selVM N) (selTys_srcTys N) (selTys_vmApprox N)
  obtain ⟨v, hv⟩ := happ "out" (.memref 4) hinv.out
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar v)) (by rfl)
  refine ⟨o, v, com, htr, hv, hcom, ?_, hlow⟩
  simp only [combSelectFront, htr, hv]
  exact hcom

theorem combSelectFront_isSome (N : Nat) (hN : 4 * N ≤ 2 ^ 64) :
    (combSelectFront N).isSome := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := combSelectFront_spec N hN
  rw [h]; rfl

theorem combSelectLowered_isSome (N : Nat) (hN : 4 * N ≤ 2 ^ 64) :
    (combSelectLowered N).isSome := by
  obtain ⟨_, _, com, _, _, _, h, hlow⟩ := combSelectFront_spec N hN
  obtain ⟨jc, hjc⟩ := Option.isSome_iff_exists.mp hlow
  simp only [combSelectLowered, h, hjc, Option.isSome_some]

/-- The argument valuation: `out ↦ O`, `d ↦ D`, `tbl ↦ T`. -/
def selVal (N : Nat) (O : Fin 4 → BitVec 64) (D : BitVec 64) (T : Fin (4 * N) → BitVec 64) :
    Ctxt.Valuation (d := catCryptDialect) (selCtx N) :=
  .cons O (.cons D (.cons T .nil))

/-- The environment the argument valuation induces through `selVM`. -/
def selEnv (N : Nat) (V : Ctxt.Valuation (d := catCryptDialect) (selCtx N)) : SEnvScalar :=
  fun s => ((selVM N).lookup s).map (fun p => ⟨p.1, (toVIRVar p.2).lookup V⟩)

/-- **Value correctness of the front output.** For every table `T`, index `D`
    and initial output buffer, the program the front produces from
    `combSelectSrc N` returns the buffer `out` with `out[k] = T[4·D + k]` when
    `D < N`, and `out[k] = 0` otherwise. The proof runs the source through the
    scalar waist semantics and transfers it by
    `TranslateDialectScalar.translateDialectControl_denote`. -/
theorem combSelectFront_denote (N : Nat) (hN : 4 * N ≤ 2 ^ 64)
    (O : Fin 4 → BitVec 64) (D : BitVec 64) (T : Fin (4 * N) → BitVec 64) :
    ∃ com, combSelectFront N = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ com.denote (selVal N O D T) = fun k =>
          if D.toNat < N then memGetDyn T (4 * D.toNat + k.val) else 0 := by
  obtain ⟨σ', htt, -⟩ := combSelectSrc_transTotal N hN
  obtain ⟨o, v, com, htr, hv, hcom, hfront, hlow⟩ := combSelectFront_spec N hN
  have hc : ConsistentS (selVM N) (selVal N O D T) (selEnv N (selVal N O D T)) :=
    fun _ => rfl
  have ht : selEnv N (selVal N O D T) "tbl" = some ⟨.memref (4 * N), T⟩ := by
    simp [selEnv, selVM, VarMap.bind, VarMap.empty, selVal]; rfl
  have hd : selEnv N (selVal N O D T) "d" = some ⟨.sword 64, D⟩ := by
    simp [selEnv, selVM, VarMap.bind, selVal]; rfl
  have ho : selEnv N (selVal N O D T) "out" = some ⟨.memref 4, O⟩ := by
    simp [selEnv, selVM, VarMap.bind, selVal]; rfl
  obtain ⟨env', hsem, hout⟩ := combSelectSrc_run N hN ht hd ho
  obtain ⟨V', hc', htail⟩ := translateDialectControl_denote htt.toIsCoveredS (selVM N)
    (selVal N O D T) _ env' o hc htr hsem
  obtain ⟨com', hcom', hden⟩ := htail (Com.ret (toVIRVar v))
  rw [hcom] at hcom'
  cases hcom'
  refine ⟨com, hfront, hlow, ?_⟩
  rw [hden]
  exact ConsistentS.lookup_eq hc' hv hout

theorem memGetDyn_of_lt {n : Nat} (arr : Fin n → BitVec 64) {k : Nat} (hk : k < n) :
    memGetDyn arr k = arr ⟨k, hk⟩ := by
  match n, arr with
  | 0, _ => exact absurd hk (Nat.not_lt_zero k)
  | (p + 1), arr => simp only [memGetDyn]; congr 1; exact Fin.ext (Nat.mod_eq_of_lt hk)

/-- For an in-range index the front output returns table entry `D`. -/
theorem combSelectFront_denote_entry (N : Nat) (hN : 4 * N ≤ 2 ^ 64)
    (O : Fin 4 → BitVec 64) (D : BitVec 64) (T : Fin (4 * N) → BitVec 64)
    (hD : D.toNat < N) :
    ∃ com, combSelectFront N = some com
      ∧ ∀ k : Fin 4, com.denote (selVal N O D T) k
          = T ⟨4 * D.toNat + k.val, by omega⟩ := by
  obtain ⟨com, hf, -, hden⟩ := combSelectFront_denote N hN O D T
  refine ⟨com, hf, fun k => ?_⟩
  rw [hden]
  simp only [if_pos hD]
  exact memGetDyn_of_lt T (by omega)

/-- The 16-entry select: `out[k] = T[4·D + k]` for every `D < 16`. -/
theorem combSelectFront16_denote (O : Fin 4 → BitVec 64) (D : BitVec 64)
    (T : Fin 64 → BitVec 64) (hD : D.toNat < 16) :
    ∃ com, combSelectFront 16 = some com
      ∧ ∀ k : Fin 4, com.denote (selVal 16 O D T) k = T ⟨4 * D.toNat + k.val, by omega⟩ :=
  combSelectFront_denote_entry 16 (by norm_num) O D T hD

/-- The 32-entry select: `out[k] = T[4·D + k]` for every `D < 32`. -/
theorem combSelectFront32_denote (O : Fin 4 → BitVec 64) (D : BitVec 64)
    (T : Fin 128 → BitVec 64) (hD : D.toNat < 32) :
    ∃ com, combSelectFront 32 = some com
      ∧ ∀ k : Fin 4, com.denote (selVal 32 O D T) k = T ⟨4 * D.toNat + k.val, by omega⟩ :=
  combSelectFront_denote_entry 32 (by norm_num) O D T hD

/-- The 64-entry select: `out[k] = T[4·D + k]` for every `D < 64`. -/
theorem combSelectFront64_denote (O : Fin 4 → BitVec 64) (D : BitVec 64)
    (T : Fin 256 → BitVec 64) (hD : D.toNat < 64) :
    ∃ com, combSelectFront 64 = some com
      ∧ ∀ k : Fin 4, com.denote (selVal 64 O D T) k = T ⟨4 * D.toNat + k.val, by omega⟩ :=
  combSelectFront_denote_entry 64 (by norm_num) O D T hD

/-- The three renderings exist: the front and the jasmin lowering succeed at
    `N = 16, 32, 64`. -/
theorem combSelectFrontAsm_isSome :
    combSelectFrontAsm.isSome ∧ combSelect5FrontAsm.isSome ∧ combSelect6FrontAsm.isSome := by
  have h : ∀ N, 4 * N ≤ 2 ^ 64 → ∀ name,
      (combSelectFrontAsmN name N).isSome := by
    intro N hN name
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (combSelectLowered_isSome N hN)
    simp only [combSelectFrontAsmN, OwnedAsm.ownedAsm, hx, Option.map_some,
      Option.isSome_some]
  exact ⟨h 16 (by norm_num) _, h 32 (by norm_num) _, h 64 (by norm_num) _⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
