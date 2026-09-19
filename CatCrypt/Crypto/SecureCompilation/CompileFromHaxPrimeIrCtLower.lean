/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrCt
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront
public import CatCrypt.Crypto.SecureCompilation.Ascent.MultiLimb

/-!
# The prime-IR constant-time select over field limbs

`CompileFromHaxPrimeIrCt` recognizes the `primeir-hax` `CtField` heads and
denotes them over `ZMod p`. This module carries two of those denotations —
`ctSelectDenote` and `ctEqDenote` — to `LowCT` source over the four-limb
little-endian view of a field element, in the shape
`X86Backend.CombSelectCmovFront` uses: the `LowCT` conditional-select
constructor `RSelect`, which `TranslateDialectDirectArms.translateDialectFull`
emits as the `catCryptDialect` comparison select (`bvEq` then word `ite`) and
`VIR.DialectToJasminCom.toJExprD` maps to `JasminOp.cmp .eq 64` and
`JasminOp.select 64`, fused by `X86Backend.LprogCmovTestElim` into `cmp` and a
conditional move.

The limb view is the base-`2^64` limb-array decoder `Transfer.Param.limbVal` of
the ParamTransfer multi-limb split surjection `(Fin n → BitVec 64) ↠ ZMod p`,
re-exported by `Ascent.MultiLimb`, at `n = 4`: `fieldOfLimbs p s` is
`(limbVal 4 s : ZMod p)` and `limbsOfField x` is `toLimbs 4 x.val`, its
canonical section.

## Signatures

```c
void f(const u64 *a, const u64 *b, u64 cond, u64 *out);  // RDI RSI RDX RCX
u64  g(const u64 *a, const u64 *b);                      // RDI RSI
```

`ctSelectSrc` writes `cond ? a : b` limb by limb into `out`; `ctEqSrc` leaves
`1` in `r` when the eight limbs agree pairwise and `0` otherwise.

## Main results

* `fieldOfLimbs`, `limbsOfField`: the four-limb view of a field element and its
  canonical section, with `fieldOfLimbs_limbsOfField` the round trip and
  `limbsOfField_eq_iff` the equality transfer on canonical limbs.
* `ctSelectSrc`, `ctEqSrc`: the two `LowCT` sources.
* `ctSelectSrc_run`, `ctEqSrc_run`: the scalar waist semantics of each source.
* `ctSelectSrc_field`: the field element the select's output limbs decode to is
  `ctSelectDenote` of a condition word in `{0, 1}` and the two decoded operands.
* `ctEqSrc_field`: for canonical limb arrays the equality test's truth value is
  `ctEqDenote`.
* `ctSelectSrc_transTotal`, `ctEqSrc_transTotal`: both sources are in the
  reads-bound covered fragment `TranslateDialectTotality.TransTotal`.
* `ctSelectFront_denote`, `ctEqFront_denote`: each front output lowers to
  `Com jasminDialect` and denotes the waist value.
* `ctSelectFront_denote_field`, `ctEqFront_denote_field`: the same two field-level
  statements about the front outputs.
* `ctSelectAsm`, `ctSelectLines`, `ctSelectClean`, `ctSelectHasCmov`: the owned
  AT&T rendering of the select and its line count, `UNHANDLED`-freedom and
  `cmov` presence, with `ctSelectAsm_isSome` for the rendering's existence.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrCtLower

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
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
  (seqL setE notTmp_of_head litClean upd_ne' readU64_of reader_of setE_run arrLoad_eq
   arrStore_eq semScalar_seqL_cons semScalar_seqL_nil semScalar_seqL_append
   transTotal_seqL_append nameTys_upd_self nameTys_upd_ne memGetDyn_of_lt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront (cmovFuseLprog)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrCt
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType)

/-! ## 1. The four-limb view of a field element

`limbVal 4 s` is the base-`2^64` little-endian value of the four words `s`, and
`toLimbs 4 v` splits a natural number into those four words. The field view
reduces that value modulo `p`. -/

/-- The field element a four-word little-endian limb array denotes. -/
def fieldOfLimbs (p : Nat) (s : Fin 4 → BitVec 64) : ZMod p :=
  ((Transfer.Param.limbVal 4 s : Nat) : ZMod p)

/-- The canonical four-limb encoding of a field element: the little-endian split
    of its representative in `[0, p)`. -/
def limbsOfField {p : Nat} (x : ZMod p) : Fin 4 → BitVec 64 := Transfer.Param.toLimbs 4 x.val

/-- **The round trip.** For `p ≤ 2^256` the canonical encoding decodes to the
    field element it encodes. -/
theorem fieldOfLimbs_limbsOfField {p : Nat} [NeZero p] (hp : p ≤ 2 ^ (64 * 4))
    (x : ZMod p) : fieldOfLimbs p (limbsOfField x) = x := by
  unfold fieldOfLimbs limbsOfField
  rw [Transfer.Param.limbVal_toLimbs 4 x.val (lt_of_lt_of_le (ZMod.val_lt x) hp)]
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- **Equality transfer on canonical limbs.** For `p ≤ 2^256` two canonical
    encodings are equal exactly when the field elements are. -/
theorem limbsOfField_eq_iff {p : Nat} [NeZero p] (hp : p ≤ 2 ^ (64 * 4))
    (x y : ZMod p) : limbsOfField x = limbsOfField y ↔ x = y := by
  constructor
  · intro h
    rw [← fieldOfLimbs_limbsOfField hp x, ← fieldOfLimbs_limbsOfField hp y, h]
  · rintro rfl; rfl

/-! ## 2. The two sources -/

/-- The condition word `c ⊕ 1`, zero exactly when `c = 1`. -/
def condCmd : LowCT := setE "q" (.SXor (.SVar "c") (.SLit 1))

/-- Limb `k` of the select: load `a[k]` and `b[k]`, take `a[k]` when the
    condition word is zero, and store the result to `out[k]`. -/
def selLimbCmds (k : Fin 4) : List LowCT :=
  [ setE "i" (.SLit k.val)
  , .RArrLoad ⟨"u", .TU64⟩ ⟨"a", .TBytes 32⟩ "i"
  , .RArrLoad ⟨"v", .TU64⟩ ⟨"b", .TBytes 32⟩ "i"
  , .RSelect ⟨"t", .TU64⟩ "q" ⟨"u", .TU64⟩ ⟨"v", .TU64⟩
  , .RArrStore ⟨"out", .TBytes 32⟩ "i" ⟨"t", .TU64⟩ ]

/-- The constant-time field select over the arguments `a`, `b` (four
    little-endian words each), the condition `c` (a truth value in `{0, 1}`) and
    `out` (four words): both operands are read on every call and the condition
    enters only as a conditional move. -/
def ctSelectSrc : LowCT :=
  seqL (condCmd :: (selLimbCmds 0 ++ (selLimbCmds 1 ++ (selLimbCmds 2 ++ selLimbCmds 3))))

/-- The running truth value and the zero it is cleared to. -/
def eqInit : List LowCT := [setE "r" (.SLit 1), setE "w" (.SLit 0)]

/-- Limb `k` of the equality test: load `a[k]` and `b[k]`, and keep the running
    truth value when they agree, clear it otherwise. -/
def eqLimbCmds (k : Fin 4) : List LowCT :=
  [ setE "i" (.SLit k.val)
  , .RArrLoad ⟨"u", .TU64⟩ ⟨"a", .TBytes 32⟩ "i"
  , .RArrLoad ⟨"v", .TU64⟩ ⟨"b", .TBytes 32⟩ "i"
  , setE "q" (.SXor (.SVar "u") (.SVar "v"))
  , .RSelect ⟨"r", .TU64⟩ "q" ⟨"r", .TU64⟩ ⟨"w", .TU64⟩ ]

/-- The constant-time field equality over the arguments `a` and `b` (four
    little-endian words each), leaving the truth value in `r`: all four limb
    pairs are compared on every call. -/
def ctEqSrc : LowCT :=
  seqL (eqInit ++ (eqLimbCmds 0 ++ (eqLimbCmds 1 ++ (eqLimbCmds 2 ++ eqLimbCmds 3))))

/-! ## 3. Waist semantics of the select -/

/-- The environment binds the two operands, the condition word and the output
    buffer. -/
structure SelInv (A B O : Fin 4 → BitVec 64) (C : BitVec 64) (env : SEnvScalar) : Prop where
  a : env "a" = some ⟨.memref 4, A⟩
  b : env "b" = some ⟨.memref 4, B⟩
  c : env "c" = some ⟨.sword 64, C⟩
  out : env "out" = some ⟨.memref 4, O⟩

/-- The names `SelInv` reads. -/
def selProt (x : String) : Bool := x == "a" || x == "b" || x == "c" || x == "out"

theorem SelInv.frame {A B O : Fin 4 → BitVec 64} {C : BitVec 64} {env env' : SEnvScalar}
    {x : String} (h : SelInv A B O C env)
    (hf : ∀ s, ¬ isTmpName s → s ≠ x → env' s = env s) (hx : selProt x = false) :
    SelInv A B O C env' := by
  simp only [selProt, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h1)]; exact h.a
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h2)]; exact h.b
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h3)]; exact h.c
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h4)]; exact h.out

/-- The condition command binds `q` to `C ⊕ 1`. -/
theorem condCmd_run {A B O : Fin 4 → BitVec 64} {C : BitVec 64} {env : SEnvScalar}
    (h : SelInv A B O C env) :
    ∃ env', semScalar condCmd env = some env' ∧ SelInv A B O C env'
      ∧ env' "q" = some ⟨.sword 64, C ^^^ 1#64⟩ := by
  have nc : ¬ isTmpName "c" := notTmp_of_head (by decide)
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "q") (e := .SXor (.SVar "c") (.SLit 1))
    (env := env) ⟨nc, litClean (by norm_num)⟩ (by simp [sexprVars, readU64_of h.c])
  refine ⟨e1, s1, h.frame f1 rfl, ?_⟩
  rw [v1]
  simp only [SExpr.evalBV, reader_of h.c]

/-- A literal limb index reads the limb it names. -/
theorem memGet_limb (A : Fin 4 → BitVec 64) (k : Fin 4) :
    memGetDyn A (BitVec.ofNat 64 k.val).toNat = A k := by
  have hk : (BitVec.ofNat 64 k.val).toNat = k.val := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hk, memGetDyn_of_lt A k.isLt]

/-- One limb of the select writes `selectWord Q (A k) (B k)` to `out[k]` and
    keeps the condition word. -/
theorem selLimbCmds_run {A B O : Fin 4 → BitVec 64} {C Q : BitVec 64} {env : SEnvScalar}
    (h : SelInv A B O C env) (hq : env "q" = some ⟨.sword 64, Q⟩) (k : Fin 4) :
    ∃ env', semScalar (seqL (selLimbCmds k)) env = some env'
      ∧ SelInv A B (memSetDyn O k.val (selectWord Q (A k) (B k))) C env'
      ∧ env' "q" = some ⟨.sword 64, Q⟩ := by
  have nq : ¬ isTmpName "q" := notTmp_of_head (by decide)
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "i") (e := .SLit k.val) (env := env)
    (litClean (by omega)) (by simp [sexprVars])
  have h1 := h.frame f1 rfl
  have q1 := (f1 "q" nq (by decide)).trans hq
  have v1' : e1 "i" = some ⟨.sword 64, BitVec.ofNat 64 k.val⟩ := v1
  have s2 := arrLoad_eq (dstN := "u") (tw := .TBytes 32) h1.a v1'
  set e2 := e1.upd "u" (t := .sword 64) (memGetDyn A (BitVec.ofNat 64 k.val).toNat) with he2
  have f2 : ∀ s, ¬ isTmpName s → s ≠ "u" → e2 s = e1 s := fun s _ hs => upd_ne' hs
  have h2 := h1.frame f2 rfl
  have q2 := (f2 "q" nq (by decide)).trans q1
  have i2 : e2 "i" = some ⟨.sword 64, BitVec.ofNat 64 k.val⟩ :=
    (f2 "i" (notTmp_of_head (by decide)) (by decide)).trans v1'
  have u2 : e2 "u" = some ⟨.sword 64, A k⟩ := by
    rw [he2, SEnvScalar.upd, if_pos rfl, memGet_limb]
  have s3 := arrLoad_eq (dstN := "v") (tw := .TBytes 32) h2.b i2
  set e3 := e2.upd "v" (t := .sword 64) (memGetDyn B (BitVec.ofNat 64 k.val).toNat) with he3
  have f3 : ∀ s, ¬ isTmpName s → s ≠ "v" → e3 s = e2 s := fun s _ hs => upd_ne' hs
  have h3 := h2.frame f3 rfl
  have q3 := (f3 "q" nq (by decide)).trans q2
  have i3 : e3 "i" = some ⟨.sword 64, BitVec.ofNat 64 k.val⟩ :=
    (f3 "i" (notTmp_of_head (by decide)) (by decide)).trans i2
  have u3 : e3 "u" = some ⟨.sword 64, A k⟩ :=
    (f3 "u" (notTmp_of_head (by decide)) (by decide)).trans u2
  have v3 : e3 "v" = some ⟨.sword 64, B k⟩ := by
    rw [he3, SEnvScalar.upd, if_pos rfl, memGet_limb]
  have s4 := semScalar_rSelect_word ⟨"t", .TU64⟩ "q" ⟨"u", .TU64⟩ ⟨"v", .TU64⟩
    e3 Q (A k) (B k) rfl q3 u3 v3
  set e4 := e3.upd "t" (t := .sword 64) (selectWord Q (A k) (B k)) with he4
  have f4 : ∀ s, ¬ isTmpName s → s ≠ "t" → e4 s = e3 s := fun s _ hs => upd_ne' hs
  have h4 := h3.frame f4 rfl
  have q4 := (f4 "q" nq (by decide)).trans q3
  have i4 : e4 "i" = some ⟨.sword 64, BitVec.ofNat 64 k.val⟩ :=
    (f4 "i" (notTmp_of_head (by decide)) (by decide)).trans i3
  have t4 : e4 "t" = some ⟨.sword 64, selectWord Q (A k) (B k)⟩ := by
    rw [he4, SEnvScalar.upd, if_pos rfl]
  have s5 := arrStore_eq (arrN := "out") (srcN := "t") h4.out i4 t4
  have hk : (BitVec.ofNat 64 k.val).toNat = k.val := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨e4.upd "out" (t := .memref 4)
    (memSetDyn O (BitVec.ofNat 64 k.val).toNat (selectWord Q (A k) (B k))), ?_,
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [selLimbCmds, semScalar_seqL_cons s1, semScalar_seqL_cons s2, semScalar_seqL_cons s3,
      semScalar_seqL_cons s4, semScalar_seqL_cons s5, semScalar_seqL_nil]
  · rw [upd_ne' (by decide)]; exact h4.a
  · rw [upd_ne' (by decide)]; exact h4.b
  · rw [upd_ne' (by decide)]; exact h4.c
  · rw [hk]; simp [SEnvScalar.upd]
  · rw [upd_ne' (by decide)]; exact q4

/-- The limbs the select leaves in `out`. -/
def ctSelectVal (Q : BitVec 64) (A B : Fin 4 → BitVec 64) : Fin 4 → BitVec 64 :=
  fun k => selectWord Q (A k) (B k)

/-- **Waist semantics of the select.** From an environment binding the two
    operands, the condition word and the output buffer, the source runs to
    completion and leaves `out[k] = a[k]` when `c = 1` and `out[k] = b[k]`
    otherwise. -/
theorem ctSelectSrc_run {A B O : Fin 4 → BitVec 64} {C : BitVec 64} {env : SEnvScalar}
    (ha : env "a" = some ⟨.memref 4, A⟩) (hb : env "b" = some ⟨.memref 4, B⟩)
    (hc : env "c" = some ⟨.sword 64, C⟩) (ho : env "out" = some ⟨.memref 4, O⟩) :
    ∃ env', semScalar ctSelectSrc env = some env'
      ∧ env' "out" = some ⟨.memref 4, ctSelectVal (C ^^^ 1#64) A B⟩ := by
  have h0 : SelInv A B O C env := ⟨ha, hb, hc, ho⟩
  obtain ⟨e0, s0, i0, q0⟩ := condCmd_run h0
  obtain ⟨e1, s1, i1, q1⟩ := selLimbCmds_run i0 q0 0
  obtain ⟨e2, s2, i2, q2⟩ := selLimbCmds_run i1 q1 1
  obtain ⟨e3, s3, i3, q3⟩ := selLimbCmds_run i2 q2 2
  obtain ⟨e4, s4, i4, -⟩ := selLimbCmds_run i3 q3 3
  refine ⟨e4, ?_, ?_⟩
  · rw [ctSelectSrc, semScalar_seqL_cons s0, semScalar_seqL_append, s1, Option.bind_some,
      semScalar_seqL_append, s2, Option.bind_some, semScalar_seqL_append, s3,
      Option.bind_some, s4]
  · rw [i4.out]
    congr 1
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext j
    match j with
    | 0 | 1 | 2 | 3 => simp [memSetDyn, ctSelectVal]

/-! ## 4. The field-level value of the select -/

/-- The select at a condition word in `{0, 1}` returns one of its two operands
    whole. -/
theorem ctSelectVal_eq (A B : Fin 4 → BitVec 64) (C : BitVec 64) (hC : C = 0#64 ∨ C = 1#64) :
    ctSelectVal (C ^^^ 1#64) A B = if C = 1#64 then A else B := by
  rcases hC with rfl | rfl
  · funext k; simp [ctSelectVal, selectWord]
  · funext k; simp [ctSelectVal, selectWord]

/-- **The select computes `ct_select` over the limb view.** For a condition word
    in `{0, 1}`, the field element the output limbs decode to is
    `ctSelectDenote` of the condition and the two decoded operands. -/
theorem ctSelectSrc_field {p : Nat} {A B O : Fin 4 → BitVec 64} {C : BitVec 64}
    {env : SEnvScalar} (hC : C = 0#64 ∨ C = 1#64)
    (ha : env "a" = some ⟨.memref 4, A⟩) (hb : env "b" = some ⟨.memref 4, B⟩)
    (hc : env "c" = some ⟨.sword 64, C⟩) (ho : env "out" = some ⟨.memref 4, O⟩) :
    ∃ env' S, semScalar ctSelectSrc env = some env'
      ∧ env' "out" = some ⟨.memref 4, S⟩
      ∧ fieldOfLimbs p S = ctSelectDenote C.toNat (fieldOfLimbs p A) (fieldOfLimbs p B) := by
  obtain ⟨env', hrun, hout⟩ := ctSelectSrc_run ha hb hc ho
  refine ⟨env', _, hrun, hout, ?_⟩
  rw [ctSelectVal_eq A B C hC]
  rcases hC with rfl | rfl
  · simp [ctSelectDenote]
  · simp [ctSelectDenote]

/-! ## 5. Waist semantics of the equality test -/

/-- The environment binds the two operands, the running truth value and the
    zero it is cleared to. -/
structure EqInv (A B : Fin 4 → BitVec 64) (R : BitVec 64) (env : SEnvScalar) : Prop where
  a : env "a" = some ⟨.memref 4, A⟩
  b : env "b" = some ⟨.memref 4, B⟩
  r : env "r" = some ⟨.sword 64, R⟩
  w : env "w" = some ⟨.sword 64, 0#64⟩

/-- The names `EqInv` reads. -/
def eqProt (x : String) : Bool := x == "a" || x == "b" || x == "r" || x == "w"

theorem EqInv.frame {A B : Fin 4 → BitVec 64} {R : BitVec 64} {env env' : SEnvScalar}
    {x : String} (h : EqInv A B R env)
    (hf : ∀ s, ¬ isTmpName s → s ≠ x → env' s = env s) (hx : eqProt x = false) :
    EqInv A B R env' := by
  simp only [eqProt, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h1)]; exact h.a
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h2)]; exact h.b
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h3)]; exact h.r
  · rw [hf _ (notTmp_of_head (by decide)) (Ne.symm h4)]; exact h.w

/-- The initialisation sets the running truth value to `1` and binds the
    zero. -/
theorem eqInit_run {A B : Fin 4 → BitVec 64} {env : SEnvScalar}
    (ha : env "a" = some ⟨.memref 4, A⟩) (hb : env "b" = some ⟨.memref 4, B⟩) :
    ∃ env', semScalar (seqL eqInit) env = some env' ∧ EqInv A B 1#64 env' := by
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "r") (e := .SLit 1) (env := env)
    (litClean (by norm_num)) (by simp [sexprVars])
  obtain ⟨e2, s2, v2, f2⟩ := setE_run (x := "w") (e := .SLit 0) (env := e1)
    (litClean (by norm_num)) (by simp [sexprVars])
  refine ⟨e2, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [eqInit, semScalar_seqL_cons s1, semScalar_seqL_cons s2, semScalar_seqL_nil]
  · rw [f2 _ (notTmp_of_head (by decide)) (by decide),
      f1 _ (notTmp_of_head (by decide)) (by decide)]; exact ha
  · rw [f2 _ (notTmp_of_head (by decide)) (by decide),
      f1 _ (notTmp_of_head (by decide)) (by decide)]; exact hb
  · rw [f2 _ (notTmp_of_head (by decide)) (by decide), v1]; rfl
  · rw [v2]; rfl

/-- One limb of the equality test keeps the running truth value when the two
    limbs agree and clears it otherwise. -/
theorem eqLimbCmds_run {A B : Fin 4 → BitVec 64} {R : BitVec 64} {env : SEnvScalar}
    (h : EqInv A B R env) (k : Fin 4) :
    ∃ env', semScalar (seqL (eqLimbCmds k)) env = some env'
      ∧ EqInv A B (selectWord (A k ^^^ B k) R 0#64) env' := by
  obtain ⟨e1, s1, v1, f1⟩ := setE_run (x := "i") (e := .SLit k.val) (env := env)
    (litClean (by omega)) (by simp [sexprVars])
  have h1 := h.frame f1 rfl
  have v1' : e1 "i" = some ⟨.sword 64, BitVec.ofNat 64 k.val⟩ := v1
  have s2 := arrLoad_eq (dstN := "u") (tw := .TBytes 32) h1.a v1'
  set e2 := e1.upd "u" (t := .sword 64) (memGetDyn A (BitVec.ofNat 64 k.val).toNat) with he2
  have f2 : ∀ s, ¬ isTmpName s → s ≠ "u" → e2 s = e1 s := fun s _ hs => upd_ne' hs
  have h2 := h1.frame f2 rfl
  have i2 : e2 "i" = some ⟨.sword 64, BitVec.ofNat 64 k.val⟩ :=
    (f2 "i" (notTmp_of_head (by decide)) (by decide)).trans v1'
  have u2 : e2 "u" = some ⟨.sword 64, A k⟩ := by
    rw [he2, SEnvScalar.upd, if_pos rfl, memGet_limb]
  have s3 := arrLoad_eq (dstN := "v") (tw := .TBytes 32) h2.b i2
  set e3 := e2.upd "v" (t := .sword 64) (memGetDyn B (BitVec.ofNat 64 k.val).toNat) with he3
  have f3 : ∀ s, ¬ isTmpName s → s ≠ "v" → e3 s = e2 s := fun s _ hs => upd_ne' hs
  have h3 := h2.frame f3 rfl
  have u3 : e3 "u" = some ⟨.sword 64, A k⟩ :=
    (f3 "u" (notTmp_of_head (by decide)) (by decide)).trans u2
  have v3 : e3 "v" = some ⟨.sword 64, B k⟩ := by
    rw [he3, SEnvScalar.upd, if_pos rfl, memGet_limb]
  obtain ⟨e4, s4, v4, f4⟩ := setE_run (x := "q") (e := .SXor (.SVar "u") (.SVar "v"))
    (env := e3) ⟨notTmp_of_head (by decide), notTmp_of_head (by decide)⟩
    (by simp [sexprVars, readU64_of u3, readU64_of v3])
  have h4 := h3.frame f4 rfl
  have q4 : e4 "q" = some ⟨.sword 64, A k ^^^ B k⟩ := by
    rw [v4]; simp only [SExpr.evalBV, reader_of u3, reader_of v3]
  have s5 := semScalar_rSelect_word ⟨"r", .TU64⟩ "q" ⟨"r", .TU64⟩ ⟨"w", .TU64⟩
    e4 (A k ^^^ B k) R 0#64 rfl q4 h4.r h4.w
  refine ⟨e4.upd "r" (t := .sword 64) (selectWord (A k ^^^ B k) R 0#64), ?_,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [eqLimbCmds, semScalar_seqL_cons s1, semScalar_seqL_cons s2, semScalar_seqL_cons s3,
      semScalar_seqL_cons s4, semScalar_seqL_cons s5, semScalar_seqL_nil]
  · rw [upd_ne' (by decide)]; exact h4.a
  · rw [upd_ne' (by decide)]; exact h4.b
  · simp [SEnvScalar.upd]
  · rw [upd_ne' (by decide)]; exact h4.w

/-- The truth value the equality test leaves in `r`. -/
def ctEqVal (A B : Fin 4 → BitVec 64) : BitVec 64 :=
  selectWord (A 3 ^^^ B 3) (selectWord (A 2 ^^^ B 2)
    (selectWord (A 1 ^^^ B 1) (selectWord (A 0 ^^^ B 0) 1#64 0#64) 0#64) 0#64) 0#64

/-- The chained select is `1` exactly when the four limb pairs agree. -/
theorem ctEqVal_eq (A B : Fin 4 → BitVec 64) :
    ctEqVal A B = if A = B then 1#64 else 0#64 := by
  have hiff : A = B ↔ (A 0 = B 0 ∧ A 1 = B 1 ∧ A 2 = B 2 ∧ A 3 = B 3) := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
    · rintro ⟨h0, h1, h2, h3⟩
      funext k
      match k with
      | 0 => exact h0
      | 1 => exact h1
      | 2 => exact h2
      | 3 => exact h3
  rw [ctEqVal, if_congr hiff rfl rfl]
  simp only [selectWord, BitVec.xor_eq_zero_iff]
  by_cases h0 : A 0 = B 0 <;> by_cases h1 : A 1 = B 1 <;> by_cases h2 : A 2 = B 2 <;>
    by_cases h3 : A 3 = B 3 <;> simp [h0, h1, h2, h3]

/-- **Waist semantics of the equality test.** From an environment binding the
    two operands, the source runs to completion and leaves `1` in `r` when the
    eight limbs agree pairwise, `0` otherwise. -/
theorem ctEqSrc_run {A B : Fin 4 → BitVec 64} {env : SEnvScalar}
    (ha : env "a" = some ⟨.memref 4, A⟩) (hb : env "b" = some ⟨.memref 4, B⟩) :
    ∃ env', semScalar ctEqSrc env = some env'
      ∧ env' "r" = some ⟨.sword 64, ctEqVal A B⟩ := by
  obtain ⟨e0, s0, i0⟩ := eqInit_run ha hb
  obtain ⟨e1, s1, i1⟩ := eqLimbCmds_run i0 0
  obtain ⟨e2, s2, i2⟩ := eqLimbCmds_run i1 1
  obtain ⟨e3, s3, i3⟩ := eqLimbCmds_run i2 2
  obtain ⟨e4, s4, i4⟩ := eqLimbCmds_run i3 3
  refine ⟨e4, ?_, ?_⟩
  · rw [ctEqSrc, semScalar_seqL_append, s0, Option.bind_some, semScalar_seqL_append, s1,
      Option.bind_some, semScalar_seqL_append, s2, Option.bind_some,
      semScalar_seqL_append, s3, Option.bind_some, s4]
  · rw [i4.r]; rfl

/-- **The equality test computes `ct_eq` over the limb view.** For canonical
    limb arrays — the sections `limbsOfField x`, `limbsOfField y` — and
    `p ≤ 2^256`, the truth value the source leaves in `r` is `ctEqDenote x y`. -/
theorem ctEqSrc_field {p : Nat} [NeZero p] (hp : p ≤ 2 ^ (64 * 4)) (x y : ZMod p)
    {env : SEnvScalar} (ha : env "a" = some ⟨.memref 4, limbsOfField x⟩)
    (hb : env "b" = some ⟨.memref 4, limbsOfField y⟩) :
    ∃ env' R, semScalar ctEqSrc env = some env' ∧ env' "r" = some ⟨.sword 64, R⟩
      ∧ R.toNat = ctEqDenote x y := by
  obtain ⟨env', hrun, hr⟩ := ctEqSrc_run ha hb
  refine ⟨env', _, hrun, hr, ?_⟩
  rw [ctEqVal_eq, if_congr (limbsOfField_eq_iff hp x y) rfl rfl, ctEqDenote]
  by_cases h : x = y <;> simp [h]

/-! ## 6. The reads-bound judgment -/

/-- A `u64`-typed location encodes to the 64-bit word type. -/
theorem encodeTy_locDst_TU64 (x : String) :
    encodeTy (Located.mk x TowerType.TU64).locDst = CryptoTy.sword 64 := rfl

/-- The name-to-type map of the select binds the four arguments at their context
    types. -/
structure SelTyInv (σ : NameTys) : Prop where
  a : σ "a" = some (.memref 4)
  b : σ "b" = some (.memref 4)
  c : σ "c" = some (.sword 64)
  out : σ "out" = some (.memref 4)

theorem SelTyInv.upd {σ : NameTys} (h : SelTyInv σ) {x : String} (t : CryptoTy)
    (hx : selProt x = false) : SelTyInv (σ.upd x t) := by
  simp only [selProt, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
  exact ⟨by rw [nameTys_upd_ne (Ne.symm h1)]; exact h.a,
    by rw [nameTys_upd_ne (Ne.symm h2)]; exact h.b,
    by rw [nameTys_upd_ne (Ne.symm h3)]; exact h.c,
    by rw [nameTys_upd_ne (Ne.symm h4)]; exact h.out⟩

theorem SelTyInv.updOut {σ : NameTys} (h : SelTyInv σ) :
    SelTyInv (σ.upd "out" (.memref 4)) :=
  ⟨by rw [nameTys_upd_ne (by decide)]; exact h.a,
   by rw [nameTys_upd_ne (by decide)]; exact h.b,
   by rw [nameTys_upd_ne (by decide)]; exact h.c,
   nameTys_upd_self _ _ _⟩

theorem condCmd_tt {σ : NameTys} (h : SelTyInv σ) :
    ∃ σ', TransTotal σ condCmd σ' ∧ SelTyInv σ' ∧ σ' "q" = some (.sword 64) := by
  refine ⟨_, .rScalarSetExpr "q" _ (notTmp_of_head (by decide))
    ⟨notTmp_of_head (by decide), litClean (by norm_num)⟩ ?_,
    h.upd (x := "q") (.sword 64) rfl, nameTys_upd_self _ _ _⟩
  simp [sexprVars, h.c]

theorem selLimbCmds_tt {σ : NameTys} (h : SelTyInv σ) (hq : σ "q" = some (.sword 64))
    (k : Fin 4) :
    ∃ σ', TransTotal σ (seqL (selLimbCmds k)) σ' ∧ SelTyInv σ'
      ∧ σ' "q" = some (.sword 64) := by
  have h1 := h.upd (x := "i") (.sword 64) rfl
  have h2 := h1.upd (x := "u") (encodeTy TowerType.TU64) rfl
  have h3 := h2.upd (x := "v") (encodeTy TowerType.TU64) rfl
  have h4 := h3.upd (x := "t") (.sword 64) rfl
  have q1 : σ.upd "i" (.sword 64) "q" = some (.sword 64) := by
    rw [nameTys_upd_ne (by decide)]; exact hq
  have q2 : (σ.upd "i" (.sword 64)).upd "u" (encodeTy TowerType.TU64) "q"
      = some (.sword 64) := by rw [nameTys_upd_ne (by decide)]; exact q1
  have q3 : ((σ.upd "i" (.sword 64)).upd "u" (encodeTy TowerType.TU64)).upd "v"
      (encodeTy TowerType.TU64) "q" = some (.sword 64) := by
    rw [nameTys_upd_ne (by decide)]; exact q2
  have q4 : (((σ.upd "i" (.sword 64)).upd "u" (encodeTy TowerType.TU64)).upd "v"
      (encodeTy TowerType.TU64)).upd "t" (.sword 64) "q" = some (.sword 64) := by
    rw [nameTys_upd_ne (by decide)]; exact q3
  refine ⟨_, .rSeq (.rScalarSetExpr "i" _ (notTmp_of_head (by decide))
      (litClean (by omega)) (by simp [sexprVars]))
    (.rSeq (.rArrLoad ⟨"u", .TU64⟩ ⟨"a", .TBytes 32⟩ "i" (notTmp_of_head (by decide))
        (by simp [nameTys_upd_ne, h.a]) (by simp [nameTys_upd_self]))
    (.rSeq (.rArrLoad ⟨"v", .TU64⟩ ⟨"b", .TBytes 32⟩ "i" (notTmp_of_head (by decide))
        (by simp [nameTys_upd_ne, h.b]) (by simp [nameTys_upd_ne, nameTys_upd_self]))
    (.rSeq (.rSelect ⟨"t", .TU64⟩ "q" ⟨"u", .TU64⟩ ⟨"v", .TU64⟩
        (notTmp_of_head (by decide)) rfl q3
        (by simp [nameTys_upd_ne, nameTys_upd_self, encodeTy_locDst_TU64])
        (by simp [nameTys_upd_self, encodeTy_locDst_TU64]))
    (.rSeq (.rArrStore ⟨"out", .TBytes 32⟩ "i" ⟨"t", .TU64⟩ (notTmp_of_head (by decide))
        (by simp [h4.out]) (by simp [nameTys_upd_self])
        (by simp [nameTys_upd_ne, nameTys_upd_self])) .rSkip)))),
    h4.updOut, ?_⟩
  rw [nameTys_upd_ne (by decide)]; exact q4

/-- The entry name-to-type map of the select. -/
def selTys : NameTys := fun s =>
  if s = "out" then some (.memref 4)
  else if s = "c" then some (.sword 64)
  else if s = "b" then some (.memref 4)
  else if s = "a" then some (.memref 4)
  else none

theorem selTys_inv : SelTyInv selTys := ⟨rfl, rfl, rfl, rfl⟩

/-- **The select source is in the reads-bound covered fragment.** -/
theorem ctSelectSrc_transTotal :
    ∃ σ', TransTotal selTys ctSelectSrc σ' ∧ SelTyInv σ' := by
  obtain ⟨σ0, t0, h0, q0⟩ := condCmd_tt selTys_inv
  obtain ⟨σ1, t1, h1, q1⟩ := selLimbCmds_tt h0 q0 0
  obtain ⟨σ2, t2, h2, q2⟩ := selLimbCmds_tt h1 q1 1
  obtain ⟨σ3, t3, h3, q3⟩ := selLimbCmds_tt h2 q2 2
  obtain ⟨σ4, t4, h4, -⟩ := selLimbCmds_tt h3 q3 3
  exact ⟨σ4, .rSeq t0 (transTotal_seqL_append t1 (transTotal_seqL_append t2
    (transTotal_seqL_append t3 t4))), h4⟩

/-- The name-to-type map of the equality test binds the two arguments, the
    running truth value and the zero. -/
structure EqTyInv (σ : NameTys) : Prop where
  a : σ "a" = some (.memref 4)
  b : σ "b" = some (.memref 4)
  r : σ "r" = some (.sword 64)
  w : σ "w" = some (.sword 64)

theorem EqTyInv.upd {σ : NameTys} (h : EqTyInv σ) {x : String} (t : CryptoTy)
    (hx : eqProt x = false) : EqTyInv (σ.upd x t) := by
  simp only [eqProt, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hx
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
  exact ⟨by rw [nameTys_upd_ne (Ne.symm h1)]; exact h.a,
    by rw [nameTys_upd_ne (Ne.symm h2)]; exact h.b,
    by rw [nameTys_upd_ne (Ne.symm h3)]; exact h.r,
    by rw [nameTys_upd_ne (Ne.symm h4)]; exact h.w⟩

theorem EqTyInv.updR {σ : NameTys} (h : EqTyInv σ) : EqTyInv (σ.upd "r" (.sword 64)) :=
  ⟨by rw [nameTys_upd_ne (by decide)]; exact h.a,
   by rw [nameTys_upd_ne (by decide)]; exact h.b,
   nameTys_upd_self _ _ _,
   by rw [nameTys_upd_ne (by decide)]; exact h.w⟩

/-- The entry name-to-type map of the equality test. -/
def eqTys : NameTys := fun s =>
  if s = "b" then some (.memref 4)
  else if s = "a" then some (.memref 4)
  else none

theorem eqInit_tt : ∃ σ', TransTotal eqTys (seqL eqInit) σ' ∧ EqTyInv σ' := by
  refine ⟨_, .rSeq (.rScalarSetExpr "r" _ (notTmp_of_head (by decide))
      (litClean (by norm_num)) (by simp [sexprVars]))
    (.rSeq (.rScalarSetExpr "w" _ (notTmp_of_head (by decide))
      (litClean (by norm_num)) (by simp [sexprVars])) .rSkip), ?_⟩
  exact ⟨by simp [NameTys.upd, eqTys], by simp [NameTys.upd, eqTys],
    by simp [NameTys.upd], by simp [NameTys.upd]⟩

theorem eqLimbCmds_tt {σ : NameTys} (h : EqTyInv σ) (k : Fin 4) :
    ∃ σ', TransTotal σ (seqL (eqLimbCmds k)) σ' ∧ EqTyInv σ' := by
  have h1 := h.upd (x := "i") (.sword 64) rfl
  have h2 := h1.upd (x := "u") (encodeTy TowerType.TU64) rfl
  have h3 := h2.upd (x := "v") (encodeTy TowerType.TU64) rfl
  have h4 := h3.upd (x := "q") (.sword 64) rfl
  refine ⟨_, .rSeq (.rScalarSetExpr "i" _ (notTmp_of_head (by decide))
      (litClean (by omega)) (by simp [sexprVars]))
    (.rSeq (.rArrLoad ⟨"u", .TU64⟩ ⟨"a", .TBytes 32⟩ "i" (notTmp_of_head (by decide))
        (by simp [nameTys_upd_ne, h.a]) (by simp [nameTys_upd_self]))
    (.rSeq (.rArrLoad ⟨"v", .TU64⟩ ⟨"b", .TBytes 32⟩ "i" (notTmp_of_head (by decide))
        (by simp [nameTys_upd_ne, h.b]) (by simp [nameTys_upd_ne, nameTys_upd_self]))
    (.rSeq (.rScalarSetExpr "q" _ (notTmp_of_head (by decide))
        ⟨notTmp_of_head (by decide), notTmp_of_head (by decide)⟩
        (by simp [sexprVars, nameTys_upd_ne, nameTys_upd_self, encodeTy_locDst_TU64]))
    (.rSeq (.rSelect ⟨"r", .TU64⟩ "q" ⟨"r", .TU64⟩ ⟨"w", .TU64⟩
        (notTmp_of_head (by decide)) rfl (nameTys_upd_self _ _ _)
        (by simp [h4.r]) (by simp [h4.w])) .rSkip)))),
    h4.updR⟩

/-- **The equality source is in the reads-bound covered fragment.** -/
theorem ctEqSrc_transTotal : ∃ σ', TransTotal eqTys ctEqSrc σ' ∧ EqTyInv σ' := by
  obtain ⟨σ0, t0, h0⟩ := eqInit_tt
  obtain ⟨σ1, t1, h1⟩ := eqLimbCmds_tt h0 0
  obtain ⟨σ2, t2, h2⟩ := eqLimbCmds_tt h1 1
  obtain ⟨σ3, t3, h3⟩ := eqLimbCmds_tt h2 2
  obtain ⟨σ4, t4, h4⟩ := eqLimbCmds_tt h3 3
  exact ⟨σ4, transTotal_seqL_append t0 (transTotal_seqL_append t1
    (transTotal_seqL_append t2 (transTotal_seqL_append t3 t4))), h4⟩

/-! ## 7. The front, the lowering and the rendering -/

/-- The argument context of the select, head first: `out` (RCX), `c` (RDX),
    `b` (RSI), `a` (RDI). -/
def ctSelCtx : Ctx := [.memref 4, .sword 64, .memref 4, .memref 4]

/-- The argument `VarMap` of the select: `a` bound deepest, then `b`, `c`,
    `out`. -/
def ctSelVM : VarMap ctSelCtx :=
  (((VarMap.empty.bind (t := .memref 4) "a").bind (t := .memref 4) "b").bind
    (t := .sword 64) "c").bind (t := .memref 4) "out"

/-- The argument context of the equality test, head first: `b` (RSI),
    `a` (RDI). -/
def ctEqCtx : Ctx := [.memref 4, .memref 4]

/-- The argument `VarMap` of the equality test. -/
def ctEqVM : VarMap ctEqCtx :=
  (VarMap.empty.bind (t := .memref 4) "a").bind (t := .memref 4) "b"

/-- The front output of the select, closed by returning `out`. -/
def ctSelectFront : Option (Com catCryptDialect ctSelCtx (.memref 4)) :=
  match translateDialectControl ctSelVM ctSelectSrc with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front output of the equality test, closed by returning the truth
    value. -/
def ctEqFront : Option (Com catCryptDialect ctEqCtx (.sword 64)) :=
  match translateDialectControl ctEqVM ctEqSrc with
  | some r =>
      match r.vm.lookup "r" with
      | some ⟨.sword 64, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The select's front output lowered to `Com jasminDialect`. -/
def ctSelectLowered :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match ctSelectFront with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-- The exported `Lprog` of the select under
    `f(a = RDI, b = RSI, cond = RDX, out = RCX)`. -/
def ctSelectLprog (name : String) : Option JasminLprogExport.Lprog :=
  ctSelectLowered.map (fun s =>
    JasminLprogExport.Com.toLprogPhysAbi s.2.2 name
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX", "RCX"]) (abiTyin := [64, 64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The exported `Lprog` of the select after `ConstIndexFold.constIndexFold`,
    the basic-block pipeline, two rounds of `LprogCopyCoalesce.coalesceRounds`
    and the conditional-move fusion `CombSelectCmovFront.cmovFuseLprog`. -/
def ctSelectFusedLprog (name : String) : Option JasminLprogExport.Lprog :=
  (ctSelectLprog name).map (fun lp =>
    cmovFuseLprog (LprogCopyCoalesce.coalesceRounds 2
      (LprogOptPipeline.optimizeLprogBasicBlocks
        (ConstIndexFold.spellLprog (ConstIndexFold.constIndexFold lp)))))

/-- The owned AT&T rendering of the select. -/
def ctSelectAsm : Option String :=
  (ctSelectFusedLprog "primeir_ct_select_x86_from_lean").map LprogAsmPrinter.renderLprogAtt

/-- The line count of the rendered select. -/
def ctSelectLines : Option Nat := ctSelectAsm.map LprogCopyCoalesce.lineCount

/-- The rendered select exists and has no `UNHANDLED` sentinel. -/
def ctSelectClean : Bool :=
  match ctSelectAsm with
  | some t => !LprogCopyCoalesce.hasUnhandled t
  | none => false

/-- The rendered select contains a `cmov` mnemonic. -/
def ctSelectHasCmov : Bool :=
  match ctSelectAsm with
  | some t => (t.splitOn "cmov").length != 1
  | none => false

/-! ## 8. The front outputs and their denotations -/

theorem selTys_srcTys : SrcTys selTys := by
  intro x hx
  simp only [selTys] at hx
  by_cases h1 : x = "out"
  · subst h1; exact notTmp_of_head (by decide)
  · by_cases h2 : x = "c"
    · subst h2; exact notTmp_of_head (by decide)
    · by_cases h3 : x = "b"
      · subst h3; exact notTmp_of_head (by decide)
      · by_cases h4 : x = "a"
        · subst h4; exact notTmp_of_head (by decide)
        · simp [h1, h2, h3, h4] at hx

theorem selTys_vmApprox : VmApprox selTys ctSelVM := by
  intro x t hx
  simp only [selTys] at hx
  by_cases h1 : x = "out"
  · subst h1
    simp only [if_true, Option.some.injEq] at hx
    subst hx
    exact ⟨.here, by simp [ctSelVM, VarMap.bind]; rfl⟩
  · by_cases h2 : x = "c"
    · subst h2
      simp only [if_neg h1, if_true, Option.some.injEq] at hx
      subst hx
      exact ⟨.there .here, by simp [ctSelVM, VarMap.bind]; rfl⟩
    · by_cases h3 : x = "b"
      · subst h3
        simp only [if_neg h1, if_neg h2, if_true, Option.some.injEq] at hx
        subst hx
        exact ⟨.there (.there .here), by simp [ctSelVM, VarMap.bind]; rfl⟩
      · by_cases h4 : x = "a"
        · subst h4
          simp only [if_neg h1, if_neg h2, if_neg h3, if_true, Option.some.injEq] at hx
          subst hx
          exact ⟨.there (.there (.there .here)),
            by simp [ctSelVM, VarMap.bind, VarMap.empty]; rfl⟩
        · simp [h1, h2, h3, h4] at hx

theorem eqTys_srcTys : SrcTys eqTys := by
  intro x hx
  simp only [eqTys] at hx
  by_cases h1 : x = "b"
  · subst h1; exact notTmp_of_head (by decide)
  · by_cases h2 : x = "a"
    · subst h2; exact notTmp_of_head (by decide)
    · simp [h1, h2] at hx

theorem eqTys_vmApprox : VmApprox eqTys ctEqVM := by
  intro x t hx
  simp only [eqTys] at hx
  by_cases h1 : x = "b"
  · subst h1
    simp only [if_true, Option.some.injEq] at hx
    subst hx
    exact ⟨.here, by simp [ctEqVM, VarMap.bind]; rfl⟩
  · by_cases h2 : x = "a"
    · subst h2
      simp only [if_neg h1, if_true, Option.some.injEq] at hx
      subst hx
      exact ⟨.there .here, by simp [ctEqVM, VarMap.bind, VarMap.empty]; rfl⟩
    · simp [h1, h2] at hx

/-- The select's front translates the source and the result lowers to
    `Com jasminDialect`. -/
theorem ctSelectFront_spec :
    ∃ (o : DTransOut ctSelCtx) (v : CVar o.Γ' (.memref 4))
      (com : Com catCryptDialect ctSelCtx (.memref 4)),
      translateDialectControl ctSelVM ctSelectSrc = some o
      ∧ o.vm.lookup "out" = some ⟨.memref 4, v⟩
      ∧ o.cont (Com.ret (toVIRVar v)) = some com
      ∧ ctSelectFront = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome := by
  obtain ⟨σ', htt, hinv⟩ := ctSelectSrc_transTotal
  obtain ⟨o, htr, happ, hcont⟩ :=
    translateDialectControl_total htt ctSelVM selTys_srcTys selTys_vmApprox
  obtain ⟨v, hv⟩ := happ "out" (.memref 4) hinv.out
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar v)) (by rfl)
  refine ⟨o, v, com, htr, hv, hcom, ?_, hlow⟩
  simp only [ctSelectFront, htr, hv]
  exact hcom

theorem ctSelectFront_isSome : ctSelectFront.isSome := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := ctSelectFront_spec
  rw [h]; rfl

theorem ctSelectLowered_isSome : ctSelectLowered.isSome := by
  obtain ⟨_, _, com, _, _, _, h, hlow⟩ := ctSelectFront_spec
  obtain ⟨jc, hjc⟩ := Option.isSome_iff_exists.mp hlow
  simp only [ctSelectLowered, h, hjc, Option.isSome_some]

/-- The rendering of the select exists. -/
theorem ctSelectAsm_isSome : ctSelectAsm.isSome := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp ctSelectLowered_isSome
  simp only [ctSelectAsm, ctSelectFusedLprog, ctSelectLprog, hs, Option.map_some,
    Option.isSome_some]

/-- The equality test's front translates the source and the result lowers to
    `Com jasminDialect`. -/
theorem ctEqFront_spec :
    ∃ (o : DTransOut ctEqCtx) (v : CVar o.Γ' (.sword 64))
      (com : Com catCryptDialect ctEqCtx (.sword 64)),
      translateDialectControl ctEqVM ctEqSrc = some o
      ∧ o.vm.lookup "r" = some ⟨.sword 64, v⟩
      ∧ o.cont (Com.ret (toVIRVar v)) = some com
      ∧ ctEqFront = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome := by
  obtain ⟨σ', htt, hinv⟩ := ctEqSrc_transTotal
  obtain ⟨o, htr, happ, hcont⟩ :=
    translateDialectControl_total htt ctEqVM eqTys_srcTys eqTys_vmApprox
  obtain ⟨v, hv⟩ := happ "r" (.sword 64) hinv.r
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar v)) (by rfl)
  refine ⟨o, v, com, htr, hv, hcom, ?_, hlow⟩
  simp only [ctEqFront, htr, hv]
  exact hcom

theorem ctEqFront_isSome : ctEqFront.isSome := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := ctEqFront_spec
  rw [h]; rfl

/-- The argument valuation of the select: `out ↦ O`, `c ↦ C`, `b ↦ B`,
    `a ↦ A`. -/
def ctSelVal (O : Fin 4 → BitVec 64) (C : BitVec 64) (B A : Fin 4 → BitVec 64) :
    Ctxt.Valuation (d := catCryptDialect) ctSelCtx :=
  .cons O (.cons C (.cons B (.cons A .nil)))

/-- The environment the select's argument valuation induces through `ctSelVM`. -/
def ctSelEnv (V : Ctxt.Valuation (d := catCryptDialect) ctSelCtx) : SEnvScalar :=
  fun s => (ctSelVM.lookup s).map (fun p => ⟨p.1, (toVIRVar p.2).lookup V⟩)

/-- The argument valuation of the equality test: `b ↦ B`, `a ↦ A`. -/
def ctEqValu (B A : Fin 4 → BitVec 64) : Ctxt.Valuation (d := catCryptDialect) ctEqCtx :=
  .cons B (.cons A .nil)

/-- The environment the equality test's argument valuation induces through
    `ctEqVM`. -/
def ctEqEnv (V : Ctxt.Valuation (d := catCryptDialect) ctEqCtx) : SEnvScalar :=
  fun s => (ctEqVM.lookup s).map (fun p => ⟨p.1, (toVIRVar p.2).lookup V⟩)

/-- **Value correctness of the select's front output.** The program the front
    produces returns the buffer `out` holding `a` when `c = 1` and `b`
    otherwise. -/
theorem ctSelectFront_denote (O : Fin 4 → BitVec 64) (C : BitVec 64)
    (B A : Fin 4 → BitVec 64) :
    ∃ com, ctSelectFront = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ com.denote (ctSelVal O C B A) = ctSelectVal (C ^^^ 1#64) A B := by
  obtain ⟨σ', htt, -⟩ := ctSelectSrc_transTotal
  obtain ⟨o, v, com, htr, hv, hcom, hfront, hlow⟩ := ctSelectFront_spec
  have hc : ConsistentS ctSelVM (ctSelVal O C B A) (ctSelEnv (ctSelVal O C B A)) :=
    fun _ => rfl
  have ha : ctSelEnv (ctSelVal O C B A) "a" = some ⟨.memref 4, A⟩ := by
    simp [ctSelEnv, ctSelVM, VarMap.bind, VarMap.empty, ctSelVal]; rfl
  have hb : ctSelEnv (ctSelVal O C B A) "b" = some ⟨.memref 4, B⟩ := by
    simp [ctSelEnv, ctSelVM, VarMap.bind, ctSelVal]; rfl
  have hcv : ctSelEnv (ctSelVal O C B A) "c" = some ⟨.sword 64, C⟩ := by
    simp [ctSelEnv, ctSelVM, VarMap.bind, ctSelVal]; rfl
  have ho : ctSelEnv (ctSelVal O C B A) "out" = some ⟨.memref 4, O⟩ := by
    simp [ctSelEnv, ctSelVM, VarMap.bind, ctSelVal]; rfl
  obtain ⟨env', hsem, hout⟩ := ctSelectSrc_run ha hb hcv ho
  obtain ⟨V', hc', htail⟩ := translateDialectControl_denote htt.toIsCoveredS ctSelVM
    (ctSelVal O C B A) _ env' o hc htr hsem
  obtain ⟨com', hcom', hden⟩ := htail (Com.ret (toVIRVar v))
  rw [hcom] at hcom'
  cases hcom'
  refine ⟨com, hfront, hlow, ?_⟩
  rw [hden]
  exact ConsistentS.lookup_eq hc' hv hout

/-- **The field-level value of the select's front output.** For a condition word
    in `{0, 1}`, the field element the returned limbs decode to is
    `ctSelectDenote` of the condition and the two decoded operands. -/
theorem ctSelectFront_denote_field {p : Nat} (O : Fin 4 → BitVec 64) (C : BitVec 64)
    (B A : Fin 4 → BitVec 64) (hC : C = 0#64 ∨ C = 1#64) :
    ∃ com, ctSelectFront = some com
      ∧ fieldOfLimbs p (com.denote (ctSelVal O C B A))
        = ctSelectDenote C.toNat (fieldOfLimbs p A) (fieldOfLimbs p B) := by
  obtain ⟨com, hfront, -, hden⟩ := ctSelectFront_denote O C B A
  refine ⟨com, hfront, ?_⟩
  rw [hden, ctSelectVal_eq A B C hC]
  rcases hC with rfl | rfl
  · simp [ctSelectDenote]
  · simp [ctSelectDenote]

/-- **Value correctness of the equality test's front output.** The program the
    front produces returns `1` when the eight limbs agree pairwise and `0`
    otherwise. -/
theorem ctEqFront_denote (B A : Fin 4 → BitVec 64) :
    ∃ com, ctEqFront = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ com.denote (ctEqValu B A) = ctEqVal A B := by
  obtain ⟨σ', htt, -⟩ := ctEqSrc_transTotal
  obtain ⟨o, v, com, htr, hv, hcom, hfront, hlow⟩ := ctEqFront_spec
  have hc : ConsistentS ctEqVM (ctEqValu B A) (ctEqEnv (ctEqValu B A)) := fun _ => rfl
  have ha : ctEqEnv (ctEqValu B A) "a" = some ⟨.memref 4, A⟩ := by
    simp [ctEqEnv, ctEqVM, VarMap.bind, VarMap.empty, ctEqValu]; rfl
  have hb : ctEqEnv (ctEqValu B A) "b" = some ⟨.memref 4, B⟩ := by
    simp [ctEqEnv, ctEqVM, VarMap.bind, ctEqValu]; rfl
  obtain ⟨env', hsem, hr⟩ := ctEqSrc_run ha hb
  obtain ⟨V', hc', htail⟩ := translateDialectControl_denote htt.toIsCoveredS ctEqVM
    (ctEqValu B A) _ env' o hc htr hsem
  obtain ⟨com', hcom', hden⟩ := htail (Com.ret (toVIRVar v))
  rw [hcom] at hcom'
  cases hcom'
  refine ⟨com, hfront, hlow, ?_⟩
  rw [hden]
  exact ConsistentS.lookup_eq hc' hv hr

/-- **The field-level value of the equality test's front output.** For canonical
    limb arrays and `p ≤ 2^256`, the word the front output returns has value
    `ctEqDenote x y`. -/
theorem ctEqFront_denote_field {p : Nat} [NeZero p] (hp : p ≤ 2 ^ (64 * 4)) (x y : ZMod p) :
    ∃ com, ctEqFront = some com
      ∧ (com.denote (ctEqValu (limbsOfField y) (limbsOfField x))).toNat = ctEqDenote x y := by
  obtain ⟨com, hfront, -, hden⟩ := ctEqFront_denote (limbsOfField y) (limbsOfField x)
  refine ⟨com, hfront, ?_⟩
  rw [hden, ctEqVal_eq, if_congr (limbsOfField_eq_iff hp x y) rfl rfl, ctEqDenote]
  by_cases h : x = y <;> simp [h]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrCtLower
