/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord

@[expose] public section

set_option autoImplicit false

/-!
# The narrow-field template: a field program at a single-word prime

For a single-word representation `F : SingleWordField p`, `wordTemplate F` is a
`FieldTemplate 1`: an element of `ZMod p` is carried by one 64-bit limb holding `F.enc`, and
a field program is lowered by the blocks of `F` (`lowerOpW F`) through the generic limb
lowering `fieldComOf` of `FieldToJasminLimbs`. Its denotation theorem is that of every
field template, so a caller of the route does not distinguish it from the Montgomery and
Solinas templates.

The template the route chooses at a modulus `p = 2³¹ − c` is `narrowTemplate p n h`: the
canonical-representative record `SingleWordField.ofCanonical` whose multiplication block is
`foldMulBlk c n p` (the product, `n` folds `x ↦ (x >>> 31) · c + (x & (2³¹ − 1))`, one
conditional subtract). The certificate `narrowCert p n` is an interval bound chain: from the
product bound `(p − 1)² + 1`, each fold maps a strict upper bound `B ≤ 2⁶²` to
`⌊B / 2³¹⌋ · c + 2³¹` (`foldW_bound`), and the last bound is at most `2 p`, the input range
of the conditional subtract. `narrowFoldsOf p` is the least `n < 16` the certificate
accepts.

The certificate requires `p ≤ 2³¹`; it holds at BabyBear (`2³¹ − 2²⁷ + 1`), KoalaBear
(`2³¹ − 2²⁴ + 1`) and Mersenne-31 (`2³¹ − 1`), and fails at every fold count at
Goldilocks (`2⁶⁴ − 2³² + 1`), whose products exceed the 64-bit range of the bound chain.

## Main definitions

* `encW`, `encLW`, `lowerOpW`, `GoodN`, `GoodNB`: the encoding, the blocks and the coverage
  of a single-word lowering.
* `compileFieldW`, `wordTemplate`: the route program and the template of a
  `SingleWordField`.
* `foldsOk`, `narrowCert`, `narrowFoldsOf`: the bound chain, the certificate and the fold
  count chosen at a modulus.
* `narrowField`, `narrowTemplate`, `narrowTemplateOf`: the record, the template and the
  template arm at a modulus.

## Main results

* `blockSquareW`: the block square of the single-word lowering.
* `compileFieldW_denote`: the output array of a routed program holds the encoding of the
  program's value.
* `foldsOk_spec`: under the bound chain, `n` folds land below `2 p` and keep the residue.
* `narrowMulBlk_denote`: under the certificate, the fold multiply is field multiplication on
  canonical representatives.
* `narrowTemplateOf_spec`: a template of the arm has the modulus `p`.
* `narrowFoldsOf_babyBear`, `narrowFoldsOf_koalaBear`, `narrowFoldsOf_mersenne31`: the
  certificate selects the arm at the three primes.
* `narrowCert_goldilocks`, `narrowTemplateOf_goldilocks`: the refusal at Goldilocks.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn limbsN)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (FieldTemplate)

/-! ## 1. The single-word lowering -/

section Word

variable {p : Nat} (F : SingleWordField p)

/-- The limb of an element: the one 64-bit word `F.enc x`. -/
def encW (x : ZMod p) : ListDenote (Rn 1) := .cons (F.enc x) .nil

/-- The encoding: `encW` on `fp p`, and the zero limb on every other type. -/
def encLW : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL 1 t)
  | .fp q, x => if h : q = p then encW F (cast (congrArg ZMod h) x) else limbsN 1 0
  | .fp2 _, _ => limbsN 1 0
  | .fp6 _, _ => limbsN 1 0
  | .fp12 _, _ => limbsN 1 0

/-- At the type `.fp p`, the encoding `encLW F` of a value is the one limb `encW F x`. -/
theorem encLW_fp (x : ZMod p) : encLW F (t := .fp p) x = encW F x := by
  simp only [encLW, dite_true]
  rfl

/-- The zero limb. -/
abbrev zeroW {Γ : Ctxt jasminDialect} : MultiReturnCom jasminDialect Γ (Rn 1) :=
  CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont.constBlk 1 0

/-- The block of each field operation: the block of `F` on the operand limbs for an
    operation at `p`, and the zero limb otherwise. -/
def lowerOpW : LimbBlocks 1
  | .fAdd q => if q = p then (F.addBlk .here (.there .here)).toMulti else zeroW
  | .fSub q => if q = p then (F.subBlk .here (.there .here)).toMulti else zeroW
  | .fNeg q => if q = p then (F.negBlk .here).toMulti else zeroW
  | .fMul q => if q = p then (F.mulBlk .here (.there .here)).toMulti else zeroW
  | .fConst q c => if h : q = p then (F.constBlk (cast (congrArg ZMod h) c)).toMulti
    else zeroW
  | .fieldDouble q => if q = p then (F.addBlk .here .here).toMulti else zeroW
  | .fieldSquare q => if q = p then (F.mulBlk .here .here).toMulti else zeroW
  | _ => zeroW

/-- The operations covered at `p`: add, sub, neg, mul, constants, doubling and squaring. -/
def GoodN (p : Nat) {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) :
    Prop :=
  e.op = .fAdd p ∨ e.op = .fSub p ∨ e.op = .fNeg p ∨ e.op = .fMul p ∨
    (∃ c : ZMod p, e.op = .fConst p c) ∨ e.op = .fieldDouble p ∨ e.op = .fieldSquare p

/-- The block square of the single-word lowering. -/
theorem blockSquareW : (loweringOf (lowerOpW F)).BlockSquare (fun {t} x => encLW F (t := t) x)
    (GoodN p) := by
  intro Γ t e hg vals
  obtain ⟨op, h, args⟩ := e
  rcases hg with hop | hop | hop | hop | ⟨c, hop⟩ | hop | hop <;> subst hop
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpW F (.fAdd p)).denote (hvAppend (encLW F a) (hvAppend (encLW F b) .nil))
      = encLW F (t := .fp p) (fAddF a b)
    rw [encLW_fp, encLW_fp, encLW_fp, lowerOpW, ite_eq_left rfl, Com.denote_toMulti]
    exact congrArg (HVector.cons · .nil) (F.addBlk_denote _ _ _ a b rfl rfl)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpW F (.fSub p)).denote (hvAppend (encLW F a) (hvAppend (encLW F b) .nil))
      = encLW F (t := .fp p) (fSubF a b)
    rw [encLW_fp, encLW_fp, encLW_fp, lowerOpW, ite_eq_left rfl, Com.denote_toMulti]
    exact congrArg (HVector.cons · .nil) (F.subBlk_denote _ _ _ a b rfl rfl)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpW F (.fNeg p)).denote (hvAppend (encLW F a) .nil)
      = encLW F (t := .fp p) (fNegF a)
    rw [encLW_fp, encLW_fp, lowerOpW, ite_eq_left rfl, Com.denote_toMulti]
    exact congrArg (HVector.cons · .nil) (F.negBlk_denote _ _ a rfl)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpW F (.fMul p)).denote (hvAppend (encLW F a) (hvAppend (encLW F b) .nil))
      = encLW F (t := .fp p) (fMulF a b)
    rw [encLW_fp, encLW_fp, encLW_fp, lowerOpW, ite_eq_left rfl, Com.denote_toMulti]
    exact congrArg (HVector.cons · .nil) (F.mulBlk_denote _ _ _ a b rfl rfl)
  · obtain ⟨⟩ := vals
    show (lowerOpW F (.fConst p c)).denote .nil = encLW F (t := .fp p) (fConstF c)
    rw [encLW_fp, lowerOpW, dite_eq_left rfl, Com.denote_toMulti]
    exact congrArg (HVector.cons · .nil) (F.constBlk_denote _ c)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpW F (.fieldDouble p)).denote (hvAppend (encLW F a) .nil)
      = encLW F (t := .fp p) (fDoubleF a)
    rw [encLW_fp, encLW_fp, lowerOpW, ite_eq_left rfl, Com.denote_toMulti]
    exact congrArg (HVector.cons · .nil) (F.addBlk_denote _ _ _ a a rfl rfl)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpW F (.fieldSquare p)).denote (hvAppend (encLW F a) .nil)
      = encLW F (t := .fp p) (fSquareF a)
    rw [encLW_fp, encLW_fp, lowerOpW, ite_eq_left rfl, Com.denote_toMulti]
    exact congrArg (HVector.cons · .nil) (F.mulBlk_denote _ _ _ a a rfl rfl)

/-- The operations `GoodNB` accepts: those of `GoodN`. -/
def opGoodNB (p : Nat) : fieldDialect.Op → Bool
  | .fAdd q | .fSub q | .fNeg q | .fMul q | .fieldDouble q | .fieldSquare q => q == p
  | .fConst q _ => q == p
  | _ => false

/-- The coverage decision: every let-bound operation passes `opGoodNB`. -/
def GoodNB (p : Nat) : {Γ : Ctxt fieldDialect} → {t : FieldTy} → Com fieldDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opGoodNB p e.op && GoodNB p body

/-- An expression whose operation the decision `opGoodNB p` accepts satisfies `GoodN p`. -/
theorem opGoodNB_sound (p : Nat) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) (h : opGoodNB p e.op = true) : GoodN p e := by
  obtain ⟨op, _, _⟩ := e
  cases op <;> simp only [opGoodNB, beq_iff_eq, Bool.false_eq_true] at h <;> subst h <;>
    simp [GoodN]

/-- A program accepted by `GoodNB` is `GoodN`-covered. -/
theorem GoodNB_sound (p : Nat) : {Γ : Ctxt fieldDialect} → {t : FieldTy} →
    (c : Com fieldDialect Γ t) → GoodNB p c = true → CoveredCom (GoodN p) c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, h => by
      simp only [GoodNB, Bool.and_eq_true] at h
      exact ⟨opGoodNB_sound p e h.1, GoodNB_sound p body h.2⟩

/-- **The route program of a field program at a single-word prime**: the straight-line
    program `fieldComOf (lowerOpW F) c` over word arrays of one limb when `GoodNB` accepts
    `c`, and `none` otherwise. -/
def compileFieldW {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    Option (RouteProg (arrCtx 1 Γ ++ [arrTy 1]) (arrTy 1)) :=
  if GoodNB p c then some (.straight (fieldComOf (lowerOpW F) c)) else none

/-- **The output array of a compiled field program at a single-word prime.** For input
    arrays whose limbs are the encodings of the values of `V`, the output array holds the
    limb of the encoding of `c.denote V`. -/
theorem compileFieldW_denote {Γ : Ctxt fieldDialect} {t : FieldTy}
    {c : Com fieldDialect Γ t} {rp : RouteProg (arrCtx 1 Γ ++ [arrTy 1]) (arrTy 1)}
    (h : compileFieldW F c = some rp) (V : Valuation Γ) (A : Valuation (arrCtx 1 Γ))
    (o : Fin 1 → BitVec 64) (hA : arrFlat A = flatVal (fun {t} x => encLW F (t := t) x) V) :
    arrLimbs (rp.denote (hvAppend A (.cons o .nil))) 1 0 = encLW F (c.denote V) := by
  unfold compileFieldW at h
  split at h
  · rename_i hc
    cases h
    rw [RouteProg.denote_straight]
    exact fieldComOf_denote (lowerOpW F) (fun {t} x => encLW F (t := t) x) (GoodN p)
      (blockSquareW F) (by norm_num) c (GoodNB_sound p c hc) V A o hA
  · cases h

/-- **The single-word template** of `F`: one limb holding `F.enc`, routed by
    `compileFieldW F`. -/
def wordTemplate (hp : 1 < p) : FieldTemplate 1 where
  p := p
  one_lt := hp
  enc := encW F
  encL := fun {t} x => encLW F (t := t) x
  encL_fp := encLW_fp F
  route := fun c => compileFieldW F c
  route_denote := fun h => compileFieldW_denote F h

end Word

/-! ## 2. The bounds certificate of the fold multiply -/

/-- **The bound chain of `k` folds by `c`** from a strict upper bound `B`: each fold needs
    `B ≤ 2⁶²` and maps `B` to `⌊B / 2³¹⌋ · c + 2³¹`; the last bound is at most `2 P`. -/
def foldsOk (c P : Nat) : Nat → Nat → Bool
  | 0, B => decide (B ≤ 2 * P)
  | k + 1, B => decide (B ≤ 2 ^ 62) && foldsOk c P k (B / 2 ^ 31 * c + 2 ^ 31)

/-- **The bound chain is sound**: for `P = 2³¹ − c` and a word below `B`, `k` folds land
    below `2 P` and keep the residue modulo `P`. -/
theorem foldsOk_spec (c : Nat) (hc : c < 2 ^ 31) :
    ∀ (k B : Nat) (x : BitVec 64), foldsOk c (2 ^ 31 - c) k B = true → x.toNat < B →
      ((foldW c)^[k] x).toNat < 2 * (2 ^ 31 - c) ∧
        ((foldW c)^[k] x).toNat % (2 ^ 31 - c) = x.toNat % (2 ^ 31 - c)
  | 0, B, x, h, hx => by
      simp only [foldsOk, decide_eq_true_eq] at h
      exact ⟨by simp only [Function.iterate_zero, id_eq]; omega, rfl⟩
  | k + 1, B, x, h, hx => by
      simp only [foldsOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2⟩ := foldsOk_spec c hc k _ (foldW c x) h.2 (foldW_bound c hc x B h.1 hx)
      rw [Function.iterate_succ_apply]
      exact ⟨h1, h2.trans (foldW_mod c hc x (by omega))⟩

/-- **The certificate of the narrow template at `p` with `n` folds**: `1 < p ≤ 2³¹`, so that
    `p = 2³¹ − c` with `c = 2³¹ − p < 2³¹`, and the bound chain of `n` folds by `c` from the
    product bound `(p − 1)² + 1`. -/
def narrowCert (p n : Nat) : Bool :=
  decide (1 < p ∧ p ≤ 2 ^ 31) && foldsOk (2 ^ 31 - p) p n ((p - 1) * (p - 1) + 1)

/-- **The fold count chosen at `p`**: the least `n < 16` that `narrowCert p` accepts. -/
def narrowFoldsOf (p : Nat) : Option Nat := (List.range 16).find? (narrowCert p)

/-- The fold count that `narrowFoldsOf p` returns satisfies the certificate `narrowCert p`. -/
theorem narrowCert_of_narrowFoldsOf {p n : Nat} (h : narrowFoldsOf p = some n) :
    narrowCert p n = true :=
  List.find?_some h

/-- A modulus that the certificate accepts satisfies `1 < p ≤ 2³¹`. -/
theorem narrowCert_bounds {p n : Nat} (h : narrowCert p n = true) : 1 < p ∧ p ≤ 2 ^ 31 := by
  simp only [narrowCert, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- The multiplication block of the narrow template: the product, `n` folds by `2³¹ − p`,
    one conditional subtract of `p`. -/
def narrowMulBlk (p n : Nat) {Γ : Ctxt jasminDialect} (a b : Var Γ w64) :
    Com jasminDialect Γ w64 :=
  foldMulBlk (2 ^ 31 - p) n p a b

/-- **The fold multiply under the certificate**: on variables holding the canonical
    representatives of `x` and `y`, `narrowMulBlk p n` denotes the canonical representative
    of `x * y`. -/
theorem narrowMulBlk_denote {p n : Nat} [NeZero p] (h : narrowCert p n = true)
    {Γ : Ctxt jasminDialect} (a b : Var Γ w64) (V : Valuation Γ) (x y : ZMod p)
    (ha : a.lookup V = canonEnc p x) (hb : b.lookup V = canonEnc p y) :
    (narrowMulBlk p n a b).denote V = canonEnc p (x * y) := by
  simp only [narrowCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp1, hp⟩, hf⟩ := h
  have hc : 2 ^ 31 - p < 2 ^ 31 := by omega
  have hP : 2 ^ 31 - (2 ^ 31 - p) = p := by omega
  have hf' : foldsOk (2 ^ 31 - p) (2 ^ 31 - (2 ^ 31 - p)) n ((p - 1) * (p - 1) + 1) = true :=
    by rwa [hP]
  have hx : x.val < p := ZMod.val_lt x
  have hy : y.val < p := ZMod.val_lt y
  have hle : x.val * y.val ≤ (p - 1) * (p - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlt : x.val * y.val < 2 ^ 62 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' hx hy)
      (le_trans (Nat.mul_le_mul hp hp) (by norm_num))
  have hprod : (canonEnc p x * canonEnc p y).toNat = x.val * y.val := by
    rw [BitVec.toNat_mul, canonEnc_toNat (by omega), canonEnc_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨h1, h2⟩ := foldsOk_spec _ hc n _ (canonEnc p x * canonEnc p y) hf'
    (by rw [hprod]; omega)
  rw [hP] at h1 h2
  apply eq_canonEnc_of_toNat (by omega)
  rw [narrowMulBlk, foldMulBlk_denote, show lk a V = canonEnc p x from ha,
    show lk b V = canonEnc p y from hb, csubW_toNat p (by omega) _ h1, h2, hprod, ZMod.val_mul]

/-! ## 3. The template arm -/

/-- **The narrow record at `p`** under the certificate `narrowCert p n`: canonical
    representatives, with the fold multiply `narrowMulBlk p n`. -/
def narrowField (p n : Nat) (h : narrowCert p n = true) : SingleWordField p :=
  haveI : NeZero p := ⟨by have := (narrowCert_bounds h).1; omega⟩
  SingleWordField.ofCanonical p (by have := (narrowCert_bounds h).2; omega)
    (narrowMulBlk p n) (narrowMulBlk_denote h)

/-- **The narrow template at `p`** under the certificate `narrowCert p n`. -/
def narrowTemplate (p n : Nat) (h : narrowCert p n = true) : FieldTemplate 1 :=
  wordTemplate (narrowField p n h) (narrowCert_bounds h).1

/-- **The narrow arm of the template dispatcher**: the narrow template at the fold count
    `narrowFoldsOf p`, and `none` when the certificate accepts no fold count below `16`. -/
def narrowTemplateOf (p : Nat) : Option (Σ n, FieldTemplate n) :=
  match h : narrowFoldsOf p with
  | some k => some ⟨1, narrowTemplate p k (narrowCert_of_narrowFoldsOf h)⟩
  | none => none

/-- A template that the arm `narrowTemplateOf p` returns has the modulus `p`. -/
theorem narrowTemplateOf_spec {p n : Nat} {T : FieldTemplate n}
    (h : narrowTemplateOf p = some ⟨n, T⟩) : T.p = p := by
  unfold narrowTemplateOf at h
  split at h
  · cases h
    rfl
  · cases h

/-- **The narrow case of the arm**: when the certificate selects `k` folds, the arm returns
    the narrow template at `k`. -/
theorem narrowTemplateOf_of_narrowFoldsOf {p k : Nat} (h : narrowFoldsOf p = some k) :
    ∃ hc, narrowTemplateOf p = some ⟨1, narrowTemplate p k hc⟩ := by
  refine ⟨narrowCert_of_narrowFoldsOf h, ?_⟩
  unfold narrowTemplateOf
  split
  · rename_i h'
    rw [h] at h'
    cases h'
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

/-- The arm `narrowTemplateOf p` returns no template when no fold count below 16 satisfies the
    certificate at `p`. -/
theorem narrowTemplateOf_of_none {p : Nat} (h : narrowFoldsOf p = none) :
    narrowTemplateOf p = none := by
  unfold narrowTemplateOf
  split
  · rename_i h'
    rw [h] at h'
    cases h'
  · rfl

/-! ## 4. The three primes and the refusal at Goldilocks -/

/-- The certificate selects eight folds at BabyBear, `p = 2³¹ − 2²⁷ + 1`. -/
theorem narrowFoldsOf_babyBear : narrowFoldsOf 2013265921 = some 8 := by decide +kernel

/-- The certificate selects five folds at KoalaBear, `p = 2³¹ − 2²⁴ + 1`. -/
theorem narrowFoldsOf_koalaBear : narrowFoldsOf 2130706433 = some 5 := by decide +kernel

/-- The certificate selects one fold at Mersenne-31, `p = 2³¹ − 1`. -/
theorem narrowFoldsOf_mersenne31 : narrowFoldsOf 2147483647 = some 1 := by decide +kernel

/-- **The refusal at Goldilocks**, `p = 2⁶⁴ − 2³² + 1`: the certificate fails at every fold
    count, since `p > 2³¹`. -/
theorem narrowCert_goldilocks (n : Nat) : narrowCert 18446744069414584321 n = false := by
  simp only [narrowCert, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  left
  omega

/-- The narrow arm returns no template at Goldilocks. -/
theorem narrowTemplateOf_goldilocks : narrowTemplateOf 18446744069414584321 = none :=
  narrowTemplateOf_of_none (by decide +kernel)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow
