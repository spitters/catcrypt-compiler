/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatField

@[expose] public section

set_option autoImplicit false

/-!
# The unsaturated template: a field program over radix-`2^b` limbs

For an unsaturated representation template `T : FieldReprTemplate` (`n` limbs of width `b`,
loose and tight limb intervals certified by `boundsOkMR`), `reprTemplate T h` is a
`FieldTemplate n`: an element `x` of `ZMod p` is carried by the `n` canonical digits of
`x.val` in base `2^b`, one per 64-bit word (`encD`). A field operation is the template's body
followed by its canonical reduction: `add`/`sub` then `carry`, or `carryMul`, then `freeze`
for a binary operation (`binBlk`), and `carrySquare` then `freeze` for a square (`sqBlk`).
Canonical digits lie in the tight intervals (`unsatCert`), so every block meets the
precondition of its certificate, and `freeze` returns canonical digits, so the encoding is
exact.

The arm `unsatTemplateOf p` takes the first instance of `unsatReprs` (Curve25519 at `5 × 51`
and p448 at `8 × 56`) whose modulus is `p` and whose certificate `unsatCert` holds.

## Main definitions

* `seqM`, `castHom`: sequential composition of multi-result programs and the renaming along
  an equality of contexts.
* `encD`: the canonical digits of a natural number as 64-bit words.
* `unsatCert`: the certificate that canonical digits are tight.
* `bodyBlk`, `binBlk`, `sqBlk`, `lowerOpU`, `GoodU`, `GoodUB`: the blocks and the coverage.
* `compileFieldU`, `reprTemplate`: the route program and the template.
* `p448`, `unsatReprs`, `unsatReprOf`, `unsatTemplateOf`: the p448 modulus, the instances
  keyed by modulus, and the template arm.

## Main results

* `seqM_denote`: the denotation of a composition.
* `eq_encD`: canonical digits of value `v` are the words `encD b n v`.
* `binBlk_denote`, `sqBlk_denote`: each block maps the encodings of its operands to the
  encoding of the operation's value.
* `blockSquareU`, `compileFieldU_denote`: the block square and the route denotation.
* `unsatTemplateOf_spec`, `unsatTemplateOf_of_unsatReprOf`, `unsatTemplateOf_of_none`: the
  arm returns templates at the modulus `p`.
* `unsatReprOf_curve25519`, `unsatReprOf_p448`: the instances selected at `2^255 - 19` and
  `2^448 - 2^224 - 1`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteUnsat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact (zvals hvGetZ ValsIn rdT rd)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn limbsN)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatBlocks (RCtx r64 carryMulBlk
  carrySquareBlk)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatField (evalL evalL_nonneg
  digits evalL_digits rdL ivVec ivsLe canonIvs valsIn_ivVec hvGetZ_zvals_nonneg FieldReprTemplate
  freezeBlk carryBlk addBlk subBlk curve25519Repr p448Repr)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (FieldTemplate)

/-! ## 1. Composition and renaming -/

/-- The sequential composition of multi-result programs: the bindings of `a`, then `b` on the
    results of `a`. -/
def seqM {Γ : Ctxt jasminDialect} {ts us : List JasminTy}
    (a : MultiReturnCom jasminDialect Γ ts) (b : MultiReturnCom jasminDialect ts us) :
    MultiReturnCom jasminDialect Γ us :=
  spliceMultiK a fun _ res => b.rename (hvToHom res)

/-- The composition `seqM a b` denotes `b` at the results of `a`. -/
theorem seqM_denote {Γ : Ctxt jasminDialect} {ts us : List JasminTy}
    (a : MultiReturnCom jasminDialect Γ ts) (b : MultiReturnCom jasminDialect ts us)
    (W : Valuation Γ) : (seqM a b).denote W = b.denote (a.denote W) :=
  spliceMultiK_denote a _ W _ fun _ res W' _ hres => by
    rw [multiReturnCom_denote_rename, pullV_hvToHom, hres]

/-- The renaming along an equality of contexts. -/
def castHom {Γ Γ' : Ctxt jasminDialect} (e : Γ = Γ') : Ctxt.Hom Γ Γ' := fun v => e ▸ v

/-- Renaming along an equality of contexts keeps the integer reading of every position. -/
theorem hvGetZ_pullV_castHom {Γ Γ' : Ctxt jasminDialect} (e : Γ = Γ') (X : Valuation Γ')
    (i : ℕ) : hvGetZ (zvals false (pullV (castHom e) X)) i = hvGetZ (zvals false X) i := by
  subst e
  have hX : pullV (castHom (rfl : Γ = Γ)) X = X := pullV_id X
  rw [hX]

/-- The integer reading at position `i` of an appended valuation is the reading of the first
    part for `i` below its length, and of the second part at `i` minus that length otherwise. -/
theorem hvGetZ_zvals_hvAppend : ∀ {xs ys : Ctxt jasminDialect} (A : Valuation xs)
    (B : Valuation ys) (i : ℕ), hvGetZ (zvals false (hvAppend A B)) i =
      if i < xs.length then hvGetZ (zvals false A) i else hvGetZ (zvals false B) (i - xs.length)
  | [], _, .nil, B, i => by simp [hvAppend]
  | _ :: _, _, .cons _ _, _, 0 => by
      simp only [List.length_cons, Nat.zero_lt_succ, ite_true]
      rfl
  | _ :: xs, _, .cons _ A, B, i + 1 => by
      show hvGetZ (zvals false (hvAppend A B)) i = _
      rw [hvGetZ_zvals_hvAppend A B i]
      simp only [List.length_cons, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]
      rfl

/-- The first `m + 1` readings of a valuation `x :: X` are the reading of `x` followed by the
    first `m` readings of `X`. -/
theorem rdL_cons {t : JasminTy} {ts : Ctxt jasminDialect} (x : ⟦t⟧) (X : Valuation ts) (m : ℕ) :
    rdL (zvals false (HVector.cons x X : Valuation (t :: ts))) 0 (m + 1) =
      rdT false t x :: rdL (zvals false X) 0 m := by
  simp only [rdL, List.ofFn_succ, Fin.val_zero, Fin.val_succ, Nat.zero_add]
  rfl

/-! ## 2. Canonical digits -/

/-- The `m` digits of `v` in base `2^b`, least significant first, as 64-bit words. -/
def encD (b : ℕ) : (m : ℕ) → ℕ → Valuation (RCtx m)
  | 0, _ => .nil
  | m + 1, v => .cons (BitVec.ofNat 64 (v % 2 ^ b)) (encD b m (v / 2 ^ b))

/-- For a digit width `b ≤ 64`, the readings of the words `encD b m v` are the `m` digits of
    `v` in base `2^b`. -/
theorem rdL_encD (b : ℕ) (hb : b ≤ 64) : ∀ (m v : ℕ),
    rdL (zvals false (encD b m v)) 0 m = (digits b m v).map (Nat.cast : ℕ → ℤ)
  | 0, _ => rfl
  | m + 1, v => by
      rw [encD, rdL_cons, rdL_encD b hb m]
      have h : v % 2 ^ b < 2 ^ 64 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos b)) (Nat.pow_le_pow_right (by norm_num) hb)
      simp only [digits, List.map_cons, rdT, rd, Bool.false_eq_true, ite_false,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Every reading of the words `encD b m v` is at most `2^b - 1`. -/
theorem hvGetZ_encD_le (b : ℕ) : ∀ (m v i : ℕ),
    hvGetZ (zvals false (encD b m v)) i ≤ 2 ^ b - 1
  | 0, _, _ => by
      show (0 : ℤ) ≤ _
      have : (0 : ℤ) < 2 ^ b := by positivity
      omega
  | m + 1, v, 0 => by
      show rd false (BitVec.ofNat 64 (v % 2 ^ b)) ≤ _
      simp only [rd, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
      have := Nat.mod_lt (v % 2 ^ b) (Nat.two_pow_pos 64)
      have h1 := Nat.mod_le (v % 2 ^ b) (2 ^ 64)
      have h2 := Nat.mod_lt v (Nat.two_pow_pos b)
      have : ((v % 2 ^ b % 2 ^ 64 : ℕ) : ℤ) < 2 ^ b := by exact_mod_cast lt_of_le_of_lt h1 h2
      omega
  | m + 1, v, i + 1 => hvGetZ_encD_le b m (v / 2 ^ b) i

/-- The value in base `2^b` of the digit list `a :: l` is `a + 2^b * evalL b l`. -/
theorem evalL_cons (b : ℕ) (a : ℤ) (l : List ℤ) : evalL b (a :: l) = a + 2 ^ b * evalL b l := rfl

/-- **Canonical digits are unique**: words whose readings lie in `[0, 2^b - 1]` and whose
    value in base `2^b` is `v` are the words `encD b m v`. -/
theorem eq_encD (b : ℕ) : ∀ (m : ℕ) (W : Valuation (RCtx m)) (v : ℕ),
    (∀ i < m, hvGetZ (zvals false W) i ≤ 2 ^ b - 1) →
    evalL b (rdL (zvals false W) 0 m) = (v : ℤ) → W = encD b m v
  | 0, .nil, _, _, _ => rfl
  | m + 1, .cons w W, v, hW, hv => by
      rw [rdL_cons, evalL_cons] at hv
      have hw : rd false w ≤ 2 ^ b - 1 := hW 0 (by omega)
      simp only [rdT, rd, Bool.false_eq_true, ite_false] at hw hv
      have hR := evalL_nonneg b (rdL (zvals false W) 0 m) fun a ha => by
        simp only [rdL, List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact hvGetZ_zvals_nonneg W _
      have hpos : (0 : ℤ) < 2 ^ b := by positivity
      have hw0 : (0 : ℤ) ≤ (w.toNat : ℤ) := by positivity
      have hmod : ((v % 2 ^ b : ℕ) : ℤ) = w.toNat := by
        push_cast
        rw [← hv, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hw0 (by omega)]
      have hdiv : ((v / 2 ^ b : ℕ) : ℤ) = evalL b (rdL (zvals false W) 0 m) := by
        push_cast
        rw [← hv, Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt hw0 (by omega),
          zero_add]
      have hw' : w = BitVec.ofNat 64 (v % 2 ^ b) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        have : v % 2 ^ b = w.toNat := by exact_mod_cast hmod
        rw [this, Nat.mod_eq_of_lt w.isLt]
      rw [encD, hw', eq_encD b m W (v / 2 ^ b) (fun i hi => by
        have := hW (i + 1) (by omega); exact this) hdiv.symm]

/-! ## 3. The blocks of a template -/

/-- **The certificate of the unsaturated template**: `1 < p`, `n < 2^64`, `n` tight intervals,
    and the canonical intervals `[0, 2^b - 1]` inside the tight intervals. -/
def unsatCert (T : FieldReprTemplate) : Bool :=
  decide (1 < T.P.p) && decide (T.P.n < 2 ^ 64) && T.tight.length == T.P.n &&
    ivsLe (canonIvs T.P) T.tight T.P.n

section Template

variable (T : FieldReprTemplate)

/-- A template that `unsatCert` accepts has a modulus above `1`, fewer than `2^64` limbs, one
    tight interval per limb, and canonical digit intervals within the tight intervals. -/
theorem unsatCert_spec {T : FieldReprTemplate} (h : unsatCert T = true) :
    1 < T.P.p ∧ T.P.n < 2 ^ 64 ∧ T.tight.length = T.P.n ∧
      ivsLe (canonIvs T.P) T.tight T.P.n = true := by
  simp only [unsatCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The context of `2 n` words is the context of two operands of `n` words each. -/
theorem ctx2_eq : RCtx (2 * T.P.n) = Rn T.P.n ++ (Rn T.P.n ++ []) := by
  rw [List.append_nil, ← List.replicate_add, two_mul]

/-- The context of `n` words is the context of one operand of `n` words. -/
theorem ctx1_eq : RCtx T.P.n = Rn T.P.n ++ [] := (List.append_nil _).symm

/-- The body of a binary operation as one block: `add` or `sub` then `carry`, or
    `carryMul`. -/
def bodyBlk : FieldReprTemplate.BinOp →
    MultiReturnCom jasminDialect (RCtx (2 * T.P.n)) (RCtx T.P.n)
  | .add => seqM (addBlk T.P) (carryBlk T.P T.sched)
  | .sub => seqM (subBlk T.P) (carryBlk T.P T.sched)
  | .mul => carryMulBlk T.P T.sched

/-- The body block of a binary operation denotes the template's body function `T.bodyRun`. -/
theorem bodyBlk_denote (o : FieldReprTemplate.BinOp) (W : Valuation (RCtx (2 * T.P.n))) :
    (bodyBlk T o).denote W = T.bodyRun o W := by
  cases o <;> simp only [bodyBlk, seqM_denote] <;> rfl

/-- **The block of a binary operation**: the body on the operand words, then `freeze`. -/
def binBlk (o : FieldReprTemplate.BinOp) :
    MultiReturnCom jasminDialect (Rn T.P.n ++ (Rn T.P.n ++ [])) (Rn T.P.n) :=
  seqM ((bodyBlk T o).rename (castHom (ctx2_eq T))) (freezeBlk T.P)

/-- **The block of a square**: `carrySquare` on the operand words, then `freeze`. -/
def sqBlk : MultiReturnCom jasminDialect (Rn T.P.n ++ []) (Rn T.P.n) :=
  seqM ((carrySquareBlk T.P T.sched).rename (castHom (ctx1_eq T))) (freezeBlk T.P)

/-- The words of an element: the canonical digits of its representative. -/
def encU (x : ZMod T.P.p) : Valuation (d := jasminDialect) (Rn T.P.n) := encD T.P.b T.P.n x.val

/-- The readings of the encoding `encU T x` are the canonical digits of `x.val` in base `2^b`. -/
theorem rdL_encU (x : ZMod T.P.p) :
    rdL (zvals false (encU T x)) 0 T.P.n = (digits T.P.b T.P.n x.val).map (Nat.cast : ℕ → ℤ) :=
  rdL_encD _ T.wordOk.1 _ _

/-- The value in base `2^b` of the encoding `encU T x` is `x.val`. -/
theorem evalL_encU (x : ZMod T.P.p) :
    evalL T.P.b (rdL (zvals false (encU T x)) 0 T.P.n) = (x.val : ℤ) := by
  have hp : 0 < T.P.p := by
    have := T.p_pos; have := T.p_cast; omega
  have : NeZero T.P.p := ⟨by omega⟩
  have hx : x.val < T.P.p := ZMod.val_lt x
  have hlt : (x.val : ℤ) < 2 ^ (T.P.b * T.P.n) := by
    have := T.p_lt
    have hc := T.p_cast
    omega
  rw [rdL_encU, evalL_digits]
  congr 1
  exact Nat.mod_eq_of_lt (by exact_mod_cast hlt)

/-- An integer `Y` whose image in `ZMod p` is `c` has residue `c.val` modulo `p`. -/
theorem toNat_emod_eq_val (Y : ℤ) (c : ZMod T.P.p) (hc : (Y : ZMod T.P.p) = c) :
    (Y % T.P.pZ).toNat = c.val := by
  have hp0 := T.p_pos
  have hpc := T.p_cast
  have : NeZero T.P.p := ⟨by omega⟩
  have h0 : 0 ≤ Y % T.P.pZ := Int.emod_nonneg _ (by omega)
  have h1 : Y % T.P.pZ < T.P.pZ := Int.emod_lt_of_pos _ hp0
  have hlt : (Y % T.P.pZ).toNat < T.P.p := by omega
  rw [← hc, ← ZMod.val_cast_of_lt hlt]
  congr 1
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0, ← hpc, ZMod.intCast_mod]

/-- The readings of the canonical digits lie in the tight intervals. -/
theorem tight_of_encU (h : unsatCert T = true) (x : ZMod T.P.p) (j : ℕ) (hj : j < T.P.n) :
    (T.tight.getD j (0, 0)).1 ≤ hvGetZ (zvals false (encU T x)) j ∧
      hvGetZ (zvals false (encU T x)) j ≤ (T.tight.getD j (0, 0)).2 := by
  have hle := of_decide_eq_true (List.all_eq_true.1 (unsatCert_spec h).2.2.2 j
    (List.mem_range.2 hj))
  simp only [canonIvs, List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hj,
    Option.getD_some] at hle
  exact ⟨le_trans hle.1 (hvGetZ_zvals_nonneg _ _),
    le_trans (hvGetZ_encD_le _ _ _ _) hle.2⟩

/-- Words within the canonical digit intervals have readings at most `2^b - 1`. -/
theorem freeze_out {W : Valuation (RCtx T.P.n)}
    (hW : ValsIn false (ivVec r64 (canonIvs T.P) T.P.n) W) (i : ℕ) (hi : i < T.P.n) :
    hvGetZ (zvals false W) i ≤ 2 ^ T.P.b - 1 := by
  have := ((valsIn_ivVec 64 T.P.n _ W).1 hW i hi).2
  simpa [canonIvs, List.getD_replicate, hi] using this

/-- **The binary block on encodings.** For `c` the image in `ZMod p` of the integer operation
    `o` on the representatives of `a` and `b`, the block maps the words of `a` and `b` to the
    words of `c`. -/
theorem binBlk_denote (h : unsatCert T = true) (o : FieldReprTemplate.BinOp)
    (a b c : ZMod T.P.p) (hc : ((o.evalZ (a.val : ℤ) (b.val : ℤ) : ℤ) : ZMod T.P.p) = c) :
    (binBlk T o).denote (hvAppend (encU T a) (hvAppend (encU T b) .nil)) = encU T c := by
  obtain ⟨-, -, hlen, -⟩ := unsatCert_spec h
  set X := hvAppend (encU T a) (hvAppend (encU T b) .nil)
  set W : Valuation (RCtx (2 * T.P.n)) := pullV (castHom (ctx2_eq T)) X with hWdef
  have hget : ∀ i, i < 2 * T.P.n → hvGetZ (zvals false W) i = if i < T.P.n then
      hvGetZ (zvals false (encU T a)) i else hvGetZ (zvals false (encU T b)) (i - T.P.n) := by
    intro i hi2
    rw [hWdef, hvGetZ_pullV_castHom, hvGetZ_zvals_hvAppend, List.length_replicate]
    split
    · rfl
    · rw [hvGetZ_zvals_hvAppend, List.length_replicate]
      split
      · rfl
      · omega
  have hW : ValsIn false (ivVec r64 (T.tight ++ T.tight) (2 * T.P.n)) W := by
    refine (valsIn_ivVec 64 (2 * T.P.n) _ W).2 fun i hi => ?_
    rw [hget i hi]
    split
    · rename_i hi'
      rw [List.getD_append _ _ _ _ (by omega)]
      exact tight_of_encU T h a i hi'
    · rename_i hi'
      rw [List.getD_append_right _ _ _ _ (by omega), hlen]
      exact tight_of_encU T h b (i - T.P.n) (by omega)
  have hA : rdL (zvals false W) 0 T.P.n = rdL (zvals false (encU T a)) 0 T.P.n := by
    simp only [rdL]
    congr 1
    funext i
    rw [hget _ (by omega), ite_eq_left (by omega)]
  have hB : rdL (zvals false W) T.P.n T.P.n = rdL (zvals false (encU T b)) 0 T.P.n := by
    simp only [rdL]
    congr 1
    funext i
    rw [hget _ (by omega), ite_eq_right (by omega)]
    congr 1
    omega
  rw [binBlk, seqM_denote, multiReturnCom_denote_rename, ← hWdef, bodyBlk_denote]
  obtain ⟨h2, e2⟩ := T.body_sem o W hW
  obtain ⟨h3, e3⟩ := T.freeze_sem _ h2
  rw [hA, hB, evalL_encU, evalL_encU] at e2
  have hv := e3.trans e2
  rw [encU, ← toNat_emod_eq_val T _ c hc]
  exact eq_encD _ _ _ _ (freeze_out T h3)
    (by rw [hv, Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt T.p_pos))])

/-- **The square block on encodings.** -/
theorem sqBlk_denote (h : unsatCert T = true) (a c : ZMod T.P.p)
    (hc : (((a.val : ℤ) * (a.val : ℤ) : ℤ) : ZMod T.P.p) = c) :
    (sqBlk T).denote (hvAppend (encU T a) .nil) = encU T c := by
  set W : Valuation (RCtx T.P.n) := pullV (castHom (ctx1_eq T)) (hvAppend (encU T a) .nil)
    with hWdef
  have hget : ∀ i, i < T.P.n → hvGetZ (zvals false W) i = hvGetZ (zvals false (encU T a)) i := by
    intro i hi
    rw [hWdef, hvGetZ_pullV_castHom, hvGetZ_zvals_hvAppend, List.length_replicate, ite_eq_left hi]
  have hW : ValsIn false (ivVec r64 T.tight T.P.n) W :=
    (valsIn_ivVec 64 T.P.n _ W).2 fun i hi => by
      rw [hget i hi]
      exact tight_of_encU T h a i hi
  have hA : rdL (zvals false W) 0 T.P.n = rdL (zvals false (encU T a)) 0 T.P.n := by
    simp only [rdL]
    congr 1
    funext i
    rw [hget _ (by omega)]
  rw [sqBlk, seqM_denote, multiReturnCom_denote_rename, ← hWdef]
  obtain ⟨h2, e2⟩ := T.sq_sem W hW
  obtain ⟨h3, e3⟩ := T.freeze_sem _ h2
  rw [hA, evalL_encU] at e2
  have hv := e3.trans e2
  rw [encU, ← toNat_emod_eq_val T _ c hc]
  exact eq_encD _ _ _ _ (freeze_out T h3)
    (by rw [hv, Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt T.p_pos))])

/-! ## 4. The lowering and the template -/

/-- The encoding: `encU` on `fp p`, and the zero words on every other type. -/
def encLU : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL T.P.n t)
  | .fp q, x => if h : q = T.P.p then encU T (cast (congrArg ZMod h) x) else limbsN T.P.n 0
  | .fp2 _, _ => limbsN T.P.n 0
  | .fp6 _, _ => limbsN T.P.n 0
  | .fp12 _, _ => limbsN T.P.n 0

/-- At the type `.fp p`, the encoding `encLU T` of a value is the words `encU T x`. -/
theorem encLU_fp (x : ZMod T.P.p) : encLU T (t := .fp T.P.p) x = encU T x := by
  simp only [encLU, dite_true]
  rfl

/-- The zero words. -/
abbrev zeroU {Γ : Ctxt jasminDialect} : MultiReturnCom jasminDialect Γ (Rn T.P.n) :=
  CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont.constBlk T.P.n 0

/-- The block of each field operation: `binBlk` for addition, subtraction and multiplication
    at `p`, `sqBlk` for squaring at `p`, and the zero words otherwise. -/
def lowerOpU : LimbBlocks T.P.n
  | .fAdd q => if q = T.P.p then binBlk T .add else zeroU T
  | .fSub q => if q = T.P.p then binBlk T .sub else zeroU T
  | .fMul q => if q = T.P.p then binBlk T .mul else zeroU T
  | .fieldSquare q => if q = T.P.p then sqBlk T else zeroU T
  | _ => zeroU T

end Template

/-- The operations covered at `p`: addition, subtraction, multiplication and squaring. -/
def GoodU (p : Nat) {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) :
    Prop :=
  e.op = .fAdd p ∨ e.op = .fSub p ∨ e.op = .fMul p ∨ e.op = .fieldSquare p

/-- **The block square of the unsaturated lowering.** -/
theorem blockSquareU (T : FieldReprTemplate) (h : unsatCert T = true) :
    (loweringOf (lowerOpU T)).BlockSquare (fun {t} x => encLU T (t := t) x) (GoodU T.P.p) := by
  have hp : 0 < T.P.p := by have := (unsatCert_spec h).1; omega
  have : NeZero T.P.p := ⟨by omega⟩
  intro Γ t e hg vals
  obtain ⟨op, hty, args⟩ := e
  rcases hg with hop | hop | hop | hop <;> subst hop
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpU T (.fAdd T.P.p)).denote (hvAppend (encLU T a) (hvAppend (encLU T b) .nil))
      = encLU T (t := .fp T.P.p) (fAddF a b)
    rw [encLU_fp, encLU_fp, encLU_fp, lowerOpU, ite_eq_left rfl]
    exact binBlk_denote T h .add a b (fAddF a b) (by
      simp only [FieldReprTemplate.BinOp.evalZ]; push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq])
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpU T (.fSub T.P.p)).denote (hvAppend (encLU T a) (hvAppend (encLU T b) .nil))
      = encLU T (t := .fp T.P.p) (fSubF a b)
    rw [encLU_fp, encLU_fp, encLU_fp, lowerOpU, ite_eq_left rfl]
    exact binBlk_denote T h .sub a b (fSubF a b) (by
      simp only [FieldReprTemplate.BinOp.evalZ]; push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq])
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpU T (.fMul T.P.p)).denote (hvAppend (encLU T a) (hvAppend (encLU T b) .nil))
      = encLU T (t := .fp T.P.p) (fMulF a b)
    rw [encLU_fp, encLU_fp, encLU_fp, lowerOpU, ite_eq_left rfl]
    exact binBlk_denote T h .mul a b (fMulF a b) (by
      simp only [FieldReprTemplate.BinOp.evalZ]; push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq])
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpU T (.fieldSquare T.P.p)).denote (hvAppend (encLU T a) .nil)
      = encLU T (t := .fp T.P.p) (fSquareF a)
    rw [encLU_fp, encLU_fp, lowerOpU, ite_eq_left rfl]
    exact sqBlk_denote T h a (fSquareF a) (by
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq])

/-- The operations `GoodUB` accepts: those of `GoodU`. -/
def opGoodUB (p : Nat) : fieldDialect.Op → Bool
  | .fAdd q | .fSub q | .fMul q | .fieldSquare q => q == p
  | _ => false

/-- The coverage decision: every let-bound operation passes `opGoodUB`. -/
def GoodUB (p : Nat) : {Γ : Ctxt fieldDialect} → {t : FieldTy} → Com fieldDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opGoodUB p e.op && GoodUB p body

/-- An expression whose operation the decision `opGoodUB p` accepts satisfies `GoodU p`. -/
theorem opGoodUB_sound (p : Nat) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) (h : opGoodUB p e.op = true) : GoodU p e := by
  obtain ⟨op, _, _⟩ := e
  cases op <;> simp only [opGoodUB, beq_iff_eq, Bool.false_eq_true] at h <;> subst h <;>
    simp [GoodU]

/-- A program accepted by `GoodUB` is `GoodU`-covered. -/
theorem GoodUB_sound (p : Nat) : {Γ : Ctxt fieldDialect} → {t : FieldTy} →
    (c : Com fieldDialect Γ t) → GoodUB p c = true → CoveredCom (GoodU p) c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, h => by
      simp only [GoodUB, Bool.and_eq_true] at h
      exact ⟨opGoodUB_sound p e h.1, GoodUB_sound p body h.2⟩

/-- **The route program of a field program over an unsaturated template**: the straight-line
    program `fieldComOf (lowerOpU T) c` over word arrays of `n` words when `GoodUB` accepts
    `c`, and `none` otherwise. -/
def compileFieldU (T : FieldReprTemplate) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) :
    Option (RouteProg (arrCtx T.P.n Γ ++ [arrTy T.P.n]) (arrTy T.P.n)) :=
  if GoodUB T.P.p c then some (.straight (fieldComOf (lowerOpU T) c)) else none

/-- **The output array of a compiled field program over an unsaturated template.** For input
    arrays whose words are the encodings of the values of `V`, the output array holds the
    words of the encoding of `c.denote V`. -/
theorem compileFieldU_denote (T : FieldReprTemplate) (h : unsatCert T = true)
    {Γ : Ctxt fieldDialect} {t : FieldTy} {c : Com fieldDialect Γ t}
    {rp : RouteProg (arrCtx T.P.n Γ ++ [arrTy T.P.n]) (arrTy T.P.n)}
    (hc : compileFieldU T c = some rp) (V : Valuation Γ) (A : Valuation (arrCtx T.P.n Γ))
    (o : Fin T.P.n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => encLU T (t := t) x) V) :
    arrLimbs (rp.denote (hvAppend A (.cons o .nil))) T.P.n 0 = encLU T (c.denote V) := by
  unfold compileFieldU at hc
  split at hc
  · rename_i hg
    cases hc
    rw [RouteProg.denote_straight]
    exact fieldComOf_denote (lowerOpU T) (fun {t} x => encLU T (t := t) x) (GoodU T.P.p)
      (blockSquareU T h) (unsatCert_spec h).2.1 c (GoodUB_sound T.P.p c hg) V A o hA
  · cases hc

/-- **The unsaturated template** of `T` under its certificate: the canonical digits of the
    representative, routed by `compileFieldU T`. -/
def reprTemplate (T : FieldReprTemplate) (h : unsatCert T = true) : FieldTemplate T.P.n where
  p := T.P.p
  one_lt := (unsatCert_spec h).1
  enc := encU T
  encL := fun {t} x => encLU T (t := t) x
  encL_fp := encLU_fp T
  route := fun c => compileFieldU T c
  route_denote := fun hc => compileFieldU_denote T h hc

/-! ## 5. The template arm -/

/-- The modulus `2^448 - 2^224 - 1` of p448, as a numeral. -/
abbrev p448 : Nat :=
  726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439

/-- The constant `p448` is `2^448 - 2^224 - 1`. -/
theorem p448_eq : p448 = 2 ^ 448 - 2 ^ 224 - 1 := by decide +kernel

/-- The unsaturated instances, each keyed by its modulus: Curve25519 at `5 × 51` and p448 at
    `8 × 56`. -/
def unsatReprs : List (Nat × FieldReprTemplate) :=
  [(2 ^ 255 - 19, curve25519Repr), (p448, p448Repr)]

/-- **The instance chosen at `p`**: the first of `unsatReprs` with modulus `p` whose
    certificate `unsatCert` holds. -/
def unsatReprOf (p : Nat) : Option FieldReprTemplate :=
  (unsatReprs.find? fun e => e.1 == p && (e.2.P.p == p && unsatCert e.2)).map Prod.snd

/-- A representation that `unsatReprOf p` returns has the modulus `p` and satisfies the
    certificate `unsatCert`. -/
theorem unsatReprOf_spec {p : Nat} {T : FieldReprTemplate} (h : unsatReprOf p = some T) :
    T.P.p = p ∧ unsatCert T = true := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.find?_some he
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

/-- **The unsaturated arm of the template dispatcher**: the template of the instance
    `unsatReprOf p`, and `none` when no instance has modulus `p`. -/
def unsatTemplateOf (p : Nat) : Option (Σ n, FieldTemplate n) :=
  match h : unsatReprOf p with
  | some T => some ⟨T.P.n, reprTemplate T (unsatReprOf_spec h).2⟩
  | none => none

/-- A template that the arm `unsatTemplateOf p` returns has the modulus `p`. -/
theorem unsatTemplateOf_spec {p n : Nat} {T : FieldTemplate n}
    (h : unsatTemplateOf p = some ⟨n, T⟩) : T.p = p := by
  unfold unsatTemplateOf at h
  split at h
  · rename_i hs
    cases h
    exact (unsatReprOf_spec hs).1
  · cases h

/-- **The case of an instance**: when `unsatReprOf p` returns `R`, the arm returns the
    template of `R`. -/
theorem unsatTemplateOf_of_unsatReprOf {p : Nat} {R : FieldReprTemplate}
    (h : unsatReprOf p = some R) :
    ∃ hc, unsatTemplateOf p = some ⟨R.P.n, reprTemplate R hc⟩ := by
  refine ⟨(unsatReprOf_spec h).2, ?_⟩
  unfold unsatTemplateOf
  split
  · rename_i h'
    rw [h] at h'
    cases h'
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

/-- The arm `unsatTemplateOf p` returns no template when `unsatReprOf p` returns no
    representation. -/
theorem unsatTemplateOf_of_none {p : Nat} (h : (unsatReprOf p).isNone = true) :
    unsatTemplateOf p = none := by
  unfold unsatTemplateOf
  split
  · rename_i h'
    rw [h'] at h
    cases h
  · rfl

/-! ## 6. The two instances -/

/-- The certificate selects the Curve25519 instance at `p = 2^255 - 19`. -/
theorem unsatReprOf_curve25519 : unsatReprOf (2 ^ 255 - 19) = some curve25519Repr := by
  rfl

/-- The certificate selects the p448 instance at `p = 2^448 - 2^224 - 1`. -/
theorem unsatReprOf_p448 : unsatReprOf p448 = some p448Repr := by
  have h1 : ((2 ^ 255 - 19 : Nat) == p448 &&
      (curve25519Repr.P.p == p448 && unsatCert curve25519Repr)) = false := by
    decide +kernel
  have h2 : (p448 == p448 && (p448Repr.P.p == p448 && unsatCert p448Repr)) = true := by
    decide +kernel
  simp only [unsatReprOf, unsatReprs, List.find?, h1, h2, Option.map_some]

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteUnsat
