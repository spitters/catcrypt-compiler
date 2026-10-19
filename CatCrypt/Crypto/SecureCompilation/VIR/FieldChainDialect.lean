/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.OpInfo
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproductLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithMont

/-!
# The prime-field dialect with representation attributes and its casts

`pfDialect` has one type constructor `PfTy.pf p r`: an element of the prime field `ZMod p`
stored in the representation `r : FieldRepr`, either canonical (`canon`, the stored residue
is the value `x`) or Montgomery with radix `2 ^ k` (`mont k`, the stored residue is
`x * 2 ^ k`). The denotation of `pf p r` is `ZMod p` at every `r`: the attribute fixes how a
later lowering stores the value, and the operations denote the field operations on values.
`toMont p k` and `fromMont p k` change the attribute between `canon` and `mont k` and are the
identity on the value.

Two dialects put the field values beside a machine layer. In `jasField` the operations of
`jasminDialect` and of `pfDialect` (the coproduct `Dialect.sum jasminDialect pfDialect`, with
type alphabet `JasminTy ⊕ PfTy`) are joined with the casts `CastOp` (`Dialect.opSum`):
`toWords p r w n` writes the stored residue of a field value as `n` little-endian words of
`w` bits (a `stackArr w n` of `jasminDialect`), and `fromWords p r w n` reads `n` words back,
failing when their value is not below `p`. The casts are the only operations whose
denotation fails, so `jasField` denotes in `Option` (`DialectDenoteM jasField Option`). In
`jasMod` the operations of `jasminDialect` and of `modArithDialect` (the coproduct
`jasModArith`, with type alphabet `JasminTy ⊕ ModArithTy`) are joined with the word casts
`ModWordCastOp`: `toWordsM p w n` writes a residue of `ZMod p` as `n` little-endian words of
`w` bits, and `fromWordsM p w n` reads `n` words back as a residue, failing when their value
is not below `p`; `jasMod` denotes in `Option` as well (`DialectDenoteM jasMod Option`).

The leakage model of `pfDialect` is quiet on every operation, as `fieldLeakModel` of
`Hax/NFFieldSumLeak.lean` is on every operation other than inversion; the casts are quiet as
well. The leakage model of `jasField` is `sumLeak` of a leakage model of `jasminDialect` and
`pfLeakModel`, and that of `jasMod` is `sumLeak` of leakage models of `jasminDialect` and
`modArithDialect`; both are extended by the quiet casts.

## Main definitions

* `FieldRepr`, `FieldRepr.toRep`, `FieldRepr.ofRep`, `FieldRepr.Admissible`: the
  representations, the stored residue of a value and the value of a stored residue.
* `PfTy`, `PfOp`, `pfDialect`, `pfTraits`, `pfLeakModel`, `pfOpInfo`.
* `wordsVal`, `wordsOf`, `fromWordsF`, `toWordsF`: the value of a word tuple, the word tuple
  of a value, and the two casts as functions.
* `CastOp`, `castDialect`, `jasPf`, `jasField`, `jasFieldTraits`, `jasFieldLeak`,
  `jasFieldOpInfo`.
* `fromWordsMF`, `toWordsMF`: the word casts of `mod_arith` residues as functions.
* `ModWordCastOp`, `modWordCastDialect`, `jasModArith`, `jasMod`, `jasModTraits`,
  `jasModLeak`, `jasModOpInfo`.

## Main results

* `FieldRepr.ofRep_toRep`, `FieldRepr.toRep_ofRep`: the stored residue and its read-back are
  inverse under an admissible representation; `FieldRepr.toRep_mont_eq` and
  `FieldRepr.toRep_canon_eq` identify `toRep` with `MontParams.toRep` of
  `VIR/FieldToModArithMont.lean`; `FieldRepr.toRep_add`, `FieldRepr.toRep_sub`,
  `FieldRepr.toRep_neg`: the stored residue commutes with addition, subtraction and negation.
* `pfDialect.denote_add`, …, `pfDialect.denote_toMont`, `pfDialect.denote_fromMont`: the
  value of every operation.
* `wordsVal_wordsOf`, `wordsOf_wordsVal`, `wordsVal_lt`: the word encoding of naturals.
* `fromWordsF_toWordsF`, `toWordsF_of_fromWordsF_eq_some`, `toWordsF_fromWordsF`,
  `isSome_fromWordsF_iff`: the casts
  are inverse on canonical word tuples, and `fromWords` succeeds exactly on them.
* `jasField_denoteM_jasmin`, `jasField_denoteM_pf`, `jasField_denoteM_fromWords`,
  `jasField_denoteM_toWords`: the denotation of each summand inside `jasField`.
* `pfConstLaw`, `pfSpecLaw`, `pfPureLaw`, `jasFieldTraits_constLaw`, `jasFieldTraits_specLaw`,
  `modWordCastSpecLaw`, `jasModTraits_specLaw`: the laws of the records.
* `jasFieldLeak_ctLeak_pf`, `jasFieldLeak_ctLeak_cast`, `jasModLeak_ctLeak_cast`: a field
  operation and a cast emit no event.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-! ## 1. Representations -/

/-- The representation of a prime-field element: canonical, or Montgomery with radix
    `2 ^ k`. -/
inductive FieldRepr where
  /-- The stored residue is the value. -/
  | canon
  /-- The stored residue is the value times `2 ^ k`. -/
  | mont (k : Nat)
  deriving DecidableEq, Repr

namespace FieldRepr

/-- The stored residue of the value `x` in the representation `r`. -/
def toRep {p : Nat} : FieldRepr → ZMod p → ZMod p
  | canon, x => x
  | mont k, x => x * 2 ^ k

/-- The value of the stored residue `y` in the representation `r`. -/
def ofRep {p : Nat} : FieldRepr → ZMod p → ZMod p
  | canon, y => y
  | mont k, y => y * (2 ^ k)⁻¹

/-- A representation is admissible at the modulus `p` when its radix is invertible modulo
    `p`: always for `canon`, and for `mont k` when `2` is coprime to `p`. -/
def Admissible (p : Nat) : FieldRepr → Prop
  | canon => True
  | mont _ => Nat.Coprime 2 p

/-- At an odd modulus the power `2 ^ k` is a unit of `ZMod p`. -/
theorem isUnit_two_pow {p : Nat} (h : Nat.Coprime 2 p) (k : Nat) :
    IsUnit ((2 : ZMod p) ^ k) := by
  have h2 : IsUnit ((2 : ℕ) : ZMod p) := (ZMod.isUnit_iff_coprime 2 p).2 h
  rw [Nat.cast_ofNat] at h2
  exact h2.pow k

/-- The read-back of the stored residue is the value. -/
theorem ofRep_toRep {p : Nat} {r : FieldRepr} (hr : r.Admissible p) (x : ZMod p) :
    r.ofRep (r.toRep x) = x := by
  cases r with
  | canon => rfl
  | mont k =>
      show x * 2 ^ k * (2 ^ k)⁻¹ = x
      rw [mul_assoc, ZMod.mul_inv_of_unit _ (isUnit_two_pow hr k), mul_one]

/-- The stored residue of the read-back is the residue. -/
theorem toRep_ofRep {p : Nat} {r : FieldRepr} (hr : r.Admissible p) (y : ZMod p) :
    r.toRep (r.ofRep y) = y := by
  cases r with
  | canon => rfl
  | mont k =>
      show y * (2 ^ k)⁻¹ * 2 ^ k = y
      rw [mul_assoc, ZMod.inv_mul_of_unit _ (isUnit_two_pow hr k), mul_one]

/-- The Montgomery representation with radix `2 ^ k` stores what `MontParams.toRep` stores
    at a Montgomery modulus of radix `2 ^ k`. -/
theorem toRep_mont_eq (M : FieldToModArithMont.MontParams) {p k : Nat}
    (hM : M.isMont p = true) (hR : M.R p = 2 ^ k) (x : ZMod p) :
    (mont k).toRep x = M.toRep x := by
  simp only [toRep, FieldToModArithMont.MontParams.toRep, hM, hR, if_true]

/-- The canonical representation stores what `MontParams.toRep` stores at a modulus whose
    Montgomery flag is unset. -/
theorem toRep_canon_eq (M : FieldToModArithMont.MontParams) {p : Nat}
    (hM : M.isMont p = false) (x : ZMod p) : canon.toRep x = M.toRep x := by
  simp only [toRep, FieldToModArithMont.MontParams.toRep, hM, Bool.false_eq_true, if_false]

/-- The stored residue of a sum is the sum of the stored residues. -/
theorem toRep_add {p : Nat} (r : FieldRepr) (a b : ZMod p) :
    r.toRep a + r.toRep b = r.toRep (a + b) := by
  cases r
  · rfl
  · simp only [toRep]
    ring

/-- The stored residue of a difference is the difference of the stored residues. -/
theorem toRep_sub {p : Nat} (r : FieldRepr) (a b : ZMod p) :
    r.toRep a - r.toRep b = r.toRep (a - b) := by
  cases r
  · rfl
  · simp only [toRep]
    ring

/-- The stored residue of a negation is the negation of the stored residue. -/
theorem toRep_neg {p : Nat} (r : FieldRepr) (a : ZMod p) : -r.toRep a = r.toRep (-a) := by
  cases r
  · rfl
  · simp only [toRep]
    ring

end FieldRepr

/-! ## 2. The dialect `pfDialect` -/

/-- The type alphabet of `pfDialect`: the prime field `ZMod p` in the representation `r`. -/
inductive PfTy where
  /-- An element of `ZMod p` stored in the representation `r`. -/
  | pf (p : Nat) (r : FieldRepr)
  deriving DecidableEq

/-- Every type of `pfDialect` denotes its prime field. -/
@[reducible] instance : TyDenote PfTy where
  denote
    | .pf p _ => ZMod p

/-- The operations of `pfDialect`. -/
inductive PfOp where
  /-- Addition at the representation `r`. -/
  | add (p : Nat) (r : FieldRepr)
  /-- Subtraction at the representation `r`. -/
  | sub (p : Nat) (r : FieldRepr)
  /-- Negation at the representation `r`. -/
  | neg (p : Nat) (r : FieldRepr)
  /-- Multiplication at the representation `r`. -/
  | mul (p : Nat) (r : FieldRepr)
  /-- Squaring at the representation `r`. -/
  | square (p : Nat) (r : FieldRepr)
  /-- Doubling at the representation `r`. -/
  | double (p : Nat) (r : FieldRepr)
  /-- The constant `c` at the representation `r`. -/
  | const (p : Nat) (r : FieldRepr) (c : ZMod p)
  /-- The copy of a value at the representation `r`. -/
  | copy (p : Nat) (r : FieldRepr)
  /-- The change of representation from `canon` to `mont k`. -/
  | toMont (p k : Nat)
  /-- The change of representation from `mont k` to `canon`. -/
  | fromMont (p k : Nat)
  deriving DecidableEq

/-- The prime-field dialect with representation attributes. -/
@[reducible] def pfDialect : Dialect := { Op := PfOp, Ty := PfTy }

instance : DialectSignature pfDialect where
  sig
    | .add p r => [.pf p r, .pf p r]
    | .sub p r => [.pf p r, .pf p r]
    | .neg p r => [.pf p r]
    | .mul p r => [.pf p r, .pf p r]
    | .square p r => [.pf p r]
    | .double p r => [.pf p r]
    | .const _ _ _ => []
    | .copy p r => [.pf p r]
    | .toMont p _ => [.pf p .canon]
    | .fromMont p k => [.pf p (.mont k)]
  ret
    | .add p r => .pf p r
    | .sub p r => .pf p r
    | .neg p r => .pf p r
    | .mul p r => .pf p r
    | .square p r => .pf p r
    | .double p r => .pf p r
    | .const p r _ => .pf p r
    | .copy p r => .pf p r
    | .toMont p k => .pf p (.mont k)
    | .fromMont p _ => .pf p .canon

/-- The denotation of `pfDialect`: the field operations on values; `toMont` and `fromMont`
    are the identity. -/
instance pfDenote : DialectDenote pfDialect where
  denote
    | .add _ _, args => modAddF args.head args.tail.head
    | .sub _ _, args => modSubF args.head args.tail.head
    | .neg _ _, args => modNegF args.head
    | .mul _ _, args => modMulF args.head args.tail.head
    | .square _ _, args => modMulF args.head args.head
    | .double _ _, args => modAddF args.head args.head
    | .const _ _ c, _ => modConstF c
    | .copy _ _, args => modCopyF args.head
    | .toMont _ _, args => modCopyF args.head
    | .fromMont _ _, args => modCopyF args.head

namespace pfDialect

variable {p : Nat} {r : FieldRepr}

/-- The value of `add`. -/
theorem denote_add (a b : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.add p r) (.cons a (.cons b .nil)) = a + b := rfl

/-- The value of `sub`. -/
theorem denote_sub (a b : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.sub p r) (.cons a (.cons b .nil)) = a - b := rfl

/-- The value of `neg`. -/
theorem denote_neg (a : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.neg p r) (.cons a .nil) = -a := rfl

/-- The value of `mul`. -/
theorem denote_mul (a b : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.mul p r) (.cons a (.cons b .nil)) = a * b := rfl

/-- The value of `square`. -/
theorem denote_square (a : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.square p r) (.cons a .nil) = a * a := rfl

/-- The value of `double`. -/
theorem denote_double (a : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.double p r) (.cons a .nil) = a + a := rfl

/-- The value of `const`. -/
theorem denote_const (c : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.const p r c) .nil = c := rfl

/-- The value of `copy`. -/
theorem denote_copy (a : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.copy p r) (.cons a .nil) = a := rfl

/-- `toMont` is the identity on the value. -/
theorem denote_toMont {k : Nat} (a : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.toMont p k) (.cons a .nil) = a := rfl

/-- `fromMont` is the identity on the value. -/
theorem denote_fromMont {k : Nat} (a : ZMod p) :
    DialectDenote.denote (d := pfDialect) (.fromMont p k) (.cons a .nil) = a := rfl

/-- The stored residue changes by `toMont` from `x` to `x * 2 ^ k`. -/
theorem toRep_toMont {k : Nat} (a : ZMod p) :
    (FieldRepr.mont k).toRep
        (DialectDenote.denote (d := pfDialect) (.toMont p k) (.cons a .nil)) =
      FieldRepr.canon.toRep a * 2 ^ k := rfl

end pfDialect

/-! ## 3. The operation information of `pfDialect` -/

/-- The operation properties of `pfDialect`: every operation is pure and speculatable, the
    constants are constant-like, and every operation costs one. -/
def pfTraits : OpTraits pfDialect where
  pure _ := true
  speculatable _ := true
  constLike
    | .const _ _ _ => true
    | _ => false
  cost _ := 1

/-- The leakage model of `pfDialect`: every operation is quiet, and a value reads as the
    least natural representative of its stored residue. -/
def pfLeakModel : LeakModel pfDialect where
  kind _ := .quiet
  valNat
    | .pf _ r, x => (r.toRep x).val

/-- The operation information of `pfDialect`. -/
def pfOpInfo : OpInfo pfDialect := { pfTraits, pfLeakModel with }

/-- The constants of `pfDialect` take no argument. -/
theorem pfConstLaw : ConstLaw pfTraits := by
  intro op h
  cases op <;> first | rfl | simp [pfTraits] at h

/-- Every operation of `pfDialect` succeeds. -/
theorem pfSpecLaw : SpecLaw pfTraits := fun _ _ _ => rfl

/-- Every operation of `pfDialect` denotes in `Option` the return of its value. -/
theorem pfPureLaw : PureLaw pfTraits Option := fun _ _ _ => rfl

/-- An expression of `pfDialect` emits no event. -/
theorem pfLeak_ctLeak {Γ : Ctxt pfDialect} {t : PfTy} (e : Expr pfDialect Γ t)
    (V : Valuation Γ) : Expr.ctLeak pfLeakModel e V = [] :=
  Expr.ctLeak_of_quiet pfLeakModel e rfl V

/-! ## 4. Word tuples -/

/-- The little-endian value of `n` words of `w` bits. -/
def wordsVal {w : Nat} : (n : Nat) → (Fin n → BitVec w) → Nat
  | 0, _ => 0
  | n + 1, ws => (ws 0).toNat + 2 ^ w * wordsVal n (fun i => ws i.succ)

/-- The `n` little-endian words of `w` bits of the natural number `N`: word `i` holds the
    bits `w * i` to `w * i + w - 1` of `N`. -/
def wordsOf (w n N : Nat) : Fin n → BitVec w :=
  fun i => BitVec.ofNat w (N / 2 ^ (w * i))

/-- The words of `N` are the low word of `N` followed by the words of `N / 2 ^ w`. -/
theorem wordsOf_succ (w n N : Nat) (i : Fin n) :
    wordsOf w (n + 1) N i.succ = wordsOf w n (N / 2 ^ w) i := by
  simp only [wordsOf, Fin.val_succ, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  ring

/-- The value of `n` words is below `2 ^ (w * n)`. -/
theorem wordsVal_lt {w : Nat} : (n : Nat) → (ws : Fin n → BitVec w) →
    wordsVal n ws < 2 ^ (w * n)
  | 0, _ => by simp [wordsVal]
  | n + 1, ws => by
      have h0 := (ws 0).isLt
      have h1 := wordsVal_lt n (fun i => ws i.succ)
      show (ws 0).toNat + 2 ^ w * wordsVal n _ < 2 ^ (w * (n + 1))
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * n))]
      have : 2 ^ w * wordsVal n (fun i => ws i.succ) + 2 ^ w ≤ 2 ^ w * 2 ^ (w * n) := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ h1
      omega

/-- The value of the words of `N` is `N` modulo `2 ^ (w * n)`. -/
theorem wordsVal_wordsOf (w : Nat) : (n N : Nat) → wordsVal n (wordsOf w n N) = N % 2 ^ (w * n)
  | 0, N => by simp [wordsVal, Nat.mod_one]
  | n + 1, N => by
      show (wordsOf w (n + 1) N 0).toNat + 2 ^ w * wordsVal n (fun i => wordsOf w (n + 1) N i.succ)
        = _
      simp only [wordsOf_succ, wordsVal_wordsOf w n]
      simp only [wordsOf, Fin.val_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
        BitVec.toNat_ofNat]
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * n)), Nat.mod_mul]

/-- The words of the value of `n` words are the words. -/
theorem wordsOf_wordsVal {w : Nat} : (n : Nat) → (ws : Fin n → BitVec w) →
    wordsOf w n (wordsVal n ws) = ws
  | 0, ws => funext fun i => i.elim0
  | n + 1, ws => by
      have hdiv : wordsVal (n + 1) ws / 2 ^ w = wordsVal n (fun i => ws i.succ) := by
        show ((ws 0).toNat + 2 ^ w * wordsVal n _) / 2 ^ w = _
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt (ws 0).isLt,
          Nat.zero_add]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · show BitVec.ofNat w ((wordsVal (n + 1) ws) / 2 ^ (w * 0)) = ws 0
        rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
        show BitVec.ofNat w ((ws 0).toNat + 2 ^ w * wordsVal n _) = ws 0
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ws 0).isLt]
      · rw [wordsOf_succ, hdiv, wordsOf_wordsVal n]

/-! ## 5. The casts as functions -/

/-- The cast from `n` words of `w` bits to the field `ZMod p` at the representation `r`:
    the word tuple holds the stored residue, and the cast fails when the value of the
    words is not below `p`. -/
def fromWordsF (p : Nat) (r : FieldRepr) (w n : Nat) (ws : Fin n → BitVec w) :
    Option (ZMod p) :=
  if wordsVal n ws < p then some (r.ofRep (wordsVal n ws : ZMod p)) else none

/-- The cast from the field `ZMod p` at the representation `r` to `n` words of `w` bits:
    the words of the least natural representative of the stored residue. -/
def toWordsF (p : Nat) (r : FieldRepr) (w n : Nat) (x : ZMod p) : Fin n → BitVec w :=
  wordsOf w n (r.toRep x).val

/-- `fromWords` succeeds exactly on the word tuples whose value is below `p`. -/
theorem isSome_fromWordsF_iff (p : Nat) (r : FieldRepr) (w n : Nat) (ws : Fin n → BitVec w) :
    (fromWordsF p r w n ws).isSome ↔ wordsVal n ws < p := by
  unfold fromWordsF
  split <;> simp_all

/-- **`fromWords ∘ toWords`.** When `p` is positive and fits in `n` words of `w` bits, and
    the representation is admissible, reading back the words of a value gives the value. -/
theorem fromWordsF_toWordsF {p : Nat} {r : FieldRepr} {w n : Nat} (hp : 0 < p)
    (hpw : p ≤ 2 ^ (w * n)) (hr : r.Admissible p) (x : ZMod p) :
    fromWordsF p r w n (toWordsF p r w n x) = some x := by
  have : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
  have hlt : (r.toRep x).val < p := ZMod.val_lt _
  have hv : wordsVal n (toWordsF p r w n x) = (r.toRep x).val := by
    rw [toWordsF, wordsVal_wordsOf, Nat.mod_eq_of_lt (lt_of_lt_of_le hlt hpw)]
  rw [fromWordsF, hv, if_pos hlt, ZMod.natCast_zmod_val, FieldRepr.ofRep_toRep hr]

/-- **`toWords ∘ fromWords`.** On a word tuple `fromWords` accepts, writing the value back
    gives the word tuple. -/
theorem toWordsF_of_fromWordsF_eq_some {p : Nat} {r : FieldRepr} {w n : Nat}
    (hr : r.Admissible p) (ws : Fin n → BitVec w) (x : ZMod p)
    (h : fromWordsF p r w n ws = some x) : toWordsF p r w n x = ws := by
  unfold fromWordsF at h
  split at h
  · rename_i hlt
    cases h
    rw [toWordsF, FieldRepr.toRep_ofRep hr, ZMod.val_natCast, Nat.mod_eq_of_lt hlt,
      wordsOf_wordsVal]
  · cases h

/-- On a word tuple whose value is below `p`, `toWords ∘ fromWords` is the identity. -/
theorem toWordsF_fromWordsF {p : Nat} {r : FieldRepr} {w n : Nat} (hr : r.Admissible p)
    (ws : Fin n → BitVec w) (hlt : wordsVal n ws < p) :
    ∃ x, fromWordsF p r w n ws = some x ∧ toWordsF p r w n x = ws := by
  refine ⟨r.ofRep (wordsVal n ws : ZMod p), by rw [fromWordsF, if_pos hlt], ?_⟩
  exact toWordsF_of_fromWordsF_eq_some hr ws _ (by rw [fromWordsF, if_pos hlt])

/-! ## 6. The casts of `jasField` -/

/-- The casts between the word tuples of `jasminDialect` and the field values of
    `pfDialect`. -/
inductive CastOp where
  /-- Read `n` words of `w` bits as an element of `ZMod p` stored in the representation
      `r`; fails when the value of the words is not below `p`. -/
  | fromWords (p : Nat) (r : FieldRepr) (w n : Nat)
  /-- Write the stored residue of an element of `ZMod p` in the representation `r` as `n`
      words of `w` bits. -/
  | toWords (p : Nat) (r : FieldRepr) (w n : Nat)
  deriving DecidableEq

/-- The dialect of the casts, over the type alphabet `JasminTy ⊕ PfTy`. -/
@[reducible] def castDialect : Dialect := { Op := CastOp, Ty := JasminTy ⊕ PfTy }

instance : DialectSignature castDialect where
  sig
    | .fromWords _ _ w n => [.inl (.stackArr w n)]
    | .toWords p r _ _ => [.inr (.pf p r)]
  ret
    | .fromWords p r _ _ => .inr (.pf p r)
    | .toWords _ _ w n => .inl (.stackArr w n)

/-- The `Option` denotation of the casts: `fromWordsF` and `toWordsF`. -/
instance castDenoteM : DialectDenoteM castDialect Option where
  denoteM
    | .fromWords p r w n, args => fromWordsF p r w n args.head
    | .toWords p r w n, args => some (toWordsF p r w n args.head)

/-- The operation properties of the casts: `toWords` is speculatable; no cast is pure or
    constant-like; every cast costs one. -/
def castTraits : OpTraits castDialect where
  pure _ := false
  speculatable
    | .fromWords _ _ _ _ => false
    | .toWords _ _ _ _ => true
  constLike _ := false
  cost _ := 1

/-- `toWords` succeeds at every argument. -/
theorem castSpecLaw : SpecLaw castTraits := by
  intro op h args
  cases op with
  | fromWords => simp [castTraits] at h
  | toWords => rfl

/-! ## 7. The dialect `jasField` -/

/-- The coproduct of `jasminDialect` and `pfDialect`. -/
abbrev jasPf : Dialect := Dialect.sum jasminDialect pfDialect

instance : DialectSignature jasPf := instDialectSignatureSum (d := jasminDialect) (e := pfDialect)

/-- The denotation of `jasPf`: each summand by its own denotation. -/
instance jasPfDenote : DialectDenote jasPf :=
  instDialectDenoteSum (d := jasminDialect) (e := pfDialect)

/-- The field dialect over `jasminDialect`: the operations of `jasminDialect` and
    `pfDialect`, and the casts between word tuples and field values. -/
abbrev jasField : Dialect := Dialect.opSum jasPf castDialect

instance : DialectSignature jasField :=
  DialectOpSum.instDialectSignatureOpSum (O₁ := jasPf.Op) (O₂ := CastOp)
    (T := JasminTy ⊕ PfTy)

/-- The `Option` denotation of `jasField`: the operations of `jasPf` succeed with their
    value, the casts denote by `castDenoteM`. -/
instance jasFieldDenoteM : DialectDenoteM jasField Option :=
  DialectOpSum.instDialectDenoteMOpSum (O₁ := jasPf.Op) (O₂ := CastOp)
    (T := JasminTy ⊕ PfTy)

/-- The trip counter of `jasField` is the 64-bit register of `jasminDialect`. -/
instance : HasWord64 jasField where
  word := .inl (JasminTy.reg 64)
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- The branch bit of `jasField` is the 1-bit register of `jasminDialect`, read as `true`
    exactly at `1#1`. -/
instance : HasBoolBit jasField where
  bit := .inl (JasminTy.reg 1)
  toBool := fun (b : BitVec 1) => decide (b = 1#1)

/-- `jasField` denotes calls in the empty environment. -/
instance : CallDenote jasField := ⟨.empty⟩

/-- An operation of `jasminDialect` denotes in `jasField` its value in `jasminDialect`. -/
theorem jasField_denoteM_jasmin (o : JasminOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasField) (.inl (.inl o)))) :
    DialectDenoteM.denoteM (d := jasField) (M := Option) (.inl (.inl o)) args =
      some (DialectDenote.denote (d := jasminDialect) o (unmapInl args)) := rfl

/-- An operation of `pfDialect` denotes in `jasField` its value in `pfDialect`. -/
theorem jasField_denoteM_pf (o : PfOp)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasField) (.inl (.inr o)))) :
    DialectDenoteM.denoteM (d := jasField) (M := Option) (.inl (.inr o)) args =
      some (DialectDenote.denote (d := pfDialect) o (unmapInr args)) := rfl

/-- `fromWords` denotes in `jasField` the cast `fromWordsF`. -/
theorem jasField_denoteM_fromWords (p : Nat) (r : FieldRepr) (w n : Nat)
    (ws : Fin n → BitVec w) :
    DialectDenoteM.denoteM (d := jasField) (M := Option) (.inr (.fromWords p r w n))
      (.cons ws .nil) = fromWordsF p r w n ws := rfl

/-- `toWords` denotes in `jasField` the cast `toWordsF`. -/
theorem jasField_denoteM_toWords (p : Nat) (r : FieldRepr) (w n : Nat) (x : ZMod p) :
    DialectDenoteM.denoteM (d := jasField) (M := Option) (.inr (.toWords p r w n))
      (.cons x .nil) = some (toWordsF p r w n x) := rfl

/-! ## 8. The operation information of `jasField` -/

/-- The operation properties of `jasPf` from a record of `jasminDialect` and `pfTraits`. -/
def jasPfTraits (T : OpTraits jasminDialect) : OpTraits jasPf where
  pure := Sum.elim T.pure pfTraits.pure
  speculatable := Sum.elim T.speculatable pfTraits.speculatable
  constLike := Sum.elim T.constLike pfTraits.constLike
  cost := Sum.elim T.cost pfTraits.cost

/-- The operation properties of `jasField` from a record of `jasminDialect`. -/
def jasFieldTraits (T : OpTraits jasminDialect) : OpTraits jasField :=
  (jasPfTraits T).opSum castTraits

/-- The leakage model of `jasField` from a leakage model `M` of `jasminDialect`: the
    coproduct model `sumLeak M pfLeakModel` on the operations of `jasPf`, and the quiet
    class on the casts. -/
def jasFieldLeak (M : LeakModel jasminDialect) : LeakModel jasField where
  kind := Sum.elim (sumLeak M pfLeakModel).kind fun
    | .fromWords .. => .quiet
    | .toWords .. => .quiet
  valNat := (sumLeak M pfLeakModel).valNat

/-- The operation information of `jasField` from that of `jasminDialect`. -/
def jasFieldOpInfo (I : OpInfo jasminDialect) : OpInfo jasField :=
  { jasFieldTraits I.toOpTraits, jasFieldLeak I.toLeakModel with }

/-- The constant law of `jasminDialect` gives the constant law of `jasField`. -/
theorem jasFieldTraits_constLaw {T : OpTraits jasminDialect} (hT : ConstLaw T) :
    ConstLaw (jasFieldTraits T)
  | .inl (.inl o), h => by
      show (DialectSignature.sig (d := jasminDialect) o).map Sum.inl = []
      rw [hT o h]
      rfl
  | .inl (.inr o), h => by
      show (DialectSignature.sig (d := pfDialect) o).map Sum.inr = []
      rw [pfConstLaw o h]
      rfl
  | .inr _, h => by simp [jasFieldTraits, OpTraits.opSum, castTraits] at h

/-- The speculation law of `jasField`: every operation of `jasPf` succeeds, and `toWords`
    succeeds; the record of `jasminDialect` may mark any of its operations
    speculatable. -/
theorem jasFieldTraits_specLaw (T : OpTraits jasminDialect) : SpecLaw (jasFieldTraits T)
  | .inl (.inl _), _, _ => rfl
  | .inl (.inr _), _, _ => rfl
  | .inr o, h, args => castSpecLaw o h args

/-- An operation of `pfDialect` emits no event in `jasField`. -/
theorem jasFieldLeak_ctLeak_pf (M : LeakModel jasminDialect) {Γ : Ctxt jasField}
    {t : jasField.Ty} (e : Expr jasField Γ t) (o : PfOp) (h : e.op = .inl (.inr o))
    (V : Valuation Γ) : Expr.ctLeak (jasFieldLeak M) e V = [] :=
  Expr.ctLeak_of_quiet _ e (by rw [h]; rfl) V

/-- A cast emits no event in `jasField`. -/
theorem jasFieldLeak_ctLeak_cast (M : LeakModel jasminDialect) {Γ : Ctxt jasField}
    {t : jasField.Ty} (e : Expr jasField Γ t) (o : CastOp) (h : e.op = .inr o)
    (V : Valuation Γ) : Expr.ctLeak (jasFieldLeak M) e V = [] :=
  Expr.ctLeak_of_quiet _ e (by rw [h]; cases o <;> rfl) V

/-- An operation of `jasminDialect` has in `jasField` the event class of `M`. -/
@[simp] theorem jasFieldLeak_kind_jasmin (M : LeakModel jasminDialect) (o : JasminOp) :
    (jasFieldLeak M).kind (.inl (.inl o)) = M.kind o := rfl

/-! ## 9. The word casts of residues -/

/-- The cast from `n` words of `w` bits to a residue of `ZMod p`: fails when the value of
    the words is not below `p`. -/
def fromWordsMF (p w n : Nat) (ws : Fin n → BitVec w) : Option (ZMod p) :=
  if wordsVal n ws < p then some (wordsVal n ws : ZMod p) else none

/-- The cast from a residue of `ZMod p` to `n` words of `w` bits: the words of its least
    natural representative. -/
def toWordsMF (p w n : Nat) (y : ZMod p) : Fin n → BitVec w :=
  wordsOf w n y.val

/-- The casts between the word tuples of `jasminDialect` and the residues of
    `modArithDialect`. -/
inductive ModWordCastOp where
  /-- Read `n` words of `w` bits as a residue of `ZMod p`; fails when the value of the words
      is not below `p`. -/
  | fromWordsM (p w n : Nat)
  /-- Write a residue of `ZMod p` as `n` words of `w` bits. -/
  | toWordsM (p w n : Nat)
  deriving DecidableEq

/-- The dialect of the word casts, over the type alphabet `JasminTy ⊕ ModArithTy`. -/
@[reducible] def modWordCastDialect : Dialect :=
  { Op := ModWordCastOp, Ty := JasminTy ⊕ ModArithTy }

instance : DialectSignature modWordCastDialect where
  sig
    | .fromWordsM _ w n => [.inl (.stackArr w n)]
    | .toWordsM p _ _ => [.inr (.fp p)]
  ret
    | .fromWordsM p _ _ => .inr (.fp p)
    | .toWordsM _ w n => .inl (.stackArr w n)

/-- The `Option` denotation of the word casts: `fromWordsMF` and `toWordsMF`. -/
instance modWordCastDenoteM : DialectDenoteM modWordCastDialect Option where
  denoteM
    | .fromWordsM p w n, args => fromWordsMF p w n args.head
    | .toWordsM p w n, args => some (toWordsMF p w n args.head)

/-- The operation properties of the word casts: `toWordsM` is speculatable; no cast is
    pure or constant-like; every cast costs one. -/
def modWordCastTraits : OpTraits modWordCastDialect where
  pure _ := false
  speculatable
    | .fromWordsM _ _ _ => false
    | .toWordsM _ _ _ => true
  constLike _ := false
  cost _ := 1

/-- `toWordsM` succeeds at every argument. -/
theorem modWordCastSpecLaw : SpecLaw modWordCastTraits := by
  intro op h args
  cases op with
  | fromWordsM => simp [modWordCastTraits] at h
  | toWordsM => rfl

/-! ## 10. The dialect `jasMod` -/

/-- The coproduct of `jasminDialect` and `modArithDialect`. -/
abbrev jasModArith : Dialect := Dialect.sum jasminDialect modArithDialect

instance : DialectSignature jasModArith :=
  instDialectSignatureSum (d := jasminDialect) (e := modArithDialect)

/-- The denotation of `jasModArith`: each summand by its own denotation. -/
instance jasModArithDenote : DialectDenote jasModArith :=
  instDialectDenoteSum (d := jasminDialect) (e := modArithDialect)

/-- The `mod_arith` dialect over `jasminDialect`: the operations of `jasminDialect` and
    `modArithDialect`, and the casts between word tuples and residues. -/
abbrev jasMod : Dialect := Dialect.opSum jasModArith modWordCastDialect

instance : DialectSignature jasMod :=
  DialectOpSum.instDialectSignatureOpSum (O₁ := jasModArith.Op) (O₂ := ModWordCastOp)
    (T := JasminTy ⊕ ModArithTy)

/-- The `Option` denotation of `jasMod`: the operations of `jasModArith` succeed with their
    value, the casts denote by `modWordCastDenoteM`. -/
instance jasModDenoteM : DialectDenoteM jasMod Option :=
  DialectOpSum.instDialectDenoteMOpSum (O₁ := jasModArith.Op) (O₂ := ModWordCastOp)
    (T := JasminTy ⊕ ModArithTy)

/-- The trip counter of `jasMod` is the 64-bit register of `jasminDialect`. -/
instance : HasWord64 jasMod where
  word := .inl (JasminTy.reg 64)
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- The branch bit of `jasMod` is the 1-bit register of `jasminDialect`, read as `true`
    exactly at `1#1`. -/
instance : HasBoolBit jasMod where
  bit := .inl (JasminTy.reg 1)
  toBool := fun (b : BitVec 1) => decide (b = 1#1)

/-- `jasMod` denotes calls in the empty environment. -/
instance : CallDenote jasMod := ⟨.empty⟩

/-- The operation properties of `jasModArith` from records of `jasminDialect` and
    `modArithDialect`. -/
def jasModArithTraits (T : OpTraits jasminDialect) (U : OpTraits modArithDialect) :
    OpTraits jasModArith where
  pure := Sum.elim T.pure U.pure
  speculatable := Sum.elim T.speculatable U.speculatable
  constLike := Sum.elim T.constLike U.constLike
  cost := Sum.elim T.cost U.cost

/-- The operation properties of `jasMod` from records of `jasminDialect` and
    `modArithDialect`. -/
def jasModTraits (T : OpTraits jasminDialect) (U : OpTraits modArithDialect) :
    OpTraits jasMod :=
  (jasModArithTraits T U).opSum modWordCastTraits

/-- The leakage model of `jasMod` from leakage models `M` of `jasminDialect` and `N` of
    `modArithDialect`: the coproduct model `sumLeak M N` on the operations of `jasModArith`,
    and the quiet class on the casts. -/
def jasModLeak (M : LeakModel jasminDialect) (N : LeakModel modArithDialect) :
    LeakModel jasMod where
  kind := Sum.elim (sumLeak M N).kind fun
    | .fromWordsM .. => .quiet
    | .toWordsM .. => .quiet
  valNat := (sumLeak M N).valNat

/-- The operation information of `jasMod` from that of `jasminDialect` and
    `modArithDialect`. -/
def jasModOpInfo (I : OpInfo jasminDialect) (J : OpInfo modArithDialect) : OpInfo jasMod :=
  { jasModTraits I.toOpTraits J.toOpTraits, jasModLeak I.toLeakModel J.toLeakModel with }

/-- The speculation law of `jasMod`: every operation of `jasModArith` succeeds, and
    `toWordsM` succeeds. -/
theorem jasModTraits_specLaw (T : OpTraits jasminDialect) (U : OpTraits modArithDialect) :
    SpecLaw (jasModTraits T U)
  | .inl (.inl _), _, _ => rfl
  | .inl (.inr _), _, _ => rfl
  | .inr o, h, args => modWordCastSpecLaw o h args

/-- A word cast emits no event in `jasMod`. -/
theorem jasModLeak_ctLeak_cast (M : LeakModel jasminDialect) (N : LeakModel modArithDialect)
    {Γ : Ctxt jasMod} {t : jasMod.Ty} (e : Expr jasMod Γ t) (o : ModWordCastOp)
    (h : e.op = .inr o) (V : Valuation Γ) : Expr.ctLeak (jasModLeak M N) e V = [] :=
  Expr.ctLeak_of_quiet _ e (by rw [h]; cases o <;> rfl) V

end CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
