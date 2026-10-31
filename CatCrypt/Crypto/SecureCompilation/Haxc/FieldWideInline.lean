/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
public import CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs

/-!
# Field templates for tagged field calls at a modulus of several words

A tagged field call `Hax.FieldTag.fieldHead m p` at a modulus `p ≥ 2^64` takes and returns
word arrays of `n = Hax.FieldTag.fieldLimbs p` limbs holding canonical representatives
(`Hax.FieldTag.limbsOf`). This module supplies the template blocks for such calls.

The canonical Montgomery template `canonMont` reads a Montgomery record `P : LimbParams n`
with canonical encodings on both sides: a field element `x` is carried by the limbs
`encL P (x · R⁻¹)`, the canonical limbs of `x`. Its block for an operation is the
Montgomery block `fieldComOf (montBlocks P).blocks` of the twisted field program
`twistOp n op`: addition, subtraction and negation are unchanged, a product `x · y` becomes
`(x · y) · R` and a constant `c` becomes `c · R⁻¹`. The radix `R = 2^(64n)` is a unit since
the modulus of a Montgomery record is odd.

`wideTemplateOf p` is the rule of wide templates by modulus, at `p ≥ 2^64`: the Solinas
template `WideTemplate.ofSolinasAt S` (through `solinasBlocks`) when `solinasParamsOf p`
recognises `p = 2 ^ k - c` with the record `S`, and otherwise, at every odd `p` with
`fieldLimbs p < 2^64`, the canonical Montgomery template of the record `montParams p` over
`fieldLimbs p` limbs with the constant `montNInv p = -p⁻¹ mod 2^64`. Each template has
`fieldLimbs p` limbs and the canonical limbs `limbsN` as its encoding.
`montWordOf p` is the same rule at `n = 1`: at every odd `1 < p < 2^64`, the record
`montParamsN 1 p`; it covers the moduli `2^31 < p < 2^64` such as Goldilocks.

`templateCall P op as o` is the block of a template for an operation over argument arrays
`as` and an output array `o`, renamed into the context of a call. `wideBlockOf W m` is the
body of a call of the method `m`: the template call of `fieldOpOf m p` on its parameters,
writing into the array of the first parameter. At one limb an operand is a `64`-bit
register: `canonRegBlock P op` is the limb lowering of the twisted program on registers,
and `montWordBlockOf P m` is the body of a call on the registers `wordSig m`.

## Main definitions

* `twistOp`, `canonL`, `CanonMont`, `canonMont` — the canonical Montgomery template.
* `montNInv`, `montParamsN`, `montParams` — the Montgomery record of an odd modulus over
  `n` limbs and over `fieldLimbs p` limbs.
* `montWordOf` — the one-limb Montgomery record of an odd modulus below `2^64`.
* `canonRegBlock`, `wordSig`, `wordNats`, `wordArgs`, `montWordBlockOf` — the register
  blocks and the call blocks over one limb.
* `solinasParamsOf` — the Solinas record of a modulus `2 ^ k - c`.
* `WideTemplate`, `solinasWideOf`, `montWideOf`, `wideTemplateOf` — the wide templates and
  their rule by modulus.
* `templateCall`, `fieldOpOf`, `wideSig`, `wideArgs`, `wideBlockOf` — the call blocks.
* `limbWords`, `wordsOf` — the source values of limbs and word arrays.

## Main results

* `canonL_fp` — the canonical Montgomery encoding is the canonical limbs.
* `solinasParamsOf_spec`, `solinasParamsOf_limbs` — a Solinas record of `p` has the modulus
  `p` and `fieldLimbs p` limbs.
* `wideTemplateOf_eq_solinas`, `wideTemplateOf_eq_mont`, `wideTemplateOf_cases` — the
  modulus `p ≥ 2^64` of a Solinas record has its Solinas template; every other odd modulus
  `p ≥ 2^64` with `fieldLimbs p < 2^64` has the canonical Montgomery template of
  `montParams p`; the rule returns no other template.
* `montWordOf_isSome`, `montWordOf_p` — every odd modulus `1 < p < 2^64` has a one-limb
  record, at that modulus.
* `canonRegBlock_denote` — the register block maps the canonical limbs of the arguments to
  the canonical limbs of the value.
* `montWordBlock_denoteAt` — on registers below `p`, the body of a method over one limb
  returns the word of `fieldVal m p a b`.
* `LimbParams.nInv_eq_montNInv` — the Montgomery constant of every record is `montNInv` of
  its modulus.
* `WideTemplate.enc_limbsOf` — the source values of the encoding of a template are
  `limbsOf n` of the canonical representative.
* `templateCall_denote` — the output array of a template call holds the encoding of the
  value of the operation.
* `wideBlock_denoteAt` — on argument arrays whose `limbsDec` is below `p`, the body of a
  method returns the limbs `limbsOf n (fieldVal m p a b)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend hvToHom pullV_hvToHom
  flatVal ctxFlat)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams R isUnit_R limbsN
  Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs (LimbBlockTemplate montBlocks
  solinasBlocks goodV_of_arithAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
open CatCrypt.Crypto.Hax.NFFieldSum (nfFieldDialect)
open Ctxt (Var Valuation)
open _root_.Hax.FieldTag (FieldMethod fieldLimbs limbsOf limbsDec fieldVal)

/-! ## 1. The canonical Montgomery template -/

/-- The radix `2^(64n)` at the modulus `q`. -/
def radix (n q : Nat) : ZMod q := 2 ^ (64 * n)

/-- Multiplication by the inverse of the radix at a prime-field type; the identity at the
    other field types. -/
def untwist (n : Nat) : {t : FieldTy} → ⟦t⟧ → ⟦t⟧
  | .fp q, x => (show ZMod q from x) * (radix n q)⁻¹
  | .fp2 _, x => x
  | .fp6 _, x => x
  | .fp12 _, x => x

/-- `untwist` at every entry of a valuation. -/
def untwistV (n : Nat) : {Γ : Ctxt fieldDialect} → Valuation Γ → Valuation Γ
  | [], .nil => .nil
  | _ :: _, .cons x V => .cons (untwist n x) (untwistV n V)

/-- **The twisted field program of an operation**: a product `x · y` is `(x · y) · R`, a
    constant `c` is `c · R⁻¹`, and every other operation is unchanged, where `R` is the
    radix `2^(64n)`. -/
def twistOp (n : Nat) : (op : fieldDialect.Op) →
    Com fieldDialect (DialectSignature.sig op) (DialectSignature.ret op)
  | .fMul q => .var ⟨.fMul q, rfl, FieldLower.allVars _⟩
      (.var ⟨.fConst q (radix n q), rfl, .nil⟩
        (.var ⟨.fMul q, rfl, .cons (.there .here) (.cons .here .nil)⟩ (.ret .here)))
  | .fConst q c => opCom (.fConst q (c * (radix n q)⁻¹))
  | .fAdd q => opCom (.fAdd q)
  | .fSub q => opCom (.fSub q)
  | .fNeg q => opCom (.fNeg q)
  | .fInv q => opCom (.fInv q)
  | .fCopy q => opCom (.fCopy q)
  | .fieldDouble q => opCom (.fieldDouble q)
  | .fieldSquare q => opCom (.fieldSquare q)

variable {n : Nat}

/-- **The canonical Montgomery encoding** of a record `P`: the Montgomery limbs `encL P` of
    `x · R⁻¹`. -/
def canonL (P : LimbParams n) : {t : FieldTy} → ⟦t⟧ → Valuation (mapTysL n t) :=
  fun {t} x => encL P (t := t) (untwist n x)

/-- The canonical Montgomery encoding of an element of `ZMod P.p` is its canonical limbs. -/
theorem canonL_fp (P : LimbParams n) (x : ZMod P.p) :
    canonL P (t := .fp P.p) x = limbsN n x.val := by
  change encL P (t := .fp P.p) (x * (R P)⁻¹) = _
  rw [encL_fp, Algebraic.FieldLimbs.Mont.enc, mul_assoc, ZMod.inv_mul_of_unit _ (isUnit_R P),
    mul_one]

theorem flatVal_canonL (P : LimbParams n) :
    ∀ {Γ : Ctxt fieldDialect} (V : Valuation Γ),
      flatVal (fun {t} x => canonL P (t := t) x) V
        = flatVal (fun {t} x => encL P (t := t) x) (untwistV n V)
  | [], .nil => rfl
  | _ :: _, .cons x V => by
      show hvAppend _ (flatVal _ V) = hvAppend _ (flatVal _ (untwistV n V))
      rw [flatVal_canonL P V]
      rfl

/-- The twisted program of an operation at `P.p` that `arithOpB` accepts is covered by the
    operations of the Montgomery blocks. -/
theorem twistOp_covered (P : LimbParams n) (op : fieldDialect.Op)
    (hg : arithOpB P.p op = true) : CoveredCom (GoodV P) (twistOp n op) := by
  cases op <;> simp only [arithOpB, beq_iff_eq, Bool.false_eq_true] at hg <;> subst hg
  · exact coveredCom_opCom (goodV_of_arithAt P) _ (by simp [arithOpB])
  · exact coveredCom_opCom (goodV_of_arithAt P) _ (by simp [arithOpB])
  · exact coveredCom_opCom (goodV_of_arithAt P) _ (by simp [arithOpB])
  · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)), Or.inr (Or.inl rfl),
      trivial⟩
  · exact coveredCom_opCom (goodV_of_arithAt P) _ (by simp [arithOpB])

/-- **The twisted program computes the untwisted value**: on the untwisted arguments, the
    twisted program of an operation at `P.p` that `arithOpB` accepts returns the untwisted
    value of the operation. -/
theorem twistOp_denote (P : LimbParams n) (op : fieldDialect.Op)
    (hg : arithOpB P.p op = true) (V : Valuation (DialectSignature.sig op)) :
    (twistOp n op).denote (untwistV n V) = untwist n (DialectDenote.denote op V) := by
  have hR : (radix n P.p)⁻¹ * radix n P.p = 1 := ZMod.inv_mul_of_unit _ (isUnit_R P)
  cases op <;> simp only [arithOpB, beq_iff_eq, Bool.false_eq_true] at hg <;> subst hg
  · rcases V with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    change (opCom (.fAdd P.p)).denote _ = _
    rw [opCom_denote]
    change (show ZMod P.p from a) * (radix n P.p)⁻¹ + (show ZMod P.p from b) * (radix n P.p)⁻¹
      = ((show ZMod P.p from a) + b) * (radix n P.p)⁻¹
    ring
  · rcases V with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    change (opCom (.fSub P.p)).denote _ = _
    rw [opCom_denote]
    change (show ZMod P.p from a) * (radix n P.p)⁻¹ - (show ZMod P.p from b) * (radix n P.p)⁻¹
      = ((show ZMod P.p from a) - b) * (radix n P.p)⁻¹
    ring
  · rcases V with _ | ⟨a, _ | _⟩
    change (opCom (.fNeg P.p)).denote _ = _
    rw [opCom_denote]
    change -((show ZMod P.p from a) * (radix n P.p)⁻¹)
      = -(show ZMod P.p from a) * (radix n P.p)⁻¹
    ring
  · rcases V with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    change (show ZMod P.p from a) * (radix n P.p)⁻¹
        * ((show ZMod P.p from b) * (radix n P.p)⁻¹) * radix n P.p
      = (show ZMod P.p from a) * b * (radix n P.p)⁻¹
    linear_combination ((show ZMod P.p from a) * b * (radix n P.p)⁻¹) * hR
  · rcases V with _ | _
    change (opCom (.fConst P.p _)).denote _ = _
    rw [opCom_denote]
    rfl

/-- A Montgomery record read with canonical encodings of its inputs and outputs. -/
structure CanonMont (n : Nat) where
  /-- The Montgomery record. -/
  mont : LimbParams n

/-- **The canonical Montgomery template** of a record `P`: the modulus `P.p`, the canonical
    limbs `canonL P`, the operations of `arithOpB P.p`, and the Montgomery block
    `fieldComOf (montBlocks P).blocks` of the twisted program `twistOp n op`. -/
instance canonMont : FieldLowerTemplate (CanonMont n) n where
  p C := C.mont.p
  enc C := fun {t} x => canonL C.mont (t := t) x
  accepts C := arithOpB C.mont.p
  block C op := fieldComOf (montBlocks C.mont).blocks (twistOp n op)
  block_denote C op hg hn V A o hA := by
    rw [fieldComOf_denote (lowerOpL C.mont) (fun {t} x => encL C.mont (t := t) x) (GoodV C.mont)
      (blockSquareV C.mont) hn (twistOp n op) (twistOp_covered C.mont op hg) (untwistV n V) A o
      (hA.trans (flatVal_canonL C.mont V)), twistOp_denote C.mont op hg V]
    rfl

/-! ## 2. The wide templates and their registry -/

/-- **A wide template at the modulus `p` over `n` limbs**: a field template `inst` at the
    value `P`, with `n < 2^64`, accepting every operation of `arithOpB p`, whose encoding of
    an element of `ZMod p` is its canonical limbs. -/
structure WideTemplate (p n : Nat) : Type 1 where
  /-- The carrier of the template. -/
  α : Type
  /-- The template. -/
  inst : FieldLowerTemplate α n
  /-- The value of the carrier. -/
  P : α
  n_lt : n < 2 ^ 64
  arith : ∀ op, arithOpB p op = true → @FieldLowerTemplate.accepts α n inst P op = true
  enc_canon : ∀ x : ZMod p, @FieldLowerTemplate.enc α n inst P (.fp p) x = limbsN n x.val

instance WideTemplate.instTemplate {p : Nat} (W : WideTemplate p n) :
    FieldLowerTemplate W.α n := W.inst

/-- The wide template of a Montgomery record through `canonMont`. -/
def WideTemplate.ofMont (P : LimbParams n) (hn : n < 2 ^ 64) : WideTemplate P.p n where
  α := CanonMont n
  inst := canonMont
  P := ⟨P⟩
  n_lt := hn
  arith _ h := h
  enc_canon x := canonL_fp P x

/-- The wide template of a block-level template whose encoding is the canonical limbs,
    through `limbTemplate`. -/
def WideTemplate.ofBlocks (T : LimbBlockTemplate n) (hn : n < 2 ^ 64)
    (hc : ∀ x : ZMod T.p, T.enc (t := .fp T.p) x = limbsN n x.val) : WideTemplate T.p n where
  α := LimbBlockTemplate n
  inst := limbTemplate
  P := T
  n_lt := hn
  arith _ h := h
  enc_canon := hc

/-- A wide template carried over to an equal number of limbs. -/
def WideTemplate.castN {p m : Nat} (h : n = m) (W : WideTemplate p n) : WideTemplate p m :=
  cast (congrArg (WideTemplate p) h) W

/-- A wide template over `fieldLimbs p` limbs carried over to an equal modulus. -/
def WideTemplate.castP {p q : Nat} (h : p = q) (W : WideTemplate p (fieldLimbs p)) :
    WideTemplate q (fieldLimbs q) :=
  cast (congrArg (fun r => WideTemplate r (fieldLimbs r)) h) W

/-- The wide template of a Montgomery record at its modulus over `fieldLimbs P.p` limbs. -/
def WideTemplate.ofMontAt (P : LimbParams n) (hn : n = fieldLimbs P.p) (h64 : n < 2 ^ 64) :
    WideTemplate P.p (fieldLimbs P.p) :=
  (WideTemplate.ofMont P h64).castN hn

/-- The wide template of a Solinas record at its modulus over `fieldLimbs` limbs. -/
def WideTemplate.ofSolinasAt (S : Algebraic.FieldLimbs.Solinas.SolinasParams n)
    (hn : n = fieldLimbs (Algebraic.FieldLimbs.Solinas.p S)) (h64 : n < 2 ^ 64) :
    WideTemplate (Algebraic.FieldLimbs.Solinas.p S)
      (fieldLimbs (Algebraic.FieldLimbs.Solinas.p S)) :=
  (WideTemplate.ofBlocks (solinasBlocks S) h64 fun x =>
    Algebraic.FieldToJasminLimbsSolinas.encL_fp S x).castN hn

/-- The Montgomery constant of a modulus `p`: `-p⁻¹ mod 2^64`. -/
def montNInv (p : Nat) : Nat := (-((p : ZMod (2 ^ 64))⁻¹)).val

theorem montNInv_lt (p : Nat) : montNInv p < 2 ^ 64 := ZMod.val_lt _

/-- For an odd `p`, `p · montNInv p + 1` is a multiple of `2^64`. -/
theorem montNInv_spec {p : Nat} (hp : p % 2 = 1) : (p * montNInv p + 1) % 2 ^ 64 = 0 := by
  have hcop : Nat.Coprime p (2 ^ 64) :=
    (Nat.Coprime.pow_left 64 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hp))).symm
  have hu := ZMod.coe_mul_inv_eq_one p hcop
  refine Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp ?_)
  push_cast
  rw [montNInv, ZMod.natCast_zmod_val, mul_neg, hu, neg_add_cancel]

/-- **The Montgomery constant of a record is `montNInv` of its modulus**: `-p⁻¹ mod 2^64` is
    the only number below `2^64` with `p · nInv + 1 ≡ 0 (mod 2^64)`. -/
theorem LimbParams.nInv_eq_montNInv (P : LimbParams n) : P.nInv = montNInv P.p := by
  have hcop : Nat.Coprime P.p (2 ^ 64) :=
    (Nat.Coprime.pow_left 64 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr P.p_odd))).symm
  have hu := ZMod.coe_mul_inv_eq_one P.p hcop
  have hs : ((P.p * P.nInv + 1 : Nat) : ZMod (2 ^ 64)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero P.nInv_spec)
  push_cast at hs
  have hb : (P.nInv : ZMod (2 ^ 64)) = -((P.p : ZMod (2 ^ 64))⁻¹) := by
    linear_combination ((P.p : ZMod (2 ^ 64)))⁻¹ * hs - (P.nInv : ZMod (2 ^ 64)) * hu
  rw [montNInv, ← hb, ZMod.val_natCast, Nat.mod_eq_of_lt P.nInv_lt]

/-- An odd modulus above `1` is below `2^(64 · fieldLimbs p)`. -/
theorem lt_pow_fieldLimbs {p : Nat} (h1 : 1 < p) (hp : p % 2 = 1) :
    p < 2 ^ (64 * fieldLimbs p) := by
  rcases (_root_.Hax.FieldTag.le_pow_fieldLimbs p).lt_or_eq with h | h
  · exact h
  · exfalso
    rcases hk : fieldLimbs p with _ | k
    · rw [hk] at h
      simp at h
      omega
    · rw [hk, Nat.mul_succ, Nat.pow_add] at h
      rw [h, Nat.mul_mod, show 2 ^ 64 % 2 = 0 by norm_num] at hp
      simp at hp

/-- **The Montgomery record of an odd modulus** `p > 1` over `n` limbs with `p < 2^(64n)`,
    with the constant `montNInv p`. -/
def montParamsN (n p : Nat) (h1 : 1 < p) (hp : p % 2 = 1) (hlt : p < 2 ^ (64 * n)) :
    LimbParams n where
  p := p
  nInv := montNInv p
  one_lt := h1
  p_odd := hp
  p_lt := hlt
  nInv_lt := montNInv_lt p
  nInv_spec := montNInv_spec hp

/-- **The Montgomery record of an odd modulus** `p > 1` over `fieldLimbs p` limbs: the record
    `montParamsN` at `n = fieldLimbs p`. -/
def montParams (p : Nat) (h1 : 1 < p) (hp : p % 2 = 1) : LimbParams (fieldLimbs p) :=
  montParamsN (fieldLimbs p) p h1 hp (lt_pow_fieldLimbs h1 hp)

/-- **The one-limb Montgomery record of the rule**: at an odd modulus `1 < p < 2^64`, the
    record `montParamsN 1 p`; `none` otherwise. -/
def montWordOf (p : Nat) : Option (LimbParams 1) :=
  if h : 1 < p ∧ p % 2 = 1 ∧ p < 2 ^ 64 then
    some (montParamsN 1 p h.1 h.2.1 (by simpa using h.2.2))
  else none

/-- The record of the one-limb rule has the modulus it is chosen at. -/
theorem montWordOf_p {p : Nat} {P : LimbParams 1} (h : montWordOf p = some P) : P.p = p := by
  unfold montWordOf at h
  split at h
  · cases h
    rfl
  · cases h

/-- **Every odd modulus `1 < p < 2^64` has a one-limb Montgomery record**, among them the
    moduli `2^31 < p < 2^64` that no narrow template covers, such as Goldilocks
    `2^64 - 2^32 + 1`. -/
theorem montWordOf_isSome {p : Nat} (h1 : 1 < p) (hp : p % 2 = 1) (h64 : p < 2 ^ 64) :
    (montWordOf p).isSome = true := by
  rw [montWordOf, dite_eq_left ⟨h1, hp, h64⟩]
  rfl

/-- **The Montgomery arm of the rule**: at an odd modulus `p ≥ 2^64` with
    `fieldLimbs p < 2^64`, the canonical Montgomery template of `montParams p`; `none`
    otherwise. -/
def montWideOf (p : Nat) : Option (WideTemplate p (fieldLimbs p)) :=
  if h : 2 ^ 64 ≤ p ∧ p % 2 = 1 ∧ fieldLimbs p < 2 ^ 64 then
    some (WideTemplate.ofMont (montParams p (Nat.lt_of_lt_of_le (by norm_num) h.1) h.2.1)
      h.2.2)
  else none

/-! ## 2b. The Solinas record of a modulus and the rule of wide templates -/

/-- **The number of words of `q` is `m`** when `q < 2^(64 m)`, `q ≥ 2^(64 (m - 1))` for
    `m ≥ 1`, and the fuel is at least `q`. -/
theorem wordsAux_eq : ∀ (fuel q m : Nat), q ≤ fuel → q < 2 ^ (64 * m) →
    (m = 0 ∨ 2 ^ (64 * (m - 1)) ≤ q) → _root_.Hax.FieldTag.wordsAux fuel q = m
  | 0, q, m, hf, _, hm => by
      have hq : q = 0 := by omega
      subst hq
      rcases hm with hm | hm
      · simp [hm, _root_.Hax.FieldTag.wordsAux]
      · exact absurd hm (Nat.not_le.mpr (Nat.two_pow_pos _))
  | fuel + 1, q, m, hf, hlt, hm => by
      simp only [_root_.Hax.FieldTag.wordsAux]
      split
      · rename_i hq
        subst hq
        rcases hm with hm | hm
        · exact hm.symm
        · exact absurd hm (Nat.not_le.mpr (Nat.two_pow_pos _))
      · rename_i hq
        rcases m with _ | m
        · simp at hlt
          omega
        · have hd : q / 2 ^ 64 < q := Nat.div_lt_self (by omega) (by decide)
          have hlt' : q / 2 ^ 64 < 2 ^ (64 * m) := by
            rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), ← Nat.pow_add]
            simpa [Nat.mul_succ] using hlt
          have hm' : m = 0 ∨ 2 ^ (64 * (m - 1)) ≤ q / 2 ^ 64 := by
            rcases m with _ | m
            · exact Or.inl rfl
            · refine Or.inr ((Nat.le_div_iff_mul_le (Nat.two_pow_pos 64)).mpr ?_)
              rcases hm with hm | hm
              · omega
              · rw [← Nat.pow_add]
                simpa [Nat.mul_succ] using hm
          rw [wordsAux_eq fuel (q / 2 ^ 64) m (by omega) hlt' hm']

/-- **The number of limbs of `p` is `m`** when `2^(64 (m - 1)) < p ≤ 2^(64 m)`. -/
theorem fieldLimbs_eq {p m : Nat} (hlo : 2 ^ (64 * (m - 1)) < p)
    (hhi : p ≤ 2 ^ (64 * m)) : fieldLimbs p = m := by
  have := Nat.two_pow_pos (64 * (m - 1))
  exact wordsAux_eq p (p - 1) m (by omega) (by omega) (Or.inr (by omega))

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams) in
/-- **The Solinas record of the modulus `p`**: with `k` the bit length of `p`,
    `c = 2 ^ k - p` and `n = ⌈k / 64⌉`, the record of `p = 2 ^ k - c` over `n` limbs when
    `c` is odd and below `2 ^ 64`, `64 ≤ k`, `c (c + 3) < 2 ^ k` and `n < 2 ^ 64`; `none`
    otherwise. -/
def solinasParamsOf (p : Nat) : Option (Σ n, SolinasParams n) :=
  let k := Nat.log2 p + 1
  let c := 2 ^ k - p
  let n := (k + 63) / 64
  if h : c % 2 = 1 ∧ c < 2 ^ 64 ∧ 64 ≤ k ∧ k ≤ 64 * n ∧ c * (c + 3) < 2 ^ k ∧
      p + c = 2 ^ k ∧ n < 2 ^ 64 then
    some ⟨n, ⟨k, c, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩⟩
  else none

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams) in
/-- **The recogniser of `2 ^ k - c` is sound**: a record it returns has the modulus `p`. -/
theorem solinasParamsOf_spec {p n : Nat} {S : SolinasParams n}
    (h : solinasParamsOf p = some ⟨n, S⟩) :
    Algebraic.FieldLimbs.Solinas.p S = p ∧ n < 2 ^ 64 := by
  unfold solinasParamsOf at h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    have := hc.2.2.2.2.2.1
    refine ⟨?_, hc.2.2.2.2.2.2⟩
    simp only [Algebraic.FieldLimbs.Solinas.p]
    omega
  · cases h

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams) in
/-- **A record of the recogniser has `fieldLimbs p` limbs.** -/
theorem solinasParamsOf_limbs {p n : Nat} {S : SolinasParams n}
    (h : solinasParamsOf p = some ⟨n, S⟩) : n = fieldLimbs p := by
  unfold solinasParamsOf at h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨hodd, -, hk, hkn, hcc, hpc, -⟩ := hc
    generalize Nat.log2 p + 1 = k at hodd hk hkn hcc hpc ⊢
    generalize 2 ^ k - p = c at hodd hcc hpc
    have h2c : 2 * c < 2 ^ k := by nlinarith
    have hk1 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    have hlo : 2 ^ (64 * ((k + 63) / 64 - 1)) ≤ 2 ^ (k - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hhi : 2 ^ k ≤ 2 ^ (64 * ((k + 63) / 64)) := Nat.pow_le_pow_right (by norm_num) hkn
    exact (fieldLimbs_eq (by omega) (by omega)).symm
  · cases h

/-- **The Solinas arm of the rule**: at a modulus `p ≥ 2^64` that `solinasParamsOf`
    recognises as `2 ^ k - c` with the record `S`, the wide template
    `WideTemplate.ofSolinasAt S` carried to `p`; `none` otherwise. -/
def solinasWideOf (p : Nat) : Option (WideTemplate p (fieldLimbs p)) :=
  match hs : solinasParamsOf p with
  | some ⟨_, S⟩ =>
      if 2 ^ 64 ≤ p then
        some ((WideTemplate.ofSolinasAt S
          ((solinasParamsOf_limbs hs).trans (congrArg fieldLimbs (solinasParamsOf_spec hs).1).symm)
          (solinasParamsOf_spec hs).2).castP (solinasParamsOf_spec hs).1)
      else none
  | none => none

/-- **The wide templates by modulus**: the first arm that returns a template, in the order
    Solinas (`solinasWideOf`), Montgomery (`montWideOf`). -/
def wideTemplateOf (p : Nat) : Option (WideTemplate p (fieldLimbs p)) :=
  solinasWideOf p <|> montWideOf p

theorem solinasWideOf_of_none {p : Nat} (hs : solinasParamsOf p = none) :
    solinasWideOf p = none := by
  unfold solinasWideOf
  split
  · rename_i hs'
    rw [hs] at hs'
    cases hs'
  · rfl

/-- **No wide template below `2^64`.** -/
theorem wideTemplateOf_of_lt {p : Nat} (h : p < 2 ^ 64) : wideTemplateOf p = none := by
  have hs : solinasWideOf p = none := by
    unfold solinasWideOf
    split
    · rw [ite_eq_right (by omega)]
    · rfl
  rw [wideTemplateOf, hs, montWideOf, dite_eq_right (by omega)]
  rfl

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams) in
/-- **The Solinas case of the rule**: at a modulus `p ≥ 2^64` with the record `S` of
    `solinasParamsOf p`, the rule returns the wide template `WideTemplate.ofSolinasAt S`
    carried to `p`. -/
theorem wideTemplateOf_eq_solinas {p n : Nat} {S : SolinasParams n}
    (h : solinasParamsOf p = some ⟨n, S⟩) (h64 : 2 ^ 64 ≤ p) :
    wideTemplateOf p = some ((WideTemplate.ofSolinasAt S
      ((solinasParamsOf_limbs h).trans (congrArg fieldLimbs (solinasParamsOf_spec h).1).symm)
      (solinasParamsOf_spec h).2).castP (solinasParamsOf_spec h).1) := by
  have hs : solinasWideOf p = some ((WideTemplate.ofSolinasAt S
      ((solinasParamsOf_limbs h).trans (congrArg fieldLimbs (solinasParamsOf_spec h).1).symm)
      (solinasParamsOf_spec h).2).castP (solinasParamsOf_spec h).1) := by
    unfold solinasWideOf
    split
    · rename_i hs
      rw [h] at hs
      cases hs
      rw [ite_eq_left h64]
    · rename_i hs
      rw [h] at hs
      cases hs
  rw [wideTemplateOf, hs]
  rfl

/-- **The Montgomery case of the rule**: at an odd `p ≥ 2^64` with `fieldLimbs p < 2^64`
    that `solinasParamsOf` does not recognise, the rule returns the canonical Montgomery
    template of `montParams p`. -/
theorem wideTemplateOf_eq_mont {p : Nat} (h64 : 2 ^ 64 ≤ p) (hp : p % 2 = 1)
    (hn : fieldLimbs p < 2 ^ 64) (hs : solinasParamsOf p = none) :
    wideTemplateOf p = some (WideTemplate.ofMont
      (montParams p (Nat.lt_of_lt_of_le (by norm_num) h64) hp) hn) := by
  rw [wideTemplateOf, solinasWideOf_of_none hs, montWideOf, dite_eq_left ⟨h64, hp, hn⟩]
  rfl

/-- **Every odd modulus of several words has a wide template**: at an odd `p ≥ 2^64` with
    `fieldLimbs p < 2^64`, the rule returns a template. -/
theorem wideTemplateOf_isSome {p : Nat} (h64 : 2 ^ 64 ≤ p) (hp : p % 2 = 1)
    (hn : fieldLimbs p < 2 ^ 64) : ∃ W, wideTemplateOf p = some W := by
  rw [wideTemplateOf]
  cases solinasWideOf p with
  | some W => exact ⟨W, rfl⟩
  | none =>
      rw [montWideOf, dite_eq_left ⟨h64, hp, hn⟩]
      exact ⟨_, rfl⟩

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams) in
/-- **The templates of the rule**: a template of `wideTemplateOf p` is the Solinas template
    `WideTemplate.ofSolinasAt S` of a record `S` with modulus `p`, carried to `p`, or the
    canonical Montgomery template of `montParams p`. -/
theorem wideTemplateOf_cases {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    (h : wideTemplateOf p = some W) :
    (∃ (n : Nat) (S : SolinasParams n)
        (hn : n = fieldLimbs (Algebraic.FieldLimbs.Solinas.p S)) (h64 : n < 2 ^ 64)
        (hp : Algebraic.FieldLimbs.Solinas.p S = p),
        W = (WideTemplate.ofSolinasAt S hn h64).castP hp) ∨
      ∃ (h1 : 1 < p) (hp : p % 2 = 1) (hn : fieldLimbs p < 2 ^ 64),
        W = WideTemplate.ofMont (montParams p h1 hp) hn := by
  unfold wideTemplateOf at h
  cases hs : solinasWideOf p with
  | some W' =>
      rw [hs] at h
      cases h
      left
      unfold solinasWideOf at hs
      split at hs
      · split at hs
        · cases hs
          exact ⟨_, _, _, _, _, rfl⟩
        · cases hs
      · cases hs
  | none =>
      rw [hs] at h
      change montWideOf p = some W at h
      right
      unfold montWideOf at h
      split at h
      · rename_i hc
        cases h
        exact ⟨_, hc.2.1, hc.2.2, rfl⟩
      · cases h

/-- **The record of the rule at the modulus of a Montgomery record** has the modulus and the
    Montgomery constant of that record. -/
theorem montParams_eq (P : LimbParams n) (h1 : 1 < P.p) :
    (montParams P.p h1 P.p_odd).p = P.p ∧
      (montParams P.p h1 P.p_odd).nInv = P.nInv :=
  ⟨rfl, (LimbParams.nInv_eq_montNInv P).symm⟩

/-! ## 2a. The register blocks of the canonical Montgomery template -/

/-- **The register block of an operation in the canonical Montgomery template** of a record
    `P`: the limb lowering with the blocks `lowerOpL P` of the twisted program `twistOp n op`,
    from the limbs of the arguments to the limbs of the value. -/
def canonRegBlock (P : LimbParams n) (op : fieldDialect.Op) :
    MultiReturnCom jasminDialect (ctxFlat (mapTysL n) (DialectSignature.sig op)) (Rn n) :=
  (loweringOf (lowerOpL P)).lowerMulti (twistOp n op)

/-- **The register block returns the canonical limbs of the value**: for an operation that
    `arithOpB P.p` accepts, on the canonical limbs of the arguments, the register block
    returns the canonical limbs of the value of the operation. -/
theorem canonRegBlock_denote (P : LimbParams n) (op : fieldDialect.Op)
    (hg : arithOpB P.p op = true) (V : Valuation (DialectSignature.sig op)) :
    (canonRegBlock P op).denote (flatVal (fun {t} x => canonL P (t := t) x) V)
      = canonL P (DialectDenote.denote op V) := by
  rw [flatVal_canonL, canonRegBlock,
    (loweringOf (lowerOpL P)).multiFundamental_on (fun {t} x => encL P (t := t) x) (GoodV P)
      (blockSquareV P) _ (twistOp_covered P op hg), twistOp_denote P op hg]
  rfl

/-! ## 3. The template call -/

section Call

variable {α : Type} [FieldLowerTemplate α n]

/-- **The template call** of an operation: the block `FieldLowerTemplate.block P op` over
    the argument arrays `as` and the output array `o` of the calling context. -/
def templateCall {Θ : Ctxt jasminDialect} (P : α) (op : fieldDialect.Op)
    (as : HVector (fun t => Var Θ t) (arrCtx n (DialectSignature.sig op)))
    (o : Var Θ (arrTy n)) : Com jasminDialect Θ (arrTy n) :=
  Com.rename (hvToHom (hvAppend as (.cons o .nil))) (FieldLowerTemplate.block P op)

/-- **The output array of a template call holds the encoding of the value**: for an
    accepted operation and argument arrays whose limbs are the encodings of the values of
    `V`. -/
theorem templateCall_denote (P : α) (hn : n < 2 ^ 64) {Θ : Ctxt jasminDialect}
    (op : fieldDialect.Op) (hg : FieldLowerTemplate.accepts P op = true)
    (as : HVector (fun t => Var Θ t) (arrCtx n (DialectSignature.sig op)))
    (o : Var Θ (arrTy n)) (W : Valuation Θ) (V : Valuation (DialectSignature.sig op))
    (hA : arrFlat (n := n) (MultiReturnCom.lookupVars as W)
      = flatVal (fun {t} x => FieldLowerTemplate.enc P (t := t) x) V) :
    arrLimbs ((templateCall P op as o).denote W) n 0
      = FieldLowerTemplate.enc P (DialectDenote.denote op V) := by
  rw [templateCall, FieldDialectBlockDescent.Com.denote_rename, pullV_hvToHom,
    lookupVars_hvAppend,
    show MultiReturnCom.lookupVars (HVector.cons o HVector.nil) W =
      HVector.cons (o.lookup W) .nil from rfl,
    FieldLowerTemplate.block_denote P op hg hn V _ _ hA]

/-- The right arm of `lowerF` is the template call on the arrays of the arguments, writing
    into the array of the first argument. -/
theorem fieldArm_eq_templateCall (P : α) {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (ρ : JRen n Δ Θ) {us : List JasminTy} (op : fieldDialect.Op)
    (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inr))
    (k : BindK n Θ (.inr (DialectSignature.ret op)) us) :
    fieldArm P ρ op args k =
      if FieldLowerTemplate.accepts P op then
        (fldArrs ρ args).bind fun as =>
          (headArr as).bind fun o =>
            NFProg.spliceNF? (templateCall P op as o) (fun {_} h res => k h (.var res))
      else none := rfl

end Call

/-- The operation of `fieldDialect` of a method at the modulus `p`: squaring is the product
    and doubling the sum of the argument with itself. -/
def fieldOpOf : FieldMethod → Nat → fieldDialect.Op
  | .add, p => .fAdd p
  | .sub, p => .fSub p
  | .mul, p => .fMul p
  | .neg, p => .fNeg p
  | .square, p => .fMul p
  | .double, p => .fAdd p

theorem arithOpB_fieldOpOf (m : FieldMethod) (p : Nat) : arithOpB p (fieldOpOf m p) = true := by
  cases m <;> simp [fieldOpOf, arithOpB]

variable (n) in
/-- The signature in `jasminDialect` of a method at a modulus of `n` limbs: two word arrays
    for a method with two arguments, one for a method with one. -/
def wideSig : FieldMethod → List JasminTy
  | .add | .sub | .mul => [arrTy n, arrTy n]
  | .neg | .square | .double => [arrTy n]

/-- The argument arrays of the operation of a method among its parameters: the two
    parameters of a method with two arguments, the one parameter twice for squaring and
    doubling, and once for negation. -/
def wideArgs (p : Nat) : (m : FieldMethod) →
    HVector (fun t => Var (wideSig n m) t) (arrCtx n (DialectSignature.sig (fieldOpOf m p)))
  | .add => .cons .here (.cons (.there .here) .nil)
  | .sub => .cons .here (.cons (.there .here) .nil)
  | .mul => .cons .here (.cons (.there .here) .nil)
  | .neg => .cons .here .nil
  | .square => .cons .here (.cons .here .nil)
  | .double => .cons .here (.cons .here .nil)

/-- The first parameter of a method. -/
def wideFirst : (m : FieldMethod) → Var (d := jasminDialect) (wideSig n m) (arrTy n)
  | .add | .sub | .mul | .neg | .square | .double => .here

/-- **The body of a call of a method** at a wide template: the template call of
    `fieldOpOf m p` on the parameters, writing into the array of the first parameter. -/
def wideBlockOf {p : Nat} (W : WideTemplate p n) (m : FieldMethod) :
    NFProg jasminDialect (wideSig n m) [arrTy n] :=
  NFProg.ofCom (templateCall W.P (fieldOpOf m p) (wideArgs p m) (wideFirst m))

/-! ## 3a. The call blocks over one limb -/

/-- The signature in `jasminDialect` of a method at a modulus below `2^64`: two `64`-bit
    registers for a method with two arguments, one for a method with one. -/
def wordSig : FieldMethod → List JasminTy
  | .add | .sub | .mul => [.reg 64, .reg 64]
  | .neg | .square | .double => [.reg 64]

/-- The numbers a valuation at the signature `wordSig` of a method holds: its first and its
    second argument, and `0` as the second number of a method with one argument. -/
def wordNats : (m : FieldMethod) → Valuation (d := jasminDialect) (wordSig m) → Nat × Nat
  | .add, .cons a (.cons b .nil) | .sub, .cons a (.cons b .nil)
  | .mul, .cons a (.cons b .nil) => (a.toNat, b.toNat)
  | .neg, .cons a .nil | .square, .cons a .nil | .double, .cons a .nil => (a.toNat, 0)

/-- The argument registers of the operation of a method among its parameters: the two
    parameters of a method with two arguments, the one parameter twice for squaring and
    doubling, and once for negation. -/
def wordArgs (p : Nat) : (m : FieldMethod) →
    HVector (fun t => Var (d := jasminDialect) (wordSig m) t)
      (ctxFlat (mapTysL 1) (DialectSignature.sig (fieldOpOf m p)))
  | .add => .cons .here (.cons (.there .here) .nil)
  | .sub => .cons .here (.cons (.there .here) .nil)
  | .mul => .cons .here (.cons (.there .here) .nil)
  | .neg => .cons .here .nil
  | .square => .cons .here (.cons .here .nil)
  | .double => .cons .here (.cons .here .nil)

/-- **The body of a call of a method over one limb**: the register block `canonRegBlock P`
    of the canonical Montgomery template of a one-limb record `P` for the operation
    `fieldOpOf m P.p`, on the parameters. -/
def montWordBlockOf (P : LimbParams 1) (m : FieldMethod) :
    NFProg jasminDialect (wordSig m) [.reg 64] :=
  NFProg.ofCom (Com.rename (hvToHom (wordArgs P.p m))
    (canonRegBlock P (fieldOpOf m P.p)).toComHead)

/-- The canonical limbs of a word below the modulus of a one-limb record are the word. -/
theorem canonL_word (P : LimbParams 1) (w : BitVec 64) (hw : w.toNat < P.p) :
    canonL P (t := .fp P.p) ((w.toNat : Nat) : ZMod P.p) = .cons w .nil := by
  have : NeZero P.p := NeZero.of_pos (by omega)
  rw [canonL_fp, ZMod.val_natCast, Nat.mod_eq_of_lt hw]
  simp [limbsN]

/-- **The body of a method over one limb returns the word of its value.** For a one-limb
    record `P`, on arguments below `P.p`, the body of the method `m` returns, at every call
    environment and fuel, the word of `fieldVal m P.p` of the arguments. -/
theorem montWordBlock_denoteAt (P : LimbParams 1) {m : FieldMethod}
    (x : Valuation (d := jasminDialect) (wordSig m))
    (ha : (wordNats m x).1 < P.p) (hb : m.binary = true → (wordNats m x).2 < P.p)
    (E : CallEnv jasminDialect) (fuel : Nat) :
    (montWordBlockOf P m).denoteAt E fuel x =
      some (.cons (BitVec.ofNat 64 (fieldVal m P.p (wordNats m x).1 (wordNats m x).2)) .nil) := by
  have : NeZero P.p := ⟨by have := P.one_lt; omega⟩
  unfold NFProg.denoteAt
  let _ : CallDenote jasminDialect := ⟨E⟩
  refine (NFProg.denote_ofCom (d := jasminDialect) _ fuel _).trans ?_
  rw [FieldDialectBlockDescent.Com.denote_rename, pullV_hvToHom,
    MultiReturnCom.toComHead_denote]
  have key : ∀ V : Valuation (DialectSignature.sig (fieldOpOf m P.p)),
      MultiReturnCom.lookupVars (wordArgs P.p m) x
        = flatVal (fun {t} z => canonL P (t := t) z) V →
      some (HVector.cons ((canonRegBlock P (fieldOpOf m P.p)).denote
        (MultiReturnCom.lookupVars (wordArgs P.p m) x)).head HVector.nil)
        = some (HVector.cons
          (canonL P (DialectDenote.denote (fieldOpOf m P.p) V)).head HVector.nil) :=
    fun V hV => by rw [hV, canonRegBlock_denote P _ (arithOpB_fieldOpOf m P.p) V]
  cases m with
  | add =>
    rcases x with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
    have hu : u.toNat < P.p := ha
    have hv : v.toNat < P.p := hb rfl
    refine (key (.cons ((u.toNat : Nat) : ZMod P.p) (.cons ((v.toNat : Nat) : ZMod P.p) .nil))
      (by
        change HVector.cons u (HVector.cons v .nil) = hvAppend (canonL P (t := .fp P.p) _)
          (hvAppend (canonL P (t := .fp P.p) _) .nil)
        rw [canonL_word P u hu, canonL_word P v hv]
        rfl)).trans ?_
    change some (HVector.cons (canonL P (t := .fp P.p)
      (((u.toNat : Nat) : ZMod P.p) + ((v.toNat : Nat) : ZMod P.p))).head .nil) = _
    rw [canonL_fp, ZMod.val_add, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hu,
      Nat.mod_eq_of_lt hv]
    rfl
  | sub =>
    rcases x with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
    have hu : u.toNat < P.p := ha
    have hv : v.toNat < P.p := hb rfl
    refine (key (.cons ((u.toNat : Nat) : ZMod P.p) (.cons ((v.toNat : Nat) : ZMod P.p) .nil))
      (by
        change HVector.cons u (HVector.cons v .nil) = hvAppend (canonL P (t := .fp P.p) _)
          (hvAppend (canonL P (t := .fp P.p) _) .nil)
        rw [canonL_word P u hu, canonL_word P v hv]
        rfl)).trans ?_
    change some (HVector.cons (canonL P (t := .fp P.p)
      (((u.toNat : Nat) : ZMod P.p) - ((v.toNat : Nat) : ZMod P.p))).head .nil) = _
    rw [canonL_fp, show ((u.toNat : Nat) : ZMod P.p) - ((v.toNat : Nat) : ZMod P.p)
      = ((u.toNat + P.p - v.toNat : Nat) : ZMod P.p) by
        rw [Nat.cast_sub (by omega)]; push_cast; simp, ZMod.val_natCast]
    rfl
  | mul =>
    rcases x with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
    have hu : u.toNat < P.p := ha
    have hv : v.toNat < P.p := hb rfl
    refine (key (.cons ((u.toNat : Nat) : ZMod P.p) (.cons ((v.toNat : Nat) : ZMod P.p) .nil))
      (by
        change HVector.cons u (HVector.cons v .nil) = hvAppend (canonL P (t := .fp P.p) _)
          (hvAppend (canonL P (t := .fp P.p) _) .nil)
        rw [canonL_word P u hu, canonL_word P v hv]
        rfl)).trans ?_
    change some (HVector.cons (canonL P (t := .fp P.p)
      (((u.toNat : Nat) : ZMod P.p) * ((v.toNat : Nat) : ZMod P.p))).head .nil) = _
    rw [canonL_fp, ZMod.val_mul, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hu,
      Nat.mod_eq_of_lt hv]
    rfl
  | neg =>
    rcases x with _ | ⟨u, _ | _⟩
    have hu : u.toNat < P.p := ha
    refine (key (.cons ((u.toNat : Nat) : ZMod P.p) .nil)
      (by
        change HVector.cons u .nil = hvAppend (canonL P (t := .fp P.p) _) .nil
        rw [canonL_word P u hu]
        rfl)).trans ?_
    change some (HVector.cons (canonL P (t := .fp P.p)
      (-((u.toNat : Nat) : ZMod P.p))).head .nil) = _
    rw [canonL_fp, show -((u.toNat : Nat) : ZMod P.p) = ((P.p - u.toNat : Nat) : ZMod P.p) by
      rw [Nat.cast_sub (by omega)]; simp, ZMod.val_natCast]
    rfl
  | square =>
    rcases x with _ | ⟨u, _ | _⟩
    have hu : u.toNat < P.p := ha
    refine (key (.cons ((u.toNat : Nat) : ZMod P.p) (.cons ((u.toNat : Nat) : ZMod P.p) .nil))
      (by
        change HVector.cons u (HVector.cons u .nil) = hvAppend (canonL P (t := .fp P.p) _)
          (hvAppend (canonL P (t := .fp P.p) _) .nil)
        rw [canonL_word P u hu]
        rfl)).trans ?_
    change some (HVector.cons (canonL P (t := .fp P.p)
      (((u.toNat : Nat) : ZMod P.p) * ((u.toNat : Nat) : ZMod P.p))).head .nil) = _
    rw [canonL_fp, ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hu]
    rfl
  | double =>
    rcases x with _ | ⟨u, _ | _⟩
    have hu : u.toNat < P.p := ha
    refine (key (.cons ((u.toNat : Nat) : ZMod P.p) (.cons ((u.toNat : Nat) : ZMod P.p) .nil))
      (by
        change HVector.cons u (HVector.cons u .nil) = hvAppend (canonL P (t := .fp P.p) _)
          (hvAppend (canonL P (t := .fp P.p) _) .nil)
        rw [canonL_word P u hu]
        rfl)).trans ?_
    change some (HVector.cons (canonL P (t := .fp P.p)
      (((u.toNat : Nat) : ZMod P.p) + ((u.toNat : Nat) : ZMod P.p))).head .nil) = _
    rw [canonL_fp, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hu]
    simp only [fieldVal, wordNats, two_mul]
    rfl

/-! ## 4. Source values of limbs and the denotation of the body -/

/-- The source values of a tuple of limbs: the integer of each limb, in order. -/
def limbWords : {m : Nat} → ListDenote (Rn m) → List _root_.Hax.Value
  | 0, _ => []
  | _ + 1, .cons x L => .int (BitVec.toNat (w := 64) x) :: limbWords L

/-- The source values of a word array of `n` limbs. -/
def wordsOf (a : Fin n → BitVec 64) : List _root_.Hax.Value := limbWords (arrLimbs a n 0)

/-- The source values of the limbs of `v` are `limbsOf m v`. -/
theorem limbWords_limbsN : ∀ (m v : Nat), limbWords (limbsN m v) = limbsOf m v
  | 0, _ => rfl
  | m + 1, v => by
      show .int (BitVec.ofNat 64 v).toNat :: limbWords (limbsN m (v / 2 ^ 64)) = _
      rw [limbWords_limbsN m, BitVec.toNat_ofNat]
      rfl

/-- Limbs whose source values `limbsDec` reads as `v` are the limbs of `v`. -/
theorem eq_limbsN_of_limbsDec {m : Nat} (L : ListDenote (Rn m)) {v : Nat}
    (h : limbsDec (limbWords L) = some v) : L = limbsN m v := by
  induction m generalizing v with
  | zero =>
    rcases L with _ | _
    rfl
  | succ m ih =>
    rcases L with _ | ⟨x, L⟩
    have hx := x.isLt
    change (if (0 : Int) ≤ (x.toNat : Int) ∧ (x.toNat : Int) < 2 ^ 64 then
      (limbsDec (limbWords L)).map fun r => (x.toNat : Int).toNat + 2 ^ 64 * r else none)
        = some v at h
    rw [ite_eq_left ⟨by omega, by omega⟩] at h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ih L hr]
    have h1 : x = BitVec.ofNat 64 ((x.toNat : Int).toNat + 2 ^ 64 * r) := by
      apply BitVec.eq_of_toNat_eq
      simp only [Int.toNat_natCast, BitVec.toNat_ofNat]
      omega
    have h2 : limbsN m r = limbsN m (((x.toNat : Int).toNat + 2 ^ 64 * r) / 2 ^ 64) := by
      congr 1
      simp only [Int.toNat_natCast]
      omega
    exact (congrArg₂ HVector.cons h1 h2).trans rfl

/-- The source values of the words of an array are its words from index `j` as
    integers. -/
theorem limbWords_arrLimbs (a : Fin n → BitVec 64) :
    ∀ (m j : Nat), limbWords (arrLimbs a m j)
      = (List.range m).map fun i => .int (stackGet a (j + i)).toNat
  | 0, _ => rfl
  | m + 1, j => by
      show .int (stackGet a j).toNat :: limbWords (arrLimbs a m (j + 1)) = _
      rw [limbWords_arrLimbs a m (j + 1), List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.add_zero]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, Nat.add_assoc, Nat.add_comm 1 i]

section Wide

variable {p : Nat} (W : WideTemplate p n)

theorem WideTemplate.enc_eq (x : ZMod p) :
    FieldLowerTemplate.enc W.P (t := .fp p) x = limbsN n x.val :=
  W.enc_canon x

/-- **The source values of the encoding of a wide template** are `limbsOf n` of the
    canonical representative. -/
theorem WideTemplate.enc_limbsOf (x : ZMod p) :
    limbWords (FieldLowerTemplate.enc W.P (t := .fp p) x) = limbsOf n x.val := by
  rw [W.enc_eq, limbWords_limbsN]

/-- An array whose source values `limbsDec` reads as `a < p` holds the encoding of `a`. -/
theorem WideTemplate.arrLimbs_eq_enc (A : Fin n → BitVec 64) {a : Nat}
    (ha : limbsDec (wordsOf A) = some a) (hap : a < p) :
    arrLimbs A n 0 = FieldLowerTemplate.enc W.P (t := .fp p) ((a : Nat) : ZMod p) := by
  have : NeZero p := ⟨by omega⟩
  rw [W.enc_eq, ZMod.val_natCast, Nat.mod_eq_of_lt hap]
  exact eq_limbsN_of_limbsDec _ ha

/-- An array holding the encoding of `z` has the source values `limbsOf n z.val`. -/
theorem WideTemplate.wordsOf_of_enc (y : Fin n → BitVec 64) (z : ZMod p)
    (h : arrLimbs y n 0 = FieldLowerTemplate.enc W.P (t := .fp p) z) :
    wordsOf y = limbsOf n z.val := by
  rw [wordsOf, h, W.enc_limbsOf]

theorem WideTemplate.arrFlat_two (A B : Fin n → BitVec 64) (x y : ZMod p)
    (hA : arrLimbs A n 0 = FieldLowerTemplate.enc W.P (t := .fp p) x)
    (hB : arrLimbs B n 0 = FieldLowerTemplate.enc W.P (t := .fp p) y) :
    arrFlat (n := n) (Γ := [.fp p, .fp p]) (.cons A (.cons B .nil))
      = flatVal (fun {t} z => FieldLowerTemplate.enc W.P (t := t) z) (.cons x (.cons y .nil)) := by
  change hvAppend (arrLimbs A n 0)
    (hvAppend (arrLimbs B n 0) (arrFlat (n := n) (Γ := []) HVector.nil)) = _
  rw [hA, hB]
  rfl

theorem WideTemplate.arrFlat_one (A : Fin n → BitVec 64) (x : ZMod p)
    (hA : arrLimbs A n 0 = FieldLowerTemplate.enc W.P (t := .fp p) x) :
    arrFlat (n := n) (Γ := [.fp p]) (.cons A .nil)
      = flatVal (fun {t} z => FieldLowerTemplate.enc W.P (t := t) z) (.cons x .nil) := by
  change hvAppend (arrLimbs A n 0) (arrFlat (n := n) (Γ := []) HVector.nil) = _
  rw [hA]
  rfl

/-- The two argument arrays of a valuation at the signature of a method; the one argument
    twice for a method with one argument. -/
def wideArrs : (m : FieldMethod) → Valuation (d := jasminDialect) (wideSig n m) →
    (Fin n → BitVec 64) × (Fin n → BitVec 64)
  | .add, .cons a (.cons b .nil) | .sub, .cons a (.cons b .nil)
  | .mul, .cons a (.cons b .nil) => (a, b)
  | .neg, .cons a .nil | .square, .cons a .nil | .double, .cons a .nil => (a, a)

/-- **The body of a method returns the limbs of its value.** For a wide template at `p`, on
    argument arrays whose source values `limbsDec` reads as `a < p` and, for a method with two
    arguments, `b < p`, the body of the method `m` returns, at every call environment and
    fuel, an array whose source values are `limbsOf n (fieldVal m p a b)`. -/
theorem wideBlock_denoteAt {m : FieldMethod} (x : Valuation (d := jasminDialect) (wideSig n m))
    {a b : Nat} (ha : limbsDec (wordsOf (wideArrs m x).1) = some a) (hap : a < p)
    (hb : m.binary = true → limbsDec (wordsOf (wideArrs m x).2) = some b ∧ b < p)
    (E : CallEnv jasminDialect) (fuel : Nat) :
    ∃ y, (wideBlockOf W m).denoteAt E fuel x = some (.cons y .nil) ∧
      wordsOf y = limbsOf n (fieldVal m p a b) := by
  have : NeZero p := ⟨by omega⟩
  unfold NFProg.denoteAt
  let _ : CallDenote jasminDialect := ⟨E⟩
  refine ⟨_, NFProg.denote_ofCom _ fuel x, ?_⟩
  have hg := W.arith _ (arithOpB_fieldOpOf m p)
  cases m with
  | add =>
    rcases x with _ | ⟨A, _ | ⟨B, _ | _⟩⟩
    obtain ⟨hb, hbp⟩ := hb rfl
    refine (W.wordsOf_of_enc _ ((a : ZMod p) + (b : ZMod p))
      (templateCall_denote W.P W.n_lt _ hg _ _ _ (.cons (a : ZMod p) (.cons (b : ZMod p) .nil))
        ?_)).trans ?_
    · exact W.arrFlat_two A B _ _ (W.arrLimbs_eq_enc A ha hap) (W.arrLimbs_eq_enc B hb hbp)
    · simp only [fieldVal, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hap,
        Nat.mod_eq_of_lt hbp]
  | sub =>
    rcases x with _ | ⟨A, _ | ⟨B, _ | _⟩⟩
    obtain ⟨hb, hbp⟩ := hb rfl
    refine (W.wordsOf_of_enc _ ((a : ZMod p) - (b : ZMod p))
      (templateCall_denote W.P W.n_lt _ hg _ _ _ (.cons (a : ZMod p) (.cons (b : ZMod p) .nil))
        ?_)).trans ?_
    · exact W.arrFlat_two A B _ _ (W.arrLimbs_eq_enc A ha hap) (W.arrLimbs_eq_enc B hb hbp)
    · rw [show (a : ZMod p) - b = ((a + p - b : Nat) : ZMod p) by
        rw [Nat.cast_sub (by omega)]; push_cast; simp]
      rw [ZMod.val_natCast]
      rfl
  | mul =>
    rcases x with _ | ⟨A, _ | ⟨B, _ | _⟩⟩
    obtain ⟨hb, hbp⟩ := hb rfl
    refine (W.wordsOf_of_enc _ ((a : ZMod p) * (b : ZMod p))
      (templateCall_denote W.P W.n_lt _ hg _ _ _ (.cons (a : ZMod p) (.cons (b : ZMod p) .nil))
        ?_)).trans ?_
    · exact W.arrFlat_two A B _ _ (W.arrLimbs_eq_enc A ha hap) (W.arrLimbs_eq_enc B hb hbp)
    · simp only [fieldVal, ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hap,
        Nat.mod_eq_of_lt hbp]
  | neg =>
    rcases x with _ | ⟨A, _ | _⟩
    refine (W.wordsOf_of_enc _ (-(a : ZMod p))
      (templateCall_denote W.P W.n_lt _ hg _ _ _ (.cons (a : ZMod p) .nil) ?_)).trans ?_
    · exact W.arrFlat_one A _ (W.arrLimbs_eq_enc A ha hap)
    · rw [show -(a : ZMod p) = ((p - a : Nat) : ZMod p) by rw [Nat.cast_sub (by omega)]; simp]
      rw [ZMod.val_natCast]
      rfl
  | square =>
    rcases x with _ | ⟨A, _ | _⟩
    refine (W.wordsOf_of_enc _ ((a : ZMod p) * (a : ZMod p))
      (templateCall_denote W.P W.n_lt _ hg _ _ _ (.cons (a : ZMod p) (.cons (a : ZMod p) .nil))
        ?_)).trans ?_
    · exact W.arrFlat_two A A _ _ (W.arrLimbs_eq_enc A ha hap) (W.arrLimbs_eq_enc A ha hap)
    · simp only [fieldVal, ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hap]
  | double =>
    rcases x with _ | ⟨A, _ | _⟩
    refine (W.wordsOf_of_enc _ ((a : ZMod p) + (a : ZMod p))
      (templateCall_denote W.P W.n_lt _ hg _ _ _ (.cons (a : ZMod p) (.cons (a : ZMod p) .nil))
        ?_)).trans ?_
    · exact W.arrFlat_two A A _ _ (W.arrLimbs_eq_enc A ha hap) (W.arrLimbs_eq_enc A ha hap)
    · simp only [fieldVal, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hap, two_mul]

end Wide

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline
