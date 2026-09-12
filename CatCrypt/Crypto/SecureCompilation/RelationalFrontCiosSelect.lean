/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontSecp256k1
public import CatCrypt.Crypto.SecureCompilation.FieldMulEmitRealizesFromCommSquare

/-!
# Representation-domain tag and cost-model selection between the CIOS and Barrett field multiplies

Two field-multiply kernels realize the secp256k1 base-field product:

* the **CIOS** Montgomery multiply `ciosMont4` (`RelationalFrontCiosFieldMul`),
  whose output decodes to the Montgomery product `x·y·R⁻¹` (`R = 2^256`), proved
  by `ciosMont4_realizes_montmul`; and
* the **Barrett** wide multiply `mlMulMod` (`RelationalFrontSecp256k1`), whose
  output decodes to the ordinary product `a·b`, proved by `secp_mul_commutes`.

The two are correct on different operand *representations*. CIOS is the right
realization when the operands are already in Montgomery form (`a·R mod p`);
Barrett is the right realization on ordinary residues. This module carries a
representation-domain tag so the instruction-selection layer can tell the two
apart, and dispatches to the matching kernel by a cost model.

## What is delivered

* **The domain tag (`FieldDomain`).** `ordinary` vs `montgomery`, a marker on a
  field value recording whether its limbs encode the residue `a` or the
  Montgomery representative `a·R`. `montDecode` reads a Montgomery-form slot back
  to its residue (`(a·R)·R⁻¹ = a`); `montgomery_domain_mul` is the algebraic
  invariant `(a·R)(b·R)·R⁻¹ = (a·b)·R` that makes CIOS the correct realization on
  Montgomery-form operands.
* **The CIOS dispatch branch (`fieldEmitRealizes_mul_of_ciosKernel`).** The
  sibling of `fieldEmitRealizes_mul_of_kernel`: from the narrowed residual
  `CiosMont4KernelRealizes` (the leaf bytes are `ciosMont4`'s bytes) and the
  Montgomery-form operand convention, it discharges `FieldEmitRealizes` for the
  Montgomery decode by composing `ciosMont4_realizes_montmul`.
* **The cost predicate (`preferCios`).** A decidable cost comparison routing a
  Montgomery-domain multiply to `ciosMont4` and an ordinary-domain one to the
  Barrett `mlMulMod`.
* **Selection soundness (`select_mul_realizes`).** Whichever kernel the selector
  picks, the emitted leaf realizes the field-multiply spec for that operand
  domain — the CIOS branch from `ciosMont4_realizes_montmul`, the Barrett branch
  from `secp_mul_commutes` (via `fieldEmitRealizes_mul_of_kernel`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4000

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosSelect

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosFieldMul
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
open CatCrypt.Crypto.SecureCompilation.FieldEmitRealizesFromCommSquare
open CatCrypt.Crypto.SecureCompilation.FieldMulEmitRealizesFromCommSquare
open CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## §1. The representation-domain tag and the Montgomery multiply invariant -/

/-- The representation domain of a field value: whether its limb encoding holds
    the ordinary residue `a` or the Montgomery representative `a·R` (`R = 2^256`). -/
inductive FieldDomain
  | ordinary
  | montgomery
deriving DecidableEq, Repr

/-- **The Montgomery multiply invariant.** In any commutative ring with a unit
    radix `rad`, the product of two Montgomery representatives, corrected by one
    `rad⁻¹`, is the Montgomery representative of the product:
    `(a·rad)(b·rad)·rad⁻¹ = (a·b)·rad`. This is the algebraic reason the CIOS
    Montgomery multiply is the right realization on Montgomery-form operands: its
    output stays in the Montgomery domain. -/
theorem montgomery_domain_mul {Rng : Type*} [CommRing Rng] (rad : Rngˣ) (a b : Rng) :
    (a * (rad : Rng)) * (b * (rad : Rng)) * ((rad⁻¹ : Rngˣ) : Rng)
      = (a * b) * (rad : Rng) := by
  have h : (rad : Rng) * ((rad⁻¹ : Rngˣ) : Rng) = 1 := rad.mul_inv
  calc (a * (rad : Rng)) * (b * (rad : Rng)) * ((rad⁻¹ : Rngˣ) : Rng)
      = (a * b) * (rad : Rng) * ((rad : Rng) * ((rad⁻¹ : Rngˣ) : Rng)) := by ring
    _ = (a * b) * (rad : Rng) * 1 := by rw [h]
    _ = (a * b) * (rad : Rng) := by ring

/-! ## §2. The Montgomery radix as a unit and the Montgomery decode -/

instance : NeZero secpP := ⟨secpP_pos.ne'⟩

/-- The Montgomery radix `R = 2^256` in the secp256k1 base field. -/
noncomputable def montR : ZMod secpP := 2 ^ 256

/-- `R = 2^256` is a unit in `ZMod secpP` — it is coprime to the odd modulus. -/
theorem montR_isUnit : IsUnit montR := by
  have hodd : ¬ (2 ∣ secpP) := by
    show ¬ (2 ∣ valLimbs secp256k1Limbs)
    rw [show secp256k1Limbs = (0xfffffffefffffc2f : BitVec 64) :: _ from rfl, valLimbs_cons]
    have : (0xfffffffefffffc2f : BitVec 64).toNat = 18446744069414583343 := by decide
    omega
  have h2 : Nat.Coprime 2 secpP := (Nat.prime_two.coprime_iff_not_dvd).mpr hodd
  have hpow : Nat.Coprime (2 ^ 256) secpP := h2.pow_left 256
  have hcast : (montR) = ((2 ^ 256 : ℕ) : ZMod secpP) := by push_cast [montR]; ring
  rw [hcast]
  exact (ZMod.isUnit_iff_coprime (2 ^ 256) secpP).mpr hpow

/-- The Montgomery-form decode: read the `.TFp` slot's limb vector via `readLimbs`
    and correct it by `R⁻¹`, recovering the residue a Montgomery representative
    stands for (`(a·R)·R⁻¹ = a`). The Montgomery-domain analogue of `klimbDecode`. -/
noncomputable def montDecode (readLimbs : RustVal .TFp → List (BitVec 64)) :
    RustVal .TFp → ZMod secpP :=
  fun v => (valLimbs (readLimbs v) : ZMod secpP) * montR⁻¹

/-! ## §3. The CIOS dispatch branch

`CiosMont4KernelRealizes readLimbs leaf leafSpec` is the CIOS analogue of
`KLimbMulKernelRealizes`: the leaf-call value, read as a limb vector, is exactly
`ciosMont4` on the operand limb vectors — the KAT fact that the emitted leaf's
bytes are the CIOS multiply's bytes. -/

/-- **The narrowed (kernel-level) residual for the CIOS multiply.** For every
    operand pair, the limb read of the leaf-call value equals `ciosMont4` run on
    the operand limb vectors. This is a fact about the emitted bytes, strictly
    narrower than the abstract-value claim. -/
def CiosMont4KernelRealizes
    (readLimbs : RustVal .TFp → List (BitVec 64)) (leaf : String)
    (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    readLimbs
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = ciosMont4 (readLimbs aVal) (readLimbs bVal)

/-- **The CIOS commuting square discharges `FieldEmitRealizes` for the Montgomery
    decode.** Given the narrowed CIOS residual `hkernel` and the Montgomery-form
    operand convention `hform` (each slot holds a 4-limb vector below the modulus),
    the emitted leaf realizes the field product under `montDecode`. The proof reads
    the leaf-call through `montDecode`, rewrites the limb read by `hkernel` to
    `ciosMont4`, and closes with `ciosMont4_realizes_montmul` — the CIOS Montgomery
    multiply law — cancelling the radix with `montR_isUnit`. The sibling of
    `fieldEmitRealizes_mul_of_kernel`, for the CIOS structure and the Montgomery
    domain. -/
theorem fieldEmitRealizes_mul_of_ciosKernel
    (readLimbs : RustVal .TFp → List (BitVec 64)) (leaf : String) (leafSpec : LeafSpec)
    (hkernel : CiosMont4KernelRealizes readLimbs leaf leafSpec)
    (hform : ∀ v : RustVal .TFp,
      (readLimbs v).length = 4 ∧ valLimbs (readLimbs v) < secpP) :
    FieldEmitRealizes secpP (montDecode readLimbs) (· * ·) leaf leafSpec := by
  intro aVal bVal oldDest
  show montDecode readLimbs
      (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = montDecode readLimbs aVal * montDecode readLimbs bVal
  unfold montDecode
  rw [hkernel aVal bVal oldDest]
  obtain ⟨hxlen, hxlt⟩ := hform aVal
  obtain ⟨hylen, hylt⟩ := hform bVal
  have hreal := ciosMont4_realizes_montmul (readLimbs aVal) (readLimbs bVal)
    hxlen hylen hxlt hylt
  -- `hreal : (valLimbs (ciosMont4 …) : ZMod secpP) * 2^256 = valLimbs aVal * valLimbs bVal`
  set c : ZMod secpP := (valLimbs (ciosMont4 (readLimbs aVal) (readLimbs bVal)) : ZMod secpP)
  set A : ZMod secpP := (valLimbs (readLimbs aVal) : ZMod secpP)
  set B : ZMod secpP := (valLimbs (readLimbs bVal) : ZMod secpP)
  have hRR : montR * montR⁻¹ = 1 := ZMod.mul_inv_of_unit _ montR_isUnit
  have hc : c * montR = A * B := hreal
  calc c * montR⁻¹
      = c * (montR * montR⁻¹) * montR⁻¹ := by rw [hRR, mul_one]
    _ = (c * montR) * (montR⁻¹ * montR⁻¹) := by ring
    _ = (A * B) * (montR⁻¹ * montR⁻¹) := by rw [hc]
    _ = (A * montR⁻¹) * (B * montR⁻¹) := by ring

/-! ## §4. The cost model and the dispatch predicate

`preferCios dom` compares a rough instruction-count cost of the two kernels for a
field-multiply whose operands are in domain `dom`. On Montgomery-form operands
`ciosMont4` is one Montgomery multiply; on ordinary residues it would need a
conversion round trip, so the Barrett product-then-reduce is cheaper there. -/

/-- Rough instruction cost of the CIOS multiply on operands in domain `dom`: one
    Montgomery multiply when the operands are already in Montgomery form, plus a
    conversion round trip when they are ordinary. -/
def ciosCost : FieldDomain → Nat
  | .montgomery => 1
  | .ordinary => 3

/-- Rough instruction cost of the Barrett wide multiply, domain-independent
    (product then reduce). -/
def barrettCost : FieldDomain → Nat
  | .montgomery => 2
  | .ordinary => 2

/-- **The dispatch predicate.** Route a field-multiply to `ciosMont4` when its
    cost is below the Barrett cost for the operand domain, otherwise to `mlMulMod`.
    Evaluates to `true` on `montgomery` and `false` on `ordinary`. -/
def preferCios (dom : FieldDomain) : Bool := ciosCost dom < barrettCost dom

theorem preferCios_montgomery : preferCios .montgomery = true := by decide

theorem preferCios_ordinary : preferCios .ordinary = false := by decide

/-! ## §5. Selection soundness

Whichever kernel the cost predicate selects, the emitted leaf realizes the
field-multiply spec for that operand domain: the CIOS branch through
`fieldEmitRealizes_mul_of_ciosKernel` (composing `ciosMont4_realizes_montmul`),
the Barrett branch through `fieldEmitRealizes_mul_of_kernel` (composing
`secp_mul_commutes`). The two branches carry independent leaf data, so the
soundness statement is non-vacuous. -/

/-- **Selection soundness.** For any representation domain, the selected kernel's
    emitted leaf realizes the field product for that domain:

    * when `preferCios dom = true`, the CIOS leaf realizes the Montgomery-decode
      field product (`fieldEmitRealizes_mul_of_ciosKernel`); and
    * when `preferCios dom = false`, the Barrett leaf realizes the ordinary-decode
      field product at the secp256k1 prime (`fieldEmitRealizes_mul_of_kernel`).

    The CIOS branch's value content is `ciosMont4_realizes_montmul`; the Barrett
    branch's is `secp_mul_commutes` (`= encMLK_mul_commutes secpKLimbPrimeMul`). -/
theorem select_mul_realizes (dom : FieldDomain)
    (readLimbsC : RustVal .TFp → List (BitVec 64)) (leafC : String) (leafSpecC : LeafSpec)
    (hcios : CiosMont4KernelRealizes readLimbsC leafC leafSpecC)
    (hformC : ∀ v : RustVal .TFp,
      (readLimbsC v).length = 4 ∧ valLimbs (readLimbsC v) < secpP)
    (readLimbsS : RustVal .TFp → List (BitVec 64)) (leafS : String) (leafSpecS : LeafSpec)
    (hkernel : KLimbMulKernelRealizes secpKLimbPrimeMul readLimbsS leafS leafSpecS)
    (hencS : ∀ v : RustVal .TFp,
      readLimbsS v = encMLK secpQ 5
        (klimbDecode secpKLimbPrimeMul.toKLimbPrime readLimbsS v)) :
    (preferCios dom = true →
        FieldEmitRealizes secpP (montDecode readLimbsC) (· * ·) leafC leafSpecC)
      ∧ (preferCios dom = false →
        FieldEmitRealizes secpQ
          (klimbDecode secpKLimbPrimeMul.toKLimbPrime readLimbsS) (· * ·) leafS leafSpecS) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact fieldEmitRealizes_mul_of_ciosKernel readLimbsC leafC leafSpecC hcios hformC
  · exact fieldEmitRealizes_mul_of_kernel secpKLimbPrimeMul readLimbsS leafS leafSpecS hkernel hencS

/-! ## §6. Non-vacuity: a canonical CIOS limb-kernel realizer

A concrete `LeafSpec` under which the narrowed CIOS residual (§3) holds, so the
CIOS dispatch branch's hypothesis is satisfiable — the analogue of
`klimbMulKernelRealizes_canonical` for `ciosMont4`. -/

/-- The canonical `CallSpec` realizing the `ciosMont4` limb kernel at `leaf`: read
    the two positional `.TFp` operands' limb vectors, run `ciosMont4`, and
    re-encode via a limb-write section; off-target return `oldDest`. -/
def ciosMont4CallSpec
    (readLimbs : RustVal .TFp → List (BitVec 64))
    (writeLimbs : List (BitVec 64) → RustVal .TFp) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → List (BitVec 64) := fun a =>
        if ht : a.1 = TowerType.TFp then readLimbs (ht ▸ a.2) else []
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ writeLimbs (ciosMont4 (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity for the CIOS residual.** For the canonical realizer built from
    `ciosMont4CallSpec` with a limb-write section (`readLimbs ∘ writeLimbs = id`),
    the CIOS kernel-realization holds. -/
theorem ciosMont4KernelRealizes_canonical
    (readLimbs : RustVal .TFp → List (BitVec 64))
    (writeLimbs : List (BitVec 64) → RustVal .TFp)
    (hsection : ∀ l : List (BitVec 64), readLimbs (writeLimbs l) = l)
    (leaf : String) (limbStore : LimbStoreSpec) :
    CiosMont4KernelRealizes readLimbs leaf
      { call := ciosMont4CallSpec readLimbs writeLimbs leaf, limbStore := limbStore } := by
  intro aVal bVal oldDest
  show readLimbs (ciosMont4CallSpec readLimbs writeLimbs leaf leaf .TFp [.TFp, .TFp]
      oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) = _
  simp only [ciosMont4CallSpec, ite_true, dite_true, hsection]

end CatCrypt.Crypto.SecureCompilation.RelationalFrontCiosSelect
