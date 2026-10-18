/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithLowering

/-!
# Poly lowering — the L4′ → L2 (Poly → ModArith) step

The lowering step of the layered crypto-IR stack (`VIR/DIALECTS.md`):

    Poly → Field → ModArith

proven denotation-preserving, mirroring `FieldLowering`'s /
`ModArithLowering`'s `lower_denote_preserved`.

A Poly op lowers to a **schedule of ModArith ops** on the underlying `ZMod q`
coefficients:

* the **forward NTT** is a fixed sequence of **Cooley–Tukey butterflies**; each
  butterfly `(a, b) ↦ (a + ζ·b, a − ζ·b)` over a twiddle `ζ` lowers to **one**
  ModArith `modMul` (the twiddle product `ζ·b`) plus a `modAdd` and a `modSub`.
  We prove the butterfly schedule (built from the `ModArith` leaves
  `modMulF`/`modAddF`/`modSubF`) denotes to the abstract CT-butterfly value.
* the **inverse NTT** is the same butterfly schedule with the inverse twiddles
  plus a final `polySMul` by `n⁻¹` (a ModArith `modMul`).
* **pointwise base-multiply** lowers to **`n` ModArith `montMul`s** (one per
  evaluation point) — each lane is an independent residue-ring multiply; we
  prove the per-lane schedule denotes to the abstract pointwise product.

## Main results

* `ctButterfly` — the abstract Cooley–Tukey butterfly over `ZMod q`.
* `ctButterflySchedule` — the ModArith-level butterfly schedule
  (`modMulF`/`modAddF`/`modSubF` on the twiddle + two coordinates).
* `ctButterflySchedule_denote` — **denotation preservation** for the NTT
  butterfly: the schedule equals the abstract CT-butterfly value.  Both sides go
  through the *same* `ZMod q` ops, so it is a ring identity.
* `pointwiseMulSchedule` / `pointwiseMulSchedule_denote` — the pointwise base
  multiply lowered to `n` per-lane ModArith multiplies, denoting to the abstract
  pointwise product `(aᵢ·bᵢ)ᵢ`.
* `lower_denote_preserved` — the op-level identity-realisation statement
  (mirrors `FieldLowering`/`ModArithLowering`), plus the butterfly +
  pointwise-mul realisation theorems end-to-end.
* `routeOfModulus_scalar_of_not_vectorizable` — the NTT-lane multiply routes to
  the scalar path at a modulus that is not pseudo-Mersenne / Solinas.

The module states no constant-time property.

## The redundant-limb gate on the Vector route

The pointwise-mul lane multiplies vectorize *only* for pseudo-Mersenne / Solinas
moduli (ML-KEM's `q = 3329`, the BabyBear/Goldilocks Plonky3 primes), per the
`ModArithLowering.vectorizable` predicate.  A random NTT-friendly prime
keeps the lanes scalar.  We surface that gate here via `routeOfModulus` (reusing
the L2 `routeOf` decision) so the Vector-vs-scalar choice for the NTT lanes is
made once, at L2, not re-decided per protocol.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic (NttDomains)

/-! ## 1. The Cooley–Tukey butterfly over ModArith leaves

The radix-2 decimation-in-time NTT butterfly maps a pair `(a, b)` and a twiddle
`ζ` to `(a + ζ·b, a − ζ·b)`.  This is the atomic step of *every* NTT layer; the
whole forward transform is `log₂ n` rounds of `n/2` such butterflies. -/

variable {q : Nat}

/-- The **abstract Cooley–Tukey butterfly**: `(a, b, ζ) ↦ (a + ζ·b, a − ζ·b)`
    over `ZMod q`.  This is the abstract spec the NTT layer realises. -/
def ctButterfly (ζ a b : ZMod q) : ZMod q × ZMod q :=
  (a + ζ * b, a - ζ * b)

/-- The **ModArith-level butterfly schedule**: the twiddle product `t = ζ·b` is a
    `modMul`, and the two outputs are a `modAdd a t` and a `modSub a t`.  Built
    from the `ModArith` leaves `modMulF`/`modAddF`/`modSubF`. -/
def ctButterflySchedule (ζ a b : ZMod q) : ZMod q × ZMod q :=
  let t := modMulF ζ b
  (modAddF a t, modSubF a t)

/-! ## 2. Denotation preservation — the NTT butterfly lowers correctly

The ModArith butterfly schedule denotes to the *same value* as the abstract
CT-butterfly.  Because the schedule is built from the ModArith leaves
(`modMulF = (· * ·)`, `modAddF = (· + ·)`, `modSubF = (· − ·)` on `ZMod q`) and
the abstract butterfly is the same `ZMod q` formula, the two coordinates are
definitionally equal. -/

/-- **Denotation preservation, NTT butterfly.** The lowered ModArith butterfly
    schedule equals the abstract Cooley–Tukey butterfly — the end-to-end
    Poly→ModArith lowering correctness statement for one NTT butterfly. -/
theorem ctButterflySchedule_denote (ζ a b : ZMod q) :
    ctButterflySchedule ζ a b = ctButterfly ζ a b := rfl

/-- The first output of the butterfly schedule equals `a + ζ·b`. -/
theorem ctButterflySchedule_fst (ζ a b : ZMod q) :
    (ctButterflySchedule ζ a b).1 = a + ζ * b := rfl

/-- The second output of the butterfly schedule equals `a − ζ·b`. -/
theorem ctButterflySchedule_snd (ζ a b : ZMod q) :
    (ctButterflySchedule ζ a b).2 = a - ζ * b := rfl

/-- **The butterfly realises the abstract NTT step via three ModArith ops.**
    Each output coordinate is the denotation of a single ModArith op applied to
    `a` and the twiddle product `modMul ζ b`: the first is `modAdd`, the second
    `modSub`.  This is the op-level lowering tie consumed by the whole-program
    fold (the NTT layer is `n/2` of these). -/
theorem ctButterfly_ops (ζ a b : ZMod q) :
    (ctButterfly ζ a b).1
      = modArithDenote.denote (.modAdd q)
          (.cons a (.cons (modArithDenote.denote (.modMul q) (.cons ζ (.cons b .nil))) .nil))
    ∧ (ctButterfly ζ a b).2
      = modArithDenote.denote (.modSub q)
          (.cons a (.cons (modArithDenote.denote (.modMul q) (.cons ζ (.cons b .nil))) .nil)) :=
  ⟨rfl, rfl⟩

/-! ## 3. Pointwise base multiply lowered to `n` ModArith multiplies

The NTT-domain pointwise product of two evaluation vectors `a, b : Fin n → ZMod q`
is the `n` independent residue-ring multiplies `(aᵢ·bᵢ)ᵢ`.  We lower it to `n`
ModArith `modMul`s — one per lane; the lanes vectorize on a pseudo-Mersenne
modulus and stay scalar otherwise. -/

variable {n : Nat}

/-- The **pointwise-mul schedule**: `n` per-lane ModArith multiplies
    `(modMulF aᵢ bᵢ)ᵢ`. -/
def pointwiseMulSchedule (a b : Fin n → ZMod q) : Fin n → ZMod q :=
  fun i => modMulF (a i) (b i)

/-- **Denotation preservation, pointwise base multiply.** The lowered `n`-lane
    ModArith multiply schedule equals the abstract pointwise product `(aᵢ·bᵢ)ᵢ`.
    Each lane is the ModArith `modMul` denotation — the per-lane Poly→ModArith
    lowering correctness for `basemul`. -/
theorem pointwiseMulSchedule_denote (a b : Fin n → ZMod q) (i : Fin n) :
    pointwiseMulSchedule a b i
      = modArithDenote.denote (.modMul q) (.cons (a i) (.cons (b i) .nil)) := rfl

/-- The pointwise-mul schedule equals the abstract lane product `aᵢ·bᵢ`. -/
theorem pointwiseMulSchedule_eq (a b : Fin n → ZMod q) (i : Fin n) :
    pointwiseMulSchedule a b i = a i * b i := rfl

/-! ## 4. Op-level identity realisation (mirrors `FieldLowering`)

For the coefficient add/sub/scalar ops the lowering is 1:1 (the leaf is the same
`ZMod q`-coefficient ModArith op), so the realised value is the op's own
denotation. -/

variable [NttDomains]

/-- The realised denotation of a Poly op (identity realisation). -/
@[reducible] noncomputable def realise (op : PolyOp)
    (args : HVector (fun (t : PolyTy) => ⟦t⟧)
              (DialectSignature.sig (d := polyDialect) op)) :
    ⟦DialectSignature.ret (d := polyDialect) op⟧ :=
  polyDenote.denote op args

/-- **Denotation preservation (op-level, identity realisation).** The realised
    value equals the Poly op's abstract denotation.  This is the L4′ lowering-
    correctness statement for the 1:1 lowering; the non-trivial NTT butterfly /
    pointwise realisations discharge the same equality from
    `ctButterflySchedule_denote` / `pointwiseMulSchedule_denote`. -/
theorem lower_denote_preserved (op : PolyOp)
    (args : HVector (fun (t : PolyTy) => ⟦t⟧)
              (DialectSignature.sig (d := polyDialect) op)) :
    realise op args = polyDenote.denote op args := rfl

/-! ## 5. The redundant-limb gate on the NTT lanes

The pointwise-mul lane multiplies route to the Vector dialect iff the modulus is
vectorizable (pseudo-Mersenne / Solinas).  We surface the L2 routing decision
(`ModArithLowering.routeOf`) for the lane multiply `modMul q`, so the
Vector-vs-scalar choice for the NTT lanes is made once at L2. -/

/-- The lowering route the redundant-limb rule selects for the NTT-lane multiply at modulus
    `q`: `vector` if `q` is a pseudo-Mersenne / Solinas prime, else `scalar`. -/
noncomputable def routeOfModulus (q : Nat) : ModArithDialect.LowerTarget :=
  ModArithDialect.routeOf (.modMul q)

omit [NttDomains] in
/-- The NTT lanes route to `scalar` at a non-vectorizable modulus — a random
    NTT-friendly prime keeps the lanes scalar (the redundant-limb rule applied to
    the NTT-domain pointwise product). -/
theorem routeOfModulus_scalar_of_not_vectorizable (q : Nat)
    (hv : ¬ ModArithDialect.vectorizable q) :
    routeOfModulus q = .scalar :=
  ModArithDialect.routeOf_scalar_of_not_vectorizable (.modMul q) q rfl hv

/-! ## 6. Smoke test: the butterfly schedule matches the abstract step

On `ζ = 3, a = 5, b = 2 : ZMod 7` the butterfly gives
`(5 + 3·2, 5 − 3·2) = (11, −1) = (4, 6) (mod 7)`, equal to the ModArith
schedule. -/

example : ctButterflySchedule (3 : ZMod 7) 5 2 = ctButterfly (3 : ZMod 7) 5 2 := rfl

example : ctButterflySchedule (3 : ZMod 7) 5 2 = ((4 : ZMod 7), (6 : ZMod 7)) := by decide

/-- Smoke: the 2-lane pointwise schedule equals the lane products. -/
example (a b : Fin 2 → ZMod 7) (i : Fin 2) : pointwiseMulSchedule a b i = a i * b i := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
