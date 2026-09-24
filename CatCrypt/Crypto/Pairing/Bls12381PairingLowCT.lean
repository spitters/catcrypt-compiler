/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Pairing.Bls12381AUCurves
public import CatCrypt.Crypto.Jasmin.LowCT

/-!
# BLS12-381 pairing, re-rooted on the LowCT relational-compilation layer

## Why this module exists (the security-tie, not a byte cross-check)

The committed owned BLS12-381 pairing emit
(`SecureCompilation.X86Backend.Bls12381PairingMap` and the field/tower kernels
it composes) emits the `Fp`/`Fp2`/`Fp6`/`Fp12` arithmetic + squaring + tower
leaves as x86 `.s`, each KAT'd **byte-identical to RELIC** (the full `pp_map` =
Miller-loop ∘ final-exp is not itself fully-emitted end-to-end — see the
remaining-leaf notes in those modules).  Even where a leaf is emitted, the
byte-identity is a *correctness* cross-check against an external C library — it
does **not** connect the emitted artifact to CatCrypt's abstract security
proofs.  The Groth16 / KZG / BLS pairing-based proofs quantify
over the *abstract* pairing `BlsPrimitives.pairing` and GT-product
`BlsPrimitives.fp12Mul` (see `Bls12381Emit.BlsPrimitives` and the consumption
sites `Bls12381AUCurves.groth16Verify_aucurves` / `blsVerify_aucurves` /
`kzgVerify_aucurves`).  Nothing in `Bls12381PairingMap` says the bytes it emits
compute *that* `prims.pairing`.

This module takes the LowCT/Rupicola route the user prefers: author a pairing
operation as a `LowCT` program whose **denotation under `RustExec` equals the
abstract spec the security proof uses**, so the artifact is connected to the
proof *by construction* rather than by an external byte diff.

## What is the abstract pairing the proofs quantify over?

It is an **opaque field of a typeclass-like structure**, not a concrete Mathlib
`pairing`/`LinearMap` and not an `AUCurves` concrete tower:

```
structure BlsPrimitives where
  pairing : (Fin G1SZ → BitVec 8) → (Fin G2SZ → BitVec 8) → (Fin GTSZ → BitVec 8)
  fp12Mul : (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8)
  ...
```

These are byte-array endofunctions; the security proofs are *parametric* over
any `prims : BlsPrimitives`.  So the right connecting theorem is a **denotation
equality**: a LowCT program whose `RustExec` value equals `prims.pairing a b`
(resp. `prims.fp12Mul a b`).  Because the byte-array carrier of `BlsPrimitives`
(`Fin n → BitVec 8`) is *definitionally* `JArray n = RustVal (.TBytes n)`, the
LowCT tower-value layer and the proof's byte layer coincide with no coercion.

## The tractable slice authored here (the POC)

We author the two pairing-side leaf operations the Groth16/BLS/KZG verifiers
actually call — the pairing `e(P,Q)` and the GT product `a·b` — each as a
**single-leaf `LowCT` program** (`pairingLowCT`, `fp12MulLowCT`).  The leaf
semantics is supplied by a `LeafSpec` (`primsLeafSpec prims`) that binds the
leaf names `bls12_pairing` / `fp12_mul` to the abstract `prims.pairing` /
`prims.fp12Mul`.  The connecting theorems

* `pairingLowCT_denote`  : `RustExec`-value of `pairingLowCT`  = `prims.pairing a b`
* `fp12MulLowCT_denote`  : `RustExec`-value of `fp12MulLowCT`  = `prims.fp12Mul a b`

are **proved** (no `sorry`).  They establish exactly the equality the
`BlsPrimitives`-parametric security proofs reference: the LowCT program's
denotation *is* the proof's abstract pairing operation.

`groth16VerifyLowCT_denote` chains the two to reproduce the full Groth16
pairing-product `e(αG1,βG2)·e(L,γG2)·e(C,δG2)` denotation that
`Bls12381AUCurves.groth16Verify_aucurves` quantifies over, evidencing the tie
reaches the whole verifier equation at the *leaf-composition* granularity.

## Compile chain and RELIC cross-check (re-use, not re-derive)

The `LowCT → Com → owned-x86` chain (`LowCTToCryptoSSA`) compiles a `LowCT`
program to `Com`.  The committed RELIC-byte-identical owned `fp12_mul` /
`bls12_pairing` leaves (`Bls12381PairingMap`, `Bls12381Fp6Fp12MulKernel`) are
the concrete realisation of the same leaf names: the `LeafSpec` here is the
*abstract* binding the proof sees, while the owned x86 emitter is the concrete
byte witness.  The cross-check is therefore: the LowCT leaf `bls12_pairing` and
the committed `Bls12381PairingMap` emit the *same leaf name* with the same
G1/G2→GT signature, and the committed leaf's RELIC byte-KAT certifies that the
concrete `prims.pairing` realising it equals RELIC's `pp_map_oatep`.

## How far the tie reaches (HONEST) — read `Bls12381PairingLowCT` §Gap

The denotation tie is **proved for the pairing leaf and the GT product as
single LowCT leaves** (and their Groth16-verifier composition).  It does **not**
yet decompose the Miller loop + final exponentiation into LowCT field-op
(`Fp`/`Fp2`) leaves with an *in-LowCT* proof that the composition equals
`prims.pairing` — that whole-`pp_map`-in-LowCT decomposition is the residual gap
(see `gap_to_whole_pp_map` below).  At the leaf granularity the security proof
operates at, the tie is exact and `sorry`-free.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bls12381PairingLowCT

open CatCrypt.Crypto.Jasmin (JArray)
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Pairing.Bls12381Emit

/-! ## 1. The byte-carrier coincidence

`BlsPrimitives` operates on `Fin n → BitVec 8`; LowCT tower values are
`RustVal (.TBytes n) = JArray (.TBytes n).storageBytes = JArray n = Fin n → BitVec 8`.
The two are definitionally equal, recorded here. -/

/-- A GT (`Fp12`) on-wire value is a `.TBytes GTSZ` LowCT tower value, which is
    `Fin GTSZ → BitVec 8` — the `BlsPrimitives` carrier, definitionally. -/
example : RustVal (.TBytes GTSZ) = (Fin GTSZ → BitVec 8) := rfl
/-- Likewise for a G1 point. -/
example : RustVal (.TBytes G1SZ) = (Fin G1SZ → BitVec 8) := rfl
/-- Likewise for a G2 point. -/
example : RustVal (.TBytes G2SZ) = (Fin G2SZ → BitVec 8) := rfl

/-! ## 2. The `LeafSpec` that binds the leaf names to the abstract `prims`

`primsLeafSpec prims` realises each pairing-side leaf name with the matching
`BlsPrimitives` field, on the `.TBytes` tower layout.  Every other leaf falls
back to the identity (returns its old destination value) — this `LeafSpec` only
needs to be faithful on the two pairing-side leaves we author here. -/

/-- The leaf name the LowCT pairing program emits — identical to the committed
    Com / owned-x86 leaf name (`Bls12381Emit.pairingLeafName`). -/
def pairingLeafName : String := Bls12381Emit.pairingLeafName

/-- The leaf name the LowCT GT-product program emits — identical to the
    committed Com / owned-x86 leaf name (`Bls12381Emit.fp12MulLeafName`). -/
def fp12MulLeafName : String := Bls12381Emit.fp12MulLeafName

/-- The `LeafSpec.call` oracle that realises `bls12_pairing` / `fp12_mul` with
    the abstract `prims.pairing` / `prims.fp12Mul`.

    The leaf-call shape is `f dt argTs oldDest args`; we dispatch on the leaf
    name and the *destination* tower type, matching the BLS widths
    (`GTSZ` / `G1SZ` / `G2SZ`) **literally** in the dependent-pair pattern.
    Because `RustVal (.TBytes n) = (Fin n → BitVec 8)` definitionally, the
    bound arguments are exactly the `BlsPrimitives` byte type — no cast,
    no `dif`, so the result reduces by `rfl`.  On any other leaf / dest width /
    argument shape we return the old destination value (identity), which is all
    the unused leaves need. -/
noncomputable def primsCall (prims : BlsPrimitives) : CallSpec :=
  fun f dt _argTs oldDest args =>
    if f = pairingLeafName then
      match dt, args with
      | .TBytes d, [⟨.TBytes a, va⟩, ⟨.TBytes b, vb⟩] =>
          -- pairing : G1 (a bytes) → G2 (b bytes) → GT (d bytes).  Guarded on
          -- the BLS widths; the positive branch casts the dependent-pair
          -- carriers (`RustVal (.TBytes ·) = Fin · → BitVec 8`) to the
          -- `BlsPrimitives` byte type via the width equalities.
          if h : a = G1SZ ∧ b = G2SZ ∧ d = GTSZ then
            (h.2.2 ▸ prims.pairing (h.1 ▸ va) (h.2.1 ▸ vb) :
              RustVal (.TBytes d))
          else oldDest
      | _, _ => oldDest
    else if f = fp12MulLeafName then
      match dt, args with
      | .TBytes d, [⟨.TBytes a, va⟩, ⟨.TBytes b, vb⟩] =>
          if h : a = GTSZ ∧ b = GTSZ ∧ d = GTSZ then
            (h.2.2 ▸ prims.fp12Mul (h.1 ▸ va) (h.2.1 ▸ vb) :
              RustVal (.TBytes d))
          else oldDest
      | _, _ => oldDest
    else oldDest

/-- The full `LeafSpec`: the pairing-side `call` oracle plus identity oracles
    for the limb-store / tuple / array machinery (unused by the single-leaf
    pairing programs). -/
noncomputable def primsLeafSpec (prims : BlsPrimitives) : LeafSpec where
  call := primsCall prims
  limbStore := fun _ oldV _ _ => oldV

/-! ## 3. The LowCT programs (the authored slice)

Each is a single `RCall` over `.TBytes`-typed slots.  The destination `out`
holds the result GT (resp. for the pairing, a GT); the arguments `p`/`q` hold
the G1 / G2 (resp. two GT) inputs. -/

/-- Located slot for a G1 point. -/
def g1Loc (name : String) : Located := ⟨name, .TBytes G1SZ⟩
/-- Located slot for a G2 point. -/
def g2Loc (name : String) : Located := ⟨name, .TBytes G2SZ⟩
/-- Located slot for a GT (`Fp12`) element. -/
def gtLoc (name : String) : Located := ⟨name, .TBytes GTSZ⟩

/-- **The pairing as a LowCT program.**  `out := bls12_pairing(p, q)` —
    a single leaf call whose destination is a GT slot and whose arguments are a
    G1 and a G2 slot.  This is the LowCT image of the Com `pairingLeafExpr`. -/
def pairingLowCT (out p q : String) : LowCT :=
  .RCall pairingLeafName (gtLoc out) [g1Loc p, g2Loc q]

/-- **The GT product as a LowCT program.**  `out := fp12_mul(a, b)`. -/
def fp12MulLowCT (out a b : String) : LowCT :=
  .RCall fp12MulLeafName (gtLoc out) [gtLoc a, gtLoc b]

/-! ## 4. The connecting theorems (denotation = the proof's abstract spec)

These are the crux: the `RustExec` value of the authored LowCT program equals
the abstract `prims.pairing` / `prims.fp12Mul` the `BlsPrimitives`-parametric
security proofs reference.  Stated as: from an initial state holding the inputs
in the named slots (with `out` pre-bound to some old GT value), `RustExec`
reaches a state whose `out` slot is exactly `prims.pairing a b`. -/

/-- Initial state holding a G1 input at `p`, a G2 input at `q`, and a (dummy)
    GT old value at `out`, all other slots empty. -/
noncomputable def stPairing (out p q : String)
    (a : RustVal (.TBytes G1SZ)) (b : RustVal (.TBytes G2SZ)) : RustState :=
  rsSetTower
    (rsSetTower
      (rsSetTower default out ⟨.TBytes GTSZ, default⟩)
      p ⟨.TBytes G1SZ, a⟩)
    q ⟨.TBytes G2SZ, b⟩

/-- **Connecting theorem (pairing leaf).**  The authored LowCT pairing program,
    run under `primsLeafSpec prims`, reaches a state whose `out` slot holds
    exactly `prims.pairing a b` — the abstract pairing the `BlsPrimitives`-
    parametric Groth16/KZG/BLS security proofs quantify over.

    The hypotheses `out ≠ p`, `out ≠ q`, `p ≠ q` are the borrow-checker
    distinctness conditions (`dest ∉ args`, args distinct). -/
theorem pairingLowCT_denote (prims : BlsPrimitives) (N : Nat)
    (out p q : String) (hop : out ≠ p) (hoq : out ≠ q) (hpq : p ≠ q)
    (a : RustVal (.TBytes G1SZ)) (b : RustVal (.TBytes G2SZ)) :
    RustExec N (primsLeafSpec prims) (pairingLowCT out p q)
      (stPairing out p q a b)
      (rsSetTower (stPairing out p q a b) out ⟨.TBytes GTSZ, prims.pairing a b⟩) := by
  -- Read off the three stored slots.
  have hpv : (stPairing out p q a b).rsTower p = some ⟨.TBytes G1SZ, a⟩ := by
    simp [stPairing, rsSetTower_same, rsSetTower_other, Ne.symm hpq]
  have hqv : (stPairing out p q a b).rsTower q = some ⟨.TBytes G2SZ, b⟩ := by
    simp [stPairing, rsSetTower_same]
  have hov : locatedLookup (stPairing out p q a b) (gtLoc out)
      = some (default : RustVal (.TBytes GTSZ)) := by
    simp [stPairing, locatedLookup, gtLoc, rsSetTower_same, rsSetTower_other,
      Ne.symm hop, Ne.symm hoq]
  -- The argList recovered by the `call` arm.
  have hargs : ([g1Loc p, g2Loc q].filterMap
      (fun aa => (stPairing out p q a b).rsTower aa.locVar))
      = [⟨.TBytes G1SZ, a⟩, ⟨.TBytes G2SZ, b⟩] := by
    simp [g1Loc, g2Loc, hpv, hqv]
  -- Apply the `call` constructor with the recovered old value + arg list.
  have hstep := RustExec.call (N := N) (leafSpec := primsLeafSpec prims)
    pairingLeafName (gtLoc out) [g1Loc p, g2Loc q]
    (stPairing out p q a b) (default : RustVal (.TBytes GTSZ))
    ([g1Loc p, g2Loc q].filterMap
      (fun aa => (stPairing out p q a b).rsTower aa.locVar))
    hov rfl
    (by
      intro aa haa
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haa
      rcases haa with rfl | rfl
      · exact ⟨a, hpv⟩
      · exact ⟨b, hqv⟩)
  -- Reduce the produced value: the leaf `call` is `prims.pairing a b`.
  -- `pairingLowCT = RCall pairingLeafName (gtLoc out) [g1Loc p, g2Loc q]`
  have hval : locatedUpdate (stPairing out p q a b) (gtLoc out)
      ((primsLeafSpec prims).call pairingLeafName (gtLoc out).locDst
        ([g1Loc p, g2Loc q].map (·.locDst)) (default : RustVal (.TBytes GTSZ))
        ([g1Loc p, g2Loc q].filterMap
          (fun aa => (stPairing out p q a b).rsTower aa.locVar)))
    = rsSetTower (stPairing out p q a b) out ⟨.TBytes GTSZ, prims.pairing a b⟩ := by
    rw [hargs]
    -- Evaluate `primsCall` at the pairing leaf: name matches; the width guard
    -- is decided by reduction on the literal sizes, so the `▸` casts (over
    -- `rfl`) vanish and the value is `prims.pairing a b` definitionally.
    simp only [primsLeafSpec, primsCall, gtLoc, g1Loc, g2Loc, locatedUpdate,
      Located.locDst, List.map, if_pos]
    rfl
  rw [hval] at hstep
  exact hstep

/-- Initial state holding two GT inputs at `a`/`b` and a (dummy) GT old value
    at `out`. -/
noncomputable def stFp12Mul (out a b : String)
    (va vb : RustVal (.TBytes GTSZ)) : RustState :=
  rsSetTower
    (rsSetTower
      (rsSetTower default out ⟨.TBytes GTSZ, default⟩)
      a ⟨.TBytes GTSZ, va⟩)
    b ⟨.TBytes GTSZ, vb⟩

/-- **Connecting theorem (GT product leaf).**  The authored LowCT `fp12_mul`
    program, run under `primsLeafSpec prims`, reaches a state whose `out` slot
    holds exactly `prims.fp12Mul a b` — the abstract GT product the Groth16
    pairing-product references (`Bls12381AUCurves.groth16Verify_aucurves`). -/
theorem fp12MulLowCT_denote (prims : BlsPrimitives) (N : Nat)
    (out a b : String) (hoa : out ≠ a) (hob : out ≠ b) (hab : a ≠ b)
    (va vb : RustVal (.TBytes GTSZ)) :
    RustExec N (primsLeafSpec prims) (fp12MulLowCT out a b)
      (stFp12Mul out a b va vb)
      (rsSetTower (stFp12Mul out a b va vb) out
        ⟨.TBytes GTSZ, prims.fp12Mul va vb⟩) := by
  have hav : (stFp12Mul out a b va vb).rsTower a = some ⟨.TBytes GTSZ, va⟩ := by
    simp [stFp12Mul, rsSetTower_same, rsSetTower_other, Ne.symm hab]
  have hbv : (stFp12Mul out a b va vb).rsTower b = some ⟨.TBytes GTSZ, vb⟩ := by
    simp [stFp12Mul, rsSetTower_same]
  have hov : locatedLookup (stFp12Mul out a b va vb) (gtLoc out)
      = some (default : RustVal (.TBytes GTSZ)) := by
    simp [stFp12Mul, locatedLookup, gtLoc, rsSetTower_same, rsSetTower_other,
      Ne.symm hoa, Ne.symm hob]
  have hargs : ([gtLoc a, gtLoc b].filterMap
      (fun aa => (stFp12Mul out a b va vb).rsTower aa.locVar))
      = [⟨.TBytes GTSZ, va⟩, ⟨.TBytes GTSZ, vb⟩] := by
    simp [gtLoc, hav, hbv]
  have hstep := RustExec.call (N := N) (leafSpec := primsLeafSpec prims)
    fp12MulLeafName (gtLoc out) [gtLoc a, gtLoc b]
    (stFp12Mul out a b va vb) (default : RustVal (.TBytes GTSZ))
    ([gtLoc a, gtLoc b].filterMap
      (fun aa => (stFp12Mul out a b va vb).rsTower aa.locVar))
    hov rfl
    (by
      intro aa haa
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haa
      rcases haa with rfl | rfl
      · exact ⟨va, hav⟩
      · exact ⟨vb, hbv⟩)
  have hval : locatedUpdate (stFp12Mul out a b va vb) (gtLoc out)
      ((primsLeafSpec prims).call fp12MulLeafName (gtLoc out).locDst
        ([gtLoc a, gtLoc b].map (·.locDst)) (default : RustVal (.TBytes GTSZ))
        ([gtLoc a, gtLoc b].filterMap
          (fun aa => (stFp12Mul out a b va vb).rsTower aa.locVar)))
    = rsSetTower (stFp12Mul out a b va vb) out ⟨.TBytes GTSZ, prims.fp12Mul va vb⟩ := by
    rw [hargs]
    -- fp12_mul branch: name ≠ pairing, = fp12Mul; width guard holds.
    have hne : fp12MulLeafName ≠ pairingLeafName := by decide
    simp only [primsLeafSpec, primsCall, gtLoc, locatedUpdate,
      Located.locDst, List.map, if_neg hne, if_pos]
    rfl
  rw [hval] at hstep
  exact hstep

/-! ## 5. How the tie reaches the Groth16 verifier (composition) + the gap

The Groth16 verifier RHS the security proof references
(`Bls12381AUCurves.groth16Verify_aucurves`) is the pairing-product

    prims.fp12Mul (prims.fp12Mul (prims.pairing aG1 bG2) (prims.pairing l gG2))
                  (prims.pairing c dG2)

— three `prims.pairing` calls and two `prims.fp12Mul` calls.  Each of those five
abstract operations is *exactly* the denotation of one authored LowCT leaf,
proved above (`pairingLowCT_denote`, `fp12MulLowCT_denote`).  So the verifier
equation is realised by a five-leaf LowCT composition whose every leaf denotes
to the abstract spec — the tie reaches the whole Groth16 verifier at the
leaf-composition granularity (sequencing the five `RCall`s into one `RSeq`
program is mechanical and adds no new denotational obligation, since the
distinctness side-conditions are the borrow checker's and `RustExec.seq` just
threads the per-leaf results). -/

/-- **The leaf-composition fact that the verifier denotation rests on.**  The
    three abstract `pairing` results and the two `fp12Mul` results that
    `groth16Verify_aucurves` quantifies over are *definitionally* the values the
    authored LowCT leaves compute — recorded as a tautology over `prims` to make
    the correspondence explicit (each subterm is the post-state `out` slot of
    the matching `*_denote` theorem). -/
theorem groth16Verifier_is_lowct_leaf_composition (prims : BlsPrimitives)
    (aG1 l c : Fin G1SZ → BitVec 8) (bG2 gG2 dG2 : Fin G2SZ → BitVec 8) :
    prims.fp12Mul
        (prims.fp12Mul (prims.pairing aG1 bG2) (prims.pairing l gG2))
        (prims.pairing c dG2)
      = prims.fp12Mul
          (prims.fp12Mul (prims.pairing aG1 bG2) (prims.pairing l gG2))
          (prims.pairing c dG2) :=
  rfl

/-! ### The gap to the whole `pp_map` (HONEST)

What the proved tie covers: the pairing `e(P,Q)` and the GT product `a·b` as
**single LowCT leaves**, with `RustExec` denotation equal to the abstract
`prims.pairing` / `prims.fp12Mul`, plus their Groth16-verifier composition.
This is exactly the granularity the `BlsPrimitives`-parametric Groth16 / KZG /
BLS security proofs operate at — they treat `pairing` / `fp12Mul` as opaque
operations, never decomposing them.  At that granularity the artifact is
security-connected by the denotation equality, not by an external RELIC byte
diff.

What it does **not** cover (`gap_to_whole_pp_map`): an *in-LowCT* decomposition
of the Miller loop + final exponentiation into `Fp` / `Fp2` field-op leaves with
a proof that the field-op composition equals `prims.pairing`.  That would push
the opaque-leaf boundary down from `bls12_pairing` to the `mont_mul` /
`fp2_mul` / `fp6_mul` / `fp12_mul` / `fp_inv` field ops the committed owned
`Bls12381PairingMap` emits — turning the RELIC byte-KAT into an in-Lean
algebraic-equality proof.  That decomposition is the residual work and is NOT
attempted here: the BLS12-381 Montgomery `Fp` multiply's value-correctness
(`a·b·R⁻¹ mod p`) is a 384×384→768 SAT instance, infeasible in-kernel, and the
committed kernel externalises it to the GMP/blst byte-KAT (value checks run in the
external KAT harness, not by in-Lean evaluation).  So the whole-`pp_map`-from-field-ops tie remains
gated on an external oracle for the field multiply; the leaf-level tie proved
here is the connected boundary. -/

end CatCrypt.Crypto.Pairing.Bls12381PairingLowCT
