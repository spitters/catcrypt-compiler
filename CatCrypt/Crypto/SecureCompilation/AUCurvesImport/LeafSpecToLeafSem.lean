/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AUCurvesImport.FieldLeafBridge
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# `LeafSpec ⇒ LeafSem` lift: carrying the AUCurves field-mul byte-edge to the VIR denotes

`AUCurvesImport.FieldLeafBridge` (`AUCurvesFieldMulBridge` /
`fieldMul_value_of_bridge`) states the AUCurves-Rocq-proved byte-Montgomery
field-multiply correctness at the **LowCT `LeafSpec` layer**: the CatCrypt
`leafSpec.call` oracle applied to two field-element slots (`RustVal leaf.dt`)
decodes to the field product `leaf.decode xa * leaf.decode xb` in
`ZMod leaf.modulus`.

The pairing / group **denote** files (`Pairing/*Denote.lean`,
`FieldLeafBridge_BLS_BN254.lean`) instead evaluate at the VIR **`LeafSem` layer**:
a leaf oracle
`LeafSem = (name) (argTys) (retTy) → HVector ⟦·⟧ argTys → ⟦retTy⟧`, whose
field-element carrier is `⟦.stackArr 8 n⟧`.  `FieldLeafBridge_BLS_BN254`'s module
header records the missing glue precisely (its `fp_mul` `leaf_computes` theorems
close the *`FieldLeafAgrees`* edge but leave the *deeper byte-Montgomery
realization* — the AUCurves fact — as a named residual, because it lives at the
LowCT `LeafSpec` layer, "not the VIR `LeafSem` layer these denote files use").

This module supplies that glue.  The two layers turn out to share the **same**
byte carrier:

* LowCT: `RustVal (.TBytes n) = JArray (TowerType.storageBytes (.TBytes n))`
  `= JArray n = Fin n → BitVec 8`.
* VIR:   `⟦.stackArr 8 n⟧ = Fin n → BitVec 8` (the reducible `TyDenote JasminTy`).

So the `reify`/`embed` between them is the **identity** (a definitional cast, not
an axiomatized encoding) — `§1`.  The lift lemma (`§3`) then carries the LowCT
byte-Montgomery fact through to a VIR `LeafSem` `fp_mul` agreement **by proof**,
consuming two named hypotheses:

1. `AUCurvesFieldMulBridge leaf leafSpec` — the AUCurves cross-prover byte edge
   (already a named, non-vacuous assumption in `FieldLeafBridge.lean`);
2. `LeafSemMulAgreesSpec … leafSem leafSpec` — the **cross-layer carrier
   agreement**: the VIR `leafSem`'s value on the `fp_mul` triple equals the
   LowCT `leafSpec.call` value on the same bytes.  Because both carriers are the
   *same* `Fin n → BitVec 8` type, this is a plain equality of two oracle values
   — the honest statement that one emitted kernel realizes both oracles — not an
   encoding axiom.  `§2` gives a non-vacuous witness (a `leafSem` literally
   routed through `leafSpec.call`), confirming the hypothesis is satisfiable.

No new `axiom` is introduced: the `fp_mul` byte edge is closed to a **proof**
modulo the two already-named cross-prover / cross-layer assumptions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AUCurvesImport.LeafSpecToLeafSem

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.AUCurvesImport

/-- The VIR leaf-semantics carrier — the exact shape of `jasminExtSem` /
    `BN254GroupEmit.LeafSem`. -/
abbrev LeafSem : Type :=
  (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧

/-! ## §1  reify / embed between the VIR and LowCT byte carriers

Both the VIR `⟦.stackArr 8 n⟧` and the LowCT `RustVal (.TBytes n)` unfold to
`Fin n → BitVec 8`, so the two maps are the identity and both round-trips hold
by `rfl`.  We name them so the correspondence is explicit rather than implicit. -/

/-- **embed**: a VIR stack-array byte value (`⟦.stackArr 8 n⟧ = Fin n → BitVec 8`)
    read as a LowCT `RustVal (.TBytes n)` (`= JArray n = Fin n → BitVec 8`). -/
@[reducible] def vsemToRustVal {n : Nat} (v : Fin n → BitVec 8) :
    RustVal (.TBytes n) := v

/-- **reify**: a LowCT `RustVal (.TBytes n)` read as a VIR stack-array byte
    value. -/
@[reducible] def rustValToVsem {n : Nat} (r : RustVal (.TBytes n)) :
    Fin n → BitVec 8 := r

/-- Round-trip: reify after embed is the identity (both maps are the definitional
    identity on `Fin n → BitVec 8`). -/
theorem rustValToVsem_vsemToRustVal {n : Nat} (v : Fin n → BitVec 8) :
    rustValToVsem (vsemToRustVal v) = v := rfl

/-- Round-trip: embed after reify is the identity. -/
theorem vsemToRustVal_rustValToVsem {n : Nat} (r : RustVal (.TBytes n)) :
    vsemToRustVal (rustValToVsem r) = r := rfl

/-! ## §2  The cross-layer carrier-agreement predicate + a non-vacuous witness -/

/-- Package a byte-carrier (`.TBytes n`) field-mul leaf for the AUCurves bridge:
    `dt := .TBytes n`, so `RustVal leaf.dt = Fin n → BitVec 8` matches the VIR
    `⟦.stackArr 8 n⟧` carrier exactly. -/
def mkBytesLeaf (fname : String) (n p : Nat)
    (decode : RustVal (.TBytes n) → ZMod p) : FieldMulLeaf where
  fname   := fname
  dt      := .TBytes n
  modulus := p
  decode  := decode

/-- **Cross-layer carrier agreement.**  The VIR `leafSem` value on the `fp_mul`
    triple `(mulName, [stackArr 8 n, stackArr 8 n], stackArr 8 n)` equals the
    LowCT `leafSpec.call` value on the same two bytes at `.TBytes n`.  Both sides
    inhabit the identical `Fin n → BitVec 8` carrier, so this is a plain oracle
    equality — the honest statement that a single emitted kernel realizes both
    the VIR `LeafSem` oracle and the LowCT `LeafSpec.call` oracle for this
    leaf. -/
def LeafSemMulAgreesSpec (n : Nat) (mulName fname : String)
    (leafSpec : LeafSpec) (oldDest : RustVal (.TBytes n)) (leafSem : LeafSem) :
    Prop :=
  ∀ (a b : Fin n → BitVec 8),
    leafSem mulName [.stackArr 8 n, .stackArr 8 n] (.stackArr 8 n)
        (.cons a (.cons b .nil))
      = leafSpec.call fname (.TBytes n) [.TBytes n, .TBytes n] oldDest
          [⟨.TBytes n, a⟩, ⟨.TBytes n, b⟩]

/-- **Canonical realizer of the carrier agreement.**  The VIR `leafSem` obtained
    by routing the `fp_mul` triple straight through `leafSpec.call` (identity
    reify/embed) and defaulting off-target.  This confirms
    `LeafSemMulAgreesSpec` is *satisfiable* — an inhabited cross-layer edge, not
    an unsatisfiable over-constraint — mirroring `FieldLeafBridge`'s
    `fieldMulCallSpec` non-vacuity discipline. -/
def carrierLeafSem (n : Nat) (mulName fname : String)
    (leafSpec : LeafSpec) (oldDest : RustVal (.TBytes n)) : LeafSem :=
  fun name argTys retTy args =>
    if h : name = mulName ∧ argTys = [.stackArr 8 n, .stackArr 8 n]
              ∧ retTy = .stackArr 8 n then
      h.2.2 ▸ (leafSpec.call fname (.TBytes n) [.TBytes n, .TBytes n] oldDest
        [⟨.TBytes n, (h.2.1 ▸ args).head⟩, ⟨.TBytes n, (h.2.1 ▸ args).tail.head⟩])
    else JasminTy.default retTy

/-- The canonical realizer satisfies the carrier agreement — `LeafSemMulAgreesSpec`
    is non-vacuous. -/
theorem carrierLeafSem_agrees (n : Nat) (mulName fname : String)
    (leafSpec : LeafSpec) (oldDest : RustVal (.TBytes n)) :
    LeafSemMulAgreesSpec n mulName fname leafSpec oldDest
      (carrierLeafSem n mulName fname leafSpec oldDest) := by
  intro a b
  simp only [carrierLeafSem]
  exact dif_pos ⟨rfl, rfl, rfl⟩

/-! ## §3  The lift lemma: LowCT `LeafSpec` byte-edge ⇒ VIR `LeafSem` `fp_mul`

Consuming (1) the AUCurves byte-Montgomery bridge at the `LeafSpec` layer and (2)
the cross-layer carrier agreement, the VIR `LeafSem` `fp_mul` value decodes to
the field product `decode a * decode b`.  This is the residual named in
`FieldLeafBridge_BLS_BN254`'s header, discharged **by proof** — no new axiom. -/

/-- **The `LeafSpec ⇒ LeafSem` field-mul lift.**  For a `.TBytes n` field-mul
    leaf, given the AUCurves byte-Montgomery bridge (`AUCurvesFieldMulBridge`, at
    the LowCT `LeafSpec` layer) and the cross-layer carrier agreement
    (`LeafSemMulAgreesSpec`), the VIR `LeafSem` `fp_mul` value decodes to the
    field product — carrying the byte edge onto the VIR carrier the denote files
    use. -/
theorem leafSem_fp_mul_of_bridge
    {n p : Nat} {mulName fname : String} {leafSpec : LeafSpec} {leafSem : LeafSem}
    {oldDest : RustVal (.TBytes n)} {decode : RustVal (.TBytes n) → ZMod p}
    (hbridge : AUCurvesFieldMulBridge (mkBytesLeaf fname n p decode) leafSpec)
    (hcarrier : LeafSemMulAgreesSpec n mulName fname leafSpec oldDest leafSem)
    (a b : Fin n → BitVec 8) :
    decode (leafSem mulName [.stackArr 8 n, .stackArr 8 n] (.stackArr 8 n)
              (.cons a (.cons b .nil)))
      = decode a * decode b := by
  rw [hcarrier a b]
  exact fieldMul_value_of_bridge hbridge a b oldDest

/-- **Pointful corollary** matching the header's requested lift shape: the
    composite `decode ∘ leafSem …` on the `fp_mul` triple sends `(a, b)` to the
    field product. -/
theorem leafSem_fp_mul_comp_of_bridge
    {n p : Nat} {mulName fname : String} {leafSpec : LeafSpec} {leafSem : LeafSem}
    {oldDest : RustVal (.TBytes n)} {decode : RustVal (.TBytes n) → ZMod p}
    (hbridge : AUCurvesFieldMulBridge (mkBytesLeaf fname n p decode) leafSpec)
    (hcarrier : LeafSemMulAgreesSpec n mulName fname leafSpec oldDest leafSem) :
    (fun ab : (Fin n → BitVec 8) × (Fin n → BitVec 8) =>
        decode (leafSem mulName [.stackArr 8 n, .stackArr 8 n] (.stackArr 8 n)
                  (.cons ab.1 (.cons ab.2 .nil))))
      = fun ab => decode ab.1 * decode ab.2 := by
  funext ab
  exact leafSem_fp_mul_of_bridge hbridge hcarrier ab.1 ab.2

end CatCrypt.Crypto.SecureCompilation.AUCurvesImport.LeafSpecToLeafSem
