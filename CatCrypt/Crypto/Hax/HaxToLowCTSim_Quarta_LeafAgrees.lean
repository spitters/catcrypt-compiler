/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta

/-!
# H3.quarta-LeafAgrees: per-leaf agreement scaffolding

Provides reusable constructors for `LeafCallAgreesTower` instances.
Concrete per-leaf instances (e.g., for `fp25519_add`, `scalar25519_mul`)
are populated by per-protocol wiring; this file gives the shape.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (Value Builtins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType RustState RustExec LeafSpec Located RustVal locatedLookup)

/-! ## §1  Generic constructor for `LeafCallAgreesTower`

The constructor takes:

* a per-leaf decoder `vRes_to_rustVal : Value → RustVal dt`,
* a bridge-alignment axiom for the decoder, and
* a per-leaf agreement axiom that `leafSpec.call` matches the decoder
  whenever the Builtins side has a successful call.

These three pieces compose into a `LeafCallAgreesTower` instance.
Per-protocol populators only need to supply the decoder plus the two
axioms (typically discharged by per-leaf computation lemmas in
e.g. `libcrux-specs`). -/

/-- Given a function `vRes_to_rustVal : Value → RustVal dt` and a proof
    that the bridge always relates `vRes` to `vRes_to_rustVal vRes`
    AND a proof that `leafSpec.call` always returns `vRes_to_rustVal`,
    we can construct a `LeafCallAgreesTower` instance. -/
theorem mkLeafCallAgreesTower
    (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (bridge : ValueTowerBridge)
    (vRes_to_rustVal : Value → RustVal dt)
    (hBridge : ∀ vRes, bridge dt vRes (vRes_to_rustVal vRes))
    (hCall : ∀ (rs : RustState) (dest : String) (args : List Located)
       (vals : List Value) (vRes : Value),
       bi f vals = some vRes →
       (∀ a ∈ args, ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩) →
       leafSpec.call f dt (args.map (·.locDst))
         ((locatedLookup rs { locVar := dest, locSrc := dt }).getD default)
         (args.filterMap (fun a => rs.rsTower a.locVar))
       = vRes_to_rustVal vRes) :
    LeafCallAgreesTower bi leafSpec f dt bridge := by
  intro rs dest args vals vRes hBi hArgs
  -- Unfold the `let` bindings introduced by `LeafCallAgreesTower`.
  simp only []
  -- Apply the per-leaf call agreement to rewrite the leafSpec.call result.
  rw [hCall rs dest args vals vRes hBi hArgs]
  -- Apply the bridge-alignment axiom.
  exact hBridge vRes

/-! ## §2  Standard-leaf instance shape

For each prefix `<P>` in the haxToLowCT whitelist
(`fp12_`, `fp6_`, `fp2_`, `fp25519_`, `scalar25519_`, `fpP256_`,
`u64_`, `fp_`), an instance has the shape:

```
def <P>_add_leafAgrees (bi : Builtins) (leafSpec : LeafSpec)
    (bridge : ValueTowerBridge) :
    LeafCallAgreesTower bi leafSpec "<P>add" dt_<P> bridge :=
  mkLeafCallAgreesTower bi leafSpec "<P>add" dt_<P> bridge
    (vRes_to_rustVal := <protocol-specific decoder>)
    (hBridge := by ...)
    (hCall := by ...)
```

Per-protocol populators live in
`CatCrypt/Crypto/<Protocol>/HaxBridge.lean` (or `SurfaceDeps.lean` per
the current convention).  Each prefix maps to a unique `dt_<P>`:

| Prefix         | TowerType         | Typical leaves                |
|----------------|-------------------|-------------------------------|
| `fp12_`        | `TFp12`           | `fp12_add`, `fp12_mul`, ...   |
| `fp6_`         | `TFp6`            | `fp6_add`, `fp6_mul`, ...     |
| `fp2_`         | `TFp2`            | `fp2_add`, `fp2_mul`, ...     |
| `fp25519_`     | `TFp25519`        | `fp25519_add`, ...            |
| `scalar25519_` | `TScalar25519`    | `scalar25519_add`, ...        |
| `fpP256_`      | `TFpP256`         | `fpP256_add`, ...             |
| `u64_`         | `TU64`            | `u64_add`, ...                |
| `fp_`          | `TFp` (BLS12-381) | `fp_add`, `fp_mul`, ...       |

For each prefix, the per-leaf decoder typically reads the byte-level
encoding from the Hax `Value` and returns the appropriate `RustVal dt`.
For example, for `fp_`, the decoder might unpack a Hax tuple of limbs
and reassemble them into the byte form expected by the libcrux-specs
opaque Fp primitives.

The `hBridge` axiom is then discharged by the per-protocol definition
of the bridge (typically by `rfl` or `by simp [bridge_def, decoder]`).

The `hCall` axiom is the substantive obligation — it says the
LeafSpec.call agrees with the decoded Builtins output.  In practice
this is established by the libcrux-specs side's existing functional
equivalence proofs (e.g. `Fp.add_correct`). -/

/-! ## §3  Vacuous instance for unmatched leaves

When the Builtins table does not provide a value for `f` (i.e., the
leaf is not part of the protocol's primitive set), the
`LeafCallAgreesTower` predicate holds vacuously.  This is useful for
populating `LeafCallAgreesTower` over the full whitelist when the
protocol only uses a subset of the leaves. -/

/-- Vacuous instance: if Builtins never returns a value for `f`,
    `LeafCallAgreesTower` holds trivially. -/
theorem leafCallAgreesTower_of_unmatched
    (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (bridge : ValueTowerBridge)
    (hUnmatched : ∀ vals, bi f vals = none) :
    LeafCallAgreesTower bi leafSpec f dt bridge := by
  intro rs dest args vals vRes hBi _hArgs
  rw [hUnmatched vals] at hBi
  cases hBi

/-! ## §4  Summary

This file lands the per-leaf scaffolding:

* `mkLeafCallAgreesTower` — generic constructor from per-leaf decoder
  plus bridge-alignment and call-agreement axioms.
* `leafCallAgreesTower_of_unmatched` — vacuous instance for leaves the
  protocol does not use.

Per-protocol populators consume these via
`CatCrypt/Crypto/<Protocol>/HaxBridge.lean` (or `SurfaceDeps.lean`)
and supply the concrete decoder + axioms for each whitelisted leaf.

**Build status**: 0 sorries, 0 axioms.
-/

end CatCrypt.Crypto.Hax
