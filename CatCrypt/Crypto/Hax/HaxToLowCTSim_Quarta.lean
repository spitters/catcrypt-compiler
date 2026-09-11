/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Call
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main

/-!
# H3.quarta: Tower-typed agreement framework

Extends the simulation theorem with tower-typed agreement, unblocking
the four `Hyp_*` parameters in `HaxToLowCTSim_Main.lean`.

## What this file adds

* **`ValueTowerBridge`**: a per-protocol relation linking Hax `Value`s
  to LowCT `RustVal dt` instances.  Parametric so each protocol
  populates its own concrete bridge (e.g., one for BLS12-381, one for
  Curve25519).
* **`nameAgreesTower`, `envAgreesRustTower`**: the per-name and
  whole-env tower-binding agreement predicates, parameterised by the
  bridge.
* **`envAgreesRustFull`**: combined scalar + tower agreement.
* **Agreement-extension lemmas**: `envAgreesRust*_extend_tower` (the
  tower-update analogue of `envAgreesRust_extend_scalar` from
  `HaxToLowCTSim_Agreement.lean`).
* **`LeafCallAgreesTower`**: the tower-typed analogue of
  `LeafCallAgrees` from `HaxToLowCTSim_Call.lean`.

## What the per-protocol bridge looks like

For BLS12-381 (Fp arithmetic) the bridge might be:

```lean
-- Bridge: a Hax Value `tuple [int a0, int a1, ...]` agrees with a
-- RustVal TFp iff the byte-decoded RustVal equals the limb-decoded
-- Hax tuple.  Per-leaf instances of `LeafCallAgreesTower` for
-- `fp_add`, `fp_mul`, etc. then ground out via the existing
-- `leafSpec.call` semantics.
def blsValueTowerBridge : Value → (dt : TowerType) → RustVal dt → Prop := ...
```

The bridge is **deliberately parametric**: closing the framework here
doesn't require committing to a single concrete encoding.  Per-leaf
agreement instances supply the concrete decoding per primitive.

## H3.quarta closure path

1. **This file** — landed: framework + structural lemmas.
2. **`HaxToLowCTSim_Quarta_LeafAgrees.lean`** (next agent) — per-leaf
   `LeafCallAgreesTower` instances for the haxToLowCT-whitelisted
   leaves (`fp_*`, `fp25519_*`, `scalar25519_*`, `fpP256_*`, `u64_*`).
3. **`HaxToLowCTSim_Quarta_Discharge.lean`** (next agent) — discharge
   `Hyp_letBindApp` and `Hyp_assignApp` from this file's framework +
   the per-leaf instances.

The other two `Hyp_*` (Hyp_match, Hyp_whileLoop) need separate work
(H2.1 tuple-destructure mechanics for match; fuel-polymorphic IH +
`AnfShaped` syntactic lemma for whileLoop).  Out of scope for this
file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  Value-tower bridge

The bridge is a per-protocol relation. -/

/-- `ValueTowerBridge eq` packages a relation `eq : ∀ dt, Value → RustVal dt → Prop`
    that says "Hax Value `v` and RustVal of tower type `dt` represent the
    same logical value".  Per-protocol instances (BLS, Curve25519, etc.)
    populate this. -/
def ValueTowerBridge : Type :=
  ∀ (dt : TowerType), Value → RustVal dt → Prop

/-! ## §2  Tower-binding agreement

Per-name and whole-env, parameterised by a bridge. -/

/-- Agreement on a single name for tower bindings.  If env has a value
    `v` for `name` AND rs has a tower binding `⟨dt, val⟩` for `name`,
    they agree iff the bridge relates them. -/
def nameAgreesTower (bridge : ValueTowerBridge)
    (env : Env) (rs : RustState) (name : String) : Prop :=
  ∀ v, env name = some v →
    ∀ (dt : TowerType) (val : RustVal dt),
      rs.rsTower name = some ⟨dt, val⟩ →
      bridge dt v val

/-- Top-level tower agreement: all names with tower bindings agree. -/
def envAgreesRustTower (bridge : ValueTowerBridge)
    (env : Env) (rs : RustState) : Prop :=
  ∀ name, nameAgreesTower bridge env rs name

/-! ## §3  Combined agreement (scalar ∧ tower) -/

/-- Combined agreement.  Required for the leaf-call simulation cases. -/
def envAgreesRustFull (bridge : ValueTowerBridge)
    (env : Env) (rs : RustState) : Prop :=
  envAgreesRust env rs ∧ envAgreesRustTower bridge env rs

/-! ## §4  Agreement-extension lemmas (tower) -/

/-- Tower-binding extension: if env and rs agree under bridge, and we
    extend env with `v` at `name` AND update rs's tower binding at
    `name` with `⟨dt, val⟩` where `bridge dt v val`, agreement is
    preserved. -/
theorem envAgreesRustTower_extend_tower
    (bridge : ValueTowerBridge)
    (env : Env) (rs : RustState) (name : String) (v : Value)
    (dt : TowerType) (val : RustVal dt)
    (hAgree : envAgreesRustTower bridge env rs)
    (hBridge : bridge dt v val) :
    envAgreesRustTower bridge (Env.extend env name v) (rsSetTower rs name ⟨dt, val⟩) := by
  intro m
  unfold nameAgreesTower
  intro v' hExt dt' val' hLookup
  by_cases hm : m = name
  · -- m = name: Env.extend returns v, rsSetTower returns ⟨dt, val⟩
    subst hm
    -- hExt : (Env.extend env m v) m = some v'
    -- After rewriting with Env.extend's matching case, v' = v
    simp [Env.extend] at hExt
    subst hExt
    -- hLookup : (rsSetTower rs m ⟨dt, val⟩).rsTower m = some ⟨dt', val'⟩
    simp [rsSetTower] at hLookup
    -- hLookup decomposes ⟨dt, val⟩ = ⟨dt', val'⟩, hence dt = dt' and val (after transport) = val'.
    -- Sigma equality: ⟨dt, val⟩ = ⟨dt', val'⟩ ↔ ∃ h : dt = dt', h ▸ val = val'.
    obtain ⟨hdt, hval⟩ := hLookup
    subst hdt
    -- hval : val = val' (after dt = dt' substitution)
    simp at hval
    subst hval
    exact hBridge
  · -- m ≠ name: both reduce to env m and rs.rsTower m
    have hEnvFall : Env.extend env name v m = env m := by
      simp [Env.extend, hm]
    have hRsFall : (rsSetTower rs name ⟨dt, val⟩).rsTower m = rs.rsTower m := by
      simp [rsSetTower]; intro hContra; exact absurd hContra hm
    rw [hEnvFall] at hExt
    rw [hRsFall] at hLookup
    exact hAgree m v' hExt dt' val' hLookup

/-- Scalar agreement preserved under tower update (the tower update
    doesn't touch `rsScalar`).  Companion to the existing
    `envAgreesRust_extend_scalar`. -/
theorem envAgreesRust_preserved_under_tower
    (env : Env) (rs : RustState) (name : String) (v : Value)
    (dt : TowerType) (val : RustVal dt)
    (hAgree : envAgreesRust env rs)
    (hDecode : valueToScalar v = none) :
    envAgreesRust (Env.extend env name v) (rsSetTower rs name ⟨dt, val⟩) := by
  intro m
  unfold nameAgreesScalar
  intro v' hExt n hScalar
  -- rsSetTower doesn't change rsScalar
  have hRs : (rsSetTower rs name ⟨dt, val⟩).rsScalar m = rs.rsScalar m := by
    simp [rsSetTower]
  rw [hRs]
  by_cases hm : m = name
  · -- m = name: env.extend returns v; valueToScalar v = none contradicts hScalar
    subst hm
    simp [Env.extend] at hExt
    subst hExt
    rw [hDecode] at hScalar
    cases hScalar
  · have hEnvFall : Env.extend env name v m = env m := by
      simp [Env.extend, hm]
    rw [hEnvFall] at hExt
    exact hAgree m v' hExt n hScalar

/-- Combined-agreement extension under tower update.  Requires
    `valueToScalar v = none` (the value is a tower-typed value, not a
    scalar) — this is the typical shape for a leaf-call result that
    populates a tower binding. -/
theorem envAgreesRustFull_extend_tower
    (bridge : ValueTowerBridge)
    (env : Env) (rs : RustState) (name : String) (v : Value)
    (dt : TowerType) (val : RustVal dt)
    (hAgree : envAgreesRustFull bridge env rs)
    (hBridge : bridge dt v val)
    (hDecode : valueToScalar v = none) :
    envAgreesRustFull bridge (Env.extend env name v) (rsSetTower rs name ⟨dt, val⟩) :=
  ⟨envAgreesRust_preserved_under_tower env rs name v dt val hAgree.1 hDecode,
   envAgreesRustTower_extend_tower bridge env rs name v dt val hAgree.2 hBridge⟩

/-! ## §5  `LeafCallAgreesTower`

The tower-typed analogue of `LeafCallAgrees` (from
`HaxToLowCTSim_Call.lean`).  Given a per-leaf bridge agreement, a
successful Builtins call produces a value related to the leaf's RustVal
output via the bridge. -/

/-- Per-leaf tower-agreement predicate.  Given a leaf `f` with
    destination type `dt`, the LeafSpec.run is bridge-aligned with the
    Builtins-side call's output. -/
def LeafCallAgreesTower
    (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (bridge : ValueTowerBridge) : Prop :=
  ∀ (rs : RustState) (dest : String) (args : List Located)
    (vals : List Value) (vRes : Value),
    bi f vals = some vRes →
    (∀ a ∈ args, ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩) →
    let oldDestV := (locatedLookup rs { locVar := dest, locSrc := dt }).getD default
    let argList := args.filterMap (fun a => rs.rsTower a.locVar)
    let newVal := leafSpec.call f dt (args.map (·.locDst)) oldDestV argList
    bridge dt vRes newVal

/-! ## §6  Summary

This file lands the framework:

* Bridge type and per-protocol slot — `ValueTowerBridge`
* Predicates — `nameAgreesTower`, `envAgreesRustTower`, `envAgreesRustFull`
* Extension lemmas — `envAgreesRustTower_extend_tower`,
  `envAgreesRust_preserved_under_tower`, `envAgreesRustFull_extend_tower`
* Leaf-agreement predicate — `LeafCallAgreesTower`

**Build status**: 0 sorries, 0 axioms, 0 warnings.

The two next steps (in separate files):

* `HaxToLowCTSim_Quarta_LeafAgrees.lean` — populate
  `LeafCallAgreesTower` for the haxToLowCT-whitelisted leaves.
* `HaxToLowCTSim_Quarta_Discharge.lean` — discharge `Hyp_letBindApp`
  and `Hyp_assignApp` from `HaxToLowCTSim_Main.lean` using the
  framework + leaf instances.  The discharge requires extending the
  simulation predicate to use `envAgreesRustFull`; we'll either
  refactor `HaxToLowCTSimulates` (invasive) or define a stronger
  parallel predicate `HaxToLowCTSimulatesFull`.
-/

end CatCrypt.Crypto.Hax
