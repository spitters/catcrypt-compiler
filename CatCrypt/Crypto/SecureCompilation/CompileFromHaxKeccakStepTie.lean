/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
public meta import CatCrypt.Crypto.Primitives.Keccak
public import CatCrypt.Crypto.Primitives.Keccak

/-!
# Direct functional ties — Keccak ι and ρ compile-from-hax leaves = FIPS-202 steps

This module is the **ι / ρ** companion to `CompileFromHaxSha2KeccakTie` (which ties the
Keccak χ and θ leaves). It wires two committed **compile-from-hax Keccak leaves**

* `CompileFromHaxKeccak.iotaLane_compiles` — the ι round-constant XOR on lane `(0,0)`;
* `CompileFromHaxKeccak.rhoLane_compiles` — the ρ lane rotation on lane `(0,1)`;

onto the **abstract FIPS-202 step functions** the rest of CatCrypt reasons over:

* Keccak ι → `CatCrypt.Crypto.Primitives.Keccak.iota a (roundConstant 0)` at cell `(0,0)`;
* Keccak ρ → `CatCrypt.Crypto.Primitives.Keccak.rho a` at cell `(0,1)`.

## What this is — and what it is NOT

This is a **functional-equality** tie, not a security claim.

- Each compile-from-hax leaf proves a *functional-correctness* fact: the artifact emitted
  by the verified compiler computes a closed-form bit-twiddling reference
  (`prog.denote … = a ⊕ 1` for ι, `prog.denote … = a.rotateRight 28` for ρ).
- This file transports each such denotation onto the **named abstract FIPS-202 step
  function** in `Primitives.Keccak`, so that "what the verified compiler emits" is
  literally "the FIPS-202 step the spec layer is written against", at the modeled cell.
- It does **NOT** establish collision-resistance, PRF, or any SHA-3 security property of
  the emitted code. Keccak is an unkeyed permutation; there is no CR/PRF claim here, only
  `<emit-form> = <FIPS-202 step fn>` at the modeled lane.

## Granularity (per-cell)

The committed leaves are **single-lane**: ι is modeled on lane `(0,0)` (the only lane ι
touches, with the first round constant `RC₀ = roundConstant 0 = 1`), ρ on lane `(0,1)`
(rotation offset `36`). Accordingly the ties below are **per-cell**:

* `iotaLane_emitted_eq_spec` ties the ι leaf to `Keccak.iota a (roundConstant 0)` evaluated
  at `(0,0)`, where the `if x==0 && y==0` guard fires and the step is `a 0 0 ⊕ RC₀`.
* `rhoLane_emitted_eq_spec` ties the ρ leaf to `Keccak.rho a` evaluated at `(0,1)`, where
  the rotation offset is `rotOffset 0 1 = 36` and `rotl64(·, 36) = rotateRight 28` (width 64).

The full ι step touches only lane `(0,0)` per round (other lanes are the identity), and the
per-round constant varies (`roundConstant r`); the full ρ step rotates every lane by its own
`rotOffset x y`. Neither full step is committed as a single compile-from-hax leaf, so no
whole-step functional tie is claimed — the modeled lanes scale by replication (ρ) / round
(ι), as documented in the leaf file.

## Round-constant / offset notes

* `roundConstant 0 = 1` (FIPS-202 RC₀ = `0x0000000000000001`); the ι leaf hard-codes this
  first constant as the materialized register `RC₀ = 1`. Later rounds use a different
  `roundConstant r`; this tie is for round 0.
* `rotOffset 0 1 = 36` (FIPS-202 ρ offset table); on width 64 left-rotate by 36 equals
  right-rotate by `64 − 36 = 28` (`rotateLeft_36_eq_rotateRight_28`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccakStepTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  Keccak ι: the leaf form is the FIPS-202 ι step at cell `(0,0)` -/

/-- `roundConstant 0 = 1` — the first FIPS-202 round constant `RC₀`. The ι leaf
    materializes this as `RC₀ = (1 : BitVec 64)`. -/
theorem roundConstant_zero : CatCrypt.Crypto.Primitives.Keccak.roundConstant 0 = (1 : BitVec 64) := by
  native_decide

/-- **`Primitives.Keccak.iota` at cell `(0,0)` is the round-constant XOR.** With the
    first constant `RC₀ = roundConstant 0 = 1`, the ι step at the only lane it touches,
    `(0,0)`, is `a 0 0 ⊕ 1`. -/
theorem iota_spec_at_00 (a : CatCrypt.Crypto.Primitives.Keccak.KState) :
    CatCrypt.Crypto.Primitives.Keccak.iota a (CatCrypt.Crypto.Primitives.Keccak.roundConstant 0) 0 0
      = a 0 0 ^^^ (1 : BitVec 64) := by
  rw [roundConstant_zero]
  unfold CatCrypt.Crypto.Primitives.Keccak.iota
  simp

/-- **Keccak ι lane emitted by the verified compiler = the FIPS-202 ι step at cell `(0,0)`.**
    The verified compiler emits a program `c` with `compileFromHax ["a"] iotaSrc = some c`,
    and for every lane value `a₀₀`, feeding it as the `(0,0)` lane makes `c`'s `BitVec 64`
    denotation equal `Keccak.iota a (roundConstant 0)` evaluated at `(0,0)` — for every
    state `a` whose `(0,0)` cell is `a₀₀`. Functional equality at the modeled cell, NOT a
    security claim. -/
theorem iotaLane_emitted_eq_spec :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] iotaSrc = some c ∧
      ∀ (a : CatCrypt.Crypto.Primitives.Keccak.KState),
        c.denote (inputValuation 64 1 ![a 0 0])
          = CatCrypt.Crypto.Primitives.Keccak.iota a
              (CatCrypt.Crypto.Primitives.Keccak.roundConstant 0) 0 0 := by
  obtain ⟨c, hc, hden⟩ := iotaLane_compiles
  exact ⟨c, hc, fun a => (hden (a 0 0)).trans (iota_spec_at_00 a).symm⟩

/-! ## §2  Keccak ρ: the leaf form is the FIPS-202 ρ step at cell `(0,1)` -/

/-- `rotateLeft 36 = rotateRight 28` on `BitVec 64` — the width-64 identity that matches the
    ρ leaf's `rotateRight 28` against `rho`'s `rotateLeft (rotOffset 0 1)`. Pure `BitVec 64`
    fact (`rotOffset 0 1 = 36`, `64 − 36 = 28`). -/
theorem rotateLeft_36_eq_rotateRight_28 (x : BitVec 64) :
    x.rotateLeft 36 = x.rotateRight 28 := by bv_decide

/-- **`Primitives.Keccak.rho` at cell `(0,1)` is `rotateRight 28`.** Lane `(0,1)` has
    rotation offset `rotOffset 0 1 = 36`, so the ρ step there is `rotl64(a 0 1, 36)`,
    which on width 64 equals `(a 0 1).rotateRight 28`. -/
theorem rho_spec_at_01 (a : CatCrypt.Crypto.Primitives.Keccak.KState) :
    CatCrypt.Crypto.Primitives.Keccak.rho a 0 1 = (a 0 1).rotateRight 28 := by
  unfold CatCrypt.Crypto.Primitives.Keccak.rho
  rw [show CatCrypt.Crypto.Primitives.Keccak.rotOffset 0 1 = 36 from by native_decide,
    rotateLeft_36_eq_rotateRight_28]

/-- **Keccak ρ lane emitted by the verified compiler = the FIPS-202 ρ step at cell `(0,1)`.**
    The verified compiler emits a program `c` with `compileFromHax ["a"] rhoLaneSrc = some c`,
    and for every lane value `a₀₁`, feeding it as the `(0,1)` lane makes `c`'s `BitVec 64`
    denotation equal `Keccak.rho a` evaluated at `(0,1)` — for every state `a` whose `(0,1)`
    cell is `a₀₁`. Functional equality at the modeled cell, NOT a security claim. -/
theorem rhoLane_emitted_eq_spec :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["a"] rhoLaneSrc = some c ∧
      ∀ (a : CatCrypt.Crypto.Primitives.Keccak.KState),
        c.denote (inputValuation 64 1 ![a 0 1])
          = CatCrypt.Crypto.Primitives.Keccak.rho a 0 1 := by
  obtain ⟨c, hc, hden⟩ := rhoLane_compiles
  exact ⟨c, hc, fun a => (hden (a 0 1)).trans (rho_spec_at_01 a).symm⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccakStepTie
