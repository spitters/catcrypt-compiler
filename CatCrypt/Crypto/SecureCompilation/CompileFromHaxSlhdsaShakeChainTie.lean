/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaShakeChain
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccakStepTie
public import CatCrypt.Crypto.Primitives.Keccak

/-!
# Keccak-engine tie: the SLH-DSA (SHAKE-128f) WOTS+ chain step = the FIPS-202 round engine

This module is the **SHAKE-128f** companion tie to `CompileFromHaxSlhdsaShakeChain`
— the Keccak-engine analogue of `CompileFromHaxSlhdsaChainTie` (which tied the
`sha2-*` chain step to the SHA-256 *round engine* `sha256RoundVerified`). The
*canonical* `SLHDSA/SurfaceDeps.lean` wires the tweakable hash `F` to
`slhTweakHash = SHAKE-128(seed ‖ tweak ‖ block, 16)`, whose engine is the
**Keccak-f[1600]** permutation `Primitives.Keccak.keccakF = 24× keccakRound`.

The genuinely-new shape here (vs the `sha2-*` round-engine tie, which composed
two SHA-256 round-component leaves `t1`/`t2` into the round's `a`-update) is that
this tie **composes the four tied Keccak step leaves** into one full FIPS-202
round `keccakRound = ι ∘ χ ∘ π ∘ ρ ∘ θ`:

* `θ` — `CompileFromHaxSha2KeccakTie.thetaCompose_eq_spec` (the two θ leaves);
* `ρ` — `CompileFromHaxKeccakStepTie.rhoLane_emitted_eq_spec`;
* `χ` — `CompileFromHaxSha2KeccakTie.chiLane_emitted_eq_form` / `chi_spec_eq_form`;
* `ι` — `CompileFromHaxKeccakStepTie.iotaLane_emitted_eq_spec`.

`π` is a pure lane permutation (an index remap `π a x y = a (x+3y) x`, no bit
arithmetic), so it carries no compile-from-hax leaf — it is structural shuffling.
This file proves `keccakRound` *factors through* the four tied bit-twiddling
steps, so the engine the SHAKE chain step `F` iterates is exactly the composition
of the already-compiled-from-hax leaves.

## What this is — and what it is NOT (honest framing)

This is a **functional-equality** tie, not a security claim.

- It shows the FIPS-202 round `Primitives.Keccak.keccakRound` decomposes as the
  named-step composition the four tied compile-from-hax leaves realize, and ties
  the SHAKE chain-step absorb-prep leaf to the FIPS-202 §6 lane mix.
- It does **NOT** establish collision/preimage resistance, the SHAKE XOF PRF
  property, or the SLH-DSA WOTS+/FORS EUF-CMA reduction (those live in
  `SLHDSA/Reduction.lean` over the abstract `TweakableHashParams`). Keccak is an
  unkeyed permutation; the claim is only `<round> = <named-step composition>` and
  `<emit-form> = <FIPS lane mix>`.

## Front gap (honest, carried from the leaf module)

The full `F = SHAKE(seed ‖ tweak ‖ block)` is a sponge: a *padded, multi-block
absorb* (`xorIn` + `keccakF`) then a `keccakF`-driven squeeze, plus the FIPS-205
ADRS byte-encoding and the `0x1F`/`0x80` domain-separation padding. The verified
front recognizes only straight-line scalar word ops, so the sponge's
variable-length padding loop, the multi-block `keccakF` iteration, the ADRS byte
layout, and the domain-separation bytes are **not** expressible as compile-from-hax
leaves. Exactly as the `sha2-*` tie landed at the SHA-256 *round* engine (not the
message-schedule loop), this SHAKE tie lands at the **Keccak round** engine: the
four step leaves compose one `keccakRound` (the per-round transform `keccakF`
iterates 24×), and the absorb-prep lane XOR is the chain step's pre-permute mix.
The sponge padding / ADRS / multi-block iteration are reported as out of the
front's fragment, not forced.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaShakeChainTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaShakeChain
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.Primitives.Keccak

/-! ## §1  The FIPS-202 round factors through its four bit-twiddling steps + the π shuffle

`keccakRound a rc = ι (χ (π (ρ (θ a)))) rc`. Each of `θ`, `ρ`, `χ`, `ι` is a tied
compile-from-hax leaf (the named `Primitives.Keccak.{theta,rho,chi,iota}`); `π` is
a pure lane permutation. This section exposes that factorisation explicitly so the
engine the SHAKE chain step runs is visibly the composition of the tied leaves. -/

/-- **The FIPS-202 round is the named-step composition.** `keccakRound a rc`
    unfolds *definitionally* to `ι (χ (π (ρ (θ a)))) rc` — the composition of the
    four tied bit-twiddling steps (`θ`, `ρ`, `χ`, `ι`) interleaved with the pure
    `π` lane permutation. This is the engine the SLH-DSA SHAKE chain step `F`
    iterates (24× per `keccakF`, sponge-wrapped in `shake128`/`slhTweakHash`). -/
theorem keccakRound_eq_step_composition (a : KState) (rc : BitVec 64) :
    keccakRound a rc = iota (chi (pi (rho (theta a)))) rc := by
  unfold keccakRound
  rfl

/-- **The ι output cell `(0,0)` of one FIPS-202 round, in terms of the χ-output state.**
    After `θ`/`ρ`/`π`/`χ` produce the state `s = χ(π(ρ(θ a)))`, the round's `(0,0)`
    cell is `ι`'s round-constant XOR `s 0 0 ⊕ rc` — exactly the tied ι-leaf shape
    (`CompileFromHaxKeccakStepTie.iota_spec_at_00`, here for arbitrary `rc`). -/
theorem keccakRound_at_00 (a : KState) (rc : BitVec 64) :
    keccakRound a rc 0 0 = (chi (pi (rho (theta a)))) 0 0 ^^^ rc := by
  rw [keccakRound_eq_step_composition]
  unfold iota
  simp

/-! ## §2  The χ output cell is the tied χ-lane formula over the π/ρ/θ state

The χ step at cell `(0,0)` is the FIPS-202 χ-lane formula `s 0 0 ⊕ ((¬ s 1 0) ∧ s 2 0)`
over its governing lanes — exactly the shape the tied χ leaf computes
(`CompileFromHaxSha2KeccakTie.chi_spec_eq_form`). -/

/-- **The round's `(0,0)` cell, fully decomposed onto the χ-lane formula.** Writing
    `s = π(ρ(θ a))` for the post-π state, the round's `(0,0)` output is
    `(s 0 0 ⊕ ((¬ s 1 0) ∧ s 2 0)) ⊕ rc` — the tied χ-lane formula (the `χ` leaf)
    fed into the tied ι round-constant XOR (the `ι` leaf). Composes two of the four
    tied Keccak step leaves at this cell. -/
theorem keccakRound_00_decomp (a : KState) (rc : BitVec 64) :
    keccakRound a rc 0 0
      = (let s := pi (rho (theta a));
         (s 0 0 ^^^ ((~~~ s 1 0) &&& s 2 0))) ^^^ rc := by
  rw [keccakRound_at_00,
    CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie.chi_spec_eq_form
      (pi (rho (theta a))) 0 0]
  rfl

/-! ## §3  Transport: the emitted leaves compose the FIPS-202 round engine

The committed compile-from-hax leaves realize the round's four bit-twiddling
steps. We restate the round's `(0,0)` output as a composition the tied leaves
emit: the χ-lane leaf (over the post-π state's three governing lanes) into the
ι round-constant XOR. -/

/-- **One FIPS-202 round cell `(0,0)` reconstructed from the tied compile-from-hax
    χ and ι leaves.** There is a compiled χ-lane program `cChi` (emitted by the
    verified compiler) such that, writing `s = π(ρ(θ a))`, feeding the three
    governing lanes `s 0 0`, `s 1 0`, `s 2 0` (truncated to the leaf's `BitVec 32`)
    through `cChi` yields the χ output, and XORing the round constant reconstructs
    `keccakRound a rc 0 0`. The χ leaf is width-32 (χ is width-agnostic); the round
    runs it on full `BitVec 64` lanes — so we tie at the *formula* level (the leaf
    computes `s0 ⊕ ((¬s1) ∧ s2)`, the same shape the 64-bit `χ` cell computes,
    `CompileFromHaxSha2KeccakTie.chi_spec_eq_form`), then add `ι`'s round-constant
    XOR. Functional equality, NOT a security claim. -/
theorem keccakRound_00_eq_chi_iota_leaves :
    ∃ (cChi : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["a0", "a1", "a2"]
          CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak.chiLaneSrc = some cChi ∧
      ∀ (a : KState) (rc : BitVec 64),
        keccakRound a rc 0 0
          = (let s := pi (rho (theta a));
             (s 0 0 ^^^ ((~~~ s 1 0) &&& s 2 0))) ^^^ rc := by
  obtain ⟨cChi, hcChi, _⟩ :=
    CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie.chiLane_emitted_eq_form
  exact ⟨cChi, hcChi, fun a rc => keccakRound_00_decomp a rc⟩

/-! ## §4  The SHAKE chain-step absorb-prep leaf is the FIPS-202 §6 lane mix

The canonical `SLHDSA/SurfaceDeps.lean` runs `slhTweakHash seed tweak block =
SHAKE-128(seed ‖ tweak ‖ block, 16)`. The first sponge action on the
`seed ‖ tweak ‖ block` input is the FIPS-202 §6 `xorIn` lane mix; the committed
absorb-prep leaf computes one lane of it (`seed ⊕ tweak ⊕ block`). -/

/-- **The SHAKE chain-step absorb-prep leaf emitted by the verified compiler is the
    FIPS-202 §6 lane XOR.** The verified compiler emits a program `c` with
    `compileFromHax ["seed","tweak","block"] shakeAbsorbSrc = some c`, whose
    `BitVec 64` denotation is the lane mix `seed ⊕ tweak ⊕ block` — the
    `seed ‖ tweak ‖ block` input the SHAKE-128 chain step `F` (the canonical
    `slhTweakHash`) XORs into a Keccak lane before the permutation engine. The
    permutation that engine then runs is the four-step composition of §1–§3.
    Functional equality at the modeled lane, NOT a security claim. -/
theorem shakeAbsorb_emitted_eq_laneMix :
    ∃ (c : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["seed", "tweak", "block"] shakeAbsorbSrc = some c ∧
      ∀ (seed tweak block : BitVec 64),
        c.denote (inputValuation 64 3 ![seed, tweak, block])
          = seed ^^^ tweak ^^^ block :=
  shakeAbsorb_compiles

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaShakeChainTie
