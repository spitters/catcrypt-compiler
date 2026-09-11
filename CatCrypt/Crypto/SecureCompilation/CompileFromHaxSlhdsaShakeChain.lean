/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxKeccak

/-!
# C4 hash-composition fan-out: the SLH-DSA (SHAKE-128f) WOTS+ chain-step Keccak engine leaf

This module is the **SHAKE-128f** companion to `CompileFromHaxSlhdsaChain` (the
`sha2-*` chain tie). Where the `sha2-*` parameter sets run the FIPS-180-4 SHA-256
round at the heart of the WOTS+ chain step `F`, the **`shake-128{s,f}` /
`shake-192{s,f}` / `shake-256{s,f}` parameter sets** (and the *canonical*
`SLHDSA/SurfaceDeps.lean` instance, which wires `slhTweakHash = SHAKE-128`)
run the **Keccak-f[1600] permutation** instead.

## What this is — the SHAKE chain shape

SLH-DSA (FIPS 205) is the stateless hash-based signature parameterised over a
tweakable hash family. For the `shake-*` parameter sets the WOTS+ chain step
`F(PK.seed, ADRS, M)` is a `SHAKE256`/`SHAKE128` call:

```text
   F(PK.seed, ADRS, M) = SHAKE(PK.seed ‖ ADRS ‖ M, n)
```

(in CatCrypt's canonical `SurfaceDeps`, `slhTweakHash seed tweak block =
SHAKE-128(seed ‖ tweak ‖ block, 16)`). The XOF's engine is the FIPS-202 §3.2
sponge over the **Keccak-f[1600]** permutation
`Primitives.Keccak.keccakF = 24× keccakRound`, with the round

```text
   keccakRound a rc = ι (χ (π (ρ (θ a)))) rc
```

The four *bit-twiddling* steps of that round — `θ`, `ρ`, `χ`, `ι` — are each
already realized by a committed compile-from-hax Keccak leaf
(`CompileFromHaxKeccak.{thetaCLane,thetaDLane,rhoLane,chiLane,iotaLane}_compiles`,
tied onto `Primitives.Keccak.{theta,rho,chi,iota}` in `CompileFromHaxSha2KeccakTie`
and `CompileFromHaxKeccakStepTie`). The `π` step is a pure **lane permutation**
(an index remap with no bit arithmetic — `π a x y = a (x+3y) x`), so it carries
no emitted leaf; it is structural shuffling, not a primitive to compile.

This module records the **SHAKE absorb-prep leaf** — the single straight-line
`wrapping_add`/`BitXor` shape the chain-step's tweaked input mixing runs before
the permutation (the `ADRS ‖ seed ‖ M` lane-XOR `xorIn` shape of FIPS-202 §6) —
as the load-bearing compile-from-hax leaf at `w = 64`, the Keccak lane width. The
genuine *engine* composition (the four tied step leaves reconstructing one
`keccakRound`) is the companion tie `CompileFromHaxSlhdsaShakeChainTie`.

## Front gap note (honest)

The full SHAKE-128 the chain step runs is `squeeze (absorb (seed ‖ tweak ‖
block)))` — a sponge: a *padded, multi-block absorb* (`xorIn` + `keccakF` per
rate-block) then a `keccakF`-driven squeeze, plus the FIPS-205 ADRS byte-encoding
and the `0x1F`/`0x80` domain-separation padding. The verified front
(`compileFromHax`) recognizes only **straight-line scalar word ops** (the
`wrapping_add`/`BitXor`/`BitAnd`/`rotate_right` recognizer set) — it does **not**
express the sponge's variable-length padding loop, the multi-block `keccakF`
iteration, the ADRS byte layout, or the `0x1F`/`0x80` domain-separation bytes.

So the tie is at the **Keccak-permute-engine level**, exactly as the `sha2-*`
tie landed at the SHA-256 *round-engine* level (not the full message-schedule
loop): we tie the leaves that the permutation runs (`θ`/`ρ`/`χ`/`ι` composing one
`keccakRound`, the engine `keccakF`/`shake128`/`slhTweakHash` iterates), and
record the absorb-prep lane mixing as the chain step's pre-permute leaf. The
sponge padding / ADRS encoding / multi-block iteration are honestly **out of the
front's expressible fragment** and are not claimed as compile-from-hax leaves.

## Honest framing

This is a **functional-equality** leaf, not a security claim. SLH-DSA's hash
chain is built on the (unkeyed) Keccak permutation; nothing here establishes
preimage/collision resistance or the WOTS+/FORS EUF-CMA reduction (those live in
`SLHDSA/Reduction.lean` over the abstract `TweakableHashParams`). The result is
`<emit-form> = <FIPS-202 lane-mix / step quantity>` — the engine the `shake-*`
chain step `F` runs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaShakeChain

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  The SHAKE chain-step absorb-prep lane mix — `w = 64`, parameters `["seed","tweak","block"]`

Before the permutation, the chain step `F(seed, tweak, block) = SHAKE(seed ‖
tweak ‖ block)` mixes its three tweaked inputs into a Keccak lane via the FIPS-202
§6 `xorIn` lane-XOR. Modeled at one lane (`w = 64`, the Keccak lane width), the
mix is a chained `BitXor` of the three input words — the same straight-line
`⊕`-reduction shape as the Keccak θ-C column parity, here over the chain step's
`(seed, tweak, block)` lane words. -/

/-- The SHAKE chain-step absorb-prep lane mix as a hax `ImpExpr`, fully
    let-normalized, parameters `["seed","tweak","block"]` (`nIn = 3`;
    `I 0 = seed`, `I 1 = tweak`, `I 2 = block`). The `seed ‖ tweak ‖ block`
    input of `F` is XORed into one Keccak lane: `lane = seed ⊕ tweak ⊕ block`. -/
def shakeAbsorbSrc : ImpExpr :=
  .letBind "t1" (.app "BitXor" [.var "seed", .var "tweak"])
    (.letBind "r" (.app "BitXor" [.var "t1", .var "block"])
      (.var "r"))

/-- The explicit closed **emit form** the absorb-prep source denotes to, at
    `w = 64`: the lane XOR `seed ⊕ tweak ⊕ block`. -/
def shakeAbsorbForm (seed tweak block : BitVec 64) : BitVec 64 :=
  seed ^^^ tweak ^^^ block

/-- The absorb-prep source denotes (under `denoteScalar`, parameters
    `["seed","tweak","block"]`) to the emit form `shakeAbsorbForm`, reading
    `seed = inpGet I 0`, `tweak = inpGet I 1`, `block = inpGet I 2`. -/
theorem shakeAbsorbSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["seed", "tweak", "block"] I shakeAbsorbSrc (fun _ => none)
      = some (shakeAbsorbForm (inpGet I 0) (inpGet I 1) (inpGet I 2)) := by
  simp only [shakeAbsorbSrc, shakeAbsorbForm, ImpExpr.denoteScalar, denoteAtomExpr,
    recogBin, JasminBinOp.apply, List.idxOf?, List.findIdx?, reduceIte, String.reduceEq]
  rfl

/-- The compile-from-hax pipeline succeeds on the absorb-prep lane mix (`w = 64`,
    three parameters). -/
theorem shakeAbsorb_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 3) ["seed", "tweak", "block"] shakeAbsorbSrc).isSome := by
  native_decide

/-- **SLH-DSA (SHAKE) chain-step absorb-prep lane mix emitted by the verified
    compiler.** There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["seed","tweak","block"] shakeAbsorbSrc = some c`, and for
    every triple `(seed, tweak, block)`, `c`'s `BitVec 64` denotation (under the
    input valuation `![seed, tweak, block]`) is exactly the lane XOR
    `seed ⊕ tweak ⊕ block` — the `seed ‖ tweak ‖ block` input mixing the
    `shake-*` chain step `F` runs into a Keccak lane before the permutation.
    Routed through the C3 per-primitive obligation `compileFromHax_meets_spec`. -/
theorem shakeAbsorb_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 3 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 3) ["seed", "tweak", "block"] shakeAbsorbSrc = some c ∧
      ∀ (seed tweak block : BitVec 64),
        c.denote (inputValuation 64 3 ![seed, tweak, block])
          = seed ^^^ tweak ^^^ block := by
  set c := (compileFromHax (w := 64) (nIn := 3) ["seed", "tweak", "block"] shakeAbsorbSrc).get
    shakeAbsorb_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 3) ["seed", "tweak", "block"] shakeAbsorbSrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro seed tweak block
  have hspec : ImpExpr.denoteScalar ["seed", "tweak", "block"] ![seed, tweak, block]
      shakeAbsorbSrc (fun _ => none) = some (seed ^^^ tweak ^^^ block) := by
    have h := shakeAbsorbSrc_denoteScalar (nIn := 3) ![seed, tweak, block]
    simpa only [shakeAbsorbForm, inpGet, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 3) ["seed", "tweak", "block"]
    ![seed, tweak, block] shakeAbsorbSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSlhdsaShakeChain
