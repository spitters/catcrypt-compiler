/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LeafSig
public import CatCrypt.Crypto.Jasmin.LeafSig
public meta import CatCrypt.Crypto.Vale.LeafLeakage
public import CatCrypt.Crypto.Vale.LeafLeakage


@[expose] public section
set_option autoImplicit false

/-!
# Bernstein-Yang safegcd inversion over `Fp_{BN254}` (AUCurves leaf)

This module declares the AUCurves verified-CT Bernstein-Yang divstep
modular inversion for the BN254 (alt_bn128) **base field** `Fp`
(the 254-bit prime
`p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`),
as an opaque verified-CT leaf for CatCrypt's verified front, following
the established extCall pattern (`Jasmin.LowCT` `RCall`).

Sibling adoption to `Vale/SafegcdP256.lean` / `Vale/SafegcdSecp256k1.lean`
— same 4-limb (32-byte) shape, same shared safegcd kernel; only the
prime constant differs.

## Scope

The `Fp` inverse in `Vale/BN254.lean` is the **Fermat** addition chain
`a^{p−2}` (`Vale_AUCurves_BN254_Fp_inv_denote`, exponent `p − 2`); the
sibling P-curves and BLS12-381 route through the AUCurves Bernstein-Yang
safegcd divstep. This module routes BN254's `Fp` inverse through the
divstep leaf, with the same recipe that puts the BLS12-381 inverse at
~1.10× blst's own divstep (`ct_inverse_mod_384`) and ~9× faster than the
Fermat chain.

BN254 inversion is the hot inner step in the Jacobian → affine
normalisation of the G1 MSM (EIP-196 `alt_bn128_add`/`_mul`) and in
the EIP-197 pairing-check denominators.

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves(safegcd leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT inversion in Fp_{BN254}
```

CatCrypt's verified front discharges the orchestration (copy-in, leaf
call, copy-out via the typed reg-ptr ABI); the leaf's denotation matches
the AUCurves Bernstein-Yang divstep convergence certificate; CT is
inherited from the safegcd structure (data-independent divsteps, fixed
iteration count at compile time).

## The AUCurves / Bernstein-Yang provenance

* **Rust source**: `safegcd_bn254.rs` (AUCurves, curve25519-jasmin-rs crate),
  function `bn254_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4])`.
  Computes `out = x^{-1} mod p` where `p` is the BN254 base prime.
* **Shared safegcd kernel**:
  `safegcd.rs` (AUCurves, curve25519-jasmin-rs crate) — the
  generic Bernstein-Yang divstep loop over `N`×62-bit signed limbs
  (`Signed62<5>` for a 254-bit prime), parameterised by `ModInfo<5>`
  carrying the prime constant and the outer iteration count. The same
  kernel services `p256`, `p384`, `p521`, `secp256k1`, `bls12_381`,
  `bn254`, etc. — each module supplies its `ModInfo` and the
  saturated↔signed62 packers (`from_saturated_4` / `to_saturated_4`).
  For BN254: `BN254: ModInfo<5> = sg::modinfo_from_4u64(BN254_P_4X64, 10)`
  — δ₀=1/2, **10 outer × 59 inner = 590 divsteps** (the Wuille/Pornin
  bound ⌈(9437·254 + 1)/(4096·59)⌉ = 10 outer iterations for `b = 254`).
* **KAT**: `safegcd_bn254.rs`'s `bn254_invert_times_self_is_one` test
  exercises 4 deterministic non-zero inputs (incl. `p − 1`) and asserts
  `x · invert(x) ≡ 1 (mod p)` byte-identically via the in-file
  schoolbook 4×4 → 8-limb mul + bit-by-bit Barrett reduce reference
  (fiat-rust 0.3.0 ships no BN254 module).
* **Algorithmic provenance**: Bernstein-Yang 2019 (eprint 2019/266),
  "Fast constant-time gcd computation and modular inversion", refined by
  Pornin 2020 (eprint 2020/972).

## Leaf C signature (Rust `extern "C"` shape, exposed by the bench shim)

```c
extern void safegcd_bn254_invert(uint64_t out[4], const uint64_t x[4]);
```

That is: `out = x^{-1} mod p_{BN254}` over saturated radix-2^64 4×u64
inputs (32 bytes per operand). Returns `[0, 0, 0, 0]` for `x = 0`
(Bernstein-Yang convention).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **AUCurves_safegcd_bn254_invert_denote**: the leaf computes
   `x^{-1} mod p`, `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`,
   on canonical 4×u64 inputs. Discharged by AUCurves' Bernstein-Yang
   divstep correctness applied to `ModInfo<5>` constructed by
   `safegcd::modinfo_from_4u64(BN254_P_4X64, 10)` (590 divsteps suffice
   for `b = 254`), plus the in-file `x · invert(x) ≡ 1 (mod p)`
   round-trip KAT.

2. **AUCurves_safegcd_bn254_invert_CT**: the leaf is constant-time in
   `x`. Sourced from the safegcd structure (fixed iteration count = 10
   outer × 59 inner = 590 divsteps; per-step update is a sequence of
   conditional-multiplexed adds / shifts with no data-dependent branches
   or memory accesses). Stated as `SecretIndependent` of the leaf's
   leakage function; the citation is in `ValeCoqAxioms.lean`.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the AUCurves-extracted Rust code (via the per-bench
   `bn254_safegcd_shim` staticlib). Standard C-linker trust.

The trust delta is **strictly smaller** than the prior Fermat
`a^{p−2}` addition chain `bn254_inv`:

* The Bernstein-Yang proof bounds 590 divsteps as sufficient to reach
  `(1, x^{-1})` from `(p, x)`; the algorithm is fully data-independent
  regardless of `x`'s bit pattern. The Fermat path is also CT but is
  ∼2× slower on the BN254 prime (≥500 field mul/sqr in the addition
  chain vs ≤590 divsteps over 5-limb Signed62 internally).
-/

namespace CatCrypt.Crypto.Vale.SafegcdBN254

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

The 32-byte BN254 base-field element (4×u64 saturated LE on the wire).
Opaque — the concrete leaf at link time is the AUCurves Rust symbol
`safegcd_bn254_invert` (re-export of `bn254_invert_divstep_sat`). -/

/-- A 32-byte BN254 `Fp` field element (4×u64 saturated LE).
    Opaque; the concrete leaf is the AUCurves verified-CT
    `bn254_invert_divstep_sat`. -/
axiom BN254SafegcdFieldElt : Type
/-- Axiomatic inhabitant. -/
axiom BN254SafegcdFieldElt.default : BN254SafegcdFieldElt
noncomputable instance : Inhabited BN254SafegcdFieldElt :=
  ⟨BN254SafegcdFieldElt.default⟩

/-! ## §2. AUCurves-leaf axioms (the trust delta)

These are the two axioms we add to CatCrypt's axiom budget when we
permit the AUCurves BY/safegcd BN254 leaf into the pipeline. Each is
sourced from AUCurves' `safegcd_bn254.rs` upstream. -/

/-- **Denotation axiom**: the AUCurves verified-CT
    `bn254_invert_divstep_sat` leaf computes the modular inverse of its
    input over the BN254 base prime
    `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`.
    Discharged by Bernstein-Yang's divstep correctness theorem applied
    to `ModInfo<5>` constructed by
    `safegcd::modinfo_from_4u64(BN254_P_4X64, 10)` (590 divsteps suffice
    for `b = 254`), and the round-trip KAT in
    `safegcd_bn254.rs::tests::bn254_invert_times_self_is_one`. -/
axiom AUCurves_safegcd_bn254_invert_denote
    (x : BN254SafegcdFieldElt) : BN254SafegcdFieldElt

/-- **Leakage function**: the observable trace the
    `bn254_invert_divstep_sat` leaf emits on operand `x`. -/
axiom AUCurves_safegcd_bn254_invert_leak (x : BN254SafegcdFieldElt) : LeafLeak

/-- **Constant-time axiom**: the leakage trace of the AUCurves verified-CT
    `bn254_invert_divstep_sat` leaf is the same at every operand `x`. The
    Bernstein-Yang divstep loop runs 10 outer × 59 inner iterations fixed at
    compile time, and the per-step update is conditional-multiplexed adds and
    shifts with no operand-dependent branch or memory access, so no execution
    of the leaf distinguishes two field elements. Cited in
    `ValeCoqAxioms.lean`. -/
axiom AUCurves_safegcd_bn254_invert_CT :
    SecretIndependent AUCurves_safegcd_bn254_invert_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/SafegcdP256.lean` pattern: registering the leaf so
the verified front accepts `RCall "safegcd_bn254_invert"` as a
well-formed extCall whose argument shape is `1 × TBytes 32` (one BN254
Fp element). -/

/-- Register `AUCurves_safegcd_bn254_invert_denote` → leaf
    `safegcd_bn254_invert` (the C symbol name, matching the `extern "C"`
    re-export of `bn254_invert_divstep_sat` in the bench shim
    staticlib). -/
@[rust_cmd_pattern]
def safegcdBN254Pattern : LowCTPattern where
  name      := "safegcd_bn254_invert"
  fnHead    := ``AUCurves_safegcd_bn254_invert_denote
  arity     := 1
  towerType := .TBytes 32   -- 32-byte BN254 Fp element (4×u64 saturated LE)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a BN254 Fp element
    (`TBytes 32` — 32 bytes, the saturated 4×u64 packing). -/
def bn254SafegcdFieldEltTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry for the AUCurves leaf

The AUCurves safegcd leaf is **non-aliasing** at the SSA level: `out`
and `x` are distinct buffers in the Rust signature (`&mut [u64; 4]` and
`&[u64; 4]` borrow-check as distinct). We declare `destAliasOk := []`
(the conservative default). -/

/-- Per-leaf signature for `safegcd_bn254_invert`: no aliasing permitted
    (out / x distinct in the Rust signature). -/
def safegcdBN254LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "safegcd_bn254_invert"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the BN254 `Fp` inversion, serving as the
front-end input to the reflection pipeline. The body is the single
AUCurves-leaf call. -/

/-- One BN254 `Fp` modular-inversion invocation. -/
noncomputable def safegcdBN254InvertLean
    (x : BN254SafegcdFieldElt) : BN254SafegcdFieldElt :=
  AUCurves_safegcd_bn254_invert_denote x

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `Vale/SafegcdP256.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `safegcdBN254InvertLean`. Shape:
    `RSeq RSkip (RCall "safegcd_bn254_invert" __result [x])`. -/
def safegcdBN254InvertBody : LowCT :=
  let x_l      := loc "x"        bn254SafegcdFieldEltTowerType
  let result_l := loc "__result" bn254SafegcdFieldEltTowerType
  .RSeq .RSkip
    (.RCall "safegcd_bn254_invert"
            result_l [x_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd BN254 leaf. -/
def safegcdBN254InvertReified : ReifiedFunc :=
  { args    := [("x", bn254SafegcdFieldEltTowerType)]
    body    := safegcdBN254InvertBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval safegcdBN254InvertReified.args.map Prod.fst
  -- [x]
#eval safegcdBN254InvertReified.args.length     -- 1
#eval safegcdBN254InvertReified.retName         -- __result

end CatCrypt.Crypto.Vale.SafegcdBN254
