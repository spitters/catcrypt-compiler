/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LeafSig
public import CatCrypt.Crypto.Jasmin.LeafSig
public meta import CatCrypt.Crypto.Vale.LeafLeakage
public import CatCrypt.Crypto.Vale.LeafLeakage


@[expose] public section
set_option autoImplicit false

/-!
# Bernstein-Yang safegcd inversion over `Fp_{Vesta}` (AUCurves leaf)

This module declares the AUCurves verified-CT Bernstein-Yang divstep
modular inversion for the **Vesta base prime** (the 255-bit base
field defining the Vesta elliptic curve), as an opaque verified-CT
leaf for CatCrypt's verified front, following the established extCall
pattern (Jasmin.LowCT `RCall`).

Sibling adoption to `Vale/Pallas.lean` — Pallas and Vesta form the
**Pasta cycle**, where each curve's base field equals the other's
scalar field. Both leaves share the same shape (1×4 limbs, 590
divsteps); only the prime constant differs.

## Pilot scope (BY/safegcd wave 2, Vesta Fp — Halo2 / Pasta cycle)

The BY/safegcd Vale-leaf adoption wave brings the audited
constant-time inversion primitives from AUCurves
(`curve25519-jasmin-rs::safegcd_vesta`) into CatCrypt's verified
front. Together with `Vale/Pallas.lean` this closes the Pasta-cycle
inversion surface — both the base-field and scalar-field inversions
are needed by Halo2 (Zcash Orchard), Mina (kimchi), Aleo, and other
IPA-based SNARK constructions that exploit the cycle (e.g. recursive
proof composition where one curve's verifier uses the other curve's
base field as its native arithmetic).

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves(safegcd leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT inversion in Fp_{Vesta}
```

CatCrypt's verified front discharges the orchestration (copy-in,
leaf call, copy-out via the typed reg-ptr ABI); the leaf's denotation
matches the AUCurves Bernstein-Yang divstep correctness theorem; CT is
inherited from the safegcd algorithm's data-independent control flow
(10 outer × 59 inner = 590 divsteps, ≥ paper Theorem 1 bound of 588
for `b = 255`).

## The AUCurves / Bernstein-Yang provenance

* **Rust source**: `curve25519-jasmin-rs/src/safegcd_vesta.rs` in the
  AUCurves tree. The entry point
  `vesta_invert_divstep_sat` takes a 4×u64 saturated little-endian
  representation of `x` and writes `x^{-1} mod p_{Vesta}` into a
  4×u64 output buffer.
* **Shared safegcd kernel**: `curve25519-jasmin-rs/src/safegcd.rs`
  contains the generic Bernstein-Yang divstep loop over 5×62-bit
  signed limbs (`Signed62<5>`), parameterised by `ModInfo<5>`
  carrying the prime constant and iteration count. The kernel is
  reused for `p256`, `p384`, `p521`, `secp256k1`, `bls12_377`,
  `bls12_381`, `bls24_509`, `bn254`, `bn256`, `bn446`, `bw6_761`,
  `pallas`, `vesta` — each module supplies its `ModInfo` and the
  saturated↔signed62 packers.
* **Vesta base prime** (FIPS-style display):
  `p = 2^254 + 45560315531506369815346746415080538113`
    `= 0x40000000_00000000_00000000_00000000_224698fc_0994a8dd_8c46eb21_00000001`
    `= 28948022309329048855892746252171976963363056481941647379679742748393362948097`.
  This is the **base** field of Vesta (and the **scalar** field of
  Pallas — the Pasta cycle property).
* **Algorithmic provenance**: Bernstein–Yang 2019 (eprint 2019/266),
  "Fast constant-time gcd computation and modular inversion", refined
  by Pornin 2020 (eprint 2020/972). The divstep loop is data-
  independent in the secret input (the iteration count `590` is fixed
  at compile time, derived from ⌈(9437 · 255 + 1) / 4096⌉ = 588 per
  the paper's Theorem 1, with 2 extra divsteps as safety margin —
  same shape as Pallas, `secp256k1`, `p256`).
* **CT audit**: AUCurves's existing valgrind/crabgrind harness
  (`tests/valgrind_ct.rs`) marks the secret limbs as undefined and
  runs the divstep loop under `valgrind --tool=memcheck`. The leaf
  is verified branch-free in the secret input via this dynamic
  taint-tracking analysis. The KAT test in
  `safegcd_vesta.rs::tests::vesta_invert_times_self_is_one`
  certifies `x · invert(x) ≡ 1 (mod p_{Vesta})` byte-identically
  against a separate schoolbook 4×4 → 8-limb mul-mod reference.

## Leaf C signature (Rust `extern "C"` shape)

```c
extern void vesta_invert_divstep_sat(uint64_t out[4], const uint64_t x[4]);
```

That is: `out = x^{-1} mod p_{Vesta}` over 4×u64 saturated LE
buffers (32 bytes per operand, the canonical wire format for Vesta
Fp elements — same shape as Pallas and Curve25519's `Fe25519`).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **Safegcd_Vesta_invert_denote**: the leaf computes the modular
   inverse `x^{-1} mod p` where `p` is the Vesta base prime, sourced
   from the Bernstein-Yang divstep correctness proof and the
   `ModInfo` derivation in `safegcd.rs::modinfo_from_4u64`.

2. **Safegcd_Vesta_invert_CT**: the leaf is constant-time in `x`
   (the secret field element). Sourced from the data-independent
   control-flow audit of the Bernstein-Yang divstep loop
   (10 outer × 59 inner iterations, fixed at compile time) plus
   AUCurves's dynamic valgrind/crabgrind CT verification on the
   compiled binary.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the Rust-exported `vesta_invert_divstep_sat` from the
   AUCurves staticlib. Standard C-linker trust.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is a hand-emitted Fermat addition chain over
`p - 2` (∼3000-bit chain of `fp_sqr`/`fp_mul` calls), because:

* The Bernstein-Yang proof bounds `590 ≥ 588` divsteps as sufficient
  to reach `(1, x^{-1})` from `(p, x)`; the algorithm is fully
  data-independent regardless of `x`'s bit pattern.
* AUCurves's divstep loop has CI taint-tracking on every release;
  hand-emitted Fermat chains do not.
* The same well-audited kernel services 13 curves; the shared
  algorithm has had far more cross-cite review than any per-curve
  Fermat chain.
-/

namespace CatCrypt.Crypto.Vale.Vesta

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

The 32-byte Vesta `Fp` element (4×u64 saturated LE on the wire).
Opaque — the concrete leaf at link time is the AUCurves Rust symbol. -/

opaque VestaFp.Impl : NonemptyType.{0}
/-- A 32-byte Vesta `Fp` field element (4×u64 saturated LE).
    Opaque; the concrete leaf is the AUCurves verified-CT
    `vesta_invert_divstep_sat`. -/
def VestaFp : Type := VestaFp.Impl.type
instance : Nonempty VestaFp := VestaFp.Impl.property
/-- An inhabitant. -/
noncomputable opaque VestaFp.default : VestaFp
noncomputable instance : Inhabited VestaFp :=
  ⟨VestaFp.default⟩

/-! ## §2. AUCurves-leaf axioms (the trust delta)

These are the two axioms we add to CatCrypt's axiom budget when we
permit the AUCurves BY/safegcd leaf into the pipeline for the Vesta
base prime. Each is sourced from AUCurves's `safegcd_vesta.rs`
upstream. -/

/-- **Denotation axiom**: the AUCurves verified-CT
    `vesta_invert_divstep_sat` leaf computes the modular inverse of
    its input over the Vesta base prime
    `p = 0x40000000…00000001 = 2^254 + 45560315531506369815346746415080538113`.
    Discharged by Bernstein-Yang's divstep correctness theorem
    applied to `ModInfo<5>` constructed by
    `safegcd::modinfo_from_4u64(VESTA_P_4X64, 10)` (590 ≥ 588
    divsteps suffice for `b = 255`), and the round-trip KAT in
    `safegcd_vesta.rs::tests::vesta_invert_times_self_is_one`. -/
noncomputable opaque Safegcd_Vesta_invert_denote
    (x : VestaFp) : VestaFp

/-- **Leakage function**: the observable trace the
    `vesta_invert_divstep_sat` leaf emits on operand `x`. -/
noncomputable opaque Safegcd_Vesta_invert_leak (x : VestaFp) : LeafLeak

/-- **Constant-time axiom**: the leakage trace of the AUCurves verified-CT
    Vesta `Fp` inverter is the same at every operand `x`. The Bernstein-Yang
    divstep loop has a compile-time-fixed iteration count and the per-step
    update is conditional-multiplexed adds and shifts with no
    operand-dependent branch or memory access, so no execution of the leaf
    distinguishes two field elements. Cited in `ValeCoqAxioms.lean`. -/
axiom Safegcd_Vesta_invert_CT :
    SecretIndependent Safegcd_Vesta_invert_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/SafegcdBLS12_381.lean` pattern: registering the
leaf so the verified front accepts `RCall "vesta_invert_divstep_sat"`
as a well-formed extCall whose argument shape is `1 × TBytes 32`
(one Fp element). -/

/-- Register `Safegcd_Vesta_invert_denote` → leaf
    `vesta_invert_divstep_sat` (the C symbol name, matching the
    AUCurves Rust `#[inline(never)]`-marked `pub fn` export). -/
@[rust_cmd_pattern]
def safegcdVestaPattern : LowCTPattern where
  name      := "vesta_invert_divstep_sat"
  fnHead    := ``Safegcd_Vesta_invert_denote
  arity     := 1
  towerType := .TBytes 32   -- 32-byte Fp element (4×u64 saturated LE)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a Vesta Fp element
    (`TBytes 32` — 32 bytes, the Vesta base-field on-wire size). -/
def vestaFpTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry for the AUCurves leaf

The AUCurves safegcd leaf is **non-aliasing** at the SSA level:
`out` and `x` are distinct buffers in the Rust signature
(`&mut [u64; 4]` and `&[u64; 4]` borrow-check as distinct). We
declare `destAliasOk := []` (the conservative default). -/

/-- Per-leaf signature for `vesta_invert_divstep_sat`:
    no aliasing permitted (out / x distinct in the Rust signature). -/
def safegcdVestaLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "vesta_invert_divstep_sat"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the Vesta `Fp` inversion, serving as the
front-end input to the reflection pipeline. The body is the single
AUCurves-leaf call. -/

/-- One Vesta `Fp` modular-inversion invocation. -/
noncomputable def safegcdVestaInvertLean
    (x : VestaFp) : VestaFp :=
  Safegcd_Vesta_invert_denote x

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `Vale/SafegcdBLS12_381.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `safegcdVestaInvertLean`. Shape:
    `RSeq RSkip (RCall "vesta_invert_divstep_sat"
                       __result [x])`. -/
def safegcdVestaInvertBody : LowCT :=
  let x_l      := loc "x"        vestaFpTowerType
  let result_l := loc "__result" vestaFpTowerType
  .RSeq .RSkip
    (.RCall "vesta_invert_divstep_sat"
            result_l [x_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd Vesta leaf. -/
def safegcdVestaInvertReified : ReifiedFunc :=
  { args    := [("x", vestaFpTowerType)]
    body    := safegcdVestaInvertBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval safegcdVestaInvertReified.args.map Prod.fst
  -- [x]
#eval safegcdVestaInvertReified.args.length     -- 1
#eval safegcdVestaInvertReified.retName         -- __result

end CatCrypt.Crypto.Vale.Vesta
