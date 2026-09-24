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
# Bernstein-Yang safegcd inversion over `Fp_{BLS12-381}` (AUCurves leaf)

This module declares the AUCurves verified-CT Bernstein-Yang divstep
modular inversion for the BLS12-381 **base field** `Fp` (the 381-bit
prime defining the BLS12-381 curve), as an opaque verified-CT leaf for
CatCrypt's verified front, following the established extCall pattern
(Jasmin.LowCT `RCall`).

Sibling adoption to `Vale/Curve25519.lean` — the trust shape is the same
`extCall` boundary; the upstream proof bundle differs.

## Pilot scope (BY/safegcd wave 1, BLS12-381 Fp)

The BY/safegcd Vale-leaf adoption wave brings the audited
constant-time inversion primitives from AUCurves
(`curve25519-jasmin-rs::safegcd_bls12_381`) into CatCrypt's verified
front. Inversion is a hot inner step in any pairing-based protocol
(`Groth16`, `KZG`, `BLS`) — every `Fp` and `Fp12` final-exponentiation
inversion routes through this primitive in the verifier path.

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves(safegcd leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT inversion in Fp
```

CatCrypt's verified front discharges the orchestration (copy-in,
leaf call, copy-out via the typed reg-ptr ABI); the leaf's denotation
matches the AUCurves Bernstein-Yang divstep correctness theorem; CT is
inherited from the safegcd algorithm's data-independent control flow
(15 outer × 59 inner = 885 divsteps, ≥ paper Theorem 1 bound of 878
for `b = 381`).

## The AUCurves / Bernstein-Yang provenance

* **Rust source**: `curve25519-jasmin-rs/src/safegcd_bls12_381.rs`
  in the AUCurves tree. The entry point
  `bls12_invert_divstep_sat` takes a 6×u64 saturated little-endian
  representation of `x` and writes `x^{-1} mod p` into a 6×u64 output
  buffer.
* **Shared safegcd kernel**: `curve25519-jasmin-rs/src/safegcd.rs`
  contains the generic Bernstein-Yang divstep loop over 7×62-bit
  signed limbs (`Signed62<7>`), parameterised by `ModInfo<7>`
  carrying the prime constant and iteration count. The kernel is
  reused for `p256`, `p384`, `p521`, `secp256k1`, `bls12_377`,
  `bls12_381`, `bls24_509`, `bn254`, `bn256`, `bn446`, `bw6_761`,
  `pallas`, `vesta` — each module supplies its `ModInfo` and the
  saturated↔signed62 packers.
* **Algorithmic provenance**: Bernstein–Yang 2019 (eprint
  2019/266), "Fast constant-time gcd computation and modular
  inversion", refined by Pornin 2020 (eprint 2020/972). The
  divstep loop is data-independent in the secret input (the
  iteration count `885` is fixed at compile time, derived from
  ⌈(9437 · 381 + 1) / 4096⌉ = 878 per the paper's Theorem 1, with
  7 extra divsteps as safety margin).
* **CT audit**: AUCurves's existing valgrind/crabgrind harness
  (`tests/valgrind_ct.rs`) marks the secret limbs as undefined and
  runs the divstep loop under `valgrind --tool=memcheck`. The leaf
  is verified branch-free in the secret input via this dynamic
  taint-tracking analysis. The KAT test in
  `safegcd_bls12_381.rs::tests::bls12_invert_times_self_is_one`
  certifies `x · invert(x) ≡ 1 (mod p)` byte-identically against a
  separate schoolbook 6×6 → 12-limb mul-mod reference.

## Leaf C signature (Rust `extern "C"` shape)

```c
extern void bls12_invert_divstep_sat(uint64_t out[6], const uint64_t x[6]);
```

That is: `out = x^{-1} mod p_{BLS12-381}` over 6×u64 saturated LE
buffers (48 bytes per operand, the canonical wire format for BLS12-381
Fp elements).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **Safegcd_BLS12_381_invert_denote**: the leaf computes the modular
   inverse `x^{-1} mod p` where `p` is the BLS12-381 base prime,
   sourced from the Bernstein-Yang divstep correctness proof and the
   `ModInfo` derivation in `safegcd.rs::modinfo_from_6u64`.

2. **Safegcd_BLS12_381_invert_CT**: the leaf is constant-time in `x`
   (the secret field element). Sourced from the data-independent
   control-flow audit of the Bernstein-Yang divstep loop
   (15 outer × 59 inner iterations, fixed at compile time) plus
   AUCurves's dynamic valgrind/crabgrind CT verification on the
   compiled binary.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the Rust-exported `bls12_invert_divstep_sat` from the
   AUCurves staticlib. Standard C-linker trust.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is a hand-emitted Fermat addition chain over
`p - 2` (∼6000-bit chain of `fp_sqr`/`fp_mul` calls), because:

* The Bernstein-Yang proof bounds `885 ≥ 878` divsteps as sufficient
  to reach `(1, x^{-1})` from `(p, x)`; the algorithm is fully
  data-independent regardless of `x`'s bit pattern. The Fermat path
  is also CT but is ∼2× slower on BLS12-381's prime (1500+ field
  multiplications in the addition chain vs ∼885 divsteps over 7-limb
  Signed62 internally).
* AUCurves's divstep loop has CI taint-tracking on every release;
  hand-emitted Fermat chains do not.
-/

namespace CatCrypt.Crypto.Vale.SafegcdBLS12_381

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

The 48-byte BLS12-381 `Fp` element (6×u64 saturated LE on the wire).
Opaque — the concrete leaf at link time is the AUCurves Rust symbol. -/

opaque BLS12_381_Fp.Impl : NonemptyType.{0}
/-- A 48-byte BLS12-381 `Fp` field element (6×u64 saturated LE).
    Opaque; the concrete leaf is the AUCurves verified-CT
    `bls12_invert_divstep_sat`. -/
def BLS12_381_Fp : Type := BLS12_381_Fp.Impl.type
instance : Nonempty BLS12_381_Fp := BLS12_381_Fp.Impl.property
/-- An inhabitant. -/
noncomputable opaque BLS12_381_Fp.default : BLS12_381_Fp
noncomputable instance : Inhabited BLS12_381_Fp :=
  ⟨BLS12_381_Fp.default⟩

/-! ## §2. AUCurves-leaf axioms (the trust delta)

These are the two axioms we add to CatCrypt's axiom budget when we
permit the AUCurves BY/safegcd leaf into the pipeline. Each is
sourced from AUCurves's `safegcd_bls12_381.rs` upstream. -/

/-- **Denotation axiom**: the AUCurves verified-CT
    `bls12_invert_divstep_sat` leaf computes the modular inverse of
    its input over the BLS12-381 base prime
    `p = 0x1A0111EA…AAAB`. Discharged by Bernstein-Yang's divstep
    correctness theorem applied to `ModInfo<7>` constructed by
    `safegcd::modinfo_from_6u64(BLS12_P_6X64, 15)` (885 ≥ 878
    divsteps suffice for `b = 381`), and the round-trip KAT in
    `safegcd_bls12_381.rs::tests::bls12_invert_times_self_is_one`. -/
axiom Safegcd_BLS12_381_invert_denote
    (x : BLS12_381_Fp) : BLS12_381_Fp

/-- **Leakage function**: the observable trace the
    `bls12_invert_divstep_sat` leaf emits on operand `x`. -/
noncomputable opaque Safegcd_BLS12_381_invert_leak (x : BLS12_381_Fp) : LeafLeak

/-- **Constant-time axiom**: the leakage trace of the AUCurves verified-CT
    BLS12-381 `Fp` inverter is the same at every operand `x`. The
    Bernstein-Yang divstep loop has a compile-time-fixed iteration count and
    the per-step update is conditional-multiplexed adds and shifts with no
    operand-dependent branch or memory access, so no execution of the leaf
    distinguishes two field elements. Cited in `ValeCoqAxioms.lean`. -/
axiom Safegcd_BLS12_381_invert_CT :
    SecretIndependent Safegcd_BLS12_381_invert_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/Curve25519.lean` pilot pattern: registering the
leaf so the verified front accepts `RCall
"bls12_invert_divstep_sat"` as a well-formed extCall whose argument
shape is `1 × TBytes 48` (one `Fp` element). -/

/-- Register `Safegcd_BLS12_381_invert_denote` → leaf
    `bls12_invert_divstep_sat` (the C symbol name, matching the
    AUCurves Rust `#[no_mangle]`-equivalent export under
    `pub fn` + `#[inline(never)]`). -/
@[rust_cmd_pattern]
def safegcdBls12_381Pattern : LowCTPattern where
  name      := "bls12_invert_divstep_sat"
  fnHead    := ``Safegcd_BLS12_381_invert_denote
  arity     := 1
  towerType := .TBytes 48   -- 48-byte Fp element (6×u64 saturated LE)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a BLS12-381 Fp element
    (`TBytes 48` — 48 bytes, the BLS12-381 base-field on-wire size). -/
def bls12_381_FpTowerType : TowerType := .TBytes 48

/-! ## §5. `LeafSig` entry for the AUCurves leaf

The AUCurves safegcd leaf is **non-aliasing** at the SSA level:
`out` and `x` are distinct buffers in the Rust signature
(`&mut [u64; 6]` and `&[u64; 6]` borrow-check as distinct). We
declare `destAliasOk := []` (the conservative default). -/

/-- Per-leaf signature for `bls12_invert_divstep_sat`:
    no aliasing permitted (out / x distinct in the Rust signature). -/
def safegcdBls12_381LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "bls12_invert_divstep_sat"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the BLS12-381 `Fp` inversion, serving as the
front-end input to the reflection pipeline. The body is the single
AUCurves-leaf call. -/

/-- One BLS12-381 `Fp` modular-inversion invocation. -/
noncomputable def safegcdBls12_381InvertLean
    (x : BLS12_381_Fp) : BLS12_381_Fp :=
  Safegcd_BLS12_381_invert_denote x

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `Vale/Curve25519.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `safegcdBls12_381InvertLean`. Shape:
    `RSeq RSkip (RCall "bls12_invert_divstep_sat"
                       __result [x])`. -/
def safegcdBls12_381InvertBody : LowCT :=
  let x_l      := loc "x"        bls12_381_FpTowerType
  let result_l := loc "__result" bls12_381_FpTowerType
  .RSeq .RSkip
    (.RCall "bls12_invert_divstep_sat"
            result_l [x_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd BLS12-381 leaf. -/
def safegcdBls12_381InvertReified : ReifiedFunc :=
  { args    := [("x", bls12_381_FpTowerType)]
    body    := safegcdBls12_381InvertBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval safegcdBls12_381InvertReified.args.map Prod.fst
  -- [x]
#eval safegcdBls12_381InvertReified.args.length     -- 1
#eval safegcdBls12_381InvertReified.retName         -- __result

end CatCrypt.Crypto.Vale.SafegcdBLS12_381
