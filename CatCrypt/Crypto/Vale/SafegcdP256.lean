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
# Bernstein-Yang safegcd inversion over `Fp_{P-256}` (AUCurves leaf)

This module declares the AUCurves verified-CT Bernstein-Yang divstep
modular inversion for the NIST P-256 base field
`p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, as an opaque verified-CT leaf
for CatCrypt's verified front, following the established extCall
pattern (`Jasmin.LowCT` `RCall`).

Sibling adoption to `Vale/SafegcdBLS12_381.lean` / `Vale/SafegcdSecp256k1.lean`
— the trust shape is the same `extCall` boundary; the upstream proof
bundle differs (P-256 prime constant; iteration count 10 outer × 59
inner = 590 divsteps; KAT cross-checked against fiat-crypto's per-step
`fiat_p256_divstep`).

## Scope (BY/safegcd wave-2, NIST P-curve sweep)

NIST P-256 powers TLS 1.3 server signatures (ECDSA P-256, the most
widely deployed signature ciphersuite on the open Internet today),
JWT signatures (RFC 7518 `ES256`), and the EMV smart-card ecosystem.
Field inversion is the hot inner step in the ECDSA verify path
(jacobian → affine normalisation) and in every modular reduction
chain that the formula encoding requires. CatCrypt's pre-pilot P-256
support routed through Fermat addition chains; the safegcd path
takes ~590 divsteps in place of ~1500+ field mul/sqr in the chain.

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves(safegcd leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT inversion in Fp_{P-256}
```

CatCrypt's verified front discharges the orchestration (copy-in,
leaf call, copy-out via the typed reg-ptr ABI); the leaf's
denotation matches AUCurves' Bernstein-Yang divstep convergence
certificate; CT is inherited from the safegcd structure
(data-independent divsteps, fixed iteration count at compile time).

## The AUCurves / Bernstein-Yang provenance

* **Rust source**: `safegcd_p256.rs` (AUCurves, curve25519-jasmin-rs crate),
  function `p256_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4])`.
  Computes `out = x^{-1} mod p` where `p` is the NIST P-256 prime.
* **Shared safegcd kernel**:
  `safegcd.rs` (AUCurves, curve25519-jasmin-rs crate) — Rust port
  of `libsecp256k1`'s `src/modinv64.c` (Peter Dettman, 2020, MIT),
  parameterised by const-generic limb count `N` so the same code body
  services all prime sizes. Bernstein-Yang δ₀=1/2; for P-256, 10 outer
  × 59 inner = 590 divsteps (paper §3.4, b = 256 lifts to the same
  divstep budget the libsecp256k1 baseline ships).
* **KAT cross-check**: `safegcd_p256.rs`'s
  `p256_divstep_matches_fiat_reference` test exercises 5 deterministic
  non-zero inputs (incl. `p − 1`) and asserts byte-identical equality
  with fiat-crypto's `fiat_p256_divstep` per-step reference (the
  machine-checked synthesis from `fiat-crypto/src/Bedrock/Field/Synthesis/`).
* **Cross-prover**: fiat-crypto's `fiat_p256_divstep` is the verified
  reference; AUCurves' batched 59-divstep step matches it to the bit.

## Leaf C signature (Rust `extern "C"` shape, exposed by the bench shim)

```c
extern void safegcd_p256_invert(uint64_t out[4], const uint64_t x[4]);
```

That is: `out = x^{-1} mod p_{P-256}` over saturated radix-2^64 4×u64
inputs (32 bytes per operand). Returns `[0, 0, 0, 0]` for `x = 0`
(Bernstein-Yang convention).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **AUCurves_safegcd_p256_invert_denote**: the leaf computes
   `x^{-1} mod p`, `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, on
   canonical 4×u64 inputs. Discharged by AUCurves' Bernstein-Yang
   divstep correctness applied to `ModInfo<5>` constructed by
   `safegcd::modinfo_from_4u64(P256_P_4X64, 10)`, plus the
   byte-identical KAT against fiat-crypto's `fiat_p256_divstep`.

2. **AUCurves_safegcd_p256_invert_CT**: the leaf is constant-time
   in `x`. Sourced from the safegcd structure (fixed iteration count
   = 10 outer × 59 inner = 590 divsteps; per-step update is a
   sequence of conditional-multiplexed adds / shifts with no
   data-dependent branches or memory accesses). Stated as
   `SecretIndependent` of the leaf's leakage function; the citation is
   in `ValeCoqAxioms.lean`.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the AUCurves-extracted Rust code (via the per-bench
   `p256_safegcd_shim` staticlib). Standard C-linker trust.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is a hand-emitted Fermat addition chain over
`p − 2`, because:

* The Bernstein-Yang proof bounds 590 divsteps sufficient to reach
  `(1, x^{-1})` from `(p, x)`; the algorithm is fully data-independent
  regardless of `x`'s bit pattern. The Fermat path is also CT but is
  ~2× slower on P-256 (≥1500 field mul/sqr in the addition chain vs
  ≤590 divsteps over 5-limb Signed62 internally).
* The KAT pin against fiat-crypto's per-step reference gives a
  cross-prover witness on identical inputs.
-/

namespace CatCrypt.Crypto.Vale.SafegcdP256

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

The 32-byte NIST P-256 base-field element (4×u64 saturated LE on the
wire). Opaque — the concrete leaf at link time is the AUCurves Rust
symbol `safegcd_p256_invert`. -/

opaque P256FieldElt.Impl : NonemptyType.{0}
/-- A 32-byte NIST P-256 `Fp` field element (4×u64 saturated LE).
    Opaque; the concrete leaf is the AUCurves verified-CT
    `p256_invert_divstep_sat`. -/
def P256FieldElt : Type := P256FieldElt.Impl.type
instance : Nonempty P256FieldElt := P256FieldElt.Impl.property
/-- An inhabitant. -/
noncomputable opaque P256FieldElt.default : P256FieldElt
noncomputable instance : Inhabited P256FieldElt :=
  ⟨P256FieldElt.default⟩

/-! ## §2. AUCurves-leaf axioms (the trust delta)

These are the two axioms we add to CatCrypt's axiom budget when we
permit the AUCurves BY/safegcd P-256 leaf into the pipeline. Each is
sourced from AUCurves' `safegcd_p256.rs` upstream. -/

/-- **Denotation axiom**: the AUCurves verified-CT
    `p256_invert_divstep_sat` leaf computes the modular inverse of
    its input over the NIST P-256 base prime
    `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`. Discharged by
    Bernstein-Yang's divstep correctness theorem applied to
    `ModInfo<5>` constructed by
    `safegcd::modinfo_from_4u64(P256_P_4X64, 10)` and the
    byte-identical KAT in
    `safegcd_p256.rs::tests::p256_divstep_matches_fiat_reference`
    against fiat-crypto's `fiat_p256_divstep` per-step reference. -/
noncomputable opaque AUCurves_safegcd_p256_invert_denote
    (x : P256FieldElt) : P256FieldElt

/-- **Leakage function**: the observable trace the
    `p256_invert_divstep_sat` leaf emits on operand `x`. -/
noncomputable opaque AUCurves_safegcd_p256_invert_leak (x : P256FieldElt) : LeafLeak

/-- **Constant-time axiom**: the leakage trace of the AUCurves verified-CT
    `p256_invert_divstep_sat` leaf is the same at every operand `x`. The
    Bernstein-Yang divstep loop runs 10 outer × 59 inner iterations fixed at
    compile time, and the per-step update is conditional-multiplexed adds and
    shifts with no operand-dependent branch or memory access, so no execution
    of the leaf distinguishes two field elements. Cited in
    `ValeCoqAxioms.lean`. -/
axiom AUCurves_safegcd_p256_invert_CT :
    SecretIndependent AUCurves_safegcd_p256_invert_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/SafegcdBLS12_381.lean` / `Vale/SafegcdSecp256k1.lean`
pattern: registering the leaf so the verified front accepts `RCall
"safegcd_p256_invert"` as a well-formed extCall whose argument shape is
`1 × TBytes 32` (one P-256 Fp element). -/

/-- Register `AUCurves_safegcd_p256_invert_denote` → leaf
    `safegcd_p256_invert` (the C symbol name, matching the
    `extern "C"` re-export of `p256_invert_divstep_sat` in the
    bench shim staticlib). -/
@[rust_cmd_pattern]
def safegcdP256Pattern : LowCTPattern where
  name      := "safegcd_p256_invert"
  fnHead    := ``AUCurves_safegcd_p256_invert_denote
  arity     := 1
  towerType := .TBytes 32   -- 32-byte P-256 Fp element (4×u64 saturated LE)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a NIST P-256 Fp element
    (`TBytes 32` — 32 bytes, the saturated 4×u64 packing). -/
def p256FieldEltTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry for the AUCurves leaf

The AUCurves safegcd leaf is **non-aliasing** at the SSA level:
`out` and `x` are distinct buffers in the Rust signature
(`&mut [u64; 4]` and `&[u64; 4]` borrow-check as distinct). We
declare `destAliasOk := []` (the conservative default). -/

/-- Per-leaf signature for `safegcd_p256_invert`: no aliasing
    permitted (out / x distinct in the Rust signature). -/
def safegcdP256LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "safegcd_p256_invert"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the NIST P-256 `Fp` inversion, serving as the
front-end input to the reflection pipeline. The body is the single
AUCurves-leaf call. -/

/-- One NIST P-256 `Fp` modular-inversion invocation. -/
noncomputable def safegcdP256InvertLean
    (x : P256FieldElt) : P256FieldElt :=
  AUCurves_safegcd_p256_invert_denote x

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `Vale/SafegcdBLS12_381.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `safegcdP256InvertLean`. Shape:
    `RSeq RSkip (RCall "safegcd_p256_invert" __result [x])`. -/
def safegcdP256InvertBody : LowCT :=
  let x_l      := loc "x"        p256FieldEltTowerType
  let result_l := loc "__result" p256FieldEltTowerType
  .RSeq .RSkip
    (.RCall "safegcd_p256_invert"
            result_l [x_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd P-256 leaf. -/
def safegcdP256InvertReified : ReifiedFunc :=
  { args    := [("x", p256FieldEltTowerType)]
    body    := safegcdP256InvertBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval safegcdP256InvertReified.args.map Prod.fst
  -- [x]
#eval safegcdP256InvertReified.args.length     -- 1
#eval safegcdP256InvertReified.retName         -- __result

end CatCrypt.Crypto.Vale.SafegcdP256
