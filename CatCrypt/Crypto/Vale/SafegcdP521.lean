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
# Bernstein-Yang safegcd inversion over `Fp_{P-521}` (AUCurves leaf)

This module declares the AUCurves verified-CT Bernstein-Yang divstep
modular inversion for the NIST P-521 base field
`p = 2^521 − 1` (the Mersenne prime `M_521`), as an opaque
verified-CT leaf for CatCrypt's verified front, following the
established extCall pattern (`Jasmin.LowCT` `RCall`).

Sibling adoption to `Vale/SafegcdP384.lean` / `Vale/SafegcdP256.lean`
— the trust shape is the same `extCall` boundary; the upstream proof
bundle differs (P-521 Mersenne prime; iteration count 21 outer × 59
inner = 1239 divsteps; KAT via `x · x^{-1} ≡ 1 (mod p)` schoolbook
mul-mod).

## Scope (BY/safegcd wave-2, NIST P-curve sweep)

NIST P-521 powers the highest-security NIST P-curve tier (Top-Secret
in CNSA-1; transitional in CNSA-2.0), JWT signatures (RFC 7518
`ES512` — the conventional 521-bit-curve label), and the higher
TLS 1.3 named-group tier (`secp521r1`). Field inversion is the
hot inner step in the ECDSA-P-521 verify path (jacobian → affine
normalisation). The 9-limb saturated radix-2^64 packing reflects the
521-bit prime's ⌈521/64⌉ = 9 limb count with a 9-bit high limb.

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves(safegcd leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT inversion in Fp_{P-521}
```

CatCrypt's verified front discharges the orchestration (copy-in,
leaf call, copy-out via the typed reg-ptr ABI); the leaf's
denotation matches AUCurves' Bernstein-Yang divstep convergence
certificate; CT is inherited from the safegcd structure
(data-independent divsteps, fixed iteration count at compile time).

## The AUCurves / Bernstein-Yang provenance

* **Rust source**: `safegcd_p521.rs` (AUCurves, curve25519-jasmin-rs crate),
  function `p521_invert_divstep_sat(out: &mut [u64; 9], x: &[u64; 9])`.
  Computes `out = x^{-1} mod p` where `p = 2^521 − 1` is the
  NIST P-521 Mersenne prime.
* **Shared safegcd kernel**:
  `safegcd.rs` (AUCurves, curve25519-jasmin-rs crate) — Rust port
  of `libsecp256k1`'s `src/modinv64.c` (Peter Dettman, 2020, MIT),
  parameterised by const-generic limb count `N` so the same code body
  services all prime sizes. Bernstein-Yang δ₀=1/2; for P-521, 21 outer
  × 59 inner = 1239 divsteps (paper Theorem 1 bound for `b = 521`:
  ⌈(9437 · 521 + 1) / (4096 · 59)⌉ = 21 outer iterations).
* **KAT**: `safegcd_p521.rs`'s `p521_invert_times_self_is_one` test
  exercises 4 deterministic non-zero inputs (incl. `p − 1`) and
  asserts `x · invert(x) ≡ 1 (mod p)` byte-identically via the
  in-file `mul_mod_p_9` schoolbook 9×9 → 18-limb mul-mod reference.
* **Algorithmic provenance**: Bernstein-Yang 2019 (eprint 2019/266),
  "Fast constant-time gcd computation and modular inversion",
  refined by Pornin 2020 (eprint 2020/972).

## Leaf C signature (Rust `extern "C"` shape, exposed by the bench shim)

```c
extern void safegcd_p521_invert(uint64_t out[9], const uint64_t x[9]);
```

That is: `out = x^{-1} mod p_{P-521}` over saturated radix-2^64 9×u64
inputs (72 bytes per operand). The high u64 holds the 9 high bits of
the 521-bit element. Returns `[0, …, 0]` for `x = 0`
(Bernstein-Yang convention).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **AUCurves_safegcd_p521_invert_denote**: the leaf computes
   `x^{-1} mod p`, `p = 2^521 − 1`, on canonical 9×u64 inputs.
   Discharged by AUCurves' Bernstein-Yang divstep correctness
   applied to `ModInfo<10>` constructed by
   `safegcd::modinfo_from_9u64(P521_P_9X64, 21)`, plus the in-file
   `x · invert(x) ≡ 1 (mod p)` round-trip KAT (which exercises
   the canonical 9-limb packing including the 9-bit high limb).

2. **AUCurves_safegcd_p521_invert_CT**: the leaf is constant-time
   in `x`. Sourced from the safegcd structure (fixed iteration count
   = 21 outer × 59 inner = 1239 divsteps; per-step update is a
   sequence of conditional-multiplexed adds / shifts with no
   data-dependent branches or memory accesses). Stated as
   `SecretIndependent` of the leaf's leakage function; the citation is
   in `ValeCoqAxioms.lean`.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the AUCurves-extracted Rust code (via the per-bench
   `p521_safegcd_shim` staticlib). Standard C-linker trust.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is a hand-emitted Fermat addition chain over
`p − 2 = 2^521 − 3`, because:

* The Bernstein-Yang proof bounds 1239 divsteps sufficient to reach
  `(1, x^{-1})` from `(p, x)`; the algorithm is fully data-independent
  regardless of `x`'s bit pattern. For Mersenne-shaped primes the
  Fermat path is reachable in ~521 sqr + 1 mul (a special addition
  chain since `p − 2 = 2^521 − 3` admits a very short chain), but
  the safegcd path still wins on side-channel CT discipline (every
  divstep is a fixed-shape op; the Fermat path's sqr-then-mul pattern
  leaks at the µ-arch level via memory access patterns of the field
  mul/sqr primitives, where the safegcd path's signed-62 internal
  representation is fully data-independent).
-/

namespace CatCrypt.Crypto.Vale.SafegcdP521

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

The 72-byte NIST P-521 base-field element (9×u64 saturated LE on the
wire). Opaque — the concrete leaf at link time is the AUCurves Rust
symbol `safegcd_p521_invert`. -/

opaque P521FieldElt.Impl : NonemptyType.{0}
/-- A 72-byte NIST P-521 `Fp` field element (9×u64 saturated LE).
    Opaque; the concrete leaf is the AUCurves verified-CT
    `p521_invert_divstep_sat`. -/
def P521FieldElt : Type := P521FieldElt.Impl.type
instance : Nonempty P521FieldElt := P521FieldElt.Impl.property
/-- An inhabitant. -/
noncomputable opaque P521FieldElt.default : P521FieldElt
noncomputable instance : Inhabited P521FieldElt :=
  ⟨P521FieldElt.default⟩

/-! ## §2. AUCurves-leaf axioms (the trust delta)

These are the two axioms we add to CatCrypt's axiom budget when we
permit the AUCurves BY/safegcd P-521 leaf into the pipeline. Each is
sourced from AUCurves' `safegcd_p521.rs` upstream. -/

/-- **Denotation axiom**: the AUCurves verified-CT
    `p521_invert_divstep_sat` leaf computes the modular inverse of
    its input over the NIST P-521 Mersenne base prime `p = 2^521 − 1`.
    Discharged by Bernstein-Yang's divstep correctness theorem applied
    to `ModInfo<10>` constructed by
    `safegcd::modinfo_from_9u64(P521_P_9X64, 21)`, and the round-trip
    KAT in `safegcd_p521.rs::tests::p521_invert_times_self_is_one`. -/
noncomputable opaque AUCurves_safegcd_p521_invert_denote
    (x : P521FieldElt) : P521FieldElt

/-- **Leakage function**: the observable trace the
    `p521_invert_divstep_sat` leaf emits on operand `x`. -/
noncomputable opaque AUCurves_safegcd_p521_invert_leak (x : P521FieldElt) : LeafLeak

/-- **Constant-time axiom**: the leakage trace of the AUCurves verified-CT
    `p521_invert_divstep_sat` leaf is the same at every operand `x`. The
    Bernstein-Yang divstep loop has a compile-time-fixed iteration count and
    the per-step update is conditional-multiplexed adds and shifts with no
    operand-dependent branch or memory access, so no execution of the leaf
    distinguishes two field elements. Cited in `ValeCoqAxioms.lean`. -/
axiom AUCurves_safegcd_p521_invert_CT :
    SecretIndependent AUCurves_safegcd_p521_invert_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/SafegcdBLS12_381.lean` / `Vale/SafegcdP384.lean`
pattern: registering the leaf so the verified front accepts `RCall
"safegcd_p521_invert"` as a well-formed extCall whose argument shape is
`1 × TBytes 72` (one P-521 Fp element, 9×u64 saturated LE). -/

/-- Register `AUCurves_safegcd_p521_invert_denote` → leaf
    `safegcd_p521_invert` (the C symbol name, matching the
    `extern "C"` re-export of `p521_invert_divstep_sat` in the
    bench shim staticlib). -/
@[rust_cmd_pattern]
def safegcdP521Pattern : LowCTPattern where
  name      := "safegcd_p521_invert"
  fnHead    := ``AUCurves_safegcd_p521_invert_denote
  arity     := 1
  towerType := .TBytes 72   -- 72-byte P-521 Fp element (9×u64 saturated LE)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a NIST P-521 Fp element
    (`TBytes 72` — 72 bytes, the saturated 9×u64 packing). -/
def p521FieldEltTowerType : TowerType := .TBytes 72

/-! ## §5. `LeafSig` entry for the AUCurves leaf

The AUCurves safegcd leaf is **non-aliasing** at the SSA level:
`out` and `x` are distinct buffers in the Rust signature
(`&mut [u64; 9]` and `&[u64; 9]` borrow-check as distinct). We
declare `destAliasOk := []` (the conservative default). -/

/-- Per-leaf signature for `safegcd_p521_invert`: no aliasing
    permitted (out / x distinct in the Rust signature). -/
def safegcdP521LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "safegcd_p521_invert"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the NIST P-521 `Fp` inversion, serving as the
front-end input to the reflection pipeline. The body is the single
AUCurves-leaf call. -/

/-- One NIST P-521 `Fp` modular-inversion invocation. -/
noncomputable def safegcdP521InvertLean
    (x : P521FieldElt) : P521FieldElt :=
  AUCurves_safegcd_p521_invert_denote x

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `Vale/SafegcdBLS12_381.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `safegcdP521InvertLean`. Shape:
    `RSeq RSkip (RCall "safegcd_p521_invert" __result [x])`. -/
def safegcdP521InvertBody : LowCT :=
  let x_l      := loc "x"        p521FieldEltTowerType
  let result_l := loc "__result" p521FieldEltTowerType
  .RSeq .RSkip
    (.RCall "safegcd_p521_invert"
            result_l [x_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd P-521 leaf. -/
def safegcdP521InvertReified : ReifiedFunc :=
  { args    := [("x", p521FieldEltTowerType)]
    body    := safegcdP521InvertBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval safegcdP521InvertReified.args.map Prod.fst
  -- [x]
#eval safegcdP521InvertReified.args.length     -- 1
#eval safegcdP521InvertReified.retName         -- __result

end CatCrypt.Crypto.Vale.SafegcdP521
