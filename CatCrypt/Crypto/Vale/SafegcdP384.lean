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
# Bernstein-Yang safegcd inversion over `Fp_{P-384}` (AUCurves leaf)

This module declares the AUCurves verified-CT Bernstein-Yang divstep
modular inversion for the NIST P-384 base field
`p = 2^384 − 2^128 − 2^96 + 2^32 − 1`, as an opaque verified-CT leaf
for CatCrypt's verified front, following the established extCall
pattern (`Jasmin.LowCT` `RCall`).

Sibling adoption to `Vale/SafegcdBLS12_381.lean` / `Vale/SafegcdP256.lean`
— the trust shape is the same `extCall` boundary; the upstream proof
bundle differs (P-384 prime constant; iteration count 15 outer × 59
inner = 885 divsteps; KAT via `x · x^{-1} ≡ 1 (mod p)` schoolbook
mul-mod).

## Scope (BY/safegcd wave-2, NIST P-curve sweep)

NIST P-384 powers TLS 1.3 ECDHE-ECDSA with the
`secp384r1` (P-384) named group (the higher-security tier of the open
Internet's TLS deployment), JWT signatures (RFC 7518 `ES384`), and
the CNSA Suite 2.0 transitional ciphersuites. Field inversion is the
hot inner step in ECDSA-P-384 verify (jacobian → affine
normalisation) and in protocol-level modular reductions.

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves(safegcd leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT inversion in Fp_{P-384}
```

CatCrypt's verified front discharges the orchestration (copy-in,
leaf call, copy-out via the typed reg-ptr ABI); the leaf's
denotation matches AUCurves' Bernstein-Yang divstep convergence
certificate; CT is inherited from the safegcd structure
(data-independent divsteps, fixed iteration count at compile time).

## The AUCurves / Bernstein-Yang provenance

* **Rust source**: `safegcd_p384.rs` (AUCurves, curve25519-jasmin-rs crate),
  function `p384_invert_divstep_sat(out: &mut [u64; 6], x: &[u64; 6])`.
  Computes `out = x^{-1} mod p` where `p` is the NIST P-384 prime.
* **Shared safegcd kernel**:
  `safegcd.rs` (AUCurves, curve25519-jasmin-rs crate) — Rust port
  of `libsecp256k1`'s `src/modinv64.c` (Peter Dettman, 2020, MIT),
  parameterised by const-generic limb count `N` so the same code body
  services all prime sizes. Bernstein-Yang δ₀=1/2; for P-384, 15 outer
  × 59 inner = 885 divsteps (paper Theorem 1 bound for `b = 384`:
  ⌈(9437 · 384 + 1) / 4096⌉ = 885 — exact match).
* **KAT**: `safegcd_p384.rs`'s `p384_invert_times_self_is_one` test
  exercises 4 deterministic non-zero inputs (incl. `p − 1`) and
  asserts `x · invert(x) ≡ 1 (mod p)` byte-identically via the
  in-file `mul_mod_p_6` schoolbook 6×6 → 12-limb mul-mod reference.
* **Algorithmic provenance**: Bernstein-Yang 2019 (eprint 2019/266),
  "Fast constant-time gcd computation and modular inversion",
  refined by Pornin 2020 (eprint 2020/972).

## Leaf C signature (Rust `extern "C"` shape, exposed by the bench shim)

```c
extern void safegcd_p384_invert(uint64_t out[6], const uint64_t x[6]);
```

That is: `out = x^{-1} mod p_{P-384}` over saturated radix-2^64 6×u64
inputs (48 bytes per operand). Returns `[0, …, 0]` for `x = 0`
(Bernstein-Yang convention).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **AUCurves_safegcd_p384_invert_denote**: the leaf computes
   `x^{-1} mod p`, `p = 2^384 − 2^128 − 2^96 + 2^32 − 1`, on
   canonical 6×u64 inputs. Discharged by AUCurves' Bernstein-Yang
   divstep correctness applied to `ModInfo<7>` constructed by
   `safegcd::modinfo_from_6u64(P384_P_6X64, 15)`, plus the in-file
   `x · invert(x) ≡ 1 (mod p)` round-trip KAT.

2. **AUCurves_safegcd_p384_invert_CT**: the leaf is constant-time
   in `x`. Sourced from the safegcd structure (fixed iteration count
   = 15 outer × 59 inner = 885 divsteps; per-step update is a
   sequence of conditional-multiplexed adds / shifts with no
   data-dependent branches or memory accesses). Stated as
   `SecretIndependent` of the leaf's leakage function; the citation is
   in `ValeCoqAxioms.lean`.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the AUCurves-extracted Rust code (via the per-bench
   `p384_safegcd_shim` staticlib). Standard C-linker trust.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is a hand-emitted Fermat addition chain over
`p − 2`, because:

* The Bernstein-Yang proof bounds 885 ≥ 878 divsteps sufficient to
  reach `(1, x^{-1})` from `(p, x)`; the algorithm is fully
  data-independent regardless of `x`'s bit pattern. The Fermat path
  is also CT but is ~2× slower on P-384 (≥2000 field mul/sqr in the
  addition chain vs ≤885 divsteps over 7-limb Signed62 internally).
-/

namespace CatCrypt.Crypto.Vale.SafegcdP384

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

The 48-byte NIST P-384 base-field element (6×u64 saturated LE on the
wire). Opaque — the concrete leaf at link time is the AUCurves Rust
symbol `safegcd_p384_invert`. -/

opaque P384FieldElt.Impl : NonemptyType.{0}
/-- A 48-byte NIST P-384 `Fp` field element (6×u64 saturated LE).
    Opaque; the concrete leaf is the AUCurves verified-CT
    `p384_invert_divstep_sat`. -/
def P384FieldElt : Type := P384FieldElt.Impl.type
instance : Nonempty P384FieldElt := P384FieldElt.Impl.property
/-- An inhabitant. -/
noncomputable opaque P384FieldElt.default : P384FieldElt
noncomputable instance : Inhabited P384FieldElt :=
  ⟨P384FieldElt.default⟩

/-! ## §2. AUCurves leaf: denotation, leakage, constant-time proposition

The leaf's denotation and leakage are opaque constants. Its constant-time
property is the proposition `AUCurves_safegcd_p384_invert_CT`, which a
theorem about the leaf takes as a hypothesis. Both are sourced from AUCurves'
`safegcd_p384.rs` upstream. -/

/-- **Denotation**: the AUCurves verified-CT
    `p384_invert_divstep_sat` leaf computes the modular inverse of
    its input over the NIST P-384 base prime
    `p = 2^384 − 2^128 − 2^96 + 2^32 − 1`. Discharged by
    Bernstein-Yang's divstep correctness theorem applied to
    `ModInfo<7>` constructed by
    `safegcd::modinfo_from_6u64(P384_P_6X64, 15)` (885 ≥ 878
    divsteps suffice for `b = 384`), and the round-trip KAT in
    `safegcd_p384.rs::tests::p384_invert_times_self_is_one`. -/
noncomputable opaque AUCurves_safegcd_p384_invert_denote
    (x : P384FieldElt) : P384FieldElt

/-- **Leakage function**: the observable trace the
    `p384_invert_divstep_sat` leaf emits on operand `x`. -/
noncomputable opaque AUCurves_safegcd_p384_invert_leak (x : P384FieldElt) : LeafLeak

/-- **Constant-time proposition**: the leakage trace of the AUCurves verified-CT
    `p384_invert_divstep_sat` leaf is the same at every operand `x`. The
    Bernstein-Yang divstep loop has a compile-time-fixed iteration count and
    the per-step update is conditional-multiplexed adds and shifts with no
    operand-dependent branch or memory access, so no execution of the leaf
    distinguishes two field elements. Cited in `ValeCoqAxioms.lean`. -/
def AUCurves_safegcd_p384_invert_CT : Prop :=
    SecretIndependent AUCurves_safegcd_p384_invert_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/SafegcdBLS12_381.lean` / `Vale/SafegcdP256.lean`
pattern: registering the leaf so the verified front accepts `RCall
"safegcd_p384_invert"` as a well-formed extCall whose argument shape is
`1 × TBytes 48` (one P-384 Fp element). -/

/-- Register `AUCurves_safegcd_p384_invert_denote` → leaf
    `safegcd_p384_invert` (the C symbol name, matching the
    `extern "C"` re-export of `p384_invert_divstep_sat` in the
    bench shim staticlib). -/
@[rust_cmd_pattern]
def safegcdP384Pattern : LowCTPattern where
  name      := "safegcd_p384_invert"
  fnHead    := ``AUCurves_safegcd_p384_invert_denote
  arity     := 1
  towerType := .TBytes 48   -- 48-byte P-384 Fp element (6×u64 saturated LE)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a NIST P-384 Fp element
    (`TBytes 48` — 48 bytes, the saturated 6×u64 packing). -/
def p384FieldEltTowerType : TowerType := .TBytes 48

/-! ## §5. `LeafSig` entry for the AUCurves leaf

The AUCurves safegcd leaf is **non-aliasing** at the SSA level:
`out` and `x` are distinct buffers in the Rust signature
(`&mut [u64; 6]` and `&[u64; 6]` borrow-check as distinct). We
declare `destAliasOk := []` (the conservative default). -/

/-- Per-leaf signature for `safegcd_p384_invert`: no aliasing
    permitted (out / x distinct in the Rust signature). -/
def safegcdP384LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "safegcd_p384_invert"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the NIST P-384 `Fp` inversion, serving as the
front-end input to the reflection pipeline. The body is the single
AUCurves-leaf call. -/

/-- One NIST P-384 `Fp` modular-inversion invocation. -/
noncomputable def safegcdP384InvertLean
    (x : P384FieldElt) : P384FieldElt :=
  AUCurves_safegcd_p384_invert_denote x

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `Vale/SafegcdBLS12_381.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `safegcdP384InvertLean`. Shape:
    `RSeq RSkip (RCall "safegcd_p384_invert" __result [x])`. -/
def safegcdP384InvertBody : LowCT :=
  let x_l      := loc "x"        p384FieldEltTowerType
  let result_l := loc "__result" p384FieldEltTowerType
  .RSeq .RSkip
    (.RCall "safegcd_p384_invert"
            result_l [x_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd P-384 leaf. -/
def safegcdP384InvertReified : ReifiedFunc :=
  { args    := [("x", p384FieldEltTowerType)]
    body    := safegcdP384InvertBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval safegcdP384InvertReified.args.map Prod.fst
  -- [x]
#eval safegcdP384InvertReified.args.length     -- 1
#eval safegcdP384InvertReified.retName         -- __result

end CatCrypt.Crypto.Vale.SafegcdP384
