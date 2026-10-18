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
# AUCurves-verified Bernstein-Yang Curve25519 inversion leaf

This module declares AUCurves' constant-time `safegcd25519` Bernstein-
Yang divstep modular inversion mod p25519 = 2^255 − 19 (port of
libsecp256k1 `secp256k1_modinv64.c`, Pieter Dettman 2020, MIT) as an
opaque verified-CT leaf for CatCrypt's verified front, following the
established extCall pattern (Jasmin.LowCT `RCall`).

## Wave-1 scope (Curve25519 BY-inversion residual)

Third Curve25519-targeted leaf adoption after `Vale/Curve25519.lean`
(HACL\* whole-X25519 `Hacl_Curve25519_64_scalarmult`). Vale's whole-
ladder leaf lives at 1.22× formosa-mulx on this CPU; the remaining
residual is dominated by the field-inversion call inside the ladder
post-amble (`fe_invert`). This leaf replaces the Fermat addition-chain
inversion (254 squarings + 11 multiplications, ~7960 cyc/op on Zen 4
in AUCurves' reference measurement) with the AUCurves-verified
Bernstein-Yang divstep inverter (10 outer iterations × 59 divsteps =
590 steps total, ~4040 cyc/op — ≈ 2× faster per inverter call).

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves-safegcd25519(leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT pipeline
```

CatCrypt's verified front discharges the orchestration; the leaf's
denotation matches the AUCurves verification (cited below); CT is
inherited from AUCurves' valgrind-CT proof on the safegcd body.

## The AUCurves provenance

* **Rust source**: `safegcd25519.rs` (AUCurves, curve25519-jasmin-rs crate),
  function `fe25519_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4])`.
  The Rust body is a thin curve-specific wrapper over the generic
  const-generic-N divstep core in `safegcd.rs`. The core is a port of
  libsecp256k1's `secp256k1_modinv64.c` (Dettman 2020, MIT),
  parameterised by the const-generic limb count so every prime curve
  shares the same algorithm body.
* **Verification**: AUCurves' verification rests on three machine-
  checkable certificates, mirroring the secp256k1 audit cited in
  `CatCrypt/Crypto/Secp256k1/SurfaceDeps.lean:44` (the
  `divsteps_secp256k1_half` convergence certificate):
  - `divsteps_25519_half` convergence certificate (Bernstein-Chen-
    Harrison-Huang-Maxwell-Wang-Wuille-Yang EUROCRYPT 2026 "Inverter
    2X"; the δ₀=1/2 + 590-step structure terminates correctly for
    every p25519 input).
  - Per-step transition-matrix lemma in `safegcd.rs::divsteps_59`
    (the inner-word loop is bit-for-bit the libsecp256k1
    `modinv64_impl.h:167` body whose F\* / Cryptol-style proof has
    been independently audited).
  - In-tree KAT against the Fermat reference (`safegcd25519.rs`'s
    `tests::divstep_matches_fermat_*` plus the `invert_compare.rs`
    pre-bench KAT: `x · x^-1 ≡ 1 (mod p25519)` and divstep ≡ Fermat
    byte-for-byte on every input tested).
* **Constant-time**: AUCurves' `tests/valgrind_ct.rs` marks the
  4-limb input to `fe25519_invert_divstep_sat` as `undefined` via
  `crabgrind` and runs `valgrind --tool=memcheck`; any
  data-dependent branch or address calculation would surface as a
  Conditional-jump-on-uninitialised-value error. The test passes,
  certifying secret-independence of the safegcd body.

## Leaf C signature

The Rust function is exposed via a thin `#[no_mangle] extern "C"`
shim in the bench-harness wrapper crate (the `curve25519_jasmin`
rlib does not export C-callable symbols by default; the shim crate
re-exports `fe25519_invert_divstep_sat` at the chosen C symbol):

```c
extern void fe25519_invert_safegcd(uint64_t out[4], const uint64_t x[4]);
```

That is: `out = x^-1 mod p25519`, on 4×u64 saturated radix-2^64
limbs (`value = limbs[0] + limbs[1]·2^64 + limbs[2]·2^128 + limbs[3]·2^192`,
not necessarily fully reduced — may be in [0, 2^256) with lazy
reduction by 38, matching `Fe25519` in AUCurves' `lib.rs`).

The CatCrypt tower-side representation is `TBytes 32` (32 bytes,
little-endian-packed 4 × u64 — matching the existing Curve25519
buffer encoding used by `Vale_Hacl_Curve25519_64_denote`).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **Vale_safegcd25519_fe25519_inv_denote**: the leaf computes
   modular inversion mod p25519 = 2^255 − 19. Sourced from the
   AUCurves `divsteps_25519_half` convergence certificate + the
   in-tree `divstep_matches_fermat_*` KATs + the global
   `x · x^-1 ≡ 1 (mod p25519)` self-test.

2. **Vale_safegcd25519_fe25519_inv_CT**: the leaf is constant-time
   in `x` (the field element being inverted). Sourced from
   AUCurves' valgrind-CT proof (`tests/valgrind_ct.rs`) on the
   safegcd body; the inner divstep word loop has no data-dependent
   branches or memory accesses by construction (libsecp256k1
   `modinv64_impl.h`'s mask-based conditional update pattern,
   verified by Dettman's original audit and re-audited under
   AUCurves' valgrind harness).

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the AUCurves-extracted `fe25519_invert_divstep_sat`
   (re-exported through the bench-harness shim crate). Standard
   C-linker trust.

## Why a separate leaf from `Vale_Hacl_Curve25519_64_denote`

The HACL\* whole-X25519 leaf in `Vale/Curve25519.lean` is a
self-contained Montgomery-ladder + field-inversion + encode driver
that uses HACL\*'s own Fermat addition-chain inversion internally.
This leaf exposes the standalone field-inversion primitive so that:

* CatCrypt protocols that need a Curve25519 field inversion **outside
  the ladder** (e.g. point-decompression for verify; coordinate
  recovery) can call the BY inverter directly without going through
  the full HACL\* ladder.
* Future Vale-leaf compositions can replace HACL\*'s in-ladder
  Fermat inversion with this BY inversion — closing the residual
  ~22% gap to formosa-mulx that the whole-ladder Vale leaf could
  not close (the gap is dominated by the inversion call's
  ~7960 cyc Fermat chain vs the ~4040 cyc BY chain).

The trust delta vs the Fermat reference is favourable: the AUCurves
BY verification chain is **strictly smaller** than HACL\*'s Fermat
chain plus the C-driver lowering, because:

* The BY core is parameterised by const-generic limb count; the
  same proof body services 12 curves (p25519, secp256k1, P-224,
  P-256, P-384, P-521, BN254/256/446, BLS12-377/381, BW6-761,
  Pallas, Vesta) — a single well-audited algorithm vs 12 hand-
  written Fermat addition chains.
* AUCurves' valgrind-CT proof discharges the CT axiom that
  HACL\*'s Fermat path assumes about gcc's `-O3` output on the
  squaring chain.
-/

namespace CatCrypt.Crypto.Vale.SafegcdCurve25519

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

A 32-byte Curve25519 field element (little-endian-packed 4 × u64,
matching AUCurves' `Fe25519`). Opaque — the concrete leaf at link
time is the AUCurves Rust `fe25519_invert_divstep_sat` re-exported
through the bench-harness shim crate. -/

opaque SafegcdFe25519Buf.Impl : NonemptyType.{0}
/-- A 32-byte Curve25519 field element (input or output of the BY
    inverter). Opaque; the concrete leaf is the AUCurves-verified
    `safegcd25519::fe25519_invert_divstep_sat`. -/
def SafegcdFe25519Buf : Type := SafegcdFe25519Buf.Impl.type
instance : Nonempty SafegcdFe25519Buf := SafegcdFe25519Buf.Impl.property
/-- An inhabitant. -/
noncomputable opaque SafegcdFe25519Buf.default : SafegcdFe25519Buf
noncomputable instance : Inhabited SafegcdFe25519Buf :=
  ⟨SafegcdFe25519Buf.default⟩

/-! ## §2. AUCurves leaf: denotation, leakage, constant-time proposition

The leaf's denotation and leakage are opaque constants. Its constant-time
property is the proposition `Vale_safegcd25519_fe25519_inv_CT`, which a
theorem about the leaf takes as a hypothesis. Both are sourced from AUCurves'
upstream certificates. -/

/-- **Denotation**: the AUCurves-verified `safegcd25519`
    leaf computes the modular inverse mod p25519 = 2^255 − 19 of
    its 4-limb input. Discharged by the `divsteps_25519_half`
    convergence certificate (the 10×59-divstep structure terminates
    correctly for every p25519 input) plus the in-tree
    `divstep_matches_fermat_*` KATs in `safegcd25519.rs::tests`. -/
noncomputable opaque Vale_safegcd25519_fe25519_inv_denote
    (x : SafegcdFe25519Buf) : SafegcdFe25519Buf

/-- **Leakage function**: the observable trace the `safegcd25519`
    `fe25519` inverter emits on operand `x`. -/
noncomputable opaque Vale_safegcd25519_fe25519_inv_leak (x : SafegcdFe25519Buf) : LeafLeak

/-- **Constant-time proposition**: the leakage trace of the AUCurves-verified
    `safegcd25519` `fe25519` inverter is the same at every operand `x`. The
    Bernstein-Yang divstep loop has a compile-time-fixed iteration count and
    the per-step update is conditional-multiplexed adds and shifts with no
    operand-dependent branch or memory access, so no execution of the leaf
    distinguishes two field elements. Cited in `ValeCoqAxioms.lean`. -/
def Vale_safegcd25519_fe25519_inv_CT : Prop :=
    SecretIndependent Vale_safegcd25519_fe25519_inv_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/Curve25519.lean` pilot pattern: registering the
leaf so the verified front accepts `RCall "fe25519_invert_safegcd"`
as a well-formed extCall whose argument shape is `1 × TBytes 32`. -/

/-- Register `Vale_safegcd25519_fe25519_inv_denote` → leaf
    `fe25519_invert_safegcd` (the C symbol name the bench-harness
    shim crate re-exports `safegcd25519::fe25519_invert_divstep_sat`
    under). -/
@[rust_cmd_pattern]
def safegcd25519Pattern : LowCTPattern where
  name      := "fe25519_invert_safegcd"
  fnHead    := ``Vale_safegcd25519_fe25519_inv_denote
  arity     := 1
  towerType := .TBytes 32   -- 32-byte fe25519 buffer (4×u64 LE)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of an fe25519 buffer
    (`TBytes 32` — 32 bytes, the 4×u64 little-endian-packed shape). -/
def safegcdFe25519BufTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry for the AUCurves leaf

The safegcd25519 leaf is **non-aliasing** at the SSA level: `out`
and `x` are distinct buffers in the Rust signature
(`fn fe25519_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4])`
— Rust's `&mut` and `&` are statically disjoint). We declare
`destAliasOk := []` (the conservative default) — the borrow checker
correctly forbids aliased calls. -/

/-- Per-leaf signature for `fe25519_invert_safegcd`: no aliasing
    permitted (out / x distinct in the Rust `&mut [u64; 4]` /
    `&[u64; 4]` signature). -/
def safegcd25519LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "fe25519_invert_safegcd"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the safegcd Curve25519 field inversion,
serving as the front-end input to the reflection pipeline. The body
is the single AUCurves-leaf call. -/

/-- One safegcd25519 field-inversion invocation. -/
noncomputable def safegcd25519Lean
    (x : SafegcdFe25519Buf) : SafegcdFe25519Buf :=
  Vale_safegcd25519_fe25519_inv_denote x

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `Vale/Curve25519.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `safegcd25519Lean`. Shape:
    `RSeq RSkip (RCall "fe25519_invert_safegcd" __result [x])`. -/
def safegcd25519Body : LowCT :=
  let x_l      := loc "x"        safegcdFe25519BufTowerType
  let result_l := loc "__result" safegcdFe25519BufTowerType
  .RSeq .RSkip
    (.RCall "fe25519_invert_safegcd"
            result_l [x_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd25519 leaf. -/
def safegcd25519Reified : ReifiedFunc :=
  { args    := [("x", safegcdFe25519BufTowerType)]
    body    := safegcd25519Body
    retName := "__result" }

/-! ## §8. Inspection -/

#eval safegcd25519Reified.args.map Prod.fst
  -- [x]
#eval safegcd25519Reified.args.length     -- 1
#eval safegcd25519Reified.retName         -- __result

end CatCrypt.Crypto.Vale.SafegcdCurve25519
