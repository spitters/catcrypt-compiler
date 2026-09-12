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
# AUCurves-verified Bernstein–Yang safegcd inversion for secp256k1's base prime

This module declares the AUCurves verified-CT Bernstein–Yang divstep
modular inversion mod the secp256k1 base prime
`p = 2^256 − 2^32 − 977` as an opaque verified-CT leaf for CatCrypt's
verified front, following the established extCall pattern
(`Jasmin.LowCT` `RCall`), used previously for the HACL\*/Vale
Curve25519, ChaCha20-Vec256, SHA-256, SHA-512, GHASH-CLMUL and AES-GCM
leaves.

## Scope (BY/safegcd adoption sweep, wave 1)

This is the **secp256k1** entry in the safegcd adoption sweep. The same
leaf shape extends to the sibling per-curve safegcd entry points
exposed by AUCurves (`safegcd25519`, `safegcd_p256`, `safegcd_p224`,
`safegcd_bn254`, `safegcd_bls12_381`, …) which share the divstep core.

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves(safegcd leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT pipeline
```

CatCrypt's verified front discharges the orchestration (typed reg-ptr
ABI: copy-in, leaf call, copy-out); the leaf's denotation matches the
AUCurves machine-checked convergence certificate (cited below); CT is
inherited from the safegcd structure (data-independent divsteps).

## Provenance

* **Rust source**:
  `safegcd_secp256k1.rs` (AUCurves, curve25519-jasmin-rs crate),
  function `secp_invert_divstep_sat(out: &mut [u64;4], x: &[u64;4])`.
  Computes `out = x^{-1} mod p` where
  `p = 2^256 − 2^32 − 977`.
* **Generic safegcd core**:
  `safegcd.rs` (AUCurves, curve25519-jasmin-rs crate) — a Rust
  port of `libsecp256k1`'s `src/modinv64.c` (Peter Dettman, 2020, MIT),
  parameterised by const-generic limb count `N` so the same code body
  services all prime sizes. Bernstein–Yang δ₀=1/2, 10 outer × 59
  divsteps = 590 (paper §3.4, b=256); matches what `libsecp256k1`
  itself ships.
* **Convergence certificate**: AUCurves' machine-checked
  `divsteps_secp256k1_half` proof
  (`AUCurves/src/Arithmetic/safegcd/divsteps_secp256k1_half.v`) — the
  Coq-verified bound that `gcd(f, g)` is reached within the chosen
  iteration count on inputs `f = p`, `g ∈ [0, p)`.
* **Self-test KAT**:
  `safegcd_secp256k1.rs`'s `secp_invert_times_self_is_one` test
  exercises 5 deterministic non-zero inputs (incl. `p − 1`); the
  product `x · x^{-1}` reduces to `[1, 0, 0, 0]` byte-identically using
  the in-file `mul_mod_secp` 4×4→8 limb schoolbook plus the
  `2^256 ≡ 2^32 + 977` reduction.
* **Cross-check**: `libsecp256k1`'s `secp256k1_fe_inv` is the bit-exact
  reference for the bench harness (production Bitcoin field inversion
  baseline, `bench_refs/secp256k1/src/field_impl.h`).

## Leaf C signature (the shim, exposed by the bench's Rust staticlib)

```c
extern void safegcd_secp256k1_invert(uint64_t out[4], const uint64_t x[4]);
```

That is: `out = x^{-1} mod p` over saturated radix-2^64 4×u64 inputs.
Returns `[0,0,0,0]` for `x = 0` (Bernstein–Yang convention).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **AUCurves_safegcd_secp256k1_invert_denote**: the leaf computes
   `x^{-1} mod p`, `p = 2^256 − 2^32 − 977`, on canonical 4×u64
   inputs. Discharged by AUCurves' `divsteps_secp256k1_half`
   convergence certificate plus the structural correspondence between
   the Coq/bedrock2 verified divstep transition and the Rust port in
   `safegcd.rs` (the same per-step matrix update, same termination
   bound).

2. **AUCurves_safegcd_secp256k1_invert_CT**: the leaf is constant-time
   in `x`. Sourced from the safegcd structure (fixed iteration count;
   the divstep update is a sequence of conditional-multiplexed adds /
   shifts with no data-dependent branches or memory accesses), which
   matches `libsecp256k1`'s CT discipline for the same algorithm.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the AUCurves-extracted Rust code (via the per-bench
   `secp256k1_safegcd_shim` staticlib). Standard C-linker trust.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is a hand-emitted Bernstein–Yang inverter we
have not yet proved against the convergence certificate.
-/

namespace CatCrypt.Crypto.Vale.SafegcdSecp256k1

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

The 32-byte secp256k1 base-field element (saturated 4×u64
little-endian). Opaque — the concrete leaf at link time is the
AUCurves-extracted Rust function `safegcd_secp256k1_invert`. -/

/-- A 32-byte secp256k1 base-field element (4×u64 saturated radix-2^64,
    little-endian). Opaque; the concrete leaf is the AUCurves
    Bernstein–Yang verified inverter
    `safegcd_secp256k1::secp_invert_divstep_sat`. -/
axiom Secp256k1FieldElt : Type
/-- Axiomatic inhabitant. -/
axiom Secp256k1FieldElt.default : Secp256k1FieldElt
noncomputable instance : Inhabited Secp256k1FieldElt :=
  ⟨Secp256k1FieldElt.default⟩

/-! ## §2. AUCurves-leaf axioms (the trust delta)

These are the two axioms we add to CatCrypt's axiom budget when we
permit the AUCurves safegcd-secp256k1 leaf. Each is sourced from
AUCurves' upstream machine-checked Coq proofs. -/

/-- **Denotation axiom**: the AUCurves
    `safegcd_secp256k1::secp_invert_divstep_sat` leaf computes
    `x^{-1} mod p` where `p = 2^256 − 2^32 − 977` is the secp256k1
    base prime. Discharged by the Coq-verified
    `divsteps_secp256k1_half` convergence certificate
    (`AUCurves/src/Arithmetic/safegcd/divsteps_secp256k1_half.v`) plus
    the structural correspondence between the bedrock2 divstep
    transition and the Rust port (`safegcd.rs` :: `divstep62`). -/
axiom AUCurves_safegcd_secp256k1_invert_denote
    (x : Secp256k1FieldElt) : Secp256k1FieldElt

/-- **Leakage function**: the observable trace the
    `safegcd_secp256k1::secp_invert_divstep_sat` leaf emits on operand
    `x`. -/
axiom AUCurves_safegcd_secp256k1_invert_leak (x : Secp256k1FieldElt) : LeafLeak

/-- **Constant-time axiom**: the leakage trace of the AUCurves verified-CT
    `secp256k1_invert_divstep_sat` leaf is the same at every operand `x`. The
    Bernstein-Yang divstep loop has a compile-time-fixed iteration count and
    the per-step update is conditional-multiplexed adds and shifts with no
    operand-dependent branch or memory access, so no execution of the leaf
    distinguishes two field elements. Cited in `ValeCoqAxioms.lean`. -/
axiom AUCurves_safegcd_secp256k1_invert_CT :
    SecretIndependent AUCurves_safegcd_secp256k1_invert_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/Curve25519.lean` / `Vale/ChaCha20Vec256.lean` /
`Vale/SHA256.lean` pattern: registering the leaf so the verified
front accepts `RCall "safegcd_secp256k1_invert"` as a well-formed
extCall whose argument shape is `1 × TBytes 32`. -/

/-- Register `AUCurves_safegcd_secp256k1_invert_denote` → leaf
    `safegcd_secp256k1_invert` (the C symbol name, matching the
    `extern "C"` re-export of `secp_invert_divstep_sat` in the bench
    shim staticlib). -/
@[rust_cmd_pattern]
def safegcdSecp256k1Pattern : LowCTPattern where
  name      := "safegcd_secp256k1_invert"
  fnHead    := ``AUCurves_safegcd_secp256k1_invert_denote
  arity     := 1
  towerType := .TBytes 32   -- 32-byte secp256k1 base-field element (4×u64)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a secp256k1 base-field element
    (`TBytes 32` — 32 bytes, the saturated 4×u64 packing). -/
def secp256k1FieldEltTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry for the AUCurves leaf

The AUCurves safegcd inverter is **non-aliasing** at the SSA level:
`out` and `x` are distinct buffers in the Rust signature
(`secp_invert_divstep_sat(out: &mut [u64;4], x: &[u64;4])`, exposed
through the shim as `safegcd_secp256k1_invert(out, x)`). We declare
`destAliasOk := []` (the conservative default) — the borrow checker
correctly forbids aliased calls. -/

/-- Per-leaf signature for `safegcd_secp256k1_invert`: no aliasing
    permitted (`out` / `x` distinct in the Rust signature). -/
def safegcdSecp256k1LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "safegcd_secp256k1_invert"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the secp256k1 field inversion, serving as the
front-end input to the reflection pipeline. The body is the single
AUCurves-leaf call. -/

/-- One secp256k1 Bernstein–Yang divstep inversion invocation. -/
noncomputable def safegcdSecp256k1Lean
    (x : Secp256k1FieldElt) : Secp256k1FieldElt :=
  AUCurves_safegcd_secp256k1_invert_denote x

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `Vale/Curve25519.lean` and `VaesReflect.vaesEnc2WayBody`
pattern: the front-end `reifyLowCT%` macro reads `knownOps` only,
so we hand-build the single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `safegcdSecp256k1Lean`. Shape:
    `RSeq RSkip (RCall "safegcd_secp256k1_invert"
                        __result [x])`. -/
def safegcdSecp256k1Body : LowCT :=
  let x_l      := loc "x"        secp256k1FieldEltTowerType
  let result_l := loc "__result" secp256k1FieldEltTowerType
  .RSeq .RSkip
    (.RCall "safegcd_secp256k1_invert"
            result_l [x_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd secp256k1 leaf. -/
def safegcdSecp256k1Reified : ReifiedFunc :=
  { args    := [("x", secp256k1FieldEltTowerType)]
    body    := safegcdSecp256k1Body
    retName := "__result" }

/-! ## §8. Inspection -/

#eval safegcdSecp256k1Reified.args.map Prod.fst
  -- [x]
#eval safegcdSecp256k1Reified.args.length     -- 1
#eval safegcdSecp256k1Reified.retName         -- __result

end CatCrypt.Crypto.Vale.SafegcdSecp256k1
