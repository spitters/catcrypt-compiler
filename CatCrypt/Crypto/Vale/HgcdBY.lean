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


@[expose] public section
set_option autoImplicit false

/-!
# Bernstein-Yang divstep generic Half-GCD leaf (architectural gap)

## Purpose

This module documents the **architectural gap** between AUCurves'
Bernstein-Yang (BY) divstep machinery and a generic multi-precision
`gcd(a, b)` leaf suitable for closing the 8.34-83.49× HGCD lag
recorded in `bench/mpn_hgcd_compare/results.txt`.

No verified leaf is adopted in this file. The file declares the
intended `LowCTPattern` and `LeafSig` *shape* of a future generic
BY-HGCD entry point and records, in present-tense fact, the
machinery currently shipped by AUCurves and by the broader BY
literature so a follow-up adoption pass knows the gap precisely.

The `bench/mpn_hgcd_safegcd_compare/` companion measures the BY
inverter mod L (`scalar_invert_divstep`) on a fixed prime as a
*latency proxy* — the only number AUCurves' shipped code can
deliver today. The proxy is a lower bound on the cost of a
constant-time generic BY-HGCD at the same operand size (any BY-HGCD
does at least the work of one BY inverter), *not* a measurement of
generic HGCD.

## What AUCurves currently ships (BY-divstep, factual scope)

AUCurves, curve25519-jasmin-rs crate (`src/`):

| File                       | Entry                                          | Computes                          |
|----------------------------|------------------------------------------------|-----------------------------------|
| `divstep_proxy.rs`         | `scalar_invert_divstep(out, x)`                | `x^-1 mod L` (L = 2^252 + ...)     |
| `safegcd.rs`               | `invert<const N: usize>(x, info)`              | `x^-1 mod p` for any `ModInfo<N>` |
| `safegcd25519.rs`          | `fe25519_invert_divstep_sat(out, x)`           | `x^-1 mod p25519`                 |
| `safegcd_secp256k1.rs`     | per-curve wrappers                             | `x^-1 mod p_{secp256k1}`          |
| `safegcd_bls12_381.rs`     | per-curve wrappers                             | `x^-1 mod p_{BLS12-381}`          |
| `safegcd_p{224,256,384,521}.rs` | per-curve wrappers                        | `x^-1 mod p_{NIST}`               |
| `safegcd_{bn254,bn256,bn446,bw6_761}.rs` | per-curve wrappers                | `x^-1 mod p_{curve}`              |
| `safegcd_{pallas,vesta}.rs`| per-curve wrappers                             | `x^-1 mod p_{curve}`              |

Every shipped BY entry point computes the **modular inverse** of one
operand against a **fixed prime modulus baked in at compile time as
a `ModInfo<N>` constant**. None compute `gcd(a, b)` for runtime-pair
operands of arbitrary size.

The matching fiat-crypto verification artefacts establish
modular-inverse correctness, not a returned GCD value. The precise
theorems (all `Qed`, all in `AUCurves/fiat-crypto/src/Arithmetic/`):

| Theorem                    | File                              | Statement                                                                 |
|----------------------------|-----------------------------------|---------------------------------------------------------------------------|
| `divstep_correct`          | `BYInv.v`                         | one BY divstep matches `divstep_spec` (transition, per-step).             |
| `divstep_correct_full`     | `BYInv.v`                         | per-step transition carrying the Montgomery inverse accumulators `(v,r)` against modulus `m`. |
| `by_inv_jump_spec`         | `BYInv_fullproof_ref/BYInvJump.v` | the full iterated jump-divstep inverter: `eval (by_inv_jump g) mod m = by_inv_jump_ref m (tc_eval g) mw · 2^(2·mw·mont_limbs) mod m`. |
| `mod_inverse_consttime_spec` | `BinaryExtendedGCD.v`           | generic (runtime `a, n`, no baked prime) single-word constant-time inverse: `Some ainv` with `(ainv·a) mod n = 1` when `gcd(a,n)=1`, else `None`. |

The reference `by_inv_jump_ref f g mw` (`BYInv_fullproof_ref/Ref.v`)
computes `sign · pc · vm mod f` — the modular inverse `g⁻¹ mod f`.
The terminal divstep register `fm` equals `±gcd(f₀, g₀)`, but every
shipped theorem reads `fm` **only for its sign** (`if fm <? 0`) and
then discards it; no theorem returns `fm` as a value. Likewise
`mod_inverse_consttime` maintains `Z.gcd u v = Z.gcd a n` as a loop
*invariant* (`BinaryExtendedGCD.v` `invariant`) but returns the
inverse, not the gcd. The Bedrock2 leaves under
AUCurves' `src/Bedrock/Field/Synthesis/Examples/*_FpInv*.v`
and `.../End2End/Ed25519/Safegcd_*_Spec.v` are inverse specs on the
same shape (the finalize step relies on `|f| = 1` at termination,
which is `gcd(x, p) = 1` for `x` coprime to the prime `p` — the
inverse special case, not a returned gcd).

## What a generic BY-HGCD would require (the gap)

To convert the per-curve BY inverter machinery into a `gcd(a, b)`
leaf usable by `mpn_hgcd_compare/bench.c`, three components are
missing from AUCurves and from the broader verified-bignum stack
we depend on:

1. **Runtime-sized `f`, `g` representation.** The current `Signed62<N>`
   uses a const-generic `N` (5 limbs for 256-bit, 9 for 509-bit, ...).
   A generic GCD takes operands of *runtime* bit-length; the inner
   `divsteps_59`, `update_fg_62`, and `update_de_62` need a non-const
   `N`-or-bounded variant. Mechanically: replace `[i64; N]` with a
   length-tagged slice and propagate the length through the outer-iter
   loop. The Bedrock2 proofs require the same generalisation.

2. **The two-operand-no-modulus loop variant.** AUCurves' outer
   iteration tracks `(f, g, d, e)` where `(d, e)` are accumulators
   used to recover `x^-1`. A pure GCD only needs `(f, g)`; the
   `update_de_62` call is dead code that must be elided to land
   competitive performance. This is the recipe Bernstein-Yang
   *Fast constant-time gcd computation* (TCHES 2019) prescribes,
   but no shipped implementation in `AUCurves/curve25519-jasmin-rs`
   compiles to it.

3. **Bound on the outer iteration count.** AUCurves' `Ref.v` defines
   the iteration count as `iterations d = if d < 46 then (49·d + 80)/17
   else (49·d + 57)/17` and the half-delta variant
   `iterations_hd d = (45907·d + 26313)/19929`, with
   `jump_iterations b mw = iterations b / (mw - 2) + 1`. `by_inv_jump_spec`
   proves the inverter converges under `iterations`; it does not prove
   a terminal `fm = ±gcd(f₀, g₀)` at that count for a *generic* pair
   (its termination argument routes through the modulus `m`). A generic
   GCD must re-prove terminal convergence of `fm` to the gcd in the
   absence of the modulus and the sign-correction finalize phase. No
   such theorem exists in a verification stack we depend on.

The cleanest path to closing this gap is:

* Port the BY 2019 §5 ("two-operand gcd") algorithm to AUCurves'
  `safegcd.rs` as a sibling to `invert<const N: usize>`, keyed on a
  runtime length.
* Re-prove the convergence-and-correctness theorem in Bedrock2 (the
  proof obligation is one of the BY 2019 paper's own theorems, but
  the mechanical port has not been done upstream).
* Add a curve-independent `safegcd_generic.rs` shim that exposes a
  C-callable `mpn_gcd_safegcd(rp, ap, an, bp, bn)` taking length-
  tagged slices.

That is research-grade work.

## What this file *does* (placeholder)

This file declares only:

* The `axiom` block for a hypothetical generic-HGCD leaf
  `AUCurves_safegcd_gcd_n_denote` over `Nat × Nat → Nat`. Marked
  `axiom NOT_YET_PROVEN` so the audit catches any attempt to use it
  as a real leaf.
* The `LowCTPattern` and `LeafSig` for the **C symbol name**
  `mpn_gcd_safegcd` that the bench companion currently *defines as
  a stub* — calling `mpz_gcd` internally so the bench harness runs
  without crashing, while the latency column it reports is the
  BY-inverter proxy, not the gcd.
* A `TODO`-tagged docstring with the gap analysis (this file).

When the upstream AUCurves work in §1-3 lands, the `axiom
NOT_YET_PROVEN` resolves to a real denotation axiom, the bench's
stub body becomes the real `safegcd_gcd` body, and the
`mpn_hgcd_safegcd_compare` README's "honest assessment" section
swaps "proxy" for "measurement".

## Plan summary (referenced by the audit)

* **Step 1.** Port BY 2019 §5 two-operand-gcd algorithm to
  `safegcd.rs` (AUCurves, curve25519-jasmin-rs crate) as
  `pub fn gcd_signed62<const N_MAX: usize>(a, b) -> Signed62<N_MAX>`.
  Estimated 4-6 weeks engineering.
* **Step 2.** Re-prove the convergence theorem in Bedrock2 at
  AUCurves' `src/Bedrock/.../Safegcd_Gcd_Generic.v`.
  Estimated 8-12 weeks proof engineering.
* **Step 3.** Replace this file's `axiom NOT_YET_PROVEN` with a real
  denotation axiom analogous to `Vale_Hacl_Curve25519_64_denote` in
  `Vale/Curve25519.lean`, citing the new Bedrock2 theorem.
* **Step 4.** Replace `bench/mpn_hgcd_safegcd_compare/safegcd_gcd_stub.c`
  with the C shim re-exporting AUCurves' `gcd_signed62` and remeasure.

## Present state

This file does **not** close any of the 8.34-83.49× HGCD gap. The
gap is architectural — AUCurves' BY machinery is modular inversion,
not a returned generic GCD value — and the closing work is
research-grade. The deliverable here is:

* a Lean-side `axiom NOT_YET_PROVEN`-tagged stub so the verified
  pipeline's surface reflects the gap explicitly (rather than
  silently routing through libgmp's `mpz_gcd` under the hood);
* a bench harness that measures AUCurves' BY scalar-inverter latency
  as a **lower-bound proxy** (any BY-HGCD must do at least the
  work of one BY inverter at the same operand size) and reports the
  proxy-vs-libgmp ratio against the existing HGCD-vs-libgmp ratio so
  the gap is quantified;
* this file's gap analysis, indexed by the audit so future passes
  start from a precise statement of what is missing.

The 8.34-83.49× gap to `mpz_gcd` recorded in `bench/mpn_hgcd_compare/`
remains open.
-/

namespace CatCrypt.Crypto.Vale.HgcdBY

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## §1. Opaque surface type

A multi-precision unsigned bignum buffer. Opaque — the concrete leaf
at link time *does not yet exist* (see file docstring §"Plan
summary"). The type is declared so the `LowCTPattern` /
`LeafSig` registration below typechecks and the bench harness can
target a stable C symbol name. -/

/-- A heap-allocated unsigned bignum buffer (length-tagged on the C
    side via a separate `size_t`). Opaque; the concrete leaf is the
    *currently-missing* `mpn_gcd_safegcd` AUCurves entry point
    documented in the file header. -/
axiom MpnBuf : Type
/-- Axiomatic inhabitant. -/
axiom MpnBuf.default : MpnBuf
noncomputable instance : Inhabited MpnBuf := ⟨MpnBuf.default⟩

/-! ## §2. Placeholder axiom (the gap marker)

The `NOT_YET_PROVEN` suffix on the axiom name is the audit-visible
marker that *no* upstream verification supports this denotation
*yet*, so a security theorem that depends on it names the gap in its
axiom list. -/

/-- **Placeholder denotation axiom — NOT BACKED BY AUCurves YET.**
    A future generic Bernstein-Yang HGCD leaf would compute
    `gcd(a, b)` constant-time over arbitrary-size bignum buffers and
    return the gcd *value* (the shape the `bench/mpn_hgcd_safegcd_compare`
    consumer needs — it compares against libgmp `mpz_gcd`).

    What AUCurves' fiat-crypto proves is the modular *inverse*:
    `by_inv_jump_spec` (`BYInv_fullproof_ref/BYInvJump.v`) gives
    `eval (by_inv_jump g) mod m = g⁻¹ · (Montgomery factor) mod m`,
    `divstep_correct`/`divstep_correct_full` (`BYInv.v`) give the
    per-step transition, and `mod_inverse_consttime_spec`
    (`BinaryExtendedGCD.v`) gives a generic single-word constant-time
    inverse. In each the terminal divstep register `fm = ±gcd(f₀, g₀)`
    is read only for its sign and then discarded; no shipped theorem
    returns the gcd. See the file header for the exact statements.

    This axiom exists so the `LowCTPattern` below typechecks; it MUST
    NOT be used in a security theorem until an upstream gcd-value
    theorem lands and this axiom is replaced. -/
axiom AUCurves_safegcd_gcd_n_denote_NOT_YET_PROVEN
    (a b : MpnBuf) : MpnBuf

/-! ## §3. `@[rust_cmd_pattern]` registration (placeholder)

Registers the *intended* C symbol `mpn_gcd_safegcd`. The bench
companion `bench/mpn_hgcd_safegcd_compare/safegcd_gcd_stub.c`
currently *stubs* this symbol to `mpz_gcd` so the bench runs;
once the AUCurves port lands the stub is replaced with the real
shim. -/

/-- Register `AUCurves_safegcd_gcd_n_denote_NOT_YET_PROVEN` → leaf
    `mpn_gcd_safegcd`. **Placeholder** — the C symbol does not yet
    have an AUCurves-verified body; see the bench stub. -/
@[rust_cmd_pattern]
def hgcdBYPattern : LowCTPattern where
  name      := "mpn_gcd_safegcd"
  fnHead    := ``AUCurves_safegcd_gcd_n_denote_NOT_YET_PROVEN
  arity     := 2
  towerType := .TBytes 32   -- placeholder: real leaf would be runtime-sized

/-! ## §4. Tower-type abbreviation (placeholder) -/

/-- Placeholder tower-type for a bignum buffer. Real leaf would use
    a length-tagged variant; `.TBytes 32` here matches the existing
    `Vale/Curve25519.lean` convention so the pattern registers. -/
def mpnBufTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry (placeholder)

`destAliasOk := []` — the real leaf, like all the existing mpn
leaves, will require non-aliasing `(rp, ap, bp)`. -/

/-- Per-leaf signature for the placeholder `mpn_gcd_safegcd`.
    No aliasing permitted. -/
def hgcdBYLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "mpn_gcd_safegcd"
  destAliasOk := []

/-! ## §6. Inspection -/

#eval hgcdBYLeafSig.name           -- mpn_gcd_safegcd
#eval hgcdBYPattern.arity          -- 2

end CatCrypt.Crypto.Vale.HgcdBY
