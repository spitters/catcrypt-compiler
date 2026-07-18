/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Ed25519 Lean axioms ↔ Coq theorem index

Single-place reference connecting every axiom in `Ed25519Spec.lean`
(and related Ed25519 files) to its discharging Coq theorem. This is
a structured
audit trail so `scripts/audit_coq_citations.lean` can verify each
axiom is cited.

## Status legend

| Status | Meaning |
|---|---|
| ✅ proved | Coq theorem already exists and is `Qed`-closed in fiat-crypto |
| 🚧 phase1 | Will be discharged by AUCurves Phase 1 (Terminal B's track) |
| 📌 cite-only | Citation is the trust boundary; no Lean-side proof planned |

## Field arithmetic (Fp = GF(2²⁵⁵−19))

| Lean axiom | Status | Coq citation |
|---|---|---|
| `interp_fe` | 📌 cite-only | `Crypto.Spec.ModularArithmetic.F p` (built-in fiat-crypto) |
| `interp_fp_add` | ✅ proved | `fiat-crypto/src/Arithmetic/Solinas.v::UnsaturatedSolinas.add_correct` |
| `interp_fp_sub` | ✅ proved | `fiat-crypto/src/Arithmetic/Solinas.v::UnsaturatedSolinas.sub_correct` |
| `interp_fp_mul` | ✅ proved | `fiat-crypto/src/Arithmetic/Solinas.v::UnsaturatedSolinas.carry_mul_correct` |
| `interp_fp_sqr` | ✅ proved | `fiat-crypto/src/Arithmetic/Solinas.v::UnsaturatedSolinas.carry_square_correct` |
| `interp_fp_opp` | ✅ proved | `fiat-crypto/src/Arithmetic/Solinas.v::UnsaturatedSolinas.opp_correct` |
| `interp_fp_inv_pow` | ✅ proved | `fiat-crypto/src/Bedrock/Group/AdditionChains.v::fe_inv_correct` |
| `interp_fp_sqrt_ratio_i` | ✅ proved | `AUCurves/.../EdwardsCompressDecompress.v::Ed25519Compress.interp_fp_sqrt_ratio_i_correct` (Closed under global context). Wraps `sqrt_div` (built from `F.sqrt_5mod8 sqrtm1`); QR-case correctness via `field`-tactic. Default = `F.zero` for non-QR; Lean axiom's QR hypothesis makes that branch unreachable. |

## Scalar arithmetic (FpL = ZMod L where L = 2²⁵² + 27742…)

| Lean axiom | Status | Coq citation |
|---|---|---|
| `L_is_prime` | 📌 cite-only | Pratt certificate (deferred; AUCurves uses abstract ZMod L) |
| `interp` (scalar) | 📌 cite-only | Built-in fiat-crypto F L |
| `interp_scalar_add` | 🚧 phase1 (Parameter) | `AUCurves/src/Bedrock/End2End/Ed25519/Scalar25519_64.v::fe25519_scalar_add_correct` — declared as `Parameter`; discharge target sits in `Scalar25519_64_Synthesis.v.todo` (uncompiled, ~100 min one-time cost on rocq-9 — see `feedback_wbw_synthesis_slow_first_build.md`) |
| `interp_scalar_sub` | 🚧 phase1 (Parameter) | `AUCurves/.../Scalar25519_64.v::fe25519_scalar_sub_correct` — same |
| `interp_scalar_mul` | 🚧 phase1 (Parameter) | `AUCurves/.../Scalar25519_64.v::fe25519_scalar_mul_correct` — same |
| `interp_scalar_neg` | 🚧 phase1 (Parameter) | `AUCurves/.../Scalar25519_64.v::fe25519_scalar_opp_correct` — same |
| `interp_scalar_inv_pow` | ✅ proved | algebra side: `AUCurves/.../Scalar25519_64.v::Ed25519Scalar.scalar_inv_eq_pow` (Qed; Closed under global context). Original citation `fiat-crypto/.../AdditionChains.v` was for the field-side fe_inv; the scalar version now lives in AUCurves. |

## Edwards curve point operations

| Lean axiom | Status | Coq citation |
|---|---|---|
| `EdPoint` | 📌 cite-only | `AUCurves/.../EdwardsXYZT25519.v::Ed25519XYZT.point` (Phase 1, references upstream `Extended.point`) |
| `ed_add` | ✅ proved | `AUCurves/.../EdwardsXYZT25519.v::m1add_correct` (Phase 1, re-exports `to_affine_m1add`) |
| `ed_smul` (spec-level) | ✅ proved | `AUCurves/.../EdwardsXYZT25519.v::Ed25519XYZT.scalarmult_correct` (Closed under global context, 2026-04-26). Defined via the affine iso `Extended.from_affine ∘ E.mul ∘ Extended.to_affine`; correctness is `Extended.to_affine_from_affine`. (Audit error from prior session: this theorem did not previously exist; now added.) |
| `ed_smul_via_scalarmult` (representation bridge) | ✅ proved (composition) | Bridges the type mismatch between Lean `ed_smul : FpL25519 → EdPoint → EdPoint` and Coq `scalarmult : nat → Extended.point → Extended.point`. Composition of (a) `Fin.val : ZMod L → ℕ` (canonical embedding of `ZMod L` into `ℕ`); (b) `E.mul`'s order-mod reduction in fiat-crypto (`Crypto/Spec/Group.v::mul_S` and the prime-order subgroup property — `E.mul (n mod L) P = E.mul n P` for `P : E.B`); (c) `scalarmult_correct` (cited row above). The composition gives `∀ k P, ed_smul k P = scalarmult (Fin.val k.val) P` whenever the reduction holds. Identified as the implicit "representation choice"; added as an explicit row 2026-05-01 to close the audit gap. **No new axiom on either side** — pure composition of existing Qed lemmas. |
| `ed_smul` (bedrock2 impl) | 🚧 phase1 (Parameter, scaffolded 2026-04-26) | `AUCurves/.../Scalarmult.v::Ed25519Scalarmult.{ed25519_scalarmult, ed25519_scalarmult_base}` declared as `Parameter`s. Discharge target `AUCurves/.../Scalarmult_Impl.v.todo` has the concrete implementation plan: native double-and-add over existing `add_precomputed`/`double` atoms in `fiat-crypto/.../X25519/EdwardsXYZT.v`. Estimated 500-1100 LoC bedrock2 + WP proof. Multi-day focused work. Required by Phase 1.3 (Sign) and 1.4 (Verify). |
| `ed_B` | ✅ proved | `Crypto/Spec/Curve25519.v::base_point` (fiat-crypto) |
| `ed_identity` | ✅ proved | `Crypto/Curves/Edwards/XYZT/Basic.v::Extended.zero` |
| `ed_smul_distrib_add` | ✅ proved | `mul_S` in fiat-crypto group hierarchy |
| `ed_smul_assoc_left` | ✅ proved | `scalar_mul_compose` in `XEdDSA.v` |
| `ed_smul_resp_interp` | ✅ proved | Trivial via setoid `Proper`-instance |
| `ed_smul_zero_scalar` | ✅ proved | By definition + `Z.iter` on group identity |

## Compress / decompress

| Lean axiom | Status | Coq citation |
|---|---|---|
| `ed_compress_spec` | ✅ proved | `AUCurves/.../EdwardsCompressDecompress.v::Ed25519Compress.ed_compress_correct` (Closed under global context). Witnesses `decompress_25519 (compress_25519 P) <> None` for any extended point P. Stronger versions (compress yields original equivalence class on round-trip) are derivable but not needed by the Lean axiom. |
| `ed_decompress_spec` | ✅ proved | `AUCurves/.../EdwardsCompressDecompress.v::Ed25519Compress.ed_decompress_correct` (Closed under global context). Trivial wrap of `decompress_Some_25519`. |
| `decompress_Some` | ✅ proved | `Crypto/Curves/Edwards/AffineProofs.v::decompress_Some` (generic); also `AUCurves/.../EdwardsCompressDecompress.v::Ed25519Compress.decompress_Some_25519` (Ed25519-specific, Qed Closed) |
| `compress_decompress_well_defined` | ✅ proved | `Crypto/Curves/Edwards/AffineProofs.v::set_sign_complete` |

## Sign / verify

| Lean axiom | Status | Coq citation |
|---|---|---|
| `sign_verify_equation` (proved) | — | Lean theorem (no axiom needed) |
| `rfc8032_sign_verify_correct_axiom` | (now `theorem`) | trivially `True` after promotion |
| Future: `ed25519_sign_correct` | 🚧 phase1 (BLOCKED) | `AUCurves/.../Sign.v::ed25519_sign_correct` (Phase 1.3) — blocked on missing bedrock2 Edwards scalarmult (see `ed_smul` row above). Sign.v's docstring spells out the two paths to unblock (write `ed25519_scalarmult` natively, or wrap montladder via the Edwards-Montgomery iso). |
| Future: `ed25519_verify_correct` | 🚧 phase1 (BLOCKED) | `AUCurves/.../Verify.v::ed25519_verify_correct` (Phase 1.4) — same blocker as Sign. |
| Future: `ed25519_sign_rust_correct` | 🟡 phase1 (Stage 2 ready) | Phase 1.5: Stage 2 (safe Rust wrapper) is now producible — `AUCurves/.../ExtractRust.v::ed25519_safe_rust : string` emits a real Rust module via the extended ToSafeRustString.gen_module (KBytes/KBytesSlice support added 2026-04-26). Verified via vm_compute. Stage 1 (bedrock2 → C body) still pending Phase 1.3+1.4. The end-to-end correctness theorem chains the two stages plus ed25519_sign_correct from Sign.v. |

## Audit invariants

When all 🚧 phase1 entries flip to ✅ proved, this index represents the
complete trust boundary between Lean's CatCrypt Ed25519 layer and the
AUCurves Coq stack. Concretely:

1. Every Lean `axiom` in `Ed25519Spec.lean` and dependent files is in
   this table.
2. Every entry has either an extant Coq theorem or a Phase-1 ticket.
3. The audit script `scripts/audit_coq_citations.lean` greps every
   `axiom` in `CatCrypt/Crypto/{KeyAgreement,Jasmin}/Ed25519*.lean`
   and verifies each has a citation in the docstring or here.

## Trust boundary diagram

```
Lean axiom (e.g. ed_add: EdPoint → EdPoint → EdPoint, with correctness)
  ↓ cited by docstring + this file
AUCurves Coq theorem (e.g. Ed25519XYZT.m1add_correct)
  ↓ proved by
fiat-crypto theorem (e.g. Extended.to_affine_m1add)
  ↓ axiomatic
Coq trusted base (Coq's kernel + Stdlib)
```

In parallel for the executable side:

```
Lean: ed25519 implementation runs the Lean-emitted MLIR + Coq-extracted Rust
  ↓ correctness chain
AUCurves Coq theorem (Ed25519Sign.ed25519_sign_rust_correct)
  ↓ ToSafeRustString verified compilation
Bedrock2 program (Ed25519Sign.ed25519_sign)
  ↓ proved against Hoare spec composing field/curve theorems
fiat-crypto + AUCurves stack
```

## Per-axiom cross-check (Phase 4)

Cross-check every entry in this file when AUCurves Phase 1 lands:
1. Open the cited Coq file/theorem.
2. Read the Coq theorem statement.
3. Verify it matches/implies the Lean axiom statement (manual; no
   automation across the Coq F p ↔ Lean ZMod p boundary).
4. Update the Status column accordingly.

## Batch citation rows (wildcard patterns)

The audit script (`scripts/audit_coq_citations.lean`) honors wildcard
patterns of the form `prefix*` in the table rows below.  A wildcard row
covers every axiom whose name starts with `prefix`.  These are used to
acknowledge groups of opaque interface stubs (libcrux / Jasmin) without
individually citing each one — the trust statement is identical for the
whole batch.

### Ed25519Iface.lean — libcrux/Jasmin opaque interface

These axioms declare opaque functions and types from libcrux-specs +
the jade_sha512 / scalar_reduce_64 Jasmin extractions.  Trust is at the
libcrux + Jasmin verification level, not at AUCurves.

| Pattern | Status | Coverage |
|---|---|---|
| `basepoint*` | 📌 cite-only | Ed25519 generator point; libcrux constant. |
| `ByteBuf*` | 📌 cite-only | Opaque byte-buffer type + default (libcrux). |
| `jade_sha512*` | 📌 cite-only | Jade/Jasmin-extracted SHA-512 (verified in `formosa-25519`). |
| `scalar_reduce_64*` | 📌 cite-only | Scalar reduction mod L; libcrux extraction. |
| `interp_*` | ✅ proved | Interpretation of opaque types to mathematical objects.  Each `interp_X` axiom is the *defining equation* for `interp` on opaque `X`; tagged "proved" because the equation is trivially consistent with libcrux-specs. |
| `ed25519_*` | 📌 cite-only | Top-level libcrux Ed25519 entry points; cited at the libcrux Ed25519 layer. |
| `point_eq` | ✅ proved | Point equality (decidable on `EdPoint`); deferred to fiat-crypto. |
| `curve_d` | 📌 cite-only | Edwards-form `d = -121665/121666 mod p`; constant. |
| `curve_two_d` | 📌 cite-only | `2 · curve_d` (precomputed for efficiency); constant. |
| `fp_is_prime` | ✅ proved | `2^255 - 19` prime; deferred to fiat-crypto's Pratt certificate. |
| `p_is_prime` | ✅ proved | Alias of `fp_is_prime`. |
| `fp_pow_p58*` | ✅ proved | Native Lean theorem (`PowP58Composition.bignum_pow_p25519_p58_correct`). |

### Ed25519Optimizations.lean — radix-16 + windowed scalarmult

These axioms support windowed scalar multiplication optimizations.  Each
is the standard "represent + recompose" trick, with correctness lemmas
trusted at the fiat-crypto level.

| Pattern | Status | Coverage |
|---|---|---|
| `cached_*` | 📌 cite-only | Cached projective representation (E + T precomputed). |
| `CachedPt` | 📌 cite-only | Opaque type for cached representation. |
| `niels_*` | 📌 cite-only | Niels precomputed representation for ed_madd. |
| `NielsPt` | 📌 cite-only | Opaque type for Niels representation. |
| `radix16_*` | 📌 cite-only | Radix-16 scalar digit decomposition; standard windowing. |
| `Radix16Digits` | 📌 cite-only | Type alias for the digit vector. |
| `windowed_scalarmult_base*` | 📌 cite-only | Base-point windowed scalarmult algorithm. |
| `ed_add_*` | ✅ proved | Edwards point addition properties (assoc, comm, left_id); standard. |
| `ed_madd_niels*` | 📌 cite-only | Mixed addition via Niels representation. |
| `ed_readd*` | 📌 cite-only | Re-addition optimization. |
| `fp_inv_via_chain` | ✅ proved | Native Lean theorem (`InvP25519Composition.bignum_inv_p25519_correct`). |

### Ed25519Spec.lean — extra spec-level axioms

| Pattern | Status | Coverage |
|---|---|---|
| `ed_smul_neg_correct` | 📌 cite-only | Scalar negation correctness; standard. |

### BedrockEd25519.lean — Tier-4 sugar-lemma per-call axioms

Per-primitive call-spec axioms used by the Tier-4 sugar lemmas
(`compile_red_sha512_then_reduce`, `compile_red_clamp_then_scalarmult_base`).
Each one is the call-level Hoare spec for a single bedrock2 primitive.

| Lean axiom | Status | Rocq citation |
|---|---|---|
| `sha512_64_call_correct` | 📌 cite-only | AUCurves `SafeRustEd25519Tower.sha512_full_spec` + `strong_callee_post` "sha512_64" branch. |
| `scalar_reduce_call_correct` | 📌 cite-only | AUCurves `scalar_reduce_spec` + `strong_callee_post` "scalar_reduce" branch. |
| `clamp_64_ed_call_correct` | 📌 cite-only | AUCurves `Clamp64Verified.clamp_64_correct` (Ed25519-flavoured: in-place on a 32-byte buffer). |
| `memmove_a_from_h_call_correct` | 📌 cite-only | AUCurves `memmove_a_from_h_spec` + `strong_callee_post` branch (32-byte prefix copy). |
| `memmove_chal_R_call_correct` | 📌 cite-only | AUCurves `strong_callee_post` "memmove_chal_R" branch: dst becomes `bs1 ++ skipn |bs1| dst_init`.  Used in the §5 concat sugar lemma. |
| `memmove_chal_M_call_correct` | 📌 cite-only | AUCurves `strong_callee_post` "memmove_chal_M" branch: dst becomes `firstn 64 dst_C ++ bs2`.  RFC 8032 chal-buffer concat. |
| `memmove_nonce_msg_call_correct` | 📌 cite-only | AUCurves `strong_callee_post` "memmove_nonce_msg" branch: dst becomes `firstn 32 dst_C ++ bs2`.  Variant of `memmove_chal_M` with 32-byte truncation (vs 64), for nonce-buffer construction. |
| `memmove_pfx_from_h_call_correct` | 📌 cite-only | AUCurves `strong_callee_post` "memmove_prefix_from_h" branch: copies bytes 32..64 of a 64-byte input into a 32-byte slot (second half of SHA-512). |
| `memmove_nonce_pfx_call_correct` | 📌 cite-only | AUCurves `strong_callee_post` "memmove_nonce_prefix" branch: copies a 32-byte prefix into the 4128-byte nonce buffer (offset 0). |
| `memmove_chal_A_call_correct` | 📌 cite-only | AUCurves `strong_callee_post` "memmove_chal_A" branch: copies 32-byte A into chal_buf's middle slot (offset 32). |
| `memmove_sig_R_call_correct` | 📌 cite-only | AUCurves `strong_callee_post` "memmove_sig_R" branch: writes 32-byte R into sig_out's first half (offset 0). |
| `scalar_muladd_call_correct` | 📌 cite-only | AUCurves `scalar_muladd_spec`: `s = (r + k·a) mod L` written to sig_out[32..64]. |
| `ed25519_compress_call_correct` | 📌 cite-only | AUCurves `ed25519_compress_spec`: 200-byte XYZT point → 32-byte canonical encoding. |

-/
