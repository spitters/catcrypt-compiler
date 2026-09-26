/* AUCurves-leaf Pallas Fp inversion — C-callable header.
 *
 * Wraps the AUCurves verified-CT Bernstein-Yang divstep modular
 * inverter `safegcd_pallas::pallas_invert_divstep_sat` so we can
 * call it from the bench/conform harnesses with a stable C signature.
 *
 *     void pallas_safegcd_invert(uint64_t out[4], const uint64_t x[4]);
 *
 * The shim is a one-line wrapper; the verified body lives in
 * `~/Claude/BLS/AUCurves/curve25519-jasmin-rs/src/safegcd_pallas.rs`
 * (10 outer × 59 inner = 590 divsteps ≥ Theorem 1 bound 588 for the
 * 255-bit base prime).
 *
 * Trust hook (Lean side): the BY/safegcd Pallas leaf is declared
 * as an opaque verified-CT extCall in
 * `CatCrypt/Crypto/Vale/Pallas.lean` (axiom
 * `Safegcd_Pallas_invert_denote`, registered as RustCmdPattern).
 * The verified-front emit driver is in `pallas_emit.lean`
 * (same pattern as `../SSProve-lean/bench/bls12381_safegcd_compare/bls12381_safegcd_emit.lean`).
 */
#ifndef PALLAS_SAFEGCD_REF_H
#define PALLAS_SAFEGCD_REF_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The AUCurves verified-CT BY/safegcd Pallas inversion leaf, C symbol.
 * Defined in `shim/src/lib.rs` (a `#[no_mangle]` re-export of
 * `safegcd_pallas::pallas_invert_divstep_sat`).  Signature:
 * `out = x^{-1} mod p_{Pallas}` over 4×u64 saturated LE buffers
 * (32 bytes per operand).  The pointers must be 8-byte aligned and
 * non-aliasing. */
extern void pallas_invert_divstep_sat(uint64_t *out, const uint64_t *x);

/* Bench/conform-facing shim. */
static inline void pallas_safegcd_invert(uint64_t out[4],
                                         const uint64_t x[4]) {
  pallas_invert_divstep_sat(out, x);
}

#ifdef __cplusplus
}
#endif

#endif /* PALLAS_SAFEGCD_REF_H */
