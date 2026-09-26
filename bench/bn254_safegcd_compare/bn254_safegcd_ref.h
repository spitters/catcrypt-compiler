/* AUCurves safegcd_bn254 BY-inversion leaf — C-callable header.
 *
 * Wraps AUCurves' Bernstein-Yang divstep modular inverter
 * `safegcd_bn254::bn254_invert_divstep_sat` so the bench harness can call
 * it with a stable C ABI:
 *
 *     extern void safegcd_bn254_invert(uint64_t out[4], const uint64_t x[4]);
 *
 * Re-exported through the staticlib shim in `shim/src/lib.rs`.
 *
 * Trust hook (Lean side): the AUCurves leaf is declared as an opaque
 * verified-CT extCall in CatCrypt/Crypto/Vale/SafegcdBN254.lean.  The
 * verified-front emit driver is in bn254_safegcd_emit.lean (the emitted
 * .jazz orchestration calls this leaf symbol).
 *
 * #489: BN254 was the one production curve whose Fp inverse was still the
 * Fermat a^(p-2) chain (bn254_inv, Vale/BN254.lean); the cross-curve audit
 * flipped it onto this divstep leaf, matching the BLS12-381 / P-256 recipe.
 */
#ifndef BN254_SAFEGCD_REF_H
#define BN254_SAFEGCD_REF_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* out = x^-1 mod p_{BN254}
 * (= 21888242871839275222246405745257275088696311157297823662689037894645226208583)
 * on 4×u64 saturated radix-2^64 limbs.  Returns [0,0,0,0] for x = 0
 * (Bernstein-Yang convention). */
extern void safegcd_bn254_invert(uint64_t out[4], const uint64_t x[4]);

#ifdef __cplusplus
}
#endif

#endif /* BN254_SAFEGCD_REF_H */
