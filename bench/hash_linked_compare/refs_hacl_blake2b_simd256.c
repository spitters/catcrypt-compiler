/* refs_hacl_blake2b_simd256.c -- adapter to HACL*'s 256-bit vector BLAKE2b (testing
 * infrastructure).
 *
 * This file includes Hacl_Hash_Blake2b_Simd256.c so that its static update_block, the
 * one-block compression with an arbitrary counter and final flag, is reachable; a
 * separate translation unit from refs.c, which includes the portable Hacl_Hash_Blake2b.c
 * whose static functions have the same names.  Compiled with -mavx2 and
 * HACL_CAN_COMPILE_VEC256.
 *
 * The vector state is four rows of four words (h[0..4), h[4..8), IV[0..4), IV[4..8)),
 * the memory layout of the portable state, so peer_hacl_blake2b_init_rows (refs.c)
 * initialises both.  hash16 and wv must be 32-byte aligned.
 */
#include "Hacl_Hash_Blake2b_Simd256.c"

#include "arms.h"

void peer_hacl_blake2b_simd256(uint64_t hash16[16], uint64_t wv[16], const uint8_t blk[128],
                               uint64_t t0, uint64_t t1, int last) {
  FStar_UInt128_uint128 tl =
      FStar_UInt128_logor(FStar_UInt128_uint64_to_uint128(t0),
                          FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128(t1), 64U));
  update_block((Lib_IntVector_Intrinsics_vec256 *)wv, (Lib_IntVector_Intrinsics_vec256 *)hash16,
               last != 0, tl, (uint8_t *)blk);
}
