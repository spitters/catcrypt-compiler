/* refs_hacl_vec256.c -- adapters to HACL*'s 4-lane 256-bit vector SHA-512 and Keccak
 * (testing infrastructure).  Compiled with -mavx2 and HACL_CAN_COMPILE_VEC256.
 *
 *   SHA-512 x4   sha512_update4, the static one-block update of Hacl_SHA2_Vec256.c (this
 *                file includes that translation unit to reach it): one compression in
 *                each of four independent lanes.  HACL* has no single-buffer vector
 *                SHA-512.
 *   Keccak-f x4  Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks over one 168-byte block
 *                of zeros per state: the block is copied, transposed and XORed into the
 *                four states (a no-op on their value), then the four states are
 *                permuted.  HACL* exports neither a single-state vector permutation nor
 *                a 4-way permutation alone, so the absorb is part of this arm's cost.
 *
 * Vector states as 32-byte aligned uint64_t arrays: st[4i + j] is word (or lane) i of
 * lane (or state) j, the layout of HACL*'s vec256 arrays.
 */
#include "Hacl_SHA2_Vec256.c"
#include "Hacl_Hash_SHA3_Simd256.h"

#include "arms.h"

void peer_hacl_sha512_x4(uint64_t st[32], const uint8_t *b0, const uint8_t *b1,
                         const uint8_t *b2, const uint8_t *b3) {
  Hacl_Hash_SHA2_uint8_4p b = {
      .fst = (uint8_t *)b0,
      .snd = {.fst = (uint8_t *)b1, .snd = {.fst = (uint8_t *)b2, .snd = (uint8_t *)b3}}};
  sha512_update4(b, (Lib_IntVector_Intrinsics_vec256 *)st);
}

static uint8_t zero168[168];

void peer_hacl_keccak_x4_absorb0(uint64_t st[100]) {
  Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks((Lib_IntVector_Intrinsics_vec256 *)st, zero168,
                                                 zero168, zero168, zero168, 168U);
}
