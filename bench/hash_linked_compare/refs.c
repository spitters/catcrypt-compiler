/* refs.c -- adapters to the peer implementations (testing infrastructure).
 *
 *   OpenSSL  SHA512_Transform (system libcrypto; deprecated in 3.0 but exported),
 *            EVP one-shot digests for the vector cross-check.
 *   HACL*    Hacl_Hash_SHA2_sha512_update_nblocks, the static update_block of
 *            Hacl_Hash_Blake2b.c (this file includes that translation unit so the
 *            one-block compression with an arbitrary counter and final flag is
 *            reachable), Hacl_Hash_SHA3_state_permute.
 *   XKCP     KeccakP1600 opt64 (KeccakP-1600-opt64.c, plain lanes: the vendored
 *            configuration defines no lane complementing); KeccakP1600_AVX2 and
 *            KeccakP1600_AVX512 (KeccakP-1600-AVX2.s, KeccakP-1600-AVX512.s, the
 *            CRYPTOGAMS permutations), declared here with an opaque state because the
 *            AVX2 state holds the lanes in a permuted order; both are read and written
 *            through their AddBytes and ExtractBytes.
 *
 * The HACL* 256-bit vector arms are in refs_hacl_blake2b_simd256.c and refs_hacl_vec256.c.
 */
#define OPENSSL_SUPPRESS_DEPRECATED
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/sha.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_Hash_Blake2b.c"

#include "KeccakP-1600-SnP.h"
#include "arms.h"

void Hacl_Hash_SHA2_sha512_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st);
void Hacl_Hash_SHA3_state_permute(uint64_t *s);

void peer_openssl_sha512(uint64_t h[8], const uint8_t blk[128]) {
  SHA512_CTX c;
  memset(&c, 0, sizeof c);
  for (int i = 0; i < 8; i++) c.h[i] = h[i];
  SHA512_Transform(&c, blk);
  for (int i = 0; i < 8; i++) h[i] = c.h[i];
}

void *peer_openssl_sha512_ctx(void) {
  SHA512_CTX *c = calloc(1, sizeof *c);
  SHA512_Init(c);
  return c;
}

void peer_openssl_sha512_ctx_step(void *ctx, const uint8_t blk[128]) {
  SHA512_Transform((SHA512_CTX *)ctx, blk);
}

void peer_hacl_sha512(uint64_t h[8], const uint8_t blk[128]) {
  Hacl_Hash_SHA2_sha512_update_nblocks(128U, (uint8_t *)blk, h);
}

/* HACL's BLAKE2b state is four rows of four words: h[0..8) then the IV. */
void peer_hacl_blake2b_init_rows(uint64_t hash16[16], const uint64_t h[8]) {
  for (int i = 0; i < 8; i++) hash16[i] = h[i];
  for (int i = 0; i < 8; i++) hash16[8 + i] = Hacl_Hash_Blake2s_ivTable_B[i];
}

void peer_hacl_blake2b(uint64_t hash16[16], uint64_t wv[16], const uint8_t blk[128],
                       uint64_t t0, uint64_t t1, int last) {
  FStar_UInt128_uint128 tl =
      FStar_UInt128_logor(FStar_UInt128_uint64_to_uint128(t0),
                          FStar_UInt128_shift_left(FStar_UInt128_uint64_to_uint128(t1), 64U));
  update_block(wv, hash16, last != 0, tl, (uint8_t *)blk);
}

void peer_xkcp_keccak_f1600(uint64_t lanes[25]) {
  KeccakP1600_state st;
  uint8_t bytes[200];
  for (int i = 0; i < 25; i++)
    for (int b = 0; b < 8; b++) bytes[8 * i + b] = (uint8_t)(lanes[i] >> (8 * b));
  KeccakP1600_Initialize(&st);
  KeccakP1600_AddBytes(&st, bytes, 0, 200);
  KeccakP1600_Permute_24rounds(&st);
  KeccakP1600_ExtractBytes(&st, bytes, 0, 200);
  for (int i = 0; i < 25; i++) {
    uint64_t w = 0;
    for (int b = 0; b < 8; b++) w |= (uint64_t)bytes[8 * i + b] << (8 * b);
    lanes[i] = w;
  }
}

void *peer_xkcp_state(void) {
  KeccakP1600_state *st = aligned_alloc(64, 256);
  KeccakP1600_Initialize(st);
  return st;
}

void peer_xkcp_state_step(void *st) { KeccakP1600_Permute_24rounds((KeccakP1600_state *)st); }

void peer_hacl_keccak_f1600(uint64_t lanes[25]) { Hacl_Hash_SHA3_state_permute(lanes); }

/* XKCP AVX2 and AVX-512 (assembly).  A state is 200 bytes; it is allocated with 64-byte
 * alignment and 256 bytes, as the opt64 state above. */
#define XKCP_ASM_ARM(tag, pfx)                                                           \
  void pfx##_Initialize(void *state);                                                    \
  void pfx##_AddBytes(void *state, const unsigned char *data, unsigned int offset,       \
                      unsigned int length);                                              \
  void pfx##_Permute_24rounds(void *state);                                              \
  void pfx##_ExtractBytes(const void *state, unsigned char *data, unsigned int offset,   \
                          unsigned int length);                                          \
  void peer_xkcp_##tag##_keccak_f1600(uint64_t lanes[25]) {                              \
    uint64_t st[32] __attribute__((aligned(64)));                                       \
    uint8_t bytes[200];                                                                  \
    for (int i = 0; i < 25; i++)                                                         \
      for (int b = 0; b < 8; b++) bytes[8 * i + b] = (uint8_t)(lanes[i] >> (8 * b));     \
    pfx##_Initialize(st);                                                                \
    pfx##_AddBytes(st, bytes, 0, 200);                                                   \
    pfx##_Permute_24rounds(st);                                                          \
    pfx##_ExtractBytes(st, bytes, 0, 200);                                               \
    for (int i = 0; i < 25; i++) {                                                       \
      uint64_t w = 0;                                                                    \
      for (int b = 0; b < 8; b++) w |= (uint64_t)bytes[8 * i + b] << (8 * b);            \
      lanes[i] = w;                                                                      \
    }                                                                                    \
  }                                                                                      \
  void *peer_xkcp_##tag##_state(void) {                                                  \
    void *st = aligned_alloc(64, 256);                                                   \
    pfx##_Initialize(st);                                                                \
    return st;                                                                           \
  }                                                                                      \
  void peer_xkcp_##tag##_state_step(void *st) { pfx##_Permute_24rounds(st); }

XKCP_ASM_ARM(avx2, KeccakP1600_AVX2)
XKCP_ASM_ARM(avx512, KeccakP1600_AVX512)

const char *peer_openssl_version(void) { return OpenSSL_version(OPENSSL_VERSION); }

int evp_digest(const char *name, const uint8_t *msg, unsigned long len, uint8_t *out,
               unsigned *outlen) {
  const EVP_MD *md = EVP_get_digestbyname(name);
  if (!md) return 0;
  return EVP_Digest(msg, len, out, outlen, md, NULL);
}
