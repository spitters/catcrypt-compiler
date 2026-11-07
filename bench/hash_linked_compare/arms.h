/* arms.h -- the arms of hash_linked_compare.
 *
 * ours: the compiler's objects in gen/ (symbols catcrypt_*), reached through the
 *       register-saving trampolines of tramp.c (symbols ours_*), and for SHA-512 and
 *       BLAKE2b through the block wrappers of tramp.c, which take the 128-byte block.
 * peers: OpenSSL (system libcrypto), HACL* (libcrux vendored C, portable and 256-bit
 *        vector), XKCP (opt64, AVX2, AVX-512).
 */
#ifndef HASH_LINKED_ARMS_H
#define HASH_LINKED_ARMS_H

#include <stdint.h>

/* SHA-512 compression: h[0..8) := compress(hm[0..8), hm[8..24)), where hm[0..8)
 * are the chaining words and hm[8..24) the 16 message words (big-endian loads
 * of the 128-byte block).  h and hm are disjoint. */
void ours_sha512_compress(uint64_t h[8], const uint64_t hm[24]);

/* BLAKE2b compression F (RFC 7693 3.2): h[0..8) := F(hm[0..8), hm[8..24), t, f)
 * with t = (t0, t1) and the flag words (f0, 0); message words are little-endian
 * loads of the block.  Register order: h %rdi, f0 %rsi, t1 %rdx, t0 %rcx,
 * hm %r8. */
void ours_blake2b_compress(uint64_t h[8], uint64_t f0, uint64_t t1, uint64_t t0,
                           const uint64_t hm[24]);

/* Keccak-f[1600]: dst := keccak_f(src), lane (x, y) at index 5y + x. */
void ours_keccak_f1600(uint64_t dst[25], const uint64_t src[25]);

/* Block wrappers (tramp.c): src[0..8) holds the chaining words; the wrapper loads the
 * 16 message words of blk into src[8..24) (big-endian for SHA-512, little-endian for
 * BLAKE2b) and calls the kernel, which writes dst[0..8).  dst and src are disjoint. */
void ours_sha512_block(uint64_t *dst, uint64_t src[24], const uint8_t blk[128]);
void ours_blake2b_block(uint64_t *dst, uint64_t src[24], const uint8_t blk[128],
                        uint64_t t0, uint64_t t1, uint64_t f0);

/* Peers (refs.c). */
void peer_openssl_sha512(uint64_t h[8], const uint8_t blk[128]);
void peer_hacl_sha512(uint64_t h[8], const uint8_t blk[128]);
void peer_hacl_blake2b(uint64_t hash16[16], uint64_t wv[16], const uint8_t blk[128],
                       uint64_t t0, uint64_t t1, int last);
void peer_hacl_blake2b_init_rows(uint64_t hash16[16], const uint64_t h[8]);
void peer_xkcp_keccak_f1600(uint64_t lanes[25]);
void peer_xkcp_avx2_keccak_f1600(uint64_t lanes[25]);
void peer_xkcp_avx512_keccak_f1600(uint64_t lanes[25]);
void peer_hacl_keccak_f1600(uint64_t lanes[25]);

/* HACL* 256-bit vector peers (refs_hacl_blake2b_simd256.c, refs_hacl_vec256.c).  All
 * array arguments are 32-byte aligned.
 *
 * BLAKE2b Simd256: hash16 and wv as for peer_hacl_blake2b (row r of the vector state
 * is words 4r..4r+3, so peer_hacl_blake2b_init_rows sets it up).
 * SHA-512 x4: st[4i + j] is chaining word i of lane j; one compression per lane, of
 * the block b_j.
 * Keccak-f x4: st[4i + j] is lane i of state j; the call XORs one 168-byte block of
 * zeros into each state and permutes the four states (HACL* exports no 4-way
 * permutation alone). */
void peer_hacl_blake2b_simd256(uint64_t hash16[16], uint64_t wv[16], const uint8_t blk[128],
                               uint64_t t0, uint64_t t1, int last);
void peer_hacl_sha512_x4(uint64_t st[32], const uint8_t *b0, const uint8_t *b1,
                         const uint8_t *b2, const uint8_t *b3);
void peer_hacl_keccak_x4_absorb0(uint64_t st[100]);

/* Resident-state entry points for timing (refs.c). */
void *peer_openssl_sha512_ctx(void);
void peer_openssl_sha512_ctx_step(void *ctx, const uint8_t blk[128]);
void *peer_xkcp_state(void);
void peer_xkcp_state_step(void *st);
void *peer_xkcp_avx2_state(void);
void peer_xkcp_avx2_state_step(void *st);
void *peer_xkcp_avx512_state(void);
void peer_xkcp_avx512_state_step(void *st);

/* One-shot digests through OpenSSL EVP, to cross-check the literal vectors. */
int evp_digest(const char *name, const uint8_t *msg, unsigned long len, uint8_t *out,
               unsigned *outlen);

/* Version string of the libcrypto the harness runs against. */
const char *peer_openssl_version(void);

#endif
