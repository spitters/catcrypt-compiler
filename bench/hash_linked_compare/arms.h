/* arms.h -- the arms of hash_linked_compare.
 *
 * ours: the compiler's objects in gen/ (symbols catcrypt_*), reached through the
 *       register-saving trampolines of tramp.c (symbols ours_*).
 * peers: OpenSSL (system libcrypto), HACL* (libcrux vendored C), XKCP (opt64).
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

/* Peers (refs.c). */
void peer_openssl_sha512(uint64_t h[8], const uint8_t blk[128]);
void peer_hacl_sha512(uint64_t h[8], const uint8_t blk[128]);
void peer_hacl_blake2b(uint64_t hash16[16], uint64_t wv[16], const uint8_t blk[128],
                       uint64_t t0, uint64_t t1, int last);
void peer_hacl_blake2b_init_rows(uint64_t hash16[16], const uint64_t h[8]);
void peer_xkcp_keccak_f1600(uint64_t lanes[25]);
void peer_hacl_keccak_f1600(uint64_t lanes[25]);

/* Resident-state entry points for timing (refs.c). */
void *peer_openssl_sha512_ctx(void);
void peer_openssl_sha512_ctx_step(void *ctx, const uint8_t blk[128]);
void *peer_xkcp_state(void);
void peer_xkcp_state_step(void *st);

/* One-shot digests through OpenSSL EVP, to cross-check the literal vectors. */
int evp_digest(const char *name, const uint8_t *msg, unsigned long len, uint8_t *out,
               unsigned *outlen);

#endif
