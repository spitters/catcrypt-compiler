/* sha256_conf.c -- conformance of catcrypt_sha256_compress (gen/sha256_compress.o, the emit row
 * sha256_compress of linked-kernel-emit) at the u64-slot layout sha256Abi: %rdi the 8 output
 * slots, %rsi the 24 input slots (8 chaining words, then 16 message words), each slot a 64-bit
 * word holding a 32-bit word with zero high bits.
 *
 * Checks:
 *   1. FIPS 180-4 vectors and 200 OpenSSL EVP SHA-256 digests of random messages (0..300 bytes),
 *      hashed by padding and iterating ours;
 *   2. 10000 random (state, block) pairs against a textbook C compression (FIPS 180-4, 6.2.2);
 *   3. the high 32 bits of every output slot are zero, and the input slots are unchanged.
 * Usage: sha256_conf [NRAND]; last line PASS or FAIL, exit code 1 on any mismatch. */
#include <openssl/evp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

__asm__(".text\n.globl ours_sha256_compress\n.type ours_sha256_compress,@function\n"
        ".p2align 4\nours_sha256_compress:\n"
        "  push %rbx\n  push %rbp\n  push %r12\n  push %r13\n  push %r14\n  push %r15\n"
        "  sub $8, %rsp\n  call catcrypt_sha256_compress\n  add $8, %rsp\n"
        "  pop %r15\n  pop %r14\n  pop %r13\n  pop %r12\n  pop %rbp\n  pop %rbx\n  ret\n"
        ".size ours_sha256_compress, .-ours_sha256_compress\n");
void ours_sha256_compress(uint64_t h[8], const uint64_t hm[24]);

static const uint32_t K[64] = {
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
static const uint32_t IV[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
                               0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
#define ROR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

/* textbook compression, FIPS 180-4 section 6.2.2 */
static void ref_compress(uint32_t H[8], const uint32_t M[16]) {
  uint32_t W[64], a = H[0], b = H[1], c = H[2], d = H[3], e = H[4], f = H[5], g = H[6], h = H[7];
  for (int t = 0; t < 16; t++) W[t] = M[t];
  for (int t = 16; t < 64; t++) {
    uint32_t s0 = ROR(W[t-15], 7) ^ ROR(W[t-15], 18) ^ (W[t-15] >> 3);
    uint32_t s1 = ROR(W[t-2], 17) ^ ROR(W[t-2], 19) ^ (W[t-2] >> 10);
    W[t] = W[t-16] + s0 + W[t-7] + s1;
  }
  for (int t = 0; t < 64; t++) {
    uint32_t T1 = h + (ROR(e, 6) ^ ROR(e, 11) ^ ROR(e, 25)) + ((e & f) ^ (~e & g)) + K[t] + W[t];
    uint32_t T2 = (ROR(a, 2) ^ ROR(a, 13) ^ ROR(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
    h = g; g = f; f = e; e = d + T1; d = c; c = b; b = a; a = T1 + T2;
  }
  H[0] += a; H[1] += b; H[2] += c; H[3] += d; H[4] += e; H[5] += f; H[6] += g; H[7] += h;
}

static int bad = 0;

/* ours on 32-bit words through the u64 slots, with the slot checks */
static void ours_compress(uint32_t H[8], const uint32_t M[16]) {
  uint64_t hm[24], keep[24], out[8];
  for (int i = 0; i < 8; i++) hm[i] = H[i];
  for (int j = 0; j < 16; j++) hm[8 + j] = M[j];
  memcpy(keep, hm, sizeof hm);
  for (int i = 0; i < 8; i++) out[i] = 0xdeadbeefcafef00dULL;
  ours_sha256_compress(out, hm);
  if (memcmp(keep, hm, sizeof hm)) { printf("INPUT-CHANGED\n"); bad = 1; }
  for (int i = 0; i < 8; i++) {
    if (out[i] >> 32) { printf("HIGH-BITS slot %d: %016llx\n", i, (unsigned long long)out[i]); bad = 1; }
    H[i] = (uint32_t)out[i];
  }
}

static void sha256_ours(uint8_t dig[32], const uint8_t *msg, size_t n) {
  uint32_t H[8];
  memcpy(H, IV, sizeof H);
  size_t total = ((n + 9 + 63) / 64) * 64;
  uint8_t *buf = calloc(total, 1);
  memcpy(buf, msg, n);
  buf[n] = 0x80;
  uint64_t bits = (uint64_t)n * 8;
  for (int i = 0; i < 8; i++) buf[total - 1 - i] = (uint8_t)(bits >> (8 * i));
  for (size_t off = 0; off < total; off += 64) {
    uint32_t M[16];
    for (int j = 0; j < 16; j++)
      M[j] = (uint32_t)buf[off+4*j] << 24 | (uint32_t)buf[off+4*j+1] << 16 |
             (uint32_t)buf[off+4*j+2] << 8 | buf[off+4*j+3];
    ours_compress(H, M);
  }
  free(buf);
  for (int i = 0; i < 8; i++)
    for (int b = 0; b < 4; b++) dig[4*i+b] = (uint8_t)(H[i] >> (24 - 8*b));
}

static uint64_t rng = 0x9e3779b97f4a7c15ULL;
static uint64_t xs(void) { rng ^= rng >> 12; rng ^= rng << 25; rng ^= rng >> 27; return rng * 0x2545f4914f6cdd1dULL; }

int main(int argc, char **argv) {
  int nrand = argc > 1 ? atoi(argv[1]) : 10000;
  int nbad = 0;
  /* 1. FIPS 180-4 and OpenSSL EVP digests */
  const char *fips[2] = {"abc", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"};
  int nmsg = 0;
  for (int v = 0; v < 202; v++) {
    uint8_t msg[300];
    size_t n;
    if (v < 2) { n = strlen(fips[v]); memcpy(msg, fips[v], n); }
    else { n = (size_t)(xs() % 301); for (size_t i = 0; i < n; i++) msg[i] = (uint8_t)xs(); }
    uint8_t a[32], b[32];
    unsigned blen = 0;
    sha256_ours(a, msg, n);
    EVP_Digest(msg, n, b, &blen, EVP_sha256(), NULL);
    if (blen != 32 || memcmp(a, b, 32)) { printf("EVP MISMATCH msg %d (len %zu)\n", v, n); nbad++; }
    nmsg++;
  }
  printf("evp digests: %d messages, %d mismatches\n", nmsg, nbad);
  /* 2. random (state, block) pairs against the textbook compression */
  int nb2 = 0;
  for (int v = 0; v < nrand; v++) {
    uint32_t H1[8], H2[8], M[16];
    for (int i = 0; i < 8; i++) H1[i] = H2[i] = (uint32_t)xs();
    for (int j = 0; j < 16; j++) M[j] = (uint32_t)xs();
    ref_compress(H1, M);
    ours_compress(H2, M);
    if (memcmp(H1, H2, sizeof H1)) { if (nb2 < 5) printf("COMPRESS MISMATCH %d\n", v); nb2++; }
  }
  printf("random compressions: %d, %d mismatches\n", nrand, nb2);
  if (nbad || nb2) bad = 1;
  printf("%s\n", bad ? "FAIL" : "PASS");
  return bad;
}
