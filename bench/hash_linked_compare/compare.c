/* compare.c -- conformance and timing of the compiler's SHA-512, BLAKE2b and
 * Keccak-f[1600] objects against OpenSSL, HACL* and XKCP.
 *
 *   compare conform [NRAND]   official vectors, then NRAND random inputs per
 *                             kernel compared word for word with every peer;
 *                             exit 1 on any mismatch.
 *   compare bench [--cpu C] [--samples S] [--inner I] [--run R] [--label L]
 *                             TSV: kernel, arm, median and minimum TSC cycles
 *                             per call over S samples of I chained calls.
 *
 * Chaining: every arm's call depends on the previous call's output, so no arm
 * overlaps independent calls.  The peers update their state in place; ours
 * alternates two input arrays, writing each call's output words into the
 * chaining words (or lanes) of the other array.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "affinity.h"
#include "arms.h"
#include "tscbench.h"

/* ---- inputs ---------------------------------------------------------------- */

static uint64_t rng_state = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd64(void) {
  uint64_t x = rng_state;
  x ^= x >> 12;
  x ^= x << 25;
  x ^= x >> 27;
  rng_state = x;
  return x * 0x2545F4914F6CDD1DULL;
}
static void rnd_bytes(uint8_t *p, int n) {
  for (int i = 0; i < n; i++) p[i] = (uint8_t)rnd64();
}

static uint64_t load_be64(const uint8_t *p) {
  uint64_t w = 0;
  for (int i = 0; i < 8; i++) w = (w << 8) | p[i];
  return w;
}
static uint64_t load_le64(const uint8_t *p) {
  uint64_t w = 0;
  for (int i = 7; i >= 0; i--) w = (w << 8) | p[i];
  return w;
}
static void store_be64(uint8_t *p, uint64_t w) {
  for (int i = 7; i >= 0; i--) { p[i] = (uint8_t)w; w >>= 8; }
}
static void store_le64(uint8_t *p, uint64_t w) {
  for (int i = 0; i < 8; i++) { p[i] = (uint8_t)w; w >>= 8; }
}

static const uint64_t SHA512_IV[8] = {
  0x6a09e667f3bcc908ULL, 0xbb67ae8584caa73bULL, 0x3c6ef372fe94f82bULL,
  0xa54ff53a5f1d36f1ULL, 0x510e527fade682d1ULL, 0x9b05688c2b3e6c1fULL,
  0x1f83d9abfb41bd6bULL, 0x5be0cd19137e2179ULL};

/* ---- the three kernels as functions of (state, block) ------------------------ */

static void ours_sha512(uint64_t h[8], const uint8_t blk[128]) {
  uint64_t hm[24], out[8];
  for (int i = 0; i < 8; i++) hm[i] = h[i];
  for (int j = 0; j < 16; j++) hm[8 + j] = load_be64(blk + 8 * j);
  ours_sha512_compress(out, hm);
  memcpy(h, out, sizeof out);
}

static void ours_blake2b(uint64_t h[8], const uint8_t blk[128], uint64_t t0, uint64_t t1,
                         int last) {
  uint64_t hm[24], out[8];
  for (int i = 0; i < 8; i++) hm[i] = h[i];
  for (int j = 0; j < 16; j++) hm[8 + j] = load_le64(blk + 8 * j);
  ours_blake2b_compress(out, last ? ~0ULL : 0ULL, t1, t0, hm);
  memcpy(h, out, sizeof out);
}

static void hacl_blake2b(uint64_t h[8], const uint8_t blk[128], uint64_t t0, uint64_t t1,
                         int last) {
  uint64_t hash16[16], wv[16];
  peer_hacl_blake2b_init_rows(hash16, h);
  peer_hacl_blake2b(hash16, wv, blk, t0, t1, last);
  memcpy(h, hash16, 8 * sizeof(uint64_t));
}

static void ours_keccak(uint64_t s[25]) {
  uint64_t out[25];
  ours_keccak_f1600(out, s);
  memcpy(s, out, sizeof out);
}

/* ---- conformance --------------------------------------------------------- */

static int failures = 0;

static void check_words(const char *what, const uint64_t *a, const uint64_t *b, int n) {
  for (int i = 0; i < n; i++)
    if (a[i] != b[i]) {
      printf("MISMATCH %s word %d: %016llx != %016llx\n", what, i, (unsigned long long)a[i],
             (unsigned long long)b[i]);
      failures++;
      return;
    }
}

static void check_bytes(const char *what, const uint8_t *a, const uint8_t *b, int n) {
  if (memcmp(a, b, (size_t)n) != 0) {
    printf("MISMATCH %s\n", what);
    failures++;
  } else {
    printf("ok       %s\n", what);
  }
}

static void hex_to_bytes(const char *hex, uint8_t *out, int n) {
  for (int i = 0; i < n; i++) {
    unsigned v;
    sscanf(hex + 2 * i, "%2x", &v);
    out[i] = (uint8_t)v;
  }
}

/* FIPS 180-4 / FIPS 202 / RFC 7693 vectors for the message "abc". */
static const char *SHA512_ABC =
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
    "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f";
static const char *BLAKE2B512_ABC =
    "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1"
    "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923";
static const char *SHA3_256_ABC =
    "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532";

static void vectors(void) {
  const uint8_t abc[3] = {'a', 'b', 'c'};
  uint8_t want[64], evp[64];
  unsigned evplen = 0;

  /* SHA-512("abc"): one compression from the IV over the padded block. */
  {
    uint8_t blk[128] = {0}, got[64];
    memcpy(blk, abc, 3);
    blk[3] = 0x80;
    blk[127] = 24;
    uint64_t h[8];
    memcpy(h, SHA512_IV, sizeof h);
    ours_sha512(h, blk);
    for (int i = 0; i < 8; i++) store_be64(got + 8 * i, h[i]);
    hex_to_bytes(SHA512_ABC, want, 64);
    if (evp_digest("SHA512", abc, 3, evp, &evplen)) check_bytes("vector literal SHA-512(abc) = OpenSSL EVP", want, evp, 64);
    check_bytes("ours sha512_compress: SHA-512(abc) (FIPS 180-4)", got, want, 64);
  }

  /* BLAKE2b-512("abc"): h = IV ^ P (digest 64, no key), t = 3, final flag. */
  {
    uint8_t blk[128] = {0}, got[64];
    memcpy(blk, abc, 3);
    uint64_t h[8];
    memcpy(h, SHA512_IV, sizeof h);
    h[0] ^= 0x01010040ULL;
    ours_blake2b(h, blk, 3, 0, 1);
    for (int i = 0; i < 8; i++) store_le64(got + 8 * i, h[i]);
    hex_to_bytes(BLAKE2B512_ABC, want, 64);
    if (evp_digest("BLAKE2B-512", abc, 3, evp, &evplen)) check_bytes("vector literal BLAKE2b-512(abc) = OpenSSL EVP", want, evp, 64);
    check_bytes("ours blake2b_compress: BLAKE2b-512(abc) (RFC 7693 App. A)", got, want, 64);
  }

  /* SHA3-256("abc"): one permutation of the absorbed padded block (rate 136). */
  {
    uint8_t blk[200] = {0}, got[32];
    memcpy(blk, abc, 3);
    blk[3] ^= 0x06;
    blk[135] ^= 0x80;
    uint64_t s[25];
    for (int i = 0; i < 25; i++) s[i] = load_le64(blk + 8 * i);
    ours_keccak(s);
    for (int i = 0; i < 4; i++) store_le64(got + 8 * i, s[i]);
    hex_to_bytes(SHA3_256_ABC, want, 32);
    if (evp_digest("SHA3-256", abc, 3, evp, &evplen)) check_bytes("vector literal SHA3-256(abc) = OpenSSL EVP", want, evp, 32);
    check_bytes("ours keccak_f1600: SHA3-256(abc) (FIPS 202)", got, want, 32);
  }

  /* Keccak-f[1600] of the zero state: lane 0 (Keccak team intermediate values). */
  {
    uint64_t s[25] = {0};
    ours_keccak(s);
    uint64_t want0 = 0xF1258F7940E1DDE7ULL;
    check_words("ours keccak_f1600: lane 0 of keccak_f(0)", s, &want0, 1);
    if (s[0] == want0) printf("ok       ours keccak_f1600: lane 0 of keccak_f(0)\n");
  }
}

static void random_batch(long nrand) {
  long n0 = failures;
  for (long r = 0; r < nrand; r++) {
    uint8_t blk[128];
    uint64_t h0[8];
    rnd_bytes(blk, 128);
    for (int i = 0; i < 8; i++) h0[i] = rnd64();

    uint64_t a[8], b[8], c[8];
    memcpy(a, h0, sizeof a); memcpy(b, h0, sizeof b); memcpy(c, h0, sizeof c);
    ours_sha512(a, blk);
    peer_openssl_sha512(b, blk);
    peer_hacl_sha512(c, blk);
    check_words("sha512 ours vs OpenSSL", a, b, 8);
    check_words("sha512 ours vs HACL*", a, c, 8);

    uint64_t t0 = rnd64(), t1 = rnd64();
    int last = (int)(rnd64() & 1);
    memcpy(a, h0, sizeof a); memcpy(b, h0, sizeof b);
    ours_blake2b(a, blk, t0, t1, last);
    hacl_blake2b(b, blk, t0, t1, last);
    check_words("blake2b ours vs HACL*", a, b, 8);

    uint64_t s[25], x[25], y[25];
    for (int i = 0; i < 25; i++) s[i] = x[i] = y[i] = rnd64();
    ours_keccak(s);
    peer_xkcp_keccak_f1600(x);
    peer_hacl_keccak_f1600(y);
    check_words("keccak_f1600 ours vs XKCP", s, x, 25);
    check_words("keccak_f1600 ours vs HACL*", s, y, 25);
    if (failures - n0 > 10) break;
  }
  if (failures == n0)
    printf("ok       random batch: %ld inputs per kernel, ours = every peer\n", nrand);
}

/* ---- timing -------------------------------------------------------------- */

typedef struct {
  long samples, inner;
} Cfg;

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y;
}

#define TIME_ARM(kernel, arm, BODY)                                               \
  do {                                                                            \
    uint64_t *d_ = malloc(sizeof(uint64_t) * (size_t)cfg.samples);                \
    for (long w_ = 0; w_ < cfg.inner; w_++) { BODY; }                             \
    for (long s_ = 0; s_ < cfg.samples; s_++) {                                   \
      uint64_t t0_ = rdtsc_start();                                               \
      for (long i_ = 0; i_ < cfg.inner; i_++) { BODY; }                           \
      uint64_t t1_ = rdtsc_end();                                                 \
      d_[s_] = t1_ - t0_;                                                         \
    }                                                                             \
    qsort(d_, (size_t)cfg.samples, sizeof *d_, cmp_u64);                          \
    printf("%s\t%s\t%.1f\t%.1f\t%s\t%d\n", kernel, arm,                           \
           (double)d_[cfg.samples / 2] / (2.0 * (double)cfg.inner),               \
           (double)d_[0] / (2.0 * (double)cfg.inner), label, run);                \
    free(d_);                                                                     \
  } while (0)

static void bench(Cfg cfg, const char *label, int run) {
  uint8_t blk[128];
  rnd_bytes(blk, 128);
  printf("# kernel\tarm\tmedian_cyc\tmin_cyc\tlabel\trun\n");

  /* SHA-512 */
  {
    uint64_t A[24], B[24];
    for (int j = 0; j < 16; j++) A[8 + j] = B[8 + j] = load_be64(blk + 8 * j);
    memcpy(A, SHA512_IV, 64); memcpy(B, SHA512_IV, 64);
    TIME_ARM("sha512_compress", "ours", { ours_sha512_compress(B, A); ours_sha512_compress(A, B); });
    void *ctx = peer_openssl_sha512_ctx();
    TIME_ARM("sha512_compress", "openssl", { peer_openssl_sha512_ctx_step(ctx, blk); peer_openssl_sha512_ctx_step(ctx, blk); });
    free(ctx);
    uint64_t st[8];
    memcpy(st, SHA512_IV, 64);
    TIME_ARM("sha512_compress", "hacl", { peer_hacl_sha512(st, blk); peer_hacl_sha512(st, blk); });
  }

  /* BLAKE2b */
  {
    uint64_t A[24], B[24];
    for (int j = 0; j < 16; j++) A[8 + j] = B[8 + j] = load_le64(blk + 8 * j);
    memcpy(A, SHA512_IV, 64); memcpy(B, SHA512_IV, 64);
    TIME_ARM("blake2b_compress", "ours", { ours_blake2b_compress(B, 0, 0, 128, A); ours_blake2b_compress(A, 0, 0, 128, B); });
    uint64_t hash16[16], wv[16];
    peer_hacl_blake2b_init_rows(hash16, SHA512_IV);
    TIME_ARM("blake2b_compress", "hacl", { peer_hacl_blake2b(hash16, wv, blk, 128, 0, 0); peer_hacl_blake2b(hash16, wv, blk, 128, 0, 0); });
  }

  /* Keccak-f[1600] */
  {
    uint64_t A[25], B[25];
    for (int i = 0; i < 25; i++) A[i] = rnd64();
    TIME_ARM("keccak_f1600", "ours", { ours_keccak_f1600(B, A); ours_keccak_f1600(A, B); });
    void *st = peer_xkcp_state();
    TIME_ARM("keccak_f1600", "xkcp", { peer_xkcp_state_step(st); peer_xkcp_state_step(st); });
    free(st);
    uint64_t s[25];
    for (int i = 0; i < 25; i++) s[i] = rnd64();
    TIME_ARM("keccak_f1600", "hacl", { peer_hacl_keccak_f1600(s); peer_hacl_keccak_f1600(s); });
  }
}

/* Every TIME_ARM body makes two calls; TIME_ARM divides by 2 * inner. */
int main(int argc, char **argv) {
  if (argc >= 2 && strcmp(argv[1], "conform") == 0) {
    long nrand = argc >= 3 ? atol(argv[2]) : 10000;
    vectors();
    random_batch(nrand);
    printf("%s: %d mismatch(es)\n", failures ? "FAIL" : "PASS", failures);
    return failures ? 1 : 0;
  }
  if (argc >= 2 && strcmp(argv[1], "bench") == 0) {
    Cfg cfg = {501, 500};
    int cpu = -1, run = 0;
    const char *label = "unlabelled";
    for (int i = 2; i + 1 < argc; i += 2) {
      if (!strcmp(argv[i], "--cpu")) cpu = atoi(argv[i + 1]);
      else if (!strcmp(argv[i], "--samples")) cfg.samples = atol(argv[i + 1]);
      else if (!strcmp(argv[i], "--inner")) cfg.inner = atol(argv[i + 1]);
      else if (!strcmp(argv[i], "--run")) run = atoi(argv[i + 1]);
      else if (!strcmp(argv[i], "--label")) label = argv[i + 1];
      else { fprintf(stderr, "unknown argument %s\n", argv[i]); return 2; }
    }
    if (cpu >= 0 && pin_to_cpu(cpu) != 0) fprintf(stderr, "warning: could not pin to cpu %d\n", cpu);
    /* --inner counts calls; the loop runs inner / 2 steps of two calls. */
    cfg.inner = cfg.inner > 1 ? cfg.inner / 2 : 1;
    printf("# hash_linked_compare: TSC cycles per call (two chained calls per inner step)\n");
    bench(cfg, label, run);
    return 0;
  }
  fprintf(stderr, "usage: %s conform [NRAND] | bench [--cpu C] [--samples S] [--inner I] "
                  "[--run R] [--label L]\n", argv[0]);
  return 2;
}
