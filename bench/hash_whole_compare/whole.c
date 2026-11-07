/* whole.c -- known-answer checks and timing of whole hash functions: the compiler's
 * entries (orchestration compiled by compileA, the compression or permutation a linked
 * kernel) against HACL* full hashes, OpenSSL EVP and libsodium.
 *
 *   whole kat                  for every hash, every length of KAT_LENS and every arm built
 *                              in: the digest of the test message against kat_table.h; our
 *                              objects also through abi_check_call (callee-saved registers
 *                              kept, same digest); exit 1 on any mismatch.
 *   whole bench [--cpu C] [--samples S] [--inner I] [--run R] [--label L]
 *                              (built only into `whole-bench`) TSV: hash, length, arm, median
 *                              and minimum TSC cycles per call over S samples of I calls,
 *                              after the known-answer checks pass.
 *
 * The arms of a hash: `openssl` (EVP), `hacl` (HACL* one-shot functions, -DWITH_HACL),
 * `sodium` (crypto_generichash, BLAKE2b only), `ours` (the objects of gen/, -DWITH_OURS).
 * Our entries take the message as 2048 64-bit words with the memory layout of the byte
 * buffer padded to whole words, and the byte length; the bytes of the buffer beyond the
 * length are set to 0xa5 here, so that an entry reading them fails the check. Each entry
 * takes its storage arrays (the sponge states, or the output and input arrays of the
 * compression) and writes the digest bytes, as words, to its last argument.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <openssl/crypto.h>
#include <openssl/evp.h>

#if defined(__has_include)
#if __has_include(<sodium.h>)
#include <sodium.h>
#define HAVE_SODIUM_H 1
#endif
#endif
#ifndef HAVE_SODIUM_H
int sodium_init(void);
int crypto_generichash(unsigned char *out, size_t outlen, const unsigned char *in,
                       unsigned long long inlen, const unsigned char *key, size_t keylen);
#endif

#include "kat_table.h"

#ifdef WITH_BENCH
#include "affinity.h"
#include "tscbench.h"
#endif

#define MSG_WORDS 2048
#define MAX_LEN (8 * MSG_WORDS)

typedef void (*hash_fn)(uint8_t *out, const uint8_t *msg, unsigned long len);

/* ---- OpenSSL EVP ---------------------------------------------------------------- */

static void evp_fixed(const char *name, uint8_t *out, const uint8_t *msg, unsigned long len) {
  unsigned outlen = 0;
  if (!EVP_Digest(msg, len, out, &outlen, EVP_get_digestbyname(name), NULL)) {
    fprintf(stderr, "EVP_Digest(%s) failed\n", name);
    exit(2);
  }
}

static void evp_xof(const char *name, uint8_t *out, size_t outlen, const uint8_t *msg,
                    unsigned long len) {
  EVP_MD_CTX *c = EVP_MD_CTX_new();
  if (!c || !EVP_DigestInit_ex(c, EVP_get_digestbyname(name), NULL) ||
      !EVP_DigestUpdate(c, msg, len) || !EVP_DigestFinalXOF(c, out, outlen)) {
    fprintf(stderr, "EVP XOF %s failed\n", name);
    exit(2);
  }
  EVP_MD_CTX_free(c);
}

static void ossl_sha512(uint8_t *o, const uint8_t *m, unsigned long n) { evp_fixed("SHA512", o, m, n); }
static void ossl_sha3_256(uint8_t *o, const uint8_t *m, unsigned long n) { evp_fixed("SHA3-256", o, m, n); }
static void ossl_shake128_256(uint8_t *o, const uint8_t *m, unsigned long n) { evp_xof("SHAKE128", o, 32, m, n); }
static void ossl_shake256_512(uint8_t *o, const uint8_t *m, unsigned long n) { evp_xof("SHAKE256", o, 64, m, n); }
static void ossl_blake2b_512(uint8_t *o, const uint8_t *m, unsigned long n) { evp_fixed("BLAKE2B512", o, m, n); }

/* ---- libsodium -------------------------------------------------------------------- */

static void sodium_blake2b_512(uint8_t *o, const uint8_t *m, unsigned long n) {
  if (crypto_generichash(o, 64, m, n, NULL, 0) != 0) {
    fprintf(stderr, "crypto_generichash failed\n");
    exit(2);
  }
}

/* ---- HACL* ------------------------------------------------------------------------ */

#ifdef WITH_HACL
void hacl_sha512(uint8_t *o, const uint8_t *m, unsigned long n);
void hacl_sha3_256(uint8_t *o, const uint8_t *m, unsigned long n);
void hacl_shake128_256(uint8_t *o, const uint8_t *m, unsigned long n);
void hacl_shake256_512(uint8_t *o, const uint8_t *m, unsigned long n);
void hacl_blake2b_512(uint8_t *o, const uint8_t *m, unsigned long n);
#endif

/* ---- ours ------------------------------------------------------------------------- */

#ifdef WITH_OURS
void catcrypt_sha3_256_words(const uint64_t *msg, uint64_t len, uint64_t *st, uint64_t *st2,
                             uint64_t *out);
void catcrypt_shake128_256_words(const uint64_t *msg, uint64_t len, uint64_t *st,
                                 uint64_t *st2, uint64_t *out);
void catcrypt_shake256_512_words(const uint64_t *msg, uint64_t len, uint64_t *st,
                                 uint64_t *st2, uint64_t *out);
void catcrypt_blake2b_512_words(const uint64_t *msg, uint64_t len, uint64_t *hd, uint64_t *hm,
                                uint64_t *out);
void catcrypt_sha512_words(const uint64_t *msg, uint64_t len, uint64_t *hd, uint64_t *hm,
                           uint64_t *out);
long abi_check_call(void *fn, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4);

/* The word buffer of every call of ours: the message, then 0xa5 up to MAX_LEN. */
static uint64_t wbuf[MSG_WORDS];
static unsigned long wbuf_len = (unsigned long)-1;
static const uint8_t *wbuf_src = NULL;

static const uint64_t *words_of(const uint8_t *m, unsigned long n) {
  if (wbuf_src != m || wbuf_len != n) {
    memset(wbuf, 0xa5, sizeof wbuf);
    memcpy(wbuf, m, n);
    wbuf_src = m;
    wbuf_len = n;
  }
  return wbuf;
}

/* An entry: its symbol, the lengths of its two storage arrays and its output words. */
typedef struct {
  void *fn;
  int s1, s2, ow;
} entry;

static void call_entry(entry e, uint8_t *o, const uint8_t *m, unsigned long n) {
  uint64_t s1[25], s2[25], out[8];
  ((void (*)(const uint64_t *, uint64_t, uint64_t *, uint64_t *, uint64_t *))e.fn)(
      words_of(m, n), n, s1, s2, out);
  memcpy(o, out, 8 * (size_t)e.ow);
}

static const entry E_SHA3_256 = {(void *)catcrypt_sha3_256_words, 25, 25, 4};
static const entry E_SHAKE128 = {(void *)catcrypt_shake128_256_words, 25, 25, 4};
static const entry E_SHAKE256 = {(void *)catcrypt_shake256_512_words, 25, 25, 8};
static const entry E_BLAKE2B = {(void *)catcrypt_blake2b_512_words, 8, 24, 8};
static const entry E_SHA512 = {(void *)catcrypt_sha512_words, 8, 24, 8};

static void ours_sha3_256(uint8_t *o, const uint8_t *m, unsigned long n) { call_entry(E_SHA3_256, o, m, n); }
static void ours_shake128_256(uint8_t *o, const uint8_t *m, unsigned long n) { call_entry(E_SHAKE128, o, m, n); }
static void ours_shake256_512(uint8_t *o, const uint8_t *m, unsigned long n) { call_entry(E_SHAKE256, o, m, n); }
static void ours_blake2b_512(uint8_t *o, const uint8_t *m, unsigned long n) { call_entry(E_BLAKE2B, o, m, n); }
static void ours_sha512(uint8_t *o, const uint8_t *m, unsigned long n) { call_entry(E_SHA512, o, m, n); }

/* abi_check_call(fn, a0, a1, a2, a3, a4): %rdi = fn, %rsi..%r9 = a0..a4.  The six
 * callee-saved registers are pushed, set to the sentinels 0x5a5a...00 + k, the
 * entry is called with a0..a4 in %rdi, %rsi, %rdx, %rcx, %r8, the registers are
 * compared with the sentinels, restored, and the count of differences returned. */
__asm__(".text\n"
        ".globl abi_check_call\n"
        ".type abi_check_call,@function\n"
        ".p2align 4\n"
        "abi_check_call:\n"
        "  push %rbx\n  push %rbp\n  push %r12\n  push %r13\n  push %r14\n  push %r15\n"
        "  sub $8, %rsp\n"
        "  mov %rdi, %rax\n"
        "  mov %rsi, %rdi\n  mov %rdx, %rsi\n  mov %rcx, %rdx\n  mov %r8, %rcx\n"
        "  mov %r9, %r8\n"
        "  movabs $0x5a5a5a5a5a5a5a00, %rbx\n"
        "  lea 1(%rbx), %rbp\n  lea 2(%rbx), %r12\n  lea 3(%rbx), %r13\n"
        "  lea 4(%rbx), %r14\n  lea 5(%rbx), %r15\n"
        "  call *%rax\n"
        "  xor %eax, %eax\n"
        "  movabs $0x5a5a5a5a5a5a5a00, %rcx\n"
        "  xor %edx, %edx\n  cmp %rcx, %rbx\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %rbp\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %r12\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %r13\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %r14\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %r15\n  setne %dl\n  add %rdx, %rax\n"
        "  add $8, %rsp\n"
        "  pop %r15\n  pop %r14\n  pop %r13\n  pop %r12\n  pop %rbp\n  pop %rbx\n"
        "  ret\n"
        ".size abi_check_call, .-abi_check_call\n");
#endif

/* ---- the table of hashes and arms --------------------------------------------------- */

typedef struct {
  const char *arm;
  hash_fn f;
} arm;

typedef struct {
  const char *name;
  int outlen;
  const char *const *kat;
  arm arms[5];
#ifdef WITH_OURS
  const entry *ours;
#endif
} hash;

#ifdef WITH_HACL
#define HACL_ARM(f) {"hacl", f},
#else
#define HACL_ARM(f)
#endif
#ifdef WITH_OURS
#define OURS_ARM(f) {"ours", f},
#define OURS_ENTRY(e) , &e
#else
#define OURS_ARM(f)
#define OURS_ENTRY(e)
#endif

static const hash HASHES[] = {
    {"sha512", 64, KAT_SHA512,
     {{"openssl", ossl_sha512}, HACL_ARM(hacl_sha512) OURS_ARM(ours_sha512)} OURS_ENTRY(E_SHA512)},
    {"sha3_256", 32, KAT_SHA3_256,
     {{"openssl", ossl_sha3_256}, HACL_ARM(hacl_sha3_256) OURS_ARM(ours_sha3_256)}
     OURS_ENTRY(E_SHA3_256)},
    {"shake128_256", 32, KAT_SHAKE128_256,
     {{"openssl", ossl_shake128_256}, HACL_ARM(hacl_shake128_256) OURS_ARM(ours_shake128_256)}
     OURS_ENTRY(E_SHAKE128)},
    {"shake256_512", 64, KAT_SHAKE256_512,
     {{"openssl", ossl_shake256_512}, HACL_ARM(hacl_shake256_512) OURS_ARM(ours_shake256_512)}
     OURS_ENTRY(E_SHAKE256)},
    {"blake2b_512", 64, KAT_BLAKE2B_512,
     {{"openssl", ossl_blake2b_512}, {"sodium", sodium_blake2b_512},
      HACL_ARM(hacl_blake2b_512) OURS_ARM(ours_blake2b_512)} OURS_ENTRY(E_BLAKE2B)},
};
#define NHASH (int)(sizeof HASHES / sizeof HASHES[0])

/* ---- known-answer checks ------------------------------------------------------------ */

static uint8_t msgbuf[MAX_LEN];

static void fill_msg(unsigned long n) {
  for (unsigned long i = 0; i < n; i++) msgbuf[i] = (uint8_t)((i * 31 + 7) & 0xff);
}

static void hex(const uint8_t *b, int n, char *out) {
  for (int i = 0; i < n; i++) sprintf(out + 2 * i, "%02x", b[i]);
  out[2 * n] = 0;
}

static int kat(void) {
  int failures = 0, checks = 0;
  char got[129];
  for (int h = 0; h < NHASH; h++) {
    const hash *H = &HASHES[h];
    for (int k = 0; k < 8; k++) {
      unsigned long n = KAT_LENS[k];
      fill_msg(n);
      for (int a = 0; a < 5 && H->arms[a].arm; a++) {
        uint8_t d[64];
        memset(d, 0, sizeof d);
        H->arms[a].f(d, msgbuf, n);
        hex(d, H->outlen, got);
        int ok = strcmp(got, H->kat[k]) == 0;
        printf("%-8s %-13s %-8s %6lu\n", ok ? "ok" : "MISMATCH", H->name, H->arms[a].arm, n);
        if (!ok) {
          printf("  got      %s\n  expected %s\n", got, H->kat[k]);
          failures++;
        }
        checks++;
      }
#ifdef WITH_OURS
      /* Ours through abi_check_call: callee-saved registers kept, same digest. */
      {
        const entry *e = H->ours;
        uint64_t s1[25], s2[25], out[8];
        long dr = abi_check_call(e->fn, (uint64_t)(uintptr_t)words_of(msgbuf, n), n,
                                 (uint64_t)(uintptr_t)s1, (uint64_t)(uintptr_t)s2,
                                 (uint64_t)(uintptr_t)out);
        hex((const uint8_t *)out, H->outlen, got);
        int ok = dr == 0 && strcmp(got, H->kat[k]) == 0;
        printf("%-8s %-13s %-8s %6lu  (abi_check_call: %ld callee-saved registers changed)\n",
               ok ? "ok" : "MISMATCH", H->name, "ours-abi", n, dr);
        if (!ok) failures++;
        checks++;
      }
#endif
    }
  }
  printf("# %d checks, %d mismatches; arms: openssl%s%s, sodium (blake2b_512)\n", checks,
         failures,
#ifdef WITH_HACL
         ", hacl",
#else
         " (hacl not built)",
#endif
#ifdef WITH_OURS
         ", ours"
#else
         " (ours not built: no gen/*.o)"
#endif
  );
  return failures;
}

/* ---- timing (reference host) ---------------------------------------------------------- */

#ifdef WITH_BENCH
typedef struct {
  int cpu;
  long samples, inner;
} Cfg;

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y;
}

/* Each call's first digest byte is folded into the first message byte, so that the calls
 * of a sample depend on one another. */
static void bench(Cfg cfg, const char *label, int run) {
  uint64_t *d = malloc(sizeof(uint64_t) * (size_t)cfg.samples);
  printf("# hash\tlen\tarm\tmedian_cyc\tmin_cyc\tlabel\trun\n");
  for (int h = 0; h < NHASH; h++) {
    const hash *H = &HASHES[h];
    for (int k = 0; k < 8; k++) {
      unsigned long n = KAT_LENS[k];
      for (int a = 0; a < 5 && H->arms[a].arm; a++) {
        uint8_t o[64] = {0};
        fill_msg(n);
        for (long w = 0; w < cfg.inner; w++) {
          H->arms[a].f(o, msgbuf, n);
          if (n) msgbuf[0] ^= o[0];
        }
        for (long s = 0; s < cfg.samples; s++) {
          uint64_t t0 = rdtsc_start();
          for (long i = 0; i < cfg.inner; i++) {
            H->arms[a].f(o, msgbuf, n);
            if (n) msgbuf[0] ^= o[0];
          }
          uint64_t t1 = rdtsc_end();
          d[s] = t1 - t0;
        }
        qsort(d, (size_t)cfg.samples, sizeof *d, cmp_u64);
        printf("%s\t%lu\t%s\t%.1f\t%.1f\t%s\t%d\n", H->name, n, H->arms[a].arm,
               (double)d[cfg.samples / 2] / (double)cfg.inner, (double)d[0] / (double)cfg.inner,
               label, run);
      }
    }
  }
  free(d);
}
#endif

int main(int argc, char **argv) {
  if (sodium_init() < 0) {
    fprintf(stderr, "sodium_init failed\n");
    return 2;
  }
  printf("# OpenSSL: %s\n", OpenSSL_version(OPENSSL_VERSION));
  if (argc >= 2 && strcmp(argv[1], "kat") == 0) return kat() ? 1 : 0;
#ifdef WITH_BENCH
  if (argc >= 2 && strcmp(argv[1], "bench") == 0) {
    Cfg cfg = {2, 101, 50};
    const char *label = "unlabelled";
    int run = 1;
    for (int i = 2; i + 1 < argc; i += 2) {
      if (!strcmp(argv[i], "--cpu")) cfg.cpu = atoi(argv[i + 1]);
      else if (!strcmp(argv[i], "--samples")) cfg.samples = atol(argv[i + 1]);
      else if (!strcmp(argv[i], "--inner")) cfg.inner = atol(argv[i + 1]);
      else if (!strcmp(argv[i], "--run")) run = atoi(argv[i + 1]);
      else if (!strcmp(argv[i], "--label")) label = argv[i + 1];
    }
    if (kat()) return 1;
    pin_to_cpu(cfg.cpu);
    bench(cfg, label, run);
    return 0;
  }
#endif
  fprintf(stderr, "usage: %s kat%s\n", argv[0],
#ifdef WITH_BENCH
          " | bench [--cpu C] [--samples S] [--inner I] [--run R] [--label L]"
#else
          ""
#endif
  );
  return 2;
}
