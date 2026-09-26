/* KAT harness for the front-compiled Mersenne-31 field kernels.
 *
 * The kernels are emitted by CatCrypt's verified front (no jasminc, no hand
 * Com/Lcmd):
 *
 *   Mersenne31FrontEmit body (LowCT: RArrLoad / RScalarSetExpr / RArrStore)
 *     -> translateDialectControl        (CProg-free front)
 *     -> cryptoDialectToJasminCom       (stackLoad/stackStore)
 *     -> Com.toLprogPhysAbi + renderLprogAtt
 *     -> gen_com/m31_field_owned.s
 *
 * Field: GF(p), p = 2^31 - 1 = 2147483647 (Mersenne-31), the CircleSTARK /
 * Plonky3-M31 / Stwo base field. The kernels use the branch-free Mersenne
 * shape (2^31 == 1 mod p): double fold (v & p) + (v >> 31) plus one
 * mask-based conditional subtract. Constant-time (no data-dependent branch).
 *
 * INDEPENDENT reference: direct `__int128 % p` / `% p` arithmetic below —
 * NOT the fold shape — matching the canonical-residue semantics of plonky3's
 * Mersenne31 (as_canonical_u31) and Stwo's M31.
 *
 * Phases:
 *   1. edge vectors        (0, 1, small, 2^30, p-2, p-1 cross products;
 *                           reduce edges up to 2^62 - 1)
 *   2. small exhaustive    (a, b in [0, 256)^2; reduce x in [0, 65536))
 *   3. boundary band       (a, b in [p-256, p)^2)
 *   4. random              (1,000,000 xorshift64* vectors; reduce < 2^62)
 * plus a light cyc/op timer on the multiply.
 *
 * Build:
 *   cc -O2 -o m31_field_kat m31_field_kat.c gen_com/m31_field_owned.s
 *   ./m31_field_kat
 */
#include <stdint.h>
#include <stdio.h>

/* The emitted owned exports. SysV pointer ABI, one u64 cell per pointer:
 *   RDI = out, RSI = a, RDX = b   (reduce: RDI = out, RSI = x). */
extern uint64_t *m31_mul_owned(uint64_t *out, const uint64_t *a, const uint64_t *b);
extern uint64_t *m31_add_owned(uint64_t *out, const uint64_t *a, const uint64_t *b);
extern uint64_t *m31_reduce_owned(uint64_t *out, const uint64_t *x);

static const uint64_t P = 2147483647ULL; /* 2^31 - 1 */

/* ---- independent reference: direct modular arithmetic, no Mersenne fold ---- */
static uint64_t m31_mul_ref(uint64_t a, uint64_t b) {
  return (uint64_t)(((unsigned __int128)a * (unsigned __int128)b) % P);
}
static uint64_t m31_add_ref(uint64_t a, uint64_t b) { return (a + b) % P; }
static uint64_t m31_reduce_ref(uint64_t x) { return x % P; }

/* ---- xorshift64* PRNG (deterministic vectors) ---- */
static uint64_t rng_state = 0x9E3779B97F4A7C15ULL;
static uint64_t rng(void) {
  uint64_t x = rng_state;
  x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
  rng_state = x;
  return x * 0x2545F4914F6CDD1DULL;
}

static long fails = 0;

static void check_mul(uint64_t a, uint64_t b) {
  uint64_t out = 0xDEADBEEFDEADBEEFULL;
  m31_mul_owned(&out, &a, &b);
  uint64_t want = m31_mul_ref(a, b);
  if (out != want) {
    if (fails < 10)
      printf("MUL FAIL a=%llu b=%llu got=%llu want=%llu\n",
             (unsigned long long)a, (unsigned long long)b,
             (unsigned long long)out, (unsigned long long)want);
    fails++;
  }
}

static void check_add(uint64_t a, uint64_t b) {
  uint64_t out = 0xDEADBEEFDEADBEEFULL;
  m31_add_owned(&out, &a, &b);
  uint64_t want = m31_add_ref(a, b);
  if (out != want) {
    if (fails < 10)
      printf("ADD FAIL a=%llu b=%llu got=%llu want=%llu\n",
             (unsigned long long)a, (unsigned long long)b,
             (unsigned long long)out, (unsigned long long)want);
    fails++;
  }
}

static void check_reduce(uint64_t x) {
  uint64_t out = 0xDEADBEEFDEADBEEFULL;
  m31_reduce_owned(&out, &x);
  uint64_t want = m31_reduce_ref(x);
  if (out != want) {
    if (fails < 10)
      printf("REDUCE FAIL x=%llu got=%llu want=%llu\n",
             (unsigned long long)x, (unsigned long long)out,
             (unsigned long long)want);
    fails++;
  }
}

static uint64_t rdtsc_begin(void) {
  uint32_t lo, hi;
  __asm__ volatile("cpuid\n\trdtsc" : "=a"(lo), "=d"(hi) :: "rbx", "rcx");
  return ((uint64_t)hi << 32) | lo;
}
static uint64_t rdtsc_end(void) {
  uint32_t lo, hi;
  __asm__ volatile("rdtscp" : "=a"(lo), "=d"(hi) :: "rcx");
  return ((uint64_t)hi << 32) | lo;
}

int main(void) {
  long n = 0;

  /* Phase 1: edge vectors. */
  const uint64_t edges[] = {0, 1, 2, 3, 1073741824ULL /* 2^30 */,
                            P - 2, P - 1};
  const int ne = sizeof(edges) / sizeof(edges[0]);
  for (int i = 0; i < ne; i++)
    for (int j = 0; j < ne; j++) {
      check_mul(edges[i], edges[j]);
      check_add(edges[i], edges[j]);
      n += 2;
    }
  const uint64_t redges[] = {0, 1, P - 1, P, P + 1,
                             2147483648ULL /* 2^31 */, 4294967295ULL /* 2^32-1 */,
                             (P - 1) * (P - 1), (1ULL << 62) - 1};
  for (int i = 0; i < (int)(sizeof(redges) / sizeof(redges[0])); i++) {
    check_reduce(redges[i]);
    n++;
  }
  printf("phase 1 (edges): %ld checks, fails so far %ld\n", n, fails);

  /* Phase 2: small exhaustive. */
  for (uint64_t a = 0; a < 256; a++)
    for (uint64_t b = 0; b < 256; b++) {
      check_mul(a, b);
      check_add(a, b);
      n += 2;
    }
  for (uint64_t x = 0; x < 65536; x++) {
    check_reduce(x);
    n++;
  }
  printf("phase 2 (small exhaustive): %ld checks, fails so far %ld\n", n, fails);

  /* Phase 3: boundary band [p-256, p)^2. */
  for (uint64_t a = P - 256; a < P; a++)
    for (uint64_t b = P - 256; b < P; b++) {
      check_mul(a, b);
      check_add(a, b);
      n += 2;
    }
  printf("phase 3 (boundary band): %ld checks, fails so far %ld\n", n, fails);

  /* Phase 4: random. */
  for (long i = 0; i < 1000000; i++) {
    uint64_t a = rng() % P, b = rng() % P;
    check_mul(a, b);
    check_add(a, b);
    check_reduce(rng() & ((1ULL << 62) - 1));
    n += 3;
  }
  printf("phase 4 (random): %ld checks, fails so far %ld\n", n, fails);

  if (fails) {
    printf("m31_field_kat: FAIL (%ld/%ld)\n", fails, n);
    return 1;
  }
  printf("m31_field_kat: PASS (%ld checks, mul+add+reduce byte-exact vs direct %%p reference)\n", n);

  /* Light cyc/op timer on the multiply (dependency chain through out). */
  {
    uint64_t a = 1234567891ULL % P, b = 987654321ULL, out = 0;
    const long iters = 10000000;
    uint64_t t0 = rdtsc_begin();
    for (long i = 0; i < iters; i++) {
      m31_mul_owned(&out, &a, &b);
      a = out | 1; /* feed back, stay nonzero */
    }
    uint64_t t1 = rdtsc_end();
    printf("m31_mul_owned: %.2f cyc/op (%ld iters, chained)\n",
           (double)(t1 - t0) / (double)iters, iters);
    uint64_t ra = 1234567891ULL % P;
    volatile uint64_t sink;
    t0 = rdtsc_begin();
    for (long i = 0; i < iters; i++) {
      ra = m31_mul_ref(ra, b) | 1;
    }
    t1 = rdtsc_end();
    sink = ra; (void)sink;
    printf("m31_mul_ref (%% via __int128): %.2f cyc/op (%ld iters, chained)\n",
           (double)(t1 - t0) / (double)iters, iters);
  }
  return 0;
}
