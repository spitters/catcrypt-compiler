/* KAT + microbench for the BabyBear NTT butterfly emitted by the IN-LEAN x86
 * backend (no jasminc in the chain).
 *
 * The leaf `plonky3_ntt_butterfly_x86(out, inp)` is the AT&T `.s` printed by
 * CatCrypt.Crypto.SecureCompilation.X86Backend.BarrettButterflyKernel.butterflyAsm
 * (AsmPrinter over a Com (x86Dialect 64) -> runBlock-verified body), assembled
 * by gas. The verified artifact is the straight-line body's runBlock/evalInstr
 * transform (Jasmin-Rocq-model port); the push/pop ABI glue is trusted.
 *
 * Same reg-ptr ABI as plonky3_ntt_butterfly_rc: out is a u64[2] result buffer,
 * inp is a u64[9] = [a,b,w,MU,p,0,30,32,63] input buffer.
 *
 * Build (see Makefile target plonky3-ntt-butterfly-x86-lean-kat):
 *   <emit the .s from Lean>
 *   gcc -O2 -o ntt_butterfly_x86_from_lean_kat \
 *       ntt_butterfly_x86_from_lean_kat.c gen_com/ntt_butterfly_x86_from_lean.s
 *   ./ntt_butterfly_x86_from_lean_kat
 */
#include <stdint.h>
#include <stdio.h>

#define P 2013265921ULL   /* BabyBear prime 2^31 - 2^27 + 1 */

extern uint64_t *plonky3_ntt_butterfly_x86(uint64_t *out, const uint64_t *inp);

/* Spec field ops (canonical residues in [0,p)). */
static uint64_t bbmul(uint64_t a, uint64_t b) { return (a * b) % P; }
static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t bbsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }

static void fill_inp(uint64_t inp[9], uint64_t a, uint64_t b, uint64_t w) {
  inp[0] = a; inp[1] = b; inp[2] = w;
  inp[3] = 2290649223ULL;            /* MU = floor(2^62 / p) */
  inp[4] = P; inp[5] = 0; inp[6] = 30; inp[7] = 32; inp[8] = 63;
}

static int run_case(const char *name, uint64_t a, uint64_t b, uint64_t w) {
  uint64_t out_emit[2] = {0};
  uint64_t inp[9];
  fill_inp(inp, a, b, w);

  uint64_t wb = bbmul(w, b);
  uint64_t r0 = bbadd(a, wb);  /* a + w*b */
  uint64_t r1 = bbsub(a, wb);  /* a - w*b */

  plonky3_ntt_butterfly_x86(out_emit, inp);

  int ok = (out_emit[0] == r0 && out_emit[1] == r1);
  printf("  [%s] %-10s  o_emit=(%lu, %lu)  o_ref=(%lu, %lu)\n",
         ok ? "PASS" : "FAIL", name, out_emit[0], out_emit[1], r0, r1);
  return ok ? 0 : 1;
}

static inline uint64_t rdtsc(void) {
  unsigned lo, hi;
  __asm__ __volatile__("lfence\n\trdtsc" : "=a"(lo), "=d"(hi));
  return ((uint64_t)hi << 32) | lo;
}

int main(void) {
  int fails = 0;

  fails += run_case("zeros", 0, 0, 0);
  fails += run_case("ones", 1, 1, 1);
  fails += run_case("max", P - 1, P - 1, P - 1);
  fails += run_case("mixed", 123456789, 987654321, 31);
  fails += run_case("gen", 7, P - 2, 1000000007 % P);

  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int c = 0; c < 64; c++) {
    st ^= st << 13; st ^= st >> 7; st ^= st << 17; uint64_t a = st % P;
    st ^= st << 13; st ^= st >> 7; st ^= st << 17; uint64_t b = st % P;
    st ^= st << 13; st ^= st >> 7; st ^= st << 17; uint64_t w = st % P;
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", c);
    fails += run_case(nm, a, b, w);
  }

  if (fails != 0) {
    printf("\nFAILED: %d case(s) mismatched spec ldeButterfly.\n", fails);
    return 1;
  }
  printf("\nAll KAT cases PASS — IN-LEAN-x86-emitted butterfly == spec ldeButterfly.\n");

  /* Microbench: cycles/op over a long run, accumulating to defeat DCE. */
  uint64_t inp[9];
  fill_inp(inp, 123456789, 987654321, 31);
  uint64_t out[2] = {0};
  const long ITERS = 50000000;

  /* warmup */
  for (long i = 0; i < 1000000; i++) { plonky3_ntt_butterfly_x86(out, inp); }

  uint64_t t0 = rdtsc();
  uint64_t acc = 0;
  for (long i = 0; i < ITERS; i++) {
    plonky3_ntt_butterfly_x86(out, inp);
    acc += out[0] ^ out[1];
    inp[0] = (inp[0] + 1) % P;   /* vary input so the call can't be hoisted */
  }
  uint64_t t1 = rdtsc();
  double cyc = (double)(t1 - t0) / (double)ITERS;
  printf("bench: %.2f cyc/butterfly over %ld iters (acc=%lu)\n", cyc, ITERS, acc);
  return 0;
}
