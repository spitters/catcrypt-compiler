/* KAT + microbench for the two-butterfly NTT *chain* emitted by the IN-LEAN
 * x86 backend (no jasminc), in two forms (#304, W4):
 *
 *   plonky3_ntt_bf2chain_abi(out, inp, scratch)
 *       — the two butterflies composed as SEPARATE LEAVES: butterfly 1's
 *         result word o0 is stored to scratch[0] (the leaf's copy-out) and
 *         reloaded as butterfly 2's a-argument (the next leaf's copy-in), and
 *         o1 round-trips through scratch[8]. The store+reload pair across the
 *         leaf boundary is the per-leaf ABI tax.
 *
 *   plonky3_ntt_bf2chain_inlined(out, inp)
 *       — the same two butterflies INLINED at the IR level with register
 *         allocation re-run: o0 stays register-resident and feeds butterfly 2
 *         directly; o1 stays in a register until the final store. The boundary
 *         store+reload is gone (and no scratch buffer is needed).
 *
 * Both .s are printed by
 *   CatCrypt.Crypto.SecureCompilation.X86Backend.InlinedNttKernel.{abiAsm,inlinedAsm}
 * (AsmPrinter over the runBlock-verified JInstr blocks; the inline+RA
 * denotation-preservation is `inlineThenRA_denote_preserves`). gas assembles
 * them. The verified artifact is each block's runBlock/evalInstr transform; the
 * push/pop ABI glue is trusted scaffolding.
 *
 * inp layout (u64): [a, b, w, b2, w2] at words [0,1,2,3,4]. (The Barrett
 * constants/shift-amounts are folded into the kernel as immediates.)
 *
 * Build (see Makefile target plonky3-ntt-bf2chain-kat):
 *   gcc -O2 -o ntt_bf2chain_kat ntt_bf2chain_kat.c \
 *       gen_com/ntt_bf2chain_abi.s gen_com/ntt_bf2chain_inlined.s
 *   taskset -c 2 ./ntt_bf2chain_kat
 */
#include <stdint.h>
#include <stdio.h>

#define P 2013265921ULL   /* BabyBear prime 2^31 - 2^27 + 1 */

extern void *plonky3_ntt_bf2chain_abi(uint64_t *out, const uint64_t *inp,
                                      uint64_t *scratch);
extern void *plonky3_ntt_bf2chain_inlined(uint64_t *out, const uint64_t *inp);

/* Spec field ops (canonical residues in [0,p)). */
static uint64_t bbmul(uint64_t a, uint64_t b) { return (a * b) % P; }
static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t bbsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }

/* The two-butterfly chain spec: o0=a+w*b, o1=a-w*b; then o0'=o0+w2*b2,
 * o1'=o0-w2*b2; observable outputs are (o0', o1', o1). */
static void spec(uint64_t a, uint64_t b, uint64_t w, uint64_t b2, uint64_t w2,
                 uint64_t ref[3]) {
  uint64_t wb = bbmul(w, b);
  uint64_t o0 = bbadd(a, wb), o1 = bbsub(a, wb);
  uint64_t wb2 = bbmul(w2, b2);
  ref[0] = bbadd(o0, wb2);   /* o0' */
  ref[1] = bbsub(o0, wb2);   /* o1' */
  ref[2] = o1;               /* carried through */
}

static int run_case(const char *name, uint64_t a, uint64_t b, uint64_t w,
                    uint64_t b2, uint64_t w2) {
  uint64_t inp[5] = {a, b, w, b2, w2};
  uint64_t ref[3];
  spec(a, b, w, b2, w2, ref);

  uint64_t out_abi[3] = {0}, scratch[2] = {0};
  plonky3_ntt_bf2chain_abi(out_abi, inp, scratch);

  uint64_t out_inl[3] = {0};
  plonky3_ntt_bf2chain_inlined(out_inl, inp);

  int ok = 1;
  for (int k = 0; k < 3; k++)
    if (out_abi[k] != ref[k] || out_inl[k] != ref[k]) ok = 0;

  printf("  [%s] %-10s  abi=(%lu,%lu,%lu) inl=(%lu,%lu,%lu) ref=(%lu,%lu,%lu)\n",
         ok ? "PASS" : "FAIL", name,
         out_abi[0], out_abi[1], out_abi[2],
         out_inl[0], out_inl[1], out_inl[2],
         ref[0], ref[1], ref[2]);
  return ok ? 0 : 1;
}

static inline uint64_t rdtsc(void) {
  unsigned lo, hi;
  __asm__ __volatile__("lfence\n\trdtsc" : "=a"(lo), "=d"(hi));
  return ((uint64_t)hi << 32) | lo;
}

int main(void) {
  int fails = 0;

  fails += run_case("zeros", 0, 0, 0, 0, 0);
  fails += run_case("ones", 1, 1, 1, 1, 1);
  fails += run_case("small", 7, 11, 13, 17, 19);
  fails += run_case("max", P - 1, P - 1, P - 1, P - 1, P - 1);
  fails += run_case("mixed", 123456789, 987654321, 31, 555, 777);

  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int c = 0; c < 64; c++) {
    uint64_t v[5];
    for (int k = 0; k < 5; k++) {
      st ^= st << 13; st ^= st >> 7; st ^= st << 17; v[k] = st % P;
    }
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", c);
    fails += run_case(nm, v[0], v[1], v[2], v[3], v[4]);
  }

  if (fails != 0) {
    printf("\nFAILED: %d case(s) mismatched. ABI and inlined forms must both "
           "equal the two-butterfly chain spec.\n", fails);
    return 1;
  }
  printf("\nAll KAT cases PASS — ABI-boundary == inlined == spec "
         "(in-Lean-x86-emitted, no jasminc).\n");

  /* Microbench: minimum cyc/op over many short trials (min filters scheduler
   * noise / contention from other processes — a standard microbench estimator).
   * The two forms are measured in interleaved trials so transient load hits
   * both equally. The input word is varied each iteration so neither call can
   * be hoisted out of the loop. */
  const long ITERS = 2000000;
  const int TRIALS = 200;
  uint64_t inp[5] = {123456789, 987654321, 31, 555, 777};
  uint64_t out[3] = {0}, scratch[2] = {0};

  /* warmup both */
  for (long i = 0; i < 2000000; i++) {
    plonky3_ntt_bf2chain_abi(out, inp, scratch);
    plonky3_ntt_bf2chain_inlined(out, inp);
  }

  uint64_t acc = 0;
  double best_abi = 1e30, best_inl = 1e30;

  for (int t = 0; t < TRIALS; t++) {
    inp[0] = 123456789;
    uint64_t a0 = rdtsc();
    for (long i = 0; i < ITERS; i++) {
      plonky3_ntt_bf2chain_abi(out, inp, scratch);
      acc += out[0] ^ out[1] ^ out[2];
      inp[0] = (inp[0] + 1) % P;
    }
    uint64_t a1 = rdtsc();
    double c_abi = (double)(a1 - a0) / (double)ITERS;
    if (c_abi < best_abi) best_abi = c_abi;

    inp[0] = 123456789;
    uint64_t b0 = rdtsc();
    for (long i = 0; i < ITERS; i++) {
      plonky3_ntt_bf2chain_inlined(out, inp);
      acc += out[0] ^ out[1] ^ out[2];
      inp[0] = (inp[0] + 1) % P;
    }
    uint64_t b1 = rdtsc();
    double c_inl = (double)(b1 - b0) / (double)ITERS;
    if (c_inl < best_inl) best_inl = c_inl;
  }

  printf("\nbench (min of %d trials x %ld iters, acc=%lu):\n", TRIALS, ITERS, acc);
  printf("  ABI-boundary (2 separate leaves): %.2f cyc/chain\n", best_abi);
  printf("  inlined-merged (1 fused body):    %.2f cyc/chain\n", best_inl);
  printf("  ABI tax closed by inline+RA:      %.2f cyc/chain (%.1f%%)\n",
         best_abi - best_inl, 100.0 * (best_abi - best_inl) / best_abi);
  return 0;
}
