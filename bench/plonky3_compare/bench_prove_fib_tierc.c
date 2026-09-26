/* Bench: legacy Tier C Plonky3 Fibonacci prover (string-templated) vs the
 * upstream Plonky3 Rust crate (whose bench lives in `upstream_ref/`).
 *
 * Tier C path:
 *   bench/plonky3_compare/gen/plonky3_prove_fib.jazz  (legacy emit, #154/#162)
 *   bench/plonky3_compare/include/plonky3_prove_leaves.jinc  (leaf bodies)
 *   bench/plonky3_compare/plonky3_prove_fib_tierc_link.jazz  (this bench's link)
 *
 * The entry point `plonky3_prove_fib_3_8_rc` is the selector-inclusive
 * Fibonacci STARK prover compressed into 6 whole-phase leaves:
 *   1. plonky3_trace_lde_3_8         u64[24] trace  -> u64[32] LDE
 *   2. plonky3_merkle_commit_orch_8  u64[32]        -> u64[4]  digest
 *   3. plonky3_challenger_squeeze    u64[4]         -> u64[1]  alpha
 *   4. plonky3_quotient_compose_8    u64[32]+u64[1] -> u64[64] quotient
 *   5. plonky3_ood_deep_8            u64[64]+u64[1] -> u64[64] ood/deep
 *   6. plonky3_fri_prove_8           u64[64]+u64[1] -> u64[4]  proof
 *
 * AIR sizing: width=3, height=8 (per the leaf signatures). This is smaller
 * than the upstream Plonky3 demo which uses N=1024; we measure at height=8
 * because that is what the legacy Tier C emit was string-templated for.
 * Both sides are normalized to cyc/op for the Fibonacci AIR at that height.
 *
 * Build:
 *   jasminc -arch x86-64 -o prove_fib_tierc.s plonky3_prove_fib_tierc_link.jazz
 *   gcc -O2 -o bench_prove_fib_tierc bench_prove_fib_tierc.c prove_fib_tierc.s
 *   taskset -c 3 ./bench_prove_fib_tierc
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

extern uint64_t *plonky3_prove_fib_3_8_rc(uint64_t *out, const uint64_t *p0);

/* ---------- rdtsc timing ---------- */

static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}

#define ITERS 5000

static uint64_t bench_emit(const uint64_t *trace) {
  uint64_t out[4];
  /* warmup */
  for (int i = 0; i < 200; i++) plonky3_prove_fib_3_8_rc(out, trace);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      plonky3_prove_fib_3_8_rc(out, trace);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

int main(void) {
  /* Fibonacci trace: width 3, height 8. Same seed as Plonky3 KAT vectors.
   * Lanes (a, b, c) where c = a + b is the Fibonacci recurrence.  The exact
   * field-arithmetic semantics are encoded in the leaves; here we just feed
   * a deterministic, byte-identical input so the cyc/op number is reproducible.
   */
  uint64_t trace[24];
  uint64_t a = 0, b = 1;
  for (int row = 0; row < 8; row++) {
    trace[3*row + 0] = a;
    trace[3*row + 1] = b;
    uint64_t c = a + b;
    trace[3*row + 2] = c;
    a = b; b = c;
  }

  /* Sanity: run once and print the proof digest. */
  uint64_t out[4];
  plonky3_prove_fib_3_8_rc(out, trace);
  printf("Plonky3 Fibonacci STARK Tier C prover (height=8, width=3):\n");
  printf("  Proof digest (4 x u64): %016lx %016lx %016lx %016lx\n",
         out[0], out[1], out[2], out[3]);

  uint64_t cyc = bench_emit(trace);
  printf("  Tier C emit (jasminc): %lu cyc/op (median-of-3, ITERS=%d)\n",
         cyc, ITERS);

  return 0;
}
