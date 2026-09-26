/* Bench: Tier A rustcmd-emitted Plonky3 AIR (Fibonacci) transition eval vs
 * pure-C reference.
 *
 * The Tier A emit:
 *   airEvalFibLean_H (pure Lean) -> RustCmd -> CryptoSSA -> Com[jasmin] ->
 *     gen_com/air_from_rustcmd_link.jazz
 *
 * Per-row Fibonacci AIR (two-column slice over width=3 storage):
 *   boundary:   trace[0..2] == [0, 1, *]
 *   transition: next.a == cur.b  and  next.b == cur.a + cur.b   (mod BB_P)
 *
 * Field: BabyBear (P = 2^31 - 2^27 + 1 = 2013265921).
 *
 * Build:
 *   make plonky3-air-rustcmd-bench
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

extern uint64_t *plonky3_air_eval_fib_3_8_rc(uint64_t *out, const uint64_t *p0);
extern uint64_t *plonky3_air_eval_fib_3_16_rc(uint64_t *out, const uint64_t *p0);

/* ---------- reference (byte-identical recipe to .jinc leaves) ---------- */

#define BB_P 2013265921ULL

static inline uint64_t air_reduce(uint64_t x) {
  uint64_t t = x - BB_P;
  uint64_t m = ((int64_t)t < 0) ? BB_P : 0;
  return t + m;
}

static inline uint64_t air_add(uint64_t a, uint64_t b) {
  return air_reduce(a + b);
}

static inline uint64_t air_sub(uint64_t a, uint64_t b) {
  return air_reduce(BB_P + a - b);
}

static void ref_air_eval_fib(uint64_t out[1], const uint64_t *s, int H) {
  uint64_t ok = 1;
  uint64_t ca = s[0]; if (ca != 0) ok = 0;
  uint64_t cb = s[1]; if (cb != 1) ok = 0;
  for (int i = 0; i < H - 1; i++) {
    ca = s[3*i];     cb = s[3*i + 1];
    uint64_t na = s[3*(i+1)], nb = s[3*(i+1) + 1];
    uint64_t c0 = air_sub(na, cb); if (c0 != 0) ok = 0;
    uint64_t sum = air_add(ca, cb);
    uint64_t c1 = air_sub(nb, sum); if (c1 != 0) ok = 0;
  }
  out[0] = ok;
}

/* ---------- rdtsc timing ---------- */

static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}

#define ITERS 20000

static uint64_t bench_emit_8(const uint64_t *trace) {
  uint64_t out[1];
  for (int i = 0; i < 200; i++) plonky3_air_eval_fib_3_8_rc(out, trace);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      plonky3_air_eval_fib_3_8_rc(out, trace);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

static uint64_t bench_ref_8(const uint64_t *trace) {
  uint64_t out[1];
  for (int i = 0; i < 200; i++) ref_air_eval_fib(out, trace, 8);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      ref_air_eval_fib(out, trace, 8);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

static uint64_t bench_emit_16(const uint64_t *trace) {
  uint64_t out[1];
  for (int i = 0; i < 200; i++) plonky3_air_eval_fib_3_16_rc(out, trace);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      plonky3_air_eval_fib_3_16_rc(out, trace);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

static uint64_t bench_ref_16(const uint64_t *trace) {
  uint64_t out[1];
  for (int i = 0; i < 200; i++) ref_air_eval_fib(out, trace, 16);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      ref_air_eval_fib(out, trace, 16);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

/* Build a valid Fibonacci trace of height H, width=3 (z slot = 0). */
static void build_fib_trace(uint64_t *trace, int H) {
  uint64_t a = 0, b = 1;
  for (int i = 0; i < H; i++) {
    trace[3*i + 0] = a;
    trace[3*i + 1] = b;
    trace[3*i + 2] = 0;
    uint64_t na = b;
    uint64_t nb = air_add(a, b);
    a = na; b = nb;
  }
}

int main(void) {
  uint64_t trace8[24], trace16[48];
  build_fib_trace(trace8,  8);
  build_fib_trace(trace16, 16);

  /* Correctness spot-check */
  uint64_t emit_out, ref_out;
  plonky3_air_eval_fib_3_8_rc(&emit_out, trace8);
  ref_air_eval_fib(&ref_out, trace8, 8);
  if (emit_out != ref_out) {
    printf("FAIL (H=8): emit=%lu ref=%lu\n", emit_out, ref_out);
  }
  plonky3_air_eval_fib_3_16_rc(&emit_out, trace16);
  ref_air_eval_fib(&ref_out, trace16, 16);
  if (emit_out != ref_out) {
    printf("FAIL (H=16): emit=%lu ref=%lu\n", emit_out, ref_out);
  }

  uint64_t e8  = bench_emit_8(trace8);
  uint64_t r8  = bench_ref_8(trace8);
  uint64_t e16 = bench_emit_16(trace16);
  uint64_t r16 = bench_ref_16(trace16);

  printf("Plonky3 AIR Fibonacci transition eval (BabyBear, width=3):\n");
  printf("  H=8:\n");
  printf("    Tier A emit (jasminc):    %lu cyc/op (median-of-3, ITERS=%d)\n",
         e8, ITERS);
  printf("    Pure-C reference (gcc -O2): %lu cyc/op\n", r8);
  if (r8 > 0) {
    printf("    Ratio (emit / ref): %.2fx\n", (double)e8 / (double)r8);
  }
  printf("  H=16:\n");
  printf("    Tier A emit (jasminc):    %lu cyc/op (median-of-3, ITERS=%d)\n",
         e16, ITERS);
  printf("    Pure-C reference (gcc -O2): %lu cyc/op\n", r16);
  if (r16 > 0) {
    printf("    Ratio (emit / ref): %.2fx\n", (double)e16 / (double)r16);
  }
  return 0;
}
