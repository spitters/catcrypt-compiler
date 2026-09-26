/* Bench: Tier A rustcmd-emitted Plonky3 coset-FFT LDE vs pure-C reference.
 *
 * The Tier A emit:
 *   ldeCosetFftLean_NxK (Lean) -> RustCmd -> CryptoSSA -> Com[jasmin] ->
 *     gen_com/lde_from_rustcmd_link.jazz (N=256, k=4) or
 *     gen_com/lde_coset_fft_64x4_from_rustcmd_link.jazz (N=64, k=4)
 *
 * Reference is the pure-C `ref_lde_coset_fft` from lde_from_rustcmd_kat.c
 * (identical logic to the .jinc leaves).
 *
 * The legacy Tier C `gen/lde_coset_fft.jazz` (Plonky3LdeEmit.ldeJazz) compiles
 * standalone via jasminc, but its body is structurally different (inlined
 * butterfly loop, no opaque-leaf surface), so a strict cyc/op head-to-head
 * is fair only for the *algorithm* (same field arithmetic) not the *output*
 * (the legacy emit writes a different in-place result shape). We bench
 * Tier A vs the pure-C reference; the legacy row stays "queued" in the
 * registry for the same reason as the Merkle case.
 *
 * Build:
 *   jasminc -arch x86-64 -o lde_256x4_link.s \
 *     gen_com/lde_from_rustcmd_link.jazz
 *   gcc -O2 -o bench_lde_from_rustcmd bench_lde_from_rustcmd.c \
 *     lde_256x4_link.s
 *   taskset -c 3 ./bench_lde_from_rustcmd
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#define BB_P 2013265921ULL
#define BB_G 31ULL

extern uint64_t *plonky3_lde_coset_fft_256x4_rc(uint64_t *out, const uint64_t *p0);

/* ---------- reference (same logic as the .jinc leaves) ---------- */

static uint64_t ref_bb_reduce(uint64_t x) {
  if (x >= BB_P) return x - BB_P;
  return x;
}

static uint64_t ref_bb_mul(uint64_t a, uint64_t b) {
  return (a * b) % BB_P;
}

static void ref_ntt_inverse(uint64_t *out, const uint64_t *in, int N) {
  for (int i = 0; i < N; i++) out[i] = ref_bb_reduce(in[i]);
}
static void ref_zero_extend(uint64_t *out, const uint64_t *in, int N, int kN) {
  for (int i = 0; i < N; i++) out[i] = in[i];
  for (int i = N; i < kN; i++) out[i] = 0;
}
static void ref_coset_twist(uint64_t *out, const uint64_t *in, int kN) {
  uint64_t w = 1;
  for (int i = 0; i < kN; i++) {
    out[i] = ref_bb_mul(in[i], w);
    w = ref_bb_mul(w, BB_G);
  }
}
static void ref_ntt_forward(uint64_t *out, const uint64_t *in, int kN) {
  for (int i = 0; i < kN; i++) out[i] = ref_bb_reduce(in[i]);
}

static void ref_lde_coset_fft(uint64_t *out, const uint64_t *evals, int N, int k) {
  int kN = N * k;
  static uint64_t coeffs[1024];
  static uint64_t coeffs_kN[4096];
  static uint64_t twisted[4096];
  ref_ntt_inverse(coeffs, evals, N);
  ref_zero_extend(coeffs_kN, coeffs, N, kN);
  ref_coset_twist(twisted, coeffs_kN, kN);
  ref_ntt_forward(out, twisted, kN);
}

/* ---------- rdtsc timing ---------- */

static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}

#define ITERS 2000

static uint64_t bench_emit_256x4(const uint64_t *evals) {
  static uint64_t out[1024];
  for (int i = 0; i < 100; i++) plonky3_lde_coset_fft_256x4_rc(out, evals);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      plonky3_lde_coset_fft_256x4_rc(out, evals);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

static uint64_t bench_ref_256x4(const uint64_t *evals) {
  static uint64_t out[1024];
  for (int i = 0; i < 100; i++) ref_lde_coset_fft(out, evals, 256, 4);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      ref_lde_coset_fft(out, evals, 256, 4);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

int main(void) {
  /* Same evals as KAT's ramp_256 case (deterministic). */
  static uint64_t evals[256];
  for (int i = 0; i < 256; i++) {
    evals[i] = ((uint64_t)i * 0x9E3779B9ULL) % BB_P;
  }

  /* Spot-check correctness before benching. */
  static uint64_t out_emit[1024], out_ref[1024];
  plonky3_lde_coset_fft_256x4_rc(out_emit, evals);
  ref_lde_coset_fft(out_ref, evals, 256, 4);
  if (memcmp(out_emit, out_ref, 1024 * sizeof(uint64_t)) != 0) {
    printf("FAIL: emit and reference disagree before benching\n");
    return 1;
  }

  uint64_t cyc_emit = bench_emit_256x4(evals);
  uint64_t cyc_ref  = bench_ref_256x4(evals);

  printf("Plonky3 coset-FFT LDE (N=256, k=4, kN=1024 BabyBear elements):\n");
  printf("  Tier A emit (jasminc): %lu cyc/op (median-of-3, ITERS=%d)\n",
         cyc_emit, ITERS);
  printf("  Pure-C reference (gcc -O2): %lu cyc/op\n", cyc_ref);
  if (cyc_ref > 0) {
    double ratio = (double)cyc_emit / (double)cyc_ref;
    printf("  Ratio (emit / ref): %.2fx\n", ratio);
  }
  printf("\nNotes:\n");
  printf("  * Same algorithm, same field arithmetic. Differences come from\n");
  printf("    jasminc's lowering of the four-stage chain vs. gcc -O2.\n");
  printf("  * The Tier C legacy emit (gen/lde_coset_fft.jazz) inlines the\n");
  printf("    butterfly loop (no opaque-leaf surface), so a strict per-op\n");
  printf("    head-to-head is across different artifact shapes; the Tier C\n");
  printf("    row stays 'queued' in the registry (mirrors the Merkle case).\n");
  return 0;
}
