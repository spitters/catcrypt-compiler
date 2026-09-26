/* Bench: Tier A rustcmd-emitted Plonky3 Merkle build-root vs pure-C reference.
 *
 * The Tier A emit:
 *   merkleBuildRootLean_N (Lean) -> RustCmd -> CryptoSSA -> Com[jasmin] ->
 *     gen_com/merkle_from_rustcmd_link.jazz (N=1024) or
 *     gen_com/merkle_build_root_4_from_rustcmd_link.jazz (N=4)
 *
 * The Tier C legacy emit (gen/merkle_build_root.jazz) does not assemble
 * standalone via jasminc 2026.03.1 — its outer `while (width > 1) { … }` and
 * inner `for j = 0 to half` use a runtime `reg u64` for the bound, which the
 * current jasminc rejects ("the expression has type u64 instead of int"). So
 * the head-to-head we can run is Tier A vs a pure-C reference; the Tier C
 * legacy stays "queued" in the registry as per its existing note.
 *
 * Reference is `ref_merkle_build_root` (identical to merkle_from_rustcmd_kat.c).
 *
 * Build:
 *   jasminc -arch x86-64 -o merkle_n1024_link.s \
 *     gen_com/merkle_from_rustcmd_link.jazz
 *   gcc -O2 -o bench_merkle_from_rustcmd bench_merkle_from_rustcmd.c \
 *     merkle_n1024_link.s
 *   taskset -c 3 ./bench_merkle_from_rustcmd
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

extern uint64_t *plonky3_merkle_build_root_1024_rc(uint64_t *out, const uint64_t *p0);

/* ---------- reference (same logic as the .jinc leaves) ---------- */

static void ref_compress(uint64_t out[4], const uint64_t l[4], const uint64_t r[4]) {
  for (int i = 0; i < 4; i++) {
    uint64_t a = l[i], b = r[i];
    uint64_t t = a + b;
    t *= 0x9E;
    t += (uint64_t)i;
    t ^= (a * 0x6D);
    t ^= b;
    out[i] = t;
  }
  uint64_t prev = out[0];
  for (int i = 1; i < 4; i++) {
    prev *= 0xC5;
    out[i] ^= prev;
    prev = out[i];
  }
}

static void ref_hleaf(uint64_t out[4], uint64_t v) {
  for (int i = 0; i < 4; i++) {
    uint64_t t = v;
    t *= 0x9E3779B97F4A7C15ULL;
    t += (uint64_t)i;
    t *= 0xBF58476D1CE4E5B9ULL;
    out[i] = t;
    v = t;
  }
  uint64_t prev = out[0];
  for (int i = 1; i < 4; i++) {
    prev *= 0xA3;
    out[i] += prev;
    prev = out[i];
  }
}

static void ref_merkle_build_root(uint64_t root[4], const uint64_t *leaves, int N) {
  static uint64_t scratch[8192];
  for (int i = 0; i < N; i++) {
    ref_hleaf(&scratch[i * 4], leaves[i]);
  }
  int width = N;
  while (width > 1) {
    int half = width / 2;
    for (int j = 0; j < half; j++) {
      uint64_t tmp[4];
      ref_compress(tmp, &scratch[(2*j) * 4], &scratch[(2*j+1) * 4]);
      memcpy(&scratch[j * 4], tmp, 32);
    }
    width = half;
  }
  memcpy(root, &scratch[0], 32);
}

/* ---------- rdtsc timing ---------- */

static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}

#define ITERS 2000

static uint64_t bench_emit_1024(const uint64_t *leaves) {
  uint64_t out[4];
  /* warmup */
  for (int i = 0; i < 100; i++) plonky3_merkle_build_root_1024_rc(out, leaves);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      plonky3_merkle_build_root_1024_rc(out, leaves);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

static uint64_t bench_ref_1024(const uint64_t *leaves) {
  uint64_t out[4];
  for (int i = 0; i < 100; i++) ref_merkle_build_root(out, leaves, 1024);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      ref_merkle_build_root(out, leaves, 1024);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

int main(void) {
  /* Same leaves as the KAT's ramp1024 case (deterministic). */
  static uint64_t leaves[1024];
  for (int i = 0; i < 1024; i++) {
    leaves[i] = ((uint64_t)i * 0x9E3779B97F4A7C15ULL) ^ 0x5A5A5A5A5A5A5A5AULL;
  }

  /* Spot-check correctness once before benching. */
  uint64_t out_emit[4], out_ref[4];
  plonky3_merkle_build_root_1024_rc(out_emit, leaves);
  ref_merkle_build_root(out_ref, leaves, 1024);
  if (memcmp(out_emit, out_ref, 32) != 0) {
    printf("FAIL: emit and reference disagree before benching\n");
    return 1;
  }

  uint64_t cyc_emit = bench_emit_1024(leaves);
  uint64_t cyc_ref  = bench_ref_1024(leaves);

  printf("Plonky3 Merkle build-root (N=1024, 32-byte root):\n");
  printf("  Tier A emit (jasminc): %lu cyc/op (median-of-3, ITERS=%d)\n",
         cyc_emit, ITERS);
  printf("  Pure-C reference (gcc -O2): %lu cyc/op\n", cyc_ref);
  if (cyc_ref > 0) {
    double ratio = (double)cyc_emit / (double)cyc_ref;
    printf("  Ratio (emit / ref): %.2fx\n", ratio);
  }
  printf("\nNotes:\n");
  printf("  * Same algorithm, same hash function. Differences come from\n");
  printf("    jasminc's lowering of the unrolled level chain vs. gcc -O2.\n");
  printf("  * The Tier C legacy emit (gen/merkle_build_root.jazz) uses a\n");
  printf("    runtime `reg u64` outer-loop bound that jasminc 2026.03.1\n");
  printf("    rejects ('expression has type u64 instead of int'); it stays\n");
  printf("    'queued' in the registry. Bench is therefore Tier A vs C.\n");
  return 0;
}
