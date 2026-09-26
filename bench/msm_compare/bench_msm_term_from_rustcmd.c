/* Bench: rustcmd-emitted MSM-term orchestration (scalarFold one-term lane).
 *
 * The link.jazz (gen_com/msm_term_from_rustcmd_link.jazz) is the single-term
 * MSM lane:
 *
 *     t0 = ec_scalar_mul(t0, s0, s1);   // k * P, the per-term op
 *
 * Linked against the toy-EC shim leaf (include/msm_leaves.jinc, pass-through
 * by design — see the file header for the trust split). This bench therefore
 * measures the *orchestration overhead* of the verified-front emit on the
 * one-term lane (memcpy-in / leaf-call / memcpy-out), NOT the EC arithmetic.
 * This mirrors the precedent of `fndsa_512_{sign,keygen}_rustcmd` whose bench
 * also reports stub-leaf orchestration overhead. The production EC analogues
 * live in bench/{secp256k1,p256,bls12381,bn254}_compare/.
 *
 * Build/run (Makefile target `msm-rustcmd-bench`):
 *   jasminc -arch x86-64 -o msm_term_rustcmd_link.s \
 *     gen_com/msm_term_from_rustcmd_link.jazz
 *   gcc -O2 -o bench_msm_term_from_rustcmd bench_msm_term_from_rustcmd.c \
 *     msm_term_rustcmd_link.s
 *   taskset -c 3 ./bench_msm_term_from_rustcmd
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define ITERS 5000000

extern uint64_t *msm_term_rustcmd(
    uint64_t *out, const uint64_t *p0, const uint64_t *p1);

static inline uint64_t rdtsc(void) {
  uint32_t lo, hi;
  __asm__ __volatile__("lfence; rdtsc" : "=a"(lo), "=d"(hi));
  return ((uint64_t)hi << 32) | lo;
}

static double median3(double x, double y, double z) {
  if (x > y) { double t = x; x = y; y = t; }
  if (y > z) { double t = y; y = z; z = t; }
  if (x > y) { double t = x; x = y; y = t; }
  return y;
}

int main(void) {
  uint64_t k[1] = { 0x0000000000000007ull };
  uint64_t P[1] = { 0x0000000000000003ull };
  uint64_t out[1] = { 0 };

  /* Warm-up. */
  for (int i = 0; i < 100000; i++) {
    msm_term_rustcmd(out, k, P);
    k[0] ^= out[0];
  }

  double samples[3];
  for (int b = 0; b < 3; b++) {
    uint64_t t0 = rdtsc();
    for (int i = 0; i < ITERS; i++) {
      msm_term_rustcmd(out, k, P);
      k[0] ^= out[0];
    }
    uint64_t t1 = rdtsc();
    samples[b] = (double)(t1 - t0) / ITERS;
  }
  double cyc = median3(samples[0], samples[1], samples[2]);

  printf("MSM-term rustcmd orchestration (toy-EC shim leaf, scope = orchestration overhead)\n");
  printf("  ITERS = %d per batch, median of 3, taskset pin recommended\n", ITERS);
  printf("  %-58s %10.2f cyc/op\n",
         "msm_term_rustcmd (verified front, one-term lane)", cyc);
  printf("  (checksum %llu — keeps the optimizer honest)\n",
         (unsigned long long)(k[0] ^ out[0]));
  return 0;
}
