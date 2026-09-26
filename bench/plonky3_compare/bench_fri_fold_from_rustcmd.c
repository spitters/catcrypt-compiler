/* cyc/op micro-benchmark for the rustcmd-EMITTED Plonky3 FRI fold + bbInv leaves
 * (CatCrypt/Crypto/SecureCompilation/VIR/Plonky3FriFoldEmit.lean). */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define P 2013265921ULL
#define NIN 16

extern uint64_t *fri_fold_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_inv_rc(uint64_t *out, const uint64_t *inp);

static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}

int main(void) {
  uint64_t inp[NIN], out[1];
  memset(inp, 0, sizeof inp);
  inp[0] = 100; inp[1] = 50; inp[2] = 7; inp[3] = 3;
  const int N = 200000;

  /* warm up */
  for (int i = 0; i < 1000; i++) fri_fold_rc(out, inp);
  uint64_t t0 = rdtscp();
  for (int i = 0; i < N; i++) { inp[2] = 7 + (i & 1023); fri_fold_rc(out, inp); }
  uint64_t t1 = rdtscp();
  double cf = (double)(t1 - t0) / N;

  for (int i = 0; i < 1000; i++) bb_inv_rc(out, inp);
  uint64_t b0 = rdtscp();
  for (int i = 0; i < N; i++) { inp[0] = 2 + (i & 1023); bb_inv_rc(out, inp); }
  uint64_t b1 = rdtscp();
  double cb = (double)(b1 - b0) / N;

  printf("fri_fold_rc : %.1f cyc/op  (one coset; includes inline bbInv 1/(2x))\n", cf);
  printf("bb_inv_rc   : %.1f cyc/op  (a^(p-2) Fermat, 60 Barrett bbMuls)\n", cb);
  printf("(sink out[0]=%lu)\n", out[0]);
  return 0;
}
