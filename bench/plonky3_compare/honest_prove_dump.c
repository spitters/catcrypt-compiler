/* Ground-truth oracle for honest_prove_ref.lean: link the jasminc-emitted
 * hp_prove (plonky3_honest_prove.s) and dump all 980 u64 proof lanes (decimal),
 * one per line, on the same Fibonacci KAT trace honest_prove_kat.c uses.
 * The Lean reference is byte-diffed against this output. */
#include <stdint.h>
#include <stdio.h>

#define PROOF_LANES 980

extern uint64_t *hp_prove(uint64_t *out, const uint64_t *p0);

int main(void) {
  uint64_t trace[24];
  uint64_t a = 0, b = 1;
  for (int row = 0; row < 8; row++) {
    trace[3*row + 0] = a;
    trace[3*row + 1] = b;
    uint64_t c = a + b;
    trace[3*row + 2] = c;
    a = b; b = c;
  }
  uint64_t proof[PROOF_LANES];
  hp_prove(proof, trace);
  for (int i = 0; i < PROOF_LANES; i++)
    printf("%llu\n", (unsigned long long)proof[i]);
  return 0;
}
