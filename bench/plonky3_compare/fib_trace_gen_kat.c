/* KAT harness for the rustcmd-EMITTED Plonky3 Fibonacci-AIR trace generator.
 *
 * `fib_trace_gen_rc` is the height-10 BabyBear `bbAdd` trace recurrence emitted
 * by the verified front's register-arith EMIT-computation path
 * (bench/plonky3_compare/fib_trace_gen_emit.lean):
 *
 *   traceCom (Com jasminDialect, all regArith add/sub/shr/and bindings)
 *     -> emitAbiOrchReg
 *     -> gen_com/fib_trace_gen.jazz
 *
 * Every line is a real jasmin reg u64 scalar assignment; the field add-mod is a
 * regArith conditional subtract (no hardware `%`). The recurrence is
 *   trace[0] = (0, 1);  trace[i] = (trace[i-1].b, bbAdd trace[i-1].a trace[i-1].b)
 * — exactly Plonky3AirEmit.fibTrace, whose column-1 KAT values
 * (kat_fibonacci_trace_values) are [1,1,2,3,5,8,13,21,34,55].
 *
 * The expected 20-word output is recomputed here by the SAME recurrence (the
 * GROUND TRUTH being fibTrace 10) and the full row buffer is byte-matched.
 *
 * Build:
 *   jasminc -arch x86-64 -o fib_trace_gen.s gen_com/fib_trace_gen.jazz
 *   gcc -O2 -o fib_trace_gen_kat fib_trace_gen_kat.c fib_trace_gen.s
 *   ./fib_trace_gen_kat
 */
#include <stdint.h>
#include <stdio.h>

#define P 2013265921ULL   /* BabyBear prime */

extern uint64_t *fib_trace_gen_rc(uint64_t *out, const uint64_t *inp);

static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }

/* Reference fibTrace(height): row 0 = (0,1); row i = (prev.b, bbAdd prev.a prev.b).
   Writes the 2*height-word buffer [a0,b0,a1,b1,...]. */
static void fib_trace_ref(uint64_t *out, int height) {
  uint64_t a = 0, b = 1;
  for (int i = 0; i < height; i++) {
    out[2 * i] = a;
    out[2 * i + 1] = b;
    uint64_t nb = bbadd(a, b);
    a = b;
    b = nb;
  }
}

int main(void) {
  uint64_t out_emit[20] = {0}, out_ref[20];
  /* inp = [a0, b0, P, 0, 63]; only a0,b0 are read into registers, the rest
     are immediates in the leaf body but present for ABI completeness. */
  uint64_t inp[5] = { 0, 1, P, 0, 63 };

  fib_trace_ref(out_ref, 10);
  fib_trace_gen_rc(out_emit, inp);

  int ok = 1;
  for (int i = 0; i < 20; i++) if (out_emit[i] != out_ref[i]) ok = 0;

  printf("  [%s] fib_trace_gen height=10\n", ok ? "PASS" : "FAIL");
  if (!ok) {
    printf("    emit:");
    for (int i = 0; i < 20; i++) printf(" %lu", out_emit[i]);
    printf("\n    ref :");
    for (int i = 0; i < 20; i++) printf(" %lu", out_ref[i]);
    printf("\n");
  }

  /* Also pin column 1 against the literal kat_fibonacci_trace_values. */
  static const uint64_t fib_col1[10] = {1,1,2,3,5,8,13,21,34,55};
  int kok = 1;
  for (int i = 0; i < 10; i++) if (out_emit[2 * i + 1] != fib_col1[i]) kok = 0;
  printf("  [%s] column-1 == kat_fibonacci_trace_values\n", kok ? "PASS" : "FAIL");

  if (ok && kok) {
    printf("\nAll fib_trace_gen KAT cases PASS — EMITTED leaf == fibTrace(10).\n");
    return 0;
  }
  printf("\nFAILED: emitted trace did not match fibTrace(10).\n");
  return 1;
}
