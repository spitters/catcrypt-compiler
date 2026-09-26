/* KAT harness for the rustcmd-EMITTED Plonky3 Fibonacci-AIR transition evaluator.
 *
 * `fib_air_transition_rc` evaluates the two Fibonacci-AIR transition constraints
 * over one row pair (cur, next), emitted by the verified front's register-arith
 * path (bench/plonky3_compare/fib_trace_gen_emit.lean, transCom):
 *
 *   c0 = bbSub next.a cur.b                  (FIB_NEXT_A)
 *   c1 = bbSub next.b (bbAdd cur.a cur.b)    (FIB_NEXT_B)
 *
 * both 0 exactly when the row pair is AIR-consistent (Plonky3AirEmit.evalTransition,
 * kat_fib_trace_satisfies_air). The reference reproduces the SAME BabyBear field
 * arithmetic and compares c0,c1 over (a) every consecutive pair of fibTrace(10)
 * (expecting 0,0) and (b) arbitrary residue row pairs.
 *
 * Build:
 *   jasminc -arch x86-64 -o fib_air_transition.s gen_com/fib_air_transition.jazz
 *   gcc -O2 -o fib_air_transition_kat fib_air_transition_kat.c fib_air_transition.s
 *   ./fib_air_transition_kat
 */
#include <stdint.h>
#include <stdio.h>

#define P 2013265921ULL

extern uint64_t *fib_air_transition_rc(uint64_t *out, const uint64_t *inp);

static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t bbsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }

/* evalTransition: c0 = bbSub na cb ; c1 = bbSub nb (bbAdd ca cb). */
static void eval_trans_ref(uint64_t out[2], const uint64_t r[4]) {
  uint64_t ca = r[0], cb = r[1], na = r[2], nb = r[3];
  out[0] = bbsub(na, cb);
  out[1] = bbsub(nb, bbadd(ca, cb));
}

static int run_case(const char *name, const uint64_t r[4]) {
  uint64_t inp[7] = { r[0], r[1], r[2], r[3], P, 0, 63 };
  uint64_t out_emit[2] = {0}, out_ref[2];
  eval_trans_ref(out_ref, r);
  fib_air_transition_rc(out_emit, inp);
  int ok = (out_emit[0] == out_ref[0]) && (out_emit[1] == out_ref[1]);
  printf("  [%s] %-14s c0=%lu c1=%lu\n", ok ? "PASS" : "FAIL", name, out_emit[0], out_emit[1]);
  if (!ok) printf("    ref: c0=%lu c1=%lu\n", out_ref[0], out_ref[1]);
  return ok ? 0 : 1;
}

int main(void) {
  int fails = 0;

  /* (a) consecutive fibTrace(10) pairs: every constraint must be 0. */
  uint64_t a = 0, b = 1;
  uint64_t prev_a = 0, prev_b = 1;
  for (int i = 0; i < 9; i++) {
    uint64_t nb = bbadd(prev_a, prev_b);
    uint64_t na = prev_b;
    uint64_t r[4] = { prev_a, prev_b, na, nb };
    char nm[20]; snprintf(nm, sizeof nm, "trace_pair%d", i);
    int rc = run_case(nm, r);
    fails += rc;
    /* the constraints must be 0 on a valid pair */
    uint64_t ref[2]; eval_trans_ref(ref, r);
    if (ref[0] != 0 || ref[1] != 0) { printf("    (ref nonzero on valid pair!)\n"); fails++; }
    prev_a = na; prev_b = nb;
  }

  /* (b) arbitrary residue row pairs (constraints generally nonzero). */
  { uint64_t r[4] = {1,2,3,4};               fails += run_case("arb_seq", r); }
  { uint64_t r[4] = {P-1, P-2, 5, 7};        fails += run_case("arb_hi", r); }
  { uint64_t r[4] = {0, 0, 0, 0};            fails += run_case("zeros", r); }
  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int c = 0; c < 16; c++) {
    uint64_t r[4];
    for (int i = 0; i < 4; i++) { st ^= st<<13; st ^= st>>7; st ^= st<<17; r[i] = st % P; }
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", c);
    fails += run_case(nm, r);
  }

  if (fails == 0) {
    printf("\nAll AIR-transition KAT cases PASS — EMITTED leaf == evalTransition.\n");
    return 0;
  }
  printf("\nFAILED: %d AIR-transition case(s) mismatched.\n", fails);
  return 1;
}
