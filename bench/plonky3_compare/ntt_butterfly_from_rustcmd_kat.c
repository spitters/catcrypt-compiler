/* KAT harness for the rustcmd-EMITTED Plonky3 BabyBear NTT butterfly.
 *
 * `plonky3_ntt_butterfly_rc` is the radix-2 decimation-in-time butterfly *body*
 * emitted by the verified front's register-arith EMIT-computation path (NOT a
 * hand-written leaf):
 *
 *   butterflyCom (Com jasminDialect, all regArith mul/shr/sub/and/add bindings)
 *     -> emitAbiOrchReg (the ChaCha20 EMIT-computation path)
 *     -> gen_com/ntt_butterfly_from_rustcmd.jazz
 *
 * Every line of the emitted .jazz is a real jasmin `reg u64` scalar assignment.
 * The field multiply bbMul = (w*b) mod p is realised as a Barrett reduction in
 * regArith words (mul/shr/sub/and/add), NOT a hardware `%` or signed shift, so
 * it is the by-construction allRegArith emit (vs the hand-written string `fmul`
 * with `%= P` in Plonky3LdeEmit.ldeJazz).
 *
 * We compare against a self-contained C reference implementing the spec
 * `ldeButterfly`: (bbAdd a (bbMul w b), bbSub a (bbMul w b)) over BabyBear,
 * asserting equality of both output words over fixed + pseudo-random inputs.
 *
 * Build:
 *   jasminc -arch x86-64 -o ntt_butterfly_from_rustcmd.s \
 *     gen_com/ntt_butterfly_from_rustcmd.jazz
 *   gcc -O2 -o ntt_butterfly_from_rustcmd_kat ntt_butterfly_from_rustcmd_kat.c \
 *     ntt_butterfly_from_rustcmd.s
 *   ./ntt_butterfly_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>

#define P 2013265921ULL   /* BabyBear prime 2^31 - 2^27 + 1 */

extern uint64_t *plonky3_ntt_butterfly_rc(uint64_t *out, const uint64_t *inp);

/* Spec field ops (canonical residues in [0,p)). */
static uint64_t bbmul(uint64_t a, uint64_t b) { return (a * b) % P; }
static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t bbsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }

static int run_case(const char *name, uint64_t a, uint64_t b, uint64_t w) {
  uint64_t out_emit[2] = {0};
  uint64_t inp[9];
  inp[0] = a; inp[1] = b; inp[2] = w;
  inp[3] = 2290649223ULL; /* MU = floor(2^62 / p) */
  inp[4] = P; inp[5] = 0; inp[6] = 30; inp[7] = 32; inp[8] = 63;

  uint64_t wb = bbmul(w, b);
  uint64_t r0 = bbadd(a, wb);  /* a + w*b */
  uint64_t r1 = bbsub(a, wb);  /* a - w*b */

  plonky3_ntt_butterfly_rc(out_emit, inp);

  int ok = (out_emit[0] == r0 && out_emit[1] == r1);
  printf("  [%s] %-10s  o_emit=(%lu, %lu)  o_ref=(%lu, %lu)\n",
         ok ? "PASS" : "FAIL", name, out_emit[0], out_emit[1], r0, r1);
  return ok ? 0 : 1;
}

int main(void) {
  int fails = 0;

  fails += run_case("zeros", 0, 0, 0);
  fails += run_case("ones", 1, 1, 1);
  fails += run_case("max", P - 1, P - 1, P - 1);
  fails += run_case("mixed", 123456789, 987654321, 31);
  fails += run_case("gen", 7, P - 2, 1000000007 % P);

  /* Pseudo-random canonical-residue cases (xorshift64, deterministic). */
  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int c = 0; c < 64; c++) {
    st ^= st << 13; st ^= st >> 7; st ^= st << 17; uint64_t a = st % P;
    st ^= st << 13; st ^= st >> 7; st ^= st << 17; uint64_t b = st % P;
    st ^= st << 13; st ^= st >> 7; st ^= st << 17; uint64_t w = st % P;
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", c);
    fails += run_case(nm, a, b, w);
  }

  if (fails == 0) {
    printf("\nAll NTT-butterfly KAT cases PASS — EMITTED butterfly == spec ldeButterfly.\n");
    return 0;
  } else {
    printf("\nFAILED: %d NTT-butterfly case(s) did not match spec.\n", fails);
    return 1;
  }
}
