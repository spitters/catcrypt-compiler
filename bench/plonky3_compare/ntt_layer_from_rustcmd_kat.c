/* KAT harness for the rustcmd-EMITTED Plonky3 BabyBear NTT layer (n=8, last layer).
 *
 * `plonky3_ntt_layer8_rc` is one full radix-2 Cooley-Tukey NTT layer *body*
 * emitted by the verified front's register-arith EMIT-computation path:
 *
 *   layerCom (Com jasminDialect, all regArith mul/shr/sub/and/add bindings)
 *     -> emitAbiOrchReg (the ChaCha20 EMIT-computation path)
 *     -> gen_com/ntt_layer_from_rustcmd.jazz
 *
 * Every line is a real jasmin reg u64 scalar assignment; the field mul-mod is a
 * regArith Barrett reduction (no hardware `%`). Four independent butterflies on
 * pairs (i, i+4), i=0..3, with twiddles wSize^0..wSize^3 supplied as inputs.
 *
 * We compare against a self-contained C reference reproducing the EXACT Lean
 * spec `Plonky3ProveEmit.nttLayer vals omega 8 2`, asserting equality of all 8
 * output words over fixed + pseudo-random inputs.
 *
 * Build:
 *   jasminc -arch x86-64 -o ntt_layer_from_rustcmd.s \
 *     gen_com/ntt_layer_from_rustcmd.jazz
 *   gcc -O2 -o ntt_layer_from_rustcmd_kat ntt_layer_from_rustcmd_kat.c \
 *     ntt_layer_from_rustcmd.s
 *   ./ntt_layer_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>

#define P 2013265921ULL   /* BabyBear prime */
#define GEN 31ULL         /* BabyBear GENERATOR */

extern uint64_t *plonky3_ntt_layer8_rc(uint64_t *out, const uint64_t *inp);

static uint64_t bbmul(uint64_t a, uint64_t b) { return (a * b) % P; }
static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t bbsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }

/* bb_pow: square-and-multiply, 64-iteration loop (matches bbPow). */
static uint64_t bbpow(uint64_t base, uint64_t e) {
  uint64_t r = 1, cur = base;
  for (int i = 0; i < 64; i++) {
    if (e & 1) r = bbmul(r, cur);
    cur = bbmul(cur, cur);
    e >>= 1;
  }
  return r;
}

/* bb_root_of_unity k = bb_pow GENERATOR ((p-1) >> k). */
static uint64_t bb_root_of_unity(int k) { return bbpow(GEN, (P - 1) >> k); }

/* EXACT Plonky3ProveEmit.nttLayer vals omega n layer, here n=8 layer=2. */
static void ntt_layer(uint64_t out[8], const uint64_t vals[8], uint64_t omega,
                      int n, int layer) {
  int size = 1 << (layer + 1);
  int half = size / 2;
  uint64_t wSize = bbpow(omega, (uint64_t)(n / size));
  for (int idx = 0; idx < n; idx++) {
    int block = (idx / size) * size;
    int off = idx % size;
    if (off < half) {
      int j = off;
      uint64_t wPow = bbpow(wSize, (uint64_t)j);
      uint64_t lo = vals[block + j];
      uint64_t t = bbmul(wPow, vals[block + j + half]);
      out[idx] = bbadd(lo, t);
    } else {
      int j = off - half;
      uint64_t wPow = bbpow(wSize, (uint64_t)j);
      uint64_t lo = vals[block + j];
      uint64_t t = bbmul(wPow, vals[block + j + half]);
      out[idx] = bbsub(lo, t);
    }
  }
}

static int run_case(const char *name, const uint64_t v[8], uint64_t omega) {
  uint64_t out_emit[8] = {0}, out_ref[8];
  /* twiddles tj = wSize^j, wSize = omega^(8/8) = omega; j = 0..3. */
  uint64_t wSize = bbpow(omega, 8 / 8);
  uint64_t inp[18];
  for (int i = 0; i < 8; i++) inp[i] = v[i];
  for (int j = 0; j < 4; j++) inp[8 + j] = bbpow(wSize, (uint64_t)j);
  inp[12] = 2290649223ULL; inp[13] = P; inp[14] = 0;
  inp[15] = 30; inp[16] = 32; inp[17] = 63;

  ntt_layer(out_ref, v, omega, 8, 2);
  plonky3_ntt_layer8_rc(out_emit, inp);

  int ok = 1;
  for (int i = 0; i < 8; i++) if (out_emit[i] != out_ref[i]) ok = 0;
  printf("  [%s] %-10s", ok ? "PASS" : "FAIL", name);
  if (!ok) {
    printf("\n    emit:");
    for (int i = 0; i < 8; i++) printf(" %lu", out_emit[i]);
    printf("\n    ref :");
    for (int i = 0; i < 8; i++) printf(" %lu", out_ref[i]);
  }
  printf("\n");
  return ok ? 0 : 1;
}

int main(void) {
  int fails = 0;
  uint64_t omega = bb_root_of_unity(3);  /* order-8 root of unity */

  { uint64_t v[8] = {0,0,0,0,0,0,0,0}; fails += run_case("zeros", v, omega); }
  { uint64_t v[8] = {1,2,3,4,5,6,7,8}; fails += run_case("seq", v, omega); }
  { uint64_t v[8] = {P-1,P-2,P-3,P-4,1,2,3,4}; fails += run_case("hi", v, omega); }

  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int c = 0; c < 64; c++) {
    uint64_t v[8];
    for (int i = 0; i < 8; i++) { st ^= st<<13; st ^= st>>7; st ^= st<<17; v[i] = st % P; }
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", c);
    fails += run_case(nm, v, omega);
  }

  if (fails == 0) {
    printf("\nAll NTT-layer KAT cases PASS — EMITTED layer == spec nttLayer(8,2).\n");
    return 0;
  } else {
    printf("\nFAILED: %d NTT-layer case(s) did not match spec.\n", fails);
    return 1;
  }
}
