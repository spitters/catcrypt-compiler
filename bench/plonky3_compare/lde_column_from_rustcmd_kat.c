/* KAT harness for the rustcmd-EMITTED Plonky3 coset-NTT column LDE.
 *
 * `computeColumnLde colEvals 3 5 31` (Plonky3ProveEmit) is emitted as a SEQUENCE
 * of 7 register-arith leaves through the verified front's EMIT-computation path
 * (JasminAbiEmit.emitAbiOrchReg):
 *
 *   lde_intt8_rc        : 8-pt inverse NTT (3 CT layers, omega_H^-1) + scale 8^-1
 *   lde_twist_rc        : zero-pad to 32 + coset-twist (coeff i *= 31^i)
 *                         fused with the 32-pt forward-NTT bit-reversal
 *   lde_ntt32_l0..l4_rc : the 5 forward-NTT Cooley-Tukey layers (omega_K)
 *
 * Each leaf's body is built entirely from regArith mul/shr/sub/and/add bindings
 * (the Barrett field mul-mod, no hardware `%`); leaf.denote = the Barrett word
 * arithmetic by construction (allRegArith proven in Lean, compositionally).
 * The leaves compose by 32-word buffer pass-through: no C-side permutation, since
 * the intt bit-reversal is folded into lde_intt8_rc's copy-in and the forward-NTT
 * bit-reversal is fused into lde_twist_rc's twist-swap.
 *
 * We compare the composed result against a self-contained C reference of the EXACT
 * Lean spec computeColumnLde over fixed + pseudo-random columns.
 *
 * Build (see Makefile target plonky3-lde-column-rustcmd-kat):
 *   jasminc -arch x86-64 -nowarning -o lde_column_from_rustcmd.s \
 *     gen_com/lde_column_from_rustcmd.jazz
 *   gcc -O2 -o lde_column_from_rustcmd_kat lde_column_from_rustcmd_kat.c \
 *     lde_column_from_rustcmd.s
 *   ./lde_column_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define P 2013265921ULL   /* BabyBear prime */
#define GEN 31ULL         /* BabyBear GENERATOR */
#define NIN 139

extern uint64_t *lde_intt8_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_twist_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l0_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l1_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l2_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l3_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l4_rc(uint64_t *out, const uint64_t *inp);

/* ---- BabyBear field reference (mirrors Plonky3LdeEmit / Plonky3ProveEmit) ---- */
static uint64_t bbmul(uint64_t a, uint64_t b) { return (a * b) % P; }
static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t bbsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }
static uint64_t bbpow(uint64_t base, uint64_t e) {
  uint64_t r = 1, cur = base;
  for (int i = 0; i < 64; i++) { if (e & 1) r = bbmul(r, cur); cur = bbmul(cur, cur); e >>= 1; }
  return r;
}
static uint64_t rou(int k) { return bbpow(GEN, (P - 1) >> k); }
static uint64_t bbinv(uint64_t a) { return a == 0 ? 0 : bbpow(a, P - 2); }

static int bitrev(int i, int logn) { int r = 0; for (int b = 0; b < logn; b++) { r = r*2 + i%2; i /= 2; } return r; }

/* ntt over a length-n array (n = 2^logn), root omega; matches bbNtt. */
static void bbntt(uint64_t *v, int n, int logn, uint64_t omega) {
  uint64_t tmp[32];
  for (int i = 0; i < n; i++) tmp[i] = v[bitrev(i, logn)];
  for (int i = 0; i < n; i++) v[i] = tmp[i];
  for (int layer = 0; layer < logn; layer++) {
    int size = 1 << (layer + 1), half = size / 2;
    uint64_t wSize = bbpow(omega, n / size);
    for (int idx = 0; idx < n; idx++) {
      int block = (idx / size) * size, off = idx % size;
      uint64_t out;
      if (off < half) {
        int j = off; uint64_t wPow = bbpow(wSize, j);
        out = bbadd(tmp[block + j], bbmul(wPow, tmp[block + j + half]));
      } else {
        int j = off - half; uint64_t wPow = bbpow(wSize, j);
        out = bbsub(tmp[block + j], bbmul(wPow, tmp[block + j + half]));
      }
      v[idx] = out;
    }
    for (int i = 0; i < n; i++) tmp[i] = v[i];
  }
}

/* intt over length-n: forward ntt with omega^-1, scaled by n^-1; matches bbIntt. */
static void bbintt(uint64_t *v, int n, int logn, uint64_t omega) {
  bbntt(v, n, logn, bbinv(omega));
  uint64_t ninv = bbinv((uint64_t)n);
  for (int i = 0; i < n; i++) v[i] = bbmul(v[i], ninv);
}

/* computeColumnLde colEvals 3 5 31 -> 32 evaluations. */
static void compute_column_lde(uint64_t out[32], const uint64_t col[8]) {
  uint64_t omegaH = rou(3), omegaN = rou(5), shift = GEN;
  uint64_t coeffs[32] = {0};
  for (int i = 0; i < 8; i++) coeffs[i] = col[i];
  bbintt(coeffs, 8, 3, omegaH);           /* intt over H (uses coeffs[0..7]) */
  /* coeffs[8..31] already 0 (zero-pad) */
  for (int i = 0; i < 32; i++) coeffs[i] = bbmul(coeffs[i], bbpow(shift, i)); /* coset twist */
  bbntt(coeffs, 32, 5, omegaN);            /* forward ntt over K */
  for (int i = 0; i < 32; i++) out[i] = coeffs[i];
}

/* ---- per-leaf input-vector construction (mirrors the Lean input-name maps) ---- */
/* intt-8 leaf: words 0..7 = col values; 8..19 = 12 intt twiddles (body order);
   132 = 8^-1; MU/p/shifts immediate (not read from inp). */
static void fill_intt_inp(uint64_t inp[NIN], const uint64_t col[8]) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  /* 8-pt bit-reversal of the column, done in the input vector: v[i] = col[br(i)] */
  for (int i = 0; i < 8; i++) inp[i] = col[bitrev(i, 3)];
  uint64_t oH = bbinv(rou(3)); /* omega_H^-1, the intt's forward root */
  /* body-order twiddles: layer0 (size2,half1) j=0 x4; layer1 (size4,half2) per
     block (0,2)/(1,3) and (4,6)/(5,7); layer2 (size8,half4) j=0..3. */
  int t = 8;
  /* layer 0: wSize = oH^(8/2)=oH^4; four butterflies all j=0 -> wSize^0 = 1 */
  for (int b = 0; b < 4; b++) inp[t++] = bbpow(bbpow(oH, 4), 0);
  /* layer 1: wSize = oH^(8/4)=oH^2; blocks (0..3),(4..7), butterflies j=0,1 each */
  { uint64_t wS = bbpow(oH, 2);
    inp[t++] = bbpow(wS, 0); inp[t++] = bbpow(wS, 1);   /* block 0: (0,2)j0,(1,3)j1 */
    inp[t++] = bbpow(wS, 0); inp[t++] = bbpow(wS, 1); } /* block 4: (4,6)j0,(5,7)j1 */
  /* layer 2: wSize = oH^(8/8)=oH; one block, j=0..3 */
  { uint64_t wS = bbpow(oH, 1);
    for (int j = 0; j < 4; j++) inp[t++] = bbpow(wS, j); }
  inp[132] = bbinv(8);  /* intt scale 8^-1 */
}

/* twist leaf: words 0..31 = buffer; 100..131 = coset powers 31^0..31^31. */
static void fill_twist_inp(uint64_t inp[NIN], const uint64_t buf[32]) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  for (int i = 0; i < 32; i++) inp[i] = buf[i];
  for (int i = 0; i < 32; i++) inp[100 + i] = bbpow(GEN, i);
}

/* ntt layer leaf: words 0..31 = buffer; 100..115 = wSize^0..wSize^15. */
static void fill_ntt_inp(uint64_t inp[NIN], const uint64_t buf[32], int layer) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  for (int i = 0; i < 32; i++) inp[i] = buf[i];
  int size = 1 << (layer + 1);
  uint64_t wSize = bbpow(rou(5), 32 / size);
  for (int j = 0; j < 16; j++) inp[100 + j] = bbpow(wSize, j);
}

/* compose the 7 emitted leaves on a shared 32-word buffer. */
static void emitted_column_lde(uint64_t out[32], const uint64_t col[8]) {
  uint64_t inp[NIN], buf[32];
  fill_intt_inp(inp, col);
  lde_intt8_rc(buf, inp);                 /* buf[0..7] = coeffs; buf[8..31] junk */
  fill_twist_inp(inp, buf);
  lde_twist_rc(buf, inp);                 /* zero-pad + twist + bitrev */
  uint64_t (*layers[5])(uint64_t*, const uint64_t*) = {0};
  fill_ntt_inp(inp, buf, 0); lde_ntt32_l0_rc(buf, inp);
  fill_ntt_inp(inp, buf, 1); lde_ntt32_l1_rc(buf, inp);
  fill_ntt_inp(inp, buf, 2); lde_ntt32_l2_rc(buf, inp);
  fill_ntt_inp(inp, buf, 3); lde_ntt32_l3_rc(buf, inp);
  fill_ntt_inp(inp, buf, 4); lde_ntt32_l4_rc(buf, inp);
  (void)layers;
  for (int i = 0; i < 32; i++) out[i] = buf[i];
}

static int run_case(const char *name, const uint64_t col[8]) {
  uint64_t out_emit[32], out_ref[32];
  emitted_column_lde(out_emit, col);
  compute_column_lde(out_ref, col);
  int ok = 1;
  for (int i = 0; i < 32; i++) if (out_emit[i] != out_ref[i]) ok = 0;
  printf("  [%s] %-10s", ok ? "PASS" : "FAIL", name);
  if (!ok) {
    printf("\n    emit:"); for (int i = 0; i < 32; i++) printf(" %lu", out_emit[i]);
    printf("\n    ref :"); for (int i = 0; i < 32; i++) printf(" %lu", out_ref[i]);
  }
  printf("\n");
  return ok ? 0 : 1;
}

int main(void) {
  int fails = 0;
  { uint64_t c[8] = {0,0,0,0,0,0,0,0}; fails += run_case("zeros", c); }
  { uint64_t c[8] = {1,2,3,4,5,6,7,8}; fails += run_case("seq", c); }
  { uint64_t c[8] = {1,1,1,1,1,1,1,1}; fails += run_case("ones", c); }
  { uint64_t c[8] = {P-1,P-2,P-3,P-4,1,2,3,4}; fails += run_case("hi", c); }

  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int t = 0; t < 64; t++) {
    uint64_t c[8];
    for (int i = 0; i < 8; i++) { st ^= st<<13; st ^= st>>7; st ^= st<<17; c[i] = st % P; }
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", t);
    fails += run_case(nm, c);
  }

  if (fails == 0) {
    printf("\nAll column-LDE KAT cases PASS -- composed EMITTED leaves == spec computeColumnLde(3,5,31).\n");
    return 0;
  } else {
    printf("\nFAILED: %d column-LDE case(s) did not match spec.\n", fails);
    return 1;
  }
}
