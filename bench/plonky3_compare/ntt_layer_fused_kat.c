/* KAT harness for the FUSED two-NTT-layer leaf (Gap 3: per-leaf marshalling tax).
 *
 * `plonky3_ntt_layer8x2_fused_rc` is TWO chained radix-2 NTT layers fused into a
 * single emitted `Com jasminDialect` body
 * (Plonky3NttLayerInlineEmit.fusedTwoLayerCom), rendered to one owned `.s`
 * (gen_com/ntt_layer_fused_owned.s) via the verified x86 backend (no jasminc).
 *
 * The fusion wires layer 1's eight outputs (live in r0..r7) straight into layer
 * 2's eight value slots — NO copy-out / copy-in buffer between the layers. The
 * denotation-preservation lemma `fusedTwoLayerCom_denote` proves (axioms:
 * propext, Quot.sound only) that the fused Com IS layer1-body then layer2-body.
 *
 * This harness checks the fused leaf is BYTE-IDENTICAL to the unfused chain:
 *   ref      = ntt_layer( ntt_layer(v) )            (C reference, applied twice)
 *   unfused  = plonky3_ntt_layer8_rc twice          (the separate-call chain)
 *   fused    = plonky3_ntt_layer8x2_fused_rc once    (the fused leaf)
 * and asserts ref == unfused == fused on all 8 output words, over fixed + random
 * inputs. The fused object drops the 32 inter-layer marshalling moves
 * (2*nOut copy-out + 2*nCopy copy-in) the separate-call chain emits.
 *
 * Build (owned `.s`, no jasminc):
 *   cd ../.. && lake env lean --run \
 *     CatCrypt/Crypto/SecureCompilation/VIR/Plonky3NttLayerInlineEmit.lean
 *   cd ../.. && lake exe plonky3owned      # for ntt_layer_from_rustcmd_owned.s
 *   gcc -O2 -o ntt_layer_fused_kat ntt_layer_fused_kat.c \
 *     gen_com/ntt_layer_fused_owned.s gen_com/ntt_layer_from_rustcmd_owned.s
 *   ./ntt_layer_fused_kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define P 2013265921ULL   /* BabyBear prime */
#define GEN 31ULL         /* BabyBear GENERATOR */

extern uint64_t *plonky3_ntt_layer8_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *plonky3_ntt_layer8x2_fused_rc(uint64_t *out, const uint64_t *inp);

static uint64_t bbmul(uint64_t a, uint64_t b) { return (a * b) % P; }
static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t bbsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }

static uint64_t bbpow(uint64_t base, uint64_t e) {
  uint64_t r = 1, cur = base;
  for (int i = 0; i < 64; i++) {
    if (e & 1) r = bbmul(r, cur);
    cur = bbmul(cur, cur);
    e >>= 1;
  }
  return r;
}
static uint64_t bb_root_of_unity(int k) { return bbpow(GEN, (P - 1) >> k); }

/* EXACT Plonky3ProveEmit.nttLayer vals omega 8 2 (one radix-2 layer). */
static void ntt_layer(uint64_t out[8], const uint64_t vals[8], uint64_t omega) {
  int n = 8, size = 8, half = 4;
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

/* Build the 18-word input ABI for a single layer over `v`. */
static void mk_inp(uint64_t inp[18], const uint64_t v[8], uint64_t omega) {
  uint64_t wSize = bbpow(omega, 8 / 8);
  for (int i = 0; i < 8; i++) inp[i] = v[i];
  for (int j = 0; j < 4; j++) inp[8 + j] = bbpow(wSize, (uint64_t)j);
  inp[12] = 2290649223ULL; inp[13] = P; inp[14] = 0;
  inp[15] = 30; inp[16] = 32; inp[17] = 63;
}

static int run_case(const char *name, const uint64_t v[8], uint64_t omega) {
  uint64_t ref1[8], ref[8];
  /* C reference: apply the layer twice (the squaring stage the fusion models). */
  ntt_layer(ref1, v, omega);
  ntt_layer(ref, ref1, omega);

  /* Unfused separate-call chain: layer twice through the single-leaf export. */
  uint64_t inp1[18], inp2[18], mid[8] = {0}, unfused[8] = {0};
  mk_inp(inp1, v, omega);
  plonky3_ntt_layer8_rc(mid, inp1);     /* layer 1 -> mid (copy-out to buffer) */
  mk_inp(inp2, mid, omega);             /* copy-in: mid becomes layer 2 input  */
  plonky3_ntt_layer8_rc(unfused, inp2); /* layer 2 -> unfused                  */

  /* Fused leaf: one call, no inter-layer buffer. Its 18-word ABI is layer 1's
   * (the values v + the shared twiddles/constants); layer 2 reuses them. */
  uint64_t inpf[18], fused[8] = {0};
  mk_inp(inpf, v, omega);
  plonky3_ntt_layer8x2_fused_rc(fused, inpf);

  int ok_ref     = (memcmp(fused, ref, sizeof ref) == 0);
  int ok_unfused = (memcmp(fused, unfused, sizeof unfused) == 0);
  int ok = ok_ref && ok_unfused;
  printf("  [%s] %-10s", ok ? "PASS" : "FAIL", name);
  if (!ok) {
    printf("\n    fused  :"); for (int i = 0; i < 8; i++) printf(" %lu", fused[i]);
    printf("\n    unfused:"); for (int i = 0; i < 8; i++) printf(" %lu", unfused[i]);
    printf("\n    ref    :"); for (int i = 0; i < 8; i++) printf(" %lu", ref[i]);
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
    printf("\nAll FUSED two-layer KAT cases PASS — fused leaf == unfused chain == 2x nttLayer, byte-identical.\n");
    return 0;
  } else {
    printf("\nFAILED: %d fused-layer case(s) mismatched.\n", fails);
    return 1;
  }
}
