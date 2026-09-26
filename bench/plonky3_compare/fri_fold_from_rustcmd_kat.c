/* KAT harness for the rustcmd-EMITTED Plonky3 FRI fold layer + bbInv.
 *
 * `Plonky3FriEmit.friFold (eval_pos, eval_neg, x, alpha)` and
 * `Plonky3FriEmit.bbInv a` are emitted as two register-arith leaves through the
 * verified front's EMIT-computation path (JasminAbiEmit.emitAbiOrchReg):
 *
 *   fri_fold_rc : the per-coset FRI fold
 *                 result = (ep+en)/2 + alpha * (ep-en)/(2x)
 *   bb_inv_rc   : the BabyBear modular inverse a^(p-2) (Fermat)
 *
 * Each leaf's body is built entirely from regArith mul/shr/sub/and/add bindings
 * (the Barrett field mul-mod + branchless add/sub + an unrolled square-and-
 * multiply for a^(p-2), no hardware `%`); leaf.denote = the Barrett word
 * arithmetic by construction (allRegArith proven in Lean, compositionally:
 * friFold_is_regarith_only / bbInv_is_regarith_only). The data-dependent
 * inverse 1/(2x) is computed INLINE inside fri_fold_rc by the same unrolled
 * Fermat chain (NOT an opaque finv / hardware %).
 *
 * We compare the emitted leaves against a self-contained C reference of the
 * EXACT Lean spec (friFold / bbInv) over fixed + pseudo-random inputs.
 *
 * Build (see Makefile target plonky3-fri-fold-rustcmd-kat):
 *   jasminc -arch x86-64 -nowarning -o fri_fold_from_rustcmd.s \
 *     gen_com/fri_fold_from_rustcmd.jazz
 *   gcc -O2 -o fri_fold_from_rustcmd_kat fri_fold_from_rustcmd_kat.c \
 *     fri_fold_from_rustcmd.s
 *   ./fri_fold_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define P 2013265921ULL   /* BabyBear prime */
#define NIN 16

/* jasmin export ABI: reg ptr out (first), reg const ptr inp; returns out. */
extern uint64_t *fri_fold_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_inv_rc(uint64_t *out, const uint64_t *inp);

/* ---- BabyBear field reference (mirrors Plonky3LdeEmit / Plonky3FriEmit) ---- */
static uint64_t bbmul(uint64_t a, uint64_t b) { return (a * b) % P; }
static uint64_t bbadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static uint64_t bbsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }
/* bbPow: byte-for-byte the Lean 64-iteration square-and-multiply loop. */
static uint64_t bbpow(uint64_t base, uint64_t e) {
  uint64_t r = 1, cur = base;
  for (int i = 0; i < 64; i++) { if (e & 1) r = bbmul(r, cur); cur = bbmul(cur, cur); e >>= 1; }
  return r;
}
/* bbInv a = a^(p-2); 0 |-> 0. */
static uint64_t bbinv(uint64_t a) { return a == 0 ? 0 : bbpow(a, P - 2); }

/* friFold(ep, en, x, alpha) -- the exact Plonky3FriEmit.friFold spec. */
static uint64_t fri_fold_ref(uint64_t ep, uint64_t en, uint64_t x, uint64_t alpha) {
  uint64_t sum     = bbadd(ep, en);
  uint64_t diff    = bbsub(ep, en);
  uint64_t invTwo  = bbinv(2);
  uint64_t twoX    = bbmul(2, x);
  uint64_t invTwoX = bbinv(twoX);
  uint64_t pEven   = bbmul(sum, invTwo);
  uint64_t pOdd    = bbmul(diff, invTwoX);
  return bbadd(pEven, bbmul(alpha, pOdd));
}

/* ---- input-vector construction (mirrors the Lean foldInName / bbInvInName) ----
 * fri_fold leaf: words 0..3 = ep,en,x,alpha (copied into the value file);
 *   the constants (invTwo, 2, 1, MU, p, 0,30,32,63) are immediates baked into
 *   the body and are NOT read from inp.
 * bb_inv  leaf: word 0 = a (copied in); rest immediates. */
static uint64_t emitted_fold(uint64_t ep, uint64_t en, uint64_t x, uint64_t alpha) {
  uint64_t inp[NIN]; memset(inp, 0, sizeof inp);
  inp[0] = ep; inp[1] = en; inp[2] = x; inp[3] = alpha;
  uint64_t out[1] = {0};
  fri_fold_rc(out, inp);
  return out[0];
}
static uint64_t emitted_inv(uint64_t a) {
  uint64_t inp[NIN]; memset(inp, 0, sizeof inp);
  inp[0] = a;
  uint64_t out[1] = {0};
  bb_inv_rc(out, inp);
  return out[0];
}

static int run_fold(const char *name, uint64_t ep, uint64_t en, uint64_t x, uint64_t al) {
  uint64_t e = emitted_fold(ep, en, x, al);
  uint64_t r = fri_fold_ref(ep, en, x, al);
  int ok = (e == r);
  printf("  [%s] fold %-12s", ok ? "PASS" : "FAIL", name);
  if (!ok) printf("  emit=%lu ref=%lu  (ep=%lu en=%lu x=%lu al=%lu)", e, r, ep, en, x, al);
  printf("\n");
  return ok ? 0 : 1;
}
static int run_inv(const char *name, uint64_t a) {
  /* bbInv on a=0 is the spec's 0|->0; the emitted leaf computes a^(p-2)
   * directly, which for a!=0 equals the inverse. We only KAT nonzero a
   * (the spec branch the fold ever exercises is twoX != 0). */
  uint64_t e = emitted_inv(a);
  uint64_t r = bbinv(a);
  int ok = (e == r);
  printf("  [%s] inv  %-12s", ok ? "PASS" : "FAIL", name);
  if (!ok) printf("  emit=%lu ref=%lu  (a=%lu)", e, r, a);
  printf("\n");
  return ok ? 0 : 1;
}

int main(void) {
  int fails = 0;

  /* ---- bbInv KAT (the new primitive) ---- */
  fails += run_inv("two",  2);          /* should be (p+1)/2 = 1006632961 */
  fails += run_inv("one",  1);
  fails += run_inv("gen",  31);
  fails += run_inv("hi",   P - 1);

  /* ---- friFold fixed KAT (matches the Lean native_decide KATs) ---- */
  fails += run_fold("specific", 100, 50, 7, 3);   /* spec: 287609503 */
  fails += run_fold("const1",   42, 42, 5, 999);  /* constant poly -> 42 */
  fails += run_fold("const2",   1, 1, 1, 0);      /* -> 1 */
  fails += run_fold("zeros",    0, 0, 1, 0);

  /* sanity: the specific KAT value */
  { uint64_t r = fri_fold_ref(100, 50, 7, 3);
    printf("  [%s] friFold(100,50,7,3) ref = %lu (expect 287609503)\n",
           r == 287609503ULL ? "PASS" : "FAIL", r);
    if (r != 287609503ULL) fails++; }

  /* ---- pseudo-random fold + inv KAT ---- */
  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int t = 0; t < 64; t++) {
    uint64_t v[4];
    for (int i = 0; i < 4; i++) { st ^= st<<13; st ^= st>>7; st ^= st<<17; v[i] = st % P; }
    if (v[2] == 0) v[2] = 1;  /* x != 0 so 2x invertible */
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", t);
    fails += run_fold(nm, v[0], v[1], v[2], v[3]);
    uint64_t a = v[0] == 0 ? 1 : v[0];
    fails += run_inv(nm, a);
  }

  if (fails == 0) {
    printf("\nAll FRI-fold KAT cases PASS -- EMITTED fri_fold_rc / bb_inv_rc == spec friFold / bbInv.\n");
    return 0;
  } else {
    printf("\nFAILED: %d FRI-fold case(s) did not match spec.\n", fails);
    return 1;
  }
}
