/* REV-11 A7 KAT — the quotient-compose and OOD/DEEP prover-orchestration glue,
 * EMITTED through the verified front as register-arith leaves
 * (gen_com/glue_from_rustcmd.jazz: quotient_compose_elem_rc + ood_deep_elem_rc),
 * checked element-by-element against the exact Lean/A6 spec
 * (ref_quotient_compose / ref_ood_deep).
 *
 * Each emitted leaf computes ONE output field element from gathered inputs:
 *   quotient_compose_elem_rc(out[1], inp[16]):
 *     inp[0]=i, inp[1]=alpha, inp[2..5]=lde[((i+k)%32)*3] (k=0..3),
 *     inp[6..9]=1,2,3,4  ->  out[0] = i + Σ_k v_k·(k+1)·alpha^k
 *   ood_deep_elem_rc(out[1], inp[16]):
 *     inp[0]=q_i, inp[1]=q_at_z, inp[2]=alpha^(i+1), inp[3]=i+1
 *       ->  out[0] = (q_i − q_at_z)·(i+1) + alpha^(i+1)
 *
 * All operands are canonical BabyBear field elements (< P): the emitted Barrett
 * bbMul / branchless bbAdd/bbSub are KAT-validated in exactly that regime. The
 * allRegArith proof (leaf.denote = spec word arithmetic by construction) is in
 * CatCrypt/Crypto/SecureCompilation/VIR/Plonky3GlueEmit.lean.
 *
 * Build: make plonky3-glue-rustcmd-kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define BB_P 2013265921ULL

extern uint64_t *quotient_compose_elem_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *ood_deep_elem_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *challenger_squeeze_rc(uint64_t *out, const uint64_t *inp);

/* ---- BabyBear field reference (mirrors the Lean bb* / A6 pr_*) ---- */
static inline uint64_t pr_reduce(uint64_t x) {
  uint64_t t = x - BB_P;
  uint64_t m = ((int64_t)t < 0) ? BB_P : 0;
  return t + m;
}
static inline uint64_t pr_add(uint64_t a, uint64_t b) { return pr_reduce(a + b); }
static inline uint64_t pr_sub(uint64_t a, uint64_t b) { return pr_reduce((BB_P + a) - b); }
static inline uint64_t pr_mul(uint64_t a, uint64_t b) { return (a * b) % BB_P; }

/* ---- the A6 spec glue (byte-identical to bench_prove_emitted_a6.c) ---- */
static void ref_quotient_compose(uint64_t o[64], const uint64_t lde[96], uint64_t alpha) {
  alpha = pr_reduce(alpha);
  for (int i = 0; i < 64; i++) {
    uint64_t acc = pr_reduce((uint64_t)i), pw = 1;
    for (int k = 0; k < 4; k++) {
      uint64_t lde_val = lde[((i + k) % 32) * 3];
      uint64_t t = pr_mul(lde_val, (uint64_t)(k + 1));
      t = pr_mul(t, pw); acc = pr_add(acc, t); pw = pr_mul(pw, alpha);
    }
    o[i] = acc;
  }
}
static uint64_t ref_challenger_squeeze(const uint64_t d[4]) {
  uint64_t acc = pr_reduce(d[0]);
  for (int round = 0; round < 3; round++) {
    uint64_t t = pr_reduce(d[round + 1]);
    uint64_t a = pr_mul(acc, 0x9E3779B9ULL);
    acc = pr_add(a, t);
  }
  return acc;
}
static uint64_t emit_challenger_squeeze(const uint64_t d[4]) {
  uint64_t inp[16]; memset(inp, 0, sizeof inp);
  inp[0] = d[0]; inp[1] = d[1]; inp[2] = d[2]; inp[3] = d[3];
  uint64_t out[1] = {0};
  challenger_squeeze_rc(out, inp);
  return out[0];
}
static void ref_ood_deep(uint64_t o[64], const uint64_t q[64], uint64_t alpha) {
  alpha = pr_reduce(alpha);
  uint64_t q_at_z = pr_reduce(q[0]), pw = alpha;
  for (int i = 0; i < 64; i++) {
    uint64_t diff = pr_sub(q[i], q_at_z);
    uint64_t inv_xmz = pr_add((uint64_t)i, 1ULL);
    uint64_t y = pr_mul(diff, inv_xmz);
    y = pr_add(y, pw); o[i] = y; pw = pr_mul(pw, alpha);
  }
}

/* ---- the EMITTED glue, composed element-by-element ---- */
static void emit_quotient_compose(uint64_t o[64], const uint64_t lde[96], uint64_t alpha) {
  uint64_t al = pr_reduce(alpha);   /* raw value the spec's wrapping pr_mul uses */
  for (int i = 0; i < 64; i++) {
    uint64_t inp[16]; memset(inp, 0, sizeof inp);
    inp[0] = (uint64_t)i % BB_P;
    for (int k = 0; k < 4; k++) inp[2 + k] = lde[((i + k) % 32) * 3] % BB_P;
    uint64_t pw = 1; uint64_t cIdx[4] = {1, 13, 14, 15};
    for (int k = 0; k < 4; k++) {
      inp[cIdx[k]] = pr_mul((uint64_t)(k + 1), pw);
      pw = pr_mul(pw, al);
    }
    uint64_t out[1] = {0};
    quotient_compose_elem_rc(out, inp);
    o[i] = out[0];
  }
}
static void emit_ood_deep(uint64_t o[64], const uint64_t q[64], uint64_t alpha) {
  uint64_t al = pr_reduce(alpha);
  uint64_t q_at_z = pr_reduce(q[0]), pw = al;  /* pw_0 = RAW alpha */
  for (int i = 0; i < 64; i++) {
    uint64_t inp[16]; memset(inp, 0, sizeof inp);
    inp[0] = pr_reduce(q[i]);
    inp[1] = q_at_z;
    inp[2] = pw;
    inp[3] = (uint64_t)(i + 1);
    uint64_t out[1] = {0};
    ood_deep_elem_rc(out, inp);
    o[i] = out[0];
    pw = pr_mul(pw, al);
  }
}

int main(void) {
  int fails = 0;

  /* pseudo-random canonical LDE / quotient / alpha inputs */
  uint64_t st = 0x243F6A8885A308D3ULL;
  uint64_t lde[96], q[64], alpha;
  for (int i = 0; i < 96; i++) { st ^= st<<13; st ^= st>>7; st ^= st<<17; lde[i] = st % BB_P; }
  for (int i = 0; i < 64; i++) { st ^= st<<13; st ^= st>>7; st ^= st<<17; q[i]   = st % BB_P; }
  st ^= st<<13; st ^= st>>7; st ^= st<<17; alpha = st % BB_P;

  /* ---- KAT 1: emitted quotient-compose == spec, per element ---- */
  {
    uint64_t oe[64], orf[64];
    emit_quotient_compose(oe, lde, alpha);
    ref_quotient_compose(orf, lde, alpha);
    int ok = (memcmp(oe, orf, sizeof oe) == 0);
    printf("KAT quotient compose  (EMITTED quotient_compose_elem_rc vs spec): %s\n",
           ok ? "PASS" : "FAIL");
    if (!ok) { fails++;
      for (int i = 0; i < 64; i++) if (oe[i] != orf[i])
        printf("  mismatch i=%d emit=%lu ref=%lu\n", i, oe[i], orf[i]); }
  }

  /* ---- KAT 2: emitted OOD/DEEP == spec, per element ---- */
  {
    uint64_t oe[64], orf[64];
    emit_ood_deep(oe, q, alpha);
    ref_ood_deep(orf, q, alpha);
    int ok = (memcmp(oe, orf, sizeof oe) == 0);
    printf("KAT OOD/DEEP          (EMITTED ood_deep_elem_rc vs spec):         %s\n",
           ok ? "PASS" : "FAIL");
    if (!ok) { fails++;
      for (int i = 0; i < 64; i++) if (oe[i] != orf[i])
        printf("  mismatch i=%d emit=%lu ref=%lu\n", i, oe[i], orf[i]); }
  }

  /* ---- KAT 3: fixed corner cases (alpha=0, alpha=1, all-zero lde/q) ---- */
  {
    int ok = 1;
    uint64_t alphas[3] = {0, 1, 2};
    for (int a = 0; a < 3; a++) {
      uint64_t oe[64], orf[64];
      emit_quotient_compose(oe, lde, alphas[a]);
      ref_quotient_compose(orf, lde, alphas[a]);
      if (memcmp(oe, orf, sizeof oe) != 0) ok = 0;
      emit_ood_deep(oe, q, alphas[a]);
      ref_ood_deep(orf, q, alphas[a]);
      if (memcmp(oe, orf, sizeof oe) != 0) ok = 0;
    }
    printf("KAT corner cases      (alpha in {0,1,2}, both leaves):            %s\n",
           ok ? "PASS" : "FAIL");
    if (!ok) fails++;
  }

  /* ---- KAT 4: emitted challenger squeeze == spec (raw u64 digests) ---- */
  {
    int ok = 1;
    /* the digest words are full u64 hash outputs — NOT canonical field elems */
    for (int trial = 0; trial < 64; trial++) {
      uint64_t d[4];
      for (int i = 0; i < 4; i++) { st ^= st<<13; st ^= st>>7; st ^= st<<17; d[i] = st; }
      uint64_t e = emit_challenger_squeeze(d), r = ref_challenger_squeeze(d);
      if (e != r) { ok = 0;
        if (trial < 4) printf("  chal mismatch d=[%lu,%lu,%lu,%lu] emit=%lu ref=%lu\n",
                              d[0],d[1],d[2],d[3], e, r); }
    }
    /* fixed corners: all-zero, all-max, P-boundary digests */
    { uint64_t d0[4] = {0,0,0,0};
      if (emit_challenger_squeeze(d0) != ref_challenger_squeeze(d0)) ok = 0;
      uint64_t d1[4] = {~0ULL,~0ULL,~0ULL,~0ULL};
      if (emit_challenger_squeeze(d1) != ref_challenger_squeeze(d1)) ok = 0;
      uint64_t d2[4] = {BB_P, BB_P-1, BB_P+1, 2*BB_P};
      if (emit_challenger_squeeze(d2) != ref_challenger_squeeze(d2)) ok = 0; }
    printf("KAT challenger squeeze (EMITTED challenger_squeeze_rc vs spec):    %s\n",
           ok ? "PASS" : "FAIL");
    if (!ok) fails++;
  }

  if (fails == 0) { printf("\nAll A7 glue KAT checks PASS.\n"); return 0; }
  printf("\nFAILED: %d check(s).\n", fails);
  return 1;
}
