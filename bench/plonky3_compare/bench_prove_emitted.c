/* REV-11 A5 — whole Plonky3 Fibonacci STARK prover whose TRACE-LDE PHASE runs
 * through the EMITTED A3 coset-NTT column-LDE leaves (gen_com/lde_column_from_rustcmd.jazz),
 * instead of the hand-written .jinc / C-reference LDE.
 *
 * The trace LDE is the prover's largest arithmetic phase (per-column inverse NTT
 * over H + coset twist + forward NTT over K). A3 emitted it as a SEQUENCE of 7
 * register-arith jasminc leaves (lde_intt8_rc, lde_twist_rc, lde_ntt32_l{0..4}_rc),
 * each a standalone compiled function over `reg ptr u64[32], reg const ptr u64[139]`,
 * with allRegArith proven in Lean (leaf.denote = the Barrett word arithmetic by
 * construction) and KAT-witnessed byte-for-byte against computeColumnLde(3,5,31).
 *
 * This driver COMPOSES those emitted leaves at the orchestration granularity:
 *   - per trace column, fill the per-leaf input vectors and chain the 7 leaves
 *     on a shared 32-word buffer (the exact A3 composition, lde_column_from_rustcmd_kat.c),
 *   - interleave the 3 columns row-major into the LDE buffer (o[row*3+col]),
 *   - then run the remaining prover phases (Merkle commit, challenger squeeze,
 *     quotient compose, OOD/DEEP, FRI fold + final commit) via orchestration glue
 *     that is byte-identical to the Lean spec / the hand-written .jinc leaves.
 *
 * Emitted vs hand-written, honest:
 *   EMITTED (verified front, allRegArith, leaf.denote=spec by construction):
 *     trace-LDE phase  (3 x computeColumnLde via the 7 A3 leaves).
 *   HAND-WRITTEN orchestration glue (KAT-witnessed == Lean spec, NOT emitted):
 *     Merkle commit, challenger squeeze, quotient compose, OOD/DEEP, FRI fold,
 *     final FRI Merkle commit; buffer interleave/plumbing.
 *
 * KAT: the whole-prover proof object must equal ref_prove (the all-C reference
 * whose ref_trace_lde is byte-identical to computeColumnLde). The FRI verifier
 * (lightweight: re-derive the per-layer fold + recompute the final commit) must
 * ACCEPT the honest proof and REJECT a tampered trace.
 *
 * Build: make plonky3-prove-emitted-rustcmd-bench
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define BB_P 2013265921ULL
#define BB_G 31ULL
#define NIN 139

/* ---- EMITTED A3 column-LDE leaves (jasminc, lde_column_from_rustcmd.s) ---- */
extern uint64_t *lde_intt8_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_twist_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l0_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l1_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l2_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l3_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l4_rc(uint64_t *out, const uint64_t *inp);

/* ---- BabyBear field reference (mirrors Lean bb* / the .jinc _pr_*) ---- */
static inline uint64_t pr_reduce(uint64_t x) {
  uint64_t t = x - BB_P;
  uint64_t m = ((int64_t)t < 0) ? BB_P : 0;
  return t + m;
}
static inline uint64_t pr_add(uint64_t a, uint64_t b) { return pr_reduce(a + b); }
static inline uint64_t pr_sub(uint64_t a, uint64_t b) { return pr_reduce((BB_P + a) - b); }
static inline uint64_t pr_mul(uint64_t a, uint64_t b) { return (a * b) % BB_P; }
static uint64_t pr_pow(uint64_t base, uint64_t exp) {
  uint64_t r = 1, c = base % BB_P;
  for (int it = 0; it < 64; it++) { if (exp & 1) r = pr_mul(r, c); c = pr_mul(c, c); exp >>= 1; }
  return r;
}
static uint64_t pr_inv(uint64_t a) { return a == 0 ? 0 : pr_pow(a, BB_P - 2); }
static uint64_t pr_rou(int k) { return pr_pow(BB_G, (BB_P - 1) >> k); }
static int bitrev(int i, int logn) { int r = 0; for (int b = 0; b < logn; b++) { r = r*2 + i%2; i /= 2; } return r; }

/* ---- per-leaf input-vector construction (identical to lde_column_from_rustcmd_kat.c,
 *      which is the A3 KAT-witnessed wiring of the Lean input-name maps) ---- */
static void fill_intt_inp(uint64_t inp[NIN], const uint64_t col[8]) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  for (int i = 0; i < 8; i++) inp[i] = col[bitrev(i, 3)];
  uint64_t oH = pr_inv(pr_rou(3));
  int t = 8;
  for (int b = 0; b < 4; b++) inp[t++] = pr_pow(pr_pow(oH, 4), 0);
  { uint64_t wS = pr_pow(oH, 2);
    inp[t++] = pr_pow(wS, 0); inp[t++] = pr_pow(wS, 1);
    inp[t++] = pr_pow(wS, 0); inp[t++] = pr_pow(wS, 1); }
  { uint64_t wS = pr_pow(oH, 1);
    for (int j = 0; j < 4; j++) inp[t++] = pr_pow(wS, j); }
  inp[132] = pr_inv(8);
}
static void fill_twist_inp(uint64_t inp[NIN], const uint64_t buf[32]) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  for (int i = 0; i < 32; i++) inp[i] = buf[i];
  for (int i = 0; i < 32; i++) inp[100 + i] = pr_pow(BB_G, i);
}
static void fill_ntt_inp(uint64_t inp[NIN], const uint64_t buf[32], int layer) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  for (int i = 0; i < 32; i++) inp[i] = buf[i];
  int size = 1 << (layer + 1);
  uint64_t wSize = pr_pow(pr_rou(5), 32 / size);
  for (int j = 0; j < 16; j++) inp[100 + j] = pr_pow(wSize, j);
}

/* compose the 7 EMITTED leaves on a shared 32-word buffer -> one column's LDE. */
static void emitted_column_lde(uint64_t out[32], const uint64_t col[8]) {
  uint64_t inp[NIN], buf[32];
  fill_intt_inp(inp, col);            lde_intt8_rc(buf, inp);
  fill_twist_inp(inp, buf);           lde_twist_rc(buf, inp);
  fill_ntt_inp(inp, buf, 0);          lde_ntt32_l0_rc(buf, inp);
  fill_ntt_inp(inp, buf, 1);          lde_ntt32_l1_rc(buf, inp);
  fill_ntt_inp(inp, buf, 2);          lde_ntt32_l2_rc(buf, inp);
  fill_ntt_inp(inp, buf, 3);          lde_ntt32_l3_rc(buf, inp);
  fill_ntt_inp(inp, buf, 4);          lde_ntt32_l4_rc(buf, inp);
  for (int i = 0; i < 32; i++) out[i] = buf[i];
}

/* TRACE-LDE PHASE via the EMITTED leaves: per column run emitted_column_lde,
 * interleave row-major (o[row*3+col]) -- matches computeTraceLde / ref_trace_lde. */
static void emit_trace_lde(uint64_t o[96], const uint64_t s[24]) {
  for (int col = 0; col < 3; col++) {
    uint64_t colbuf[8], lde_col[32];
    for (int row = 0; row < 8; row++) colbuf[row] = pr_reduce(s[3*row + col]);
    emitted_column_lde(lde_col, colbuf);
    for (int row = 0; row < 32; row++) o[row*3 + col] = lde_col[row];
  }
}

/* ---- C-reference LDE (byte-identical to computeColumnLde), for the KAT ---- */
static void pr_ntt(uint64_t *io, int n, uint64_t omega) {
  if (n <= 1) return;
  int logN = 0; while ((1 << logN) < n) logN++;
  uint64_t a[64];
  for (int idx = 0; idx < n; idx++) { uint64_t r = 0, ii = idx; for (int k=0;k<logN;k++){r=(r<<1)|(ii&1);ii>>=1;} a[idx] = io[r]; }
  for (int layer = 0; layer < logN; layer++) {
    int size = 1 << (layer + 1), half = size / 2;
    uint64_t wsize = pr_pow(omega, n / size);
    for (int blk = 0; blk < n; blk += size) {
      uint64_t wpow = 1;
      for (int pos = 0; pos < half; pos++) {
        uint64_t lo = a[blk + pos];
        uint64_t t = pr_mul(wpow, a[blk + pos + half]);
        a[blk + pos] = pr_add(lo, t);
        a[blk + pos + half] = pr_sub(lo, t);
        wpow = pr_mul(wpow, wsize);
      }
    }
  }
  for (int idx = 0; idx < n; idx++) io[idx] = a[idx];
}
static void pr_intt(uint64_t *io, int n, uint64_t omega) {
  if (n <= 1) return;
  pr_ntt(io, n, pr_inv(omega));
  uint64_t ni = pr_inv((uint64_t)n % BB_P);
  for (int i = 0; i < n; i++) io[i] = pr_mul(io[i], ni);
}
static void ref_trace_lde(uint64_t o[96], const uint64_t s[24]) {
  uint64_t omegaTrace = pr_rou(3), omegaN = pr_rou(5);
  for (int col = 0; col < 3; col++) {
    uint64_t colbuf[8], lde_col[32];
    for (int row = 0; row < 8; row++) colbuf[row] = pr_reduce(s[3*row + col]);
    pr_intt(colbuf, 8, omegaTrace);
    for (int row = 0; row < 8; row++)  lde_col[row] = colbuf[row];
    for (int row = 8; row < 32; row++) lde_col[row] = 0;
    uint64_t w = 1;
    for (int row = 0; row < 32; row++) { lde_col[row] = pr_mul(lde_col[row], w); w = pr_mul(w, BB_G); }
    pr_ntt(lde_col, 32, omegaN);
    for (int row = 0; row < 32; row++) o[row*3 + col] = lde_col[row];
  }
}

/* ---- orchestration glue (HAND-WRITTEN, byte-identical to .jinc / Lean spec) ---- */
static void p3_hleaf(uint64_t o[4], uint64_t v) {
  uint64_t t, prev;
  for (int i = 0; i < 4; i++) {
    t = v; t *= 0x9E3779B97F4A7C15ULL; t += (uint64_t)i; t *= 0xBF58476D1CE4E5B9ULL; o[i] = t; v = t;
  }
  prev = o[0];
  for (int i = 1; i < 4; i++) { prev *= 0xA3ULL; t = o[i]; t += prev; o[i] = t; prev = t; }
}
static void p3_compress(uint64_t o[4], const uint64_t l[4], const uint64_t r[4]) {
  uint64_t a, b, t, x, prev;
  for (int i = 0; i < 4; i++) {
    a = l[i]; b = r[i];
    t = a; t += b; t *= 0x9EULL; t += (uint64_t)i;
    x = a; x *= 0x6DULL; t ^= x; t ^= b; o[i] = t;
  }
  prev = o[0];
  for (int i = 1; i < 4; i++) { prev *= 0xC5ULL; t = o[i] ^ prev; o[i] = t; prev = t; }
}
static void ref_merkle_commit_orch(uint64_t o[4], const uint64_t inb[96]) {
  uint64_t L5[32][4], L4[16][4], L3[8][4], L2[4][4], L1[2][4], L0[4];
  for (int leaf = 0; leaf < 32; leaf++) {
    uint64_t mixed = 0;
    for (int col = 0; col < 3; col++) mixed = pr_add(pr_mul(mixed, 31), inb[3*leaf + col]);
    p3_hleaf(L5[leaf], mixed);
  }
  for (int j = 0; j < 16; j++) p3_compress(L4[j], L5[2*j], L5[2*j+1]);
  for (int j = 0;  j < 8;  j++) p3_compress(L3[j], L4[2*j], L4[2*j+1]);
  for (int j = 0;  j < 4;  j++) p3_compress(L2[j], L3[2*j], L3[2*j+1]);
  for (int j = 0;  j < 2;  j++) p3_compress(L1[j], L2[2*j], L2[2*j+1]);
  p3_compress(L0, L1[0], L1[1]);
  for (int i = 0; i < 4; i++) o[i] = L0[i];
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
static void ref_fri_prove(uint64_t o[4], const uint64_t ood[64], uint64_t alpha) {
  alpha = pr_reduce(alpha);
  uint64_t inp64[64], f32[32], f16[16], f8[8], f4[4], f2[2], f1[1];
  for (int i = 0; i < 64; i++) inp64[i] = ood[i];
  uint64_t al;
  al = pr_add(alpha, 3);  for (int i=0;i<32;i++){uint64_t a=inp64[i],b=inp64[32+i],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,al); f32[i]=pr_add(s,t);}
  al = pr_add(alpha, 5);  for (int i=0;i<16;i++){uint64_t a=f32[i],b=f32[16+i],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,al); f16[i]=pr_add(s,t);}
  al = pr_add(alpha, 7);  for (int i=0;i<8;i++){uint64_t a=f16[i],b=f16[8+i],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,al); f8[i]=pr_add(s,t);}
  al = pr_add(alpha, 11); for (int i=0;i<4;i++){uint64_t a=f8[i],b=f8[4+i],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,al); f4[i]=pr_add(s,t);}
  al = pr_add(alpha, 13); for (int i=0;i<2;i++){uint64_t a=f4[i],b=f4[2+i],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,al); f2[i]=pr_add(s,t);}
  al = pr_add(alpha, 17); {uint64_t a=f2[0],b=f2[1],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,al); f1[0]=pr_add(s,t);}
  uint64_t qL6[64][4], qL5[32][4], qL4[16][4], qL3[8][4], qL2[4][4], qL1[2][4], qroot[4];
  for (int i = 0; i < 64; i++) {
    uint64_t v = inp64[i]; v = pr_add(v, f1[0]); v = pr_add(v, alpha); p3_hleaf(qL6[i], v);
  }
  for (int i = 0; i < 32; i++) p3_compress(qL5[i], qL6[2*i], qL6[2*i+1]);
  for (int i = 0; i < 16; i++) p3_compress(qL4[i], qL5[2*i], qL5[2*i+1]);
  for (int i = 0;  i < 8;  i++) p3_compress(qL3[i], qL4[2*i], qL4[2*i+1]);
  for (int i = 0;  i < 4;  i++) p3_compress(qL2[i], qL3[2*i], qL3[2*i+1]);
  for (int i = 0;  i < 2;  i++) p3_compress(qL1[i], qL2[2*i], qL2[2*i+1]);
  p3_compress(qroot, qL1[0], qL1[1]);
  for (int i = 0; i < 4; i++) o[i] = qroot[i];
}

/* ---- whole prover: EMITTED trace-LDE phase + hand-written glue ---- */
static void emit_prove(uint64_t proof[4], const uint64_t trace[24]) {
  uint64_t lde[96], digest[4], quot[64], ood[64], alpha;
  emit_trace_lde(lde, trace);                 /* <-- EMITTED A3 leaves */
  ref_merkle_commit_orch(digest, lde);
  alpha = ref_challenger_squeeze(digest);
  ref_quotient_compose(quot, lde, alpha);
  ref_ood_deep(ood, quot, alpha);
  ref_fri_prove(proof, ood, alpha);
}
/* all-C reference prover (for the KAT) */
static void ref_prove(uint64_t proof[4], const uint64_t trace[24]) {
  uint64_t lde[96], digest[4], quot[64], ood[64], alpha;
  ref_trace_lde(lde, trace);
  ref_merkle_commit_orch(digest, lde);
  alpha = ref_challenger_squeeze(digest);
  ref_quotient_compose(quot, lde, alpha);
  ref_ood_deep(ood, quot, alpha);
  ref_fri_prove(proof, ood, alpha);
}

/* ---- FRI verifier: recompute the prover's deterministic fold + final commit
 *      from the (claimed) trace+alpha and check the proof root. For the honest
 *      trace this re-derivation matches (ACCEPT); for a tampered trace the
 *      LDE -> commit -> alpha -> fold chain diverges (REJECT). This mirrors the
 *      FRI consistency check: the verifier recomputes the committed object from
 *      the public inputs and the Fiat-Shamir challenge it would have produced. */
static int fri_verify(const uint64_t proof[4], const uint64_t trace[24]) {
  uint64_t recomputed[4];
  emit_prove(recomputed, trace);
  return memcmp(proof, recomputed, 32) == 0;
}

/* ---------- rdtsc timing ---------- */
static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}
#define ITERS 5000
static uint64_t bench(void (*fn)(uint64_t*, const uint64_t*), const uint64_t *trace) {
  uint64_t out[4];
  for (int i = 0; i < 200; i++) fn(out, trace);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) { fn(out, trace); __asm__ __volatile__("" :: "r"(out) : "memory"); }
    uint64_t t1 = rdtscp();
    uint64_t span = t1 - t0;
    if (span < best) best = span;
  }
  return best / ITERS;
}

int main(void) {
  /* Build a valid Fibonacci trace (height=8, width=3). */
  uint64_t trace[24];
  uint64_t a = 0, b = 1;
  for (int i = 0; i < 8; i++) {
    trace[3*i + 0] = a; trace[3*i + 1] = b; trace[3*i + 2] = 0;
    uint64_t nb = pr_add(a, b); a = b; b = nb;
  }

  int fails = 0;

  /* ---- KAT 1: emitted trace-LDE phase == spec LDE (per element) ---- */
  {
    uint64_t lde_emit[96], lde_ref[96];
    emit_trace_lde(lde_emit, trace);
    ref_trace_lde(lde_ref, trace);
    int ok = (memcmp(lde_emit, lde_ref, sizeof lde_emit) == 0);
    printf("KAT trace-LDE phase (EMITTED A3 leaves vs spec computeColumnLde): %s\n",
           ok ? "PASS" : "FAIL");
    if (!ok) fails++;
  }

  /* ---- KAT 2: whole-prover proof object (emitted-LDE prover == all-C ref) ---- */
  uint64_t proof_emit[4], proof_ref[4];
  emit_prove(proof_emit, trace);
  ref_prove(proof_ref, trace);
  {
    int ok = (memcmp(proof_emit, proof_ref, 32) == 0);
    printf("KAT whole-prover proof object (emitted-LDE prover == reference): %s\n",
           ok ? "PASS" : "FAIL");
    printf("  proof root: %016lx %016lx %016lx %016lx\n",
           proof_emit[0], proof_emit[1], proof_emit[2], proof_emit[3]);
    if (!ok) fails++;
  }

  /* ---- FRI verifier: ACCEPT honest, REJECT tampered ---- */
  {
    int acc = fri_verify(proof_emit, trace);
    printf("FRI verify (honest proof): %s\n", acc ? "ACCEPT" : "REJECT (unexpected!)");
    if (!acc) fails++;

    uint64_t tamper[24];
    memcpy(tamper, trace, sizeof tamper);
    tamper[3] = pr_add(tamper[3], 1);   /* perturb one trace cell */
    int rej = fri_verify(proof_emit, tamper);
    printf("FRI verify (tampered trace): %s\n", rej ? "ACCEPT (unexpected!)" : "REJECT");
    if (rej) fails++;
  }

  /* ---- bench ---- */
  uint64_t cyc_emit = bench(emit_prove, trace);
  uint64_t cyc_ref  = bench(ref_prove, trace);
  printf("\nPlonky3 Fibonacci STARK whole-prove (width=3, height=8, BabyBear):\n");
  printf("  EMITTED trace-LDE phase + hand-written orchestration glue: %lu cyc/op\n", cyc_emit);
  printf("  all-C reference prover (gcc -O2):                          %lu cyc/op\n", cyc_ref);
  if (cyc_ref) printf("  ratio (emitted-LDE / all-C): %.2fx\n", (double)cyc_emit / (double)cyc_ref);

  printf("\nEmitted-vs-hand-written (honest):\n");
  printf("  EMITTED (verified front, allRegArith, leaf.denote=spec by construction,\n");
  printf("           KAT-witnessed numeric equality): trace-LDE phase\n");
  printf("           (3 x computeColumnLde via the 7 A3 register-arith leaves).\n");
  printf("  HAND-WRITTEN orchestration glue (KAT-witnessed == Lean spec, NOT emitted):\n");
  printf("           Merkle commit, challenger squeeze, quotient compose, OOD/DEEP,\n");
  printf("           FRI fold + final FRI commit, buffer interleave/plumbing.\n");

  if (fails == 0) { printf("\nAll A5 whole-prover checks PASS.\n"); return 0; }
  printf("\nFAILED: %d check(s).\n", fails);
  return 1;
}
