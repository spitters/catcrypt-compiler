/* TASK #647: p3-verifier-accepted prover over the EMITTED Poseidon2 leaf.
 *
 * This implements the EXACT `p3-uni-stark` 0.5.3 `prove()` pipeline for the
 * Fibonacci AIR under the interop config (DEFAULT BabyBear Poseidon2-16
 * constants, log_blowup=2, log_final_poly_len=2, max_log_arity=1, 8 queries,
 * 0 PoW bits) — including the two phases the previous honest prover lacked:
 *
 *   (1) the quotient / DEEP-ALI phase: evaluate the folded AIR constraints on
 *       the disjoint quotient coset, divide by the zerofier Z_H, flatten the
 *       degree-4-extension quotient into base columns, LDE + Merkle-commit it,
 *       and open trace/quotient at the out-of-domain point zeta (barycentric);
 *   (2) degree-4 binomial-extension (x^4 = 11) arithmetic end-to-end: the
 *       challenges alpha/zeta/FRI-alpha/beta are extension elements, the
 *       reduced openings and the FRI fold run over the extension, and the FRI
 *       commit-phase layer commits flattened extension rows;
 *
 * plus (3) the exact DuplexChallenger<16,8> transcript order and the
 * bincode/serde wire layout of `Proof<SC>` (monty-form u32 field elements).
 *
 * Every Poseidon2 permutation (Merkle leaf hash, 2-to-1 compress, Fiat-Shamir
 * duplex) goes through the verified-emitted jasmin leaf `hp_perm16`
 * (plonky3_honest_prove.s) — the same leaf that KAT-matches upstream
 * `test_default_babybear_poseidon2_width_16`.
 *
 * Output: `p3_our_proof.bin` — to be byte-compared against the real p3
 * prover's `p3_ref/p3_default_proof.bin` and fed to the REAL p3 verifier
 * (`p3-fib-dump verify p3_our_proof.bin`).
 *
 * It also prints each intermediate in the same format as `p3-fib-dump` so the
 * two transcripts can be diffed stage by stage.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define P 2013265921ULL /* BabyBear: 2^31 - 2^27 + 1 */
#define GEN 31ULL       /* multiplicative generator */
#define EXT_W 11ULL     /* binomial extension: x^4 = 11 */

/* p3 canonical two-adic generators (TWO_ADIC_GENERATORS table, canonical form) */
#define TAG2 1728404513ULL /* order 4   */
#define TAG3 1592366214ULL /* order 8   */
#define TAG5 760005850ULL  /* order 32  */

/* the verified-emitted Poseidon2-BabyBear-16 permutation leaf (jasmin) */
extern uint64_t *hp_perm16(uint64_t *o, const uint64_t *s);

/* the verified-emitted A3 column-LDE leaves (lde_column_from_rustcmd.s).
 * Their roots of unity (31^((p-1)>>k)) coincide with p3's TWO_ADIC_GENERATORS
 * table, so the composition computes exactly p3's coset_lde_batch column. */
#define NIN 139
extern uint64_t *lde_intt8_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_twist_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l0_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l1_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l2_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l3_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *lde_ntt32_l4_rc(uint64_t *out, const uint64_t *inp);

/* ---------------- base field ---------------- */
static inline uint64_t fadd(uint64_t a, uint64_t b) { uint64_t s = a + b; return s >= P ? s - P : s; }
static inline uint64_t fsub(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P - b; }
static inline uint64_t fmul(uint64_t a, uint64_t b) { return (a * b) % P; }
static uint64_t fpow(uint64_t b, uint64_t e) {
  uint64_t r = 1; b %= P;
  while (e) { if (e & 1) r = fmul(r, b); b = fmul(b, b); e >>= 1; }
  return r;
}
static uint64_t finv(uint64_t a) { return fpow(a, P - 2); }
/* monty form for serde: x * 2^32 mod p (2^32 mod p = 268435454) */
static inline uint32_t monty(uint64_t x) { return (uint32_t)fmul(x % P, 268435454ULL); }

static uint64_t bitrev(uint64_t i, int bits) {
  uint64_t r = 0;
  for (int k = 0; k < bits; k++) { r = (r << 1) | (i & 1); i >>= 1; }
  return r;
}

/* ---------------- degree-4 binomial extension (x^4 = 11) ---------------- */
typedef struct { uint64_t c[4]; } E;

static E ezero(void) { E r = {{0,0,0,0}}; return r; }
static E ebase(uint64_t x) { E r = {{x % P,0,0,0}}; return r; }
static E eadd(E a, E b) { E r; for (int i = 0; i < 4; i++) r.c[i] = fadd(a.c[i], b.c[i]); return r; }
static E esub(E a, E b) { E r; for (int i = 0; i < 4; i++) r.c[i] = fsub(a.c[i], b.c[i]); return r; }
static E escale(E a, uint64_t s) { E r; for (int i = 0; i < 4; i++) r.c[i] = fmul(a.c[i], s); return r; }
static E emul(E a, E b) {
  E r;
  r.c[0] = fadd(fmul(a.c[0], b.c[0]),
                fmul(EXT_W, fadd(fadd(fmul(a.c[1], b.c[3]), fmul(a.c[2], b.c[2])), fmul(a.c[3], b.c[1]))));
  r.c[1] = fadd(fadd(fmul(a.c[0], b.c[1]), fmul(a.c[1], b.c[0])),
                fmul(EXT_W, fadd(fmul(a.c[2], b.c[3]), fmul(a.c[3], b.c[2]))));
  r.c[2] = fadd(fadd(fadd(fmul(a.c[0], b.c[2]), fmul(a.c[1], b.c[1])), fmul(a.c[2], b.c[0])),
                fmul(EXT_W, fmul(a.c[3], b.c[3])));
  r.c[3] = fadd(fadd(fadd(fmul(a.c[0], b.c[3]), fmul(a.c[1], b.c[2])), fmul(a.c[2], b.c[1])), fmul(a.c[3], b.c[0]));
  return r;
}
/* Frobenius x -> x^p: coeff i scaled by W^{i(p-1)/4} */
static E efrob(E a) {
  static uint64_t f1 = 0;
  if (!f1) f1 = fpow(EXT_W, (P - 1) / 4);
  E r; uint64_t s = 1;
  for (int i = 0; i < 4; i++) { r.c[i] = fmul(a.c[i], s); s = fmul(s, f1); }
  return r;
}
static E einv(E a) {
  E b = efrob(a), c = efrob(b), d = efrob(c);
  E t = emul(b, emul(c, d));
  E n = emul(a, t); /* norm: must be base */
  if (n.c[1] | n.c[2] | n.c[3]) { fprintf(stderr, "einv: norm not in base field!\n"); exit(1); }
  return escale(t, finv(n.c[0]));
}
static E epow2(E a, int k) { for (int i = 0; i < k; i++) a = emul(a, a); return a; } /* a^(2^k) */

static void eprint(const char *pre, E x, const char *post) {
  printf("%s[%llu, %llu, %llu, %llu]%s", pre,
         (unsigned long long)x.c[0], (unsigned long long)x.c[1],
         (unsigned long long)x.c[2], (unsigned long long)x.c[3], post);
}

/* ---------------- NTT (natural order; row i = p(omega^i)) ---------------- */
static void ntt(uint64_t *io, int n, uint64_t omega) {
  int logN = 0;
  while ((1 << logN) < n) logN++;
  uint64_t a[64];
  for (int i = 0; i < n; i++) a[i] = io[bitrev(i, logN)];
  for (int layer = 0; layer < logN; layer++) {
    int size = 1 << (layer + 1), half = size / 2;
    uint64_t wsize = fpow(omega, (uint64_t)(n / size));
    for (int blk = 0; blk < n; blk += size) {
      uint64_t w = 1;
      for (int pos = 0; pos < half; pos++) {
        uint64_t lo = a[blk + pos], t = fmul(w, a[blk + pos + half]);
        a[blk + pos] = fadd(lo, t);
        a[blk + pos + half] = fsub(lo, t);
        w = fmul(w, wsize);
      }
    }
  }
  for (int i = 0; i < n; i++) io[i] = a[i];
}
static void intt(uint64_t *io, int n, uint64_t omega) {
  ntt(io, n, finv(omega));
  uint64_t ni = finv((uint64_t)n);
  for (int i = 0; i < n; i++) io[i] = fmul(io[i], ni);
}

/* ---- column LDE through the EMITTED A3 leaves (input-vector wiring as in
 *      lde_column_from_rustcmd_kat.c / bench_prove_emitted.c) ---- */
static void fill_intt_inp(uint64_t inp[NIN], const uint64_t col[8]) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  for (int i = 0; i < 8; i++) inp[i] = col[bitrev(i, 3)];
  uint64_t oH = finv(TAG3);
  int t = 8;
  for (int b = 0; b < 4; b++) inp[t++] = 1; /* (oH^4)^0 */
  { uint64_t wS = fmul(oH, oH);
    inp[t++] = 1; inp[t++] = wS; inp[t++] = 1; inp[t++] = wS; }
  { for (int j = 0; j < 4; j++) inp[t++] = fpow(oH, (uint64_t)j); }
  inp[132] = finv(8);
}
/* The twist leaf does zero-pad + per-coefficient multiply + bitrev framing.
 * The multipliers are leaf INPUTS: g^i for the trace LDE (domain shift 1),
 * all-ones for the quotient LDE (domain shift already g => no twist). */
static void fill_twist_inp(uint64_t inp[NIN], const uint64_t bufv[32], int with_twist) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  for (int i = 0; i < 32; i++) inp[i] = bufv[i];
  for (int i = 0; i < 32; i++) inp[100 + i] = with_twist ? fpow(GEN, (uint64_t)i) : 1;
}
static void fill_ntt_inp(uint64_t inp[NIN], const uint64_t bufv[32], int layer) {
  memset(inp, 0, NIN * sizeof(uint64_t));
  for (int i = 0; i < 32; i++) inp[i] = bufv[i];
  int size = 1 << (layer + 1);
  uint64_t wSize = fpow(TAG5, (uint64_t)(32 / size));
  for (int j = 0; j < 16; j++) inp[100 + j] = fpow(wSize, (uint64_t)j);
}
/* with_twist=1: trace LDE (domain shift 1, coset twist by g);
 * with_twist=0: quotient LDE (domain shift already g, no twist). */
static void emitted_column_lde(uint64_t out[32], const uint64_t col[8], int with_twist) {
  uint64_t inp[NIN], bufv[32];
  fill_intt_inp(inp, col);
  lde_intt8_rc(bufv, inp); /* bufv[0..7] = coeffs; bufv[8..31] junk (twist leaf zero-pads) */
  fill_twist_inp(inp, bufv, with_twist);
  lde_twist_rc(bufv, inp); /* zero-pad + multiply + bitrev framing */
  fill_ntt_inp(inp, bufv, 0); lde_ntt32_l0_rc(bufv, inp);
  fill_ntt_inp(inp, bufv, 1); lde_ntt32_l1_rc(bufv, inp);
  fill_ntt_inp(inp, bufv, 2); lde_ntt32_l2_rc(bufv, inp);
  fill_ntt_inp(inp, bufv, 3); lde_ntt32_l3_rc(bufv, inp);
  fill_ntt_inp(inp, bufv, 4); lde_ntt32_l4_rc(bufv, inp);
  memcpy(out, bufv, 32 * sizeof(uint64_t));
}

/* ---------------- Poseidon2 constructions over the emitted leaf ---------- */
/* PaddingFreeSponge<16,8,8> on a row of len<=8 (one block) */
static void sponge_row(uint64_t out[8], const uint64_t *row, int len) {
  uint64_t st[16] = {0}, po[16];
  for (int i = 0; i < len; i++) st[i] = row[i] % P;
  hp_perm16(po, st);
  memcpy(out, po, 8 * sizeof(uint64_t));
}
/* TruncatedPermutation<2,8,16> */
static void compress2(uint64_t out[8], const uint64_t l[8], const uint64_t r[8]) {
  uint64_t st[16], po[16];
  memcpy(st, l, 8 * sizeof(uint64_t));
  memcpy(st + 8, r, 8 * sizeof(uint64_t));
  hp_perm16(po, st);
  memcpy(out, po, 8 * sizeof(uint64_t));
}

/* binary Merkle tree, up to 32 leaves; lev[k][i][8], lev0 = leaf digests */
typedef struct { uint64_t lev[6][32][8]; int n; int logn; } Tree;

static void tree_build(Tree *t, int n, const uint64_t *rows, int width) {
  t->n = n;
  t->logn = 0;
  while ((1 << t->logn) < n) t->logn++;
  for (int r = 0; r < n; r++) sponge_row(t->lev[0][r], rows + (size_t)r * width, width);
  for (int k = 0; k < t->logn; k++)
    for (int i = 0; i < (n >> (k + 1)); i++)
      compress2(t->lev[k + 1][i], t->lev[k][2 * i], t->lev[k][2 * i + 1]);
}
/* path: sibling digests from leaf level up (logn entries) */
static void tree_path(const Tree *t, int idx, uint64_t path[][8]) {
  for (int k = 0; k < t->logn; k++) {
    memcpy(path[k], t->lev[k][(idx >> k) ^ 1], 8 * sizeof(uint64_t));
  }
}

/* ---------------- DuplexChallenger<BabyBear, Perm16, 16, 8> -------------- */
typedef struct {
  uint64_t st[16];
  uint64_t inbuf[8]; int inlen;
  uint64_t outbuf[8]; int outlen; /* outbuf[0..outlen), pop from the END */
} Chal;

static void ch_init(Chal *c) { memset(c, 0, sizeof(*c)); }
static void ch_duplex(Chal *c) {
  for (int i = 0; i < c->inlen; i++) c->st[i] = c->inbuf[i];
  c->inlen = 0;
  uint64_t po[16];
  hp_perm16(po, c->st);
  memcpy(c->st, po, sizeof(po));
  memcpy(c->outbuf, c->st, 8 * sizeof(uint64_t));
  c->outlen = 8;
}
static void ch_observe(Chal *c, uint64_t v) {
  c->outlen = 0;
  c->inbuf[c->inlen++] = v % P;
  if (c->inlen == 8) ch_duplex(c);
}
static void ch_observe8(Chal *c, const uint64_t d[8]) { for (int i = 0; i < 8; i++) ch_observe(c, d[i]); }
static uint64_t ch_sample(Chal *c) {
  if (c->inlen > 0 || c->outlen == 0) ch_duplex(c);
  return c->outbuf[--c->outlen];
}
static E ch_sample_ext(Chal *c) {
  E r;
  for (int i = 0; i < 4; i++) r.c[i] = ch_sample(c);
  return r;
}
static uint64_t ch_sample_bits5(Chal *c) { return ch_sample(c) & 31; }

/* ---------------- bincode writer ---------------- */
static uint8_t buf[8192];
static size_t blen = 0;
static void w_u8(uint8_t v) { buf[blen++] = v; }
static void w_u32(uint32_t v) { for (int i = 0; i < 4; i++) buf[blen++] = (v >> (8 * i)) & 0xff; }
static void w_u64(uint64_t v) { for (int i = 0; i < 8; i++) buf[blen++] = (v >> (8 * i)) & 0xff; }
static void w_fe(uint64_t x) { w_u32(monty(x)); }
static void w_ext(E x) { for (int i = 0; i < 4; i++) w_fe(x.c[i]); }
static void w_digest(const uint64_t d[8]) { for (int i = 0; i < 8; i++) w_fe(d[i]); }

/* ---------------- the prover ---------------- */
int main(void) {
  /* sanity: extension inverse */
  { E a = {{123456789, 7, 42, 1999999}}; E ai = einv(a); E one = emul(a, ai);
    if (one.c[0] != 1 || one.c[1] || one.c[2] || one.c[3]) { fprintf(stderr, "einv self-test FAILED\n"); return 1; } }

  /* trace: Fibonacci 8 x 2, pis = [0, 1, 21] */
  uint64_t trace[8][2];
  trace[0][0] = 0; trace[0][1] = 1;
  for (int i = 1; i < 8; i++) { trace[i][0] = trace[i - 1][1]; trace[i][1] = fadd(trace[i - 1][0], trace[i - 1][1]); }
  const uint64_t pv_a = 0, pv_b = 1, pv_x = 21;

  /* ---- phase 1: trace LDE (8 -> 32 on the coset g*K) + Merkle commit.
   * Per column through the EMITTED A3 leaves; cross-checked against the
   * plain-C reference (must agree exactly). ---- */
  uint64_t lde[32][2];
  for (int col = 0; col < 2; col++) {
    uint64_t colv[8], v[32], vref[32];
    for (int r = 0; r < 8; r++) colv[r] = trace[r][col];
    emitted_column_lde(v, colv, 1);
    /* reference: intt8 + coset twist by g + ntt32 */
    for (int r = 0; r < 8; r++) vref[r] = colv[r];
    intt(vref, 8, TAG3);
    { uint64_t w = 1;
      for (int j = 0; j < 8; j++) { vref[j] = fmul(vref[j], w); w = fmul(w, GEN); } }
    for (int j = 8; j < 32; j++) vref[j] = 0;
    ntt(vref, 32, TAG5);
    if (memcmp(v, vref, sizeof(v))) { fprintf(stderr, "emitted trace LDE != C reference (col %d)\n", col); return 1; }
    for (int r = 0; r < 32; r++) lde[r][col] = v[r];
  }
  printf("trace_lde (natural order over gK, 32 rows x 2 cols, canonical):\n");
  for (int r = 0; r < 32; r++)
    printf("  lde[%d] = [%llu, %llu]\n", r, (unsigned long long)lde[r][0], (unsigned long long)lde[r][1]);

  /* committed matrix = bit-reversed rows */
  uint64_t ctrace[32][2];
  for (int r = 0; r < 32; r++) { int s = (int)bitrev(r, 5); ctrace[r][0] = lde[s][0]; ctrace[r][1] = lde[s][1]; }
  Tree ttrace;
  tree_build(&ttrace, 32, &ctrace[0][0], 2);
  const uint64_t *trace_root = ttrace.lev[5][0];
  printf("trace_commit = [%llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu]\n",
         (unsigned long long)trace_root[0], (unsigned long long)trace_root[1],
         (unsigned long long)trace_root[2], (unsigned long long)trace_root[3],
         (unsigned long long)trace_root[4], (unsigned long long)trace_root[5],
         (unsigned long long)trace_root[6], (unsigned long long)trace_root[7]);

  /* ---- Fiat-Shamir: observe instance + trace commit + public values ---- */
  Chal ch;
  ch_init(&ch);
  ch_observe(&ch, 3); /* log_ext_degree */
  ch_observe(&ch, 3); /* log_degree */
  ch_observe(&ch, 0); /* preprocessed_width */
  ch_observe8(&ch, trace_root);
  ch_observe(&ch, pv_a); ch_observe(&ch, pv_b); ch_observe(&ch, pv_x);
  E alpha = ch_sample_ext(&ch);
  eprint("alpha = ", alpha, "\n");

  /* ---- phase 2: quotient values on the disjoint coset gH (size 8) ---- */
  /* selectors_on_coset(trace domain H, coset gH) */
  uint64_t h = TAG3, h_last = fpow(TAG3, 7); /* h^{-1} = h^7 */
  uint64_t zh = fsub(fpow(GEN, 8), 1);       /* Z_H on the coset is constant */
  uint64_t inv_van = finv(zh);
  uint64_t sel_first[8], sel_last[8], sel_trans[8], xs[8];
  for (int j = 0; j < 8; j++) {
    xs[j] = fmul(GEN, fpow(h, (uint64_t)j));
    sel_first[j] = fmul(zh, finv(fsub(xs[j], 1)));
    sel_last[j] = fmul(zh, finv(fsub(xs[j], h_last)));
    sel_trans[j] = fsub(xs[j], h_last);
  }
  printf("selectors (canonical):\n");
  for (int j = 0; j < 8; j++)
    printf("  i=%d first=%llu last=%llu trans=%llu invvan=%llu\n", j,
           (unsigned long long)sel_first[j], (unsigned long long)sel_last[j],
           (unsigned long long)sel_trans[j], (unsigned long long)inv_van);

  /* trace on the quotient domain (natural order) = every 4th natural-LDE row */
  uint64_t tq[8][2];
  for (int j = 0; j < 8; j++) { tq[j][0] = lde[4 * j][0]; tq[j][1] = lde[4 * j][1]; }

  /* alpha powers, descending: constraint i (of 5) weighted alpha^{4-i} */
  E apow[5];
  apow[0] = ebase(1);
  for (int i = 1; i < 5; i++) apow[i] = emul(apow[i - 1], alpha);

  E qvals[8];
  for (int i = 0; i < 8; i++) {
    const uint64_t *local = tq[i], *next = tq[(i + 1) & 7];
    uint64_t cons[5];
    cons[0] = fmul(sel_first[i], fsub(local[0], pv_a));
    cons[1] = fmul(sel_first[i], fsub(local[1], pv_b));
    cons[2] = fmul(sel_trans[i], fsub(local[1], next[0]));
    cons[3] = fmul(sel_trans[i], fsub(fadd(local[0], local[1]), next[1]));
    cons[4] = fmul(sel_last[i], fsub(local[1], pv_x));
    E folded = ezero();
    for (int k = 0; k < 5; k++) folded = eadd(folded, escale(apow[4 - k], cons[k]));
    qvals[i] = escale(folded, inv_van);
  }
  printf("quotient_values (8 ext elts, canonical coeffs):\n");
  for (int i = 0; i < 8; i++) { printf("  q[%d] = ", i); eprint("", qvals[i], "\n"); }

  /* flatten to 8x4 base, LDE each column onto gK (domain shift g => no twist),
   * through the EMITTED A3 leaves (twist powers fed as 1), cross-checked. */
  uint64_t qlde[32][4];
  for (int col = 0; col < 4; col++) {
    uint64_t colv[8], v[32], vref[32];
    for (int r = 0; r < 8; r++) colv[r] = qvals[r].c[col];
    emitted_column_lde(v, colv, 0);
    for (int r = 0; r < 8; r++) vref[r] = colv[r];
    intt(vref, 8, TAG3);
    for (int j = 8; j < 32; j++) vref[j] = 0;
    ntt(vref, 32, TAG5);
    if (memcmp(v, vref, sizeof(v))) { fprintf(stderr, "emitted quotient LDE != C reference (col %d)\n", col); return 1; }
    for (int r = 0; r < 32; r++) qlde[r][col] = v[r];
  }
  uint64_t cq[32][4];
  for (int r = 0; r < 32; r++) { int s = (int)bitrev(r, 5); for (int k = 0; k < 4; k++) cq[r][k] = qlde[s][k]; }
  Tree tq_tree;
  tree_build(&tq_tree, 32, &cq[0][0], 4);
  const uint64_t *q_root = tq_tree.lev[5][0];
  printf("quotient_commit = [%llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu]\n",
         (unsigned long long)q_root[0], (unsigned long long)q_root[1],
         (unsigned long long)q_root[2], (unsigned long long)q_root[3],
         (unsigned long long)q_root[4], (unsigned long long)q_root[5],
         (unsigned long long)q_root[6], (unsigned long long)q_root[7]);

  ch_observe8(&ch, q_root);
  E zeta = ch_sample_ext(&ch);
  E zeta_next = escale(zeta, TAG3); /* next_point = * subgroup generator */
  eprint("zeta = ", zeta, "\n");
  eprint("zeta_next = ", zeta_next, "\n");

  /* ---- phase 3: open() — barycentric OOD evaluations ---- */
  /* bit-reversed coset points of gK */
  uint64_t pts[32];
  for (int r = 0; r < 32; r++) pts[r] = fmul(GEN, fpow(TAG5, bitrev(r, 5)));
  E invd_z[32], invd_zn[32];
  for (int r = 0; r < 32; r++) {
    invd_z[r] = einv(esub(zeta, ebase(pts[r])));
    invd_zn[r] = einv(esub(zeta_next, ebase(pts[r])));
  }
  /* scale = (z^8 - g^8) / (8 * g^8) */
  uint64_t g8 = fpow(GEN, 8), inv_8g8 = finv(fmul(8, g8));
  E scale_z = escale(esub(epow2(zeta, 3), ebase(g8)), inv_8g8);
  E scale_zn = escale(esub(epow2(zeta_next, 3), ebase(g8)), inv_8g8);

  /* ys = scale * sum_r pts[r]*invd[r]*M[r][j], over the first 8 bitrev rows */
  E ys_t_z[2], ys_t_zn[2], ys_q_z[4];
  for (int j = 0; j < 2; j++) {
    E acc_z = ezero(), acc_zn = ezero();
    for (int r = 0; r < 8; r++) {
      acc_z = eadd(acc_z, escale(invd_z[r], fmul(pts[r], ctrace[r][j])));
      acc_zn = eadd(acc_zn, escale(invd_zn[r], fmul(pts[r], ctrace[r][j])));
    }
    ys_t_z[j] = emul(scale_z, acc_z);
    ys_t_zn[j] = emul(scale_zn, acc_zn);
  }
  for (int j = 0; j < 4; j++) {
    E acc = ezero();
    for (int r = 0; r < 8; r++) acc = eadd(acc, escale(invd_z[r], fmul(pts[r], cq[r][j])));
    ys_q_z[j] = emul(scale_z, acc);
  }
  printf("opened trace_local  = [");
  eprint("", ys_t_z[0], ", "); eprint("", ys_t_z[1], "]\n");
  printf("opened trace_next   = [");
  eprint("", ys_t_zn[0], ", "); eprint("", ys_t_zn[1], "]\n");
  printf("opened quotient_chunks[0] = [");
  eprint("", ys_q_z[0], ", "); eprint("", ys_q_z[1], ", ");
  eprint("", ys_q_z[2], ", "); eprint("", ys_q_z[3], "]\n");

  /* observe openings in prove order, then sample the FRI batching alpha */
  for (int j = 0; j < 2; j++) for (int i = 0; i < 4; i++) ch_observe(&ch, ys_t_z[j].c[i]);
  for (int j = 0; j < 2; j++) for (int i = 0; i < 4; i++) ch_observe(&ch, ys_t_zn[j].c[i]);
  for (int j = 0; j < 4; j++) for (int i = 0; i < 4; i++) ch_observe(&ch, ys_q_z[j].c[i]);
  E fa = ch_sample_ext(&ch);
  eprint("fri_alpha = ", fa, "\n");
  E fa2 = emul(fa, fa), fa3 = emul(fa2, fa), fa4 = emul(fa2, fa2);

  /* reduced openings over the 32 bitrev rows */
  E reduced[32];
  E ro_t_z = eadd(ys_t_z[0], emul(fa, ys_t_z[1]));
  E ro_t_zn = eadd(ys_t_zn[0], emul(fa, ys_t_zn[1]));
  E ro_q_z = eadd(eadd(ys_q_z[0], emul(fa, ys_q_z[1])), eadd(emul(fa2, ys_q_z[2]), emul(fa3, ys_q_z[3])));
  for (int r = 0; r < 32; r++) {
    E mt = eadd(ebase(ctrace[r][0]), escale(fa, ctrace[r][1]));
    E mq = eadd(eadd(ebase(cq[r][0]), escale(fa, cq[r][1])), eadd(escale(fa2, cq[r][2]), escale(fa3, cq[r][3])));
    E acc = emul(esub(ro_t_z, mt), invd_z[r]);
    acc = eadd(acc, emul(fa2, emul(esub(ro_t_zn, mt), invd_zn[r])));
    acc = eadd(acc, emul(fa4, emul(esub(ro_q_z, mq), invd_z[r])));
    reduced[r] = acc;
  }

  /* ---- phase 4: FRI commit phase (one arity-2 round) ---- */
  /* commit the 16x2-ext matrix as 16x8 base rows */
  uint64_t frirows[16][8];
  for (int r = 0; r < 16; r++)
    for (int k = 0; k < 4; k++) { frirows[r][k] = reduced[2 * r].c[k]; frirows[r][4 + k] = reduced[2 * r + 1].c[k]; }
  Tree tfri;
  tree_build(&tfri, 16, &frirows[0][0], 8);
  const uint64_t *fri_root = tfri.lev[4][0];
  printf("fri commit_phase_commit[0] = [%llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu]\n",
         (unsigned long long)fri_root[0], (unsigned long long)fri_root[1],
         (unsigned long long)fri_root[2], (unsigned long long)fri_root[3],
         (unsigned long long)fri_root[4], (unsigned long long)fri_root[5],
         (unsigned long long)fri_root[6], (unsigned long long)fri_root[7]);
  ch_observe8(&ch, fri_root);
  /* grind(0) = no transcript effect, witness ZERO */
  E beta = ch_sample_ext(&ch);
  eprint("fri beta = ", beta, "\n");

  /* fold: folded'[r] = (lo+hi)/2 + (lo-hi)*beta*(g^{-r_bitrev}/2) */
  uint64_t ginv = finv(TAG5), inv2 = finv(2);
  uint64_t hip[16];
  for (int i = 0; i < 16; i++) hip[i] = fmul(inv2, fpow(ginv, (uint64_t)i));
  /* bit-reverse hip (16 entries, 4 bits) */
  for (int i = 0; i < 16; i++) {
    int j = (int)bitrev(i, 4);
    if (j > i) { uint64_t t = hip[i]; hip[i] = hip[j]; hip[j] = t; }
  }
  E folded16[16];
  for (int r = 0; r < 16; r++) {
    E lo = reduced[2 * r], hi = reduced[2 * r + 1];
    folded16[r] = eadd(escale(eadd(lo, hi), inv2), escale(emul(esub(lo, hi), beta), hip[r]));
  }

  /* final poly: truncate to 4, un-bitrev, size-4 inverse DFT (omega = TAG2) */
  E fvals[4] = {folded16[0], folded16[2], folded16[1], folded16[3]}; /* bitrev2 swap of [1],[2] */
  E fp[4];
  uint64_t inv4 = finv(4), w4inv = finv(TAG2);
  for (int k = 0; k < 4; k++) {
    E acc = ezero();
    for (int i = 0; i < 4; i++) acc = eadd(acc, escale(fvals[i], fpow(w4inv, (uint64_t)((i * k) % 4))));
    fp[k] = escale(acc, inv4);
  }
  printf("fri final_poly:\n");
  for (int k = 0; k < 4; k++) { printf("  fp[%d] = ", k); eprint("", fp[k], "\n"); }
  for (int k = 0; k < 4; k++) for (int i = 0; i < 4; i++) ch_observe(&ch, fp[k].c[i]);

  ch_observe(&ch, 1); /* log_arity of the single round */
  /* query grind(0): no transcript effect, witness ZERO */

  uint64_t qidx[8];
  printf("fri query indices = [");
  for (int q = 0; q < 8; q++) { qidx[q] = ch_sample_bits5(&ch); printf("%llu%s", (unsigned long long)qidx[q], q < 7 ? ", " : "]\n"); }

  /* ---- phase 5: serialize Proof<SC> in bincode-1.x layout ---- */
  /* commitments */
  w_u64(1); w_digest(trace_root);
  w_u64(1); w_digest(q_root);
  w_u8(0); /* random: None */
  /* opened_values */
  w_u64(2); w_ext(ys_t_z[0]); w_ext(ys_t_z[1]);
  w_u8(1); w_u64(2); w_ext(ys_t_zn[0]); w_ext(ys_t_zn[1]);
  w_u8(0); w_u8(0); /* preprocessed local/next: None */
  w_u64(1); w_u64(4); for (int j = 0; j < 4; j++) w_ext(ys_q_z[j]);
  w_u8(0); /* random opened: None */
  /* opening_proof: FriProof */
  w_u64(1); w_u64(1); w_digest(fri_root); /* commit_phase_commits */
  w_u64(1); w_fe(0);                      /* commit_pow_witnesses = [ZERO] */
  w_u64(8);                               /* query_proofs */
  for (int q = 0; q < 8; q++) {
    int idx = (int)qidx[q];
    uint64_t path[5][8];
    /* input_proof: Vec of 2 BatchOpenings */
    w_u64(2);
    /* batch 1: trace tree */
    w_u64(1); w_u64(2); w_fe(ctrace[idx][0]); w_fe(ctrace[idx][1]);
    tree_path(&ttrace, idx, path);
    w_u64(5); for (int k = 0; k < 5; k++) w_digest(path[k]);
    /* batch 2: quotient tree */
    w_u64(1); w_u64(4); for (int k = 0; k < 4; k++) w_fe(cq[idx][k]);
    tree_path(&tq_tree, idx, path);
    w_u64(5); for (int k = 0; k < 5; k++) w_digest(path[k]);
    /* commit_phase_openings: 1 step */
    w_u64(1);
    w_u8(1); /* log_arity */
    int group = idx >> 1, pos = idx & 1;
    w_u64(1); w_ext(reduced[2 * group + (1 - pos)]); /* sibling value */
    tree_path(&tfri, group, path);
    w_u64(4); for (int k = 0; k < 4; k++) w_digest(path[k]);
  }
  w_u64(4); for (int k = 0; k < 4; k++) w_ext(fp[k]); /* final_poly */
  w_fe(0);                                            /* query_pow_witness = ZERO */
  w_u64(3);                                           /* degree_bits */

  FILE *f = fopen("p3_our_proof.bin", "wb");
  if (!f) { perror("p3_our_proof.bin"); return 1; }
  fwrite(buf, 1, blen, f);
  fclose(f);
  printf("wrote p3_our_proof.bin (%zu bytes)\n", blen);
  return 0;
}
