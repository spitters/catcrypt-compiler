/* External KAT + verifier for the emitted Plonky3 FRI PROOF OBJECT.
 *
 * The emitted prover
 *   plonky3_fri_prove_obj_rc(proof[546], evals[32], alpha[4], qidx[4])
 * (Tier A path: Lean spec -> RustCmd -> CryptoSSA -> Com[jasmin] ->
 *  gen_com/fri_proof_from_rustcmd_link.jazz, jasminc -> fri_proof_link.s)
 * produces a REAL structured FRI proof object matching plonky3-hax/src/fri.rs:
 * per-layer Merkle commitments, per-query openings (eval_pos/eval_neg +
 * Merkle authentication paths at the query indices), and the final-layer
 * remainder polynomial.
 *
 * This harness is the EXTERNAL KAT (the conform.c pattern): the emitted
 * binary's proof is checked by a verifier here. We:
 *   1. build a column LDE on the bare subgroup K_32 (a known low-degree poly),
 *   2. run the emitted prover to get the proof object,
 *   3. run fri_verify (spec-adherent to fri.rs::fri_verify) -> must ACCEPT,
 *   4. tamper with the proof (flip an eval / a path / the remainder) ->
 *      must REJECT (negative tests),
 *   5. report prove + verify cyc/op.
 *
 * The Merkle hash is the same u64-lane _p3_hleaf_u64 / _p3_compress_u64 the
 * emitted prover uses (the CatCrypt bridge axiomatizes it as a random oracle;
 * prover and verifier agree on the concrete mixing).
 *
 * FRI parameters: n=32 (domain_log2=5), num_layers=4, num_queries=3,
 * coset_shift=1.  After 4 folds the codeword has size 2 (remainder degree 1).
 *
 * Build: make plonky3-fri-proof-rustcmd-bench
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

extern uint64_t *plonky3_fri_prove_obj_rc(uint64_t *out, const uint64_t *evals,
                                           const uint64_t *alpha,
                                           const uint64_t *qidx);

#define BB_P 2013265921ULL
#define BB_G 31ULL

#define N0          32      /* layer-0 domain size */
#define DOMAIN_LOG2 5
#define NUM_LAYERS  4
#define NUM_QUERIES 3
#define COSET_SHIFT 1ULL

#define LANES       4
#define MAX_DEPTH   5        /* path padded to 5 sibling digests */
#define PATH_U64    (MAX_DEPTH * LANES)         /* 20 */
#define QUERY_U64   (4 + 2 * PATH_U64)          /* 44 */
#define LAYER_U64   (LANES + NUM_QUERIES * QUERY_U64)  /* 136 */
#define PROOF_U64   (NUM_LAYERS * LAYER_U64 + 2)        /* 546 */

/* ---------- BabyBear field (byte-identical to the .jinc) ---------- */
static inline uint64_t f_reduce(uint64_t x) {
  uint64_t t = x - BB_P;
  uint64_t m = ((int64_t)t < 0) ? BB_P : 0;
  return t + m;
}
static inline uint64_t f_add(uint64_t a, uint64_t b) { return f_reduce(a + b); }
static inline uint64_t f_sub(uint64_t a, uint64_t b) { return f_reduce((BB_P + a) - b); }
static inline uint64_t f_mul(uint64_t a, uint64_t b) { return (a * b) % BB_P; }
static uint64_t f_pow(uint64_t base, uint64_t exp) {
  uint64_t r = 1, c = base % BB_P;
  for (int it = 0; it < 64; it++) { if (exp & 1) r = f_mul(r, c); c = f_mul(c, c); exp >>= 1; }
  return r;
}
static uint64_t f_inv(uint64_t a) { return a == 0 ? 0 : f_pow(a, BB_P - 2); }
static uint64_t f_rou(int k) { return f_pow(BB_G, (BB_P - 1) >> k); }
/* p(x) = sum coeffs[i] x^i (fri.rs::bb_poly_eval, Horner) */
static uint64_t f_poly_eval(const uint64_t *coeffs, int n, uint64_t x) {
  uint64_t acc = 0;
  for (int i = n - 1; i >= 0; i--) acc = f_add(f_mul(acc, x), coeffs[i]);
  return acc;
}

/* fri.rs::fri_fold */
static uint64_t f_fri_fold(uint64_t ep, uint64_t en, uint64_t x, uint64_t alpha) {
  uint64_t sum = f_add(ep, en), diff = f_sub(ep, en);
  uint64_t inv2 = f_inv(2);
  uint64_t inv2x = f_inv(f_mul(2, x));
  uint64_t peven = f_mul(sum, inv2);
  uint64_t podd  = f_mul(diff, inv2x);
  return f_add(peven, f_mul(alpha, podd));
}
/* domain element omega^index on K_{2^domain_log2}; coset = shift * that */
static uint64_t f_domain_element(int domain_log2, uint64_t index) {
  return f_pow(f_rou(domain_log2), index);
}
static uint64_t f_coset_element(uint64_t shift, int domain_log2, uint64_t index) {
  return f_mul(shift, f_domain_element(domain_log2, index));
}
static uint64_t f_sibling_index(uint64_t index, int domain_log2) {
  uint64_t n = 1ULL << domain_log2;
  return (index + (n >> 1)) & (n - 1);
}
static uint64_t f_folded_index(uint64_t index, int domain_log2) {
  uint64_t half_n = 1ULL << (domain_log2 - 1);
  return index & (half_n - 1);
}

/* ---------- u64-lane Merkle hash (matches plonky3_merkle_leaves.jinc) ------- */
static void p3_hleaf(uint64_t o[4], uint64_t v) {
  uint64_t t, prev;
  for (int i = 0; i < 4; i++) {
    t = v; t *= 0x9E3779B97F4A7C15ULL; t += (uint64_t)i;
    t *= 0xBF58476D1CE4E5B9ULL; o[i] = t; v = t;
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

/* merkle_verify_path (merkle.rs): recompute root from leaf + siblings.
 * siblings[level] is a 4-lane digest. depth levels. */
static int merkle_verify_path(const uint64_t root[4], const uint64_t leaf[4],
                              uint64_t index, const uint64_t *siblings, int depth) {
  uint64_t cur[4]; memcpy(cur, leaf, sizeof cur);
  uint64_t idx = index;
  for (int level = 0; level < depth; level++) {
    const uint64_t *sib = siblings + level * 4;
    uint64_t nxt[4];
    if ((idx & 1) == 0) p3_compress(nxt, cur, sib);
    else                p3_compress(nxt, sib, cur);
    memcpy(cur, nxt, sizeof cur);
    idx >>= 1;
  }
  return memcmp(cur, root, sizeof cur) == 0;
}

/* ---------- proof-buffer accessors ---------- */
static const uint64_t *layer_commitment(const uint64_t *p, int L) { return p + L * LAYER_U64; }
static const uint64_t *query_base(const uint64_t *p, int L, int q) {
  return p + L * LAYER_U64 + LANES + q * QUERY_U64;
}
static const uint64_t *proof_remainder(const uint64_t *p) { return p + NUM_LAYERS * LAYER_U64; }

/* depth (Merkle tree height) of a layer of size n = N0 >> L. */
static int layer_depth(int L) {
  int n = N0 >> L, d = 0;
  while (n > 1) { n >>= 1; d++; }
  return d;
}

/* fri_verify (spec-adherent to fri.rs::fri_verify), single column,
 * coset_shift = COSET_SHIFT. alphas[L] = layer challenge. */
static int fri_verify(const uint64_t *proof, const uint64_t *alphas) {
  int cur_log2 = DOMAIN_LOG2;
  uint64_t cur_shift = COSET_SHIFT;

  for (int L = 0; L < NUM_LAYERS; L++) {
    const uint64_t *commit = layer_commitment(proof, L);
    uint64_t alpha = alphas[L];
    int depth = layer_depth(L);

    /* next-layer claimed evals at each query */
    uint64_t next_evals[NUM_QUERIES];
    if (L + 1 < NUM_LAYERS) {
      for (int q = 0; q < NUM_QUERIES; q++)
        next_evals[q] = query_base(proof, L + 1, q)[0];   /* eval_pos */
    } else {
      /* final layer: remainder poly evaluated at x^2 on the next coset */
      const uint64_t *rem = proof_remainder(proof);
      int next_log2 = cur_log2 - 1;
      uint64_t next_shift = f_mul(cur_shift, cur_shift);
      for (int q = 0; q < NUM_QUERIES; q++) {
        uint64_t ipos = query_base(proof, L, q)[2];
        uint64_t xi = f_folded_index(ipos, cur_log2);
        uint64_t x2 = f_coset_element(next_shift, next_log2, xi);
        next_evals[q] = f_poly_eval(rem, 2, x2);
      }
    }

    for (int q = 0; q < NUM_QUERIES; q++) {
      const uint64_t *qb = query_base(proof, L, q);
      uint64_t eval_pos = qb[0], eval_neg = qb[1];
      uint64_t ipos = qb[2], ineg = qb[3];
      const uint64_t *path_pos = qb + 4;
      const uint64_t *path_neg = qb + 4 + PATH_U64;

      uint64_t leaf_pos[4], leaf_neg[4];
      p3_hleaf(leaf_pos, eval_pos);
      p3_hleaf(leaf_neg, eval_neg);

      /* 1+2: Merkle paths */
      if (!merkle_verify_path(commit, leaf_pos, ipos, path_pos, depth)) return 0;
      if (!merkle_verify_path(commit, leaf_neg, ineg, path_neg, depth)) return 0;
      /* 3: sibling index */
      if (ineg != f_sibling_index(ipos, cur_log2)) return 0;
      /* 4: folding relation vs next layer */
      uint64_t x = f_coset_element(cur_shift, cur_log2, ipos);
      uint64_t folded = f_fri_fold(eval_pos, eval_neg, x, alpha);
      if (folded != next_evals[q]) return 0;
    }

    cur_log2 -= 1;
    cur_shift = f_mul(cur_shift, cur_shift);
  }

  /* remainder degree bound: degree-1 remainder, both coeffs allowed */
  return 1;
}

/* ---------- build a known low-degree column LDE on K_32 ---------- */
/* poly p(x) = 7 + 3x + 5x^2 + 2x^3 (degree 3 << 32/blowup -> low degree).
 * evals[i] = p(omega^i), omega = bb_root_of_unity(5). The fold chain of a
 * genuinely low-degree codeword lands on a degree-<=1 remainder -> verify. */
static void build_column_lde(uint64_t evals[32], const uint64_t coeffs[4]) {
  uint64_t omega = f_rou(DOMAIN_LOG2);
  uint64_t x = 1;
  for (int i = 0; i < 32; i++) {
    evals[i] = f_poly_eval(coeffs, 4, x);
    x = f_mul(x, omega);
  }
}

/* ---------- independent C reference prover (GOLDEN-KAT oracle) ----------
 * Builds the SAME flat FRI proof object as the emitted leaf, directly from
 * the fri.rs recipe (fri_prove_column), so the emit is validated against a
 * second independent implementation — not merely self-consistent with the
 * verifier. */
static void ref_build_leaf_hashes(uint64_t leaves[128], const uint64_t *cur, int n) {
  for (int i = 0; i < n; i++) p3_hleaf(&leaves[i * 4], cur[i]);
}
static void ref_merkle_root(uint64_t root[4], const uint64_t leaves[128], int n) {
  uint64_t a[128], b[128];
  memcpy(a, leaves, sizeof(uint64_t) * 4 * n);
  int pairs = n;
  while (pairs > 1) {
    for (int j = 0; j < pairs / 2; j++) p3_compress(&b[j * 4], &a[(2 * j) * 4], &a[(2 * j + 1) * 4]);
    memcpy(a, b, sizeof(uint64_t) * 4 * (pairs / 2));
    pairs /= 2;
  }
  memcpy(root, a, sizeof(uint64_t) * 4);
}
static void ref_merkle_path(uint64_t out_path[PATH_U64], const uint64_t leaves[128],
                            int n, uint64_t leaf_index) {
  uint64_t a[128], b[128];
  memcpy(a, leaves, sizeof(uint64_t) * 4 * n);
  int pairs = n, level = 0;
  uint64_t x = leaf_index;
  for (int i = 0; i < PATH_U64; i++) out_path[i] = 0;
  while (pairs > 1) {
    uint64_t sib = x ^ 1;
    memcpy(&out_path[level * 4], &a[sib * 4], sizeof(uint64_t) * 4);
    for (int j = 0; j < pairs / 2; j++) p3_compress(&b[j * 4], &a[(2 * j) * 4], &a[(2 * j + 1) * 4]);
    memcpy(a, b, sizeof(uint64_t) * 4 * (pairs / 2));
    pairs /= 2; x >>= 1; level++;
  }
}
static void ref_fri_prove_obj(uint64_t proof[PROOF_U64], const uint64_t evals[32],
                              const uint64_t alpha[4], const uint64_t qidx[4]) {
  uint64_t cur[32];
  memcpy(cur, evals, sizeof cur);
  for (int L = 0; L < NUM_LAYERS; L++) {
    int n = N0 >> L, half = n / 2, log = DOMAIN_LOG2 - L;
    int lbase = L * LAYER_U64;
    uint64_t leaves[128];
    ref_build_leaf_hashes(leaves, cur, n);
    ref_merkle_root(&proof[lbase], leaves, n);     /* commitment */
    for (int q = 0; q < NUM_QUERIES; q++) {
      int qb = lbase + LANES + q * QUERY_U64;
      uint64_t ipos = qidx[q] & (uint64_t)(n - 1);
      uint64_t ineg = (ipos + half) & (uint64_t)(n - 1);
      proof[qb + 0] = cur[ipos];
      proof[qb + 1] = cur[ineg];
      proof[qb + 2] = ipos;
      proof[qb + 3] = ineg;
      ref_merkle_path(&proof[qb + 4], leaves, n, ipos);
      ref_merkle_path(&proof[qb + 4 + PATH_U64], leaves, n, ineg);
    }
    /* fold using REAL fri_fold, x_i = omega_layer^i, omega_layer = rou(log) */
    uint64_t ol = f_rou(log), xpow = 1;
    uint64_t a = alpha[L];
    uint64_t next[32];
    for (int i = 0; i < half; i++) {
      next[i] = f_fri_fold(cur[i], cur[i + half], xpow, a);
      xpow = f_mul(xpow, ol);
    }
    memcpy(cur, next, sizeof(uint64_t) * half);
  }
  /* remainder of size 2 on K_1: [(e0+e1)/2, (e0-e1)/2] */
  uint64_t inv2 = f_inv(2);
  proof[NUM_LAYERS * LAYER_U64 + 0] = f_mul(f_add(cur[0], cur[1]), inv2);
  proof[NUM_LAYERS * LAYER_U64 + 1] = f_mul(f_sub(cur[0], cur[1]), inv2);
}

/* ---------- rdtsc ---------- */
static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}
#define ITERS 5000

int main(void) {
  uint64_t coeffs[4] = {7, 3, 5, 2};
  uint64_t evals[32];
  build_column_lde(evals, coeffs);

  /* FS-style layer challenges (fixed for KAT; the prover takes them as input
   * exactly as fri.rs::fri_prove_column takes `alphas`). */
  uint64_t alpha[4] = {101, 202, 303, 404};
  uint64_t qidx[4]  = {3, 11, 26, 0};   /* 3 query indices (4th unused) */

  uint64_t proof[PROOF_U64];
  plonky3_fri_prove_obj_rc(proof, evals, alpha, qidx);

  /* GOLDEN-KAT: emitted proof object vs independent C reference prover
   * (fri.rs::fri_prove_column recipe) — byte-for-byte over the full 546 u64. */
  uint64_t ref_proof[PROOF_U64];
  ref_fri_prove_obj(ref_proof, evals, alpha, qidx);
  int golden_ok = (memcmp(proof, ref_proof, sizeof proof) == 0);

  printf("Plonky3 FRI PROOF-OBJECT external KAT (emit -> verifier):\n");
  printf("  params: n=%d, domain_log2=%d, layers=%d, queries=%d, shift=%llu\n",
         N0, DOMAIN_LOG2, NUM_LAYERS, NUM_QUERIES, (unsigned long long)COSET_SHIFT);
  printf("  proof object: %d u64 (%d layers x %d + 2 remainder)\n",
         PROOF_U64, NUM_LAYERS, LAYER_U64);

  /* per-layer commitments */
  for (int L = 0; L < NUM_LAYERS; L++) {
    const uint64_t *c = layer_commitment(proof, L);
    printf("  layer %d commitment: %016llx %016llx %016llx %016llx\n", L,
           (unsigned long long)c[0], (unsigned long long)c[1],
           (unsigned long long)c[2], (unsigned long long)c[3]);
  }
  const uint64_t *rem = proof_remainder(proof);
  printf("  remainder coeffs: [%llu, %llu]\n",
         (unsigned long long)rem[0], (unsigned long long)rem[1]);

  int all_ok = 1;

  /* (0) GOLDEN: emit == independent reference prover (byte-for-byte) */
  printf("\n  [GOLDEN] emit proof == C reference prover (546 u64): %s\n",
         golden_ok ? "match" : "MISMATCH");
  if (!golden_ok) all_ok = 0;

  /* (1) ACCEPT the honest proof */
  int accept = fri_verify(proof, alpha);
  printf("\n  [ACCEPT] honest proof verifies: %s\n", accept ? "ACCEPT" : "REJECT");
  if (!accept) all_ok = 0;

  /* (2) negative: tamper an eval_pos -> must REJECT */
  {
    uint64_t bad[PROOF_U64]; memcpy(bad, proof, sizeof bad);
    uint64_t *qb = bad + 0 * LAYER_U64 + LANES + 0 * QUERY_U64;
    qb[0] = f_add(qb[0], 1);  /* corrupt layer0 query0 eval_pos */
    int r = fri_verify(bad, alpha);
    printf("  [REJECT] tampered eval_pos: %s\n", r ? "ACCEPT (BUG)" : "REJECT (ok)");
    if (r) all_ok = 0;
  }
  /* (3) negative: tamper a Merkle path sibling -> must REJECT */
  {
    uint64_t bad[PROOF_U64]; memcpy(bad, proof, sizeof bad);
    uint64_t *qb = bad + 1 * LAYER_U64 + LANES + 0 * QUERY_U64;
    qb[4] = qb[4] ^ 0xFFULL;  /* corrupt a path_pos sibling lane */
    int r = fri_verify(bad, alpha);
    printf("  [REJECT] tampered Merkle path: %s\n", r ? "ACCEPT (BUG)" : "REJECT (ok)");
    if (r) all_ok = 0;
  }
  /* (4) negative: tamper the remainder polynomial -> must REJECT */
  {
    uint64_t bad[PROOF_U64]; memcpy(bad, proof, sizeof bad);
    uint64_t *r0 = bad + NUM_LAYERS * LAYER_U64;
    r0[0] = f_add(r0[0], 1);
    int r = fri_verify(bad, alpha);
    printf("  [REJECT] tampered remainder: %s\n", r ? "ACCEPT (BUG)" : "REJECT (ok)");
    if (r) all_ok = 0;
  }
  /* (5) negative: wrong challenge alpha (verifier uses different alpha) -> REJECT.
   * Corrupt alpha[0] (layer-0 fold): the layer-0 codeword is genuinely
   * non-constant, so the fold result depends on the challenge. (Corrupting
   * only the LAST layer's alpha would NOT be caught, and correctly so: the
   * final codeword here is constant — fri_fold(c,c,x,alpha)=c for all alpha —
   * a real property of low-degree FRI, not a verifier gap.) */
  {
    uint64_t alpha_bad[4] = {999, 202, 303, 404};
    int r = fri_verify(proof, alpha_bad);
    printf("  [REJECT] wrong fold challenge (layer 0): %s\n", r ? "ACCEPT (BUG)" : "REJECT (ok)");
    if (r) all_ok = 0;
  }

  /* ---------- cyc/op ---------- */
  uint64_t out[PROOF_U64];
  for (int i = 0; i < 100; i++) plonky3_fri_prove_obj_rc(out, evals, alpha, qidx);
  uint64_t best_p = ~0ULL;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      plonky3_fri_prove_obj_rc(out, evals, alpha, qidx);
      __asm__ __volatile__("" :: "r"(out) : "memory");
    }
    uint64_t t1 = rdtscp();
    if (t1 - t0 < best_p) best_p = t1 - t0;
  }
  volatile int sink = 0;
  for (int i = 0; i < 100; i++) sink ^= fri_verify(proof, alpha);
  uint64_t best_v = ~0ULL;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) { sink ^= fri_verify(proof, alpha); }
    uint64_t t1 = rdtscp();
    if (t1 - t0 < best_v) best_v = t1 - t0;
  }
  (void)sink;

  printf("\n  prove  (Tier A emit, jasminc): %llu cyc/op\n",
         (unsigned long long)(best_p / ITERS));
  printf("  verify (pure-C reference):     %llu cyc/op\n",
         (unsigned long long)(best_v / ITERS));

  printf("\n  RESULT: %s\n", all_ok ? "ALL CHECKS PASS (accept + 4 rejects)"
                                    : "FAILURE — see above");
  return all_ok ? 0 : 1;
}
