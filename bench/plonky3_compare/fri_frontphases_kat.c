/* KAT for the FRONT-COMPILED fri_proof spine phases
 * (gen_com/fri_proof_frontphases.s, emitted by
 * CatCrypt/Crypto/SecureCompilation/VIR/Plonky3FriProofFrontEmit.lean —
 * owned render, no jasminc, no hand Com/Lcmd).
 *
 * Two fragments, each checked against the independent C reference recipe of
 * bench_fri_proof_from_rustcmd.c (the fri.rs::fri_prove_column oracle the
 * whole-artifact KAT uses):
 *
 *   p3_fri_fold_chain(acc[34], alpha[4], n0, n1, n2, n3)
 *     acc[0..31] = column LDE in, folded in place through 4 FRI layers
 *     (counts 16, 8, 4, 2); acc[32..33] = the degree-1 remainder out.
 *     Gate: acc[0..1] == reference layer-4 codeword, acc[32..33] ==
 *     reference remainder (the proof words 544..545).
 *
 *   p3_merkle_flat8(nodes[60], src[8], n=8, levels=3)
 *     flat single-buffer Merkle build (level l at lane 8n - (8n >> l)).
 *     Gate: nodes[0..31] == reference leaf hashes, nodes[56..59] ==
 *     reference Merkle root.
 *
 *   p3_fri_fold_chain_fx(acc[34], alpha[4])
 *     the SAME fold chain with every trip count compile-time (two-register
 *     ABI, no count arguments). Gate: identical to p3_fri_fold_chain.
 *
 *   p3_fri_query_walk(qproof[136], cur[32], tree[256], qidx[4], levels=5)
 *     the layer-0 query/auth-path walk: root copy + per query q<3 the
 *     openings cur[ipos]/cur[ineg] (ipos = qidx[q] & 31, ineg = (ipos+16)
 *     & 31), the index words, and BOTH 20-word authentication paths read
 *     from the flat tree (level l at lane 256 - (256 >> l)).
 *     Gate: qproof[0..135] == the reference prover's proof[0..135].
 *
 * Build: make plonky3-fri-frontphases-kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void p3_fri_fold_chain(uint64_t *acc, const uint64_t *alpha,
                              uint64_t n0, uint64_t n1, uint64_t n2, uint64_t n3);
extern void p3_merkle_flat8(uint64_t *nodes, const uint64_t *src,
                            uint64_t n, uint64_t levels);
extern void p3_fri_fold_chain_fx(uint64_t *acc, const uint64_t *alpha);
extern void p3_fri_query_walk(uint64_t *qproof, const uint64_t *cur,
                              const uint64_t *tree, const uint64_t *qidx,
                              uint64_t levels);

#define BB_P 2013265921ULL
#define BB_G 31ULL

/* ---------- BabyBear field (bench_fri_proof_from_rustcmd.c reference) ------ */
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
static uint64_t f_poly_eval(const uint64_t *coeffs, int n, uint64_t x) {
  uint64_t acc = 0;
  for (int i = n - 1; i >= 0; i--) acc = f_add(f_mul(acc, x), coeffs[i]);
  return acc;
}
static uint64_t f_fri_fold(uint64_t ep, uint64_t en, uint64_t x, uint64_t alpha) {
  uint64_t sum = f_add(ep, en), diff = f_sub(ep, en);
  uint64_t inv2 = f_inv(2);
  uint64_t inv2x = f_inv(f_mul(2, x));
  uint64_t peven = f_mul(sum, inv2);
  uint64_t podd  = f_mul(diff, inv2x);
  return f_add(peven, f_mul(alpha, podd));
}

/* ---------- u64-lane Merkle mixers (plonky3_merkle_leaves.jinc reference) -- */
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
  for (int i = 1; i < 4; i++) { prev *= 0xC5ULL; t = o[i]; t ^= prev; o[i] = t; prev = t; }
}
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

/* Authentication path (20 words = 5 sibling digests) for leaf_index
 * (bench_fri_proof_from_rustcmd.c recipe). */
static void ref_merkle_path(uint64_t out_path[20], const uint64_t leaves[128],
                            int n, int leaf_index) {
  uint64_t a[128], b[128];
  memcpy(a, leaves, sizeof(uint64_t) * 4 * n);
  memset(out_path, 0, sizeof(uint64_t) * 20);
  int pairs = n, level = 0, x = leaf_index;
  while (pairs > 1) {
    int sib = x ^ 1;
    for (int k = 0; k < 4; k++) out_path[level * 4 + k] = a[sib * 4 + k];
    for (int j = 0; j < pairs / 2; j++) p3_compress(&b[j * 4], &a[(2 * j) * 4], &a[(2 * j + 1) * 4]);
    memcpy(a, b, sizeof(uint64_t) * 4 * (pairs / 2));
    pairs /= 2;
    x >>= 1;
    level++;
  }
}

/* The flat n=32 tree the walk reads: level l at lane 256 - (256 >> l). */
static void ref_flat_tree32(uint64_t tree[256], const uint64_t *cur) {
  uint64_t a[128], b[128];
  memset(tree, 0, sizeof(uint64_t) * 256);
  ref_build_leaf_hashes(a, cur, 32);
  int pairs = 32;
  for (int l = 0; l < 6; l++) {
    int base = 256 - (256 >> l);
    for (int j = 0; j < pairs * 4; j++) tree[base + j] = a[j];
    for (int j = 0; j < pairs / 2; j++) p3_compress(&b[j * 4], &a[(2 * j) * 4], &a[(2 * j + 1) * 4]);
    memcpy(a, b, sizeof(uint64_t) * 4 * (pairs / 2 > 0 ? pairs / 2 : 1));
    pairs /= 2;
  }
}

/* The reference layer-0 proof block (ref_fri_prove_obj's root+query arm,
 * words 0..135). */
static void ref_layer0_block(uint64_t blk[136], const uint64_t *cur,
                             const uint64_t *qidx) {
  uint64_t leaves[128], root[4], pp[20], pn[20];
  memset(blk, 0, sizeof(uint64_t) * 136);
  ref_build_leaf_hashes(leaves, cur, 32);
  ref_merkle_root(root, leaves, 32);
  for (int k = 0; k < 4; k++) blk[k] = root[k];
  for (int q = 0; q < 3; q++) {
    int qb = 4 + q * 44;
    int ipos = (int)(qidx[q] % 32);
    int ineg = (ipos + 16) % 32;
    blk[qb + 0] = cur[ipos];
    blk[qb + 1] = cur[ineg];
    blk[qb + 2] = (uint64_t)ipos;
    blk[qb + 3] = (uint64_t)ineg;
    ref_merkle_path(pp, leaves, 32, ipos);
    for (int k = 0; k < 20; k++) blk[qb + 4 + k] = pp[k];
    ref_merkle_path(pn, leaves, 32, ineg);
    for (int k = 0; k < 20; k++) blk[qb + 24 + k] = pn[k];
  }
}

/* ---------- the reference fold chain (ref_fri_prove_obj's fold arm) -------- */
static void ref_fold_chain(uint64_t cur[32], uint64_t rem[2],
                           const uint64_t evals[32], const uint64_t alpha[4]) {
  memcpy(cur, evals, sizeof(uint64_t) * 32);
  for (int L = 0; L < 4; L++) {
    int half = (32 >> L) / 2, log = 5 - L;
    uint64_t ol = f_rou(log), xpow = 1;
    uint64_t a = alpha[L];
    uint64_t next[32];
    for (int i = 0; i < half; i++) {
      next[i] = f_fri_fold(cur[i], cur[i + half], xpow, a);
      xpow = f_mul(xpow, ol);
    }
    memcpy(cur, next, sizeof(uint64_t) * half);
  }
  uint64_t inv2 = f_inv(2);
  rem[0] = f_mul(f_add(cur[0], cur[1]), inv2);
  rem[1] = f_mul(f_sub(cur[0], cur[1]), inv2);
}

static void build_column_lde(uint64_t evals[32], const uint64_t coeffs[4]) {
  uint64_t omega = f_rou(5);
  uint64_t x = 1;
  for (int i = 0; i < 32; i++) {
    evals[i] = f_poly_eval(coeffs, 4, x);
    x = f_mul(x, omega);
  }
}

int main(void) {
  const uint64_t coeffs[4] = {7, 3, 5, 2};
  const uint64_t alpha[4] = {101, 202, 303, 404};
  uint64_t evals[32];
  build_column_lde(evals, coeffs);
  int fails = 0;

  /* --- fold chain --- */
  uint64_t ref_cur[32], ref_rem[2];
  ref_fold_chain(ref_cur, ref_rem, evals, alpha);
  uint64_t acc[34];
  memcpy(acc, evals, sizeof(uint64_t) * 32);
  acc[32] = 0; acc[33] = 0;
  p3_fri_fold_chain(acc, alpha, 16, 8, 4, 2);
  for (int i = 0; i < 2; i++)
    if (acc[i] != ref_cur[i]) {
      printf("FAIL fold codeword[%d]: got %llu want %llu\n", i,
             (unsigned long long)acc[i], (unsigned long long)ref_cur[i]);
      fails++;
    }
  for (int i = 0; i < 2; i++)
    if (acc[32 + i] != ref_rem[i]) {
      printf("FAIL remainder[%d]: got %llu want %llu\n", i,
             (unsigned long long)acc[32 + i], (unsigned long long)ref_rem[i]);
      fails++;
    }

  /* --- Merkle flat build (n = 8) --- */
  uint64_t leaves[128], root[4];
  ref_build_leaf_hashes(leaves, evals, 8);
  ref_merkle_root(root, leaves, 8);
  uint64_t nodes[60];
  memset(nodes, 0, sizeof nodes);
  p3_merkle_flat8(nodes, evals, 8, 3);
  for (int i = 0; i < 32; i++)
    if (nodes[i] != leaves[i]) {
      printf("FAIL merkle leaf lane %d: got %llu want %llu\n", i,
             (unsigned long long)nodes[i], (unsigned long long)leaves[i]);
      fails++;
    }
  for (int i = 0; i < 4; i++)
    if (nodes[56 + i] != root[i]) {
      printf("FAIL merkle root lane %d: got %llu want %llu\n", i,
             (unsigned long long)nodes[56 + i], (unsigned long long)root[i]);
      fails++;
    }

  /* --- fixed-count fold chain (two-register ABI) --- */
  uint64_t accfx[34];
  memcpy(accfx, evals, sizeof(uint64_t) * 32);
  accfx[32] = 0; accfx[33] = 0;
  p3_fri_fold_chain_fx(accfx, alpha);
  for (int i = 0; i < 2; i++)
    if (accfx[i] != ref_cur[i]) {
      printf("FAIL fx fold codeword[%d]: got %llu want %llu\n", i,
             (unsigned long long)accfx[i], (unsigned long long)ref_cur[i]);
      fails++;
    }
  for (int i = 0; i < 2; i++)
    if (accfx[32 + i] != ref_rem[i]) {
      printf("FAIL fx remainder[%d]: got %llu want %llu\n", i,
             (unsigned long long)accfx[32 + i], (unsigned long long)ref_rem[i]);
      fails++;
    }

  /* --- query/auth-path walk (layer 0, n = 32) --- */
  const uint64_t qidx[4] = {3, 11, 26, 0};
  uint64_t tree[256], blk_ref[136], qproof[136];
  ref_flat_tree32(tree, evals);
  ref_layer0_block(blk_ref, evals, qidx);
  memset(qproof, 0, sizeof qproof);
  p3_fri_query_walk(qproof, evals, tree, qidx, 5);
  for (int i = 0; i < 136; i++)
    if (qproof[i] != blk_ref[i]) {
      printf("FAIL query block[%d]: got %llu want %llu\n", i,
             (unsigned long long)qproof[i], (unsigned long long)blk_ref[i]);
      fails++;
    }

  if (fails == 0) {
    printf("fri_frontphases KAT: PASS (fold chain codeword+remainder [runtime + fixed counts], merkle leaves+root, layer-0 query block 136/136)\n");
    printf("  remainder = %llu, %llu\n",
           (unsigned long long)acc[32], (unsigned long long)acc[33]);
    return 0;
  }
  printf("fri_frontphases KAT: FAIL (%d mismatches)\n", fails);
  return 1;
}
