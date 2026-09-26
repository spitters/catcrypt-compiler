/* Honest Plonky3 Fibonacci-STARK prover over the VERIFIED Poseidon2 permutation.
 *
 * The prover (hp_prove) is fully emitted by jasminc from the verified leaves:
 * its Merkle commit, FRI fold-layer commit, Fiat-Shamir challenger and PoW all
 * run through the verified Poseidon2-BabyBear permutation as
 *   leaf hash = PaddingFreeSponge<16,8,8>   (hp_sponge8)
 *   compress  = TruncatedPermutation<2,8,16> (hp_compress8)
 *   duplex     = permutation                 (hp_perm16)
 * (KAT-matched to Plonky3 in p2_hash_kat). It emits a serialized proof of 980
 * u64 lanes: roots, FRI final poly, beta, PoW nonce, and 8 query openings with
 * full Merkle authentication paths.
 *
 * The verifier here is C control-flow ONLY: every hash it computes is a call to
 * the SAME emitted verified leaves (hp_sponge8 / hp_compress8 / hp_perm16), so
 * the soundness-critical hashing is the verified permutation, not a C
 * re-implementation. It re-derives the Fiat-Shamir challenges, recomputes every
 * Merkle root from the openings + auth paths, checks the FRI fold relation at
 * each (re-derived) query, and checks the PoW.
 *
 * KAT gate: verify ACCEPT on the honest proof, verify REJECT on a tampered
 * public input (claimed 8th Fibonacci 21 -> 22). Bench: end-to-end prove cyc/op
 * (min-of-3), same harness as p3_ref/.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define PROOF_LANES 980
#define BB_P 2013265921ULL

extern uint64_t *hp_prove(uint64_t *out, const uint64_t *p0);
extern uint64_t *hp_sponge8(uint64_t *o, const uint64_t *row);     /* PaddingFreeSponge<16,8,8> */
extern uint64_t *hp_compress8(uint64_t *o, const uint64_t *l, const uint64_t *r); /* Trunc<2,8,16> */
extern uint64_t *hp_perm16(uint64_t *o, const uint64_t *s);        /* verified permutation */

static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}

static inline uint64_t bb_red(uint64_t x) { return x % BB_P; }
static inline uint64_t bb_add(uint64_t a, uint64_t b) { return (bb_red(a) + bb_red(b)) % BB_P; }
static inline uint64_t bb_sub(uint64_t a, uint64_t b) { return (bb_red(a) + BB_P - bb_red(b)) % BB_P; }
static inline uint64_t bb_mul(uint64_t a, uint64_t b) { return (bb_red(a) * bb_red(b)) % BB_P; }

/* leaf hash of a width-3 row (a,b,c) -> 8-lane digest, via verified sponge. */
static void leaf_row3(uint64_t out[8], uint64_t v0, uint64_t v1, uint64_t v2) {
  uint64_t row[8] = { v0, v1, v2, 0, 0, 0, 0, 0 };
  hp_sponge8(out, row);
}
static void leaf_fe(uint64_t out[8], uint64_t v) {
  uint64_t row[8] = { v, 0, 0, 0, 0, 0, 0, 0 };
  hp_sponge8(out, row);
}

/* recompute a depth-`d` Merkle root from leaf digest + d sibling digests. */
static void root_from_path(uint64_t out[8], const uint64_t leaf[8],
                           const uint64_t *path, int d, uint64_t idx) {
  uint64_t cur[8], sib[8], lc[8], rc[8];
  memcpy(cur, leaf, 8 * sizeof(uint64_t));
  for (int lvl = 0; lvl < d; lvl++) {
    memcpy(sib, path + lvl * 8, 8 * sizeof(uint64_t));
    if ((idx & 1) == 0) { memcpy(lc, cur, 64); memcpy(rc, sib, 64); }
    else                { memcpy(lc, sib, 64); memcpy(rc, cur, 64); }
    hp_compress8(cur, lc, rc);
    idx >>= 1;
  }
  memcpy(out, cur, 64);
}

/* duplex challenger: absorb an 8-lane block (overwrite rate, permute). */
static void fs_absorb8(uint64_t st[16], const uint64_t blk[8]) {
  uint64_t tmp[16];
  for (int i = 0; i < 8; i++) st[i] = bb_red(blk[i]);
  hp_perm16(tmp, st);
  memcpy(st, tmp, 16 * sizeof(uint64_t));
}
static void fs_squeeze(uint64_t st[16]) {
  uint64_t tmp[16];
  hp_perm16(tmp, st);
  memcpy(st, tmp, 16 * sizeof(uint64_t));
}

static int digest_ne(const uint64_t a[8], const uint64_t b[8]) {
  for (int i = 0; i < 8; i++) if (a[i] != b[i]) return 1;
  return 0;
}

/* Honest verifier (control flow in C, hashing via verified emitted leaves). */
static int hp_verify(const uint64_t *proof, const uint64_t pub[3]) {
  uint64_t root0[8], root16[8], fs[16], blk[8], rec[8], leaf[8];
  for (int i = 0; i < 8; i++) { root0[i] = proof[i]; root16[i] = proof[8 + i]; }
  int ok = 1;

  /* re-derive beta: absorb pub, root0, squeeze. */
  memset(fs, 0, sizeof fs);
  blk[0] = pub[0]; blk[1] = pub[1]; blk[2] = pub[2];
  for (int i = 3; i < 8; i++) blk[i] = 0;
  fs_absorb8(fs, blk);
  fs_absorb8(fs, root0);
  fs_squeeze(fs);
  uint64_t beta = bb_red(fs[0]);
  if (beta != bb_red(proof[18])) ok = 0;

  /* PoW: sponge16(root0 || nonce)[0] & 255 == 0. */
  uint64_t nonce = proof[19];
  memset(fs, 0, sizeof fs);
  for (int i = 0; i < 8; i++) fs[i] = root0[i];
  fs[8] = nonce;
  uint64_t perm[16];
  hp_perm16(perm, fs);
  if ((perm[0] & 255ULL) != 0) ok = 0;

  /* re-derive query challenger: pub, root0, root16, nonce. */
  memset(fs, 0, sizeof fs);
  blk[0] = pub[0]; blk[1] = pub[1]; blk[2] = pub[2];
  for (int i = 3; i < 8; i++) blk[i] = 0;
  fs_absorb8(fs, blk);
  fs_absorb8(fs, root0);
  fs_absorb8(fs, root16);
  blk[0] = nonce; for (int i = 1; i < 8; i++) blk[i] = 0;
  fs_absorb8(fs, blk);

  for (int r = 0; r < 8; r++) {
    fs_squeeze(fs);
    uint64_t qf = bb_red(fs[0]) & 31ULL;
    int base = 20 + r * 120;
    uint64_t q = proof[base + 0];
    if (q != qf) ok = 0;

    /* (1) root0 from q's row + auth path (depth 5). */
    uint64_t av = proof[base + 1], bv = proof[base + 2], cv = proof[base + 3];
    leaf_row3(leaf, av, bv, cv);
    root_from_path(rec, leaf, proof + base + 4, 5, q);
    if (digest_ne(rec, root0)) ok = 0;

    /* (2) root0 from partner row q^16 + auth path (depth 5). */
    uint64_t qp = q ^ 16ULL;
    uint64_t pa = proof[base + 44], pb = proof[base + 45], pc = proof[base + 46];
    leaf_row3(leaf, pa, pb, pc);
    root_from_path(rec, leaf, proof + base + 47, 5, qp);
    if (digest_ne(rec, root0)) ok = 0;

    /* (3) FRI fold: a = col0 at index <16, b = col0 at >=16; folded = (a+b)+beta*(a-b). */
    uint64_t lo, t;
    if ((q & 16ULL) == 0) { lo = av; t = pa; } else { lo = pa; t = av; }
    uint64_t folded = bb_add(bb_add(lo, t), bb_mul(bb_sub(lo, t), beta));
    uint64_t fv = proof[base + 87];
    if (folded != fv) ok = 0;

    /* (4) root16 from f16 opening + depth-4 auth path. */
    leaf_fe(leaf, fv);
    root_from_path(rec, leaf, proof + base + 88, 4, q & 15ULL);
    if (digest_ne(rec, root16)) ok = 0;
  }
  return ok;
}

#define ITERS 200

int main(void) {
  uint64_t trace[24];
  uint64_t a = 0, b = 1;
  for (int row = 0; row < 8; row++) {
    trace[3*row + 0] = a;
    trace[3*row + 1] = b;
    uint64_t c = a + b;
    trace[3*row + 2] = c;
    a = b; b = c;
  }
  uint64_t pub[3]     = { trace[0], trace[1], trace[23] };
  uint64_t pub_bad[3] = { trace[0], trace[1], trace[23] + 1 };

  uint64_t proof[PROOF_LANES];
  hp_prove(proof, trace);

  printf("Honest Plonky3 Fibonacci STARK prover (verified Poseidon2, height=8, width=3,\n");
  printf("  blowup=4 domain=32, 8 queries, PoW 8 bits):\n");
  printf("  root0[0..1]=%llu,%llu  root16[0..1]=%llu,%llu  finalpoly=%llu,%llu  beta=%llu  nonce=%llu\n",
         (unsigned long long)proof[0], (unsigned long long)proof[1],
         (unsigned long long)proof[8], (unsigned long long)proof[9],
         (unsigned long long)proof[16], (unsigned long long)proof[17],
         (unsigned long long)proof[18], (unsigned long long)proof[19]);

  int acc = hp_verify(proof, pub);
  int rej = hp_verify(proof, pub_bad);
  int ok = 1;
  if (acc == 1) printf("  KAT: verify ACCEPT on honest proof              [PASS]\n");
  else { printf("  KAT: verify REJECTED honest proof                [FAIL]\n"); ok = 0; }
  if (rej == 0) printf("  KAT: verify REJECT on tampered public input     [PASS]\n");
  else { printf("  KAT: verify ACCEPTED tampered public input       [FAIL]\n"); ok = 0; }
  if (!ok) return 1;

  for (int i = 0; i < 50; i++) { hp_prove(proof, trace); __asm__ volatile("":: "r"(proof) : "memory"); }
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) {
      hp_prove(proof, trace);
      __asm__ volatile("" :: "r"(proof) : "memory");
    }
    uint64_t t1 = rdtscp();
    if (t1 - t0 < best) best = t1 - t0;
  }
  printf("  Honest emit prove (jasminc): %llu cyc/op (min-of-3, ITERS=%d)\n",
         (unsigned long long)(best / ITERS), ITERS);
  return 0;
}
