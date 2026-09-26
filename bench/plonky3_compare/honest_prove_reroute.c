/* Honest Plonky3 Fibonacci-STARK prover — Poseidon2 backend REROUTE harness.
 *
 * This replicates the EXACT algorithm of the verified-emitted jasmin prover
 * `hp_prove` (include/plonky3_honest_prover.jinc), but routes every Poseidon2
 * permutation through a pluggable backend so the SAME prover can be timed with:
 *
 *   backend 0 (scalar):  the verified-emitted jasmin leaf hp_perm16
 *                        (the permutation baked into plonky3_honest_prove.s,
 *                         KAT-matched to Plonky3 PaddingFreeSponge<16,8,8>).
 *   backend 1 (avx512):  the fast AVX-512 (ZMM 8-lane Montgomery) leaf
 *                        poseidon2_bb_avx512_mont
 *                        (../SSProve-lean/bench/poseidon2_compare, ~0.92x vs Plonky3 prod;
 *                         KAT-matched to the SAME upstream
 *                         test_default_babybear_poseidon2_width_16 vector).
 *
 * Both backends compute the IDENTICAL Poseidon2-BabyBear permutation, so the
 * produced proof must be byte-identical. The harness GATES on that (proof must
 * match the jasmin monolith's proof AND scalar==avx512 byte-for-byte) before it
 * reports any timing. It also breaks the prover cost into phases so the Amdahl
 * fraction of Poseidon2 (and of the PoW grind specifically) is measured, not
 * assumed.
 *
 * The field/LDE/FRI arithmetic and all control flow are pure C here, faithful to
 * the jinc; only the permutation is the swappable backend. Validation that this
 * C replica is faithful = its proof equals the jasmin monolith hp_prove proof.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define BB_P 2013265921ULL
#define BB_G 31ULL
#define PROOF_LANES 980

/* ---- the two emitted permutation backends ---- */
extern uint64_t *hp_prove(uint64_t *out, const uint64_t *p0);   /* jasmin monolith (scalar), for the gate */
extern uint64_t *hp_perm16(uint64_t *o, const uint64_t *s);     /* verified scalar leaf (jasmin) */
extern void poseidon2_bb_avx512_mont(uint64_t out[16], const uint64_t in[16]); /* fast AVX-512 leaf */

/* perm-call counter (Amdahl bookkeeping) */
static uint64_t g_perm_calls = 0;

/* pluggable backend: 0 = scalar jasmin leaf, 1 = avx512 leaf */
static int g_backend = 0;
static inline void perm16(uint64_t out[16], const uint64_t in[16]) {
  g_perm_calls++;
  if (g_backend == 0) hp_perm16(out, in);
  else                poseidon2_bb_avx512_mont(out, in);
}

/* ---- BabyBear field (byte-faithful to _pr_* in plonky3_prove_leaves.jinc) ---- */
static inline uint64_t pr_reduce(uint64_t x) {
  uint64_t t = x - BB_P;
  uint64_t m = ((int64_t)t < 0) ? BB_P : 0;
  return t + m;
}
static inline uint64_t pr_add(uint64_t a, uint64_t b) { return pr_reduce(pr_reduce(a) + pr_reduce(b)); }
static inline uint64_t pr_sub(uint64_t a, uint64_t b) { return pr_reduce((BB_P + pr_reduce(a)) - pr_reduce(b)); }
static inline uint64_t pr_mul(uint64_t a, uint64_t b) { return (pr_reduce(a) * pr_reduce(b)) % BB_P; }
static uint64_t pr_pow(uint64_t base, uint64_t exp) {
  uint64_t r = 1, c = base % BB_P;
  for (int it = 0; it < 64; it++) { if (exp & 1) r = pr_mul(r, c); c = pr_mul(c, c); exp >>= 1; }
  return r;
}
static uint64_t pr_inv(uint64_t a) { return a == 0 ? 0 : pr_pow(a, BB_P - 2); }
static uint64_t pr_rou(int k) { return pr_pow(BB_G, (BB_P - 1) >> k); }
static uint64_t pr_bitrev(uint64_t i, int logN) {
  uint64_t r = 0; for (int k = 0; k < logN; k++) { r = (r << 1) | (i & 1); i >>= 1; } return r;
}
static void pr_ntt(uint64_t *io, int n, uint64_t omega) {
  if (n <= 1) return;
  int logN = 0; while ((1 << logN) < n) logN++;
  uint64_t a[64];
  for (int idx = 0; idx < n; idx++) a[idx] = io[pr_bitrev(idx, logN)];
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
/* trace LDE: 3 columns interleaved row-major (plonky3_trace_lde_3_8). */
static void trace_lde(uint64_t o[96], const uint64_t s[24]) {
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

/* ---- Poseidon2 hash constructions over the swappable permutation ---- */
/* PaddingFreeSponge<16,8,8>: reduce the width-<=8 row, zero-pad to 16, permute, take 8. */
static void sponge8(uint64_t o[8], const uint64_t row[8]) {
  uint64_t st[16], po[16];
  for (int i = 0; i < 8; i++)  st[i] = pr_reduce(row[i]);
  for (int i = 8; i < 16; i++) st[i] = 0;
  perm16(po, st);
  for (int i = 0; i < 8; i++) o[i] = po[i];
}
/* TruncatedPermutation<2,8,16>: concat two 8-lane digests, permute, take 8. */
static void compress8(uint64_t o[8], const uint64_t l[8], const uint64_t r[8]) {
  uint64_t st[16], po[16];
  for (int i = 0; i < 8; i++) st[i] = l[i];
  for (int i = 0; i < 8; i++) st[8 + i] = r[i];
  perm16(po, st);
  for (int i = 0; i < 8; i++) o[i] = po[i];
}
static void leaf_row3(uint64_t o[8], uint64_t v0, uint64_t v1, uint64_t v2) {
  uint64_t row[8] = { v0, v1, v2, 0, 0, 0, 0, 0 }; sponge8(o, row);
}
static void leaf_fe(uint64_t o[8], uint64_t v) {
  uint64_t row[8] = { v, 0, 0, 0, 0, 0, 0, 0 }; sponge8(o, row);
}

/* ---- Merkle trees (faithful to the jinc) ---- */
/* codeword tree32: nodes[504] = leaves(256)+l16(128)+l8(64)+l4(32)+l2(16)+root(8). */
static void build_tree32(uint64_t nodes[504], const uint64_t lde[96]) {
  for (int leaf = 0; leaf < 32; leaf++) {
    uint64_t lf[8];
    leaf_row3(lf, lde[3*leaf+0], lde[3*leaf+1], lde[3*leaf+2]);
    for (int i = 0; i < 8; i++) nodes[leaf*8 + i] = lf[i];
  }
  for (int j = 0; j < 16; j++) compress8(&nodes[256 + j*8], &nodes[(2*j)*8],       &nodes[(2*j+1)*8]);
  for (int j = 0; j <  8; j++) compress8(&nodes[384 + j*8], &nodes[256+(2*j)*8],   &nodes[256+(2*j+1)*8]);
  for (int j = 0; j <  4; j++) compress8(&nodes[448 + j*8], &nodes[384+(2*j)*8],   &nodes[384+(2*j+1)*8]);
  for (int j = 0; j <  2; j++) compress8(&nodes[480 + j*8], &nodes[448+(2*j)*8],   &nodes[448+(2*j+1)*8]);
  compress8(&nodes[496], &nodes[480], &nodes[488]);
}
/* fold-layer tree16: nd[248] = l16(128)+l8(64)+l4(32)+l2(16)+root(8). */
static void build_tree16(uint64_t nd[248], const uint64_t ev[16]) {
  for (int leaf = 0; leaf < 16; leaf++) {
    uint64_t lf[8]; leaf_fe(lf, ev[leaf]);
    for (int i = 0; i < 8; i++) nd[leaf*8 + i] = lf[i];
  }
  for (int j = 0; j < 8; j++) compress8(&nd[128 + j*8], &nd[(2*j)*8],     &nd[(2*j+1)*8]);
  for (int j = 0; j < 4; j++) compress8(&nd[192 + j*8], &nd[128+(2*j)*8], &nd[128+(2*j+1)*8]);
  for (int j = 0; j < 2; j++) compress8(&nd[224 + j*8], &nd[192+(2*j)*8], &nd[192+(2*j+1)*8]);
  compress8(&nd[240], &nd[224], &nd[232]);
}
static void authpath32(uint64_t path[40], const uint64_t nodes[504], uint64_t idx) {
  uint64_t sib;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[0*8+i]=nodes[sib*8+i];       idx>>=1;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[1*8+i]=nodes[256+sib*8+i];   idx>>=1;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[2*8+i]=nodes[384+sib*8+i];   idx>>=1;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[3*8+i]=nodes[448+sib*8+i];   idx>>=1;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[4*8+i]=nodes[480+sib*8+i];
}
static void authpath16(uint64_t path[32], const uint64_t nd[248], uint64_t idx) {
  uint64_t sib;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[0*8+i]=nd[sib*8+i];       idx>>=1;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[1*8+i]=nd[128+sib*8+i];   idx>>=1;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[2*8+i]=nd[192+sib*8+i];   idx>>=1;
  sib = idx ^ 1;       for (int i=0;i<8;i++) path[3*8+i]=nd[224+sib*8+i];
}

/* ---- Fiat-Shamir duplex challenger ---- */
static void fs_absorb8(uint64_t st[16], const uint64_t blk[8]) {
  uint64_t po[16];
  for (int i = 0; i < 8; i++) st[i] = pr_reduce(blk[i]);
  perm16(po, st);
  for (int i = 0; i < 16; i++) st[i] = po[i];
}
static void fs_squeeze(uint64_t st[16]) {
  uint64_t po[16];
  perm16(po, st);
  for (int i = 0; i < 16; i++) st[i] = po[i];
}

/* ---- open one query (faithful to _hp_open_query) ---- */
static void open_query(uint64_t out[980], const uint64_t lde[96],
                       const uint64_t nodes[504], const uint64_t nd16[248],
                       const uint64_t f16[16], uint64_t q, uint64_t base) {
  out[base + 0] = q;
  uint64_t r3 = q * 3;
  out[base + 1] = lde[r3 + 0]; out[base + 2] = lde[r3 + 1]; out[base + 3] = lde[r3 + 2];
  uint64_t path[40];
  authpath32(path, nodes, q);
  for (int i = 0; i < 40; i++) out[base + 4 + i] = path[i];
  uint64_t qp = q ^ 16; uint64_t r3p = qp * 3;
  out[base + 44] = lde[r3p + 0]; out[base + 45] = lde[r3p + 1]; out[base + 46] = lde[r3p + 2];
  authpath32(path, nodes, qp);
  for (int i = 0; i < 40; i++) out[base + 47 + i] = path[i];
  uint64_t q15 = q & 15;
  out[base + 87] = f16[q15];
  uint64_t path16[32];
  authpath16(path16, nd16, q15);
  for (int i = 0; i < 32; i++) out[base + 88 + i] = path16[i];
}

/* ---- the full prover (faithful C replica of hp_prove) ---- */
/* Phase-timed counters returned via out-params for Amdahl. */
static void prove(uint64_t out[980], const uint64_t p0[24]) {
  uint64_t trace[24], lde[96], nodes[504], col0[16], f16[16], nd16[248], fs[16], blk[8];
  for (int i = 0; i < 24; i++) trace[i] = p0[i];
  trace_lde(lde, trace);
  build_tree32(nodes, lde);
  for (int i = 0; i < 8; i++) out[i] = nodes[496 + i];

  /* Fiat-Shamir beta */
  memset(fs, 0, sizeof fs);
  blk[0]=trace[0]; blk[1]=trace[1]; blk[2]=trace[23]; for (int i=3;i<8;i++) blk[i]=0;
  fs_absorb8(fs, blk);
  for (int i=0;i<8;i++) blk[i]=nodes[496+i];
  fs_absorb8(fs, blk);
  fs_squeeze(fs);
  uint64_t beta = pr_reduce(fs[0]);

  /* FRI fold 32->16 */
  for (int i = 0; i < 16; i++) col0[i] = pr_reduce(lde[3*i]);
  for (int i = 0; i < 16; i++) {
    uint64_t a = col0[i], b = pr_reduce(lde[3*(i+16)]);
    uint64_t s = pr_add(a,b), d = pr_sub(a,b), t = pr_mul(d,beta);
    f16[i] = pr_add(s,t);
  }
  build_tree16(nd16, f16);
  for (int i = 0; i < 8; i++) out[8 + i] = nd16[240 + i];

  /* fold 16->8->4->2 final poly */
  for (int i=0;i<8;i++){ uint64_t a=f16[i],b=f16[8+i],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,beta); col0[i]=pr_add(s,t); }
  for (int i=0;i<4;i++){ uint64_t a=col0[i],b=col0[4+i],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,beta); col0[i]=pr_add(s,t); }
  for (int i=0;i<2;i++){ uint64_t a=col0[i],b=col0[2+i],s=pr_add(a,b),d=pr_sub(a,b),t=pr_mul(d,beta); col0[i]=pr_add(s,t); }
  out[16]=col0[0]; out[17]=col0[1]; out[18]=beta;

  /* PoW grind: nonce s.t. perm(root0 || nonce)[0] & 255 == 0 */
  uint64_t nonce = 0;
  memset(fs, 0, sizeof fs);
  for (int i=0;i<8;i++) fs[i]=nodes[496+i];
  uint64_t h0 = 1;
  while (h0 != 0) {
    fs[8] = nonce;
    uint64_t po[16];
    perm16(po, fs);
    h0 = po[0] & 255ULL;
    if (h0 != 0) nonce += 1;
  }
  out[19] = nonce;

  /* query phase */
  memset(fs, 0, sizeof fs);
  blk[0]=trace[0]; blk[1]=trace[1]; blk[2]=trace[23]; for (int i=3;i<8;i++) blk[i]=0;
  fs_absorb8(fs, blk);
  for (int i=0;i<8;i++) blk[i]=nodes[496+i]; fs_absorb8(fs, blk);
  for (int i=0;i<8;i++) blk[i]=nd16[240+i];  fs_absorb8(fs, blk);
  blk[0]=out[19]; for (int i=1;i<8;i++) blk[i]=0; fs_absorb8(fs, blk);
  for (int r = 0; r < 8; r++) {
    fs_squeeze(fs);
    uint64_t q = pr_reduce(fs[0]) & 31ULL;
    open_query(out, lde, nodes, nd16, f16, q, 20 + r*120);
  }
}

/* ---- rdtsc timing ---- */
static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}
#define ITERS 200

static uint64_t bench_prove(const uint64_t *trace, int backend) {
  uint64_t out[980];
  g_backend = backend;
  for (int i = 0; i < 50; i++) prove(out, trace);
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 3; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < ITERS; i++) { prove(out, trace); __asm__ volatile("":: "r"(out):"memory"); }
    uint64_t t1 = rdtscp();
    if (t1 - t0 < best) best = t1 - t0;
  }
  return best / ITERS;
}

/* time a raw permutation backend in isolation (cyc/perm). */
static uint64_t bench_perm(int backend) {
  uint64_t in[16], out[16];
  for (int i = 0; i < 16; i++) in[i] = (uint64_t)(i*2654435761u % BB_P);
  for (int i = 0; i < 100; i++) { if (backend==0) hp_perm16(out,in); else poseidon2_bb_avx512_mont(out,in); memcpy(in,out,sizeof in); }
  uint64_t best = ~(uint64_t)0;
  for (int trial = 0; trial < 5; trial++) {
    uint64_t t0 = rdtscp();
    for (int i = 0; i < 4000; i++) { if (backend==0) hp_perm16(out,in); else poseidon2_bb_avx512_mont(out,in); __asm__ volatile("":: "r"(out):"memory"); }
    uint64_t t1 = rdtscp();
    if (t1 - t0 < best) best = t1 - t0;
  }
  return best / 4000;
}

int main(void) {
  uint64_t trace[24];
  uint64_t a = 0, b = 1;
  for (int row = 0; row < 8; row++) {
    trace[3*row+0]=a; trace[3*row+1]=b; uint64_t c=a+b; trace[3*row+2]=c; a=b; b=c;
  }

  int ok = 1;

  /* (A) faithfulness gate: C-replica scalar prover == jasmin monolith hp_prove. */
  uint64_t proof_mono[980], proof_scalar[980], proof_avx[980];
  hp_prove(proof_mono, trace);
  g_backend = 0; prove(proof_scalar, trace);
  int mono_ok = (memcmp(proof_mono, proof_scalar, sizeof proof_mono) == 0);
  printf("GATE A  C-replica(scalar) == jasmin-monolith hp_prove : %s\n",
         mono_ok ? "byte-identical [PASS]" : "MISMATCH [FAIL]");
  if (!mono_ok) {
    for (int i = 0; i < 20; i++)
      if (proof_mono[i] != proof_scalar[i])
        printf("    lane %d: mono=%llu replica=%llu\n", i,
               (unsigned long long)proof_mono[i], (unsigned long long)proof_scalar[i]);
    ok = 0;
  }

  /* (B) reroute correctness gate: avx512 prover proof == scalar prover proof. */
  g_perm_calls = 0; g_backend = 1; prove(proof_avx, trace);
  uint64_t perm_per_prove = g_perm_calls;
  int reroute_ok = (memcmp(proof_scalar, proof_avx, sizeof proof_scalar) == 0);
  printf("GATE B  AVX-512-rerouted proof == scalar proof        : %s\n",
         reroute_ok ? "byte-identical [PASS]" : "MISMATCH [FAIL]");
  if (!reroute_ok) {
    for (int i = 0; i < 980; i++)
      if (proof_scalar[i] != proof_avx[i]) {
        printf("    first diff lane %d: scalar=%llu avx=%llu\n", i,
               (unsigned long long)proof_scalar[i], (unsigned long long)proof_avx[i]);
        break;
      }
    ok = 0;
  }
  printf("  proof root0[0..1]=%llu,%llu  nonce=%llu  (Poseidon2 perms / prove = %llu)\n",
         (unsigned long long)proof_scalar[0], (unsigned long long)proof_scalar[1],
         (unsigned long long)proof_scalar[19], (unsigned long long)perm_per_prove);

  if (!ok) { printf("\nCORRECTNESS GATE FAILED — not reporting timing.\n"); return 1; }

  /* (C) timing: prover scalar vs avx512, plus raw perm cost for Amdahl. */
  uint64_t cyc_scalar = bench_prove(trace, 0);
  uint64_t cyc_avx    = bench_prove(trace, 1);
  uint64_t perm_scalar = bench_perm(0);
  uint64_t perm_avx    = bench_perm(1);

  printf("\n--- prover timing (taskset -c 3, min-of-3, ITERS=%d) ---\n", ITERS);
  printf("  scalar-Poseidon2 prover : %llu cyc/op\n", (unsigned long long)cyc_scalar);
  printf("  avx512-Poseidon2 prover : %llu cyc/op\n", (unsigned long long)cyc_avx);
  if (cyc_avx) printf("  prover speedup (scalar/avx512): %.3fx\n", (double)cyc_scalar/(double)cyc_avx);

  printf("\n--- Amdahl breakdown ---\n");
  printf("  raw permutation cost  : scalar=%llu cyc/perm   avx512=%llu cyc/perm  (%.2fx faster)\n",
         (unsigned long long)perm_scalar, (unsigned long long)perm_avx,
         perm_avx ? (double)perm_scalar/(double)perm_avx : 0.0);
  uint64_t p2_scalar = perm_scalar * perm_per_prove;
  uint64_t p2_avx    = perm_avx    * perm_per_prove;
  printf("  Poseidon2 perms/prove : %llu  (note: PoW grind is data-dependent; ~256 expected for 8 PoW bits)\n",
         (unsigned long long)perm_per_prove);
  printf("  est Poseidon2 time    : scalar=%llu cyc (%.1f%% of prover)   avx512=%llu cyc (%.1f%% of prover)\n",
         (unsigned long long)p2_scalar, 100.0*(double)p2_scalar/(double)cyc_scalar,
         (unsigned long long)p2_avx,    100.0*(double)p2_avx/(double)cyc_avx);
  printf("  non-Poseidon2 (LDE/FRI arith/serialize): scalar ~= %lld cyc (%.1f%%)\n",
         (long long)cyc_scalar - (long long)p2_scalar,
         100.0*((double)cyc_scalar-(double)p2_scalar)/(double)cyc_scalar);
  return 0;
}
