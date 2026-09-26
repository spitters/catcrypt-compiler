/* Windowed (Straus) multi-scalar multiplication over the verified HACL* Ed25519
 * group — the bucketed MSM that replaces the per-term variable-base ladder used
 * by ../SSProve-lean/bench/bulletproofs_compare/ipa_prover_prod_kat.c.
 *
 * Algorithm (window-4, 64 windows, interleaved across all m terms — Straus):
 *   for each base P_i: precompute T_i[0..15] = {0, P_i, 2P_i, ..., 15P_i}
 *   Q := identity
 *   for w in 63..0:                          (MSB-first window scan, PUBLIC counter)
 *     Q := 16*Q                              (4 shared doublings, shared across ALL terms)
 *     for i in 0..m:
 *       digit := (scalar_i >> (4*w)) & 15    (pure shift/and — no branch)
 *       sel   := T_i[digit]   via CT 16-way CMOV select (touch all 16 entries)
 *       Q     := Q + sel
 *
 * The 256 doublings are shared across all m terms instead of being paid m times
 * (a per-term ladder pays m*255 doublings). This is exactly what AUCurves'
 * src/Bedrock/End2End/Ed25519/Straus2MSMBody.v verifies (CT table lookup via
 * ct_table_lookup_16 + CMOV accumulation) and what the Lean reflect surface
 * CatCrypt/Crypto/Jasmin/StrausMsmReflect.lean proves constant-time
 * (strausScalarMulBody_isCT).
 *
 * CONSTANT TIME: digit is a pure shift/and of the scalar; the table lookup is a
 * 16-way CMOV (ct_select_point) that touches EVERY entry and selects by an
 * arithmetic mask, so there is NO secret-index memory access and NO
 * data-dependent branch. The window counter w is public. dalek's MSM is CT and
 * this one is too.
 *
 * KAT: the windowed result is checked byte-equal against the per-term ladder MSM
 * (msm_ladder, the #377/#370 oracle) over several scalar/point cases — the
 * bucket MSM must produce the same group element as the ladder.
 *
 * Build:
 *   gcc -O2 -march=native -o msm_straus msm_straus.c \
 *       ../../../SSProve-lean/bench/ed25519_compare/hacl_ed25519.o ../../../SSProve-lean/bench/ed25519_compare/hacl_curve25519_51.o \
 *       ../../../SSProve-lean/bench/ed25519_compare/hacl_hash_sha2.o
 *   taskset -c 3 ./msm_straus
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* verified HACL* Ed25519 group leaves */
extern void Hacl_Impl_Ed25519_PointConstants_make_point_inf(uint64_t *b);
extern void Hacl_Impl_Ed25519_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q);
extern void Hacl_Impl_Ed25519_PointDouble_point_double(uint64_t *out, uint64_t *p);
extern void Hacl_Impl_Ed25519_Ladder_point_mul(uint64_t *out, uint8_t *scalar, uint64_t *q);
extern _Bool Hacl_Impl_Ed25519_PointEqual_point_equal(uint64_t *p, uint64_t *q);
extern _Bool Hacl_Impl_Ed25519_PointDecompress_point_decompress(uint64_t *out, uint8_t *s);

#define mk_inf       Hacl_Impl_Ed25519_PointConstants_make_point_inf
#define point_add    Hacl_Impl_Ed25519_PointAdd_point_add
#define point_double Hacl_Impl_Ed25519_PointDouble_point_double
#define point_mul    Hacl_Impl_Ed25519_Ladder_point_mul
#define point_eq     Hacl_Impl_Ed25519_PointEqual_point_equal
#define decompress   Hacl_Impl_Ed25519_PointDecompress_point_decompress

#define PT 20  /* HACL XYZT point = 20 u64 */

static const uint8_t ED25519_BASE_COMP[32] = {
  0x58,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,
  0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66
};

static inline uint64_t rdtscp(void) {
  uint32_t lo, hi;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "rcx", "memory");
  return ((uint64_t)hi << 32) | lo;
}

static void set_scalar(uint8_t s[32], uint64_t k) {
  memset(s, 0, 32);
  for (int i = 0; i < 8; i++) s[i] = (uint8_t)((k >> (8 * i)) & 0xff);
}

/* ---------- oracle: per-term variable-base ladder MSM (the old path) -------- */
static void msm_ladder(const uint64_t *Ps, const uint64_t *k, int m, uint64_t out[PT]) {
  uint64_t acc[PT], term[PT], Pi[PT];
  uint8_t s[32];
  mk_inf(acc);
  for (int i = 0; i < m; i++) {
    set_scalar(s, k[i]);
    memcpy(Pi, Ps + PT * i, sizeof(Pi));
    point_mul(term, s, Pi);
    point_add(acc, acc, term);
  }
  memcpy(out, acc, sizeof(acc));
}

/* ---------- CT 16-way table select (all-buckets-touched CMOV) --------------- */
/* dst := T[digit], digit in 0..15. Touches every entry; selects by arithmetic
 * mask. No secret-index load, no branch. Mirrors AUCurves ct_table_lookup_16
 * and the Lean ctTableSelect16. */
static inline void ct_select_point(uint64_t dst[PT], const uint64_t T[16][PT],
                                   uint64_t digit) {
  for (int w = 0; w < PT; w++) dst[w] = 0;
  for (int e = 0; e < 16; e++) {
    /* mask = 0xFFFF... if digit==e else 0, computed without a branch */
    uint64_t x = digit ^ (uint64_t)e;
    uint64_t nz = (x | (uint64_t)(-(int64_t)x)) >> 63;   /* 1 if x!=0 else 0 */
    uint64_t mask = nz - 1ULL;                            /* all-ones if x==0 */
    for (int w = 0; w < PT; w++) dst[w] |= T[e][w] & mask;
  }
}

/* ---------- windowed (Straus) MSM ------------------------------------------ */
/* out = Sum_{i<m} k[i] * P_i, window-4, 64 windows, interleaved (shared
 * doublings). Scalars here are <= 64-bit (the bench uses small bit-vectors and
 * folding challenges), so 64 windows / 4-bit covers 256 bits. */
static void msm_straus(const uint64_t *Ps, const uint64_t *k, int m, uint64_t out[PT]) {
  /* m is small in the bench (<= 64); cap the table store. */
  static uint64_t T[64][16][PT];
  for (int i = 0; i < m; i++) {
    /* T[i][0] = identity; T[i][1] = P_i; T[i][e] = T[i][e-1] + P_i */
    mk_inf(T[i][0]);
    memcpy(T[i][1], Ps + PT * i, PT * sizeof(uint64_t));
    for (int e = 2; e < 16; e++) point_add(T[i][e], T[i][e - 1], (uint64_t*)Ps + PT * i);
  }
  uint64_t Q[PT], sel[PT];
  mk_inf(Q);
  for (int w = 63; w >= 0; w--) {
    point_double(Q, Q);
    point_double(Q, Q);
    point_double(Q, Q);
    point_double(Q, Q);
    for (int i = 0; i < m; i++) {
      uint64_t digit = (w < 16) ? ((k[i] >> (4 * w)) & 0xf) : 0; /* k[i] <= 64-bit */
      ct_select_point(sel, (const uint64_t (*)[PT])T[i], digit);
      point_add(Q, Q, sel);
    }
  }
  memcpy(out, Q, PT * sizeof(uint64_t));
}

/* Bulletproofs A commitment basis pack: k = [aL | aR] over Gen[0..2n). */
#define N    32
#define G2N  (2 * N)

int main(void) {
  uint64_t B[PT];
  uint8_t base[32]; memcpy(base, ED25519_BASE_COMP, 32);
  if (!decompress(B, base)) { printf("basepoint decompress FAIL\n"); return 1; }

  /* 2n=64 Pedersen generators G_i = (1+i)*B (same as ipa_prover_prod_kat.c) */
  static uint64_t Gen2n[PT * G2N];
  for (int i = 0; i < G2N; i++) {
    uint8_t s[32]; set_scalar(s, (uint64_t)(1 + i));
    point_mul(Gen2n + PT * i, s, B);
  }

  /* witness: 32-bit value bit decomposition (same secret as the dalek bench) */
  const uint64_t value = 1037578891u;
  uint64_t k[G2N];
  for (int i = 0; i < N; i++) {
    uint64_t bit = (value >> i) & 1u;
    k[i]     = bit;            /* a_L */
    k[N + i] = bit ? 0 : 1;    /* a_R */
  }

  /* ===== KAT: windowed MSM == per-term ladder MSM (the #377/#370 oracle) ===== */
  int kat_ok = 1;
  {
    uint64_t L[PT], S[PT];
    msm_ladder(Gen2n, k, G2N, L);
    msm_straus(Gen2n, k, G2N, S);
    if (!point_eq(L, S)) kat_ok = 0;
    printf("  KAT straus==ladder (64-term A commitment)  : %s\n", point_eq(L, S) ? "PASS" : "FAIL");

    /* second case: blinding-style scalars */
    uint64_t k2[G2N];
    for (int i = 0; i < N; i++) { k2[i] = (uint64_t)(7 + 3 * i); k2[N + i] = (uint64_t)(11 + 5 * i); }
    uint64_t L2[PT], S2[PT];
    msm_ladder(Gen2n, k2, G2N, L2);
    msm_straus(Gen2n, k2, G2N, S2);
    if (!point_eq(L2, S2)) kat_ok = 0;
    printf("  KAT straus==ladder (64-term S commitment)  : %s\n", point_eq(L2, S2) ? "PASS" : "FAIL");

    /* third case: a small cross-MSM length (IPA round shape, 2h terms) */
    uint64_t k3[8]; for (int i = 0; i < 8; i++) k3[i] = (uint64_t)(1 + 13 * i);
    uint64_t L3[PT], S3[PT];
    msm_ladder(Gen2n, k3, 8, L3);
    msm_straus(Gen2n, k3, 8, S3);
    if (!point_eq(L3, S3)) kat_ok = 0;
    printf("  KAT straus==ladder (8-term IPA cross MSM)  : %s\n", point_eq(L3, S3) ? "PASS" : "FAIL");
  }
  if (!kat_ok) { printf("KAT FAIL\n"); return 1; }
  printf("KAT PASS (windowed Straus MSM agrees with the per-term ladder)\n");

  /* ===== bench: a 64-term A commitment MSM, ladder vs windowed Straus ===== */
  const int M = 200;
  uint64_t sink = 0, bo[PT];
  for (int w = 0; w < 4; w++) { msm_ladder(Gen2n, k, G2N, bo); sink ^= bo[0]; }

  uint64_t t0 = rdtscp();
  for (int it = 0; it < M; it++) { k[0] = (value >> 0) & 1; msm_ladder(Gen2n, k, G2N, bo); sink ^= bo[0]; }
  uint64_t t1 = rdtscp();
  double ladder_cyc = (double)(t1 - t0) / M;

  for (int w = 0; w < 4; w++) { msm_straus(Gen2n, k, G2N, bo); sink ^= bo[0]; }
  uint64_t t2 = rdtscp();
  for (int it = 0; it < M; it++) { k[0] = (value >> 0) & 1; msm_straus(Gen2n, k, G2N, bo); sink ^= bo[0]; }
  uint64_t t3 = rdtscp();
  double straus_cyc = (double)(t3 - t2) / M;

  printf("\n64-term Ed25519 MSM (the A/S commitment workload), taskset -c 3:\n");
  printf("  per-term ladder (old path)  : %.0f cyc/MSM\n", ladder_cyc);
  printf("  windowed Straus (new path)  : %.0f cyc/MSM\n", straus_cyc);
  printf("  speedup ladder/straus       : %.2fx\n", ladder_cyc / straus_cyc);
  printf("(sink=%llu)\n", (unsigned long long)sink);
  return 0;
}
