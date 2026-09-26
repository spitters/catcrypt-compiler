/* REAL-curve MSM (closes the toy-EC MSM gap) over the VERIFIED HACL* Ed25519
 * group (Hacl_EC_Ed25519: point_mul / point_add / mk_base_point, the
 * prime-order Edwards-25519 group). This replaces the toy order-28 dlog-table
 * group of ec_leaves.jinc with a genuine 255-bit elliptic-curve scalar-mul +
 * point-add, the lane / horizontal-sum ops a Bulletproofs / Halo2-IPA / IVC
 * Pedersen-commitment MSM actually performs.
 *
 *   msm(k[], P[], n) = sum_i k_i * P_i   (point_mul lane op, point_add hsum op)
 *
 * KAT gate (soundness-relevant correctness of the real-curve leaves):
 *   1. linearity:   2*G + 3*G  ==  5*G                (MSM over base point)
 *   2. distributive: msm({2,3},{G,G}) == 5*G          (two-term MSM)
 *   3. identity:     0*G == point_at_infinity, P + inf == P
 * Point equality via the verified Hacl_EC_Ed25519_point_equal.
 *
 * Build: gcc -O2 -o msm_real_curve_kat msm_real_curve_kat.c \
 *        ../../../SSProve-lean/bench/ed25519_compare/hacl_ed25519.o ../../../SSProve-lean/bench/ed25519_compare/hacl_curve25519_51.o \
 *        ../../../SSProve-lean/bench/ed25519_compare/hacl_hash_sha2.o
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Verified HACL* Ed25519 group ops (internal Impl API; out-first arg order). */
extern void Hacl_Impl_Ed25519_PointConstants_make_point_inf(uint64_t *b);
extern void Hacl_Impl_Ed25519_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q);
extern void Hacl_Impl_Ed25519_Ladder_point_mul(uint64_t *out, uint8_t *scalar, uint64_t *q);
extern _Bool Hacl_Impl_Ed25519_PointEqual_point_equal(uint64_t *p, uint64_t *q);
extern _Bool Hacl_Impl_Ed25519_PointDecompress_point_decompress(uint64_t *out, uint8_t *s);

#define mk_inf      Hacl_Impl_Ed25519_PointConstants_make_point_inf
#define point_add   Hacl_Impl_Ed25519_PointAdd_point_add
#define point_mul   Hacl_Impl_Ed25519_Ladder_point_mul
#define point_eq    Hacl_Impl_Ed25519_PointEqual_point_equal
#define decompress  Hacl_Impl_Ed25519_PointDecompress_point_decompress

/* canonical Ed25519 base point, compressed (RFC 8032 generator, y=4/5). */
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

/* msm: out = sum_i k_i * P_i. acc starts at infinity. */
static void msm(const uint64_t *Ps, const uint64_t *ks, int n, uint64_t out[20]) {
  uint64_t acc[20], term[20];
  uint8_t s[32];
  mk_inf(acc);
  for (int i = 0; i < n; i++) {
    set_scalar(s, ks[i]);
    uint64_t Pi[20];
    memcpy(Pi, Ps + 20 * i, sizeof(Pi));
    point_mul(term, s, Pi);     /* lane op: k_i * P_i */
    point_add(acc, acc, term);  /* hsum op: acc += term */
  }
  memcpy(out, acc, 20 * sizeof(uint64_t));
}

int main(void) {
  uint64_t G[20], inf[20];
  uint8_t base[32]; memcpy(base, ED25519_BASE_COMP, 32);
  if (!decompress(G, base)) { printf("basepoint decompress FAIL\n"); return 1; }
  mk_inf(inf);

  uint8_t s2[32], s3[32], s5[32], s0[32];
  set_scalar(s2, 2); set_scalar(s3, 3); set_scalar(s5, 5); set_scalar(s0, 0);

  uint64_t G2[20], G3[20], G5[20], sum23[20], G0[20];
  point_mul(G2, s2, G);
  point_mul(G3, s3, G);
  point_mul(G5, s5, G);
  point_mul(G0, s0, G);
  point_add(sum23, G2, G3);
  int lin_ok = point_eq(sum23, G5);
  int id_ok  = point_eq(G0, inf);

  /* two-term MSM: msm({G,G},{2,3}) == 5*G */
  uint64_t Ps[40]; memcpy(Ps, G, sizeof(G)); memcpy(Ps + 20, G, sizeof(G));
  uint64_t ks[2] = {2, 3};
  uint64_t msm_out[20];
  msm(Ps, ks, 2, msm_out);
  int msm_ok = point_eq(msm_out, G5);

  /* infinity neutrality: G + inf == G */
  uint64_t Gpi[20];
  point_add(Gpi, G, inf);
  int neutral_ok = point_eq(Gpi, G);

  printf("REAL-curve MSM over verified HACL* Ed25519 (closes toy-EC MSM gap)\n");
  printf("  KAT 2*G + 3*G == 5*G            : %s\n", lin_ok ? "PASS" : "FAIL");
  printf("  KAT msm({G,G},{2,3}) == 5*G     : %s\n", msm_ok ? "PASS" : "FAIL");
  printf("  KAT 0*G == infinity             : %s\n", id_ok ? "PASS" : "FAIL");
  printf("  KAT G + inf == G                : %s\n", neutral_ok ? "PASS" : "FAIL");
  int ok = lin_ok && msm_ok && id_ok && neutral_ok;
  if (!ok) { printf("KAT FAIL\n"); return 1; }
  printf("KAT PASS\n");

  /* --- self-bench: per-term cost (one full 255-bit scalar-mul + point-add) --- */
  const int N = 4096;
  uint64_t bigP[20 * 8], bigk[8];
  for (int i = 0; i < 8; i++) { memcpy(bigP + 20 * i, G, sizeof(G)); bigk[i] = 1 + i; }
  uint64_t mo[20];
  uint64_t sink = 0;
  for (int i = 0; i < 64; i++) { bigk[0] = 1 + i; msm(bigP, bigk, 8, mo); sink ^= mo[0]; }
  uint64_t t0 = rdtscp();
  for (int i = 0; i < N; i++) { bigk[0] = 1 + (i & 1023); msm(bigP, bigk, 8, mo); sink ^= mo[0]; }
  uint64_t t1 = rdtscp();
  double per_msm = (double)(t1 - t0) / N;
  printf("real-curve MSM self-bench : %.0f cyc / 8-term MSM  (%.0f cyc/term: Ed25519 scalar-mul + point-add)\n",
         per_msm, per_msm / 8.0);
  printf("(sink=%llu)\n", (unsigned long long)sink);
  return 0;
}
