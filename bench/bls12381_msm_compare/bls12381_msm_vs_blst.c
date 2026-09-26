/* BLS12-381 G1 multi-scalar multiplication (Pippenger bucketing) composed from
 * the three landed legs, head-to-head against blst's own Pippenger MSM.
 *
 *   #490  field-mul : the IN-LEAN x86-backend CIOS Montgomery multiply
 *                     (bls12381_mont_mul_x86_from_lean, ~1.07-1.09x blst).
 *   #488  inverse   : the AUCurves Bernstein-Yang safegcd divstep inverse
 *                     (bls12_invert_divstep_sat, ~1.10x blst_fp_inverse).
 *   #481  batch-inv : Montgomery's trick in the affine-conversion path
 *                     (1 inverse + 3(n-1) muls instead of n inverses).
 *
 * The composed MSM runs a real Pippenger bucket accumulation over a
 * Jacobian G1 group law whose EVERY field multiply/square is the lean x86
 * kernel and whose ONE batched inversion (final bucket-window normalisation
 * is kept Jacobian; affine batch conversion is exercised separately and
 * KAT'd) is the safegcd leaf.  Field add/sub use blst's (cheap, not the leg
 * we are matching) so the composition is not advantaged there.
 *
 * Oracle (NO fabricated vectors): blst_p1s_mult_pippenger over the SAME
 * (points, scalars).  Points are real scalar multiples of the standard
 * BLS12-381 G1 generator (blst_p1_generator + blst_p1_mult); scalars are a
 * deterministic xorshift stream reduced mod r.  The MSM result is compared
 * byte-identically on the 96-byte uncompressed serialisation.
 *
 * Domain: a blst_fp is canonical-value-in-Montgomery-form 6xu64 LE.  The lean
 * kernel operates on exactly those bytes (the #490 KAT proves
 * bls12381_mont_mul_x86_from_lean == blst_fp_mul byte-for-byte).  The safegcd
 * leaf operates on canonical limbs, so the inverse is bracketed by blst's
 * Montgomery<->canonical maps.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "blst.h"
#include "bls12_381_safegcd_ref.h"   /* bls12_381_safegcd_invert (AUCurves leaf) */
#include "tscbench.h"
#include "affinity.h"

/* ---- the lean x86-backend field multiply (gen_com .s leaf) ------------ */
extern void bls12381_mont_mul_x86_from_lean(uint64_t *z, const uint64_t *x,
                                            const uint64_t *y);

/* ---- Fp layer: blst_fp bytes, lean kernel for mul/sqr ----------------- */
typedef blst_fp Fp;

static uint64_t g_fpmul = 0, g_fpsqr = 0, g_fpinv = 0; /* op counters */

static inline void fp_mul(Fp *z, const Fp *x, const Fp *y) {
  bls12381_mont_mul_x86_from_lean(z->l, x->l, y->l); g_fpmul++;
}
static inline void fp_sqr(Fp *z, const Fp *x) {
  bls12381_mont_mul_x86_from_lean(z->l, x->l, x->l); g_fpsqr++;
}
static inline void fp_add(Fp *z, const Fp *x, const Fp *y) { blst_fp_add(z, x, y); }
static inline void fp_sub(Fp *z, const Fp *x, const Fp *y) { blst_fp_sub(z, x, y); }
static inline void fp_neg(Fp *z, const Fp *x) { blst_fp_cneg(z, x, true); }

/* safegcd inverse, bracketed by blst's Montgomery<->canonical maps. */
static inline void fp_inv(Fp *z, const Fp *x) {
  uint64_t canon[6], inv[6];
  blst_uint64_from_fp(canon, x);
  bls12_381_safegcd_invert(inv, canon);
  blst_fp_from_uint64(z, inv);
  g_fpinv++;
}

static int fp_is_zero(const Fp *x) {
  for (int i = 0; i < 6; i++) if (x->l[i]) return 0;
  return 1;
}
static int fp_eq(const Fp *a, const Fp *b) {
  for (int i = 0; i < 6; i++) if (a->l[i] != b->l[i]) return 0;
  return 1;
}

/* ---- G1 in Jacobian coordinates over the composed Fp ------------------ */
/* point at infinity := Z == 0. */
typedef struct { Fp X, Y, Z; } G1;

static const Fp FP_ZERO = {{0,0,0,0,0,0}};
/* the Montgomery field one (R mod p), captured from blst's generator Z in main. */
static Fp g_fp_one;

static void g1_set_inf(G1 *p) { p->X = FP_ZERO; p->Y = FP_ZERO; p->Z = FP_ZERO; }
static int  g1_is_inf(const G1 *p) { return fp_is_zero(&p->Z); }

/* dbl-2009-l (cost 2M + 5S + ... ), curve a = 0 (BLS12-381 y^2=x^3+4). */
static void g1_double(G1 *r, const G1 *p) {
  if (g1_is_inf(p) || fp_is_zero(&p->Y)) { g1_set_inf(r); return; }
  Fp A, B, C, D, E, F, Z3, t, t2;
  fp_sqr(&A, &p->X);                 /* A = X^2 */
  fp_sqr(&B, &p->Y);                 /* B = Y^2 */
  fp_sqr(&C, &B);                    /* C = B^2 */
  /* Z3 = 2*Y*Z — computed FIRST so it survives r==p aliasing. */
  fp_mul(&t, &p->Y, &p->Z); fp_add(&Z3, &t, &t);
  /* D = 2*((X+B)^2 - A - C) */
  fp_add(&t, &p->X, &B); fp_sqr(&t, &t);
  fp_sub(&t, &t, &A); fp_sub(&t, &t, &C);
  fp_add(&D, &t, &t);
  /* E = 3*A */
  fp_add(&E, &A, &A); fp_add(&E, &E, &A);
  fp_sqr(&F, &E);                    /* F = E^2 */
  /* X3 = F - 2*D */
  fp_add(&t, &D, &D); fp_sub(&r->X, &F, &t);
  /* Y3 = E*(D - X3) - 8*C */
  fp_sub(&t, &D, &r->X); fp_mul(&t, &E, &t);
  fp_add(&t2, &C, &C); fp_add(&t2, &t2, &t2); fp_add(&t2, &t2, &t2); /* 8C */
  fp_sub(&r->Y, &t, &t2);
  r->Z = Z3;
}

/* add-2007-bl (Jacobian + Jacobian), generic. */
static void g1_add(G1 *r, const G1 *p, const G1 *q) {
  if (g1_is_inf(p)) { *r = *q; return; }
  if (g1_is_inf(q)) { *r = *p; return; }
  Fp Z1Z1, Z2Z2, U1, U2, S1, S2, H, I, J, rr, V, t, t2;
  fp_sqr(&Z1Z1, &p->Z);              /* Z1Z1 = Z1^2 */
  fp_sqr(&Z2Z2, &q->Z);              /* Z2Z2 = Z2^2 */
  fp_mul(&U1, &p->X, &Z2Z2);         /* U1 = X1*Z2Z2 */
  fp_mul(&U2, &q->X, &Z1Z1);         /* U2 = X2*Z1Z1 */
  fp_mul(&t, &q->Z, &Z2Z2); fp_mul(&S1, &p->Y, &t);   /* S1 = Y1*Z2*Z2Z2 */
  fp_mul(&t, &p->Z, &Z1Z1); fp_mul(&S2, &q->Y, &t);   /* S2 = Y2*Z1*Z1Z1 */
  if (fp_eq(&U1, &U2)) {
    if (fp_eq(&S1, &S2)) { g1_double(r, p); return; }
    g1_set_inf(r); return;            /* P = -Q */
  }
  fp_sub(&H, &U2, &U1);               /* H = U2 - U1 */
  fp_add(&I, &H, &H); fp_sqr(&I, &I); /* I = (2H)^2 */
  fp_mul(&J, &H, &I);                 /* J = H*I */
  fp_sub(&rr, &S2, &S1); fp_add(&rr, &rr, &rr); /* r = 2*(S2-S1) */
  fp_mul(&V, &U1, &I);                /* V = U1*I */
  /* X3 = r^2 - J - 2V */
  fp_sqr(&t, &rr); fp_sub(&t, &t, &J);
  fp_add(&t2, &V, &V); fp_sub(&r->X, &t, &t2);
  /* Y3 = r*(V - X3) - 2*S1*J */
  fp_sub(&t, &V, &r->X); fp_mul(&t, &rr, &t);
  fp_mul(&t2, &S1, &J); fp_add(&t2, &t2, &t2);
  fp_sub(&r->Y, &t, &t2);
  /* Z3 = ((Z1+Z2)^2 - Z1Z1 - Z2Z2)*H */
  fp_add(&t, &p->Z, &q->Z); fp_sqr(&t, &t);
  fp_sub(&t, &t, &Z1Z1); fp_sub(&t, &t, &Z2Z2);
  fp_mul(&r->Z, &t, &H);
}

/* mixed add: q affine (Zq == 1 implicit). madd-2007-bl. */
static void g1_add_affine(G1 *r, const G1 *p, const Fp *qx, const Fp *qy) {
  if (g1_is_inf(p)) { r->X = *qx; r->Y = *qy; r->Z = g_fp_one; return; }
  Fp Z1Z1, U2, S2, H, HH, I, J, rr, V, t, t2;
  fp_sqr(&Z1Z1, &p->Z);
  fp_mul(&U2, qx, &Z1Z1);
  fp_mul(&t, &p->Z, &Z1Z1); fp_mul(&S2, qy, &t);
  if (fp_eq(&p->X, &U2)) {
    if (fp_eq(&p->Y, &S2)) { g1_double(r, p); return; }
    g1_set_inf(r); return;
  }
  fp_sub(&H, &U2, &p->X);
  fp_sqr(&HH, &H);
  fp_add(&I, &HH, &HH); fp_add(&I, &I, &I);    /* I = 4*HH */
  fp_mul(&J, &H, &I);
  fp_sub(&rr, &S2, &p->Y); fp_add(&rr, &rr, &rr);
  fp_mul(&V, &p->X, &I);
  fp_sqr(&t, &rr); fp_sub(&t, &t, &J);
  fp_add(&t2, &V, &V); fp_sub(&r->X, &t, &t2);
  fp_sub(&t, &V, &r->X); fp_mul(&t, &rr, &t);
  fp_mul(&t2, &p->Y, &J); fp_add(&t2, &t2, &t2);
  fp_sub(&r->Y, &t, &t2);
  /* Z3 = (Z1 + H)^2 - Z1Z1 - HH  (= 2*Z1*H; NO extra *H — madd-2007-bl). */
  fp_add(&t, &p->Z, &H); fp_sqr(&t, &t);
  fp_sub(&t, &t, &Z1Z1); fp_sub(&r->Z, &t, &HH);
}

/* ---- Jacobian -> affine, single point (Montgomery's trick is for many) - */
static void g1_to_affine(Fp *ax, Fp *ay, const G1 *p) {
  if (g1_is_inf(p)) { *ax = FP_ZERO; *ay = FP_ZERO; return; }
  Fp zinv, zinv2, zinv3;
  fp_inv(&zinv, &p->Z);
  fp_sqr(&zinv2, &zinv);
  fp_mul(&zinv3, &zinv2, &zinv);
  fp_mul(ax, &p->X, &zinv2);
  fp_mul(ay, &p->Y, &zinv3);
}

/* Montgomery's trick: invert n field elements with 1 inverse + 3(n-1) muls.
   Exercised by the affine batch-conversion KAT/bench below. */
static void batch_inv(Fp *out, const Fp *in, int n) {
  if (n <= 0) return;
  Fp *prefix = malloc((size_t)(n + 1) * sizeof(Fp));
  prefix[0] = g_fp_one;
  for (int i = 0; i < n; i++) fp_mul(&prefix[i + 1], &prefix[i], &in[i]);
  Fp u; fp_inv(&u, &prefix[n]);              /* the ONE inverse */
  for (int i = n - 1; i >= 0; i--) {
    fp_mul(&out[i], &u, &prefix[i]);
    Fp nu; fp_mul(&nu, &u, &in[i]); u = nu;
  }
  free(prefix);
}

/* ---- Pippenger bucketing (signed-digit windows), composed Fp ---------- */
/* scalar layout: 32-byte LE (256 bits; r is 255 bits). */
#define NBITS 255

static inline int get_bits(const uint8_t *s, int off, int w) {
  /* extract w bits starting at bit `off`, little-endian; bits >= 256 read as
     0 (no over-read of the 32-byte scalar). */
  uint32_t v = 0;
  for (int k = 0; k < w; k++) {
    int bitpos = off + k;
    if (bitpos >= 256) break;
    uint32_t b = (uint32_t)((s[bitpos >> 3] >> (bitpos & 7)) & 1);
    v |= b << k;
  }
  return (int)v;
}

/* balanced Pippenger window: minimise (n + 2^w) per window over nwin windows.
   The bucket-reduction sweep is ~2^w point-adds/window, the accumulation ~n;
   the textbook balance is w ~ floor(log2 n) - a few, picked empirically here to
   match the measured cost surface (the empty-bucket sweep dominates at large
   w, so a smaller window than the naive log2(n) wins). */
static int pippenger_window(int n) {
  int w = 1;
  while ((1 << (w + 1)) <= n) w++;       /* w = floor(log2 n) */
  w -= 2;                                 /* signed-digit halves bucket cost */
  if (w < 2) w = 2;
  if (w > 14) w = 14;
  return w;
}

/* Signed-digit (booth-style) recoding of one scalar into `nwin` windows of
   `wbits` bits each, digits in [-2^(w-1), 2^(w-1)].  Halves the bucket count
   (only |digit| up to 2^(w-1) is bucketed) and the per-window accumulation —
   the same lever blst's Pippenger uses.  Carry propagates low->high. */
static void recode_signed(int16_t *digits, const uint8_t *s, int wbits, int nwin) {
  int half = 1 << (wbits - 1);
  int full = 1 << wbits;
  int carry = 0;
  for (int w = 0; w < nwin; w++) {
    int d = get_bits(s, w * wbits, wbits) + carry;
    if (d >= half) { d -= full; carry = 1; } else carry = 0;
    digits[w] = (int16_t)d;
  }
}

/* accumulate sum_i scalar_i * P_i into ret over wbits-wide signed-digit windows.
   Buckets are indexed by |digit| in [1, 2^(w-1)]; a negative digit adds -P_i
   (Y-negated affine).  ret is built high->low with wbits doublings per step. */
static void pippenger(G1 *ret, const Fp *px, const Fp *py, const uint8_t *scalars,
                      int n, int wbits) {
  int nwin = (NBITS + 1 + wbits - 1) / wbits;     /* +1 bit of recoding headroom */
  int half = 1 << (wbits - 1);
  G1 *buckets = malloc((size_t)(half + 1) * sizeof(G1));
  int16_t *digits = malloc((size_t)n * nwin * sizeof(int16_t));
  for (int i = 0; i < n; i++)
    recode_signed(&digits[(size_t)i * nwin], &scalars[(size_t)i * 32], wbits, nwin);

  g1_set_inf(ret);
  for (int w = nwin - 1; w >= 0; w--) {
    for (int d = 0; d < wbits; d++) g1_double(ret, ret);
    for (int b = 0; b <= half; b++) g1_set_inf(&buckets[b]);
    int hi = 0;
    for (int i = 0; i < n; i++) {
      int d = digits[(size_t)i * nwin + w];
      if (d > 0) {
        g1_add_affine(&buckets[d], &buckets[d], &px[i], &py[i]);
        if (d > hi) hi = d;
      } else if (d < 0) {
        int a = -d; Fp ny; fp_neg(&ny, &py[i]);
        g1_add_affine(&buckets[a], &buckets[a], &px[i], &ny);
        if (a > hi) hi = a;
      }
    }
    G1 acc, sum; g1_set_inf(&acc); g1_set_inf(&sum);
    for (int b = hi; b >= 1; b--) {
      if (!g1_is_inf(&buckets[b])) g1_add(&acc, &acc, &buckets[b]);
      g1_add(&sum, &sum, &acc);
    }
    g1_add(ret, ret, &sum);
  }
  free(buckets); free(digits);
}

/* ---- harness ---------------------------------------------------------- */
/* r (BLS12-381 scalar field order) LE limbs, for reducing the scalar stream. */
static uint64_t rng = 0x9E3779B97F4A7C15ULL;
static inline uint64_t xrand(void) {
  rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
  return rng * 0x2545F4914F6CDD1DULL;
}

static void serialize_g1(uint8_t out[96], const G1 *p) {
  Fp ax, ay; g1_to_affine(&ax, &ay, p);
  blst_p1 bp;
  bp.x = ax; bp.y = ay;
  bp.z = g1_is_inf(p) ? FP_ZERO : g_fp_one;
  blst_p1_serialize(out, &bp);
}

int main(int argc, char **argv) {
  setvbuf(stdout, NULL, _IONBF, 0);
  long reps = (argc > 1) ? atol(argv[1]) : 1;   /* <=1 => KAT only */
  int wbits = (argc > 2) ? atoi(argv[2]) : 0;   /* 0 => auto per n */
  pin_to_cpu(3);

  /* capture the Montgomery field one (R mod p) from blst's generator Z. */
  g_fp_one = blst_p1_generator()->z;

  const int sizes[] = {256, 1024, 4096};
  const int nsizes = 3;
  int maxn = sizes[nsizes - 1];

  /* build real test points = i'th generator multiple, deterministic scalars. */
  Fp *px = malloc((size_t)maxn * sizeof(Fp));
  Fp *py = malloc((size_t)maxn * sizeof(Fp));
  uint8_t *scalars = malloc((size_t)maxn * 32);
  const blst_p1 *gen = blst_p1_generator();
  for (int i = 0; i < maxn; i++) {
    /* point P_i = (i+1) * G  (real generator multiples, NOT fabricated). */
    blst_p1 pi;
    uint8_t e[32]; memset(e, 0, 32);
    uint64_t k = (uint64_t)(i + 1);
    memcpy(e, &k, 8);
    blst_p1_mult(&pi, gen, e, 64);
    blst_p1_affine af; blst_p1_to_affine(&af, &pi);
    px[i] = af.x; py[i] = af.y;
    /* scalar_i: xorshift stream, then reduce into the scalar field. */
    uint8_t sc[32];
    for (int j = 0; j < 32; j += 8) { uint64_t w = xrand(); memcpy(sc + j, &w, 8); }
    /* reduce the 256-bit stream mod r via blst_fr round-trip. */
    blst_scalar bs; blst_scalar_from_lendian(&bs, sc);
    blst_fr fr; blst_fr_from_scalar(&fr, &bs);
    blst_scalar_from_fr(&bs, &fr);
    blst_lendian_from_scalar(scalars + (size_t)i * 32, &bs);
  }

  int total_fail = 0;
  for (int si = 0; si < nsizes; si++) {
    int n = sizes[si];
    int w = wbits ? wbits : pippenger_window(n);

    /* ---- KAT: composed MSM == blst Pippenger MSM ---- */
    g_fpmul = g_fpsqr = g_fpinv = 0;
    G1 ours; pippenger(&ours, px, py, scalars, n, w);
    uint8_t our_ser[96]; serialize_g1(our_ser, &ours);
    uint64_t ops_mul = g_fpmul, ops_sqr = g_fpsqr, ops_inv = g_fpinv;

    /* blst oracle. */
    blst_p1_affine *aff = malloc((size_t)n * sizeof(blst_p1_affine));
    const blst_p1_affine **affp = malloc((size_t)n * sizeof(blst_p1_affine *));
    const uint8_t **scp = malloc((size_t)n * sizeof(uint8_t *));
    for (int i = 0; i < n; i++) {
      aff[i].x = px[i]; aff[i].y = py[i];
      affp[i] = &aff[i];
      scp[i] = scalars + (size_t)i * 32;
    }
    size_t scratch_sz = blst_p1s_mult_pippenger_scratch_sizeof((size_t)n);
    limb_t *scratch = malloc(scratch_sz);
    blst_p1 bref;
    blst_p1s_mult_pippenger(&bref, affp, (size_t)n, scp, NBITS, scratch);
    uint8_t ref_ser[96]; blst_p1_serialize(ref_ser, &bref);

    int ok = (memcmp(our_ser, ref_ser, 96) == 0);
    printf("KAT n=%-5d w=%-2d : composed-MSM %s blst_p1s_mult_pippenger  "
           "(fp_mul=%llu fp_sqr=%llu fp_inv=%llu, ~%.1f mul-eq/point)\n",
           n, w, ok ? "==" : "!=",
           (unsigned long long)ops_mul, (unsigned long long)ops_sqr,
           (unsigned long long)ops_inv,
           (double)(ops_mul + ops_sqr) / n);
    if (!ok) {
      total_fail++;
      fprintf(stderr, "  ours="); for (int k=0;k<96;k++) fprintf(stderr,"%02x",our_ser[k]); fprintf(stderr,"\n");
      fprintf(stderr, "  blst="); for (int k=0;k<96;k++) fprintf(stderr,"%02x",ref_ser[k]); fprintf(stderr,"\n");
    }

    /* ---- bench (only if KAT passed and reps>1) ---- */
    if (reps > 1 && ok) {
      uint64_t best_ours = ~0ULL, best_blst = ~0ULL;
      for (int s = 0; s < 5; s++) {
        uint64_t c0 = rdtsc_start();
        for (long r = 0; r < reps; r++) { G1 t; pippenger(&t, px, py, scalars, n, w);
          /* defeat DCE */ if (t.X.l[0] == 0xdeadbeef) total_fail++; }
        uint64_t c1 = rdtsc_end();
        uint64_t d = (c1 - c0); if (d < best_ours) best_ours = d;
      }
      for (int s = 0; s < 5; s++) {
        uint64_t c0 = rdtsc_start();
        for (long r = 0; r < reps; r++) { blst_p1 t;
          blst_p1s_mult_pippenger(&t, affp, (size_t)n, scp, NBITS, scratch);
          if (t.x.l[0] == 0xdeadbeef) total_fail++; }
        uint64_t c1 = rdtsc_end();
        uint64_t d = (c1 - c0); if (d < best_blst) best_blst = d;
      }
      double cyc_ours = (double)best_ours / reps;
      double cyc_blst = (double)best_blst / reps;
      printf("  bench n=%-5d : composed %12.0f cyc/MSM (%9.1f cyc/point) | "
             "blst %12.0f cyc/MSM (%9.1f cyc/point) | ratio %.3fx\n",
             n, cyc_ours, cyc_ours / n, cyc_blst, cyc_blst / n,
             cyc_ours / cyc_blst);
    }

    free(aff); free(affp); free(scp); free(scratch);
  }

  /* ---- batch-inversion (#481) KAT: Montgomery's trick == per-point inv ---- */
  {
    int n = 64;
    Fp *xs = malloc((size_t)n * sizeof(Fp));
    Fp *bt = malloc((size_t)n * sizeof(Fp));
    Fp *pp = malloc((size_t)n * sizeof(Fp));
    for (int i = 0; i < n; i++) xs[i] = px[i];        /* real field elements */
    batch_inv(bt, xs, n);
    for (int i = 0; i < n; i++) fp_inv(&pp[i], &xs[i]);
    int bok = 1;
    for (int i = 0; i < n; i++) if (!fp_eq(&bt[i], &pp[i])) bok = 0;
    printf("KAT batch-inv  : Montgomery's trick (1 safegcd inv + %d fp_mul) %s "
           "per-point (%d safegcd inv)\n", 3 * (n - 1), bok ? "==" : "!=", n);
    if (!bok) total_fail++;
    free(xs); free(bt); free(pp);
  }

  free(px); free(py); free(scalars);
  if (total_fail) { printf("\nFAILED (%d)\n", total_fail); return 1; }
  printf("\nALL KAT PASSED.\n");
  return 0;
}
