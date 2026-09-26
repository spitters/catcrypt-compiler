/*
 * Reference schoolbook affine elliptic-curve arithmetic over the toy field
 * Fp = Z/23, curve y^2 = x^3 + a*x + b with (a,b) = (1,1).  This mirrors the
 * Lean toy EC group MsmReduce.toyW (a=1, b=1 over ZMod 23), whose nonsingular
 * affine points carry Mathlib's proved AddCommGroup (the AddCommMonoid lane the
 * MSM = scalarFold reduction runs over).
 *
 *   Repr:   a curve point is two bytes (x, y), 0 <= x,y < 23.
 *           The point at infinity (the group identity / 0) is (0xff, 0xff).
 *   Group:  28 points, cyclic, generator G = (0, 1) of order 28.
 *
 * Used as the INDEPENDENT oracle for the emitted ec_msm kernel KAT: this is the
 * mathematical multi-scalar multiplication Sum_i k_i * P_i, computed by a
 * straightforward reference loop (schoolbook double-and-add scalar-mul +
 * schoolbook affine point-add), cross-checked byte-identical against the
 * emitted-and-leaf-linked kernel.  These same two routines (point_add /
 * scalar_mul) ALSO back the ec_point_add / ec_scalar_mul leaves the emitted
 * ec_msm.jazz calls (ec_leaves.c), so the leaf agreement EcLeafAgrees is
 * discharged operationally here.
 *
 * The production analogue is the AUCurves/fiat BLS12-381 G1 leaves
 * (scalar_mul / g1_add, wired in CatCrypt/Crypto/{KZG,ECDSA}) at a 381-bit
 * field; we pin the reduction at this small field so the emitted kernel and the
 * reference are byte-identical without dragging in the 381-bit fiat machinery.
 */
#ifndef EC_REF_H
#define EC_REF_H
#include <stdint.h>
#include <string.h>

#define EC_P    23
#define EC_A    1
#define EC_B    1
#define EC_INF  0xff   /* point-at-infinity sentinel byte (both coords) */

/* a point on the wire: two bytes (x, y); (0xff,0xff) = infinity. */
typedef struct { uint8_t x, y; } ec_point;

static inline int ec_is_inf(ec_point P) { return P.x == EC_INF && P.y == EC_INF; }
static inline ec_point ec_inf(void) { ec_point R = { EC_INF, EC_INF }; return R; }

/* modular inverse mod EC_P via Fermat (EC_P is prime). */
static inline uint8_t ec_inv(uint8_t a) {
  int base = a % EC_P, result = 1, e = EC_P - 2;
  while (e > 0) {
    if (e & 1) result = (result * base) % EC_P;
    base = (base * base) % EC_P;
    e >>= 1;
  }
  return (uint8_t)result;
}

/* R = P + Q, schoolbook affine addition (the EC point-add leaf). */
static inline ec_point ec_point_add_ref(ec_point P, ec_point Q) {
  if (ec_is_inf(P)) return Q;
  if (ec_is_inf(Q)) return P;
  int x1 = P.x, y1 = P.y, x2 = Q.x, y2 = Q.y;
  if (x1 == x2 && (y1 + y2) % EC_P == 0) return ec_inf();  /* P = -Q */
  int lam;
  if (x1 == x2 && y1 == y2) {
    /* doubling: lam = (3 x1^2 + a) / (2 y1) */
    int num = (3 * x1 * x1 + EC_A) % EC_P;
    lam = (num * ec_inv((uint8_t)((2 * y1) % EC_P))) % EC_P;
  } else {
    /* chord: lam = (y2 - y1) / (x2 - x1) */
    int num = ((y2 - y1) % EC_P + EC_P) % EC_P;
    int den = ((x2 - x1) % EC_P + EC_P) % EC_P;
    lam = (num * ec_inv((uint8_t)den)) % EC_P;
  }
  int x3 = ((lam * lam - x1 - x2) % EC_P + EC_P) % EC_P;
  int y3 = ((lam * (x1 - x3) - y1) % EC_P + EC_P) % EC_P;
  ec_point R = { (uint8_t)x3, (uint8_t)y3 };
  return R;
}

/* R = k * P, schoolbook double-and-add (the EC scalar-mul leaf). */
static inline ec_point ec_scalar_mul_ref(uint8_t k, ec_point P) {
  ec_point R = ec_inf();
  ec_point base = P;
  while (k) {
    if (k & 1) R = ec_point_add_ref(R, base);
    base = ec_point_add_ref(base, base);
    k >>= 1;
  }
  return R;
}

/* out = Sum_{i=0}^{L-1} k_i * P_i  over the curve group (the MSM).
 * ks[i] is the i-th scalar byte; ps[2 i], ps[2 i + 1] are P_i = (x_i, y_i). */
static inline void ec_msm_ref(const uint8_t *ks, const uint8_t *ps, int L, uint8_t out[2]) {
  ec_point acc = ec_inf();
  for (int i = 0; i < L; i++) {
    ec_point Pi = { ps[2 * i], ps[2 * i + 1] };
    ec_point term = ec_scalar_mul_ref(ks[i], Pi);
    acc = ec_point_add_ref(acc, term);
  }
  out[0] = acc.x;
  out[1] = acc.y;
}

#endif /* EC_REF_H */
