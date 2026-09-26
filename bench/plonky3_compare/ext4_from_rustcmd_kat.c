/* KAT for the EMITTED deg-4 extension-field FRI kernels: the front-generated,
 * proved kernels bb_ext4_mul_c0..c3 and bb_ext4_fold_c0..c3
 * (BinomialExt4.mulJasmin / foldJasmin, correctness theorems
 * babyBear_mulJasmin_spec / babyBear_foldJasmin_spec), the hand-authored
 * ext4_mul_c0..c3_rc (cross-checked against the proved multiply) and
 * ext4_scale_rc, byte-identical to the p3 reference
 * BinomialExtensionField<BabyBear,4> arithmetic (x^4 = 11) — the SAME emul /
 * escale / einv schedule p3_accept_prove.c runs (transcribed from p3's
 * BinomialExtensionField). The einv (Frobenius/norm inverse) is composed here
 * from the emitted ext-mul + scale leaves and the emitted base-field bb_inv_rc
 * (finv of the norm).
 *
 * Build:
 *   cc -O2 -o ext4_from_rustcmd_kat ext4_from_rustcmd_kat.c \
 *      gen_com/ext4_from_rustcmd_owned.s gen_com/fri_fold_from_rustcmd_owned.s
 *   ./ext4_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>

#define P 2013265921ULL
#define EXT_W 11ULL

/* ---- EMITTED ext-field leaves (ext4_from_rustcmd_owned.s) ---- */
extern uint64_t *ext4_mul_c0_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *ext4_mul_c1_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *ext4_mul_c2_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *ext4_mul_c3_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *ext4_scale_rc(uint64_t *out, const uint64_t *inp);
/* ---- front-generated proved kernels (same .s); input i at inp[i] ---- */
extern uint64_t *bb_ext4_mul_c0(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_mul_c1(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_mul_c2(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_mul_c3(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_fold_c0(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_fold_c1(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_fold_c2(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_fold_c3(uint64_t *out, const uint64_t *inp);
/* ---- EMITTED base-field inverse (fri_fold_from_rustcmd_owned.s) ---- */
extern uint64_t *bb_inv_rc(uint64_t *out, const uint64_t *inp);

/* ---- C reference (byte-for-byte p3_accept_prove.c) ---- */
static inline uint64_t fadd(uint64_t a, uint64_t b){ uint64_t s=a+b; return s>=P?s-P:s; }
static inline uint64_t fsub(uint64_t a, uint64_t b){ return a>=b?a-b:a+P-b; }
static inline uint64_t fmul(uint64_t a, uint64_t b){ return (a*b)%P; }
static uint64_t fpow(uint64_t b, uint64_t e){ uint64_t r=1; b%=P; while(e){ if(e&1)r=fmul(r,b); b=fmul(b,b); e>>=1; } return r; }
static uint64_t finv(uint64_t a){ return fpow(a,P-2); }
typedef struct { uint64_t c[4]; } E;
static E eadd(E a,E b){ E r; for(int i=0;i<4;i++) r.c[i]=fadd(a.c[i],b.c[i]); return r; }
static E escale_ref(E a,uint64_t s){ E r; for(int i=0;i<4;i++) r.c[i]=fmul(a.c[i],s); return r; }
static E emul_ref(E a,E b){
  E r;
  r.c[0]=fadd(fmul(a.c[0],b.c[0]), fmul(EXT_W, fadd(fadd(fmul(a.c[1],b.c[3]),fmul(a.c[2],b.c[2])),fmul(a.c[3],b.c[1]))));
  r.c[1]=fadd(fadd(fmul(a.c[0],b.c[1]),fmul(a.c[1],b.c[0])), fmul(EXT_W, fadd(fmul(a.c[2],b.c[3]),fmul(a.c[3],b.c[2]))));
  r.c[2]=fadd(fadd(fadd(fmul(a.c[0],b.c[2]),fmul(a.c[1],b.c[1])),fmul(a.c[2],b.c[0])), fmul(EXT_W, fmul(a.c[3],b.c[3])));
  r.c[3]=fadd(fadd(fadd(fmul(a.c[0],b.c[3]),fmul(a.c[1],b.c[2])),fmul(a.c[2],b.c[1])),fmul(a.c[3],b.c[0]));
  return r;
}
static E efrob_ref(E a){
  static uint64_t f1=0; if(!f1) f1=fpow(EXT_W,(P-1)/4);
  E r; uint64_t s=1; for(int i=0;i<4;i++){ r.c[i]=fmul(a.c[i],s); s=fmul(s,f1); } return r;
}
static E einv_ref(E a){
  E b=efrob_ref(a), c=efrob_ref(b), d=efrob_ref(c);
  E t=emul_ref(b,emul_ref(c,d));
  E n=emul_ref(a,t);
  return escale_ref(t, finv(n.c[0]));
}

/* fold reference: (lo + hi) * inv2 + beta * ((lo - hi) * hip), inv2 = 2^{-1} */
static E efold_ref(E lo, E hi, E beta, uint64_t hip){
  uint64_t inv2=finv(2); E d, s;
  for(int i=0;i<4;i++){ d.c[i]=fmul(fsub(lo.c[i],hi.c[i]),hip); s.c[i]=fmul(fadd(lo.c[i],hi.c[i]),inv2); }
  return eadd(s, emul_ref(beta,d));
}

/* ---- EMITTED wrappers ---- */
/* proved multiply: a0..a3 -> inp[0..3], b0..b3 -> inp[4..7] */
static E emul_emit(E a, E b){
  uint64_t inp[8], o[1]; E r;
  for(int i=0;i<4;i++){ inp[i]=a.c[i]; inp[4+i]=b.c[i]; }
  bb_ext4_mul_c0(o,inp); r.c[0]=o[0];
  bb_ext4_mul_c1(o,inp); r.c[1]=o[0];
  bb_ext4_mul_c2(o,inp); r.c[2]=o[0];
  bb_ext4_mul_c3(o,inp); r.c[3]=o[0];
  return r;
}
/* proved fold: lo -> inp[0..3], hi -> inp[4..7], beta -> inp[8..11], hip -> inp[12] */
static E efold_emit(E lo, E hi, E beta, uint64_t hip){
  uint64_t inp[13], o[1]; E r;
  for(int i=0;i<4;i++){ inp[i]=lo.c[i]; inp[4+i]=hi.c[i]; inp[8+i]=beta.c[i]; }
  inp[12]=hip;
  bb_ext4_fold_c0(o,inp); r.c[0]=o[0];
  bb_ext4_fold_c1(o,inp); r.c[1]=o[0];
  bb_ext4_fold_c2(o,inp); r.c[2]=o[0];
  bb_ext4_fold_c3(o,inp); r.c[3]=o[0];
  return r;
}
/* hand-authored multiply: a0..a3 -> 0,1,2,3 ; b0,b1 -> 4,5 ; b2,b3 -> 13,14 ; W -> 15 */
static E emul_rc(E a, E b){
  uint64_t inp[16], o[1]; E r;
  for(int i=0;i<16;i++) inp[i]=0;
  inp[0]=a.c[0]; inp[1]=a.c[1]; inp[2]=a.c[2]; inp[3]=a.c[3];
  inp[4]=b.c[0]; inp[5]=b.c[1]; inp[13]=b.c[2]; inp[14]=b.c[3];
  inp[15]=EXT_W;
  ext4_mul_c0_rc(o,inp); r.c[0]=o[0];
  ext4_mul_c1_rc(o,inp); r.c[1]=o[0];
  ext4_mul_c2_rc(o,inp); r.c[2]=o[0];
  ext4_mul_c3_rc(o,inp); r.c[3]=o[0];
  return r;
}
static uint64_t scale1_emit(uint64_t x, uint64_t s){
  uint64_t inp[16], o[1]; for(int i=0;i<16;i++) inp[i]=0; inp[0]=x; inp[1]=s;
  ext4_scale_rc(o,inp); return o[0];
}
static E escale_emit(E a, uint64_t s){ E r; for(int i=0;i<4;i++) r.c[i]=scale1_emit(a.c[i],s); return r; }
static E efrob_emit(E a){
  static uint64_t f1=0; if(!f1) f1=fpow(EXT_W,(P-1)/4);
  E r; uint64_t s=1; for(int i=0;i<4;i++){ r.c[i]=scale1_emit(a.c[i],s); s=fmul(s,f1); } return r;
}
static uint64_t finv_emit(uint64_t a){ uint64_t inp[16],o[1]; for(int i=0;i<16;i++) inp[i]=0; inp[0]=a; bb_inv_rc(o,inp); return o[0]; }
/* einv composed ENTIRELY from emitted leaves: emul/escale/efrob/finv all emitted */
static E einv_emit(E a){
  E b=efrob_emit(a), c=efrob_emit(b), d=efrob_emit(c);
  E t=emul_emit(b,emul_emit(c,d));
  E n=emul_emit(a,t);
  return escale_emit(t, finv_emit(n.c[0]));
}

static int eeq(E a, E b){ for(int i=0;i<4;i++) if(a.c[i]!=b.c[i]) return 0; return 1; }

int main(void){
  /* deterministic test vectors (no fabricated KAT: the oracle is the p3 ref). */
  uint64_t seed=0x1234567;
  E A[16], B[16];
  for(int t=0;t<16;t++){
    for(int i=0;i<4;i++){ seed=seed*6364136223846793005ULL+1; A[t].c[i]=(seed>>17)%P; }
    for(int i=0;i<4;i++){ seed=seed*6364136223846793005ULL+1; B[t].c[i]=(seed>>17)%P; }
  }
  int mul_fail=0, rc_fail=0, fold_fail=0, scale_fail=0, inv_fail=0, inv_id_fail=0;
  for(int t=0;t<16;t++){
    if(!eeq(emul_emit(A[t],B[t]), emul_ref(A[t],B[t]))) mul_fail++;
    if(!eeq(emul_rc(A[t],B[t]), emul_emit(A[t],B[t]))) rc_fail++;
    /* fold on f(x) = A, f(-x) = B, beta = A[t+1], x = B[t].c[0] (hip = (2x)^{-1}) */
    {
      E beta=A[(t+1)%16]; uint64_t x=B[t].c[0]; if(x==0) x=1;
      uint64_t hip=finv(fmul(2,x));
      if(!eeq(efold_emit(A[t],B[t],beta,hip), efold_ref(A[t],B[t],beta,hip))) fold_fail++;
    }
    if(!eeq(escale_emit(A[t],B[t].c[0]), escale_ref(A[t],B[t].c[0]))) scale_fail++;
    if(!eeq(efrob_emit(A[t]), efrob_ref(A[t]))) scale_fail++;
    /* inverse: emitted einv == ref einv, AND a * a^{-1} == 1 (extension identity) */
    int nonzero = A[t].c[0]|A[t].c[1]|A[t].c[2]|A[t].c[3];
    if(nonzero){
      E inv_e=einv_emit(A[t]);
      if(!eeq(inv_e, einv_ref(A[t]))) inv_fail++;
      E prod=emul_emit(A[t], inv_e);
      E one={{1,0,0,0}};
      if(!eeq(prod, one)) inv_id_fail++;
    }
  }
  printf("=== deg-4 extension-field FRI kernels (x^4=11) EMITTED vs p3 reference ===\n");
  printf("  ext4 multiply (all 4 coords) == p3 emul        : %s\n", mul_fail?"FAIL":"PASS");
  printf("  hand-authored ext4_mul_c*_rc == proved mul     : %s\n", rc_fail?"FAIL":"PASS");
  printf("  ext4 FRI fold (all 4 coords) == reference fold : %s\n", fold_fail?"FAIL":"PASS");
  printf("  ext4 scale/Frobenius == p3 escale/efrob        : %s\n", scale_fail?"FAIL":"PASS");
  printf("  ext4 inverse (Frobenius/norm) == p3 einv       : %s\n", inv_fail?"FAIL":"PASS");
  printf("  ext4 inverse identity a*a^{-1} == 1            : %s\n", inv_id_fail?"FAIL":"PASS");
  if(mul_fail||rc_fail||fold_fail||scale_fail||inv_fail||inv_id_fail){
    printf("KAT FAIL (mul=%d rc=%d fold=%d scale=%d inv=%d id=%d)\n",
           mul_fail, rc_fail, fold_fail, scale_fail, inv_fail, inv_id_fail);
    return 1;
  }
  printf("All ext4 KAT cases PASS — EMITTED deg-4 ext-field mul/fold/scale/inverse byte-identical to p3 reference.\n");
  return 0;
}
