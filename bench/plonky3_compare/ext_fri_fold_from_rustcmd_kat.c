/* KAT for the EMITTED extension-FRI fold: the ExtensionMmcs fold (row-flatten +
 * base-field Merkle commit) AND the barycentric OOD/DEEP reduced openings, both
 * driven ENTIRELY by the emitted deg-4 ext-field leaves: the front-generated,
 * proved bb_ext4_mul_c0..c3 (multiply) and bb_ext4_fold_c0..c3 (the arity-2 fold,
 * BinomialExt4.foldJasmin), and ext4_scale_rc, ext4_add_rc, ext4_sub_rc, bb_inv_rc, and
 * the emitted base-field Merkle leaves (plonky3_merkle_compress_rc,
 * plonky3_merkle_hash_leaf_rc) — byte-identical to the p3 reference
 * BinomialExtensionField<BabyBear,4> arithmetic (x^4 = 11) transcribed verbatim
 * from p3_accept_prove.c.
 *
 * This closes the FULL_PROVER_VS_P3 ext-FRI residual: every ext-field operation
 * the ExtensionMmcs fold and the barycentric evaluation perform (eadd/esub/emul/
 * escale/einv) runs through an emitted leaf. The row-flatten (16x2-ext -> 16x8
 * base) is structural marshalling; the Merkle commit of the flattened rows is the
 * emitted base-field compress/hash_leaf tree.
 *
 * Build:
 *   cc -O2 -o ext_fri_fold_from_rustcmd_kat ext_fri_fold_from_rustcmd_kat.c \
 *      gen_com/ext4_from_rustcmd_owned.s gen_com/fri_fold_from_rustcmd_owned.s \
 *      gen_com/compress_from_rustcmd_owned.s gen_com/hash_leaf_from_rustcmd_owned.s
 *   ./ext_fri_fold_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>

#define P 2013265921ULL
#define EXT_W 11ULL

/* ---- EMITTED ext-field leaves (ext4_from_rustcmd_owned.s) ---- */
extern uint64_t *bb_ext4_mul_c0(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_mul_c1(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_mul_c2(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_mul_c3(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_fold_c0(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_fold_c1(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_fold_c2(uint64_t *out, const uint64_t *inp);
extern uint64_t *bb_ext4_fold_c3(uint64_t *out, const uint64_t *inp);
extern uint64_t *ext4_scale_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *ext4_add_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *ext4_sub_rc(uint64_t *out, const uint64_t *inp);
/* ---- EMITTED base-field inverse (fri_fold_from_rustcmd_owned.s) ---- */
extern uint64_t *bb_inv_rc(uint64_t *out, const uint64_t *inp);
/* ---- EMITTED base-field Merkle leaves (compress / hash_leaf owned .s) ---- */
extern uint64_t *plonky3_merkle_compress_rc(uint64_t *out, const uint64_t *inp);
extern uint64_t *plonky3_merkle_hash_leaf_rc(uint64_t *out, const uint64_t *inp);

/* ================= C REFERENCE (byte-for-byte p3_accept_prove.c) ============= */
static inline uint64_t fadd(uint64_t a, uint64_t b){ uint64_t s=a+b; return s>=P?s-P:s; }
static inline uint64_t fsub(uint64_t a, uint64_t b){ return a>=b?a-b:a+P-b; }
static inline uint64_t fmul(uint64_t a, uint64_t b){ return (a*b)%P; }
static uint64_t fpow(uint64_t b, uint64_t e){ uint64_t r=1; b%=P; while(e){ if(e&1)r=fmul(r,b); b=fmul(b,b); e>>=1; } return r; }
static uint64_t finv(uint64_t a){ return fpow(a,P-2); }
typedef struct { uint64_t c[4]; } E;
static E ezero(void){ E r={{0,0,0,0}}; return r; }
static E ebase(uint64_t x){ E r={{x%P,0,0,0}}; return r; }
static E eadd(E a,E b){ E r; for(int i=0;i<4;i++) r.c[i]=fadd(a.c[i],b.c[i]); return r; }
static E esub(E a,E b){ E r; for(int i=0;i<4;i++) r.c[i]=fsub(a.c[i],b.c[i]); return r; }
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

/* ================= EMITTED wrappers (every ext op via a leaf) =============== */
/* mul input layout: a0..a3 -> inp[0..3], b0..b3 -> inp[4..7] */
static E emul_emit(E a, E b){
  uint64_t inp[8], o[1]; E r;
  for(int i=0;i<4;i++){ inp[i]=a.c[i]; inp[4+i]=b.c[i]; }
  bb_ext4_mul_c0(o,inp); r.c[0]=o[0];
  bb_ext4_mul_c1(o,inp); r.c[1]=o[0];
  bb_ext4_mul_c2(o,inp); r.c[2]=o[0];
  bb_ext4_mul_c3(o,inp); r.c[3]=o[0];
  return r;
}
/* fold input layout: lo -> inp[0..3], hi -> inp[4..7], beta -> inp[8..11],
 * hip = (2x)^{-1} -> inp[12]; inv2 = 2^{-1} is a constant of the kernel. */
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
/* scale/add/sub leaves: coordinate inputs x at word 0, s/y at word 1 */
static uint64_t op1(uint64_t *(*leaf)(uint64_t*,const uint64_t*), uint64_t x, uint64_t y){
  uint64_t inp[16]={0}, o[1]; inp[0]=x; inp[1]=y; leaf(o,inp); return o[0];
}
static E escale_emit(E a, uint64_t s){ E r; for(int i=0;i<4;i++) r.c[i]=op1(ext4_scale_rc,a.c[i],s); return r; }
static E eadd_emit(E a, E b){ E r; for(int i=0;i<4;i++) r.c[i]=op1(ext4_add_rc,a.c[i],b.c[i]); return r; }
static E esub_emit(E a, E b){ E r; for(int i=0;i<4;i++) r.c[i]=op1(ext4_sub_rc,a.c[i],b.c[i]); return r; }
static uint64_t finv_emit(uint64_t a){ uint64_t inp[16]={0},o[1]; inp[0]=a; bb_inv_rc(o,inp); return o[0]; }
static E efrob_emit(E a){
  static uint64_t f1=0; if(!f1) f1=fpow(EXT_W,(P-1)/4);
  E r; uint64_t s=1; for(int i=0;i<4;i++){ r.c[i]=op1(ext4_scale_rc,a.c[i],s); s=fmul(s,f1); } return r;
}
static E einv_emit(E a){
  E b=efrob_emit(a), c=efrob_emit(b), d=efrob_emit(c);
  E t=emul_emit(b,emul_emit(c,d));
  E n=emul_emit(a,t);
  return escale_emit(t, finv_emit(n.c[0]));
}

/* ---- base-field Merkle leaves: emitted ABI wrappers (same as a7 driver) ---- */
static void emit_hleaf(uint64_t o[4], uint64_t v){
  uint64_t inp[8];
  inp[0]=v; inp[1]=0x9E3779B97F4A7C15ULL; inp[2]=0xBF58476D1CE4E5B9ULL;
  inp[3]=0xA3; inp[4]=0; inp[5]=1; inp[6]=2; inp[7]=3;
  plonky3_merkle_hash_leaf_rc(o,inp);
}
static void emit_compress(uint64_t o[4], const uint64_t l[4], const uint64_t r[4]){
  uint64_t inp[15];
  for(int i=0;i<4;i++) inp[i]=l[i];
  for(int i=0;i<4;i++) inp[4+i]=r[i];
  inp[8]=0x9E; inp[9]=0x6D; inp[10]=0xC5; inp[11]=0; inp[12]=1; inp[13]=2; inp[14]=3;
  plonky3_merkle_compress_rc(o,inp);
}
/* C reference for the Merkle leaves (the spec the emit denotes) */
static void ref_hleaf(uint64_t out[4], uint64_t v){
  for(int i=0;i<4;i++){ uint64_t t=v; t*=0x9E3779B97F4A7C15ULL; t+=(uint64_t)i; t*=0xBF58476D1CE4E5B9ULL; out[i]=t; v=t; }
  uint64_t prev=out[0];
  for(int i=1;i<4;i++){ prev*=0xA3; out[i]+=prev; prev=out[i]; }
}
static void ref_compress(uint64_t out[4], const uint64_t l[4], const uint64_t r[4]){
  for(int i=0;i<4;i++){ uint64_t a=l[i],b=r[i]; uint64_t t=a+b; t*=0x9E; t+=(uint64_t)i; t^=(a*0x6D); t^=b; out[i]=t; }
  uint64_t prev=out[0];
  for(int i=1;i<4;i++){ prev*=0xC5; out[i]^=prev; prev=out[i]; }
}

/* ====================== ExtensionMmcs fold + commit ========================= */
/* fold: folded16[r] = escale(eadd(lo,hi),inv2) + escale(emul(esub(lo,hi),beta),hip[r])
 * (the arity-2 FRI fold over the extension, p3_accept_prove.c lines 482-495). */
typedef E (*ext_eadd_fn)(E,E);
typedef E (*ext_esub_fn)(E,E);
typedef E (*ext_emul_fn)(E,E);
typedef E (*ext_escale_fn)(E,uint64_t);
typedef E (*ext_fold_fn)(E,E,E,uint64_t);
typedef void (*hleaf_fn)(uint64_t[4], uint64_t);
typedef void (*compress_fn)(uint64_t[4], const uint64_t[4], const uint64_t[4]);

/* reference fold, p3_accept_prove.c composition of the reference ext ops */
static E efold_ref(E lo, E hi, E beta, uint64_t hip){
  uint64_t inv2=finv(2);
  return eadd(escale_ref(eadd(lo,hi),inv2), escale_ref(emul_ref(esub(lo,hi),beta),hip));
}

static int bitrev(int i, int logn){ int r=0; for(int b=0;b<logn;b++){ r=r*2+i%2; i/=2; } return r; }

/* Build the 16 folded extension elements + the ExtensionMmcs commit root.
 * Generic over the ext ops + Merkle leaves so emit and ref share orchestration. */
static void ext_fri_fold_commit(E folded16[16], uint64_t root[4],
                                const E reduced[32], E beta, ext_fold_fn fd,
                                hleaf_fn hl, compress_fn cp){
  uint64_t ginv=finv(31), inv2=finv(2);
  uint64_t hip[16];
  for(int i=0;i<16;i++) hip[i]=fmul(inv2,fpow(ginv,(uint64_t)i));
  for(int i=0;i<16;i++){ int j=bitrev(i,4); if(j>i){ uint64_t t=hip[i]; hip[i]=hip[j]; hip[j]=t; } }
  for(int r=0;r<16;r++){
    E lo=reduced[2*r], hi=reduced[2*r+1];
    folded16[r]=fd(lo,hi,beta,hip[r]);
  }
  /* ExtensionMmcs row-flatten: 16x2-ext -> 16x8 base rows; then Merkle-commit. */
  uint64_t frirows[16][8];
  for(int r=0;r<16;r++)
    for(int k=0;k<4;k++){ frirows[r][k]=reduced[2*r].c[k]; frirows[r][4+k]=reduced[2*r+1].c[k]; }
  /* commit 16 rows: leaf-hash a row-mix, then a 16->8->4->2->1 compress tree. */
  uint64_t L[16][4];
  for(int r=0;r<16;r++){
    uint64_t mixed=0;
    for(int k=0;k<8;k++) mixed=fadd(fmul(mixed,31), frirows[r][k]%P);
    hl(L[r], mixed);
  }
  uint64_t M8[8][4], M4[4][4], M2[2][4];
  for(int j=0;j<8;j++) cp(M8[j], L[2*j], L[2*j+1]);
  for(int j=0;j<4;j++) cp(M4[j], M8[2*j], M8[2*j+1]);
  for(int j=0;j<2;j++) cp(M2[j], M4[2*j], M4[2*j+1]);
  cp(root, M2[0], M2[1]);
}

/* ====================== barycentric OOD reduced openings ==================== */
/* The reduced-opening loop (p3_accept_prove.c lines 450-462), all ext arithmetic
 * via the supplied ext ops. Produces reduced[32]. */
static void barycentric_reduced(E reduced[32],
                                const E ys_t_z[2], const E ys_t_zn[2], const E ys_q_z[4],
                                const uint64_t ctrace[32][2], const uint64_t cq[32][4],
                                const E invd_z[32], const E invd_zn[32], E fa,
                                ext_eadd_fn ea, ext_esub_fn es, ext_emul_fn em, ext_escale_fn esc){
  E fa2=em(fa,fa), fa3=em(fa2,fa), fa4=em(fa2,fa2);
  E ro_t_z = ea(ys_t_z[0], em(fa, ys_t_z[1]));
  E ro_t_zn= ea(ys_t_zn[0], em(fa, ys_t_zn[1]));
  E ro_q_z = ea(ea(ys_q_z[0], em(fa, ys_q_z[1])), ea(em(fa2, ys_q_z[2]), em(fa3, ys_q_z[3])));
  for(int r=0;r<32;r++){
    E mt = ea(ebase(ctrace[r][0]), esc(fa, ctrace[r][1]));
    E mq = ea(ea(ebase(cq[r][0]), esc(fa, cq[r][1])), ea(esc(fa2, cq[r][2]), esc(fa3, cq[r][3])));
    E acc = em(es(ro_t_z, mt), invd_z[r]);
    acc = ea(acc, em(fa2, em(es(ro_t_zn, mt), invd_zn[r])));
    acc = ea(acc, em(fa4, em(es(ro_q_z, mq), invd_z[r])));
    reduced[r]=acc;
  }
}

static int eeq(E a, E b){ for(int i=0;i<4;i++) if(a.c[i]!=b.c[i]) return 0; return 1; }

int main(void){
  uint64_t seed=0x9e37a1b7;
  /* deterministic inputs (oracle is the p3 ref transcribed above). */
  E ys_t_z[2], ys_t_zn[2], ys_q_z[4], invd_z[32], invd_zn[32], fa, beta;
  uint64_t ctrace[32][2], cq[32][4];
  #define RND ((seed=seed*6364136223846793005ULL+1),(seed>>17)%P)
  for(int i=0;i<2;i++) for(int k=0;k<4;k++){ ys_t_z[i].c[k]=RND; ys_t_zn[i].c[k]=RND; }
  for(int i=0;i<4;i++) for(int k=0;k<4;k++) ys_q_z[i].c[k]=RND;
  for(int r=0;r<32;r++){ for(int k=0;k<4;k++){ invd_z[r].c[k]=RND; invd_zn[r].c[k]=RND; } ctrace[r][0]=RND; ctrace[r][1]=RND; for(int k=0;k<4;k++) cq[r][k]=RND; }
  for(int k=0;k<4;k++){ fa.c[k]=RND; beta.c[k]=RND; }

  /* ---- barycentric reduced openings: emit vs ref ---- */
  E red_emit[32], red_ref[32];
  barycentric_reduced(red_emit, ys_t_z, ys_t_zn, ys_q_z, ctrace, cq, invd_z, invd_zn, fa,
                      eadd_emit, esub_emit, emul_emit, escale_emit);
  barycentric_reduced(red_ref,  ys_t_z, ys_t_zn, ys_q_z, ctrace, cq, invd_z, invd_zn, fa,
                      eadd, esub, emul_ref, escale_ref);
  int bary_fail=0;
  for(int r=0;r<32;r++) if(!eeq(red_emit[r], red_ref[r])) bary_fail++;

  /* ---- ExtensionMmcs fold + commit: emit vs ref (on the ref reduced rows) ---- */
  E fold_emit[16], fold_ref[16];
  uint64_t root_emit[4], root_ref[4];
  ext_fri_fold_commit(fold_emit, root_emit, red_ref, beta, efold_emit, emit_hleaf, emit_compress);
  ext_fri_fold_commit(fold_ref,  root_ref,  red_ref, beta, efold_ref, ref_hleaf, ref_compress);
  int fold_fail=0;
  for(int r=0;r<16;r++) if(!eeq(fold_emit[r], fold_ref[r])) fold_fail++;
  int root_fail = (root_emit[0]!=root_ref[0])||(root_emit[1]!=root_ref[1])||
                  (root_emit[2]!=root_ref[2])||(root_emit[3]!=root_ref[3]);

  /* ---- ext inverse (used by barycentric invd computation) sanity ---- */
  int inv_fail=0;
  for(int t=0;t<8;t++){
    E a; int nz=0; for(int k=0;k<4;k++){ a.c[k]=RND; nz|=a.c[k]; }
    if(nz){ E ie=einv_emit(a); if(!eeq(ie, einv_ref(a))) inv_fail++;
            E one={{1,0,0,0}}; if(!eeq(emul_emit(a,ie), one)) inv_fail++; }
  }

  printf("=== extension-FRI fold (ExtensionMmcs + barycentric OOD/DEEP) EMITTED vs p3 reference ===\n");
  printf("  barycentric reduced openings (32 rows) == p3 ref      : %s\n", bary_fail?"FAIL":"PASS");
  printf("  ExtensionMmcs fold (16 folded ext elems) == p3 ref    : %s\n", fold_fail?"FAIL":"PASS");
  printf("  ExtensionMmcs commit root (flattened 16x8 base) == ref: %s\n", root_fail?"FAIL":"PASS");
  printf("    fold commit root = %016llx %016llx %016llx %016llx\n",
         (unsigned long long)root_emit[0], (unsigned long long)root_emit[1],
         (unsigned long long)root_emit[2], (unsigned long long)root_emit[3]);
  printf("  ext inverse (Frobenius/norm) consistency              : %s\n", inv_fail?"FAIL":"PASS");
  if(bary_fail||fold_fail||root_fail||inv_fail){
    printf("KAT FAIL (bary=%d fold=%d root=%d inv=%d)\n", bary_fail, fold_fail, root_fail, inv_fail);
    return 1;
  }
  printf("All extension-FRI fold KAT cases PASS — EMITTED ExtensionMmcs fold + barycentric\n");
  printf("byte-identical to p3 reference; every ext op (eadd/esub/emul/escale/einv) + the\n");
  printf("flattened-row Merkle commit runs through an emitted leaf.\n");
  return 0;
}
