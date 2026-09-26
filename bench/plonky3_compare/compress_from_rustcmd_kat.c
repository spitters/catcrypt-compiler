/* KAT harness for the rustcmd-EMITTED Plonky3 Merkle 2-to-1 compress.
 *
 * `plonky3_merkle_compress_rc` is the compress *body* emitted by the verified
 * front's register-arith EMIT-computation path (NOT a hand-written leaf):
 *
 *   compressComFinal (Com jasminDialect, all regArith add/mul/xor bindings)
 *     -> emitAbiOrchReg (the ChaCha20 EMIT-computation path)
 *     -> gen_com/compress_from_rustcmd.jazz
 *
 * Every line of the emitted .jazz is a real jasmin `reg u64` scalar assignment
 * (`w0 = a; w0 = w0 * 158; ...`); there is no opaque leaf call in the body.
 * This is the increment-A1 distinction vs the hand-written `_p3_compress_u64`
 * in include/plonky3_merkle_leaves.jinc, whose spec-agreement is KAT-only.
 *
 * We compare against a self-contained C reference `ref_compress` (the SAME
 * arithmetic the Lean spec / `merkle_from_rustcmd_kat.c` uses), asserting
 * byte-equality of the 32-byte output digest over fixed + pseudo-random
 * inputs.
 *
 * Build:
 *   jasminc -arch x86-64 -o compress_from_rustcmd.s \
 *     gen_com/compress_from_rustcmd.jazz
 *   gcc -O2 -o compress_from_rustcmd_kat compress_from_rustcmd_kat.c \
 *     compress_from_rustcmd.s
 *   ./compress_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Extern from the jasmin-assembled emit. ABI: typed array pointers; at the
   System V level these are uint64_t *. The 15-word input is [l0..3, r0..3,
   0x9E, 0x6D, 0xC5, 0, 1, 2, 3]; output is the 4-word compressed digest. */
extern uint64_t *plonky3_merkle_compress_rc(uint64_t *out, const uint64_t *inp);

/* Reference: the same u64-lane compress logic as ref_compress in
   merkle_from_rustcmd_kat.c (the Lean spec the emit denotes). */
static void ref_compress(uint64_t out[4], const uint64_t l[4], const uint64_t r[4]) {
  for (int i = 0; i < 4; i++) {
    uint64_t a = l[i], b = r[i];
    uint64_t t = a + b;
    t *= 0x9E;
    t += (uint64_t)i;
    t ^= (a * 0x6D);
    t ^= b;
    out[i] = t;
  }
  uint64_t prev = out[0];
  for (int i = 1; i < 4; i++) {
    prev *= 0xC5;
    out[i] ^= prev;
    prev = out[i];
  }
}

static int run_case(const char *name, const uint64_t l[4], const uint64_t r[4]) {
  uint64_t out_emit[4] = {0};
  uint64_t out_ref[4];
  /* Assemble the 15-word input the emitted ABI expects. */
  uint64_t inp[15];
  for (int i = 0; i < 4; i++) inp[i] = l[i];
  for (int i = 0; i < 4; i++) inp[4 + i] = r[i];
  inp[8] = 0x9E; inp[9] = 0x6D; inp[10] = 0xC5;
  inp[11] = 0; inp[12] = 1; inp[13] = 2; inp[14] = 3;

  ref_compress(out_ref, l, r);
  plonky3_merkle_compress_rc(out_emit, inp);

  int ok = (memcmp(out_emit, out_ref, 32) == 0);
  printf("  [%s] %-10s  o_emit=%016lx %016lx %016lx %016lx\n"
         "                       o_ref =%016lx %016lx %016lx %016lx\n",
         ok ? "PASS" : "FAIL", name,
         out_emit[0], out_emit[1], out_emit[2], out_emit[3],
         out_ref[0], out_ref[1], out_ref[2], out_ref[3]);
  return ok ? 0 : 1;
}

int main(void) {
  int fails = 0;

  { uint64_t l[4] = {0,0,0,0}, r[4] = {0,0,0,0};
    fails += run_case("zeros", l, r); }
  { uint64_t l[4] = {1,2,3,4}, r[4] = {5,6,7,8};
    fails += run_case("seq", l, r); }
  { uint64_t l[4] = {0xffffffffffffffffULL, 0xdeadbeefcafebabeULL,
                     0x0123456789abcdefULL, 0x8000000000000000ULL};
    uint64_t r[4] = {0xfedcba9876543210ULL, 0x5a5a5a5a5a5a5a5aULL,
                     0x0000000000000001ULL, 0xffffffff00000000ULL};
    fails += run_case("mixed", l, r); }

  /* Pseudo-random cases (xorshift64, deterministic). */
  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int c = 0; c < 64; c++) {
    uint64_t l[4], r[4];
    for (int i = 0; i < 4; i++) {
      st ^= st << 13; st ^= st >> 7; st ^= st << 17; l[i] = st;
    }
    for (int i = 0; i < 4; i++) {
      st ^= st << 13; st ^= st >> 7; st ^= st << 17; r[i] = st;
    }
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", c);
    fails += run_case(nm, l, r);
  }

  if (fails == 0) {
    printf("\nAll compress KAT cases PASS — EMITTED leaf byte-identical to reference.\n");
    return 0;
  } else {
    printf("\nFAILED: %d compress case(s) did not match reference.\n", fails);
    return 1;
  }
}
