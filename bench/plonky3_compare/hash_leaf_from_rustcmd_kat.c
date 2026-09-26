/* KAT harness for the rustcmd-EMITTED Plonky3 Merkle leaf-hash.
 *
 * `plonky3_merkle_hash_leaf_rc` is the leaf-hash *body* emitted by the verified
 * front's register-arith EMIT-computation path (NOT a hand-written leaf):
 *
 *   hashLeafCom (Com jasminDialect, all regArith add/mul bindings)
 *     -> emitAbiOrchReg (the ChaCha20 EMIT-computation path)
 *     -> gen_com/hash_leaf_from_rustcmd.jazz
 *
 * Every line of the emitted .jazz is a real jasmin `reg u64` scalar assignment
 * (`w0 = r4; w0 = w0 * 11400714819323198485; ...`); there is no opaque leaf
 * call in the body. This is the increment-A2 distinction vs the hand-written
 * `_p3_hleaf_u64` in include/plonky3_merkle_leaves.jinc, whose spec-agreement
 * is KAT-only.
 *
 * We compare against a self-contained C reference `ref_hleaf` (the SAME
 * arithmetic the Lean spec / `_p3_hleaf_u64` uses), asserting byte-equality of
 * the 32-byte output digest over fixed + pseudo-random inputs.
 *
 * Build:
 *   jasminc -arch x86-64 -o hash_leaf_from_rustcmd.s \
 *     gen_com/hash_leaf_from_rustcmd.jazz
 *   gcc -O2 -o hash_leaf_from_rustcmd_kat hash_leaf_from_rustcmd_kat.c \
 *     hash_leaf_from_rustcmd.s
 *   ./hash_leaf_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Extern from the jasmin-assembled emit. ABI: typed array pointers; at the
   System V level these are uint64_t *. The 8-word input is
   [v, G1, G2, 0xA3, 0, 1, 2, 3]; output is the 4-word leaf digest. */
extern uint64_t *plonky3_merkle_hash_leaf_rc(uint64_t *out, const uint64_t *inp);

/* Reference: the same u64-lane leaf-hash logic as `_p3_hleaf_u64`. */
static void ref_hleaf(uint64_t out[4], uint64_t v) {
  for (int i = 0; i < 4; i++) {
    uint64_t t = v;
    t *= 0x9E3779B97F4A7C15ULL;   /* golden-ratio multiplier */
    t += (uint64_t)i;
    t *= 0xBF58476D1CE4E5B9ULL;   /* splittable-random multiplier */
    out[i] = t;
    v = t;                        /* chain for next lane */
  }
  uint64_t prev = out[0];
  for (int i = 1; i < 4; i++) {
    prev *= 0xA3;
    out[i] += prev;
    prev = out[i];
  }
}

static int run_case(const char *name, uint64_t v) {
  uint64_t out_emit[4] = {0};
  uint64_t out_ref[4];
  /* Assemble the 8-word input the emitted ABI expects. */
  uint64_t inp[8];
  inp[0] = v;
  inp[1] = 0x9E3779B97F4A7C15ULL; inp[2] = 0xBF58476D1CE4E5B9ULL;
  inp[3] = 0xA3; inp[4] = 0; inp[5] = 1; inp[6] = 2; inp[7] = 3;

  ref_hleaf(out_ref, v);
  plonky3_merkle_hash_leaf_rc(out_emit, inp);

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

  fails += run_case("zero", 0);
  fails += run_case("one", 1);
  fails += run_case("max", 0xffffffffffffffffULL);
  fails += run_case("mixed", 0xdeadbeefcafebabeULL);

  /* Pseudo-random cases (xorshift64, deterministic). */
  uint64_t st = 0x243F6A8885A308D3ULL;
  for (int c = 0; c < 64; c++) {
    st ^= st << 13; st ^= st >> 7; st ^= st << 17;
    char nm[16]; snprintf(nm, sizeof nm, "rand%d", c);
    fails += run_case(nm, st);
  }

  if (fails == 0) {
    printf("\nAll hash-leaf KAT cases PASS — EMITTED leaf byte-identical to reference.\n");
    return 0;
  } else {
    printf("\nFAILED: %d hash-leaf case(s) did not match reference.\n", fails);
    return 1;
  }
}
