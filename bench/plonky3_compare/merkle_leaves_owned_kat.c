/* Independent KAT for the OWNED x86 emit of the plonky3 FRI surrogate-hash
 * leaves (`_p3_hleaf_u64` / `_p3_compress_u64`), emitted by
 * CatCrypt/Crypto/SecureCompilation/VIR/Plonky3MerkleLeafOwnedEmit.lean into
 * gen_com/merkle_leaves_owned.s (no jasminc).
 *
 * The reference below is transcribed DIRECTLY from the jinc formulas in
 * include/plonky3_merkle_leaves.jinc (the `_p3_hleaf_u64` / `_p3_compress_u64`
 * bodies), independent of the Lean Com. The harness links the owned .s and
 * checks byte-identity of the four-lane digest over random inputs.
 *
 * Build:
 *   cc -O2 merkle_leaves_owned_kat.c gen_com/merkle_leaves_owned.s -o /tmp/mlkat
 *   /tmp/mlkat
 *
 * ABI (matching toLprogPhysAbi (out:RDI, inp:RSI), stdOutStore 4):
 *   _p3_hleaf_u64(out[4], inp[16]):  inp[0]=v, inp[1]=GOLDEN, inp[2]=SPLIT
 *   _p3_compress_u64(out[4], inp[16]): inp[0..3]=l, inp[4..7]=r
 * (the small mix constants and lane indices are baked as immediates in the .s;
 *  the remaining inp[] words are unused dead loads — any value is fine.)
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static const uint64_t GOLDEN = 0x9E3779B97F4A7C15ULL;
static const uint64_t SPLIT  = 0xBF58476D1CE4E5B9ULL;

/* reference _p3_hleaf_u64 (jinc transcription, all wrapping u64) */
static void ref_hleaf(uint64_t v, uint64_t o[4]) {
  uint64_t prev = v;
  for (int i = 0; i < 4; i++) {
    uint64_t t = prev;
    t *= GOLDEN;
    t += (uint64_t)i;
    t *= SPLIT;
    o[i] = t;
    prev = t;
  }
  prev = o[0];
  for (int i = 1; i < 4; i++) {
    prev *= 0xA3ULL;
    uint64_t t = o[i];
    t += prev;
    o[i] = t;
    prev = t;
  }
}

/* reference _p3_compress_u64 (jinc transcription, all wrapping u64) */
static void ref_compress(const uint64_t l[4], const uint64_t r[4], uint64_t o[4]) {
  for (int i = 0; i < 4; i++) {
    uint64_t a = l[i], b = r[i];
    uint64_t t = a;
    t += b;
    t *= 0x9EULL;
    t += (uint64_t)i;
    uint64_t x = a;
    x *= 0x6DULL;
    t ^= x;
    t ^= b;
    o[i] = t;
  }
  uint64_t prev = o[0];
  for (int i = 1; i < 4; i++) {
    prev *= 0xC5ULL;
    uint64_t t = o[i];
    t ^= prev;
    o[i] = t;
    prev = t;
  }
}

extern void _p3_hleaf_u64(uint64_t *out, uint64_t *inp);
extern void _p3_compress_u64(uint64_t *out, uint64_t *inp);

static uint64_t rng_state = 0x123456789abcdef0ULL;
static uint64_t rng(void) {
  uint64_t x = rng_state;
  x ^= x << 13; x ^= x >> 7; x ^= x << 17;
  rng_state = x;
  return x;
}

int main(void) {
  int fails = 0;
  const int trials = 200000;

  /* a couple of fixed corner cases first */
  uint64_t fixed_v[3] = { 0ULL, 1ULL, ~0ULL };
  for (int k = 0; k < 3; k++) {
    uint64_t inp[16] = {0};
    inp[0] = fixed_v[k]; inp[1] = GOLDEN; inp[2] = SPLIT;
    uint64_t got[4], exp[4];
    _p3_hleaf_u64(got, inp);
    ref_hleaf(fixed_v[k], exp);
    if (memcmp(got, exp, sizeof exp)) {
      printf("hleaf fixed mismatch k=%d\n", k); fails++;
    }
  }

  for (int t = 0; t < trials; t++) {
    /* hleaf */
    uint64_t v = rng();
    uint64_t inp[16];
    for (int i = 0; i < 16; i++) inp[i] = rng();   /* fill dead words too */
    inp[0] = v; inp[1] = GOLDEN; inp[2] = SPLIT;
    uint64_t got[4], exp[4];
    _p3_hleaf_u64(got, inp);
    ref_hleaf(v, exp);
    if (memcmp(got, exp, sizeof exp)) {
      if (fails < 5)
        printf("hleaf mismatch t=%d v=%016llx got0=%016llx exp0=%016llx\n",
               t, (unsigned long long)v,
               (unsigned long long)got[0], (unsigned long long)exp[0]);
      fails++;
    }

    /* compress */
    uint64_t l[4], r[4], cinp[16];
    for (int i = 0; i < 16; i++) cinp[i] = rng();
    for (int i = 0; i < 4; i++) { l[i] = rng(); r[i] = rng(); cinp[i] = l[i]; cinp[4+i] = r[i]; }
    uint64_t cgot[4], cexp[4];
    _p3_compress_u64(cgot, cinp);
    ref_compress(l, r, cexp);
    if (memcmp(cgot, cexp, sizeof cexp)) {
      if (fails < 5)
        printf("compress mismatch t=%d got0=%016llx exp0=%016llx\n",
               t, (unsigned long long)cgot[0], (unsigned long long)cexp[0]);
      fails++;
    }
  }

  if (fails == 0) {
    printf("PASS: %d trials (+3 fixed), both _p3_hleaf_u64 and _p3_compress_u64 "
           "byte-identical to the jinc reference\n", trials);
    return 0;
  }
  printf("FAIL: %d mismatches\n", fails);
  return 1;
}
