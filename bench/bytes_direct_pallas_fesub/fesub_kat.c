/* fesub_kat.c — Pasta Pallas base-field subtract, bytes-direct vs text-path vs GMP.
 *
 * KATs the 4-limb Pallas base-field subtract leaf
 *   void pallas_fe_sub(uint64_t out[4], const uint64_t a[4], const uint64_t b[4])
 * produced two ways:
 *
 *   pallas_fe_sub    (from ..._bytes.o)  -- ELF64 .o BYTES emitted by the verified
 *                        byte encoder (ScalarEncoder.encodeJBlock), NO assembler
 *                        in the object-build path.
 *   pallas_fe_subt   (from ..._text.o)   -- Lean-printed `.s`, then `as`.
 *
 * Both are the completed masked-conditional-add-back subtract (SBB borrow chain
 * then `d += (0-CF) & p`, all four prime limbs masked). This harness confirms:
 *   (1) the bytes-direct .o LINKS,
 *   (2) it computes (a - b) mod p, KAT-validated against an INDEPENDENT GMP
 *       reference, over random reduced inputs INCLUDING many borrow cases (a<b),
 *   (3) it is byte-identical to the text->as path.
 *
 * Reference prime (STANDARD Pasta Pallas base field, Halo 2 / Nova):
 *   p = 2^254 + 45560315531419706090280762371685220353
 *     = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001.
 * GMP computes mpz_sub then mpz_mod p (canonical residue in [0,p)); a-b<0 wraps
 * to a-b+p, exactly the add-back the kernel emits. Independent of the kernel.
 * Instantiation of EcFeSubPastaComplete.feSubFrameAtPallas_value.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <gmp.h>

extern void pallas_fe_sub (uint64_t *out, const uint64_t *a, const uint64_t *b); /* bytes-direct */
extern void pallas_fe_subt(uint64_t *out, const uint64_t *a, const uint64_t *b); /* text -> as   */

#define N_TRIALS 300000

static uint64_t rng = 0xa5a5c3c3f0f01234ULL;
static inline uint64_t xrand(void) {
    rng ^= rng >> 12; rng ^= rng << 25; rng ^= rng >> 27;
    return rng * 0x2545F4914F6CDD1DULL;
}

/* p = 2^254 + 45560315531419706090280762371685220353, little-endian limbs. */
static const uint64_t P[4] = {
    0x992d30ed00000001ULL, 0x224698fc094cf91bULL,
    0x0000000000000000ULL, 0x4000000000000000ULL
};

/* Returns 1 iff x >= p (x a 4-limb value < 2^256). */
static int ge_p(const uint64_t x[4]) {
    for (int i = 3; i >= 0; i--) {
        if (x[i] != P[i]) return x[i] > P[i];
    }
    return 1; /* x == p */
}

/* Reduce a 4-limb value to canonical [0,p) by conditional subtracts of p. */
static void reduce_modp(uint64_t x[4]) {
    while (ge_p(x)) {
        unsigned __int128 borrow = 0;
        for (int i = 0; i < 4; i++) {
            unsigned __int128 t = (unsigned __int128)x[i] - P[i] - borrow;
            x[i] = (uint64_t)t;
            borrow = (t >> 64) & 1;
        }
    }
}

/* a < b as 4-limb little-endian unsigned. */
static int lt4(const uint64_t a[4], const uint64_t b[4]) {
    for (int i = 3; i >= 0; i--) {
        if (a[i] != b[i]) return a[i] < b[i];
    }
    return 0;
}

static mpz_t mp;
static void gmp_oracle_init(void) {
    mpz_init(mp);
    mpz_import(mp, 4, -1, 8, 0, 0, P);   /* Pallas base prime, LE limbs */
}

/* INDEPENDENT GMP reference: out = (a - b) mod p, canonical in [0,p). */
static void ref_sub(uint64_t out[4], const uint64_t a_in[4], const uint64_t b_in[4]) {
    mpz_t A, B, Z;
    mpz_inits(A, B, Z, NULL);
    mpz_import(A, 4, -1, 8, 0, 0, a_in);
    mpz_import(B, 4, -1, 8, 0, 0, b_in);
    mpz_sub(Z, A, B);
    mpz_mod(Z, Z, mp);
    for (int i = 0; i < 4; i++) out[i] = 0;
    size_t count = 0;
    mpz_export(out, &count, -1, 8, 0, 0, Z);
    mpz_clears(A, B, Z, NULL);
}

int main(void) {
    int fails = 0, mismatch = 0;
    long borrow_cases = 0, noborrow_cases = 0;

    gmp_oracle_init();

    /* Corner cases over {0, 1, 2, p-1, p-2}. */
    uint64_t corners[5][4] = {
        {0,0,0,0},
        {1,0,0,0},
        {2,0,0,0},
        {0x992d30ed00000000ULL,0x224698fc094cf91bULL,0x0000000000000000ULL,0x4000000000000000ULL}, /* p-1 */
        {0x992d30ecffffffffULL,0x224698fc094cf91bULL,0x0000000000000000ULL,0x4000000000000000ULL}  /* p-2 */
    };
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) {
        uint64_t a[4], b[4], r[4], rt[4], ref[4];
        memcpy(a, corners[i], sizeof a); memcpy(b, corners[j], sizeof b);
        ref_sub(ref, a, b);
        pallas_fe_sub (r,  a, b);
        pallas_fe_subt(rt, a, b);
        if (lt4(a,b)) borrow_cases++; else noborrow_cases++;
        if (memcmp(r, ref, sizeof r) != 0) {
            if (fails < 5) fprintf(stderr, "[KAT FAIL bytes-direct] corner i=%d j=%d\n", i, j);
            fails++;
        }
        if (memcmp(r, rt, sizeof r) != 0) {
            if (mismatch < 5) fprintf(stderr, "[MISMATCH bytes-vs-text] corner i=%d j=%d\n", i, j);
            mismatch++;
        }
    }

    /* Random reduced inputs; every other trial swaps a,b to force borrow cases. */
    for (long t = 0; t < N_TRIALS; t++) {
        uint64_t a[4], b[4], r[4], rt[4], ref[4];
        for (int k = 0; k < 4; k++) { a[k] = xrand(); b[k] = xrand(); }
        reduce_modp(a); reduce_modp(b);
        if ((t & 1) == 0) {
            if (lt4(a,b)) { uint64_t tmp[4]; memcpy(tmp,a,32); memcpy(a,b,32); memcpy(b,tmp,32); }
        } else {
            if (!lt4(a,b)) { uint64_t tmp[4]; memcpy(tmp,a,32); memcpy(a,b,32); memcpy(b,tmp,32); }
        }

        if (lt4(a,b)) borrow_cases++; else noborrow_cases++;

        ref_sub(ref, a, b);
        pallas_fe_sub (r,  a, b);
        pallas_fe_subt(rt, a, b);

        if (memcmp(r, ref, sizeof r) != 0) {
            if (fails < 5) fprintf(stderr,
                "[KAT FAIL bytes-direct] t=%ld  a=[%016llx %016llx %016llx %016llx] b=[%016llx %016llx %016llx %016llx]\n",
                t,(unsigned long long)a[0],(unsigned long long)a[1],(unsigned long long)a[2],(unsigned long long)a[3],
                (unsigned long long)b[0],(unsigned long long)b[1],(unsigned long long)b[2],(unsigned long long)b[3]);
            fails++;
        }
        if (memcmp(r, rt, sizeof r) != 0) {
            if (mismatch < 5) fprintf(stderr, "[MISMATCH bytes-vs-text] t=%ld\n", t);
            mismatch++;
        }
    }

    if (fails == 0 && mismatch == 0) {
        printf("PASS  pallas_fe_sub bytes-direct .o: %d random + 25 corner trials KAT-correct\n"
               "      vs INDEPENDENT GMP (a-b mod Pallas base prime 2^254+...),\n", N_TRIALS);
        printf("      borrow cases (a<b) = %ld, no-borrow cases = %ld,\n", borrow_cases, noborrow_cases);
        printf("      byte-identical to text->as path (assembler `as` NOT in bytes-direct path)\n");
        return 0;
    }
    printf("FAIL  bytes-direct KAT failures=%d, bytes-vs-text mismatches=%d (borrow=%ld noborrow=%ld)\n",
           fails, mismatch, borrow_cases, noborrow_cases);
    return 1;
}
