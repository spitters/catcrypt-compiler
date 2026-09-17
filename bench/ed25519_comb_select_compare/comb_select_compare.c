/* ed25519_comb_compare — the constant-time comb-window SELECT primitive,
 * self-emit (verified Lean x86 backend) vs a portable C reference.
 *
 * The kernel under test is `ed25519_comb_select_x86_from_lean`, emitted by
 * CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel (Com x86Dialect
 * -> runBlock -> AsmPrinter, assembled by gas; no jasminc). It performs the
 * constant-time linear-scan + cmov select of one 256-bit (4x u64) window entry
 * from a 16-entry table given a secret index d in {0..15}. This is the CT-hot
 * primitive of fixed-base (comb) Ed25519 signing -- the lever that closes the
 * 8.5x variable-base sign gap reported in bench/ed25519_adx_compare.
 *
 * ABI: void ed25519_comb_select_x86_from_lean(const u64 *tbl, u64 d, u64 *out)
 *   tbl -> %rdi (16 entries x 4 u64, row-major), d -> %rsi, out -> %rdx.
 *
 * Comparisons:
 *  - lean-owned-backend  : the emitted .s (the artifact)
 *  - portable-ref-CT     : a portable C linear-scan + arithmetic-mask select
 *                          (the same CT shape libsodium ge25519_cmov8 / dalek
 *                          LookupTable::select use), as the correctness oracle
 *                          and a same-algorithm timing reference.
 *  - naive-indexed (NOT CT, reference only): out = tbl[d] direct index, to size
 *                          how much CT linear-scan costs vs a leaky direct load.
 *
 * KAT: for 16 indices over fixed + 100000 random tables, all three agree.
 * No fabricated vectors: the oracle is the portable CT select, cross-checked
 * against the naive direct index (which is value-identical, only not CT).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;

extern void ed25519_comb_select_x86_from_lean(const u64 *tbl, u64 d, u64 *out);

/* Portable constant-time select: linear scan, arithmetic equality mask, no
 * data-dependent branch or load address. Mirrors the emitted kernel. */
static void portable_ct_select(const u64 *tbl, u64 d, u64 *out) {
    out[0] = out[1] = out[2] = out[3] = 0;
    for (u64 j = 0; j < 16; j++) {
        /* mask = 0xFFFF... iff d==j, else 0, branch-free */
        u64 diff = d ^ j;
        u64 nz = (diff | (~diff + 1)) >> 63;   /* 0 if d==j else 1 */
        u64 mask = nz - 1;                       /* all-ones iff d==j */
        const u64 *e = tbl + 4 * j;
        out[0] |= e[0] & mask;
        out[1] |= e[1] & mask;
        out[2] |= e[2] & mask;
        out[3] |= e[3] & mask;
    }
}

/* Non-CT direct index (reference value oracle only). */
static void naive_index(const u64 *tbl, u64 d, u64 *out) {
    memcpy(out, tbl + 4 * d, 32);
}

static inline u64 rdtscp_now(void) {
    unsigned aux;
    __asm__ __volatile__("lfence" ::: "memory");
    u64 t = __builtin_ia32_rdtscp(&aux);
    __asm__ __volatile__("lfence" ::: "memory");
    return t;
}

static u64 xs = 0x243F6A8885A308D3ULL;
static inline u64 xorshift(void) {
    xs ^= xs << 13; xs ^= xs >> 7; xs ^= xs << 17; return xs;
}

int main(int argc, char **argv) {
    long trials = (argc > 1) ? atol(argv[1]) : 4000000;

    /* ---- KAT: fixed + random tables, all 16 indices, three impls agree ---- */
    int fails = 0;
    u64 tbl[64];
    /* fixed table: distinct per cell (matches Lean tabLit shape) */
    for (int j = 0; j < 16; j++)
        for (int k = 0; k < 4; k++)
            tbl[4*j+k] = 0xC0DE0000ULL + 16*j + k;
    for (u64 d = 0; d < 16; d++) {
        u64 a[4], b[4], c[4];
        ed25519_comb_select_x86_from_lean(tbl, d, a);
        portable_ct_select(tbl, d, b);
        naive_index(tbl, d, c);
        if (memcmp(a, b, 32) || memcmp(a, c, 32)) { fails++; }
    }
    for (long t = 0; t < 100000; t++) {
        for (int i = 0; i < 64; i++) tbl[i] = xorshift();
        u64 d = xorshift() & 15;
        u64 a[4], b[4], c[4];
        ed25519_comb_select_x86_from_lean(tbl, d, a);
        portable_ct_select(tbl, d, b);
        naive_index(tbl, d, c);
        if (memcmp(a, b, 32) || memcmp(a, c, 32)) { fails++; }
    }
    if (fails) {
        fprintf(stderr, "KAT FAIL: %d mismatches (lean vs portable-CT vs naive)\n", fails);
        return 1;
    }
    printf("KAT OK: 16 fixed + 100000 random tables, all indices: "
           "lean == portable-CT == naive-index\n");

    /* ---- microbench: min-of-SAMPLES, accumulate to defeat DCE ---- */
    const int SAMPLES = 7;
    for (int i = 0; i < 64; i++) tbl[i] = xorshift();
    u64 out[4]; u64 sink = 0;

    u64 best_lean = ~0ULL, best_ref = ~0ULL, best_naive = ~0ULL;
    for (int s = 0; s < SAMPLES; s++) {
        u64 t0 = rdtscp_now();
        for (long t = 0; t < trials; t++) {
            ed25519_comb_select_x86_from_lean(tbl, (u64)(t & 15), out);
            sink ^= out[0] ^ out[3];
        }
        u64 d0 = rdtscp_now() - t0;
        if (d0 < best_lean) best_lean = d0;
    }
    for (int s = 0; s < SAMPLES; s++) {
        u64 t0 = rdtscp_now();
        for (long t = 0; t < trials; t++) {
            portable_ct_select(tbl, (u64)(t & 15), out);
            sink ^= out[0] ^ out[3];
        }
        u64 d0 = rdtscp_now() - t0;
        if (d0 < best_ref) best_ref = d0;
    }
    for (int s = 0; s < SAMPLES; s++) {
        u64 t0 = rdtscp_now();
        for (long t = 0; t < trials; t++) {
            naive_index(tbl, (u64)(t & 15), out);
            sink ^= out[0] ^ out[3];
        }
        u64 d0 = rdtscp_now() - t0;
        if (d0 < best_naive) best_naive = d0;
    }

    double cl = (double)best_lean  / trials;
    double cr = (double)best_ref   / trials;
    double cn = (double)best_naive / trials;
    printf("\nComb-window CT select (16 entries x 4 u64), min-of-%d, %ld trials\n",
           SAMPLES, trials);
    printf("impl                          cyc/op   ratio-vs-lean\n");
    printf("lean-owned-backend (CT)      %8.2f   %6.3fx\n", cl, 1.0);
    printf("portable-ref     (CT)        %8.2f   %6.3fx\n", cr, cr/cl);
    printf("naive-index   (NOT CT, ref)  %8.2f   %6.3fx\n", cn, cn/cl);
    printf("\n(sink=%llu)\n", (unsigned long long)sink);
    return 0;
}
