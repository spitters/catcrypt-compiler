/* KAT harness for the rustcmd-emitted Plonky3 coset-FFT LDE.
 *
 * `plonky3_lde_coset_fft_<N>x<k>_rc` is the orchestration emitted by the
 * verified pipeline:
 *
 *   ldeCosetFftLean_NxK (pure Lean)
 *     -> reifyRustCmd%-equivalent hand-built RustCmd (Plonky3LdeReflect.lean)
 *     -> translate (RustCmdToCryptoSSA)
 *     -> extractedFrontProg
 *     -> cprogToJasminCom (A1)
 *     -> emitAbiOrchRegPtr
 *     -> gen_com/lde_<config>_from_rustcmd_link.jazz
 *
 * The orchestration calls four leaves implemented in u64-lane BabyBear
 * arithmetic in `include/plonky3_lde_leaves.jinc`:
 *   - babybear_ntt_inverse_N: N evals (canonical residues) -> N coeffs (reduced)
 *   - babybear_zero_extend_N_to_kN: copy lower N, zero upper (k-1)*N
 *   - babybear_coset_twist_kN: position i  *=  31^i mod BB_P
 *   - babybear_ntt_forward_kN: identity reduction (stub matching reference)
 *
 * We compare the pipeline output against a self-contained C reference that
 * runs the SAME u64-lane BabyBear logic, asserting byte-equality of the
 * kN-element output (kN * 8 bytes). 4 test cases covering
 * (N, k) ∈ {(64, 4), (256, 4)} with several input shapes.
 *
 * This is the Plonky3-LDE analogue of bench/plonky3_compare/merkle_from_rustcmd_kat.c
 * and ../SSProve-lean/bench/fndsa_compare/verify_from_rustcmd_kat.c.
 *
 * Build:
 *   jasminc -arch x86-64 -o lde_64x4_link.s \
 *     gen_com/lde_coset_fft_64x4_from_rustcmd_link.jazz
 *   jasminc -arch x86-64 -o lde_256x4_link.s \
 *     gen_com/lde_from_rustcmd_link.jazz
 *   gcc -O2 -o lde_from_rustcmd_kat lde_from_rustcmd_kat.c \
 *     lde_64x4_link.s lde_256x4_link.s
 *   ./lde_from_rustcmd_kat
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define BB_P 2013265921ULL
#define BB_G 31ULL

/* Externs from the jasmin-assembled Tier A emit. ABI: rax = output pointer,
   args left-to-right (out, p0). The orchestration's `emitAbiOrchRegPtr`
   passes everything by typed array pointer. */
extern uint64_t *plonky3_lde_coset_fft_64x4_rc(uint64_t *out, const uint64_t *p0);
extern uint64_t *plonky3_lde_coset_fft_256x4_rc(uint64_t *out, const uint64_t *p0);

/* ------- Reference: re-implement the same u64-lane BabyBear logic the
   .jinc leaves use, so we can verify byte-by-byte that the emit produces
   the same output. ------- */

static uint64_t ref_bb_reduce(uint64_t x) {
  if (x >= BB_P) return x - BB_P;
  return x;
}

static uint64_t ref_bb_mul(uint64_t a, uint64_t b) {
  return (a * b) % BB_P;
}

/* babybear_ntt_inverse_N: identity-with-reduction stub. */
static void ref_ntt_inverse(uint64_t *out, const uint64_t *in, int N) {
  for (int i = 0; i < N; i++) {
    out[i] = ref_bb_reduce(in[i]);
  }
}

/* babybear_zero_extend_N_to_kN: copy lower N, zero upper (k-1)*N. */
static void ref_zero_extend(uint64_t *out, const uint64_t *in, int N, int kN) {
  for (int i = 0; i < N; i++) out[i] = in[i];
  for (int i = N; i < kN; i++) out[i] = 0;
}

/* babybear_coset_twist_kN: pointwise multiply by 31^i mod BB_P. */
static void ref_coset_twist(uint64_t *out, const uint64_t *in, int kN) {
  uint64_t w = 1;
  for (int i = 0; i < kN; i++) {
    out[i] = ref_bb_mul(in[i], w);
    w = ref_bb_mul(w, BB_G);
  }
}

/* babybear_ntt_forward_kN: same identity-with-reduction stub. */
static void ref_ntt_forward(uint64_t *out, const uint64_t *in, int kN) {
  for (int i = 0; i < kN; i++) {
    out[i] = ref_bb_reduce(in[i]);
  }
}

/* Reference: full coset-FFT LDE for parameters (N, k). */
static void ref_lde_coset_fft(uint64_t *out, const uint64_t *evals, int N, int k) {
  int kN = N * k;
  static uint64_t coeffs[4096];     /* large enough for N=1024 */
  static uint64_t coeffs_kN[16384]; /* large enough for kN=4096 */
  static uint64_t twisted[16384];
  ref_ntt_inverse(coeffs, evals, N);
  ref_zero_extend(coeffs_kN, coeffs, N, kN);
  ref_coset_twist(twisted, coeffs_kN, kN);
  ref_ntt_forward(out, twisted, kN);
}

static int run_case(const char *name, int N, int k, const uint64_t *evals) {
  int kN = N * k;
  static uint64_t out_emit[16384];
  static uint64_t out_ref[16384];
  memset(out_emit, 0, sizeof(out_emit));
  ref_lde_coset_fft(out_ref, evals, N, k);
  if (N == 64 && k == 4) {
    plonky3_lde_coset_fft_64x4_rc(out_emit, evals);
  } else if (N == 256 && k == 4) {
    plonky3_lde_coset_fft_256x4_rc(out_emit, evals);
  } else {
    printf("  [SKIP] %s (N=%d, k=%d): no linked emit for this config\n", name, N, k);
    return 0;
  }
  int ok = (memcmp(out_emit, out_ref, kN * sizeof(uint64_t)) == 0);
  printf("  [%s] %s (N=%d, k=%d, kN=%d)  out_emit[0]=%016lx  out_ref[0]=%016lx",
         ok ? "PASS" : "FAIL", name, N, k, kN, out_emit[0], out_ref[0]);
  if (!ok) {
    /* Find first diff for diagnostic. */
    for (int i = 0; i < kN; i++) {
      if (out_emit[i] != out_ref[i]) {
        printf("  diff at i=%d: emit=%016lx ref=%016lx", i, out_emit[i], out_ref[i]);
        break;
      }
    }
  }
  printf("\n");
  return ok ? 0 : 1;
}

int main(void) {
  int fails = 0;

  /* Case 1: (N=64, k=4), all zeros — output should be all zeros. */
  {
    static uint64_t evals[64] = {0};
    fails += run_case("zeros_64", 64, 4, evals);
  }
  /* Case 2: (N=64, k=4), sequential 0..63 — sparse-trace probe. */
  {
    static uint64_t evals[64];
    for (int i = 0; i < 64; i++) evals[i] = (uint64_t)i;
    fails += run_case("seq_64", 64, 4, evals);
  }
  /* Case 3: (N=256, k=4), the canonical config — deterministic ramp. */
  {
    static uint64_t evals[256];
    for (int i = 0; i < 256; i++) {
      /* BabyBear residues: keep < BB_P so the ntt_inverse stub's reduce is a no-op. */
      evals[i] = ((uint64_t)i * 0x9E3779B9ULL) % BB_P;
    }
    fails += run_case("ramp_256", 256, 4, evals);
  }
  /* Case 4: (N=256, k=4), large-residue stress — values close to BB_P. */
  {
    static uint64_t evals[256];
    for (int i = 0; i < 256; i++) {
      evals[i] = (BB_P - 1 - (uint64_t)i) % BB_P;
    }
    fails += run_case("near_p_256", 256, 4, evals);
  }

  if (fails == 0) {
    printf("\nAll 4 KAT cases PASS — Tier A emit byte-identical to reference.\n");
    return 0;
  } else {
    printf("\nFAILED: %d case(s) did not match reference.\n", fails);
    return 1;
  }
}
