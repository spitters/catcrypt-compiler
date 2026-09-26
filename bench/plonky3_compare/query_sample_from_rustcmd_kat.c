/* KAT for the OWNED FRI query-index sampler (plonky3_query_sample_owned.s).
 *
 * The owned-emitted p3_fs_observe / p3_fs_sample / p3_fs_sample_bits implement
 * the DuplexChallenger<16,8> observe/sample/sample_bits WRAPPER as owned
 * control flow: the inlen/outlen counters in the flat Chal struct, the
 * `if (inlen==8)` / `if (inlen>0 || outlen==0)` duplex triggers as owned
 * CMP/Lcond forward branches, the `& 31` mask as an owned AND:64, and the
 * duplex on the trigger as a `call` to the emitted duplex (p3_fs_duplex for the
 * full-absorb inlen==8 case, p3_fs_duplex_n — emitted in the same .s — for the
 * partial-absorb sample-path case).
 *
 * This KAT links the owned wrapper against a shared deterministic permute
 * `hp_perm16` (the SAME permute the reference DuplexChallenger uses) and checks
 * the squeezed words / 5-bit query indices byte-for-byte against the plain-C
 * reference ch_observe/ch_sample/ch_sample_bits5 over a sequence of observes +
 * samples. The permute is identical on both sides, so any difference is a bug in
 * the owned counter/branch/mask wrapper. (In production hp_perm16 is the
 * verified-emitted Poseidon2 leaf; the wrapper is permute-agnostic.)
 *
 * Values fed to observe are already field-reduced (< P), so the reference's
 * `v % P` is the identity and matches the owned straight store — the wrapper is
 * tested in isolation, exactly the gap-1 posture (the field reduction is a field
 * op, deliberately outside this index/counter/mask leaf).
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define P 2013265921ULL  /* BabyBear */

/* Flat Chal layout shared with the owned .s:
 *   st[16]    @ word 0   (byte 0)
 *   inbuf[8]  @ word 16  (byte 128)
 *   outbuf[8] @ word 24  (byte 192)
 *   inlen     @ word 32  (byte 256)
 *   outlen    @ word 33  (byte 264)
 */
typedef struct {
  uint64_t st[16];
  uint64_t inbuf[8];
  uint64_t outbuf[8];
  uint64_t inlen;
  uint64_t outlen;
} Chal;

/* shared deterministic permute (a stand-in for the verified Poseidon2 leaf —
 * BOTH the owned wrapper and the C reference call THIS, so the wrapper is tested
 * in isolation). (out, in) ABI, may alias (in-place). Identical body to the
 * gap-1 fiat_shamir KAT's hp_perm16. */
uint64_t *hp_perm16(uint64_t *o, const uint64_t *s) {
  uint64_t t[16];
  for (int i = 0; i < 16; i++) {
    uint64_t x = s[i] ^ (s[(i + 1) & 15] * 0x9E3779B97F4A7C15ULL);
    x ^= x >> 29; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 32;
    t[i] = x + (uint64_t)i;
  }
  for (int i = 0; i < 16; i++) o[i] = t[i];
  return o;
}

/* the owned-emitted wrapper */
extern void     p3_fs_observe(Chal *c, uint64_t v);
extern uint64_t p3_fs_sample(Chal *c);
extern uint64_t p3_fs_sample_bits(Chal *c);

/* ---- plain-C reference DuplexChallenger (p3_accept_prove.c, ch_* logic) ---- */
static void ref_duplex(Chal *c) {
  for (uint64_t i = 0; i < c->inlen; i++) c->st[i] = c->inbuf[i];
  c->inlen = 0;
  hp_perm16(c->st, c->st);
  for (int i = 0; i < 8; i++) c->outbuf[i] = c->st[i];
  c->outlen = 8;
}
static void ref_observe(Chal *c, uint64_t v) {
  c->outlen = 0;
  c->inbuf[c->inlen++] = v % P;   /* values are pre-reduced, so == v */
  if (c->inlen == 8) ref_duplex(c);
}
static uint64_t ref_sample(Chal *c) {
  if (c->inlen > 0 || c->outlen == 0) ref_duplex(c);
  return c->outbuf[--c->outlen];
}
static uint64_t ref_sample_bits5(Chal *c) { return ref_sample(c) & 31; }

static int fails = 0;

/* Run the SAME observe/sample script on the owned wrapper and the reference,
 * comparing every squeezed word and query index. The script intentionally
 * exercises: a partial-absorb sample (0<inlen<8 → p3_fs_duplex_n partial copy),
 * a full-absorb observe duplex (inlen==8 → p3_fs_duplex), and a drained-then-
 * empty re-duplex (inlen==0,outlen==0 → p3_fs_duplex_n zero-absorb). */
static void check_word(const char *what, uint64_t got, uint64_t ref) {
  if (got != ref) {
    printf("FAIL %-28s owned=%016llx ref=%016llx\n", what,
           (unsigned long long)got, (unsigned long long)ref);
    fails++;
  }
}

int main(void) {
  Chal a, b;
  memset(&a, 0, sizeof a);
  memset(&b, 0, sizeof b);

  /* A p3-flavored transcript: 14 observes (forces one inlen==8 duplex, leaving
   * inlen=6), then an ext sample (4 squeezes: the first is a partial-absorb
   * duplex with inlen=6), then 8 sample_bits (drains outlen 8->0, then forces a
   * fresh inlen==0,outlen==0 zero-absorb duplex), then more samples. */
  uint64_t obs[14];
  obs[0] = 3; obs[1] = 3; obs[2] = 0;                 /* log_ext_degree, log_degree, prep_width */
  for (int i = 0; i < 8; i++) obs[3 + i] = (0x0123456789ULL * (i + 1)) % P; /* trace_root[8] */
  obs[11] = 11 % P; obs[12] = 22 % P; obs[13] = 33 % P;                     /* pv_a, pv_b, pv_x */

  for (int i = 0; i < 14; i++) {
    p3_fs_observe(&a, obs[i]);
    ref_observe(&b, obs[i]);
  }
  /* sample_ext: 4 squeezes (first triggers partial-absorb p3_fs_duplex_n, inlen=6) */
  for (int i = 0; i < 4; i++) {
    char nm[40]; snprintf(nm, sizeof nm, "alpha-squeeze[%d]", i);
    check_word(nm, p3_fs_sample(&a), ref_sample(&b));
  }
  /* observe a FRI commit (8 words) -> a full inlen==8 duplex via p3_fs_duplex */
  for (int i = 0; i < 8; i++) {
    uint64_t v = (0xDEADBEEFULL ^ ((uint64_t)i << 24)) % P;
    p3_fs_observe(&a, v);
    ref_observe(&b, v);
  }
  /* sample 8 query indices (sample_bits & 31): the first triggers a duplex,
   * draining outlen 8->0; further samples after that re-duplex with empty inbuf
   * (inlen==0,outlen==0 -> zero-absorb p3_fs_duplex_n). */
  for (int i = 0; i < 8; i++) {
    char nm[40]; snprintf(nm, sizeof nm, "qidx[%d]", i);
    uint64_t go = p3_fs_sample_bits(&a), re = ref_sample_bits5(&b);
    check_word(nm, go, re);
    if (go > 31) { printf("FAIL %s not a 5-bit value: %llu\n", nm, (unsigned long long)go); fails++; }
  }
  /* a few more plain samples to exercise repeated zero-absorb re-duplexing */
  for (int i = 0; i < 12; i++) {
    char nm[40]; snprintf(nm, sizeof nm, "tail-squeeze[%d]", i);
    check_word(nm, p3_fs_sample(&a), ref_sample(&b));
  }

  if (fails) { printf("\n%d query-sample KAT word(s) FAILED\n", fails); return 1; }
  printf("ALL FRI query-sample wrapper KATs PASS "
         "(owned observe/sample/sample_bits == reference DuplexChallenger)\n");
  return 0;
}
