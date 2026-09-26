/* KAT for the OWNED Fiat-Shamir duplex bookkeeping (plonky3_fiat_shamir_owned.s).
 *
 * The owned-emitted p3_fs_duplex performs the DuplexChallenger duplexing step —
 * absorb the input buffer into the state, permute, squeeze the rate into the
 * output buffer — as owned loopLcmd word-move control flow around a
 * `call hp_perm16` to the Poseidon2 permute leaf.
 *
 * This KAT isolates the BOOKKEEPING (the buffer marshalling), so it links the
 * owned duplex against a shared deterministic permute `hp_perm16` and checks the
 * resulting (st, outbuf) byte-for-byte against the plain-C reference ch_duplex
 * driving the SAME permute. The permute is identical on both sides, so any
 * difference would be a bug in the owned buffer moves. (In production hp_perm16
 * is the verified-emitted Poseidon2 leaf; the bookkeeping is permute-agnostic.)
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Flat Chal layout shared with the owned .s:
 *   st[16]    @ word 0   (byte 0)
 *   inbuf[8]  @ word 16  (byte 128)
 *   outbuf[8] @ word 24  (byte 192)
 */
typedef struct { uint64_t st[16]; uint64_t inbuf[8]; uint64_t outbuf[8]; } Chal;

/* shared deterministic permute (a stand-in for the verified Poseidon2 leaf —
 * BOTH the owned duplex and the C reference call THIS, so the bookkeeping is
 * tested in isolation). (out, in) ABI, may alias (in-place). */
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

/* the owned-emitted duplex */
extern void p3_fs_duplex(Chal *c);

/* plain-C reference ch_duplex (the buffer marshalling of p3_accept_prove.c,
 * specialized to the full-absorb case the owned leaf implements: copy all 8
 * inbuf words into st, permute in place, squeeze st[0..8] into outbuf). */
static void ref_duplex(Chal *c) {
  for (int i = 0; i < 8; i++) c->st[i] = c->inbuf[i];
  hp_perm16(c->st, c->st);
  for (int i = 0; i < 8; i++) c->outbuf[i] = c->st[i];
}

static int fails = 0;
static void run_one(const char *name, const uint64_t st0[16], const uint64_t inb[8]) {
  Chal a, b;
  memset(&a, 0, sizeof a); memset(&b, 0, sizeof b);
  memcpy(a.st, st0, 16 * sizeof(uint64_t));  memcpy(b.st, st0, 16 * sizeof(uint64_t));
  memcpy(a.inbuf, inb, 8 * sizeof(uint64_t)); memcpy(b.inbuf, inb, 8 * sizeof(uint64_t));
  p3_fs_duplex(&a);
  ref_duplex(&b);
  /* check st[0..16] and outbuf[0..8] match (the full duplexed state + squeeze) */
  if (memcmp(a.st, b.st, sizeof a.st) != 0 || memcmp(a.outbuf, b.outbuf, sizeof a.outbuf) != 0) {
    printf("FAIL %s\n", name);
    printf("  owned st[0]=%016llx outbuf[0]=%016llx\n",
           (unsigned long long)a.st[0], (unsigned long long)a.outbuf[0]);
    printf("  ref   st[0]=%016llx outbuf[0]=%016llx\n",
           (unsigned long long)b.st[0], (unsigned long long)b.outbuf[0]);
    fails++;
  } else {
    printf("PASS %s (st[16]+outbuf[8] byte-identical, outbuf[0]=%016llx)\n",
           name, (unsigned long long)a.outbuf[0]);
  }
}

int main(void) {
  uint64_t z16[16] = {0};
  uint64_t z8[8] = {0};
  run_one("zero state, zero input", z16, z8);

  uint64_t st1[16], in1[8];
  for (int i = 0; i < 16; i++) st1[i] = 0x1111111111111111ULL * (i + 1);
  for (int i = 0; i < 8; i++)  in1[i] = 0xABCDEF0123456789ULL ^ ((uint64_t)i << 40);
  run_one("nonzero state, nonzero input", st1, in1);

  uint64_t st2[16], in2[8];
  for (int i = 0; i < 16; i++) st2[i] = (uint64_t)(i * i) + 2013265921ULL;
  for (int i = 0; i < 8; i++)  in2[i] = (uint64_t)(7 - i);
  run_one("p3-flavored values", st2, in2);

  if (fails) { printf("\n%d FS-duplex KAT(s) FAILED\n", fails); return 1; }
  printf("\nALL Fiat-Shamir duplex bookkeeping KATs PASS (owned == reference ch_duplex)\n");
  return 0;
}
