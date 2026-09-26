/* KAT: verified Poseidon2 permutation + PaddingFreeSponge<16,8,8> wired through
 * the Plonky3 prover hash include must match Plonky3's own digest. */
#include <stdint.h>
#include <stdio.h>

extern uint64_t *p2_perm16(uint64_t *out, const uint64_t *p0);
extern uint64_t *p2_sponge16(uint64_t *out, const uint64_t *p0);

static const uint64_t hash_input[16] = {
  894848333u, 1437655012u, 1200606629u, 1690012884u,
  71131202u,  1749206695u, 1717947831u, 120589055u,
  19776022u,  42382981u,   1831865506u, 724844064u,
  171220207u, 1299207443u, 227047920u,  1783754913u
};
static const uint64_t PLONKY3_HASH_KAT[8] = {
  411034481u, 1814977382u, 279610982u, 1352442104u,
  1142612668u, 684731508u, 446845482u, 91189130u
};

int main(void) {
  uint64_t perm[16], digest[8];
  p2_perm16(perm, hash_input);
  p2_sponge16(digest, hash_input);
  int ok = 1;
  printf("Poseidon2 sponge (PaddingFreeSponge<16,8,8>) via plonky3_poseidon2_hash.jinc:\n");
  for (int i = 0; i < 8; i++) {
    if (digest[i] != PLONKY3_HASH_KAT[i]) ok = 0;
    printf("  digest[%d] = %10llu   plonky3 = %10llu   %s\n",
           i, (unsigned long long)digest[i],
           (unsigned long long)PLONKY3_HASH_KAT[i],
           digest[i] == PLONKY3_HASH_KAT[i] ? "ok" : "MISMATCH");
  }
  if (!ok) { printf("KAT FAIL\n"); return 1; }
  printf("KAT PASS: verified Poseidon2 hash == Plonky3 PaddingFreeSponge<16,8,8>.\n");
  return 0;
}
