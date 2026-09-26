/* Known-answer test of the owned width-16 Poseidon2 permutations against the
 * Plonky3 0.5.4 test vectors:
 *   -DFIELD_KB   poseidon2_kb   test_default_koalabear_poseidon2_width_16
 *   -DFIELD_M31  poseidon2_m31  test_default_mersenne31_poseidon2_width_16
 *
 * ABI: void f(uint64_t *out, const uint64_t *in); in[0..15] the canonical lanes,
 * out[0..15] the permuted lanes, one lane per 64-bit word.
 */
#include <stdint.h>
#include <stdio.h>

#if defined(FIELD_KB)
#define PERM poseidon2_kb
#define NAME "poseidon2_kb"
static const uint64_t kat_in[16] = {
    894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
    19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913};
static const uint64_t kat_out[16] = {
    1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110, 1391183747, 351743874,
    1238264085, 1292768839, 2023573270, 1201586780, 1360691759, 1230682461, 748270449, 651545025};
#elif defined(FIELD_M31)
#define PERM poseidon2_m31
#define NAME "poseidon2_m31"
static const uint64_t kat_in[16] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};
static const uint64_t kat_out[16] = {
    0x0b2c803a, 0x5b1ee4d1, 0x49c6b1e3, 0x2cdc280c, 0x310a60c8, 0x530a729e, 0x4e61bcb4, 0x2e84d3c3,
    0x58709c08, 0x7e82ac42, 0x2162bcef, 0x6d153ab6, 0x742cf0e3, 0x2f21632d, 0x61adce1e, 0x1973d6f1};
#else
#error "define FIELD_KB or FIELD_M31"
#endif

extern void PERM(uint64_t *out, const uint64_t *in);

int main(void) {
  uint64_t in[16], out[16];
  for (int i = 0; i < 16; i++) in[i] = kat_in[i];
  PERM(out, in);
  int bad = 0;
  for (int i = 0; i < 16; i++) {
    if (out[i] != kat_out[i]) {
      fprintf(stderr, "FAIL %s lane %d: got %llu want %llu\n", NAME, i,
              (unsigned long long)out[i], (unsigned long long)kat_out[i]);
      bad = 1;
    }
    if (in[i] != kat_in[i]) {
      fprintf(stderr, "FAIL %s: input lane %d was modified\n", NAME, i);
      bad = 1;
    }
  }
  if (bad) return 1;
  printf("%s: Plonky3 width-16 test vector passed\n", NAME);
  return 0;
}
