/* Calls the verified RV64 X25519 ladder object on lines "scalar u" (64 hex digits each,
   little-endian, scalar already clamped) read from stdin, and prints "x2 z2" for each.
   The 576-byte state block layout is RiscvX25519LadderFnProof.off: the scalar at 0, then
   x1, x2, z2, x3, z3 at 32, 64, 96, 128, 160. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

void catcrypt_x25519_ladder(uint8_t *block);

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static int parse32(const char *s, uint8_t *out) {
  if (strlen(s) != 64) return 1;
  for (int i = 0; i < 32; i++) {
    int hi = hexval(s[2 * i]), lo = hexval(s[2 * i + 1]);
    if (hi < 0 || lo < 0) return 1;
    out[i] = (uint8_t)(hi * 16 + lo);
  }
  return 0;
}

static void put32(const uint8_t *b) {
  for (int i = 0; i < 32; i++) printf("%02x", b[i]);
}

static uint8_t block[576] __attribute__((aligned(16)));

int main(void) {
  char a[80], b[80];
  while (scanf("%79s %79s", a, b) == 2) {
    memset(block, 0, sizeof block);
    if (parse32(a, block) || parse32(b, block + 32)) return 2;
    block[64] = 1;                    /* x2 = 1 */
    memcpy(block + 128, block + 32, 32); /* x3 = u */
    block[160] = 1;                   /* z3 = 1 */
    catcrypt_x25519_ladder(block);
    put32(block + 64);
    putchar(' ');
    put32(block + 96);
    putchar('\n');
  }
  return 0;
}
