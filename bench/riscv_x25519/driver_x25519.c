/* Calls the verified RV64 X25519 C function catcrypt_x25519(out, scalar, u) on lines "k u"
   (64 hex digits each, the RFC 7748 byte strings, unclamped and unmasked) read from stdin,
   and prints the 32 output bytes for each. X25519CPre asks for 8-byte aligned buffers and
   nothing about where they lie, so the driver also checks that the inputs are unchanged and
   that a call with out == u gives the same bytes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

void catcrypt_x25519(uint8_t *out, const uint8_t *scalar, const uint8_t *u);

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

static uint8_t k[32] __attribute__((aligned(8)));
static uint8_t u[32] __attribute__((aligned(8)));
static uint8_t out[32] __attribute__((aligned(8)));
static uint8_t k0[32], u0[32];

int main(void) {
  char a[80], b[80];
  while (scanf("%79s %79s", a, b) == 2) {
    if (parse32(a, k) || parse32(b, u)) return 2;
    memcpy(k0, k, 32);
    memcpy(u0, u, 32);
    memset(out, 0xa5, sizeof out);
    catcrypt_x25519(out, k, u);
    if (memcmp(k, k0, 32) || memcmp(u, u0, 32)) return 3;
    catcrypt_x25519(u, k, u);
    if (memcmp(u, out, 32)) return 4;
    for (int i = 0; i < 32; i++) printf("%02x", out[i]);
    putchar('\n');
  }
  return 0;
}
