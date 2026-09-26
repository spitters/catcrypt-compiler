/* KAT for the OWNED bincode byte-packer (plonky3_serialize_owned.s).
 *
 * The owned-emitted LE byte writers (p3_ser_u64_le / p3_ser_u32_le / p3_ser_u8 /
 * p3_ser_digest_le) are checked byte-for-byte against the plain-C bincode
 * reference (the w_u64 / w_u32 / w_fe / w_digest of p3_accept_prove.c). The
 * monty() field multiply that produces the u32 wire value is the caller's
 * job (an emitted Barrett-by-constant field leaf); the byte-packer serializes
 * a value already in monty/u32 form, so this KAT feeds the byte layout directly.
 *
 * Each owned writer takes (out_stream_ptr, value_ptr) in SysV (%rdi, %rsi) and
 * advances %rdi past the bytes it wrote, returning nothing. p3_ser_digest_le
 * takes the 8 monty-form words contiguously in *value_ptr and emits 32 bytes.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* the owned-emitted byte-packer leaves */
extern void p3_ser_u64_le(uint8_t *out, const uint64_t *v);
extern void p3_ser_u32_le(uint8_t *out, const uint64_t *v);
extern void p3_ser_u8(uint8_t *out, const uint64_t *v);
extern void p3_ser_digest_le(uint8_t *out, const uint64_t *d);

/* ---- plain-C bincode reference (verbatim shape from p3_accept_prove.c) ---- */
static void ref_u64(uint8_t *b, uint64_t v) { for (int i = 0; i < 8; i++) b[i] = (v >> (8 * i)) & 0xff; }
static void ref_u32(uint8_t *b, uint32_t v) { for (int i = 0; i < 4; i++) b[i] = (v >> (8 * i)) & 0xff; }
static void ref_u8(uint8_t *b, uint8_t v)   { b[0] = v; }
static void ref_digest(uint8_t *b, const uint64_t d[8]) { for (int i = 0; i < 8; i++) ref_u32(b + 4 * i, (uint32_t)d[i]); }

static int fails = 0;
static void check(const char *name, const uint8_t *a, const uint8_t *b, int n) {
  if (memcmp(a, b, n) != 0) {
    printf("FAIL %s (%d bytes)\n  owned:", name, n);
    for (int i = 0; i < n; i++) printf(" %02x", a[i]);
    printf("\n  ref:  ");
    for (int i = 0; i < n; i++) printf(" %02x", b[i]);
    printf("\n");
    fails++;
  } else {
    printf("PASS %s (%d bytes byte-identical)\n", name, n);
  }
}

int main(void) {
  /* deterministic test vectors (incl. p3-realistic values) */
  uint64_t u64v[] = { 0, 1, 2, 8, 0x0123456789abcdefULL, 2013265921ULL, 0xffffffffffffffffULL };
  uint64_t u32v[] = { 0, 1, 268435454ULL /* 2^32 mod p */, 1902249559ULL, 0xdeadbeefULL };
  uint64_t u8v[]  = { 0, 1, 5, 163, 255 };

  for (unsigned k = 0; k < sizeof(u64v) / sizeof(*u64v); k++) {
    uint8_t a[8] = {0}, b[8] = {0};
    p3_ser_u64_le(a, &u64v[k]);
    ref_u64(b, u64v[k]);
    char nm[32]; snprintf(nm, sizeof nm, "u64[%u]", k);
    check(nm, a, b, 8);
  }
  for (unsigned k = 0; k < sizeof(u32v) / sizeof(*u32v); k++) {
    uint8_t a[4] = {0}, b[4] = {0};
    p3_ser_u32_le(a, &u32v[k]);
    ref_u32(b, (uint32_t)u32v[k]);
    char nm[32]; snprintf(nm, sizeof nm, "u32[%u]", k);
    check(nm, a, b, 4);
  }
  for (unsigned k = 0; k < sizeof(u8v) / sizeof(*u8v); k++) {
    uint8_t a[1] = {0}, b[1] = {0};
    p3_ser_u8(a, &u8v[k]);
    ref_u8(b, (uint8_t)u8v[k]);
    char nm[32]; snprintf(nm, sizeof nm, "u8[%u]", k);
    check(nm, a, b, 1);
  }
  /* digest: 8 monty-form words -> 32 bytes (the trace/quotient/fri root layout) */
  {
    uint64_t d[8] = { 1902249559ULL, 0, 1, 268435454ULL, 42, 0xabcdef, 2013265920ULL, 7 };
    uint8_t a[32] = {0}, b[32] = {0};
    p3_ser_digest_le(a, d);
    ref_digest(b, d);
    check("digest[8]", a, b, 32);
  }

  if (fails) { printf("\n%d KAT(s) FAILED\n", fails); return 1; }
  printf("\nALL serialize byte-packer KATs PASS (owned == bincode reference)\n");
  return 0;
}
