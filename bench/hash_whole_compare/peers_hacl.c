/* peers_hacl.c -- the HACL* full-hash arms of whole.c: the one-shot functions of the HACL*
 * C distribution in libcrux (sys/hacl/c): Hacl_Hash_SHA2_hash_512, Hacl_Hash_SHA3_sha3_256,
 * Hacl_Hash_SHA3_shake128, Hacl_Hash_SHA3_shake256 and Hacl_Hash_Blake2b_hash_with_key with
 * an empty key.  Compiled only with HACL=1 (the Makefile sets it when the sources exist). */
#include <stdint.h>

#include "Hacl_Hash_Blake2b.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Hash_SHA3.h"

void hacl_sha512(uint8_t *o, const uint8_t *m, unsigned long n) {
  Hacl_Hash_SHA2_hash_512(o, (uint8_t *)m, (uint32_t)n);
}

void hacl_sha3_256(uint8_t *o, const uint8_t *m, unsigned long n) {
  Hacl_Hash_SHA3_sha3_256(o, (uint8_t *)m, (uint32_t)n);
}

void hacl_shake128_256(uint8_t *o, const uint8_t *m, unsigned long n) {
  Hacl_Hash_SHA3_shake128(o, 32U, (uint8_t *)m, (uint32_t)n);
}

void hacl_shake256_512(uint8_t *o, const uint8_t *m, unsigned long n) {
  Hacl_Hash_SHA3_shake256(o, 64U, (uint8_t *)m, (uint32_t)n);
}

void hacl_blake2b_512(uint8_t *o, const uint8_t *m, unsigned long n) {
  Hacl_Hash_Blake2b_hash_with_key(o, 64U, (uint8_t *)m, (uint32_t)n, NULL, 0U);
}
