/* tramp.c -- calling-convention adapters for the compiler's objects in gen/.
 *
 * The region-compiled kernels may change every general-purpose register except
 * %rsp (their clobber sets sha512Clob, blake2bKClob, keccakFClob include the
 * System V callee-saved registers %rbx, %rbp, %r12-%r15).  A C caller assumes
 * those registers survive a call, so each kernel is reached through a
 * trampoline that saves the six callee-saved registers, calls the kernel with
 * the argument registers untouched, and restores them.  The trampoline is
 * harness code; the kernel bytes are the object's.  Its cost (six pushes, six
 * pops, a call) is part of every "ours" figure; a C compiler emits the same
 * saves in the prologue of a function that uses those registers.
 *
 * The block wrappers below give our SHA-512 and BLAKE2b arms the interface of the
 * peers: they take the 128-byte block and load its 16 message words into the
 * kernel's input array on every call (big-endian for SHA-512, little-endian for
 * BLAKE2b), inside the timed loop.  The peers do the same loads inside their
 * compression functions.  This file is compiled with the peers' flags.
 */
#include <stdint.h>
#include <string.h>

#include "arms.h"

#define TRAMP(name, target)                                                   \
  __asm__(".text\n"                                                           \
          ".globl " #name "\n"                                                \
          ".type " #name ",@function\n"                                       \
          ".p2align 4\n" #name ":\n"                                          \
          "  push %rbx\n  push %rbp\n  push %r12\n"                           \
          "  push %r13\n  push %r14\n  push %r15\n"                           \
          "  sub $8, %rsp\n"                                                  \
          "  call " #target "\n"                                              \
          "  add $8, %rsp\n"                                                  \
          "  pop %r15\n  pop %r14\n  pop %r13\n"                              \
          "  pop %r12\n  pop %rbp\n  pop %rbx\n"                              \
          "  ret\n"                                                           \
          ".size " #name ", .-" #name "\n");

TRAMP(ours_sha512_compress, catcrypt_sha512_compress)
TRAMP(ours_blake2b_compress, catcrypt_blake2b_compress)
TRAMP(ours_keccak_f1600, catcrypt_keccak_f1600)

/* x86-64 is little-endian: a big-endian word load is a load and a byte swap
 * (MOVBE or BSWAP), a little-endian one a plain load. */
void ours_sha512_block(uint64_t *dst, uint64_t src[24], const uint8_t blk[128]) {
  for (int j = 0; j < 16; j++) {
    uint64_t w;
    memcpy(&w, blk + 8 * j, 8);
    src[8 + j] = __builtin_bswap64(w);
  }
  ours_sha512_compress(dst, src);
}

void ours_blake2b_block(uint64_t *dst, uint64_t src[24], const uint8_t blk[128],
                        uint64_t t0, uint64_t t1, uint64_t f0) {
  memcpy(src + 8, blk, 128);
  ours_blake2b_compress(dst, f0, t1, t0, src);
}
