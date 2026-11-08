/* tramp.c -- the block wrappers of the compiler's objects in gen/, and the
 * callee-saved register check of the conformance run.
 *
 * The objects follow the System V AMD64 calling convention: each kernel saves
 * every callee-saved register its body writes (%rbx, %rbp, %r12-%r15) in its
 * own frame and restores it before the return (the contracts of
 * Sha2Linked.sha512KernelAbi, Blake2Linked.blake2bKernelAbi and
 * KeccakLinked.keccakFKernelAbi state clobber sets without them).  A C caller
 * therefore calls the symbols catcrypt_* directly, and the cost of those saves
 * is part of the kernel's figure.
 *
 * The block wrappers below give our SHA-512 and BLAKE2b arms the interface of the
 * peers: they take the 128-byte block and load its 16 message words into the
 * kernel's input array on every call (big-endian for SHA-512, little-endian for
 * BLAKE2b), inside the timed loop, and then call the kernel.  The peers do the
 * same loads inside their compression functions.  This file is compiled with the
 * peers' flags.
 *
 * abi_check_call (conformance only, never timed) calls a kernel with known
 * values in the six callee-saved registers and returns the number of them that
 * differ after the return: the run-time check that the objects keep them.
 */
#include <stdint.h>
#include <string.h>

#include "arms.h"

/* x86-64 is little-endian: a big-endian word load is a load and a byte swap
 * (MOVBE or BSWAP), a little-endian one a plain load. */
void ours_sha512_block(uint64_t *dst, uint64_t src[24], const uint8_t blk[128]) {
  for (int j = 0; j < 16; j++) {
    uint64_t w;
    memcpy(&w, blk + 8 * j, 8);
    src[8 + j] = __builtin_bswap64(w);
  }
  catcrypt_sha512_compress(dst, src);
}

void ours_blake2b_block(uint64_t *dst, uint64_t src[24], const uint8_t blk[128],
                        uint64_t t0, uint64_t t1, uint64_t f0) {
  memcpy(src + 8, blk, 128);
  catcrypt_blake2b_compress(dst, f0, t1, t0, src);
}

/* abi_check_call(fn, a0, a1, a2, a3, a4): %rdi = fn, %rsi..%r9 = a0..a4.  The six
 * callee-saved registers are pushed, set to the sentinels 0x5a5a...00 + k, the
 * kernel is called with a0..a4 in %rdi, %rsi, %rdx, %rcx, %r8, the registers are
 * compared with the sentinels, restored, and the count of differences returned. */
__asm__(".text\n"
        ".globl abi_check_call\n"
        ".type abi_check_call,@function\n"
        ".p2align 4\n"
        "abi_check_call:\n"
        "  push %rbx\n  push %rbp\n  push %r12\n  push %r13\n  push %r14\n  push %r15\n"
        "  sub $8, %rsp\n"
        "  mov %rdi, %rax\n"
        "  mov %rsi, %rdi\n  mov %rdx, %rsi\n  mov %rcx, %rdx\n  mov %r8, %rcx\n"
        "  mov %r9, %r8\n"
        "  movabs $0x5a5a5a5a5a5a5a00, %rbx\n"
        "  lea 1(%rbx), %rbp\n  lea 2(%rbx), %r12\n  lea 3(%rbx), %r13\n"
        "  lea 4(%rbx), %r14\n  lea 5(%rbx), %r15\n"
        "  call *%rax\n"
        "  xor %eax, %eax\n"
        "  movabs $0x5a5a5a5a5a5a5a00, %rcx\n"
        "  xor %edx, %edx\n  cmp %rcx, %rbx\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %rbp\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %r12\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %r13\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %r14\n  setne %dl\n  add %rdx, %rax\n"
        "  inc %rcx\n  xor %edx, %edx\n  cmp %rcx, %r15\n  setne %dl\n  add %rdx, %rax\n"
        "  add $8, %rsp\n"
        "  pop %r15\n  pop %r14\n  pop %r13\n  pop %r12\n  pop %rbp\n  pop %rbx\n"
        "  ret\n"
        ".size abi_check_call, .-abi_check_call\n");
