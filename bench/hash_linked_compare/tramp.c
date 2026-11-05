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
 */

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
