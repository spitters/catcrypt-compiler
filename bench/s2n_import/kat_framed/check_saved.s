# check_saved(z, x, y): loads fixed values into the six callee-saved registers,
# calls bignum_montmul_p384_framed(z, x, y), and returns 0 if all six still hold
# those values, otherwise a nonzero bitmask of the registers that changed.
	.text
	.globl check_saved
	.type check_saved, @function
check_saved:
	pushq %rbx
	pushq %rbp
	pushq %r12
	pushq %r13
	pushq %r14
	pushq %r15
	subq $8, %rsp
	movabsq $0x1111111111111111, %rbx
	movabsq $0x2222222222222222, %rbp
	movabsq $0x3333333333333333, %r12
	movabsq $0x4444444444444444, %r13
	movabsq $0x5555555555555555, %r14
	movabsq $0x6666666666666666, %r15
	call bignum_montmul_p384_framed
	xorl %eax, %eax
	movabsq $0x1111111111111111, %rcx
	cmpq %rcx, %rbx
	je 1f
	orl $1, %eax
1:	movabsq $0x2222222222222222, %rcx
	cmpq %rcx, %rbp
	je 2f
	orl $2, %eax
2:	movabsq $0x3333333333333333, %rcx
	cmpq %rcx, %r12
	je 3f
	orl $4, %eax
3:	movabsq $0x4444444444444444, %rcx
	cmpq %rcx, %r13
	je 4f
	orl $8, %eax
4:	movabsq $0x5555555555555555, %rcx
	cmpq %rcx, %r14
	je 5f
	orl $16, %eax
5:	movabsq $0x6666666666666666, %rcx
	cmpq %rcx, %r15
	je 6f
	orl $32, %eax
6:	addq $8, %rsp
	popq %r15
	popq %r14
	popq %r13
	popq %r12
	popq %rbp
	popq %rbx
	ret
	.section .note.GNU-stack,"",@progbits
