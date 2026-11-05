	.text
	.globl mpn_ior_n_loop_owned
	.type mpn_ior_n_loop_owned, @function
mpn_ior_n_loop_owned:
	leaq -64(%rsp), %rsp
	movq %rdi, 56(%rsp)
	movq %rsi, 48(%rsp)
	movq %rbx, 40(%rsp)
	movq %rbp, 32(%rsp)
	movq %r12, 24(%rsp)
	movq %r13, 16(%rsp)
	movq %r14, 8(%rsp)
	movq %r15, 0(%rsp)
	movq %rsi, %r14
	movq %rdx, -8(%rsp)
	movq %rcx, -16(%rsp)
	movq 56(%rsp), %rbx
	movq 48(%rsp), %rcx
	movq -16(%rsp), %rsi
	movq %rbx, %rbx
	movq $0, %rax
	movq %rsi, %rdi
	cmpq $0, %rdi
	je .Lmpn_ior_n_loop_owned_1073741828
.Lmpn_ior_n_loop_owned_4:
	movq %rax, %rsi
	movq 48(%rsp), %r14
	movq (%r14, %rsi, 8), %rbp
	movq -8(%rsp), %r14
	movq (%r14, %rsi, 8), %r8
	movq %rbp, %r9
	xorq %r8, %r9
	movq %rbp, %r10
	andq %r8, %r10
	movq %r9, %rbp
	xorq %r10, %rbp
	movq %rbp, %r8
	movq 56(%rsp), %r14
	movq %r8, (%r14, %rsi, 8)
	movq %rbx, %rbx
	addq $1, %rax
	subq $1, %rdi
	cmpq %rcx, %rdi
	cmpq %rdx, %rdi
	cmpq $0, %rdi
	jne .Lmpn_ior_n_loop_owned_4
.Lmpn_ior_n_loop_owned_1073741828:
	movq 40(%rsp), %rbx
	movq 32(%rsp), %rbp
	movq 24(%rsp), %r12
	movq 16(%rsp), %r13
	movq 8(%rsp), %r14
	movq 0(%rsp), %r15
	leaq 64(%rsp), %rsp
	ret
	.section .note.GNU-stack,"",@progbits
