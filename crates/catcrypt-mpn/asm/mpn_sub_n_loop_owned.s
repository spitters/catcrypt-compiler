	.text
	.globl mpn_sub_n_loop_owned
	.type mpn_sub_n_loop_owned, @function
mpn_sub_n_loop_owned:
	leaq -80(%rsp), %rsp
	movq %rdi, 72(%rsp)
	movq %rsi, 64(%rsp)
	movq %rbx, 56(%rsp)
	movq %rbp, 48(%rsp)
	movq %r12, 40(%rsp)
	movq %r13, 32(%rsp)
	movq %r14, 24(%rsp)
	movq %r15, 16(%rsp)
	movq %rsi, %r14
	movq %rdx, -8(%rsp)
	movq %rcx, -16(%rsp)
	movq 72(%rsp), %rbx
	movq 64(%rsp), %rcx
	movq -8(%rsp), %r15
	movq %r15, 8(%rsp)
	movq -16(%rsp), %rsi
	movq $0, %rax
	movq $0, %rdi
	movq %rsi, %rbp
	cmpq $0, %rbp
	je .Lmpn_sub_n_loop_owned_1073741829
.Lmpn_sub_n_loop_owned_5:
	movq %rdi, %rsi
	movq 64(%rsp), %r14
	movq (%r14, %rsi, 8), %r8
	movq -8(%rsp), %r14
	movq (%r14, %rsi, 8), %r9
	movq $18446744073709551615, %r10
	movq %r9, %r11
	xorq %r10, %r11
	movq %r11, %r9
	movq $1, %r10
	movq %rax, %r11
	xorq %r10, %r11
	movq %r11, %r10
	movq $1, %r11
	movq %r8, %r11
	shrq $1, %r11
	movq $1, %r12
	movq %r9, %r12
	shrq $1, %r12
	movq %r11, %r13
	addq %r12, %r13
	movq %r8, %r11
	andq %r9, %r11
	movq $1, %r12
	movq %r11, %rdx
	andq %r12, %rdx
	movq %r13, %r11
	addq %rdx, %r11
	movq $63, %rdx
	movq %r11, %rdx
	shrq $63, %rdx
	movq %rdx, %r11
	movq %r8, %rdx
	addq %r9, %rdx
	movq $18446744073709551615, %r8
	movq %rdx, %r9
	andq %r8, %r9
	movq %r9, %rdx
	movq $1, %r8
	movq %rdx, %r8
	shrq $1, %r8
	movq $1, %r9
	movq %r10, %r9
	shrq $1, %r9
	movq %r8, %r12
	addq %r9, %r12
	movq %rdx, %r8
	andq %r10, %r8
	movq $1, %r9
	movq %r8, %r13
	andq %r9, %r13
	movq %r12, %r8
	addq %r13, %r8
	movq $63, %r9
	movq %r8, %r9
	shrq $63, %r9
	movq %r9, %r8
	movq %rdx, %r9
	addq %r10, %r9
	movq $18446744073709551615, %rdx
	movq %r9, %r10
	andq %rdx, %r10
	movq %r10, %rdx
	movq 72(%rsp), %r14
	movq %rdx, (%r14, %rsi, 8)
	movq %r11, %rdx
	addq %r8, %rdx
	movq $1, %rsi
	movq %rdx, %r8
	xorq %rsi, %r8
	movq %r8, %rdx
	movq %rdx, %rax
	addq $1, %rdi
	subq $1, %rbp
	cmpq %rcx, %rbp
	cmpq 8(%rsp), %rbp
	cmpq %rbx, %rbp
	cmpq $0, %rbp
	jne .Lmpn_sub_n_loop_owned_5
.Lmpn_sub_n_loop_owned_1073741829:
	movq 56(%rsp), %rbx
	movq 48(%rsp), %rbp
	movq 40(%rsp), %r12
	movq 32(%rsp), %r13
	movq 24(%rsp), %r14
	movq 16(%rsp), %r15
	leaq 80(%rsp), %rsp
	ret
	.section .note.GNU-stack,"",@progbits
