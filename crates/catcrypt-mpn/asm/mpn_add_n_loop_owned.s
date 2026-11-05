	.text
	.globl mpn_add_n_loop_owned
	.type mpn_add_n_loop_owned, @function
mpn_add_n_loop_owned:
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
	movq $0, %rax
	movq $0, %rdi
	movq %rsi, %rbp
	cmpq $0, %rbp
	je .Lmpn_add_n_loop_owned_1073741829
.Lmpn_add_n_loop_owned_5:
	movq %rdi, %rsi
	movq 48(%rsp), %r14
	movq (%r14, %rsi, 8), %r8
	movq -8(%rsp), %r14
	movq (%r14, %rsi, 8), %r9
	movq $1, %r10
	movq %r8, %r10
	shrq $1, %r10
	movq $1, %r11
	movq %r9, %r11
	shrq $1, %r11
	movq %r10, %r12
	addq %r11, %r12
	movq %r8, %r10
	andq %r9, %r10
	movq $1, %r11
	movq %r10, %r13
	andq %r11, %r13
	movq %r12, %r10
	addq %r13, %r10
	movq $63, %r11
	movq %r10, %r11
	shrq $63, %r11
	movq %r11, %r10
	movq %r8, %r11
	addq %r9, %r11
	movq $18446744073709551615, %r8
	movq %r11, %r9
	andq %r8, %r9
	movq %r9, %r8
	movq $1, %r9
	movq %r8, %r9
	shrq $1, %r9
	movq $1, %r11
	movq %rax, %r11
	shrq $1, %r11
	movq %r9, %r12
	addq %r11, %r12
	movq %r8, %r9
	andq %rax, %r9
	movq $1, %r11
	movq %r9, %r13
	andq %r11, %r13
	movq %r12, %r9
	addq %r13, %r9
	movq $63, %r11
	movq %r9, %r11
	shrq $63, %r11
	movq %r11, %r9
	movq %r8, %r11
	addq %rax, %r11
	movq $18446744073709551615, %r8
	movq %r11, %r12
	andq %r8, %r12
	movq %r12, %r8
	movq 56(%rsp), %r14
	movq %r8, (%r14, %rsi, 8)
	movq %r10, %rsi
	addq %r9, %rsi
	movq %rsi, %r8
	movq %r8, %rax
	addq $1, %rdi
	subq $1, %rbp
	cmpq %rcx, %rbp
	cmpq %rdx, %rbp
	cmpq %rbx, %rbp
	cmpq $0, %rbp
	jne .Lmpn_add_n_loop_owned_5
.Lmpn_add_n_loop_owned_1073741829:
	movq 40(%rsp), %rbx
	movq 32(%rsp), %rbp
	movq 24(%rsp), %r12
	movq 16(%rsp), %r13
	movq 8(%rsp), %r14
	movq 0(%rsp), %r15
	leaq 64(%rsp), %rsp
	ret
	.section .note.GNU-stack,"",@progbits
