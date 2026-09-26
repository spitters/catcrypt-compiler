	.text
	.globl j_bn254_Fp2_add
	.type j_bn254_Fp2_add, @function
j_bn254_Fp2_add:
	leaq -80(%rsp), %rsp
	movq %rdi, 72(%rsp)
	movq %rsi, 64(%rsp)
	movq %rbx, 56(%rsp)
	movq %rbp, 48(%rsp)
	movq %r12, 40(%rsp)
	movq %r13, 32(%rsp)
	movq %r14, 24(%rsp)
	movq %r15, 16(%rsp)
	movq %rdx, -8(%rsp)
	movq 72(%rsp), %rbx
	movq 64(%rsp), %rcx
	movq -8(%rsp), %r15
	movq %r15, 8(%rsp)
	movq $0, %rax
	movq %rax, %rsi
	movq $1, %rax
	movq %rax, %rsi
	movq $2, %rax
	movq %rax, %rsi
	movq $3, %rax
	movq %rax, %rsi
	movq $4, %rax
	movq %rax, %rsi
	movq $5, %rax
	movq %rax, %rsi
	movq $6, %rax
	movq %rax, %rsi
	movq $7, %rax
	movq %rax, %rsi
	movq $0, %rax
	movq %rax, %rsi
	movq %rcx, %r14
	movq (%r14, %rsi, 8), %rax
	movq $1, %rsi
	movq %rsi, %rdi
	movq (%r14, %rdi, 8), %rsi
	movq $2, %rdi
	movq %rdi, %rbp
	movq (%r14, %rbp, 8), %rdi
	movq $3, %rbp
	movq %rbp, %r8
	movq (%r14, %r8, 8), %rbp
	movq $0, %r8
	movq %r8, %r9
	movq %r15, %r14
	movq (%r14, %r9, 8), %r8
	movq $1, %r9
	movq %r9, %r10
	movq (%r14, %r10, 8), %r9
	movq $2, %r10
	movq %r10, %r11
	movq (%r14, %r11, 8), %r10
	movq $3, %r11
	movq %r11, %r12
	movq (%r14, %r12, 8), %r11
	movl $0, %r12d
	movq %rax, %r13
	btq $0, %r12
	adcxq %r8, %r13
	movq %rsi, %rax
	adcxq %r9, %rax
	movq %rdi, %rdx
	adcxq %r10, %rdx
	movq %rbp, %rdi
	adcxq %r11, %rdi
	movq $14114127202429895352, %rsi
	movl $1, %ebp
	movq %r13, %r8
	btq $0, %rbp
	adcxq %rsi, %r8
	movq $7529619929231668594, %rsi
	movq %rax, %rbp
	adcxq %rsi, %rbp
	movq $5165552122434856866, %rsi
	movq %rdx, %r9
	adcxq %rsi, %r9
	movq $14959745806906580950, %rsi
	movq %rdi, %r10
	adcxq %rsi, %r10
	movq $0, %rsi
	movq %rsi, %r11
	adcxq %rsi, %r11
	movq %r11, %r12
	xorq $1, %r12
	movq $0, %r11
	subq %r12, %r11
	movq %r11, %rsi
	movq %r13, %r11
	andq %rsi, %r11
	movq $18446744073709551615, %r12
	movq %rsi, %r13
	xorq %r12, %r13
	movq %r8, %r12
	andq %r13, %r12
	movq %r11, %r8
	addq %r12, %r8
	movq %r8, %r11
	movq %rax, %r8
	andq %rsi, %r8
	movq $18446744073709551615, %rax
	movq %rsi, %r12
	xorq %rax, %r12
	movq %rbp, %rax
	andq %r12, %rax
	movq %r8, %rbp
	addq %rax, %rbp
	movq %rbp, %rax
	movq %rdx, %rbp
	andq %rsi, %rbp
	movq $18446744073709551615, %rdx
	movq %rsi, %r8
	xorq %rdx, %r8
	movq %r9, %rdx
	andq %r8, %rdx
	movq %rbp, %r8
	addq %rdx, %r8
	movq %r8, %rdx
	movq %rdi, %rbp
	andq %rsi, %rbp
	movq $18446744073709551615, %rdi
	movq %rsi, %r8
	xorq %rdi, %r8
	movq %r10, %rsi
	andq %r8, %rsi
	movq %rbp, %rdi
	addq %rsi, %rdi
	movq %rdi, %rsi
	movq $0, %rdi
	movq %rdi, %rbp
	movq %rbx, %r14
	movq %r11, (%r14, %rbp, 8)
	movq $1, %rdi
	movq %rdi, %rbp
	movq %rax, (%r14, %rbp, 8)
	movq $2, %rax
	movq %rax, %rdi
	movq %rdx, (%r14, %rdi, 8)
	movq $3, %rax
	movq %rax, %rdx
	movq %rsi, (%r14, %rdx, 8)
	movq $4, %rax
	movq %rax, %rdx
	movq 64(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $5, %rdx
	movq %rdx, %rsi
	movq (%r14, %rsi, 8), %rdx
	movq $6, %rsi
	movq %rsi, %rdi
	movq (%r14, %rdi, 8), %rsi
	movq $7, %rdi
	movq %rdi, %rbp
	movq (%r14, %rbp, 8), %rdi
	movq $4, %rcx
	movq %rcx, %rbp
	movq -8(%rsp), %r14
	movq (%r14, %rbp, 8), %rcx
	movq $5, %rbp
	movq %rbp, %r8
	movq (%r14, %r8, 8), %rbp
	movq $6, %r8
	movq %r8, %r9
	movq (%r14, %r9, 8), %r8
	movq $7, %r9
	movq %r9, %r10
	movq (%r14, %r10, 8), %r9
	movl $0, %r10d
	movq %rax, %r11
	btq $0, %r10
	adcxq %rcx, %r11
	movq %rdx, %rax
	adcxq %rbp, %rax
	movq %rsi, %rdx
	adcxq %r8, %rdx
	movq %rdi, %rcx
	adcxq %r9, %rcx
	movq $14114127202429895352, %rsi
	movl $1, %edi
	movq %r11, %rbp
	btq $0, %rdi
	adcxq %rsi, %rbp
	movq $7529619929231668594, %rsi
	movq %rax, %rdi
	adcxq %rsi, %rdi
	movq $5165552122434856866, %rsi
	movq %rdx, %r8
	adcxq %rsi, %r8
	movq $14959745806906580950, %rsi
	movq %rcx, %r9
	adcxq %rsi, %r9
	movq $0, %rsi
	movq %rsi, %r10
	adcxq %rsi, %r10
	movq %r10, %r12
	xorq $1, %r12
	movq $0, %r10
	subq %r12, %r10
	movq %r10, %rsi
	movq %r11, %r10
	andq %rsi, %r10
	movq $18446744073709551615, %r11
	movq %rsi, %r12
	xorq %r11, %r12
	movq %rbp, %r11
	andq %r12, %r11
	movq %r10, %rbp
	addq %r11, %rbp
	movq %rbp, %r10
	movq %rax, %rbp
	andq %rsi, %rbp
	movq $18446744073709551615, %rax
	movq %rsi, %r11
	xorq %rax, %r11
	movq %rdi, %rax
	andq %r11, %rax
	movq %rbp, %rdi
	addq %rax, %rdi
	movq %rdi, %rax
	movq %rdx, %rdi
	andq %rsi, %rdi
	movq $18446744073709551615, %rdx
	movq %rsi, %rbp
	xorq %rdx, %rbp
	movq %r8, %rdx
	andq %rbp, %rdx
	movq %rdi, %rbp
	addq %rdx, %rbp
	movq %rbp, %rdx
	movq %rcx, %rdi
	andq %rsi, %rdi
	movq $18446744073709551615, %rcx
	movq %rsi, %rbp
	xorq %rcx, %rbp
	movq %r9, %rcx
	andq %rbp, %rcx
	movq %rdi, %rsi
	addq %rcx, %rsi
	movq %rsi, %rcx
	movq $4, %rsi
	movq %rsi, %rdi
	movq 72(%rsp), %r14
	movq %r10, (%r14, %rdi, 8)
	movq $5, %rsi
	movq %rsi, %rdi
	movq %rax, (%r14, %rdi, 8)
	movq $6, %rax
	movq %rax, %rsi
	movq %rdx, (%r14, %rsi, 8)
	movq $7, %rax
	movq %rax, %rdx
	movq %rcx, (%r14, %rdx, 8)
	movq 56(%rsp), %rbx
	movq 48(%rsp), %rbp
	movq 40(%rsp), %r12
	movq 32(%rsp), %r13
	movq 24(%rsp), %r14
	movq 16(%rsp), %r15
	leaq 80(%rsp), %rsp
	ret
	.section .note.GNU-stack,"",@progbits

	.text
	.globl j_bn254_Fp2_sub
	.type j_bn254_Fp2_sub, @function
j_bn254_Fp2_sub:
	leaq -80(%rsp), %rsp
	movq %rdi, 72(%rsp)
	movq %rsi, 64(%rsp)
	movq %rbx, 56(%rsp)
	movq %rbp, 48(%rsp)
	movq %r12, 40(%rsp)
	movq %r13, 32(%rsp)
	movq %r14, 24(%rsp)
	movq %r15, 16(%rsp)
	movq %rdx, -8(%rsp)
	movq 72(%rsp), %rbx
	movq 64(%rsp), %rcx
	movq -8(%rsp), %r15
	movq %r15, 8(%rsp)
	movq $0, %rax
	movq %rax, %rsi
	movq $1, %rax
	movq %rax, %rsi
	movq $2, %rax
	movq %rax, %rsi
	movq $3, %rax
	movq %rax, %rsi
	movq $4, %rax
	movq %rax, %rsi
	movq $5, %rax
	movq %rax, %rsi
	movq $6, %rax
	movq %rax, %rsi
	movq $7, %rax
	movq %rax, %rsi
	movq $0, %rax
	movq %rax, %rsi
	movq %rcx, %r14
	movq (%r14, %rsi, 8), %rax
	movq $1, %rsi
	movq %rsi, %rdi
	movq (%r14, %rdi, 8), %rsi
	movq $2, %rdi
	movq %rdi, %rbp
	movq (%r14, %rbp, 8), %rdi
	movq $3, %rbp
	movq %rbp, %r8
	movq (%r14, %r8, 8), %rbp
	movq $0, %r8
	movq %r8, %r9
	movq %r15, %r14
	movq (%r14, %r9, 8), %r8
	movq $1, %r9
	movq %r9, %r10
	movq (%r14, %r10, 8), %r9
	movq $2, %r10
	movq %r10, %r11
	movq (%r14, %r11, 8), %r10
	movq $3, %r11
	movq %r11, %r12
	movq (%r14, %r12, 8), %r11
	movq $18446744073709551615, %r12
	movq %r8, %r13
	xorq %r12, %r13
	movl $1, %r8d
	movq %rax, %r12
	btq $0, %r8
	adcxq %r13, %r12
	setc %dl
	movzbq %dl, %rdx
	movq $18446744073709551615, %rax
	movq %r9, %r8
	xorq %rax, %r8
	movq %rsi, %rax
	btq $0, %rdx
	adcxq %r8, %rax
	setc %r9b
	movzbq %r9b, %r9
	movq $18446744073709551615, %rdx
	movq %r10, %rsi
	xorq %rdx, %rsi
	movq %rdi, %rdx
	btq $0, %r9
	adcxq %rsi, %rdx
	setc %r8b
	movzbq %r8b, %r8
	movq $18446744073709551615, %rsi
	movq %r11, %rdi
	xorq %rsi, %rdi
	movq %rbp, %rsi
	btq $0, %r8
	adcxq %rdi, %rsi
	movq $0, %rdi
	movq %rdi, %rbp
	adcxq %rdi, %rbp
	movq %rbp, %r8
	xorq $1, %r8
	movq $0, %rbp
	subq %r8, %rbp
	movq %rbp, %rdi
	movq $4332616871279656263, %rbp
	movq %rbp, %r8
	andq %rdi, %r8
	movq %r8, %rbp
	movl $0, %r8d
	movq %r12, %r9
	btq $0, %r8
	adcxq %rbp, %r9
	setc %r10b
	movzbq %r10b, %r10
	movq $10917124144477883021, %rbp
	movq %rbp, %r8
	andq %rdi, %r8
	movq %r8, %rbp
	movq %rax, %r8
	btq $0, %r10
	adcxq %rbp, %r8
	setc %r11b
	movzbq %r11b, %r11
	movq $13281191951274694749, %rax
	movq %rax, %rbp
	andq %rdi, %rbp
	movq %rbp, %rax
	movq %rdx, %rbp
	btq $0, %r11
	adcxq %rax, %rbp
	setc %r10b
	movzbq %r10b, %r10
	movq $3486998266802970665, %rax
	movq %rax, %rdx
	andq %rdi, %rdx
	movq %rdx, %rax
	movq %rsi, %rdx
	btq $0, %r10
	adcxq %rax, %rdx
	movq $0, %rax
	movq %rax, %rsi
	movq %rbx, %r14
	movq %r9, (%r14, %rsi, 8)
	movq $1, %rax
	movq %rax, %rsi
	movq %r8, (%r14, %rsi, 8)
	movq $2, %rax
	movq %rax, %rsi
	movq %rbp, (%r14, %rsi, 8)
	movq $3, %rax
	movq %rax, %rsi
	movq %rdx, (%r14, %rsi, 8)
	movq $4, %rax
	movq %rax, %rdx
	movq 64(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $5, %rdx
	movq %rdx, %rsi
	movq (%r14, %rsi, 8), %rdx
	movq $6, %rsi
	movq %rsi, %rdi
	movq (%r14, %rdi, 8), %rsi
	movq $7, %rdi
	movq %rdi, %rbp
	movq (%r14, %rbp, 8), %rdi
	movq $4, %rcx
	movq %rcx, %rbp
	movq -8(%rsp), %r14
	movq (%r14, %rbp, 8), %rcx
	movq $5, %rbp
	movq %rbp, %r8
	movq (%r14, %r8, 8), %rbp
	movq $6, %r8
	movq %r8, %r9
	movq (%r14, %r9, 8), %r8
	movq $7, %r9
	movq %r9, %r10
	movq (%r14, %r10, 8), %r9
	movq $18446744073709551615, %r10
	movq %rcx, %r11
	xorq %r10, %r11
	movl $1, %ecx
	movq %rax, %r10
	btq $0, %rcx
	adcxq %r11, %r10
	setc %r12b
	movzbq %r12b, %r12
	movq $18446744073709551615, %rax
	movq %rbp, %rcx
	xorq %rax, %rcx
	movq %rdx, %rax
	btq $0, %r12
	adcxq %rcx, %rax
	setc %bpl
	movzbq %bpl, %rbp
	movq $18446744073709551615, %rcx
	movq %r8, %rdx
	xorq %rcx, %rdx
	movq %rsi, %rcx
	btq $0, %rbp
	adcxq %rdx, %rcx
	setc %r8b
	movzbq %r8b, %r8
	movq $18446744073709551615, %rdx
	movq %r9, %rsi
	xorq %rdx, %rsi
	movq %rdi, %rdx
	btq $0, %r8
	adcxq %rsi, %rdx
	movq $0, %rsi
	movq %rsi, %rdi
	adcxq %rsi, %rdi
	movq %rdi, %rbp
	xorq $1, %rbp
	movq $0, %rdi
	subq %rbp, %rdi
	movq %rdi, %rsi
	movq $4332616871279656263, %rdi
	movq %rdi, %rbp
	andq %rsi, %rbp
	movq %rbp, %rdi
	movl $0, %ebp
	movq %r10, %r8
	btq $0, %rbp
	adcxq %rdi, %r8
	setc %r9b
	movzbq %r9b, %r9
	movq $10917124144477883021, %rdi
	movq %rdi, %rbp
	andq %rsi, %rbp
	movq %rbp, %rdi
	movq %rax, %rbp
	btq $0, %r9
	adcxq %rdi, %rbp
	setc %r10b
	movzbq %r10b, %r10
	movq $13281191951274694749, %rax
	movq %rax, %rdi
	andq %rsi, %rdi
	movq %rdi, %rax
	movq %rcx, %rdi
	btq $0, %r10
	adcxq %rax, %rdi
	setc %r9b
	movzbq %r9b, %r9
	movq $3486998266802970665, %rax
	movq %rax, %rcx
	andq %rsi, %rcx
	movq %rcx, %rax
	movq %rdx, %rcx
	btq $0, %r9
	adcxq %rax, %rcx
	movq $4, %rax
	movq %rax, %rdx
	movq 72(%rsp), %r14
	movq %r8, (%r14, %rdx, 8)
	movq $5, %rax
	movq %rax, %rdx
	movq %rbp, (%r14, %rdx, 8)
	movq $6, %rax
	movq %rax, %rdx
	movq %rdi, (%r14, %rdx, 8)
	movq $7, %rax
	movq %rax, %rdx
	movq %rcx, (%r14, %rdx, 8)
	movq 56(%rsp), %rbx
	movq 48(%rsp), %rbp
	movq 40(%rsp), %r12
	movq 32(%rsp), %r13
	movq 24(%rsp), %r14
	movq 16(%rsp), %r15
	leaq 80(%rsp), %rsp
	ret
	.section .note.GNU-stack,"",@progbits

	.text
	.globl j_bn254_Fp2_felem_copy
	.type j_bn254_Fp2_felem_copy, @function
j_bn254_Fp2_felem_copy:
	leaq -64(%rsp), %rsp
	movq %rdi, 56(%rsp)
	movq %rsi, 48(%rsp)
	movq %rbx, 40(%rsp)
	movq %rbp, 32(%rsp)
	movq %r12, 24(%rsp)
	movq %r13, 16(%rsp)
	movq %r14, 8(%rsp)
	movq %r15, 0(%rsp)
	movq 56(%rsp), %rbx
	movq 48(%rsp), %rcx
	movq $0, %rax
	movq %rax, %rdx
	movq $1, %rax
	movq %rax, %rdx
	movq $2, %rax
	movq %rax, %rdx
	movq $3, %rax
	movq %rax, %rdx
	movq $4, %rax
	movq %rax, %rdx
	movq $5, %rax
	movq %rax, %rdx
	movq $6, %rax
	movq %rax, %rdx
	movq $7, %rax
	movq %rax, %rdx
	movq $0, %rax
	movq %rax, %rdx
	movq %rcx, %r14
	movq (%r14, %rdx, 8), %rax
	movq $0, %rdx
	movq %rdx, %rsi
	movq %rbx, %r14
	movq %rax, (%r14, %rsi, 8)
	movq $1, %rax
	movq %rax, %rdx
	movq 48(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $1, %rdx
	movq %rdx, %rsi
	movq 56(%rsp), %r14
	movq %rax, (%r14, %rsi, 8)
	movq $2, %rax
	movq %rax, %rdx
	movq 48(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $2, %rdx
	movq %rdx, %rsi
	movq 56(%rsp), %r14
	movq %rax, (%r14, %rsi, 8)
	movq $3, %rax
	movq %rax, %rdx
	movq 48(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $3, %rdx
	movq %rdx, %rsi
	movq 56(%rsp), %r14
	movq %rax, (%r14, %rsi, 8)
	movq $4, %rax
	movq %rax, %rdx
	movq 48(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $4, %rdx
	movq %rdx, %rsi
	movq 56(%rsp), %r14
	movq %rax, (%r14, %rsi, 8)
	movq $5, %rax
	movq %rax, %rdx
	movq 48(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $5, %rdx
	movq %rdx, %rsi
	movq 56(%rsp), %r14
	movq %rax, (%r14, %rsi, 8)
	movq $6, %rax
	movq %rax, %rdx
	movq 48(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $6, %rdx
	movq %rdx, %rsi
	movq 56(%rsp), %r14
	movq %rax, (%r14, %rsi, 8)
	movq $7, %rax
	movq %rax, %rdx
	movq 48(%rsp), %r14
	movq (%r14, %rdx, 8), %rax
	movq $7, %rcx
	movq %rcx, %rdx
	movq 56(%rsp), %r14
	movq %rax, (%r14, %rdx, 8)
	movq 40(%rsp), %rbx
	movq 32(%rsp), %rbp
	movq 24(%rsp), %r12
	movq 16(%rsp), %r13
	movq 8(%rsp), %r14
	movq 0(%rsp), %r15
	leaq 64(%rsp), %rsp
	ret
	.section .note.GNU-stack,"",@progbits
