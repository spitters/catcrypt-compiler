	.text
	.globl bn254_mont_mul_x86_from_lean
	.type bn254_mont_mul_x86_from_lean, @function
bn254_mont_mul_x86_from_lean:
	pushq %rbx
	pushq %r12
	pushq %r13
	pushq %r14
	pushq %r15
	pushq %rbp
	subq $32, %rsp
	movq %rsp, %rbp
	movq %rdx, %rbx
	movq $0, %rcx
	movq $0, %r8
	movq $0, %r9
	movq $0, %r10
	movq $0, %r11
	movq $0, %rax
	xorq %rcx, %rcx
	movq 0(%rbx), %rdx
	mulxq 0(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r8
	adox %r12, %r9
	mulxq 8(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r9
	adox %r12, %r10
	mulxq 16(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r10
	adox %r12, %r11
	mulxq 24(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r11
	adox %r12, %rax
	adcx %rcx, %rax
	adox %rcx, %rax
	movq %r8, %rdx
	movq $9786893198990664585, %r12
	imulq %r12, %rdx
	xorq %rcx, %rcx
	movq $4332616871279656263, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r8
	adox %r12, %r9
	movq $10917124144477883021, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r9
	adox %r12, %r10
	movq $13281191951274694749, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r10
	adox %r12, %r11
	movq $3486998266802970665, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r11
	adox %r12, %rax
	adcx %rcx, %rax
	adox %rcx, %rax
	movq %r9, %r8
	movq %r10, %r9
	movq %r11, %r10
	movq %rax, %r11
	movq $0, %rax
	xorq %rcx, %rcx
	movq 8(%rbx), %rdx
	mulxq 0(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r8
	adox %r12, %r9
	mulxq 8(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r9
	adox %r12, %r10
	mulxq 16(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r10
	adox %r12, %r11
	mulxq 24(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r11
	adox %r12, %rax
	adcx %rcx, %rax
	adox %rcx, %rax
	movq %r8, %rdx
	movq $9786893198990664585, %r12
	imulq %r12, %rdx
	xorq %rcx, %rcx
	movq $4332616871279656263, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r8
	adox %r12, %r9
	movq $10917124144477883021, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r9
	adox %r12, %r10
	movq $13281191951274694749, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r10
	adox %r12, %r11
	movq $3486998266802970665, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r11
	adox %r12, %rax
	adcx %rcx, %rax
	adox %rcx, %rax
	movq %r9, %r8
	movq %r10, %r9
	movq %r11, %r10
	movq %rax, %r11
	movq $0, %rax
	xorq %rcx, %rcx
	movq 16(%rbx), %rdx
	mulxq 0(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r8
	adox %r12, %r9
	mulxq 8(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r9
	adox %r12, %r10
	mulxq 16(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r10
	adox %r12, %r11
	mulxq 24(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r11
	adox %r12, %rax
	adcx %rcx, %rax
	adox %rcx, %rax
	movq %r8, %rdx
	movq $9786893198990664585, %r12
	imulq %r12, %rdx
	xorq %rcx, %rcx
	movq $4332616871279656263, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r8
	adox %r12, %r9
	movq $10917124144477883021, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r9
	adox %r12, %r10
	movq $13281191951274694749, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r10
	adox %r12, %r11
	movq $3486998266802970665, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r11
	adox %r12, %rax
	adcx %rcx, %rax
	adox %rcx, %rax
	movq %r9, %r8
	movq %r10, %r9
	movq %r11, %r10
	movq %rax, %r11
	movq $0, %rax
	xorq %rcx, %rcx
	movq 24(%rbx), %rdx
	mulxq 0(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r8
	adox %r12, %r9
	mulxq 8(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r9
	adox %r12, %r10
	mulxq 16(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r10
	adox %r12, %r11
	mulxq 24(%rsi), %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r11
	adox %r12, %rax
	adcx %rcx, %rax
	adox %rcx, %rax
	movq %r8, %rdx
	movq $9786893198990664585, %r12
	imulq %r12, %rdx
	xorq %rcx, %rcx
	movq $4332616871279656263, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r8
	adox %r12, %r9
	movq $10917124144477883021, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r9
	adox %r12, %r10
	movq $13281191951274694749, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r10
	adox %r12, %r11
	movq $3486998266802970665, %r12
	mulx %r12, %r13, %r12  # src1=%rdx=%rdx
	adcx %r13, %r11
	adox %r12, %rax
	adcx %rcx, %rax
	adox %rcx, %rax
	movq %r9, %r8
	movq %r10, %r9
	movq %r11, %r10
	movq %rax, %r11
	movq $0, %rax
	movq %r8, %r13
	movq $4332616871279656263, %r12
	subq %r12, %r13
	movq %r13, 0(%rbp)
	movq %r9, %r13
	movq $10917124144477883021, %r12
	sbbq %r12, %r13
	movq %r13, 8(%rbp)
	movq %r10, %r13
	movq $13281191951274694749, %r12
	sbbq %r12, %r13
	movq %r13, 16(%rbp)
	movq %r11, %r13
	movq $3486998266802970665, %r12
	sbbq %r12, %r13
	movq %r13, 24(%rbp)
	sbbq $0, %rax
	movq 0(%rbp), %r12
	cmovbq %r8, %r12
	movq %r12, 0(%rdi)
	movq 8(%rbp), %r12
	cmovbq %r9, %r12
	movq %r12, 8(%rdi)
	movq 16(%rbp), %r12
	cmovbq %r10, %r12
	movq %r12, 16(%rdi)
	movq 24(%rbp), %r12
	cmovbq %r11, %r12
	movq %r12, 24(%rdi)
	addq $32, %rsp
	popq %rbp
	popq %r15
	popq %r14
	popq %r13
	popq %r12
	popq %rbx
	ret
	.section .note.GNU-stack,"",@progbits
