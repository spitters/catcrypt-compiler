	.att_syntax
	.text
	.p2align	5
	.global	plonky3_air_eval_fib_3_16_rc
	.global	plonky3_air_eval_fib_3_8_rc
	.type	plonky3_air_eval_fib_3_16_rc, %function
plonky3_air_eval_fib_3_16_rc:
	movq	%rsp, %r11
	leaq	-392(%rsp), %rsp
	andq	$-8, %rsp
	movq	(%rsi), %rax
	movq	%rax, 8(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 16(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 24(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 32(%rsp)
	movq	32(%rsi), %rax
	movq	%rax, 40(%rsp)
	movq	40(%rsi), %rax
	movq	%rax, 48(%rsp)
	movq	48(%rsi), %rax
	movq	%rax, 56(%rsp)
	movq	56(%rsi), %rax
	movq	%rax, 64(%rsp)
	movq	64(%rsi), %rax
	movq	%rax, 72(%rsp)
	movq	72(%rsi), %rax
	movq	%rax, 80(%rsp)
	movq	80(%rsi), %rax
	movq	%rax, 88(%rsp)
	movq	88(%rsi), %rax
	movq	%rax, 96(%rsp)
	movq	96(%rsi), %rax
	movq	%rax, 104(%rsp)
	movq	104(%rsi), %rax
	movq	%rax, 112(%rsp)
	movq	112(%rsi), %rax
	movq	%rax, 120(%rsp)
	movq	120(%rsi), %rax
	movq	%rax, 128(%rsp)
	movq	128(%rsi), %rax
	movq	%rax, 136(%rsp)
	movq	136(%rsi), %rax
	movq	%rax, 144(%rsp)
	movq	144(%rsi), %rax
	movq	%rax, 152(%rsp)
	movq	152(%rsi), %rax
	movq	%rax, 160(%rsp)
	movq	160(%rsi), %rax
	movq	%rax, 168(%rsp)
	movq	168(%rsi), %rax
	movq	%rax, 176(%rsp)
	movq	176(%rsi), %rax
	movq	%rax, 184(%rsp)
	movq	184(%rsi), %rax
	movq	%rax, 192(%rsp)
	movq	192(%rsi), %rax
	movq	%rax, 200(%rsp)
	movq	200(%rsi), %rax
	movq	%rax, 208(%rsp)
	movq	208(%rsi), %rax
	movq	%rax, 216(%rsp)
	movq	216(%rsi), %rax
	movq	%rax, 224(%rsp)
	movq	224(%rsi), %rax
	movq	%rax, 232(%rsp)
	movq	232(%rsi), %rax
	movq	%rax, 240(%rsp)
	movq	240(%rsi), %rax
	movq	%rax, 248(%rsp)
	movq	248(%rsi), %rax
	movq	%rax, 256(%rsp)
	movq	256(%rsi), %rax
	movq	%rax, 264(%rsp)
	movq	264(%rsi), %rax
	movq	%rax, 272(%rsp)
	movq	272(%rsi), %rax
	movq	%rax, 280(%rsp)
	movq	280(%rsi), %rax
	movq	%rax, 288(%rsp)
	movq	288(%rsi), %rax
	movq	%rax, 296(%rsp)
	movq	296(%rsi), %rax
	movq	%rax, 304(%rsp)
	movq	304(%rsi), %rax
	movq	%rax, 312(%rsp)
	movq	312(%rsi), %rax
	movq	%rax, 320(%rsp)
	movq	320(%rsi), %rax
	movq	%rax, 328(%rsp)
	movq	328(%rsi), %rax
	movq	%rax, 336(%rsp)
	movq	336(%rsi), %rax
	movq	%rax, 344(%rsp)
	movq	344(%rsi), %rax
	movq	%rax, 352(%rsp)
	movq	352(%rsi), %rax
	movq	%rax, 360(%rsp)
	movq	360(%rsi), %rax
	movq	%rax, 368(%rsp)
	movq	368(%rsi), %rax
	movq	%rax, 376(%rsp)
	movq	376(%rsi), %rax
	movq	%rax, 384(%rsp)
	movq	$1, %rax
	movq	8(%rsp), %rcx
	cmpq	$0, %rcx
	je  	Lplonky3_air_eval_fib_3_16_rc$32
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$32:
	movq	16(%rsp), %rcx
	cmpq	$1, %rcx
	je  	Lplonky3_air_eval_fib_3_16_rc$31
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$31:
	movq	8(%rsp), %rcx
	movq	16(%rsp), %rdx
	movq	32(%rsp), %rsi
	movq	40(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$30
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$30:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$29
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$29:
	movq	32(%rsp), %rcx
	movq	40(%rsp), %rdx
	movq	56(%rsp), %rsi
	movq	64(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$28
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$28:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$27
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$27:
	movq	56(%rsp), %rcx
	movq	64(%rsp), %rdx
	movq	80(%rsp), %rsi
	movq	88(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$26
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$26:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$25
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$25:
	movq	80(%rsp), %rcx
	movq	88(%rsp), %rdx
	movq	104(%rsp), %rsi
	movq	112(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$24
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$24:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$23
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$23:
	movq	104(%rsp), %rcx
	movq	112(%rsp), %rdx
	movq	128(%rsp), %rsi
	movq	136(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$22
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$22:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$21
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$21:
	movq	128(%rsp), %rcx
	movq	136(%rsp), %rdx
	movq	152(%rsp), %rsi
	movq	160(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$20
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$20:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$19
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$19:
	movq	152(%rsp), %rcx
	movq	160(%rsp), %rdx
	movq	176(%rsp), %rsi
	movq	184(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$18
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$18:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$17
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$17:
	movq	176(%rsp), %rcx
	movq	184(%rsp), %rdx
	movq	200(%rsp), %rsi
	movq	208(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$16
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$16:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$15
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$15:
	movq	200(%rsp), %rcx
	movq	208(%rsp), %rdx
	movq	224(%rsp), %rsi
	movq	232(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$14
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$14:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$13
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$13:
	movq	224(%rsp), %rcx
	movq	232(%rsp), %rdx
	movq	248(%rsp), %rsi
	movq	256(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$12
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$12:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$11
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$11:
	movq	248(%rsp), %rcx
	movq	256(%rsp), %rdx
	movq	272(%rsp), %rsi
	movq	280(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$10
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$10:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$9
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$9:
	movq	272(%rsp), %rcx
	movq	280(%rsp), %rdx
	movq	296(%rsp), %rsi
	movq	304(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$8
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$8:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$7
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$7:
	movq	296(%rsp), %rcx
	movq	304(%rsp), %rdx
	movq	320(%rsp), %rsi
	movq	328(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$6
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$6:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$5
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$5:
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	344(%rsp), %rsi
	movq	352(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$4
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$4:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$3
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$3:
	movq	344(%rsp), %rcx
	movq	352(%rsp), %rdx
	movq	368(%rsp), %rsi
	movq	376(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$2
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$2:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_16_rc$1
	movq	$0, %rax
Lplonky3_air_eval_fib_3_16_rc$1:
	movq	%rax, (%rsp)
	movq	(%rsp), %rax
	movq	%rax, (%rdi)
	movq	%r11, %rsp
	ret
	.type	plonky3_air_eval_fib_3_8_rc, %function
plonky3_air_eval_fib_3_8_rc:
	movq	%rsp, %r11
	leaq	-200(%rsp), %rsp
	andq	$-8, %rsp
	movq	(%rsi), %rax
	movq	%rax, 8(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 16(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 24(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 32(%rsp)
	movq	32(%rsi), %rax
	movq	%rax, 40(%rsp)
	movq	40(%rsi), %rax
	movq	%rax, 48(%rsp)
	movq	48(%rsi), %rax
	movq	%rax, 56(%rsp)
	movq	56(%rsi), %rax
	movq	%rax, 64(%rsp)
	movq	64(%rsi), %rax
	movq	%rax, 72(%rsp)
	movq	72(%rsi), %rax
	movq	%rax, 80(%rsp)
	movq	80(%rsi), %rax
	movq	%rax, 88(%rsp)
	movq	88(%rsi), %rax
	movq	%rax, 96(%rsp)
	movq	96(%rsi), %rax
	movq	%rax, 104(%rsp)
	movq	104(%rsi), %rax
	movq	%rax, 112(%rsp)
	movq	112(%rsi), %rax
	movq	%rax, 120(%rsp)
	movq	120(%rsi), %rax
	movq	%rax, 128(%rsp)
	movq	128(%rsi), %rax
	movq	%rax, 136(%rsp)
	movq	136(%rsi), %rax
	movq	%rax, 144(%rsp)
	movq	144(%rsi), %rax
	movq	%rax, 152(%rsp)
	movq	152(%rsi), %rax
	movq	%rax, 160(%rsp)
	movq	160(%rsi), %rax
	movq	%rax, 168(%rsp)
	movq	168(%rsi), %rax
	movq	%rax, 176(%rsp)
	movq	176(%rsi), %rax
	movq	%rax, 184(%rsp)
	movq	184(%rsi), %rax
	movq	%rax, 192(%rsp)
	movq	$1, %rax
	movq	8(%rsp), %rcx
	cmpq	$0, %rcx
	je  	Lplonky3_air_eval_fib_3_8_rc$16
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$16:
	movq	16(%rsp), %rcx
	cmpq	$1, %rcx
	je  	Lplonky3_air_eval_fib_3_8_rc$15
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$15:
	movq	8(%rsp), %rcx
	movq	16(%rsp), %rdx
	movq	32(%rsp), %rsi
	movq	40(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$14
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$14:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$13
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$13:
	movq	32(%rsp), %rcx
	movq	40(%rsp), %rdx
	movq	56(%rsp), %rsi
	movq	64(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$12
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$12:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$11
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$11:
	movq	56(%rsp), %rcx
	movq	64(%rsp), %rdx
	movq	80(%rsp), %rsi
	movq	88(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$10
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$10:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$9
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$9:
	movq	80(%rsp), %rcx
	movq	88(%rsp), %rdx
	movq	104(%rsp), %rsi
	movq	112(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$8
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$8:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$7
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$7:
	movq	104(%rsp), %rcx
	movq	112(%rsp), %rdx
	movq	128(%rsp), %rsi
	movq	136(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$6
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$6:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$5
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$5:
	movq	128(%rsp), %rcx
	movq	136(%rsp), %rdx
	movq	152(%rsp), %rsi
	movq	160(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$4
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$4:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$3
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$3:
	movq	152(%rsp), %rcx
	movq	160(%rsp), %rdx
	movq	176(%rsp), %rsi
	movq	184(%rsp), %r8
	movq	$2013265921, %r9
	addq	%rsi, %r9
	subq	%rdx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$2
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$2:
	addq	%rdx, %rcx
	addq	$-2013265921, %rcx
	movq	%rcx, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %rcx
	movq	$2013265921, %r9
	addq	%r8, %r9
	subq	%rcx, %r9
	addq	$-2013265921, %r9
	movq	%r9, %rsi
	sarq	$63, %rsi
	andq	$2013265921, %rsi
	addq	%rsi, %r9
	cmpq	$0, %r9
	je  	Lplonky3_air_eval_fib_3_8_rc$1
	movq	$0, %rax
Lplonky3_air_eval_fib_3_8_rc$1:
	movq	%rax, (%rsp)
	movq	(%rsp), %rax
	movq	%rax, (%rdi)
	movq	%r11, %rsp
	ret
	.ident	"Jasmin Compiler 2026.03.1"
	.section	".note.GNU-stack", "", %progbits
