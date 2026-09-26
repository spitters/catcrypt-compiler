	.att_syntax
	.text
	.p2align	5
	.global	msm_term_rustcmd
	.type	msm_term_rustcmd, %function
msm_term_rustcmd:
	movq	%rsp, %r10
	leaq	-16(%rsp), %rsp
	andq	$-8, %rsp
	movq	(%rdx), %rax
	movq	%rax, (%rsp)
	movq	(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	8(%rsp), %rax
	movq	%rax, (%rdi)
	movq	%r10, %rsp
	ret
	.ident	"Jasmin Compiler 2026.03.1"
	.section	".note.GNU-stack", "", %progbits
