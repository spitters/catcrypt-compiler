# Import parameters for s2n-bignum's `bignum_montmul_p384`; sourced by
# import_s2n.sh.  `@FRAME@` in `convention` is replaced by the saved registers.

ident=S2nMontmulP384
src_dir=p384
pin_commit=7bd7c8ca1f3316fbc705d464e23f31358aff9e8a
pin_sha256=d9521c0e0c8308a3b7426a6ebc84aa987e79dbaca075876f083565adcf425b4f
macros='`mulpadd` and `montredc`'
computes='the Montgomery product'

read -r -d '' description <<'TXT' || true
`s2nMontmulP384Block` is the body of s2n-bignum's hand-written x86-64 Montgomery
multiplication modulo `p_384 = 2^384 - 2^128 - 2^96 + 2^32 - 1`: for six-limb inputs
`x`, `y` it writes `z = x * y * 2^(-384) mod p_384`, under the precondition
`x * y <= 2^384 * p_384` stated in the source (it holds when `x, y < p_384`).
TXT

read -r -d '' convention <<'TXT' || true
System V AMD64, as in s2n-bignum's header: `%rdi` points to the six output limbs
`z`, `%rsi` to the input limbs `x`, `%rdx` to the input limbs `y`, each
little-endian at offsets `0, 8, …, 40`. The block copies `%rdx` to `%rcx` and reads
`y` through `%rcx`, reads `x` through `%rsi`, and writes `z` through `%rdi`. The
omitted frame saves and restores @FRAME@.
TXT

# The tactic of the length theorem.  The default, `unfold` then `simp only`,
# is what new kernels use; this module keeps the form it was committed with.
length_tactic='simp only [s2nMontmulP384Block, List.length_append]; rfl'
