# Import parameters for s2n-bignum's `bignum_montsqr_p384`; sourced by
# import_s2n.sh.  `@FRAME@` in `convention` is replaced by the saved registers.

ident=S2nMontsqrP384
src_dir=p384
pin_commit=7bd7c8ca1f3316fbc705d464e23f31358aff9e8a
pin_sha256=5e2b95a1592b11aed7d3a14d8d02f5b8a0669614b7fe7e8ac5bc89959918b01b
macros='`mulpadd` and `montreds`'
computes='the Montgomery square'

read -r -d '' description <<'TXT' || true
`s2nMontsqrP384Block` is the body of s2n-bignum's hand-written x86-64 Montgomery
squaring modulo `p_384 = 2^384 - 2^128 - 2^96 + 2^32 - 1`: for a six-limb input `x`
it writes `z = x^2 * 2^(-384) mod p_384`, under the precondition
`x^2 <= 2^384 * p_384` stated in the source (it holds when `x < p_384`).
TXT

read -r -d '' convention <<'TXT' || true
System V AMD64, as in s2n-bignum's header: `%rdi` points to the six output limbs
`z` and `%rsi` to the six input limbs `x`, each little-endian at offsets
`0, 8, …, 40`. The block reads `x` through `%rsi` until the last squaring term
overwrites `%rsi`, uses the output limb `z[0]` to hold `%rbx` during the
reduction, and writes `z` through `%rdi`. The omitted frame saves and restores
@FRAME@.
TXT
