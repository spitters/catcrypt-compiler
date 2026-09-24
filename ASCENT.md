# The ascent

The ascent proves that low-level code computes its mathematical specification. It takes
a program at one of the compiler's levels (a `LowCT` command, an x86 instruction block,
or an RV64 instruction block) and relates each run of it to a function on integers,
field elements or bit vectors. The largest results are about machine code that is
actually linked: the x86 blocks of the Ed25519 implementation, and s2n-bignum's P-384
Montgomery multiplication.

The calculus follows AutoCorres (Greenaway, Andronick, Klein, ITP 2012; Greenaway, Lim,
Andronick, Klein, PLDI 2014), and its design and vocabulary follow Sebastian Graf's
Lean port [sgraf812/ascent](https://github.com/sgraf812/ascent); see
[PROVENANCE.md](PROVENANCE.md).

## Contents

1. [How it works](#how-it-works)
2. [Quick start](#quick-start)
3. [Tactics](#tactics)
4. [Results on shipped machine code](#results-on-shipped-machine-code)
5. [Demos](#demos)
6. [A worked path: from a `LowCT` kernel to its Jasmin program](#a-worked-path-from-a-lowct-kernel-to-its-jasmin-program)
7. [Further reading](#further-reading)

## How it works

The central judgment is a correspondence square in the style of AutoCorres. A state
relation `SR` links concrete states to abstract ones. `Corres SR P f c` says: from a
concrete state related to an abstract state `a` with `P a`, the program `c` runs to a
concrete state related to `f a`. Squares compose sequentially (`corres_seq`,
`corresJ_append`) and through loops (`corres_for`, `corresU_while`,
`corresU_whileFun`). The same judgment is instantiated over three machines:

| Program | Semantics | Judgment |
|---|---|---|
| `LowCT` command | `semScalar`, and `semU` with `while` | `Corres`, `CorresU` |
| x86 block `List (JInstr 64)` | `runBlock`, the Lean transcription of Jasmin's x86 semantics, with registers, memory and flags | `CorresJ` |
| RV64 block | `runRBlock64` | `CorresR` |

Word abstraction maps machine words to rings (`wEnc : BitVec 64 → ZMod 2^64`), so a
carry chain over limbs becomes one addition of integers. The compiler's verified
lowering runs in the opposite direction, and the two meet in `legWeld`, which joins a
source program, the Jasmin program the compiler emits for it, and an ascent square.

## Quick start

The module [Demos/Decide](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Decide.lean)
lifts a two-line kernel to its specification over `ZMod 2^64`:

```lean
/-- The arithmetic kernel `t := a + b; r := t * c`. -/
def arithK : LowCT :=
  .RSeq (.RScalarSetExpr "t" (.SAdd (.SVar "a") (.SVar "b")))
    (.RScalarSetExpr "r" (.SMul (.SVar "t") (.SVar "c")))

theorem arithK_expr : Corres SRwordNT (fun _ => True) (asemWExpr arithK) arithK := by
  ascend_expr!
```

Build it with

```
lake build CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Decide
```

`ascend_expr!` decides that the kernel lies in the arithmetic fragment and closes the
goal with the soundness theorem `ascend_expr_sound`. The specification `asemWExpr arithK`
is the kernel's abstract denotation; a theorem about a particular kernel relates it to
the intended mathematics, as the shipped-code results below do.

## Tactics

| Goal | Tactic |
|---|---|
| a straight-line `LowCT` kernel at its word specification (`asemW`, `asemWExpr`, `asemWBV`) | `ascend!`, `ascend_expr!`, `ascend_bitwise!`, `ascend_unified!` |
| the same for a large or generated kernel | `ascend_meta` |
| a straight-line `LowCT` kernel mixing arithmetic and bitwise operations, at a `wordStep` fold | `corres_sym_scalar`, `corres_solve_scalar` |
| an x86 block at an abstract fold | `corres_sym` |
| an RV64 block at an abstract fold | `corres_sym_rv` |
| a kernel with loops, conditionals or arrays | the theorems `ascendG_sound`, `ascendGL_sound_scalar`, `tsLowCT_sound` |
| carry-out and Montgomery range side goals | `mont_bound` |

`corres_sym` and `corres_sym_rv` run a symbolic-execution engine over the block and
return the side conditions that `decide` does not close. The choice of tactic per goal
shape is discussed in
[Ascent/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md#choosing-a-tactic).

## Results on shipped machine code

Each theorem states what the linked x86 block computes under Jasmin's x86 semantics
(`runBlock`, or `runBlockA` with addressed memory). The hypotheses are that the input and output buffers do not
overlap and, where the algorithm needs it, that the inputs are reduced.

| Kernel | Result | Theorem | Module |
|---|---|---|---|
| `ed25519_point_add` | the encoded bytes decode to a block that computes Edwards addition | `paShippedBytes_correct` | [Ed25519PointAddBytes](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519PointAddBytes.lean) |
| `ed25519_madd` | mixed addition in `ZMod p25519` | `maddShipped_correct_cross` | [Ed25519MaddShippedProof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519MaddShippedProof.lean) |
| `ed25519_invert` | the inverse in `ZMod p25519` | `invertShipped_correct` | [Ed25519InvertShippedProof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519InvertShippedProof.lean) |
| `ed25519_compress` | the encoding `y + 2^255 · (x mod 2)` of the affine point | `compressShipped_correct_addr` | [Ed25519CompressShippedProof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519CompressShippedProof.lean) |
| `ed25519_sc_reduce` | `x mod L` | `scReduceShipped_correct_addr` | [Ed25519ScReduceShippedProof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519ScReduceShippedProof.lean) |
| `ed25519_sc_muladd` | `(a·b + c) mod L` | `scMuladdShipped_correct_addr` | [Ed25519ScMuladdShippedProof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519ScMuladdShippedProof.lean) |
| `fe25519_mul`, `fe25519_sqr` | `x · y mod p25519` | `feMulBlock_mod`, `feSqrBlock_mod` | [Fe25519MulSqrProof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Fe25519MulSqrProof.lean) |
| `fe25519_add`, `fe25519_sub` | `(x ± y) mod p25519` | `feAddBlock_correct`, `feSubBlock_correct` | [Fe25519AddSubSelectProof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Fe25519AddSubSelectProof.lean) |
| comb-table select | the selected entry, at the bytes, with a leakage trace independent of the index | `combSelectBytes_correct`, `selBytes_constant_time` | [CombSelectBytes](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/CombSelectBytes.lean) |
| s2n-bignum `bignum_montmul_p384` | `x · y · 2^-384 mod p384`, and the same for its encoded bytes | `s2nMontmulP384_correct`, `s2nMontmulP384_bytesCorresJ` | [S2nMontmulP384Proof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Proof.lean), [S2nMontmulP384Bytes](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Bytes.lean) |
| `mpn_and_n` loop | the exported Jasmin loop halts with the array its model denotes | `binAnd_export_machine_shipped` | [JasminLsemExportShippedAnd](CatCrypt/Crypto/SecureCompilation/VIR/JasminLsemExportShippedAnd.lean) |

The Ed25519 proofs cut each block at boundary certificates and check each part in its
own module ([Ed25519PointAddShippedProof](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519PointAddShippedProof.lean)
shows the pattern), so every module elaborates within a few gigabytes.

## Demos

Each demo is a small, self-contained module under
[`Ascent/Demos/`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/).

Tactics on small kernels:

| Demo | Shows | Main theorem |
|---|---|---|
| [Decide](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Decide.lean) | the deciding tactics on arithmetic and bitwise kernels | `arithK_expr` |
| [Scalar](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Scalar.lean) | `corres_solve_scalar` on a ChaCha quarter-round fragment | `qrFrag_refines` |
| [X86StraightLine](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/X86StraightLine.lean) | `corres_sym` on x86 carry chains and on compiler output | `sbb3_refines` |
| [Riscv](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Riscv.lean) | an RV64 add with carry-out | `addCarry_ascends` |
| [HeapAbs](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/HeapAbs.lean) | an `n`-limb addition over the generic value abstraction | `feAddN_capstone` |

From source to machine:

| Demo | Shows | Main theorem |
|---|---|---|
| [LeanSourceX86](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/LeanSourceX86.lean) | a Lean function compiled to x86 and ascended back | `add_descent_x86` |
| [LeanSourceRiscv](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/LeanSourceRiscv.lean) | the same on RV64 | `add_descent_riscv` |
| [SourceToBytes](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/SourceToBytes.lean) | source-to-Jasmin capstones evaluated at their values | `feSub_value` |
| [Strengthen](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Strengthen.lean) | the result monad chosen per kernel by type strengthening | `feSubC_ts_refines` |

Loops and early exit:

| Demo | Shows | Main theorem |
|---|---|---|
| [WhileFunSum](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/WhileFunSum.lean) | a `while` loop read as a function (sum of `1..k`) | `sumLoop_total` |
| [WhileFunSumJasmin](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/WhileFunSumJasmin.lean) | the same loop through the compiler to Jasmin | `sumLoop_jasminDenote` |
| [EarlyExit](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/EarlyExit.lean) | a search loop with `return`, read as an exception program | `searchU_except_found` |
| [MillerLoopKernelBench](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/MillerLoopKernelBench.lean) | a counted Miller loop over field leaves | `millerLoopProg_corres` |

## A worked path: from a `LowCT` kernel to its Jasmin program

[FeSubSymbolic.lean](CatCrypt/Crypto/SecureCompilation/Ascent/FeSubSymbolic.lean)
proves that the Jasmin program the compiler emits for `r := a - b` computes the
difference, for all inputs:

```lean
theorem feSub_symbolic_source_to_jasmin (a b : BitVec 64) :
    feSubSymJcom.denote (ctMapValD (valAB a b)) = ctTransTy (a - b)
```

1. **Ascent.** `corres_solve_scalar` proves
   `Corres SRwordBV (fun _ => True) _ feSubSymC`; the abstract step sets `r` to the
   wrapping difference.
2. **Weld.** `corresScalar_jasminDenote` carries the square through the compiler's
   front and its Jasmin lowering, at the entry environment the valuation `valAB a b`
   induces.
3. **Entry map.** The front produces the same program at a map that resolves every
   name, which discharges the weld's side condition (`comSubAll_eq`, by `rfl`).

[ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#a-worked-path-fesub_source_to_bytes_tower)
traces the longer path from a Rust-subset source through `legWeld`.

## Further reading

- [Ascent/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md): module map,
  naming conventions, choice of tactic, and how to add a kernel.
- [ASCENT_REFERENCE.md](ASCENT_REFERENCE.md): the layers of the calculus with their
  declarations, the loop rules, the results at the source and leaf boundaries, and the
  precise hypotheses of each result.
- [PROVENANCE.md](PROVENANCE.md): what the package takes from
  [sgraf812/ascent](https://github.com/sgraf812/ascent).
