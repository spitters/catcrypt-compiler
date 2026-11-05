# Overview

This document follows one function from Rust to x86-64 bytes, states the two theorems about the
result, and gives the work this compiler builds on.

## The source

The function is from the test suite of [Aeneas](https://github.com/AeneasVerif/aeneas):

```rust
pub fn incr_array(mut x: &mut [u32; 2]) {
    x[0] += 1
}
```

Aeneas translates it to a pure Lean function. The mutable borrow becomes a returned array, and the
addition is checked, in the monad `Result`:

```lean
def incr_array (x : Array Std.U32 2#usize) : Result (Array Std.U32 2#usize) := do
  let i ← Array.index_usize x 0#usize
  let i1 ← i + 1#u32
  Array.update x 0#usize i1
```

The theorems below are about this Lean function. The step from Rust to Lean is the Aeneas translation.

The elaborator `reifyAeneas%` reads the function as a program in the first typed dialect of the
compiler. Its output contains a proof by construction:
[`incrArray_denote`](CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/Reified.lean) states that
each value of the Lean function is the denotation of the program.

## The compiled code

Every intermediate language is a typed SSA dialect with a Lean denotation. A chain of certified
passes lowers the program to the Jasmin dialect, and an untrusted allocator then assigns registers.
A verified checker accepts or rejects the allocation
([`ownedCheckMC_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVChecked.lean)). The
compiler also decides a leakage check and a decode round trip of the encoder's output. It returns
no bytes when a check fails ([PIPELINE.md](PIPELINE.md) gives each stage with its check and theorem).

A layout states the calling convention of the theorems. Here
[`incrAbi`](CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/Compiled.lean) has the array at
`%rdi`, one 64-bit word per element, and the result at the same address. The compiler returns
120 bytes, which disassemble to:

```
lea    -0x40(%rsp),%rsp
mov    %rdi,0x38(%rsp)
mov    %rsi,0x30(%rsp)
mov    %rbx,0x28(%rsp)
mov    %rbp,0x20(%rsp)
mov    %r12,0x18(%rsp)
mov    %r13,0x10(%rsp)
mov    %r14,0x8(%rsp)
mov    %r15,(%rsp)
mov    0x38(%rsp),%rbx
mov    $0x0,%rax
mov    %rbx,%r14
mov    (%r14),%rcx            # read x[0]
add    $0x1,%rcx              # add one
movabs $0xffffffff,%rbx
mov    %rcx,%rdx
and    %rbx,%rdx              # reduce to 32 bits
mov    %rdx,(%r14)            # write x[0]
mov    0x28(%rsp),%rbx
mov    0x20(%rsp),%rbp
mov    0x18(%rsp),%r12
mov    0x10(%rsp),%r13
mov    0x8(%rsp),%r14
mov    (%rsp),%r15
lea    0x40(%rsp),%rsp
ret
```

The backend saves every callee-saved register on entry, whether or not the body uses it.

## The theorems

[`incrArray_compileR_correct`](CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/Compiled.lean)
states correctness:

```lean
theorem incrArray_compileR_correct (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR incrArraySrc incrAbi "incr_array" = some (P, bytes))
    (sa : AState) (hsep : incrAbi.Regions sa) (v : Value)
    (hrun : aeneasRuns incrAbi incrArraySrc sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ incrAbi.ResultOf sa sa' v ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") incrAbi.frameLo incrAbi.frameHi) →
        (∀ p ∈ incrAbi.regions,
          SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
```

The hypothesis `hc` says that the compiler returned `bytes`. Let `sa` be a machine state that
satisfies the layout, and `v` a value of a run of the Lean function from `sa`. The bytes then decode
to a program that halts on the x86-64 model `aMachine`, with `v` in the array and `%rsp` restored.
Memory outside the stack frame and the array is unchanged. Since the addition is checked, a run with
a value is a run without overflow.

[`incrArray_compileR_ct`](CatCrypt/Crypto/SecureCompilation/AeneasFront/Demo/Compiled.lean) states
constant time, with the array secret. Two runs of any decoding of the bytes, from states that agree
on the stack register and the address of the array and from which the source has a run, have equal
leakage traces. A trace holds branch outcomes, memory addresses and the operands of variable-time
instructions, under the hardware timing regime `ctRegime`
([`ConstantTimeRel`](CatCrypt/Crypto/SecureCompilation/CT/Leakage.lean)).

The proofs in this file are short because both theorems are instances of general ones,
[`NFEntry.compileR_correct`](CatCrypt/Crypto/SecureCompilation/Haxc/ComposeV1.lean) and
[`aeneasEntry_compileR_ct`](CatCrypt/Crypto/SecureCompilation/AeneasFront/EntryCT.lean), which hold for every source of the entry. The instance supplies the level
check of the program, the label check of the layout and the distinctness of the names, each by
`decide`.

## Related work

**Verified compilers.** Our correctness theorem has the form of CompCert's [Leroy 2009]: it holds for
every program the compiler accepts. Translation validation of register allocation also comes from
CompCert [Rideau and Leroy 2010]. CakeML [Kumar et al. 2014] takes its theorem to machine code, and
ours reaches decoded bytes. Both systems cover divergence and I/O, whereas our theorem covers
terminating runs of the source.

**Constant-time compilation.** CT-CompCert [Barthe et al. 2020] and Jasmin [Almeida et al. 2017;
Barthe et al. 2021] prove that compilation preserves constant time, and our theorem follows theirs. Our trace adds the operands of variable-time instructions under a named timing regime.
CT-CompCert also covers diverging runs, and Jasmin also preserves cost. The Last Yard [Haselwarter et
al. 2024] links Jasmin programs to game-based security proofs in SSProve, and is a predecessor of
this work. Our robust-compilation statement follows Abate et al. [2019, 2020].

**Relational compilation.** Our Lean front derives programs from Lean functions in the style of
Rupicola [Pit-Claudel et al. 2022], which targets Bedrock2 [Erbsen et al. 2021].

**Templates.** Fiat Cryptography [Erbsen et al. 2019] proves field arithmetic once over all
parameters, and AUCurves [Hvass et al. 2023] builds field inversion and curve arithmetic on it. We
extend the method to lattice transforms, hash functions, GHASH and extension towers
([FIAT_TEMPLATES.md](FIAT_TEMPLATES.md)). CryptOpt [Kuepper et al. 2023] searches for fast assembly and
checks each result against Fiat Cryptography; our ascent also certifies its output.

**Typed dialects.** The dialect structure comes from MLIR [Lattner et al. 2021]. Our intrinsically
typed SSA programs follow Lean-MLIR [Bhat et al. 2024], and the package has a bridge to
[Veir](https://github.com/opencompl/veir).

**Rust.** The two Rust routes use hax [Bhargavan et al. 2024] and Aeneas [Ho and Protzenko 2022].

**Decompilation and machine models.** Ascent is in the line of decompilation into logic [Myreen et al.
2008] and AutoCorres [Greenaway et al. 2014]. Its targets include
[s2n-bignum](https://github.com/awslabs/s2n-bignum), which has its own proofs in HOL Light. Our x86-64
model is transcribed from Jasmin's semantics and Sail [Armstrong et al. 2019], whose x86 model derives
from x86isa [Goel et al. 2017].

### References

- Abate, Blanco, Garg, Hriţcu, Patrignani, Thibault. [Journey Beyond Full Abstraction](https://doi.org/10.1109/CSF.2019.00025). CSF 2019.
- Abate et al. [Trace-Relating Compiler Correctness and Secure Compilation](https://doi.org/10.1007/978-3-030-44914-8_1). ESOP 2020.
- Almeida et al. [Jasmin: High-Assurance and High-Speed Cryptography](https://doi.org/10.1145/3133956.3134078). CCS 2017.
- Armstrong et al. [ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS](https://doi.org/10.1145/3290384). POPL 2019.
- Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu. [Formal Verification of a Constant-Time Preserving C Compiler](https://doi.org/10.1145/3371075). POPL 2020.
- Barthe, Grégoire, Laporte, Priya. [Structured Leakage and Applications to Cryptographic Constant-Time and Cost](https://doi.org/10.1145/3460120.3484761). CCS 2021.
- Bhargavan et al. [hax: Verifying Security-Critical Rust Software using Multiple Provers](https://doi.org/10.1007/978-3-031-86695-1_7). VSTTE 2024.
- Bhat, Keizer, Hughes, Goens, Grosser. [Verifying Peephole Rewriting in SSA Compiler IRs](https://doi.org/10.4230/LIPIcs.ITP.2024.9). ITP 2024.
- Erbsen, Philipoom, Gross, Sloan, Chlipala. [Simple High-Level Code for Cryptographic Arithmetic](https://doi.org/10.1109/SP.2019.00005). S&P 2019.
- Erbsen et al. [Integration Verification across Software and Hardware for a Simple Embedded System](https://doi.org/10.1145/3453483.3454065). PLDI 2021.
- Goel, Hunt, Kaufmann. [Engineering a Formal, Executable x86 ISA Simulator for Software Verification](https://doi.org/10.1007/978-3-319-48628-4_8). 2017.
- Greenaway, Lim, Andronick, Klein. [Don't Sweat the Small Stuff](https://doi.org/10.1145/2594291.2594296). PLDI 2014.
- Haselwarter et al. [The Last Yard: Foundational End-to-End Verification of High-Speed Cryptography](https://doi.org/10.1145/3636501.3636961). CPP 2024.
- Ho, Protzenko. [Aeneas: Rust Verification by Functional Translation](https://doi.org/10.1145/3547647). ICFP 2022.
- Hvass, Aranha, Spitters. [High-Assurance Field Inversion for Curve-Based Cryptography](https://doi.org/10.1109/CSF57540.2023.00008). CSF 2023.
- Kuepper et al. [CryptOpt: Verified Compilation with Randomized Program Search for Cryptographic Primitives](https://doi.org/10.1145/3591272). PLDI 2023.
- Kumar, Myreen, Norrish, Owens. [CakeML: A Verified Implementation of ML](https://doi.org/10.1145/2535838.2535841). POPL 2014.
- Lattner et al. [MLIR: Scaling Compiler Infrastructure for Domain Specific Computation](https://doi.org/10.1109/CGO51591.2021.9370308). CGO 2021.
- Leroy. [Formal Verification of a Realistic Compiler](https://doi.org/10.1145/1538788.1538814). CACM 2009.
- Myreen, Slind, Gordon. [Machine-Code Verification for Multiple Architectures](https://doi.org/10.1109/FMCAD.2008.ECP.24). FMCAD 2008.
- Pit-Claudel et al. [Relational Compilation for Performance-Critical Applications](https://doi.org/10.1145/3519939.3523706). PLDI 2022.
- Rideau, Leroy. [Validating Register Allocation and Spilling](https://doi.org/10.1007/978-3-642-11970-5_13). CC 2010.
