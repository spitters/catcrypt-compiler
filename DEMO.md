# Demo

The compiler is a Lean library rather than a command-line tool. A program is a Rust
source extracted by hax or a Lean specification, and compiling it means applying
verified functions and building the module; every program enters through a front.
This page walks what the demo compiles and what is proved about it; [Getting
started](GETTING_STARTED.md) has the install and the first run.

## Compiling a program to assembly

`CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo` takes a Rust routine,

```rust
fn f(a: u64, b: u64) -> u64 { let t = a * b; t + a }
```

hax extracts it, the front (`thirToJasmin`) lowers it to a `Com`, and the backend
compiles that to the AArch64 block `srcArm`. [Getting
started](GETTING_STARTED.md) runs the module and shows the three instructions it
prints.

Two theorems cover the route the value takes. `ThirToComFront.thirToJasmin_denote`
proves the front's output `Com` denotes the source THIR. `ScalarLinNeutralDemo.com_arm_e2e`
proves the AArch64 side: for a straight-line `Com` over the supported op set
(`ComOK`) in an all-`reg 64` context, the compiled-and-run machine block, read at
the result register, computes the source `Com.denote`. The demo's `srcCom` is such
a program and `srcArm` is that compiled block.

`ARMBackend.ComToArmLsem.comToArmLsem_correct` restates the AArch64 result over the
`runBBlock` machine model on the base-ALU subset (`ADD`/`SUB`/`AND`/`ORR`/`EOR`),
adding that every executed instruction lies in the subset whose encoding is checked
against the transcribed `sail-arm` decode clauses. The demo's multiply is outside
that subset. `RISCVBackend.ComToRiscvLsem.comToRiscvLsem_correct` is the RISC-V
counterpart, where each executed step is additionally proved equal to the
sail-riscv `execute_RTYPE` clause.

## The relational front

`CatCrypt.Crypto.SecureCompilation.RelationalFrontCurve25519` is a second entry
point: a Lean specification, compiled by realizing it over a concrete carrier. The
Curve25519 base field is `ZMod q` with `q = 2²⁵⁵ − 19`; the front realizes each
field operation over a 4×64-bit limb vector and proves the abstract operation equals
the emitted kernel.

```lean
abbrev Fe25519P := ZMod curve25519Q          -- the base field, q = 2²⁵⁵ − 19

/-- Abstract `ZMod q` addition equals the emitted 4×64-bit limb kernel. -/
theorem c25519_add_commutes (a b : Fe25519P) :
    (a + b).val
      = bignumVal (mlAddModK c25519Limbs (encMLK curve25519Q 4 a)
                                         (encMLK curve25519Q 4 b)) :=
  encMLK_add_commutes c25519KLimbPrime a b
```

`c25519_mul_commutes` is the multiplication counterpart. Build both with:

```bash
lake build CatCrypt.Crypto.SecureCompilation.RelationalFrontCurve25519
```

## Headline theorems

Three theorems state the compiler's correctness end to end:

- [`rustToJasminCom_endToEnd`](CatCrypt/Crypto/SecureCompilation/VIR/CompilerCorrectnessExtracted.lean)
  — for a source in the covered fragment (`IsCoveredCtl`), given the front's
  adequacy edge and the per-pass success witnesses, a hax-extracted Rust routine
  and the Jasmin `Com` it compiles to compute the same value.
- [`robustCompilation_source_to_x86`](CatCrypt/Crypto/SecureCompilation/VIR/RobustCompilationPipeline.lean)
  — for every lattice-dialect source program the emitted x86, executed and decoded,
  has the source's meaning, and is constant-time. Jasmin's verified compiler enters
  as an explicit `JasminVerifiedCompiler` hypothesis, alongside leaf agreement and
  the SSA-naming injectivity side conditions.
- [`compileVia_comp_correct`](CatCrypt/Crypto/SecureCompilation/VIR/LoweringDataComp.lean)
  — for a program compiled through a chain of dialects (`d → d' → jasmin`), running
  the owned-emitted code computes the composite value transport of the program's
  denotation. The single-dialect case (`compileVia_correct`) and the lattice
  route (`compile_correct_all`) are instances.

The trusted base these rest on is described in [PROVENANCE.md](PROVENANCE.md).

## The manual

```bash
cd docs && lake update && lake build CompilerManual && lake exe compiler-manual --output _out
```
