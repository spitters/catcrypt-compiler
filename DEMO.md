# Demo

The compiler is a Lean library rather than a command-line tool. A program is a Rust
source extracted by hax or a Lean specification, and compiling it means applying
verified functions and building the module; every program enters through a front.
The first build compiles the dependencies (see [BUILDING.md](BUILDING.md)).

## Compiling a program to assembly

`CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo` takes a Rust routine,

```rust
fn f(a: u64, b: u64) -> u64 { let t = a * b; t + a }
```

hax extracts it, the front (`thirToJasmin`) lowers it to a `Com`, and the backend
compiles that to AArch64. Elaborating the module runs the `#eval` and prints the
emitted assembly:

```bash
lake env lean CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean
```

```
	mul w2, w1, w0
	add w3, w2, w1
	orr w4, w3, w3
```

The correctness theorems are in the same file: `thirToJasmin_denote` proves the
compiled `Com` denotes the source, and `com_riscv_e2e` proves the machine block
computes that denotation for every supported program.

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
  — a hax-extracted Rust routine and the Jasmin `Com` it compiles to compute the
  same value.
- [`robustCompilation_source_to_x86`](CatCrypt/Crypto/SecureCompilation/VIR/RobustCompilationPipeline.lean)
  — for every source program the emitted x86, executed and decoded, has the
  source's meaning, and is constant-time.
- [`compileVia_comp_correct`](CatCrypt/Crypto/SecureCompilation/VIR/LoweringDataComp.lean)
  — for a program compiled through a chain of dialects (`d → d' → jasmin`), running
  the owned-emitted code computes the composite value transport of the program's
  denotation. The single-dialect keystone (`compileVia_correct`) and the lattice
  route (`compile_correct_all`) are instances.

The trusted base these rest on is described in [PROVENANCE.md](PROVENANCE.md).

## The manual

```bash
cd docs && lake build CompilerManual && lake exe compiler-manual --output _out
```
