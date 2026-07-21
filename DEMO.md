# Demo

The compiler is a Lean library, not a command-line tool: a program is a Rust source
extracted by hax, or a Lean specification, and "compile" means applying verified
functions and building the module. Programs enter through a front — never as a
hand-authored `Com`. The first build compiles the dependencies; see
[BUILDING.md](BUILDING.md).

## Compile a program and see the assembly

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

The correctness sits beside it in the same file: `thirToJasmin_denote` proves the
compiled `Com` denotes the source, and `com_riscv_e2e` proves the machine block
computes that denotation for every supported program.

## The relational front

`CatCrypt.Crypto.SecureCompilation.RelationalFrontCurve25519` is the other on-ramp: a
Lean specification — the Curve25519 base-field add and multiply as `ZMod q`
operations — realized relationally over a 4×64-bit carrier, with the field laws
proved (`c25519_add_commutes`, `c25519_mul_commutes`).

```bash
lake build CatCrypt.Crypto.SecureCompilation.RelationalFrontCurve25519
```

## Headline theorems, trusted base, and the manual

```bash
lake env lean AxiomAudit.lean        # the axioms the three headline theorems rest on
cd docs && lake build CompilerManual && lake exe compiler-manual --output _out
```
