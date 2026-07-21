# Demo

The compiler is a Lean library, not a command-line tool: a program is authored as a
`Com` (or extracted from Rust by hax), and the compile functions lower it to a
backend together with a proof that the emitted code computes the source. Below are
two worked programs. Build each with `lake build <module>` (the first build compiles
the dependencies; see [BUILDING.md](BUILDING.md)).

## A Lean-authored kernel → AArch64 and RISC-V

Module `CatCrypt.Crypto.SecureCompilation.MultiBackendDemo`. The source is a kernel
in the shared register waist, authored as a `Com`:

```lean
-- v2 := v0 · v1 ; ret v2
def mulCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) := …
```

Compiling it, each step carrying its correctness:

```lean
-- Com → register program:
theorem mulCom_flatten : comToRegProg mulCom 2 = [RegStmt.mul "v2" "v0" "v1"] := by rfl

-- register program → AArch64 machine block, computing the source denotation:
theorem mulCom_arm (s : BState) :
    runBBlock s (lowerBBlock (regToBOp (comToRegProg mulCom 2)))
      = armTarget.denote (comToRegProg mulCom 2) s

-- …and → RISC-V, with the same guarantee:
theorem mulCom_riscv_e2e (V) (s : RState64) (hs) :
    (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg mulCom 2)))).regs (comRetName mulCom 2)
      = Com.denote mulCom V
```

```bash
lake build CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
```

`com_riscv_e2e` in the same module gives this guarantee for every supported `Com`, so
`mulCom` is one instance of the general result.

## A Rust routine, extracted with hax → compiled

Module `CatCrypt.Crypto.SecureCompilation.CompileFromHaxLinkExample`. The source calls
the SHA-256 message-schedule σ₀ leaf:

```rust
fn sigma0_caller(inp: &[u32]) -> u32 {
    sha256_sigma0(inp[0])          // sha256_sigma0 is a fast leaf, provided separately
}
```

hax extracts it to the THIR the front lowers, `let r = sha256_sigma0(inp[0]); ret r`.
The front produces a `Com` with one leaf-call boundary; linking the leaf yields the
whole-program theorem:

```lean
def outerSigma0Thir : Thir := .let_ "r" (.call "sha256_sigma0" [.inp 0]) (.ret (.lvar "r"))
def outerSigma0Com  : Com jasminDialect … := (thirToJasmin … outerSigma0Thir).get …

-- given the σ₀ leaf's agreement, the compiled program denotes the FIPS 180-4 formula:
theorem linkedExample_correct … (x : BitVec 32) :
    outerSigma0Com.denote … = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3
```

```bash
lake build CatCrypt.Crypto.SecureCompilation.CompileFromHaxLinkExample
```

## Headline theorems, trusted base, and the manual

```bash
lake env lean AxiomAudit.lean        # the axioms the three headline theorems rest on
cd docs && lake build CompilerManual && lake exe compiler-manual --output _out
```
