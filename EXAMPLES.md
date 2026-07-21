# Examples

Buildable example modules, each a single file. Build one with
`lake build <module>` or elaborate it with `lake env lean <path>` to run its
`#eval`s. Start with [GETTING_STARTED.md](GETTING_STARTED.md) and
[DEMO.md](DEMO.md); this is the fuller index.

| Module | What it shows |
|---|---|
| `SecureCompilation.CompilerHelloDemo` | A hax-extracted Rust routine compiled to AArch64, with the emitted assembly printed. |
| `SecureCompilation.CompileFromHaxLinkExample` | A hax routine calling a leaf, linked to the SHA-256 σ₀ kernel, proved to denote the FIPS 180-4 formula. |
| `SecureCompilation.MultiBackendDemo` | One source `Com` compiled to both AArch64 and RISC-V, each with the theorem that the machine block computes the source denotation. |
| `SecureCompilation.RelationalFrontCurve25519` | The Curve25519 base-field add and multiply realized by relational compilation from their `ZMod` specifications, with the field laws proved. |
| `Jasmin.Examples.JincParserDemo` | The import direction: a hand-written Jasmin `.jinc` leaf parsed into the IR and inspected. |
| `SecureCompilation.MLIR.VectorDialect.LoweringAVX512Demo` | A SIMD vector-dialect kernel lowered to AVX-512. |

The correctness capstones behind these are named in the manual's "Headline theorems"
section; `lake env lean AxiomAudit.lean` prints the axioms they rest on.
