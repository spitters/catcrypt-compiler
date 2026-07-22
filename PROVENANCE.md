# Provenance

The low-level design of the CatCrypt compiler builds on prior verified-compilation
work. This file records the lineage.

## The low-level command IR (`LowCT`)

`LowCT` — the compiler's low-level constant-time command IR — and its `bedrockC` /
`rust_cmd` command language are ported from
[AUCurves](https://github.com/AU-COBRA/AUCurves), a Coq development that compiles
elliptic-curve code through the **bedrock2** verified low-level language. Through
AUCurves the design inherits the command-language and semantics style of
[bedrock2](https://github.com/mit-plv/bedrock2).

## Relational compilation

The relational front — compiling a Lean specification to a low-level program by a
denotation-preserving relation — follows the approach of
[Rupicola](https://github.com/mit-plv/rupicola), which relationally compiles
Gallina to bedrock2.

## Connecting the bedrock2 / AUCurves lineage to Jasmin

CatCrypt bridges this bedrock2/AUCurves-style command IR to the
[Jasmin](https://github.com/jasmin-lang/jasmin) toolchain: `LowCT` lowers to a
word-level Jasmin dialect (`LowCTToJasmin`), so a source can target the Jasmin
compiler (`jasminc`) in addition to CatCrypt's byte-level backend. This
carries the relational / bedrock2 low-level design onto the Jasmin path for
constant-time assembly.

## The `Com` dialect framework

The `Com` IR — typed SSA dialects, each carrying a Lean denotation — follows the
structure of [lean-mlir](https://github.com/opencompl/lean-mlir), used via the
Veir library. lean-mlir shapes the IR; code generation runs through CatCrypt's own
backend and does not depend on it for emitting bytes. The `ComToVeir` path
is an optional export to MLIR, not part of code generation.
