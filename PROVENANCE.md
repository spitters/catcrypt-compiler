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

## The ascent

The ascent (`CatCrypt/Crypto/SecureCompilation/Ascent/`, described in
[ASCENT.md](ASCENT.md)) follows the AutoCorres abstraction of C programs (Greenaway,
Andronick, Klein, ITP 2012; Greenaway, Lim, Andronick, Klein, PLDI 2014) as ported to
Lean by Sebastian Graf in [sgraf812/ascent](https://github.com/sgraf812/ascent)
("WIP AutoCorres2 in Lean"). The package takes the design of the calculus from that
port: a `Corres` correspondence relation, abstraction in AutoCorres phases (the port
develops type strengthening and word abstraction, with heap examples in its tests), and
the names `Ascent`, `ascend` and `Corres`. The port states its correspondence over the
weakest-precondition metatheory `Std.Internal.Do`; the package relates its x86
correspondence to Lean's `Std.Do` triples in `RunBlockMvcgen`. The module docstrings
credit the port.

The definitions and proofs in the package are written for its own semantics. The
package's `Corres` is a forward simulation over the `LowCT` denotation `semScalar`. The
port's `Corres`, described in its README, was an abstract-interpretation inequality
between `Std.Internal.Do` weakest preconditions; at revision `1fdcb17` (2026-07-10) its
judgment is `RTriple`, a triple over the relational weakest precondition `rwp` of a
`Concretization` with value and exception couplings, and its `ascend` engine is a
worklist driver over registered rules. A comparison of the 293 distinct declaration names in the port's Lean
files (revision `1fdcb17`) with the declarations of the package's `Ascent` modules finds
two common names, `Heap` and `incr`, with different definitions, and no declaration
taken from the port. The port's repository has no license file.

## The `Com` dialect framework

The `Com` IR — typed SSA dialects, each carrying a Lean denotation — follows the
structure of [lean-mlir](https://github.com/opencompl/lean-mlir), used via the
Veir library. lean-mlir shapes the IR; code generation runs through CatCrypt's own
backend and does not depend on it for emitting bytes. The `ComToVeir` path
is an optional export to MLIR, not part of code generation.
