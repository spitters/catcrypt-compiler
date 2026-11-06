# `CatCrypt/Crypto/Jasmin/`: LowCT, the Jasmin AST and the reflect surfaces

This directory holds the source language LowCT with its semantics and analyses, the
Jasmin AST and its operational semantics, the `.jinc` import path, and the reflect
surfaces that elaborate Lean programs to LowCT for each primitive. Modules are in the
namespace `CatCrypt.Crypto.Jasmin`. The word-level Jasmin dialect (`jasminDialect`)
and its lowerings live in `SecureCompilation/VIR/`.

## Entry points

| Module | Contents |
|---|---|
| [`LowCT`](LowCT.lean) | `LowCT`, the typed low-level constant-time command language; `RustExec`, its execution relation |
| [`LowCTReflect`](LowCTReflect.lean) | the elaborator `reifyLowCT%` from Lean value-level programs to `LowCT` |
| [`LowCTDSL`](LowCTDSL.lean) | the LowCT surface syntax |
| [`LowCTCTAnalysis`](LowCTCTAnalysis.lean) | the constant-time analysis `cmdCT` and `cmdCT_sound` |
| [`InfoFlow`](InfoFlow.lean) | information-flow rules for LowCT |
| [`LowCTBorrowCheck`](LowCTBorrowCheck.lean), [`LowCTBorrowCheckSig`](LowCTBorrowCheckSig.lean), [`PointerBorrow`](PointerBorrow.lean) | borrow checks and frame theorems |
| [`LowCTToJasmin`](LowCTToJasmin.lean) | LowCT to the Jasmin AST |
| [`RustEmit`](RustEmit.lean) | Rust source from LowCT |
| [`JasminAST`](JasminAST.lean), [`JasminSem`](JasminSem.lean), [`JasminOps`](JasminOps.lean) | the Jasmin AST, its semantics and x86 operation semantics |
| [`JasminCoqSemMirror`](JasminCoqSemMirror.lean) | a port of `jasminc`'s Coq operational semantics |
| [`JasminToRustEmit`](JasminToRustEmit.lean), [`JasminToRustEmitSimulates`](JasminToRustEmitSimulates.lean) | Jasmin AST to safe Rust, with its simulation theorem |
| [`JincToCom`](JincToCom.lean), [`JincElab`](JincElab.lean), [`JincToLowCT`](JincToLowCT.lean) | the `.jinc` import path: text, untyped AST, `Com jasminDialect`, the compiler's x86; [JINC_IMPORT.md](../../../JINC_IMPORT.md) states its fragment, its imports and its theorems |
| [`MemoryModel`](MemoryModel.lean), [`Hoare`](Hoare.lean) | the flat memory model and Hoare triples over `JasminMemState` |
| [`ISA`](ISA.lean) | the ISA abstraction for compiler targets |
| [`BignumExec`](BignumExec.lean), [`InstrRReflect`](InstrRReflect.lean), `BignumHoare/` | the bignum SSA fragment, its interpreter and reflective evaluators |

## Reflect surfaces

`*Reflect.lean` modules (for example [`X25519Reflect`](X25519Reflect.lean),
[`P384EcdsaReflect`](P384EcdsaReflect.lean), [`Poseidon2Reflect`](Poseidon2Reflect.lean),
[`ShaNiReflect`](ShaNiReflect.lean)) register a primitive's leaves and elaborate its
orchestration to LowCT with `reifyLowCT%`. [CAPABILITIES.md](../../../CAPABILITIES.md)
states what is proved about each primitive.

## Subdirectories

| Directory | Contents |
|---|---|
| `AES/` | AES-128 specification, a Jasmin program and their equivalence |
| `BignumHoare/` | reflective evaluators for field exponentiation chains, field-parametric in `EvalChainGeneric` and for chain-shaped LowCT in `LowCTReflectiveEval`, and the contract of the `bignum_montmul_p25519` call |
| `BLS12_381/`, `P256/` | instances of `EvalChainGeneric` for BLS12-381 and P-256 |
| `Ed25519/` | Ed25519 field-leaf chains, the compress leaf and its correctness |
| `Mpn/` | width-parametric multi-precision kernels and the q̂ bound |
| `Passes/` | constant folding, dead-code and no-op elimination on the Jasmin AST |
| `Examples/` | worked examples and emit drivers |

## Conventions

- A new primitive front: copy the nearest `*Reflect.lean`, register the leaves, and
  state the lowering checks as its siblings do.
- The Rust route reaches LowCT from `CatCrypt/Crypto/Hax/`
  ([AGENTS.md](../Hax/AGENTS.md)); the LowCT front to the SSA IR is in
  `SecureCompilation/Dialects/`.
