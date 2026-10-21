# `CatCrypt/Crypto/Hax/`: the hax-lean AST to `NFProg` and to LowCT

This directory holds the front of `compileA`, which translates hax-lean's `ImpExpr` to
`NFProg`, and the deprecated front `haxToLowCT`, which translates it to LowCT, with the
printers of LowCT back to Rust. Modules are in the namespace `CatCrypt.Crypto.Hax`. The
hax-lean AST and its semantics `denote` / `evalImp` come from the `hax-lean` dependency.

## The front of `compileA`

| Module | Contents |
|---|---|
| [`ImpToNF`](ImpToNF.lean) | `impToNF`, the structured translation of `ImpExpr` to `NFProg nfDialect` |
| [`FrontDomain`](FrontDomain.lean) | `frontOut`, the domain of `impToNF` as a function |
| [`FrontTyping`](FrontTyping.lean) | `FrontTy`, the typing judgement of the front |
| [`Module`](Module.lean) | `HaxModule`, an entry function with its callees and linked functions |
| [`HaxCallNames`](HaxCallNames.lean) | the call-name, width, scalar-value and slot-name tables, shared with `haxToLowCT` |
| [`HaxSourceLeak`](HaxSourceLeak.lean) | the source leakage of a run of `denote'` |

The import closure of `compileA` contains no `HaxToLowCT*` module; the development
repository's CI checks this.

## The deprecated front `haxToLowCT`

`haxToLowCT` remains as the producer of the protocols' `*HaxLowCTBridge` modules and of
the kernel producers. New code does not import it; the development repository's CI
freezes the set of its importers.

| Module | Contents |
|---|---|
| [`HaxToLowCT`](HaxToLowCT.lean) | `haxToLowCT : ImpExpr → Option LowCT` |
| [`LowCTSubset`](LowCTSubset.lean) | the subset filter on `ImpExpr` |
| [`HaxToLowCT_ConstFold`](HaxToLowCT_ConstFold.lean) | the constant-substitution pre-pass |
| [`HaxToLowCTExit`](HaxToLowCTExit.lean) | the exit-flag lowering of early returns |
| [`HaxToLowCTSim_Program`](HaxToLowCTSim_Program.lean) | `haxToLowCT_simulates_program`: the program-level simulation under `simScope` |
| [`HaxToLowCTSim_Full`](HaxToLowCTSim_Full.lean) | `haxToLowCT_simulates_full` |
| [`HaxToLowCTSim_ProgramTower`](HaxToLowCTSim_ProgramTower.lean) | `haxToLowCT_simulates_programT`: builtins returning scalars |
| [`HaxToLowCTSim_ProgramLit`](HaxToLowCTSim_ProgramLit.lean) | `haxToLowCT_simulates_programL`: literal call arguments |
| [`HaxToLowCTSim_ProgramFor`](HaxToLowCTSim_ProgramFor.lean), [`HaxToLowCTSim_ProgramLoops`](HaxToLowCTSim_ProgramLoops.lean), [`HaxToLowCTSim_ProgramArr`](HaxToLowCTSim_ProgramArr.lean) | counted, runtime-bound and data-dependent loops; array loads and stores |
| [`HaxToLowCTSim_Exit`](HaxToLowCTSim_Exit.lean) | `haxToLowCTFn_simulates`: early returns, over `Hax.denote'` |

The `HaxToLowCTSim_*` modules without a row hold the per-constructor cases
(`_Call`, `_If`, `_Match`, `_While`, `_AssignMatch`, `_Quarta*`) that
`HaxToLowCTSim_Main` assembles.

## Printers from LowCT to Rust

| Module | Contents |
|---|---|
| [`LowCTToHax`](LowCTToHax.lean) | `lowCTToImp : LowCT → Option ImpExpr`; `lowCTToImp_roundTrip` |
| [`LowCTToHaxSim`](LowCTToHaxSim.lean) | `lowCTToImp_simulates`: agreement with `RustExec` |
| [`ImpRustPrint`](ImpRustPrint.lean) | `ppImpRustFnRet`, the Rust printer; `parse_ppImpRustFnRet` |
| [`ImpRustHaxCheck`](ImpRustHaxCheck.lean) | `haxReadAgrees`, `haxReadAgrees_sound` |
| [`ImpRustHaxRoundTrip`](ImpRustHaxRoundTrip.lean) | `roundTrip_haxReadAgrees` on the example read back by hax |

## Conventions

- The simulations conclude a `RustExec` run of the LowCT image
  (`CatCrypt/Crypto/Jasmin/LowCT.lean`). The Rust front theorems of
  `SecureCompilation/` start at LowCT; compose with them to reach the Jasmin dialect.
- State call-side side conditions per program, as `simScope`, `ScopeBound` and
  `NamesFresh` do.
- [HAX_RUST.md](../../../HAX_RUST.md) describes the LowCT → Rust round trip and its
  procedure. The reifier and the ascent over `ImpExpr` live in
  [`CatCrypt/Hax/`](../../Hax/AGENTS.md).
