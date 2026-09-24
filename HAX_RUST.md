# From Lean to Rust and back through hax

This guide covers three uses of the hax bridge of this package:

1. print a `LowCT` program as Rust and prove that the Rust hax reads back is the
   program;
2. print a pure Lean function as Rust with the same guarantee;
3. relate existing Rust, extracted by haxpipeT, to a Lean function (the ascent
   on `ImpExpr`).

All three meet in hax-lean's `ImpExpr` (`HaxLean/AST.lean`) and its semantics
`denote` / `evalImp` (`HaxLean/Semantics.lean`). The trusted base is rustc's
THIR as exported by `cargo hax json`, hax-lean's JSON adapter, and the Rust
bodies of the leaf operations.

## 1. `LowCT` → Rust

| Step | Entry point | File |
|---|---|---|
| `LowCT` → `ImpExpr` | `lowCTToImp : LowCT → Option ImpExpr` | `CatCrypt/Crypto/Hax/LowCTToHax.lean` |
| inverse of the front | `lowCTToImp_roundTrip`: `haxToLowCT e = some (frontNF c)` | same |
| semantics | `lowCTToImp_simulates` | `CatCrypt/Crypto/Hax/LowCTToHaxSim.lean` |
| `ImpExpr` → Rust text | `ppImpRustFnRet name params retTy ty body : Option String` | `CatCrypt/Crypto/Hax/ImpRustPrint.lean` |
| printing is injective | `parse_ppImpRustFnRet` | same |
| hax reads the text back | `bench/hax_roundtrip/run.sh` | `bench/hax_roundtrip/` |
| the reading is the program | `haxReadAgrees printed reading : Bool` | `CatCrypt/Crypto/Hax/ImpRustHaxCheck.lean` |
| check ⇒ same evaluation | `haxReadAgrees_sound` | same |

Procedure:

1. Compute `e := lowCTToImp c` and the text with `ppImpRustFnRet`; write it with
   the leaf operations' Rust into a crate (`bench/hax_roundtrip/emit_roundtrip.lean`
   does this for the example).
2. Run `bench/hax_roundtrip/run.sh`: `cargo hax json` on the crate, then
   `read_back.lean` writes the reading as a Lean literal module.
3. State `haxReadAgrees e reading = true` and close it by `decide +kernel`
   (`roundTrip_haxReadAgrees` in `CatCrypt/Crypto/Hax/ImpRustHaxRoundTrip.lean`).
4. `haxReadAgrees_sound` gives `evalImp bi fuel (forToLoop reading) env =
   evalImp bi fuel (forToLoop e) env`; compose with `lowCTToImp_simulates`.

The printer covers the fragment in the table at the top of `ImpRustPrint.lean`:
straight-line `let` chains, calls with variable arguments, loops, `if`, tuples of
variables and `None` in tail position. Before pinning a new literal, check
that `impEq e e` evaluates to `true`; a constructor `impEq` lacks makes every
comparison false.

## 2. Pure Lean → Rust

The reifier and the driver are in `CatCrypt/Hax/`, with the driver's inputs in
`bench/reify_roundtrip/`:

| Step | Entry point |
|---|---|
| Lean → `ImpExpr` (A-normal form) | `reifyImp% n f` (`ReifyImp.lean`) |
| the program denotes `f` | `ascend_reified` closes `FnCorres bi e entry G f` |
| to the read-back semantics | `fnCorres_evalImp` (`ReifyImpBridge.lean`) |
| leaf stubs and printed text | `leafStubsText`, the `reify-emit` executable (`ReifyImpDriver.lean`, `ReifyImpEmit.lean`) |
| round trip | `scripts/reify-roundtrip.sh FN DEF OUT` |
| end-to-end theorem | `edwardsAdd_endToEnd`, `decode_endToEnd` |

The fragment is nested `let`, calls of named operations (the function's leading
binders), tuples and projections, `if` over `Bool`/`Int`, and `some`/`none`.
For a new function: reify it, prove `FnCorres` with `ascend_reified`, add it
to the emit list, run the round trip, and state the end-to-end theorem as the
two templates do.

## 3. Existing Rust → Lean: the ascent on `ImpExpr`

1. Extract with haxpipeT: `--emit-certified` for monomorphic code,
   `--emit-classes <trait-export.json>` for code generic over traits (one Lean
   class per trait, instances per `impl`).
2. In a Lean module, `hax_ascend Ns` (`CatCrypt/Hax/Ascent/Coverage.lean`)
   reads the extraction in namespace `Ns`, builds its builtin table
   (`Ns.HaxGen.table`, `Ns.HaxGen.builtins`) and generates, per function `f`,
   a shallow Lean function with the `FnCorres` theorem `Ns.HaxGen.«f».corres`.
   `#hax_coverage Ns` lists the functions the generator does not cover.
3. Prove the generated function equal to your specification.
   `CatCrypt/Crypto/ACME/SurfaceCorresGen.lean` in the development repository is
   a complete example.

For class-generic extractions, a builtins table built from a class instance
(`Builtins.ofClass`, development repository `CatCrypt/Hax/ClassCertified.lean`)
certifies each literal at every instance by `ascend_reified`.

The ascent on machine code, `LowCT` and Jasmin is described in `ASCENT.md`.

## Building

Build from the development repository's root, as `BUILDING.md` requires, e.g.
`lake build CatCrypt.Crypto.Hax.ImpRustHaxRoundTrip`. `cargo hax` needs the hax
frontend (`cargo-hax`) on the path.
