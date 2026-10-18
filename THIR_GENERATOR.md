# The THIR kernel generator

The THIR generator compiles small scalar kernels written in a let-normal arithmetic IR,
`Thir`, to `Com jasminDialect`, and from there to owned x86 assembly or to Jasmin. It is one of
the five producers of the linked kernels that programs compiled by `compileA` call; the others
are the field and lattice templates, LowCT written in Lean, relational compilation, and the
Jasmin `.jinc` importer. [NAVIGATION.md](NAVIGATION.md) lists its modules under the THIR rows.

## What `Thir` is

`Thir` is an IR of this package, not rustc's THIR. It is named after its ancestry: Rust source
reaches it through rustc's THIR as hax exports it. The data flow is

```
rustc THIR ──cargo hax json──▶ hax ExprKind ──hax-lean HaxAdapter──▶ ImpExpr / TExpr
          ──impExprToThir / texprToThir──▶ Thir ──thirToJasmin──▶ Com jasminDialect
```

so its alignment with rustc is the alignment of hax-lean's `ImpExpr` and `TExpr`, the same
input `compileA` reads through `haxToNF`. The IR itself (`ThirToComFront.lean`) has atoms
(literals, local and input variables), twelve right-hand sides (add, mul, the high half of a
product, the bitwise operations, rotate, shifts by an immediate, casts, calls), and three
statements (`ret`, `let_`, `forUp`), at one word width per program. A second, dialect lane
uses `thirDialect` (`VIR/ThirDialect.lean`), a `Com` dialect whose fifteen operations map
almost one to one to `jasminDialect`.

## Stages and theorems

| Stage | Theorem | Statement |
|---|---|---|
| `ImpExpr` → `Thir` | `impExprToThir_denoteScalar` (`ImpExprToThir.lean`) | the scalar reading `ImpExpr.denoteScalar` equals `Thir.denote` |
| `TExpr` → `Thir` | `texprToThir_denoteScalarT` (`TExprToThir.lean`) | the typed reading `TExpr.denoteScalarT` equals `Thir.denote` |
| `Thir` → `Com jasminDialect` | `thirToJasmin_denote` (`ThirToComFront.lean`) | `Thir.denote` equals `Com.denote` |
| composite | `compileFromHax_denote`, `compileFromHax_meets_spec` (`CompileFromHax.lean`); `impToJasmin_denote` (`HaxToThirFront.lean`) | the source reading equals the denotation of the compiled `Com` |
| dialect lane | `lowerThir_denote` (`VIR/ThirDialect.lean`) | `Com thirDialect` and its lowering to `Com jasminDialect` denote the same function |
| ties | the rows of `scripts/compile_from_hax_tie_manifest.tsv` (development repository), e.g. `bigSigma0_emitted_eq_spec` | a compiled `Com` whose denotation equals the FIPS or NIST specification function |

The source readings `denoteScalar` and `denoteScalarT` are defined in this package for the
accepted arithmetic subset.

## Outputs

The X86Backend `*ThirEmit` modules compile the SHA-256 round parts (e′, T1, T2, the message
word), the SHA-512 T1, Ch/Maj and message word, the ChaCha quarter round, the BLAKE2b `G`
function, the SM3 permutation, the LEA round, the LSH mix, an NTT butterfly, BabyBear and FHE
Montgomery multiplication, and the treehash and WOTS chains. They lower `Com jasminDialect`
with `Com.toLprogPhysAbi`, `legalizeShiftImmLprog` and `LprogOptPipeline.renderOwned` to AT&T
assembly, or print Jasmin for jasminc. The bench drivers are under `bench/thir_front_*` in the
development repository; `bench/lea_lsh_compare` links the LEA and LSH kernels. The artifacts
are checked by the C known-answer tests of their benches and listed in
`scripts/chain-manifest.tsv`.

## Trust base

The hax frontend and hax-lean's adapter; the definitions `denoteScalar` and `denoteScalarT`;
the opaque `jasminExtSem` leaves (`thExtCall`, `thEqLit`); for assembly output,
`legalizeShiftImmLprog`, `renderOwned` and the system assembler; for Jasmin output, jasminc.

## Certifying a THIR kernel at the bytes

A THIR kernel reaches the bytes theorem of the compiler through the region back half:
`compileRegion σ a (NFProg.ofCom (lowerThir c))` with `compileRegion_correct` and
`NFProg.denote_ofCom`, the pattern of `producer_bytes_straight` (`Haxc/ProducerBytes.lean` in
the development repository). Rotates and `ANDN` enter that route through their expansion into
shifts and bitwise operations at the `Com` level, since the checked encoder encodes shifts.
