# The Jasmin importer

The importer reads Jasmin source text and lowers it through this compiler's backend to x86-64,
without `jasminc`.

```
Jasmin source text
   │  JincParser   text to JasminCoqSemMirror.Cmd, the straight-line subset
   │  JincToCom    text to the untyped JFun
   │  JincInline   a source unit to JFun, by partial evaluation
   ├▶ JincElab     JFun to Com jasminDialect, with loops unrolled
   └▶ JincToLowCT  JFun to LowCT, with loops kept as RFor and RWhileNz
   ▼  Com.toLprogPhysAbi, renderLprogAtt
x86-64 assembly
```

The modules are in `CatCrypt/Crypto/Jasmin/`.

## The fragment

`JincToCom` reads the straight-line fragment: `reg` and `reg ptr` parameters and locals, width casts
`(Wu)x`, binary `* + -`, compound `+=`, shifts and bitwise operations, indexed load `tbl[idx]`,
constant-indexed store `out[k]=v`, the global-table assignment `name = GLOBAL` as a pointer parameter,
branchless `c ? a : b` as `select`, and `return name`.

`JincInline` reads a whole source unit: `param int` constants, global tables, `inline fn`, `fn` and
`export fn`, `if`/`else`, `for`, `while`, calls, and the intrinsics its module docstring lists. It
partially evaluates one function into a `JFun`. It inlines calls to source functions and refuses a
data-dependent branch, so `if` conditions, loop bounds and `while` guards must fold at compile time.
`importFunRolled` keeps a loop over an affine counter rolled, as a loop over a run-time trip index, and
keeps a `while (v < n)` with a run-time bound `n` as a run-time loop. `JincToLowCT` carries such loops to
the backend as loop nodes.

## Theorems

The partial evaluator has no simulation theorem, so a theorem about an imported function concerns the
`Com` or `LowCT` that the import produces. [CORRECTNESS.md](CORRECTNESS.md) places the importer among the
correctness techniques.

| Module | Role | Theorems |
|---|---|---|
| `JincElab` | `JFun` to `Com jasminDialect` and x86-64 | `ecDlog_elaborates`, `ecPowStore_elaborates` (typing), and their `_denote_concrete` forms (the denotation is the specification) |
| `JincToLowCT` | `JFun` to `LowCT` with loop nodes, and x86-64 | constant time of the rendered `Lprog` |
| `MldsaJincImport` | the ML-DSA Montgomery reduction | `mldsaMontRedWord_toNat`, `mldsaMontRed_montgomery_law` |
| `KeccakJincImport` | formosa-keccak's permutation, its sponges and the AVX2 four-way permutation | known-answer tests; `KeccakJincEmit.keccakF1600_constant_time` |
| `Examples/JincParserDemo` | parser fidelity | `parsedCmdValue = handGf16MulStepCmd` |

## Adding an import

1. Confirm that the function is in the fragment, or extend `JincInline`. Keep the code constant time:
   branchless `select`, no branch on a secret.
2. Add an emit driver, and a behavioural comparison with `jasminc` where a reference exists.
3. Add a row to the table above.
