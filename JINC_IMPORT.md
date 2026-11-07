# The Jasmin importer

The importer reads Jasmin source text and lowers it through this compiler's backend to x86-64,
without `jasminc`.

```
Jasmin source text
   │  JincToCom    text to the untyped JFun
   │  JincInline   a source unit to JFun, by partial evaluation
   ├▶ JincElab     JFun to Com jasminDialect, with loops unrolled
   └▶ JincToLowCT  JFun to LowCT, with loops kept as RFor and RWhileNz
   ▼  Com.toLprogPhysAbi, renderLprogAtt
x86-64 assembly
```

The modules are in `CatCrypt/Crypto/Jasmin/`.

## The fragment

`JincToCom` reads the straight-line fragment: `reg` and `reg ptr` parameters and locals, the
zero-extending cast `(Wu)x` (a sign-extending `(Ws)x` is refused), one binary operator
`* + - & | ^ << >>` per right-hand side, compound `+=`, indexed load `tbl[idx]`, constant-indexed store
`out[k]=v`, the global-table assignment `name = GLOBAL` as a pointer parameter, branchless `c ? a : b`
as `select`, and `return name`.

`JincInline` reads a whole source unit: `param int` constants, global tables, `inline fn`, `fn` and
`export fn`, `if`/`else`, `for`, `while`, calls, and the intrinsics its module docstring lists. It
partially evaluates one function into a `JFun`. It inlines calls to source functions and refuses a
data-dependent branch, so `if` conditions, loop bounds and `while` guards must fold at compile time.
`importFunRolled` keeps a loop over an affine counter rolled, as a loop over a run-time trip index, and
keeps a `while (v < n)` with a run-time bound `n` as a run-time loop. `JincToLowCT` carries such loops to
the backend as loop nodes.

`JincInline` and `JazzToInstrR` (the `.jazz` reader of `JazzPrint`'s round trip) read expressions with
the precedence of Jasmin's grammar (`compiler/src/parser.mly`), loosest first: `?:`; `||`; `&&`;
`== !=`; `< <= > >=` and their signed and unsigned forms; `|`; `^`; `&`; the shifts; `+ -`; `* / %`;
`!` and the casts. Unlike C, `| ^ &` bind tighter than the comparisons, so `a & b == c` is
`(a & b) == c`. A unary `-` has the precedence of the binary `-` and takes the products that follow it,
so `-a / b` is `-(a / b)`. Binary operators associate to the left.

In `JincInline`, `b = a` into a `reg` or `stack` array `b` copies `a`: every cell of a memory array `a`
is read at the assignment, and a `stack` array of the frame receives them by stores. Into a `reg ptr`
or `stack ptr` array, `b = a` makes `b` refer to `a`.

`JincInline` refuses, with an error naming the construct, the forms it does not implement: the
sign-extending casts `(Ns)` and `(Nsi)`, the cast `(sint)`, the signed word-int types `siN`, and the
annotation `64s` on `< <= > >= / % >>`. It keeps three forms whose reading preserves their meaning:
`uiN` is read as `uN` and `(Nui)` as `(Nu)`, since Jasmin makes the overflow of an unsigned word-int a
safety condition and without overflow the two agree; `(uint) e` (and `(int) e` of older Jasmin) is the
unsigned value of the word `e`, an integer at compile time. The checks are in
`Examples/JincGrammarDemo`.

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
| `Examples/JincGrammarDemo` | precedence, array copy and refusals of `JincInline` and `JazzToInstrR` | known-answer checks |

## Adding an import

1. Confirm that the function is in the fragment, or extend `JincInline`. Keep the code constant time:
   branchless `select`, no branch on a secret.
2. Add an emit driver, and a behavioural comparison with `jasminc` where a reference exists.
3. Add a row to the table above.
