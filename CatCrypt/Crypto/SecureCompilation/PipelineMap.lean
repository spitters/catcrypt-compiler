/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.Hax.HaxToLowCT
public import CatCrypt.Crypto.Hax.HaxToLowCT_ConstFold
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Compiler / IR pipeline map  (START HERE before building front-end work)

The mid-level of the compiler is the upstream-named denoting dialects in
`VIR/` — `MlirArithDialect` (`arith`), `MlirMemrefDialect` (`memref`),
`MlirVectorDialect` (`vector`), `MlirScfDialect` (`scf`), `MlirPolynomialDialect`
— with a verified `Com→Com` lowering chain (`DialectLoweringChain`,
`DialectToJasminCom`) down to `jasminDialect`, and a generic machine layer
(`RegMachineSim` / `GenericRegAllocSim` + the x86 `JInstrRegMachineSim` instance)
below it.  The two **physical IRs coincide** on the covered fragment
(`encodeLprog = encodeJBlock`; GoldenPath kernels emit via the JInstr path).
The crypto-SSA IR for kernels is `catCryptDialect` (`Com catCryptDialect`, aligned
with MLIR, lowered by `cryptoDialectToJasminCom`); kernels do not use the `Lprog`
kernel-emit path.
The `llvm` waist is veir-deferred (no in-tree LLVM dialect by design).  The **frontend ingestion** below is
the two ingestion paths, whose scalar denotations coincide by the DF result (`Dialects/FrontendCoincidence*` —
base, shifts, let-engine, whole-body, RustState bridge).

A discoverability index for the hax→Lean compiler IRs.  The EMIT side is indexed
per primitive in `CAPABILITIES.md`; this is the COMPILER side.  The `#check`s at the
bottom name each referenced entry point, so a rename or removal stops this module
from building.

## There are TWO hax-ingestion pipelines.  Do not conflate them.

```
                         (A) value-correct scalar leaves
  hax ImpExpr ──compileFromHax──▶ Thir ──▶ Com jasminDialect
                  (ANF core; C3 meta-thm + ~64 leaf value proofs)

                         (B) whole-function loops + arrays
  hax ImpExpr ──haxToLowCT──▶ LowCT ──translateDialectFull──▶ Com catCryptDialect
                  (loops, dynamic opaque arrays, while/if)         └▶ LowCTToJasmin
```

* **`compileFromHax`** (`CompileFromHax.lean`): the NARROW ANF core.  Accepts
  `var`/`lit`/`app`/`letBind` + arithmetic atoms + *literal-index* reads of
  input array params (`P[k]`, `k` literal — `ImpExprToThir.indexAtom?`).  It has
  **no loops and no arrays**: loops are meta-unrolled to flat let-chains
  (`hornerUnroll`/`schedUnroll`/`arrRecUnroll`) for *literal* bounds *before*
  reaching it.  This is the path with the C3 meta-theorem
  (`compileFromHax_denote`) and the ~64 compile-from-hax leaf value-agreement
  proofs.  Its denotation (`ImpExpr.denoteScalar`) is PURE SCALAR — no heap.
* **`haxToLowCT`** (`Crypto/Hax/HaxToLowCT.lean`): the capable whole-function
  path.  Targets `LowCT` (which has a memory model via `RustExec`), then
  `translateDialectFull` and `LowCTToJasmin` downstream.  Value
  preservation is in `HaxToLowCTSimulates.lean`.

## Capability matrix  (✓ handled · ✗ none · ~ partial)

| construct                         | compileFromHax | haxToLowCT | downstream (translate) |
|-----------------------------------|:--------------:|:----------:|:----------------------:|
| scalar arith / `let` / call       | ✓              | ✓          | ✓                      |
| literal-index input read `P[k]`   | ✓ (atom)       | —          | —                      |
| `if` (public scrutinee)           | ✗              | ✓ `RIfNz`  | ✓                      |
| `while` (var cond)                | ✗              | ✓ `RWhileNz` | ✓                    |
| `forFold`, LITERAL bound          | ✗ (pre-unroll) | ✓ `RFor`   | ✓ (`loopRFor`)         |
| `forFold`, SYMBOLIC bound         | ✗              | ✓ `RForRuntime` | ✓                    |
| dynamic array read `index[a,i]`   | ✗              | ✓ `RArrLoad`  | ✓ (`memGetDyn`)        |
| dynamic array write `array_update`| ✗              | ✓ `RArrStore` | ✓ (`memSetDyn`)        |
| array-valued `forFold` body       | ✗              | ✗          | —                      |
| nested 2-D `array_update`         | ✗              | ✗          | —                      |

Key `file:line` (against the `haxToLowCT` translator at
`HaxToLowCT.lean:477`; the typed `haxToLowCTEnv` at `:713` repeats the same arms):
* `haxToLowCT`: `array_update→RArrStore` HaxToLowCT.lean:502; `index→RArrLoad`
  :512; `whileLoop→RWhileNz` :577; `forFold (lit n)→RFor` :641/:648;
  `forFold` with a runtime bound `→RForRuntime` :654 (zero-start) / :676
  (offset-start); `forFold` otherwise / `forLoop` → `none` :679/:626.
* `substConsts` + `mlkemConstTable` (K=3,N=256,Q=3329) / `mldsaConstTable`:
  `HaxToLowCT_ConstFold.lean` — turns `forFold _ _ (.var "K")` into the literal
  form the line-641 arm accepts.  This is an optimization, not a
  prerequisite: a bound `impBoundToSExpr` accepts reaches `RForRuntime` unfolded.
* dynamic-array CT discipline: `cmdCT` requires the index `Public`
  (`cmdCT_RArrLoad`/`cmdCT_RArrStore`); soundness `cmdCT_sound`
  (`LowCTCTAnalysis.lean`).  The same `cmdCT` rejects a SECRET index.
* `RArrLoad`/`RArrStore` translate through `translateDialectFull`
  (`Dialects/TranslateDialectDirectArms.lean`) to `memrefGetDyn` / `memrefSetDyn` —
  opaque-value, index-as-arg.

## Decision table — "I want to ingest X, which path?"

* a **scalar leaf** with a value-correctness proof (SHA round, field op) →
  `compileFromHax` (literal loops pre-unrolled).
* a **whole function with loops / dynamic arrays** (ML-KEM/ML-DSA NTT,
  sampling) → `haxToLowCT` (`substConsts` folds a symbolic bound to a literal
  where an unrolled loop is wanted; otherwise it lowers to `RForRuntime`).  NO THIR
  change and NO `compileFromHax` denotation change is required for this.
* **constant-time** of a runtime-indexed array loop → `cmdCT` on a public index
  (`Crypto/SecureCompilation/ArrayLoopCT.lean` has the worked NTT-pattern proof).

## The `LowCT → catCryptDialect` arm (`translateDialectFull`)

The matrix above maps the two hax-ingestion FRONTS. Downstream of `haxToLowCT`, the
`LowCT → catCryptDialect` arm is `translateDialectFull` (`catCryptDialect` is the
crypto-SSA IR, lowered to jasmin via `cryptoDialectToJasminCom`). Its coverage:

| arm construct                       | `translateDialectFull` status |
|-------------------------------------|-------------------------------|
| scalar `SExpr` arithmetic (`RScalarSetExpr`) | ✓ (the scalar-arith arm, § 1b of `TranslateDialectDirectArms`) |
| SIMD ext ops (`gf2p8mulb` / `vpshufb` / `pclmulqdq` / `aesenc`) | ✗ NOT in the high front (SIMD/vectorization concern, not scalar-front) |
| whole-protocol orchestration        | ✗ NOT (multi-session spines stay hand-authored / linked) |

The scalar-arith arm covers the common `haxToLowCT → catCryptDialect` path for scalar
bodies; the SIMD-ext and orchestration rows are outside the arm, which keeps the
hand-authored owned-emit fleet on hand-`Com` (listed in
`scripts/handcom-provenance-baseline.txt`).

## Convention (keep this map true)

Every IR translator's MODULE DOCSTRING must list exactly which source
constructs it **handles** vs returns **`none`** on — so the capability is
discoverable at the source, not just here.  `Crypto/Hax/HaxToLowCT.lean` is the
reference example (its docstring enumerates the handled/`none` constructors).
This matrix is the cross-cutting view; the per-file docstrings are the
authoritative detail.  When you extend a translator, update both its docstring
and the row above.

## Constructs outside `haxToLowCT`
ML-KEM `sample_ntt_poly` fails `haxToLowCT (substConsts mlkemConstTable …)`
on: (1) a `forFold` body that *returns an array* (only statement-form
`let _ = array_update …; body` is handled), and (2) nested 2-D
`array_update(a, i, array_update(index(a,i), j, …))`.  These are narrow
translator-pattern extensions in `HaxToLowCT.lean`, not architecture.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.PipelineMap

open CatCrypt.Crypto.SecureCompilation
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Jasmin.LowCT

-- Rot-guards: if any entry point named above is renamed or removed, this file
-- stops building, forcing the map above to be updated.
#check @CompileFromHax.compileFromHax
#check @ImpExprToThir.impExprToThir
#check @haxToLowCT
#check @substConsts
#check @mlkemConstTable
#check @cmdCT
#check @cmdCT_sound

end CatCrypt.Crypto.SecureCompilation.PipelineMap
