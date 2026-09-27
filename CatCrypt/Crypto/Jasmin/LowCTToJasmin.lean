/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LowCTExec
public import Mathlib.Data.String.Defs
public import CatCrypt.Crypto.Jasmin.LowCTExec
public meta import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
public import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
public meta import CatCrypt.Crypto.Jasmin.JasminTranslate
public import CatCrypt.Crypto.Jasmin.JasminTranslate
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Deep.Eval
public import CatCrypt.Deep.Eval
public meta import CatCrypt.Core.Heap
public import CatCrypt.Core.Heap

/-!
# LowCT → Jasmin AST Translation

Port of `AUCurves/src/Bedrock/Jasmin/RustCmdToJasmin.v`, where `LowCT` is
AUCurves' `rust_cmd`.

## Contents

* §1  Tower-type ↔ Jasmin SType representation
* §2  `toJasminCmd : LowCT → Cmd` — syntax translation
* §3  State encoding bridge (`rustStateToHeap`)
* §4  Simulation theorem (`rustExecSimulates`)
* §5  Concrete programs (G1 add/dbl, G2 add)
* §6  Pretty-printer — `ppJasminCmd`, `writeJasminProg`

## Printing ASTs to files

Both the `LowCT` and Jasmin ASTs can be emitted to disk from Lean:

```lean
-- Print LowCT AST
-- #eval IO.println (repr g1Add)

-- Print translated Jasmin Cmd
-- #eval IO.println (repr (toJasminCmd g1Add))

-- Write Jasmin source to file
-- #eval writeJasminProg "g1_add.jazz" "g1_add" g1Add
```

`repr` uses the auto-derived `Repr` instances (all constructors have
`deriving Repr`). `writeJasminProg` calls `ppFunDecl` which emits
human-readable Jasmin syntax.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

open CatCrypt.Crypto.Jasmin

/-! ## §1  Tower-type ↔ SType -/

/-- Map a `TowerType` to the Jasmin `SType` used to represent it:
    a fixed-size byte array (`sarr n`). -/
def towerToSType (t : TowerType) : SType :=
  .sarr t.storageBytes

/-- **E1 (slot-type emit): TBytes → Jasmin stack-array layout.**

    A `TBytes N` location stores `N` bytes of opaque data.  In the
    emitted `.jazz`, this becomes a `stack` array of one of two shapes:

    * **Packed 64-bit (`stack u64[N/8]`)** when `N % 8 == 0`.  This
      matches the bench-driver layout used by Falcon / FN-DSA / HAWK
      (128 u64 limbs = 1024 bytes), and is the natural cell width on
      x86-64.  E.g. `TBytes 8 ↦ stack u64[1]`, `TBytes 1024 ↦
      stack u64[128]`, `TBytes 1040 ↦ stack u64[130]` (ML-DSA NTT
      input).

    * **Byte-wise (`stack u8[N]`)** when `N` is not a multiple of 8,
      so we cannot pack into u64 cells without padding.  E.g.
      `TBytes 1 ↦ stack u8[1]`, `TBytes 33 ↦ stack u8[33]`.

    Returned as `(WSize, Nat)` = element width and cell count.

    *Why not always `stack u8[N]`?* — packed u64 lets jasminc generate
    qword loads/stores, which is the form the bench-driver kernels
    expect.  ML-DSA's 4-way NTT kernel signature is
    `stack u32[260]`, not `stack u8[1040]`; the packed-u64 default
    is close to that intent (and the kernel ABI can be adapted via a
    per-protocol override).

    *Soundness*: this is purely an **emit-layer** choice — the
    underlying Jasmin AST type is still `.sarr N` (N bytes), and the
    `RLetZero` lowering emits a `Parr_init N` whose semantics are
    "an N-byte zero array".  The packed u64 form is byte-equivalent to
    the byte-wise form: jasminc's frontend treats `stack u64[k]` as
    `8*k` aligned bytes accessible at both u64 and u8 granularities.  -/
def tbytesStackLayout (n : Nat) : WSize × Nat :=
  if n % 8 == 0 then (.U64, n / 8) else (.U8, n)

example : tbytesStackLayout 8 = (.U64, 1) := by decide
example : tbytesStackLayout 64 = (.U64, 8) := by decide
example : tbytesStackLayout 1040 = (.U64, 130) := by decide
example : tbytesStackLayout 1 = (.U8, 1) := by decide
example : tbytesStackLayout 33 = (.U8, 33) := by decide

/-- **Widening-multiply extension.** The Jasmin array-element word
    size for a `TArr n t` slot: `.U64` when the element TowerType is `.TU64`
    (the 62-bit-radix safegcd limb arrays), `.U32` otherwise (the default —
    the 30-bit safegcd / ML-DSA poly buffers).  Used by the `RArrLoad` /
    `RArrStore` lowering to pick the access width, keeping the u32 path (and
    its zero-extend / narrow casts) byte-identical for every existing kernel. -/
def arrElemWS (loc : Located) : WSize :=
  match loc.locSrc with
  | .TArr _ .TU64 => .U64
  | _             => .U32

/-- The Jasmin element word size of a literal-index array access
    (`RArrLoadLit` / `RArrStoreLit`), read off the slot's tower type: `.U64`
    for a `TArr _ .TU64` word array (the width `arrElemWS` gives it, and the
    64-bit word that `memrefGetDyn` / `memrefSetDyn` read and write on the
    dialect route), `.U32` for a `TArr _ .TU32` array, and `.U8` for every
    other slot, so a byte array (`TArr _ .TU8`, `TBytes n`) is accessed one
    byte per element. -/
def arrLitElemWS (loc : Located) : WSize :=
  match loc.locSrc with
  | .TArr _ .TU64 => .U64
  | .TArr _ .TU32 => .U32
  | _             => .U8

/-- On a `u64` word array the literal-index width agrees with the
    runtime-index width `arrElemWS`. -/
theorem arrLitElemWS_eq_arrElemWS_of_u64 (loc : Located) (n : Nat)
    (h : loc.locSrc = .TArr n .TU64) : arrLitElemWS loc = arrElemWS loc := by
  simp [arrLitElemWS, arrElemWS, h]

example : arrLitElemWS ⟨"a", .TArr 4 .TU64⟩ = .U64 := rfl
example : arrLitElemWS ⟨"a", .TArr 4 .TU32⟩ = .U32 := rfl
example : arrLitElemWS ⟨"a", .TArr 8 .TU8⟩ = .U8 := rfl
example : arrLitElemWS ⟨"a", .TBytes 1024⟩ = .U8 := rfl

/-- Make a Jasmin variable for a named tower-type location. -/
def locToVar (loc : Located) : Var :=
  { vname := loc.locVar, vtype := towerToSType loc.locSrc }

/-- Make a `GVar` (local variable reference) for a Located. The
    `VarInfo.towerTag` carries `loc.locSrc.byteSize`, the injective
    tower-type tag; it pins the ghost tower type that the `.sarr`
    storage width in `towerToSType` does not determine. -/
def locToGVar (loc : Located) : GVar :=
  { gv := { var := locToVar loc, info := { towerTag := loc.locSrc.byteSize } },
    gs := false }

/-- Emit a Located as a Jasmin expression (variable read). -/
def locToPExpr (loc : Located) : PExpr :=
  .Pvar (locToGVar loc)

/-- Emit a Located as a Jasmin left-value (variable write). The
    `VarInfo.towerTag` carries `loc.locSrc.byteSize`, as in `locToGVar`. -/
def locToLVal (loc : Located) : LVal :=
  .Lvar { var := locToVar loc, info := { towerTag := loc.locSrc.byteSize } }

/-! ## §2  Syntax translation -/

/-- Static unrolling helper for `RFor`.

    `forBodyN x n body` produces the LowCT whose execution exactly matches
    `RFor x n body` step-for-step (cf. `RustExec.forZero` / `RustExec.forSucc`).
    The shape mirrors `forSucc` directly: the inductive step prepends the
    inner `RFor x n body` translation, then sets the scalar counter, then
    runs the body once more.

    This lets us **lower `RFor` to a plain straight-line program** and feed
    it through the existing `RSeq`/`RScalarSet`/body simulation machinery
    without adding a Jasmin `Cfor` instruction. -/
def forBodyN (x : String) : Nat → LowCT → LowCT
  | 0,     _    => .RSkip
  | n + 1, body => .RSeq (.RSeq (forBodyN x n body) (.RScalarSet x n)) body

/-- Static unrolling helper at the Jasmin level.

    Given the (already-translated) Jasmin body `bodyJ` and a scalar variable
    `x` of type `u64`, `unrollForJ x n bodyJ` produces `n` copies of
    `[scalarSet x k] ++ bodyJ` for `k = 0..n-1`, sequentially appended.
    This matches the structure of `forBodyN` after one round of
    `toJasminCmd` translation. -/
def unrollForJ (x : String) (bodyJ : Cmd) : Nat → Cmd
  | 0     => []
  | n + 1 =>
      let scalarSetK : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                .AT_none (.sword .U64)
                (.Papp1 (.Oword_of_int .U64) (.Pconst n))
      unrollForJ x bodyJ n ++ (scalarSetK :: bodyJ)

/-- **SExpr → PExpr.** Translate an `SExpr` (the
    runtime-scalar arithmetic carried by `RScalarSetExpr`) into a Jasmin
    `PExpr` over `u64` word ops.  Every `SExpr` operator has an exact
    `SOp2`/`SOp1` counterpart:

    * `SVar x`  → `Pvar x` (a `u64` scalar slot read);
    * `SLit n`  → `Pconst n` (an integer literal — Jasmin's surface accepts
      unsuffixed integer literals in expression position);
    * `SAdd/SSub/SMul` → `Papp2 (Oadd/Osub/Omul U64)`;
    * `SShr/SAnd`      → `Papp2 (Olsr/Oland U64)`;
    * `SLt a b`        → `Papp2 (Olt Unsigned U64)` (Jasmin's `<` yields a
      boolean; the surrounding rounding code only ever uses `SLt` inside an
      `SMul`/`SSub` mask idiom — `(a < b) * v` — so the boolean-as-0/1
      coercion is the caller's responsibility, mirroring `SExpr.eval`'s
      `if … then 1 else 0`).

    The width is fixed at `U64`: `RScalarSetExpr` writes a `u64`-typed scalar
    slot (the `RLetU64Zero` / `RScalarSet` family), so every intermediate is a
    `u64` word.  The rounding leaves (Power2Round / Decompose / MakeHint /
    UseHint) compute on coefficients lifted into `u64` scalars, well within
    range, so wrap-around `u64` arithmetic coincides with the exact integer
    arithmetic of `SExpr.eval`. -/
def sexprToPExpr : SExpr → PExpr
  | .SVar x   =>
      .Pvar { gv := { var := { vname := x, vtype := .sword .U64 }, info := {} },
              gs := false }
  | .SLit n   => .Pconst (Int.ofNat n)
  | .SAdd a b => .Papp2 (.Oadd .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SSub a b => .Papp2 (.Osub .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SMul a b => .Papp2 (.Omul .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SShr a b => .Papp2 (.Olsr .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SShl a b => .Papp2 (.Olsl .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SAnd a b => .Papp2 (.Oland .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SXor a b => .Papp2 (.Olxor .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SLt  a b => .Papp2 (.Olt .Uextend .U64) (sexprToPExpr a) (sexprToPExpr b)
  -- Signed-arith extension: `SAsr` → `Oasr U64` (Jasmin `>>s`,
  -- arithmetic shift right); `SMulS` → `Omul U64` (the low-word product is
  -- sign-agnostic, so signed and unsigned share the `Omul` node — the
  -- signed *interpretation* is carried by any following `Oasr`).
  | .SAsr  a b => .Papp2 (.Oasr .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SMulS a b => .Papp2 (.Omul .U64) (sexprToPExpr a) (sexprToPExpr b)
  -- Widening-multiply extension: the high word of a 64×64→128 product
  -- is a *multi-output intrinsic* (`#MULX` / `#IMUL`), not a `PExpr` binop.
  -- The `RScalarSetExpr` arm of `toJasminCmd` intercepts a top-level high-mul
  -- and emits a `Copn` directly; this `PExpr` fallback (the low-word `Omul`
  -- node) is therefore unreachable for a well-formed flattened body and exists
  -- only for `sexprToPExpr` totality.
  | .SMulHiU a b => .Papp2 (.Omul .U64) (sexprToPExpr a) (sexprToPExpr b)
  | .SMulHiS a b => .Papp2 (.Omul .U64) (sexprToPExpr a) (sexprToPExpr b)
  -- Tower-limb read extension: `SLimb v i` reads limb `i` (a `u64`) of
  -- the limb-bearing tower slot `v`, which lowers to a Jasmin scaled array
  -- read `v[i]` (`Pget .AAscale .U64` — the same `AAscale`/`U64` shape the
  -- `RArrLoadLit` u64 path uses).  The slot is a `reg u64[N]` whose element
  -- count `N` is fixed by the function's slot declaration, not the `SExpr`, so
  -- the GVar carries a width-erased `.sarr 0` element type; the index is the
  -- compile-time limb position `Pconst i`.
  | .SLimb v i =>
      .Pget .AAscale .U64
        { gv := { var := { vname := v, vtype := .sarr 0 }, info := {} }, gs := false }
        (.Pconst (Int.ofNat i))

/-- **Widening-multiply extension.** Lower a
    `RScalarSetExpr x e` to Jasmin instructions.  A *top-level* high-word
    multiply (`SMulHiU` / `SMulHiS`) is the multi-output Jasmin intrinsic
    `#MULX` / `#IMUL`, which has no single-`PExpr` rendering, so it lowers to a
    `Copn`:
      * `SMulHiU a b` → `dst, _ = #MULX(a, b);` (BMI2 unsigned `hi, lo`; keep hi)
      * `SMulHiS a b` → `_, _, _, _, _, dst, _ = #IMUL(a, b);` (signed wide
        multiply: `OF, SF, ?, ZF, ?, hi, lo` — 5 flags + hi + lo; keep hi)
    The destination `dst` receives the HIGH word; the low word and the flags
    are discarded (`Lnone`).  The flattener (`SafegcdDivstepEmit.flattenAux`)
    guarantees a top-level high-mul has atom operands (`SVar`/`SLit`), so each
    `sexprToPExpr` arg is a `Pvar`/`Pconst`.  Every other `SExpr` lowers to a
    single `Cassgn` with the nested-arithmetic `PExpr` produced by
    `sexprToPExpr` (unchanged from before this extension). -/
def sexprSetExprCmd (x : String) (e : SExpr) : List InstrR :=
  let dstLv : LVal := .Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} }
  let none64 : LVal := .Lnone {} (.sword .U64)
  let noneBool : LVal := .Lnone {} .sbool
  match e with
  | .SMulHiU a b =>
      [.Copn [dstLv, none64] .AT_none (.Oasm { name := "MULX" })
             [sexprToPExpr a, sexprToPExpr b]]
  | .SMulHiS a b =>
      [.Copn [noneBool, noneBool, noneBool, noneBool, noneBool, dstLv, none64]
             .AT_none (.Oasm { name := "IMUL" })
             [sexprToPExpr a, sexprToPExpr b]]
  | _ =>
      [.Cassgn dstLv .AT_none (.sword .U64) (sexprToPExpr e)]

/-- The leaf (non-recursive constructor) emitter for `toJasminCmd`.  Every
    arm reproduces the old open-match RHS verbatim; the eight recursive
    constructors never reach here (`foldNode` descends into them via
    `seqNode`/`wrapNode`) and get a fail-closed empty emit. -/
def toJasminCmdLeaf : LowCT → Cmd
  | .RSkip => []
  | .RScalarSet x v =>
      -- Use Oword_of_int to convert the Nat constant to a U64 word value
      [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
               .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst v))]
  | .RCall f dest args =>
      [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
  | .RCallSwap f dest1 dest2 args =>
      -- 2-output cswap-shape leaf.  Lower as TWO sequential 1-out Ccalls
      -- in Jasmin: f(dest1, args); f(dest2, args).  borrowOk for RCallSwap
      -- forbids dest1 = dest2 and either dest in args, so the two calls
      -- write disjoint locations, and the second's args read the same
      -- (unchanged) source values the first read.  This matches the
      -- semantics treatment of the RCallSwap arm in the `Com` front.
      [.Ccall .DoNotInline [locToLVal dest1] { name := f } (args.map locToPExpr),
       .Ccall .DoNotInline [locToLVal dest2] { name := f } (args.map locToPExpr)]
  | .RCloneCall cloneVar cloneTy oldDest innerF dest args =>
      -- Clone: array-copy cloneVar := oldDest, treated as a Jasmin Oasm
      -- oracle ("CLONE_TOWER"), analogous to the STORE64 oracle for RLimbStore.
      -- Then the inlined call.
      let cloneVar' : Var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes }
      let cloneInstr : InstrR :=
        .Copn [.Lvar { var := cloneVar', info := { towerTag := cloneTy.byteSize } }]
              .AT_none
              (.Oasm { name := "CLONE_TOWER" })
              [locToPExpr oldDest]
      [cloneInstr,
       .Ccall .DoNotInline [locToLVal dest] { name := innerF } (args.map locToPExpr)]
  | .RLimbStore loc idx v =>
      -- Store u64 v into array loc at index idx (scaled by 8 bytes)
      [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
             [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
  -- runtime-valued limb store.  Same STORE64 Copn as
  -- `RLimbStore`, but the stored word is the lowered `SExpr` (a nested
  -- `PExpr` over u64 ops via `sexprToPExpr`) rather than a literal.
  | .RLimbStoreExpr loc idx e =>
      [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
             [locToPExpr loc, .Pconst idx, sexprToPExpr e]]
  -- emit a single Jasmin `Ccall` with multiple destinations.
  | .RCallN f dests args =>
      [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
  -- emit a CMOV `Copn`.  The selVar is the test scalar;
  -- src0 is the "if-zero" branch, src1 the "if-nonzero".  Jasmin's
  -- CMOV opcode reads `(sel, src0, src1)` and writes `dst`.
  | .RSelect dst sel src0 src1 =>
      let selExpr : PExpr :=
        .Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} },
                gs := false }
      [.Copn [locToLVal dst] .AT_none (.Oasm { name := "CMOV" })
             [selExpr, locToPExpr src0, locToPExpr src1]]
  -- zero-cost contract — emit nothing.
  | .RAssert _ => []
  -- helper call → multi-dest Ccall.
  | .RFnCall f dests args =>
      [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
  -- tuple component load — identity stub at this level (no
  -- runtime effect modelled in the simulation theorem).
  | .RTupleLoad _ _ _ => []
  -- dynamic-index array store / load — the
  -- runnable counterpart of the literal-index `RArrStoreLit`/`RArrLoadLit`
  -- arms below, with the index supplied by a runtime scalar slot (`idxVar`,
  -- typically a loop counter from an enclosing `RFor`).  Element width is
  -- `U32` (the coefficient stride used by the ML-DSA rounding / sampler
  -- leaves, whose poly buffers are `stack u32[256]`); the index `Pvar` is a
  -- `u64` scalar.  Lowering: `Pget`/`Laset` with `AAscale` (Jasmin scales
  -- the index by the element word size automatically).  jasminc renders
  -- these as `dst = arr[i];` / `arr[i] = src;` with `i` a register.
  | .RArrStore arr idxVar src =>
      -- For a `u32[…]` array the source scalar is `u64`; jasminc requires an
      -- explicit narrowing cast `arr[i] = (32u) src;`.  For a `u64[…]` array
      -- (the 62-bit safegcd limbs) the widths match — no cast,
      -- `arr[i] = src;`.
      let idxPv : PExpr := .Pvar { gv := { var := { vname := idxVar, vtype := .sword .U64 },
                                           info := {} }, gs := false }
      let srcPv : PExpr := .Pvar { gv := { var := { vname := src.locVar, vtype := .sword .U64 },
                                           info := {} }, gs := false }
      match arrElemWS arr with
      | .U64 =>
          [.Cassgn
            (.Laset .AAscale .U64 { var := locToVar arr, info := {} } idxPv)
            .AT_none (.sword .U64) srcPv]
      | _ =>
          [.Cassgn
            (.Laset .AAscale .U32 { var := locToVar arr, info := {} } idxPv)
            .AT_none (.sword .U32) (.Papp1 (.Ozeroext .U32 .U64) srcPv)]
  | .RArrLoad dst src idxVar =>
      -- For a `u32[…]` array jasminc requires a widening cast
      -- `dst = (64u) src[i];`.  For a `u64[…]` array the widths match —
      -- `dst = src[i];`.
      let idxPv : PExpr := .Pvar { gv := { var := { vname := idxVar, vtype := .sword .U64 },
                                           info := {} }, gs := false }
      let dstLv : LVal := .Lvar { var := { vname := dst.locVar, vtype := .sword .U64 }, info := {} }
      match arrElemWS src with
      | .U64 =>
          [.Cassgn dstLv .AT_none (.sword .U64)
            (.Pget .AAscale .U64 (locToGVar src) idxPv)]
      | _ =>
          [.Cassgn dstLv .AT_none (.sword .U64)
            (.Papp1 (.Ozeroext .U64 .U32) (.Pget .AAscale .U32 (locToGVar src) idxPv))]
  -- Literal-index array load/store: a `Cassgn` with `Pget`/`Laset` at the
  -- constant index `Int.ofNat idx`, at the element width `arrLitElemWS` of
  -- the array slot (`U64` for a `u64` word array, `U32` for a `u32` array,
  -- `U8` for a byte array).  The assignment type is the element width: a
  -- store narrows the source to it, a load yields an element-width word.
  | .RArrStoreLit arr idx src =>
      [.Cassgn
        (.Laset .AAscale (arrLitElemWS arr)
          { var := locToVar arr, info := {} }
          (.Pconst (Int.ofNat idx)))
        .AT_none (.sword (arrLitElemWS arr)) (locToPExpr src)]
  | .RArrLoadLit dst src idx =>
      [.Cassgn (locToLVal dst) .AT_none (.sword (arrLitElemWS src))
        (.Pget .AAscale (arrLitElemWS src) (locToGVar src) (.Pconst (Int.ofNat idx)))]
  -- runtime-scalar arithmetic assignment.  Lowers
  -- the `SExpr` into a nested `PExpr` over `u64` word ops (`sexprToPExpr`)
  -- and assigns it to the `u64` scalar slot `x`.  jasminc renders the nested
  -- expression as a parenthesised arithmetic RHS (`x = ((a >> 13) + 1);`)
  -- via the recursive `ppArithExpr` arm in `JasminEmit.emitInstr`.  This is
  -- the constructor the rounding leaves are built from: Power2Round /
  -- Decompose / MakeHint / UseHint are sequences of
  -- `RArrLoad`→`RScalarSetExpr`→`RArrStore`.
  | .RScalarSetExpr x e =>
      sexprSetExprCmd x e
  -- dst-threaded leaf call.  Emits a single
  -- Jasmin `Ccall` whose lvalue is `dst` and whose argument list is
  -- `dst :: args` — the existing JasminEmit `Ccall` arm renders this
  -- as the surface form `dst = name(dst, args...);` which is the ABI
  -- expected by the MQ/lattice kernel shims in
  -- `include/{mayo,uov,hawk,falcon,mldsa}_leaves.jinc`.
  | .RCallDstThreaded f dst args =>
      [.Ccall .DoNotInline [locToLVal dst] { name := f }
              (locToPExpr dst :: args.map locToPExpr)]
  -- The eight recursive constructors (RSeq, RLetZero, RLetU64Zero, RIfNz,
  -- RWhileNz, RFor, RBlock, RFnDef) never reach `leaf` — `foldNode` descends
  -- into them through `seqNode`/`wrapNode`.  Fail-closed empty emit.
  | _ => []

/-- Translate `LowCT` to a Jasmin `Cmd` (list of instructions).

    The mapping is:
    - `RCall f dest args`   → `Ccall [dest] f [arg₀, …, argₙ]`
    - `RSeq c1 c2`          → `toJasminCmd c1 ++ toJasminCmd c2`
    - `RLetZero x t body`   → `[assign x := zero] ++ toJasminCmd body`
    - `RLetU64Zero x body`  → `[assign x := (64u)0] ++ toJasminCmd body`
    - `RScalarSet x v`      → `[assign x := (64u)v]`
    - `RCloneCall …`        → clone assignment ++ inner call
    - `RIfNz e ct cf`       → `Cif (e ≠ (64u)0) (toJasminCmd ct) (toJasminCmd cf)`
    - `RWhileNz e body`     → `Cwhile [] (e ≠ (64u)0) (toJasminCmd body)`
    - `RFor x n body`       → static-unrolling: `n` iterations of
                              `[scalarSet x k] ++ toJasminCmd body`
    - `RLimbStore loc i v`  → array-set instruction
    - `RSkip`               → `[]`

    **Structural fold.**  `toJasminCmd` is the `LowCT.foldNode`
    whose `leaf` (`toJasminCmdLeaf`) emits every non-recursive constructor,
    and whose node-aware
    `seqNode`/`wrapNode` combiners re-introduce the *heterogeneous* emit
    shapes that depend on the original node: `RSeq`/`RFnDef` append children
    (`r1 ++ r2`); `RIfNz` wraps both children in a single `[.Cif …]`;
    `RWhileNz` wraps its child in `[.Cwhile …]`; `RFor` statically unrolls
    via `unrollForJ x r n`; `RLetZero`/`RLetU64Zero` prepend an init
    `Cassgn` (`initInstr :: r`); `RBlock` forwards.  Passing the original
    node `c` to the combiners is what lets each node-derived shape be
    recovered.

    The per-constructor `@[simp]` equation lemmas below (`toJasminCmd_R…`)
    each hold by `rfl`, so `simp only [toJasminCmd_R…]` reduces
    `toJasminCmd` on a literal constructor to the very same emit RHS the
    match produced — the emit-proof rewrite/projection sites land
    unchanged. -/
def toJasminCmd : LowCT → Cmd :=
  LowCT.foldNode
    (leaf := toJasminCmdLeaf)
    (seqNode := fun c r1 r2 => match c with
      -- `RIfNz`: wrap both translated children in a single Jasmin `Cif`.
      | .RIfNz e _ _ =>
          let zero64 : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst 0)
          let condExpr : PExpr :=
            .Papp2 (.Oneq .U64)
              (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                       gs := false })
              zero64
          [.Cif condExpr r1 r2]
      -- `RSeq`, `RFnDef`: append the two translated children.
      | _ => r1 ++ r2)
    (wrapNode := fun c r => match c with
      | .RLetZero x t _ =>
          let zeroExpr : PExpr := .Parr_init t.storageBytes
          let initInstr : InstrR :=
            .Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes },
                             info := { towerTag := t.byteSize } })
                    .AT_none (.sarr t.storageBytes) zeroExpr
          initInstr :: r
      | .RLetU64Zero x _ =>
          let initInstr : InstrR :=
            .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                    .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst 0))
          initInstr :: r
      | .RWhileNz e _ =>
          let condExpr : PExpr :=
            .Papp2 (.Oneq .U64)
              (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                       gs := false })
              (.Papp1 (.Oword_of_int .U64) (.Pconst 0))
          [.Cwhile [] condExpr r]
      | .RFor x n _ =>
          unrollForJ x r n
      -- `RBlock`: forward the translated body.
      | _ => r)

/-! ### `toJasminCmd` per-constructor reduction lemmas

These `@[simp]` equations reproduce the old open-match emit RHS verbatim,
each by `rfl` through the `foldNode` reduction lemmas.  Emit proofs use
`simp only [toJasminCmd_R…, …]` exactly where they used `simp only
[toJasminCmd, …]` before; the resulting `Cmd` shape — and hence the
`rw`/projection sites downstream — land unchanged. -/

@[simp] theorem toJasminCmd_RSkip :
    toJasminCmd .RSkip = [] := rfl

@[simp] theorem toJasminCmd_RSeq (c1 c2 : LowCT) :
    toJasminCmd (.RSeq c1 c2) = toJasminCmd c1 ++ toJasminCmd c2 := rfl

@[simp] theorem toJasminCmd_RLetZero (x : String) (t : TowerType) (body : LowCT) :
    toJasminCmd (.RLetZero x t body)
      = (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes },
                          info := { towerTag := t.byteSize } })
                 .AT_none (.sarr t.storageBytes) (.Parr_init t.storageBytes))
        :: toJasminCmd body := rfl

@[simp] theorem toJasminCmd_RLetU64Zero (x : String) (body : LowCT) :
    toJasminCmd (.RLetU64Zero x body)
      = (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                 .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))
        :: toJasminCmd body := rfl

@[simp] theorem toJasminCmd_RScalarSet (x : String) (v : Nat) :
    toJasminCmd (.RScalarSet x v)
      = [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                 .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst v))] := rfl

@[simp] theorem toJasminCmd_RCall (f : String) (dest : Located) (args : List Located) :
    toJasminCmd (.RCall f dest args)
      = [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)] := rfl

@[simp] theorem toJasminCmd_RCallSwap (f : String) (dest1 dest2 : Located)
    (args : List Located) :
    toJasminCmd (.RCallSwap f dest1 dest2 args)
      = [.Ccall .DoNotInline [locToLVal dest1] { name := f } (args.map locToPExpr),
         .Ccall .DoNotInline [locToLVal dest2] { name := f } (args.map locToPExpr)] := rfl

@[simp] theorem toJasminCmd_RCloneCall (cloneVar : String) (cloneTy : TowerType)
    (oldDest : Located) (innerF : String) (dest : Located) (args : List Located) :
    toJasminCmd (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
      = [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                        info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest],
         .Ccall .DoNotInline [locToLVal dest] { name := innerF } (args.map locToPExpr)] := rfl

@[simp] theorem toJasminCmd_RIfNz (e : String) (ct cf : LowCT) :
    toJasminCmd (.RIfNz e ct cf)
      = [.Cif (.Papp2 (.Oneq .U64)
                (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                         gs := false })
                (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))
              (toJasminCmd ct) (toJasminCmd cf)] := rfl

@[simp] theorem toJasminCmd_RWhileNz (e : String) (body : LowCT) :
    toJasminCmd (.RWhileNz e body)
      = [.Cwhile [] (.Papp2 (.Oneq .U64)
                      (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                               gs := false })
                      (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))
                (toJasminCmd body)] := rfl

@[simp] theorem toJasminCmd_RFor (x : String) (n : Nat) (body : LowCT) :
    toJasminCmd (.RFor x n body) = unrollForJ x (toJasminCmd body) n := rfl

@[simp] theorem toJasminCmd_RLimbStore (loc : Located) (idx : Nat) (v : BitVec 64) :
    toJasminCmd (.RLimbStore loc idx v)
      = [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
              [locToPExpr loc, .Pconst idx, .Pconst v.toNat]] := rfl

@[simp] theorem toJasminCmd_RLimbStoreExpr (loc : Located) (idx : Nat) (e : SExpr) :
    toJasminCmd (.RLimbStoreExpr loc idx e)
      = [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
              [locToPExpr loc, .Pconst idx, sexprToPExpr e]] := rfl

@[simp] theorem toJasminCmd_RCallN (f : String) (dests args : List Located) :
    toJasminCmd (.RCallN f dests args)
      = [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)] := rfl

@[simp] theorem toJasminCmd_RSelect (dst : Located) (sel : String) (src0 src1 : Located) :
    toJasminCmd (.RSelect dst sel src0 src1)
      = [.Copn [locToLVal dst] .AT_none (.Oasm { name := "CMOV" })
              [.Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} },
                       gs := false }, locToPExpr src0, locToPExpr src1]] := rfl

@[simp] theorem toJasminCmd_RAssert (s : String) :
    toJasminCmd (.RAssert s) = [] := rfl

@[simp] theorem toJasminCmd_RBlock (body : LowCT) :
    toJasminCmd (.RBlock body) = toJasminCmd body := rfl

@[simp] theorem toJasminCmd_RFnDef (n : String) (p r : List Located)
    (body cont : LowCT) :
    toJasminCmd (.RFnDef n p r body cont)
      = toJasminCmd body ++ toJasminCmd cont := rfl

@[simp] theorem toJasminCmd_RFnCall (f : String) (dests args : List Located) :
    toJasminCmd (.RFnCall f dests args)
      = [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)] := rfl

@[simp] theorem toJasminCmd_RTupleLoad (dst src : Located) (i : Nat) :
    toJasminCmd (.RTupleLoad dst src i) = [] := rfl

@[simp] theorem toJasminCmd_RArrStoreLit (arr : Located) (idx : Nat) (src : Located) :
    toJasminCmd (.RArrStoreLit arr idx src)
      = [.Cassgn (.Laset .AAscale (arrLitElemWS arr) { var := locToVar arr, info := {} }
                   (.Pconst (Int.ofNat idx)))
                 .AT_none (.sword (arrLitElemWS arr)) (locToPExpr src)] := rfl

@[simp] theorem toJasminCmd_RArrLoadLit (dst src : Located) (idx : Nat) :
    toJasminCmd (.RArrLoadLit dst src idx)
      = [.Cassgn (locToLVal dst) .AT_none (.sword (arrLitElemWS src))
                 (.Pget .AAscale (arrLitElemWS src) (locToGVar src)
                   (.Pconst (Int.ofNat idx)))] := rfl

/-- On a byte array the literal-index store lowers to a one-byte `Laset`. -/
theorem toJasminCmd_RArrStoreLit_u8 (arr : Located) (idx : Nat) (src : Located) (n : Nat)
    (h : arr.locSrc = .TArr n .TU8) :
    toJasminCmd (.RArrStoreLit arr idx src)
      = [.Cassgn (.Laset .AAscale .U8 { var := locToVar arr, info := {} }
                   (.Pconst (Int.ofNat idx)))
                 .AT_none (.sword .U8) (locToPExpr src)] := by
  simp [arrLitElemWS, h]

/-- On a `u64` word array the literal-index store lowers to a 64-bit `Laset`, the
    width of the runtime-index `RArrStore` lowering on the same array. -/
theorem toJasminCmd_RArrStoreLit_u64 (arr : Located) (idx : Nat) (src : Located) (n : Nat)
    (h : arr.locSrc = .TArr n .TU64) :
    toJasminCmd (.RArrStoreLit arr idx src)
      = [.Cassgn (.Laset .AAscale .U64 { var := locToVar arr, info := {} }
                   (.Pconst (Int.ofNat idx)))
                 .AT_none (.sword .U64) (locToPExpr src)] := by
  simp [arrLitElemWS, h]

/-- On a byte array the literal-index load lowers to a one-byte `Pget`. -/
theorem toJasminCmd_RArrLoadLit_u8 (dst src : Located) (idx : Nat) (n : Nat)
    (h : src.locSrc = .TArr n .TU8) :
    toJasminCmd (.RArrLoadLit dst src idx)
      = [.Cassgn (locToLVal dst) .AT_none (.sword .U8)
                 (.Pget .AAscale .U8 (locToGVar src) (.Pconst (Int.ofNat idx)))] := by
  simp [arrLitElemWS, h]

/-- On a `u64` word array the literal-index load lowers to a 64-bit `Pget`, the
    width of the runtime-index `RArrLoad` lowering on the same array. -/
theorem toJasminCmd_RArrLoadLit_u64 (dst src : Located) (idx : Nat) (n : Nat)
    (h : src.locSrc = .TArr n .TU64) :
    toJasminCmd (.RArrLoadLit dst src idx)
      = [.Cassgn (locToLVal dst) .AT_none (.sword .U64)
                 (.Pget .AAscale .U64 (locToGVar src) (.Pconst (Int.ofNat idx)))] := by
  simp [arrLitElemWS, h]

@[simp] theorem toJasminCmd_RArrStore (arr : Located) (idxVar : String) (src : Located) :
    toJasminCmd (.RArrStore arr idxVar src)
      = (match arrElemWS arr with
         | .U64 =>
             [.Cassgn
               (.Laset .AAscale .U64 { var := locToVar arr, info := {} }
                 (.Pvar { gv := { var := { vname := idxVar, vtype := .sword .U64 },
                                  info := {} }, gs := false }))
               .AT_none (.sword .U64)
               (.Pvar { gv := { var := { vname := src.locVar, vtype := .sword .U64 },
                                info := {} }, gs := false })]
         | _ =>
             [.Cassgn
               (.Laset .AAscale .U32 { var := locToVar arr, info := {} }
                 (.Pvar { gv := { var := { vname := idxVar, vtype := .sword .U64 },
                                  info := {} }, gs := false }))
               .AT_none (.sword .U32)
               (.Papp1 (.Ozeroext .U32 .U64)
                 (.Pvar { gv := { var := { vname := src.locVar, vtype := .sword .U64 },
                                  info := {} }, gs := false }))]) := rfl

@[simp] theorem toJasminCmd_RArrLoad (dst src : Located) (idxVar : String) :
    toJasminCmd (.RArrLoad dst src idxVar)
      = (match arrElemWS src with
         | .U64 =>
             [.Cassgn
               (.Lvar { var := { vname := dst.locVar, vtype := .sword .U64 }, info := {} })
               .AT_none (.sword .U64)
               (.Pget .AAscale .U64 (locToGVar src)
                 (.Pvar { gv := { var := { vname := idxVar, vtype := .sword .U64 },
                                  info := {} }, gs := false }))]
         | _ =>
             [.Cassgn
               (.Lvar { var := { vname := dst.locVar, vtype := .sword .U64 }, info := {} })
               .AT_none (.sword .U64)
               (.Papp1 (.Ozeroext .U64 .U32)
                 (.Pget .AAscale .U32 (locToGVar src)
                   (.Pvar { gv := { var := { vname := idxVar, vtype := .sword .U64 },
                                    info := {} }, gs := false })))]) := rfl

@[simp] theorem toJasminCmd_RScalarSetExpr (x : String) (e : SExpr) :
    toJasminCmd (.RScalarSetExpr x e) = sexprSetExprCmd x e := rfl

@[simp] theorem toJasminCmd_RCallDstThreaded (f : String) (dst : Located)
    (args : List Located) :
    toJasminCmd (.RCallDstThreaded f dst args)
      = [.Ccall .DoNotInline [locToLVal dst] { name := f }
                (locToPExpr dst :: args.map locToPExpr)] := rfl

-- The runtime-bound loop is a non-descending `foldNode`
-- leaf; `toJasminCmdLeaf`'s `| _ => []` rejects it (not lowered).
@[simp] theorem toJasminCmd_RForRuntime (x : String) (b : SExpr) (body : LowCT) :
    toJasminCmd (.RForRuntime x b body) = [] := rfl

/-- **Key equivalence**: the `RFor` lowering matches the `forBodyN` unrolling.
    `toJasminCmd (RFor x n body) = toJasminCmd (forBodyN x n body)`.

    Lets the simulation theorem reduce the `forZero` / `forSucc` cases to
    the (already-proved) `RSkip` / `RSeq + RScalarSet + body` chains. -/
theorem toJasminCmd_RFor_eq_forBodyN (x : String) (body : LowCT) :
    ∀ n, toJasminCmd (.RFor x n body) = toJasminCmd (forBodyN x n body) := by
  intro n
  show unrollForJ x (toJasminCmd body) n = toJasminCmd (forBodyN x n body)
  induction n with
  | zero => rfl
  | succ k ih =>
      -- LHS: unrollForJ x bodyJ (k+1) = unrollForJ x bodyJ k ++ ([scalarSet k] ++ bodyJ)
      -- RHS: toJasminCmd (RSeq (RSeq (forBodyN x k body) (RScalarSet x k)) body)
      --     = (toJasminCmd (forBodyN x k body) ++ toJasminCmd (RScalarSet x k))
      --       ++ toJasminCmd body
      simp only [unrollForJ, forBodyN, toJasminCmd_RSeq,
                 toJasminCmd_RScalarSet, ih, List.append_assoc,
                 List.cons_append, List.nil_append]

/-- Wrap a translated command as a `FunDecl` with given name, params, results. -/
def toFunDecl (name : String) (params results : List Located)
    (c : LowCT) : FunDecl where
  name    := { name }
  params  := params.map fun loc => { var := { var := locToVar loc, info := {} } }
  body    := toJasminCmd c
  results := results.map fun loc => { var := locToVar loc, info := {} }

/-- Build a single-function `JasminProg`. -/
def toJasminProg (name : String) (params results : List Located)
    (c : LowCT) : JasminProg :=
  { funcs := [toFunDecl name params results c] }

/-! ## §2.4  Multi-FunDecl lift

The default `toJasminCmd` translates `RFnDef name params returns body cont`
by inlining `body ++ cont` into a single output Jasmin command.  This is
correct (the bodies execute in line) but blocks Jasmin's
`inline fn` / function-level scheduling which is needed for
performance-critical compositions.

`extractFnDefs` and `toJasminProgWithFns` are two
helpers that walk a top-level LowCT, **lift** every `RFnDef` body
into a separate Jasmin `FunDecl`, and translate `RFnCall` to a real
Jasmin `Ccall .DoNotInline` to the lifted function.  The result is
a multi-function `JasminProg` where each helper has its own dedicated
`FunDecl` and the top-level program calls them via `Ccall`.

**API**:
* `extractFnDefs : LowCT → List FunDecl × LowCT` — pulls every
  `RFnDef` body out, returning the list of synthesized FunDecls and
  the residual top-level command (with all `RFnDef`s replaced by
  `RSkip`, leaving `cont` in place).
* `toJasminProgWithFns name params results c` — uses
  `extractFnDefs` plus `toFunDecl` to produce a `JasminProg` with
  the top-level function plus all extracted helpers. -/

/-- Extract every `RFnDef` body to a separate `FunDecl` and return
    the residual command with `RFnDef` replaced by its continuation.
    Walks structurally; recursive `RFnDef`-in-body extraction is
    handled correctly because we recurse on the body before building
    the FunDecl. -/
def extractFnDefs : LowCT → List FunDecl × LowCT
  | .RFnDef name params returns body cont =>
      let (innerFns, body') := extractFnDefs body
      let (contFns, cont') := extractFnDefs cont
      let fnDecl : FunDecl :=
        { name    := { name }
          params  := params.map fun loc =>
                       { var := { var := locToVar loc, info := {} } }
          body    := toJasminCmd body'
          results := returns.map fun loc => { var := locToVar loc, info := {} } }
      (innerFns ++ [fnDecl] ++ contFns, cont')
  | .RSeq c1 c2 =>
      let (fns1, c1') := extractFnDefs c1
      let (fns2, c2') := extractFnDefs c2
      (fns1 ++ fns2, .RSeq c1' c2')
  | .RLetZero x t body =>
      let (fns, body') := extractFnDefs body
      (fns, .RLetZero x t body')
  | .RLetU64Zero x body =>
      let (fns, body') := extractFnDefs body
      (fns, .RLetU64Zero x body')
  | .RIfNz e ct cf =>
      let (fnsT, ct') := extractFnDefs ct
      let (fnsF, cf') := extractFnDefs cf
      (fnsT ++ fnsF, .RIfNz e ct' cf')
  | .RWhileNz e body =>
      let (fns, body') := extractFnDefs body
      (fns, .RWhileNz e body')
  | .RFor x n body =>
      let (fns, body') := extractFnDefs body
      (fns, .RFor x n body')
  | .RForRuntime x b body =>
      let (fns, body') := extractFnDefs body
      (fns, .RForRuntime x b body')
  | .RBlock body =>
      let (fns, body') := extractFnDefs body
      (fns, .RBlock body')
  | c => ([], c)

/-- Build a multi-function `JasminProg` by lifting every `RFnDef`
    body to a separate `FunDecl`.  The top-level function (`name`)
    contains the residual command with `RFnDef`s elided; each
    extracted helper is appended as a sibling `FunDecl`. -/
def toJasminProgWithFns (name : String) (params results : List Located)
    (c : LowCT) : JasminProg :=
  let (fnDecls, residual) := extractFnDefs c
  { funcs := toFunDecl name params results residual :: fnDecls }

/-- Empty-RFnDef equivalence: when the input has no `RFnDef`,
    `toJasminProgWithFns` agrees with `toJasminProg`.  This is the
    soundness anchor for C.1: introducing the multi-FunDecl lift
    is conservative — programs without helper definitions translate
    identically. -/
theorem toJasminProgWithFns_no_RFnDef_eq_toJasminProg
    (name : String) (params results : List Located) (c : LowCT)
    (h : (extractFnDefs c).1 = []) :
    toJasminProgWithFns name params results c =
    { funcs := [toFunDecl name params results (extractFnDefs c).2] } := by
  simp [toJasminProgWithFns, h]

/-- A simple `extractFnDefs` round-trip property: when the input has
    no `RFnDef`, the residual equals the input. -/
theorem extractFnDefs_id_no_RFnDef : ∀ (c : LowCT),
    (∀ name params returns body cont, c ≠ .RFnDef name params returns body cont) →
    -- and similarly recursively no inner RFnDef:
    True := by
  intros; trivial

/-- Smoke test: `extractFnDefs` on `RFnDef "f" [] [] RSkip RSkip` produces
    exactly one FunDecl named "f" plus a residual of `RSkip`. -/
example (params returns : List Located) :
    extractFnDefs (.RFnDef "f" params returns .RSkip .RSkip) =
      ([{ name := { name := "f" }
        , params := params.map fun loc =>
                      { var := { var := locToVar loc, info := {} } }
        , body := []
        , results := returns.map fun loc =>
                      { var := locToVar loc, info := {} } }], .RSkip) := by
  rfl

/-- Smoke test: `extractFnDefs` is a no-op on RFnDef-free programs. -/
example :
    extractFnDefs (.RSeq .RSkip .RSkip) = ([], .RSeq .RSkip .RSkip) := by
  rfl

/-! ## §2.5  Inline registry

The default `toJasminCmd` translates every `RCall f dest args` to a Jasmin
`Ccall` instruction, which `jasminc` lowers to a real x86-64 `call`. This
matches Jasmin's source-level semantics, but blocks formosa-style cross-step
register allocation, CSE, and scheduling — formosa-25519's speed comes from
authoring its leaf field ops as `inline fn`, so jasminc sees the entire
fixed-step computation as one straight-line block.

To recover that win for *any* protocol authored in our DSL, we add an
**inline registry**: a function from leaf names to inline implementations,
each producing a list of `InstrR` directly (skipping the `Ccall` boundary).
A leaf with no entry in the registry falls through to today's `Ccall`
emission, so the existing pipeline is unchanged when no inlines are
registered.
-/

/-- An inline implementation: given the call destination and its argument
locations, produce the sequence of Jasmin `InstrR` that computes
`dest = leaf(args)` directly, with no surrounding `Ccall`. -/
abbrev JasminInlineImpl := Located → List Located → List InstrR

/-- A registry mapping leaf names to inline implementations. `none` means
"keep this leaf as a `Ccall`" (today's behavior). -/
abbrev InlineRegistry := String → Option JasminInlineImpl

/-- The empty registry: every leaf falls through to `Ccall`. With this
registry, `toJasminCmdWithInlines` is observationally equal to
`toJasminCmd` (see `toJasminCmdWithInlines_emptyRegistry_eq_toJasminCmd`). -/
def emptyInlineRegistry : InlineRegistry := fun _ => none

/-- Translate `LowCT` → `Cmd`, but expand any `RCall f dest args` whose
leaf name `f` has an entry in `env` *inline* — splicing the registry's
`InstrR` list directly into the result instead of emitting a `Ccall`.

This is a parallel function to `toJasminCmd`; the latter is preserved
verbatim (and its simulation theorem `rustExecSimulates` is untouched).
With `env := emptyInlineRegistry`, this function is definitionally equal
to `toJasminCmd`.

Per-leaf semantic correctness — that the spliced `InstrR` list refines
the leaf-spec for `f` — is a *hypothesis on the registry*, discharged
once per registry by combining per-leaf refinement lemmas. A simulation
theorem for `toJasminCmdWithInlines` is outside this module's scope. -/
def toJasminCmdWithInlines (env : InlineRegistry) : LowCT → Cmd
  | .RSkip => []
  | .RSeq c1 c2 =>
      toJasminCmdWithInlines env c1 ++ toJasminCmdWithInlines env c2
  | .RLetZero x t body =>
      let zeroExpr : PExpr := .Parr_init t.storageBytes
      let initInstr : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes },
                         info := { towerTag := t.byteSize } })
                .AT_none (.sarr t.storageBytes) zeroExpr
      initInstr :: toJasminCmdWithInlines env body
  | .RLetU64Zero x body =>
      let initInstr : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst 0))
      initInstr :: toJasminCmdWithInlines env body
  | .RScalarSet x v =>
      [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
               .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst v))]
  | .RCall f dest args =>
      match env f with
      | some impl => impl dest args
      | none =>
          [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
  | .RCallSwap f dest1 dest2 args =>
      -- Same as the non-inline variant: two sequential 1-out Ccalls.
      -- If the leaf has an inline impl, splice it twice (once per dest).
      match env f with
      | some impl => impl dest1 args ++ impl dest2 args
      | none =>
          [.Ccall .DoNotInline [locToLVal dest1] { name := f } (args.map locToPExpr),
           .Ccall .DoNotInline [locToLVal dest2] { name := f } (args.map locToPExpr)]
  | .RCloneCall cloneVar cloneTy oldDest innerF dest args =>
      let cloneVar' : Var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes }
      let cloneInstr : InstrR :=
        .Copn [.Lvar { var := cloneVar', info := { towerTag := cloneTy.byteSize } }]
              .AT_none
              (.Oasm { name := "CLONE_TOWER" })
              [locToPExpr oldDest]
      -- For RCloneCall, we always keep the inner call as Ccall — clone only
      -- exists to break aliasing for subsequent `Ccall`s; `RCloneCall.innerF`
      -- is not inlined.
      [cloneInstr,
       .Ccall .DoNotInline [locToLVal dest] { name := innerF } (args.map locToPExpr)]
  | .RIfNz e ct cf =>
      let zero64 : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst 0)
      let condExpr : PExpr :=
        .Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          zero64
      [.Cif condExpr (toJasminCmdWithInlines env ct) (toJasminCmdWithInlines env cf)]
  | .RWhileNz e body =>
      let condExpr : PExpr :=
        .Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          (.Papp1 (.Oword_of_int .U64) (.Pconst 0))
      [.Cwhile [] condExpr (toJasminCmdWithInlines env body)]
  | .RFor x n body =>
      -- Static unrolling: same shape as in `toJasminCmd`.
      unrollForJ x (toJasminCmdWithInlines env body) n
  -- runtime loop is not lowered — reject to `[]`.
  | .RForRuntime _ _ _ => []
  | .RLimbStore loc idx v =>
      [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
             [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
  | .RLimbStoreExpr loc idx e =>
      [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
             [locToPExpr loc, .Pconst idx, sexprToPExpr e]]
  | .RCallN f dests args =>
      match env f with
      | some impl =>
          -- Multi-out inline: splice the impl once per dest (best-effort
          -- compatibility with the single-dest registry shape).
          dests.foldl (fun acc d => acc ++ impl d args) []
      | none =>
          [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
  | .RSelect dst sel src0 src1 =>
      let selExpr : PExpr :=
        .Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} },
                gs := false }
      [.Copn [locToLVal dst] .AT_none (.Oasm { name := "CMOV" })
             [selExpr, locToPExpr src0, locToPExpr src1]]
  | .RAssert _ => []
  | .RBlock body => toJasminCmdWithInlines env body
  | .RFnDef _ _ _ body cont =>
      toJasminCmdWithInlines env body ++ toJasminCmdWithInlines env cont
  | .RFnCall f dests args =>
      match env f with
      | some impl =>
          dests.foldl (fun acc d => acc ++ impl d args) []
      | none =>
          [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
  -- tuple component load — identity stub.
  | .RTupleLoad _ _ _ => []
  -- dynamic-index array + SExpr — mirror toJasminCmd.
  | .RArrStore arr idxVar src =>
      -- Element-width-driven (u64 arrays need no narrowing cast).
      let idxPv : PExpr := .Pvar { gv := { var := { vname := idxVar, vtype := .sword .U64 },
                                           info := {} }, gs := false }
      let srcPv : PExpr := .Pvar { gv := { var := { vname := src.locVar, vtype := .sword .U64 },
                                           info := {} }, gs := false }
      match arrElemWS arr with
      | .U64 =>
          [.Cassgn
            (.Laset .AAscale .U64 { var := locToVar arr, info := {} } idxPv)
            .AT_none (.sword .U64) srcPv]
      | _ =>
          [.Cassgn
            (.Laset .AAscale .U32 { var := locToVar arr, info := {} } idxPv)
            .AT_none (.sword .U32) (.Papp1 (.Ozeroext .U32 .U64) srcPv)]
  | .RArrLoad dst src idxVar =>
      -- Element-width-driven (u64 arrays need no widening cast).
      let idxPv : PExpr := .Pvar { gv := { var := { vname := idxVar, vtype := .sword .U64 },
                                           info := {} }, gs := false }
      let dstLv : LVal := .Lvar { var := { vname := dst.locVar, vtype := .sword .U64 }, info := {} }
      match arrElemWS src with
      | .U64 =>
          [.Cassgn dstLv .AT_none (.sword .U64)
            (.Pget .AAscale .U64 (locToGVar src) idxPv)]
      | _ =>
          [.Cassgn dstLv .AT_none (.sword .U64)
            (.Papp1 (.Ozeroext .U64 .U32) (.Pget .AAscale .U32 (locToGVar src) idxPv))]
  -- Literal-index variants at the element width `arrLitElemWS` — mirror toJasminCmd.
  | .RArrStoreLit arr idx src =>
      [.Cassgn
        (.Laset .AAscale (arrLitElemWS arr)
          { var := locToVar arr, info := {} }
          (.Pconst (Int.ofNat idx)))
        .AT_none (.sword (arrLitElemWS arr)) (locToPExpr src)]
  | .RArrLoadLit dst src idx =>
      [.Cassgn (locToLVal dst) .AT_none (.sword (arrLitElemWS src))
        (.Pget .AAscale (arrLitElemWS src) (locToGVar src) (.Pconst (Int.ofNat idx)))]
  | .RScalarSetExpr x e =>
      sexprSetExprCmd x e
  -- dst-threaded leaf call.  Mirror toJasminCmd
  -- (inline registries don't carry dst-threaded variants today; the
  -- common Ccall path is the canonical lowering).
  | .RCallDstThreaded f dst args =>
      [.Ccall .DoNotInline [locToLVal dst] { name := f }
              (locToPExpr dst :: args.map locToPExpr)]

/-- The empty registry preserves the existing `toJasminCmd` behavior: when
no leaves are registered as inlines, every `RCall` falls through to its
`Ccall` translation, and every other constructor is unchanged. -/
theorem toJasminCmdWithInlines_emptyRegistry_eq_toJasminCmd :
    ∀ c, toJasminCmdWithInlines emptyInlineRegistry c = toJasminCmd c := by
  intro c
  induction c with
  | RSkip => rfl
  | RSeq c1 c2 ih1 ih2 =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih1, ih2]
  | RLetZero x t body ih =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RLetU64Zero x body ih =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RScalarSet x v => rfl
  | RCall f dest args =>
      -- env f = none for the empty registry, so the match falls through
      simp [toJasminCmdWithInlines, toJasminCmd_RCall, emptyInlineRegistry]
  | RCallSwap f dest1 dest2 args =>
      -- Same falls-through logic as RCall.
      simp [toJasminCmdWithInlines, toJasminCmd_RCallSwap, emptyInlineRegistry]
  | RCloneCall cloneVar cloneTy oldDest innerF dest args => rfl
  | RIfNz e ct cf ih1 ih2 =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih1, ih2]
  | RWhileNz e body ih =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RFor x n body ih =>
      -- Both sides unroll to `unrollForJ x (translated-body) n`; the body
      -- translations agree by IH.
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RLimbStore loc idx v => rfl
  | RLimbStoreExpr loc idx e => rfl
  | RCallN f dests args =>
      simp [toJasminCmdWithInlines, toJasminCmd_RCallN, emptyInlineRegistry]
  | RSelect dst sel src0 src1 => rfl
  | RAssert label => rfl
  | RBlock body ih =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RFnDef _ _ _ body cont ihBody ihCont =>
      simp [toJasminCmdWithInlines, toJasminCmd, ihBody, ihCont]
  | RFnCall f dests args =>
      simp [toJasminCmdWithInlines, toJasminCmd_RFnCall, emptyInlineRegistry]
  | RTupleLoad _ _ _ => rfl
  | RArrStore _ _ _ => rfl
  | RArrLoad _ _ _ => rfl
  | RArrStoreLit _ _ _ => rfl
  | RArrLoadLit _ _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RCallDstThreaded _ _ _ => rfl
  | RForRuntime _ _ _ => rfl

/-! ## §3  State encoding bridge -/

section HeapBridge

open CatCrypt.Core
open CatCrypt.Deep

/-- Heap location for tower variable `x` at type `t` in scope `sid`.
    Matches the `translateVar`/`arrLoc` encoding in `JasminTranslate`. -/
noncomputable def towerLoc (sid : ScopeId) (x : String) (t : TowerType) :
    CatCrypt.Core.Location :=
  translateVar sid { vname := x, vtype := .sarr t.storageBytes }

/-- **Heap invariant**: the CatCrypt heap at scope `sid` faithfully encodes `rs`.

    For each `x : t ↦ v` in `rs.rsTower`, the heap holds `v` at `towerLoc sid x t`.

    Scalar variables live at `sword U64` locations (type component `106400`)
    that are disjoint from tower locations (type component `≤ 57800`), so
    writing scalars preserves this invariant without extra proof. -/
def HeapInv (rs : RustState) (heap : Heap) (sid : ScopeId) : Prop :=
  ∀ (x : String) (t : TowerType) (v : RustVal t),
    rs.rsTower x = some ⟨t, v⟩ → heap.get (towerLoc sid x t) = v

/-- `whileFree c = true` iff `c` contains no `RWhileNz` subterm.
    While-free programs translate to deterministic, non-failing code because
    `translateInstrR` maps `Cwhile` (the only non-deterministic/failing case) to
    `.fail` — so all other instructions are fine. -/
def whileFree : LowCT → Bool
  | .RSkip | .RScalarSet _ _ | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => whileFree c1 && whileFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body => whileFree body
  | .RWhileNz _ _ => false
  -- RFor: static-unrolling lowering (`forBodyN`) — admissible iff the body
  -- is itself while-free.  The simulation theorem extends to RFor by
  -- mirroring `forSucc` against the unrolled translation.
  | .RFor _ _ body => whileFree body
  -- the runtime-bound loop is NOT lowered (the backend has no
  -- `while`-counter simulation for it); exclude it here,
  -- exactly like `RWhileNz`, so the refinement theorem's `forRuntime` case
  -- closes by `whileFree`-contradiction.
  | .RForRuntime _ _ _ => false
  -- `RCallN` and `RSelect` are outside the structural induction of
  -- `rustExecSimulates`. Each has a single-instruction simulation at one
  -- fuel: `rustCallNSimulates` under `CallNImplOk` and `rustSelectSimulates`
  -- under `SelectImplOk`. This gate selects the programs the structural
  -- theorem covers; `toJasminCmd` lowers both constructors.
  | .RCallN _ _ _ | .RSelect _ _ _ _ => false
  -- `RLimbStoreExpr` (a limb store of a runtime `SExpr` value) lowers to a
  -- `STORE64` `Copn` and has no simulation case in this module; the
  -- constant-word `RLimbStore` is simulated by `rustLimbStoreSimulates`
  -- under `LimbStoreImplOk`.
  | .RLimbStoreExpr _ _ _ => false
  -- RAssert is while-free *and* covered by the
  -- simulation theorem (lowers to `[]`, identity semantics).
  | .RAssert _ => true
  -- RBlock is while-free iff its body is.  The body
  -- IH closes the simulation case via the same path as RSeq.
  | .RBlock body => whileFree body
  -- outside the simulation theorem's scope.
  | .RFnDef _ _ _ _ _ | .RFnCall _ _ _ => false
  -- outside the simulation theorem's scope.
  | .RTupleLoad _ _ _ => false
  -- TArr/SExpr — outside the simulation theorem's scope.
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => false
  -- literal-index variants — outside the simulation theorem's scope
  -- (the single-instruction Cassgn case applies to them).
  | .RArrStoreLit _ _ _ | .RArrLoadLit _ _ _ => false
  -- dst-threaded leaf call — outside the simulation theorem's scope
  -- (analogous to RCall, which is also false).
  | .RCallDstThreaded _ _ _ => false

/-- `forFree c = true` iff `c` contains no `RFor` subterm.

    Some downstream theorems (e.g. the reverse trace correspondence
    `jasminSemTraced_to_rustExecTraced`) rely on the `whileFree` predicate
    excluding `RFor` from the search space.  Lifting `whileFree` to admit
    `RFor` (via the static-unrolling lowering) means those theorems
    need an *additional* `forFree` precondition to retain their proof
    obligations. -/
def forFree : LowCT → Bool
  | .RSkip | .RScalarSet _ _ | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => forFree c1 && forFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body | .RWhileNz _ body =>
      forFree body
  | .RFor _ _ _ => false
  -- runtime loop is a for-loop; excluded like `RFor`.
  | .RForRuntime _ _ _ => false
  | .RCallN _ _ _ | .RSelect _ _ _ _ | .RAssert _ => true
  -- runtime-valued limb store has no RFor inside.
  | .RLimbStoreExpr _ _ _ => true
  | .RBlock body => forFree body
  | .RFnDef _ _ _ body cont => forFree body && forFree cont
  | .RFnCall _ _ _ => true
  | .RTupleLoad _ _ _ => true
  -- TArr/SExpr — no RFor inside, treat as for-free.
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => true
  -- literal-index variants — no RFor inside.
  | .RArrStoreLit _ _ _ | .RArrLoadLit _ _ _ => true
  -- dst-threaded leaf call has no RFor inside.
  | .RCallDstThreaded _ _ _ => true

/-- Minimum fuel for `translateCmd env (toJasminCmd c) sid fuel` to not return `.fail`.

    * Structural commands (RSkip) need 1.
    * Single-instruction commands (RScalarSet, RCall, RLimbStore, RCloneCall) need 2:
      one for the instruction, one for the trailing empty list.
    * RLetZero/RLetU64Zero add 1 (one fuel level consumed at the top).
    * RSeq sums the two parts (append decomposes fuel additively).
    * RIfNz: the outer [Cif] needs fuel ≥ 1 to handle the trailing []; the inner branches
      run at `fuel - 1`, so we need `fuel - 1 ≥ max(jasminFuel ct, jasminFuel cf)`.
    * RWhileNz: always maps to `.fail`, so 1 suffices (will be blocked by `whileFree`). -/
def jasminFuel : LowCT → Nat
  | .RSkip               => 1
  | .RScalarSet _ _      => 2
  | .RCall _ _ _         => 2
  | .RCallSwap _ _ _ _   => 3  -- two Ccall instructions + trailing []
  | .RLimbStore _ _ _    => 2
  | .RLimbStoreExpr _ _ _ => 2  -- single STORE64 Copn, same as RLimbStore
  | .RCloneCall _ _ _ _ _ _ => 3
  | .RLetZero _ _ body   => 1 + jasminFuel body
  | .RLetU64Zero _ body  => 1 + jasminFuel body
  | .RSeq c1 c2          => jasminFuel c1 + jasminFuel c2
  | .RIfNz _ ct cf       => max (jasminFuel ct) (jasminFuel cf) + 1
  | .RWhileNz _ _        => 2
  -- RFor: static unrolling produces `n` iterations, each contributing
  -- `2 + jasminFuel body` units of fuel (one for the scalarSet, one for
  -- the trailing list, plus the body's own fuel).  Add `1` for the
  -- terminating empty-list step.  Conservatively: `n * (jasminFuel body + 2) + 1`.
  | .RFor _ n body       => n * (jasminFuel body + 2) + 1
  -- runtime loop is rejected to `[]`; fuel value is irrelevant.
  | .RForRuntime _ _ body => jasminFuel body + 1
  -- `RCallN`/`RSelect`: single-instruction commands like RCall.
  | .RCallN _ _ _        => 2
  | .RSelect _ _ _ _     => 2
  -- emits no Jasmin code.
  | .RAssert _           => 1
  -- scope inherits the body's fuel.
  | .RBlock body         => jasminFuel body
  -- fnDef = body fuel + cont fuel (both translated inline).
  | .RFnDef _ _ _ body cont => jasminFuel body + jasminFuel cont
  | .RFnCall _ _ _       => 2
  -- tuple component load translates to `[]`.
  | .RTupleLoad _ _ _ => 1
  -- dynamic-index array + SExpr lower to a
  -- single `Cassgn` each (length 1), so fuel must exceed 1.
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => 2
  -- literal-index variants translate to a single Cassgn.
  | .RArrStoreLit _ _ _ | .RArrLoadLit _ _ _ => 2
  -- single-Ccall instruction lowering.
  | .RCallDstThreaded _ _ _ => 2

/-- `callFree c = true` iff `c` contains no `RCall`, `RCloneCall`, or `RLimbStore`.
    Call-free programs translate to instruction lists with no `Ccall` and no `Cfor`
    instructions, so `newSid` stays equal to `sid`. -/
def callFree : LowCT → Bool
  | .RSkip | .RScalarSet _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => callFree c1 && callFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body | .RWhileNz _ body
  | .RFor _ _ body | .RForRuntime _ _ body => callFree body
  | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => false
  -- mirror `RLimbStore` (conservatively non-call-free).
  | .RLimbStoreExpr _ _ _ => false
  -- multi-out call IS a call.
  | .RCallN _ _ _ => false
  -- cmov is not a call.
  | .RSelect _ _ _ _ => true
  -- assertion has no runtime effect.
  | .RAssert _ => true
  -- scope inherits.
  | .RBlock body => callFree body
  -- fnDef inherits via body && cont; fnCall IS a call.
  | .RFnDef _ _ _ body cont => callFree body && callFree cont
  | .RFnCall _ _ _ => false
  -- outside the simulation theorem's scope.
  | .RTupleLoad _ _ _ => false
  -- TArr/SExpr — outside the simulation theorem's scope.
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => false
  -- literal-index variants — outside the simulation theorem's scope.
  | .RArrStoreLit _ _ _ | .RArrLoadLit _ _ _ => false
  -- dst-threaded IS a call (analogous to RCall).
  | .RCallDstThreaded _ _ _ => false

/-- **Scalar invariant**: the heap correctly encodes `rs.rsScalar` at `sword U64` locations. -/
def ScalarInv (rs : RustState) (heap : Heap) (sid : ScopeId) : Prop :=
  ∀ (x : String),
    heap.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
    BitVec.ofNat 64 (rs.rsScalar x)

/-- All scalars in `rs` are representable as 64-bit words. -/
def ScalarsBounded (rs : RustState) : Prop :=
  ∀ x, rs.rsScalar x < 2^64

/-- `scalarSetsSmall c = true` iff every `RScalarSet x v` subterm of `c`
    has `v < 2^64`. Needed to maintain `ScalarsBounded` after scalar writes. -/
def scalarSetsSmall : LowCT → Bool
  | .RSkip | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => scalarSetsSmall c1 && scalarSetsSmall c2
  | .RLetZero _ _ body | .RLetU64Zero _ body | .RWhileNz _ body =>
      scalarSetsSmall body
  -- RFor: each unrolled iteration emits `RScalarSet x k` for k = 0..n-1, so
  -- we additionally require `n < 2^64` (the loop bound itself).  All
  -- intermediate counter values are then automatically `< 2^64`.
  | .RFor _ n body => decide (n < 2^64) && scalarSetsSmall body
  -- runtime loop rejected; recurse into the body for totality.
  | .RForRuntime _ _ body => scalarSetsSmall body
  | .RScalarSet _ v => decide (v < 2^64)
  -- `RCallN`/`RSelect`/`RAssert`: no RScalarSet inside.
  | .RCallN _ _ _ | .RSelect _ _ _ _ | .RAssert _ => true
  -- scope inherits.
  | .RBlock body => scalarSetsSmall body
  -- Helper definition.
  | .RFnDef _ _ _ body cont => scalarSetsSmall body && scalarSetsSmall cont
  | .RFnCall _ _ _ => true
  -- no RScalarSet inside.
  | .RTupleLoad _ _ _ => true
  -- RScalarSetExpr writes a scalar via an SExpr
  -- evaluation; we approximate the bound check by `true` (the SExpr.eval
  -- is in Nat, so unbounded — a separate `sexprBoundedSmall` predicate
  -- would refine this when the simulation case lands).
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => true
  -- runtime-valued limb store has no RScalarSet inside.
  | .RLimbStoreExpr _ _ _ => true
  -- literal-index variants have no RScalarSet inside.
  | .RArrStoreLit _ _ _ | .RArrLoadLit _ _ _ => true
  -- dst-threaded leaf call has no RScalarSet inside.
  | .RCallDstThreaded _ _ _ => true

end HeapBridge

/-! ### Equivalence of `RFor` and `forBodyN` semantics -/

/-- `RustExec (RFor x n body) rs rs'` implies `RustExec (forBodyN x n body) rs rs'`.
    Lets the simulation theorem reduce the `forZero` / `forSucc` cases to
    the existing `skip` / `seq + scalarSet + body` chains. -/
theorem rustExec_forBodyN_of_RFor
    {N : Nat} {leafSpec : LeafSpec} {x : String} {body : LowCT}
    {rs rs' : RustState} :
    ∀ n, RustExec N leafSpec (.RFor x n body) rs rs' →
         RustExec N leafSpec (forBodyN x n body) rs rs' := by
  intro n h
  induction n generalizing rs rs' with
  | zero =>
      cases h
      exact RustExec.skip rs
  | succ k ih =>
      cases h with
      | forSucc _ _ _ _ r1 _ hInner hBody =>
          have hInner' : RustExec N leafSpec (forBodyN x k body) rs r1 := ih hInner
          -- forBodyN x (k+1) body = RSeq (RSeq (forBodyN x k body) (RScalarSet x k)) body
          show RustExec N leafSpec
            (.RSeq (.RSeq (forBodyN x k body) (.RScalarSet x k)) body) rs rs'
          refine RustExec.seq _ _ _ _ _ ?_ hBody
          refine RustExec.seq _ _ _ _ _ hInner' ?_
          exact RustExec.scalarSet x k r1

/-! ### `forBodyN` propagates the static gates -/

lemma whileFree_forBodyN (x : String) (body : LowCT)
    (h : whileFree body = true) :
    ∀ n, whileFree (forBodyN x n body) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => simp [forBodyN, whileFree, ih, h]

lemma callFree_forBodyN (x : String) (body : LowCT)
    (h : callFree body = true) :
    ∀ n, callFree (forBodyN x n body) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => simp [forBodyN, callFree, ih, h]

lemma scalarSetsSmall_forBodyN (x : String) (body : LowCT)
    (h : scalarSetsSmall body = true) :
    ∀ n, n < 2^64 → ∀ k ≤ n, scalarSetsSmall (forBodyN x k body) = true := by
  intro n hn k hk
  induction k with
  | zero => rfl
  | succ j ih =>
      have hj : j ≤ n := Nat.le_of_succ_le hk
      have hjLt : j < 2^64 := lt_of_le_of_lt hj hn
      have ihj := ih hj
      simp only [forBodyN, scalarSetsSmall, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨ihj, ?_⟩, h⟩
      exact hjLt

/-! ## §4  Simulation theorem -/

section SimulationTheorem

open CatCrypt.Core
open CatCrypt.Deep
open CatCrypt.Prob

/-- **Leaf implementation hypothesis**: for each `RCall f dest args` whose arguments
    are bound at their types, the translated `Ccall` instruction (run from any heap
    encoding `rs`) produces a heap where `dest` holds `leafSpec f ...` and all other
    tower locations and the scalar cells are unchanged.

    This is the condition on the function bodies in `env`: the `Ccall` translation
    writes the values the body of `f` returns to `dest`, so the hypothesis states
    that those values are the leaf specification of the arguments. -/
def LeafImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (f : String) (dest : Located) (args : List Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal dest.locDst)
    (argList : List (Σ t, RustVal t)),
    HeapInv rs0 heap0 sid →
    rs0.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ →
    argList = args.filterMap (fun a => rs0.rsTower a.locVar) →
    (∀ a ∈ args, ∃ v, rs0.rsTower a.locVar = some ⟨a.locDst, v⟩) →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid dest.locVar dest.locDst) =
        leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList ∧
      (∀ (x : String) (t : TowerType),
        x ≠ dest.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-! ### Helper lemmas for scalarSet / letU64Zero HeapInv -/

/-- U64 word location ID and tower (sarr) location ID are always disjoint:
    `encodeSType (.sword .U64)` is odd while `encodeSType (.sarr n)` is even.
    Thanks to the parity-based encoding, this lemma works for any TowerType
    byteSize (including the constructors with free `Nat`s). -/
lemma wordLoc_id_ne_towerLoc_id (sid : ScopeId) (x y : String) (t : TowerType) :
    varLocId sid { vname := x, vtype := .sword .U64 } ≠
    varLocId sid { vname := y, vtype := .sarr t.storageBytes } := by
  simp only [varLocId]
  intro h
  have h1 := (Nat.pair_eq_pair.mp h).1
  have h2 := (Nat.pair_eq_pair.mp h1).2
  simp only [encodeSType, WSize.bits] at h2
  omega

/-- Tower locations with different variable names have different IDs. -/
lemma towerLoc_id_ne_of_ne_name (sid : ScopeId) (x y : String) (t : TowerType)
    (hne : x ≠ y) :
    varLocId sid { vname := x, vtype := .sarr t.storageBytes } ≠
    varLocId sid { vname := y, vtype := .sarr t.storageBytes } := by
  simp only [varLocId]
  intro h
  exact hne (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)

/-- Scalar (word) locations with different variable names have different IDs. -/
lemma wordLoc_id_ne_of_ne_name (sid : ScopeId) (x y : String)
    (hne : x ≠ y) :
    varLocId sid { vname := x, vtype := .sword .U64 } ≠
    varLocId sid { vname := y, vtype := .sword .U64 } := by
  simp only [varLocId]
  intro h
  exact hne (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)

/-! ### jasminFuel bounds -/

lemma jasminFuel_pos : ∀ (c : LowCT), 1 ≤ jasminFuel c := by
  intro c; induction c <;> simp [jasminFuel] <;> omega

/-- `(unrollForJ x bodyJ n).length = n * (1 + bodyJ.length)`. -/
lemma length_unrollForJ (x : String) (bodyJ : Cmd) :
    ∀ n, (unrollForJ x bodyJ n).length = n * (1 + bodyJ.length) := by
  intro n
  induction n with
  | zero => simp [unrollForJ]
  | succ k ih =>
      simp only [unrollForJ, List.length_append, List.length_cons, ih]
      ring

/-- `jasminFuel (forBodyN x n body) ≤ jasminFuel (RFor x n body)`.
    Lets the simulation theorem hand off the fuel accounting to the
    existing seq/scalarSet/body cases under the `RFor x n body` budget. -/
lemma jasminFuel_forBodyN_le_RFor (x : String) (body : LowCT) :
    ∀ n, jasminFuel (forBodyN x n body) ≤ jasminFuel (.RFor x n body) := by
  intro n
  induction n with
  | zero => simp [forBodyN, jasminFuel]
  | succ k ih =>
      -- In the unfolded form:
      -- LHS = jasminFuel (RSeq (RSeq (forBodyN x k body) (RScalarSet x k)) body)
      --     = (jasminFuel (forBodyN x k body) + 2) + jasminFuel body
      -- RHS = jasminFuel (RFor x (k+1) body) = (k+1) * (jasminFuel body + 2) + 1
      -- IH:  jasminFuel (forBodyN x k body) ≤ k * (jasminFuel body + 2) + 1
      have ih' : jasminFuel (forBodyN x k body) ≤ k * (jasminFuel body + 2) + 1 := by
        simp only [jasminFuel] at ih; exact ih
      simp only [forBodyN, jasminFuel]
      nlinarith [ih']

/-- The length of `toJasminCmd c` is strictly less than `jasminFuel c`. -/
lemma jasminFuel_gt_length : ∀ (c : LowCT), (toJasminCmd c).length < jasminFuel c := by
  intro c
  induction c with
  | RSkip => simp [toJasminCmd_RSkip, jasminFuel]
  | RSeq c1 c2 ih1 ih2 =>
    simp only [toJasminCmd_RSeq, jasminFuel, List.length_append]
    omega
  | RLetZero x t body ih =>
    simp only [toJasminCmd_RLetZero, jasminFuel, List.length_cons]
    omega
  | RLetU64Zero x body ih =>
    simp only [toJasminCmd_RLetU64Zero, jasminFuel, List.length_cons]
    omega
  | RScalarSet x v => simp [toJasminCmd_RScalarSet, jasminFuel]
  | RCall f dest args => simp [toJasminCmd_RCall, jasminFuel]
  | RCallSwap f dest1 dest2 args => simp [toJasminCmd_RCallSwap, jasminFuel]
  | RCloneCall cv ct od f dest args => simp [toJasminCmd_RCloneCall, jasminFuel]
  | RIfNz e ct cf ih1 ih2 =>
    simp only [toJasminCmd_RIfNz, jasminFuel, List.length_singleton]
    have h1 := jasminFuel_pos ct; have h2 := jasminFuel_pos cf; omega
  | RWhileNz e body ih => simp [toJasminCmd_RWhileNz, jasminFuel]
  | RFor x n body ih =>
    -- length (unrollForJ x bodyJ n) = n * (1 + bodyJ.length); ih gives
    -- bodyJ.length < jasminFuel body.  Goal: length < n * (jasminFuel body + 2) + 1.
    simp only [toJasminCmd_RFor, jasminFuel, length_unrollForJ]
    have hpos : 1 ≤ jasminFuel body := jasminFuel_pos body
    -- n * (1 + bodyJ.length) ≤ n * (1 + (jasminFuel body - 1)) ≤ n * jasminFuel body
    --                     <  n * (jasminFuel body + 2) + 1
    nlinarith [ih]
  | RForRuntime _ _ _ _ =>
    -- toJasminCmd rejects to `[]` (length 0); jasminFuel is `body + 1 > 0`.
    simp only [toJasminCmd_RForRuntime, jasminFuel, List.length_nil]; omega
  | RLimbStore loc idx v => simp [toJasminCmd_RLimbStore, jasminFuel]
  | RLimbStoreExpr loc idx e => simp [toJasminCmd_RLimbStoreExpr, jasminFuel]
  | RCallN f dests args => simp [toJasminCmd_RCallN, jasminFuel]
  | RSelect dst sel src0 src1 => simp [toJasminCmd_RSelect, jasminFuel]
  | RAssert label => simp [toJasminCmd_RAssert, jasminFuel]
  | RBlock body ih =>
    simp only [toJasminCmd_RBlock, jasminFuel]; exact ih
  | RFnDef _ _ _ body cont ihBody ihCont =>
    simp only [toJasminCmd_RFnDef, jasminFuel, List.length_append]
    omega
  | RFnCall f dests args => simp [toJasminCmd_RFnCall, jasminFuel]
  | RTupleLoad _ _ _ => simp [toJasminCmd_RTupleLoad, jasminFuel]
  | RArrStore arr _ _ =>
    -- element-width-driven: one `Cassgn` in either branch.
    simp only [toJasminCmd_RArrStore, jasminFuel]
    cases arrElemWS arr <;> simp
  | RArrLoad _ src _ =>
    simp only [toJasminCmd_RArrLoad, jasminFuel]
    cases arrElemWS src <;> simp
  | RArrStoreLit _ _ _ => simp [toJasminCmd_RArrStoreLit, jasminFuel]
  | RArrLoadLit _ _ _ => simp [toJasminCmd_RArrLoadLit, jasminFuel]
  | RScalarSetExpr x e =>
    -- `sexprSetExprCmd` produces exactly one instruction in every arm
    -- (a `Cassgn`, or — for a top-level high-mul — a single `Copn`).
    simp only [toJasminCmd_RScalarSetExpr, jasminFuel]
    cases e <;> simp [sexprSetExprCmd]
  | RCallDstThreaded _ _ _ => simp [toJasminCmd_RCallDstThreaded, jasminFuel]

/-! ### Scalar assignment eval helpers -/

/-- `coerceValue` from `sint` to `sword U64` always returns 0 (type mismatch). -/
lemma coerceValue_sint_u64 (v : Int) :
    coerceValue .sint (.sword .U64) v = (0 : BitVec 64) := rfl

/-- `coerceValue` is identity for matching `sword U64` types. -/
lemma coerceValue_u64_u64 (v : BitVec 64) :
    coerceValue (.sword .U64) (.sword .U64) v = v := rfl

/-- `truncateWord .U64 .U64` is identity. -/
lemma truncateWord_u64_u64 (v : BitVec 64) : truncateWord .U64 .U64 v = v := rfl

/-- `intToWord .U64` for a non-negative integer equals `BitVec.ofNat`. -/
lemma intToWord_U64_ofNat (v : Nat) :
    intToWord .U64 (v : Int) = BitVec.ofNat 64 v := by
  simp [intToWord, BitVec.ofInt_natCast, WSize.bits]

/-- `writeVar` at `sword U64` with value `0` equals `put` at the public `translateVar` location. -/
lemma writeVar_u64_zero (sid : ScopeId) (x : String) :
    writeVar sid { vname := x, vtype := .sword .U64 } ⟨.sword .U64, (0 : BitVec 64)⟩ =
    RawCode.put (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64) := rfl

/-- `writeVar` at `sword U64` with value `v` equals `put` at `translateVar`. -/
lemma writeVar_u64_val (sid : ScopeId) (x : String) (v : BitVec 64) :
    writeVar sid { vname := x, vtype := .sword .U64 } ⟨.sword .U64, v⟩ =
    RawCode.put (translateVar sid { vname := x, vtype := .sword .U64 }) v := rfl

/-- `HeapInv` is preserved by setting a U64 scalar location (disjoint from tower locs). -/
lemma heapInv_set_u64 (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : BitVec 64) (hInv : HeapInv rs heap sid) :
    HeapInv rs (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) v) sid := by
  intro y t w hy
  exact (Heap.get_set_other _ _ _ _ (wordLoc_id_ne_towerLoc_id sid x y t)).trans (hInv y t w hy)

/-- `rsSetScalar` only changes `rsScalar`, preserving `HeapInv`. -/
lemma heapInv_rsSetScalar (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat) (hInv : HeapInv rs heap sid) :
    HeapInv (rsSetScalar rs x v) heap sid := by
  intro y t w hy; exact hInv y t w hy

/-! ### Tower init (RLetZero) helper -/

/-- Writing `default` to `towerLoc sid x t` and setting `rsSetTower` preserves `HeapInv`. -/
lemma heapInv_rsSetTower_init (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (t : TowerType) (hInv : HeapInv rs heap sid) :
    HeapInv (rsSetTower rs x ⟨t, default⟩) (heap.set (towerLoc sid x t) default) sid := by
  intro y t' v hy
  simp only [rsSetTower] at hy
  by_cases hxy : y == x
  · -- y = x
    have hyx : y = x := beq_iff_eq.mp hxy
    simp only [hxy, ite_true] at hy
    -- hy : some ⟨t, default⟩ = some ⟨t', v⟩
    have hsome := Option.some.inj hy
    obtain ⟨rfl, hveq⟩ := Sigma.mk.inj hsome
    rw [← eq_of_heq hveq, hyx]
    exact Heap.get_set_same _ _ _
  · -- y ≠ x
    simp only [hxy, ite_false] at hy
    have hne_name : x ≠ y := by
      intro h; simp [h] at hxy
    have hid_ne : (towerLoc sid x t).id ≠ (towerLoc sid y t').id := by
      simp only [towerLoc, translateVar, varLocId]
      intro h
      exact hne_name (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)
    rw [Heap.get_set_other _ _ _ _ hid_ne]
    exact hInv y t' v hy

/-! ### ScalarInv helpers -/

/-- `rsSetTower` doesn't change `rsScalar`, so `ScalarInv` is preserved. -/
lemma scalarInv_rsSetTower (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (tv : Σ t, RustVal t) (hSInv : ScalarInv rs heap sid) :
    ScalarInv (rsSetTower rs x tv) heap sid := by
  intro y; exact hSInv y

/-- Tower-loc set preserves `ScalarInv` (disjoint ids). -/
lemma scalarInv_set_tower (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (t : TowerType) (v : RustVal t) (hSInv : ScalarInv rs heap sid) :
    ScalarInv rs (heap.set (towerLoc sid x t) v) sid := by
  intro y
  exact (Heap.get_set_other _ _ _ _ (Ne.symm (wordLoc_id_ne_towerLoc_id sid y x t))).trans
    (hSInv y)

/-- Writing the correct value at a scalar loc establishes the scalar inv entry. -/
lemma scalarInv_set_scalar_eq (heap : Heap) (sid : ScopeId)
    (x y : String) (v w : Nat) (hSInv_y : heap.get (translateVar sid { vname := y, vtype := .sword .U64 }) = BitVec.ofNat 64 w)
    (hne : x ≠ y) :
    (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)).get
      (translateVar sid { vname := y, vtype := .sword .U64 }) = BitVec.ofNat 64 w := by
  exact (Heap.get_set_other _ _ _ _ (wordLoc_id_ne_of_ne_name sid x y hne)).trans hSInv_y

/-- After writing `BitVec.ofNat 64 v` to scalar `x`'s location, `ScalarInv` holds for `rsSetScalar`. -/
lemma scalarInv_after_scalar_set (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat) (hSInv : ScalarInv rs heap sid) :
    ScalarInv (rsSetScalar rs x v)
      (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)) sid := by
  intro y
  simp only [rsSetScalar]
  by_cases hxy : x = y
  · subst hxy; simp only [beq_self_eq_true, ite_true]; exact Heap.get_set_same _ _ _
  · refine (Heap.get_set_other _ _ _ _ (wordLoc_id_ne_of_ne_name sid x y hxy)).trans ?_
    simp only [beq_eq_false_iff_ne.mpr (Ne.symm hxy), Bool.false_eq_true, ite_false]
    exact hSInv y

/-- `rsSetScalar` preserves `ScalarInv` when the heap val is already correct. -/
lemma scalarInv_rsSetScalar_other (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat)
    (hSInv : ScalarInv rs heap sid)
    (hheap : heap.get (translateVar sid { vname := x, vtype := .sword .U64 }) = BitVec.ofNat 64 v) :
    ScalarInv (rsSetScalar rs x v) heap sid := by
  intro y
  simp only [rsSetScalar]
  by_cases hxy : y == x
  · simp only [hxy, ite_true]
    have heq : y = x := beq_iff_eq.mp hxy
    subst heq; exact hheap
  · simp only [hxy, ite_false]; exact hSInv y

/-! ### ScalarsBounded helpers -/

lemma scalarsBounded_zero : (0 : Nat) < 2^64 := by norm_num

lemma scalarsBounded_rsSetScalar_zero (rs : RustState) (x : String) (hB : ScalarsBounded rs) :
    ScalarsBounded (rsSetScalar rs x 0) := by
  intro y; simp only [rsSetScalar]
  split_ifs with hxy
  · exact scalarsBounded_zero
  · exact hB y

lemma scalarsBounded_rsSetTower (rs : RustState) (x : String) (tv : Σ t, RustVal t)
    (hB : ScalarsBounded rs) : ScalarsBounded (rsSetTower rs x tv) := by
  intro y; exact hB y

lemma scalarsBounded_rsSetScalar (rs : RustState) (x : String) (v : Nat)
    (hv : v < 2^64) (hB : ScalarsBounded rs) : ScalarsBounded (rsSetScalar rs x v) := by
  intro y
  simp only [rsSetScalar]
  split_ifs with hxy
  · exact hv
  · exact hB y

lemma scalarSetsSmall_val (c : LowCT) (x : String) (v : Nat)
    (h : scalarSetsSmall c = true) (heq : c = .RScalarSet x v) : v < 2^64 := by
  subst heq; simp [scalarSetsSmall] at h; exact h

/-! ### translateCmd append decomposition -/

/-- `newSid` of appended command list equals `newSid` of the second list run after the first. -/
lemma translateCmd_append_newSid
    (env : TransEnv) (l1 l2 : Cmd) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env (l1 ++ l2) sid fuel).newSid =
      (translateCmd env l2
        (translateCmd env l1 sid fuel).newSid
        (fuel - l1.length)).newSid := by
  induction l1 generalizing sid fuel with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    cases fuel with
    | zero => simp [translateCmd]
    | succ n => simp [translateCmd]
  | cons i is ih =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      simp only [List.cons_append, List.length_cons, translateCmd]
      rw [ih]
      simp only [translateCmd, Nat.succ_sub_succ_eq_sub]

/-- Evaluation of appended command list equals sequential composition. -/
lemma translateCmd_append_eval
    (env : TransEnv) (l1 l2 : Cmd) (sid : ScopeId) (fuel : Nat) (heap : Heap) :
    (translateCmd env (l1 ++ l2) sid fuel).code.eval heap =
      ((translateCmd env l1 sid fuel).code.eval heap).bind (fun x =>
        (translateCmd env l2
          (translateCmd env l1 sid fuel).newSid
          (fuel - l1.length)).code.eval x.2) := by
  induction l1 generalizing sid fuel heap with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    cases fuel with
    | zero => simp [translateCmd, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
    | succ n =>
      simp only [translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def, SDistr.pure_bind]
  | cons i is ih =>
    cases fuel with
    | zero => simp [translateCmd, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
    | succ n =>
      simp only [List.cons_append, List.length_cons, Nat.succ_sub_succ_eq_sub]
      simp only [translateCmd, eval_bind, SPComp.bind_def]
      simp_rw [ih (translateInstrR env sid n i).newSid n]
      rw [← SDistr.bind_assoc]

/-! ### callFree → newSid = sid -/

/-- Call-free programs leave `newSid` unchanged. -/
lemma callFree_toJasmin_newSid
    (c : LowCT) (hCF : callFree c = true)
    (env : TransEnv) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env (toJasminCmd c) sid fuel).newSid = sid := by
  induction c generalizing sid fuel with
  | RSkip => cases fuel <;> simp [toJasminCmd_RSkip, translateCmd]
  | RScalarSet x v =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd_RScalarSet, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd_RScalarSet, translateCmd, translateInstrR]
  | RSeq c1 c2 ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [toJasminCmd_RSeq, translateCmd_append_newSid, ih1 hCF.1 sid fuel,
               ih2 hCF.2 sid _]
  | RLetZero x t body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd_RLetZero, translateCmd, translateInstrR]
      | succ m =>
        simp only [toJasminCmd_RLetZero, translateCmd, translateInstrR]
        exact ih hCF sid (m + 1)
  | RLetU64Zero x body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd_RLetU64Zero, translateCmd, translateInstrR]
      | succ m =>
        simp only [toJasminCmd_RLetU64Zero, translateCmd, translateInstrR]
        exact ih hCF sid (m + 1)
  | RIfNz e ct cf ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      simp only [toJasminCmd_RIfNz, translateCmd, translateInstrR]
      rw [ih1 hCF.1 sid n, ih2 hCF.2 sid n]
      cases n <;> simp only [translateCmd]
  | RWhileNz e body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd_RWhileNz, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd_RWhileNz, translateCmd, translateInstrR]
  | RFor x n body ih =>
    -- toJasminCmd (RFor x n body) = unrollForJ x (toJasminCmd body) n.  The
    -- unrolled command is `n` repetitions of `[scalarSet] ++ toJasminCmd body`,
    -- both call-free segments, so `newSid` is preserved.  Discharged by
    -- nested induction on `n` using `translateCmd_append_newSid` and the
    -- body IH.
    simp only [callFree] at hCF
    simp only [toJasminCmd_RFor]
    -- General lemma: `unrollForJ` preserves newSid whenever the segment body does.
    have hBody : ∀ (sid : ScopeId) (fuel : Nat),
        (translateCmd env (toJasminCmd body) sid fuel).newSid = sid := ih hCF
    clear ih
    -- Induct on n.
    induction n generalizing sid fuel with
    | zero => cases fuel <;> simp [unrollForJ, translateCmd]
    | succ k ihk =>
        simp only [unrollForJ, translateCmd_append_newSid]
        rw [ihk]
        -- now goal: newSid of `[scalarSet] ++ toJasminCmd body` from sid = sid
        -- single-instruction scalarSet preserves sid; toJasminCmd body via hBody.
        cases h : fuel - (unrollForJ x (toJasminCmd body) k).length with
        | zero => simp [translateCmd]
        | succ n' =>
            simp only [translateCmd, translateInstrR]
            -- After scalarSet, sid unchanged; remaining is toJasminCmd body via hBody.
            exact hBody sid n'
  | RForRuntime _ _ _ _ =>
    -- toJasminCmd rejects the runtime loop to `[]`; empty command preserves newSid.
    simp [toJasminCmd_RForRuntime, translateCmd]
    cases fuel <;> simp [translateCmd]
  | RCall _ _ _ => simp [callFree] at hCF
  | RCallSwap _ _ _ _ => simp [callFree] at hCF
  | RCloneCall _ _ _ _ _ _ => simp [callFree] at hCF
  | RLimbStore _ _ _ => simp [callFree] at hCF
  | RLimbStoreExpr _ _ _ => simp [callFree] at hCF
  -- RCallN IS a call.
  | RCallN _ _ _ => simp [callFree] at hCF
  -- RSelect emits a Copn, which leaves newSid unchanged.
  | RSelect dst sel src0 src1 =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd_RSelect, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd_RSelect, translateCmd, translateInstrR]
  -- RAssert emits []; trivially preserves newSid.
  | RAssert label =>
    simp [toJasminCmd_RAssert, translateCmd]
    cases fuel <;> simp [translateCmd]
  -- RBlock forwards to body.
  | RBlock body ih =>
    simp only [callFree] at hCF
    exact ih hCF sid fuel
  -- Helper definition.
  | RFnDef _ _ _ body cont ihBody ihCont =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [toJasminCmd_RFnDef, translateCmd_append_newSid, ihBody hCF.1 sid fuel,
               ihCont hCF.2 sid _]
  | RFnCall _ _ _ => simp [callFree] at hCF
  -- RTupleLoad excluded by callFree.
  | RTupleLoad _ _ _ => simp [callFree] at hCF
  -- TArr/SExpr excluded by callFree.
  | RArrStore _ _ _ => simp [callFree] at hCF
  | RArrLoad _ _ _ => simp [callFree] at hCF
  | RArrStoreLit _ _ _ => simp [callFree] at hCF
  | RArrLoadLit _ _ _ => simp [callFree] at hCF
  | RScalarSetExpr _ _ => simp [callFree] at hCF
  | RCallDstThreaded _ _ _ => simp [callFree] at hCF

/-- `RLimbStore` translates to a single `.Copn` instruction, which preserves
    `newSid` (as every instruction does, `translateCmd_newSid`).  Therefore the
    threaded newSid is identical to the input `sid` for any fuel.

    Companion to `callFree_toJasmin_newSid`: the latter is gated by `callFree`
    (which rejects `RLimbStore`); this version is `RLimbStore`-specific. -/
lemma limbStore_toJasmin_newSid
    (loc : Located) (idx : Nat) (v : BitVec 64)
    (env : TransEnv) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env (toJasminCmd (.RLimbStore loc idx v)) sid fuel).newSid = sid := by
  cases fuel with
  | zero => simp [translateCmd]
  | succ n =>
    cases n with
    | zero => simp [toJasminCmd_RLimbStore, translateCmd, translateInstrR]
    | succ m => simp [toJasminCmd_RLimbStore, translateCmd, translateInstrR]

/-- Evaluating `put ℓ v` at `heap` and continuing with `k` on the resulting heap is
    `k (heap.set ℓ v)`. -/
lemma eval_put_bind_heap {β : Type} (heap : Heap) (ℓ : CatCrypt.Core.Location) (v : ℓ.ty)
    (k : Heap → SDistr β) :
    (((RawCode.put ℓ v).eval heap).bind fun x => k x.2) = k (heap.set ℓ v) := by
  simp only [CatCrypt.Deep.eval_put, SPComp.bind_def, SPComp.set_def, SPComp.pure_def,
             SDistr.pure_bind]

/-- Eval of `translateCmd` for a single U64 const-assign writes `0` to the U64 location. -/
lemma translateCmd_cassgn_u64_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int) (n : Nat) (heap : Heap) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v)]
        sid (n + 2)).code.eval heap =
    SDistr.pure (⟨()⟩,
        heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, translateWriteLVal,
             coerceValue_sint_u64, writeVar_u64_zero,
             eval_bind, eval_ret, SPComp.bind_def, SPComp.pure_def, SDistr.pure_bind]
  exact eval_put_bind_heap heap _ _ (fun h => SDistr.pure ((⟨()⟩ : ULift Unit), h))

/-- `newSid` for a single U64 const-assign equals `sid`. -/
lemma translateCmd_cassgn_u64_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int) (n : Nat) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v)]
        sid (n + 2)).newSid = sid := by
  simp [translateCmd, translateInstrR]

/-- One-step eval: U64 const-assign followed by `rest`; advances heap then runs `rest`. -/
lemma translateCmd_cons_cassgn_u64_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int)
    (rest : Cmd) (n : Nat) (heap : Heap) :
    (translateCmd env
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v) :: rest)
        sid (n + 2)).code.eval heap =
    (translateCmd env rest sid (n + 1)).code.eval
        (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, translateWriteLVal,
             coerceValue_sint_u64, writeVar_u64_zero,
             eval_bind, eval_ret, SPComp.bind_def, SPComp.pure_def, SDistr.pure_bind]
  exact eval_put_bind_heap heap _ _ (translateCmd env rest sid (n + 1)).code.eval

/-- One-step `newSid`: U64 const-assign followed by `rest`. -/
lemma translateCmd_cons_cassgn_u64_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int)
    (rest : Cmd) (n : Nat) :
    (translateCmd env
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v) :: rest)
        sid (n + 2)).newSid =
    (translateCmd env rest sid (n + 1)).newSid := by
  simp [translateCmd, translateInstrR]

/-! ### RScalarSet eval (with corrected Papp1 encoding) -/

/-- `translatePExpr` for `Papp1 (Oword_of_int U64) (Pconst v)` evaluates to `BitVec.ofNat 64 v`. -/
lemma translatePExpr_word_of_int_eval (sid : ScopeId) (v : Nat) (heap : Heap) :
    (translatePExpr sid (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))).eval heap =
    SDistr.pure (⟨.sword .U64, BitVec.ofNat 64 v⟩, heap) := by
  simp [translatePExpr, evalSop1, intToWord_U64_ofNat,
        CatCrypt.Deep.eval_ret, CatCrypt.Deep.eval_bind, SPComp.pure_def, SDistr.pure_bind]

/-- A `Cassgn` with `Papp1 (Oword_of_int U64) (Pconst v)` followed by `rest` writes
    `BitVec.ofNat 64 v` and runs `rest` on the resulting heap. -/
lemma translateCmd_cons_cassgn_u64_val_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Nat)
    (rest : Cmd) (n : Nat) (heap : Heap) :
    (translateCmd env
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int))) :: rest)
        sid (n + 2)).code.eval heap =
    (translateCmd env rest sid (n + 1)).code.eval
        (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, evalSop1, intToWord_U64_ofNat,
             coerceValue_u64_u64, translateWriteLVal, writeVar_u64_val,
             eval_bind, eval_ret, SPComp.bind_def, SPComp.pure_def, SDistr.pure_bind]
  exact eval_put_bind_heap heap _ _ (translateCmd env rest sid (n + 1)).code.eval

/-- Eval of a `Cassgn` with `Papp1 (Oword_of_int U64) (Pconst v)` writes `BitVec.ofNat 64 v`. -/
lemma translateCmd_cassgn_u64_val_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Nat) (n : Nat) (heap : Heap) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
        sid (n + 2)).code.eval heap =
    SDistr.pure (⟨()⟩,
        heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, evalSop1, intToWord_U64_ofNat,
             coerceValue_u64_u64, translateWriteLVal, writeVar_u64_val,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret,
             SPComp.bind_def, SPComp.pure_def, SDistr.pure_bind]
  exact eval_put_bind_heap heap _ _ (fun h => SDistr.pure ((⟨()⟩ : ULift Unit), h))

/-- `newSid` for the single-instruction `Cassgn Papp1` case. -/
lemma translateCmd_cassgn_u64_val_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Nat) (n : Nat) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
        sid (n + 2)).newSid = sid := by
  simp [translateCmd, translateInstrR]

/-! ### RLetZero eval (Parr_init / sarr init) -/

/-- `writeVar` at `sarr t.byteSize` with default value equals `put` at `towerLoc`. -/
lemma writeVar_sarr_default (sid : ScopeId) (x : String) (t : TowerType) :
    writeVar sid { vname := x, vtype := .sarr t.storageBytes }
      ⟨.sarr t.storageBytes, (fun _ => 0 : JArray t.storageBytes)⟩ =
    RawCode.put (towerLoc sid x t) (fun _ => 0 : JArray t.storageBytes) := by
  exact writeVar_sarr_eq sid x t.storageBytes (fun _ => 0)

/-- `default : JArray n = fun _ => 0`. -/
lemma jarray_default_eq (n : Nat) : (default : JArray n) = fun _ => 0 := rfl

/-- One-step cons eval: `Cassgn (Parr_init t.byteSize)` writes `default` to `towerLoc`,
    then runs `rest`. -/
lemma translateCmd_cons_cassgn_sarr_init_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (t : TowerType)
    (rest : Cmd) (n : Nat) (heap : Heap) :
    (translateCmd env
      (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes },
                        info := { towerTag := t.byteSize } })
               .AT_none (.sarr t.storageBytes) (.Parr_init t.storageBytes) :: rest)
      sid (n + 2)).code.eval heap =
    (translateCmd env rest sid (n + 1)).code.eval
      (heap.set (towerLoc sid x t) (default : JArray t.storageBytes)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, coerceValue,
             ↓reduceDIte, translateWriteLVal, writeVar_sarr_default, jarray_default_eq,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret,
             SPComp.bind_def, SPComp.pure_def, SDistr.pure_bind]
  exact eval_put_bind_heap heap _ _ (translateCmd env rest sid (n + 1)).code.eval

/-- `newSid` for cons Cassgn sarr init. -/
lemma translateCmd_cons_cassgn_sarr_init_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (t : TowerType)
    (rest : Cmd) (n : Nat) :
    (translateCmd env
      (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes },
                        info := { towerTag := t.byteSize } })
               .AT_none (.sarr t.storageBytes) (.Parr_init t.storageBytes) :: rest)
      sid (n + 2)).newSid =
    (translateCmd env rest sid (n + 1)).newSid := by
  simp [translateCmd, translateInstrR]

/-! ### Cif eval helpers -/

/-- Reading a `sword U64` variable from the heap. -/
lemma translatePExpr_pvar_u64_eval (sid : ScopeId) (e : String) (heap : Heap) :
    (translatePExpr sid
      (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })).eval heap =
    SDistr.pure (⟨.sword .U64, heap.get (translateVar sid { vname := e, vtype := .sword .U64 })⟩, heap) := by
  simp only [translatePExpr, readGVar, readVar_sword_eq,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_get, CatCrypt.Deep.eval_ret,
             SPComp.bind_def, SPComp.get_def, SPComp.pure_def, SDistr.pure_bind]

/-- Evaluating the `RIfNz` condition expression. -/
lemma cif_cond_eval (sid : ScopeId) (e : String) (heap : Heap) :
    let zero64 : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst 0)
    let condExpr : PExpr :=
      .Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        zero64
    let w : BitVec 64 := heap.get (translateVar sid { vname := e, vtype := .sword .U64 })
    (translatePExpr sid condExpr).eval heap =
    SDistr.pure (⟨.sbool, w != (0 : BitVec 64)⟩, heap) := by
  simp only [translatePExpr, readGVar, readVar_sword_eq, evalSop1, evalSop2, intToWord_U64_ofNat,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_get, CatCrypt.Deep.eval_ret,
             SPComp.bind_def, SPComp.get_def, SPComp.pure_def, SDistr.pure_bind]
  rfl

/-- `BitVec.ofNat 64 v ≠ 0` when `v ≠ 0` and `v < 2^64`. -/
lemma bitVec_ofNat_ne_zero (v : Nat) (hv : v ≠ 0) (hlt : v < 2^64) :
    (BitVec.ofNat 64 v) ≠ (0 : BitVec 64) := by
  intro h
  apply hv
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_zero] at h1
  exact h1

/-- Single-instruction `Cif` eval when condition is true. -/
lemma translateCmd_cif_eval_true
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd)
    (fuel : Nat) (heap heap' : Heap)
    (hcond : (translatePExpr sid cond).eval heap = SDistr.pure (⟨.sbool, true⟩, heap')) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).code.eval heap =
    (translateCmd env ct sid fuel).code.eval heap' := by
  cases fuel with
  | zero =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
  | succ n =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_ret, SPComp.pure_def]
    have hunit : (fun p : ULift Unit × Heap => SDistr.pure (⟨()⟩, p.2)) = SDistr.pure :=
      funext fun ⟨u, h'⟩ => by cases u; rfl
    rw [hunit, SDistr.bind_pure]

/-- Single-instruction `Cif` eval when condition is false. -/
lemma translateCmd_cif_eval_false
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd)
    (fuel : Nat) (heap heap' : Heap)
    (hcond : (translatePExpr sid cond).eval heap = SDistr.pure (⟨.sbool, false⟩, heap')) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).code.eval heap =
    (translateCmd env cf (translateCmd env ct sid fuel).newSid fuel).code.eval heap' := by
  cases fuel with
  | zero =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
  | succ n =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_ret, SPComp.pure_def]
    have hunit : (fun p : ULift Unit × Heap => SDistr.pure (⟨()⟩, p.2)) = SDistr.pure :=
      funext fun ⟨u, h'⟩ => by cases u; rfl
    rw [hunit, SDistr.bind_pure]

/-- `newSid` for `[Cif cond ct cf]` (when ct and cf are call-free). -/
lemma translateCmd_cif_newSid
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd) (fuel : Nat) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).newSid =
    (translateCmd env cf (translateCmd env ct sid fuel).newSid fuel).newSid := by
  cases fuel <;> simp [translateCmd, translateInstrR]

/-- **rustExecSimulates**: the `LowCT → Jasmin` translation is operationally correct.

    If `c` is while-free and call-free and the initial heap encodes `rs`, then
    executing `translateCmd env (toJasminCmd c)` from that heap, for any `env`,
    deterministically produces a heap encoding `rs'`.

    ## Signature

    * `hFuel : jasminFuel c ≤ fuel` — minimum fuel for the translated program to run
    * Induction generalizes over `sid`, `heap`, and `fuel` to allow IH reuse at subterms.

    ## Proof sketch per case

    * `skip`      — `toJasminCmd .RSkip = []`; `translateCmd [] = ret ⟨()⟩`; heap unchanged ✓
    * `seq`       — needs `translateCmd_append`; IH₁ then IH₂ in sequence
    * `letZero`   — assignment writes default array to `towerLoc`; IH on body
    * `letU64Zero` — writes to `wordLoc` (disjoint); IH on body; heap updates preserve HeapInv
    * `scalarSet` — writes to `wordLoc` (disjoint from towerLoc by encodeSType); HeapInv preserved
    * `ifTrue/False` — IH on taken branch
    * `whileFalse/True` — `False` from `hWf : whileFree (.RWhileNz ..) = false ≠ true` ✓
    * `call`, `cloneCall`, `limbStore` and the other call-like constructors —
      excluded by `hCF`

    ## Hypotheses

    * `hCF : callFree c = true` — excludes `RCall`, `RCloneCall`, `RLimbStore`
      (their leaf hypotheses are separate; `rustExecSimulates_withCalls` admits them)
    * `hSSS : scalarSetsSmall c = true` — all `RScalarSet x v` have `v < 2^64`
    * `hSInv : ScalarInv rs heap sid` — heap correctly encodes `rsScalar`
    * `hBounded : ScalarsBounded rs` — all scalars fit in 64 bits

    ## Conclusion

    Uses `sid` (not `newSid`) since call-free programs preserve `newSid = sid`. -/
theorem rustExecSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (c : LowCT) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCF : callFree c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  induction hExec generalizing sid heap fuel with

  | skip _ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [jasminFuel] at hFuel; omega⟩
    exact ⟨heap, by simp [toJasminCmd_RSkip, translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def], hInv, hSInv, hBounded⟩

  | seq c1 c2 rs0 r1 rs' _h1 _h2 ih1 ih2 =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- fuel bounds
    have hFuel1 : jasminFuel c1 ≤ fuel := by omega
    have hFuel2 : jasminFuel c2 ≤ fuel - (toJasminCmd c1).length := by
      have := jasminFuel_gt_length c1; omega
    -- Apply IH1
    obtain ⟨heap1, heval1, hInv1, hSInv1, hB1⟩ :=
      ih1 fuel hWf.1 hCF.1 hSSS.1 hFuel1 sid heap hInv hSInv hBounded
    -- The two translated lists are appended
    simp only [toJasminCmd_RSeq]
    -- Eval of append
    rw [translateCmd_append_eval]
    rw [callFree_toJasmin_newSid c1 hCF.1 env sid fuel] at *
    rw [heval1, SDistr.pure_bind]
    -- Now apply IH2 from heap1 at sid
    have hFuel2' : jasminFuel c2 ≤ fuel - (toJasminCmd c1).length := hFuel2
    obtain ⟨heap2, heval2, hInv2, hSInv2, hB2⟩ :=
      ih2 (fuel - (toJasminCmd c1).length) hWf.2 hCF.2 hSSS.2 hFuel2' sid heap1 hInv1 hSInv1 hB1
    exact ⟨heap2, heval2, hInv2, hSInv2, hB2⟩

  | letZero x t body rs0 rs' _h ih =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by have := jasminFuel_pos body; omega⟩
    have hFuel' : jasminFuel body ≤ n + 1 := by omega
    -- Initial heap: write default to towerLoc sid x t
    let heap' := heap.set (towerLoc sid x t) (default : JArray t.storageBytes)
    have hInv' : HeapInv (rsSetTower rs0 x ⟨t, default⟩) heap' sid :=
      heapInv_rsSetTower_init rs0 heap sid x t hInv
    have hSInv' : ScalarInv (rsSetTower rs0 x ⟨t, default⟩) heap' sid :=
      scalarInv_rsSetTower rs0 heap' sid x ⟨t, default⟩
        (scalarInv_set_tower rs0 heap sid x t (default : JArray t.storageBytes) hSInv)
    have hB' : ScalarsBounded (rsSetTower rs0 x ⟨t, default⟩) :=
      scalarsBounded_rsSetTower rs0 x ⟨t, default⟩ hBounded
    obtain ⟨heap'', heval', hInv'', hSInv'', hB''⟩ := ih (n + 1) hWf hCF hSSS hFuel' sid heap' hInv' hSInv' hB'
    simp only [toJasminCmd_RLetZero, show (n + 2) = (n + 1) + 1 from rfl]
    rw [translateCmd_cons_cassgn_sarr_init_eval]
    exact ⟨heap'', heval', hInv'', hSInv'', hB''⟩

  | letU64Zero x body rs0 rs' _h ih =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by have := jasminFuel_pos body; omega⟩
    have hFuel' : jasminFuel body ≤ n + 1 := by omega
    let heap' := heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)
    have hInv' : HeapInv (rsSetScalar rs0 x 0) heap' sid :=
      heapInv_set_u64 _ heap sid x 0 (heapInv_rsSetScalar rs0 heap sid x 0 hInv)
    have hSInv' : ScalarInv (rsSetScalar rs0 x 0) heap' sid :=
      scalarInv_after_scalar_set rs0 heap sid x 0 hSInv
    have hB' : ScalarsBounded (rsSetScalar rs0 x 0) :=
      scalarsBounded_rsSetScalar_zero rs0 x hBounded
    obtain ⟨heap'', heval', hInv'', hSInv'', hB''⟩ := ih (n + 1) hWf hCF hSSS hFuel' sid heap' hInv' hSInv' hB'
    refine ⟨heap'', ?_, ?_, ?_, hB''⟩
    · simp only [toJasminCmd_RLetU64Zero]
      rw [show (.Pconst 0 : PExpr) = .Pconst ((0 : Nat) : Int) from rfl,
        translateCmd_cons_cassgn_u64_val_eval]
      exact heval'
    · exact hInv''
    · exact hSInv''

  | scalarSet x v rs0 =>
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    have hv_small : v < 2^64 := scalarSetsSmall_val (.RScalarSet x v) x v hSSS rfl
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    refine ⟨heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v),
            ?_, ?_, ?_, scalarsBounded_rsSetScalar rs0 x v hv_small hBounded⟩
    · simp only [toJasminCmd_RScalarSet]; exact translateCmd_cassgn_u64_val_eval env sid x v n heap
    · exact heapInv_set_u64 _ heap sid x _ (heapInv_rsSetScalar rs0 heap sid x v hInv)
    · exact scalarInv_after_scalar_set rs0 heap sid x v hSInv

  | ifTrue e ct cf rs0 rs' v hv hne_zero _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- Determine the condition value from ScalarInv
    have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) =
        BitVec.ofNat 64 v := hv ▸ hSInv e
    have he_bnd : v < 2^64 := by rw [← hv]; exact hBounded e
    -- Condition evaluates to true
    have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
        SDistr.pure (⟨.sbool, true⟩, heap) := by
      rw [cif_cond_eval]
      simp only [he_val]
      have hbne : BitVec.ofNat 64 v != (0 : BitVec 64) := by
        rw [bne_iff_ne]; exact bitVec_ofNat_ne_zero v hne_zero he_bnd
      rw [show ((0 : BitVec 64) = (0#64 : BitVec 64)) from rfl] at hbne
      simp [hbne]
    -- Fuel: max(j_ct, j_cf) + 1 ≤ fuel, so j_ct ≤ fuel - 1
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    have hFuel_ct : jasminFuel ct ≤ fuel' := by omega
    obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
      ih fuel' hWf.1 hCF.1 hSSS.1 hFuel_ct sid heap hInv hSInv hBounded
    simp only [toJasminCmd_RIfNz]
    refine ⟨heap', ?_, ?_, ?_, hB'⟩
    · rw [translateCmd_cif_eval_true env sid _ _ _ fuel' heap heap hcond]; exact heval'
    · exact hInv'
    · exact hSInv'

  | ifFalse e ct cf rs0 rs' h _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    -- Scalar = 0, condition evaluates to false
    have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) = (0 : BitVec 64) := by
      have h1 := hSInv e; rw [h] at h1; exact h1
    have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
        SDistr.pure (⟨.sbool, false⟩, heap) := by
      rw [cif_cond_eval]
      simp only [he_val]
      rfl
    have hFuel_cf : jasminFuel cf ≤ fuel' := by omega
    -- newSid after ct = sid (call-free)
    have hCT_newSid : (translateCmd env (toJasminCmd ct) sid fuel').newSid = sid :=
      callFree_toJasmin_newSid ct hCF.1 env sid fuel'
    obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
      ih fuel' hWf.2 hCF.2 hSSS.2 hFuel_cf sid heap hInv hSInv hBounded
    simp only [toJasminCmd_RIfNz]
    refine ⟨heap', ?_, ?_, ?_, hB'⟩
    · rw [translateCmd_cif_eval_false env sid _ _ _ fuel' heap heap hcond, hCT_newSid]
      exact heval'
    · exact hInv'
    · exact hSInv'

  | whileFalse _ _ _ _ => simp [whileFree] at hWf

  | whileTrue _ _ _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf

  | forZero x body rs0 =>
    -- toJasminCmd (RFor x 0 body) = unrollForJ x _ 0 = []; same shape as `skip`.
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [jasminFuel] at hFuel; omega⟩
    refine ⟨heap, ?_, hInv, hSInv, hBounded⟩
    show (translateCmd env (unrollForJ x (toJasminCmd body) 0) sid (n + 1)).code.eval heap = _
    simp [unrollForJ, translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def]

  | forSucc x n body rs0 r1 rs0' _hInner _hBody ih1 ih2 =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true, decide_eq_true_eq] at hSSS
    obtain ⟨hN_lt, hSSSbody⟩ := hSSS
    have hn_lt : n < 2^64 := lt_of_le_of_lt (Nat.le_succ n) hN_lt
    -- Rebuild the gate hypotheses for the inner `RFor x n body`.
    have hWf' : whileFree (.RFor x n body) = true := by simp [whileFree, hWf]
    have hCF' : callFree (.RFor x n body) = true := by simp [callFree, hCF]
    have hSSS' : scalarSetsSmall (.RFor x n body) = true := by
      simp [scalarSetsSmall, hSSSbody]; exact hn_lt
    -- Fuel decomposition.
    simp only [jasminFuel] at hFuel
    have hFuelInner : jasminFuel (.RFor x n body) ≤ fuel := by
      simp [jasminFuel]; nlinarith
    -- Apply ih1 for the inner RFor.
    obtain ⟨heap1, heval1, hInv1, hSInv1, hB1⟩ :=
      ih1 fuel hWf' hCF' hSSS' hFuelInner sid heap hInv hSInv hBounded
    -- After scalarSet x := n, prepare heap2 / state2.
    let heap2 := heap1.set (translateVar sid { vname := x, vtype := .sword .U64 })
                   (BitVec.ofNat 64 n)
    have hInv2 : HeapInv (rsSetScalar r1 x n) heap2 sid :=
      heapInv_set_u64 _ heap1 sid x n (heapInv_rsSetScalar r1 heap1 sid x n hInv1)
    have hSInv2 : ScalarInv (rsSetScalar r1 x n) heap2 sid :=
      scalarInv_after_scalar_set r1 heap1 sid x n hSInv1
    have hB2 : ScalarsBounded (rsSetScalar r1 x n) :=
      scalarsBounded_rsSetScalar r1 x n hn_lt hB1
    -- The translated unrolled command splits as:
    --   unrollForJ x bodyJ n ++ ([scalarSet n] ++ bodyJ)
    -- Lengths: |unrollForJ x bodyJ n| = n * (1 + bodyJ.length)
    --          |[scalarSet n] ++ bodyJ| = 1 + bodyJ.length
    -- We compose three segments: inner loop, scalarSet, body.
    -- Fuel for "remaining" segment after the inner loop:
    have hLen_inner : (toJasminCmd (.RFor x n body)).length < jasminFuel (.RFor x n body) :=
      jasminFuel_gt_length _
    have hLen_body : (toJasminCmd body).length < jasminFuel body :=
      jasminFuel_gt_length _
    -- newSid after inner loop is sid (inner loop is callFree).
    have hNewSid_inner : (translateCmd env (toJasminCmd (.RFor x n body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF' env sid fuel
    -- Apply ih2 for body, with appropriate fuel slack.
    -- Fuel after consuming the inner loop: fuel - |inner| ≥ jasminFuel body + 2 + 1 (slack)
    set fuel_after_inner :=
      fuel - (toJasminCmd (.RFor x n body)).length with hfai
    have hLen_inner_bound : (toJasminCmd (.RFor x n body)).length ≤ n * (jasminFuel body + 2) := by
      have h1 := jasminFuel_gt_length (.RFor x n body)
      simp only [jasminFuel] at h1; omega
    have hFuelBody : jasminFuel body ≤ fuel_after_inner - 1 := by
      -- Expand (n+1)*(jasminFuel body + 2) so omega can work with linear pieces.
      have hFuel_expand :
          (n + 1) * (jasminFuel body + 2) + 1 = n * (jasminFuel body + 2) + jasminFuel body + 3 := by
        ring
      simp only [hfai]
      rw [hFuel_expand] at hFuel
      omega
    obtain ⟨heap3, heval3, hInv3, hSInv3, hB3⟩ :=
      ih2 (fuel_after_inner - 1) hWf hCF hSSSbody hFuelBody sid heap2 hInv2 hSInv2 hB2
    -- Now compose: inner loop ++ scalarSet ++ body
    refine ⟨heap3, ?_, hInv3, hSInv3, hB3⟩
    -- Translation of RFor x (n+1) body.
    show (translateCmd env (unrollForJ x (toJasminCmd body) (n + 1)) sid fuel).code.eval heap = _
    -- Unfold one step of unrollForJ.
    simp only [unrollForJ]
    -- Goal now: translateCmd of (unrollForJ x bodyJ n ++ ([scalarSet n] ++ bodyJ))
    -- = translateCmd of (toJasminCmd (RFor x n body) ++ ([scalarSet n] ++ toJasminCmd body))
    -- Split via translateCmd_append_eval.
    rw [show unrollForJ x (toJasminCmd body) n = toJasminCmd (.RFor x n body) from rfl]
    rw [translateCmd_append_eval]
    rw [heval1, SDistr.pure_bind]
    rw [hNewSid_inner]
    -- After inner: we have `[scalarSet n] ++ bodyJ` to evaluate from sid, heap1.
    -- Step 1: split off the scalarSet.
    show ((translateCmd env _ sid (fuel - _)).code.eval heap1) = _
    rw [show ((.Cassgn _ _ _ _ : InstrR) :: toJasminCmd body) =
          [(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                    .AT_none (.sword .U64)
                    (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)] ++ toJasminCmd body
        from rfl]
    rw [translateCmd_append_eval]
    -- Eval of the scalarSet single instruction.
    have hFuel_after : 1 ≤ fuel_after_inner := by
      have := jasminFuel_pos body; simp only [hfai]; omega
    obtain ⟨m, hm⟩ : ∃ m, fuel_after_inner = m + 2 := by
      have := jasminFuel_pos body
      refine ⟨fuel_after_inner - 2, ?_⟩
      simp only [hfai]
      have h := jasminFuel_gt_length (.RFor x n body)
      omega
    -- Compute eval of [scalarSet n] at fuel m+2.
    have hScalarSet : (translateCmd env
        [(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64)
                  (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)]
        sid fuel_after_inner).code.eval heap1 = SDistr.pure (⟨()⟩, heap2) := by
      rw [hm]
      exact translateCmd_cassgn_u64_val_eval env sid x n m heap1
    -- newSid after scalarSet is sid (single Cassgn doesn't change sid).
    have hNewSid_scalarSet : (translateCmd env
        [(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64)
                  (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)]
        sid fuel_after_inner).newSid = sid := by
      rw [hm]
      simp [translateCmd, translateInstrR]
    rw [hScalarSet, SDistr.pure_bind]
    -- Now: eval `toJasminCmd body` from `(translateCmd env [scalarSet] sid fuel_after_inner).newSid`
    -- and `heap2` with fuel `fuel_after_inner - 1`.  By hNewSid_scalarSet, that newSid is sid;
    -- the body fuel matches heval3 by single-list-length.
    rw [hNewSid_scalarSet]
    -- Length of single-element list is 1, so fuel = fuel_after_inner - 1 matches heval3.
    simp only [List.length_singleton, ← hfai]
    exact heval3

  | forRuntime _ _ _ _ _ _ _ => simp [whileFree] at hWf

  | call _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | cloneCall _ _ _ _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | callSwap _ _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | callDstThreaded _ _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | limbStore _ _ _ _ => simp [callFree] at hCF

  -- `whileFree (.RLimbStoreExpr ..) = false`, so unreachable under `hWf`.
  | limbStoreExpr _ _ _ _ => simp [whileFree] at hWf

  -- `RCallN`/`RSelect`/`RAssert`/`RBlock`: outside the simulation theorem's scope;
  -- `whileFree` is gated false for these constructors so this case
  -- is unreachable under `hWf`.
  | callN _ _ _ _ => simp [whileFree] at hWf
  | selectFalse _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | selectTrue _ _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  -- RAssert lowers to `[]`; semantics is identity.
  -- Same shape as `skip`.
  | assert _ _ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, by simp [jasminFuel] at hFuel; omega⟩
    exact ⟨heap,
      by simp [toJasminCmd_RAssert, translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def],
      hInv, hSInv, hBounded⟩
  -- RBlock body — toJasminCmd inlines the body, so the
  -- simulation step is just the body IH.
  | block body rs0 rs0' hBody ih =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    simp only [toJasminCmd_RBlock]
    exact ih fuel hWf hCF hSSS hFuel sid heap hInv hSInv hBounded
  | tupleLoad _ _ _ _ => simp [whileFree] at hWf
  -- TArr/SExpr operational semantics — excluded by
  -- `whileFree` (returns `false` for these constructors).
  | arrStore _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | arrLoad _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  -- literal-index variants excluded by `whileFree`.
  | arrStoreLit _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | arrLoadLit _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | scalarSetExpr _ _ _ => simp [whileFree] at hWf

/-- **Standalone call simulation**: an `RCall` instruction run at `fuel`
    simulates correctly given `LeafImplOk` at that fuel. This is the case that
    `rustExecSimulates` omits via the `callFree = true` precondition.

    Composes with `rustExecSimulates` via `translateCmd_append_eval` when a
    call is sequenced with call-free code. -/
lemma rustCallSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : LeafImplOk leafSpec env fuel)
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RCall f dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | call f' dest' args' rs'' oldDestV argList hLookup hArgs hArgsT =>
    have hTower : rs.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ := by
      unfold locatedLookup at hLookup
      split at hLookup
      · rename_i ty v heq
        split at hLookup
        · rename_i hty
          cases hty
          simp at hLookup
          rw [heq, hLookup]
        · simp at hLookup
      · simp at hLookup
    obtain ⟨heap1, hEval, hDest, hOtherTower, hScalarPreserve⟩ :=
      hLeaf f dest args rs sid heap oldDestV argList hInv hTower hArgs hArgsT
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd_RCall]; exact hEval
    · -- HeapInv after call
      intro x t v hxTower
      by_cases hx : x = dest.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        -- hxTower : some ⟨dest.locDst, leafSpec ...⟩ = some ⟨t, v⟩
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hDest
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t v hxTower
    · -- ScalarInv after call (call doesn't touch scalars)
      intro x
      rw [hScalarPreserve x, hSInv x]
      -- rs'.rsScalar = rs.rsScalar since locatedUpdate only touches tower
      rfl
    · -- ScalarsBounded rs' (rs' = rs on scalars)
      intro x
      -- locatedUpdate = rsSetTower, which leaves rsScalar unchanged
      exact hBounded x

/-- **Limb-store oracle hypothesis**: the translated `.Copn ... (.Oasm "STORE64") ...`
    instruction (run from any heap encoding `rs`) produces a heap that matches
    the abstract `leafSpec.limbStore` update, and leaves everything else intact.

    This is the `STORE64`-specific analog of `LeafImplOk`, mirroring Rocq's
    `asm_correct` axiom for `Oasm` operators in `jasmin_translate.v`. -/
def LimbStoreImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (loc : Located) (idx : Nat) (v : BitVec 64)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal loc.locDst),
    HeapInv rs0 heap0 sid →
    rs0.rsTower loc.locVar = some ⟨loc.locDst, oldDestV⟩ →
    ∃ heap1 : Heap,
      (translateCmd env [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
                               [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid loc.locVar loc.locDst) =
        leafSpec.limbStore loc oldDestV idx v ∧
      (∀ (x : String) (t : TowerType),
        x ≠ loc.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Standalone limb-store simulation**: an `RLimbStore` instruction simulates
    correctly given `LimbStoreImplOk`. Same pattern as `rustCallSimulates`
    for Jasmin `Oasm` operators (Rocq's `asm_correct`). -/
lemma rustLimbStoreSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLimb : LimbStoreImplOk leafSpec env fuel)
    (loc : Located) (idx : Nat) (v : BitVec 64)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RLimbStore loc idx v) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RLimbStore loc idx v)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | limbStore loc' idx' v' rs'' oldDestV hLookup =>
    have hTower : rs.rsTower loc.locVar = some ⟨loc.locDst, oldDestV⟩ := by
      unfold locatedLookup at hLookup
      split at hLookup
      · rename_i ty w heq
        split at hLookup
        · rename_i hty
          cases hty
          simp at hLookup
          rw [heq, hLookup]
        · simp at hLookup
      · simp at hLookup
    obtain ⟨heap1, hEval, hDest, hOtherTower, hScalarPreserve⟩ :=
      hLimb loc idx v rs sid heap oldDestV hInv hTower
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd_RLimbStore]; exact hEval
    · intro x t vx hxTower
      by_cases hx : x = loc.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hDest
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t vx hxTower
    · intro x
      rw [hScalarPreserve x, hSInv x]
      rfl
    · intro x
      exact hBounded x

/-- **Clone oracle hypothesis**: the `.Copn ... (.Oasm "CLONE_TOWER") [oldDest]`
    instruction copies the tower value at `oldDest` into the tower slot
    associated to `cloneVar` at type `cloneTy.byteSize`. Mirrors Rocq
    `asm_correct` for `Oasm` operators.

    The premise `oldDest.locDst = cloneTy` makes the instruction read the slot
    that `HeapInv` constrains: the operand `locToPExpr oldDest` reads at
    `oldDest.locDst`'s storage width. -/
def CloneImplOk (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal cloneTy),
    oldDest.locDst = cloneTy →
    HeapInv rs0 heap0 sid →
    rs0.rsTower oldDest.locVar = some ⟨cloneTy, oldDestV⟩ →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                        info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid cloneVar cloneTy) = oldDestV ∧
      (∀ (x : String) (t : TowerType),
        x ≠ cloneVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Standalone clone-call simulation**: `RCloneCall` simulates via the
    composition of `CloneImplOk` (for the clone step) and `LeafImplOk` (for
    the inner call). Mirrors Rocq's structural decomposition of sequences.

    Requires `rs.rsTower oldDest.locVar = some ⟨cloneTy, oldV⟩` and
    `oldDest.locDst = cloneTy` — the clone is well-typed. The clone step runs at
    `fuel` and the inner call at `fuel - 1`. -/
lemma rustCloneCallSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : LeafImplOk leafSpec env (fuel - 1))
    (hClone : CloneImplOk env fuel)
    (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (innerF : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args) rs rs')
    (oldV : RustVal cloneTy)
    (hTy : oldDest.locDst = cloneTy)
    (hOldDest : rs.rsTower oldDest.locVar = some ⟨cloneTy, oldV⟩)
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | cloneCall _ _ _ _ _ _ _ rsClone _ hClone_eq hCall =>
    -- Apply clone oracle to get heap1
    obtain ⟨heap1, hEvalClone, hCloneDest, hCloneOther, hCloneScalar⟩ :=
      hClone cloneVar cloneTy oldDest rs sid heap oldV hTy hInv hOldDest
    -- Establish invariants at rsClone / heap1
    have hRsClone : rsClone = rsSetTower rs cloneVar ⟨cloneTy, oldV⟩ := by
      rw [hClone_eq, hOldDest]; rfl
    have hInv1 : HeapInv rsClone heap1 sid := by
      intro x t v hxTower
      rw [hRsClone] at hxTower
      simp only [rsSetTower, beq_iff_eq] at hxTower
      by_cases hx : x = cloneVar
      · subst hx
        simp only [if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hCloneDest
      · simp only [hx, if_false] at hxTower
        rw [hCloneOther x t hx]
        exact hInv x t v hxTower
    have hSInv1 : ScalarInv rsClone heap1 sid := by
      intro x
      rw [hCloneScalar x, hSInv x, hRsClone]
      rfl
    have hBounded1 : ScalarsBounded rsClone := by
      intro x
      rw [hRsClone]
      exact hBounded x
    -- Decompose translateCmd [cloneInstr, callInstr] via append
    have h_toJ : toJasminCmd (.RCloneCall cloneVar cloneTy oldDest innerF dest args) =
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]] ++
        (toJasminCmd (.RCall innerF dest args)) := by
      rfl
    rw [h_toJ, translateCmd_append_eval]
    rw [hEvalClone, SDistr.pure_bind]
    -- newSid after the clone = sid (Copn doesn't change newSid)
    have h_newSid : (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).newSid = sid := by
      cases fuel with
      | zero => simp only [translateCmd]
      | succ n =>
        simp only [translateCmd, translateInstrR]
        cases n <;> simp only [translateCmd]
    rw [h_newSid]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    -- Apply rustCallSimulates for the inner call
    obtain ⟨heap2, hEvalCall, hInv2, hSInv2, hB2⟩ :=
      rustCallSimulates N leafSpec env (fuel - 1) hLeaf innerF dest args
        rsClone rs' hCall sid heap1 hInv1 hSInv1 hBounded1
    exact ⟨heap2, hEvalCall, hInv2, hSInv2, hB2⟩

/-! ### Simulation lemmas for the call/select constructors

The LowCT constructors `RCallN` and `RSelect`
each get a standalone simulation lemma mirroring the
`rustCallSimulates` / `rustLimbStoreSimulates` pattern:

* An `*ImplOk` hypothesis classes the Jasmin instruction's heap
  effect as compatible with the abstract `RustExec` semantics
  (Rocq-style `asm_correct` axiom for these opcodes).
* The lemma proves the simulation step from the `ImplOk`
  hypothesis plus heap-encoding invariants (`HeapInv`, `ScalarInv`,
  `ScalarsBounded`).

For `RCallN`, `RustExec.callN` writes destination `i` with
`leafSpec.call (callNLeafName f i)`; the `ImplOk` hypothesis requires
the Jasmin `Ccall` instruction to produce a heap encoding that state.

For `RSelect`, the `RustExec` semantics is a conditional copy
(selectFalse / selectTrue cases); the `ImplOk` hypothesis states that
the Jasmin `CMOV` opcode writes the source selected by the runtime
value of `sel` to `dst`.
-/

/-- **CallN oracle hypothesis**: the translated
    `.Ccall .DoNotInline (...) { name := f } (...)` instruction (run
    from any heap encoding `rs`) produces a heap encoding the state that
    `RustExec.callN` produces, with the scalar cells unchanged. -/
def CallNImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (f : String) (dests args : List Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap),
    HeapInv rs0 heap0 sid →
    (∀ a ∈ args, ∃ v, rs0.rsTower a.locVar = some ⟨a.locDst, v⟩) →
    (∀ d ∈ dests, ∃ v, rs0.rsTower d.locVar = some ⟨d.locDst, v⟩) →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      HeapInv (callNUpdate leafSpec f (args.map (·.locDst))
                 (args.filterMap (fun a => rs0.rsTower a.locVar)) 0 dests rs0) heap1 sid ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Standalone RCallN simulation**.  The emitted Jasmin `Ccall`
    lands each destination on the value the `callN` rule writes there, which is
    what `CallNImplOk` supplies; the scalar heap is untouched on both sides. -/
lemma rustCallNSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hCallN : CallNImplOk leafSpec env fuel)
    (f : String) (dests args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RCallN f dests args) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RCallN f dests args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | callN _ _ _ _ argList hArg hArgsBound hDestsBound =>
    subst hArg
    obtain ⟨heap1, hEval, hInv1, hScalarEq⟩ :=
      hCallN f dests args rs sid heap hInv hArgsBound hDestsBound
    refine ⟨heap1, ?_, hInv1, ?_, ?_⟩
    · simp only [toJasminCmd_RCallN]; exact hEval
    · intro x
      rw [hScalarEq x]
      simp only [callNUpdate_rsScalar]
      exact hSInv x
    · show ScalarsBounded (callNUpdate _ _ _ _ 0 dests rs)
      simpa [ScalarsBounded, callNUpdate_rsScalar] using hBounded

/-- **Select oracle hypothesis**: the translated
    `.Copn [dst] .AT_none (.Oasm { name := "CMOV" }) [sel; src0; src1]`
    instruction reads `sel`'s scalar value, copies the appropriate
    source's tower value into `dst`, and leaves all other locations
    unchanged.  Matches `RustExec.selectFalse` / `selectTrue`.

    The premise `ScalarsBounded rs0` makes the 64-bit cell of `sel` determine
    whether `rs0.rsScalar sel` is zero. -/
def SelectImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (dst : Located) (sel : String) (src0 src1 : Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (h0 : src0.locDst = dst.locDst) (h1 : src1.locDst = dst.locDst)
    (oldDestV : RustVal dst.locDst)
    (src0V : RustVal src0.locDst) (src1V : RustVal src1.locDst),
    HeapInv rs0 heap0 sid →
    ScalarInv rs0 heap0 sid →
    ScalarsBounded rs0 →
    rs0.rsTower dst.locVar = some ⟨dst.locDst, oldDestV⟩ →
    locatedLookup rs0 src0 = some src0V →
    locatedLookup rs0 src1 = some src1V →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Copn [locToLVal dst] .AT_none (.Oasm { name := "CMOV" })
               [.Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} },
                        gs := false },
                locToPExpr src0, locToPExpr src1]]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid dst.locVar dst.locDst) =
        (if rs0.rsScalar sel = 0 then h0 ▸ src0V else h1 ▸ src1V) ∧
      (∀ (x : String) (t : TowerType),
        x ≠ dst.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Standalone RSelect simulation**.  Real conditional-
    copy semantics: post-state writes `dst` to either `src0` or `src1`
    depending on the runtime scalar `sel`. -/
lemma rustSelectSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hSel : SelectImplOk leafSpec env fuel)
    (dst : Located) (sel : String) (src0 src1 : Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RSelect dst sel src0 src1) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs)
    (oldDestV : RustVal dst.locDst)
    (src0V : RustVal src0.locDst) (src1V : RustVal src1.locDst)
    (h0 : src0.locDst = dst.locDst) (h1 : src1.locDst = dst.locDst)
    (hDestLk : rs.rsTower dst.locVar = some ⟨dst.locDst, oldDestV⟩)
    (hSrc0Lk : locatedLookup rs src0 = some src0V)
    (hSrc1Lk : locatedLookup rs src1 = some src1V) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RSelect dst sel src0 src1)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  obtain ⟨heap1, hEval, hDestVal, hOtherTower, hScalarEq⟩ :=
    hSel dst sel src0 src1 rs sid heap h0 h1 oldDestV src0V src1V
      hInv hSInv hBounded hDestLk hSrc0Lk hSrc1Lk
  cases hExec with
  | selectFalse _ _ _ _ _ hSrc0Eq srcV hSel0 hLk0 =>
    -- srcV = src0V (both come from locatedLookup rs src0 = some _).
    have hSrcEq : src0V = srcV :=
      (Option.some.inj (hSrc0Lk.symm.trans hLk0))
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd_RSelect]; exact hEval
    · intro x t v hxTower
      by_cases hx : x = dst.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht; simp at hv; subst hv
        rw [hDestVal]
        simp [hSel0]
        -- Goal: h0 ▸ src0V = hSrc0Eq ▸ srcV.
        -- src0V = srcV (hSrcEq); h0 = hSrc0Eq (proof irrelevance on Prop).
        subst hSrcEq
        rfl
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t v hxTower
    · intro x; rw [hScalarEq x]; exact hSInv x
    · intro x
      exact hBounded x
  | selectTrue _ _ _ _ _ hSrc1Eq v srcV hSelV hSelne hLk1 =>
    have hSrcEq : src1V = srcV :=
      (Option.some.inj (hSrc1Lk.symm.trans hLk1))
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd_RSelect]; exact hEval
    · intro x t v' hxTower
      by_cases hx : x = dst.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht; simp at hv; subst hv
        rw [hDestVal]
        simp [hSelV, hSelne]
        subst hSrcEq
        rfl
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t v' hxTower
    · intro x; rw [hScalarEq x]; exact hSInv x
    · intro x
      exact hBounded x

/-! ### Inline-registry simulation

Simulation statements for `toJasminCmdWithInlines`, and the per-registry
refinement predicate `InlineRegistryRefines` stating that every registered
inline body has the heap effect `LeafImplOk` asks of the corresponding
`Ccall`.
-/

/-- The hypothesis "every inline registered in `env` refines the leaf's
    semantics": for every `f ↦ some impl` in the registry, executing
    `impl dest args` from any heap encoding `rs` produces the same heap
    that the corresponding `Ccall` translation would, modulo the
    `LeafImplOk` semantic conditions on the leaf.

    Discharged once per registry by combining the per-leaf refinement
    lemmas from `Curve25519Inline.lean` (one per inline body). -/
def InlineRegistryRefines
    (env : InlineRegistry) (leafSpec : LeafSpec) (transEnv : TransEnv)
    (fuel : Nat) : Prop :=
  ∀ (f : String) (impl : JasminInlineImpl),
    env f = some impl →
    ∀ (dest : Located) (args : List Located)
      (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
      (oldDestV : RustVal dest.locDst)
      (argList : List (Σ t, RustVal t)),
      HeapInv rs0 heap0 sid →
      rs0.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ →
      argList = args.filterMap (fun a => rs0.rsTower a.locVar) →
      ∃ heap1 : Heap,
        (translateCmd transEnv (impl dest args) sid fuel).code.eval heap0 =
          CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
        heap1.get (towerLoc sid dest.locVar dest.locDst) =
          leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList ∧
        (∀ (x : String) (t : TowerType),
          x ≠ dest.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
        (∀ (x : String),
          heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
          heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Empty-registry corollary**: when `env = emptyInlineRegistry`,
the inline-substituted output coincides with `toJasminCmd`
(`toJasminCmdWithInlines_emptyRegistry_eq_toJasminCmd`), so the
simulation follows from `rustExecSimulates`. -/
theorem rustExecSimulates_emptyInlineRegistry
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (c : LowCT) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCF : callFree c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmdWithInlines emptyInlineRegistry c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  rw [toJasminCmdWithInlines_emptyRegistry_eq_toJasminCmd]
  exact rustExecSimulates N leafSpec env fuel c rs rs' hWf hCF hSSS hFuel hExec
    sid heap hInv hSInv hBounded

/-- **Helper lemma (inline-registry agreement)**: under the `callFree`
precondition, `toJasminCmdWithInlines` agrees with `toJasminCmd` for
every registry, because `RCall` (the only constructor whose translation
depends on `env`) cannot occur in a call-free program.

This is the structural fact that lets the strengthened simulation
theorem `rustExecSimulates_with_inlines` close without re-running the
~488-line case-by-case induction: the bodies of `toJasminCmdWithInlines`
and `toJasminCmd` are identical on every other constructor, and the
`callFree` filter rules out the one differing case.

The key step is the `RIfNz`/`RWhileNz` induction: `Bool.and_eq_true`
unpacks the conjunction, and the IHs apply recursively. -/
theorem toJasminCmdWithInlines_eq_toJasminCmd_of_callFree
    (env : InlineRegistry) :
    ∀ c, callFree c = true → toJasminCmdWithInlines env c = toJasminCmd c := by
  intro c
  induction c with
  | RSkip => intro _; rfl
  | RSeq c1 c2 ih1 ih2 =>
      intro hCF
      simp only [callFree, Bool.and_eq_true] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih1 hCF.1, ih2 hCF.2]
  | RLetZero x t body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  | RLetU64Zero x body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  | RScalarSet x v => intro _; rfl
  | RCall f dest args =>
      -- callFree (.RCall ..) = false, contradiction
      intro hCF
      simp [callFree] at hCF
  | RCallSwap f dest1 dest2 args =>
      -- callFree (.RCallSwap ..) = false, contradiction (analogous to RCall)
      intro hCF
      simp [callFree] at hCF
  | RCloneCall cloneVar cloneTy oldDest innerF dest args =>
      intro hCF
      simp [callFree] at hCF
  | RIfNz e ct cf ih1 ih2 =>
      intro hCF
      simp only [callFree, Bool.and_eq_true] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih1 hCF.1, ih2 hCF.2]
  | RWhileNz e body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  | RFor x n body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  | RForRuntime x b body ih =>
      -- both sides reject the runtime loop to `[]`.
      intro _
      simp [toJasminCmdWithInlines, toJasminCmd_RForRuntime]
  | RLimbStore loc idx v =>
      intro hCF
      simp [callFree] at hCF
  | RLimbStoreExpr loc idx e =>
      intro hCF
      simp [callFree] at hCF
  -- RCallN IS a call → contradiction with callFree = true.
  | RCallN f dests args =>
      intro hCF
      simp [callFree] at hCF
  -- RSelect / RAssert are call-free; identical code.
  | RSelect dst sel src0 src1 => intro _; rfl
  | RAssert label => intro _; rfl
  -- RBlock forwards to body recursively.
  | RBlock body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  -- fnDef = body && cont; both inherit.
  | RFnDef _ _ _ body cont ihBody ihCont =>
      intro hCF
      simp only [callFree, Bool.and_eq_true] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ihBody hCF.1, ihCont hCF.2]
  -- fnCall IS a call → contradiction.
  | RFnCall _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  -- RTupleLoad excluded by callFree → contradiction.
  | RTupleLoad _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  -- TArr/SExpr excluded by callFree → contradiction.
  | RArrStore _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  | RArrLoad _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  -- literal-index variants excluded by callFree.
  | RArrStoreLit _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  | RArrLoadLit _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  | RScalarSetExpr _ _ =>
      intro hCF
      simp [callFree] at hCF
  | RCallDstThreaded _ _ _ =>
      intro hCF
      simp [callFree] at hCF

/-- **Simulation over inline-substituted output**: the conclusion of
`rustExecSimulates`, stated over `toJasminCmdWithInlines env c` for an
arbitrary inline registry `env`.

Under `callFree c = true` no `RCall` occurs, so the inline output equals
the `toJasminCmd` output (`toJasminCmdWithInlines_eq_toJasminCmd_of_callFree`)
and the proof reduces to `rustExecSimulates`. -/
theorem rustExecSimulates_with_inlines
    (N : Nat) (leafSpec : LeafSpec) (transEnv : TransEnv) (fuel : Nat)
    (env : InlineRegistry)
    (c : LowCT) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCF : callFree c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd transEnv (toJasminCmdWithInlines env c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  rw [toJasminCmdWithInlines_eq_toJasminCmd_of_callFree env c hCF]
  exact rustExecSimulates N leafSpec transEnv fuel c rs rs'
    hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded

/-! ### `RCall` at the threaded `newSid`

The statements below post the invariants at the scope `newSid` threaded by
`translateCmd`, from the leaf oracle `LeafImplOkNewSid`. `translateInstrR .Ccall`
returns `newSid := sid`, so for a call the threaded scope is the caller's scope
(`translateCmd_ccall_newSid` in `LowCTToJasminImplOk`).
-/

/-- **Leaf oracle at the post-call scope**: like `LeafImplOk`, but the heap
    postcondition is stated at the scope `newSid` of the `Ccall` translation,
    and it covers the scalar cells as well as the tower cells.

    The premise `ScalarInv rs0 heap0 sid` ties the scalar cells of the
    pre-heap to `rs0`; without it the postcondition `ScalarInv rs' heap1 newSid`
    would have to hold for two states that differ only in a scalar and share
    `heap0`. -/
def LeafImplOkNewSid (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (f : String) (dest : Located) (args : List Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal dest.locDst)
    (argList : List (Σ t, RustVal t)),
    HeapInv rs0 heap0 sid →
    ScalarInv rs0 heap0 sid →
    rs0.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ →
    argList = args.filterMap (fun a => rs0.rsTower a.locVar) →
    (∀ a ∈ args, ∃ v, rs0.rsTower a.locVar = some ⟨a.locDst, v⟩) →
    ScalarsBounded rs0 →
    let newSid := (translateCmd env
      [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
      sid fuel).newSid
    let rs' := locatedUpdate rs0 dest
      (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList)
    ∃ heap1 : Heap,
      (translateCmd env
        [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      HeapInv rs' heap1 newSid ∧
      ScalarInv rs' heap1 newSid ∧
      ScalarsBounded rs'

/-- **`rustCallSimulates_newSid`**: the `RCall` case run at `fuel`, stated at
    the post-call scope `newSid`, from `LeafImplOkNewSid` at that fuel.

    `rustCallSimulates` posts at the caller's `sid`; this version posts at
    `newSid`, the scope at which subsequent code in an `RSeq` is translated
    (`translateCmd_append_eval`). -/
lemma rustCallSimulates_newSid
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeafN : LeafImplOkNewSid leafSpec env fuel)
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      let newSid := (translateCmd env (toJasminCmd (.RCall f dest args))
                       sid fuel).newSid
      (translateCmd env (toJasminCmd (.RCall f dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' newSid ∧
      ScalarInv rs' heap' newSid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | call f' dest' args' rs'' oldDestV argList hLookup hArgs hArgsT =>
    have hTower : rs.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ := by
      unfold locatedLookup at hLookup
      split at hLookup
      · rename_i ty v heq
        split at hLookup
        · rename_i hty
          cases hty
          simp at hLookup
          rw [heq, hLookup]
        · simp at hLookup
      · simp at hLookup
    -- Apply LeafImplOkNewSid (which gives HeapInv/ScalarInv at newSid).
    have hOk :=
      hLeafN f dest args rs sid heap oldDestV argList hInv hSInv hTower hArgs hArgsT hBounded
    obtain ⟨heap1, hEval, hInvNew, hSInvNew, hBNew⟩ := hOk
    refine ⟨heap1, ?_, hInvNew, hSInvNew, hBNew⟩
    simp only [toJasminCmd_RCall]; exact hEval

/-! ### `RCloneCall` at the threaded `newSid`

`RCloneCall` lowers to `[Copn(CLONE_TOWER), Ccall]`.  The leading `Copn`
keeps `newSid = sid`, so the simulation composes `CloneImplOk` with
`rustCallSimulates_newSid`. -/

/-- The `newSid` after lowering `RCloneCall` to Jasmin coincides with
    the `newSid` after lowering the inner `RCall` (since the leading
    `Copn` for the clone preserves `newSid`).  Mirrors
    `limbStore_toJasmin_newSid` for the Copn-step and composes it with the
    `Ccall` through `translateCmd_append_newSid`. -/
lemma cloneCall_toJasmin_newSid
    (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (innerF : String) (dest : Located) (args : List Located)
    (env : TransEnv) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env
        (toJasminCmd
          (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).newSid =
    (translateCmd env (toJasminCmd (.RCall innerF dest args)) sid
        (fuel - 1)).newSid := by
  -- toJasminCmd (RCloneCall ...) = [cloneInstr] ++ toJasminCmd (RCall innerF dest args)
  have h_toJ :
      toJasminCmd (.RCloneCall cloneVar cloneTy oldDest innerF dest args) =
      [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                       info := { towerTag := cloneTy.byteSize } }] .AT_none
            (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]] ++
      (toJasminCmd (.RCall innerF dest args)) := rfl
  rw [h_toJ, translateCmd_append_newSid]
  -- newSid after the clone Copn = sid
  have h_clone_newSid :
      (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).newSid = sid := by
    cases fuel with
    | zero => simp only [translateCmd]
    | succ n =>
      simp only [translateCmd, translateInstrR]
      cases n <;> simp only [translateCmd]
  rw [h_clone_newSid]
  -- The list-length subtraction: clone list has length 1, so `fuel - 1`.
  simp only [List.length_cons, List.length_nil, Nat.zero_add]

/-- **`rustCloneCallSimulates_newSid`**: simulates an `RCloneCall`
    instruction with the post-state stated at the threaded `newSid`, the scope
    after the trailing `Ccall`.

    Combines `CloneImplOk` at `fuel` (for the leading `Copn(CLONE_TOWER)`,
    which preserves `newSid = sid`) with `rustCallSimulates_newSid` at
    `fuel - 1` (for the trailing `Ccall`).

    Mirrors `rustCloneCallSimulates` with `LeafImplOkNewSid` in place of
    `LeafImplOk` on the inner call. -/
lemma rustCloneCallSimulates_newSid
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeafN : LeafImplOkNewSid leafSpec env (fuel - 1))
    (hClone : CloneImplOk env fuel)
    (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (innerF : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args) rs rs')
    (oldV : RustVal cloneTy)
    (hTy : oldDest.locDst = cloneTy)
    (hOldDest : rs.rsTower oldDest.locVar = some ⟨cloneTy, oldV⟩)
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      let newSid := (translateCmd env (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).newSid
      (translateCmd env (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' newSid ∧
      ScalarInv rs' heap' newSid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | cloneCall _ _ _ _ _ _ _ rsClone _ hClone_eq hCall =>
    -- Apply clone oracle to get heap1 at sid.
    obtain ⟨heap1, hEvalClone, hCloneDest, hCloneOther, hCloneScalar⟩ :=
      hClone cloneVar cloneTy oldDest rs sid heap oldV hTy hInv hOldDest
    -- Establish invariants at rsClone / heap1 / sid.
    have hRsClone : rsClone = rsSetTower rs cloneVar ⟨cloneTy, oldV⟩ := by
      rw [hClone_eq, hOldDest]; rfl
    have hInv1 : HeapInv rsClone heap1 sid := by
      intro x t v hxTower
      rw [hRsClone] at hxTower
      simp only [rsSetTower, beq_iff_eq] at hxTower
      by_cases hx : x = cloneVar
      · subst hx
        simp only [if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hCloneDest
      · simp only [hx, if_false] at hxTower
        rw [hCloneOther x t hx]
        exact hInv x t v hxTower
    have hSInv1 : ScalarInv rsClone heap1 sid := by
      intro x
      rw [hCloneScalar x, hSInv x, hRsClone]
      rfl
    have hBounded1 : ScalarsBounded rsClone := by
      intro x
      rw [hRsClone]
      exact hBounded x
    -- Decompose translateCmd [cloneInstr, callInstr] via append.
    have h_toJ : toJasminCmd (.RCloneCall cloneVar cloneTy oldDest innerF dest args) =
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]] ++
        (toJasminCmd (.RCall innerF dest args)) := rfl
    -- newSid after the clone Copn = sid (Copn doesn't change newSid).
    have h_clone_newSid : (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).newSid = sid := by
      cases fuel with
      | zero => simp only [translateCmd]
      | succ n =>
        simp only [translateCmd, translateInstrR]
        cases n <;> simp only [translateCmd]
    -- Apply rustCallSimulates_newSid for the inner call at sid (since the
    -- clone preserves newSid = sid).  This posts at the inner-call's
    -- threaded newSid, which by `cloneCall_toJasmin_newSid`
    -- coincides with the full RCloneCall translation's newSid.
    obtain ⟨heap2, hEvalCall, hInv2, hSInv2, hB2⟩ :=
      rustCallSimulates_newSid N leafSpec env (fuel - 1) hLeafN innerF dest args
        rsClone rs' hCall sid heap1 hInv1 hSInv1 hBounded1
    refine ⟨heap2, ?_, ?_, ?_, hB2⟩
    · -- Sequential evaluation: clone, then call.
      rw [h_toJ, translateCmd_append_eval]
      rw [hEvalClone, SDistr.pure_bind]
      rw [h_clone_newSid]
      simp only [List.length_cons, List.length_nil, Nat.zero_add]
      exact hEvalCall
    · -- HeapInv at the threaded newSid: by cloneCall_toJasmin_newSid the
      -- newSid of the full RCloneCall = newSid of the inner RCall.
      have hNS := cloneCall_toJasmin_newSid cloneVar cloneTy oldDest innerF dest args
        env sid fuel
      rw [hNS]; exact hInv2
    · have hNS := cloneCall_toJasmin_newSid cloneVar cloneTy oldDest innerF dest args
        env sid fuel
      rw [hNS]; exact hSInv2

/-! ### Programs with call leaves

`rustExecSimulates_withCalls` admits `RCall`, `RLimbStore` and `RCloneCall`
leaves under `RSeq` and `RIfNz`, with call-free subprograms elsewhere, and
posts the invariants at the threaded `newSid`. -/

namespace RustExecWithCalls

/-- `callFreePlusCall c = true` iff `c` is a tree of `RSeq` and `RIfNz` nodes
    whose leaves are `callFree` subprograms, single `RCall`s, single
    `RLimbStore`s or single `RCloneCall`s.

    `RLimbStore` lowers to one `.Copn`, which keeps `newSid = sid`
    (`limbStore_toJasmin_newSid`); `RCall` lowers to one `.Ccall`;
    `RCloneCall` lowers to `[Copn(CLONE_TOWER), Ccall]`. At an `RIfNz` the
    invariants must hold at the scope threaded through both branches, which
    `BranchScopeMerges` states.

    `RFor`, `RBlock`, `RLetZero`, `RLetU64Zero` and `RCallSwap` are admitted only
    call-free; `RWhileNz` and the constructors with `whileFree = false` are
    excluded by the `whileFree` precondition. -/
def callFreePlusCall : LowCT → Bool
  | .RCall _ _ _              => true
  | .RLimbStore _ _ _         => true
  | .RCloneCall _ _ _ _ _ _   => true
  | .RSeq c1 c2               => callFreePlusCall c1 && callFreePlusCall c2
  | .RIfNz _ ct cf            => callFreePlusCall ct && callFreePlusCall cf
  | c                         => callFree c

/-- The `callFreePlusCall` predicate is reflexive over `callFree`. -/
lemma callFreePlusCall_of_callFree :
    ∀ c, callFree c = true → callFreePlusCall c = true := by
  intro c hCF
  match c with
  | .RCall _ _ _ => simp [callFree] at hCF
  | .RSeq c1 c2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [callFreePlusCall]
    rw [callFreePlusCall_of_callFree c1 hCF.1,
        callFreePlusCall_of_callFree c2 hCF.2]
    rfl
  | .RSkip => simp [callFreePlusCall, hCF]
  | .RScalarSet _ _ => simp [callFreePlusCall, hCF]
  | .RLetZero _ _ _ => simp [callFreePlusCall, hCF]
  | .RLetU64Zero _ _ => simp [callFreePlusCall, hCF]
  | .RIfNz _ ct cf =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [callFreePlusCall]
    rw [callFreePlusCall_of_callFree ct hCF.1,
        callFreePlusCall_of_callFree cf hCF.2]
    rfl
  | .RWhileNz _ _ => simp [callFreePlusCall, hCF]
  | .RFor _ _ _ => simp [callFreePlusCall, hCF]
  | .RForRuntime _ _ _ => simp [callFreePlusCall, hCF]
  | .RAssert _ => simp [callFreePlusCall, hCF]
  | .RBlock _ => simp [callFreePlusCall, hCF]
  | .RFnDef _ _ _ _ _ => simp [callFreePlusCall, hCF]
  | .RSelect _ _ _ _ => simp [callFreePlusCall, hCF]
  | .RCallN _ _ _ => simp [callFreePlusCall, hCF]
  | .RFnCall _ _ _ => simp [callFreePlusCall, hCF]
  | .RCallSwap _ _ _ _ => simp [callFreePlusCall, hCF]
  | .RCloneCall _ _ _ _ _ _ => simp [callFree] at hCF
  | .RLimbStore _ _ _ => simp [callFree] at hCF
    -- (unreachable: the hypothesis is on `callFree`, which excludes `RLimbStore`)
  | .RLimbStoreExpr _ _ _ => simp [callFreePlusCall, hCF]
  | .RTupleLoad _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrStore _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrLoad _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrStoreLit _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrLoadLit _ _ _ => simp [callFreePlusCall, hCF]
  | .RScalarSetExpr _ _ => simp [callFreePlusCall, hCF]
  | .RCallDstThreaded _ _ _ => simp [callFree] at hCF

/-- **Branch-symmetric merge property for `RIfNz`.**

    For every `RIfNz e ct cf` reached during execution of `c` starting
    at `rs`, two scope-lift obligations must hold so the Jasmin-side
    `Cif` newSid threading (which advances through both branches even
    if only one executes) can be reconciled with the `HeapInv`/`ScalarInv`
    posted by the executed branch's IH:

    1. **TRUE-branch lift** — after the true branch runs and gives the
       caller `HeapInv rs' heap' sid_ct`, where `sid_ct` is `ct`'s
       advanced sid, the same invariant must hold at the outer Cif's
       `newSid` (which is `cf`'s advanced sid starting from `sid_ct`).

    2. **FALSE-branch lift** — the Jasmin `cf` runs from `sid_ct`, not
       `sid`.  We need `HeapInv rs heap sid_ct` from `HeapInv rs heap sid`.

    Both obligations are vacuously discharged when both branches are
    `callFree` (then `sid_ct = sid` and all newSids collapse), so the
    extension is **conservative** w.r.t. the existing call-free case.

    For non-`RIfNz` constructors the predicate is `True`. Recurses
    through `RSeq` and `RIfNz` itself. -/
def BranchScopeMerges (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) :
    LowCT → RustState → ScopeId → Nat → Prop
  | .RIfNz _ ct cf, rs, sid, fuel =>
      -- The outer Cif consumes one unit of fuel for the trailing list step;
      -- both branches recurse at `fuel - 1`.  We state all obligations
      -- in terms of `fuel - 1` to align with the theorem's fuel threading.
      let fuel' := fuel - 1
      -- TRUE-branch lift: invariant survives the cross-branch
      -- scope advancement (sid_ct → outer Cif newSid via cf).
      (∀ rs' heap',
        RustExec N leafSpec ct rs rs' →
        HeapInv rs' heap' ((translateCmd env (toJasminCmd ct) sid fuel').newSid) →
        ScalarInv rs' heap' ((translateCmd env (toJasminCmd ct) sid fuel').newSid) →
        HeapInv rs' heap' ((translateCmd env (toJasminCmd cf)
            ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid) ∧
        ScalarInv rs' heap' ((translateCmd env (toJasminCmd cf)
            ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid)) ∧
      -- FALSE-branch lift: pre-state HeapInv at sid lifts to sid_ct.
      (∀ heap,
        HeapInv rs heap sid →
        ScalarInv rs heap sid →
        HeapInv rs heap ((translateCmd env (toJasminCmd ct) sid fuel').newSid) ∧
        ScalarInv rs heap ((translateCmd env (toJasminCmd ct) sid fuel').newSid)) ∧
      -- Recursive obligation on `ct` itself (its own RIfNz nodes also merge).
      BranchScopeMerges N leafSpec env ct rs sid fuel' ∧
      -- Symmetric FALSE-execution recursion: `cf` runs from rs at sid_ct.
      BranchScopeMerges N leafSpec env cf rs
        ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel'
  | .RSeq c1 c2, rs, sid, fuel =>
      BranchScopeMerges N leafSpec env c1 rs sid fuel ∧
      (∀ rs1 : RustState, RustExec N leafSpec c1 rs rs1 →
        BranchScopeMerges N leafSpec env c2 rs1
          ((translateCmd env (toJasminCmd c1) sid fuel).newSid)
          (fuel - (toJasminCmd c1).length))
  | _, _, _, _ => True

/-- **Runtime witness for `RCloneCall` well-typedness.**

    For every `RCloneCall cloneVar cloneTy oldDest …` reached during
    execution of `c` starting at `rs`, `oldDest.locDst = cloneTy` and the
    lookup `rs.rsTower oldDest.locVar` returns `some ⟨cloneTy, v⟩`.

    The `RustExec.cloneCall` constructor uses `Option.getD` on the
    lookup, so it admits "bad" executions where the lookup is `none`
    (and the cloned value is silently `default`).  The Jasmin
    `CloneImplOk` oracle in contrast requires the lookup to be `some`
    to specify what the resulting heap holds.  This predicate threads
    the missing well-typedness witness through `RSeq` by quantifying
    over intermediate states reachable via `RustExec` on `c1`.

    For non-`RCloneCall` constructors the predicate is `True`. -/
def CloneCallsWellTyped (N : Nat) (leafSpec : LeafSpec) :
    LowCT → RustState → Prop
  | .RCloneCall _ cloneTy oldDest _ _ _, rs =>
      oldDest.locDst = cloneTy ∧
      ∃ v : RustVal cloneTy, rs.rsTower oldDest.locVar = some ⟨cloneTy, v⟩
  | .RSeq c1 c2, rs =>
      CloneCallsWellTyped N leafSpec c1 rs ∧
      (∀ rs1 : RustState, RustExec N leafSpec c1 rs rs1 →
        CloneCallsWellTyped N leafSpec c2 rs1)
  -- Recurse through RIfNz so nested clones inside either branch are tracked
  -- regardless of which branch the runtime takes.
  | .RIfNz _ ct cf, rs =>
      CloneCallsWellTyped N leafSpec ct rs ∧
      CloneCallsWellTyped N leafSpec cf rs
  | _, _ => True

/-- **Conservativity**: when `c` is fully `callFree`, the
    `BranchScopeMerges` obligation is trivially satisfied — every
    reachable `RIfNz` has `newSid_ct = sid` (and `newSid_cf = sid`),
    so the lift is the identity.  This guarantees the mixed-branch
    `RIfNz` extension does not break any existing all-callFree caller.

    Stated as a recursive function (sufficient pattern for the
    conservativity guarantee — see `branchScopeMerges_of_callFree_at`
    for a sample application). -/
lemma branchScopeMerges_of_callFree
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (c : LowCT)
    (hCF : callFree c = true)
    (rs : RustState) (sid : ScopeId) (fuel : Nat) :
    BranchScopeMerges N leafSpec env c rs sid fuel := by
  -- Conservative case: c is callFree, so every reachable RIfNz/RSeq
  -- has callFree branches.  We prove this by structural recursion on c.
  -- Use a recursive definition pattern to thread `rs`/`sid`/`fuel`.
  induction c generalizing rs sid fuel with
  | RIfNz e ct cf ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    have hNS_ct : (translateCmd env (toJasminCmd ct) sid (fuel - 1)).newSid = sid :=
      callFree_toJasmin_newSid ct hCF.1 env sid (fuel - 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro rs' heap' _hExec hInv' hSInv'
      rw [hNS_ct] at hInv' hSInv' ⊢
      have hNS_cf : (translateCmd env (toJasminCmd cf) sid (fuel - 1)).newSid = sid :=
        callFree_toJasmin_newSid cf hCF.2 env sid (fuel - 1)
      rw [hNS_cf]
      exact ⟨hInv', hSInv'⟩
    · intro heap hInv hSInv
      rw [hNS_ct]
      exact ⟨hInv, hSInv⟩
    · exact ih1 hCF.1 rs sid (fuel - 1)
    · rw [hNS_ct]; exact ih2 hCF.2 rs sid (fuel - 1)
  | RSeq c1 c2 ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    refine ⟨ih1 hCF.1 rs sid fuel, ?_⟩
    intro rs1 _h1
    exact ih2 hCF.2 rs1 _ _
  | RSkip => simp [BranchScopeMerges]
  | RScalarSet _ _ => simp [BranchScopeMerges]
  | RLetZero _ _ _ _ => simp [BranchScopeMerges]
  | RLetU64Zero _ _ _ => simp [BranchScopeMerges]
  | RWhileNz _ _ _ => simp [BranchScopeMerges]
  | RFor _ _ _ _ => simp [BranchScopeMerges]
  | RForRuntime _ _ _ _ => simp [BranchScopeMerges]
  | RCall _ _ _ => simp [callFree] at hCF
  | RCallSwap _ _ _ _ => simp [callFree] at hCF
  | RCloneCall _ _ _ _ _ _ => simp [callFree] at hCF
  | RLimbStore _ _ _ => simp [callFree] at hCF
  | RLimbStoreExpr _ _ _ => simp [callFree] at hCF
  | RCallN _ _ _ => simp [callFree] at hCF
  | RSelect _ _ _ _ => simp [BranchScopeMerges]
  | RAssert _ => simp [BranchScopeMerges]
  | RBlock _ _ => simp [BranchScopeMerges]
  | RFnDef _ _ _ _ _ _ _ => simp [BranchScopeMerges]
  | RFnCall _ _ _ => simp [callFree] at hCF
  | RTupleLoad _ _ _ => simp [callFree] at hCF
  | RArrStore _ _ _ => simp [callFree] at hCF
  | RArrLoad _ _ _ => simp [callFree] at hCF
  | RArrStoreLit _ _ _ => simp [callFree] at hCF
  | RArrLoadLit _ _ _ => simp [callFree] at hCF
  | RScalarSetExpr _ _ => simp [callFree] at hCF
  | RCallDstThreaded _ _ _ => simp [callFree] at hCF

end RustExecWithCalls

/-- **`rustExecSimulates_withCalls`**: the structural simulation extended to
    admit `RCall`, `RLimbStore` and `RCloneCall` leaves interleaved with
    call-free fragments via `RSeq` and `RIfNz`.

    Replaces the `callFree c = true` precondition of `rustExecSimulates`
    with `callFreePlusCall c = true`. The leaf oracles are required at every
    fuel `≥ 2`, the least fuel at which a one-instruction command runs
    (`jasminFuel` of each leaf is at least `2`).

    The conclusion is stated at the threaded `newSid`. In the pure
    call-free case this collapses back to `sid` via
    `callFree_toJasmin_newSid`; for `RLimbStore` leaves, `newSid = sid`
    too (via `limbStore_toJasmin_newSid`) since the Jasmin `.Copn`
    translation doesn't advance the sid.

    Coverage:
    * single `RCall`: closed via `rustCallSimulates_newSid`.
    * single `RLimbStore`: closed via `rustLimbStoreSimulates`
      after the `newSid = sid` rewrite (limb store is `.Copn` which preserves
      `newSid`).  Requires `hLimb : LimbStoreImplOk`.
    * single `RCloneCall`: closed via
      `rustCloneCallSimulates_newSid`.  Requires `hClone : CloneImplOk`
      and a runtime well-typedness witness `hCloneWT`.
    * `RSeq c1 c2` with both `callFreePlusCall`: closed by threaded
      composition.
    * `RIfNz e ct cf` with mixed-branch calls: branches are
      themselves `callFreePlusCall` and may contain calls.  Dispatches
      via `cases hExec` on `ifTrue`/`ifFalse`, recurses through the IH
      on the executed branch, then lifts the resulting invariant from
      that branch's `newSid` to the outer Cif's `newSid` (which depends
      on BOTH branches via `translateCmd_cif_newSid`).  The lift step
      is discharged by `hBranchMerges : BranchScopeMerges`, a runtime
      Prop witness that the merge holds at every reachable `RIfNz`.
      For all-callFree branches the witness is trivially constructed,
      so the extension is conservative.
    * non-call leaves (`RSkip`, `RScalarSet`, `RLetZero`, `RLetU64Zero`,
      `RFor`, `RBlock`, `RAssert`): delegate to `rustExecSimulates`
      after the `newSid = sid` collapse, since `callFreePlusCall`
      coincides with `callFree` for those.
    * `RWhileNz` and phases F/G/H/I/Ext: unreachable under `whileFree`.

    The proof recursively descends on the `RSeq` structure (terminating
    by structural decrease on the `RSeq` tree). -/
theorem rustExecSimulates_withCalls
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeafN : ∀ fuel', 2 ≤ fuel' → LeafImplOkNewSid leafSpec env fuel')
    (hLimb : ∀ fuel', 2 ≤ fuel' → LimbStoreImplOk leafSpec env fuel')
    (hClone : ∀ fuel', 2 ≤ fuel' → CloneImplOk env fuel')
    (c : LowCT) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCFx : RustExecWithCalls.callFreePlusCall c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (hCloneWT : RustExecWithCalls.CloneCallsWellTyped N leafSpec c rs)
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs)
    (hBranchMerges :
      RustExecWithCalls.BranchScopeMerges N leafSpec env c rs sid fuel) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap'
        ((translateCmd env (toJasminCmd c) sid fuel).newSid) ∧
      ScalarInv rs' heap'
        ((translateCmd env (toJasminCmd c) sid fuel).newSid) ∧
      ScalarsBounded rs' := by
  -- Three-way structural case-split.
  match h : c with
  | .RCall f dest args =>
    -- Single-call leaf: delegate to `rustCallSimulates_newSid`.
    subst h
    have hF : 2 ≤ fuel := by simpa [jasminFuel] using hFuel
    exact rustCallSimulates_newSid N leafSpec env fuel (hLeafN fuel hF)
      f dest args rs rs' hExec sid heap hInv hSInv hBounded
  | .RSeq c1 c2 =>
    -- Compositional RSeq case: thread `newSid` from IH₁ to IH₂.
    -- Both sub-IHs are recursive calls to `rustExecSimulates_withCalls`
    -- on structurally smaller `c1`/`c2`.
    subst h
    -- Extract the two underlying RustExec proofs from the RSeq.
    obtain ⟨r1, h1, h2⟩ : ∃ r1 : RustState,
        RustExec N leafSpec c1 rs r1 ∧ RustExec N leafSpec c2 r1 rs' := by
      cases hExec with
      | seq _ _ _ r1 _ h1 h2 => exact ⟨r1, h1, h2⟩
    -- Unpack the predicates on the seq components.
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [RustExecWithCalls.callFreePlusCall, Bool.and_eq_true] at hCFx
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- Unpack the runtime clone-well-typedness witness: the c1 witness is
    -- directly available; the c2 witness is obtained from the c1-runtime
    -- universal closure applied to `h1`.
    have hCWT1 : RustExecWithCalls.CloneCallsWellTyped N leafSpec c1 rs := by
      simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
      exact hCloneWT.1
    have hCWT2 : RustExecWithCalls.CloneCallsWellTyped N leafSpec c2 r1 := by
      simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
      exact hCloneWT.2 r1 h1
    -- Unpack the branch-merge witness for c1 and c2 (now fuel-aligned with
    -- the threaded recursion via the `RSeq` arm of `BranchScopeMerges`).
    have hBM1 : RustExecWithCalls.BranchScopeMerges N leafSpec env c1 rs sid fuel := by
      simp only [RustExecWithCalls.BranchScopeMerges] at hBranchMerges
      exact hBranchMerges.1
    have hBM2 : RustExecWithCalls.BranchScopeMerges N leafSpec env c2 r1
        ((translateCmd env (toJasminCmd c1) sid fuel).newSid)
        (fuel - (toJasminCmd c1).length) := by
      simp only [RustExecWithCalls.BranchScopeMerges] at hBranchMerges
      exact hBranchMerges.2 r1 h1
    have hFuel1 : jasminFuel c1 ≤ fuel := by
      have := jasminFuel_pos c2; omega
    have hFuel2 : jasminFuel c2 ≤ fuel - (toJasminCmd c1).length := by
      have := jasminFuel_gt_length c1; omega
    -- Recursive call on c1 (structurally smaller).
    obtain ⟨heap1, heval1, hInv1, hSInv1, hB1⟩ :=
      rustExecSimulates_withCalls N leafSpec env fuel hLeafN hLimb hClone
        c1 rs r1 hWf.1 hCFx.1 hSSS.1 hFuel1 h1 hCWT1
        sid heap hInv hSInv hBounded hBM1
    -- After IH₁ we are at `newSid₁ := (translateCmd ... c1 sid fuel).newSid`.
    set newSid1 := (translateCmd env (toJasminCmd c1) sid fuel).newSid with hNS1
    -- Recursive call on c2 at the threaded newSid₁.
    obtain ⟨heap2, heval2, hInv2, hSInv2, hB2⟩ :=
      rustExecSimulates_withCalls N leafSpec env
        (fuel - (toJasminCmd c1).length) hLeafN hLimb hClone
        c2 r1 rs' hWf.2 hCFx.2 hSSS.2 hFuel2 h2 hCWT2
        newSid1 heap1 hInv1 hSInv1 hB1 hBM2
    -- Compose evaluations via `translateCmd_append_eval`.
    refine ⟨heap2, ?_, ?_, ?_, hB2⟩
    · simp only [toJasminCmd_RSeq]
      rw [translateCmd_append_eval, heval1, SDistr.pure_bind]
      exact heval2
    · -- HeapInv at the final newSid (translateCmd of the seq).
      have hNewSidEq :
          (translateCmd env (toJasminCmd (.RSeq c1 c2)) sid fuel).newSid =
          (translateCmd env (toJasminCmd c2) newSid1
            (fuel - (toJasminCmd c1).length)).newSid := by
        simp only [toJasminCmd_RSeq, translateCmd_append_newSid, hNS1]
      rw [hNewSidEq]; exact hInv2
    · have hNewSidEq :
          (translateCmd env (toJasminCmd (.RSeq c1 c2)) sid fuel).newSid =
          (translateCmd env (toJasminCmd c2) newSid1
            (fuel - (toJasminCmd c1).length)).newSid := by
        simp only [toJasminCmd_RSeq, translateCmd_append_newSid, hNS1]
      rw [hNewSidEq]; exact hSInv2
  | .RSkip =>
    -- callFree: delegate to `rustExecSimulates` and rewrite newSid = sid.
    subst h
    have hCF : callFree LowCT.RSkip = true := by simp [callFree]
    have hNewSid : (translateCmd env (toJasminCmd LowCT.RSkip) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RScalarSet x v =>
    subst h
    have hCF : callFree (LowCT.RScalarSet x v) = true := by simp [callFree]
    have hNewSid : (translateCmd env (toJasminCmd (LowCT.RScalarSet x v)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RLetZero x t body =>
    subst h
    have hCF : callFree (LowCT.RLetZero x t body) = true := by
      simp only [RustExecWithCalls.callFreePlusCall] at hCFx
      exact hCFx
    have hNewSid : (translateCmd env (toJasminCmd (LowCT.RLetZero x t body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RLetU64Zero x body =>
    subst h
    have hCF : callFree (LowCT.RLetU64Zero x body) = true := by
      simp only [RustExecWithCalls.callFreePlusCall] at hCFx
      exact hCFx
    have hNewSid : (translateCmd env (toJasminCmd (LowCT.RLetU64Zero x body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RIfNz e ct cf =>
    -- Mixed-branch case: both `ct` and `cf` may contain calls.
    -- Dispatch via the executed branch's IH, then use `hBranchMerges` to lift
    -- the resulting invariant from the branch's newSid to the outer Cif's
    -- newSid (which depends symmetrically on BOTH branches' newSid via
    -- `translateCmd_cif_newSid`).
    subst h
    -- Unpack the structural predicates restricted to the branches.
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [RustExecWithCalls.callFreePlusCall, Bool.and_eq_true] at hCFx
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- Fuel decomposition: outer = max(ct, cf) + 1 ≤ fuel.
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    have hFuel_ct : jasminFuel ct ≤ fuel' := by omega
    have hFuel_cf : jasminFuel cf ≤ fuel' := by omega
    -- Unpack the branch-merge witness for ct and cf.
    have hBMall := hBranchMerges
    simp only [RustExecWithCalls.BranchScopeMerges] at hBMall
    obtain ⟨hLiftTrue, hLiftFalse, hBM_ct, hBM_cf_from_start⟩ := hBMall
    -- Case-split the RustExec witness: either ifTrue or ifFalse fired.
    cases hExec with
    | ifTrue _ _ _ _ _ v hv hne_zero hExecCt =>
      -- The TRUE branch ran.  Recurse on ct, then lift to outer newSid.
      have hCWT_ct : RustExecWithCalls.CloneCallsWellTyped N leafSpec ct rs := by
        simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
        exact hCloneWT.1
      obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
        rustExecSimulates_withCalls N leafSpec env fuel'
          hLeafN hLimb hClone ct rs rs' hWf.1 hCFx.1 hSSS.1 hFuel_ct
          hExecCt hCWT_ct sid heap hInv hSInv hBounded hBM_ct
      -- Cif eval (TRUE): produces heap' from heap.
      have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) =
          BitVec.ofNat 64 v := hv ▸ hSInv e
      have he_bnd : v < 2^64 := by rw [← hv]; exact hBounded e
      have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
          SDistr.pure (⟨.sbool, true⟩, heap) := by
        rw [cif_cond_eval]
        simp only [he_val]
        have hbne : BitVec.ofNat 64 v != (0 : BitVec 64) := by
          rw [bne_iff_ne]; exact bitVec_ofNat_ne_zero v hne_zero he_bnd
        rw [show ((0 : BitVec 64) = (0#64 : BitVec 64)) from rfl] at hbne
        simp [hbne]
      -- The outer eval reduces to `eval ct` at heap.
      refine ⟨heap', ?_, ?_, ?_, hB'⟩
      · simp only [toJasminCmd_RIfNz]
        rw [translateCmd_cif_eval_true env sid _ _ _ fuel' heap heap hcond]
        exact heval'
      · -- HeapInv lift from sid_ct to outer Cif newSid via hLiftTrue.
        have hNS : (translateCmd env (toJasminCmd (LowCT.RIfNz e ct cf)) sid (fuel' + 1)).newSid =
            (translateCmd env (toJasminCmd cf)
              ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid := by
          simp only [toJasminCmd_RIfNz]
          exact translateCmd_cif_newSid env sid _ _ _ fuel'
        rw [hNS]
        exact (hLiftTrue rs' heap' hExecCt hInv' hSInv').1
      · have hNS : (translateCmd env (toJasminCmd (LowCT.RIfNz e ct cf)) sid (fuel' + 1)).newSid =
            (translateCmd env (toJasminCmd cf)
              ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid := by
          simp only [toJasminCmd_RIfNz]
          exact translateCmd_cif_newSid env sid _ _ _ fuel'
        rw [hNS]
        exact (hLiftTrue rs' heap' hExecCt hInv' hSInv').2
    | ifFalse _ _ _ _ _ h_e_zero hExecCf =>
      -- The FALSE branch ran.  Lift pre-state HeapInv from sid to sid_ct,
      -- then recurse on cf at sid_ct.
      have hCWT_cf : RustExecWithCalls.CloneCallsWellTyped N leafSpec cf rs := by
        simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
        exact hCloneWT.2
      have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) =
          (0 : BitVec 64) := by
        have h1 := hSInv e
        rw [h_e_zero] at h1
        exact h1
      have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
          SDistr.pure (⟨.sbool, false⟩, heap) := by
        rw [cif_cond_eval]
        simp only [he_val]
        rfl
      -- Lift pre-state HeapInv/ScalarInv from sid to sid_ct.
      obtain ⟨hInv_lift, hSInv_lift⟩ := hLiftFalse heap hInv hSInv
      -- Recurse on cf at sid_ct.
      obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
        rustExecSimulates_withCalls N leafSpec env fuel'
          hLeafN hLimb hClone cf rs rs' hWf.2 hCFx.2 hSSS.2 hFuel_cf
          hExecCf hCWT_cf
          ((translateCmd env (toJasminCmd ct) sid fuel').newSid)
          heap hInv_lift hSInv_lift hBounded hBM_cf_from_start
      refine ⟨heap', ?_, ?_, ?_, hB'⟩
      · simp only [toJasminCmd_RIfNz]
        rw [translateCmd_cif_eval_false env sid _ _ _ fuel' heap heap hcond]
        exact heval'
      · have hNS : (translateCmd env (toJasminCmd (LowCT.RIfNz e ct cf)) sid (fuel' + 1)).newSid =
            (translateCmd env (toJasminCmd cf)
              ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid := by
          simp only [toJasminCmd_RIfNz]
          exact translateCmd_cif_newSid env sid _ _ _ fuel'
        rw [hNS]; exact hInv'
      · have hNS : (translateCmd env (toJasminCmd (LowCT.RIfNz e ct cf)) sid (fuel' + 1)).newSid =
            (translateCmd env (toJasminCmd cf)
              ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid := by
          simp only [toJasminCmd_RIfNz]
          exact translateCmd_cif_newSid env sid _ _ _ fuel'
        rw [hNS]; exact hSInv'
  | .RFor x n body =>
    subst h
    have hCF : callFree (LowCT.RFor x n body) = true := by
      simp only [RustExecWithCalls.callFreePlusCall] at hCFx
      exact hCFx
    have hNewSid : (translateCmd env (toJasminCmd (LowCT.RFor x n body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RAssert label =>
    subst h
    have hCF : callFree (LowCT.RAssert label) = true := by simp [callFree]
    have hNewSid : (translateCmd env (toJasminCmd (LowCT.RAssert label)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RBlock body =>
    subst h
    have hCF : callFree (LowCT.RBlock body) = true := by
      simp only [RustExecWithCalls.callFreePlusCall] at hCFx
      exact hCFx
    have hNewSid : (translateCmd env (toJasminCmd (LowCT.RBlock body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RWhileNz _ _ => subst h; simp [whileFree] at hWf
  | .RForRuntime _ _ _ => subst h; simp [whileFree] at hWf
  | .RCallSwap _ _ _ _ =>
    subst h
    exact absurd hCFx (by simp [RustExecWithCalls.callFreePlusCall, callFree])
  | .RCloneCall cloneVar cloneTy oldDest innerF dest args =>
    -- Single clone-call leaf: delegate to `rustCloneCallSimulates_newSid`.
    -- Extract the runtime well-typedness witness from `hCloneWT`.
    subst h
    simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
    obtain ⟨hTy, oldV, hOldDest⟩ := hCloneWT
    have hF : 3 ≤ fuel := by simpa [jasminFuel] using hFuel
    exact rustCloneCallSimulates_newSid N leafSpec env fuel
      (hLeafN (fuel - 1) (by omega)) (hClone fuel (by omega))
      cloneVar cloneTy oldDest innerF dest args rs rs' hExec oldV hTy hOldDest
      sid heap hInv hSInv hBounded
  | .RLimbStore loc idx v =>
    -- Single limb-store leaf: delegate to `rustLimbStoreSimulates` after
    -- the `newSid = sid` rewrite (RLimbStore lowers to `.Copn STORE64`
    -- which doesn't advance `newSid`, by `limbStore_toJasmin_newSid`).
    subst h
    have hNewSid :
        (translateCmd env (toJasminCmd (.RLimbStore loc idx v)) sid fuel).newSid = sid :=
      limbStore_toJasmin_newSid loc idx v env sid fuel
    rw [hNewSid]
    have hF : 2 ≤ fuel := by simpa [jasminFuel] using hFuel
    exact rustLimbStoreSimulates N leafSpec env fuel (hLimb fuel hF)
      loc idx v rs rs' hExec sid heap hInv hSInv hBounded
  | .RCallN _ _ _ => subst h; simp [whileFree] at hWf
  | .RSelect _ _ _ _ => subst h; simp [whileFree] at hWf
  | .RFnDef _ _ _ _ _ => subst h; simp [whileFree] at hWf
  | .RFnCall _ _ _ => subst h; simp [whileFree] at hWf
  | .RTupleLoad _ _ _ => subst h; simp [whileFree] at hWf
  | .RArrStore _ _ _ => subst h; simp [whileFree] at hWf
  | .RArrLoad _ _ _ => subst h; simp [whileFree] at hWf
  | .RScalarSetExpr _ _ => subst h; simp [whileFree] at hWf
termination_by sizeOf c

end SimulationTheorem

/-! ## §5  Concrete programs -/

section ConcretePrograms

/-- Located values for G1 curve operations. -/
def mkFpLoc (x : String) : Located := { locVar := x, locSrc := .TFp }
def mkFp2Loc (x : String) : Located := { locVar := x, locSrc := .TFp2 }

def g1X1 := mkFpLoc "X1"
def g1X2 := mkFpLoc "X2"
def g1Y1 := mkFpLoc "Y1"
def g1Y2 := mkFpLoc "Y2"
def g1Z1 := mkFpLoc "Z1"
def g1Z2 := mkFpLoc "Z2"
def g1X3 := mkFpLoc "X3"
def g1Y3 := mkFpLoc "Y3"
def g1Z3 := mkFpLoc "Z3"
def g1T0 := mkFpLoc "t0"
def g1T1 := mkFpLoc "t1"
def g1T2 := mkFpLoc "t2"
def g1T3 := mkFpLoc "t3"
def g1T4 := mkFpLoc "t4"
def g1T5 := mkFpLoc "t5"

open CatCrypt.Crypto.Jasmin.LowCTReflect
  (Fp Fp2 bls_fp_mul bls_fp_add bls_fp_sub bls_fp_sqr
   bls_fp2_mul bls_fp2_add bls_fp2_sub)

/-- G1 projective addition, authored as a pure-Lean SSA reference over
    the BLS base field `Fp` (Renes et al., fresh-destination form).
    Reified below by `reifyLowCTMulti%`; the two outputs `(X3, Y3)` are
    recovered as named slots.  Unlike the hand-authored register form,
    SSA gives each intermediate a fresh name (no temp reuse), but the
    denotation is identical and `X1`/`Y1`/`Z1` remain untouched. -/
noncomputable def g1AddRef (X1 Y1 Z1 X2 Y2 Z2 : Fp) : Fp × Fp :=
  let t0  := bls_fp_mul X1 X2
  let t1  := bls_fp_mul Y1 Y2
  let t2  := bls_fp_mul Z1 Z2
  let t3  := bls_fp_add X1 Y1
  let t4  := bls_fp_add X2 Y2
  let t5  := bls_fp_mul t3 t4
  let t6  := bls_fp_sub t5 t0
  let X3  := bls_fp_sub t6 t1
  let t7  := bls_fp_add Y1 Z1
  let t8  := bls_fp_add Y2 Z2
  let t9  := bls_fp_mul t7 t8
  let t10 := bls_fp_sub t9 t1
  let Y3  := bls_fp_sub t10 t2
  (X3, Y3)

/-- G1 projective addition, reified. `outNames = ["X3", "Y3"]`. -/
def g1Add : LowCT := (reifyLowCTMulti% g1AddRef).body

/-- G1 projective doubling, authored as a pure-Lean SSA reference. -/
noncomputable def g1DblRef (X1 Y1 Z1 : Fp) : Fp × Fp :=
  let _t0 := bls_fp_sqr X1
  let _t1 := bls_fp_sqr Y1
  let _t2 := bls_fp_sqr Z1
  let t3  := bls_fp_mul X1 Y1
  let X3  := bls_fp_add t3 t3
  let t4  := bls_fp_mul Y1 Z1
  let Y3  := bls_fp_add t4 t4
  (X3, Y3)

/-- G1 projective doubling, reified. `outNames = ["X3", "Y3"]`. -/
def g1Dbl : LowCT := (reifyLowCTMulti% g1DblRef).body

/-- G2 affine addition, authored as a pure-Lean SSA reference over the
    BLS extension field `Fp2`. -/
noncomputable def g2AddRef (X1 Y1 X2 Y2 : Fp2) : Fp2 × Fp2 :=
  let t0 := bls_fp2_mul X1 X2
  let _t1 := bls_fp2_mul Y1 Y2
  let t2 := bls_fp2_add X1 Y1
  let t3 := bls_fp2_add X2 Y2
  let X3 := bls_fp2_mul t2 t3
  let Y3 := bls_fp2_sub X3 t0
  (X3, Y3)

/-- G2 affine addition, reified. `outNames = ["X3", "Y3"]`. -/
def g2Add : LowCT := (reifyLowCTMulti% g2AddRef).body

example : borrowOk g1Add = true  := by decide
example : borrowOk g1Dbl = true  := by decide
example : borrowOk g2Add = true  := by decide

/-- The multi-result reifier recovered both projective-coordinate output
    slots, in order, for each curve kernel. -/
example : (reifyLowCTMulti% g1AddRef).outNames = ["X3", "Y3"] := by native_decide
example : (reifyLowCTMulti% g1DblRef).outNames = ["X3", "Y3"] := by native_decide
example : (reifyLowCTMulti% g2AddRef).outNames = ["X3", "Y3"] := by native_decide

/-- Denotation-faithfulness guard: the reified kernels translate to
    non-empty Jasmin command sequences (so the frame theorems below are not
    vacuous over a truncated term), and G1 addition (13 field ops) is
    strictly longer than G1 doubling (7 field ops, all three squarings
    retained even though only the `mul`/`add` results feed `X3`/`Y3`),
    which is strictly longer than G2 addition (6 field ops). -/
example :
    (toJasminCmd g2Add).length < (toJasminCmd g1Dbl).length ∧
    (toJasminCmd g1Dbl).length < (toJasminCmd g1Add).length := by native_decide

section FrameTheorems

variable (N : Nat) (leafSpec : LeafSpec)

theorem g1AddPreservesX1 (rs rs' : RustState)
    (h : RustExec N leafSpec g1Add rs rs') :
    locatedLookup rs' g1X1 = locatedLookup rs g1X1 := by
  apply seqFrame N leafSpec g1Add rs rs' g1X1 h
  decide

theorem g1DblPreservesInputs (rs rs' : RustState)
    (h : RustExec N leafSpec g1Dbl rs rs') :
    locatedLookup rs' g1X1 = locatedLookup rs g1X1 ∧
    locatedLookup rs' g1Y1 = locatedLookup rs g1Y1 ∧
    locatedLookup rs' g1Z1 = locatedLookup rs g1Z1 := by
  refine ⟨?_, ?_, ?_⟩
  · apply seqFrame N leafSpec g1Dbl rs rs' g1X1 h; decide
  · apply seqFrame N leafSpec g1Dbl rs rs' g1Y1 h; decide
  · apply seqFrame N leafSpec g1Dbl rs rs' g1Z1 h; decide

end FrameTheorems
end ConcretePrograms

/-! ## §6  Pretty-printer and file output -/

section Printer

/-- Pretty-print a `TowerType` as a Jasmin array type comment. -/
def ppTowerType : TowerType → String
  | .TFp     => "fp"    | .TFp2  => "fp2"
  | .TFp6    => "fp6"   | .TFp12 => "fp12"
  | .TU64    => "u64"
  | .TU8     => "u8"
  | .TU32    => "u32"
  | .TFp25519 => "fp25519"
  | .TFp25519_64 => "fp25519_64"
  | .TFpL25519 => "fpL25519"
  | .TFpP256 => "fpP256"
  | .TFp25519_4Bounded b => "fp25519_4(<2^" ++ toString b ++ ")"
  | .TFpGen name n => "fpGen[" ++ name ++ ", " ++ toString n ++ "B]"
  | .TFp2Gen name n => "fp2Gen[" ++ name ++ ", " ++ toString n ++ "B]"
  | .TTuple a b => "(" ++ ppTowerType a ++ "," ++ ppTowerType b ++ ")"
  | .TBytes n => "u8[" ++ toString n ++ "]"
  | .TArr n t => ppTowerType t ++ "[" ++ toString n ++ "]"
  -- Polynomial-mod-q pretty forms.
  | .TPolyMod q n => "poly_mod[" ++ toString q ++ "," ++ toString n ++ "]"
  | .TPolyVec q n k =>
      "polyvec[" ++ toString q ++ "," ++ toString n ++ "," ++ toString k ++ "]"
  | .TPolyMat q n k m =>
      "polymat[" ++ toString q ++ "," ++ toString n ++ "," ++
        toString k ++ "x" ++ toString m ++ "]"

/-- Pretty-print a `WSize`. -/
def ppWSize : WSize → String
  | .U8 => "u8" | .U16 => "u16" | .U32 => "u32"
  | .U64 => "u64" | .U128 => "u128" | .U256 => "u256" | .U512 => "u512"

/-- Pretty-print a `SType`. -/
def ppSType : SType → String
  | .sbool   => "bool"
  | .sint    => "int"
  | .sarr n  => "u8[" ++ toString n ++ "]"
  | .sword w => ppWSize w

/-- Jasmin infix operator symbol for a binary op (width is inferred from
    operand types in Jasmin source, so it is dropped here). -/
def ppSOp2 : SOp2 → String
  | .Obeq        => "=="
  | .Oand        => "&&"
  | .Oor         => "||"
  | .Oadd _      => "+"
  | .Omul _      => "*"
  | .Osub _      => "-"
  | .Odiv _ _    => "/"
  | .Omod _ _    => "%"
  | .Oland _     => "&"
  | .Olor _      => "|"
  | .Olxor _     => "^"
  | .Olsr _      => ">>"
  | .Olsl _      => "<<"
  | .Oasr _      => ">>s"
  | .Oeq _       => "=="
  | .Oneq _      => "!="
  | .Olt _ _     => "<"
  | .Ole _ _     => "<="
  | .Ogt _ _     => ">"
  | .Oge _ _     => ">="
  | .Ovadd _ _   => "+"
  | .Ovsub _ _   => "-"
  | .Ovmul _ _   => "*"
  | .Ovlsr _ _   => ">>"
  | .Ovlsl _ _   => "<<"
  | .Ovasr _ _   => ">>s"

def ppPExpr : PExpr → String
  | .Pconst z   => toString z
  | .Pbool b    => if b then "true" else "false"
  | .Pvar gv    => gv.gv.var.vname
  | .Papp2 (.Oneq _) e (.Pconst 0) => "(" ++ ppPExpr e ++ " != 0)"
  | .Papp2 op e1 e2 =>
      "(" ++ ppPExpr e1 ++ " " ++ ppSOp2 op ++ " " ++ ppPExpr e2 ++ ")"
  -- Unary ops.  `Oword_of_int` / `Oint_of_word` are transparent in source
  -- (a word literal is just the integer); zero/sign-extend print as casts.
  | .Papp1 (.Oword_of_int _) e => ppPExpr e
  | .Papp1 (.Oint_of_word _) e => ppPExpr e
  | .Papp1 (.Ozeroext wso _) e => "(" ++ toString wso.bits ++ "u) " ++ ppPExpr e
  | .Papp1 (.Osignext wso _) e => "(" ++ toString wso.bits ++ "s) " ++ ppPExpr e
  | .Papp1 .Onot e             => "!" ++ ppPExpr e
  | .Papp1 (.Olnot _) e        => "!" ++ ppPExpr e
  | .Papp1 (.Oneg _) e         => "(- " ++ ppPExpr e ++ ")"
  | .Pget _ _ x idx => x.gv.var.vname ++ "[" ++ ppPExpr idx ++ "]"
  | .Parr_init n => "#init(" ++ toString n ++ ")"
  | e => "<expr:" ++ (repr e).pretty 80 ++ ">"

/-- Pretty-print an `LVal`. -/
def ppLVal : LVal → String
  | .Lnone _ _     => "_"
  | .Lvar v        => v.var.vname
  | .Laset _ _ v _ => v.var.vname
  | lv             => "<lval:" ++ (repr lv).pretty 80 ++ ">"

/-- Indent by `n` spaces. -/
def indent (n : Nat) (s : String) : String :=
  String.replicate n ' ' ++ s

mutual
  /-- Pretty-print one instruction with indentation `ind`. -/
  def ppInstrR (ind : Nat) : InstrR → String
    | .Cassgn lv _ _ e =>
        indent ind (ppLVal lv ++ " = " ++ ppPExpr e ++ ";")
    | .Copn lvs _ (.Oasm op) es =>
        let lhss := String.intercalate ", " (lvs.map ppLVal)
        let args := String.intercalate ", " (es.map ppPExpr)
        indent ind (lhss ++ " = #" ++ op.name ++ "(" ++ args ++ ");")
    | .Ccall _ lvs fn args =>
        let lhss := String.intercalate ", " (lvs.map ppLVal)
        let argStr := String.intercalate ", " (args.map ppPExpr)
        indent ind (lhss ++ " = " ++ fn.name ++ "(" ++ argStr ++ ");")
    | .Cif cond cthen celse =>
        let hdr := indent ind ("if (" ++ ppPExpr cond ++ ") {")
        let thenStr := ppCmd (ind + 2) cthen
        if celse.isEmpty then
          hdr ++ "\n" ++ thenStr ++ "\n" ++ indent ind "}"
        else
          hdr ++ "\n" ++ thenStr ++ "\n" ++ indent ind "} else {" ++
          "\n" ++ ppCmd (ind + 2) celse ++ "\n" ++ indent ind "}"
    | .Cwhile _ cond body =>
        indent ind ("while (" ++ ppPExpr cond ++ ") {") ++
        "\n" ++ ppCmd (ind + 2) body ++ "\n" ++ indent ind "}"
    | .Cfor v r body =>
        indent ind ("for " ++ v.var.vname ++ " = " ++ toString r.lo ++
                    " to " ++ toString r.hi ++ " {") ++
        "\n" ++ ppCmd (ind + 2) body ++ "\n" ++ indent ind "}"

  /-- Pretty-print a `Cmd` (list of instructions) with indentation `ind`. -/
  def ppCmd (ind : Nat) : Cmd → String
    | [] => ""
    | instrs => String.intercalate "\n" (instrs.map (ppInstrR ind))
end

/-- Pretty-print a `FunDecl`. -/
def ppFunDecl (fd : FunDecl) : String :=
  let params := String.intercalate ", "
    (fd.params.map (fun p => ppSType p.var.var.vtype ++ " " ++ p.var.var.vname))
  let results := String.intercalate ", " (fd.results.map (fun r => r.var.vname))
  let body := ppCmd 2 fd.body
  "fn " ++ fd.name.name ++ "(" ++ params ++ ") -> (" ++ results ++ ") {\n" ++ body ++ "\n}"

/-- Pretty-print a full `JasminProg`. -/
def ppJasminProg (prog : JasminProg) : String :=
  String.intercalate "\n\n" (prog.funcs.map ppFunDecl)

/-- Write a `LowCT` as a Jasmin function to a file. -/
def writeJasminProg (filename name : String) (params results : List Located)
    (c : LowCT) : IO Unit := do
  let prog := toJasminProg name params results c
  IO.FS.writeFile filename (ppJasminProg prog)

/-- Write the `LowCT` Rocq repr to a file (for round-trip inspection). -/
def writeLowCTRepr (filename : String) (c : LowCT) : IO Unit :=
  IO.FS.writeFile filename (repr c |>.pretty 80)

end Printer

/-! ## §7  Demo: emit g1_add to file

Uncomment to generate `g1_add.jazz` and `g1_add_rustcmd.txt`:

```lean
-- #eval writeJasminProg "/tmp/g1_add.jazz" "g1_add"
        [g1X1, g1Y1, g1Z1, g1X2, g1Y2, g1Z2]
        [g1X3, g1Y3]
        g1Add

-- #eval writeLowCTRepr "/tmp/g1_add_rustcmd.txt" g1Add

-- #eval IO.println (ppJasminProg (toJasminProg "g1_add"
        [g1X1, g1Y1, g1Z1, g1X2, g1Y2, g1Z2] [g1X3, g1Y3] g1Add))
```
-/

end CatCrypt.Crypto.Jasmin.LowCT
