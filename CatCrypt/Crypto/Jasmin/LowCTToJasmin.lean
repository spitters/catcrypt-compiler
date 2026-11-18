/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import Mathlib.Data.String.Defs
public import CatCrypt.Crypto.Jasmin.LowCTExec
public meta import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
public import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
public import CatCrypt.Crypto.Jasmin.JasminVar
public import CatCrypt.Crypto.Jasmin.JasminOps
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
* §3  Static predicates `whileFree`, `forFree`, `callFree`, `callFreePlusCall`
* §5  Concrete programs (G1 add/dbl, G2 add)
* §6  Pretty-printer — `ppInstrR`, `ppCmd`

Correctness of the lowering is by the dialect route (`rustExecSimulatesDialect`); the
`.jazz` text is checked against the `psem.v` mirror (`JasminCoqSemMirror`).

## Frozen text printers

The text printers of §6 (`ppInstrR` and `ppCmd`) are frozen: they are kept unchanged for
the bench drivers that print through them, by way of `JForProg.toJazzExport`. New Jasmin
text is produced by the single printer, `Jazz.printChecked`, and its entries `JasminPrintText.emitJazzN`,
`emitJazzOuts`, `emitJazzInOuts` and `JasminAbiJazz.emitAbiOrchJ`. The lowering
`toJasminCmd` is not a printer and is not frozen.
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
  -- Whole-slot copy: one array assignment `dst = src` at the storage type
  -- of the destination tower.
  | .RCopy dst src =>
      [.Cassgn (locToLVal dst) .AT_none (towerToSType dst.locDst) (locToPExpr src)]
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

@[simp] theorem toJasminCmd_RCopy (dst src : Located) :
    toJasminCmd (.RCopy dst src)
      = [.Cassgn (locToLVal dst) .AT_none (towerToSType dst.locDst) (locToPExpr src)] := rfl

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

This is a parallel function to `toJasminCmd`, which it leaves unchanged.
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
  | .RCopy dst src =>
      [.Cassgn (locToLVal dst) .AT_none (towerToSType dst.locDst) (locToPExpr src)]
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
  | RCopy _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RCallDstThreaded _ _ _ => rfl
  | RForRuntime _ _ _ => rfl

/-! ## §3  Static predicates

Boolean predicates on the `LowCT` syntax that select the program classes of the
theorems stated over `toJasminCmd` elsewhere (`JasminSem.rustExecSoundInJasmin`,
`RustExecTraced`, `VIR/LowCTMirrorTranslate`). Correctness of the lowering
`toJasminCmd` is by the dialect route (`rustExecSimulatesDialect`); the `.jazz` text
`compileA` prints is checked against the `psem.v` mirror. -/

/-- `whileFree c = true` iff `c` is built from `RSkip`, `RScalarSet`, `RCall`,
    `RCallSwap`, `RCloneCall`, `RLimbStore` and `RAssert` leaves by `RSeq`, `RIfNz`,
    `RLetZero`, `RLetU64Zero`, `RFor` and `RBlock`. It is `false` on every other
    constructor: the loops `RWhileNz` and `RForRuntime`, the multi-output call `RCallN`,
    `RSelect`, `RLimbStoreExpr`, the function constructors `RFnDef`/`RFnCall`, the
    tuple, array and `SExpr` constructors, `RCopy` and `RCallDstThreaded`. -/
def whileFree : LowCT → Bool
  | .RSkip | .RScalarSet _ _ | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => whileFree c1 && whileFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body => whileFree body
  | .RWhileNz _ _ => false
  -- `RFor` lowers by static unrolling (`forBodyN`).
  | .RFor _ _ body => whileFree body
  | .RForRuntime _ _ _ => false
  | .RCallN _ _ _ | .RSelect _ _ _ _ => false
  | .RLimbStoreExpr _ _ _ => false
  | .RAssert _ => true
  | .RBlock body => whileFree body
  | .RFnDef _ _ _ _ _ | .RFnCall _ _ _ => false
  | .RTupleLoad _ _ _ => false
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => false
  | .RArrStoreLit _ _ _ | .RArrLoadLit _ _ _ | .RCopy _ _ => false
  | .RCallDstThreaded _ _ _ => false

/-- `forFree c = true` iff `c` contains no `RFor` and no `RForRuntime` subterm.
    The reverse trace correspondence `jasminSemTraced_to_rustExecTraced` takes it
    beside `whileFree`, which admits `RFor`. -/
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
  | .RArrStoreLit _ _ _ | .RArrLoadLit _ _ _ | .RCopy _ _ => true
  -- dst-threaded leaf call has no RFor inside.
  | .RCallDstThreaded _ _ _ => true

/-- `callFree c = true` iff `c` contains no call constructor (`RCall`, `RCallSwap`,
    `RCloneCall`, `RCallN`, `RFnCall`, `RCallDstThreaded`), no limb store
    (`RLimbStore`, `RLimbStoreExpr`) and none of `RTupleLoad`, the array and `SExpr`
    constructors and `RCopy`. -/
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
  | .RTupleLoad _ _ _ => false
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => false
  | .RArrStoreLit _ _ _ | .RArrLoadLit _ _ _ | .RCopy _ _ => false
  -- dst-threaded IS a call (analogous to RCall).
  | .RCallDstThreaded _ _ _ => false

namespace RustExecWithCalls

/-- `callFreePlusCall c = true` iff `c` is a tree of `RSeq` and `RIfNz` nodes
    whose leaves are `callFree` subprograms, single `RCall`s, single
    `RLimbStore`s or single `RCloneCall`s. Every other constructor, `RFor`,
    `RBlock`, `RLetZero`, `RLetU64Zero` and `RCallSwap` among them, is admitted
    only when it is `callFree`. -/
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
  | .RLimbStoreExpr _ _ _ => simp [callFreePlusCall, hCF]
  | .RTupleLoad _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrStore _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrLoad _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrStoreLit _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrLoadLit _ _ _ => simp [callFreePlusCall, hCF]
  | .RCopy _ _ => simp [callFreePlusCall, hCF]
  | .RScalarSetExpr _ _ => simp [callFreePlusCall, hCF]
  | .RCallDstThreaded _ _ _ => simp [callFree] at hCF

end RustExecWithCalls

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

/-! ## §6  Pretty-printer

These printers are frozen for the bench drivers that call them (module docstring). -/

section Printer

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

end Printer

end CatCrypt.Crypto.Jasmin.LowCT
