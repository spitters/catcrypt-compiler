/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.String.Defs
public import CatCrypt.Crypto.Jasmin.LowCTSyntax

/-!
# `LowCT → Jasmin` direct emit

Parallel emit path to `RustEmit.lean` (Rust source) and
`LowCTToMLIR.lean` (MLIR `func.func`) — produces a `.jazz`-style
string directly from a `LowCT`, with tower-type-aware lowering for
the polynomial types (`TPolyMod`, `TPolyVec`, `TPolyMat`).

### Why a direct emit instead of going through `FunDecl`?

The existing `JasminEmit.emitFunDecl` (in `JasminEmit.lean`) only
handles `reg u64`-typed SSA shapes (its body type, `List InstrR`,
is the SSA form used by the bignum/field kernels).  The polynomial
kernels in `MlkemLowCT.lean` / `MldsaLowCT.lean` live in
`TPolyMod q n` etc., which don't map cleanly to that SSA — each
polynomial slot is naturally a `stack u16[n]` allocation (Jasmin's
convention for formosa-mlkem), not a single `reg u64`.

Bridging the two paths would require a per-coefficient SSA expansion
(256 `InstrR` per polynomial), losing the leaf-call structure that
formosa relies on.  The direct emit here keeps polynomial leaves as
single-line Jasmin function calls and emits the stack-array
allocations at the top of the function body.

### Lowering map (tower type → Jasmin type)

```
TPolyMod q n      → stack u16[n]      (q < 2^16, e.g. ML-KEM q=3329)
                  → stack u32[n]      (q < 2^32, e.g. ML-DSA q=8380417)
TPolyVec q n k    → stack u16[n*k]    (or u32)
TPolyMat q n k m  → stack u16[n*k*m]  (or u32)
TBytes n          → stack u8[n]
TArr m t          → stack <innerJasminType> [m]   (recursive)
TFp               → reg u16            (default; for >2^16 fields use TPolyMod)
TFp25519, TFp25519_64, ... → comment placeholder
TU64              → reg u64
TTuple a b        → fallback: `stack u8` flat-pack to (sizeOf a + sizeOf b)
```

`TPolyMod` / `TPolyVec` / `TPolyMat` carry the array shapes; the other
tower types either match the `JasminEmit` path or get a placeholder.  Real formosa-mlkem uses `stack u16[MLKEM_VECN]`
for polyvec (= `stack u16[k*256]` = `stack u16[768]` for ML-KEM-768),
which exactly matches `TPolyVec 3329 256 3`'s lowering.

### Smoke-test level

This emit is **structural**: it produces Jasmin source that
references the leaf primitives by name as `extern fn` calls.  The
caller is expected to `include` the appropriate `.jinc` files
(formosa's `poly.jinc`, `polyvec.jinc`, `gen_matrix.jinc`, etc.)
that provide the leaf bodies.  A from-scratch compile of the emitted
`.jazz` against a stub `.jinc` is the natural next step.

## Replacement

This module will be removed; Jasmin text is produced by the single printer
`Jazz.print` (`Jasmin/JazzPrint.lean`), and its polynomial typing becomes storage
inference over `toJasminCmd`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1 Tower-type lowering -/

/-- Pick the Jasmin coefficient word width for a prime modulus.
    ML-KEM (q = 3329) fits in `u16`; ML-DSA (q = 8380417) needs `u32`.
    Anything beyond `u32` is out of scope for this pass and gets a
    sentinel `"u64"` (likely incorrect for the protocol but keeps
    emit going). -/
def coeffWordSize (q : Nat) : String :=
  if q < 65536 then "u16"
  else if q < 4294967296 then "u32"
  else "u64"

/-- Bytes per coefficient at the chosen word size (used to compute
    sub-array offsets when needed). -/
def coeffWordBytes (q : Nat) : Nat :=
  if q < 65536 then 2
  else if q < 4294967296 then 4
  else 8

/-- Jasmin storage-declaration form for a `TowerType` slot.  This is
    the type that goes in the `stack ... <name>;` line at the top of
    the function, NOT the in-line reference form. -/
partial def jasminTowerType : TowerType → String
  | .TU64                 => "reg u64"
  | .TU8                  => "reg u8"
  | .TU32                 => "reg u32"
  | .TFp                  => "reg u16"
  | .TFp2                 => "stack u16[2]"
  | .TFp6                 => "stack u16[6]"
  | .TFp12                => "stack u16[12]"
  | .TFp25519             => "stack u8[32]"
  | .TFp25519_64          => "stack u64[4]"
  | .TFpL25519            => "stack u8[32]"
  | .TFpP256              => "stack u8[32]"
  | .TFp25519_4Bounded _  => "stack u8[32]"
  | .TFpGen _ _           => "stack u64[4]"
  | .TFp2Gen _ _          => "stack u64[8]"
  | .TTuple a b           =>
      -- Flat-pack to a byte buffer of the sum of byte sizes — matches
      -- the way `LowCTToCryptoSSA.encodeTy` handles tuples.
      s!"stack u8[{a.storageBytes + b.storageBytes}]"
  | .TBytes n             => s!"stack u8[{n}]"
  | .TArr n t             =>
      -- Array of `n` copies of the inner type.  For `TArr n (TBytes m)`
      -- this becomes `stack u8[n*m]`.  For nested arrays we flat-pack
      -- conservatively to a byte buffer of `n * inner.storageBytes`.
      match t with
      | .TBytes m => s!"stack u8[{n * m}]"
      | _         => s!"stack u8[{n * t.storageBytes}]"
  -- Polynomial-mod-q slots.
  | .TPolyMod q n         => s!"stack {coeffWordSize q}[{n}]"
  | .TPolyVec q n k       => s!"stack {coeffWordSize q}[{k * n}]"
  | .TPolyMat q n k m     => s!"stack {coeffWordSize q}[{k * m * n}]"

/-- Number of underlying `u16`/`u8` cells in one element of a
    container `TowerType`.  Used to compute slice strides in
    `RArrLoad`/`RArrStore` when the element is itself an array
    (polyvec → polynomial slice, polymat → polyvec slice). -/
def TowerType.elemStride : TowerType → Nat
  | .TPolyMod _q n        => n                    -- 256 u16 cells per poly
  | .TPolyVec _q n _k     => n                    -- one element of a polyvec is a poly of n cells
  | .TPolyMat _q n _k m   => n * m                -- a polymat element is a polyvec of n*m cells
  | .TBytes _             => 1                    -- bytes are scalar
  | .TArr _ t             => t.elemStride
  | _                     => 1                    -- scalar elements

/-- Total number of `u8`/`u16` cells in a stack-array `TowerType`, or
    `none` for scalar (`reg`) slots.  Used to size the zeroing prologue
    for accumulator slots whose `repeat(0, n)` initialiser is not emitted
    (Jasmin stack slots are *not* implicitly zeroed). -/
def TowerType.arrayCellCount : TowerType → Option Nat
  | .TPolyMod _q n        => some n
  | .TPolyVec _q n k      => some (k * n)
  | .TPolyMat _q n k m    => some (k * m * n)
  | .TBytes n             => some n
  | _                     => none

/-- A short comment fragment naming the original tower type, used to
    annotate stack declarations so the emitted `.jazz` stays
    self-documenting. -/
def jasminTowerComment : TowerType → String
  | .TFp                  => "TFp"
  | .TU64                 => "TU64"
  | .TBytes n             => s!"TBytes {n}"
  | .TPolyMod q n         => s!"TPolyMod {q} {n}"
  | .TPolyVec q n k       => s!"TPolyVec {q} {n} {k}"
  | .TPolyMat q n k m     => s!"TPolyMat {q} {n} {k} {m}"
  | _                     => "<tower>"

/-! ## §2 Declaration collection

Jasmin requires variable declarations at the top of the function
body (classic C89-style).  Walk the `LowCT` collecting every
`RLetZero` / `RLetU64Zero` slot name + type, then emit them as a
declaration block before pretty-printing the body. -/

/-- Walk `c` collecting every `RLetZero` binding as `(name, type)`.
    Order: pre-order traversal, which matches how the body
    pretty-printer encounters them. -/
partial def collectLetZeros : LowCT → List (String × TowerType)
  | .RSkip                         => []
  | .RSeq c1 c2                    => collectLetZeros c1 ++ collectLetZeros c2
  | .RLetZero x t body             => (x, t) :: collectLetZeros body
  | .RLetU64Zero _ body            => collectLetZeros body
  | .RScalarSet _ _                => []
  | .RIfNz _ ct cf                 => collectLetZeros ct ++ collectLetZeros cf
  | .RWhileNz _ body               => collectLetZeros body
  | .RFor _ _ body                 => collectLetZeros body
  | .RForRuntime _ _ body          => collectLetZeros body
  | .RCall _ _ _                   => []
  | .RCallSwap _ _ _ _             => []
  | .RCloneCall cv t _ _ _ _       => [(cv, t)]
  | .RLimbStore _ _ _              => []
  | .RLimbStoreExpr _ _ _          => []
  | .RCallN _ _ _                  => []
  | .RSelect _ _ _ _               => []
  | .RAssert _                     => []
  | .RBlock body                   => collectLetZeros body
  | .RFnDef _ _ _ _ cont           => collectLetZeros cont
  | .RFnCall _ _ _                 => []
  | .RTupleLoad _ _ _              => []
  | .RArrStore _ _ _               => []
  | .RArrLoad _ _ _                => []
  | .RArrStoreLit _ _ _            => []
  | .RArrLoadLit _ _ _             => []
  | .RScalarSetExpr _ _            => []
  | .RCallDstThreaded _ _ _        => []
  | .RCopy _ _                     => []

/-- `RFor` loops with bound above this lower to a runtime `while` (a
    `reg u64` counter) rather than Jasmin's always-unrolled `for`.
    Small loops (≤ this, e.g. the k=3 polyvec-row loops) keep the
    unrolled `for` so their reg-offset slices (`a[i*256:256]`) still
    type-check — Jasmin can't form a reg-offset stack slice (only
    reg *scalar* indexing works under a `while`).  Large loops (256,
    384, …, and especially poly_mul's nested 256×256) become `while`
    so jasminc doesn't unroll 65 536 bodies and stack-overflow. -/
def forLoopThreshold : Nat := 16

/-- Collect `RFor` index names whose bound is `> forLoopThreshold`
    when `large = true`, or `≤ forLoopThreshold` when `large = false`.
    Large indices are declared `reg u64` (while counters); small ones
    `inline int` (unrolled for). -/
partial def collectLoopIdxs (large : Bool) : LowCT → List String
  | .RSkip                         => []
  | .RSeq c1 c2                    => collectLoopIdxs large c1 ++ collectLoopIdxs large c2
  | .RLetZero _ _ body             => collectLoopIdxs large body
  | .RLetU64Zero _ body            => collectLoopIdxs large body
  | .RScalarSet _ _                => []
  | .RIfNz _ ct cf                 => collectLoopIdxs large ct ++ collectLoopIdxs large cf
  | .RWhileNz _ body               => collectLoopIdxs large body
  | .RFor x n body                 =>
      (if (n > forLoopThreshold) = large then [x] else []) ++ collectLoopIdxs large body
  | .RForRuntime x _ body          =>
      -- runtime-bound loop is lowered as a while-counter (large=true)
      (if large then [x] else []) ++ collectLoopIdxs large body
  | .RCall _ _ _                   => []
  | .RCallSwap _ _ _ _             => []
  | .RCloneCall _ _ _ _ _ _        => []
  | .RLimbStore _ _ _              => []
  | .RLimbStoreExpr _ _ _          => []
  | .RCallN _ _ _                  => []
  | .RSelect _ _ _ _               => []
  | .RAssert _                     => []
  | .RBlock body                   => collectLoopIdxs large body
  | .RFnDef _ _ _ _ cont           => collectLoopIdxs large cont
  | .RFnCall _ _ _                 => []
  | .RTupleLoad _ _ _              => []
  | .RArrStore _ _ _               => []
  | .RArrLoad _ _ _                => []
  | .RArrStoreLit _ _ _            => []
  | .RArrLoadLit _ _ _             => []
  | .RScalarSetExpr _ _            => []
  | .RCallDstThreaded _ _ _        => []
  | .RCopy _ _                     => []

/-- Small (`≤ forLoopThreshold`) loop indices — declared `inline int`. -/
def collectForIndices (c : LowCT) : List String := collectLoopIdxs false c

/-- Large (`> forLoopThreshold`) loop counters — declared `reg u64`. -/
def collectWhileCounters (c : LowCT) : List String := collectLoopIdxs true c

/-- Walk `c` collecting every `RLetU64Zero` binding (just the name). -/
partial def collectLetU64s : LowCT → List String
  | .RSkip                         => []
  | .RSeq c1 c2                    => collectLetU64s c1 ++ collectLetU64s c2
  | .RLetZero _ _ body             => collectLetU64s body
  | .RLetU64Zero x body            => x :: collectLetU64s body
  | .RScalarSet _ _                => []
  | .RIfNz _ ct cf                 => collectLetU64s ct ++ collectLetU64s cf
  | .RWhileNz _ body               => collectLetU64s body
  | .RFor _ _ body                 => collectLetU64s body
  | .RForRuntime _ _ body          => collectLetU64s body
  | .RCall _ _ _                   => []
  | .RCallSwap _ _ _ _             => []
  | .RCloneCall _ _ _ _ _ _        => []
  | .RLimbStore _ _ _              => []
  | .RLimbStoreExpr _ _ _          => []
  | .RCallN _ _ _                  => []
  | .RSelect _ _ _ _               => []
  | .RAssert _                     => []
  | .RBlock body                   => collectLetU64s body
  | .RFnDef _ _ _ _ cont           => collectLetU64s cont
  | .RFnCall _ _ _                 => []
  | .RTupleLoad _ _ _              => []
  | .RArrStore _ _ _               => []
  | .RArrLoad _ _ _                => []
  | .RArrStoreLit _ _ _            => []
  | .RArrLoadLit _ _ _             => []
  | .RScalarSetExpr _ _            => []
  | .RCallDstThreaded _ _ _        => []
  | .RCopy _ _                     => []

/-- Walk `c` collecting every variable used as an array **index**
    (`RArrStore`'s 2nd field, `RArrLoad`'s 3rd field).  Jasmin requires
    an index expression be either an `inline int` or a `reg u64`; a
    `reg u16` slot (which is how the translator types a `TFp` index
    accumulator like `idx = i + j`) is rejected at linearization
    (`R8 = RDX +64u RSI` has no target instruction).  Any `RLetZero`
    slot whose name appears here must therefore be declared `reg u64`
    rather than from its inferred tower type. -/
partial def collectIndexVars : LowCT → List String
  | .RSkip                         => []
  | .RSeq c1 c2                    => collectIndexVars c1 ++ collectIndexVars c2
  | .RLetZero _ _ body             => collectIndexVars body
  | .RLetU64Zero _ body            => collectIndexVars body
  | .RScalarSet _ _                => []
  | .RIfNz _ ct cf                 => collectIndexVars ct ++ collectIndexVars cf
  | .RWhileNz _ body               => collectIndexVars body
  | .RFor _ _ body                 => collectIndexVars body
  | .RForRuntime _ _ body          => collectIndexVars body
  | .RCall _ _ _                   => []
  | .RCallSwap _ _ _ _             => []
  | .RCloneCall _ _ _ _ _ _        => []
  | .RLimbStore _ _ _              => []
  | .RLimbStoreExpr _ _ _          => []
  | .RCallN _ _ _                  => []
  | .RSelect _ _ _ _               => []
  | .RAssert _                     => []
  | .RBlock body                   => collectIndexVars body
  | .RFnDef _ _ _ _ cont           => collectIndexVars cont
  | .RFnCall _ _ _                 => []
  | .RTupleLoad _ _ _              => []
  | .RArrStore _ idxVar _          => [idxVar]
  | .RArrLoad _ _ idxVar           => [idxVar]
  | .RArrStoreLit _ _ _            => []   -- literal index, no index var
  | .RArrLoadLit _ _ _             => []   -- literal index, no index var
  | .RScalarSetExpr _ _            => []
  | .RCallDstThreaded _ _ _        => []
  | .RCopy _ _                     => []

/-- Walk `c` collecting every array slot that is **read**: an
    `RArrLoad` source (`r[idx]`) or any argument to a function-style
    `RCall` / `RCallSwap` / `RCallN` (`poly_add(acc, prod)`).  A slot
    that is read is a zeroing candidate (it may be consumed before being
    written). -/
partial def collectArrReadSlots : LowCT → List String
  | .RSkip                         => []
  | .RSeq c1 c2                    => collectArrReadSlots c1 ++ collectArrReadSlots c2
  | .RLetZero _ _ body             => collectArrReadSlots body
  | .RLetU64Zero _ body            => collectArrReadSlots body
  | .RScalarSet _ _                => []
  | .RIfNz _ ct cf                 => collectArrReadSlots ct ++ collectArrReadSlots cf
  | .RWhileNz _ body               => collectArrReadSlots body
  | .RFor _ _ body                 => collectArrReadSlots body
  | .RForRuntime _ _ body          => collectArrReadSlots body
  | .RCall _ _ args                => args.map (·.locVar)
  | .RCallSwap _ _ _ args          => args.map (·.locVar)
  | .RCloneCall _ _ _ _ _ args     => args.map (·.locVar)
  | .RLimbStore _ _ _              => []
  | .RLimbStoreExpr _ _ _          => []
  | .RCallN _ _ args               => args.map (·.locVar)
  | .RSelect _ _ _ _               => []
  | .RAssert _                     => []
  | .RBlock body                   => collectArrReadSlots body
  | .RFnDef _ _ _ _ cont           => collectArrReadSlots cont
  | .RFnCall _ _ args              => args.map (·.locVar)
  | .RTupleLoad _ _ _              => []
  | .RArrStore _ _ _               => []
  | .RArrLoad _ src _              => [src.locVar]
  | .RArrStoreLit _ _ _            => []
  | .RArrLoadLit _ src _           => [src.locVar]
  | .RScalarSetExpr _ _            => []
  | .RCallDstThreaded _ _ args     => args.map (·.locVar)
  | .RCopy _ src                   => [src.locVar]

/-- Walk `c` collecting every `RArrLoad` *destination* slot — i.e. a
    slot fully overwritten by a slice-copy (`__anorm_0 = a[i*256:256]`).
    Such a slot never needs zeroing even if later read. -/
partial def collectArrLoadDsts : LowCT → List String
  | .RSkip                         => []
  | .RSeq c1 c2                    => collectArrLoadDsts c1 ++ collectArrLoadDsts c2
  | .RLetZero _ _ body             => collectArrLoadDsts body
  | .RLetU64Zero _ body            => collectArrLoadDsts body
  | .RScalarSet _ _                => []
  | .RIfNz _ ct cf                 => collectArrLoadDsts ct ++ collectArrLoadDsts cf
  | .RWhileNz _ body               => collectArrLoadDsts body
  | .RFor _ _ body                 => collectArrLoadDsts body
  | .RForRuntime _ _ body          => collectArrLoadDsts body
  | .RCall _ _ _                   => []
  | .RCallSwap _ _ _ _             => []
  | .RCloneCall _ _ _ _ _ _        => []
  | .RLimbStore _ _ _              => []
  | .RLimbStoreExpr _ _ _          => []
  | .RCallN _ _ _                  => []
  | .RSelect _ _ _ _               => []
  | .RAssert _                     => []
  | .RBlock body                   => collectArrLoadDsts body
  | .RFnDef _ _ _ _ cont           => collectArrLoadDsts cont
  | .RFnCall _ _ _                 => []
  | .RTupleLoad _ _ _              => []
  | .RArrStore _ _ _               => []
  | .RArrLoad dst _ _              => [dst.locVar]
  | .RArrStoreLit _ _ _            => []
  | .RArrLoadLit dst _ _           => [dst.locVar]
  | .RScalarSetExpr _ _            => []
  | .RCallDstThreaded _ _ _        => []
  | .RCopy dst _                   => [dst.locVar]

/-! ## §3 Body pretty-printer

After the declarations are stripped to the function-top block, the
body is pretty-printed without re-emitting `RLetZero` / `RLetU64Zero`
lines (Jasmin doesn't allow inline declarations).  Other constructs
emit as Jasmin pseudo-source. -/

def jasIndent (n : Nat) (s : String) : String :=
  String.replicate n ' ' ++ s

/-- Jasmin infix operator for an arithmetic / bitwise leaf-call name.
    The hax extraction emits binary arithmetic and bit operations as
    `RCall`s with operator names (`Mul`, `Add`, `BitAnd#32`, `Shr#32`,
    …); jasminc has no such functions — they must become infix
    operators.  Returns `none` for leaf calls (poly_add etc.). -/
def jasminBinOp (f : String) : Option String :=
  match f with
  | "Add" | "add" | "wrapping_add" => some "+"
  | "Sub" | "sub" | "wrapping_sub" => some "-"
  | "Mul" | "mul" | "wrapping_mul" => some "*"
  | "Div" | "div"                  => some "/"
  | "Rem" | "rem"                  => some "%"
  | "Shl" | "Shl#32" | "Shl#16" | "Shl#64"   => some "<<"
  | "Shr" | "Shr#32" | "Shr#16" | "Shr#64"   => some ">>"
  | "BitAnd" | "BitAnd#32" | "BitAnd#16" | "BitAnd#64" => some "&"
  | "BitOr"  | "BitOr#32"  | "BitOr#16"  | "BitOr#64"  => some "|"
  | "BitXor" | "BitXor#32" | "BitXor#16" | "BitXor#64" => some "^"
  | _                              => none

/-- Names that are width-casts (`cast#16`, `cast#32`, `cast#8`).  In
    Jasmin a cast is `(<n>u) x` / `(<n>s) x`; for our unsigned coefficient
    arithmetic we emit `(<width>u) x`.  Returns the bit-width string. -/
def jasminCastWidth (f : String) : Option String :=
  match f with
  | "cast#8"  => some "8u"
  | "cast#16" => some "16u"
  | "cast#32" => some "32u"
  | "cast#64" => some "64u"
  | _         => none

/-- Jasmin comparison operator for a comparison leaf-call name.  The
    hax extraction lowers `(X^n+1)` fold-down comparisons as
    `RCall <op> dst [a, b]` (e.g. `RCall "Lt" dst [idx, bound]`)
    immediately followed by an `RIfNz dst.locVar …`; jasminc has no
    such `Lt`/`Le`/… functions and wants a bool-valued `if (a < b)`
    rather than `t = Lt(a,b); if (t != 0)`.  Width-suffixed forms
    (`Lt#32`, `Lt#16`, …) map to the same operator.  Returns `none`
    for non-comparison names. -/
def jasminCmpOp (f : String) : Option String :=
  match f with
  | "Lt" | "lt" | "Lt#8" | "Lt#16" | "Lt#32" | "Lt#64" => some "<"
  | "Le" | "le" | "Le#8" | "Le#16" | "Le#32" | "Le#64" => some "<="
  | "Gt" | "gt" | "Gt#8" | "Gt#16" | "Gt#32" | "Gt#64" => some ">"
  | "Ge" | "ge" | "Ge#8" | "Ge#16" | "Ge#32" | "Ge#64" => some ">="
  | "Eq" | "eq" | "Eq#8" | "Eq#16" | "Eq#32" | "Eq#64" => some "=="
  | "Ne" | "ne" | "Ne#8" | "Ne#16" | "Ne#32" | "Ne#64" => some "!="
  | _                                                  => none

/-- Pretty-print the body of a `LowCT` as Jasmin pseudo-source,
    skipping declaration lines (handled by `ppJasminFunction`'s prelude). -/
partial def ppJasminBody (ind : Nat) : LowCT → String
  | .RSkip => ""
  | .RSeq c1 c2 =>
      -- Fuse a comparison leaf-call with an immediately-following
      -- `if`-on-its-result into a single bool-valued Jasmin `if`.
      -- The extraction emits `RSeq (RCall <op> d [a,b]) (RIfNz d.locVar ct cf)`
      -- for `(X^n+1)` fold-down conditionals; jasminc rejects both the
      -- unknown `Lt(…)` call and the `t != 0` test, so emit `if (a <op> b)`.
      -- The comparison var is a fresh single-use ANF slot, set then
      -- immediately tested, so dropping its assignment is safe.
      match c1, c2 with
      | .RCall op d [a, b], .RIfNz cv ct cf =>
          match jasminCmpOp op with
          | some jop =>
              if cv == d.locVar then
                let hdr := jasIndent ind
                  ("if (" ++ a.locVar ++ " " ++ jop ++ " " ++ b.locVar ++ ") {")
                let body1 := ppJasminBody (ind + 2) ct
                if cf matches .RSkip then
                  hdr ++ "\n" ++ body1 ++ "\n" ++ jasIndent ind "}"
                else
                  hdr ++ "\n" ++ body1 ++ "\n" ++ jasIndent ind "} else {" ++ "\n" ++
                  ppJasminBody (ind + 2) cf ++ "\n" ++ jasIndent ind "}"
              else
                let s1 := ppJasminBody ind c1
                let s2 := ppJasminBody ind c2
                if s1.isEmpty then s2
                else if s2.isEmpty then s1
                else s1 ++ "\n" ++ s2
          | none =>
              let s1 := ppJasminBody ind c1
              let s2 := ppJasminBody ind c2
              if s1.isEmpty then s2
              else if s2.isEmpty then s1
              else s1 ++ "\n" ++ s2
      | _, _ =>
          let s1 := ppJasminBody ind c1
          let s2 := ppJasminBody ind c2
          if s1.isEmpty then s2
          else if s2.isEmpty then s1
          else s1 ++ "\n" ++ s2
  | .RLetZero _ _ body =>
      -- Declaration handled at top; just recurse into the body.
      ppJasminBody ind body
  | .RLetU64Zero _ body =>
      ppJasminBody ind body
  | .RScalarSet x v =>
      jasIndent ind (x ++ " = " ++ toString v ++ ";")
  | .RIfNz e ct cf =>
      let hdr := jasIndent ind ("if (" ++ e ++ " != 0) {")
      let body1 := ppJasminBody (ind + 2) ct
      if cf matches .RSkip then
        hdr ++ "\n" ++ body1 ++ "\n" ++ jasIndent ind "}"
      else
        hdr ++ "\n" ++ body1 ++ "\n" ++ jasIndent ind "} else {" ++ "\n" ++
        ppJasminBody (ind + 2) cf ++ "\n" ++ jasIndent ind "}"
  | .RWhileNz e body =>
      jasIndent ind ("while (" ++ e ++ " != 0) {") ++ "\n" ++
      ppJasminBody (ind + 2) body ++ "\n" ++ jasIndent ind "}"
  | .RFor x n body =>
      if n > forLoopThreshold then
        -- Large bound: runtime `while` (reg counter) so jasminc doesn't
        -- unroll.  `x` is declared `reg u64` (via collectWhileCounters).
        jasIndent ind (x ++ " = 0;") ++ "\n" ++
        jasIndent ind ("while (" ++ x ++ " < " ++ toString n ++ ") {") ++ "\n" ++
        ppJasminBody (ind + 2) body ++ "\n" ++
        jasIndent (ind + 2) (x ++ " += 1;") ++ "\n" ++
        jasIndent ind "}"
      else
        -- Small bound: unrolled `for` (so reg-offset slices in the body
        -- still type-check — see `forLoopThreshold`).  `x` is `inline int`.
        jasIndent ind ("for " ++ x ++ " = 0 to " ++ toString n ++ " {") ++ "\n" ++
        ppJasminBody (ind + 2) body ++ "\n" ++ jasIndent ind "}"
  | .RForRuntime x bound body =>
      -- Runtime-bound loop: always a `while`-counter (bound is an SExpr,
      -- not a compile-time literal).  `x` is a `reg u64` counter.
      jasIndent ind (x ++ " = 0;") ++ "\n" ++
      jasIndent ind ("while (" ++ x ++ " < " ++ bound.ppJazz ++ ") {") ++ "\n" ++
      ppJasminBody (ind + 2) body ++ "\n" ++
      jasIndent (ind + 2) (x ++ " += 1;") ++ "\n" ++
      jasIndent ind "}"
  | .RCall f dest args =>
      -- Recognise arithmetic / bitwise / cast operator names emitted by
      -- the hax extraction and lower them to Jasmin infix / cast syntax.
      -- Leaf calls (poly_add, mat_vec_mul, …) fall through to the
      -- function-call form.
      match jasminBinOp f, jasminCastWidth f, args with
      | some op, _, [a, b] =>
          -- Jasmin reg arithmetic is *two-address* (`d op= b`).  Emitting
          -- a three-address `d = a op b` forces the register allocator to
          -- reuse `a`'s register for `d`; when `a` is still live (e.g.
          -- `idx = i + j` with the loop counter `i` live across the body)
          -- this raises "conflicting variables … must be merged".  Break
          -- it with an explicit copy.  ANF freshness ⇒ `d ≠ b`, so the
          -- copy never clobbers the second operand.
          if dest.locVar == a.locVar then
            jasIndent ind (dest.locVar ++ " " ++ op ++ "= " ++ b.locVar ++ ";")
          else
            jasIndent ind (dest.locVar ++ " = " ++ a.locVar ++ ";") ++ "\n" ++
            jasIndent ind (dest.locVar ++ " " ++ op ++ "= " ++ b.locVar ++ ";")
      | _, some w, [a] =>
          jasIndent ind (dest.locVar ++ " = (" ++ w ++ ") " ++ a.locVar ++ ";")
      | _, _, _ =>
          -- `repeat(v, n)` is an array-fill: emit `dst = #init` so the
          -- slot is zero/constant-initialised.  (jasminc accepts an
          -- array slot left to its declared zero; we use a no-op assign
          -- comment to document intent without an unsupported builtin.)
          if f == "repeat" || f == "repeat_" then
            jasIndent ind ("// " ++ dest.locVar ++ " = repeat(...) — array " ++
                           "pre-zeroed at declaration")
          else
            let argStr := String.intercalate ", " (args.map (·.locVar))
            jasIndent ind (dest.locVar ++ " = " ++ f ++ "(" ++ argStr ++ ");")
  | .RCallSwap f dest1 dest2 args =>
      let argStr := String.intercalate ", " (args.map (·.locVar))
      jasIndent ind (dest1.locVar ++ ", " ++ dest2.locVar ++
                     " = " ++ f ++ "(" ++ argStr ++ ");")
  | .RCloneCall _cv _t oldDest innerF dest args =>
      let argStr := String.intercalate ", " (args.map (·.locVar))
      jasIndent ind (dest.locVar ++ " = " ++ innerF ++ "(" ++ oldDest.locVar ++
                     (if args.isEmpty then "" else ", " ++ argStr) ++ ");")
  | .RLimbStore loc idx v =>
      jasIndent ind (loc.locVar ++ "[" ++ toString idx ++ "] = " ++
                     toString v.toNat ++ ";")
  | .RLimbStoreExpr loc idx e =>
      jasIndent ind (loc.locVar ++ "[" ++ toString idx ++ "] = " ++
                     e.ppJazz ++ ";")
  | .RCallN f dests args =>
      let dStr := String.intercalate ", " (dests.map (·.locVar))
      let aStr := String.intercalate ", " (args.map (·.locVar))
      jasIndent ind (dStr ++ " = " ++ f ++ "(" ++ aStr ++ ");")
  | .RSelect dst sel src0 src1 =>
      -- Jasmin idiom: `dst = (sel == 0) ? src0 : src1` is normally
      -- implemented via `?{f}=...` cmov; we emit the high-level form
      -- so the developer can refine it.
      jasIndent ind (dst.locVar ++ " = (" ++ sel ++ " == 0) ? " ++
                     src0.locVar ++ " : " ++ src1.locVar ++ ";")
  | .RAssert _ => ""
  | .RBlock body =>
      jasIndent ind "{" ++ "\n" ++ ppJasminBody (ind + 2) body ++ "\n" ++
      jasIndent ind "}"
  | .RFnDef name params returns body cont =>
      -- Nested inline fn declaration.  Recurse into the body as a
      -- sub-pretty-print, then emit the continuation.
      let paramStr := String.intercalate ", "
        (params.map (fun p => jasminTowerType p.locSrc ++ " " ++ p.locVar))
      let resultStr := String.intercalate ", "
        (returns.map (fun r => jasminTowerType r.locSrc ++ " " ++ r.locVar))
      let allParams :=
        if params.isEmpty then resultStr
        else if returns.isEmpty then paramStr
        else paramStr ++ ", " ++ resultStr
      let innerDecls := collectLetZeros body
      let innerU64s  := collectLetU64s body
      let declLines :=
        (innerU64s.map (fun n => jasIndent (ind + 2) ("reg u64 " ++ n ++ ";"))) ++
        (innerDecls.map (fun (n, t) =>
          jasIndent (ind + 2)
            (jasminTowerType t ++ " " ++ n ++ ";  // " ++ jasminTowerComment t)))
      let declBlock :=
        if declLines.isEmpty then "" else String.intercalate "\n" declLines ++ "\n"
      jasIndent ind ("inline fn " ++ name ++ "(" ++ allParams ++ ") {") ++ "\n" ++
      declBlock ++
      ppJasminBody (ind + 2) body ++ "\n" ++
      jasIndent ind "}" ++ "\n" ++
      ppJasminBody ind cont
  | .RFnCall f dests args =>
      let dStr := String.intercalate ", " (dests.map (·.locVar))
      let aStr := String.intercalate ", " (args.map (·.locVar))
      jasIndent ind (dStr ++ " = " ++ f ++ "(" ++ aStr ++ ");")
  | .RTupleLoad dst src idx =>
      jasIndent ind (dst.locVar ++ " = " ++ src.locVar ++ "[" ++
                     toString idx ++ "];")
  | .RArrStore arr idxVar src =>
      -- Slice-aware store: if EITHER side is a known polyvec/polymat or
      -- its element type, emit slice syntax instead of single-element
      -- indexing (jasminc rejects `arr[i] = src` when both sides are
      -- arrays).  The source-side fallback handles cases where the
      -- typed pipeline can identify `src` but the container slot got
      -- shadowed by an upstream alias (untyped `let r = ZERO_VEC`).
      match arr.locSrc, src.locSrc with
      | .TPolyVec _ n _, _ =>
          -- polyvec[i] ← polynomial slice of length n
          jasIndent ind (arr.locVar ++ "[" ++ idxVar ++ "*" ++ toString n ++
                         " : " ++ toString n ++ "] = " ++ src.locVar ++ ";")
      | .TPolyMat _ n _ m, _ =>
          -- polymat[i] ← polyvec slice of length n*m
          jasIndent ind (arr.locVar ++ "[" ++ idxVar ++ "*" ++ toString (n*m) ++
                         " : " ++ toString (n*m) ++ "] = " ++ src.locVar ++ ";")
      | _, .TPolyMod _ n =>
          -- Source-side hint: storing a polynomial of length n means
          -- the container must be a polyvec.  Stride = n.
          jasIndent ind (arr.locVar ++ "[" ++ idxVar ++ "*" ++ toString n ++
                         " : " ++ toString n ++ "] = " ++ src.locVar ++ ";")
      | _, .TPolyVec _ n _ =>
          -- Source-side hint: storing a polyvec into a polymat.
          -- We can't determine `m` from the src alone (`TPolyVec n m`
          -- gives the inner poly length but not the polymat row count).
          -- Conservatively assume the container is a polymat whose rows
          -- are this exact polyvec; stride = n * (k of the inner type).
          -- Here we only have the inner poly length, so fall back to n.
          jasIndent ind (arr.locVar ++ "[" ++ idxVar ++ "*" ++ toString n ++
                         " : " ++ toString n ++ "] = " ++ src.locVar ++ ";")
      | .TBytes _, .TFp =>
          -- Truncating store: writing a u16 coefficient (`TFp`) into a
          -- u8 byte buffer.  jasminc rejects the implicit u16→u8 cast,
          -- so emit an explicit `(8u)` truncation.  This is the byte-
          -- serialization shape (byte_encode_12 / poly_compress_du).
          jasIndent ind (arr.locVar ++ "[" ++ idxVar ++ "] = (8u) " ++
                         src.locVar ++ ";")
      | _, _ =>
          -- scalar element: keep historical single-element store.
          jasIndent ind (arr.locVar ++ "[" ++ idxVar ++ "] = " ++
                         src.locVar ++ ";")
  | .RArrLoad dst src idxVar =>
      -- Symmetric to `RArrStore` — polyvec/matrix loads must emit slice
      -- syntax so jasminc can type-check `stack u16[256] = stack u16[768][...]`.
      -- Slice-aware load: prefer `src.locSrc` (the container type), but
      -- accept `dst.locSrc` as a fallback when the container slot has
      -- been shadowed by an alias.
      match src.locSrc, dst.locSrc with
      | .TPolyVec _ n _, _ =>
          -- polyvec[i] → polynomial slice of length n
          jasIndent ind (dst.locVar ++ " = " ++ src.locVar ++ "[" ++ idxVar ++
                         "*" ++ toString n ++ " : " ++ toString n ++ "];")
      | .TPolyMat _ n _ m, _ =>
          -- polymat[i] → polyvec slice of length n*m
          jasIndent ind (dst.locVar ++ " = " ++ src.locVar ++ "[" ++ idxVar ++
                         "*" ++ toString (n*m) ++ " : " ++ toString (n*m) ++ "];")
      | _, .TPolyMod _ n =>
          -- Destination-side hint: loading into a poly slot of length n
          -- means the source must be a polyvec with stride n.
          jasIndent ind (dst.locVar ++ " = " ++ src.locVar ++ "[" ++ idxVar ++
                         "*" ++ toString n ++ " : " ++ toString n ++ "];")
      | _, .TPolyVec _ n _ =>
          -- Destination-side hint: loading into a polyvec slot.
          jasIndent ind (dst.locVar ++ " = " ++ src.locVar ++ "[" ++ idxVar ++
                         "*" ++ toString n ++ " : " ++ toString n ++ "];")
      | _, _ =>
          -- scalar element: single-element load.  Bare `[idx]` works for
          -- both inline-int (for) and reg (while) index vars.
          jasIndent ind (dst.locVar ++ " = " ++ src.locVar ++ "[" ++
                         idxVar ++ "];")
  | .RScalarSetExpr x e =>
      -- Use the Jasmin surface pretty-printer, not `ppRust`.  The Rust
      -- pretty-printer emits `.saturating_sub(...)`, `0u64`, etc. which
      -- jasminc rejects; `ppJazz` emits plain `-`, suffix-less literals.
      jasIndent ind (x ++ " = " ++ e.ppJazz ++ ";")
  | .RArrStoreLit arr idx src =>
      -- Literal-index store: `arr[idx] = src;`.  This is the constant-
      -- index sibling of `RArrStore`; the slice-aware container logic of
      -- the var-index path doesn't apply (a literal index addresses a
      -- single element, not a polyvec/polymat row).
      jasIndent ind (arr.locVar ++ "[" ++ toString idx ++ "] = " ++
                     src.locVar ++ ";")
  | .RArrLoadLit dst src idx =>
      -- Literal-index load: `dst = src[idx];`.
      jasIndent ind (dst.locVar ++ " = " ++ src.locVar ++ "[" ++
                     toString idx ++ "];")
  | .RCallDstThreaded f dst args =>
      -- Dst-threaded leaf call: `dst = f(dst, args)` (the destination
      -- slot is both the first argument and the receiving lvalue — the
      -- MQ/lattice in-place ABI).
      let argStr := String.intercalate ", " (dst.locVar :: args.map (·.locVar))
      jasIndent ind (dst.locVar ++ " = " ++ f ++ "(" ++ argStr ++ ");")
  | .RCopy dst src =>
      -- Whole-array copy: `dst = #copy(src);`.
      jasIndent ind (dst.locVar ++ " = #copy(" ++ src.locVar ++ ");")

/-- Select the accumulator slots that need an explicit zeroing
    prologue, from a list of `(name, TowerType)` candidates (the body's
    `RLetZero` slots plus result slots).  A slot needs zeroing iff it is
    an array type, is *read* somewhere (`collectArrReadSlots`), and is
    *not* fully overwritten by a slice-copy (`collectArrLoadDsts`).  This
    catches the negacyclic accumulator `r` in `poly_mul` (read via
    `r[idx]`) and `acc` in `polyvec_dot` (read as a `poly_add` argument),
    while leaving slice-copy transients and write-only results alone. -/
def selectZeroSlots (c : LowCT) (cands : List (String × TowerType)) :
    List (String × Nat) :=
  let readers := collectArrReadSlots c
  let fullWritten := collectArrLoadDsts c
  cands.filterMap (fun (n, t) =>
    match t.arrayCellCount with
    | some cnt =>
        if readers.contains n && !fullWritten.contains n then some (n, cnt) else none
    | none => none)

/-- Emit the zeroing prologue (one `while`-loop per slot, sharing a
    `reg u64 _zinit` counter declared by the caller).  Jasmin does not
    implicitly zero stack slots and the verified pipeline drops the
    `repeat(0, n)` initialiser, so accumulators must be zeroed here. -/
def zeroPrologue (slots : List (String × Nat)) : String :=
  if slots.isEmpty then ""
  else
    String.intercalate "\n" (slots.map (fun (n, cnt) =>
      jasIndent 2 "_zinit = 0;" ++ "\n" ++
      jasIndent 2 ("while (_zinit < " ++ toString cnt ++ ") {") ++ "\n" ++
      jasIndent 4 (n ++ "[_zinit] = 0;") ++ "\n" ++
      jasIndent 4 "_zinit += 1;" ++ "\n" ++
      jasIndent 2 "}")) ++ "\n"

/-! ## §3b Width inference

The hax extraction computes ML-KEM coefficient arithmetic in `u32`
(e.g. `poly_mul`'s accumulator is `let mut r = [0u32; 256]` and
`prod = a[i] as u32 * b[j] as u32`), truncating back to `u16` only at
the final `out[k] = r[k] as u16`.  The verified `haxToLowCT` types
these slots over the *abstract* field (`TPolyMod`/`TFp`), which the
default lowering renders as `u16`.  That silently truncates the `u32`
product before the mod-q reduction.

The body statements already carry the explicit `cast#32`/`cast#16`
nodes, so the only thing wrong is the *declared slot widths*.  This
pass infers the right Jasmin register width per slot and the pretty
printer emits declarations at that width; `ppJasminBody` is unchanged. -/

/-- Default Jasmin element width (bits) for a tower type. -/
def towerElemWidth : TowerType → Nat
  | .TU8                  => 8
  | .TU32                 => 32
  | .TU64                 => 64
  | .TBytes _             => 8
  | .TPolyMod q _         => if q < 65536 then 16 else 32
  | .TPolyVec q _ _       => if q < 65536 then 16 else 32
  | .TPolyMat q _ _ _     => if q < 65536 then 16 else 32
  | _                     => 16

/-- An associative `name → width` map (small kernels — linear ops). -/
abbrev WMap := List (String × Nat)

def WMap.get (m : WMap) (k : String) : Nat := (m.find? (·.1 == k)).elim 16 (·.2)
def WMap.set (m : WMap) (k : String) (v : Nat) : WMap :=
  (k, v) :: m.filter (·.1 != k)
def WMap.bump (m : WMap) (k : String) (v : Nat) : WMap :=
  m.set k (max (m.get k) v)

/-- Collect every `cast#N` destination — these are *pinned* to width `N`
    and never raised by arithmetic unification (a `cast#16` is a
    truncation boundary). -/
partial def collectCastDests : LowCT → List String
  | .RSeq c1 c2                    => collectCastDests c1 ++ collectCastDests c2
  | .RLetZero _ _ body             => collectCastDests body
  | .RLetU64Zero _ body            => collectCastDests body
  | .RIfNz _ ct cf                 => collectCastDests ct ++ collectCastDests cf
  | .RWhileNz _ body               => collectCastDests body
  | .RFor _ _ body                 => collectCastDests body
  | .RForRuntime _ _ body          => collectCastDests body
  | .RCall f dst _                 => if (jasminCastWidth f).isSome then [dst.locVar] else []
  | .RBlock body                   => collectCastDests body
  | .RFnDef _ _ _ _ cont           => collectCastDests cont
  | _                              => []

/-- One forward pass of the width-propagation rules over the body.
    `pinned` is the set of `cast#N` destinations (set elsewhere, never
    raised here). -/
partial def widthPass (pinned : List String) (m : WMap) : LowCT → WMap
  | .RSeq c1 c2                    => widthPass pinned (widthPass pinned m c1) c2
  | .RLetZero _ _ body             => widthPass pinned m body
  | .RLetU64Zero _ body            => widthPass pinned m body
  | .RIfNz _ ct cf                 => widthPass pinned (widthPass pinned m ct) cf
  | .RWhileNz _ body               => widthPass pinned m body
  | .RFor _ _ body                 => widthPass pinned m body
  | .RForRuntime _ _ body          => widthPass pinned m body
  | .RBlock body                   => widthPass pinned m body
  | .RFnDef _ _ _ _ cont           => widthPass pinned m cont
  | .RCall f dst args              =>
      match jasminCastWidth f, jasminBinOp f, jasminCmpOp f, args with
      | some w, _, _, _ =>
          -- cast#w: pin destination to width w (overwrite).  `w` is the
          -- Jasmin width string ("8u"/"16u"/"32u"/"64u"); drop the `u`.
          m.set dst.locVar ((w.dropEnd 1).toString.toNat!)
      | _, some _, _, [a, b] =>
          -- arithmetic: dst, a, b share a width = max of the three;
          -- raise the non-pinned members to that width.
          let mx := max (m.get dst.locVar) (max (m.get a.locVar) (m.get b.locVar))
          let m := if pinned.contains dst.locVar then m else m.set dst.locVar mx
          let m := if pinned.contains a.locVar then m else m.set a.locVar mx
          if pinned.contains b.locVar then m else m.set b.locVar mx
      | _, _, some _, [a, b] =>
          -- comparison: operands share a width.
          let mx := max (m.get a.locVar) (m.get b.locVar)
          let m := if pinned.contains a.locVar then m else m.set a.locVar mx
          if pinned.contains b.locVar then m else m.set b.locVar mx
      | _, _, _, _ => m
  | .RArrLoad dst src _            => m.bump dst.locVar (m.get src.locVar)
  | .RArrStore arr _ src           => m.bump arr.locVar (m.get src.locVar)
  | .RCopy dst src                 => m.bump dst.locVar (m.get src.locVar)
  | _                              => m

/-- Infer a Jasmin register width for every slot in the body.  Seeds:
    index variables at 64 (Jasmin array indices), each `cast#N` dest at
    `N`, and every param/result/letZero array slot at its declared tower
    width.  Iterates the propagation rules to a fixpoint (8 passes is
    ample for ML-KEM kernels' short def-use chains). -/
def inferWidths (c : LowCT) (params results : List Located) : WMap :=
  let castDests := collectCastDests c
  let seedSlots : WMap :=
    (params ++ results).map (fun l => (l.locVar, towerElemWidth l.locSrc)) ++
    (collectLetZeros c).map (fun (n, t) => (n, towerElemWidth t)) ++
    (collectIndexVars c).map (fun n => (n, 64))
  -- `WMap.get` takes the first binding, so index/cast seeds (prepended
  -- last) win over the array seeds for shared names.
  let m0 : WMap := castDests.foldl (fun m d => m.set d 32) seedSlots
  -- Re-pin index vars after cast seeds so they stay 64.
  let m0 : WMap := (collectIndexVars c).foldl (fun m n => m.set n 64) m0
  (List.range 8).foldl (fun m _ => widthPass castDests m c) m0

/-- Render a tower type's Jasmin declaration at an inferred width `w`,
    overriding the default element width.  Scalars become `reg uW`;
    arrays keep their cell count but use width `W`. -/
def renderAtWidth (t : TowerType) (w : Nat) : String :=
  match t with
  | .TFp | .TU8 | .TU32 | .TU64 => "reg u" ++ toString w
  | .TPolyMod _ n         => "stack u" ++ toString w ++ "[" ++ toString n ++ "]"
  | .TPolyVec _ n k       => "stack u" ++ toString w ++ "[" ++ toString (k * n) ++ "]"
  | .TPolyMat _ n k m     => "stack u" ++ toString w ++ "[" ++ toString (k * m * n) ++ "]"
  | .TBytes n             => "stack u" ++ toString w ++ "[" ++ toString n ++ "]"
  | _                     => jasminTowerType t

/-! ## §4 Function emit

Top-level `LowCT → Jasmin .jazz string` entry point.  Produces:

```
// Auto-generated from LowCT via RustEmitJazz.  Edit by hand only
// to splice in the appropriate `.jinc` include lines.
//
// Tower-type lowering: TPolyMod q n → stack u{16,32}[n]; TPolyVec q n
// k → stack u{16,32}[k*n]; TBytes n → stack u8[n]; etc.

inline fn <name>(<jasmin-typed params>, <jasmin-typed results>) {
  <stack u… [N]> v1;  // <tower-type comment>
  <stack u… [N]> v2;  // <tower-type comment>
  ...
  reg u64 s1;
  reg u64 s2;
  ...

  <body>
}
```

Function results are passed as `&mut`-equivalent parameters (Jasmin
convention for inline calls).  No `return` statement — outputs are
written via the result-slot parameters.
-/

/-- Emit a complete Jasmin function definition for a `LowCT`.
    Params and results are passed as parameters (Jasmin doesn't
    distinguish call-by-reference vs call-by-value at this level —
    both are stack/reg slots).

    `kind` controls the function qualifier: `"inline"` for helper
    bodies inlined at every call site (default), `"export"` for
    top-level entry points callable from C / Rust (required when
    benching a kernel through FFI). -/
def ppJasminFunctionKind (kind : String) (name : String)
    (params : List Located) (results : List Located)
    (c : LowCT) : String :=
  let paramStr := String.intercalate ", "
    (params.map (fun p => jasminTowerType p.locSrc ++ " " ++ p.locVar))
  let resultStr := String.intercalate ", "
    (results.map (fun r => jasminTowerType r.locSrc ++ " " ++ r.locVar))
  let allParams :=
    if params.isEmpty then resultStr
    else if results.isEmpty then paramStr
    else paramStr ++ ", " ++ resultStr
  -- Collect local declarations.  Filter out names that are already
  -- function parameters (caller-provided slots) so we don't shadow them.
  let paramNames := params.map (·.locVar) ++ results.map (·.locVar)
  -- Inferred Jasmin register widths (u32 accumulators, u16 coefficients,
  -- u64 indices).  Local decls render at the inferred width.
  let W := inferWidths c params results
  -- Index accumulators (`idx = i + j`, used as `r[idx]`) must be `reg
  -- u64`, not their inferred `TFp`/`reg u16` slot — Jasmin rejects a
  -- u16 index at linearization.  Force them via `collectIndexVars`.
  let idxVars := collectIndexVars c
  -- Dedup `letZeros` by name: the same accumulator (`acc`) can be
  -- re-bound by several `RLetZero`s along the body, and jasminc rejects
  -- a duplicate declaration.
  let dedupNamed : List (String × TowerType) → List (String × TowerType) :=
    (·.foldr (fun nt acc => if acc.any (·.1 == nt.1) then acc else nt :: acc) [])
  let letZeros := dedupNamed ((collectLetZeros c).filter
    (fun (n, _) => !paramNames.contains n && !idxVars.contains n))
  let idxLetZeros := (collectLetZeros c).filterMap
    (fun (n, _) => if !paramNames.contains n && idxVars.contains n then some n else none)
  let letU64s  := (collectLetU64s c).filter (fun n => !paramNames.contains n)
  -- Jasmin requires `inline int <i>;` declarations at function top
  -- for every `for`-loop index.  Dedup since the same index name may
  -- appear in multiple unrelated loops.
  let dedup := (·.foldr (fun n acc => if List.contains acc n then acc else n :: acc) [])
  let forIdxs : List String :=
    dedup ((collectForIndices c).filter (fun n => !paramNames.contains n))
  let whileIdxs : List String :=
    dedup ((collectWhileCounters c).filter (fun n => !paramNames.contains n))
  let idxU64DeclLines := (dedup idxLetZeros).map
    (fun n => "  reg u64 " ++ n ++ ";  // array index")
  let u64DeclLines := letU64s.map (fun n => "  reg u" ++ toString (W.get n) ++ " " ++ n ++ ";")
    ++ idxU64DeclLines
  let stackDeclLines := letZeros.map (fun (n, t) =>
    "  " ++ renderAtWidth t (W.get n) ++ " " ++ n ++ ";  // " ++ jasminTowerComment t)
  let forIdxDecl : List String :=
    if forIdxs.isEmpty then []
    else ["  inline int " ++ String.intercalate " " forIdxs ++ ";"]
  let whileIdxDecl : List String :=
    whileIdxs.map (fun n => "  reg u64 " ++ n ++ ";  // while-loop counter")
  -- Zeroing prologue for accumulator slots (results may also accumulate).
  let zeroSlots := selectZeroSlots c (letZeros ++ results.map (fun r => (r.locVar, r.locSrc)))
  let zinitDecl : List String :=
    if zeroSlots.isEmpty then [] else ["  reg u64 _zinit;  // zeroing counter"]
  let declBlock :=
    if u64DeclLines.isEmpty && stackDeclLines.isEmpty && forIdxDecl.isEmpty
       && whileIdxDecl.isEmpty && zinitDecl.isEmpty then ""
    else String.intercalate "\n"
           (forIdxDecl ++ whileIdxDecl ++ zinitDecl ++ u64DeclLines ++ stackDeclLines) ++ "\n\n"
  let header :=
    "// Auto-generated from LowCT via RustEmitJazz.\n" ++
    "// Tower-type lowering: TPolyMod q n → stack u{16,32}[n];\n" ++
    "//   TPolyVec q n k → stack u{16,32}[k*n]; TBytes n → stack u8[n].\n" ++
    "// Splice in the appropriate `.jinc` include lines for leaf\n" ++
    "// primitives before passing through `jasminc`.\n\n"
  header ++
  kind ++ " fn " ++ name ++ "(" ++ allParams ++ ") {\n" ++
  declBlock ++
  zeroPrologue zeroSlots ++
  ppJasminBody 2 c ++ "\n}\n"

/-- Return-value calling-convention variant.  Emits

    ```
    inline fn name(<input params>) -> <result types> {
      <result slots as locals> <other locals>
      <body>
      return <result names>;
    }
    ```

    This matches the call-site shape `RCall` produces
    (`dst = f(args)` in `ppJasminBody`), so functions emitted this way
    are composable: a kernel calling `__t = poly_add(a, b)` links
    against a `poly_add` emitted here.  (The param-style
    `ppJasminFunctionKind` emits results as trailing void params, which
    only works for top-level entry points whose results are written
    in-place, not for callees invoked via `x = f(...)`.) -/
def ppJasminFunctionRet (name : String)
    (params : List Located) (results : List Located)
    (c : LowCT) : String :=
  -- Result slots become locals (declared + returned), not params.
  let paramStr := String.intercalate ", "
    (params.map (fun p => jasminTowerType p.locSrc ++ " " ++ p.locVar))
  let retTyStr := String.intercalate ", " (results.map (fun r => jasminTowerType r.locSrc))
  let retNames := String.intercalate ", " (results.map (·.locVar))
  let arrow := if results.isEmpty then "" else " -> " ++ retTyStr
  let retStmt := if results.isEmpty then "" else "\n  return " ++ retNames ++ ";"
  -- Locals: the body's RLetZero / RLetU64Zero slots, PLUS the result
  -- slots (which are written by the body but not passed as params here).
  let paramNames := params.map (·.locVar)
  let resultNames := results.map (·.locVar)
  -- The result slot's declared TowerType is authoritative.  When a result
  -- name is *also* re-bound by an `RLetZero` in the body (e.g. the function
  -- result `r : TPolyMod 3329 256` is re-bound `let r = repeat(0, 256)`,
  -- which the translator types `.TFp`), the body letZero would otherwise
  -- shadow the result with `reg u16 r` instead of `stack u16[256] r`, and
  -- jasminc rejects the subsequent `r[idx]` indexing.  Filter the body
  -- letZeros to exclude *both* param and result names, and always emit the
  -- result decl from its own `Located.locSrc`.
  let idxVars := collectIndexVars c
  -- Inferred Jasmin register widths: u32 for the coefficient accumulator
  -- and product chain, u16 for plain coefficients, u64 for indices.
  let W := inferWidths c params results
  let dedupNamed : List (String × TowerType) → List (String × TowerType) :=
    (·.foldr (fun nt acc => if acc.any (·.1 == nt.1) then acc else nt :: acc) [])
  let letZeros := dedupNamed ((collectLetZeros c).filter
    (fun (n, _) => !paramNames.contains n && !resultNames.contains n && !idxVars.contains n))
  let idxLetZeros := (collectLetZeros c).filterMap
    (fun (n, _) =>
      if !paramNames.contains n && !resultNames.contains n && idxVars.contains n
      then some n else none)
  let letU64s  := (collectLetU64s c).filter (fun n => !paramNames.contains n)
  let dedup := (·.foldr (fun n acc => if List.contains acc n then acc else n :: acc) [])
  let forIdxs : List String :=
    dedup ((collectForIndices c).filter (fun n => !paramNames.contains n))
  let whileIdxs : List String :=
    dedup ((collectWhileCounters c).filter (fun n => !paramNames.contains n))
  let idxU64DeclLines := (dedup idxLetZeros).map
    (fun n => "  reg u64 " ++ n ++ ";  // array index")
  -- All result slots are declared from their own (authoritative) tower type.
  let resultDecls := results
  let u64DeclLines := letU64s.map (fun n => "  reg u" ++ toString (W.get n) ++ " " ++ n ++ ";")
    ++ idxU64DeclLines
  let resultDeclLines := resultDecls.map (fun r =>
    "  " ++ jasminTowerType r.locSrc ++ " " ++ r.locVar ++ ";  // result")
  let stackDeclLines := letZeros.map (fun (n, t) =>
    "  " ++ renderAtWidth t (W.get n) ++ " " ++ n ++ ";  // " ++ jasminTowerComment t)
  let forIdxDecl : List String :=
    if forIdxs.isEmpty then []
    else ["  inline int " ++ String.intercalate " " forIdxs ++ ";"]
  let whileIdxDecl : List String :=
    whileIdxs.map (fun n => "  reg u64 " ++ n ++ ";  // while-loop counter")
  -- Zeroing prologue for accumulator slots (result slots may accumulate,
  -- e.g. `acc` in `polyvec_dot`), plus the shared `_zinit` counter.
  let zeroSlots := selectZeroSlots c
    (letZeros ++ results.map (fun r => (r.locVar, r.locSrc)))
  let zinitDecl : List String :=
    if zeroSlots.isEmpty then [] else ["  reg u64 _zinit;  // zeroing counter"]
  let allDecls := forIdxDecl ++ whileIdxDecl ++ zinitDecl ++ u64DeclLines ++
    resultDeclLines ++ stackDeclLines
  let declBlock :=
    if allDecls.isEmpty then "" else String.intercalate "\n" allDecls ++ "\n\n"
  let header :=
    "// Auto-generated from LowCT via RustEmitJazz (return-value form).\n\n"
  header ++
  "inline fn " ++ name ++ "(" ++ paramStr ++ ")" ++ arrow ++ " {\n" ++
  declBlock ++
  zeroPrologue zeroSlots ++
  ppJasminBody 2 c ++ retStmt ++ "\n}\n"

/-- Inline-fn variant (helper bodies; emitted at every call site). -/
def ppJasminFunction (name : String)
    (params : List Located) (results : List Located)
    (c : LowCT) : String :=
  ppJasminFunctionKind "inline" name params results c

/-- Export-fn variant (top-level kernels callable from C / Rust). -/
def ppJasminFunctionExport (name : String)
    (params : List Located) (results : List Located)
    (c : LowCT) : String :=
  ppJasminFunctionKind "export" name params results c

/-- Write a Jasmin function definition to disk (inline fn). -/
def writeJasminFunction (filename name : String)
    (params results : List Located) (c : LowCT) : IO Unit :=
  IO.FS.writeFile filename (ppJasminFunction name params results c)

/-- Write a Jasmin function definition to disk (export fn). -/
def writeJasminFunctionExport (filename name : String)
    (params results : List Located) (c : LowCT) : IO Unit :=
  IO.FS.writeFile filename (ppJasminFunctionExport name params results c)

end CatCrypt.Crypto.Jasmin.LowCT
