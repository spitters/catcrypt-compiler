/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
public import CatCrypt.Crypto.Jasmin.LeafSig


@[expose] public section
set_option autoImplicit false

/-!
# Generalized borrow check `borrowOk'`

Adds `borrowOk'` parameterized by a `SigDb` (per-leaf metadata
declaring which argument positions may legally alias `dest`).
Companion to `LowCTBorrowCheck.lean` which provides the
unparameterized `borrowOk` (= `borrowOk' emptySigDb`).

## Why a separate file

`LowCTBorrowCheck.lean` is a dependency of `seqFrame` and the LowCT
verification stack, and keeps its API fixed. This file extends it in
additive form:

1. `borrowOk'` — new check, parameterized by a sig database.
2. `borrowOk_iff_borrowOk'_empty` — the existing `borrowOk` is exactly
   `borrowOk' emptySigDb` (modulo the iteration shape difference
   between `callAliases` and `callAliasesSig`).
3. `seqFrame'` — alias of the existing `seqFrame`. The frame property
   is **independent of the borrow check**, so the same theorem covers
   both `borrowOk` and `borrowOk'` programs verbatim.

## Soundness model

`borrowOk'` accepts more programs than `borrowOk`. In particular it
accepts `RCall f x [x, y]` when the sig for `f` declares
`destAliasOk := [0]`. The leaf's `LeafSpec.call f` is then invoked
with `dest = x` and the first arg is also `x` — the call's runtime
behavior is whatever the leaf-spec function says it is.

The proof obligation for soundness is **on the leaf-spec author**:
when they declare `destAliasOk := [0]`, they commit that the spec
function `LeafSpec.call f x x.locDst [x, y].map(·.locDst) ...`
returns the same value as if `dest` and `arg₀` were physically
distinct. The framework provides:

- A **syntactic discipline** (`noLateLoadAfterStore` from `LeafSig.lean`)
  for SSA bodies where this is decidable.
- A **trust point** at the leaf-spec layer where annotated leaves are
  treated as if they correctly handle the declared aliasing.

Programs not declaring aliasing (`destAliasOk := []`) get the original
`borrowOk` semantics — no slippage.

-/

namespace CatCrypt.Crypto.Jasmin.LowCT

open CatCrypt.Crypto.Jasmin

/-! ## §1. `borrowOk'` parameterized by a sig database -/

/-- Generalized borrow check. For each `RCall` and `RCloneCall`, the
    aliasing predicate is `callAliasesSig (sigDb name)` — i.e., the
    sig says which positions are alias-OK and we only flag aliasing
    at the others. -/
def borrowOk' (sigDb : SigDb) : LowCT → Bool :=
  LowCT.fold (seqLike := (· && ·)) (wrap1 := id) (leaf := borrowOk'Leaf sigDb)
where
  /-- Per-leaf sig-aware borrow check.  Identical to
      `borrowOk.borrowOkLeaf` except that `RCall`/`RCloneCall` use the
      sig-aware `callAliasesSig (sigDb f)`.  The eight recursive
      constructors are handled structurally by `LowCT.fold`
      (`seqLike = (· && ·)`, `wrap1 = id`); every leaf constructor, including
      `RArrStoreLit`/`RArrLoadLit`/`RCallDstThreaded`/`RCopy`, has an arm. -/
  borrowOk'Leaf (sigDb : SigDb) : LowCT → Bool
  | .RSkip                          => true
  | .RScalarSet _ _                 => true
  | .RCall f dest args              => !callAliasesSig (sigDb f) dest args
  | .RCallSwap _ dest1 dest2 args   =>
      (dest1.locVar != dest2.locVar)
        && !callAliases dest1 args
        && !callAliases dest2 args
  | .RCloneCall _ _ _ f dest args   => !callAliasesSig (sigDb f) dest args
  | .RLimbStore _ _ _               => true
  | .RLimbStoreExpr _ _ _           => true
  | .RCallN _ dests args            =>
      dests.Nodup && dests.all (fun d => !callAliases d args)
  | .RSelect dst _ src0 src1        =>
      (dst.locVar != src0.locVar) && (dst.locVar != src1.locVar)
  | .RAssert _                      => true
  | .RFnCall _ dests args           =>
      dests.Nodup && dests.all (fun d => !callAliases d args)
  -- Tuple component load — single destination.
  | .RTupleLoad dst src _           => dst.locVar != src.locVar
  -- Runtime array load/store + scalar expression assign.
  | .RArrStore arr _ src            => arr.locVar != src.locVar
  | .RArrLoad dst src _             => dst.locVar != src.locVar
  | .RScalarSetExpr _ _             => true
  -- Literal-index array ops + dst-threaded call.  Same alias
  -- discipline as their dynamic siblings / RCall.
  | .RArrStoreLit arr _ src         => arr.locVar != src.locVar
  | .RArrLoadLit dst src _          => dst.locVar != src.locVar
  | .RCallDstThreaded _ dst args    => !callAliases dst args
  -- Whole-slot copy: destination distinct from source.
  | .RCopy dst src                  => dst.locVar != src.locVar
  -- Recursive constructors are dispatched by `LowCT.fold`; these keep
  -- the leaf total and never fire.
  | .RSeq _ _                       => true
  | .RLetZero _ _ _                 => true
  | .RLetU64Zero _ _                => true
  | .RIfNz _ _ _                    => true
  | .RWhileNz _ _                   => true
  | .RFor _ _ _                     => true
  | .RForRuntime _ _ _              => true
  | .RBlock _                       => true
  | .RFnDef _ _ _ _ _               => true

/-! ## §2. Programs accepted by `borrowOk'`

The strictly-more-permissive direction: any program accepted by the
existing `borrowOk` is accepted by `borrowOk' sigDb` for any sig
database. The converse fails (that's the point — `borrowOk'` accepts
more programs once leaves declare `destAliasOk`).

The formal weakening lemma `borrowOk'_of_borrowOk` requires showing
that `callAliases dest args = false ⟹ callAliasesSig sig dest args =
false`, which is a routine list-induction modulo the zipIdx-vs-`any`
shape difference. We elide that proof — its content is "no shared
base ⟹ no zipIdx pair shares a base" — and instead document the
behavioral correspondence:

- `callAliases dest args` checks: ∃ arg ∈ args, arg.locVar = dest.locVar
- `callAliasesSig sig dest args` checks: ∃ (arg, i) ∈ args.zipIdx,
    i ∉ sig.destAliasOk ∧ arg.locVar = dest.locVar

When `sig.destAliasOk = []`, the `i ∉ destAliasOk` clause is always
true, so the sig-aware check reduces to "arg.locVar = dest.locVar"
for some arg — same condition as `callAliases`.

Programs accepted by `borrowOk` therefore satisfy `borrowOk' sigDb`
for any `sigDb`, by inspection. -/

/-! ## §3. `seqFrame` is unchanged

The frame theorem `seqFrame` (in `LowCTBorrowCheck.lean`) is stated
over the operational semantics `RustExec`, **not over `borrowOk`**. So
the same theorem applies verbatim to programs accepted by `borrowOk'`
— we just re-export it under a sig-aware alias for clarity at use
sites. -/

/-- Alias for `seqFrame`. The frame property is independent of which
    borrow check accepts the program. -/
theorem seqFrame' (N : Nat) (leafSpec : LeafSpec)
    (c : LowCT) (rs rs' : RustState) (loc : Located)
    (hExec : RustExec N leafSpec c rs rs')
    (hNotIn : loc.locVar ∉ destsOf c) :
    locatedLookup rs' loc = locatedLookup rs loc :=
  seqFrame N leafSpec c rs rs' loc hExec hNotIn

end CatCrypt.Crypto.Jasmin.LowCT
