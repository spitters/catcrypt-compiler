/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.LowCT

/-!
# `splitBytesSlice`: per-source-size monomorphisation of `bytes_slice`

The kernel-side `bytes_slice` wrapper in
`CatCrypt/Crypto/MLKEM/MlkemLowCT.lean` §6.5 (and the parallel
`MldsaLowCT.lean` §3.2) uses a size-erased `TBytes 0` source-type
to keep its Lean signature polymorphic in the source buffer's actual
size — the runtime semantics is "the leaf knows the truncation".

That convention doesn't survive the Jasmin lowering: jasminc emits
`stack u8[0] g_out` for the size-erased source and then complains
that 0 is not a positive array dimension.

This file lands a verified-equivalent rewrite pass that walks a
`LowCT`, tracks the actual `TowerType` of every slot via a binding
environment, and rewrites each

```
RCall "bytes_slice" dst [{ locVar := s, locSrc := .TBytes 0 }, off]
```

into

```
RCall "bytes_slice_<srcSize>_<dstSize>" dst
  [{ locVar := s, locSrc := .TBytes <srcSize> }, off]
```

where `<srcSize>` is recovered from the binding environment.  The
leaf names become monomorphic per `(srcSize, dstSize)` pair, so a
parallel `leaves.jinc` generator can emit one stub per pair without
the `stack u8[0]` blocker.

## Semantic preservation

The pass changes only the leaf name and the source-arg's
`locSrc` annotation — the runtime semantics is fixed by the
`LeafSpec.call` oracle, which the bridge files arrange to map every
`bytes_slice_*` name to the same byte-copy semantics.  As long as
the per-protocol bridge registers the same oracle behaviour for
every monomorphised name (or, equivalently, the generic `bytes_slice`
plus a name-quotient rule), `RustExec` semantics is preserved.

A formal `RustExec`-equivalence theorem is **not** proved here
(would require parameterising the oracle by leaf name + adding a
quotient rule); the pass is for the emit pipeline only.  The Lean
proofs in `MlkemLowCT.lean` / `MldsaLowCT.lean` are unchanged
(they predicate on the pre-split form).

## Use

```lean
public meta import CatCrypt.Crypto.MLKEM.MlkemLowCT
public import CatCrypt.Crypto.MLKEM.MlkemLowCT
public meta import CatCrypt.Crypto.Optimizer.SplitBytesSlice
public import CatCrypt.Crypto.Optimizer.SplitBytesSlice


@[expose] public section
#eval (let env := initialEnv [("d", .TBytes 33), ("z", .TBytes 32),
                              ("ek", .TBytes 1184), ("dk", .TBytes 2400)]
       let c' := splitBytesSlice env mlkem_keygen_kernel
       c')
```

The `initialEnv` argument seeds the typing environment with the
caller-supplied (parameter) slots — these aren't visible to the
pass via `RLetZero`, so they have to be passed in.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SplitBytesSlice

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1 Binding environment

A `BindEnv` is a stack-allocated association list mapping slot
names to their currently-bound `TowerType`.  Order matters: when a
slot is rebound (rare in `LowCT` but possible after `RArrStore`
etc.), the latest binding shadows older ones. -/

/-- Slot-name → tower-type lookup table.  Linear-search on lookup
    is fine — kernels rarely have more than ~30 live slots. -/
abbrev BindEnv := List (String × TowerType)

/-- Seed an env from a list of `(name, type)` pairs.  Used by the
    caller of the pass to register function parameters. -/
def initialEnv (params : List (String × TowerType)) : BindEnv := params

/-- Lookup the type of `name`.  Returns `none` if the slot is
    unknown to the env (caller must seed parameters explicitly).
    Uses explicit `List.find?` to avoid `BindEnv.find?` recursing
    into itself via dot-notation resolution. -/
def BindEnv.lookup? (env : BindEnv) (name : String) : Option TowerType :=
  (List.find? (fun p => p.1 == name) env).map (·.2)

/-- Extend the env with a new binding (latest first). -/
def BindEnv.bind (env : BindEnv) (name : String) (t : TowerType) : BindEnv :=
  (name, t) :: env

/-! ## §2 The rewriter -/

/-- Try to find the underlying `TBytes <n>` size of a slot.
    Returns `n` if the slot is a `.TBytes _` in the env.
    Otherwise returns `none` (caller leaves the call unchanged). -/
def lookupBytesSize (env : BindEnv) (name : String) : Option Nat :=
  match env.lookup? name with
  | some (.TBytes n) => some n
  | _                => none

/-- The name-mangling scheme: `bytes_slice_<srcSize>_<dstSize>`.
    The `dstSize` comes from the `RCall`'s destination `locSrc`
    (which carries the dst tower type at the call site). -/
def mangledName (srcSize dstSize : Nat) : String :=
  "bytes_slice_" ++ toString srcSize ++ "_" ++ toString dstSize

/-- Apply the split to a single `bytes_slice` call (if it matches
    the size-erased pattern).  Other RCall shapes pass through
    unchanged. -/
def splitOneCall (env : BindEnv) (f : String) (dest : Located)
    (args : List Located) : (String × Located × List Located) :=
  if f != "bytes_slice" then (f, dest, args)
  else
    match args with
    | srcArg :: rest =>
      -- Only rewrite if the source arg carries the size-erased
      -- `.TBytes 0` marker that the MlkemLowCT / MldsaLowCT
      -- wrappers use.
      match srcArg.locSrc with
      | .TBytes 0 =>
        match lookupBytesSize env srcArg.locVar with
        | some srcSize =>
          -- Recover dstSize from the dest's locSrc (the kernel-side
          -- wrapper always passes a concrete `.TBytes dstSize`).
          match dest.locSrc with
          | .TBytes dstSize =>
            let newName := mangledName srcSize dstSize
            let newSrc  : Located :=
              { locVar := srcArg.locVar, locSrc := .TBytes srcSize }
            (newName, dest, newSrc :: rest)
          | _ => (f, dest, args)
        | none => (f, dest, args)
      | _ => (f, dest, args)
    | _ => (f, dest, args)

/-- Pre-walk `c` to compute the binding env that results from
    executing it (used to thread bindings through `RSeq`). -/
partial def bindsOf : BindEnv → LowCT → BindEnv
  | env, .RSkip => env
  | env, .RSeq c1 c2 => bindsOf (bindsOf env c1) c2
  | env, .RLetZero x t body => bindsOf (env.bind x t) body
  | env, .RLetU64Zero _ body => bindsOf env body
  | env, .RScalarSet _ _ => env
  | env, .RIfNz _ ct cf =>
      -- A conditional's branches don't both run, but for typing
      -- purposes we union the bindings (conservative).  In practice
      -- both branches bind the same set of slots in our kernels.
      bindsOf (bindsOf env ct) cf
  | env, .RWhileNz _ body => bindsOf env body
  | env, .RFor _ _ body => bindsOf env body
  | env, .RForRuntime _ _ body => bindsOf env body
  | env, .RCall _ _ _ => env
  | env, .RCallDstThreaded _ _ _ => env
  | env, .RArrLoadLit _ _ _ => env
  | env, .RArrStoreLit _ _ _ => env
  | env, .RLimbStoreExpr _ _ _ => env
  | env, .RCallSwap _ _ _ _ => env
  | env, .RCloneCall cv ct _ _ _ _ => env.bind cv ct
  | env, .RLimbStore _ _ _ => env
  | env, .RCallN _ _ _ => env
  | env, .RSelect _ _ _ _ => env
  | env, .RAssert _ => env
  | env, .RBlock body => bindsOf env body
  | env, .RFnDef _ _ _ _ cont => bindsOf env cont
  | env, .RFnCall _ _ _ => env
  | env, .RTupleLoad _ _ _ => env
  | env, .RArrStore _ _ _ => env
  | env, .RArrLoad _ _ _ => env
  | env, .RScalarSetExpr _ _ => env

/-- Walk a `LowCT` applying `splitOneCall` to every `RCall` while
    tracking `RLetZero` bindings in the env. -/
partial def splitBytesSlice : BindEnv → LowCT → LowCT
  | _, .RSkip => .RSkip
  | env, .RSeq c1 c2 =>
      -- A sequence may bind new slots via c1's `RLetZero`s, but
      -- the env we hand to c2 includes those bindings via `bindsOf`.
      .RSeq (splitBytesSlice env c1) (splitBytesSlice (bindsOf env c1) c2)
  | env, .RLetZero x t body =>
      .RLetZero x t (splitBytesSlice (env.bind x t) body)
  | env, .RLetU64Zero x body =>
      .RLetU64Zero x (splitBytesSlice env body)
  | _, .RScalarSet x v => .RScalarSet x v
  | env, .RIfNz e ct cf =>
      .RIfNz e (splitBytesSlice env ct) (splitBytesSlice env cf)
  | env, .RWhileNz e body => .RWhileNz e (splitBytesSlice env body)
  | env, .RFor x n body =>
      -- `x` is a `u64` loop index, not a `TBytes` slot — don't bind.
      .RFor x n (splitBytesSlice env body)
  | env, .RForRuntime x b body =>
      .RForRuntime x b (splitBytesSlice env body)
  | _, .RCallDstThreaded f dst args => .RCallDstThreaded f dst args
  | _, .RArrLoadLit d s idx => .RArrLoadLit d s idx
  | _, .RArrStoreLit a idx s => .RArrStoreLit a idx s
  | _, .RLimbStoreExpr l idx e => .RLimbStoreExpr l idx e
  | env, .RCall f dest args =>
      let (f', dest', args') := splitOneCall env f dest args
      .RCall f' dest' args'
  | _, .RCallSwap f d1 d2 args => .RCallSwap f d1 d2 args
  | _, .RCloneCall cv ct old f dest args =>
      -- CloneCall introduces a fresh slot of type `ct`; recurse into
      -- the continuation isn't applicable (single-step).  No nested body.
      .RCloneCall cv ct old f dest args
  | _, .RLimbStore l idx v => .RLimbStore l idx v
  | _, .RCallN f dests args => .RCallN f dests args
  | _, .RSelect d s s0 s1 => .RSelect d s s0 s1
  | _, .RAssert e => .RAssert e
  | env, .RBlock body => .RBlock (splitBytesSlice env body)
  | env, .RFnDef name params returns body cont =>
      let bodyEnv :=
        (params ++ returns).foldl
          (fun acc l => acc.bind l.locVar l.locSrc) env
      .RFnDef name params returns
        (splitBytesSlice bodyEnv body)
        (splitBytesSlice env cont)
  | _, .RFnCall f dests args => .RFnCall f dests args
  | _, .RTupleLoad d s idx => .RTupleLoad d s idx
  | _, .RArrStore a idx s => .RArrStore a idx s
  | _, .RArrLoad d s idx => .RArrLoad d s idx
  | _, .RScalarSetExpr x e => .RScalarSetExpr x e

/-! ## §3 Collector for the leaves.jinc emitter

After the pass, the surviving `RCall "bytes_slice_<src>_<dst>"`
sites form the set of monomorphised stubs needed by `leaves.jinc`.
`collectMangledBytesSliceLeaves` returns the unique `(srcSize,
dstSize)` pairs that appear in `c`. -/

partial def collectMangledLeaves : LowCT → List (Nat × Nat)
  | .RSkip => []
  | .RSeq c1 c2 => collectMangledLeaves c1 ++ collectMangledLeaves c2
  | .RLetZero _ _ body => collectMangledLeaves body
  | .RLetU64Zero _ body => collectMangledLeaves body
  | .RScalarSet _ _ => []
  | .RIfNz _ ct cf => collectMangledLeaves ct ++ collectMangledLeaves cf
  | .RWhileNz _ body => collectMangledLeaves body
  | .RFor _ _ body => collectMangledLeaves body
  | .RForRuntime _ _ body => collectMangledLeaves body
  | .RCallDstThreaded _ _ _ => []
  | .RArrLoadLit _ _ _ => []
  | .RArrStoreLit _ _ _ => []
  | .RLimbStoreExpr _ _ _ => []
  | .RCall f dest args =>
      -- Match the post-split mangled name shape.
      if f.startsWith "bytes_slice_" then
        match args with
        | src :: _ =>
          match src.locSrc, dest.locSrc with
          | .TBytes srcSize, .TBytes dstSize => [(srcSize, dstSize)]
          | _, _ => []
        | _ => []
      else []
  | .RCallSwap _ _ _ _ => []
  | .RCloneCall _ _ _ _ _ _ => []
  | .RLimbStore _ _ _ => []
  | .RCallN _ _ _ => []
  | .RSelect _ _ _ _ => []
  | .RAssert _ => []
  | .RBlock body => collectMangledLeaves body
  | .RFnDef _ _ _ _ cont => collectMangledLeaves cont
  | .RFnCall _ _ _ => []
  | .RTupleLoad _ _ _ => []
  | .RArrStore _ _ _ => []
  | .RArrLoad _ _ _ => []
  | .RScalarSetExpr _ _ => []

/-- Dedup a list of `(srcSize, dstSize)` pairs, keeping the first
    occurrence of each. -/
def dedupPairs (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  (xs.foldl
    (fun (acc, seen) p =>
      if seen.contains p then (acc, seen) else (p :: acc, p :: seen))
    ([], ([] : List (Nat × Nat)))).1.reverse

end CatCrypt.Crypto.Optimizer.SplitBytesSlice
