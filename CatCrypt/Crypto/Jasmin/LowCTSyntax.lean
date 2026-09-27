/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCTTypes
public import CatCrypt.Crypto.Jasmin.LowCTSExpr

/-!
# `LowCT` commands

The command syntax `LowCT` (`CatCrypt.Crypto.Jasmin.LowCT` re-exports it), the
derived vector statement `LowCT.RVsimdSetExpr`, and the structural folds
`LowCT.fold` and `LowCT.foldNode` with their reduction lemmas.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

/-! ## §3  Rust commands -/

/-- Safe Rust commands over tower-typed variables.

    Every `RCall` writes to `dest` and reads from `args`; the borrow
    checker (`borrowOk`) ensures `dest ∉ args` at every call site.

    `RCloneCall` breaks the alias by cloning the old destination value into
    a fresh variable before dispatching the inner call. -/
inductive LowCT where
  | RSkip      : LowCT
  | RSeq       : LowCT → LowCT → LowCT
  | RLetZero   : String → TowerType → LowCT → LowCT
  | RLetU64Zero : String → LowCT → LowCT
  | RScalarSet : String → Nat → LowCT
  | RCall      : String → Located → List Located → LowCT
  /-- 2-destination leaf call, used for cswap-style operations whose
      semantics mutate two field elements at once.  Emits as
      `f(&mut dest1, &mut dest2, &args…)`.  borrowOk requires
      `dest1 ≠ dest2` and neither in `args`.  The Rocq / `Com`
      semantics treats this as two independent writes; the leaf's
      Hoare spec must mention both destinations. -/
  | RCallSwap : String → Located → Located → List Located → LowCT
  | RCloneCall : String → TowerType → Located → String →
                 Located → List Located → LowCT
  | RIfNz      : String → LowCT → LowCT → LowCT
  | RWhileNz   : String → LowCT → LowCT
  /-- Bounded for-loop: `RFor x n body` runs `body` `n` times, with the
      scalar variable `x` set to `0, 1, …, n-1` on successive iterations.
      `n` is a closed Nat at the AST level — the loop is structurally
      terminating, no fuel needed. Authored to mirror Bedrock2's bounded
      `for`; the Hoare rule `RustExec.rfor_invariant` gives `0 ≤ x < n` as a free invariant. -/
  | RFor       : String → Nat → LowCT → LowCT
  | RLimbStore : Located → Nat → BitVec 64 → LowCT
  /-- **Runtime-valued limb store.**
      `RLimbStoreExpr loc idx e` writes the *runtime-computed* word
      `SExpr.eval e` (truncated to `BitVec 64`) into limb index `idx`
      of the tower slot `loc`.  This is the limb-indexed analogue of
      `RScalarSetExpr` (which stores a runtime `SExpr` into a *scalar*
      slot): `RLimbStore` only takes a compile-time literal `BitVec 64`,
      so an inline field-op body that stores a computed limb (e.g.
      `fe25519_add`'s `out[i] = a[i] + b[i]`) has no faithful image
      under `RLimbStore`.  `RLimbStoreExpr` closes that gap and is the
      structural correspondent of AUCurves' Rocq `REdLimbStore : … →
      sexpr_ed → …` constructor (which stores a runtime sexpr value).
      Lowering / oracle treatment mirrors `RLimbStore`: the stored word
      is `(BitVec.ofNat 64 (e.eval rs.rsScalar))` fed through
      `leafSpec.limbStore`. -/
  | RLimbStoreExpr : Located → Nat → SExpr → LowCT
  /-- **N-output function call.**  Generalisation of `RCall`
      (1-out) and `RCallSwap` (2-out) to arbitrary destination count.
      The oracle `LeafSpec.callN` is the multi-output analogue of
      `LeafSpec.call`.  Borrow checker: `dests` distinct, `dests ∩ args
      = ∅`.  Used for `(carry, sum) = adcx(a, b, c_in)` shapes. -/
  | RCallN     : String → List Located → List Located → LowCT
  /-- **CT-safe conditional select primitive.**
      `RSelect dst sel src0 src1` writes `dst := if sel = 0 then src0
      else src1`.  Hardware-level: a single `CMOV`-shaped opcode chain.
      Promoting cmov to a constructor (rather than emulating via leaf
      call) lets the borrow checker reason about it precisely (read sel,
      read src0, read src1, write dst — no aliasing constraint between
      dst and srcs since cmov is read-then-write). -/
  | RSelect    : Located → String → Located → Located → LowCT
  /-- **Zero-cost contract assertion.**  No runtime effect;
      the Hoare rule injects an external proposition (looked up by
      `label` in the proof context) into the postcondition.  Used to
      strengthen loop invariants without inserting any bytes into the
      output asm. -/
  | RAssert    : String → LowCT
  /-- **Scoped block.**  `RBlock body` runs `body` in a fresh
      scope; locally bound slots (via `RLetZero` / `RLetU64Zero` inside
      `body`) are released at scope end, allowing stack reuse across
      multiple `RBlock`s in a sequence.  Lowering: emits `body`'s Jasmin
      bracketed by `stackalloc`/dealloc; runtime semantics are
      identical to `body`. -/
  | RBlock     : LowCT → LowCT
  /-- **User-defined helper definition.**
      `RFnDef name params returns body cont` declares a helper
      function `name` with `params` (read-only, by-ref) and `returns`
      (write, by-ref).  `body` runs with `params` and `returns` in
      scope; `cont` is the continuation in the outer scope (the
      function body is *not* inlined here — it's lifted to a separate
      Jasmin `FunDecl` at lowering time).  This is the
      compile-time analogue of `fn name(out: ..., in: ...) { body }`. -/
  | RFnDef     : (name : String)
              → (params : List Located)
              → (returns : List Located)
              → (body : LowCT)
              → (cont : LowCT)
              → LowCT
  /-- **User-defined helper call.**
      `RFnCall f dests args` invokes a helper declared via
      `RFnDef` (or in an outer environment).  Borrow checker: same as
      `RCallN` (dests distinct, dests ∩ args = ∅).  Lowers to a single
      Jasmin `Ccall .DoNotInline` to the `name` function. -/
  | RFnCall    : (f : String)
              → (dests : List Located)
              → (args : List Located)
              → LowCT
  /-- **Tuple component load.**
      `RTupleLoad dst src idx` reads component `idx` of `src` into
      `dst`.  Lowering: array-index load.  -/
  | RTupleLoad  : (dst : Located) → (src : Located) → (idx : Nat) → LowCT
  /-- **Array element store.**
      `RArrStore arr idxVar src` writes the value of slot `src` into
      element `idxVar` of the array slot `arr`.  `idxVar` is the name
      of a `u64`-typed scalar variable in `rsScalar` holding the
      runtime index.  Requires `arr.locSrc = TArr n t` and
      `src.locSrc = t`.  Lowering: `arr[idxVar as usize] = *src;`. -/
  | RArrStore  : (arr : Located) → (idxVar : String) → (src : Located) → LowCT
  /-- **Array element load.**
      `RArrLoad dst src idxVar` reads element `idxVar` of array slot
      `src` into `dst`.  Requires `src.locSrc = TArr n t` and
      `dst.locSrc = t`.  Lowering: `*dst = src[idxVar as usize];`. -/
  | RArrLoad   : (dst : Located) → (src : Located) → (idxVar : String) → LowCT
  /-- **Literal-index array store.**
      `RArrStoreLit arr idx src` writes the value of `src` into element
      `idx` of `arr`, where `idx : Nat` is a *compile-time literal*
      (not read from a runtime scalar slot).  This is the
      static-index complement of `RArrStore` and is sufficient for
      post-`RFor`-unroll outer-loop array access — the most common
      emit pattern.  Lowering: `arr[idx] = *src;`.

      Composes naturally with the static `unrollForJ` pattern: after
      `RFor x N body` unrolls into `N` explicit iterations, any
      `RArrLoad/RArrStore` whose `idxVar = x` (loop counter) can be
      rewritten to `RArrLoadLit/RArrStoreLit` with the literal
      iteration index. -/
  | RArrStoreLit : (arr : Located) → (idx : Nat) → (src : Located) → LowCT
  /-- **Literal-index array load.**
      `RArrLoadLit dst src idx` reads element `idx` of `src` into
      `dst`, where `idx : Nat` is a *compile-time literal*.  The
      static-index complement of `RArrLoad`.  Lowering:
      `*dst = src[idx];`. -/
  | RArrLoadLit  : (dst : Located) → (src : Located) → (idx : Nat) → LowCT
  /-- **Assign expression to scalar slot.**
      `RScalarSetExpr x e` evaluates `SExpr e` against the current
      scalar environment and writes the result to scalar slot `x`.
      Strictly more expressive than `RScalarSet x n` (which only takes
      a literal Nat).  Unlocks index arithmetic like `k := i * 16 + d`
      for runtime-bound `i`, `d`. -/
  | RScalarSetExpr : (x : String) → (e : SExpr) → LowCT
  /-- **Dst-threaded leaf call.**
      `RCallDstThreaded f dst args` calls leaf `f` with the destination
      slot threaded as both the first argument **and** the receiving
      lvalue: `dst = f(dst, args)`.  It is the shape for a shim whose
      signature receives the output buffer by value, mutates it in
      place, and returns it.  Lowering: a single Jasmin `Ccall`
      with `dst` as the lvalue and `(dst :: args)` as the call
      arguments.  Borrow check: `dst ∉ args` (same as `RCall`).

      Construction sites are `bench/` drivers and optimizer passes; no
      protocol kernel builds this node.  -/
  | RCallDstThreaded : (name : String) → (dst : Located) →
                       (args : List Located) → LowCT
  /-- Runtime-bound for-loop. `RForRuntime x bound body` runs `body` with
      the scalar counter `x = 0 … (bound.evalState rs) - 1`; the trip count
      is fixed by evaluating `bound : SExpr` in the ENTRY state. Runtime-valued
      sibling of `RFor x n body`. Faithful image of a hax `forFold` whose `hi`
      bound is a non-literal `SExpr` (`2*K`, `min(eta,128)`, symbolic const). -/
  | RForRuntime : (x : String) → (bound : SExpr) → (body : LowCT) → LowCT
  /-- **Whole-array copy.**
      `RCopy dst src` writes the value of slot `src` into slot `dst`; both
      slots have the same tower type. It reads no selector and no index.
      Lowering: a Jasmin `Cassgn` of the array (`dst = #copy(src)`); Rust
      `dst.copy_from_slice(&src)`. Borrow check: `dst ≠ src`. -/
  | RCopy : (dst : Located) → (src : Located) → LowCT
  deriving Repr, Inhabited

/-- **128-bit SIMD vector assignment (the vector analog
    of `RScalarSetExpr`).**  `RVsimdSetExpr x tag args` assigns to the 128-bit
    vector slot `x` the result of the SIMD op named by `tag` applied to the
    128-bit operand slots named in `args`.  `tag` is a `vsimd`-op tag
    (`"vsimd.gf2p8mulb"`, `"vpsrldq.8"`, `"vsimd.xor"`, `"vpshufd.<imm>"`,
    `"vaeskeygen.<rcon>"`, `"affineqb.<imm>"`, `"clmul.<imm>"`,
    `"packed.<bop>.<laneW>"`, …); the vector front `translateDialectControlV`
    parses it (`vsimdTag`) and emits the matching **inlined** `CatCryptOp.vsimd` /
    `vpsrldqC` / … op over `.sword 128`, lowered by the verified
    `cryptoDialectToJasminCom` map to the owned x86 SIMD backend.

    This is the vector companion of the scalar `RScalarSetExpr`.  It is a
    *derived* `LowCT` statement — it desugars to a reserved-tag `RCall`, so it
    needs no new `LowCT` inductive constructor (and hence no cascade through the
    ~56 modules that match on `LowCT` exhaustively) while remaining a distinct,
    first-class source node.  Because it is definitionally an `RCall`, its
    operational semantics is `RustExec.call` (a data-oblivious opaque leaf: the
    128-bit vector value lives outside the `TowerType`-modeled `RustState`, so the
    RHP/CT chain treats it opaquely and the SIMD lane semantics is pinned at the
    dialect `denote = spec` level), it is `IsCovered` via `rCall`, its Rust ↔
    dialect simulation is the `RCall` case of `rustExecSimulatesDialect`, and its
    emitted-prefix leak trace is the constant `RCall`/`varBind` factor.  The
    located-type `.TU64` is inert: the vector front resolves operands
    by *name* (`lookupReg128`) and binds the destination at `.sword 128`
    regardless of the located type. -/
def LowCT.RVsimdSetExpr (x : String) (tag : String) (args : List String) : LowCT :=
  .RCall tag ⟨x, .TU64⟩ (args.map (fun s => ⟨s, .TU64⟩))

/-- `RVsimdSetExpr` is definitionally the reserved-tag `RCall`.  This `rfl`
    exposes the desugaring so every `RCall`-parametric result — `RustExec.call`,
    `IsCovered.rCall`, the `RCall` case of `rustExecSimulatesDialect`, and the
    leak-factoring `RCall` arm — applies to the vector node unchanged. -/
theorem LowCT.RVsimdSetExpr_desugar (x tag : String) (args : List String) :
    LowCT.RVsimdSetExpr x tag args
      = .RCall tag ⟨x, .TU64⟩ (args.map (fun s => ⟨s, .TU64⟩)) := rfl

/-! ## §3b  Generic structural recursor / fold

The *recursion structure* of `LowCT` — which constructors carry sub-commands
and how their results combine — is shared by every structural analysis
(`borrowOk`, `destsOf`, `rcSize`, leak-trace collection, …).  Written as an
open match, adding a constructor would require editing each analysis.

`LowCT.fold` factors that recursion structure into **one** place.  An
analysis with carrier type `α` supplies:

* `leaf  : LowCT → α`  — the value for a non-recursive (leaf) node.  The
  argument is the *original* node, so the analysis reads off its fields
  (dest/args/etc.) directly.  A new leaf constructor only
  needs an arm here (or a catch-all default), never a new recursion clause.
* `seqLike  : α → α → α`        — combine the two children of `RSeq`/`RIfNz`
  (and `RFnDef`'s body × cont).
* `wrap1    : α → α`            — wrap the single child of
  `RLetZero`/`RLetU64Zero`/`RWhileNz`/`RFor`/`RBlock`.

Because *only* the eight recursive constructors recurse, this captures the
entire structural skeleton.  Analyses that are monoidal folds
(`destsOf` = list-append, `rcSize` = sum, `borrowOk` = conjunction) collapse
to a one-line algebra; the per-leaf arm stays where it belongs.

The recursion is structural (every recursive call is on a syntactic
sub-term), so the equation lemmas are definitional `rfl`s and
`unfold`/`simp [LowCT.fold]` reduces `fold` on a constructor. -/
def LowCT.fold {α : Type _}
    (leaf : LowCT → α)
    (seqLike : α → α → α)
    (wrap1 : α → α) : LowCT → α
  | .RSeq c1 c2            => seqLike (LowCT.fold leaf seqLike wrap1 c1)
                                     (LowCT.fold leaf seqLike wrap1 c2)
  | .RIfNz _ ct cf         => seqLike (LowCT.fold leaf seqLike wrap1 ct)
                                     (LowCT.fold leaf seqLike wrap1 cf)
  | .RFnDef _ _ _ body cont => seqLike (LowCT.fold leaf seqLike wrap1 body)
                                       (LowCT.fold leaf seqLike wrap1 cont)
  | .RLetZero _ _ body     => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | .RLetU64Zero _ body    => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | .RWhileNz _ body       => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | .RFor _ _ body         => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | .RBlock body           => wrap1 (LowCT.fold leaf seqLike wrap1 body)
  | c                      => leaf c

/-- **Node-aware structural fold.**  Generalises `LowCT.fold` by passing
    the *original* recursive node to the combiners, so analyses whose
    recursive case contributes node-derived data — e.g. `cmdCT`'s
    `lt cond == .Public &&` guard on `RIfNz`/`RWhileNz`, or `destsOf`'s
    `x ::` prepend on `RLetZero` — can be expressed as a fold instead of an
    open match.  `seqNode node r1 r2` combines the two children's results of
    a two-child node (`RSeq`/`RIfNz`/`RFnDef`); `wrapNode node r` wraps the
    single child's result (`RLetZero`/`RLetU64Zero`/`RWhileNz`/`RFor`/
    `RBlock`).  Leaves go through `leaf` as in `LowCT.fold`. -/
def LowCT.foldNode {α : Type _}
    (leaf : LowCT → α)
    (seqNode : LowCT → α → α → α)
    (wrapNode : LowCT → α → α) : LowCT → α
  | c@(.RSeq c1 c2)            => seqNode c (LowCT.foldNode leaf seqNode wrapNode c1)
                                           (LowCT.foldNode leaf seqNode wrapNode c2)
  | c@(.RIfNz _ ct cf)         => seqNode c (LowCT.foldNode leaf seqNode wrapNode ct)
                                           (LowCT.foldNode leaf seqNode wrapNode cf)
  | c@(.RFnDef _ _ _ body cont) => seqNode c (LowCT.foldNode leaf seqNode wrapNode body)
                                             (LowCT.foldNode leaf seqNode wrapNode cont)
  | c@(.RLetZero _ _ body)     => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c@(.RLetU64Zero _ body)    => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c@(.RWhileNz _ body)       => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c@(.RFor _ _ body)         => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c@(.RBlock body)           => wrapNode c (LowCT.foldNode leaf seqNode wrapNode body)
  | c                          => leaf c

/-! ### `LowCT.fold` reduction lemmas

These `@[simp]` equations let `simp [LowCT.fold]` (and any analysis defined
as `f := LowCT.fold …`, via `simp [f]`) reduce `fold` on a literal
constructor to its per-constructor right-hand side, so proofs close by
unfolding the analysis.  Each is a definitional `rfl`. -/
section FoldLemmas
variable {α : Type _} (leaf : LowCT → α) (seqLike : α → α → α) (wrap1 : α → α)

@[simp] theorem LowCT.fold_RSeq (c1 c2 : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RSeq c1 c2)
      = seqLike (LowCT.fold leaf seqLike wrap1 c1)
                (LowCT.fold leaf seqLike wrap1 c2) := rfl

@[simp] theorem LowCT.fold_RIfNz (s : String) (ct cf : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RIfNz s ct cf)
      = seqLike (LowCT.fold leaf seqLike wrap1 ct)
                (LowCT.fold leaf seqLike wrap1 cf) := rfl

@[simp] theorem LowCT.fold_RFnDef (n : String) (p r : List Located)
    (body cont : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RFnDef n p r body cont)
      = seqLike (LowCT.fold leaf seqLike wrap1 body)
                (LowCT.fold leaf seqLike wrap1 cont) := rfl

@[simp] theorem LowCT.fold_RLetZero (x : String) (t : TowerType) (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RLetZero x t body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

@[simp] theorem LowCT.fold_RLetU64Zero (x : String) (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RLetU64Zero x body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

@[simp] theorem LowCT.fold_RWhileNz (s : String) (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RWhileNz s body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

@[simp] theorem LowCT.fold_RFor (x : String) (n : Nat) (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RFor x n body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

@[simp] theorem LowCT.fold_RBlock (body : LowCT) :
    LowCT.fold leaf seqLike wrap1 (.RBlock body)
      = wrap1 (LowCT.fold leaf seqLike wrap1 body) := rfl

end FoldLemmas

section FoldNodeLemmas
variable {α : Type _} (leaf : LowCT → α) (seqNode : LowCT → α → α → α)
  (wrapNode : LowCT → α → α)

@[simp] theorem LowCT.foldNode_RSeq (c1 c2 : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RSeq c1 c2)
      = seqNode (.RSeq c1 c2) (LowCT.foldNode leaf seqNode wrapNode c1)
                              (LowCT.foldNode leaf seqNode wrapNode c2) := rfl

@[simp] theorem LowCT.foldNode_RIfNz (s : String) (ct cf : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RIfNz s ct cf)
      = seqNode (.RIfNz s ct cf) (LowCT.foldNode leaf seqNode wrapNode ct)
                                 (LowCT.foldNode leaf seqNode wrapNode cf) := rfl

@[simp] theorem LowCT.foldNode_RFnDef (n : String) (p r : List Located)
    (body cont : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RFnDef n p r body cont)
      = seqNode (.RFnDef n p r body cont)
                (LowCT.foldNode leaf seqNode wrapNode body)
                (LowCT.foldNode leaf seqNode wrapNode cont) := rfl

@[simp] theorem LowCT.foldNode_RLetZero (x : String) (t : TowerType) (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RLetZero x t body)
      = wrapNode (.RLetZero x t body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

@[simp] theorem LowCT.foldNode_RLetU64Zero (x : String) (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RLetU64Zero x body)
      = wrapNode (.RLetU64Zero x body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

@[simp] theorem LowCT.foldNode_RWhileNz (s : String) (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RWhileNz s body)
      = wrapNode (.RWhileNz s body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

@[simp] theorem LowCT.foldNode_RFor (x : String) (n : Nat) (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RFor x n body)
      = wrapNode (.RFor x n body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

@[simp] theorem LowCT.foldNode_RBlock (body : LowCT) :
    LowCT.foldNode leaf seqNode wrapNode (.RBlock body)
      = wrapNode (.RBlock body) (LowCT.foldNode leaf seqNode wrapNode body) := rfl

end FoldNodeLemmas

/-- The eight recursive `LowCT` constructors, the ones `LowCT.fold`
    descends into.  Anything else is a leaf for the purposes of structural
    folds.  Exposed so analyses / proofs can branch on "is this a recursive
    node?" without re-listing the constructors. -/
def LowCT.isRecursive : LowCT → Bool
  | .RSeq _ _          => true
  | .RIfNz _ _ _       => true
  | .RFnDef _ _ _ _ _  => true
  | .RLetZero _ _ _    => true
  | .RLetU64Zero _ _   => true
  | .RWhileNz _ _      => true
  | .RFor _ _ _        => true
  | .RBlock _          => true
  | _                  => false

end CatCrypt.Crypto.Jasmin.LowCT
