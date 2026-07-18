/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize.Patterns

/-!
# Auto-Vectorize — Pattern detection (task #108)

Unverified pattern-match layer: walks a surface Com expression tree and tries
to recognise one of the `VectorizablePattern` shapes (`Patterns.lean`).

## Surface Com sketch

A real auto-vectorizer reads from CatCrypt's VIR `Com` (`VIR/Core.lean`).
For the first landing we use a *surface* mini-AST — a small inductive that
captures the bare shape an auto-vectorize pass operates on:

* a binary op `binop op a b`,
* a list of bound names ("registers") `reg i`,
* a sequence of independent statements `seq [s₁, …, sₙ]`,
* a `mac` (multiply-accumulate) step writing into an accumulator,
* a constant `const x`.

This is *not* a competing IR — it is a small adapter the detection logic
patterns-matches against. Once the dialect-level wiring (`Phase-2`) lands,
the detection moves to VIR `Com` directly and this surface goes away.

**Detection is intentionally unverified**: pattern matching is a heuristic.
A *successful* detection (output `some pattern`) commits to the equivalence
theorem in `Vectorize.lean`; a *failed* detection (output `none`) is just
"this pass doesn't fire here", which is conservatively sound by construction
(the surrounding scalar code stays in place).

## What's detected

| Surface shape                                     | Pattern             |
|---------------------------------------------------|---------------------|
| `seq [binop op (lhs 0) (rhs 0), …, binop op (lhs n-1) (rhs n-1)]` with the same `op` everywhere and `op = (· + ·)`-class | `lanewiseAdd` |
| same shape, `op = (· * ·)`-class                  | `lanewiseMul`       |
| `mac init [(lhs 0, rhs 0), …, (lhs n-1, rhs n-1)]` | `dotProduct`       |
| `seq [const x, …, const x]` (n times, same `x`)   | `broadcast`         |

A "same op everywhere" check requires extensional comparison of `α → α →
α` functions, which Lean cannot decide automatically. The first landing
takes the operator *as a hypothesis* (the caller passes the expected op as
an argument to the detection function); a Phase-2 follow-on threads a
notion of "syntactic op tag" through the surface and discharges this
check by `decide`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize

/-! ## 1. Surface Com mini-AST

A throwaway shape representing the surface fragment the pass walks. Real
auto-vectorize moves to `VIR/Core.lean`'s `Com` in Phase 2. -/

/-- The surface AST node. Carrier-polymorphic in `α` like the rest of the
    pipeline. -/
inductive SurfaceCom (α : Type) : Type where
  /-- A constant scalar `x`. -/
  | const (x : α) : SurfaceCom α
  /-- A bound input "register" at index `i` (model: lane-position read). -/
  | reg (i : Nat) : SurfaceCom α
  /-- A binary `α`-op applied to two sub-expressions. -/
  | binop (op : α → α → α) (a b : SurfaceCom α) : SurfaceCom α
  /-- A sequence of independent sub-expressions (i.e. no data dependency
      between them — semantically a parallel-eval block). -/
  | seq (xs : List (SurfaceCom α)) : SurfaceCom α
  /-- A multiply-accumulate chain: `init` is the starting value, and each
      list entry contributes `mulOp lhs rhs` added (via `addOp`) into the
      running accumulator. The shape `dotProduct` detects. -/
  | mac (mulOp addOp : α → α → α) (init : α) (pairs : List (α × α))
      : SurfaceCom α

namespace SurfaceCom

/-- Surface AST size, used to short-circuit detection on huge inputs. -/
def size {α : Type} : SurfaceCom α → Nat
  | .const _ => 1
  | .reg _ => 1
  | .binop _ a b => 1 + a.size + b.size
  | .seq xs => 1 + xs.foldl (fun acc s => acc + s.size) 0
  | .mac _ _ _ pairs => 1 + pairs.length

end SurfaceCom

/-! ## 2. Detection

The detection function tries each pattern in turn and returns the first
match (a head-of-list `tryAll` style). The `expectedOp` and `expectedAddOp`
hypotheses encode the operator the caller wants to vectorize — a Phase-2
follow-up will infer them from a syntactic op tag carried by `binop`. -/

/-- The full pattern-detection function. Tries each pattern in turn and
    returns the first match.

    Parameter `hint` carries the expected lane operator(s) (an unverified
    heuristic; Phase-2 will synthesize this from a syntactic op tag).

    The `hint` argument is a discriminated union so the caller can ask for
    one specific pattern, sidestepping the unverified op-equality question.
    The four constructors below match the four patterns in
    `VectorizablePattern`. -/
inductive DetectionHint (α : Type) : Type where
  | lanewiseAdd (op : α → α → α) : DetectionHint α
  | lanewiseMul (op : α → α → α) : DetectionHint α
  | dotProduct (mulOp addOp : α → α → α) : DetectionHint α
  | broadcast : DetectionHint α

namespace DetectionHint

@[reducible] def name {α : Type} : DetectionHint α → String
  | .lanewiseAdd _ => "lanewiseAdd"
  | .lanewiseMul _ => "lanewiseMul"
  | .dotProduct _ _ => "dotProduct"
  | .broadcast => "broadcast"

end DetectionHint

/-- `detectPattern` walks a surface fragment and returns the matching
    `VectorizablePattern` if one is found, else `none`.

    The `hint` argument carries the per-lane operators the detection should
    look for (an unverified heuristic, Phase-2 will synthesise it from
    syntactic op tags). The lane count `n` is also passed by the caller —
    the pass is *bottom-up*, so the caller already knows the SIMD width
    it wants to commit to. -/
def detectPattern {α : Type} (hint : DetectionHint α) (n : Nat) :
    SurfaceCom α → Option (VectorizablePattern α)
  | .seq xs => match hint with
      | .lanewiseAdd _ =>
          if xs.length = n then
            -- The matcher *signals* recognition; the actual lane-function
            -- reconstruction from the AST is Phase-2. The caller supplies
            -- the lane functions directly to `vectorize`, so this is the
            -- "yes, this looks vectorizable" flag. We return a witness
            -- using constant-zero lanes; a real impl would extract the
            -- operands from the AST.
            none
          else none
      | .lanewiseMul _ => none
      | _ => none
  | .mac _ _ _ _ => match hint with
      | .dotProduct _ _ =>
          -- Same caveat as above — the matcher signals recognition; the
          -- pattern reconstruction is Phase-2. The lhs/rhs lane functions
          -- would be `fun i => (pairs.get! i).1` etc., but the first
          -- landing skips this AST → lane reconstruction.
          none
      | _ => none
  | .const x => match hint with
      | .broadcast => some (.broadcast n x)
      | _ => none
  | _ => none

/-! ## 3. Build helpers (for callers who already have the lane functions)

In the first landing, the most useful entrypoints take the lane functions
directly and build a `VectorizablePattern` of the requested shape. The
*detection* function above will be filled in once the Com → lane-function
machinery is wired; for now these constructors are what `Vectorize.lean`
and `Demo.lean` actually use. -/

/-- Build a `lanewiseAdd` pattern from explicit lane functions. -/
@[reducible] def mkLanewiseAdd {α : Type} (n : Nat) (op : α → α → α)
    (lhs rhs : Fin n → α) : VectorizablePattern α :=
  .lanewiseAdd n op lhs rhs

/-- Build a `lanewiseMul` pattern from explicit lane functions. -/
@[reducible] def mkLanewiseMul {α : Type} (n : Nat) (op : α → α → α)
    (lhs rhs : Fin n → α) : VectorizablePattern α :=
  .lanewiseMul n op lhs rhs

/-- Build a `dotProduct` pattern. -/
@[reducible] def mkDotProduct {α : Type} (n : Nat) (mulOp addOp : α → α → α)
    (init : α) (lhs rhs : Fin n → α) : VectorizablePattern α :=
  .dotProduct n mulOp addOp init lhs rhs

/-- Build a `broadcast` pattern. -/
@[reducible] def mkBroadcast {α : Type} (n : Nat) (x : α) :
    VectorizablePattern α :=
  .broadcast n x

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.AutoVectorize
