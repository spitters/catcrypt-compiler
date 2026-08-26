/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Hax.AST

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpPat)

/-! # Constant-substitution pre-pass for the H2 translator

Replaces `.var name` with `.lit (.int value)` for names in a
caller-supplied substitution table.  Used to inline module-level
constants like ML-KEM's `K = 3`, `N = 256`, `Q = 3329` so the
extracted `.forFold _ _ (.var "K") _` becomes `.forFold _ _ (.lit 3) _`
— a form `haxToLowCT.forFold` accepts.

This pass is intentionally MINIMAL: it does not evaluate expressions,
fold arithmetic, or perform any other constant folding.  It just
substitutes pre-known names.  Composes with `aNormalize`.
-/

/-- A substitution table: list of (name, value-as-Int) pairs. -/
abbrev ConstTable := List (String × Int)

/-- The ML-KEM-768 constants (FIPS 203 §5). -/
def mlkemConstTable : ConstTable :=
  [ ("Q", 3329), ("N", 256), ("K", 3),
    ("ETA1", 2), ("ETA2", 2),
    ("DU", 10), ("DV", 4),
    ("SS_BYTES", 32), ("SEED_BYTES", 32) ]

/-- The ML-DSA-65 constants (FIPS 204 §5). -/
def mldsaConstTable : ConstTable :=
  [ ("Q", 8380417), ("N", 256), ("K", 6), ("L", 5),
    ("ETA", 4), ("TAU", 49),
    ("GAMMA1", 524288), ("GAMMA2", 261888),
    ("OMEGA", 55), ("BETA", 196), ("D", 13) ]

/-- Lookup helper. -/
def ConstTable.find (t : ConstTable) (name : String) : Option Int :=
  match t with
  | [] => none
  | (n, v) :: rest => if n == name then some v else ConstTable.find rest name

/-- Substitute known constants throughout an ImpExpr.  Recurses
    through every constructor; replaces `.var name` (when `name` is in
    the table) with `.lit (.int value)`.

    `partial` is used to side-step the nested-inductive termination
    obligation (`List ImpExpr`, `List (ImpPat × ImpExpr)`).  The
    recursion is structurally well-founded; a clean termination proof
    would mirror the `ImpExpr.ind` helper in `Hax/AST.lean`. -/
partial def substConsts (t : ConstTable) : ImpExpr → ImpExpr
  -- Core (survive all phases)
  | .lit l => .lit l
  | .var name =>
      match t.find name with
      | some v => .lit (.int v)
      | none   => .var name
  | .letBind n rhs body =>
      .letBind n (substConsts t rhs) (substConsts t body)
  | .lam ps body =>
      .lam ps (substConsts t body)
  | .app f args =>
      .app f (args.map (substConsts t))
  | .tuple elems =>
      .tuple (elems.map (substConsts t))
  | .proj e i =>
      .proj (substConsts t e) i
  | .ifThenElse c thn els =>
      .ifThenElse (substConsts t c) (substConsts t thn) (substConsts t els)
  | .match_ scrut arms =>
      .match_ (substConsts t scrut)
        (arms.map (fun (p, e) => (p, substConsts t e)))
  | .unitVal => .unitVal
  | .seq a b => .seq (substConsts t a) (substConsts t b)
  -- Consumed by dropReferences (Phase 1)
  | .borrow e => .borrow (substConsts t e)
  | .deref e => .deref (substConsts t e)
  -- Consumed by localMutation (Phase 2)
  | .assign n rhs => .assign n (substConsts t rhs)
  -- Consumed by functionalizeLoops (Phase 3)
  | .forLoop v lo hi body =>
      .forLoop v (substConsts t lo) (substConsts t hi) (substConsts t body)
  | .forLoopRev v lo hi body =>
      .forLoopRev v (substConsts t lo) (substConsts t hi) (substConsts t body)
  | .whileLoop c body =>
      .whileLoop (substConsts t c) (substConsts t body)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (substConsts t e))
  | .continue_ => .continue_
  -- Consumed by cfIntoMonads (Phase 4)
  | .earlyReturn e => .earlyReturn (substConsts t e)
  | .questionMark e => .questionMark (substConsts t e)
  -- Produced by functionalizeLoops (Phase 3)
  | .forFold v lo hi body =>
      .forFold v (substConsts t lo) (substConsts t hi) (substConsts t body)
  | .forFoldRev v lo hi body =>
      .forFoldRev v (substConsts t lo) (substConsts t hi) (substConsts t body)
  | .whileFold c body =>
      .whileFold (substConsts t c) (substConsts t body)
  | .forFoldReturn v lo hi body =>
      .forFoldReturn v (substConsts t lo) (substConsts t hi) (substConsts t body)
  | .forFoldRevReturn v lo hi body =>
      .forFoldRevReturn v (substConsts t lo) (substConsts t hi) (substConsts t body)
  | .whileFoldReturn c body =>
      .whileFoldReturn (substConsts t c) (substConsts t body)
  | .cfBreak e => .cfBreak (substConsts t e)
  | .cfContinue e => .cfContinue (substConsts t e)
  | .cfBreakContinue e => .cfBreakContinue (substConsts t e)

/-- Convenience: substitute the ML-KEM constants. -/
def substMlkemConsts : ImpExpr → ImpExpr := substConsts mlkemConstTable

/-- Convenience: substitute the ML-DSA constants. -/
def substMldsaConsts : ImpExpr → ImpExpr := substConsts mldsaConstTable

/-! ## §2  Arithmetic constant-folding

Recursively reduces `.app "Div" / "Mul" / "Add" / "Sub" / "Rem"
[.lit (.int a), .lit (.int b)]` to `.lit (.int (a op b))`. Other `.app`
shapes pass through unchanged.

Motivation: after `substMlkemConsts` rewrites `.var "N"` → `.lit (.int 256)`,
a `.forFold _ _ (.app "Div" [.var "N", .lit (.int 2)]) _` becomes
`.forFold _ _ (.app "Div" [.lit (.int 256), .lit (.int 2)]) _` — still
not a `.lit`, so the H2 translator's `.forFold` arm rejects it. Folding
the `.app "Div"` to `.lit (.int 128)` unblocks ~12 more ML-KEM functions.

Composes with `substConsts` — typical pipeline is
`foldArith ∘ substMlkemConsts ∘ raw_extraction`.

### Note on integer division semantics

Lean's `Int.div` is the standard (Euclidean-style) `Int` division which
truncates toward zero for non-negative numerators (the only case that
arises for ML-KEM/ML-DSA-style bounds). For arbitrary signed dividends,
Rust's `/` operator on `i64` also truncates toward zero, matching Lean
on the positive arguments we actually fold here. The constants involved
in ML-KEM and ML-DSA bounds (`N`, `K`, `Q`, `L`, `ETA`, `D`, etc.) are
all positive, so no semantic divergence arises in practice.
-/

/-- Try to reduce a single `.app` of an arithmetic operator on two
    integer literals. Returns `.lit (.int v)` on success; `none` if the
    args aren't both `.lit (.int _)` or the op isn't recognized.

    Division and remainder by zero are deliberately *not* folded —
    leaving the original `.app` in place is safer than introducing a
    fold that would change behaviour at runtime. -/
def tryArithFold (f : String) (args : List ImpExpr) : Option ImpExpr :=
  match args with
  | [.lit (.int a), .lit (.int b)] =>
      match f with
      | "Add" | "add" => some (.lit (.int (a + b)))
      | "Sub" | "sub" => some (.lit (.int (a - b)))
      | "Mul" | "mul" => some (.lit (.int (a * b)))
      | "Div" | "div" => if b = 0 then none else some (.lit (.int (a / b)))
      | "Rem" | "rem" => if b = 0 then none else some (.lit (.int (a % b)))
      | _ => none
  | _ => none

/-- Apply `foldArith` recursively over an ImpExpr.  Bottom-up: reduce
    children first, then attempt to fold the current node.

    `partial` is used to side-step the nested-inductive termination
    obligation (`List ImpExpr`, `List (ImpPat × ImpExpr)`) — mirroring
    `substConsts` above. -/
partial def foldArith : ImpExpr → ImpExpr
  -- Core (survive all phases)
  | .lit l => .lit l
  | .var n => .var n
  | .letBind n rhs body =>
      .letBind n (foldArith rhs) (foldArith body)
  | .lam ps body =>
      .lam ps (foldArith body)
  | .app f args =>
      let args' := args.map foldArith
      match tryArithFold f args' with
      | some folded => folded
      | none => .app f args'
  | .tuple elems =>
      .tuple (elems.map foldArith)
  | .proj e i =>
      .proj (foldArith e) i
  | .ifThenElse c thn els =>
      .ifThenElse (foldArith c) (foldArith thn) (foldArith els)
  | .match_ scrut arms =>
      .match_ (foldArith scrut)
        (arms.map (fun (p, e) => (p, foldArith e)))
  | .unitVal => .unitVal
  | .seq a b => .seq (foldArith a) (foldArith b)
  -- Consumed by dropReferences (Phase 1)
  | .borrow e => .borrow (foldArith e)
  | .deref e => .deref (foldArith e)
  -- Consumed by localMutation (Phase 2)
  | .assign n rhs => .assign n (foldArith rhs)
  -- Consumed by functionalizeLoops (Phase 3)
  | .forLoop v lo hi body =>
      .forLoop v (foldArith lo) (foldArith hi) (foldArith body)
  | .forLoopRev v lo hi body =>
      .forLoopRev v (foldArith lo) (foldArith hi) (foldArith body)
  | .whileLoop c body =>
      .whileLoop (foldArith c) (foldArith body)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (foldArith e))
  | .continue_ => .continue_
  -- Consumed by cfIntoMonads (Phase 4)
  | .earlyReturn e => .earlyReturn (foldArith e)
  | .questionMark e => .questionMark (foldArith e)
  -- Produced by functionalizeLoops (Phase 3)
  | .forFold v lo hi body =>
      .forFold v (foldArith lo) (foldArith hi) (foldArith body)
  | .forFoldRev v lo hi body =>
      .forFoldRev v (foldArith lo) (foldArith hi) (foldArith body)
  | .whileFold c body =>
      .whileFold (foldArith c) (foldArith body)
  | .forFoldReturn v lo hi body =>
      .forFoldReturn v (foldArith lo) (foldArith hi) (foldArith body)
  | .forFoldRevReturn v lo hi body =>
      .forFoldRevReturn v (foldArith lo) (foldArith hi) (foldArith body)
  | .whileFoldReturn c body =>
      .whileFoldReturn (foldArith c) (foldArith body)
  | .cfBreak e => .cfBreak (foldArith e)
  | .cfContinue e => .cfContinue (foldArith e)
  | .cfBreakContinue e => .cfBreakContinue (foldArith e)

/-- Convenience: substitute ML-KEM constants, then fold arithmetic.

    Designed to be a drop-in replacement for `substMlkemConsts` in the
    H2 translator pipeline. A follow-up commit can swap the call site
    in `HaxToLowCT_Pipeline.lean`'s `haxToLowCT_mlkem` without
    touching this file. -/
def mlkemFold : ImpExpr → ImpExpr := foldArith ∘ substMlkemConsts

/-- Convenience: substitute ML-DSA constants, then fold arithmetic. -/
def mldsaFold : ImpExpr → ImpExpr := foldArith ∘ substMldsaConsts

/-! ## Surgical re-inlining of `repeat`'s length argument

`aNormalize` hoists every non-`var` `.app` argument — including the
integer length of `repeat(v, n)` — into a fresh `let __anorm_k = <lit>`
binding (to keep "every app arg is a `.var`", which the leaf lowering
needs).  The translator's `repeat` arm wants that length back as a
literal so it can size the array.

A *global* re-inline (`substConsts` over all uses) is WRONG: it would
also replace the lit-var in array **index** positions
(`r[__anorm_k]`), where the `index`/`array_update` arms strictly
require a `.var`.  This pass is **surgical** — it rewrites *only* the
second argument of `repeat`, leaving every other `.var` use intact.
Names are unique post-A-normalisation, so a single global
`collectLitBindings` map is sound. -/
partial def collectLitBindings : ImpExpr → ConstTable
  | .letBind v (.lit (.int n)) body => (v, n) :: collectLitBindings body
  | .letBind _ rhs body => collectLitBindings rhs ++ collectLitBindings body
  | .seq a b => collectLitBindings a ++ collectLitBindings b
  | .app _ args => args.foldr (fun a acc => collectLitBindings a ++ acc) []
  | .ifThenElse c t e =>
      collectLitBindings c ++ collectLitBindings t ++ collectLitBindings e
  | .match_ s arms =>
      collectLitBindings s ++ arms.foldr (fun (_, e) acc => collectLitBindings e ++ acc) []
  | .forFold _ lo hi b =>
      collectLitBindings lo ++ collectLitBindings hi ++ collectLitBindings b
  | .forFoldRev _ lo hi b =>
      collectLitBindings lo ++ collectLitBindings hi ++ collectLitBindings b
  | _ => []

/-- Rewrite ONLY `repeat`'s length arg (`.app "repeat" [v, .var lenVar]`
    → `[v, .lit (.int n)]`) using a pre-collected literal map.  All
    other subterms — crucially array indices — are recursed into but
    never substituted. -/
partial def rewriteRepeatLen (m : ConstTable) : ImpExpr → ImpExpr
  | .app "repeat" args =>
      let args' := args.map (rewriteRepeatLen m)
      match args' with
      | [v, .var lenVar] =>
          match m.find lenVar with
          | some n => .app "repeat" [v, .lit (.int n)]
          | none   => .app "repeat" args'
      | _ => .app "repeat" args'
  | .letBind n rhs body => .letBind n (rewriteRepeatLen m rhs) (rewriteRepeatLen m body)
  | .app f args => .app f (args.map (rewriteRepeatLen m))
  | .tuple es => .tuple (es.map (rewriteRepeatLen m))
  | .proj e i => .proj (rewriteRepeatLen m e) i
  | .ifThenElse c t e =>
      .ifThenElse (rewriteRepeatLen m c) (rewriteRepeatLen m t) (rewriteRepeatLen m e)
  | .match_ s arms =>
      .match_ (rewriteRepeatLen m s) (arms.map (fun (p, e) => (p, rewriteRepeatLen m e)))
  | .seq a b => .seq (rewriteRepeatLen m a) (rewriteRepeatLen m b)
  | .borrow e => .borrow (rewriteRepeatLen m e)
  | .deref e => .deref (rewriteRepeatLen m e)
  | .assign n rhs => .assign n (rewriteRepeatLen m rhs)
  | .forLoop v lo hi b =>
      .forLoop v (rewriteRepeatLen m lo) (rewriteRepeatLen m hi) (rewriteRepeatLen m b)
  | .forLoopRev v lo hi b =>
      .forLoopRev v (rewriteRepeatLen m lo) (rewriteRepeatLen m hi) (rewriteRepeatLen m b)
  | .whileLoop c b => .whileLoop (rewriteRepeatLen m c) (rewriteRepeatLen m b)
  | .earlyReturn e => .earlyReturn (rewriteRepeatLen m e)
  | .questionMark e => .questionMark (rewriteRepeatLen m e)
  | .forFold v lo hi b =>
      .forFold v (rewriteRepeatLen m lo) (rewriteRepeatLen m hi) (rewriteRepeatLen m b)
  | .forFoldRev v lo hi b =>
      .forFoldRev v (rewriteRepeatLen m lo) (rewriteRepeatLen m hi) (rewriteRepeatLen m b)
  | .whileFold c b => .whileFold (rewriteRepeatLen m c) (rewriteRepeatLen m b)
  | .forFoldReturn v lo hi b =>
      .forFoldReturn v (rewriteRepeatLen m lo) (rewriteRepeatLen m hi) (rewriteRepeatLen m b)
  | .forFoldRevReturn v lo hi b =>
      .forFoldRevReturn v (rewriteRepeatLen m lo) (rewriteRepeatLen m hi) (rewriteRepeatLen m b)
  | .whileFoldReturn c b => .whileFoldReturn (rewriteRepeatLen m c) (rewriteRepeatLen m b)
  | .cfBreak e => .cfBreak (rewriteRepeatLen m e)
  | .cfContinue e => .cfContinue (rewriteRepeatLen m e)
  | .cfBreakContinue e => .cfBreakContinue (rewriteRepeatLen m e)
  | e => e   -- .lit, .var, .unitVal, .break_, .continue_

/-- Surgically re-inline `repeat`'s A-normalised length argument. -/
def inlineRepeatLen (e : ImpExpr) : ImpExpr :=
  rewriteRepeatLen (collectLitBindings e) e

/-! ## Smoke tests -/

namespace SmokeTests

/-! Smoke tests use `BEq` (via `==`) rather than `=` because
    `substConsts` is a `partial def`: its equation compiler does not
    expose definitional equations, so `Eq` cannot be decided.
    `ImpExpr.beq` from `Hax/AST.lean` IS reducible, so `#guard`
    evaluates the BEq form through the interpreter. -/

-- Basic lookups: var → lit.
#guard substMlkemConsts (.var "K") == .lit (.int 3)
#guard substMlkemConsts (.var "N") == .lit (.int 256)
#guard substMlkemConsts (.var "Q") == .lit (.int 3329)
#guard substMlkemConsts (.var "ETA1") == .lit (.int 2)
#guard substMlkemConsts (.var "ETA2") == .lit (.int 2)
#guard substMlkemConsts (.var "DU") == .lit (.int 10)
#guard substMlkemConsts (.var "DV") == .lit (.int 4)
#guard substMlkemConsts (.var "SS_BYTES") == .lit (.int 32)
#guard substMlkemConsts (.var "SEED_BYTES") == .lit (.int 32)

-- Unknown name passes through unchanged.
#guard substMlkemConsts (.var "unknown") == .var "unknown"

-- Literals and unitVal are identity.
#guard substMlkemConsts (.lit (.int 7)) == .lit (.int 7)
#guard substMlkemConsts .unitVal == .unitVal

-- The motivating forFold motif: var-bound → lit-bound.
#guard substMlkemConsts
    (.forFold "i" (.lit (.int 0)) (.var "K") .unitVal) ==
    (.forFold "i" (.lit (.int 0)) (.lit (.int 3)) .unitVal)

-- Nested substitution under `.app`.
#guard substMlkemConsts
    (.app "Mul" [.var "K", .var "N"]) ==
    (.app "Mul" [.lit (.int 3), .lit (.int 256)])

-- Tuple recursion.
#guard substMlkemConsts
    (.tuple [.var "K", .var "N", .var "Q"]) ==
    (.tuple [.lit (.int 3), .lit (.int 256), .lit (.int 3329)])

-- letBind recursion (rhs and body).
#guard substMlkemConsts
    (.letBind "x" (.var "K") (.var "N")) ==
    (.letBind "x" (.lit (.int 3)) (.lit (.int 256)))

-- ifThenElse recursion.
#guard substMlkemConsts
    (.ifThenElse (.var "K") (.var "N") (.var "Q")) ==
    (.ifThenElse (.lit (.int 3)) (.lit (.int 256)) (.lit (.int 3329)))

-- proj recursion.
#guard substMlkemConsts
    (.proj (.var "K") 0) ==
    (.proj (.lit (.int 3)) 0)

-- seq recursion.
#guard substMlkemConsts
    (.seq (.var "K") (.var "N")) ==
    (.seq (.lit (.int 3)) (.lit (.int 256)))

-- borrow / deref recursion.
#guard substMlkemConsts (.borrow (.var "K")) == .borrow (.lit (.int 3))
#guard substMlkemConsts (.deref (.var "K")) == .deref (.lit (.int 3))

-- assign recursion (rhs only; name is a string, not an expression).
#guard substMlkemConsts (.assign "x" (.var "K")) == .assign "x" (.lit (.int 3))

-- forLoop recursion (lo, hi, body).
#guard substMlkemConsts
    (.forLoop "i" (.var "K") (.var "N") .unitVal) ==
    (.forLoop "i" (.lit (.int 3)) (.lit (.int 256)) .unitVal)

-- forLoopRev recursion.
#guard substMlkemConsts
    (.forLoopRev "i" (.var "K") (.var "N") .unitVal) ==
    (.forLoopRev "i" (.lit (.int 3)) (.lit (.int 256)) .unitVal)

-- whileLoop / whileFold recursion.
#guard substMlkemConsts
    (.whileLoop (.var "K") (.var "N")) ==
    (.whileLoop (.lit (.int 3)) (.lit (.int 256)))

#guard substMlkemConsts
    (.whileFold (.var "K") (.var "N")) ==
    (.whileFold (.lit (.int 3)) (.lit (.int 256)))

-- break_ / continue_.
#guard substMlkemConsts (.break_ none) == .break_ none
#guard substMlkemConsts (.break_ (some (.var "K"))) ==
    .break_ (some (.lit (.int 3)))
#guard substMlkemConsts .continue_ == .continue_

-- earlyReturn / questionMark.
#guard substMlkemConsts (.earlyReturn (.var "K")) ==
    .earlyReturn (.lit (.int 3))
#guard substMlkemConsts (.questionMark (.var "K")) ==
    .questionMark (.lit (.int 3))

-- forFoldRev / forFoldReturn / forFoldRevReturn / whileFoldReturn.
#guard substMlkemConsts
    (.forFoldRev "i" (.var "K") (.var "N") .unitVal) ==
    (.forFoldRev "i" (.lit (.int 3)) (.lit (.int 256)) .unitVal)

#guard substMlkemConsts
    (.forFoldReturn "i" (.var "K") (.var "N") .unitVal) ==
    (.forFoldReturn "i" (.lit (.int 3)) (.lit (.int 256)) .unitVal)

#guard substMlkemConsts
    (.forFoldRevReturn "i" (.var "K") (.var "N") .unitVal) ==
    (.forFoldRevReturn "i" (.lit (.int 3)) (.lit (.int 256)) .unitVal)

#guard substMlkemConsts
    (.whileFoldReturn (.var "K") (.var "N")) ==
    (.whileFoldReturn (.lit (.int 3)) (.lit (.int 256)))

-- cfBreak / cfContinue / cfBreakContinue.
#guard substMlkemConsts (.cfBreak (.var "K")) == .cfBreak (.lit (.int 3))
#guard substMlkemConsts (.cfContinue (.var "K")) == .cfContinue (.lit (.int 3))
#guard substMlkemConsts (.cfBreakContinue (.var "K")) ==
    .cfBreakContinue (.lit (.int 3))

-- match_ recursion (scrutinee and arm bodies; patterns are unchanged).
#guard substMlkemConsts
    (.match_ (.var "K") [(.wildcard, .var "N")]) ==
    (.match_ (.lit (.int 3)) [(.wildcard, .lit (.int 256))])

-- ML-DSA table sanity check.
#guard substMldsaConsts (.var "Q") == .lit (.int 8380417)
#guard substMldsaConsts (.var "K") == .lit (.int 6)
#guard substMldsaConsts (.var "L") == .lit (.int 5)

/-! ### foldArith smoke tests -/

-- Basic arithmetic folds (each op + lowercase alias).
#guard foldArith (.app "Mul" [.lit (.int 7), .lit (.int 6)]) ==
            ImpExpr.lit (.int 42)
#guard foldArith (.app "mul" [.lit (.int 7), .lit (.int 6)]) ==
            ImpExpr.lit (.int 42)
#guard foldArith (.app "Add" [.lit (.int 100), .lit (.int 28)]) ==
            ImpExpr.lit (.int 128)
#guard foldArith (.app "add" [.lit (.int 100), .lit (.int 28)]) ==
            ImpExpr.lit (.int 128)
#guard foldArith (.app "Sub" [.lit (.int 256), .lit (.int 1)]) ==
            ImpExpr.lit (.int 255)
#guard foldArith (.app "sub" [.lit (.int 256), .lit (.int 1)]) ==
            ImpExpr.lit (.int 255)
#guard foldArith (.app "Div" [.lit (.int 256), .lit (.int 2)]) ==
            ImpExpr.lit (.int 128)
#guard foldArith (.app "div" [.lit (.int 256), .lit (.int 2)]) ==
            ImpExpr.lit (.int 128)
#guard foldArith (.app "Rem" [.lit (.int 17), .lit (.int 5)]) ==
            ImpExpr.lit (.int 2)
#guard foldArith (.app "rem" [.lit (.int 17), .lit (.int 5)]) ==
            ImpExpr.lit (.int 2)

-- Division by 0 is not folded.
#guard foldArith (.app "Div" [.lit (.int 10), .lit (.int 0)]) ==
            .app "Div" [.lit (.int 10), .lit (.int 0)]

-- Remainder by 0 is not folded.
#guard foldArith (.app "Rem" [.lit (.int 10), .lit (.int 0)]) ==
            .app "Rem" [.lit (.int 10), .lit (.int 0)]

-- Non-arithmetic ops pass through (preserving recursion on children).
#guard foldArith (.app "poly_add" [.var "a", .var "b"]) ==
            .app "poly_add" [.var "a", .var "b"]

-- Unrecognized op with literal args also passes through.
#guard foldArith (.app "BitAnd" [.lit (.int 7), .lit (.int 3)]) ==
            .app "BitAnd" [.lit (.int 7), .lit (.int 3)]

-- Arity ≠ 2: no fold.
#guard foldArith (.app "Add" [.lit (.int 1), .lit (.int 2), .lit (.int 3)]) ==
            .app "Add" [.lit (.int 1), .lit (.int 2), .lit (.int 3)]
#guard foldArith (.app "Add" [.lit (.int 1)]) ==
            .app "Add" [.lit (.int 1)]

-- One operand non-literal: no fold (but children still recursed into).
#guard foldArith (.app "Mul" [.var "x", .lit (.int 2)]) ==
            .app "Mul" [.var "x", .lit (.int 2)]

-- Nested fold (bottom-up): inner Div reduces, then outer Mul.
#guard foldArith
    (.app "Mul" [.lit (.int 2), .app "Div" [.lit (.int 256), .lit (.int 2)]])
    == ImpExpr.lit (.int 256)

-- Triple nesting: Sub (Mul 4 8) (Div 16 8) = 32 - 2 = 30.
#guard foldArith
    (.app "Sub"
      [.app "Mul" [.lit (.int 4), .lit (.int 8)],
       .app "Div" [.lit (.int 16), .lit (.int 8)]])
    == ImpExpr.lit (.int 30)

-- Literal pass-through.
#guard foldArith (.lit (.int 7)) == .lit (.int 7)
#guard foldArith .unitVal == .unitVal
#guard foldArith (.var "x") == .var "x"

-- Recursion through letBind: rhs and body both folded.
#guard foldArith
    (.letBind "x" (.app "Mul" [.lit (.int 3), .lit (.int 4)])
      (.app "Add" [.lit (.int 1), .lit (.int 2)])) ==
    .letBind "x" (.lit (.int 12)) (.lit (.int 3))

-- Recursion through tuple.
#guard foldArith
    (.tuple [.app "Mul" [.lit (.int 2), .lit (.int 3)],
             .app "Add" [.lit (.int 4), .lit (.int 5)]]) ==
    .tuple [.lit (.int 6), .lit (.int 9)]

-- Recursion through ifThenElse.
#guard foldArith
    (.ifThenElse (.app "Sub" [.lit (.int 5), .lit (.int 5)])
      (.app "Mul" [.lit (.int 2), .lit (.int 3)])
      (.app "Add" [.lit (.int 1), .lit (.int 1)])) ==
    .ifThenElse (.lit (.int 0)) (.lit (.int 6)) (.lit (.int 2))

-- Recursion through forFold (lo, hi, body all folded).
#guard foldArith
    (.forFold "i" (.lit (.int 0)) (.app "Div" [.lit (.int 256), .lit (.int 2)])
      (.app "Mul" [.lit (.int 2), .lit (.int 3)])) ==
    .forFold "i" (.lit (.int 0)) (.lit (.int 128)) (.lit (.int 6))

-- Recursion through match_ (scrutinee + arm bodies).
#guard foldArith
    (.match_ (.app "Add" [.lit (.int 1), .lit (.int 2)])
      [(.wildcard, .app "Mul" [.lit (.int 4), .lit (.int 5)])]) ==
    .match_ (.lit (.int 3)) [(.wildcard, .lit (.int 20))]

-- Combined pipeline: substMlkemConsts then foldArith reduces forFold hi.
#guard foldArith (substMlkemConsts
    (.forFold "i" (.lit (.int 0)) (.app "Div" [.var "N", .lit (.int 2)]) .unitVal))
    == .forFold "i" (.lit (.int 0)) (.lit (.int 128)) .unitVal

-- mlkemFold convenience: same as the previous example.
#guard mlkemFold
    (.forFold "i" (.lit (.int 0)) (.app "Div" [.var "N", .lit (.int 2)]) .unitVal)
    == .forFold "i" (.lit (.int 0)) (.lit (.int 128)) .unitVal

-- mlkemFold on K * N = 3 * 256 = 768.
#guard mlkemFold (.app "Mul" [.var "K", .var "N"]) ==
            .lit (.int 768)

-- mldsaFold on K * L = 6 * 5 = 30.
#guard mldsaFold (.app "Mul" [.var "K", .var "L"]) ==
            .lit (.int 30)

-- mldsaFold on GAMMA1 / 2 = 524288 / 2 = 262144.
#guard mldsaFold (.app "Div" [.var "GAMMA1", .lit (.int 2)]) ==
            .lit (.int 262144)

end SmokeTests

end CatCrypt.Crypto.Hax
