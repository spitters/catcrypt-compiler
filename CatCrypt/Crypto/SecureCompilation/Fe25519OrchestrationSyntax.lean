/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample

/-!
# Concrete syntax for the fe25519 orchestration layer (the ergonomic win)

`Fe25519OrchestrationExample.lean` builds the orchestration AST by hand — a wall
of `.RFor "i" n (.RSeq (.RCallN …) (.RCall …))` with every `Located` spelled as
`⟨"a_i", .TFp25519⟩`. This file adds a **Rust-like surface syntax** for that layer
so the same program reads:

```text
  orch% for "i" in 0..n {|
    "p"   := callN fe25519_mul("a_i", "b_i");
    "acc" := call  fe25519_add("p")
  |}
```

(The body brackets are `{| … |}` rather than bare `{ … }` — see the `orchFor`
syntax note below.)

The macro is a **transparent AST builder**: it performs no semantic
transformation, only the plumbing — string names become field-typed `Located`
slots (`⟨name, .TFp25519⟩`), a leaf identifier becomes the leaf-name string, and
the `;`-separated body folds right into `RSeq`. Its whole value is doing that
plumbing faithfully, which the payoff theorems below witness by `rfl`:

* `orchSyntax_eq_raw` — `orch% for … { … }` elaborates to **exactly** the raw AST
  term (`= macAccumulate n` by `rfl`). Concrete syntax adds ergonomics, not trust.
* `orchStmt_callN_eq_raw` / `orchStmt_call_eq_raw` — the per-statement builders,
  each `rfl`-equal to its `RCallN` / `RCall` target.

## Leaf-notation status

A minimal Jasmin-like leaf notation (`jexpr%`, §3) lands: it hides the
`Expr` record boilerplate (`retTy_eq := rfl`, the `HVector` `.cons`/`.nil`
spine) so a `Com jasminDialect` op reads `jexpr% (.regArith .mul 64) [x, y]`.
`macColSugar_eq_leaf` proves a two-op kernel built this way is `rfl`-equal to
the golden-path leaf `fe25519MacColLoCom`. The typed de-Bruijn resolution
(`.here` / `.there (.there …)`) is outside its scope: turning a *named* kernel
variable into its `Ctxt.Var` index needs a typed symbol-table elaborator (the
index carries the proof its slot has the right `JasminTy`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open Lean

/-! ## 1. The orchestration surface syntax

Every orchestration slot is a field element (`TowerType.TFp25519`), so the
surface names a slot by a bare string literal; the builder attaches the type. -/

/-- Right-fold a statement list into `RSeq`. `orchSeq [a, b]` is definitionally
    `RSeq a b`, so a two-statement body elaborates to exactly the hand-written
    `.RSeq … …` term (the basis of the `rfl` payoff). -/
def orchSeq : List LowCT → LowCT
  | []      => .RSkip
  | [c]     => c
  | c :: cs => .RSeq c (orchSeq cs)

/-- A single orchestration statement: an accumulating leaf call. -/
declare_syntax_cat orchStmt

/-- `dst := callN fn(a, b, …)` builds `RCallN "fn" [dst] [a, b, …]`
    (multi-destination leaf call, one destination). -/
syntax:min str ":=" "callN" ident "(" str,* ")" : orchStmt
/-- `dst := call fn(a, b, …)` builds `RCall "fn" dst [a, b, …]`
    (single-destination accumulating leaf call). -/
syntax:min str ":=" "call" ident "(" str,* ")" : orchStmt

macro_rules
  | `(orchStmt| $dst:str := callN $fn:ident ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCallN $fnName
          [(⟨$dst, TowerType.TFp25519⟩ : Located)]
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])
  | `(orchStmt| $dst:str := call $fn:ident ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCall $fnName
          (⟨$dst, TowerType.TFp25519⟩ : Located)
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])

/-- `orch% for i in 0..n {| s₁ ; s₂ ; … |}` — a bounded-loop orchestration over
    field-op leaf calls. Elaborates to `RFor i n (orchSeq [s₁, s₂, …])`. The
    lower bound is fixed at `0` (`RFor` is 0-based); it is written for
    readability and ignored by the builder. The body delimiters are `{| … |}`
    rather than `{ … }` because bare braces collide with Lean's structure-instance
    syntax inside the elaborating quotation. -/
syntax (name := orchFor) "orch% " "for " str " in " num ".." term " {|" sepBy1(orchStmt, ";") "|}" : term

macro_rules
  | `(orch% for $i:str in $_lo:num .. $n:term {| $[$stmts];* |}) => do
      -- each statement node macro-expands to a `LowCT` term in list position
      let stmtsT : Array (TSyntax `term) := stmts.map (fun s => ⟨s.raw⟩)
      `(LowCT.RFor $i $n (orchSeq [$[$stmtsT],*]))

/-! ## 2. The payoff — concrete syntax = raw AST, by `rfl`

The whole point of a transparent builder: the ergonomic surface and the
hand-written AST are the *same term*. -/

/-- **The ergonomic win, witnessed.** The Rust-like surface elaborates to
    **exactly** the raw orchestration AST `macAccumulate n` — `rfl`. The concrete
    syntax adds readability and hides the `Located`/`RSeq` plumbing without
    introducing any new trust: there is nothing to verify about the macro beyond
    this definitional identity. -/
theorem orchSyntax_eq_raw (n : Nat) :
    (orch% for "i" in 0.. n {|
        "p"   := callN fe25519_mul("a_i", "b_i");
        "acc" := call  fe25519_add("p")
      |})
      = macAccumulate n := rfl

/-- The `callN` statement builder is `rfl`-equal to its raw `RCallN`. -/
theorem orchStmt_callN_eq_raw :
    (orch% for "i" in 0.. 1 {| "p" := callN fe25519_mul("a_i", "b_i") |})
      = .RFor "i" 1
          (.RCallN "fe25519_mul" [⟨"p", .TFp25519⟩] [⟨"a_i", .TFp25519⟩, ⟨"b_i", .TFp25519⟩]) := rfl

/-- The `call` statement builder is `rfl`-equal to its raw `RCall`. -/
theorem orchStmt_call_eq_raw :
    (orch% for "i" in 0.. 1 {| "acc" := call fe25519_add("p") |})
      = .RFor "i" 1 (.RCall "fe25519_add" ⟨"acc", .TFp25519⟩ [⟨"p", .TFp25519⟩]) := rfl

/-! ## 3. A minimal Jasmin-like leaf notation

`jexpr% op [arg₀, arg₁, …]` builds the `Expr` record for a single dialect op,
hiding the `retTy_eq := rfl` obligation and the `HVector` `.cons`/`.nil` spine.
The arguments are still explicit typed de-Bruijn `Ctxt.Var`s (`.here`,
`.there …`) — see the module docstring for why name→index resolution is the
deferred hard part. -/

/-- Build an `HVector` spine `.cons a₀ (.cons a₁ … .nil)` from a term list. -/
macro "hvec%" "[" xs:term,* "]" : term => do
  let mut acc ← `(HVector.nil)
  for x in xs.getElems.reverse do
    acc ← `(HVector.cons $x $acc)
  return acc

/-- `jexpr% op [args…]` = the `Expr` record `{ op, retTy_eq := rfl, args }`. -/
macro "jexpr%" op:term:max "[" args:term,* "]" : term =>
  `({ op := $op, retTy_eq := rfl, args := hvec% [$args,*] })

/-- The multiply-accumulate column low-word kernel, built through the leaf
    notation: `p_lo := a * b ; s := acc_lo + p_lo ; ret s`. Compare the
    hand-written `Fe25519MulLeaf.fe25519MacColLoCom` (same body, explicit
    `Expr` records). -/
def macColSugar : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- p_lo := a * b     (a = index 2, b = index 3)
  .var (jexpr% (JasminOp.regArith .mul 64) [.there (.there .here), .there (.there (.there .here))])
  -- s := acc_lo + p_lo   (acc_lo = index 1, p_lo = index 0)
  (.var (jexpr% (JasminOp.regArith .add 64) [.there .here, .here])
    (.ret .here))

/-- **The leaf notation is a transparent builder too** — `rfl`. The kernel built
    through `jexpr%` is *exactly* the hand-authored golden-path leaf
    `fe25519MacColLoCom`; the notation only hid the `Expr`-record boilerplate. -/
theorem macColSugar_eq_leaf :
    macColSugar = Fe25519MulLeaf.fe25519MacColLoCom := rfl

end CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample
