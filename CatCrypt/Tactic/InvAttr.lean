/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# Simp sets for inversion and code layout

The two named simp sets of `CatCrypt.Tactic.Inv`. An attribute registered with
`register_simp_attr` is usable only in modules that import the registering module, so the
registration is a module of its own; `CatCrypt.Tactic.Inv` tags the lemmas.

## Main definitions

* `ir_inv`: inversion of a hypothesis `f x = some y` over `Option`-valued executable
  functions and Boolean checkers.
* `code_layout`: normalisation of instruction lists built by `++` and `::`.
-/

@[expose] public section

/-- Inversion lemmas for a hypothesis `f x = some y`: monadic `Option` binds and maps,
    `if`-guards returning `none`, constructor injectivity, and Boolean conjunctions and
    equality tests. -/
register_simp_attr ir_inv

/-- Layout lemmas for instruction lists: associativity of `++`, `::` against `++`,
    lengths, indexing into an append and membership in an append. -/
register_simp_attr code_layout
