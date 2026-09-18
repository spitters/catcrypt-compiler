/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.JasminToRustEmit
public import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.Jasmin.JasminSem

/-!
# Simulation theorem for `JasminToRustEmit.ppFunDecl`

The per-constructor lemmas of §1 state, by `rfl`, the string `ppPExpr` prints
for each expression constructor.

§2 states the simulation of `ppFunDecl` against an opaque `RustcExec`
predicate. `ppFunDecl_simulates` is the named axiom `RustcExec_correct`
applied to its hypothesis, and `RustcExec` is constrained by nothing else, so
the statement is assumed rather than proved. The axiom bundles the
correctness of the printer with that of rustc and LLVM; the printer's part has
no proof in this module.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.JasminToRustEmitSimulates

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.JasminToRustEmit
open CatCrypt.Crypto.Jasmin.SemBridge

/-! ## §1.  Per-constructor lemmas for the expression printer

Each lemma states what `ppPExpr` produces on a single constructor of
`PExpr`. These are the building blocks for a future inductive proof of a
full simulation theorem `ppFunDecl_simulates`. -/

/-- The expression printer on a `Pvar` produces the Rust variable name.
    This is the simplest non-trivial case: a `GVar` is rendered via
    `rustGVar`. -/
theorem ppPExpr_simulates_Pvar (g : GVar) :
    ppPExpr (PExpr.Pvar g) = rustGVar g := by
  rfl

/-- The expression printer on a `Pconst` produces the decimal `toString`. -/
theorem ppPExpr_simulates_Pconst (z : Int) :
    ppPExpr (PExpr.Pconst z) = toString z := by
  rfl

/-- The expression printer on `Pbool true` produces the string `"true"`. -/
theorem ppPExpr_simulates_Pbool_true :
    ppPExpr (PExpr.Pbool true) = "true" := by
  rfl

/-- The expression printer on `Pbool false` produces the string `"false"`. -/
theorem ppPExpr_simulates_Pbool_false :
    ppPExpr (PExpr.Pbool false) = "false" := by
  rfl

/-- The expression printer on a `Papp1` of `Olnot` wraps the recursive
    pretty-print in `!(` … `)` brackets — this is dictated by `rustSOp1`. -/
theorem ppPExpr_simulates_Papp1_Olnot (ws : WSize) (e : PExpr) :
    ppPExpr (PExpr.Papp1 (SOp1.Olnot ws) e) = "!(" ++ ppPExpr e ++ ")" := by
  rfl

/-- The expression printer on a `Papp1` of `Onot` (boolean negation) likewise
    wraps the operand in `!(` … `)`. -/
theorem ppPExpr_simulates_Papp1_Onot (e : PExpr) :
    ppPExpr (PExpr.Papp1 SOp1.Onot e) = "!(" ++ ppPExpr e ++ ")" := by
  rfl

/-- The expression printer on `Parr_init n` produces a Rust zero-initialised
    `[0u8; n]` array literal. -/
theorem ppPExpr_simulates_Parr_init (n : Nat) :
    ppPExpr (PExpr.Parr_init n) = "[0u8; " ++ toString n ++ "]" := by
  rfl

/-- The expression printer on `Pif _ c et ef` produces a Rust ternary-style
    `if c { et } else { ef }` form. -/
theorem ppPExpr_simulates_Pif (ty : SType) (c et ef : PExpr) :
    ppPExpr (PExpr.Pif ty c et ef) =
      "if " ++ ppPExpr c ++ " { " ++ ppPExpr et ++ " } else { " ++
      ppPExpr ef ++ " }" := by
  rfl

/-- The expression printer on a `Papp2` of `Oadd` (a method-like binop) emits
    `.wrapping_add` in suffix-call form. -/
theorem ppPExpr_simulates_Papp2_Oadd (ws : WSize) (e1 e2 : PExpr) :
    ppPExpr (PExpr.Papp2 (SOp2.Oadd ws) e1 e2) =
      "(" ++ ppPExpr e1 ++ ")" ++ ".wrapping_add" ++ "(" ++ ppPExpr e2 ++ ")" := by
  rfl

/-- The expression printer on a `Papp2` of `Obeq` (a normal infix binop) emits
    `(e1 == e2)` with surrounding parens. -/
theorem ppPExpr_simulates_Papp2_Obeq (e1 e2 : PExpr) :
    ppPExpr (PExpr.Papp2 SOp2.Obeq e1 e2) =
      "(" ++ ppPExpr e1 ++ " " ++ "==" ++ " " ++ ppPExpr e2 ++ ")" := by
  rfl

/-- The expression printer on a `PappN _ _` falls through to the
    `unhandled-PappN` placeholder string — this lemma fixes the surface so
    callers can detect that PappN is currently unsupported. -/
theorem ppPExpr_simulates_PappN (op : OpN) (es : List PExpr) :
    ppPExpr (PExpr.PappN op es) = "/* unhandled PappN */" := by
  rfl

/-! ## §2.  Top-level simulation statement

The statement ties the emitted Rust source `ppFunDecl fd` to the `jasminSem`
big-step operational semantics through an opaque `RustcExec` predicate, and
the named axiom `RustcExec_correct` asserts it. -/

/-- Trust-rustc oracle: predicate "rustc compiles `src` and the resulting
    binary, when executed, transitions `σ` to `σ'` (under the same
    `RustState` view used by the Jasmin operational semantics)." Opaque —
    we do not model rustc / LLVM internals. -/
opaque RustcExec : String → LowCT.RustState → LowCT.RustState → Prop

/-- **Trust leaf for the printer and rustc together** (named axiom).

    For any `FunDecl fd` and any `jasminSem` derivation taking `σ` to `σ'`
    on `fd.body`, the rustc-compiled emitted source `ppFunDecl fd` exhibits
    the same transition under `RustcExec`. The axiom bundles two claims: that
    `ppFunDecl` prints a program with the meaning of `fd.body`, and that rustc
    and LLVM execute it faithfully. The first is a property of the printer and
    is not proved. -/
axiom RustcExec_correct
    (leafSpec : LowCT.LeafSpec) (fd : FunDecl) (σ σ' : LowCT.RustState) :
    jasminSem leafSpec fd.body σ σ' → RustcExec (ppFunDecl fd) σ σ'

/-- (assumed bound) **JasminToRustEmit simulation statement.**

    For any `FunDecl`, `RustcExec (ppFunDecl fd)` holds of every `jasminSem`
    transition of `fd.body`. The statement is the axiom `RustcExec_correct`
    applied to its hypothesis. `RustcExec` is opaque and constrained by
    nothing but that axiom, so the statement carries no information about the
    printed text: the correctness of `ppFunDecl` is assumed here, not proved,
    and the axiom covers outputs containing the printer's `unhandled`
    markers. -/
theorem ppFunDecl_simulates
    (leafSpec : LowCT.LeafSpec) (fd : FunDecl) (σ σ' : LowCT.RustState)
    (h : jasminSem leafSpec fd.body σ σ') :
    RustcExec (ppFunDecl fd) σ σ' :=
  RustcExec_correct leafSpec fd σ σ' h

end CatCrypt.Crypto.Jasmin.JasminToRustEmitSimulates
