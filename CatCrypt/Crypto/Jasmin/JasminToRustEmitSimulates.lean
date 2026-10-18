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
# Printer equations for `JasminToRustEmit.ppPExpr`

The lemmas of this module state, by `rfl`, the Rust source string the
expression printer `ppPExpr` produces on each `PExpr` constructor. They are
facts about the printed text; no statement here relates the printed program to
the Jasmin semantics.

## Main results

* `ppPExpr_simulates_Pvar`, `ppPExpr_simulates_Pconst`, `ppPExpr_simulates_Pif`,
  `ppPExpr_simulates_Papp2_Oadd` and the other `ppPExpr_simulates_*` lemmas —
  the printed string for each constructor.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.JasminToRustEmitSimulates

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.JasminToRustEmit
open CatCrypt.Crypto.Jasmin.SemBridge

/-! ## §1.  Per-constructor lemmas for the expression printer

Each lemma states what `ppPExpr` produces on a single constructor of
`PExpr`. -/

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

end CatCrypt.Crypto.Jasmin.JasminToRustEmitSimulates
