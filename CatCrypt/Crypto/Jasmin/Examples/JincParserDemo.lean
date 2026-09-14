/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.JincParser
public import CatCrypt.Crypto.Jasmin.JincParser


@[expose] public section
set_option autoImplicit false

/-!
# Demo: parse one round of a MAYO GF(16) multiply-step leaf

This file applies the `.jinc` text → `JasminCoqSemMirror.Cmd` parser
(`JincParser.parseBody`) to one round of the inner `for bit_i = 0 to 4` loop of
`gf16_mul_scalar`, a MAYO GF(16) scalar-multiply leaf written in Jasmin. The
source text is `gf16MulRoundSrc`; the reference AST `handGf16MulStepCmd` is
written by hand in this file.

## Constructs used by the source text

- `reg u8 ...;` declarations
- straight-line assignments (`x = expr;`)
- compound `>>=` and `<<=`
- binary `&`, `^` with two atoms
- unary `-x`
- hex constants (`0x1`, `0x3`, `0xf`) and decimal shift amounts

## What is checked

The parser output is compared with `handGf16MulStepCmd` through projections,
each checked by `native_decide`:

- the instruction counts are equal (an `example`);
- the per-instruction pair (LHS `Lval` constructor, RHS `Pexpr` constructor)
  agrees (`parsedCmd_shapes_eq_handShapes`);
- the LHS variable names agree (`parsedCmd_lhs_names_eq`);
- the RHS head-operator tags agree (`parsedCmd_rhs_ops_eq`).

Equality of the two `Cmd` values is not proved, and neither is equivalence of
their execution under `JasminCoqSemMirror` or agreement with a specification.
-/

namespace CatCrypt.Crypto.Jasmin.JincParserDemo

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.Jasmin.JincParser

/-! ## §0. Hand-authored reference AST

The reference AST for one round, written with the `mkLvar` / `aword .U8` /
`AT_none` convention: every instruction is a `Cassgn` of type `aword .U8` with
assignment tag `AT_none` to a `u8` variable, and variables are read with local
scope (`mkLvar`). -/

/-- A `reg u8` variable. -/
def vU8 (s : String) : VarI :=
  { v_var := { vtype := .aword .U8, vname := s } }

def vSh   : VarI := vU8 "sh"
def vBb   : VarI := vU8 "bb"
def vR    : VarI := vU8 "r"
def vBitV : VarI := vU8 "bit_v"
def vHi   : VarI := vU8 "hi"
def vMask : VarI := vU8 "mask"
def vProd : VarI := vU8 "prod"

def rdU8 (v : VarI) : Pexpr := .Pvar (mkLvar v)
def wrU8 (v : VarI) : Lval := .Lvar v
def cU8 (n : Nat) : Pexpr :=
  .Papp1 (.Oword_of_int .U8) (.Pconst (Int.ofNat n))

/-- One round of `gf16_mul_scalar`'s inner loop body, hand-authored as a
    `Cmd` by transcribing `gf16MulRoundSrc` instruction by instruction. -/
def handGf16MulStepCmd : Cmd :=
  let mk (l : Lval) (e : Pexpr) : Instr :=
    .MkI () (.Cassgn l .AT_none (.aword .U8) e)
  [ mk (wrU8 vBitV) (rdU8 vBb)
  , mk (wrU8 vBitV) (.Papp2 (.Oland .U8) (rdU8 vBitV) (cU8 1))
  , mk (wrU8 vProd) (rdU8 vSh)
  , mk (wrU8 vBitV) (.Papp1 (.Oneg (.Op_w .U8)) (rdU8 vBitV))
  , mk (wrU8 vProd) (.Papp2 (.Oland .U8) (rdU8 vProd) (rdU8 vBitV))
  , mk (wrU8 vR)    (.Papp2 (.Olxor .U8) (rdU8 vR) (rdU8 vProd))
  , mk (wrU8 vBb)   (.Papp2 (.Olsr .U8) (rdU8 vBb) (cU8 1))
  , mk (wrU8 vHi)   (rdU8 vSh)
  , mk (wrU8 vHi)   (.Papp2 (.Olsr .U8) (rdU8 vHi) (cU8 3))
  , mk (wrU8 vSh)   (.Papp2 (.Olsl (.Op_w .U8)) (rdU8 vSh) (cU8 1))
  , mk (wrU8 vHi)   (.Papp2 (.Oland .U8) (rdU8 vHi) (cU8 1))
  , mk (wrU8 vHi)   (.Papp1 (.Oneg (.Op_w .U8)) (rdU8 vHi))
  , mk (wrU8 vMask) (cU8 3)
  , mk (wrU8 vHi)   (.Papp2 (.Oland .U8) (rdU8 vHi) (rdU8 vMask))
  , mk (wrU8 vSh)   (.Papp2 (.Olxor .U8) (rdU8 vSh) (rdU8 vHi))
  , mk (wrU8 vSh)   (.Papp2 (.Oland .U8) (rdU8 vSh) (cU8 0xf))
  ]

/-! ## §1. Source: one round of `gf16_mul_scalar`

The body of the inner `for bit_i = 0 to 4` loop of the Jasmin leaf
`gf16_mul_scalar` (one iteration), preceded by its `reg u8` declarations. -/

/-- Source text of one round of `gf16_mul_scalar`'s inner loop. -/
def gf16MulRoundSrc : String := "
  reg u8 r sh bb bit_v hi mask prod;
  bit_v = bb;
  bit_v = bit_v & 0x1;
  prod = sh;
  bit_v = -bit_v;
  prod = prod & bit_v;
  r = r ^ prod;
  bb >>= 1;
  hi = sh;
  hi >>= 3;
  sh <<= 1;
  hi = hi & 0x1;
  hi = -hi;
  mask = 0x3;
  hi = hi & mask;
  sh = sh ^ hi;
  sh = sh & 0xf;
"

/-! ## §2. Parse and inspect -/

/-- Parser result on the round source. -/
def parsedCmd : Except String Cmd := parseBody gf16MulRoundSrc

-- Quick sanity: print the number of instructions.
#eval (match parsedCmd with
  | .ok c => s!"parsed {c.length} instructions"
  | .error e => s!"parse error: {e}")

/-! ## §3. Comparison with the hand-authored AST

`handGf16MulStepCmd` (§0) transcribes the same body into `Instr` / `Cassgn`
terms. This section and the next two compare projections of the parser output
with the same projections of `handGf16MulStepCmd`. -/

/-- The parser-produced `Cmd` extracted from the `Except` (the empty `Cmd` on a
    parse error). -/
def parsedCmdValue : Cmd :=
  match parsedCmd with
  | .ok c => c
  | .error _ => []

/-- The instruction counts agree (checked by `native_decide`). -/
example : parsedCmdValue.length = handGf16MulStepCmd.length := by
  native_decide

-- Diagnostic: report whether the parser output has a first instruction.
#eval (parsedCmdValue.head?.map fun _ => "first instr parsed OK").getD "no instructions"

-- **Shape comparison.** The parser output and the hand-authored AST are
-- compared through constructor-tag projections rather than through
-- `DecidableEq Instr`, which does not reduce (`Value` carries `JArrayMirror`).

/-- Tag a `Pexpr` constructor by a small enum for compare-friendly
    projection. -/
def pexprTag : Pexpr → Nat
  | .Pconst _      => 1
  | .Pbool _       => 2
  | .Parr_init _ _ => 3
  | .Pvar _        => 4
  | .Pget _ _ _ _ _ => 5
  | .Psub _ _ _ _ _ => 6
  | .Pload _ _ _   => 7
  | .Papp1 _ _     => 8
  | .Papp2 _ _ _   => 9
  | .PappN _ _     => 10
  | .Pif _ _ _ _   => 11

/-- Tag an `Lval` constructor. -/
def lvalTag : Lval → Nat
  | .Lnone _ _      => 1
  | .Lvar _         => 2
  | .Lmem _ _ _ _   => 3
  | .Laset _ _ _ _ _ => 4
  | .Lasub _ _ _ _ _ => 5

/-- Tag an `InstrR` constructor. -/
def instrRTag : InstrR → Nat
  | .Cassgn _ _ _ _  => 1
  | .Copn _ _ _ _    => 2
  | .Csyscall _ _ _  => 3
  | .Cif _ _ _       => 4
  | .Cfor _ _ _      => 5
  | .Cwhile _ _ _ _ _ => 6
  | .Ccall _ _ _     => 7

/-- Project an `Instr` to its top-level tag (always 1 = MkI). -/
def instrTopTag : Instr → Nat
  | .MkI _ _ => 1

/-- Get the `InstrR` payload of an `Instr.MkI`. -/
def instrPayload : Instr → InstrR
  | .MkI _ ir => ir

/-- Project a `Cassgn` to `(lvalTag, pexprTag)` for shallow comparison.
    Returns `(0, 0)` for non-`Cassgn`. -/
def cassgnShape : InstrR → Nat × Nat
  | .Cassgn lv _ _ e => (lvalTag lv, pexprTag e)
  | _ => (0, 0)

/-- Shape vector of the parser output: for each instruction, the pair
    (`lvalTag`, `pexprTag`) of its `Cassgn`, or `(0, 0)` if it is not a
    `Cassgn`. -/
def parsedShapes : List (Nat × Nat) :=
  parsedCmdValue.map (fun i => cassgnShape (instrPayload i))

/-- Shape vector of the hand-authored AST. -/
def handShapes : List (Nat × Nat) :=
  handGf16MulStepCmd.map (fun i => cassgnShape (instrPayload i))

#eval parsedShapes
#eval handShapes

/-- **Shape agreement.** The parser output and `handGf16MulStepCmd` have equal
    shape vectors: the same length and, per instruction, the same `Lval` and
    `Pexpr` constructor tags of the `Cassgn`. Checked by `native_decide`. -/
theorem parsedCmd_shapes_eq_handShapes : parsedShapes = handShapes := by
  native_decide

/-! ## §4. Deeper structural test: variable names + ops

For each `Cassgn`, project the LHS variable name (this section) and the
head operator of the RHS (§5). Both projections have decidable equality. -/

/-- Extract the LHS variable name from an `Instr` that is a `Cassgn (Lvar v) ...`. -/
def cassgnLhsName? : Instr → Option String
  | .MkI _ (.Cassgn (.Lvar x) _ _ _) => some x.v_var.vname
  | _ => none

/-- Names extracted from the parser output. -/
def parsedLhsNames : List (Option String) := parsedCmdValue.map cassgnLhsName?

/-- Names extracted from the hand-authored AST. -/
def handLhsNames : List (Option String) := handGf16MulStepCmd.map cassgnLhsName?

#eval parsedLhsNames
#eval handLhsNames

/-- **LHS name agreement.** Per instruction, the LHS variable name of a
    `Cassgn (Lvar x) …` (or `none` otherwise) agrees between the parser output
    and `handGf16MulStepCmd`. Checked by `native_decide`. -/
theorem parsedCmd_lhs_names_eq : parsedLhsNames = handLhsNames := by
  native_decide

/-! ## §5. Op-discriminator test

Project each `Cassgn`'s RHS to a string tag of its head constructor and, for
`Papp1`/`Papp2`, its operator constructor (for example `Papp2.Olsr` versus
`Papp2.Olsl`). Operators outside the listed ones map to `Papp1.other` or
`Papp2.other`; operand trees and operator width arguments are not compared. -/

/-- Project the RHS head operator as a short string. -/
def cassgnRhsOpTag : Instr → String
  | .MkI _ (.Cassgn _ _ _ (.Pvar _))         => "Pvar"
  | .MkI _ (.Cassgn _ _ _ (.Papp1 op _))     =>
      match op with
      | .Oneg _ => "Papp1.Oneg"
      | .Oword_of_int _ => "Papp1.Oword_of_int"
      | _ => "Papp1.other"
  | .MkI _ (.Cassgn _ _ _ (.Papp2 op _ _))   =>
      match op with
      | .Oland _ => "Papp2.Oland"
      | .Olxor _ => "Papp2.Olxor"
      | .Olor  _ => "Papp2.Olor"
      | .Olsr  _ => "Papp2.Olsr"
      | .Olsl  _ => "Papp2.Olsl"
      | _ => "Papp2.other"
  | _ => "other"

/-- RHS op tags from the parser output. -/
def parsedRhsOps : List String := parsedCmdValue.map cassgnRhsOpTag

/-- RHS op tags from the hand-authored AST. -/
def handRhsOps : List String := handGf16MulStepCmd.map cassgnRhsOpTag

#eval parsedRhsOps
#eval handRhsOps

/-- **RHS operator-tag agreement.** Per instruction, the RHS head-operator tag
    (`cassgnRhsOpTag`) agrees between the parser output and
    `handGf16MulStepCmd`. Checked by `native_decide`. -/
theorem parsedCmd_rhs_ops_eq : parsedRhsOps = handRhsOps := by
  native_decide

/-! ## §6. Summary

| Property compared (parser output vs. `handGf16MulStepCmd`) | Declaration | Tactic |
|---|---|---|
| Instruction count | `example` in §3 | `native_decide` |
| Per-instruction (`Lval`, `Pexpr`) constructor tags | `parsedCmd_shapes_eq_handShapes` | `native_decide` |
| LHS variable names | `parsedCmd_lhs_names_eq` | `native_decide` |
| RHS head-operator tags | `parsedCmd_rhs_ops_eq` | `native_decide` |

The projections do not compare the variable scope, the assignment tag, the
assignment type, the operator width arguments, or the operand trees below the
head operator. Equality of the parsed `Cmd` with `handGf16MulStepCmd`, and
equivalence of their execution under `JasminCoqSemMirror`, are not proved in
this package.
-/

end CatCrypt.Crypto.Jasmin.JincParserDemo
