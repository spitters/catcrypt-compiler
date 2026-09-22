/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.NatKernelEmit

/-!
# A rule-110 generation emitted through the kernel backend

One generation of rule 110 on a cyclic row of 256 cells, packed into the low 256
bits of a natural number, is seventeen straight-line operations on that number.
This module holds the program, the function `natKernelFn%` emits from it, and
the two equations that tie them together.

`rule110Step_run` is the translation validation: the emitted let-chain computes
what `FlatProg.run` says the program computes, by `rfl`, so the elaborator that
built the term is not trusted. `rule110Step_eq` identifies the emitted function
with the arithmetic it is meant to be, again by `rfl`.

The cell rule is `(c ∨ r) ∧ ¬(l ∧ c ∧ r)`: over the packed row, `l` is the row
rotated left by one and `r` the row rotated right by one, both cyclic at 256,
and negation within the row is `xor` with the all-ones mask.

## Slot numbering

Each operation's arguments are named by de Bruijn index into the value list,
counted from the most recent binding. The program below was laid out by
absolute slot — the input is slot `0` and each operation's result takes the next
slot — and converted with `index = slot - 1 - argument`, which is what
`FlatProg.run`'s environment discipline requires.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.NatKernel

set_option maxRecDepth 8000

/-- The low 256 bits set. -/
def rowMask256 : Nat := 2 ^ 256 - 1

/-- One generation of rule 110 on a 256-cell packed row, as a straight-line
    program over one input. -/
def rule110Prog : FlatProg where
  instrs :=
    [ { op := .const 1,          a := 0,  b := 0 }   -- slot 1
    , { op := .shiftLeft,        a := 1,  b := 0 }   -- slot 2: row <<< 1
    , { op := .const 255,        a := 0,  b := 0 }   -- slot 3
    , { op := .shiftRight,       a := 3,  b := 0 }   -- slot 4: row >>> 255
    , { op := .lor,              a := 2,  b := 0 }   -- slot 5
    , { op := .const rowMask256, a := 0,  b := 0 }   -- slot 6
    , { op := .land,             a := 1,  b := 0 }   -- slot 7: l
    , { op := .shiftRight,       a := 7,  b := 6 }   -- slot 8: row >>> 1
    , { op := .land,             a := 8,  b := 7 }   -- slot 9: row &&& 1
    , { op := .shiftLeft,        a := 0,  b := 6 }   -- slot 10
    , { op := .lor,              a := 2,  b := 0 }   -- slot 11
    , { op := .land,             a := 0,  b := 5 }   -- slot 12: r
    , { op := .lor,              a := 12, b := 0 }   -- slot 13: row ||| r
    , { op := .land,             a := 6,  b := 13 }  -- slot 14: l &&& row
    , { op := .land,             a := 0,  b := 2 }   -- slot 15: … &&& r
    , { op := .xor,              a := 9,  b := 0 }   -- slot 16: mask ^^^ …
    , { op := .land,             a := 3,  b := 0 }   -- slot 17
    ]
  ret := 0

/-- The generation function the backend emits from `rule110Prog`. -/
def rule110Step : Nat → Nat := natKernelFn% rule110Prog 1

/-- The emitted function computes what the program specifies. -/
theorem rule110Step_run (row : Nat) : rule110Step row = rule110Prog.run [row] := rfl

/-- The emitted function is one cyclic rule-110 generation on the packed row. -/
theorem rule110Step_eq (row : Nat) :
    rule110Step row =
      (row ||| (((row >>> 1) ||| ((row &&& 1) <<< 255)) &&& rowMask256))
        &&& (rowMask256 ^^^
              (((((row <<< 1) ||| (row >>> 255)) &&& rowMask256) &&& row)
                &&& (((row >>> 1) ||| ((row &&& 1) <<< 255)) &&& rowMask256))) := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.NatKernel
