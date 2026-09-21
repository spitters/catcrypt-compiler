/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# `natKernelDialect`: the Lean kernel as a target machine

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

The kernel reduces a closed application of certain `Nat` operations by calling
GMP instead of unfolding the definition. Those operations are the instruction
set of this dialect: a program over `natKernelDialect` is one whose every step
is a single GMP call when the kernel reduces it.

## The instruction set is fixed by the kernel, not chosen

`Nat` is the only type the kernel accelerates. Every other carrier reduces
through it: `BitVec w` is a structure over `Fin (2 ^ w)` over `Nat`, and
`UInt64` is a structure over `BitVec 64`, so an operation on either unfolds to
`Nat` operations plus the wrapping. The dialect therefore has one value type
for data (`.nat`) and one for the two predicates (`.bool`).

The fifteen operations below are the accelerated set, in the order the
reducer tests them:

| dialect op | kernel function | arity |
|---|---|---|
| `const n` | a literal | 0 |
| `add` | `Nat.add` | 2 |
| `sub` | `Nat.sub` | 2 |
| `mul` | `Nat.mul` | 2 |
| `pow` | `Nat.pow` | 2 |
| `gcd` | `Nat.gcd` | 2 |
| `mod` | `Nat.mod` | 2 |
| `div` | `Nat.div` | 2 |
| `beq` | `Nat.beq` | 2 |
| `ble` | `Nat.ble` | 2 |
| `land` | `Nat.land` | 2 |
| `lor` | `Nat.lor` | 2 |
| `xor` | `Nat.xor` | 2 |
| `shiftLeft` | `Nat.shiftLeft` | 2 |
| `shiftRight` | `Nat.shiftRight` | 2 |

Each op's denotation is the kernel function itself, so a reduced application
of `DialectDenote.denote` is an application the reducer recognises. The
`denote_*` lemmas at the end pin that: each is `rfl` against the `Nat`
function it claims, and a denotation that drifted to a wrapper would break
them.

`Nat.sub` truncates at zero and `Nat.div`/`Nat.mod` return zero at a zero
divisor. Those are the kernel's semantics and the dialect states them as they
are; a lowering into this dialect discharges its own side conditions.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.NatKernel

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. The dialect -/

/-- The value-type alphabet: unbounded naturals, and the booleans the two
    comparison operations return. -/
inductive NatKernelTy where
  | nat
  | bool
  deriving DecidableEq, Repr

/-- The operations the Lean kernel reduces through GMP, plus a literal. -/
inductive NatKernelOp where
  /-- A `Nat` literal. -/
  | const (n : Nat)
  /-- `Nat.add`. -/
  | add
  /-- `Nat.sub` (truncated at zero). -/
  | sub
  /-- `Nat.mul`. -/
  | mul
  /-- `Nat.pow`. -/
  | pow
  /-- `Nat.gcd`. -/
  | gcd
  /-- `Nat.mod` (zero at a zero divisor). -/
  | mod
  /-- `Nat.div` (zero at a zero divisor). -/
  | div
  /-- `Nat.beq`. -/
  | beq
  /-- `Nat.ble`. -/
  | ble
  /-- `Nat.land`. -/
  | land
  /-- `Nat.lor`. -/
  | lor
  /-- `Nat.xor`. -/
  | xor
  /-- `Nat.shiftLeft`. -/
  | shiftLeft
  /-- `Nat.shiftRight`. -/
  | shiftRight
  deriving DecidableEq, Repr

/-- The dialect whose machine is the Lean kernel's `Nat` reducer. -/
def natKernelDialect : Dialect where
  Op := NatKernelOp
  Ty := NatKernelTy

instance : TyDenote natKernelDialect.Ty where
  denote
    | .nat => Nat
    | .bool => Bool

/-- The argument types of an operation: none for a literal, two naturals for
    everything else. Named rather than inlined into the instance so that a
    proof can reduce it with `dsimp only [natSig]`; the instance field's match
    has no equation lemma a proof can reach. -/
@[reducible] def natSig : NatKernelOp → List NatKernelTy
  | .const _ => []
  | _ => [.nat, .nat]

/-- The result type of an operation: `.bool` for the two comparisons, `.nat`
    for the rest. -/
@[reducible] def natRet : NatKernelOp → NatKernelTy
  | .beq => .bool
  | .ble => .bool
  | _ => .nat

instance natKernelSig : DialectSignature natKernelDialect where
  sig := natSig
  ret := natRet

instance : DialectDenote natKernelDialect where
  denote
    | .const n,    _                                  => n
    | .add,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.add a b
    | .sub,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.sub a b
    | .mul,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.mul a b
    | .pow,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.pow a b
    | .gcd,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.gcd a b
    | .mod,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.mod a b
    | .div,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.div a b
    | .beq,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.beq a b
    | .ble,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.ble a b
    | .land,       .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.land a b
    | .lor,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.lor a b
    | .xor,        .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.xor a b
    | .shiftLeft,  .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.shiftLeft a b
    | .shiftRight, .cons (a : Nat) (.cons (b : Nat) .nil) => Nat.shiftRight a b

/-! ## 2. Each denotation is the kernel function it claims

A denotation that drifted to a wrapper — a `BitVec` round trip, a `Fin`
coercion, a defeq-but-not-syntactic alias — would still typecheck and would
still be extensionally right, while costing the reducer its GMP path. These
lemmas are what stop that: each holds by `rfl` against the `Nat` function
named in the table above. -/

/-- The argument vector shape the binary operations take. -/
abbrev args2 (a b : Nat) :
    HVector (fun t => ⟦t⟧)
      (([NatKernelTy.nat, NatKernelTy.nat] : List natKernelDialect.Ty)) :=
  .cons a (.cons b .nil)

theorem denote_const (n : Nat) :
    DialectDenote.denote (d := natKernelDialect) (.const n) .nil = n := rfl

theorem denote_add (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .add (args2 a b) = Nat.add a b := rfl

theorem denote_sub (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .sub (args2 a b) = Nat.sub a b := rfl

theorem denote_mul (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .mul (args2 a b) = Nat.mul a b := rfl

theorem denote_pow (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .pow (args2 a b) = Nat.pow a b := rfl

theorem denote_gcd (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .gcd (args2 a b) = Nat.gcd a b := rfl

theorem denote_mod (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .mod (args2 a b) = Nat.mod a b := rfl

theorem denote_div (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .div (args2 a b) = Nat.div a b := rfl

theorem denote_beq (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .beq (args2 a b) = Nat.beq a b := rfl

theorem denote_ble (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .ble (args2 a b) = Nat.ble a b := rfl

theorem denote_land (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .land (args2 a b) = Nat.land a b := rfl

theorem denote_lor (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .lor (args2 a b) = Nat.lor a b := rfl

theorem denote_xor (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .xor (args2 a b) = Nat.xor a b := rfl

theorem denote_shiftLeft (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .shiftLeft (args2 a b)
      = Nat.shiftLeft a b := rfl

theorem denote_shiftRight (a b : Nat) :
    DialectDenote.denote (d := natKernelDialect) .shiftRight (args2 a b)
      = Nat.shiftRight a b := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.NatKernel
