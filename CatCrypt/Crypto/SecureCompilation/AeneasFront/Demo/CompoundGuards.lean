/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestAssertCfg

/-!
# Conditions with compound operands of the Aeneas test `assert_cfg`

The functions `assert_not_and`, `assert_not_b0_or_b1`, `assert_b0_or_not_b1` and
`assert_not_b0_or_not_b1` of the Aeneas test output `assert_cfg` (`TestAssertCfg`, copied
unchanged from Aeneas commit `b08bf81`) assert a disjunction whose operands are negations of
Boolean arguments, as `massert ((¬ b0) || b1)`. The condition is no single expression of the
reader `ReadCond`; `reifyAeneas%` reads it as a prefix of bindings and a bit (`ReadBit`): the
decision of `b = true` is the bit `b` (`readBitDecEq`), a decided negation binds the negation of
the bit of its operand (`readBitDecNot`), the disjunction binds the connective of the bits of its
operands (`readBitConn`), and the guard is `Reify.guardP` at that prefix. The functions
`assert_not_b0_and_b1`, `assert_b0_and_not_b1` and `assert_not_b0_and_not_b1` assert their two
conditions in turn, each a Boolean argument or its negation, read as one expression by
`Reify.assert`.

Each definition below is the output of the elaborator, with its soundness statement proved by
construction; each theorem is its composition with `Reify.toDenote`.

## Main results

* `assertNotAnd_denote`, `assertNotB0OrB1_denote`, `assertB0OrNotB1_denote`,
  `assertNotB0OrNotB1_denote` — disjunctions of negations, read as a prefix and a bit.
* `assertNotB0AndB1_denote`, `assertB0AndNotB1_denote`, `assertNotB0AndNotB1_denote` — two
  assertions in turn.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.Hax (hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP)

/-- `assert_cfg.assert_not_and` read as an NF program. -/
def assertNotAnd := reifyAeneas% assert_cfg.assert_not_and

/-- `assert_cfg.assert_not_b0_or_b1` read as an NF program. -/
def assertNotB0OrB1 := reifyAeneas% assert_cfg.assert_not_b0_or_b1

/-- `assert_cfg.assert_b0_or_not_b1` read as an NF program. -/
def assertB0OrNotB1 := reifyAeneas% assert_cfg.assert_b0_or_not_b1

/-- `assert_cfg.assert_not_b0_or_not_b1` read as an NF program. -/
def assertNotB0OrNotB1 := reifyAeneas% assert_cfg.assert_not_b0_or_not_b1

/-- `assert_cfg.assert_not_b0_and_b1` read as an NF program. -/
def assertNotB0AndB1 := reifyAeneas% assert_cfg.assert_not_b0_and_b1

/-- `assert_cfg.assert_b0_and_not_b1` read as an NF program. -/
def assertB0AndNotB1 := reifyAeneas% assert_cfg.assert_b0_and_not_b1

/-- `assert_cfg.assert_not_b0_and_not_b1` read as an NF program. -/
def assertNotB0AndNotB1 := reifyAeneas% assert_cfg.assert_not_b0_and_not_b1

/-- A value of `assert_cfg.assert_not_and` is the denotation of its NF program. -/
theorem assertNotAnd_denote (b0 b1 : Bool) (h : assert_cfg.assert_not_and b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel assertNotAnd.prog (wCons b0 (wCons b1 vNil)) = some (.cons () .nil) :=
  Reify.toDenote (assertNotAnd.sound b0 b1) h

/-- A value of `assert_cfg.assert_not_b0_or_b1` is the denotation of its NF program. -/
theorem assertNotB0OrB1_denote (b0 b1 : Bool) (h : assert_cfg.assert_not_b0_or_b1 b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel assertNotB0OrB1.prog (wCons b0 (wCons b1 vNil)) = some (.cons () .nil) :=
  Reify.toDenote (assertNotB0OrB1.sound b0 b1) h

/-- A value of `assert_cfg.assert_b0_or_not_b1` is the denotation of its NF program. -/
theorem assertB0OrNotB1_denote (b0 b1 : Bool) (h : assert_cfg.assert_b0_or_not_b1 b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel assertB0OrNotB1.prog (wCons b0 (wCons b1 vNil)) = some (.cons () .nil) :=
  Reify.toDenote (assertB0OrNotB1.sound b0 b1) h

/-- A value of `assert_cfg.assert_not_b0_or_not_b1` is the denotation of its NF program. -/
theorem assertNotB0OrNotB1_denote (b0 b1 : Bool) (h : assert_cfg.assert_not_b0_or_not_b1 b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel assertNotB0OrNotB1.prog (wCons b0 (wCons b1 vNil)) = some (.cons () .nil) :=
  Reify.toDenote (assertNotB0OrNotB1.sound b0 b1) h

/-- A value of `assert_cfg.assert_not_b0_and_b1` is the denotation of its NF program. -/
theorem assertNotB0AndB1_denote (b0 b1 : Bool) (h : assert_cfg.assert_not_b0_and_b1 b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel assertNotB0AndB1.prog (wCons b0 (wCons b1 vNil)) = some (.cons () .nil) :=
  Reify.toDenote (assertNotB0AndB1.sound b0 b1) h

/-- A value of `assert_cfg.assert_b0_and_not_b1` is the denotation of its NF program. -/
theorem assertB0AndNotB1_denote (b0 b1 : Bool) (h : assert_cfg.assert_b0_and_not_b1 b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel assertB0AndNotB1.prog (wCons b0 (wCons b1 vNil)) = some (.cons () .nil) :=
  Reify.toDenote (assertB0AndNotB1.sound b0 b1) h

/-- A value of `assert_cfg.assert_not_b0_and_not_b1` is the denotation of its NF program. -/
theorem assertNotB0AndNotB1_denote (b0 b1 : Bool) (h : assert_cfg.assert_not_b0_and_not_b1 b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel assertNotB0AndNotB1.prog (wCons b0 (wCons b1 vNil)) = some (.cons () .nil) :=
  Reify.toDenote (assertNotB0AndNotB1.sound b0 b1) h

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
