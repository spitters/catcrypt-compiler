/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestAssertCfg

/-!
# The guards of the Aeneas test `assert_cfg` read by `reifyAeneas%`

The functions of the Aeneas test output `assert_cfg` (`TestAssertCfg`, copied unchanged from
Aeneas commit `b08bf81`) assert a condition with `massert` and continue with the unit
function `f`. `reifyAeneas%` reads every assertion by the one lemma `Reify.assert` (an instance
of `Reify.guardS`), its condition by the class `ReadCond`:

* the six comparisons `<`, `≤`, `>`, `≥`, `=`, `!=` of a `u32` word with a literal, the literal
  bound first (`Reify.letLit`), each by `readCmp` at its entry of `CmpProp`;
* the comparison of the checked sum of two words with a literal (`assert_arith`);
* the connective `b0 || b1` of two Boolean arguments (`readBool`), the assertions of `b0` and
  of `b1` in turn (`readBit`), and of their negations (`readNotBit`); a Boolean argument is
  the word `boolW b` of the layout, whose bit is bound first (`Reify.argBit`).

Each definition below is the output of the elaborator, with its soundness statement proved by
construction; each theorem is its composition with `Reify.toDenote`, the denotation in the
compiler's semantics.

## Main results

* `assertLt_denote`, `assertLe_denote`, `assertGt_denote`, `assertGe_denote`,
  `assertEq_denote`, `assertNe_denote` — the comparisons with a literal.
* `assertArith_denote` — a comparison of a computed word.
* `assertOr_denote`, `assertAnd_denote`, `assertNotOr_denote` — Boolean conditions.
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

/-- `assert_cfg.assert_lt` read as an NF program. -/
def assertLt := reifyAeneas% assert_cfg.assert_lt

/-- `assert_cfg.assert_le` read as an NF program. -/
def assertLe := reifyAeneas% assert_cfg.assert_le

/-- `assert_cfg.assert_gt` read as an NF program. -/
def assertGt := reifyAeneas% assert_cfg.assert_gt

/-- `assert_cfg.assert_ge` read as an NF program. -/
def assertGe := reifyAeneas% assert_cfg.assert_ge

/-- `assert_cfg.assert_eq` read as an NF program. -/
def assertEq := reifyAeneas% assert_cfg.assert_eq

/-- `assert_cfg.assert_ne` read as an NF program. -/
def assertNe := reifyAeneas% assert_cfg.assert_ne

/-- `assert_cfg.assert_arith` read as an NF program. -/
def assertArith := reifyAeneas% assert_cfg.assert_arith

/-- `assert_cfg.assert_or` read as an NF program. -/
def assertOr := reifyAeneas% assert_cfg.assert_or

/-- `assert_cfg.assert_and` read as an NF program. -/
def assertAnd := reifyAeneas% assert_cfg.assert_and

/-- `assert_cfg.assert_not_or` read as an NF program. -/
def assertNotOr := reifyAeneas% assert_cfg.assert_not_or

/-- A value of `assert_cfg.assert_lt` is the denotation of its NF program. -/
theorem assertLt_denote (x : U32) (h : assert_cfg.assert_lt x = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertLt.prog (vCons x vNil) =
      some (.cons () .nil) :=
  Reify.toDenote (assertLt.sound x) h

/-- A value of `assert_cfg.assert_le` is the denotation of its NF program. -/
theorem assertLe_denote (x : U32) (h : assert_cfg.assert_le x = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertLe.prog (vCons x vNil) =
      some (.cons () .nil) :=
  Reify.toDenote (assertLe.sound x) h

/-- A value of `assert_cfg.assert_gt` is the denotation of its NF program. -/
theorem assertGt_denote (x : U32) (h : assert_cfg.assert_gt x = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertGt.prog (vCons x vNil) =
      some (.cons () .nil) :=
  Reify.toDenote (assertGt.sound x) h

/-- A value of `assert_cfg.assert_ge` is the denotation of its NF program. -/
theorem assertGe_denote (x : U32) (h : assert_cfg.assert_ge x = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertGe.prog (vCons x vNil) =
      some (.cons () .nil) :=
  Reify.toDenote (assertGe.sound x) h

/-- A value of `assert_cfg.assert_eq` is the denotation of its NF program. -/
theorem assertEq_denote (x : U32) (h : assert_cfg.assert_eq x = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertEq.prog (vCons x vNil) =
      some (.cons () .nil) :=
  Reify.toDenote (assertEq.sound x) h

/-- A value of `assert_cfg.assert_ne` is the denotation of its NF program. -/
theorem assertNe_denote (x : U32) (h : assert_cfg.assert_ne x = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertNe.prog (vCons x vNil) =
      some (.cons () .nil) :=
  Reify.toDenote (assertNe.sound x) h

/-- A value of `assert_cfg.assert_arith` is the denotation of its NF program. -/
theorem assertArith_denote (x y : U32) (h : assert_cfg.assert_arith x y = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertArith.prog (vCons x (vCons y vNil)) =
      some (.cons () .nil) :=
  Reify.toDenote (assertArith.sound x y) h

/-- A value of `assert_cfg.assert_or` is the denotation of its NF program. -/
theorem assertOr_denote (b0 b1 : Bool) (h : assert_cfg.assert_or b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertOr.prog (wCons b0 (wCons b1 vNil)) =
      some (.cons () .nil) :=
  Reify.toDenote (assertOr.sound b0 b1) h

/-- A value of `assert_cfg.assert_and` is the denotation of its NF program. -/
theorem assertAnd_denote (b0 b1 : Bool) (h : assert_cfg.assert_and b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel assertAnd.prog (wCons b0 (wCons b1 vNil)) =
      some (.cons () .nil) :=
  Reify.toDenote (assertAnd.sound b0 b1) h

/-- A value of `assert_cfg.assert_not_or` is the denotation of its NF program. -/
theorem assertNotOr_denote (b0 b1 : Bool) (h : assert_cfg.assert_not_or b0 b1 = .ok ()) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel assertNotOr.prog (wCons b0 (wCons b1 vNil)) = some (.cons () .nil) :=
  Reify.toDenote (assertNotOr.sound b0 b1) h

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
