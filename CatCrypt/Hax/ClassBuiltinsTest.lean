/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.ReifyImp
public import CatCrypt.Hax.ClassBuiltins
public import CatCrypt.Hax.TExprTypingCore

/-!
# A class-generic literal over a two-method class

A class `TwoOps` with a binary method `op` and a unary method `neg`, a definition
`opNeg x y = op (neg x) y` generic in the instance, and its `ImpExpr` literal calling the
methods by name. The methods of an instance form the builtin table `twoOpsBi`; the
ascent generator proves that the literal computes `opNeg` at every instance, and the
checker types the typed literal at the type parameter `F` and at every instantiation.

## Main results

* `opNeg_fnCorres` — the literal of `opNeg` denotes it at every instance with an
  injective, plain encoding
* `opNeg_texpr_hasType` — the typed literal has type `F` under the method signatures
* `opNeg_texpr_instTypes_hasType` — its instance at a type environment `σ` has type
  `σ F`, and it erases to the untyped literal
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.ClassBuiltinsTest

open _root_.Hax _root_.Hax.Ascent
open CatCrypt.Hax.ClassBuiltins CatCrypt.Hax.TExprTyping

/-- A class with a binary method `op` and a unary method `neg`. -/
class TwoOps (F : Type) where
  /-- The binary method. -/
  op : F → F → F
  /-- The unary method. -/
  neg : F → F

/-- The generic definition `op (neg x) y`. -/
def opNeg {F : Type} [TwoOps F] (x y : F) : F :=
  TwoOps.op (TwoOps.neg x) y

/-- The literal of `opNeg`: the parameters bound and the methods called by name. -/
def opNeg_impExpr : ImpExpr :=
  .letBind "x" (.var "x") (.letBind "y" (.var "y")
    (.app "op" [.app "neg" [.var "x"], .var "y"]))

/-- The typed literal of `opNeg` over the type parameter `F`. -/
def opNeg_texpr : TExpr :=
  let tF : ImpType := .typeVar "F"
  .mk (.letBind "x" (.mk (.var "x") tF) (.mk (.letBind "y" (.mk (.var "y") tF)
    (.mk (.app "op" [.mk (.app "neg" [.mk (.var "x") tF]) tF, .mk (.var "y") tF]) tF)) tF))
    tF

theorem opNeg_texpr_erase : opNeg_texpr.erase = opNeg_impExpr := rfl

variable (F : Type) [TwoOps F] [HaxEnc F] [HaxEnc.Inj F]

/-- The methods of a `TwoOps` instance as a table, each under the name the literal calls
    it by. -/
noncomputable def twoOpsTable : Table :=
  [("op", leaf2 (TwoOps.op : F → F → F)), ("neg", leaf1 (TwoOps.neg : F → F))]

/-- The builtin table of a `TwoOps` instance under an encoding of its carrier. -/
noncomputable def twoOpsBi : Builtins := Table.toBuiltins (twoOpsTable F)

variable {F}

theorem twoOpsBi_op (x y : F) :
    twoOpsBi F "op" [enc x, enc y] = some (enc (TwoOps.op x y)) := by
  rw [twoOpsBi, Table.toBuiltins_of_lookup rfl, leaf2_apply]

theorem twoOpsBi_neg (x : F) : twoOpsBi F "neg" [enc x] = some (enc (TwoOps.neg x)) := by
  rw [twoOpsBi, Table.toBuiltins_of_lookup rfl, leaf1_apply]

/-- From the entry environment binding `x` and `y`, the literal `opNeg_impExpr` returns
    the encoding of `opNeg` at the instance `F`. -/
theorem opNeg_fnCorres [HaxEnc.Plain F] :
    FnCorres (twoOpsBi F) opNeg_impExpr (A := F × F × Unit)
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1)]) (fun _ => True)
      (fun a => opNeg a.1 a.2.1) := by
  ascend_reified (opNeg (F := F)) using [twoOpsBi_op, twoOpsBi_neg]

/-- The signatures of the methods of `TwoOps` over the type parameter `F`. -/
def twoOpsSig : Sig
  | "op" => some ([.typeVar "F", .typeVar "F"], .typeVar "F")
  | "neg" => some ([.typeVar "F"], .typeVar "F")
  | _ => none

/-- The parameter environment of `opNeg`. -/
def xyEnv : TyEnv
  | "x" | "y" => some (.typeVar "F")
  | _ => none

theorem opNeg_texpr_check : check twoOpsSig xyEnv opNeg_texpr = some (.typeVar "F") := by
  rfl

/-- The typed literal of `opNeg` has type `F` under the method signatures. -/
theorem opNeg_texpr_hasType : HasType twoOpsSig xyEnv opNeg_texpr (.typeVar "F") :=
  check_sound twoOpsSig xyEnv _ _ opNeg_texpr_check

/-- At every type environment `σ`, the instantiated typed literal of `opNeg` has the
    instantiated type and erases to `opNeg_impExpr`. -/
theorem opNeg_texpr_instTypes_hasType (σ : String → Option ImpType) :
    HasType (twoOpsSig.subst σ) (xyEnv.subst σ) (TExpr.instTypes σ opNeg_texpr)
        (ImpType.substVars σ (.typeVar "F")) ∧
      (TExpr.instTypes σ opNeg_texpr).erase = opNeg_impExpr :=
  ⟨opNeg_texpr_hasType.instTypes σ, by rw [TExpr.erase_instTypes]; rfl⟩

end CatCrypt.Hax.ClassBuiltinsTest
