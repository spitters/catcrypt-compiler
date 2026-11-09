/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront
public import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLoweringJacobian
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLoweringJacobian

/-!
# Compiled bytes of the `X` coordinate of Jacobian addition over BabyBear

`jacAddXLean` is the first coordinate of the `add-2007-bl` addition `jacAddOps` of two
Jacobian triples over BabyBear, `p = 2013265921`, as a function of the six coordinates.
`reifyField%` reads it, with `jacAddOps` unfolded and the projection of the result tuple
reduced, as a literal over the six parameters, in which the coordinates `Y₃` and `Z₃` do
not occur.

## Main results

* `jacAddX_fnCorres` — the literal denotes `jacAddXLean` under `hax64WExit`.
* `jacAddX_bytes` — for every result of `compileA` on the typed literal under `addXAbi`,
  the decoded bytes compute `jacAddXLean` of the six argument registers. That `compileA`
  accepts the literal is measured outside Lean, by the executables' row harness.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect (jacAddOps)
open _root_.Hax (TExpr ImpExpr)
open _root_.Hax.Ascent (FnCorres enc bindParams)
open CatCrypt.Crypto.Hax (hax64WExit spineLamFree)
open CatCrypt.Hax.ReifyField (enc_zmod)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- The `X` coordinate of the Jacobian sum of `(x1, y1, z1)` and `(x2, y2, z2)` over
    BabyBear. -/
def jacAddXLean (x1 y1 z1 x2 y2 z2 : ZMod 2013265921) : ZMod 2013265921 :=
  (jacAddOps (x1, y1, z1) (x2, y2, z2)).1

/-- The literal of `jacAddXLean`, with `jacAddOps` unfolded. -/
def jacAddXImp : ImpExpr := reifyField% jacAddXLean unfolding jacAddOps

/-- The layout of `jacAddXLean`: the six scalar parameters in `%rdi`, `%rsi`, `%rdx`,
    `%rcx`, `%r8`, `%r9`, no constant, the scalar result in `%rax`, the frame of
    `compileA`. -/
def addXAbi : AbiLayout :=
  AbiLayout.mk [⟨"x1", "%rdi", .scalar⟩, ⟨"y1", "%rsi", .scalar⟩, ⟨"z1", "%rdx", .scalar⟩,
    ⟨"x2", "%rcx", .scalar⟩, ⟨"y2", "%r8", .scalar⟩, ⟨"z2", "%r9", .scalar⟩] []
    (.reg "%rax") [] (-256) (-8) [] []

/-- The types of the parameters of `addXAbi`: each a `u64` word. -/
def addXTypes : List (String × _root_.Hax.ImpType) :=
  addXAbi.args.map fun a => (a.name, .uint .w64)

theorem jacAddXImp_toTExpr_isSome : (jacAddXImp.toTExpr addXTypes).isSome = true := by
  rfl

/-- The typed literal of `jacAddXLean`, the six parameters typed as `u64` words. -/
def jacAddXT : TExpr := (jacAddXImp.toTExpr addXTypes).get jacAddXImp_toTExpr_isSome

/-- The erasure of `jacAddXT` is the literal `jacAddXImp`. -/
theorem jacAddXT_erase : jacAddXT.erase = jacAddXImp :=
  ImpExpr.erase_toTExpr (Option.some_get jacAddXImp_toTExpr_isSome).symm

/-- From the entry environment binding the six coordinates, the literal `jacAddXImp` returns
    the encoding of `jacAddXLean` under the table `hax64WExit`. -/
theorem jacAddX_fnCorres :
    FnCorres hax64WExit jacAddXImp
      (A := ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 ×
        ZMod 2013265921 × ZMod 2013265921 × Unit)
      (fun a => bindParams [("x1", enc a.1), ("y1", enc a.2.1), ("z1", enc a.2.2.1),
        ("x2", enc a.2.2.2.1), ("y2", enc a.2.2.2.2.1), ("z2", enc a.2.2.2.2.2.1)])
      (fun _ => True)
      (fun a => jacAddXLean a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1) := by
  ascend_reified jacAddXLean using [hax64WExit_babyBear_mul, hax64WExit_babyBear_add,
    hax64WExit_babyBear_sub]

theorem jacAddX_spineLamFree : spineLamFree jacAddXT.erase = true := by
  rw [jacAddXT_erase]; decide

/-- **The compiled bytes of `jacAddXLean`.** If `compileA` returns `(P, bytes)` on `jacAddXT`
    under `addXAbi`, then from every entry state whose registers `%rdi`, `%rsi`, `%rdx`,
    `%rcx`, `%r8`, `%r9` hold the canonical representatives of the six coordinates of `a`, the
    bytes decode to a program that halts in a state whose `%rax` reads back the encoding of
    `jacAddXLean` of `a`. -/
theorem jacAddX_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA jacAddXT addXAbi "jacAddX" = some (P, bytes)) (sa : AState)
    (a : ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 ×
      ZMod 2013265921 × ZMod 2013265921 × Unit)
    (h1 : a.1.val = (sa.regs "%rdi").toNat) (h2 : a.2.1.val = (sa.regs "%rsi").toNat)
    (h3 : a.2.2.1.val = (sa.regs "%rdx").toNat) (h4 : a.2.2.2.1.val = (sa.regs "%rcx").toNat)
    (h5 : a.2.2.2.2.1.val = (sa.regs "%r8").toNat)
    (h6 : a.2.2.2.2.2.1.val = (sa.regs "%r9").toNat) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ addXAbi.ResultOf sa sa'
        (enc (jacAddXLean a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1)) := by
  have hf := jacAddX_fnCorres
  rw [← jacAddXT_erase] at hf
  refine leanFront_correct_scalar jacAddXT addXAbi "jacAddX" _ _ hc
    jacAddX_spineLamFree _ _ _ hf (by simp [addXAbi]) rfl (by decide) sa ?_ a trivial ?_
  · have hr : addXAbi.regions = [] := rfl
    refine ⟨by simp [addXAbi], ?_, ?_,
      AbiLayout.stackIn_of_regCarriedB (by decide) sa⟩ <;> simp [hr]
  · simp [addXAbi, enc_zmod, h1, h2, h3, h4, h5, h6]

end CatCrypt.Crypto.SecureCompilation.Haxc
