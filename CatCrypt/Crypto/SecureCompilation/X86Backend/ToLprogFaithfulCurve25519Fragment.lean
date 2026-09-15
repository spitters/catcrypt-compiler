/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulMulCarrySel
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519

/-!
# The Curve25519 limb expressions against the physical faithfulness fragment

`Algebraic/FieldLimbs/Curve25519.lean` builds its add, sub, neg, mul, sqr, const
and copy blocks from seven expression constructors: `eConst` (`regConst 64`),
`eBit` (`regConst 1`), `eBin` (`regArith bop 64`), `eMulhi` (`mulhi 64`), `eAdc`
(`addCarryLo 64`), `eCarry` (`addCarryHi 64`) and `eSel` (`select 64`). This
module places each of them against `ToLprogFaithfulMulCarrySel.UniformRegArithMCS`,
the `Com` fragment of the whole-function physical faithfulness theorems
`toLprogPhysAbi_faithful_uniformMCS` and its two-pointer and epilogue instances.

Six of the seven are inside the fragment: a `Com` binding `eConst`, `eBit`,
`eMulhi`, `eAdc`, `eCarry` or `eSel` on top of a fragment body is again in the
fragment. `eSel` is the conditional correction of every Curve25519 block — the
conditional subtraction of `p = 2^255 - 19` in `csubK`, the fold of the carry by
`38` in `reduceK`, and the limb-wise `selR` — and it is in the fragment through
`SelectBinding` and the `CMOV` arm of `JasminLsem.applyOpn`.

`eBin op` is outside: the fragment's binary `regArith` arm carries the side
condition `w ≠ 64`, which the blocks' width 64 does not meet. The condition comes
from `ToLprogFaithfulCover.regArithHead_realizes`, whose `InstrRealizesBinding`
obligation requires the head mnemonic to carry no `:64` width tag, while
`withWidthTag 64 (binOpName bop)` carries it
(`hasSuffix_withWidthTag_64_binOpName`); at width 64 the two-address expansion of
`physBodyElem` injects the `MOV:64` legalization move rather than the untagged
`MOV` of `BinopBinding.block`.

Two shape conditions of the whole-function theorems are also unmet by the blocks
as written. The blocks are `MultiReturnCom jasminDialect Γ [reg 64, reg 64,
reg 64, reg 64]`, returning four limb variables, while `UniformRegArithMCS` and
the cover data are stated over the single-return `Com`. And `CoverDataMCS` is
indexed by one word width `w` for the whole binding list, while the blocks bind
`regConst 1` (`eBit`, the carry-chain's zero carry-in) beside their width-64
bindings.

## Main results

* `uniformRegArithMCS_eConst`, `uniformRegArithMCS_eBit`,
  `uniformRegArithMCS_eMulhi`, `uniformRegArithMCS_eAdc`,
  `uniformRegArithMCS_eCarry`, `uniformRegArithMCS_eSel`: the six constructors
  inside the fragment.
* `hasSuffix_withWidthTag_64_binOpName`: the width-64 binop mnemonic carries the
  `:64` tag that the binop cover arm excludes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCurve25519Fragment

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulMulCarrySel
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519

/-! ## 1. The six constructors inside the fragment -/

/-- A `regConst 64` limb constant (`eConst`) keeps a `Com` in the fragment. -/
theorem uniformRegArithMCS_eConst {Γ : Ctxt jasminDialect} {s : JasminTy} (n : Nat)
    (body : Com jasminDialect (w64 :: Γ) s) (hbody : UniformRegArithMCS body) :
    UniformRegArithMCS (Com.var (eConst (Γ := Γ) n) body) := by
  show UniformRegArithMCS
    (Com.var ⟨JasminOp.regConst 64 n, rfl, .nil⟩ body)
  exact .const rfl body hbody

/-- A `regConst 1` carry constant (`eBit`) keeps a `Com` in the fragment. -/
theorem uniformRegArithMCS_eBit {Γ : Ctxt jasminDialect} {s : JasminTy} (n : Nat)
    (body : Com jasminDialect (w1 :: Γ) s) (hbody : UniformRegArithMCS body) :
    UniformRegArithMCS (Com.var (eBit (Γ := Γ) n) body) := by
  show UniformRegArithMCS
    (Com.var ⟨JasminOp.regConst 1 n, rfl, .nil⟩ body)
  exact .const rfl body hbody

/-- A `mulhi 64` product high word (`eMulhi`) keeps a `Com` in the fragment. -/
theorem uniformRegArithMCS_eMulhi {Γ : Ctxt jasminDialect} {s : JasminTy}
    (a b : Ctxt.Var Γ w64) (body : Com jasminDialect (w64 :: Γ) s)
    (hbody : UniformRegArithMCS body) :
    UniformRegArithMCS (Com.var (eMulhi a b) body) := by
  show UniformRegArithMCS
    (Com.var ⟨JasminOp.mulhi 64, rfl, .cons a (.cons b .nil)⟩ body)
  exact .mulhi rfl a b body hbody

/-- An `addCarryLo 64` carry-chain data word (`eAdc`) keeps a `Com` in the
    fragment. -/
theorem uniformRegArithMCS_eAdc {Γ : Ctxt jasminDialect} {s : JasminTy}
    (a b : Ctxt.Var Γ w64) (c : Ctxt.Var Γ w1)
    (body : Com jasminDialect (w64 :: Γ) s) (hbody : UniformRegArithMCS body) :
    UniformRegArithMCS (Com.var (eAdc a b c) body) := by
  show UniformRegArithMCS
    (Com.var ⟨JasminOp.addCarryLo 64, rfl, .cons a (.cons b (.cons c .nil))⟩ body)
  exact .addCarryLo rfl a b c body hbody

/-- An `addCarryHi 64` carry-out bit (`eCarry`) keeps a `Com` in the fragment. -/
theorem uniformRegArithMCS_eCarry {Γ : Ctxt jasminDialect} {s : JasminTy}
    (a b : Ctxt.Var Γ w64) (c : Ctxt.Var Γ w1)
    (body : Com jasminDialect (w1 :: Γ) s) (hbody : UniformRegArithMCS body) :
    UniformRegArithMCS (Com.var (eCarry a b c) body) := by
  show UniformRegArithMCS
    (Com.var ⟨JasminOp.addCarryHi 64, rfl, .cons a (.cons b (.cons c .nil))⟩ body)
  exact .addCarryHi rfl a b c body hbody

/-- A `select 64` conditional correction (`eSel`) keeps a `Com` in the fragment.
    This is the conditional subtraction and the carry fold of every Curve25519
    block. -/
theorem uniformRegArithMCS_eSel {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Ctxt.Var Γ w1) (a b : Ctxt.Var Γ w64)
    (body : Com jasminDialect (w64 :: Γ) s) (hbody : UniformRegArithMCS body) :
    UniformRegArithMCS (Com.var (eSel c a b) body) := by
  show UniformRegArithMCS
    (Com.var ⟨JasminOp.select 64, rfl, .cons c (.cons a (.cons b .nil))⟩ body)
  exact .select rfl c a b body hbody

/-! ## 2. The width-64 binop mnemonic carries the `:64` tag -/

/-- At width 64 `withWidthTag` appends the `:64` tag. -/
theorem withWidthTag_64_eq (mnem : String) :
    withWidthTag 64 mnem = mnem ++ ":64" := by
  simp [withWidthTag]

/-- The mnemonic a width-64 `regArith bop` head carries ends with the `:64` width
    tag. `InstrRealizesBinding` requires the opposite, which is the side condition
    `w ≠ 64` on the fragment's binary `regArith` arm. -/
theorem hasSuffix_withWidthTag_64_binOpName (bop : JasminBinOp) :
    hasSuffix (withWidthTag 64 (binOpName bop)) ":64" = true := by
  rw [withWidthTag_64_eq]
  cases bop <;> decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCurve25519Fragment
