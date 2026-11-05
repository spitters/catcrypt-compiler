/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalf
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFFront
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalf
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.NFFront
public import CatCryptCore.Tactics.KatGuard

@[expose] public section

set_option autoImplicit false

/-!
# The field product at the bytes

The straight-line limb program of the field product over word arrays
(`fieldCom P (FieldRoute.mulProg P.p)`), presented to the region back half
`RegionBackend.compileRegion` as the program `NFProg.ofCom` with one result, under the
layout `FieldRoute.fieldAbi2 n`: for every result of `compileRegion`, from every machine
state whose operand arrays at `%rdx` and `%rsi` hold the Montgomery limbs of `x` and `y`,
the decoded bytes halt in a state from which the layout reads back an array of `n` words
whose limbs are the Montgomery limbs of `x * y`.

## Main results

* `field_correct_bytes`: the composed theorem for every modulus record `P : LimbParams n`.
* `fieldTestP1`, `fieldAbiNames`: a one-limb modulus record (`p = 2^64 - 59`) and the export
  names of `fieldAbi2 n` without loop arguments.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldBytes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams enc)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (fieldCom arrLimbs)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- **The field product at the bytes.** For a result `(P', bytes)` of `compileRegion` on the
    limb program of the field product at the modulus record `P` (`NFProg.ofCom`), under the
    layout `fieldAbi2 n`: from every machine state `sa` satisfying the layout's regions,
    whose arrays at `%rdx` and `%rsi` hold the Montgomery limbs of `x` and `y`, the bytes
    decode to a program that halts in a state from which the layout reads back the words of
    an array whose limbs are the Montgomery limbs of `x * y`. -/
theorem field_correct_bytes {n : Nat} (P : LimbParams n) (hn : n < 2 ^ 64) (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 n) a (NFProg.ofCom (fieldCom P (mulProg P.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 n).Regions sa) (x y : ZMod P.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") n) n 0 = enc P x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") n) n 0 = enc P y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin n → BitVec 64, (fieldAbi2 n).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr n 0 = enc P (x * y) := by
  obtain ⟨prog, sa', hd, hh, hr, -⟩ :=
    compileRegion_correct_wide h sa (abiVal2 n P.p sa) (abiValOf_fieldAbi2 n P.p sa) hreg 0
      (NFProg.denote_ofCom _ 0 _) rfl
  refine ⟨prog, sa', hd, hh, (fieldCom P (mulProg P.p)).denote (abiVal2 n P.p sa), hr, ?_⟩
  have hm := fieldMul_denote P hn sa x y hx hy
  rwa [RouteProg.denote_straight] at hm

/-! ## A one-limb modulus record and export names -/

/-- The one-limb modulus record `p = 2^64 - 59`, `nInv = -p⁻¹ mod 2^64`. -/
def fieldTestP1 : LimbParams 1 where
  p := 2 ^ 64 - 59
  nInv := 0xcbeea4e1a08ad8f3
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The export names of the layout `fieldAbi2 n` under the symbol `field_mul`. -/
def fieldAbiNames (n : Nat) : AbiNames where
  fname := "field_mul"
  outArg := ""
  inArgs := []
  abiArgs := (fieldAbi2 n).args.map fun a => exportReg a.reg

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldBytes
