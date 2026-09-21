/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import Std.Data.String.ToNat
import CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode

/-!
# Closed round trips of the logical loops

`LprogBytesDecode.and_n_roundtrip`, `xor_n_roundtrip` and `ior_n_roundtrip` take two
string facts as hypotheses: the frame size of the loop body is 64 and the count of the
tag `"SHL:0"` is 0. This module proves both and states the three round trips without
hypotheses.

`maxIdxL` is the spill-index scan with the prefix test over the character lists
(`WellFormedX86.isPrefixOf_eq_hasPrefix`), and `frameSize_of_noSpill` reads the frame
size of a body whose scans find no `k.N` and no `kv.N` name off it. The count of
`"SHL:0"` follows from the `Std` characterisation of `String.toNat?` by
`Nat.ofDigitChars`, applied through `LprogBytes.tagShiftCount_eq`.
-/

public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecodeClosed

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode

/-- The maximum index `N` over the register names `<pfx>N` of a body, with the prefix test
    `JasminLprogExport.hasPrefix` on character lists; `n` is the length of `pfx`. -/
def maxIdxL (pfx : String) (n : Nat) (body : Lcmd) : Option Nat :=
  body.foldl (fun acc i =>
    match i.li_i with
    | .Lopn dsts _ srcs =>
        (dsts ++ srcs).foldl (fun acc' o =>
          match o with
          | .reg nm =>
              if hasPrefix nm pfx then
                match String.toNat? (nm.drop n).toString with
                | some k => some (max (acc'.getD 0) k)
                | none => acc'
              else acc'
          | _ => acc') acc
    | _ => acc) none

theorem maxSpillIdx_eq (body : Lcmd) : maxSpillIdx body = maxIdxL "k." 2 body := by
  rw [maxSpillIdx_eq_toNat?]
  simp only [maxIdxL, WellFormedX86.isPrefixOf_eq_hasPrefix]
  rfl

theorem maxVecSpillIdx_eq (body : Lcmd) : maxVecSpillIdx body = maxIdxL "kv." 3 body := by
  rw [maxVecSpillIdx_eq_toNat?]
  simp only [maxIdxL, WellFormedX86.isPrefixOf_eq_hasPrefix]
  rfl

/-- The frame size of a body whose list-side spill scans find no `k.N` and no `kv.N`
    name, from the frame size computed with both scans at `none`. -/
theorem frameSize_of_noSpill (body : Lcmd) (F : Nat)
    (hk : maxIdxL "k." 2 body = none) (hkv : maxIdxL "kv." 3 body = none)
    (hF : (let frameAdd := frameAddDirective body
      let f16 :=
        match frameDirective body with
        | some f => (f + frameAdd + (qsaveBytesFor body - qsaveBytes) + 15) / 16 * 16
        | none => (qsaveBytesFor body + 0 + 0 + frameAdd + 15) / 16 * 16
      if bodyHasCall body
          && (8 + 8 * (calleeSavedToSave body).length + f16) % 16 != 0 then f16 + 8
      else f16) = F) :
    frameSize body = F := by
  rw [← hF]
  simp only [frameSize, vecSpillBytes, maxSpillIdx_eq, maxVecSpillIdx_eq, hk, hkv]
  rfl

/-- The count of the tag `"SHL:0"` is `0`. -/
theorem tagShiftCount_SHL0 : tagShiftCount "SHL:0" = 0 := by
  rw [tagShiftCount_eq]
  rw [show String.ofList (List.drop 4 "SHL:0".toList) = "0" by decide,
    String.toNat?_eq_some_ofDigitChars (String.isNat_of_isDigit (by decide) (by simp))]
  simp [Nat.ofDigitChars_cons, Nat.ofDigitChars_nil]

theorem frameSize_and :
    frameSize (binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64") = 64 :=
  frameSize_of_noSpill _ 64 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem frameSize_xor :
    frameSize (binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64") = 64 :=
  frameSize_of_noSpill _ 64 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem frameSize_ior :
    frameSize (binLoopBody (iorMid "SHL:0:64") "SHL:0:64") = 64 :=
  frameSize_of_noSpill _ 64 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`mpn_and_n_loop_owned`.** The function bytes the encoder lays down for the `and`
    loop decode to `binDecoded (andMidDecoded .and_)`. -/
theorem and_n_roundtrip_closed :
    decodeLprog (encodeLfundefBytes (binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64"))
      = some (binDecoded (andMidDecoded .and_)) :=
  and_n_roundtrip frameSize_and tagShiftCount_SHL0

/-- **`mpn_xor_n_loop_owned`.** As `and_n_roundtrip_closed`, at the `XOR:64` limb
    operation. -/
theorem xor_n_roundtrip_closed :
    decodeLprog (encodeLfundefBytes (binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64"))
      = some (binDecoded (andMidDecoded .xor_)) :=
  xor_n_roundtrip frameSize_xor tagShiftCount_SHL0

/-- **`mpn_ior_n_loop_owned`.** As `and_n_roundtrip_closed`, at the limb operation
    `iorMid`. -/
theorem ior_n_roundtrip_closed :
    decodeLprog (encodeLfundefBytes (binLoopBody (iorMid "SHL:0:64") "SHL:0:64"))
      = some (binDecoded iorMidDecoded) :=
  ior_n_roundtrip frameSize_ior tagShiftCount_SHL0

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecodeClosed
