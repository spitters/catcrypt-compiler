/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

@[expose] public section

set_option autoImplicit false

/-!
# The runtime-length shift, compare and multiply kernels as verified-encoder ELF objects

The `catcrypt-mpn` crate links three runtime-length kernels beyond the
`MpnLoopBytesEmit` five: the funnel shift `mpn_shift_rt`
(`MpnShiftFrontEmit.shiftRtLprogOpt`), the constant-time compare `mpn_cmp_ct`
(`MpnCmpFrontEmit.cmpRtLprogOpt`), and the schoolbook product
`mpn_mul_basecase_rt` (`MpnMulBasecaseFrontEmit.bcRtLprogOpt`). This module
byte-encodes each front `Lprog` with `LprogBytes.encodeLprogChecked` into a
single-symbol ELF64 relocatable object.

The encoded program is the front's `ComL.toLprogPhysAbi` output with no
optimization pass, the program the modules' denotation and machine-tie theorems
describe. The `.s` files under `bench/mpn_*_front_compare/gen_com/` are the
`renderOwned` rendering of the same program after the optimization pipeline, a
different instruction sequence with the same symbol.

The `#guard`s check that each front compiled its source and that every body
instruction is in the encoder's fragment, so `objBytes` returns `some`; they
evaluate three encoder runs over short programs and pin the artifact against
a front or encoder change that would leave the crate without an object.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRuntimeBytesEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-- The gated object bytes of a front-compiled `Lprog`: `none` when the front
    declined the source or a body instruction is outside the encoder fragment. -/
def objBytes (p : Option Lprog) : Option (List (BitVec 8)) :=
  p.bind encodeLprogChecked

/-- The three kernels, keyed by the object name `crates/catcrypt-mpn/build.rs`
    archives; each object defines the symbol named by its `Lprog`. -/
def kernels : List (String × Option Lprog) :=
  [ ("mpn_shift_rt_owned", MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt")
  , ("mpn_cmp_ct_owned", MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct")
  , ("mpn_mul_basecase_rt_owned", MpnMulBasecaseFrontEmit.bcRtLprogOpt "mpn_mul_basecase_rt") ]

#guard (objBytes (MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt")).isSome
#guard (objBytes (MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct")).isSome
#guard (objBytes (MpnMulBasecaseFrontEmit.bcRtLprogOpt "mpn_mul_basecase_rt")).isSome

/-- Byte list to `ByteArray`, for `IO.FS.writeBinFile`. -/
def toByteArray (bs : List (BitVec 8)) : ByteArray :=
  ⟨(bs.map (fun b => UInt8.ofNat b.toNat)).toArray⟩

/-- Write the three objects as `<dir>/<name>.o`. Fails rather than writing a
    truncated object when a kernel is outside the encoder fragment. -/
def emitTo (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for (name, p) in kernels do
    match objBytes p with
    | some bs => IO.FS.writeBinFile (dir / s!"{name}.o") (toByteArray bs)
    | none => throw (IO.userError s!"{name}: front declined or body outside the byte-encoder fragment")

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRuntimeBytesEmit
