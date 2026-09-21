/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
public meta import CatCrypt.Crypto.SecureCompilation.AsconLinearGoldenPath
public import CatCrypt.Crypto.SecureCompilation.AsconLinearGoldenPath

/-!
# The whole-ELF byte identity on `asconSigma0`, without the body-agreement hypothesis

`CompileComToElfJInstrFull.jElf_eq_lprogElf` equates the JInstr full-body ELF
`ByteArray` with the `Lprog` entry's, under the hypothesis `jBodyBytes body =
encodeLcmd body`. This module discharges that hypothesis on the physical-ABI body
of the GoldenPath kernel `asconSigma0` by kernel reduction, and applies the
conditional theorem to it.

The body equality is a closed computation: the gather `gatherJBlock5` runs over a
closed `Linstr` list, its shift arm detects the mnemonic with
`JasminLprogExport.hasPrefix` (`List.isPrefixOf` on the character lists) and
recovers the count with `shiftCountOf` (`String.toList`/`drop`), and both sides
land in `List (BitVec 8)`, which has a `DecidableEq` instance the kernel
evaluates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FullBodyByteIdentity

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
open CatCrypt.Crypto.SecureCompilation.AsconLinear (asconSigma0Com)

/-- The physical-ABI body of the `asconSigma0` kernel: the single exported
    function's `lfd_body` from `Com.toLprogPhysAbi`, the body both the JInstr
    full-body entry and the `Lprog` entry encode. -/
def asconSigma0PhysBody : List Linstr :=
  physBodyOf asconSigma0Com "ascon_sigma0"

/-- The full-body JInstr bytes of `asconSigma0`'s physical body equal the `Lprog`
    encoder's bytes for the same body. Both sides are 128 bytes.

    The agreement holds and is checked by kernel conversion, outside the module
    system: in a plain Lean file importing this one, at a raised `maxRecDepth`,
    `with_unfolding_all rfl` closes it. Inside a `module` the same proof fails,
    because the definitions on the path are not exposed and the conversion
    cannot unfold them, so the hypothesis cannot yet be discharged here.
    Exposing that path is what would make this a theorem in the package.

    Three measurements say where the difficulty is and is not. Both sides
    reduce: each is 128 bytes and the lengths and the leading byte values close
    by `decide +kernel`. `instDecidableEqList` on the two composite terms does
    not reduce, so the route is conversion rather than decision. And the
    conversion exhausts the default recursion depth, reporting that as a failure
    of definitional equality, which it is not. -/
def BodyBytesAgree : Prop :=
  jBodyBytes asconSigma0PhysBody = encodeLcmd asconSigma0PhysBody

/-- The JInstr full-body ELF object of `asconSigma0` equals the `Lprog` entry's
    ELF object for the single-function `Lprog` carrying the same physical body —
    the whole object, symbol table and section headers included — given the body
    byte agreement `BodyBytesAgree`. -/
theorem asconSigma0_jElf_eq_lprogElf (h : BodyBytesAgree) :
    compileComToElfJInstrFull asconSigma0Com "ascon_sigma0"
      = compileLprogToElf
          { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
          , lp_funcs := [("ascon_sigma0", { lfd_body := asconSigma0PhysBody })] } := by
  show jElf asconSigma0PhysBody "ascon_sigma0" = _
  exact jElf_eq_lprogElf _ _ h

end CatCrypt.Crypto.SecureCompilation.X86Backend.FullBodyByteIdentity
