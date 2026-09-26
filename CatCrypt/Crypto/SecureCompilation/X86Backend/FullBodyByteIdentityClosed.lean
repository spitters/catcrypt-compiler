/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.FullBodyByteIdentity

/-!
# The whole-body byte agreement on `asconSigma0`

`FullBodyByteIdentity.BodyBytesAgree` — the JInstr full-body encoder and the `Lprog`
encoder produce the same byte list on the physical-ABI body of the GoldenPath kernel
`asconSigma0` — and the whole-ELF byte identity that follows from it, with no
hypothesis.

The body equality is a closed computation on both sides, so the kernel evaluates the
decidable equality of the two byte lists. This file is not a `module`, so the bodies of
the encoders on the path are visible to that evaluation without exposing them to the
consumers of their own modules.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FullBodyByteIdentity

open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
open CatCrypt.Crypto.SecureCompilation.AsconLinear (asconSigma0Com)

/-- The full-body JInstr bytes of `asconSigma0`'s physical body equal the `Lprog`
    encoder's bytes for the same body. Both sides are the same 128-byte list; the
    kernel evaluates the decidable equality of the two lists. -/
theorem bodyBytesAgree : BodyBytesAgree := by
  show jBodyBytes asconSigma0PhysBody = encodeLcmd asconSigma0PhysBody
  decide +kernel

/-- The JInstr full-body ELF object of `asconSigma0` equals the `Lprog` entry's ELF
    object for the single-function `Lprog` carrying the same physical body — the whole
    object, symbol table and section headers included. -/
theorem asconSigma0_jElf_eq_lprogElf_closed :
    compileComToElfJInstrFull asconSigma0Com "ascon_sigma0"
      = compileLprogToElf
          { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
          , lp_funcs := [("ascon_sigma0", { lfd_body := asconSigma0PhysBody })] } :=
  asconSigma0_jElf_eq_lprogElf bodyBytesAgree

end CatCrypt.Crypto.SecureCompilation.X86Backend.FullBodyByteIdentity
