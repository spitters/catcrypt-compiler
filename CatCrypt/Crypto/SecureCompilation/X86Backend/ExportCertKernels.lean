/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit

@[expose] public section

set_option autoImplicit false

/-!
# The export certificate on the word-only `mpn` loops

`MpnLoopFrontEmit.binLprog` is the physical-ABI export of the front-compiled runtime-count
loop `binProg op` (`binLprog_eq`). `ExportCertLoop.comLCertB` accepts that loop at the export
names of `binLprog` for the limb operations of `mpn_and_n`, `mpn_xor_n` and `mpn_ior_n`. The
loop of `mpn_add_n` carries its carry in a scalar accumulator and writes the out array as an
invariant (`MpnLoopFrontEmit.addRtProgOpt`); the check covers array accumulators only and
refuses it.

## Main definitions

* `binProg` — the front-compiled loop `binLprog` exports.
* `binLprog_eq` — `binLprog` is the physical-ABI export of `binProg`.
* `binCert` — the check on `binProg` at the export names of `binLprog`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertKernels

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop (rolledForLoopNRt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop (comLCertB)
open CatCrypt.Crypto.Jasmin.LowCT (SExpr)

/-- The front-compiled runtime-count loop of the binary limb operation `op`, with the
    arguments `binLprog` passes. -/
def binProg (op : SExpr → SExpr → SExpr) :=
  rolledForLoopNRt (Γouter := ΓouterBin) (accCTy := .memref N)
    (invCTys := [.memref N, .memref N])
    vmBin "out" (binBody op)
    (count := .here)
    (init := .there (.there (.there .here)))
    (invs := .cons (.there (.there .here)) (.cons (.there .here) .nil))

/-- `binLprog` is the physical-ABI export of `binProg`. -/
theorem binLprog_eq (name : String) (op : SExpr → SExpr → SExpr) :
    binLprog name op = (binProg op).map (fun c =>
      ComL.toLprogPhysAbi c name (argName 0) [argName 1, argName 2] (fun _ => none)
        (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]) := rfl

/-- The export check on `binProg op` at the names `binLprog` exports it under. -/
def binCert (op : SExpr → SExpr → SExpr) : Bool :=
  match binProg op with
  | some c => comLCertB c (argName 0) [argName 1, argName 2] ["RDI", "RSI", "RDX", "RCX"]
  | none => false

/-! ## Kernels -/

-- `mpn_and_n`, `mpn_xor_n`, `mpn_ior_n` (the limb operation of `iorLprog`)
#kat binCert .SAnd
#kat binCert .SXor
#kat binCert (fun x y => .SXor (.SXor x y) (.SAnd x y))

-- `mpn_add_n`: scalar carry accumulator, refused
#kat (addRtProgOpt ()).map (fun c => comLCertB c (argName 0) [] ["RDI", "RSI", "RDX", "RCX"])
  == some false

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertKernels
