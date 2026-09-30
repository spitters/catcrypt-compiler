/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertKernels
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertKernels
public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront

@[expose] public section

set_option autoImplicit false

/-!
# The export gates on front-compiled kernels

`ExportCertGate.singleLoopB` accepts the front-compiled runtime-count loops of `mpn_and_n`,
`mpn_xor_n` and `mpn_ior_n` (`ExportCertKernels.binProg`) at the export names of
`MpnLoopFrontEmit.binLprog`: the updates are in `ArrMemN` with `ComExpOK` and the renaming
certificate holds. `ExportCertStraight.straightCertB` accepts the front-compiled SHA-2
`Maj` and `Ch` bodies of `ThirToComFront`: both are in `ScalarMemN`, and the virtual body
the physical-ABI export allocates is the liveness pin, the typed chain and the return.

## Main definitions

* `binGate` — the gate on `binProg` at the export names of `binLprog`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGateKernels

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (argName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertKernels (binProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate (singleLoopB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight (straightCertB)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (majCom chCom)
open CatCrypt.Crypto.Jasmin.LowCT (SExpr)

/-- The gate `singleLoopB` on `binProg op` at the names `binLprog` exports it under. -/
def binGate (op : SExpr → SExpr → SExpr) : Bool :=
  match binProg op with
  | some c => singleLoopB c (argName 0) [argName 1, argName 2] ["RDI", "RSI", "RDX", "RCX"]
  | none => false

-- `mpn_and_n`, `mpn_xor_n`, `mpn_ior_n`
#kat binGate .SAnd
#kat binGate .SXor
#kat binGate (fun x y => .SXor (.SXor x y) (.SAnd x y))

-- SHA-2 `Maj` and `Ch`, straight-line
#kat straightCertB majCom
#kat straightCertB chCom

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGateKernels
