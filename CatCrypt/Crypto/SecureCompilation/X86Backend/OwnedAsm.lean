/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Owned AT&T text of a lowered program

`ownedAsm name abiArgs j` renders a lowered `Com jasminDialect` as owned AT&T text
under the SysV pointer ABI: `Com.toLprogPhysAbi` with every argument register
listed in `abiArgs` taken as a 64-bit pointer, then `LprogOptPipeline.renderOwned`.
It carries no program of its own, so importing it costs nothing at start-up.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedAsm

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)

/-- Render an owned AT&T `.s` for a lowered program under the SysV pointer ABI. -/
def ownedAsm (name : String) (abiArgs : List String)
    (j : Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t)) :
    Option String :=
  j.map (fun s =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
      (Com.toLprogPhysAbi s.2.2 name
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := abiArgs) (abiTyin := abiArgs.map (fun _ => 64))
        (residence := none) (abiW := 0) (forceLivePin := true)))

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedAsm
