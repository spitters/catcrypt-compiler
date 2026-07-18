/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportKeccak
import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
import CatCrypt.Crypto.Optimizer.LoadCSE
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# PROBE: the resident Keccak variants re-routed through the owned Com→render path

Investigation probe (NOT a committed kernel). Demonstrates that the two resident
Keccak emits (`KeccakResidentBebOwnedEmit`, `KeccakResidentChiRowOwnedEmit`),
currently HAND-AUTHORED asm-string `flatMap`s, are expressible through the SAME
`KeccakEmit.keccakF1600Com → toLprogPhysAbi → (load-CSE) → renderLprogAtt`
pipeline that `KeccakLinearMain.lean` already uses for the plain owned `.s`:

* **Beb** is currently a degenerate plain-round emit (its own docstring), so its
  owned `.s` is the plain permutation under symbol `keccak_f1600_resident_beb` —
  the canonical `toLprogPhysAbi` path with the symbol name changed.

* **ChiRow** is a χ B-lane load-scheduling refinement; the *verified*
  `LoadCSE.loadCSELprog` pass (`KeccakLinearMain` already runs it) realizes the
  same "load each B lane once" reuse generically, value-identically
  (`loadCSEAux_pointwise`).

This file only type-checks the composition; it does not force-evaluate the
~6900-binding term (that needs the compiled `lean_exe`, per `KeccakLinearMain`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakResidentComRenderProbe

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (Com.toLprogPhysAbi keccakImmSlots keccakInLoadMap keccakOutStoreMap)
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit (keccakF1600Com)

/-- The plain owned Keccak `Lprog`, but under the resident-Beb symbol name. Since
    Beb's hand emit is the degenerate plain round, this Com-rendered Lprog is its
    value-identical replacement. -/
def bebLprog : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog :=
  Com.toLprogPhysAbi keccakF1600Com "keccak_f1600_resident_beb"
    (fun _ => none) keccakImmSlots keccakInLoadMap keccakOutStoreMap

/-- The ChiRow variant: the SAME Com-rendered Lprog under the ChiRow symbol, with
    the verified cross-register load-CSE pass applied — the generic, value-identical
    realization of the "load each row's five B lanes once" reuse. -/
def chiRowLprog : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog :=
  CatCrypt.Crypto.Optimizer.LoadCSE.loadCSELprog
    (Com.toLprogPhysAbi keccakF1600Com "keccak_f1600_resident_chirow"
      (fun _ => none) keccakImmSlots keccakInLoadMap keccakOutStoreMap)

/-- Render both to AT&T `.s` text through the owned printer — the same final step
    `KeccakLinearMain` uses for the plain kernel. -/
def bebAsm : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt bebLprog

def chiRowAsm : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt chiRowLprog

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakResidentComRenderProbe
