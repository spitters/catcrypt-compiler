/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
public import CatCrypt.Crypto.SecureCompilation.VIR.AllocOut

/-!
# Definedness of the region allocation and the dead-write half of its post-pass

`regionLprog` is defined exactly when the region export `exportR` is: after the export it
refuses nothing. The dead-write elimination `deadWriteRet` of the post-pass `regionPostFuse`
keeps a sublist of each body, so it preserves the operand form `AllocOut I` of an allocated
program.

## Main statements

* `regionLprog_isSome_iff_exportR`: `regionLprog` is defined iff `exportR` is.
* `deadWriteRet_subset`: every instruction of `deadWriteRet body` is an instruction of `body`.
* `allocOut_mapBodies_deadWriteRet`: `deadWriteRet` on every body preserves `AllocOut I`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (AllocOut AllocOutInstr)

/-- **The region allocation refuses nothing after the export**: `regionLprog` is defined
    exactly when the region export `exportR` of the program is. -/
theorem regionLprog_isSome_iff_exportR (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (callee : Option CalleeTab)
    (ex : List String) :
    (regionLprog a p callee ex).isSome = (exportR Γ.length a.fname p Γ.length 0).isSome := by
  unfold regionLprog regionLprogC regionAllocC exportRLfundef
  cases exportR Γ.length a.fname p Γ.length 0 <;> rfl

/-- Every instruction of `deadWriteRet body` is an instruction of `body`. -/
theorem deadWriteRet_subset (body : Lcmd) : ∀ i ∈ deadWriteRet body, i ∈ body := by
  intro i hi
  unfold deadWriteRet at hi
  split at hi
  · next r hr =>
    split at hi
    · rcases List.mem_append.mp hi with h | h
      · exact List.dropLast_subset _
          ((X86Backend.OwnedLprogTV.dropDeadWriteBody_sublist _).subset h)
      · rw [List.mem_singleton.mp h]
        exact List.mem_of_getLast? hr
    · exact hi
  · exact hi

/-- **The dead-write elimination preserves the allocated operand form**: `deadWriteRet` on
    every function body keeps `AllocOut I`. -/
theorem allocOut_mapBodies_deadWriteRet (I : LprogIsa.IsaData) (P : Lprog)
    (h : AllocOut I P) : AllocOut I (X86Backend.LprogOptPipeline.mapBodies deadWriteRet P) := by
  intro f hf i hi
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact h g hg i (deadWriteRet_subset _ i hi)

end CatCrypt.Crypto.SecureCompilation.Haxc
