/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteProg
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegions
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVDeadImm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRegW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

@[expose] public section

set_option autoImplicit false

/-!
# The printed program and the body the encoder reads

Definitions of the region back half `RegionBackend.compileRegion` of the hax compiler and of
the drivers that print and measure its output: the printed program and the body the encoder
reads.

## Main definitions

* `firstBody` — the body of the first function of an `Lprog`.
* `printedLprog`, `firstBody_printedLprog` — the printed program, the owned back end
  followed by the reload of spilled compare operands, and its first function body.
* `bodyTiedOk_cmpReload` — the reload of spilled compare operands keeps the two-address
  precondition.
* `bodyTiedOk_printedLprog_of_legalizes` — the first body of the printed program satisfies
  the printer's two-address precondition when every instruction the legaliser receives
  satisfies it or is rewritten.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The body of the first function of an `Lprog`: the body the encoder reads. -/
def firstBody (p : Lprog) : Option Lcmd := p.lp_funcs.head?.map (·.2.lfd_body)

/-- **The printed program of the back half** at the instruction-set data `I` (by default
    `TwoAddrLegalize.x86Data`): the owned back end `LprogOptPipeline.ownedLprog` at `I`
    followed by the pass `CmpSpillReload.cmpReload` at the register file of `I` on every
    function body, under which a compare whose first operand is a spill slot reads that
    operand from the reload scratch. The pass is the identity on a body the gated encoder
    accepts (`CmpSpillEncodable.cmpReload_of_checked`). -/
def printedLprog (p : Lprog)
    (I : LprogIsa.IsaData := X86Backend.TwoAddrLegalize.x86Data) : Lprog :=
  X86Backend.LprogOptPipeline.mapBodies (fun b => X86Backend.CmpSpillReload.cmpReload b I.toIsaAbi)
    (X86Backend.LprogOptPipeline.ownedLprog p I)

/-- The first function body of a program with a pass applied to every body is the pass on
    the first function body. -/
theorem firstBody_mapBodies (f : Lcmd → Lcmd) (P : Lprog) :
    firstBody (X86Backend.LprogOptPipeline.mapBodies f P) = (firstBody P).map f := by
  simp only [firstBody, X86Backend.LprogOptPipeline.mapBodies, List.head?_map, Option.map_map]
  rfl

/-- The first function body of the printed program is the pass `cmpReload` on the first
    function body of the owned back end. -/
theorem firstBody_printedLprog {p : Lprog} {I : LprogIsa.IsaData} {b : Lcmd}
    (h : firstBody (printedLprog p I) = some b) :
    ∃ b0, firstBody (X86Backend.LprogOptPipeline.ownedLprog p I) = some b0
      ∧ b = X86Backend.CmpSpillReload.cmpReload b0 I.toIsaAbi := by
  rw [printedLprog, firstBody_mapBodies] at h
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b0, hb0, rfl⟩

/-- An instruction of the reload `cmpReloadI` of an instruction that satisfies the printer's
    two-address precondition at `I` satisfies it: the copy has one source and the compare
    has its destination as its first source. -/
theorem tiedOk_of_mem_cmpReloadI {i j : Linstr} {abi : LprogIsa.IsaAbi} {I : LprogIsa.IsaData}
    (hi : X86Backend.TwoAddrLegalize.tiedOk i.li_i I = true)
    (hj : j ∈ X86Backend.CmpSpillReload.cmpReloadI i abi) :
    X86Backend.TwoAddrLegalize.tiedOk j.li_i I = true := by
  unfold X86Backend.CmpSpillReload.cmpReloadI at hj
  split at hj
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp [X86Backend.TwoAddrLegalize.tiedOk]
  · rcases List.mem_singleton.mp hj with rfl
    exact hi

/-- **The reload of spilled compare operands keeps the two-address precondition**, at every
    register file `abi` and instruction-set data `I`. -/
theorem bodyTiedOk_cmpReload {b : Lcmd} {abi : LprogIsa.IsaAbi} {I : LprogIsa.IsaData}
    (h : X86Backend.TwoAddrLegalize.bodyTiedOk b I = true) :
    X86Backend.TwoAddrLegalize.bodyTiedOk (X86Backend.CmpSpillReload.cmpReload b abi) I = true := by
  simp only [X86Backend.TwoAddrLegalize.bodyTiedOk, List.all_eq_true,
    X86Backend.CmpSpillReload.cmpReload, List.mem_flatMap] at h ⊢
  rintro j ⟨i, hi, hj⟩
  exact tiedOk_of_mem_cmpReloadI (h i hi) hj

/-- **The first body of the printed program at `I` satisfies the printer's two-address
    precondition** `TwoAddrLegalize.bodyTiedOk` when every instruction of the first body that
    `TwoAddrLegalize.twoAddrBody` receives in `LprogOptPipeline.ownedLprog` satisfies the
    precondition or is rewritten by `TwoAddrLegalize.legalizeInstr` at the scratch flag of
    that body. -/
theorem bodyTiedOk_printedLprog_of_legalizes {P : Lprog} {I : LprogIsa.IsaData} {b : Lcmd}
    (h : firstBody (printedLprog P I) = some b)
    (hleg : ∀ b0, firstBody (X86Backend.LprogGpRealloc.reallocLprog
        (X86Backend.ConstIndexFold.foldIndexedLprog
          (X86Backend.LprogOptPipeline.optimizeLprogBasicBlocks P))) = some b0 →
      ∀ i ∈ b0, X86Backend.TwoAddrLegalize.tiedOk i.li_i I = true ∨
        X86Backend.TwoAddrLegalize.legalizeInstr
          (X86Backend.TwoAddrLegalize.bodyAvoids b0 I) i I ≠ [i]) :
    X86Backend.TwoAddrLegalize.bodyTiedOk b I = true := by
  obtain ⟨b1, hb1, rfl⟩ := firstBody_printedLprog h
  rw [X86Backend.LprogOptPipeline.ownedLprog, firstBody_mapBodies] at hb1
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb1
  exact bodyTiedOk_cmpReload
    (X86Backend.TwoAddrLegalize.bodyTiedOk_twoAddrBody b0 I (hleg b0 hb0))

end CatCrypt.Crypto.SecureCompilation.Haxc
