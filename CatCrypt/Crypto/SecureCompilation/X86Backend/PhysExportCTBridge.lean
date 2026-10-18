/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CFGatherBridge
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CFGatherBridge

/-!
# The speculative statements on the ABI-wrapped physical export

`CFGatherBridge.parseLcmdCF_backEdgeFrame` pins the recogniser's parse of the
raw exporter frame `backEdgeFrame pre top region cc`. The shipped body is the
register-allocated, ABI-wrapped one `ComL.toLfundefPhysAbi` builds: the raw
frame is wrapped in a red-zone prologue, the SysV argument materialization, the
callee-saved restore epilogue and a terminal `Lret`.

This module carries the parse across that wrapping.

## The frame with a continuation

`backEdgeFrameTail pre top region cc post` is `backEdgeFrame pre top region cc`
with a continuation `post` after the back-edge.
`parseLcmdCF_backEdgeFrameTail` gives its parse,
`.seq (.straight pre) (.seq (.loop n (.straight region)) (.straight post))`.

The shape is closed under the three operations the ABI wrapping performs:
appending a straight-line prefix on the left (the prologue and the argument
materialization), appending a suffix on the right (the epilogue), and
`insertEpilogue`'s `dropLast`/re-append of the terminal `Lret`.

## The wrapped body

`physAbiLoopBody` is the body `ComL.toLfundefPhysAbi` emits
(`ComL_toLfundefPhysAbi_eq_physAbiLoopBody`), in the shape
`LoopExporterCTBridge.physAbiLoopWrap_lcmdDirect` states its addressing result
over (`physAbiLoopBody_lcmdDirect`).
`physAbiLoopBody_branchFree` recognises it to a conditional-free block
whenever the register-allocated body it wraps is a back-edge frame followed by
the terminal `Lret`, and `physAbiLoopBody_cfSpec_state_independent` /
`physAbiLoopBody_cfSpec_mem_addr_in_program` are the two speculative statements
on the recognised block.

The predictor hypothesis of the leakage-equality statement is
`CFGatherBridge.noPub`-drivenness, which `CFGatherBridge.pubDriven_noPub_iff`
reads as "the predictor's decision does not read the machine state". It is not
removable: `SpeculativeCTControlFlow.secretDrivenPredictor_leaks` separates two
states with a secret-reading predictor on a block that is both `CFControlled`
and index-free.

## Scope

The frame shape of the register-allocated body — that
`(physBodyWithStores …).filter` of a virtual back-edge frame is again a
back-edge frame — is a hypothesis here, `hra`. Two conditions decide it. The
per-instruction expansion carries a `Llabel` and a `Lcond` to themselves and an
`Lopn` to a run of `Lopn`s, so the label, the back-edge and the straight-line
runs keep their places; and `loopFrameOk` survives only when the trip counter is
allocated to a register. A spilled counter's decrement `SUB ctr,#1` goes through
`JasminLprogExport.legalizeBinop`'s spill route `MOV R15,ctr ; SUB R15,#1 ;
MOV ctr,R15`, whose subtraction names `R15` rather than the counter the seed
declares, and `loopFrameOk`'s `isCounterDec` demand then fails.

## Register allocation and the addressing class

A spill slot is a `reg` operand whose name begins `k.`
(`JasminLprogExport.LOperand.isSpill`), not an `arrIdx`, and every operand the
allocator and the spill legalizers write is a `reg`, an `imm`, or the rewritten
base/index of an `arrIdx` that was already one
(`AllocCTPreservation.remapOperand_isIndexed`,
`AllocCTPreservation.legalizeSibElem_of_direct`,
`AllocCTPreservation.reloadMemrefBase_of_direct`). So the allocation and spill
passes carry `isIndexed` to `isIndexed`, which is
`AllocCTPreservation.physBodyWithStores_lcmdDirect`, and the index-free premise
of the speculative statements survives register allocation:
`LoopExporterCTBridge.ComL_toLfundefPhysAbi_lcmdDirect` states it for the
deployed looped export.

## Witnesses

`loopSmokeAbiBody` is the shipped body of the deployed counted-loop smoke
program through `ComL.toLfundefPhysAbi`. The `#guard`s of §6 exhibit its
decomposition into a prologue, a register-allocated back-edge frame and the
epilogue, and check each hypothesis of the theorems above on it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysExportCTBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdToOwnedCF
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (OwnedCF MLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow
  (CFPredictor PubDriven SLeak cfSpecExec CFAllDirect cfAddrs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (lcmdDirect lcmdDirect_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CFGatherBridge

/-! ## 1. Straight-line runs -/

/-- A straight-line run holds no return. -/
theorem straight_filter_isLret {c : Lcmd} (h : ∀ i ∈ c, isStraightL i = true) :
    c.filter (fun i => !isLret i) = c :=
  List.filter_eq_self.mpr fun i hi => by simp [isLret_of_isStraightL (h i hi)]

/-- A straight-line run is its own `takeWhile`. -/
theorem takeWhile_all {c : Lcmd} (h : ∀ i ∈ c, isStraightL i = true) :
    c.takeWhile isStraightL = c := by
  have := takeWhile_append_of_all (p := isStraightL) (a := c) (b := []) h
  simpa using this

/-- A straight-line run drops to nothing. -/
theorem dropWhile_all {c : Lcmd} (h : ∀ i ∈ c, isStraightL i = true) :
    c.dropWhile isStraightL = [] := by
  have := dropWhile_append_of_all (p := isStraightL) (a := c) (b := []) h
  simpa using this

/-- The parse of a straight-line run is the single leaf holding it. -/
theorem parseLcmdCF_straight {c : Lcmd} {fuel : Nat} (hfuel : 0 < fuel)
    (h : ∀ i ∈ c, isStraightL i = true) :
    parseLcmdCF fuel c = some (.straight c) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp only [parseLcmdCF, dropWhile_all h, takeWhile_all h]

/-- The red-zone save prologue is straight-line. -/
theorem buildPrologue_straight (virt : Lfundef) (tbl : Array Nat) (m : InLoadMap) :
    ∀ i ∈ buildPrologue virt tbl m, isStraightL i = true := by
  intro i hi
  simp only [buildPrologue, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The callee-saved restore epilogue is straight-line. -/
theorem calleeSaveRestoreEpilogue_straight :
    ∀ i ∈ calleeSaveRestoreEpilogue, isStraightL i = true := by
  intro i hi
  simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The SysV argument materialization is straight-line. -/
theorem buildArgPtrMaterialize_straight (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (m : InLoadMap) :
    ∀ i ∈ buildArgPtrMaterialize virt tbl abiArgs m, isStraightL i = true := by
  intro i hi
  rw [buildArgPtrMaterialize, List.mem_flatMap] at hi
  obtain ⟨⟨abiReg, j⟩, -, hmem⟩ := hi
  dsimp only at hmem
  repeat' split at hmem
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  all_goals (rcases hmem with rfl | rfl) <;> rfl

/-- The saves of a list of argument registers to their save slots, which a multi-input
    prologue appends, are straight-line. -/
theorem extraInputSaves_straight (regs : List String) :
    ∀ i ∈ regs.filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none), isStraightL i = true := by
  intro i hi
  rw [List.mem_filterMap] at hi
  obtain ⟨a, -, ha⟩ := hi
  split at ha <;> simp only [Option.some.injEq, reduceCtorEq] at ha
  subst ha
  rfl

/-! ## 2. The back-edge frame with a continuation -/

/-- A bottom-tested back-edge frame followed by a continuation: a straight-line
    prefix whose last instruction seeds the counter, the loop label, the loop
    region ending in the counter test, the conditional back-edge, and the
    continuation `post`. -/
def backEdgeFrameTail (pre : Lcmd) (top : LLabel) (region : Lcmd) (cc : String)
    (post : Lcmd) : Lcmd :=
  pre ++ (⟨0, .Llabel .internal top⟩ ::
    (region ++ (⟨0, .Lcond (.reg cc) top⟩ :: post)))

/-- With an empty continuation the shape is the raw exporter frame. -/
theorem backEdgeFrameTail_nil (pre : Lcmd) (top : LLabel) (region : Lcmd)
    (cc : String) :
    backEdgeFrameTail pre top region cc [] = backEdgeFrame pre top region cc := by
  simp [backEdgeFrameTail, backEdgeFrame]

/-- **A back-edge frame with a straight-line continuation parses.** The prefix is
    a straight-line leaf, the region between the label and the back-edge is the
    body of a counted loop whose trip count is the immediate the prefix's last
    instruction seeds the counter with, and the continuation is a straight-line
    leaf. -/
theorem parseLcmdCF_backEdgeFrameTail {pre region post : Lcmd} {top : LLabel}
    {cc ctr : String} {n fuel : Nat} (hfuel : 2 ≤ fuel)
    (hpre : ∀ i ∈ pre, isStraightL i = true)
    (hseed : pre.getLast?.bind counterSeed? = some (ctr, n)) (hn : 0 < n)
    (hregion : ∀ i ∈ region, isStraightL i = true)
    (hok : loopFrameOk ctr region = true) (hcc : isCondCode cc = true)
    (hpost : ∀ i ∈ post, isStraightL i = true) :
    parseLcmdCF fuel (backEdgeFrameTail pre top region cc post)
      = some (.seq (.straight pre)
          (.seq (.loop n (.straight region)) (.straight post))) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
  have hlbl : isStraightL (⟨0, .Llabel .internal top⟩ : Linstr) = false := rfl
  have hdrop : (backEdgeFrameTail pre top region cc post).dropWhile isStraightL
      = ⟨0, .Llabel .internal top⟩ ::
        (region ++ (⟨0, .Lcond (.reg cc) top⟩ :: post)) := by
    rw [backEdgeFrameTail, dropWhile_append_of_all hpre]
    simp [hlbl]
  have htake : (backEdgeFrameTail pre top region cc post).takeWhile isStraightL
      = pre := by
    rw [backEdgeFrameTail, takeWhile_append_of_all hpre]
    simp [hlbl]
  have hnbe : ∀ i ∈ region, (!isBackEdge top i) = true := fun i hi => by
    simp [isBackEdge_of_isStraightL (hregion i hi)]
  have hbe : isBackEdge top (⟨0, .Lcond (.reg cc) top⟩ : Linstr) = true := by
    simp [isBackEdge, hcc]
  have hdrop2 : (region ++ ((⟨0, .Lcond (.reg cc) top⟩ : Linstr) :: post)).dropWhile
      (fun j => !isBackEdge top j) = (⟨0, .Lcond (.reg cc) top⟩ : Linstr) :: post := by
    rw [dropWhile_append_of_all hnbe]
    simp [hbe]
  have htake2 : (region ++ ((⟨0, .Lcond (.reg cc) top⟩ : Linstr) :: post)).takeWhile
      (fun j => !isBackEdge top j) = region := by
    rw [takeWhile_append_of_all hnbe]
    simp [hbe]
  have hps : parseLcmdCF (f + 1) post = some (.straight post) :=
    parseLcmdCF_straight (Nat.succ_pos f) hpost
  rw [parseLcmdCF]
  simp only [hdrop, htake, hdrop2, htake2, hseed, hps, if_pos hn, if_pos hok,
    Option.map_some]

/-- Filtering the returns out of a back-edge frame with a straight-line prefix
    and region filters only its continuation. -/
theorem backEdgeFrameTail_filter_isLret {pre region post : Lcmd} {top : LLabel}
    {cc : String} (hpre : ∀ i ∈ pre, isStraightL i = true)
    (hregion : ∀ i ∈ region, isStraightL i = true) :
    (backEdgeFrameTail pre top region cc post).filter (fun i => !isLret i)
      = backEdgeFrameTail pre top region cc (post.filter (fun i => !isLret i)) := by
  rw [backEdgeFrameTail, backEdgeFrameTail, List.filter_append,
    straight_filter_isLret hpre, List.filter_cons_of_pos (by rfl),
    List.filter_append, straight_filter_isLret hregion,
    List.filter_cons_of_pos (by rfl)]

theorem backEdgeFrameTail_length (pre region post : Lcmd) (top : LLabel)
    (cc : String) : 2 ≤ (backEdgeFrameTail pre top region cc post).length + 1 := by
  rw [backEdgeFrameTail]
  simp only [List.length_append, List.length_cons]
  omega

/-- **A back-edge frame whose continuation is straight-line up to the returns
    recognises to a conditional-free block.** -/
theorem lcmdToOwnedCF_backEdgeFrameTail_branchFree {pre region post : Lcmd}
    {top : LLabel} {cc ctr : String} {n : Nat}
    (hpre : ∀ i ∈ pre, isStraightL i = true)
    (hseed : pre.getLast?.bind counterSeed? = some (ctr, n)) (hn : 0 < n)
    (hregion : ∀ i ∈ region, isStraightL i = true)
    (hok : loopFrameOk ctr region = true) (hcc : isCondCode cc = true)
    (hpost : ∀ i ∈ post.filter (fun i => !isLret i), isStraightL i = true)
    {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (backEdgeFrameTail pre top region cc post) = some cf) :
    CFBranchFree cf := by
  rw [lcmdToOwnedCF, backEdgeFrameTail_filter_isLret hpre hregion,
    parseLcmdCF_backEdgeFrameTail (backEdgeFrameTail_length pre region post top cc)
      hpre hseed hn hregion hok hcc hpost] at hrec
  rw [Option.bind] at hrec
  refine lcmdCFToOwnedCF_branchFree _ cf ?_ hrec
  exact ⟨trivial, trivial, trivial⟩

/-! ## 3. The shape is closed under the ABI wrapping -/

/-- A prefix on the left extends the frame's prefix. -/
theorem append_backEdgeFrameTail (prol pre region post : Lcmd) (top : LLabel)
    (cc : String) :
    prol ++ backEdgeFrameTail pre top region cc post
      = backEdgeFrameTail (prol ++ pre) top region cc post := by
  simp [backEdgeFrameTail, List.append_assoc]

/-- A suffix on the right extends the frame's continuation. -/
theorem backEdgeFrameTail_append (pre region post suf : Lcmd) (top : LLabel)
    (cc : String) :
    backEdgeFrameTail pre top region cc post ++ suf
      = backEdgeFrameTail pre top region cc (post ++ suf) := by
  simp [backEdgeFrameTail, List.append_assoc]

/-- Dropping the last instruction of a frame with a non-empty continuation drops
    it from the continuation. -/
theorem backEdgeFrameTail_dropLast (pre region post : Lcmd) (top : LLabel)
    (cc : String) (h : post ≠ []) :
    (backEdgeFrameTail pre top region cc post).dropLast
      = backEdgeFrameTail pre top region cc post.dropLast := by
  rw [backEdgeFrameTail, backEdgeFrameTail,
    List.dropLast_append_of_ne_nil (by simp),
    List.dropLast_cons_of_ne_nil (by simp),
    List.dropLast_append_of_ne_nil (by simp),
    List.dropLast_cons_of_ne_nil h]

/-- A prefix on the left does not disturb the counter seed. -/
theorem getLast?_append_of_ne_nil {pre : Lcmd} (prol : Lcmd) (h : pre ≠ []) :
    (prol ++ pre).getLast? = pre.getLast? := by
  rcases hh : pre.getLast? with _ | x
  · exact absurd (List.getLast?_eq_none_iff.mp hh) h
  · simp [List.getLast?_append, hh]

/-! ## 4. The ABI-wrapped register-allocated body -/

/-- The body `ComL.toLfundefPhysAbi` emits: the red-zone prologue, the extra
    pointer-argument saves, the SysV argument materialization, and the
    register-allocated body with the callee-saved restore epilogue inserted
    before its terminal return. Stated in the shape
    `LoopExporterCTBridge.physAbiLoopWrap_lcmdDirect` gives the addressing result
    over. -/
def physAbiLoopBody (virt : Lfundef) (tbl : Array Nat) (abiArgs : List String)
    (extra raBody : Lcmd) : Lcmd :=
  buildPrologue virt tbl (fun _ => none) ++ extra
    ++ buildArgPtrMaterialize virt tbl abiArgs (fun _ => none)
    ++ insertEpilogue raBody calleeSaveRestoreEpilogue

/-- The wrapped body of a register-allocated back-edge frame is a back-edge
    frame: the prologue and the argument materialization extend the prefix, and
    the callee-saved restore epilogue with the terminal return is the
    continuation. -/
theorem physAbiLoopBody_eq_backEdgeFrameTail {virt : Lfundef} {tbl : Array Nat}
    {abiArgs : List String} {extra raBody pre region : Lcmd} {top : LLabel}
    {cc : String}
    (hra : raBody = backEdgeFrameTail pre top region cc [⟨0, .Lret⟩]) :
    physAbiLoopBody virt tbl abiArgs extra raBody
      = backEdgeFrameTail
          (buildPrologue virt tbl (fun _ => none) ++ extra
            ++ buildArgPtrMaterialize virt tbl abiArgs (fun _ => none) ++ pre)
          top region cc (calleeSaveRestoreEpilogue ++ [⟨0, .Lret⟩]) := by
  rw [physAbiLoopBody, insertEpilogue, hra,
    backEdgeFrameTail_dropLast _ _ _ _ _ (by simp)]
  simp [backEdgeFrameTail, List.append_assoc]

/-- **The shipped body of a register-allocated back-edge frame recognises to a
    conditional-free block.** The prologue and the SysV argument materialization
    are straight-line and end before the counter seed, the register-allocated
    frame is unchanged, and the callee-saved restore epilogue is a straight-line
    continuation after the back-edge — so the recogniser's parse of the wrapped
    body is the parse of the frame with a longer prefix and a trailing leaf. -/
theorem physAbiLoopBody_branchFree {virt : Lfundef} {tbl : Array Nat}
    {abiArgs : List String} {extra raBody pre region : Lcmd} {top : LLabel}
    {cc ctr : String} {n : Nat}
    (hextra : ∀ i ∈ extra, isStraightL i = true)
    (hra : raBody = backEdgeFrameTail pre top region cc [⟨0, .Lret⟩])
    (hpre : ∀ i ∈ pre, isStraightL i = true) (hpreNe : pre ≠ [])
    (hseed : pre.getLast?.bind counterSeed? = some (ctr, n)) (hn : 0 < n)
    (hregion : ∀ i ∈ region, isStraightL i = true)
    (hok : loopFrameOk ctr region = true) (hcc : isCondCode cc = true)
    {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (physAbiLoopBody virt tbl abiArgs extra raBody)
      = some cf) : CFBranchFree cf := by
  rw [physAbiLoopBody_eq_backEdgeFrameTail hra] at hrec
  refine lcmdToOwnedCF_backEdgeFrameTail_branchFree (ctr := ctr) (n := n)
    ?_ ?_ hn hregion hok hcc ?_ hrec
  · intro i hi
    rcases List.mem_append.mp hi with h | h
    · rcases List.mem_append.mp h with h' | h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact buildPrologue_straight _ _ _ i h''
        · exact hextra i h''
      · exact buildArgPtrMaterialize_straight _ _ _ _ i h'
    · exact hpre i h
  · rw [getLast?_append_of_ne_nil _ hpreNe]; exact hseed
  · intro i hi
    rw [List.filter_append,
      show ([(⟨0, .Lret⟩ : Linstr)]).filter (fun i => !isLret i) = [] from rfl,
      List.append_nil,
      straight_filter_isLret calleeSaveRestoreEpilogue_straight] at hi
    exact calleeSaveRestoreEpilogue_straight i hi

/-- The deployed looped export's body is an instance of `physAbiLoopBody`: the
    prologue with the extra pointer-argument saves, the SysV argument
    materialization, and the register-allocated body with the callee-saved
    restore epilogue. -/
theorem ComL_toLfundefPhysAbi_eq_physAbiLoopBody {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : ComL Γ t) (outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap) (abiArgs : List String)
    (abiTyin : List Nat) :
    ∃ (virt : Lfundef) (tbl : Array Nat) (extra raBody : Lcmd),
      (ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs
        abiTyin).lfd_body = physAbiLoopBody virt tbl abiArgs extra raBody :=
  ⟨_, _, _, _, rfl⟩

/-- The addressing class of the wrapped body, from
    `LoopExporterCTBridge.physAbiLoopWrap_lcmdDirect`: when the virtual body uses
    no register-indexed operand, neither does the register-allocated, ABI-wrapped
    one. -/
theorem physAbiLoopBody_lcmdDirect (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (extra : Lcmd) (shiftImm : ShiftImmOracle)
    (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (p : Linstr → Bool)
    (hextra : lcmdDirect extra = true) (hv : lcmdDirect virt.lfd_body = true) :
    lcmdDirect (physAbiLoopBody virt tbl abiArgs extra
      ((physBodyWithStores shiftImm virt.lfd_body (fun _ => none) reloadScratch2 []
          reloadScratch2 0 memrefBaseReload callArgBaseReload).filter p)) = true :=
  LoopExporterCTBridge.physAbiLoopWrap_lcmdDirect virt tbl abiArgs extra shiftImm
    memrefBaseReload callArgBaseReload p hextra hv

/-! ## 5. The two speculative statements on the shipped body -/

/-- **Branch-misprediction (Spectre-v1) leakage-equality for the shipped
    body.** The block the recogniser returns for the ABI-wrapped,
    register-allocated export of a back-edge frame has the same speculative
    leakage trace from any two machine states, under a state-blind branch
    predictor and for every speculation window.

    The predictor hypothesis is `PubDriven noPub P`, which
    `CFGatherBridge.pubDriven_noPub_iff` reads as: the predictor's decision does
    not depend on the machine state.
    `SpeculativeCTControlFlow.secretDrivenPredictor_leaks` shows it is not
    removable. -/
theorem physAbiLoopBody_cfSpec_state_independent {virt : Lfundef} {tbl : Array Nat}
    {abiArgs : List String} {extra raBody pre region : Lcmd} {top : LLabel}
    {cc ctr : String} {n : Nat}
    (hextra : ∀ i ∈ extra, isStraightL i = true)
    (hra : raBody = backEdgeFrameTail pre top region cc [⟨0, .Lret⟩])
    (hpre : ∀ i ∈ pre, isStraightL i = true) (hpreNe : pre ≠ [])
    (hseed : pre.getLast?.bind counterSeed? = some (ctr, n)) (hn : 0 < n)
    (hregion : ∀ i ∈ region, isStraightL i = true)
    (hok : loopFrameOk ctr region = true) (hcc : isCondCode cc = true)
    (hd : lcmdDirect (physAbiLoopBody virt tbl abiArgs extra raBody) = true)
    {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (physAbiLoopBody virt tbl abiArgs extra raBody) = some cf)
    (window : Nat) {P : CFPredictor 64} (hP : PubDriven noPub P)
    (s₁ s₂ : JState 64) :
    (cfSpecExec window P s₁ cf).1 = (cfSpecExec window P s₂ cf).1 :=
  cfSpecExec_state_independent window hP cf (lcmdToOwnedCF_cfAllDirect hd hrec)
    (physAbiLoopBody_branchFree hextra hra hpre hpreNe hseed hn hregion hok hcc hrec)
    s₁ s₂

/-- **Predictor-free (Spectre-v1) containment for the shipped body.** Every
    memory event of the speculative trace of the recognised block — transient
    events across the back-edge included — names an address that occurs in the
    block's program text, for every branch predictor, every window and every
    state. -/
theorem physAbiLoopBody_cfSpec_mem_addr_in_program {virt : Lfundef}
    {tbl : Array Nat} {abiArgs : List String} {extra raBody : Lcmd}
    (hd : lcmdDirect (physAbiLoopBody virt tbl abiArgs extra raBody) = true)
    {cf : OwnedCF 64}
    (hrec : lcmdToOwnedCF (physAbiLoopBody virt tbl abiArgs extra raBody) = some cf)
    (window : Nat) (P : CFPredictor 64) (s : JState 64) (base : String) (off : Int)
    (hmem : SLeak.arch (MLeak.mem base off) ∈ (cfSpecExec window P s cf).1) :
    MLeak.mem base off ∈ cfAddrs cf :=
  SpeculativeCTControlFlow.cfSpecExec_mem_addr_in_program window P cf
    (lcmdToOwnedCF_cfAllDirect hd hrec) s base off hmem

/-! ## 6. The shipped body of the deployed counted loop

`JasminLprogExport.loopSmokeProg` is the deployed counted-loop smoke program.
`loopSmokeAbiBody` is its body through the looped 2-pointer ABI export — the
register-allocated, prologue/epilogue-wrapped command that is assembled and
shipped, not the raw exporter frame.

The instruction texts of two commands agree iff each pair of positions renders
the same; the shape checks below compare them at that level. -/

/-- The shipped body of the deployed counted-loop smoke program. -/
def loopSmokeAbiBody : Lcmd :=
  (ComL.toLfundefPhysAbi loopSmokeProg "a1" []).lfd_body

/-- The rendered instruction texts of a command. -/
def lcmdText (c : Lcmd) : List String := c.map (fun i => i.li_i.toText)

/-- The straight-line prefix of the shipped body: the red-zone prologue, the
    SysV argument materialization, the accumulator seed and the counter seed. -/
def smokePre : Lcmd := loopSmokeAbiBody.take 12

/-- The loop region of the shipped body: the two-address doubling, the
    accumulator feedback, the counter decrement and the counter test. -/
def smokeRegion : Lcmd := (loopSmokeAbiBody.drop 13).take 5

/-- The continuation of the shipped body after the back-edge: the callee-saved
    restore epilogue and the terminal return. -/
def smokePost : Lcmd := loopSmokeAbiBody.drop 19

/-- The register-allocated body the ABI wrapping wraps: the accumulator and
    counter seeds, the loop frame, and the terminal return. -/
def smokeRaBody : Lcmd :=
  backEdgeFrameTail (smokePre.drop 10) 1 smokeRegion "NZ" [⟨0, .Lret⟩]

-- The shipped body has the back-edge-frame-with-continuation shape.
#guard lcmdText loopSmokeAbiBody
  == lcmdText (backEdgeFrameTail smokePre 1 smokeRegion "NZ" smokePost)

-- The shipped body is the ABI wrapping of `smokeRaBody`.
#guard lcmdText loopSmokeAbiBody
  == lcmdText (loopSmokeAbiBody.take 10
        ++ insertEpilogue smokeRaBody calleeSaveRestoreEpilogue)

-- `hpre`, `hpreNe`, `hseed`, `hn` of `physAbiLoopBody_branchFree`, on the
-- register-allocated frame's own prefix (the accumulator and counter seeds).
#guard (smokePre.drop 10).all isStraightL
#guard !(smokePre.drop 10).isEmpty
#guard (smokePre.drop 10).getLast?.bind counterSeed? == some ("RBX", 4)

-- `hregion`, `hok` and `hcc`: the region is a loop body for the counter `RBX`
-- the seed names, and the back-edge names a condition code.
#guard smokeRegion.all isStraightL
#guard loopFrameOk "RBX" smokeRegion
#guard isCondCode "NZ"

-- The whole prefix of the wrapped body, prologue and argument materialization
-- included, is straight-line and still ends at the counter seed.
#guard smokePre.all isStraightL
#guard smokePre.getLast?.bind counterSeed? == some ("RBX", 4)

-- The continuation is the callee-saved restore epilogue and the return, which
-- is straight-line once the return is filtered out.
#guard lcmdText smokePost == lcmdText (calleeSaveRestoreEpilogue ++ [⟨0, .Lret⟩])
#guard (smokePost.filter (fun i => !isLret i)).all isStraightL

-- `hrec` and `hd`: the recogniser accepts the shipped body, and no operand of
-- it is register-indexed — so the two speculative statements above apply to it.
#guard (lcmdToOwnedCF loopSmokeAbiBody).isSome
#guard lcmdDirect loopSmokeAbiBody

-- The recognised block holds exactly one counted loop, of the program's trip
-- count.
#guard (parseLcmdCF (loopSmokeAbiBody.length + 1)
  (loopSmokeAbiBody.filter (fun i => !isLret i))).map LcmdCF.loopCounts == some [4]

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysExportCTBridge
