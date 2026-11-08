/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFoldFuelMemF
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrFuelMemF

/-!
# The owned back end on the flag machine

`LprogOptPipeline.ownedLprog` composes four stages on every function body: the basic-block
optimiser `optimizeBasicBlocks`, the constant-index fold `ConstIndexFold.foldIndexedBody`, the
register re-allocation `LprogGpRealloc.reallocBody` and the two-address legalisation
`TwoAddrLegalize.twoAddrBody`. This module composes the theorems of the four stages on the
fuel-stepped flag machine `lsemFuelMemF` into one theorem on `ownedLprog`.

The machine takes no step at `Lret`, so a halting run of a function body is a run of the body
without its trailing return (`OwnedLprogTV.dropRet`); the re-allocation theorem is stated on
that form. The other three stages commute with appending a return to a body
(`optimizeBasicBlocks_append_ret`, `foldIndexedBody_append_ret`, `twoAddrBody_append_ret`), so
their theorems apply to the body without its return.

## Main results

* `optimizeBasicBlocks_append_ret`, `foldIndexedBody_append_ret`, `twoAddrBody_append_ret`,
  `reallocBody_append_ret`: each stage maps a body ending with `Lret` to a body ending with the
  same `Lret`.
* `ownedBody_lsemFuelMemF`: the four stages on one body ending with `Lret`.
* `ownedLprog_lsemFuelMemF`: the four stages on every function of a program whose body ends
  with `Lret`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (EqPc)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg (TagShape)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdFlags
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (typeBody dropRet TagFirstSrc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFoldFuelMemF
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL (CellRelF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrFuelMemF
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (isRecognizedOpn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.StackZeroize (endsWithLret dropLast_append_Lret)

/-! ## 1. The basic-block optimiser -/

theorem flagsLiveAux_append_ret (ii : Nat) :
    ∀ (c : Bool) (l : Lcmd), flagsLiveAux c (l ++ [⟨ii, .Lret⟩]) = flagsLiveAux c l := by
  intro c l
  induction l generalizing c with
  | nil => simp [flagsLiveAux, flagEffect]
  | cons i rest ih =>
      simp only [List.cons_append, flagsLiveAux]
      cases flagEffect i <;> simp [ih]

theorem splitStraightRunsAux_append_ret (ii : Nat) :
    ∀ (l cur : Lcmd), splitStraightRunsAux cur (l ++ [⟨ii, .Lret⟩])
      = splitStraightRunsAux cur l ++ [[⟨ii, .Lret⟩]] := by
  intro l
  induction l with
  | nil =>
      intro cur
      simp [splitStraightRunsAux, isCtlInstr, flushRun, flagsLive, flagsLiveAux, flagEffect]
  | cons i rest ih =>
      intro cur
      have hfl : flagsLive (i :: (rest ++ [⟨ii, .Lret⟩])) = flagsLive (i :: rest) :=
        flagsLiveAux_append_ret ii false (i :: rest)
      simp only [List.cons_append, splitStraightRunsAux, flushRun, flagHold, hfl, ih]
      grind

/-- The basic-block optimiser maps a body followed by `Lret` to the optimised body followed by
    the same `Lret`. -/
theorem optimizeBasicBlocks_append_ret (ii : Nat) (body : Lcmd) :
    optimizeBasicBlocks (body ++ [⟨ii, .Lret⟩]) = optimizeBasicBlocks body ++ [⟨ii, .Lret⟩] := by
  simp [optimizeBasicBlocks, splitStraightRuns, splitStraightRunsAux_append_ret,
    bodyIsStraightLine]

/-! ## 2. The constant-index fold -/

theorem frameDirective_append_ret (ii : Nat) (body : Lcmd) :
    frameDirective (body ++ [⟨ii, .Lret⟩]) = frameDirective body := by
  rw [frameDirective, frameDirective, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  generalize List.foldl _ none body = a
  cases a <;> rfl

/-- The frame parameters of a body do not change when `Lret` is appended to it. -/
theorem bodyParams_append_ret (ii : Nat) (body : Lcmd) :
    bodyParams (body ++ [⟨ii, .Lret⟩]) = bodyParams body := by
  simp [bodyParams, frameSize, frameDirective_append_ret, frameAddDirective, faBytes,
    maxSpillIdx, maxVecSpillIdx, vecSpillBytes, bodyIsU64, qsaveBytesFor, bodyHasCall,
    calleeSavedToSave, bodyWritesBareReg, bodyParksQsave, List.foldl_append]

theorem foldCore_append_ret (p : Nat × Nat × Nat) (ex : List String) (ii : Nat) :
    ∀ (env : ConstIndexFold.KEnv) (body : Lcmd),
      foldCore p ex env (body ++ [⟨ii, .Lret⟩]) = foldCore p ex env body ++ [⟨ii, .Lret⟩] := by
  intro env body
  induction body generalizing env with
  | nil => simp [foldCore, foldInstr, skipB, idxBases, foldTarget?]
  | cons i is ih => simp [foldCore, ih, ConstIndexFold.foldEnv_append_ret]

theorem runtimeBases_append_ret (p : Nat × Nat × Nat) (ii : Nat) :
    ∀ (acc : List String) (env : ConstIndexFold.KEnv) (body : Lcmd),
      runtimeBases p acc env (body ++ [⟨ii, .Lret⟩]) = runtimeBases p acc env body := by
  intro acc env body
  induction body generalizing acc env with
  | nil => simp [runtimeBases, foldTarget?, idxBases]
  | cons i is ih => simp [runtimeBases, ih]

theorem constIndexFoldBody_append_ret (ii : Nat) (body : Lcmd) :
    constIndexFoldBody (body ++ [⟨ii, .Lret⟩]) = constIndexFoldBody body ++ [⟨ii, .Lret⟩] := by
  unfold constIndexFoldBody
  simp only [bodyParams_append_ret, runtimeBases_append_ret, foldCore_append_ret]
  split <;> rfl

theorem deadAfter_append_ret (p : Nat × Nat × Nat) (r : String) (ii : Nat) :
    ∀ (js : Lcmd), deadAfter p r (js ++ [⟨ii, .Lret⟩]) = deadAfter p r js := by
  intro js
  induction js with
  | nil => simp [deadAfter, isLret]
  | cons j js ih => simp only [List.cons_append, deadAfter, ih]

theorem dropDeadCore_append_ret (p : Nat × Nat × Nat) (ii : Nat) :
    ∀ (body : Lcmd),
      dropDeadCore p (body ++ [⟨ii, .Lret⟩]) = dropDeadCore p body ++ [⟨ii, .Lret⟩] := by
  intro body
  induction body with
  | nil =>
      simp only [List.nil_append, dropDeadCore, deadAfter]
      split <;> simp
  | cons i is ih =>
      simp only [List.cons_append, dropDeadCore, deadAfter_append_ret, ih]
      split
      · split <;> simp
      · simp

theorem dropDeadImmBody_append_ret (ii : Nat) (body : Lcmd) :
    dropDeadImmBody (body ++ [⟨ii, .Lret⟩]) = dropDeadImmBody body ++ [⟨ii, .Lret⟩] := by
  unfold dropDeadImmBody
  simp only [bodyParams_append_ret, dropDeadCore_append_ret]
  split <;> rfl

/-- The constant-index fold maps a body followed by `Lret` to the folded body followed by the
    same `Lret`. -/
theorem foldIndexedBody_append_ret (ii : Nat) (body : Lcmd) :
    foldIndexedBody (body ++ [⟨ii, .Lret⟩]) = foldIndexedBody body ++ [⟨ii, .Lret⟩] := by
  simp [foldIndexedBody, constIndexFoldBody_append_ret, dropDeadImmBody_append_ret,
    spellMemBody, spellMemInstr]

/-! ## 3. The register re-allocation and the two-address legalisation -/

/-- The register re-allocation maps a body followed by `Lret` to a body followed by the same
    `Lret`. -/
theorem reallocBody_append_ret (res : List String) (abi : IsaAbi) (recog : String → Bool)
    (body : Lcmd) (ii : Nat) :
    ∃ Y, reallocBody res (body ++ [⟨ii, .Lret⟩]) abi recog = Y ++ [⟨ii, .Lret⟩] := by
  set T : Lcmd := [⟨ii, .Lret⟩]
  set L0 := (labelLiveFrames (body ++ T)).insertMany (Piece.bar ⟨ii, .Lret⟩).frames
  obtain ⟨Y, hY, -⟩ := fold_out res abi T L0 (pieces body recog)
  refine ⟨Y, ?_⟩
  have hrb : reallocBody res (body ++ T) abi recog
      = ((pieces body recog).foldr (rstep res abi) (T, L0)).1 := by
    rw [reallocBody_eq, pieces_append_bar _ rfl, List.foldr_append]
    rfl
  rw [hrb, hY]

/-- The two-address legalisation maps a body followed by `Lret` to the legalised body followed
    by the same `Lret`. -/
theorem twoAddrBody_append_ret (ii : Nat) (body : Lcmd) :
    twoAddrBody (body ++ [⟨ii, .Lret⟩]) = twoAddrBody body ++ [⟨ii, .Lret⟩] := by
  have ha : bodyAvoids (body ++ [⟨ii, .Lret⟩]) = bodyAvoids body := by
    simp [bodyAvoids, instrAvoids]
  simp only [twoAddrBody, ha, LegalizeShiftImm.legalizeBody, List.flatMap_append]
  simp [legalizeInstr]

/-! ## 4. The composition -/

/-- The names whose values the owned back end keeps at the end of a body that ends with a
    return, with result registers `res`: every name that is not a location (a general-purpose
    register or a frame cell) and every general-purpose register live at the return, other
    than the save slot `scratchSave` of the two-address legalisation. -/
def RetKept (res : List String) (x : String) : Prop :=
  (isLoc x x86Abi = false ∨ (isGP x x86Abi = true ∧ x ∈ retLive res x86Abi))
    ∧ x ≠ scratchSave

/-- The relation of a final state `t` of a source body and a final state `t'` of its image
    under the owned back end, at the slot arrays `R` and result registers `res`. -/
structure OwnedObs (R : Slots) (res : List String) (t t' : LstateMF) : Prop where
  /-- The function names agree. -/
  lfn : t'.prog.lfn = t.prog.lfn
  /-- The zero flags agree. -/
  zf : t'.zf = t.zf
  /-- The word memories agree. -/
  mem : t'.prog.base.lmem = t.prog.base.lmem
  /-- The carry flags agree. -/
  cf : t'.prog.base.cf = t.prog.base.cf
  /-- The overflow flags agree. -/
  of : t'.prog.base.of = t.prog.base.of
  /-- The arrays other than the slot arrays agree. -/
  arr : ∀ r, isArrB R r = false → t'.prog.base.larr r = t.prog.base.larr r
  /-- The names of `RetKept res` other than the cell names agree. -/
  reg : ∀ x, isCellB R x = false → RetKept res x →
    t'.prog.base.reg.lvm x = t.prog.base.reg.lvm x
  /-- The cell names of `RetKept res` of the target hold the slot arrays of the source. -/
  cells : ∀ q ∈ R, ∃ arr : Fin q.2 → BitVec 64, t.prog.base.getArr q.1 64 q.2 = some arr
    ∧ ∀ j (hj : j < q.2), RetKept res (memName q.1 (8 * j)) →
      t'.prog.base.reg.lvm (memName q.1 (8 * j)) = ⟨64, arr ⟨j, hj⟩⟩

/-- **`ownedBody_lsemFuelMemF`: the four stages of `ownedLprog` on one body.** Let the body be
    `body` followed by `Lret`, with result registers `res` that are no frame cells. Let the
    tagging `tag` satisfy the conditions of the four stage theorems (`TagShape`,
    `TagFirstSrc`, the register tag on the re-allocated fragment), let the slot arrays `R` pass
    `slotsOkB` and `cellsDistinctB`, and let the stages pass their checks: `optBlocksOKB` on
    `body`, `FoldIndexedOK` on its optimised form, `reallocCfgOKB` on the folded body and
    `twoAddrOK` on the re-allocated body without its return.
    Every halting run of the checked machine on the typed body without its return, from
    program counter `0` and a state `s` of `RelInv A`, is matched by a halting run of the
    typed output body without its return from every state `s'` cell-related to `s`, with at
    most five times the fuel, into a state related by `OwnedObs R res`. -/
theorem ownedBody_lsemFuelMemF {A : String → Option Nat} {tag : LinstrR → MemTag}
    (hT : TagShape tag) (hF : TagFirstSrc tag)
    (htag : ∀ d opn srcs, isRecognizedOpn opn = true → opn ≠ "LOADIDX" → opn ≠ "STOREIDX" →
      tag (.Lopn [.reg d] opn srcs) = .reg none)
    {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    (res : List String) (hres : ∀ y ∈ res, isFrame y = false) (body : Lcmd) (ii : Nat)
    (hbb : optBlocksOKB A tag body = true)
    (hfold : FoldIndexedOK tag R (optimizeBasicBlocks body))
    (hra : reallocCfgOKB tag isRecognizedOpn
      (foldIndexedBody (optimizeBasicBlocks body) ++ [⟨ii, .Lret⟩]) = true)
    (htw : twoAddrOK tag (reallocBody res (foldIndexedBody (optimizeBasicBlocks body)
      ++ [⟨ii, .Lret⟩]) x86Abi isRecognizedOpn).dropLast = true)
    (fn : String) {fuel : Nat} {s s' t : LstateMF}
    (hpc : s.prog.base.lpc = 0) (hI : RelInv A s.prog.base) (hC : CellRelF R [] s s')
    (hrun : lsemFuelMemFk true
      (singletonProgM fn (dropRet (typeBody tag (body ++ [⟨ii, .Lret⟩])))) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 5
      ∧ lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag
          (twoAddrBody (reallocBody res (foldIndexedBody (optimizeBasicBlocks
            (body ++ [⟨ii, .Lret⟩]))) x86Abi isRecognizedOpn))))) fuel' s' = some t'
      ∧ OwnedObs R res t t' := by
  rw [dropRet_typeBody_ret] at hrun
  obtain ⟨f1, t1, hf1, hrun1, hlfn1, hzf1, hpc1, -⟩ := optBlocksOKB_sound hT hbb fn hpc hI hrun
  obtain ⟨f2, t2, hf2, hrun2, hobs2, hzf2, hlfn2⟩ :=
    foldIndexedBody_lsemFuelMemF hR hD hfold fn f1 hpc hC hrun1
  have hpc' : s'.prog.base.lpc = 0 := by
    have := hC.base.pc
    simp only [LstateM.lpc] at hpc ⊢
    rw [this, hpc]
  obtain ⟨hret, hkeep, hcmp⟩ := reallocCfgOKB_sound hra
  obtain ⟨f3, t3, hf3, hrun3, hlfn3, hzf3, harr3, hmem3, hcf3, hof3, hreg3⟩ :=
    reallocBody_lsemFuelMemF res x86Abi isRecognizedOpn tag (abiOK_x86 res hres) htag _ hret
      hkeep hcmp fn hpc' (by rw [dropRet_typeBody_ret]; exact hrun2)
  obtain ⟨Y, hY⟩ := reallocBody_append_ret res x86Abi isRecognizedOpn
    (foldIndexedBody (optimizeBasicBlocks body)) ii
  rw [hY, dropRet_typeBody_ret] at hrun3
  rw [hY, List.dropLast_concat] at htw
  obtain ⟨f4, t4, hf4, hrun4, hag4, hzf4, hlfn4, -⟩ :=
    twoAddrBody_lsemFuelMemF hF htw fn s' t3 hpc' f3 hrun3
  have hend : endRegs res x86Abi (foldIndexedBody (optimizeBasicBlocks body) ++ [⟨ii, .Lret⟩])
      = retLive res x86Abi := by
    simp [endRegs]
  rw [hend] at hreg3
  unfold EqPc at hpc1
  rw [hpc1] at hobs2
  refine ⟨f4, t4, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [optimizeBasicBlocks_append_ret, foldIndexedBody_append_ret, hY,
      twoAddrBody_append_ret, dropRet_typeBody_ret]
    exact hrun4
  · exact hlfn4.trans (hlfn3.trans (hlfn2.trans hlfn1))
  · exact hzf4.trans (hzf3.trans (hzf2.trans hzf1))
  · exact hag4.mem.trans (hmem3.trans hobs2.mem)
  · exact hag4.cf.trans (hcf3.trans hobs2.cf)
  · exact hag4.of.trans (hof3.trans hobs2.of)
  · intro r hr
    exact (congrFun (hag4.arr.trans harr3) r).trans (hobs2.arr r hr)
  · intro x hx hk
    exact (hag4.reg x (fun _ => hk.2)).trans ((hreg3 x hk.1).trans (hobs2.reg x hx))
  · intro q hq
    obtain ⟨arr, harr, hcell⟩ := hobs2.cells q hq
    exact ⟨arr, harr, fun j hj hk =>
      (hag4.reg _ (fun _ => hk.2)).trans ((hreg3 _ hk.1).trans (hcell j hj))⟩

/-- **`ownedLprog_lsemFuelMemF`: the owned back end on the functions of a program.** Every
    function `(fn, fd)` of `p` whose body ends with `Lret` has the function `(fn, fd')` in
    `ownedLprog p`, with the same result registers and the body of the four stages. When the
    stages pass their checks on the bodies they read (`optBlocksOKB` on the body without its
    return, `FoldIndexedOK` on its optimised form, `reallocCfgOKB` on the folded body,
    `twoAddrOK` on the re-allocated body without its return), the conclusion of
    `ownedBody_lsemFuelMemF` holds between the two bodies. -/
theorem ownedLprog_lsemFuelMemF (p : Lprog) {fn : String} {fd : Lfundef}
    (hf : (fn, fd) ∈ p.lp_funcs) (hend : endsWithLret fd.lfd_body = true)
    {A : String → Option Nat} {tag : LinstrR → MemTag} (hT : TagShape tag) (hF : TagFirstSrc tag)
    (htag : ∀ d opn srcs, isRecognizedOpn opn = true → opn ≠ "LOADIDX" → opn ≠ "STOREIDX" →
      tag (.Lopn [.reg d] opn srcs) = .reg none)
    {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    (hres : ∀ y ∈ fd.lfd_res, isFrame y = false)
    (hbb : optBlocksOKB A tag fd.lfd_body.dropLast = true)
    (hfold : FoldIndexedOK tag R (optimizeBasicBlocks fd.lfd_body.dropLast))
    (hra : reallocCfgOKB tag isRecognizedOpn
      (foldIndexedBody (optimizeBasicBlocks fd.lfd_body)) = true)
    (htw : twoAddrOK tag (reallocBody fd.lfd_res (foldIndexedBody
      (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn).dropLast = true) :
    ∃ fd', (fn, fd') ∈ (ownedLprog p).lp_funcs ∧ fd'.lfd_res = fd.lfd_res
      ∧ fd'.lfd_body = twoAddrBody (reallocBody fd.lfd_res
          (foldIndexedBody (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn)
      ∧ ∀ {fuel : Nat} {s s' t : LstateMF}, s.prog.base.lpc = 0 → RelInv A s.prog.base →
        CellRelF R [] s s' →
        lsemFuelMemFk true (singletonProgM fn (dropRet (typeBody tag fd.lfd_body))) fuel s
          = some t →
        ∃ fuel' t', fuel' ≤ fuel * 5
          ∧ lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag fd'.lfd_body))) fuel' s'
              = some t'
          ∧ OwnedObs R fd.lfd_res t t' := by
  let fd' : Lfundef := { fd with lfd_body := twoAddrBody (reallocBody fd.lfd_res
      (foldIndexedBody (optimizeBasicBlocks fd.lfd_body)) x86Abi isRecognizedOpn) }
  refine ⟨fd', ?_, ?_, ?_, ?_⟩
  rotate_left
  · rfl
  · rfl
  rotate_left
  · simp only [ownedLprog, mapBodies, LprogGpRealloc.reallocLprog, foldIndexedLprog,
      optimizeLprogBasicBlocks, List.map_map, List.mem_map]
    grind
  · intro fuel s s' t hpc hI hC hrun
    obtain ⟨k, hk⟩ := dropLast_append_Lret hend
    generalize fd.lfd_body.dropLast = b0 at hk hbb hfold
    have e : foldIndexedBody (optimizeBasicBlocks fd.lfd_body)
        = foldIndexedBody (optimizeBasicBlocks b0) ++ [⟨k, .Lret⟩] := by
      rw [← hk, optimizeBasicBlocks_append_ret, foldIndexedBody_append_ret]
    rw [e] at hra htw
    rw [← hk] at hrun
    have := ownedBody_lsemFuelMemF hT hF htag hR hD fd.lfd_res hres b0 k hbb hfold hra htw fn
      hpc hI hC hrun
    grind

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogFuel
