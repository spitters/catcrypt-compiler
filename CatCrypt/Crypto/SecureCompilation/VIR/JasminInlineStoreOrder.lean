/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreSpillArm

@[expose] public section

set_option autoImplicit false

/-!
# The value of an output cell in the emitted instruction order

`physBodyWithStores` interleaves each designated binding's store block with the
body expansions, so the list it emits is `pre ++ block ++ post` for that block,
with `pre` the expansions and stores before it and `post` those after it
(`JasminInlineStoreBlockEmit.physBodyWithStores_inlineStoreOps`,
`JasminInlineStoreSpillArm.physBodyWithStores_spillStoreOps`).

`emittedStoreBlock_value` reads the block's cell after a run of the whole list:
when no instruction of `post` names the cell as a destination, the cell holds
the masked value the block's source register held when the block was reached.
`physBodyWithStores_cell_value` states this for the list `physBodyWithStores`
emits, with the `post` condition replaced by a count over the emitted list: the
cell is the destination of exactly one instruction. `LinstrR.writesReg` is the
decidable destination test, so the count is a `#kat` on a concrete kernel.

The buffer mnemonic is carried under `MovesMasked`, so the statements cover the
narrow `MOV:8` and `MOV:16` exports along with the word-moving ones.

## Scope

The run is `lsemStraight` over the emitted list lifted to `LinstrR`. `lsemStep`
returns `none` on `Lret`, so a body carrying its `Lret` terminator has to be
passed without it, as `JasminLsemSimulation.straightOps_eq_body` does with
`dropLast`. The theorems say nothing about the value the source register holds
when the block is reached; `JasminBindingPrefixDenote.straightOps_binding_denote`
is the reading of that register for a uniform-`regArith` chain, over the
pre-allocation names.

`physBodyWithStores_cell_value` takes the spill-free arm. The spill-routed arm
goes through `emittedStoreBlock_value` with `physBodyWithStores_spillStoreOps`
in the same way.

## Main definitions

* `LinstrR.writesReg` — the instruction names the register among its
  destinations.

## Main results

* `lsemStep_lvm_of_not_writesReg`, `lsemStraight_lvm_of_not_writesReg` — a step,
  or a run, of instructions none of which names `r` as a destination leaves
  `r` unchanged.
* `storeBlockFor_countP_cell` — a store block names its cell as a destination
  exactly once.
* `emittedStoreBlock_value` — after a run of `pre ++ block ++ post` with `post`
  not naming the cell, the cell holds the masked source value at the block.
* `emittedStoreBlock_value_of_countP` — the same with the `post` condition
  replaced by the count over the whole list.
* `physBodyWithStores_cell_value` — for a designated binding with a non-spill
  remapped destination, the cell of its output target holds the masked value of
  that destination at the block, after a run of the emitted list.
* `mixedStoreBlocks_binding_denote` — with the sources the binding registers of a
  uniform-`regArith` chain, a target's cell holds the masked denotation of the
  source program truncated at that binding.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreOrder

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminBindingPrefixDenote
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreValue
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreBlockEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreSpillArm

/-! ## 1. The destination test and its frame -/

/-- The instruction names the register `r` among its destinations. -/
def LinstrR.writesReg (r : String) : LinstrR → Bool
  | .Lopn dsts _ _ => dsts.contains (.reg r)
  | _ => false

/-- A step of an instruction that does not name `r` as a destination leaves `r`
    unchanged. -/
theorem lsemStep_lvm_of_not_writesReg {w : Nat} (i : LinstrR) (s s' : Lstate w)
    (h : lsemStep i s = some s') (r : String) (hr : LinstrR.writesReg r i = false) :
    s'.lvm r = s.lvm r := by
  cases i with
  | Lopn dsts opn srcs =>
      rcases dsts with _ | ⟨d, ds⟩
      · simp [lsemStep] at h
      cases d <;> cases ds
      all_goals try (simp [lsemStep] at h; done)
      rename_i n
      have hne : r ≠ n := by
        intro he; subst he; simp [LinstrR.writesReg] at hr
      exact lsemStep_lvm_of_ne n opn srcs s s' h r hne
  | Lalign => simp [lsemStep] at h; subst h; rfl
  | Llabel _ _ => simp [lsemStep] at h; subst h; rfl
  | Lsyscall _ => simp [lsemStep] at h
  | Lgoto _ => simp [lsemStep] at h
  | Lcond _ _ => simp [lsemStep] at h
  | Ligoto _ => simp [lsemStep] at h
  | Lcall _ _ => simp [lsemStep] at h
  | Lret => simp [lsemStep] at h
  | LstoreLabel _ _ => simp [lsemStep] at h

/-- A run of instructions none of which names `r` as a destination leaves `r`
    unchanged. -/
theorem lsemStraight_lvm_of_not_writesReg {w : Nat} :
    ∀ (is : List LinstrR) (s s' : Lstate w), lsemStraight is s = some s' →
      ∀ r : String, (∀ i ∈ is, LinstrR.writesReg r i = false) → s'.lvm r = s.lvm r := by
  intro is
  induction is with
  | nil => intro s s' h r _; cases h; rfl
  | cons i rest ih =>
      intro s s' h r hr
      rw [lsemStraight_cons] at h
      rcases hstep : lsemStep i s with _ | s1
      · rw [hstep] at h; simp at h
      · rw [hstep] at h
        simp only at h
        rw [ih s1 s' h r (fun i' hi' => hr i' (by simp [hi']))]
        exact lsemStep_lvm_of_not_writesReg i s s1 hstep r (hr i (by simp))

/-! ## 2. The block names its cell once -/

/-- A store block names its cell as a destination exactly once, whichever arm
    the target takes. -/
theorem storeBlockFor_countP_cell (movReg movBuf storeBase : String) (t : OutTarget) :
    (storeBlockFor movReg movBuf storeBase t).countP
      (LinstrR.writesReg (memName storeBase t.off)) = 1 := by
  have h1 := memName_ne_reloadScratch storeBase t.off
  have h2 := memName_ne_reloadScratch2 storeBase t.off
  unfold storeBlockFor
  split
  · simp [spillStoreOps, LinstrR.writesReg, h1, h2]
  · simp [inlineStoreOps, LinstrR.writesReg, h2]

/-! ## 3. The cell after a run of the emitted list -/

/-- **The cell after a run of `pre ++ block ++ post`.** When no instruction of
    `post` names the block's cell as a destination, the run reaches the block
    from a state `sMid` (the run of `pre`) and leaves the cell holding the
    masked value the block's source held in `sMid`. -/
theorem emittedStoreBlock_value {w : Nat} (movReg movBuf storeBase : String)
    (mask : BitVec w) (hreg : MovesWord w movReg) (hbuf : MovesMasked w mask movBuf)
    (t : OutTarget) (hsrc : t.src ≠ reloadScratch2) (pre post : List LinstrR)
    (s s' : Lstate w)
    (hrun : lsemStraight (pre ++ storeBlockFor movReg movBuf storeBase t ++ post) s
      = some s')
    (hpost : ∀ i ∈ post, LinstrR.writesReg (memName storeBase t.off) i = false) :
    ∃ sMid : Lstate w, lsemStraight pre s = some sMid ∧
      s'.lvm (memName storeBase t.off) = sMid.lvm t.src &&& mask := by
  rw [lsemStraight_append, lsemStraight_append] at hrun
  rcases hpre : lsemStraight pre s with _ | sMid
  · rw [hpre] at hrun; simp at hrun
  · rw [hpre] at hrun
    simp only [Option.bind_some] at hrun
    rcases hblk : lsemStraight (storeBlockFor movReg movBuf storeBase t) sMid with _ | sB
    · rw [hblk] at hrun; simp at hrun
    · rw [hblk] at hrun
      simp only [Option.bind_some] at hrun
      refine ⟨sMid, rfl, ?_⟩
      rw [lsemStraight_lvm_of_not_writesReg post sB s' hrun _ hpost]
      exact storeBlockFor_value movReg movBuf storeBase mask hreg hbuf t hsrc sMid sB hblk

/-- **The cell after a run of a list naming it once.** The `post` condition of
    `emittedStoreBlock_value` follows from the cell being the destination of
    exactly one instruction of the whole list, since the block itself names it
    once. -/
theorem emittedStoreBlock_value_of_countP {w : Nat} (movReg movBuf storeBase : String)
    (mask : BitVec w) (hreg : MovesWord w movReg) (hbuf : MovesMasked w mask movBuf)
    (t : OutTarget) (hsrc : t.src ≠ reloadScratch2) (pre post : List LinstrR)
    (s s' : Lstate w)
    (hrun : lsemStraight (pre ++ storeBlockFor movReg movBuf storeBase t ++ post) s
      = some s')
    (hcount : (pre ++ storeBlockFor movReg movBuf storeBase t ++ post).countP
      (LinstrR.writesReg (memName storeBase t.off)) = 1) :
    ∃ sMid : Lstate w, lsemStraight pre s = some sMid ∧
      s'.lvm (memName storeBase t.off) = sMid.lvm t.src &&& mask := by
  refine emittedStoreBlock_value movReg movBuf storeBase mask hreg hbuf t hsrc pre post
    s s' hrun ?_
  rw [List.countP_append, List.countP_append, storeBlockFor_countP_cell] at hcount
  have hzero : post.countP (LinstrR.writesReg (memName storeBase t.off)) = 0 := by omega
  exact fun i hi => by simpa using List.countP_eq_zero.mp hzero i hi

/-! ## 4. The emitted list -/

/-- **The output cell of a designated binding after a run of the emitted list.**
    For a designated binding at virtual position `virtIdx` whose remapped
    destination is the register `src`, not a spill slot and not the out-pointer
    scratch, whose output target is `(base, off)`, and whose cell
    `memName storeBase off` is the destination of exactly one instruction of the
    emitted list, a run of the emitted list reaches that binding's store block
    from a state `sMid` and leaves the cell holding `sMid.lvm src &&& mask`, the
    mask that of the buffer mnemonic `physAbiMovBuf body abiW`. -/
theorem physBodyWithStores_cell_value {w : Nat}
    (shiftImm : ShiftImmOracle) (body : Lcmd) (inLoadMap : InLoadMap)
    (loadBase : String) (outStoreMap : OutStoreMap) (storeBase : String)
    (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    {i : Linstr} {virtIdx : Nat} (hmem : (i, virtIdx) ∈ body.zipIdx)
    {d : LOperand} {ds : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn (d :: ds) opn srcs)
    (hlo : bindingIndexAt body virtIdx ≥ numBindings body - outStoreMap.length)
    (hhi : bindingIndexAt body virtIdx < numBindings body)
    {base : String} {off : Nat}
    (hout : outStoreMap[bindingIndexAt body virtIdx
              - (numBindings body - outStoreMap.length)]? = some (base, off))
    {src : String} (hd : physRmap body outStoreMap reservedVec d = .reg src)
    (hnospill : (LOperand.reg src).isSpill = false) (hsrc : src ≠ reloadScratch2)
    (mask : BitVec w) (hbuf : MovesMasked w mask (physAbiMovBuf body abiW))
    (s s' : Lstate w)
    (hrun : lsemStraight ((physBodyWithStores shiftImm body inLoadMap loadBase
      outStoreMap storeBase abiW memrefBaseReload callArgBaseReload
      reservedVec).map Linstr.li_i) s = some s')
    (hcount : ((physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap
      storeBase abiW memrefBaseReload callArgBaseReload reservedVec).map
        Linstr.li_i).countP (LinstrR.writesReg (memName storeBase off)) = 1) :
    ∃ sMid : Lstate w, s'.lvm (memName storeBase off) = sMid.lvm src &&& mask := by
  obtain ⟨pre, post, hsplit⟩ := physBodyWithStores_inlineStoreOps shiftImm body inLoadMap
    loadBase outStoreMap storeBase abiW memrefBaseReload callArgBaseReload reservedVec
    hmem hi hlo hhi hout (hd ▸ hnospill)
  rw [hsplit, hd] at hrun hcount
  have hblk : (atTagZero (inlineStoreOps (physAbiMovBuf body abiW) storeBase off
        (.reg src))).map Linstr.li_i
      = storeBlockFor "MOVQ" (physAbiMovBuf body abiW) storeBase ⟨off, src, false⟩ := by
    simp [atTagZero, inlineStoreOps, storeBlockFor]
  simp only [List.map_append, hblk] at hrun hcount
  obtain ⟨sMid, _, hval⟩ := emittedStoreBlock_value_of_countP "MOVQ"
    (physAbiMovBuf body abiW) storeBase mask (MovesWord_MOVQ w) hbuf
    ⟨off, src, false⟩ hsrc _ _ s s' hrun hcount
  exact ⟨sMid, hval⟩

/-! ## 5. Reading a masked cell as a truncated denotation -/

/-- **A target's cell holds the masked truncated denotation.** Running the chain
    a uniform-`regArith` `Com` emits and then the mixed store blocks, the cell of
    a target whose source is binding `k`'s register holds the denotation of the
    source program truncated at binding `k`, conjoined with the buffer
    mnemonic's mask. The masked form of
    `JasminInlineStoreValue.storeBlocks_binding_denote`, with the same order:
    the whole chain, then all the stores. -/
theorem mixedStoreBlocks_binding_denote {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com)
    (movReg movBuf storeBase : String) (mask : BitVec w)
    (hreg : MovesWord w movReg) (hbuf : MovesMasked w mask movBuf)
    {nArgs curDepth : Nat} {st stMid st' : Lstate w} {V : Ctxt.Valuation Γ}
    (hlen : Γ.length = curDepth) (harg : nArgs ≤ curDepth)
    (hagree : StoreAgrees w nArgs curDepth st V)
    (hchain : lsemStraight (straightOps nArgs com curDepth) st = some stMid)
    (targets : List OutTarget)
    (hrun : lsemStraight (mixedStoreBlocks movReg movBuf storeBase targets) stMid = some st')
    (hsrcR15 : ∀ u ∈ targets, u.src ≠ reloadScratch)
    (hsrcR14 : ∀ u ∈ targets, u.src ≠ reloadScratch2)
    (hsrcCell : ∀ u ∈ targets, ∀ u' ∈ targets, u.src ≠ memName storeBase u'.off)
    (hdistinct : targets.Pairwise (fun u u' => u.off ≠ u'.off))
    (off k : Nat) (spilled : Bool)
    (hmemT : (⟨off, regName (curDepth + k), spilled⟩ : OutTarget) ∈ targets)
    (hk : k < comLen com) (hty : comBindingTy com k = .reg w) :
    st'.lvm (memName storeBase off)
      = @HAnd.hAnd (BitVec w) (BitVec w) (BitVec w) _
          (hty ▸ (comPrefix com k).denote V : ⟦(JasminTy.reg w)⟧) mask := by
  have hval := mixedStoreBlocks_value movReg movBuf storeBase mask hreg hbuf targets stMid
    st' hrun hsrcR15 hsrcR14 hsrcCell hdistinct ⟨off, regName (curDepth + k), spilled⟩ hmemT
  rw [hval]
  congr 1
  exact straightOps_binding_denote hcom hlen harg hagree hchain hk hty

end CatCrypt.Crypto.SecureCompilation.VIR.JasminInlineStoreOrder
