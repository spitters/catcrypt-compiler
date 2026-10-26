/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ImageSpFree
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW

@[expose] public section

set_option autoImplicit false

/-!
# The image of a cell body names no stack pointer

The cell routes, of the loops with carry chains and cells and of the straight-line programs
with cells, check the class `printedAddrWB` of printed bodies with carry chains, and their
images are images of the cell body `cellBody slotArr body`, in which each access
`LOAD:64 D, mem.B.off` or `STORE:64 mem.B.off, S` to a cell of an array `A` of the slot map
is the move of the name `memName A off`. This module derives, for such an image, the two
Boolean conditions of the procedure specification of a callee: no instruction names the
stack pointer `RSP`, and no instruction is a call or a return. The derivation uses the
predicate `rspFreeNameB` of `ImageSpFree`, which the cell name of a name inherits.

## Main results

* `virtImg_rspFree`, `virtImg_noCall_of`: the two facts for the image of a body whose
  instructions pass `RspFreeUpToStore`, and are no calls and no returns.
* `cellMove_cases`: an instruction of the cell body is the instruction of the body or the
  move of a cell name of an array of the slot map.
* `cellImage_spFreeBodyB`, `cellImage_noCall`: the two facts for the image of the cell body
  of a covered printed body with carry chains.
* `rspFreeNameB_slotArrOf`, `rspFreeNameB_slotR_synthRen`: every array name of the slot map
  of a layout, and of the slot map `slotR` at the synthesised renaming, passes
  `rspFreeNameB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg imgInstr accArr
  physImgB accOkB bitStore? bitStore?_spec virtImg_getElem? cellIdxStore?_spec arrImmImg
  arrImmImg_lopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (normA condPol)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames cellBase)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellParts? slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (isCall)
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf resolveVar_top)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (straightArrB chainAlias
  straightRegB straightRouteB straightRouteOutB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (physImgB_at accArr_spec
  imgInstr_stx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpList mem_gpList Arm
  classify classify_instr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (AArm classifyA
  classifyA_instr cellParts?_gp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (notSlot_of_cell
  instrOKWB printedAddrWB classifyK classifyK_spec castOk imm32Ok classifyS classifyS_instr
  SArm classifyC classifyC_instr CArm classifyM classifyM_instr MArm classifyI classifyI_instr
  iOk classifyL classifyL_instr lOk classifyV classifyV_instr vOk vtOk vfOk kOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB instrOKB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (isSpillOrQsave spillQsaveOff)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody cellMove
  cellBody_getElem? cellBody_length cellA_ld cellA_st hasPrefix_memName hasPrefix_of_cellParts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC slotArrC_some
  straightCellB cellRouteB cellArrs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW (slotR cellArrsR)

/-! ## 1. The image of a body whose instructions pass `RspFreeUpToStore` -/

/-- An instruction of the image of a body is the image of an instruction of the body at a
    position before the last. -/
theorem mem_virtImg_lt {slotArr : String → Option (String × Nat)} {body : Lcmd} {i : LinstrRM}
    (hi : i ∈ virtImg slotArr body) :
    ∃ k j, body[k]? = some j ∧ k + 1 < body.length ∧ i = imgInstr slotArr body k j.li_i := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
  rw [virtImg_getElem?] at hk
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hk
  rw [List.dropLast_eq_take, List.getElem?_take] at hj
  split_ifs at hj with hlt
  exact ⟨k, j, hj, by omega, rfl⟩

/-- **The image of an instruction that passes `RspFreeUpToStore` passes `rspFreeB`**, when
    every indexed access of the instruction resolves to an array (`accOkB`), every array
    name of the slot map passes `rspFreeNameB` and every instruction of the body before it
    passes `RspFreeUpToStore`. -/
theorem rspFreeB_imgInstr {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {x : LinstrR} (hx : RspFreeUpToStore x) (hacc : accOkB slotArr body k x = true)
    (hsl : ∀ q A n, slotArr q = some (A, n) → rspFreeNameB A = true)
    (hpre : ∀ j i, j < k → body[j]? = some i → RspFreeUpToStore i.li_i) :
    rspFreeB (imgInstr slotArr body k x).fst = true := by
  have harr : ∀ {b A : String} {n : Nat}, accArr slotArr body k b = some (A, n) →
      rspFreeNameB A = true := by
    intro b A n h
    obtain ⟨q, -, hq, -⟩ := accArr_spec h
    exact hsl q A n hq
  rcases hx with hf | ⟨d, b, i, v, rfl, hb, hi, hv⟩
  · rcases imgInstr_cases slotArr body k x with h | ⟨d, o, b, idx, A, n, -, rfl, hA, h⟩ |
      ⟨d, o, b, idx, v, A, n, -, rfl, hA, h⟩ | ⟨d, n, rfl, h⟩ | ⟨A, n, q, v, hc, h⟩ |
      ⟨ri, hri, h⟩
    · rw [h]
      simp only [rspFreeB, operandNames_normA] at hf ⊢
      exact hf
    · rw [h]
      have hA' := harr hA
      simp [rspFreeB, operandNames, srcNames] at hf ⊢
      simp [hf, hA']
    · rw [h]
      have hA' := harr hA
      simp [rspFreeB, operandNames, srcNames] at hf ⊢
      simp [hf, hA']
    · rw [h]
      simpa [rspFreeB, operandNames, srcNames] using hf
    · obtain ⟨c, D, B, X, d1, s, l, r', m, hx, -, h3, -, -, -, hr', hm, -, -, -, -, -, -, -,
        hacc'⟩ := cellIdxStore?_spec hc
      obtain ⟨q', -, hq', -⟩ := accArr_spec hacc'
      have hqf : rspFreeNameB q = true := by
        rcases hpre (k - 3) r' (by omega) hr' with hf' | ⟨_, _, _, _, he, -⟩
        · have hn : ∀ r ∈ operandNames r'.li_i, rspFreeNameB r = true := by
            simpa [rspFreeB] using hf'
          exact hn q (rdWr_sub (read_of_slotMov hm))
        · rw [he] at hm
          simp [slotMov?] at hm
      rw [h]
      subst hx
      simp [rspFreeB, operandNames, srcNames] at hf ⊢
      simp [hf, hsl q' A n hq', hqf]
    · rw [h]
      unfold arrImmImg at hri
      split at hri
      · split_ifs at hri
        split at hri
        · rename_i A n hA
          cases hri
          simp [rspFreeB, operandNames, srcNames, harr hA]
        · cases hri
      · split_ifs at hri
        split at hri
        · rename_i A n hA
          cases hri
          simp [rspFreeB, operandNames, srcNames] at hf ⊢
          simp [hf, harr hA]
        · cases hri
      · cases hri
  · simp only [accOkB, Bool.true_and] at hacc
    obtain ⟨⟨A, n⟩, hA⟩ := Option.isSome_iff_exists.mp hacc
    rw [imgInstr_stx slotArr body k hA]
    simp [rspFreeB, operandNames, srcNames, harr hA, hi, hv]

/-- **The image of a body whose instructions before the last pass `RspFreeUpToStore` names
    no stack name**, for a body in the image class `physImgB` at a slot map whose array
    names pass `rspFreeNameB`. -/
theorem virtImg_rspFree {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hx : ∀ k j, body[k]? = some j → k + 1 < body.length → RspFreeUpToStore j.li_i)
    (hphys : physImgB slotArr body = true)
    (hsl : ∀ q A n, slotArr q = some (A, n) → rspFreeNameB A = true) :
    ∀ i ∈ virtImg slotArr body, rspFreeB i.fst = true := by
  intro i hi
  obtain ⟨k, j, hk, hlt, rfl⟩ := mem_virtImg_lt hi
  exact rspFreeB_imgInstr (hx k j hk hlt) (physImgB_at hphys hk).1 hsl
    (fun j' i' hj' hb' => hx j' i' hb' (by omega))

/-- The widening multiply read at its width is a call or a return exactly when the
    instruction is. -/
theorem isCall_normA (x : LinstrR) : isCall (normA x) = isCall x := by
  cases x <;> rfl

/-- **The image of a body none of whose instructions before the last is a call or a return
    contains no call and no return**, at every slot map. -/
theorem virtImg_noCall_of {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hx : ∀ k j, body[k]? = some j → k + 1 < body.length → isCall j.li_i = false) :
    ((virtImg slotArr body).all fun i => !isCall i.fst) = true := by
  refine List.all_eq_true.mpr fun i hi => ?_
  obtain ⟨k, j, hk, hlt, rfl⟩ := mem_virtImg_lt hi
  rcases imgInstr_cases slotArr body k j.li_i with h | ⟨_, _, _, _, _, _, -, -, -, h⟩ |
    ⟨_, _, _, _, _, _, _, -, -, -, h⟩ | ⟨_, _, -, h⟩ | ⟨_, _, _, _, -, h⟩ | ⟨_, hri, h⟩
  · rw [h, isCall_normA, hx k j hk hlt]
    rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · obtain ⟨_, _, _, he⟩ := arrImmImg_lopn hri
    rw [h, he]; rfl

/-! ## 2. The covered printed bodies with carry chains and their cell bodies -/

/-- Every instruction of a covered printed body with carry chains at a position before the
    last is in the covered fragment with carry chains. -/
theorem instrOKWB_of_printedAddrWB {body : Lcmd} (hp : printedAddrWB body = true) {k : Nat}
    {j : Linstr} (hk : body[k]? = some j) (hlt : k + 1 < body.length) :
    instrOKWB body (X86Backend.LprogBytesDecode.Params.ofBody body) j.li_i = true := by
  simp only [printedAddrWB, Bool.and_eq_true, List.all_eq_true] at hp
  refine hp.1.1.1.2 j (List.mem_iff_getElem?.mpr ⟨k, ?_⟩)
  rw [List.dropLast_eq_take, List.getElem?_take, ite_eq_left (by omega)]
  exact hk

/-- An instruction of the covered fragment with carry chains is no call and no return. -/
theorem isCall_of_instrOKWB {body : Lcmd} {P : X86Backend.LprogBytesDecode.Params}
    {x : LinstrR} (h : instrOKWB body P x = true) : isCall x = false := by
  cases x <;> first | rfl | simp [instrOKWB] at h

/-- **The shapes of the frame-word move of an instruction**: the instruction; the move of
    the cell name of a resolved array into the destination of a cell load; or the move of
    the stored register of a cell store into the cell name of a resolved array. -/
theorem cellMove_cases (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : Linstr) :
    cellMove slotArr body k i = i
    ∨ (∃ D n mm B A m off, i.li_i = .Lopn [.reg D] mm [.reg n]
        ∧ accArr slotArr body k B = some (A, m)
        ∧ (cellMove slotArr body k i).li_i = .Lopn [.reg D] "MOVQ" [.reg (memName A off)])
    ∨ ∃ n S mm B A m off, i.li_i = .Lopn [.reg n] mm [.reg S]
        ∧ accArr slotArr body k B = some (A, m)
        ∧ (cellMove slotArr body k i).li_i = .Lopn [.reg (memName A off)] "MOVQ" [.reg S] := by
  unfold cellMove
  split
  · rename_i D B off hc
    obtain ⟨mm, n, hx, -, -⟩ := cellA_ld hc
    split
    · rename_i A m hA
      exact Or.inr (Or.inl ⟨D, n, mm, B, A, m, off, hx, hA, rfl⟩)
    · exact Or.inl rfl
  · rename_i B off S hc
    obtain ⟨mm, n, hx, -, -⟩ := cellA_st hc
    split
    · rename_i A m hA
      exact Or.inr (Or.inr ⟨n, S, mm, B, A, m, off, hx, hA, rfl⟩)
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **The frame-word move of an instruction that passes `RspFreeUpToStore` passes it**, at a
    slot map whose array names pass `rspFreeNameB`: the cell name of a move is the cell name
    of an array of the slot map. -/
theorem rspFree_cellMove {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : Linstr} (hx : RspFreeUpToStore i.li_i)
    (hsl : ∀ q A n, slotArr q = some (A, n) → rspFreeNameB A = true) :
    RspFreeUpToStore (cellMove slotArr body k i).li_i := by
  have harr : ∀ {b A : String} {n : Nat}, accArr slotArr body k b = some (A, n) →
      rspFreeNameB A = true := by
    intro b A n h
    obtain ⟨q, -, hq, -⟩ := accArr_spec h
    exact hsl q A n hq
  rcases cellMove_cases slotArr body k i with h | ⟨D, n, mm, B, A, m, off, hi, hA, h⟩ |
    ⟨n, S, mm, B, A, m, off, hi, hA, h⟩
  · rw [h]
    exact hx
  · rw [h]
    rw [hi] at hx
    rcases hx with hf | ⟨_, _, _, _, he, -⟩
    · left
      simp [rspFreeB, operandNames, srcNames] at hf ⊢
      exact ⟨hf.1, rspFreeNameB_memName (harr hA) off⟩
    · simp at he
  · rw [h]
    rw [hi] at hx
    rcases hx with hf | ⟨_, _, _, _, he, -⟩
    · left
      simp [rspFreeB, operandNames, srcNames] at hf ⊢
      exact ⟨rspFreeNameB_memName (harr hA) off, hf.2⟩
    · simp at he

/-- The frame-word move of an instruction that is no call and no return is no call and no
    return. -/
theorem isCall_cellMove {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : Linstr} (hx : isCall i.li_i = false) :
    isCall (cellMove slotArr body k i).li_i = false := by
  rcases cellMove_cases slotArr body k i with h | ⟨_, _, _, _, _, _, _, -, -, h⟩ |
    ⟨_, _, _, _, _, _, _, -, -, h⟩
  · rw [h]
    exact hx
  · rw [h]; rfl
  · rw [h]; rfl

/-- **The image of the cell body of a covered printed body with carry chains does not name
    the stack pointer**: for a body in the class `printedAddrWB` whose cell body is in the
    image class `physImgB`, at a slot map whose array names pass `rspFreeNameB`, the image
    of the cell body passes the check `spFreeBodyB` of `RSP`. -/
theorem cellImage_spFreeBodyB {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hp : printedAddrWB body = true)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hsl : ∀ q A n, slotArr q = some (A, n) → rspFreeNameB A = true) :
    spFreeBodyB "RSP" (virtImg slotArr (cellBody slotArr body)) = true := by
  refine List.all_eq_true.mpr fun i hi => spFreeB_of_stackFreeB (stackFreeB_of_rspFreeB
    (virtImg_rspFree (fun k j' hk hlt => ?_) hphys hsl i hi))
  rw [cellBody_getElem?] at hk
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hk
  rw [cellBody_length] at hlt
  exact rspFree_cellMove (rspFree_of_instrOKWB (instrOKWB_of_printedAddrWB hp hj hlt)) hsl

/-- **The image of the cell body of a covered printed body with carry chains contains no
    call and no return**, at every slot map. -/
theorem cellImage_noCall (slotArr : String → Option (String × Nat)) {body : Lcmd}
    (hp : printedAddrWB body = true) :
    ((virtImg slotArr (cellBody slotArr body)).all fun i => !isCall i.fst) = true := by
  refine virtImg_noCall_of fun k j' hk hlt => ?_
  rw [cellBody_getElem?] at hk
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hk
  rw [cellBody_length] at hlt
  exact isCall_cellMove (isCall_of_instrOKWB (instrOKWB_of_printedAddrWB hp hj hlt))

/-! ## 3. The slot maps of the cell routes -/

/-- A name an instruction that passes `RspFreeUpToStore` reads passes `rspFreeNameB`. -/
theorem rspFreeNameB_of_read {x : LinstrR} (hx : RspFreeUpToStore x) {r : String}
    (hr : r ∈ (rdWr x).1) : rspFreeNameB r = true := by
  rcases hx with hf | ⟨d, b, i, v, rfl, hb, hi, hv⟩
  · have hn : ∀ r ∈ operandNames x, rspFreeNameB r = true := by simpa [rspFreeB] using hf
    exact hn r (rdWr_sub hr)
  · simp [rdWr, opNames] at hr
    rcases hr with rfl | rfl | rfl <;> assumption

/-- **A name an instruction of the image of a covered printed body with carry chains reads
    passes `rspFreeNameB`**, at a slot map whose array names pass it. -/
theorem rspFreeNameB_of_read_virtImg {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hp : printedAddrWB body = true)
    (hsl : ∀ q A n, slotArr q = some (A, n) → rspFreeNameB A = true) {i : LinstrRM}
    (hi : i ∈ virtImg slotArr body) {r : String} (hr : r ∈ (rdWr i.fst).1) :
    rspFreeNameB r = true := by
  obtain ⟨k, j, hk, hlt, rfl⟩ := mem_virtImg_lt hi
  rcases read_imgInstr hr with h | ⟨q, n, hq⟩ | ⟨_, _, _, j', i', -, hj', hb', hr'⟩
  · exact rspFreeNameB_of_read (rspFree_of_instrOKWB (instrOKWB_of_printedAddrWB hp hk hlt)) h
  · exact hsl q r n hq
  · exact rspFreeNameB_of_read
      (rspFree_of_instrOKWB (instrOKWB_of_printedAddrWB hp hb' (by omega))) hr'

/-- Every array name of the slot map of a layout passes `rspFreeNameB`: it is an argument
    name. -/
theorem rspFreeNameB_slotArrOf {σ : AbiLayout} {nm : String → String} {q A : String} {n : Nat}
    (h : slotArrOf σ nm q = some (A, n)) : rspFreeNameB A = true := by
  obtain ⟨j, a, -, -, rfl, -⟩ := slotArrOf_some h
  exact rspFreeNameB_argName j

/-- **Every array name of the slot map of a loop with carry chains and cells passes
    `rspFreeNameB`**: for a covered printed body with carry chains, an array name of the
    slot map `slotR` at the renaming synthesised against the image of the body is an
    argument name or a name that an instruction of that image reads. -/
theorem rspFreeNameB_slotR_synthRen {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {src : List LinstrRM} {k0 : Nat} (hp : printedAddrWB body = true) {q A : String} {n : Nat}
    (h : slotR σ nm (synthRen src (virtImg (slotArrOf σ nm) body) k0) q = some (A, n)) :
    rspFreeNameB A = true := by
  obtain ⟨m, h1, -⟩ := slotArrC_some h
  obtain ⟨A0, h0, rfl⟩ := slotRen_some h1
  rcases renOf_cases (synthRen src (virtImg (slotArrOf σ nm) body) k0) A0 with
    he | ⟨p, hp', -, he⟩
  · rw [he]
    exact rspFreeNameB_slotArrOf h0
  · rw [he]
    obtain ⟨i, hi, hr⟩ := synthRen_target_mem hp'
    exact rspFreeNameB_of_read_virtImg hp (fun _ _ _ => rspFreeNameB_slotArrOf) hi hr

end CatCrypt.Crypto.SecureCompilation.Haxc
