/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW

@[expose] public section

set_option autoImplicit false

/-!
# Cell accesses on the image route

A printed straight body accesses a word array at a constant index through a cell name
`mem.B.off` of a pointer register `B` reloaded from the slot of an array `A`
(`JasminLsemAddrMem.cellA?`). This module simulates such a body with the image machinery
of `ImageAddrSim`, unchanged, run on the cell body `cellBody`: the body with each cell
access rewritten to the frame-word move `MOVQ D, memName A off` or `MOVQ memName A off, S`,
under a frame map that gives the cell name `memName A off` the address of the word. On the
address machine the cell access and the frame-word move address the same word when `B`
holds the pointer of `A` (`stepA_cellBody`).

## Main definitions

* `cellMove`, `cellBody`: the frame-word move of a cell access, and the cell body.

## Main results

* `cellBody_getElem?`, `accArr_cellBody`: the cell body position by position.
* `tagAt_cellBody`: the tag of the address machine at a position is that of the cell body.
* `stepA_cellBody`: at a cell access whose base holds the pointer of its array, the address
  machine steps the body as the cell body.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg accArr imgInstr
  reloadOf reloadOf_succ_some reloadOf_succ_lopn reloadOf_succ_none_eq dstHitB bitStore?
  bitStore?_of_ne bitStore?_of_bitStoreB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (LoadSafeAt)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (read64 write64)

/-! ## 1. The cell body -/

/-- The frame-word move of the cell access `i` at position `k` of `body`: the load
    `MOVQ D, memName A off` or the store `MOVQ memName A off, S`, with `A` the array whose
    pointer the base register holds there (`accArr`); every other instruction, the address
    `LEA:64 d, mem.B.off` of a cell among them, itself. -/
def cellMove (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) (i : Linstr) :
    Linstr :=
  match cellA? i.li_i with
  | some (.ld D B off) =>
      match accArr slotArr body k B with
      | some (A, _) => ⟨i.li_ii, .Lopn [.reg D] "MOVQ" [.reg (memName A off)]⟩
      | none => i
  | some (.st B off S) =>
      match accArr slotArr body k B with
      | some (A, _) => ⟨i.li_ii, .Lopn [.reg (memName A off)] "MOVQ" [.reg S]⟩
      | none => i
  | _ => i

/-- **The cell body**: every cell access replaced by its frame-word move. -/
def cellBody (slotArr : String → Option (String × Nat)) (body : Lcmd) : Lcmd :=
  body.mapIdx (cellMove slotArr body)

theorem cellBody_getElem? (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) :
    (cellBody slotArr body)[k]? = (body[k]?).map (cellMove slotArr body k) := by
  simp [cellBody, List.getElem?_mapIdx]

theorem cellBody_length (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    (cellBody slotArr body).length = body.length := by
  simp [cellBody]

theorem cellMove_of_none {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : Linstr} (h : cellA? i.li_i = none) : cellMove slotArr body k i = i := by
  simp [cellMove, h]

theorem cellMove_of_lea {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : Linstr} {D B : String} {off : Nat} (h : cellA? i.li_i = some (.lea D B off)) :
    cellMove slotArr body k i = i := by
  simp [cellMove, h]

theorem cellA_some {x : LinstrR} {c : CellOp} (h : cellA? x = some c) :
    ∃ d o n, x = .Lopn [.reg d] o [.reg n] ∧
      (o = "LOAD:64" ∨ o = "STORE:64" ∨ o = "LEA:64") := by
  unfold cellA? at h
  split at h
  · rename_i d o n
    split at h
    · exact ⟨d, o, n, rfl, Or.inl (by assumption)⟩
    · split at h
      · exact ⟨d, o, n, rfl, Or.inr (Or.inl (by assumption))⟩
      · split at h
        · exact ⟨d, o, n, rfl, Or.inr (Or.inr (by assumption))⟩
        · cases h
  · cases h

theorem slotMov_cell {x : LinstrR} {c : CellOp} (h : cellA? x = some c) : slotMov? x = none := by
  obtain ⟨d, o, n, rfl, ho⟩ := cellA_some h
  rcases ho with rfl | rfl | rfl <;> simp [slotMov?]

/-- The slot moves of the cell body name no array slot: each frame-word move of a cell has
    no array-slot operand. -/
def CellNoSlot (slotArr : String → Option (String × Nat)) (body : Lcmd) : Prop :=
  ∀ k i d q, body[k]? = some i → slotMov? (cellMove slotArr body k i).li_i = some (d, q) →
    cellA? i.li_i ≠ none → slotArr d = none ∧ slotArr q = none

theorem cellA_ld {x : LinstrR} {D B : String} {off : Nat} (h : cellA? x = some (.ld D B off)) :
    ∃ n, x = .Lopn [.reg D] "LOAD:64" [.reg n] ∧ cellParts? n = some (B, off) := by
  unfold cellA? at h
  split at h
  · rename_i d o n
    split at h
    · rename_i ho
      subst ho
      obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact ⟨n, rfl, hp⟩
    · split_ifs at h
      all_goals obtain ⟨p, -, he⟩ := Option.map_eq_some_iff.mp h
      all_goals cases he
  · cases h

theorem cellA_st {x : LinstrR} {B S : String} {off : Nat} (h : cellA? x = some (.st B off S)) :
    ∃ n, x = .Lopn [.reg n] "STORE:64" [.reg S] ∧ cellParts? n = some (B, off) := by
  unfold cellA? at h
  split at h
  · rename_i d o n
    split at h
    · obtain ⟨p, -, he⟩ := Option.map_eq_some_iff.mp h
      cases he
    · split at h
      · rename_i _ ho
        subst ho
        obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact ⟨d, rfl, hp⟩
      · split_ifs at h
        obtain ⟨p, -, he⟩ := Option.map_eq_some_iff.mp h
        cases he
  · cases h

theorem cellA_lea {x : LinstrR} {D B : String} {off : Nat}
    (h : cellA? x = some (.lea D B off)) :
    ∃ n, x = .Lopn [.reg D] "LEA:64" [.reg n] ∧ cellParts? n = some (B, off) := by
  unfold cellA? at h
  split at h
  · rename_i d o n
    split_ifs at h with h1 h2 h3
    · obtain ⟨p, -, he⟩ := Option.map_eq_some_iff.mp h
      cases he
    · obtain ⟨p, -, he⟩ := Option.map_eq_some_iff.mp h
      cases he
    · subst h3
      obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact ⟨n, rfl, hp⟩
  · cases h

theorem hasPrefix_memName (A : String) (off : Nat) : hasPrefix (memName A off) "mem." = true := by
  simp [hasPrefix, memName, List.isPrefixOf]

theorem hasPrefix_of_cellParts {n : String} {p : String × Nat} (h : cellParts? n = some p) :
    hasPrefix n "mem." = true := by
  unfold cellParts? at h
  split at h
  · assumption
  · cases h

/-- A general-purpose name is no cell name. -/
theorem hasPrefix_gpName {r : String} (h : JasminLsemAddrImage.gpNameB r = true) :
    hasPrefix r "mem." = false := by
  simp only [JasminLsemAddrImage.gpNameB, List.contains_iff_mem, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

/-- A reload that the body shows, of a name that is no cell name, is one the cell body
    shows: the scan passes the frame-word move of a cell access exactly where it passes the
    access, since the move writes the access's destination register or a cell name that is
    no array slot (`CellNoSlot`). -/
theorem reloadOf_cellBody {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hN : CellNoSlot slotArr body) {q : String} :
    ∀ {k : Nat} {b : String}, hasPrefix b "mem." = false → reloadOf slotArr body k b = some q →
      reloadOf slotArr (cellBody slotArr body) k b = some q
  | 0, _, _, h => by cases h
  | k + 1, b, hpb, h => by
      cases hbk : body[k]? with
      | none => simp [reloadOf, hbk] at h
      | some j =>
          have hb' : (cellBody slotArr body)[k]? = some (cellMove slotArr body k j) := by
            rw [cellBody_getElem?, hbk]; rfl
          cases hm : slotMov? j.li_i with
          | some p =>
              obtain ⟨d, q0⟩ := p
              have hc : cellA? j.li_i = none := by
                cases hc : cellA? j.li_i with
                | none => rfl
                | some c => rw [slotMov_cell hc] at hm; cases hm
              rw [cellMove_of_none hc] at hb'
              rw [reloadOf_succ_some hbk hm] at h
              rw [reloadOf_succ_some hb' hm]
              split_ifs at h ⊢ with h1 h3 h2
              · simp only [Bool.and_eq_true] at h3
                exact reloadOf_cellBody hN (hasPrefix_gpName h3.2) h
              · exact h
              · exact reloadOf_cellBody hN hpb h
          | none =>
              obtain ⟨ds, o, ss, hx, hnd, h'⟩ := reloadOf_succ_none_eq hbk hm b h
              have hIH := reloadOf_cellBody hN hpb h'
              cases hc : cellA? j.li_i with
              | none =>
                  rw [cellMove_of_none hc] at hb'
                  rw [reloadOf_succ_lopn hb' hm hx, hnd]
                  exact hIH
              | some c =>
                  cases c with
                  | ld D B off =>
                      obtain ⟨n, hxn, -⟩ := cellA_ld hc
                      rw [hxn] at hx
                      obtain ⟨rfl, -, -⟩ := LinstrR.Lopn.inj hx
                      simp only [List.any_cons, List.any_nil, Bool.or_false, dstHitB,
                        Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hnd
                      cases hacc : accArr slotArr body k B with
                      | some Am =>
                        obtain ⟨A, m⟩ := Am
                        have hmv : cellMove slotArr body k j
                            = ⟨j.li_ii, .Lopn [.reg D] "MOVQ" [.reg (memName A off)]⟩ := by
                          simp only [cellMove, hc, hacc]
                        rw [hmv] at hb'
                        have hm' : slotMov? (LinstrR.Lopn [.reg D] "MOVQ" [.reg (memName A off)])
                            = some (D, memName A off) := by simp [slotMov?]
                        rw [reloadOf_succ_some hb' hm', if_neg hnd.1,
                          if_pos (by simpa using hnd.2)]
                        exact hIH
                      | none =>
                        have hmv : cellMove slotArr body k j = j := by
                          simp only [cellMove, hc, hacc]
                        rw [hmv] at hb'
                        rw [reloadOf_succ_lopn hb' hm hxn]
                        simp only [List.any_cons, List.any_nil, Bool.or_false, dstHitB,
                          hnd.2, beq_iff_eq, hnd.1, if_false]
                        exact hIH
                  | st B off S =>
                      obtain ⟨n, hxn, -⟩ := cellA_st hc
                      cases hacc : accArr slotArr body k B with
                      | some Am =>
                        obtain ⟨A, m⟩ := Am
                        have hmv : cellMove slotArr body k j
                            = ⟨j.li_ii, .Lopn [.reg (memName A off)] "MOVQ" [.reg S]⟩ := by
                          simp only [cellMove, hc, hacc]
                        rw [hmv] at hb'
                        have hm' : slotMov? (LinstrR.Lopn [.reg (memName A off)] "MOVQ" [.reg S])
                            = some (memName A off, S) := by simp [slotMov?]
                        have hsl := (hN k j (memName A off) S hbk (by rw [hmv]; exact hm')
                          (by rw [hc]; simp)).1
                        have hne : memName A off ≠ b := fun e => by
                          rw [← e, hasPrefix_memName] at hpb; cases hpb
                        rw [reloadOf_succ_some hb' hm', if_neg hne, if_pos (by simp [hsl])]
                        exact hIH
                      | none =>
                        have hmv : cellMove slotArr body k j = j := by
                          simp only [cellMove, hc, hacc]
                        rw [hmv] at hb'
                        rw [reloadOf_succ_lopn hb' hm hx, hnd]
                        exact hIH
                  | lea D B off =>
                      rw [cellMove_of_lea hc] at hb'
                      rw [reloadOf_succ_lopn hb' hm hx, hnd]
                      exact hIH

/-- The array of an access in the body, through a name that is no cell name, is its array in
    the cell body. -/
theorem accArr_cellBody {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hN : CellNoSlot slotArr body) {k : Nat} {b : String} (hpb : hasPrefix b "mem." = false)
    {p : String × Nat} (h : accArr slotArr body k b = some p) :
    accArr slotArr (cellBody slotArr body) k b = some p := by
  unfold accArr at h ⊢
  obtain ⟨q, hr, hq⟩ := Option.bind_eq_some_iff.mp h
  rw [reloadOf_cellBody hN hpb hr]
  exact hq

/-- The frame-word move of an instruction names a name that is no cell name exactly where the
    instruction does, and reads it as a carry-in exactly where the instruction does. -/
theorem cellMove_names (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {d : String} (hd : hasPrefix d "mem." = false) (i : Linstr) :
    namesB d (cellMove slotArr body k i).li_i = namesB d i.li_i
      ∧ carryUseB d (cellMove slotArr body k i).li_i = carryUseB d i.li_i := by
  unfold cellMove
  split
  · rename_i D B off hc
    obtain ⟨nm, hx, hn⟩ := cellA_ld hc
    have hnd : nm ≠ d := fun e => by rw [← e, hasPrefix_of_cellParts hn] at hd; cases hd
    split
    · rename_i A _ _
      have hmd : memName A off ≠ d := fun e => by rw [← e, hasPrefix_memName] at hd; cases hd
      simp [hx, namesB, opNamesB, carryUseB, beq_eq_false_iff_ne.2 hnd,
        beq_eq_false_iff_ne.2 hmd]
    · exact ⟨rfl, rfl⟩
  · rename_i B off S hc
    obtain ⟨nm, hx, hn⟩ := cellA_st hc
    have hnd : nm ≠ d := fun e => by rw [← e, hasPrefix_of_cellParts hn] at hd; cases hd
    split
    · rename_i A _ _
      have hmd : memName A off ≠ d := fun e => by rw [← e, hasPrefix_memName] at hd; cases hd
      simp [hx, namesB, opNamesB, carryUseB, beq_eq_false_iff_ne.2 hnd,
        beq_eq_false_iff_ne.2 hmd]
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- The tag of an instruction at a position is the same in the body and in the cell body. -/
theorem tagAt_cellBody (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (x : LinstrR) : tagAt (cellBody slotArr body) k x = tagAt body k x := by
  have hb : bitMovB (cellBody slotArr body) k x = bitMovB body k x := by
    unfold bitMovB
    split
    · rename_i d n _
      cases hd : hasPrefix d "mem."
      · have hc : carryInNext (cellBody slotArr body) k d = carryInNext body k d := by
          unfold carryInNext
          apply carryInFirst_congr
          · simp [cellBody_length]
          · intro i h h'
            simp only [List.getElem_drop, cellBody, List.getElem_mapIdx]
            exact cellMove_names slotArr body _ hd _
        rw [hc]
      · simp
    · rfl
  simp [tagAt, hb]

/-- **A cell load on the address machine is its frame-word move** when its base holds the
    pointer `p` of its array and the cell name has the address `p + off`. -/
theorem stepA_cellBody_ld {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {sa : LstateA} {zf : Bool}
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {D B : String} {off : Nat}
    (hc : cellA? bi.li_i = some (.ld D B off)) {A : String} {n : Nat}
    (hacc : accArr slotArr body sa.reg.lpc B = some (A, n)) {p : BitVec 64}
    (hp : sa.reg.getW B 64 = some p)
    (hfr : frame (memName A off) = some (p + BitVec.ofNat 64 off)) :
    stepA frame body sa zf = stepA frame (cellBody slotArr body) sa zf := by
  obtain ⟨nm, hx, hn⟩ := cellA_ld hc
  have hb2 : (cellBody slotArr body)[sa.reg.lpc]?
      = some ⟨bi.li_ii, .Lopn [.reg D] "MOVQ" [.reg (memName A off)]⟩ := by
    rw [cellBody_getElem?, hb]
    simp [cellMove, hc, hacc]
  rw [stepA_lopn frame hb hx, stepA_lopn frame hb2 rfl, hx]
  have h1 : normA (.Lopn [.reg D] "LOAD:64" [.reg nm]) = .Lopn [.reg D] "LOAD:64" [.reg nm] := by
    simp [normA]
  have h2 : tagAt body sa.reg.lpc (.Lopn [.reg D] "LOAD:64" [.reg nm]) = .reg none := by
    rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?])]; simp [tagA]
  have h3 : normA (.Lopn [.reg D] "MOVQ" [.reg (memName A off)])
      = .Lopn [.reg D] "MOVQ" [.reg (memName A off)] := by simp [normA]
  have h4 : tagAt (cellBody slotArr body) sa.reg.lpc
      (.Lopn [.reg D] "MOVQ" [.reg (memName A off)]) = .reg none := by
    rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?])]; simp [tagA]
  rw [h1, h2, h3, h4, fstepA_ldm frame hn hp,
    fstepA_slotLoad frame (d := D) (q := memName A off) (by simp [slotMov?]) hfr]

/-- **A cell store on the address machine is its frame-word move** when its base holds the
    pointer `p` of its array, the cell name has the address `p + off`, and the stored
    register has no frame word. -/
theorem stepA_cellBody_st {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {sa : LstateA} {zf : Bool}
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {B S : String} {off : Nat}
    (hc : cellA? bi.li_i = some (.st B off S)) {A : String} {n : Nat}
    (hacc : accArr slotArr body sa.reg.lpc B = some (A, n)) {p : BitVec 64}
    (hp : sa.reg.getW B 64 = some p)
    (hfr : frame (memName A off) = some (p + BitVec.ofNat 64 off)) (hS : frame S = none) :
    stepA frame body sa zf = stepA frame (cellBody slotArr body) sa zf := by
  obtain ⟨nm, hx, hn⟩ := cellA_st hc
  have hb2 : (cellBody slotArr body)[sa.reg.lpc]?
      = some ⟨bi.li_ii, .Lopn [.reg (memName A off)] "MOVQ" [.reg S]⟩ := by
    rw [cellBody_getElem?, hb]
    simp [cellMove, hc, hacc]
  rw [stepA_lopn frame hb hx, stepA_lopn frame hb2 rfl, hx]
  have h1 : normA (.Lopn [.reg nm] "STORE:64" [.reg S]) = .Lopn [.reg nm] "STORE:64" [.reg S] := by
    simp [normA]
  have h2 : tagAt body sa.reg.lpc (.Lopn [.reg nm] "STORE:64" [.reg S]) = .reg none := by
    rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?])]; simp [tagA]
  have h3 : normA (.Lopn [.reg (memName A off)] "MOVQ" [.reg S])
      = .Lopn [.reg (memName A off)] "MOVQ" [.reg S] := by simp [normA]
  have h4 : tagAt (cellBody slotArr body) sa.reg.lpc
      (.Lopn [.reg (memName A off)] "MOVQ" [.reg S]) = .reg none := by
    rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?])]; simp [tagA]
  rw [h1, h2, h3, h4]
  cases hv : sa.reg.getW S 64 with
  | some v =>
      rw [fstepA_stm frame hn hp hv, fstepA_slotStore frame (by simp [slotMov?]) hS hfr sa zf hv]
  | none =>
      simp [fstepA, slotMov?, slotCmp?, cellA?, hn, hp, hv, hfr, hS]

theorem cellMove_lret {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : Linstr} : (cellMove slotArr body k i).li_i = .Lret ↔ i.li_i = .Lret := by
  unfold cellMove
  cases hc : cellA? i.li_i with
  | none => rfl
  | some c =>
      obtain ⟨d, o, n, hx, -⟩ := cellA_some hc
      cases c with
      | ld D B off =>
          simp only
          split <;> simp [hx]
      | st B off S =>
          simp only
          split <;> simp [hx]
      | lea D B off => rfl

theorem haltedA_cellBody (slotArr : String → Option (String × Nat)) (body : Lcmd)
    (sa : LstateA) : haltedA (cellBody slotArr body) sa = haltedA body sa := by
  unfold haltedA
  rw [cellBody_getElem?]
  cases hb : body[sa.reg.lpc]? with
  | none => rfl
  | some bi =>
      simp only [Option.map_some]
      have h := cellMove_lret (slotArr := slotArr) (body := body) (k := sa.reg.lpc) (i := bi)
      generalize cellMove slotArr body sa.reg.lpc bi = bj at h
      obtain ⟨ii, li⟩ := bi
      obtain ⟨jj, lj⟩ := bj
      simp only at h
      by_cases hr : li = .Lret
      · subst hr
        rw [h.mpr rfl]
      · have hr' : lj ≠ .Lret := fun e => hr (h.mp e)
        cases li <;> cases lj <;> simp_all

theorem loadSafeAt_cellBody (slotArr : String → Option (String × Nat)) (rsp : BitVec 64)
    (body : Lcmd) (sa : LstateA) :
    LoadSafeAt rsp (cellBody slotArr body) sa ↔ LoadSafeAt rsp body sa := by
  unfold LoadSafeAt
  rw [cellBody_getElem?]
  cases hb : body[sa.reg.lpc]? with
  | none => simp
  | some bi =>
      simp only [Option.map_some]
      cases hc : cellA? bi.li_i with
      | none => rw [cellMove_of_none hc]
      | some c =>
          obtain ⟨d, o, n, hx, ho⟩ := cellA_some hc
          have hn1 : ∀ ii D B I, bi ≠ ⟨ii, .Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]⟩ := by
            intro ii D B I he
            subst he
            simp at hx
          have hn2 : ∀ ii D B I, cellMove slotArr body sa.reg.lpc bi
              ≠ ⟨ii, .Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]⟩ := by
            intro ii D B I he
            unfold cellMove at he
            rw [hc] at he
            cases c with
            | ld D' B' off =>
                simp only at he
                split at he
                · simp at he
                · exact hn1 ii D B I he
            | st B' off S =>
                simp only at he
                split at he
                · simp at he
                · exact hn1 ii D B I he
            | lea D' B' off => exact hn1 ii D B I he
          constructor
          · intro _ ii D B I h
            exact absurd (Option.some.inj h) (hn1 ii D B I)
          · intro _ ii D B I h
            exact absurd (Option.some.inj h) (hn2 ii D B I)

/-- **An instruction that the cell body keeps steps alike in the body and the cell body**,
    when it is no conditional branch. -/
theorem stepA_cellBody_of_fix {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {sa : LstateA} {zf : Bool}
    {b0 : Linstr} (hb0 : body[sa.reg.lpc]? = some b0)
    (hfix : cellMove slotArr body sa.reg.lpc b0 = b0)
    (hnc : ∀ cc l, b0.li_i ≠ .Lcond cc l) :
    stepA frame body sa zf = stepA frame (cellBody slotArr body) sa zf := by
  have hbC : (cellBody slotArr body)[sa.reg.lpc]? = some b0 := by
    rw [cellBody_getElem?, hb0, Option.map_some, hfix]
  unfold stepA
  rw [hbC, hb0]
  obtain ⟨ii, li⟩ := b0
  cases li with
  | Lcond c l => exact absurd rfl (hnc c l)
  | _ => simp only [tagAt_cellBody]

/-! ## 2. One step of a straight body -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (evalInstrPMemFk)

/-- **One step of the image of a straight body.** At a position that is no conditional
    branch, a checked step of the image instruction of a body that passes the gate is matched
    by one step of the address machine. The cases of `ImageAddrSim.img_step` without the
    branch. -/
theorem img_stepStraight {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : JasminLsemAddrImage.physImgB slotArr c = true)
    (hgate : imgGateB frame slotArr c = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRel frame slotArr base c s sa s.zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hnc : ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    haltedA c sa = false ∧ LoadSafeAt rsp c sa
      ∧ ∃ sa1, stepA frame c sa s.zf = some (sa1, t.zf)
        ∧ ImgRel frame slotArr base c t sa1 t.zf := by
  have hg : instrGateB frame slotArr c sa.reg.lpc bi.li_i = true := by
    simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  unfold instrGateB at hg
  cases hc : icase frame bi.li_i with
  | other => rw [hc] at hg; cases hg
  | cond cc l => exact absurd (icase_cond hc) (hnc _ _)
  | label =>
      obtain ⟨ii, l, hx⟩ := icase_label hc
      have hi : imgInstr slotArr c sa.reg.lpc bi.li_i = (bi.li_i, .reg none) := by
        rw [hx]; rfl
      rw [hi, evalInstrPMemFk_reg, hx, eval_label] at hstep
      cases hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp),
        sa.setLpc (sa.reg.lpc + 1), ?_, rel_label hphys hrel hb (by rw [hx]; rfl)⟩
      obtain ⟨ii0, li⟩ := bi
      simp only at hx
      subst hx
      simp [stepA, hb]
  | ldx d b idx =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
      obtain ⟨⟨⟨⟨⟨An, hacc⟩, hgd⟩, hd⟩, hidx⟩, hbf⟩ := hg
      obtain ⟨A, n⟩ := An
      have hx := icase_ldx hc
      rw [hx, imgInstr_ldx slotArr _ _ hacc] at hstep
      obtain ⟨hsafe, sa', hst, hr⟩ :=
        rel_ldx hsep hphys (.of_imgGateB hgate) P hrel hb hx hacc hgd hd hidx hbf hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
      rw [stepA_lopn frame hb hx, ← hst, hx]
      rfl
  | stx d b idx v =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
      obtain ⟨⟨⟨⟨An, hacc⟩, hidx⟩, hbf⟩, hv⟩ := hg
      obtain ⟨A, n⟩ := An
      have hx := icase_stx hc
      rw [hx, imgInstr_stx slotArr _ _ hacc] at hstep
      obtain ⟨sa', hst, hr⟩ := rel_stx hsep hphys (.of_imgGateB hgate) P hrel hb hx hacc hidx hbf hv hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), sa', ?_, hr⟩
      rw [stepA_lopn frame hb hx, ← hst, hx]
      rfl
  | sload d q =>
      rw [hc] at hg
      have hm := (icase_sload hc).1
      have hsafe := loadSafe_of (rsp := rsp) hb
        (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
      have h3 : bitMovB c sa.reg.lpc bi.li_i = false := bitMovB_of_slotMov hm
      have h4 : bitStore? c sa.reg.lpc bi.li_i = none := bitStore?_of_slotMov hm
      rcases slotMov?_cases hm with hx | hx <;>
      · rw [hx] at h3 h4
        rw [hx, imgInstr_reg slotArr _ _ (by decide) (by decide) (by decide) h3 h4, evalInstrPMemFk_reg,
          ← hx] at hstep
        obtain ⟨sa', hst, hr⟩ := rel_sload hsep hphys P hrel hb hc hg hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
        rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg (by decide) (by decide) (by decide) h3]
  | sstore q S =>
      rw [hc] at hg
      have hm := (icase_sstore hc).1
      have hsafe := loadSafe_of (rsp := rsp) hb
        (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
      have h3 : bitMovB c sa.reg.lpc bi.li_i = false := bitMovB_of_slotMov hm
      have h4 : bitStore? c sa.reg.lpc bi.li_i = none := bitStore?_of_slotMov hm
      rcases slotMov?_cases hm with hx | hx <;>
      · rw [hx] at h3 h4
        rw [hx, imgInstr_reg slotArr _ _ (by decide) (by decide) (by decide) h3 h4, evalInstrPMemFk_reg,
          ← hx] at hstep
        obtain ⟨sa', hst, hr⟩ := rel_sstore hsep hphys P hrel hb hc hg hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
        rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg (by decide) (by decide) (by decide) h3]
  | scmp d y q =>
      rw [hc] at hg
      have hx := slotCmp?_eq (icase_scmp hc).1
      have hsafe := loadSafe_of (rsp := rsp) hb
        (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
      have h3 : bitMovB c sa.reg.lpc (.Lopn [.reg d] "CMP:64" [.reg y, .reg q]) = false :=
        bitMovB_of_ne (by simp [JasminLsemCast.movImmStruct?])
      rw [hx, imgInstr_reg slotArr _ _ (by decide) (by decide) (by decide) h3
        (bitStore?_of_ne (by simp)), evalInstrPMemFk_reg, ← hx] at hstep
      obtain ⟨sa', hst, hr⟩ := rel_scmp hphys P hrel hb hc (by simpa using hg) hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
      rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg (by decide) (by decide) (by decide) h3]
  | reg =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      obtain ⟨⟨hg, h3⟩, h4⟩ := hg
      obtain ⟨ds, o, ss, hx, ho1, ho2, hko⟩ := icase_reg hc
      have hsafe := loadSafe_of (rsp := rsp) hb
        (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
      rw [hx] at h3 h4
      rw [hx, imgInstr_reg slotArr _ _ ho1 ho2 hko h3 (bitStore?_of_bitStoreB h4),
        evalInstrPMemFk_reg, ← hx] at hstep
      obtain ⟨sa', hst, hr⟩ := rel_reg hsep hphys (.of_imgGateB hgate) P hrel hb hc hg hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
      rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg ho1 ho2 hko h3]

/-! ## 3. The run of a straight body with cells -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (SafeW WideSafeAt
  CellSafeAt)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (Disjoint8)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (findInstrMem_single)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next)

/-- **The cell accesses of a body have their arrays and frame words**: the base register of
    each cell access is reloaded from the slot of an array `A` (`accArr`) and has no frame
    word, the cell name `memName A off` has the frame word `base A + off`, a loaded word is
    disjoint from the red-zone word, a stored register has no frame word, and the base
    register is a general-purpose name. -/
structure CellFrames (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (body : Lcmd) : Prop where
  ld : ∀ k bi D B off, body[k]? = some bi → cellA? bi.li_i = some (.ld D B off) →
    ∃ A n, accArr slotArr body k B = some (A, n) ∧ frame B = none
      ∧ frame (memName A off) = some (base A + BitVec.ofNat 64 off)
      ∧ Disjoint8 (redW rsp) (base A + BitVec.ofNat 64 off)
  st : ∀ k bi B off S, body[k]? = some bi → cellA? bi.li_i = some (.st B off S) →
    ∃ A n, accArr slotArr body k B = some (A, n) ∧ frame B = none ∧ frame S = none
      ∧ frame (memName A off) = some (base A + BitVec.ofNat 64 off)
  ldGp : ∀ (k : Nat) (bi : Linstr) D B off, body[k]? = some bi →
    cellA? bi.li_i = some (.ld D B off) → DecodePrinted.gpOk B = true
  stGp : ∀ (k : Nat) (bi : Linstr) B off S, body[k]? = some bi →
    cellA? bi.li_i = some (.st B off S) → DecodePrinted.gpOk B = true

/-- **One step of a straight body with cells through its cell body.** -/
theorem cell_step {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : JasminLsemAddrImage.physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateB frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (hnc : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) s sa s.zf) {bi : Linstr}
    (hb : (cellBody slotArr body)[sa.reg.lpc]? = some bi)
    (hlt : sa.reg.lpc < (cellBody slotArr body).length - 1)
    (hstep : evalInstrPMemFk true P
      (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s = some t) :
    haltedA body sa = false ∧ SafeW rsp body sa
      ∧ ∃ sa1, stepA frame body sa s.zf = some (sa1, t.zf)
        ∧ ImgRel frame slotArr base (cellBody slotArr body) t sa1 t.zf := by
  rw [cellBody_getElem?] at hb
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hnc' : ∀ cc l, (cellMove slotArr body sa.reg.lpc b0).li_i ≠ .Lcond cc l := by
    intro cc l he
    unfold cellMove at he
    split at he
    · split at he
      · cases he
      · exact hnc _ _ hb0 cc l he
    · split at he
      · cases he
      · exact hnc _ _ hb0 cc l he
    · exact hnc _ _ hb0 cc l he
  have hbC : (cellBody slotArr body)[sa.reg.lpc]? = some (cellMove slotArr body sa.reg.lpc b0) := by
    rw [cellBody_getElem?, hb0]; rfl
  obtain ⟨hh, hsafe, sa1, hst, hr⟩ :=
    img_stepStraight hsep hphys hgate P hrel hbC hlt hnc' hstep
  have hwide : WideSafeAt body sa := by
    intro ii ds o ss _ r _ hr _ _
    exact hrel.wid r hr
  refine ⟨by rw [← haltedA_cellBody slotArr]; exact hh, ⟨(loadSafeAt_cellBody slotArr rsp body sa).mp hsafe,
    hwide, ?_⟩, sa1, ?_, hr⟩
  · intro ii D n B off p hbi hn hp
    rw [hb0] at hbi
    cases hbi
    have hc : cellA? (.Lopn [.reg D] "LOAD:64" [.reg n]) = some (.ld D B off) := by
      simp [cellA?, hn]
    obtain ⟨A, m, hacc, hBf, -, hred⟩ := hF.ld _ _ D B off hb0 hc
    obtain ⟨q, -, hpA⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel
      (accArr_cellBody hN (hasPrefix_gpName (hF.ldGp _ _ D B off hb0 hc)) hacc) hBf
    rw [hp] at hpA
    cases hpA
    exact hred
  · cases hc : cellA? b0.li_i with
    | none =>
        have he : stepA frame body sa s.zf = stepA frame (cellBody slotArr body) sa s.zf := by
          unfold stepA
          rw [hbC, hb0, cellMove_of_none hc]
          obtain ⟨ii, li⟩ := b0
          cases li with
          | Lcond c l =>
              exact absurd rfl (hnc _ _ hb0 c l)
          | _ => simp only [tagAt_cellBody]
        rw [he]
        exact hst
    | some op =>
        cases op with
        | ld D B off =>
            obtain ⟨A, m, hacc, hBf, hfr, -⟩ := hF.ld _ _ D B off hb0 hc
            obtain ⟨q, -, hpA⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel
              (accArr_cellBody hN (hasPrefix_gpName (hF.ldGp _ _ D B off hb0 hc)) hacc) hBf
            rw [stepA_cellBody_ld hb0 hc hacc hpA hfr]
            exact hst
        | st B off S =>
            obtain ⟨A, m, hacc, hBf, hSf, hfr⟩ := hF.st _ _ B off S hb0 hc
            obtain ⟨q, -, hpA⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel
              (accArr_cellBody hN (hasPrefix_gpName (hF.stGp _ _ B off S hb0 hc)) hacc) hBf
            rw [stepA_cellBody_st hb0 hc hacc hpA hfr hSf]
            exact hst
        | lea D B off =>
            rw [stepA_cellBody_of_fix hb0 (cellMove_of_lea hc) (hnc _ _ hb0)]
            exact hst

/-- **The image of the cell body simulated on the body.** For a straight body (no
    conditional branch) whose cell body passes the gate `imgGateB` and the class `physImgB`,
    whose cell moves name no array slot and whose cell accesses have their frame words, at a
    separation `ImgSep`: every halting checked run of the image of the cell body from a state
    related to an address state is matched by a halting run of the address machine on the
    body itself, whose final state is related to the final state of the image, and which is
    safe in the sense of `DecodePrintedAddrW.SafeW`. -/
theorem image_addr_simB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : JasminLsemAddrImage.physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateB frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (hnc : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (fn : String) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base (cellBody slotArr body) s sa zf →
      lsemFuelMemFk true (singletonProgM fn (JasminLsemAddrImage.virtImg slotArr
        (cellBody slotArr body))) fuel s = some t →
      ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
        ∧ ImgRel frame slotArr base (cellBody slotArr body) t sa' zf'
        ∧ RunSafe frame body (SafeW rsp body) fuel' sa zf := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hfn hrel hrun
      cases hf : JasminLsemMemLoop.findInstrMem (singletonProgM fn
          (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr body))) s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          have hh := haltedA_of_img (.of_imgGateB hgate) fn hfn hrel.pc hf
          rw [haltedA_cellBody] at hh
          exact ⟨0, sa, zf, runA_halt frame body 0 sa zf hh, hrel, trivial⟩
  | succ f ih =>
      intro s t sa zf hfn hrel hrun
      cases hf : JasminLsemMemLoop.findInstrMem (singletonProgM fn
          (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr body))) s.prog with
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          have hh := haltedA_of_img (.of_imgGateB hgate) fn hfn hrel.pc hf
          rw [haltedA_cellBody] at hh
          exact ⟨0, sa, zf, runA_halt frame body 0 sa zf hh, hrel, trivial⟩
      | some i =>
          simp only [lsemFuelMemFk, hf] at hrun
          cases he : evalInstrPMemFk true (singletonProgM fn
              (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr body))) i s with
          | none => rw [he] at hrun; cases hrun
          | some s1 =>
              rw [he] at hrun
              have hlfn : s1.prog.lfn = fn :=
                (evalInstrPMemF_next _ i s s1 (JasminLsemMemChecked.evalInstrPMemF_of_k he)).1.trans
                  hfn
              have hz := hrel.zf
              subst hz
              rw [findInstrMem_single hfn, JasminLsemAddrImage.virtImg_getElem?, ← hrel.pc,
                List.getElem?_dropLast] at hf
              split at hf
              case isFalse => cases hf
              rename_i hlt
              obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hf
              obtain ⟨hh, hsafe, sa1, hst, hr⟩ :=
                cell_step hsep hphys hgate hN hF hnc _ hrel hb hlt he
              obtain ⟨f', sa', zf', hr', hrel', hsafe'⟩ := ih s1 t sa1 s1.zf hlfn hr hrun
              refine ⟨f' + 1, sa', zf', ?_, hrel', hsafe, fun s' zf'' hs' => ?_⟩
              · rw [runA_step frame body f' sa s.zf hh, hst]
                exact hr'
              · rw [hst] at hs'
                cases hs'
                exact hsafe'

/-! ## 3b. The run of a straight body with cells and carry chains -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (ImgRelW imgGateBW img_stepW
  ptr_of_reloadW haltedA_of_imgW wideSafe_of_gateW)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (readsI srcNames cellBase
  readsRdx rdxShape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (carryIns classifyK
  narrowStep narrowIn narrowIn_zero narrowIn_succ narrowSrc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (width_of_getW)

/-- A cell access and its frame-word move are no width-carrying casts. -/
theorem classifyK_cellMove (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : Linstr) : classifyK (cellMove slotArr body k i).li_i = classifyK i.li_i := by
  cases hca : cellA? i.li_i with
  | none => rw [cellMove_of_none hca]
  | some op =>
    obtain ⟨d, o, n, hx, ho⟩ := cellA_some hca
    have h0 : classifyK i.li_i = none := by
      rw [hx]
      rcases ho with rfl | rfl | rfl <;>
        simp [classifyK, show LprogBytes.castMovBits "LOAD:64" = none from by decide,
          show LprogBytes.castMovBits "STORE:64" = none from by decide,
          show LprogBytes.castMovBits "LEA:64" = none from by decide]
    have hm : ∀ a b : String, classifyK (.Lopn [.reg a] "MOVQ" [.reg b]) = none := fun a b => by
      simp [classifyK, show LprogBytes.castMovBits "MOVQ" = none from by decide]
    rw [h0]
    unfold cellMove
    rw [hca]
    cases op <;> simp only <;> (try split) <;> first | exact h0 | exact hm _ _

/-- The cast width analysis of the cell body is that of the body. -/
theorem narrowIn_cellBody (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    ∀ k, narrowIn (cellBody slotArr body) k = narrowIn body k
  | 0 => by rw [narrowIn_zero, narrowIn_zero]
  | k + 1 => by
    cases hb : body[k]? with
    | none =>
      have hl : body.length ≤ k := by simpa using hb
      have h1 : narrowIn body (k + 1) = narrowIn body k := by
        unfold narrowIn
        rw [List.take_of_length_le (by omega), List.take_of_length_le hl]
      have h2 : narrowIn (cellBody slotArr body) (k + 1) = narrowIn (cellBody slotArr body) k := by
        unfold narrowIn
        rw [List.take_of_length_le (by rw [cellBody_length]; omega),
          List.take_of_length_le (by rw [cellBody_length]; exact hl)]
      rw [h1, h2, narrowIn_cellBody slotArr body k]
    | some bi =>
      have hc : (cellBody slotArr body)[k]? = some (cellMove slotArr body k bi) := by
        rw [cellBody_getElem?, hb]; rfl
      rw [narrowIn_succ hb, narrowIn_succ hc, narrowIn_cellBody slotArr body k]
      simp only [narrowStep, classifyK_cellMove]

/-- The cast source with an entry of the cast width analysis at a position of the cell body
    is that of the body. -/
theorem narrowSrc_cellBody (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) :
    narrowSrc (cellBody slotArr body) k = narrowSrc body k := by
  unfold narrowSrc
  rw [cellBody_getElem?]
  cases body[k]? <;>
    simp only [Option.map_none, Option.map_some, classifyK_cellMove, narrowIn_cellBody]

/-- **The width safety of a body from that of its cell body.** At a relation of the image
    simulation with carry chains on the cell body that passes `imgGateBW`, the body is width
    safe: the names a cell access reads beyond its frame-word move are the base register,
    which holds an array pointer, and the cell name, which is no general-purpose name. -/
theorem wideSafe_cellBody {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base (cellBody slotArr body) s sa zf) :
    WideSafeAt body sa := by
  have hW := wideSafe_of_gateW hgate hrel
  intro ii ds o ss hb r hr hg hc hn
  have hn' : r ∉ narrowSrc (cellBody slotArr body) sa.reg.lpc := by
    rw [narrowSrc_cellBody]; exact hn
  have hbC := cellBody_getElem? slotArr body sa.reg.lpc
  rw [hb, Option.map_some] at hbC
  cases hca : cellA? (LinstrR.Lopn ds o ss) with
  | none =>
      rw [cellMove_of_none (i := ⟨ii, .Lopn ds o ss⟩) hca] at hbC
      exact hW ii ds o ss hbC r hr hg hc hn'
  | some op =>
      cases op with
      | ld D B off =>
          obtain ⟨n, hx, hn⟩ := cellA_ld hca
          obtain ⟨A, m, hacc, hBf, -, -⟩ := hF.ld _ _ D B off hb hca
          have hmv : cellMove slotArr body sa.reg.lpc ⟨ii, .Lopn ds o ss⟩
              = ⟨ii, .Lopn [.reg D] "MOVQ" [.reg (memName A off)]⟩ := by
            simp only [cellMove, hca, hacc]
          rw [hmv] at hbC
          have hW' := hW ii _ _ _ hbC r
          have hcar : r ∉ carryIns (.Lopn [.reg D] "MOVQ" [.reg (memName A off)]) := by
            simp [carryIns]
          simp only [hx] at hr
          rcases hr with h | h | h | h
          · exact hW' (Or.inl h) hg hcar hn'
          · simp [readsRdx, rdxShape] at h
          · simp only [List.flatMap_cons, List.flatMap_nil, srcNames, List.append_nil,
              List.mem_singleton] at h
            subst h
            rw [DecodePrintedAddr.cellParts?_gp hg] at hn
            cases hn
          · obtain ⟨a, ha, hab⟩ := List.mem_filterMap.mp h
            simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false] at ha
            rcases ha with rfl | rfl
            · exact hW' (Or.inr (Or.inr (Or.inr (List.mem_filterMap.mpr
                ⟨.reg D, by simp, hab⟩)))) hg hcar hn'
            · simp only [cellBase, hn, Option.map_some, Option.some.injEq] at hab
              subst hab
              obtain ⟨q, -, hp⟩ := ptr_of_reloadW hsep hgate hrel
                (accArr_cellBody hN (hasPrefix_gpName (hF.ldGp _ _ D B off hb hca)) hacc) hBf
              exact width_of_getW hp
      | st B off S =>
          obtain ⟨n, hx, hn⟩ := cellA_st hca
          obtain ⟨A, m, hacc, hBf, -, -⟩ := hF.st _ _ B off S hb hca
          have hmv : cellMove slotArr body sa.reg.lpc ⟨ii, .Lopn ds o ss⟩
              = ⟨ii, .Lopn [.reg (memName A off)] "MOVQ" [.reg S]⟩ := by
            simp only [cellMove, hca, hacc]
          rw [hmv] at hbC
          have hW' := hW ii _ _ _ hbC r
          have hcar : r ∉ carryIns (.Lopn [.reg (memName A off)] "MOVQ" [.reg S]) := by
            simp [carryIns]
          simp only [hx] at hr
          rcases hr with h | h | h | h
          · exact hW' (Or.inl h) hg hcar hn'
          · simp [readsRdx, rdxShape] at h
          · exact hW' (Or.inr (Or.inr (Or.inl h))) hg hcar hn'
          · obtain ⟨a, ha, hab⟩ := List.mem_filterMap.mp h
            simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false] at ha
            rcases ha with rfl | rfl
            · simp only [cellBase, hn, Option.map_some, Option.some.injEq] at hab
              subst hab
              obtain ⟨q, -, hp⟩ := ptr_of_reloadW hsep hgate hrel
                (accArr_cellBody hN (hasPrefix_gpName (hF.stGp _ _ B off S hb hca)) hacc) hBf
              exact width_of_getW hp
            · exact hW' (Or.inr (Or.inr (Or.inr (List.mem_filterMap.mpr
                ⟨.reg S, by simp, hab⟩)))) hg hcar hn'
      | lea D B off =>
          rw [cellMove_of_lea (i := ⟨ii, .Lopn ds o ss⟩) hca] at hbC
          exact hW ii ds o ss hbC r hr hg hc hn'

/-- **One step of a straight body with cells and carry chains through its cell body.** -/
theorem cell_stepW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : JasminLsemAddrImage.physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (hnc : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base (cellBody slotArr body) s sa s.zf) {bi : Linstr}
    (hb : (cellBody slotArr body)[sa.reg.lpc]? = some bi)
    (hlt : sa.reg.lpc < (cellBody slotArr body).length - 1)
    (hstep : evalInstrPMemFk true P
      (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s = some t) :
    haltedA body sa = false ∧ SafeW rsp body sa
      ∧ ∃ sa1, stepA frame body sa s.zf = some (sa1, t.zf)
        ∧ ImgRelW frame slotArr base (cellBody slotArr body) t sa1 t.zf := by
  have hwide := wideSafe_cellBody hsep hgate hN hF hrel
  rw [cellBody_getElem?] at hb
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hnc' : ∀ cc l, (cellMove slotArr body sa.reg.lpc b0).li_i ≠ .Lcond cc l := by
    intro cc l he
    unfold cellMove at he
    split at he
    · split at he
      · cases he
      · exact hnc _ _ hb0 cc l he
    · split at he
      · cases he
      · exact hnc _ _ hb0 cc l he
    · exact hnc _ _ hb0 cc l he
  have hbC : (cellBody slotArr body)[sa.reg.lpc]? = some (cellMove slotArr body sa.reg.lpc b0) := by
    rw [cellBody_getElem?, hb0]; rfl
  obtain ⟨hh, hsafe, sa1, hst, hr⟩ :=
    img_stepW hsep hphys hgate P hrel hbC hlt hnc' hstep
  refine ⟨by rw [← haltedA_cellBody slotArr]; exact hh, ⟨(loadSafeAt_cellBody slotArr rsp body sa).mp hsafe,
    hwide, ?_⟩, sa1, ?_, hr⟩
  · intro ii D n B off p hbi hn hp
    rw [hb0] at hbi
    cases hbi
    have hc : cellA? (.Lopn [.reg D] "LOAD:64" [.reg n]) = some (.ld D B off) := by
      simp [cellA?, hn]
    obtain ⟨A, m, hacc, hBf, -, hred⟩ := hF.ld _ _ D B off hb0 hc
    obtain ⟨q, -, hpA⟩ := ptr_of_reloadW hsep hgate hrel
      (accArr_cellBody hN (hasPrefix_gpName (hF.ldGp _ _ D B off hb0 hc)) hacc) hBf
    rw [hp] at hpA
    cases hpA
    exact hred
  · cases hc : cellA? b0.li_i with
    | none =>
        have he : stepA frame body sa s.zf = stepA frame (cellBody slotArr body) sa s.zf := by
          unfold stepA
          rw [hbC, hb0, cellMove_of_none hc]
          obtain ⟨ii, li⟩ := b0
          cases li with
          | Lcond c l =>
              exact absurd rfl (hnc _ _ hb0 c l)
          | _ => simp only [tagAt_cellBody]
        rw [he]
        exact hst
    | some op =>
        cases op with
        | ld D B off =>
            obtain ⟨A, m, hacc, hBf, hfr, -⟩ := hF.ld _ _ D B off hb0 hc
            obtain ⟨q, -, hpA⟩ := ptr_of_reloadW hsep hgate hrel
              (accArr_cellBody hN (hasPrefix_gpName (hF.ldGp _ _ D B off hb0 hc)) hacc) hBf
            rw [stepA_cellBody_ld hb0 hc hacc hpA hfr]
            exact hst
        | st B off S =>
            obtain ⟨A, m, hacc, hBf, hSf, hfr⟩ := hF.st _ _ B off S hb0 hc
            obtain ⟨q, -, hpA⟩ := ptr_of_reloadW hsep hgate hrel
              (accArr_cellBody hN (hasPrefix_gpName (hF.stGp _ _ B off S hb0 hc)) hacc) hBf
            rw [stepA_cellBody_st hb0 hc hacc hpA hfr hSf]
            exact hst
        | lea D B off =>
            rw [stepA_cellBody_of_fix hb0 (cellMove_of_lea hc) (hnc _ _ hb0)]
            exact hst

/-- **The image of the cell body simulated on the body, with carry chains.**
    `image_addr_simB` at the relation `ImgRelW` and the gate `imgGateBW`, which admit one-bit
    carries in general-purpose names. -/
theorem image_addr_simBW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : JasminLsemAddrImage.physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (hnc : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (fn : String) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRelW frame slotArr base (cellBody slotArr body) s sa zf →
      lsemFuelMemFk true (singletonProgM fn (JasminLsemAddrImage.virtImg slotArr
        (cellBody slotArr body))) fuel s = some t →
      ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
        ∧ ImgRelW frame slotArr base (cellBody slotArr body) t sa' zf'
        ∧ RunSafe frame body (SafeW rsp body) fuel' sa zf := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hfn hrel hrun
      cases hf : JasminLsemMemLoop.findInstrMem (singletonProgM fn
          (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr body))) s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          have hh := haltedA_of_imgW hgate fn hfn hrel.pc hf
          rw [haltedA_cellBody] at hh
          exact ⟨0, sa, zf, runA_halt frame body 0 sa zf hh, hrel, trivial⟩
  | succ f ih =>
      intro s t sa zf hfn hrel hrun
      cases hf : JasminLsemMemLoop.findInstrMem (singletonProgM fn
          (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr body))) s.prog with
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          have hh := haltedA_of_imgW hgate fn hfn hrel.pc hf
          rw [haltedA_cellBody] at hh
          exact ⟨0, sa, zf, runA_halt frame body 0 sa zf hh, hrel, trivial⟩
      | some i =>
          simp only [lsemFuelMemFk, hf] at hrun
          cases he : evalInstrPMemFk true (singletonProgM fn
              (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr body))) i s with
          | none => rw [he] at hrun; cases hrun
          | some s1 =>
              rw [he] at hrun
              have hlfn : s1.prog.lfn = fn :=
                (evalInstrPMemF_next _ i s s1 (JasminLsemMemChecked.evalInstrPMemF_of_k he)).1.trans
                  hfn
              have hz := hrel.zf
              subst hz
              rw [findInstrMem_single hfn, JasminLsemAddrImage.virtImg_getElem?, ← hrel.pc,
                List.getElem?_dropLast] at hf
              split at hf
              case isFalse => cases hf
              rename_i hlt
              obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hf
              obtain ⟨hh, hsafe, sa1, hst, hr⟩ :=
                cell_stepW hsep hphys hgate hN hF hnc _ hrel hb hlt he
              obtain ⟨f', sa', zf', hr', hrel', hsafe'⟩ := ih s1 t sa1 s1.zf hlfn hr hrun
              refine ⟨f' + 1, sa', zf', ?_, hrel', hsafe, fun s' zf'' hs' => ?_⟩
              · rw [runA_step frame body f' sa s.zf hh, hst]
                exact hr'
              · rw [hst] at hs'
                cases hs'
                exact hsafe'

/-! ## 4. A virtual body on the decoded bytes of a body with cells -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
  (RunIdxOk lsemFuelMemFk_of_runIdxOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
  (ownedCheckMC ownedCheckMC_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB
  printedAddr_simW_noCall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP read64_eq_of_agree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsNoCall
  halts_of_haltsNoCall)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (runA_congr runSafe_congr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF)

/-- **A virtual body on the decoded bytes of a straight body with cells.** Let the register
    allocation checker accept a virtual body `B` against the image of the cell body, with the
    observed names `outs`, and let the body pass the W class of printed bodies and the cell
    body the class `physImgB` and the gate `imgGateB` or the gate with carry chains
    `imgGateBW` with no observed name in the width analysis at the return (`retOutsB`), at a
    frame map that agrees with the stack frame on the names of the body. A halting run of `B` from a state related to an address state corresponding to the
    machine state `sa` is matched by a halting run of the decoded bytes of the body from
    `sa`, at the end of which every observed name with a frame word outside the red-zone
    word holds the machine word at that frame word. The halting run makes no call. -/
theorem virt_bytesC_noCall {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {sa : AState} {outs : List String} {B : List LinstrRM}
    (hck : ownedCheckMC outs B (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr body))
      = true)
    (hpr : printedAddrWB body = true)
    (hphys : JasminLsemAddrImage.physImgB slotArr (cellBody slotArr body) = true)
    (hgate : (imgGateB frame slotArr (cellBody slotArr body)
      || (imgGateBW frame slotArr (cellBody slotArr body)
        && ImageAddrSimW.retOutsB frame (cellBody slotArr body) outs)) = true)
    (hsep : ImgSep frame slotArr base (frameRsp body sa))
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base (frameRsp body sa) body)
    (hnc : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (hfr : ∀ q ∈ ImageAddrFrame.bodyNamesI body,
      frame q = frameP (Params.ofBody body) (frameRsp body sa) q)
    (fn : String) (b t : LstateMF) (hfn : b.prog.lfn = fn) (hbpc : b.prog.base.reg.lpc = 0)
    (s : LstateA) (zf : Bool)
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) b s zf)
    (hpc : s.reg.lpc = 0)
    (hent : ∀ R, DecodePrinted.gpOk R = true → s.reg.getW R 64 = some (sa.regs (DecodePrinted.phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel b = some t)
    (hok : RunIdxOk (singletonProgM fn B) fuel b) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ HaltsNoCall aMachine prog 0 sa sa'
      ∧ ∀ r a, r ∈ outs → frame r = some a → Disjoint8 (redW (frameRsp body sa)) a →
        t.prog.base.reg.lvm r = ⟨64, read64 sa'.mem a⟩ := by
  have hck' := lsemFuelMemFk_of_runIdxOk true _ fuel b t hrun hok
  obtain ⟨f', t', hr', hobs⟩ := ownedCheckMC_sound hck fn b t hfn hbpc fuel hck'
  have hsim : ∃ fA sA zA, runA frame body fA s zf = some (sA, zA)
      ∧ (∀ q a, q ∈ outs → frame q = some a → t'.prog.base.reg.lvm q = ⟨64, read64 sA.mem a⟩)
      ∧ RunSafe frame body (SafeW (frameRsp body sa) body) fA s zf := by
    rcases Bool.or_eq_true_iff.mp hgate with hg | hg
    · obtain ⟨fA, sA, zA, h1, h2, h3⟩ :=
        image_addr_simB hsep hphys hg hN hF hnc fn f' b t' s zf hfn hrel hr'
      exact ⟨fA, sA, zA, h1, fun q a _ ha => h2.slots q a ha, h3⟩
    · obtain ⟨hg, hro⟩ := Bool.and_eq_true_iff.mp hg
      obtain ⟨fA, sA, zA, h1, h2, h3⟩ :=
        image_addr_simBW hsep hphys hg hN hF hnc fn f' b t' s zf hfn
          (ImageAddrSimW.imgRelW_of hrel) hr'
      have hh : haltedA (cellBody slotArr body) sA = true := by
        rw [haltedA_cellBody]
        exact JasminLsemAddrRun.haltedA_of_runA frame body fA s zf (sA, zA) h1
      exact ⟨fA, sA, zA, h1, fun q a hq ha => (h2.slots q a ha).word
        (ImageAddrSimW.not_mem_oneBitAt_of_halted hg hh
          (ImageAddrSimW.not_mem_of_retOutsB hro hq)), h3⟩
  obtain ⟨fA, sA, zA, hrA, hslots, hsafe⟩ := hsim
  rw [runA_congr hfr] at hrA
  rw [runSafe_congr hfr] at hsafe
  obtain ⟨prog, sa', hdec, hh, -, -, hm'⟩ :=
    printedAddr_simW_noCall body hpr sa s zf hpc (fun R hR => Or.inl (hent R hR)) hmem fA
      (sA, zA) hrA hsafe
  refine ⟨prog, sa', hdec, hh, fun r a hr ha hd => ?_⟩
  rw [← hobs.1 r hr, hslots r a hr ha, read64_eq_of_agree hm' hd]

/-- **A virtual body on the decoded bytes of a straight body with cells.** The statement of
    `virt_bytesC_noCall` with the halting run as a halting run through calls
    (`halts_of_haltsNoCall`). -/
theorem virt_bytesC {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {sa : AState} {outs : List String} {B : List LinstrRM}
    (hck : ownedCheckMC outs B (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr body))
      = true)
    (hpr : printedAddrWB body = true)
    (hphys : JasminLsemAddrImage.physImgB slotArr (cellBody slotArr body) = true)
    (hgate : (imgGateB frame slotArr (cellBody slotArr body)
      || (imgGateBW frame slotArr (cellBody slotArr body)
        && ImageAddrSimW.retOutsB frame (cellBody slotArr body) outs)) = true)
    (hsep : ImgSep frame slotArr base (frameRsp body sa))
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base (frameRsp body sa) body)
    (hnc : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (hfr : ∀ q ∈ ImageAddrFrame.bodyNamesI body,
      frame q = frameP (Params.ofBody body) (frameRsp body sa) q)
    (fn : String) (b t : LstateMF) (hfn : b.prog.lfn = fn) (hbpc : b.prog.base.reg.lpc = 0)
    (s : LstateA) (zf : Bool)
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) b s zf)
    (hpc : s.reg.lpc = 0)
    (hent : ∀ R, DecodePrinted.gpOk R = true →
      s.reg.getW R 64 = some (sa.regs (DecodePrinted.phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel b = some t)
    (hok : RunIdxOk (singletonProgM fn B) fuel b) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∀ r a, r ∈ outs → frame r = some a → Disjoint8 (redW (frameRsp body sa)) a →
        t.prog.base.reg.lvm r = ⟨64, read64 sa'.mem a⟩ := by
  obtain ⟨prog, sa', hdec, hh, hobs⟩ := virt_bytesC_noCall hck hpr hphys hgate hsep hN hF hnc
    hfr fn b t hfn hbpc s zf hrel hpc hent hmem fuel hrun hok
  exact ⟨prog, sa', hdec, halts_of_haltsNoCall hh, hobs⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells
