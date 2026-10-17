/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold
public import CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

/-!
# The image class under the two-address legalisation and the compare-spill reload

The image check `physImgB slotArr body` (`JasminLsemAddrImage`) reads each indexed access of a
body through the reload scan `reloadOf`, and each write of an array slot through the entry scan
`entryRegB`. The two last passes of the printer, the two-address legalisation
`TwoAddrLegalize.twoAddrBody` and the compare-spill reload `CmpSpillReload.cmpReload`, expand
each instruction of a body into a block. This module proves that both keep the class.

A body expanded block by block (`b.flatMap g`) is in the class when every instruction is kept
alone, or is no move and is expanded into a block with no access and no array-slot destination
whose scan dominates the scan of the instruction, from the scan of the body in front of it
(`physImgB_flatMap_of_dom`).

## Main results

* `provF_pass`: a block of single-destination operations none of which writes a name, or an
  array slot, passes the scan of that name.
* `domOn_flatMap`, `physImgB_flatMap_of_dom`: the class of a body expanded block by block.
* `physImgB_twoAddrBody`: the two-address legalisation keeps the class, when no flag-only
  compare is untied (`flagTiedB`) and the save slot of the scratch register is no array slot.
* `physImgB_cmpReload`: the compare-spill reload keeps the class, when the reload scratch
  holds the pointer of no array at a compare on a spilled first operand (`cmpScratchFreeB`).

Every result assumes that every array slot is a `qsave.` slot, which the region layout gives.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. Blocks and the scan -/

theorem provF_cons (j : Linstr) (l : Lcmd) (f : String → Option String) :
    provF slotArr (j :: l) f = provF slotArr l (scanStepF slotArr j f) := rfl

theorem provF_singleton (j : Linstr) (f : String → Option String) :
    provF slotArr [j] f = scanStepF slotArr j f := rfl

/-- A block of operations, each with a single destination that is neither `x` nor an array
    slot, passes the scan of `x`. -/
theorem provF_pass {x : String} : ∀ (L : Lcmd) (g : String → Option String),
    (∀ r ∈ L, ∃ e o ss, r.li_i = .Lopn [.reg e] o ss ∧ e ≠ x ∧ slotArr e = none) →
      provF slotArr L g x = g x
  | [], _, _ => rfl
  | r :: L, g, h => by
    rw [provF_cons, provF_pass L _ (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]
    obtain ⟨e, o, ss, hr, hne, hs⟩ := h r List.mem_cons_self
    exact scanStepF_single_ne hs hr (Ne.symm hne) g

/-- The step of the scan at an operation that is no move ends the scan or passes it. -/
theorem scanStepF_nonmove {i : Linstr} {ds : List LOperand} {o : String} {ss : List LOperand}
    (hm : slotMov? i.li_i = none) (hi : i.li_i = .Lopn ds o ss) (f : String → Option String)
    (x : String) : scanStepF slotArr i f x = none ∨ scanStepF slotArr i f x = f x := by
  unfold scanStepF
  rw [hm, hi]
  simp only
  split_ifs <;> simp

/-- The step of the scan at an instruction that is no move into `x` keeps the scan of `x`
    without a result. -/
theorem scanStepF_none_of_not_movInto {j : Linstr} {x : String}
    (hj : ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ x) {f : String → Option String}
    (hf : f x = none) : scanStepF slotArr j f x = none := by
  unfold scanStepF
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d, s⟩ := p
    have hd := hj d s hm
    simp only [if_neg hd]
    split_ifs <;> simp [hf]
  | none =>
    simp only
    cases j.li_i with
    | Lopn ds o ss => simp only; split_ifs <;> simp [hf]
    | _ => rfl

/-- The scan of `x` after a list of instructions none of which is a move into `x` has no
    result. -/
theorem provF_none_of_not_movInto {x : String} :
    ∀ (A : Lcmd), (∀ j ∈ A, ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ x) →
      ∀ {f : String → Option String}, f x = none → provF slotArr A f x = none
  | [], _, _, hf => hf
  | j :: A, h, _, hf => by
    rw [provF_cons]
    exact provF_none_of_not_movInto A (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))
      (scanStepF_none_of_not_movInto (h j List.mem_cons_self) hf)

/-- **An operation replaced by a block.** Let `i` be an operation that is no move, and let every
    name `x` of `S` either have no result after `i`, or be passed by the block `L`, or hold the
    pointer of no array in front of `i`. Then the scan after `L` dominates the scan after
    `i`. -/
theorem domOn_nonmove_block {S : String → Prop} {i : Linstr} {ds : List LOperand} {o : String}
    {ss : List LOperand} {L : Lcmd} {f g : String → Option String}
    (hm : slotMov? i.li_i = none) (hi : i.li_i = .Lopn ds o ss)
    (hL : ∀ x, S x → scanStepF slotArr i f x = none ∨ provF slotArr L g x = g x ∨
      ∀ q, f x = some q → (slotArr q).isSome = false)
    (h : DomOn slotArr S f g) : DomOn slotArr S (scanStepF slotArr i f) (provF slotArr L g) := by
  intro x hx q hf hq
  rcases hL x hx with h0 | h1 | h2
  · rw [h0] at hf; cases hf
  · rw [h1]
    rcases scanStepF_nonmove hm hi f x with e | e <;> rw [e] at hf
    · cases hf
    · exact h x hx q hf hq
  · rcases scanStepF_nonmove hm hi f x with e | e <;> rw [e] at hf
    · cases hf
    · rw [h2 q hf] at hq; cases hq

/-! ## 2. A body expanded block by block -/

/-- An instruction of a body expanded block by block lies in the block of an instruction of the
    body. -/
theorem flatMap_getElem?_split {g : Linstr → Lcmd} : ∀ (l : Lcmd) (k : Nat) (r : Linstr),
    (l.flatMap g)[k]? = some r → ∃ A i C o, l = A ++ i :: C ∧
      k = (A.flatMap g).length + o ∧ (g i)[o]? = some r
  | [], k, r, h => by simp at h
  | i :: l, k, r, h => by
    rw [List.flatMap_cons] at h
    by_cases hk : k < (g i).length
    · exact ⟨[], i, l, k, rfl, by simp, by rwa [List.getElem?_append_left hk] at h⟩
    · rw [List.getElem?_append_right (by omega)] at h
      obtain ⟨A, j, C, o, rfl, hk', hj⟩ := flatMap_getElem?_split l _ r h
      exact ⟨i :: A, j, C, o, rfl, by simp only [List.flatMap_cons, List.length_append]; omega,
        hj⟩

/-- **The scans at the block boundaries.** Let every instruction of `b` be kept alone or be
    expanded into a block whose scan dominates its step, from the scan of the body in front of
    it. Then at every boundary the scan of the expanded body dominates the scan of `b`. -/
theorem domOn_flatMap {S : String → Prop} (hS : ∀ q, gpNameB q = true → S q) {b : Lcmd}
    {g : Linstr → Lcmd}
    (hblk : ∀ A i C, b = A ++ i :: C → g i = [i] ∨ ∀ f', DomOn slotArr S
      (provF slotArr A fun _ => none) f' →
      DomOn slotArr S (scanStepF slotArr i (provF slotArr A fun _ => none)) (provF slotArr (g i) f')) :
    ∀ A C, b = A ++ C → DomOn slotArr S (provF slotArr A fun _ => none)
      (provF slotArr (A.flatMap g) fun _ => none) := by
  intro A
  induction A using List.reverseRecOn with
  | nil => intro C _ x _ q hf; simp [provF] at hf
  | append_singleton A i ih =>
    intro C hb
    have hb' : b = A ++ i :: C := by simpa using hb
    have hD := ih (i :: C) hb'
    rw [provF_append, List.flatMap_append, provF_append, provF_singleton]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases hblk A i C hb' with hk | hr
    · rw [hk, provF_singleton]; exact domOn_step hS hD i
    · exact hr _ hD

/-- **The class of a body expanded block by block.** Let `b` be in the class, let the base of
    every access of `b` be in `S`, and let every instruction `i` of `b` be kept alone, or be no
    move expanded into a block with no access and no array-slot destination whose scan dominates
    the step at `i`, from the scan of the body in front of `i`. Then `b.flatMap g` is in the
    class. -/
theorem physImgB_flatMap_of_dom {S : String → Prop} (hS : ∀ q, gpNameB q = true → S q)
    {b : Lcmd} {g : Linstr → Lcmd} (h : physImgB slotArr b = true)
    (hbase : ∀ i ∈ b, ∀ ds o x y ss, i.li_i = .Lopn ds o (.arrIdx x y 8 :: ss) → S x)
    (hblk : ∀ A i C, b = A ++ i :: C → g i = [i] ∨
      ((∀ r ∈ g i, isAccB r.li_i = false ∧ DstOk slotArr r.li_i) ∧ slotMov? i.li_i = none ∧
        ∀ f', DomOn slotArr S (provF slotArr A fun _ => none) f' →
          DomOn slotArr S (scanStepF slotArr i (provF slotArr A fun _ => none))
            (provF slotArr (g i) f'))) :
    physImgB slotArr (b.flatMap g) = true := by
  have hD := domOn_flatMap hS (fun A i C hb => (hblk A i C hb).imp id fun h => h.2.2)
  refine physImgB_of_embed h fun k r hk => ?_
  obtain ⟨A, i, C, o, hb, rfl, hr⟩ := flatMap_getElem?_split b k r hk
  have hfl : b.flatMap g = A.flatMap g ++ (g i ++ C.flatMap g) := by
    rw [hb, List.flatMap_append, List.flatMap_cons]
  rcases hblk A i C hb with hk1 | ⟨hblkr, -, -⟩
  · rw [hk1] at hr
    cases o with
    | succ o => simp at hr
    | zero =>
      simp only [List.getElem?_singleton, if_true, Option.some.injEq] at hr
      subst hr
      refine Or.inr ⟨A.length, by rw [hb]; simp, fun x hx ha => ?_, Or.inl fun R hR => ?_⟩
      · obtain ⟨ds, o', y, ss, hx'⟩ := hx
        have hSx := hbase i (by rw [hb]; simp) ds o' x y ss hx'
        rw [hb, accArr_append_left _ _ _ _ _ le_rfl] at ha
        rw [hfl, Nat.add_zero, accArr_append_left _ _ _ _ _ le_rfl]
        simp only [accArr] at ha ⊢
        have e1 := congrFun (reloadOf_eq_provF (slotArr := slotArr) A A.length le_rfl) x
        have e2 := congrFun (reloadOf_eq_provF (slotArr := slotArr) (A.flatMap g)
          (A.flatMap g).length le_rfl) x
        rw [List.take_length] at e1 e2
        rw [e1] at ha
        rw [e2]
        cases hq1 : provF slotArr A (fun _ => none) x with
        | none => simp [hq1] at ha
        | some q =>
          rw [hq1, Option.bind_some] at ha
          rw [hD A (i :: C) hb x hSx q hq1 ha, Option.bind_some]
          exact ha
      · by_cases hall : ∀ j ∈ A, g j = [j]
        · have hA : A.flatMap g = A := by
            rw [List.flatMap_congr (fun j hj => hall j hj)]
            simp
          refine entryRegB_of_take_sublist ?_ hR
          rw [hfl, hb, Nat.add_zero, List.take_left' rfl, hA, List.take_left' rfl]
        · push Not at hall
          obtain ⟨j, hj, hjne⟩ := hall
          obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hj
          have hbj : b = A₁ ++ j :: (A₂ ++ i :: C) := by rw [hb]; simp
          rcases hblk A₁ j _ hbj with hk2 | ⟨-, hmj, -⟩
          · exact absurd hk2 hjne
          · exfalso
            unfold entryRegB at hR
            rw [hb, List.take_left' rfl, List.all_eq_true] at hR
            have := hR j hj
            rw [hmj] at this
            cases this
  · have hmem : r ∈ g i := List.mem_of_getElem? hr
    exact Or.inl ⟨(hblkr r hmem).1, slotWriteB_of_dstOk (hblkr r hmem).2 _ _⟩

/-- An operation with two sources whose first source is a register or an immediate, at which
    `accOkB` holds, is no indexed access. -/
theorem accOkB_two {body : Lcmd} {k : Nat} {d opn : String} {a c : LOperand}
    (h : accOkB slotArr body k (.Lopn [.reg d] opn [a, c]) = true)
    (ha : ∀ x y sc, a ≠ .arrIdx x y sc) : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" := by
  constructor <;> rintro rfl <;> cases a <;> simp_all [accOkB]

theorem isAccB_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h1 : o ≠ "LOADIDX") (h2 : o ≠ "STOREIDX") : isAccB (.Lopn ds o ss) = false := by
  simp [isAccB, h1, h2]

theorem isAccB_mov {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : o = "MOV" ∨ o = "MOV:64") : isAccB (.Lopn ds o ss) = false := by
  rcases h with rfl | rfl <;> simp [isAccB]

/-! ## 3. The two-address legalisation -/

section TwoAddr

open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize

/-- Every flag-only compare `Lopn [d] opn [x, c]` with a register `x` as its first source is
    tied: `x = d`. -/
def flagTiedB (body : Lcmd) : Bool :=
  body.all fun i => match i.li_i with
    | .Lopn [.reg d] opn [.reg x, _] => !(x86Data.flagOnly (tieBase opn)) || x == d
    | _ => true

/-- **The blocks of the legalisation.** On an instruction that is no untied flag-only compare,
    the legalisation keeps the instruction, or the instruction is an operation `opn d, [a, c]`
    with a register or immediate `a`, and every instruction of its block is an operation with a
    single destination, `d` or, on the scratch route, the scratch register or its save slot, at
    the mnemonic `opn` or a copy mnemonic. -/
theorem legalizeInstr_shape (ok : Bool) (i : Linstr)
    (hflag : ∀ d opn x c, i.li_i = .Lopn [.reg d] opn [.reg x, c] →
      x86Data.flagOnly (tieBase opn) = true → x = d) :
    legalizeInstr ok i = [i] ∨ ∃ d opn a c, i.li_i = .Lopn [.reg d] opn [a, c] ∧
      isRegOrImm a = true ∧ ∀ r ∈ legalizeInstr ok i, ∃ e o ss, r.li_i = .Lopn [.reg e] o ss ∧
        (o = opn ∨ o = "MOV" ∨ o = "MOV:64") ∧
        (e = d ∨ (ok = true ∧ (e = x86Data.tieScratch ∨ e = scratchSave))) := by
  generalize hL : legalizeInstr ok i = L
  unfold legalizeInstr at hL
  split at hL
  · rename_i d opn a c hi
    split at hL
    · rename_i htie
      split at hL
      · exact Or.inl hL.symm
      · rename_i m hm
        have hm' : m = "MOV" ∨ m = "MOV:64" := by
          change movFor opn = some m at hm
          unfold movFor at hm
          split_ifs at hm <;> (simp only [Option.some.injEq] at hm; subst hm; simp)
        split at hL
        · rename_i hfo
          split at hL
          · rename_i x
            exfalso
            have := hflag d opn x c hi hfo
            subst this
            simp at htie
          · exact Or.inl hL.symm
        · split at hL
          · exact Or.inl hL.symm
          · rename_i hreg
            have ha : isRegOrImm a = true := by simpa using hreg
            right
            refine ⟨d, opn, a, c, hi, ha, ?_⟩
            subst hL
            split
            · intro r hr
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · exact ⟨d, m, [a], rfl, Or.inr hm', Or.inl rfl⟩
              · exact ⟨d, opn, _, rfl, Or.inl rfl, Or.inl rfl⟩
            · split
              · intro r hr
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl
                exact ⟨d, opn, _, rfl, Or.inl rfl, Or.inl rfl⟩
              · split
                · rename_i hok
                  split <;>
                  · intro r hr
                    simp only [scratchRoute, List.mem_cons, List.not_mem_nil, or_false] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl
                    · exact ⟨_, _, _, rfl, Or.inr (Or.inr rfl), Or.inr ⟨hok, Or.inr rfl⟩⟩
                    · exact ⟨_, _, _, rfl, Or.inr hm', Or.inr ⟨hok, Or.inl rfl⟩⟩
                    · exact ⟨_, _, _, rfl, Or.inl rfl, Or.inr ⟨hok, Or.inl rfl⟩⟩
                    · exact ⟨_, _, _, rfl, Or.inr hm', Or.inl rfl⟩
                    · exact ⟨_, _, _, rfl, Or.inr (Or.inr rfl), Or.inr ⟨hok, Or.inl rfl⟩⟩
                · intro r hr
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                  rcases hr with rfl
                  exact ⟨d, opn, _, hi, Or.inl rfl, Or.inl rfl⟩
    · exact Or.inl hL.symm
  · exact Or.inl hL.symm

/-- A body none of whose instructions names the scratch register has no move into the scratch
    register or into its save slot. -/
theorem movInto_of_avoids {j : Linstr} (hj : instrAvoids j.li_i = true) {d s : String}
    (hs : slotMov? j.li_i = some (d, s)) : d ≠ x86Data.tieScratch ∧ d ≠ scratchSave := by
  rcases slotMov?_shape hs with he | he <;> rw [he] at hj <;>
    simp_all [instrAvoids, opAvoids, mentionsScratch, scratchSave]

/-- **The two-address legalisation keeps the class.** When every array slot is a `qsave.` slot,
    the save slot of the scratch register is no array slot and every flag-only compare is tied
    (`flagTiedB`), the legalisation of a body in the class is in the class. -/
theorem physImgB_twoAddrBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (hsave : slotArr scratchSave = none) (hflag : flagTiedB b = true)
    (h : physImgB slotArr b = true) : physImgB slotArr (twoAddrBody b) = true := by
  have hR : slotArr x86Data.tieScratch = none :=
    PhysImgFold.slotArr_none_of_prefix hq (gpNameB_prefix (d := x86Data.tieScratch) (by decide)).1
  show physImgB slotArr (b.flatMap fun i => legalizeInstr (bodyAvoids b) i) = true
  refine physImgB_flatMap_of_dom (S := fun _ => True) (fun _ _ => trivial) h
    (fun _ _ _ _ _ _ _ _ => trivial) fun A i C hb => ?_
  have hib : i ∈ b := by rw [hb]; simp
  have hpos : b[A.length]? = some i := by rw [hb]; simp
  have hfl : ∀ d opn x c, i.li_i = .Lopn [.reg d] opn [.reg x, c] →
      x86Data.flagOnly (tieBase opn) = true → x = d := by
    intro d opn x c hi hf
    have := List.all_eq_true.mp hflag i hib
    rw [hi] at this
    have hf' : (tieBase opn == "CMP" || tieBase opn == "TEST") = true := hf
    simp only [hf', Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact this
  rcases legalizeInstr_shape (bodyAvoids b) i hfl with h1 | ⟨d, opn, a, c, hi, ha, hL⟩
  · exact Or.inl h1
  · right
    have hm : slotMov? i.li_i = none := by rw [hi]; cases a <;> rfl
    obtain ⟨hacc, hwr⟩ := physImgB_getElem h hpos
    rw [hi] at hacc hwr
    have hd : slotArr d = none := slotArr_of_slotWriteB (by rw [← hi]; exact hm) hwr
    obtain ⟨hn1, hn2⟩ := accOkB_two hacc (by intro x y sc he; subst he; cases ha)
    refine ⟨fun r hr => ?_, hm, fun f' hD => ?_⟩
    · obtain ⟨e, o, ss, hr', ho, he⟩ := hL r hr
      have hse : slotArr e = none := by rcases he with rfl | ⟨-, rfl | rfl⟩ <;> assumption
      rw [hr']
      refine ⟨?_, dstOk_single hse⟩
      rcases ho with rfl | ho
      · exact isAccB_lopn hn1 hn2
      · exact isAccB_mov ho
    · refine domOn_nonmove_block hm hi (fun x _ => ?_) hD
      by_cases hxd : x = d
      · left
        subst hxd
        unfold scanStepF
        rw [hm, hi]
        simp [dstHitB]
      · by_cases hsx : bodyAvoids b = true ∧ (x = x86Data.tieScratch ∨ x = scratchSave)
        · right; right
          intro q hq
          rw [provF_none_of_not_movInto A ?_ rfl] at hq
          · cases hq
          intro j hj d' s hs
          have hjb : j ∈ b := by rw [hb]; simp [hj]
          have hav := List.all_eq_true.mp hsx.1 j hjb
          obtain ⟨h1, h2⟩ := movInto_of_avoids hav hs
          rcases hsx.2 with rfl | rfl
          · exact h1
          · exact h2
        · right; left
          refine provF_pass _ _ fun r hr => ?_
          obtain ⟨e, o, ss, hr', -, he⟩ := hL r hr
          refine ⟨e, o, ss, hr', ?_, ?_⟩
          · rintro rfl
            rcases he with he | ⟨hok, he | he⟩
            · exact hxd he
            · exact hsx ⟨hok, Or.inl he⟩
            · exact hsx ⟨hok, Or.inr he⟩
          · rcases he with rfl | ⟨-, rfl | rfl⟩ <;> assumption

end TwoAddr

/-! ## 4. The compare-spill reload -/

section CmpReload

open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

/-- At every compare on a spilled first operand, the reload scratch `reloadScratch` holds the
    pointer of no array. -/
def cmpScratchFreeB (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  (List.range body.length).all fun k =>
    match body[k]? with
    | some i => (spillCmp? i.li_i).isNone || (accArr slotArr body k reloadScratch).isNone
    | none => true

/-- A compare on a spilled first operand is `Lopn [d] opn [d, s]`. -/
theorem spillCmp?_some {r : LinstrR} {opn d : String} {s : LOperand}
    (h : spillCmp? r = some (opn, d, s)) : r = .Lopn [.reg d] opn [.reg d, s] := by
  unfold spillCmp? at h
  split at h
  · split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hc.1.1.2]
  · cases h

/-- **The compare-spill reload keeps the class.** When every array slot is a `qsave.` slot and
    the reload scratch holds the pointer of no array at a compare on a spilled first operand
    (`cmpScratchFreeB`), the reload of a body in the class is in the class. -/
theorem physImgB_cmpReload
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (hfree : cmpScratchFreeB slotArr b = true) (h : physImgB slotArr b = true) :
    physImgB slotArr (cmpReload b) = true := by
  have hR : slotArr reloadScratch = none :=
    PhysImgFold.slotArr_none_of_prefix hq (gpNameB_prefix (d := reloadScratch) (by decide)).1
  show physImgB slotArr (b.flatMap fun i => cmpReloadI i) = true
  refine physImgB_flatMap_of_dom (S := fun _ => True) (fun _ _ => trivial) h
    (fun _ _ _ _ _ _ _ _ => trivial) fun A i C hb => ?_
  have hpos : b[A.length]? = some i := by rw [hb]; simp
  cases hs : spillCmp? i.li_i with
  | none => exact Or.inl (cmpReloadI_of_none hs)
  | some p =>
    obtain ⟨opn, d, s⟩ := p
    right
    have hi := spillCmp?_some hs
    have hg : cmpReloadI i = [⟨i.li_ii, .Lopn [.reg reloadScratch] (movOf opn) [.reg d]⟩,
        ⟨i.li_ii, .Lopn [.reg reloadScratch] opn [.reg reloadScratch, s]⟩] := by
      simp only [cmpReloadI, hs]; rfl
    have hm : slotMov? i.li_i = none := by rw [hi]; rfl
    obtain ⟨hacc, -⟩ := physImgB_getElem h hpos
    rw [hi] at hacc
    obtain ⟨hn1, hn2⟩ := accOkB_two hacc (by intro x y sc he; cases he)
    rw [hg]
    refine ⟨fun r hr => ?_, hm, fun f' hD => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨isAccB_mov ?_, dstOk_single hR⟩
        unfold movOf; split_ifs <;> simp
      · exact ⟨isAccB_lopn hn1 hn2, dstOk_single hR⟩
    · refine domOn_nonmove_block hm hi (fun x _ => ?_) hD
      by_cases hx : x = reloadScratch
      · right; right
        subst hx
        intro q hq
        have hk : A.length < b.length := (List.getElem?_eq_some_iff.mp hpos).1
        have := List.all_eq_true.mp hfree A.length (List.mem_range.mpr hk)
        rw [hpos] at this
        simp only [hs, Option.isNone_some, Bool.false_or, Option.isNone_iff_eq_none] at this
        have e1 := congrFun (reloadOf_eq_provF (slotArr := slotArr) b A.length hk.le) reloadScratch
        rw [hb, List.take_left' rfl, ← hb] at e1
        simp only [accArr, e1, hq, Option.bind_some] at this
        simp [this]
      · right; left
        refine provF_pass _ _ fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, _, _, rfl, Ne.symm hx, hR⟩
        · exact ⟨_, _, _, rfl, Ne.symm hx, hR⟩

end CmpReload

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint
