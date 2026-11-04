/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVBlocks
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SymFootprint
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of the checks of the segments of a calling body

The checks of the segments of a calling body (`CalleeSegCheck.calleeSegB`) run the register
allocation checker with an entry set (`OwnedLprogTVChecked.ownedCheckMCIn`) on every cut
program. The checker computes its live sets by the iteration `liveIter` from the empty sets,
checks the block pairs against them, and requires the live names of the entry block to lie
in the entry set. The entry sets `ins` enter twice: as the entry set of a segment, and,
through `CalleeSegCheck.segOutsAt`, as the names observed at the exit of a segment that ends
at a call.

This module proves that the checks are monotone in the entry sets at names that neither body
writes (`calleeSegB_mono`): such a name holds its start word at the end of every run of both
bodies, so its comparison at an exit passes, and the live sets of the checker grow only by
names of this kind. The growth is a backward propagation along the edges of the graph of the
cut program (`Yit`), which ends within as many rounds as there are blocks (`Yit_stable`),
well within the budget `4 · nb + 64` of the iteration. The statement is parametric in the two
entry sets; at the entry sets of the register liveness table (`RegionBackend.insTab`), whose
names include the array names of the body, it states that array names no body writes as
registers add no refusal.

It proves further that the live names the checker finds at the entry of a cut program lie in
every table of names closed along the cut program (`liveIter_entry_sub`,
`ownedCheckMCIn_of_tab`). The names of such a table at the starts of the blocks, with the
flags live, are a post-fixpoint of `liveRound` (`livePost_tab`): the needs of a block
(`blockNeed`) read the cached registers of the shared term table, which the substitution of
the table bounds from above (`VarsUB`, kept by interning, `tRun_validU`), so they are
registers that the words of the symbolic run read, and these lie in the table at the start of
the block by the transfer of the table along the run (`symRun_tab`). The image enters only
through its guards, which the block checks place among the reference guards (`GuardsIn`). A
table closed along a body gives, along the inverse `cutBack` of `LprogCallCut.cutPos`, a
table closed along each of its cut programs (`tabClosed_cutAt`); the module
`Haxc.RegionCalleeNames` instantiates it at the liveness table and `insTab`.

## Main definitions

* `KeepsReg`: the symbolic step of every instruction of a body keeps the word of a register.
* `FactFree`: no must-constant fact names a register.
* `RunsOk`, `RunsOkAt`: the block pairs that the checker checks.
* `liveIt`: the iterate of `liveRound` from the empty sets.
* `Yit`: the names the iteration propagates from the observed names of a halt.
* `VarsUB`, `TValidU`: a substitution bounds the cached registers of a table from above.
* `StepTr`, `TabClosed`: a table of names over the positions of a body transfers every step
  and is closed along the jumps, the conditional jumps and the end.
* `tabLive`: the names of a table at the starts of the blocks, with the flags live.
* `GuardsIn`: the image guards of a block pair are among its reference guards.
* `LabelsOnce`, `FinFree`: labels declared once; a label neither declared nor jumped to.
* `cutBack`, `cutIns`, `cutTab`: the positions, instructions and table of a body along a cut
  program.

## Main results

* `liveIter_eq_iterate`: the live-set iteration stops only at a fixpoint, so it is the
  iterate of `liveRound` by its budget.
* `liveIter_le_post`: the live sets the iteration computes lie below every post-fixpoint of
  `liveRound` above its start.
* `keepsReg_of_regDefs`: a register outside `regDefs` of a body with one register destination
  per operation is kept (from `SymFootprint.symStep_frame`).
* `constAnnot_free`, `tRun_keeps`: the facts and the shared runs keep such a register at its
  start word.
* `liveIt_rel`: the iterations for two sets of observed names differ by names of `Yit`.
* `Yit_stable`: the propagation ends within as many rounds as there are blocks.
* `ownedCheckMCIn_obs_mono`: the checker with an entry set accepts more observed names that
  both bodies keep.
* `calleeSegB_mono`: the checks of the segments are monotone in the entry sets at names that
  neither body writes.
* `STerm.varsT_sub_subst`, `tRun_validU`: the registers a word reads over the shared table
  are registers of its substitution instance, for a substitution that interning keeps.
* `SG.norm_vars`: a normal form of a guard reads only registers of the guard.
* `runs_fp`: the reads of the reference run of a block pair over the shared table.
* `livePost_tab`: a closed table at the starts of the blocks is a post-fixpoint of
  `liveRound`.
* `liveIter_entry_sub`, `ownedCheckMCIn_of_tab`: the live names at the entry lie in a
  closed table, so the entry set needs no name outside it.
* `cutAt_getElem?`, `tabClosed_cutAt`: the instructions of a cut program, and the table of a
  body along a cut program.

Elaboration takes about twenty seconds.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

/-! ## 1. The live-set iteration -/

section Iterate

variable (outs : List String) (B : List LinstrRM) (G : CFG) (R : Array (Tbl × SOut × SOut))
  (dec : SSt → LOperand → SDec)

/-- The join of live sets appends to the first list. -/
theorem foldl_join_append : ∀ (l acc : List String),
    ∃ e, l.foldl (fun a v => if a.contains v then a else a ++ [v]) acc = acc ++ e
  | [], acc => ⟨[], by simp⟩
  | v :: l, acc => by
      simp only [List.foldl_cons]
      split
      · exact foldl_join_append l acc
      · obtain ⟨e, he⟩ := foldl_join_append l (acc ++ [v])
        exact ⟨[v] ++ e, by rw [he, List.append_assoc]⟩

/-- A join that keeps the length of the names and the flag keeps the live set. -/
theorem joinLive_eq_of_length {n m : List String × Bool}
    (h : ((joinLive n m).1.length, (joinLive n m).2) = (n.1.length, n.2)) :
    joinLive n m = n := by
  obtain ⟨e, he⟩ := foldl_join_append m.1 n.1
  simp only [Prod.mk.injEq] at h
  have h1 : (joinLive n m).1 = n.1 ++ e := he
  rw [h1, List.length_append] at h
  have he' : e = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst he'
  exact Prod.ext (by rw [h1, List.append_nil]) h.2

/-- **A round that keeps every length and flag keeps the live sets.** -/
theorem liveRound_eq_of_lengths {L : Array (List String × Bool)} (hs : L.size = G.blocks.size)
    (h : (liveRound outs B G R L dec).map (fun p => (p.1.length, p.2)) ==
      L.map (fun p => (p.1.length, p.2))) : liveRound outs B G R L dec = L := by
  have he := beq_iff_eq.mp h
  apply Array.ext (by simp [liveRound, hs])
  intro k hk1 hk2
  have e := congrArg (·[k]?) he
  simp only [Array.getElem?_map] at e
  rw [Array.getElem?_eq_getElem hk1, Array.getElem?_eq_getElem hk2] at e
  simp only [Option.map_some, Option.some.injEq] at e
  have hk : k < G.blocks.size := by simpa [liveRound] using hk1
  have hr : (liveRound outs B G R L dec)[k] =
      joinLive (L.getD k ([], false))
        (match R[k]? with
          | some r =>
              blockNeed outs (fun j => L.getD j ([], false)) (G.blk k).term r B (G.blk k) dec
          | none => ([], false)) := by
    simp [liveRound]
    rfl
  have hl : L.getD k ([], false) = L[k] := by simp [Array.getD, hk2]
  rw [hr, hl] at e ⊢
  exact joinLive_eq_of_length e

/-- **The live-set iteration is the iterate of `liveRound` by its budget**: it stops only at
    a fixpoint of `liveRound`. -/
theorem liveIter_eq_iterate : ∀ (n : Nat) (L : Array (List String × Bool)),
    L.size = G.blocks.size →
    liveIter outs B G R n L dec = (fun L => liveRound outs B G R L dec)^[n] L
  | 0, _, _ => rfl
  | n + 1, L, hs => by
      rw [liveIter]
      split
      · rename_i h
        have hf := liveRound_eq_of_lengths outs B G R dec hs h
        exact (Function.iterate_fixed hf (n + 1)).symm
      · rw [Function.iterate_succ_apply]
        exact liveIter_eq_iterate n _ (by simp [liveRound])

/-- **The live sets of the iteration lie below every post-fixpoint of `liveRound`** above
    the start, for the default branch condition. -/
theorem liveIter_le_post {P : Array (List String × Bool)} (hP : LivePost outs B G R P) :
    ∀ (n : Nat) (L : Array (List String × Bool)), LiveLe L P →
      LiveLe (liveIter outs B G R n L) P
  | 0, _, hL => hL
  | n + 1, L, hL => by
      rw [liveIter]
      split
      · exact hL
      · refine liveIter_le_post hP n _ fun k => ?_
        by_cases hk : k < G.blocks.size
        · rw [liveRound_getD outs B G R L hk]
          exact (hL k).joinLive ((hP k hk).trans (needAt_mono outs B G R hL k))
        · rw [liveRound_getD_ge outs B G R L (Nat.not_lt.mp hk)]
          exact LiveCov.nil _

end Iterate

/-! ## 2. Registers a body does not write -/

/-- **The symbolic step of every instruction of `B` keeps the word of the register `y`.** -/
def KeepsReg (y : String) (B : List LinstrRM) : Prop :=
  ∀ i ∈ B, ∀ (ss s : SSt) (gs : List SG), symStep i ss = .ok s gs → s.regs y = ss.regs y

/-- A register outside `regDefs` of every instruction of a body with one register destination
    per operation is kept (`SymFootprint.symStep_frame`). -/
theorem keepsReg_of_regDefs {y : String} {B : List LinstrRM}
    (h : ∀ i ∈ B, SymFootprint.OneDst i ∧ y ∉ JasminLsemExportRegAlloc.regDefs i) :
    KeepsReg y B :=
  fun i hi _ _ _ hs => SymFootprint.symStep_frame (h i hi).1 hs (h i hi).2

theorem KeepsReg.mono {y : String} {B C : List LinstrRM} (h : KeepsReg y B)
    (hC : ∀ i ∈ C, i ∈ B) : KeepsReg y C :=
  fun i hi => h i (hC i hi)

/-- A run of instructions of `B` keeps the word of a register `B` keeps. -/
theorem symRun_keeps {y : String} {B : List LinstrRM} (h : KeepsReg y B) :
    ∀ (is : List LinstrRM), (∀ i ∈ is, i ∈ B) → ∀ {ss s : SSt} {gs : List SG},
      symRun is ss = .ok s gs → s.regs y = ss.regs y
  | [], _, _, _, _, hr => by
      simp only [symRun, SOut.ok.injEq] at hr
      rw [hr.1]
  | i :: is, hB, ss, s, gs, hr => by
      simp only [symRun] at hr
      split at hr
      · rename_i ss1 g1 h1
        split at hr
        · rename_i ss2 g2 h2
          simp only [SOut.ok.injEq] at hr
          rw [← hr.1, symRun_keeps h is (fun i' hi' => hB i' (List.mem_cons_of_mem _ hi')) h2,
            h i (hB i List.mem_cons_self) ss ss1 g1 h1]
        · cases hr
        · cases hr
      · cases hr
      · cases hr

/-- Interning keeps the word of a register that holds an atom. -/
theorem internRegs_regs_atom {y : String} :
    ∀ (T : Tbl) (ss : SSt) (ds : List String), (ss.regs y).atom = true →
      (T.internRegs ss ds).2.regs y = ss.regs y
  | _, _, [], _ => rfl
  | T, ss, d :: ds, h => by
      simp only [Tbl.internRegs]
      by_cases hd : d = y
      · subst hd
        rw [Tbl.intern_atom T h]
        have e : ss.putR d (ss.regs d) = ss := by
          refine SSt.ext (fun r => ?_) rfl rfl rfl rfl rfl rfl
          rw [SSt.putR_regs]
          split <;> simp_all
        rw [e]
        exact internRegs_regs_atom T ss ds h
      · have hr : (ss.putR d (T.intern (ss.regs d)).2).regs y = ss.regs y := by
          rw [SSt.putR_regs, ite_eq_right (Ne.symm hd)]
        rw [internRegs_regs_atom _ _ ds (by rw [hr]; exact h), hr]

theorem internSt_regs_atom {y : String} (T : Tbl) (ss : SSt) (ds : List String)
    (h : (ss.regs y).atom = true) : (T.internSt ss ds).2.regs y = ss.regs y := by
  simp only [Tbl.internSt]
  exact internRegs_regs_atom T ss ds h

/-- **A shared run keeps a register that holds the start word `.reg y`** when every step
    keeps it. -/
theorem tRun_keeps {y : String} {B : List LinstrRM} (h : KeepsReg y B) :
    ∀ (is : List LinstrRM), (∀ i ∈ is, i ∈ B) → ∀ {ss s : SSt} {T T' : Tbl} {gs : List SG},
      ss.regs y = .reg y → tRun is ss T = (T', .ok s gs) → s.regs y = .reg y
  | [], _, _, _, _, _, _, hy, hr => by
      simp only [tRun, Prod.mk.injEq, SOut.ok.injEq] at hr
      rw [← hr.2.1]
      exact hy
  | i :: is, hB, ss, s, T, T', gs, hy, hr => by
      simp only [tRun] at hr
      split at hr
      · rename_i ss1 g1 h1
        have h1y : ss1.regs y = .reg y := by
          rw [h i (hB i List.mem_cons_self) ss ss1 g1 h1, hy]
        have hpy : (T.internSt ss1 (ss1.newWr ss)).2.regs y = .reg y := by
          rw [internSt_regs_atom _ _ _ (by rw [h1y]; rfl), h1y]
        split at hr
        · rename_i ss2 g2 h2
          simp only [Prod.mk.injEq, SOut.ok.injEq] at hr
          obtain ⟨-, rfl, -⟩ := hr
          exact tRun_keeps h is (fun i' hi' => hB i' (List.mem_cons_of_mem _ hi')) hpy
            (Prod.ext rfl h2)
        · simp at hr
        · simp at hr
      · simp at hr
      · simp at hr

/-! ## 3. Must-constant facts on registers a body does not write -/

section Facts

variable {y : String} {B : List LinstrRM} {G : CFG}

/-- No fact of the annotation `ann` is about the register `y`. -/
def FactFree (y : String) (ann : Array (List CFact)) : Prop :=
  ∀ k, ∀ f ∈ ann.getD k [], f.1 ≠ y

theorem startC_regs_of_free {fs : List CFact} (h : ∀ f ∈ fs, f.1 ≠ y) :
    (startC fs).regs y = .reg y := by
  rw [startC_regs]
  have hn : fs.find? (fun f => f.1 == y) = none := by
    rw [List.find?_eq_none]
    intro f hf
    simpa using h f hf
  rw [hn]

theorem constExit_free {ss : SSt} (hy : ss.regs y = .reg y) : ∀ f ∈ constExit ss, f.1 ≠ y := by
  intro f hf
  simp only [constExit, List.mem_filterMap] at hf
  obtain ⟨r, -, hr⟩ := hf
  split at hr
  · rename_i w n he
    cases hr
    rintro rfl
    rw [hy] at he
    cases he
  · cases hr

theorem mem_of_mem_bodyAt {b : Block} {T : Term} {i : LinstrRM} (h : i ∈ bodyAt B b T) :
    i ∈ B :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem exitsOf_free (hk : KeepsReg y B) {ann : Array (List CFact)} (ha : FactFree y ann)
    {k : Nat} {ss : SSt} {g : List SG} (he : (exitsOf B G symStep ann)[k]? = some (.ok ss g)) :
    ss.regs y = .reg y := by
  simp only [exitsOf, Array.getElem?_map, Array.getElem?_range] at he
  split at he
  · simp only [Option.map_some, Option.some.injEq] at he
    rw [symRun_keeps hk _ (fun i hi => mem_of_mem_bodyAt hi) he]
    exact startC_regs_of_free (ha k)
  · cases he

theorem getD_map_range {α : Type} (n k : Nat) (f : Nat → α) (d : α) :
    ((Array.range n).map f).getD k d = if k < n then f k else d := by
  by_cases hk : k < n <;> simp [Array.getD, hk]

theorem constGrow_free (hk : KeepsReg y B) {P : Array (Array Nat)} {ann : Array (List CFact)}
    (ha : FactFree y ann) : FactFree y (constGrow B G symStep P ann) := by
  intro k f hf
  unfold constGrow at hf
  rw [getD_map_range] at hf
  split_ifs at hf with hkn hk0
  · simp at hf
  · rw [List.mem_eraseDups, List.mem_append] at hf
    rcases hf with hf | hf
    · exact ha k f hf
    · simp only [List.mem_flatMap] at hf
      obtain ⟨j, -, hj⟩ := hf
      split at hj
      · rename_i ss g he
        exact constExit_free (exitsOf_free hk ha he) f hj
      · simp at hj
  · simp at hf

theorem constPass_free {P : Array (Array Nat)} {ann : Array (List CFact)}
    (ha : FactFree y ann) : FactFree y (constPass B G symStep P ann) := by
  intro k f hf
  unfold constPass at hf
  rw [getD_map_range] at hf
  split_ifs at hf with hkn hk0
  · simp at hf
  · exact ha k f (List.mem_of_mem_filter hf)
  · simp at hf

theorem constFix_free {F : Array (List CFact) → Array (List CFact)}
    (hF : ∀ ann, FactFree y ann → FactFree y (F ann)) :
    ∀ (n : Nat) (ann : Array (List CFact)), FactFree y ann → FactFree y (constFix F n ann)
  | 0, _, ha => ha
  | n + 1, ann, ha => by
      simp only [constFix]
      split
      · exact ha
      · exact constFix_free hF n _ (hF ann ha)

/-- **The must-constant facts of a body name no register the body keeps.** -/
theorem constAnnot_free (hk : KeepsReg y B) (k : Nat) :
    ∀ f ∈ constAnnot B G symStep k, f.1 ≠ y := by
  unfold constAnnot annotAt constAnnotArr
  split
  · simp
  · intro f hf
    refine constFix_free (fun _ ha => constPass_free ha) _ _
      (constFix_free (fun _ ha => constGrow_free hk ha) _ _ (fun j f' hf' => ?_)) k f hf
    simp [Array.getD] at hf'

end Facts

/-! ## 4. The checks are monotone in the live sets -/

section Mono

variable {E : Array TEnt} {n n' : List String × Bool}

theorem okIn_mono (h : LiveCov n' n) {vs : List String} {rf : Bool} (ho : okIn n vs rf = true) :
    okIn n' vs rf = true := by
  obtain ⟨h1, h2⟩ := okIn_spec ho
  simp only [okIn, vIn, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨fun v hv => h.1 v (h1 v hv), ?_⟩
  cases rf
  · exact Or.inl rfl
  · exact Or.inr (h.2 (h2 rfl))

theorem okInT_mono (h : LiveCov n' n) {t : STerm} (ho : okInT E n t = true) :
    okInT E n' t = true := by
  simp only [okInT, Bool.and_eq_true] at ho ⊢
  exact ⟨ho.1, okIn_mono h ho.2⟩

theorem okInAT_mono (h : LiveCov n' n) {a : SArr} (ho : okInAT E n a = true) :
    okInAT E n' a = true := by
  simp only [okInAT, Bool.and_eq_true] at ho ⊢
  exact ⟨ho.1, okIn_mono h ho.2⟩

theorem okInFT_mono (h : LiveCov n' n) {f : SFlag} (ho : okInFT E n f = true) :
    okInFT E n' f = true := by
  simp only [okInFT, Bool.and_eq_true] at ho ⊢
  exact ⟨ho.1, okIn_mono h ho.2⟩

theorem okInGT_mono (h : LiveCov n' n) {g : SG} (ho : okInGT E n g = true) :
    okInGT E n' g = true := by
  simp only [okInGT, Bool.and_eq_true] at ho ⊢
  exact ⟨ho.1, okIn_mono h ho.2⟩

theorem okInDT_mono (h : LiveCov n' n) {d : SDec} (ho : okInDT E n d = true) :
    okInDT E n' d = true := by
  simp only [okInDT, Bool.and_eq_true] at ho ⊢
  exact ⟨ho.1, okIn_mono h ho.2⟩

theorem guardsT_mono (h : LiveCov n' n) {gs gs' : List SG} (hg : guardsT E n gs gs' = true) :
    guardsT E n' gs gs' = true := by
  simp only [guardsT, Bool.and_eq_true, List.all_eq_true] at hg ⊢
  exact ⟨hg.1, fun g hgm => ⟨(hg.2 g hgm).1, okInGT_mono h (hg.2 g hgm).2⟩⟩

theorem termAgreeT_mono (h : LiveCov n' n) {T : Term} {ss ss' : SSt} {x z : Option LinstrRM}
    {dec : SSt → LOperand → SDec} (ht : termAgreeT E T n ss ss' x z dec = true) :
    termAgreeT E T n' ss ss' x z dec = true := by
  unfold termAgreeT at ht ⊢
  split at ht
  · exact ht
  · split at ht
    · simp only [Bool.and_eq_true] at ht ⊢
      exact ⟨ht.1, okInDT_mono h ht.2⟩
    · exact ht
  · exact ht

theorem oblOk_mono {L L' : Nat → List String × Bool} {k : Nat} (h : LiveCov (L' k) (L k))
    {T : Term} {B B' : List LinstrRM} {b b' : Block} {sym : LinstrRM → SSt → SOut}
    {A A' : Nat → List CFact} (ho : oblOk L k T B B' b b' sym A A' = true) :
    oblOk L' k T B B' b b' sym A A' = true := by
  unfold oblOk at ho ⊢
  have key : ∀ T' : Term, (match symRun (bodyAt B b T') (startC (A k)) sym with
      | .ok _ _ =>
          (symObl (bodyAt B' b' T') (startC (A' k)) sym).all fun o =>
            (symObl (bodyAt B b T') (startC (A k)) sym).contains o &&
              okIn (L k) o.1.vars o.1.readsF
      | _ => true) = true →
      (match symRun (bodyAt B b T') (startC (A k)) sym with
      | .ok _ _ =>
          (symObl (bodyAt B' b' T') (startC (A' k)) sym).all fun o =>
            (symObl (bodyAt B b T') (startC (A k)) sym).contains o &&
              okIn (L' k) o.1.vars o.1.readsF
      | _ => true) = true := by
    intro T' hT
    cases hr : symRun (bodyAt B b T') (startC (A k)) sym with
    | ok ss gs =>
        simp only [hr, List.all_eq_true, Bool.and_eq_true] at hT ⊢
        exact fun o hm => ⟨(hT o hm).1, okIn_mono h (hT o hm).2⟩
    | fail => rfl
    | unk => rfl
  rcases T with _ | _ | _ | _
  · exact key _ ho
  · exact key _ ho
  · exact key _ ho
  · rfl

theorem oblCheckWith_mono {L L' : Nat → List String × Bool} (h : ∀ k, LiveCov (L' k) (L k))
    {B B' : List LinstrRM} {sym : LinstrRM → SSt → SOut} {A A' : Nat → List CFact}
    (ho : oblCheckWith L B B' sym A A' = true) : oblCheckWith L' B B' sym A A' = true := by
  unfold oblCheckWith at ho ⊢
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at ho
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at ho
      | some G' =>
          simp only [hG, hG', List.all_eq_true] at ho ⊢
          exact fun k hk => oblOk_mono (h k) (ho k hk)

end Mono

/-! ## 5. Observed names that neither body writes -/

theorem joinLive_mem {n m : List String × Bool} {v : String} :
    v ∈ (joinLive n m).1 ↔ v ∈ n.1 ∨ v ∈ m.1 :=
  ⟨fun h => foldl_join_mem m.1 n.1 v h, fun h => h.elim (fun h => (foldl_join_spec m.1 n.1).1 v h)
    (fun h => (foldl_join_spec m.1 n.1).2.1 v h)⟩

section Need

variable {O₁ O₂ : List String} {Yp : String → Prop} {L₁ L₂ : Nat → List String × Bool}
  {T : Term} {r : Tbl × SOut × SOut} {B : List LinstrRM} {b : Block}

/-- The runs of a block both succeed and its terminator is no return: the block has a
    check. -/
def RunsOk (T : Term) (r : Tbl × SOut × SOut) : Prop :=
  T ≠ .ret ∧ ∃ ss g ss' g', r.2.1 = .ok ss g ∧ r.2.2 = .ok ss' g'

/-- **The needs of a block for more observed names**: a name the block needs for the
    observed names `O₂` and the live sets `L₂` is a name it needs for `O₁` and `L₁`, or a name
    of `Yp` that is observed at a halt or live at a successor in `L₂` and not in `L₁`, when the
    names of `O₂` and of `L₂` outside `O₁` and `L₁` are names of `Yp` whose word the run of the
    block keeps at the start word. -/
theorem blockNeed_names (hO2 : ∀ v ∈ O₂, v ∈ O₁ ∨ Yp v)
    (hY : ∀ ss g, r.2.1 = .ok ss g → ∀ y, Yp y → ss.regs y = .reg y)
    (hL : ∀ j, ∀ v ∈ (L₂ j).1, v ∈ (L₁ j).1 ∨ Yp v) (hF : ∀ j, (L₂ j).2 = (L₁ j).2) {v : String}
    (hv : v ∈ (blockNeed O₂ L₂ T r B b).1) :
    v ∈ (blockNeed O₁ L₁ T r B b).1 ∨ (Yp v ∧ RunsOk T r ∧
      ((T.halts ∧ v ∈ O₂) ∨ ∃ j ∈ T.succs, v ∈ (L₂ j).1 ∧ v ∉ (L₁ j).1)) := by
  obtain ⟨tb, o1, o2⟩ := r
  unfold blockNeed at hv ⊢
  cases T
  case ret => simp at hv
  all_goals
    cases o1 with
    | fail => simp at hv
    | unk => simp at hv
    | ok ss g =>
      cases o2 with
      | fail => simp at hv
      | unk => simp at hv
      | ok ss' g' =>
        have hYs := hY ss g rfl
        simp only [List.mem_append, List.mem_flatMap] at hv ⊢
        rcases hv with ((((hv | hv) | ⟨j, hj, hv⟩) | hv) | hv)
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hv))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hv))))
        · rcases hv with ⟨w, hw, hv⟩ | hv
          · rcases Classical.em (w ∈ (L₁ j).1) with hw1 | hw1
            · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inl ⟨w, hw1, hv⟩⟩)))
            · have hyw : Yp w := (hL j w hw).resolve_left hw1
              rw [hYs w hyw] at hv
              simp only [STerm.varsT, List.mem_singleton] at hv
              subst hv
              exact Or.inr ⟨hyw, ⟨by simp, ss, g, ss', g', rfl, rfl⟩, Or.inr ⟨j, hj, hw, hw1⟩⟩
          · refine Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inr ?_⟩)))
            rw [← hF j]
            exact hv
        · split at hv
          · rename_i hh
            simp only [List.mem_flatMap] at hv
            obtain ⟨w, hw, hv⟩ := hv
            rcases hO2 w hw with hw1 | hyw
            · refine Or.inl (Or.inl (Or.inr ?_))
              rw [ite_eq_left hh]
              exact List.mem_flatMap.mpr ⟨w, hw1, hv⟩
            · rw [hYs w hyw] at hv
              simp only [STerm.varsT, List.mem_singleton] at hv
              subst hv
              exact Or.inr ⟨hyw, ⟨by simp, ss, g, ss', g', rfl, rfl⟩, Or.inl ⟨hh, hw⟩⟩
          · simp at hv
        · exact Or.inl (Or.inr hv)

/-- **The flag a block needs does not change with observed names it keeps.** -/
theorem blockNeed_flag (hO : ∀ v ∈ O₁, v ∈ O₂) (hO2 : ∀ v ∈ O₂, v ∈ O₁ ∨ Yp v)
    (hY : ∀ ss g, r.2.1 = .ok ss g → ∀ y, Yp y → ss.regs y = .reg y)
    (hL : ∀ j, ∀ v ∈ (L₂ j).1, v ∈ (L₁ j).1 ∨ Yp v) (hL' : ∀ j, ∀ v ∈ (L₁ j).1, v ∈ (L₂ j).1)
    (hF : ∀ j, (L₂ j).2 = (L₁ j).2) :
    (blockNeed O₂ L₂ T r B b).2 = (blockNeed O₁ L₁ T r B b).2 := by
  obtain ⟨tb, o1, o2⟩ := r
  unfold blockNeed
  cases T
  case ret => rfl
  all_goals
    cases o1 with
    | fail => rfl
    | unk => rfl
    | ok ss g =>
      cases o2 with
      | fail => rfl
      | unk => rfl
      | ok ss' g' =>
        have hYs := hY ss g rfl
        have hrf : ∀ w, Yp w → (ss.regs w).readsFT tb.ents = false := by
          intro w hw
          rw [hYs w hw]
          rfl
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, hF]
        constructor
        · rintro ((((h | h) | ⟨j, hj, h⟩) | ⟨hh, w, hw, h⟩) | h)
          · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
          · refine Or.inl (Or.inl (Or.inr ⟨j, hj, ?_⟩))
            rcases h with ⟨w, hw, h⟩ | h
            · rcases hL j w hw with hw1 | hyw
              · exact Or.inl ⟨w, hw1, h⟩
              · rw [hrf w hyw] at h; cases h
            · exact Or.inr h
          · rcases hO2 w hw with hw1 | hyw
            · exact Or.inl (Or.inr ⟨hh, w, hw1, h⟩)
            · rw [hrf w hyw] at h; cases h
          · exact Or.inr h
        · rintro ((((h | h) | ⟨j, hj, h⟩) | ⟨hh, w, hw, h⟩) | h)
          · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
          · refine Or.inl (Or.inl (Or.inr ⟨j, hj, ?_⟩))
            rcases h with ⟨w, hw, h⟩ | h
            · exact Or.inl ⟨w, hL' j w hw, h⟩
            · exact Or.inr h
          · exact Or.inl (Or.inr ⟨hh, w, hO w hw, h⟩)
          · exact Or.inr h

/-- **The needs of a block are monotone in the observed names and the live sets.** -/
theorem blockNeed_mono2 (hO : ∀ v ∈ O₁, v ∈ O₂) (h : ∀ j, LiveCov (L₂ j) (L₁ j)) :
    LiveCov (blockNeed O₂ L₂ T r B b) (blockNeed O₁ L₁ T r B b) := by
  refine (blockNeed_mono T r B b h).trans ?_
  obtain ⟨tb, o1, o2⟩ := r
  unfold blockNeed
  cases T
  case ret => exact LiveCov.refl _
  all_goals
    cases o1 with
    | fail => exact LiveCov.refl _
    | unk => exact LiveCov.refl _
    | ok ss g =>
      cases o2 with
      | fail => exact LiveCov.refl _
      | unk => exact LiveCov.refl _
      | ok ss' g' =>
        refine ⟨fun v hv => ?_, fun hv => ?_⟩
        · simp only [List.mem_append, List.mem_flatMap] at hv ⊢
          rcases hv with ((((hv | hv) | hv) | hv) | hv)
          · exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr hv)))
          · exact Or.inl (Or.inl (Or.inr hv))
          · refine Or.inl (Or.inr ?_)
            split at hv
            · rename_i hh
              rw [ite_eq_left hh]
              obtain ⟨w, hw, hv⟩ := List.mem_flatMap.mp hv
              exact List.mem_flatMap.mpr ⟨w, hO w hw, hv⟩
            · simp at hv
          · exact Or.inr hv
        · simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at hv ⊢
          rcases hv with ((((hv | hv) | hv) | ⟨hh, w, hw, hv⟩) | hv)
          · exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr hv)))
          · exact Or.inl (Or.inl (Or.inr hv))
          · exact Or.inl (Or.inr ⟨hh, w, hO w hw, hv⟩)
          · exact Or.inr hv

/-- **A name of `Yp` observed at a halt or live at a successor is needed** by a block with a
    check whose run keeps it at the start word. -/
theorem mem_blockNeed_of (hY : ∀ ss g, r.2.1 = .ok ss g → ∀ y, Yp y → ss.regs y = .reg y)
    (hr : RunsOk T r) {v : String} (hv : Yp v)
    (h : (T.halts ∧ v ∈ O₂) ∨ ∃ j ∈ T.succs, v ∈ (L₂ j).1) :
    v ∈ (blockNeed O₂ L₂ T r B b).1 := by
  obtain ⟨hT, ss, g, ss', g', h1, h2⟩ := hr
  obtain ⟨tb, o1, o2⟩ := r
  simp only at h1 h2
  subst h1 h2
  have hYs := hY ss g rfl
  unfold blockNeed
  cases T
  case ret => exact absurd rfl hT
  all_goals
    simp only [List.mem_append, List.mem_flatMap]
    rcases h with ⟨hh, hO⟩ | ⟨j, hj, hj2⟩
    · refine Or.inl (Or.inr ?_)
      rw [ite_eq_left hh]
      exact List.mem_flatMap.mpr ⟨v, hO, by rw [hYs v hv]; simp [STerm.varsT]⟩
    · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inl ⟨v, hj2, by rw [hYs v hv]; simp [STerm.varsT]⟩⟩))

end Need

/-! ## 6. The live-set iterations for more observed names -/

section Iter

variable (B : List LinstrRM) (G : CFG) (R : Array (Tbl × SOut × SOut))

/-- The iterate of `liveRound` from the empty sets. -/
def liveIt (O : List String) (n : Nat) : Array (List String × Bool) :=
  (fun L => liveRound O B G R L symDec)^[n] (Array.replicate G.blocks.size ([], false))

/-- Block `k` has runs `R[k]` with a check. -/
def RunsOkAt (k : Nat) : Prop := ∃ r, R[k]? = some r ∧ RunsOk (G.blk k).term r

/-- **The names of `Yp` the iteration propagates within `n` rounds**: from a block with a
    check that halts and observes them in `O₂`, and backwards along the edges into blocks with
    a check. -/
def Yit (O₂ : List String) (Yp : String → Prop) : Nat → Nat → String → Prop
  | 0, _, _ => False
  | n + 1, k, v => Yit O₂ Yp n k v ∨ (k < G.blocks.size ∧ RunsOkAt G R k ∧ Yp v ∧
      (((G.blk k).term.halts = true ∧ v ∈ O₂) ∨ ∃ j ∈ (G.blk k).term.succs, Yit O₂ Yp n j v))

variable {B G R} {O₁ O₂ : List String} {Yp : String → Prop}

theorem Yit_yp : ∀ {n k : Nat} {v : String}, Yit G R O₂ Yp n k v → Yp v
  | 0, _, _, h => h.elim
  | _ + 1, _, _, Or.inl h => Yit_yp h
  | _ + 1, _, _, Or.inr h => h.2.2.1

theorem Yit_lt : ∀ {n k : Nat} {v : String}, Yit G R O₂ Yp n k v → k < G.blocks.size
  | 0, _, _, h => h.elim
  | _ + 1, _, _, Or.inl h => Yit_lt h
  | _ + 1, _, _, Or.inr h => h.1

theorem Yit_mono : ∀ {n m k : Nat} {v : String}, n ≤ m → Yit G R O₂ Yp n k v →
    Yit G R O₂ Yp m k v
  | n, m, k, v, hnm, h => by
      induction m with
      | zero =>
          rw [Nat.le_zero.mp hnm] at h
          exact h
      | succ m ih =>
          rcases Nat.lt_or_ge n (m + 1) with h1 | h1
          · exact Or.inl (ih (by omega))
          · rw [show m + 1 = n by omega]
            exact h

theorem liveIt_zero (O : List String) (k : Nat) : (liveIt B G R O 0).getD k ([], false) =
    ([], false) := by
  by_cases hk : k < G.blocks.size <;> simp [liveIt, Array.getD, hk]

theorem liveIt_succ_lt (O : List String) (n : Nat) {k : Nat} (hk : k < G.blocks.size) :
    (liveIt B G R O (n + 1)).getD k ([], false) =
      joinLive ((liveIt B G R O n).getD k ([], false)) (needAt O B G R (liveIt B G R O n) k) := by
  simp only [liveIt, Function.iterate_succ_apply']
  exact liveRound_getD O B G R _ hk

theorem liveIt_ge (O : List String) (n : Nat) {k : Nat} (hk : G.blocks.size ≤ k) :
    (liveIt B G R O n).getD k ([], false) = ([], false) := by
  cases n with
  | zero => exact liveIt_zero O k
  | succ n =>
      simp only [liveIt, Function.iterate_succ_apply']
      exact liveRound_getD_ge O B G R _ hk

theorem joinLive_cov_left (n m : List String × Bool) : LiveCov (joinLive n m) n :=
  ⟨fun v hv => joinLive_mem.mpr (Or.inl hv), fun h => by simp [joinLive, h]⟩

/-- **The iterations for the observed names `O₁` and `O₂`**, where the names of `O₂` outside
    `O₁` are names of `Yp` that the runs of the blocks keep at their start words: at every
    round the live sets for `O₂` cover those for `O₁`, add to them only names that `Yit`
    propagates, have the same flags, and hold every name `Yit` propagates. -/
theorem liveIt_rel (hO : ∀ v ∈ O₁, v ∈ O₂) (hO2 : ∀ v ∈ O₂, v ∈ O₁ ∨ Yp v)
    (hY : ∀ (k : Nat) (r : Tbl × SOut × SOut) (ss : SSt) (g : List SG), R[k]? = some r →
      r.2.1 = .ok ss g → ∀ y, Yp y → ss.regs y = .reg y) :
    ∀ n k, LiveCov ((liveIt B G R O₂ n).getD k ([], false)) ((liveIt B G R O₁ n).getD k ([], false))
      ∧ (∀ v ∈ ((liveIt B G R O₂ n).getD k ([], false)).1,
          v ∈ ((liveIt B G R O₁ n).getD k ([], false)).1 ∨ Yit G R O₂ Yp n k v)
      ∧ ((liveIt B G R O₂ n).getD k ([], false)).2 = ((liveIt B G R O₁ n).getD k ([], false)).2
      ∧ ∀ v, Yit G R O₂ Yp n k v → v ∈ ((liveIt B G R O₂ n).getD k ([], false)).1 := by
  intro n
  induction n with
  | zero =>
      intro k
      rw [liveIt_zero, liveIt_zero]
      exact ⟨LiveCov.refl _, fun v hv => by simp at hv, rfl, fun v h => h.elim⟩
  | succ n ih =>
      intro k
      by_cases hk : k < G.blocks.size
      · rw [liveIt_succ_lt O₂ n hk, liveIt_succ_lt O₁ n hk]
        have hL : ∀ j, ∀ v ∈ ((liveIt B G R O₂ n).getD j ([], false)).1,
            v ∈ ((liveIt B G R O₁ n).getD j ([], false)).1 ∨ Yp v := fun j v hv =>
          ((ih j).2.1 v hv).imp id Yit_yp
        have hL' : ∀ j, ∀ v ∈ ((liveIt B G R O₁ n).getD j ([], false)).1,
            v ∈ ((liveIt B G R O₂ n).getD j ([], false)).1 := fun j v hv => (ih j).1.1 v hv
        have hF : ∀ j, ((liveIt B G R O₂ n).getD j ([], false)).2 =
            ((liveIt B G R O₁ n).getD j ([], false)).2 := fun j => (ih j).2.2.1
        unfold needAt
        cases hR : R[k]? with
        | none =>
            simp only
            refine ⟨((joinLive_cov_left _ _).trans (ih k).1).joinLive (LiveCov.nil _),
              fun v hv => ?_, ?_, fun v hv => ?_⟩
            · rcases joinLive_mem.mp hv with hv | hv
              · rcases (ih k).2.1 v hv with h | h
                · exact Or.inl (joinLive_mem.mpr (Or.inl h))
                · exact Or.inr (Or.inl h)
              · simp at hv
            · simp only [joinLive, Bool.or_false, (ih k).2.2.1]
            · rcases hv with hv | ⟨-, ⟨r, hr, -⟩, -⟩
              · exact joinLive_mem.mpr (Or.inl ((ih k).2.2.2 v hv))
              · rw [hR] at hr; cases hr
        | some r =>
            simp only
            have hYk : ∀ ss g, r.2.1 = .ok ss g → ∀ y, Yp y → ss.regs y = .reg y :=
              fun ss g h => hY k r ss g hR h
            refine ⟨((joinLive_cov_left _ _).trans (ih k).1).joinLive
                ((joinLive_cov _ _).trans (blockNeed_mono2 hO fun j => (ih j).1)),
              fun v hv => ?_, ?_, fun v hv => ?_⟩
            · rcases joinLive_mem.mp hv with hv | hv
              · rcases (ih k).2.1 v hv with h | h
                · exact Or.inl (joinLive_mem.mpr (Or.inl h))
                · exact Or.inr (Or.inl h)
              · rcases blockNeed_names hO2 hYk hL hF hv with h | ⟨hyv, hrun, h⟩
                · exact Or.inl (joinLive_mem.mpr (Or.inr h))
                · refine Or.inr (Or.inr ⟨hk, ⟨r, hR, hrun⟩, hyv, ?_⟩)
                  rcases h with h | ⟨j, hj, h1, h2⟩
                  · exact Or.inl h
                  · exact Or.inr ⟨j, hj, ((ih j).2.1 v h1).resolve_left h2⟩
            · simp only [joinLive, (ih k).2.2.1, blockNeed_flag hO hO2 hYk hL hL' hF]
            · rcases hv with hv | ⟨-, ⟨r', hr', hrun⟩, hyv, h⟩
              · exact joinLive_mem.mpr (Or.inl ((ih k).2.2.2 v hv))
              · rw [hR] at hr'
                cases hr'
                refine joinLive_mem.mpr (Or.inr (mem_blockNeed_of hYk hrun hyv ?_))
                rcases h with h | ⟨j, hj, h⟩
                · exact Or.inl h
                · exact Or.inr ⟨j, hj, (ih j).2.2.2 v h⟩
      · rw [liveIt_ge O₂ (n + 1) (Nat.not_lt.mp hk), liveIt_ge O₁ (n + 1) (Nat.not_lt.mp hk)]
        exact ⟨LiveCov.refl _, fun v hv => by simp at hv, rfl,
          fun v hv => absurd (Yit_lt hv) hk⟩

/-- A round that propagates nothing new for `v` is followed only by such rounds. -/
theorem Yit_stable_succ {v : String} {n : Nat}
    (h : ∀ k, Yit G R O₂ Yp (n + 1) k v → Yit G R O₂ Yp n k v) :
    ∀ k, Yit G R O₂ Yp (n + 2) k v → Yit G R O₂ Yp (n + 1) k v := by
  intro k hk
  rcases hk with hk | ⟨hkl, hok, hy, hh | ⟨j, hj, hjv⟩⟩
  · exact hk
  · exact Or.inr ⟨hkl, hok, hy, Or.inl hh⟩
  · exact Or.inr ⟨hkl, hok, hy, Or.inr ⟨j, hj, h j hjv⟩⟩

theorem Yit_stable_ge {v : String} {n : Nat}
    (h : ∀ k, Yit G R O₂ Yp (n + 1) k v → Yit G R O₂ Yp n k v) :
    ∀ m, n ≤ m → ∀ k, Yit G R O₂ Yp (m + 1) k v → Yit G R O₂ Yp m k v := by
  intro m hm
  induction m with
  | zero =>
      rw [Nat.le_zero.mp hm] at h
      exact h
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h1 | h1
      · exact Yit_stable_succ (ih (by omega))
      · rw [show m + 1 = n by omega]
        exact h

open Classical in
/-- The blocks to which `Yit` has propagated `v` within `n` rounds. -/
noncomputable def yitSet (v : String) (n : Nat) : Finset Nat :=
  (Finset.range G.blocks.size).filter fun k => Yit G R O₂ Yp n k v

open Classical in
theorem card_yitSet_ge {v : String} : ∀ n : Nat,
    (∀ m, m < n → ¬ ∀ k, Yit G R O₂ Yp (m + 1) k v → Yit G R O₂ Yp m k v) →
    n ≤ (yitSet (G := G) (R := R) (O₂ := O₂) (Yp := Yp) v n).card
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
      have ih := card_yitSet_ge n fun m hm => h m (by omega)
      have hs : yitSet (G := G) (R := R) (O₂ := O₂) (Yp := Yp) v n ⊂
          yitSet (G := G) (R := R) (O₂ := O₂) (Yp := Yp) v (n + 1) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun k hk => ?_, fun he => h n (by omega) fun k hk => ?_⟩
        · simp only [yitSet, Finset.mem_filter] at hk ⊢
          exact ⟨hk.1, Or.inl hk.2⟩
        · have hk' : k ∈ yitSet (G := G) (R := R) (O₂ := O₂) (Yp := Yp) v (n + 1) := by
            simp only [yitSet, Finset.mem_filter, Finset.mem_range]
            exact ⟨Yit_lt hk, hk⟩
          rw [← he] at hk'
          simp only [yitSet, Finset.mem_filter] at hk'
          exact hk'.2
      have := Finset.card_lt_card hs
      omega

open Classical in
/-- **The propagation of `Yit` ends within as many rounds as there are blocks**: beyond that,
    a round propagates nothing new. -/
theorem Yit_stable {v : String} {N : Nat} (hN : G.blocks.size < N) {k : Nat}
    (h : Yit G R O₂ Yp N k v) : Yit G R O₂ Yp (N - 1) k v := by
  by_cases hs : ∀ k, Yit G R O₂ Yp (N - 1 + 1) k v → Yit G R O₂ Yp (N - 1) k v
  · exact hs k (by rw [show N - 1 + 1 = N by omega]; exact h)
  · exfalso
    have hall : ∀ m, m < N → ¬ ∀ k, Yit G R O₂ Yp (m + 1) k v → Yit G R O₂ Yp m k v :=
      fun m hm hm' => hs (Yit_stable_ge hm' (N - 1) (by omega))
    have h1 := card_yitSet_ge (G := G) (R := R) (O₂ := O₂) (Yp := Yp) (v := v) N hall
    have h2 : (yitSet (G := G) (R := R) (O₂ := O₂) (Yp := Yp) v N).card ≤ G.blocks.size := by
      unfold yitSet
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega

end Iter

/-! ## 7. The check for more observed names -/

section Check

/-- **The check of a block for more observed names**: the check of block `k` for `O₁` and
    the live sets `L₁` implies its check for `O₂` and `L₂`, when `L₂ k` covers `L₁ k`, the
    flags agree, and at a block with a check every name of `L₂` at a successor or of `O₂` at
    a halt outside `L₁` and `O₁` is a name that both runs keep at the start word and that is
    live in `L₂ k`. -/
theorem blockOkR_obs_mono {O₁ O₂ : List String} {L₁ L₂ : Nat → List String × Bool} {k : Nat}
    {T : Term} {r : Tbl × SOut × SOut} {B B' : List LinstrRM} {b b' : Block}
    (hcov : LiveCov (L₂ k) (L₁ k)) (hF : ∀ j, (L₂ j).2 = (L₁ j).2)
    (hsucc : RunsOk T r → ∀ j ∈ T.succs, ∀ v ∈ (L₂ j).1, v ∈ (L₁ j).1 ∨
      ((∀ ss g, r.2.1 = .ok ss g → ss.regs v = .reg v) ∧
        (∀ ss g, r.2.2 = .ok ss g → ss.regs v = .reg v) ∧ v ∈ (L₂ k).1))
    (hhalt : RunsOk T r → T.halts = true → ∀ v ∈ O₂, v ∈ O₁ ∨
      ((∀ ss g, r.2.1 = .ok ss g → ss.regs v = .reg v) ∧
        (∀ ss g, r.2.2 = .ok ss g → ss.regs v = .reg v) ∧ v ∈ (L₂ k).1))
    (h : blockOkR O₁ L₁ k T r B B' b b' = true) : blockOkR O₂ L₂ k T r B B' b b' = true := by
  obtain ⟨tb, o1, o2⟩ := r
  have hreg : ∀ v ∈ (L₂ k).1, okInT tb.ents (L₂ k) (STerm.reg v) = true := by
    intro v hv
    simp [okInT, okIn, vIn, STerm.refsLt, STerm.varsT, STerm.readsFT, hv]
  cases o1 with
  | fail =>
      unfold blockOkR
      cases T <;> rfl
  | unk =>
      unfold blockOkR at h ⊢
      cases T <;> simp_all
  | ok ss g =>
    cases o2 with
    | fail =>
        unfold blockOkR at h ⊢
        cases T <;> simp_all
    | unk =>
        unfold blockOkR at h ⊢
        cases T <;> simp_all
    | ok ss' g' =>
      have hrunG : T ≠ .ret → RunsOk T (tb, SOut.ok ss g, SOut.ok ss' g') :=
        fun hT => ⟨hT, ss, g, ss', g', rfl, rfl⟩
      have hhaltG : T ≠ .ret →
          (T.halts = false ∨ ∀ x ∈ O₁, ss.regs x = ss'.regs x ∧
            okInT tb.ents (L₁ k) (ss.regs x) = true) →
          (T.halts = false ∨ ∀ x ∈ O₂, ss.regs x = ss'.regs x ∧
            okInT tb.ents (L₂ k) (ss.regs x) = true) := by
        intro hT hh
        cases hb : T.halts
        · exact Or.inl rfl
        · rw [hb] at hh
          have ho := hh.resolve_left (by simp)
          refine Or.inr fun v hv => ?_
          rcases hhalt (hrunG hT) hb v hv with hv1 | ⟨e1, e2, hvk⟩
          · exact ⟨(ho v hv1).1, okInT_mono hcov (ho v hv1).2⟩
          · rw [e1 ss g rfl, e2 ss' g' rfl]
            exact ⟨rfl, hreg v hvk⟩
      unfold blockOkR at h ⊢
      cases T
      case ret => rfl
      all_goals
        have hrun := hrunG (by simp)
        simp only [Bool.and_eq_true] at h ⊢
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        refine ⟨⟨guardsT_mono hcov h1, termAgreeT_mono hcov h2⟩, ?_⟩
        unfold exitAgreeT at h3 ⊢
        simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          beq_iff_eq] at h3 ⊢
        obtain ⟨⟨hs, hh⟩, ha⟩ := h3
        refine ⟨⟨fun j hj => ⟨fun v hv => ?_, ?_⟩, ?_⟩, fun q hq => ?_⟩
        · rcases hsucc hrun j hj v hv with hv1 | ⟨e1, e2, hvk⟩
          · exact ⟨((hs j hj).1 v hv1).1, okInT_mono hcov ((hs j hj).1 v hv1).2⟩
          · rw [e1 ss g rfl, e2 ss' g' rfl]
            exact ⟨rfl, hreg v hvk⟩
        · rw [hF j]
          rcases (hs j hj).2 with h0 | ⟨⟨⟨⟨⟨z1, z2⟩, c1⟩, c2⟩, o1'⟩, o2'⟩
          · exact Or.inl h0
          · exact Or.inr ⟨⟨⟨⟨⟨z1, okInFT_mono hcov z2⟩, c1⟩, okInT_mono hcov c2⟩, o1'⟩,
              okInT_mono hcov o2'⟩
        · exact hhaltG (by simp) hh
        · simp only [arrAgreeT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ha ⊢
          rcases ha q hq with ⟨e, o⟩ | ⟨e, o⟩
          · exact Or.inl ⟨e, okInAT_mono hcov o⟩
          · exact Or.inr ⟨e, okInAT_mono hcov o⟩

end Check

/-- The runs of the check keep, at the start word, a register that both bodies keep. -/
theorem runsOfC_keeps {y : String} {C C' : List LinstrRM} {G G' : CFG}
    (hK : KeepsReg y C) (hK' : KeepsReg y C') {k : Nat} {r : Tbl × SOut × SOut}
    (hR : (runsOfC (constAnnot C G symStep) (constAnnot C' G' symStep) C C' G G' symStep)[k]?
      = some r) :
    (∀ ss g, r.2.1 = .ok ss g → ss.regs y = .reg y) ∧
      (∀ ss g, r.2.2 = .ok ss g → ss.regs y = .reg y) := by
  simp only [runsOfC, Array.getElem?_map, Array.getElem?_range] at hR
  split at hR
  · simp only [Option.map_some, Option.some.injEq] at hR
    subst hR
    refine ⟨fun ss g h => ?_, fun ss g h => ?_⟩
    · exact tRun_keeps hK _ (fun i hi => mem_of_mem_bodyAt hi)
        (startC_regs_of_free (constAnnot_free hK k)) (Prod.ext rfl h)
    · exact tRun_keeps hK' _ (fun i hi => mem_of_mem_bodyAt hi)
        (startC_regs_of_free (constAnnot_free hK' k)) (Prod.ext rfl h)
  · cases hR

/-- **The checker with an entry set accepts more observed names that both bodies keep**:
    when every name of `O₂` outside `O₁` is a name of `Yp`, the runs of both bodies keep every
    name of `Yp` (`KeepsReg`), the entry set `ins₂` holds `ins₁` and every name of `Yp`, a pair
    that `ownedCheckMCIn ins₁ O₁` accepts is accepted by `ownedCheckMCIn ins₂ O₂`. -/
theorem ownedCheckMCIn_obs_mono {ins₁ ins₂ O₁ O₂ : List String} {Yp : String → Prop}
    {C C' : List LinstrRM} (hO : ∀ v ∈ O₁, v ∈ O₂) (hO2 : ∀ v ∈ O₂, v ∈ O₁ ∨ Yp v)
    (hK : ∀ y, Yp y → KeepsReg y C ∧ KeepsReg y C') (hins : ∀ v ∈ ins₁, v ∈ ins₂)
    (hent : ∀ v, Yp v → v ∈ ins₂) (h : ownedCheckMCIn ins₁ O₁ C C' = true) :
    ownedCheckMCIn ins₂ O₂ C C' = true := by
  unfold ownedCheckMCIn at h ⊢
  cases hG : cfgOf (C.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
  cases hG' : cfgOf (C'.map Prod.fst) with
  | none => simp [hG, hG'] at h
  | some G' =>
  simp only [hG, hG'] at h ⊢
  set R := runsOfC (annotAt (constAnnotArr C G symStep)) (annotAt (constAnnotArr C' G' symStep))
    C C' G G' symStep
    with hRdef
  have hsz : (Array.replicate G.blocks.size (([] : List String), false)).size =
      G.blocks.size := by simp
  rw [liveIter_eq_iterate O₁ C G R symDec _ _ hsz] at h
  rw [liveIter_eq_iterate O₂ C G R symDec _ _ hsz]
  have hY : ∀ (k : Nat) (r : Tbl × SOut × SOut) (ss : SSt) (g : List SG), R[k]? = some r →
      r.2.1 = .ok ss g → ∀ y, Yp y → ss.regs y = .reg y :=
    fun k r ss g hR h1 y hy => (runsOfC_keeps (hK y hy).1 (hK y hy).2 hR).1 ss g h1
  have hY' : ∀ (k : Nat) (r : Tbl × SOut × SOut) (ss : SSt) (g : List SG), R[k]? = some r →
      r.2.2 = .ok ss g → ∀ y, Yp y → ss.regs y = .reg y :=
    fun k r ss g hR h1 y hy => (runsOfC_keeps (hK y hy).1 (hK y hy).2 hR).2 ss g h1
  have rel := liveIt_rel (B := C) (G := G) (R := R) hO hO2 hY (4 * G.blocks.size + 64)
  set F := 4 * G.blocks.size + 64 with hFdef
  have hFlt : G.blocks.size < F := by omega
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem] at h ⊢
  obtain ⟨⟨⟨⟨⟨hW, hObl⟩, hf1⟩, hf2⟩, hEnt⟩, hFl⟩ := h
  have hL₁ : (fun L => liveRound O₁ C G R L symDec)^[F]
      (Array.replicate G.blocks.size ([], false)) = liveIt C G R O₁ F := rfl
  have hL₂ : (fun L => liveRound O₂ C G R L symDec)^[F]
      (Array.replicate G.blocks.size ([], false)) = liveIt C G R O₂ F := rfl
  rw [hL₁] at hW hObl hEnt hFl
  rw [hL₂]
  refine ⟨⟨⟨⟨⟨?_, oblCheckWith_mono (fun k => (rel k).1) hObl⟩, hf1⟩, hf2⟩, fun v hv => ?_⟩, ?_⟩
  · unfold ownedCheckWithR at hW ⊢
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hW ⊢
    obtain ⟨hne, hall⟩ := hW
    refine ⟨hne, fun k hk => ⟨(hall k hk).1, ?_⟩⟩
    have hb := (hall k hk).2
    cases hR : R[k]? with
    | none => rw [hR] at hb; cases hb
    | some r =>
      rw [hR] at hb
      simp only
      refine blockOkR_obs_mono (rel k).1 (fun j => (rel j).2.2.1) (fun hrun j hj v hv => ?_)
        (fun hrun hh v hv => ?_) hb
      · rcases (rel j).2.1 v hv with h1 | h1
        · exact Or.inl h1
        · have hyv := Yit_yp h1
          refine Or.inr ⟨fun ss g e => hY k r ss g hR e v hyv,
            fun ss g e => hY' k r ss g hR e v hyv, (rel k).2.2.2 v ?_⟩
          have h2 := Yit_stable hFlt h1
          rw [show F = F - 1 + 1 by omega]
          exact Or.inr ⟨hk, ⟨r, hR, hrun⟩, hyv, Or.inr ⟨j, hj, h2⟩⟩
      · rcases hO2 v hv with h1 | hyv
        · exact Or.inl h1
        · refine Or.inr ⟨fun ss g e => hY k r ss g hR e v hyv,
            fun ss g e => hY' k r ss g hR e v hyv, (rel k).2.2.2 v ?_⟩
          exact Yit_mono (n := 1) (by omega) (Or.inr ⟨hk, ⟨r, hR, hrun⟩, hyv, Or.inl ⟨hh, hv⟩⟩)
  · rcases (rel 0).2.1 v hv with h1 | h1
    · exact hins v (hEnt v h1)
    · exact hent v (Yit_yp h1)
  · rw [(rel 0).2.2.1]
    exact hFl

/-! ## 8. Monotonicity of the checks of the segments in the entry sets -/

section Seg

open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (cutAt exitI finI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck (calleeSegB segOutsAt)

theorem getD_getElem?_mem {α : Type} (L : List α) (d : α) (p : Nat) :
    (L[p]?).getD d ∈ L ∨ (L[p]?).getD d = d := by
  cases hp : L[p]? with
  | none => exact Or.inr rfl
  | some j => exact Or.inl (List.mem_of_getElem? hp)

/-- An instruction of a cut program is an instruction of the body, the jump to the label of
    the end, or the declaration of that label. -/
theorem mem_cutAt {fn : String} {fin : LLabel} {B : List LinstrRM} {e x : Option Nat}
    {i : LinstrRM} (h : i ∈ cutAt fn fin B e x) : i ∈ B ∨ i = exitI fn fin ∨ i = finI fin := by
  have hset : ∀ (q : Nat) (j : LinstrRM), j ∈ B.set q (exitI fn fin) →
      j ∈ B ∨ j = exitI fn fin ∨ j = finI fin := fun q j hj =>
    (List.mem_or_eq_of_mem_set hj).imp_right Or.inl
  have hget : ∀ (L : List LinstrRM) (d : LinstrRM), (∀ j ∈ L, j ∈ B ∨ j = exitI fn fin) →
      (d ∈ B ∨ d = exitI fn fin) → ∀ q, (L[q]?).getD d ∈ B ∨ (L[q]?).getD d = exitI fn fin :=
    fun L d hL hd q => (getD_getElem?_mem L d q).elim (fun h1 => hL _ h1)
      (fun h1 => by rw [h1]; exact hd)
  unfold cutAt at h
  cases x with
  | none =>
      cases e with
      | none =>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      | some p =>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with ((h | h) | h) | h | h
          · exact Or.inl (List.mem_of_mem_drop h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl (List.mem_of_mem_take h)
          · rw [h]
            exact (hget B (exitI fn fin) (fun j hj => Or.inl hj) (Or.inr rfl) p).imp_right Or.inl
          · exact Or.inr (Or.inr h)
  | some q =>
      have hB' : ∀ j ∈ B.set q (exitI fn fin), j ∈ B ∨ j = exitI fn fin :=
        fun j hj => List.mem_or_eq_of_mem_set hj
      have hO := hget B (exitI fn fin) (fun j hj => Or.inl hj) (Or.inr rfl) q
      cases e with
      | none =>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h
          · exact hset q i h
          · rw [h]; exact hO.imp_right Or.inl
          · exact Or.inr (Or.inr h)
      | some p =>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with ((h | h) | h) | h | h
          · exact hset q i (List.mem_of_mem_drop h)
          · rw [h]; exact hO.imp_right Or.inl
          · exact hset q i (List.mem_of_mem_take h)
          · rw [h]
            exact (hget _ _ hB' hO p).imp_right Or.inl
          · exact Or.inr (Or.inr h)

/-- **A cut program keeps the registers the body keeps.** -/
theorem keepsReg_cutAt {y fn : String} {fin : LLabel} {B : List LinstrRM} {e x : Option Nat}
    (h : KeepsReg y B) : KeepsReg y (cutAt fn fin B e x) := by
  intro i hi ss s gs hs
  rcases mem_cutAt hi with hi | rfl | rfl
  · exact h i hi ss s gs hs
  · simp [symStep, exitI, cmpArgs?, movRegArgs?, flagCondCC?] at hs
  · simp only [symStep, finI, cmpArgs?, movRegArgs?, flagCondCC?, SOut.ok.injEq] at hs
    rw [hs.1]

/-- **The checks of the segments are monotone in the entry sets at names that neither body
    writes.** For two entry sets `ins ⊆ ins'` such that both bodies keep every name of
    `ins' x` outside `ins x` (`KeepsReg`, from `regDefs` by `keepsReg_of_regDefs`) and every
    entry set `ins' e` holds such names, `calleeSegB` at `ins` implies `calleeSegB` at `ins'`.
    The added names are observed at the exits of the segments (`segOutsAt`): their words are
    the start words in both runs, so they add no refusal of the comparison of the exits, and
    the live sets of the checker grow only by them. -/
theorem calleeSegB_mono {T : LprogIsa.ProcTable} {fn : String} {fin : LLabel}
    {ins ins' : Option Nat → List String} {outs : List String} {ref img : List LinstrRM}
    (hsub : ∀ e, ∀ v ∈ ins e, v ∈ ins' e)
    (hK : ∀ v, (∃ x, v ∈ ins' x ∧ v ∉ ins x) → KeepsReg v ref ∧ KeepsReg v img)
    (hent : ∀ e v, (∃ x, v ∈ ins' x ∧ v ∉ ins x) → v ∈ ins' e)
    (h : calleeSegB T fn fin ins outs ref img = true) :
    calleeSegB T fn fin ins' outs ref img = true := by
  unfold calleeSegB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun e he x hx => ?_⟩
  refine ownedCheckMCIn_obs_mono (Yp := fun v => ∃ x, v ∈ ins' x ∧ v ∉ ins x)
    (fun v hv => ?_) (fun v hv => ?_) (fun y hy => ⟨keepsReg_cutAt (hK y hy).1,
      keepsReg_cutAt (hK y hy).2⟩) (hsub e) (fun v hv => hent e v hv) (h.2 e he x hx)
  · cases x with
    | none => exact hv
    | some p =>
        simp only [segOutsAt] at hv ⊢
        split at hv
        · simp only [List.mem_append, List.mem_filter] at hv ⊢
          exact hv.imp_right fun h => ⟨hsub _ v h.1, h.2⟩
        · exact hv
  · cases x with
    | none => exact Or.inl hv
    | some p =>
        simp only [segOutsAt] at hv ⊢
        split at hv
        · simp only [List.mem_append, List.mem_filter] at hv ⊢
          rcases hv with hv | ⟨hv1, hv2⟩
          · exact Or.inl (Or.inl hv)
          · by_cases hin : v ∈ ins (some p)
            · exact Or.inl (Or.inr ⟨hin, hv2⟩)
            · exact Or.inr ⟨some p, hv1, hin⟩
        · exact Or.inl hv

end Seg

/-! ## 9. The cached registers of a term table, bounded from above

`TblOK σ E` bounds the cached registers of an entry from below by the registers of the word
`σ` gives it. The needs of the checker (`blockNeed`) read the cached registers, so their
bound needs the converse, `VarsUB`: the cached registers of every entry are registers of
its word. Interning keeps both bounds for one substitution (`tRun_validU`). -/

section Upper

/-- **The cached registers of the entries of `E` are registers of the words `σ` gives
    them.** -/
def VarsUB (σ : Nat → STerm) (E : Array TEnt) : Prop :=
  ∀ k (h : k < E.size), ∀ v ∈ E[k].vars, v ∈ (σ k).vars

variable {σ : Nat → STerm} {E : Array TEnt}

mutual
/-- The registers a word over a table reads are registers of its substitution instance. -/
theorem STerm.varsT_sub_subst (h : VarsUB σ E) :
    ∀ (t : STerm), ∀ v ∈ t.varsT E, v ∈ (t.subst σ).vars
  | .reg _, v, hv => by simpa [STerm.subst, STerm.vars, STerm.varsT] using hv
  | .immW _ _, v, hv => by simp [STerm.varsT] at hv
  | .immAt _ x, v, hv => STerm.varsT_sub_subst h x v (by simpa [STerm.varsT] using hv)
  | .bin _ x y, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v)
  | .un _ x, v, hv => STerm.varsT_sub_subst h x v (by simpa [STerm.varsT] using hv)
  | .shImm _ _ x, v, hv => STerm.varsT_sub_subst h x v (by simpa [STerm.varsT] using hv)
  | .aget a _ _ i, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (SArr.varsT_sub_subst h a v) (STerm.varsT_sub_subst h i v)
  | .cin _, v, hv => by simp [STerm.varsT] at hv
  | .aluF _ _ x y o, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v))
        (STerm.varsT_sub_subst h o v)
  | .carryW _ x y c, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v))
        (STerm.varsT_sub_subst h c v)
  | .carryF _ _ x y c, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v))
        (STerm.varsT_sub_subst h c v)
  | .mulx _ x y, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v)
  | .cout _ x y c, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v))
        (STerm.varsT_sub_subst h c v)
  | .sel x y c, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (Or.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v))
        (STerm.varsT_sub_subst h c v)
  | .setcc _ x y, v, hv => by
      simp only [STerm.varsT, List.mem_append] at hv
      simp only [STerm.subst, STerm.vars, List.mem_append]
      exact hv.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v)
  | .ref k, v, hv => by
      simp only [STerm.varsT, STerm.subst] at hv ⊢
      rcases Nat.lt_or_ge k E.size with hk | hk
      · rw [Array.getElem?_eq_getElem hk, Option.map_some, Option.getD_some] at hv
        exact h k hk v hv
      · rw [Array.getElem?_eq_none hk] at hv
        simp at hv

/-- The registers an array over a table reads are registers of its substitution
    instance. -/
theorem SArr.varsT_sub_subst (h : VarsUB σ E) :
    ∀ (a : SArr), ∀ v ∈ a.varsT E, v ∈ (a.subst σ).vars
  | .cell _, v, hv => by simp [SArr.varsT] at hv
  | .aset a _ _ i x, v, hv => by
      simp only [SArr.varsT, List.mem_append] at hv
      simp only [SArr.subst, SArr.vars, List.mem_append]
      exact hv.imp (Or.imp (SArr.varsT_sub_subst h a v) (STerm.varsT_sub_subst h i v))
        (STerm.varsT_sub_subst h x v)
  | .zero _ _, v, hv => by simp [SArr.varsT] at hv
end

theorem SFlag.varsT_sub_subst (h : VarsUB σ E) (f : SFlag) :
    ∀ v ∈ f.varsT E, v ∈ (f.subst σ).vars := by
  intro v hv
  cases f with
  | init => simp [SFlag.varsT] at hv
  | cmp x y =>
      simp only [SFlag.varsT, List.mem_append] at hv
      simp only [SFlag.subst, SFlag.vars, List.mem_append]
      exact hv.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v)

theorem SG.varsT_sub_subst (h : VarsUB σ E) (g : SG) :
    ∀ v ∈ g.varsT E, v ∈ (g.subst σ).vars := by
  intro v hv
  cases g with
  | wid t w => exact STerm.varsT_sub_subst h t v hv
  | eqW x y =>
      simp only [SG.varsT, List.mem_append] at hv
      simp only [SG.subst, SG.vars, List.mem_append]
      exact hv.imp (STerm.varsT_sub_subst h x v) (STerm.varsT_sub_subst h y v)
  | shp a w n => exact SArr.varsT_sub_subst h a v hv

mutual
/-- The registers of a word are registers it reads over every table. -/
theorem STerm.vars_sub_varsT (E : Array TEnt) :
    ∀ (t : STerm), ∀ v ∈ t.vars, v ∈ t.varsT E
  | .reg _, v, hv => hv
  | .immW _ _, v, hv => by simp [STerm.vars] at hv
  | .immAt _ x, v, hv => STerm.vars_sub_varsT E x v hv
  | .bin _ x y, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v)
  | .un _ x, v, hv => STerm.vars_sub_varsT E x v hv
  | .shImm _ _ x, v, hv => STerm.vars_sub_varsT E x v hv
  | .aget a _ _ i, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (SArr.vars_sub_varsT E a v) (STerm.vars_sub_varsT E i v)
  | .cin _, v, hv => by simp [STerm.vars] at hv
  | .aluF _ _ x y o, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v))
        (STerm.vars_sub_varsT E o v)
  | .carryW _ x y c, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v))
        (STerm.vars_sub_varsT E c v)
  | .carryF _ _ x y c, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v))
        (STerm.vars_sub_varsT E c v)
  | .mulx _ x y, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v)
  | .cout _ x y c, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v))
        (STerm.vars_sub_varsT E c v)
  | .sel x y c, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (Or.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v))
        (STerm.vars_sub_varsT E c v)
  | .setcc _ x y, v, hv => by
      simp only [STerm.vars, List.mem_append] at hv
      simp only [STerm.varsT, List.mem_append]
      exact hv.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v)
  | .ref _, v, hv => by simp [STerm.vars] at hv

/-- The registers of an array are registers it reads over every table. -/
theorem SArr.vars_sub_varsT (E : Array TEnt) :
    ∀ (a : SArr), ∀ v ∈ a.vars, v ∈ a.varsT E
  | .cell _, v, hv => by simp [SArr.vars] at hv
  | .aset a _ _ i x, v, hv => by
      simp only [SArr.vars, List.mem_append] at hv
      simp only [SArr.varsT, List.mem_append]
      exact hv.imp (Or.imp (SArr.vars_sub_varsT E a v) (STerm.vars_sub_varsT E i v))
        (STerm.vars_sub_varsT E x v)
  | .zero _ _, v, hv => by simp [SArr.vars] at hv
end

theorem SFlag.vars_sub_varsT (E : Array TEnt) (f : SFlag) :
    ∀ v ∈ f.vars, v ∈ f.varsT E := by
  intro v hv
  cases f with
  | init => simp [SFlag.vars] at hv
  | cmp x y =>
      simp only [SFlag.vars, List.mem_append] at hv
      simp only [SFlag.varsT, List.mem_append]
      exact hv.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v)

theorem SG.vars_sub_varsT (E : Array TEnt) (g : SG) :
    ∀ v ∈ g.vars, v ∈ g.varsT E := by
  intro v hv
  cases g with
  | wid t w => exact STerm.vars_sub_varsT E t v hv
  | eqW x y =>
      simp only [SG.vars, List.mem_append] at hv
      simp only [SG.varsT, List.mem_append]
      exact hv.imp (STerm.vars_sub_varsT E x v) (STerm.vars_sub_varsT E y v)
  | shp a w n => exact SArr.vars_sub_varsT E a v hv

/-- The width base of a word reads only registers the word reads. -/
theorem STerm.wbase_vars : ∀ (t : STerm), ∀ v ∈ t.wbase.vars, v ∈ t.vars
  | .immAt _ x, v, hv => STerm.wbase_vars x v hv
  | .bin _ x _, v, hv => by
      simp only [STerm.vars, List.mem_append]
      exact Or.inl (STerm.wbase_vars x v hv)
  | .un _ x, v, hv => STerm.wbase_vars x v hv
  | .shImm _ _ x, v, hv => STerm.wbase_vars x v hv
  | .sel x _ _, v, hv => by
      simp only [STerm.vars, List.mem_append]
      exact Or.inl (Or.inl (STerm.wbase_vars x v hv))
  | .reg _, _, hv => hv
  | .immW _ _, _, hv => hv
  | .aget _ _ _ _, _, hv => hv
  | .cin _, _, hv => hv
  | .aluF _ _ _ _ _, _, hv => hv
  | .carryW _ _ _ _, _, hv => hv
  | .carryF _ _ _ _ _, _, hv => hv
  | .mulx _ _ _, _, hv => hv
  | .cout _ _ _ _, _, hv => hv
  | .setcc _ _ _, _, hv => hv
  | .ref _, _, hv => hv

/-- **A normal form of a guard reads only registers the guard reads.** -/
theorem SG.norm_vars (g : SG) : ∀ g' ∈ g.norm, ∀ v ∈ g'.vars, v ∈ g.vars := by
  intro g' hg' v hv
  cases g with
  | wid t w =>
      simp only [SG.norm] at hg'
      split at hg'
      · split at hg'
        · simp at hg'
        · simp only [List.mem_singleton] at hg'
          subst hg'
          simp [SG.falseG, SG.vars, STerm.vars] at hv
      · simp only [List.mem_singleton] at hg'
        subst hg'
        exact STerm.wbase_vars t v hv
  | eqW x y =>
      simp only [SG.norm] at hg'
      split at hg'
      · split at hg'
        · simp at hg'
        · simp only [List.mem_singleton] at hg'
          subst hg'
          simp [SG.falseG, SG.vars, STerm.vars] at hv
      · simp only [List.mem_singleton] at hg'
        subst hg'
        simp only [SG.vars, List.mem_append] at hv ⊢
        exact hv.imp (STerm.wbase_vars x v) (STerm.wbase_vars y v)
  | shp a w n =>
      simp only [SG.norm, List.mem_singleton] at hg'
      subst hg'
      exact hv

/-- A table that some substitution agrees with and bounds from above (`VarsUB`), and whose
    entries read only its own entries. -/
def TValidU (E : Array TEnt) : Prop := (∃ σ, TblOK σ E ∧ VarsUB σ E) ∧ TBnd E

theorem tValidU_empty : TValidU #[] :=
  ⟨⟨fun k => .ref k, fun k h => by simp at h, fun k h => by simp at h⟩,
    fun k h => by simp at h⟩

theorem TValidU.valid {E : Array TEnt} (h : TValidU E) : TValid E :=
  ⟨h.1.elim fun σ hσ => ⟨σ, hσ.1⟩, h.2⟩

theorem TValidU.push {E : Array TEnt} (hv : TValidU E) {n : STerm}
    (hn : n.refsLt E.size = true) : TValidU (E.push (mkEnt E n)) := by
  obtain ⟨⟨σ, hσ, hU⟩, hb⟩ := hv
  let σ' : Nat → STerm := fun j => if j = E.size then n.subst σ else σ j
  have hag : ∀ k, k < E.size → σ k = σ' k := fun k hk => by
    simp only [σ', ite_eq_right (Nat.ne_of_lt hk)]
  have hwb := STerm.wbT_refsLt hb n hn
  have e : σ' E.size = n.subst σ := by simp [σ']
  refine ⟨⟨σ', fun k hk => ?_, fun k hk v hv => ?_⟩, (TValid.push ⟨⟨σ, hσ⟩, hb⟩ hn).2⟩
  · rw [Array.size_push] at hk
    rcases Nat.lt_or_ge k E.size with hk' | hk'
    · rw [Array.getElem_push_lt hk']
      obtain ⟨h1, h2, h3, h4, h5⟩ := hσ k hk'
      have e' : σ' k = σ k := (hag k hk').symm
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [e', h1]; exact STerm.subst_congr hag _ (hb k hk').1
      · rw [e']; exact h2
      · rw [e']; exact h3
      · rw [e', h4]; exact STerm.subst_congr hag _ (hb k hk').2
      · rw [e']; exact h5
    · have hk2 : k = E.size := by omega
      subst hk2
      rw [Array.getElem_push_eq]
      obtain ⟨w1, w2⟩ := STerm.wbT_spec hσ n hn
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [e]; exact STerm.subst_congr hag _ hn
      · intro v hv
        rw [e] at hv
        exact List.mem_eraseDups.mpr (STerm.varsT_spec hσ n hn v hv)
      · intro hf
        rw [e] at hf
        exact STerm.readsFT_spec hσ n hn hf
      · rw [e, w1]; exact STerm.subst_congr hag _ hwb
      · rw [e]; exact w2
  · rw [Array.size_push] at hk
    rcases Nat.lt_or_ge k E.size with hk' | hk'
    · rw [Array.getElem_push_lt hk'] at hv
      rw [← hag k hk']
      exact hU k hk' v hv
    · have hk2 : k = E.size := by omega
      subst hk2
      rw [Array.getElem_push_eq] at hv
      rw [e]
      exact STerm.varsT_sub_subst hU n v (List.mem_eraseDups.mp hv)

theorem Tbl.push_validU {T : Tbl} (hv : TValidU T.ents) (n : STerm) :
    TValidU (T.push n).1.ents := by
  unfold Tbl.push
  split
  · exact hv.push (by assumption)
  · exact hv

theorem Tbl.share_validU {T : Tbl} (hv : TValidU T.ents) (n : STerm) :
    TValidU (T.share n).1.ents := by
  unfold Tbl.share
  split
  · split
    · exact hv
    · exact Tbl.push_validU hv n
  · exact Tbl.push_validU hv n

theorem Tbl.intern_validU : ∀ (T : Tbl) (t : STerm), TValidU T.ents →
    TValidU (T.intern t).1.ents
  | T, .immAt _ x, hv => Tbl.share_validU (Tbl.intern_validU T x hv) _
  | T, .bin _ x y, hv =>
      Tbl.share_validU (Tbl.intern_validU _ y (Tbl.intern_validU T x hv)) _
  | T, .un _ x, hv => Tbl.share_validU (Tbl.intern_validU T x hv) _
  | T, .shImm _ _ x, hv => Tbl.share_validU (Tbl.intern_validU T x hv) _
  | T, .aget _ _ _ i, hv => Tbl.share_validU (Tbl.intern_validU T i hv) _
  | T, .aluF _ _ x y o, hv =>
      Tbl.share_validU
        (Tbl.intern_validU _ o (Tbl.intern_validU _ y (Tbl.intern_validU T x hv))) _
  | T, .carryW _ x y c, hv =>
      Tbl.share_validU
        (Tbl.intern_validU _ c (Tbl.intern_validU _ y (Tbl.intern_validU T x hv))) _
  | T, .carryF _ _ x y c, hv =>
      Tbl.share_validU
        (Tbl.intern_validU _ c (Tbl.intern_validU _ y (Tbl.intern_validU T x hv))) _
  | T, .mulx _ x y, hv =>
      Tbl.share_validU (Tbl.intern_validU _ y (Tbl.intern_validU T x hv)) _
  | T, .cout _ x y c, hv =>
      Tbl.share_validU
        (Tbl.intern_validU _ c (Tbl.intern_validU _ y (Tbl.intern_validU T x hv))) _
  | T, .sel x y c, hv =>
      Tbl.share_validU
        (Tbl.intern_validU _ c (Tbl.intern_validU _ y (Tbl.intern_validU T x hv))) _
  | T, .setcc _ x y, hv =>
      Tbl.share_validU (Tbl.intern_validU _ y (Tbl.intern_validU T x hv)) _
  | _, .reg _, hv => hv
  | _, .immW _ _, hv => hv
  | _, .cin _, hv => hv
  | _, .ref _, hv => hv

theorem Tbl.internRegs_validU : ∀ (T : Tbl) (ss : SSt) (ds : List String), TValidU T.ents →
    TValidU (T.internRegs ss ds).1.ents
  | _, _, [], hv => hv
  | T, ss, d :: ds, hv => Tbl.internRegs_validU _ _ ds (Tbl.intern_validU T (ss.regs d) hv)

theorem Tbl.internSt_validU {T : Tbl} (hv : TValidU T.ents) (ss : SSt) (ds : List String) :
    TValidU (T.internSt ss ds).1.ents :=
  Tbl.intern_validU _ _ (Tbl.intern_validU _ _ (Tbl.internRegs_validU T ss ds hv))

/-- **The shared run keeps a substitution that bounds the table from both sides.** -/
theorem tRun_validU (sym : LinstrRM → SSt → SOut) :
    ∀ (is : List LinstrRM) (ss : SSt) (T : Tbl), TValidU T.ents →
    TValidU (tRun is ss T sym).1.ents
  | [], _, _, hv => hv
  | i :: is, ss, T, hv => by
      simp only [tRun]
      split
      · rename_i ss1 _ _
        have := tRun_validU sym is
          (T.internSt ss1 (ss1.newWr ss)).2 _
          (Tbl.internSt_validU hv ss1 (ss1.newWr ss))
        split <;> exact this
      · exact hv
      · exact hv

end Upper

/-! ## 10. A table of names closed along a body bounds the live sets

A table `A` of names over the positions of a body `C` is closed (`TabClosed`) when it
transfers every symbolic step from the names at a position to the names at the next one,
covers the names at the target of every jump, the names after every conditional jump (which
tests the zero flag), and the observed names at the end. The names of `A` at the starts of
the blocks, with the flags live, are then a post-fixpoint of `liveRound` on the shared runs
(`livePost_tab`) as soon as the image guards of every block are among its reference guards,
so the live sets of the checker lie below them (`liveIter_entry_sub`). -/

section Closed

open SymFootprint (ReadsIn)

/-- **The table `A` over the positions of `C` transfers the symbolic step at `j`**: a
    successful step of the instruction at `j` from a state whose words at the names of
    `A j`, arrays and flags read within `X` ends in a state whose words at the names of
    `A (j + 1)`, arrays and flags read within `X`, with guards that read within `X`. -/
def StepTr (C : List LinstrRM) (A : Nat → List String) (j : Nat) : Prop :=
  ∀ i, C[j]? = some i → ∀ (E : Array TEnt) (X : String → Prop) (ss s : SSt) (gs : List SG),
    symStep i ss = .ok s gs → ReadsIn E X (· ∈ A j) ss →
      ReadsIn E X (· ∈ A (j + 1)) s ∧ ∀ g ∈ gs, ∀ v ∈ g.varsT E, X v

/-- **The table `A` of names over the positions of `C` is closed for the observed names
    `O`**: it transfers every symbolic step; the names at the label of a jump are names at
    the jump; a conditional jump tests the zero flag and the names after it are names at
    it; and the names `O` are names at the end of `C`. -/
structure TabClosed (C : List LinstrRM) (O : List String) (A : Nat → List String) : Prop where
  /-- Every step transfers. -/
  step : ∀ j, StepTr C A j
  /-- The names at the label of a jump. -/
  jump : ∀ j i l p, C[j]? = some i → JasminLsemExportRegAlloc.jumpLabel? i.1 = some l →
    JasminLsemMemLoop.findLabelMem l C = some p → ∀ y ∈ A p, y ∈ A j
  /-- A conditional jump tests the zero flag and keeps the names after it. -/
  cond : ∀ j c l tag, C[j]? = some (.Lcond c l, tag) →
    (ccPol c).isSome = true ∧ ∀ y ∈ A (j + 1), y ∈ A j
  /-- The observed names at the end. -/
  out : ∀ y ∈ O, y ∈ A C.length

/-- **A run along a closed table**: the run of the instructions of `C` from position `a`
    reads, at the names of the table at its end, only start registers that the words at the
    names of the table at `a` read. -/
theorem symRun_tab {C : List LinstrRM} {A : Nat → List String} {E : Array TEnt}
    {X : String → Prop} (hT : ∀ j, StepTr C A j) :
    ∀ (is : List LinstrRM) (a : Nat) {ss s : SSt} {gs : List SG},
      (∀ j (hj : j < is.length), C[a + j]? = some is[j]) →
      ReadsIn E X (· ∈ A a) ss → symRun is ss = .ok s gs →
      ReadsIn E X (· ∈ A (a + is.length)) s ∧ ∀ g ∈ gs, ∀ v ∈ g.varsT E, X v
  | [], a, ss, s, gs, _, hX, h => by
      simp only [symRun, SOut.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simpa using hX, fun g hg => by simp at hg⟩
  | i :: is, a, ss, s, gs, hC, hX, h => by
      simp only [symRun] at h
      split at h
      · rename_i ss1 g1 h1
        split at h
        · rename_i ss2 g2 h2
          simp only [SOut.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have h0 : C[a]? = some i := by
            have := hC 0 (by simp)
            rwa [Nat.add_zero, List.getElem_cons_zero] at this
          have hX1 := hT a i h0 E X ss ss1 g1 h1 hX
          have ih := symRun_tab hT is (a + 1) (fun j hj => by
              have := hC (j + 1) (by simp only [List.length_cons]; omega)
              rw [show a + 1 + j = a + (j + 1) by omega, this, List.getElem_cons_succ]) hX1.1 h2
          have e : a + (i :: is).length = a + 1 + is.length := by
            simp only [List.length_cons]; omega
          rw [e]
          refine ⟨ih.1, fun g hg => ?_⟩
          rcases List.mem_append.mp hg with hg | hg
          · exact hX1.2 g hg
          · exact ih.2 g hg
        · cases h
        · cases h
      · cases h
      · cases h

/-- The start of a block with facts reads, at every name of a list, only that name. -/
theorem readsIn_startC (E : Array TEnt) (N : List String) (fs : List CFact) :
    ReadsIn E (· ∈ N) (· ∈ N) (startC fs) := by
  refine ⟨fun r hr v hv => ?_, fun a v hv => ?_, fun v hv => ?_, fun v hv => ?_,
    fun v hv => ?_⟩
  · rw [startC_regs] at hv
    split at hv
    · simp [STerm.varsT] at hv
    · simp only [STerm.varsT, List.mem_singleton] at hv
      subst hv
      exact hr
  · simp [startC, SArr.varsT] at hv
  · simp [startC, SFlag.varsT] at hv
  · simp [startC, STerm.varsT] at hv
  · simp [startC, STerm.varsT] at hv

/-- **The reads of the reference run of a block pair, over the shared table**: when the
    table `A` transfers every step and the reference run of block `b` succeeds, the words
    of its final state at the names of the table at the end of the body of the block, its
    arrays, its flags and its normalised guards read, over the shared table, only names of
    the table at the start of the block. -/
theorem runs_fp {fs fs' : List CFact} {C C' : List LinstrRM} {b b' : Block} {T : Term}
    {A : Nat → List String} (hT : ∀ j, StepTr C A j) (hle : bstopOf T b ≤ C.length)
    (hst : b.start ≤ bstopOf T b) {ss : SSt} {gs : List SG}
    (h : (blockRunsS (startC fs) (startC fs') C C' b b' T).2.1 = .ok ss gs) :
    (∀ r ∈ A (bstopOf T b), ∀ v ∈ (ss.regs r).varsT
        (blockRunsS (startC fs) (startC fs') C C' b b' T).1.ents, v ∈ A b.start) ∧
    (∀ q, ∀ v ∈ (ss.arrs q).varsT
        (blockRunsS (startC fs) (startC fs') C C' b b' T).1.ents, v ∈ A b.start) ∧
    (∀ v ∈ ss.zf.varsT (blockRunsS (startC fs) (startC fs') C C' b b' T).1.ents,
        v ∈ A b.start) ∧
    (∀ v ∈ ss.cf.varsT (blockRunsS (startC fs) (startC fs') C C' b b' T).1.ents,
        v ∈ A b.start) ∧
    (∀ v ∈ ss.of.varsT (blockRunsS (startC fs) (startC fs') C C' b b' T).1.ents,
        v ∈ A b.start) ∧
    (gs.all (SG.refsLt (blockRunsS (startC fs) (startC fs') C C' b b' T).1.ents.size) = true →
      ∀ g ∈ normGT (blockRunsS (startC fs) (startC fs') C C' b b' T).1.ents gs,
        ∀ v ∈ g.varsT (blockRunsS (startC fs) (startC fs') C C' b b' T).1.ents,
          v ∈ A b.start) := by
  generalize hR : blockRunsS (startC fs) (startC fs') C C' b b' T = R at h ⊢
  have hv : TValidU R.1.ents := by
    rw [← hR]
    exact tRun_validU symStep _ _ _ (tRun_validU symStep _ _ _ tValidU_empty)
  obtain ⟨⟨σ, hσ, hU⟩, -⟩ := hv
  have e1 : symRun (bodyAt C b T) (startC fs) = R.2.1.subst σ := by
    have h1 := tRun_subst hσ (bodyAt C b T) (startC fs) Tbl.empty
      (by rw [← hR]; exact tRun_ext_at symStep _ _ _)
    rw [startC_subst σ] at h1
    rw [← hR]
    exact h1.symm
  rw [h] at e1
  simp only [SOut.subst] at e1
  have hlen : b.start + (bodyAt C b T).length = bstopOf T b := by
    simp only [bodyAt, List.length_take, List.length_drop]
    omega
  have fp := symRun_tab (E := #[]) (X := (· ∈ A b.start)) hT (bodyAt C b T) b.start
    (fun j hj => by
      simp only [bodyAt, List.getElem_take, List.getElem_drop]
      rw [List.getElem?_eq_getElem])
    (readsIn_startC #[] (A b.start) fs) e1
  rw [hlen] at fp
  obtain ⟨⟨fr, fa, fz, fc, fo⟩, fg⟩ := fp
  refine ⟨fun r hr v hv => ?_, fun q v hv => ?_, fun v hv => ?_, fun v hv => ?_,
    fun v hv => ?_, fun hb g hg v hv => ?_⟩
  · have h1 := STerm.varsT_sub_subst hU _ v hv
    rw [← SSt.subst_regs_apply] at h1
    exact fr r hr v (STerm.vars_sub_varsT #[] _ v h1)
  · exact fa q v (SArr.vars_sub_varsT #[] _ v (SArr.varsT_sub_subst hU _ v hv))
  · exact fz v (SFlag.vars_sub_varsT #[] _ v (SFlag.varsT_sub_subst hU _ v hv))
  · exact fc v (STerm.vars_sub_varsT #[] _ v (STerm.varsT_sub_subst hU _ v hv))
  · exact fo v (STerm.vars_sub_varsT #[] _ v (STerm.varsT_sub_subst hU _ v hv))
  · have h1 := SG.varsT_sub_subst hU g v hv
    have hm : g.subst σ ∈ normG (gs.map (SG.subst σ)) := by
      rw [← normGT_subst hσ gs hb]
      exact List.mem_map_of_mem hg
    simp only [normG, List.mem_flatMap] at hm
    obtain ⟨g0, hg0, hn⟩ := hm
    exact fg g0 hg0 v (SG.vars_sub_varsT #[] g0 v (SG.norm_vars g0 _ hn v h1))

/-- The live sets of the table `A` at the starts of the blocks of `G`, with the flags
    live. -/
def tabLive (G : CFG) (A : Nat → List String) : Array (List String × Bool) :=
  (Array.range G.blocks.size).map fun k => (A (G.blk k).start, true)

theorem tabLive_getD (G : CFG) (A : Nat → List String) {k : Nat} (hk : k < G.blocks.size) :
    (tabLive G A).getD k ([], false) = (A (G.blk k).start, true) := by
  rw [tabLive, getD_map_range, ite_eq_left hk]

/-- **The image guards of the shared runs `r` are among the reference guards**, and all
    guards read only entries of the table. -/
def GuardsIn (r : Tbl × SOut × SOut) : Prop :=
  ∀ ss gs ss' gs', r.2.1 = .ok ss gs → r.2.2 = .ok ss' gs' →
    (gs ++ gs').all (SG.refsLt r.1.ents.size) = true ∧
      ∀ g ∈ normGT r.1.ents gs', g ∈ normGT r.1.ents gs

/-- The block check gives the guard containment. -/
theorem guardsIn_of_blockOkR {O : List String} {L : Nat → List String × Bool} {k : Nat}
    {T : Term} {r : Tbl × SOut × SOut} {C C' : List LinstrRM} {b b' : Block}
    (h : blockOkR O L k T r C C' b b' = true) (hT : T ≠ .ret) : GuardsIn r := by
  intro ss gs ss' gs' h1 h2
  unfold blockOkR at h
  split at h
  · exact absurd rfl hT
  · rw [h1, h2] at h
    simp only [Bool.and_eq_true] at h
    have hg := h.1.1
    simp only [guardsT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hg
    exact ⟨List.all_eq_true.mpr hg.1, fun g hgm => (hg.2 g hgm).1⟩

/-- **The block structure against a closed table**: the body of block `k` lies in `C`;
    the names at the start of every successor are names at the end of the body; at a halt
    the observed names are names at the end of the body; and a conditional terminator
    tests the zero flag. -/
theorem block_tab {C : List LinstrRM} {O : List String} {G : CFG}
    (hG : cfgOf (C.map Prod.fst) = some G) {A : Nat → List String} (hA : TabClosed C O A)
    {k : Nat} (hk : k < G.blocks.size) :
    bstopOf (G.blk k).term (G.blk k) ≤ C.length ∧
    (G.blk k).start ≤ bstopOf (G.blk k).term (G.blk k) ∧
    (∀ j ∈ (G.blk k).term.succs, j < G.blocks.size ∧
      ∀ y ∈ A (G.blk j).start, y ∈ A (bstopOf (G.blk k).term (G.blk k))) ∧
    ((G.blk k).term.halts = true → ∀ y ∈ O, y ∈ A (bstopOf (G.blk k).term (G.blk k))) ∧
    (∀ t nx c l tag, (G.blk k).term = .cond t nx →
      C[(G.blk k).stop - 1]? = some (.Lcond c l, tag) → (ccPol c).isSome = true) := by
  have bf := blockFacts hG hk
  have hlen : (C.map Prod.fst).length = C.length := List.length_map _
  have hs1 : (G.blk k).stop - 1 < C.length := by
    have := bf.lt; have := bf.le; omega
  obtain ⟨i, hi⟩ : ∃ i, C[(G.blk k).stop - 1]? = some i :=
    ⟨_, List.getElem?_eq_getElem hs1⟩
  have hiw : (C.map Prod.fst)[(G.blk k).stop - 1]? = some i.1 := by
    rw [List.getElem?_map, hi]; rfl
  have ht := bf.term
  rw [hiw] at ht
  have hnx : ∀ j, G.next k = some j → j < G.blocks.size ∧ (G.blk j).start = (G.blk k).stop := by
    intro j hj
    have e := bf.stop_eq
    unfold CFG.next at hj
    split at hj
    · cases hj
      refine ⟨by assumption, ?_⟩
      rw [e, CFG.nextStart, CFG.next, ite_eq_left (by assumption)]
    · cases hj
  have hnone : G.next k = none → (G.blk k).stop = C.length := by
    intro hj
    rw [bf.stop_eq, CFG.nextStart, hj, hlen]
  have hlt := bf.lt
  have hle := bf.le
  rw [hlen] at hle
  rcases termOk_spec ht with ⟨nx, hT, -, hn⟩ | ⟨t, x, l, hT, hiT, htl, hf⟩ |
      ⟨t, nx, c, l, hT, hiT, htl, hf, hn⟩ | ⟨hT, -⟩
  · rw [hT]
    simp only [bstopOf]
    refine ⟨hle, by omega, fun j hj => ?_, fun hh y hy => ?_, fun _ _ _ _ _ he => by cases he⟩
    · cases nx with
      | none => simp [Term.succs] at hj
      | some j' =>
          simp only [Term.succs, Option.toList_some, List.mem_singleton] at hj
          subst hj
          obtain ⟨h1, h2⟩ := hnx _ hn.symm
          exact ⟨h1, fun y hy => by rw [← h2]; exact hy⟩
    · cases nx with
      | none => rw [hnone hn.symm]; exact hA.out y hy
      | some _ => simp [Term.halts] at hh
  · rw [hT]
    simp only [bstopOf, Term.succs, List.mem_singleton, Term.halts]
    refine ⟨by omega, by omega, fun j hj => ?_, (fun hh => by cases hh),
      fun _ _ _ _ _ he => by cases he⟩
    subst hj
    refine ⟨htl, fun y hy => hA.jump _ i l _ hi (by rw [hiT]; rfl) hf y hy⟩
  · rw [hT]
    obtain ⟨w, tag⟩ := i
    simp only at hiT
    subst hiT
    have hc := hA.cond _ c l tag hi
    have hst : (G.blk k).stop - 1 + 1 = (G.blk k).stop := by omega
    rw [hst] at hc
    simp only [bstopOf, Term.succs, List.mem_cons]
    refine ⟨by omega, by omega, fun j hj => ?_, fun hh y hy => ?_, fun _ _ c' l' tag' _ he => ?_⟩
    · rcases hj with rfl | hj
      · exact ⟨htl, fun y hy => hA.jump _ _ l _ hi rfl hf y hy⟩
      · cases nx with
        | none => simp at hj
        | some j' =>
            simp only [Option.toList_some, List.mem_singleton] at hj
            subst hj
            obtain ⟨h1, h2⟩ := hnx _ hn.symm
            exact ⟨h1, fun y hy => hc.2 y (by rw [← h2]; exact hy)⟩
    · cases nx with
      | none => exact hc.2 y (by rw [hnone hn.symm]; exact hA.out y hy)
      | some _ => simp [Term.halts] at hh
    · rw [hi] at he
      cases he
      exact hc.1
  · rw [hT]
    simp only [bstopOf, Term.succs, List.not_mem_nil, Term.halts]
    exact ⟨by omega, by omega, fun j hj => hj.elim, (fun hh => by cases hh),
      fun _ _ _ _ _ he => by cases he⟩

/-- **The table at the starts of the blocks is a post-fixpoint of `liveRound`.** For a
    table `A` closed along `C` for the observed names `O`, and shared runs whose image
    guards are among their reference guards at every block that does not return, the names
    of `A` at the starts of the blocks of `G`, with the flags live, cover what every block
    needs. -/
theorem livePost_tab {C C' : List LinstrRM} {O : List String} {G G' : CFG}
    (hG : cfgOf (C.map Prod.fst) = some G) {A : Nat → List String} (hA : TabClosed C O A)
    {F F' : Nat → List CFact}
    (hgd : ∀ k r, (runsOfC F F' C C' G G' symStep)[k]? = some r → (G.blk k).term ≠ .ret →
      GuardsIn r) :
    LivePost O C G (runsOfC F F' C C' G G' symStep) (tabLive G A) := by
  intro k hk
  rw [tabLive_getD G A hk]
  obtain ⟨hle, hst, hsucc, hhalt, hcond⟩ := block_tab hG hA hk
  have hRk : (runsOfC F F' C C' G G' symStep)[k]? = some (blockRunsS (startC (F k))
      (startC (F' k)) C C' (G.blk k) (G'.blk k) (G.blk k).term) := by
    simp [runsOfC, hk]
  have hgk := hgd k _ hRk
  unfold needAt
  rw [hRk]
  dsimp only
  refine ⟨fun v hv => ?_, fun _ => rfl⟩
  generalize hR : blockRunsS (startC (F k)) (startC (F' k)) C C' (G.blk k) (G'.blk k)
    (G.blk k).term = R at hv hgk
  have fp := fun ss gs (h : R.2.1 = .ok ss gs) =>
    runs_fp (fs' := F' k) (C' := C') (b' := G'.blk k) hA.step hle hst (hR ▸ h)
  unfold blockNeed at hv
  split at hv
  · simp at hv
  · rename_i hT
    split at hv
    · rename_i ss gs1 ss' gs' h1 h2
      obtain ⟨fr, fa, fz, fc, fo, fg⟩ := fp ss gs1 h1
      rw [hR] at fr fa fz fc fo fg
      obtain ⟨hgb, hgc⟩ := hgk hT ss gs1 ss' gs' h1 h2
      simp only [List.mem_append, List.mem_flatMap] at hv
      rcases hv with ((((⟨g, hg, hv⟩ | hv) | ⟨j, hj, hv⟩) | hv) | ⟨q, -, hv⟩)
      · exact fg (by simp only [List.all_append, Bool.and_eq_true] at hgb; exact hgb.1) g
          (hgc g hg) v hv
      · revert hv
        split
        · rename_i t nx c l tag hT' hc
          intro hv
          have hp := hcond t nx c l tag hT' hc
          simp only [Option.map_some, Option.getD_some, symDec] at hv
          obtain ⟨pol, hpol⟩ := Option.isSome_iff_exists.mp hp
          rw [hpol] at hv
          exact fz v hv
        · simp
      · obtain ⟨hjs, hjA⟩ := hsucc j hj
        simp only [tabLive_getD G A hjs, ite_true, List.mem_append] at hv
        rcases hv with ⟨r, hr, hv⟩ | ((hv | hv) | hv)
        · exact fr r (hjA r hr) v hv
        · exact fz v hv
        · exact fc v hv
        · exact fo v hv
      · split at hv
        · rename_i hh
          simp only [List.mem_flatMap] at hv
          obtain ⟨r, hr, hv⟩ := hv
          exact fr r (hhalt hh r hr) v hv
        · simp at hv
      · exact fa q v hv
    · simp at hv

/-- **The live sets of the checker lie below a closed table**: the names the iteration of
    `ownedCheckMC` finds live at the entry block are names of the table at position `0`. -/
theorem liveIter_entry_sub {C C' : List LinstrRM} {O : List String} {G G' : CFG}
    (hG : cfgOf (C.map Prod.fst) = some G) (hne : C ≠ []) {A : Nat → List String}
    (hA : TabClosed C O A) {F F' : Nat → List CFact}
    (hgd : ∀ k r, (runsOfC F F' C C' G G' symStep)[k]? = some r → (G.blk k).term ≠ .ret →
      GuardsIn r) (n : Nat) :
    ∀ v ∈ ((liveIter O C G (runsOfC F F' C C' G G' symStep) n
      (Array.replicate G.blocks.size ([], false))).getD 0 ([], false)).1, v ∈ A 0 := by
  intro v hv
  have hle := liveIter_le_post O C G _ (livePost_tab hG hA hgd) n _ (fun k => by
    have : (Array.replicate G.blocks.size (([] : List String), false)).getD k ([], false) =
        ([], false) := by
      by_cases hk : k < G.blocks.size <;> simp [Array.getD, hk]
    rw [this]
    exact LiveCov.nil _)
  have h0 := cfgOf_start_zero hG (by simpa using hne)
  have := (hle 0).1 v hv
  rw [tabLive_getD G A h0.1, h0.2] at this
  exact this

/-- **The checker with an entry set needs no entry name outside a closed table.** If
    `ownedCheckMCIn ins O` accepts `C` against `C'`, and the table `A` is closed along `C`
    for `O`, then `ownedCheckMCIn ins' O` accepts them for every entry set `ins'` that holds
    the names of `A` at position `0`. The image enters only through the checks themselves:
    the guard containment of the accepted block checks. -/
theorem ownedCheckMCIn_of_tab {ins ins' O : List String} {C C' : List LinstrRM}
    {A : Nat → List String} (hA : TabClosed C O A) (hins : ∀ v ∈ A 0, v ∈ ins')
    (h : ownedCheckMCIn ins O C C' = true) : ownedCheckMCIn ins' O C C' = true := by
  unfold ownedCheckMCIn at h ⊢
  cases hG : cfgOf (C.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
  cases hG' : cfgOf (C'.map Prod.fst) with
  | none => simp [hG, hG'] at h
  | some G' =>
  simp only [hG, hG'] at h ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem] at h ⊢
  obtain ⟨⟨⟨⟨⟨hW, hObl⟩, hf1⟩, hf2⟩, -⟩, hFl⟩ := h
  refine ⟨⟨⟨⟨⟨hW, hObl⟩, hf1⟩, hf2⟩, fun v hv => hins v ?_⟩, hFl⟩
  have hW' := hW
  unfold ownedCheckWithR at hW'
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hW'
  obtain ⟨⟨⟨hne, -⟩, -⟩, hall⟩ := hW'
  refine liveIter_entry_sub hG (by simpa using hne) hA (fun k r hr hT => ?_) _ v hv
  have hk : k < G.blocks.size := by
    have := (Array.getElem?_eq_some_iff.mp hr).1
    simpa [runsOfC] using this
  have hb := (hall k hk).2
  rw [hr] at hb
  exact guardsIn_of_blockOkR hb hT

end Closed

/-! ## 11. A table of a body along its cut programs

The cut program `cutAt fn fin B e x` holds, at position `c ≤ B.length`, the instruction of
the body at the position `cutBack B e c` (the inverse of `LprogCallCut.cutPos`), with the
exit replaced by the jump to `fin`, and the instruction of the end of the body at the image
of `B.length`; it ends with the declaration of `fin`. A table of names over the positions of
`B` that is closed along `B` gives, along `cutBack`, a table closed along the cut program
(`tabClosed_cutAt`). The seams of the rotation are positions whose instruction is a jump or
a shadow instruction of a call: the first has no symbolic step and the second has no
successful one (`SymFootprint.symStep_shadowCall`), so no transfer is asked there. -/

section Cut

open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (cutAt exitI finI stopPos entryPos)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel findLabel_sound)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (jumpLabel?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem)

/-- The position of the body `B` that position `c` of a cut program for the entry `e`
    comes from: the inverse of `LprogCallCut.cutPos B e` on the positions up to
    `B.length`. -/
def cutBack (B : List LinstrRM) : Option Nat → Nat → Nat
  | none, c => c
  | some p, c => if c ≤ B.length - p - 1 then c + p + 1 else c - (B.length - p)

/-- The instruction of a cut program for the exit `x` that comes from position `q` of the
    body `B`: the jump to `fin` at the exit, the instruction of `B` at every other position
    of `B`, and the instruction of the end of the body at `B.length`. -/
def cutIns (fn : String) (fin : LLabel) (B : List LinstrRM) (x : Option Nat) (q : Nat) :
    LinstrRM :=
  if x = some q then exitI fn fin
  else match B[q]? with
    | some i => i
    | none =>
        match x with
        | none => exitI fn fin
        | some p => (B[p]?).getD (exitI fn fin)

/-- **The positions of a site**: `e` is the end of the body or a position of `B` that holds
    a shadow instruction of a call. -/
def SiteOk (B : List LinstrRM) (e : Option Nat) : Prop :=
  ∀ p, e = some p → ∃ i, B[p]? = some i ∧ LprogIsa.shadowCall? i.1 ≠ none

theorem SiteOk.lt {B : List LinstrRM} {e : Option Nat} (h : SiteOk B e) {p : Nat}
    (hp : e = some p) : p < B.length := by
  obtain ⟨i, hi, -⟩ := h p hp
  exact (List.getElem?_eq_some_iff.mp hi).1

theorem cutAt_length (fn : String) (fin : LLabel) (B : List LinstrRM) {e : Option Nat}
    (x : Option Nat) (he : SiteOk B e) : (cutAt fn fin B e x).length = B.length + 2 := by
  unfold cutAt
  cases x <;> cases e with
  | none => simp
  | some p =>
      have := he.lt rfl
      simp only [List.length_append, List.length_drop, List.length_cons, List.length_take,
        List.length_nil, List.length_set]
      omega

theorem cutBack_zero (B : List LinstrRM) {e : Option Nat} (he : SiteOk B e) :
    cutBack B e 0 = entryPos e := by
  cases e with
  | none => rfl
  | some p =>
      simp only [cutBack, entryPos]
      rw [ite_eq_left (by omega)]
      omega

theorem cutBack_le (B : List LinstrRM) {e : Option Nat} (he : SiteOk B e) {c : Nat}
    (hc : c ≤ B.length) : cutBack B e c ≤ B.length := by
  cases e with
  | none => exact hc
  | some p =>
      have := he.lt rfl
      simp only [cutBack]
      split <;> omega

private theorem getElem?_append_two (L : List LinstrRM) (o d : LinstrRM) {c : Nat}
    (hc : c ≤ L.length) : (L ++ [o, d])[c]? = some ((L[c]?).getD o) := by
  rcases Nat.lt_or_ge c L.length with h | h
  · rw [List.getElem?_append_left h, List.getElem?_eq_getElem h]
    rfl
  · obtain rfl : c = L.length := by omega
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_eq_none (Nat.le_refl _)]
    rfl

private theorem getElem?_rot (L : List LinstrRM) (o d : LinstrRM) {p c : Nat}
    (hp : p < L.length) (hc : c ≤ L.length) :
    (L.drop (p + 1) ++ [o] ++ L.take p ++ [(L[p]?).getD o, d])[c]? =
      some ((L[if c ≤ L.length - p - 1 then c + p + 1 else c - (L.length - p)]?).getD o) := by
  simp only [List.getElem?_append, List.length_append, List.length_drop, List.length_take,
    List.length_singleton, List.getElem?_drop, List.getElem?_take]
  repeat' split
  all_goals first
    | omega
    | (rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
       simp only [Option.getD_some, Option.some.injEq]
       congr 1
       omega)
    | (rw [List.getElem?_eq_none (l := L) (by omega),
          show c - (L.length - (p + 1)) = 0 by omega]
       rfl)
    | (rw [show c - (L.length - (p + 1) + 1 + min p L.length) = 0 by omega,
          show c - (L.length - p) = p by omega]
       rfl)

theorem cutIns_none (fn : String) (fin : LLabel) (B : List LinstrRM) (q : Nat) :
    cutIns fn fin B none q = (B[q]?).getD (exitI fn fin) := by
  unfold cutIns
  simp only [reduceCtorEq, ite_false]
  cases B[q]? <;> rfl

theorem cutIns_some (fn : String) (fin : LLabel) (B : List LinstrRM) {p : Nat}
    (hp : p < B.length) (q : Nat) :
    cutIns fn fin B (some p) q =
      ((B.set p (exitI fn fin))[q]?).getD ((B[p]?).getD (exitI fn fin)) := by
  unfold cutIns
  by_cases hpq : p = q
  · subst hpq
    simp [hp]
  · rw [ite_eq_right (by simpa using hpq), List.getElem?_set_ne hpq]
    cases B[q]? <;> rfl

/-- The instruction at position `c ≤ B.length` of a cut program. -/
theorem cutAt_getElem? (fn : String) (fin : LLabel) (B : List LinstrRM) {e x : Option Nat}
    (he : SiteOk B e) (hx : SiteOk B x) {c : Nat} (hc : c ≤ B.length) :
    (cutAt fn fin B e x)[c]? = some (cutIns fn fin B x (cutBack B e c)) := by
  unfold cutAt
  cases x with
  | none =>
      cases e with
      | none =>
          dsimp only
          rw [getElem?_append_two B _ _ hc, cutIns_none]
          rfl
      | some p =>
          dsimp only
          rw [getElem?_rot B _ _ (he.lt rfl) hc, cutIns_none]
          rfl
  | some p' =>
      have hp' := hx.lt rfl
      have hl : (B.set p' (exitI fn fin)).length = B.length := List.length_set ..
      cases e with
      | none =>
          dsimp only
          rw [getElem?_append_two _ _ _ (by rw [hl]; exact hc), cutIns_some fn fin B hp']
          rfl
      | some p =>
          dsimp only
          rw [getElem?_rot _ _ _ (by rw [hl]; exact he.lt rfl) (by rw [hl]; exact hc),
            cutIns_some fn fin B hp', hl]
          rfl

/-- A cut program ends with the declaration of `fin`. -/
theorem cutAt_last (fn : String) (fin : LLabel) (B : List LinstrRM) (e x : Option Nat) :
    ∃ L, cutAt fn fin B e x = L ++ [finI fin] := by
  unfold cutAt
  cases x <;> cases e
  · exact ⟨B ++ [exitI fn fin], by simp⟩
  · rename_i p
    exact ⟨B.drop (p + 1) ++ [exitI fn fin] ++ B.take p ++ [(B[p]?).getD (exitI fn fin)],
      by simp⟩
  · rename_i p'
    exact ⟨B.set p' (exitI fn fin) ++ [(B[p']?).getD (exitI fn fin)], by simp⟩
  · rename_i p' p
    exact ⟨(B.set p' (exitI fn fin)).drop (p + 1) ++ [(B[p']?).getD (exitI fn fin)] ++
      (B.set p' (exitI fn fin)).take p ++
      [((B.set p' (exitI fn fin))[p]?).getD ((B[p']?).getD (exitI fn fin))], by simp⟩

theorem cutAt_getElem?_fin (fn : String) (fin : LLabel) (B : List LinstrRM)
    {e : Option Nat} (x : Option Nat) (he : SiteOk B e) :
    (cutAt fn fin B e x)[B.length + 1]? = some (finI fin) := by
  obtain ⟨L, hL⟩ := cutAt_last fn fin B e x
  have hl := cutAt_length fn fin B x he
  rw [hL] at hl ⊢
  simp only [List.length_append, List.length_singleton] at hl
  rw [List.getElem?_append_right (by omega), show B.length + 1 - L.length = 0 by omega]
  rfl

/-- The instruction of a cut program that comes from a position of the body is the jump to
    `fin` at the exit, an instruction of the body at a position other than the exit, or a
    shadow instruction of a call. -/
theorem cutIns_cases {fn : String} {fin : LLabel} {B : List LinstrRM} {x : Option Nat}
    (hx : SiteOk B x) {q : Nat} (hq : q ≤ B.length) :
    (cutIns fn fin B x q = exitI fn fin ∧ q = stopPos B x) ∨
    (x ≠ some q ∧ B[q]? = some (cutIns fn fin B x q)) ∨
    LprogIsa.shadowCall? (cutIns fn fin B x q).1 ≠ none := by
  unfold cutIns
  by_cases hxq : x = some q
  · subst hxq
    exact Or.inl ⟨by simp, rfl⟩
  · rw [ite_eq_right hxq]
    split
    · rename_i i hi
      exact Or.inr (Or.inl ⟨hxq, hi⟩)
    · rename_i hn
      have hqn : q = B.length := by
        rcases Nat.lt_or_ge q B.length with h | h
        · rw [List.getElem?_eq_getElem h] at hn; cases hn
        · omega
      cases x with
      | none => exact Or.inl ⟨rfl, hqn⟩
      | some p =>
          obtain ⟨i, hi, hs⟩ := hx p rfl
          refine Or.inr (Or.inr ?_)
          simp only [hi, Option.getD_some]
          exact hs

theorem cutBack_succ (B : List LinstrRM) {e : Option Nat} (he : SiteOk B e) {c : Nat}
    (hc : c ≤ B.length) (hq : cutBack B e c < B.length) (hne : e ≠ some (cutBack B e c)) :
    c + 1 ≤ B.length ∧ cutBack B e (c + 1) = cutBack B e c + 1 := by
  cases e with
  | none => exact ⟨by simp only [cutBack] at hq; omega, rfl⟩
  | some p =>
      have hp := he.lt rfl
      simp only [cutBack, ne_eq, Option.some.injEq] at hq hne ⊢
      by_cases h1 : c ≤ B.length - p - 1
      · rw [ite_eq_left h1] at hq hne
        rw [ite_eq_left h1, ite_eq_left (by omega)]
        omega
      · rw [ite_eq_right h1] at hq hne
        rw [ite_eq_right h1, ite_eq_right (by omega)]
        omega

theorem isLabel_shadow {i : LinstrRM} (h : LprogIsa.shadowCall? i.1 ≠ none) (l : LLabel) :
    isLabel l i.1 = false ∧ jumpLabel? i.1 = none ∧ ∀ c l', i.1 ≠ .Lcond c l' := by
  obtain ⟨dst, opn, srcs, he, -⟩ := LprogIsaProcs.shadowCall?_wire h
  rw [he]
  exact ⟨rfl, rfl, fun _ _ e => by cases e⟩

/-- **The labels of `B` are declared once**: two positions that declare one label are
    equal. -/
def LabelsOnce (B : List LinstrRM) : Prop :=
  ∀ (q q' : Nat) (i i' : LinstrRM) (l : LLabel), B[q]? = some i → B[q']? = some i' →
    isLabel l i.1 = true → isLabel l i'.1 = true → q = q'

/-- **The label `fin` is free in `B`**: no instruction of `B` declares it or jumps to it. -/
def FinFree (fin : LLabel) (B : List LinstrRM) : Prop :=
  ∀ i ∈ B, isLabel fin i.1 = false ∧ jumpLabel? i.1 ≠ some fin

/-- **The first declaration of a label declared once**: a label declared at `q` and at no
    other position is found at `q`. -/
theorem findLabelMem_of_unique {B : List LinstrRM}
    (huniq : LabelsOnce B)
    {q : Nat} {i : LinstrRM} {l : LLabel} (hq : B[q]? = some i)
    (hl : isLabel l i.1 = true) : findLabelMem l B = some q := by
  cases hf : findLabelMem l B with
  | none =>
      exfalso
      unfold findLabelMem findLabel at hf
      rw [List.findIdx?_eq_none_iff] at hf
      have := hf i.1 (List.mem_map.mpr ⟨i, List.mem_of_getElem? hq, rfl⟩)
      rw [hl] at this
      cases this
  | some q' =>
      obtain ⟨k, hk, hlk⟩ := findLabel_sound l _ q' hf
      rw [List.getElem?_map] at hk
      obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp hk
      exact congrArg some (huniq q' q i' i l hi' hq hlk hl)

/-- The table of a body `B` along the cut programs for the entry `e`, with the names `O` at
    the declaration of the label of the end and after it. -/
def cutTab (B : List LinstrRM) (TB : Nat → List String) (O : List String) (e : Option Nat)
    (c : Nat) : List String :=
  if c ≤ B.length then TB (cutBack B e c) else O

/-- **A table closed along a body is closed along its cut programs.** For an entry `e` and
    an exit `x` that are the end of the body or shadow instructions of calls, a body with no
    declaration of and no jump to the label `fin` (`FinFree`), and labels declared once
    (`LabelsOnce`), a table `TB` closed along `B` gives the table `cutTab B TB O e`, closed
    along the cut program `cutAt fn fin B e x` for observed names `O` that are names of
    `TB` at the exit. -/
theorem tabClosed_cutAt {fn : String} {fin : LLabel} {B : List LinstrRM} {e x : Option Nat}
    {outs O : List String} {TB : Nat → List String} (he : SiteOk B e) (hx : SiteOk B x)
    (hfin : FinFree fin B)
    (huniq : LabelsOnce B)
    (hTB : TabClosed B outs TB) (hO : ∀ y ∈ O, y ∈ TB (stopPos B x)) :
    TabClosed (cutAt fn fin B e x) O (cutTab B TB O e) := by
  have hlen := cutAt_length fn fin B x he
  have hfinI := cutAt_getElem?_fin fn fin B x he
  have hget := fun c (hc : c ≤ B.length) => cutAt_getElem? fn fin B he hx hc
  have hcases := fun c (hc : c ≤ B.length) =>
    cutIns_cases (fn := fn) (fin := fin) hx (cutBack_le B he hc)
  have hTc : ∀ c, c ≤ B.length → cutTab B TB O e c = TB (cutBack B e c) :=
    fun c hc => ite_eq_left hc
  have hTO : ∀ c, B.length < c → cutTab B TB O e c = O := fun c hc => ite_eq_right (by omega)
  have hsymX : ∀ ss, symStep (exitI fn fin) ss = .unk := fun ss => by
    simp [symStep, exitI, cmpArgs?, movRegArgs?, flagCondCC?]
  -- the labels of a cut program up to the end of the body are labels of the body
  have hlab : ∀ c l, c ≤ B.length → isLabel l (cutIns fn fin B x (cutBack B e c)).1 = true →
      x ≠ some (cutBack B e c) ∧
        B[cutBack B e c]? = some (cutIns fn fin B x (cutBack B e c)) := by
    intro c l hc hl
    rcases hcases c hc with ⟨h1, -⟩ | h1 | h1
    · rw [h1] at hl
      simp [exitI, isLabel] at hl
    · exact h1
    · rw [(isLabel_shadow h1 l).1] at hl
      cases hl
  refine ⟨fun c => ?_, fun c i l pc hi hl hpc => ?_, fun c c' l tag hi => ?_,
    fun y hy => ?_⟩
  · intro i hi E X ss s gs hs hX
    rcases Nat.lt_or_ge c (B.length + 1) with hc | hc
    · rw [hget c (by omega), Option.some.injEq] at hi
      subst hi
      rcases hcases c (by omega) with ⟨h1, -⟩ | ⟨hxq, hq⟩ | h1
      · rw [h1, hsymX] at hs; cases hs
      · by_cases heq : e = some (cutBack B e c)
        · obtain ⟨i', hi', hsh⟩ := he _ heq
          rw [hq, Option.some.injEq] at hi'
          rw [hi'] at hs
          exact absurd hs (SymFootprint.symStep_shadowCall hsh _ _ _)
        · have hqlt : cutBack B e c < B.length := (List.getElem?_eq_some_iff.mp hq).1
          obtain ⟨hc1, hb1⟩ := cutBack_succ B he (by omega) hqlt heq
          rw [hTc c (by omega)] at hX
          rw [hTc (c + 1) hc1, hb1]
          exact hTB.step _ _ hq E X ss s gs hs hX
      · exact absurd hs (SymFootprint.symStep_shadowCall h1 _ _ _)
    · rcases Nat.lt_or_ge c (B.length + 2) with hc2 | hc2
      · have hcn : c = B.length + 1 := by omega
        subst hcn
        rw [hfinI, Option.some.injEq] at hi
        subst hi
        rw [symStep_label (by rfl)] at hs
        simp only [SOut.ok.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        rw [hTO _ (by omega)] at hX
        rw [hTO _ (by omega)]
        exact ⟨hX, fun g hg => by simp at hg⟩
      · rw [List.getElem?_eq_none (by omega)] at hi
        cases hi
  · -- jumps
    have hc : c ≤ B.length := by
      rcases Nat.lt_or_ge c (B.length + 1) with hc | hc
      · omega
      · rcases Nat.lt_or_ge c (B.length + 2) with hc2 | hc2
        · rw [show c = B.length + 1 by omega, hfinI, Option.some.injEq] at hi
          subst hi
          cases hl
        · rw [List.getElem?_eq_none (by omega)] at hi
          cases hi
    rw [hget c hc, Option.some.injEq] at hi
    subst hi
    obtain ⟨ins, hpc1, hpcl⟩ := findLabel_sound l _ pc hpc
    rw [List.getElem?_map] at hpc1
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hpc1
    rcases hcases c hc with ⟨h1, hq⟩ | ⟨hxq, hq⟩ | h1
    · -- the jump to the end
      rw [h1] at hl
      simp only [exitI, jumpLabel?, Option.some.injEq] at hl
      subst hl
      have hpcn : pc = B.length + 1 := by
        rcases Nat.lt_or_ge pc (B.length + 1) with h2 | h2
        · exfalso
          rw [hget pc (by omega), Option.some.injEq] at hj
          subst hj
          obtain ⟨-, hq'⟩ := hlab pc _ (by omega) hpcl
          exact absurd hpcl (by rw [(hfin _ (List.mem_of_getElem? hq')).1]; simp)
        · have := (List.getElem?_eq_some_iff.mp hj).1
          omega
      intro y hy
      rw [hpcn, hTO _ (by omega)] at hy
      rw [hTc c hc, hq]
      exact hO y hy
    · -- a jump of the body
      have hfl := hfin _ (List.mem_of_getElem? hq)
      have hpcn : pc ≤ B.length := by
        rcases Nat.lt_or_ge pc (B.length + 1) with h2 | h2
        · omega
        · exfalso
          have hpc2 : pc = B.length + 1 := by
            have := (List.getElem?_eq_some_iff.mp hj).1
            omega
          rw [hpc2, hfinI, Option.some.injEq] at hj
          subst hj
          have hlf : l = fin := by simpa [finI, isLabel] using hpcl
          subst hlf
          exact hfl.2 hl
      rw [hget pc hpcn, Option.some.injEq] at hj
      subst hj
      obtain ⟨-, hq'⟩ := hlab pc l hpcn hpcl
      have hfB := findLabelMem_of_unique huniq hq' hpcl
      intro y hy
      rw [hTc pc hpcn] at hy
      rw [hTc c hc]
      exact hTB.jump _ _ l _ hq hl hfB y hy
    · rw [(isLabel_shadow h1 l).2.1] at hl
      cases hl
  · -- conditional jumps
    have hc : c ≤ B.length := by
      rcases Nat.lt_or_ge c (B.length + 1) with hc | hc
      · omega
      · rcases Nat.lt_or_ge c (B.length + 2) with hc2 | hc2
        · rw [show c = B.length + 1 by omega, hfinI, Option.some.injEq] at hi
          cases hi
        · rw [List.getElem?_eq_none (by omega)] at hi
          cases hi
    rw [hget c hc, Option.some.injEq] at hi
    rcases hcases c hc with ⟨h1, -⟩ | ⟨hxq, hq⟩ | h1
    · rw [h1] at hi; cases hi
    · rw [hi] at hq
      have heq : e ≠ some (cutBack B e c) := by
        intro heq
        obtain ⟨i', hi', hsh⟩ := he _ heq
        rw [hq, Option.some.injEq] at hi'
        exact (isLabel_shadow hsh 0).2.2 c' l (by rw [← hi'])
      have hqlt : cutBack B e c < B.length := (List.getElem?_eq_some_iff.mp hq).1
      obtain ⟨hc1, hb1⟩ := cutBack_succ B he hc hqlt heq
      have h2 := hTB.cond _ c' l tag hq
      refine ⟨h2.1, fun y hy => ?_⟩
      rw [hTc (c + 1) hc1, hb1] at hy
      rw [hTc c hc]
      exact h2.2 y hy
    · exact absurd (by rw [hi]) ((isLabel_shadow h1 0).2.2 c' l)
  · rw [hlen, hTO _ (by omega)]
    exact hy

end Cut

end CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegComplete
