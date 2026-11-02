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

## Main definitions

* `KeepsReg`: the symbolic step of every instruction of a body keeps the word of a register.
* `FactFree`: no must-constant fact names a register.
* `RunsOk`, `RunsOkAt`: the block pairs that the checker checks.
* `liveIt`: the iterate of `liveRound` from the empty sets.
* `Yit`: the names the iteration propagates from the observed names of a halt.

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

Elaboration takes about ten seconds.
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

theorem constGrow_free (hk : KeepsReg y B) {ann : Array (List CFact)} (ha : FactFree y ann) :
    FactFree y (constGrow B G symStep ann) := by
  intro k f hf
  unfold constGrow at hf
  rw [getD_map_range] at hf
  split_ifs at hf with hkn hk0
  · simp at hf
  · rw [List.mem_eraseDups, List.mem_append] at hf
    rcases hf with hf | hf
    · exact ha k f hf
    · simp only [List.mem_flatMap, List.mem_range] at hf
      obtain ⟨j, -, hj⟩ := hf
      split at hj
      · split at hj
        · rename_i ss g he
          exact constExit_free (exitsOf_free hk ha he) f hj
        · simp at hj
      · simp at hj
  · simp at hf

theorem constPass_free {ann : Array (List CFact)} (ha : FactFree y ann) :
    FactFree y (constPass B G symStep ann) := by
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
  unfold constAnnot
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
  set R := runsOfC (constAnnot C G symStep) (constAnnot C' G' symStep) C C' G G' symStep
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegComplete
