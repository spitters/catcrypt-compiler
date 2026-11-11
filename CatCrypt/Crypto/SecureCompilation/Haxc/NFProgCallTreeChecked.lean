/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents

/-!
# Call trees on the bounds-checked x86 instruction set

The bounds check `CheckedIsaCall.idxInvCheckPB` of a body is sound for halting runs of the x86
flag machine with procedures (`CheckedIsaCall.refRun_checked`), through an invariant over block
entries and halting runs. A call tree related by `NFProgCallTreeExport.TSim` to a state of the
body has no halting run: between its events the body runs to a call site, and after each event
the result is written by an arbitrary answer. The check is sound for these runs through a step
invariant (`BInvAt`): the state is inside the body of a block and described by facts and a
symbolic state from which the segmented walk of the rest of the body gives the walk of the whole
body. Every step of the x86 flag machine from a state of the invariant is a step of the
bounds-checked machine to a state of the invariant (`binv_step`), and so is the write of the
result of a call of a symbol of the table, whatever the answer (`binv_callRet`), since the facts
after a call keep only register facts that do not name the destination. A call tree related on
the x86 flag machine to the entry state of a body that passes the check is then related on the
bounds-checked machine (`tsim_checked`).

## Main definitions

* `BInvAt`: the bounds invariant at a state of a body, in a block of its control-flow graph.
* `BInv`: the invariant in some block, or a state at or past the end of the body.

## Main results

* `binvAt_entry`: the invariant at the entry of a block whose facts hold.
* `binvAt_step_body`, `binvAt_step_term`: a step inside the body of a block, and the jump or
  branch that ends it, are checked steps that keep the invariant.
* `binv_step`, `binv_steps`: steps from a state of the invariant are checked steps.
* `binv_callRet`: the state after a call keeps the invariant.
* `tsim_checked_of_binv`, `tsim_checked`: a call tree related on the x86 flag machine is related
  on the bounds-checked machine.
-/
@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChecked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable procCall? shadowCall?
  procStep retWord retArr retRes CallRes lfn_retRes lpc_retRes isCtl ctlStep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall

variable {T : ProcTable} {ann : List (List IdxFact)} {B : List LinstrRM} {G : CFG}
  {fn : String}

/-- **The bounds invariant at a state of a body in block `k`**: the state is in `fn` between the
    start of the block and the end of its body, and there are facts and a symbolic state that
    describe it, from which the segmented walk of the rest of the body gives the walk of the whole
    body from the facts of the block. -/
def BInvAt (T : ProcTable) (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG) (fn : String)
    (k : Nat) (s : LstateMF) : Prop :=
  s.prog.lfn = fn ∧ k < G.blocks.size ∧ (G.blk k).start ≤ s.prog.base.reg.lpc
    ∧ s.prog.base.reg.lpc ≤ bstopOf (G.blk k).term (G.blk k)
    ∧ ∃ (F : List SFact) (ss : SSt) (V : String → Σ w, BitVec w) (A : String → ArrCell)
      (C O Z : Bool), Holds V A C O Z ss s ∧ (∀ g ∈ F, g.holds V A C O)
      ∧ segWalk T ann.flatten F ss ((B.drop s.prog.base.reg.lpc).take
          (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc))
        = segWalk T ann.flatten (startF (annAt ann k)) SSt.start
          (bodyAt B (G.blk k) (G.blk k).term)

/-- **The invariant at the entry of a block whose facts hold.** -/
theorem binvAt_entry (hG : cfgOf (B.map Prod.fst) = some G) {k : Nat} (hk : k < G.blocks.size)
    {s : LstateMF} (hE : EntryAt B (G.blk k) s.prog.base.reg.lpc) (hfn : s.prog.lfn = fn)
    (hinv : ∀ f ∈ annAt ann k, f.holds s.prog.base.reg.lvm s.prog.base.larr) :
    BInvAt T ann B G fn k s := by
  obtain ⟨hs, hle⟩ := entry_le hG hk hE
  exact ⟨hfn, hk, hs, hle, _, _, _, _, _, _, _, holds_start s, startF_holds hinv,
    segWalk_entry hE hle⟩


/-- A step of an instruction that is no terminator goes to the next position. -/
theorem nextPc_of_not_term {wl : List LinstrR} {x : LinstrR} {pc pc' : Nat}
    (hx : isTermR x = false) (h : NextPc wl x pc pc') : pc' = pc + 1 := by
  cases x <;> simp_all [NextPc, isTermR]

/-- The walk of a block body that passes `blockInvOkP` is not rejected. -/
theorem walk_ne_bad (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret) {k : Nat} (hk : k < G.blocks.size) :
    segWalk T ann.flatten (startF (annAt ann k)) SSt.start (bodyAt B (G.blk k) (G.blk k).term)
      ≠ .bad := by
  have hbk := hb k hk
  unfold blockInvOkP at hbk
  intro hS
  revert hbk
  cases hT : (G.blk k).term with
  | ret => exact absurd hT (hnr k hk)
  | _ => simp [← hT, hS]

/-- **A step inside the body of a block is a checked step that keeps the invariant.** -/
theorem binvAt_step_body (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret) {k : Nat} {s u : LstateMF}
    (hI : BInvAt T ann B G fn k s)
    (hlt : s.prog.base.reg.lpc < bstopOf (G.blk k).term (G.blk k))
    (h : x86Isa.lsemStepPMemF (singletonProgM fn B) s = some u) :
    x86IsaK.lsemStepPMemF (singletonProgM fn B) s = some u
      ∧ BInvAt T ann B G fn k u := by
  obtain ⟨hfn, hk, hs, hle, F, ss, V, A, C, O, Z, hH, hF, hW⟩ := hI
  have FB := blockFacts hG hk
  have hbl : bstopOf (G.blk k).term (G.blk k) ≤ B.length := by
    have := FB.le
    unfold bstopOf; split <;> simp at this <;> omega
  obtain ⟨i, hi⟩ : ∃ i, B[s.prog.base.reg.lpc]? = some i :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hfetch := findInstrMem_single (B := B) hfn
  unfold Isa.lsemStepPMemF at h ⊢
  simp only [hfetch, hi] at h ⊢
  have hplain := body_plain hG hk hs i (by rw [take_cons B hlt hi]; exact List.mem_cons_self)
  rw [take_cons B hlt hi] at hW
  rw [x86Isa_step] at h
  have hnot : shadowCall? i.1 = none := by
    by_contra hsh
    rw [LprogIsaProcs.evalInstrPMemF_shadowCall _ i s hsh] at h
    cases h
  have hq : procCall? T i.1 = none := by simp [procCall?, hnot]
  have hnb := walk_ne_bad hb hnr hk
  have hstep := symStep_sound (singletonProgM fn B) i ss V A C O Z s hH
  cases h1 : symStep i ss with
  | ok ss1 g1 =>
      rw [h1] at hstep
      obtain ⟨hg1, hH1, -⟩ := hstep.1 u h
      have hF1 : ∀ g ∈ F ++ g1.flatMap guardW64, g.holds V A C O := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF g hg
        · exact guardW64_holds hg1 g hg
      by_cases hob : oblsOk (F ++ g1.flatMap guardW64) (oblOf i ss) = true
      · have hw : segWalk T ann.flatten F ss (i :: (B.drop (s.prog.base.reg.lpc + 1)).take
            (bstopOf (G.blk k).term (G.blk k) - (s.prog.base.reg.lpc + 1)))
            = segWalk T ann.flatten (F ++ g1.flatMap guardW64) ss1
              ((B.drop (s.prog.base.reg.lpc + 1)).take
                (bstopOf (G.blk k).term (G.blk k) - (s.prog.base.reg.lpc + 1))) := by
          simp only [segWalk, hq, h1, ite_eq_left hob]
        have hidx : JasminLsemMemChecked.idxOkB i s = true :=
          (oblOf_iff hH.1 i).mpr (oblsOk_sound hob hF1)
        have hnx := X86Backend.AllocCheck.LcmdCFG.evalInstrPMemF_next _ _ s u h
        have hpc : u.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 :=
          nextPc_of_not_term hplain hnx.2
        refine ⟨?_, hnx.1.trans hfn, hk, by omega, by omega, _, ss1, V, A, C, O, _, hH1, hF1, ?_⟩
        · rw [x86IsaK_step, JasminLsemMemChecked.evalInstrPMemFk_true,
            ite_eq_left hidx]
          exact h
        · rw [hpc, ← hw]
          exact hW
      · exfalso
        apply hnb
        rw [← hW]
        simp only [segWalk, hq, h1, ite_eq_right hob]
  | fail =>
      rw [h1] at hstep
      simp only [SOut.Desc] at hstep
      rw [hstep] at h
      cases h
  | unk =>
      exfalso
      apply hnb
      rw [← hW]
      simp only [segWalk, hq, h1]


/-- **The bounds invariant at a state of a body**: the invariant in some block, or a state of
    `fn` at or past the end of the body. -/
def BInv (T : ProcTable) (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG) (fn : String)
    (s : LstateMF) : Prop :=
  (∃ k, BInvAt T ann B G fn k s) ∨ (s.prog.lfn = fn ∧ B.length ≤ s.prog.base.reg.lpc)

/-- At the end of the body of a block, the walk of the body has given its facts and symbolic
    state: the terminator check holds of them. -/
theorem binvAt_end (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret) {k : Nat} {s : LstateMF}
    (hI : BInvAt T ann B G fn k s)
    (heq : s.prog.base.reg.lpc = bstopOf (G.blk k).term (G.blk k)) :
    ∃ (F : List SFact) (ss : SSt) (V : String → Σ w, BitVec w) (A : String → ArrCell)
      (C O Z : Bool), Holds V A C O Z ss s ∧ (∀ g ∈ F, g.holds V A C O)
      ∧ termInvOk ann F ss (G.blk k).term B[(G.blk k).stop - 1]? = true := by
  obtain ⟨-, hk, -, -, F, ss, V, A, C, O, Z, hH, hF, hW⟩ := hI
  refine ⟨F, ss, V, A, C, O, Z, hH, hF, ?_⟩
  rw [heq, Nat.sub_self, List.take_zero] at hW
  have hbk := hb k hk
  unfold blockInvOkP at hbk
  revert hbk
  cases hT : (G.blk k).term with
  | ret => exact absurd hT (hnr k hk)
  | _ => simp [← hT, ← hW, segWalk]

/-- **The invariant before an instruction is the invariant inside the body of a block or at the
    jump or branch that ends a block.** -/
theorem binvAt_norm (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret) :
    ∀ (n k : Nat) (s : LstateMF), G.blocks.size - k ≤ n → BInvAt T ann B G fn k s →
      ∀ i, B[s.prog.base.reg.lpc]? = some i →
      ∃ k', BInvAt T ann B G fn k' s
        ∧ (s.prog.base.reg.lpc < bstopOf (G.blk k').term (G.blk k')
          ∨ (s.prog.base.reg.lpc = bstopOf (G.blk k').term (G.blk k')
            ∧ (∀ nx, (G.blk k').term ≠ .fall nx) ∧ isTermR i.1 = true)) := by
  intro n
  induction n with
  | zero =>
      intro k s hn hI
      have := hI.2.1
      omega
  | succ n ih =>
      intro k s hn hI i hi
      obtain ⟨hfn, hk, hs, hle, -⟩ := id hI
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact ⟨k, hI, Or.inl hlt⟩
      obtain ⟨F, ss, V, A, C, O, Z, hH, hF, htm⟩ := binvAt_end hb hnr hI heq
      have FB := blockFacts hG hk
      have hterm := FB.term
      have hlt : (G.blk k).stop - 1 < B.length := by have := FB.le; have := FB.lt; simp at *; omega
      obtain ⟨z, hz⟩ : ∃ z, B[(G.blk k).stop - 1]? = some z :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      rw [List.getElem?_map, hz, Option.map_some] at hterm
      rw [hz] at htm
      rcases termOk_spec hterm with ⟨nx, hT, -, hnx⟩ | ⟨t, x, l, hT, hzi, -, -⟩ |
          ⟨t, nx, c, l, hT, hzi, -, -, -⟩ | ⟨hT, -⟩
      · have hw : s.prog.base.reg.lpc = (G.blk k).stop := by rw [heq, hT]; rfl
        rw [hT] at htm
        cases nx with
        | none =>
            have e1 := (stop_next hG hk).1 hnx.symm
            rw [hw, e1, List.getElem?_eq_none (le_refl _)] at hi
            cases hi
        | some j =>
            obtain ⟨hj, hjlt, e1⟩ := (stop_next hG hk).2 j hnx.symm
            subst hj
            have hI' : BInvAt T ann B G fn (k + 1) s :=
              binvAt_entry hG hjlt (Or.inl (hw.trans e1)) hfn (succOk_sound htm hF hH)
            exact ih (k + 1) s (by omega) hI' i hi
      · have hw : s.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [heq, hT]; rfl
        rw [hw, hz] at hi
        obtain rfl := Option.some.inj hi
        exact ⟨k, hI, Or.inr ⟨heq, (fun nx h => by rw [hT] at h; cases h), by rw [hzi]; rfl⟩⟩
      · have hw : s.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [heq, hT]; rfl
        rw [hw, hz] at hi
        obtain rfl := Option.some.inj hi
        exact ⟨k, hI, Or.inr ⟨heq, (fun nx' h => by rw [hT] at h; cases h), by rw [hzi]; rfl⟩⟩
      · exact absurd hT (hnr k hk)


/-- **The step of the jump or branch that ends a block is a checked step that keeps the
    invariant.** -/
theorem binvAt_step_term (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret) {k : Nat} {s u : LstateMF}
    (hI : BInvAt T ann B G fn k s)
    (heq : s.prog.base.reg.lpc = bstopOf (G.blk k).term (G.blk k))
    (hnf : ∀ nx, (G.blk k).term ≠ .fall nx)
    (h : x86Isa.lsemStepPMemF (singletonProgM fn B) s = some u) :
    x86IsaK.lsemStepPMemF (singletonProgM fn B) s = some u ∧ BInv T ann B G fn u := by
  obtain ⟨hfn, hk, -, -, -⟩ := id hI
  obtain ⟨F, ss, V, A, C, O, Z, hH, hF, htm⟩ := binvAt_end hb hnr hI heq
  have FB := blockFacts hG hk
  have hterm := FB.term
  have hlt : (G.blk k).stop - 1 < B.length := by have := FB.le; have := FB.lt; simp at *; omega
  obtain ⟨z, hz⟩ : ∃ z, B[(G.blk k).stop - 1]? = some z :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  rw [List.getElem?_map, hz, Option.map_some] at hterm
  rw [hz] at htm
  have hfetch := findInstrMem_single (B := B) hfn
  unfold Isa.lsemStepPMemF at h ⊢
  rcases termOk_spec hterm with ⟨nx, hT, -, -⟩ | ⟨t, x, l, hT, hzi, htg, hl⟩ |
      ⟨t, nx, c, l, hT, hzi, htg, hl, hnx⟩ | ⟨hT, -⟩
  · exact absurd hT (hnf nx)
  · have hw : s.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [heq, hT]; rfl
    obtain ⟨zi, zt⟩ := z
    simp only at hzi
    subst hzi
    simp only [hfetch, hw, hz] at h ⊢
    rw [x86IsaK_step, JasminLsemMemChecked.evalInstrPMemFk_true, ite_eq_left (idxOkB_goto _ _ _ _),
      ← x86Isa_step]
    refine ⟨h, ?_⟩
    rw [Isa.step_goto] at h
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [ite_eq_left hx, evalJumpMem_single hl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rw [hT] at htm
      exact Or.inl ⟨t, binvAt_entry hG htg (Or.inr ⟨rfl, label_at hl⟩) hfn
        (succOk_sound htm hF hH)⟩
    · rw [ite_eq_right hx] at h
      cases h
  · have hw : s.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [heq, hT]; rfl
    obtain ⟨zi, zt⟩ := z
    simp only at hzi
    subst hzi
    simp only [hfetch, hw, hz] at h ⊢
    rw [x86IsaK_step, JasminLsemMemChecked.evalInstrPMemFk_true, ite_eq_left (idxOkB_cond _ _ _ _),
      ← x86Isa_step]
    refine ⟨h, ?_⟩
    rw [hT] at htm
    simp only [termInvOk, Bool.and_eq_true] at htm
    obtain ⟨htk, hnt⟩ := htm
    have hdec := decC_eq hH c
    have hce : x86Isa.condEval s c = decC s c := rfl
    rw [Isa.step_cond, hce] at h
    have hstop : 0 < (G.blk k).stop := by have := FB.lt; omega
    by_cases hd : decC s c = true
    · rw [ite_eq_left hd, evalJumpMem_single hl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hE' : ∀ g ∈ F ++ edgeFacts (symDec ss c) true, g.holds V A C O := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF g hg
        · exact edgeFacts_sound (hdec.symm.trans hd) g hg
      exact Or.inl ⟨t, binvAt_entry hG htg (Or.inr ⟨rfl, label_at hl⟩) hfn
        (succOk_sound htk hE' hH)⟩
    · rw [ite_eq_right hd] at h
      simp only [Option.some.injEq] at h
      subst h
      have hE' : ∀ g ∈ F ++ edgeFacts (symDec ss c) false, g.holds V A C O := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF g hg
        · exact edgeFacts_sound (by rw [← hdec]; simpa using hd) g hg
      have hw1 : s.prog.base.reg.lpc + 1 = (G.blk k).stop := by omega
      cases nx with
      | none =>
          have e1 := (stop_next hG hk).1 hnx.symm
          exact Or.inr ⟨hfn, by
            show B.length ≤ s.prog.base.reg.lpc + 1
            omega⟩
      | some j =>
          obtain ⟨hj, hjlt, e1⟩ := (stop_next hG hk).2 j hnx.symm
          subst hj
          simp only at hnt
          exact Or.inl ⟨k + 1, binvAt_entry hG hjlt (Or.inl (by
            show s.prog.base.reg.lpc + 1 = _
            omega)) hfn (succOk_sound hnt hE' hH)⟩
  · exact absurd hT (hnr k hk)


/-- **A step of the x86 flag machine from a state of the invariant is a checked step to a state
    of the invariant.** -/
theorem binv_step (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret) {s u : LstateMF}
    (hI : BInv T ann B G fn s) (h : x86Isa.lsemStepPMemF (singletonProgM fn B) s = some u) :
    x86IsaK.lsemStepPMemF (singletonProgM fn B) s = some u ∧ BInv T ann B G fn u := by
  rcases hI with ⟨k, hI⟩ | ⟨hfn, hle⟩
  · have hfetch := findInstrMem_single (B := B) hI.1
    cases hi : B[s.prog.base.reg.lpc]? with
    | none =>
        unfold Isa.lsemStepPMemF at h
        simp only [hfetch, hi] at h
        cases h
    | some i =>
        obtain ⟨k', hI', hpos⟩ := binvAt_norm hG hb hnr _ k s le_rfl hI i hi
        rcases hpos with hlt | ⟨heq, hnf, -⟩
        · obtain ⟨hK, hI''⟩ := binvAt_step_body hG hb hnr hI' hlt h
          exact ⟨hK, Or.inl ⟨k', hI''⟩⟩
        · exact binvAt_step_term hG hb hnr hI' heq hnf h
  · have hfetch := findInstrMem_single (B := B) hfn
    unfold Isa.lsemStepPMemF at h
    simp only [hfetch, List.getElem?_eq_none hle] at h
    cases h

/-- **Steps of the x86 flag machine from a state of the invariant are checked steps to a state
    of the invariant.** -/
theorem binv_steps (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret) :
    ∀ (n : Nat) (s t : LstateMF), BInv T ann B G fn s →
      Ascent.IsaCfg.Steps x86Isa (singletonProgM fn B) n s t →
      Ascent.IsaCfg.Steps x86IsaK (singletonProgM fn B) n s t ∧ BInv T ann B G fn t
  | 0, s, t, hI, h => by
      have hst : s = t := Option.some.inj h
      subst hst
      exact ⟨Ascent.IsaCfg.Steps.refl _ _ _, hI⟩
  | n + 1, s, t, hI, h => by
      obtain ⟨u, hu, hn⟩ := NFProgCallTreeExportTransfer.steps_succ h
      obtain ⟨hK, hIu⟩ := binv_step hG hb hnr hI hu
      obtain ⟨hK', hIt⟩ := binv_steps hG hb hnr n u t hIu hn
      have := (Ascent.IsaCfg.Steps.one hK).trans hK'
      rw [Nat.add_comm] at this
      exact ⟨this, hIt⟩


/-- **The state after a call keeps the invariant.** If every shadow instruction of a call in the
    body names a symbol of `T`, a state after the call of an event from a call site of the
    invariant is a state of the invariant. -/
theorem binv_callRet (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret)
    (hT : ∀ (k : Nat) (dst f : String) (srcs : List LOperand) (tag : MemTag),
      B[k]? = some (LprogIsa.callShadow dst f srcs, tag) → (T f).isSome = true)
    {e : NFProgCallTree.NFCall jasminDialect}
    {u u' : LstateMF} {a : Option (Ctxt.Valuation (d := jasminDialect) e.resTys)}
    (hI : BInv T ann B G fn u)
    (hq : NFProgCallTreeExport.CallRet (singletonProgM fn B) e u a u') :
    BInv T ann B G fn u' := by
  obtain ⟨dst, srcs, tag, p, res, hat, hf, -, hout⟩ := hq
  obtain ⟨rfl, -, -⟩ := NFProgCallTreeWebs.callOut_retRes hout
  have hpc : u.prog.base.reg.lpc = p := hat.2
  have hf' : B[u.prog.base.reg.lpc]? = some (LprogIsa.callShadow dst e.name srcs, tag) := by
    rw [hpc]; exact hf
  rcases hI with ⟨k, hI⟩ | ⟨-, hle⟩
  · obtain ⟨k', hI', hpos⟩ := binvAt_norm hG hb hnr _ k u le_rfl hI _ hf'
    rcases hpos with hlt | ⟨-, -, htm⟩
    · obtain ⟨hfn, hk, hs, hle, F, ss, V, A, C, O, Z, hH, hF, hW⟩ := hI'
      rw [take_cons B hlt hf'] at hW
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.mp (hT _ _ _ _ _ hf)
      have hw : segWalk T ann.flatten F ss ((LprogIsa.callShadow dst e.name srcs, tag) ::
          (B.drop (u.prog.base.reg.lpc + 1)).take
            (bstopOf (G.blk k').term (G.blk k') - (u.prog.base.reg.lpc + 1)))
          = segWalk T ann.flatten (startF (callFacts ann.flatten F ss dst)) SSt.start
            ((B.drop (u.prog.base.reg.lpc + 1)).take
              (bstopOf (G.blk k').term (G.blk k') - (u.prog.base.reg.lpc + 1))) := by
        simp only [segWalk, LprogIsa.procCall?_callShadow, hpr, Option.map_some]
      refine Or.inl ⟨k', ?_⟩
      refine ⟨(lfn_retRes _ _ _).trans hfn, hk, ?_, ?_, startF (callFacts ann.flatten F ss dst),
        SSt.start, _, _, _, _, _, holds_start _,
        startF_holds (callFacts_sound hF hH fun q hq => retRes_lvm_ne _ u hq), ?_⟩
      · show _ ≤ (LprogIsa.retRes dst _ u).prog.base.lpc
        rw [lpc_retRes]
        exact Nat.le_succ_of_le hs
      · show (LprogIsa.retRes dst _ u).prog.base.lpc ≤ _
        rw [lpc_retRes]
        exact hlt
      · have hl : (LprogIsa.retRes dst (NFProgCallTreeWebs.callResOf e.resTys res)
            u).prog.base.reg.lpc = u.prog.base.reg.lpc + 1 := lpc_retRes _ _ _
        rw [hl, ← hw]
        exact hW
    · simp [LprogIsa.callShadow, isTermR] at htm
  · rw [List.getElem?_eq_none hle] at hf'
    cases hf'


/-- **A call tree related on the x86 flag machine is related on the bounds-checked machine** from
    a state of the invariant, when every shadow instruction of a call names a symbol of `T`. -/
theorem tsim_checked_of_binv (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true)
    (hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret)
    (hT : ∀ (k : Nat) (dst f : String) (srcs : List LOperand) (tag : MemTag),
      B[k]? = some (LprogIsa.callShadow dst f srcs, tag) → (T f).isSome = true)
    {α : Type} {t : NFCallTree.CallTree (NFProgCallTree.nfCallSig jasminDialect) (Option α)}
    {s : LstateMF} {Post : α → LstateMF → Prop} (hI : BInv T ann B G fn s)
    (h : NFProgCallTreeExport.TSim x86Isa (singletonProgM fn B)
      (NFProgCallTreeExport.CallSite (singletonProgM fn B))
      (NFProgCallTreeExport.CallRet (singletonProgM fn B)) t s Post) :
    NFProgCallTreeExport.TSim x86IsaK (singletonProgM fn B)
      (NFProgCallTreeExport.CallSite (singletonProgM fn B))
      (NFProgCallTreeExport.CallRet (singletonProgM fn B)) t s Post := by
  refine NFProgCallTreeExportTransfer.TSim.transfer (fun a b => a = b ∧ BInv T ann B G fn b)
    (fun n s₁ t₁ s' hs hR => ?_) (fun e u u' hR hsi => hR.1 ▸ hsi)
    (fun e u u' a v' hR _ hq => ?_) (fun x m m' hR hp => hR.1 ▸ hp) ⟨rfl, hI⟩ h
  · obtain ⟨rfl, hI'⟩ := hR
    obtain ⟨hK, hIt⟩ := binv_steps hG hb hnr n s₁ t₁ hI' hs
    exact ⟨n, t₁, hK, rfl, hIt⟩
  · obtain ⟨rfl, hI'⟩ := hR
    exact ⟨v', hq, rfl, binv_callRet hG hb hnr hT hI' hq⟩

/-- **A call tree related on the x86 flag machine to a state at the counter `0` where the entry
    facts hold is related on the bounds-checked machine**, for a body without a return that passes
    the bounds check `idxInvCheckPB` at a table `T` naming the symbol of every call. -/
theorem tsim_checked {entry : List IdxFact} (h : idxInvCheckPB T entry ann B = true)
    (hnoRet : ∀ i ∈ B, i.1 ≠ LinstrR.Lret)
    (hT : ∀ (k : Nat) (dst f : String) (srcs : List LOperand) (tag : MemTag),
      B[k]? = some (LprogIsa.callShadow dst f srcs, tag) → (T f).isSome = true)
    {α : Type} {t : NFCallTree.CallTree (NFProgCallTree.nfCallSig jasminDialect) (Option α)}
    {s : LstateMF} {Post : α → LstateMF → Prop} (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr)
    (hS : NFProgCallTreeExport.TSim x86Isa (singletonProgM fn B)
      (NFProgCallTreeExport.CallSite (singletonProgM fn B))
      (NFProgCallTreeExport.CallRet (singletonProgM fn B)) t s Post) :
    NFProgCallTreeExport.TSim x86IsaK (singletonProgM fn B)
      (NFProgCallTreeExport.CallSite (singletonProgM fn B))
      (NFProgCallTreeExport.CallRet (singletonProgM fn B)) t s Post := by
  unfold idxInvCheckPB at h
  split at h
  · rename_i G hG
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    obtain ⟨hb, h0⟩ := h
    have hnr : ∀ k < G.blocks.size, (G.blk k).term ≠ .ret := by
      intro k hk hret
      have FB := blockFacts hG hk
      have hterm := FB.term
      have hlt : (G.blk k).stop - 1 < B.length := by
        have := FB.le; have := FB.lt; simp at *; omega
      obtain ⟨z, hz⟩ : ∃ z, B[(G.blk k).stop - 1]? = some z :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      rw [List.getElem?_map, hz, Option.map_some] at hterm
      rcases termOk_spec hterm with ⟨_, hT', _⟩ | ⟨_, _, _, hT', _⟩ | ⟨_, _, _, _, hT', _⟩ |
          ⟨-, hzr⟩
      all_goals try (rw [hret] at hT'; cases hT')
      exact hnoRet z (List.mem_of_getElem? hz) hzr
    by_cases hB : B.map Prod.fst = []
    · have hBn : B = [] := by simpa using hB
      refine tsim_checked_of_binv hG hb hnr hT (Or.inr ⟨hfn, ?_⟩) hS
      rw [hBn]
      exact Nat.zero_le _
    obtain ⟨hpos, hs0⟩ := cfgOf_start_zero hG hB
    have hF := startF_holds (A := s.prog.base.larr) (C := s.prog.base.cf)
      (O := s.prog.base.of) hent
    have hinv : ∀ f ∈ annAt ann 0, f.holds s.prog.base.reg.lvm s.prog.base.larr :=
      fun f hf => (IdxFact.toS_holds STerm.reg SArr.cell f).mp (entails_sound hF _ (h0 f hf))
    exact tsim_checked_of_binv hG hb hnr hT
      (Or.inl ⟨0, binvAt_entry hG hpos (Or.inl (hpc.trans hs0.symm)) hfn hinv⟩) hS
  · cases h

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChecked
