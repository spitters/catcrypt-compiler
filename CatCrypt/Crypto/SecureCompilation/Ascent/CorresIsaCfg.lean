/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsa
public import HaxAscent.Calculus.CorresMCutPoint

/-!
# The cut-point rule for labelled control-flow programs over an instruction set

`CorresIsa isa P SR Pre fa fuel` is the correspondence `CorresM` at the run
`Isa.lsemFuelMemF` of the `Lprog` program `P`. This module instantiates the cut-point rule
of `HaxAscent.Calculus.CorresMCutPoint` at that run: the interpreter with fuel is
`isa.lsemFuelMemF P`, its one-step function is the fetch-and-step `isa.lsemStepPMemF P`,
and a state is halted when no instruction is fetched at its program counter. The two run
equations of the rule are `Isa.lsemFuelMemF_halt` and `lsemFuelMemF_stepI`.

A run between two cut points is `Steps isa P n s t`: `n` iterations of the one-step
function from `s` end in `t`. The segment lemmas produce such runs:

* `steps_of_runL` for a straight-line stretch `seg` in the middle of the body
  (`P.body = pre ++ seg ++ post`), from the list run `Isa.runL`; `steps_of_runL_halted` for
  a stretch at the end of the body, which ends in a halted state, and
  `lsemFuelMemF_of_runL_atPc`, the form of `Isa.lsemFuelMemF_of_runL` over `atPc`;
* `steps_label`, `steps_cond_taken`, `steps_cond_not_taken`, `steps_goto` for the control
  instructions, from `Isa.step_label`, `Isa.step_cond` and `Isa.step_goto`.

The position of a state is `atPc P k s` (in the function of `P` at counter `k`) or
`atLabel P l s` (at the counter a jump to the label `l` lands on, one past the first
declaration of `l`). A cut point is `none`, the entry of the body at counter `0`, or
`some l`, the label `l`; `atCut` is the corresponding position predicate.

## Main results

* `atPc`, `atLabel`, `atCut`, `Halted`, `Steps`: positions, halted states and segment runs.
* `lsemFuelMemF_stepI`: one step of the one-step function consumes one unit of fuel.
* `steps_of_runL`, `steps_of_runL_halted`, `lsemFuelMemF_of_runL_atPc`: straight-line
  segments.
* `steps_label`, `steps_cond_taken`, `steps_cond_not_taken`, `steps_goto`: control steps.
* `corresIsa_of_cutPoint`: `CorresIsa` from an invariant family over an arbitrary type of
  cut points.
* `corresIsa_of_labels`: `CorresIsa` from an invariant family indexed by the entry and the
  labels of `P`, with one verification condition per cut point.
* `corresIsa_of_labels_floyd`: the instance with the abstract state fixed at its entry
  value and the exit condition `SR m' (fa a)` at a halted state.
* `lsemFuelMemF_of_labels_floyd`, `corresIsaRun_of_labels_floyd`: the same rule with the
  fuel `B * (μ none m a + 1)` of the initial state, and its form as `CorresIsaRun`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace IsaCfg

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LLabel LabelKind LOperand
  LinstrR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM findInstrMem
  findLabelMem evalJumpMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)

/-! ## Positions -/

/-- The state is in the function of `P` at program counter `k`. -/
def atPc (P : LprogM) (k : Nat) (s : LstateMF) : Prop :=
  s.prog.lfn = P.lfn ∧ s.prog.base.lpc = k

/-- The state is at the label `l` of `P`: in the function of `P`, at the counter one past
    the first declaration of `l` in the body, where a jump to `l` lands. -/
def atLabel (P : LprogM) (l : LLabel) (s : LstateMF) : Prop :=
  ∃ q, findLabelMem l P.body = some q ∧ atPc P (q + 1) s

/-- The position of a cut point: `none` is the entry of the body, at counter `0`, and
    `some l` is the label `l`. -/
def atCut (P : LprogM) : Option LLabel → LstateMF → Prop
  | none, s => atPc P 0 s
  | some l, s => atLabel P l s

/-- No instruction is fetched at the program counter of the state. -/
def Halted (P : LprogM) (s : LstateMF) : Prop := findInstrMem P s.prog = none

/-- The state `s` with the program counter advanced by one. -/
def next (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := s.prog.base.nextPc } }

/-- The state `s` with the program counter set to `k`. -/
def goto (s : LstateMF) (k : Nat) : LstateMF :=
  { s with prog := { s.prog with base := s.prog.base.setLpc k } }

theorem atPc_next {P : LprogM} {k : Nat} {s : LstateMF} (h : atPc P k s) :
    atPc P (k + 1) (next s) :=
  ⟨h.1, by simp only [next, VIR.JasminLsemMemLoop.LstateM.lpc_nextPc, h.2]⟩

theorem atPc_goto {P : LprogM} {k : Nat} {s : LstateMF} (j : Nat) (h : atPc P k s) :
    atPc P j (goto s j) :=
  ⟨h.1, rfl⟩

theorem atLabel_goto {P : LprogM} {k q : Nat} {l : LLabel} {s : LstateMF}
    (hl : findLabelMem l P.body = some q) (h : atPc P k s) : atLabel P l (goto s (q + 1)) :=
  ⟨q, hl, atPc_goto (q + 1) h⟩

/-- At counter `k` in the function of `P`, the fetch reads the body at `k`. -/
theorem findInstrMem_of_atPc {P : LprogM} {k : Nat} {s : LstateMF} (h : atPc P k s) :
    findInstrMem P s.prog = P.body[k]? := by
  unfold findInstrMem
  rw [if_pos h.1, h.2]

/-- A state at or past the end of the body is halted. -/
theorem halted_of_atPc {P : LprogM} {k : Nat} {s : LstateMF} (h : atPc P k s)
    (hk : P.body.length ≤ k) : Halted P s := by
  unfold Halted
  rw [findInstrMem_of_atPc h, List.getElem?_eq_none hk]

/-! ## The run equations and segment runs -/

/-- One step of the fetch-and-step function consumes one unit of fuel. -/
theorem lsemFuelMemF_stepI (isa : Isa) (P : LprogM) (fuel : Nat) (s s' : LstateMF)
    (h : isa.lsemStepPMemF P s = some s') :
    isa.lsemFuelMemF P (fuel + 1) s = isa.lsemFuelMemF P fuel s' := by
  unfold Isa.lsemStepPMemF at h
  cases hf : findInstrMem P s.prog with
  | none => rw [hf] at h; cases h
  | some i =>
      rw [hf] at h
      exact isa.lsemFuelMemF_step P fuel i s s' hf h

/-- `n` iterations of the fetch-and-step function of `P` from `s` end in `t`. -/
def Steps (isa : Isa) (P : LprogM) (n : Nat) (s t : LstateMF) : Prop :=
  CutPoint.iter (isa.lsemStepPMemF P) n s = some t

theorem Steps.refl (isa : Isa) (P : LprogM) (s : LstateMF) : Steps isa P 0 s s := rfl

theorem Steps.trans {isa : Isa} {P : LprogM} {n k : Nat} {s t u : LstateMF}
    (h : Steps isa P n s t) (h' : Steps isa P k t u) : Steps isa P (n + k) s u :=
  CutPoint.iter_add _ n k s t u h h'

theorem Steps.one {isa : Isa} {P : LprogM} {s t : LstateMF}
    (h : isa.lsemStepPMemF P s = some t) : Steps isa P 1 s t := by
  simp only [Steps, CutPoint.iter, h, Option.bind_some]

/-- At counter `k` holding the instruction `i`, the fetch-and-step function is the step
    of `i`. -/
theorem lsemStepPMemF_of_atPc (isa : Isa) {P : LprogM} {k : Nat} {s : LstateMF}
    {i : LinstrRM} (h : atPc P k s) (hi : P.body[k]? = some i) :
    isa.lsemStepPMemF P s = isa.step P i s := by
  unfold Isa.lsemStepPMemF
  rw [findInstrMem_of_atPc h, hi]

/-- A run of steps to a halted state is the run of the interpreter at every fuel from the
    number of steps. -/
theorem lsemFuelMemF_of_steps (isa : Isa) (P : LprogM) {n : Nat} {s t : LstateMF}
    (h : Steps isa P n s t) (ht : Halted P t) (k : Nat) :
    isa.lsemFuelMemF P (n + k) s = some t :=
  CutPoint.run_of_iter (isa.lsemFuelMemF P) (isa.lsemStepPMemF P) (Halted P)
    (fun fuel m hm => isa.lsemFuelMemF_halt P fuel m hm) (lsemFuelMemF_stepI isa P) n k s t h ht

/-! ## Straight-line segments -/

/-- **A straight-line segment between two counters.** When the body of `P` is
    `pre ++ seg ++ post`, the state is at counter `pre.length`, and every step of an
    instruction of `seg` stays in the function and advances the counter by one, a list run
    `Isa.runL` of `seg` to `t` is a run of `seg.length` steps of `P` to `t`, which is at
    counter `pre.length + seg.length`. -/
theorem steps_of_runL (isa : Isa) (P : LprogM) :
    ∀ (seg pre post : List LinstrRM) (s t : LstateMF), P.body = pre ++ seg ++ post →
      atPc P pre.length s →
      (∀ i ∈ seg, ∀ u u', isa.step P i u = some u' →
        u'.prog.lfn = u.prog.lfn ∧ u'.prog.base.lpc = u.prog.base.lpc + 1) →
      isa.runL P seg s = some t →
      Steps isa P seg.length s t ∧ atPc P (pre.length + seg.length) t := by
  intro seg
  induction seg with
  | nil =>
      intro pre post s t _ hat _ hrun
      cases hrun
      exact ⟨Steps.refl isa P s, hat⟩
  | cons i seg ih =>
      intro pre post s t hbody hat hstep hrun
      simp only [Isa.runL, Option.bind_eq_some_iff] at hrun
      obtain ⟨u, hu, hrun⟩ := hrun
      have hi : P.body[pre.length]? = some i := by
        rw [hbody, List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
        rfl
      have h1 : Steps isa P 1 s u := Steps.one (by rw [lsemStepPMemF_of_atPc isa hat hi, hu])
      obtain ⟨hufn, hupc⟩ := hstep i (List.mem_cons_self ..) s u hu
      have hat' : atPc P (pre ++ [i]).length u :=
        ⟨hufn.trans hat.1, by rw [hupc, hat.2, List.length_append, List.length_singleton]⟩
      obtain ⟨h2, hend⟩ := ih (pre ++ [i]) post u t
        (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        hat' (fun j hj => hstep j (List.mem_cons_of_mem i hj)) hrun
      refine ⟨?_, ?_⟩
      · have h := h1.trans h2
        rwa [Nat.add_comm, ← List.length_cons] at h
      · rw [List.length_append, List.length_singleton] at hend
        rw [List.length_cons]
        rwa [show pre.length + (seg.length + 1) = pre.length + 1 + seg.length by omega]

/-- **A straight-line segment at the end of the body** ends in a halted state. -/
theorem steps_of_runL_halted (isa : Isa) (P : LprogM) (seg pre : List LinstrRM)
    (s t : LstateMF) (hbody : P.body = pre ++ seg) (hat : atPc P pre.length s)
    (hstep : ∀ i ∈ seg, ∀ u u', isa.step P i u = some u' →
      u'.prog.lfn = u.prog.lfn ∧ u'.prog.base.lpc = u.prog.base.lpc + 1)
    (hrun : isa.runL P seg s = some t) :
    Steps isa P seg.length s t ∧ Halted P t := by
  obtain ⟨h, hend⟩ := steps_of_runL isa P seg pre [] s t (by rw [hbody, List.append_nil])
    hat hstep hrun
  exact ⟨h, halted_of_atPc hend (by rw [hbody, List.length_append])⟩

/-- `Isa.lsemFuelMemF_of_runL` over `atPc`: a straight-line stretch at the end of the body
    is the run of the interpreter with fuel its length. -/
theorem lsemFuelMemF_of_runL_atPc (isa : Isa) (P : LprogM) (seg pre : List LinstrRM)
    (s t : LstateMF) (hbody : P.body = pre ++ seg) (hat : atPc P pre.length s)
    (hstep : ∀ i ∈ seg, ∀ u u', isa.step P i u = some u' →
      u'.prog.lfn = u.prog.lfn ∧ u'.prog.base.lpc = u.prog.base.lpc + 1)
    (hrun : isa.runL P seg s = some t) : isa.lsemFuelMemF P seg.length s = some t :=
  isa.lsemFuelMemF_of_runL P seg pre s t hbody hat.1 hat.2 hstep hrun

/-! ## Control steps -/

/-- A jump to a label declared at index `q` sets the counter to `q + 1`. -/
theorem evalJumpMem_of_findLabelMem {P : LprogM} {l : LLabel} {q : Nat}
    (hl : findLabelMem l P.body = some q) (s : LstateMF) :
    (evalJumpMem P l s.prog).map (fun p => { s with prog := p }) = some (goto s (q + 1)) := by
  simp only [evalJumpMem, hl, Option.map_some, goto]

/-- **A label** is one step that advances the counter. -/
theorem steps_label (isa : Isa) {P : LprogM} {k : Nat} {s : LstateMF} {kind : LabelKind}
    {l : LLabel} {tag : MemTag} (hat : atPc P k s)
    (hi : P.body[k]? = some (.Llabel kind l, tag)) :
    Steps isa P 1 s (next s) ∧ atPc P (k + 1) (next s) :=
  ⟨Steps.one (by rw [lsemStepPMemF_of_atPc isa hat hi, isa.step_label]; rfl), atPc_next hat⟩

/-- **A conditional jump whose condition holds** is one step to its label. -/
theorem steps_cond_taken (isa : Isa) {P : LprogM} {k q : Nat} {s : LstateMF} {c : LOperand}
    {l : LLabel} {tag : MemTag} (hat : atPc P k s)
    (hi : P.body[k]? = some (.Lcond c l, tag)) (hc : isa.condEval s c = true)
    (hl : findLabelMem l P.body = some q) :
    Steps isa P 1 s (goto s (q + 1)) ∧ atLabel P l (goto s (q + 1)) :=
  ⟨Steps.one (by
      rw [lsemStepPMemF_of_atPc isa hat hi, isa.step_cond, if_pos hc,
        evalJumpMem_of_findLabelMem hl]),
    atLabel_goto hl hat⟩

/-- **A conditional jump whose condition fails** is one step that advances the counter. -/
theorem steps_cond_not_taken (isa : Isa) {P : LprogM} {k : Nat} {s : LstateMF}
    {c : LOperand} {l : LLabel} {tag : MemTag} (hat : atPc P k s)
    (hi : P.body[k]? = some (.Lcond c l, tag)) (hc : isa.condEval s c = false) :
    Steps isa P 1 s (next s) ∧ atPc P (k + 1) (next s) :=
  ⟨Steps.one (by
      rw [lsemStepPMemF_of_atPc isa hat hi, isa.step_cond, if_neg (by rw [hc]; decide)]
      rfl),
    atPc_next hat⟩

/-- **A goto within the function of `P`** is one step to its label. -/
theorem steps_goto (isa : Isa) {P : LprogM} {k q : Nat} {s : LstateMF} {l : LLabel}
    {tag : MemTag} (hat : atPc P k s) (hi : P.body[k]? = some (.Lgoto (P.lfn, l), tag))
    (hl : findLabelMem l P.body = some q) :
    Steps isa P 1 s (goto s (q + 1)) ∧ atLabel P l (goto s (q + 1)) :=
  ⟨Steps.one (by
      rw [lsemStepPMemF_of_atPc isa hat hi, isa.step_goto, if_pos rfl,
        evalJumpMem_of_findLabelMem hl]),
    atLabel_goto hl hat⟩

/-! ## The correspondence from cut points -/

section Rule

variable {AState L E : Type}

/-- **`CorresIsa` from cut points.** `CutPoint.corresM_run` at the run of the instruction
    set `isa` on `P`. If `SR` under `Pre` implies an invariant at a cut point whose bound
    `B * (μ l m a + 1)` is at most `fuel` (`hentry`), from every cut point a run of at most
    `B` steps reaches an exit relation or an invariant at a smaller measure (`hseg`), and
    the exit relations imply that the state is halted (`hfinal`) and related to `fa a`
    (`hexit`), then `P` corresponds to `fa` at `fuel`. -/
theorem corresIsa_of_cutPoint (isa : Isa) (P : LprogM) (SR : LstateMF → AState → Prop)
    (Pre : AState → Prop) (fa : AState → AState)
    (T : AState → AState → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'')
    (Inv : L → LstateMF → AState → Prop) (Post : E → LstateMF → AState → Prop)
    (μ : L → LstateMF → AState → Nat) (B fuel : Nat)
    (hentry : ∀ m a, SR m a → Pre a → ∃ l, Inv l m a ∧ B * (μ l m a + 1) ≤ fuel)
    (hseg : ∀ l m a, Inv l m a → ∃ n m' a', n ≤ B ∧ Steps isa P n m m' ∧ T a a' ∧
      ((∃ e, Post e m' a') ∨ ∃ l', Inv l' m' a' ∧ μ l' m' a' < μ l m a))
    (hfinal : ∀ e m a, Post e m a → Halted P m)
    (hexit : ∀ a m' a' e, Pre a → T a a' → Post e m' a' → SR m' (fa a)) :
    CorresIsa isa P SR Pre fa fuel := by
  intro m a hSR hPre
  exact CutPoint.corresM_run (C := Unit) (fun _ => isa.lsemFuelMemF P)
    (fun _ => isa.lsemStepPMemF P) () (Halted P)
    (fun fuel m hm => isa.lsemFuelMemF_halt P fuel m hm) (lsemFuelMemF_stepI isa P)
    SR Pre fa T htrans Inv Post μ B fuel hentry hseg hfinal hexit m a hSR hPre

/-- **`CorresIsa` from invariants at the entry and the labels of `P`.** The cut points are
    the entry of the body (`none`) and its labels (`some l`), and the invariant `Inv c` is
    required at the states at the position `atCut P c`. There is one verification
    condition per cut point (`hseg`): from a state at the cut point satisfying its
    invariant, a run of at most `B` steps reaches a state satisfying an exit relation, or
    a state at a cut point satisfying the invariant of that cut point at a smaller
    measure. -/
theorem corresIsa_of_labels (isa : Isa) (P : LprogM) (SR : LstateMF → AState → Prop)
    (Pre : AState → Prop) (fa : AState → AState)
    (T : AState → AState → Prop) (htrans : ∀ a a' a'', T a a' → T a' a'' → T a a'')
    (Inv : Option LLabel → LstateMF → AState → Prop) (Post : E → LstateMF → AState → Prop)
    (μ : Option LLabel → LstateMF → AState → Nat) (B fuel : Nat)
    (hentry : ∀ m a, SR m a → Pre a →
      ∃ c, atCut P c m ∧ Inv c m a ∧ B * (μ c m a + 1) ≤ fuel)
    (hseg : ∀ c m a, atCut P c m → Inv c m a →
      ∃ n m' a', n ≤ B ∧ Steps isa P n m m' ∧ T a a' ∧
        ((∃ e, Post e m' a') ∨ ∃ c', atCut P c' m' ∧ Inv c' m' a' ∧ μ c' m' a' < μ c m a))
    (hfinal : ∀ e m a, Post e m a → Halted P m)
    (hexit : ∀ a m' a' e, Pre a → T a a' → Post e m' a' → SR m' (fa a)) :
    CorresIsa isa P SR Pre fa fuel :=
  corresIsa_of_cutPoint isa P SR Pre fa T htrans
    (fun c m a => atCut P c m ∧ Inv c m a) Post μ B fuel
    (fun m a hSR hPre => by
      obtain ⟨c, hat, hI, hb⟩ := hentry m a hSR hPre
      exact ⟨c, ⟨hat, hI⟩, hb⟩)
    (fun c m a hI => by
      obtain ⟨n, m', a', hn, hs, hT, hd⟩ := hseg c m a hI.1 hI.2
      refine ⟨n, m', a', hn, hs, hT, ?_⟩
      cases hd with
      | inl he => exact Or.inl he
      | inr hc =>
          obtain ⟨c', hat', hI', hlt⟩ := hc
          exact Or.inr ⟨c', ⟨hat', hI'⟩, hlt⟩)
    hfinal hexit

/-- **`CorresIsa` from invariants over the entry abstract state.** The instance of
    `corresIsa_of_labels` in which the abstract state is the entry state throughout and a
    segment exits at a halted state related to `fa a`: `Pre` and `SR` at the entry give the
    invariant of the entry cut point (`hentry`), and from a state at a cut point
    satisfying its invariant a run of at most `B` steps reaches a halted state related to
    `fa a`, or a state at a cut point satisfying its invariant at a smaller measure
    (`hseg`). The fuel is `B * (N + 1)` for a bound `N` on the measure at the entry. -/
theorem corresIsa_of_labels_floyd (isa : Isa) (P : LprogM) (SR : LstateMF → AState → Prop)
    (Pre : AState → Prop) (fa : AState → AState)
    (Inv : Option LLabel → LstateMF → AState → Prop)
    (μ : Option LLabel → LstateMF → AState → Nat) (B N : Nat)
    (hentry : ∀ m a, SR m a → Pre a → atCut P none m ∧ Inv none m a ∧ μ none m a ≤ N)
    (hseg : ∀ c m a, atCut P c m → Inv c m a →
      ∃ n m', n ≤ B ∧ Steps isa P n m m' ∧
        ((Halted P m' ∧ SR m' (fa a)) ∨
          ∃ c', atCut P c' m' ∧ Inv c' m' a ∧ μ c' m' a < μ c m a)) :
    CorresIsa isa P SR Pre fa (B * (N + 1)) :=
  corresIsa_of_labels (E := Unit) isa P SR Pre fa (fun a a' => a' = a)
    (fun _ _ _ h h' => h'.trans h) Inv (fun _ m a => Halted P m ∧ SR m (fa a)) μ B
    (B * (N + 1))
    (fun m a hSR hPre => by
      obtain ⟨hat, hI, hμ⟩ := hentry m a hSR hPre
      exact ⟨none, hat, hI, Nat.mul_le_mul_left B (by omega)⟩)
    (fun c m a hat hI => by
      obtain ⟨n, m', hn, hs, hd⟩ := hseg c m a hat hI
      refine ⟨n, m', a, hn, hs, rfl, ?_⟩
      cases hd with
      | inl he => exact Or.inl ⟨(), he⟩
      | inr hc => exact Or.inr hc)
    (fun _ _ _ h => h.1)
    (fun a m' a' _ _ hT h => by subst hT; exact h.2)

/-- **The run from invariants, with the fuel of the initial state.** Under the segment
    condition of `corresIsa_of_labels_floyd`, from a state `m` related by `SR` to an
    abstract state `a` satisfying `Pre`, the run of `P` with fuel `B * (μ none m a + 1)`,
    the step bound times the successor of the measure of `m` at the entry, halts in a state
    related to `fa a`. The measure is not bounded over the related states. -/
theorem lsemFuelMemF_of_labels_floyd (isa : Isa) (P : LprogM) (SR : LstateMF → AState → Prop)
    (Pre : AState → Prop) (fa : AState → AState)
    (Inv : Option LLabel → LstateMF → AState → Prop)
    (μ : Option LLabel → LstateMF → AState → Nat) (B : Nat)
    (hentry : ∀ m a, SR m a → Pre a → atCut P none m ∧ Inv none m a)
    (hseg : ∀ c m a, atCut P c m → Inv c m a →
      ∃ n m', n ≤ B ∧ Steps isa P n m m' ∧
        ((Halted P m' ∧ SR m' (fa a)) ∨
          ∃ c', atCut P c' m' ∧ Inv c' m' a ∧ μ c' m' a < μ c m a))
    (m : LstateMF) (a : AState) (hSR : SR m a) (hPre : Pre a) :
    ∃ t, isa.lsemFuelMemF P (B * (μ none m a + 1)) m = some t ∧ SR t (fa a) := by
  have h : CorresIsa (AState := AState × Bool) isa P
      (fun m' p => if p.2 = true then SR m' p.1 else (m' = m ∧ p.1 = a))
      (fun p => p.2 = false) (fun p => (fa p.1, true)) (B * (μ none m a + 1)) :=
    corresIsa_of_labels_floyd isa P _ _ _ (fun c m' p => Inv c m' p.1)
      (fun c m' p => μ c m' p.1) B (μ none m a)
      (by
        rintro m' ⟨a', b⟩ hS hb
        obtain rfl : b = false := hb
        obtain ⟨rfl, rfl⟩ : m' = m ∧ a' = a := by simpa using hS
        obtain ⟨hat, hI⟩ := hentry _ _ hSR hPre
        exact ⟨hat, hI, Nat.le_refl _⟩)
      (by
        rintro c m' ⟨a', b⟩ hat hI
        obtain ⟨n, m'', hn, hs, hd⟩ := hseg c m' a' hat hI
        exact ⟨n, m'', hn, hs, by simpa using hd⟩)
  obtain ⟨t, ht, hS⟩ := h m (a, false) (by simp) rfl
  exact ⟨t, ht, by simpa using hS⟩

/-- **`CorresIsaRun` from invariants over the entry abstract state**:
    `lsemFuelMemF_of_labels_floyd` with the fuel quantified. -/
theorem corresIsaRun_of_labels_floyd (isa : Isa) (P : LprogM)
    (SR : LstateMF → AState → Prop) (Pre : AState → Prop) (fa : AState → AState)
    (Inv : Option LLabel → LstateMF → AState → Prop)
    (μ : Option LLabel → LstateMF → AState → Nat) (B : Nat)
    (hentry : ∀ m a, SR m a → Pre a → atCut P none m ∧ Inv none m a)
    (hseg : ∀ c m a, atCut P c m → Inv c m a →
      ∃ n m', n ≤ B ∧ Steps isa P n m m' ∧
        ((Halted P m' ∧ SR m' (fa a)) ∨
          ∃ c', atCut P c' m' ∧ Inv c' m' a ∧ μ c' m' a < μ c m a)) :
    CorresIsaRun isa P SR Pre fa := fun m a hSR hPre => by
  obtain ⟨t, ht, hS⟩ :=
    lsemFuelMemF_of_labels_floyd isa P SR Pre fa Inv μ B hentry hseg m a hSR hPre
  exact ⟨_, t, ht, hS⟩

end Rule

end IsaCfg

end CatCrypt.Crypto.SecureCompilation.Ascent
