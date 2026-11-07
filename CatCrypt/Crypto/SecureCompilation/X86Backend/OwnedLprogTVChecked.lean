/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked

@[expose] public section

set_option autoImplicit false

/-!
# The checker `ownedCheckM` on bounds-checked runs

`OwnedLprogTV.ownedCheckM_sound` relates halting runs of `lsemFuelMemF`, which reads an
array at the index modulo its length. `ownedCheckMC` is `ownedCheckM` with one more check
per block pair: every index obligation of the rewritten block is an index obligation of the
source block, over registers live at the block. An index obligation (`SObl`) is the
symbolic index of an indexed load or store with the length of its array (`oblOf`); the
obligations of a block are collected along its symbolic run (`symObl`). A halting checked
run of the source (`lsemFuelMemFk true`) satisfies the obligations of every block it
passes, so the rewritten body satisfies its own, and its run is a halting checked run.

The block pairs are compared from must-constant facts at block entry. A fact (`CFact`) states
that a register holds an immediate; the symbolic run of a block starts from its facts
(`startC`), so a register known to hold `63` at entry is the immediate `63` in the symbolic
words of the block. The facts of each of the two graphs are computed by `constAnnot`, which
is untrusted, and checked as an invariant of that graph by `factCheck`: block `0` has no
fact, and the run of every block from its facts leaves each register of a fact of a
successor at that fact's immediate. A halting run therefore satisfies the facts of every
block it enters, on each of the two bodies.

The checks take the symbolic step and the symbolic branch condition as trailing arguments
that default to the x86 ones, as in `OwnedLprogTV`. The theorems with the suffix `_at` are
stated for an instruction set `I : LprogIsa.Isa` whose step the symbolic step describes
(`OwnedLprogTV.SymLaws`); the theorems about `lsemFuelMemF` and `lsemFuelMemFk` are their
instances at `X86Isa.x86Isa`.

## Main definitions

* `SObl`, `SObl.holds`, `oblOf`, `symObl`: index obligations and their collection.
* `RunLOk`: the steps of a list of instructions are in bounds.
* `CFact`, `FactsAt`, `startC`: must-constant facts and the symbolic start state they give.
* `factsOk`, `factCheck`: the invariant check of the facts; `constAnnot`: the annotation.
* `blockOkS`, `blockRunsS`, `runsOfC`, `CheckedC`: the block check from given start states,
  its shared runs, and the facts the checks establish.
* `oblOk`, `oblCheckWith`, `ownedCheckMC`: the checks; `hasOutsB`, `callFreePieces`, `blocksRunCB`:
  the conditions under which an acceptance of `ownedCheckMC` compares an output.

## Main results

* `oblOf_iff`, `symObl_sound_at`, `symObl_sound`: the obligations of a step and of a stretch
  hold exactly when its accesses are in bounds.
* `runIdxOk_runL_at`, `runIdxOk_of_runL_at`, `runIdxOk_runL`, `runIdxOk_of_runL`: the
  in-bounds condition of a run splits at a stretch.
* `holds_startC`, `factsAt_of_holds`, `factsOk_spec`: the facts describe the block entry and
  pass to the successors.
* `blockOkR_specS`, `checkedC_of_withR`, `checkedC_of_with`, `ownedCheckMC_checked_at`: the
  shared check gives `CheckedC`; `ownedCheckWith` gives it with no fact.
* `ownedCheckMC_hasOuts`: an accepted pair has an output to compare and no block whose
  symbolic run fails between its calls.
* `OwnedCheckFuel.sim_stepCF`, `OwnedCheckFuel.simAtCF_all`,
  `OwnedCheckFuel.checkedC_sound_at_fuel`, `OwnedCheckFuel.ownedCheckWithC_sound_at_fuel`,
  `OwnedCheckFuel.ownedCheckMC_idx_sound_at_fuel`: the simulation of the rewritten body, with
  its fuel at most `OwnedCheckFuel.checkFuel`.
* `ownedCheckWithC_sound_at`, `ownedCheckMC_sound_at`: soundness on bounds-checked runs of an
  instruction set.
* `ownedCheckWithC_sound`, `ownedCheckMC_sound`: soundness on bounds-checked runs of the
  flag machine.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
  (x86Isa x86Isa_lsemFuelMemF x86Isa_runL x86Isa_lsemFuelMemFk x86Isa_RunIdxOk)

/-! ## 1. Index obligations -/

/-- An index obligation: the symbolic index of an access and the length of its array. -/
abbrev SObl : Type := STerm × Nat

/-- An index obligation holds: an index of width `64` is below the length. -/
def SObl.holds (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) (o : SObl) :
    Prop :=
  (o.1.ev V A C O).1 = 64 → (castW (o.1.ev V A C O) 64).toNat < o.2

/-- The index obligations of an instruction from the symbolic state `ss`: the index of an
    indexed load tagged `.load w n` or an indexed store tagged `.store w n`, with `n`. -/
def oblOf (i : LinstrRM) (ss : SSt) : List SObl :=
  match i.2 with
  | .load _ n =>
      match loadStruct? i.1 with
      | some (_, _, idx) => [(ss.regs idx, n)]
      | none => []
  | .store _ n =>
      match storeStruct? i.1 with
      | some (_, _, idx, _) => [(ss.regs idx, n)]
      | none => []
  | _ => []

theorem idxBelowB_iff {s : LstateMF} {idx : String} {n : Nat} {x : Σ w, BitVec w}
    (hx : s.prog.base.reg.lvm idx = x) :
    idxBelowB s idx n = true ↔ (x.1 = 64 → (castW x 64).toNat < n) := by
  unfold idxBelowB
  rw [getW_eq, hx]
  by_cases h : x.1 = 64 <;> simp [h]

/-- **The obligations of a step hold exactly when the step is in bounds.** -/
theorem oblOf_iff {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {ss : SSt} {s : LstateMF} (hr : ∀ q, s.prog.base.reg.lvm q = (ss.regs q).ev V A C O)
    (i : LinstrRM) : idxOkB i s = true ↔ ∀ o ∈ oblOf i ss, o.holds V A C O := by
  obtain ⟨x, tag⟩ := i
  cases tag with
  | load w n =>
      simp only [idxOkB, oblOf]
      cases hl : loadStruct? x with
      | some p =>
          obtain ⟨_, _, idx⟩ := p
          simp [idxBelowB_iff (hr idx), SObl.holds]
      | none => simp
  | store w n =>
      simp only [idxOkB, oblOf]
      cases hl : storeStruct? x with
      | some p =>
          obtain ⟨_, _, idx, _⟩ := p
          simp [idxBelowB_iff (hr idx), SObl.holds]
      | none => simp
  | _ => simp [idxOkB, oblOf]

theorem idxOkB_of_none {i : LinstrRM} {s : LstateMF} (h1 : loadStruct? i.1 = none)
    (h2 : storeStruct? i.1 = none) : idxOkB i s = true := by
  obtain ⟨x, tag⟩ := i
  cases tag <;> simp_all [idxOkB]

theorem idxOkB_goto (x : String) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    idxOkB (.Lgoto (x, l), tag) s = true := idxOkB_of_none rfl rfl

theorem idxOkB_cond (c : LOperand) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    idxOkB (.Lcond c l, tag) s = true := idxOkB_of_none rfl rfl

/-- The index obligations of a list of instructions, collected along its symbolic run under
    the symbolic step `sym`. -/
def symObl : List LinstrRM → SSt → optParam (LinstrRM → SSt → SOut) symStep → List SObl
  | [], _, _ => []
  | i :: is, ss, sym =>
      oblOf i ss ++
        match sym i ss with
        | .ok ss1 _ => symObl is ss1 sym
        | _ => []

/-- A label at the head of a list contributes no index obligation, when `sym` describes a
    label as the identity. -/
theorem symObl_label_at {sym : LinstrRM → SSt → SOut}
    (hlab : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, sym i ss = .ok ss [])
    {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) (ss : SSt) :
    symObl (i :: is) ss sym = symObl is ss sym := by
  obtain ⟨x, tag⟩ := i
  have hx : loadStruct? x = none ∧ storeStruct? x = none := by
    cases x <;> simp_all [isLbl, loadStruct?, storeStruct?]
  have ho : oblOf (x, tag) ss = [] := by
    cases tag <;> simp [oblOf, hx.1, hx.2]
  simp only [symObl, ho, hlab h, List.nil_append]

theorem symObl_label {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) (ss : SSt) :
    symObl (i :: is) ss = symObl is ss :=
  symObl_label_at (fun h ss => symStep_label h ss) h is ss

/-- The steps of a list of instructions of the instruction set `I` are in bounds. The
    instruction set defaults to `x86Isa`. -/
def RunLOk (P : LprogM) : List LinstrRM → LstateMF → optParam Isa x86Isa → Prop
  | [], _, _ => True
  | i :: is, s, I => idxOkB i s = true ∧ ∀ s1, I.step P i s = some s1 → RunLOk P is s1 I

/-- **The obligations of a stretch hold exactly when its run is in bounds**, for a run of
    the instruction set `I` from a state the start of a successful symbolic run describes,
    under a symbolic step that describes the step of `I`. -/
theorem symObl_sound_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    (hsym : ∀ (P : LprogM) (i : LinstrRM) (ss : SSt), StepSound (I.step P i) ss (sym i ss))
    (P : LprogM) :
    ∀ (is : List LinstrRM) (ss : SSt) (V : String → Σ w, BitVec w) (A : String → ArrCell)
      (C O Z : Bool) (s u : LstateMF), Holds V A C O Z ss s →
      (∃ ss' gs, symRun is ss sym = .ok ss' gs) → I.runL P is s = some u →
      (RunLOk P is s I ↔ ∀ o ∈ symObl is ss sym, o.holds V A C O)
  | [], _, _, _, _, _, _, _, _, _, _, _ => by simp [RunLOk, symObl]
  | i :: is, ss, V, A, C, O, Z, s, u, hs, ⟨ss', gs, hr⟩, hu => by
      have hstep := hsym P i ss V A C O Z s hs
      simp only [Isa.runL] at hu
      obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp hu
      simp only [symRun] at hr
      cases h1 : sym i ss with
      | ok ss1 g1 =>
          rw [h1] at hstep
          simp only [h1] at hr
          cases h2 : symRun is ss1 sym with
          | ok ss2 g2 =>
              have hH1 := (hstep.1 s1 e1).2.1
              have ih := symObl_sound_at hsym P is ss1 V A C O Z s1 u hH1 ⟨_, _, h2⟩ e2
              have hi := oblOf_iff hs.1 i
              simp only [RunLOk, symObl, h1, List.mem_append]
              constructor
              · rintro ⟨hok, hrest⟩ o (ho | ho)
                · exact hi.mp hok o ho
                · exact ih.mp (hrest s1 e1) o ho
              · intro hall
                refine ⟨hi.mpr fun o ho => hall o (Or.inl ho), fun s1' e1' => ?_⟩
                rw [e1] at e1'
                cases e1'
                exact ih.mpr fun o ho => hall o (Or.inr ho)
          | fail => simp [h2] at hr
          | unk => simp [h2] at hr
      | fail => simp [h1] at hr
      | unk => simp [h1] at hr

/-- **The obligations of a stretch hold exactly when its run is in bounds**, for a run
    from a state the start of a successful symbolic run describes. -/
theorem symObl_sound (P : LprogM) (is : List LinstrRM) (ss : SSt)
    (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O Z : Bool) (s u : LstateMF)
    (hs : Holds V A C O Z ss s) (hr : ∃ ss' gs, symRun is ss = .ok ss' gs)
    (hu : runL P is s = some u) :
    (RunLOk P is s ↔ ∀ o ∈ symObl is ss, o.holds V A C O) := by
  rw [← x86Isa_runL] at hu
  exact symObl_sound_at (I := x86Isa) symStep_sound P is ss V A C O Z s u hs hr hu

/-! ## 2. The in-bounds condition of a run at a stretch -/

section Run

variable {fn : String} {B : List LinstrRM}

/-- A run of the instruction set `I` in bounds that starts with a stretch `xs` of
    non-terminators runs `xs` in bounds and then the rest in bounds. -/
theorem runIdxOk_runL_at {I : Isa} (hpl : StepPlain I) :
    ∀ (xs rest : List LinstrRM) (s u : LstateMF) (f : Nat), s.prog.lfn = fn →
      B.drop s.prog.base.reg.lpc = xs ++ rest → (∀ x ∈ xs, isTermR x.1 = false) →
      I.runL (singletonProgM fn B) xs s = some u →
      I.RunIdxOk (singletonProgM fn B) (xs.length + f) s →
      RunLOk (singletonProgM fn B) xs s I ∧ I.RunIdxOk (singletonProgM fn B) f u
  | [], _, s, u, f, _, _, _, h, hok => by
      simp only [Isa.runL, Option.some.injEq] at h
      subst h
      exact ⟨trivial, by simpa using hok⟩
  | x :: xs, rest, s, u, f, hfn, hB, hx, h, hok => by
      have hget : B[s.prog.base.reg.lpc]? = some x := by
        rw [← List.head?_drop, hB]; rfl
      simp only [Isa.runL] at h
      obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨h1, h2⟩ := hpl _ (hx x (by simp)) e1
      have hB1 : B.drop s1.prog.base.reg.lpc = xs ++ rest := by
        rw [h2, ← List.drop_drop, hB]; rfl
      rw [List.length_cons, show xs.length + 1 + f = (xs.length + f) + 1 by omega] at hok
      obtain ⟨hi, hnext⟩ := hok x (by rw [findInstrMem_single hfn, hget])
      obtain ⟨ih1, ih2⟩ := runIdxOk_runL_at hpl xs rest s1 u f (h1.trans hfn) hB1
        (fun y hy => hx y (by simp [hy])) e2 (hnext s1 e1)
      refine ⟨⟨hi, fun s1' e1' => ?_⟩, ih2⟩
      rw [e1] at e1'
      cases e1'
      exact ih1

/-- A run in bounds that starts with a stretch `xs` of non-terminators runs `xs` in bounds
    and then the rest in bounds. -/
theorem runIdxOk_runL (xs rest : List LinstrRM) (s u : LstateMF) (f : Nat)
    (hfn : s.prog.lfn = fn) (hB : B.drop s.prog.base.reg.lpc = xs ++ rest)
    (hx : ∀ x ∈ xs, isTermR x.1 = false) (h : runL (singletonProgM fn B) xs s = some u)
    (hok : RunIdxOk (singletonProgM fn B) (xs.length + f) s) :
    RunLOk (singletonProgM fn B) xs s ∧ RunIdxOk (singletonProgM fn B) f u := by
  rw [← x86Isa_runL] at h
  rw [← x86Isa_RunIdxOk] at hok ⊢
  exact runIdxOk_runL_at stepPlain_x86 xs rest s u f hfn hB hx h hok

/-- A stretch `xs` of non-terminators of the instruction set `I` run in bounds, followed by
    a run in bounds, is a run in bounds. -/
theorem runIdxOk_of_runL_at {I : Isa} (hpl : StepPlain I) :
    ∀ (xs rest : List LinstrRM) (s u : LstateMF) (f : Nat), s.prog.lfn = fn →
      B.drop s.prog.base.reg.lpc = xs ++ rest → (∀ x ∈ xs, isTermR x.1 = false) →
      I.runL (singletonProgM fn B) xs s = some u →
      RunLOk (singletonProgM fn B) xs s I → I.RunIdxOk (singletonProgM fn B) f u →
      I.RunIdxOk (singletonProgM fn B) (xs.length + f) s
  | [], _, s, u, f, _, _, _, h, _, hok => by
      simp only [Isa.runL, Option.some.injEq] at h
      subst h
      simpa using hok
  | x :: xs, rest, s, u, f, hfn, hB, hx, h, hl, hok => by
      have hget : B[s.prog.base.reg.lpc]? = some x := by
        rw [← List.head?_drop, hB]; rfl
      simp only [Isa.runL] at h
      obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨h1, h2⟩ := hpl _ (hx x (by simp)) e1
      have hB1 : B.drop s1.prog.base.reg.lpc = xs ++ rest := by
        rw [h2, ← List.drop_drop, hB]; rfl
      rw [List.length_cons, show xs.length + 1 + f = (xs.length + f) + 1 by omega]
      intro i hi
      rw [findInstrMem_single hfn, hget, Option.some.injEq] at hi
      subst hi
      refine ⟨hl.1, fun s1' e1' => ?_⟩
      rw [e1] at e1'
      cases e1'
      exact runIdxOk_of_runL_at hpl xs rest s1 u f (h1.trans hfn) hB1
        (fun y hy => hx y (by simp [hy])) e2 (hl.2 s1 e1) hok

/-- A stretch `xs` of non-terminators run in bounds, followed by a run in bounds, is a run in
    bounds. -/
theorem runIdxOk_of_runL (xs rest : List LinstrRM) (s u : LstateMF) (f : Nat)
    (hfn : s.prog.lfn = fn) (hB : B.drop s.prog.base.reg.lpc = xs ++ rest)
    (hx : ∀ x ∈ xs, isTermR x.1 = false) (h : runL (singletonProgM fn B) xs s = some u)
    (hl : RunLOk (singletonProgM fn B) xs s) (hok : RunIdxOk (singletonProgM fn B) f u) :
    RunIdxOk (singletonProgM fn B) (xs.length + f) s := by
  rw [← x86Isa_runL] at h
  rw [← x86Isa_RunIdxOk] at hok ⊢
  exact runIdxOk_of_runL_at stepPlain_x86 xs rest s u f hfn hB hx h hl hok

end Run

/-- A halted state of the instruction set `I` is in bounds for every fuel. -/
theorem runIdxOk_halt_at (I : Isa) {P : LprogM} {s : LstateMF}
    (h : findInstrMem P s.prog = none) : ∀ f, I.RunIdxOk P f s
  | 0 => trivial
  | _ + 1 => fun i hi => by rw [h] at hi; cases hi

/-- A halted state is in bounds for every fuel. -/
theorem runIdxOk_halt {P : LprogM} {s : LstateMF} (h : findInstrMem P s.prog = none)
    (f : Nat) : RunIdxOk P f s := by
  rw [← x86Isa_RunIdxOk]; exact runIdxOk_halt_at x86Isa h f

/-- One step of the instruction set `I` in bounds followed by a run in bounds is a run in
    bounds. -/
theorem runIdxOk_step_at {I : Isa} {P : LprogM} {s s1 : LstateMF} {i : LinstrRM} {f : Nat}
    (hfetch : findInstrMem P s.prog = some i) (hi : idxOkB i s = true)
    (he : I.step P i s = some s1) (hok : I.RunIdxOk P f s1) : I.RunIdxOk P (f + 1) s := by
  intro i' hi'
  rw [hfetch, Option.some.injEq] at hi'
  subst hi'
  refine ⟨hi, fun s1' e1' => ?_⟩
  rw [he] at e1'
  cases e1'
  exact hok

/-- One step in bounds followed by a run in bounds is a run in bounds. -/
theorem runIdxOk_step {P : LprogM} {s s1 : LstateMF} {i : LinstrRM} {f : Nat}
    (hfetch : findInstrMem P s.prog = some i) (hi : idxOkB i s = true)
    (he : evalInstrPMemF P i s = some s1) (hok : RunIdxOk P f s1) : RunIdxOk P (f + 1) s := by
  rw [← x86Isa_RunIdxOk] at hok ⊢
  exact runIdxOk_step_at (I := x86Isa) hfetch hi he hok

/-- The run in bounds after one step of a run in bounds of the instruction set `I`. -/
theorem runIdxOk_next_at {I : Isa} {P : LprogM} {s s1 : LstateMF} {i : LinstrRM} {f : Nat}
    (hfetch : findInstrMem P s.prog = some i) (he : I.step P i s = some s1)
    (hok : I.RunIdxOk P (f + 1) s) : I.RunIdxOk P f s1 :=
  (hok i hfetch).2 s1 he

/-- The run in bounds after one step of a run in bounds. -/
theorem runIdxOk_next {P : LprogM} {s s1 : LstateMF} {i : LinstrRM} {f : Nat}
    (hfetch : findInstrMem P s.prog = some i) (he : evalInstrPMemF P i s = some s1)
    (hok : RunIdxOk P (f + 1) s) : RunIdxOk P f s1 := by
  rw [← x86Isa_RunIdxOk] at hok ⊢
  exact runIdxOk_next_at (I := x86Isa) hfetch he hok

theorem symObl_entry_at {sym : LinstrRM → SSt → SOut}
    (hlab : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, sym i ss = .ok ss [])
    {B : List LinstrRM} {b : Block} {T : Term} {p : Nat} {ss : SSt}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symObl ((B.drop p).take (bstopOf T b - p)) ss sym = symObl (bodyAt B b T) ss sym := by
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · rfl
  · unfold bodyAt
    rw [take_cons B (by omega) hx, symObl_label_at hlab hl]

theorem symObl_entry {B : List LinstrRM} {b : Block} {T : Term} {p : Nat}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symObl ((B.drop p).take (bstopOf T b - p)) SSt.start = symObl (bodyAt B b T) SSt.start :=
  symObl_entry_at (fun h ss => symStep_label h ss) hp hle

/-- The symbolic run of a block body entered at `p` from the symbolic state `ss` is the
    symbolic run of the block body from `ss`. -/
theorem symRun_entryS_at {sym : LinstrRM → SSt → SOut}
    (hlab : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, sym i ss = .ok ss [])
    {B : List LinstrRM} {b : Block} {T : Term} {p : Nat} {ss : SSt}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symRun ((B.drop p).take (bstopOf T b - p)) ss sym = symRun (bodyAt B b T) ss sym := by
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · rfl
  · unfold bodyAt
    rw [take_cons B (by omega) hx, symRun_label_at hlab hl]

/-! ## 3. Must-constant facts at block entry -/

/-- A must-constant fact: the register `f.1` holds the immediate `f.2.2` at width `f.2.1`. -/
abbrev CFact : Type := String × Nat × Nat

/-- The fact `f` holds of the register values `V`. -/
def CFact.holds (V : String → Σ w, BitVec w) (f : CFact) : Prop :=
  V f.1 = ⟨f.2.1, BitVec.ofNat f.2.1 f.2.2⟩

/-- The facts `fs` hold at the state `s`. -/
def FactsAt (fs : List CFact) (s : LstateMF) : Prop :=
  ∀ f ∈ fs, f.holds s.prog.base.reg.lvm

/-- The symbolic state at the start of a block with the facts `fs`: a register with a fact
    is the immediate of its first fact, every other register and every array name its start
    value; the registers with a fact count as written. -/
def startC (fs : List CFact) : SSt :=
  { rf := fs.foldr (fun f rf => rf.set f.1 (.immW f.2.1 f.2.2)) .empty, arrs := SArr.cell,
    zf := .init, wr := fs.map Prod.fst, awr := [], cf := .cin false, of := .cin true }

theorem startC_nil : startC [] = SSt.start := rfl

theorem startC_regs (fs : List CFact) (r : String) :
    (startC fs).regs r =
      match fs.find? (fun f => f.1 == r) with
      | some f => .immW f.2.1 f.2.2
      | none => .reg r := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      change ((fs.foldr (fun (f : CFact) (rf : RegFile) => rf.set f.1 (.immW f.2.1 f.2.2))
        RegFile.empty).set f.1 (.immW f.2.1 f.2.2)).get r = _
      rw [RegFile.get_set, List.find?_cons]
      by_cases h : r = f.1
      · have h' : (f.1 == r) = true := beq_iff_eq.mpr h.symm
        rw [ite_eq_left h, h']
      · have h' : (f.1 == r) = false := beq_false_of_ne (Ne.symm h)
        rw [ite_eq_right h, h']
        exact ih

theorem startC_good (fs : List CFact) : (startC fs).Good := by
  refine ⟨fun r hr => ?_, fun _ _ => rfl⟩
  rw [startC_regs]
  cases h : fs.find? (fun f => f.1 == r) with
  | none => rfl
  | some f =>
      have he : f.1 = r := by simpa using List.find?_some h
      exact absurd (List.mem_map.mpr ⟨f, List.mem_of_find?_eq_some h, he⟩) hr

theorem startC_subst (σ : Nat → STerm) (fs : List CFact) :
    (startC fs).subst σ = startC fs := by
  refine SSt.ext (fun r => ?_) rfl rfl rfl rfl rfl rfl
  rw [SSt.subst_regs_apply, startC_regs]
  cases fs.find? (fun f => f.1 == r) <;> rfl

theorem startC_regs_ev {fs : List CFact} {V : String → Σ w, BitVec w}
    (h : ∀ f ∈ fs, f.holds V) (A : String → ArrCell) (C O : Bool) (q : String) :
    ((startC fs).regs q).ev V A C O = V q := by
  rw [startC_regs]
  cases hf : fs.find? (fun f => f.1 == q) with
  | none => rfl
  | some f =>
      have he : f.1 = q := by simpa using List.find?_some hf
      rw [← he, h f (List.mem_of_find?_eq_some hf)]
      rfl

/-- A state satisfying the facts `fs`, with the arrays `A`, is described by `startC fs`. -/
theorem holds_startC {fs : List CFact} {s : LstateMF} {A : String → ArrCell}
    (hf : FactsAt fs s) (hA : ∀ q, s.prog.base.larr q = A q) :
    Holds s.prog.base.reg.lvm A s.prog.base.cf s.prog.base.of s.zf (startC fs) s :=
  ⟨fun q => (startC_regs_ev hf _ _ _ q).symm, hA, rfl, by simp [startC, STerm.ev],
    by simp [startC, STerm.ev]⟩

/-- The facts `fs` hold at a state described by `ss` whose words of the registers of `fs`
    are their immediates. -/
theorem factsAt_of_holds {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {ss : SSt} {u : LstateMF} (hH : Holds V A C O Z ss u) {fs : List CFact}
    (h : ∀ f ∈ fs, ss.regs f.1 = .immW f.2.1 f.2.2) : FactsAt fs u := by
  intro f hf
  unfold CFact.holds
  rw [hH.1 f.1, h f hf]
  rfl

/-- The final symbolic state `ss` of a block with terminator `T` gives the facts `A j` of
    every successor `j`: the word of each of their registers is its immediate. -/
def factsExit (A : Nat → List CFact) (T : Term) (ss : SSt) : Bool :=
  T.succs.all fun j => (A j).all fun f => ss.regs f.1 == .immW f.2.1 f.2.2

/-- The run of block `k` (block `b` of `B`, terminator `T`) from its facts `A k` gives the
    facts of its successors, unless it fails or leaves the fragment. -/
def factsOk (A : Nat → List CFact) (k : Nat) (T : Term) (B : List LinstrRM) (b : Block)
    (sym : LinstrRM → SSt → SOut := symStep) : Bool :=
  match symRun (bodyAt B b T) (startC (A k)) sym with
  | .ok ss _ => factsExit A T ss
  | _ => true

/-- **The invariant check of the facts `A`** on the graph `G` of `B`: block `0` has no fact
    and every block passes `factsOk`. -/
def factCheck (A : Nat → List CFact) (B : List LinstrRM) (G : CFG)
    (sym : LinstrRM → SSt → SOut := symStep) : Bool :=
  (A 0).isEmpty &&
    (List.range G.blocks.size).all fun k => factsOk A k (G.blk k).term B (G.blk k) sym

theorem factsOk_spec {A : Nat → List CFact} {k : Nat} {T : Term} {B : List LinstrRM}
    {b : Block} {sym : LinstrRM → SSt → SOut} (h : factsOk A k T B b sym = true) {ss : SSt}
    {gs : List SG} (hs : symRun (bodyAt B b T) (startC (A k)) sym = .ok ss gs) :
    ∀ j ∈ T.succs, ∀ f ∈ A j, ss.regs f.1 = .immW f.2.1 f.2.2 := by
  unfold factsOk at h
  rw [hs] at h
  simpa only [factsExit, List.all_eq_true, beq_iff_eq] using h

theorem factCheck_nil (B : List LinstrRM) (G : CFG) (sym : LinstrRM → SSt → SOut) :
    factCheck (fun _ => []) B G sym = true := by
  simp only [factCheck, List.isEmpty_nil, Bool.true_and, List.all_eq_true]
  intro k _
  unfold factsOk
  split <;> simp [factsExit]

/-! ### The annotation -/

/-- The facts a final symbolic state gives: each written register whose word is an
    immediate. -/
def constExit (ss : SSt) : List CFact :=
  ss.wr.eraseDups.filterMap fun r =>
    match ss.regs r with
    | .immW w n => some (r, w, n)
    | _ => none

/-- The symbolic runs of the blocks of `G` from the facts of `ann`. -/
def exitsOf (B : List LinstrRM) (G : CFG) (sym : LinstrRM → SSt → SOut)
    (ann : Array (List CFact)) : Array SOut :=
  (Array.range G.blocks.size).map fun k =>
    symRun (bodyAt B (G.blk k) (G.blk k).term) (startC (ann.getD k [])) sym

/-- The predecessors of each block of `G`, in increasing order: entry `j` lists the blocks
    `k` with `j` among the successors of the terminator of `k`, once per such successor. -/
def predsOf (G : CFG) : Array (Array Nat) :=
  (List.range G.blocks.size).foldl (fun P k =>
    (G.blk k).term.succs.foldl (fun P j => P.modify j (·.push k)) P)
    (Array.replicate G.blocks.size #[])

/-- One widening round of the candidates: each block other than `0` adds the facts the runs
    of its predecessors `P` give. -/
def constGrow (B : List LinstrRM) (G : CFG) (sym : LinstrRM → SSt → SOut)
    (P : Array (Array Nat)) (ann : Array (List CFact)) : Array (List CFact) :=
  let E := exitsOf B G sym ann
  (Array.range G.blocks.size).map fun j =>
    if j = 0 then []
    else
      (ann.getD j [] ++ (P.getD j #[]).toList.flatMap fun k =>
        match (E[k]? : Option SOut) with
        | some (.ok ss _) => constExit ss
        | _ => []).eraseDups

/-- One restriction round: a fact of a block other than `0` is kept when the run of every
    predecessor in `P` from its facts gives it. -/
def constPass (B : List LinstrRM) (G : CFG) (sym : LinstrRM → SSt → SOut)
    (P : Array (Array Nat)) (ann : Array (List CFact)) : Array (List CFact) :=
  let E := exitsOf B G sym ann
  (Array.range G.blocks.size).map fun j =>
    if j = 0 then []
    else
      (ann.getD j []).filter fun f =>
        (P.getD j #[]).all fun k =>
          match (E[k]? : Option SOut) with
          | some (.ok ss _) => ss.regs f.1 == .immW f.2.1 f.2.2
          | _ => true

/-- The iteration of `f` from `a`, stopped at a fixed point or after `n` rounds. -/
def constFix (f : Array (List CFact) → Array (List CFact)) :
    Nat → Array (List CFact) → Array (List CFact)
  | 0, a => a
  | n + 1, a =>
      let a' := f a
      if a' == a then a else constFix f n a'

/-- **The table of must-constant facts** of the graph `G` of `B`, one entry per block: no
    entry on a graph of at most one block; otherwise the candidates of `G.blocks.size + 1`
    widening rounds from no fact, restricted by `constPass` to a fixed point, both over the
    predecessors `predsOf G`. The table is untrusted: `factCheck` checks the facts it
    gives. -/
def constAnnotArr (B : List LinstrRM) (G : CFG) (sym : LinstrRM → SSt → SOut := symStep) :
    Array (List CFact) :=
  if G.blocks.size ≤ 1 then #[]
  else
    let P := predsOf G
    let a0 := constFix (constGrow B G sym P) (G.blocks.size + 1)
      (Array.replicate G.blocks.size [])
    constFix (constPass B G sym P) ((a0.toList.map List.length).sum + 1) a0

/-- The facts of block `k` in the table `a`, none past its end. -/
def annotAt (a : Array (List CFact)) (k : Nat) : List CFact := a.getD k []

/-- **The annotation of must-constant facts** of the graph `G` of `B`: the facts of each block
    in the table `constAnnotArr`. The checks bind the table once and read it through
    `annotAt`, so that the fixed point is computed once per graph and not once per block
    read. -/
def constAnnot (B : List LinstrRM) (G : CFG) (sym : LinstrRM → SSt → SOut := symStep) :
    Nat → List CFact :=
  annotAt (constAnnotArr B G sym)

/-! ## 4. The checks -/

/-- `blockOk` with the symbolic run of the source block started at `st` and that of the
    rewritten block started at `st'`. -/
noncomputable def blockOkS (st st' : SSt) (outs : List String) (L : Nat → List String × Bool)
    (k : Nat) (T : Term) (B B' : List LinstrRM) (b b' : Block)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match T with
  | .ret => true
  | _ =>
      match symRun (bodyAt B b T) st sym with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match symRun (bodyAt B' b' T) st' sym with
          | .ok ss' gs' =>
              (normG gs').all (fun g =>
                  ((normG gs).contains g || SG.impG gs g) && okIn (L k) g.vars g.readsF) &&
                termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? dec &&
                exitAgree outs L (L k) T ss ss' gs gs'
          | _ => false

theorem blockOkS_spec {st st' : SSt} {outs : List String} {L : Nat → List String × Bool}
    {k : Nat} {T : Term} {B B' : List LinstrRM} {b b' : Block} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (h : blockOkS st st' outs L k T B B' b b' sym dec = true)
    (hT : T ≠ .ret) :
    symRun (bodyAt B b T) st sym = .fail ∨
      ∃ ss gs ss' gs', symRun (bodyAt B b T) st sym = .ok ss gs ∧
        symRun (bodyAt B' b' T) st' sym = .ok ss' gs' ∧
        (∀ g ∈ normG gs',
          (∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool),
            AllG V A C O gs → g.holds V A C O) ∧ (∀ v ∈ g.vars, v ∈ (L k).1) ∧
          (g.readsF = true → (L k).2 = true)) ∧
        termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? dec = true ∧
        exitAgree outs L (L k) T ss ss' gs gs' = true := by
  have h2 : (match symRun (bodyAt B b T) st sym with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match symRun (bodyAt B' b' T) st' sym with
          | .ok ss' gs' =>
              (normG gs').all (fun g =>
                  ((normG gs).contains g || SG.impG gs g) && okIn (L k) g.vars g.readsF) &&
                termAgree T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]? dec &&
                exitAgree outs L (L k) T ss ss' gs gs'
          | _ => false) = true := by
    cases T with
    | ret => exact absurd rfl hT
    | _ => exact h
  cases hs : symRun (bodyAt B b T) st sym with
  | fail => exact Or.inl rfl
  | unk => rw [hs] at h2; cases h2
  | ok ss gs =>
      rw [hs] at h2
      cases ht : symRun (bodyAt B' b' T) st' sym with
      | ok ss' gs' =>
          rw [ht] at h2
          simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
            List.contains_iff_mem] at h2
          obtain ⟨⟨hg, hta⟩, hex⟩ := h2
          refine Or.inr ⟨ss, gs, ss', gs', rfl, rfl, fun g hg' => ⟨fun V A C O hA => ?_,
            okIn_spec (hg g hg').2⟩, hta, hex⟩
          rcases (hg g hg').1 with hm | hi
          · exact allG_normG.mpr hA g hm
          · exact SG.impG_spec hi hA
      | fail => rw [ht] at h2; cases h2
      | unk => rw [ht] at h2; cases h2

/-- The shared runs of block `b` of `B` from `st` and block `b'` of `B'` from `st'`, with
    terminator `T`: the final table and the two descriptions over it. -/
def blockRunsS (st st' : SSt) (B B' : List LinstrRM) (b b' : Block) (T : Term)
    (sym : LinstrRM → SSt → SOut := symStep) : Tbl × SOut × SOut :=
  let p := tRun (bodyAt B b T) st Tbl.empty sym
  let q := tRun (bodyAt B' b' T) st' p.1 sym
  (q.1, p.2, q.2)

/-- **The shared check implies the check from the starts `st` and `st'`**, for every
    symbolic step and branch condition that commute with substitution and starts that
    every substitution fixes. -/
theorem blockOkR_specS {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hS : SymSubst sym dec) {st st' : SSt} (hst : ∀ σ, st.subst σ = st)
    (hst' : ∀ σ, st'.subst σ = st') {outs : List String} {L : Nat → List String × Bool}
    {k : Nat} {T : Term} {B B' : List LinstrRM} {b b' : Block}
    (h : blockOkR outs L k T (blockRunsS st st' B B' b b' T sym) B B' b b' dec = true) :
    blockOkS st st' outs L k T B B' b b' sym dec = true := by
  have hv : TValid (blockRunsS st st' B B' b b' T sym).1.ents :=
    tRun_valid_at sym _ _ _ (tRun_valid_at sym _ _ _ tValid_empty)
  obtain ⟨⟨σ, hσ⟩, -⟩ := hv
  have e1 : symRun (bodyAt B b T) st sym = (blockRunsS st st' B B' b b' T sym).2.1.subst σ := by
    have h1 := tRun_subst_at hS.step_subst hσ (bodyAt B b T) st Tbl.empty
      (tRun_ext_at sym _ _ _)
    rw [hst σ] at h1
    exact h1.symm
  have e2 : symRun (bodyAt B' b' T) st' sym =
      (blockRunsS st st' B B' b b' T sym).2.2.subst σ := by
    have h2 := tRun_subst_at hS.step_subst hσ (bodyAt B' b' T) st'
      (tRun (bodyAt B b T) st Tbl.empty sym).1 (TExt.refl _)
    rw [hst' σ] at h2
    exact h2.symm
  unfold blockOkR at h
  unfold blockOkS
  split
  · rfl
  · rename_i hT
    have h' : (match (blockRunsS st st' B B' b b' T sym).2.1 with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          match (blockRunsS st st' B B' b b' T sym).2.2 with
          | .ok ss' gs' =>
              guardsT (blockRunsS st st' B B' b b' T sym).1.ents (L k) gs gs' &&
                termAgreeT (blockRunsS st st' B B' b b' T sym).1.ents T (L k) ss ss'
                  B[b.stop - 1]? B'[b'.stop - 1]? dec &&
                exitAgreeT (blockRunsS st st' B B' b b' T sym).1.ents outs L (L k) T ss ss' gs gs'
          | _ => false) = true := by
      split at h
      · exact absurd rfl hT
      · exact h
    rw [e1, e2]
    revert h'
    generalize blockRunsS st st' B B' b b' T sym = R at hσ
    obtain ⟨Tb, o, o'⟩ := R
    intro h'
    cases o with
    | fail => rfl
    | unk => cases h'
    | ok ss gs =>
        cases o' with
        | ok ss' gs' =>
            simp only [Bool.and_eq_true] at h'
            obtain ⟨⟨hg, hta⟩, hex⟩ := h'
            simp only [SOut.subst, Bool.and_eq_true]
            exact ⟨⟨guardsT_spec hσ hg, termAgreeT_spec_at hS.dec_subst hσ hta⟩,
              exitAgreeT_spec hσ hex⟩
        | fail => cases h'
        | unk => cases h'

/-- The shared runs of the block pairs of `G` and `G'`: block `k` of the source from its
    facts `A k`, block `k` of the rewritten body from its facts `A' k`. -/
def runsOfC (A A' : Nat → List CFact) (B B' : List LinstrRM) (G G' : CFG)
    (sym : LinstrRM → SSt → SOut := symStep) : Array (Tbl × SOut × SOut) :=
  (Array.range G.blocks.size).map fun k =>
    blockRunsS (startC (A k)) (startC (A' k)) B B' (G.blk k) (G'.blk k) (G.blk k).term sym

/-- The facts the checks establish about the two bodies, their graphs, the live sets `L`,
    the facts `A` of the source graph and the facts `A'` of the rewritten graph: the bodies
    are non-empty, the graphs have the same number of blocks and the same terminators,
    every block pair passes `blockOkS` from the facts `A k` and `A' k`, and `A` and `A'`
    pass `factCheck` on their graphs. -/
structure CheckedC (outs : List String) (L : Nat → List String × Bool)
    (A A' : Nat → List CFact) (B B' : List LinstrRM) (G G' : CFG)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) :
    Prop where
  hG : cfgOf (B.map Prod.fst) = some G
  hG' : cfgOf (B'.map Prod.fst) = some G'
  ne : B.map Prod.fst ≠ []
  ne' : B'.map Prod.fst ≠ []
  size : G'.blocks.size = G.blocks.size
  blk : ∀ k < G.blocks.size, (G'.blk k).term = (G.blk k).term ∧
    blockOkS (startC (A k)) (startC (A' k)) outs L k (G.blk k).term B B' (G.blk k) (G'.blk k)
      sym dec = true
  facts : factCheck A B G sym = true
  facts' : factCheck A' B' G' sym = true

theorem factCheck_entry {A : Nat → List CFact} {B : List LinstrRM} {G : CFG}
    {sym : LinstrRM → SSt → SOut} (h : factCheck A B G sym = true) : A 0 = [] := by
  simp only [factCheck, Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.1

theorem factCheck_blk {A : Nat → List CFact} {B : List LinstrRM} {G : CFG}
    {sym : LinstrRM → SSt → SOut} (h : factCheck A B G sym = true) {k : Nat}
    (hk : k < G.blocks.size) : factsOk A k (G.blk k).term B (G.blk k) sym = true := by
  simp only [factCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.2 k hk

/-- The check over the shared runs from the facts `A` and `A'`, with `factCheck` on both
    graphs, gives `CheckedC`, for every symbolic step and branch condition that commute with
    substitution. -/
theorem checkedC_of_withR {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hS : SymSubst sym dec) {outs : List String} {L : Nat → List String × Bool}
    {A A' : Nat → List CFact} {B B' : List LinstrRM} {G G' : CFG}
    (hG : cfgOf (B.map Prod.fst) = some G) (hG' : cfgOf (B'.map Prod.fst) = some G')
    (h : ownedCheckWithR outs L B B' G G' (runsOfC A A' B B' G G' sym) dec = true)
    (hf : factCheck A B G sym = true) (hf' : factCheck A' B' G' sym = true) :
    CheckedC outs L A A' B B' G G' sym dec := by
  simp only [ownedCheckWithR, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hne, hne'⟩, hsz⟩, hall⟩ := h
  refine ⟨hG, hG', by simpa using hne, by simpa using hne', hsz.symm, fun k hk => ?_, hf, hf'⟩
  obtain ⟨ht, hb⟩ := hall k hk
  refine ⟨ht.symm, ?_⟩
  have hR : (runsOfC A A' B B' G G' sym)[k]? =
      some (blockRunsS (startC (A k)) (startC (A' k)) B B' (G.blk k) (G'.blk k)
        (G.blk k).term sym) := by
    simp [runsOfC, hk]
  rw [hR] at hb
  exact blockOkR_specS hS (fun σ => startC_subst σ _) (fun σ => startC_subst σ _) hb

/-- `ownedCheckWith` for the live sets `L` gives `CheckedC` with no fact. -/
theorem checkedC_of_with {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    (h : ownedCheckWith outs L B B' sym dec = true) :
    ∃ G G', CheckedC outs L (fun _ => []) (fun _ => []) B B' G G' sym dec := by
  unfold ownedCheckWith at h
  split at h
  · rename_i G G' hG hG'
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq,
      List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨hne, hne'⟩, hsz⟩, hblk⟩ := h
    exact ⟨G, G', hG, hG', by simpa using hne, by simpa using hne', hsz.symm,
      fun k hk => ⟨(hblk k hk).1.symm, (hblk k hk).2⟩, factCheck_nil B G sym,
      factCheck_nil B' G' sym⟩
  · cases h

/-- The index obligations of the rewritten block are obligations of the source block over
    registers and flags live at the block, unless no halting run passes through the block.
    The source block runs from its facts `A k`, the rewritten block from its facts `A' k`;
    both default to no fact. -/
def oblOk (L : Nat → List String × Bool) (k : Nat) (T : Term) (B B' : List LinstrRM)
    (b b' : Block) (sym : LinstrRM → SSt → SOut := symStep)
    (A A' : Nat → List CFact := fun _ => []) : Bool :=
  match T with
  | .ret => true
  | _ =>
      match symRun (bodyAt B b T) (startC (A k)) sym with
      | .ok _ _ =>
          (symObl (bodyAt B' b' T) (startC (A' k)) sym).all fun o =>
            (symObl (bodyAt B b T) (startC (A k)) sym).contains o &&
              okIn (L k) o.1.vars o.1.readsF
      | _ => true

/-- `oblOk` at every block pair of the two graphs, with the facts `A` and `A'`. -/
def oblCheckWith (L : Nat → List String × Bool) (B B' : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (A A' : Nat → List CFact := fun _ => []) :
    Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      (List.range G.blocks.size).all fun k =>
        oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A'
  | _, _ => false

theorem oblCheckWith_spec {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {sym : LinstrRM → SSt → SOut} {A A' : Nat → List CFact} {G G' : CFG}
    (hG : cfgOf (B.map Prod.fst) = some G) (hG' : cfgOf (B'.map Prod.fst) = some G')
    (h : oblCheckWith L B B' sym A A' = true) :
    ∀ k < G.blocks.size,
      oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true := by
  unfold oblCheckWith at h
  rw [hG, hG'] at h
  simpa only [List.all_eq_true, List.mem_range] using h

/-- **The check has an output to compare**: an observed name, or an array store of `B`
    (`writesArrB`), which `Obs` compares with the arrays. A check with neither compares nothing
    that a run of `B` computes. -/
def hasOutsB (outs : List String) (B : List LinstrRM) : Bool :=
  !outs.isEmpty || B.any (fun i => writesArrB i.1)

/-- The pieces of a list of instructions between its call shadows (`LprogIsa.shadowCall?`):
    the maximal runs of instructions that are no call shadow, in order. -/
def callFreePieces : List LinstrRM → List (List LinstrRM)
  | [] => [[]]
  | i :: is =>
      match callFreePieces is with
      | p :: ps => if (LprogIsa.shadowCall? i.1).isSome then [] :: p :: ps else (i :: p) :: ps
      | [] => [[i]]

/-- **Every block runs symbolically between its calls**: for each block of `B`, the symbolic
    run under `sym` of each piece of the block between its call shadows (`callFreePieces`) is not
    `.fail`. A block whose run fails is accepted by the block check without a comparison
    (`blockOkR`), since no halting run passes through it: an operation the flag machine does
    not step makes the acceptance compare nothing on the runs through that block. A call
    shadow is such an operation; the segments between the calls of a calling body are
    compared by the segment check `calleeSegB` of the region gate (`ownedCheckMCIn` on the
    cut programs), and every other instruction of the block must be stepped. -/
def blocksRunCB (B : List LinstrRM) (sym : LinstrRM → SSt → SOut := symStep) : Bool :=
  match cfgOf (B.map Prod.fst) with
  | some G => (List.range G.blocks.size).all fun k =>
      (callFreePieces (bodyAt B (G.blk k) (G.blk k).term)).all fun p =>
        match symRun p SSt.start sym with
        | .fail => false
        | _ => true
  | none => false

/-- **The checker on bounds-checked runs.** The must-constant facts are computed once on each
    of the two graphs as the table `constAnnotArr`, read through `annotAt`, and checked as
    its invariant (`factCheck`); each block pair runs once over a shared term table from the facts of its two blocks (`runsOfC`);
    the live sets are computed from these runs by `liveIter` and the runs checked by
    `ownedCheckWithR`, and so are the index obligations (`oblCheckWith`). The check has an
    output to compare (`hasOutsB`) and every block of `B` runs symbolically between its calls
    (`blocksRunCB`), so that an acceptance is not a comparison of nothing. The symbolic step
    `sym` and the symbolic branch condition `dec` default to the x86 ones, `symStep` and
    `symDec`. -/
def ownedCheckMC (outs : List String) (B B' : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let A := annotAt (constAnnotArr B G sym)
      let A' := annotAt (constAnnotArr B' G' sym)
      let R := runsOfC A A' B B' G G' sym
      let L := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false)) dec
      ownedCheckWithR outs (fun k => L.getD k ([], false)) B B' G G' R dec
        && oblCheckWith (fun k => L.getD k ([], false)) B B' sym A A'
        && factCheck A B G sym && factCheck A' B' G' sym
        && hasOutsB outs B && blocksRunCB B sym
  | _, _ => false

/-- A pair `ownedCheckMC` accepts under `sym` and `dec` satisfies `CheckedC` and the index
    obligations for some live sets and facts, when `sym` and `dec` commute with
    substitution. -/
theorem ownedCheckMC_checked_at {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hS : SymSubst sym dec) {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' sym dec = true) :
    ∃ L A A' G G', CheckedC outs L A A' B B' G G' sym dec ∧
      ∀ k < G.blocks.size,
        oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true := by
  unfold ownedCheckMC at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := h
          exact ⟨_, _, _, G, G', checkedC_of_withR hS hG hG' h1 h3 h4,
            oblCheckWith_spec hG hG' h2⟩

/-- **An accepted pair compares an output.** If `ownedCheckMC outs B B' sym dec` accepts, the
    check has an output to compare (an observed name or an array store of `B`) and every
    block of `B` runs symbolically between its calls. -/
theorem ownedCheckMC_hasOuts {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    {outs : List String} {B B' : List LinstrRM} (h : ownedCheckMC outs B B' sym dec = true) :
    hasOutsB outs B = true ∧ blocksRunCB B sym = true := by
  unfold ownedCheckMC at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true] at h
          exact ⟨h.1.2, h.2⟩

/-- **The checker with an entry set**: `ownedCheckMC`, and at the entry block the live
    names of the computed live sets are names of `ins` and the flags are dead. A pair it
    accepts is matched from two start states that agree on the names `ins`, the arrays and
    the word memory (`OwnedCheckFuel.ownedCheckMCIn_sound_rel`). -/
def ownedCheckMCIn (ins outs : List String) (B B' : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let A := annotAt (constAnnotArr B G sym)
      let A' := annotAt (constAnnotArr B' G' sym)
      let R := runsOfC A A' B B' G G' sym
      let L := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false)) dec
      ownedCheckWithR outs (fun k => L.getD k ([], false)) B B' G G' R dec
        && oblCheckWith (fun k => L.getD k ([], false)) B B' sym A A'
        && factCheck A B G sym && factCheck A' B' G' sym
        && (L.getD 0 ([], false)).1.all (fun r => ins.contains r)
        && !(L.getD 0 ([], false)).2
  | _, _ => false

/-- A pair `ownedCheckMCIn ins` accepts under `sym` and `dec` satisfies `CheckedC` and the
    index obligations for some live sets and facts, the live names of the entry block are
    names of `ins` and its flags are dead, when `sym` and `dec` commute with
    substitution. -/
theorem ownedCheckMCIn_checked_at {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hS : SymSubst sym dec) {ins outs : List String}
    {B B' : List LinstrRM} (h : ownedCheckMCIn ins outs B B' sym dec = true) :
    ∃ L A A' G G', CheckedC outs L A A' B B' G G' sym dec ∧
      (∀ k < G.blocks.size,
        oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true) ∧
      (∀ r ∈ (L 0).1, r ∈ ins) ∧ (L 0).2 = false := by
  unfold ownedCheckMCIn at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
            List.contains_iff_mem] at h
          obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
          exact ⟨_, _, _, G, G', checkedC_of_withR hS hG hG' h1 h3 h4,
            oblCheckWith_spec hG hG' h2, h5, h6⟩

theorem oblOk_spec {L : Nat → List String × Bool} {k : Nat} {T : Term} {B B' : List LinstrRM}
    {b b' : Block} {sym : LinstrRM → SSt → SOut} {A A' : Nat → List CFact}
    (h : oblOk L k T B B' b b' sym A A' = true) (hT : T ≠ .ret) {ss : SSt}
    {gs : List SG} (hs : symRun (bodyAt B b T) (startC (A k)) sym = .ok ss gs) :
    ∀ o ∈ symObl (bodyAt B' b' T) (startC (A' k)) sym,
      o ∈ symObl (bodyAt B b T) (startC (A k)) sym ∧
      (∀ v ∈ o.1.vars, v ∈ (L k).1) ∧ (o.1.readsF = true → (L k).2 = true) := by
  have h2 : (match symRun (bodyAt B b T) (startC (A k)) sym with
      | .ok _ _ =>
          (symObl (bodyAt B' b' T) (startC (A' k)) sym).all fun o =>
            (symObl (bodyAt B b T) (startC (A k)) sym).contains o &&
              okIn (L k) o.1.vars o.1.readsF
      | _ => true) = true := by
    cases T with
    | ret => exact absurd rfl hT
    | _ => exact h
  rw [hs] at h2
  simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h2
  intro o ho
  exact ⟨(h2 o ho).1, okIn_spec (h2 o ho).2⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCheckFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)

/-! ## 5. The simulation with the fuel bound -/

/-- The number of blocks of the control-flow graph of a body, `0` when the body has none. -/
def blockCount (B : List LinstrRM) : Nat :=
  match cfgOf (B.map Prod.fst) with
  | some G => G.blocks.size
  | none => 0

/-- The fuel of the rewritten body `B'` for a run of `B` at fuel `fuel`. -/
def checkFuel (B B' : List LinstrRM) (fuel : Nat) : Nat :=
  (B'.length + 1) * (fuel * (blockCount B + 1) + blockCount B + 1)

theorem blockCount_eq {B : List LinstrRM} {G : CFG} (hG : cfgOf (B.map Prod.fst) = some G) :
    blockCount B = G.blocks.size := by
  unfold blockCount
  rw [hG]

/-- One step of the simulation adds at most `L + 1` to the fuel of the rewritten run. -/
theorem step_bound {L N m f : Nat} (hm : m ≤ L) (hf : f ≤ (L + 1) * N) :
    m + (f + 1) ≤ (L + 1) * (N + 1) := by
  rw [Nat.mul_add_one]
  omega

/-- The simulation on runs in bounds of the instruction set `I` up to the measure `N`, with
    the fuel of the rewritten run bounded: a halting source run in bounds from a block entry,
    of measure below `N`, the source state satisfying the facts `A` of the block and the
    rewritten state the facts `A'`, is matched by a halting run in bounds of the rewritten
    body of at most `(B'.length + 1) * N` steps. -/
def SimAtCF (I : Isa) (outs : List String) (L : Nat → List String × Bool)
    (A A' : Nat → List CFact) (B B' : List LinstrRM) (G G' : CFG) (fn : String) (N : Nat) :
    Prop :=
  ∀ (fuel k : Nat) (s s' t : LstateMF),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    Pair B B' (G.blk k) (G'.blk k) s.prog.base.reg.lpc s'.prog.base.reg.lpc →
    Rel (L k) s s' → FactsAt (A k) s ∧ FactsAt (A' k) s' → s.prog.lfn = fn →
    I.lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    I.RunIdxOk (singletonProgM fn B) fuel s →
    ∃ f' t', f' ≤ (B'.length + 1) * N ∧
      I.lsemFuelMemF (singletonProgM fn B') f' s' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' s'

theorem fall_contCF {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    {outs : List String} {L : Nat → List String × Bool} {A A' : Nat → List CFact}
    {B B' : List LinstrRM} {G G' : CFG} {fn : String}
    (hc : CheckedC outs L A A' B B' G G' sym dec) {N k : Nat}
    (ih : SimAtCF I outs L A A' B B' G G' fn N) (hk : k < G.blocks.size) {nx : Option Nat}
    (hn : G.next k = nx) (hn' : G'.next k = nx) {w w' t : LstateMF} {f0 : Nat}
    (hw : w.prog.base.reg.lpc = (G.blk k).stop) (hw' : w'.prog.base.reg.lpc = (G'.blk k).stop)
    (hfn : w.prog.lfn = fn) (hfn' : w'.prog.lfn = fn)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) f0 w = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) f0 w)
    (hmeas : f0 * (G.blocks.size + 1) + (G.blocks.size - (k + 1)) < N)
    (hrel : ∀ j, nx = some j → Rel (L j) w w')
    (hfa : ∀ j, nx = some j → FactsAt (A j) w ∧ FactsAt (A' j) w')
    (hobs : nx = none → Obs outs w w') :
    ∃ f' t', f' ≤ (B'.length + 1) * N ∧
      I.lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' w' := by
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  cases nx with
  | none =>
      have e1 := (stop_next hc.hG hk).1 hn
      have e2 := (stop_next hc.hG' hk').1 hn'
      rw [halt_at_end_at I hfn (hw.trans e1)] at hrun
      cases hrun
      exact ⟨0, w', Nat.zero_le _, halt_at_end_at I hfn' (hw'.trans e2) 0, hobs rfl, trivial⟩
  | some j =>
      obtain ⟨hj, hjlt, e1⟩ := (stop_next hc.hG hk).2 j hn
      obtain ⟨-, -, e2⟩ := (stop_next hc.hG' hk').2 j hn'
      subst hj
      exact ih f0 (k + 1) w w' t hmeas hjlt (Or.inl ⟨hw.trans e1, hw'.trans e2⟩) (hrel _ rfl)
        (hfa _ rfl) hfn hrun hok

theorem jump_contCF {I : Isa} {outs : List String} {L : Nat → List String × Bool}
    {A A' : Nat → List CFact} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} {N tg : Nat} (ih : SimAtCF I outs L A A' B B' G G' fn N)
    (htg : tg < G.blocks.size) {l l' : LLabel}
    (hl : findLabel l (B.map Prod.fst) = some (G.blk tg).start)
    (hl' : findLabel l' (B'.map Prod.fst) = some (G'.blk tg).start) {w w' t : LstateMF}
    {f1 : Nat} (hw : w.prog.base.reg.lpc = (G.blk tg).start + 1)
    (hw' : w'.prog.base.reg.lpc = (G'.blk tg).start + 1) (hfn : w.prog.lfn = fn)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) f1 w = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) f1 w)
    (hmeas : f1 * (G.blocks.size + 1) + (G.blocks.size - tg) < N) (hrel : Rel (L tg) w w')
    (hfa : FactsAt (A tg) w ∧ FactsAt (A' tg) w') :
    ∃ f' t', f' ≤ (B'.length + 1) * N ∧
      I.lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' w' :=
  ih f1 tg w w' t hmeas htg (Or.inr ⟨hw, label_at hl, hw', label_at hl'⟩) hrel hfa hfn hrun hok

/-- **One step of the simulation with the fuel bound.** The rewritten run of the block costs
    at most `B'.length + 1` steps, by the terminator of the block (fall through, jump, branch
    taken, branch not taken). -/
theorem sim_stepCF {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool} {A A' : Nat → List CFact}
    {B B' : List LinstrRM} {G G' : CFG} {fn : String}
    (hc : CheckedC outs L A A' B B' G G' sym dec)
    (hob : ∀ k < G.blocks.size,
      oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true)
    {N : Nat} (ih : SimAtCF I outs L A A' B B' G G' fn N) :
    SimAtCF I outs L A A' B B' G G' fn (N + 1) := by
  intro fuel k s s' t hN hk hpair hrel ⟨hfa, hfa'⟩ hfn hrun hokS
  obtain ⟨hTk, hok⟩ := hc.blk k hk
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  have F := blockFacts hc.hG hk
  have F' := blockFacts hc.hG' hk'
  obtain ⟨hE, hE'⟩ := hpair.entry
  obtain ⟨hs1, hle⟩ := entry_le hc.hG hk hE
  obtain ⟨hs1', hle'⟩ := entry_le hc.hG' hk' hE'
  have hfn' : s'.prog.lfn = fn := hrel.1.trans hfn
  -- the source runs the block body
  have hplain := body_plain hc.hG hk hs1
  obtain ⟨u, f, hf, hu, hru⟩ :=
    fuel_runL_at hL.plain _ _ s t fuel hfn (drop_split B hle) hplain hrun
  have hokS' := hf ▸ hokS
  obtain ⟨hlS, hokU⟩ :=
    runIdxOk_runL_at hL.plain _ _ s u f hfn (drop_split B hle) hplain hu hokS'
  obtain ⟨hul, hup⟩ := runL_frame_at hL.plain _ s u hplain hu
  have hbstop : bstopOf (G.blk k).term (G.blk k) ≤ B.length := by
    unfold bstopOf; split <;> have := F.le <;> simp at this <;> omega
  have hbstop' : bstopOf (G'.blk k).term (G'.blk k) ≤ B'.length := by
    unfold bstopOf; split <;> have := F'.le <;> simp at this <;> omega
  simp only [List.length_take, List.length_drop] at hup hf
  have hupc : u.prog.base.reg.lpc = bstopOf (G.blk k).term (G.blk k) := by
    rw [hup]; omega
  have hul' : u.prog.lfn = fn := hul.trans hfn
  -- the last instruction of the source block
  have hlt : (G.blk k).stop - 1 < B.length := by have := F.le; have := F.lt; simp at *; omega
  obtain ⟨z, hz⟩ : ∃ z, B[(G.blk k).stop - 1]? = some z :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hterm := F.term
  rw [List.getElem?_map, hz, Option.map_some] at hterm
  have hlt' : (G'.blk k).stop - 1 < B'.length := by
    have := F'.le; have := F'.lt; simp at *; omega
  obtain ⟨z', hz'⟩ : ∃ z', B'[(G'.blk k).stop - 1]? = some z' :=
    ⟨_, List.getElem?_eq_getElem hlt'⟩
  have hterm' := F'.term
  rw [List.getElem?_map, hz', Option.map_some, hTk] at hterm'
  -- a block ending in `Lret` is never left by a halting run
  by_cases hret : (G.blk k).term = .ret
  · rcases termOk_spec hterm with ⟨_, hT, _⟩ | ⟨_, _, _, hT, _⟩ | ⟨_, _, _, _, hT, _⟩ | ⟨_, hzr⟩
    all_goals try (rw [hret] at hT; cases hT)
    have hupc2 : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by
      rw [hupc]; simp [bstopOf, hret]
    obtain ⟨_, _, _, he, _⟩ :=
      run_inv_at hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [hL.ret] at he
    cases he
  -- the symbolic runs of the two block bodies
  have hD := symRun_sound_at hL.step_sound (singletonProgM fn B)
    ((B.drop s.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) (startC (A k)) _ _ _ _ _ s
    (holds_startC hfa fun _ => rfl)
  rw [symRun_entryS_at hL.label hE hle] at hD
  rcases blockOkS_spec hok hret with hfail | ⟨ss, gs, ss', gs', hS, hS', hgs, hta, hex⟩
  · rw [hfail] at hD
    simp only [SOut.DescN] at hD
    rw [hD] at hu
    cases hu
  rw [hS] at hD
  obtain ⟨hAll, hH, hFr⟩ := hD.1 u hu
  have hV : ∀ r ∈ (L k).1, s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r := hrel.2.2.2.1
  have hH0' : Holds s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of s'.zf
      (startC (A' k)) s' :=
    holds_startC hfa' fun q => by rw [hrel.2.1]
  rw [hTk] at hle'
  have hD' := symRun_sound_at hL.step_sound (singletonProgM fn B')
    ((B'.drop s'.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) (startC (A' k))
    _ _ _ _ _ s' hH0'
  rw [symRun_entryS_at hL.label hE' hle', hS'] at hD'
  have hAll' : AllG s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of gs' :=
    allG_normG.mp fun g hg =>
      (SG.holds_congr _ g (fun r hr => (hV r ((hgs g hg).2.1 r hr)).symm)
        (fun e => by
          obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 ((hgs g hg).2.2 e)
          exact ⟨hc.symm, ho.symm⟩)).mp
      ((hgs g hg).1 _ _ _ _ hAll)
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (hD'.2 hAll')
  obtain ⟨-, hH', hFr'⟩ := hD'.1 u' hu'
  have hplain' := body_plain hc.hG' hk' hs1'
  rw [hTk] at hplain' hbstop'
  -- the index obligations: the source block is in bounds, so the rewritten block is
  have hOS := (symObl_sound_at hL.step_sound (singletonProgM fn B) _ (startC (A k)) _ _ _ _ _ s
    u (holds_startC hfa fun _ => rfl)
    ⟨ss, gs, by rw [symRun_entryS_at hL.label hE hle]; exact hS⟩ hu).mp hlS
  rw [symObl_entry_at hL.label hE hle] at hOS
  have hO := oblOk_spec (hob k hk) hret hS
  have hlI : RunLOk (singletonProgM fn B') ((B'.drop s'.prog.base.reg.lpc).take
      (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) s' I := by
    refine (symObl_sound_at hL.step_sound (singletonProgM fn B') _
      (startC (A' k)) _ _ _ _ _ s' u'
      hH0' ⟨ss', gs', by rw [symRun_entryS_at hL.label hE' hle']; exact hS'⟩ hu').mpr
      fun o ho => ?_
    rw [symObl_entry_at hL.label hE' hle'] at ho
    obtain ⟨hoS, hvars, hfl⟩ := hO o ho
    have hev := STerm.ev_congr s.prog.base.larr o.1
      (V := s'.prog.base.reg.lvm) (V' := s.prog.base.reg.lvm)
      (C := s'.prog.base.cf) (O := s'.prog.base.of)
      (C' := s.prog.base.cf) (O' := s.prog.base.of)
      (fun r hr => hV r (hvars r hr))
      (fun e => by
        obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 (hfl e)
        exact ⟨hc, ho⟩)
    have h1 := hOS o hoS
    unfold SObl.holds at h1 ⊢
    rw [hev]
    exact h1
  have hrun' := runL_fuel_at hL.plain _ _ s' u' hfn' (drop_split B' hle') hplain' hu'
  have hokJ : ∀ f0, I.RunIdxOk (singletonProgM fn B') f0 u' →
      I.RunIdxOk (singletonProgM fn B') (((B'.drop s'.prog.base.reg.lpc).take
        (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)).length + f0) s' :=
    fun f0 h0 =>
      runIdxOk_of_runL_at hL.plain _ _ s' u' f0 hfn' (drop_split B' hle') hplain' hu' hlI h0
  simp only [List.length_take, List.length_drop] at hrun' hokJ
  have hupc' : u'.prog.base.reg.lpc = bstopOf (G.blk k).term (G'.blk k) := by
    rw [hFr'.2.1]; simp only [List.length_take, List.length_drop]; omega
  have hul'' : u'.prog.lfn = fn := hFr'.1.trans hfn'
  obtain ⟨hsucc, hhalt⟩ := exit_rel hH hH' hV (fun hz => hrel.2.2.2.2 hz)
    (symRun_good_at hL.good _ (startC_good _) hS) (symRun_good_at hL.good _ (startC_good _) hS')
    (by rw [hul'', hul']) (by rw [hFr'.2.2, hrel.2.2.1, hFr.2.2]) hAll
    (allG_normG.mp fun g hg => (hgs g hg).1 _ _ _ _ hAll) hex
  have hfk' := factCheck_blk hc.facts' hk'
  rw [hTk] at hfk'
  have hfs : ∀ j ∈ (G.blk k).term.succs, FactsAt (A j) u ∧ FactsAt (A' j) u' := fun j hj =>
    ⟨factsAt_of_holds hH (factsOk_spec (factCheck_blk hc.facts hk) hS j hj),
      factsAt_of_holds hH' (factsOk_spec hfk' hS' j hj)⟩
  have hfle : f ≤ fuel := by omega
  obtain ⟨m', hm', hmok, hmle⟩ : ∃ m',
      (∀ f0, I.lsemFuelMemF (singletonProgM fn B') (m' + f0) s' =
        I.lsemFuelMemF (singletonProgM fn B') f0 u') ∧
      (∀ f0, I.RunIdxOk (singletonProgM fn B') f0 u' →
        I.RunIdxOk (singletonProgM fn B') (m' + f0) s') ∧ m' ≤ B'.length :=
    ⟨_, hrun', hokJ, by omega⟩
  clear hrun' hokJ
  obtain ⟨zi, zt⟩ := z
  obtain ⟨zi', zt'⟩ := z'
  rw [hz, hz'] at hta
  simp only at hterm hterm'
  rcases termOk_spec hterm with ⟨nx, hT, _, hnx⟩ | ⟨tg, x, l, hT, hzi, htg, hl⟩ |
      ⟨tg, nx, c, l, hT, hzi, htg, hl, hnx⟩ | ⟨hT, _⟩
  · -- fall through
    obtain ⟨nx', hT', _, hnx'⟩ | ⟨_, _, _, hT', _⟩ | ⟨_, _, _, _, hT', _⟩ | ⟨hT', _⟩ :=
      termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    have hw : u.prog.base.reg.lpc = (G.blk k).stop := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop := by rw [hupc', hT]; rfl
    obtain ⟨f'', t', hfb, hr, hobs, hrok⟩ := fall_contCF hc ih hk hnx.symm hnx'.symm hw hw' hul'
      hul'' hru hokU (measure_le hN hfle hk)
      (fun j hj => hsucc j (by simp [hT, Term.succs, hj]))
      (fun j hj => hfs j (by simp [hT, Term.succs, hj]))
      (fun hn => hhalt (by simp [hT, hn, Term.halts]))
    exact ⟨m' + f'', t',
      Nat.le_trans (Nat.add_le_add_left (Nat.le_succ f'') m') (step_bound hmle hfb),
      by rw [hm']; exact hr, hobs, hmok _ hrok⟩
  · -- jump
    obtain ⟨_, hT', _⟩ | ⟨tg', x', l', hT', hzi', htg', hl'⟩ | ⟨_, _, _, _, hT', _⟩ |
        ⟨hT', _⟩ := termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    subst hzi hzi'
    have hxx : x = x' := by simpa [termAgree, hT] using hta
    subst hxx
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop - 1 := by rw [hupc', hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lgoto (x, l), zt) := by
      rw [findInstrMem_single hul', hw, hz]
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv_at hru hfetch
    have hok1 := runIdxOk_next_at hfetch he (hf1 ▸ hokU)
    rw [I.step_goto] at he
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [ite_eq_left hx, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : I.step (singletonProgM fn B') (.Lgoto (x, l'), zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [I.step_goto, ite_eq_left (by simpa [singletonProgM, hul'', hul'] using hx),
          evalJumpMem_single hl']
        rfl
      have hfetch' : findInstrMem (singletonProgM fn B') u'.prog =
          some (.Lgoto (x, l'), zt') := by
        rw [findInstrMem_single hul'', hw', hz']
      obtain ⟨f'', t', hfb, hr, hobs, hrok⟩ := jump_contCF
        (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1 hok1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
        (hfs tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', step_bound hmle hfb, ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_goto _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
    · rw [ite_eq_right hx] at he
      cases he
  · -- branch
    obtain ⟨_, hT', _⟩ | ⟨_, _, _, hT', _⟩ | ⟨tg', nx', c', l', hT', hzi', htg', hl', hnx'⟩ |
        ⟨hT', _⟩ := termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    subst hzi hzi'
    simp only [termAgree, hT, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at hta
    obtain ⟨⟨hdeq, hdv⟩, hdz⟩ := hta
    have hdec : I.condEval u' c' = I.condEval u c := by
      rw [hL.dec_sound hH' c', hL.dec_sound hH c, ← hdeq]
      exact SDec.ev_congr _ _ (fun r hr => hV r (vIn_spec hdv r hr))
        (fun hz => hrel.2.2.2.2 (by
          rcases hdz with h | h
          · rw [hz] at h; cases h
          · exact h))
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop - 1 := by rw [hupc', hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lcond c l, zt) := by
      rw [findInstrMem_single hul', hw, hz]
    have hfetch' : findInstrMem (singletonProgM fn B') u'.prog = some (.Lcond c' l', zt') := by
      rw [findInstrMem_single hul'', hw', hz']
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv_at hru hfetch
    have hok1 := runIdxOk_next_at hfetch he (hf1 ▸ hokU)
    rw [I.step_cond] at he
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    have hstop' : 0 < (G'.blk k).stop := by have := F'.lt; omega
    by_cases hd : I.condEval u c = true
    · rw [ite_eq_left hd, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : I.step (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [I.step_cond, ite_eq_left (hdec.trans hd), evalJumpMem_single hl']
        rfl
      obtain ⟨f'', t', hfb, hr, hobs, hrok⟩ := jump_contCF
        (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1 hok1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
        (hfs tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', step_bound hmle hfb, ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_cond _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
    · rw [ite_eq_right hd] at he
      simp only [Option.some.injEq] at he
      have he' : I.step (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with base := u'.prog.base.nextPc } } := by
        rw [I.step_cond, ite_eq_right (by rw [hdec]; exact hd)]
      obtain ⟨f'', t', hfb, hr, hobs, hrok⟩ := fall_contCF (w := u1)
        (w' := { u' with prog := { u'.prog with base := u'.prog.base.nextPc } })
        hc ih hk hnx.symm hnx'.symm
        (by rw [← he]; show u.prog.base.reg.lpc + 1 = _; omega)
        (by show u'.prog.base.reg.lpc + 1 = _; omega)
        (by rw [← he]; exact hul') hul'' hr1 hok1
        (measure_le hN (show f1 ≤ fuel by omega) hk)
        (fun j hj => by rw [← he]; exact hsucc j (by simp [hT, Term.succs, hj]))
        (fun j hj => by rw [← he]; exact hfs j (by simp [hT, Term.succs, hj]))
        (fun hn => by rw [← he]; exact hhalt (by simp [hT, hn, Term.halts]))
      refine ⟨m' + (f'' + 1), t', step_bound hmle hfb, ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_cond _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
  · exact absurd hT hret

theorem simAtCF_all {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec) {outs : List String} {L : Nat → List String × Bool}
    {A A' : Nat → List CFact} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : CheckedC outs L A A' B B' G G' sym dec)
    (hob : ∀ k < G.blocks.size,
      oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true) :
    ∀ N, SimAtCF I outs L A A' B B' G G' fn N
  | 0 => fun _ _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => sim_stepCF hL hc hob (simAtCF_all hL hc hob N)

/-- **Soundness for given live sets and facts, with the fuel bound.** If the symbolic step
    `sym` and branch condition `dec` satisfy `SymLaws I sym dec`, the two bodies satisfy
    `CheckedC` for the live sets `L` and the facts `A` and `A'`, and every block pair meets
    its index obligations, every halting run of `I` on `B` from pc `0` whose accesses are in
    bounds is matched by a halting run on `B'` from the same state, of fuel at most
    `checkFuel B B' fuel`, whose accesses are in bounds, the end states agreeing on `outs`,
    the arrays and the word memory. -/
theorem checkedC_sound_at_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool} {A A' : Nat → List CFact}
    {B B' : List LinstrRM} {G G' : CFG} (hc : CheckedC outs L A A' B B' G G' sym dec)
    (hob : ∀ k < G.blocks.size,
      oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', fuel' ≤ checkFuel B B' fuel ∧
      I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s := by
  obtain ⟨h0, hs0⟩ := cfgOf_start_zero hc.hG hc.ne
  obtain ⟨-, hs0'⟩ := cfgOf_start_zero hc.hG' hc.ne'
  have hsim := simAtCF_all hL hc hob
    (fuel * (G.blocks.size + 1) + (G.blocks.size - 0) + 1) fuel 0 s s t
    (Nat.lt_succ_self _) h0
    (Or.inl ⟨hpc.trans hs0.symm, hpc.trans hs0'.symm⟩)
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
    ⟨(by rw [factCheck_entry hc.facts]; intro f hf; cases hf),
      (by rw [factCheck_entry hc.facts']; intro f hf; cases hf)⟩ hfn hrun hok
  unfold checkFuel
  rw [blockCount_eq hc.hG]
  rw [Nat.sub_zero] at hsim
  exact hsim

/-- **Soundness for given live sets and facts from related start states, with the fuel
    bound.** Under the hypotheses of `checkedC_sound_at_fuel`, every halting run of `I` on
    `B` from a state `s` at pc `0` whose accesses are in bounds is matched by a halting run on
    `B'`, of fuel at most `checkFuel B B' fuel`, from every state `s'` at pc `0` related to
    `s` by `Rel (L 0)`, whose accesses are in bounds, the end states agreeing on `outs`, the
    arrays and the word memory. -/
theorem checkedC_sound_rel_at_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool} {A A' : Nat → List CFact}
    {B B' : List LinstrRM} {G G' : CFG} (hc : CheckedC outs L A A' B B' G G' sym dec)
    (hob : ∀ k < G.blocks.size,
      oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true) (fn : String)
    (s s' t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hpc' : s'.prog.base.reg.lpc = 0) (hrel : Rel (L 0) s s') (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', fuel' ≤ checkFuel B B' fuel ∧
      I.lsemFuelMemF (singletonProgM fn B') fuel' s' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s' := by
  obtain ⟨h0, hs0⟩ := cfgOf_start_zero hc.hG hc.ne
  obtain ⟨-, hs0'⟩ := cfgOf_start_zero hc.hG' hc.ne'
  have hsim := simAtCF_all hL hc hob
    (fuel * (G.blocks.size + 1) + (G.blocks.size - 0) + 1) fuel 0 s s' t
    (Nat.lt_succ_self _) h0
    (Or.inl ⟨hpc.trans hs0.symm, hpc'.trans hs0'.symm⟩) hrel
    ⟨(by rw [factCheck_entry hc.facts]; intro f hf; cases hf),
      (by rw [factCheck_entry hc.facts']; intro f hf; cases hf)⟩ hfn hrun hok
  unfold checkFuel
  rw [blockCount_eq hc.hG]
  rw [Nat.sub_zero] at hsim
  exact hsim

/-- **Soundness of the checker with an entry set on runs in bounds, with the fuel bound.**
    If the symbolic step `sym` and branch condition `dec` satisfy `SymLaws I sym dec` and
    `SymSubst sym dec`, and `ownedCheckMCIn ins outs B B' sym dec` accepts, every halting
    run of `I` on `B` from a state `s` at pc `0` whose accesses are in bounds is matched by a
    halting run on `B'`, of fuel at most `checkFuel B B' fuel`, from every state `s'` at pc
    `0` that agrees with `s` on the function, the names `ins`, the arrays and the word
    memory, whose accesses are in bounds, the end states agreeing on `outs`, the arrays and
    the word memory. -/
theorem ownedCheckMCIn_idx_sound_rel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {ins outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMCIn ins outs B B' sym dec = true) (fn : String) (s s' t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (hpc' : s'.prog.base.reg.lpc = 0)
    (hrel : Rel (ins, false) s s') (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', fuel' ≤ checkFuel B B' fuel ∧
      I.lsemFuelMemF (singletonProgM fn B') fuel' s' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s' := by
  obtain ⟨L, A, A', G, G', hc, hob, hin, hfl⟩ := ownedCheckMCIn_checked_at hS h
  obtain ⟨h1, h2, h3, h4, -⟩ := hrel
  exact checkedC_sound_rel_at_fuel hL hc hob fn s s' t hfn hpc hpc'
    ⟨h1, h2, h3, fun r hr => h4 r (hin r hr), fun hf => absurd (hfl ▸ hf) (by simp)⟩
    fuel hrun hok

/-- **Soundness for given live sets, with the fuel bound.** If the symbolic step `sym` and
    branch condition `dec` satisfy `SymLaws I sym dec`, and
    `ownedCheckWith outs L B B' sym dec` and `oblCheckWith L B B' sym` accept, every halting
    run of `I` on `B` from pc `0` whose accesses are in bounds is matched by a halting run on
    `B'` from the same state, of fuel at most `checkFuel B B' fuel`, whose accesses are in
    bounds, the end states agreeing on `outs`, the arrays and the word memory. -/
theorem ownedCheckWithC_sound_at_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' sym dec = true)
    (hob : oblCheckWith L B B' sym = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', fuel' ≤ checkFuel B B' fuel ∧
      I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s := by
  obtain ⟨G, G', hc⟩ := checkedC_of_with h
  exact checkedC_sound_at_fuel hL hc (oblCheckWith_spec hc.hG hc.hG' hob) fn s t hfn hpc fuel
    hrun hok

/-- **Soundness of the checker on runs in bounds, with the fuel bound.** If the symbolic step
    `sym` and branch condition `dec` satisfy `SymLaws I sym dec` and `SymSubst sym dec`, and
    `ownedCheckMC outs B B' sym dec` accepts, every halting run of `I` on `B` from pc `0`
    whose accesses are in bounds is matched by a halting run on `B'` from the same state, of
    fuel at most `checkFuel B B' fuel`, whose accesses are in bounds, the end states
    agreeing on `outs`, the arrays and the word memory. -/
theorem ownedCheckMC_idx_sound_at_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM} (h : ownedCheckMC outs B B' sym dec = true)
    (fn : String) (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (fuel : Nat) (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', fuel' ≤ checkFuel B B' fuel ∧
      I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s := by
  obtain ⟨L, A, A', G, G', hc, hob⟩ := ownedCheckMC_checked_at hS h
  exact checkedC_sound_at_fuel hL hc hob fn s t hfn hpc fuel hrun hok

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCheckFuel

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
  (x86Isa x86Isa_lsemFuelMemF x86Isa_runL x86Isa_lsemFuelMemFk x86Isa_RunIdxOk)

/-! ## 6. Soundness -/

/-- **Soundness on runs in bounds for given live sets, over an instruction set.** If the
    symbolic step `sym` and branch condition `dec` satisfy `SymLaws I sym dec`, and
    `ownedCheckWith outs L B B' sym dec` and `oblCheckWith L B B' sym` accept, every halting
    run of `I` on `B` from pc `0` whose accesses are in bounds is matched by a halting run on
    `B'` from the same state whose accesses are in bounds, the end states agreeing on `outs`,
    the arrays and the word memory. -/
theorem ownedCheckWithC_sound_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' sym dec = true)
    (hob : oblCheckWith L B B' sym = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s :=
  (OwnedCheckFuel.ownedCheckWithC_sound_at_fuel hL h hob fn s t hfn hpc fuel hrun hok).elim
    fun f' ht => ht.elim fun t' hrest => ⟨f', t', hrest.2⟩

/-- **Soundness on runs in bounds for given live sets.** If `ownedCheckWith outs L B B'` and
    `oblCheckWith L B B'` accept, every halting run of `lsemFuelMemF` on `B` from pc `0`
    whose accesses are in bounds is matched by a halting run on `B'` from the same state
    whose accesses are in bounds, the end states agreeing on `outs`, the arrays and the word
    memory. -/
theorem ownedCheckWithC_sound {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' = true)
    (hob : oblCheckWith L B B' = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' ∧
      RunIdxOk (singletonProgM fn B') fuel' s := by
  rw [← x86Isa_lsemFuelMemF] at hrun
  rw [← x86Isa_RunIdxOk] at hok
  simpa only [x86Isa_lsemFuelMemF, x86Isa_RunIdxOk] using
    ownedCheckWithC_sound_at symLaws_x86 h hob fn s t hfn hpc fuel hrun hok

/-- **Soundness of the checker on bounds-checked runs, over an instruction set.** If the
    symbolic step `sym` and branch condition `dec` satisfy `SymLaws I sym dec` and
    `SymSubst sym dec`, and `ownedCheckMC outs B B' sym dec` accepts, every halting checked
    run (`I.lsemFuelMemFk true`) of the singleton program over `B` from a state at pc `0` of
    that function is matched by a halting checked run of the singleton program over `B'` from
    the same state, the end states agreeing on the registers `outs`, on the arrays and on the
    word memory. -/
theorem ownedCheckMC_sound_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' sym dec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  obtain ⟨f', t', -, hr, hobs, hok⟩ := OwnedCheckFuel.ownedCheckMC_idx_sound_at_fuel hL hS h
    fn s t hfn hpc fuel (I.lsemFuelMemF_of_checked _ fuel s t hrun)
    (I.runIdxOk_of_checked _ fuel s t hrun)
  exact ⟨f', t', I.lsemFuelMemFk_of_runIdxOk true _ f' s t' hr hok, hobs⟩

/-- **Soundness of the checker with an entry set on bounds-checked runs, over an
    instruction set.** If the symbolic step `sym` and branch condition `dec` satisfy
    `SymLaws I sym dec` and `SymSubst sym dec`, and `ownedCheckMCIn ins outs B B' sym dec`
    accepts, every halting checked run of the singleton program over `B` from a state `s` at
    pc `0` of that function is matched by a halting checked run of the singleton program
    over `B'` from every state `s'` at pc `0` that agrees with `s` on the function, the
    names `ins`, the arrays and the word memory, the end states agreeing on the registers
    `outs`, on the arrays and on the word memory. -/
theorem ownedCheckMCIn_sound_rel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {ins outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMCIn ins outs B B' sym dec = true) (fn : String) (s s' t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (hpc' : s'.prog.base.reg.lpc = 0)
    (hrel : Rel (ins, false) s s') (fuel : Nat)
    (hrun : I.lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemFk true (singletonProgM fn B') fuel' s' = some t' ∧
      Obs outs t t' := by
  obtain ⟨f', t', -, hr, hobs, hok⟩ := OwnedCheckFuel.ownedCheckMCIn_idx_sound_rel hL hS h
    fn s s' t hfn hpc hpc' hrel fuel (I.lsemFuelMemF_of_checked _ fuel s t hrun)
    (I.runIdxOk_of_checked _ fuel s t hrun)
  exact ⟨f', t', I.lsemFuelMemFk_of_runIdxOk true _ f' s' t' hr hok, hobs⟩

/-- **Soundness of the checker on bounds-checked runs.** If `ownedCheckMC outs B B'`
    accepts, every halting checked run (`lsemFuelMemFk true`) of the singleton program over
    `B` from a state at pc `0` of that function is matched by a halting checked run of the
    singleton program over `B'` from the same state, the end states agreeing on the
    registers `outs`, on the arrays and on the word memory. -/
theorem ownedCheckMC_sound {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  rw [← x86Isa_lsemFuelMemFk] at hrun
  simpa only [x86Isa_lsemFuelMemFk] using
    ownedCheckMC_sound_at symLaws_x86 symSubst_x86 h fn s t hfn hpc fuel hrun

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
