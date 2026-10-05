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

The checks take the symbolic step and the symbolic branch condition as trailing arguments
that default to the x86 ones, as in `OwnedLprogTV`. The theorems with the suffix `_at` are
stated for an instruction set `I : LprogIsa.Isa` whose step the symbolic step describes
(`OwnedLprogTV.SymLaws`); the theorems about `lsemFuelMemF` and `lsemFuelMemFk` are their
instances at `X86Isa.x86Isa`.

## Main definitions

* `SObl`, `SObl.holds`, `oblOf`, `symObl`: index obligations and their collection.
* `RunLOk`: the steps of a list of instructions are in bounds.
* `oblOk`, `oblCheckWith`, `ownedCheckMC`: the checks.

## Main results

* `oblOf_iff`, `symObl_sound_at`, `symObl_sound`: the obligations of a step and of a stretch
  hold exactly when its accesses are in bounds.
* `runIdxOk_runL_at`, `runIdxOk_of_runL_at`, `runIdxOk_runL`, `runIdxOk_of_runL`: the
  in-bounds condition of a run splits at a stretch.
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
    {B : List LinstrRM} {b : Block} {T : Term} {p : Nat}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symObl ((B.drop p).take (bstopOf T b - p)) SSt.start sym =
      symObl (bodyAt B b T) SSt.start sym := by
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · rfl
  · unfold bodyAt
    rw [take_cons B (by omega) hx, symObl_label_at hlab hl]

theorem symObl_entry {B : List LinstrRM} {b : Block} {T : Term} {p : Nat}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symObl ((B.drop p).take (bstopOf T b - p)) SSt.start = symObl (bodyAt B b T) SSt.start :=
  symObl_entry_at (fun h ss => symStep_label h ss) hp hle

/-! ## 3. The checks -/

/-- The index obligations of the rewritten block are obligations of the source block over
    registers and flags live at the block, unless no halting run passes through the
    block. -/
def oblOk (L : Nat → List String × Bool) (k : Nat) (T : Term) (B B' : List LinstrRM)
    (b b' : Block) (sym : LinstrRM → SSt → SOut := symStep) : Bool :=
  match T with
  | .ret => true
  | _ =>
      match symRun (bodyAt B b T) SSt.start sym with
      | .ok _ _ =>
          (symObl (bodyAt B' b' T) SSt.start sym).all fun o =>
            (symObl (bodyAt B b T) SSt.start sym).contains o &&
              okIn (L k) o.1.vars o.1.readsF
      | _ => true

/-- `oblOk` at every block pair of the two graphs. -/
def oblCheckWith (L : Nat → List String × Bool) (B B' : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      (List.range G.blocks.size).all fun k =>
        oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym
  | _, _ => false

/-- **The checker on bounds-checked runs**: `ownedCheckM` and `oblCheckWith` at the live
    sets `ownedCheckM` computes. The symbolic step `sym` and the symbolic branch condition
    `dec` default to the x86 ones, `symStep` and `symDec`. -/
def ownedCheckMC (outs : List String) (B B' : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let R := runsOf B B' G G' sym
      let L := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false)) dec
      ownedCheckWithR outs (fun k => L.getD k ([], false)) B B' G G' R dec
        && oblCheckWith (fun k => L.getD k ([], false)) B B' sym
  | _, _ => false

theorem ownedCheckMC_with_at {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hS : SymSubst sym dec) {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' sym dec = true) :
    ∃ L, ownedCheckWith outs L B B' sym dec = true ∧ oblCheckWith L B B' sym = true := by
  unfold ownedCheckMC at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true] at h
          exact ⟨_, ownedCheckWithR_spec_at hS hG hG' h.1, h.2⟩

theorem ownedCheckMC_with {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' = true) :
    ∃ L, ownedCheckWith outs L B B' = true ∧ oblCheckWith L B B' = true :=
  ownedCheckMC_with_at symSubst_x86 h

/-- `ownedCheckMC` accepts only pairs `ownedCheckM` accepts. -/
theorem ownedCheckM_of_ownedCheckMC {outs : List String} {B B' : List LinstrRM}
    {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (h : ownedCheckMC outs B B' sym dec = true) : ownedCheckM outs B B' sym dec = true := by
  unfold ownedCheckMC at h
  unfold ownedCheckM
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true] at h
          exact h.1

theorem oblOk_spec {L : Nat → List String × Bool} {k : Nat} {T : Term} {B B' : List LinstrRM}
    {b b' : Block} {sym : LinstrRM → SSt → SOut} (h : oblOk L k T B B' b b' sym = true)
    (hT : T ≠ .ret) {ss : SSt}
    {gs : List SG} (hs : symRun (bodyAt B b T) SSt.start sym = .ok ss gs) :
    ∀ o ∈ symObl (bodyAt B' b' T) SSt.start sym, o ∈ symObl (bodyAt B b T) SSt.start sym ∧
      (∀ v ∈ o.1.vars, v ∈ (L k).1) ∧ (o.1.readsF = true → (L k).2 = true) := by
  have h2 : (match symRun (bodyAt B b T) SSt.start sym with
      | .ok _ _ =>
          (symObl (bodyAt B' b' T) SSt.start sym).all fun o =>
            (symObl (bodyAt B b T) SSt.start sym).contains o &&
              okIn (L k) o.1.vars o.1.readsF
      | _ => true) = true := by
    cases T with
    | ret => exact absurd rfl hT
    | _ => exact h
  rw [hs] at h2
  simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h2
  intro o ho
  exact ⟨(h2 o ho).1, okIn_spec (h2 o ho).2⟩

/-! ## 4. Soundness -/

/-- The simulation on runs in bounds of the instruction set `I` up to the measure `N`: a
    halting source run in bounds from a block entry is matched by a halting run in bounds of
    the rewritten body. -/
def SimAtC (I : Isa) (outs : List String) (L : Nat → List String × Bool)
    (B B' : List LinstrRM) (G G' : CFG) (fn : String) (N : Nat) : Prop :=
  ∀ (fuel k : Nat) (s s' t : LstateMF),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    Pair B B' (G.blk k) (G'.blk k) s.prog.base.reg.lpc s'.prog.base.reg.lpc →
    Rel (L k) s s' → s.prog.lfn = fn →
    I.lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    I.RunIdxOk (singletonProgM fn B) fuel s →
    ∃ f' t', I.lsemFuelMemF (singletonProgM fn B') f' s' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' s'

theorem fall_contC {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec) {N k : Nat}
    (ih : SimAtC I outs L B B' G G' fn N) (hk : k < G.blocks.size) {nx : Option Nat}
    (hn : G.next k = nx) (hn' : G'.next k = nx) {w w' t : LstateMF} {f0 : Nat}
    (hw : w.prog.base.reg.lpc = (G.blk k).stop) (hw' : w'.prog.base.reg.lpc = (G'.blk k).stop)
    (hfn : w.prog.lfn = fn) (hfn' : w'.prog.lfn = fn)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) f0 w = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) f0 w)
    (hmeas : f0 * (G.blocks.size + 1) + (G.blocks.size - (k + 1)) < N)
    (hrel : ∀ j, nx = some j → Rel (L j) w w') (hobs : nx = none → Obs outs w w') :
    ∃ f' t', I.lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' w' := by
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  cases nx with
  | none =>
      have e1 := (stop_next hc.hG hk).1 hn
      have e2 := (stop_next hc.hG' hk').1 hn'
      rw [halt_at_end_at I hfn (hw.trans e1)] at hrun
      cases hrun
      exact ⟨0, w', halt_at_end_at I hfn' (hw'.trans e2) 0, hobs rfl, trivial⟩
  | some j =>
      obtain ⟨hj, hjlt, e1⟩ := (stop_next hc.hG hk).2 j hn
      obtain ⟨-, -, e2⟩ := (stop_next hc.hG' hk').2 j hn'
      subst hj
      exact ih f0 (k + 1) w w' t hmeas hjlt (Or.inl ⟨hw.trans e1, hw'.trans e2⟩) (hrel _ rfl)
        hfn hrun hok

theorem jump_contC {I : Isa} {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} {N tg : Nat} (ih : SimAtC I outs L B B' G G' fn N)
    (htg : tg < G.blocks.size) {l l' : LLabel}
    (hl : findLabel l (B.map Prod.fst) = some (G.blk tg).start)
    (hl' : findLabel l' (B'.map Prod.fst) = some (G'.blk tg).start) {w w' t : LstateMF}
    {f1 : Nat} (hw : w.prog.base.reg.lpc = (G.blk tg).start + 1)
    (hw' : w'.prog.base.reg.lpc = (G'.blk tg).start + 1) (hfn : w.prog.lfn = fn)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) f1 w = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) f1 w)
    (hmeas : f1 * (G.blocks.size + 1) + (G.blocks.size - tg) < N) (hrel : Rel (L tg) w w') :
    ∃ f' t', I.lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' w' :=
  ih f1 tg w w' t hmeas htg (Or.inr ⟨hw, label_at hl, hw', label_at hl'⟩) hrel hfn hrun hok

theorem sim_stepC {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec)
    (hob : ∀ k < G.blocks.size, oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym = true)
    {N : Nat} (ih : SimAtC I outs L B B' G G' fn N) :
    SimAtC I outs L B B' G G' fn (N + 1) := by
  intro fuel k s s' t hN hk hpair hrel hfn hrun hokS
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
    (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s
    (holds_start s)
  rw [symRun_entry_at hL.label hE hle] at hD
  rcases blockOk_spec hok hret with hfail | ⟨ss, gs, ss', gs', hS, hS', hgs, hta, hex⟩
  · rw [hfail] at hD
    simp only [SOut.DescN] at hD
    rw [hD] at hu
    cases hu
  rw [hS] at hD
  obtain ⟨hAll, hH, hFr⟩ := hD.1 u hu
  have hV : ∀ r ∈ (L k).1, s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r := hrel.2.2.2.1
  have hH0' : Holds s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of s'.zf
      SSt.start s' :=
    ⟨fun _ => rfl, fun q => by rw [hrel.2.1]; rfl, rfl, by simp [SSt.start, STerm.ev],
      by simp [SSt.start, STerm.ev]⟩
  rw [hTk] at hle'
  have hD' := symRun_sound_at hL.step_sound (singletonProgM fn B')
    ((B'.drop s'.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s' hH0'
  rw [symRun_entry_at hL.label hE' hle', hS'] at hD'
  have hAllN := allG_normG.mpr hAll
  have hAll' : AllG s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of gs' :=
    allG_normG.mp fun g hg =>
      (SG.holds_congr _ g (fun r hr => (hV r ((hgs g hg).2.1 r hr)).symm)
        (fun e => by
          obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 ((hgs g hg).2.2 e)
          exact ⟨hc.symm, ho.symm⟩)).mp
      (hAllN g (hgs g hg).1)
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (hD'.2 hAll')
  obtain ⟨-, hH', hFr'⟩ := hD'.1 u' hu'
  have hplain' := body_plain hc.hG' hk' hs1'
  rw [hTk] at hplain' hbstop'
  -- the index obligations: the source block is in bounds, so the rewritten block is
  have hOS := (symObl_sound_at hL.step_sound (singletonProgM fn B) _ SSt.start _ _ _ _ _ s u
    (holds_start s)
    ⟨ss, gs, by rw [symRun_entry_at hL.label hE hle]; exact hS⟩ hu).mp hlS
  rw [symObl_entry_at hL.label hE hle] at hOS
  have hO := oblOk_spec (hob k hk) hret hS
  have hlI : RunLOk (singletonProgM fn B') ((B'.drop s'.prog.base.reg.lpc).take
      (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) s' I := by
    refine (symObl_sound_at hL.step_sound (singletonProgM fn B') _ SSt.start _ _ _ _ _ s' u'
      hH0' ⟨ss', gs', by rw [symRun_entry_at hL.label hE' hle']; exact hS'⟩ hu').mpr
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
    (symRun_good_at hL.good _ SSt.good_start hS) (symRun_good_at hL.good _ SSt.good_start hS')
    (by rw [hul'', hul']) (by rw [hFr'.2.2, hrel.2.2.1, hFr.2.2]) hex
  have hfle : f ≤ fuel := by omega
  obtain ⟨m', hm', hmok⟩ : ∃ m', (∀ f0, I.lsemFuelMemF (singletonProgM fn B') (m' + f0) s' =
      I.lsemFuelMemF (singletonProgM fn B') f0 u') ∧
      ∀ f0, I.RunIdxOk (singletonProgM fn B') f0 u' →
        I.RunIdxOk (singletonProgM fn B') (m' + f0) s' := ⟨_, hrun', hokJ⟩
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
    obtain ⟨f'', t', hr, hobs, hrok⟩ := fall_contC hc ih hk hnx.symm hnx'.symm hw hw' hul'
      hul'' hru hokU (measure_le hN hfle hk)
      (fun j hj => hsucc j (by simp [hT, Term.succs, hj]))
      (fun hn => hhalt (by simp [hT, hn, Term.halts]))
    exact ⟨m' + f'', t', by rw [hm']; exact hr, hobs, hmok _ hrok⟩
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
    · rw [if_pos hx, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : I.step (singletonProgM fn B') (.Lgoto (x, l'), zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [I.step_goto, if_pos (by simpa [singletonProgM, hul'', hul'] using hx),
          evalJumpMem_single hl']
        rfl
      have hfetch' : findInstrMem (singletonProgM fn B') u'.prog =
          some (.Lgoto (x, l'), zt') := by
        rw [findInstrMem_single hul'', hw', hz']
      obtain ⟨f'', t', hr, hobs, hrok⟩ := jump_contC (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1 hok1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_goto _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
    · rw [if_neg hx] at he
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
    · rw [if_pos hd, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : I.step (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [I.step_cond, if_pos (hdec.trans hd), evalJumpMem_single hl']
        rfl
      obtain ⟨f'', t', hr, hobs, hrok⟩ := jump_contC (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1 hok1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_cond _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
    · rw [if_neg hd] at he
      simp only [Option.some.injEq] at he
      have he' : I.step (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with base := u'.prog.base.nextPc } } := by
        rw [I.step_cond, if_neg (by rw [hdec]; exact hd)]
      obtain ⟨f'', t', hr, hobs, hrok⟩ := fall_contC (w := u1)
        (w' := { u' with prog := { u'.prog with base := u'.prog.base.nextPc } })
        hc ih hk hnx.symm hnx'.symm
        (by rw [← he]; show u.prog.base.reg.lpc + 1 = _; omega)
        (by show u'.prog.base.reg.lpc + 1 = _; omega)
        (by rw [← he]; exact hul') hul'' hr1 hok1
        (measure_le hN (show f1 ≤ fuel by omega) hk)
        (fun j hj => by rw [← he]; exact hsucc j (by simp [hT, Term.succs, hj]))
        (fun hn => by rw [← he]; exact hhalt (by simp [hT, hn, Term.halts]))
      refine ⟨m' + (f'' + 1), t', ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_cond _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
  · exact absurd hT hret

theorem simAtC_all {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec) {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec)
    (hob : ∀ k < G.blocks.size,
      oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym = true) :
    ∀ N, SimAtC I outs L B B' G G' fn N
  | 0 => fun _ _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => sim_stepC hL hc hob (simAtC_all hL hc hob N)

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
      I.RunIdxOk (singletonProgM fn B') fuel' s := by
  unfold ownedCheckWith at h
  unfold oblCheckWith at hob
  split at h
  · rename_i G G' hG hG'
    rw [hG, hG'] at hob
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq,
      List.all_eq_true, List.mem_range] at h hob
    obtain ⟨⟨⟨hne, hne'⟩, hsz⟩, hblk⟩ := h
    have hc : Checked outs L B B' G G' sym dec :=
      ⟨hG, hG', hsz.symm, fun k hk => ⟨(hblk k hk).1.symm, (hblk k hk).2⟩⟩
    have hwl : B.map Prod.fst ≠ [] := by simpa using hne
    have hwl' : B'.map Prod.fst ≠ [] := by simpa using hne'
    obtain ⟨h0, hs0⟩ := cfgOf_start_zero hG hwl
    obtain ⟨-, hs0'⟩ := cfgOf_start_zero hG' hwl'
    exact simAtC_all hL hc hob _ fuel 0 s s t (Nat.lt_succ_self _) h0
      (Or.inl ⟨hpc.trans hs0.symm, hpc.trans hs0'.symm⟩)
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩ hfn hrun hok
  · cases h

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
  obtain ⟨L, hL', hO⟩ := ownedCheckMC_with_at hS h
  obtain ⟨f', t', hr, hobs, hok⟩ := ownedCheckWithC_sound_at hL hL' hO fn s t hfn hpc fuel
    (I.lsemFuelMemF_of_checked _ fuel s t hrun) (I.runIdxOk_of_checked _ fuel s t hrun)
  exact ⟨f', t', I.lsemFuelMemFk_of_runIdxOk true _ f' s t' hr hok, hobs⟩

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
