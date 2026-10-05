/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold

@[expose] public section

set_option autoImplicit false

/-!
# The cell fold of a body with labels and conditionals

`ImageCellFold.cellFold` folds the constant-index array accesses of a chain of `Lopn`
instructions into cell copies. This module gives the fold for a body with control flow
and proves it sound on the flag machine `lsemFuelMemF`.

`cellFoldL R env is` passes over the body once. An `Lopn` is folded by
`ImageCellFold.foldOne` under the constants known at its position; a label, a `goto` and
a conditional on the zero flag are kept. The known constants follow `ImageCellFold.kstep`
through an `Lopn`, are emptied by a label, and pass a `goto` or a conditional unchanged.
A jump lands behind a label, where no constant is known, so the constants known at a
position hold on every path that reaches it. The fold maps instruction to instruction:
the folded body has the length, the labels and the control instructions of the body at
the same positions, and the immediate move that sets an index register is kept.

## Main definitions

* `ctlB`: the control instructions the fold keeps (a label, a `goto`, a conditional on
  the zero flag).
* `foldOneL`, `kstepL`, `cellFoldL`: the fold of one instruction, the known constants
  behind an instruction, and the fold of a body.
* `envAt env is pc`: the constants known at position `pc` of the body `is`, from the
  constants `env` at position `0`.
* `CellRelF`: `ImageCellFold.CellRel` on the bases of two flag-machine states, with the
  same function name and zero flag.

## Main results

* `cellFoldL_length`, `cellFoldL_getElem?`, `isLabel_foldOneL`, `findLabelMem_cellFoldL`,
  `cellFoldL_eq_cellFold`: the structural facts of the fold.
* `evalInstrPMemF_cellFoldL`: one step of the body is matched by one step of the folded
  body.
* `lsemFuelMemF_cellFoldL`: a halting run of the body is matched, with the same fuel, by a
  run of the folded body.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM MemTag)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM LstatePM singletonProgM
  findInstrMem findLabelMem evalJumpMem evalInstrPMemL)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF evalInstrPMemF
  lsemFuelMemF findInstrMem_singleton flagCondCC? cmpArgs? movRegArgs? carryArgs? wideArgs? aluFlagOp? withALUFlags)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn
  fstepF fstepF_lpc_succ evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (isLabel findLabel
  findLabel_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold

/-! ## The fold -/

/-- The control instructions the fold keeps: a label, a `goto` and a conditional on the
    zero flag. -/
def ctlB (i : LinstrRM) : Bool :=
  match i.1 with
  | .Llabel _ _ => true
  | .Lgoto _ => true
  | .Lcond _ _ => (flagCondCC? i).isSome
  | _ => false

/-- **The fold of one instruction of a body** under the known constants `env`: an `Lopn`
    is folded by `foldOne`, a control instruction of `ctlB` is kept, and every other
    instruction is refused. -/
def foldOneL (R : Slots) (env : KEnv) (i : LinstrRM) : Option LinstrRM :=
  if isLopnB i then foldOne R env i else if ctlB i then some i else none

/-- The known constants behind an instruction of a body: `kstep` through an `Lopn`, none
    behind a label, and the same constants behind every other instruction. -/
def kstepL (env : KEnv) (i : LinstrRM) : KEnv :=
  match i.1 with
  | .Lopn _ _ _ => kstep env i
  | .Llabel _ _ => []
  | _ => env

/-- **The cell fold of a body** from the known constants `env`. -/
def cellFoldL (R : Slots) : KEnv → List LinstrRM → Option (List LinstrRM)
  | _, [] => some []
  | env, i :: is =>
      match foldOneL R env i, cellFoldL R (kstepL env i) is with
      | some i', some is' => some (i' :: is')
      | _, _ => none

/-- The constants known at position `pc` of the body `is`, from the constants `env` at
    position `0`. -/
def envAt (env : KEnv) (is : List LinstrRM) (pc : Nat) : KEnv := (is.take pc).foldl kstepL env

/-! ## Structural facts -/

theorem envAt_zero (env : KEnv) (is : List LinstrRM) : envAt env is 0 = env := rfl

theorem envAt_cons_succ (env : KEnv) (i : LinstrRM) (is : List LinstrRM) (pc : Nat) :
    envAt env (i :: is) (pc + 1) = envAt (kstepL env i) is pc := rfl

theorem envAt_succ {env : KEnv} {is : List LinstrRM} {pc : Nat} {i : LinstrRM}
    (h : is[pc]? = some i) : envAt env is (pc + 1) = kstepL (envAt env is pc) i := by
  unfold envAt
  rw [List.take_add_one, h, List.foldl_append]
  rfl

theorem kstepL_lopn {env : KEnv} {i : LinstrRM} (h : isLopnB i = true) :
    kstepL env i = kstep env i := by
  obtain ⟨d, o, sr, hd⟩ := isLopnB_isLopn h
  unfold kstepL
  rw [hd]

theorem kstepL_label {env : KEnv} {i : LinstrRM} {l : LLabel} (h : isLabel l i.1 = true) :
    kstepL env i = [] := by
  unfold kstepL
  unfold isLabel at h
  split at h
  · rename_i hd
    rw [hd]
  · cases h

/-- A folded instruction is an `Lopn`. -/
theorem foldOne_isLopn {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOne R env i = some i') : isLopnB i' = true := by
  have hk : ∀ j : LinstrRM, keepB R j = true → isLopnB j = true := fun j hj => by
    simp only [keepB, Bool.and_eq_true] at hj
    exact hj.1.1
  unfold foldOne at hf
  repeat' split at hf
  all_goals first
    | cases hf; rfl
    | (cases hf; exact hk _ ‹_›)
    | cases hf

/-- The fold of an `Lopn` is `foldOne`; an instruction that is no `Lopn` is kept. -/
theorem foldOneL_cases {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOneL R env i = some i') :
    (isLopnB i = true ∧ isLopnB i' = true ∧ foldOne R env i = some i')
      ∨ (isLopnB i = false ∧ ctlB i = true ∧ i' = i) := by
  unfold foldOneL at hf
  split at hf
  · rename_i hl
    exact Or.inl ⟨hl, foldOne_isLopn hf, hf⟩
  · rename_i hl
    split at hf
    · rename_i hc
      cases hf
      exact Or.inr ⟨by simpa using hl, hc, rfl⟩
    · cases hf

theorem isLabel_of_isLopnB {i : LinstrRM} (h : isLopnB i = true) (l : LLabel) :
    isLabel l i.1 = false := by
  obtain ⟨d, o, sr, hd⟩ := isLopnB_isLopn h
  rw [hd]
  rfl

/-- **The fold keeps the labels.** -/
theorem isLabel_foldOneL {R : Slots} {env : KEnv} {i i' : LinstrRM}
    (hf : foldOneL R env i = some i') (l : LLabel) : isLabel l i'.1 = isLabel l i.1 := by
  rcases foldOneL_cases hf with ⟨h1, h2, -⟩ | ⟨-, -, rfl⟩
  · rw [isLabel_of_isLopnB h1, isLabel_of_isLopnB h2]
  · rfl

/-- **The fold keeps the length of the body.** -/
theorem cellFoldL_length {R : Slots} :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldL R env is = some is' →
      is'.length = is.length
  | [], _, _, hf => by
      cases hf
      rfl
  | i :: is, env, is', hf => by
      unfold cellFoldL at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        simp only [List.length_cons, cellFoldL_length is _ _ h2]
      · cases hf

/-- **The fold is position by position:** the instruction of the folded body at a
    position is the fold of the instruction of the body there, under the constants known
    at that position. -/
theorem cellFoldL_getElem? {R : Slots} :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldL R env is = some is' →
      ∀ (k : Nat) (i : LinstrRM), is[k]? = some i →
        ∃ i', is'[k]? = some i' ∧ foldOneL R (envAt env is k) i = some i'
  | [], _, _, _, k, i, hi => by simp at hi
  | j :: is, env, is', hf, k, i, hi => by
      unfold cellFoldL at hf
      split at hf
      · rename_i j' is'' h1 h2
        cases hf
        cases k with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨j', rfl, h1⟩
        | succ k =>
            rw [List.getElem?_cons_succ] at hi
            obtain ⟨i', hi', hfo⟩ := cellFoldL_getElem? is _ _ h2 k i hi
            exact ⟨i', by rw [List.getElem?_cons_succ]; exact hi', by
              rw [envAt_cons_succ]; exact hfo⟩
      · cases hf

/-- **The fold keeps the label positions.** -/
theorem findLabelMem_cellFoldL {R : Slots} (l : LLabel) :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFoldL R env is = some is' →
      findLabelMem l is' = findLabelMem l is
  | [], _, _, hf => by
      cases hf
      rfl
  | i :: is, env, is', hf => by
      unfold cellFoldL at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        have ih := findLabelMem_cellFoldL l is _ _ h2
        unfold findLabelMem findLabel at ih ⊢
        simp only [List.map_cons, List.findIdx?_cons, isLabel_foldOneL h1 l, ih]
      · cases hf

/-- On a chain of `Lopn` instructions the fold of a body is the fold of the chain. -/
theorem cellFoldL_eq_cellFold {R : Slots} :
    ∀ (is : List LinstrRM) (env : KEnv), is.all isLopnB = true →
      cellFoldL R env is = cellFold R env is
  | [], _, _ => rfl
  | i :: is, env, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      unfold cellFoldL cellFold
      rw [kstepL_lopn h.1, cellFoldL_eq_cellFold is _ h.2]
      simp only [foldOneL, h.1, if_true]
      cases foldOne R env i <;> cases cellFold R (kstep env i) is <;> rfl

/-- Behind a label no constant is known. -/
theorem envAt_findLabelMem {env : KEnv} {is : List LinstrRM} {l : LLabel} {pc : Nat}
    (h : findLabelMem l is = some pc) : envAt env is (pc + 1) = [] := by
  obtain ⟨k, hk, hl⟩ := findLabel_sound l _ pc h
  rw [List.getElem?_map] at hk
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hk
  rw [envAt_succ hi]
  exact kstepL_label hl

/-! ## The state relation -/

/-- **The cell relation of two flag-machine states:** `CellRel` on the bases, the same
    function name and the same zero flag. -/
structure CellRelF (R : Slots) (env : KEnv) (s s' : LstateMF) : Prop where
  base : CellRel R env s.prog.base s'.prog.base
  lfn : s'.prog.lfn = s.prog.lfn
  zf : s'.zf = s.zf

theorem cellRel_nil {R : Slots} {env : KEnv} {s s' : LstateM} (h : CellRel R env s s') :
    CellRel R [] s s' :=
  { h with env := fun x k hk => by simp [kval] at hk }

theorem cellRel_setLpc {R : Slots} {env : KEnv} {s s' : LstateM} (h : CellRel R env s s')
    (p : Nat) : CellRel R env (s.setLpc p) (s'.setLpc p) :=
  ⟨h.reg, rfl, h.arr, h.mem, h.cf, h.of, h.cells, h.env⟩

theorem cellRel_nextPc {R : Slots} {env : KEnv} {s s' : LstateM} (h : CellRel R env s s') :
    CellRel R env s.nextPc s'.nextPc :=
  ⟨h.reg, congrArg (· + 1) h.pc, h.arr, h.mem, h.cf, h.of, h.cells, h.env⟩

/-! ## The steps of the control instructions -/

theorem evalInstrPMemF_label (P : LprogM) (k : LabelKind) (l : LLabel) (tg : MemTag)
    (s : LstateMF) :
    evalInstrPMemF P (.Llabel k l, tg) s
      = some { s with prog := { s.prog with base := s.prog.base.nextPc } } := by
  rfl

theorem evalInstrPMemF_goto (P : LprogM) (f : String) (l : LLabel) (tg : MemTag)
    (s : LstateMF) :
    evalInstrPMemF P (.Lgoto (f, l), tg) s
      = if f = P.lfn then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
        else none := by
  have he : evalInstrPMemL P (.Lgoto (f, l), tg) s.prog
      = if f = P.lfn then evalJumpMem P l s.prog else none := rfl
  simp only [evalInstrPMemF, cmpArgs?, movRegArgs?, flagCondCC?, he, carryArgs?,
    wideArgs?, withALUFlags, aluFlagOp?]
  by_cases hfn : f = P.lfn
  · simp only [if_pos hfn]
    cases evalJumpMem P l s.prog <;> rfl
  · simp only [if_neg hfn]

theorem evalInstrPMemF_flagCond (P : LprogM) {i : LinstrRM} {c : LOperand} {l l' : LLabel}
    {pol : Bool} (hi : i.1 = .Lcond c l) (h : flagCondCC? i = some (pol, l'))
    (s : LstateMF) :
    evalInstrPMemF P i s
      = if s.zf = pol then (evalJumpMem P l' s.prog).map (fun p => { s with prog := p })
        else some { s with prog := { s.prog with base := s.prog.base.nextPc } } := by
  have h1 : cmpArgs? i = none := by
    unfold cmpArgs?
    rw [hi]
  have h2 : movRegArgs? i = none := by
    unfold movRegArgs?
    rw [hi]
  unfold evalInstrPMemF
  rw [h1, h2, h]

/-- **A jump** from cell-related states: the folded body has the label at the same
    position, and behind a label no constant is known. -/
theorem evalJumpMem_cellFoldL {R : Slots} {env e0 : KEnv} {fn : String}
    {is is' : List LinstrRM} {l : LLabel} (hlbl : findLabelMem l is' = findLabelMem l is)
    {p p' q : LstatePM} (hC : CellRel R env p.base p'.base) (hfn : p'.lfn = p.lfn)
    (h : evalJumpMem (singletonProgM fn is) l p = some q) :
    ∃ q', evalJumpMem (singletonProgM fn is') l p' = some q' ∧ q'.lfn = q.lfn
      ∧ CellRel R (envAt e0 is q.base.lpc) q.base q'.base := by
  unfold evalJumpMem at h ⊢
  simp only [singletonProgM] at h ⊢
  rw [hlbl]
  cases hl : findLabelMem l is with
  | none => rw [hl] at h; cases h
  | some pc =>
      rw [hl] at h
      cases h
      refine ⟨_, rfl, hfn, ?_⟩
      have he : envAt e0 is (p.base.setLpc (pc + 1)).lpc = [] := envAt_findLabelMem hl
      rw [he]
      exact cellRel_setLpc (cellRel_nil hC) _

/-! ## One step -/

/-- **One step of the fold of a body.** For slot arrays `R` that pass `slotsOkB` and
    `cellsDistinctB` and a body `is` whose cell fold from the constants `e0` is `is'`: a
    step of the instruction of `is` at the program counter of `s` is matched, from every
    state `s'` cell-related to `s` under the constants known at that position, by a step
    of the instruction of `is'` at the same position, into a state cell-related under the
    constants known at the new program counter. -/
theorem evalInstrPMemF_cellFoldL {R : Slots} (hR : slotsOkB R = true)
    (hD : cellsDistinctB R = true) {e0 : KEnv} {is is' : List LinstrRM}
    (hf : cellFoldL R e0 is = some is') (fn : String) {i : LinstrRM} {s s' t : LstateMF}
    (hi : is[s.prog.base.lpc]? = some i)
    (hC : CellRelF R (envAt e0 is s.prog.base.lpc) s s')
    (h : evalInstrPMemF (singletonProgM fn is) i s = some t) :
    ∃ i' t', is'[s.prog.base.lpc]? = some i'
      ∧ evalInstrPMemF (singletonProgM fn is') i' s' = some t'
      ∧ CellRelF R (envAt e0 is t.prog.base.lpc) t t' := by
  obtain ⟨i', hi', hfo⟩ := cellFoldL_getElem? is e0 is' hf _ i hi
  refine ⟨i', ?_⟩
  have hlbl := fun l => findLabelMem_cellFoldL (R := R) l is e0 is' hf
  have hnext : envAt e0 is (s.prog.base.lpc + 1) = kstepL (envAt e0 is s.prog.base.lpc) i :=
    envAt_succ hi
  rcases foldOneL_cases hfo with ⟨hl, hl', hfo'⟩ | ⟨hl, hc, hii⟩
  · rw [evalInstrPMemF_isLopn _ i s (isLopnB_isLopn hl)] at h
    obtain ⟨bz, hbz, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨b, z⟩ := bz
    obtain ⟨b', hb', hCb⟩ := fold_step hR hD hfo' hC.base hbz
    refine ⟨{ prog := { s'.prog with base := b' }, zf := z }, hi', ?_, ?_, hC.lfn, rfl⟩
    · rw [evalInstrPMemF_isLopn _ i' s' (isLopnB_isLopn hl'), hC.zf, hb']
      rfl
    · have hpc : b.lpc = s.prog.base.lpc + 1 := fstepF_lpc_succ i _ b _ z hbz
      show CellRel R (envAt e0 is b.lpc) b b'
      rw [hpc, hnext, kstepL_lopn hl]
      exact hCb
  · subst hii
    obtain ⟨w, tg⟩ := i'
    unfold ctlB at hc
    dsimp only at hc
    split at hc
    · rename_i k l
      rw [evalInstrPMemF_label] at h
      cases h
      refine ⟨_, hi', evalInstrPMemF_label _ _ _ _ _, ?_, hC.lfn, hC.zf⟩
      show CellRel R (envAt e0 is (s.prog.base.nextPc).lpc) _ _
      rw [JasminLsemMemLoop.LstateM.lpc_nextPc, hnext]
      exact cellRel_nextPc (cellRel_nil hC.base)
    · rename_i tgt
      obtain ⟨f, l⟩ := tgt
      rw [evalInstrPMemF_goto] at h ⊢
      by_cases hfn : f = (singletonProgM fn is).lfn
      · rw [if_pos hfn] at h
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨q', hq', hqfn, hCq⟩ := evalJumpMem_cellFoldL (e0 := e0) (fn := fn) (hlbl l)
          hC.base hC.lfn hq
        refine ⟨{ s' with prog := q' }, hi', ?_, hCq, hqfn, hC.zf⟩
        rw [if_pos (show f = (singletonProgM fn is').lfn from hfn), hq']
        rfl
      · rw [if_neg hfn] at h
        cases h
    · rename_i c l
      obtain ⟨⟨pol, l'⟩, hcc⟩ := Option.isSome_iff_exists.mp hc
      rw [evalInstrPMemF_flagCond _ rfl hcc] at h ⊢
      rw [hC.zf]
      split at h
      · rename_i hz
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨q', hq', hqfn, hCq⟩ := evalJumpMem_cellFoldL (e0 := e0) (fn := fn) (hlbl l')
          hC.base hC.lfn hq
        refine ⟨{ prog := q', zf := s.zf }, hi', ?_, hCq, hqfn, rfl⟩
        rw [if_pos hz, hq']
        rfl
      · rename_i hz
        cases h
        refine ⟨_, hi', if_neg hz, ?_, hC.lfn, rfl⟩
        show CellRel R (envAt e0 is (s.prog.base.nextPc).lpc) _ _
        rw [JasminLsemMemLoop.LstateM.lpc_nextPc, hnext]
        exact cellRel_nextPc hC.base
    · cases hc

/-! ## The run -/

/-- **The cell fold of a body realises the body.** For slot arrays `R` that pass
    `slotsOkB` and `cellsDistinctB` and a body `is` whose cell fold from the constants `e0`
    is `is'`: a halting run of `is` on the flag machine from `s` is matched, with the same
    fuel, by a run of `is'` from every state `s'` cell-related to `s` under the constants
    known at the program counter of `s`, into a state cell-related to the final state, with
    the same zero flag. -/
theorem lsemFuelMemF_cellFoldL {R : Slots} (hR : slotsOkB R = true)
    (hD : cellsDistinctB R = true) {e0 : KEnv} {is is' : List LinstrRM}
    (hf : cellFoldL R e0 is = some is') (fn : String) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      lsemFuelMemF (singletonProgM fn is) fuel s = some t →
      ∃ t', lsemFuelMemF (singletonProgM fn is') fuel s' = some t'
        ∧ CellRelF R (envAt e0 is t.prog.base.lpc) t t' := by
  have hfetch : ∀ {s s' : LstateMF}, CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      findInstrMem (singletonProgM fn is) s.prog = none →
      findInstrMem (singletonProgM fn is') s'.prog = none := fun {s s'} hC h => by
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hC.base.pc
    by_cases hfn : s.prog.lfn = fn
    · rw [findInstrMem_singleton _ _ _ hfn] at h
      rw [findInstrMem_singleton _ _ _ (hC.lfn.trans hfn), hpc]
      rw [List.getElem?_eq_none_iff] at h ⊢
      rw [cellFoldL_length is e0 is' hf]
      exact h
    · exact if_neg fun h' => hfn (hC.lfn.symm.trans h')
  have hfetch' : ∀ {s s' : LstateMF} {i : LinstrRM},
      CellRelF R (envAt e0 is s.prog.base.lpc) s s' →
      findInstrMem (singletonProgM fn is) s.prog = some i →
      is[s.prog.base.lpc]? = some i
        ∧ ∀ i', is'[s.prog.base.lpc]? = some i' →
          findInstrMem (singletonProgM fn is') s'.prog = some i' := fun {s s' i} hC h => by
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hC.base.pc
    by_cases hfn : s.prog.lfn = fn
    · rw [findInstrMem_singleton _ _ _ hfn] at h
      refine ⟨h, fun i' hi' => ?_⟩
      rw [findInstrMem_singleton _ _ _ (hC.lfn.trans hfn), hpc]
      exact hi'
    · have hn : findInstrMem (singletonProgM fn is) s.prog = none := if_neg hfn
      rw [hn] at h
      cases h
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hC h
      unfold lsemFuelMemF at h ⊢
      cases hfi : findInstrMem (singletonProgM fn is) s.prog with
      | none =>
          rw [hfi] at h
          cases h
          rw [hfetch hC hfi]
          exact ⟨s', rfl, hC⟩
      | some i =>
          rw [hfi] at h
          cases h
  | succ n ih =>
      intro s s' t hC h
      unfold lsemFuelMemF at h ⊢
      cases hfi : findInstrMem (singletonProgM fn is) s.prog with
      | none =>
          rw [hfi] at h
          cases h
          rw [hfetch hC hfi]
          exact ⟨s', rfl, hC⟩
      | some i =>
          rw [hfi] at h
          dsimp only at h
          cases hev : evalInstrPMemF (singletonProgM fn is) i s with
          | none => rw [hev] at h; cases h
          | some u =>
              rw [hev] at h
              dsimp only at h
              obtain ⟨hi, hfi'⟩ := hfetch' hC hfi
              obtain ⟨i', u', hi', hev', hCu⟩ :=
                evalInstrPMemF_cellFoldL hR hD hf fn hi hC hev
              rw [hfi' i' hi']
              dsimp only
              rw [hev']
              exact ih hCu h

end CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL
