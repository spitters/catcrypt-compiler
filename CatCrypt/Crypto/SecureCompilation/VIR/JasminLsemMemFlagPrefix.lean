/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86IsaDef

@[expose] public section

set_option autoImplicit false

/-!
# A straight-line prefix in front of a body on the flag machine

A body `B` run by the flag machine `lsemFuelMemF` and the body `pre ++ B` behind a
straight-line prefix of `Lopn` instructions differ in their program counters and label
positions by the length of the prefix. This module proves that a run of `B` is matched, step
for step, by a run of `pre ++ B` from the state with the program counter moved by that
length, and composes it with the run of the prefix.

## Main results

* `findLabelMem_prefix`: a label search behind an all-`Lopn` prefix is the search in the
  rest, moved by the prefix length.
* `ShiftRel`: two states equal up to a program counter moved by `d`.
* `CtlOK`: the instructions the matching covers (an `Lopn`, a label, a zero-flag
  conditional, a goto).
* `evalJumpMem_prefix`, `findInstrMem_prefix`: a jump and a fetch behind the prefix from the
  moved state.
* `evalInstrPMemF_prefix`, `lsemFuelMemF_prefix`: one step and every halting run of `B` are
  matched by the same number of steps of `pre ++ B` from the moved state.
* `lsemFuelMemF_prepend`: a run of the prefix followed by a halting run of `B` from its end
  state, with the program counter at `0`, is a halting run of `pre ++ B`.
* `shiftS`, `evalInstrPMemF_prefix_eq`, `lsemFuelMemF_prefix_eq`: the run of `pre ++ B` from
  the moved state is the moved run of `B`, as an equation; `lsemFuelMemF_of_prefix` is its
  converse direction, a halting run of the body behind the prefix as a halting run of `B`.
* `step_prefix_eq_calls`, `lsemFuelMemF_prefix_eq_calls`, `lsemFuelMemF_of_prefix_calls`,
  `lsemFuelMemF_prepend_calls`: the same at an instruction set whose steps contain those of
  `x86Isa` and whose further steps are local calls; `lsemFuelMemF_of_prefix` and
  `lsemFuelMemF_prepend` are their instances at `x86Isa`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower

/-- A label search behind an all-`Lopn` prefix is the search in the rest, moved by the
    prefix length. -/
theorem findLabelMem_prefix (l : LLabel) (xs ys : List LinstrRM)
    (hx : ∀ i ∈ xs, IsLopn i) :
    findLabelMem l (xs ++ ys) = (findLabelMem l ys).map (· + xs.length) := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_append, List.findIdx?_append]
  have hnone : (xs.map Prod.fst).findIdx? (JasminLsemLabeled.isLabel l) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    obtain ⟨d, o, s, hd⟩ := hx i hi
    rw [hd]
    rfl
  rw [hnone, List.length_map]
  simp

/-- Two flag-machine states equal up to the program counter, the second moved by `d`. -/
structure ShiftRel (d : Nat) (s s' : LstateMF) : Prop where
  /-- The function names agree. -/
  lfn : s'.prog.lfn = s.prog.lfn
  /-- The zero flags agree. -/
  zf : s'.zf = s.zf
  /-- The bases agree up to the program counter moved by `d`. -/
  base : s'.prog.base = s.prog.base.setLpc (s.prog.base.lpc + d)

theorem ShiftRel.lpc {d : Nat} {s s' : LstateMF} (h : ShiftRel d s s') :
    s'.prog.base.lpc = s.prog.base.lpc + d := by
  rw [h.base]; rfl

/-- The instructions the prefix matching covers: an `Lopn`, a label, a conditional on the
    zero flag, or a goto. -/
def CtlOK (i : LinstrRM) : Prop :=
  IsLopn i ∨ (∃ kd l, i.1 = LinstrR.Llabel kd l)
    ∨ (∃ c l, i.1 = LinstrR.Lcond c l ∧ flagCondCC? i ≠ none)
    ∨ (∃ tgt, i.1 = LinstrR.Lgoto tgt)

theorem evalJumpMem_prefix (fn : String) (pre B : List LinstrRM) (hpre : ∀ i ∈ pre, IsLopn i)
    (l : LLabel) (p q : LstatePM)
    (h : evalJumpMem (singletonProgM fn B) l p = some q) :
    evalJumpMem (singletonProgM fn (pre ++ B)) l
        { p with base := p.base.setLpc (p.base.lpc + pre.length) }
      = some { q with base := q.base.setLpc (q.base.lpc + pre.length) } := by
  unfold evalJumpMem at h ⊢
  simp only [singletonProgM] at h ⊢
  rw [findLabelMem_prefix l pre B hpre]
  cases hl : findLabelMem l B with
  | none => simp [hl] at h
  | some pc =>
      simp only [hl, Option.some.injEq] at h
      subst h
      simp only [Option.map_some, Option.some.injEq]
      rw [show pc + pre.length + 1 = pc + 1 + pre.length by omega]
      rfl

theorem nextPc_shift (b : LstateM) (d : Nat) :
    (b.setLpc (b.lpc + d)).nextPc = b.nextPc.setLpc (b.nextPc.lpc + d) := by
  simp only [LstateM.setLpc_nextPc', LstateM.nextPc_setLpc', LstateM.lpc_nextPc]
  rw [Nat.add_right_comm]

/-- **One step behind the prefix.** A step of `B` at an instruction of `CtlOK` is matched by
    the step of `pre ++ B` at the same instruction from the moved state, into the moved
    state. -/
theorem evalInstrPMemF_prefix (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) {i : LinstrRM} (hi : CtlOK i) {s s' u : LstateMF}
    (hR : ShiftRel pre.length s s')
    (h : evalInstrPMemF (singletonProgM fn B) i s = some u) :
    ∃ u', evalInstrPMemF (singletonProgM fn (pre ++ B)) i s' = some u'
      ∧ ShiftRel pre.length u u' := by
  obtain ⟨hfn, hzf, hbase⟩ := hR
  obtain ⟨⟨b, lfn⟩, zf⟩ := s
  obtain ⟨⟨b', lfn'⟩, zf'⟩ := s'
  simp only at hfn hzf hbase
  subst hfn hzf hbase
  rcases hi with hl | ⟨kd, l, hw⟩ | ⟨c, l, hw, hcc⟩ | ⟨tgt, hw⟩
  · rw [evalInstrPMemF_isLopn _ i _ hl] at h ⊢
    obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨b1, z1⟩ := bz
    have hpc := fstepF_lpc_succ _ _ _ _ _ hb
    refine ⟨{ prog := { base := b1.setLpc (b.lpc + pre.length + 1), lfn := lfn' }, zf := z1 },
      ?_, rfl, rfl, ?_⟩
    · simp only at hb
      simp only [fstepF_setLpc]
      rw [hb]
      rfl
    · show b1.setLpc (b.lpc + pre.length + 1) = b1.setLpc (b1.lpc + pre.length)
      rw [show b1.lpc = b.lpc + 1 from hpc, Nat.add_right_comm]
  · obtain ⟨wire, tag⟩ := i
    obtain rfl : wire = LinstrR.Llabel kd l := hw
    rw [evalInstrPMemF_label] at h ⊢
    cases h
    exact ⟨_, rfl, rfl, rfl, nextPc_shift b pre.length⟩
  · obtain ⟨wire, tag⟩ := i
    obtain rfl : wire = LinstrR.Lcond c l := hw
    have h1 : cmpArgs? (LinstrR.Lcond c l, tag) = none := rfl
    have h2 : movRegArgs? (LinstrR.Lcond c l, tag) = none := rfl
    cases h3 : flagCondCC? (LinstrR.Lcond c l, tag) with
    | none => exact absurd h3 hcc
    | some pl =>
        obtain ⟨pol, lbl⟩ := pl
        unfold evalInstrPMemF at h ⊢
        simp only [h1, h2, h3] at h ⊢
        split at h
        · rename_i hz
          rw [if_pos hz]
          obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
          have hj := evalJumpMem_prefix fn pre B hpre lbl ⟨b, lfn'⟩ q hq
          refine ⟨⟨⟨q.base.setLpc (q.base.lpc + pre.length), q.lfn⟩, zf'⟩, ?_, rfl, rfl, rfl⟩
          rw [hj]; rfl
        · rename_i hz
          rw [if_neg hz]
          cases h
          exact ⟨_, rfl, rfl, rfl, nextPc_shift b pre.length⟩
  · obtain ⟨wire, tag⟩ := i
    obtain rfl : wire = LinstrR.Lgoto tgt := hw
    obtain ⟨gfn, l⟩ := tgt
    have hev : ∀ (R : LprogM) (x : LstateMF),
        evalInstrPMemF R (LinstrR.Lgoto (gfn, l), tag) x
          = (if gfn = R.lfn then evalJumpMem R l x.prog else none).map
              (fun p => { x with prog := p }) := fun R x => by
      rw [evalInstrPMemF_delegate R _ x rfl rfl rfl rfl rfl rfl]; rfl
    rw [hev] at h ⊢
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    split at hq
    · rename_i hf
      have hj := evalJumpMem_prefix fn pre B hpre l ⟨b, lfn'⟩ q hq
      refine ⟨⟨⟨q.base.setLpc (q.base.lpc + pre.length), q.lfn⟩, zf'⟩, ?_, rfl, rfl, rfl⟩
      rw [if_pos (show gfn = (singletonProgM fn (pre ++ B)).lfn from hf)]
      simp only at hj ⊢
      rw [hj]; rfl
    · exact absurd hq (by simp)

/-- The instruction fetched behind the prefix from the moved state is the instruction of `B`
    fetched from the state. -/
theorem findInstrMem_prefix (fn : String) (pre B : List LinstrRM) {s s' : LstateMF}
    (hR : ShiftRel pre.length s s') :
    findInstrMem (singletonProgM fn (pre ++ B)) s'.prog
      = findInstrMem (singletonProgM fn B) s.prog := by
  unfold findInstrMem
  simp only [singletonProgM]
  rw [hR.lfn, hR.lpc, Nat.add_comm, List.getElem?_append_right (by omega)]
  simp
  rfl

/-- **A run behind the prefix.** Every halting run of `B` from a state is matched, with the
    same fuel, by a halting run of `pre ++ B` from the state with the program counter moved
    by the length of the prefix, into the moved final state. -/
theorem lsemFuelMemF_prefix (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, CtlOK i) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, ShiftRel pre.length s s' →
      lsemFuelMemF (singletonProgM fn B) fuel s = some t →
      ∃ t', lsemFuelMemF (singletonProgM fn (pre ++ B)) fuel s' = some t'
        ∧ ShiftRel pre.length t t' := by
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hR h
      unfold lsemFuelMemF at h ⊢
      rw [findInstrMem_prefix fn pre B hR]
      cases hf : findInstrMem (singletonProgM fn B) s.prog with
      | none => simp only [hf] at h; cases h; exact ⟨s', rfl, hR⟩
      | some i => simp [hf] at h
  | succ n ih =>
      intro s s' t hR h
      unfold lsemFuelMemF at h ⊢
      rw [findInstrMem_prefix fn pre B hR]
      cases hf : findInstrMem (singletonProgM fn B) s.prog with
      | none => simp only [hf] at h; cases h; exact ⟨s', rfl, hR⟩
      | some i =>
          simp only [hf] at h ⊢
          have hiB : i ∈ B := by
            unfold findInstrMem at hf
            split at hf
            · exact List.mem_of_getElem? hf
            · cases hf
          cases he : evalInstrPMemF (singletonProgM fn B) i s with
          | none => simp [he] at h
          | some u =>
              simp only [he] at h
              obtain ⟨u', he', hRu⟩ := evalInstrPMemF_prefix fn pre B hpre (hB i hiB) hR he
              rw [he']
              exact ih hRu h

/-! ## The run behind the prefix as an equation -/

/-- The state with its program counter moved by `d`. -/
def shiftS (d : Nat) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := s.prog.base.setLpc (s.prog.base.lpc + d) } }

theorem shiftRel_shiftS (d : Nat) (s : LstateMF) : ShiftRel d s (shiftS d s) :=
  ⟨rfl, rfl, rfl⟩

theorem ShiftRel.eq_shiftS {d : Nat} {s s' : LstateMF} (h : ShiftRel d s s') :
    s' = shiftS d s := by
  obtain ⟨⟨b', lfn'⟩, zf'⟩ := s'
  obtain ⟨hfn, hzf, hbase⟩ := h
  simp only at hfn hzf hbase
  subst hfn hzf hbase
  rfl

theorem evalJumpMem_prefix_eq (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (l : LLabel) (p : LstatePM) :
    evalJumpMem (singletonProgM fn (pre ++ B)) l
        { p with base := p.base.setLpc (p.base.lpc + pre.length) }
      = (evalJumpMem (singletonProgM fn B) l p).map
          fun q => { q with base := q.base.setLpc (q.base.lpc + pre.length) } := by
  cases h : evalJumpMem (singletonProgM fn B) l p with
  | some q => exact evalJumpMem_prefix fn pre B hpre l p q h
  | none =>
      unfold evalJumpMem at h ⊢
      simp only [singletonProgM] at h ⊢
      rw [findLabelMem_prefix l pre B hpre]
      cases hl : findLabelMem l B with
      | none => rfl
      | some pc => simp [hl] at h

/-- **One step behind the prefix, as an equation.** At an instruction of `CtlOK`, the step of
    `pre ++ B` from the moved state is the moved step of `B`. -/
theorem evalInstrPMemF_prefix_eq (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) {i : LinstrRM} (hi : CtlOK i) (s : LstateMF) :
    evalInstrPMemF (singletonProgM fn (pre ++ B)) i (shiftS pre.length s)
      = (evalInstrPMemF (singletonProgM fn B) i s).map (shiftS pre.length) := by
  cases h : evalInstrPMemF (singletonProgM fn B) i s with
  | some u =>
      obtain ⟨u', hu', hR⟩ := evalInstrPMemF_prefix fn pre B hpre hi (shiftRel_shiftS _ s) h
      rw [hu', hR.eq_shiftS]
      rfl
  | none =>
      obtain ⟨⟨b, lfn⟩, zf⟩ := s
      rcases hi with hl | ⟨kd, l, hw⟩ | ⟨c, l, hw, hcc⟩ | ⟨tgt, hw⟩
      · rw [evalInstrPMemF_isLopn _ i _ hl] at h ⊢
        simp only [shiftS, fstepF_setLpc]
        simp only [Option.map_eq_none_iff] at h
        simp [h]
      · obtain ⟨wire, tag⟩ := i
        obtain rfl : wire = LinstrR.Llabel kd l := hw
        rw [evalInstrPMemF_label] at h
        cases h
      · obtain ⟨wire, tag⟩ := i
        obtain rfl : wire = LinstrR.Lcond c l := hw
        have h1 : cmpArgs? (LinstrR.Lcond c l, tag) = none := rfl
        have h2 : movRegArgs? (LinstrR.Lcond c l, tag) = none := rfl
        cases h3 : flagCondCC? (LinstrR.Lcond c l, tag) with
        | none => exact absurd h3 hcc
        | some pl =>
            obtain ⟨pol, lbl⟩ := pl
            unfold evalInstrPMemF at h ⊢
            simp only [h1, h2, h3] at h ⊢
            split at h
            · rename_i hz
              rw [if_pos (show (shiftS pre.length
                { prog := { base := b, lfn := lfn }, zf := zf }).zf = pol from hz)]
              simp only [shiftS]
              have hj := evalJumpMem_prefix_eq fn pre B hpre lbl ⟨b, lfn⟩
              simp only [Option.map_eq_none_iff] at h
              simp only at hj ⊢
              rw [hj, h]
              rfl
            · cases h
      · obtain ⟨wire, tag⟩ := i
        obtain rfl : wire = LinstrR.Lgoto tgt := hw
        obtain ⟨gfn, l⟩ := tgt
        have hev : ∀ (R : LprogM) (x : LstateMF),
            evalInstrPMemF R (LinstrR.Lgoto (gfn, l), tag) x
              = (if gfn = R.lfn then evalJumpMem R l x.prog else none).map
                  (fun p => { x with prog := p }) := fun R x => by
          rw [evalInstrPMemF_delegate R _ x rfl rfl rfl rfl rfl rfl]; rfl
        rw [hev] at h ⊢
        simp only [Option.map_eq_none_iff] at h
        simp only [Option.map_none, Option.map_eq_none_iff]
        by_cases hf : gfn = fn
        · rw [if_pos (show gfn = (singletonProgM fn (pre ++ B)).lfn from hf)]
          rw [if_pos (show gfn = (singletonProgM fn B).lfn from hf)] at h
          have hj := evalJumpMem_prefix_eq fn pre B hpre l ⟨b, lfn⟩
          simp only [shiftS] at hj ⊢
          rw [hj, h]
          rfl
        · rw [if_neg (show ¬ gfn = (singletonProgM fn (pre ++ B)).lfn from hf)]

/-- **A run behind the prefix, as an equation.** The run of `pre ++ B` from the moved state is
    the moved run of `B`. -/
theorem lsemFuelMemF_prefix_eq (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, CtlOK i) :
    ∀ (fuel : Nat) (s : LstateMF),
      lsemFuelMemF (singletonProgM fn (pre ++ B)) fuel (shiftS pre.length s)
        = (lsemFuelMemF (singletonProgM fn B) fuel s).map (shiftS pre.length) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s
      unfold lsemFuelMemF
      rw [findInstrMem_prefix fn pre B (shiftRel_shiftS _ s)]
      cases findInstrMem (singletonProgM fn B) s.prog <;> rfl
  | succ n ih =>
      intro s
      unfold lsemFuelMemF
      rw [findInstrMem_prefix fn pre B (shiftRel_shiftS _ s)]
      cases hf : findInstrMem (singletonProgM fn B) s.prog with
      | none => rfl
      | some i =>
          have hiB : i ∈ B := by
            unfold findInstrMem at hf
            split at hf
            · exact List.mem_of_getElem? hf
            · cases hf
          simp only
          rw [evalInstrPMemF_prefix_eq fn pre B hpre (hB i hiB) s]
          cases evalInstrPMemF (singletonProgM fn B) i s with
          | none => rfl
          | some u => exact ih u

/-! ## The prefix at an instruction set with local calls -/

section Calls

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
  (Isa shadowCall? callShadow retWord CallRes retRes retRes_arr retArr argsRead argsRead_congr
    eq_callShadow_of_shadowCall?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

/-- The argument words of operands do not depend on the program counter. -/
theorem argsRead_shiftS (aa : Nat → Option Nat) (d : Nat) (s : LstateMF) (k : Nat)
    (srcs : List LOperand) :
    argsRead aa (shiftS d s).prog.base k srcs = argsRead aa s.prog.base k srcs :=
  argsRead_congr aa (b := s.prog.base) (b' := (shiftS d s).prog.base) rfl k srcs
    fun o _ => by cases o <;> rfl

/-- Writing a result word commutes with moving the program counter. -/
theorem retWord_shiftS (dst : String) (r : BitVec 64) (d : Nat) (s : LstateMF) :
    retWord dst r (shiftS d s) = shiftS d (retWord dst r s) := by
  simp only [retWord, shiftS, LstateM.setReg, LstateM.nextPc, LstateM.setLpc, LstateM.lpc,
    JasminLsemWidthN.LstateN.setReg, JasminLsemWidthN.LstateN.nextPc, Nat.add_right_comm]

/-- Writing the result of a call commutes with moving the program counter. -/
theorem retRes_shiftS (dst : String) (x : CallRes) (d : Nat) (s : LstateMF) :
    retRes dst x (shiftS d s) = shiftS d (retRes dst x s) := by
  cases x with
  | word r => exact retWord_shiftS dst r d s
  | arr a =>
      simp only [retRes_arr, retArr, shiftS, LstateM.setArr, LstateM.nextPc, LstateM.setLpc,
        LstateM.lpc, JasminLsemWidthN.LstateN.nextPc, Nat.add_right_comm]

/-- **One step behind the prefix at an instruction set with local calls.** For an instruction
    set `I` whose steps contain those of `x86Isa` and whose further steps are local calls, at
    an instruction of `CtlOK` the step of `pre ++ B` from the moved state is the moved step of
    `B`. -/
theorem step_prefix_eq_calls {I : Isa} {aa : String → Nat → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa) (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) {i : LinstrRM} (hi : CtlOK i) (s : LstateMF) :
    I.step (singletonProgM fn (pre ++ B)) i (shiftS pre.length s)
      = (I.step (singletonProgM fn B) i s).map (shiftS pre.length) := by
  have hx : x86Isa.step (singletonProgM fn (pre ++ B)) i (shiftS pre.length s)
      = (x86Isa.step (singletonProgM fn B) i s).map (shiftS pre.length) :=
    evalInstrPMemF_prefix_eq fn pre B hpre hi s
  cases hsh : shadowCall? i.1 with
  | none =>
      rw [Isa.CallLocal.step_eq I hle hcl _ hsh, Isa.CallLocal.step_eq I hle hcl _ hsh, hx]
  | some q =>
      cases hB : I.step (singletonProgM fn B) i s with
      | some t =>
          rcases hcl _ _ s t hB with hxB | ⟨dst, f, srcs, x, hsh', rfl, hfwd⟩
          · rw [hxB, Option.map_some] at hx
            exact hle _ _ _ _ hx
          · obtain ⟨w, tag⟩ := i
            simp only at hsh'
            subst hsh'
            rw [Option.map_some, ← retRes_shiftS]
            exact hfwd _ tag dst srcs _ rfl (argsRead_shiftS _ _ _ _ _)
      | none =>
          cases hA : I.step (singletonProgM fn (pre ++ B)) i (shiftS pre.length s) with
          | none => rfl
          | some t' =>
              exfalso
              rcases hcl _ _ _ t' hA with hxA | ⟨dst, f, srcs, x, hsh', -, hfwd⟩
              · rw [hxA] at hx
                obtain ⟨u, hu, -⟩ := Option.map_eq_some_iff.mp hx.symm
                rw [hle _ _ _ _ hu] at hB
                cases hB
              · obtain ⟨w, tag⟩ := i
                simp only at hsh'
                subst hsh'
                rw [hfwd _ tag dst srcs s rfl (argsRead_shiftS _ _ _ _ _).symm] at hB
                cases hB

/-- **A run behind the prefix at an instruction set with local calls, as an equation.** The
    run of `pre ++ B` from the moved state is the moved run of `B`. -/
theorem lsemFuelMemF_prefix_eq_calls {I : Isa} {aa : String → Nat → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa) (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, CtlOK i) :
    ∀ (fuel : Nat) (s : LstateMF),
      I.lsemFuelMemF (singletonProgM fn (pre ++ B)) fuel (shiftS pre.length s)
        = (I.lsemFuelMemF (singletonProgM fn B) fuel s).map (shiftS pre.length) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s
      unfold Isa.lsemFuelMemF
      rw [findInstrMem_prefix fn pre B (shiftRel_shiftS _ s)]
      cases findInstrMem (singletonProgM fn B) s.prog <;> rfl
  | succ n ih =>
      intro s
      unfold Isa.lsemFuelMemF
      rw [findInstrMem_prefix fn pre B (shiftRel_shiftS _ s)]
      cases hf : findInstrMem (singletonProgM fn B) s.prog with
      | none => rfl
      | some i =>
          have hiB : i ∈ B := by
            unfold findInstrMem at hf
            split at hf
            · exact List.mem_of_getElem? hf
            · cases hf
          simp only
          rw [step_prefix_eq_calls hle hcl fn pre B hpre (hB i hiB) s]
          cases I.step (singletonProgM fn B) i s with
          | none => rfl
          | some u => exact ih u

/-- **The body behind the prefix at an instruction set with local calls.** A halting run of
    `pre ++ B` from the moved state is the moved halting run of `B`. -/
theorem lsemFuelMemF_of_prefix_calls {I : Isa} {aa : String → Nat → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa) (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, CtlOK i) (fuel : Nat) (s : LstateMF)
    (t' : LstateMF)
    (h : I.lsemFuelMemF (singletonProgM fn (pre ++ B)) fuel (shiftS pre.length s) = some t') :
    ∃ t, I.lsemFuelMemF (singletonProgM fn B) fuel s = some t ∧ t' = shiftS pre.length t := by
  rw [lsemFuelMemF_prefix_eq_calls hle hcl fn pre B hpre hB fuel s] at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨t, ht, rfl⟩

/-- **The prefix and then the body at an instruction set with local calls.** If the prefix
    runs from a base `b0` at program counter `0` to `b1`, and `B` runs at `I` from `b1` with
    the program counter at `0` to `t`, then `pre ++ B` runs at `I` from `b0` to the state `t`
    with the program counter moved by the length of the prefix. -/
theorem lsemFuelMemF_prepend_calls {I : Isa} {aa : String → Nat → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa) (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, CtlOK i) (b0 b1 : LstateM) (zf z1 : Bool)
    (h0 : b0.lpc = 0) (hpreRun : runStraightF pre b0 zf = some (b1, z1)) (fuel : Nat)
    (t : LstateMF)
    (h : I.lsemFuelMemF (singletonProgM fn B) fuel
      { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } = some t) :
    ∃ t', I.lsemFuelMemF (singletonProgM fn (pre ++ B)) (pre.length + fuel)
        { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ ShiftRel pre.length t t' := by
  rw [lsemFuelMemF_segF_of_some hle (singletonProgM fn (pre ++ B)) fn rfl pre b0 zf fuel _ hpre
    (fun k hk => by
      simp only [singletonProgM, h0, Nat.zero_add]
      exact List.getElem?_append_left hk) hpreRun]
  have hpc := runStraightF_lpc pre b0 zf b1 z1 hpreRun
  rw [h0, Nat.zero_add] at hpc
  have hsh : ({ prog := { base := b1, lfn := fn }, zf := z1 } : LstateMF)
      = shiftS pre.length { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } := by
    simp only [shiftS, LstateM.lpc_setLpc, Nat.zero_add, ← hpc]
    rfl
  rw [hsh, lsemFuelMemF_prefix_eq_calls hle hcl fn pre B hpre hB fuel, h, Option.map_some]
  exact ⟨_, rfl, shiftRel_shiftS _ _⟩

/-- **The body behind the prefix.** A halting run of `pre ++ B` from the moved state is the
    moved halting run of `B`. -/
theorem lsemFuelMemF_of_prefix (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, CtlOK i) (fuel : Nat) (s : LstateMF)
    (t' : LstateMF)
    (h : lsemFuelMemF (singletonProgM fn (pre ++ B)) fuel (shiftS pre.length s) = some t') :
    ∃ t, lsemFuelMemF (singletonProgM fn B) fuel s = some t ∧ t' = shiftS pre.length t := by
  rw [← x86Isa_lsemFuelMemF] at h ⊢
  exact lsemFuelMemF_of_prefix_calls (Isa.StepLe.refl x86Isa)
    (Isa.CallLocal.refl x86Isa (fun _ _ => none)) fn pre B hpre hB fuel s t' h

/-- **The prefix and then the body.** If the prefix runs from a base `b0` at program counter
    `0` to `b1`, and `B` runs from `b1` with the program counter at `0` to `t`, then
    `pre ++ B` runs from `b0` to the state `t` with the program counter moved by the length of
    the prefix. -/
theorem lsemFuelMemF_prepend (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, CtlOK i) (b0 b1 : LstateM) (zf z1 : Bool)
    (h0 : b0.lpc = 0) (hpreRun : runStraightF pre b0 zf = some (b1, z1)) (fuel : Nat)
    (t : LstateMF)
    (h : lsemFuelMemF (singletonProgM fn B) fuel
      { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } = some t) :
    ∃ t', lsemFuelMemF (singletonProgM fn (pre ++ B)) (pre.length + fuel)
        { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ ShiftRel pre.length t t' := by
  rw [← x86Isa_lsemFuelMemF] at h ⊢
  exact lsemFuelMemF_prepend_calls (Isa.StepLe.refl x86Isa)
    (Isa.CallLocal.refl x86Isa (fun _ _ => none)) fn pre B hpre hB b0 b1 zf z1 h0 hpreRun
    fuel t h

end Calls

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix
