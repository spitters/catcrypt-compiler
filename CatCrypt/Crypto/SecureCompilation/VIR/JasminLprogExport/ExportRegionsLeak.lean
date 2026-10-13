/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-!
# The leakage of the region export

The machine leakage of the code `exportR` emits for a structured program, as a function of
the program and the entry valuation, and its preservation by the export on the programs of
`RegionExportable` without a `call`.

A traced run of `k` steps is `StepsL P k s t ℓ`: the run `Steps x86Isa P k s t` together
with the events `stepsLeak P k s = ℓ` of the instructions it fetches, in the event model
`instrLeakF` of the traced flag machine `lsemFuelMemFLeak`. The events are a function of
the program, the number of steps and the entry state, and a traced run to a halted state
is the terminating run of `lsemFuelMemFLeak` with the same events.

`machRun Pj nArgs fn fuel p d n V` runs `p` from `V` at depth `d` and label `n` and returns
its results with the machine events of its export in the function `fn`:

* a binding emits `bindLeak`: for a `stackLoad` or `stackStore`, the address event of its
  source event at the array name and with the scaled index of its instruction, and
  nothing for every other operation;
* a counted loop with trip count `N` emits the events `forHeadLeak` of the seeds of its
  carried arrays, `branch (N = 0)` for the zero-trip guard, then for each trip `i` the
  events of the body, the events `forTailLeak` of the assignment of the returned arrays
  and `branch (i + 1 < N)` for the back edge, then the events `forShiftLeak` of the shift
  of the carried arrays and the events of the continuation; it emits no event of the trip
  count. Each array move emits two address events at the source name and the offset `0`
  (`arrMoves_idx0Leak`), so the three lists are empty for carried registers and do not
  depend on the valuation;
* a branch on the bit `b` emits `branch (!b)` for its guard, which jumps to the else arm
  when the bit is clear, then the events of the arm `b` selects, then, after the then arm,
  `branch true` for the jump to the join label, which every run takes, then the events of
  the continuation;
* a loop in exit-flag form emits, for each run of its body within `fuel`, the events of
  the body followed by `branch b` for the flag `b` it returns, then the events of the
  continuation;
* a call returns `none`.

A run of a straight segment is obtained from the value lemma of the segment. The lemma is
applied to the program cut after the segment, in which a run that reaches the end of the
segment has the length of the segment, and the run is moved to the full program: with no
event for instructions that emit nothing (`stepsL_of_quiet`), and with the events
`idx0Leak` for array moves behind a move of zero into their index register
(`stepsL_of_idx0`). A value lemma with an explicit number of steps gives its traced run
directly (`stepsL_of_quiet_le`).

## Main definitions

* `stepsLeak`, `StepsL`: the events of a run of steps and the traced run.
* `QuietLopn`, `idx0Leak`, `Idx0Lopn`: instructions that emit nothing, and the events of
  an array move at the index zero.
* `bindLeak`, `tripLeak`, `forHeadLeak`, `forTailLeak`, `forShiftLeak`, `machRun`,
  `machLeak`, `ifResLeak`: the machine events of an exported program and of the
  assignment of the results of a branch arm.
* `ExportRLeakSim`: the simulation statement of `ExportRSim` with the events of the run.
* `RegionEntry`, `RegionEntryPub`, `RegionEntryPubDen`: entry states of the exported code
  that agree with a valuation, pairs of them at valuations equal on the public positions,
  and such pairs at the first of which the program denotes within the fuel.

## Main results

* `lsemFuelMemFLeak_stepsL`, `fRun_of_stepsL`: a traced run of steps in front of a traced
  run of the flag machine, and a traced run to a halted state as a terminating run.
* `stepsL_of_quiet`, `stepsL_of_idx0`, `stepsL_of_quiet_le`: the traced runs of straight
  segments.
* `exportRLeakSim_ret`, `exportRLeakSim_var`, `exportRLeakSim_for`, `exportRLeakSim_if`,
  `exportRLeakSim_while`: the rules of the return, the binding, the counted loop, the
  branch and the loop in exit-flag form.
* `exportR_leakSim`: the traced simulation on the programs of `RegionExportable` without a
  `call`.
* `machRun_of_leakRun`: the source events of two runs determine their machine events.
* `exportR_leak_of_machRun`, `exportR_leak`: every terminating traced run of the exported
  code from an entry state that agrees with `V` has the events `machLeak` at `V`, at a
  fuel at which the source run succeeds.
* `exportR_memFCT`: a program of `RegionExportable` without a `call` that is constant time
  at the source events (`NFCT`) has exported code that is constant time on the traced flag
  machine (`MemFCT`) between the entry states of `RegionEntryPubDen`.
* `exportR_memFCT_whileFree`: for a program that also has no `whileLoop`, between the
  entry states of `RegionEntryPub`.
* `exportR_abiEntryCT`: for such a program exported with its context as the arguments,
  constant time from ABI entries whose valuations agree on the public labels
  (`AbiEntryCT`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF fstepF_lpc_succ
  evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (straightOpsMem_plain
  scalarMemN_comOpsPlain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (loopCtr_ne_argName
  loopCtr_ne_regName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames fstepF_frame_dst)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend inlHom inrHom hvToHom
  lookup_inlHom lookup_inrHom)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel)

/-! ## 1. Traced runs of steps -/

/-- The events of the first `k` steps of `P` from `s`, in execution order: the events
    `instrLeakF` of each fetched instruction at the state it runs from. The list ends at a
    halted state and after the events of an instruction whose step fails. -/
def stepsLeak (P : LprogM) : Nat → LstateMF → List CTLeak
  | 0, _ => []
  | k + 1, s =>
      match findInstrMem P s.prog with
      | none => []
      | some i =>
          instrLeakF i s ++
            match evalInstrPMemF P i s with
            | some s' => stepsLeak P k s'
            | none => []

/-- **The traced run of steps**: `k` steps of `P` on the x86 flag machine from `s` end in
    `t` and emit the events `ℓ`. -/
def StepsL (P : LprogM) (k : Nat) (s t : LstateMF) (ℓ : List CTLeak) : Prop :=
  Steps x86Isa P k s t ∧ stepsLeak P k s = ℓ

/-- A run of no step ends in its entry state. -/
theorem steps_zero_iff {P : LprogM} {s t : LstateMF} : Steps x86Isa P 0 s t ↔ s = t := by
  simp only [Steps, CatCrypt.Crypto.SecureCompilation.Ascent.CutPoint.iter, Option.some.injEq]

/-- A run of `k + 1` steps is the step of the fetched instruction followed by a run of `k`
    steps. -/
theorem steps_succ_iff {P : LprogM} {k : Nat} {s t : LstateMF} :
    Steps x86Isa P (k + 1) s t ↔
      ∃ i u, findInstrMem P s.prog = some i ∧ evalInstrPMemF P i s = some u
        ∧ Steps x86Isa P k u t := by
  simp only [Steps, CatCrypt.Crypto.SecureCompilation.Ascent.CutPoint.iter,
    Option.bind_eq_some_iff, Isa.lsemStepPMemF]
  constructor
  · rintro ⟨u, hu, h⟩
    cases hf : findInstrMem P s.prog with
    | none => rw [hf] at hu; cases hu
    | some i => rw [hf] at hu; exact ⟨i, u, rfl, hu, h⟩
  · rintro ⟨i, u, hf, hu, h⟩
    exact ⟨u, by rw [hf]; exact hu, h⟩

/-- The events of `k + 1` steps are the events of the fetched instruction followed by the
    events of `k` steps from the next state. -/
theorem stepsLeak_succ {P : LprogM} {k : Nat} {s u : LstateMF} {i : LinstrRM}
    (hf : findInstrMem P s.prog = some i) (hu : evalInstrPMemF P i s = some u) :
    stepsLeak P (k + 1) s = instrLeakF i s ++ stepsLeak P k u := by
  simp only [stepsLeak, hf, hu]

/-- The events of a run of `k` steps followed by `j` steps. -/
theorem stepsLeak_add {P : LprogM} {j : Nat} :
    ∀ {k : Nat} {s t : LstateMF}, Steps x86Isa P k s t →
      stepsLeak P (k + j) s = stepsLeak P k s ++ stepsLeak P j t := by
  intro k
  induction k with
  | zero =>
      intro s t h
      obtain rfl := steps_zero_iff.mp h
      simp [stepsLeak]
  | succ k ih =>
      intro s t h
      obtain ⟨i, u, hf, hu, h'⟩ := steps_succ_iff.mp h
      rw [show k + 1 + j = (k + j) + 1 by omega, stepsLeak_succ hf hu, stepsLeak_succ hf hu,
        ih h', List.append_assoc]

/-- The traced run of no step. -/
theorem StepsL.refl (P : LprogM) (s : LstateMF) : StepsL P 0 s s [] :=
  ⟨Steps.refl x86Isa P s, rfl⟩

/-- Traced runs compose, and their events concatenate. -/
theorem StepsL.trans {P : LprogM} {k j : Nat} {s t u : LstateMF} {ℓ ℓ' : List CTLeak}
    (h : StepsL P k s t ℓ) (h' : StepsL P j t u ℓ') : StepsL P (k + j) s u (ℓ ++ ℓ') :=
  ⟨h.1.trans h'.1, by rw [stepsLeak_add h.1, h.2, h'.2]⟩

/-- A traced run at an equal list of events. -/
theorem StepsL.cast {P : LprogM} {k : Nat} {s t : LstateMF} {ℓ ℓ' : List CTLeak}
    (h : StepsL P k s t ℓ) (e : ℓ = ℓ') : StepsL P k s t ℓ' := e ▸ h

/-- **One step with its events.** A step at the counter `k` holding the instruction `i`
    emits the events of `i` at the state it runs from. -/
theorem stepsL_one {P : LprogM} {k : Nat} {s t : LstateMF} {i : LinstrRM} (hat : atPc P k s)
    (hi : P.body[k]? = some i) (h : Steps x86Isa P 1 s t) : StepsL P 1 s t (instrLeakF i s) := by
  refine ⟨h, ?_⟩
  obtain ⟨i', u, hf, hu, -⟩ := steps_succ_iff.mp h
  have hii : i' = i := by
    rw [findInstrMem_of_atPc hat, hi] at hf
    exact (Option.some.inj hf).symm
  subst hii
  rw [stepsLeak_succ hf hu]
  simp [stepsLeak]

/-- A label emits nothing. -/
theorem stepsL_label {P : LprogM} {k : Nat} {s t : LstateMF} {kind : LabelKind} {l : LLabel}
    {tag : MemTag} (hat : atPc P k s) (hi : P.body[k]? = some (.Llabel kind l, tag))
    (h : Steps x86Isa P 1 s t) : StepsL P 1 s t [] :=
  stepsL_one hat hi h

/-- A conditional jump on a condition code emits the branch event of its decision: the
    zero flag against the polarity `pol` on which the jump is taken. -/
theorem stepsL_cc {P : LprogM} {k : Nat} {s t : LstateMF} {cc : String} {l : LLabel}
    {pol : Bool} (hcc : flagCondCC? (condI (.reg cc) l) = some (pol, l)) (hat : atPc P k s)
    (hi : P.body[k]? = some (condI (.reg cc) l)) (h : Steps x86Isa P 1 s t) :
    StepsL P 1 s t [.branch (s.zf == pol)] := by
  have h1 := stepsL_one hat hi h
  have he : instrLeakF (condI (.reg cc) l) s = [.branch (s.zf == pol)] := by
    simp only [instrLeakF, hcc]
  rwa [he] at h1

/-- **A traced run of steps in front of a traced run of the flag machine.** -/
theorem lsemFuelMemFLeak_stepsL {P : LprogM} (f : Nat) :
    ∀ {k : Nat} {s t : LstateMF} {ℓ : List CTLeak}, StepsL P k s t ℓ →
      lsemFuelMemFLeak P (k + f) s
        = (lsemFuelMemFLeak P f t).map fun r => (r.1, ℓ ++ r.2) := by
  intro k
  induction k with
  | zero =>
      intro s t ℓ h
      obtain rfl := steps_zero_iff.mp h.1
      obtain rfl : [] = ℓ := h.2
      simp
  | succ k ih =>
      intro s t ℓ h
      obtain ⟨i, u, hf, hu, h'⟩ := steps_succ_iff.mp h.1
      obtain rfl : stepsLeak P (k + 1) s = ℓ := h.2
      rw [show k + 1 + f = (k + f) + 1 by omega, lsemFuelMemFLeak_step P _ i s u hf hu,
        ih ⟨h', rfl⟩, Option.map_map, stepsLeak_succ hf hu]
      congr 1
      funext r
      simp [List.append_assoc]

/-- **A traced run to a halted state is a terminating run of the flag machine** with the
    same events. -/
theorem fRun_of_stepsL {P : LprogM} {k : Nat} {s t : LstateMF} {ℓ : List CTLeak}
    (h : StepsL P k s t ℓ) (ht : Halted P t) : FRun P s ℓ := by
  refine ⟨k + 0, t, ?_⟩
  rw [lsemFuelMemFLeak_stepsL 0 h, lsemFuelMemFLeak_halt P 0 t ht]
  simp

/-! ## 2. Segments of instructions that emit nothing -/

/-- An `Lopn` instruction that emits no event at any register file. -/
def QuietLopn (i : LinstrRM) : Prop := IsLopn i ∧ ∀ r : LstateN, instrLeakB r i = []

/-- The step of an `Lopn` instruction stays in the function, advances the counter by one
    and is the step of the instruction in every program. -/
theorem lopn_step {P : LprogM} {i : LinstrRM} {s u : LstateMF} (hl : IsLopn i)
    (h : evalInstrPMemF P i s = some u) :
    u.prog.lfn = s.prog.lfn ∧ u.prog.base.lpc = s.prog.base.lpc + 1
      ∧ ∀ P2 : LprogM, evalInstrPMemF P2 i s = some u := by
  rw [evalInstrPMemF_isLopn P i s hl] at h
  obtain ⟨bz, hbz, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨rfl, fstepF_lpc_succ i _ bz.1 s.zf bz.2 hbz, fun P2 => ?_⟩
  rw [evalInstrPMemF_isLopn P2 i s hl, hbz]
  rfl

/-- **A run to the end of a program that ends in a segment of quiet `Lopn` instructions.**
    In a program `Q` whose body is `pre ++ seg`, a run from the counter `pre.length` to the
    counter after `seg` has `seg.length` steps, and it is a traced run with no event of
    every program of the same function whose body is `pre ++ seg ++ post`. -/
theorem stepsL_of_quiet_end (Q : LprogM) :
    ∀ (seg pre : List LinstrRM) (s u : LstateMF) (k : Nat), Q.body = pre ++ seg →
      (∀ i ∈ seg, QuietLopn i) → atPc Q pre.length s → Steps x86Isa Q k s u →
      u.prog.base.lpc = pre.length + seg.length →
      ∀ (P : LprogM) (post : List LinstrRM), P.lfn = Q.lfn → P.body = pre ++ seg ++ post →
        StepsL P seg.length s u [] := by
  intro seg
  induction seg with
  | nil =>
      intro pre s u k hQ _ hat hs _ P post _ _
      cases k with
      | zero =>
          obtain rfl := steps_zero_iff.mp hs
          exact StepsL.refl P s
      | succ k =>
          obtain ⟨i, w, hf, -, -⟩ := steps_succ_iff.mp hs
          rw [findInstrMem_of_atPc hat, hQ, List.append_nil,
            List.getElem?_eq_none (le_refl _)] at hf
          cases hf
  | cons i seg ih =>
      intro pre s u k hQ hq hat hs hend P post hfn hP
      cases k with
      | zero =>
          obtain rfl := steps_zero_iff.mp hs
          rw [hat.2, List.length_cons] at hend
          omega
      | succ k =>
          obtain ⟨i', w, hf, hw, hrest⟩ := steps_succ_iff.mp hs
          have hii : i' = i := by
            rw [findInstrMem_of_atPc hat, hQ, List.getElem?_append_right (le_refl _),
              Nat.sub_self] at hf
            exact (Option.some.inj hf).symm
          subst hii
          obtain ⟨hl, hquiet⟩ := hq i' (List.mem_cons_self ..)
          obtain ⟨hwfn, hwpc, hwP⟩ := lopn_step hl hw
          have hatw : atPc Q (pre ++ [i']).length w :=
            ⟨hwfn.trans hat.1, by rw [hwpc, hat.2, List.length_append, List.length_singleton]⟩
          have hrec := ih (pre ++ [i']) w u k
            (by rw [hQ]; simp only [List.append_assoc, List.cons_append, List.nil_append])
            (fun j hj => hq j (List.mem_cons_of_mem _ hj)) hatw hrest
            (by rw [hend, List.length_append, List.length_singleton, List.length_cons]; omega)
            P post hfn
            (by rw [hP]; simp only [List.append_assoc, List.cons_append, List.nil_append])
          have hfP : findInstrMem P s.prog = some i' := by
            rw [findInstrMem_of_atPc (P := P) ⟨hat.1.trans hfn.symm, hat.2⟩, hP,
              List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
            rfl
          refine ⟨steps_succ_iff.mpr ⟨i', w, hfP, hwP P, hrec.1⟩, ?_⟩
          rw [List.length_cons, stepsLeak_succ hfP (hwP P), hrec.2,
            instrLeakF_of_lopn hl, hquiet]
          rfl

/-- **A segment of quiet `Lopn` instructions, from the run of the program cut after it.**
    When the body of `P` is `pre ++ seg ++ post`, a run of the program with the body
    `pre ++ seg` from the counter `pre.length` to the counter after `seg` is a traced run
    of `P` of `seg.length` steps with no event. -/
theorem stepsL_of_quiet {P : LprogM} {seg pre post : List LinstrRM} {s u : LstateMF}
    {k : Nat} (hbody : P.body = pre ++ seg ++ post) (hq : ∀ i ∈ seg, QuietLopn i)
    (hat : atPc P pre.length s)
    (hs : Steps x86Isa (singletonProgM P.lfn (pre ++ seg)) k s u)
    (hend : u.prog.base.lpc = pre.length + seg.length) : StepsL P seg.length s u [] :=
  stepsL_of_quiet_end (singletonProgM P.lfn (pre ++ seg)) seg pre s u k rfl hq hat hs hend
    P post rfl hbody

/-- An `Lopn` that writes one register from registers and immediates is quiet. -/
theorem quietLopn_regs (dst opn : String) (ss : List LOperand) (tag : MemTag)
    (h : ∀ o ∈ ss, (∃ x, o = LOperand.reg x) ∨ ∃ c, o = LOperand.imm c) :
    QuietLopn (.Lopn [.reg dst] opn ss, tag) :=
  ⟨⟨_, _, _, rfl⟩, fun r => instrLeakB_quiet r dst opn ss tag fun o ho => by
    rcases h o ho with ⟨x, rfl⟩ | ⟨c, rfl⟩ <;> rfl⟩

/-- A copy of a register is quiet. -/
theorem quietLopn_movReg (dst src : String) : QuietLopn (movI dst (.reg src)) :=
  quietLopn_regs _ _ _ _ fun o ho => by
    rw [List.mem_singleton.mp ho]; exact Or.inl ⟨_, rfl⟩

/-- A move of an immediate is quiet. -/
theorem quietLopn_movImm (dst : String) (c : Nat) : QuietLopn (movImmI dst c) :=
  quietLopn_regs _ _ _ _ fun o ho => by
    rw [List.mem_singleton.mp ho]; exact Or.inr ⟨_, rfl⟩

/-- The compare of a register with zero is quiet. -/
theorem quietLopn_cmp (r : String) :
    QuietLopn (guardI (.Lopn [.reg r] (withWidthTag 64 "CMP") [.reg r, .imm 0])) :=
  quietLopn_regs _ _ _ _ fun o ho => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩

/-- The advance of a counted loop is quiet. -/
theorem quietLopn_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, QuietLopn i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;>
  · refine quietLopn_regs _ _ _ _ fun o ho => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩

/-- Register copies are quiet. -/
theorem quietLopn_regMoves (mv : List (String × String)) : ∀ i ∈ regMoves mv, QuietLopn i := by
  intro i hi
  simp only [regMoves, List.mem_map] at hi
  obtain ⟨p, -, rfl⟩ := hi
  exact quietLopn_movReg _ _

/-- A parallel assignment of registers is quiet. -/
theorem quietLopn_parMoves (D : Nat) (tgts : List String) (ops : List LOperand)
    (h : ∀ o ∈ ops, ∃ x, o = LOperand.reg x) : ∀ i ∈ parMoves D tgts ops, QuietLopn i := by
  intro i hi
  simp only [parMoves, stageMoves, commitMoves, List.mem_append, List.mem_map] at hi
  rcases hi with ⟨p, hp, rfl⟩ | ⟨p, -, rfl⟩
  · obtain ⟨x, hx⟩ := h p.1 (List.fst_mem_of_mem_zipIdx hp)
    rw [hx]
    exact quietLopn_movReg _ _
  · exact quietLopn_movReg _ _

/-- A list of typed pairs of register types has no array move. -/
theorem arrPairs_eq_nil {tp : List (JasminTy × String × String)}
    (h : ∀ p ∈ tp, isRegTy p.1 = true) : arrPairs tp = [] := by
  simp only [arrPairs, List.filterMap_eq_nil_iff]
  intro p hp
  have := h p hp
  cases hp1 : p.1 <;> simp_all [isRegTy]

/-- The typed pairs of a carried tuple of register types have no array move. -/
theorem arrPairs_carriedPairs {cs : List JasminTy} (hcs : RegTys cs) (car : List String)
    (ops : List LOperand) : arrPairs (carriedPairs cs car ops) = [] :=
  arrPairs_eq_nil fun p hp => hcs p.1 (List.of_mem_zip (a := p.1) (b := p.2) hp).1

/-- The typed pairs of the shift of a carried tuple of register types have no array
    move. -/
theorem arrPairs_shiftPairs {cs : List JasminTy} (hcs : RegTys cs) (d : Nat) :
    arrPairs (shiftPairs d cs) = [] :=
  arrPairs_eq_nil fun p hp =>
    hcs p.1 (List.of_mem_zip (a := p.1) (b := p.2) (List.mem_reverse.mp hp)).1

/-- **A prefix of a segment of quiet `Lopn` instructions emits nothing.** A run of at most
    `seg.length` steps from the counter of the segment is a traced run with no event. -/
theorem stepsL_of_quiet_le {P : LprogM} :
    ∀ (k : Nat) (seg pre post : List LinstrRM) (s u : LstateMF), P.body = pre ++ seg ++ post →
      (∀ i ∈ seg, QuietLopn i) → atPc P pre.length s → Steps x86Isa P k s u →
      k ≤ seg.length → StepsL P k s u [] := by
  intro k
  induction k with
  | zero => exact fun _ _ _ _ _ _ _ _ hs _ => ⟨hs, rfl⟩
  | succ k ih =>
      intro seg pre post s u hP hq hat hs hk
      cases seg with
      | nil => exact absurd hk (by simp)
      | cons i seg =>
          obtain ⟨i', w, hf, hw, hrest⟩ := steps_succ_iff.mp hs
          have hii : i' = i := by
            rw [findInstrMem_of_atPc hat, hP, List.append_assoc,
              List.getElem?_append_right (le_refl _), Nat.sub_self] at hf
            exact (Option.some.inj hf).symm
          subst hii
          obtain ⟨hl, hquiet⟩ := hq i' (List.mem_cons_self ..)
          obtain ⟨hwfn, hwpc, -⟩ := lopn_step hl hw
          have hrec := ih seg (pre ++ [i']) post w u
            (by rw [hP]; simp only [List.append_assoc, List.cons_append, List.nil_append])
            (fun j hj => hq j (List.mem_cons_of_mem _ hj))
            ⟨hwfn.trans hat.1, by rw [hwpc, hat.2, List.length_append, List.length_singleton]⟩
            hrest (by rw [List.length_cons] at hk; omega)
          refine ⟨hs, ?_⟩
          rw [stepsLeak_succ hf hw, hrec.2, instrLeakF_of_lopn hl, hquiet]
          rfl

/-! ## 2a. Segments of array moves at the index zero -/

/-- The events of an `Lopn` whose first source is an array at a register index, when the
    index register holds zero: the address event at the array name and the offset `0`.
    Every other instruction has none. -/
def idx0Leak (i : LinstrRM) : List CTLeak :=
  match i.1 with
  | .Lopn _ _ (.arrIdx b _ _ :: _) => [.addr b 0]
  | _ => []

/-- An `Lopn` that keeps the register `z` and, from a register file in which `z` holds the
    word zero, emits `idx0Leak`. -/
def Idx0Lopn (z : String) (i : LinstrRM) : Prop :=
  IsLopn i ∧ (∀ r : LstateN, r.lvm z = ⟨64, 0#64⟩ → instrLeakB r i = idx0Leak i)
    ∧ ∀ (P : LprogM) (s u : LstateMF), evalInstrPMemF P i s = some u →
        u.prog.base.reg.lvm z = s.prog.base.reg.lvm z

/-- The load of an array move at the index register `z` into another register. -/
theorem idx0Lopn_load {z t : String} (hzt : z ≠ t) (src : String) (sc w n : Nat) :
    Idx0Lopn z (.Lopn [.reg t] "LOADIDX" [.arrIdx src z sc], .load w n) := by
  refine ⟨⟨_, _, _, rfl⟩, fun r hr => ?_, fun P s u h => ?_⟩
  · simp [instrLeakB, idx0Leak, opLeakF, idxVal]
    exact Or.inr (by rw [hr]; rfl)
  · rw [evalInstrPMemF_isLopn P _ s ⟨_, _, _, rfl⟩] at h
    obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (fstepF_frame_dst (t := bz.1) (z := bz.2) hb
      (by simp [dstNames, opNames, hzt])).1

/-- The store of an array move at the index register `z`: it writes an array cell and
    keeps every register. -/
theorem idx0Lopn_store (z dst src val : String) (sc w n : Nat) :
    Idx0Lopn z (.Lopn [.reg dst] "STOREIDX" [.arrIdx src z sc, .reg val], .store w n) := by
  refine ⟨⟨_, _, _, rfl⟩, fun r hr => ?_, fun P s u h => ?_⟩
  · simp [instrLeakB, idx0Leak, opLeakF, idxVal]
    exact Or.inr (by rw [hr]; rfl)
  · rw [evalInstrPMemF_lopn P _ s ⟨_, _, _, rfl⟩
      (by unfold cmpArgs?; exact if_neg (by decide)) rfl] at h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold stepMemF at hb
    cases h1 : lsemStepMem (.Lopn [.reg dst] "STOREIDX" [.arrIdx src z sc, .reg val],
        .store w n) s.prog.base with
    | some b1 =>
        rw [h1] at hb
        obtain rfl := Option.some.inj hb
        show (withALUFlags _ _ b1).reg.lvm z = _
        rw [withALUFlags_reg]
        simp only [lsemStepMem, storeStruct?, if_true] at h1
        split at h1
        · cases h1
          rfl
        · cases h1
    | none =>
        rw [h1] at hb
        have e1 : ¬ ("STOREIDX" = withWidthTag 64 "ADC") := by decide
        have e2 : ¬ ("STOREIDX" = withWidthTag 64 "SBB") := by decide
        have e3 : ¬ ("STOREIDX" = withWidthTag 64 "ADCX") := by decide
        have e4 : ¬ ("STOREIDX" = withWidthTag 64 "ADOX") := by decide
        have e5 : ¬ ("STOREIDX" = withWidthTag 64 "MOV") := by decide
        simp [carryArgs?, wideArgs?, e1, e2, e3, e4, e5] at hb

/-- Every instruction of a list of array moves at the index register `z` with a scratch
    register other than `z`. -/
theorem idx0Lopn_arrMoves {z t : String} (hzt : z ≠ t) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, Idx0Lopn z i := by
  intro i hi
  simp only [arrMoves, arrMove, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  obtain ⟨a, -, rfl | rfl⟩ := hi
  · exact idx0Lopn_load hzt _ _ _ _
  · exact idx0Lopn_store _ _ _ _ _ _ _

/-- Every instruction of a parallel assignment of arrays at the index register `z`. -/
theorem idx0Lopn_arrParMoves {z t : String} (hzt : z ≠ t) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, Idx0Lopn z i := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact idx0Lopn_arrMoves hzt _ i hi
  · rcases List.mem_append.mp hi with h | h <;> exact idx0Lopn_arrMoves hzt _ i h

/-- **The events of array moves at the index zero**: for each move, two address events at
    the source name and the offset `0`, of its load and of its store. -/
theorem arrMoves_idx0Leak (z t : String) (mv : List ArrMove) :
    (arrMoves z t mv).flatMap idx0Leak
      = mv.flatMap fun a => [CTLeak.addr a.src 0, CTLeak.addr a.src 0] := by
  induction mv with
  | nil => rfl
  | cons a mv ih =>
      rw [arrMoves_cons, List.flatMap_append, ih, List.flatMap_cons]
      rfl

/-- **A run to the end of a program that ends in array moves at the index zero followed by
    quiet instructions.** In a program `Q` whose body is `pre ++ zseg ++ qseg`, a run from
    the counter `pre.length`, where the index register `z` holds zero, to the counter after
    `qseg` is a traced run of every program of the same function whose body is
    `pre ++ zseg ++ qseg ++ post`, with the events `idx0Leak` of `zseg`. -/
theorem stepsL_of_idx0_end (Q : LprogM) (z : String) (qseg : List LinstrRM)
    (hq : ∀ i ∈ qseg, QuietLopn i) :
    ∀ (zseg pre : List LinstrRM) (s u : LstateMF) (k : Nat), Q.body = pre ++ zseg ++ qseg →
      (∀ i ∈ zseg, Idx0Lopn z i) → atPc Q pre.length s →
      s.prog.base.reg.lvm z = ⟨64, 0#64⟩ → Steps x86Isa Q k s u →
      u.prog.base.lpc = pre.length + zseg.length + qseg.length →
      ∀ (P : LprogM) (post : List LinstrRM), P.lfn = Q.lfn →
        P.body = pre ++ zseg ++ qseg ++ post →
        StepsL P (zseg.length + qseg.length) s u (zseg.flatMap idx0Leak) := by
  intro zseg
  induction zseg with
  | nil =>
      intro pre s u k hQ _ hat _ hs hend P post hfn hP
      have h := stepsL_of_quiet_end Q qseg pre s u k (by rw [hQ, List.append_nil]) hq hat hs
        (by rw [hend, List.length_nil]; omega) P post hfn (by rw [hP, List.append_nil])
      rw [List.length_nil, Nat.zero_add]
      exact h
  | cons i zseg ih =>
      intro pre s u k hQ hz hat hz0 hs hend P post hfn hP
      cases k with
      | zero =>
          obtain rfl := steps_zero_iff.mp hs
          rw [hat.2, List.length_cons] at hend
          omega
      | succ k =>
          obtain ⟨i', w, hf, hw, hrest⟩ := steps_succ_iff.mp hs
          have hii : i' = i := by
            rw [findInstrMem_of_atPc hat, hQ, List.append_assoc,
              List.getElem?_append_right (le_refl _), Nat.sub_self] at hf
            exact (Option.some.inj hf).symm
          subst hii
          obtain ⟨hl, hleak, hkeep⟩ := hz i' (List.mem_cons_self ..)
          obtain ⟨hwfn, hwpc, hwP⟩ := lopn_step hl hw
          have hatw : atPc Q (pre ++ [i']).length w :=
            ⟨hwfn.trans hat.1, by rw [hwpc, hat.2, List.length_append, List.length_singleton]⟩
          have hrec := ih (pre ++ [i']) w u k
            (by rw [hQ]; simp only [List.append_assoc, List.cons_append, List.nil_append])
            (fun j hj => hz j (List.mem_cons_of_mem _ hj)) hatw
            (by rw [hkeep Q s w hw]; exact hz0) hrest
            (by rw [hend, List.length_append, List.length_singleton, List.length_cons]; omega)
            P post hfn
            (by rw [hP]; simp only [List.append_assoc, List.cons_append, List.nil_append])
          have hfP : findInstrMem P s.prog = some i' := by
            rw [findInstrMem_of_atPc (P := P) ⟨hat.1.trans hfn.symm, hat.2⟩, hP,
              List.append_assoc, List.append_assoc, List.getElem?_append_right (le_refl _),
              Nat.sub_self]
            rfl
          rw [show (i' :: zseg).length + qseg.length = (zseg.length + qseg.length) + 1 by
            rw [List.length_cons]; omega]
          refine ⟨steps_succ_iff.mpr ⟨i', w, hfP, hwP P, hrec.1⟩, ?_⟩
          rw [stepsLeak_succ hfP (hwP P), hrec.2, instrLeakF_of_lopn hl, hleak _ hz0,
            List.flatMap_cons]

/-- **A segment that sets the index register to zero, moves arrays and ends in quiet
    instructions, from the run of the program cut after it.** When the body of `P` is
    `pre ++ movImmI z 0 :: (zseg ++ qseg) ++ post`, a run of the program with the body
    `pre ++ movImmI z 0 :: (zseg ++ qseg)` from the counter `pre.length` to the counter
    after `qseg` is a traced run of `P` with the events `idx0Leak` of `zseg`. -/
theorem stepsL_of_idx0 {P : LprogM} {z : String} {zseg qseg pre post : List LinstrRM}
    {s u : LstateMF} {k : Nat}
    (hbody : P.body = pre ++ movImmI z 0 :: (zseg ++ qseg) ++ post)
    (hz : ∀ i ∈ zseg, Idx0Lopn z i) (hq : ∀ i ∈ qseg, QuietLopn i)
    (hat : atPc P pre.length s)
    (hs : Steps x86Isa (singletonProgM P.lfn (pre ++ movImmI z 0 :: (zseg ++ qseg))) k s u)
    (hend : u.prog.base.lpc = pre.length + 1 + zseg.length + qseg.length) :
    StepsL P (1 + (zseg.length + qseg.length)) s u (zseg.flatMap idx0Leak) := by
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = singletonProgM P.lfn (pre ++ movImmI z 0 :: (zseg ++ qseg)) :=
    ⟨_, rfl⟩
  rw [← hQd] at hs
  have hQb : Q.body = pre ++ movImmI z 0 :: (zseg ++ qseg) := by rw [hQd]; rfl
  have hQfn : Q.lfn = P.lfn := by rw [hQd]; rfl
  have hatQ : atPc Q pre.length s := ⟨hat.1.trans hQfn.symm, hat.2⟩
  have hfQ : Q.body[pre.length]? = some (movImmI z 0) := fetch_of_body hQb rfl
  cases k with
  | zero =>
      obtain rfl := steps_zero_iff.mp hs
      rw [hat.2] at hend
      omega
  | succ k =>
      obtain ⟨i', w, hf, hw, hrest⟩ := steps_succ_iff.mp hs
      have hii : i' = movImmI z 0 := by
        rw [findInstrMem_of_atPc hatQ, hfQ] at hf
        exact (Option.some.inj hf).symm
      subst hii
      obtain ⟨hl, hquiet⟩ := quietLopn_movImm z 0
      obtain ⟨hwfn, hwpc, hwP⟩ := lopn_step hl hw
      have hwz : w.prog.base.reg.lvm z = ⟨64, 0#64⟩ := by
        obtain ⟨t, ht, -, -, hlvm⟩ := steps_movImm (dst := z) (c := 0) hatQ hfQ
        obtain ⟨i'', t', hf', ht', h0⟩ := steps_succ_iff.mp ht
        obtain rfl := steps_zero_iff.mp h0
        rw [hf] at hf'
        obtain rfl := Option.some.inj hf'
        rw [hw] at ht'
        obtain rfl := Option.some.inj ht'
        rw [hlvm, if_pos rfl]
      have hrec := stepsL_of_idx0_end Q z qseg hq zseg (pre ++ [movImmI z 0]) w u k
        (by rw [hQb]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hz
        ⟨hwfn.trans hatQ.1, by
          rw [hwpc, hat.2, List.length_append, List.length_singleton]⟩
        hwz hrest (by rw [hend, List.length_append, List.length_singleton]) P post hQfn.symm
        (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
      have hfP : findInstrMem P s.prog = some (movImmI z 0) := by
        rw [findInstrMem_of_atPc hat]
        exact fetch_of_body (xs := pre) (by rw [hbody, List.append_assoc]; rfl) rfl
      have h1 : StepsL P 1 s w [] := by
        refine ⟨steps_succ_iff.mpr ⟨_, w, hfP, hwP P, Steps.refl x86Isa P w⟩, ?_⟩
        rw [stepsLeak_succ hfP (hwP P), instrLeakF_of_lopn hl, hquiet]
        rfl
      exact (h1.trans hrec).cast (List.nil_append _)

/-! ## 3. The machine events of an exported program -/

/-- **The machine events of a binding** at depth `d`: for a memory operation with a runtime
    index, the source events of the binding relabelled at the array name and the scale of
    its instruction (`siteOf`); for every other operation, none. -/
def bindLeak (Pj : JLeakParams) (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) (V : Ctxt.Valuation Γ) : List CTLeak :=
  if memOpB e.op then
    (Expr.ctLeak (jLeakModel Pj) e V).map
      (siteOf (opToLinstrR e.op (regName d) (exprArgs d nArgs argName (fun _ => none) e)))
  else []

/-- The run of trip `i` of a counted loop with trip count `N`: the run `bodyRun` of the
    body, the events `tailEv` of the assignment at the back edge, and the branch event of
    the back edge, which is taken when a trip remains. -/
def tripLeak {cs : List JasminTy} (tailEv : List CTLeak) (N : Nat)
    (bodyRun : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak))
    (i : Nat) (acc : Ctxt.Valuation (d := jasminDialect) cs) :
    Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak) :=
  (bodyRun i acc).map fun r =>
    (r.1, r.2 ++ (tailEv ++ [CTLeak.branch (decide (i + 1 < N))]))

/-- The events of the seeds of a counted loop at depth `d`: the events `idx0Leak` of the
    moves of the carried arrays from the initial operands, two address events at the
    source name and the offset `0` for each carried array. -/
def forHeadLeak (nArgs d : Nat) {Γ : Ctxt jasminDialect} {cs : List JasminTy}
    (inits : HVector (fun t => Ctxt.Var Γ t) cs) : List CTLeak :=
  (arrMoves (regName d) (regName (d + 1 + cs.length))
    (arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length)
      (exprArgsHV d nArgs argName (fun _ => none) inits)))).flatMap idx0Leak

/-- The events of the assignment at the back edge of a counted loop at depth `d` whose
    exported body is `b`: the events `idx0Leak` of the parallel assignment of the returned
    arrays to the carried block. -/
def forTailLeak (d : Nat) (cs : List JasminTy) (b : Exported) : List CTLeak :=
  (arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth
    (arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) b.res))).flatMap idx0Leak

/-- The events of the shift of the carried block of a counted loop at depth `d`: the events
    `idx0Leak` of the moves of the carried arrays down one name. -/
def forShiftLeak (d : Nat) (cs : List JasminTy) : List CTLeak :=
  (arrMoves (regName d) (regName (d + 1 + cs.length)) (arrPairs (shiftPairs d cs))).flatMap
    idx0Leak

/-- The seeds of a carried tuple of register types emit nothing. -/
theorem forHeadLeak_of_regTys (nArgs d : Nat) {Γ : Ctxt jasminDialect} {cs : List JasminTy}
    (hcs : RegTys cs) (inits : HVector (fun t => Ctxt.Var Γ t) cs) :
    forHeadLeak nArgs d inits = [] := by
  rw [forHeadLeak, arrPairs_carriedPairs hcs]
  rfl

/-- The assignment at the back edge of a carried tuple of register types emits nothing. -/
theorem forTailLeak_of_regTys (d : Nat) {cs : List JasminTy} (hcs : RegTys cs)
    (b : Exported) : forTailLeak d cs b = [] := by
  rw [forTailLeak, arrPairs_carriedPairs hcs]
  rfl

/-- The shift of a carried tuple of register types emits nothing. -/
theorem forShiftLeak_of_regTys (d : Nat) {cs : List JasminTy} (hcs : RegTys cs) :
    forShiftLeak d cs = [] := by
  rw [forShiftLeak, arrPairs_shiftPairs hcs]
  rfl

/-- The events of the assignment of the results of a branch arm exported as `b`, of the
    result types `rs`, to the block of the depth `d`: the events `idx0Leak` of the parallel
    assignment of the returned arrays in `ifResMoves`. -/
def ifResLeak (d : Nat) (rs : List JasminTy) (b : Exported) : List CTLeak :=
  (arrParMoves (regName (b.depth + rs.length + 1)) (regName (b.depth + rs.length))
    (b.depth + rs.length) (arrPairs (ifResPairs rs d b.res))).flatMap idx0Leak

/-- The assignment of branch results of register types emits nothing. -/
theorem ifResLeak_of_regTys (d : Nat) {rs : List JasminTy} (hrs : RegTys rs)
    (b : Exported) : ifResLeak d rs b = [] := by
  rw [ifResLeak, ifResPairs, arrPairs_carriedPairs hrs]
  rfl

/-- **The run of a program with the machine events of its export** in the function `fn`, at
    depth `d` and label `n`, from the valuation `V`; `fuel` bounds the runs of each
    exit-flag loop body. The labels and the array names of the frames are those of
    `exportR`, and the run returns `none` where the export of a region fails and at a
    call. -/
def machRun (Pj : JLeakParams) (nArgs : Nat) (fn : String) (fuel : Nat) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Nat → Nat →
    Ctxt.Valuation Γ → Option (Ctxt.Valuation (d := jasminDialect) ts × List CTLeak)
  | _, _, .ret vs, _, _, V => some (Expr.lookupArgs vs V, [])
  | _, _, .var e k, d, n, V =>
      (machRun Pj nArgs fn fuel k (d + 1) n (V.extend (e.denote V))).map fun r =>
        (r.1, bindLeak Pj nArgs e d V ++ r.2)
  | _, _, .forLoop (cs := cs) count inits body k, d, n, V =>
      (exportR nArgs fn body (d + 1 + cs.length) (n + 2)).bind fun b =>
      (forIterLeak
          (tripLeak (forTailLeak d cs b) (BitVec.toNat (count.lookup V)) fun i acc =>
            machRun Pj nArgs fn fuel body (d + 1 + cs.length) (n + 2)
              (hvAppend acc (.cons (BitVec.ofNat 64 i) V)))
          (List.range (BitVec.toNat (count.lookup V))) (Expr.lookupArgs inits V)).bind fun r =>
        (machRun Pj nArgs fn fuel k (d + cs.length) b.next (hvAppend r.1 V)).map fun q =>
          (q.1, forHeadLeak nArgs d inits
            ++ .branch (decide (BitVec.toNat (count.lookup V) = 0))
              :: (r.2 ++ (forShiftLeak d cs ++ q.2)))
  | _, _, .ifThenElse (rs := rs) cond thn els k, d, n, V =>
      (exportR nArgs fn thn d (n + 3)).bind fun t =>
      (exportR nArgs fn els d t.next).bind fun e =>
      (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V)
        then machRun Pj nArgs fn fuel thn d (n + 3) V
        else machRun Pj nArgs fn fuel els d t.next V).bind fun r =>
        (machRun Pj nArgs fn fuel k (d + rs.length) e.next (hvAppend r.1 V)).map fun q =>
          (q.1, .branch (!HasBoolBit.toBool (d := jasminDialect) (cond.lookup V))
            :: (r.2 ++ (ifResLeak d rs
              (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then t else e)
              ++ ((if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V)
                then [CTLeak.branch true] else []) ++ q.2))))
  | _, _, .whileLoop (cs := cs) inits body k, d, n, V =>
      (exportR nArgs fn body (d + cs.length) (n + 1)).bind fun b =>
      (whileIterLeak
          (fun acc => machRun Pj nArgs fn fuel body (d + cs.length) (n + 1) (hvAppend acc V))
          fuel (Expr.lookupArgs inits V)).bind fun r =>
        (machRun Pj nArgs fn fuel k (d + cs.length) b.next (hvAppend r.1 V)).map fun q =>
          (q.1, r.2 ++ q.2)
  | _, _, .call .., _, _, _ => none

/-- **The machine events of an exported program** in the function `fn`, at depth `d` and
    label `n`, from the valuation `V`. -/
def machLeak (Pj : JLeakParams) (nArgs : Nat) (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (d n : Nat)
    (V : Ctxt.Valuation Γ) : Option (List CTLeak) :=
  (machRun Pj nArgs fn fuel p d n V).map Prod.snd

/-- **The simulation statement of the region export with events.** The statement of
    `ExportRSim` on the x86 flag machine with the run `machRun` in place of the denotation:
    when `machRun` returns `v` with the events `ℓ` at `V`, the run of steps to the counter
    after the code is a traced run with the events `ℓ`. -/
def ExportRLeakSim (Pj : JLeakParams) (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) : Prop :=
  ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n = some r → Γ.length = d → nArgs ≤ d →
  ∀ (P : LprogM) (pre post : List LinstrRM), P.lfn = fn → P.body = pre ++ r.code ++ post →
    (∀ l, n ≤ l → findLabelMem l pre = none) →
  ∀ (fuel : Nat) (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (ℓ : List CTLeak) (m : LstateMF),
    machRun Pj nArgs fn fuel p d n V = some (v, ℓ) → atPc P pre.length m →
    StoreAgreesM nArgs d m.prog.base V →
    ∃ (k : Nat) (m' : LstateMF), StepsL P k m m' ℓ
      ∧ atPc P (pre.length + r.code.length) m'
      ∧ ResAgrees nArgs r.depth m'.prog.base r.res v
      ∧ RegionFrame d n m.prog.base m'.prog.base

/-! ## 4. The return and the binding -/

/-- **The rule of a return.** The code is empty and the run emits nothing. -/
theorem exportRLeakSim_ret (Pj : JLeakParams) (nArgs : Nat) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts) :
    ExportRLeakSim Pj nArgs fn (NFProg.ret (d := jasminDialect) vs) := by
  intro d n r h hlen _ P pre post _ _ _ fuel V v ℓ m hrun hat hag
  simp only [exportR, Option.some.injEq] at h
  subst h
  simp only [machRun, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  exact ⟨0, m, StepsL.refl P m, by simpa using hat,
    ⟨Γ, V, vs, hlen, hag, rfl, rfl⟩, RegionFrame.refl d n _⟩

/-- **The events of the instruction of a binding.** From a state that agrees with `V`, the
    instruction of a binding of the stack-memory fragment emits `bindLeak` at `V`. -/
theorem bindOps_leak (Pj : JLeakParams) {nArgs d : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {e : Expr jasminDialect Γ t} (he : BindMemN e) {st st' : LstateM}
    {V : Ctxt.Valuation Γ} {i : LinstrRM} (hlen : Γ.length = d) (harg : nArgs ≤ d)
    (hag : StoreAgreesM nArgs d st V) (hi : bindOps nArgs e d = [i])
    (hstep : lsemStepMem i st = some st') :
    instrLeakB st.reg i = bindLeak Pj nArgs e d V := by
  obtain ⟨w, v0, hmem⟩ := he
  have h := straightLeakF_straightOps Pj hmem hlen harg hag
  have hops : straightOpsMem nArgs (Com.var e (Com.ret v0)) d = [i] := hi
  rw [hops, straightLeakF_cons_of_step hstep, comCtLeak_var] at h
  have hret : Com.ctLeak (jLeakModel Pj) (Com.ret v0) (V.extend (e.denote V)) = [] := rfl
  rw [hret, straightT_var Pj nArgs d e (Com.ret v0) [] (exprCtLeak_length Pj e V)] at h
  simpa [straightLeakF, straightT, bindLeak] using h

/-- **The rule of a binding.** The statement for the continuation gives the statement for
    a binding of the stack-memory fragment in front of it, with the events of the binding
    in front of the events of the continuation. -/
theorem exportRLeakSim_var (Pj : JLeakParams) (nArgs : Nat) (fn : String)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy} (e : Expr jasminDialect Γ t)
    (k : NFProg jasminDialect (t :: Γ) ts) (he : BindMemN e)
    (hk : ExportRLeakSim Pj nArgs fn k) : ExportRLeakSim Pj nArgs fn (NFProg.var e k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V v ℓ m hrun hat hag
  simp only [exportR, Option.map_eq_some_iff] at h
  obtain ⟨rk, hrk, rfl⟩ := h
  simp only [machRun, Option.map_eq_some_iff, Prod.mk.injEq] at hrun
  obtain ⟨⟨v', ℓk⟩, hkrun, rfl, rfl⟩ := hrun
  have he' := he
  obtain ⟨w, v0, hmem⟩ := he
  obtain ⟨st', hrun, hAg, hFr⟩ :=
    lsemStraightMem_straightOps_store (nArgs := nArgs) hmem hlen harg hag
  have hplain : PlainLopnBody (bindOps nArgs e d) :=
    straightOpsMem_plain nArgs _ (scalarMemN_comOpsPlain hmem) d
  obtain ⟨i, hi⟩ := bindOps_eq_singleton nArgs e d
  have hrun' : lsemStraightMem [i] m.prog.base = some st' := hi ▸ hrun
  have hstep : lsemStepMem i m.prog.base = some st' := by
    rw [lsemStraightMem_cons] at hrun'
    cases hs : lsemStepMem i m.prog.base with
    | none => rw [hs] at hrun'; cases hrun'
    | some b => rw [hs] at hrun'; exact hrun'
  obtain ⟨hl, hc, hm⟩ := hplain i (by rw [hi]; exact List.mem_singleton_self i)
  have hcode : (Exported.prepend (bindOps nArgs e d) rk).code = i :: rk.code := by
    simp only [Exported.prepend, hi, List.singleton_append]
  rw [hcode] at hbody
  have hfetch : P.body[pre.length]? = some i := by
    rw [hbody, List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  obtain ⟨hs1, hat1⟩ := x86_steps_mem hat hfetch hl hc hm hstep
  have hL1 : StepsL P 1 m (setBase m (withALUFlags i m.prog.base st'))
      (bindLeak Pj nArgs e d V) :=
    (stepsL_one hat hfetch hs1).cast (by
      rw [instrLeakF_of_lopn hl, bindOps_leak Pj he' hlen harg hag hi hstep])
  have hAg' : StoreAgreesM nArgs (d + 1) st' (V.extend (e.denote V)) := hAg
  have hlab : ∀ l, n ≤ l → findLabelMem l (pre ++ [i]) = none := by
    intro l hl'
    rw [findLabelMem_eq_none_iff, labelsOf_append,
      labelsOf_of_isLopn (xs := [i]) (fun j hj => by
        rw [List.mem_singleton.mp hj]; exact hl),
      List.append_nil, ← findLabelMem_eq_none_iff]
    exact hpre l hl'
  obtain ⟨k', m', hs2, hat2, hres, hfr2⟩ := hk (d + 1) n rk hrk
    (by rw [List.length_cons, hlen]) (by omega) P (pre ++ [i]) post hfn
    (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hlab
    fuel _ v' ℓk (setBase m (withALUFlags i m.prog.base st')) hkrun
    (by rw [List.length_append, List.length_singleton]; exact hat1)
    (StoreAgreesM.withALUFlags i m.prog.base hAg')
  refine ⟨1 + k', m', hL1.trans hs2, ?_, hres, ?_⟩
  · rw [hcode, List.length_cons]
    rw [List.length_append, List.length_singleton] at hat2
    rwa [show pre.length + (rk.code.length + 1) = pre.length + 1 + rk.code.length by omega]
  · exact ((RegionFrame.of_writeFrame n hFr).withALUFlags i _).trans hfr2 (by omega) le_rfl

/-! ## 5. The straight segments of a counted loop -/

/-- **The head of a counted loop, with its events.** The run of `forArrHead_steps` is a
    traced run with the events of the moves of the carried arrays at the index zero. -/
theorem forArrHead_stepsL {P : LprogM} {d n : Nat} {cs : Ctxt jasminDialect}
    {ops : List LOperand} {cn : String} {tp : List (JasminTy × String × String)}
    (htp : tp = carriedPairs cs (carriedRegs (d + 1) cs.length) ops)
    (pre post : List LinstrRM) (s : LstateMF) {cnt : BitVec 64}
    (hbody : P.body = pre ++ movImmI (regName d) 0
        :: typedMoves (regName d) (regName (d + 1 + cs.length)) tp
      ++ (movI (loopCtr n) (.reg cn)
        :: guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])
        :: post))
    (hat : atPc P pre.length s) (hlen : ops.length = cs.length)
    (hops : ∀ o ∈ ops, ∀ k, d ≤ k → operandName o ≠ regName k)
    (hcn : ∀ k, d ≤ k → cn ≠ regName k) (hcnt : s.prog.base.reg.lvm cn = ⟨64, cnt⟩)
    (hsrc : ∀ {w m : Nat} (v : Ctxt.Var cs (.stackArr w m)), ∃ arr : Fin m → BitVec w,
      s.prog.base.getArr (operandName (ops.getD (varIndex v) (.imm 0))) w m = some arr) :
    ∃ (k : Nat) (u : LstateMF), StepsL P k s u
        ((arrMoves (regName d) (regName (d + 1 + cs.length)) (arrPairs tp)).flatMap idx0Leak)
      ∧ atPc P ((pre ++ movImmI (regName d) 0
          :: typedMoves (regName d) (regName (d + 1 + cs.length)) tp).length + 2) u
      ∧ u.zf = (cnt == 0#64)
      ∧ u.prog.base.reg.lvm (regName d) = ⟨64, 0#64⟩
      ∧ u.prog.base.reg.lvm (loopCtr n) = ⟨64, cnt⟩
      ∧ (∀ {w : Nat} (v : Ctxt.Var cs (.reg w)),
          u.prog.base.reg.lvm (regName (d + 1 + (cs.length - 1 - varIndex v)))
            = s.prog.base.reg.lvm (operandName (ops.getD (varIndex v) (.imm 0))))
      ∧ (∀ {w m : Nat} (v : Ctxt.Var cs (.stackArr w m)),
          u.prog.base.larr (regName (d + 1 + (cs.length - 1 - varIndex v)))
            = s.prog.base.larr (operandName (ops.getD (varIndex v) (.imm 0))))
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) → r ≠ loopCtr n →
          u.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) → u.prog.base.larr r = s.prog.base.larr r) := by
  have hzt : regName d ≠ regName (d + 1 + cs.length) := fun he => by
    have := JasminLsemSimulation.regName_injective he
    omega
  obtain ⟨zseg, hzseg⟩ : ∃ zseg, zseg
      = arrMoves (regName d) (regName (d + 1 + cs.length)) (arrPairs tp) := ⟨_, rfl⟩
  obtain ⟨qseg, hqseg⟩ : ∃ qseg, qseg = regMoves (regPairs tp)
    ++ [movI (loopCtr n) (.reg cn),
      guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])] :=
    ⟨_, rfl⟩
  have hq : ∀ i ∈ qseg, QuietLopn i := by
    intro i hi
    rw [hqseg] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | rfl | rfl
    · exact quietLopn_regMoves _ i hi
    · exact quietLopn_movReg _ _
    · exact quietLopn_cmp _
  have hbP : P.body = pre ++ movImmI (regName d) 0 :: (zseg ++ qseg) ++ post := by
    rw [hbody, hzseg, hqseg]
    simp only [typedMoves, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨k, u, hs, hat', rest⟩ := forArrHead_steps
    (P := singletonProgM P.lfn (pre ++ movImmI (regName d) 0 :: (zseg ++ qseg)))
    (d := d) (n := n) htp pre [] s (cnt := cnt)
    (by
      show pre ++ movImmI (regName d) 0 :: (zseg ++ qseg) = _
      rw [hzseg, hqseg]
      simp only [typedMoves, List.append_assoc, List.cons_append])
    hat hlen hops hcn hcnt hsrc
  have hL := stepsL_of_idx0 hbP (by rw [hzseg]; exact idx0Lopn_arrMoves hzt _) hq hat hs
    (by
      rw [hat'.2, hzseg, hqseg]
      simp only [typedMoves, List.length_append, List.length_cons, List.length_nil]
      omega)
  exact ⟨_, u, hL.cast (by rw [hzseg]), ⟨hat'.1, hat'.2⟩, rest.2⟩

/-- **The tail of a counted trip, with its events.** The run of `forArrTail_steps` is a
    traced run with the events of the parallel assignment of the returned arrays at the
    index zero. -/
theorem forArrTail_stepsL {P : LprogM} {d n bD : Nat} {cs : Ctxt jasminDialect}
    {ops : List LOperand} {tp : List (JasminTy × String × String)}
    (htp : tp = carriedPairs cs (carriedRegs (d + 1) cs.length) ops)
    (pre post : List LinstrRM) (s : LstateMF) {x c : BitVec 64}
    (hbody : P.body = pre ++ movImmI (regName (bD + 1)) 0
        :: arrParMoves (regName (bD + 1)) (regName bD) bD (arrPairs tp)
      ++ parMoves bD ((regPairs tp).map Prod.fst) ((regPairs tp).map fun p => .reg p.2)
      ++ (advanceOps (regName d) (loopCtr n)
      ++ guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])
        :: post))
    (hat : atPc P pre.length s) (hlen : ops.length = cs.length) (hD : d + 1 + cs.length ≤ bD)
    (hops : ∀ o ∈ ops, ∀ k, bD ≤ k → operandName o ≠ regName k)
    (hx : s.prog.base.reg.lvm (regName d) = ⟨64, x⟩)
    (hc : s.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩)
    (hsrc : ∀ {w m : Nat} (v : Ctxt.Var cs (.stackArr w m)), ∃ arr : Fin m → BitVec w,
      s.prog.base.getArr (operandName (ops.getD (varIndex v) (.imm 0))) w m = some arr) :
    ∃ (k : Nat) (u : LstateMF), StepsL P k s u
        ((arrParMoves (regName (bD + 1)) (regName bD) bD (arrPairs tp)).flatMap idx0Leak)
      ∧ atPc P ((pre ++ movImmI (regName (bD + 1)) 0
            :: arrParMoves (regName (bD + 1)) (regName bD) bD (arrPairs tp)
          ++ parMoves bD ((regPairs tp).map Prod.fst)
            ((regPairs tp).map fun p => .reg p.2)).length + 3) u
      ∧ u.zf = (c - 1#64 == 0#64)
      ∧ u.prog.base.reg.lvm (regName d) = ⟨64, x + 1#64⟩
      ∧ u.prog.base.reg.lvm (loopCtr n) = ⟨64, c - 1#64⟩
      ∧ (∀ {w : Nat} (v : Ctxt.Var cs (.reg w)),
          u.prog.base.reg.lvm (regName (d + 1 + (cs.length - 1 - varIndex v)))
            = s.prog.base.reg.lvm (operandName (ops.getD (varIndex v) (.imm 0))))
      ∧ (∀ {w m : Nat} (v : Ctxt.Var cs (.stackArr w m)),
          u.prog.base.larr (regName (d + 1 + (cs.length - 1 - varIndex v)))
            = s.prog.base.larr (operandName (ops.getD (varIndex v) (.imm 0))))
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) → r ≠ loopCtr n →
          u.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) → u.prog.base.larr r = s.prog.base.larr r) := by
  have hzt : regName (bD + 1) ≠ regName bD := fun he => by
    have := JasminLsemSimulation.regName_injective he
    omega
  obtain ⟨zseg, hzseg⟩ : ∃ zseg, zseg
      = arrParMoves (regName (bD + 1)) (regName bD) bD (arrPairs tp) := ⟨_, rfl⟩
  obtain ⟨qseg, hqseg⟩ : ∃ qseg, qseg
      = parMoves bD ((regPairs tp).map Prod.fst) ((regPairs tp).map fun p => .reg p.2)
      ++ (advanceOps (regName d) (loopCtr n)
      ++ [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
        [.reg (loopCtr n), .imm 0])]) := ⟨_, rfl⟩
  have hq : ∀ i ∈ qseg, QuietLopn i := by
    intro i hi
    rw [hqseg] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | rfl
    · refine quietLopn_parMoves _ _ _ (fun o ho => ?_) i hi
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
      exact ⟨_, rfl⟩
    · exact quietLopn_advanceOps _ _ i hi
    · exact quietLopn_cmp _
  have hbP : P.body = pre ++ movImmI (regName (bD + 1)) 0 :: (zseg ++ qseg) ++ post := by
    rw [hbody, hzseg, hqseg]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨k, u, hs, hat', rest⟩ := forArrTail_steps
    (P := singletonProgM P.lfn (pre ++ movImmI (regName (bD + 1)) 0 :: (zseg ++ qseg)))
    (d := d) (n := n) (bD := bD) htp pre [] s (x := x) (c := c)
    (by
      show pre ++ movImmI (regName (bD + 1)) 0 :: (zseg ++ qseg) = _
      rw [hzseg, hqseg]
      simp only [List.append_assoc, List.cons_append])
    hat hlen hD hops hx hc hsrc
  have hL := stepsL_of_idx0 hbP (by rw [hzseg]; exact idx0Lopn_arrParMoves hzt _ _) hq hat hs
    (by
      rw [hat'.2, hzseg, hqseg]
      simp only [List.length_append, List.length_cons, List.length_nil, advanceOps]
      omega)
  exact ⟨_, u, hL.cast (by rw [hzseg]), ⟨hat'.1, hat'.2⟩, rest.2⟩

/-- **The shift of a carried block, with its events.** The run of `forArrShift_steps` is a
    traced run with the events `forShiftLeak` of the moves of the carried arrays. -/
theorem forArrShift_stepsL {P : LprogM} {d : Nat} {cs : Ctxt jasminDialect}
    (pre post : List LinstrRM) (s : LstateMF)
    (hbody : P.body = pre ++ movImmI (regName d) 0
      :: (typedMoves (regName d) (regName (d + 1 + cs.length)) (shiftPairs d cs) ++ post))
    (hat : atPc P pre.length s)
    (hsrc : ∀ {w n : Nat} (v : Ctxt.Var cs (.stackArr w n)), ∃ arr : Fin n → BitVec w,
      s.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex v))) w n = some arr) :
    ∃ (k : Nat) (u : LstateMF), StepsL P k s u (forShiftLeak d cs)
      ∧ atPc P (pre.length + 1 + (typedMoves (regName d) (regName (d + 1 + cs.length))
          (shiftPairs d cs)).length) u
      ∧ (∀ {w : Nat} (v : Ctxt.Var cs (.reg w)),
          u.prog.base.reg.lvm (regName (d + (cs.length - 1 - varIndex v)))
            = s.prog.base.reg.lvm (regName (d + 1 + (cs.length - 1 - varIndex v))))
      ∧ (∀ {w n : Nat} (v : Ctxt.Var cs (.stackArr w n)),
          u.prog.base.larr (regName (d + (cs.length - 1 - varIndex v)))
            = s.prog.base.larr (regName (d + 1 + (cs.length - 1 - varIndex v))))
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) → u.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) → u.prog.base.larr r = s.prog.base.larr r) := by
  have hzt : regName d ≠ regName (d + 1 + cs.length) := fun he => by
    have := JasminLsemSimulation.regName_injective he
    omega
  obtain ⟨zseg, hzseg⟩ : ∃ zseg, zseg
      = arrMoves (regName d) (regName (d + 1 + cs.length)) (arrPairs (shiftPairs d cs)) :=
    ⟨_, rfl⟩
  obtain ⟨qseg, hqseg⟩ : ∃ qseg, qseg = regMoves (regPairs (shiftPairs d cs)) := ⟨_, rfl⟩
  have hbP : P.body = pre ++ movImmI (regName d) 0 :: (zseg ++ qseg) ++ post := by
    rw [hbody, hzseg, hqseg]
    simp only [typedMoves, List.append_assoc, List.cons_append]
  obtain ⟨u, hs, hat', rest⟩ := forArrShift_steps
    (P := singletonProgM P.lfn (pre ++ movImmI (regName d) 0 :: (zseg ++ qseg)))
    (d := d) (cs := cs) pre [] s
    (by
      show pre ++ movImmI (regName d) 0 :: (zseg ++ qseg) = _
      rw [hzseg, hqseg, List.append_nil]
      rfl)
    hat hsrc
  have hL := stepsL_of_idx0 hbP (by rw [hzseg]; exact idx0Lopn_arrMoves hzt _)
    (by rw [hqseg]; exact quietLopn_regMoves _) hat hs
    (by
      rw [hat'.2, hzseg, hqseg]
      simp only [typedMoves, List.length_append]
      omega)
  exact ⟨_, u, hL.cast (by rw [hzseg]; rfl), ⟨hat'.1, hat'.2⟩, rest⟩

/-! ## 6. The trips of a counted loop -/

/-- The run of the iterations `i :: is` is a first iteration followed by the run of
    `is`. -/
theorem forIterLeak_cons_eq_some {cs : List JasminTy}
    {step : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)}
    {i : Nat} {is : List Nat} {acc a : Ctxt.Valuation (d := jasminDialect) cs}
    {ℓ : List CTLeak} :
    forIterLeak step (i :: is) acc = some (a, ℓ) ↔
      ∃ a1 ℓ1 ℓ2, step i acc = some (a1, ℓ1) ∧ forIterLeak step is a1 = some (a, ℓ2)
        ∧ ℓ = ℓ1 ++ ℓ2 := by
  simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq,
    Prod.exists]
  constructor
  · rintro ⟨a1, ℓ1, h1, a2, ℓ2, h2, rfl, rfl⟩
    exact ⟨a1, ℓ1, ℓ2, h1, h2, rfl⟩
  · rintro ⟨a1, ℓ1, ℓ2, h1, h2, rfl⟩
    exact ⟨a1, ℓ1, h1, a, ℓ2, h2, rfl, rfl⟩

/-- A trip returns the tuple of the body with the events of the body followed by the
    events of the assignment at the back edge and the branch event of the back edge. -/
theorem tripLeak_eq_some {cs : List JasminTy} {E : List CTLeak} {N : Nat}
    {bodyRun : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)}
    {i : Nat} {acc a : Ctxt.Valuation (d := jasminDialect) cs} {ℓ : List CTLeak} :
    tripLeak E N bodyRun i acc = some (a, ℓ) ↔
      ∃ ℓb, bodyRun i acc = some (a, ℓb)
        ∧ ℓ = ℓb ++ (E ++ [CTLeak.branch (decide (i + 1 < N))]) := by
  simp only [tripLeak, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨a1, ℓb, h, rfl, rfl⟩
    exact ⟨ℓb, h, rfl⟩
  · rintro ⟨ℓb, h, rfl⟩
    exact ⟨a, ℓb, h, rfl, rfl⟩

section ForRegLoop

variable (Pj : JLeakParams) (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
  (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
  (hsim : ExportRLeakSim Pj nArgs fn body) {d n : Nat} {b : Exported}
  (hb : exportR nArgs fn body (d + 1 + cs.length) (n + 2) = some b) (hlen : Γ.length = d)
  (harg : nArgs ≤ d) {P : LprogM} {A R T Z : List LinstrRM} (hfn : P.lfn = fn)
  {tp : List (JasminTy × String × String)}
  (htp : tp = carriedPairs cs (carriedRegs (d + 1) cs.length) b.res)
  (hT : T = movImmI (regName (b.depth + 1)) 0
      :: arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth (arrPairs tp)
    ++ parMoves b.depth ((regPairs tp).map Prod.fst) ((regPairs tp).map fun p => .reg p.2))
  (hbody : P.body = A ++ labelI n :: (b.code ++ R))
  (hR : R = T ++ (advanceOps (regName d) (loopCtr n)
    ++ guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])
      :: condI (.reg "NZ") n :: Z))
  (hA : ∀ l, n ≤ l → findLabelMem l A = none) (fuel : Nat) (V : Ctxt.Valuation Γ)

include hsim hb hlen harg hfn htp hT hbody hR hA in
/-- **One trip of a counted loop, with its events**, from the counter after the top label
    to the back-edge jump: the events of the body, then those of the assignment of the
    returned arrays. -/
theorem forArrLoop_tripL (i : Nat) (acc acc1 : Ctxt.Valuation cs) (ℓ : List CTLeak)
    (m : LstateMF) (c : BitVec 64)
    (hden : machRun Pj nArgs fn fuel body (d + 1 + cs.length) (n + 2) (hvAppend acc
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ)))
        = some (acc1, ℓ))
    (hat : atPc P (A.length + 1) m) (hag : StoreAgreesM nArgs d m.prog.base V)
    (hidx : m.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i⟩)
    (hctr : m.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩)
    (hblk : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc))
    (hblkA : ∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
      m.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
        = some (u.lookup acc)) :
    ∃ (k : Nat) (t : LstateMF), StepsL P k m t (ℓ ++
          (arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth
            (arrPairs tp)).flatMap idx0Leak)
      ∧ atPc P (A.length + 1 + b.code.length + T.length + 3) t
      ∧ RegionFrame d n m.prog.base t.prog.base ∧ t.zf = (c - 1#64 == 0#64)
      ∧ t.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i + 1#64⟩
      ∧ t.prog.base.reg.lvm (loopCtr n) = ⟨64, c - 1#64⟩
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          t.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup acc1))
      ∧ (∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
          t.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
            = some (u.lookup acc1)) := by
  have hag1 : StoreAgreesM nArgs (d + 1) m.prog.base
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ)) :=
    storeAgreesM_append (cs := [JasminTy.reg 64])
      (acc := (HVector.cons (BitVec.ofNat 64 i) HVector.nil :
        Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 64]))
      (fun t ht => by rw [List.mem_singleton.mp ht]; rfl) harg hag
      (fun {w} u => by
        cases u with
        | here => exact getW_of_lvm _ _ _ hidx
        | there u => cases u)
  have hag2 : StoreAgreesM nArgs (d + 1 + cs.length) m.prog.base (hvAppend acc
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ))) :=
    storeAgreesM_append_arr (by omega) hag1 hblk hblkA
  have hbd := exportR_depth_le nArgs fn body _ _ _ hb
  obtain ⟨k1, m1, hs1, hat1, ⟨Δ, W, vs, hΔ, hagW, hops, hacc⟩, hfr1⟩ :=
    hsim (d + 1 + cs.length) (n + 2) b hb
      (by simp only [List.length_append, List.length_cons, hlen]; omega) (by omega) P
      (A ++ [labelI n]) R hfn
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
      (fun l hl => by
        rw [findLabelMem_eq_none_iff, labelsOf_append]
        simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
          not_or]
        exact ⟨(findLabelMem_eq_none_iff l A).mp (hA l (by omega)),
          fun he => by have : (l : Nat) = n := he; omega⟩)
      fuel _ acc1 ℓ m hden
      (by rw [List.length_append, List.length_singleton]; exact hat) hag2
  have hres_len : b.res.length = cs.length := by rw [hops, exprArgsHV_length]
  have hat1' : atPc P (A ++ labelI n :: b.code).length m1 := by
    rw [List.length_append, List.length_singleton] at hat1
    rw [List.length_append, List.length_cons]
    rwa [show A.length + (b.code.length + 1) = A.length + 1 + b.code.length by omega]
  obtain ⟨k2, t, hs2, hat2, hz, hidx', hctr', hR', hA', hothR, hothA⟩ :=
    forArrTail_stepsL (d := d) (n := n) (bD := b.depth) (ops := b.res) htp
      (A ++ labelI n :: b.code) (condI (.reg "NZ") n :: Z) m1 (x := BitVec.ofNat 64 i) (c := c)
      (by rw [hbody, hR, hT]; simp only [List.append_assoc, List.cons_append]) hat1' hres_len hbd
      (by rw [hops]; exact fun o ho => (exprArgsHV_reg nArgs hΔ vs o ho).2)
      (by
        rw [hfr1.lvm_eq _
          (fun k hk he => by have := JasminLsemSimulation.regName_injective he; omega)
          (fun l _ he => loopCtr_ne_regName l d he.symm)]
        exact hidx)
      (by
        rw [hfr1.lvm_eq _ (fun k _ => loopCtr_ne_regName n k)
          (fun l hl he => by have := loopCtr_injective he; omega)]
        exact hctr)
      (fun {w q} u => ⟨_, by rw [hops, exprArgsHV_getD]; exact hagW.2 (hvToHom vs u)⟩)
  refine ⟨k1 + k2, t, hs1.trans hs2, ?_, ?_, hz, hidx', hctr',
    fun {w} u => ?_,
    fun {w q} u => ?_⟩
  · rw [hT]
    simp only [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] at hat2 ⊢
    exact hat2
  · exact (hfr1.mono (by omega) (by omega)).trans
      (RegionFrame.of_lvm_larr (fun r hr hl => hothR r hr (hl n le_rfl)) hothA) le_rfl le_rfl
  · rw [getW_of_lvm_eq w (hR' u), hops, exprArgsHV_getD,
      ← evalOperandN_resolveVar, hacc, lookup_lookupArgs]
    exact hagW.1 (hvToHom vs u)
  · rw [getArr_of_larr_eq w q (hA' u), hops, exprArgsHV_getD, hacc, lookup_lookupArgs]
    exact hagW.2 (hvToHom vs u)

include hsim hb hlen harg hfn htp hT hbody hR hA in
/-- **The trips of a counted loop, with their events.** From the counter after the top
    label with `rem + 1` trips left of `N`, the run to the counter after the back-edge jump
    emits, for each trip, the events of the body, those of the assignment of the returned
    arrays, and the branch event of the back edge. -/
theorem forArrLoop_tripsL (N : Nat) : ∀ (rem i : Nat) (acc accN : Ctxt.Valuation cs)
    (ℓ : List CTLeak) (m : LstateMF) (c : BitVec 64),
    forIterLeak (tripLeak ((arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth
        (arrPairs tp)).flatMap idx0Leak) N fun j a =>
      machRun Pj nArgs fn fuel body (d + 1 + cs.length) (n + 2) (hvAppend a
        (HVector.cons (BitVec.ofNat 64 j) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ))))
      (List.range' i (rem + 1)) acc = some (accN, ℓ) →
    N = i + rem + 1 →
    c.toNat = rem + 1 → atPc P (A.length + 1) m → StoreAgreesM nArgs d m.prog.base V →
    m.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i⟩ →
    m.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩ →
    (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) →
    (∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
      m.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
        = some (u.lookup acc)) →
    ∃ (k : Nat) (m' : LstateMF), StepsL P k m m' ℓ
      ∧ atPc P (A.length + 1 + b.code.length + T.length + 3 + 1) m'
      ∧ RegionFrame d n m.prog.base m'.prog.base
      ∧ (∃ x : BitVec 64, m'.prog.base.reg.lvm (regName d) = ⟨64, x⟩)
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          m'.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN))
      ∧ (∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
          m'.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
            = some (u.lookup accN)) := by
  have hcc : flagCondCC? (condI (.reg "NZ") n) = some (false, n) := rfl
  have hfetch : P.body[A.length + 1 + b.code.length + T.length + 3]?
      = some (condI (.reg "NZ") n) :=
    fetch_of_body (xs := A ++ labelI n :: (b.code ++ (T ++ (advanceOps (regName d) (loopCtr n)
        ++ [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
          [.reg (loopCtr n), .imm 0])]))))
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by
        simp only [List.length_append, List.length_cons, advanceOps, List.length_nil]
        omega)
  intro rem
  induction rem with
  | zero =>
      intro i acc accN ℓ m c hfold hN hc hat hag hidx hctr hblk hblkA
      rw [List.range'_succ] at hfold
      obtain ⟨acc1, ℓ1, ℓ2, hstep, hrest, rfl⟩ := forIterLeak_cons_eq_some.mp hfold
      rw [List.range'_zero] at hrest
      simp only [forIterLeak, Option.some.injEq, Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      obtain ⟨ℓb, hden, rfl⟩ := tripLeak_eq_some.mp hstep
      obtain ⟨k, t, hs, hat2, hfr, hz, hidx', _, hblk', hblkA'⟩ :=
        forArrLoop_tripL Pj nArgs fn body hsim hb hlen harg hfn htp hT hbody hR hA fuel V i
          acc acc1 ℓb m c hden hat hag hidx hctr hblk hblkA
      have hc1 : c - 1#64 = 0#64 := by bv_omega
      obtain ⟨hs', hat'⟩ := steps_cc_fall hcc hat2 hfetch (by rw [hz, hc1]; decide)
      have hev : (t.zf == false) = decide (i + 1 < N) := by
        rw [hz, hc1, hN]
        simp
      exact ⟨k + 1, next t,
        (hs.trans (stepsL_cc hcc hat2 hfetch hs')).cast (by
          rw [hev]
          simp only [List.append_assoc, List.append_nil]),
        hat', hfr, ⟨_, hidx'⟩, fun {w} u => hblk' u, fun {w q} u => hblkA' u⟩
  | succ rem ih =>
      intro i acc accN ℓ m c hfold hN hc hat hag hidx hctr hblk hblkA
      rw [List.range'_succ] at hfold
      obtain ⟨acc1, ℓ1, ℓ2, hstep, hrest, rfl⟩ := forIterLeak_cons_eq_some.mp hfold
      obtain ⟨ℓb, hden, rfl⟩ := tripLeak_eq_some.mp hstep
      obtain ⟨k, t, hs, hat2, hfr, hz, hidx', hctr', hblk', hblkA'⟩ :=
        forArrLoop_tripL Pj nArgs fn body hsim hb hlen harg hfn htp hT hbody hR hA fuel V i
          acc acc1 ℓb m c hden hat hag hidx hctr hblk hblkA
      have hc1 : c - 1#64 ≠ 0#64 := by bv_omega
      have hl : findLabelMem n P.body = some A.length := by
        rw [hbody]
        exact findLabelMem_append_labelI n A _ ((findLabelMem_eq_none_iff n A).mp (hA n le_rfl))
      obtain ⟨hs', hat'⟩ := steps_cc_taken hcc hat2 hfetch (by rw [hz]; simpa using hc1) hl
      have hev : (t.zf == false) = decide (i + 1 < N) := by
        rw [hz, hN]
        simp [hc1]
      have hfr' : RegionFrame d n m.prog.base (goto t (A.length + 1)).prog.base :=
        hfr.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      obtain ⟨k', m', hs'', hat'', hfr'', hx'', hblk'', hblkA''⟩ := ih (i + 1) acc1 accN ℓ2
        (goto t (A.length + 1)) (c - 1#64) hrest (by omega) (by bv_omega) hat'
        (StoreAgreesM.of_regionFrame hlen hag hfr')
        (by rw [BitVec.ofNat_add]; exact hidx') hctr' (fun {w} u => hblk' u)
        (fun {w q} u => hblkA' u)
      exact ⟨k + 1 + k', m',
        ((hs.trans (stepsL_cc hcc hat2 hfetch hs')).trans hs'').cast (by
          rw [hev]
          simp only [List.append_assoc]),
        hat'', hfr'.trans hfr'' le_rfl le_rfl, hx'', fun {w} u => hblk'' u,
        fun {w q} u => hblkA'' u⟩

end ForRegLoop

/-! ## 7. The rule of a counted loop -/

/-- **The rule of a counted loop.** The statements for the body and for the continuation
    give the statement for the loop: the run emits the events of the seeds of the carried
    arrays, the branch event of the zero-trip guard, the events of the trips, the events of
    the shift of the carried arrays, and the events of the continuation. -/
theorem exportRLeakSim_for (Pj : JLeakParams) (nArgs : Nat) (fn : String)
    {Γ cs : Ctxt jasminDialect} {ts : List JasminTy} (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts)
    (hbsim : ExportRLeakSim Pj nArgs fn body) (hksim : ExportRLeakSim Pj nArgs fn k) :
    ExportRLeakSim Pj nArgs fn (NFProg.forLoop count inits body k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V v ℓ m hrun hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rk, hrk, rfl⟩ := h
  obtain ⟨cnt, hcd⟩ : ∃ cnt : BitVec 64, count.lookup V = cnt := ⟨_, rfl⟩
  simp only [machRun, hb, Option.bind_some] at hrun
  rw [hcd] at hrun
  obtain ⟨⟨accN, ℓr⟩, hiter, hkrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨⟨v', ℓk⟩, hkden, heq⟩ := Option.map_eq_some_iff.mp hkrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hbody0 := hbody
  have hLab := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ _ hb
  -- the count and the seeds
  obtain ⟨cn, hcn⟩ : ∃ cn, cn = operandName (resolveVar d nArgs argName (fun _ => none) count) :=
    ⟨_, rfl⟩
  have hcreg : resolveVar d nArgs argName (fun _ => none) count = .reg cn := by
    rw [hcn]
    exact resolveVar_isReg count
  have hcnt : m.prog.base.reg.lvm cn = ⟨64, cnt⟩ := by
    have := hag.1 count
    rw [evalOperandN_resolveVar, ← hcn, hcd] at this
    exact getW_eq_some_iff.mp this
  have hcnk : ∀ k, d ≤ k → cn ≠ regName k := fun k hk => by
    rw [hcn]
    exact resolveVar_operandName_ne_regName count
      (hlen ▸ JasminLsemSimulation.varIndex_lt count) k hk
  obtain ⟨ops, hops⟩ : ∃ ops, ops = exprArgsHV d nArgs argName (fun _ => none) inits := ⟨_, rfl⟩
  have hopslen : ops.length = cs.length := by rw [hops, exprArgsHV_length]
  have hopsreg : ∀ o ∈ ops, ∀ k, d ≤ k → operandName o ≠ regName k := by
    rw [hops]
    exact fun o ho => (exprArgsHV_reg nArgs hlen inits o ho).2
  -- the layout of the body
  obtain ⟨cmp, hcmp⟩ : ∃ cmp, cmp = guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
      [.reg (loopCtr n), .imm 0]) := ⟨_, rfl⟩
  obtain ⟨tpI, htpI⟩ : ∃ tpI, tpI = carriedPairs cs (carriedRegs (d + 1) cs.length) ops :=
    ⟨_, rfl⟩
  obtain ⟨tpB, htpB⟩ : ∃ tpB, tpB = carriedPairs cs (carriedRegs (d + 1) cs.length) b.res :=
    ⟨_, rfl⟩
  have hHL : forHeadLeak nArgs d inits = (arrMoves (regName d) (regName (d + 1 + cs.length))
      (arrPairs tpI)).flatMap idx0Leak := by
    rw [htpI, hops]
    rfl
  have hTL : forTailLeak d cs b = (arrParMoves (regName (b.depth + 1)) (regName b.depth)
      b.depth (arrPairs tpB)).flatMap idx0Leak := by
    rw [htpB]
    rfl
  rw [hTL] at hiter
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = movImmI (regName d) 0
      :: typedMoves (regName d) (regName (d + 1 + cs.length)) tpI := ⟨_, rfl⟩
  obtain ⟨Sh, hSh⟩ : ∃ Sh, Sh = movImmI (regName d) 0
      :: typedMoves (regName d) (regName (d + 1 + cs.length)) (shiftPairs d cs) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = movImmI (regName (b.depth + 1)) 0
        :: arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth (arrPairs tpB)
      ++ parMoves b.depth ((regPairs tpB).map Prod.fst)
        ((regPairs tpB).map fun p => .reg p.2) := ⟨_, rfl⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs, Zs = labelI (n + 1) :: (Sh ++ (rk.code ++ post)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = T
      ++ (advanceOps (regName d) (loopCtr n) ++ cmp :: condI (.reg "NZ") n :: Zs) := ⟨_, rfl⟩
  have hF : forArrFrame d n cs ops (.reg cn) b.code b.res b.depth
      = S0 ++ (movI (loopCtr n) (.reg cn) :: cmp
          :: condI (.reg "Z") (n + 1) :: labelI n :: (b.code
          ++ (movImmI (regName (b.depth + 1)) 0
          :: (arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth (arrPairs tpB)
          ++ (parMoves b.depth ((regPairs tpB).map Prod.fst)
            ((regPairs tpB).map fun p => .reg p.2)
          ++ (advanceOps (regName d) (loopCtr n) ++ (cmp :: condI (.reg "NZ") n
          :: labelI (n + 1) :: Sh))))))) := by
    rw [hcmp, hS0, hSh, htpI, htpB]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hcreg, ← hops, hF]
    at hbody
  have hbodyH : P.body = pre ++ S0
      ++ (movI (loopCtr n) (.reg cn) :: cmp
        :: (condI (.reg "Z") (n + 1) :: labelI n :: (b.code ++ R))) := by
    rw [hbody, hR, hZs, hT]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ S0
      ++ [movI (loopCtr n) (.reg cn), cmp, condI (.reg "Z") (n + 1)] :=
    ⟨_, rfl⟩
  have hbodyL : P.body = A ++ labelI n :: (b.code ++ R) := by
    rw [hbodyH, hAd]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hAlen : A.length = (pre ++ S0).length + 2 + 1 := by
    rw [hAd]
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, hcmp, hS0, labelsOf_append, labelsOf_append, labelsOf_cons_movImmI,
      labelsOf_typedMoves, List.append_nil]
    exact List.append_nil _
  have hAlab : ∀ l, n ≤ l → findLabelMem l A = none := fun l hl => by
    rw [findLabelMem_eq_none_iff, hAlabs, ← findLabelMem_eq_none_iff]
    exact hpre l hl
  obtain ⟨X, hX⟩ : ∃ X, X = A ++ labelI n :: (b.code
      ++ (T ++ (advanceOps (regName d) (loopCtr n) ++ [cmp, condI (.reg "NZ") n]))) := ⟨_, rfl⟩
  have hbodyX : P.body = X ++ labelI (n + 1) :: (Sh ++ (rk.code ++ post)) := by
    rw [hbodyL, hR, hZs, hX]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hXlen : X.length = A.length + 1 + b.code.length + T.length + 3 + 1 := by
    rw [hX]
    simp only [List.length_append, List.length_cons, advanceOps, List.length_nil]
    omega
  have hXlabs : labelsOf X = labelsOf pre ++ n :: labelsOf b.code := by
    rw [hX, hcmp, hT]
    simp only [labelsOf_append, hAlabs, labelsOf_cons_labelI, labelsOf_cons_movImmI,
      labelsOf_arrParMoves, labelsOf_parMoves, labelsOf_advanceOps, List.nil_append]
    rw [show labelsOf [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
      [.reg (loopCtr n), .imm 0]), condI (.reg "NZ") n] = [] from rfl, List.append_nil]
  have hl1 : findLabelMem (n + 1) P.body = some X.length := by
    rw [hbodyX]
    refine findLabelMem_append_labelI (n + 1) X _ ?_
    rw [hXlabs, List.mem_append, List.mem_cons, not_or, not_or]
    refine ⟨(findLabelMem_eq_none_iff _ pre).mp (hpre _ (by omega)), fun he => ?_, fun hm => ?_⟩
    · have : (n + 1 : Nat) = n := he
      omega
    · have := hLab.range _ hm
      omega
  -- the head
  obtain ⟨k0, t0, hs0, hat0, hz0, hidx0, hctr0, hR0, hA0, hothR0, hothA0⟩ :=
    forArrHead_stepsL (d := d) (n := n) (ops := ops) (cn := cn) htpI pre _ m (cnt := cnt)
      (by rw [hbodyH, hcmp, hS0]) hat hopslen hopsreg hcnk hcnt
      (fun {w q} u => ⟨_, by rw [hops, exprArgsHV_getD]; exact hag.2 (hvToHom inits u)⟩)
  rw [← hS0] at hat0
  have hfr0 : RegionFrame d n m.prog.base t0.prog.base :=
    RegionFrame.of_lvm_larr (fun r hr hl => hothR0 r hr (hl n le_rfl)) hothA0
  have hblkI : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      t0.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup (Expr.lookupArgs inits V)) := fun {w} u => by
    rw [getW_of_lvm_eq w (hR0 u), hops, exprArgsHV_getD,
      ← evalOperandN_resolveVar, lookup_lookupArgs]
    exact hag.1 (hvToHom inits u)
  have hblkAI : ∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
      t0.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
        = some (u.lookup (Expr.lookupArgs inits V)) := fun {w q} u => by
    rw [getArr_of_larr_eq w q (hA0 u), hops, exprArgsHV_getD, lookup_lookupArgs]
    exact hag.2 (hvToHom inits u)
  have hfetchZ : P.body[(pre ++ S0).length + 2]? = some (condI (.reg "Z") (n + 1)) :=
    fetch_of_body (xs := pre ++ S0
        ++ [movI (loopCtr n) (.reg cn), cmp])
      (by rw [hbodyH]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by simp only [List.length_append, List.length_cons, List.length_nil])
  -- the trips, to the counter after the exit label
  have hexit : ∃ (kE : Nat) (mE : LstateMF),
      StepsL P kE m mE (forHeadLeak nArgs d inits ++ .branch (decide (cnt.toNat = 0)) :: ℓr)
      ∧ atPc P (X.length + 1) mE
      ∧ RegionFrame d n m.prog.base mE.prog.base
      ∧ (∃ x : BitVec 64, mE.prog.base.reg.lvm (regName d) = ⟨64, x⟩)
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          mE.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN))
      ∧ (∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
          mE.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
            = some (u.lookup accN)) := by
    cases hN : cnt.toNat with
    | zero =>
        rw [hN, List.range_zero] at hiter
        simp only [forIterLeak, Option.some.injEq, Prod.mk.injEq] at hiter
        obtain ⟨rfl, rfl⟩ := hiter
        have hc0 : cnt = 0#64 := by bv_omega
        obtain ⟨hs1, hat1⟩ := steps_cc_taken (pol := true) rfl hat0 hfetchZ
          (by rw [hz0, hc0]; rfl) hl1
        exact ⟨_, _,
          (hs0.trans (stepsL_cc (pol := true) rfl hat0 hfetchZ hs1)).cast (by
            rw [hz0, hc0, hHL]
            rfl),
          hat1,
          hfr0.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl,
          ⟨_, hidx0⟩, fun {w} u => hblkI u, fun {w q} u => hblkAI u⟩
    | succ rem =>
        rw [hN, List.range_eq_range'] at hiter
        have hc0 : cnt ≠ 0#64 := by bv_omega
        obtain ⟨hs1, hat1⟩ := steps_cc_fall (pol := true) rfl hat0 hfetchZ
          (by rw [hz0]; simpa using hc0)
        have hL1 := stepsL_cc (pol := true) rfl hat0 hfetchZ hs1
        rw [← hAlen] at hat1
        obtain ⟨hs2, hat2⟩ := steps_label x86Isa (kind := .internal) (l := n) (tag := .reg none)
          hat1 (fetch_of_body hbodyL rfl)
        have hL2 := stepsL_label hat1 (fetch_of_body hbodyL rfl) hs2
        have hfr2 : RegionFrame d n m.prog.base (next (next t0)).prog.base :=
          hfr0.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
        obtain ⟨k3, m3, hs3, hat3, hfr3, hx3, hblk3, hblkA3⟩ :=
          forArrLoop_tripsL Pj nArgs fn body hbsim hb hlen harg hfn htpB hT hbodyL
            (by rw [hR, hcmp]) hAlab fuel V (rem + 1) rem 0 (Expr.lookupArgs inits V) accN ℓr
            (next (next t0)) cnt hiter (by omega) hN hat2
            (StoreAgreesM.of_regionFrame hlen hag hfr2) hidx0 hctr0 (fun {w} u => hblkI u)
            (fun {w q} u => hblkAI u)
        rw [← hXlen] at hat3
        obtain ⟨hs4, hat4⟩ := steps_label x86Isa (kind := .internal) (l := n + 1)
          (tag := .reg none) hat3 (fetch_of_body hbodyX rfl)
        have hL4 := stepsL_label hat3 (fetch_of_body hbodyX rfl) hs4
        exact ⟨_, _,
          ((((hs0.trans hL1).trans hL2).trans hs3).trans hL4).cast (by
            rw [hz0, hHL]
            simp [hc0]),
          hat4,
          (hfr2.trans hfr3 le_rfl le_rfl).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl)
            le_rfl le_rfl,
          hx3, fun {w} u => hblk3 u, fun {w q} u => hblkA3 u⟩
  obtain ⟨kE, mE, hsE, hatE, hfrE, -, hblkE, hblkAE⟩ := hexit
  -- the shift of the carried block
  obtain ⟨kS, mS, hsS, hatS, hRS, hAS, hoRS, hoAS⟩ := forArrShift_stepsL (d := d) (cs := cs)
    (X ++ [labelI (n + 1)]) (rk.code ++ post) mE
    (by rw [hbodyX, hSh]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    (by rw [List.length_append, List.length_singleton]; exact hatE)
    (fun {w q} u => ⟨_, hblkAE u⟩)
  have hfrS : RegionFrame d n m.prog.base mS.prog.base :=
    hfrE.trans (RegionFrame.of_lvm_larr (fun r hr _ => hoRS r hr) hoAS) le_rfl le_rfl
  have hagS : StoreAgreesM nArgs (d + cs.length) mS.prog.base (hvAppend accN V) :=
    storeAgreesM_append_arr harg (StoreAgreesM.of_regionFrame hlen hag hfrS)
      (fun {w} u => by
        rw [getW_of_lvm_eq w (hRS u)]
        exact hblkE u)
      (fun {w q} u => by
        rw [getArr_of_larr_eq w q (hAS u)]
        exact hblkAE u)
  -- the continuation
  have hnext := hLab.le
  obtain ⟨kK, m', hsK, hatK, hresK, hfrK⟩ := hksim (d + cs.length) b.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P
    (X ++ labelI (n + 1) :: Sh) post hfn
    (by rw [hbodyX]; simp only [List.append_assoc, List.cons_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append, hXlabs, labelsOf_cons_labelI, hSh,
        labelsOf_cons_movImmI, labelsOf_typedMoves]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨⟨(findLabelMem_eq_none_iff l pre).mp (hpre l (by omega)), fun he => ?_,
        fun hm => ?_⟩, fun he => ?_⟩
      · have : (l : Nat) = n := he
        omega
      · have := hLab.range _ hm
        omega
      · have : (l : Nat) = n + 1 := he
        omega)
    fuel _ v' ℓk mS hkden
    (by
      rw [show (X ++ labelI (n + 1) :: Sh).length = (X ++ [labelI (n + 1)]).length + 1
          + (typedMoves (regName d) (regName (d + 1 + cs.length)) (shiftPairs d cs)).length by
        rw [hSh]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega]
      exact hatS)
    hagS
  have hlenEq : pre.length + (Exported.prepend (forArrFrame d n cs
      (exprArgsHV d nArgs argName (fun _ => none) inits)
      (resolveVar d nArgs argName (fun _ => none) count) b.code b.res b.depth) rk).code.length
      = (X ++ labelI (n + 1) :: Sh).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyX] at h1
    simp only [List.length_append, List.length_cons] at h1 ⊢
    omega
  refine ⟨_, m', ((hsE.trans hsS).trans hsK).cast (by simp only [List.append_assoc,
    List.cons_append]), ?_, hresK,
    hfrS.trans hfrK (by omega) (by omega)⟩
  rw [hlenEq]
  exact hatK

/-! ## 7a. The rule of a branch -/

/-- The select of the widening of a bit is quiet. -/
theorem quietLopn_select (r opn f z : String) :
    QuietLopn (.Lopn [.reg r] opn [.reg f, .reg r, .reg z], .reg none) :=
  quietLopn_regs _ _ _ _ fun o ho => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> exact Or.inl ⟨_, rfl⟩

/-- **The jump to the join label of a branch with its events**: `MOV r, #1 ; CMP r, #0 ;
    jnz l`. The move and the compare emit nothing and the jump emits `branch true` on every
    run; the three steps reach the counter after the label `l`, keep the array carrier and
    write no register cell other than `r`. -/
theorem joinJump_stepsL {P : LprogM} {r : String} {l : LLabel} {q : Nat}
    (pre post : List LinstrRM) (s : LstateMF)
    (hbody : P.body = pre ++ (movImmI r 1
      :: guardI (.Lopn [.reg r] (withWidthTag 64 "CMP") [.reg r, .imm 0])
      :: condI (.reg "NZ") l :: post))
    (hat : atPc P pre.length s) (hl : findLabelMem l P.body = some q) :
    ∃ t, StepsL P 3 s t [.branch true] ∧ atPc P (q + 1) t
      ∧ t.prog.base.larr = s.prog.base.larr
      ∧ ∀ x, x ≠ r → t.prog.base.reg.lvm x = s.prog.base.reg.lvm x := by
  obtain ⟨t1, hs1, hat1, ha1, hm1⟩ := steps_movImm (dst := r) (c := 1) hat
    (fetch_of_body hbody rfl)
  obtain ⟨t2, hs2, hat2, ha2, hm2, hz2⟩ := steps_cmpZero (r := r) (v := BitVec.ofNat 64 1) hat1
    (fetch_of_body (xs := pre ++ [movImmI r 1])
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append]; rfl))
    (by rw [hm1, if_pos rfl])
  have hfJ : P.body[pre.length + 1 + 1]? = some (condI (.reg "NZ") l) :=
    fetch_of_body (xs := pre ++ [movImmI r 1,
        guardI (.Lopn [.reg r] (withWidthTag 64 "CMP") [.reg r, .imm 0])])
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append]; rfl)
  obtain ⟨hs3, hat3⟩ := steps_cc_taken (cc := "NZ") (pol := false) rfl hat2 hfJ
    (by rw [hz2]; decide) hl
  have hL12 : StepsL P 2 s t2 [] := stepsL_of_quiet_le 2
    [movImmI r 1, guardI (.Lopn [.reg r] (withWidthTag 64 "CMP") [.reg r, .imm 0])] pre
    (condI (.reg "NZ") l :: post) s t2
    (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact quietLopn_movImm _ _
      · exact quietLopn_cmp _)
    hat (hs1.trans hs2) (le_refl _)
  have hL3 := stepsL_cc (cc := "NZ") (pol := false) rfl hat2 hfJ hs3
  refine ⟨_, (hL12.trans hL3).cast (by rw [hz2]; rfl), hat3, ha2.trans ha1, fun x hx => ?_⟩
  show t2.prog.base.reg.lvm x = s.prog.base.reg.lvm x
  rw [hm2, hm1, if_neg hx]

/-- **The assignment of the results of a branch, with its events.** The run of
    `ifResMoves_steps` is a traced run with the events `idx0Leak` of the parallel
    assignment of the returned arrays. -/
theorem ifResMoves_stepsL {P : LprogM} {nArgs d D : Nat} {rs : Ctxt jasminDialect}
    {ops : List LOperand} (pre post : List LinstrRM) (s : LstateMF)
    {rv : Ctxt.Valuation rs}
    (hbody : P.body = pre ++ ifResMoves rs d (D + rs.length) ops ++ post)
    (hat : atPc P pre.length s) (hD : d ≤ D) (hres : ResAgrees nArgs D s.prog.base ops rv) :
    ∃ t, StepsL P (ifResMoves rs d (D + rs.length) ops).length s t
        ((arrParMoves (regName (D + rs.length + 1)) (regName (D + rs.length))
          (D + rs.length) (arrPairs (ifResPairs rs d ops))).flatMap idx0Leak)
      ∧ atPc P (pre.length + (ifResMoves rs d (D + rs.length) ops).length) t
      ∧ (∀ n, RegionFrame d n s.prog.base t.prog.base)
      ∧ (∀ {w : Nat} (u : Ctxt.Var rs (.reg w)),
          t.prog.base.reg.getW (regName (d + (rs.length - 1 - varIndex u))) w
            = some (u.lookup rv))
      ∧ (∀ {w m : Nat} (u : Ctxt.Var rs (.stackArr w m)),
          t.prog.base.getArr (regName (d + (rs.length - 1 - varIndex u))) w m
            = some (u.lookup rv)) := by
  obtain ⟨M, hM⟩ : ∃ M, M = ifResMoves rs d (D + rs.length) ops := ⟨_, rfl⟩
  obtain ⟨t, hs, hat', rest⟩ := ifResMoves_steps (nArgs := nArgs) (d := d) (D := D)
    (rs := rs) (ops := ops) (P := singletonProgM P.lfn (pre ++ M)) pre [] s (rv := rv)
    (by rw [hM, List.append_nil]; rfl) hat hD hres
  rw [← hM] at hs hat' ⊢
  rw [← hM] at hbody
  obtain ⟨tp, htp⟩ : ∃ tp, tp = arrPairs (ifResPairs rs d ops) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = parMoves (D + rs.length) ((regPairs (ifResPairs rs d ops)).map
      Prod.fst) ((regPairs (ifResPairs rs d ops)).map fun p => .reg p.2) := ⟨_, rfl⟩
  have hq : ∀ i ∈ Q, QuietLopn i := by
    rw [hQ]
    refine quietLopn_parMoves _ _ _ fun o ho => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
    exact ⟨_, rfl⟩
  rw [← htp]
  by_cases hemp : tp.isEmpty = true
  · have hM' : M = Q := by
      rw [hM, hQ, ifResMoves, ← htp, if_pos hemp, List.nil_append]
    rw [List.isEmpty_iff.mp hemp]
    subst hM'
    exact ⟨t, (stepsL_of_quiet hbody hq hat hs hat'.2).cast (by
        simp [arrParMoves, arrMoves]), ⟨hat'.1, hat'.2⟩, rest⟩
  · have hzt : regName (D + rs.length + 1) ≠ regName (D + rs.length) := fun he => by
      have := JasminLsemSimulation.regName_injective he
      omega
    have hM' : M = movImmI (regName (D + rs.length + 1)) 0
        :: (arrParMoves (regName (D + rs.length + 1)) (regName (D + rs.length))
          (D + rs.length) tp ++ Q) := by
      rw [hM, hQ, ifResMoves, ← htp, if_neg hemp, List.cons_append]
    subst hM'
    have hL := stepsL_of_idx0 hbody (idx0Lopn_arrParMoves hzt _ _) hq hat hs (by
      rw [hat'.2]
      simp only [List.length_cons, List.length_append]
      omega)
    refine ⟨t, ?_, ⟨hat'.1, hat'.2⟩, rest⟩
    rw [List.length_cons, List.length_append, Nat.add_comm]
    exact hL

/-- **The rule of a branch.** The statements for the two arms and for the continuation give
    the statement for the branch: the run emits the branch event of the guard, which is
    taken when the condition bit is clear, then the events of the arm the bit selects, then
    the events `ifResLeak` of the assignment of its results, then, after the then arm, the
    event `branch true` of the jump to the join label, then the events of the
    continuation. -/
theorem exportRLeakSim_if (Pj : JLeakParams) (nArgs : Nat) (fn : String)
    {Γ rs : Ctxt jasminDialect} {ts : List JasminTy} (cond : Ctxt.Var Γ (JasminTy.reg 1))
    (thn els : NFProg jasminDialect Γ rs) (k : NFProg jasminDialect (rs ++ Γ) ts)
    (htsim : ExportRLeakSim Pj nArgs fn thn)
    (hesim : ExportRLeakSim Pj nArgs fn els) (hksim : ExportRLeakSim Pj nArgs fn k) :
    ExportRLeakSim Pj nArgs fn (NFProg.ifThenElse cond thn els k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V v ℓ m hrun hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, e, he, rk, hrk, rfl⟩ := h
  simp only [machRun, ht, he, Option.bind_some] at hrun
  obtain ⟨⟨rv, ℓa⟩, hbr, hkrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨⟨v', ℓk⟩, hkden, heq⟩ := Option.map_eq_some_iff.mp hkrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hbody0 := hbody
  have hLT := exportR_labelsOK nArgs fn x86Data_guardsPlain thn _ _ _ ht
  have hLE := exportR_labelsOK nArgs fn x86Data_guardsPlain els _ _ _ he
  have hTle := hLT.le
  have hEle := hLE.le
  have htd := exportR_depth_le nArgs fn thn _ _ _ ht
  have hed := exportR_depth_le nArgs fn els _ _ _ he
  have htl := exportR_res_length nArgs fn thn _ _ _ ht
  have hel := exportR_res_length nArgs fn els _ _ _ he
  -- the condition
  obtain ⟨cn, hcn⟩ : ∃ cn, cn = operandName (resolveVar d nArgs argName (fun _ => none) cond) :=
    ⟨_, rfl⟩
  have hcreg : resolveVar d nArgs argName (fun _ => none) cond = .reg cn := by
    rw [hcn]
    exact resolveVar_isReg cond
  have hbit : m.prog.base.reg.lvm cn = ⟨1, cond.lookup V⟩ := by
    have := hag.1 cond
    rw [evalOperandN_resolveVar, ← hcn] at this
    exact getW_eq_some_iff.mp this
  have hcnk : ∀ k, d ≤ k → cn ≠ regName k := fun k hk => by
    rw [hcn]
    exact resolveVar_operandName_ne_regName cond
      (hlen ▸ JasminLsemSimulation.varIndex_lt cond) k hk
  -- the layout of the body
  obtain ⟨cmov, hcmov⟩ : ∃ cmov : LinstrRM, cmov = (.Lopn [.reg (regName d)]
      (withWidthTag 64 "CMOV") [.reg cn, .reg (regName d), .reg (regName (d + 1))], .reg none) :=
    ⟨_, rfl⟩
  obtain ⟨cmp, hcmp⟩ : ∃ cmp, cmp = guardI (.Lopn [.reg (regName d)] (withWidthTag 64 "CMP")
      [.reg (regName d), .imm 0]) := ⟨_, rfl⟩
  obtain ⟨TM, hTM⟩ : ∃ TM, TM = ifResMoves rs d (t.depth + rs.length) t.res := ⟨_, rfl⟩
  obtain ⟨EM, hEM⟩ : ∃ EM, EM = ifResMoves rs d (e.depth + rs.length) e.res := ⟨_, rfl⟩
  have hTMlab : labelsOf TM = [] := by rw [hTM]; exact labelsOf_ifResMoves _ _ _ _
  have hEMlab : labelsOf EM = [] := by rw [hEM]; exact labelsOf_ifResMoves _ _ _ _
  have hHq : ∀ i ∈ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0, cmov, cmp],
      QuietLopn i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact quietLopn_movImm _ _
    · exact quietLopn_movImm _ _
    · rw [hcmov]; exact quietLopn_select _ _ _ _
    · rw [hcmp]; exact quietLopn_cmp _
  obtain ⟨J, hJ⟩ : ∃ J : List LinstrRM, J = [movImmI (regName (d + rs.length)) 1,
      guardI (.Lopn [.reg (regName (d + rs.length))] (withWidthTag 64 "CMP")
        [.reg (regName (d + rs.length)), .imm 0]), condI (.reg "NZ") (n + 2)] := ⟨_, rfl⟩
  have hJlab : labelsOf J = [] := by rw [hJ]; rfl
  have hF : ifFrame fn d n rs (.reg cn) t.code t.res t.depth e.code e.res e.depth
      = movImmI (regName d) 1 :: movImmI (regName (d + 1)) 0 :: cmov :: cmp
        :: condI (.reg "Z") (n + 1) :: labelI n :: (t.code ++ (TM ++ (J
        ++ labelI (n + 1) :: (e.code ++ (EM ++ [labelI (n + 2)]))))) := by
    rw [hcmov, hcmp, hTM, hEM, hJ]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hcreg, hF]
    at hbody
  have hbodyH : P.body = pre ++ (movImmI (regName d) 1 :: movImmI (regName (d + 1)) 0 :: cmov
      :: cmp :: condI (.reg "Z") (n + 1) :: labelI n :: (t.code ++ (TM ++ (J
      ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post))))))) := by
    rw [hbody]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0, cmov,
      cmp, condI (.reg "Z") (n + 1)] := ⟨_, rfl⟩
  have hbodyA : P.body = A ++ labelI n :: (t.code ++ (TM ++ (J
      ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post)))))) := by
    rw [hbodyH, hAd]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hAlen : A.length = pre.length + 4 + 1 := by
    rw [hAd, List.length_append]
    rfl
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, hcmov, hcmp, labelsOf_append]
    exact List.append_nil _
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = A ++ labelI n :: (t.code ++ (TM ++ J)) := ⟨_, rfl⟩
  have hbodyY : P.body = Y ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2)
      :: (rk.code ++ post))) := by
    rw [hbodyA, hYd]
    simp only [List.append_assoc, List.cons_append]
  have hYlabs : labelsOf Y = labelsOf pre ++ n :: labelsOf t.code := by
    simp only [hYd, labelsOf_append, hAlabs, labelsOf_cons_labelI, hJlab, hTMlab,
      List.append_nil]
  obtain ⟨X, hXd⟩ : ∃ X, X = Y ++ labelI (n + 1) :: (e.code ++ EM) := ⟨_, rfl⟩
  have hbodyX : P.body = X ++ labelI (n + 2) :: (rk.code ++ post) := by
    rw [hbodyY, hXd]
    simp only [List.append_assoc, List.cons_append]
  have hXlabs : labelsOf X
      = labelsOf pre ++ n :: (labelsOf t.code ++ (n + 1) :: labelsOf e.code) := by
    simp only [hXd, labelsOf_append, hYlabs, labelsOf_cons_labelI, hEMlab, List.append_nil,
      List.append_assoc, List.cons_append]
  have hXlen : X.length = (Y ++ labelI (n + 1) :: e.code).length + EM.length := by
    rw [hXd]
    simp only [List.length_append, List.length_cons]
    omega
  have hpreL : ∀ l, n ≤ l → l ∉ labelsOf pre := fun l hl =>
    (findLabelMem_eq_none_iff l pre).mp (hpre l hl)
  have hYnot : ∀ l : Nat, n + 1 ≤ l → l ∉ labelsOf t.code → l ∉ labelsOf Y := by
    intro l hl ht' hm
    rw [hYlabs, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm
    · exact hpreL l (by omega) hm
    · omega
    · exact ht' hm
  have hXnot : ∀ l : Nat, n + 2 ≤ l → l ∉ labelsOf t.code → l ∉ labelsOf e.code →
      l ∉ labelsOf X := by
    intro l hl ht' he' hm
    rw [hXlabs, List.mem_append, List.mem_cons, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm | hm | hm
    · exact hpreL l (by omega) hm
    · omega
    · exact ht' hm
    · omega
    · exact he' hm
  have hl1 : findLabelMem (n + 1) P.body = some Y.length := by
    rw [hbodyY]
    exact findLabelMem_append_labelI (n + 1) Y _
      (hYnot (n + 1) le_rfl fun hm => by have := hLT.range _ hm; omega)
  have hl2 : findLabelMem (n + 2) P.body = some X.length := by
    rw [hbodyX]
    exact findLabelMem_append_labelI (n + 2) X _
      (hXnot (n + 2) le_rfl (fun hm => by have := hLT.range _ hm; omega)
        fun hm => by have := hLE.range _ hm; omega)
  -- the head
  obtain ⟨t0, hs0v, hat0, hz0, hfr0⟩ := ifHead_steps (d := d) (f := cn) pre _ m
    (bit := cond.lookup V) (by rw [hbodyH, hcmov, hcmp]) hat hcnk hbit
  have hs0 : StepsL P 4 m t0 [] := stepsL_of_quiet_le 4 _ pre _ m t0
    (show P.body = pre ++ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0, cmov, cmp]
        ++ (condI (.reg "Z") (n + 1) :: labelI n :: (t.code ++ (TM ++ (J
        ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post))))))) by
      rw [hbodyH]
      simp only [List.append_assoc, List.cons_append, List.nil_append])
    hHq hat hs0v (le_refl _)
  have hz0' : t0.zf = !(HasBoolBit.toBool (d := jasminDialect) (cond.lookup V)) := hz0
  have hfetchZ : P.body[pre.length + 4]? = some (condI (.reg "Z") (n + 1)) :=
    fetch_of_body (xs := pre ++ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0, cmov, cmp])
      (by rw [hbodyH]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append]; rfl)
  -- the selected branch, to the counter after the join label
  have hjoin : ∃ (kJ : Nat) (mJ : LstateMF),
      StepsL P kJ m mJ
        (.branch (!HasBoolBit.toBool (d := jasminDialect) (cond.lookup V))
          :: (ℓa ++ (ifResLeak d rs
            (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then t else e)
            ++ if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V)
              then [CTLeak.branch true] else [])))
      ∧ atPc P (X.length + 1) mJ
      ∧ RegionFrame d n m.prog.base mJ.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var rs (.reg w)),
          mJ.prog.base.reg.getW (regName (d + (rs.length - 1 - varIndex u))) w
            = some (u.lookup rv))
      ∧ (∀ {w m : Nat} (u : Ctxt.Var rs (.stackArr w m)),
          mJ.prog.base.getArr (regName (d + (rs.length - 1 - varIndex u))) w m
            = some (u.lookup rv)) := by
    by_cases hbt : HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) = true
    · rw [if_pos hbt] at hbr
      obtain ⟨hs1, hat1⟩ := steps_cc_fall (pol := true) rfl hat0 hfetchZ
        (by rw [hz0', hbt]; decide)
      have hL1 := stepsL_cc (pol := true) rfl hat0 hfetchZ hs1
      rw [← hAlen] at hat1
      obtain ⟨hs2, hat2⟩ := steps_label x86Isa (kind := .internal) (l := n) (tag := .reg none)
        hat1 (fetch_of_body hbodyA rfl)
      have hL2 := stepsL_label hat1 (fetch_of_body hbodyA rfl) hs2
      have hfr2 : RegionFrame d n m.prog.base (next (next t0)).prog.base :=
        (hfr0 n).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      obtain ⟨k3, m3, hs3, hat3, hres3, hfr3⟩ := htsim d (n + 3) t ht hlen harg P
        (A ++ [labelI n]) (TM ++ (J ++ labelI (n + 1) :: (e.code ++ (EM
          ++ labelI (n + 2) :: (rk.code ++ post))))) hfn
        (by rw [hbodyA]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        (fun l hl => by
          rw [findLabelMem_eq_none_iff, labelsOf_append, hAlabs]
          simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
            not_or]
          exact ⟨hpreL l (by omega), fun he => by have : (l : Nat) = n := he; omega⟩)
        fuel V rv ℓa (next (next t0)) hbr
        (by rw [List.length_append, List.length_singleton]; exact hat2)
        (StoreAgreesM.of_regionFrame hlen hag hfr2)
      have hat3' : atPc P (A ++ labelI n :: t.code).length m3 := by
        rw [List.length_append, List.length_singleton] at hat3
        rw [List.length_append, List.length_cons]
        rwa [show A.length + (t.code.length + 1) = A.length + 1 + t.code.length by omega]
      obtain ⟨m4, hL4, hat4, hfr4, hblk4, hblkA4⟩ := ifResMoves_stepsL (nArgs := nArgs)
        (d := d) (D := t.depth) (rs := rs) (ops := t.res) (A ++ labelI n :: t.code)
        (J ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2)
          :: (rk.code ++ post)))) m3 (rv := rv)
        (by rw [hbodyA, ← hTM]; simp only [List.append_assoc, List.cons_append])
        hat3' htd hres3
      rw [← hTM] at hL4 hat4
      have hlen4 : (A ++ labelI n :: (t.code ++ TM)).length
          = (A ++ labelI n :: t.code).length + TM.length := by
        simp only [List.length_append, List.length_cons]
        omega
      rw [← hlen4] at hat4
      obtain ⟨m5, hL5, hat5, ha5, hm5⟩ := joinJump_stepsL (r := regName (d + rs.length))
        (l := n + 2) (A ++ labelI n :: (t.code ++ TM))
        (labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post)))) m4
        (by rw [hbodyA, hJ]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        hat4 hl2
      exact ⟨_, m5, (((((hs0.trans hL1).trans hL2).trans hs3).trans hL4).trans hL5).cast (by
          rw [hz0', hbt]
          simp [ifResLeak]),
        hat5,
        (((hfr2.trans hfr3 le_rfl (by omega)).trans (hfr4 n) le_rfl le_rfl).trans
          (RegionFrame.of_cells ha5 fun r hr _ => hm5 r (hr _ (Nat.le_add_right _ _)))
          le_rfl le_rfl),
        fun {w} u => (getW_congr w (hm5 _ fun he => by
          have := JasminLsemSimulation.regName_injective he
          have := JasminLsemSimulation.varIndex_lt u
          omega)).trans (hblk4 u),
        fun {w m} u => (getArr_of_larr_eq w m (by rw [ha5])).trans (hblkA4 u)⟩
    · rw [if_neg hbt] at hbr
      rw [Bool.not_eq_true] at hbt
      obtain ⟨hs1, hat1⟩ := steps_cc_taken (pol := true) rfl hat0 hfetchZ
        (by rw [hz0', hbt]; rfl) hl1
      have hL1 := stepsL_cc (pol := true) rfl hat0 hfetchZ hs1
      have hfr1 : RegionFrame d n m.prog.base (goto t0 (Y.length + 1)).prog.base :=
        (hfr0 n).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      obtain ⟨k3, m3, hs3, hat3, hres3, hfr3⟩ := hesim d t.next e he hlen harg P
        (Y ++ [labelI (n + 1)]) (EM ++ labelI (n + 2) :: (rk.code ++ post)) hfn
        (by rw [hbodyY]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        (fun l hl => by
          rw [findLabelMem_eq_none_iff, labelsOf_append]
          simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
            not_or]
          exact ⟨hYnot l (by omega) fun hm => by have := hLT.range l hm; omega,
            fun he => by have : (l : Nat) = n + 1 := he; omega⟩)
        fuel V rv ℓa (goto t0 (Y.length + 1)) hbr
        (by rw [List.length_append, List.length_singleton]; exact hat1)
        (StoreAgreesM.of_regionFrame hlen hag hfr1)
      have hat3' : atPc P (Y ++ labelI (n + 1) :: e.code).length m3 := by
        rw [List.length_append, List.length_singleton] at hat3
        rw [List.length_append, List.length_cons]
        rwa [show Y.length + (e.code.length + 1) = Y.length + 1 + e.code.length by omega]
      obtain ⟨m4, hL4, hat4, hfr4, hblk4, hblkA4⟩ := ifResMoves_stepsL (nArgs := nArgs)
        (d := d) (D := e.depth) (rs := rs) (ops := e.res) (Y ++ labelI (n + 1) :: e.code)
        (labelI (n + 2) :: (rk.code ++ post)) m3 (rv := rv)
        (by rw [hbodyY, ← hEM]; simp only [List.append_assoc, List.cons_append])
        hat3' hed hres3
      rw [← hEM] at hL4 hat4
      rw [← hXlen] at hat4
      obtain ⟨hs5, hat5⟩ := steps_label x86Isa (kind := .internal) (l := n + 2)
        (tag := .reg none) hat4 (fetch_of_body hbodyX rfl)
      have hL5 := stepsL_label hat4 (fetch_of_body hbodyX rfl) hs5
      exact ⟨_, _, ((((hs0.trans hL1).trans hs3).trans hL4).trans hL5).cast (by
          rw [hz0', hbt]
          simp [ifResLeak]),
        hat5,
        (((hfr1.trans hfr3 le_rfl (by omega)).trans (hfr4 n) le_rfl le_rfl).trans
          (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl),
        fun {w} u => hblk4 u, fun {w m} u => hblkA4 u⟩
  obtain ⟨kJ, mJ, hsJ, hatJ, hfrJ, hblkJ, hblkAJ⟩ := hjoin
  have hagJ : StoreAgreesM nArgs (d + rs.length) mJ.prog.base (hvAppend rv V) :=
    storeAgreesM_append_arr harg (StoreAgreesM.of_regionFrame hlen hag hfrJ)
      (fun {w} u => hblkJ u) (fun {w m} u => hblkAJ u)
  -- the continuation
  obtain ⟨kK, m', hsK, hatK, hresK, hfrK⟩ := hksim (d + rs.length) e.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P (X ++ [labelI (n + 2)]) post hfn
    (by rw [hbodyX]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append]
      simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
        not_or]
      exact ⟨hXnot l (by omega) (fun hm => by have := hLT.range l hm; omega)
          fun hm => by have := hLE.range l hm; omega,
        fun he => by have : (l : Nat) = n + 2 := he; omega⟩)
    fuel _ v' ℓk mJ hkden
    (by rw [List.length_append, List.length_singleton]; exact hatJ) hagJ
  have hlenEq : pre.length + (Exported.prepend (ifFrame fn d n rs
      (resolveVar d nArgs argName (fun _ => none) cond) t.code t.res t.depth e.code e.res
      e.depth) rk).code.length = (X ++ [labelI (n + 2)]).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyX] at h1
    simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
    omega
  refine ⟨kJ + kK, m', (hsJ.trans hsK).cast (by
      simp only [List.cons_append, List.append_assoc]), ?_, hresK,
    hfrJ.trans hfrK (by omega) (by omega)⟩
  rw [hlenEq]
  exact hatK

/-! ## 7b. The rule of a loop in exit-flag form -/

/-- **The tail of a trip of an exit-flag loop, with its events.** The run of
    `whileTail_steps` is a traced run with no event. -/
theorem whileTail_stepsL {P : LprogM} {d nCar bD : Nat} {ops : List LOperand} {f : String}
    (pre post : List LinstrRM) (s : LstateMF) {bit : BitVec 1}
    (hbody : P.body = pre ++ (movImmI (regName (bD + nCar)) 1
      :: movImmI (regName (bD + nCar + 1)) 0
      :: (.Lopn [.reg (regName (bD + nCar))] (withWidthTag 64 "CMOV")
        [.reg f, .reg (regName (bD + nCar)), .reg (regName (bD + nCar + 1))], .reg none)
      :: (parMoves bD (carriedRegs d nCar) ops
        ++ guardI (.Lopn [.reg (regName (bD + nCar))] (withWidthTag 64 "CMP")
          [.reg (regName (bD + nCar)), .imm 0]) :: post)))
    (hat : atPc P pre.length s) (hlen : ops.length = nCar) (hD : d + nCar ≤ bD)
    (hops : ∀ o ∈ ops, o = .reg (operandName o) ∧ ∀ k, bD ≤ k → operandName o ≠ regName k)
    (hf : ∀ k, bD ≤ k → f ≠ regName k) (hbit : s.prog.base.reg.lvm f = ⟨1, bit⟩) :
    ∃ (k : Nat) (t : LstateMF), StepsL P k s t [] ∧ atPc P (pre.length + 2 * nCar + 4) t
      ∧ t.prog.base.larr = s.prog.base.larr ∧ t.zf = !decide (bit = 1#1)
      ∧ (∀ j, j < nCar → t.prog.base.reg.lvm (regName (d + (nCar - 1 - j)))
          = s.prog.base.reg.lvm (operandName (ops.getD j (.imm 0))))
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) →
          t.prog.base.reg.lvm r = s.prog.base.reg.lvm r) := by
  obtain ⟨seg, hseg⟩ : ∃ seg, seg = movImmI (regName (bD + nCar)) 1
      :: movImmI (regName (bD + nCar + 1)) 0
      :: (.Lopn [.reg (regName (bD + nCar))] (withWidthTag 64 "CMOV")
        [.reg f, .reg (regName (bD + nCar)), .reg (regName (bD + nCar + 1))], .reg none)
      :: (parMoves bD (carriedRegs d nCar) ops
        ++ [guardI (.Lopn [.reg (regName (bD + nCar))] (withWidthTag 64 "CMP")
          [.reg (regName (bD + nCar)), .imm 0])]) := ⟨_, rfl⟩
  have hq : ∀ i ∈ seg, QuietLopn i := by
    intro i hi
    rw [hseg] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | hi | rfl
    · exact quietLopn_movImm _ _
    · exact quietLopn_movImm _ _
    · exact quietLopn_select _ _ _ _
    · exact quietLopn_parMoves _ _ _ (fun o ho => ⟨_, (hops o ho).1⟩) i hi
    · exact quietLopn_cmp _
  have hbP : P.body = pre ++ seg ++ post := by
    rw [hbody, hseg]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨k, t, hs, hat', rest⟩ := whileTail_steps
    (P := singletonProgM P.lfn (pre ++ seg)) (d := d) (nCar := nCar) (bD := bD) (ops := ops)
    (f := f) pre [] s (bit := bit)
    (by
      show pre ++ seg = _
      rw [hseg])
    hat hlen hD hops hf hbit
  refine ⟨seg.length, t, stepsL_of_quiet hbP hq hat hs ?_, ⟨hat'.1, hat'.2⟩, rest.2⟩
  rw [hat'.2, hseg]
  simp only [List.length_append, List.length_cons, List.length_nil, parMoves_length,
    carriedRegs_length, hlen]
  omega

/-- The iteration of an exit-flag loop within `f + 1` runs is a first run of the body
    followed by the branch event of its flag and, when the flag is set, the iteration
    within `f` runs. -/
theorem whileIterLeak_succ_eq_some {cs : List JasminTy}
    {step : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) (JasminTy.reg 1 :: cs) × List CTLeak)}
    {f : Nat} {acc a : Ctxt.Valuation (d := jasminDialect) cs} {ℓ : List CTLeak} :
    whileIterLeak step (f + 1) acc = some (a, ℓ) ↔
      ∃ r ℓb, step acc = some (r, ℓb) ∧
        ((HasBoolBit.toBool (d := jasminDialect) r.head = true
            ∧ ∃ ℓ2, whileIterLeak step f r.tail = some (a, ℓ2)
              ∧ ℓ = ℓb ++ CTLeak.branch true :: ℓ2)
          ∨ (HasBoolBit.toBool (d := jasminDialect) r.head = false ∧ a = r.tail
              ∧ ℓ = ℓb ++ [CTLeak.branch false])) := by
  simp only [whileIterLeak, Option.bind_eq_some_iff, Prod.exists]
  constructor
  · rintro ⟨r, ℓb, hstep, h⟩
    refine ⟨r, ℓb, hstep, ?_⟩
    by_cases hb : HasBoolBit.toBool (d := jasminDialect) r.head = true
    · rw [if_pos hb] at h
      obtain ⟨⟨a', ℓ2⟩, h2, heq⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact Or.inl ⟨hb, ℓ2, h2, rfl⟩
    · rw [if_neg hb] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact Or.inr ⟨Bool.not_eq_true _ ▸ hb, rfl, rfl⟩
  · rintro ⟨r, ℓb, hstep, ⟨hb, ℓ2, h2, rfl⟩ | ⟨hb, rfl, rfl⟩⟩
    · exact ⟨r, ℓb, hstep, by rw [if_pos hb, h2]; rfl⟩
    · exact ⟨r, ℓb, hstep, by rw [if_neg (by rw [hb]; decide)]⟩

section WhileLoopL

variable (Pj : JLeakParams) (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
  (body : NFProg jasminDialect (cs ++ Γ) (JasminTy.reg 1 :: cs)) (hcs : RegTys cs)
  (hsim : ExportRLeakSim Pj nArgs fn body) {d n : Nat} {b : Exported}
  (hb : exportR nArgs fn body (d + cs.length) (n + 1) = some b) (hlen : Γ.length = d)
  (harg : nArgs ≤ d) {P : LprogM} {A R Z : List LinstrRM} {fname : String} (hfn : P.lfn = fn)
  (hbody : P.body = A ++ labelI n :: (b.code ++ R))
  (hfh : b.res.headD (.imm 0) = .reg fname)
  (hR : R = movImmI (regName (b.depth + cs.length)) 1
    :: movImmI (regName (b.depth + cs.length + 1)) 0
    :: (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
      [.reg fname, .reg (regName (b.depth + cs.length)),
        .reg (regName (b.depth + cs.length + 1))], .reg none)
    :: (parMoves b.depth (carriedRegs d cs.length) b.res.tail
      ++ guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
        [.reg (regName (b.depth + cs.length)), .imm 0]) :: condI (.reg "NZ") n :: Z))
  (hA : ∀ l, n ≤ l → findLabelMem l A = none) (fuel : Nat) (V : Ctxt.Valuation Γ)

include hcs hsim hb hlen harg hfn hbody hfh hR hA in
/-- **One trip of an exit-flag loop, with its events**, from the counter after the label
    to the back-edge jump: the events are those of the body. -/
theorem whileLoop_tripL (acc : Ctxt.Valuation cs)
    (r : Ctxt.Valuation (d := jasminDialect) (JasminTy.reg 1 :: cs)) (ℓ : List CTLeak)
    (m : LstateMF)
    (hden : machRun Pj nArgs fn fuel body (d + cs.length) (n + 1) (hvAppend acc V)
      = some (r, ℓ))
    (hat : atPc P (A.length + 1) m) (hag : StoreAgreesM nArgs d m.prog.base V)
    (hblk : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) :
    ∃ (k : Nat) (t : LstateMF), StepsL P k m t ℓ
      ∧ atPc P ((A ++ labelI n :: b.code).length + 2 * cs.length + 4) t
      ∧ RegionFrame d n m.prog.base t.prog.base
      ∧ t.zf = !(HasBoolBit.toBool (d := jasminDialect) r.head)
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          t.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
            = some (u.lookup r.tail)) := by
  have hag2 : StoreAgreesM nArgs (d + cs.length) m.prog.base (hvAppend acc V) :=
    storeAgreesM_append hcs harg hag hblk
  have hbd := exportR_depth_le nArgs fn body _ _ _ hb
  obtain ⟨k1, m1, hs1, hat1, ⟨Δ, W, vs, hΔ, hagW, hops, hr⟩, hfr1⟩ :=
    hsim (d + cs.length) (n + 1) b hb
      (by rw [List.length_append, hlen]; omega) (by omega) P
      (A ++ [labelI n]) R hfn
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
      (fun l hl => by
        rw [findLabelMem_eq_none_iff, labelsOf_append]
        simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
          not_or]
        exact ⟨(findLabelMem_eq_none_iff l A).mp (hA l (by omega)),
          fun he => by have : (l : Nat) = n := he; omega⟩)
      fuel _ r ℓ m hden
      (by rw [List.length_append, List.length_singleton]; exact hat) hag2
  subst hr
  cases vs with
  | cons v0 vrest =>
  have hops' : b.res = resolveVar b.depth nArgs argName (fun _ => none) v0
      :: exprArgsHV b.depth nArgs argName (fun _ => none) vrest := hops
  have hfh' : resolveVar b.depth nArgs argName (fun _ => none) v0 = .reg fname := by
    rw [hops'] at hfh
    exact hfh
  have hfname : fname = operandName (resolveVar b.depth nArgs argName (fun _ => none) v0) := by
    rw [hfh']
    rfl
  have hbit : m1.prog.base.reg.lvm fname = ⟨1, v0.lookup W⟩ := by
    have := hagW.1 v0
    rw [hfh'] at this
    exact getW_eq_some_iff.mp this
  have hat1' : atPc P (A ++ labelI n :: b.code).length m1 := by
    rw [List.length_append, List.length_singleton] at hat1
    rw [List.length_append, List.length_cons]
    rwa [show A.length + (b.code.length + 1) = A.length + 1 + b.code.length by omega]
  obtain ⟨k2, t, hs2, hat2, harr, hz, hblk', hoth⟩ :=
    whileTail_stepsL (d := d) (nCar := cs.length) (bD := b.depth) (ops := b.res.tail)
      (f := fname) (A ++ labelI n :: b.code) (condI (.reg "NZ") n :: Z) m1 (bit := v0.lookup W)
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append])
      hat1' (by rw [hops', List.tail_cons, exprArgsHV_length]) (by omega)
      (by rw [hops', List.tail_cons]; exact exprArgsHV_reg nArgs hΔ vrest)
      (fun k hk => by
        rw [hfname]
        exact resolveVar_operandName_ne_regName v0
          (hΔ ▸ JasminLsemSimulation.varIndex_lt v0) k hk)
      hbit
  refine ⟨k1 + k2, t, (hs1.trans hs2).cast (List.append_nil _), hat2, ?_, hz,
    fun {w} u => ?_⟩
  · exact (hfr1.mono (by omega) (by omega)).trans
      (RegionFrame.of_cells harr fun r hr _ => hoth r hr) le_rfl le_rfl
  · have hu := JasminLsemSimulation.varIndex_lt u
    rw [getW_of_lvm_eq w (hblk' (varIndex u) hu), hops', List.tail_cons, exprArgsHV_getD,
      ← evalOperandN_resolveVar]
    exact (hagW.1 (hvToHom vrest u)).trans (congrArg some (lookup_lookupArgs W vrest u).symm)

include hcs hsim hb hlen harg hfn hbody hfh hR hA in
/-- **The trips of an exit-flag loop, with their events.** From the counter after the label
    with the carried tuple in the carried block, if the iteration of the body within `f`
    runs returns `accN` with the events `ℓ`, the run to the counter after the back-edge
    jump is a traced run with the events `ℓ`: for each run of the body its events followed
    by the branch event of the back edge, which is taken when the flag is set. -/
theorem whileLoop_tripsL : ∀ (f : Nat) (acc accN : Ctxt.Valuation cs) (ℓ : List CTLeak)
    (m : LstateMF),
    whileIterLeak (fun acc => machRun Pj nArgs fn fuel body (d + cs.length) (n + 1)
      (hvAppend acc V)) f acc = some (accN, ℓ) →
    atPc P (A.length + 1) m → StoreAgreesM nArgs d m.prog.base V →
    (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) →
    ∃ (k : Nat) (m' : LstateMF), StepsL P k m m' ℓ
      ∧ atPc P ((A ++ labelI n :: b.code).length + 2 * cs.length + 4 + 1) m'
      ∧ RegionFrame d n m.prog.base m'.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          m'.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN)) := by
  have hcc : flagCondCC? (condI (.reg "NZ") n) = some (false, n) := rfl
  have hreslen := exportR_res_length nArgs fn body _ _ _ hb
  have hfetch : P.body[(A ++ labelI n :: b.code).length + 2 * cs.length + 4]?
      = some (condI (.reg "NZ") n) :=
    fetch_of_body (xs := (A ++ labelI n :: b.code)
        ++ [movImmI (regName (b.depth + cs.length)) 1,
          movImmI (regName (b.depth + cs.length + 1)) 0,
          (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
            [.reg fname, .reg (regName (b.depth + cs.length)),
              .reg (regName (b.depth + cs.length + 1))], .reg none)]
        ++ parMoves b.depth (carriedRegs d cs.length) b.res.tail
        ++ [guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
          [.reg (regName (b.depth + cs.length)), .imm 0])])
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by
        simp only [List.length_append, parMoves_length, carriedRegs_length, List.length_tail,
          hreslen, List.length_cons, List.length_nil]
        omega)
  have hl : findLabelMem n P.body = some A.length := by
    rw [hbody]
    exact findLabelMem_append_labelI n A _ ((findLabelMem_eq_none_iff n A).mp (hA n le_rfl))
  intro f
  induction f with
  | zero =>
      intro acc accN ℓ m h
      simp only [whileIterLeak] at h
      cases h
  | succ f ih =>
      intro acc accN ℓ m h hat hag hblk
      obtain ⟨r, ℓb, hden, hcase⟩ := whileIterLeak_succ_eq_some.mp h
      obtain ⟨k, t, hs, hat2, hfr, hz, hblk'⟩ :=
        whileLoop_tripL Pj nArgs fn body hcs hsim hb hlen harg hfn hbody hfh hR hA fuel V acc r
          ℓb m hden hat hag hblk
      rcases hcase with ⟨hbt, ℓ2, hrest, rfl⟩ | ⟨hbt, rfl, rfl⟩
      · obtain ⟨hs', hat'⟩ := steps_cc_taken hcc hat2 hfetch (by rw [hz, hbt]; rfl) hl
        have hL := stepsL_cc hcc hat2 hfetch hs'
        have hfr' : RegionFrame d n m.prog.base (goto t (A.length + 1)).prog.base :=
          hfr.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
        obtain ⟨k', m', hs'', hat'', hfr'', hblk''⟩ := ih r.tail accN ℓ2
          (goto t (A.length + 1)) hrest hat' (StoreAgreesM.of_regionFrame hlen hag hfr')
          (fun {w} u => hblk' u)
        exact ⟨k + 1 + k', m', ((hs.trans hL).trans hs'').cast (by
            rw [hz, hbt]
            simp),
          hat'', hfr'.trans hfr'' le_rfl le_rfl, fun {w} u => hblk'' u⟩
      · obtain ⟨hs', hat'⟩ := steps_cc_fall hcc hat2 hfetch (by rw [hz, hbt]; decide)
        have hL := stepsL_cc hcc hat2 hfetch hs'
        exact ⟨k + 1, next t, (hs.trans hL).cast (by
            rw [hz, hbt]
            rfl),
          hat', hfr, fun {w} u => hblk' u⟩

end WhileLoopL

/-- **The rule of a loop in exit-flag form.** For carried types held in register cells, the
    statements for the body and for the continuation give the statement for the loop: the
    run emits the events of the trips and the events of the continuation. -/
theorem exportRLeakSim_while (Pj : JLeakParams) (nArgs : Nat) (fn : String)
    {Γ cs : Ctxt jasminDialect} {ts : List JasminTy}
    (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ Γ) (JasminTy.reg 1 :: cs))
    (k : NFProg jasminDialect (cs ++ Γ) ts) (hcs : RegTys cs)
    (hbsim : ExportRLeakSim Pj nArgs fn body) (hksim : ExportRLeakSim Pj nArgs fn k) :
    ExportRLeakSim Pj nArgs fn (NFProg.whileLoop inits body k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V v ℓ m hrun hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rk, hrk, rfl⟩ := h
  simp only [machRun, hb, Option.bind_some] at hrun
  obtain ⟨⟨accN, ℓr⟩, hiter, hkrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨⟨v', ℓk⟩, hkden, heq⟩ := Option.map_eq_some_iff.mp hkrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hbody0 := hbody
  have hLab := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ _ hb
  have hreslen := exportR_res_length nArgs fn body _ _ _ hb
  have hisreg := exportR_res_isReg nArgs fn body _ _ _ hb
  obtain ⟨fname, hfh⟩ : ∃ fname, b.res.headD (.imm 0) = .reg fname := by
    cases hres : b.res with
    | nil => rw [hres] at hreslen; simp at hreslen
    | cons o rest => exact ⟨operandName o, hisreg o (by rw [hres]; exact List.mem_cons_self)⟩
  have htail : b.res.tail.length = cs.length := by
    rw [List.length_tail, hreslen]
    rfl
  obtain ⟨ops, hops⟩ : ∃ ops, ops = exprArgsHV d nArgs argName (fun _ => none) inits := ⟨_, rfl⟩
  have hopslen : ops.length = cs.length := by rw [hops, exprArgsHV_length]
  have hopsreg := exprArgsHV_reg nArgs hlen inits
  rw [← hops] at hopsreg
  -- the layout of the body
  obtain ⟨T, hT⟩ : ∃ T, T = movImmI (regName (b.depth + cs.length)) 1
      :: movImmI (regName (b.depth + cs.length + 1)) 0
      :: (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
        [.reg fname, .reg (regName (b.depth + cs.length)),
          .reg (regName (b.depth + cs.length + 1))], .reg none)
      :: (parMoves b.depth (carriedRegs d cs.length) b.res.tail
        ++ [guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
          [.reg (regName (b.depth + cs.length)), .imm 0]), condI (.reg "NZ") n]) := ⟨_, rfl⟩
  have hTlen : T.length = 2 * cs.length + 4 + 1 := by
    rw [hT]
    simp only [List.length_cons, List.length_append, parMoves_length, carriedRegs_length,
      htail, List.length_nil]
    omega
  have hTlabs : labelsOf T = [] := by
    rw [hT]
    show labelsOf (parMoves b.depth (carriedRegs d cs.length) b.res.tail ++ [_, _]) = []
    rw [labelsOf_append, labelsOf_parMoves]
    rfl
  have hF : whileFrame d n cs.length ops b.code (.reg fname) b.res.tail b.depth
      = seedMoves (carriedRegs d cs.length) ops ++ labelI n :: (b.code ++ T) := by
    rw [hT]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hfh, ← hops, hF]
    at hbody
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ seedMoves (carriedRegs d cs.length) ops := ⟨_, rfl⟩
  have hbodyL : P.body = A ++ labelI n :: (b.code ++ (T ++ (rk.code ++ post))) := by
    rw [hbody, hAd]
    simp only [List.append_assoc, List.cons_append]
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, labelsOf_append, labelsOf_seedMoves, List.append_nil]
  have hAlab : ∀ l, n ≤ l → findLabelMem l A = none := fun l hl => by
    rw [findLabelMem_eq_none_iff, hAlabs, ← findLabelMem_eq_none_iff]
    exact hpre l hl
  have hcar := carriedRegs_length d cs.length
  -- the seeds
  have hbodyS : P.body = pre ++ (List.range cs.length).map (fun j =>
      movI ((carriedRegs d cs.length).getD j "") (.reg (operandName (ops.getD j (.imm 0)))))
      ++ labelI n :: (b.code ++ (T ++ (rk.code ++ post))) := by
    rw [hbodyL, hAd, seedMoves_eq_range _ _ (by rw [hopslen, hcar])
      (fun o ho => (hopsreg o ho).1), hcar]
  obtain ⟨t0, hs0v, hat0, ha0, hm0, ho0⟩ := steps_moves P
    (fun j => (carriedRegs d cs.length).getD j "")
    (fun j => operandName (ops.getD j (.imm 0))) cs.length pre _ m hbodyS hat
    (fun i j hij hj => getD_ne_of_nodup (carriedRegs_nodup _ _) hij (by rw [hcar]; exact hj))
    (fun i j hij hj he => by
      rw [carriedRegs_getD _ _ _ (by omega)] at he
      exact (hopsreg _ (getD_mem_of_lt _ (hopslen ▸ hj))).2 _ (by omega) he)
  have hs0 : StepsL P cs.length m t0 [] := stepsL_of_quiet_le _ _ pre _ m t0 hbodyS
    (fun i hi => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
      exact quietLopn_movReg _ _)
    hat hs0v (by rw [List.length_map, List.length_range])
  have hAlen : A.length = pre.length + cs.length := by
    rw [hAd, List.length_append]
    simp only [seedMoves, List.length_map, List.length_zip, hcar, hopslen, Nat.min_self]
  rw [← hAlen] at hat0
  obtain ⟨hs1, hat1⟩ := steps_label x86Isa (kind := .internal) (l := n) (tag := .reg none)
    hat0 (fetch_of_body hbodyL rfl)
  have hL1 := stepsL_label hat0 (fetch_of_body hbodyL rfl) hs1
  have hfr1 : RegionFrame d n m.prog.base (next t0).prog.base :=
    RegionFrame.of_cells ha0 fun r hr _ => ho0 r fun j hj => by
      rw [carriedRegs_getD _ _ _ hj]
      exact hr _ (by omega)
  have hblkI : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      (next t0).prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup (Expr.lookupArgs inits V)) := fun {w} u => by
    have hu := JasminLsemSimulation.varIndex_lt u
    have h1 := hm0 (varIndex u) hu
    rw [carriedRegs_getD _ _ _ hu] at h1
    rw [show (next t0).prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = t0.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w from rfl,
      getW_of_lvm_eq w h1, hops, exprArgsHV_getD, ← evalOperandN_resolveVar, lookup_lookupArgs]
    exact hag.1 (hvToHom inits u)
  -- the trips
  obtain ⟨k3, m3, hs3, hat3, hfr3, hblk3⟩ :=
    whileLoop_tripsL Pj nArgs fn body hcs hbsim hb hlen harg hfn hbodyL hfh
      (Z := rk.code ++ post) (by rw [hT]; simp only [List.append_assoc, List.cons_append,
        List.nil_append]) hAlab fuel V fuel (Expr.lookupArgs inits V) accN ℓr (next t0) hiter
      hat1 (StoreAgreesM.of_regionFrame hlen hag hfr1) (fun {w} u => hblkI u)
  have hfrS : RegionFrame d n m.prog.base m3.prog.base := hfr1.trans hfr3 le_rfl le_rfl
  have hagS : StoreAgreesM nArgs (d + cs.length) m3.prog.base (hvAppend accN V) :=
    storeAgreesM_append hcs harg (StoreAgreesM.of_regionFrame hlen hag hfrS)
      (fun {w} u => hblk3 u)
  -- the continuation
  have hnext := hLab.le
  obtain ⟨kK, m', hsK, hatK, hresK, hfrK⟩ := hksim (d + cs.length) b.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P
    (A ++ labelI n :: (b.code ++ T)) post hfn
    (by rw [hbodyL]; simp only [List.append_assoc, List.cons_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append, hAlabs, labelsOf_cons_labelI,
        labelsOf_append, hTlabs, List.append_nil]
      simp only [List.mem_append, List.mem_cons, not_or]
      refine ⟨(findLabelMem_eq_none_iff l pre).mp (hpre l (by omega)), fun he => ?_,
        fun hm => ?_⟩
      · have : (l : Nat) = n := he
        omega
      · have := hLab.range _ hm
        omega)
    fuel _ v' ℓk m3 hkden
    (by
      simp only [List.length_append, List.length_cons, hTlen] at hat3 ⊢
      rwa [show A.length + (b.code.length + (2 * cs.length + 4 + 1) + 1)
        = A.length + (b.code.length + 1) + 2 * cs.length + 4 + 1 by omega])
    hagS
  have hlenEq : pre.length + (Exported.prepend (whileFrame d n cs.length
      (exprArgsHV d nArgs argName (fun _ => none) inits) b.code (b.res.headD (.imm 0))
      b.res.tail b.depth) rk).code.length
      = (A ++ labelI n :: (b.code ++ T)).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyL] at h1
    simp only [List.length_append, List.length_cons] at h1 ⊢
    omega
  refine ⟨_, m', (((hs0.trans hL1).trans hs3).trans hsK).cast (by
    simp only [List.nil_append, List.append_nil]), ?_, hresK,
    hfrS.trans hfrK (by omega) (by omega)⟩
  rw [hlenEq]
  exact hatK

/-! ## 8. The traced simulation of the programs without calls -/

/-- **The traced simulation of the region export** on the programs of `RegionExportable`
    without a `call`, by the rules of the return, the binding, the two loops and the
    branch. -/
theorem exportR_leakSim (Pj : JLeakParams) (nArgs : Nat) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) : ExportRLeakSim Pj nArgs fn p := by
  induction p with
  | ret vs => exact exportRLeakSim_ret Pj nArgs fn vs
  | var e k ih => exact exportRLeakSim_var Pj nArgs fn e k hp.1 (ih hp.2 hc)
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      exact exportRLeakSim_for Pj nArgs fn count inits body k (ihb hp.1 hc.1) (ihk hp.2 hc.2)
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      exact exportRLeakSim_if Pj nArgs fn cond thn els k (iht hp.1 hc.1.1)
        (ihe hp.2.1 hc.1.2) (ihk hp.2.2 hc.2)
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      exact exportRLeakSim_while Pj nArgs fn inits body k hp.1 (ihb hp.2.1 hc.1)
        (ihk hp.2.2 hc.2)
  | call f args k ih => simp [NFProg.callFree] at hc

/-! ## 9. The machine events as a function of the source events -/

/-- The run of iterations succeeds when every iteration does. -/
theorem forIterLeak_isSome {cs : List JasminTy}
    {step : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)}
    (h : ∀ i acc, ∃ r, step i acc = some r) :
    ∀ (is : List Nat) (acc : Ctxt.Valuation (d := jasminDialect) cs),
      ∃ r, forIterLeak step is acc = some r
  | [], acc => ⟨_, rfl⟩
  | i :: is, acc => by
      obtain ⟨r, hr⟩ := h i acc
      obtain ⟨q, hq⟩ := forIterLeak_isSome h is r.1
      refine ⟨(q.1, r.2 ++ q.2), ?_⟩
      simp only [forIterLeak, hr, Option.bind_some, hq, Option.map_some]

/-- **The source run of a program without calls and without exit-flag loops succeeds** at
    every valuation. -/
theorem leakRun_isSome (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hc : p.callFree = true)
    (hw : p.whileFree = true) :
    ∀ V : Ctxt.Valuation Γ, ∃ r, NFProg.leakRun (jLeakModel Pj) fuel p V = some r := by
  induction p with
  | ret vs => exact fun V => ⟨_, rfl⟩
  | var e k ih =>
      intro V
      obtain ⟨r, hr⟩ := ih hc hw (V.extend (e.denote V))
      refine ⟨(r.1, Expr.ctLeak (jLeakModel Pj) e V ++ r.2), ?_⟩
      simp only [NFProg.leakRun, hr, Option.map_some]
  | forLoop count inits body k ihb ihk =>
      intro V
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      simp only [NFProg.whileFree, Bool.and_eq_true] at hw
      simp only [NFProg.leakRun]
      obtain ⟨r, hr⟩ := forIterLeak_isSome
        (step := fun i acc => NFProg.leakRun (jLeakModel Pj) fuel body
          (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)))
        (fun i acc => ihb hc.1 hw.1 _)
        (List.range (HasWord64.toNat (d := jasminDialect) (count.lookup V)))
        (Expr.lookupArgs inits V)
      obtain ⟨q, hq⟩ := ihk hc.2 hw.2 (hvAppend r.1 V)
      rw [hr, Option.bind_some, hq]
      exact ⟨_, rfl⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro V
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      simp only [NFProg.whileFree, Bool.and_eq_true] at hw
      simp only [NFProg.leakRun]
      obtain ⟨r, hr⟩ : ∃ r, (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V)
          then NFProg.leakRun (jLeakModel Pj) fuel thn V
          else NFProg.leakRun (jLeakModel Pj) fuel els V) = some r := by
        split
        · exact iht hc.1.1 hw.1.1 V
        · exact ihe hc.1.2 hw.1.2 V
      obtain ⟨q, hq⟩ := ihk hc.2 hw.2 (hvAppend r.1 V)
      rw [hr, Option.bind_some, hq]
      exact ⟨_, rfl⟩
  | whileLoop inits body k ihb ihk => simp [NFProg.whileFree] at hw
  | call f args k ih => simp [NFProg.callFree] at hc

/-- A source run succeeds where the program denotes in the empty call environment. -/
theorem leakRun_eq_some_of_denote (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ)
    (h : (p.denoteAt CallEnv.empty fuel V).isSome = true) :
    ∃ r, NFProg.leakRun (jLeakModel Pj) fuel p V = some r := by
  rw [← NFProg.leakRun_fst (jLeakModel Pj) fuel p V] at h
  cases hL : NFProg.leakRun (jLeakModel Pj) fuel p V with
  | none => rw [hL] at h; cases h
  | some r => exact ⟨r, rfl⟩

/-- **The events of an iteration in exit-flag form factor through the events of each run of
    the body.** When the source events of a run of the body determine where they end in a
    longer list and determine the machine events of the run, the same holds for the
    iteration: two iterations with equal events take the same number of runs. -/
theorem whileIterLeak_factor {cs : List JasminTy}
    {sL₁ sL₂ sM₁ sM₂ : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) (JasminTy.reg 1 :: cs) × List CTLeak)}
    (h : ∀ (acc₁ acc₂ : Ctxt.Valuation (d := jasminDialect) cs)
      (r₁ r₂ : Ctxt.Valuation (d := jasminDialect) (JasminTy.reg 1 :: cs))
      (ℓ₁ ℓ₂ s₁ s₂ : List CTLeak), sL₁ acc₁ = some (r₁, ℓ₁) → sL₂ acc₂ = some (r₂, ℓ₂) →
      ℓ₁ ++ s₁ = ℓ₂ ++ s₂ →
      ℓ₁ = ℓ₂ ∧ s₁ = s₂ ∧ ∃ μ, sM₁ acc₁ = some (r₁, μ) ∧ sM₂ acc₂ = some (r₂, μ)) :
    ∀ (f : Nat) (acc₁ acc₂ a₁ a₂ : Ctxt.Valuation (d := jasminDialect) cs)
      (ℓ₁ ℓ₂ s₁ s₂ : List CTLeak), whileIterLeak sL₁ f acc₁ = some (a₁, ℓ₁) →
      whileIterLeak sL₂ f acc₂ = some (a₂, ℓ₂) → ℓ₁ ++ s₁ = ℓ₂ ++ s₂ →
      ℓ₁ = ℓ₂ ∧ s₁ = s₂
        ∧ ∃ μ, whileIterLeak sM₁ f acc₁ = some (a₁, μ)
          ∧ whileIterLeak sM₂ f acc₂ = some (a₂, μ)
  | 0, _, _, _, _, _, _, _, _, h₁, _, _ => by
      simp only [whileIterLeak] at h₁
      cases h₁
  | f + 1, acc₁, acc₂, a₁, a₂, ℓ₁, ℓ₂, s₁, s₂, h₁, h₂, hs => by
      obtain ⟨r₁, t₁, e₁, c₁⟩ := whileIterLeak_succ_eq_some.mp h₁
      obtain ⟨r₂, t₂, e₂, c₂⟩ := whileIterLeak_succ_eq_some.mp h₂
      rcases c₁ with ⟨b₁, u₁, w₁, rfl⟩ | ⟨b₁, rfl, rfl⟩ <;>
        rcases c₂ with ⟨b₂, u₂, w₂, rfl⟩ | ⟨b₂, rfl, rfl⟩
      · rw [List.append_assoc, List.append_assoc] at hs
        obtain ⟨ht, hs', μ, m₁, m₂⟩ := h acc₁ acc₂ r₁ r₂ t₁ t₂ _ _ e₁ e₂ hs
        simp only [List.cons_append, List.cons.injEq, true_and] at hs'
        obtain ⟨hu, hs'', ν, n₁, n₂⟩ :=
          whileIterLeak_factor h f r₁.tail r₂.tail a₁ a₂ u₁ u₂ s₁ s₂ w₁ w₂ hs'
        exact ⟨by rw [ht, hu], hs'', μ ++ CTLeak.branch true :: ν,
          whileIterLeak_succ_eq_some.mpr ⟨r₁, μ, m₁, Or.inl ⟨b₁, ν, n₁, rfl⟩⟩,
          whileIterLeak_succ_eq_some.mpr ⟨r₂, μ, m₂, Or.inl ⟨b₂, ν, n₂, rfl⟩⟩⟩
      · rw [List.append_assoc, List.append_assoc] at hs
        obtain ⟨-, hs', -⟩ := h acc₁ acc₂ r₁ r₂ t₁ t₂ _ _ e₁ e₂ hs
        simp at hs'
      · rw [List.append_assoc, List.append_assoc] at hs
        obtain ⟨-, hs', -⟩ := h acc₁ acc₂ r₁ r₂ t₁ t₂ _ _ e₁ e₂ hs
        simp at hs'
      · rw [List.append_assoc, List.append_assoc] at hs
        obtain ⟨ht, hs', μ, m₁, m₂⟩ := h acc₁ acc₂ r₁ r₂ t₁ t₂ _ _ e₁ e₂ hs
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at hs'
        exact ⟨by rw [ht], hs', μ ++ [CTLeak.branch false],
          whileIterLeak_succ_eq_some.mpr ⟨r₁, μ, m₁, Or.inr ⟨b₁, rfl, rfl⟩⟩,
          whileIterLeak_succ_eq_some.mpr ⟨r₂, μ, m₂, Or.inr ⟨b₂, rfl, rfl⟩⟩⟩

/-- **The events of iterations factor through the events of each iteration.** When the
    source events of an iteration determine where they end in a longer list and determine
    the machine events of the iteration, the same holds for the run of the iterations. -/
theorem forIterLeak_factor {cs : List JasminTy}
    {sL₁ sL₂ sM₁ sM₂ : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)}
    (h : ∀ (i : Nat) (acc₁ acc₂ a₁ a₂ : Ctxt.Valuation (d := jasminDialect) cs)
      (ℓ₁ ℓ₂ s₁ s₂ : List CTLeak), sL₁ i acc₁ = some (a₁, ℓ₁) → sL₂ i acc₂ = some (a₂, ℓ₂) →
      ℓ₁ ++ s₁ = ℓ₂ ++ s₂ →
      ℓ₁ = ℓ₂ ∧ s₁ = s₂ ∧ ∃ μ, sM₁ i acc₁ = some (a₁, μ) ∧ sM₂ i acc₂ = some (a₂, μ)) :
    ∀ (is : List Nat) (acc₁ acc₂ a₁ a₂ : Ctxt.Valuation (d := jasminDialect) cs)
      (ℓ₁ ℓ₂ s₁ s₂ : List CTLeak), forIterLeak sL₁ is acc₁ = some (a₁, ℓ₁) →
      forIterLeak sL₂ is acc₂ = some (a₂, ℓ₂) → ℓ₁ ++ s₁ = ℓ₂ ++ s₂ →
      ℓ₁ = ℓ₂ ∧ s₁ = s₂
        ∧ ∃ μ, forIterLeak sM₁ is acc₁ = some (a₁, μ) ∧ forIterLeak sM₂ is acc₂ = some (a₂, μ)
  | [], acc₁, acc₂, a₁, a₂, ℓ₁, ℓ₂, s₁, s₂, h₁, h₂, hs => by
      simp only [forIterLeak, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, hs, [], rfl, rfl⟩
  | i :: is, acc₁, acc₂, a₁, a₂, ℓ₁, ℓ₂, s₁, s₂, h₁, h₂, hs => by
      obtain ⟨b₁, t₁, u₁, e₁, r₁, rfl⟩ := forIterLeak_cons_eq_some.mp h₁
      obtain ⟨b₂, t₂, u₂, e₂, r₂, rfl⟩ := forIterLeak_cons_eq_some.mp h₂
      rw [List.append_assoc, List.append_assoc] at hs
      obtain ⟨ht, hs', μ, m₁, m₂⟩ := h i acc₁ acc₂ b₁ b₂ t₁ t₂ _ _ e₁ e₂ hs
      obtain ⟨hu, hs'', ν, n₁, n₂⟩ :=
        forIterLeak_factor h is b₁ b₂ a₁ a₂ u₁ u₂ s₁ s₂ r₁ r₂ hs'
      exact ⟨by rw [ht, hu], hs'', μ ++ ν,
        forIterLeak_cons_eq_some.mpr ⟨b₁, μ, ν, m₁, n₁, rfl⟩,
        forIterLeak_cons_eq_some.mpr ⟨b₂, μ, ν, m₂, n₂, rfl⟩⟩

/-- **The source events of a program without calls determine its machine events.** For two
    source runs whose events, each followed by a list, are equal: the events are equal, the
    lists are equal, and `machRun` returns the results of the source runs with one list of
    machine events. Two runs with equal source events take the same arm of every branch
    and the same number of trips of every loop. -/
theorem machRun_of_leakRun (Pj : JLeakParams) (nArgs : Nat) (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) :
    ∀ (d n : Nat) (V₁ V₂ : Ctxt.Valuation Γ) (v₁ v₂ : Ctxt.Valuation (d := jasminDialect) ts)
      (ℓ₁ ℓ₂ s₁ s₂ : List CTLeak),
      NFProg.leakRun (jLeakModel Pj) fuel p V₁ = some (v₁, ℓ₁) →
      NFProg.leakRun (jLeakModel Pj) fuel p V₂ = some (v₂, ℓ₂) → ℓ₁ ++ s₁ = ℓ₂ ++ s₂ →
      ℓ₁ = ℓ₂ ∧ s₁ = s₂
        ∧ ∃ μ, machRun Pj nArgs fn fuel p d n V₁ = some (v₁, μ)
          ∧ machRun Pj nArgs fn fuel p d n V₂ = some (v₂, μ) := by
  induction p with
  | ret vs =>
      intro d n V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hs
      simp only [NFProg.leakRun, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, hs, [], rfl, rfl⟩
  | var e k ih =>
      intro d n V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hs
      simp only [NFProg.leakRun, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at h₁ h₂
      obtain ⟨a₁, t₁, hk₁, rfl, rfl⟩ := h₁
      obtain ⟨a₂, t₂, hk₂, rfl, rfl⟩ := h₂
      rw [List.append_assoc, List.append_assoc] at hs
      obtain ⟨he, hrest⟩ := List.append_inj hs
        (by rw [exprCtLeak_length, exprCtLeak_length])
      obtain ⟨ht, hss, μ, hm₁, hm₂⟩ := ih hp.2 hc (d + 1) n _ _ _ _ _ _ _ _ hk₁ hk₂ hrest
      refine ⟨by rw [he, ht], hss, bindLeak Pj nArgs e d V₁ ++ μ, ?_, ?_⟩
      · simp only [machRun, hm₁, Option.map_some]
      · simp only [machRun, hm₂, Option.map_some, bindLeak, he]
  | forLoop count inits body k ihb ihk =>
      rename_i Γ' cs ts'
      intro d n V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hs
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      obtain ⟨b, hb⟩ := hp.1.exportR_eq_some nArgs fn (d + 1 + cs.length) (n + 2)
      simp only [NFProg.leakRun, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.mk.injEq, Prod.exists] at h₁ h₂
      obtain ⟨a₁, t₁, hi₁, c₁, u₁, hk₁, rfl, rfl⟩ := h₁
      obtain ⟨a₂, t₂, hi₂, c₂, u₂, hk₂, rfl, rfl⟩ := h₂
      simp only [List.cons_append, List.cons.injEq, CTLeak.trip.injEq, List.append_assoc] at hs
      obtain ⟨hN, hs⟩ := hs
      have hN' : BitVec.toNat (count.lookup V₁) = BitVec.toNat (count.lookup V₂) := hN
      rw [← hN] at hi₂
      obtain ⟨ht, hs', μ, hm₁, hm₂⟩ := forIterLeak_factor
        (sM₁ := tripLeak (forTailLeak d cs b) (BitVec.toNat (count.lookup V₁)) fun i acc =>
          machRun Pj nArgs fn fuel body (d + 1 + cs.length) (n + 2)
            (hvAppend acc (.cons (BitVec.ofNat 64 i) V₁)))
        (sM₂ := tripLeak (forTailLeak d cs b) (BitVec.toNat (count.lookup V₁)) fun i acc =>
          machRun Pj nArgs fn fuel body (d + 1 + cs.length) (n + 2)
            (hvAppend acc (.cons (BitVec.ofNat 64 i) V₂)))
        (fun i acc₁ acc₂ b₁ b₂ x₁ x₂ y₁ y₂ e₁ e₂ es => by
          obtain ⟨hl, hss, μ, m₁, m₂⟩ :=
            ihb hp.1 hc.1 (d + 1 + cs.length) (n + 2) _ _ _ _ _ _ _ _ e₁ e₂ es
          exact ⟨hl, hss, _, tripLeak_eq_some.mpr ⟨μ, m₁, rfl⟩,
            tripLeak_eq_some.mpr ⟨μ, m₂, rfl⟩⟩)
        _ _ _ _ _ _ _ _ _ hi₁ hi₂ hs
      obtain ⟨hu, hss, ν, hn₁, hn₂⟩ :=
        ihk hp.2 hc.2 (d + cs.length) b.next _ _ _ _ _ _ _ _ hk₁ hk₂ hs'
      refine ⟨by rw [hN, ht, hu], hss,
        forHeadLeak nArgs d inits ++ .branch (decide (BitVec.toNat (count.lookup V₁) = 0))
          :: (μ ++ (forShiftLeak d cs ++ ν)), ?_, ?_⟩
      · simp only [machRun, hb, Option.bind_some]
        exact Option.bind_eq_some_iff.mpr ⟨(a₁, μ), hm₁, by rw [hn₁]; rfl⟩
      · simp only [machRun, hb, Option.bind_some]
        rw [← hN']
        exact Option.bind_eq_some_iff.mpr ⟨(a₂, μ), hm₂, by rw [hn₂]; rfl⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      rename_i Γ' rs ts'
      intro d n V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hs
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      obtain ⟨t, ht⟩ := hp.1.exportR_eq_some nArgs fn d (n + 3)
      obtain ⟨e, he⟩ := hp.2.1.exportR_eq_some nArgs fn d t.next
      simp only [NFProg.leakRun, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.mk.injEq, Prod.exists] at h₁ h₂
      obtain ⟨a₁, t₁, hi₁, c₁, u₁, hk₁, rfl, rfl⟩ := h₁
      obtain ⟨a₂, t₂, hi₂, c₂, u₂, hk₂, rfl, rfl⟩ := h₂
      simp only [List.cons_append, List.cons.injEq, CTLeak.branch.injEq,
        List.append_assoc] at hs
      obtain ⟨hB, hs⟩ := hs
      rw [← hB] at hi₂
      obtain ⟨hta, hs', μ, hm₁, hm₂⟩ : t₁ = t₂ ∧ u₁ ++ s₁ = u₂ ++ s₂ ∧ ∃ μ,
          (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁)
            then machRun Pj nArgs fn fuel thn d (n + 3) V₁
            else machRun Pj nArgs fn fuel els d t.next V₁) = some (a₁, μ)
          ∧ (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁)
            then machRun Pj nArgs fn fuel thn d (n + 3) V₂
            else machRun Pj nArgs fn fuel els d t.next V₂) = some (a₂, μ) := by
        by_cases hbt : HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁) = true
        · rw [if_pos hbt] at hi₁ hi₂
          rw [if_pos hbt, if_pos hbt]
          exact iht hp.1 hc.1.1 d (n + 3) _ _ _ _ _ _ _ _ hi₁ hi₂ hs
        · rw [if_neg hbt] at hi₁ hi₂
          rw [if_neg hbt, if_neg hbt]
          exact ihe hp.2.1 hc.1.2 d t.next _ _ _ _ _ _ _ _ hi₁ hi₂ hs
      obtain ⟨hu, hss, ν, hn₁, hn₂⟩ :=
        ihk hp.2.2 hc.2 (d + rs.length) e.next _ _ _ _ _ _ _ _ hk₁ hk₂ hs'
      refine ⟨by rw [hB, hta, hu], hss,
        .branch (!HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁))
          :: (μ ++ (ifResLeak d rs
            (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁) then t else e)
            ++ ((if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁)
              then [CTLeak.branch true] else []) ++ ν))), ?_, ?_⟩
      · simp only [machRun, ht, he, Option.bind_some]
        exact Option.bind_eq_some_iff.mpr ⟨(a₁, μ), hm₁, by rw [hn₁]; rfl⟩
      · simp only [machRun, ht, he, Option.bind_some]
        rw [← hB]
        exact Option.bind_eq_some_iff.mpr ⟨(a₂, μ), hm₂, by rw [hn₂]; rfl⟩
  | whileLoop inits body k ihb ihk =>
      rename_i Γ' cs ts'
      intro d n V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hs
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      obtain ⟨b, hb⟩ := hp.2.1.exportR_eq_some nArgs fn (d + cs.length) (n + 1)
      simp only [NFProg.leakRun, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.mk.injEq, Prod.exists] at h₁ h₂
      obtain ⟨a₁, t₁, hi₁, c₁, u₁, hk₁, rfl, rfl⟩ := h₁
      obtain ⟨a₂, t₂, hi₂, c₂, u₂, hk₂, rfl, rfl⟩ := h₂
      rw [List.append_assoc, List.append_assoc] at hs
      obtain ⟨ht, hs', μ, hm₁, hm₂⟩ := whileIterLeak_factor
        (sM₁ := fun acc => machRun Pj nArgs fn fuel body (d + cs.length) (n + 1)
          (hvAppend acc V₁))
        (sM₂ := fun acc => machRun Pj nArgs fn fuel body (d + cs.length) (n + 1)
          (hvAppend acc V₂))
        (fun acc₁ acc₂ r₁ r₂ x₁ x₂ y₁ y₂ e₁ e₂ es =>
          ihb hp.2.1 hc.1 (d + cs.length) (n + 1) _ _ _ _ _ _ _ _ e₁ e₂ es)
        fuel _ _ _ _ _ _ _ _ hi₁ hi₂ hs
      obtain ⟨hu, hss, ν, hn₁, hn₂⟩ :=
        ihk hp.2.2 hc.2 (d + cs.length) b.next _ _ _ _ _ _ _ _ hk₁ hk₂ hs'
      refine ⟨by rw [ht, hu], hss, μ ++ ν, ?_, ?_⟩
      · simp only [machRun, hb, Option.bind_some]
        exact Option.bind_eq_some_iff.mpr ⟨(a₁, μ), hm₁, by rw [hn₁]; rfl⟩
      · simp only [machRun, hb, Option.bind_some]
        exact Option.bind_eq_some_iff.mpr ⟨(a₂, μ), hm₂, by rw [hn₂]; rfl⟩
  | call f args k ih => simp [NFProg.callFree] at hc

/-! ## 10. The leakage of the exported code and constant time -/

/-- An entry state of the exported code of the function `fn` at depth `d`: in the function,
    at the counter `0`, with a store that agrees with `V`. -/
def RegionEntry (nArgs : Nat) (fn : String) (d : Nat) {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) (s : LstateMF) : Prop :=
  s.prog.lfn = fn ∧ s.prog.base.lpc = 0 ∧ StoreAgreesM nArgs d s.prog.base V

/-- Two entry states of the exported code whose stores agree with valuations that are equal
    on the positions `L` marks public. -/
def RegionEntryPub (nArgs : Nat) (fn : String) (d : Nat) {Γ : Ctxt jasminDialect}
    (L : Labels Γ) (s₁ s₂ : LstateMF) : Prop :=
  ∃ V₁ V₂ : Ctxt.Valuation Γ, PubEqV L V₁ V₂ ∧ RegionEntry nArgs fn d V₁ s₁
    ∧ RegionEntry nArgs fn d V₂ s₂

/-- Two entry states of the exported code whose stores agree with valuations that are equal
    on the positions `L` marks public and at the first of which the program `p` denotes
    within `fuel` in the empty call environment. -/
def RegionEntryPubDen (nArgs : Nat) (fn : String) (fuel d : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (L : Labels Γ)
    (s₁ s₂ : LstateMF) : Prop :=
  ∃ V₁ V₂ : Ctxt.Valuation Γ, PubEqV L V₁ V₂ ∧ RegionEntry nArgs fn d V₁ s₁
    ∧ RegionEntry nArgs fn d V₂ s₂ ∧ (p.denoteAt CallEnv.empty fuel V₁).isSome = true

/-- **The events of the exported code.** For a program of `RegionExportable` without a
    `call`, exported at the depth of its context, every terminating traced run of the code
    from an entry state that agrees with `V` has the events of `machRun` at `V`, at every
    fuel at which `machRun` returns. -/
theorem exportR_leak_of_machRun (Pj : JLeakParams) {nArgs : Nat} {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n = some r) (hlen : Γ.length = d) (harg : nArgs ≤ d)
    {fuel : Nat} {V : Ctxt.Valuation Γ} {v : Ctxt.Valuation (d := jasminDialect) ts}
    {μ : List CTLeak} (hm : machRun Pj nArgs fn fuel p d n V = some (v, μ))
    {s : LstateMF} {ℓ : List CTLeak}
    (hent : RegionEntry nArgs fn d V s) (hrun : FRun (singletonProgM fn r.code) s ℓ) :
    ℓ = μ := by
  obtain ⟨k, m', hs, hat', -, -⟩ := exportR_leakSim Pj nArgs fn hp hc d n r hr hlen harg
    (singletonProgM fn r.code) [] [] rfl (by simp [singletonProgM])
    (fun l _ => (findLabelMem_eq_none_iff l []).mpr (by simp [labelsOf])) fuel V v μ s hm
    ⟨hent.1, hent.2.1⟩ hent.2.2
  have hF := fRun_of_stepsL hs (halted_of_atPc hat' (by simp [singletonProgM]))
  exact fRun_unique hrun hF

/-- **The leakage of the exported code.** For a program of `RegionExportable` without a
    `call`, exported at the depth of its context, and a valuation `V` at which the source
    run succeeds within `fuel`: every terminating traced run of the code from an entry
    state that agrees with `V` has the events `machLeak` at `V`. -/
theorem exportR_leak (Pj : JLeakParams) {nArgs : Nat} {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n = some r) (hlen : Γ.length = d) (harg : nArgs ≤ d)
    {fuel : Nat} {V : Ctxt.Valuation Γ} {x : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak}
    (hsrc : NFProg.leakRun (jLeakModel Pj) fuel p V = some x)
    {s : LstateMF} {ℓ : List CTLeak}
    (hent : RegionEntry nArgs fn d V s) (hrun : FRun (singletonProgM fn r.code) s ℓ) :
    machLeak Pj nArgs fn fuel p d n V = some ℓ := by
  obtain ⟨v, t⟩ := x
  obtain ⟨-, -, μ, hm, -⟩ :=
    machRun_of_leakRun Pj nArgs fn fuel hp hc d n V V v v t t [] [] hsrc hsrc rfl
  rw [machLeak, hm, exportR_leak_of_machRun Pj hp hc hr hlen harg hm hent hrun]
  rfl

/-- **Constant time of the exported code from constant time of the program.** A program of
    `RegionExportable` without a `call` that is constant time at the source events for the
    entry labels `L` at `fuel` has exported code that is constant time on the traced flag
    machine between entry states whose stores agree with valuations that are equal on the
    public positions and at the first of which the program denotes within `fuel`. -/
theorem exportR_memFCT (Pj : JLeakParams) {nArgs : Nat} {fn : String} (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ}
    (hct : NFCT (jLeakModel Pj) L fuel p)
    {d n : Nat} {r : Exported} (hr : exportR nArgs fn p d n = some r) (hlen : Γ.length = d)
    (harg : nArgs ≤ d) :
    MemFCT (singletonProgM fn r.code) (RegionEntryPubDen nArgs fn fuel d p L) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨V₁, V₂, hpub, e₁, e₂, hden⟩ r₁ r₂
  obtain ⟨⟨v₁, t₁⟩, h₁⟩ := leakRun_eq_some_of_denote Pj fuel p V₁ hden
  have hnf := hct V₁ V₂ hpub
  rw [h₁] at hnf
  cases h₂ : NFProg.leakRun (jLeakModel Pj) fuel p V₂ with
  | none => rw [h₂] at hnf; cases hnf
  | some x₂ =>
      obtain ⟨v₂, t₂⟩ := x₂
      rw [h₂] at hnf
      obtain rfl : t₁ = t₂ := Option.some.inj hnf
      obtain ⟨-, -, μ, m₁, m₂⟩ :=
        machRun_of_leakRun Pj nArgs fn fuel hp hc d n V₁ V₂ v₁ v₂ t₁ t₁ [] [] h₁ h₂ rfl
      rw [exportR_leak_of_machRun Pj hp hc hr hlen harg m₁ e₁ r₁,
        exportR_leak_of_machRun Pj hp hc hr hlen harg m₂ e₂ r₂]

/-- **Constant time of the exported code of a program without exit-flag loops.** A program
    of `RegionExportable` without a `call` and without a `whileLoop` that is constant time
    at the source events for the entry labels `L` has exported code that is constant time
    on the traced flag machine between entry states whose stores agree with valuations
    equal on the public positions. -/
theorem exportR_memFCT_whileFree (Pj : JLeakParams) {nArgs : Nat} {fn : String} (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) (hw : p.whileFree = true)
    {L : Labels Γ} (hct : NFCT (jLeakModel Pj) L fuel p)
    {d n : Nat} {r : Exported} (hr : exportR nArgs fn p d n = some r) (hlen : Γ.length = d)
    (harg : nArgs ≤ d) :
    MemFCT (singletonProgM fn r.code) (RegionEntryPub nArgs fn d L) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨V₁, V₂, hpub, e₁, e₂⟩ r₁ r₂
  obtain ⟨x, hx⟩ := leakRun_isSome Pj fuel hc hw V₁
  refine exportR_memFCT Pj fuel hp hc hct hr hlen harg s₁ s₂ ℓ₁ ℓ₂
    ⟨V₁, V₂, hpub, e₁, e₂, ?_⟩ r₁ r₂
  rw [← NFProg.leakRun_fst (jLeakModel Pj) fuel p V₁, hx]
  rfl

/-! ## 11. From an ABI entry -/

section Abi

open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- **Constant time of the exported code from ABI entries.** A program of
    `RegionExportable` without a `call` and without a `whileLoop` that is constant time at
    the source events for the entry labels `L`, exported with its context as the arguments,
    has code that is constant time on the traced flag machine from the flag-machine entries
    of two ABI entries whose valuations agree on the public labels (`AbiEntryCT`). -/
theorem exportR_abiEntryCT (Pj : JLeakParams) {fn : String} (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) (hw : p.whileFree = true)
    {L : Labels Γ} (hct : NFCT (jLeakModel Pj) L fuel p) {n : Nat} {r : Exported}
    (hr : exportR Γ.length fn p Γ.length n = some r) (σ : AbiLayout) :
    AbiEntryCT (singletonProgM fn r.code) fn σ L := by
  rintro ⟨sa₁, V₁, b₁⟩ ⟨sa₂, V₂, b₂⟩ ℓ₁ ℓ₂ ⟨hV₁, hb₁, hV₂, hb₂, hpub⟩ r₁ r₂
  exact exportR_memFCT_whileFree Pj fuel hp hc hw hct hr rfl (le_refl _) _ _ ℓ₁ ℓ₂
    ⟨V₁, V₂, hpub, ⟨rfl, hb₁.pc, storeAgreesM_of_abi hV₁ hb₁⟩,
      ⟨rfl, hb₂.pc, storeAgreesM_of_abi hV₂ hb₂⟩⟩ r₁ r₂

end Abi

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
