/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-!
# The leakage of the region export

The machine leakage of the code `exportR` emits for a structured program, as a function of
the program and the entry valuation, and its preservation by the export on the fragment of
bindings, returns and counted loops whose carried tuple holds registers.

A traced run of `k` steps is `StepsL P k s t ℓ`: the run `Steps x86Isa P k s t` together
with the events `stepsLeak P k s = ℓ` of the instructions it fetches, in the event model
`instrLeakF` of the traced flag machine `lsemFuelMemFLeak`. The events are a function of
the program, the number of steps and the entry state, and a traced run to a halted state
is the terminating run of `lsemFuelMemFLeak` with the same events.

`machRun Pj nArgs p d V` runs `p` from `V` at depth `d` and returns its results with the
machine events of its export:

* a binding emits `bindLeak`: for a `stackLoad` or `stackStore`, the address event of its
  source event at the array name and with the scaled index of its instruction, and
  nothing for every other operation;
* a counted loop with trip count `N` whose carried types are held in registers emits
  `branch (N = 0)` for the zero-trip guard, then for each trip `i` the events of the body
  followed by `branch (i + 1 < N)` for the back edge, then the events of the continuation;
  it emits no event of the trip count;
* a counted loop that carries an array, a branch, a loop in exit-flag form and a call
  return `none`.

A run of a straight segment of instructions that emit nothing is obtained from the value
lemma of the segment: the lemma is applied to the program cut after the segment, in which
a run that reaches the end of the segment has the length of the segment, and the run is
moved to the full program (`stepsL_of_quiet`).

## Main definitions

* `stepsLeak`, `StepsL`: the events of a run of steps and the traced run.
* `bindLeak`, `tripLeak`, `machRun`, `machLeak`: the machine events of an exported program.
* `ExportRLeakSim`: the simulation statement of `ExportRSim` with the events of the run.
* `RegLoopFragment`: bindings of the stack-memory fragment, returns and counted loops whose
  carried types are held in registers.
* `RegionEntry`, `RegionEntryPub`: entry states of the exported code that agree with a
  valuation, and pairs of them at valuations equal on the public positions.

## Main results

* `lsemFuelMemFLeak_stepsL`: a traced run of steps in front of a traced run of the flag
  machine.
* `stepsL_of_quiet`: a run of a segment of instructions that emit nothing, in the program
  cut after the segment, is a traced run of the full program with no event.
* `exportRLeakSim_ret`, `exportRLeakSim_var`, `exportRLeakSim_forReg`: the rules of the
  return, the binding and the counted loop with carried registers.
* `exportR_leakSim`: the traced simulation on `RegLoopFragment`.
* `exportR_leak_forReg`: every terminating traced run of the exported code from an entry
  state that agrees with `V` has the events `machLeak` at `V`.
* `machLeak_eq_of_leakRun_eq`: valuations with equal source events have equal machine
  events.
* `exportR_memFCT`: a program of the fragment that is constant time at the source events
  (`NFCT`) has exported code that is constant time on the traced flag machine (`MemFCT`)
  between entry states that agree with valuations equal on the public positions.
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

/-- The moves of a list of typed pairs with no array move are quiet. -/
theorem quietLopn_typedMoves (z t : String) {tp : List (JasminTy × String × String)}
    (h : arrPairs tp = []) : ∀ i ∈ typedMoves z t tp, QuietLopn i := by
  intro i hi
  simp only [typedMoves, h, arrMoves, List.flatMap_nil, List.nil_append] at hi
  exact quietLopn_regMoves _ i hi

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
    body followed by the branch event of the back edge, which is taken when a trip
    remains. -/
def tripLeak {cs : List JasminTy} (N : Nat)
    (bodyRun : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak))
    (i : Nat) (acc : Ctxt.Valuation (d := jasminDialect) cs) :
    Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak) :=
  (bodyRun i acc).map fun r => (r.1, r.2 ++ [CTLeak.branch (decide (i + 1 < N))])

/-- **The run of a program with the machine events of its export** at depth `d`, from the
    valuation `V`. A counted loop that carries an array, a branch, a loop in exit-flag form
    and a call return `none`. -/
def machRun (Pj : JLeakParams) (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Nat →
    Ctxt.Valuation Γ → Option (Ctxt.Valuation (d := jasminDialect) ts × List CTLeak)
  | _, _, .ret vs, _, V => some (Expr.lookupArgs vs V, [])
  | _, _, .var e k, d, V =>
      (machRun Pj nArgs k (d + 1) (V.extend (e.denote V))).map fun r =>
        (r.1, bindLeak Pj nArgs e d V ++ r.2)
  | _, _, .forLoop (cs := cs) count inits body k, d, V =>
      if RegTys cs then
        (forIterLeak
            (tripLeak (BitVec.toNat (count.lookup V)) fun i acc =>
              machRun Pj nArgs body (d + 1 + cs.length)
                (hvAppend acc (.cons (BitVec.ofNat 64 i) V)))
            (List.range (BitVec.toNat (count.lookup V))) (Expr.lookupArgs inits V)).bind fun r =>
          (machRun Pj nArgs k (d + cs.length) (hvAppend r.1 V)).map fun q =>
            (q.1, .branch (decide (BitVec.toNat (count.lookup V) = 0)) :: (r.2 ++ q.2))
      else none
  | _, _, .ifThenElse .., _, _ => none
  | _, _, .whileLoop .., _, _ => none
  | _, _, .call .., _, _ => none

/-- **The machine events of an exported program** at depth `d`, from the valuation `V`. -/
def machLeak (Pj : JLeakParams) (nArgs : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (d : Nat) (V : Ctxt.Valuation Γ) : Option (List CTLeak) :=
  (machRun Pj nArgs p d V).map Prod.snd

/-- **The simulation statement of the region export with events.** The statement of
    `ExportRSim` on the x86 flag machine with the run `machRun` in place of the denotation:
    when `machRun` returns `v` with the events `ℓ` at `V`, the run of steps to the counter
    after the code is a traced run with the events `ℓ`. -/
def ExportRLeakSim (Pj : JLeakParams) (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) : Prop :=
  ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n = some r → Γ.length = d → nArgs ≤ d →
  ∀ (P : LprogM) (pre post : List LinstrRM), P.lfn = fn → P.body = pre ++ r.code ++ post →
    (∀ l, n ≤ l → findLabelMem l pre = none) →
  ∀ (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) ts) (ℓ : List CTLeak)
    (m : LstateMF),
    machRun Pj nArgs p d V = some (v, ℓ) → atPc P pre.length m →
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
  intro d n r h hlen _ P pre post _ _ _ V v ℓ m hrun hat hag
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
  intro d n r h hlen harg P pre post hfn hbody hpre V v ℓ m hrun hat hag
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
    _ v' ℓk (setBase m (withALUFlags i m.prog.base st')) hkrun
    (by rw [List.length_append, List.length_singleton]; exact hat1)
    (StoreAgreesM.withALUFlags i m.prog.base hAg')
  refine ⟨1 + k', m', hL1.trans hs2, ?_, hres, ?_⟩
  · rw [hcode, List.length_cons]
    rw [List.length_append, List.length_singleton] at hat2
    rwa [show pre.length + (rk.code.length + 1) = pre.length + 1 + rk.code.length by omega]
  · exact ((RegionFrame.of_writeFrame n hFr).withALUFlags i _).trans hfr2 (by omega) le_rfl

/-! ## 5. The straight segments of a counted loop with carried registers -/

/-- **The head of a counted loop with carried registers, with its events.** The run of
    `forArrHead_steps` is a traced run with no event. -/
theorem forRegHead_stepsL {P : LprogM} {d n : Nat} {cs : Ctxt jasminDialect} (hcs : RegTys cs)
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
    ∃ (k : Nat) (u : LstateMF), StepsL P k s u []
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
  obtain ⟨seg, hseg⟩ : ∃ seg, seg = movImmI (regName d) 0
      :: typedMoves (regName d) (regName (d + 1 + cs.length)) tp
    ++ [movI (loopCtr n) (.reg cn),
      guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])] :=
    ⟨_, rfl⟩
  have hq : ∀ i ∈ seg, QuietLopn i := by
    intro i hi
    rw [hseg] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi) | rfl | rfl
    · exact quietLopn_movImm _ _
    · exact quietLopn_typedMoves _ _ (by rw [htp]; exact arrPairs_carriedPairs hcs _ _) i hi
    · exact quietLopn_movReg _ _
    · exact quietLopn_cmp _
  have hbP : P.body = pre ++ seg ++ post := by
    rw [hbody, hseg]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨k, u, hs, hat', rest⟩ := forArrHead_steps
    (P := singletonProgM P.lfn (pre ++ seg)) (d := d) (n := n) htp pre [] s (cnt := cnt)
    (by
      show pre ++ seg = _
      rw [hseg]
      simp only [List.append_assoc, List.cons_append])
    hat hlen hops hcn hcnt hsrc
  refine ⟨seg.length, u, stepsL_of_quiet hbP hq hat hs ?_, ⟨hat'.1, hat'.2⟩, rest⟩
  rw [hat'.2, hseg]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **The tail of a counted trip with carried registers, with its events.** The run of
    `forArrTail_steps` is a traced run with no event. -/
theorem forRegTail_stepsL {P : LprogM} {d n bD : Nat} {cs : Ctxt jasminDialect}
    (hcs : RegTys cs)
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
    ∃ (k : Nat) (u : LstateMF), StepsL P k s u []
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
  have ha : arrPairs tp = [] := by rw [htp]; exact arrPairs_carriedPairs hcs _ _
  obtain ⟨seg, hseg⟩ : ∃ seg, seg = movImmI (regName (bD + 1)) 0
        :: arrParMoves (regName (bD + 1)) (regName bD) bD (arrPairs tp)
      ++ parMoves bD ((regPairs tp).map Prod.fst) ((regPairs tp).map fun p => .reg p.2)
      ++ (advanceOps (regName d) (loopCtr n)
      ++ [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
        [.reg (loopCtr n), .imm 0])]) := ⟨_, rfl⟩
  have hq : ∀ i ∈ seg, QuietLopn i := by
    intro i hi
    rw [hseg] at hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | hi) | hi) | hi | rfl
    · exact quietLopn_movImm _ _
    · simp [ha, arrParMoves, arrMoves] at hi
    · refine quietLopn_parMoves _ _ _ (fun o ho => ?_) i hi
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
      exact ⟨_, rfl⟩
    · exact quietLopn_advanceOps _ _ i hi
    · exact quietLopn_cmp _
  have hbP : P.body = pre ++ seg ++ post := by
    rw [hbody, hseg]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨k, u, hs, hat', rest⟩ := forArrTail_steps
    (P := singletonProgM P.lfn (pre ++ seg)) (d := d) (n := n) (bD := bD) htp pre [] s
    (x := x) (c := c)
    (by
      show pre ++ seg = _
      rw [hseg]
      simp only [List.append_assoc, List.cons_append])
    hat hlen hD hops hx hc hsrc
  refine ⟨seg.length, u, stepsL_of_quiet hbP hq hat hs ?_, ⟨hat'.1, hat'.2⟩, rest⟩
  rw [hat'.2, hseg]
  simp only [List.length_append, List.length_cons, List.length_nil, advanceOps]
  omega

/-- **The shift of a carried block of registers, with its events.** The run of
    `forArrShift_steps` is a traced run with no event. -/
theorem forRegShift_stepsL {P : LprogM} {d : Nat} {cs : Ctxt jasminDialect} (hcs : RegTys cs)
    (pre post : List LinstrRM) (s : LstateMF)
    (hbody : P.body = pre ++ movImmI (regName d) 0
      :: (typedMoves (regName d) (regName (d + 1 + cs.length)) (shiftPairs d cs) ++ post))
    (hat : atPc P pre.length s)
    (hsrc : ∀ {w n : Nat} (v : Ctxt.Var cs (.stackArr w n)), ∃ arr : Fin n → BitVec w,
      s.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex v))) w n = some arr) :
    ∃ (k : Nat) (u : LstateMF), StepsL P k s u []
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
  obtain ⟨seg, hseg⟩ : ∃ seg, seg = movImmI (regName d) 0
      :: typedMoves (regName d) (regName (d + 1 + cs.length)) (shiftPairs d cs) := ⟨_, rfl⟩
  have hq : ∀ i ∈ seg, QuietLopn i := by
    intro i hi
    rw [hseg] at hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact quietLopn_movImm _ _
    · exact quietLopn_typedMoves _ _ (arrPairs_shiftPairs hcs d) i hi
  have hbP : P.body = pre ++ seg ++ post := by
    rw [hbody, hseg]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨u, hs, hat', rest⟩ := forArrShift_steps
    (P := singletonProgM P.lfn (pre ++ seg)) (d := d) (cs := cs) pre [] s
    (by
      show pre ++ seg = _
      rw [hseg, List.append_nil])
    hat hsrc
  refine ⟨seg.length, u, stepsL_of_quiet hbP hq hat hs ?_, ⟨hat'.1, hat'.2⟩, rest⟩
  rw [hat'.2, hseg, List.length_cons]
  omega

/-! ## 6. The trips of a counted loop with carried registers -/

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
    branch event of the back edge. -/
theorem tripLeak_eq_some {cs : List JasminTy} {N : Nat}
    {bodyRun : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)}
    {i : Nat} {acc a : Ctxt.Valuation (d := jasminDialect) cs} {ℓ : List CTLeak} :
    tripLeak N bodyRun i acc = some (a, ℓ) ↔
      ∃ ℓb, bodyRun i acc = some (a, ℓb) ∧ ℓ = ℓb ++ [CTLeak.branch (decide (i + 1 < N))] := by
  simp only [tripLeak, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨a1, ℓb, h, rfl, rfl⟩
    exact ⟨ℓb, h, rfl⟩
  · rintro ⟨ℓb, h, rfl⟩
    exact ⟨a, ℓb, h, rfl, rfl⟩

section ForRegLoop

variable (Pj : JLeakParams) (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
  (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs) (hcs : RegTys cs)
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
  (hA : ∀ l, n ≤ l → findLabelMem l A = none) (V : Ctxt.Valuation Γ)

include hcs hsim hb hlen harg hfn htp hT hbody hR hA in
/-- **One trip of a counted loop with carried registers, with its events**, from the
    counter after the top label to the back-edge jump: the events are those of the body. -/
theorem forRegLoop_trip (i : Nat) (acc acc1 : Ctxt.Valuation cs) (ℓ : List CTLeak)
    (m : LstateMF) (c : BitVec 64)
    (hden : machRun Pj nArgs body (d + 1 + cs.length) (hvAppend acc
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
    ∃ (k : Nat) (t : LstateMF), StepsL P k m t ℓ
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
      _ acc1 ℓ m hden
      (by rw [List.length_append, List.length_singleton]; exact hat) hag2
  have hres_len : b.res.length = cs.length := by rw [hops, exprArgsHV_length]
  have hat1' : atPc P (A ++ labelI n :: b.code).length m1 := by
    rw [List.length_append, List.length_singleton] at hat1
    rw [List.length_append, List.length_cons]
    rwa [show A.length + (b.code.length + 1) = A.length + 1 + b.code.length by omega]
  obtain ⟨k2, t, hs2, hat2, hz, hidx', hctr', hR', hA', hothR, hothA⟩ :=
    forRegTail_stepsL hcs (d := d) (n := n) (bD := b.depth) (ops := b.res) htp
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
  refine ⟨k1 + k2, t, (hs1.trans hs2).cast (List.append_nil _), ?_, ?_, hz, hidx', hctr',
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

include hcs hsim hb hlen harg hfn htp hT hbody hR hA in
/-- **The trips of a counted loop with carried registers, with their events.** From the
    counter after the top label with `rem + 1` trips left of `N`, the run to the counter
    after the back-edge jump emits, for each trip, the events of the body followed by the
    branch event of the back edge. -/
theorem forRegLoop_trips (N : Nat) : ∀ (rem i : Nat) (acc accN : Ctxt.Valuation cs)
    (ℓ : List CTLeak) (m : LstateMF) (c : BitVec 64),
    forIterLeak (tripLeak N fun j a => machRun Pj nArgs body (d + 1 + cs.length) (hvAppend a
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
        forRegLoop_trip Pj nArgs fn body hcs hsim hb hlen harg hfn htp hT hbody hR hA V i acc
          acc1 ℓb m c hden hat hag hidx hctr hblk hblkA
      have hc1 : c - 1#64 = 0#64 := by bv_omega
      obtain ⟨hs', hat'⟩ := steps_cc_fall hcc hat2 hfetch (by rw [hz, hc1]; decide)
      have hev : (t.zf == false) = decide (i + 1 < N) := by
        rw [hz, hc1, hN]
        simp
      exact ⟨k + 1, next t,
        (hs.trans (stepsL_cc hcc hat2 hfetch hs')).cast (by rw [hev, List.append_nil]),
        hat', hfr, ⟨_, hidx'⟩, fun {w} u => hblk' u, fun {w q} u => hblkA' u⟩
  | succ rem ih =>
      intro i acc accN ℓ m c hfold hN hc hat hag hidx hctr hblk hblkA
      rw [List.range'_succ] at hfold
      obtain ⟨acc1, ℓ1, ℓ2, hstep, hrest, rfl⟩ := forIterLeak_cons_eq_some.mp hfold
      obtain ⟨ℓb, hden, rfl⟩ := tripLeak_eq_some.mp hstep
      obtain ⟨k, t, hs, hat2, hfr, hz, hidx', hctr', hblk', hblkA'⟩ :=
        forRegLoop_trip Pj nArgs fn body hcs hsim hb hlen harg hfn htp hT hbody hR hA V i acc
          acc1 ℓb m c hden hat hag hidx hctr hblk hblkA
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
        ((hs.trans (stepsL_cc hcc hat2 hfetch hs')).trans hs'').cast (by rw [hev]),
        hat'', hfr'.trans hfr'' le_rfl le_rfl, hx'', fun {w} u => hblk'' u,
        fun {w q} u => hblkA'' u⟩

end ForRegLoop

/-! ## 7. The rule of a counted loop with carried registers -/

/-- **The rule of a counted loop with carried registers.** The statements for the body and
    for the continuation give the statement for the loop: the run emits the branch event of
    the zero-trip guard, the events of the trips, and the events of the continuation. -/
theorem exportRLeakSim_forReg (Pj : JLeakParams) (nArgs : Nat) (fn : String)
    {Γ cs : Ctxt jasminDialect} {ts : List JasminTy} (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts) (hcs : RegTys cs)
    (hbsim : ExportRLeakSim Pj nArgs fn body) (hksim : ExportRLeakSim Pj nArgs fn k) :
    ExportRLeakSim Pj nArgs fn (NFProg.forLoop count inits body k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre V v ℓ m hrun hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rk, hrk, rfl⟩ := h
  obtain ⟨cnt, hcd⟩ : ∃ cnt : BitVec 64, count.lookup V = cnt := ⟨_, rfl⟩
  simp only [machRun, if_pos hcs] at hrun
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
    forRegHead_stepsL hcs (d := d) (n := n) (ops := ops) (cn := cn) htpI pre _ m (cnt := cnt)
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
      StepsL P kE m mE (.branch (decide (cnt.toNat = 0)) :: ℓr) ∧ atPc P (X.length + 1) mE
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
            rw [hz0, hc0]
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
          forRegLoop_trips Pj nArgs fn body hcs hbsim hb hlen harg hfn htpB hT hbodyL
            (by rw [hR, hcmp]) hAlab V (rem + 1) rem 0 (Expr.lookupArgs inits V) accN ℓr
            (next (next t0)) cnt hiter (by omega) hN hat2
            (StoreAgreesM.of_regionFrame hlen hag hfr2) hidx0 hctr0 (fun {w} u => hblkI u)
            (fun {w q} u => hblkAI u)
        rw [← hXlen] at hat3
        obtain ⟨hs4, hat4⟩ := steps_label x86Isa (kind := .internal) (l := n + 1)
          (tag := .reg none) hat3 (fetch_of_body hbodyX rfl)
        have hL4 := stepsL_label hat3 (fetch_of_body hbodyX rfl) hs4
        exact ⟨_, _,
          ((((hs0.trans hL1).trans hL2).trans hs3).trans hL4).cast (by
            rw [hz0]
            simp [hc0]),
          hat4,
          (hfr2.trans hfr3 le_rfl le_rfl).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl)
            le_rfl le_rfl,
          hx3, fun {w} u => hblk3 u, fun {w q} u => hblkA3 u⟩
  obtain ⟨kE, mE, hsE, hatE, hfrE, -, hblkE, hblkAE⟩ := hexit
  -- the shift of the carried block
  obtain ⟨kS, mS, hsS, hatS, hRS, hAS, hoRS, hoAS⟩ := forRegShift_stepsL hcs (d := d) (cs := cs)
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
    _ v' ℓk mS hkden
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
  refine ⟨_, m', ((hsE.trans hsS).trans hsK).cast (by simp), ?_, hresK,
    hfrS.trans hfrK (by omega) (by omega)⟩
  rw [hlenEq]
  exact hatK

/-! ## 8. The traced simulation on the fragment -/

/-- **The fragment of the leakage theorem**: bindings of the stack-memory fragment, returns,
    and counted loops whose carried types are held in register cells. -/
def RegLoopFragment : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Prop
  | _, _, .ret _ => True
  | _, _, .var e k => BindMemN e ∧ RegLoopFragment k
  | _, _, .forLoop (cs := cs) _ _ body k => RegTys cs ∧ RegLoopFragment body ∧ RegLoopFragment k
  | _, _, .ifThenElse .. => False
  | _, _, .whileLoop .. => False
  | _, _, .call .. => False

/-- **The traced simulation of the region export** on `RegLoopFragment`. -/
theorem exportR_leakSim (Pj : JLeakParams) (nArgs : Nat) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegLoopFragment p) : ExportRLeakSim Pj nArgs fn p := by
  induction p with
  | ret vs => exact exportRLeakSim_ret Pj nArgs fn vs
  | var e k ih => exact exportRLeakSim_var Pj nArgs fn e k hp.1 (ih hp.2)
  | forLoop count inits body k ihb ihk =>
      exact exportRLeakSim_forReg Pj nArgs fn count inits body k hp.1 (ihb hp.2.1) (ihk hp.2.2)
  | ifThenElse cond thn els k iht ihe ihk => exact hp.elim
  | whileLoop inits body k ihb ihk => exact hp.elim
  | call f args k ih => exact hp.elim

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

/-- **The source run of a program of the fragment succeeds** at every valuation. -/
theorem leakRun_isSome (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : RegLoopFragment p) :
    ∀ V : Ctxt.Valuation Γ, ∃ r, NFProg.leakRun (jLeakModel Pj) fuel p V = some r := by
  induction p with
  | ret vs => exact fun V => ⟨_, rfl⟩
  | var e k ih =>
      intro V
      obtain ⟨r, hr⟩ := ih hp.2 (V.extend (e.denote V))
      refine ⟨(r.1, Expr.ctLeak (jLeakModel Pj) e V ++ r.2), ?_⟩
      simp only [NFProg.leakRun, hr, Option.map_some]
  | forLoop count inits body k ihb ihk =>
      intro V
      simp only [NFProg.leakRun]
      obtain ⟨r, hr⟩ := forIterLeak_isSome
        (step := fun i acc => NFProg.leakRun (jLeakModel Pj) fuel body
          (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)))
        (fun i acc => ihb hp.2.1 _)
        (List.range (HasWord64.toNat (d := jasminDialect) (count.lookup V)))
        (Expr.lookupArgs inits V)
      obtain ⟨q, hq⟩ := ihk hp.2.2 (hvAppend r.1 V)
      rw [hr, Option.bind_some, hq]
      exact ⟨_, rfl⟩
  | ifThenElse cond thn els k iht ihe ihk => exact hp.elim
  | whileLoop inits body k ihb ihk => exact hp.elim
  | call f args k ih => exact hp.elim

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

/-- **The source events of a program of the fragment determine its machine events.** For
    two source runs whose events, each followed by a list, are equal: the events are
    equal, the lists are equal, and `machRun` returns the results of the source runs with
    one list of machine events. -/
theorem machRun_of_leakRun (Pj : JLeakParams) (nArgs fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : RegLoopFragment p) :
    ∀ (d : Nat) (V₁ V₂ : Ctxt.Valuation Γ) (v₁ v₂ : Ctxt.Valuation (d := jasminDialect) ts)
      (ℓ₁ ℓ₂ s₁ s₂ : List CTLeak),
      NFProg.leakRun (jLeakModel Pj) fuel p V₁ = some (v₁, ℓ₁) →
      NFProg.leakRun (jLeakModel Pj) fuel p V₂ = some (v₂, ℓ₂) → ℓ₁ ++ s₁ = ℓ₂ ++ s₂ →
      ℓ₁ = ℓ₂ ∧ s₁ = s₂
        ∧ ∃ μ, machRun Pj nArgs p d V₁ = some (v₁, μ) ∧ machRun Pj nArgs p d V₂ = some (v₂, μ) := by
  induction p with
  | ret vs =>
      intro d V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hs
      simp only [NFProg.leakRun, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, hs, [], rfl, rfl⟩
  | var e k ih =>
      intro d V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hs
      simp only [NFProg.leakRun, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at h₁ h₂
      obtain ⟨a₁, t₁, hk₁, rfl, rfl⟩ := h₁
      obtain ⟨a₂, t₂, hk₂, rfl, rfl⟩ := h₂
      rw [List.append_assoc, List.append_assoc] at hs
      obtain ⟨he, hrest⟩ := List.append_inj hs
        (by rw [exprCtLeak_length, exprCtLeak_length])
      obtain ⟨ht, hss, μ, hm₁, hm₂⟩ := ih hp.2 (d + 1) _ _ _ _ _ _ _ _ hk₁ hk₂ hrest
      refine ⟨by rw [he, ht], hss, bindLeak Pj nArgs e d V₁ ++ μ, ?_, ?_⟩
      · simp only [machRun, hm₁, Option.map_some]
      · simp only [machRun, hm₂, Option.map_some, bindLeak, he]
  | forLoop count inits body k ihb ihk =>
      rename_i Γ' cs ts'
      intro d V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hs
      simp only [NFProg.leakRun, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.mk.injEq, Prod.exists] at h₁ h₂
      obtain ⟨a₁, t₁, hi₁, c₁, u₁, hk₁, rfl, rfl⟩ := h₁
      obtain ⟨a₂, t₂, hi₂, c₂, u₂, hk₂, rfl, rfl⟩ := h₂
      simp only [List.cons_append, List.cons.injEq, CTLeak.trip.injEq, List.append_assoc] at hs
      obtain ⟨hN, hs⟩ := hs
      have hN' : BitVec.toNat (count.lookup V₁) = BitVec.toNat (count.lookup V₂) := hN
      rw [← hN] at hi₂
      obtain ⟨ht, hs', μ, hm₁, hm₂⟩ := forIterLeak_factor
        (sM₁ := tripLeak (BitVec.toNat (count.lookup V₁)) fun i acc =>
          machRun Pj nArgs body (d + 1 + cs.length)
            (hvAppend acc (.cons (BitVec.ofNat 64 i) V₁)))
        (sM₂ := tripLeak (BitVec.toNat (count.lookup V₁)) fun i acc =>
          machRun Pj nArgs body (d + 1 + cs.length)
            (hvAppend acc (.cons (BitVec.ofNat 64 i) V₂)))
        (fun i acc₁ acc₂ b₁ b₂ x₁ x₂ y₁ y₂ e₁ e₂ es => by
          obtain ⟨hl, hss, μ, m₁, m₂⟩ :=
            ihb hp.2.1 (d + 1 + cs.length) _ _ _ _ _ _ _ _ e₁ e₂ es
          exact ⟨hl, hss, _, tripLeak_eq_some.mpr ⟨μ, m₁, rfl⟩,
            tripLeak_eq_some.mpr ⟨μ, m₂, rfl⟩⟩)
        _ _ _ _ _ _ _ _ _ hi₁ hi₂ hs
      obtain ⟨hu, hss, ν, hn₁, hn₂⟩ := ihk hp.2.2 (d + cs.length) _ _ _ _ _ _ _ _ hk₁ hk₂ hs'
      refine ⟨by rw [hN, ht, hu], hss,
        .branch (decide (BitVec.toNat (count.lookup V₁) = 0)) :: (μ ++ ν), ?_, ?_⟩
      · simp only [machRun, if_pos hp.1]
        exact Option.bind_eq_some_iff.mpr ⟨(a₁, μ), hm₁, by rw [hn₁]; rfl⟩
      · simp only [machRun, if_pos hp.1]
        rw [← hN']
        exact Option.bind_eq_some_iff.mpr ⟨(a₂, μ), hm₂, by rw [hn₂]; rfl⟩
  | ifThenElse cond thn els k iht ihe ihk => exact hp.elim
  | whileLoop inits body k ihb ihk => exact hp.elim
  | call f args k ih => exact hp.elim

/-- **`machRun` succeeds on the fragment** at every depth and valuation. -/
theorem machRun_isSome (Pj : JLeakParams) (nArgs : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : RegLoopFragment p) (d : Nat)
    (V : Ctxt.Valuation Γ) : ∃ r, machRun Pj nArgs p d V = some r := by
  obtain ⟨⟨v, ℓ⟩, h⟩ := leakRun_isSome Pj 0 hp V
  obtain ⟨-, -, μ, hm, -⟩ := machRun_of_leakRun Pj nArgs 0 hp d V V v v ℓ ℓ [] [] h h rfl
  exact ⟨_, hm⟩

/-- **Valuations with equal source events have equal machine events**, for a program of
    the fragment at every depth. -/
theorem machLeak_eq_of_leakRun_eq (Pj : JLeakParams) (nArgs fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegLoopFragment p) (d : Nat) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
      = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd) :
    machLeak Pj nArgs p d V₁ = machLeak Pj nArgs p d V₂ := by
  obtain ⟨⟨v₁, ℓ₁⟩, h₁⟩ := leakRun_isSome Pj fuel hp V₁
  obtain ⟨⟨v₂, ℓ₂⟩, h₂⟩ := leakRun_isSome Pj fuel hp V₂
  rw [h₁, h₂] at h
  have hℓ : ℓ₁ = ℓ₂ := by simpa using h
  obtain ⟨-, -, μ, m₁, m₂⟩ :=
    machRun_of_leakRun Pj nArgs fuel hp d V₁ V₂ v₁ v₂ ℓ₁ ℓ₂ [] [] h₁ h₂ (by rw [hℓ])
  simp only [machLeak, m₁, m₂, Option.map_some]

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

/-- **The leakage of the exported code.** For a program of the fragment exported at the
    depth of its context, every terminating traced run of the code from an entry state that
    agrees with `V` has the events `machLeak` at `V`. -/
theorem exportR_leak_forReg (Pj : JLeakParams) {nArgs : Nat} {fn : String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegLoopFragment p) {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n = some r) (hlen : Γ.length = d) (harg : nArgs ≤ d)
    {V : Ctxt.Valuation Γ} {s : LstateMF} {ℓ : List CTLeak}
    (hent : RegionEntry nArgs fn d V s) (hrun : FRun (singletonProgM fn r.code) s ℓ) :
    machLeak Pj nArgs p d V = some ℓ := by
  obtain ⟨⟨v, μ⟩, hm⟩ := machRun_isSome Pj nArgs hp d V
  obtain ⟨k, m', hs, hat', -, -⟩ := exportR_leakSim Pj nArgs fn hp d n r hr hlen harg
    (singletonProgM fn r.code) [] [] rfl (by simp [singletonProgM])
    (fun l _ => (findLabelMem_eq_none_iff l []).mpr (by simp [labelsOf])) V v μ s hm
    ⟨hent.1, hent.2.1⟩ hent.2.2
  have hF := fRun_of_stepsL hs (halted_of_atPc hat' (by simp [singletonProgM]))
  rw [machLeak, hm]
  exact congrArg some (fRun_unique hF hrun)

/-- **Constant time of the exported code from constant time of the program.** A program of
    the fragment that is constant time at the source events for the entry labels `L` has
    exported code that is constant time on the traced flag machine between entry states
    whose stores agree with valuations equal on the public positions. -/
theorem exportR_memFCT (Pj : JLeakParams) {nArgs : Nat} {fn : String} (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegLoopFragment p) {L : Labels Γ} (hct : NFCT (jLeakModel Pj) L fuel p)
    {d n : Nat} {r : Exported} (hr : exportR nArgs fn p d n = some r) (hlen : Γ.length = d)
    (harg : nArgs ≤ d) :
    MemFCT (singletonProgM fn r.code) (RegionEntryPub nArgs fn d L) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨V₁, V₂, hpub, e₁, e₂⟩ r₁ r₂
  have h₁ := exportR_leak_forReg Pj hp hr hlen harg e₁ r₁
  have h₂ := exportR_leak_forReg Pj hp hr hlen harg e₂ r₂
  have h := machLeak_eq_of_leakRun_eq Pj nArgs fuel hp d V₁ V₂ (hct V₁ V₂ hpub)
  rw [h₁, h₂] at h
  exact Option.some.inj h

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
