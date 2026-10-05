/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaMachine
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT

@[expose] public section

set_option autoImplicit false

/-!
# The x86 instance of the `Lprog` instruction-set record, and the symbolic step over it

`x86Isa` is the `LprogIsa.Isa` whose step is the flag machine `evalInstrPMemF` and whose
branch-condition evaluation is `OwnedLprogTV.decC` (the zero flag for the condition codes
`Z`/`NZ`, a non-zero register test otherwise). Each generic interpreter of `LprogIsa` is, at
`x86Isa`, the existing x86 interpreter by `rfl`.

`IsaSym I` extends an instruction set `I` by a symbolic step over the term language of
`OwnedLprogTV` (`STerm`, `SSt`, `SOut`, `SDec`) with the obligations that it describes
`I.step` exactly (`StepSound`) and that the symbolic branch condition evaluates to
`I.condEval`. The term language is fixed across instruction sets. `x86Sym` is the instance at
`x86Isa`, with `OwnedLprogTV.symStep` and `OwnedLprogTV.symDec`.

## Main results

* `x86Isa_allocPool`, `x86Isa_calleeSaved`, `x86Isa_tied`, `x86Isa_copyMnemonic`,
  `x86Isa_implicitReads`, `x86Isa_loopGuard` and the other data equations: the data fields at
  x86 are the existing constants, by `rfl`.
* `x86LeaksOperands`, `x86Isa_leaksOperands`, `x86Isa_leaksOperands_of`: the leakage regime
  at x86 is `CT.DoitRegime.leaksOperands .doitm` at the mnemonic the printer emits, by `rfl`.
* `x86Isa`, `x86Isa_step`, `x86Isa_lsemFuelMemF`, `x86Isa_lsemFuelMemFk`,
  `x86Isa_evalInstrPMemFk`, `x86Isa_RunIdxOk`, `x86Isa_runL`: the x86 instance and the
  definitional recovery of the x86 interpreters.
* `x86Isa_invTouch`, `x86Isa_withKeep_step_keep`, `x86Isa_withKeep_step_of_not_keep`: the
  x86 invariant touch is the compare, and `x86Isa.withKeep` steps the keep marker as a no-op
  and every other instruction as `evalInstrPMemF`.
* `IsaSym`, `IsaSym.symRun`, `IsaSym.symRun_sound`: the symbolic step record and the exact
  description of a straight-line run by the symbolic run.
* `x86Sym`, `x86Sym_symRun`, `symRun_sound_x86`: the x86 symbolic instance, the recovery of
  `OwnedLprogTV.symRun`, and `OwnedLprogTV.symRun_sound` as the specialisation.
* `IsaSym.Lawful`, `IsaSym.symLaws`, `IsaSym.symSubst`, `IsaSym.ownedCheckM`,
  `IsaSym.ownedCheckM_sound`, `x86Sym_lawful`, `x86Sym_ownedCheckM`: the laws of a symbolic
  companion from which the checker soundness follows, the checker of an instruction set with
  its soundness, and the x86 instance.
* `x86Mach`, `x86Mach_exec`, `x86Mach_opLeak`, `x86Mach_runBlock`, `x86Mach_blockLeak`,
  `x86Mach_BlockOk`, `x86Mach_mstep`: the x86 machine level `IsaMachine` under a timing
  regime, whose operations, state, step and leakage are those of the address machine
  `aMachine` and of `DecodedCT`.
* `x86Mach_runL_iff`, `x86Mach_haltsC_iff`, `x86Mach_halts_iff`: the generic leakage
  semantics and halting runs at `x86Mach` are `DecodedCT.RunL`, `RInstrSemantics.HaltsC` and
  `RInstrSemantics.Halts`.
* `runL_halts_x86`, `haltsC_runL_x86`, `halts_runL_x86`: `DecodedCT.RunL.halts`,
  `DecodedCT.haltsC_runL` and `DecodedCT.halts_runL` as specialisations of the generic
  theorems.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-! The definitions `evalInstrPMemF_ctl`, `attMnem?`, `x86MnemOfBase`, `x86LeaksOperands` and
`x86Isa` of this namespace, with `x86Isa_lsemFuelMemF` and `x86Isa_runL`, are stated in
`X86Backend.OwnedLprogTV`, whose checker soundness is instantiated at `x86Isa`. -/

theorem x86Isa_step : x86Isa.step = evalInstrPMemF := rfl

theorem x86Isa_condEval : x86Isa.condEval = decC := rfl

/-! The data fields of `x86Isa` are the x86 constants of the exporter, the printer and the
legaliser. -/

theorem x86Isa_allocPool : x86Isa.allocPool = gpRegNames := rfl

theorem x86Isa_scratch : x86Isa.scratch = [reloadScratch, reloadScratch2] := rfl

theorem x86Isa_argRegs : x86Isa.argRegs = sysvArgRegs := rfl

theorem x86Isa_calleeSaved : x86Isa.calleeSaved = LprogAsmPrinter.calleeSavedRegs := rfl

theorem x86Isa_saveSlot : x86Isa.saveSlot = LprogAsmPrinter.qsaveSlot := rfl

theorem x86Isa_tied : x86Isa.tied = TwoAddrLegalize.needsTie := rfl

theorem x86Isa_commutes (base : String) :
    x86Isa.commutes base = TwoAddrLegalize.commBases.contains base := rfl

theorem x86Isa_tieScratch : x86Isa.tieScratch = reloadScratch := rfl

theorem x86Isa_copyMnemonic : x86Isa.copyMnemonic = TwoAddrLegalize.movFor := rfl

theorem x86Isa_sp : x86Isa.sp = "RSP" := rfl

theorem x86Isa_retRegs_head : x86Isa.retRegs.head? = some sysvRetReg := rfl

theorem x86Isa_callerSaved : x86Isa.callerSaved = sysvCallerSaved := rfl

theorem x86Isa_redZone : x86Isa.redZone = 128 := rfl

theorem x86Isa_supports (base : String) : x86Isa.supports base = true := rfl

/-- The implicit reads of `x86Isa` at an `Lopn` are those of the scheduler,
    `LprogScheduler.implicitReads`. -/
theorem x86Isa_implicitReads (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    LprogScheduler.implicitReads (.Lopn dsts opn srcs) = x86Isa.implicitReads opn := rfl

/-- The x86 loop guard is the flag guard `CMP ctr, 0; jne top` of the loop export. -/
theorem x86Isa_loopGuard (ctr : String) (top : LLabel) :
    x86Isa.loopGuard ctr top =
      [.Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0], .Lcond (.reg "NZ") top] :=
  rfl

/-- The x86 zero-trip guard is the flag guard `CMP ctr, 0; je endL` of the loop export. -/
theorem x86Isa_zeroTripGuard (ctr : String) (top endL : LLabel) :
    x86Isa.zeroTripGuard ctr top endL =
      [.Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0], .Lcond (.reg "Z") endL] :=
  rfl

/-- The x86 invariant touch is the compare `CMP ctr, r` of the loop export. -/
theorem x86Isa_invTouch (ctr r : String) :
    x86Isa.invTouch ctr r = .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r] :=
  rfl

/-- **The keep marker is a no-op of `x86Isa.withKeep`**: the step advances the program
    counter and changes nothing else. -/
theorem x86Isa_withKeep_step_keep (P : LprogM) (dsts srcs : List LOperand) (tag : MemTag)
    (s : LstateMF) :
    x86Isa.withKeep.step P (.Lopn dsts "KEEP" srcs, tag) s = some (keepStep s) :=
  x86Isa.withKeep_step_keep P _ s rfl

/-- On an instruction other than a keep marker the step of `x86Isa.withKeep` is the flag
    machine `evalInstrPMemF`. -/
theorem x86Isa_withKeep_step_of_not_keep (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : isKeep i.fst = false) : x86Isa.withKeep.step P i s = evalInstrPMemF P i s :=
  x86Isa.withKeep_step_of_not_keep P i s h

theorem x86Isa_leaksOperands (base : String) :
    x86Isa.leaksOperands base =
      ((x86MnemOfBase base).map (CT.DoitRegime.leaksOperands .doitm)).getD true := rfl

/-- At a base the printer names, the x86 regime is `CT.DoitRegime.leaksOperands .doitm` of
    its table mnemonic. -/
theorem x86Isa_leaksOperands_of {base : String} {m : CT.X86Mnem}
    (h : x86MnemOfBase base = some m) :
    x86Isa.leaksOperands base = CT.DoitRegime.doitm.leaksOperands m := by
  rw [x86Isa_leaksOperands, h]; rfl

/-- The generic fetch-and-step at `x86Isa` is `lsemStepPMemF`. -/
theorem x86Isa_lsemStepPMemF : x86Isa.lsemStepPMemF = lsemStepPMemF := rfl

/-- **The symbolic step of an instruction set** over the fixed term language: a symbolic
    step that describes `I.step` exactly from every state a symbolic state describes, and a
    symbolic branch condition whose value is `I.condEval`. -/
structure IsaSym (I : Isa) : Type where
  /-- The symbolic step of one instruction. -/
  symStep : LinstrRM → SSt → SOut
  /-- The symbolic value of a branch condition. -/
  symDec : SSt → LOperand → SDec
  /-- The symbolic step describes the step exactly. -/
  symStep_sound : ∀ (P : LprogM) (i : LinstrRM) (ss : SSt),
    StepSound (I.step P i) ss (symStep i ss)
  /-- The symbolic branch condition evaluates to the branch condition. -/
  symDec_sound : ∀ {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {ss : SSt} {s : LstateMF}, Holds V A C O Z ss s → ∀ c : LOperand,
    I.condEval s c = (symDec ss c).ev V A C O Z

namespace IsaSym

variable {I : Isa} (T : IsaSym I)

/-- The symbolic run of a list of instructions: the final symbolic state with the guards of
    every step, `fail` when a step always fails, `unk` when a step is outside the fragment. -/
def symRun : List LinstrRM → SSt → SOut
  | [], ss => .ok ss []
  | i :: is, ss =>
      match T.symStep i ss with
      | .ok ss1 g1 =>
          match symRun is ss1 with
          | .ok ss2 g2 => .ok ss2 (g1 ++ g2)
          | .fail => .fail
          | .unk => .unk
      | .fail => .fail
      | .unk => .unk

/-- **The symbolic run describes the run exactly.** From every state `ss` describes, the
    steps of `is` succeed exactly when the guards of `T.symRun is ss` hold, and then end in a
    state its final symbolic state describes; a run `symRun` reports as failing fails. -/
theorem symRun_sound (P : LprogM) :
    ∀ (is : List LinstrRM) (ss : SSt) (V : String → Σ w, BitVec w) (A : String → ArrCell)
      (C O : Bool) (Z : Bool) (s : LstateMF), Holds V A C O Z ss s →
      (T.symRun is ss).DescN is.length (I.runL P is s) V A C O Z s
  | [], ss, V, A, C, O, Z, s, hs => by
      refine ⟨fun t ht => ?_, fun _ => rfl⟩
      cases ht
      exact ⟨allG_nil V A C O, hs, rfl, rfl, rfl⟩
  | i :: is, ss, V, A, C, O, Z, s, hs => by
      have hstep := T.symStep_sound P i ss V A C O Z s hs
      simp only [symRun, Isa.runL]
      cases h1 : T.symStep i ss with
      | ok ss1 g1 =>
          rw [h1] at hstep
          obtain ⟨hs1, hs2⟩ := hstep
          cases h2 : T.symRun is ss1 with
          | ok ss2 g2 =>
              simp only [h2, SOut.DescN]
              refine ⟨fun t ht => ?_, fun hg => ?_⟩
              · obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp ht
                obtain ⟨hg1, hH1, hF1⟩ := hs1 s1 e1
                have ih := symRun_sound P is ss1 V A C O Z s1 hH1
                rw [h2] at ih
                obtain ⟨hg2, hH2, hF2⟩ := ih.1 t e2
                refine ⟨allG_append.mpr ⟨hg1, hg2⟩, hH2, ?_, ?_, ?_⟩
                · rw [hF2.1, hF1.1]
                · rw [hF2.2.1, hF1.2.1, List.length_cons]; omega
                · rw [hF2.2.2, hF1.2.2]
              · obtain ⟨hg1, hg2⟩ := allG_append.mp hg
                obtain ⟨s1, e1⟩ := Option.isSome_iff_exists.mp (hs2 hg1)
                have ih := symRun_sound P is ss1 V A C O Z s1 (hs1 s1 e1).2.1
                rw [h2] at ih
                rw [e1, Option.bind_some]
                exact ih.2 hg2
          | fail =>
              simp only [h2, SOut.DescN]
              cases e1 : I.step P i s with
              | none => rfl
              | some s1 =>
                  have ih := symRun_sound P is ss1 V A C O Z s1 (hs1 s1 e1).2.1
                  rw [h2] at ih
                  exact ih
          | unk => simp only [h2, SOut.DescN]
      | fail =>
          rw [h1] at hstep
          simp only [SOut.DescN]
          simp only [SOut.Desc] at hstep
          rw [hstep, Option.bind_none]
      | unk => simp only [SOut.DescN]

end IsaSym

/-- **The x86 symbolic step**: `symStep` and `symDec`, with `symStep_sound` and `decC_eq`. -/
def x86Sym : IsaSym x86Isa where
  symStep := symStep
  symDec := symDec
  symStep_sound := symStep_sound
  symDec_sound := fun hs c => decC_eq hs c

/-- The generic symbolic run at `x86Sym` is `OwnedLprogTV.symRun`. -/
theorem x86Sym_symRun : x86Sym.symRun = fun is ss => OwnedLprogTV.symRun is ss := by
  funext is ss
  induction is generalizing ss with
  | nil => rfl
  | cons i is ih =>
      simp only [IsaSym.symRun, OwnedLprogTV.symRun, ih]
      rfl

/-- `OwnedLprogTV.symRun_sound` is the specialisation of `IsaSym.symRun_sound` at
    `x86Sym`. -/
theorem symRun_sound_x86 (P : LprogM) (is : List LinstrRM) (ss : SSt)
    (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O Z : Bool) (s : LstateMF)
    (hs : Holds V A C O Z ss s) :
    (OwnedLprogTV.symRun is ss).DescN is.length (OwnedLprogTV.runL P is s) V A C O Z s := by
  have h := x86Sym.symRun_sound P is ss V A C O Z s hs
  rwa [x86Sym_symRun, x86Isa_runL] at h

/-! ## The checker of an instruction set

The checkers `OwnedLprogTV.ownedCheckM`, `OwnedLprogTVChecked.ownedCheckMC` and
`OwnedTVLeak.ownedCheckML` take a symbolic step and a symbolic branch condition; their
soundness is proved from `OwnedLprogTV.SymLaws` and `OwnedLprogTV.SymSubst`. A symbolic
companion `T : IsaSym I` supplies both when it is `T.Lawful`. -/

/-- **The laws of a symbolic companion beyond its two soundness fields**: the symbolic step
    keeps `SSt.Good`, describes a label as the identity and commutes with substitution, the
    symbolic branch condition commutes with substitution, a step of the instruction set at an
    instruction that is no terminator stays in the function and advances the pc by one, and
    the instruction set takes no step at `Lret`. -/
structure IsaSym.Lawful {I : Isa} (T : IsaSym I) : Prop where
  /-- The symbolic step keeps `SSt.Good`. -/
  good : ∀ (i : LinstrRM) {ss : SSt}, ss.Good → ∀ {ss' : SSt} {gs : List SG},
    T.symStep i ss = .ok ss' gs → ss'.Good
  /-- The symbolic step of a label is the identity, with no guard. -/
  label : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, T.symStep i ss = .ok ss []
  /-- A step at an instruction that is no terminator stays in the function and advances the
      pc by one. -/
  plain : StepPlain I
  /-- The instruction set takes no step at `Lret`. -/
  ret : ∀ (P : LprogM) (tag : MemTag) (s : LstateMF), I.step P (.Lret, tag) s = none
  /-- The symbolic step commutes with substitution. -/
  step_subst : ∀ (σ : Nat → STerm) (i : LinstrRM) (ss : SSt),
    T.symStep i (ss.subst σ) = (T.symStep i ss).subst σ
  /-- The symbolic branch condition commutes with substitution. -/
  dec_subst : ∀ (σ : Nat → STerm) (ss : SSt) (c : LOperand),
    T.symDec (ss.subst σ) c = (T.symDec ss c).subst σ

namespace IsaSym

variable {I : Isa} (T : IsaSym I)

/-- A lawful symbolic companion satisfies the laws the checker soundness is proved from. -/
theorem symLaws (h : T.Lawful) : SymLaws I T.symStep T.symDec where
  step_sound := T.symStep_sound
  dec_sound := fun hs c => T.symDec_sound hs c
  good := fun i _ hg _ _ e => h.good i hg e
  label := fun hl ss => h.label hl ss
  plain := h.plain
  ret := h.ret

/-- A lawful symbolic companion commutes with substitution. -/
theorem symSubst (h : T.Lawful) : SymSubst T.symStep T.symDec :=
  ⟨h.step_subst, h.dec_subst⟩

/-- The symbolic run of the record is `OwnedLprogTV.symRun` at its symbolic step. -/
theorem symRun_eq (is : List LinstrRM) (ss : SSt) :
    T.symRun is ss = OwnedLprogTV.symRun is ss T.symStep := by
  induction is generalizing ss with
  | nil => rfl
  | cons i is ih =>
      simp only [symRun, OwnedLprogTV.symRun, ih]
      rfl

/-- **The checker of an instruction set**: `OwnedLprogTV.ownedCheckM` at the symbolic step
    and the symbolic branch condition of the companion. -/
def ownedCheckM (outs : List String) (B B' : List LinstrRM) : Bool :=
  OwnedLprogTV.ownedCheckM outs B B' T.symStep T.symDec

/-- **Soundness of the checker of an instruction set.** If `T.ownedCheckM outs B B'` accepts
    for a lawful symbolic companion `T` of `I`, every halting run of `I` on the singleton
    program over `B` from a state at pc `0` of that function is matched by a halting run on
    the singleton program over `B'` from the same state, and the end states agree on the
    registers `outs`, on the arrays and on the word memory. -/
theorem ownedCheckM_sound (h : T.Lawful) {outs : List String} {B B' : List LinstrRM}
    (hc : T.ownedCheckM outs B B' = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' :=
  ownedCheckM_sound_at (T.symLaws h) (T.symSubst h) hc fn s t hfn hpc fuel hrun

end IsaSym

/-- The x86 symbolic companion is lawful. -/
theorem x86Sym_lawful : x86Sym.Lawful where
  good := fun i _ hg _ _ e => symStep_good i hg e
  label := fun hl ss => symStep_label hl ss
  plain := stepPlain_x86
  ret := evalInstrPMemF_ret
  step_subst := symStep_subst
  dec_subst := symDec_subst

/-- The checker of `x86Sym` is `OwnedLprogTV.ownedCheckM`. -/
theorem x86Sym_ownedCheckM (outs : List String) (B B' : List LinstrRM) :
    x86Sym.ownedCheckM outs B B' = OwnedLprogTV.ownedCheckM outs B B' := rfl

/-! ## The machine level at x86 -/

section Machine

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState evalInstrA runBlockA)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-- The action of the decoded x86 instruction at `pc` on the address machine: an `op` is an
    operation, a `jcc` a branch whose outcome is the condition of its nibble on the flags,
    `push` and `pop` the blocks `pushOps` and `popOps`, `call` and `ret` themselves. -/
def x86Act (prog : List RInstr) (pc : Nat) (sa : AState) : Option (MAct (JInstr 64)) :=
  match prog[pc]? with
  | none => none
  | some (.op i) => some (.op i)
  | some (.jcc cc t) =>
      (RInstrSemantics.condtOfNibble cc).map fun c => .branch (sa.view.condB c) t
  | some .ret => some .ret
  | some (.push r) => some (.block (LprogBytesDecode.pushOps r))
  | some (.pop r) => some (.block (LprogBytesDecode.popOps r))
  | some (.call t) => some (.call t)

/-- **The x86 machine** under the timing regime `r`: decoded programs `List RInstr` of
    `JInstr 64` operations on the address machine `aMachine` (`AState`, `evalInstrA`), the
    decoder `decodeLprog`, the call blocks `callOps` and `retOps`, and the leakage
    `DecodedCT.opLeak r` (the memory events of `instrLeak` at their effective addresses and
    the operands the regime makes observable). -/
@[reducible] def x86Mach (r : CT.DoitRegime) : IsaMachine where
  Instr := RInstr
  Op := JInstr 64
  MState := AState
  exec := evalInstrA
  decode := LprogBytesDecode.decodeLprog
  act := x86Act
  callOps := LprogBytesDecode.callOps
  retOps := LprogBytesDecode.retOps
  opLeak := DecodedCT.opLeak r

variable (r : CT.DoitRegime)

theorem x86Mach_Instr : (x86Mach r).Instr = RInstr := rfl

theorem x86Mach_Op : (x86Mach r).Op = JInstr 64 := rfl

theorem x86Mach_MState : (x86Mach r).MState = AState := rfl

theorem x86Mach_exec : (x86Mach r).exec = aMachine.exec := rfl

theorem x86Mach_decode : (x86Mach r).decode = LprogBytesDecode.decodeLprog := rfl

theorem x86Mach_opLeak : (x86Mach r).opLeak = DecodedCT.opLeak r := rfl

/-- The block fold at `x86Mach` is `runBlockA`, by unfolding both definitions. -/
theorem x86Mach_runBlock : (x86Mach r).runBlock = runBlockA := by
  delta IsaMachine.runBlock runBlockA; rfl

/-- The block leakage at `x86Mach` is `DecodedCT.blockLeakA`, by unfolding both
    definitions. -/
theorem x86Mach_blockLeak : (x86Mach r).blockLeak = DecodedCT.blockLeakA r := by
  delta IsaMachine.blockLeak DecodedCT.blockLeakA; rfl

/-- The block side condition at `x86Mach` is `DecodedCT.BlockOk`, by unfolding both
    definitions. -/
theorem x86Mach_BlockOk (ok : AState → JInstr 64 → Prop) :
    (x86Mach r).BlockOk ok = DecodedCT.BlockOk ok := by
  delta IsaMachine.BlockOk DecodedCT.BlockOk; rfl

/-- The step at `x86Mach` is `RInstrSemantics.step aMachine`. -/
theorem x86Mach_mstep : (x86Mach r).mstep = RInstrSemantics.step aMachine := by
  funext prog pc s
  simp only [IsaMachine.mstep, RInstrSemantics.step, x86Act]
  rcases h : prog[pc]? with _ | ri
  · rfl
  · cases ri <;> try rfl
    rename_i cc t
    rcases hc : RInstrSemantics.condtOfNibble cc with _ | c
    · simp [hc]
    · simp only [hc, Option.map_some]
      cases hb : (AState.view s).condB c <;> simp [hb, Ascent.RInstrAddrMem.aMachine_view]

/-! The actions of `x86Act` against the decoded instruction. -/

theorem x86Act_ret {prog : List RInstr} {pc : Nat} {sa : AState} :
    x86Act prog pc sa = some .ret ↔ prog[pc]? = some .ret := by
  unfold x86Act
  rcases prog[pc]? with _ | ri
  · simp
  · cases ri <;> simp

theorem x86Act_op {prog : List RInstr} {pc : Nat} {sa : AState} {i : JInstr 64} :
    x86Act prog pc sa = some (.op i) ↔ prog[pc]? = some (.op i) := by
  unfold x86Act
  rcases prog[pc]? with _ | ri
  · simp
  · cases ri <;> simp

theorem x86Act_call {prog : List RInstr} {pc : Nat} {sa : AState} {tgt : Nat} :
    x86Act prog pc sa = some (.call tgt) ↔ prog[pc]? = some (.call tgt) := by
  unfold x86Act
  rcases prog[pc]? with _ | ri
  · simp
  · cases ri <;> simp

theorem x86Act_block {prog : List RInstr} {pc : Nat} {sa : AState} {ops : List (JInstr 64)} :
    x86Act prog pc sa = some (.block ops) ↔
      ∃ ri, prog[pc]? = some ri ∧ ri.stackOps? = some ops := by
  unfold x86Act
  rcases prog[pc]? with _ | ri
  · simp
  · cases ri <;> simp [RInstr.stackOps?]

theorem x86Act_branch {prog : List RInstr} {pc : Nat} {sa : AState} {b : Bool} {tgt : Nat} :
    x86Act prog pc sa = some (.branch b tgt) ↔
      ∃ cc c, prog[pc]? = some (.jcc cc tgt) ∧ RInstrSemantics.condtOfNibble cc = some c ∧
        sa.view.condB c = b := by
  unfold x86Act
  rcases prog[pc]? with _ | ri
  · simp
  · cases ri <;> simp
    rename_i cc t
    cases RInstrSemantics.condtOfNibble cc <;> simp [eq_comm, and_comm]

/-- **The leakage semantics at `x86Mach` is `DecodedCT.RunL`.** -/
theorem x86Mach_runL_iff {ok : AState → JInstr 64 → Prop} {prog : List RInstr} {pc : Nat}
    {sa : AState} {t : List CT.CTLeak} {sa' : AState} :
    (x86Mach r).RunL ok prog pc sa t sa' ↔ DecodedCT.RunL r ok prog pc sa t sa' := by
  constructor
  · intro h
    refine IsaMachine.RunL.rec
      (motive := fun pc sa t sa' _ => DecodedCT.RunL r ok prog pc sa t sa')
      (fun h => .ret (x86Act_ret.mp h)) (fun h hok _ ih => .op (x86Act_op.mp h) hok ih)
      (fun h hok _ ih => ?_) (fun h _ ih => ?_) (fun h hok _ hokr _ ihc ihr => ?_) h
    · obtain ⟨ri, h1, h2⟩ := x86Act_block.mp h
      rw [x86Mach_BlockOk] at hok
      rw [x86Mach_runBlock] at ih
      rw [x86Mach_blockLeak]
      exact .stack h1 h2 hok ih
    · obtain ⟨cc, c, h1, h2, rfl⟩ := x86Act_branch.mp h
      exact .jcc h1 h2 ih
    · rw [x86Mach_BlockOk] at hok hokr
      rw [x86Mach_runBlock] at ihc ihr
      rw [x86Mach_blockLeak]
      exact .call (x86Act_call.mp h) hok ihc hokr ihr
  · intro h
    induction h with
    | ret h => exact .ret (x86Act_ret.mpr h)
    | op h hok _ ih => exact .op (x86Act_op.mpr h) hok ih
    | stack h hops hok _ ih =>
      rw [← x86Mach_BlockOk r] at hok
      rw [← x86Mach_runBlock r] at ih
      rw [← x86Mach_blockLeak r]
      exact .block (x86Act_block.mpr ⟨_, h, hops⟩) hok ih
    | jcc h hc _ ih => exact .branch (x86Act_branch.mpr ⟨_, _, h, hc, rfl⟩) ih
    | call h hok _ hokr _ ihc ihr =>
      rw [← x86Mach_BlockOk r] at hok hokr
      rw [← x86Mach_runBlock r] at ihc ihr
      rw [← x86Mach_blockLeak r]
      exact .call (x86Act_call.mpr h) hok ihc hokr ihr

/-- The halting runs through calls at `x86Mach` are those of `aMachine`. -/
theorem x86Mach_haltsC_iff {prog : List RInstr} {pc : Nat} {sa sa' : AState} :
    (x86Mach r).HaltsC prog pc sa sa' ↔ RInstrSemantics.HaltsC aMachine prog pc sa sa' := by
  constructor
  · intro h
    refine IsaMachine.HaltsC.rec
      (motive := fun pc sa sa' _ => RInstrSemantics.HaltsC aMachine prog pc sa sa')
      (fun h => .ret (x86Act_ret.mp h))
      (fun h _ ih => .go (by rw [← x86Mach_mstep r]; exact h) ih)
      (fun h _ _ ihc ihr => ?_) h
    rw [x86Mach_runBlock, ← DecodedCT.foldl_aMachine_exec] at ihc ihr
    exact .call (x86Act_call.mp h) ihc ihr
  · intro h
    induction h with
    | ret h => exact .ret (x86Act_ret.mpr h)
    | go h _ ih => exact .go (by rw [x86Mach_mstep r]; exact h) ih
    | call h _ _ ihc ihr =>
      rw [DecodedCT.foldl_aMachine_exec, ← x86Mach_runBlock r] at ihc ihr
      exact .call (x86Act_call.mpr h) ihc ihr

/-- The call-free halting runs at `x86Mach` are those of `aMachine`. -/
theorem x86Mach_halts_iff {prog : List RInstr} {pc : Nat} {sa sa' : AState} :
    (x86Mach r).Halts prog pc sa sa' ↔ RInstrSemantics.Halts aMachine prog pc sa sa' := by
  have hr : ∀ {pc pc' : Nat} {s s' : AState}, (x86Mach r).Reaches prog pc s pc' s' ↔
      RInstrSemantics.Reaches aMachine prog pc s pc' s' := by
    intro pc pc' s s'
    constructor
    · intro h
      exact IsaMachine.Reaches.rec
        (motive := fun pc s pc' s' _ => RInstrSemantics.Reaches aMachine prog pc s pc' s')
        (fun pc s => .refl pc s)
        (fun h _ ih => .next (by rw [← x86Mach_mstep r]; exact h) ih) h
    · intro h
      induction h with
      | refl => exact .refl _ _
      | next h _ ih => exact .next (by rw [x86Mach_mstep r]; exact h) ih
  unfold IsaMachine.Halts RInstrSemantics.Halts
  simp only [hr, x86Act_ret]

/-- `DecodedCT.RunL.halts` is the specialisation of `IsaMachine.RunL.haltsC` at
    `x86Mach`. -/
theorem runL_halts_x86 {ok : AState → JInstr 64 → Prop} {prog : List RInstr} {pc : Nat}
    {sa : AState} {t : List CT.CTLeak} {sa' : AState} (h : DecodedCT.RunL r ok prog pc sa t sa') :
    RInstrSemantics.HaltsC aMachine prog pc sa sa' :=
  (x86Mach_haltsC_iff r).mp ((x86Mach_runL_iff r).mpr h).haltsC

/-- `DecodedCT.haltsC_runL` is the specialisation of `IsaMachine.haltsC_runL` at
    `x86Mach`. -/
theorem haltsC_runL_x86 {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    (h : RInstrSemantics.HaltsC aMachine prog pc sa sa') :
    ∃ t, DecodedCT.RunL r (fun _ _ => True) prog pc sa t sa' := by
  obtain ⟨t, ht⟩ := IsaMachine.haltsC_runL ((x86Mach_haltsC_iff r).mpr h)
  exact ⟨t, (x86Mach_runL_iff r).mp ht⟩

/-- `DecodedCT.halts_runL` is the specialisation of `IsaMachine.halts_runL` at `x86Mach`. -/
theorem halts_runL_x86 {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    (h : RInstrSemantics.Halts aMachine prog pc sa sa') :
    ∃ t, DecodedCT.RunL r (fun _ _ => True) prog pc sa t sa' := by
  obtain ⟨t, ht⟩ := IsaMachine.halts_runL ((x86Mach_halts_iff r).mpr h)
  exact ⟨t, (x86Mach_runL_iff r).mp ht⟩

end Machine

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
