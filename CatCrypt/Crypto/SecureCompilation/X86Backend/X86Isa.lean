/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage

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

* `x86Isa_allocPool`, `x86Isa_calleeSaved`, `x86Isa_tied`, `x86Isa_copyMnemonic` and the
  other data equations: the data fields at x86 are the existing constants, by `rfl`.
* `x86LeaksOperands`, `x86Isa_leaksOperands`, `x86Isa_leaksOperands_of`: the leakage regime
  at x86 is `CT.DoitRegime.leaksOperands .doitm` at the mnemonic the printer emits, by `rfl`.
* `x86Isa`, `x86Isa_step`, `x86Isa_lsemFuelMemF`, `x86Isa_lsemFuelMemFk`,
  `x86Isa_evalInstrPMemFk`, `x86Isa_RunIdxOk`, `x86Isa_runL`: the x86 instance and the
  definitional recovery of the x86 interpreters.
* `IsaSym`, `IsaSym.symRun`, `IsaSym.symRun_sound`: the symbolic step record and the exact
  description of a straight-line run by the symbolic run.
* `x86Sym`, `x86Sym_symRun`, `symRun_sound_x86`: the x86 symbolic instance, the definitional
  recovery of `OwnedLprogTV.symRun`, and `OwnedLprogTV.symRun_sound` as the specialisation.
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

/-- The x86 step of a control instruction is the shared control step under `decC`. -/
theorem evalInstrPMemF_ctl (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : isCtl i.fst = true) : evalInstrPMemF P i s = ctlStep decC P i s := by
  obtain ⟨x, tag⟩ := i
  cases x with
  | Llabel k l =>
      rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl rfl]
      rfl
  | Lcond c l => rw [evalInstrPMemF_cond]; rfl
  | Lgoto t =>
      obtain ⟨x, l⟩ := t
      rw [evalInstrPMemF_goto]; rfl
  | _ => simp [isCtl] at h

/-- The table mnemonic of an AT&T base mnemonic of `LprogAsmPrinter.attBase`, `none` for one
    outside that table. -/
def attMnem? : String → Option CT.X86Mnem
  | "add" => some .add
  | "sub" => some .sub
  | "adc" => some .adc
  | "sbb" => some .sbb
  | "and" => some .and
  | "or" => some .or
  | "xor" => some .xor
  | "andn" => some .andn
  | "shl" => some .shl
  | "shr" => some .shr
  | "imul" => some .imul
  | "mov" => some .mov
  | "cmp" => some .cmp
  | "test" => some .test
  | "adcx" => some .adcx
  | "adox" => some .adox
  | "cmove" | "cmovne" | "cmovb" | "cmovae" | "cmovl" | "cmovge" => some .cmovcc
  | "lea" => some .lea
  | _ => none

/-- The table mnemonic of an `Lprog` mnemonic base: the AT&T mnemonic the printer emits for
    it (`LprogAsmPrinter.attBase`), read in the table. -/
def x86MnemOfBase (base : String) : Option CT.X86Mnem :=
  (LprogAsmPrinter.attBase base).bind attMnem?

/-- The x86 leakage regime under DOITM: `CT.DoitRegime.leaksOperands .doitm` at the table
    mnemonic of the base, every operand observable for a base the printer does not name. -/
def x86LeaksOperands (base : String) : Bool :=
  ((x86MnemOfBase base).map (CT.DoitRegime.leaksOperands .doitm)).getD true

/-- **The x86 instruction set**: the data `TwoAddrLegalize.x86Data` with the leakage regime
    `x86LeaksOperands`, the flag machine `evalInstrPMemF` with the branch condition `decC`. -/
def x86Isa : Isa where
  toIsaData := { TwoAddrLegalize.x86Data with leaksOperands := x86LeaksOperands }
  step := evalInstrPMemF
  condEval := decC
  step_ctl := evalInstrPMemF_ctl

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

theorem x86Isa_leaksOperands (base : String) :
    x86Isa.leaksOperands base =
      ((x86MnemOfBase base).map (CT.DoitRegime.leaksOperands .doitm)).getD true := rfl

/-- At a base the printer names, the x86 regime is `CT.DoitRegime.leaksOperands .doitm` of
    its table mnemonic. -/
theorem x86Isa_leaksOperands_of {base : String} {m : CT.X86Mnem}
    (h : x86MnemOfBase base = some m) :
    x86Isa.leaksOperands base = CT.DoitRegime.doitm.leaksOperands m := by
  rw [x86Isa_leaksOperands, h]; rfl

/-- The generic run at `x86Isa` is `lsemFuelMemF`, by unfolding both definitions. -/
theorem x86Isa_lsemFuelMemF : x86Isa.lsemFuelMemF = lsemFuelMemF := by
  delta Isa.lsemFuelMemF lsemFuelMemF; rfl

/-- The generic fetch-and-step at `x86Isa` is `lsemStepPMemF`. -/
theorem x86Isa_lsemStepPMemF : x86Isa.lsemStepPMemF = lsemStepPMemF := rfl

/-- The generic checked step at `x86Isa` is `evalInstrPMemFk`. -/
theorem x86Isa_evalInstrPMemFk : x86Isa.evalInstrPMemFk = evalInstrPMemFk := rfl

/-- The generic checked run at `x86Isa` is `lsemFuelMemFk`, by unfolding both
    definitions. -/
theorem x86Isa_lsemFuelMemFk : x86Isa.lsemFuelMemFk = lsemFuelMemFk := by
  delta Isa.lsemFuelMemFk lsemFuelMemFk; rfl

/-- The generic in-bounds run predicate at `x86Isa` is `RunIdxOk`, by unfolding both
    definitions. -/
theorem x86Isa_RunIdxOk : x86Isa.RunIdxOk = JasminLsemMemChecked.RunIdxOk := by
  delta Isa.RunIdxOk JasminLsemMemChecked.RunIdxOk; rfl

/-- The generic straight-line run at `x86Isa` is `OwnedLprogTV.runL`, by unfolding both
    definitions. -/
theorem x86Isa_runL : x86Isa.runL = OwnedLprogTV.runL := by
  delta Isa.runL OwnedLprogTV.runL; rfl

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

/-- The generic symbolic run at `x86Sym` is `OwnedLprogTV.symRun`, by unfolding both
    definitions. -/
theorem x86Sym_symRun : x86Sym.symRun = OwnedLprogTV.symRun := by
  delta IsaSym.symRun OwnedLprogTV.symRun; rfl

/-- `OwnedLprogTV.symRun_sound` is the specialisation of `IsaSym.symRun_sound` at
    `x86Sym`. -/
theorem symRun_sound_x86 (P : LprogM) (is : List LinstrRM) (ss : SSt)
    (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O Z : Bool) (s : LstateMF)
    (hs : Holds V A C O Z ss s) :
    (OwnedLprogTV.symRun is ss).DescN is.length (OwnedLprogTV.runL P is s) V A C O Z s := by
  rw [← x86Sym_symRun, ← x86Isa_runL]
  exact x86Sym.symRun_sound P is ss V A C O Z s hs

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
