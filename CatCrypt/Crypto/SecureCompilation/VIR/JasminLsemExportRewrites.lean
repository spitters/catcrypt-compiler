/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer

@[expose] public section

set_option autoImplicit false

/-!
# The two body rewrites of the physical export on the flag machine

`ComL.toLfundefPhysAbi` rewrites the exported body twice before allocation:
`aliasRegBody accReg outArg` and `canonicalizeMemrefThread`. Both rename register
names inside `Lopn` operands and change nothing else
(`aliasRegBody_eq_renLcmd`, `canonicalizeMemrefThread_eq_renLcmd`). This module
states what a renaming does to a run of the flag machine `lsemFuelMemF` over
`LstateM`, whose registers and arrays are keyed by name.

## Renaming as a forward simulation

For a renaming `σ` that is injective on a name set `N` and fixes the empty name
(`RenOn σ N`), the relation `RelF σ N s s'` says that the renamed state holds at
`σ r` the register cell and the array cell the original holds at `r`, for every
`r` in `N`, with equal program counter, zero flag, function name and
compile-time-offset word memory. Names outside `N` are unconstrained on both
sides; this is the relation register allocation can consume, since it fixes the
observable names and says nothing about the rest.

* `lsemStepN_ren`, `lsemStepSh_ren`, `lsemStepMC_ren`, `lsemStepCast_ren`,
  `lsemStepMem_ren`, `evalInstrPMemF_ren` — one successful step of an instruction
  whose names lie in `N` is matched by a step of the renamed instruction.
* `lsemFuelMemF_ren` — a halting run of a program is matched, with the same fuel,
  by a halting run of any program that holds the renamed instructions from an
  index `k0` on and has the same labels (`RenProg`), from a state at `k0` or
  later. `lsemFuelMemF_map_renRM` is the case `k0 = 0` of a program and its image.

## `aliasRegBody` on the loop node

`aliasRegName acc out` is injective on the names other than `out`
(`renOn_aliasRegName`). The typed loop node `forLoopLcmdNRtRM` mentions `out` in
its first instruction only, the seed `MOV acc, out`
(`forLoopLcmdNRtRM_fresh`, for a fragment update and the export's name shapes),
and no jump lands on that instruction. `forLoopLcmdNRtRM_alias` runs the seed on
both sides and applies `lsemFuelMemF_ren` from index `1`:
the aliased node, whose wire is `aliasRegBody acc out` of the export's
`forLoopLcmdNRt` (`forLoopLcmdNRtRM_alias_wire`), ends in a state that holds at
`out` what the original holds at `acc` and agrees with it on every other name.
`forLoopLcmdNRtRM_alias_regName_argName` is the instance at `regName k` and
`argName j`.

## `canonicalizeMemrefThread`

The pass sends the result name `d` of a `STOREIDX d, (b, i), v` to its base `b`.
On the name-keyed machine the store writes the array cell `d` and leaves the cell
`b` unchanged, so the renaming is not injective on the names the body uses, and
`lsemFuelMemF_ren` does not apply. `canonicalizeMemrefThread_threadCmd_run` is a
two-instruction body on which the pass changes the computed value: a load through
`b` after the store reads the old array before the pass and the stored array
after it. A loop body that loads through its accumulator base on the next trip
has this shape.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer

/-! ## 1. Names and the renaming side condition -/

/-- The register names an operand mentions: a plain register, and the base and
    index of a SIB element. -/
def opNames : LOperand → List String
  | .reg r => [r]
  | .arrIdx b i _ => [b, i]
  | _ => []

/-- The register names an instruction's wire mentions: the operand names of an
    `Lopn`; no name for any other instruction. -/
def instrNames : LinstrR → List String
  | .Lopn d _ s => (d ++ s).flatMap opNames
  | _ => []

/-- A renaming `σ` is usable on the name set `N`: it is injective on `N`, and the
    empty name (the name `operandName` gives a non-register operand) lies in `N`
    and is fixed. -/
structure RenOn (σ : String → String) (N : String → Prop) : Prop where
  /-- `σ` is injective on `N`. -/
  inj : ∀ a b, N a → N b → σ a = σ b → a = b
  /-- The empty name lies in `N`. -/
  emp : N ""
  /-- The empty name is fixed. -/
  fix : σ "" = ""

/-! ## 2. Inversion of the operand renaming -/

theorem renOperand_reg (σ : String → String) (r : String) :
    renOperand σ (.reg r) = .reg (σ r) := rfl

theorem renOperand_imm (σ : String → String) (n : Nat) :
    renOperand σ (.imm n) = .imm n := rfl

theorem renOperand_arr (σ : String → String) (b : String) (n : Nat) :
    renOperand σ (.arr b n) = .arr b n := rfl

theorem renOperand_arrIdx (σ : String → String) (b i : String) (k : Nat) :
    renOperand σ (.arrIdx b i k) = .arrIdx (σ b) (σ i) k := rfl

@[simp] theorem renOperand_eq_reg (σ : String → String) (o : LOperand) (x : String) :
    renOperand σ o = .reg x ↔ ∃ y, o = .reg y ∧ σ y = x := by
  cases o <;> simp [renOperand]

@[simp] theorem renOperand_eq_imm (σ : String → String) (o : LOperand) (n : Nat) :
    renOperand σ o = .imm n ↔ o = .imm n := by
  cases o <;> simp [renOperand]

@[simp] theorem renOperand_eq_arr (σ : String → String) (o : LOperand) (b : String) (n : Nat) :
    renOperand σ o = .arr b n ↔ o = .arr b n := by
  cases o <;> simp [renOperand]

@[simp] theorem renOperand_eq_arrIdx (σ : String → String) (o : LOperand) (b i : String)
    (k : Nat) :
    renOperand σ o = .arrIdx b i k ↔ ∃ b' i', o = .arrIdx b' i' k ∧ σ b' = b ∧ σ i' = i := by
  cases o <;> simp [renOperand]
  constructor
  · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩

/-! ## 3. The state relations -/

/-- The register-file relation of a renaming `σ` on `N`: equal program counters,
    and the renamed state holds at `σ r` the cell the original holds at `r`, for
    every `r` in `N`. -/
def RelN (σ : String → String) (N : String → Prop) (s s' : LstateN) : Prop :=
  s'.lpc = s.lpc ∧ ∀ r, N r → s'.lvm (σ r) = s.lvm r

variable {σ : String → String} {N : String → Prop}

theorem RelN.getW {s s' : LstateN} (h : RelN σ N s s') {r : String} (hr : N r) (w : Nat) :
    s'.getW (σ r) w = s.getW r w := by
  unfold LstateN.getW
  rw [h.2 r hr]

theorem RelN.readReg {s s' : LstateN} (h : RelN σ N s s') (o : LOperand)
    (ho : ∀ n ∈ opNames o, N n) : readReg s' (renOperand σ o) = readReg s o := by
  cases o <;> simp only [JasminLsemWidthN.readReg, renOperand]
  rw [h.2 _ (ho _ (by simp [opNames]))]

theorem RelN.evalOperandN {s s' : LstateN} (h : RelN σ N s s') (w : Nat) (o : LOperand)
    (ho : ∀ n ∈ opNames o, N n) : evalOperandN s' w (renOperand σ o) = evalOperandN s w o := by
  cases o <;> simp [JasminLsemWidthN.evalOperandN, renOperand]
  exact h.getW (ho _ (by simp [opNames])) w

theorem RelN.operandName {s s' : LstateN} (hσ : RenOn σ N) (h : RelN σ N s s') (w : Nat)
    (o : LOperand) (ho : ∀ n ∈ opNames o, N n) :
    s'.getW (operandName (renOperand σ o)) w = s.getW (operandName o) w := by
  cases o
  case reg r => exact h.getW (ho _ (by simp [opNames])) w
  all_goals
    simp only [renOperand, JasminLsemWidthN.operandName]
    have := h.getW hσ.emp w
    rwa [hσ.fix] at this

theorem RelN.setReg {s s' : LstateN} (hσ : RenOn σ N) (h : RelN σ N s s') {d : String}
    (hd : N d) {w : Nat} (v : BitVec w) :
    RelN σ N ((s.setReg d v).nextPc) ((s'.setReg (σ d) v).nextPc) := by
  refine ⟨by simp [h.1], fun r hr => ?_⟩
  simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg]
  by_cases hrd : r = d
  · subst hrd; simp
  · rw [if_neg (fun he => hrd (hσ.inj _ _ hr hd he)), if_neg hrd]
    exact h.2 r hr

theorem RelN.nextPc {s s' : LstateN} (h : RelN σ N s s') : RelN σ N s.nextPc s'.nextPc :=
  ⟨by simp [h.1], fun r hr => h.2 r hr⟩

/-! ## 4. The register steps under a renaming -/

/-- The names of an `Lopn`, operand by operand. -/
theorem names_of_lopn {d s : List LOperand} {opn : String}
    (hi : ∀ n ∈ instrNames (.Lopn d opn s), N n) :
    ∀ o, o ∈ d ∨ o ∈ s → ∀ n ∈ opNames o, N n := by
  intro o ho n hn
  refine hi n ?_
  simp only [instrNames, List.mem_flatMap, List.mem_append]
  exact ⟨o, ho, hn⟩

set_option hygiene false in
/-- Close a step goal whose renamed side has been rewritten to read the original
    state: split the hypothesis `h`, discard the failing arms, and close the
    successful arm with `RelN.setReg` at the destination membership `hd`. -/
local macro "ren_close " hd:term : tactic =>
  `(tactic| ((repeat' split at h) <;>
      first
        | (simp at h; done)
        | (cases h; refine ⟨_, ?_, RelN.setReg hσ hR $hd _⟩;
           simp only [*, if_true, if_false, reduceIte]; try (rw [if_neg (by decide)]))))

/-- **`lsemStepN` under a renaming.** A successful step of the original
    instruction is matched by a step of the renamed instruction from a related
    state, into a related state. -/
theorem lsemStepN_ren (hσ : RenOn σ N) (i : LinstrR) (hi : ∀ n ∈ instrNames i, N n)
    {s s' t : LstateN} (hR : RelN σ N s s') (h : lsemStepN i s = some t) :
    ∃ t', lsemStepN (renLinstrR σ i) s' = some t' ∧ RelN σ N t t' := by
  unfold lsemStepN at h
  split at h
  · rename_i dst opn c a b
    have ho := names_of_lopn hi
    have hd : N dst := ho (.reg dst) (Or.inl (by simp)) dst (by simp [opNames])
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, lsemStepN,
      hR.operandName hσ 1 c (ho c (Or.inr (by simp))),
      hR.readReg a (ho a (Or.inr (by simp))),
      fun w => hR.evalOperandN w b (ho b (Or.inr (by simp)))]
    ren_close hd
  · rename_i dst opn a b
    have ho := names_of_lopn hi
    have hd : N dst := ho (.reg dst) (Or.inl (by simp)) dst (by simp [opNames])
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, lsemStepN,
      hR.readReg a (ho a (Or.inr (by simp))),
      fun w => hR.evalOperandN w b (ho b (Or.inr (by simp)))]
    cases hra : readReg s a with
    | some wv =>
      obtain ⟨w, va⟩ := wv
      simp only [hra] at h ⊢
      ren_close hd
    | none =>
      simp only [hra] at h ⊢
      cases a with
      | imm n =>
        simp only [renOperand_imm, immFirstN,
          fun w => hR.evalOperandN w b (ho b (Or.inr (by simp)))] at h ⊢
        cases hb : evalOperandN s (widthFromTag opn) b with
        | none => simp [hb] at h
        | some vb =>
          simp only [hb] at h ⊢
          obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
          exact ⟨_, by rw [hv]; rfl, RelN.setReg hσ hR hd _⟩
      | _ => simp at h
  · rename_i dst opn n
    have ho := names_of_lopn hi
    have hd : N dst := ho (.reg dst) (Or.inl (by simp)) dst (by simp [opNames])
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, renOperand_imm,
      lsemStepN]
    ren_close hd
  · rename_i dst opn a
    have ho := names_of_lopn hi
    have hd : N dst := ho (.reg dst) (Or.inl (by simp)) dst (by simp [opNames])
    have hra : readReg s' (.reg (σ a)) = readReg s (.reg a) :=
      hR.readReg (.reg a) (ho (.reg a) (Or.inr (by simp)))
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, lsemStepN, hra]
    ren_close hd
  · rename_i dst opn b x sc
    have ho := names_of_lopn hi
    have hd : N dst := ho (.reg dst) (Or.inl (by simp)) dst (by simp [opNames])
    have hb : s'.getW (σ b) 64 = s.getW b 64 :=
      hR.getW (ho (.arrIdx b x sc) (Or.inr (by simp)) b (by simp [opNames])) 64
    have hx : s'.getW (σ x) 64 = s.getW x 64 :=
      hR.getW (ho (.arrIdx b x sc) (Or.inr (by simp)) x (by simp [opNames])) 64
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, renOperand_arrIdx,
      lsemStepN, hb, hx]
    ren_close hd
  · exact absurd h (by simp)
  · cases h; exact ⟨_, rfl, hR.nextPc⟩
  · cases h; exact ⟨_, rfl, hR.nextPc⟩
  all_goals exact absurd h (by simp)

/-! ## 5. The structured recognisers under a renaming -/

/-- A renamed instruction is an `Lopn` exactly when the original is, with renamed
    operand lists. -/
theorem renLinstrR_eq_lopn {i : LinstrR} {d s : List LOperand} {o : String} :
    renLinstrR σ i = .Lopn d o s ↔
      ∃ d' s', i = .Lopn d' o s' ∧ d'.map (renOperand σ) = d ∧ s'.map (renOperand σ) = s := by
  cases i <;> simp [renLinstrR]
  tauto

set_option hygiene false in
/-- Prove that a structured recogniser commutes with the renaming: invert the
    renamed wire when the recogniser fires on it, and refute the firing pattern on
    the original otherwise. -/
local macro "ren_recog" : tactic =>
  `(tactic| (
      split
      · next heq =>
          obtain ⟨d', s', rfl, hd, hs⟩ := renLinstrR_eq_lopn.mp heq
          simp [List.map_eq_cons_iff] at hd hs
          grind
      · next hne =>
          split
          · exfalso; apply hne; rfl
          · rfl))

theorem sarStruct?_ren (i : LinstrR) :
    sarStruct? (renLinstrR σ i) = (sarStruct? i).map (fun p => (σ p.1, σ p.2.1, p.2.2)) := by
  unfold sarStruct?; ren_recog

theorem mulhiStruct?_ren (i : LinstrR) :
    mulhiStruct? (renLinstrR σ i)
      = (mulhiStruct? i).map (fun p => (σ p.1, σ p.2.1, σ p.2.2)) := by
  unfold mulhiStruct?; ren_recog

theorem adcxStruct?_ren (i : LinstrR) :
    adcxStruct? (renLinstrR σ i)
      = (adcxStruct? i).map (fun p => (σ p.1, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold adcxStruct?; ren_recog

theorem adcxhiStruct?_ren (i : LinstrR) :
    adcxhiStruct? (renLinstrR σ i)
      = (adcxhiStruct? i).map (fun p => (σ p.1, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold adcxhiStruct?; ren_recog

theorem sbbStruct?_ren (i : LinstrR) :
    sbbStruct? (renLinstrR σ i)
      = (sbbStruct? i).map (fun p => (σ p.1, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold sbbStruct?; ren_recog

theorem sbbhiStruct?_ren (i : LinstrR) :
    sbbhiStruct? (renLinstrR σ i)
      = (sbbhiStruct? i).map (fun p => (σ p.1, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold sbbhiStruct?; ren_recog

theorem castStruct?_ren (i : LinstrR) :
    castStruct? (renLinstrR σ i) = (castStruct? i).map (fun p => (σ p.1, σ p.2)) := by
  unfold castStruct?; ren_recog

theorem movImmStruct?_ren (i : LinstrR) :
    movImmStruct? (renLinstrR σ i) = (movImmStruct? i).map (fun p => (σ p.1, p.2)) := by
  unfold movImmStruct?; ren_recog

theorem loadStruct?_ren (i : LinstrR) :
    loadStruct? (renLinstrR σ i)
      = (loadStruct? i).map (fun p => (σ p.1, σ p.2.1, σ p.2.2)) := by
  unfold loadStruct?; ren_recog

theorem storeStruct?_ren (i : LinstrR) :
    storeStruct? (renLinstrR σ i)
      = (storeStruct? i).map (fun p => (σ p.1, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold storeStruct?; ren_recog

theorem loadCStruct?_ren (i : LinstrR) :
    loadCStruct? (renLinstrR σ i)
      = (loadCStruct? i).map (fun p => (σ p.1, p.2.1, p.2.2)) := by
  unfold loadCStruct?; ren_recog

theorem storeCStruct?_ren (i : LinstrR) :
    storeCStruct? (renLinstrR σ i)
      = (storeCStruct? i).map (fun p => (p.1, p.2.1, σ p.2.2)) := by
  unfold storeCStruct?; ren_recog

/-- An `Lopn` whose mnemonic is not `ZEROARR` is no array zeroing. -/
theorem zeroStruct?_of_ne {ds : List LOperand} {opn : String} {ss : List LOperand}
    (h : opn ≠ "ZEROARR") : zeroStruct? (.Lopn ds opn ss) = none := by
  unfold zeroStruct?
  split
  · rename_i heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨-, rfl, -⟩ := heq
    exact if_neg h
  · rfl

theorem zeroStruct?_ren (i : LinstrR) :
    zeroStruct? (renLinstrR σ i) = (zeroStruct? i).map σ := by
  unfold zeroStruct?; ren_recog

/-- An `Lopn` whose mnemonic is not `STOREIMM` is no constant-index store. -/
theorem storeImmStruct?_of_ne {ds : List LOperand} {opn : String} {ss : List LOperand}
    (h : opn ≠ "STOREIMM") : storeImmStruct? (.Lopn ds opn ss) = none := by
  unfold storeImmStruct?
  split
  · rename_i heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨-, rfl, -⟩ := heq
    exact if_neg h
  · rfl

theorem storeImmStruct?_ren (i : LinstrR) :
    storeImmStruct? (renLinstrR σ i)
      = (storeImmStruct? i).map (fun p => (σ p.1, σ p.2.1, σ p.2.2.1, p.2.2.2)) := by
  unfold storeImmStruct?; ren_recog

theorem cmpArgs?_ren (i : LinstrRM) :
    cmpArgs? (renRM σ i) = (cmpArgs? i).map (fun p => (renOperand σ p.1, renOperand σ p.2)) := by
  obtain ⟨w, t⟩ := i
  unfold cmpArgs? renRM; dsimp only; ren_recog

theorem movRegArgs?_ren (i : LinstrRM) :
    movRegArgs? (renRM σ i) = (movRegArgs? i).map (fun p => (σ p.1, σ p.2)) := by
  obtain ⟨w, t⟩ := i
  unfold movRegArgs? renRM; dsimp only; ren_recog

theorem flagCondCC?_ren (i : LinstrRM) : flagCondCC? (renRM σ i) = flagCondCC? i := by
  obtain ⟨w, t⟩ := i
  cases w <;> rfl

theorem aluFlagOp?_ren (i : LinstrRM) :
    aluFlagOp? (renRM σ i)
      = (aluFlagOp? i).map (fun p => (p.1, renOperand σ p.2.1, renOperand σ p.2.2)) := by
  obtain ⟨w, t⟩ := i
  unfold aluFlagOp? renRM; dsimp only; ren_recog

theorem carryArgs?_ren (i : LinstrRM) :
    carryArgs? (renRM σ i)
      = (carryArgs? i).map
          (fun p => (p.1, σ p.2.1, renOperand σ p.2.2.1, renOperand σ p.2.2.2)) := by
  obtain ⟨w, t⟩ := i
  unfold carryArgs? renRM; dsimp only; ren_recog

/-! ## 6. The names a recogniser returns -/

set_option hygiene false in
/-- Prove that the names a recogniser returns are names of the instruction. -/
local macro "recog_names" : tactic =>
  `(tactic| (
      split at h
      · split at h
        · cases h; simp [instrNames, opNames]
        · simp at h
      · simp at h))

theorem sarStruct?_names {i : LinstrR} {p : String × String × Nat}
    (h : sarStruct? i = some p) : p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i := by
  unfold sarStruct? at h; recog_names

theorem mulhiStruct?_names {i : LinstrR} {p : String × String × String}
    (h : mulhiStruct? i = some p) :
    p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i ∧ p.2.2 ∈ instrNames i := by
  unfold mulhiStruct? at h; recog_names

theorem adcxStruct?_names {i : LinstrR} {p : String × String × String × String}
    (h : adcxStruct? i = some p) :
    p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i ∧ p.2.2.1 ∈ instrNames i
      ∧ p.2.2.2 ∈ instrNames i := by
  unfold adcxStruct? at h; recog_names

theorem adcxhiStruct?_names {i : LinstrR} {p : String × String × String × String}
    (h : adcxhiStruct? i = some p) :
    p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i ∧ p.2.2.1 ∈ instrNames i
      ∧ p.2.2.2 ∈ instrNames i := by
  unfold adcxhiStruct? at h; recog_names

theorem sbbStruct?_names {i : LinstrR} {p : String × String × String × String}
    (h : sbbStruct? i = some p) :
    p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i ∧ p.2.2.1 ∈ instrNames i
      ∧ p.2.2.2 ∈ instrNames i := by
  unfold sbbStruct? at h; recog_names

theorem sbbhiStruct?_names {i : LinstrR} {p : String × String × String × String}
    (h : sbbhiStruct? i = some p) :
    p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i ∧ p.2.2.1 ∈ instrNames i
      ∧ p.2.2.2 ∈ instrNames i := by
  unfold sbbhiStruct? at h; recog_names

theorem castStruct?_names {i : LinstrR} {p : String × String}
    (h : castStruct? i = some p) : p.1 ∈ instrNames i ∧ p.2 ∈ instrNames i := by
  unfold castStruct? at h; recog_names

theorem movImmStruct?_names {i : LinstrR} {p : String × Nat}
    (h : movImmStruct? i = some p) : p.1 ∈ instrNames i := by
  unfold movImmStruct? at h
  split at h
  · cases h; simp [instrNames, opNames]
  · simp at h

theorem loadStruct?_names {i : LinstrR} {p : String × String × String}
    (h : loadStruct? i = some p) :
    p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i ∧ p.2.2 ∈ instrNames i := by
  unfold loadStruct? at h; recog_names

theorem storeStruct?_names {i : LinstrR} {p : String × String × String × String}
    (h : storeStruct? i = some p) :
    p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i ∧ p.2.2.1 ∈ instrNames i
      ∧ p.2.2.2 ∈ instrNames i := by
  unfold storeStruct? at h; recog_names

theorem loadCStruct?_names {i : LinstrR} {p : String × String × Nat}
    (h : loadCStruct? i = some p) : p.1 ∈ instrNames i := by
  unfold loadCStruct? at h; recog_names

theorem storeCStruct?_names {i : LinstrR} {p : String × Nat × String}
    (h : storeCStruct? i = some p) : p.2.2 ∈ instrNames i := by
  unfold storeCStruct? at h; recog_names

theorem zeroStruct?_names {i : LinstrR} {d : String}
    (h : zeroStruct? i = some d) : d ∈ instrNames i := by
  unfold zeroStruct? at h; recog_names

theorem storeImmStruct?_names {i : LinstrR} {p : String × String × String × Nat}
    (h : storeImmStruct? i = some p) :
    p.1 ∈ instrNames i ∧ p.2.1 ∈ instrNames i ∧ p.2.2.1 ∈ instrNames i := by
  unfold storeImmStruct? at h; recog_names

/-! ## 7. The shift, carry and cast steps under a renaming -/

/-- A register read at a renamed name of `N` is the original read. -/
theorem RelN.readReg_reg {s s' : LstateN} (h : RelN σ N s s') {r : String} (hr : N r) :
    JasminLsemWidthN.readReg s' (.reg (σ r)) = JasminLsemWidthN.readReg s (.reg r) := by
  simp only [JasminLsemWidthN.readReg]
  rw [h.2 r hr]

/-- **`lsemStepSh` under a renaming.** -/
theorem lsemStepSh_ren (hσ : RenOn σ N) (i : LinstrR) (hi : ∀ n ∈ instrNames i, N n)
    {s s' t : LstateN} (hR : RelN σ N s s') (h : lsemStepSh i s = some t) :
    ∃ t', lsemStepSh (renLinstrR σ i) s' = some t' ∧ RelN σ N t t' := by
  unfold lsemStepSh at h ⊢
  rw [sarStruct?_ren]
  cases hs : sarStruct? i with
  | none =>
      rw [hs] at h
      exact lsemStepN_ren hσ i hi hR h
  | some p =>
      obtain ⟨d, a, n⟩ := p
      simp only [hs] at h
      obtain ⟨hd, ha⟩ := sarStruct?_names hs
      simp only [Option.map_some, hR.readReg_reg (hi _ ha)]
      ren_close (hi _ hd)

/-- **`lsemStepMC` under a renaming.** -/
theorem lsemStepMC_ren (hσ : RenOn σ N) (i : LinstrR) (hi : ∀ n ∈ instrNames i, N n)
    {s s' t : LstateN} (hR : RelN σ N s s') (h : lsemStepMC i s = some t) :
    ∃ t', lsemStepMC (renLinstrR σ i) s' = some t' ∧ RelN σ N t t' := by
  unfold lsemStepMC at h ⊢
  rw [mulhiStruct?_ren, adcxStruct?_ren, adcxhiStruct?_ren, sbbStruct?_ren, sbbhiStruct?_ren]
  cases h1 : mulhiStruct? i with
  | some p =>
      obtain ⟨d, a, b⟩ := p
      simp only [h1] at h
      obtain ⟨hd, ha, hb⟩ := mulhiStruct?_names h1
      simp only [Option.map_some, hR.readReg_reg (hi _ ha), fun w => hR.getW (hi _ hb) w]
      ren_close (hi _ hd)
  | none =>
  simp only [h1, Option.map_none] at h ⊢
  cases h2 : adcxStruct? i with
  | some p =>
      obtain ⟨d, a, b, c⟩ := p
      simp only [h2] at h
      obtain ⟨hd, ha, hb, hc⟩ := adcxStruct?_names h2
      simp only [Option.map_some, hR.readReg_reg (hi _ ha), fun w => hR.getW (hi _ hb) w,
        hR.getW (hi _ hc) 1]
      ren_close (hi _ hd)
  | none =>
  simp only [h2, Option.map_none] at h ⊢
  cases h3 : adcxhiStruct? i with
  | some p =>
      obtain ⟨d, a, b, c⟩ := p
      simp only [h3] at h
      obtain ⟨hd, ha, hb, hc⟩ := adcxhiStruct?_names h3
      simp only [Option.map_some, hR.readReg_reg (hi _ ha), fun w => hR.getW (hi _ hb) w,
        hR.getW (hi _ hc) 1]
      ren_close (hi _ hd)
  | none =>
  simp only [h3, Option.map_none] at h ⊢
  cases h4 : sbbStruct? i with
  | some p =>
      obtain ⟨d, a, b, c⟩ := p
      simp only [h4] at h
      obtain ⟨hd, ha, hb, hc⟩ := sbbStruct?_names h4
      simp only [Option.map_some, hR.readReg_reg (hi _ ha), fun w => hR.getW (hi _ hb) w,
        hR.getW (hi _ hc) 1]
      ren_close (hi _ hd)
  | none =>
  simp only [h4, Option.map_none] at h ⊢
  cases h5 : sbbhiStruct? i with
  | some p =>
      obtain ⟨d, a, b, c⟩ := p
      simp only [h5] at h
      obtain ⟨hd, ha, hb, hc⟩ := sbbhiStruct?_names h5
      simp only [Option.map_some, hR.readReg_reg (hi _ ha), fun w => hR.getW (hi _ hb) w,
        hR.getW (hi _ hc) 1]
      ren_close (hi _ hd)
  | none =>
  simp only [h5, Option.map_none] at h ⊢
  exact lsemStepSh_ren hσ i hi hR h

/-- **`lsemStepCast` under a renaming.** -/
theorem lsemStepCast_ren (hσ : RenOn σ N) (i : LinstrR) (cd : Option Nat)
    (hi : ∀ n ∈ instrNames i, N n)
    {s s' t : LstateN} (hR : RelN σ N s s') (h : lsemStepCast (i, cd) s = some t) :
    ∃ t', lsemStepCast (renLinstrR σ i, cd) s' = some t' ∧ RelN σ N t t' := by
  cases cd with
  | none =>
      rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)] at h
      rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
      exact lsemStepMC_ren hσ i hi hR h
  | some w' =>
      unfold lsemStepCast at h ⊢
      dsimp only at h ⊢
      rw [castStruct?_ren, movImmStruct?_ren]
      cases h1 : castStruct? i with
      | none =>
          cases h2 : movImmStruct? i with
          | none =>
              simp only [h1, h2, Option.map_none] at h ⊢
              exact lsemStepMC_ren hσ i hi hR h
          | some p =>
              obtain ⟨d, n⟩ := p
              have hd := movImmStruct?_names h2
              simp only [h1, h2, Option.map_none, Option.map_some] at h ⊢
              cases h
              exact ⟨_, rfl, RelN.setReg hσ hR (hi _ hd) _⟩
      | some p =>
          obtain ⟨d, a⟩ := p
          obtain ⟨hd, ha⟩ := castStruct?_names h1
          simp only [h1, Option.map_some, hR.readReg_reg (hi _ ha)] at h ⊢
          ren_close (hi _ hd)

/-! ## 8. The memory step under a renaming -/

/-- The memory-state relation of a renaming `σ` on `N`: the register files are
    related, the renamed state holds at `σ r` the array cell the original holds at
    `r` for every `r` in `N`, and the compile-time-offset word memories are
    equal (an `.arr` operand is not renamed). -/
def RelM (σ : String → String) (N : String → Prop) (s s' : LstateM) : Prop :=
  RelN σ N s.reg s'.reg ∧ (∀ r, N r → s'.larr (σ r) = s.larr r) ∧ s'.lmem = s.lmem

theorem RelM.getArr {s s' : LstateM} (h : RelM σ N s s') {r : String} (hr : N r) (w n : Nat) :
    s'.getArr (σ r) w n = s.getArr r w n := by
  unfold LstateM.getArr
  rw [h.2.1 r hr]

theorem RelM.setReg {s s' : LstateM} (hσ : RenOn σ N) (h : RelM σ N s s') {d : String}
    (hd : N d) {w : Nat} (v : BitVec w) :
    RelM σ N ((s.setReg d v).nextPc) ((s'.setReg (σ d) v).nextPc) :=
  ⟨RelN.setReg hσ h.1 hd v, h.2.1, h.2.2⟩

theorem RelM.setArr {s s' : LstateM} (hσ : RenOn σ N) (h : RelM σ N s s') {d : String}
    (hd : N d) {w n : Nat} (arr : Fin n → BitVec w) :
    RelM σ N ((s.setArr d arr).nextPc) ((s'.setArr (σ d) arr).nextPc) := by
  refine ⟨h.1.nextPc, fun r hr => ?_, h.2.2⟩
  simp only [LstateM.larr_nextPc, LstateM.larr_setArr]
  by_cases hrd : r = d
  · subst hrd; simp
  · rw [if_neg (fun he => hrd (hσ.inj _ _ hr hd he)), if_neg hrd]
    exact h.2.1 r hr

theorem RelM.storeMemC {s s' : LstateM} (h : RelM σ N s s') (base : String) (off : Int)
    (v : BitVec 64) :
    RelM σ N ((s.storeMemC base off v).nextPc) ((s'.storeMemC base off v).nextPc) := by
  refine ⟨h.1.nextPc, h.2.1, ?_⟩
  simp only [LstateM.lmem_nextPc, LstateM.lmem_storeMemC, h.2.2]

/-- The register-binding delegate of the memory step under a renaming. -/
theorem lsemStepMem_delegate_ren (hσ : RenOn σ N) (i : LinstrR) (cd : Option Nat)
    (hi : ∀ n ∈ instrNames i, N n) {s s' t : LstateM} (hR : RelM σ N s s')
    (h : (lsemStepCast (i, cd) s.reg).map (fun r => { s with reg := r }) = some t) :
    ∃ t', (lsemStepCast (renLinstrR σ i, cd) s'.reg).map (fun r => { s' with reg := r })
        = some t' ∧ RelM σ N t t' := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r', hr', hRr⟩ := lsemStepCast_ren hσ i cd hi hR.1 hr
  exact ⟨{ s' with reg := r' }, by rw [hr']; rfl, hRr, hR.2.1, hR.2.2⟩

set_option hygiene false in
/-- `ren_close` with the closing relation proof given explicitly. -/
local macro "ren_close_with " t:term : tactic =>
  `(tactic| ((repeat' split at h) <;>
      first
        | (simp at h; done)
        | (cases h; refine ⟨_, ?_, $t⟩;
           simp only [*, if_true, if_false, reduceIte])))

/-- **`lsemStepMem` under a renaming.** A successful typed memory step of the
    original instruction is matched by a step of the renamed instruction from a
    related state, into a related state. -/
theorem lsemStepMem_ren (hσ : RenOn σ N) (i : LinstrRM) (hi : ∀ n ∈ instrNames i.1, N n)
    {s s' t : LstateM} (hR : RelM σ N s s') (h : lsemStepMem i s = some t) :
    ∃ t', lsemStepMem (renRM σ i) s' = some t' ∧ RelM σ N t t' := by
  obtain ⟨wire, tag⟩ := i
  unfold lsemStepMem at h ⊢
  cases tag with
  | reg cd => exact lsemStepMem_delegate_ren hσ wire cd hi hR h
  | load w n =>
      dsimp only [renRM] at h ⊢
      rw [loadStruct?_ren]
      cases h1 : loadStruct? wire with
      | none =>
          simp only [h1, Option.map_none] at h ⊢
          exact lsemStepMem_delegate_ren hσ wire none hi hR h
      | some p =>
          obtain ⟨d, b, x⟩ := p
          obtain ⟨hd, hb, hx⟩ := loadStruct?_names h1
          simp only [h1, Option.map_some, hR.getArr (hi _ hb), hR.1.getW (hi _ hx)] at h ⊢
          ren_close_with (RelM.setReg hσ hR (hi _ hd) _)
  | store w n =>
      dsimp only [renRM] at h ⊢
      rw [storeStruct?_ren]
      cases h1 : storeStruct? wire with
      | none =>
          simp only [h1, Option.map_none] at h ⊢
          exact lsemStepMem_delegate_ren hσ wire none hi hR h
      | some p =>
          obtain ⟨d, b, x, v⟩ := p
          obtain ⟨hd, hb, hx, hv⟩ := storeStruct?_names h1
          simp only [h1, Option.map_some, hR.getArr (hi _ hb), hR.1.getW (hi _ hx),
            hR.1.getW (hi _ hv)] at h ⊢
          ren_close_with (RelM.setArr hσ hR (hi _ hd) _)
  | loadC =>
      dsimp only [renRM] at h ⊢
      rw [loadCStruct?_ren]
      cases h1 : loadCStruct? wire with
      | none => simp [h1] at h
      | some p =>
          obtain ⟨d, b, off⟩ := p
          have hd := loadCStruct?_names h1
          simp only [h1, Option.map_some, hR.2.2] at h ⊢
          ren_close_with (RelM.setReg hσ hR (hi _ hd) _)
  | storeC =>
      dsimp only [renRM] at h ⊢
      rw [storeCStruct?_ren]
      cases h1 : storeCStruct? wire with
      | none => simp [h1] at h
      | some p =>
          obtain ⟨b, off, src⟩ := p
          have hsrc := storeCStruct?_names h1
          simp only [h1, Option.map_some, hR.1.getW (hi _ hsrc)] at h ⊢
          ren_close_with (RelM.storeMemC hR _ _ _)
  | zero w n =>
      dsimp only [renRM] at h ⊢
      rw [zeroStruct?_ren]
      cases h1 : zeroStruct? wire with
      | none => simp [h1] at h
      | some d =>
          have hd := zeroStruct?_names h1
          simp only [h1, Option.map_some] at h ⊢
          cases h
          exact ⟨_, rfl, RelM.setArr hσ hR (hi _ hd) _⟩
  | storeImm w n =>
      dsimp only [renRM] at h ⊢
      rw [storeImmStruct?_ren]
      cases h1 : storeImmStruct? wire with
      | none => simp [h1] at h
      | some p =>
          obtain ⟨d, b, v, k⟩ := p
          obtain ⟨hd, hb, hv⟩ := storeImmStruct?_names h1
          simp only [h1, Option.map_some, hR.getArr (hi _ hb), hR.1.getW (hi _ hv)] at h ⊢
          ren_close_with (RelM.setArr hσ hR (hi _ hd) _)

/-! ## 9. The flag machine under a renaming -/

theorem RelM.nextPc {s s' : LstateM} (h : RelM σ N s s') : RelM σ N s.nextPc s'.nextPc :=
  ⟨h.1.nextPc, h.2.1, h.2.2⟩

theorem RelM.setLpc {s s' : LstateM} (h : RelM σ N s s') (pc : Nat) :
    RelM σ N (s.setLpc pc) (s'.setLpc pc) :=
  ⟨⟨rfl, h.1.2⟩, h.2.1, h.2.2⟩

/-- The flag-machine state relation of a renaming: related memory states, the
    same function name, the same zero flag and the same carry and overflow flags. -/
def RelF (σ : String → String) (N : String → Prop) (s s' : LstateMF) : Prop :=
  RelM σ N s.prog.base s'.prog.base ∧ s'.prog.lfn = s.prog.lfn ∧ s'.zf = s.zf
    ∧ s'.prog.base.cf = s.prog.base.cf ∧ s'.prog.base.of = s.prog.base.of

/-- A memory step keeps the carry and overflow flags. -/
theorem lsemStepMem_flags {i : LinstrRM} {s b : LstateM} (h : lsemStepMem i s = some b) :
    b.cf = s.cf ∧ b.of = s.of := by
  have hs := lsemStepMem_setFlags i s s.cf s.of
  rw [show ({ s with cf := s.cf, of := s.of } : LstateM) = s from rfl, h,
    Option.map_some, Option.some.injEq] at hs
  rw [hs]
  exact ⟨rfl, rfl⟩

/-- A jump keeps the carry and overflow flags. -/
theorem evalJumpMem_flags {P : LprogM} {l : LLabel} {p q : LstatePM}
    (hq : evalJumpMem P l p = some q) : q.base.cf = p.base.cf ∧ q.base.of = p.base.of := by
  unfold evalJumpMem at hq
  split at hq
  · cases hq; exact ⟨rfl, rfl⟩
  · cases hq

/-- A labelled step keeps the carry and overflow flags. -/
theorem evalInstrPMemL_flags {P : LprogM} {i : LinstrRM} {p q : LstatePM}
    (h : evalInstrPMemL P i p = some q) : q.base.cf = p.base.cf ∧ q.base.of = p.base.of := by
  have hj : ∀ {l : LLabel} {q : LstatePM}, evalJumpMem P l p = some q →
      q.base.cf = p.base.cf ∧ q.base.of = p.base.of := fun hq => evalJumpMem_flags hq
  unfold evalInstrPMemL at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · exact hj h
    · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · exact hj h
    · cases h
  · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact lsemStepMem_flags hb

/-- The flag writes of `withALUFlags` preserve the renaming relation. -/
theorem RelM.withALUFlags {b b' : LstateM} (h : RelM σ N b b') (i i' : LinstrRM)
    (s0 s0' : LstateM) : RelM σ N (withALUFlags i s0 b) (withALUFlags i' s0' b') := by
  unfold RelM
  simp only [withALUFlags_reg, withALUFlags_larr, withALUFlags_lmem]
  exact h

/-- The register step does not step a two-source instruction whose stripped mnemonic is a
    carry-family mnemonic. -/
theorem lsemStepCast_carry (d opn : String) (a b : LOperand)
    (hm : stripWidthTag opn = "ADC" ∨ stripWidthTag opn = "SBB" ∨ stripWidthTag opn = "ADCX"
      ∨ stripWidthTag opn = "ADOX")
    (cd : Option Nat) (r : LstateN) :
    lsemStepCast (.Lopn [.reg d] opn [a, b], cd) r = none := by
  have hmh : mulhiStruct? (.Lopn [.reg d] opn [a, b]) = none := by
    unfold mulhiStruct?
    split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      rcases hm with h | h | h | h <;> simp [h]
    · rfl
  have hsar : sarStruct? (.Lopn [.reg d] opn [a, b]) = none := by
    unfold sarStruct?
    split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      rcases hm with h | h | h | h <;> simp [h]
    · rfl
  rw [lsemStepCast_of_delegate _ _
      (Or.inl ⟨by simp [castStruct?], by simp [movImmStruct?]⟩),
    lsemStepMC_of_delegate _ _ hmh (by cases a <;> cases b <;> rfl)
      (by cases a <;> cases b <;> rfl) (by cases a <;> cases b <;> rfl)
      (by cases a <;> cases b <;> rfl),
    lsemStepSh_of_not_sar _ _ hsar]
  simp only [lsemStepN]
  cases readReg r a with
  | none =>
      cases a <;> simp only [immFirstN]
      cases evalOperandN r (widthFromTag opn) b with
      | none => rfl
      | some vb => rcases hm with h | h | h | h <;> simp [h, applyOpnN]
  | some wv =>
      obtain ⟨w, va⟩ := wv
      simp only []
      cases evalOperandN r w b with
      | none => rfl
      | some vb => rcases hm with h | h | h | h <;> simp [h, applyOpnN, cmpOfName?]

/-- The memory step does not step a carry-family instruction. -/
theorem lsemStepMem_of_carryArgs {i : LinstrRM} {p : CarryOp × String × LOperand × LOperand}
    (h : carryArgs? i = some p) (s : LstateM) : lsemStepMem i s = none := by
  obtain ⟨wire, tag⟩ := i
  unfold carryArgs? at h
  dsimp only at h
  split at h
  · rename_i d opn a b
    have hm : stripWidthTag opn = "ADC" ∨ stripWidthTag opn = "SBB"
        ∨ stripWidthTag opn = "ADCX" ∨ stripWidthTag opn = "ADOX" := by
      split_ifs at h <;> subst_vars
      · exact Or.inl (by decide +kernel)
      · exact Or.inr (Or.inl (by decide +kernel))
      · exact Or.inr (Or.inr (Or.inl (by decide +kernel)))
      · exact Or.inr (Or.inr (Or.inr (by decide +kernel)))
    have hst : storeStruct? (.Lopn [.reg d] opn [a, b]) = none := by
      unfold storeStruct?
      split
      · rename_i heq
        simp only [LinstrR.Lopn.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        rw [if_neg]
        intro he
        subst he
        rcases hm with h | h | h | h <;> revert h <;> decide +kernel
      · rfl
    have hz : zeroStruct? (.Lopn [.reg d] opn [a, b]) = none := zeroStruct?_of_ne (by
      rintro rfl
      rcases hm with h | h | h | h <;> revert h <;> decide +kernel)
    cases tag <;> simp [lsemStepMem, loadStruct?, hst, hz, storeImmStruct?, loadCStruct?,
      storeCStruct?, lsemStepCast_carry d opn a b hm]
  · cases h

/-- A carry-family step under a renaming. -/
theorem carryStep_ren (hσ : RenOn σ N) {op : CarryOp} {d : String} {a c : LOperand}
    (hd : N d) (ha : ∀ n ∈ opNames a, N n) (hc : ∀ n ∈ opNames c, N n)
    {s s' t : LstateM} (hR : RelM σ N s s') (hf : s'.cf = s.cf ∧ s'.of = s.of)
    (h : carryStep op d a c s = some t) :
    ∃ t', carryStep op (σ d) (renOperand σ a) (renOperand σ c) s' = some t'
      ∧ RelM σ N t t' ∧ t'.cf = t.cf ∧ t'.of = t.of := by
  unfold carryStep at h ⊢
  rw [hR.1.evalOperandN 64 a ha, hR.1.evalOperandN 64 c hc, hf.1, hf.2]
  split at h
  · cases op <;> cases h <;>
      exact ⟨_, rfl, ⟨(RelM.setReg hσ hR hd _).1, hR.2.1, hR.2.2⟩,
        by first | rfl | exact hf.1, by first | rfl | exact hf.2⟩
  · cases h

/-- The register step does not step a two-source `MOV`. -/
theorem lsemStepCast_mov2 (d opn : String) (a b : LOperand) (hm : stripWidthTag opn = "MOV")
    (cd : Option Nat) (r : LstateN) :
    lsemStepCast (.Lopn [.reg d] opn [a, b], cd) r = none := by
  have hmh : mulhiStruct? (.Lopn [.reg d] opn [a, b]) = none := by
    unfold mulhiStruct?
    split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      simp [hm]
    · rfl
  have hsar : sarStruct? (.Lopn [.reg d] opn [a, b]) = none := by
    unfold sarStruct?
    split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      simp [hm]
    · rfl
  rw [lsemStepCast_of_delegate _ _
      (Or.inl ⟨by simp [castStruct?], by simp [movImmStruct?]⟩),
    lsemStepMC_of_delegate _ _ hmh (by cases a <;> cases b <;> rfl)
      (by cases a <;> cases b <;> rfl) (by cases a <;> cases b <;> rfl)
      (by cases a <;> cases b <;> rfl),
    lsemStepSh_of_not_sar _ _ hsar]
  simp only [lsemStepN]
  cases readReg r a with
  | none =>
      cases a <;> simp only [immFirstN]
      cases evalOperandN r (widthFromTag opn) b with
      | none => rfl
      | some vb => simp [hm, applyOpnN]
  | some wv =>
      obtain ⟨w, va⟩ := wv
      simp only []
      cases evalOperandN r w b with
      | none => rfl
      | some vb => simp [hm, applyOpnN, cmpOfName?]

/-- The memory step does not step a flag-quiet lift instruction. -/
theorem lsemStepMem_of_wideArgs {i : LinstrRM} {w : WideOp} (h : wideArgs? i = some w)
    (s : LstateM) : lsemStepMem i s = none := by
  obtain ⟨wire, tag⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · rename_i d opn a b
    have hm : stripWidthTag opn = "MOV" := by
      split_ifs at h with he
      · subst he; decide +kernel
    have hst : storeStruct? (.Lopn [.reg d] opn [a, b]) = none := by
      unfold storeStruct?
      split
      · rename_i heq
        simp only [LinstrR.Lopn.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        rw [if_neg]
        intro he
        subst he
        revert hm; decide +kernel
      · rfl
    have hz : zeroStruct? (.Lopn [.reg d] opn [a, b]) = none := zeroStruct?_of_ne (by
      rintro rfl
      revert hm; decide +kernel)
    cases tag <;> simp [lsemStepMem, loadStruct?, hst, hz, storeImmStruct?, loadCStruct?,
      storeCStruct?, lsemStepCast_mov2 d opn a b hm]
  · cases tag <;> simp [lsemStepMem, loadStruct?, storeStruct?, zeroStruct?, storeImmStruct?,
      loadCStruct?, storeCStruct?,
      lsemStepCast, castStruct?, movImmStruct?, lsemStepMC, mulhiStruct?, adcxStruct?,
      adcxhiStruct?, sbbStruct?, sbbhiStruct?, lsemStepSh, sarStruct?, lsemStepN]
  · cases h

/-- A flag-quiet lift instruction is an `Lopn`. -/
theorem wideArgs?_isLopn {i : LinstrRM} {w : WideOp} (h : wideArgs? i = some w) : IsLopn i := by
  obtain ⟨wire, tag⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · cases h

/-- The two-source `MOV` recognizer commutes with the renaming. -/
theorem wideArgs?_ren_mov {i : LinstrRM} {d : String} {b : LOperand}
    (h : wideArgs? i = some (.mov d b)) :
    wideArgs? (renRM σ i) = some (.mov (σ d) (renOperand σ b)) := by
  obtain ⟨wire, tag⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h with ho
    · cases h
      simp [renRM, renLinstrR, wideArgs?, ho, renOperand]
  · split_ifs at h
    cases h
  · cases h

/-- The destination and the source of a two-source `MOV` are names and operands of the
    instruction. -/
theorem wideArgs?_names_mov {i : LinstrRM} {d : String} {b : LOperand}
    (h : wideArgs? i = some (.mov d b)) :
    d ∈ instrNames i.1 ∧ ∀ n ∈ opNames b, n ∈ instrNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h
    · cases h
      exact ⟨by simp [instrNames, opNames], fun n hn => by
        simp only [instrNames, List.mem_flatMap, List.mem_append]
        exact ⟨_, Or.inr (by simp), hn⟩⟩
  · split_ifs at h
    cases h
  · cases h

/-- A two-source `MOV` step under a renaming. -/
theorem wideStep_mov_ren (hσ : RenOn σ N) {d : String} {b : LOperand} (hd : N d)
    (hb : ∀ n ∈ opNames b, N n) {s s' t : LstateM} (hR : RelM σ N s s')
    (hf : s'.cf = s.cf ∧ s'.of = s.of) (h : wideStep (.mov d b) s = some t) :
    ∃ t', wideStep (.mov (σ d) (renOperand σ b)) s' = some t'
      ∧ RelM σ N t t' ∧ t'.cf = t.cf ∧ t'.of = t.of := by
  simp only [wideStep] at h ⊢
  rw [hR.1.evalOperandN 64 b hb]
  split at h
  · cases h
    exact ⟨_, rfl, RelM.setReg hσ hR hd _, hf.1, hf.2⟩
  · cases h

/-- The instruction is not a widening multiply `MULX`, whose implicit source `RDX` a
    renaming of the operands does not rename. -/
def mulxFree (i : LinstrRM) : Bool :=
  match wideArgs? i with
  | some (.mulx _ _ _) => false
  | _ => true

/-- An `Lopn` with one destination is not a `MULX`. -/
theorem mulxFree_of_lopn1 {i : LinstrRM} (h : ∃ d o s, i.1 = LinstrR.Lopn [d] o s) :
    mulxFree i = true := by
  obtain ⟨d, o, s, h⟩ := h
  unfold mulxFree
  cases hw : wideArgs? i with
  | none => rfl
  | some w =>
      cases w with
      | mov _ _ => rfl
      | mulx lo hi b =>
          exfalso
          obtain ⟨wire, tag⟩ := i
          dsimp only at h
          subst h
          unfold wideArgs? at hw
          dsimp only at hw
          split at hw <;> (try split_ifs at hw) <;> simp_all

/-- The operands the flag compare returns are operands of the instruction. -/
theorem cmpArgs?_names {i : LinstrRM} {p : LOperand × LOperand} (h : cmpArgs? i = some p) :
    (∀ n ∈ opNames p.1, n ∈ instrNames i.1) ∧ (∀ n ∈ opNames p.2, n ∈ instrNames i.1) := by
  obtain ⟨wire, tag⟩ := i
  unfold cmpArgs? at h
  dsimp only at h
  split at h
  · split at h
    · cases h
      simp only [instrNames, List.mem_flatMap, List.mem_append]
      exact ⟨fun n hn => ⟨_, Or.inr (by simp), hn⟩, fun n hn => ⟨_, Or.inr (by simp), hn⟩⟩
    · simp at h
  · simp at h

theorem movRegArgs?_names {i : LinstrRM} {p : String × String} (h : movRegArgs? i = some p) :
    p.1 ∈ instrNames i.1 ∧ p.2 ∈ instrNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold movRegArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h <;> cases h <;> simp [instrNames, opNames]
  · simp at h

/-- The operands a flag-writing arithmetic operation reads are operands of the
    instruction. -/
theorem aluFlagOp?_names {i : LinstrRM} {p : AluOp × LOperand × LOperand}
    (h : aluFlagOp? i = some p) :
    (∀ n ∈ opNames p.2.1, n ∈ instrNames i.1) ∧ (∀ n ∈ opNames p.2.2, n ∈ instrNames i.1) := by
  obtain ⟨wire, tag⟩ := i
  unfold aluFlagOp? at h
  dsimp only at h
  split at h
  · split_ifs at h <;> cases h <;>
      exact ⟨fun n hn => by simp only [instrNames, List.mem_flatMap, List.mem_append]
                            exact ⟨_, Or.inr (by simp), hn⟩,
             fun n hn => by simp only [instrNames, List.mem_flatMap, List.mem_append]
                            exact ⟨_, Or.inr (by simp), hn⟩⟩
  · simp at h

/-- The destination and the operands of a carry-family instruction are names and operands
    of the instruction. -/
theorem carryArgs?_names {i : LinstrRM} {p : CarryOp × String × LOperand × LOperand}
    (h : carryArgs? i = some p) :
    p.2.1 ∈ instrNames i.1 ∧ (∀ n ∈ opNames p.2.2.1, n ∈ instrNames i.1)
      ∧ (∀ n ∈ opNames p.2.2.2, n ∈ instrNames i.1) := by
  obtain ⟨wire, tag⟩ := i
  unfold carryArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h <;> cases h <;>
      exact ⟨by simp [instrNames, opNames],
             fun n hn => by simp only [instrNames, List.mem_flatMap, List.mem_append]
                            exact ⟨_, Or.inr (by simp), hn⟩,
             fun n hn => by simp only [instrNames, List.mem_flatMap, List.mem_append]
                            exact ⟨_, Or.inr (by simp), hn⟩⟩
  · simp at h

/-- The flags `withALUFlags` writes for the renamed instruction from a related state are
    the flags it writes for the original instruction. -/
theorem withALUFlags_ren {i : LinstrRM} (hi : ∀ n ∈ instrNames i.1, N n) {s0 s0' b b' : LstateM}
    (hR : RelN σ N s0.reg s0'.reg) (hb : b'.cf = b.cf ∧ b'.of = b.of) :
    (withALUFlags (renRM σ i) s0' b').cf = (withALUFlags i s0 b).cf
      ∧ (withALUFlags (renRM σ i) s0' b').of = (withALUFlags i s0 b).of := by
  unfold withALUFlags
  rw [aluFlagOp?_ren]
  cases h : aluFlagOp? i with
  | none => exact hb
  | some p =>
      obtain ⟨op, a, c⟩ := p
      obtain ⟨ha, hc⟩ := aluFlagOp?_names h
      simp only [Option.map_some,
        hR.evalOperandN 64 a (fun n hn => hi n (ha n hn)),
        hR.evalOperandN 64 c (fun n hn => hi n (hc n hn))]
      split
      · exact ⟨rfl, rfl⟩
      · exact hb

/-- A conditional jump of the instruction reads the zero flag (every `Lcond` is
    one of the two condition-code forms `flagCondCC?` recognises), and the instruction
    reads no implicit register (it is not a `MULX`, `mulxFree`). -/
def CondOK (i : LinstrRM) : Prop :=
  (∀ c l, i.1 = LinstrR.Lcond c l → flagCondCC? i ≠ none) ∧ mulxFree i = true

/-- The two programs of a renaming simulation from program counter `k0` on: the
    same function name and label positions, the renamed program holds the renamed
    instruction at every index from `k0` on, those instructions mention names of
    `N` only, branch on the zero flag only and read no implicit register, and every
    jump lands at `k0` or later. -/
structure RenProg (σ : String → String) (N : String → Prop) (k0 : Nat)
    (P P' : LprogM) : Prop where
  /-- The function names agree. -/
  lfn : P'.lfn = P.lfn
  /-- The label positions agree. -/
  lbl : ∀ l, findLabelMem l P'.body = findLabelMem l P.body
  /-- From `k0` on the renamed program holds the renamed instructions. -/
  body : ∀ k, k0 ≤ k → P'.body[k]? = (P.body[k]?).map (renRM σ)
  /-- From `k0` on the instructions mention names of `N` only. -/
  names : ∀ k i, k0 ≤ k → P.body[k]? = some i → ∀ n ∈ instrNames i.1, N n
  /-- From `k0` on the conditionals read the zero flag and no instruction is a `MULX`. -/
  cond : ∀ k i, k0 ≤ k → P.body[k]? = some i → CondOK i
  /-- Every jump lands at `k0` or later. -/
  jmp : ∀ l pc, findLabelMem l P.body = some pc → k0 ≤ pc + 1

theorem evalJumpMem_ren {k0 : Nat} {P P' : LprogM} (hP : RenProg σ N k0 P P') (l : LLabel)
    {p p' q : LstatePM} (hR : RelM σ N p.base p'.base) (hfn : p'.lfn = p.lfn)
    (h : evalJumpMem P l p = some q) :
    ∃ q', evalJumpMem P' l p' = some q' ∧ RelM σ N q.base q'.base ∧ q'.lfn = q.lfn
      ∧ k0 ≤ q.base.lpc := by
  unfold evalJumpMem at h ⊢
  rw [hP.lbl l]
  cases hl : findLabelMem l P.body with
  | none => simp [hl] at h
  | some pc =>
      simp only [hl] at h ⊢
      cases h
      exact ⟨_, rfl, hR.setLpc _, hfn, hP.jmp l pc hl⟩

/-- **The labelled step under a renaming**, for an instruction that is not a
    register-reading conditional. -/
theorem evalInstrPMemL_ren {k0 : Nat} {P P' : LprogM} (hσ : RenOn σ N)
    (hP : RenProg σ N k0 P P') (i : LinstrRM) (hi : ∀ n ∈ instrNames i.1, N n)
    (hc : ∀ c l, i.1 ≠ LinstrR.Lcond c l)
    {p p' q : LstatePM} (hR : RelM σ N p.base p'.base) (hfn : p'.lfn = p.lfn)
    (hk : k0 ≤ p.base.lpc) (h : evalInstrPMemL P i p = some q) :
    ∃ q', evalInstrPMemL P' (renRM σ i) p' = some q' ∧ RelM σ N q.base q'.base
      ∧ q'.lfn = q.lfn ∧ k0 ≤ q.base.lpc := by
  obtain ⟨wire, tag⟩ := i
  have hstep : ∀ {q : LstatePM},
      (lsemStepMem (wire, tag) p.base).map (fun b => { p with base := b }) = some q →
      ∃ q', (lsemStepMem (renRM σ (wire, tag)) p'.base).map (fun b => { p' with base := b })
          = some q' ∧ RelM σ N q.base q'.base ∧ q'.lfn = q.lfn ∧ k0 ≤ q.base.lpc := by
    intro q h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨b', hb', hRb⟩ := lsemStepMem_ren hσ (wire, tag) hi hR hb
    refine ⟨{ p' with base := b' }, by rw [hb']; rfl, hRb, hfn, ?_⟩
    have := lsemStepMem_lpc_succ (wire, tag) p.base b hb
    show k0 ≤ b.lpc
    omega
  cases wire with
  | Llabel kd l =>
      simp only [evalInstrPMemL, renRM, renLinstrR] at h ⊢
      cases h
      exact ⟨_, rfl, hR.nextPc, hfn, Nat.le_succ_of_le hk⟩
  | Lcond c l => exact absurd rfl (hc c l)
  | Lgoto tgt =>
      obtain ⟨fn, l⟩ := tgt
      simp only [evalInstrPMemL, renRM, renLinstrR] at h ⊢
      rw [hP.lfn]
      split at h
      · rw [if_pos (by assumption)]
        exact evalJumpMem_ren hP l hR hfn h
      · simp at h
  | Lopn d o s => exact hstep h
  | Lsyscall _ => exact hstep h
  | Lcall _ _ => exact hstep h
  | Lret => exact hstep h
  | Lalign => exact hstep h
  | Ligoto _ => exact hstep h
  | LstoreLabel _ _ => exact hstep h

/-- **The flag step under a renaming.** A successful flag-machine step of the
    original instruction is matched by a step of the renamed instruction from a
    related state, into a related state, and the program counter stays at `k0` or
    later. -/
theorem evalInstrPMemF_ren {k0 : Nat} {P P' : LprogM} (hσ : RenOn σ N)
    (hP : RenProg σ N k0 P P') (i : LinstrRM) (hi : ∀ n ∈ instrNames i.1, N n)
    (hc : CondOK i) {s s' t : LstateMF} (hR : RelF σ N s s')
    (hk : k0 ≤ s.prog.base.lpc) (h : evalInstrPMemF P i s = some t) :
    ∃ t', evalInstrPMemF P' (renRM σ i) s' = some t' ∧ RelF σ N t t'
      ∧ k0 ≤ t.prog.base.lpc := by
  unfold evalInstrPMemF at h ⊢
  rw [cmpArgs?_ren, movRegArgs?_ren, flagCondCC?_ren]
  cases h1 : cmpArgs? i with
  | some p =>
      obtain ⟨a, b⟩ := p
      obtain ⟨ha, hb⟩ := cmpArgs?_names h1
      simp only [h1, Option.map_some,
        hR.1.1.evalOperandN 64 a (fun n hn => hi n (ha n hn)),
        hR.1.1.evalOperandN 64 b (fun n hn => hi n (hb n hn))] at h ⊢
      split at h
      · cases h
        exact ⟨_, rfl, ⟨hR.1.nextPc, hR.2.1, rfl, hR.2.2.2⟩, Nat.le_succ_of_le hk⟩
      · simp at h
  | none =>
  simp only [h1, Option.map_none] at h ⊢
  cases h2 : movRegArgs? i with
  | some p =>
      obtain ⟨d, r⟩ := p
      obtain ⟨hd, hr⟩ := movRegArgs?_names h2
      simp only [h2, Option.map_some, hR.1.1.readReg_reg (hi _ hr)] at h ⊢
      split at h
      · cases h
        exact ⟨_, rfl, ⟨RelM.setReg hσ hR.1 (hi _ hd) _, hR.2.1, hR.2.2⟩,
          Nat.le_succ_of_le hk⟩
      · simp at h
  | none =>
  simp only [h2, Option.map_none] at h ⊢
  cases h3 : flagCondCC? i with
  | some p =>
      obtain ⟨pol, l⟩ := p
      simp only [h3, hR.2.2.1] at h ⊢
      split at h
      · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨q', hq', hRq, hfn, hkq⟩ := evalJumpMem_ren hP l hR.1 hR.2.1 hq
        refine ⟨{ prog := q', zf := s.zf }, by rw [if_pos (by assumption), hq']; rfl,
          ⟨hRq, hfn, rfl, ?_, ?_⟩, hkq⟩
        · rw [(evalJumpMem_flags hq').1, (evalJumpMem_flags hq).1]; exact hR.2.2.2.1
        · rw [(evalJumpMem_flags hq').2, (evalJumpMem_flags hq).2]; exact hR.2.2.2.2
      · cases h
        exact ⟨{ prog := { s'.prog with base := s'.prog.base.nextPc }, zf := s.zf },
          by rw [if_neg (by assumption)], ⟨hR.1.nextPc, hR.2.1, rfl, hR.2.2.2⟩,
          Nat.le_succ_of_le hk⟩
  | none =>
  simp only [h3] at h ⊢
  rw [carryArgs?_ren]
  cases hq : evalInstrPMemL P i s.prog with
  | some q =>
      simp only [hq, Option.some.injEq] at h
      subst h
      obtain ⟨q', hq', hRq, hfn, hkq⟩ := evalInstrPMemL_ren hσ hP i hi
        (fun c l he => hc.1 c l he h3) hR.1 hR.2.1 hk hq
      have hfq := evalInstrPMemL_flags hq
      have hfq' := evalInstrPMemL_flags hq'
      have hw := withALUFlags_ren (i := i) (s0 := s.prog.base) (s0' := s'.prog.base)
        (b := q.base) (b' := q'.base) hi hR.1.1
        ⟨by rw [hfq'.1, hfq.1]; exact hR.2.2.2.1, by rw [hfq'.2, hfq.2]; exact hR.2.2.2.2⟩
      refine ⟨{ prog := { base := withALUFlags (renRM σ i) s'.prog.base q'.base,
                          lfn := q'.lfn }, zf := s'.zf },
        by rw [hq'], ⟨RelM.withALUFlags hRq _ _ _ _, hfn, hR.2.2.1, hw.1, hw.2⟩, ?_⟩
      show k0 ≤ (withALUFlags i s.prog.base q.base).lpc
      rw [withALUFlags_lpc]; exact hkq
  | none =>
      simp only [hq] at h
      cases hk3 : carryArgs? i with
      | none =>
          simp only [hk3] at h
          cases hw : wideArgs? i with
          | none => simp [hw] at h
          | some w =>
              cases w with
              | mulx lo hi b => exact absurd hc.2 (by simp [mulxFree, hw])
              | mov d b =>
                  obtain ⟨hd, hb⟩ := wideArgs?_names_mov hw
                  simp only [hw] at h
                  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
                  obtain ⟨u', hu', hRu, hcf, hof⟩ := wideStep_mov_ren hσ (hi _ hd)
                    (fun n hn => hi n (hb n hn)) hR.1 hR.2.2.2 hu
                  have hw' := wideArgs?_ren_mov (σ := σ) hw
                  have hq'none : evalInstrPMemL P' (renRM σ i) s'.prog = none := by
                    rw [evalInstrPMemL_lopn _ _ _ (wideArgs?_isLopn hw'),
                      lsemStepMem_of_wideArgs hw', Option.map_none]
                  refine ⟨{ prog := { base := u', lfn := s'.prog.lfn }, zf := s'.zf },
                    by rw [hq'none]; simp only [Option.map_none, hw', Option.map_some, hu'],
                    ⟨hRu, hR.2.1, hR.2.2.1, hcf, hof⟩, ?_⟩
                  have := wideStep_lpc _ _ _ hu
                  show k0 ≤ u.lpc
                  omega
      | some p =>
          obtain ⟨op, d, a, c⟩ := p
          obtain ⟨hd, ha, hcn⟩ := carryArgs?_names hk3
          simp only [hk3] at h
          obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨u', hu', hRu, hcf, hof⟩ := carryStep_ren hσ (hi _ hd)
            (fun n hn => hi n (ha n hn)) (fun n hn => hi n (hcn n hn)) hR.1
            hR.2.2.2 hu
          have hk3' : carryArgs? (renRM σ i) = some (op, σ d, renOperand σ a, renOperand σ c) := by
            rw [carryArgs?_ren, hk3]; rfl
          have hq'none : evalInstrPMemL P' (renRM σ i) s'.prog = none := by
            have hlopn : IsLopn (renRM σ i) := by
              unfold carryArgs? at hk3'
              split at hk3'
              · rename_i heq; exact ⟨_, _, _, heq⟩
              · cases hk3'
            rw [evalInstrPMemL_lopn _ _ _ hlopn, lsemStepMem_of_carryArgs hk3', Option.map_none]
          simp only [] at hu'
          refine ⟨{ prog := { base := u', lfn := s'.prog.lfn }, zf := s'.zf },
            by rw [hq'none]; simp only [Option.map_some, hu'],
            ⟨hRu, hR.2.1, hR.2.2.1, hcf, hof⟩, ?_⟩
          have := carryStep_lpc _ _ _ _ _ _ hu
          show k0 ≤ u.lpc
          omega

/-- **The flag machine under a renaming.** For two programs related by a
    renaming from `k0` on (`RenProg`), every halting run of the original from a
    state at program counter `k0` or later is matched, with the same fuel, by a
    halting run of the renamed program from a related state, into a related
    state. -/
theorem lsemFuelMemF_ren {k0 : Nat} {P P' : LprogM} (hσ : RenOn σ N)
    (hP : RenProg σ N k0 P P') :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelF σ N s s' → k0 ≤ s.prog.base.lpc →
      lsemFuelMemF P fuel s = some t →
      ∃ t', lsemFuelMemF P' fuel s' = some t' ∧ RelF σ N t t' := by
  have hfetch : ∀ {s s' : LstateMF}, RelF σ N s s' → k0 ≤ s.prog.base.lpc →
      findInstrMem P' s'.prog = (findInstrMem P s.prog).map (renRM σ) := by
    intro s s' hR hk
    unfold findInstrMem
    rw [hR.2.1, hP.lfn]
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
    split
    · rw [hpc]; exact hP.body _ hk
    · rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hR hk h
      unfold lsemFuelMemF at h ⊢
      rw [hfetch hR hk]
      cases hf : findInstrMem P s.prog with
      | none => simp only [hf] at h ⊢; cases h; exact ⟨_, rfl, hR⟩
      | some i => simp [hf] at h
  | succ n ih =>
      intro s s' t hR hk h
      unfold lsemFuelMemF at h ⊢
      rw [hfetch hR hk]
      cases hf : findInstrMem P s.prog with
      | none => simp only [hf] at h ⊢; cases h; exact ⟨_, rfl, hR⟩
      | some i =>
          simp only [hf, Option.map_some] at h ⊢
          have hget : P.body[s.prog.base.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact hf
            · simp at hf
          cases he : evalInstrPMemF P i s with
          | none => simp [he] at h
          | some u =>
              simp only [he] at h
              obtain ⟨u', hu', hRu, hku⟩ := evalInstrPMemF_ren hσ hP i
                (hP.names _ i hk hget) (hP.cond _ i hk hget) hR hk he
              simp only [hu']
              exact ih hRu hku h

/-- Related flag-machine states decode the same array at a name of `N` and its
    renaming. -/
theorem RelF.decodeArrM_eq {t t' : LstateMF} (h : RelF σ N t t') {r : String} (hr : N r)
    (w n : Nat) :
    JasminLsemMemSourceTieUncond.decodeArrM t'.prog.base (σ r) w n
      = JasminLsemMemSourceTieUncond.decodeArrM t.prog.base r w n := by
  unfold JasminLsemMemSourceTieUncond.decodeArrM LstateM.getArr
  rw [h.1.2.1 r hr]

/-- Related flag-machine states read the same register at a name of `N` and its
    renaming. -/
theorem RelF.getW_eq {t t' : LstateMF} (h : RelF σ N t t') {r : String} (hr : N r)
    (w : Nat) : t'.prog.base.reg.getW (σ r) w = t.prog.base.reg.getW r w :=
  h.1.1.getW hr w

/-! ## 10. A program and its renaming -/

theorem isLabel_renLinstrR (l : LLabel) (i : LinstrR) :
    JasminLsemLabeled.isLabel l (renLinstrR σ i) = JasminLsemLabeled.isLabel l i := by
  cases i <;> rfl

/-- Renaming leaves every label position unchanged. -/
theorem findLabelMem_map_renRM (l : LLabel) (body : List LinstrRM) :
    findLabelMem l (body.map (renRM σ)) = findLabelMem l body := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_map, List.findIdx?_map, List.findIdx?_map]
  congr 1
  funext i
  exact isLabel_renLinstrR l i.1

/-- **A program and its renaming are related from `k0 ≤ 1` on**, when from `k0` on
    the instructions mention names of `N` only and branch on the zero flag only. -/
theorem renProg_map (fn : String) (body : List LinstrRM) {k0 : Nat} (hk0 : k0 ≤ 1)
    (hn : ∀ k i, k0 ≤ k → body[k]? = some i → ∀ n ∈ instrNames i.1, N n)
    (hc : ∀ k i, k0 ≤ k → body[k]? = some i → CondOK i) :
    RenProg σ N k0 (singletonProgM fn body) (singletonProgM fn (body.map (renRM σ))) where
  lfn := rfl
  lbl := fun l => findLabelMem_map_renRM l body
  body := fun k _ => by simp [singletonProgM]
  names := hn
  cond := hc
  jmp := fun _ _ _ => by omega

section Calls

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes lpc_retRes argRead
  argsRead)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-- Related states read the same argument words from operands with names in `N` and from
    their renamings, at every array position: a word position reads the register file, an
    array position the array carrier, and the relation holds on both. -/
theorem RelM.argsRead_ren {s s' : LstateM} (h : RelM σ N s s') (aa : Nat → Option Nat) :
    ∀ (k : Nat) (srcs : List LOperand), (∀ o ∈ srcs, ∀ n ∈ opNames o, N n) →
      argsRead aa s' k (srcs.map (renOperand σ)) = argsRead aa s k srcs
  | _, [], _ => rfl
  | k, o :: os, ho => by
      have h1 : argRead aa s' k (renOperand σ o) = argRead aa s k o := by
        unfold argRead
        split
        · rw [h.1.evalOperandN 64 o (ho o List.mem_cons_self)]
        · cases o with
          | reg A =>
              have hA : N A := ho _ List.mem_cons_self A (by simp [opNames])
              simp only [renOperand, h.getArr hA]
          | imm _ => rfl
          | arr _ _ => rfl
          | arrIdx _ _ _ => rfl
      rw [List.map_cons, argsRead, argsRead, h1,
        RelM.argsRead_ren h aa (k + 1) os fun o' ho' => ho o' (List.mem_cons_of_mem _ ho')]

/-- **A step under a renaming at an instruction set with local calls.** For an instruction set
    `I` whose steps contain those of `x86Isa` and whose further steps are local calls, a
    successful step of the original instruction is matched by a step of the renamed
    instruction from a related state, into a related state, and the program counter stays at
    `k0` or later. A local call reads the same argument words from the renamed operands
    (`RelM.argsRead_ren`), at word and at array positions, and writes its result, a word or a
    word array, to the renamed destination. -/
theorem step_ren_calls {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) {k0 : Nat} {P P' : LprogM}
    (hσ : RenOn σ N)
    (hP : RenProg σ N k0 P P') (i : LinstrRM) (hi : ∀ n ∈ instrNames i.1, N n)
    (hc : CondOK i) {s s' t : LstateMF} (hR : RelF σ N s s')
    (hk : k0 ≤ s.prog.base.lpc) (h : I.step P i s = some t) :
    ∃ t', I.step P' (renRM σ i) s' = some t' ∧ RelF σ N t t'
      ∧ k0 ≤ t.prog.base.lpc := by
  rcases hcl P i s t h with hx | ⟨dst, f, srcs, x, hsh, rfl, hfwd, -⟩
  · obtain ⟨t', ht', hrest⟩ := evalInstrPMemF_ren hσ hP i hi hc hR hk hx
    exact ⟨t', hle _ _ _ _ ht', hrest⟩
  · obtain ⟨w, tag⟩ := i
    simp only at hsh
    subst hsh
    have hd : N dst := hi dst (by simp [callShadow, instrNames, opNames])
    have hs : ∀ o ∈ srcs, ∀ n ∈ opNames o, N n := fun o ho n hn =>
      hi n (by
        simp only [callShadow, instrNames, List.flatMap_append, List.mem_append,
          List.mem_flatMap]
        exact Or.inr ⟨o, ho, hn⟩)
    refine ⟨retRes (σ dst) x s', ?_, ?_, ?_⟩
    · exact hfwd P' tag (σ dst) (srcs.map (renOperand σ)) s' (List.length_map _)
        (hR.1.argsRead_ren (aa f) 0 srcs hs)
    · cases x with
      | word r => exact ⟨RelM.setReg hσ hR.1 hd r, hR.2.1, hR.2.2⟩
      | arr a => exact ⟨RelM.setArr hσ hR.1 hd a, hR.2.1, hR.2.2⟩
    · rw [lpc_retRes]
      exact Nat.le_succ_of_le hk

/-- **An instruction set with local calls under a renaming.** For two programs related by a
    renaming from `k0` on (`RenProg`) and an instruction set `I` whose steps contain those of
    `x86Isa` and whose further steps are local calls, every halting run of `I` on the original
    from a state at program counter `k0` or later is matched, with the same fuel, by a halting
    run of `I` on the renamed program from a related state, into a related state. -/
theorem lsemFuelMemF_ren_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    {k0 : Nat} {P P' : LprogM}
    (hσ : RenOn σ N) (hP : RenProg σ N k0 P P') :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelF σ N s s' → k0 ≤ s.prog.base.lpc →
      I.lsemFuelMemF P fuel s = some t →
      ∃ t', I.lsemFuelMemF P' fuel s' = some t' ∧ RelF σ N t t' := by
  have hfetch : ∀ {s s' : LstateMF}, RelF σ N s s' → k0 ≤ s.prog.base.lpc →
      findInstrMem P' s'.prog = (findInstrMem P s.prog).map (renRM σ) := by
    intro s s' hR hk
    unfold findInstrMem
    rw [hR.2.1, hP.lfn]
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
    split
    · rw [hpc]; exact hP.body _ hk
    · rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hR hk h
      unfold Isa.lsemFuelMemF at h ⊢
      rw [hfetch hR hk]
      cases hf : findInstrMem P s.prog with
      | none => simp only [hf] at h ⊢; cases h; exact ⟨_, rfl, hR⟩
      | some i => simp [hf] at h
  | succ n ih =>
      intro s s' t hR hk h
      unfold Isa.lsemFuelMemF at h ⊢
      rw [hfetch hR hk]
      cases hf : findInstrMem P s.prog with
      | none => simp only [hf] at h ⊢; cases h; exact ⟨_, rfl, hR⟩
      | some i =>
          simp only [hf, Option.map_some] at h ⊢
          have hget : P.body[s.prog.base.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact hf
            · simp at hf
          cases he : I.step P i s with
          | none => simp [he] at h
          | some u =>
              simp only [he] at h
              obtain ⟨u', hu', hRu, hku⟩ := step_ren_calls hle hcl hσ hP i
                (hP.names _ i hk hget) (hP.cond _ i hk hget) hR hk he
              simp only [hu']
              exact ih hRu hku h

/-- **Renaming a whole program at an instruction set with local calls.** For `σ` usable on
    `N`, a program whose instructions mention names of `N` only and branch on the zero flag
    only, its image under `σ`, and an instruction set `I` whose steps contain those of
    `x86Isa` and whose further steps are local calls at any array positions: every halting run
    of `I` on the original is matched, with the same fuel, by a halting run of `I` on the image
    from a related state, into a related state. -/
theorem lsemFuelMemF_map_renRM_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hσ : RenOn σ N) (fn : String)
    (body : List LinstrRM) (hn : ∀ i ∈ body, ∀ n ∈ instrNames i.1, N n)
    (hc : ∀ i ∈ body, CondOK i) (fuel : Nat) {s s' t : LstateMF} (hR : RelF σ N s s')
    (h : I.lsemFuelMemF (singletonProgM fn body) fuel s = some t) :
    ∃ t', I.lsemFuelMemF (singletonProgM fn (body.map (renRM σ))) fuel s' = some t'
      ∧ RelF σ N t t' :=
  lsemFuelMemF_ren_calls hle hcl hσ
    (renProg_map fn body (Nat.zero_le 1)
      (fun _ i _ hi => hn i (List.mem_of_getElem? hi))
      (fun _ i _ hi => hc i (List.mem_of_getElem? hi)))
    fuel hR (Nat.zero_le _) h

end Calls

/-- **Renaming a whole program.** For `σ` usable on `N`, a program whose
    instructions mention names of `N` only and branch on the zero flag only, and
    its image under `σ`: every halting flag-machine run of the original is
    matched, with the same fuel, by a halting run of the image from a related
    state, into a related state. -/
theorem lsemFuelMemF_map_renRM (hσ : RenOn σ N) (fn : String) (body : List LinstrRM)
    (hn : ∀ i ∈ body, ∀ n ∈ instrNames i.1, N n) (hc : ∀ i ∈ body, CondOK i)
    (fuel : Nat) {s s' t : LstateMF} (hR : RelF σ N s s')
    (h : lsemFuelMemF (singletonProgM fn body) fuel s = some t) :
    ∃ t', lsemFuelMemF (singletonProgM fn (body.map (renRM σ))) fuel s' = some t'
      ∧ RelF σ N t t' := by
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF] at h ⊢
  exact lsemFuelMemF_map_renRM_calls (LprogIsa.Isa.StepLe.refl _)
    (LprogIsa.Isa.CallLocal.refl _ (fun _ _ => none)) hσ fn body hn hc fuel hR h

/-! ## 11. The two body rewrites as renamings -/

/-- Rename the wire of an exported instruction, keeping its position tag. -/
def renLinstr (σ : String → String) (i : Linstr) : Linstr := ⟨i.li_ii, renLinstrR σ i.li_i⟩

/-- Rename every instruction of an exported `Lcmd`. -/
def renLcmd (σ : String → String) (c : Lcmd) : Lcmd := c.map (renLinstr σ)

theorem aliasRegOperand_eq_renOperand (from_ to_ : String) :
    aliasRegOperand from_ to_ = renOperand (aliasRegName from_ to_) := by
  funext o; cases o <;> rfl

theorem canonMemrefOperand_eq_renOperand (m : Std.HashMap String String) :
    canonMemrefOperand m = renOperand (canonMemrefName m) := by
  funext o; cases o <;> rfl

/-- **`aliasRegBody` is the renaming `aliasRegName from_ to_`.** -/
theorem aliasRegBody_eq_renLcmd (from_ to_ : String) (c : Lcmd) :
    aliasRegBody from_ to_ c = renLcmd (aliasRegName from_ to_) c := by
  unfold aliasRegBody renLcmd
  refine List.map_congr_left (fun i _ => ?_)
  obtain ⟨ii, w⟩ := i
  cases w <;> simp [renLinstr, renLinstrR, aliasRegOperand_eq_renOperand]

/-- **`canonicalizeMemrefThread` is the identity or the renaming
    `canonMemrefName (arrChainAlias c)`**, by emptiness of the alias map. -/
theorem canonicalizeMemrefThread_eq_renLcmd (c : Lcmd) :
    canonicalizeMemrefThread c
      = if (arrChainAlias c).isEmpty then c
        else renLcmd (canonMemrefName (arrChainAlias c)) c := by
  unfold canonicalizeMemrefThread renLcmd
  dsimp only
  split
  · rfl
  · refine List.map_congr_left (fun i _ => ?_)
    obtain ⟨ii, w⟩ := i
    cases w <;> simp [renLinstr, renLinstrR, canonMemrefOperand_eq_renOperand]

/-- The lift of a renamed `Lcmd` is the renaming of the lift, for a descriptor
    oracle that gives a renamed instruction the descriptor of the original. -/
theorem liftLcmdRM_renLcmd (tag tag' : Linstr → MemTag) (c : Lcmd)
    (htag : ∀ i ∈ c, tag' (renLinstr σ i) = tag i) :
    liftLcmdRM tag' (renLcmd σ c) = (liftLcmdRM tag c).map (renRM σ) := by
  unfold liftLcmdRM renLcmd
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun i hi => ?_)
  simp only [Function.comp, liftLinstrRM, renRM, renLinstr]
  rw [← htag i hi]
  rfl

/-! ## 12. `aliasRegBody` on the runtime-count loop node -/

/-- The accumulator alias `from_ ↦ to_` is usable on the names other than `to_`. -/
theorem renOn_aliasRegName {from_ to_ : String} (hf : from_ ≠ "") (ht : to_ ≠ "") :
    RenOn (aliasRegName from_ to_) (fun r => r ≠ to_) where
  inj := by
    intro a b ha hb h
    unfold aliasRegName at h
    by_cases h1 : a = from_ <;> by_cases h2 : b = from_ <;> simp_all
  emp := fun h => ht h.symm
  fix := by
    unfold aliasRegName
    rw [if_neg (by simpa using fun h : "" = from_ => hf h.symm)]

/-- An `Lopn` that is not a `MULX` satisfies `CondOK`. -/
theorem condOK_of_isLopn {i : LinstrRM} (h : IsLopn i) (hm : mulxFree i = true) : CondOK i := by
  obtain ⟨d, o, s, hd⟩ := h
  refine ⟨fun c l he => ?_, hm⟩
  rw [hd] at he
  cases he

/-- An `Lopn` with one destination satisfies `CondOK`. -/
theorem condOK_of_lopn1 {i : LinstrRM} (h : ∃ d o s, i.1 = LinstrR.Lopn [d] o s) : CondOK i :=
  condOK_of_isLopn (by obtain ⟨d, o, s, h⟩ := h; exact ⟨_, _, _, h⟩) (mulxFree_of_lopn1 h)

/-- A lowered binding writes its one destination register. -/
theorem opToLinstrR_lopn1 (op : JasminOp) (dst : String) (srcs : List LOperand) :
    ∃ o s, opToLinstrR op dst srcs = LinstrR.Lopn [.reg dst] o s := by
  unfold opToLinstrR
  split <;> (repeat' (first | exact ⟨_, _, rfl⟩ | split | dsimp only))

/-- Every instruction of the typed walk has one destination. -/
theorem loopBodyWalkNM_lopn1 (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    ∀ i ∈ loopBodyWalkNM d accReg idxReg invRegs immSlotMap com curDepth,
      ∃ d o s, i.1 = LinstrR.Lopn [d] o s := by
  induction com generalizing curDepth with
  | ret v => intro i hi; simp [loopBodyWalkNM] at hi
  | var e body ih =>
      intro i hi
      simp only [loopBodyWalkNM, List.mem_cons] at hi
      rcases hi with rfl | hi
      · obtain ⟨o, s, h⟩ := opToLinstrR_lopn1 e.op (loopReg d curDepth)
          (loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e)
        exact ⟨_, o, s, h⟩
      · exact ih (curDepth + 1) i hi

/-- Every instruction of the looped segment has one destination. -/
theorem forLoopBodyNRtRM_lopn1 (d : Nat) (accReg : String) {accTy : JasminTy}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    ∀ i ∈ forLoopBodyNRtRM d accReg update invOps immSlotMap,
      ∃ d o s, i.1 = LinstrR.Lopn [d] o s := by
  intro i hi
  simp only [forLoopBodyNRtRM, List.mem_append] at hi
  rcases hi with ((hi | hi) | hi) | hi
  · exact loopBodyWalkNM_lopn1 _ _ _ _ _ _ _ i hi
  · unfold loopFeedbackRM at hi
    split at hi
    · simp at hi
    · simp only [List.mem_singleton] at hi; subst hi; exact ⟨_, _, _, rfl⟩
  · simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · simp only [loopTouchRM, List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact ⟨_, _, _, rfl⟩

/-- Every conditional of the typed loop node reads the zero flag. -/
theorem forLoopLcmdNRtRM_condOK (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    ∀ i ∈ forLoopLcmdNRtRM d accReg initOp countOp update invOps immSlotMap, CondOK i := by
  intro i hi
  simp only [forLoopLcmdNRtRM, guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge,
    loopSeedsRM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl) | (rfl | rfl | (rfl | hi | rfl | rfl)) | rfl
  · exact condOK_of_lopn1 ⟨_, _, _, rfl⟩
  · exact condOK_of_lopn1 ⟨_, _, _, rfl⟩
  · exact condOK_of_lopn1 ⟨_, _, _, rfl⟩
  · exact condOK_of_lopn1 ⟨_, _, _, rfl⟩
  · exact ⟨fun c l _ => by simp [flagCondCC?], rfl⟩
  · exact ⟨fun c l he => (by cases he), rfl⟩
  · exact condOK_of_lopn1 (forLoopBodyNRtRM_lopn1 d accReg update invOps immSlotMap i hi)
  · exact condOK_of_lopn1 ⟨_, _, _, rfl⟩
  · exact ⟨fun c l _ => by simp [flagCondCC?], rfl⟩
  · exact ⟨fun c l he => (by cases he), rfl⟩

/-- The flag step of a register-copy `MOV dst, src`: write the cell of `src` to
    `dst` and advance. -/
theorem evalInstrPMemF_movReg (P : LprogM) (dst src : String) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (LinstrR.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src], tag) s
      = some { s with prog := { s.prog with base :=
          (s.prog.base.setReg dst (s.prog.base.reg.lvm src).2).nextPc } } := by
  unfold evalInstrPMemF
  simp only [cmpArgs?, movRegArgs?]
  rw [if_pos (show stripWidthTag (withWidthTag 64 "MOV") = "MOV" by decide)]
  rfl

/-- **`aliasRegBody` preserves the runs of the runtime-count loop node.** Let the
    node seed its accumulator `acc` from the register `out`, and let no
    instruction after that seed mention `out`. Take two entry states at program
    counter `0` that agree on every register other than `acc`, in which the
    aliased state holds at `out` the array the original holds at `acc`, and that
    agree on every other array. Then every halting flag-machine run of the node
    is matched, with the same fuel, by a halting run of the node renamed by
    `aliasRegName acc out`, and the final states are related by that renaming on
    every name other than `out`: the aliased run holds at `out` the register and
    the array the original holds at `acc`, and agrees with it elsewhere. -/
theorem forLoopLcmdNRtRM_alias (fn : String) (d : Nat) (acc out : String) (countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hacc : acc ≠ "") (hout : out ≠ "")
    (hfresh : ∀ k i, 1 ≤ k →
      (forLoopLcmdNRtRM d acc (.reg out) countOp update invOps immSlotMap)[k]? = some i →
      ∀ n ∈ instrNames i.1, n ≠ out)
    (fuel : Nat) {s s' t : LstateMF}
    (hfn : s.prog.lfn = fn) (hfn' : s'.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 0) (hpc' : s'.prog.base.lpc = 0) (hzf : s'.zf = s.zf)
    (hreg : ∀ r, r ≠ out → r ≠ acc → s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
    (hro : s'.prog.base.reg.lvm out = s.prog.base.reg.lvm out)
    (harr : ∀ r, r ≠ out →
      s'.prog.base.larr (aliasRegName acc out r) = s.prog.base.larr r)
    (hmem : s'.prog.base.lmem = s.prog.base.lmem)
    (hflags : s'.prog.base.cf = s.prog.base.cf ∧ s'.prog.base.of = s.prog.base.of)
    (hrun : lsemFuelMemF (singletonProgM fn
      (forLoopLcmdNRtRM d acc (.reg out) countOp update invOps immSlotMap)) fuel s = some t) :
    ∃ t', lsemFuelMemF (singletonProgM fn
        ((forLoopLcmdNRtRM d acc (.reg out) countOp update invOps immSlotMap).map
          (renRM (aliasRegName acc out)))) fuel s' = some t'
      ∧ RelF (aliasRegName acc out) (fun r => r ≠ out) t t' := by
  have hσ := renOn_aliasRegName hacc hout
  have hP := renProg_map (σ := aliasRegName acc out) (N := fun r => r ≠ out) fn
    (forLoopLcmdNRtRM d acc (.reg out) countOp update invOps immSlotMap) (Nat.le_refl 1)
    hfresh (fun _ i _ hi => forLoopLcmdNRtRM_condOK d acc (.reg out) countOp update invOps
      immSlotMap i (List.mem_of_getElem? hi))
  have hseed : ∀ {u : LstateMF}, u.prog.lfn = fn → u.prog.base.lpc = 0 →
      findInstrMem (singletonProgM fn
        (forLoopLcmdNRtRM d acc (.reg out) countOp update invOps immSlotMap)) u.prog
        = some (LinstrR.Lopn [.reg acc] (withWidthTag 64 "MOV") [.reg out], MemTag.reg none) := by
    intro u hu hu0
    unfold findInstrMem
    rw [if_pos (by simpa [singletonProgM] using hu), hu0]
    rfl
  have hseed' : findInstrMem (singletonProgM fn
        ((forLoopLcmdNRtRM d acc (.reg out) countOp update invOps immSlotMap).map
          (renRM (aliasRegName acc out)))) s'.prog
        = some (LinstrR.Lopn [.reg out] (withWidthTag 64 "MOV") [.reg out], MemTag.reg none) := by
    unfold findInstrMem
    rw [if_pos (by simpa [singletonProgM] using hfn'), hpc']
    simp [singletonProgM, forLoopLcmdNRtRM, loopSeedsRM, renRM, renLinstrR, renOperand,
      aliasRegName]
  cases fuel with
  | zero =>
      unfold lsemFuelMemF at hrun
      rw [hseed hfn hpc] at hrun
      simp at hrun
  | succ n =>
      rw [lsemFuelMemF_step _ n _ s _ (hseed hfn hpc) (evalInstrPMemF_movReg _ acc out _ s)]
        at hrun
      rw [lsemFuelMemF_step _ n _ s' _ hseed' (evalInstrPMemF_movReg _ out out _ s')]
      refine lsemFuelMemF_ren hσ hP n ?_ ?_ hrun
      rotate_left
      · show 1 ≤ s.prog.base.reg.lpc + 1
        omega
      refine ⟨⟨⟨?_, ?_⟩, harr, hmem⟩, ?_, hzf, hflags⟩
      · show s'.prog.base.reg.lpc + 1 = s.prog.base.reg.lpc + 1
        have h1 : s'.prog.base.reg.lpc = 0 := hpc'
        have h2 : s.prog.base.reg.lpc = 0 := hpc
        rw [h1, h2]
      · intro r hr
        show (if aliasRegName acc out r = out then _ else _) = (if r = acc then _ else _)
        by_cases hra : r = acc
        · subst hra
          simp [aliasRegName, hro]
        · have : aliasRegName acc out r = r := by simp [aliasRegName, hra]
          rw [this, if_neg hr, if_neg hra]
          exact hreg r hr hra
      · show s'.prog.lfn = s.prog.lfn
        rw [hfn, hfn']

/-- The wire projection of a renamed `Lcmd`. -/
theorem renLcmd_wire (σ : String → String) (c : Lcmd) :
    (renLcmd σ c).map Linstr.li_i = (c.map Linstr.li_i).map (renLinstrR σ) := by
  simp [renLcmd, renLinstr, List.map_map, Function.comp_def]

/-- **Wire tie of the aliased node.** The wire projection of the typed loop node
    renamed by `aliasRegName acc out` is the instruction stream of
    `aliasRegBody acc out` applied to the export's `forLoopLcmdNRt`. -/
theorem forLoopLcmdNRtRM_alias_wire (d : Nat) (acc out : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    ((forLoopLcmdNRtRM d acc initOp countOp update invOps immSlotMap).map
        (renRM (aliasRegName acc out))).map Prod.fst
      = (aliasRegBody acc out
          (forLoopLcmdNRt d acc initOp countOp update invOps immSlotMap)).map Linstr.li_i := by
  rw [aliasRegBody_eq_renLcmd, renLcmd_wire, ← forLoopLcmdNRtRM_wire]
  simp [List.map_map, Function.comp_def, renRM]

/-! ## 13. `canonicalizeMemrefThread`: a store thread read again through its base -/

/-- A store through base `b` into the thread name `d`, then a load through `b`. -/
def threadCmd : Lcmd :=
  [ ⟨0, .Lopn [.reg "d"] "STOREIDX" [.arrIdx "b" "i" 8, .reg "v"]⟩
  , ⟨0, .Lopn [.reg "x"] "LOADIDX" [.arrIdx "b" "i" 8]⟩ ]

/-- The descriptors of `threadCmd`: a one-cell 64-bit array. -/
def threadTag (i : Linstr) : MemTag :=
  match i.li_i with
  | .Lopn _ "STOREIDX" _ => .store 64 1
  | _ => .load 64 1

/-- An entry state: index `0`, stored value `1`, and a zero cell in `b`. -/
def threadState : LstateMF :=
  { prog :=
      { base :=
          { reg := { lvm := fun r => if r = "v" then ⟨64, 1#64⟩ else ⟨64, 0#64⟩ }
            larr := fun _ => ⟨64, 1, fun _ => 0#64⟩ }
        lfn := "f" } }

theorem threadCmd_run :
    ∃ t, lsemFuelMemF (singletonProgM "f" (liftLcmdRM threadTag threadCmd)) 2 threadState
        = some t ∧ t.prog.base.reg.getW "x" 64 = some 0#64 :=
  ⟨_, rfl, rfl⟩

/-- The thread renaming of `threadCmd`: the store's result name `d` to its base
    `b`. -/
def threadRen (n : String) : String := if n = "d" then "b" else n

theorem threadCmd_ren_run :
    ∃ t, lsemFuelMemF (singletonProgM "f"
          ((liftLcmdRM threadTag threadCmd).map (renRM threadRen))) 2 threadState
        = some t ∧ t.prog.base.reg.getW "x" 64 = some 1#64 :=
  ⟨_, rfl, rfl⟩

theorem arrChainAlias_threadCmd :
    arrChainAlias threadCmd = (∅ : Std.HashMap String String).insert "d" "b" := by
  have h1 : stripWidthTag "STOREIDX" = "STOREIDX" := by decide
  have h2 : stripWidthTag "LOADIDX" = "LOADIDX" := by decide
  simp [arrChainAlias, threadCmd, isMemStore, h1, h2]

/-- On `threadCmd` the pass `canonicalizeMemrefThread` is the renaming
    `threadRen`. -/
theorem canonicalizeMemrefThread_threadCmd :
    canonicalizeMemrefThread threadCmd = renLcmd threadRen threadCmd := by
  rw [canonicalizeMemrefThread_eq_renLcmd, arrChainAlias_threadCmd, if_neg (by simp)]
  have hσ : canonMemrefName ((∅ : Std.HashMap String String).insert "d" "b") = threadRen := by
    funext n
    simp only [canonMemrefName, threadRen, Std.HashMap.getD_insert]
    by_cases h : n = "d"
    · subst h; simp
    · have h' : ("d" == n) = false := by simpa using fun e : "d" = n => h e.symm
      simp [h', h]
  rw [hσ]

/-- **`canonicalizeMemrefThread` changes a value the name-keyed machine computes.**
    From the same entry state, the lift of `threadCmd` halts with `x = 0` and the
    lift of `canonicalizeMemrefThread threadCmd` halts with `x = 1`: the original
    load reads the base array `b`, which the store left unchanged, and the
    canonicalised load reads the array the store wrote. The two runs are closed
    two-instruction evaluations. -/
theorem canonicalizeMemrefThread_threadCmd_run :
    (∃ t, lsemFuelMemF (singletonProgM "f" (liftLcmdRM threadTag threadCmd)) 2 threadState
        = some t ∧ t.prog.base.reg.getW "x" 64 = some 0#64)
    ∧ (∃ t, lsemFuelMemF (singletonProgM "f"
          (liftLcmdRM threadTag (canonicalizeMemrefThread threadCmd))) 2 threadState
        = some t ∧ t.prog.base.reg.getW "x" 64 = some 1#64) := by
  refine ⟨threadCmd_run, ?_⟩
  rw [canonicalizeMemrefThread_threadCmd,
    liftLcmdRM_renLcmd threadTag threadTag threadCmd (by
      intro i hi
      simp only [threadCmd, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> rfl)]
  exact threadCmd_ren_run

/-! ## 14. Names of the runtime-count loop node -/

/-- A name that starts with `L`: the export's loop-node names `L<d>_r<k>`,
    `Lidx<d>`, `Lctr<d>` and `Linv<d>_<j>`. -/
def HeadL (n : String) : Prop := n.toList.head? = some 'L'

theorem headL_loopIdx (d : Nat) : HeadL (loopIdx d) := head?_append_of _ _ _ rfl

/-- The names an op of the fragment's op set emits are its destination and the
    names of its source operands. -/
theorem opToLinstrR_names (op : JasminOp) (hop : OpPlain op) (dst : String)
    (srcs : List LOperand) :
    ∀ n ∈ instrNames (opToLinstrR op dst srcs), n = dst ∨ n ∈ srcs.flatMap opNames := by
  cases op <;> simp only [OpPlain] at hop
  all_goals first
    | (simp only [opToLinstrR]
       try split
       all_goals
         intro n hn
         simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
           List.flatMap_nil, List.mem_cons, List.not_mem_nil, or_false,
           List.append_nil] at hn ⊢
         tauto)
    | (intro n hn
       simp only [opToLinstrR, instrNames, opNames, List.cons_append, List.nil_append,
         List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.mem_cons,
         List.append_nil] at hn ⊢
       tauto)

/-- A name the body walk of a loop node can mention: the accumulator register, an
    invariant base register, or a loop-node name starting with `L`. -/
def NodeName (acc : String) (invRegs : List String) (n : String) : Prop :=
  n = acc ∨ n ∈ invRegs ∨ HeadL n

theorem loopResolveVarN_names (d : Nat) (acc : String) (invRegs : List String)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    ∀ n ∈ opNames (loopResolveVarN d acc (loopIdx d) invRegs curDepth immSlotMap v),
      NodeName acc invRegs n := by
  intro n hn
  unfold loopResolveVarN at hn
  dsimp only at hn
  split at hn
  · split at hn
    · simp [opNames] at hn
    · simp only [opNames, List.mem_singleton] at hn
      exact Or.inl hn
  · split at hn
    · simp only [opNames, List.mem_singleton] at hn
      exact Or.inr (Or.inr (hn ▸ headL_loopIdx d))
    · split at hn
      · simp only [opNames, List.mem_singleton] at hn
        subst hn
        rw [List.getD_eq_getElem?_getD]
        cases hg : invRegs[invRegs.length - 1 - (curDepth - 1 - varIndex v)]? with
        | none =>
            exact Or.inr (Or.inr (head?_append_of _ _ _ (head?_append_of _ _ _
              (head?_append_of _ _ _ rfl))))
        | some x => exact Or.inr (Or.inl (List.mem_of_getElem? hg))
      · simp only [opNames, List.mem_singleton] at hn
        exact Or.inr (Or.inr (hn ▸ head?_loopReg d _))

theorem loopExprArgsN_go_names (d : Nat) (acc : String) (invRegs : List String)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ n ∈ (loopExprArgsN.go d acc (loopIdx d) invRegs curDepth immSlotMap hv).flatMap opNames,
        NodeName acc invRegs n
  | [], .nil => by intro n hn; simp [loopExprArgsN.go] at hn
  | _ :: _, .cons v rest => by
      intro n hn
      have hgo : loopExprArgsN.go d acc (loopIdx d) invRegs curDepth immSlotMap (.cons v rest)
          = loopResolveVarN d acc (loopIdx d) invRegs curDepth immSlotMap v
            :: loopExprArgsN.go d acc (loopIdx d) invRegs curDepth immSlotMap rest := rfl
      rw [hgo, List.flatMap_cons, List.mem_append] at hn
      rcases hn with hn | hn
      · exact loopResolveVarN_names d acc invRegs curDepth immSlotMap v n hn
      · exact loopExprArgsN_go_names d acc invRegs curDepth immSlotMap rest n hn

/-- Every name of the typed body walk of a fragment update is a `NodeName`. -/
theorem loopBodyWalkNM_names (d : Nat) (acc : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (hcom : ComOpsPlain com) (curDepth : Nat) :
    ∀ i ∈ loopBodyWalkNM d acc (loopIdx d) invRegs immSlotMap com curDepth,
      ∀ n ∈ instrNames i.1, NodeName acc invRegs n := by
  induction com generalizing curDepth with
  | ret v => intro i hi; simp [loopBodyWalkNM] at hi
  | var e body ih =>
      intro i hi n hn
      simp only [loopBodyWalkNM, List.mem_cons] at hi
      rcases hi with rfl | hi
      · rcases opToLinstrR_names e.op hcom.1 _ _ n hn with rfl | h
        · exact Or.inr (Or.inr (head?_loopReg d curDepth))
        · exact loopExprArgsN_go_names d acc invRegs curDepth immSlotMap e.args n h
      · exact ih hcom.2 (curDepth + 1) i hi n hn

/-- **No instruction after the accumulator seed mentions the out-argument.** For a
    fragment update, the typed loop node seeded from `.reg out` mentions `out`
    after its first instruction nowhere, when `out` is distinct from the
    accumulator register, from every invariant base register, from the names of
    the count operand and from the body's return register, and does not start with
    `L`. -/
theorem forLoopLcmdNRtRM_fresh (d : Nat) (acc out : String) (countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hplain : ComOpsPlain update) (hacc : acc ≠ out) (hinv : out ∉ invRegsOf invOps)
    (hcnt : ∀ n ∈ opNames countOp, n ≠ out) (hL : ¬ HeadL out)
    (hret : (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) immSlotMap update
      (2 + invTys.length)).2 ≠ out) :
    ∀ k i, 1 ≤ k →
      (forLoopLcmdNRtRM d acc (.reg out) countOp update invOps immSlotMap)[k]? = some i →
      ∀ n ∈ instrNames i.1, n ≠ out := by
  have hnode : ∀ n, NodeName acc (invRegsOf invOps) n → n ≠ out := by
    rintro n (rfl | h | h) he
    · exact hacc he
    · exact hinv (he ▸ h)
    · exact hL (he ▸ h)
  have hidx : loopIdx d ≠ out := hnode _ (Or.inr (Or.inr (headL_loopIdx d)))
  have hctr : loopCtr d ≠ out := hnode _ (Or.inr (Or.inr (head?_loopCtr d)))
  intro k i hk hi n hn he
  subst he
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [forLoopLcmdNRtRM, loopSeedsRM, List.cons_append, List.nil_append,
    List.getElem?_cons_succ] at hi
  have hmem := List.mem_of_getElem? hi
  simp only [guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge, forLoopBodyNRtRM,
    loopFeedbackRM, loopAdvanceRM, loopTouchRM, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hmem
  rcases hmem with rfl | rfl | (rfl | rfl | rfl |
    ((((hw | hf) | rfl | rfl) | ⟨a, ha, rfl⟩) | rfl | rfl)) | rfl
  case inr.inr.inl.inr.inr.inr.inl.inl.inl.inl =>
    exact hnode n (loopBodyWalkNM_names d acc (invRegsOf invOps) immSlotMap update hplain _
      i hw n hn) rfl
  case inr.inr.inl.inr.inr.inr.inl.inl.inl.inr =>
    split at hf
    · simp at hf
    · simp only [List.mem_singleton] at hf
      subst hf
      simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · exact hacc rfl
      · exact hret rfl
  all_goals
    simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false, or_self] at hn
  all_goals
    first
      | (rcases hn with rfl | rfl | rfl
         · exact hctr rfl
         · exact hctr rfl
         · exact hinv ha)
      | (rcases hn with rfl | rfl <;> first | exact hidx rfl | exact hctr rfl)
      | (rcases hn with rfl | hn
         · exact hctr rfl
         · exact hcnt _ hn rfl)

/-- A string with a first character is not empty. -/
theorem ne_empty_of_head? {s : String} {c : Char} (h : s.toList.head? = some c) : s ≠ "" := by
  rintro rfl
  simp at h

/-- **`aliasRegBody` on the export's names.** The instance of
    `forLoopLcmdNRtRM_alias` at the accumulator register `regName k` and an
    out-argument `argName j`, for a fragment update: the freshness of `argName j`
    after the seed follows from the name shapes, and what remains is that
    `argName j` is no invariant base register, is not mentioned by the count
    operand and is not the body's return register. -/
theorem forLoopLcmdNRtRM_alias_regName_argName (fn : String) (d k j : Nat)
    (countOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hplain : ComOpsPlain update) (hinv : argName j ∉ invRegsOf invOps)
    (hcnt : ∀ n ∈ opNames countOp, n ≠ argName j)
    (hret : (loopBodyWalkN d (regName k) (loopIdx d) (invRegsOf invOps) immSlotMap update
      (2 + invTys.length)).2 ≠ argName j)
    (fuel : Nat) {s s' t : LstateMF}
    (hfn : s.prog.lfn = fn) (hfn' : s'.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 0) (hpc' : s'.prog.base.lpc = 0) (hzf : s'.zf = s.zf)
    (hreg : ∀ r, r ≠ argName j → r ≠ regName k →
      s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
    (hro : s'.prog.base.reg.lvm (argName j) = s.prog.base.reg.lvm (argName j))
    (harr : ∀ r, r ≠ argName j →
      s'.prog.base.larr (aliasRegName (regName k) (argName j) r) = s.prog.base.larr r)
    (hmem : s'.prog.base.lmem = s.prog.base.lmem)
    (hflags : s'.prog.base.cf = s.prog.base.cf ∧ s'.prog.base.of = s.prog.base.of)
    (hrun : lsemFuelMemF (singletonProgM fn
      (forLoopLcmdNRtRM d (regName k) (.reg (argName j)) countOp update invOps immSlotMap))
        fuel s = some t) :
    ∃ t', lsemFuelMemF (singletonProgM fn
        ((forLoopLcmdNRtRM d (regName k) (.reg (argName j)) countOp update invOps
          immSlotMap).map (renRM (aliasRegName (regName k) (argName j))))) fuel s' = some t'
      ∧ RelF (aliasRegName (regName k) (argName j)) (fun r => r ≠ argName j) t t' := by
  have hne : regName k ≠ argName j := by
    intro h
    have h1 := head?_regName k
    rw [h, head?_argName] at h1
    exact absurd h1 (by decide)
  have hL : ¬ HeadL (argName j) := by
    intro h
    unfold HeadL at h
    rw [head?_argName] at h
    exact absurd h (by decide)
  exact forLoopLcmdNRtRM_alias fn d (regName k) (argName j) countOp update invOps immSlotMap
    (ne_empty_of_head? (head?_regName k)) (ne_empty_of_head? (head?_argName j))
    (forLoopLcmdNRtRM_fresh d (regName k) (argName j) countOp update invOps immSlotMap hplain
      hne hinv hcnt hL hret)
    fuel hfn hfn' hpc hpc' hzf hreg hro harr hmem hflags hrun

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
