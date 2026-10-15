/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

@[expose] public section

set_option autoImplicit false

/-!
# Register allocation on the flag machine

The physical export renames the registers of a body through the linear-scan
table (`remapOperand body (physTableOut body [])`). The scan gives names with
disjoint live ranges the same register, so the renaming is not injective on the
names of a body and `JasminLsemExportRewrites.lsemFuelMemF_ren` does not apply.
This module states and proves the simulation for a renaming that is injective
only among the names live at one program counter, on the name-keyed flag machine
`lsemFuelMemF` over `LstateM`: array accesses stay keyed by array name, and a
stack slot `k.N` is a register name like any other.

## Contents

* **§1–§5 two-set step lemmas.** `Keeps σ N M ds` is the write condition of a
  step that writes the names `ds`: a name related after the step is the written
  name, or was related before and has an image different from the written
  name's. `lsemStepN_live`, `lsemStepSh_live`, `lsemStepMC_live`,
  `lsemStepCast_live`, `lsemStepMem_live` match a step of an instruction by a
  step of its renaming between a state pair related on the read names and a
  state pair related on the names kept. Register cells and array cells carry
  separate name sets (`RelM2`), since a register write leaves the array cell of
  the same name unchanged.
* **§6 `LiveCert` and `lsemFuelMemF_live`.** A certificate gives, per program
  counter, the related register names and array names; reads lie in the sets,
  fall-through edges satisfy `Keeps`, and jump edges shrink the sets. Under a
  certificate every halting run is matched with the same fuel.
  `lsemFuelMemF_live_calls` is the same matching at an instruction set `I` with
  `x86Isa.StepLe I` whose further steps are local calls (`Isa.CallLocal`), under the
  call condition `LiveCalls`: the array operands of a call are related arrays, and the
  destination of a word-array result is related before the call. A word result is
  written as by `regDefs_callShadow`, an array result as an array store, and the renamed
  operands read the same argument words (`argsRead_ren`). `lsemFuelMemF_live` is the
  instance at `x86Isa`.
* **§7 live ranges.** `liveCert_of_ranges` builds a certificate from one interval
  per name (`RangeCert`): a write lies in the interval of its name, a name that
  is not an input starts at a write, and names whose intervals share a program
  counter have different images (`Interf`). A jump needs `JumpOK`: every name
  live after the target label has an interval that reaches a backward jump.
  `Interf.extend` lengthens one interval when no other interval begins inside
  the added part.
* **§8 the export's table.** `physSigma` is the export's renaming with the empty
  name fixed; `remapOperand_eq_renOperand` identifies the operand remap with it.
  `physSigma_interf` derives `Interf` for intervals inside the scan's own live
  ranges from `physRename_hinj_of_liveAt`.
* **§9** a counted loop whose two temporaries share a register, with its
  certificate (`reuseBody_run`) and a closed halting run (`reuseBody_halts`).

## Scope

The renamed program is `body.map (renRM σ)`. The export's physical body also
lowers each three-address binop to `MOV d, a ; OP d, d, b` and routes operands
in stack slots through `R15`/`R14` (`lowerTwoAddr_length`), which changes
instruction counts and program counters; that expansion is not treated here.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc

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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill (physRename)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference
  (LiveAt physRename_hinj_of_liveAt)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow callMnem_ne retWord
  retRes lpc_retRes argRead argsRead argsRead_none storeStruct?_callShadow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

/-! ## 1. Read names, written names and the write condition -/

/-- The register names the source operands of an instruction mention. -/
def useNames : LinstrR → List String
  | .Lopn _ _ s => s.flatMap opNames
  | _ => []

/-- The register names the destination operands of an instruction mention. -/
def defNames : LinstrR → List String
  | .Lopn d _ _ => d.flatMap opNames
  | _ => []

/-- The write condition of a step that writes the names `ds`, between the name set
    `N` related before the step and the name set `M` related after it: a name of
    `M` is the single written name, or it lies in `N` and its image under `σ`
    differs from the image of every written name. -/
def Keeps (σ : String → String) (N M : String → Prop) (ds : List String) : Prop :=
  ∀ r, M r → ds = [r] ∨ (N r ∧ ∀ d ∈ ds, σ r ≠ σ d)

variable {σ : String → String} {N M : String → Prop}

theorem Keeps.sub (h : Keeps σ N M []) : ∀ r, M r → N r := by
  intro r hr
  rcases h r hr with h | h
  · exact absurd h (by simp)
  · exact h.1

theorem relN_mono {s s' : LstateN} (h : RelN σ N s s') (hM : ∀ r, M r → N r) :
    RelN σ M s s' :=
  ⟨h.1, fun r hr => h.2 r (hM r hr)⟩

/-- A write of the same value to `d` and to `σ d` carries the relation on `N` to
    the relation on `M`, under the write condition at `[d]`. -/
theorem relN_setReg_keeps {s s' : LstateN} (h : RelN σ N s s') {d : String}
    (hK : Keeps σ N M [d]) {w : Nat} (v : BitVec w) :
    RelN σ M ((s.setReg d v).nextPc) ((s'.setReg (σ d) v).nextPc) := by
  refine ⟨by simp [h.1], fun r hr => ?_⟩
  simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg]
  rcases hK r hr with hd | ⟨hN, hne⟩
  · obtain rfl : d = r := by simpa using hd
    simp
  · have hrd : r ≠ d := fun he => hne d (by simp) (by rw [he])
    rw [if_neg (hne d (by simp)), if_neg hrd]
    exact h.2 r hN

theorem relN_operandName_of {s s' : LstateN} (hemp : N "") (hfix : σ "" = "")
    (h : RelN σ N s s') (w : Nat) (o : LOperand) (ho : ∀ n ∈ opNames o, N n) :
    s'.getW (operandName (renOperand σ o)) w = s.getW (operandName o) w := by
  cases o
  case reg r => exact h.getW (ho _ (by simp [opNames])) w
  all_goals
    simp only [renOperand, JasminLsemWidthN.operandName]
    have := h.getW hemp w
    rwa [hfix] at this

/-- The names of the source operands of an `Lopn`, operand by operand. -/
theorem uses_of_lopn {d s : List LOperand} {opn : String}
    (hu : ∀ n ∈ useNames (.Lopn d opn s), N n) :
    ∀ o ∈ s, ∀ n ∈ opNames o, N n := by
  intro o ho n hn
  refine hu n ?_
  simp only [useNames, List.mem_flatMap]
  exact ⟨o, ho, hn⟩

/-! ## 2. The register steps -/

set_option hygiene false in
/-- Close a step goal whose renamed side reads the original state: split the
    hypothesis `h`, discard the failing arms, and close the successful arm with
    `RelN.setReg_keeps` at the write condition `hK`. -/
local macro "live_close" : tactic =>
  `(tactic| ((repeat' split at h) <;>
      first
        | (simp at h; done)
        | (cases h; refine ⟨_, ?_, relN_setReg_keeps hR hK _⟩;
           simp only [*, if_true, if_false, reduceIte]; try (rw [if_neg (by decide)]))))

/-- **`lsemStepN` between two name sets.** A successful step of an instruction
    whose read names lie in `N` is matched by a step of the renamed instruction
    from a state related on `N`, into a state related on `M`, under the write
    condition of the instruction's destination. -/
theorem lsemStepN_live (hemp : N "") (hfix : σ "" = "") (i : LinstrR)
    (hu : ∀ n ∈ useNames i, N n) (hK : Keeps σ N M (defNames i))
    {s s' t : LstateN} (hR : RelN σ N s s') (h : lsemStepN i s = some t) :
    ∃ t', lsemStepN (renLinstrR σ i) s' = some t' ∧ RelN σ M t t' := by
  unfold lsemStepN at h
  split at h
  · rename_i dst opn c a b
    have ho := uses_of_lopn hu
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, lsemStepN,
      relN_operandName_of hemp hfix hR 1 c (ho c (by simp)),
      hR.readReg a (ho a (by simp)),
      fun w => hR.evalOperandN w b (ho b (by simp))]
    live_close
  · rename_i dst opn a b
    have ho := uses_of_lopn hu
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, lsemStepN,
      hR.readReg a (ho a (by simp)),
      fun w => hR.evalOperandN w b (ho b (by simp))]
    cases hra : readReg s a with
    | some wv =>
      obtain ⟨w, va⟩ := wv
      simp only [hra] at h ⊢
      live_close
    | none =>
      simp only [hra] at h ⊢
      cases a with
      | imm n =>
        simp only [renOperand_imm, immFirstN,
          fun w => hR.evalOperandN w b (ho b (by simp))] at h ⊢
        cases hb : evalOperandN s (widthFromTag opn) b with
        | none => simp [hb] at h
        | some vb =>
          simp only [hb] at h ⊢
          obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
          exact ⟨_, by rw [hv]; rfl, relN_setReg_keeps hR hK _⟩
      | _ => simp at h
  · rename_i dst opn n
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, renOperand_imm,
      lsemStepN]
    live_close
  · rename_i dst opn a
    have ho := uses_of_lopn hu
    have hra : readReg s' (.reg (σ a)) = readReg s (.reg a) :=
      hR.readReg (.reg a) (ho (.reg a) (by simp))
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, lsemStepN, hra]
    live_close
  · rename_i dst opn b x sc
    have ho := uses_of_lopn hu
    have hb : s'.getW (σ b) 64 = s.getW b 64 :=
      hR.getW (ho (.arrIdx b x sc) (by simp) b (by simp [opNames])) 64
    have hx : s'.getW (σ x) 64 = s.getW x 64 :=
      hR.getW (ho (.arrIdx b x sc) (by simp) x (by simp [opNames])) 64
    simp only [renLinstrR, List.map_cons, List.map_nil, renOperand_reg, renOperand_arrIdx,
      lsemStepN, hb, hx]
    live_close
  · exact absurd h (by simp)
  · cases h; exact ⟨_, rfl, (relN_mono hR hK.sub).nextPc⟩
  · cases h; exact ⟨_, rfl, (relN_mono hR hK.sub).nextPc⟩
  all_goals exact absurd h (by simp)

/-! ## 3. The written name and the read names of a recognised instruction -/

set_option hygiene false in
/-- Prove the shape facts of a recogniser: the destination list of the recognised
    instruction is the returned destination, and the returned sources are read
    names. -/
local macro "recog_shape" : tactic =>
  `(tactic| (
      split at h
      · split at h
        · cases h; simp [defNames, useNames, opNames]
        · simp at h
      · simp at h))

theorem sarStruct?_shape {i : LinstrR} {p : String × String × Nat}
    (h : sarStruct? i = some p) : defNames i = [p.1] ∧ p.2.1 ∈ useNames i := by
  unfold sarStruct? at h; recog_shape

theorem mulhiStruct?_shape {i : LinstrR} {p : String × String × String}
    (h : mulhiStruct? i = some p) :
    defNames i = [p.1] ∧ p.2.1 ∈ useNames i ∧ p.2.2 ∈ useNames i := by
  unfold mulhiStruct? at h; recog_shape

theorem adcxStruct?_shape {i : LinstrR} {p : String × String × String × String}
    (h : adcxStruct? i = some p) :
    defNames i = [p.1] ∧ p.2.1 ∈ useNames i ∧ p.2.2.1 ∈ useNames i
      ∧ p.2.2.2 ∈ useNames i := by
  unfold adcxStruct? at h; recog_shape

theorem adcxhiStruct?_shape {i : LinstrR} {p : String × String × String × String}
    (h : adcxhiStruct? i = some p) :
    defNames i = [p.1] ∧ p.2.1 ∈ useNames i ∧ p.2.2.1 ∈ useNames i
      ∧ p.2.2.2 ∈ useNames i := by
  unfold adcxhiStruct? at h; recog_shape

theorem sbbStruct?_shape {i : LinstrR} {p : String × String × String × String}
    (h : sbbStruct? i = some p) :
    defNames i = [p.1] ∧ p.2.1 ∈ useNames i ∧ p.2.2.1 ∈ useNames i
      ∧ p.2.2.2 ∈ useNames i := by
  unfold sbbStruct? at h; recog_shape

theorem sbbhiStruct?_shape {i : LinstrR} {p : String × String × String × String}
    (h : sbbhiStruct? i = some p) :
    defNames i = [p.1] ∧ p.2.1 ∈ useNames i ∧ p.2.2.1 ∈ useNames i
      ∧ p.2.2.2 ∈ useNames i := by
  unfold sbbhiStruct? at h; recog_shape

theorem castStruct?_shape {i : LinstrR} {p : String × String}
    (h : castStruct? i = some p) : defNames i = [p.1] ∧ p.2 ∈ useNames i := by
  unfold castStruct? at h; recog_shape

theorem movImmStruct?_shape {i : LinstrR} {p : String × Nat}
    (h : movImmStruct? i = some p) : defNames i = [p.1] := by
  unfold movImmStruct? at h
  split at h
  · cases h; simp [defNames, opNames]
  · simp at h

theorem loadStruct?_shape {i : LinstrR} {p : String × String × String}
    (h : loadStruct? i = some p) :
    defNames i = [p.1] ∧ p.2.1 ∈ useNames i ∧ p.2.2 ∈ useNames i := by
  unfold loadStruct? at h; recog_shape

theorem storeStruct?_shape {i : LinstrR} {p : String × String × String × String}
    (h : storeStruct? i = some p) :
    defNames i = [p.1] ∧ p.2.1 ∈ useNames i ∧ p.2.2.1 ∈ useNames i
      ∧ p.2.2.2 ∈ useNames i := by
  unfold storeStruct? at h; recog_shape

theorem storeImmStruct?_shape {i : LinstrR} {p : String × String × String × Nat}
    (h : storeImmStruct? i = some p) :
    defNames i = [p.1] ∧ p.2.1 ∈ useNames i ∧ p.2.2.1 ∈ useNames i := by
  unfold storeImmStruct? at h; recog_shape

theorem loadCStruct?_shape {i : LinstrR} {p : String × String × Nat}
    (h : loadCStruct? i = some p) : defNames i = [p.1] := by
  unfold loadCStruct? at h; recog_shape

theorem storeCStruct?_shape {i : LinstrR} {p : String × Nat × String}
    (h : storeCStruct? i = some p) : defNames i = [] ∧ p.2.2 ∈ useNames i := by
  unfold storeCStruct? at h; recog_shape

/-! ## 4. The shift, carry and cast steps -/

/-- **`lsemStepSh` between two name sets.** -/
theorem lsemStepSh_live (hemp : N "") (hfix : σ "" = "") (i : LinstrR)
    (hu : ∀ n ∈ useNames i, N n) (hK : Keeps σ N M (defNames i))
    {s s' t : LstateN} (hR : RelN σ N s s') (h : lsemStepSh i s = some t) :
    ∃ t', lsemStepSh (renLinstrR σ i) s' = some t' ∧ RelN σ M t t' := by
  unfold lsemStepSh at h ⊢
  rw [sarStruct?_ren]
  cases hs : sarStruct? i with
  | none =>
      rw [hs] at h
      exact lsemStepN_live hemp hfix i hu hK hR h
  | some p =>
      obtain ⟨d, a, n⟩ := p
      simp only [hs] at h
      obtain ⟨hd, ha⟩ := sarStruct?_shape hs
      rw [hd] at hK
      simp only [Option.map_some, hR.readReg_reg (hu _ ha)]
      live_close

/-- **`lsemStepMC` between two name sets.** -/
theorem lsemStepMC_live (hemp : N "") (hfix : σ "" = "") (i : LinstrR)
    (hu : ∀ n ∈ useNames i, N n) (hK : Keeps σ N M (defNames i))
    {s s' t : LstateN} (hR : RelN σ N s s') (h : lsemStepMC i s = some t) :
    ∃ t', lsemStepMC (renLinstrR σ i) s' = some t' ∧ RelN σ M t t' := by
  unfold lsemStepMC at h ⊢
  rw [mulhiStruct?_ren, adcxStruct?_ren, adcxhiStruct?_ren, sbbStruct?_ren, sbbhiStruct?_ren]
  cases h1 : mulhiStruct? i with
  | some p =>
      obtain ⟨d, a, b⟩ := p
      simp only [h1] at h
      obtain ⟨hd, ha, hb⟩ := mulhiStruct?_shape h1
      rw [hd] at hK
      simp only [Option.map_some, hR.readReg_reg (hu _ ha), fun w => hR.getW (hu _ hb) w]
      live_close
  | none =>
  simp only [h1, Option.map_none] at h ⊢
  cases h2 : adcxStruct? i with
  | some p =>
      obtain ⟨d, a, b, c⟩ := p
      simp only [h2] at h
      obtain ⟨hd, ha, hb, hc⟩ := adcxStruct?_shape h2
      rw [hd] at hK
      simp only [Option.map_some, hR.readReg_reg (hu _ ha), fun w => hR.getW (hu _ hb) w,
        hR.getW (hu _ hc) 1]
      live_close
  | none =>
  simp only [h2, Option.map_none] at h ⊢
  cases h3 : adcxhiStruct? i with
  | some p =>
      obtain ⟨d, a, b, c⟩ := p
      simp only [h3] at h
      obtain ⟨hd, ha, hb, hc⟩ := adcxhiStruct?_shape h3
      rw [hd] at hK
      simp only [Option.map_some, hR.readReg_reg (hu _ ha), fun w => hR.getW (hu _ hb) w,
        hR.getW (hu _ hc) 1]
      live_close
  | none =>
  simp only [h3, Option.map_none] at h ⊢
  cases h4 : sbbStruct? i with
  | some p =>
      obtain ⟨d, a, b, c⟩ := p
      simp only [h4] at h
      obtain ⟨hd, ha, hb, hc⟩ := sbbStruct?_shape h4
      rw [hd] at hK
      simp only [Option.map_some, hR.readReg_reg (hu _ ha), fun w => hR.getW (hu _ hb) w,
        hR.getW (hu _ hc) 1]
      live_close
  | none =>
  simp only [h4, Option.map_none] at h ⊢
  cases h5 : sbbhiStruct? i with
  | some p =>
      obtain ⟨d, a, b, c⟩ := p
      simp only [h5] at h
      obtain ⟨hd, ha, hb, hc⟩ := sbbhiStruct?_shape h5
      rw [hd] at hK
      simp only [Option.map_some, hR.readReg_reg (hu _ ha), fun w => hR.getW (hu _ hb) w,
        hR.getW (hu _ hc) 1]
      live_close
  | none =>
  simp only [h5, Option.map_none] at h ⊢
  exact lsemStepSh_live hemp hfix i hu hK hR h

/-- **`lsemStepCast` between two name sets.** -/
theorem lsemStepCast_live (hemp : N "") (hfix : σ "" = "") (i : LinstrR) (cd : Option Nat)
    (hu : ∀ n ∈ useNames i, N n) (hK : Keeps σ N M (defNames i))
    {s s' t : LstateN} (hR : RelN σ N s s') (h : lsemStepCast (i, cd) s = some t) :
    ∃ t', lsemStepCast (renLinstrR σ i, cd) s' = some t' ∧ RelN σ M t t' := by
  cases cd with
  | none =>
      rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)] at h
      rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
      exact lsemStepMC_live hemp hfix i hu hK hR h
  | some w' =>
      unfold lsemStepCast at h ⊢
      dsimp only at h ⊢
      rw [castStruct?_ren, movImmStruct?_ren]
      cases h1 : castStruct? i with
      | none =>
          cases h2 : movImmStruct? i with
          | none =>
              simp only [h1, h2, Option.map_none] at h ⊢
              exact lsemStepMC_live hemp hfix i hu hK hR h
          | some p =>
              obtain ⟨d, n⟩ := p
              have hd := movImmStruct?_shape h2
              rw [hd] at hK
              simp only [h1, h2, Option.map_none, Option.map_some] at h ⊢
              cases h
              exact ⟨_, rfl, relN_setReg_keeps hR hK _⟩
      | some p =>
          obtain ⟨d, a⟩ := p
          obtain ⟨hd, ha⟩ := castStruct?_shape h1
          rw [hd] at hK
          simp only [h1, Option.map_some, hR.readReg_reg (hu _ ha)] at h ⊢
          live_close

/-! ## 5. The memory step between two pairs of name sets

Register cells and array cells are keyed by the same names and written by
different instructions, so the relation carries one name set for each. -/

/-- The memory-state relation of a renaming `σ` on a register name set `Nr` and an
    array name set `Na`: related register files on `Nr`, the renamed state holds
    at `σ r` the array cell the original holds at `r` for `r` in `Na`, and equal
    compile-time-offset word memories. -/
def RelM2 (σ : String → String) (Nr Na : String → Prop) (s s' : LstateM) : Prop :=
  RelN σ Nr s.reg s'.reg ∧ (∀ r, Na r → s'.larr (σ r) = s.larr r) ∧ s'.lmem = s.lmem

/-- The array name a store-tagged `STOREIDX`, a zero-tagged `ZEROARR` or a
    constant-index `STOREIMM` writes. -/
def storeHit? (i : LinstrRM) : Option String :=
  match i.2 with
  | .store _ _ => (storeStruct? i.1).map (fun p => p.1)
  | .zero _ _ => zeroStruct? i.1
  | .storeImm _ _ => (storeImmStruct? i.1).map (fun p => p.1)
  | _ => none

/-- The array name a load-tagged `LOADIDX` or a store-tagged `STOREIDX` reads. -/
def arrUse? (i : LinstrRM) : Option String :=
  match i.2 with
  | .load _ _ => (loadStruct? i.1).map (fun p => p.2.1)
  | .store _ _ => (storeStruct? i.1).map (fun p => p.2.1)
  | .storeImm _ _ => (storeImmStruct? i.1).map (fun p => p.2.1)
  | _ => none

/-- The register names the memory step of an instruction writes. -/
def memRegDefs (i : LinstrRM) : List String :=
  if (storeHit? i).isSome then [] else defNames i.1

/-- The array names the memory step of an instruction writes. -/
def memArrDefs (i : LinstrRM) : List String := (storeHit? i).toList

variable {Nr Na Mr Ma : String → Prop}

theorem RelM2.getArr {s s' : LstateM} (h : RelM2 σ Nr Na s s') {r : String} (hr : Na r)
    (w n : Nat) : s'.getArr (σ r) w n = s.getArr r w n := by
  unfold LstateM.getArr
  rw [h.2.1 r hr]

theorem RelM2.setReg_keeps {s s' : LstateM} (h : RelM2 σ Nr Na s s') {d : String}
    (hK : Keeps σ Nr Mr [d]) (hA : ∀ r, Ma r → Na r) {w : Nat} (v : BitVec w) :
    RelM2 σ Mr Ma ((s.setReg d v).nextPc) ((s'.setReg (σ d) v).nextPc) :=
  ⟨relN_setReg_keeps h.1 hK v, fun r hr => h.2.1 r (hA r hr), h.2.2⟩

theorem RelM2.setArr_keeps {s s' : LstateM} (h : RelM2 σ Nr Na s s') {d : String}
    (hK : Keeps σ Na Ma [d]) (hRg : ∀ r, Mr r → Nr r) {w n : Nat} (arr : Fin n → BitVec w) :
    RelM2 σ Mr Ma ((s.setArr d arr).nextPc) ((s'.setArr (σ d) arr).nextPc) := by
  refine ⟨(relN_mono h.1 hRg).nextPc, fun r hr => ?_, h.2.2⟩
  simp only [LstateM.larr_nextPc, LstateM.larr_setArr]
  rcases hK r hr with hd | ⟨hN, hne⟩
  · obtain rfl : d = r := by simpa using hd
    simp
  · have hrd : r ≠ d := fun he => hne d (by simp) (by rw [he])
    rw [if_neg (hne d (by simp)), if_neg hrd]
    exact h.2.1 r hN

theorem RelM2.storeMemC {s s' : LstateM} (h : RelM2 σ Nr Na s s') (hRg : ∀ r, Mr r → Nr r)
    (hA : ∀ r, Ma r → Na r) (base : String) (off : Int) (v : BitVec 64) :
    RelM2 σ Mr Ma ((s.storeMemC base off v).nextPc) ((s'.storeMemC base off v).nextPc) := by
  refine ⟨(relN_mono h.1 hRg).nextPc, fun r hr => h.2.1 r (hA r hr), ?_⟩
  simp only [LstateM.lmem_nextPc, LstateM.lmem_storeMemC, h.2.2]

/-- The register-binding delegate of the memory step between two pairs of name
    sets. -/
theorem lsemStepMem_delegate_live (hemp : Nr "") (hfix : σ "" = "") (i : LinstrR)
    (cd : Option Nat) (hu : ∀ n ∈ useNames i, Nr n) (hK : Keeps σ Nr Mr (defNames i))
    (hA : ∀ r, Ma r → Na r) {s s' t : LstateM} (hR : RelM2 σ Nr Na s s')
    (h : (lsemStepCast (i, cd) s.reg).map (fun r => { s with reg := r }) = some t) :
    ∃ t', (lsemStepCast (renLinstrR σ i, cd) s'.reg).map (fun r => { s' with reg := r })
        = some t' ∧ RelM2 σ Mr Ma t t' := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r', hr', hRr⟩ := lsemStepCast_live hemp hfix i cd hu hK hR.1 hr
  exact ⟨{ s' with reg := r' }, by rw [hr']; rfl, hRr, fun r hr => hR.2.1 r (hA r hr), hR.2.2⟩

set_option hygiene false in
/-- `live_close` with the closing relation proof given explicitly. -/
local macro "live_close_with " t:term : tactic =>
  `(tactic| ((repeat' split at h) <;>
      first
        | (simp at h; done)
        | (cases h; refine ⟨_, ?_, $t⟩;
           simp only [*, if_true, if_false, reduceIte])))

/-- **`lsemStepMem` between two pairs of name sets.** A successful typed memory
    step of an instruction whose read register names lie in `Nr` and whose read
    array name lies in `Na` is matched by a step of the renamed instruction from
    a state related on `(Nr, Na)`, into a state related on `(Mr, Ma)`, under the
    write conditions of the written register names and the written array name. -/
theorem lsemStepMem_live (hemp : Nr "") (hfix : σ "" = "") (i : LinstrRM)
    (hu : ∀ n ∈ useNames i.1, Nr n) (hau : ∀ b, arrUse? i = some b → Na b)
    (hKr : Keeps σ Nr Mr (memRegDefs i)) (hKa : Keeps σ Na Ma (memArrDefs i))
    {s s' t : LstateM} (hR : RelM2 σ Nr Na s s') (h : lsemStepMem i s = some t) :
    ∃ t', lsemStepMem (renRM σ i) s' = some t' ∧ RelM2 σ Mr Ma t t' := by
  obtain ⟨wire, tag⟩ := i
  unfold lsemStepMem at h ⊢
  cases tag with
  | reg cd =>
      exact lsemStepMem_delegate_live hemp hfix wire cd hu
        (by simpa [memRegDefs, storeHit?] using hKr)
        (by simpa [memArrDefs, storeHit?] using hKa.sub) hR h
  | load w n =>
      have hKr' : Keeps σ Nr Mr (defNames wire) := by simpa [memRegDefs, storeHit?] using hKr
      have hA : ∀ r, Ma r → Na r := by simpa [memArrDefs, storeHit?] using hKa.sub
      dsimp only [renRM] at h ⊢
      rw [loadStruct?_ren]
      cases h1 : loadStruct? wire with
      | none =>
          simp only [h1, Option.map_none] at h ⊢
          exact lsemStepMem_delegate_live hemp hfix wire none hu hKr' hA hR h
      | some p =>
          obtain ⟨d, b, x⟩ := p
          obtain ⟨hd, hb, hx⟩ := loadStruct?_shape h1
          rw [hd] at hKr'
          have hNb : Na b := hau b (by simp [arrUse?, h1])
          simp only [h1, Option.map_some, hR.getArr hNb, hR.1.getW (hu _ hx)] at h ⊢
          live_close_with (RelM2.setReg_keeps hR hKr' hA _)
  | store w n =>
      dsimp only [renRM] at h ⊢
      rw [storeStruct?_ren]
      cases h1 : storeStruct? wire with
      | none =>
          simp only [h1, Option.map_none] at h ⊢
          exact lsemStepMem_delegate_live hemp hfix wire none hu
            (by simpa [memRegDefs, storeHit?, h1] using hKr)
            (by
              have : Keeps σ Na Ma [] := by simpa [memArrDefs, storeHit?, h1] using hKa
              exact this.sub) hR h
      | some p =>
          obtain ⟨d, b, x, v⟩ := p
          obtain ⟨hd, hb, hx, hv⟩ := storeStruct?_shape h1
          have hKa' : Keeps σ Na Ma [d] := by simpa [memArrDefs, storeHit?, h1] using hKa
          have hRg : ∀ r, Mr r → Nr r := by
            have : Keeps σ Nr Mr [] := by simpa [memRegDefs, storeHit?, h1] using hKr
            exact this.sub
          have hNb : Na b := hau b (by simp [arrUse?, h1])
          simp only [h1, Option.map_some, hR.getArr hNb, hR.1.getW (hu _ hx),
            hR.1.getW (hu _ hv)] at h ⊢
          live_close_with (RelM2.setArr_keeps hR hKa' hRg _)
  | loadC =>
      have hKr' : Keeps σ Nr Mr (defNames wire) := by simpa [memRegDefs, storeHit?] using hKr
      have hA : ∀ r, Ma r → Na r := by simpa [memArrDefs, storeHit?] using hKa.sub
      dsimp only [renRM] at h ⊢
      rw [loadCStruct?_ren]
      cases h1 : loadCStruct? wire with
      | none => simp [h1] at h
      | some p =>
          obtain ⟨d, b, off⟩ := p
          rw [loadCStruct?_shape h1] at hKr'
          simp only [h1, Option.map_some, hR.2.2] at h ⊢
          live_close_with (RelM2.setReg_keeps hR hKr' hA _)
  | storeC =>
      have hKr' : Keeps σ Nr Mr (defNames wire) := by simpa [memRegDefs, storeHit?] using hKr
      have hA : ∀ r, Ma r → Na r := by simpa [memArrDefs, storeHit?] using hKa.sub
      dsimp only [renRM] at h ⊢
      rw [storeCStruct?_ren]
      cases h1 : storeCStruct? wire with
      | none => simp [h1] at h
      | some p =>
          obtain ⟨b, off, src⟩ := p
          obtain ⟨hd, hsrc⟩ := storeCStruct?_shape h1
          rw [hd] at hKr'
          simp only [h1, Option.map_some, hR.1.getW (hu _ hsrc)] at h ⊢
          live_close_with (RelM2.storeMemC hR hKr'.sub hA _ _ _)
  | zero w n =>
      dsimp only [renRM] at h ⊢
      rw [zeroStruct?_ren]
      cases h1 : zeroStruct? wire with
      | none => simp [h1] at h
      | some d =>
          have hKa' : Keeps σ Na Ma [d] := by simpa [memArrDefs, storeHit?, h1] using hKa
          have hRg : ∀ r, Mr r → Nr r := by
            have : Keeps σ Nr Mr [] := by simpa [memRegDefs, storeHit?, h1] using hKr
            exact this.sub
          simp only [h1, Option.map_some] at h ⊢
          cases h
          exact ⟨_, rfl, RelM2.setArr_keeps hR hKa' hRg _⟩
  | storeImm w n =>
      dsimp only [renRM] at h ⊢
      rw [storeImmStruct?_ren]
      cases h1 : storeImmStruct? wire with
      | none => simp [h1] at h
      | some p =>
          obtain ⟨d, b, v, k⟩ := p
          obtain ⟨hd, hb, hv⟩ := storeImmStruct?_shape h1
          have hKa' : Keeps σ Na Ma [d] := by simpa [memArrDefs, storeHit?, h1] using hKa
          have hRg : ∀ r, Mr r → Nr r := by
            have : Keeps σ Nr Mr [] := by simpa [memRegDefs, storeHit?, h1] using hKr
            exact this.sub
          have hNb : Na b := hau b (by simp [arrUse?, h1])
          simp only [h1, Option.map_some, hR.getArr hNb, hR.1.getW (hu _ hv)] at h ⊢
          live_close_with (RelM2.setArr_keeps hR hKa' hRg _)

/-! ## 6. The flag machine under a liveness certificate -/

/-- The register names the flag-machine step of an instruction writes: none for
    the flag compare, the destination for the register copy, and the names of the
    memory step otherwise. -/
def regDefs (i : LinstrRM) : List String :=
  if (cmpArgs? i).isSome then []
  else if (movRegArgs? i).isSome then defNames i.1
  else memRegDefs i

/-- The array names the flag-machine step of an instruction writes. -/
def arrDefs (i : LinstrRM) : List String :=
  if (cmpArgs? i).isSome then []
  else if (movRegArgs? i).isSome then []
  else memArrDefs i

/-- The label a jump instruction names. -/
def jumpLabel? : LinstrR → Option LLabel
  | .Lcond _ l => some l
  | .Lgoto (_, l) => some l
  | _ => none

/-- The flag-machine state relation on a register name set and an array name set:
    related memory states, the same function name, the same zero flag and the same
    carry and overflow flags. -/
def RelF2 (σ : String → String) (Nr Na : String → Prop) (s s' : LstateMF) : Prop :=
  RelM2 σ Nr Na s.prog.base s'.prog.base ∧ s'.prog.lfn = s.prog.lfn ∧ s'.zf = s.zf
    ∧ s'.prog.base.cf = s.prog.base.cf ∧ s'.prog.base.of = s.prog.base.of

/-- The flag writes of `withALUFlags` preserve the relation. -/
theorem RelM2.withALUFlags {b b' : LstateM} (h : RelM2 σ Nr Na b b') (i i' : LinstrRM)
    (s0 s0' : LstateM) : RelM2 σ Nr Na (withALUFlags i s0 b) (withALUFlags i' s0' b') := by
  unfold RelM2
  simp only [withALUFlags_reg, withALUFlags_larr, withALUFlags_lmem]
  exact h

/-- The operands a flag-writing arithmetic operation reads are source operands. -/
theorem aluFlagOp?_uses {i : LinstrRM} {p : AluOp × LOperand × LOperand}
    (h : aluFlagOp? i = some p) :
    (∀ n ∈ opNames p.2.1, n ∈ useNames i.1) ∧ (∀ n ∈ opNames p.2.2, n ∈ useNames i.1) := by
  obtain ⟨wire, tag⟩ := i
  unfold aluFlagOp? at h
  dsimp only at h
  split at h
  · split_ifs at h <;> cases h <;> simp only [useNames, List.mem_flatMap] <;>
      exact ⟨fun n hn => ⟨_, by simp, hn⟩, fun n hn => ⟨_, by simp, hn⟩⟩
  · simp at h

/-- A carry-family instruction writes its destination register, no array, and reads its
    two source operands. -/
theorem carryArgs?_shape {i : LinstrRM} {p : CarryOp × String × LOperand × LOperand}
    (h : carryArgs? i = some p) :
    memRegDefs i = [p.2.1] ∧ memArrDefs i = []
      ∧ (∀ n ∈ opNames p.2.2.1, n ∈ useNames i.1) ∧ (∀ n ∈ opNames p.2.2.2, n ∈ useNames i.1) := by
  obtain ⟨wire, tag⟩ := i
  unfold carryArgs? at h
  dsimp only at h
  split at h
  · rename_i d opn a b
    have hm : opn ≠ "STOREIDX" := by
      split_ifs at h <;> subst_vars <;> decide +kernel
    have hmz : opn ≠ "ZEROARR" := by
      split_ifs at h <;> subst_vars <;> decide +kernel
    have hst : storeStruct? (.Lopn [.reg d] opn [a, b]) = none := by
      unfold storeStruct?
      split
      · rename_i heq
        simp only [LinstrR.Lopn.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        rw [if_neg hm]
      · rfl
    have hsh : storeHit? (.Lopn [.reg d] opn [a, b], tag) = none := by
      unfold storeHit?
      cases tag <;> simp [hst, zeroStruct?, hmz, storeImmStruct?]
    split_ifs at h <;> cases h <;>
      exact ⟨by simp [memRegDefs, hsh, defNames, opNames], by simp [memArrDefs, hsh],
        fun n hn => by simp only [useNames, List.mem_flatMap]; exact ⟨_, by simp, hn⟩,
        fun n hn => by simp only [useNames, List.mem_flatMap]; exact ⟨_, by simp, hn⟩⟩
  · simp at h

/-- The flags `withALUFlags` writes for the renamed instruction from a related state are
    the flags it writes for the original instruction. -/
theorem withALUFlags_live {i : LinstrRM} (hu : ∀ n ∈ useNames i.1, Nr n) {s0 s0' b b' : LstateM}
    (hR : RelN σ Nr s0.reg s0'.reg) (hb : b'.cf = b.cf ∧ b'.of = b.of) :
    (withALUFlags (renRM σ i) s0' b').cf = (withALUFlags i s0 b).cf
      ∧ (withALUFlags (renRM σ i) s0' b').of = (withALUFlags i s0 b).of := by
  unfold withALUFlags
  rw [aluFlagOp?_ren]
  cases h : aluFlagOp? i with
  | none => exact hb
  | some p =>
      obtain ⟨op, a, c⟩ := p
      obtain ⟨ha, hc⟩ := aluFlagOp?_uses h
      simp only [Option.map_some,
        hR.evalOperandN 64 a (fun n hn => hu n (ha n hn)),
        hR.evalOperandN 64 c (fun n hn => hu n (hc n hn))]
      split
      · exact ⟨rfl, rfl⟩
      · exact hb

/-- A carry-family step under the relation. -/
theorem carryStep_live {op : CarryOp} {d : String} {a c : LOperand}
    (hK : Keeps σ Nr Mr [d]) (hA : ∀ r, Ma r → Na r)
    (ha : ∀ n ∈ opNames a, Nr n) (hc : ∀ n ∈ opNames c, Nr n)
    {s s' t : LstateM} (hR : RelM2 σ Nr Na s s') (hf : s'.cf = s.cf ∧ s'.of = s.of)
    (h : carryStep op d a c s = some t) :
    ∃ t', carryStep op (σ d) (renOperand σ a) (renOperand σ c) s' = some t'
      ∧ RelM2 σ Mr Ma t t' ∧ t'.cf = t.cf ∧ t'.of = t.of := by
  unfold carryStep at h ⊢
  rw [hR.1.evalOperandN 64 a ha, hR.1.evalOperandN 64 c hc, hf.1, hf.2]
  split at h
  · cases op <;> cases h <;>
      exact ⟨_, rfl, RelM2.setReg_keeps hR hK hA _,
        by first | rfl | exact hf.1, by first | rfl | exact hf.2⟩
  · cases h

/-- A two-source `MOV` writes its destination register, no array, and reads its second
    source operand. -/
theorem wideArgs?_shape_mov {i : LinstrRM} {d : String} {b : LOperand}
    (h : wideArgs? i = some (.mov d b)) :
    memRegDefs i = [d] ∧ memArrDefs i = [] ∧ (∀ n ∈ opNames b, n ∈ useNames i.1) := by
  obtain ⟨wire, tag⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · rename_i d' opn a b'
    split_ifs at h with ho
    cases h
    have hst : storeStruct? (.Lopn [.reg d] opn [a, b]) = none := by
      unfold storeStruct?
      split
      · rename_i heq
        simp only [LinstrR.Lopn.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        rw [if_neg (by subst ho; decide +kernel)]
      · rfl
    have hmz : opn ≠ "ZEROARR" := by subst ho; decide +kernel
    have hsh : storeHit? (.Lopn [.reg d] opn [a, b], tag) = none := by
      unfold storeHit?
      cases tag <;> simp [hst, zeroStruct?, hmz, storeImmStruct?]
    exact ⟨by simp [memRegDefs, hsh, defNames, opNames], by simp [memArrDefs, hsh],
      fun n hn => by simp only [useNames, List.mem_flatMap]; exact ⟨_, by simp, hn⟩⟩
  · split_ifs at h
    cases h
  · cases h

/-- A two-source `MOV` step under a liveness certificate. -/
theorem wideStep_mov_live {d : String} {b : LOperand}
    (hK : Keeps σ Nr Mr [d]) (hA : ∀ r, Ma r → Na r) (hb : ∀ n ∈ opNames b, Nr n)
    {s s' t : LstateM} (hR : RelM2 σ Nr Na s s') (hf : s'.cf = s.cf ∧ s'.of = s.of)
    (h : wideStep (.mov d b) s = some t) :
    ∃ t', wideStep (.mov (σ d) (renOperand σ b)) s' = some t'
      ∧ RelM2 σ Mr Ma t t' ∧ t'.cf = t.cf ∧ t'.of = t.of := by
  simp only [wideStep] at h ⊢
  rw [hR.1.evalOperandN 64 b hb]
  split at h
  · cases h
    exact ⟨_, rfl, RelM2.setReg_keeps hR hK hA _, hf.1, hf.2⟩
  · cases h

theorem RelM2.mono {s s' : LstateM} (h : RelM2 σ Nr Na s s') (hRg : ∀ r, Mr r → Nr r)
    (hA : ∀ r, Ma r → Na r) : RelM2 σ Mr Ma s s' :=
  ⟨relN_mono h.1 hRg, fun r hr => h.2.1 r (hA r hr), h.2.2⟩

theorem RelM2.nextPc {s s' : LstateM} (h : RelM2 σ Nr Na s s') :
    RelM2 σ Nr Na s.nextPc s'.nextPc :=
  ⟨h.1.nextPc, h.2.1, h.2.2⟩

theorem RelM2.setLpc {s s' : LstateM} (h : RelM2 σ Nr Na s s') (pc : Nat) :
    RelM2 σ Nr Na (s.setLpc pc) (s'.setLpc pc) :=
  ⟨⟨rfl, h.1.2⟩, h.2.1, h.2.2⟩

/-- The operands the flag compare returns are source operands. -/
theorem cmpArgs?_uses {i : LinstrRM} {p : LOperand × LOperand} (h : cmpArgs? i = some p) :
    (∀ n ∈ opNames p.1, n ∈ useNames i.1) ∧ (∀ n ∈ opNames p.2, n ∈ useNames i.1) := by
  obtain ⟨wire, tag⟩ := i
  unfold cmpArgs? at h
  dsimp only at h
  split at h
  · split at h
    · cases h
      simp only [useNames, List.mem_flatMap]
      exact ⟨fun n hn => ⟨_, by simp, hn⟩, fun n hn => ⟨_, by simp, hn⟩⟩
    · simp at h
  · simp at h

theorem movRegArgs?_shape {i : LinstrRM} {p : String × String} (h : movRegArgs? i = some p) :
    defNames i.1 = [p.1] ∧ p.2 ∈ useNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold movRegArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h <;> cases h <;> simp [defNames, useNames, opNames]
  · simp at h

theorem flagCondCC?_jumpLabel {i : LinstrRM} {p : Bool × LLabel} (h : flagCondCC? i = some p) :
    jumpLabel? i.1 = some p.2 := by
  obtain ⟨wire, tag⟩ := i
  unfold flagCondCC? at h
  dsimp only at h
  split at h <;> first | (cases h; rfl) | simp at h

theorem jumpLabel?_not_lopn {i : LinstrR} {l : LLabel} (h : jumpLabel? i = some l) :
    ∀ d o s, i ≠ LinstrR.Lopn d o s := by
  intro d o s he
  subst he
  simp [jumpLabel?] at h

/-- The memory step of an instruction that is not an `Lopn` writes no name. -/
theorem memDefs_nil_of_not_lopn {i : LinstrRM} (h : ∀ d o s, i.1 ≠ LinstrR.Lopn d o s) :
    memRegDefs i = [] ∧ memArrDefs i = [] := by
  obtain ⟨wire, tag⟩ := i
  cases wire with
  | Lopn d o s => exact absurd rfl (h d o s)
  | _ => cases tag <;> simp [memRegDefs, memArrDefs, storeHit?, storeStruct?, zeroStruct?,
      storeImmStruct?, defNames]

/-- A liveness certificate for a program `P`, a renaming `σ` and the program `P'`
    that holds the renamed instructions from index `k0` on. `Lr k` and `La k` are
    the register names and the array names whose cells are related at program
    counter `k`.

    * The read names of the instruction at `k` lie in `Lr k`, and its read array
      name in `La k`.
    * Fall-through: a name of `Lr (k + 1)` is the single name the instruction
      writes, or lies in `Lr k` and its image differs from the image of every
      written name; the same for arrays.
    * Jump: the sets at the instruction after the target label are included in
      the sets at the jump.

    `σ` is not required to be injective: two names with the same image are never
    in the same set `Lr k` across a write to one of them. -/
structure LiveCert (σ : String → String) (k0 : Nat) (P P' : LprogM)
    (Lr La : Nat → String → Prop) : Prop where
  /-- The function names agree. -/
  lfn : P'.lfn = P.lfn
  /-- The label positions agree. -/
  lbl : ∀ l, findLabelMem l P'.body = findLabelMem l P.body
  /-- From `k0` on the renamed program holds the renamed instructions. -/
  body : ∀ k, k0 ≤ k → P'.body[k]? = (P.body[k]?).map (renRM σ)
  /-- From `k0` on the conditionals read the zero flag. -/
  cond : ∀ k i, k0 ≤ k → P.body[k]? = some i → CondOK i
  /-- Every jump lands at `k0` or later. -/
  jmp : ∀ l pc, findLabelMem l P.body = some pc → k0 ≤ pc + 1
  /-- The empty name is related at every program counter. -/
  emp : ∀ k, Lr k ""
  /-- The empty name is fixed. -/
  fix : σ "" = ""
  /-- The read register names are related before the step. -/
  uses : ∀ k i, k0 ≤ k → P.body[k]? = some i → ∀ n ∈ useNames i.1, Lr k n
  /-- The read array name is related before the step. -/
  arrUse : ∀ k i, k0 ≤ k → P.body[k]? = some i → ∀ b, arrUse? i = some b → La k b
  /-- The register write condition of the fall-through edge. -/
  fallR : ∀ k i, k0 ≤ k → P.body[k]? = some i → Keeps σ (Lr k) (Lr (k + 1)) (regDefs i)
  /-- The array write condition of the fall-through edge. -/
  fallA : ∀ k i, k0 ≤ k → P.body[k]? = some i → Keeps σ (La k) (La (k + 1)) (arrDefs i)
  /-- The register sets along a jump edge. -/
  jumpR : ∀ k i l pc, k0 ≤ k → P.body[k]? = some i → jumpLabel? i.1 = some l →
    findLabelMem l P.body = some pc → ∀ r, Lr (pc + 1) r → Lr k r
  /-- The array sets along a jump edge. -/
  jumpA : ∀ k i l pc, k0 ≤ k → P.body[k]? = some i → jumpLabel? i.1 = some l →
    findLabelMem l P.body = some pc → ∀ r, La (pc + 1) r → La k r

variable {k0 : Nat} {P P' : LprogM} {Lr La : Nat → String → Prop}

/-- A jump under a certificate: the target state is related on the sets of the
    instruction after the label. -/
theorem evalJumpMem_live (hC : LiveCert σ k0 P P' Lr La) {k : Nat} {i : LinstrRM} {l : LLabel}
    (hk : k0 ≤ k) (hget : P.body[k]? = some i) (hl : jumpLabel? i.1 = some l)
    {p p' q : LstatePM} (hR : RelM2 σ (Lr k) (La k) p.base p'.base) (hfn : p'.lfn = p.lfn)
    (h : evalJumpMem P l p = some q) :
    ∃ q', evalJumpMem P' l p' = some q'
      ∧ RelM2 σ (Lr q.base.lpc) (La q.base.lpc) q.base q'.base ∧ q'.lfn = q.lfn
      ∧ k0 ≤ q.base.lpc := by
  unfold evalJumpMem at h ⊢
  rw [hC.lbl l]
  cases hf : findLabelMem l P.body with
  | none => simp [hf] at h
  | some pc =>
      simp only [hf] at h ⊢
      cases h
      exact ⟨_, rfl,
        (hR.mono (hC.jumpR k i l pc hk hget hl hf) (hC.jumpA k i l pc hk hget hl hf)).setLpc _,
        hfn, hC.jmp l pc hf⟩

/-- **The flag step under a liveness certificate.** A successful flag-machine step
    of the instruction at program counter `k ≥ k0`, from a state related on the
    sets at `k`, is matched by a step of the renamed instruction, into a state
    related on the sets at its program counter. -/
theorem evalInstrPMemF_live (hC : LiveCert σ k0 P P' Lr La) (i : LinstrRM)
    {s s' t : LstateMF} (hk : k0 ≤ s.prog.base.lpc) (hget : P.body[s.prog.base.lpc]? = some i)
    (hR : RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s')
    (h : evalInstrPMemF P i s = some t) :
    ∃ t', evalInstrPMemF P' (renRM σ i) s' = some t'
      ∧ RelF2 σ (Lr t.prog.base.lpc) (La t.prog.base.lpc) t t' ∧ k0 ≤ t.prog.base.lpc := by
  have hu := hC.uses _ i hk hget
  have hau := hC.arrUse _ i hk hget
  have hKr := hC.fallR _ i hk hget
  have hKa := hC.fallA _ i hk hget
  have hemp := hC.emp s.prog.base.lpc
  unfold evalInstrPMemF at h ⊢
  rw [cmpArgs?_ren, movRegArgs?_ren, flagCondCC?_ren]
  cases h1 : cmpArgs? i with
  | some p =>
      obtain ⟨a, b⟩ := p
      obtain ⟨ha, hb⟩ := cmpArgs?_uses h1
      have hKr' : Keeps σ (Lr s.prog.base.lpc) (Lr (s.prog.base.lpc + 1)) [] := by
        simpa [regDefs, h1] using hKr
      have hKa' : Keeps σ (La s.prog.base.lpc) (La (s.prog.base.lpc + 1)) [] := by
        simpa [arrDefs, h1] using hKa
      simp only [h1, Option.map_some,
        hR.1.1.evalOperandN 64 a (fun n hn => hu n (ha n hn)),
        hR.1.1.evalOperandN 64 b (fun n hn => hu n (hb n hn))] at h ⊢
      split at h
      · cases h
        exact ⟨_, rfl, ⟨(hR.1.mono hKr'.sub hKa'.sub).nextPc, hR.2.1, rfl, hR.2.2.2⟩,
          Nat.le_succ_of_le hk⟩
      · simp at h
  | none =>
  simp only [h1, Option.map_none] at h ⊢
  cases h2 : movRegArgs? i with
  | some p =>
      obtain ⟨d, r⟩ := p
      obtain ⟨hd, hr⟩ := movRegArgs?_shape h2
      have hKr' : Keeps σ (Lr s.prog.base.lpc) (Lr (s.prog.base.lpc + 1)) [d] := by
        simpa [regDefs, h1, h2, hd] using hKr
      have hKa' : Keeps σ (La s.prog.base.lpc) (La (s.prog.base.lpc + 1)) [] := by
        simpa [arrDefs, h1, h2] using hKa
      simp only [h2, Option.map_some, hR.1.1.readReg_reg (hu _ hr)] at h ⊢
      split at h
      · cases h
        exact ⟨_, rfl, ⟨RelM2.setReg_keeps hR.1 hKr' hKa'.sub _, hR.2.1, hR.2.2.1, hR.2.2.2⟩,
          Nat.le_succ_of_le hk⟩
      · simp at h
  | none =>
  simp only [h2, Option.map_none] at h ⊢
  have hKr' : Keeps σ (Lr s.prog.base.lpc) (Lr (s.prog.base.lpc + 1)) (memRegDefs i) := by
    simpa [regDefs, h1, h2] using hKr
  have hKa' : Keeps σ (La s.prog.base.lpc) (La (s.prog.base.lpc + 1)) (memArrDefs i) := by
    simpa [arrDefs, h1, h2] using hKa
  have hstep : ∀ {q : LstatePM},
      (lsemStepMem i s.prog.base).map (fun b => { s.prog with base := b }) = some q →
      ∃ q', (lsemStepMem (renRM σ i) s'.prog.base).map (fun b => { s'.prog with base := b })
          = some q' ∧ RelM2 σ (Lr q.base.lpc) (La q.base.lpc) q.base q'.base
          ∧ q'.lfn = q.lfn ∧ k0 ≤ q.base.lpc := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨b', hb', hRb⟩ := lsemStepMem_live hemp hC.fix i hu hau hKr' hKa' hR.1 hb
    have hpc : b.lpc = s.prog.base.lpc + 1 := lsemStepMem_lpc_succ i s.prog.base b hb
    refine ⟨{ s'.prog with base := b' }, by rw [hb']; rfl, ?_, hR.2.1, ?_⟩
    · show RelM2 σ (Lr b.lpc) (La b.lpc) b b'
      rw [hpc]; exact hRb
    · show k0 ≤ b.lpc
      omega
  have hfall : (∀ d o s, i.1 ≠ LinstrR.Lopn d o s) →
      RelM2 σ (Lr (s.prog.base.lpc + 1)) (La (s.prog.base.lpc + 1))
        s.prog.base.nextPc s'.prog.base.nextPc := by
    intro hno
    obtain ⟨hr0, ha0⟩ := memDefs_nil_of_not_lopn hno
    rw [hr0] at hKr'
    rw [ha0] at hKa'
    exact (hR.1.mono hKr'.sub hKa'.sub).nextPc
  cases h3 : flagCondCC? i with
  | some p =>
      obtain ⟨pol, l⟩ := p
      have hl := flagCondCC?_jumpLabel h3
      simp only [h3, hR.2.2.1] at h ⊢
      split at h
      · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨q', hq', hRq, hfn, hkq⟩ := evalJumpMem_live hC hk hget hl hR.1 hR.2.1 hq
        refine ⟨{ prog := q', zf := s.zf }, by rw [if_pos (by assumption), hq']; rfl,
          ⟨hRq, hfn, rfl, ?_, ?_⟩, hkq⟩
        · rw [(evalJumpMem_flags hq').1, (evalJumpMem_flags hq).1]; exact hR.2.2.2.1
        · rw [(evalJumpMem_flags hq').2, (evalJumpMem_flags hq).2]; exact hR.2.2.2.2
      · cases h
        exact ⟨{ prog := { s'.prog with base := s'.prog.base.nextPc }, zf := s.zf },
          by rw [if_neg (by assumption)],
          ⟨hfall (jumpLabel?_not_lopn hl), hR.2.1, rfl, hR.2.2.2⟩, Nat.le_succ_of_le hk⟩
  | none =>
  simp only [h3] at h ⊢
  have hc := hC.cond _ i hk hget
  have hL : ∀ {q : LstatePM}, evalInstrPMemL P i s.prog = some q →
      ∃ q', evalInstrPMemL P' (renRM σ i) s'.prog = some q'
        ∧ RelM2 σ (Lr q.base.lpc) (La q.base.lpc) q.base q'.base ∧ q'.lfn = q.lfn
        ∧ k0 ≤ q.base.lpc := by
    intro q hq
    clear h
    obtain ⟨wire, tag⟩ := i
    cases wire with
    | Llabel kd l =>
        simp only [evalInstrPMemL, renRM, renLinstrR] at hq ⊢
        cases hq
        exact ⟨_, rfl, hfall (fun _ _ _ he => by cases he), hR.2.1, Nat.le_succ_of_le hk⟩
    | Lcond c l => exact absurd h3 (hc.1 c l rfl)
    | Lgoto tgt =>
        obtain ⟨fn, l⟩ := tgt
        simp only [evalInstrPMemL, renRM, renLinstrR] at hq ⊢
        rw [hC.lfn]
        split at hq
        · rw [if_pos (by assumption)]
          exact evalJumpMem_live hC hk hget rfl hR.1 hR.2.1 hq
        · simp at hq
    | Lopn d o s => exact hstep hq
    | Lsyscall _ => exact hstep hq
    | Lcall _ _ => exact hstep hq
    | Lret => exact hstep hq
    | Lalign => exact hstep hq
    | Ligoto _ => exact hstep hq
    | LstoreLabel _ _ => exact hstep hq
  rw [carryArgs?_ren]
  cases hq : evalInstrPMemL P i s.prog with
  | some q =>
      simp only [hq, Option.some.injEq] at h
      subst h
      obtain ⟨q', hq', hRq, hfn, hkq⟩ := hL hq
      have hfq := evalInstrPMemL_flags hq
      have hfq' := evalInstrPMemL_flags hq'
      have hw := withALUFlags_live (i := i) (s0 := s.prog.base) (s0' := s'.prog.base)
        (b := q.base) (b' := q'.base) hu hR.1.1
        ⟨by rw [hfq'.1, hfq.1]; exact hR.2.2.2.1, by rw [hfq'.2, hfq.2]; exact hR.2.2.2.2⟩
      refine ⟨{ prog := { base := withALUFlags (renRM σ i) s'.prog.base q'.base,
                          lfn := q'.lfn }, zf := s'.zf },
        by rw [hq'], ⟨?_, hfn, hR.2.2.1, hw.1, hw.2⟩, ?_⟩
      · show RelM2 σ (Lr (withALUFlags i s.prog.base q.base).lpc)
          (La (withALUFlags i s.prog.base q.base).lpc) _ _
        rw [withALUFlags_lpc]
        exact RelM2.withALUFlags hRq _ _ _ _
      · show k0 ≤ (withALUFlags i s.prog.base q.base).lpc
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
                  obtain ⟨hmr, hma, hb⟩ := wideArgs?_shape_mov hw
                  simp only [hw] at h
                  obtain ⟨u, hu', rfl⟩ := Option.map_eq_some_iff.mp h
                  rw [hmr] at hKr'
                  rw [hma] at hKa'
                  obtain ⟨u', hu'', hRu, hcf, hof⟩ := wideStep_mov_live hKr' hKa'.sub
                    (fun n hn => hu n (hb n hn)) hR.1 hR.2.2.2 hu'
                  have hw' := wideArgs?_ren_mov (σ := σ) hw
                  have hq'none : evalInstrPMemL P' (renRM σ i) s'.prog = none := by
                    rw [evalInstrPMemL_lopn _ _ _ (wideArgs?_isLopn hw'),
                      lsemStepMem_of_wideArgs hw', Option.map_none]
                  have hpc := wideStep_lpc _ _ _ hu'
                  refine ⟨{ prog := { base := u', lfn := s'.prog.lfn }, zf := s'.zf },
                    by rw [hq'none]; simp only [Option.map_none, hw', Option.map_some, hu''],
                    ⟨?_, hR.2.1, hR.2.2.1, hcf, hof⟩, ?_⟩
                  · show RelM2 σ (Lr u.lpc) (La u.lpc) u u'
                    rw [hpc]; exact hRu
                  · show k0 ≤ u.lpc
                    omega
      | some p =>
          obtain ⟨op, d, a, c⟩ := p
          obtain ⟨hmr, hma, ha, hcn⟩ := carryArgs?_shape hk3
          simp only [hk3] at h
          obtain ⟨u, hu', rfl⟩ := Option.map_eq_some_iff.mp h
          rw [hmr] at hKr'
          rw [hma] at hKa'
          obtain ⟨u', hu'', hRu, hcf, hof⟩ := carryStep_live hKr' hKa'.sub
            (fun n hn => hu n (ha n hn)) (fun n hn => hu n (hcn n hn)) hR.1 hR.2.2.2 hu'
          have hk3' : carryArgs? (renRM σ i) = some (op, σ d, renOperand σ a, renOperand σ c) := by
            rw [carryArgs?_ren, hk3]; rfl
          have hq'none : evalInstrPMemL P' (renRM σ i) s'.prog = none := by
            have hlopn : IsLopn (renRM σ i) := by
              unfold carryArgs? at hk3'
              split at hk3'
              · rename_i heq; exact ⟨_, _, _, heq⟩
              · cases hk3'
            rw [evalInstrPMemL_lopn _ _ _ hlopn, lsemStepMem_of_carryArgs hk3', Option.map_none]
          have hpc := carryStep_lpc _ _ _ _ _ _ hu'
          refine ⟨{ prog := { base := u', lfn := s'.prog.lfn }, zf := s'.zf },
            by rw [hq'none]; simp only [Option.map_some, hu''], ⟨?_, hR.2.1, hR.2.2.1, hcf, hof⟩,
            ?_⟩
          · show RelM2 σ (Lr u.lpc) (La u.lpc) u u'
            rw [hpc]; exact hRu
          · show k0 ≤ u.lpc
            omega


theorem cmpArgs?_callShadow (dst f : String) (srcs : List LOperand) (tag : MemTag) :
    cmpArgs? (callShadow dst f srcs, tag) = none := by
  unfold cmpArgs? callShadow
  split
  · next heq =>
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      exact if_neg (callMnem_ne (by decide))
  · rfl

/-- A shadow instruction of a call is no array zeroing. -/
theorem zeroStruct?_callShadow (dst f : String) (srcs : List LOperand) :
    zeroStruct? (callShadow dst f srcs) = none := by
  simp only [callShadow, zeroStruct?]
  exact if_neg (callMnem_ne (by decide))

/-- A shadow instruction of a call is no constant-index store. -/
theorem storeImmStruct?_callShadow (dst f : String) (srcs : List LOperand) :
    storeImmStruct? (callShadow dst f srcs) = none := by
  unfold callShadow storeImmStruct?
  split
  · rename_i heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨-, rfl, -⟩ := heq
    exact if_neg (callMnem_ne (by decide))
  · rfl

/-- A shadow instruction of a call writes its destination register. -/
theorem regDefs_callShadow (dst f : String) (srcs : List LOperand) (tag : MemTag) :
    regDefs (callShadow dst f srcs, tag) = [dst] := by
  have hs : storeHit? (callShadow dst f srcs, tag) = none := by
    cases tag <;> simp [storeHit?, storeStruct?_callShadow, zeroStruct?_callShadow,
      storeImmStruct?_callShadow]
  unfold regDefs memRegDefs
  rw [cmpArgs?_callShadow, hs]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, ite_self]
  rfl

/-- A shadow instruction of a call writes no array. -/
theorem arrDefs_callShadow (dst f : String) (srcs : List LOperand) (tag : MemTag) :
    arrDefs (callShadow dst f srcs, tag) = [] := by
  have hs : storeHit? (callShadow dst f srcs, tag) = none := by
    cases tag <;> simp [storeHit?, storeStruct?_callShadow, zeroStruct?_callShadow,
      storeImmStruct?_callShadow]
  unfold arrDefs memArrDefs
  rw [cmpArgs?_callShadow, hs]
  simp only [Option.isSome_none, Bool.false_eq_true, Option.toList_none, ite_self]

/-- The renamed operands read, as words, the words of the operands. -/
theorem mapM_evalOperandN_ren {s s' : LstateN} (h : RelN σ N s s') :
    ∀ (srcs : List LOperand), (∀ o ∈ srcs, ∀ n ∈ opNames o, N n) →
      (srcs.map (renOperand σ)).mapM (evalOperandN s' 64) = srcs.mapM (evalOperandN s 64)
  | [], _ => rfl
  | o :: os, ho => by
      rw [List.map_cons, List.mapM_cons, List.mapM_cons,
        h.evalOperandN 64 o (ho o List.mem_cons_self),
        mapM_evalOperandN_ren h os fun o' h' => ho o' (List.mem_cons_of_mem _ h')]

/-- **The call condition of a liveness certificate**, at the array positions `aa f` and the
    result lengths `ao f` of the called symbols: from `k0` on, at a shadow instruction
    `callShadow dst f srcs`, the register operand at every array position of `f` names an
    array related before the step; and at a symbol with a word-array result, the destination
    is a register name related before the step, and every array name related after the step
    is the destination, or is related before it and has an image other than the image of
    the destination. -/
def LiveCalls (σ : String → String) (k0 : Nat) (P : LprogM) (Lr La : Nat → String → Prop)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) : Prop :=
  ∀ (k : Nat) (i : LinstrRM) (dst f : String) (srcs : List LOperand), k0 ≤ k →
    P.body[k]? = some i → i.1 = callShadow dst f srcs →
      (∀ (j n : Nat) (A : String), aa f j = some n → srcs[j]? = some (.reg A) → La k A)
      ∧ ∀ n, ao f = some n → Lr k dst ∧ Keeps σ (La k) (La (k + 1)) [dst]

/-- Without array positions and without word-array results the call condition holds. -/
theorem liveCalls_none : LiveCalls σ k0 P Lr La (fun _ _ => none) (fun _ => none) :=
  fun _ _ _ _ _ _ _ _ => ⟨fun _ _ _ h _ => (nomatch h), fun _ h => (nomatch h)⟩

/-- **The argument words of the renamed operands.** In states related on the register names
    `Nr` and the array names `Na`, the renamed operands read, from the argument position
    `j` at the array positions `a`, the argument words of the operands, when the register
    names of the operands lie in `Nr` and the register operand at every array position
    names an array of `Na`. -/
theorem argsRead_ren {Nr Na : String → Prop} {a : Nat → Option Nat} {b b' : LstateM}
    (hR : RelM2 σ Nr Na b b') :
    ∀ (j : Nat) (srcs : List LOperand), (∀ o ∈ srcs, ∀ n ∈ opNames o, Nr n) →
      (∀ (m n : Nat) (A : String), a (j + m) = some n → srcs[m]? = some (.reg A) → Na A) →
      argsRead a b' j (srcs.map (renOperand σ)) = argsRead a b j srcs
  | _, [], _, _ => rfl
  | j, o :: os, hu, hA => by
      have ho : argRead a b' j (renOperand σ o) = argRead a b j o := by
        unfold argRead
        cases hj : a j with
        | none =>
            simp only
            rw [hR.1.evalOperandN 64 o (hu o List.mem_cons_self)]
        | some n =>
            cases o with
            | reg A =>
                have hNA : Na A := hA 0 n A (by simpa using hj) rfl
                simp only [renOperand, hR.getArr hNA]
            | _ => rfl
      rw [List.map_cons, argsRead, argsRead, ho,
        argsRead_ren hR (j + 1) os (fun o' h' => hu o' (List.mem_cons_of_mem _ h'))
          (fun m n A h1 h2 => hA (m + 1) n A (by rw [← h1]; congr 1; omega) h2)]

/-- **The step under a liveness certificate at an instruction set with local calls.** The
    statement of `evalInstrPMemF_live` for the step of an instruction set `I` whose steps
    contain those of `x86Isa` and whose further steps are local calls at the array
    positions `aa` and the result lengths `ao`, under the call condition `LiveCalls`. -/
theorem step_live_calls {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) (hC : LiveCert σ k0 P P' Lr La)
    (hK : LiveCalls σ k0 P Lr La aa ao) (i : LinstrRM)
    {s s' t : LstateMF} (hk : k0 ≤ s.prog.base.lpc) (hget : P.body[s.prog.base.lpc]? = some i)
    (hR : RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s')
    (h : I.step P i s = some t) :
    ∃ t', I.step P' (renRM σ i) s' = some t'
      ∧ RelF2 σ (Lr t.prog.base.lpc) (La t.prog.base.lpc) t t' ∧ k0 ≤ t.prog.base.lpc := by
  rcases hcl P i s t h with hx | ⟨dst, f, srcs, x, hi, rfl, hfwd, hlen⟩
  · obtain ⟨t', ht', hrest⟩ := evalInstrPMemF_live hC i hk hget hR hx
    exact ⟨t', hle _ _ _ _ ht', hrest⟩
  · obtain ⟨w, tag⟩ := i
    simp only at hi
    subst hi
    have hu := hC.uses _ _ hk hget
    have hKr := hC.fallR _ _ hk hget
    have hKa := hC.fallA _ _ hk hget
    obtain ⟨hcA, hcO⟩ := hK _ _ dst f srcs hk hget rfl
    rw [regDefs_callShadow] at hKr
    rw [arrDefs_callShadow] at hKa
    have hpc := lpc_retRes dst x s
    have hren : renRM σ (callShadow dst f srcs, tag)
        = (callShadow (σ dst) f (srcs.map (renOperand σ)), tag) := rfl
    rw [hren]
    obtain ⟨⟨hRn, hRa, hRm⟩, hfn, hz, hcf, hof⟩ := hR
    refine ⟨retRes (σ dst) x s', hfwd P' tag (σ dst) _ s' (List.length_map _) ?_, ?_, ?_⟩
    · exact argsRead_ren ⟨hRn, hRa, hRm⟩ 0 srcs
        (fun o ho n hn => hu n (List.mem_flatMap.mpr ⟨o, ho, hn⟩))
        (fun m n A h1 h2 => hcA m n A (by simpa using h1) h2)
    · rw [hpc]
      cases x with
      | word r =>
          exact ⟨⟨relN_setReg_keeps hRn hKr r, fun a ha => hRa a (hKa.sub a ha), hRm⟩, hfn, hz,
            hcf, hof⟩
      | arr a =>
          obtain ⟨hd, hKa'⟩ := hcO _ hlen.symm
          have hsub : ∀ r, Lr (s.prog.base.lpc + 1) r → Lr s.prog.base.lpc r := fun r hr => by
            rcases hKr r hr with h1 | h1
            · obtain rfl : dst = r := by simpa using h1
              exact hd
            · exact h1.1
          exact ⟨RelM2.setArr_keeps ⟨hRn, hRa, hRm⟩ hKa' hsub a, hfn, hz, hcf, hof⟩
    · rw [hpc]
      exact Nat.le_succ_of_le hk

/-- **The flag machine under a liveness certificate, at an instruction set with local
    calls.** For a program `P`, a renaming `σ`, a program `P'` with a certificate from `k0`
    on and an instruction set `I` whose steps contain those of `x86Isa` and whose further
    steps are local calls at the array positions `aa` and the result lengths `ao`, under
    the call condition `LiveCalls`, every halting run of `I` on `P` from a state at program
    counter `k ≥ k0` is matched, with the same fuel, by a halting run of `I` on `P'` from a
    state related on the sets at `k`, into a state related on the sets at the final program
    counter. -/
theorem lsemFuelMemF_live_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hC : LiveCert σ k0 P P' Lr La) (hK : LiveCalls σ k0 P Lr La aa ao) :
    ∀ (fuel : Nat) {s s' t : LstateMF},
      RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s' → k0 ≤ s.prog.base.lpc →
      I.lsemFuelMemF P fuel s = some t →
      ∃ t', I.lsemFuelMemF P' fuel s' = some t'
        ∧ RelF2 σ (Lr t.prog.base.lpc) (La t.prog.base.lpc) t t' := by
  have hfetch : ∀ {s s' : LstateMF},
      RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s' → k0 ≤ s.prog.base.lpc →
      findInstrMem P' s'.prog = (findInstrMem P s.prog).map (renRM σ) := by
    intro s s' hR hk
    unfold findInstrMem
    rw [hR.2.1, hC.lfn]
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
    split
    · rw [hpc]; exact hC.body _ hk
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
              obtain ⟨u', hu', hRu, hku⟩ := step_live_calls hle hcl hC hK i hk hget hR he
              simp only [hu']
              exact ih hRu hku h

/-- **The flag machine under a liveness certificate.** For a program `P`, a
    renaming `σ` and a program `P'` with a certificate from `k0` on, every halting
    run of `P` from a state at program counter `k ≥ k0` is matched, with the same
    fuel, by a halting run of `P'` from a state related on the sets at `k`, into a
    state related on the sets at the final program counter. -/
theorem lsemFuelMemF_live (hC : LiveCert σ k0 P P' Lr La) :
    ∀ (fuel : Nat) {s s' t : LstateMF},
      RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s' → k0 ≤ s.prog.base.lpc →
      lsemFuelMemF P fuel s = some t →
      ∃ t', lsemFuelMemF P' fuel s' = some t'
        ∧ RelF2 σ (Lr t.prog.base.lpc) (La t.prog.base.lpc) t t' := by
  rw [← x86Isa_lsemFuelMemF]
  exact lsemFuelMemF_live_calls (Isa.StepLe.refl x86Isa)
    (Isa.CallLocal.refl x86Isa (fun _ _ => none)) hC liveCalls_none

/-! ## 7. Certificates from live ranges

A linear-scan allocator works against one interval of program counters per name.
This section builds the sets of a `LiveCert` from such intervals and reduces the
certificate to statements about the intervals. -/

/-- The program counter `k` lies in the interval `rng`. -/
def Covers (rng : Nat × Nat) (k : Nat) : Prop := rng.1 ≤ k ∧ k ≤ rng.2

/-- The name `n` holds a value before the instruction at `k`: its interval has not
    ended, and it started before `k` or `n` is an input. -/
def LiveIn (rng : String → Nat × Nat) (In : String → Prop) (k : Nat) (n : String) : Prop :=
  k ≤ (rng n).2 ∧ ((rng n).1 < k ∨ In n)

/-- The related names at `k`: the empty name and the names that hold a value. -/
def Live (rng : String → Nat × Nat) (In : String → Prop) (k : Nat) (n : String) : Prop :=
  n = "" ∨ LiveIn rng In k n

/-- Interference freedom of a renaming against a family of intervals: two distinct
    non-empty names whose intervals share a program counter have different
    images. -/
def Interf (σ : String → String) (rng : String → Nat × Nat) : Prop :=
  ∀ a b k, a ≠ b → a ≠ "" → b ≠ "" → Covers (rng a) k → Covers (rng b) k → σ a ≠ σ b

/-- **Lengthening one interval keeps interference freedom** when every other
    interval that meets the added part `(e, e']` also contains the old end `e`.
    This is the case of a loop-carried name whose last touch precedes the
    back-edge: the instructions between that touch and the back-edge touch only
    names whose intervals began before it. -/
theorem Interf.extend {rng : String → Nat × Nat} (h : Interf σ rng) (x : String) (e' : Nat)
    (hx : (rng x).1 ≤ (rng x).2)
    (hmeet : ∀ a k, a ≠ x → a ≠ "" → (rng x).2 < k → k ≤ e' → Covers (rng a) k →
      Covers (rng a) (rng x).2) :
    Interf σ (fun n => if n = x then ((rng x).1, e') else rng n) := by
  have key : ∀ a k, a ≠ x → a ≠ "" → x ≠ "" → Covers (rng a) k →
      Covers ((rng x).1, e') k → σ a ≠ σ x := by
    intro a k hax ha hx0 hca hcx
    by_cases hk : k ≤ (rng x).2
    · exact h a x k hax ha hx0 hca ⟨hcx.1, hk⟩
    · exact h a x (rng x).2 hax ha hx0
        (hmeet a k hax ha (by omega) hcx.2 hca) ⟨hx, Nat.le_refl _⟩
  intro a b k hab ha hb hca hcb
  by_cases hax : a = x
  · subst hax
    have hbx : b ≠ a := fun he => hab he.symm
    simp only [if_true, if_neg hbx] at hca hcb
    exact fun he => key b k hbx hb ha hcb hca he.symm
  · by_cases hbx : b = x
    · subst hbx
      simp only [if_true, if_neg hax] at hca hcb
      exact key a k hax ha hb hca hcb
    · simp only [if_neg hax, if_neg hbx] at hca hcb
      exact h a b k hab ha hb hca hcb

/-- The interval conditions for one kind of cell (register or array), for the
    written-name function `defs` of that kind. -/
structure RangeCert (σ : String → String) (k0 : Nat) (body : List LinstrRM)
    (defs : LinstrRM → List String) (rng : String → Nat × Nat) (In : String → Prop) :
    Prop where
  /-- An instruction writes at most one name. -/
  single : ∀ k i, k0 ≤ k → body[k]? = some i → (defs i).length ≤ 1
  /-- The interval of an input starts at `k0` or earlier. -/
  inEarly : ∀ n, In n → (rng n).1 ≤ k0
  /-- A write lies in the interval of the written name. -/
  defCov : ∀ k i, k0 ≤ k → body[k]? = some i → ∀ d ∈ defs i, d ≠ "" → Covers (rng d) k
  /-- The interval of a name that is not an input starts at a write of it. -/
  start : ∀ k i n, k0 ≤ k → body[k]? = some i → n ≠ "" → ¬ In n → (rng n).1 = k →
    k < (rng n).2 → n ∈ defs i
  /-- Interference freedom: two names whose intervals share a program counter
      have different images. -/
  interf : Interf σ rng

theorem eq_singleton_of_mem {l : List String} {r : String} (hl : l.length ≤ 1) (hr : r ∈ l) :
    l = [r] := by
  match l, hl, hr with
  | [x], _, hr => rw [List.mem_singleton.mp hr]
  | _ :: _ :: _, hl, _ => simp at hl

/-- The write condition of the fall-through edge, from the interval conditions. -/
theorem RangeCert.keeps {k0 : Nat} {body : List LinstrRM} {defs : LinstrRM → List String}
    {rng : String → Nat × Nat} {In : String → Prop}
    (hC : RangeCert σ k0 body defs rng In) (hfix : σ "" = "") (hne : ∀ n, n ≠ "" → σ n ≠ "")
    {k : Nat} {i : LinstrRM} (hk : k0 ≤ k) (hget : body[k]? = some i) :
    Keeps σ (Live rng In k) (Live rng In (k + 1)) (defs i) := by
  intro r hr
  by_cases hmem : r ∈ defs i
  · exact Or.inl (eq_singleton_of_mem (hC.single k i hk hget) hmem)
  · refine Or.inr ⟨?_, ?_⟩
    · rcases hr with rfl | ⟨he, hb⟩
      · exact Or.inl rfl
      · by_cases hr0 : r = ""
        · exact Or.inl hr0
        · refine Or.inr ⟨by omega, ?_⟩
          by_cases hIn : In r
          · exact Or.inr hIn
          · rcases hb with hb | hb
            · by_cases hst : (rng r).1 = k
              · exact absurd (hC.start k i r hk hget hr0 hIn hst (by omega)) hmem
              · exact Or.inl (by omega)
            · exact absurd hb hIn
    · intro d hd
      by_cases hd0 : d = ""
      · subst hd0
        rw [hfix]
        exact hne r (fun he => hmem (he ▸ hd))
      · by_cases hr0 : r = ""
        · subst hr0
          rw [hfix]
          exact fun he => hne d hd0 he.symm
        · have hlive : LiveIn rng In (k + 1) r := by
            rcases hr with h | h
            · exact absurd h hr0
            · exact h
          refine hC.interf r d k (fun he => hmem (he ▸ hd)) hr0 hd0 ⟨?_, by have := hlive.1; omega⟩
            (hC.defCov k i hk hget d hd hd0)
          rcases hlive.2 with hb | hb
          · omega
          · have := hC.inEarly r hb
            omega

/-- The set inclusion of a jump edge, from the interval conditions: a name that
    holds a value after the target label has an interval that reaches a backward
    jump, and starts before a forward jump or belongs to an input. -/
def JumpOK (body : List LinstrRM) (k0 : Nat) (rng : String → Nat × Nat)
    (In : String → Prop) : Prop :=
  ∀ k i l pc, k0 ≤ k → body[k]? = some i → jumpLabel? i.1 = some l →
    findLabelMem l body = some pc → ∀ r, LiveIn rng In (pc + 1) r →
      (pc + 1 ≤ k → k ≤ (rng r).2) ∧ (k < pc + 1 → (rng r).1 < k ∨ In r)

theorem JumpOK.sub {body : List LinstrRM} {k0 : Nat} {rng : String → Nat × Nat}
    {In : String → Prop} (hJ : JumpOK body k0 rng In) {k : Nat} {i : LinstrRM} {l : LLabel}
    {pc : Nat} (hk : k0 ≤ k) (hget : body[k]? = some i) (hl : jumpLabel? i.1 = some l)
    (hf : findLabelMem l body = some pc) :
    ∀ r, Live rng In (pc + 1) r → Live rng In k r := by
  intro r hr
  rcases hr with h | h
  · exact Or.inl h
  · obtain ⟨hback, hfwd⟩ := hJ k i l pc hk hget hl hf r h
    refine Or.inr ?_
    by_cases hle : pc + 1 ≤ k
    · refine ⟨hback hle, ?_⟩
      rcases h.2 with hb | hb
      · exact Or.inl (by omega)
      · exact Or.inr hb
    · exact ⟨by have := h.1; omega, hfwd (by omega)⟩

/-- **A liveness certificate from live ranges.** For a body and its image under
    `σ`, register intervals `rr` with inputs `InR` and array intervals `ra` with
    inputs `InA` that satisfy the interval conditions, contain every read, and
    satisfy the jump condition give a `LiveCert` on the sets `Live rr InR` and
    `Live ra InA`. Injectivity of `σ` enters through `RangeCert.interf` only:
    names with disjoint intervals may share an image. -/
theorem liveCert_of_ranges (fn : String) (body : List LinstrRM) (k0 : Nat)
    (hfix : σ "" = "") (hne : ∀ n, n ≠ "" → σ n ≠ "")
    {rr ra : String → Nat × Nat} {InR InA : String → Prop}
    (hcond : ∀ k i, k0 ≤ k → body[k]? = some i → CondOK i)
    (hjmp : ∀ l pc, findLabelMem l body = some pc → k0 ≤ pc + 1)
    (hR : RangeCert σ k0 body regDefs rr InR) (hA : RangeCert σ k0 body arrDefs ra InA)
    (huse : ∀ k i, k0 ≤ k → body[k]? = some i → ∀ n ∈ useNames i.1, Live rr InR k n)
    (harr : ∀ k i, k0 ≤ k → body[k]? = some i → ∀ b, arrUse? i = some b → Live ra InA k b)
    (hjR : JumpOK body k0 rr InR) (hjA : JumpOK body k0 ra InA) :
    LiveCert σ k0 (singletonProgM fn body) (singletonProgM fn (body.map (renRM σ)))
      (Live rr InR) (Live ra InA) where
  lfn := rfl
  lbl := fun l => findLabelMem_map_renRM l body
  body := fun k _ => by simp [singletonProgM]
  cond := hcond
  jmp := hjmp
  emp := fun _ => Or.inl rfl
  fix := hfix
  uses := huse
  arrUse := harr
  fallR := fun _ _ hk hget => hR.keeps hfix hne hk hget
  fallA := fun _ _ hk hget => hA.keeps hfix hne hk hget
  jumpR := fun _ _ _ _ hk hget hl hf => hjR.sub hk hget hl hf
  jumpA := fun _ _ _ _ hk hget hl hf => hjA.sub hk hget hl hf

/-! ## 8. The export's allocation table -/

/-- The register renaming of the export's call-free operand remap
    (`remapOperand body (physTableOut body [])`), with the empty name fixed. -/
def physSigma (body : Lcmd) (n : String) : String :=
  if n = "" then "" else physRename body (bodyPhysTable body) n

/-- With no output stores the ABI export's table is the body's class-aware table. -/
theorem physTableOut_nil (body : Lcmd) : physTableOut body [] = bodyPhysTable body := by
  simp [physTableOut, bodyTraceOut, outStoreSlots, bodyPhysTable]

theorem append_ne_empty (a b : String) (ha : a ≠ "") : a ++ b ≠ "" := by
  intro h
  have hl : (a ++ b).length = 0 := by rw [h]; rfl
  rw [String.length_append] at hl
  have : a.length = 0 := by omega
  exact ha (String.length_eq_zero_iff.mp this)

theorem physRegName_ne_empty (p : Nat) : physRegName p ≠ "" := by
  have hgp : ∀ r ∈ gpRegNames, r ≠ "" := by decide
  have hvec : ∀ r ∈ vectorRegNames, r ≠ "" := by decide
  unfold physRegName
  split
  · dsimp only
    split
    · next r hr => exact hvec r (List.mem_of_getElem? hr)
    · exact append_ne_empty _ _ (by decide)
  · split
    · next r hr => exact hgp r (List.mem_of_getElem? hr)
    · exact append_ne_empty _ _ (by decide)

theorem physSigma_fix (body : Lcmd) : physSigma body "" = "" := by simp [physSigma]

theorem physSigma_ne_empty (body : Lcmd) (n : String) (hn : n ≠ "") :
    physSigma body n ≠ "" := by
  simp only [physSigma, if_neg hn]
  exact physRegName_ne_empty _

/-- The export's operand remap is the renaming `physSigma` on operands that do not
    mention the empty name. -/
theorem remapOperand_eq_renOperand (body : Lcmd) (o : LOperand)
    (ho : ∀ n ∈ opNames o, n ≠ "") :
    remapOperand body (physTableOut body []) o = renOperand (physSigma body) o := by
  rw [physTableOut_nil]
  cases o with
  | reg r =>
      have hr : r ≠ "" := ho r (by simp [opNames])
      simp [remapOperand, renOperand, physSigma, physRename, hr]
  | arrIdx b i k =>
      have hb : b ≠ "" := ho b (by simp [opNames])
      have hi : i ≠ "" := ho i (by simp [opNames])
      simp [remapOperand, renOperand, physSigma, physRename, hb, hi]
  | _ => rfl

/-- **The linear scan is interference free against its own live ranges.** Let
    `pos` send a program counter to a position of the body's allocation trace,
    and let every interval of `rng` lie inside the scan's conservative live range
    of its name, read through `pos`. Then the export's renaming separates any two
    names whose intervals share a program counter. The separation is
    `physRename_hinj_of_liveAt`, a theorem about `physScanSpill`. -/
theorem physSigma_interf (body : Lcmd) (pos : Nat → Nat) (rng : String → Nat × Nat)
    (hfit : numGPRegs + (physLiveItems (bodyTrace body)).length ≤ vectorBase)
    (hcov : ∀ n k, n ≠ "" → Covers (rng n) k →
      n ∈ bodyNames body ∧ pos k < (bodyTrace body).length
        ∧ LiveAt (bodyTrace body) (pos k) (nameSlot body n)) :
    Interf (physSigma body) rng := by
  intro a b k hab ha hb hca hcb he
  obtain ⟨hma, hpos, hla⟩ := hcov a k ha hca
  obtain ⟨hmb, _, hlb⟩ := hcov b k hb hcb
  simp only [physSigma, if_neg ha, if_neg hb] at he
  exact hab (physRename_hinj_of_liveAt hfit hpos hma hmb hla hlb he)

/-! ### The allocated body is not a renaming of the virtual body

The physical body (`physBodyRmap`, and `physBodyWithStores` after it) lowers a
three-address binop to the two-address pair `MOV d, a ; OP d, d, b`, so it has
more instructions than the virtual body, and the linear scan gives names with
disjoint live ranges the same register. -/

/-- A binop whose destination differs from its first source lowers to at least
    two instructions, so the image of a body with such a binop is not a `map` of
    that body. -/
theorem lowerTwoAddr_length (dst s0 s1 : LOperand) (opn mov : String) (h : dst ≠ s0) :
    2 ≤ (lowerTwoAddr dst s0 s1 opn mov).length := by
  have h1 : 1 ≤ (legalizeMov dst s0 mov).length := by
    unfold legalizeMov; split <;> simp
  have h2 : ∀ s, 1 ≤ (legalizeBinop dst s opn mov).length := by
    intro s; unfold legalizeBinop; split <;> simp
  unfold lowerTwoAddr
  simp only [if_neg h, List.length_append]
  have := h2 (materializeWideImm s1 mov).2
  omega

/-- A literal body with the instruction sequence of the `mpn_and_n` runtime-count
    loop node before allocation: `LIVEPIN`, then the aliased and canonicalised
    `forLoopLcmdNRt` of an and-update. -/
def andNodeCmd : Lcmd :=
  [ ⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" [.reg "a0", .reg "a1", .reg "a2", .reg "a3"]⟩
  , ⟨0, .Lopn [.reg "a0"] "MOV:64" [.reg "a0"]⟩
  , ⟨0, .Lopn [.reg "Lidx4"] "MOV:64" [.imm 0]⟩
  , ⟨0, .Lopn [.reg "Lctr4"] "MOV:64" [.reg "a3"]⟩
  , ⟨0, .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0]⟩
  , ⟨0, .Lcond (.reg "Z") 1073741828⟩
  , ⟨0, .Llabel .internal 4⟩
  , ⟨0, .Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8]⟩
  , ⟨0, .Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a2" "Lidx4" 8]⟩
  , ⟨0, .Lopn [.reg "L4_r6"] "AND:64" [.reg "L4_r4", .reg "L4_r5"]⟩
  , ⟨0, .Lopn [.reg "L4_r7"] "SHL:0:64" [.reg "L4_r6"]⟩
  , ⟨0, .Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "Lidx4" 8, .reg "L4_r7"]⟩
  , ⟨0, .Lopn [.reg "a0"] "MOV:64" [.reg "a0"]⟩
  , ⟨0, .Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1]⟩
  , ⟨0, .Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1]⟩
  , ⟨0, .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"]⟩
  , ⟨0, .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a2"]⟩
  , ⟨0, .Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0]⟩
  , ⟨0, .Lcond (.reg "NZ") 4⟩
  , ⟨0, .Llabel .internal 1073741828⟩
  , ⟨0, .Lret⟩ ]

-- Static check on a 21-instruction literal: the linear scan places the count
-- argument `a3` and the body temporaries `L4_r4` and `L4_r7`, whose live ranges
-- are pairwise disjoint, in the one register `RSI`, and assigns no stack slot. It
-- pins the fact that the export's renaming is not injective on the node's names.
#guard (["a3", "L4_r4", "L4_r7"].map (fun n =>
    physRegName (physMapTabled (physTableOut andNodeCmd []) (nameSlot andNodeCmd n))))
  = ["RSI", "RSI", "RSI"]
#guard (bodyNames andNodeCmd).all (fun n =>
    physMapTabled (physTableOut andNodeCmd []) (nameSlot andNodeCmd n) < numGPRegs)
-- Static check on the same literal: the scan's live range of the accumulator `a0`
-- ends at trace position 10 (the feedback `MOV`), before the back-edge compare at
-- position 15, and no name is first touched after position 10. The second fact is
-- the premise of `Interf.extend` for lengthening the range of `a0` to the
-- back-edge.
#guard physLiveRange (bodyTrace andNodeCmd) (nameSlot andNodeCmd "a0") = (0, 10)
#guard (bodyTrace andNodeCmd).length = 16
#guard (bodyNames andNodeCmd).all (fun n =>
    (physLiveRange (bodyTrace andNodeCmd) (nameSlot andNodeCmd n)).1 ≤ 10)

/-- **Runs under live ranges.** The composition of `liveCert_of_ranges` and
    `lsemFuelMemF_live`: every halting run of a body is matched, with the same
    fuel, by a halting run of its image under `σ`, between states related on the
    names live at their program counters. -/
theorem lsemFuelMemF_ranges (fn : String) (body : List LinstrRM) (k0 : Nat)
    (hfix : σ "" = "") (hne : ∀ n, n ≠ "" → σ n ≠ "")
    {rr ra : String → Nat × Nat} {InR InA : String → Prop}
    (hcond : ∀ k i, k0 ≤ k → body[k]? = some i → CondOK i)
    (hjmp : ∀ l pc, findLabelMem l body = some pc → k0 ≤ pc + 1)
    (hR : RangeCert σ k0 body regDefs rr InR) (hA : RangeCert σ k0 body arrDefs ra InA)
    (huse : ∀ k i, k0 ≤ k → body[k]? = some i → ∀ n ∈ useNames i.1, Live rr InR k n)
    (harr : ∀ k i, k0 ≤ k → body[k]? = some i → ∀ b, arrUse? i = some b → Live ra InA k b)
    (hjR : JumpOK body k0 rr InR) (hjA : JumpOK body k0 ra InA)
    (fuel : Nat) {s s' t : LstateMF}
    (hrel : RelF2 σ (Live rr InR s.prog.base.lpc) (Live ra InA s.prog.base.lpc) s s')
    (hk : k0 ≤ s.prog.base.lpc)
    (hrun : lsemFuelMemF (singletonProgM fn body) fuel s = some t) :
    ∃ t', lsemFuelMemF (singletonProgM fn (body.map (renRM σ))) fuel s' = some t'
      ∧ RelF2 σ (Live rr InR t.prog.base.lpc) (Live ra InA t.prog.base.lpc) t t' :=
  lsemFuelMemF_live
    (liveCert_of_ranges fn body k0 hfix hne hcond hjmp hR hA huse harr hjR hjA) fuel hrel hk hrun

/-! ## 9. A loop with a shared register

A counted loop whose two body temporaries `t` and `v` have disjoint intervals and
the same image `RBX`. The renaming is not injective on the names of the body, so
`lsemFuelMemF_ren` does not apply; the interval conditions hold. -/

/-- `c := 2; L: t := 5; u := t + c; v := 1; c := c - v; cmp c, 0; jne L`. -/
def reuseBody : List LinstrRM :=
  [ (.Lopn [.reg "c"] (withWidthTag 64 "MOV") [.imm 2], .reg none)
  , (.Llabel .internal 7, .reg none)
  , (.Lopn [.reg "t"] (withWidthTag 64 "MOV") [.imm 5], .reg none)
  , (.Lopn [.reg "u"] (withWidthTag 64 "ADD") [.reg "t", .reg "c"], .reg none)
  , (.Lopn [.reg "v"] (withWidthTag 64 "MOV") [.imm 1], .reg none)
  , (.Lopn [.reg "c"] (withWidthTag 64 "SUB") [.reg "c", .reg "v"], .reg none)
  , (.Lopn [.reg "c"] (withWidthTag 64 "CMP") [.reg "c", .imm 0], .reg none)
  , (.Lcond (.reg "NZ") 7, .reg none) ]

/-- The renaming of `reuseBody`: `t` and `v` share `RBX`. -/
def reuseSigma (n : String) : String :=
  if n = "c" then "RAX" else if n = "t" then "RBX" else if n = "u" then "RCX"
  else if n = "v" then "RBX" else n

/-- The register intervals of `reuseBody`; the empty interval for any other name. -/
def reuseRng (n : String) : Nat × Nat :=
  if n = "c" then (0, 7) else if n = "t" then (2, 3) else if n = "u" then (3, 3)
  else if n = "v" then (4, 5) else (1, 0)

theorem reuseSigma_not_injective : reuseSigma "t" = reuseSigma "v" ∧ "t" ≠ "v" := by
  decide

theorem reuseBody_lt {k : Nat} {i : LinstrRM} (h : reuseBody[k]? = some i) : k < 8 := by
  have := (List.getElem?_eq_some_iff.mp h).1
  simpa [reuseBody] using this

theorem reuseBody_regCert :
    RangeCert reuseSigma 0 reuseBody regDefs reuseRng (fun _ => False) where
  single := by
    intro k i _ hget
    have hk := reuseBody_lt hget
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;> decide
  inEarly := fun _ h => h.elim
  defCov := by
    intro k i _ hget
    have hk := reuseBody_lt hget
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;>
      simp [regDefs, cmpArgs?, movRegArgs?, memRegDefs, storeHit?, defNames, opNames,
        withWidthTag, Covers, reuseRng]
  start := by
    intro k i n _ hget hn _ hst hlt
    have hk := reuseBody_lt hget
    unfold reuseRng at hst hlt
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;>
      split_ifs at hst hlt <;> simp_all [regDefs, cmpArgs?, movRegArgs?, memRegDefs, storeHit?,
        defNames, opNames]
  interf := by
    intro a b k hab ha hb hca hcb
    unfold Covers reuseRng at hca hcb
    unfold reuseSigma
    split_ifs at hca hcb ⊢ <;> simp_all <;> omega

/-- The array intervals of `reuseBody`: the body has no array access. -/
def reuseRngA (_ : String) : Nat × Nat := (1, 0)

theorem reuseBody_arrCert :
    RangeCert reuseSigma 0 reuseBody arrDefs reuseRngA (fun _ => False) where
  single := by
    intro k i _ hget
    have hk := reuseBody_lt hget
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;> decide
  inEarly := fun _ h => h.elim
  defCov := by
    intro k i _ hget
    have hk := reuseBody_lt hget
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;>
      simp [arrDefs, cmpArgs?, movRegArgs?, memArrDefs, storeHit?]
  start := by
    intro k i n _ _ _ _ hst hlt
    simp [reuseRngA] at hst hlt
  interf := by
    intro a b k _ _ _ hca _
    simp [Covers, reuseRngA] at hca
    omega

/-- An entry state of `reuseBody`: every register cell a zero 64-bit word. -/
def reuseInit : LstateMF :=
  { prog :=
      { base :=
          { reg := { lvm := fun _ => ⟨64, 0#64⟩ }
            larr := fun _ => ⟨64, 1, fun _ => 0#64⟩ }
        lfn := "f" } }

/-- `reuseBody` halts from `reuseInit` after two trips, with the counter at zero:
    the run hypothesis of `reuseBody_run` is satisfiable. -/
theorem reuseBody_halts :
    ∃ t, lsemFuelMemF (singletonProgM "f" reuseBody) 14 reuseInit = some t
      ∧ t.prog.base.reg.getW "c" 64 = some 0#64 ∧ t.prog.base.lpc = 8 :=
  ⟨_, rfl, rfl, rfl⟩

/-- **The shared-register loop runs under its renaming.** Every halting run of
    `reuseBody` is matched, with the same fuel, by a halting run of its image
    under `reuseSigma`, in which `t` and `v` occupy the same register. -/
theorem reuseBody_run (fn : String) (fuel : Nat) {s s' t : LstateMF}
    (hrel : RelF2 reuseSigma (Live reuseRng (fun _ => False) s.prog.base.lpc)
      (Live reuseRngA (fun _ => False) s.prog.base.lpc) s s')
    (hrun : lsemFuelMemF (singletonProgM fn reuseBody) fuel s = some t) :
    ∃ t', lsemFuelMemF (singletonProgM fn (reuseBody.map (renRM reuseSigma))) fuel s' = some t'
      ∧ RelF2 reuseSigma (Live reuseRng (fun _ => False) t.prog.base.lpc)
          (Live reuseRngA (fun _ => False) t.prog.base.lpc) t t' := by
  refine lsemFuelMemF_ranges fn reuseBody 0 (by decide) ?_ ?_ (fun _ _ _ => Nat.zero_le _)
    reuseBody_regCert reuseBody_arrCert ?_ ?_ ?_ ?_ fuel hrel (Nat.zero_le _) hrun
  · intro n hn
    unfold reuseSigma
    split_ifs <;> first | decide | exact hn
  · intro k i _ hget
    have hk := reuseBody_lt hget
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;>
      first
        | exact condOK_of_lopn1 ⟨_, _, _, rfl⟩
        | exact ⟨fun c l he => (by cases he; simp [flagCondCC?]), rfl⟩
        | exact ⟨fun c l he => (by cases he), rfl⟩
  · intro k i _ hget
    have hk := reuseBody_lt hget
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;>
      simp [useNames, opNames, Live, LiveIn, reuseRng]
  · intro k i _ hget b hb
    have hk := reuseBody_lt hget
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;> simp [arrUse?] at hb
  · intro k i l pc _ hget hl hf r hr
    have hk := reuseBody_lt hget
    interval_cases k <;> simp [reuseBody] at hget <;> subst hget <;> simp [jumpLabel?] at hl
    subst hl
    have hpc : findLabelMem 7 reuseBody = some 1 := by decide
    rw [hpc] at hf
    cases hf
    unfold LiveIn at hr
    unfold reuseRng at hr ⊢
    split_ifs at hr ⊢ <;> simp_all
  · intro k i l pc _ _ _ _ r hr
    simp [LiveIn, reuseRngA] at hr

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
