/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrCtLower

/-!
# Constant-time blocks with a known index register

`ConstantTimeCoverage.allDirect_constant_time` gives the machine leakage trace of
a straight-line `List (JInstr 64)` block as a function of the program text when
every instruction addresses memory through a base register and a compile-time
displacement. A register-indexed access is outside that class even when its index
register holds a value fixed by the program text.

This module widens the class: an indexed access whose index register holds a
value recorded in a known-value environment emits the same effective address
from every state satisfying the environment, so a block mixing direct accesses
with indexed accesses at known indices still has a state-independent leakage
trace. The environment is `ConstIndexFold.KEnv`, carried across an instruction by
the register-preservation check `keepsReg`.

The index condition is what the class turns on:
`MachineConstantTime.nonCT_storeMemIdx_leaks_value` exhibits a register-indexed
store whose leakage differs between two states disagreeing on the index
register, so an indexed access at an index the environment does not know is
rejected rather than admitted.

The shape the class is cut for is the prime-IR constant-time field select
`CompileFromHaxPrimeIrCtLower.ctSelectFusedLprog`, whose four output stores are
register-indexed through an index register written by an immediate `mov`, with a
compare and a conditional move between the `mov` and the store.

## Main results

* `keepsReg`, `get_evalInstr_of_keepsReg`: the decidable check that an
  instruction writes no register named `r`, and its semantic reading.
* `stepKeep`, `holds_stepKeep`: the known-value environment after one
  instruction, and its soundness against `evalInstr`.
* `idxOK`, `scanCT`: the decidable class check on a block — every instruction is
  direct, or is indexed through a register the environment knows.
* `blockLeak_state_independent_of_scanCT`: a block passing `scanCT` has the same
  `MachineConstantTime.blockLeak` trace from any two initial states satisfying
  the environment; `blockLeak_constant_time_of_scanCT` is the statement at the
  empty environment, where the two states are unconstrained.
* `scanCT_of_allDirect`: the check subsumes `ConstantTimeCoverage.allDirect`.
* `ctSelectBody`, `ctSelectGather`, `ctSelectScanOK`: the `Lcmd` body of the
  exported prime-IR field select, its `JInstr` gather, and the class check on it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CtSelectLeak

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold (KEnv gatherPrinted)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrCtLower (ctSelectFusedLprog)

/-! ## 1. Registers an instruction leaves unchanged -/

/-- `keepsReg r i` is `true` only when instruction `i` writes no register named
    `r`: the flag-only and memory-store ops keep every register, a
    single-destination op keeps every register but its destination, and a
    two-destination op keeps every register but its two. An instruction outside
    these shapes is reported as possibly writing `r`. -/
def keepsReg (r : String) : JInstr 64 → Bool
  | .cmp _ _ | .test _ _ | .testN _ _ _ | .bt _ _ | .clc | .stc
  | .storeMem _ _ _ | .storeMemIdx _ _ _ _ | .addToMem _ _ _ | .cmpMem _ _ _ => true
  | .mov d _ | .add d _ | .sub d _ | .adc d _ | .sbb d _ | .imul d _ | .neg d
  | .setc d | .and_ d _ | .not_ d | .andn d _ _ | .rol d _ | .ror d _
  | .rorx d _ _ | .shlx d _ _ | .shrx d _ _ | .sarx d _ _ | .movzx d _ _
  | .movsx d _ _ | .lea d _ _ _ _ | .or_ d _ | .xor_ d _ | .shl d _ | .shr d _
  | .sar d _ | .cmove d _ | .cmovne d _ | .cmovb d _ | .adcx d _ | .adox d _
  | .loadMem d _ _ | .loadMemIdx d _ _ _ | .loadSym d _ | .inc d | .dec d
  | .imulri d _ _ | .shld d _ _ | .shrd d _ _ | .rcl d _ | .rcr d _
  | .btr d _ | .bts d _ | .addMem d _ _ | .adcxMem d _ _ | .adoxMem d _ _
  | .imulMem d _ _ | .imulriMem d _ _ _ | .bzhi d _ _
  | .aluMem _ d _ _ | .andnMem d _ _ _ => r != d
  | .cmovcc _ d _ | .cmovccMem _ d _ _ | .setcc _ d => r != d
  | .mulx d₁ d₂ _ _ | .mulxMem d₁ d₂ _ _ _ | .mul d₁ d₂ _ | .imulWide d₁ d₂ _
  | .xchg d₁ d₂ => r != d₁ && r != d₂

/-- A register an instruction keeps holds the same value after the instruction
    as before it. -/
theorem get_evalInstr_of_keepsReg {r : String} {i : JInstr 64}
    (h : keepsReg r i = true) (s : JState 64) :
    (evalInstr s i).get r = s.get r := by
  cases i <;> simp only [keepsReg, bne_iff_ne, ne_eq, Bool.and_eq_true] at h <;>
    simp_all [evalInstr, JState.setReg, JState.setRegMerge, JState.writeB5W, JState.writeB2W,
      JState.writeB4W, JState.writeB5W2, JState.writeCFW, JState.writeB5,
      JState.writeB5N, JState.writeB5Mem, JState.store, JState.storeIdx,
      JState.get]

/-! ## 2. The known-value environment across an instruction -/

/-- A lookup in an environment filtered by a predicate on register names is a
    lookup in the environment, and its name passes the predicate. -/
theorem find_filterKey (q : String → Bool) :
    ∀ (env : KEnv) (r : String) (v : BitVec 64),
      KEnv.find (env.filter (fun p => q p.1)) r = some v →
        KEnv.find env r = some v ∧ q r = true := by
  intro env
  induction env with
  | nil => intro r v h; simp [KEnv.find] at h
  | cons e t ih =>
      intro r v h
      obtain ⟨er, ev⟩ := e
      by_cases hq : q er = true
      · rw [List.filter_cons_of_pos (by simpa using hq)] at h
        by_cases hr : er = r
        · subst hr
          simp [KEnv.find] at h
          subst h
          exact ⟨by simp [KEnv.find], hq⟩
        · simp only [KEnv.find, ite_eq_right hr] at h
          exact ⟨by simp [KEnv.find, hr, (ih r v h).1], (ih r v h).2⟩
      · rw [List.filter_cons_of_neg (by simpa using hq)] at h
        by_cases hr : er = r
        · subst hr; exact absurd (ih er v h).2 hq
        · exact ⟨by simp [KEnv.find, hr, (ih r v h).1], (ih r v h).2⟩

/-- The known-value environment after one instruction: the entries whose
    registers the instruction keeps, together with the constant an immediate
    `mov` writes. -/
def stepKeep (env : KEnv) (i : JInstr 64) : KEnv :=
  let kept := env.filter (fun p => keepsReg p.1 i)
  match i with
  | .mov d (.imm k) => (d, BitVec.ofNat 64 k) :: kept
  | _ => kept

/-- The environment after an instruction holds in the state after it. -/
theorem holds_stepKeep {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (i : JInstr 64) : KEnv.Holds (evalInstr s i) (stepKeep env i) := by
  have hkept : KEnv.Holds (evalInstr s i) (env.filter (fun p => keepsReg p.1 i)) := by
    intro r v hr
    obtain ⟨hmem, hk⟩ := find_filterKey (fun x => keepsReg x i) env r v hr
    show (evalInstr s i).get r = v
    rw [get_evalInstr_of_keepsReg hk s]
    exact h r v hmem
  unfold stepKeep
  match i with
  | .mov d (.imm k) =>
      intro r v hr
      by_cases hd : d = r
      · subst hd
        simp [KEnv.find] at hr
        subst hr
        simp [evalInstr, JOperand.eval, JState.setReg, x86_MOV]
      · simp only [KEnv.find, ite_eq_right hd] at hr
        exact hkept r v hr
  | .mov _ (.reg _) | .add _ _ | .sub _ _ | .adc _ _ | .sbb _ _ | .imul _ _
  | .neg _ | .setc _ | .and_ _ _ | .test _ _ | .cmp _ _ | .not_ _ | .andn _ _ _
  | .rol _ _ | .ror _ _ | .rorx _ _ _ | .shlx _ _ _ | .shrx _ _ _ | .sarx _ _ _
  | .movzx _ _ _ | .movsx _ _ _ | .lea _ _ _ _ _ | .or_ _ _ | .xor_ _ _
  | .shl _ _ | .shr _ _ | .sar _ _ | .cmove _ _ | .cmovne _ _ | .cmovb _ _
  | .mulx _ _ _ _ | .mulxMem _ _ _ _ _ | .adcx _ _ | .adox _ _ | .loadMem _ _ _
  | .storeMem _ _ _ | .loadMemIdx _ _ _ _ | .storeMemIdx _ _ _ _ | .loadSym _ _
  | .inc _ | .dec _ | .clc | .stc | .xchg _ _ | .imulri _ _ _ | .mul _ _ _
  | .imulWide _ _ _ | .shld _ _ _ | .shrd _ _ _ | .rcl _ _ | .rcr _ _
  | .cmovcc _ _ _ | .setcc _ _ | .testN _ _ _ | .bt _ _ | .btr _ _ | .bts _ _
  | .addMem _ _ _ | .addToMem _ _ _ | .adcxMem _ _ _ | .adoxMem _ _ _
  | .imulMem _ _ _ | .imulriMem _ _ _ _ | .cmpMem _ _ _ | .cmovccMem _ _ _ _
  | .bzhi _ _ _ | .aluMem _ _ _ _ | .andnMem _ _ _ _ => exact hkept

/-! ## 3. The class check and the leakage theorem -/

/-- An instruction is in the class under `env` when it is direct, or is a
    register-indexed access whose index register `env` knows. -/
def idxOK (env : KEnv) : JInstr 64 → Bool
  | .loadMemIdx _ _ idx _ => (KEnv.find env idx).isSome
  | .storeMemIdx _ idx _ _ => (KEnv.find env idx).isSome
  | i => decide (IsDirect i)

/-- The class check on a block: every instruction is in the class under the
    environment reaching it. -/
def scanCT (env : KEnv) : List (JInstr 64) → Bool
  | [] => true
  | i :: is => idxOK env i && scanCT (stepKeep env i) is

/-- An instruction in the class under an environment leaks the same events from
    any two states satisfying that environment. -/
theorem instrLeak_eq_of_idxOK {env : KEnv} {i : JInstr 64} (h : idxOK env i = true)
    {s₁ s₂ : JState 64} (h₁ : KEnv.Holds s₁ env) (h₂ : KEnv.Holds s₂ env) :
    instrLeak s₁ i = instrLeak s₂ i := by
  match i with
  | .loadMemIdx d b idx sc =>
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (by simpa [idxOK] using h)
      simp only [instrLeak]
      rw [show s₁.get idx = v from h₁ idx v hv, show s₂.get idx = v from h₂ idx v hv]
  | .storeMemIdx b idx sc v =>
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (by simpa [idxOK] using h)
      simp only [instrLeak]
      rw [show s₁.get idx = u from h₁ idx u hu, show s₂.get idx = u from h₂ idx u hu]
  | .mov _ _ | .add _ _ | .sub _ _ | .adc _ _ | .sbb _ _ | .imul _ _
  | .neg _ | .setc _ | .and_ _ _ | .test _ _ | .cmp _ _ | .not_ _ | .andn _ _ _
  | .rol _ _ | .ror _ _ | .rorx _ _ _ | .shlx _ _ _ | .shrx _ _ _ | .sarx _ _ _
  | .movzx _ _ _ | .movsx _ _ _ | .lea _ _ _ _ _ | .or_ _ _ | .xor_ _ _
  | .shl _ _ | .shr _ _ | .sar _ _ | .cmove _ _ | .cmovne _ _ | .cmovb _ _
  | .mulx _ _ _ _ | .mulxMem _ _ _ _ _ | .adcx _ _ | .adox _ _ | .loadMem _ _ _
  | .storeMem _ _ _ | .loadSym _ _
  | .inc _ | .dec _ | .clc | .stc | .xchg _ _ | .imulri _ _ _ | .mul _ _ _
  | .imulWide _ _ _ | .shld _ _ _ | .shrd _ _ _ | .rcl _ _ | .rcr _ _
  | .cmovcc _ _ _ | .setcc _ _ | .testN _ _ _ | .bt _ _ | .btr _ _ | .bts _ _
  | .addMem _ _ _ | .addToMem _ _ _ | .adcxMem _ _ _ | .adoxMem _ _ _
  | .imulMem _ _ _ | .imulriMem _ _ _ _ | .cmpMem _ _ _ | .cmovccMem _ _ _ _ | .bzhi _ _ _
  | .aluMem _ _ _ _ | .andnMem _ _ _ _ =>
      exact instrLeak_state_independent _ (by simpa [idxOK] using h) s₁ s₂

/-- **The leakage trace of a block in the class is state-independent.** A
    straight-line block each of whose instructions is direct or is indexed
    through a register whose value the environment records produces the same
    machine leakage trace — control-flow decisions and memory-access addresses —
    from any two initial states satisfying the environment. Under the empty
    environment the two states are unconstrained: they may differ in every
    register and every memory cell. -/
theorem blockLeak_state_independent_of_scanCT :
    ∀ (body : List (JInstr 64)) (env : KEnv), scanCT env body = true →
      ∀ s₁ s₂ : JState 64, KEnv.Holds s₁ env → KEnv.Holds s₂ env →
        blockLeak s₁ body = blockLeak s₂ body := by
  intro body
  induction body with
  | nil => intro _ _ _ _ _ _; rfl
  | cons i is ih =>
      intro env h s₁ s₂ h₁ h₂
      simp only [scanCT, Bool.and_eq_true] at h
      simp only [blockLeak_cons]
      rw [instrLeak_eq_of_idxOK h.1 h₁ h₂]
      exact congrArg _ (ih (stepKeep env i) h.2 _ _ (holds_stepKeep h₁ i) (holds_stepKeep h₂ i))

/-- The class check subsumes `ConstantTimeCoverage.allDirect`: a block with no
    register-indexed access is in the class under every environment. -/
theorem scanCT_of_allDirect :
    ∀ (body : List (JInstr 64)) (env : KEnv), allDirect body = true →
      scanCT env body = true := by
  intro body
  induction body with
  | nil => intro _ _; rfl
  | cons i is ih =>
      intro env h
      simp only [allDirect, List.all_cons, Bool.and_eq_true] at h
      have h2 : allDirect is = true := by simpa [allDirect] using h.2
      have hd : IsDirect i := of_decide_eq_true h.1
      have hi : idxOK env i = true := by
        cases i <;> first
          | exact decide_eq_true hd
          | simp only [IsDirect] at hd
      simp only [scanCT, hi, Bool.true_and]
      exact ih (stepKeep env i) h2

/-! ## 4. The empty environment and the prime-IR select -/

/-- **A block in the class has a state-independent leakage trace.** At the empty
    environment the two initial states are unconstrained: they may differ in
    every register — in particular in the register holding a select's condition —
    and in every memory cell, in particular in the two operand buffers of a
    select. The statement covers a `JInstr` block, not the rendered AT&T text and
    not the encoded bytes. -/
theorem blockLeak_constant_time_of_scanCT (g : List (JInstr 64))
    (hs : scanCT [] g = true) (s₁ s₂ : JState 64) :
    blockLeak s₁ g = blockLeak s₂ g :=
  blockLeak_state_independent_of_scanCT g [] hs s₁ s₂
    (KEnv.Holds.nil s₁) (KEnv.Holds.nil s₂)

/-- The `Lcmd` body of the exported and optimized prime-IR constant-time field
    select. -/
def ctSelectBody : Lcmd :=
  match ctSelectFusedLprog "primeir_ct_select_x86_from_lean" with
  | some lp => (lp.lp_funcs.map (fun f => f.2.lfd_body)).flatten
  | none => []

/-- The `JInstr` gather of `ctSelectBody`, the block
    `MachineConstantTime.blockLeak` is stated over. The gather is defined on the
    instruction forms `ConstIndexFold.lowerPrinted` lowers; the compare and
    conditional-move forms of the select's output are outside them. -/
def ctSelectGather : Option (List (JInstr 64)) := gatherPrinted ctSelectBody

/-- The class check on the gathered select. -/
def ctSelectScanOK : Bool :=
  match ctSelectGather with
  | some g => scanCT [] g
  | none => false

end CatCrypt.Crypto.SecureCompilation.CtSelectLeak
