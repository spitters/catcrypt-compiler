/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CT.X86Timing
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
public import CatCrypt.Crypto.SecureCompilation.VarTimeOpDetector

/-!
# The constant-time leakage model

One observation type and one definition of constant time, instantiated here at
the machine level (`JInstr` blocks and structured `OwnedCF` blocks) and in
`CT/LowCTLeakage.lean` at the source level (`LowCT` under `RustExec`).

* `CTLeak` is the observation type: branch outcomes, memory addresses,
  the data operands of variable-time instructions, runtime trip counts, and the
  arguments of variable-time leaf calls.
* `ConstantTime pubEq leak` is the two-run property: two inputs related by
  `pubEq` (agreement on the public data) give equal leakage traces;
  `ConstantTimeRel` is the same property for a relational semantics, over runs
  that both terminate.
* `DoitRegime` is the hardware regime under which the timing table of
  `CT/X86Timing.lean` holds. Under `DoitRegime.doitm` an instruction leaks its
  data operands exactly when the table classes it variable time; under
  `DoitRegime.unguaranteed` every non-control instruction leaks them.
* `blockLeakCT r s body` is the machine leakage of a straight-line block: the
  address events of `MachineConstantTime.instrLeak` followed, per instruction, by
  a `vt` event when the regime makes the instruction's operands observable.
  `blockLeakCT_filterMap` recovers `MachineConstantTime.blockLeak` from it, and
  `cfLeakCT_filterMap` recovers `MachineConstantTime.cfExec`'s trace.
* `vopMnem` maps the abstract ops of `VarTimeOpDetector` to x86 mnemonics;
  `vop_varTime_of_mnem_varTime` states that every op the allowlist classes
  variable time is on the denylist, and `vop_vshift_mismatch` names the op on
  which the two classifications differ.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.VarTimeOpDetector (VOp)

/-! ## 1. Observations and the definition of constant time -/

/-- A leakage event. -/
inductive CTLeak where
  /-- The outcome of a conditional branch. -/
  | branch (b : Bool)
  /-- A memory access at offset `off` of the region `region`. At the machine
      level `region` is the base register name and `off` the byte offset; at
      `LowCT` it is the array variable and the element index. -/
  | addr (region : String) (off : Int)
  /-- A variable-time instruction `op` executed on the data operands `args`. -/
  | vt (op : X86Mnem) (args : List Nat)
  /-- The trip count of a loop whose bound is computed at run time. -/
  | trip (n : Nat)
  /-- A call of a leaf classed variable time, with its argument bytes. -/
  | vtCall (f : String) (args : List (List Nat))
  deriving DecidableEq, Repr

/-- Constant time for a leakage function: inputs that agree on the public data
    (`pubEq`) have equal leakage traces. -/
def ConstantTime {σ : Type} (pubEq : σ → σ → Prop) (leak : σ → List CTLeak) : Prop :=
  ∀ s₁ s₂, pubEq s₁ s₂ → leak s₁ = leak s₂

/-- Constant time for a relational semantics `run s t` (a terminating run from
    `s` with leakage trace `t`): two terminating runs from inputs that agree on
    the public data have equal traces. -/
def ConstantTimeRel {σ : Type} (pubEq : σ → σ → Prop) (run : σ → List CTLeak → Prop) :
    Prop :=
  ∀ s₁ s₂ t₁ t₂, pubEq s₁ s₂ → run s₁ t₁ → run s₂ t₂ → t₁ = t₂

/-- The functional definition is the relational one at the graph of the leakage
    function. -/
theorem constantTime_iff_rel {σ : Type} (pubEq : σ → σ → Prop) (leak : σ → List CTLeak) :
    ConstantTime pubEq leak ↔ ConstantTimeRel pubEq (fun s t => t = leak s) := by
  constructor
  · intro h s₁ s₂ t₁ t₂ hp h₁ h₂
    subst h₁ h₂
    exact h s₁ s₂ hp
  · intro h s₁ s₂ hp
    exact h s₁ s₂ _ _ hp rfl rfl

/-! ## 2. The hardware regime -/

/-- The hardware regime of a run. `doitm`: DOITM is set, or the core does not
    enumerate `IA32_UARCH_MISC_CTL`, so the Intel DOIT list applies.
    `unguaranteed`: no vendor timing guarantee holds. -/
inductive DoitRegime where
  | doitm
  | unguaranteed
  deriving DecidableEq, Repr

/-- Whether an instruction with mnemonic `m` makes its data operands observable
    under the regime. -/
def DoitRegime.leaksOperands : DoitRegime → X86Mnem → Bool
  | .doitm, m =>
      match m.timing with
      | .varTime => true
      | _ => false
  | .unguaranteed, m =>
      match m.timing with
      | .control => false
      | _ => true

theorem DoitRegime.leaksOperands_doitm_iff (m : X86Mnem) :
    DoitRegime.doitm.leaksOperands m = true ↔ m.timing = .varTime := by
  cases h : m.timing <;> simp [DoitRegime.leaksOperands, h]

/-! ## 3. Machine leakage of `JInstr` -/

/-- The data operands an instruction reads, as natural numbers: register
    values, immediates, the memory word of a memory source, and the flags it
    reads (as `0`/`1`). Memory addresses are not data operands; they are
    `addr` events. -/
def _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.JInstr.dataArgs {w : Nat}
    (s : JState w) : JInstr w → List Nat
  | .mov _ src => [(src.eval s).toNat]
  | .add d src | .sub d src | .imul d src | .and_ d src | .or_ d src | .xor_ d src
  | .shl d src | .shr d src | .sar d src | .rol d src | .ror d src =>
      [(s.get d).toNat, (src.eval s).toNat]
  | .adc d src | .sbb d src | .adcx d src =>
      [(s.get d).toNat, (src.eval s).toNat, (s.flagB (·.cf)).toNat]
  | .adox d src => [(s.get d).toNat, (src.eval s).toNat, (s.flagB (·.of)).toNat]
  | .neg d | .not_ d | .inc d | .dec d => [(s.get d).toNat]
  | .setc _ => [(s.flagB (·.cf)).toNat]
  | .test a b | .cmp a b | .testN _ a b | .bt a b => [(s.get a).toNat, (b.eval s).toNat]
  | .btr d b | .bts d b => [(s.get d).toNat, (b.eval s).toNat]
  | .andn _ a b => [(s.get a).toNat, (s.get b).toNat]
  | .rorx _ src amt => [(s.get src).toNat, (amt.eval s).toNat]
  | .shlx _ src c | .shrx _ src c | .sarx _ src c | .bzhi _ src c =>
      [(s.get src).toNat, (s.get c).toNat]
  | .movzx _ _ src | .movsx _ _ src | .imulri _ src _ => [(s.get src).toNat]
  | .lea _ base idx _ _ => [(s.get base).toNat, (s.get idx).toNat]
  | .cmove d src => [(s.flagB (·.zf)).toNat, (src.eval s).toNat, (s.get d).toNat]
  | .cmovne d src => [(s.flagB (·.zf)).toNat, (src.eval s).toNat, (s.get d).toNat]
  | .cmovb d src => [(s.flagB (·.cf)).toNat, (src.eval s).toNat, (s.get d).toNat]
  | .cmovcc c d src => [(s.condB c).toNat, (src.eval s).toNat, (s.get d).toNat]
  | .setcc c _ => [(s.condB c).toNat]
  | .mulx _ _ a b => [(a.eval s).toNat, (b.eval s).toNat]
  | .mulxMem _ _ a base off => [(a.eval s).toNat, (s.load base off).toNat]
  | .loadMem _ base off => [(s.load base off).toNat]
  | .storeMem _ _ src | .storeMemIdx _ _ _ src => [(src.eval s).toNat]
  | .loadMemIdx _ base idx scale => [(s.loadIdx base idx scale).toNat]
  | .loadSym _ _ | .clc | .stc => []
  | .xchg a b => [(s.get a).toNat, (s.get b).toNat]
  | .mul _ rax src | .imulWide _ rax src => [(s.get rax).toNat, (s.get src).toNat]
  | .shld d src amt | .shrd d src amt =>
      [(s.get d).toNat, (s.get src).toNat, (amt.eval s).toNat]
  | .rcl d amt | .rcr d amt =>
      [(s.get d).toNat, (amt.eval s).toNat, (s.flagB (·.cf)).toNat]
  | .addMem d base off | .imulMem d base off =>
      [(s.get d).toNat, (s.load base off).toNat]
  | .addToMem base off src => [(s.load base off).toNat, (src.eval s).toNat]
  | .adcxMem d base off =>
      [(s.get d).toNat, (s.load base off).toNat, (s.flagB (·.cf)).toNat]
  | .adoxMem d base off =>
      [(s.get d).toNat, (s.load base off).toNat, (s.flagB (·.of)).toNat]
  | .imulriMem _ base off _ => [(s.load base off).toNat]

/-- The embedding of `MachineConstantTime`'s events into `CTLeak`. `MLeak.branch`
    carries no outcome and maps to `branch true`. -/
def mleakToCT : MLeak → CTLeak
  | .branch => .branch true
  | .mem base off => .addr base off

/-- The projection of `CTLeak` onto `MachineConstantTime`'s events: branch and
    address events are kept (the branch outcome is forgotten); operand, trip and
    leaf events are dropped. -/
def ctToMLeak? : CTLeak → Option MLeak
  | .branch _ => some .branch
  | .addr base off => some (.mem base off)
  | _ => none

@[simp] theorem ctToMLeak?_mleakToCT (e : MLeak) : ctToMLeak? (mleakToCT e) = some e := by
  cases e <;> rfl

/-- An instruction is quiet under a regime when it does not make its data
    operands observable. -/
def Quiet {w : Nat} (r : DoitRegime) (i : JInstr w) : Prop :=
  r.leaksOperands i.mnem = false

/-- The leakage of one instruction from state `s`: its memory-address events,
    then a `vt` event with its data operands when the regime makes them
    observable. -/
def instrLeakCT {w : Nat} (r : DoitRegime) (s : JState w) (i : JInstr w) : List CTLeak :=
  (instrLeak s i).map mleakToCT ++
    (if r.leaksOperands i.mnem then [.vt i.mnem (i.dataArgs s)] else [])

/-- The leakage of a straight-line block, the state threaded by `evalInstr`. -/
def blockLeakCT {w : Nat} (r : DoitRegime) (s : JState w) : List (JInstr w) → List CTLeak
  | [] => []
  | i :: is => instrLeakCT r s i ++ blockLeakCT r (evalInstr s i) is

@[simp] theorem blockLeakCT_nil {w : Nat} (r : DoitRegime) (s : JState w) :
    blockLeakCT r s [] = [] := rfl

@[simp] theorem blockLeakCT_cons {w : Nat} (r : DoitRegime) (s : JState w) (i : JInstr w)
    (is : List (JInstr w)) :
    blockLeakCT r s (i :: is) = instrLeakCT r s i ++ blockLeakCT r (evalInstr s i) is := rfl

theorem instrLeakCT_filterMap {w : Nat} (r : DoitRegime) (s : JState w) (i : JInstr w) :
    (instrLeakCT r s i).filterMap ctToMLeak? = instrLeak s i := by
  have hcomp : (ctToMLeak? ∘ mleakToCT) = some := funext ctToMLeak?_mleakToCT
  unfold instrLeakCT
  rw [List.filterMap_append, List.filterMap_map, hcomp, List.filterMap_some]
  split <;> simp [ctToMLeak?]

/-- The address and branch events of `blockLeakCT` are `MachineConstantTime.blockLeak`. -/
theorem blockLeakCT_filterMap {w : Nat} (r : DoitRegime) (s : JState w)
    (body : List (JInstr w)) :
    (blockLeakCT r s body).filterMap ctToMLeak? = blockLeak s body := by
  induction body generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [blockLeakCT_cons, blockLeak_cons, List.filterMap_append,
      instrLeakCT_filterMap, ih]

theorem instrLeakCT_of_quiet {w : Nat} (r : DoitRegime) (s : JState w) (i : JInstr w)
    (hq : Quiet r i) : instrLeakCT r s i = (instrLeak s i).map mleakToCT := by
  unfold instrLeakCT
  unfold Quiet at hq
  simp [hq]

/-- On a block of quiet instructions `blockLeakCT` is `MachineConstantTime.blockLeak`
    with its events embedded. -/
theorem blockLeakCT_eq_map_of_quiet {w : Nat} (r : DoitRegime) (s : JState w)
    (body : List (JInstr w)) (hq : ∀ i ∈ body, Quiet r i) :
    blockLeakCT r s body = (blockLeak s body).map mleakToCT := by
  induction body generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [blockLeakCT_cons, blockLeak_cons, List.map_append]
    rw [instrLeakCT_of_quiet r s i (hq i (List.mem_cons_self ..)),
      ih (evalInstr s i) (fun j hj => hq j (List.mem_cons_of_mem i hj))]

/-- Constant time of a machine block with respect to the public registers `pub`. -/
def MachineCT {w : Nat} (r : DoitRegime) (pub : PubPred) (body : List (JInstr w)) : Prop :=
  ConstantTime (fun s₁ s₂ : JState w => agreePub pub s₁ s₂) (fun s => blockLeakCT r s body)

/-- A block of quiet, CT-addressed instructions is constant time. -/
theorem machineCT_of_ctAddressed_quiet {w : Nat} (r : DoitRegime) (pub : PubPred)
    (body : List (JInstr w)) (hbody : ∀ i ∈ body, CTAddressed pub i ∧ Quiet r i) :
    MachineCT r pub body := by
  intro s₁ s₂ hag
  have hq : ∀ i ∈ body, Quiet r i := fun i hi => (hbody i hi).2
  simp only
  rw [blockLeakCT_eq_map_of_quiet r s₁ body hq, blockLeakCT_eq_map_of_quiet r s₂ body hq,
    blockLeak_pub_determined pub body (fun i hi => (hbody i hi).1) s₁ s₂ hag]

/-- A straight-line block of data-independent instructions with direct
    addressing has the same leakage trace from any two states: the trace does
    not depend on any register, flag or memory value. -/
theorem blockLeakCT_state_independent {w : Nat} (body : List (JInstr w))
    (hbody : ∀ i ∈ body, IsDirect i ∧ i.mnem.isDataIndependent = true)
    (s₁ s₂ : JState w) :
    blockLeakCT .doitm s₁ body = blockLeakCT .doitm s₂ body := by
  have hq : ∀ i ∈ body, Quiet .doitm i := by
    intro i hi
    have h := (X86Mnem.isDataIndependent_iff _).1 (hbody i hi).2
    simp [Quiet, DoitRegime.leaksOperands, h]
  rw [blockLeakCT_eq_map_of_quiet _ s₁ body hq, blockLeakCT_eq_map_of_quiet _ s₂ body hq,
    blockLeak_state_independent body (fun i hi => (hbody i hi).1) s₁ s₂]

/-! ### 3.1 Sanity instances -/

/-- A register-only block of data-independent instructions (moves, add with
    carry, wide multiply, conditional move). -/
def regDoitBlock : List (JInstr 64) :=
  [ .mov "t" (.reg "a"), .add "t" (.reg "b"), .adc "u" (.reg "c"),
    .mulx "h" "l" (.reg "t") (.reg "u"), .cmovcc .b "h" (.reg "l") ]

/-- The leakage trace of `regDoitBlock` is empty from every state. -/
theorem regDoitBlock_leak (s : JState 64) : blockLeakCT .doitm s regDoitBlock = [] := rfl

/-- `regDoitBlock` is constant time for every public/secret split. -/
theorem regDoitBlock_ct (pub : PubPred) : MachineCT .doitm pub regDoitBlock :=
  fun s₁ s₂ _ => (regDoitBlock_leak s₁).trans (regDoitBlock_leak s₂).symm

/-- The split in which only the table base `tab` is public. -/
def tabPub : PubPred := fun r => r == "tab"

/-- The all-zero register state. -/
def zeroState : JState 64 := { regs := fun _ => 0 }

/-- The state with register `k` set to `1` and every other register `0`. -/
def kOneState : JState 64 := { regs := fun r => if r = "k" then 1 else 0 }

theorem zero_kOne_agree (pub : PubPred) (hk : pub "k" = false) :
    agreePub pub zeroState kOneState := by
  intro r hr
  have : r ≠ "k" := by rintro rfl; rw [hk] at hr; cases hr
  simp [zeroState, kOneState, JState.get, this]

/-- A load from the table `tab` at the secret index register `k` is not
    constant time: the two runs access `tab + 0` and `tab + 8`. -/
theorem secretIndexedLoad_not_ct :
    ¬ MachineCT .doitm tabPub [JInstr.loadMemIdx (w := 64) "x" "tab" "k" 8] := by
  intro h
  have := h zeroState kOneState (zero_kOne_agree tabPub rfl)
  simp [blockLeakCT, instrLeakCT, instrLeak, zeroState, kOneState, JState.get,
    mleakToCT] at this

/-- `sarx` with a secret count is not constant time: it is variable time under
    the allowlist, and its `vt` event carries the count. -/
theorem sarx_secret_not_ct :
    ¬ MachineCT .doitm (fun _ => false) [JInstr.sarx (w := 64) "y" "a" "k"] := by
  intro h
  have := h zeroState kOneState (zero_kOne_agree _ rfl)
  simp [blockLeakCT, instrLeakCT, instrLeak, JInstr.dataArgs, JInstr.mnem,
    DoitRegime.leaksOperands, X86Mnem.timing, zeroState, kOneState, JState.get] at this

/-- `shrx` with a secret count is constant time under DOITM. -/
theorem shrx_secret_ct (pub : PubPred) :
    MachineCT .doitm pub [JInstr.shrx (w := 64) "y" "a" "k"] :=
  fun _ _ _ => rfl

/-- Without the DOITM regime an `add` on secret operands is not constant time:
    the regime hypothesis is used. -/
theorem add_secret_not_ct_unguaranteed :
    ¬ MachineCT .unguaranteed (fun _ => false) [JInstr.add (w := 64) "a" (.reg "k")] := by
  intro h
  have := h zeroState kOneState (zero_kOne_agree _ rfl)
  simp [blockLeakCT, instrLeakCT, instrLeak, JInstr.dataArgs, JInstr.mnem,
    DoitRegime.leaksOperands, X86Mnem.timing, zeroState, kOneState, JState.get] at this

/-! ## 4. Machine leakage of structured control flow -/

/-- The leakage of `n` iterations of a step with leakage `f` and successor
    state `step`. -/
def iterLeak {σ : Type} (f : σ → List CTLeak) (step : σ → σ) : Nat → σ → List CTLeak
  | 0, _ => []
  | n + 1, s => f s ++ iterLeak f step n (step s)

/-- The leakage of a structured owned block: straight-line leaves by
    `blockLeakCT`, a conditional by the branch outcome followed by the taken arm,
    a counted loop by its iterations. States are threaded by
    `MachineConstantTime.cfExec`. -/
def cfLeakCT (r : DoitRegime) {w : Nat} : JState w → OwnedCF w → List CTLeak
  | s, .straight body => blockLeakCT r s body
  | s, .seq a b => cfLeakCT r s a ++ cfLeakCT r (cfExec s a).2 b
  | s, .loop n body =>
      iterLeak (fun s' => cfLeakCT r s' body) (fun s' => (cfExec s' body).2) n s
  | s, .ifPub guard thenB elseB =>
      if s.get guard = 0 then .branch false :: cfLeakCT r s elseB
      else .branch true :: cfLeakCT r s thenB

/-- Every straight-line leaf of a structured block is quiet. -/
def CFQuiet (r : DoitRegime) {w : Nat} : OwnedCF w → Prop
  | .straight body => ∀ i ∈ body, Quiet r i
  | .seq a b => CFQuiet r a ∧ CFQuiet r b
  | .loop _ body => CFQuiet r body
  | .ifPub _ thenB elseB => CFQuiet r thenB ∧ CFQuiet r elseB

/-- The address and branch events of `cfLeakCT` are `MachineConstantTime.cfExec`'s
    trace. -/
theorem cfLeakCT_filterMap (r : DoitRegime) {w : Nat} (cf : OwnedCF w) (s : JState w) :
    (cfLeakCT r s cf).filterMap ctToMLeak? = (cfExec s cf).1 := by
  induction cf generalizing s with
  | straight body =>
    simp only [cfLeakCT, cfExec, blockLeakCT_filterMap]
  | seq a b iha ihb =>
    simp only [cfLeakCT, cfExec, List.filterMap_append, iha, ihb]
  | loop n body ih =>
    simp only [cfLeakCT, cfExec]
    induction n generalizing s with
    | zero => simp only [iterLeak, cfLoop, List.filterMap_nil]
    | succ m ihm => simp only [iterLeak, cfLoop, List.filterMap_append, ih, ihm]
  | ifPub guard thenB elseB iht ihe =>
    by_cases hz : s.get guard = 0
    · simp only [cfLeakCT, cfExec, if_pos hz, List.filterMap_cons, ctToMLeak?, ihe]
    · simp only [cfLeakCT, cfExec, if_neg hz, List.filterMap_cons, ctToMLeak?, iht]

/-- Constant time over structured control flow: a CT-controlled block
    (`MachineConstantTime.CFControlled`: public guards, public index registers,
    public registers not overwritten) whose leaves are quiet has the same
    leakage trace from any two states agreeing on the public registers. -/
theorem owned_ct_control_flow_CT (r : DoitRegime) (pub : PubPred) {w : Nat} (cf : OwnedCF w)
    (hcf : CFControlled pub cf) (hq : CFQuiet r cf) :
    ConstantTime (fun s₁ s₂ : JState w => agreePub pub s₁ s₂) (fun s => cfLeakCT r s cf) := by
  induction cf with
  | straight body =>
    intro s₁ s₂ hag
    exact machineCT_of_ctAddressed_quiet r pub body (fun i hi => ⟨hcf i hi, hq i hi⟩) s₁ s₂ hag
  | seq a b iha ihb =>
    intro s₁ s₂ hag
    have hpost := (cfExec_pub_determined pub a hcf.1 s₁ s₂ hag).2
    exact congrArg₂ (· ++ ·) (iha hcf.1 hq.1 s₁ s₂ hag) (ihb hcf.2 hq.2 _ _ hpost)
  | loop n body ih =>
    have hcb : CFControlled pub body := hcf
    have hqb : CFQuiet r body := hq
    simp only [cfLeakCT]
    induction n with
    | zero => intro _ _ _; rfl
    | succ m ihm =>
      intro s₁ s₂ hag
      have hpost := (cfExec_pub_determined pub body hcb s₁ s₂ hag).2
      exact congrArg₂ (· ++ ·) (ih hcb hqb s₁ s₂ hag) (ihm hcb hqb _ _ hpost)
  | ifPub guard thenB elseB iht ihe =>
    intro s₁ s₂ hag
    obtain ⟨hg, hct, hce⟩ := hcf
    have hgeq : s₁.get guard = s₂.get guard := hag guard hg
    by_cases hz : s₁.get guard = 0
    · have hz2 : s₂.get guard = 0 := by rw [← hgeq]; exact hz
      simp only [cfLeakCT, if_pos hz, if_pos hz2]
      exact congrArg (List.cons _) (ihe hce hq.2 s₁ s₂ hag)
    · have hz2 : ¬ s₂.get guard = 0 := by rw [← hgeq]; exact hz
      simp only [cfLeakCT, if_neg hz, if_neg hz2]
      exact congrArg (List.cons _) (iht hct hq.1 s₁ s₂ hag)

/-! ## 5. The denylist of `VarTimeOpDetector` against the allowlist -/

/-- The x86 mnemonic an abstract op of `VarTimeOpDetector` lowers to: `mul` to
    `IMUL`, a constant shift to `SHL`, a variable shift to `SHLX`, division and
    remainder to `DIV`. The early-exit ops have no x86 instruction. -/
def vopMnem : VOp → Option X86Mnem
  | .add => some .add
  | .mul => some .imul
  | .xorOp => some .xor
  | .andOp => some .and
  | .shiftConst => some .shl
  | .div => some .div
  | .mod => some .div
  | .vshift => some .shlx
  | .mulEarlyExit => none
  | .cmpEarlyExit => none

/-- Every op whose x86 mnemonic the allowlist classes variable time is on the
    denylist `VOp.varTime`. -/
theorem vop_varTime_of_mnem_varTime (op : VOp) (m : X86Mnem) (h : vopMnem op = some m)
    (hm : m.timing = .varTime) : op.varTime = true := by
  cases op <;> simp only [vopMnem, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | rfl | simp [X86Mnem.timing] at hm

/-- Every op off the denylist lowers to a data-independent x86 mnemonic. -/
theorem vop_mnem_doit_of_not_varTime (op : VOp) (h : op.varTime = false) :
    ∃ m, vopMnem op = some m ∧ m.timing = .doit := by
  cases op <;> first | exact ⟨_, rfl, rfl⟩ | simp at h

/-- The classifications differ at the variable shift: the denylist classes it
    variable time, the allowlist classes its x86 form `SHLX` data independent. -/
theorem vop_vshift_mismatch :
    VOp.varTime .vshift = true ∧ vopMnem .vshift = some .shlx ∧ X86Mnem.timing .shlx = .doit :=
  ⟨rfl, rfl, rfl⟩

/-- The denylist names no op lowering to the variable-time `SARX` or `BZHI`. -/
theorem vopMnem_ne_sarx_bzhi (op : VOp) : vopMnem op ≠ some .sarx ∧ vopMnem op ≠ some .bzhi := by
  cases op <;> simp [vopMnem]

end CatCrypt.Crypto.SecureCompilation.CT
