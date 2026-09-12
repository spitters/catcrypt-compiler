/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SpeculativeCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTMachine

/-!
# Speculative constant-time from the `LowCT` source to the emitted `JInstr` block

Two speculative leakage models exist in the pipeline. `SpeculativeCT` runs over the
source instruction stream `LowCT`: its observation alphabet `Obs` is a sequence of
`(slot name, runtime value)` events, and a branch contributes the wrong arm's
observations truncated to a speculation window followed by `Obs.rollback`.
`SpeculativeCTMachine` runs over the emitted straight-line block `List (JInstr 64)`:
its observation alphabet `MLeak` is `branch` and `mem base off`, and a load may be
forwarded a stale value out of a store buffer.

This module relates them: it defines the observation-refinement map between the two
alphabets, states the leakage-refinement obligation a compilation must discharge for
speculative constant-time to transfer, and reduces speculative constant-time of the
emitted block to that obligation together with source speculative constant-time.

## The control-flow shape of the emitted block

`Com` (`VIR/Core.lean`) has two constructors, `ret` and `var`, so the IR the export
`Com.toLprogPhysAbi` consumes carries no conditional. Conditionals live in `ComR`
(`VIR/Regions.lean`) as `ifBit`, and a `Secret`-tagged `ifBit` over `.bit` or
`.sword n` is rewritten to the branch-free chains `Transforms.cmovBit` /
`Transforms.cmovSword`.

At the `Lprog` level the gather `GatherImmForms.gatherJBlock6` maps every non-`Lret`
instruction through `lowerCov6`, whose innermost fall-through
(`LoweringExtended.lowerLinstrExt`) returns `none` on every non-`Lopn` shape.
`gatherJBlock6_no_control_transfer` reads that off: a body containing `Lcond`,
`Lgoto`, `Ligoto`, `Lcall`, `Llabel`, `LstoreLabel` or `Lsyscall` does not gather.
At the `JInstr` level `MachineConstantTime.instrLeak` emits only `MLeak.mem`, so
`specBlockLeak_no_branch` holds: a gathered block's speculative trace contains no
`MLeak.branch`.

`source_branch_not_refined` combines the two: under the slot-map refinement
`refineTrace`, which sends `Obs.branch` to `[MLeak.branch]`, a source command whose
speculative trace contains a branch observation has no gathered block satisfying the
refinement obligation. The refinement a branch-free lowering induces is
`refineTraceCmov`, which sends `Obs.branch`, `Obs.indirectTarget` and
`Obs.retTarget` to `[]`.

## The reduction

`machineSCT_of_sourceSCT`: given a refinement `ρ` for which the compilation
satisfies `LeakRefines`, source `SpeculativelyConstantTime` gives machine
`MachineSCT` on the states the source relation `R` connects. The whole content of a
preservation claim therefore sits in `LeakRefines`, which is where the register
allocator's slot placement enters.

## Scope

`leakRefines_of_allDirect` discharges `LeakRefines` on the direct-addressing
fragment with the constant refinement, because on that fragment
`SpeculativeCTMachine.specBlockLeak_state_independent` makes the machine trace
independent of the machine state; the source hypothesis is not used there.
`sct_source_to_machine_direct` and `sct_source_to_toLprogPhysAbi` record both halves
against the deployed export.

`slotMap_refinement_fails` shows the slot-map refinement `refineTrace` is not
satisfiable by a compilation that issues memory accesses of its own: a source
command with an empty speculative trace refines to the empty machine trace, while a
spill/reload block leaks at the frame address. A refinement covering a spilling
allocation therefore has to account for allocator-introduced traffic that no source
observation names.

No general `LeakRefines` instance is established here, for any source-to-machine
compilation that places source slots in registers and spill slots.

The machine speculative model covers the fragment on which `gatherJBlock6`
succeeds. `LprogBytes.encodeLinstrR` encodes `Lcond` and `Lgoto` to `jcc`/`jmp`,
so a body with a public-guard conditional or a loop back-edge reaches bytes while
lying outside `specBlockLeak`. Architecturally that fragment is covered by
`MachineConstantTime.cfExec` over `OwnedCF`, whose `ifPub` guard `CFControlled`
requires public; there is no speculative model over `OwnedCF`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTPreservation

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.SpeculativeCT
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTMachine
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
  (gatherJBlock6 lowerCov6 lowerCov6L)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation (lcmdDirect)

/-! ## 1. The emitted block carries no branch site -/

/-- No instruction of the emitted subset produces a control-flow leakage event:
    `instrLeak` yields either `[]` or a single `MLeak.mem`. -/
theorem instrLeak_no_branch {w : Nat} (s : JState w) (i : JInstr w) :
    MLeak.branch ∉ instrLeak s i := by
  cases i <;> simp [instrLeak]

/-- The architectural leakage trace of a straight-line block contains no
    control-flow event. -/
theorem blockLeak_no_branch {w : Nat} (s : JState w) (body : List (JInstr w)) :
    MLeak.branch ∉ blockLeak s body := by
  induction body generalizing s with
  | nil => simp
  | cons i is ih =>
    simp only [blockLeak_cons, List.mem_append, not_or]
    exact ⟨instrLeak_no_branch s i, ih _⟩

/-- The speculative leakage trace of a straight-line block contains no control-flow
    event, for every window and every store-bypass predictor. -/
theorem specBlockLeak_no_branch {w : Nat} (O : BypassOracle w) (σ : SpecState w)
    (body : List (JInstr w)) : MLeak.branch ∉ specBlockLeak O σ body := by
  induction body generalizing σ with
  | nil => simp
  | cons i is ih =>
    simp only [specBlockLeak_cons, List.mem_append, not_or]
    exact ⟨instrLeak_no_branch σ.arch i, ih (specStep O σ i)⟩

/-! ## 2. The gather rejects control transfer -/

/-- The `Lprog` instructions that transfer control or leave the straight-line
    subset: the conditional and unconditional jumps, the indirect jump, the call,
    the label forms and the syscall. -/
def isControlTransfer : LinstrR → Bool
  | .Lcond _ _ => true
  | .Lgoto _ => true
  | .Ligoto _ => true
  | .Lcall _ _ => true
  | .Llabel _ _ => true
  | .LstoreLabel _ _ => true
  | .Lsyscall _ => true
  | _ => false

/-- The whole-body lowering has no arm for a control-transfer instruction. -/
theorem lowerCov6_of_controlTransfer (frame spillW : Nat) {i : LinstrR}
    (h : isControlTransfer i = true) : lowerCov6 frame spillW i = none := by
  cases i <;> first | rfl | simp [isControlTransfer] at h

/-- A successful `Option`-valued `mapM` succeeds on every element. -/
theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ x ∈ l, ∃ y, f x = some y := by
  intro l
  induction l with
  | nil => intro _ _ x hx; simp at hx
  | cons a t ih =>
    intro r h x hx
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp only [hfa] at h; simp at h
    | some b =>
      cases hmt : t.mapM f with
      | none => simp only [hfa, hmt] at h; simp at h
      | some bs =>
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨b, hfa⟩
        · exact ih hmt x hx'

/-- **A gathered body contains no control transfer.** The whole-body gather maps
    every instruction other than the terminating `Lret` through `lowerCov6`, which
    has no arm for a jump, a call, a label or a syscall, so a body carrying one of
    those gathers to `none`. -/
theorem gatherJBlock6_no_control_transfer {body : Lcmd} {g : List (JInstr 64)}
    (h : gatherJBlock6 body = some g) (i : Linstr) (hi : i ∈ body) :
    isControlTransfer i.li_i = false := by
  simp only [gatherJBlock6, Option.map_eq_some_iff] at h
  obtain ⟨ls, hls, -⟩ := h
  by_contra hc
  have hct : isControlTransfer i.li_i = true := by
    cases hb : isControlTransfer i.li_i
    · exact absurd hb hc
    · rfl
  have hnr : isLret i = false := by
    have key : ∀ r : LinstrR, isControlTransfer r = true →
        (match r with | .Lret => true | _ => false) = false := by
      intro r hr; cases r <;> simp_all [isControlTransfer]
    simpa [isLret] using! key i.li_i hct
  have hmem : i ∈ body.filter (fun j => !isLret j) := by
    rw [List.mem_filter]
    exact ⟨hi, by simp [hnr]⟩
  obtain ⟨js, hjs⟩ := mapM_some_mem hls i hmem
  rw [lowerCov6L, lowerCov6_of_controlTransfer _ _ hct] at hjs
  simp at hjs

/-! ## 3. Refining source observations to machine leakage

A source observation names a `LowCT` slot and carries its runtime value. A machine
leakage event names a base register and an effective displacement. A refinement map
therefore needs the compilation's placement of each source slot: the base register
holding the object the slot indexes into, and the element scale, so that a source
`memIdx s v` refines to the machine `mem base (scale * v)` that
`MachineConstantTime.instrLeak` records for a register-indexed access. -/

/-- Where a compilation placed the object a source index slot addresses: the base
    register and the element scale of the indexed access. -/
structure Placement where
  /-- The base register of the machine access. -/
  base : String
  /-- The element scale of the machine access. -/
  scale : Nat

/-- The placement a compilation chose for each source slot; `none` for a slot with
    no machine memory access. -/
abbrev SlotMap := String → Option Placement

/-- The machine leakage a single source observation refines to when a source branch
    is compiled to a machine branch. A memory-index observation refines to the
    access at the placed base and the scaled runtime index; a rollback marker has no
    machine counterpart. -/
def refineObs (m : SlotMap) : Obs → List MLeak
  | .branch _ _ => [MLeak.branch]
  | .memIdx s v => (m s).elim [] fun p => [MLeak.mem p.base ((p.scale * v : Nat) : Int)]
  | .rollback => []
  | .indirectTarget _ _ => [MLeak.branch]
  | .retTarget _ _ => [MLeak.branch]
  | .stlForward s v => (m s).elim [] fun p => [MLeak.mem p.base ((p.scale * v : Nat) : Int)]

/-- The machine leakage a single source observation refines to when the branching
    sources are compiled branch-free: a branch, an indirect target and a return
    target have no machine counterpart. -/
def refineObsCmov (m : SlotMap) : Obs → List MLeak
  | .branch _ _ => []
  | .memIdx s v => (m s).elim [] fun p => [MLeak.mem p.base ((p.scale * v : Nat) : Int)]
  | .rollback => []
  | .indirectTarget _ _ => []
  | .retTarget _ _ => []
  | .stlForward s v => (m s).elim [] fun p => [MLeak.mem p.base ((p.scale * v : Nat) : Int)]

/-- The refinement of a whole source speculative trace. -/
def refineTrace (m : SlotMap) (t : ObsTrace) : List MLeak := t.flatMap (refineObs m)

/-- The refinement of a whole source speculative trace under a branch-free
    lowering. -/
def refineTraceCmov (m : SlotMap) (t : ObsTrace) : List MLeak :=
  t.flatMap (refineObsCmov m)

@[simp] theorem refineTrace_nil (m : SlotMap) : refineTrace m [] = [] := rfl

@[simp] theorem refineTraceCmov_nil (m : SlotMap) : refineTraceCmov m [] = [] := rfl

/-- A source branch observation refines to a machine control-flow event. -/
theorem branch_mem_refineTrace (m : SlotMap) {t : ObsTrace} {s : String} {v : Nat}
    (h : Obs.branch s v ∈ t) : MLeak.branch ∈ refineTrace m t := by
  rw [refineTrace, List.mem_flatMap]
  exact ⟨Obs.branch s v, h, by simp [refineObs]⟩

/-- The branch-free refinement produces no machine control-flow event. -/
theorem refineTraceCmov_no_branch (m : SlotMap) (t : ObsTrace) :
    MLeak.branch ∉ refineTraceCmov m t := by
  have key : ∀ o : Obs, MLeak.branch ∉ refineObsCmov m o := by
    intro o
    cases o with
    | branch _ _ => simp [refineObsCmov]
    | memIdx s v => cases hm : m s <;> simp [refineObsCmov, hm]
    | rollback => simp [refineObsCmov]
    | indirectTarget _ _ => simp [refineObsCmov]
    | retTarget _ _ => simp [refineObsCmov]
    | stlForward s v => cases hm : m s <;> simp [refineObsCmov, hm]
  rw [refineTraceCmov, List.mem_flatMap]
  rintro ⟨o, -, ho⟩
  exact key o ho

/-! ## 4. The preservation obligation -/

/-- A correspondence between a source runtime state and a speculative machine
    state: what a compilation's correctness argument supplies. -/
abbrev StateRel := RustState → SpecState 64 → Prop

/-- **The leakage-refinement obligation.** On corresponding states, the speculative
    machine trace of the compiled block is the refinement `ρ` of the speculative
    source trace. -/
def LeakRefines (ρ : ObsTrace → List MLeak) (window : SpecWindow) (O : MispredOracle)
    (c : LowCT) (OM : BypassOracle 64) (g : List (JInstr 64)) (R : StateRel) : Prop :=
  ∀ rs σ, R rs σ → specBlockLeak OM σ g = ρ (specObs window O rs c)

/-- Speculative constant-time of a machine block on a set of state pairs. -/
def MachineSCT (OM : BypassOracle 64) (g : List (JInstr 64))
    (P : SpecState 64 → SpecState 64 → Prop) : Prop :=
  ∀ σ₁ σ₂, P σ₁ σ₂ → specBlockLeak OM σ₁ g = specBlockLeak OM σ₂ g

/-- The machine state pairs the source public-equivalence relates through `R`. -/
def PubRelated (lt : LevelTable) (R : StateRel) :
    SpecState 64 → SpecState 64 → Prop :=
  fun σ₁ σ₂ => ∃ rs₁ rs₂, R rs₁ σ₁ ∧ R rs₂ σ₂ ∧ PublicEquiv lt rs₁ rs₂

/-- **Speculative constant-time transfers along a leakage refinement.** A
    compilation satisfying `LeakRefines` carries source `SpeculativelyConstantTime`
    to machine `MachineSCT` on the state pairs `PubRelated` connects. -/
theorem machineSCT_of_sourceSCT {ρ : ObsTrace → List MLeak} {window : SpecWindow}
    {O : MispredOracle} {lt : LevelTable} {c : LowCT} {OM : BypassOracle 64}
    {g : List (JInstr 64)} {R : StateRel}
    (hRef : LeakRefines ρ window O c OM g R)
    (hSrc : SpeculativelyConstantTime window O lt c) :
    MachineSCT OM g (PubRelated lt R) := by
  rintro σ₁ σ₂ ⟨rs₁, rs₂, h1, h2, hpe⟩
  rw [hRef rs₁ σ₁ h1, hRef rs₂ σ₂ h2, hSrc rs₁ rs₂ hpe]

/-- **A source branch observation has no refinement into an emitted block.** The
    branch-preserving refinement sends `Obs.branch` to a machine control-flow event,
    and a straight-line `List (JInstr 64)` trace has none. -/
theorem source_branch_not_refined {m : SlotMap} {window : SpecWindow}
    {O : MispredOracle} {c : LowCT} {OM : BypassOracle 64} {g : List (JInstr 64)}
    {R : StateRel} {rs : RustState} {σ : SpecState 64} {s : String} {v : Nat}
    (hRef : LeakRefines (refineTrace m) window O c OM g R) (hR : R rs σ)
    (hb : Obs.branch s v ∈ specObs window O rs c) : False := by
  have h2 : MLeak.branch ∈ refineTrace m (specObs window O rs c) :=
    branch_mem_refineTrace m hb
  rw [← hRef rs σ hR] at h2
  exact specBlockLeak_no_branch OM σ g h2

/-- A source conditional contributes a branch observation to its speculative
    trace. -/
theorem branch_mem_specObs_RIfNz (window : SpecWindow) (O : MispredOracle)
    (rs : RustState) (cond : String) (ct cf : LowCT) :
    Obs.branch cond (rs.rsScalar cond) ∈ specObs window O rs (.RIfNz cond ct cf) := by
  simp [specObs]

/-- **A source conditional has no branch-preserving refinement into an emitted
    block.** Instantiates `source_branch_not_refined` at a command whose speculative
    trace does contain a branch observation, so the obligation is unsatisfiable
    rather than vacuously discharged: the emitted block realises a source
    conditional branch-free or not at all. -/
theorem ifNz_no_branch_refinement {m : SlotMap} {window : SpecWindow}
    {O : MispredOracle} {cond : String} {ct cf : LowCT} {OM : BypassOracle 64}
    {g : List (JInstr 64)} {R : StateRel} {rs : RustState} {σ : SpecState 64}
    (hR : R rs σ)
    (hRef : LeakRefines (refineTrace m) window O (.RIfNz cond ct cf) OM g R) :
    False :=
  source_branch_not_refined hRef hR (branch_mem_specObs_RIfNz window O rs cond ct cf)

/-! ## 5. The direct-addressing fragment -/

/-- The constant refinement: the machine trace a direct-addressing block produces
    from a fixed speculative state. -/
def constRefine (OM : BypassOracle 64) (g : List (JInstr 64)) (σ₀ : SpecState 64) :
    ObsTrace → List MLeak := fun _ => specBlockLeak OM σ₀ g

/-- On a block all of whose instructions address memory through a base register and
    a compile-time-constant displacement, the leakage-refinement obligation holds
    with the constant refinement, for every source command and every state
    correspondence. -/
theorem leakRefines_of_allDirect (window : SpecWindow) (O : MispredOracle) (c : LowCT)
    (OM : BypassOracle 64) {g : List (JInstr 64)} (h : allDirect g = true)
    (R : StateRel) (σ₀ : SpecState 64) :
    LeakRefines (constRefine OM g σ₀) window O c OM g R :=
  fun _ σ _ => allDirect_specBlockLeak_state_independent g h OM σ σ₀

/-- On the direct-addressing fragment the machine block is speculatively
    constant-time on every set of state pairs. -/
theorem machineSCT_allDirect (OM : BypassOracle 64) {g : List (JInstr 64)}
    (h : allDirect g = true) (P : SpecState 64 → SpecState 64 → Prop) :
    MachineSCT OM g P :=
  fun σ₁ σ₂ _ => allDirect_specBlockLeak_state_independent g h OM σ₁ σ₂

/-- **Source and machine speculative constant-time on the direct-addressing
    fragment.** A source command accepted by the architectural analyser `cmdCT` is
    speculatively constant-time; a machine block in the direct-addressing class
    satisfies the leakage-refinement obligation with the constant refinement and is
    speculatively constant-time.

    The three conjuncts are independent: `c` and `g` are not tied by a compilation
    relation, and the constant refinement holds for every source command, so the
    machine conclusions do not use `hCT`. -/
theorem sct_source_to_machine_direct (window : SpecWindow) (O : MispredOracle)
    (lt : LevelTable) (leafCT : LeafCTTable) {c : LowCT}
    (hCT : cmdCT c lt leafCT = true) (OM : BypassOracle 64) {g : List (JInstr 64)}
    (hg : allDirect g = true) (R : StateRel) (σ₀ : SpecState 64) :
    SpeculativelyConstantTime window O lt c
      ∧ LeakRefines (constRefine OM g σ₀) window O c OM g R
      ∧ MachineSCT OM g (PubRelated lt R) :=
  ⟨architecturally_CT_imp_SCT window O lt leafCT c hCT,
   leakRefines_of_allDirect window O c OM hg R σ₀,
   machineSCT_allDirect OM hg _⟩

/-- **The deployed export.** When the virtual body a `Com` lowers to uses no
    register-indexed operand and its exported function gathers to a machine block,
    a source command accepted by `cmdCT` is speculatively constant-time and the
    emitted block satisfies the leakage-refinement obligation with the constant
    refinement and is speculatively constant-time.

    As in `sct_source_to_machine_direct`, `c` and `g` are not tied by a compilation
    relation and the machine conclusions do not use `hCT`. -/
theorem sct_source_to_toLprogPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin : Bool)
    (hd : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (window : SpecWindow) (O : MispredOracle) (lt : LevelTable) (leafCT : LeafCTTable)
    {c : LowCT} (hCT : cmdCT c lt leafCT = true) (OM : BypassOracle 64)
    (R : StateRel) (σ₀ : SpecState 64) :
    SpeculativelyConstantTime window O lt c
      ∧ LeakRefines (constRefine OM g σ₀) window O c OM g R
      ∧ MachineSCT OM g (PubRelated lt R) :=
  sct_source_to_machine_direct window O lt leafCT hCT OM
    (AllocCTPreservation.toLprogPhysAbi_gather_allDirect com fname shiftImm immSlotMap
      inLoadMap outStoreMap abiArgs abiTyin residence abiW forceLivePin hd hf hg)
    R σ₀

/-! ## 6. Allocator-introduced traffic is outside the source alphabet -/

/-- A scalar assignment has an empty speculative source trace. -/
@[simp] theorem specObs_RScalarSet (window : SpecWindow) (O : MispredOracle)
    (rs : RustState) (x : String) (v : Nat) :
    specObs window O rs (.RScalarSet x v) = [] := rfl

/-- The spill/reload block leaks at the frame address, whatever the speculative
    state and predictor. -/
theorem stlSpillGadget_leak_ne_nil (O : BypassOracle 64) (σ : SpecState 64) :
    specBlockLeak O σ stlSpillGadget ≠ [] := by
  intro h
  have hmem : MLeak.mem "rsp" 8 ∈ specBlockLeak O σ stlSpillGadget := by
    simp [stlSpillGadget, instrLeak]
  rw [h] at hmem
  simp at hmem

/-- A speculative machine state on the zero register file. -/
def zeroSpecState : SpecState 64 := { arch := { regs := fun _ => 0 } }

/-- **The slot-map refinement does not cover allocator-introduced memory traffic.**
    A scalar assignment has an empty source trace, so under `refineTrace` the
    obligation forces the machine trace to be empty; the spill/reload block's is
    not. A refinement for a spilling allocation has to account for machine accesses
    that no source observation names. -/
theorem slotMap_refinement_fails (m : SlotMap) (window : SpecWindow)
    (O : MispredOracle) (OM : BypassOracle 64) (x : String) (v : Nat) :
    ¬ LeakRefines (refineTrace m) window O (.RScalarSet x v) OM stlSpillGadget
        (fun _ _ => True) := by
  intro h
  have hEq := h default zeroSpecState trivial
  rw [specObs_RScalarSet, refineTrace_nil] at hEq
  exact stlSpillGadget_leak_ne_nil OM zeroSpecState hEq

end CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTPreservation
