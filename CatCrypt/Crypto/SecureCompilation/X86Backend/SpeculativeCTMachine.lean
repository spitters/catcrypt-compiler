/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

/-!
# Speculative store-bypass leakage for the emitted x86 subset

`MachineConstantTime.blockLeak` is the architectural machine leakage trace of a
straight-line `List (JInstr w)`: the control-flow and memory-address events an
attacker reads from the committed execution. This module adds the
store-to-load-forwarding (Spectre-v4 / STL) transient to that model, at the same
`JInstr` level the register allocator's output lives at, and states constant-time
against it.

## The model

`SpecState` carries the machine state `JState`, a **store buffer** recording for
each memory write the value that write overwrote, and a **speculation window**
bounding how many transient forwards may occur. `specStep` runs one instruction:
a store appends the overwritten (stale) value to the buffer and otherwise steps
`evalInstr`; a load either takes `evalInstr`'s value, or — when the window is open
and the `BypassOracle` fires — is forwarded the stale value the buffer holds for
its effective address, consuming one unit of window. `specBlockLeak` concatenates
the existing per-instruction leak `MachineConstantTime.instrLeak` against the
speculative register file, so the observable is unchanged from the architectural
model and only the state the observer reads differs.

The oracle is an arbitrary function of the whole speculative state, of the base
register name, and of the effective displacement. It may read secret registers.

## Scope

Modelled: speculative store bypass at `loadMem`, `loadMemIdx` and `mulxMem`, with
a per-address store buffer and a bounded transient window; the memory-address
channel at `(base register name, effective displacement)` granularity.

Not modelled: branch misprediction (Spectre-PHT) and indirect-branch or return
misprediction (Spectre-BTB, Spectre-RSB) — `List (JInstr w)` has no conditional
jump and no call instruction, so those sites do not exist at this level; the value
held in a base register (`MLeak.mem` records the base register's *name*, so the
model treats base contents as public); cache-line granularity, port contention and
timing; transient instructions fetched from outside the block; and the drain of
the store buffer at retirement, which is irrelevant to a single block's trace.

## The two results

`specBlockLeak_state_independent`: a block all of whose instructions are
`IsDirect` has a speculative leakage trace independent of the speculative state,
for every window and every bypass oracle. `toLprogPhysAbi_gather_speculative_ct`
composes it with `AllocCTPreservation.toLprogPhysAbi_gather_allDirect`, giving the
property for the block the deployed allocator emits.

`stlSpillGadget_arch_constant_time` and `stlSpillGadget_speculative_leak`: a
four-instruction spill/reload block whose architectural leakage is determined by
the public registers, and whose speculative leakage separates two states that
differ only on a secret register. Architectural constant-time therefore does not
imply speculative constant-time at the machine level. The separating block is
outside `IsDirect`: its last access is a register-indexed load whose index came
from a bypassed reload of a spill slot.

## References

* Cauligi, Disselkoen, von Gleissenthall, Tullsen, Stefan, Rezk, Barthe,
  "Constant-Time Foundations for the New Spectre Era", PLDI 2020.
* Vassena, Disselkoen, von Gleissenthall, Cauligi, Kıcı, Jhala, Tullsen, Stefan,
  "Automatically Eliminating Speculative Leaks with Blade", POPL 2021.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTMachine

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)

/-! ## 1. The store buffer and the speculative state -/

/-- A store buffer entry list, newest first. An entry `(base, off, v)` records
    that a write to `[base + off]` overwrote the word `v`; `v` is the value a load
    that speculatively bypasses that write is forwarded. -/
abbrev StoreBuf (w : Nat) := List (String × Int × BitVec w)

/-- The value the newest buffered write to `[base + off]` overwrote, if the buffer
    holds one. -/
def sbLookup {w : Nat} : StoreBuf w → String → Int → Option (BitVec w)
  | [], _, _ => none
  | (b, o, v) :: rest, base, off =>
      if b = base ∧ o = off then some v else sbLookup rest base off

@[simp] theorem sbLookup_nil {w : Nat} (base : String) (off : Int) :
    sbLookup ([] : StoreBuf w) base off = none := rfl

/-- The speculative machine state: the register/flag/memory state the committed
    semantics works on, the store buffer of overwritten values, and the number of
    transient forwards the speculation window still permits. -/
structure SpecState (w : Nat) where
  /-- The machine state `evalInstr` steps. -/
  arch : JState w
  /-- The overwritten values a bypassing load may be forwarded, newest first. -/
  buf : StoreBuf w := []
  /-- The number of transient store bypasses still permitted. -/
  window : Nat := 0

/-- A store-bypass predictor: at a load from `[base + off]` in speculative state
    `σ`, does the load bypass the pending write and take the stale value? An
    arbitrary function of the whole state, so the predictor may read secrets. -/
abbrev BypassOracle (w : Nat) := SpecState w → String → Int → Bool

/-- The predictor that never bypasses; `specStep` under it is `evalInstr`. -/
def neverBypass {w : Nat} : BypassOracle w := fun _ _ _ => false

/-- The value a load from `[base + off]` is forwarded by a bypass, if the window
    is open, the oracle fires, and the buffer holds an overwritten value for that
    address. -/
def bypasses {w : Nat} (O : BypassOracle w) (σ : SpecState w) (base : String)
    (off : Int) : Option (BitVec w) :=
  if 0 < σ.window ∧ O σ base off = true then sbLookup σ.buf base off else none

@[simp] theorem bypasses_neverBypass {w : Nat} (σ : SpecState w) (base : String)
    (off : Int) : bypasses neverBypass σ base off = none := by
  simp [bypasses, neverBypass]

@[simp] theorem bypasses_of_window_zero {w : Nat} (O : BypassOracle w)
    (σ : SpecState w) (h : σ.window = 0) (base : String) (off : Int) :
    bypasses O σ base off = none := by
  simp [bypasses, h]

/-! ## 2. The speculative step -/

/-- One instruction of the speculative semantics.

    A store steps `evalInstr` and pushes the word it overwrote onto the buffer. A
    memory read (`loadMem`, `loadMemIdx`, the memory source of `mulxMem` and of the
    memory-operand arithmetic `addMem`, `adcxMem`, `adoxMem`, `imulMem`, `imulriMem`,
    of the compare `cmpMem` and of the conditional move `cmovccMem`)
    takes the bypassed stale value when `bypasses` supplies one, consuming a unit of
    window, and otherwise steps `evalInstr`. `addToMem` does both: it reads its cell,
    possibly bypassed, and pushes the word it overwrites. Every other instruction steps
    `evalInstr`. -/
def specStep {w : Nat} (O : BypassOracle w) (σ : SpecState w) :
    JInstr w → SpecState w
  | .storeMem base off src =>
      { arch := evalInstr σ.arch (.storeMem base off src)
        buf := (base, off, σ.arch.load base off) :: σ.buf
        window := σ.window }
  | .storeMemIdx base idx scale src =>
      let off : Int := ((scale * (σ.arch.get idx).toNat : Nat) : Int)
      { arch := evalInstr σ.arch (.storeMemIdx base idx scale src)
        buf := (base, off, σ.arch.load base off) :: σ.buf
        window := σ.window }
  | .loadMem dst base off =>
      match bypasses O σ base off with
      | some stale =>
          { arch := σ.arch.setReg dst stale, buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.loadMem dst base off) }
  | .loadMemIdx dst base idx scale =>
      let off : Int := ((scale * (σ.arch.get idx).toNat : Nat) : Int)
      match bypasses O σ base off with
      | some stale =>
          { arch := σ.arch.setReg dst stale, buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.loadMemIdx dst base idx scale) }
  | .mulxMem dHi dLo a base off =>
      match bypasses O σ base off with
      | some stale =>
          let (lo, hi) := x86_MULX_lo_hi (a.eval σ.arch) stale
          { arch := (σ.arch.setReg dLo lo).setReg dHi hi
            buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.mulxMem dHi dLo a base off) }
  | .addMem dst base off =>
      match bypasses O σ base off with
      | some stale =>
          { arch := σ.arch.writeB5W dst (x86_ADD (σ.arch.get dst) stale)
            buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.addMem dst base off) }
  | .adcxMem dst base off =>
      match bypasses O σ base off with
      | some stale =>
          let (co, res) := x86_ADCX (σ.arch.get dst) stale (σ.arch.flagB (·.cf))
          { arch := { regs := fun r' => if r' = dst then res else σ.arch.regs r'
                      flags := { σ.arch.flags with cf := co }
                      mem := σ.arch.mem }
            buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.adcxMem dst base off) }
  | .adoxMem dst base off =>
      match bypasses O σ base off with
      | some stale =>
          let (co, res) := x86_ADCX (σ.arch.get dst) stale (σ.arch.flagB (·.of))
          { arch := { regs := fun r' => if r' = dst then res else σ.arch.regs r'
                      flags := { σ.arch.flags with of := co }
                      mem := σ.arch.mem }
            buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.adoxMem dst base off) }
  | .imulMem dst base off =>
      match bypasses O σ base off with
      | some stale =>
          { arch := σ.arch.writeB5W dst (x86_IMULt (σ.arch.get dst) stale)
            buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.imulMem dst base off) }
  | .imulriMem dst base off imm =>
      match bypasses O σ base off with
      | some stale =>
          { arch := σ.arch.writeB5W dst (x86_IMULt stale (BitVec.ofNat w imm))
            buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.imulriMem dst base off imm) }
  | .cmpMem a base off =>
      match bypasses O σ base off with
      | some stale =>
          { arch := σ.arch.writeB5 (x86_CMP (σ.arch.get a) stale)
            buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.cmpMem a base off) }
  | .cmovccMem c dst base off =>
      match bypasses O σ base off with
      | some stale =>
          { arch := σ.arch.setReg dst (x86_CMOVcc (σ.arch.condB c) stale (σ.arch.get dst))
            buf := σ.buf, window := σ.window - 1 }
      | none => { σ with arch := evalInstr σ.arch (.cmovccMem c dst base off) }
  | .addToMem base off src =>
      match bypasses O σ base off with
      | some stale =>
          { arch := σ.arch.writeB5Mem base off (x86_ADD stale (src.eval σ.arch))
            buf := (base, off, σ.arch.load base off) :: σ.buf
            window := σ.window - 1 }
      | none =>
          { arch := evalInstr σ.arch (.addToMem base off src)
            buf := (base, off, σ.arch.load base off) :: σ.buf
            window := σ.window }
  | i => { σ with arch := evalInstr σ.arch i }

/-- The speculative leakage trace: the per-instruction leak
    `MachineConstantTime.instrLeak` read against the speculative register file,
    with the state threaded by `specStep`. -/
def specBlockLeak {w : Nat} (O : BypassOracle w) (σ : SpecState w) :
    List (JInstr w) → List MLeak
  | [] => []
  | i :: is => instrLeak σ.arch i ++ specBlockLeak O (specStep O σ i) is

@[simp] theorem specBlockLeak_nil {w : Nat} (O : BypassOracle w) (σ : SpecState w) :
    specBlockLeak O σ [] = [] := rfl

@[simp] theorem specBlockLeak_cons {w : Nat} (O : BypassOracle w) (σ : SpecState w)
    (i : JInstr w) (is : List (JInstr w)) :
    specBlockLeak O σ (i :: is)
      = instrLeak σ.arch i ++ specBlockLeak O (specStep O σ i) is := rfl

/-! ## 3. The architectural projection

With no bypass available the speculative state's `arch` component is exactly what
`evalInstr` computes, so the speculative trace is the architectural one. This
holds under the never-bypass predictor, and under any predictor once the window is
closed. -/

theorem specStep_arch_of_no_bypass {w : Nat} (O : BypassOracle w) (σ : SpecState w)
    (h : ∀ base off, bypasses O σ base off = none) (i : JInstr w) :
    (specStep O σ i).arch = evalInstr σ.arch i := by
  cases i <;> simp [specStep, h]

theorem specStep_window_of_window_zero {w : Nat} (O : BypassOracle w)
    (σ : SpecState w) (h : σ.window = 0) (i : JInstr w) :
    (specStep O σ i).window = 0 := by
  cases i <;> simp [specStep, h]

/-- Once the speculation window is closed, the speculative trace is the
    architectural trace, for every predictor. -/
theorem specBlockLeak_of_window_zero {w : Nat} (O : BypassOracle w)
    (body : List (JInstr w)) (σ : SpecState w) (h : σ.window = 0) :
    specBlockLeak O σ body = blockLeak σ.arch body := by
  induction body generalizing σ with
  | nil => rfl
  | cons i is ih =>
    simp only [specBlockLeak_cons, blockLeak_cons]
    rw [ih (specStep O σ i) (specStep_window_of_window_zero O σ h i),
      specStep_arch_of_no_bypass O σ (fun base off => bypasses_of_window_zero O σ h base off) i]

/-- Under the never-bypass predictor the speculative trace is the architectural
    trace. -/
theorem specBlockLeak_neverBypass {w : Nat} (body : List (JInstr w))
    (σ : SpecState w) :
    specBlockLeak neverBypass σ body = blockLeak σ.arch body := by
  induction body generalizing σ with
  | nil => rfl
  | cons i is ih =>
    simp only [specBlockLeak_cons, blockLeak_cons]
    rw [ih (specStep neverBypass σ i),
      specStep_arch_of_no_bypass neverBypass σ (fun base off => bypasses_neverBypass σ base off) i]

/-! ## 4. Direct addressing is speculatively constant-time

`instrLeak` reads the machine state only through the index register of a
register-indexed access. An `IsDirect` instruction has none, so its leak is fixed
by the instruction (`MachineConstantTime.instrLeak_state_independent`) whatever
value a bypass forwarded into the register file. The whole trace is therefore
independent of the speculative state, for every window and every predictor. -/

/-- **Speculative constant-time for direct addressing.** A block all of whose
    instructions use base + compile-time-constant displacement addressing produces
    the same speculative leakage trace from any two speculative states, for every
    store-bypass predictor. A bypass changes only register values, and no
    register value reaches an address in this class. -/
theorem specBlockLeak_state_independent {w : Nat} (body : List (JInstr w))
    (hbody : ∀ i ∈ body, IsDirect i) (O : BypassOracle w) (σ₁ σ₂ : SpecState w) :
    specBlockLeak O σ₁ body = specBlockLeak O σ₂ body := by
  induction body generalizing σ₁ σ₂ with
  | nil => rfl
  | cons i is ih =>
    have hi : IsDirect i := hbody i (List.mem_cons_self ..)
    have htl : ∀ j ∈ is, IsDirect j := fun j hj => hbody j (List.mem_cons_of_mem i hj)
    simp only [specBlockLeak_cons]
    rw [instrLeak_state_independent i hi σ₁.arch σ₂.arch]
    rw [ih htl (specStep O σ₁ i) (specStep O σ₂ i)]

/-- The `allDirect` form of `specBlockLeak_state_independent`. -/
theorem allDirect_specBlockLeak_state_independent {w : Nat} (body : List (JInstr w))
    (h : allDirect body = true) (O : BypassOracle w) (σ₁ σ₂ : SpecState w) :
    specBlockLeak O σ₁ body = specBlockLeak O σ₂ body :=
  specBlockLeak_state_independent body
    (ConstantTimeCoverage.allDirect_mem_isDirect body h) O σ₁ σ₂

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation (lcmdDirect)

/-- **The exported function's gathered block is speculatively constant-time.**
    Composes `AllocCTPreservation.toLprogPhysAbi_gather_allDirect` with
    `allDirect_specBlockLeak_state_independent`: when the virtual body a `Com`
    lowers to uses no register-indexed operand, the block the deployed allocator
    emits has the same speculative leakage trace from any two speculative states,
    for every window and every store-bypass predictor. -/
theorem toLprogPhysAbi_gather_speculative_ct {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin : Bool)
    (h : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (O : BypassOracle 64) (σ₁ σ₂ : SpecState 64) :
    specBlockLeak O σ₁ g = specBlockLeak O σ₂ g :=
  allDirect_specBlockLeak_state_independent g
    (AllocCTPreservation.toLprogPhysAbi_gather_allDirect com fname shiftImm immSlotMap
      inLoadMap outStoreMap abiArgs abiTyin residence abiW forceLivePin h hf hg) O σ₁ σ₂

/-! ## 5. A spill/reload block that is architecturally but not speculatively
constant-time

The block writes a secret to a frame slot, overwrites the slot with a public
value, reloads the slot, and uses the reloaded word as a table index. Committed
execution reloads the public value, so the address trace is determined by the
public registers. A load that bypasses the second write is forwarded the secret
the first write left in the slot, and the table index — hence the address the
attacker reads — is then the secret.

Spill slots are fixed frame displacements and hold whatever the previous spill
left there, so this is the shape register allocation produces. The block is
outside `IsDirect`, which is what `specBlockLeak_state_independent` requires and
what `AllocCTPreservation` establishes of the deployed allocator's output: the
allocator emits no register-indexed access, so the reloaded word never reaches an
address. -/

/-- Secret in the frame slot, overwritten by a public value, reloaded, and used as
    a table index. -/
def stlSpillGadget : List (JInstr 64) :=
  [ .storeMem "rsp" 8 (.reg "sec")
  , .storeMem "rsp" 8 (.reg "pubv")
  , .loadMem "i" "rsp" 8
  , .loadMemIdx "d" "tbl" "i" 8 ]

/-- The public/secret split for `stlSpillGadget`: the frame pointer `rsp`, the
    table base `tbl` and the spilled public word `pubv` are public; `sec` is
    secret. -/
def stlPub : PubPred := fun r => r == "rsp" || r == "tbl" || r == "pubv"

/-- `stlSpillGadget` uses a register-indexed access, so it is not in the direct
    addressing class. -/
theorem stlSpillGadget_not_direct : ¬ (∀ i ∈ stlSpillGadget, IsDirect i) := by
  intro h
  have := h (.loadMemIdx "d" "tbl" "i" 8) (by simp [stlSpillGadget])
  simp [IsDirect] at this

/-- **`stlSpillGadget` is architecturally constant-time.** Committed execution
    reloads the public word `pubv` from the frame slot, so the whole leakage trace
    — three accesses at the constant frame address and one at `tbl` offset by the
    reloaded word — is the same from any two states agreeing on the public
    registers, whatever the secret `sec` holds. -/
theorem stlSpillGadget_arch_constant_time (s₁ s₂ : JState 64)
    (hag : agreePub stlPub s₁ s₂) :
    blockLeak s₁ stlSpillGadget = blockLeak s₂ stlSpillGadget := by
  have hp : s₁.regs "pubv" = s₂.regs "pubv" := hag "pubv" (by decide)
  simp only [stlSpillGadget, blockLeak_cons, blockLeak_nil, instrLeak, evalInstr,
    x86_MOV, JState.setReg, JState.store, JState.get, JState.load, JOperand.eval,
    List.nil_append, List.cons_append]
  simp only [and_self, ite_true, hp]

/-- **`stlSpillGadget` is not speculatively constant-time.** Under a predictor that
    bypasses the frame-slot write, the reload is forwarded the secret the earlier
    write left in the slot; the register-indexed load then addresses `tbl` at a
    secret-dependent displacement. Two states differing only on `sec` produce
    different speculative traces, so architectural constant-time does not imply
    speculative constant-time at the machine level. -/
theorem stlSpillGadget_speculative_leak :
    ∃ (O : BypassOracle 64) (σ₁ σ₂ : SpecState 64),
      agreePub stlPub σ₁.arch σ₂.arch ∧
        specBlockLeak O σ₁ stlSpillGadget ≠ specBlockLeak O σ₂ stlSpillGadget := by
  refine ⟨fun _ _ _ => true,
          { arch := { regs := fun r => if r = "sec" then 0 else 0 }, buf := [], window := 4 },
          { arch := { regs := fun r => if r = "sec" then 1 else 0 }, buf := [], window := 4 },
          ?_, ?_⟩
  · intro r hr
    simp only [stlPub, Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with (rfl | rfl) | rfl <;> rfl
  · decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTMachine
