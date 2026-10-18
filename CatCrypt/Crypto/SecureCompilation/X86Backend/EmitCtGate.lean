/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bignum4AddArrAbiDemo

/-!
# The constant-time obligation of an emitted kernel

An emitter writes an artifact by rendering an `Lprog` and calling
`IO.FS.writeFile`. This module puts a policy between the program and the
rendering: a kernel is rendered either under `publicData := true` with a recorded
reason, or after every function body of the program passes the `Lcmd` directness
check `AllocCTPreservation.lcmdDirect` (no register-indexed operand, so no memory
address depends on a register value). A program that satisfies neither yields an
error naming the offending function and instruction, and `emitCheckedTo` raises
it instead of writing the file.

`CtPolicy` is the `Lprog`-level form of the `publicData : Bool` flag the
comparison ops of `VIR/FieldEcCmpOps.lean` carry: it does not change what is
emitted, it records whether the kernel's inputs are public, and a kernel with
secret inputs is admitted only when its addressing is index-free. A secret-input
kernel that fails the check is flagged, not silently rendered.

## The object the leak conclusion covers

The check is a predicate on the `Lcmd` bodies of the program. Composed with
`AllocCTPreservation.gatherJBlock6_allDirect` (or `ConstIndexFold`'s
`gatherPrinted_allDirect`) and `ConstantTimeCoverage.allDirect_constant_time`, a
passing body whose gather succeeds has a `List (JInstr 64)` block whose
`MachineConstantTime.blockLeak` trace is the same from any two initial machine
states. The conclusion is about that gathered block. No theorem here reaches the
AT&T text `renderLprogAtt`/`renderOwned` prints, or the bytes an assembler
produces from it.

## Main results

* `CtPolicy` — the emit-time policy: `publicData : Bool` and a `reason`.
* `firstOffender`, `lprogDirect` — the first function body and instruction using
  register-indexed addressing, and the whole-program Boolean check, related by
  `firstOffender_eq_none_iff`.
* `emitChecked`, `emitChecked?`, `emitCheckedTo` — the gate in `Except`, `Option`
  and `IO` form, in place of a bare `renderOwned` + `writeFile`.
* `emitChecked_lcmdDirect` — a rendering obtained under `publicData := false`
  comes from a program every one of whose bodies is `lcmdDirect`.
* `emitChecked_gather_constant_time`, `emitChecked_gatherPrinted_constant_time` —
  the gathered `JInstr 64` block of any such body has a state-independent leakage
  trace.
* `bignum4AddPolicy`, `bignum4AddLprog_lprogDirect`, `bignum4Add_emitChecked`,
  `bignum4Add_gather_constant_time`, `emitBignum4AddTo` — the gate applied to the
  owned-backend 4-limb add `Bignum4AddArrAbiDemo.bignum4AddLprog`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EmitCtGate

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_constant_time)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (linstrRDirect lcmdDirect lcmdDirect_iff gatherJBlock6_allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
  (gatherPrinted gatherPrinted_allDirect)

/-! ## 1. The policy -/

/-- The constant-time policy of an emitted kernel: whether its inputs are public
    data, and the reason recorded for that judgement. The policy does not change
    what is emitted; it records the input classification, and a kernel with
    secret inputs (`publicData := false`) is emitted only when every function
    body of its program is index-free. -/
structure CtPolicy where
  /-- `true` when the kernel's inputs are public data, so its addressing is not
      required to be independent of them. -/
  publicData : Bool
  /-- The recorded reason for the classification. -/
  reason : String

/-- A policy declaring the kernel's inputs public data, with a reason. -/
def CtPolicy.publicInputs (reason : String) : CtPolicy :=
  { publicData := true, reason := reason }

/-- A policy declaring the kernel's inputs secret, with a reason. The directness
    check is then the condition for emitting. -/
def CtPolicy.secretInputs (reason : String) : CtPolicy :=
  { publicData := false, reason := reason }

/-! ## 2. The directness check on a whole program -/

/-- The first instruction of the body using register-indexed addressing. -/
def firstIndexed : Lcmd → Option Linstr
  | [] => none
  | i :: is => if linstrRDirect i.li_i then firstIndexed is else some i

theorem firstIndexed_eq_none_iff (body : Lcmd) :
    firstIndexed body = none ↔ lcmdDirect body = true := by
  induction body with
  | nil => simp [firstIndexed, lcmdDirect]
  | cons i is ih =>
      by_cases h : linstrRDirect i.li_i = true
      · simp only [firstIndexed, h, if_true, lcmdDirect, List.all_cons,
          Bool.and_eq_true, true_and]
        simpa [lcmdDirect] using ih
      · simp only [Bool.not_eq_true] at h
        simp [firstIndexed, h, lcmdDirect]

/-- The first function of the list one of whose instructions uses
    register-indexed addressing, with that instruction. -/
def funcsOffender : List (String × Lfundef) → Option (String × Linstr)
  | [] => none
  | f :: fs =>
      match firstIndexed f.2.lfd_body with
      | some i => some (f.1, i)
      | none => funcsOffender fs

/-- The first function of the program one of whose instructions uses
    register-indexed addressing, with that instruction. -/
def firstOffender (lp : Lprog) : Option (String × Linstr) :=
  funcsOffender lp.lp_funcs

/-- `true` when no function body of the program uses register-indexed
    addressing. -/
def lprogDirect (lp : Lprog) : Bool :=
  lp.lp_funcs.all (fun f => lcmdDirect f.2.lfd_body)

theorem funcsOffender_eq_none_iff (fs : List (String × Lfundef)) :
    funcsOffender fs = none ↔ ∀ f ∈ fs, lcmdDirect f.2.lfd_body = true := by
  induction fs with
  | nil => simp [funcsOffender]
  | cons f fs ih =>
      cases h : firstIndexed f.2.lfd_body with
      | some i =>
          have hf : ¬ lcmdDirect f.2.lfd_body = true := by
            intro hd
            rw [(firstIndexed_eq_none_iff f.2.lfd_body).mpr hd] at h
            exact absurd h (by simp)
          simp only [funcsOffender, h]
          simp only [List.mem_cons, reduceCtorEq, false_iff, not_forall]
          exact ⟨f, by simp, hf⟩
      | none =>
          have hf : lcmdDirect f.2.lfd_body = true :=
            (firstIndexed_eq_none_iff f.2.lfd_body).mp h
          simp only [funcsOffender, h, List.mem_cons, ih]
          constructor
          · intro hall g hg
            rcases hg with rfl | hg
            · exact hf
            · exact hall g hg
          · intro hall g hg
            exact hall g (Or.inr hg)

theorem firstOffender_eq_none_iff (lp : Lprog) :
    firstOffender lp = none ↔ lprogDirect lp = true := by
  simp only [firstOffender, lprogDirect, funcsOffender_eq_none_iff, List.all_eq_true]

/-! ## 3. The gate -/

/-- The message a failing gate reports: the kernel symbol, the function, and the
    instruction using register-indexed addressing. -/
def offenderMessage (sym fn : String) (i : Linstr) : String :=
  "constant-time gate: kernel " ++ sym ++ " is declared secret-input, and " ++
    "function " ++ fn ++ " uses register-indexed addressing at " ++
    LinstrR.toText i.li_i

/-- The rendering of `lp` under the policy: the rendering when the policy
    declares public data, the rendering when every function body of `lp` is
    index-free, and otherwise the message naming the first offending function and
    instruction. An emit driver calls this in place of a bare renderer. -/
def emitChecked (render : Lprog → String) (pol : CtPolicy) (sym : String)
    (lp : Lprog) : Except String String :=
  if pol.publicData then .ok (render lp)
  else
    match firstOffender lp with
    | none => .ok (render lp)
    | some (fn, i) => .error (offenderMessage sym fn i)

/-- `emitChecked` without the message. -/
def emitChecked? (render : Lprog → String) (pol : CtPolicy) (sym : String)
    (lp : Lprog) : Option String :=
  (emitChecked render pol sym lp).toOption

/-- Write the rendering of `lp` to `path` when the gate admits it, and raise the
    gate's message otherwise, so a kernel failing the check stops the emit
    instead of reaching the file. -/
def emitCheckedTo (render : Lprog → String) (pol : CtPolicy) (sym : String)
    (lp : Lprog) (path : System.FilePath) : IO Unit := do
  match emitChecked render pol sym lp with
  | .error msg => throw (IO.userError msg)
  | .ok text =>
      match path.parent with
      | some dir => IO.FS.createDirAll dir
      | none => pure ()
      IO.FS.writeFile path text
      IO.println s!"wrote {path} ({sym}, publicData := {pol.publicData}: {pol.reason})"

/-! ## 4. What a passing gate gives -/

/-- A program every function body of which is index-free passes the gate under
    any policy. -/
theorem emitChecked_of_direct (render : Lprog → String) (pol : CtPolicy)
    (sym : String) {lp : Lprog} (h : lprogDirect lp = true) :
    emitChecked render pol sym lp = .ok (render lp) := by
  unfold emitChecked
  split
  · rfl
  · rw [(firstOffender_eq_none_iff lp).mpr h]

/-- **The gate's content.** A rendering obtained under a secret-input policy
    comes from a program every one of whose function bodies is index-free. -/
theorem emitChecked_lcmdDirect {render : Lprog → String} {pol : CtPolicy}
    {sym : String} {lp : Lprog} {s : String} (hp : pol.publicData = false)
    (h : emitChecked render pol sym lp = .ok s) :
    ∀ f ∈ lp.lp_funcs, lcmdDirect f.2.lfd_body = true := by
  rw [emitChecked, hp, if_neg (by simp)] at h
  cases ho : firstOffender lp with
  | some p =>
      rw [ho] at h
      exact absurd h (by simp)
  | none =>
      have : lprogDirect lp = true := (firstOffender_eq_none_iff lp).mp ho
      simpa [lprogDirect] using this

/-- The whole-program Boolean form of `emitChecked_lcmdDirect`. -/
theorem emitChecked_lprogDirect {render : Lprog → String} {pol : CtPolicy}
    {sym : String} {lp : Lprog} {s : String} (hp : pol.publicData = false)
    (h : emitChecked render pol sym lp = .ok s) : lprogDirect lp = true := by
  simpa [lprogDirect] using emitChecked_lcmdDirect hp h

/-- **The gathered block of a gated body is in the machine constant-time class.**
    The gather of `AllocCTPreservation` on any function body of a program the
    gate admitted under a secret-input policy produces only direct
    base + compile-time-displacement accesses. -/
theorem emitChecked_gather_allDirect {render : Lprog → String} {pol : CtPolicy}
    {sym : String} {lp : Lprog} {s : String} {f : String × Lfundef}
    {g : List (JInstr 64)} (hp : pol.publicData = false)
    (h : emitChecked render pol sym lp = .ok s) (hf : f ∈ lp.lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g) : allDirect g = true :=
  gatherJBlock6_allDirect (emitChecked_lcmdDirect hp h f hf) hg

/-- **The leakage conclusion.** For a program the gate admitted under a
    secret-input policy, the gathered `JInstr 64` block of every function body
    has the same machine leakage trace from any two initial states. The statement
    is about the gathered block, not about the rendered text or the bytes. -/
theorem emitChecked_gather_constant_time {render : Lprog → String} {pol : CtPolicy}
    {sym : String} {lp : Lprog} {s : String} {f : String × Lfundef}
    {g : List (JInstr 64)} (hp : pol.publicData = false)
    (h : emitChecked render pol sym lp = .ok s) (hf : f ∈ lp.lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g) (s₁ s₂ : JState 64) :
    MachineConstantTime.blockLeak s₁ g = MachineConstantTime.blockLeak s₂ g :=
  allDirect_constant_time g (emitChecked_gather_allDirect hp h hf hg) s₁ s₂

/-- The same conclusion for `ConstIndexFold.gatherPrinted`, the gather that
    lowers a register rebind the way `LprogAsmPrinter` prints it. -/
theorem emitChecked_gatherPrinted_constant_time {render : Lprog → String}
    {pol : CtPolicy} {sym : String} {lp : Lprog} {s : String}
    {f : String × Lfundef} {g : List (JInstr 64)} (hp : pol.publicData = false)
    (h : emitChecked render pol sym lp = .ok s) (hf : f ∈ lp.lp_funcs)
    (hg : gatherPrinted f.2.lfd_body = some g) (s₁ s₂ : JState 64) :
    MachineConstantTime.blockLeak s₁ g = MachineConstantTime.blockLeak s₂ g :=
  allDirect_constant_time g
    (gatherPrinted_allDirect (emitChecked_lcmdDirect hp h f hf) hg) s₁ s₂

/-! ## 5. The gate on the owned-backend 4-limb add

`Bignum4AddArrAbiDemo.bignum4AddLprog` is the limbwise 4-limb add `Com` exported
through `Com.toLprogPhysAbi` with the array-ABI load and store maps, rendered by
`LprogOptPipeline.renderOwned` and written as `bignum4_add_owned.s`. Its inputs
are bignum limbs, so its policy is `publicData := false` and the directness check
is the condition for emitting it.

The check is discharged structurally rather than by evaluating the export:
`bignum4AddCom` binds only `regArith` ops, so it is in the index-free fragment
`ComJasminCTByConstruction`, and `ComToLfundefDirect.comToLfundef_lcmdDirect` with
`AllocCTPreservation.toLprogPhysAbi_lcmdDirect` carry that through the virtual
body and the deployed allocation to the exported program.

A caller whose kernel does not pass the check has two moves, and the policy
records which: set `publicData := true` with a reason stating why the kernel's
inputs are public data, or keep `publicData := false` and remove the
register-indexed access — `ConstIndexFold.constIndexFold` rewrites an indexed
access whose index register holds a literal to its compile-time-displacement
form. A secret-input kernel that still fails is reported by `offenderMessage`
and not rendered. -/

open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
  (ComJasminCTByConstruction comJasminCT?_eq_true_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect (comToLfundef_lcmdDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (toLprogPhysAbi_lcmdDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bignum4AddArrAbiDemo
  (bignum4AddCom bignum4AddLprog)

/-- The policy of the 4-limb add: its limbs are secret, so it is emitted only
    through the directness check. -/
def bignum4AddPolicy : CtPolicy :=
  CtPolicy.secretInputs "the input limbs of a bignum add are secret"

/-- The 4-limb add `Com` binds only register arithmetic, so it is in the
    index-free fragment of `Com jasminDialect`. -/
theorem bignum4AddCom_indexFree : ComJasminCTByConstruction bignum4AddCom :=
  (comJasminCT?_eq_true_iff bignum4AddCom).mp rfl

/-- No function body of the 4-limb-add export uses register-indexed
    addressing. -/
theorem bignum4AddLprog_lprogDirect : lprogDirect bignum4AddLprog = true := by
  rw [lprogDirect, List.all_eq_true]
  intro f hf
  simpa using
    toLprogPhysAbi_lcmdDirect bignum4AddCom "bignum4_add" (fun _ => none) (fun _ => none)
      (CompileComToElf.deriveInLoadArr 8 8) (CompileComToElf.deriveOutStoreArr 4 8)
      ["RDI", "RSI"]
      [64, 64, 64, 64, 64, 64, 64, 64] none 64 false
      (comToLfundef_lcmdDirect bignum4AddCom (fun _ => none) bignum4AddCom_indexFree) f hf

/-- The gate admits the 4-limb add under its secret-input policy. -/
theorem bignum4Add_emitChecked :
    emitChecked LprogOptPipeline.renderOwned bignum4AddPolicy "bignum4_add" bignum4AddLprog
      = .ok (LprogOptPipeline.renderOwned bignum4AddLprog) :=
  emitChecked_of_direct _ _ _ bignum4AddLprog_lprogDirect

/-- The gathered block of every function body of the 4-limb-add export has the
    same machine leakage trace from any two initial states. -/
theorem bignum4Add_gather_constant_time {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ bignum4AddLprog.lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g) (s₁ s₂ : JState 64) :
    MachineConstantTime.blockLeak s₁ g = MachineConstantTime.blockLeak s₂ g :=
  emitChecked_gather_constant_time (render := LprogOptPipeline.renderOwned)
    (sym := "bignum4_add") rfl bignum4Add_emitChecked hf hg s₁ s₂

/-- Write the owned-backend 4-limb add through the gate. -/
def emitBignum4AddTo (dir : String) : IO Unit :=
  emitCheckedTo LprogOptPipeline.renderOwned bignum4AddPolicy "bignum4_add"
    bignum4AddLprog (dir ++ "/bignum4_add_owned.s")

end CatCrypt.Crypto.SecureCompilation.X86Backend.EmitCtGate
