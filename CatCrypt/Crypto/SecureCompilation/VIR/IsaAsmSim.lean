/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.IsaMachine

@[expose] public section

set_option autoImplicit false

/-!
# The assembly simulation of an instruction set

The assembly simulation of an instruction set states that the bytes its encoder produces for
a gated body decode at the machine to a program whose run simulates the run of the body. The
statement has four ingredients: a decidable gate on bodies, an encoder from bodies to bytes,
a relation between the states of the body and of the machine at entry and at the end, and
the semantics the body runs in. `AsmSim S M` packages them over a source semantics `S` and
an `IsaMachine` `M`.

The record is a structure over an `IsaMachine`, a machine with its assembly simulation, and
not a field of `IsaMachine`: the machine of an instruction set is one record for every gate,
while an instruction set has several gated classes of bodies (on x86 the classes
`printedAddrB` and `printedAddrWB`, on AArch64 and RV64 one selection per array layout),
each with its own encoder, relation and simulation.

The source semantics is a parameter because the simulations differ in it. On AArch64 and
RV64 the body is a straight-line list of instructions run by the step of the instruction set
(`Isa.straightSem`). On x86 the simulation of printed bodies runs the address semantics of
the linear language, whose frame words sit at addresses fixed by the entry stack register;
its run through the step of the instruction set is `Isa.checkedSem`, the fuel run of a
program whose array accesses are in bounds.

## Main definitions

* `SrcSem`: a source semantics, the bodies, the states and the halting runs.
* `Isa.straightSem`, `Isa.checkedSem`: the straight-line run and the in-bounds fuel run of
  an instruction set as source semantics.
* `AsmSim`: the gate, the encoder, the entry and exit relations and the simulation.
* `AsmSim.ofGate`: the simulation restricted to a gate that implies the gate of the record.

## Main results

* `AsmSim.halts`: a run of a gated body from a related state gives a halting run of the
  decoded bytes.
* `AsmSim.runL`: the halting run has a leakage trace, with the exit relation.
* `AsmSim.haltsC`: the halting run as a run through calls.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.CT

/-- **A source semantics**: the bodies, the states, and the halting runs of a body from a
    state to a state. -/
structure SrcSem : Type 1 where
  /-- The bodies. -/
  Body : Type
  /-- The states a body runs on. -/
  State : Type
  /-- The halting runs of a body. -/
  Run : Body → State → State → Prop

namespace Isa

variable (I : Isa)

/-- The straight-line source semantics of an instruction set in a program `P`: a body is a
    list of instructions and its run is `I.runL P`. -/
def straightSem (P : LprogM) : SrcSem where
  Body := List LinstrRM
  State := LstateMF
  Run := fun is s s' => I.runL P is s = some s'

/-- The in-bounds fuel semantics of an instruction set: a body gives a program by `toProg`
    and its run is a halting run of `I.lsemFuelMemF` whose array accesses are in bounds
    (`I.RunIdxOk`). -/
def checkedSem {Body : Type} (toProg : Body → LprogM) : SrcSem where
  Body := Body
  State := LstateMF
  Run := fun B s s' => ∃ fuel, I.lsemFuelMemF (toProg B) fuel s = some s'
    ∧ I.RunIdxOk (toProg B) fuel s

end Isa

/-- **The assembly simulation of an instruction set** over a source semantics `S` and a
    machine `M`: a gate on bodies, an encoder of bodies to bytes, the relation `Pre` of a
    source state and a machine state at entry, the relation `Post` of the final source state
    and the final machine state (which may refer to the two states at entry), and the
    simulation. -/
structure AsmSim (S : SrcSem) (M : IsaMachine) : Type where
  /-- The gate that decides the covered bodies. -/
  gate : S.Body → Bool
  /-- The encoder of a body to bytes. -/
  encode : S.Body → List (BitVec 8)
  /-- The relation of a source state and a machine state at entry to a body. -/
  Pre : S.Body → S.State → M.MState → Prop
  /-- The relation of the final source state and the final machine state of a body, given
      the source state and the machine state at entry. -/
  Post : S.Body → S.State → M.MState → S.State → M.MState → Prop
  /-- The bytes of a gated body decode to a program, and every source run of the body from a
      state related to a machine state is matched by a halting run of that program from index
      0, the final states related. -/
  sim : ∀ (body : S.Body), gate body = true → ∀ (s : S.State) (b : M.MState) (s' : S.State),
    Pre body s b → S.Run body s s' →
    ∃ prog b', M.decode (encode body) = some prog ∧ M.Halts prog 0 b b' ∧ Post body s b s' b'

namespace AsmSim

variable {S : SrcSem} {M : IsaMachine} (A : AsmSim S M)

/-- The assembly simulation at a gate `g` that implies the gate of `A`. -/
def ofGate (g : S.Body → Bool) (hg : ∀ body, g body = true → A.gate body = true) :
    AsmSim S M where
  gate := g
  encode := A.encode
  Pre := A.Pre
  Post := A.Post
  sim := fun body h => A.sim body (hg body h)

/-- **A source run of a gated body gives a halting run of the decoded bytes.** From a
    machine state related at entry to the initial state of a source run of a gated body, the
    bytes of the body decode to a program that halts from index 0. -/
theorem halts {body : S.Body} (hg : A.gate body = true) {s s' : S.State} {b : M.MState}
    (hpre : A.Pre body s b) (hrun : S.Run body s s') :
    ∃ prog b', M.decode (A.encode body) = some prog ∧ M.Halts prog 0 b b' := by
  obtain ⟨prog, b', hd, hh, -⟩ := A.sim body hg s b s' hpre hrun
  exact ⟨prog, b', hd, hh⟩

/-- **The halting run of the decoded bytes has a leakage trace.** From a machine state
    related at entry to the initial state of a source run of a gated body, the decoded
    program has a run with a leakage trace from index 0 to a state related to the final
    source state. -/
theorem runL {body : S.Body} (hg : A.gate body = true) {s s' : S.State} {b : M.MState}
    (hpre : A.Pre body s b) (hrun : S.Run body s s') :
    ∃ prog b' t, M.decode (A.encode body) = some prog
      ∧ M.RunL (fun _ _ => True) prog 0 b t b' ∧ A.Post body s b s' b' := by
  obtain ⟨prog, b', hd, hh, hpost⟩ := A.sim body hg s b s' hpre hrun
  obtain ⟨t, ht⟩ := IsaMachine.halts_runL hh
  exact ⟨prog, b', t, hd, ht, hpost⟩

/-- The halting run of the decoded bytes of a gated body, as a run through calls. -/
theorem haltsC {body : S.Body} (hg : A.gate body = true) {s s' : S.State} {b : M.MState}
    (hpre : A.Pre body s b) (hrun : S.Run body s s') :
    ∃ prog b', M.decode (A.encode body) = some prog ∧ M.HaltsC prog 0 b b'
      ∧ A.Post body s b s' b' := by
  obtain ⟨prog, b', hd, hh, hpost⟩ := A.sim body hg s b s' hpre hrun
  exact ⟨prog, b', hd, IsaMachine.haltsC_of_halts hh, hpost⟩

end AsmSim

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
