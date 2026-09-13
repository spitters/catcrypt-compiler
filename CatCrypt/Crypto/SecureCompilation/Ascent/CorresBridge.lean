/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres

/-!
# Bridging `Corres` and `CorresJ` — the AutoCorres phase division, made explicit

`Corres` (over the flag-free scalar machine `semScalar : LowCT → SEnvScalar →
Option SEnvScalar`) and `CorresJ` (over the flag-carrying machine `runBlock :
JState 64 → List (JInstr 64) → JState 64`) are the ascent's two correspondence
relations. They share the abstract triple `(AState, P, fa)` but run over different
machines. The two bridges below connect the machines, and both map onto
AutoCorres's phase division (Cock–Klein–Sewell; Greenaway's thesis): **L1**
SIMPL→monad, **L2** local-variable lifting, **HL** heap abstraction, **WA** word
abstraction, **TS** type strengthening.

## The forgetful register view (`regEnv`)

`regEnv st` reads the `JState` register file as a scalar environment, at the
uniform word type `.sword 64`, **forgetting** the condition flags and the memory
axis. The state functor carries the concrete flag-carrying machine up to the
flag-free scalar machine.

## Bridge 1 — the forgetful morphism (`corresJ_forget_to_corres`): L1 + L2

A machine morphism transporting a `CorresJ` down to a `Corres`. It composes
AutoCorres's two lower phases:

* **L1 (SIMPL → monad).** `runBlock` is *total* (a hardware-style step relation, no
  failure); `semScalar` is `Option`-valued — the exception/failure monad. Crossing
  from the total machine to the `Option` machine introduces the monad. The
  `hmirror` hypothesis lands in `some _`, i.e. it discharges L1's "no-fault"
  obligation for the emitted fragment.
* **L2 (local-variable lifting).** `regEnv` turns the register file (hardware state)
  into named scalar variables — AutoCorres's L2 replaces the state-record encoding of
  locals with named variables; here the registers *are* the lifted locals.

The **flag axis** `regEnv` forgets makes `CorresJ` strictly lower than `Corres`: a
carry/borrow chain (`corresJ_sbb`) cannot be stated over `SEnvScalar` (no flag
field), so it is proved at the `CorresJ` level and only *then* forgotten.

## Bridge 2 — the shared-spec meet (`coRefine`): TS

Both relations are forward simulations of the **same** `(P, fa)` on the same
`AState`. `coRefine` states that a `Corres` and a `CorresJ` for one `fa` make the
scalar kernel and the assembly kernel two implementations of a single abstract
transition, both landing in `SR`-images of `fa a₀`. It is the whole-stack
coherence AutoCorres relies on: every phase's `corres` targets the *same* abstract
HOL program, so the phases compose (the **TS** endpoint — the pure abstract spec
they all strengthen to).

## The remaining phases (elsewhere in the ascent)

* **WA (word abstraction).** `wEnc : BitVec 64 → ZMod 2^64` (`Corres.lean`) and its
  `RelatedBinOp` squares — the `UInt64 ↝ Int/ZMod` step, entirely inside `Corres`.
* **HL (heap abstraction).** The `AArr`/memref layer (`ArrLoadLeaf`/`ArrStoreLeaf`)
  abstracting the dynamic-index memory axis `regEnv` forgets.
* **TS (type strengthening).** The total, failure-free `asemW`/`ascend_sound` over
  `IsAscendable` (`Ascend.lean`) — collapsing the `Option` monad to a pure spec.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The forgetful register view -/

/-- `regEnv st`: the `JState` register file read as a scalar `SEnvScalar` at the
    uniform word type `.sword 64`, **forgetting** flags and the memory axis. The
    state functor carrying the flag-carrying machine (`runBlock`) up to the
    flag-free scalar machine (`semScalar`). -/
def regEnv (st : JState 64) : SEnvScalar :=
  fun r => some ⟨.sword 64, st.regs r⟩

/-! ## Bridge 1 — the forgetful morphism (L1 + L2) -/

/-- **`corresJ_forget_to_corres`.** The forgetful transport: a `CorresJ` for the
    JInstr block `c_J` becomes a `Corres` for a scalar program `c_s` that mirrors
    `c_J`'s register effect (`hmirror`), through the pushforward state relation
    `fun env a => ∃ st, regEnv st = env ∧ SR_J st a`. This composes AutoCorres's L1
    (total machine → `Option` machine) and L2 (registers → scalar locals via
    `regEnv`); the flag axis is forgotten by `regEnv`. -/
theorem corresJ_forget_to_corres {AState : Type} (SR_J : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState)
    (c_J : List (JInstr 64)) (c_s : LowCT)
    (hJ : CorresJ SR_J P fa c_J)
    (hmirror : ∀ st, semScalar c_s (regEnv st) = some (regEnv (runBlock st c_J))) :
    Corres (fun env a => ∃ st, regEnv st = env ∧ SR_J st a) P fa c_s := by
  intro env a hSR hP
  obtain ⟨st, hst, hSRJ⟩ := hSR
  refine ⟨regEnv (runBlock st c_J), ?_, runBlock st c_J, rfl, hJ st a hSRJ hP⟩
  rw [← hst]; exact hmirror st

/-! ## Bridge 2 — the shared-spec meet (TS) -/

/-- **`coRefine`.** A `Corres` for `c_s` and a `CorresJ` for `c_J`, both for the
    same abstract transition `fa` under precondition `P`, exhibit the scalar kernel
    and the assembly kernel as two implementations of one abstract step: from a
    shared abstract point `a₀` (related on both sides) both concrete runs land in
    `SR`-images of `fa a₀`. The whole-stack coherence — every phase's `corres`
    targets the same abstract program (the TS endpoint). -/
theorem coRefine {AState : Type}
    (SR_s : SEnvScalar → AState → Prop) (SR_J : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState)
    (c_s : LowCT) (c_J : List (JInstr 64))
    (hS : Corres SR_s P fa c_s) (hJ : CorresJ SR_J P fa c_J)
    (env₀ : SEnvScalar) (st₀ : JState 64) (a₀ : AState)
    (hSs : SR_s env₀ a₀) (hSJ : SR_J st₀ a₀) (hP : P a₀) :
    (∃ env', semScalar c_s env₀ = some env' ∧ SR_s env' (fa a₀))
      ∧ SR_J (runBlock st₀ c_J) (fa a₀) :=
  ⟨hS env₀ a₀ hSs hP, hJ st₀ a₀ hSJ hP⟩

/-! ## Non-vacuity: the forgetful bridge on a matched constant-set kernel

`hmirror` is discharged by computation for the matched pair
(`RScalarSet name n`, `[.mov name (.imm n)]`): both write `BitVec.ofNat 64 n` to
`name`, so the scalar update of `regEnv st` equals `regEnv` of the moved `JState`.
This exhibits Bridge 1's `hmirror` as satisfiable (the transport is not vacuous). -/

/-- The scalar constant-set mirrors the JInstr immediate-`mov` on the register view:
    `semScalar (RScalarSet name n) (regEnv st) = some (regEnv (runBlock st [.mov …]))`.
    Both sides set `name := BitVec.ofNat 64 n` and agree off `name`. -/
theorem regEnv_mirror_setConst (name : String) (n : Nat) (st : JState 64) :
    semScalar (.RScalarSet name n) (regEnv st)
      = some (regEnv (runBlock st [.mov name (.imm n)])) := by
  simp only [semScalar]
  congr 1
  funext r
  simp only [regEnv, SEnvScalar.upd, runBlock_cons, runBlock_nil, evalInstr, x86_MOV,
    JOperand.eval, JState.setReg]
  by_cases hr : r = name
  · subst hr; simp
  · simp [hr]

/-- **Non-vacuity witness for Bridge 1.** Instantiating `corresJ_forget_to_corres`
    at the matched constant-set kernel yields a `Corres` from any `CorresJ`
    for the immediate-`mov` block — the forgetful transport fires on a real pair. -/
theorem corres_of_corresJ_setConst {AState : Type} (SR_J : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (name : String) (n : Nat)
    (hJ : CorresJ SR_J P fa [.mov name (.imm n)]) :
    Corres (fun env a => ∃ st, regEnv st = env ∧ SR_J st a) P fa (.RScalarSet name n) :=
  corresJ_forget_to_corres SR_J P fa [.mov name (.imm n)] (.RScalarSet name n) hJ
    (regEnv_mirror_setConst name n)

end CatCrypt.Crypto.SecureCompilation.Ascent
