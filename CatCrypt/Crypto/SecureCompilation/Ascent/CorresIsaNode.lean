/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop

@[expose] public section

set_option autoImplicit false

/-!
# A flag-machine node as a correspondence over the x86 instruction set

A node is an `Lprog` program run by the flag machine `lsemFuelMemF` beside a decoded machine
program run by the address machine `RInstrAddrMem.aMachine`. This module states the pair of
runs as one correspondence `CorresIsa` at `X86Isa.x86Isa`, at a fixed fuel.

The abstract state `PhaseAbs O` is a machine entry state `sa` of the decoded program together
with an optional output in `O`: `none` before the run, `some out` after it. The abstraction
`phaseAbs spec` sets the output to `spec sa`. The relation `phaseSR fn Entry dec layout Exit`
reads, before the run, the entry relation `Entry` between the flag-machine state and `sa`;
after the run, it states that the decoder `dec` reads the output from the flag-machine state
and that the address machine halts on `layout` from `sa` in a state satisfying `Exit` at the
output. The precondition `phasePre PreS` is `PreS` at the entry state with no output yet.

## Main results

* `PhaseAbs`, `phaseAbs`, `phaseSR`, `phasePre`: the two-phase abstract state, abstraction,
  relation and precondition over an arbitrary output type.
* `corresIsa_of_node_halts_fuel`: `CorresIsa x86Isa` at a fixed fuel for a program with a
  two-machine run at bounded fuel and an export statement.
* `corresIsa_of_node_halts_spec`: the same correspondence from a single two-machine run whose
  flag-machine end state decodes to the specification.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (lsemFuelMemF_det)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

variable {O : Type}

/-- A two-phase abstract state over outputs `O`: a machine entry state and the output,
    `none` before the run. -/
structure PhaseAbs (O : Type) where
  /-- The machine entry state of the decoded function bytes. -/
  sa : AState
  /-- The output, present after the run. -/
  out : Option O

/-- The abstraction of a run with specification `spec`: the output is `spec` of the entry
    state. -/
def phaseAbs (spec : AState → O) (a : PhaseAbs O) : PhaseAbs O :=
  { a with out := some (spec a.sa) }

/-- The two-phase relation between a flag-machine state and an abstract state. Before the
    run the state is in the function `fn` and satisfies `Entry`. After the run the decoder
    `dec` reads the output from the flag-machine state, and the address machine halts on
    `layout` from the entry state in a state satisfying `Exit` at the output. -/
def phaseSR (fn : String) (Entry : AState → LstateM → Bool → Prop)
    (dec : LstateM → Option O) (layout : List RInstr) (Exit : AState → AState → O → Prop)
    (t : LstateMF) (a : PhaseAbs O) : Prop :=
  match a.out with
  | none => t.prog.lfn = fn ∧ Entry a.sa t.prog.base t.zf
  | some out =>
      dec t.prog.base = some out ∧ ∃ sa', Halts aMachine layout 0 a.sa sa' ∧ Exit a.sa sa' out

/-- The two-phase precondition: no output yet, and `PreS` at the entry state. -/
def phasePre (PreS : AState → Prop) (a : PhaseAbs O) : Prop :=
  a.out = none ∧ PreS a.sa

/-- **A node as a fixed-fuel correspondence.** Let `P` be a flag-machine program. Assume
    `hnode`: from states related by `Entry` under `PreS`, the address machine halts on
    `layout`, the flag machine halts in one state `t` at every fuel from `fuelAt sa` on, and
    `t` decodes to an output satisfying `Exit`. Assume `hexport`: from the same states the
    flag machine halts at some fuel in a state decoding to `spec sa`. If `fuelAt sa ≤ fuel`
    under `PreS`, then `P` corresponds at fuel `fuel` to `phaseAbs spec` under the two-phase
    relation and precondition. -/
theorem corresIsa_of_node_halts_fuel (P : LprogM) (fn : String)
    (Entry : AState → LstateM → Bool → Prop) (dec : LstateM → Option O)
    (layout : List RInstr) (Exit : AState → AState → O → Prop) (spec : AState → O)
    (PreS : AState → Prop) (fuelAt : AState → Nat) (fuel : Nat)
    (hfuel : ∀ sa, PreS sa → fuelAt sa ≤ fuel)
    (hnode : ∀ sa b zf, PreS sa → Entry sa b zf →
      ∃ sa' t, Halts aMachine layout 0 sa sa'
        ∧ (∀ k, fuelAt sa ≤ k →
            lsemFuelMemF P k { prog := { base := b, lfn := fn }, zf := zf } = some t)
        ∧ ∃ out, dec t.prog.base = some out ∧ Exit sa sa' out)
    (hexport : ∀ sa b zf, PreS sa → Entry sa b zf →
      ∃ k t, lsemFuelMemF P k { prog := { base := b, lfn := fn }, zf := zf } = some t
        ∧ dec t.prog.base = some (spec sa)) :
    CorresIsa x86Isa P (phaseSR fn Entry dec layout Exit) (phasePre PreS) (phaseAbs spec)
      fuel := by
  rintro ⟨⟨b, lfn⟩, zf⟩ ⟨sa, o⟩ hSR ⟨ho, hpre⟩
  simp only at ho hpre
  subst ho
  obtain ⟨hfn, hE⟩ := hSR
  simp only at hfn hE
  subst hfn
  obtain ⟨sa', t, hhalt, hrun, out, hout, hexit⟩ := hnode sa b zf hpre hE
  obtain ⟨k', t', hrun', hdec⟩ := hexport sa b zf hpre hE
  have hrunF := hrun fuel (hfuel sa hpre)
  obtain rfl := lsemFuelMemF_det _ fuel k' _ t t' hrunF hrun'
  obtain rfl : out = spec sa := Option.some.inj (hout.symm.trans hdec)
  exact ⟨t, by rw [x86Isa_lsemFuelMemF]; exact hrunF, hout, sa', hhalt, hexit⟩

/-- **A node as a fixed-fuel correspondence, from one run.** `corresIsa_of_node_halts_fuel`
    when the two-machine run `hnode` already ends in a flag-machine state decoding to
    `spec sa`. -/
theorem corresIsa_of_node_halts_spec (P : LprogM) (fn : String)
    (Entry : AState → LstateM → Bool → Prop) (dec : LstateM → Option O)
    (layout : List RInstr) (Exit : AState → AState → O → Prop) (spec : AState → O)
    (PreS : AState → Prop) (fuelAt : AState → Nat) (fuel : Nat)
    (hfuel : ∀ sa, PreS sa → fuelAt sa ≤ fuel)
    (hnode : ∀ sa b zf, PreS sa → Entry sa b zf →
      ∃ sa' t, Halts aMachine layout 0 sa sa'
        ∧ (∀ k, fuelAt sa ≤ k →
            lsemFuelMemF P k { prog := { base := b, lfn := fn }, zf := zf } = some t)
        ∧ dec t.prog.base = some (spec sa) ∧ Exit sa sa' (spec sa)) :
    CorresIsa x86Isa P (phaseSR fn Entry dec layout Exit) (phasePre PreS) (phaseAbs spec)
      fuel := by
  refine corresIsa_of_node_halts_fuel P fn Entry dec layout Exit spec PreS fuelAt fuel hfuel
    (fun sa b zf hpre hE => ?_) (fun sa b zf hpre hE => ?_)
  · obtain ⟨sa', t, hhalt, hrun, hdec, hexit⟩ := hnode sa b zf hpre hE
    exact ⟨sa', t, hhalt, hrun, _, hdec, hexit⟩
  · obtain ⟨_, t, _, hrun, hdec, _⟩ := hnode sa b zf hpre hE
    exact ⟨_, t, hrun _ (Nat.le_refl _), hdec⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
