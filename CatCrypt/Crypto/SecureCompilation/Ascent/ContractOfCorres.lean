/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaNode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSig
public import CatCrypt.Crypto.SecureCompilation.SepLogic.Contract

@[expose] public section

set_option autoImplicit false

/-!
# Contracts of the leaky run of a decoded block from a two-phase correspondence

The callee of a decoded block `q` under a leakage regime `r` is the run relation `runOf r q`
(the leaky runs `RunL` of `q` from index `0`). The leaky run and the halting run of the
address machine `aMachine` have the same final states (`halts_runL`, `RunL.halts`), and the
leaky run is deterministic (`runL_det`). A contract of the halting run, with the trace
`Unit`, is then a contract of `runOf r q` once the traces of `runOf r q` from publicly related
entry states that satisfy a precondition are equal (`ConstantTimeRel`).

A two-phase correspondence `CorresIsaRun x86Isa P (phaseSR fn Entry dec layout Exit)
(phasePre PreS) (phaseAbs spec)` states, for each entry state `sa` satisfying `PreS` and
related by `Entry` to a flag-machine state of the function `fn`, that the address machine
halts on `layout` from `sa` in a state satisfying `Exit sa · (spec sa)`. A contract whose
preconditions give `PreS` and `Entry`, whose postconditions follow from `Exit`, and whose
write sets bound the halting runs is then a contract of `runOf r layout`.

## Main results

* `sContract_runOf_of_halts`: a contract of the halting run on `q` and a constant-time
  hypothesis on the leaky runs give the same contract of `runOf r q`.
* `contract_of_corresIsa`: a two-phase correspondence over `x86Isa`, with an entry, a post,
  a keep and a constant-time hypothesis, gives a contract of `runOf r layout`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.SepLogic
open Footprinted
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL halts_runL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (runL_det)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel DoitRegime)

variable {L : Type} [Footprinted AState L] {α : Type}

/-- **A contract of the halting run is a contract of the leaky run.** Let the halting run of
    `aMachine` on `q` from index `0`, with the trace `Unit`, meet `C`, and let two leaky runs
    of `q` from entry states related by `C.pub` that satisfy a precondition have equal traces.
    Then `runOf r q` meets `C`. -/
theorem sContract_runOf_of_halts {r : DoitRegime} {q : List RInstr} {C : ContractSpec AState L α}
    (h : SContract (fun s (_ : Unit) s' => Halts aMachine q 0 s s') C)
    (hct : ConstantTimeRel
      (fun s₁ s₂ => C.pub s₁ s₂ ∧ (∃ a, (C.pre a).holds s₁) ∧ ∃ a, (C.pre a).holds s₂)
      (fun s t => ∃ s', RunL r (fun _ _ => True) q 0 s t s')) :
    SContract (runOf r q) C where
  halts a s hs := by
    obtain ⟨-, s', hH⟩ := h.halts a s hs
    obtain ⟨t, hR⟩ := halts_runL r hH
    exact ⟨t, s', hR⟩
  post a s t s' hs hR := by
    obtain ⟨-, s'', hH⟩ := h.halts a s hs
    obtain ⟨t'', hR''⟩ := halts_runL r hH
    obtain rfl := (runL_det hR hR'').2
    exact h.post a s () s' hs hH
  keep a s t s' hs hR := by
    obtain ⟨-, s'', hH⟩ := h.halts a s hs
    obtain ⟨t'', hR''⟩ := halts_runL r hH
    obtain rfl := (runL_det hR hR'').2
    exact h.keep a s () s' hs hH
  ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hR₁ hR₂ :=
    hct s₁ s₂ t₁ t₂ ⟨hp, ⟨a₁, h₁⟩, ⟨a₂, h₂⟩⟩ ⟨s₁', hR₁⟩ ⟨s₂', hR₂⟩

/-- **A contract from a two-phase correspondence.** Let `P` correspond over `x86Isa` to
    `phaseAbs spec` under the two-phase relation and precondition. Assume `hentry`: a state
    satisfying `C.pre a` satisfies `PreS` and is related by `Entry` to some flag-machine
    memory and flag; `hpost`: from such a state, an exit state satisfying `Exit` at
    `spec s` satisfies `C.post a`; `hkeep`: a halting run of `layout` from such a state keeps
    the locations outside `C.writes a s`; and `hct`: the leaky runs of `layout` from publicly
    related states satisfying a precondition have equal traces. Then `runOf r layout` meets
    `C`. -/
theorem contract_of_corresIsa {O : Type} {r : DoitRegime} {P : LprogM} {fn : String}
    {Entry : AState → LstateM → Bool → Prop} {dec : LstateM → Option O}
    {layout : List RInstr} {Exit : AState → AState → O → Prop} {spec : AState → O}
    {PreS : AState → Prop} {C : ContractSpec AState L α}
    (hc : CorresIsaRun x86Isa P (phaseSR fn Entry dec layout Exit) (phasePre PreS)
      (phaseAbs spec))
    (hentry : ∀ a s, (C.pre a).holds s → PreS s ∧ ∃ b zf, Entry s b zf)
    (hpost : ∀ a s s', (C.pre a).holds s → Exit s s' (spec s) → (C.post a).holds s')
    (hkeep : ∀ a s s', (C.pre a).holds s → Halts aMachine layout 0 s s' →
      AgreeOn (C.writes a s)ᶜ s s')
    (hct : ConstantTimeRel
      (fun s₁ s₂ => C.pub s₁ s₂ ∧ (∃ a, (C.pre a).holds s₁) ∧ ∃ a, (C.pre a).holds s₂)
      (fun s t => ∃ s', RunL r (fun _ _ => True) layout 0 s t s')) :
    SContract (runOf r layout) C := by
  have hexit : ∀ a s, (C.pre a).holds s →
      ∃ s', Halts aMachine layout 0 s s' ∧ Exit s s' (spec s) := by
    intro a s hs
    obtain ⟨hpre, b, zf, hE⟩ := hentry a s hs
    obtain ⟨-, -, -, -, s', hH, hX⟩ :=
      hc { prog := { base := b, lfn := fn }, zf := zf } ⟨s, none⟩ ⟨rfl, hE⟩ ⟨rfl, hpre⟩
    exact ⟨s', hH, hX⟩
  refine sContract_runOf_of_halts
    ⟨?_, ?_, fun a s _ s' => hkeep a s s', fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩ hct
  · intro a s hs
    obtain ⟨s', hH, -⟩ := hexit a s hs
    exact ⟨(), s', hH⟩
  · intro a s _ s' hs hH
    obtain ⟨s'', hH'', hX⟩ := hexit a s hs
    obtain ⟨t, hR⟩ := halts_runL r hH
    obtain ⟨t'', hR''⟩ := halts_runL r hH''
    obtain rfl := (runL_det hR hR'').2
    exact hpost a s s' hs hX

end CatCrypt.Crypto.SecureCompilation.Ascent
