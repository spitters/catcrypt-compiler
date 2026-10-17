/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaNode
public import CatCrypt.Crypto.SecureCompilation.Ascent.BlockHalts
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

A straight-line block `blk` followed by `ret` halts from every state in `runBlockA sa blk`
(`BlockHalts.halts_of_runBlockA`). A contract whose postconditions hold at `runBlockA s blk`
and whose write sets bound `runBlockA s blk` from every state satisfying a precondition is
then a contract of `runOf r (blk.map .op ++ [.ret])`, with the same constant-time hypothesis.
The checker `DecodedCT.bytesCTCheck` with no frame words gives that hypothesis for every
contract whose public relation implies agreement on its public entry set.

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
  (RunL halts_runL PubA FrameSep bytesCTCheck bytesCTCheck_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (runBlockA)
open CatCrypt.Crypto.SecureCompilation.Ascent.BlockHalts (halts_of_runBlockA)
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

/-- **A contract of a straight-line block.** Let every state `s` satisfying `C.pre a` satisfy
    `C.post a` at `runBlockA s blk` (`hpost`) and agree with `runBlockA s blk` outside
    `C.writes a s` (`hkeep`), and let the leaky runs of `blk` followed by `ret` from publicly
    related states satisfying a precondition have equal traces (`hct`). Then
    `runOf r (blk.map .op ++ [.ret])` meets `C`. -/
theorem contract_of_runBlockA {r : DoitRegime} {blk : List (JInstr 64)}
    {C : ContractSpec AState L α}
    (hpost : ∀ a s, (C.pre a).holds s → (C.post a).holds (runBlockA s blk))
    (hkeep : ∀ a s, (C.pre a).holds s → AgreeOn (C.writes a s)ᶜ s (runBlockA s blk))
    (hct : ConstantTimeRel
      (fun s₁ s₂ => C.pub s₁ s₂ ∧ (∃ a, (C.pre a).holds s₁) ∧ ∃ a, (C.pre a).holds s₂)
      (fun s t => ∃ s', RunL r (fun _ _ => True) (blk.map .op ++ [.ret]) 0 s t s')) :
    SContract (runOf r (blk.map .op ++ [.ret])) C := by
  have hfin : ∀ s s', Halts aMachine (blk.map .op ++ [.ret]) 0 s s' → s' = runBlockA s blk := by
    intro s s' hH
    obtain ⟨t, hR⟩ := halts_runL r hH
    obtain ⟨t', hR'⟩ := halts_runL r (halts_of_runBlockA blk s)
    exact (runL_det hR hR').2
  refine sContract_runOf_of_halts
    ⟨fun a s _ => ⟨(), _, halts_of_runBlockA blk s⟩, ?_, ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩ hct
  · intro a s _ s' hs hH
    rw [hfin s s' hH]
    exact hpost a s hs
  · intro a s _ s' hs hH
    rw [hfin s s' hH]
    exact hkeep a s hs

/-- **A contract of the bytes of a straight-line function.** When `decodeLprog bs` is the
    block `blk` followed by `ret`, a contract met by `runBlockA s blk` from its
    preconditions, with the constant-time hypothesis of `contract_of_runBlockA`, is a contract
    of `runOf r q` for the program `q` that `bs` decodes to. -/
theorem contract_of_block {r : DoitRegime} {bs : List (BitVec 8)} {blk : List (JInstr 64)}
    {C : ContractSpec AState L α} (hdec : decodeLprog bs = some (blk.map .op ++ [.ret]))
    (hpost : ∀ a s, (C.pre a).holds s → (C.post a).holds (runBlockA s blk))
    (hkeep : ∀ a s, (C.pre a).holds s → AgreeOn (C.writes a s)ᶜ s (runBlockA s blk))
    (hct : ConstantTimeRel
      (fun s₁ s₂ => C.pub s₁ s₂ ∧ (∃ a, (C.pre a).holds s₁) ∧ ∃ a, (C.pre a).holds s₂)
      (fun s t => ∃ s', RunL r (fun _ _ => True) (blk.map .op ++ [.ret]) 0 s t s')) :
    ∃ q, decodeLprog bs = some q ∧ SContract (runOf r q) C :=
  ⟨_, hdec, contract_of_runBlockA hpost hkeep hct⟩

/-- **The constant-time hypothesis from the byte-level checker.** If `bytesCTCheck r [] P q`
    holds and the public relation of `C` implies agreement on `P`, two leaky runs of `q` from
    publicly related states have equal traces. -/
theorem ctRel_of_bytesCTCheck {r : DoitRegime} {P : PubA} {q : List RInstr}
    {C : ContractSpec AState L α} (h : bytesCTCheck r [] P q = true)
    (hpub : ∀ s₁ s₂, C.pub s₁ s₂ → P.Agree s₁ s₂) :
    ConstantTimeRel
      (fun s₁ s₂ => C.pub s₁ s₂ ∧ (∃ a, (C.pre a).holds s₁) ∧ ∃ a, (C.pre a).holds s₂)
      (fun s t => ∃ s', RunL r (fun _ _ => True) q 0 s t s') := by
  have hok : ∀ sa i, (fun _ _ => True : AState → JInstr 64 → Prop) sa i → FrameSep [] sa i :=
    fun _ _ _ _ _ _ o ho => absurd ho List.not_mem_nil
  intro s₁ s₂ t₁ t₂ hp ⟨s₁', h₁⟩ ⟨s₂', h₂⟩
  exact bytesCTCheck_sound h s₁ s₂ t₁ t₂ (hpub _ _ hp.1) ⟨s₁', h₁.mono hok⟩ ⟨s₂', h₂.mono hok⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
