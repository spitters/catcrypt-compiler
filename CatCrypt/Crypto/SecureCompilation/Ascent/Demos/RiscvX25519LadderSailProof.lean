/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvPc64Refinement

/-!
# The RV64 Curve25519 ladder in the Sail model

`RiscvX25519LadderBytesProof.ladderProg_spec` states the ladder program over
`RiscvPc64.steps`. `SailRiscvPc64Refinement.fnSpec_sail` carries a function meeting `FnSpec`
to the Sail clauses, for a program whose instructions all have words. Here the two meet: the
Sail run of the ladder program from a related state returns to `ra` in a state related to
one `LadderPost` allows.

## Main results

* `ladderProg_ok`: every instruction of `ladderProg` has a word (`PInstOKb`), by
  `decide +kernel`.
* `x25519Ladder_sail`: the ladder program run by the Sail clauses meets the ladder
  specification.
* `x25519LadderSailBytes_correct`: the same for the program decoded from the encoded bytes.

## Scope

The Sail side is that of `SailRiscvPc64Refinement`: transcribed clauses over a flat
little-endian memory, with the simplifications listed there.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderSailProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvPc64Ref
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderLoopProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof

theorem ladderProg_ok : ladderProg.all PInstOKb = true := by decide +kernel

/-- **The ladder in Sail.** On a word-aligned base, from a Sail state related to a state
    satisfying `LadderPre`, with `PC` at the base, the Sail run of the ladder program returns
    to `ra` (bit 0 cleared) in a state related to one that `LadderPost` allows: the block
    holds `ladderN 255` of the ladder state it held, `s0..s11`, `sp` and `ra` are restored,
    and no byte outside the frames below `sp` and the field region of the block changed. -/
theorem x25519Ladder_sail (base : BitVec 64) (hb : base &&& 3 = 0) (st : MState64)
    (σ : SailSt) (hR : Rel st σ) (hpc : σ.PC = base) (hpre : LadderPre st) :
    ∃ n σ' st', sailRun ladderProg base n σ = some σ' ∧
      σ'.PC = st.regs.get "ra" &&& ~~~1 ∧ Rel st' σ' ∧ LadderPost st st' := by
  have h := ladderProg_spec base hb
  rw [show addrOf base 0 = base by simp [addrOf]] at h
  exact fnSpec_sail ladderProg base base hb ladderProg_ok h st σ hR hpc hpre

/-- **The encoded ladder in Sail.** The encoded bytes of the ladder program decode as 3098
    instructions `prog` whose Sail run, from any state related to one satisfying `LadderPre`
    with `PC` at a word-aligned base, returns to `ra` in a state related to one that
    `LadderPost` allows. -/
theorem x25519LadderSailBytes_correct :
    ∃ prog, decodePStream64 3098 (encodePBlock64 ladderProg) = some prog ∧
      ∀ (base : BitVec 64), base &&& 3 = 0 → ∀ (st : MState64) (σ : SailSt), Rel st σ →
        σ.PC = base → LadderPre st →
        ∃ n σ' st', sailRun prog base n σ = some σ' ∧
          σ'.PC = st.regs.get "ra" &&& ~~~1 ∧ Rel st' σ' ∧ LadderPost st st' :=
  ⟨ladderProg, ladderProg_decode, x25519Ladder_sail⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderSailProof.x25519LadderSailBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519LadderSailBytes_correct

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderSailProof.x25519Ladder_sail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519Ladder_sail

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderSailProof
