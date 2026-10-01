/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Proof
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvPc64Refinement

/-!
# RV64 X25519 in the Sail model

`RiscvX25519Proof.x25519Prog_spec` and `x25519CProg_spec` state the X25519 block function
and the C function `catcrypt_x25519` over `RiscvPc64.steps`.
`SailRiscvPc64Refinement.fnSpec_sail` carries them to the Sail clauses, as
`RiscvX25519LadderSailProof` does for the ladder alone.

## Main results

* `x25519_sail`: the X25519 program run by the Sail clauses from instruction 3098 meets
  `X25519Pre` and `X25519Post`.
* `x25519C_sail`: the same from instruction 4213 meets `X25519CPre` and `X25519CPost`.
* `x25519SailBytes_correct`, `x25519CSailBytes_correct`: the same for the program decoded
  from the encoded bytes.

## Scope

The Sail side is that of `SailRiscvPc64Refinement`: the register clauses excerpted in
`SailRiscv64Refinement` and the `ld`, `sd`, `bne`, `jal` and `jalr` clauses transcribed from
the sail-riscv 0.13.1 extraction, over a flat little-endian byte memory with no address
translation or PMP. Instructions come from the decoded instruction list, mapped to Sail
instructions by `toInstr`; the word decoder is the project's `decodePStream64`, not Sail's
`encdec`. No constant-time or leakage property is proved.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519SailProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvPc64Ref
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Proof

/-- **X25519 in Sail.** On a word-aligned base, from a Sail state related to a state
    satisfying `X25519Pre`, with `PC` at instruction 3098, the Sail run of the X25519 program
    returns to `ra` (bit 0 cleared) in a state related to one that `X25519Post` allows: the
    block holds `x25519 k u` at offset 64, `s0..s11`, `sp` and `ra` are restored, and no byte
    outside the frame below `sp` and the block changed. -/
theorem x25519_sail (base : BitVec 64) (hb : base &&& 3 = 0) (st : MState64) (σ : SailSt)
    (hR : Rel st σ) (hpc : σ.PC = addrOf base 3098) (hpre : X25519Pre st) :
    ∃ n σ' st', sailRun x25519Prog base n σ = some σ' ∧
      σ'.PC = st.regs.get "ra" &&& ~~~1 ∧ Rel st' σ' ∧ X25519Post st st' :=
  fnSpec_sail x25519Prog base _ hb x25519Prog_ok (x25519Prog_spec base hb) st σ hR hpc hpre

/-- **`catcrypt_x25519` in Sail.** On a word-aligned base, from a Sail state related to a
    state satisfying `X25519CPre`, with `PC` at instruction 4213, the Sail run of the X25519
    program returns to `ra` (bit 0 cleared) in a state related to one that `X25519CPost`
    allows: `out` holds `x25519 k u` for the scalar at `scalar` and `u` at `u`, `s0..s11`, `sp`
    and `ra` are restored, and no byte outside the 848 bytes below `sp` and `out` changed. -/
theorem x25519C_sail (base : BitVec 64) (hb : base &&& 3 = 0) (st : MState64) (σ : SailSt)
    (hR : Rel st σ) (hpc : σ.PC = addrOf base 4213) (hpre : X25519CPre st) :
    ∃ n σ' st', sailRun x25519Prog base n σ = some σ' ∧
      σ'.PC = st.regs.get "ra" &&& ~~~1 ∧ Rel st' σ' ∧ X25519CPost st st' :=
  fnSpec_sail x25519Prog base _ hb x25519Prog_ok (x25519CProg_spec base hb) st σ hR hpc hpre

/-- **The encoded X25519 program in Sail.** The encoded bytes decode as 4246 instructions
    `prog` whose Sail run from instruction 3098, from any state related to one satisfying
    `X25519Pre` at a word-aligned base, returns to `ra` in a state related to one that
    `X25519Post` allows. -/
theorem x25519SailBytes_correct :
    ∃ prog, decodePStream64 4246 (encodePBlock64 x25519Prog) = some prog ∧
      ∀ (base : BitVec 64), base &&& 3 = 0 → ∀ (st : MState64) (σ : SailSt), Rel st σ →
        σ.PC = addrOf base 3098 → X25519Pre st →
        ∃ n σ' st', sailRun prog base n σ = some σ' ∧
          σ'.PC = st.regs.get "ra" &&& ~~~1 ∧ Rel st' σ' ∧ X25519Post st st' :=
  ⟨x25519Prog, x25519Prog_decode, x25519_sail⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519SailProof.x25519SailBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519SailBytes_correct

/-- **The encoded `catcrypt_x25519` in Sail.** The encoded bytes decode as 4246 instructions
    `prog` whose Sail run from instruction 4213, from any state related to one satisfying
    `X25519CPre` at a word-aligned base, returns to `ra` in a state related to one that
    `X25519CPost` allows. -/
theorem x25519CSailBytes_correct :
    ∃ prog, decodePStream64 4246 (encodePBlock64 x25519Prog) = some prog ∧
      ∀ (base : BitVec 64), base &&& 3 = 0 → ∀ (st : MState64) (σ : SailSt), Rel st σ →
        σ.PC = addrOf base 4213 → X25519CPre st →
        ∃ n σ' st', sailRun prog base n σ = some σ' ∧
          σ'.PC = st.regs.get "ra" &&& ~~~1 ∧ Rel st' σ' ∧ X25519CPost st st' :=
  ⟨x25519Prog, x25519Prog_decode, x25519C_sail⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519SailProof.x25519CSailBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519CSailBytes_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519SailProof
