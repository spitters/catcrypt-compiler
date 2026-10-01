/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderLoopProof

/-!
# The RV64 Curve25519 ladder at its encoded bytes

`ladderProg` is a whole program for the program-counter machine `RiscvPc64`, 3098
instructions. It holds the ladder function at instruction 0, the swap function, the ladder
step function and the five field-operation functions, each a call target of the ones
before it. Its bytes are `RiscvPc64.encodePBlock64 ladderProg`.

## Main results

* `ladderProg_decode`: the bytes decode back to `ladderProg`, by `decide +kernel` on the
  decoder.
* `ladderProg_spec`: on a word-aligned base, the function at the base meets `FnSpec` with
  `LadderPre` and `LadderPost`.
* `x25519LadderBytes_correct`: the same, stated over the decoded bytes.
* `x25519Ladder_init`: from the initial ladder state of RFC 7748 §5, the run leaves 255
  iterations of `x25519LadderStepVerified` in the block.

## Scope

The final inversion `x2 / z2` and the scalar clamping and decoding of RFC 7748 §5 are not
in the program. That `RiscvPc64.step` agrees with an RV64 processor is not proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof (memLimbs4)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderLoopProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof (FeOp)

/-- The instruction of the function of a field operation. -/
def fnIdx : FeOp → Nat
  | .add => 226
  | .sub => 453
  | .mul => 710
  | .sqr => 1784
  | .a24 => 2862

/-- The X25519 ladder program: the ladder function at instruction 0, the swap at 74, the
    step at 146, then the five field-operation functions. -/
def ladderProg : List PInst64 :=
  ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146 ++ fnCode (phys .add) ++
    fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24)

theorem ladderProg_length : ladderProg.length = 3098 := by decide +kernel

theorem ladderProg_decode :
    decodePStream64 3098 (encodePBlock64 ladderProg) = some ladderProg := by decide +kernel

theorem fnCode_length (k : List MInst64) : (fnCode k).length = (bufFn k).length + 1 := by
  simp [fnCode]

theorem fn_at (base : BitVec 64) (op : FeOp) (pre post : List PInst64)
    (h : ladderProg = pre ++ fnCode (phys op) ++ post) (hl : pre.length = fnIdx op) :
    FnSpec ladderProg base (addrOf base (fnIdx op)) (BufPre op.pre) (BufPost op.eval) := by
  have hL := congrArg List.length h
  rw [ladderProg_length, List.length_append, List.length_append, fnCode_length] at hL
  rw [← hl, h]
  exact fnSpec_buf pre post base (phys op) op.eval op.pre (phys_correct op) (phys_sp_ra op).1
    (phys_sp_ra op).2 (by omega)

theorem fnSpecs (base : BitVec 64) :
    ∀ op, FnSpec ladderProg base (addrOf base (fnIdx op)) (BufPre op.pre) (BufPost op.eval) := by
  intro op
  cases op
  · exact fn_at base .add (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146)
      (fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24))
      (by simp [ladderProg]) (by decide +kernel)
  · exact fn_at base .sub (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146
        ++ fnCode (phys .add))
      (fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24))
      (by simp [ladderProg]) (by decide +kernel)
  · exact fn_at base .mul (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146
        ++ fnCode (phys .add) ++ fnCode (phys .sub))
      (fnCode (phys .sqr) ++ fnCode (phys .a24))
      (by simp [ladderProg]) (by decide +kernel)
  · exact fn_at base .sqr (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146
        ++ fnCode (phys .add) ++ fnCode (phys .sub) ++ fnCode (phys .mul))
      (fnCode (phys .a24))
      (by simp [ladderProg]) (by decide +kernel)
  · exact fn_at base .a24 (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146
        ++ fnCode (phys .add) ++ fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr))
      [] (by simp [ladderProg]) (by decide +kernel)

/-- **The ladder program.** On a word-aligned base, the function at instruction 0 meets
    `FnSpec` with `LadderPre` and `LadderPost`. -/
theorem ladderProg_spec (base : BitVec 64) (hb : base &&& 3 = 0) :
    FnSpec ladderProg base (addrOf base 0) LadderPre LadderPost := by
  have hC : FnSpec ladderProg base (addrOf base 74) CswapPre CswapPost := by
    have := fnSpec_cswap (ladderCode 74 146 0) (stepCode fnIdx 146 ++ fnCode (phys .add) ++
      fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24)) base
      (by rw [ladderCode_length]; decide)
    rw [ladderCode_length] at this
    convert this using 1
    simp [ladderProg]
  have hS : FnSpec ladderProg base (addrOf base 146) StepPre StepPost := by
    have hl : (ladderCode 74 146 0 ++ cswapCode).length = 146 := by
      rw [List.length_append, ladderCode_length]; rfl
    have := fnSpec_step ladderProg base hb fnIdx (fun op => by cases op <;> decide)
      (fnSpecs base) (ladderCode 74 146 0 ++ cswapCode) (fnCode (phys .add) ++
      fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24))
      (by rw [hl]; simp [ladderProg]) (by rw [hl]; decide)
    rwa [hl] at this
  exact fnSpec_ladder ladderProg base hb 74 146 (by decide) (by decide) hC hS [] _
    (by simp [ladderProg]; rfl) (by decide)

open CatCrypt.Util (X25519State)
open CatCrypt.Util.Fp25519 (fromNat)

theorem addrOf_zero (base : BitVec 64) : addrOf base 0 = base := by simp [addrOf]

/-- **The encoded X25519 ladder.** The bytes of `ladderProg` decode as 3098 instructions
    `prog` such that, loaded at any word-aligned `base`, the function at `base` meets
    `FnSpec` with `LadderPre` and `LadderPost`: from every state whose 240 bytes below `sp`
    are disjoint from the 576-byte state block at `a0`, with `z2`, `z3 ≤ 2·p25519` and `sp`,
    `a0` 16- and 8-byte aligned, a run
    returns to `ra` with the block holding `ladderN 255` of the ladder state it held,
    `s0..s11`, `sp` and `ra` restored, and no byte outside the frames below `sp` and the field
    region of the block changed. -/
theorem x25519LadderBytes_correct :
    ∃ prog, decodePStream64 3098 (encodePBlock64 ladderProg) = some prog ∧
      ∀ base : BitVec 64, base &&& 3 = 0 → FnSpec prog base base LadderPre LadderPost :=
  ⟨ladderProg, ladderProg_decode, fun base hb => by
    have := ladderProg_spec base hb
    rwa [addrOf_zero] at this⟩

/-- **From the initial ladder state.** When the block holds `x2 = 1`, `z2 = 0`, `x3 = x1`,
    `z3 = 1` and the scalar `K`, a run of the ladder program returns to `ra` with the block
    holding the RFC 7748 ladder of `K` on the base point `x1`, as 255 iterations of
    `x25519LadderStepVerified`. -/
theorem x25519Ladder_init (base : BitVec 64) (hb : base &&& 3 = 0) (st : MState64)
    (hpre : LadderPre st) (hx2 : fe st.mem (st.regs.get "a0") "x2" = 1)
    (hz2 : fe st.mem (st.regs.get "a0") "z2" = 0)
    (hx3 : fe st.mem (st.regs.get "a0") "x3" = fe st.mem (st.regs.get "a0") "x1")
    (hz3 : fe st.mem (st.regs.get "a0") "z3" = 1) :
    ∃ n st', steps ladderProg base n ⟨base, st⟩ = some ⟨st.regs.get "ra" &&& ~~~1, st'⟩ ∧
      Holds st'.mem (st.regs.get "a0") (ladderN 255 (X25519State.init
        (memLimbs4 st.mem (st.regs.get "a0")) (fromNat (fe st.mem (st.regs.get "a0") "x1")))) := by
  obtain ⟨n, st', hrun, hpost, -⟩ := ladderProg_spec base hb st hpre
  rw [addrOf_zero] at hrun
  refine ⟨n, st', hrun, ?_⟩
  have e : blockState st.mem (st.regs.get "a0") = X25519State.init
      (memLimbs4 st.mem (st.regs.get "a0")) (fromNat (fe st.mem (st.regs.get "a0") "x1")) := by
    simp only [blockState, X25519State.init, hx2, hz2, hx3, hz3, fromNat, Nat.cast_one,
      Nat.cast_zero]
  rw [← e]
  exact hpost

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof.x25519LadderBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519LadderBytes_correct

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof.x25519Ladder_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519Ladder_init

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof
