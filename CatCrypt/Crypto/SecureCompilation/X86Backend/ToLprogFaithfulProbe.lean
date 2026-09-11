/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-!
# `toLprogPhysAbi` faithfulness — the two-address-lowering fragment (probe)

The proven straight-line faithfulness `comToLprog_faithful_straightline`
(`JasminLsemSimulation.lean`) ties `Com.denote` to `lsemStraight` over the
**virtual** linearizer `Com.toLprog` — three-address `Lopn [dst] op [s0, s1]`
instructions over fresh `regName`/`argName` operands.

The **shipped** x86 path `Com.toLprogPhysAbi` applies two further passes on top
of that virtual body, neither of which the proven waist covers:

1. **linear-scan register allocation + spilling** (`physMap` / `physBody` /
   `remapOperand`): a logical→physical slot map over a `Nat` universe, identity
   on the live set's first `13` registers, spilling the rest to `k.N` stack
   cells (`JasminLprogExport.lean:1069` `physMap`, `:1353` `physBody`);
2. **two-address legalization** (`lowerTwoAddr`, `JasminLprogExport.lean:1192`):
   the destructive rewrite `dst = op s0 s1  ↦  mov dst, s0 ; op dst, s1`
   (collapsing the `mov` when `dst = s0`), plus spill-reload threading through
   the reserved scratches `R15`/`R14`.

This module discharges, against the increment-1 linear machine
`JasminLsem.lsemStraight`, the **core semantic obligation that pass (2)
introduces in the no-spill register case**: the two-instruction expansion
`mov dst, s0 ; op dst, s1` computes, at `dst`, exactly what the original
three-address `Lopn [dst] op [s0, s1]` computes — **provided `dst ≠ s1`** (else
the leading `mov` clobbers the second source before the op reads it). This is
the `lsem`/`LinstrR` analogue of `ScalarLinX86Demo.hstep_x86_on` (which proves
the same fact over the `X86Backend.Model` register machine `xrun`/`XState`).

What is **not** proved here (the residual, named honestly):
* the register-allocation pass `physMap`/`physBody` preserves the denotation
  (the `RegMachineSim` keystone `jinstr_renameBlock_sound` proves this for the
  `JInstr`/`JState` machine under a *uniform* renaming `ρ`, but `physBody` is
  not a uniform renaming — it inserts the two-address `mov`s and spill reloads,
  so the keystone does not directly apply to the `LinstrR` body);
* the spill cases of `legalizeBinop` (the `R15`/`R14` reload sequences);
* the ABI prologue/epilogue (`buildPrologue`/`buildEpilogue`) and the `Lret`
  terminator (control flow, out of increment-1 scope).

So this is **not** a `toLprogPhysAbi` faithfulness theorem; it is the proof of
the single new ingredient pass (2) needs, isolated and verified against the
real `lsemStraight` semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProbe

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-- The no-spill register two-address expansion of one binop: `mov dst, s0` then
    `op dst, s1`, with `dst`, `s0`, `s1` plain register names. This is exactly
    `legalizeMov ++ legalizeBinop` of `lowerTwoAddr` on the `(¬dst.isSpill,
    ¬s0.isSpill, ¬s1.isSpill)`, `dst ≠ s0` branch — written out concretely so the
    probe needs no `isSpill`/`materializeWideImm` reasoning. The op mnemonic is
    taken already width-tag-stripped (so `lsemStep`'s `stripWidthTag opn` is the
    identity on it), matching the bare `ADD/SUB/.../XOR` alphabet `applyOpn`
    models. -/
def twoAddrExpand (dst s0 s1 : String) (opn : String) : List LinstrR :=
  [ .Lopn [.reg dst] "MOV" [.reg s0],
    .Lopn [.reg dst] opn [.reg dst, .reg s1] ]

/-- `stripWidthTag "MOV" = "MOV"` — the bare move mnemonic carries no `:64` tag.
    (`String.endsWith` is `Slice`-based and does not reduce by plain `rfl`; closed
    by kernel evaluation, the pattern `JasminLsemSimulation` uses for these.) -/
theorem stripWidthTag_MOV : stripWidthTag "MOV" = "MOV" := by
  unfold stripWidthTag; decide +kernel

/-- **The two-address-lowering fragment of `toLprogPhysAbi` faithfulness.**

    Running the two-instruction expansion `mov dst, s0 ; op dst, s1` under the
    linear machine `lsemStraight` writes, at `dst`, the value
    `applyOpn opn [s.lvm s0, s.lvm s1]` — i.e. exactly the result of the original
    three-address `Lopn [dst] op [s0, s1]` (whose `lsemStep` is
    `applyOpn opn [eval s0, eval s1]`). The hypothesis `hds : dst ≠ s1` is the
    freshness side condition the de Bruijn front guarantees (the destination of a
    binding is strictly fresher than every source); without it the leading `mov`
    would clobber `s1`.

    `opn` is taken width-tag-stripped (`hstrip : stripWidthTag opn = opn`), so it
    is one of the modeled bare word ops (`ADD/SUB/MUL/AND/OR/XOR/SHL/SHR/ANDN`);
    the premise `hop : applyOpn opn [s.lvm s0, s.lvm s1] = some v` both selects a
    modeled op and names its result `v`. -/
theorem twoAddrExpand_lsem {w : Nat} (s : Lstate w) (dst s0 s1 opn : String)
    (hds : dst ≠ s1) (hstrip : stripWidthTag opn = opn) (v : BitVec w)
    (hop : applyOpn opn [s.lvm s0, s.lvm s1] = some v) :
    ∃ s', lsemStraight (twoAddrExpand dst s0 s1 opn) s = some s' ∧ s'.lvm dst = v := by
  -- Step 1: `mov dst, s0` writes `s.lvm s0` to `dst` and bumps the pc.
  have hmov : lsemStep (LinstrR.Lopn [.reg dst] "MOV" [.reg s0]) s
      = some ((s.setReg dst (s.lvm s0)).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, stripWidthTag_MOV,
      applyOpn]
  -- The post-`mov` store: `dst ↦ s.lvm s0`, every other register unchanged.
  let s1State : Lstate w := (s.setReg dst (s.lvm s0)).nextPc
  -- `op dst, s1` reads `dst` (= `s.lvm s0`) and `s1` (= `s.lvm s1`, since
  -- `dst ≠ s1`), applies `opn`, writes `dst`.
  have heval_dst : evalOperand s1State (.reg dst) = s.lvm s0 := by
    show evalOperand ((s.setReg dst (s.lvm s0)).nextPc) (.reg dst) = s.lvm s0
    simp [evalOperand, Lstate.setReg, Lstate.nextPc]
  have heval_s1 : evalOperand s1State (.reg s1) = s.lvm s1 := by
    show evalOperand ((s.setReg dst (s.lvm s0)).nextPc) (.reg s1) = s.lvm s1
    simp only [evalOperand, Lstate.setReg, Lstate.nextPc, if_neg (Ne.symm hds)]
  have hop2 : lsemStep (LinstrR.Lopn [.reg dst] opn [.reg dst, .reg s1]) s1State
      = some ((s1State.setReg dst v).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, heval_dst, heval_s1, hstrip, hop]
  refine ⟨(s1State.setReg dst v).nextPc, ?_, ?_⟩
  · -- run the two instructions in sequence
    show lsemStraight (twoAddrExpand dst s0 s1 opn) s = some ((s1State.setReg dst v).nextPc)
    simp only [twoAddrExpand, lsemStraight, hmov]
    rw [hop2]
  · -- read back `dst`: the second write put `v` there
    show ((s1State.setReg dst v).nextPc).lvm dst = v
    simp [Lstate.setReg, Lstate.nextPc]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProbe
