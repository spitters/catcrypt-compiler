/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth

@[expose] public section

set_option autoImplicit false

/-!
# Lifting the A1–A3 control-flow interpreters into the export-faithfulness chain (B3)

The straight-line export gate `ComLsemExportFaithfulMem`
(`JasminLsemGeneralFaithfulMem`) states the real content of "the emitted bytes
execute as `Com.denote`": run the emitted singleton program
(`singletonProgM fn …`, whose body is the linearizer-emitted `LinstrRM` list the
trusted `lsem→bytes` encoder turns into bytes) under the memref machine model
`lsemFuelMem` over `LstateM` from the encoded inputs, and the result register
`decodeM`s to `Com.denote`.  That gate is **straight-line only**.

The A1–A3 interpreter capabilities extended the machine model with control flow,
all over the **same** `LstateM` substrate:

* **A1** (`JasminLsemMemLoop.lsemFuelMemL`): `Llabel`/`Lcond`/`Lgoto` back-edges —
  counter loops over `LstateM`.  `loopMem_runBounded`: the emitted counter loop
  `loopLinstrRM` run by `lsemFuelMemL` realises the `m`-fold `runBoundedLoopMem`.
* **A2** (`JasminLsemMemLoopCall.lsemFuelMemLC`): a loop body may `Lcall` a linked
  owned leaf.  `loopCall_runBounded`: the emitted loop-with-call realises the
  call-resolving fold `runBoundedLoopMemC`.
* **A3** (`JasminLsemMemLoopNestWhile`): a data-dependent `while (nReg ≠ 0)`.
  `whileMem_realizes`: the emitted `whileLinstrRM` realises the do-while
  `runWhileMem`, the trip read off the run.
* **depth-N** (`JasminLsemMemLoopNestDepth.calleeRunDN`): arbitrary-depth nested
  region calls, `denote = spec` closed depth-indexed.

## What B3 is (the honest assessment)

`lsemFuelMemL`/`lsemFuelMemLC` are **conservative extensions** of the
straight-line `lsemFuelMem` the export gate is stated over: same `LstateM` base,
same `encodeM`/`decodeM`, same `singletonProgM`, same `findInstrMem[C]` fetch
(`body[lpc]?`) — only the *eval* arm gains control transfer / region calls.  So
there is **no genuine `LstateM` ↔ machine-model gap**: the export lift is a
**wrapper** that (a) re-expresses each A1–A3 run result in the export gate's
observable form — `decodeM t.base retReg w` at the result register — and (b)
records that the observed value is the source fold's denotation
(`runBoundedLoopMem` / `runBoundedLoopMemC` / `runWhileMem` /
`lsemStraightMemDN`), exactly as the static-loop template
`JasminLsemLoop.loop_lsem_correct` ties `lsemFuel` to the `bodyStep`-fold (not
directly to `JForProg` — that tie is `general_loopBody_lsem_faithful`, a separate
theorem).

The single bridge brick is `decodeM_congr_reg_lvm`: `decodeM` reads only
`reg.lvm` (via `LstateN.getW`), and every A1–A3 run result already proves the
halt state agrees with the source fold on `reg.lvm` (and on the array carrier).
So the emitted control-flow form's machine execution **observes the source fold
denotation** at the result register — the export statement, instantiated at the
loop / loop-with-call / data-dependent-while / arbitrary-depth-nest shapes.

These are NOT `rfl` shadows: each quantifies over the emitted instruction list
`singletonProgM fn (loopLinstrRM …)` / `whileLinstrRM …` executed by the machine
model `lsemFuelMemL[C]`, and discharges via the A1–A3 `*_runBounded` /
`whileMem_realizes` / `calleeRunDN` results (never re-proved here) composed with
`decodeM_congr_reg_lvm`.

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound} (+
`Lean.ofReduceBool` for the concrete depth-3 non-vacuity witness).**  The
`lsem→bytes` encoder + Sail tables remain the declared trusted base.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth

/-! ## 0. The bridge brick: `decodeM` reads only `reg.lvm` -/

/-- **`decodeM` depends only on `reg.lvm`.**  `decodeM st r w = st.reg.getW r w`,
    and `LstateN.getW` reads only the register value map `lvm`.  So two states
    agreeing on `reg.lvm` decode identically at every register / width.  This is
    the single brick turning each A1–A3 raw-state agreement (`t.base.reg.lvm =
    bfin.reg.lvm`) into the export gate's observable `decodeM`-agreement. -/
theorem decodeM_congr_reg_lvm (s1 s2 : LstateM) (h : s1.reg.lvm = s2.reg.lvm)
    (r : String) (w : Nat) : decodeM s1 r w = decodeM s2 r w := by
  unfold decodeM LstateN.getW
  rw [h]

/-- `setLpc` preserves the decode: it only moves the pc field, leaving `reg.lvm`
    unchanged. -/
theorem decodeM_setLpc (s : LstateM) (pc : Nat) (r : String) (w : Nat) :
    decodeM (s.setLpc pc) r w = decodeM s r w :=
  decodeM_congr_reg_lvm (s.setLpc pc) s (LstateM.reg_lvm_setLpc s pc) r w

/-! ## 1. A1 — the counter loop, lifted to the export gate

`loopMem_runBounded` gives the emitted counter loop's `lsemFuelMemL` run and its
agreement with the `m`-fold `runBoundedLoopMem` on `reg.lvm` + the array carrier.
Wrapping the `reg.lvm` half with `decodeM_congr_reg_lvm` gives the export
statement: the emitted loop's machine execution `decodeM`s at the result register
to the source loop's `m`-fold denotation. -/

/-- **A1 export faithfulness — the counter loop.**  For the emitted counter-loop
    program `singletonProgM fn (loopLinstrRM top nReg body)` with an all-`Lopn`
    body, run by the memref machine model `lsemFuelMemL` from the loop top
    (`lpc = 1`), under the public counter schedule (`hprev`/`hlast`/`hbfin`/
    `htaken`/`hhalt`), there is a halt state `t` whose result register `decodeM`s
    to the source loop's `m`-fold denotation `runBoundedLoopMem body m s.base =
    some bfin`.  Discharged by A1's `loopMem_runBounded` (never re-proved) +
    `decodeM_congr_reg_lvm`. -/
theorem loopMem_export_faithful (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem body (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem body bprev = some blast)
    (hbfin : runBoundedLoopMem body m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMem body i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false)
    (retReg : String) (w : Nat) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (body.length + 1)) s = some t
        ∧ decodeM t.base retReg w = decodeM bfin retReg w := by
  obtain ⟨t, ht, hreg, _harr⟩ := loopMem_runBounded fn top nReg body hlopn s hfn hpc m hm
    bprev blast bfin hprev hlast hbfin htaken hhalt
  exact ⟨t, ht, decodeM_congr_reg_lvm t.base bfin hreg retReg w⟩

/-! ## 2. A2 — the loop-with-region-call, lifted to the export gate -/

/-- **A2 export faithfulness — the loop that CALLS a linked leaf.**  For the
    emitted loop-with-call program `singletonProgM fn (loopLinstrRM top nReg
    body)` (body `BodyStepOK` — `Lopn ∪ call-to-a-linked-leaf`), run by the
    region-call machine model `lsemFuelMemLC` from the loop top, under the counter
    schedule, there is a halt state `t` whose result register `decodeM`s to the
    concrete-leaf fold `runBoundedLoopMemC env body m s.base = some bfin`.
    Discharged by A2's `loopCall_runBounded` + `decodeM_congr_reg_lvm`. -/
theorem loopCall_export_faithful (env : LeafEnvM) (fn : String) (top : LLabel)
    (nReg : String) (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (loopLinstrRM top nReg body)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMemC env body (m - 1) s.base = some bprev)
    (hlast : lsemStraightMemC env body bprev = some blast)
    (hbfin : runBoundedLoopMemC env body m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMemC env body i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false)
    (retReg : String) (w : Nat) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (fuelCostC env body + 1)) s = some t
        ∧ decodeM t.base retReg w = decodeM bfin retReg w := by
  obtain ⟨t, ht, hreg, _harr⟩ := loopCall_runBounded env fn top nReg body hok s hfn hpc m hm
    bprev blast bfin hprev hlast hbfin htaken hhalt
  exact ⟨t, ht, decodeM_congr_reg_lvm t.base bfin hreg retReg w⟩

/-! ## 3. A3 — the data-dependent `while`, lifted to the export gate

This is the PRIORITY lift (unblocks the `honest_prove` consumer per the plan):
the trip count is decided by the values the body produces, not a proof
parameter. -/

/-- **A3 export faithfulness — the data-dependent `while (nReg ≠ 0)`.**  For the
    emitted `whileLinstrRM top nReg [] body` run by `lsemFuelMemLC` from the loop
    top, if the do-while denotation `runWhileMem (condNZ nReg) body fuel` halts
    within `fuel` to `bfin`, there is a halt state `t` — reached in
    `whileTripsMem … * (fuelCostC body + 1)` steps, the trip **read off the run**,
    not supplied — whose result register `decodeM`s to `bfin`.  Discharged by A3's
    `whileMem_realizes` + `decodeM_congr_reg_lvm`.  The consumer supplies only a
    termination/variant `fuel`; the loop trip is data-dependent. -/
theorem whileMem_export_faithful (env : LeafEnvM) (fn : String) (top : LLabel)
    (nReg : String) (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (whileLinstrRM top nReg [] body)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg nReg)) body fuel s.base = some bfin)
    (retReg : String) (w : Nat) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn (whileLinstrRM top nReg [] body))
          (whileTripsMem env (fun b => condNZ b (.reg nReg)) body fuel s.base
            * (fuelCostC env body + 1)) s = some t
        ∧ decodeM t.base retReg w = decodeM bfin retReg w := by
  obtain ⟨t, ht, hreg, _harr⟩ := whileMem_realizes env fn top nReg body hok s hfn hpc fuel bfin hhalt
  exact ⟨t, ht, decodeM_congr_reg_lvm t.base bfin hreg retReg w⟩

/-! ## 4. depth-N — arbitrary-depth nested calls, lifted to the export gate

`calleeRunDN` is the closed depth-indexed nested-call denote (the C1/B4 residual
of A3, done at the interpreter level).  We lift it into a whole-run export
statement: entering a depth-`d` callee and running to a halted caller `decodes` at
the result register to the depth-`d` spec fold `lsemStraightMemDN env d
calleeBody`.  This is the lift that carries the arbitrary-depth nesting
`fri_proof` needs (layer ⊃ Merkle ⊃ query, depth-3+). -/

/-- **depth-N export faithfulness — arbitrary-depth nested calls.**  Given a
    depth-`d` callee `sym` (its body may call depth-`(d-1)` callees, recursively)
    whose depth-`d` spec fold runs `lsemStraightMemDN env d calleeBody
    (base.setLpc 0) = some b`, and a caller frame that halts immediately on return
    (`hcallerHalt`), the machine model `lsemFuelMemLC` runs the whole depth-`d`
    nested-call chain — in `fuelCostDN env d calleeBody + 1` steps — to a halt
    state `t` whose result register `decodeM`s to the depth-`d` spec fold result
    `b`.  Discharged by depth-N's `calleeRunDN` + `decodeM_congr_reg_lvm`. -/
theorem calleeRunDN_export_faithful (env : LeafEnvM) (P : LprogM) (d : Nat)
    (sym callerFn : String) (retPc : Nat) (calleeBody : List LinstrRM)
    (hbok : ∀ i ∈ calleeBody, NestBodyOK env P d i) (hne : sym ≠ P.lfn)
    (hsym : env sym = some (calleeBody ++ [(LinstrR.Lret, MemTag.reg none)]))
    (base b : LstateM) (rest : List (String × Nat))
    (hrun : lsemStraightMemDN env d calleeBody (base.setLpc 0) = some b)
    (hcallerHalt : findInstrMemC env P
      { base := b.setLpc retPc, lfn := callerFn, rstack := rest } = none)
    (retReg : String) (w : Nat) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env P (fuelCostDN env d calleeBody + 1)
          { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest } = some t
        ∧ decodeM t.base retReg w = decodeM b retReg w := by
  have hrun2 := calleeRunDN env P d sym callerFn retPc calleeBody hbok hne hsym base b rest 0 hrun
  rw [Nat.add_zero] at hrun2
  refine ⟨{ base := b.setLpc retPc, lfn := callerFn, rstack := rest }, ?_, ?_⟩
  · rw [hrun2, lsemFuelMemLC, hcallerHalt]
  · exact decodeM_setLpc b retPc retReg w

/-! ## 5. Non-vacuity: a concrete depth-3 nested-call export witness

The depth-3 tower `l1 → l2 → l3` (`JasminLsemMemLoopNestDepth.depth3Env`) run
from `acc = 5`, `t = 7`: the machine model runs the full depth-3 region-call
chain to a halt (the loop function `g` has an empty body, so the return frame
halts at fuel 0) and `decodeM`s `acc = 12`.  A concrete inhabitant of
`calleeRunDN_export_faithful` — the export lift is non-vacuous at a genuine
depth-3 nest. -/

/-- The depth-3 entry base: `acc = 5`, `t = 7`. -/
def depth3Base : LstateM :=
  (({} : LstateM).setReg "acc" (5#64)).setReg "t" (7#64)

/-- The depth-3 spec fold reaches a state (`= some b`); read off by `native_decide`
    from the interpreter's own `calleeRun_depth3_value`. -/
theorem depth3_fold_isSome :
    (lsemStraightMemDN depth3Env 2
        [(LinstrR.Lcall none ("l2", (0 : LLabel)), MemTag.reg none)]
        (depth3Base.setLpc 0)).isSome = true := by native_decide

/-- **Concrete depth-3 export witness (unconditional).**  Entering `l1` (which
    calls `l2`, which calls `l3`) over the shared `LstateM`, the machine model runs
    the genuine depth-3 region-call chain to a halt state `t` whose result register
    `acc` decodes to the depth-3 spec fold `b`'s `acc` (= `12`).  The spec fold
    reaches `some b` (`depth3_fold_isSome`), so the existence is unconditional —
    `calleeRunDN_export_faithful` is inhabited by a real arbitrary-depth nest, not
    vacuous. -/
theorem depth3_export_witness :
    ∃ (t : LstatePMC) (b : LstateM),
      lsemStraightMemDN depth3Env 2
          [(LinstrR.Lcall none ("l2", (0 : LLabel)), MemTag.reg none)] (depth3Base.setLpc 0)
        = some b ∧
      lsemFuelMemLC depth3Env depth3Prog
          (fuelCostDN depth3Env 2 [(LinstrR.Lcall none ("l2", (0 : LLabel)), MemTag.reg none)] + 1)
          { base := depth3Base.setLpc 0, lfn := "l1", rstack := ("g", 3) :: [] } = some t
        ∧ decodeM t.base "acc" 64 = decodeM b "acc" 64 := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp depth3_fold_isSome
  obtain ⟨t, ht, hdec⟩ := calleeRunDN_export_faithful depth3Env depth3Prog 2 "l1" "g" 3
    [(LinstrR.Lcall none ("l2", (0 : LLabel)), MemTag.reg none)] depth3_l1_body_ok
    (by decide) rfl depth3Base b [] hb
    -- the caller frame halts: `depth3Prog`'s body is empty, so the return pc is out of range.
    rfl "acc" 64
  exact ⟨t, b, hb, ht, hdec⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge
