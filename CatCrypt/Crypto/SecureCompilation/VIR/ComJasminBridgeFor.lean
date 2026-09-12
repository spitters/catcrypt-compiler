/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn
public import CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering

/-!
# The `Com ↔ Jasmin` bridge for the counted `Cfor` arm (`JForProg`)

`JasminPrint.JForProg.toCfor` emits a counted loop

```
Cfor i { dir := UpTo, lo := 0, hi := n } body
```

with an `int` loop index `i` and a straight-line body. This file relates the run
of that instruction under the `psem.v` mirror (`execInstrR`, `Cfor` arm
`execFor`) to the JasminPrint `Store`, for a body that is a mixed
`Cassgn`/rotate block (`ComJasminBridgeCopn.MixedBlockSim`).

## The loop invariant

The loop is described by three families indexed by the iteration number
`k ≤ n`: the JasminPrint stores `stores k`, the mirror states `states k` and the
register frames `frames k`. The invariant at `k` is
`StateCorrReg (frames k) (stores k) (states k).evm`. Iteration `k` writes the
index `i := Vint k` into the mirror state; since `i` is an `int` variable outside
every frame, the write preserves the invariant (`stateCorrReg_set_outside`), and
the body chain `MixedBlockSim` from the written state to `states (k+1)`
re-establishes it at `k+1` (`mixedBlock_simulates`). The index itself is tracked
on the mirror side only: after the write its slot holds `Vint k`.

## Contents

* `forRange`, `forInstr` — the mirror image of the emitted `Cfor`.
* `stateCorrReg_set_outside` — a write outside the frame preserves `StateCorrReg`.
* `wrange_upTo_zero` — the iteration list of `0..n` is `(List.range' 0 n).map Int.ofNat`.
* `ForBodySim` — the per-iteration body chains of the loop.
* `execFor_forBodySim` — the fuel-indexed loop run, by induction on the remaining count.
* `cfor_simulates` / `cfor_endToEnd` — the `Cfor` run reaches `states n` in
  `StateCorrReg`, and witnesses the relational `SemIr` step.
* `cfor_acc_eq_loopRun` — when each body chain advances a register accumulator by
  one `loopN` body step, the accumulator register of the final mirror state is
  the emitted counted-loop run `LoopLowering.loopRun` of `loopN n body`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFor

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The emitted loop and the index write -/

/-- The range `0..n` of the emitted counted loop. -/
def forRange (n : Nat) : Range := { dir := .UpTo, lo := .Pconst 0, hi := .Pconst n }

/-- The emitted counted loop over index `i` and body `body`. -/
def forInstr (i : VarI) (n : Nat) (body : List MixedStep) : InstrR :=
  .Cfor i (forRange n) (mixedBlockCmd body)

/-- Writing a variable `x` outside the frame `names` preserves `StateCorrReg`:
    no frame variable reads the written slot. -/
theorem stateCorrReg_set_outside (names : List Var) (st : Store) (vm : Vm)
    (x : Var) (v : Value) (hx : ∀ r ∈ names, r ≠ x)
    (hcorr : StateCorrReg names st vm) :
    StateCorrReg names st (vm.set x v) := by
  intro r hr
  have hget : (vm.set x v).get r = vm.get r := by
    simp [Vm.get, Vm.set, hx r hr]
  rw [hget]
  exact hcorr r hr

/-- The iteration list of the upward range `0..n` is `0, 1, …, n-1`. -/
theorem wrange_upTo_zero (n : Nat) :
    wrange .UpTo 0 (n : Int) = (List.range' 0 n).map Int.ofNat := by
  simp [wrange, List.range_eq_range']

/-! ## §2. The per-iteration body chains -/

/-- `ForBodySim aS gd opS i n body stores states frames`: for every iteration
    `k < n`, the body `body`, started at store `stores k`, at the mirror state
    `states k` with the index written `i := Vint k`, and at frame `frames k`, is
    a `MixedBlockSim` chain ending at `(stores (k+1), states (k+1), frames (k+1))`;
    and the index `i` is an `int` variable outside every frame. -/
structure ForBodySim (aS : AsmSem) (gd : GlobDecls) (opS : OpSem)
    (i : VarI) (n : Nat) (body : List MixedStep)
    (stores : Nat → Store) (states : Nat → Estate SyscallState Mem)
    (frames : Nat → List Var) : Prop where
  /-- The loop index is declared `int`. -/
  index_int : i.v_var.vtype = .aint
  /-- The loop index lies outside every frame of the loop. -/
  index_fresh : ∀ k ≤ n, ∀ r ∈ frames k, r ≠ i.v_var
  /-- Iteration `k` of the body is a mixed-block chain. -/
  step : ∀ k < n, MixedBlockSim aS gd opS body (stores k)
    ((states k).withVm ((states k).evm.set i.v_var (.Vint (Int.ofNat k))))
    (frames k) (stores (k + 1)) (states (k + 1)) (frames (k + 1))

omit [MemModel Mem] in
/-- Writing the `int` index `i := Vint z` succeeds and sets the slot. -/
theorem writeVar_index (i : VarI) (z : Int) (s : Estate SyscallState Mem)
    (hi : i.v_var.vtype = .aint) :
    writeVar (Mem := Mem) true i (.Vint z) s
      = .ok (s.withVm ((s.evm).set i.v_var (.Vint z))) := by
  unfold writeVar setVar
  rw [hi]
  simp only [DB, Value.isDefined, truncatable, Value.typeOf,
    Bool.not_true, decide_true, Bool.true_and]
  rfl

/-! ## §3. The loop run -/

/-- **The loop run from iteration `k`.** Under `ForBodySim`, with `m` iterations
    remaining from `k` (`k + m = n`) and the invariant at `k`, `execFor` over the
    remaining indices `k, …, n-1` at fuel `fuel + m + 1` reaches `states n`, and
    the invariant holds at `n`. -/
theorem execFor_forBodySim
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (i : VarI) (n : Nat) (body : List MixedStep)
    (stores : Nat → Store) (states : Nat → Estate SyscallState Mem)
    (frames : Nat → List Var)
    (hsim : ForBodySim aS gd opS i n body stores states frames) :
    ∀ (m k fuel : Nat), k + m = n →
      StateCorrReg (frames k) (stores k) (states k).evm →
      execFor (Mem := Mem) aS opS gd (fuel + m + 1) i
          ((List.range' k m).map Int.ofNat) (mixedBlockCmd body) (states k) prog
        = .ok (states n)
      ∧ StateCorrReg (frames n) (stores n) (states n).evm := by
  intro m
  induction m with
  | zero =>
    intro k fuel hk hcorr
    simp only [Nat.add_zero] at hk
    subst hk
    refine ⟨?_, hcorr⟩
    rw [List.range'_zero, List.map_nil]
    conv_lhs => rw [execFor]
  | succ m ih =>
    intro k fuel hk hcorr
    have hkn : k < n := by omega
    have hcorrW : StateCorrReg (frames k) (stores k)
        ((states k).evm.set i.v_var (.Vint (Int.ofNat k))) :=
      stateCorrReg_set_outside _ _ _ _ _ (hsim.index_fresh k (by omega)) hcorr
    obtain ⟨hbody, hcorr'⟩ :=
      mixedBlock_simulates aS opS gd prog body (stores k)
        ((states k).withVm ((states k).evm.set i.v_var (.Vint (Int.ofNat k))))
        (frames k) (stores (k + 1)) (states (k + 1)) (frames (k + 1)) (fuel + m)
        (hsim.step k hkn) hcorrW
    obtain ⟨hrest, hcorrN⟩ := ih (k + 1) fuel (by omega) hcorr'
    refine ⟨?_, hcorrN⟩
    rw [List.range'_succ, List.map_cons,
      show fuel + (m + 1) + 1 = (fuel + m + 1) + 1 by omega]
    conv_lhs => rw [execFor]
    show (do
        let s' ← writeVar (Mem := Mem) true i (.Vint (Int.ofNat k)) (states k)
        let s'' ← execCmd (Mem := Mem) aS opS gd (fuel + m + 1) s' (mixedBlockCmd body) prog
        execFor (Mem := Mem) aS opS gd (fuel + m + 1) i
          ((List.range' (k + 1) m).map Int.ofNat) (mixedBlockCmd body) s'' prog) = _
    rw [writeVar_index i _ _ hsim.index_int]
    show (do
        let s'' ← execCmd (Mem := Mem) aS opS gd (fuel + m + 1)
          ((states k).withVm ((states k).evm.set i.v_var (.Vint (Int.ofNat k))))
          (mixedBlockCmd body) prog
        execFor (Mem := Mem) aS opS gd (fuel + m + 1) i
          ((List.range' (k + 1) m).map Int.ofNat) (mixedBlockCmd body) s'' prog) = _
    rw [hbody]
    exact hrest

/-- **Simulation for the emitted counted loop.** Under `ForBodySim` and the
    invariant `StateCorrReg (frames 0) (stores 0) (states 0).evm`, the mirror run
    of `Cfor i (0..n) body` at fuel `fuel + n + 2` returns `.ok (states n)`, and
    `StateCorrReg (frames n) (stores n) (states n).evm` holds. -/
theorem cfor_simulates
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (i : VarI) (n : Nat) (body : List MixedStep)
    (stores : Nat → Store) (states : Nat → Estate SyscallState Mem)
    (frames : Nat → List Var) (fuel : Nat)
    (hsim : ForBodySim aS gd opS i n body stores states frames)
    (hcorr : StateCorrReg (frames 0) (stores 0) (states 0).evm) :
    execInstrR (Mem := Mem) aS opS gd (fuel + n + 2) (states 0) (forInstr i n body) prog
      = .ok (states n)
    ∧ StateCorrReg (frames n) (stores n) (states n).evm := by
  obtain ⟨hrun, hcorrN⟩ :=
    execFor_forBodySim aS opS gd prog i n body stores states frames hsim n 0 fuel
      (Nat.zero_add n) hcorr
  refine ⟨?_, hcorrN⟩
  rw [show fuel + n + 2 = (fuel + n + 1) + 1 by omega, forInstr,
    OpSemCoverage.execInstrR_Cfor_eq]
  show execFor (Mem := Mem) aS opS gd (fuel + n + 1) i
      (wrange .UpTo 0 (n : Int)) (mixedBlockCmd body) (states 0) prog = _
  rw [wrange_upTo_zero]
  exact hrun

/-- **End-to-end bridge for the emitted counted loop.** Under the hypotheses of
    `cfor_simulates`, the `Cfor` witnesses the relational step `SemIr` from
    `states 0` to `states n`, and `states n` corresponds to `stores n` on
    `frames n`. -/
theorem cfor_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (i : VarI) (n : Nat) (body : List MixedStep)
    (stores : Nat → Store) (states : Nat → Estate SyscallState Mem)
    (frames : Nat → List Var)
    (hsim : ForBodySim aS gd opS i n body stores states frames)
    (hcorr : StateCorrReg (frames 0) (stores 0) (states 0).evm) :
    SemIr (Mem := Mem) aS opS gd prog (states 0) (forInstr i n body) (states n)
    ∧ StateCorrReg (frames n) (stores n) (states n).evm := by
  obtain ⟨hrun, hcorrN⟩ :=
    cfor_simulates aS opS gd prog i n body stores states frames 0 hsim hcorr
  exact ⟨execInstrR_sound (n := 0 + n + 2) aS opS gd prog hrun, hcorrN⟩

/-! ## §4. The accumulator and the emitted counted-loop run -/

/-- **The final accumulator register is the emitted loop run.** Let `acc` be a
    register of width `sz` in the final frame. Suppose the JasminPrint store
    holds `init` at `acc` before the loop, and each body chain advances it by one
    step of the single-op body `lbody`. If the final mirror state holds
    `Vword sz x` at `acc`, then `x` is the counted-loop run
    `loopRun (loopN n lbody) (bodyStepRun leafSem (loopN n lbody)) init` of
    `LoopLowering`, and the mirror `Cfor` reaches that state. -/
theorem cfor_acc_eq_loopRun
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (i : VarI) (n : Nat) (body : List MixedStep)
    (stores : Nat → Store) (states : Nat → Estate SyscallState Mem)
    (frames : Nat → List Var)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (sz : WSize) (lbody : LoopLowering.LoopBody (.reg sz.bits))
    (acc : VarI) (init x : BitVec sz.bits)
    (hsim : ForBodySim aS gd opS i n body stores states frames)
    (hcorr : StateCorrReg (frames 0) (stores 0) (states 0).evm)
    (hinit : Store.get (stores 0) acc.v_var.vname (.reg sz.bits) = init)
    (hadv : ∀ k < n, Store.get (stores (k + 1)) acc.v_var.vname (.reg sz.bits)
        = lbody.denote (.cons (Store.get (stores k) acc.v_var.vname (.reg sz.bits)) .nil))
    (hmem : acc.v_var ∈ frames n)
    (hfinal : (states n).evm.get acc.v_var = .Vword sz x) :
    SemIr (Mem := Mem) aS opS gd prog (states 0) (forInstr i n body) (states n)
    ∧ x = JForProgCT.loopRun (LoopLowering.loopN n lbody)
        (JForProgSemCorrect.bodyStepRun leafSem (LoopLowering.loopN n lbody)) init := by
  obtain ⟨hsem, hcorrN⟩ :=
    cfor_endToEnd aS opS gd prog i n body stores states frames hsim hcorr
  refine ⟨hsem, ?_⟩
  rw [LoopLowering.loopN_lower_denote_iterate hLeaf n lbody init]
  have hstore : ∀ k ≤ n, Store.get (stores k) acc.v_var.vname (.reg sz.bits)
      = (fun a => lbody.denote (.cons a .nil))^[k] init := by
    intro k
    induction k with
    | zero => intro _; exact hinit
    | succ k ih =>
      intro hk
      rw [hadv k (by omega), ih (by omega), Function.iterate_succ_apply']
  have hx := (pvar_read_corr (SyscallState := SyscallState) (Mem := Mem) gd opS
    (states n) (stores n) (frames n) acc sz x hcorrN hmem hfinal).2
  rw [← hx]
  exact hstore n le_rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFor
