/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall

@[expose] public section

set_option autoImplicit false

/-!
# Nested region-calls and a data-dependent `while` over `LstateM` (capability A3)

A1 (`JasminLsemMemLoop`) ran a **straight-line** loop body over the memref state
`LstateM`; A2 (`JasminLsemMemLoopCall`) let the loop body **call a linked owned
leaf** (all-`Lopn`) via `Lcall`, giving `loopCall_runBounded` — the `n`-fold of a
call-containing body for a **fixed** trip `m` supplied (with its counter schedule)
by the consumer.  This module (A3) closes the backend loop machinery with the two
remaining shapes:

## 1. NESTING (depth-2 region calls)

A2's `callee_run` requires the callee body to be **all-`Lopn`**.  Here `segCallG`
generalises A2's `segCallC` to run a straight-line-with-calls segment of **any**
current function (the loop function *or* an env-fetched callee), and `callee_run2`
uses it to run a callee whose **own body may contain a region call** (`BodyStepOK`
— `Lopn ∪ call-to-a-linked-leaf`).  So a call to a depth-2 callee (a leaf whose
body itself calls a leaf) denotes the nested inline fold `lsemStraightMemC` — the
`honest_prove` GGM / `ConvertToVole` nested-call shape.  The concrete
loop→leaf→leaf run and a true inline nested loop are validated by `native_decide`.

## 2. DATA-DEPENDENT `while` (runtime-determined trip)

`runWhileMem` is the fuel-bounded do-while denotation over `LstateM`: run the
call-resolving body-fold, and *continue while a runtime guard on the out-state
holds* — the trip count is **determined by the values the body produces** (the
counter register `nReg` the body decrements), not a fixed proof parameter.
`whileTripsMem` is that data-dependent trip count, and `runWhileMem_halts_schedule`
proves a terminating `runWhileMem` **reconstructs** the fixed-`m` counter schedule
A2's `loopCall_runBounded` consumes.  `whileMem_runWhile` composes the two: the
emitted counter-loop (`whileLinstrRM = loopLinstrRM`) run by `lsemFuelMemLC`
realises `runWhileMem` — the consumer supplies only the fuel (a
decreasing-measure/variant bound) and the fact that the guard goes false within
it; the trip count is read off the run.

## Validation

`§ Validate` checks by `native_decide`: (a) a nested loop→leaf→leaf run decodes to
the expected fold; (b) a true inline nested loop (outer × inner, distinct labels)
decodes to the doubly-nested fold; (c) a data-dependent `while (n != 0)` whose body
does `n -= 1` and `acc += buf[i]` decodes to the fold, the trip determined by the
initial `n`, and agrees with `runWhileMem`.

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound} (+ `Lean.ofReduceBool`
for the `native_decide` validates).**

### Reported residual (arbitrary-depth mutual recursion)

`callee_run2` gives depth-2 nesting with the **correct** callee cost
(`fuelCostC env calleeBody`, a call-aware fold).  Composing a depth-2 callee back
*into* A2's loop-with-calls bridge at the theorem level is the residual: A2's
per-call cost `stepCostC = |env sym| + 1` assumes an all-`Lopn` callee (each
instruction one step), so it undercounts a callee whose body itself calls.  A
fully general (arbitrary-depth) nested-loop/nested-call bridge needs a
depth-indexed / well-founded `fuelCost` recursing on call-graph depth; the
interpreter already *runs* arbitrary nesting (validated below), only the closed
cost accounting is depth-2-bounded.  Likewise an *inline* nested loop realises the
doubly-nested fold at run time (validated), but a closed inline-nested-loop theorem
needs a control-flow-aware (not `Lopn ∪ call`) segment lemma.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall

/-! ## 1. `segCallG` — the straight-line-with-calls segment for ANY current function

A2's `segCallC` runs a `BodyStepOK` segment of the **loop function** (`s.lfn =
P.lfn`, body `P.body`).  `segCallG` generalises the current function to an
arbitrary `cf` with body `curBodyC env P cf` — so it applies both to the loop
function *and* to an env-fetched callee, the enabler for a callee whose body itself
calls (depth-2 nesting).  The proof mirrors `segCallC` verbatim, replacing
`P.body`/`P.lfn` with `curBodyC env P cf`/`cf`. -/
theorem segCallG (env : LeafEnvM) (P : LprogM) (cf : String) :
    ∀ (seg : List LinstrRM) (s : LstatePMC) (f : Nat),
      s.lfn = cf →
      (∀ i ∈ seg, BodyStepOK env P i) →
      (∀ k, k < seg.length → (curBodyC env P cf)[s.base.lpc + k]? = seg[k]?) →
      lsemFuelMemLC env P (fuelCostC env seg + f) s
        = (lsemStraightMemC env seg s.base).bind
            (fun b => lsemFuelMemLC env P f { s with base := b }) := by
  intro seg
  induction seg with
  | nil =>
      intro s f _ _ _
      simp only [fuelCostC_nil, Nat.zero_add, lsemStraightMemC_nil, Option.bind_some]
  | cons i is ih =>
      intro s f hfn hok hpos
      have hcur : curBodyC env P s.lfn = curBodyC env P cf := by rw [hfn]
      have hii : BodyStepOK env P i := hok i (by simp)
      have his : ∀ j ∈ is, BodyStepOK env P j := fun j hj => hok j (by simp [hj])
      have hfetch : findInstrMemC env P s = some i := by
        unfold findInstrMemC; rw [hcur]
        have := hpos 0 (by simp); simpa using this
      have hpostail : ∀ (b : LstateM), b.lpc = s.base.lpc + 1 →
          ∀ k, k < is.length →
            (curBodyC env P cf)[({ s with base := b } : LstatePMC).base.lpc + k]? = is[k]? := by
        intro b hb k hk
        have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
        show (curBodyC env P cf)[b.lpc + k]? = is[k]?
        rw [hb, show s.base.lpc + 1 + k = s.base.lpc + (k + 1) from by omega, hp]; simp
      rw [fuelCostC_cons]
      rcases hii with hlopn | ⟨ra, sym, lbl, hcall, hcOK⟩
      · -- `Lopn`: cost 1, mirror A2.
        have hcost : stepCostC env i = 1 := by
          obtain ⟨d, o, src, hd⟩ := hlopn; unfold stepCostC; rw [hd]
        rw [hcost, show 1 + fuelCostC env is + f = (fuelCostC env is + f) + 1 from by omega,
          lsemFuelMemLC, hfetch]
        simp only []
        rw [evalInstrPMemLC_lopn env P i s hlopn]
        rw [lsemStraightMemC_cons, lsemStepMemC_lopn env i s.base hlopn]
        cases hstep : lsemStepMem i s.base with
        | none => simp
        | some b =>
            simp only [Option.map_some]
            have hb_lpc : b.lpc = s.base.lpc + 1 := lsemStepMem_lpc_succ i s.base b hstep
            have hfn' : ({ s with base := b } : LstatePMC).lfn = cf := hfn
            have := ih { s with base := b } f hfn' his (hpostail b hb_lpc)
            simpa using this
      · -- region call: cost `|env sym| + 1`, discharged by A2's `callee_run`.
        obtain ⟨hne, leafOps, hsym, hleafLopn⟩ := hcOK
        have hcost : stepCostC env i = leafOps.length + 2 := by
          unfold stepCostC; rw [hcall]
          simp only [hsym, Option.getD_some, List.length_append, List.length_cons,
            List.length_nil]
        rw [hcost,
          show leafOps.length + 2 + fuelCostC env is + f
            = (leafOps.length + 1 + (fuelCostC env is + f)) + 1 from by omega,
          lsemFuelMemLC, hfetch]
        simp only []
        have henter : evalInstrPMemLC env P i s
            = some { base := s.base.setLpc 0, lfn := sym,
                     rstack := (s.lfn, s.base.lpc + 1) :: s.rstack } := by
          unfold evalInstrPMemLC; rw [hcall]; simp only []; rw [hsym]
        rw [henter]
        simp only []
        rw [lsemStraightMemC_cons]
        unfold lsemStepMemC
        rw [hcall]
        simp only []
        unfold calleeEffect
        rw [hsym]
        simp only [List.dropLast_concat]
        cases hleaf : lsemStraightMem leafOps (s.base.setLpc 0) with
        | none =>
            simp only [Option.map_none, Option.bind_none]
            exact callee_run_none env P sym s.lfn (s.base.lpc + 1) leafOps hleafLopn hne hsym
              s.base (fuelCostC env is + f) s.rstack hleaf
        | some b =>
            simp only [Option.map_some]
            have hcallee := callee_run env P sym s.lfn (s.base.lpc + 1) leafOps hleafLopn hne
              hsym s.base b s.rstack (fuelCostC env is + f) hleaf
            rw [hcallee]
            have hbset_lpc : (b.setLpc (s.base.lpc + 1)).lpc = s.base.lpc + 1 := rfl
            have := ih { base := b.setLpc (s.base.lpc + 1), lfn := s.lfn,
                          rstack := s.rstack } f hfn his (hpostail _ hbset_lpc)
            have hstateEq :
                ({ base := b.setLpc (s.base.lpc + 1), lfn := s.lfn, rstack := s.rstack }
                    : LstatePMC)
                  = { s with base := b.setLpc (s.base.lpc + 1) } := by
              cases s; rfl
            rw [hstateEq] at *
            exact this

/-! ## 2. `callee_run2` — a callee whose body itself calls (depth-2 nesting)

The A2 `callee_run` is the all-`Lopn` callee sub-run.  `callee_run2` relaxes the
callee body to `BodyStepOK` (its instructions may be region calls to linked
leaves), giving the **depth-2 nested denote**: entering a callee whose body itself
calls a leaf runs the call-resolving fold `lsemStraightMemC env calleeBody` then
`Lret`-pops back to the caller.  The callee sub-run is `segCallG` (over the callee
function `sym`); the trailing `Lret` pops the frame. -/
theorem callee_run2 (env : LeafEnvM) (P : LprogM) (sym callerFn : String) (retPc : Nat)
    (calleeBody : List LinstrRM)
    (hbok : ∀ i ∈ calleeBody, BodyStepOK env P i)
    (hne : sym ≠ P.lfn)
    (hsym : env sym = some (calleeBody ++ [(LinstrR.Lret, MemTag.reg none)]))
    (base b : LstateM) (rest : List (String × Nat)) (f : Nat)
    (hrun : lsemStraightMemC env calleeBody (base.setLpc 0) = some b) :
    lsemFuelMemLC env P (fuelCostC env calleeBody + 1 + f)
        { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest }
      = lsemFuelMemLC env P f
          { base := b.setLpc retPc, lfn := callerFn, rstack := rest } := by
  have hcur : curBodyC env P sym = calleeBody ++ [(LinstrR.Lret, MemTag.reg none)] := by
    unfold curBodyC; rw [if_neg hne, hsym]; rfl
  have hseg := segCallG env P sym calleeBody
      { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest } (1 + f)
      rfl hbok
      (by intro k hk
          show (curBodyC env P sym)[(base.setLpc 0).lpc + k]? = calleeBody[k]?
          rw [hcur]
          simp only [LstateM.lpc_setLpc, Nat.zero_add]
          rw [List.getElem?_append_left (by simpa using hk)])
  rw [show fuelCostC env calleeBody + 1 + f = fuelCostC env calleeBody + (1 + f) from by omega,
    hseg, hrun, Option.bind_some]
  have hb_lpc : b.lpc = calleeBody.length := by
    have := lsemStraightMemC_lpc (P := P) env calleeBody hbok (base.setLpc 0) b hrun
    simpa using this
  have hfetchRet : findInstrMemC env P
      { base := b, lfn := sym, rstack := (callerFn, retPc) :: rest }
        = some (LinstrR.Lret, MemTag.reg none) := by
    unfold findInstrMemC
    show (curBodyC env P sym)[b.lpc]? = _
    rw [hcur, hb_lpc, List.getElem?_append_right (by simp)]
    simp
  rw [show 1 + f = f + 1 from by omega, lsemFuelMemLC, hfetchRet]
  simp only []
  unfold evalInstrPMemLC
  simp only []

/-! ## 3. `runWhileMem` / `whileTripsMem` — the data-dependent do-while denotation

`runWhileMem env guard body fuel s` runs the do-while
`repeat { s := body-fold s } while (guard on the out-state)` for at most `fuel`
iterations, resolving each body-fold via A2's call-aware `lsemStraightMemC` and
resetting the pc to `1` (the loop top) after each taken back-edge.  Unlike A2's
`runBoundedLoopMemC` (a *fixed* trip count), the trip is decided by `guard` on the
values the body produces — the data-dependent `while (nReg != 0)` shape.  `fuel = 0`
returns `none` (the do-while runs the body at least once when entered), so any
`some` result is a genuine termination within `fuel`. -/
def runWhileMem (env : LeafEnvM) (guard : LstateM → Bool) (body : List LinstrRM) :
    Nat → LstateM → Option LstateM
  | 0, _ => none
  | k + 1, s =>
      match lsemStraightMemC env body s with
      | some b => if guard b then runWhileMem env guard body k (b.setLpc 1) else some b
      | none => none

theorem runWhileMem_succ (env : LeafEnvM) (guard : LstateM → Bool) (body : List LinstrRM)
    (k : Nat) (s : LstateM) :
    runWhileMem env guard body (k + 1) s =
      match lsemStraightMemC env body s with
      | some b => if guard b then runWhileMem env guard body k (b.setLpc 1) else some b
      | none => none := rfl

/-- The **data-dependent trip count**: the number of do-while iterations before the
    guard goes false, bounded by `fuel`.  Unknown at entry — fixed at run time by
    the values the body produces (the counter the body decrements). -/
def whileTripsMem (env : LeafEnvM) (guard : LstateM → Bool) (body : List LinstrRM) :
    Nat → LstateM → Nat
  | 0, _ => 0
  | k + 1, s =>
      match lsemStraightMemC env body s with
      | some b => if guard b then whileTripsMem env guard body k (b.setLpc 1) + 1 else 1
      | none => 0

theorem whileTripsMem_succ (env : LeafEnvM) (guard : LstateM → Bool) (body : List LinstrRM)
    (k : Nat) (s : LstateM) :
    whileTripsMem env guard body (k + 1) s =
      match lsemStraightMemC env body s with
      | some b => if guard b then whileTripsMem env guard body k (b.setLpc 1) + 1 else 1
      | none => 0 := rfl

/-- The emitted **data-dependent** counter-loop back-edge over `LstateM`: label;
    body; the (possibly empty) guard-compute segment materialising the predicate
    into `gReg`; the conditional back-edge `Lcond (.reg gReg) top`.  Folding the
    guard-compute into the loop-body tail, this is exactly A2's `loopLinstrRM` on
    the extended body — so all the A2 loop machinery (`loopCall_runBounded`,
    `segCallC`) applies.  The `LstateM`/`LinstrRM` analogue of
    `X86Backend.LprogControlFlow.whileLcmd`. -/
def whileLinstrRM (top : LLabel) (gReg : String) (guardCompute body : List LinstrRM) :
    List LinstrRM := loopLinstrRM top gReg (body ++ guardCompute)

theorem whileLinstrRM_eq (top : LLabel) (gReg : String) (guardCompute body : List LinstrRM) :
    whileLinstrRM top gReg guardCompute body = loopLinstrRM top gReg (body ++ guardCompute) :=
  rfl

/-- `setLpc` leaves the register value map unchanged (only the pc field moves). -/
theorem LstateM.reg_lvm_setLpc (s : LstateM) (pc : Nat) :
    (s.setLpc pc).reg.lvm = s.reg.lvm := rfl

/-- `setLpc` leaves the array carrier unchanged. -/
theorem LstateM.larr_setLpc (s : LstateM) (pc : Nat) :
    (s.setLpc pc).larr = s.larr := rfl

/-! ## 4. A `runBoundedLoopMemC` shift lemma -/

/-- Peel one leading body-fold off a `runBoundedLoopMemC`: if the first fold from
    `s0` is `some b`, an `(i+1)`-fold from `s0` is an `i`-fold from `b.setLpc 1`. -/
theorem runBoundedLoopMemC_succ_shift (env : LeafEnvM) (body : List LinstrRM)
    (s0 b : LstateM) (i : Nat) (hb : lsemStraightMemC env body s0 = some b) :
    runBoundedLoopMemC env body (i + 1) s0 = runBoundedLoopMemC env body i (b.setLpc 1) := by
  rw [runBoundedLoopMemC_succ, hb, Option.bind_some]

/-! ## 5. `runWhileMem_halts_schedule` — a terminating do-while reconstructs the
    fixed-`m` counter schedule A2's `loopCall_runBounded` consumes

This is the data-dependent core: a `runWhileMem` that halts within `fuel` yields
its trip count `m = whileTripsMem …` and *proves* the counter schedule
(`0 < m`, the `(m-1)`-fold `bprev` whose last body-fold is the result, the `m`-fold,
and "guard true after each of the first `m-1` iterations") — the very hypotheses
A2's `loopCall_runBounded` requires, but here **derived** from the run, not
supplied. -/
theorem runWhileMem_halts_schedule (env : LeafEnvM) (guard : LstateM → Bool)
    (body : List LinstrRM) (hgpc : ∀ (b : LstateM) (pc : Nat), guard (b.setLpc pc) = guard b) :
    ∀ (fuel : Nat) (s0 bfin : LstateM),
      runWhileMem env guard body fuel s0 = some bfin →
      0 < whileTripsMem env guard body fuel s0 ∧
      guard bfin = false ∧
      (∃ bprev, runBoundedLoopMemC env body (whileTripsMem env guard body fuel s0 - 1) s0
          = some bprev ∧ lsemStraightMemC env body bprev = some bfin) ∧
      runBoundedLoopMemC env body (whileTripsMem env guard body fuel s0) s0
          = some (bfin.setLpc 1) ∧
      (∀ i, 0 < i → i < whileTripsMem env guard body fuel s0 →
        ∀ bi, runBoundedLoopMemC env body i s0 = some bi → guard bi = true) := by
  intro fuel
  induction fuel with
  | zero => intro s0 bfin h; exact absurd h (by simp [runWhileMem])
  | succ k ih =>
      intro s0 bfin h
      cases hb : lsemStraightMemC env body s0 with
      | none =>
          have hnone : runWhileMem env guard body (k + 1) s0 = none := by
            rw [runWhileMem_succ, hb]
          rw [hnone] at h; exact absurd h (by simp)
      | some b =>
          have hstep : runWhileMem env guard body (k + 1) s0
              = (if guard b = true then runWhileMem env guard body k (b.setLpc 1) else some b) := by
            rw [runWhileMem_succ, hb]
          rw [hstep] at h
          have htrip : whileTripsMem env guard body (k + 1) s0 =
              (if guard b = true then whileTripsMem env guard body k (b.setLpc 1) + 1 else 1) := by
            rw [whileTripsMem_succ, hb]
          by_cases hg : guard b = true
          · -- guard true: recurse; m = m' + 1.
            rw [if_pos hg] at h
            rw [if_pos hg] at htrip
            obtain ⟨hm', hgfin', ⟨bprev', hprev', hlast'⟩, hbfin', hsched'⟩ :=
              ih (b.setLpc 1) bfin h
            set m' := whileTripsMem env guard body k (b.setLpc 1) with hm'def
            rw [htrip]
            refine ⟨by omega, hgfin', ⟨bprev', ?_, hlast'⟩, ?_, ?_⟩
            · -- runBoundedLoopMemC body (m'+1-1) s0 = runBoundedLoopMemC body m' s0 = some bprev'
              have hmm : m' + 1 - 1 = (m' - 1) + 1 := by omega
              rw [hmm, runBoundedLoopMemC_succ_shift env body s0 b (m' - 1) hb]
              exact hprev'
            · -- runBoundedLoopMemC body (m'+1) s0 = runBoundedLoopMemC body m' (b.setLpc 1)
              rw [runBoundedLoopMemC_succ_shift env body s0 b m' hb]; exact hbfin'
            · -- taken schedule for 0 < i < m' + 1
              intro i hi him bi hbi
              have hi1 : i = (i - 1) + 1 := by omega
              rw [hi1, runBoundedLoopMemC_succ_shift env body s0 b (i - 1) hb] at hbi
              rcases Nat.lt_or_ge 1 i with hlt | hle
              · -- i ≥ 2 : use IH schedule on (i-1)
                exact hsched' (i - 1) (by omega) (by omega) bi hbi
              · -- i = 1 : bi = b.setLpc 1, guard = guard b = true
                have hi_eq : i = 1 := by omega
                rw [hi_eq] at hbi
                simp only [Nat.sub_self, runBoundedLoopMemC_zero, Option.some.injEq] at hbi
                rw [← hbi, hgpc]; exact hg
          · -- guard false: bfin = b, m = 1.
            rw [if_neg hg] at h
            obtain rfl : b = bfin := Option.some.inj h
            have hgf : guard b = false := by simpa using hg
            rw [if_neg hg] at htrip
            rw [htrip]
            refine ⟨Nat.one_pos, hgf, ⟨s0, ?_, ?_⟩, ?_, ?_⟩
            · simp
            · exact hb
            · rw [runBoundedLoopMemC_succ_shift env body s0 b 0 hb]; simp
            · intro i hi him _ _; omega

/-! ## 6. `whileMem_runWhile` — the emitted loop realises `runWhileMem`

Composing §5 with A2's `loopCall_runBounded`: for the emitted counter-loop
`loopLinstrRM top nReg body` run by `lsemFuelMemLC`, starting at the loop top, if
the data-dependent do-while `runWhileMem (condNZ nReg) body fuel` halts within
`fuel` to `bfin`, then the interpreter — given `whileTripsMem … * (fuelCostC + 1)`
steps (the trip *read off the run*, not supplied) — halts in a state agreeing with
`bfin` on the register store and the array carrier.  The consumer supplies only
`fuel` (a termination/variant bound); the trip is data-dependent. -/
theorem whileMem_runWhile (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (loopLinstrRM top nReg body)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg nReg)) body fuel s.base = some bfin) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body))
          (whileTripsMem env (fun b => condNZ b (.reg nReg)) body fuel s.base
            * (fuelCostC env body + 1)) s = some t
        ∧ t.base.reg.lvm = bfin.reg.lvm ∧ t.base.larr = bfin.larr := by
  set guard : LstateM → Bool := (fun b => condNZ b (.reg nReg)) with hguard
  have hgpc : ∀ (b : LstateM) (pc : Nat), guard (b.setLpc pc) = guard b := by
    intro b pc; simp only [hguard]; exact condNZ_setLpc b pc (.reg nReg)
  obtain ⟨hm, hgfin, ⟨bprev, hprev, hlast⟩, hbfin, hsched⟩ :=
    runWhileMem_halts_schedule env guard body hgpc fuel s.base bfin hhalt
  set m := whileTripsMem env guard body fuel s.base with hmdef
  have htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMemC env body i s.base = some bi →
      condNZ bi (.reg nReg) = true := by
    intro i hi him bi hbi
    have := hsched i hi him bi hbi
    simpa only [hguard] using this
  have hhaltcond : condNZ bfin (.reg nReg) = false := by simpa only [hguard] using hgfin
  obtain ⟨t, ht, hreg, harr⟩ := loopCall_runBounded env fn top nReg body hok s hfn hpc m hm
    bprev bfin (bfin.setLpc 1) hprev hlast hbfin htaken hhaltcond
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hreg, LstateM.reg_lvm_setLpc]
  · rw [harr, LstateM.larr_setLpc]

/-- Corollary over `whileLinstrRM` (empty guard-compute, `gReg = nReg`): the
    emitted `while (nReg != 0)` realises `runWhileMem`. -/
theorem whileMem_realizes (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (whileLinstrRM top nReg [] body)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg nReg)) body fuel s.base = some bfin) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn (whileLinstrRM top nReg [] body))
          (whileTripsMem env (fun b => condNZ b (.reg nReg)) body fuel s.base
            * (fuelCostC env body + 1)) s = some t
        ∧ t.base.reg.lvm = bfin.reg.lvm ∧ t.base.larr = bfin.larr := by
  have hbody : (body ++ ([] : List LinstrRM)) = body := by simp
  rw [whileLinstrRM_eq, hbody] at *
  exact whileMem_runWhile env fn top nReg body hok s hfn hpc fuel bfin hhalt

/-! ## 7. Validate (a): a NESTED loop→leaf→leaf run (depth-2 region calls)

The loop body calls `sum` per element; `sum`'s body itself calls the innermost
`add` leaf (`acc += t`).  So the run is loop → `sum` → `add`, a real depth-2 nested
region call over the shared `LstateM`.  Checked by `native_decide` to decode
`acc = 60`. -/

/-- The two-level leaf environment: `sum` calls `add`; `add` does `acc += t`. -/
def nestEnv : LeafEnvM := fun name =>
  if name = "add" then
    some [ (LinstrR.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .reg "t"], MemTag.reg none)
         , (LinstrR.Lret, MemTag.reg none) ]
  else if name = "sum" then
    some [ (LinstrR.Lcall none ("add", (0 : LLabel)), MemTag.reg none)
         , (LinstrR.Lret, MemTag.reg none) ]
  else none

/-- The loop body: load `buf[i]` into `t`, **call `sum`** (which calls `add`),
    `i += 1`, `n -= 1`. -/
def nestBody : List LinstrRM :=
  [ (LinstrR.Lopn [.reg "t"] "LOADIDX" [.arrIdx "buf" "i" 8], MemTag.load 64 3)
  , (LinstrR.Lcall none ("sum", (0 : LLabel)), MemTag.reg none)
  , (LinstrR.Lopn [.reg "i"] "ADD:64" [.reg "i", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "n"] "SUB:64" [.reg "n", .imm 1], MemTag.reg none) ]

def nestProg : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" nestBody)

def nestStart : LstatePMC :=
  { base :=
      ((((({} : LstateM).setReg "acc" (0#64)).setReg "i" (0#64)).setReg "n" (3#64)).setArr
        "buf" (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64))
    lfn := "f"
    rstack := [] }

/-- **Validate (a).**  The depth-2 nested-call loop (loop → `sum` → `add`) decodes
    `acc = 10 + 20 + 30 = 60`: the interpreter followed a real two-level region-call
    chain per element over the shared `LstateM`. -/
theorem nestLoop_validate :
    (lsemFuelMemLC nestEnv nestProg 80 nestStart).map (fun t => decodeM t.base "acc" 64)
      = some (some (60#64)) := by native_decide

/-! ## 8. Validate (b): a true INLINE nested loop (outer × inner, distinct labels)

An outer loop (counter `n`) whose body resets an inner counter `m := 3`, runs an
**inline** inner loop (counter `m`, distinct top label `1`) that does `acc += 1`
each inner pass, then `n -= 1`.  The interpreter's label resolution
(`findLabelMem`) picks the correct (inner vs outer) label, so a genuine nested
inline loop runs over `LstateM`.  Outer trip `2` × inner trip `3` ⇒ `acc = 6`. -/

/-- The inner loop body: `acc += 1`, `m -= 1`. -/
def innerBody : List LinstrRM :=
  [ (LinstrR.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "m"] "SUB:64" [.reg "m", .imm 1], MemTag.reg none) ]

/-- The outer loop body: reset `m := 3` (immediate MOV), the **inline** inner loop
    `loopLinstrRM 1 "m" innerBody`, then `n -= 1`. -/
def outerBody : List LinstrRM :=
  (LinstrR.Lopn [.reg "m"] "MOV:64" [.imm 3], MemTag.reg none)
    :: (loopLinstrRM 1 "m" innerBody
        ++ [(LinstrR.Lopn [.reg "n"] "SUB:64" [.reg "n", .imm 1], MemTag.reg none)])

/-- The doubly-nested loop program: the outer loop (top label `0`, counter `n`)
    over `outerBody` (which contains the inner loop at top label `1`). -/
def nestedLoopProg : LprogM := singletonProgM "g" (loopLinstrRM 0 "n" outerBody)

def nestedLoopStart : LstatePMC :=
  { base := (((({} : LstateM).setReg "acc" (0#64)).setReg "n" (2#64)).setReg "m" (3#64))
    lfn := "g"
    rstack := [] }

/-- **Validate (b).**  The true inline nested loop (outer `n = 2` × inner `m = 3`,
    distinct labels `0`/`1`) decodes `acc = 2 * 3 = 6` — the interpreter ran a
    genuine doubly-nested inline loop over `LstateM`, its label resolution keeping
    the inner and outer back-edges distinct. -/
theorem nestedLoop_validate :
    (lsemFuelMemLC (fun _ => none) nestedLoopProg 200 nestedLoopStart).map
        (fun t => decodeM t.base "acc" 64)
      = some (some (6#64)) := by native_decide

/-! ## 9. Validate (c): a DATA-DEPENDENT `while (n != 0)`

`acc += buf[i]` while `n != 0`, the body doing `n -= 1` — the trip count is
determined by the initial `n` (here `3`), not a proof parameter.  Checked by
`native_decide` to decode `acc = 60`, to match `runWhileMem`, and that the
data-dependent trip count `whileTripsMem = 3` (read off the run). -/

/-- The `while` body (all `Lopn`): load `buf[i]`, `acc += t`, `i += 1`, `n -= 1`. -/
def whileBody : List LinstrRM :=
  [ (LinstrR.Lopn [.reg "t"] "LOADIDX" [.arrIdx "buf" "i" 8], MemTag.load 64 3)
  , (LinstrR.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .reg "t"], MemTag.reg none)
  , (LinstrR.Lopn [.reg "i"] "ADD:64" [.reg "i", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "n"] "SUB:64" [.reg "n", .imm 1], MemTag.reg none) ]

/-- The emitted `while (n != 0)` program: `whileLinstrRM` with an empty guard-compute
    (the body already leaves the counter in `n`). -/
def whileProg : LprogM := singletonProgM "w" (whileLinstrRM 0 "n" [] whileBody)

def whileStart : LstatePMC :=
  { base :=
      ((((({} : LstateM).setReg "acc" (0#64)).setReg "i" (0#64)).setReg "n" (3#64)).setArr
        "buf" (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64))
    lfn := "w"
    rstack := [] }

/-- **Validate (c) functional.**  The data-dependent `while (n != 0)` decodes
    `acc = 60`: the interpreter followed the counter-guarded back-edge until `n`
    reached `0`, the trip determined by the initial `n = 3`. -/
theorem whileLoop_validate :
    (lsemFuelMemLC (fun _ => none) whileProg 40 whileStart).map
        (fun t => decodeM t.base "acc" 64)
      = some (some (60#64)) := by native_decide

/-- **Validate (c) trip count.**  The data-dependent trip count `whileTripsMem` for
    the `while` body equals `3` — determined by the run (initial `n = 3`), not
    supplied. -/
theorem whileLoop_trips :
    whileTripsMem (fun _ => none) (fun b => condNZ b (.reg "n")) whileBody 10 whileStart.base = 3 := by
  native_decide

/-- **Validate (c) `runWhileMem` agreement.**  The interpreter's decoded result
    equals the `runWhileMem` do-while denotation (guard `n != 0`) of the same body
    over the same start — the emitted loop realises the data-dependent while. -/
theorem whileLoop_runWhileMem_agreement :
    (lsemFuelMemLC (fun _ => none) whileProg 40 whileStart).map
        (fun t => decodeM t.base "acc" 64)
      = (runWhileMem (fun _ => none) (fun b => condNZ b (.reg "n")) whileBody 10 whileStart.base).map
          (fun b => decodeM b "acc" 64) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
