/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop

@[expose] public section

set_option autoImplicit false

/-!
# A loop body that CALLS a linked owned leaf, over the memref state

`JasminLsemMemLoop` unifies control transfer (`Llabel`/`Lcond`/`Lgoto`) with
the memref state `LstateM`, so a **straight-line** loop body runs over the bundled
register+array state via `lsemFuelMemL`.  Its `evalInstrPMemL` delegates every
non-control instruction to `lsemStepMem`, which returns `none` on the region-call
instructions `Lcall`/`Lret`, so under it a loop body cannot CALL a leaf.

This module **adds the region call**: the loop-body may contain a
`LinstrR.Lcall` to a **linked owned leaf** held in a `LeafEnvM` (name → owned
body), and that call denotes to the **concrete leaf's effect on `LstateM`** — the
piece the whole-prover loops need to call a hash leaf per node, and that
`ConvertToVole` needs to call `prg_14` per node.

## Structure (additive on `JasminLsemMemLoop`)

* `LstatePMC` extends the loop interpreter's `LstatePM` with a **return-address stack**
  `rstack : List (String × Nat)` (caller function + return pc).
* `LeafEnvM := String → Option (List LinstrRM)` — the callee environment: each
  linked leaf `sym` maps to its **owned body** (a straight-line `List LinstrRM`
  ending in `LinstrR.Lret`).
* `evalInstrPMemLC` mirrors the loop interpreter's `evalInstrPMemL` and adds two arms:
  * `Lcall _ (sym, _)` — push the return address `(lfn, pc+1)`, enter the callee
    (`lfn := sym`, `pc := 0`), running the callee's owned body over the **shared**
    `LstateM` (register store + array carrier threaded per the ABI).
  * `Lret` — pop the return frame, resume the caller at the saved pc.
  The fetch `findInstrMemC` reads the **current** function's body — `P.body` when
  `lfn = P.lfn`, else the callee body `env lfn` — so the callee's instructions are
  fetched from the environment while sharing the one `LstateM`.
* `lsemFuelMemLC` iterates `evalInstrPMemLC`, halting when the fetch is `none`.

## The concrete-leaf effect and the region-call denote theorem

`lsemStepMemC` folds a call inline: a `Lcall sym` denotes `calleeEffect env sym`,
running the callee's leaf ops (`(env sym).dropLast`, i.e. the body minus its
trailing `Lret`) over the shared state and returning the pc to `call-site + 1` —
the concrete leaf's effect on `LstateM`.  `callee_run` proves the interpreter
`lsemFuelMemLC`, from a pushed callee frame, executes exactly that (leaf ops then
`Lret`-pop-resume): **the region call denotes the concrete leaf, threaded through
memory**.  `segCallC` lifts this to a mixed straight-line segment (Lopn ∪ Lcall),
and `loopCall_pass_taken`/`loopCall_pass_halt` give the one-pass loop-with-call
bridge: one pass over a call-containing body denotes one `lsemStraightMemC`
body-fold then loops / exits.

## Validation

`§ Validate` runs a concrete memref loop whose body **calls a leaf per element**
(`acc += buf[i]` performed by an in-`LeafEnvM` `sum` leaf via a real `Lcall`) and
checks by `native_decide` that the result decodes to the fold `acc = 60`, and that
it agrees with `runBoundedLoopMemC` (the fold using the concrete-leaf call step).
This is the region-call harness `ConvertToVole` reuses.

**All goals closed, axioms ⊆ {propext, Classical.choice, Quot.sound} (+ `Lean.ofReduceBool`
for the `native_decide` validate).**
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop

/-! ## 1. The callee environment and the program-indexed state with a return stack -/

/-- The **callee environment**: each linked owned leaf `sym` maps to its owned
    body (a straight-line `List LinstrRM` ending in `LinstrR.Lret`). This is the
    `LstateM`/loop analogue of `JasminLsemLabeledLeaf`'s `LeafEnvN` (which maps a
    name to an opaque `BitVec` function) — here the leaf is a *linked* owned body
    run over the shared state. -/
abbrev LeafEnvM : Type := String → Option (List LinstrRM)

/-- The program-indexed bundled state with a **return-address stack**: the loop
    interpreter's `base`/`lfn` plus `rstack`, a stack of return frames `(caller fn, return pc)`
    pushed on `Lcall` and popped on `Lret`. -/
structure LstatePMC where
  /-- The bundled stack-memory base (register file + array carrier + pc). -/
  base : LstateM
  /-- The current function name (indexes `P.body` or the callee `env lfn`). -/
  lfn : String
  /-- The return-address stack: `(caller fn, return pc)` frames. -/
  rstack : List (String × Nat)

/-- The **current function's body**: the program's own body `P.body` when the
    current function is `P.lfn`, otherwise the callee body `env lfn` from the
    environment (empty on a missing symbol). -/
def curBodyC (env : LeafEnvM) (P : LprogM) (lfn : String) : List LinstrRM :=
  if lfn = P.lfn then P.body else (env lfn).getD []

/-- On the program's own function, the current body is `P.body`. -/
theorem curBodyC_self (env : LeafEnvM) (P : LprogM) (lfn : String) (h : lfn = P.lfn) :
    curBodyC env P lfn = P.body := by unfold curBodyC; rw [ite_eq_left h]

/-- `find_instr`: the typed instruction at `lpc` in the current function's body. -/
def findInstrMemC (env : LeafEnvM) (P : LprogM) (s : LstatePMC) : Option LinstrRM :=
  (curBodyC env P s.lfn)[s.base.lpc]?

/-- `eval_jump`: resolve a label in the current function's body and jump after it. -/
def evalJumpMemC (env : LeafEnvM) (P : LprogM) (lbl : LLabel) (s : LstatePMC) :
    Option LstatePMC :=
  match findLabelMem lbl (curBodyC env P s.lfn) with
  | some pc => some { s with base := s.base.setLpc (pc + 1) }
  | none => none

/-- **The control-transfer + region-call eval arm over the bundled state.**
    `Llabel`/`Lcond`/`Lgoto` are the loop interpreter's control transfer (resolving in the current
    function's body).  The two new arms:
    * `Lcall _ (sym, _)` — if `sym` is a linked leaf (`env sym` present), push the
      return frame `(lfn, pc+1)`, enter the callee (`lfn := sym`, `pc := 0`),
      sharing the one `LstateM`.
    * `Lret` — pop the return frame and resume the caller at the saved pc.
    Every other instruction is the straight-line/memory step `lsemStepMem`. -/
def evalInstrPMemLC (env : LeafEnvM) (P : LprogM) (i : LinstrRM) (s : LstatePMC) :
    Option LstatePMC :=
  match i.fst with
  | .Llabel _ _ => some { s with base := s.base.nextPc }
  | .Lcond cond lbl =>
      if condNZ s.base cond then evalJumpMemC env P lbl s
      else some { s with base := s.base.nextPc }
  | .Lgoto (fn, lbl) => if fn = s.lfn then evalJumpMemC env P lbl s else none
  | .Lcall _ (sym, _) =>
      match env sym with
      | some _ =>
          some { base := s.base.setLpc 0, lfn := sym,
                 rstack := (s.lfn, s.base.lpc + 1) :: s.rstack }
      | none => none
  | .Lret =>
      match s.rstack with
      | (callerFn, retPc) :: rest =>
          some { base := s.base.setLpc retPc, lfn := callerFn, rstack := rest }
      | [] => none
  | _ => (lsemStepMem i s.base).map (fun b => { s with base := b })

/-- **The full labeled + region-call fuel-stepped interpreter over `LstateM`.** -/
def lsemFuelMemLC (env : LeafEnvM) (P : LprogM) : Nat → LstatePMC → Option LstatePMC
  | 0, s => match findInstrMemC env P s with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMemC env P s with
      | none => some s
      | some i =>
          match evalInstrPMemLC env P i s with
          | some s' => lsemFuelMemLC env P fuel s'
          | none => none

/-- A halted state (`findInstrMemC = none`) takes no step. -/
theorem lsemFuelMemLC_halt (env : LeafEnvM) (P : LprogM) (fuel : Nat) (s : LstatePMC)
    (h : findInstrMemC env P s = none) : lsemFuelMemLC env P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelMemLC, h]
  | succ n => simp [lsemFuelMemLC, h]

/-! ## 2. The concrete-leaf effect and the inline call step -/

/-- The **concrete leaf effect** of an inline call to `sym` returning to `retPc`:
    run the callee's leaf ops (`(env sym).dropLast`, the owned body minus its
    trailing `Lret`) over the shared state started at pc `0`, then set the pc to
    the caller's return address `retPc`.  The reg/array effect is exactly the
    concrete leaf's; the pc bookkeeping is the call/return plumbing. -/
def calleeEffect (env : LeafEnvM) (sym : String) (retPc : Nat) (s : LstateM) :
    Option LstateM :=
  match env sym with
  | some body => (lsemStraightMem body.dropLast (s.setLpc 0)).map (fun b => b.setLpc retPc)
  | none => none

/-- The inline single-step over `LstateM` with region calls: an `Lcall sym`
    denotes `calleeEffect` (the concrete leaf); every other instruction is the
    straight-line/memory step `lsemStepMem`. -/
def lsemStepMemC (env : LeafEnvM) (i : LinstrRM) (s : LstateM) : Option LstateM :=
  match i.fst with
  | .Lcall _ (sym, _) => calleeEffect env sym (s.lpc + 1) s
  | _ => lsemStepMem i s

/-- Typed straight-line execution with region calls: the sequential fold of
    `lsemStepMemC`. -/
def lsemStraightMemC (env : LeafEnvM) : List LinstrRM → LstateM → Option LstateM
  | [], s => some s
  | i :: is, s =>
      match lsemStepMemC env i s with
      | some s' => lsemStraightMemC env is s'
      | none => none

@[simp] theorem lsemStraightMemC_nil (env : LeafEnvM) (s : LstateM) :
    lsemStraightMemC env [] s = some s := rfl

@[simp] theorem lsemStraightMemC_cons (env : LeafEnvM) (i : LinstrRM)
    (is : List LinstrRM) (s : LstateM) :
    lsemStraightMemC env (i :: is) s =
      (match lsemStepMemC env i s with
        | some s' => lsemStraightMemC env is s'
        | none => none) := rfl

/-! ## 3. Well-formed callees and body instructions -/

/-- A **linked owned leaf** callee `sym` of the loop program `P`: it is not the
    loop function itself (`sym ≠ P.lfn`, so its body is fetched from `env`), and
    its owned body is a straight-line block of `Lopn`s ending in a single `Lret`. -/
def CalleeOK (env : LeafEnvM) (P : LprogM) (sym : String) : Prop :=
  sym ≠ P.lfn ∧
  ∃ leafOps : List LinstrRM,
    env sym = some (leafOps ++ [(LinstrR.Lret, MemTag.reg none)]) ∧
    (∀ i ∈ leafOps, IsLopn i)

/-- A loop-body instruction is either a straight-line `Lopn` or a region call to a
    well-formed linked leaf. -/
def BodyStepOK (env : LeafEnvM) (P : LprogM) (i : LinstrRM) : Prop :=
  IsLopn i ∨ ∃ ra sym lbl, i.fst = LinstrR.Lcall ra (sym, lbl) ∧ CalleeOK env P sym

/-- The per-instruction fuel cost: an `Lopn` costs one interpreter step; a call to
    `sym` costs `|env sym| + 1` (enter + leaf ops + the callee's `Lret`). -/
def stepCostC (env : LeafEnvM) (i : LinstrRM) : Nat :=
  match i.fst with
  | .Lcall _ (sym, _) => ((env sym).getD []).length + 1
  | _ => 1

/-- The fuel cost of a straight-line-with-calls segment. -/
def fuelCostC (env : LeafEnvM) (body : List LinstrRM) : Nat :=
  (body.map (stepCostC env)).sum

@[simp] theorem fuelCostC_nil (env : LeafEnvM) : fuelCostC env [] = 0 := rfl

@[simp] theorem fuelCostC_cons (env : LeafEnvM) (i : LinstrRM) (is : List LinstrRM) :
    fuelCostC env (i :: is) = stepCostC env i + fuelCostC env is := by
  simp [fuelCostC, List.sum_cons]

/-! ## 4. The `Lopn` delegate arm coincides with the loop interpreter -/

/-- On an `Lopn`, `evalInstrPMemLC` is the straight-line/memory step, exactly like
    the loop interpreter's `evalInstrPMemL`. -/
theorem evalInstrPMemLC_lopn (env : LeafEnvM) (P : LprogM) (i : LinstrRM) (s : LstatePMC)
    (hi : IsLopn i) :
    evalInstrPMemLC env P i s
      = (lsemStepMem i s.base).map (fun b => { s with base := b }) := by
  obtain ⟨d, o, src, hd⟩ := hi
  unfold evalInstrPMemLC
  rw [hd]

/-- On an `Lopn`, the inline step is `lsemStepMem`. -/
theorem lsemStepMemC_lopn (env : LeafEnvM) (i : LinstrRM) (s : LstateM) (hi : IsLopn i) :
    lsemStepMemC env i s = lsemStepMem i s := by
  obtain ⟨d, o, src, hd⟩ := hi
  unfold lsemStepMemC
  rw [hd]

/-! ## 5. The straight-line-with-calls segment lemma

`segCallC` is the call-aware analogue of `lsemFuelMemL_seg`, relaxed so the segment
may contain region calls: running `lsemFuelMemLC` for `fuelCostC seg + f` fuel
executes the inline body-fold `lsemStraightMemC seg` then continues with `f` fuel.
Each `Lopn` mirrors the loop interpreter; each call is discharged by the callee sub-run. -/

/-- The all-`Lopn` callee sub-run: from a callee frame at pc `0`, running the leaf
    ops (`leafOps`, all `Lopn`) then the trailing `Lret` executes the leaf ops via
    `lsemStraightMem` and pops back to the caller at `retPc`.  This is the
    **region-call denote core**: the interpreter's call/return realises the
    concrete leaf's effect on the shared `LstateM`. -/
theorem callee_run (env : LeafEnvM) (P : LprogM) (sym callerFn : String) (retPc : Nat)
    (leafOps : List LinstrRM) (hlopn : ∀ i ∈ leafOps, IsLopn i)
    (hne : sym ≠ P.lfn)
    (hsym : env sym = some (leafOps ++ [(LinstrR.Lret, MemTag.reg none)]))
    (base b : LstateM) (rest : List (String × Nat)) (f : Nat)
    (hrun : lsemStraightMem leafOps (base.setLpc 0) = some b) :
    lsemFuelMemLC env P (leafOps.length + 1 + f)
        { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest }
      = lsemFuelMemLC env P f
          { base := b.setLpc retPc, lfn := callerFn, rstack := rest } := by
  -- the callee's current body is `leafOps ++ [Lret]`, fetched from the environment.
  have hcur : curBodyC env P sym = leafOps ++ [(LinstrR.Lret, MemTag.reg none)] := by
    unfold curBodyC; rw [ite_eq_right hne, hsym]; rfl
  -- run the all-`Lopn` leaf ops as a straight-line segment (mirrors `lsemFuelMemL_seg`).
  have hseg :
      ∀ (seg pre : List LinstrRM),
        (∀ i ∈ seg, IsLopn i) →
        ∀ (sb : LstateM) (g : Nat),
          sb.lpc = pre.length →
          curBodyC env P sym = pre ++ seg ++ [(LinstrR.Lret, MemTag.reg none)] →
          lsemFuelMemLC env P (seg.length + g)
              { base := sb, lfn := sym, rstack := (callerFn, retPc) :: rest }
            = (lsemStraightMem seg sb).bind
                (fun c => lsemFuelMemLC env P g
                  { base := c, lfn := sym, rstack := (callerFn, retPc) :: rest }) := by
    intro seg
    induction seg with
    | nil =>
        intro pre _ sb g _ _
        simp only [List.length_nil, Nat.zero_add, lsemStraightMem_nil, Option.bind_some]
    | cons i is ih =>
        intro pre hlop sb g hpc hbody
        have hi : IsLopn i := hlop i (by simp)
        have his : ∀ j ∈ is, IsLopn j := fun j hj => hlop j (by simp [hj])
        have hfetch : findInstrMemC env P
            { base := sb, lfn := sym, rstack := (callerFn, retPc) :: rest } = some i := by
          unfold findInstrMemC
          show (curBodyC env P sym)[sb.lpc]? = some i
          rw [hbody, hpc]
          simp
        rw [List.length_cons, show is.length + 1 + g = (is.length + g) + 1 from by omega,
          lsemFuelMemLC, hfetch]
        simp only []
        rw [evalInstrPMemLC_lopn env P i _ hi]
        cases hstep : lsemStepMem i sb with
        | none =>
            simp only [Option.map_none]
            rw [lsemStraightMem_cons, hstep]; rfl
        | some c =>
            simp only [Option.map_some]
            rw [lsemStraightMem_cons, hstep]
            have hc_lpc : c.lpc = (pre ++ [i]).length := by
              rw [lsemStepMem_lpc_succ i sb c hstep, hpc]; simp
            have hbody' : curBodyC env P sym
                = (pre ++ [i]) ++ is ++ [(LinstrR.Lret, MemTag.reg none)] := by
              rw [hbody]; simp
            have := ih (pre ++ [i]) his c g hc_lpc hbody'
            simpa using this
  -- specialise the segment run to `pre = []`, `seg = leafOps`, `g = 1 + f`.
  have hbase0 : (base.setLpc 0).lpc = ([] : List LinstrRM).length := by simp
  have hrunSeg := hseg leafOps [] hlopn (base.setLpc 0) (1 + f) hbase0 (by simpa using hcur)
  rw [show leafOps.length + 1 + f = leafOps.length + (1 + f) from by omega, hrunSeg, hrun,
    Option.bind_some]
  -- now at the trailing `Lret`: pc is at `leafOps.length`.
  have hb_lpc : b.lpc = leafOps.length := by
    have := lsemStraightMem_lpc leafOps (base.setLpc 0) b hrun
    rw [hbase0] at this; simpa using this
  have hfetchRet : findInstrMemC env P
      { base := b, lfn := sym, rstack := (callerFn, retPc) :: rest }
        = some (LinstrR.Lret, MemTag.reg none) := by
    unfold findInstrMemC
    show (curBodyC env P sym)[b.lpc]? = _
    rw [hcur, hb_lpc]
    rw [List.getElem?_append_right (by simp)]
    simp
  rw [show 1 + f = f + 1 from by omega, lsemFuelMemLC, hfetchRet]
  simp only []
  unfold evalInstrPMemLC
  simp only []

/-- The failing-callee variant of `callee_run`: if the leaf ops fail, the whole
    call run is `none`. -/
theorem callee_run_none (env : LeafEnvM) (P : LprogM) (sym callerFn : String) (retPc : Nat)
    (leafOps : List LinstrRM) (hlopn : ∀ i ∈ leafOps, IsLopn i)
    (hne : sym ≠ P.lfn)
    (hsym : env sym = some (leafOps ++ [(LinstrR.Lret, MemTag.reg none)]))
    (base : LstateM) (g : Nat) (rest : List (String × Nat))
    (hrun : lsemStraightMem leafOps (base.setLpc 0) = none) :
    lsemFuelMemLC env P (leafOps.length + 1 + g)
        { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest }
      = none := by
  have hcur : curBodyC env P sym = leafOps ++ [(LinstrR.Lret, MemTag.reg none)] := by
    unfold curBodyC; rw [ite_eq_right hne, hsym]; rfl
  have hseg :
      ∀ (seg pre : List LinstrRM),
        (∀ i ∈ seg, IsLopn i) →
        ∀ (sb : LstateM) (g' : Nat),
          sb.lpc = pre.length →
          curBodyC env P sym = pre ++ seg ++ [(LinstrR.Lret, MemTag.reg none)] →
          lsemFuelMemLC env P (seg.length + g')
              { base := sb, lfn := sym, rstack := (callerFn, retPc) :: rest }
            = (lsemStraightMem seg sb).bind
                (fun c => lsemFuelMemLC env P g'
                  { base := c, lfn := sym, rstack := (callerFn, retPc) :: rest }) := by
    intro seg
    induction seg with
    | nil =>
        intro pre _ sb g' _ _
        simp only [List.length_nil, Nat.zero_add, lsemStraightMem_nil, Option.bind_some]
    | cons i is ih =>
        intro pre hlop sb g' hpc hbody
        have hi : IsLopn i := hlop i (by simp)
        have his : ∀ j ∈ is, IsLopn j := fun j hj => hlop j (by simp [hj])
        have hfetch : findInstrMemC env P
            { base := sb, lfn := sym, rstack := (callerFn, retPc) :: rest } = some i := by
          unfold findInstrMemC
          show (curBodyC env P sym)[sb.lpc]? = some i
          rw [hbody, hpc]; simp
        rw [List.length_cons, show is.length + 1 + g' = (is.length + g') + 1 from by omega,
          lsemFuelMemLC, hfetch]
        simp only []
        rw [evalInstrPMemLC_lopn env P i _ hi]
        cases hstep : lsemStepMem i sb with
        | none => simp only [Option.map_none]; rw [lsemStraightMem_cons, hstep]; rfl
        | some c =>
            simp only [Option.map_some]
            rw [lsemStraightMem_cons, hstep]
            have hc_lpc : c.lpc = (pre ++ [i]).length := by
              rw [lsemStepMem_lpc_succ i sb c hstep, hpc]; simp
            have hbody' : curBodyC env P sym
                = (pre ++ [i]) ++ is ++ [(LinstrR.Lret, MemTag.reg none)] := by
              rw [hbody]; simp
            have := ih (pre ++ [i]) his c g' hc_lpc hbody'
            simpa using this
  have hbase0 : (base.setLpc 0).lpc = ([] : List LinstrRM).length := by simp
  have hrunSeg := hseg leafOps [] hlopn (base.setLpc 0) (1 + g) hbase0 (by simpa using hcur)
  rw [show leafOps.length + 1 + g = leafOps.length + (1 + g) from by omega, hrunSeg, hrun,
    Option.bind_none]

/-- **The straight-line-with-calls segment run.**  If the segment `seg` (Lopn ∪
    well-formed-call) occupies positions `lpc .. lpc+|seg|-1` of the loop program's
    body, then running `lsemFuelMemLC` for `fuelCostC seg + f` fuel executes the
    inline body-fold `lsemStraightMemC seg` and then continues with `f` fuel. -/
theorem segCallC (env : LeafEnvM) (P : LprogM) :
    ∀ (seg : List LinstrRM) (s : LstatePMC) (f : Nat),
      s.lfn = P.lfn →
      (∀ i ∈ seg, BodyStepOK env P i) →
      (∀ k, k < seg.length → P.body[s.base.lpc + k]? = seg[k]?) →
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
      have hcur : curBodyC env P s.lfn = P.body := by unfold curBodyC; rw [ite_eq_left hfn]
      have hii : BodyStepOK env P i := hok i (by simp)
      have his : ∀ j ∈ is, BodyStepOK env P j := fun j hj => hok j (by simp [hj])
      have hfetch : findInstrMemC env P s = some i := by
        unfold findInstrMemC; rw [hcur]
        have := hpos 0 (by simp); simpa using this
      -- position bookkeeping for the tail after this instruction (1 body slot).
      have hpostail : ∀ (b : LstateM), b.lpc = s.base.lpc + 1 →
          ∀ k, k < is.length →
            P.body[({ s with base := b } : LstatePMC).base.lpc + k]? = is[k]? := by
        intro b hb k hk
        have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
        show P.body[b.lpc + k]? = is[k]?
        rw [hb, show s.base.lpc + 1 + k = s.base.lpc + (k + 1) from by omega, hp]; simp
      rw [fuelCostC_cons]
      rcases hii with hlopn | ⟨ra, sym, lbl, hcall, hcOK⟩
      · -- `Lopn`: cost 1, mirror the loop interpreter.
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
            have hfn' : ({ s with base := b } : LstatePMC).lfn = P.lfn := hfn
            have := ih { s with base := b } f hfn' his (hpostail b hb_lpc)
            simpa using this
      · -- region call: cost `|env sym| + 1`, discharged by `callee_run`.
        obtain ⟨hne, leafOps, hsym, hleafLopn⟩ := hcOK
        have hcost : stepCostC env i = leafOps.length + 2 := by
          unfold stepCostC; rw [hcall]
          simp only [hsym, Option.getD_some, List.length_append, List.length_cons,
            List.length_nil]
        -- fetch and enter the callee.
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
        -- the inline fold at this call.
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
            -- interpreter enters the callee and the leaf ops fail: result none.
            exact callee_run_none env P sym s.lfn (s.base.lpc + 1) leafOps hleafLopn hne hsym
              s.base (fuelCostC env is + f) s.rstack hleaf
        | some b =>
            simp only [Option.map_some]
            have hcallee := callee_run env P sym s.lfn (s.base.lpc + 1) leafOps hleafLopn hne
              hsym s.base b s.rstack (fuelCostC env is + f) hleaf
            rw [hcallee]
            have hb_lpc : b.lpc = leafOps.length := by
              have := lsemStraightMem_lpc leafOps (s.base.setLpc 0) b hleaf
              simpa using this
            have hbset_lpc : (b.setLpc (s.base.lpc + 1)).lpc = s.base.lpc + 1 := rfl
            have := ih { base := b.setLpc (s.base.lpc + 1), lfn := s.lfn,
                          rstack := s.rstack } f hfn his (hpostail _ hbset_lpc)
            -- align the continuation states.
            have hstateEq :
                ({ base := b.setLpc (s.base.lpc + 1), lfn := s.lfn, rstack := s.rstack }
                    : LstatePMC)
                  = { s with base := b.setLpc (s.base.lpc + 1) } := by
              cases s; rfl
            rw [hstateEq] at *
            exact this

/-! ## 6. The loop shape and the single-pass loop-with-call bridge -/

/-- The bounded fold semantics of a memref loop **with region calls**: run the
    inline call body-fold `lsemStraightMemC env body` `n` times, resetting the pc
    to `1` after each pass (as `runBoundedLoopMem`, but the body-fold resolves
    calls to the concrete leaf). -/
def runBoundedLoopMemC (env : LeafEnvM) (body : List LinstrRM) :
    Nat → LstateM → Option LstateM
  | 0, s => some s
  | k + 1, s =>
      (lsemStraightMemC env body s).bind
        (fun b => runBoundedLoopMemC env body k (b.setLpc 1))

@[simp] theorem runBoundedLoopMemC_zero (env : LeafEnvM) (body : List LinstrRM)
    (s : LstateM) : runBoundedLoopMemC env body 0 s = some s := rfl

@[simp] theorem runBoundedLoopMemC_succ (env : LeafEnvM) (body : List LinstrRM)
    (k : Nat) (s : LstateM) :
    runBoundedLoopMemC env body (k + 1) s =
      (lsemStraightMemC env body s).bind
        (fun b => runBoundedLoopMemC env body k (b.setLpc 1)) := rfl

/-- The body-fold with calls advances the pc by the body length (each step — Lopn
    or call — advances the pc by one). -/
theorem lsemStraightMemC_lpc (env : LeafEnvM) (P : LprogM) :
    ∀ (body : List LinstrRM), (∀ i ∈ body, BodyStepOK env P i) →
      ∀ (s b : LstateM), lsemStraightMemC env body s = some b →
        b.lpc = s.lpc + body.length := by
  intro body
  induction body with
  | nil => intro _ s b h; simp only [lsemStraightMemC_nil, Option.some.injEq] at h; subst h; simp
  | cons i is ih =>
      intro hok s b h
      have hii : BodyStepOK env P i := hok i (by simp)
      have his : ∀ j ∈ is, BodyStepOK env P j := fun j hj => hok j (by simp [hj])
      rw [lsemStraightMemC_cons] at h
      cases hstep : lsemStepMemC env i s with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some s' =>
          rw [hstep] at h
          have h1 : s'.lpc = s.lpc + 1 := by
            rcases hii with hlopn | ⟨ra, sym, lbl, hcall, _⟩
            · rw [lsemStepMemC_lopn env i s hlopn] at hstep
              exact lsemStepMem_lpc_succ i s s' hstep
            · unfold lsemStepMemC at hstep; rw [hcall] at hstep
              simp only [] at hstep
              unfold calleeEffect at hstep
              cases hb : env sym with
              | none => rw [hb] at hstep; simp at hstep
              | some cbody =>
                  rw [hb] at hstep; simp only [Option.map_eq_some_iff] at hstep
                  obtain ⟨c, _, hc⟩ := hstep; rw [← hc]; rfl
          have h2 : b.lpc = s'.lpc + is.length := ih his s' b h
          rw [h2, h1, List.length_cons]; omega

/-- `findLabelMem` finds the loop's top label at position 0 (head of `loopLinstrRM`),
    reused from the loop interpreter's shape. -/
theorem findLabelMemC_loop (top : LLabel) (nReg : String) (body : List LinstrRM) :
    findLabelMem top (loopLinstrRM top nReg body) = some 0 :=
  findLabelMem_loop top nReg body

/-- Position of the body in the loop program (index `1+k` is `body[k]`). -/
theorem loopCall_body_pos (top : LLabel) (nReg : String) (body : List LinstrRM)
    (k : Nat) (hk : k < body.length) :
    (loopLinstrRM top nReg body)[1 + k]? = body[k]? :=
  loop_body_pos top nReg body k hk

/-- Position of the back-edge (index `1 + body.length`). -/
theorem loopCall_cond_pos (top : LLabel) (nReg : String) (body : List LinstrRM) :
    (loopLinstrRM top nReg body)[1 + body.length]? =
      some (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) :=
  loop_cond_pos top nReg body

/-- **Single loop pass with a call body — back-edge TAKEN.**  From the top of the
    body (`lpc = 1`), if the inline body-fold (with calls resolved to the concrete
    leaf) runs `lsemStraightMemC env body s.base = some b` and the counter is
    non-zero at `b`, then one pass (body + taken back-edge) consumes
    `fuelCostC env body + 1` fuel and lands back at the top with base `b`. -/
theorem loopCall_pass_taken (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (loopLinstrRM top nReg body)) i)
    (s : LstatePMC) (b : LstateM) (f : Nat)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hbody : lsemStraightMemC env body s.base = some b)
    (htaken : condNZ b (.reg nReg) = true) :
    lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body))
        (fuelCostC env body + 1 + f) s
      = lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body)) f
          { base := b.setLpc 1, lfn := fn, rstack := s.rstack } := by
  subst hfn
  set Q := singletonProgM s.lfn (loopLinstrRM top nReg body) with hQ
  have hQbody : Q.body = loopLinstrRM top nReg body := rfl
  have hseg := segCallC env Q body s (1 + f) rfl hok
    (by intro k hk; show Q.body[s.base.lpc + k]? = body[k]?
        rw [hQbody, hpc]; exact loopCall_body_pos top nReg body k hk)
  rw [show fuelCostC env body + 1 + f = fuelCostC env body + (1 + f) from by omega, hseg,
    hbody, Option.bind_some]
  have hb_lpc : b.lpc = 1 + body.length := by
    have := lsemStraightMemC_lpc (P := Q) env body hok s.base b hbody
    rw [hpc] at this; omega
  have hfetch : findInstrMemC env Q { s with base := b } =
      some (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) := by
    unfold findInstrMemC
    have hcur : curBodyC env Q ({ s with base := b } : LstatePMC).lfn = Q.body := by
      exact curBodyC_self env Q _ rfl
    rw [hcur, hQbody]
    show (loopLinstrRM top nReg body)[b.lpc]? = _
    rw [hb_lpc]; exact loopCall_cond_pos top nReg body
  rw [show 1 + f = f + 1 from by omega, lsemFuelMemLC, hfetch]
  simp only []
  unfold evalInstrPMemLC
  simp only [htaken, ite_true]
  unfold evalJumpMemC
  have hcur : curBodyC env Q ({ s with base := b } : LstatePMC).lfn = Q.body := by
    exact curBodyC_self env Q _ rfl
  rw [hcur, hQbody, findLabelMemC_loop]

/-- **Single loop pass with a call body — back-edge NOT taken (HALT).** -/
theorem loopCall_pass_halt (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (loopLinstrRM top nReg body)) i)
    (s : LstatePMC) (b : LstateM)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hbody : lsemStraightMemC env body s.base = some b)
    (hhalt : condNZ b (.reg nReg) = false) :
    lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body))
        (fuelCostC env body + 1) s
      = some { base := b.nextPc, lfn := fn, rstack := s.rstack } := by
  subst hfn
  set Q := singletonProgM s.lfn (loopLinstrRM top nReg body) with hQ
  have hQbody : Q.body = loopLinstrRM top nReg body := rfl
  have hseg := segCallC env Q body s 1 rfl hok
    (by intro k hk; show Q.body[s.base.lpc + k]? = body[k]?
        rw [hQbody, hpc]; exact loopCall_body_pos top nReg body k hk)
  rw [hseg, hbody, Option.bind_some]
  have hb_lpc : b.lpc = 1 + body.length := by
    have := lsemStraightMemC_lpc (P := Q) env body hok s.base b hbody
    rw [hpc] at this; omega
  have hfetch : findInstrMemC env Q { base := b, lfn := s.lfn, rstack := s.rstack } =
      some (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) := by
    unfold findInstrMemC
    have hcur : curBodyC env Q
        ({ base := b, lfn := s.lfn, rstack := s.rstack } : LstatePMC).lfn = Q.body :=
      curBodyC_self env Q _ rfl
    rw [hcur, hQbody]
    show (loopLinstrRM top nReg body)[b.lpc]? = _
    rw [hb_lpc]; exact loopCall_cond_pos top nReg body
  have hhaltfetch : findInstrMemC env Q
      { base := b.nextPc, lfn := s.lfn, rstack := s.rstack } = none := by
    unfold findInstrMemC
    have hcur : curBodyC env Q
        ({ base := b.nextPc, lfn := s.lfn, rstack := s.rstack } : LstatePMC).lfn = Q.body :=
      curBodyC_self env Q _ rfl
    rw [hcur, hQbody]
    show (loopLinstrRM top nReg body)[(b.nextPc).lpc]? = none
    have hpc2 : (b.nextPc).lpc = body.length + 2 := by
      rw [LstateM.lpc_nextPc, hb_lpc]; omega
    rw [hpc2]
    apply List.getElem?_eq_none
    unfold loopLinstrRM; simp [List.length_append]
  change lsemFuelMemLC env Q (0 + 1) { base := b, lfn := s.lfn, rstack := s.rstack } = _
  rw [lsemFuelMemLC, hfetch]
  simp only []
  unfold evalInstrPMemLC
  simp only [hhalt]
  exact lsemFuelMemLC_halt env Q 0 { base := b.nextPc, lfn := s.lfn, rstack := s.rstack }
    hhaltfetch

/-! ## 6b. Structural facts on `runBoundedLoopMemC` and the `n`-fold bridge

Assemble the two single-pass lemmas into the full bounded-loop-with-calls bridge:
from the top of a call-containing body, running `lsemFuelMemLC` realises
`runBoundedLoopMemC env body m` — the `m`-fold of the (call-resolving) body over
`LstateM`.  This is the region-call loop for an arbitrary trip count `m` (e.g. `m`
tree nodes), the shape `ConvertToVole` needs. -/

/-- After ≥1 iteration the fold sits at the loop top (`lpc = 1`). -/
theorem runBoundedLoopMemC_succ_lpc (env : LeafEnvM) :
    ∀ (k : Nat) (body : List LinstrRM) (s bj : LstateM),
      runBoundedLoopMemC env body (k + 1) s = some bj → bj.lpc = 1 := by
  intro k
  induction k with
  | zero =>
      intro body s bj h
      rw [runBoundedLoopMemC_succ] at h
      cases hb : lsemStraightMemC env body s with
      | none => rw [hb] at h; simp at h
      | some b =>
          rw [hb, Option.bind_some, runBoundedLoopMemC_zero] at h
          obtain rfl := Option.some.inj h; simp
  | succ n ih =>
      intro body s bj h
      rw [runBoundedLoopMemC_succ] at h
      cases hb : lsemStraightMemC env body s with
      | none => rw [hb] at h; simp at h
      | some b => rw [hb, Option.bind_some] at h; exact ih body (b.setLpc 1) bj h

/-- Peel the last fold. -/
theorem runBoundedLoopMemC_succ_right (env : LeafEnvM) :
    ∀ (j : Nat) (body : List LinstrRM) (s : LstateM),
      runBoundedLoopMemC env body (j + 1) s =
        (runBoundedLoopMemC env body j s).bind
          (fun bj => (lsemStraightMemC env body bj).map (fun b => b.setLpc 1)) := by
  intro j
  induction j with
  | zero =>
      intro body s
      simp only [runBoundedLoopMemC_succ, runBoundedLoopMemC_zero, Option.bind_some]
      cases lsemStraightMemC env body s <;> simp
  | succ n ih =>
      intro body s
      rw [runBoundedLoopMemC_succ]
      conv_rhs => rw [runBoundedLoopMemC_succ]
      cases hb : lsemStraightMemC env body s with
      | none => simp
      | some b => rw [Option.bind_some, Option.bind_some]; exact ih body (b.setLpc 1)

/-- **Taken chain (with calls).**  If the back-edge is taken after every iteration
    `1..j`, the interpreter runs the first `j` passes and continues (with `f` fuel)
    from the fold's `j`-th state. -/
theorem loopCall_taken_chain (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (loopLinstrRM top nReg body)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1) :
    ∀ (j f : Nat),
      (∀ i, 0 < i → i ≤ j → ∀ bi, runBoundedLoopMemC env body i s.base = some bi →
        condNZ bi (.reg nReg) = true) →
      lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body))
          (j * (fuelCostC env body + 1) + f) s
        = (runBoundedLoopMemC env body j s.base).bind
            (fun bj => lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body)) f
              { base := bj, lfn := fn, rstack := s.rstack }) := by
  set Q := singletonProgM fn (loopLinstrRM top nReg body) with hQ
  intro j
  induction j with
  | zero =>
      intro f _
      simp only [Nat.zero_mul, Nat.zero_add, runBoundedLoopMemC_zero, Option.bind_some]
      have hs : ({ base := s.base, lfn := fn, rstack := s.rstack } : LstatePMC) = s := by
        obtain ⟨sb, sl, sr⟩ := s; subst hfn; rfl
      rw [hs]
  | succ n ih =>
      intro f htk
      have htk' : ∀ i, 0 < i → i ≤ n → ∀ bi, runBoundedLoopMemC env body i s.base = some bi →
          condNZ bi (.reg nReg) = true := fun i hi hin bi hbi => htk i hi (by omega) bi hbi
      have hfuel : (n + 1) * (fuelCostC env body + 1) + f
          = n * (fuelCostC env body + 1) + ((fuelCostC env body + 1) + f) := by ring
      rw [hfuel, ih ((fuelCostC env body + 1) + f) htk']
      rw [runBoundedLoopMemC_succ_right]
      cases hj : runBoundedLoopMemC env body n s.base with
      | none => simp
      | some bj =>
          simp only [Option.bind_some]
          have hbj_lpc : bj.lpc = 1 := by
            cases n with
            | zero =>
                rw [runBoundedLoopMemC_zero] at hj; obtain rfl := Option.some.inj hj; exact hpc
            | succ k => exact runBoundedLoopMemC_succ_lpc env k body s.base bj hj
          cases hb : lsemStraightMemC env body bj with
          | none =>
              simp only [Option.map_none, Option.bind_none]
              -- the body-fold fails from `bj`: the segment run gives `none`.
              have h2 := segCallC env Q body
                { base := bj, lfn := fn, rstack := s.rstack } (1 + f) rfl hok
                (by intro k hk
                    show (loopLinstrRM top nReg body)[bj.lpc + k]? = body[k]?
                    rw [hbj_lpc]; exact loopCall_body_pos top nReg body k hk)
              rw [show (fuelCostC env body + 1) + f = fuelCostC env body + (1 + f) from by omega,
                h2, hb, Option.bind_none]
          | some blast =>
              simp only [Option.map_some, Option.bind_some]
              have htaken : condNZ blast (.reg nReg) = true := by
                have hfold : runBoundedLoopMemC env body (n + 1) s.base = some (blast.setLpc 1) := by
                  rw [runBoundedLoopMemC_succ_right, hj, Option.bind_some, hb, Option.map_some]
                have := htk (n + 1) (by omega) (by omega) (blast.setLpc 1) hfold
                rwa [condNZ_setLpc] at this
              have hpass := loopCall_pass_taken env fn top nReg body hok
                { base := bj, lfn := fn, rstack := s.rstack } blast f
                rfl hbj_lpc hb htaken
              rw [← hQ] at hpass
              rw [hpass]

/-- **The bounded memref-loop-with-calls bridge.**  For the loop program with a
    call-containing body, starting at the top of the body (`lpc = 1`), given the
    counter schedule (back-edge taken after iterations `1..m-1`, the `m`-th
    body-fold `lsemStraightMemC body bprev = blast` with the counter zero after
    it), the interpreter runs `m*(fuelCostC body + 1)` steps and halts in a state
    whose base agrees with `runBoundedLoopMemC env body m s.base` on the register
    store and the array carrier — the region-call loop realises the concrete-leaf
    fold for arbitrary trip count `m`. -/
theorem loopCall_runBounded (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (loopLinstrRM top nReg body)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMemC env body (m - 1) s.base = some bprev)
    (hlast : lsemStraightMemC env body bprev = some blast)
    (hbfin : runBoundedLoopMemC env body m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMemC env body i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (fuelCostC env body + 1)) s = some t
        ∧ t.base.reg.lvm = bfin.reg.lvm ∧ t.base.larr = bfin.larr := by
  set Q := singletonProgM fn (loopLinstrRM top nReg body) with hQ
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hprev
  have htk : ∀ i, 0 < i → i ≤ k → ∀ bi, runBoundedLoopMemC env body i s.base = some bi →
      condNZ bi (.reg nReg) = true := fun i hi hik bi hbi => htaken i hi (by omega) bi hbi
  have hchain := loopCall_taken_chain env fn top nReg body hok s hfn hpc k
    (fuelCostC env body + 1) htk
  have hfuel : (k + 1) * (fuelCostC env body + 1)
      = k * (fuelCostC env body + 1) + (fuelCostC env body + 1) := by ring
  rw [hfuel, hchain, hprev, Option.bind_some]
  have hhaltpass := loopCall_pass_halt env fn top nReg body hok
    { base := bprev, lfn := fn, rstack := s.rstack } blast rfl
    (by
      cases k with
      | zero => rw [runBoundedLoopMemC_zero] at hprev; obtain rfl := Option.some.inj hprev; exact hpc
      | succ j => exact runBoundedLoopMemC_succ_lpc env j body s.base bprev hprev)
    hlast hhalt
  rw [← hQ] at hhaltpass
  rw [hhaltpass]
  have hbfin' : bfin = blast.setLpc 1 := by
    have : runBoundedLoopMemC env body (k + 1) s.base = some (blast.setLpc 1) := by
      rw [runBoundedLoopMemC_succ_right, hprev, Option.bind_some, hlast, Option.map_some]
    rw [this] at hbfin; exact (Option.some.inj hbfin).symm
  exact ⟨_, rfl, by rw [hbfin']; rfl, by rw [hbfin']; rfl⟩

/-! ## 7. Validate: a memref loop that CALLS a leaf per element

`acc += buf[i]` over a 3-element buffer, where the accumulate is performed by an
in-`LeafEnvM` leaf `sum` invoked by a real `Lcall` per iteration.  The loop body:
`LOADIDX t := buf[i]`, `Lcall sum` (the leaf does `acc += t`), `i += 1`, `n -= 1`.
Run by `lsemFuelMemLC`; checked by `native_decide` to decode `acc = 60` and to
agree with the concrete-leaf `runBoundedLoopMemC` fold. -/

/-- The linked leaf environment: `sum` maps to the owned body `acc += t; Lret`. -/
def sumEnv : LeafEnvM := fun name =>
  if name = "sum" then
    some [ (LinstrR.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .reg "t"], MemTag.reg none)
         , (LinstrR.Lret, MemTag.reg none) ]
  else none

/-- The loop body: load `buf[i]` into `t`, **call** the `sum` leaf (`acc += t`),
    `i += 1`, `n -= 1`.  The accumulate step is a real region `Lcall`. -/
def callBody : List LinstrRM :=
  [ (LinstrR.Lopn [.reg "t"] "LOADIDX" [.arrIdx "buf" "i" 8], MemTag.load 64 3)
  , (LinstrR.Lcall none ("sum", (0 : LLabel)), MemTag.reg none)
  , (LinstrR.Lopn [.reg "i"] "ADD:64" [.reg "i", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "n"] "SUB:64" [.reg "n", .imm 1], MemTag.reg none) ]

/-- The looped call program: `callBody` wrapped in the back-edge on counter `n`. -/
def callProg : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" callBody)

/-- The start state: `acc = 0`, `i = 0`, `n = 3`, `buf = [10, 20, 30]`, pc at the
    loop label, an empty return stack. -/
def callStart : LstatePMC :=
  { base :=
      ((((({} : LstateM).setReg "acc" (0#64)).setReg "i" (0#64)).setReg "n" (3#64)).setArr
        "buf" (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64))
    lfn := "f"
    rstack := [] }

/-- **Validate (functional).**  The interpreter runs the 3-iteration memref loop
    whose body calls the `sum` leaf each pass, and the result register `acc`
    decodes to `10 + 20 + 30 = 60` — the region call actually invoked the concrete
    leaf per element over the shared `LstateM`. -/
theorem callLoop_validate :
    (lsemFuelMemLC sumEnv callProg 40 callStart).map (fun t => decodeM t.base "acc" 64)
      = some (some (60#64)) := by native_decide

/-- **Validate (fold agreement).**  The interpreter's decoded result equals the
    `runBoundedLoopMemC` fold (which resolves each call to the concrete leaf) of
    the same body over the same start — the region-call interpreter realises the
    concrete-leaf fold. -/
theorem callLoop_fold_agreement :
    (lsemFuelMemLC sumEnv callProg 40 callStart).map (fun t => decodeM t.base "acc" 64)
      = (runBoundedLoopMemC sumEnv callBody 3 callStart.base).map
          (fun b => decodeM b "acc" 64) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
