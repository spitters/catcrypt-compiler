/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC

@[expose] public section

set_option autoImplicit false

/-!
# Labeled control-transfer over the memref-bundled state `LstateM` (capability A1)

`JasminLsemGeneralFaithfulMem` lifted the stack-memory fragment
(`stackLoad`/`stackStore` over the aliasing array carrier) into a
program-indexed, fuel-stepped interpreter `lsemFuelMem` over the bundled state
`LstateM` (register file + array carrier).  That interpreter is **straight-line
only** — its `evalInstrPMem` delegates every typed instruction to `lsemStepMem`
on the base, and `findInstrMem` simply reads `body[lpc]?`; there is no
control-transfer arm, so loops cannot run over the memref state.

The register-only labeled interpreter `JasminLsemLabeled.lsemFuel` (over
`LstateP`) *does* have control flow (`Llabel`/`Lcond`/`Lgoto`, label resolution,
back-edges) but no memory.  This module **unifies the two**: a full labeled
fuel-stepped interpreter `lsemFuelMemL` over the memref state `LstateM` — the
control-transfer arm (`Llabel`/`Lcond`/`Lgoto`, label resolution, back-edges)
threading the register carrier *and* the aliasing array carrier through
unchanged (control flow doesn't touch memory), so **loops run over the memref
state**.

## Structure

* `evalInstrPMemL` resolves `Llabel` (pc bump / marker), `Lcond` (conditional
  back-edge — reads the counter register off the bundled base's register half,
  jumps to the resolved label, threading the array carrier unchanged) and
  `Lgoto`; **every other instruction is the straight-line/memory step
  `lsemStepMem` on the base** (the exact delegate `JasminLsemGeneralFaithfulMem`'s
  `evalInstrPMem` uses), so `lsemStepMem`'s straight-line + memory behaviour is
  reused verbatim.
* `findInstrMem` (fetch) is the same `body[lpc]?` as the straight-line
  interpreter — only the *eval* arm gains control transfer (it changes `lpc`).
* `lsemFuelMemL` iterates `evalInstrPMemL`, halting when `findInstrMem` is `none`
  (lpc past the body end), exactly as `lsemFuelMem` does.  On a control-free
  body it coincides with the straight-line fold (`lsemFuelMemL_seg`), so this is
  a conservative extension of `JasminLsemGeneralFaithfulMem.lsemFuelMem`.

  (This module imports `JasminLsemMem` directly and re-states the small
  program-layer scaffolding — `LstatePM`/`LprogM`/`findInstrMem`/`singletonProgM`
  — over `LstateM`, rather than importing `JasminLsemGeneralFaithfulMem`, only to
  keep the import cone off a sibling file that a concurrent call-marshalling
  churn left transiently unbuildable; the definitions here match that module's
  verbatim and can be re-based onto it once the tree restabilises.)

## The loop-lowering bridge

`loopLinstrRM top nReg body = Llabel top :: body ++ [Lcond nReg → top]` is the
owned-backend counter-loop shape over the typed memref instruction list (the
`LstateM` analogue of `X86Backend.LprogControlFlow.loopLcmd`).  `runBoundedLoopMem`
is the fold — running the body-fold `lsemStraightMem body` `n` times over
`LstateM` (the `runBoundedLoop`/`JState` analogue lifted to carry the array,
resetting the pc at each back-edge exactly as the interpreter does).

The core bridge is the two single-pass back-edge lemmas
(`loopMem_pass_taken` / `loopMem_pass_halt`) — the "loop-back-edge over
`LstateM` denotes one body-fold then loops / exits" content — assembled into the
`n`-fold `loopMem_runBounded`.  The body is a **general** `List LinstrRM` over
`LstateM` (not a fixed straight-line shape), so a loop body can later carry a
call (A2) or nest (A3): this is the lowering target for a future
`scf.for`-with-region-call.

## Validation

`§ Validate` runs a concrete memref-accumulate loop (`acc += buf[i]` over a
3-element buffer) through `lsemFuelMemL` and checks by `native_decide` that the
result decodes to the expected fold, and that it agrees with `runBoundedLoopMem`.

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound} (+ `Lean.ofReduceBool`
for the `native_decide` validate).**  The `lsem→bytes` encoder and Sail tables
remain the declared trusted base.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

/-! ## 1. The program counter and `setcpc` on the bundled state -/

/-- The program counter of the bundled state lives on its register half. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem.LstateM.lpc
    (s : LstateM) : Nat := s.reg.lpc

@[simp] theorem LstateM.lpc_nextPc (s : LstateM) : s.nextPc.lpc = s.lpc + 1 := by
  simp [LstateM.lpc, LstateM.nextPc]

@[simp] theorem LstateM.lpc_setReg (s : LstateM) (r : String) {w : Nat} (v : BitVec w) :
    (s.setReg r v).lpc = s.lpc := by simp [LstateM.lpc]

@[simp] theorem LstateM.lpc_setArr (s : LstateM) (r : String) {w n : Nat}
    (arr : Fin n → BitVec w) : (s.setArr r arr).lpc = s.lpc := by simp [LstateM.lpc]

/-- Set the program counter of the bundled state (on its register half), leaving
    the register store and the array carrier unchanged. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem.LstateM.setLpc
    (s : LstateM) (pc : Nat) : LstateM :=
  { s with reg := { s.reg with lpc := pc } }

@[simp] theorem LstateM.lpc_setLpc (s : LstateM) (pc : Nat) : (s.setLpc pc).lpc = pc := rfl

/-! ## 2. `lsemStepMem` advances the pc by one (any instruction) -/

/-- Every successful typed width-cast step advances the pc by one (a local copy of
    `JasminLsemLabeledLeaf.lsemStepCast_lpc_succ`, re-proved over `JasminLsemLabeledMC`
    to keep the import cone off a sibling file left transiently unbuildable). -/
theorem lsemStepCast_lpc_succ' (i : LinstrRT) (s s' : LstateN)
    (h : lsemStepCast i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold lsemStepCast at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp [LstateN.lpc_nextPc, LstateN.lpc_setReg])
      | exact absurd h (by simp)
      | exact lsemStepMC_lpc_succ _ s s' h

/-- **Every successful bundled step advances the pc by one.**  A `LOADIDX` writes
    the loaded value and `.nextPc`s; a `STOREIDX` writes the new array and
    `.nextPc`s; every register-delegated arm runs `lsemStepCast` over the register
    half (`lsemStepCast_lpc_succ`), the array carrier untouched. -/
theorem lsemStepMem_lpc_succ (i : LinstrRM) (s s' : LstateM)
    (h : lsemStepMem i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold lsemStepMem at h
  repeat' split at h
  all_goals
    first
      | (obtain ⟨r, hr, hrfl⟩ := h
         subst hrfl
         simpa [LstateM.lpc] using lsemStepCast_lpc_succ' _ _ _ hr)
      | (obtain ⟨r, hr, hrfl⟩ := Option.map_eq_some_iff.mp h
         subst hrfl
         simpa [LstateM.lpc] using lsemStepCast_lpc_succ' _ _ _ hr)
      | (obtain rfl := Option.some.inj h
         simp [LstateM.lpc, LstateM.nextPc, LstateM.setReg, LstateM.setArr])
      | simp at h

/-! ## 3. The program-indexed bundled state, program, and fetch -/

/-- The program-indexed bundled state: the memref bundled state `LstateM` plus the
    current function name `lfn`. -/
structure LstatePM where
  /-- The bundled stack-memory base (register file + array carrier + pc). -/
  base : LstateM
  /-- The current function name. -/
  lfn : String

/-- A typed singleton program: the one function `lfn` with the typed body
    `body : List LinstrRM`. -/
structure LprogM where
  /-- The sole function's name. -/
  lfn : String
  /-- The sole function's typed body. -/
  body : List LinstrRM

/-- The typed singleton program with function `fn` and typed body `body`. -/
def singletonProgM (fn : String) (body : List LinstrRM) : LprogM := ⟨fn, body⟩

/-- `find_instr`: the typed instruction at `lpc` in the current function's body,
    or `none` (halted / out of range / wrong function).  Shared with the
    straight-line interpreter — only *eval* gains control transfer. -/
def findInstrMem (P : LprogM) (s : LstatePM) : Option LinstrRM :=
  if s.lfn = P.lfn then P.body[s.base.lpc]? else none

/-! ## 4. Label resolution and the control-transfer eval arm

Label resolution reads the wire projection of the typed body (`body.map Prod.fst`)
— the byte-for-byte emitted instruction stream — via the register-side
`JasminLsemLabeled.findLabel`, so the array-shape `MemTag` never enters label
search. -/

/-- `find_label lbl body` over the typed memref body: search the **wire**
    projection for the first `Llabel _ lbl`. -/
def findLabelMem (lbl : LLabel) (body : List LinstrRM) : Option Nat :=
  JasminLsemLabeled.findLabel lbl (body.map Prod.fst)

/-- `eval_jump`: resolve label `lbl` in the (single-function) program's typed body
    and jump to the instruction **after** the label (`setLpc (pc+1)`), threading
    both carriers unchanged.  `none` if the label is absent. -/
def evalJumpMem (P : LprogM) (lbl : LLabel) (s : LstatePM) : Option LstatePM :=
  match findLabelMem lbl P.body with
  | some pc => some { s with base := s.base.setLpc (pc + 1) }
  | none => none

/-- The `Lcond`/`Lgoto` boolean condition: the operand reads a **non-zero** word
    off the bundled base's register half (at the counter width 64).  For a loop
    back-edge `Lcond (.reg nReg) top` this is "the counter `nReg` is non-zero" —
    the `while (n != 0)` guard.  A read miss is false (fall through). -/
def condNZ (s : LstateM) (cond : LOperand) : Bool :=
  match evalOperandN s.reg 64 cond with
  | some v => decide (v ≠ 0#64)
  | none => false

/-- The loop counter test ignores the pc: `setLpc` leaves the register store
    `condNZ` reads unchanged. -/
@[simp] theorem condNZ_setLpc (s : LstateM) (pc : Nat) (cond : LOperand) :
    condNZ (s.setLpc pc) cond = condNZ s cond := rfl

/-- **The control-transfer eval arm over the bundled state.**  `Llabel` bumps the
    pc (inert marker); `Lcond cond lbl` jumps to `lbl` iff `condNZ`, else falls
    through (`nextPc`); `Lgoto (fn,lbl)` jumps within the single function.  **Every
    other instruction is the straight-line/memory step `lsemStepMem` on the base**
    (the exact delegate the straight-line interpreter uses).  Control flow only
    rewrites `lpc`/`lfn`; the register store and array carrier are unchanged. -/
def evalInstrPMemL (P : LprogM) (i : LinstrRM) (s : LstatePM) : Option LstatePM :=
  match i.fst with
  | .Llabel _ _ => some { s with base := s.base.nextPc }
  | .Lcond cond lbl =>
      if condNZ s.base cond then evalJumpMem P lbl s
      else some { s with base := s.base.nextPc }
  | .Lgoto (fn, lbl) => if fn = P.lfn then evalJumpMem P lbl s else none
  | _ => (lsemStepMem i s.base).map (fun b => { s with base := b })

/-- `step`: fetch (shared `findInstrMem`) and control-transfer-eval. -/
def lsemStepPMemL (P : LprogM) (s : LstatePM) : Option LstatePM :=
  match findInstrMem P s with
  | some i => evalInstrPMemL P i s
  | none => none

/-- **The full labeled fuel-stepped interpreter over `LstateM`.**  Iterate
    `lsemStepPMemL` up to `fuel` times, halting (returning the state) when
    `findInstrMem` is `none`.  Unlike the straight-line `lsemFuelMem`, this
    follows `Llabel`/`Lcond`/`Lgoto` back-edges, so **loops run over the memref
    state**. -/
def lsemFuelMemL (P : LprogM) : Nat → LstatePM → Option LstatePM
  | 0, s => match findInstrMem P s with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s with
      | none => some s
      | some i =>
          match evalInstrPMemL P i s with
          | some s' => lsemFuelMemL P fuel s'
          | none => none

/-- A halted state (`findInstrMem = none`) takes no step. -/
theorem lsemFuelMemL_halt (P : LprogM) (fuel : Nat) (s : LstatePM)
    (h : findInstrMem P s = none) : lsemFuelMemL P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelMemL, h]
  | succ n => simp [lsemFuelMemL, h]

/-- **Determinism**: same fuel ⇒ same result. -/
theorem lsemFuelMemL_deterministic (P : LprogM) (fuel : Nat) (s t1 t2 : LstatePM)
    (h1 : lsemFuelMemL P fuel s = some t1) (h2 : lsemFuelMemL P fuel s = some t2) :
    t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-- **Monotonicity**: once a halted result is reached, extra fuel is a no-op. -/
theorem lsemFuelMemL_mono (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstatePM),
      lsemFuelMemL P fuel s = some t → lsemFuelMemL P (fuel + 1) s = some t := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      rw [lsemFuelMemL] at h
      cases hf : findInstrMem P s with
      | none =>
          rw [hf] at h
          obtain rfl := Option.some.inj h
          exact lsemFuelMemL_halt P 1 s hf
      | some i => rw [hf] at h; exact absurd h (by simp)
  | succ n ih =>
      intro s t h
      rw [lsemFuelMemL] at h
      rw [lsemFuelMemL]
      cases hf : findInstrMem P s with
      | none => rw [hf] at h; exact h
      | some i =>
          rw [hf] at h
          simp only [] at h ⊢
          cases he : evalInstrPMemL P i s with
          | none => rw [he] at h; exact absurd h (by simp)
          | some s' => rw [he] at h; exact ih s' t h

/-- More fuel never changes a reached result. -/
theorem lsemFuelMemL_mono_add (P : LprogM) (fuel : Nat) (s t : LstatePM)
    (h : lsemFuelMemL P fuel s = some t) : ∀ k, lsemFuelMemL P (fuel + k) s = some t := by
  intro k
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have : fuel + (n + 1) = (fuel + n) + 1 := by omega
      rw [this]; exact lsemFuelMemL_mono P (fuel + n) s t ih

/-! ## 5. Conservative extension: `Lopn` instructions are the straight-line step -/

/-- An `Lopn` (non-control) wire: the delegate arm of `evalInstrPMemL`. -/
def IsLopn (i : LinstrRM) : Prop := ∃ d o s, i.fst = LinstrR.Lopn d o s

/-- On an `Lopn` instruction, `evalInstrPMemL` is exactly the straight-line/memory
    step `lsemStepMem` lifted over the base — the per-instruction
    conservative-extension tie (`evalInstrPMem` of the straight-line interpreter). -/
theorem evalInstrPMemL_lopn (P : LprogM) (i : LinstrRM) (s : LstatePM)
    (hi : IsLopn i) :
    evalInstrPMemL P i s = (lsemStepMem i s.base).map (fun b => { s with base := b }) := by
  obtain ⟨d, o, src, hd⟩ := hi
  unfold evalInstrPMemL
  rw [hd]

/-! ## 6. The loop shape and its fold semantics over `LstateM` -/

/-- The owned-backend counter-loop shape over the typed memref instruction list:
    `Llabel top :: body ++ [Lcond (.reg nReg) top]`.  The `LstateM`/`LinstrRM`
    analogue of `X86Backend.LprogControlFlow.loopLcmd`: the back-edge reads the
    counter register `nReg` directly (`while (nReg != 0)`), and `body` is assumed
    to perform its own `nReg -= 1`.  The body is a **general** `List LinstrRM`
    (loads/stores/arith over `LstateM`), so it can later carry a call/nest — the
    `scf.for`-with-region-call lowering target. -/
def loopLinstrRM (top : LLabel) (nReg : String) (body : List LinstrRM) : List LinstrRM :=
  (LinstrR.Llabel .internal top, MemTag.reg none)
    :: (body ++ [(LinstrR.Lcond (.reg nReg) top, MemTag.reg none)])

/-- **The fold semantics of a bounded memref loop.**  Run the body-fold
    `lsemStraightMem body` exactly `n` times over the bundled state `LstateM`
    (register file *and* array carrier), resetting the pc to `1` (the top of the
    body) after each iteration — exactly as the interpreter's back-edge does.  The
    `LstateM` analogue of `LoopUnroll.runBoundedLoop` (over `JState`), lifted to
    thread the aliasing array carrier.  Only the pc is reset; the register store
    and array carrier are the pure body-fold. -/
def runBoundedLoopMem (body : List LinstrRM) : Nat → LstateM → Option LstateM
  | 0, s => some s
  | k + 1, s =>
      (lsemStraightMem body s).bind (fun b => runBoundedLoopMem body k (b.setLpc 1))

@[simp] theorem runBoundedLoopMem_zero (body : List LinstrRM) (s : LstateM) :
    runBoundedLoopMem body 0 s = some s := rfl

@[simp] theorem runBoundedLoopMem_succ (body : List LinstrRM) (k : Nat) (s : LstateM) :
    runBoundedLoopMem body (k + 1) s =
      (lsemStraightMem body s).bind (fun b => runBoundedLoopMem body k (b.setLpc 1)) := rfl

/-! ## 7. Execution lemmas and the single-pass loop-back-edge core -/

/-- The body-fold advances the pc by the body length (each `lsemStepMem` advances
    by one), for **any** body. -/
theorem lsemStraightMem_lpc :
    ∀ (body : List LinstrRM) (s b : LstateM),
      lsemStraightMem body s = some b → b.lpc = s.lpc + body.length := by
  intro body
  induction body with
  | nil => intro s b h; simp only [lsemStraightMem_nil, Option.some.injEq] at h; subst h; simp
  | cons i is ih =>
      intro s b h
      rw [lsemStraightMem_cons] at h
      cases hstep : lsemStepMem i s with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some s' =>
          rw [hstep] at h
          have h1 : s'.lpc = s.lpc + 1 := lsemStepMem_lpc_succ i s s' hstep
          have h2 : b.lpc = s'.lpc + is.length := ih s' b h
          rw [h2, h1, List.length_cons]; omega

/-- **Straight-line segment run with continuation fuel.**  If the `Lopn` segment
    `seg` occupies positions `lpc .. lpc+|seg|-1` of the program body, then running
    `lsemFuelMemL` for `|seg| + f` fuel executes the body-fold `lsemStraightMem
    seg` on the base and then continues with `f` fuel from the resulting state. -/
theorem lsemFuelMemL_seg (P : LprogM) :
    ∀ (seg : List LinstrRM) (s : LstatePM) (f : Nat),
      s.lfn = P.lfn →
      (∀ i ∈ seg, IsLopn i) →
      (∀ k, k < seg.length → P.body[s.base.lpc + k]? = seg[k]?) →
      lsemFuelMemL P (seg.length + f) s
        = (lsemStraightMem seg s.base).bind
            (fun b => lsemFuelMemL P f { base := b, lfn := s.lfn }) := by
  intro seg
  induction seg with
  | nil =>
      intro s f hfn _ _
      simp only [List.length_nil, Nat.zero_add, lsemStraightMem_nil, Option.bind_some]
  | cons i is ih =>
      intro s f hfn hlopn hpos
      have hi : IsLopn i := hlopn i (by simp)
      have his : ∀ j ∈ is, IsLopn j := fun j hj => hlopn j (by simp [hj])
      have hfetch : findInstrMem P s = some i := by
        unfold findInstrMem
        rw [if_pos hfn]
        have := hpos 0 (by simp)
        simpa using this
      rw [List.length_cons, show is.length + 1 + f = (is.length + f) + 1 from by omega,
        lsemFuelMemL, hfetch]
      simp only []
      rw [evalInstrPMemL_lopn P i s hi]
      cases hstep : lsemStepMem i s.base with
      | none =>
          simp only [Option.map_none]
          rw [lsemStraightMem_cons, hstep]; rfl
      | some b =>
          simp only [Option.map_some]
          rw [lsemStraightMem_cons, hstep]
          have hb_lpc : b.lpc = s.base.lpc + 1 := lsemStepMem_lpc_succ i s.base b hstep
          have hpos' : ∀ k, k < is.length →
              P.body[({ base := b, lfn := s.lfn } : LstatePM).base.lpc + k]? = is[k]? := by
            intro k hk
            have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
            show P.body[b.lpc + k]? = is[k]?
            rw [hb_lpc, show s.base.lpc + 1 + k = s.base.lpc + (k + 1) from by omega]
            rw [hp]; simp
          have := ih { base := b, lfn := s.lfn } f hfn his hpos'
          simpa using this

/-- `findLabelMem` finds the loop's top label at position 0 (the head of
    `loopLinstrRM`). -/
theorem findLabelMem_loop (top : LLabel) (nReg : String) (body : List LinstrRM) :
    findLabelMem top (loopLinstrRM top nReg body) = some 0 := by
  unfold findLabelMem loopLinstrRM JasminLsemLabeled.findLabel
  rw [List.map_cons, List.findIdx?_cons]
  simp [JasminLsemLabeled.isLabel]

/-- Position of the body in the loop program: index `1+k` is `body[k]` for
    `k < body.length` (index 0 is the label). -/
theorem loop_body_pos (top : LLabel) (nReg : String) (body : List LinstrRM)
    (k : Nat) (hk : k < body.length) :
    (loopLinstrRM top nReg body)[1 + k]? = body[k]? := by
  unfold loopLinstrRM
  rw [show 1 + k = k + 1 from by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by simpa using hk)]

/-- Position of the back-edge in the loop program: index `1 + body.length`. -/
theorem loop_cond_pos (top : LLabel) (nReg : String) (body : List LinstrRM) :
    (loopLinstrRM top nReg body)[1 + body.length]? =
      some (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) := by
  unfold loopLinstrRM
  rw [show 1 + body.length = body.length + 1 from by omega, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- **Single loop pass — back-edge TAKEN.**  From the top of the body
    (`lpc = 1`), if the body-fold runs `lsemStraightMem body s.base = some b` and
    the counter `nReg` is non-zero at `b`, then one pass (body + taken back-edge)
    consumes `body.length + 1` fuel and lands back at the top with base `b` (pc
    reset to `1`) — `lsemFuelMemL` continues with `f` fuel from
    `{ base := b.setLpc 1, lfn }`.  The "loop-back-edge denotes one body-fold then
    loops" core. -/
theorem loopMem_pass_taken (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (b : LstateM) (f : Nat)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hbody : lsemStraightMem body s.base = some b)
    (htaken : condNZ b (.reg nReg) = true) :
    lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body)) (body.length + 1 + f) s
      = lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body)) f
          { base := b.setLpc 1, lfn := fn } := by
  subst hfn
  set P := singletonProgM s.lfn (loopLinstrRM top nReg body) with hP
  have hPbody : P.body = loopLinstrRM top nReg body := rfl
  have hseg := lsemFuelMemL_seg P body s (1 + f) rfl
    (fun i hi => hlopn i hi)
    (by intro k hk; show P.body[s.base.lpc + k]? = body[k]?
        rw [hPbody, hpc]; exact loop_body_pos top nReg body k hk)
  rw [show body.length + 1 + f = body.length + (1 + f) from by omega, hseg, hbody,
    Option.bind_some]
  have hb_lpc : b.lpc = 1 + body.length := by
    have := lsemStraightMem_lpc body s.base b hbody; rw [hpc] at this; omega
  have hfetch : findInstrMem P { base := b, lfn := s.lfn } =
      some (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) := by
    have hc : ({ base := b, lfn := s.lfn } : LstatePM).lfn = P.lfn := rfl
    unfold findInstrMem
    rw [if_pos hc, hPbody]
    show (loopLinstrRM top nReg body)[b.lpc]? = _
    rw [hb_lpc]; exact loop_cond_pos top nReg body
  rw [show 1 + f = f + 1 from by omega, lsemFuelMemL, hfetch]
  simp only []
  unfold evalInstrPMemL
  simp only [htaken, if_true]
  unfold evalJumpMem
  rw [hPbody, findLabelMem_loop]

/-- **Single loop pass — back-edge NOT taken (HALT).**  From the top of the body,
    if the body-fold runs `lsemStraightMem body s.base = some b` and the counter
    `nReg` is zero at `b`, then one pass consumes `body.length + 1` fuel, falls
    through the back-edge (`nextPc`), and halts — `lsemFuelMemL` returns
    `{ base := b.nextPc, lfn }`.  The loop's exit. -/
theorem loopMem_pass_halt (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (b : LstateM)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hbody : lsemStraightMem body s.base = some b)
    (hhalt : condNZ b (.reg nReg) = false) :
    lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body)) (body.length + 1) s
      = some { base := b.nextPc, lfn := fn } := by
  subst hfn
  set P := singletonProgM s.lfn (loopLinstrRM top nReg body) with hP
  have hPbody : P.body = loopLinstrRM top nReg body := rfl
  have hseg := lsemFuelMemL_seg P body s 1 rfl
    (fun i hi => hlopn i hi)
    (by intro k hk; show P.body[s.base.lpc + k]? = body[k]?
        rw [hPbody, hpc]; exact loop_body_pos top nReg body k hk)
  rw [hseg, hbody, Option.bind_some]
  have hb_lpc : b.lpc = 1 + body.length := by
    have := lsemStraightMem_lpc body s.base b hbody; rw [hpc] at this; omega
  have hfetch : findInstrMem P { base := b, lfn := s.lfn } =
      some (LinstrR.Lcond (.reg nReg) top, MemTag.reg none) := by
    have hc : ({ base := b, lfn := s.lfn } : LstatePM).lfn = P.lfn := rfl
    unfold findInstrMem
    rw [if_pos hc, hPbody]
    show (loopLinstrRM top nReg body)[b.lpc]? = _
    rw [hb_lpc]; exact loop_cond_pos top nReg body
  have hhaltfetch : findInstrMem P { base := b.nextPc, lfn := s.lfn } = none := by
    have hc : ({ base := b.nextPc, lfn := s.lfn } : LstatePM).lfn = P.lfn := rfl
    unfold findInstrMem
    rw [if_pos hc, hPbody]
    show (loopLinstrRM top nReg body)[(b.nextPc).lpc]? = none
    have hpc2 : (b.nextPc).lpc = body.length + 2 := by
      rw [LstateM.lpc_nextPc, hb_lpc]; omega
    rw [hpc2]
    apply List.getElem?_eq_none
    unfold loopLinstrRM
    simp [List.length_append]
  change lsemFuelMemL P (0 + 1) { base := b, lfn := s.lfn } = _
  rw [lsemFuelMemL, hfetch]
  simp only []
  unfold evalInstrPMemL
  simp only [hhalt, if_false]
  exact lsemFuelMemL_halt P 0 { base := b.nextPc, lfn := s.lfn } hhaltfetch

/-! ## 8. Structural facts on `runBoundedLoopMem` (for the `n`-fold bridge) -/

/-- After at least one iteration, the fold's state sits at the loop top (`lpc = 1`,
    from the back-edge's `setLpc 1`). -/
theorem runBoundedLoopMem_succ_lpc :
    ∀ (k : Nat) (body : List LinstrRM) (s bj : LstateM),
      runBoundedLoopMem body (k + 1) s = some bj → bj.lpc = 1 := by
  intro k
  induction k with
  | zero =>
      intro body s bj h
      rw [runBoundedLoopMem_succ] at h
      cases hb : lsemStraightMem body s with
      | none => rw [hb] at h; simp at h
      | some b =>
          rw [hb, Option.bind_some, runBoundedLoopMem_zero] at h
          obtain rfl := Option.some.inj h
          simp
  | succ n ih =>
      intro body s bj h
      rw [runBoundedLoopMem_succ] at h
      cases hb : lsemStraightMem body s with
      | none => rw [hb] at h; simp at h
      | some b => rw [hb, Option.bind_some] at h; exact ih body (b.setLpc 1) bj h

/-- Peel the **last** fold: `runBoundedLoopMem body (j+1) s` runs `j` folds then
    one more body-fold (with the back-edge's `setLpc 1`). -/
theorem runBoundedLoopMem_succ_right :
    ∀ (j : Nat) (body : List LinstrRM) (s : LstateM),
      runBoundedLoopMem body (j + 1) s =
        (runBoundedLoopMem body j s).bind
          (fun bj => (lsemStraightMem body bj).map (fun b => b.setLpc 1)) := by
  intro j
  induction j with
  | zero =>
      intro body s
      simp only [runBoundedLoopMem_succ, runBoundedLoopMem_zero, Option.bind_some]
      cases lsemStraightMem body s <;> simp
  | succ n ih =>
      intro body s
      rw [runBoundedLoopMem_succ]
      conv_rhs => rw [runBoundedLoopMem_succ]
      cases hb : lsemStraightMem body s with
      | none => simp
      | some b => rw [Option.bind_some, Option.bind_some]; exact ih body (b.setLpc 1)

/-! ## 9. The `n`-fold loop bridge

Assemble the two single-pass lemmas into the full bounded-loop bridge: from the
top of the body, running `lsemFuelMemL` realises `runBoundedLoopMem body m` — the
`m`-fold of the body over `LstateM`.  The trip count `m` is characterised by the
counter schedule: after each of the first `m-1` iterations the counter is
non-zero (back-edge taken), and after the `m`-th it is zero (halt). -/

/-- **Taken chain.**  If the back-edge is taken after every iteration `1..j`, the
    interpreter runs the first `j` passes and continues (with `f` fuel) from the
    fold's `j`-th state — `lsemFuelMemL P (j*(|body|+1) + f) s` factors through
    `runBoundedLoopMem body j s.base`. -/
theorem loopMem_taken_chain (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1) :
    ∀ (j f : Nat),
      (∀ i, 0 < i → i ≤ j → ∀ bi, runBoundedLoopMem body i s.base = some bi →
        condNZ bi (.reg nReg) = true) →
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          (j * (body.length + 1) + f) s
        = (runBoundedLoopMem body j s.base).bind
            (fun bj => lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body)) f
              { base := bj, lfn := fn }) := by
  set P := singletonProgM fn (loopLinstrRM top nReg body) with hP
  intro j
  induction j with
  | zero =>
      intro f _
      simp only [Nat.zero_mul, Nat.zero_add, runBoundedLoopMem_zero, Option.bind_some]
      have hs : ({ base := s.base, lfn := fn } : LstatePM) = s := by
        obtain ⟨sb, sl⟩ := s; simp only [LstatePM.mk.injEq, true_and]; exact hfn.symm
      rw [hs]
  | succ n ih =>
      intro f htk
      have htk' : ∀ i, 0 < i → i ≤ n → ∀ bi, runBoundedLoopMem body i s.base = some bi →
          condNZ bi (.reg nReg) = true := fun i hi hin bi hbi => htk i hi (by omega) bi hbi
      have hfuel : (n + 1) * (body.length + 1) + f
          = n * (body.length + 1) + ((body.length + 1) + f) := by ring
      rw [hfuel, ih ((body.length + 1) + f) htk']
      rw [runBoundedLoopMem_succ_right]
      cases hj : runBoundedLoopMem body n s.base with
      | none => simp
      | some bj =>
          simp only [Option.bind_some]
          -- `bj` sits at the loop top.
          have hbj_lpc : bj.lpc = 1 := by
            cases n with
            | zero =>
                rw [runBoundedLoopMem_zero] at hj; obtain rfl := Option.some.inj hj; exact hpc
            | succ k => exact runBoundedLoopMem_succ_lpc k body s.base bj hj
          have hsegpos : ∀ k, k < body.length →
              P.body[({ base := bj, lfn := fn } : LstatePM).base.lpc + k]? = body[k]? := by
            intro k hk
            show P.body[bj.lpc + k]? = body[k]?
            rw [hP]; show (loopLinstrRM top nReg body)[bj.lpc + k]? = body[k]?
            rw [hbj_lpc]; exact loop_body_pos top nReg body k hk
          cases hb : lsemStraightMem body bj with
          | none =>
              -- interpreter runs body from bj, fails; result none.
              have hseg := lsemFuelMemL_seg P body { base := bj, lfn := fn } (1 + f)
                rfl (fun i hi => hlopn i hi) hsegpos
              rw [show body.length + 1 + f = body.length + (1 + f) from by omega, hseg]
              simp only [Option.map_none, Option.bind_none]
              show (lsemStraightMem body bj).bind _ = none
              rw [hb]; rfl
          | some blast =>
              simp only [Option.map_some, Option.bind_some]
              -- the (n+1)-th back-edge is taken.
              have htaken : condNZ blast (.reg nReg) = true := by
                have hfold : runBoundedLoopMem body (n + 1) s.base = some (blast.setLpc 1) := by
                  rw [runBoundedLoopMem_succ_right, hj, Option.bind_some, hb, Option.map_some]
                have := htk (n + 1) (by omega) (by omega) (blast.setLpc 1) hfold
                rwa [condNZ_setLpc] at this
              have hpass := loopMem_pass_taken fn top nReg body hlopn
                { base := bj, lfn := fn } blast f rfl hbj_lpc hb htaken
              rw [← hP] at hpass
              exact hpass

/-- **The bounded memref-loop bridge.**  For the loop program `P = singletonProgM
    fn (loopLinstrRM top nReg body)` with an all-`Lopn` body, starting at the top
    of the body (`lpc = 1`), given the counter schedule — the back-edge is taken
    after iterations `1..m-1`, the `m`-th body-fold `lsemStraightMem body bprev`
    runs to `blast` with the counter zero after it — the interpreter runs
    `m*(|body|+1)` steps and halts in a state whose base agrees with
    `runBoundedLoopMem body m s.base` **on the register store and the array
    carrier** (they differ only in the exit pc: `nextPc` at the halt vs `setLpc 1`
    in the fold).  In particular the decoded result equals the fold. -/
theorem loopMem_runBounded (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem body (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem body bprev = some blast)
    (hbfin : runBoundedLoopMem body m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMem body i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (body.length + 1)) s = some t
        ∧ t.base.reg.lvm = bfin.reg.lvm ∧ t.base.larr = bfin.larr := by
  set P := singletonProgM fn (loopLinstrRM top nReg body) with hP
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hprev
  -- run the first `k` passes (all taken) via the chain, continuing with `|body|+1` fuel.
  have htk : ∀ i, 0 < i → i ≤ k → ∀ bi, runBoundedLoopMem body i s.base = some bi →
      condNZ bi (.reg nReg) = true := fun i hi hik bi hbi => htaken i hi (by omega) bi hbi
  have hchain := loopMem_taken_chain fn top nReg body hlopn s hfn hpc k (body.length + 1) htk
  have hfuel : (k + 1) * (body.length + 1) = k * (body.length + 1) + (body.length + 1) := by ring
  rw [hfuel, hchain, hprev, Option.bind_some]
  -- the last pass halts.
  have hhaltpass := loopMem_pass_halt fn top nReg body hlopn
    { base := bprev, lfn := fn } blast rfl
    (by
      -- `bprev` sits at the loop top.
      cases k with
      | zero => rw [runBoundedLoopMem_zero] at hprev; obtain rfl := Option.some.inj hprev; exact hpc
      | succ j => exact runBoundedLoopMem_succ_lpc j body s.base bprev hprev)
    hlast hhalt
  rw [← hP] at hhaltpass
  rw [hhaltpass]
  refine ⟨_, rfl, ?_, ?_⟩
  · -- register store: interpreter halts at `blast.nextPc`; fold ends at `blast.setLpc 1`.
    have hbfin' : bfin = blast.setLpc 1 := by
      have : runBoundedLoopMem body (k + 1) s.base = some (blast.setLpc 1) := by
        rw [runBoundedLoopMem_succ_right, hprev, Option.bind_some, hlast, Option.map_some]
      rw [this] at hbfin; exact (Option.some.inj hbfin).symm
    rw [hbfin']; rfl
  · have hbfin' : bfin = blast.setLpc 1 := by
      have : runBoundedLoopMem body (k + 1) s.base = some (blast.setLpc 1) := by
        rw [runBoundedLoopMem_succ_right, hprev, Option.bind_some, hlast, Option.map_some]
      rw [this] at hbfin; exact (Option.some.inj hbfin).symm
    rw [hbfin']; rfl

/-! ## 10. Validate: a concrete memref-accumulate loop over `lsemFuelMemL`

`acc += buf[i]` over a 3-element buffer `[10, 20, 30]`, ascending index `i`,
counter `n = 3` down to 0.  Body (all `Lopn`): a `LOADIDX buf[i]` into a scratch
register, `ADD acc, scratch`, `ADD i, 1`, `SUB n, 1`.  Wrapped by `loopLinstrRM`
into `Llabel :: body ++ [Lcond n → top]`, run by the labeled interpreter
`lsemFuelMemL` from the encoded start state.  Checked by `native_decide`: the
result decodes `acc = 60` — and equals `runBoundedLoopMem body 3`. -/

/-- The memref-accumulate loop body (all `Lopn`): load `buf[i]` (SIB `LOADIDX`),
    `acc += t`, `i += 1`, `n -= 1`. -/
def accBody : List LinstrRM :=
  [ (LinstrR.Lopn [.reg "t"] "LOADIDX" [.arrIdx "buf" "i" 8], MemTag.load 64 3)
  , (LinstrR.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .reg "t"], MemTag.reg none)
  , (LinstrR.Lopn [.reg "i"] "ADD:64" [.reg "i", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "n"] "SUB:64" [.reg "n", .imm 1], MemTag.reg none) ]

/-- The looped memref-accumulate program: `accBody` wrapped in the back-edge on
    counter `"n"`, top label `0`. -/
def accProg : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" accBody)

/-- The start bundled state: `acc = 0`, `i = 0`, `n = 3` (all 64-bit), the buffer
    `buf = [10, 20, 30]` in the array carrier, pc at the loop label (`0`). -/
def accStart : LstatePM :=
  { base :=
      ((((({} : LstateM).setReg "acc" (0#64)).setReg "i" (0#64)).setReg "n" (3#64)).setArr
        "buf" (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64))
    lfn := "f" }

/-- **Validate (functional).**  The labeled interpreter runs the 3-iteration
    memref loop and the result register `acc` decodes to `10 + 20 + 30 = 60` — the
    loop actually followed the back-edge three times over the memref state.  The
    fuel `20` (> `1 + 3*(4+1) = 16` for the label + three passes) is ample; the
    halt fixpoint absorbs the surplus. -/
example :
    (lsemFuelMemL accProg 20 accStart).map (fun t => decodeM t.base "acc" 64)
      = some (some (60#64)) := by native_decide

/-- **Validate (fold agreement).**  The interpreter's decoded result equals the
    `runBoundedLoopMem` fold of the same body over the same start (three
    body-folds) — the interpreter realises the fold. -/
example :
    (lsemFuelMemL accProg 20 accStart).map (fun t => decodeM t.base "acc" 64)
      = (runBoundedLoopMem accBody 3 accStart.base).map (fun b => decodeM b "acc" 64) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
