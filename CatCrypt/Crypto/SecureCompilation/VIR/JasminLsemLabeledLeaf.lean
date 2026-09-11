/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC

@[expose] public section

set_option autoImplicit false

/-!
# The labeled, program-indexed linear semantics over the typed `LinstrRT` IR (opaque-leaf)

`JasminLsemLabeledMC` ported jasmin's program-indexed `lsem` (`findInstrN`/
`evalInstrPN`/`lsemFuelMC`) over the width-tagged `LstateN` for the mul/carry fragment —
crucially over the *untyped* `LinstrR` instruction type and the `Lprog`/`Lfundef`
program structure of the labeled layer.

The opaque-leaf fragment (`JasminLsemLeaf`) instead runs over the **typed** instruction
`LinstrRT := LinstrR × Option Nat` (the wire `LinstrR` paired with a descriptor slot that
carries the cast / leaf result width — never on the wire) and is parametric over an opaque
leaf environment `leaf : LeafEnvN`. So the program-indexed semantics cannot reuse the
`LinstrR`-typed `Lprog`/`findInstrN`: it indexes a `List LinstrRT` body. The *state*
`LstatePN` (`LstateN` + the current function name `lfn`) fits unchanged — both fragments
run over `LstateN` — so we reuse it.

This is the typed counterpart of the labeled layer: a typed singleton program `LprogT`
(a function name + `List LinstrRT` body), `findInstrLeaf`, `evalInstrPNLeaf leaf`
(delegating the straight-line arms to `lsemStepLeaf leaf` on the base), `lsemFuelLeaf leaf`
(fuel-bounded iteration), and the straight-line bridge `lsemFuelLeaf_straightline` lifting
the opaque-leaf body-fold `lsemStraightLeaf` into the program-indexed `lsem`. It is the
target semantics for lifting `comToLprog_faithful_leaf` into `lsem`, the leaf analogue of
`JasminLsemLabeledMC.lsemFuelMC_straightline`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC

/-! ## The `lpc`-advancement chain: every successful typed leaf step advances the pc -/

/-- Every successful typed width-cast step advances the pc by one: the cast arm ends in
    `.nextPc`, the delegate arm is `lsemStepMC` on the wire (`lsemStepMC_lpc_succ`). -/
theorem lsemStepCast_lpc_succ (i : LinstrRT) (s s' : LstateN)
    (h : lsemStepCast i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold lsemStepCast at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp [LstateN.lpc_nextPc, LstateN.lpc_setReg])
      | exact absurd h (by simp)
      | exact lsemStepMC_lpc_succ _ s s' h

/-- **Every successful typed opaque-leaf step advances the pc by one.** The `extCall` arm
    writes the leaf result and `.nextPc`s; every other typed instruction delegates to
    `lsemStepCast` (`lsemStepCast_lpc_succ`). The leaf step's success arms all end in a
    pc bump, exactly as `lsemStepMC_lpc_succ`. -/
theorem lsemStepLeaf_lpc_succ (leaf : LeafEnvN) (i : LinstrRT) (s s' : LstateN)
    (h : lsemStepLeaf leaf i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold lsemStepLeaf at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp [LstateN.lpc_nextPc, LstateN.lpc_setReg])
      | exact absurd h (by simp)
      | exact lsemStepCast_lpc_succ _ s s' h

/-! ## The typed program and the program-indexed leaf state -/

/-- The program-indexed leaf state: the width-tagged `LstateN` straight-line state plus the
    current function name `lfn` (indexing the typed body). This is exactly the mul/carry
    `LstatePN` (both fragments run over `LstateN`), reused here. -/
abbrev LstatePNL := LstatePN

/-- A typed singleton program: the one function `fn` with the typed body `body : List
    LinstrRT`. The typed analogue of `singletonProg` (whose body is `List LinstrR`); the
    program-indexed leaf `findInstr` indexes a `List LinstrRT`, so the body is typed. -/
structure LprogT where
  /-- The sole function's name. -/
  lfn : String
  /-- The sole function's typed body. -/
  body : List LinstrRT

/-- `find_instr` over the typed program: the typed instruction at `lpc` in the current
    function's body (`LinstrRT`), or `none` (halted / out of range / wrong function). -/
def findInstrLeaf (P : LprogT) (s : LstatePNL) : Option LinstrRT :=
  if s.lfn = P.lfn then P.body[s.base.lpc]? else none

/-- `eval_instr` over the typed leaf state: the straight-line typed instruction delegates
    to `lsemStepLeaf leaf` on the base, carrying `lfn`. The typed body a straight-line
    kernel emits has no control-transfer instruction, so this is total over the emitted
    body (every leaf step is straight-line). -/
def evalInstrPNLeaf (leaf : LeafEnvN) (i : LinstrRT) (s : LstatePNL) : Option LstatePNL :=
  (lsemStepLeaf leaf i s.base).map (fun b => { s with base := b })

/-- `step`: fetch and evaluate. -/
def lsemStepPNLeaf (leaf : LeafEnvN) (P : LprogT) (s : LstatePNL) : Option LstatePNL :=
  match findInstrLeaf P s with
  | some i => evalInstrPNLeaf leaf i s
  | none => none

/-- `lsemFuel` over the typed leaf state: iterate `lsemStepPNLeaf`, halting (returning the
    state) when `findInstrLeaf` is `none` (lpc past the body end — `lsem_final`). -/
def lsemFuelLeaf (leaf : LeafEnvN) (P : LprogT) : Nat → LstatePNL → Option LstatePNL
  | 0, s => match findInstrLeaf P s with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrLeaf P s with
      | none => some s
      | some i =>
          match evalInstrPNLeaf leaf i s with
          | some s' => lsemFuelLeaf leaf P fuel s'
          | none => none

/-- A halted state (`findInstrLeaf = none`) takes no step: `lsemFuelLeaf` returns it
    unchanged at every fuel (`lsem_final_nostep`). -/
theorem lsemFuelLeaf_halt (leaf : LeafEnvN) (P : LprogT) (fuel : Nat) (s : LstatePNL)
    (h : findInstrLeaf P s = none) : lsemFuelLeaf leaf P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelLeaf, h]
  | succ n => simp [lsemFuelLeaf, h]

/-- **Determinism**: same fuel ⇒ same result (`lsemFuelLeaf` is a function). -/
theorem lsemFuelLeaf_deterministic (leaf : LeafEnvN) (P : LprogT) (fuel : Nat)
    (s t1 t2 : LstatePNL)
    (h1 : lsemFuelLeaf leaf P fuel s = some t1) (h2 : lsemFuelLeaf leaf P fuel s = some t2) :
    t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## The straight-line bridge: `lsemFuelLeaf` over a body = `lsemStraightLeaf` -/

/-- The typed singleton program with function `fn` and body `body`. -/
def singletonProgT (fn : String) (body : List LinstrRT) : LprogT := ⟨fn, body⟩

/-- `findInstrLeaf` on a singleton typed program reads the `pc`-th element of `body`. -/
theorem findInstrLeaf_singleton (fn : String) (body : List LinstrRT) (s : LstatePNL)
    (hfn : s.lfn = fn) :
    findInstrLeaf (singletonProgT fn body) s = body[s.base.lpc]? := by
  simp [findInstrLeaf, singletonProgT, hfn]

/-- `findInstrLeaf` past the end of a singleton body is `none` (halted). -/
theorem findInstrLeaf_singleton_halt (fn : String) (body : List LinstrRT) (s : LstatePNL)
    (hfn : s.lfn = fn) (hpc : body.length ≤ s.base.lpc) :
    findInstrLeaf (singletonProgT fn body) s = none := by
  rw [findInstrLeaf_singleton fn body s hfn]; exact List.getElem?_eq_none hpc

/-- **Straight-line consistency (suffix form), opaque-leaf.** Running a `suffix` of a
    singleton typed program's `body` via `lsemFuelLeaf` (from the program position
    `body.length - suffix.length`, with `suffix.length` fuel) agrees with the typed
    body-fold `lsemStraightLeaf leaf` over that suffix on the base state. The `lpc`-lockstep
    invariant: the program's `lpc` equals the already-executed prefix length, so
    `findInstrLeaf` fetches the next suffix instruction, and `evalInstrPNLeaf` reduces to
    `lsemStepLeaf leaf` (advancing the pc by one via `lsemStepLeaf_lpc_succ`). -/
theorem lsemFuelLeaf_straightline_suffix (leaf : LeafEnvN) (fn : String)
    (pre suffix : List LinstrRT) :
    ∀ (s : LstatePNL), s.lfn = fn → s.base.lpc = pre.length →
      lsemFuelLeaf leaf (singletonProgT fn (pre ++ suffix)) suffix.length s
        = (lsemStraightLeaf leaf suffix s.base).map (fun b => { s with base := b }) := by
  induction suffix generalizing pre with
  | nil =>
      intro s hfn hpc
      simp only [List.length_nil, lsemFuelLeaf, lsemStraightLeaf_nil, Option.map_some]
      have hhalt : findInstrLeaf (singletonProgT fn (pre ++ [])) s = none := by
        apply findInstrLeaf_singleton_halt fn (pre ++ []) s hfn; simp [hpc]
      rw [hhalt]
  | cons i is ih =>
      intro s hfn hpc
      have hfetch : findInstrLeaf (singletonProgT fn (pre ++ i :: is)) s = some i := by
        rw [findInstrLeaf_singleton fn (pre ++ i :: is) s hfn, hpc]; simp
      rw [List.length_cons, lsemFuelLeaf, hfetch]
      simp only [evalInstrPNLeaf]
      cases hstep : lsemStepLeaf leaf i s.base with
      | none => simp only [Option.map_none]; rw [lsemStraightLeaf_cons, hstep]; rfl
      | some b =>
          simp only [Option.map_some]
          rw [lsemStraightLeaf_cons, hstep]
          have hb_lpc : b.lpc = (pre ++ [i]).length := by
            rw [lsemStepLeaf_lpc_succ leaf i s.base b hstep, hpc]; simp
          have htail :
              lsemFuelLeaf leaf (singletonProgT fn ((pre ++ [i]) ++ is)) is.length
                  { s with base := b }
                = (lsemStraightLeaf leaf is b).map (fun b' => { s with base := b' }) := by
            have := ih (pre ++ [i]) { s with base := b } hfn hb_lpc
            simpa using this
          rw [show pre ++ i :: is = (pre ++ [i]) ++ is by simp] at *
          rw [htail]

/-- **Straight-line bridge (opaque-leaf).** For the typed `body`, the program-level
    `lsemFuelLeaf` over the singleton typed program with that body, run from `lpc = 0` with
    `body.length` fuel, agrees with the typed body-fold `lsemStraightLeaf leaf`. The leaf
    analogue of `JasminLsemLabeledMC.lsemFuelMC_straightline`: every opaque-leaf-fragment
    simulation over `lsemStraightLeaf` lifts to the program-indexed `lsem`. (No
    `IsStraightLine` side-condition: the leaf step has no control-transfer arm — every
    typed instruction either is the `extCall` leaf or delegates to a straight-line
    `lsemStepCast`.) -/
theorem lsemFuelLeaf_straightline (leaf : LeafEnvN) (fn : String) (body : List LinstrRT)
    (s : LstatePNL) (hfn : s.lfn = fn) (hpc : s.base.lpc = 0) :
    lsemFuelLeaf leaf (singletonProgT fn body) body.length s
      = (lsemStraightLeaf leaf body s.base).map (fun b => { s with base := b }) := by
  have := lsemFuelLeaf_straightline_suffix leaf fn [] body s hfn (by simpa using hpc)
  simpa using this

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf
