/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCallN
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf

set_option autoImplicit false

/-!
# The labeled, program-indexed linear semantics over the typed `LinstrRT` IR (multi-result call)

`JasminLsemLabeledLeaf` ported jasmin's program-indexed `lsem` over the typed instruction
`LinstrRT := LinstrR × Option Nat` for the opaque-leaf fragment, parametric over an opaque
leaf environment `leaf : LeafEnvN`. The multi-result-call fragment (`JasminLsemCallN`) runs
over the **same** typed instruction `LinstrRT` and the **same** width-tagged `LstateN`, only
replacing the per-step semantics `lsemStepLeaf` with `lsemStepCallN`, parametric over a
multi-result-call leaf environment `leaf : LeafEnvCN`. So the program-indexed machinery
(`LstatePNL`, the typed singleton program `LprogT`, `findInstrLeaf`, `singletonProgT`) is
reused unchanged from `JasminLsemLabeledLeaf`; only the program-indexed step / iteration
(`evalInstrPNCallN` / `lsemFuelCallN`) carry the `callN` step.

The `callN` step's success arms end in a pc bump (`.nextPc`, exactly like the leaf step):
the `"CALLN:name"` head writes the leaf result and `.nextPc`s, and every other instruction
delegates to `lsemStepLeaf` (`lsemStepLeaf_lpc_succ`). This is the multi-result-call
counterpart of the labeled layer: the straight-line bridge `lsemFuelCallN_straightline`
lifts the `callN`-fragment body-fold `lsemStraightCallN` into the program-indexed `lsem`,
the analogue of `JasminLsemLabeledLeaf.lsemFuelLeaf_straightline`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledCallN

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCallN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf

/-! ## The `lpc`-advancement chain: every successful typed `callN` step advances the pc -/

/-- **Every successful typed multi-result-call step advances the pc by one.** The
    `"CALLN:name"` arm writes the leaf result and `.nextPc`s; every other typed instruction
    delegates to `lsemStepLeaf` (`lsemStepLeaf_lpc_succ`). -/
theorem lsemStepCallN_lpc_succ (leaf : LeafEnvCN) (i : LinstrRT) (s s' : LstateN)
    (h : lsemStepCallN leaf i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold lsemStepCallN at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp [LstateN.lpc_nextPc, LstateN.lpc_setReg])
      | exact absurd h (by simp)
      | exact lsemStepLeaf_lpc_succ leaf _ s s' h

/-! ## The program-indexed `callN` state and iteration

The program-indexed state `LstatePNL`, the typed singleton program `LprogT`, the fetch
`findInstrLeaf`, and the constructor `singletonProgT` are reused verbatim from
`JasminLsemLabeledLeaf` (the `callN` fragment threads the same typed `LinstrRT`). Only the
program-indexed evaluation / iteration carry the `callN` step `lsemStepCallN`. -/

/-- `eval_instr` over the typed `callN` state: the typed instruction delegates to
    `lsemStepCallN leaf` on the base, carrying `lfn`. -/
def evalInstrPNCallN (leaf : LeafEnvCN) (i : LinstrRT) (s : LstatePNL) : Option LstatePNL :=
  (lsemStepCallN leaf i s.base).map (fun b => { s with base := b })

/-- `step`: fetch and evaluate. -/
def lsemStepPNCallN (leaf : LeafEnvCN) (P : LprogT) (s : LstatePNL) : Option LstatePNL :=
  match findInstrLeaf P s with
  | some i => evalInstrPNCallN leaf i s
  | none => none

/-- `lsemFuel` over the typed `callN` state: iterate `lsemStepPNCallN`, halting (returning
    the state) when `findInstrLeaf` is `none` (lpc past the body end — `lsem_final`). -/
def lsemFuelCallN (leaf : LeafEnvCN) (P : LprogT) : Nat → LstatePNL → Option LstatePNL
  | 0, s => match findInstrLeaf P s with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrLeaf P s with
      | none => some s
      | some i =>
          match evalInstrPNCallN leaf i s with
          | some s' => lsemFuelCallN leaf P fuel s'
          | none => none

/-- A halted state (`findInstrLeaf = none`) takes no step: `lsemFuelCallN` returns it
    unchanged at every fuel (`lsem_final_nostep`). -/
theorem lsemFuelCallN_halt (leaf : LeafEnvCN) (P : LprogT) (fuel : Nat) (s : LstatePNL)
    (h : findInstrLeaf P s = none) : lsemFuelCallN leaf P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelCallN, h]
  | succ n => simp [lsemFuelCallN, h]

/-- **Determinism**: same fuel ⇒ same result (`lsemFuelCallN` is a function). -/
theorem lsemFuelCallN_deterministic (leaf : LeafEnvCN) (P : LprogT) (fuel : Nat)
    (s t1 t2 : LstatePNL)
    (h1 : lsemFuelCallN leaf P fuel s = some t1) (h2 : lsemFuelCallN leaf P fuel s = some t2) :
    t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## The straight-line bridge: `lsemFuelCallN` over a body = `lsemStraightCallN` -/

/-- **Straight-line consistency (suffix form), multi-result-call.** Running a `suffix` of a
    singleton typed program's `body` via `lsemFuelCallN` (from the program position
    `body.length - suffix.length`, with `suffix.length` fuel) agrees with the typed
    body-fold `lsemStraightCallN leaf` over that suffix on the base state. The `lpc`-lockstep
    invariant: the program's `lpc` equals the already-executed prefix length, so
    `findInstrLeaf` fetches the next suffix instruction, and `evalInstrPNCallN` reduces to
    `lsemStepCallN leaf` (advancing the pc by one via `lsemStepCallN_lpc_succ`). -/
theorem lsemFuelCallN_straightline_suffix (leaf : LeafEnvCN) (fn : String)
    (pre suffix : List LinstrRT) :
    ∀ (s : LstatePNL), s.lfn = fn → s.base.lpc = pre.length →
      lsemFuelCallN leaf (singletonProgT fn (pre ++ suffix)) suffix.length s
        = (lsemStraightCallN leaf suffix s.base).map (fun b => { s with base := b }) := by
  induction suffix generalizing pre with
  | nil =>
      intro s hfn hpc
      simp only [List.length_nil, lsemFuelCallN, lsemStraightCallN_nil, Option.map_some]
      have hhalt : findInstrLeaf (singletonProgT fn (pre ++ [])) s = none := by
        apply findInstrLeaf_singleton_halt fn (pre ++ []) s hfn; simp [hpc]
      rw [hhalt]
  | cons i is ih =>
      intro s hfn hpc
      have hfetch : findInstrLeaf (singletonProgT fn (pre ++ i :: is)) s = some i := by
        rw [findInstrLeaf_singleton fn (pre ++ i :: is) s hfn, hpc]; simp
      rw [List.length_cons, lsemFuelCallN, hfetch]
      simp only [evalInstrPNCallN]
      cases hstep : lsemStepCallN leaf i s.base with
      | none => simp only [Option.map_none]; rw [lsemStraightCallN_cons, hstep]; rfl
      | some b =>
          simp only [Option.map_some]
          rw [lsemStraightCallN_cons, hstep]
          have hb_lpc : b.lpc = (pre ++ [i]).length := by
            rw [lsemStepCallN_lpc_succ leaf i s.base b hstep, hpc]; simp
          have htail :
              lsemFuelCallN leaf (singletonProgT fn ((pre ++ [i]) ++ is)) is.length
                  { s with base := b }
                = (lsemStraightCallN leaf is b).map (fun b' => { s with base := b' }) := by
            have := ih (pre ++ [i]) { s with base := b } hfn hb_lpc
            simpa using this
          rw [show pre ++ i :: is = (pre ++ [i]) ++ is by simp] at *
          rw [htail]

/-- **Straight-line bridge (multi-result-call).** For the typed `body`, the program-level
    `lsemFuelCallN` over the singleton typed program with that body, run from `lpc = 0` with
    `body.length` fuel, agrees with the typed body-fold `lsemStraightCallN leaf`. The
    multi-result-call analogue of `JasminLsemLabeledLeaf.lsemFuelLeaf_straightline`: every
    `callN`-fragment simulation over `lsemStraightCallN` lifts to the program-indexed `lsem`.
    (No `IsStraightLine` side-condition: the `callN` step has no control-transfer arm — every
    typed instruction either is the `"CALLN:name"` head or delegates to a straight-line
    `lsemStepLeaf`.) -/
theorem lsemFuelCallN_straightline (leaf : LeafEnvCN) (fn : String) (body : List LinstrRT)
    (s : LstatePNL) (hfn : s.lfn = fn) (hpc : s.base.lpc = 0) :
    lsemFuelCallN leaf (singletonProgT fn body) body.length s
      = (lsemStraightCallN leaf body s.base).map (fun b => { s with base := b }) := by
  have := lsemFuelCallN_straightline_suffix leaf fn [] body s hfn (by simpa using hpc)
  simpa using this

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledCallN
