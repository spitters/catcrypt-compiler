/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf

@[expose] public section

set_option autoImplicit false

/-!
# The labeled, program-indexed linear semantics over the typed `LinstrRS` IR (packed-lane SIMD)

`JasminLsemLabeledLeaf` ported jasmin's program-indexed `lsem` over the typed instruction
`LinstrRT := LinstrR × Option Nat` for the opaque-leaf fragment. The AVX-512 packed-lane
SIMD fragment (`JasminLsemSimd`) runs over the wider typed instruction `LinstrRS := LinstrR
× SimdDesc` (the `Option Nat` descriptor widened to also carry the SIMD lane op
`SimdDesc.vpack bop`), with the per-step semantics `lsemStepSimd`, parametric over an opaque
leaf environment `leaf : LeafEnvN`. The program-indexed *state* `LstatePNL` (the width-tagged
`LstateN` + the current function name `lfn`) is independent of the typed instruction type, so
it is reused from `JasminLsemLabeledLeaf`; the typed singleton program `LprogS` indexes a
`List LinstrRS` body.

The `vpackZMM` step's success arms end in a pc bump (`.nextPc`, exactly like the leaf step):
the `"VPACK8u64:bop"` head writes the packed-lane result and `.nextPc`s, and every other
instruction delegates to `lsemStepLeaf` over the projected descriptor (`lsemStepLeaf_lpc_succ`).
This is the SIMD counterpart of the labeled layer: the straight-line bridge
`lsemFuelSimd_straightline` lifts the SIMD-fragment body-fold `lsemStraightSimd` into the
program-indexed `lsem`, the analogue of `JasminLsemLabeledLeaf.lsemFuelLeaf_straightline`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledSimd

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledMC
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf

/-! ## The `lpc`-advancement chain: every successful typed SIMD step advances the pc -/

/-- **Every successful typed packed-lane SIMD step advances the pc by one.** The
    `"VPACK8u64:bop"` arm writes the packed-lane result and `.nextPc`s; every other typed
    instruction delegates to `lsemStepLeaf` over the projected descriptor
    (`lsemStepLeaf_lpc_succ`). -/
theorem lsemStepSimd_lpc_succ (leaf : LeafEnvN) (i : LinstrRS) (s s' : LstateN)
    (h : lsemStepSimd leaf i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold lsemStepSimd at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; simp [LstateN.lpc_nextPc, LstateN.lpc_setReg])
      | exact absurd h (by simp)
      | exact lsemStepLeaf_lpc_succ leaf _ s s' h

/-! ## The typed SIMD program and the program-indexed SIMD state

The program-indexed state `LstatePNL` (the width-tagged `LstateN` + `lfn`) is reused from
`JasminLsemLabeledLeaf`; only the typed singleton program indexes a `List LinstrRS` body. -/

/-- A typed singleton program for the SIMD fragment: the one function `fn` with the typed
    body `body : List LinstrRS`. The SIMD analogue of `LprogT` (whose body is
    `List LinstrRT`); the program-indexed SIMD `findInstr` indexes a `List LinstrRS`. -/
structure LprogS where
  /-- The sole function's name. -/
  lfn : String
  /-- The sole function's typed SIMD body. -/
  body : List LinstrRS

/-- `find_instr` over the typed SIMD program: the typed instruction at `lpc` in the current
    function's body (`LinstrRS`), or `none` (halted / out of range / wrong function). -/
def findInstrSimd (P : LprogS) (s : LstatePNL) : Option LinstrRS :=
  if s.lfn = P.lfn then P.body[s.base.lpc]? else none

/-- `eval_instr` over the typed SIMD state: the typed instruction delegates to
    `lsemStepSimd leaf` on the base, carrying `lfn`. -/
def evalInstrPNSimd (leaf : LeafEnvN) (i : LinstrRS) (s : LstatePNL) : Option LstatePNL :=
  (lsemStepSimd leaf i s.base).map (fun b => { s with base := b })

/-- `step`: fetch and evaluate. -/
def lsemStepPNSimd (leaf : LeafEnvN) (P : LprogS) (s : LstatePNL) : Option LstatePNL :=
  match findInstrSimd P s with
  | some i => evalInstrPNSimd leaf i s
  | none => none

/-- `lsemFuel` over the typed SIMD state: iterate `lsemStepPNSimd`, halting (returning the
    state) when `findInstrSimd` is `none` (lpc past the body end — `lsem_final`). -/
def lsemFuelSimd (leaf : LeafEnvN) (P : LprogS) : Nat → LstatePNL → Option LstatePNL
  | 0, s => match findInstrSimd P s with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrSimd P s with
      | none => some s
      | some i =>
          match evalInstrPNSimd leaf i s with
          | some s' => lsemFuelSimd leaf P fuel s'
          | none => none

/-- A halted state (`findInstrSimd = none`) takes no step: `lsemFuelSimd` returns it
    unchanged at every fuel (`lsem_final_nostep`). -/
theorem lsemFuelSimd_halt (leaf : LeafEnvN) (P : LprogS) (fuel : Nat) (s : LstatePNL)
    (h : findInstrSimd P s = none) : lsemFuelSimd leaf P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelSimd, h]
  | succ n => simp [lsemFuelSimd, h]

/-- **Determinism**: same fuel ⇒ same result (`lsemFuelSimd` is a function). -/
theorem lsemFuelSimd_deterministic (leaf : LeafEnvN) (P : LprogS) (fuel : Nat)
    (s t1 t2 : LstatePNL)
    (h1 : lsemFuelSimd leaf P fuel s = some t1) (h2 : lsemFuelSimd leaf P fuel s = some t2) :
    t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## The straight-line bridge: `lsemFuelSimd` over a body = `lsemStraightSimd` -/

/-- The typed singleton SIMD program with function `fn` and body `body`. -/
def singletonProgS (fn : String) (body : List LinstrRS) : LprogS := ⟨fn, body⟩

/-- `findInstrSimd` on a singleton typed SIMD program reads the `pc`-th element of `body`. -/
theorem findInstrSimd_singleton (fn : String) (body : List LinstrRS) (s : LstatePNL)
    (hfn : s.lfn = fn) :
    findInstrSimd (singletonProgS fn body) s = body[s.base.lpc]? := by
  simp [findInstrSimd, singletonProgS, hfn]

/-- `findInstrSimd` past the end of a singleton body is `none` (halted). -/
theorem findInstrSimd_singleton_halt (fn : String) (body : List LinstrRS) (s : LstatePNL)
    (hfn : s.lfn = fn) (hpc : body.length ≤ s.base.lpc) :
    findInstrSimd (singletonProgS fn body) s = none := by
  rw [findInstrSimd_singleton fn body s hfn]; exact List.getElem?_eq_none hpc

/-- **Straight-line consistency (suffix form), packed-lane SIMD.** Running a `suffix` of a
    singleton typed SIMD program's `body` via `lsemFuelSimd` (from the program position
    `body.length - suffix.length`, with `suffix.length` fuel) agrees with the typed
    body-fold `lsemStraightSimd leaf` over that suffix on the base state. The `lpc`-lockstep
    invariant: the program's `lpc` equals the already-executed prefix length, so
    `findInstrSimd` fetches the next suffix instruction, and `evalInstrPNSimd` reduces to
    `lsemStepSimd leaf` (advancing the pc by one via `lsemStepSimd_lpc_succ`). -/
theorem lsemFuelSimd_straightline_suffix (leaf : LeafEnvN) (fn : String)
    (pre suffix : List LinstrRS) :
    ∀ (s : LstatePNL), s.lfn = fn → s.base.lpc = pre.length →
      lsemFuelSimd leaf (singletonProgS fn (pre ++ suffix)) suffix.length s
        = (lsemStraightSimd leaf suffix s.base).map (fun b => { s with base := b }) := by
  induction suffix generalizing pre with
  | nil =>
      intro s hfn hpc
      simp only [List.length_nil, lsemFuelSimd, lsemStraightSimd_nil, Option.map_some]
      have hhalt : findInstrSimd (singletonProgS fn (pre ++ [])) s = none := by
        apply findInstrSimd_singleton_halt fn (pre ++ []) s hfn; simp [hpc]
      rw [hhalt]
  | cons i is ih =>
      intro s hfn hpc
      have hfetch : findInstrSimd (singletonProgS fn (pre ++ i :: is)) s = some i := by
        rw [findInstrSimd_singleton fn (pre ++ i :: is) s hfn, hpc]; simp
      rw [List.length_cons, lsemFuelSimd, hfetch]
      simp only [evalInstrPNSimd]
      cases hstep : lsemStepSimd leaf i s.base with
      | none => simp only [Option.map_none]; rw [lsemStraightSimd_cons, hstep]; rfl
      | some b =>
          simp only [Option.map_some]
          rw [lsemStraightSimd_cons, hstep]
          have hb_lpc : b.lpc = (pre ++ [i]).length := by
            rw [lsemStepSimd_lpc_succ leaf i s.base b hstep, hpc]; simp
          have htail :
              lsemFuelSimd leaf (singletonProgS fn ((pre ++ [i]) ++ is)) is.length
                  { s with base := b }
                = (lsemStraightSimd leaf is b).map (fun b' => { s with base := b' }) := by
            have := ih (pre ++ [i]) { s with base := b } hfn hb_lpc
            simpa using this
          rw [show pre ++ i :: is = (pre ++ [i]) ++ is by simp] at *
          rw [htail]

/-- **Straight-line bridge (packed-lane SIMD).** For the typed `body`, the program-level
    `lsemFuelSimd` over the singleton typed SIMD program with that body, run from `lpc = 0`
    with `body.length` fuel, agrees with the typed body-fold `lsemStraightSimd leaf`. The
    SIMD analogue of `JasminLsemLabeledLeaf.lsemFuelLeaf_straightline`: every SIMD-fragment
    simulation over `lsemStraightSimd` lifts to the program-indexed `lsem`. (No
    `IsStraightLine` side-condition: the SIMD step has no control-transfer arm — every typed
    instruction either is the `"VPACK8u64:bop"` head or delegates to a straight-line
    `lsemStepLeaf`.) -/
theorem lsemFuelSimd_straightline (leaf : LeafEnvN) (fn : String) (body : List LinstrRS)
    (s : LstatePNL) (hfn : s.lfn = fn) (hpc : s.base.lpc = 0) :
    lsemFuelSimd leaf (singletonProgS fn body) body.length s
      = (lsemStraightSimd leaf body s.base).map (fun b => { s with base := b }) := by
  have := lsemFuelSimd_straightline_suffix leaf fn [] body s hfn (by simpa using hpc)
  simpa using this

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledSimd
