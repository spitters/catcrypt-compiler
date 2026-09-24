/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

@[expose] public section

set_option autoImplicit false

/-!
# The labeled, program-indexed `lsem` for the stack-memory fragment

`JasminLsemMem` brought the `stackLoad`/`stackStore` memory ops — the aliasing
array carrier, an orthogonal state axis — into the **body-fold** simulation
`lsemStraightMem` over the bundled state `LstateM` (register file + array
carrier), with the full faithfulness `comToLprog_faithful_mem` and the
unconditional `correct ∧ robust` capstone `owned_lsem_correct_and_robust_mem`.
That fragment covers a *runtime-indexed* (SIB) load/store: the index is read
from a register and used as `stackGet arr idx.toNat` / `stackSet arr idx.toNat v`,
so the aliasing core — `stackStore n i v` then `stackLoad n i` reads back `v`,
and distinct offsets don't interfere — is exactly `LstateM.getArr_setArr_same`
and `LstateM.getArr_setArr_other`, both proved in `JasminLsemMem`.

This file **lifts that fragment into the program-indexed, labeled `lsem`** — the
semantics the control-flow increments live in, and the shape every other
fragment's export gate is stated over (`ComLsemExportFaithful` /
`ComLsemExportFaithfulMC` / `ComLsemExportFaithfulLeaf`). The construction is the
typed-program labeled layer of `JasminLsemLabeledLeaf` / `JasminLsemLabeledCallN`
ported to the bundled state `LstateM`:

* `LstatePM` — the bundled state `LstateM` + the current function name `lfn`.
* `LprogM` / `singletonProgM` — a typed singleton program whose body is the
  typed `List LinstrRM` (`straightOpsMem`'s output): the wire `LinstrR`
  byte-for-byte (`straightOpsMem_wire`), paired with the array-shape `MemTag`
  jasmin's `read_linear` reconstructs from the `sarr len` descriptor.
* `findInstrMem` / `evalInstrPMem` / `lsemFuelMem` — fetch / step / fuel-bounded
  iteration, delegating each step to `lsemStepMem` on the bundled base.
* `lsemFuelMem_straightline` — the straight-line bridge: a memory-fragment body
  run by `lsemFuelMem` agrees with the body-fold `lsemStraightMem`. (No
  `IsStraightLine` side-condition: the memory step has no control-transfer arm —
  every typed instruction is a `LOADIDX`/`STOREIDX` or delegates to a
  straight-line `lsemStepCast`.)

`ComLsemExportFaithfulMem` is then the memory-fragment export-faithfulness
predicate, in the same labeled `lsem` shape as the other fragments, and
`comLsemExportFaithfulMem_of_mem` discharges it for **every** `Com` in the
`ScalarMemN` fragment (`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪
addCarryLo ∪ addCarryHi ∪ castW ∪ stackLoad ∪ stackStore`) — assembled from
`comToLprog_lsemMem` + the bridge.

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound}.** The `lsem→bytes`
encoder and Sail tables remain the declared trusted base, as for every verified
compiler.
-/

/-! ## 1. The program counter on the bundled state -/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN

/-- The program counter of the bundled state lives on the register half. -/
def LstateM.lpc (s : LstateM) : Nat := s.reg.lpc

@[simp] theorem LstateM.lpc_nextPc (s : LstateM) : s.nextPc.lpc = s.lpc + 1 := by
  simp [LstateM.lpc, LstateM.nextPc]

@[simp] theorem LstateM.lpc_setReg (s : LstateM) (r : String) {w : Nat} (v : BitVec w) :
    (s.setReg r v).lpc = s.lpc := by
  simp [LstateM.lpc]

@[simp] theorem LstateM.lpc_setArr (s : LstateM) (r : String) {w n : Nat}
    (arr : Fin n → BitVec w) : (s.setArr r arr).lpc = s.lpc := by
  simp [LstateM.lpc]

/-- A compile-time-offset word store (`storeMemC`) touches only `lmem`, so the pc
    (which lives on the register half) is unchanged. The `lpc`-preservation lemma
    for the third memory axis, alongside the register/array ones above. -/
@[simp] theorem LstateM.lpc_storeMemC (s : LstateM) (base : String) (off : Int)
    (v : BitVec 64) : (s.storeMemC base off v).lpc = s.lpc := by
  simp [LstateM.lpc, LstateM.reg_storeMemC]

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeledLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

/-- **Every successful bundled stack-memory step advances the pc by one.** A
    `LOADIDX` arm writes the loaded value and `.nextPc`s (the array carrier
    unchanged); a `STOREIDX` arm writes the new array to the carrier slot and
    `.nextPc`s (the register half unchanged); every register-delegated arm runs
    `lsemStepCast` over the register half (`lsemStepCast_lpc_succ`), the array
    carrier untouched. -/
theorem lsemStepMem_lpc_succ (i : LinstrRM) (s s' : LstateM)
    (h : lsemStepMem i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold lsemStepMem at h
  repeat' split at h
  all_goals
    first
      | (obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
         exact lsemStepCast_lpc_succ _ _ _ hr)
      | (obtain rfl := Option.some.inj h; simp)
      | simp at h

/-! ## 2. The typed program and the program-indexed bundled state -/

/-- The program-indexed bundled state: the stack-memory bundled state `LstateM`
    plus the current function name `lfn`. The `LstateM` analogue of
    `LstatePN`/`LstatePNL`. -/
structure LstatePM where
  /-- The bundled stack-memory base (register file + array carrier + pc). -/
  base : LstateM
  /-- The current function name. -/
  lfn : String

/-- A typed singleton program: the one function `fn` with the typed body
    `body : List LinstrRM`. The bundled-state analogue of `singletonProgT`. -/
structure LprogM where
  /-- The sole function's name. -/
  lfn : String
  /-- The sole function's typed body. -/
  body : List LinstrRM

/-- `find_instr` over the typed program: the typed instruction at `lpc` in the
    current function's body (`LinstrRM`), or `none` (halted / out of range /
    wrong function). -/
def findInstrMem (P : LprogM) (s : LstatePM) : Option LinstrRM :=
  if s.lfn = P.lfn then P.body[s.base.lpc]? else none

/-- `eval_instr` over the typed bundled state: the typed instruction delegates to
    `lsemStepMem` on the base, carrying `lfn`. The typed body a straight-line
    kernel emits has no control-transfer instruction, so this is total over the
    emitted body. -/
def evalInstrPMem (i : LinstrRM) (s : LstatePM) : Option LstatePM :=
  (lsemStepMem i s.base).map (fun b => { s with base := b })

/-- `step`: fetch and evaluate. -/
def lsemStepPMem (P : LprogM) (s : LstatePM) : Option LstatePM :=
  match findInstrMem P s with
  | some i => evalInstrPMem i s
  | none => none

/-- `lsemFuel` over the typed bundled state: iterate `lsemStepPMem`, halting
    (returning the state) when `findInstrMem` is `none` (lpc past the body end —
    `lsem_final`). -/
def lsemFuelMem (P : LprogM) : Nat → LstatePM → Option LstatePM
  | 0, s => match findInstrMem P s with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s with
      | none => some s
      | some i =>
          match evalInstrPMem i s with
          | some s' => lsemFuelMem P fuel s'
          | none => none

/-- A halted state (`findInstrMem = none`) takes no step: `lsemFuelMem` returns
    it unchanged at every fuel (`lsem_final_nostep`). -/
theorem lsemFuelMem_halt (P : LprogM) (fuel : Nat) (s : LstatePM)
    (h : findInstrMem P s = none) : lsemFuelMem P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelMem, h]
  | succ n => simp [lsemFuelMem, h]

/-- **Determinism**: same fuel ⇒ same result (`lsemFuelMem` is a function). -/
theorem lsemFuelMem_deterministic (P : LprogM) (fuel : Nat) (s t1 t2 : LstatePM)
    (h1 : lsemFuelMem P fuel s = some t1) (h2 : lsemFuelMem P fuel s = some t2) :
    t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## 3. The straight-line bridge: `lsemFuelMem` over a body = `lsemStraightMem` -/

/-- The typed singleton program with function `fn` and typed body `body`. -/
def singletonProgM (fn : String) (body : List LinstrRM) : LprogM := ⟨fn, body⟩

/-- `findInstrMem` on a singleton typed program reads the `pc`-th element of
    `body`. -/
theorem findInstrMem_singleton (fn : String) (body : List LinstrRM) (s : LstatePM)
    (hfn : s.lfn = fn) :
    findInstrMem (singletonProgM fn body) s = body[s.base.lpc]? := by
  simp [findInstrMem, singletonProgM, hfn]

/-- `findInstrMem` past the end of a singleton body is `none` (halted). -/
theorem findInstrMem_singleton_halt (fn : String) (body : List LinstrRM) (s : LstatePM)
    (hfn : s.lfn = fn) (hpc : body.length ≤ s.base.lpc) :
    findInstrMem (singletonProgM fn body) s = none := by
  rw [findInstrMem_singleton fn body s hfn]; exact List.getElem?_eq_none hpc

/-- **Straight-line consistency (suffix form), stack-memory.** Running a `suffix`
    of a singleton typed program's `body` via `lsemFuelMem` (from the program
    position `body.length - suffix.length`, with `suffix.length` fuel) agrees with
    the typed body-fold `lsemStraightMem` over that suffix on the bundled base.
    The `lpc`-lockstep invariant: the program's `lpc` equals the already-executed
    prefix length, so `findInstrMem` fetches the next suffix instruction, and
    `evalInstrPMem` reduces to `lsemStepMem` (advancing the pc by one via
    `lsemStepMem_lpc_succ`). -/
theorem lsemFuelMem_straightline_suffix (fn : String) (pre suffix : List LinstrRM) :
    ∀ (s : LstatePM), s.lfn = fn → s.base.lpc = pre.length →
      lsemFuelMem (singletonProgM fn (pre ++ suffix)) suffix.length s
        = (lsemStraightMem suffix s.base).map (fun b => { s with base := b }) := by
  induction suffix generalizing pre with
  | nil =>
      intro s hfn hpc
      simp only [List.length_nil, lsemFuelMem, lsemStraightMem_nil, Option.map_some]
      have hhalt : findInstrMem (singletonProgM fn (pre ++ [])) s = none := by
        apply findInstrMem_singleton_halt fn (pre ++ []) s hfn; simp [hpc]
      rw [hhalt]
  | cons i is ih =>
      intro s hfn hpc
      have hfetch : findInstrMem (singletonProgM fn (pre ++ i :: is)) s = some i := by
        rw [findInstrMem_singleton fn (pre ++ i :: is) s hfn, hpc]; simp
      rw [List.length_cons, lsemFuelMem, hfetch]
      simp only [evalInstrPMem]
      cases hstep : lsemStepMem i s.base with
      | none => simp only [Option.map_none]; rw [lsemStraightMem_cons, hstep]; rfl
      | some b =>
          simp only [Option.map_some]
          rw [lsemStraightMem_cons, hstep]
          have hb_lpc : b.lpc = (pre ++ [i]).length := by
            rw [lsemStepMem_lpc_succ i s.base b hstep, hpc]; simp
          have htail :
              lsemFuelMem (singletonProgM fn ((pre ++ [i]) ++ is)) is.length
                  { s with base := b }
                = (lsemStraightMem is b).map (fun b' => { s with base := b' }) := by
            have := ih (pre ++ [i]) { s with base := b } hfn hb_lpc
            simpa using this
          rw [show pre ++ i :: is = (pre ++ [i]) ++ is by simp] at *
          rw [htail]

/-- **Straight-line bridge (stack-memory).** For the typed `body`, the
    program-level `lsemFuelMem` over the singleton typed program with that body,
    run from `lpc = 0` with `body.length` fuel, agrees with the typed body-fold
    `lsemStraightMem`. The stack-memory analogue of
    `JasminLsemLabeledLeaf.lsemFuelLeaf_straightline`: the memory-fragment
    simulation over `lsemStraightMem` lifts to the program-indexed `lsem`. (No
    `IsStraightLine` side-condition: the memory step has no control-transfer arm —
    every typed instruction is a `LOADIDX`/`STOREIDX` head or delegates to a
    straight-line `lsemStepCast`.) -/
theorem lsemFuelMem_straightline (fn : String) (body : List LinstrRM)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 0) :
    lsemFuelMem (singletonProgM fn body) body.length s
      = (lsemStraightMem body s.base).map (fun b => { s with base := b }) := by
  have := lsemFuelMem_straightline_suffix fn [] body s hfn (by simpa using hpc)
  simpa using this

/-! ## 4. The encoded bundled state starts at pc 0 -/

/-- The encoded bundled state starts at program counter `0`: its register half is
    `encodeN V`, which starts at `0` (`encodeN_lpc`), and the array encoder leaves
    the register half untouched (`encodeArrAuxM_reg`). -/
theorem encodeM_lpc {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    (encodeM V).lpc = 0 := by
  show (encodeM V).reg.lpc = 0
  rw [show (encodeM V).reg = encodeN V from encodeArrAuxM_reg V _]
  exact encodeN_lpc V

/-! ## 5. The stack-memory export-faithfulness predicate and its discharge -/

/-- **General-`Com` `lsem` export faithfulness, stack-memory fragment.** Over the
    labeled program-indexed `lsem` on the bundled state `LstateM`: the emitted
    singleton typed program drives the encoded inputs to a state whose result
    register decodes to `Com.denote`. The memory-fragment analogue of
    `ComLsemExportFaithful` / `ComLsemExportFaithfulMC` / `ComLsemExportFaithfulLeaf`.
    The aliasing memory mutation is carried by the bundled state's array carrier:
    a `stackStore` writes the new array via `LstateM.setArr`, a subsequent
    `stackLoad` reads it back via `LstateM.getArr` — the aliasing core proved in
    `JasminLsemMem` and threaded through the body-fold faithfulness
    `comToLprog_lsemMem`. -/
def ComLsemExportFaithfulMem {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fn : String) {w : Nat} (hw : t = .reg w) : Prop :=
  ∀ V : Ctxt.Valuation Γ, ∃ st' : LstateM,
    lsemFuelMem (singletonProgM fn (straightOpsMem Γ.length com Γ.length))
        (straightOpsMem Γ.length com Γ.length).length
        { base := encodeM V, lfn := fn }
      = some { base := st', lfn := fn }
    ∧ decodeM st' (comRetReg Γ.length argName com Γ.length) w
        = some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧)

/-- **The export gate is discharged for the stack-memory fragment.**
    Any `Com` over `{regArith, select, regConst, immediate shifts, mulhi,
    addCarryLo/Hi, castW, stackLoad, stackStore}` (`ScalarMemN`) satisfies
    `ComLsemExportFaithfulMem` — the real, non-`True` content of the
    export-faithfulness gate, assembled from the body-fold faithfulness
    `comToLprog_lsemMem` (which carries the runtime-indexed load/store aliasing)
    and the straight-line bridge `lsemFuelMem_straightline`. This is the first
    export-faithfulness result covering the **aliasing memory** ops. -/
theorem comLsemExportFaithfulMem_of_mem {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulMem com fn hw := by
  intro V
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemMem hcom hw V
  refine ⟨st', ?_, hdec⟩
  rw [lsemFuelMem_straightline fn (straightOpsMem Γ.length com Γ.length)
    { base := encodeM V, lfn := fn } rfl (encodeM_lpc V), hrun]
  simp

/-- **Stack-memory export faithfulness specialises to the width-cast fragment.**
    Every `ScalarCastN` program (`JasminLsemCast`) is in `ScalarMemN`
    (`ScalarMemN.of_scalarCastN`), so the stack-memory export gate covers the whole
    register tower (`JasminLsemSimulation` through `JasminLsemCast`) as a special
    case. -/
theorem comLsemExportFaithfulMem_of_scalarCastN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCastN com) {w : Nat} (hw : t = .reg w)
    (fn : String) : ComLsemExportFaithfulMem com fn hw :=
  comLsemExportFaithfulMem_of_mem (ScalarMemN.of_scalarCastN hcom) hw fn

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMem
