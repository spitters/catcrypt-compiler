/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
public import HaxLean.RuntimeM

/-!
# A `RustM` state-monad reading of the linear memref language

The linear instruction language `LinstrRM` of the `Lprog` back end (typed `Lopn`, label,
jump and conditional instructions over a register file, stack arrays and word memory) has
the fuel-stepped interpreter `JasminLsemMemFlagGuard.lsemFuelMemF` over the flag-extended
state `LstateMF`. This module reads it into the state monad `StateT σ RustM`, whose
`Std.WP.WPMonad` instance is the toolchain's `StateT` lift of the `RustM` instance of
`HaxLean.RuntimeM`, so that the toolchain's `vcgen` (through `rust_vc`) proves triples
of instruction sequences.

A failed step (`none`) is the `RustM` panic `.fail .panic`; the reading never diverges.

* `ProgM`, `fetchM`, `stepPM`, `runM`: the reading of a whole program over `LstateMF`:
  fetch the instruction at the program counter, step it by `evalInstrPMemF`, and repeat
  for the fuel, with the recursion of `lsemFuelMemF`.
* `BodyM`, `stepM`, `bodyM`: the reading of a straight-line body over the base state
  `LstateM`, each instruction stepped by the flag machine's straight-line step `stepMemF`.

## Main results

* `runM_run`, `runM_ok_iff`, `runM_fail_iff`, `runM_ne_div`: the run of the program
  reading at fuel `f` is the run of `lsemFuelMemF` at fuel `f`; a value at a state is a
  run of the interpreter to that state, and conversely.
* `bodyM_run`, `bodyM_ok_iff`: the run of the body reading is the flag body-fold
  `lsemStraightMemF`.
* `lsemFuelMemF_of_bodyM`: a run of the body reading of a plain-`Lopn` segment of a
  program is a run of `lsemFuelMemF` across the segment.
* `run_of_triple`: a `Std.WP` triple with exception postcondition `⊥` over
  `StateT σ RustM` gives, at a state satisfying the precondition, a run to a value.
* `lsemFuelMemF_of_bodyM_triple`: a triple of the body reading of a program's whole
  plain-`Lopn` body is a run of `lsemFuelMemF` to a state satisfying the postcondition.
* `stepM_load_spec`, `stepM_store_spec`, `stepM_add_spec`: the `@[spec]` triples of the
  runtime-indexed array load `LOADIDX`, the array store `STOREIDX` (each with the index
  bound as a precondition) and the 64-bit addition `ADD:64`.
* `loadAddStore_spec`, `loadAddStore_lsemFuelMemF`: the triple of a load, an addition and a
  store, proved by `vcgen`, and its run under `lsemFuelMemF`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LcmdRustM

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (x86_ADD)
open Aeneas.Std (RustM Error)
open _root_.Std.WP Lean.Order

/-! ## 1. The program reading -/

/-- The reading monad of a program: the flag-extended state over `RustM`. -/
abbrev ProgM := StateT LstateMF RustM

/-- Fetch the instruction at the program counter, `none` when the run halts. -/
def fetchM (P : LprogM) : ProgM (Option LinstrRM) := fun s => .ok (findInstrMem P s.prog, s)

/-- One flag-machine step of the instruction `i`; a stuck step is a panic. -/
def stepPM (P : LprogM) (i : LinstrRM) : ProgM Unit := fun s =>
  RustM.ofOption ((evalInstrPMemF P i s).map (fun s' => ((), s'))) .panic

/-- The reading of a run of `P` with `fuel` steps: fetch, halt on `none`, step and repeat.
    Out of fuel at an instruction, the run panics. -/
def runM (P : LprogM) : Nat → ProgM Unit
  | 0 => do
      match ← fetchM P with
      | none => pure ()
      | some _ => StateT.lift (.fail .panic)
  | fuel + 1 => do
      match ← fetchM P with
      | none => pure ()
      | some i => do stepPM P i; runM P fuel

/-- **Adequacy of the program reading.** The run of `runM P fuel` from `s` is the run of
    `lsemFuelMemF P fuel` from `s`, a `none` read as the panic. -/
theorem runM_run (P : LprogM) (fuel : Nat) (s : LstateMF) :
    (runM P fuel).run s
      = RustM.ofOption ((lsemFuelMemF P fuel s).map (fun s' => ((), s'))) .panic := by
  induction fuel generalizing s with
  | zero =>
    simp only [runM, lsemFuelMemF, StateT.run_bind]
    rw [show (fetchM P).run s = .ok (findInstrMem P s.prog, s) from rfl]
    cases findInstrMem P s.prog <;> rfl
  | succ n ih =>
    simp only [runM, lsemFuelMemF, StateT.run_bind]
    rw [show (fetchM P).run s = .ok (findInstrMem P s.prog, s) from rfl]
    cases findInstrMem P s.prog with
    | none => rfl
    | some i =>
      change ((stepPM P i).run s >>= fun p => (runM P n).run p.2) = _
      rw [show (stepPM P i).run s
          = RustM.ofOption ((evalInstrPMemF P i s).map (fun s' => ((), s'))) .panic from rfl]
      cases h : evalInstrPMemF P i s with
      | none => simp only [h, Option.map_none]; rfl
      | some s' => simp only [h, Option.map_some]; exact ih s'

/-- A run of the program reading to a value at `s'` is a run of `lsemFuelMemF` to `s'`,
    and conversely. -/
theorem runM_ok_iff (P : LprogM) (fuel : Nat) (s s' : LstateMF) :
    (runM P fuel).run s = .ok ((), s') ↔ lsemFuelMemF P fuel s = some s' := by
  rw [runM_run]
  cases h : lsemFuelMemF P fuel s <;> simp

/-- The program reading panics exactly when `lsemFuelMemF` is stuck. -/
theorem runM_fail_iff (P : LprogM) (fuel : Nat) (s : LstateMF) :
    (runM P fuel).run s = .fail .panic ↔ lsemFuelMemF P fuel s = none := by
  rw [runM_run]
  cases h : lsemFuelMemF P fuel s <;> simp

/-- The program reading does not diverge. -/
theorem runM_ne_div (P : LprogM) (fuel : Nat) (s : LstateMF) :
    (runM P fuel).run s ≠ .div := by
  rw [runM_run]
  cases h : lsemFuelMemF P fuel s <;> simp

/-! ## 2. The straight-line body reading -/

/-- The reading monad of a straight-line body: the base state over `RustM`. -/
abbrev BodyM := StateT LstateM RustM

/-- One straight-line step `stepMemF` of the instruction `i`; a stuck step is a panic. -/
def stepM (i : LinstrRM) : BodyM Unit := fun s =>
  RustM.ofOption ((stepMemF i s).map (fun s' => ((), s'))) .panic

/-- Unfolding lemma of `stepM`. -/
theorem stepM_run (i : LinstrRM) (s : LstateM) :
    (stepM i).run s = RustM.ofOption ((stepMemF i s).map (fun s' => ((), s'))) .panic := rfl

/-- The reading of a straight-line body: its steps in order. -/
def bodyM : List LinstrRM → BodyM Unit
  | [] => pure ()
  | i :: is => do stepM i; bodyM is

/-- **Adequacy of the body reading.** The run of `bodyM body` is the flag body-fold
    `lsemStraightMemF body`, a `none` read as the panic. -/
theorem bodyM_run (body : List LinstrRM) (s : LstateM) :
    (bodyM body).run s
      = RustM.ofOption ((lsemStraightMemF body s).map (fun s' => ((), s'))) .panic := by
  induction body generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [bodyM, lsemStraightMemF_cons, StateT.run_bind]
    rw [show (stepM i).run s
        = RustM.ofOption ((stepMemF i s).map (fun s' => ((), s'))) .panic from rfl]
    cases stepMemF i s with
    | none => rfl
    | some s' => exact ih s'

/-- A run of the body reading to a value at `s'` is a run of the body-fold to `s'`, and
    conversely. -/
theorem bodyM_ok_iff (body : List LinstrRM) (s s' : LstateM) :
    (bodyM body).run s = .ok ((), s') ↔ lsemStraightMemF body s = some s' := by
  rw [bodyM_run]
  cases h : lsemStraightMemF body s <;> simp

/-- **The body reading runs the interpreter across a segment.** When the plain-`Lopn`
    segment `seg` sits in `P` at the program counter of `b0` and its reading runs from
    `b0` to `b1`, `lsemFuelMemF` runs across it from `b0` to `b1` with `zf` unchanged. -/
theorem lsemFuelMemF_of_bodyM (P : LprogM) (fn : String) (hfn : fn = P.lfn)
    (seg : List LinstrRM) (b0 b1 : LstateM) (zf : Bool) (f : Nat)
    (hplain : PlainLopnBody seg)
    (hpos : ∀ k, k < seg.length → P.body[b0.lpc + k]? = seg[k]?)
    (hrun : (bodyM seg).run b0 = .ok ((), b1)) :
    lsemFuelMemF P (seg.length + f) { prog := { base := b0, lfn := fn }, zf := zf }
      = lsemFuelMemF P f { prog := { base := b1, lfn := fn }, zf := zf } := by
  rw [lsemFuelMemF_seg P fn hfn seg b0 zf f hplain hpos, (bodyM_ok_iff seg b0 b1).1 hrun,
    Option.bind_some]

/-! ## 3. Triples over `StateT σ RustM` -/

/-- A `Std.WP` triple with exception postcondition `⊥` over `StateT σ RustM` gives, at
    every state satisfying the precondition, a run to a value and a state satisfying the
    postcondition. -/
theorem run_of_triple {σ α : Type} {x : StateT σ RustM α} {Pre : σ → Prop}
    {Q : α → σ → Prop} (h : Triple x Pre Q Lean.Order.bot) {s : σ} (hs : Pre s) :
    ∃ a s', x.run s = .ok (a, s') ∧ Q a s' := by
  have h' := h.le_wp s hs
  rw [StateT.wp_apply_eq] at h'
  cases hx : x.run s with
  | ok p => rw [hx] at h'; exact ⟨p.1, p.2, rfl, h'⟩
  | fail e => rw [hx] at h'; exact (Lean.Order.bot_le (fun _ : Error => False) e h').elim
  | div => rw [hx] at h'; exact h'.elim

/-- **A triple of the body reading is a run of the interpreter.** For the program whose
    whole body is the plain-`Lopn` list `body`, a triple of `bodyM body` gives, from a state
    at program counter `0` satisfying the precondition, a run of `lsemFuelMemF` at fuel
    `body.length` to a state satisfying the postcondition. -/
theorem lsemFuelMemF_of_bodyM_triple (fn : String) (body : List LinstrRM)
    {Pre : LstateM → Prop} {Q : Unit → LstateM → Prop}
    (h : Triple (bodyM body) Pre Q Lean.Order.bot) (hplain : PlainLopnBody body)
    (s : LstateM) (h0 : s.lpc = 0) (hs : Pre s) (zf : Bool) :
    ∃ s', lsemFuelMemF (singletonProgM fn body) body.length
        { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := s', lfn := fn }, zf := zf } ∧ Q () s' := by
  obtain ⟨_, s', hrun, hQ⟩ := run_of_triple h hs
  have hfold := (bodyM_ok_iff body s s').1 hrun
  have hlpc : s'.lpc = body.length := by
    rw [lsemStraightMemF_lpc body s s' hfold, h0, Nat.zero_add]
  refine ⟨s', ?_, hQ⟩
  have hseg := lsemFuelMemF_of_bodyM (singletonProgM fn body) fn rfl body s s' zf 0 hplain
    (fun k _ => by rw [h0, Nat.zero_add]; rfl) hrun
  rw [Nat.add_zero] at hseg
  rw [hseg]
  apply lsemFuelMemF_halt
  rw [findInstrMem_singleton fn body _ rfl]
  simp [hlpc]

/-! ## 4. Specifications of the memory operations and the arithmetic

Each triple is in weakest-precondition form: the precondition is the meet of the facts the
step reads and the postcondition at the state after the step, with the read values written
as `Option.getD`. `vcgen` splits the meet into a verification condition for the facts and
continues with the postcondition. -/

/-- The state `t` with the carry flag `c` and the overflow flag `o`. -/
def withFlags (t : LstateM) (c o : Bool) : LstateM := { t with cf := c, of := o }

/-- Unfolding lemma of `withFlags` at the register file. -/
@[simp] theorem withFlags_reg (t : LstateM) (c o : Bool) : (withFlags t c o).reg = t.reg := rfl

/-- Unfolding lemma of `withFlags` at the array carrier. -/
@[simp] theorem withFlags_getArr (t : LstateM) (c o : Bool) (r : String) (w n : Nat) :
    (withFlags t c o).getArr r w n = t.getArr r w n := rfl

/-- Unfolding lemma of `LstateM.nextPc` at the array carrier. -/
@[simp] theorem getArr_nextPc (t : LstateM) (r : String) (w n : Nat) :
    t.nextPc.getArr r w n = t.getArr r w n := rfl

/-- **The array load.** `LOADIDX dst ← base[idx]` at shape `(w, n)`: when `base` holds an
    array of shape `(w, n)` and the index register `idx` a 64-bit word below `n`, the step
    writes the array element to `dst` and advances the pc. -/
@[spec]
theorem stepM_load_spec (dst base idx : String) (sc w n : Nat)
    (post : Unit → LstateM → Prop) {epost : Error → Prop} :
    Triple (stepM (.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx sc], .load w n))
      (fun s : LstateM => Lean.Order.meet ((s.getArr base w n).isSome ∧
        (s.reg.getW idx 64).isSome ∧ ((s.reg.getW idx 64).getD 0).toNat < n)
        (post () ((s.setReg dst (stackGet ((s.getArr base w n).getD fun _ => 0)
          ((s.reg.getW idx 64).getD 0).toNat)).nextPc)))
      post epost := by
  refine ⟨fun s h => ?_⟩
  obtain ⟨⟨h1, h2, _⟩, hp⟩ := (meet_prop_eq_and _ _).mp h
  obtain ⟨arr, ha⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨vi, hi⟩ := Option.isSome_iff_exists.mp h2
  rw [ha, hi] at hp
  have hstep : stepMemF (.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx sc], .load w n) s
      = some ((s.setReg dst (stackGet arr vi.toNat)).nextPc) := by
    simp only [stepMemF, lsemStepMem, loadStruct?, ite_true, ha, hi, withALUFlags, aluFlagOp?]
  rw [StateT.wp_apply_eq, stepM_run, hstep]
  exact hp

/-- **The array store.** `STOREIDX dst ← base[idx] := val` at shape `(w, n)`: when `base`
    holds an array of shape `(w, n)`, the index register `idx` a 64-bit word below `n` and
    `val` a `w`-bit word, the step writes the updated array to `dst` and advances the pc. -/
@[spec]
theorem stepM_store_spec (dst base idx val : String) (sc w n : Nat)
    (post : Unit → LstateM → Prop) {epost : Error → Prop} :
    Triple (stepM (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx sc, .reg val], .store w n))
      (fun s : LstateM => Lean.Order.meet ((s.getArr base w n).isSome ∧
        (s.reg.getW idx 64).isSome ∧ (s.reg.getW val w).isSome ∧
        ((s.reg.getW idx 64).getD 0).toNat < n)
        (post () ((s.setArr dst (stackSet ((s.getArr base w n).getD fun _ => 0)
          ((s.reg.getW idx 64).getD 0).toNat ((s.reg.getW val w).getD 0))).nextPc)))
      post epost := by
  refine ⟨fun s h => ?_⟩
  obtain ⟨⟨h1, h2, h3, _⟩, hp⟩ := (meet_prop_eq_and _ _).mp h
  obtain ⟨arr, ha⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨vi, hi⟩ := Option.isSome_iff_exists.mp h2
  obtain ⟨vv, hv⟩ := Option.isSome_iff_exists.mp h3
  rw [ha, hi, hv] at hp
  have hflag : aluFlagOp?
      (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx sc, .reg val], .store w n) = none := by
    simp [aluFlagOp?, withWidthTag]
  have hstep : stepMemF (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx sc, .reg val],
      .store w n) s = some ((s.setArr dst (stackSet arr vi.toNat vv)).nextPc) := by
    simp only [stepMemF, lsemStepMem, storeStruct?, ite_true, ha, hi, hv,
      withALUFlags_of_none hflag]
  rw [StateT.wp_apply_eq, stepM_run, hstep]
  exact hp

/-- **The 64-bit addition.** `ADD:64 dst ← a, b` (the emitted mnemonic
    `withWidthTag 64 "ADD"`): when `a` and `b` hold 64-bit words, the step writes their sum
    to `dst`, the carry and overflow flags of the machine's `x86_ADD`, and advances the
    pc. -/
@[spec]
theorem stepM_add_spec (dst a b : String) (cd : Option Nat)
    (post : Unit → LstateM → Prop) {epost : Error → Prop} :
    Triple (stepM (.Lopn [.reg dst] "ADD:64" [.reg a, .reg b], .reg cd))
      (fun s : LstateM => Lean.Order.meet ((s.reg.getW a 64).isSome ∧ (s.reg.getW b 64).isSome)
        (post () (withFlags
          (s.setReg dst ((s.reg.getW a 64).getD 0 + (s.reg.getW b 64).getD 0)).nextPc
          ((x86_ADD ((s.reg.getW a 64).getD 0) ((s.reg.getW b 64).getD 0)).cf.getD false)
          ((x86_ADD ((s.reg.getW a 64).getD 0) ((s.reg.getW b 64).getD 0)).of.getD false))))
      post epost := by
  refine ⟨fun s h => ?_⟩
  obtain ⟨⟨h1, h2⟩, hp⟩ := (meet_prop_eq_and _ _).mp h
  obtain ⟨va, ha⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨vb, hb⟩ := Option.isSome_iff_exists.mp h2
  rw [ha, hb] at hp
  have hstrip : stripWidthTag "ADD:64" = "ADD" := by decide +kernel
  have hlow : lsemStepMem (.Lopn [.reg dst] "ADD:64" [.reg a, .reg b], .reg cd) s
      = some ((s.setReg dst (va + vb)).nextPc) := by
    rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inl ⟨rfl, rfl⟩),
      lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (by simp [sarStruct?])]
    simp only [lsemStepN, readReg_of_getW ha, evalOperandN, hb, hstrip, applyOpnN,
      Option.map_some]
    rfl
  have hflag : aluFlagOp? (.Lopn [.reg dst] "ADD:64" [.reg a, .reg b], .reg cd)
      = some (.add, .reg a, .reg b) := by
    simp [aluFlagOp?, withWidthTag]
  rw [StateT.wp_apply_eq, stepM_run, stepMemF_of_lsemStepMem hlow]
  simp only [withALUFlags, hflag, evalOperandN, ha, hb, Option.map_some]
  exact hp

/-! ## 5. A worked example: load, add, store

The body `x := a[i]; y := x + k; a[i] := y` over a stack array `a` of four 64-bit words. -/

/-- The straight-line body `LOADIDX x ← a[i]; ADD:64 y ← x, k; STOREIDX a ← a[i] := y`. -/
def loadAddStore : List LinstrRM :=
  [(.Lopn [.reg "x"] "LOADIDX" [.arrIdx "a" "i" 8], .load 64 4),
   (.Lopn [.reg "y"] "ADD:64" [.reg "x", .reg "k"], .reg none),
   (.Lopn [.reg "a"] "STOREIDX" [.arrIdx "a" "i" 8, .reg "y"], .store 64 4)]

/-- **The triple of the example body, proved by `vcgen`.** When `a` holds `arr`, `i` an
    index below `4` and `k` a word, the body leaves `a[i] + k` in `a[i]`. -/
theorem loadAddStore_spec (arr : Fin 4 → BitVec 64) (i k : BitVec 64) (hi : i.toNat < 4) :
    ⦃fun s => s.getArr "a" 64 4 = some arr ∧ s.reg.getW "i" 64 = some i ∧
        s.reg.getW "k" 64 = some k⦄
      bodyM loadAddStore
    ⦃fun _ s' => s'.getArr "a" 64 4
        = some (stackSet arr i.toNat (stackGet arr i.toNat + k))⦄ := by
  simp only [loadAddStore, bodyM]
  set_option experimental.vcgen true in vcgen
  all_goals
    rename_i h
    obtain ⟨ha, hi', hk⟩ := h
    simp [LstateN.getW_setReg_other, ha, hi', hk, hi]

/-- The example body is a plain-`Lopn` body. -/
theorem loadAddStore_plain : PlainLopnBody loadAddStore := by
  intro i hmem
  simp only [loadAddStore, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact ⟨⟨_, _, _, rfl⟩, by decide, by decide⟩
  · exact ⟨⟨_, _, _, rfl⟩, by decide, by decide⟩
  · exact ⟨⟨_, _, _, rfl⟩, by decide, by decide⟩

/-- **The example transferred to the interpreter.** From a state at program counter `0`
    satisfying the precondition, `lsemFuelMemF` runs the one-function program of the
    example body in three steps to a state whose array `a` holds `a[i] + k` at `i`. -/
theorem loadAddStore_lsemFuelMemF (fn : String) (arr : Fin 4 → BitVec 64) (i k : BitVec 64)
    (hi : i.toNat < 4) (s : LstateM) (h0 : s.lpc = 0) (ha : s.getArr "a" 64 4 = some arr)
    (hreg : s.reg.getW "i" 64 = some i) (hk : s.reg.getW "k" 64 = some k) (zf : Bool) :
    ∃ s', lsemFuelMemF (singletonProgM fn loadAddStore) 3
        { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := s', lfn := fn }, zf := zf } ∧
      s'.getArr "a" 64 4 = some (stackSet arr i.toNat (stackGet arr i.toNat + k)) :=
  lsemFuelMemF_of_bodyM_triple fn loadAddStore (loadAddStore_spec arr i k hi)
    loadAddStore_plain s h0 ⟨ha, hreg, hk⟩ zf

end CatCrypt.Crypto.SecureCompilation.VIR.LcmdRustM
