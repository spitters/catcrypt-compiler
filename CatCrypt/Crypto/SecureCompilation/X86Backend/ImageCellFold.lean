/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi

@[expose] public section

set_option autoImplicit false

/-!
# Constant-index array accesses folded into cell names

The owned back end prints a load or store of a word array at a constant index `k` as a
copy between a register and the register-shaped cell name `memName A (8 k)`
(`ConstIndexFold`). This module gives the same fold on a typed chain and proves it
sound on the flag machine.

For slot arrays `R` (name and length), `cellFold R env is` rewrites each
`LOADIDX d, A[x]` and in-place `STOREIDX A, A[x] := v` of a slot array `A` whose index
`x` holds a known constant `k < n` (an immediate `MOV:64 x, $k` earlier in the chain and
no write of `x` since, tracked by `kstep`) into `LOAD:64 d, memName A (8 k)` and `STORE:64 memName A (8 k), v`,
and keeps every other instruction when it names no slot array and no cell (`keepB`).
`CellRel R env s s'` relates a state `s` of the chain to a state `s'` of the folded chain:
the same registers off the cells, arrays off the slot arrays, word memory and flags,
each slot array of `s` held word for word in its cells in `s'`, and the known constants
held in `s`.

## Main results

* `fstepF_of_agree`: a step from states that agree on the instruction's names
  (`JasminLsemExportRewrites.evalInstrPMemF_ren` at the identity renaming).
* `fstepF_movImm64`, `fstepF_load64`, `fstepF_store64`, `fstepF_loadIdx`, `fstepF_storeIdx`:
  the steps of the immediate move, the cell copies and the indexed accesses.
* `keep_step`, `load_step`, `store_step`, `fold_step`: one step of the fold.
* `runStraightF_cellFold`: a run of a chain is matched by a run of its cell fold from
  every cell-related state, into a cell-related state.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames
  sarStruct?_names mulhiStruct?_names adcxStruct?_names adcxhiStruct?_names sbbStruct?_names
  sbbhiStruct?_names castStruct?_names movImmStruct?_names loadStruct?_names
  storeStruct?_names loadCStruct?_names storeCStruct?_names wideArgs?_names_mov
  movRegArgs?_names carryArgs?_names RenOn RenProg RelM RelF CondOK evalInstrPMemF_ren)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (renLinstrR_of_fix)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (evalInstrPMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn
  runStraightF runStraightF_cons)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (mulxFree)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (stepMemF withALUFlags
  withALUFlags_reg withALUFlags_larr carryStep wideStep wideArgs? WideOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame

/-- **A flag-machine step from states that agree on its names.** For an `Lopn` instruction
    that is no `MULX` and a name set `N` holding its names and the empty name, a step
    from `s` is matched by a step from every state `s'` with the same registers and
    arrays on `N`, the same word memory and the same carry and overflow flags, into a
    state related in the same way, with the same zero flag. -/
theorem fstepF_of_agree {i : LinstrRM} (hl : JasminLsemMemLoop.IsLopn i)
    (hc : CondOK i) {N : String → Prop} (hN0 : N "") (hi : ∀ n ∈ instrNames i.1, N n)
    {s s' t : LstateM} {zf z : Bool} (hR : RelM (fun x => x) N s s')
    (hcf : s'.cf = s.cf) (hof : s'.of = s.of) (h : fstepF i s zf = some (t, z)) :
    ∃ t', fstepF i s' zf = some (t', z) ∧ RelM (fun x => x) N t t'
      ∧ t'.cf = t.cf ∧ t'.of = t.of := by
  have hσ : RenOn (fun x => x) N := ⟨fun _ _ _ _ h => h, hN0, rfl⟩
  let P : JasminLsemMemLoop.LprogM := ⟨"", []⟩
  have hP : RenProg (fun x => x) N 0 P P :=
    ⟨rfl, fun _ => rfl, fun _ _ => by simp [P], fun _ _ _ h => by simp [P] at h,
      fun _ _ _ h => by simp [P] at h, fun l pc h => by
        simp [P, JasminLsemMemLoop.findLabelMem, JasminLsemLabeled.findLabel] at h⟩
  have h1 : evalInstrPMemF P i { prog := { base := s, lfn := "" }, zf := zf }
      = some { prog := { base := t, lfn := "" }, zf := z } := by
    rw [evalInstrPMemF_isLopn P i _ hl, h]
    rfl
  obtain ⟨t'', h2, hRt, -⟩ := evalInstrPMemF_ren hσ hP i hi hc
    (s := { prog := { base := s, lfn := "" }, zf := zf })
    (s' := { prog := { base := s', lfn := "" }, zf := zf }) ⟨hR, rfl, rfl, hcf, hof⟩
    (Nat.zero_le _) h1
  have hren : renRM (fun x => x) i = i := by
    obtain ⟨w, tg⟩ := i
    simp only [renRM, Prod.mk.injEq, and_true]
    exact renLinstrR_of_fix _ w fun _ _ => rfl
  rw [hren, evalInstrPMemF_isLopn P i _ hl] at h2
  obtain ⟨bz, hbz, he⟩ := Option.map_eq_some_iff.mp h2
  obtain ⟨b, zb⟩ := bz
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · rw [hbz]
    have : zb = z := by
      have h3 := hRt.2.2.1
      rw [← he] at h3
      exact h3
    rw [this]
  · have h3 := hRt.1
    rw [← he] at h3
    exact h3
  · have h3 := hRt.2.2.2.1
    rw [← he] at h3
    exact h3
  · have h3 := hRt.2.2.2.2
    rw [← he] at h3
    exact h3

theorem fstepF_movImm64 (d : String) (k : Nat) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] "MOV:64" [.imm k], .reg none) s zf
      = some ((s.setReg d (BitVec.ofNat 64 k)).nextPc, zf) := by
  rfl

theorem fstepF_load64 (d c : String) {s : LstateM} (zf : Bool) {w : Nat} {v : BitVec w}
    (hc : s.reg.lvm c = ⟨w, v⟩) :
    fstepF (.Lopn [.reg d] "LOAD:64" [.reg c], .reg none) s zf
      = some ((s.setReg d v).nextPc, zf) := by
  have : fstepF (.Lopn [.reg d] "LOAD:64" [.reg c], .reg none) s zf
      = some ((s.setReg d (s.reg.lvm c).2).nextPc, zf) := rfl
  rw [this, hc]

theorem fstepF_store64 (c u : String) {s : LstateM} (zf : Bool) {w : Nat} {v : BitVec w}
    (hu : s.reg.lvm u = ⟨w, v⟩) :
    fstepF (.Lopn [.reg c] "STORE:64" [.reg u], .reg none) s zf
      = some ((s.setReg c v).nextPc, zf) := by
  have : fstepF (.Lopn [.reg c] "STORE:64" [.reg u], .reg none) s zf
      = some ((s.setReg c (s.reg.lvm u).2).nextPc, zf) := rfl
  rw [this, hu]

/-! ## The fold of constant-index accesses into cell names -/

/-- The slot arrays: the name and the length of each. -/
abbrev Slots := List (String × Nat)

/-- `r` is the name of a slot array. -/
def isArrB (R : Slots) (r : String) : Bool := R.any (·.1 == r)

/-- `r` is a cell name `memName A (8 j)` of a slot array `(A, n)`, `j < n`. -/
def isCellB (R : Slots) (r : String) : Bool :=
  R.any fun p => (List.range p.2).any fun j => r == memName p.1 (8 * j)

/-- The length of the slot array `A`. -/
def lenOf (R : Slots) (A : String) : Option Nat := (R.find? (·.1 == A)).map (·.2)

/-- Registers known to hold constants. -/
abbrev KEnv := List (String × Nat)

/-- The constant a register is known to hold. -/
def kval (env : KEnv) (x : String) : Option Nat := (env.find? (·.1 == x)).map (·.2)

/-- An instruction kept by the fold: an `Lopn`, no `MULX`, naming no slot array and no
    cell. -/
def keepB (R : Slots) (i : LinstrRM) : Bool :=
  isLopnB i && mulxFree i && (instrNames i.1).all fun r => !isArrB R r && !isCellB R r

/-- **The fold of one instruction** under the known constants `env`: a load of a slot
    array at a known index `k` becomes the copy `LOAD:64` from the cell `memName A (8 k)`,
    an in-place store to a slot array at a known index the copy `STORE:64` to that cell;
    every other instruction is kept when `keepB` holds. -/
def foldOne (R : Slots) (env : KEnv) (i : LinstrRM) : Option LinstrRM :=
  match i.2, i.1 with
  | .load w n, .Lopn [.reg d] o [.arrIdx b x _] =>
      if isArrB R b then
        if o = "LOADIDX" ∧ w = 64 ∧ lenOf R b = some n ∧ isCellB R d = false
            ∧ isArrB R d = false then
          match kval env x with
          | some k => if k < n then
              some (.Lopn [.reg d] "LOAD:64" [.reg (memName b (8 * k))], .reg none)
            else none
          | none => none
        else none
      else if keepB R i then some i else none
  | .store w n, .Lopn [.reg d] o [.arrIdx b x _, .reg v] =>
      if isArrB R b then
        if o = "STOREIDX" ∧ w = 64 ∧ d = b ∧ lenOf R b = some n ∧ isCellB R v = false then
          match kval env x with
          | some k => if k < n then
              some (.Lopn [.reg (memName b (8 * k))] "STORE:64" [.reg v], .reg none)
            else none
          | none => none
        else none
      else if keepB R i then some i else none
  | _, _ => if keepB R i then some i else none

/-- The known constants after an instruction: an immediate `MOV:64 d, $k` records `k` at
    `d`; every name the instruction writes is forgotten, and the constants of the names it
    only reads are kept. -/
def kstep (env : KEnv) (i : LinstrRM) : KEnv :=
  let env' := env.filter fun p => !(dstNames i.1).contains p.1
  match i.2, i.1 with
  | .reg none, .Lopn [.reg d] o [.imm k] => if o = "MOV:64" then (d, k) :: env' else env'
  | _, _ => env'

/-- **The cell fold of a chain** from the known constants `env`. -/
def cellFold (R : Slots) : KEnv → List LinstrRM → Option (List LinstrRM)
  | _, [] => some []
  | env, i :: is =>
      match foldOne R env i, cellFold R (kstep env i) is with
      | some i', some is' => some (i' :: is')
      | _, _ => none

/-- The well-formedness of the slot arrays: the empty name is no array and no cell, the
    array names are distinct and every array is shorter than `2 ^ 60`. -/
def slotsOkB (R : Slots) : Bool :=
  !isArrB R "" && !isCellB R "" && (R.map (·.1)).Nodup && R.all (fun p => decide (p.2 < 2 ^ 60))

/-- **The cell relation** of a state `s` of the chain and a state `s'` of the folded
    chain: the same registers off the cells, program counter, arrays off the slot
    arrays, word memory and flags; each slot array of `s` held in its cells in `s'`; and
    the known constants held in `s`. -/
structure CellRel (R : Slots) (env : KEnv) (s s' : LstateM) : Prop where
  reg : ∀ r, isCellB R r = false → s'.reg.lvm r = s.reg.lvm r
  pc : s'.reg.lpc = s.reg.lpc
  arr : ∀ r, isArrB R r = false → s'.larr r = s.larr r
  mem : s'.lmem = s.lmem
  cf : s'.cf = s.cf
  of : s'.of = s.of
  cells : ∀ p ∈ R, ∃ arr : Fin p.2 → BitVec 64, s.getArr p.1 64 p.2 = some arr
    ∧ ∀ j (hj : j < p.2), s'.reg.lvm (memName p.1 (8 * j)) = ⟨64, arr ⟨j, hj⟩⟩
  env : ∀ x k, kval env x = some k → s.reg.getW x 64 = some (BitVec.ofNat 64 k)

theorem fstepF_loadIdx (d b x : String) (sc n : Nat) {s : LstateM} (zf : Bool)
    {arr : Fin n → BitVec 64} {vi : BitVec 64} (hb : s.getArr b 64 n = some arr)
    (hx : s.reg.getW x 64 = some vi) :
    fstepF (.Lopn [.reg d] "LOADIDX" [.arrIdx b x sc], .load 64 n) s zf
      = some ((s.setReg d (JasminDialect.stackGet arr vi.toNat)).nextPc, zf) := by
  simp [fstepF, JasminLsemMemFlagGuard.cmpArgs?, JasminLsemMemFlagGuard.movRegArgs?, stepMemF,
    JasminLsemMem.lsemStepMem, JasminLsemMem.loadStruct?, hb, hx, withALUFlags,
    JasminLsemMemFlagGuard.aluFlagOp?]

theorem fstepF_storeIdx (d b x v : String) (sc n : Nat) {s : LstateM} (zf : Bool)
    {arr : Fin n → BitVec 64} {vi vv : BitVec 64} (hb : s.getArr b 64 n = some arr)
    (hx : s.reg.getW x 64 = some vi) (hv : s.reg.getW v 64 = some vv) :
    fstepF (.Lopn [.reg d] "STOREIDX" [.arrIdx b x sc, .reg v], .store 64 n) s zf
      = some ((s.setArr d (JasminDialect.stackSet arr vi.toNat vv)).nextPc, zf) := by
  simp [fstepF, JasminLsemMemFlagGuard.cmpArgs?, JasminLsemMemFlagGuard.movRegArgs?, stepMemF,
    JasminLsemMem.lsemStepMem, JasminLsemMem.storeStruct?, hb, hx, hv, withALUFlags,
    JasminLsemMemFlagGuard.aluFlagOp?, withWidthTag]

/-! ## Facts of the fold -/

/-- Distinct cells have distinct names. -/
def cellsDistinctB (R : Slots) : Bool :=
  R.all fun p => R.all fun q => (List.range p.2).all fun j => (List.range q.2).all fun j' =>
    !(memName p.1 (8 * j) == memName q.1 (8 * j')) || (p.1 == q.1 && j == j')

theorem cellsDistinct {R : Slots} (h : cellsDistinctB R = true) {p q : String × Nat}
    (hp : p ∈ R) (hq : q ∈ R) {j j' : Nat} (hj : j < p.2) (hj' : j' < q.2)
    (he : memName p.1 (8 * j) = memName q.1 (8 * j')) : p.1 = q.1 ∧ j = j' := by
  have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp h p hp) q hq) j (List.mem_range.mpr hj)) j' (List.mem_range.mpr hj')
  simpa [he] using this

theorem isCellB_cell {R : Slots} {p : String × Nat} (hp : p ∈ R) {j : Nat} (hj : j < p.2) :
    isCellB R (memName p.1 (8 * j)) = true :=
  List.any_eq_true.mpr ⟨p, hp, List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, by simp⟩⟩

theorem isArrB_mem {R : Slots} {p : String × Nat} (hp : p ∈ R) : isArrB R p.1 = true :=
  List.any_eq_true.mpr ⟨p, hp, by simp⟩

theorem lenOf_mem {R : Slots} {A : String} {n : Nat} (h : lenOf R A = some n) :
    (A, n) ∈ R := by
  unfold lenOf at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have h1 := List.mem_of_find?_eq_some hp
  have h2 : p.1 = A := by simpa using List.find?_some hp
  rw [← h2]
  exact h1

theorem kval_cons_self (env : KEnv) (d : String) (k : Nat) : kval ((d, k) :: env) d = some k := by
  simp [kval]

theorem kval_cons_ne {env : KEnv} {d x : String} {k : Nat} (h : x ≠ d) :
    kval ((d, k) :: env) x = kval env x := by
  simp [kval, Ne.symm h]

theorem kval_filter {env : KEnv} {P : String → Bool} {x : String} {k : Nat}
    (h : kval (env.filter fun p => P p.1) x = some k) : kval env x = some k ∧ P x = true := by
  unfold kval at h ⊢
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hx : p.1 = x := by simpa using List.find?_some hp
  have hm := List.mem_of_find?_eq_some hp
  rw [List.mem_filter] at hm
  have hP : P x = true := hx ▸ hm.2
  refine ⟨?_, hP⟩
  rw [List.find?_filter] at hp
  have he : (env.find? fun a => decide (P a.1 = true ∧ (a.1 == x) = true))
      = env.find? fun a => a.1 == x := by
    congr 1
    funext a
    by_cases ha : a.1 = x
    · simp [ha, hP]
    · simp [ha]
  rw [he] at hp
  rw [hp]
  rfl

theorem kstep_env {env : KEnv} {i : LinstrRM} {x : String} {k : Nat}
    (h : kval (kstep env i) x = some k) :
    (kval env x = some k ∧ x ∉ dstNames i.1)
      ∨ (∃ d, i = (.Lopn [.reg d] "MOV:64" [.imm k], .reg none) ∧ x = d) := by
  obtain ⟨w, tg⟩ := i
  have hf : ∀ {k'}, kval (env.filter fun p => !(dstNames w).contains p.1) x = some k' →
      kval env x = some k' ∧ x ∉ dstNames w := fun hk => by
    obtain ⟨h1, h2⟩ := kval_filter (P := fun y => !(dstNames w).contains y) hk
    exact ⟨h1, by simpa using h2⟩
  unfold kstep at h
  dsimp only at h
  split at h
  · rename_i d o n
    split at h
    · rename_i ho
      by_cases hx : x = d
      · subst hx
        rw [kval_cons_self] at h
        cases h
        exact Or.inr ⟨x, by rw [ho], rfl⟩
      · rw [kval_cons_ne hx] at h
        exact Or.inl (hf h)
    · exact Or.inl (hf h)
  · exact Or.inl (hf h)

theorem stepEnv {env : KEnv} {i : LinstrRM} {s t : LstateM} {zf z : Bool}
    (h : fstepF i s zf = some (t, z))
    (hE : ∀ x k, kval env x = some k → s.reg.getW x 64 = some (BitVec.ofNat 64 k)) :
    ∀ x k, kval (kstep env i) x = some k → t.reg.getW x 64 = some (BitVec.ofNat 64 k) := by
  intro x k hk
  rcases kstep_env hk with ⟨h1, h2⟩ | ⟨d, rfl, rfl⟩
  · have hfr := (fstepF_frame_dst h h2).1
    unfold JasminLsemWidthN.LstateN.getW
    rw [hfr]
    exact hE x k h1
  · rw [fstepF_movImm64] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact JasminLsemWidthN.getW_eq_some_iff.mpr (by
      simp [LstateM.setReg, LstateM.nextPc, JasminLsemWidthN.LstateN.setReg,
        JasminLsemWidthN.LstateN.nextPc])

theorem getArr_congr {s t : LstateM} {A : String} (h : t.larr A = s.larr A) (w n : Nat) :
    t.getArr A w n = s.getArr A w n := by
  unfold LstateM.getArr
  rw [h]

/-- **A kept instruction** steps alike from cell-related states. -/
theorem keep_step {R : Slots} (hR : slotsOkB R = true) {env : KEnv} {i : LinstrRM}
    (hk : keepB R i = true) {s s' t : LstateM} {zf z : Bool} (hC : CellRel R env s s')
    (h : fstepF i s zf = some (t, z)) :
    ∃ t', fstepF i s' zf = some (t', z) ∧ CellRel R (kstep env i) t t' := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hk
  obtain ⟨⟨hl, hm⟩, hn⟩ := hk
  simp only [slotsOkB, Bool.and_eq_true, Bool.not_eq_true'] at hR
  have hl' := isLopnB_isLopn hl
  have hc : CondOK i := by
    refine ⟨fun c l he => ?_, hm⟩
    obtain ⟨d, o, sr, hd⟩ := hl'
    rw [hd] at he
    cases he
  let N : String → Prop := fun r => isCellB R r = false ∧ isArrB R r = false
  have hN0 : N "" := ⟨hR.1.1.2, hR.1.1.1⟩
  have hi : ∀ n ∈ instrNames i.1, N n := fun n hn' => ⟨(hn n hn').2, (hn n hn').1⟩
  have hRel : RelM (fun x => x) N s s' :=
    ⟨⟨hC.pc, fun r hr => hC.reg r hr.1⟩, fun r hr => hC.arr r hr.2, hC.mem⟩
  obtain ⟨t', h', hRt, hcf, hof⟩ := fstepF_of_agree hl' hc hN0 hi hRel hC.cf hC.of h
  refine ⟨t', h', ⟨fun r hr => ?_, hRt.1.1, fun r hr => ?_, hRt.2.2, hcf, hof, fun p hp => ?_,
    stepEnv h hC.env⟩⟩
  · by_cases hrn : r ∈ instrNames i.1
    · exact hRt.1.2 r (hi r hrn)
    · rw [(fstepF_frame h' hrn).1, (fstepF_frame h hrn).1]
      exact hC.reg r hr
  · by_cases hrc : isCellB R r = false
    · exact hRt.2.1 r ⟨hrc, hr⟩
    · have hrn : r ∉ instrNames i.1 := fun hm' => hrc (hn r hm').2
      rw [(fstepF_frame h' hrn).2, (fstepF_frame h hrn).2]
      exact hC.arr r hr
  · obtain ⟨arr, ha, hcl⟩ := hC.cells p hp
    have hpn : p.1 ∉ instrNames i.1 := fun hm' => by
      have := (hn p.1 hm').1
      rw [isArrB_mem hp] at this
      cases this
    refine ⟨arr, ?_, fun j hj => ?_⟩
    · rw [getArr_congr (fstepF_frame h hpn).2]
      exact ha
    · have hcn : memName p.1 (8 * j) ∉ instrNames i.1 := fun hm' => by
        have := (hn _ hm').2
        rw [isCellB_cell hp hj] at this
        cases this
      rw [(fstepF_frame h' hcn).1]
      exact hcl j hj

theorem stackGet_lt {n : Nat} (arr : Fin n → BitVec 64) {k : Nat} (hk : k < n) :
    JasminDialect.stackGet arr k = arr ⟨k, hk⟩ := by
  cases n with
  | zero => omega
  | succ m => simp [JasminDialect.stackGet, Nat.mod_eq_of_lt hk]

theorem stackSet_apply {n : Nat} (arr : Fin n → BitVec 64) {k : Nat} (hk : k < n)
    (v : BitVec 64) (j : Fin n) :
    JasminDialect.stackSet arr k v j = if j.val = k then v else arr j := by
  cases n with
  | zero => exact j.elim0
  | succ m =>
      simp only [JasminDialect.stackSet, Nat.mod_eq_of_lt hk, Fin.ext_iff]

theorem slot_lt {R : Slots} (hR : slotsOkB R = true) {p : String × Nat} (hp : p ∈ R) :
    p.2 < 2 ^ 60 := by
  simp only [slotsOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
  exact hR.2 p hp

theorem lvm_setReg_nextPc (s : LstateM) (d r : String) {w : Nat} (v : BitVec w) :
    ((s.setReg d v).nextPc).reg.lvm r = if r = d then ⟨w, v⟩ else s.reg.lvm r := by
  simp [LstateM.setReg, LstateM.nextPc, JasminLsemWidthN.LstateN.setReg,
    JasminLsemWidthN.LstateN.nextPc]

/-- **A folded load** steps alike from cell-related states. -/
theorem load_step {R : Slots} (hR : slotsOkB R = true) {env : KEnv} {d b x : String}
    {sc n k : Nat} (hlen : lenOf R b = some n) (hdc : isCellB R d = false)
    (hk : kval env x = some k) (hkn : k < n) {s s' t : LstateM} {zf z : Bool}
    (hC : CellRel R env s s')
    (h : fstepF (.Lopn [.reg d] "LOADIDX" [.arrIdx b x sc], .load 64 n) s zf = some (t, z)) :
    ∃ t', fstepF (.Lopn [.reg d] "LOAD:64" [.reg (memName b (8 * k))], .reg none) s' zf
        = some (t', z)
      ∧ CellRel R (kstep env (.Lopn [.reg d] "LOADIDX" [.arrIdx b x sc], .load 64 n)) t t' := by
  have hmem := lenOf_mem hlen
  obtain ⟨arr, ha, hcl⟩ := hC.cells _ hmem
  have hx := hC.env x k hk
  have hn60 := slot_lt hR hmem
  have h0 := h
  rw [fstepF_loadIdx d b x sc n zf ha hx] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hv : JasminDialect.stackGet arr (BitVec.ofNat 64 k).toNat = arr ⟨k, hkn⟩ := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp at hn60; omega)]
    exact stackGet_lt arr hkn
  rw [hv] at h0 ⊢
  refine ⟨_, fstepF_load64 d _ zf (hcl k hkn), ⟨fun r hr => ?_, ?_, fun r hr => hC.arr r hr,
    hC.mem, hC.cf, hC.of, fun p hp => ?_, stepEnv h0 hC.env⟩⟩
  · rw [lvm_setReg_nextPc, lvm_setReg_nextPc]
    split
    · rfl
    · exact hC.reg r hr
  · simp [LstateM.setReg, LstateM.nextPc, JasminLsemWidthN.LstateN.setReg,
      JasminLsemWidthN.LstateN.nextPc, hC.pc]
  · obtain ⟨arr', ha', hcl'⟩ := hC.cells p hp
    refine ⟨arr', ha', fun j hj => ?_⟩
    rw [lvm_setReg_nextPc, ite_eq_right]
    · exact hcl' j hj
    · intro he
      have := isCellB_cell hp hj
      rw [he, hdc] at this
      cases this

theorem slot_key {R : Slots} (hR : slotsOkB R = true) {p q : String × Nat} (hp : p ∈ R)
    (hq : q ∈ R) (h : p.1 = q.1) : p = q := by
  simp only [slotsOkB, Bool.and_eq_true] at hR
  have hnd : (R.map (·.1)).Nodup := by simpa using hR.1.2
  exact List.inj_on_of_nodup_map hnd hp hq h

theorem getArr_setArr_self (s : LstateM) (A : String) {n : Nat} (arr : Fin n → BitVec 64) :
    ((s.setArr A arr).nextPc).getArr A 64 n = some arr := by
  have hc : ((s.setArr A arr).nextPc).larr A = ⟨64, n, arr⟩ := by
    simp [LstateM.setArr, LstateM.nextPc]
  rw [LstateM.getArr, hc]
  simp

/-- **A folded store** steps alike from cell-related states. -/
theorem store_step {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    {env : KEnv} {b x v : String} {sc n k : Nat} (hlen : lenOf R b = some n)
    (hvc : isCellB R v = false) (hk : kval env x = some k) (hkn : k < n)
    {s s' t : LstateM} {zf z : Bool} (hC : CellRel R env s s')
    (h : fstepF (.Lopn [.reg b] "STOREIDX" [.arrIdx b x sc, .reg v], .store 64 n) s zf
      = some (t, z)) :
    ∃ t', fstepF (.Lopn [.reg (memName b (8 * k))] "STORE:64" [.reg v], .reg none) s' zf
        = some (t', z)
      ∧ CellRel R (kstep env (.Lopn [.reg b] "STOREIDX" [.arrIdx b x sc, .reg v], .store 64 n))
        t t' := by
  have hmem := lenOf_mem hlen
  obtain ⟨arr, ha, hcl⟩ := hC.cells _ hmem
  have hx := hC.env x k hk
  have hn60 := slot_lt hR hmem
  have h0 := h
  cases hvv : s.reg.getW v 64 with
  | none =>
      exfalso
      simp [fstepF, JasminLsemMemFlagGuard.cmpArgs?, JasminLsemMemFlagGuard.movRegArgs?,
        stepMemF, JasminLsemMem.lsemStepMem, JasminLsemMem.storeStruct?, ha, hx, hvv,
        withWidthTag, JasminLsemMemFlagGuard.carryArgs?, wideArgs?] at h
  | some vv =>
  rw [fstepF_storeIdx b b x v sc n zf ha hx hvv] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hkk : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp at hn60; omega)]
  rw [hkk] at h0 ⊢
  have hv' : s'.reg.lvm v = ⟨64, vv⟩ := by
    rw [hC.reg v hvc]
    exact JasminLsemWidthN.getW_eq_some_iff.mp hvv
  have hbc : isArrB R b = true := isArrB_mem hmem
  refine ⟨_, fstepF_store64 _ v zf hv', ⟨fun r hr => ?_, ?_, fun r hr => ?_,
    hC.mem, hC.cf, hC.of, fun p hp => ?_, stepEnv h0 hC.env⟩⟩
  · rw [lvm_setReg_nextPc, ite_eq_right]
    · exact hC.reg r hr
    · intro he
      rw [he, isCellB_cell hmem hkn] at hr
      cases hr
  · simp [LstateM.setReg, LstateM.setArr, LstateM.nextPc, JasminLsemWidthN.LstateN.setReg,
      JasminLsemWidthN.LstateN.nextPc, hC.pc]
  · have hrb : r ≠ b := fun he => by rw [he, hbc] at hr; cases hr
    simp only [LstateM.setReg, LstateM.setArr, LstateM.nextPc, hrb, ite_false]
    exact hC.arr r hr
  · by_cases hpb : p.1 = b
    · have hpe : p = (b, n) := slot_key hR hp hmem hpb
      subst hpe
      refine ⟨JasminDialect.stackSet arr k vv, getArr_setArr_self _ _ _, fun j hj => ?_⟩
      rw [lvm_setReg_nextPc, stackSet_apply arr hkn]
      by_cases hjk : j = k
      · subst hjk
        simp
      · rw [ite_eq_right, ite_eq_right hjk]
        · exact hcl j hj
        · intro he
          exact hjk (cellsDistinct hD hp hp hj hkn he).2
    · obtain ⟨arr', ha', hcl'⟩ := hC.cells p hp
      refine ⟨arr', ?_, fun j hj => ?_⟩
      · rw [getArr_congr (s := s) (A := p.1)
          (t := (s.setArr b (JasminDialect.stackSet arr k vv)).nextPc)
          (by simp [LstateM.setArr, LstateM.nextPc, hpb])]
        exact ha'
      · rw [lvm_setReg_nextPc, ite_eq_right]
        · exact hcl' j hj
        · intro he
          exact hpb (cellsDistinct hD hp hmem hj hkn he).1

/-- **One step of the fold.** -/
theorem fold_step {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    {env : KEnv} {i i' : LinstrRM} (hf : foldOne R env i = some i') {s s' t : LstateM}
    {zf z : Bool} (hC : CellRel R env s s') (h : fstepF i s zf = some (t, z)) :
    ∃ t', fstepF i' s' zf = some (t', z) ∧ CellRel R (kstep env i) t t' := by
  obtain ⟨wire, tg⟩ := i
  unfold foldOne at hf
  dsimp only at hf
  split at hf
  · rename_i w n d o b x sc
    split at hf
    · split at hf
      · rename_i hc
        obtain ⟨rfl, rfl, hlen, hdc, -⟩ := hc
        split at hf
        · rename_i k hk
          split at hf
          · rename_i hkn
            cases hf
            exact load_step hR hlen hdc hk hkn hC h
          · cases hf
        · cases hf
      · cases hf
    · split at hf
      · rename_i hk
        cases hf
        exact keep_step hR hk hC h
      · cases hf
  · rename_i w n d o b x sc v
    split at hf
    · split at hf
      · rename_i hc
        obtain ⟨rfl, rfl, rfl, hlen, hvc⟩ := hc
        split at hf
        · rename_i k hk
          split at hf
          · rename_i hkn
            cases hf
            exact store_step hR hD hlen hvc hk hkn hC h
          · cases hf
        · cases hf
      · cases hf
    · split at hf
      · rename_i hk
        cases hf
        exact keep_step hR hk hC h
      · cases hf
  · split at hf
    · rename_i hk
      cases hf
      exact keep_step hR hk hC h
    · cases hf

/-- **The cell fold realises the chain.** For slot arrays `R` that pass `slotsOkB` and
    `cellsDistinctB`, and a chain `is` whose cell fold from the known constants `env` is
    `is'`: a run of `is` on the flag machine from `s` is matched by a run of `is'` from
    every cell-related state `s'`, into a cell-related state. -/
theorem runStraightF_cellFold {R : Slots} (hR : slotsOkB R = true)
    (hD : cellsDistinctB R = true) :
    ∀ (is : List LinstrRM) (env : KEnv) (is' : List LinstrRM), cellFold R env is = some is' →
      ∀ {s s' b : LstateM} {zf z : Bool}, CellRel R env s s' →
        runStraightF is s zf = some (b, z) →
        ∃ env' b', runStraightF is' s' zf = some (b', z) ∧ CellRel R env' b b'
  | [], env, is', hf, s, s', b, zf, z, hC, h => by
      cases hf
      cases h
      exact ⟨env, s', rfl, hC⟩
  | i :: is, env, is', hf, s, s', b, zf, z, hC, h => by
      unfold cellFold at hf
      split at hf
      · rename_i i' is'' h1 h2
        cases hf
        rw [runStraightF_cons] at h
        cases hs : fstepF i s zf with
        | none => rw [hs] at h; cases h
        | some tz =>
            obtain ⟨t, z1⟩ := tz
            rw [hs] at h
            simp only [Option.bind_some] at h
            obtain ⟨t', h', hC'⟩ := fold_step hR hD h1 hC hs
            obtain ⟨env', b', hr, hCb⟩ := runStraightF_cellFold hR hD is _ _ h2 hC' h
            refine ⟨env', b', ?_, hCb⟩
            rw [runStraightF_cons, h']
            exact hr
      · cases hf

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
