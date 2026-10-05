/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksMemF
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

/-!
# The bridge between the uniform-width and the flag machine semantics of `Lprog`

Two straight-line semantics run the same `LinstrR` bodies. `JasminLsem.lsemStep` steps a
state `Lstate 64` with a uniform-width register file `lvm` and a word memory `lmem` that a
runtime-indexed access `LOADIDX`/`STOREIDX (B, x, 8)` reads and writes at byte offset
`8 · x`. `JasminLsemMemFlagGuard.stepMemF` steps a state `LstateM` with a width-tagged
register file, stack arrays `larr` that the same accesses read and write by element index
under the memory tag `MemTag.load 64 n`/`MemTag.store 64 n`, and the carry and overflow
flags `cf`, `of`.

`LsemRel A s l` relates the two states: every register of `s` holds the 64-bit value of
`l`, the program counters agree, and every array `B` with `A B = some n` is the array of the
`n` words of `l.lmem` at the byte offsets `8 · k`, `k < n`. The flags of `s` are not
related: `Lstate 64` has none.

On the fragment `fragB A` (64-bit two-source arithmetic and logic with a register first
source, the immediate move, and the indexed load and in-place store at scale `8` on a
tracked array), from related states both machines step, and the results are related
(`lsemStep_stepMemF_rel`), provided an indexed access is in bounds (`inBoundsB`). The
in-bounds run `runIB` is `lsemStraight` that fails at an out-of-bounds indexed access.

## Main definitions

* `LsemRel` — the relation between `LstateM` and `Lstate 64`.
* `Shape`, `shape?`, `fragB` — the modelled fragment as a decidable predicate.
* `inBoundsB`, `runIB` — the in-bounds condition of one step and of a run.
* `ObsAgree` — agreement of two `Lstate 64` on observed registers and tracked arrays.

## Main results

* `lsemStep_stepMemF_rel` — the per-instruction simulation on the fragment.
* `lsemStraight_lsemStraightMemF_rel` — the simulation of a run.
* `lsemStraightMemF_transport`, `lsemFuelMemF_transport` — two fragment bodies whose
  `lsemStraight` runs agree on the observed names run under `stepMemF` (and under
  `lsemFuelMemF` in a singleton program) to states that agree on those names, on every
  array and on the word memory.
* `runIB_scheduleBody` — the schedule preserves the in-bounds run.
* `scheduleBody_lsemStraightMemF_bridge` — schedule soundness on the flag machine, up to the
  flags, derived from `LprogScheduler.scheduleBody_lsemStraight` through the bridge.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
  (hasArrIdx opIsArrIdx indep indep_arrIdx_left indep_arrIdx_right lsemStraight_swap
    scheduleBody scheduleBody_run scheduleBody_lsemStraight scheduleBody_perm scheduleBody_length)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksMemF (lstateN_ext lstateM_ext)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
  (lsemStepMem_regArith3 lsemStepMem_movImm)

/-! ## 1. The relation -/

/-- The relation between a flag-machine state `s` and a uniform-width state `l`. Every
    register of `s` holds the 64-bit value `l` gives it, the program counters agree, and
    every tracked array `B` (`A B = some n`) is the array of the words of `l.lmem B` at the
    byte offsets `8 · k`, `k < n`. The flags of `s` are unconstrained. -/
structure LsemRel (A : String → Option Nat) (s : LstateM) (l : Lstate 64) : Prop where
  /-- Every register is a 64-bit register holding the value of `l`. -/
  regs : ∀ r, s.reg.lvm r = ⟨64, l.lvm r⟩
  /-- The program counters agree. -/
  pc : s.reg.lpc = l.lpc
  /-- Every tracked array is the word memory of `l` at the offsets `8 · k`. -/
  arrs : ∀ B n, A B = some n →
    s.larr B = ⟨64, n, fun k => l.lmem B (Int.ofNat (8 * k.val))⟩

theorem LsemRel.getW {A : String → Option Nat} {s : LstateM} {l : Lstate 64}
    (h : LsemRel A s l) (r : String) : s.reg.getW r 64 = some (l.lvm r) :=
  getW_eq_some_iff.2 (h.regs r)

theorem LsemRel.getArr {A : String → Option Nat} {s : LstateM} {l : Lstate 64}
    (h : LsemRel A s l) {B : String} {n : Nat} (hB : A B = some n) :
    s.getArr B 64 n = some (fun k => l.lmem B (Int.ofNat (8 * k.val))) := by
  unfold LstateM.getArr
  rw [h.arrs B n hB]
  simp

/-- The relation does not read the flags. -/
theorem LsemRel.setFlags {A : String → Option Nat} {s : LstateM} {l : Lstate 64}
    (h : LsemRel A s l) (c o : Bool) : LsemRel A { s with cf := c, of := o } l :=
  ⟨h.regs, h.pc, h.arrs⟩

/-- Two flag-machine states related to the same uniform-width state have the same
    register file and the same tracked arrays. -/
theorem LsemRel.functional {A : String → Option Nat} {s s' : LstateM} {l : Lstate 64}
    (h : LsemRel A s l) (h' : LsemRel A s' l) :
    s.reg = s'.reg ∧ ∀ B n, A B = some n → s.larr B = s'.larr B := by
  refine ⟨lstateN_ext (funext fun r => by rw [h.regs, h'.regs]) (by rw [h.pc, h'.pc]), ?_⟩
  intro B n hB
  rw [h.arrs B n hB, h'.arrs B n hB]

/-! ## 2. The fragment -/

/-- The base mnemonics of the two-source arithmetic and logical arm. -/
def aluBases : List String := ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "ANDN"]

/-- A second source that is a register or an immediate. -/
def regOrImm : LOperand → Bool
  | .reg _ => true
  | .imm _ => true
  | _ => false

/-- The instruction shapes of the fragment. -/
inductive Shape where
  /-- `d := a m b` at width `64`, `m ∈ aluBases`. -/
  | alu (d m a : String) (b : LOperand)
  /-- `d := $k` at width `64`. -/
  | movImm (d : String) (k : Nat)
  /-- `d := B[x]`, the array `B` of `n` words. -/
  | load (d B x : String) (n : Nat)
  /-- `B[x] := v` in place, the array `B` of `n` words. -/
  | store (B x v : String) (n : Nat)

/-- The tagged instruction of a shape. -/
def Shape.toInstr : Shape → LinstrRM
  | .alu d m a b => (.Lopn [.reg d] (withWidthTag 64 m) [.reg a, b], .reg none)
  | .movImm d k => (.Lopn [.reg d] (withWidthTag 64 "MOV") [.imm k], .reg none)
  | .load d B x n => (.Lopn [.reg d] "LOADIDX" [.arrIdx B x 8], .load 64 n)
  | .store B x v n => (.Lopn [.reg B] "STOREIDX" [.arrIdx B x 8, .reg v], .store 64 n)

/-- The side conditions of a shape: a modelled mnemonic and second source, and an indexed
    access on a tracked array of the tagged length. -/
def Shape.ok (A : String → Option Nat) : Shape → Bool
  | .alu _ m _ b => decide (m ∈ aluBases) && regOrImm b
  | .movImm _ _ => true
  | .load _ B _ n => decide (A B = some n)
  | .store B _ _ n => decide (A B = some n)

/-- The shape recognizer. -/
def shape? : LinstrRM → Option Shape
  | (.Lopn [.reg d] opn [.reg a, b], .reg none) =>
      if opn = withWidthTag 64 (stripWidthTag opn) then some (.alu d (stripWidthTag opn) a b)
      else none
  | (.Lopn [.reg d] opn [.imm k], .reg none) =>
      if opn = withWidthTag 64 "MOV" then some (.movImm d k) else none
  | (.Lopn [.reg d] opn [.arrIdx B x sc], .load w n) =>
      if opn = "LOADIDX" ∧ sc = 8 ∧ w = 64 then some (.load d B x n) else none
  | (.Lopn [.reg d] opn [.arrIdx B x sc, .reg v], .store w n) =>
      if opn = "STOREIDX" ∧ sc = 8 ∧ w = 64 ∧ d = B then some (.store B x v n) else none
  | _ => none

theorem shape?_toInstr {i : LinstrRM} {sh : Shape} (h : shape? i = some sh) :
    sh.toInstr = i := by
  unfold shape? at h
  split at h
  · split_ifs at h with hc
    cases h
    simp only [Shape.toInstr]
    rw [← hc]
  · split_ifs at h with hc
    cases h
    subst hc
    rfl
  · split_ifs at h with hc
    cases h
    obtain ⟨rfl, rfl, rfl⟩ := hc
    rfl
  · split_ifs at h with hc
    cases h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
    rfl
  · cases h

/-- **The modelled fragment**, a decidable predicate on tagged instructions. -/
def fragB (A : String → Option Nat) (i : LinstrRM) : Bool :=
  match shape? i with
  | some sh => sh.ok A
  | none => false

theorem fragB_shape {A : String → Option Nat} {i : LinstrRM} (h : fragB A i = true) :
    ∃ sh : Shape, sh.toInstr = i ∧ sh.ok A = true := by
  unfold fragB at h
  split at h
  · next sh hs => exact ⟨sh, shape?_toInstr hs, h⟩
  · exact absurd h (by simp)

/-! ## 3. The in-bounds condition -/

/-- An indexed access under a `load`/`store` tag of length `n` reads its index below `n` in
    `l`; every other instruction is in bounds. -/
def inBoundsB (l : Lstate 64) : LinstrRM → Bool
  | (.Lopn _ _ (.arrIdx _ x _ :: _), .load _ n) => decide ((l.lvm x).toNat < n)
  | (.Lopn _ _ (.arrIdx _ x _ :: _), .store _ n) => decide ((l.lvm x).toNat < n)
  | _ => true

theorem inBoundsB_of_hasArrIdx {i : LinstrR} (h : hasArrIdx i = false) (t : MemTag)
    (l : Lstate 64) : inBoundsB l (i, t) = true := by
  unfold inBoundsB
  split <;> simp_all [hasArrIdx, opIsArrIdx]

/-- One step of `lsemStraight` that fails at an out-of-bounds indexed access. -/
def stepIB (i : LinstrRM) (l : Lstate 64) : Option (Lstate 64) :=
  if inBoundsB l i then lsemStep i.1 l else none

/-- The in-bounds run: `lsemStraight` failing at an out-of-bounds indexed access. -/
def runIB : List LinstrRM → Lstate 64 → Option (Lstate 64)
  | [], l => some l
  | i :: is, l => (stepIB i l).bind (runIB is)

theorem runIB_append (l1 l2 : List LinstrRM) (l : Lstate 64) :
    runIB (l1 ++ l2) l = (runIB l1 l).bind (runIB l2) := by
  induction l1 generalizing l with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runIB, ih, Option.bind_assoc]

/-- The in-bounds run is `lsemStraight` where it succeeds. -/
theorem runIB_lsemStraight :
    ∀ (body : List LinstrRM) (l t : Lstate 64),
      runIB body l = some t → lsemStraight (body.map Prod.fst) l = some t := by
  intro body
  induction body with
  | nil => intro l t h; simpa [runIB] using h
  | cons i is ih =>
      intro l t h
      simp only [runIB, stepIB] at h
      by_cases hb : inBoundsB l i = true
      swap
      · simp [hb] at h
      rw [if_pos hb] at h
      cases hs : lsemStep i.1 l with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some l1 =>
          rw [hs, Option.bind_some] at h
          simp only [List.map_cons, lsemStraight_cons, hs]
          exact ih l1 t h

/-! ## 4. The per-instruction simulation -/

theorem alu_facts {m : String} (hm : m ∈ aluBases) (x y : BitVec 64) :
    stripWidthTag (withWidthTag 64 m) = m ∧ m ≠ "MULXHI" ∧ m ≠ "ADCX" ∧ m ≠ "ADCXHI" ∧
      m ≠ "SAR" ∧ ∃ v, applyOpnN 64 m [x, y] = some v ∧ applyOpn m [x, y] = some v := by
  simp only [aluBases, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide +kernel, by decide, by decide, by decide, by decide, _, rfl, rfl⟩

theorem evalOperand_regOrImm {A : String → Option Nat} {s : LstateM} {l : Lstate 64}
    (h : LsemRel A s l) {b : LOperand} (hb : regOrImm b = true) :
    evalOperandN s.reg 64 b = some (evalOperand l b) := by
  cases b with
  | reg r => exact h.getW r
  | imm k => rfl
  | arr _ _ => exact absurd hb (by simp [regOrImm])
  | arrIdx _ _ _ => exact absurd hb (by simp [regOrImm])

/-- A register write and a pc step on both sides preserve the relation. -/
theorem LsemRel.setReg {A : String → Option Nat} {s : LstateM} {l : Lstate 64}
    (h : LsemRel A s l) (d : String) (v : BitVec 64) :
    LsemRel A { s with reg := (s.reg.setReg d v).nextPc } (l.setReg d v).nextPc := by
  refine ⟨fun r => ?_, by simp [h.pc], fun B n hB => h.arrs B n hB⟩
  by_cases hr : r = d
  · subst hr; simp [Lstate.setReg]
  · simp [Lstate.setReg, hr, h.regs r]

/-- **Per-instruction simulation on the fragment.** From related states, an in-bounds
    fragment instruction steps under both `stepMemF` and `lsemStep`, the results are
    related, the word memory of the flag machine is unchanged, and so is every untracked
    array. -/
theorem lsemStep_stepMemF_rel {A : String → Option Nat} {i : LinstrRM}
    (hi : fragB A i = true) {s : LstateM} {l : Lstate 64} (hr : LsemRel A s l)
    (hb : inBoundsB l i = true) :
    ∃ s' l', stepMemF i s = some s' ∧ lsemStep i.1 l = some l' ∧ LsemRel A s' l' ∧
      s'.lmem = s.lmem ∧ ∀ b, A b = none → s'.larr b = s.larr b := by
  obtain ⟨sh, rfl, hok⟩ := fragB_shape hi
  clear hi
  cases sh <;> simp only [Shape.toInstr] at hb ⊢
  case alu d m a b =>
      simp only [Shape.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hm, hb2⟩ := hok
      obtain ⟨hstrip, h1, h2, h3, h4, v, hN, hO⟩ := alu_facts hm (l.lvm a) (evalOperand l b)
      have hM := lsemStepMem_regArith3 d a b s m hstrip h1 h2 h3 h4 _ _ v (hr.getW a)
        (evalOperand_regOrImm hr hb2) hN
      obtain ⟨c, o, hw⟩ := withALUFlags_eq
        (.Lopn [.reg d] (withWidthTag 64 m) [.reg a, b], .reg none) s
        { s with reg := (s.reg.setReg d v).nextPc }
      refine ⟨_, (l.setReg d v).nextPc, by rw [stepMemF_of_lsemStepMem hM, hw], ?_,
        (hr.setReg d v).setFlags c o, rfl, fun _ _ => rfl⟩
      simp only [lsemStep, hstrip, List.map]
      rw [show evalOperand l (.reg a) = l.lvm a from rfl, hO]
  case movImm d k =>
      have hM := lsemStepMem_movImm d k s
      obtain ⟨c, o, hw⟩ := withALUFlags_eq
        (.Lopn [.reg d] (withWidthTag 64 "MOV") [.imm k], .reg none) s
        { s with reg := (s.reg.setReg d (BitVec.ofNat 64 k)).nextPc }
      refine ⟨_, (l.setReg d (BitVec.ofNat 64 k)).nextPc,
        by rw [stepMemF_of_lsemStepMem hM, hw], ?_,
        (hr.setReg d _).setFlags c o, rfl, fun _ _ => rfl⟩
      simp only [lsemStep, JasminLsemScalar.stripWidthTag_withWidthTag_MOV, List.map,
        evalOperand]
      rfl
  case load d B x n =>
      simp only [Shape.ok, decide_eq_true_eq] at hok
      simp only [inBoundsB, decide_eq_true_eq] at hb
      have hg : stackGet (fun k : Fin n => l.lmem B (Int.ofNat (8 * k.val))) (l.lvm x).toNat
          = l.lmem B (Int.ofNat (8 * (l.lvm x).toNat)) := stackGet_id _ ⟨_, hb⟩
      have hM : lsemStepMem (.Lopn [.reg d] "LOADIDX" [.arrIdx B x 8], .load 64 n) s
          = some { s with reg := (s.reg.setReg d
              (l.lmem B (Int.ofNat (8 * (l.lvm x).toNat)))).nextPc } := by
        simp only [lsemStepMem, loadStruct?, if_pos, hr.getArr hok, hr.getW x, hg]
        rfl
      obtain ⟨c, o, hw⟩ := withALUFlags_eq
        (.Lopn [.reg d] "LOADIDX" [.arrIdx B x 8], .load 64 n) s
        { s with reg := (s.reg.setReg d (l.lmem B (Int.ofNat (8 * (l.lvm x).toNat)))).nextPc }
      exact ⟨_, _, by rw [stepMemF_of_lsemStepMem hM, hw]; rfl, lsemStep_loadidx d B x 8 l,
        (hr.setReg d _).setFlags c o, rfl, fun _ _ => rfl⟩
  case store B x v n =>
      simp only [Shape.ok, decide_eq_true_eq] at hok
      simp only [inBoundsB, decide_eq_true_eq] at hb
      set vi := (l.lvm x).toNat with hvi
      have hM : lsemStepMem (.Lopn [.reg B] "STOREIDX" [.arrIdx B x 8, .reg v], .store 64 n) s
          = some { s with
              reg := s.reg.nextPc,
              larr := fun r => if r = B then
                ⟨64, n, stackSet (fun k : Fin n => l.lmem B (Int.ofNat (8 * k.val))) vi (l.lvm v)⟩
                else s.larr r } := by
        simp only [lsemStepMem, storeStruct?, if_pos, hr.getArr hok, hr.getW x, hr.getW v]
        rfl
      obtain ⟨c, o, hw⟩ := withALUFlags_eq
        (.Lopn [.reg B] "STOREIDX" [.arrIdx B x 8, .reg v], .store 64 n) s
        { s with
              reg := s.reg.nextPc,
              larr := fun r => if r = B then
                ⟨64, n, stackSet (fun k : Fin n => l.lmem B (Int.ofNat (8 * k.val))) vi (l.lvm v)⟩
                else s.larr r }
      refine ⟨{ s with
              reg := s.reg.nextPc,
              larr := fun r => if r = B then
                ⟨64, n, stackSet (fun k : Fin n => l.lmem B (Int.ofNat (8 * k.val))) vi (l.lvm v)⟩
                else s.larr r,
              cf := c, of := o }, _,
        by rw [stepMemF_of_lsemStepMem hM, hw], lsemStep_storeidx B B x 8 (.reg v) l,
        ⟨fun r => hr.regs r, by simp [hr.pc], fun B' n' hB' => ?_⟩, rfl, fun b hb' => ?_⟩
      · dsimp only
        by_cases hBB : B' = B
        · subst hBB
          rw [hok] at hB'
          cases hB'
          rw [if_pos rfl]
          congr 2
          funext k
          cases n with
          | zero => exact absurd hb (by omega)
          | succ m =>
              simp only [stackSet, Nat.mod_eq_of_lt hb, evalOperand, ← hvi]
              rw [Lstate.lmem_nextPc]
              dsimp only
              rw [if_pos rfl]
              by_cases hk : k = ⟨vi, hb⟩
              · subst hk; simp
              · have hk' : Int.ofNat (8 * k.val) ≠ Int.ofNat (8 * vi) := by
                  intro he
                  apply hk
                  ext
                  show k.val = vi
                  simp only [Int.ofNat_eq_natCast, Nat.cast_mul] at he
                  omega
                rw [if_neg hk, if_neg hk']
        · rw [if_neg hBB, hr.arrs B' n' hB']
          simp [hBB]
      · have hbB : b ≠ B := by rintro rfl; rw [hok] at hb'; cases hb'
        simp [hbB]

/-! ## 5. The simulation of a run -/

/-- **Run simulation on the fragment.** From related states, a fragment body whose in-bounds
    run succeeds runs under `lsemStraightMemF` to a state related to the result of the
    in-bounds run, with the word memory and every untracked array unchanged. -/
theorem lsemStraight_lsemStraightMemF_rel {A : String → Option Nat} :
    ∀ (body : List LinstrRM) (s : LstateM) (l : Lstate 64),
      (∀ i ∈ body, fragB A i = true) → LsemRel A s l → (runIB body l).isSome →
      ∃ s' l', lsemStraightMemF body s = some s' ∧ runIB body l = some l' ∧
        LsemRel A s' l' ∧ s'.lmem = s.lmem ∧ ∀ b, A b = none → s'.larr b = s.larr b := by
  intro body
  induction body with
  | nil => intro s l _ hr _; exact ⟨s, l, rfl, rfl, hr, rfl, fun _ _ => rfl⟩
  | cons i is ih =>
      intro s l hf hr hib
      simp only [runIB, stepIB] at hib ⊢
      by_cases hb : inBoundsB l i = true
      swap
      · simp [hb] at hib
      rw [if_pos hb] at hib ⊢
      obtain ⟨s1, l1, hs1, hl1, hr1, hm1, ha1⟩ :=
        lsemStep_stepMemF_rel (hf i List.mem_cons_self) hr hb
      rw [hl1, Option.bind_some] at hib ⊢
      obtain ⟨s2, l2, hs2, hl2, hr2, hm2, ha2⟩ :=
        ih s1 l1 (fun j hj => hf j (List.mem_cons_of_mem i hj)) hr1 hib
      refine ⟨s2, l2, ?_, hl2, hr2, hm2.trans hm1, fun b hb' => (ha2 b hb').trans (ha1 b hb')⟩
      rw [lsemStraightMemF_cons, hs1, Option.bind_some, hs2]

/-! ## 6. Transport -/

/-- Agreement of two uniform-width states on the registers satisfying `O` and on the words
    of every tracked array. -/
def ObsAgree (O : String → Prop) (A : String → Option Nat) (t t' : Lstate 64) : Prop :=
  (∀ r, O r → t.lvm r = t'.lvm r) ∧
    ∀ B n, A B = some n → ∀ k < n, t.lmem B (Int.ofNat (8 * k)) = t'.lmem B (Int.ofNat (8 * k))

/-- **Transport.** Let `B` and `B'` be fragment bodies whose in-bounds runs from `l` succeed
    and whose `lsemStraight` runs from `l` agree on the observed registers `O` and on the
    tracked arrays. From a state related to `l`, both run under `lsemStraightMemF`, and the
    results agree on the registers `O`, on every array and on the word memory. -/
theorem lsemStraightMemF_transport {A : String → Option Nat} {O : String → Prop}
    {B B' : List LinstrRM} (hB : ∀ i ∈ B, fragB A i = true) (hB' : ∀ i ∈ B', fragB A i = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRel A s l)
    (hib : (runIB B l).isSome) (hib' : (runIB B' l).isSome)
    (hpass : ∀ t t', lsemStraight (B.map Prod.fst) l = some t →
      lsemStraight (B'.map Prod.fst) l = some t' → ObsAgree O A t t') :
    ∃ u u', lsemStraightMemF B s = some u ∧ lsemStraightMemF B' s = some u' ∧
      (∀ r, O r → u.reg.lvm r = u'.reg.lvm r) ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem := by
  obtain ⟨u, t, hu, ht, hrt, hmu, hau⟩ := lsemStraight_lsemStraightMemF_rel B s l hB hr hib
  obtain ⟨u', t', hu', ht', hrt', hmu', hau'⟩ :=
    lsemStraight_lsemStraightMemF_rel B' s l hB' hr hib'
  obtain ⟨hO, hA⟩ := hpass t t' (runIB_lsemStraight B l t ht) (runIB_lsemStraight B' l t' ht')
  refine ⟨u, u', hu, hu', fun r hr' => by rw [hrt.regs, hrt'.regs, hO r hr'], ?_,
    hmu.trans hmu'.symm⟩
  funext b
  cases hb : A b with
  | none => rw [hau b hb, hau' b hb]
  | some n =>
      rw [hrt.arrs b n hb, hrt'.arrs b n hb]
      congr 2
      funext k
      exact hA b n hb k.val k.isLt

/-- A fragment instruction is a plain `Lopn`: neither a flag-`CMP` nor a register copy. -/
theorem fragB_plain {A : String → Option Nat} {i : LinstrRM} (hi : fragB A i = true) :
    IsLopn i ∧ cmpArgs? i = none ∧ movRegArgs? i = none := by
  obtain ⟨sh, rfl, hok⟩ := fragB_shape hi
  cases sh with
  | alu d m a b =>
      simp only [Shape.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hm, -⟩ := hok
      simp only [aluBases, List.mem_cons, List.not_mem_nil, or_false] at hm
      refine ⟨⟨_, _, _, rfl⟩, ?_, rfl⟩
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Shape.toInstr, cmpArgs?, withWidthTag]
  | movImm d k => exact ⟨⟨_, _, _, rfl⟩, rfl, rfl⟩
  | load d B x n => exact ⟨⟨_, _, _, rfl⟩, rfl, rfl⟩
  | store B x v n =>
      exact ⟨⟨_, _, _, rfl⟩, by simp [Shape.toInstr, cmpArgs?, withWidthTag], rfl⟩

/-- A fragment body run by `lsemFuelMemF` as a singleton program from pc `0`, with fuel its
    length, is the run of `lsemStraightMemF`. -/
theorem lsemFuelMemF_of_frag {A : String → Option Nat} {body : List LinstrRM}
    (hB : ∀ i ∈ body, fragB A i = true) (fn : String) (zf : Bool) {s u : LstateM}
    (hpc : s.reg.lpc = 0) (hu : lsemStraightMemF body s = some u) :
    lsemFuelMemF (singletonProgM fn body) body.length { prog := { base := s, lfn := fn }, zf := zf }
      = some { prog := { base := u, lfn := fn }, zf := zf } := by
  have hseg := lsemFuelMemF_seg (singletonProgM fn body) fn rfl body s zf 0
    (fun i hi => fragB_plain (hB i hi))
    (fun k _ => by simp [singletonProgM, LstateM.lpc, hpc])
  rw [Nat.add_zero] at hseg
  rw [hseg, hu, Option.bind_some]
  apply lsemFuelMemF_halt
  rw [findInstrMem_singleton fn body _ rfl]
  have := lsemStraightMemF_lpc body s u hu
  simp only [LstateM.lpc, hpc, Nat.zero_add] at this
  simp [LstateM.lpc, this]

/-- **Transport to the fuel machine.** Under the hypotheses of `lsemStraightMemF_transport`
    and from pc `0`, the singleton programs of `B` and `B'` run under `lsemFuelMemF` with fuel
    their lengths to halted states whose bases agree on the registers `O`, on every array
    and on the word memory, with the zero flag and the function name unchanged. -/
theorem lsemFuelMemF_transport {A : String → Option Nat} {O : String → Prop}
    {B B' : List LinstrRM} (hB : ∀ i ∈ B, fragB A i = true) (hB' : ∀ i ∈ B', fragB A i = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRel A s l)
    (hib : (runIB B l).isSome) (hib' : (runIB B' l).isSome)
    (hpass : ∀ t t', lsemStraight (B.map Prod.fst) l = some t →
      lsemStraight (B'.map Prod.fst) l = some t' → ObsAgree O A t t')
    (fn : String) (zf : Bool) (hpc : s.reg.lpc = 0) :
    ∃ u u',
      lsemFuelMemF (singletonProgM fn B) B.length { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := u, lfn := fn }, zf := zf } ∧
      lsemFuelMemF (singletonProgM fn B') B'.length { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := u', lfn := fn }, zf := zf } ∧
      (∀ r, O r → u.reg.lvm r = u'.reg.lvm r) ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem := by
  obtain ⟨u, u', hu, hu', hO, hA, hM⟩ := lsemStraightMemF_transport hB hB' hr hib hib' hpass
  exact ⟨u, u', lsemFuelMemF_of_frag hB fn zf hpc hu, lsemFuelMemF_of_frag hB' fn zf hpc hu',
    hO, hA, hM⟩

/-! ## 7. Schedule soundness through the bridge -/

/-- Two adjacent independent instructions commute under the in-bounds run. -/
theorem runIB_swap (tag : LinstrR → MemTag) (i1 i2 : LinstrR) (rest : List LinstrR)
    (l : Lstate 64) (h : indep i1 i2 = true) :
    runIB ((i1 :: i2 :: rest).map fun i => (i, tag i)) l
      = runIB ((i2 :: i1 :: rest).map fun i => (i, tag i)) l := by
  have e : ∀ j k : LinstrR, hasArrIdx j = false → hasArrIdx k = false →
      runIB ((j :: k :: rest).map fun i => (i, tag i)) l
        = (lsemStraight [j, k] l).bind (runIB (rest.map fun i => (i, tag i))) := by
    intro j k hj hk
    simp only [List.map_cons, runIB, stepIB, inBoundsB_of_hasArrIdx hj,
      inBoundsB_of_hasArrIdx hk, if_true, lsemStraight_cons, lsemStraight_nil]
    cases lsemStep j l with
    | none => rfl
    | some l1 =>
        simp only [Option.bind_some]
        cases lsemStep k l1 <;> rfl
  rw [e i1 i2 (indep_arrIdx_left h) (indep_arrIdx_right h),
    e i2 i1 (indep_arrIdx_right h) (indep_arrIdx_left h), lsemStraight_swap i1 i2 [] l h]

/-- The schedule preserves the in-bounds run of a body tagged by a function of the wire. -/
theorem runIB_scheduleBody (tag : LinstrR → MemTag) (b : List Linstr) (l : Lstate 64) :
    runIB ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)) l
      = runIB (b.map fun i => (i.li_i, tag i.li_i)) l := by
  have := scheduleBody_run (run := fun l s => runIB (l.map fun i => (i, tag i)) s)
    (fun l1 l2 s => by simp only [List.map_append, runIB_append])
    (fun i1 i2 rest s hi => runIB_swap tag i1 i2 rest s hi) b l
  simpa [List.map_map, Function.comp_def] using this

/-- **Schedule soundness on the flag machine through the bridge.** For a fragment body whose
    in-bounds run succeeds, from a state related to `l`, the scheduled body and the input
    body run under `lsemStraightMemF` to states with the same register file, arrays and word
    memory. The conclusion of `OptBlocksMemF.scheduleBody_lsemStraightMemF` up to the carry
    and overflow flags, obtained from `LprogScheduler.scheduleBody_lsemStraight` by
    `lsemStraightMemF_transport`. -/
theorem scheduleBody_lsemStraightMemF_bridge {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragB A (i.li_i, tag i.li_i) = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRel A s l)
    (hib : (runIB (b.map fun i => (i.li_i, tag i.li_i)) l).isSome) :
    ∃ u u', lsemStraightMemF ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)) s = some u ∧
      lsemStraightMemF (b.map fun i => (i.li_i, tag i.li_i)) s = some u' ∧
      u.reg = u'.reg ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem := by
  have hB : ∀ i ∈ (scheduleBody b).map (fun i => (i.li_i, tag i.li_i)), fragB A i = true := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hfrag j ((scheduleBody_perm b).mem_iff.1 hj)
  have hB' : ∀ i ∈ b.map (fun i => (i.li_i, tag i.li_i)), fragB A i = true := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hfrag j hj
  have hst : lsemStraight (((scheduleBody b).map fun i => (i.li_i, tag i.li_i)).map Prod.fst) l
      = lsemStraight ((b.map fun i => (i.li_i, tag i.li_i)).map Prod.fst) l := by
    simpa [List.map_map, Function.comp_def] using scheduleBody_lsemStraight (w := 64) b l
  obtain ⟨u, u', hu, hu', hO, hA, hM⟩ := lsemStraightMemF_transport (O := fun _ => True)
    hB hB' hr (by rw [runIB_scheduleBody]; exact hib) hib
    (fun t t' ht ht' => by
      rw [hst, ht'] at ht
      cases ht
      exact ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩)
  refine ⟨u, u', hu, hu', lstateN_ext (funext fun r => hO r trivial) ?_, hA, hM⟩
  have h1 := lsemStraightMemF_lpc _ s u hu
  have h2 := lsemStraightMemF_lpc _ s u' hu'
  simp only [LstateM.lpc, List.length_map, scheduleBody_length] at h1 h2
  rw [h1, h2]

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
