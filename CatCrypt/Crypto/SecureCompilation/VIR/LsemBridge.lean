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
`n` words of `l.lmem` at the byte offsets `8 · k`, `k < n`. `LsemRel` does not relate the
flags, which `lsemStep` neither reads nor writes; `LsemRelF` is `LsemRel` with the flags
`cf`, `of` of the two states equal.

`lsemStepFlag` is `lsemStep` with the flags of the flag machine, built over `lsemStep` as
`stepMemF` is built over `lsemStepMem`. On the fragment `fragFB A` (the fragment `fragB A`,
the two-source carry family `ADC`, `SBB`, `ADCX`, `ADOX`, the two-source copy and the
widening multiply `MULX`), from states related by `LsemRelF` both `stepMemF` and
`lsemStepFlag` step, and the results are related by `LsemRelF`
(`lsemStepFlag_stepMemF_rel`).

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
* `lsemStepFlag`, `lsemStraightFlag`, `runIBF` — the uniform-width step with flags, its
  fold and its in-bounds run.
* `LsemRelF`, `ShapeF`, `shapeF?`, `fragFB` — the relation and the fragment with flags.

## Main results

* `lsemStep_stepMemF_rel` — the per-instruction simulation on the fragment.
* `lsemStraight_lsemStraightMemF_rel` — the simulation of a run.
* `lsemStraightMemF_transport`, `lsemFuelMemF_transport` — two fragment bodies whose
  `lsemStraight` runs agree on the observed names run under `stepMemF` (and under
  `lsemFuelMemF` in a singleton program) to states that agree on those names, on every
  array and on the word memory.
* `lsemStepFlag_stepMemF_rel`, `lsemStraightFlag_lsemStraightMemF_rel` — the
  per-instruction and the run simulation on the fragment with flags.
* `lsemStraightMemF_transportF`, `lsemFuelMemF_transportF` — transport on the fragment
  with flags, with the flags of each result those of the `lsemStraightFlag` run.
* `lsemStepFlag_lsemStep`, `lsemStraightFlag_of_lsemStraight` — where `lsemStep` steps,
  `lsemStepFlag` steps to the same state up to the flags.
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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast

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
      rw [ite_eq_left hb] at h
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

/-- **Per-instruction simulation of the memory step on a shape.** From related states, an
    in-bounds instruction of a shape steps under both `lsemStepMem` and `lsemStep`, the
    results are related, and the memory step keeps the word memory, every untracked array
    and the flags. -/
theorem lsemStep_lsemStepMem_rel_shape {A : String → Option Nat} (sh : Shape)
    (hok : sh.ok A = true) {s : LstateM} {l : Lstate 64} (hr : LsemRel A s l)
    (hb : inBoundsB l sh.toInstr = true) :
    ∃ s' l', lsemStepMem sh.toInstr s = some s' ∧ lsemStep sh.toInstr.1 l = some l' ∧
      LsemRel A s' l' ∧ s'.lmem = s.lmem ∧ (∀ b, A b = none → s'.larr b = s.larr b) ∧
      s'.cf = s.cf ∧ s'.of = s.of := by
  cases sh <;> simp only [Shape.toInstr] at hb ⊢
  case alu d m a b =>
      simp only [Shape.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hm, hb2⟩ := hok
      obtain ⟨hstrip, h1, h2, h3, h4, v, hN, hO⟩ := alu_facts hm (l.lvm a) (evalOperand l b)
      have hM := lsemStepMem_regArith3 d a b s m hstrip h1 h2 h3 h4 _ _ v (hr.getW a)
        (evalOperand_regOrImm hr hb2) hN
      refine ⟨_, (l.setReg d v).nextPc, hM, ?_, hr.setReg d v, rfl, fun _ _ => rfl, rfl, rfl⟩
      simp only [lsemStep, hstrip, List.map]
      rw [show evalOperand l (.reg a) = l.lvm a from rfl, hO]
  case movImm d k =>
      have hM := lsemStepMem_movImm d k s
      refine ⟨_, (l.setReg d (BitVec.ofNat 64 k)).nextPc, hM, ?_, hr.setReg d _, rfl,
        fun _ _ => rfl, rfl, rfl⟩
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
        simp only [lsemStepMem, loadStruct?, ite_eq_left, hr.getArr hok, hr.getW x, hg]
        rfl
      exact ⟨_, _, hM, lsemStep_loadidx d B x 8 l, hr.setReg d _, rfl, fun _ _ => rfl, rfl,
        rfl⟩
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
        simp only [lsemStepMem, storeStruct?, ite_eq_left, hr.getArr hok, hr.getW x, hr.getW v]
        rfl
      refine ⟨{ s with
              reg := s.reg.nextPc,
              larr := fun r => if r = B then
                ⟨64, n, stackSet (fun k : Fin n => l.lmem B (Int.ofNat (8 * k.val))) vi (l.lvm v)⟩
                else s.larr r }, _,
        hM, lsemStep_storeidx B B x 8 (.reg v) l,
        ⟨fun r => hr.regs r, by simp [hr.pc], fun B' n' hB' => ?_⟩, rfl, fun b hb' => ?_,
        rfl, rfl⟩
      · dsimp only
        by_cases hBB : B' = B
        · subst hBB
          rw [hok] at hB'
          cases hB'
          rw [ite_eq_left rfl]
          congr 2
          funext k
          cases n with
          | zero => exact absurd hb (by omega)
          | succ m =>
              simp only [stackSet, Nat.mod_eq_of_lt hb, evalOperand, ← hvi]
              rw [Lstate.lmem_nextPc]
              dsimp only
              rw [ite_eq_left rfl]
              by_cases hk : k = ⟨vi, hb⟩
              · subst hk; simp
              · have hk' : Int.ofNat (8 * k.val) ≠ Int.ofNat (8 * vi) := by
                  intro he
                  apply hk
                  ext
                  show k.val = vi
                  simp only [Int.ofNat_eq_natCast, Nat.cast_mul] at he
                  omega
                rw [ite_eq_right hk, ite_eq_right hk']
        · rw [ite_eq_right hBB, hr.arrs B' n' hB']
          simp [hBB]
      · have hbB : b ≠ B := by rintro rfl; rw [hok] at hb'; cases hb'
        simp [hbB]

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
  obtain ⟨b, l', hM, hL, hrel, hm, ha, -, -⟩ := lsemStep_lsemStepMem_rel_shape sh hok hr hb
  obtain ⟨c, o, hw⟩ := withALUFlags_eq sh.toInstr s b
  exact ⟨_, l', stepMemF_of_lsemStepMem hM, hL, by rw [hw]; exact hrel.setFlags c o,
    by rw [withALUFlags_lmem]; exact hm, fun x hx => by rw [withALUFlags_larr]; exact ha x hx⟩

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
      rw [ite_eq_left hb] at hib ⊢
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

/-- The instruction of a shape is a plain `Lopn`: neither a flag-`CMP` nor a register
    copy. -/
theorem Shape.toInstr_plain {A : String → Option Nat} (sh : Shape) (hok : sh.ok A = true) :
    IsLopn sh.toInstr ∧ cmpArgs? sh.toInstr = none ∧ movRegArgs? sh.toInstr = none := by
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

/-- A fragment instruction is a plain `Lopn`: neither a flag-`CMP` nor a register copy. -/
theorem fragB_plain {A : String → Option Nat} {i : LinstrRM} (hi : fragB A i = true) :
    IsLopn i ∧ cmpArgs? i = none ∧ movRegArgs? i = none := by
  obtain ⟨sh, rfl, hok⟩ := fragB_shape hi
  exact sh.toInstr_plain hok

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
      inBoundsB_of_hasArrIdx hk, ite_true, lsemStraight_cons, lsemStraight_nil]
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

/-! ## 8. The flag layer of the uniform-width step

`lsemStep` neither reads nor writes the flags `cf`, `of` of `Lstate`
(`JasminLsem.lsemStep_flags`). `lsemStepFlag` is `lsemStep` with the flags of the flag
machine, built over `lsemStep` as `stepMemF` is built over `lsemStepMem`: where `lsemStep`
steps, the flags of `withALUFlagsL`; otherwise a carry-family step `carryStepL`
(`carryArgs?`) or a flag-quiet lift step `wideStepL` (`wideArgs?`). -/

/-- The 64-bit value of a register or immediate operand; a memory operand has none. The
    counterpart of `evalOperandN · 64` on `Lstate 64`. -/
def evalRI (l : Lstate 64) : LOperand → Option (BitVec 64)
  | .reg r => some (l.lvm r)
  | .imm k => some (BitVec.ofNat 64 k)
  | .arr _ _ => none
  | .arrIdx _ _ _ => none

theorem LsemRel.evalRI {A : String → Option Nat} {s : LstateM} {l : Lstate 64}
    (h : LsemRel A s l) (o : LOperand) : evalOperandN s.reg 64 o = evalRI l o := by
  cases o with
  | reg r => exact h.getW r
  | imm k => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

section FlagStep

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- The flags an instruction writes onto its post-state `l1`, computed from its pre-state
    `l0`: the counterpart of `withALUFlags`. -/
def withALUFlagsL (i : LinstrRM) (l0 l1 : Lstate 64) : Lstate 64 :=
  match aluFlagOp? i with
  | some (op, a, b) =>
      match evalRI l0 a, evalRI l0 b with
      | some va, some vb =>
          { l1 with cf := (aluB5 op va vb).cf.getD false,
                    of := (aluB5 op va vb).of.getD false }
      | _, _ => l1
  | none => l1

/-- One carry-family step on `Lstate 64`: the counterpart of `carryStep`. -/
def carryStepL (op : CarryOp) (d : String) (a b : LOperand) (l : Lstate 64) :
    Option (Lstate 64) :=
  match evalRI l a, evalRI l b with
  | some va, some vb =>
      match op with
      | .adc =>
          some { (l.setReg d (x86_ADC va vb l.cf).word).nextPc with
                   cf := (x86_ADC va vb l.cf).cf.getD false,
                   of := (x86_ADC va vb l.cf).of.getD false }
      | .sbb =>
          some { (l.setReg d (x86_SBB va vb l.cf).word).nextPc with
                   cf := (x86_SBB va vb l.cf).cf.getD false,
                   of := (x86_SBB va vb l.cf).of.getD false }
      | .adcx =>
          some { (l.setReg d (x86_ADCX va vb l.cf).2).nextPc with
                   cf := (x86_ADCX va vb l.cf).1.getD false }
      | .adox =>
          some { (l.setReg d (x86_ADCX va vb l.of).2).nextPc with
                   of := (x86_ADCX va vb l.of).1.getD false }
  | _, _ => none

/-- One flag-quiet lift step on `Lstate 64`: the counterpart of `wideStep`. -/
def wideStepL (w : WideOp) (l : Lstate 64) : Option (Lstate 64) :=
  match w with
  | .mov d b =>
      match evalRI l b with
      | some v => some ((l.setReg d v).nextPc)
      | none => none
  | .mulx lo hi b =>
      match evalRI l b with
      | some y =>
          some (((l.setReg lo (x86_MULX_lo_hi (l.lvm mulxSrc) y).1).setReg hi
            (x86_MULX_lo_hi (l.lvm mulxSrc) y).2).nextPc)
      | none => none

/-- **The uniform-width step with flags**: `lsemStep` with the flags of `withALUFlagsL`; an
    instruction `lsemStep` does not step is a carry-family step, a flag-quiet lift step or
    stuck. The counterpart of `stepMemF`. -/
def lsemStepFlag (i : LinstrRM) (l : Lstate 64) : Option (Lstate 64) :=
  match lsemStep i.1 l with
  | some b => some (withALUFlagsL i l b)
  | none =>
      match carryArgs? i with
      | some (op, d, a, b) => carryStepL op d a b l
      | none =>
          match wideArgs? i with
          | some w => wideStepL w l
          | none => none

/-- Where `lsemStep` steps, `lsemStepFlag` is that step with the flags of
    `withALUFlagsL`. -/
theorem lsemStepFlag_of_lsemStep {i : LinstrRM} {l b : Lstate 64}
    (h : lsemStep i.1 l = some b) : lsemStepFlag i l = some (withALUFlagsL i l b) := by
  unfold lsemStepFlag; rw [h]

/-- On a carry-family instruction that `lsemStep` does not step, `lsemStepFlag` is
    `carryStepL`. -/
theorem lsemStepFlag_carry {i : LinstrRM} {l : Lstate 64} {op : CarryOp} {d : String}
    {a b : LOperand} (h : lsemStep i.1 l = none) (hc : carryArgs? i = some (op, d, a, b)) :
    lsemStepFlag i l = carryStepL op d a b l := by
  unfold lsemStepFlag; rw [h, hc]

/-- On a flag-quiet lift instruction that `lsemStep` does not step and that is not in the
    carry family, `lsemStepFlag` is `wideStepL`. -/
theorem lsemStepFlag_wide {i : LinstrRM} {l : Lstate 64} {w : WideOp}
    (h : lsemStep i.1 l = none) (hc : carryArgs? i = none) (hw : wideArgs? i = some w) :
    lsemStepFlag i l = wideStepL w l := by
  unfold lsemStepFlag; rw [h, hc, hw]

@[simp] theorem withALUFlagsL_lvm (i : LinstrRM) (l0 l1 : Lstate 64) :
    (withALUFlagsL i l0 l1).lvm = l1.lvm := by
  unfold withALUFlagsL; split
  · split <;> rfl
  · rfl

@[simp] theorem withALUFlagsL_lmem (i : LinstrRM) (l0 l1 : Lstate 64) :
    (withALUFlagsL i l0 l1).lmem = l1.lmem := by
  unfold withALUFlagsL; split
  · split <;> rfl
  · rfl

@[simp] theorem withALUFlagsL_lpc (i : LinstrRM) (l0 l1 : Lstate 64) :
    (withALUFlagsL i l0 l1).lpc = l1.lpc := by
  unfold withALUFlagsL; split
  · split <;> rfl
  · rfl

/-- `withALUFlagsL` changes at most the two flags. -/
theorem withALUFlagsL_eq (i : LinstrRM) (l0 l1 : Lstate 64) :
    ∃ c o, withALUFlagsL i l0 l1 = { l1 with cf := c, of := o } := by
  unfold withALUFlagsL; split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨l1.cf, l1.of, rfl⟩
  · exact ⟨l1.cf, l1.of, rfl⟩

/-- **Conservativity.** Where `lsemStep` steps, `lsemStepFlag` steps to the same state up
    to the flags. -/
theorem lsemStepFlag_lsemStep {i : LinstrRM} {l b : Lstate 64}
    (h : lsemStep i.1 l = some b) :
    ∃ c o, lsemStepFlag i l = some { b with cf := c, of := o } := by
  obtain ⟨c, o, hw⟩ := withALUFlagsL_eq i l b
  exact ⟨c, o, by rw [lsemStepFlag_of_lsemStep h, hw]⟩

/-! ### The relation with flags -/

/-- `LsemRel` with the carry and overflow flags related. -/
structure LsemRelF (A : String → Option Nat) (s : LstateM) (l : Lstate 64) : Prop
    extends LsemRel A s l where
  /-- The carry flags agree. -/
  cf : s.cf = l.cf
  /-- The overflow flags agree. -/
  of : s.of = l.of

/-- The flags `withALUFlags` and `withALUFlagsL` write agree from related pre-states. -/
theorem withALUFlags_rel {A : String → Option Nat} (i : LinstrRM) {s : LstateM}
    {l : Lstate 64} (hr : LsemRel A s l) {s1 : LstateM} {l1 : Lstate 64}
    (h1 : LsemRel A s1 l1) (hc : s1.cf = l1.cf) (ho : s1.of = l1.of) :
    LsemRelF A (withALUFlags i s s1) (withALUFlagsL i l l1) := by
  unfold withALUFlags withALUFlagsL
  cases aluFlagOp? i with
  | none => exact ⟨h1, hc, ho⟩
  | some q =>
      obtain ⟨op, a, b⟩ := q
      simp only [hr.evalRI]
      cases evalRI l a with
      | none => exact ⟨h1, hc, ho⟩
      | some va =>
          cases evalRI l b with
          | none => exact ⟨h1, hc, ho⟩
          | some vb => exact ⟨⟨h1.regs, h1.pc, h1.arrs⟩, rfl, rfl⟩

/-! ### The fragment with the carry family -/

/-- The base mnemonic of a carry-family operation. -/
def carryBase : CarryOp → String
  | .adc => "ADC"
  | .sbb => "SBB"
  | .adcx => "ADCX"
  | .adox => "ADOX"

/-- The instruction shapes of the fragment with flags: the shapes of `Shape`, the
    two-source carry family, the two-source copy and the widening multiply. -/
inductive ShapeF where
  /-- A shape of the flag-free fragment. -/
  | plain (sh : Shape)
  /-- `d := a op b` with the flag carry-in, at width `64`. -/
  | carry (op : CarryOp) (d a : String) (b : LOperand)
  /-- The two-source copy `MOV:64 [d] [x, b]`: `d := b`. -/
  | mov2 (d x : String) (b : LOperand)
  /-- The widening multiply `MULX:64 [lo, hi] [b]`: `(lo, hi) := RDX * b`. -/
  | mulx (lo hi : String) (b : LOperand)

/-- The tagged instruction of a shape. -/
def ShapeF.toInstr : ShapeF → LinstrRM
  | .plain sh => sh.toInstr
  | .carry op d a b =>
      (.Lopn [.reg d] (withWidthTag 64 (carryBase op)) [.reg a, b], .reg none)
  | .mov2 d x b => (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg x, b], .reg none)
  | .mulx lo hi b => (.Lopn [.reg lo, .reg hi] (withWidthTag 64 "MULX") [b], .reg none)

/-- The side conditions of a shape. -/
def ShapeF.ok (A : String → Option Nat) : ShapeF → Bool
  | .plain sh => sh.ok A
  | .carry _ _ _ b => regOrImm b
  | .mov2 _ _ b => regOrImm b
  | .mulx _ _ b => regOrImm b

/-- The shape recognizer of the fragment with flags. -/
def shapeF? : LinstrRM → Option ShapeF
  | (.Lopn [.reg d] opn [.reg a, b], .reg none) =>
      if opn = withWidthTag 64 "ADC" then some (.carry .adc d a b)
      else if opn = withWidthTag 64 "SBB" then some (.carry .sbb d a b)
      else if opn = withWidthTag 64 "ADCX" then some (.carry .adcx d a b)
      else if opn = withWidthTag 64 "ADOX" then some (.carry .adox d a b)
      else if opn = withWidthTag 64 "MOV" then some (.mov2 d a b)
      else (shape? (.Lopn [.reg d] opn [.reg a, b], .reg none)).map .plain
  | (.Lopn [.reg lo, .reg hi] opn [b], .reg none) =>
      if opn = withWidthTag 64 "MULX" then some (.mulx lo hi b) else none
  | i => (shape? i).map .plain

theorem shapeF?_toInstr {i : LinstrRM} {sh : ShapeF} (h : shapeF? i = some sh) :
    sh.toInstr = i := by
  unfold shapeF? at h
  split at h
  · split_ifs at h with h1 h2 h3 h4 h5
    · cases h; rw [h1]; rfl
    · cases h; rw [h2]; rfl
    · cases h; rw [h3]; rfl
    · cases h; rw [h4]; rfl
    · cases h; rw [h5]; rfl
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
      exact shape?_toInstr hp
  · split_ifs at h with h1
    cases h; rw [h1]; rfl
  · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
    exact shape?_toInstr hp

/-- **The fragment with flags**, a decidable predicate on tagged instructions. -/
def fragFB (A : String → Option Nat) (i : LinstrRM) : Bool :=
  match shapeF? i with
  | some sh => sh.ok A
  | none => false

theorem fragFB_shape {A : String → Option Nat} {i : LinstrRM} (h : fragFB A i = true) :
    ∃ sh : ShapeF, sh.toInstr = i ∧ sh.ok A = true := by
  unfold fragFB at h
  split at h
  · next sh hs => exact ⟨sh, shapeF?_toInstr hs, h⟩
  · exact absurd h (by simp)

/-- The recognizer accepts every carry-family instruction with a register or immediate
    second source. -/
theorem fragFB_carry (A : String → Option Nat) (op : CarryOp) (d a : String) {b : LOperand}
    (hb : regOrImm b = true) : fragFB A (ShapeF.toInstr (.carry op d a b)) = true := by
  cases op <;> simpa [fragFB, shapeF?, ShapeF.toInstr, ShapeF.ok, carryBase, withWidthTag]
    using hb

/-- The fragment with flags contains the flag-free fragment. -/
theorem fragFB_of_fragB {A : String → Option Nat} {i : LinstrRM} (hi : fragB A i = true) :
    fragFB A i = true := by
  unfold fragB at hi
  cases hs : shape? i with
  | none => rw [hs] at hi; exact absurd hi (by simp)
  | some sh =>
      rw [hs] at hi
      have key : shapeF? i = some (.plain sh) := by
        unfold shapeF?
        split
        · next d opn a b =>
          have hsh : sh = .alu d (stripWidthTag opn) a b := by
            simp only [shape?] at hs
            split_ifs at hs
            exact (Option.some.inj hs).symm
          subst hsh
          simp only [Shape.ok, Bool.and_eq_true, decide_eq_true_eq] at hi
          have hne : ∀ m, m ∉ aluBases → stripWidthTag (withWidthTag 64 m) = m →
              opn ≠ withWidthTag 64 m := by
            rintro m hm hst rfl
            rw [hst] at hi
            exact hm hi.1
          rw [ite_eq_right (hne "ADC" (by decide) (by decide +kernel)),
            ite_eq_right (hne "SBB" (by decide) (by decide +kernel)),
            ite_eq_right (hne "ADCX" (by decide) (by decide +kernel)),
            ite_eq_right (hne "ADOX" (by decide) (by decide +kernel)),
            ite_eq_right (hne "MOV" (by decide) (by decide +kernel)), hs]
          rfl
        · simp [shape?] at hs
        · rw [hs]; rfl
      unfold fragFB
      rw [key]
      exact hi

/-! ### The per-instruction simulation with flags -/

/-- The memory step does not step a two-source instruction whose base mnemonic neither
    `applyOpnN` nor the comparison arm models. -/
theorem lsemStepMem_two_none (dst a : String) (b : LOperand) (ls : LstateM) (base : String)
    (hstrip : stripWidthTag (withWidthTag 64 base) = base)
    (h1 : base ≠ "MULXHI") (h4 : base ≠ "SAR") (va vb : BitVec 64)
    (hva : ls.reg.getW a 64 = some va) (hvb : evalOperandN ls.reg 64 b = some vb)
    (hop : applyOpnN 64 base [va, vb] = none) (hc : cmpOfName? base = none) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b], .reg none) ls = none := by
  have hm : mulhiStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b]) = none := by
    cases b <;> simp only [mulhiStruct?, hstrip, ite_eq_right h1]
  have ha : adcxStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b]) = none := by
    cases b <;> rfl
  have hh : adcxhiStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b]) = none := by
    cases b <;> rfl
  have hs : sarStruct? (.Lopn [.reg dst] (withWidthTag 64 base) [.reg a, b]) = none := by
    cases b <;> simp only [sarStruct?, hstrip, ite_eq_right h4]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm ha hh (by cases b <;> rfl) (by cases b <;> rfl),
      lsemStepSh_of_not_sar _ _ hs]
  simp only [lsemStepN, readReg_of_getW hva, hvb, hstrip, hop, hc, Option.map_none]

theorem carry_facts (op : CarryOp) (x y : BitVec 64) :
    stripWidthTag (withWidthTag 64 (carryBase op)) = carryBase op ∧
      carryBase op ≠ "MULXHI" ∧ carryBase op ≠ "SAR" ∧
      applyOpnN 64 (carryBase op) [x, y] = none ∧
      applyOpn (carryBase op) [x, y] = none := by
  cases op <;> exact ⟨by decide +kernel, by decide, by decide, rfl, rfl⟩

theorem carryArgs?_carry (op : CarryOp) (d a : String) (b : LOperand) :
    carryArgs? (ShapeF.toInstr (.carry op d a b)) = some (op, d, .reg a, b) := by
  cases op <;> simp [ShapeF.toInstr, carryArgs?, carryBase, withWidthTag]

/-- **Per-instruction simulation on the fragment with flags.** From states related with
    their flags, an in-bounds fragment instruction steps under both `stepMemF` and
    `lsemStepFlag`, the results are related with their flags, the word memory of the flag
    machine is unchanged, and so is every untracked array. -/
theorem lsemStepFlag_stepMemF_rel {A : String → Option Nat} {i : LinstrRM}
    (hi : fragFB A i = true) {s : LstateM} {l : Lstate 64} (hr : LsemRelF A s l)
    (hb : inBoundsB l i = true) :
    ∃ s' l', stepMemF i s = some s' ∧ lsemStepFlag i l = some l' ∧ LsemRelF A s' l' ∧
      s'.lmem = s.lmem ∧ ∀ b, A b = none → s'.larr b = s.larr b := by
  obtain ⟨sh, rfl, hok⟩ := fragFB_shape hi
  clear hi
  cases sh with
  | plain sh =>
      obtain ⟨b, l', hM, hL, hrel, hm, ha, hcf, hof⟩ :=
        lsemStep_lsemStepMem_rel_shape sh hok hr.toLsemRel hb
      obtain ⟨hcl, hol⟩ := lsemStep_flags _ _ _ hL
      exact ⟨_, _, stepMemF_of_lsemStepMem hM, lsemStepFlag_of_lsemStep hL,
        withALUFlags_rel sh.toInstr hr.toLsemRel hrel (by rw [hcf, hcl, hr.cf])
          (by rw [hof, hol, hr.of]),
        by rw [withALUFlags_lmem]; exact hm, fun x hx => by rw [withALUFlags_larr]; exact ha x hx⟩
  | carry op d a b =>
      simp only [ShapeF.ok] at hok
      obtain ⟨hstrip, h1, h4, hN, hO⟩ := carry_facts op (l.lvm a) (evalOperand l b)
      have hvb : evalOperandN s.reg 64 b = some (evalOperand l b) :=
        evalOperand_regOrImm hr.toLsemRel hok
      have hM := lsemStepMem_two_none d a b s (carryBase op) hstrip h1 h4 _ _
        (hr.getW a) hvb hN (by cases op <;> rfl)
      have hL : lsemStep (ShapeF.toInstr (.carry op d a b)).1 l = none := by
        simp only [ShapeF.toInstr, lsemStep, hstrip, List.map]
        rw [show evalOperand l (.reg a) = l.lvm a from rfl, hO]
      have hS : stepMemF (ShapeF.toInstr (.carry op d a b)) s
          = carryStep op d (.reg a) b s := by
        unfold stepMemF
        rw [show lsemStepMem (ShapeF.toInstr (.carry op d a b)) s = none from hM]
        simp only [carryArgs?_carry]
      have hvb' : evalRI l b = some (evalOperand l b) := by
        rw [← hr.toLsemRel.evalRI, hvb]
      have hva : evalOperandN s.reg 64 (.reg a) = some (l.lvm a) := hr.getW a
      have hrs := fun v => hr.toLsemRel.setReg d v
      rw [hS, lsemStepFlag_carry hL (carryArgs?_carry op d a b)]
      simp only [carryStep, carryStepL, hva, hvb, hvb',
        show evalRI l (.reg a) = some (l.lvm a) from rfl, hr.cf, hr.of]
      cases op <;>
        exact ⟨_, _, rfl, rfl, ⟨⟨(hrs _).regs, (hrs 0).pc, (hrs 0).arrs⟩,
          by first | rfl | exact hr.cf, by first | rfl | exact hr.of⟩, rfl, fun _ _ => rfl⟩
  | mov2 d x b =>
      simp only [ShapeF.ok] at hok
      have hvb : evalOperandN s.reg 64 b = some (evalOperand l b) :=
        evalOperand_regOrImm hr.toLsemRel hok
      have hM := lsemStepMem_two_none d x b s "MOV"
        (JasminLsemScalar.stripWidthTag_withWidthTag_MOV 64) (by decide) (by decide) _ _
        (hr.getW x) hvb rfl rfl
      have hL : lsemStep (ShapeF.toInstr (.mov2 d x b)).1 l = none := by
        simp only [ShapeF.toInstr, lsemStep,
          JasminLsemScalar.stripWidthTag_withWidthTag_MOV, List.map]
        rfl
      have hc : carryArgs? (ShapeF.toInstr (.mov2 d x b)) = none := by
        simp [ShapeF.toInstr, carryArgs?, withWidthTag]
      have hw : wideArgs? (ShapeF.toInstr (.mov2 d x b)) = some (.mov d b) := by
        simp [ShapeF.toInstr, wideArgs?]
      have hS : stepMemF (ShapeF.toInstr (.mov2 d x b)) s = wideStep (.mov d b) s := by
        unfold stepMemF
        rw [show lsemStepMem (ShapeF.toInstr (.mov2 d x b)) s = none from hM]
        simp only [hc, hw]
      have hvb' : evalRI l b = some (evalOperand l b) := by
        rw [← hr.toLsemRel.evalRI, hvb]
      have hrs := hr.toLsemRel.setReg d (evalOperand l b)
      rw [hS, lsemStepFlag_wide hL hc hw]
      simp only [wideStep, wideStepL, hvb, hvb']
      exact ⟨_, _, rfl, rfl, ⟨⟨hrs.regs, hrs.pc, hrs.arrs⟩, hr.cf, hr.of⟩, rfl,
        fun _ _ => rfl⟩
  | mulx lo hi b =>
      simp only [ShapeF.ok] at hok
      have hvb : evalOperandN s.reg 64 b = some (evalOperand l b) :=
        evalOperand_regOrImm hr.toLsemRel hok
      have hM : lsemStepMem (ShapeF.toInstr (.mulx lo hi b)) s = none := by
        simp only [ShapeF.toInstr]
        rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl)]
        cases b <;> rfl
      have hL : lsemStep (ShapeF.toInstr (.mulx lo hi b)).1 l = none := rfl
      have hc : carryArgs? (ShapeF.toInstr (.mulx lo hi b)) = none := rfl
      have hw : wideArgs? (ShapeF.toInstr (.mulx lo hi b)) = some (.mulx lo hi b) := by
        simp [ShapeF.toInstr, wideArgs?]
      have hS : stepMemF (ShapeF.toInstr (.mulx lo hi b)) s = wideStep (.mulx lo hi b) s := by
        unfold stepMemF
        rw [hM]
        simp only [hc, hw]
      have hvb' : evalRI l b = some (evalOperand l b) := by
        rw [← hr.toLsemRel.evalRI, hvb]
      have hx : evalOperandN s.reg 64 (.reg mulxSrc) = some (l.lvm mulxSrc) := hr.getW _
      rw [hS, lsemStepFlag_wide hL hc hw]
      simp only [wideStep, wideStepL, hvb, hvb', hx]
      refine ⟨_, _, rfl, rfl, ⟨⟨fun r => ?_, by simp [hr.pc], fun B n hB => hr.arrs B n hB⟩,
        hr.cf, hr.of⟩, rfl, fun _ _ => rfl⟩
      by_cases h2 : r = hi
      · subst h2; simp [Lstate.setReg, LstateM.setReg, LstateM.nextPc]
      · by_cases h1 : r = lo
        · subst h1; simp [Lstate.setReg, LstateM.setReg, LstateM.nextPc, h2]
        · simp [Lstate.setReg, LstateM.setReg, LstateM.nextPc, h1, h2, hr.regs r]

/-! ### The simulation of a run with flags -/

/-- Straight-line execution with flags: the fold of `lsemStepFlag`. -/
def lsemStraightFlag : List LinstrRM → Lstate 64 → Option (Lstate 64)
  | [], l => some l
  | i :: is, l => (lsemStepFlag i l).bind (lsemStraightFlag is)

@[simp] theorem lsemStraightFlag_nil (l : Lstate 64) : lsemStraightFlag [] l = some l := rfl

theorem lsemStraightFlag_cons (i : LinstrRM) (is : List LinstrRM) (l : Lstate 64) :
    lsemStraightFlag (i :: is) l = (lsemStepFlag i l).bind (lsemStraightFlag is) := rfl

theorem lsemStraightFlag_append (l1 l2 : List LinstrRM) (l : Lstate 64) :
    lsemStraightFlag (l1 ++ l2) l = (lsemStraightFlag l1 l).bind (lsemStraightFlag l2) := by
  induction l1 generalizing l with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, lsemStraightFlag, ih, Option.bind_assoc]

/-- **Conservativity of a run.** Where `lsemStraight` runs a body, `lsemStraightFlag` runs
    it from the same state with any flags to the same state up to the flags. -/
theorem lsemStraightFlag_of_lsemStraight :
    ∀ (body : List LinstrRM) (l t : Lstate 64) (c o : Bool),
      lsemStraight (body.map Prod.fst) l = some t →
      ∃ c' o', lsemStraightFlag body { l with cf := c, of := o }
        = some { t with cf := c', of := o' } := by
  intro body
  induction body with
  | nil =>
      intro l t c o h
      simp only [List.map_nil, lsemStraight_nil, Option.some.injEq] at h
      subst h
      exact ⟨c, o, rfl⟩
  | cons i is ih =>
      intro l t c o h
      simp only [List.map_cons, lsemStraight_cons] at h
      cases hs : lsemStep i.1 l with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some l1 =>
          rw [hs] at h
          have h1 : lsemStep i.1 { l with cf := c, of := o }
              = some { l1 with cf := c, of := o } := by
            rw [lsemStep_setFlags, hs]; rfl
          obtain ⟨c1, o1, hw⟩ := lsemStepFlag_lsemStep h1
          obtain ⟨c', o', hr⟩ := ih l1 t c1 o1 h
          exact ⟨c', o', by rw [lsemStraightFlag_cons, hw, Option.bind_some]; exact hr⟩

/-- One step of `lsemStraightFlag` that fails at an out-of-bounds indexed access. -/
def stepIBF (i : LinstrRM) (l : Lstate 64) : Option (Lstate 64) :=
  if inBoundsB l i then lsemStepFlag i l else none

/-- The in-bounds run with flags: `lsemStraightFlag` failing at an out-of-bounds indexed
    access. -/
def runIBF : List LinstrRM → Lstate 64 → Option (Lstate 64)
  | [], l => some l
  | i :: is, l => (stepIBF i l).bind (runIBF is)

theorem runIBF_append (l1 l2 : List LinstrRM) (l : Lstate 64) :
    runIBF (l1 ++ l2) l = (runIBF l1 l).bind (runIBF l2) := by
  induction l1 generalizing l with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runIBF, ih, Option.bind_assoc]

/-- The in-bounds run with flags is `lsemStraightFlag` where it succeeds. -/
theorem runIBF_lsemStraightFlag :
    ∀ (body : List LinstrRM) (l t : Lstate 64),
      runIBF body l = some t → lsemStraightFlag body l = some t := by
  intro body
  induction body with
  | nil => intro l t h; simpa [runIBF] using h
  | cons i is ih =>
      intro l t h
      simp only [runIBF, stepIBF] at h
      by_cases hb : inBoundsB l i = true
      swap
      · simp [hb] at h
      rw [ite_eq_left hb] at h
      cases hs : lsemStepFlag i l with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some l1 =>
          rw [hs, Option.bind_some] at h
          rw [lsemStraightFlag_cons, hs, Option.bind_some]
          exact ih l1 t h

/-- **Run simulation on the fragment with flags.** From states related with their flags, a
    fragment body whose in-bounds run succeeds runs under `lsemStraightMemF` to a state
    related, with its flags, to the result of the in-bounds run; the word memory and every
    untracked array are unchanged. -/
theorem lsemStraightFlag_lsemStraightMemF_rel {A : String → Option Nat} :
    ∀ (body : List LinstrRM) (s : LstateM) (l : Lstate 64),
      (∀ i ∈ body, fragFB A i = true) → LsemRelF A s l → (runIBF body l).isSome →
      ∃ s' l', lsemStraightMemF body s = some s' ∧ runIBF body l = some l' ∧
        LsemRelF A s' l' ∧ s'.lmem = s.lmem ∧ ∀ b, A b = none → s'.larr b = s.larr b := by
  intro body
  induction body with
  | nil => intro s l _ hr _; exact ⟨s, l, rfl, rfl, hr, rfl, fun _ _ => rfl⟩
  | cons i is ih =>
      intro s l hf hr hib
      simp only [runIBF, stepIBF] at hib ⊢
      by_cases hb : inBoundsB l i = true
      swap
      · simp [hb] at hib
      rw [ite_eq_left hb] at hib ⊢
      obtain ⟨s1, l1, hs1, hl1, hr1, hm1, ha1⟩ :=
        lsemStepFlag_stepMemF_rel (hf i List.mem_cons_self) hr hb
      rw [hl1, Option.bind_some] at hib ⊢
      obtain ⟨s2, l2, hs2, hl2, hr2, hm2, ha2⟩ :=
        ih s1 l1 (fun j hj => hf j (List.mem_cons_of_mem i hj)) hr1 hib
      refine ⟨s2, l2, ?_, hl2, hr2, hm2.trans hm1, fun b hb' => (ha2 b hb').trans (ha1 b hb')⟩
      rw [lsemStraightMemF_cons, hs1, Option.bind_some, hs2]

/-- **Transport with flags.** Let `B` and `B'` be bodies of the fragment with flags whose
    in-bounds runs from `l` succeed and whose `lsemStraightFlag` runs from `l` agree on the
    observed registers `O` and on the tracked arrays. From a state related to `l` with its
    flags, both run under `lsemStraightMemF`, and the results agree on the registers `O`,
    on every array and on the word memory; the flags of each result are those of the
    corresponding `lsemStraightFlag` run. -/
theorem lsemStraightMemF_transportF {A : String → Option Nat} {O : String → Prop}
    {B B' : List LinstrRM} (hB : ∀ i ∈ B, fragFB A i = true)
    (hB' : ∀ i ∈ B', fragFB A i = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRelF A s l)
    (hib : (runIBF B l).isSome) (hib' : (runIBF B' l).isSome)
    (hpass : ∀ t t', lsemStraightFlag B l = some t →
      lsemStraightFlag B' l = some t' → ObsAgree O A t t') :
    ∃ u u' t t', lsemStraightMemF B s = some u ∧ lsemStraightMemF B' s = some u' ∧
      lsemStraightFlag B l = some t ∧ lsemStraightFlag B' l = some t' ∧
      (∀ r, O r → u.reg.lvm r = u'.reg.lvm r) ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem ∧
      u.cf = t.cf ∧ u.of = t.of ∧ u'.cf = t'.cf ∧ u'.of = t'.of := by
  obtain ⟨u, t, hu, ht, hrt, hmu, hau⟩ := lsemStraightFlag_lsemStraightMemF_rel B s l hB hr hib
  obtain ⟨u', t', hu', ht', hrt', hmu', hau'⟩ :=
    lsemStraightFlag_lsemStraightMemF_rel B' s l hB' hr hib'
  have hst := runIBF_lsemStraightFlag B l t ht
  have hst' := runIBF_lsemStraightFlag B' l t' ht'
  obtain ⟨hO, hA⟩ := hpass t t' hst hst'
  refine ⟨u, u', t, t', hu, hu', hst, hst',
    fun r hr' => by rw [hrt.regs, hrt'.regs, hO r hr'], ?_,
    hmu.trans hmu'.symm, hrt.cf, hrt.of, hrt'.cf, hrt'.of⟩
  funext b
  cases hb : A b with
  | none => rw [hau b hb, hau' b hb]
  | some n =>
      rw [hrt.arrs b n hb, hrt'.arrs b n hb]
      congr 2
      funext k
      exact hA b n hb k.val k.isLt

/-- An instruction of the fragment with flags is a plain `Lopn`: neither a flag-`CMP` nor
    a register copy. -/
theorem fragFB_plain {A : String → Option Nat} {i : LinstrRM} (hi : fragFB A i = true) :
    IsLopn i ∧ cmpArgs? i = none ∧ movRegArgs? i = none := by
  obtain ⟨sh, rfl, hok⟩ := fragFB_shape hi
  cases sh with
  | plain sh => exact sh.toInstr_plain hok
  | carry op d a b =>
      refine ⟨⟨_, _, _, rfl⟩, ?_, rfl⟩
      cases op <;> simp [ShapeF.toInstr, cmpArgs?, carryBase, withWidthTag]
  | mov2 d x b =>
      exact ⟨⟨_, _, _, rfl⟩, by simp [ShapeF.toInstr, cmpArgs?, withWidthTag], rfl⟩
  | mulx lo hi b => exact ⟨⟨_, _, _, rfl⟩, rfl, rfl⟩

/-- A body of the fragment with flags run by `lsemFuelMemF` as a singleton program from pc
    `0`, with fuel its length, is the run of `lsemStraightMemF`. -/
theorem lsemFuelMemF_of_fragF {A : String → Option Nat} {body : List LinstrRM}
    (hB : ∀ i ∈ body, fragFB A i = true) (fn : String) (zf : Bool) {s u : LstateM}
    (hpc : s.reg.lpc = 0) (hu : lsemStraightMemF body s = some u) :
    lsemFuelMemF (singletonProgM fn body) body.length { prog := { base := s, lfn := fn }, zf := zf }
      = some { prog := { base := u, lfn := fn }, zf := zf } := by
  have hseg := lsemFuelMemF_seg (singletonProgM fn body) fn rfl body s zf 0
    (fun i hi => fragFB_plain (hB i hi))
    (fun k _ => by simp [singletonProgM, LstateM.lpc, hpc])
  rw [Nat.add_zero] at hseg
  rw [hseg, hu, Option.bind_some]
  apply lsemFuelMemF_halt
  rw [findInstrMem_singleton fn body _ rfl]
  have := lsemStraightMemF_lpc body s u hu
  simp only [LstateM.lpc, hpc, Nat.zero_add] at this
  simp [LstateM.lpc, this]

/-- **Transport with flags to the fuel machine.** Under the hypotheses of
    `lsemStraightMemF_transportF` and from pc `0`, the singleton programs of `B` and `B'`
    run under `lsemFuelMemF` with fuel their lengths to halted states whose bases agree on
    the registers `O`, on every array and on the word memory, and carry the flags of the
    corresponding `lsemStraightFlag` runs; the zero flag and the function name are
    unchanged. -/
theorem lsemFuelMemF_transportF {A : String → Option Nat} {O : String → Prop}
    {B B' : List LinstrRM} (hB : ∀ i ∈ B, fragFB A i = true)
    (hB' : ∀ i ∈ B', fragFB A i = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRelF A s l)
    (hib : (runIBF B l).isSome) (hib' : (runIBF B' l).isSome)
    (hpass : ∀ t t', lsemStraightFlag B l = some t →
      lsemStraightFlag B' l = some t' → ObsAgree O A t t')
    (fn : String) (zf : Bool) (hpc : s.reg.lpc = 0) :
    ∃ u u' t t',
      lsemFuelMemF (singletonProgM fn B) B.length { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := u, lfn := fn }, zf := zf } ∧
      lsemFuelMemF (singletonProgM fn B') B'.length { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := u', lfn := fn }, zf := zf } ∧
      lsemStraightFlag B l = some t ∧ lsemStraightFlag B' l = some t' ∧
      (∀ r, O r → u.reg.lvm r = u'.reg.lvm r) ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem ∧
      u.cf = t.cf ∧ u.of = t.of ∧ u'.cf = t'.cf ∧ u'.of = t'.of := by
  obtain ⟨u, u', t, t', hu, hu', ht, ht', hrest⟩ :=
    lsemStraightMemF_transportF hB hB' hr hib hib' hpass
  exact ⟨u, u', t, t', lsemFuelMemF_of_fragF hB fn zf hpc hu,
    lsemFuelMemF_of_fragF hB' fn zf hpc hu', ht, ht', hrest⟩

end FlagStep

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
