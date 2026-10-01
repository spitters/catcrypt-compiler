/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

@[expose] public section

set_option autoImplicit false

/-!
# A checked single-loop node with word-array memory, from the System V entry

`DecodeGenMem.decSim_of_loopOK_idx` simulates one trip of a checked loop body from a loop
head related by `MCorr`, under the separation `MemSep` of the regions and with the index
register below the bound. This module derives those hypotheses once for a whole node and
composes the node with `DecodedLsemLoop.decNode_halts`.

## The prologue

`prun` runs the machine prologue symbolically: every register holds the entry value of a
register or a constant (`SVal`), or is unknown; the stack pointer is the entry stack
pointer plus a tracked offset; the stack words the prologue writes are recorded at their
offsets from the entry stack pointer, and a store is accepted only at an offset inside the
frame range `[lo, hi]`. `frun` runs the flag-machine seeds symbolically from the names that
hold the entry value of their System V register (`abi`). `preOK` compares the two at the
loop head: every live name and the machine register of it hold the same symbolic value,
the frame slot of every region holds the entry value of the region's register, the index
register holds `0`, and the counter holds a value below the index bound. `decSim_pre` is
the resulting simulation from the entry correspondence `NodeEntry` to `MCorr` with no
machine facts.

## The loop and the node

`decNodeMem_halts` composes the prologue, the guard, the trips of an accepted loop body
(`loopOK`) whose decoded body decrements the counter register once and increments the index
register once, and an epilogue that writes no memory: the machine halts on the decoded node,
the flag machine halts, and each word of each region is read in the final machine memory at
its layout address as the flag machine's array holds it.

## The System V layout

`abiArgOf σ A` is the parameter of `σ` named by the array or register name `A`
(`argName j` for parameter `j`). `rsOK σ rs` checks that each region is an array parameter
of its length, below `2 ^ 61` words, with pairwise distinct registers. From
`AbiLayout.Regions`, `memSep_of_regions` derives `MemSep` and `frameSep_of_regions` the
separation of the cells from the frame words.

## Main results

* `prun_sound`: the symbolic prologue describes the machine state it runs to.
* `frun_sound`: the symbolic seeds describe the flag-machine state they run to.
* `decSim_pre`: an accepted prologue simulates the seeds from `NodeEntry` to `MCorr`.
* `FrameNames`, `frameRes`, `decSim_pre_fr`: names held in frame words at the loop head, the
  prologue check that records them, and the prologue simulation that establishes them.
* `decSim_cmp_mcorr_fr`, `decNodeMem_halts_fr`: the node on both machines with the loop
  invariant extended by the names held in frame words, from a simulation of the loop body.
* `decNodeMem_halts`: the node on both machines, from `NodeEntry`, under `MemSep`, the frame
  separation and the counter bound.
* `memSep_of_regions`, `frameSep_of_regions`, `ctrBound_of_regions`: the per-trip
  hypotheses from `AbiLayout.Regions`.
* `decNodeAbi_halts`: the node from the System V entry state, with no separation hypothesis.
* `result_of_cells`, `decNodeAbi_result`: the decoded bytes of a node halt in a state whose
  result read-back (`AbiLayout.ResultOf`) is the flag machine's output array.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop XLoop.cmpInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
  (nodeLayout decNode_halts evalInstrA_loadMem_regs')
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim
  (decrOnce runBlock_regs_of_decrOnce runBlock_regs_of_not_dsts evalInstrA_cmp0 ofNat_sub_one
    ofNat_eq_zero_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem

/-! ## 1. Symbolic words -/

/-- A symbolic machine word: the entry value of a register, or a constant. -/
inductive SVal where
  /-- The value of the register at the entry state. -/
  | ent (R : String)
  /-- The constant word `n`. -/
  | imm (n : Nat)
  deriving DecidableEq, Repr

/-- The word a symbolic value denotes at the entry state `sa0`. -/
def SVal.den (sa0 : AState) : SVal → BitVec 64
  | .ent R => sa0.regs R
  | .imm n => BitVec.ofNat 64 n

/-- The value of `r` in a list of writes, latest first, falling back to `dflt`. -/
def getV (dflt : String → Option SVal) : List (String × Option SVal) → String → Option SVal
  | [], r => dflt r
  | (x, v) :: t, r => if x = r then v else getV dflt t r

theorem getV_cons (dflt : String → Option SVal) (x r : String) (v : Option SVal)
    (t : List (String × Option SVal)) :
    getV dflt ((x, v) :: t) r = if x = r then v else getV dflt t r := rfl

/-- The recorded value of the stack word at the offset `o`. -/
def stkGet : List (Int × SVal) → Int → Option SVal
  | [], _ => none
  | (o, v) :: t, o' => if o = o' then some v else stkGet t o'

theorem stkGet_mem : ∀ (t : List (Int × SVal)) (o : Int) (v : SVal), stkGet t o = some v →
    (o, v) ∈ t
  | [], _, _, h => by simp [stkGet] at h
  | (o', v') :: t, o, v, h => by
    simp only [stkGet] at h
    split at h
    · rename_i he
      obtain rfl := Option.some.inj h
      subst he
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (stkGet_mem t o v h)

/-- The recorded stack words that a store at the offset `o` does not overlap. -/
def stkDrop (o : Int) (t : List (Int × SVal)) : List (Int × SVal) :=
  t.filter (fun e => decide (8 ≤ (o - e.1).natAbs) && decide ((o - e.1).natAbs ≤ 2 ^ 64 - 8))

/-! ## 2. The symbolic prologue -/

/-- The symbolic machine state of a prologue: the register writes, latest first (`none`
    for an unknown value); the stack words written, at their offsets from the entry stack
    pointer; and the offset of the stack pointer from its entry value. -/
structure PSt where
  /-- The register writes, latest first. -/
  regs : List (String × Option SVal)
  /-- The stack words written, at offsets from the entry stack pointer. -/
  stk : List (Int × SVal)
  /-- The offset of the stack pointer from its entry value. -/
  sp : Int
  deriving Repr

/-- The entry state: no writes, the stack pointer at its entry value. -/
def PSt.init : PSt := ⟨[], [], 0⟩

/-- The symbolic value of the register `r`: its last write, or its entry value. -/
def PSt.get (p : PSt) (r : String) : Option SVal := getV (fun r => some (.ent r)) p.regs r

/-- **One prologue instruction.** The frame `lea` of the stack pointer; a register store to
    a stack word inside the frame range `[lo, hi]`; a load of a stack word; a register copy
    and an immediate move to a register other than the stack pointer. -/
def pstep (lo hi : Int) (p : PSt) : JInstr 64 → Option PSt
  | .lea D B _ sc off =>
      if D = "%rsp" ∧ B = "%rsp" ∧ sc = 0 then
        some { p with regs := ("%rsp", none) :: p.regs, sp := p.sp + off }
      else none
  | .storeMem B off (.reg Y) =>
      if B = "%rsp" ∧ lo ≤ p.sp + off ∧ p.sp + off ≤ hi then
        some { p with stk := match p.get Y with
          | some v => (p.sp + off, v) :: stkDrop (p.sp + off) p.stk
          | none => stkDrop (p.sp + off) p.stk }
      else none
  | .loadMem D B off =>
      if B = "%rsp" ∧ D ≠ "%rsp" then
        some { p with regs := (D, stkGet p.stk (p.sp + off)) :: p.regs }
      else none
  | .mov D (.reg Y) =>
      if D ≠ "%rsp" then some { p with regs := (D, p.get Y) :: p.regs } else none
  | .mov D (.imm n) =>
      if D ≠ "%rsp" then some { p with regs := (D, some (.imm n)) :: p.regs } else none
  | _ => none

/-- The symbolic run of a machine block. -/
def prun (lo hi : Int) : PSt → List (JInstr 64) → Option PSt
  | p, [] => some p
  | p, j :: js => (pstep lo hi p j).bind fun p' => prun lo hi p' js

/-- The symbolic state `p` describes the machine state `sa`, from the entry state `sa0`:
    the stack pointer is at its offset, every known register holds its value, every recorded
    stack word holds its value, and every word disjoint from the frame words `[lo, hi]` holds
    its entry value. -/
structure PInv (lo hi : Int) (sa0 : AState) (p : PSt) (sa : AState) : Prop where
  sp : sa.regs "%rsp" = sa0.regs "%rsp" + BitVec.ofInt 64 p.sp
  regs : ∀ r v, p.get r = some v → sa.regs r = v.den sa0
  stk : ∀ e ∈ p.stk, read64 sa.mem (sa0.regs "%rsp" + BitVec.ofInt 64 e.1) = e.2.den sa0
  mem : ∀ a, (∀ o : Int, lo ≤ o → o ≤ hi → Disjoint8 (sa0.regs "%rsp" + BitVec.ofInt 64 o) a) →
    read64 sa.mem a = read64 sa0.mem a

theorem pInv_init (lo hi : Int) (sa0 : AState) : PInv lo hi sa0 PSt.init sa0 where
  sp := by simp [PSt.init]
  regs r v h := by
    simp only [PSt.get, PSt.init, getV, Option.some.injEq] at h
    subst h; rfl
  stk e he := by simp [PSt.init] at he
  mem _ _ := rfl

/-- The register write of a prologue instruction keeps the invariant. -/
theorem pInv_write {lo hi : Int} {sa0 : AState} {p : PSt} {sa sa' : AState} (D : String)
    (v : Option SVal) (x : BitVec 64) (hD : D ≠ "%rsp")
    (hr : ∀ r, sa'.regs r = if r = D then x else sa.regs r) (hm : sa'.mem = sa.mem)
    (hv : ∀ w, v = some w → x = w.den sa0) (h : PInv lo hi sa0 p sa) :
    PInv lo hi sa0 { p with regs := (D, v) :: p.regs } sa' where
  sp := by rw [hr, if_neg (Ne.symm hD)]; exact h.sp
  regs r w hw := by
    simp only [PSt.get, getV_cons] at hw
    rw [hr]
    split at hw
    · rename_i he; subst he; rw [if_pos rfl]; exact hv w hw
    · rename_i he; rw [if_neg (Ne.symm he)]; exact h.regs r w hw
  stk e he := by rw [hm]; exact h.stk e he
  mem a ha := by rw [hm]; exact h.mem a ha

/-- **One prologue instruction is sound.** -/
theorem pstep_sound {lo hi : Int} {sa0 : AState} {p p' : PSt} {j : JInstr 64}
    (hs : pstep lo hi p j = some p') {sa : AState} (h : PInv lo hi sa0 p sa) :
    PInv lo hi sa0 p' (evalInstrA sa j) := by
  unfold pstep at hs
  split at hs
  · -- lea
    rename_i D B I sc off
    split at hs
    · rename_i hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain rfl := Option.some.inj hs
      have hr : ∀ r, (evalInstrA sa (.lea "%rsp" "%rsp" I 0 off)).regs r
          = if r = "%rsp" then sa.regs "%rsp" + sa.regs I * BitVec.ofNat 64 0
            + BitVec.ofInt 64 off else sa.regs r := fun _ => rfl
      refine ⟨?_, fun r w hw => ?_, fun e he => h.stk e he, fun a ha => h.mem a ha⟩
      · rw [hr, if_pos rfl, h.sp, BitVec.ofInt_add]
        simp [BitVec.add_assoc]
      · simp only [PSt.get, getV_cons] at hw
        split at hw
        · exact absurd hw (by simp)
        · rename_i he
          rw [hr, if_neg (Ne.symm he)]; exact h.regs r w hw
    · exact absurd hs (by simp)
  · -- store
    rename_i B off Y
    split at hs
    · rename_i hc
      obtain ⟨rfl, hlo, hhi⟩ := hc
      obtain rfl := Option.some.inj hs
      have hr : (evalInstrA sa (.storeMem "%rsp" off (.reg Y))).regs = sa.regs := rfl
      have hm : (evalInstrA sa (.storeMem "%rsp" off (.reg Y))).mem
          = write64 sa.mem (sa0.regs "%rsp" + BitVec.ofInt 64 (p.sp + off)) (sa.regs Y) := by
        show write64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 off) (sa.regs Y) = _
        rw [h.sp, BitVec.ofInt_add, BitVec.add_assoc]
      have hdrop : ∀ e ∈ stkDrop (p.sp + off) p.stk,
          read64 (write64 sa.mem (sa0.regs "%rsp" + BitVec.ofInt 64 (p.sp + off)) (sa.regs Y))
            (sa0.regs "%rsp" + BitVec.ofInt 64 e.1) = e.2.den sa0 := by
        intro e he
        simp only [stkDrop, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
        rw [read64_write64_of_disjoint _ _ _ _
          (disjoint8_add_ofInt _ _ _ he.2.1 he.2.2)]
        exact h.stk e he.1
      refine ⟨by rw [hr]; exact h.sp, fun r w hw => by rw [hr]; exact h.regs r w hw,
        fun e he => ?_, fun a ha => ?_⟩
      · rw [hm]
        simp only at he
        split at he
        · rename_i v hv
          rcases List.mem_cons.mp he with rfl | he
          · rw [read64_write64_same]; exact h.regs Y v hv
          · exact hdrop e he
        · exact hdrop e he
      · rw [hm, read64_write64_of_disjoint _ _ _ _ (ha _ hlo hhi)]
        exact h.mem a ha
    · exact absurd hs (by simp)
  · -- load
    rename_i D B off
    split at hs
    · rename_i hc
      obtain ⟨rfl, hD⟩ := hc
      obtain rfl := Option.some.inj hs
      refine pInv_write D _ _ hD (fun r => evalInstrA_loadMem_regs' sa D "%rsp" off r) rfl
        (fun w hw => ?_) h
      obtain he := stkGet_mem _ _ _ hw
      rw [h.sp, BitVec.add_assoc, ← BitVec.ofInt_add]
      exact h.stk (p.sp + off, w) he
    · exact absurd hs (by simp)
  · -- register copy
    rename_i D Y
    split at hs
    · rename_i hD
      obtain rfl := Option.some.inj hs
      exact pInv_write D _ (sa.regs Y) hD (fun _ => rfl) rfl (fun w hw => h.regs Y w hw) h
    · exact absurd hs (by simp)
  · -- immediate move
    rename_i D n
    split at hs
    · rename_i hD
      obtain rfl := Option.some.inj hs
      exact pInv_write D _ (BitVec.ofNat 64 n) hD (fun _ => rfl) rfl
        (fun w hw => by obtain rfl := Option.some.inj hw; rfl) h
    · exact absurd hs (by simp)
  · exact absurd hs (by simp)

/-- **The symbolic prologue is sound.** -/
theorem prun_sound {lo hi : Int} {sa0 : AState} :
    ∀ (js : List (JInstr 64)) (p p' : PSt) (sa : AState), prun lo hi p js = some p' →
      PInv lo hi sa0 p sa → PInv lo hi sa0 p' (aMachine.runBlock sa js) := by
  intro js
  induction js with
  | nil => intro p p' sa hs h; obtain rfl := Option.some.inj hs; exact h
  | cons j js ih =>
    intro p p' sa hs h
    obtain ⟨p1, h1, h2⟩ := Option.bind_eq_some_iff.mp hs
    rw [Machine.runBlock_cons, aMachine_exec]
    exact ih p1 p' _ h2 (pstep_sound h1 h)

/-! ## 3. The symbolic seeds -/

/-- The symbolic value of a name at the entry: the entry value of its System V register. -/
def fdflt (abi : String → Option String) (r : String) : Option SVal := (abi r).map SVal.ent

/-- **One seed on the flag machine.** The register copy and the immediate move at width
    `64`, from a name with a known value. -/
def fstep (dflt : String → Option SVal) (t : List (String × Option SVal)) :
    LinstrRM → Option (List (String × Option SVal))
  | (.Lopn [.reg d] opn [.reg a], .reg none) =>
      if opn = "MOV:64" then (getV dflt t a).map fun v => (d, some v) :: t else none
  | (.Lopn [.reg d] opn [.imm n], .reg none) =>
      if opn = "MOV:64" then some ((d, some (.imm n)) :: t) else none
  | _ => none

/-- The symbolic run of the seeds. -/
def frun (dflt : String → Option SVal) :
    List (String × Option SVal) → List LinstrRM → Option (List (String × Option SVal))
  | t, [] => some t
  | t, i :: is => (fstep dflt t i).bind fun t' => frun dflt t' is

/-- The symbolic writes `t` describe the flag-machine registers of `b`. -/
def FInv (sa0 : AState) (dflt : String → Option SVal) (t : List (String × Option SVal))
    (b : LstateM) : Prop :=
  ∀ r v, getV dflt t r = some v → b.reg.getW r 64 = some (v.den sa0)

theorem fInv_set {sa0 : AState} {dflt : String → Option SVal} {t : List (String × Option SVal)}
    {b : LstateM} (h : FInv sa0 dflt t b) (d : String) (v : SVal) :
    FInv sa0 dflt ((d, some v) :: t) ((b.setReg d (v.den sa0)).nextPc) := by
  intro r w hw
  rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc]
  rw [getV_cons] at hw
  split at hw
  · rename_i he; subst he
    obtain rfl := Option.some.inj hw
    exact LstateN.getW_setReg_same _ _ _
  · rename_i he
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm he)]
    exact h r w hw

/-- **One seed is sound.** The flag machine's step succeeds, keeps the zero flag and the
    arrays, and ends in a state the new writes describe. -/
theorem fstep_sound {sa0 : AState} {dflt : String → Option SVal}
    {t t' : List (String × Option SVal)} {i : LinstrRM} (hs : fstep dflt t i = some t')
    {b : LstateM} (h : FInv sa0 dflt t b) (zf : Bool) :
    ∃ b', fstepF i b zf = some (b', zf) ∧ FInv sa0 dflt t' b'
      ∧ ∀ A n, b'.getArr A 64 n = b.getArr A 64 n := by
  unfold fstep at hs
  split at hs
  · rename_i d opn a
    split at hs
    · rename_i ho
      subst ho
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact ⟨_, fstepF_movRI d a b zf _ (h a v hv), fInv_set h d v, fun _ _ => by simp⟩
    · exact absurd hs (by simp)
  · rename_i d opn n
    split at hs
    · rename_i ho
      subst ho
      obtain rfl := Option.some.inj hs
      exact ⟨_, fstepF_movII d n b zf, fInv_set h d (.imm n), fun _ _ => by simp⟩
    · exact absurd hs (by simp)
  · exact absurd hs (by simp)

/-- **The symbolic seeds are sound.** -/
theorem frun_sound {sa0 : AState} {dflt : String → Option SVal} :
    ∀ (is : List LinstrRM) (t t' : List (String × Option SVal)) (b : LstateM) (zf : Bool),
      frun dflt t is = some t' → FInv sa0 dflt t b →
      ∃ b', runStraightF is b zf = some (b', zf) ∧ FInv sa0 dflt t' b'
        ∧ ∀ A n, b'.getArr A 64 n = b.getArr A 64 n := by
  intro is
  induction is with
  | nil => intro t t' b zf hs h; obtain rfl := Option.some.inj hs; exact ⟨b, rfl, h, fun _ _ => rfl⟩
  | cons i is ih =>
    intro t t' b zf hs h
    obtain ⟨t1, h1, h2⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨b1, hr1, hi1, ha1⟩ := fstep_sound h1 h zf
    obtain ⟨b2, hr2, hi2, ha2⟩ := ih t1 t' b1 zf h2 hi1
    refine ⟨b2, ?_, hi2, fun A n => by rw [ha2, ha1]⟩
    rw [runStraightF_cons, hr1, Option.bind_some]
    exact hr2

/-! ## 4. The entry and the prologue check -/

/-- The base map of the regions at the entry state `sa`: the entry value of the System V
    register of each name. -/
def abiBase (abi : String → Option String) (sa : AState) (A : String) : BitVec 64 :=
  match abi A with
  | some R => sa.regs R
  | none => 0

/-- **The entry correspondence.** Each name with a System V register reads the entry value
    of that register, and each word of each region sits at its layout address from the
    entry value of the region's register. -/
structure NodeEntry (abi : String → Option String) (rs : List Region) (sa : AState)
    (b : LstateM) : Prop where
  /-- A name with a System V register reads its entry value. -/
  regs : ∀ r R, abi r = some R → b.reg.getW r 64 = some (sa.regs R)
  /-- The words of the regions at their layout addresses. -/
  cells : ∀ A j, regK rs A j → ∃ arr : Fin (regLen rs A) → BitVec 64,
    b.getArr A 64 (regLen rs A) = some arr
      ∧ read64 sa.mem ((regLay rs (abiBase abi sa)).addr A j) = stackGet arr j

/-- The counter's symbolic value is at most the index bound `nb`: a constant at most `nb`,
    or the entry value of a register with a bound at most `nb`. -/
def ctrB (bounds : List (String × Nat)) (nb : Nat) : Option SVal → Bool
  | some (.ent R) => bounds.any (fun x => x.1 == R && decide (x.2 ≤ nb))
  | some (.imm n) => decide (n ≤ nb)
  | none => false

/-- **The prologue check.** The symbolic prologue and seeds agree at the loop head on every
    live name of `L0`; the frame slot of every region lies in `[lo, hi]` and holds the entry
    value of the region's register; the index register `R` holds `0`; the counter register
    is bounded by `ctrB`. Returns the symbolic machine state at the loop head. -/
def preRes (E : MemEnv) (abi : String → Option String) (bounds : List (String × Nat))
    (lo hi : Int) (L0 : List String) (ctr R : String) (seeds : List LinstrRM)
    (pre : List (JInstr 64)) : Option PSt :=
  match prun lo hi PSt.init pre, frun (fdflt abi) [] seeds with
  | some p, some t =>
      if L0.all (fun r => (getV (fdflt abi) t r).isSome
            && getV (fdflt abi) t r == p.get (E.pi r))
          && E.rs.all (fun g => decide (lo ≤ p.sp + g.off) && decide (p.sp + g.off ≤ hi)
            && (abi g.name).isSome && stkGet p.stk (p.sp + g.off) == (abi g.name).map SVal.ent)
          && p.get R == some (.imm 0)
          && ctrB bounds E.nb (p.get (E.pi ctr)) then some p
      else none
  | _, _ => none

theorem regFind_spec {rs : List Region} {A : String} {g : Region} (h : regFind rs A = some g) :
    g ∈ rs ∧ g.name = A :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem ctrB_sound {bounds : List (String × Nat)} {nb : Nat} {v : Option SVal} {sa0 : AState}
    (h : ctrB bounds nb v = true) (hb : ∀ x ∈ bounds, (sa0.regs x.1).toNat ≤ x.2) :
    ∃ w, v = some w ∧ (w.den sa0).toNat ≤ nb := by
  unfold ctrB at h
  split at h
  · rename_i R
    obtain ⟨x, hx, hc⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨rfl, hle⟩ := hc
    exact ⟨_, rfl, le_trans (hb x hx) hle⟩
  · rename_i n
    simp only [decide_eq_true_eq] at h
    refine ⟨_, rfl, ?_⟩
    show (BitVec.ofNat 64 n).toNat ≤ nb
    rw [BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) h
  · exact absurd h (by simp)

/-- **The prologue.** For an accepted prologue with loop-head state `p`, from the entry
    correspondence at the entry state `sa0`, whose region cells are disjoint from the frame
    words `[lo, hi]` and whose bounded registers are within their bounds, the seeds simulate
    the machine prologue to `MCorr` on the live names `L0` with no machine facts, at the
    stack pointer `sa0.regs "%rsp" + p.sp`, with the index register at `0` and the counter
    register at most the index bound. -/
theorem decSim_pre {E : MemEnv} {abi : String → Option String} {bounds : List (String × Nat)}
    {lo hi : Int} {L0 : List String} {ctr R : String} {seeds : List LinstrRM}
    {pre : List (JInstr 64)} {p : PSt} (hsp : E.sp = "%rsp")
    (hres : preRes E abi bounds lo hi L0 ctr R seeds pre = some p) (sa0 : AState)
    (hfr : ∀ A j, regK E.rs A j → ∀ o : Int, lo ≤ o → o ≤ hi →
      Disjoint8 (sa0.regs "%rsp" + BitVec.ofInt 64 o) ((regLay E.rs (abiBase abi sa0)).addr A j))
    (hb : ∀ x ∈ bounds, (sa0.regs x.1).toNat ≤ x.2) :
    DecSim (fun sa b _ => sa = sa0 ∧ NodeEntry abi E.rs sa b)
      (fun sa b zf => MCorr E (abiBase abi sa0) (sa0.regs "%rsp" + BitVec.ofInt 64 p.sp)
          (L0, Abs.empty) False sa b zf
        ∧ sa.regs R = 0 ∧ (sa.regs (E.pi ctr)).toNat ≤ E.nb)
      seeds pre := by
  unfold preRes at hres
  split at hres
  · rename_i p' t hp ht
    split at hres
    · rename_i hc
      obtain rfl := Option.some.inj hres
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
        Option.isSome_iff_exists] at hc
      obtain ⟨⟨⟨hL, hrs⟩, hR⟩, hctr⟩ := hc
      rintro sa b zf ⟨rfl, hent⟩
      have hpi := prun_sound pre _ _ sa hp (pInv_init lo hi sa)
      have hfi : FInv sa (fdflt abi) [] b := by
        intro r v hv
        simp only [getV, fdflt, Option.map_eq_some_iff] at hv
        obtain ⟨R', hR', rfl⟩ := hv
        exact hent.regs r R' hR'
      obtain ⟨b', hrun, hfi', harr⟩ := frun_sound seeds [] t b zf ht hfi
      refine ⟨b', zf, hrun, ⟨⟨fun r hr => ?_, fun hz => hz.elim, fun A j hk => ?_,
        fun A q hq => ?_⟩, ?_, Abs.holds_empty _ _ _⟩, ?_, ?_⟩
      · obtain ⟨⟨v, hv⟩, he⟩ := hL r hr
        rw [hfi' r v hv, hpi.regs (E.pi r) v (he ▸ hv)]
      · obtain ⟨arr, ha, hc⟩ := hent.cells A j hk
        exact ⟨hk, arr, by rw [harr]; exact ha, by rw [hpi.mem _ (hfr A j hk)]; exact hc⟩
      · have hq' : (regFind E.rs A).isSome = true ∧ A = q := by
          simp only [regLay] at hq
          split at hq
          · rename_i hs; exact ⟨hs, Option.some.inj hq⟩
          · exact absurd hq (by simp)
        obtain ⟨hs, rfl⟩ := hq'
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨hgm, hgn⟩ := regFind_spec hg
        obtain ⟨⟨⟨_, _⟩, ⟨R', hR'⟩⟩, hst⟩ := hrs g hgm
        rw [hR'] at hst
        refine ⟨sa.regs "%rsp" + BitVec.ofInt 64 (p'.sp + g.off), ?_, ?_⟩
        · simp [regFrame, hg, BitVec.ofInt_add, BitVec.add_assoc]
        · rw [hpi.stk _ (stkGet_mem _ _ (.ent R') hst), ← hgn]
          show sa.regs R' = abiBase abi sa g.name
          simp only [abiBase, hR']
      · rw [hsp]; exact hpi.sp
      · rw [hpi.regs R _ hR]; rfl
      · obtain ⟨w, hw, hle⟩ := ctrB_sound hctr hb
        rw [hpi.regs _ w hw]; exact hle
    · exact absurd hres (by simp)
  · exact absurd hres (by simp)

/-- **Names held in frame words.** Each pair `(v, off)` of `Fr`: the flag-machine name `v`
    reads at width `64` the word at `rsp + off`. -/
def FrameNames (Fr : List (String × Int)) (rsp : BitVec 64) (sa : AState) (b : LstateM) :
    Prop :=
  ∀ p ∈ Fr, b.reg.getW p.1 64 = some (read64 sa.mem (rsp + BitVec.ofInt 64 p.2))

/-- **The frame check of the prologue.** Each pair `(v, off)` of `Fr`: the seeds give the
    name `v` a known value, and the symbolic prologue records that value in the stack word
    at `off` from the stack pointer at the loop head. -/
def frameRes (abi : String → Option String) (lo hi : Int) (Fr : List (String × Int))
    (seeds : List LinstrRM) (pre : List (JInstr 64)) : Bool :=
  match prun lo hi PSt.init pre, frun (fdflt abi) [] seeds with
  | some p, some t =>
      Fr.all fun q => (getV (fdflt abi) t q.1).isSome
        && getV (fdflt abi) t q.1 == stkGet p.stk (p.sp + q.2)
  | _, _ => false

/-- **The prologue with names held in frame words.** `decSim_pre`, with the names of `Fr`
    held in their frame words at the loop-head stack pointer when `frameRes` accepts. -/
theorem decSim_pre_fr {E : MemEnv} {abi : String → Option String}
    {bounds : List (String × Nat)} {lo hi : Int} {L0 : List String} {ctr R : String}
    {seeds : List LinstrRM} {pre : List (JInstr 64)} {p : PSt} (hsp : E.sp = "%rsp")
    (hres : preRes E abi bounds lo hi L0 ctr R seeds pre = some p) {Fr : List (String × Int)}
    (hfr : frameRes abi lo hi Fr seeds pre = true) (sa0 : AState)
    (hsep : ∀ A j, regK E.rs A j → ∀ o : Int, lo ≤ o → o ≤ hi →
      Disjoint8 (sa0.regs "%rsp" + BitVec.ofInt 64 o) ((regLay E.rs (abiBase abi sa0)).addr A j))
    (hb : ∀ x ∈ bounds, (sa0.regs x.1).toNat ≤ x.2) :
    DecSim (fun sa b _ => sa = sa0 ∧ NodeEntry abi E.rs sa b)
      (fun sa b zf => (MCorr E (abiBase abi sa0) (sa0.regs "%rsp" + BitVec.ofInt 64 p.sp)
          (L0, Abs.empty) False sa b zf
        ∧ sa.regs R = 0 ∧ (sa.regs (E.pi ctr)).toNat ≤ E.nb)
        ∧ FrameNames Fr (sa0.regs "%rsp" + BitVec.ofInt 64 p.sp) sa b)
      seeds pre := by
  intro sa b zf hI
  obtain ⟨b', z', hrun, hJ⟩ := decSim_pre hsp hres sa0 hsep hb sa b zf hI
  obtain ⟨rfl, hent⟩ := hI
  have hp : prun lo hi PSt.init pre = some p := by
    unfold preRes at hres
    split at hres
    · rename_i p' t hp' _
      split at hres
      · obtain rfl := Option.some.inj hres; exact hp'
      · exact absurd hres (by simp)
    · exact absurd hres (by simp)
  unfold frameRes at hfr
  rw [hp] at hfr
  split at hfr
  · rename_i p' t hp'' ht
    obtain rfl := Option.some.inj hp''
    have hpi := prun_sound pre _ _ sa hp (pInv_init lo hi sa)
    have hfi : FInv sa (fdflt abi) [] b := by
      intro r v hv
      simp only [getV, fdflt, Option.map_eq_some_iff] at hv
      obtain ⟨R', hR', rfl⟩ := hv
      exact hent.regs r R' hR'
    obtain ⟨b'', hrun'', hfi', -⟩ := frun_sound seeds [] t b zf ht hfi
    rw [hrun''] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrun)
    refine ⟨_, _, hrun'', hJ, fun q hq => ?_⟩
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hfr
    obtain ⟨⟨v, hv⟩, he⟩ := hfr q hq
    rw [hv] at he
    have hs := hpi.stk _ (stkGet_mem _ _ v he.symm)
    simp only [BitVec.ofInt_add, ← BitVec.add_assoc] at hs
    rw [hfi' q.1 v hv, hs]
  · cases hfr

/-! ## 5. The loop registers and the epilogue on the machine -/

/-- The decoded loop body writes the register `R` once, by `add $1, %R`. -/
def incrOnce (R : String) : List (JInstr 64) → Bool
  | [] => false
  | j :: js =>
      if j = .add R (.imm 1) then js.all (fun j' => !(dsts j').contains R)
      else !(dsts j).contains R && incrOnce R js

theorem runBlock_regs_of_incrOnce (R : String) :
    ∀ (js : List (JInstr 64)) (sa : AState), incrOnce R js = true →
      (aMachine.runBlock sa js).regs R = sa.regs R + 1 := by
  intro js
  induction js with
  | nil => intro _ h; simp [incrOnce] at h
  | cons j js ih =>
    intro sa h
    simp only [incrOnce] at h
    split at h
    · rename_i hj
      subst hj
      rw [Machine.runBlock_cons, runBlock_regs_of_not_dsts R js _ h]
      show (if R = R then sa.regs R + BitVec.ofNat 64 1 else sa.regs R) = _
      rw [if_pos rfl]; rfl
    · simp only [Bool.and_eq_true] at h
      rw [Machine.runBlock_cons, ih _ h.2]
      have hj : R ∉ dsts j := by simpa using h.1
      exact congrArg (· + 1) (evalInstrA_regs_of_not_mem_dsts sa j R hj)

/-- The machine instructions that write no memory: loads, `lea` and register moves. -/
def noStoreB : JInstr 64 → Bool
  | .loadMem .. => true
  | .lea .. => true
  | .mov .. => true
  | _ => false

theorem runBlock_mem_of_noStoreB :
    ∀ (js : List (JInstr 64)) (sa : AState), js.all noStoreB = true →
      (aMachine.runBlock sa js).mem = sa.mem := by
  intro js
  induction js with
  | nil => intro _ _; rfl
  | cons j js ih =>
    intro sa h
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [Machine.runBlock_cons, ih _ h.2]
    cases j <;> first | rfl | exact absurd h.1 (by simp [noStoreB])

/-- A label search behind an all-`Lopn` prefix is the search in the rest, shifted by the
    prefix length. -/
theorem findLabelMem_append_lopn (l : LLabel) (xs ys : List LinstrRM)
    (hx : ∀ i ∈ xs, IsLopn i) :
    findLabelMem l (xs ++ ys) = (findLabelMem l ys).map (· + xs.length) := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_append, List.findIdx?_append]
  have hnone : (xs.map Prod.fst).findIdx? (JasminLsemLabeled.isLabel l) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    obtain ⟨d, o, s, hd⟩ := hx i hi
    rw [hd]
    rfl
  rw [hnone, List.length_map]
  simp

/-! ## 6. The node -/

/-- The back-edge compare on `MCorr` with no machine facts, carrying a fact `P` on the
    registers, and setting the machine zero flag to the test of the counter register. -/
theorem decSim_cmp_mcorr {E : MemEnv} {base : String → BitVec 64} {rsp : BitVec 64}
    {L0 : List String} {ctr : String} (hctr : ctr ∈ L0) (P : (String → BitVec 64) → Prop)
    (zl : Prop) :
    DecSim (fun sa b zf => MCorr E base rsp (L0, Abs.empty) zl sa b zf ∧ P sa.regs)
      (fun sa b zf => MCorr E base rsp (L0, Abs.empty) True sa b zf
        ∧ P sa.regs ∧ sa.flags.zf.getD false = (sa.regs (E.pi ctr) == 0))
      [cmpRI ctr (.imm 0)] [.cmp (E.pi ctr) (.imm 0)] := by
  have h := (decSim_cmpImm (Lay := regLay E.rs base) (frame := regFrame E.rs rsp)
    (K := regK E.rs) (zl := zl) (L := (· ∈ L0)) (π := E.pi) ctr 0 hctr).andMach
    (P := fun sa => sa.regs E.sp = rsp ∧ P sa.regs)
    (Q := fun sa => (sa.regs E.sp = rsp ∧ P sa.regs)
      ∧ sa.flags.zf.getD false = (sa.regs (E.pi ctr) == 0)) (fun sa hp => by
      obtain ⟨e1, e2⟩ := evalInstrA_cmp0 sa (E.pi ctr)
      simp only [Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
      exact ⟨by rw [e1]; exact hp, by rw [e2, e1]⟩)
  exact h.weaken (fun _ _ _ hi => ⟨hi.1.1, hi.1.2.1, hi.2⟩)
    (fun sa _ _ hj => ⟨⟨hj.1, hj.2.1.1, Abs.holds_empty _ _ _⟩, hj.2.1.2, hj.2.2⟩)

/-- The back-edge compare of `decSim_cmp_mcorr`, keeping the names held in frame words. -/
theorem decSim_cmp_mcorr_fr {E : MemEnv} {base : String → BitVec 64} {rsp : BitVec 64}
    {L0 : List String} {ctr : String} (hctr : ctr ∈ L0) (P : (String → BitVec 64) → Prop)
    (zl : Prop) (Fr : List (String × Int)) :
    DecSim (fun sa b zf => (MCorr E base rsp (L0, Abs.empty) zl sa b zf ∧ P sa.regs)
        ∧ FrameNames Fr rsp sa b)
      (fun sa b zf => (MCorr E base rsp (L0, Abs.empty) True sa b zf
        ∧ P sa.regs ∧ sa.flags.zf.getD false = (sa.regs (E.pi ctr) == 0))
        ∧ FrameNames Fr rsp sa b)
      [cmpRI ctr (.imm 0)] [.cmp (E.pi ctr) (.imm 0)] := by
  intro sa b zf ⟨h, hF⟩
  obtain ⟨b', z', hr, hJ⟩ := decSim_cmp_mcorr (E := E) (base := base) (rsp := rsp) hctr P zl
    sa b zf h
  have hc := fstepF_cmpRI ctr (.imm 0) b zf _ _ (h.1.1.regs ctr hctr) rfl
  rw [runStraightF_singleton, hc] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr).symm
  refine ⟨_, _, by rw [runStraightF_singleton, hc], hJ, fun p hp => ?_⟩
  rw [LstateM.reg_nextPc, LstateN.getW_nextPc]
  exact hF p hp

/-- **A checked node whose loop keeps names in frame words.** `decNodeMem_halts` with the
    loop invariant extended by the names `Fr` held in frame words at the loop-head stack
    pointer `rsp` (`FrameNames`): the prologue `hpre` establishes them, the loop body `hbody`
    simulates its machine instructions from `MCorr` with them and a valid index to `MCorr`
    with them, and the back-edge compare keeps them. -/
theorem decNodeMem_halts_fr {E : MemEnv} {base : String → BitVec 64} {rsp : BitVec 64}
    (fn : String) (seeds body : List LinstrRM)
    (top endL : LLabel) (ctr R : String) (L0 : List String) (Fr : List (String × Int))
    (pre post : List (JInstr 64))
    (l : XLoop 64) (hseedsL : seeds.all isLopnB = true) (hbodyL : body.all isLopnB = true)
    (htopE : top ≠ endL)
    (hbody : DecSim (fun sa b zf => (MCorr E base rsp (L0, Abs.empty) False sa b zf
        ∧ FrameNames Fr rsp sa b) ∧ (sa.regs R).toNat < E.nb)
      (fun sa b zf => MCorr E base rsp (L0, Abs.empty) False sa b zf ∧ FrameNames Fr rsp sa b)
      body l.body)
    (hctr : ctr ∈ L0) (hlctr : l.ctr = E.pi ctr) (hdec : decrOnce (E.pi ctr) l.body = true)
    (hinc : incrOnce R l.body = true) (hpost : post.all noStoreB = true)
    (E₀ : AState → LstateM → Bool → Prop)
    (hpre : DecSim E₀ (fun sa b zf => (MCorr E base rsp (L0, Abs.empty) False sa b zf
      ∧ sa.regs R = 0 ∧ (sa.regs (E.pi ctr)).toNat ≤ E.nb) ∧ FrameNames Fr rsp sa b) seeds pre)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hE : E₀ sa b zf) :
    ∃ sa' t k, Halts aMachine (nodeLayout pre l post) 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∀ A j, regK E.rs A j → ∃ arr : Fin (regLen E.rs A) → BitVec 64,
          t.prog.base.getArr A 64 (regLen E.rs A) = some arr
            ∧ read64 sa'.mem ((regLay E.rs base).addr A j) = stackGet arr j := by
  have hsL : ∀ i ∈ seeds, IsLopn i := fun i hi => isLopnB_isLopn (List.all_eq_true.mp hseedsL i hi)
  have hbL : ∀ i ∈ body, IsLopn i := fun i hi => isLopnB_isLopn (List.all_eq_true.mp hbodyL i hi)
  set C := E.pi ctr with hC
  set m := ((aMachine.runBlock sa pre).regs C).toNat with hm
  have hm64 : m < 2 ^ 64 := BitVec.isLt _
  let Inv : Nat → AState → LstateM → Bool → Prop := fun t sa' b' zf' =>
    (MCorr E base rsp (L0, Abs.empty) False sa' b' zf'
      ∧ (sa'.regs C = BitVec.ofNat 64 (m - t) ∧ sa'.regs R = BitVec.ofNat 64 t ∧ m ≤ E.nb))
      ∧ FrameNames Fr rsp sa' b'
  let Inv' : Nat → AState → LstateM → Bool → Prop := fun t sa' b' zf' =>
    (MCorr E base rsp (L0, Abs.empty) True sa' b' zf'
      ∧ (sa'.regs C = BitVec.ofNat 64 (m - t) - 1 ∧ sa'.regs R = BitVec.ofNat 64 t + 1
        ∧ m ≤ E.nb) ∧ sa'.flags.zf.getD false = (sa'.regs C == 0))
      ∧ FrameNames Fr rsp sa' b'
  -- the prologue, at the entry state `sa`
  have hpre' : DecSim (fun sa' b' zf' => E₀ sa' b' zf' ∧ sa' = sa) (Inv 0) seeds pre := by
    refine (hpre.andMach (P := (· = sa)) (Q := (· = aMachine.runBlock sa pre))
      (fun _ h => by rw [h])).weaken (fun _ _ _ h => h) (fun sa' _ _ h => ?_)
    obtain ⟨⟨⟨hc, hR, hle⟩, hF⟩, rfl⟩ := h
    exact ⟨⟨hc, by rw [Nat.sub_zero, hm, BitVec.ofNat_toNat, BitVec.setWidth_eq], by
      rw [hR]; rfl, hle⟩, hF⟩
  -- the guard
  have hg := decSim_cmp_mcorr_fr (E := E) (base := base) (rsp := rsp) hctr
    (fun rg => rg C = BitVec.ofNat 64 (m - 0) ∧ rg R = BitVec.ofNat 64 0 ∧ m ≤ E.nb) False Fr
  -- the trips
  have hsim : ∀ t, t < m →
      DecSim (Inv t) (Inv' t) (body ++ [cmpRI ctr (.imm 0)]) (l.body ++ [l.cmpInstr]) := by
    intro t ht
    have hB := hbody.andMach
      (P := fun sa' => sa'.regs C = BitVec.ofNat 64 (m - t) ∧ sa'.regs R = BitVec.ofNat 64 t
        ∧ m ≤ E.nb)
      (Q := fun sa' => sa'.regs C = BitVec.ofNat 64 (m - t) - 1
        ∧ sa'.regs R = BitVec.ofNat 64 t + 1 ∧ m ≤ E.nb) (fun sa' h => by
        rw [runBlock_regs_of_decrOnce C _ sa' hdec, runBlock_regs_of_incrOnce R _ sa' hinc,
          h.1, h.2.1]
        exact ⟨rfl, rfl, h.2.2⟩)
    have hC' := decSim_cmp_mcorr_fr (E := E) (base := base) (rsp := rsp) hctr
      (fun rg => rg C = BitVec.ofNat 64 (m - t) - 1 ∧ rg R = BitVec.ofNat 64 t + 1
        ∧ m ≤ E.nb) False Fr
    rw [XLoop.cmpInstr, hlctr]
    refine (hB.weaken (fun sa' _ _ h => ⟨⟨⟨h.1.1, h.2⟩, ?_⟩, h.1.2⟩)
      (fun _ _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩)).append hC'
    rw [h.1.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨sa', t, k, hh, hrun, hQ⟩ := decNode_halts fn seeds body top endL ctr l m
    (fun sa' b' zf' => E₀ sa' b' zf' ∧ sa' = sa) (Inv 0)
    (fun sa' b' zf' => (MCorr E base rsp (L0, Abs.empty) True sa' b' zf'
      ∧ (sa'.regs C = BitVec.ofNat 64 (m - 0) ∧ sa'.regs R = BitVec.ofNat 64 0 ∧ m ≤ E.nb)
      ∧ sa'.flags.zf.getD false = (sa'.regs C == 0)) ∧ FrameNames Fr rsp sa' b')
    Inv Inv'
    (fun sa' b' => ∃ sa₀, MCorr E base rsp (L0, Abs.empty) False sa₀ b' true
      ∧ sa'.mem = sa₀.mem)
    pre post hsL hbL
    (by rw [findLabelMem_append_lopn _ _ _ hsL, findLabelMem_guarded_top]; simp [Nat.add_comm])
    (by
      rw [findLabelMem_append_lopn _ _ _ hsL, findLabelMem_guarded_endL _ _ _ _ hbL htopE]
      simp only [Option.map_some, Option.some.injEq]
      omega)
    hpre' (by rw [XLoop.cmpInstr, hlctr]; exact hg)
    (fun sa' b' zf' ⟨⟨hc, ⟨hv, _⟩, hz⟩, _⟩ => by
      refine ⟨hc.1.zfEq trivial, ?_⟩
      rw [← hc.1.zfEq trivial, hz, hv, Nat.sub_zero]
      simp only [beq_iff_eq]
      constructor
      · intro h
        have h2 := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at h2
        simpa using h2
      · intro h; rw [h]; rfl)
    (fun sa' b' zf' pc ⟨⟨hc, hv, _⟩, hF⟩ =>
      ⟨⟨⟨(hc.1.setLpc pc).dropZf, hc.2⟩, hv⟩, fun p hp => hF p hp⟩)
    hsim
    (fun t ht sa' b' zf' ⟨⟨hc, ⟨hv, _⟩, hz⟩, _⟩ => by
      refine ⟨hc.1.zfEq trivial, ?_⟩
      rw [← hc.1.zfEq trivial, hz, hv, ofNat_sub_one m t ht]
      exact ofNat_eq_zero_iff m t ht hm64)
    (fun t ht sa' b' zf' pc ⟨⟨hc, ⟨hv, hr, hle⟩, _⟩, hF⟩ =>
      ⟨⟨⟨(hc.1.setLpc pc).dropZf, hc.2⟩, by rw [hv, ofNat_sub_one m t ht], by
        rw [hr, BitVec.ofNat_add]; rfl, hle⟩, fun p hp => hF p hp⟩)
    (fun sa' b' ⟨⟨hc, _⟩, _⟩ => ⟨sa', hc, runBlock_mem_of_noStoreB post sa' hpost⟩)
    sa b zf hpc ⟨hE, rfl⟩
  obtain ⟨sa₀, hc, hmem⟩ := hQ
  refine ⟨sa', t, k, hh, hrun, fun A j hk => ?_⟩
  obtain ⟨hj, arr, ha, hr⟩ := hc.1.cells A j hk
  exact ⟨arr, ha, by rw [hmem]; exact hr⟩

/-- **A checked node with word-array memory on both machines.** The flag-machine node
    `seeds ++ guardedFlagLoopLinstrRM top endL ctr body` with all-`Lopn` seeds and body and
    the decoded node `nodeLayout pre l post`: the prologue `hpre` simulates the seeds from
    `E₀` to `MCorr` on the live names `L0` with no machine facts, the index register `R` at
    `0` and the counter register at most the index bound; the loop body is accepted by
    `loopOK` from the fact that `R` holds a valid index; the decoded loop body decrements
    the counter register once and increments `R` once; the epilogue `post` writes no
    memory. Under `MemSep` of the regions, from states related by `E₀` with the flag machine
    at program counter `0`, the machine halts from index `0` in a state `sa'`, the flag
    machine halts in `t`, and every word of every region is read in the memory of `sa'` at
    its layout address as `t` holds it. -/
theorem decNodeMem_halts {E : MemEnv} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : MemSep E.rs base rsp) (fn : String) (seeds body : List LinstrRM)
    (top endL : LLabel) (ctr R : String) (L0 : List String) (pre post : List (JInstr 64))
    (l : XLoop 64) (hseedsL : seeds.all isLopnB = true) (hbodyL : body.all isLopnB = true)
    (htopE : top ≠ endL) (hloop : loopOK E L0 (Abs.idx R) body l.body = true)
    (hctr : ctr ∈ L0) (hlctr : l.ctr = E.pi ctr) (hdec : decrOnce (E.pi ctr) l.body = true)
    (hinc : incrOnce R l.body = true) (hpost : post.all noStoreB = true)
    (E₀ : AState → LstateM → Bool → Prop)
    (hpre : DecSim E₀ (fun sa b zf => MCorr E base rsp (L0, Abs.empty) False sa b zf
      ∧ sa.regs R = 0 ∧ (sa.regs (E.pi ctr)).toNat ≤ E.nb) seeds pre)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hE : E₀ sa b zf) :
    ∃ sa' t k, Halts aMachine (nodeLayout pre l post) 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∀ A j, regK E.rs A j → ∃ arr : Fin (regLen E.rs A) → BitVec 64,
          t.prog.base.getArr A 64 (regLen E.rs A) = some arr
            ∧ read64 sa'.mem ((regLay E.rs base).addr A j) = stackGet arr j := by
  have hnil : ∀ (sa' : AState) (b' : LstateM), FrameNames [] rsp sa' b' :=
    fun _ _ p hp => by cases hp
  exact decNodeMem_halts_fr fn seeds body top endL ctr R L0 [] pre post l hseedsL hbodyL htopE
    ((decSim_of_loopOK_idx (E := E) (base := base) (rsp := rsp) hsep hloop False).weaken
      (fun _ _ _ h => ⟨h.1.1, h.2⟩) (fun sa' b' _ h => ⟨h, hnil sa' b'⟩))
    hctr hlctr hdec hinc hpost E₀
    (hpre.weaken (fun _ _ _ h => h) (fun sa' b' _ h => ⟨h, hnil sa' b'⟩)) sa b zf hpc hE

/-! ## 7. The System V layout -/

open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout AbiArg ArgKind ResultKind wordsAt)

/-- The parameter of `σ` that the name `A` denotes: parameter `j` for `A = argName j`. -/
def abiArgOf (σ : AbiLayout) (A : String) : Option AbiArg :=
  ((List.range σ.args.length).find? (fun j => argName j == A)).bind (fun j => σ.args[j]?)

/-- The System V register of the parameter the name `A` denotes. -/
def abiReg (σ : AbiLayout) (A : String) : Option String := (abiArgOf σ A).map (·.reg)

/-- **The regions of a layout.** Each region is an array parameter of `σ` of the region's
    length, at most `2 ^ 61` words, and the registers of the regions are pairwise
    distinct. -/
def rsOK (σ : AbiLayout) (rs : List Region) : Bool :=
  rs.all (fun g => (abiArgOf σ g.name).any (fun a => a.kind == .words g.len)
      && decide (g.len ≤ 2 ^ 61))
    && decide ((rs.map (fun g => abiReg σ g.name)).Nodup)

theorem abiArgOf_mem {σ : AbiLayout} {A : String} {a : AbiArg} (h : abiArgOf σ A = some a) :
    a ∈ σ.args := by
  obtain ⟨j, -, hj⟩ := Option.bind_eq_some_iff.mp h
  exact List.mem_of_getElem? hj

/-- A region of an accepted list: its parameter, an array of its length, and the entry
    value of the parameter's register as its base. -/
theorem rsOK_region {σ : AbiLayout} {rs : List Region} (hrs : rsOK σ rs = true) {g : Region}
    (hg : g ∈ rs) (sa : AState) :
    ∃ a : AbiArg, abiReg σ g.name = some a.reg ∧ (a.reg, g.len) ∈ σ.regions
      ∧ g.len ≤ 2 ^ 61 ∧ abiBase (abiReg σ) sa g.name = sa.regs a.reg := by
  simp only [rsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hrs
  obtain ⟨hk, hlen⟩ := hrs.1 g hg
  obtain ⟨a, ha, hka⟩ : ∃ a, abiArgOf σ g.name = some a ∧ a.kind = .words g.len := by
    cases hx : abiArgOf σ g.name with
    | none => rw [hx] at hk; simp at hk
    | some a => rw [hx] at hk; exact ⟨a, rfl, by simpa using hk⟩
  have hr : abiReg σ g.name = some a.reg := by simp [abiReg, ha]
  refine ⟨a, hr, List.mem_filterMap.mpr ⟨a, abiArgOf_mem ha, by simp [AbiArg.region, hka]⟩,
    hlen, by simp [abiBase, hr]⟩

/-- A cell of the regions lies in a region of the list. -/
theorem regK_region {rs : List Region} {A : String} {j : Nat} (hk : regK rs A j) :
    ∃ g, regFind rs A = some g ∧ g ∈ rs ∧ g.name = A ∧ j < g.len := by
  unfold regK regLen at hk
  cases hg : regFind rs A with
  | none => rw [hg] at hk; simp at hk
  | some g =>
    rw [hg] at hk
    obtain ⟨hm, hn⟩ := regFind_spec hg
    exact ⟨g, rfl, hm, hn, by simpa using hk⟩

/-- Two distinct words of one array of at most `2 ^ 61` words are disjoint. -/
theorem disjoint8_words_lt (x : BitVec 64) {j j' : Nat} (hj : j < 2 ^ 61) (hj' : j' < 2 ^ 61)
    (hne : j ≠ j') :
    Disjoint8 (x + BitVec.ofNat 64 (8 * j)) (x + BitVec.ofNat 64 (8 * j')) := by
  apply disjoint8_add_left
  unfold Disjoint8
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

variable {σ : AbiLayout} {rs : List Region}

/-- Distinct cells of accepted regions are disjoint. -/
theorem cells_disjoint (hrs : rsOK σ rs = true) {sa : AState} (h : σ.Regions sa)
    {A A' : String} {j j' : Nat} (hk : regK rs A j) (hk' : regK rs A' j')
    (hne : ¬ (A = A' ∧ j = j')) :
    Disjoint8 ((regLay rs (abiBase (abiReg σ) sa)).addr A j)
      ((regLay rs (abiBase (abiReg σ) sa)).addr A' j') := by
  obtain ⟨g, -, hg, rfl, hj⟩ := regK_region hk
  obtain ⟨g', -, hg', rfl, hj'⟩ := regK_region hk'
  obtain ⟨a, hr, hreg, hlen, hb⟩ := rsOK_region hrs hg sa
  obtain ⟨a', hr', hreg', hlen', hb'⟩ := rsOK_region hrs hg' sa
  simp only [Layout.addr, regLay, hb, hb']
  by_cases hgg : g = g'
  · subst hgg
    rw [hr] at hr'
    rw [show a'.reg = a.reg from (Option.some.inj hr').symm]
    exact disjoint8_words_lt (sa.regs a.reg) (lt_of_lt_of_le hj hlen)
      (lt_of_lt_of_le hj' hlen) (fun he => hne ⟨rfl, he⟩)
  · have hnd : (rs.map (fun g => abiReg σ g.name)).Nodup := by
      simp only [rsOK, Bool.and_eq_true, decide_eq_true_eq] at hrs
      exact hrs.2
    have hrr : a.reg ≠ a'.reg := fun he =>
      hgg (List.inj_on_of_nodup_map hnd hg hg' (by rw [hr, hr', he]))
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hreg
    obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp hreg'
    have hii : i ≠ i' := by
      rintro rfl
      rw [hi] at hi'
      exact hrr (congrArg Prod.fst (Option.some.inj hi'))
    exact h.2.1 i i' _ _ hii hi hi' j j' hj hj'

/-- **The frame separation from the layout.** Every cell of accepted regions is disjoint
    from every stack word in the frame range of `σ`. -/
theorem frameSep_of_regions (hrs : rsOK σ rs = true) {sa : AState} (h : σ.Regions sa) :
    ∀ A j, regK rs A j → ∀ o : Int, σ.frameLo ≤ o → o ≤ σ.frameHi →
      Disjoint8 (sa.regs "%rsp" + BitVec.ofInt 64 o)
        ((regLay rs (abiBase (abiReg σ) sa)).addr A j) := by
  intro A j hk o ho1 ho2
  obtain ⟨g, -, hg, rfl, hj⟩ := regK_region hk
  obtain ⟨a, -, hreg, -, hb⟩ := rsOK_region hrs hg sa
  simp only [Layout.addr, regLay, hb]
  exact h.2.2 _ hreg j hj o ho1 ho2

/-- **`MemSep` from the layout.** Accepted regions at the entry bases, with their pointer
    slots at the stack pointer `sa.regs "%rsp" + sp` inside the frame range of `σ`, satisfy
    `MemSep`. -/
theorem memSep_of_regions (hrs : rsOK σ rs = true) {sa : AState} (h : σ.Regions sa)
    (sp : Int) (hslot : ∀ g ∈ rs, σ.frameLo ≤ sp + g.off ∧ sp + g.off ≤ σ.frameHi) :
    MemSep rs (abiBase (abiReg σ) sa) (sa.regs "%rsp" + BitVec.ofInt 64 sp) where
  sep :=
    { cells := fun A j A' j' hj hj' => by
        by_cases he : A = A' ∧ j = j'
        · obtain ⟨rfl, rfl⟩ := he; exact Or.inl rfl
        · exact Or.inr (cells_disjoint hrs h hj hj' he)
      slots := fun A j B q x hj hq hx => by
        have hq' : (regFind rs B).isSome = true ∧ B = q := by
          simp only [regLay] at hq
          split at hq
          · rename_i hs; exact ⟨hs, Option.some.inj hq⟩
          · exact absurd hq (by simp)
        obtain ⟨hs, rfl⟩ := hq'
        obtain ⟨gB, hgB⟩ := Option.isSome_iff_exists.mp hs
        have hx' : x = sa.regs "%rsp" + BitVec.ofInt 64 (sp + gB.off) := by
          simp only [regFrame, hgB, Option.map_some, Option.some.injEq] at hx
          rw [← hx, BitVec.ofInt_add, BitVec.add_assoc]
        obtain ⟨h1, h2⟩ := hslot gB (regFind_spec hgB).1
        rw [hx']
        exact (frameSep_of_regions hrs h A j hj _ h1 h2).symm }
  inj := fun A j A' j' hk hk' he => by
    by_contra hne
    have hd := cells_disjoint hrs h hk hk' hne
    rw [he] at hd
    simp [Disjoint8] at hd

/-! ## 8. The node from the System V entry -/

/-- **The node check.** The stack register, the regions of `σ`, the prologue check at the
    frame range and bounds of `σ`, the all-`Lopn` seeds and body, distinct labels, the loop
    body check from the index fact on `R`, the live counter with its machine register as
    the loop counter, one decrement of the counter register and one increment of `R` in the
    decoded loop body, and an epilogue that writes no memory. -/
def nodeCheck (σ : AbiLayout) (E : MemEnv) (seeds body : List LinstrRM) (top endL : LLabel)
    (ctr R : String) (L0 : List String) (pre post : List (JInstr 64)) (l : XLoop 64) : Bool :=
  E.sp == "%rsp" && rsOK σ E.rs
    && (preRes E (abiReg σ) σ.bounds σ.frameLo σ.frameHi L0 ctr R seeds pre).isSome
    && seeds.all isLopnB && body.all isLopnB && top != endL
    && loopOK E L0 (Abs.idx R) body l.body && decide (ctr ∈ L0) && l.ctr == E.pi ctr
    && decrOnce (E.pi ctr) l.body && incrOnce R l.body && post.all noStoreB

/-- The pointer slots of an accepted prologue lie in the frame range. -/
theorem preRes_slots {E : MemEnv} {abi : String → Option String} {bounds : List (String × Nat)}
    {lo hi : Int} {L0 : List String} {ctr R : String} {seeds : List LinstrRM}
    {pre : List (JInstr 64)} {p : PSt}
    (hres : preRes E abi bounds lo hi L0 ctr R seeds pre = some p) :
    ∀ g ∈ E.rs, lo ≤ p.sp + g.off ∧ p.sp + g.off ≤ hi := by
  unfold preRes at hres
  split at hres
  · split at hres
    · rename_i hc
      obtain rfl := Option.some.inj hres
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      exact fun g hg => (hc.1.1.2 g hg).1.1
    · exact absurd hres (by simp)
  · exact absurd hres (by simp)

/-- **The node from the System V entry.** For a node that passes `nodeCheck` against the
    layout `σ`, from an entry state `sa` satisfying `σ.Regions` and the entry correspondence
    at the System V registers of `σ`, with the flag machine at program counter `0`: the
    machine halts on the decoded node from index `0` in a state `sa'`, the flag machine
    halts on the node in `t`, and every word of every region is read in the memory of `sa'`
    at its address from the entry value of the region's register as `t` holds it. -/
theorem decNodeAbi_halts (σ : AbiLayout) (E : MemEnv) (fn : String)
    (seeds body : List LinstrRM) (top endL : LLabel) (ctr R : String) (L0 : List String)
    (pre post : List (JInstr 64)) (l : XLoop 64)
    (hchk : nodeCheck σ E seeds body top endL ctr R L0 pre post l = true)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hreg : σ.Regions sa)
    (hent : NodeEntry (abiReg σ) E.rs sa b) :
    ∃ sa' t k, Halts aMachine (nodeLayout pre l post) 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∀ A j, regK E.rs A j → ∃ arr : Fin (regLen E.rs A) → BitVec 64,
          t.prog.base.getArr A 64 (regLen E.rs A) = some arr
            ∧ read64 sa'.mem ((regLay E.rs (abiBase (abiReg σ) sa)).addr A j)
              = stackGet arr j := by
  simp only [nodeCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp, hrs⟩, hres⟩, hsL⟩, hbL⟩, htop⟩, hloop⟩, hctr⟩, hlctr⟩, hdec⟩,
    hinc⟩, hpost⟩ := hchk
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hres
  have hsep := memSep_of_regions hrs hreg p.sp (preRes_slots hp)
  exact decNodeMem_halts hsep fn seeds body top endL ctr R L0 pre post l hsL hbL htop hloop
    hctr hlctr hdec hinc hpost _ (decSim_pre hsp hp sa (frameSep_of_regions hrs hreg) hreg.1)
    sa b zf hpc ⟨rfl, hent⟩

/-- **The result read-back from the cells.** When the result of `σ` is the words of the
    region `A`, and every cell of the regions is read in the memory of `sa'` at its layout
    address as the flag-machine state `t` holds it, `σ` reads back the array `t` holds at
    `A`. -/
theorem result_of_cells (σ : AbiLayout) (E : MemEnv) (A RA : String)
    (hA : abiReg σ A = some RA) (hres : σ.result = .words RA (regLen E.rs A))
    (hn : 0 < regLen E.rs A) (sa sa' : AState) (t : LstateMF)
    (hcells : ∀ A j, regK E.rs A j → ∃ arr : Fin (regLen E.rs A) → BitVec 64,
      t.prog.base.getArr A 64 (regLen E.rs A) = some arr
        ∧ read64 sa'.mem ((regLay E.rs (abiBase (abiReg σ) sa)).addr A j) = stackGet arr j) :
    ∃ arr : Fin (regLen E.rs A) → BitVec 64,
      t.prog.base.getArr A 64 (regLen E.rs A) = some arr
        ∧ σ.ResultOf sa sa'
            (.array ((List.range (regLen E.rs A)).map fun j => .int (stackGet arr j).toNat)) := by
  obtain ⟨arr, ha, -⟩ := hcells A 0 hn
  refine ⟨arr, ha, ?_⟩
  show _ = σ.result.read sa sa'
  rw [hres]
  simp only [ResultKind.read, wordsAt]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨arr', ha', hr⟩ := hcells A j (List.mem_range.mp hj)
  rw [ha] at ha'
  obtain rfl := Option.some.inj ha'
  rw [← hr]
  simp [Layout.addr, regLay, abiBase, hA]

/-- **The decoded bytes of a node realise the result read-back.** For bytes that decode to
    the node layout and a node that passes `nodeCheck`, from an entry state satisfying
    `σ.Regions` and the entry correspondence: when the result of `σ` is the `n` words at the
    entry value of the register of the region `A` of `n > 0` words, the decoded program
    halts in a state `sa'`, the flag machine halts in `t` with the array `arr` at `A`, and
    `σ.ResultOf sa sa'` holds of the words of `arr`. -/
theorem decNodeAbi_result (σ : AbiLayout) (E : MemEnv) (fn : String)
    (seeds body : List LinstrRM) (top endL : LLabel) (ctr R : String) (L0 : List String)
    (pre post : List (JInstr 64)) (l : XLoop 64) (bytes : List (BitVec 8))
    (hdec : LprogBytesDecode.decodeLprog bytes = some (nodeLayout pre l post))
    (hchk : nodeCheck σ E seeds body top endL ctr R L0 pre post l = true)
    (A RA : String) (hA : abiReg σ A = some RA)
    (hres : σ.result = .words RA (regLen E.rs A)) (hn : 0 < regLen E.rs A)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hreg : σ.Regions sa)
    (hent : NodeEntry (abiReg σ) E.rs sa b) :
    ∃ prog sa' t k, LprogBytesDecode.decodeLprog bytes = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∃ arr : Fin (regLen E.rs A) → BitVec 64,
          t.prog.base.getArr A 64 (regLen E.rs A) = some arr
            ∧ σ.ResultOf sa sa'
                (.array ((List.range (regLen E.rs A)).map fun j => .int (stackGet arr j).toNat)) := by
  obtain ⟨sa', t, k, hh, hrun, hcells⟩ := decNodeAbi_halts σ E fn seeds body top endL ctr R L0
    pre post l hchk sa b zf hpc hreg hent
  obtain ⟨arr, ha, hR⟩ := result_of_cells σ E A RA hA hres hn sa sa' t hcells
  exact ⟨_, sa', t, k, hdec, hh, hrun, arr, ha, hR⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
