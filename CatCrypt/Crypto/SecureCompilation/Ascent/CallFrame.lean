/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-!
# Call frames of `pushq`/`popq` form on the address machine

@ascent-fixture theorems: pushed_framePro, popped_frameEpi, framedCall_popped
The frame lists model the prologues and epilogues of a call. They are the subjects
of these theorems and encode no bytes that ship.

`JInstr 64` has no `push`, `pop`, `call` or `ret`. This module writes them as
`JInstr 64` sequences that leave the flags alone, as the hardware instructions do:

* `pushq r` is `pushI r`: `leaq -8(%rsp), %rsp` followed by the store of `r` at `0(%rsp)`;
* `popq r` is `popI r`: the load of `r` from `0(%rsp)` followed by `leaq 8(%rsp), %rsp`;
* a frame allocation `leaq -N(%rsp), %rsp` and its release `leaq N(%rsp), %rsp` are
  `allocI N` and `releaseI N`;
* `call` is `callEntry ra`: `%rsp` moved down eight bytes and the return address `ra`
  stored at `0(%rsp)`; `ret` is `retI`, `%rsp` moved up eight bytes.

`framePro rs N` pushes the registers `rs` in order and allocates `N` bytes; `frameEpi rs N`
releases the `N` bytes and pops `rs` in reverse order. `framedCall pro epi f ra sa` is the
state a call leaves: the return address pushed, `pro`, the body `f`, `epi`, and the return.
The body is a state transformer, so a straight-line block (`runBlockA · blk`) and a block
with calls both instantiate it.

## Main definitions

* `rspAdd`, `pushI`, `popI`, `pushSeq`, `popSeq`, `allocI`, `releaseI`, `framePro`,
  `frameEpi`, `callEntry`, `retI`: the frame instructions.
* `entryState`, `framedCall`: the state at the start of the body, and the state a call
  leaves.
* `slotAddr`: the address of the `k`-th eight-byte slot below a stack pointer.
* `Pushed`, `Popped`, `Entered`: the state after the pushes, after the pops, and at the
  start of the body.

## Main results

* `framedCall_popped`: for pushed registers `rs` without duplicates and without `%rsp`,
  and a body that keeps `%rsp` and the words of the saved slots, the call returns `%rsp`
  and each register of `rs` at its value at the call, and every other register, the flags
  and the memory as the body leaves them.
* `entered`: the body starts with `%rsp` below the return address, the saved slots and
  the allocation, the other registers and the flags as at the call, and the memory of the
  call except in the return-address slot and the saved slots, which hold the return
  address and the pushed registers.
* `pushed_framePro`, `popped_frameEpi`: the prologue and the epilogue from any state.
* `Entered.read64_eq`: a word disjoint from those slots reads back at the start of the body
  as at the call.
* `runBlockA_regs_of_all`: the decidable condition under which a block keeps a register.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-! ## The frame instructions -/

/-- `leaq d(%rsp), %rsp`: `%rsp` moved by `d` bytes, the flags unchanged. -/
def rspAdd (d : Int) : JInstr 64 := .lea "%rsp" "%rsp" "%rsp" 0 d

/-- `pushq r`. -/
def pushI (r : String) : List (JInstr 64) := [rspAdd (-8), .storeMem "%rsp" 0 (.reg r)]

/-- `popq r`. -/
def popI (r : String) : List (JInstr 64) := [.loadMem r "%rsp" 0, rspAdd 8]

/-- `pushq` of each register of the list, in order. -/
def pushSeq : List String → List (JInstr 64)
  | [] => []
  | r :: rs => pushI r ++ pushSeq rs

/-- `popq` of each register of the list, in reverse order. -/
def popSeq : List String → List (JInstr 64)
  | [] => []
  | r :: rs => popSeq rs ++ popI r

/-- The allocation of `n` bytes of stack, `leaq -n(%rsp), %rsp`, or nothing for `n = 0`. -/
def allocI (n : Nat) : List (JInstr 64) := if n = 0 then [] else [rspAdd (-(n : Int))]

/-- The release of `n` bytes of stack, `leaq n(%rsp), %rsp`, or nothing for `n = 0`. -/
def releaseI (n : Nat) : List (JInstr 64) := if n = 0 then [] else [rspAdd (n : Int)]

/-- The prologue: `pushq` of `rs` in order, then the allocation of `n` bytes. -/
def framePro (rs : List String) (n : Nat) : List (JInstr 64) := pushSeq rs ++ allocI n

/-- The epilogue: the release of `n` bytes, then `popq` of `rs` in reverse order. -/
def frameEpi (rs : List String) (n : Nat) : List (JInstr 64) := releaseI n ++ popSeq rs

/-- The data effect of `call`: `%rsp` moved down eight bytes and the return address `ra`
    stored at `0(%rsp)`. -/
def callEntry (ra : BitVec 64) : List (JInstr 64) :=
  [rspAdd (-8), .storeMem "%rsp" 0 (.imm ra.toNat)]

/-- The data effect of `ret`: `%rsp` moved up eight bytes. -/
def retI : List (JInstr 64) := [rspAdd 8]

/-- The state at the start of the body: the return address pushed, then the prologue. -/
def entryState (pro : List (JInstr 64)) (ra : BitVec 64) (sa : AState) : AState :=
  runBlockA sa (callEntry ra ++ pro)

/-- The state a call leaves: the return address pushed, the prologue, the body `f`, the
    epilogue and the return. -/
def framedCall (pro epi : List (JInstr 64)) (f : AState → AState) (ra : BitVec 64)
    (sa : AState) : AState :=
  runBlockA (f (entryState pro ra sa)) (epi ++ retI)

/-- The address of the `k`-th eight-byte slot below `sp`: `sp - 8 (k + 1)`. -/
def slotAddr (sp : BitVec 64) (k : Nat) : BitVec 64 :=
  sp + BitVec.ofInt 64 (-(8 * ((k : Int) + 1)))

/-! ## One instruction -/

/-- The state `sa` with `%rsp` set to `v`. -/
def setRsp (sa : AState) (v : BitVec 64) : AState :=
  { sa with regs := fun r => if r = "%rsp" then v else sa.regs r }

theorem evalInstrA_rspAdd (sa : AState) (d : Int) :
    evalInstrA sa (rspAdd d) = setRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d) := by
  simp [evalInstrA, rspAdd, evalInstr, JState.setReg, AState.view, writeAddr, setRsp,
    x86_LEA]

theorem evalInstrA_storeMem (sa : AState) (b : String) (o : Int) (src : JOperand) :
    evalInstrA sa (.storeMem b o src) =
      { sa with
        mem := write64 sa.mem (sa.regs b + BitVec.ofInt 64 o) (src.eval sa.view) } := by
  simp [evalInstrA, evalInstr, JState.store, AState.view, writeAddr, writeVal, x86_MOV]

theorem evalInstrA_loadMem (sa : AState) (d b : String) (o : Int) :
    evalInstrA sa (.loadMem d b o) =
      { sa with
        regs := fun r' => if r' = d then read64 sa.mem (sa.regs b + BitVec.ofInt 64 o)
          else sa.regs r' } := by
  simp [evalInstrA, evalInstr, JState.setReg, AState.view, writeAddr, x86_MOV]

theorem evalInstrA_storeRsp (sa : AState) (src : JOperand) :
    evalInstrA sa (.storeMem "%rsp" 0 src) =
      { sa with mem := write64 sa.mem (sa.regs "%rsp") (src.eval sa.view) } := by
  simp [evalInstrA, evalInstr, JState.store, AState.view, writeAddr, writeVal, x86_MOV]

theorem evalInstrA_loadRsp (sa : AState) (r : String) :
    evalInstrA sa (.loadMem r "%rsp" 0) =
      { sa with regs := fun r' => if r' = r then read64 sa.mem (sa.regs "%rsp")
        else sa.regs r' } := by
  simp [evalInstrA, evalInstr, JState.setReg, AState.view, writeAddr, x86_MOV]

theorem ofInt_add_ofInt (p : BitVec 64) (a b : Int) :
    p + BitVec.ofInt 64 a + BitVec.ofInt 64 b = p + BitVec.ofInt 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofInt_add]

theorem slotAddr_zero (sp : BitVec 64) : slotAddr sp 0 = sp + BitVec.ofInt 64 (-8) := by
  simp [slotAddr]

theorem slotAddr_succ (sp : BitVec 64) (k : Nat) :
    slotAddr (sp + BitVec.ofInt 64 (-8)) k = slotAddr sp (k + 1) := by
  rw [slotAddr, slotAddr, ofInt_add_ofInt]
  congr 2
  push_cast
  omega

/-- Two distinct slots below one stack pointer are disjoint. -/
theorem disjoint8_slot (sp : BitVec 64) (j k : Nat) (hjk : j ≠ k) (hj : j < 2 ^ 32)
    (hk : k < 2 ^ 32) : Disjoint8 (slotAddr sp j) (slotAddr sp k) :=
  disjoint8_add_ofInt sp _ _ (by omega) (by omega)

/-- A word whose eight bytes agree in two memories reads back equal. -/
theorem read64_congr (m m' : AMem) (a : BitVec 64)
    (h : ∀ i : Nat, i < 8 → m' (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    read64 m' a = read64 m a := by
  have h0 : m' a = m a := by simpa using h 0 (by decide)
  simp only [read64, h0, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem runBlockA_pushI (t : AState) (r : String) (hr : r ≠ "%rsp") :
    runBlockA t (pushI r) =
      { regs := (setRsp t (slotAddr (t.regs "%rsp") 0)).regs
        flags := t.flags
        mem := write64 t.mem (slotAddr (t.regs "%rsp") 0) (t.regs r) } := by
  simp only [pushI, runBlockA_cons, runBlockA_nil, evalInstrA_rspAdd, evalInstrA_storeRsp,
    slotAddr_zero]
  simp [setRsp, AState.view, hr]

theorem runBlockA_popI (t : AState) (r : String) (hr : r ≠ "%rsp") :
    runBlockA t (popI r) =
      { regs := fun r' => if r' = "%rsp" then t.regs "%rsp" + BitVec.ofInt 64 8
          else if r' = r then read64 t.mem (t.regs "%rsp") else t.regs r'
        flags := t.flags
        mem := t.mem } := by
  simp only [popI, runBlockA_cons, runBlockA_nil, evalInstrA_rspAdd, evalInstrA_loadRsp]
  simp only [setRsp, Ne.symm hr, if_false]

/-! ## The pushes -/

/-- `s` is `t` after the pushes of `rs` and the allocation of `n` bytes. -/
structure Pushed (t s : AState) (rs : List String) (n : Nat) : Prop where
  /-- `%rsp` below the saved slots and the allocation. -/
  rsp : s.regs "%rsp" = t.regs "%rsp" + BitVec.ofInt 64 (-(8 * (rs.length : Int) + n))
  /-- The other registers. -/
  regs : ∀ r, r ≠ "%rsp" → s.regs r = t.regs r
  /-- The flags. -/
  flags : s.flags = t.flags
  /-- The memory outside the saved slots. -/
  mem : ∀ x, (∀ k, k < rs.length → ¬ InRange8 (slotAddr (t.regs "%rsp") k) x) →
    s.mem x = t.mem x
  /-- The saved slots. -/
  slot : ∀ (k : Nat) (hk : k < rs.length),
    read64 s.mem (slotAddr (t.regs "%rsp") k) = t.regs rs[k]

theorem runBlockA_allocI (t : AState) (n : Nat) :
    runBlockA t (allocI n) = setRsp t (t.regs "%rsp" + BitVec.ofInt 64 (-(n : Int))) := by
  unfold allocI
  split
  · subst_vars
    cases t
    simp only [setRsp, runBlockA_nil, AState.mk.injEq, and_true]
    funext r
    by_cases h : r = "%rsp" <;> simp [h]
  · simp [evalInstrA_rspAdd]

theorem runBlockA_releaseI (t : AState) (n : Nat) :
    runBlockA t (releaseI n) = setRsp t (t.regs "%rsp" + BitVec.ofInt 64 (n : Int)) := by
  unfold releaseI
  split
  · subst_vars
    cases t
    simp only [setRsp, runBlockA_nil, AState.mk.injEq, and_true]
    funext r
    by_cases h : r = "%rsp" <;> simp [h]
  · simp [evalInstrA_rspAdd]

/-- **The prologue.** From any state, the pushes of `rs` and the allocation of `n` bytes
    leave the state `Pushed` describes. -/
theorem pushed_framePro (n : Nat) :
    ∀ (rs : List String) (t : AState), "%rsp" ∉ rs → rs.length < 2 ^ 32 →
      Pushed t (runBlockA t (framePro rs n)) rs n := by
  intro rs
  induction rs with
  | nil =>
    intro t _ _
    rw [framePro, pushSeq, List.nil_append, runBlockA_allocI]
    refine ⟨by simp [setRsp], fun r hr => by simp [setRsp, hr], rfl, fun x _ => rfl,
      fun k hk => absurd hk (by simp)⟩
  | cons r rs ih =>
    intro t hr hlen
    have hr0 : r ≠ "%rsp" := fun h => hr (h ▸ List.mem_cons_self)
    have hr1 : "%rsp" ∉ rs := fun h => hr (List.mem_cons_of_mem _ h)
    have hl : rs.length < 2 ^ 32 := by simp at hlen; omega
    have e : runBlockA t (framePro (r :: rs) n)
        = runBlockA (runBlockA t (pushI r)) (framePro rs n) := by
      rw [← runBlockA_append]; simp [framePro, pushSeq]
    rw [e]
    have hp := runBlockA_pushI t r hr0
    set t' := runBlockA t (pushI r) with ht'
    have t'rsp : t'.regs "%rsp" = t.regs "%rsp" + BitVec.ofInt 64 (-8) := by
      rw [hp]; simp [setRsp, slotAddr_zero]
    have t'regs : ∀ q, q ≠ "%rsp" → t'.regs q = t.regs q := by
      intro q hq; rw [hp]; simp [setRsp, hq]
    have t'mem : t'.mem = write64 t.mem (slotAddr (t.regs "%rsp") 0) (t.regs r) := by rw [hp]
    have I := ih t' hr1 hl
    have hslot : ∀ k, slotAddr (t'.regs "%rsp") k = slotAddr (t.regs "%rsp") (k + 1) :=
      fun k => by rw [t'rsp, slotAddr_succ]
    refine ⟨?_, fun q hq => (I.regs q hq).trans (t'regs q hq), ?_, ?_, ?_⟩
    · rw [I.rsp, t'rsp, ofInt_add_ofInt]
      congr 2
      simp only [List.length_cons]
      push_cast
      omega
    · rw [I.flags, hp]
    · intro x hx
      rw [I.mem x (fun k hk => by rw [hslot]; exact hx (k + 1) (by simp; omega)), t'mem]
      exact write64_of_not_inRange _ _ _ _ (hx 0 (by simp))
    · intro k hk
      cases k with
      | zero =>
        have hb : ∀ i : Nat, i < 8 →
            (runBlockA t' (framePro rs n)).mem (slotAddr (t.regs "%rsp") 0 + BitVec.ofNat 64 i)
              = t'.mem (slotAddr (t.regs "%rsp") 0 + BitVec.ofNat 64 i) := by
          intro i hi
          refine I.mem _ fun k hk' => ?_
          rw [hslot]
          exact not_inRange_of_disjoint _ _ i
            (disjoint8_slot _ _ _ (by omega) (by simp at hlen; omega) (by omega)) hi
        rw [read64_congr _ _ _ hb, t'mem, read64_write64_same]
        rfl
      | succ k =>
        have h := I.slot k (by simp at hk; omega)
        rw [hslot] at h
        rw [h, t'regs _ (fun he => hr1 (he ▸ List.getElem_mem _))]
        rfl

/-! ## The pops -/

/-- `s` is the state after the release and the pops of a frame entered at `t` whose body
    left `u`: `%rsp` and the registers of `rs` as at `t`, everything else as at `u`. -/
structure Popped (t u s : AState) (rs : List String) : Prop where
  /-- `%rsp`. -/
  rsp : s.regs "%rsp" = t.regs "%rsp"
  /-- The saved registers. -/
  saved : ∀ r ∈ rs, s.regs r = t.regs r
  /-- The other registers. -/
  other : ∀ r, r ∉ rs → r ≠ "%rsp" → s.regs r = u.regs r
  /-- The flags. -/
  flags : s.flags = u.flags
  /-- The memory. -/
  mem : s.mem = u.mem

/-- **The epilogue.** After the prologue from `t` and a body `f` that keeps `%rsp` and the
    words of the saved slots, the release and the pops leave the state `Popped`
    describes. -/
theorem popped_frameEpi (n : Nat) (f : AState → AState) :
    ∀ (rs : List String) (t : AState), "%rsp" ∉ rs → rs.Nodup → rs.length < 2 ^ 32 →
      (f (runBlockA t (framePro rs n))).regs "%rsp"
        = (runBlockA t (framePro rs n)).regs "%rsp" →
      (∀ k, k < rs.length →
        read64 (f (runBlockA t (framePro rs n))).mem (slotAddr (t.regs "%rsp") k)
          = read64 (runBlockA t (framePro rs n)).mem (slotAddr (t.regs "%rsp") k)) →
      Popped t (f (runBlockA t (framePro rs n)))
        (runBlockA (f (runBlockA t (framePro rs n))) (frameEpi rs n)) rs := by
  intro rs
  induction rs with
  | nil =>
    intro t _ _ _ hf _
    have P := pushed_framePro n [] t (by simp) (by simp)
    set u := f (runBlockA t (framePro [] n))
    rw [frameEpi, popSeq, List.append_nil, runBlockA_releaseI]
    refine ⟨?_, fun r hr => absurd hr (by simp), fun r _ hr => by simp [setRsp, hr], rfl, rfl⟩
    simp only [setRsp]
    rw [hf, P.rsp, ofInt_add_ofInt, List.length_nil,
      show -(8 * ((0 : Nat) : Int) + (n : Int)) + (n : Int) = 0 by omega]
    simp
  | cons r rs ih =>
    intro t hr hnd hlen hf hs
    have hr0 : r ≠ "%rsp" := fun h => hr (h ▸ List.mem_cons_self)
    have hr1 : "%rsp" ∉ rs := fun h => hr (List.mem_cons_of_mem _ h)
    have hl : rs.length < 2 ^ 32 := by simp at hlen; omega
    have hrr : r ∉ rs := (List.nodup_cons.1 hnd).1
    have e : runBlockA t (framePro (r :: rs) n)
        = runBlockA (runBlockA t (pushI r)) (framePro rs n) := by
      rw [← runBlockA_append]; simp [framePro, pushSeq]
    have P := pushed_framePro n (r :: rs) t hr hlen
    rw [e] at hf hs P ⊢
    have hp := runBlockA_pushI t r hr0
    set t' := runBlockA t (pushI r) with ht'
    set u := f (runBlockA t' (framePro rs n)) with hu
    have t'rsp : t'.regs "%rsp" = t.regs "%rsp" + BitVec.ofInt 64 (-8) := by
      rw [hp]; simp [setRsp, slotAddr_zero]
    have t'regs : ∀ q, q ≠ "%rsp" → t'.regs q = t.regs q := by
      intro q hq; rw [hp]; simp [setRsp, hq]
    have I := ih t' hr1 (List.nodup_cons.1 hnd).2 hl hf (fun k hk => by
      rw [t'rsp, slotAddr_succ]; exact hs (k + 1) (by simp; omega))
    have e2 : frameEpi (r :: rs) n = frameEpi rs n ++ popI r := by
      simp [frameEpi, popSeq]
    rw [e2, runBlockA_append, runBlockA_popI _ _ hr0]
    set s' := runBlockA u (frameEpi rs n)
    refine ⟨?_, ?_, ?_, I.flags, I.mem⟩
    · simp only
      rw [I.rsp, t'rsp, ofInt_add_ofInt]
      simp
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · simp only [if_neg hr0]
        rw [I.rsp, I.mem, t'rsp, ← slotAddr_zero, hs 0 (by simp), P.slot 0 (by simp)]
        rfl
      · have hq0 : q ≠ "%rsp" := fun h => hr1 (h ▸ hq)
        have hqr : q ≠ r := fun h => hrr (h ▸ hq)
        simp only [if_neg hq0, if_neg hqr]
        rw [I.saved q hq, t'regs q hq0]
    · intro q hq hq0
      have hqr : q ≠ r := fun h => hq (h ▸ List.mem_cons_self)
      simp only [if_neg hq0, if_neg hqr]
      exact I.other q (fun h => hq (List.mem_cons_of_mem _ h)) hq0

/-! ## The call -/

theorem runBlockA_callEntry (sa : AState) (ra : BitVec 64) :
    runBlockA sa (callEntry ra) =
      { regs := (setRsp sa (slotAddr (sa.regs "%rsp") 0)).regs
        flags := sa.flags
        mem := write64 sa.mem (slotAddr (sa.regs "%rsp") 0) ra } := by
  simp only [callEntry, runBlockA_cons, runBlockA_nil, evalInstrA_rspAdd, evalInstrA_storeRsp,
    slotAddr_zero]
  simp [setRsp]

/-- `E` is the state at the start of the body of a call made at `sa` whose prologue pushes
    `rs` and allocates `n` bytes. -/
structure Entered (sa E : AState) (rs : List String) (n : Nat) (ra : BitVec 64) : Prop where
  /-- `%rsp` below the return address, the saved slots and the allocation. -/
  rsp : E.regs "%rsp"
    = sa.regs "%rsp" + BitVec.ofInt 64 (-(8 * ((rs.length : Int) + 1) + n))
  /-- The other registers. -/
  regs : ∀ r, r ≠ "%rsp" → E.regs r = sa.regs r
  /-- The flags. -/
  flags : E.flags = sa.flags
  /-- The memory outside the return-address slot and the saved slots. -/
  mem : ∀ x, (∀ k, k < rs.length + 1 → ¬ InRange8 (slotAddr (sa.regs "%rsp") k) x) →
    E.mem x = sa.mem x
  /-- The return address. -/
  ret : read64 E.mem (slotAddr (sa.regs "%rsp") 0) = ra
  /-- The saved slots. -/
  slot : ∀ (k : Nat) (hk : k < rs.length),
    read64 E.mem (slotAddr (sa.regs "%rsp") (k + 1)) = sa.regs rs[k]

/-- A word disjoint from the return-address slot and the saved slots reads back at the
    start of the body as at the call. -/
theorem Entered.read64_eq {sa E : AState} {rs : List String} {n : Nat} {ra : BitVec 64}
    (h : Entered sa E rs n ra) (b : BitVec 64)
    (hb : ∀ k, k < rs.length + 1 → Disjoint8 (slotAddr (sa.regs "%rsp") k) b) :
    read64 E.mem b = read64 sa.mem b :=
  read64_congr _ _ _ fun i hi =>
    h.mem _ fun k hk => not_inRange_of_disjoint _ _ i (hb k hk) hi

theorem entryState_eq (rs : List String) (n : Nat) (ra : BitVec 64) (sa : AState) :
    entryState (framePro rs n) ra sa
      = runBlockA (runBlockA sa (callEntry ra)) (framePro rs n) :=
  runBlockA_append _ _ _

/-- **The state at the start of the body.** -/
theorem entered (rs : List String) (n : Nat) (ra : BitVec 64) (sa : AState)
    (hr : "%rsp" ∉ rs) (hlen : rs.length < 2 ^ 32) :
    Entered sa (entryState (framePro rs n) ra sa) rs n ra := by
  rw [entryState_eq]
  have hp := runBlockA_callEntry sa ra
  set t := runBlockA sa (callEntry ra) with ht
  have trsp : t.regs "%rsp" = sa.regs "%rsp" + BitVec.ofInt 64 (-8) := by
    rw [hp]; simp [setRsp, slotAddr_zero]
  have tregs : ∀ q, q ≠ "%rsp" → t.regs q = sa.regs q := by
    intro q hq; rw [hp]; simp [setRsp, hq]
  have tmem : t.mem = write64 sa.mem (slotAddr (sa.regs "%rsp") 0) ra := by rw [hp]
  have P := pushed_framePro n rs t hr hlen
  have hslot : ∀ k, slotAddr (t.regs "%rsp") k = slotAddr (sa.regs "%rsp") (k + 1) :=
    fun k => by rw [trsp, slotAddr_succ]
  refine ⟨?_, fun q hq => (P.regs q hq).trans (tregs q hq), by rw [P.flags, hp], ?_, ?_, ?_⟩
  · rw [P.rsp, trsp, ofInt_add_ofInt]
    congr 2
    omega
  · intro x hx
    rw [P.mem x (fun k hk => by rw [hslot]; exact hx (k + 1) (by omega)), tmem]
    exact write64_of_not_inRange _ _ _ _ (hx 0 (by omega))
  · have hb : ∀ i : Nat, i < 8 →
        (runBlockA t (framePro rs n)).mem (slotAddr (sa.regs "%rsp") 0 + BitVec.ofNat 64 i)
          = t.mem (slotAddr (sa.regs "%rsp") 0 + BitVec.ofNat 64 i) := by
      intro i hi
      refine P.mem _ fun k hk => ?_
      rw [hslot]
      exact not_inRange_of_disjoint _ _ i
        (disjoint8_slot _ _ _ (by omega) (by omega) (by omega)) hi
    rw [read64_congr _ _ _ hb, tmem, read64_write64_same]
  · intro k hk
    rw [← hslot, P.slot k hk, tregs _ (fun he => hr (he ▸ List.getElem_mem _))]

/-- **The call.** For pushed registers `rs` without duplicates and without `%rsp`, and a
    body `f` that keeps `%rsp` and the words of the saved slots, the call returns `%rsp`
    and each register of `rs` at its value at the call, and every other register, the
    flags and the memory as the body leaves them. -/
theorem framedCall_popped (rs : List String) (n : Nat) (f : AState → AState)
    (ra : BitVec 64) (sa : AState) (hr : "%rsp" ∉ rs) (hnd : rs.Nodup)
    (hlen : rs.length < 2 ^ 32)
    (hf : (f (entryState (framePro rs n) ra sa)).regs "%rsp"
      = (entryState (framePro rs n) ra sa).regs "%rsp")
    (hs : ∀ k, k < rs.length →
      read64 (f (entryState (framePro rs n) ra sa)).mem (slotAddr (sa.regs "%rsp") (k + 1))
        = read64 (entryState (framePro rs n) ra sa).mem
          (slotAddr (sa.regs "%rsp") (k + 1))) :
    Popped sa (f (entryState (framePro rs n) ra sa))
      (framedCall (framePro rs n) (frameEpi rs n) f ra sa) rs := by
  have hp := runBlockA_callEntry sa ra
  have trsp : (runBlockA sa (callEntry ra)).regs "%rsp"
      = sa.regs "%rsp" + BitVec.ofInt 64 (-8) := by
    rw [hp]; simp [setRsp, slotAddr_zero]
  have tregs : ∀ q, q ≠ "%rsp" → (runBlockA sa (callEntry ra)).regs q = sa.regs q := by
    intro q hq; rw [hp]; simp [setRsp, hq]
  rw [framedCall, entryState_eq] at *
  have I := popped_frameEpi n f rs _ hr hnd hlen hf (fun k hk => by
    rw [trsp, slotAddr_succ]; exact hs k hk)
  rw [runBlockA_append, retI, runBlockA_cons, runBlockA_nil, evalInstrA_rspAdd]
  refine ⟨?_, fun q hq => ?_, fun q hq hq0 => ?_, I.flags, I.mem⟩
  · simp only [setRsp, if_true]
    rw [I.rsp, trsp, ofInt_add_ofInt]
    simp
  · have hq0 : q ≠ "%rsp" := fun h => hr (h ▸ hq)
    simp only [setRsp, if_neg hq0]
    rw [I.saved q hq, tregs q hq0]
  · simp only [setRsp, if_neg hq0]
    exact I.other q hq hq0

/-! ## Straight-line bodies -/

/-- A register that no instruction of a block may write keeps its value. -/
theorem runBlockA_regs_of_all (sa : AState) (blk : List (JInstr 64)) (r : String)
    (h : blk.all (fun i => decide (r ∉ dsts i)) = true) :
    (runBlockA sa blk).regs r = sa.regs r := by
  induction blk generalizing sa with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [runBlockA_cons, ih _ h.2]
    exact evalInstr_regs_of_not_mem_dsts sa.view i r h.1

end CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame
