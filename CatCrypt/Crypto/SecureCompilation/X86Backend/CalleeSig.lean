/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak

/-!
# Callees as run relations, and runs with a callee as an oracle

A callee of a linked call is a relation `CalleeRun` between the state at its entry, a
leakage trace and the state at its return. The entry state is the caller's state after the
stack operations of the call (`LprogBytesDecode.callOps`); the return state is the state
before the stack operation of the return (`LprogBytesDecode.retOps`). The relation is not
tied to an instruction list of the byte machine: the leaky run of a decoded block is one
instance (`runOf`), and a kernel that uses registers outside `AState` is another, given by
its own theorems.

`CalleeSig` is the interface of a callee and `CalleeSpec X c` states that the relation `X`
meets it. `HaltsO M O prog` is the halting run of `prog` in which a `call t` is answered by
the relation `O t` on states. With the oracle that never answers it is
`RInstrSemantics.Halts` (`haltsO_empty_iff`); with an oracle whose answers are runs of a
block `q` it gives `RInstrSemantics.HaltsC` of the program linked with `q`
(`haltsC_linked_of_haltsO`, `haltsC_append_of_haltsO`).

## Main results

* `CalleeRun`, `CalleeSig`, `CalleeSpec`: a callee and its specification.
* `runOf`, `oracleAt`: the callee of a decoded block, and the oracle of one target.
* `HaltsO`: halting runs with calls answered by an oracle.
* `haltsO_empty_iff`: at the oracle that never answers, `HaltsO` is `Halts`.
* `haltsC_of_haltsO`: an oracle whose answers are runs of the program gives `HaltsC`.
* `haltsO_of_haltsC`: `HaltsC` is `HaltsO` at the oracle of its own runs.
* `haltsC_linked_of_haltsO`, `haltsC_append_of_haltsO`, `haltsC_append_of_haltsO_runOf`:
  an oracle whose answers are runs of a block without `call` gives `HaltsC` of the program
  linked with a relocated copy of the block.
* `haltsO_call_of_spec`: a call to a specified callee continues after the call.
* `keepCheckB`, `keepCheck_sound`: a Boolean check on a decoded block of the form
  `leaq -F(%rsp), %rsp ; body ; leaq F(%rsp), %rsp ; ret`, under which every leaky run
  restores the stack register, keeps the registers outside a clobber set and keeps the
  bytes outside the `F` bytes below the entry stack register.
* `calleeSpec_of_keepCheck`: `CalleeSpec` of the leaky run of a decoded block from the keep
  check, a halting run with a postcondition and equality of traces.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Callee

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (evalInstrA_leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (runL_det)

/-! ## 1. The callee and its specification -/

/-- A callee as a relation on the caller's machine: `X s t s'` holds when the callee,
    entered in the state `s` after the stack operations of the call, returns in the state
    `s'` with leakage trace `t`. -/
abbrev CalleeRun : Type := AState → List CTLeak → AState → Prop

/-- The interface of a callee. -/
structure CalleeSig where
  /-- The names of the argument registers, in order. -/
  args : List String
  /-- The name of the result register, for a callee that returns a word. -/
  res : Option String
  /-- The registers the callee may change. -/
  clob : String → Bool
  /-- The precondition on the state at the callee's entry. -/
  pre : AState → Prop
  /-- The addresses the callee may write, from the state at its entry. -/
  foot : AState → BitVec 64 → Prop
  /-- The relation between the entry state and the return state: the result register and
      the memory inside the footprint. -/
  post : AState → AState → Prop
  /-- The relation between two entry states that agree on the public data. -/
  pub : AState → AState → Prop

/-- **The specification of a callee.** The relation `X` meets the interface `c`.

    * The callee is a relation on the caller's states, so a kernel that computes in
      registers outside `AState` (vector and mask registers) is specified by its effect on
      the general-purpose registers, the flags and the memory.
    * A result that is a function of memory, and the contents of an array the callee
      writes for its caller, are stated by `c.post`, which reads the memory of the entry
      state and of the return state inside `c.foot`.
    * Memory inside the footprint is read back through `c.post`; memory outside it is kept
      (`frame`). The footprint depends on the entry state, so it covers both a frame below
      the entry stack pointer and the words at a pointer argument.
    * Leakage is the trace of `X`; two runs from entry states related by `c.pub` have equal
      traces (`ct`).
    * The clobber set is the parameter `c.clob`: a register outside it is kept (`keep`),
      the stack register is restored (`rsp`), and nothing is stated about the flags or
      about a register inside it. -/
structure CalleeSpec (X : CalleeRun) (c : CalleeSig) : Prop where
  /-- The callee returns from every entry state that satisfies the precondition. -/
  halts : ∀ s, c.pre s → ∃ t s', X s t s'
  /-- The stack register at the return is the stack register at the entry. -/
  rsp : ∀ s t s', c.pre s → X s t s' → s'.regs "%rsp" = s.regs "%rsp"
  /-- A register outside the clobber set is kept. -/
  keep : ∀ s t s', c.pre s → X s t s' → ∀ r, c.clob r = false → s'.regs r = s.regs r
  /-- A byte outside the footprint is kept. -/
  frame : ∀ s t s', c.pre s → X s t s' → ∀ x, ¬ c.foot s x → s'.mem x = s.mem x
  /-- The postcondition holds at every return. -/
  post : ∀ s t s', c.pre s → X s t s' → c.post s s'
  /-- Two runs from publicly related entry states have equal traces. -/
  ct : ∀ s₁ s₂ t₁ t₂ s₁' s₂', c.pre s₁ → c.pre s₂ → c.pub s₁ s₂ →
    X s₁ t₁ s₁' → X s₂ t₂ s₂' → t₁ = t₂

/-- The callee of a decoded block `q` under the leakage regime `r`: its leaky runs from
    index `0` to its `ret`. -/
def runOf (r : DoitRegime) (q : List RInstr) : CalleeRun :=
  fun s t s' => RunL r (fun _ _ => True) q 0 s t s'

/-- The oracle that answers a call to the target `tgt` by the callee `X`, forgetting the
    trace, and answers no other target. -/
def oracleAt (tgt : Nat) (X : CalleeRun) : Nat → AState → AState → Prop :=
  fun t s s' => t = tgt ∧ ∃ tr, X s tr s'

/-! ## 2. Runs with calls answered by an oracle -/

variable {σ : Type}

/-- The program halts from `pc` in `s''`, each call answered by the oracle: a continuing
    `step`, a `ret` that ends the run, or a `call t` for which `O t` relates the state after
    `LprogBytesDecode.callOps` to a state `sc`, the run continuing at the next index on the
    state after `LprogBytesDecode.retOps`. The callee of `RInstrSemantics.HaltsC` is a
    nested run of the same instruction list from index `t`; here index `t` need not hold
    an instruction, and `O t` is any relation on states. -/
inductive HaltsO (M : Machine σ) (O : Nat → σ → σ → Prop) (prog : List RInstr) :
    Nat → σ → σ → Prop
  | ret {pc : Nat} {s : σ} (h : prog[pc]? = some .ret) : HaltsO M O prog pc s s
  | go {pc : Nat} {s : σ} {pc' : Nat} {s' s'' : σ} (h : RInstrSemantics.step M prog pc s = some (.go pc' s'))
      (hr : HaltsO M O prog pc' s' s'') : HaltsO M O prog pc s s''
  | call {pc t : Nat} {s sc s'' : σ} (h : prog[pc]? = some (.call t))
      (hc : O t ((callOps (pc + 1)).foldl M.exec s) sc)
      (hr : HaltsO M O prog (pc + 1) (retOps.foldl M.exec sc) s'') :
      HaltsO M O prog pc s s''

/-- A run under an oracle is a run under every oracle with more answers. -/
theorem HaltsO.mono {M : Machine σ} {O O' : Nat → σ → σ → Prop} {prog : List RInstr}
    (hO : ∀ t s sc, O t s sc → O' t s sc) {pc : Nat} {s s' : σ}
    (h : HaltsO M O prog pc s s') : HaltsO M O' prog pc s s' := by
  induction h with
  | ret h => exact .ret h
  | go h _ ih => exact .go h ih
  | call h hc _ ih => exact .call h (hO _ _ _ hc) ih

/-- **At the oracle that never answers, `HaltsO` is `Halts`.** -/
theorem haltsO_empty_iff (M : Machine σ) (prog : List RInstr) (pc : Nat) (s s' : σ) :
    HaltsO M (fun _ _ _ => False) prog pc s s' ↔ Halts M prog pc s s' := by
  constructor
  · intro h
    induction h with
    | ret h => exact ⟨_, .refl _ _, h⟩
    | go h _ ih =>
      obtain ⟨pc', hr, hret⟩ := ih
      exact ⟨pc', .next h hr, hret⟩
    | call _ hc _ _ => exact hc.elim
  · rintro ⟨pc', hr, hret⟩
    induction hr with
    | refl => exact .ret hret
    | next hs _ ih => exact .go hs (ih hret)

/-- A call-free halting run is a run under every oracle. -/
theorem haltsO_of_halts {M : Machine σ} (O : Nat → σ → σ → Prop) {prog : List RInstr}
    {pc : Nat} {s s' : σ} (h : Halts M prog pc s s') : HaltsO M O prog pc s s' :=
  HaltsO.mono (fun _ _ _ hf => hf.elim) ((haltsO_empty_iff M prog pc s s').mpr h)

/-- **An oracle whose answers are runs of the program.** If every answer of `O` at a
    target `t` is a run of `prog` through calls from `t`, a run under `O` is a run through
    calls. -/
theorem haltsC_of_haltsO {M : Machine σ} {O : Nat → σ → σ → Prop} {prog : List RInstr}
    (hO : ∀ t s sc, O t s sc → HaltsC M prog t s sc) {pc : Nat} {s s' : σ}
    (h : HaltsO M O prog pc s s') : HaltsC M prog pc s s' := by
  induction h with
  | ret h => exact .ret h
  | go h _ ih => exact .go h ih
  | call h hc _ ih => exact .call h (hO _ _ _ hc) ih

/-- A run through calls is a run under the oracle of the program's own runs. -/
theorem haltsO_of_haltsC {M : Machine σ} {prog : List RInstr} {pc : Nat} {s s' : σ}
    (h : HaltsC M prog pc s s') : HaltsO M (fun t => HaltsC M prog t) prog pc s s' := by
  induction h with
  | ret h => exact .ret h
  | go h _ ih => exact .go h ih
  | call h hc _ _ ihr => exact .call h hc ihr

/-- **The linked program of a run under an oracle.** In
    `pre ++ shiftProg pre.length q ++ post` with `q` a block without `call`, let every
    answer of `O` be at the target `pre.length` and be a run of `q` from index `0`. A run
    of the linked program under `O` is a run of it through calls. -/
theorem haltsC_linked_of_haltsO (M : Machine σ) (pre q post : List RInstr)
    (hq : ∀ tg, RInstr.call tg ∉ q) {O : Nat → σ → σ → Prop}
    (hO : ∀ t s sc, O t s sc → t = pre.length ∧ HaltsC M q 0 s sc) {pc : Nat} {s s' : σ}
    (h : HaltsO M O (pre ++ shiftProg pre.length q ++ post) pc s s') :
    HaltsC M (pre ++ shiftProg pre.length q ++ post) pc s s' := by
  refine haltsC_of_haltsO (fun t s sc ho => ?_) h
  obtain ⟨rfl, hrun⟩ := hO t s sc ho
  exact haltsC_relocated M pre q post hq hrun

/-- A step of a program is a step of the program with instructions appended. -/
theorem step_append_left (M : Machine σ) (p ext : List RInstr) {pc : Nat} {s : σ}
    {n : Next σ} (h : RInstrSemantics.step M p pc s = some n) :
    RInstrSemantics.step M (p ++ ext) pc s = some n := by
  have hlt : pc < p.length := by
    by_contra hn
    simp [RInstrSemantics.step, List.getElem?_eq_none (Nat.le_of_not_gt hn)] at h
  rw [← h]
  simp only [RInstrSemantics.step, List.getElem?_append_left hlt]

/-- A run under an oracle is a run of the program with instructions appended. -/
theorem HaltsO.append_left {M : Machine σ} {O : Nat → σ → σ → Prop} {p : List RInstr}
    (ext : List RInstr) {pc : Nat} {s s' : σ} (h : HaltsO M O p pc s s') :
    HaltsO M O (p ++ ext) pc s s' := by
  induction h with
  | ret h =>
    exact .ret (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h)
  | go h _ ih => exact .go (step_append_left M p ext h) ih
  | call h hc _ ih =>
    exact .call (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h)
      hc ih

/-- **Linking a caller with its callee.** Let `p` run under an oracle `O` whose every
    answer is at the target `p.length` and is a run of the block `q` without `call`. Then
    `p` followed by the relocated copy of `q` runs through calls to the same state. The
    target `p.length` holds no instruction of `p`. -/
theorem haltsC_append_of_haltsO (M : Machine σ) (p q : List RInstr)
    (hq : ∀ tg, RInstr.call tg ∉ q) {O : Nat → σ → σ → Prop}
    (hO : ∀ t s sc, O t s sc → t = p.length ∧ HaltsC M q 0 s sc) {pc : Nat} {s s' : σ}
    (h : HaltsO M O p pc s s') : HaltsC M (p ++ shiftProg p.length q) pc s s' := by
  have h' := haltsC_linked_of_haltsO M p q [] hq hO
    (by simpa using h.append_left (shiftProg p.length q))
  simpa using h'

/-- **Linking a caller with a decoded callee block.** A run of `p` under the oracle of the
    leaky runs of `q` at the target `p.length` is a run through calls of `p` followed by
    the relocated copy of `q`. -/
theorem haltsC_append_of_haltsO_runOf (r : DoitRegime) (p q : List RInstr)
    (hq : ∀ tg, RInstr.call tg ∉ q) {pc : Nat} {s s' : AState}
    (h : HaltsO aMachine (oracleAt p.length (runOf r q)) p pc s s') :
    HaltsC aMachine (p ++ shiftProg p.length q) pc s s' :=
  haltsC_append_of_haltsO aMachine p q hq
    (fun _ _ _ ho => ⟨ho.1, ho.2.elim fun _ hrun => RunL.halts hrun⟩) h

/-! ## 3. A call to a specified callee -/

/-- **A call to a specified callee under its oracle.** Let index `pc` of `prog` hold a
    call to `tgt`, and let the state after the stack operations of the call satisfy the
    precondition of a callee `X` with `CalleeSpec X c`. There is a return state `sc` of the
    callee, with the stack register, the registers outside the clobber set and the memory
    outside the footprint as at the entry and with the postcondition, such that every run
    from `pc + 1` on `sc` after the stack operation of the return extends to a run from
    `pc`. -/
theorem haltsO_call_of_spec {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {prog : List RInstr} {pc tgt : Nat} (hcall : prog[pc]? = some (.call tgt)) (s : AState)
    (hpre : c.pre ((callOps (pc + 1)).foldl aMachine.exec s)) :
    ∃ sc : AState,
      sc.regs "%rsp" = ((callOps (pc + 1)).foldl aMachine.exec s).regs "%rsp"
      ∧ (∀ r, c.clob r = false →
          sc.regs r = ((callOps (pc + 1)).foldl aMachine.exec s).regs r)
      ∧ (∀ x, ¬ c.foot ((callOps (pc + 1)).foldl aMachine.exec s) x →
          sc.mem x = ((callOps (pc + 1)).foldl aMachine.exec s).mem x)
      ∧ c.post ((callOps (pc + 1)).foldl aMachine.exec s) sc
      ∧ ∀ s'', HaltsO aMachine (oracleAt tgt X) prog (pc + 1)
            (retOps.foldl aMachine.exec sc) s'' →
          HaltsO aMachine (oracleAt tgt X) prog pc s s'' := by
  obtain ⟨t, sc, hrun⟩ := hX.halts _ hpre
  exact ⟨sc, hX.rsp _ t sc hpre hrun, hX.keep _ t sc hpre hrun, hX.frame _ t sc hpre hrun,
    hX.post _ t sc hpre hrun, fun s'' hr => .call hcall ⟨rfl, t, hrun⟩ hr⟩

/-! ## 4. The keep check on a decoded block -/

/-- The address `x` lies in the `F` bytes below the address `e`. -/
def InFrame (e : BitVec 64) (F : Nat) (x : BitVec 64) : Prop :=
  (x - (e + BitVec.ofInt 64 (-(F : Int)))).toNat < F

/-- The instruction is `leaq d(%rsp), %rsp`. -/
def isLeaRsp (d : Int) : RInstr → Bool
  | .op (.lea dst base idx sc off) =>
      dst == "%rsp" && base == "%rsp" && idx == "%rsp" && sc == 0 && off == d
  | _ => false

theorem eq_of_isLeaRsp {d : Int} {ri : RInstr} (h : isLeaRsp d ri = true) :
    ri = .op (leaFrame d) := by
  cases ri with
  | op i =>
    cases i <;> simp only [isLeaRsp, Bool.false_eq_true] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
    rfl
  | _ => simp [isLeaRsp] at h

/-- A store of the instruction, if any, is to a word of the frame: the eight bytes at a
    displacement `o` from the stack register with `0 ≤ o` and `o + 8 ≤ F`. An indexed store
    is refused. -/
def storeOkB (F : Nat) : JInstr 64 → Bool
  | .storeMem b o _ => b == "%rsp" && decide (0 ≤ o) && decide (o + 8 ≤ (F : Int))
  | .addToMem b o _ => b == "%rsp" && decide (0 ≤ o) && decide (o + 8 ≤ (F : Int))
  | .storeMemIdx .. => false
  | _ => true

/-- The check of an instruction between the two frame instructions of a block of length
    `n`: an `op` writes only registers of `clob` other than the stack register and stores
    only to the frame; a branch has its target among the indices `1, …, n - 2`; `ret`,
    `push`, `pop` and `call` are refused. -/
def bodyOkB (n : Nat) (clob : String → Bool) (F : Nat) : RInstr → Bool
  | .op i => (dsts i).all (fun d => d != "%rsp" && clob d) && storeOkB F i
  | .jcc _ t => decide (1 ≤ t) && decide (t + 2 ≤ n)
  | _ => false

/-- The check of the instruction at index `k` of a block of length `n`: index `0` lowers
    the stack register by `F`, index `n - 2` raises it by `F`, index `n - 1` is `ret`, and
    every other index satisfies `bodyOkB`. -/
def instrOkB (n : Nat) (clob : String → Bool) (F : Nat) (k : Nat) (ri : RInstr) : Bool :=
  if k = 0 then isLeaRsp (-(F : Int)) ri
  else if k + 2 = n then isLeaRsp (F : Int) ri
  else if k + 1 = n then (match ri with | .ret => true | _ => false)
  else bodyOkB n clob F ri

/-- `f k x` for every instruction `x` of the list at index `k`, counted from `k₀`. -/
def allFrom (f : Nat → RInstr → Bool) : Nat → List RInstr → Bool
  | _, [] => true
  | k, ri :: l => f k ri && allFrom f (k + 1) l

theorem allFrom_getElem? {f : Nat → RInstr → Bool} :
    ∀ (l : List RInstr) (k j : Nat) (ri : RInstr), allFrom f k l = true → l[j]? = some ri →
      f (k + j) ri = true
  | [], _, _, _, _, h => by simp at h
  | x :: l, k, 0, ri, hk, h => by
    simp only [allFrom, Bool.and_eq_true] at hk
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact hk.1
  | x :: l, k, j + 1, ri, hk, h => by
    simp only [allFrom, Bool.and_eq_true] at hk
    have := allFrom_getElem? l (k + 1) j ri hk.2 (by simpa using h)
    rwa [show k + 1 + j = k + (j + 1) by omega] at this

/-- **The keep check.** The block `q` has the form
    `leaq -F(%rsp), %rsp ; body ; leaq F(%rsp), %rsp ; ret`, and every instruction of
    `body` satisfies `bodyOkB`: it writes no register outside `clob`, does not write the
    stack register, stores only to the `F` bytes of the frame, branches inside
    `body ; leaq F(%rsp), %rsp`, and is not `ret`, `push`, `pop` or `call`. -/
def keepCheckB (q : List RInstr) (clob : String → Bool) (F : Nat) : Bool :=
  decide (3 ≤ q.length) && allFrom (instrOkB q.length clob F) 0 q

/-- The invariant of a run of a checked block of length `n` entered in the state `e`: the
    stack register is that of `e` at index `0` and at the `ret`, and `F` below it at every
    other index; a register outside `clob` other than the stack register, and a byte
    outside the frame, are those of `e`. -/
def KeepInv (n : Nat) (clob : String → Bool) (F : Nat) (e : AState) (pc : Nat) (s : AState) :
    Prop :=
  s.regs "%rsp" = (if pc = 0 ∨ pc + 1 = n then e.regs "%rsp"
      else e.regs "%rsp" + BitVec.ofInt 64 (-(F : Int)))
    ∧ (∀ r, r ≠ "%rsp" → clob r = false → s.regs r = e.regs r)
    ∧ ∀ x, ¬ InFrame (e.regs "%rsp") F x → s.mem x = e.mem x

/-- A store to a word of the frame changes no byte outside the frame. -/
theorem evalInstrA_mem_of_storeOk {F : Nat} {s : AState} {i : JInstr 64} {e : BitVec 64}
    (hs : storeOkB F i = true) (hb : s.regs "%rsp" = e + BitVec.ofInt 64 (-(F : Int)))
    (x : BitVec 64) (hx : ¬ InFrame e F x) : (evalInstrA s i).mem x = s.mem x := by
  have key : ∀ o : Int, 0 ≤ o → o + 8 ≤ (F : Int) →
      ¬ InRange8 (s.regs "%rsp" + BitVec.ofInt 64 o) x := by
    intro o h0 h8 hin
    apply hx
    rw [hb] at hin
    unfold InRange8 at hin
    unfold InFrame
    generalize e + BitVec.ofInt 64 (-(F : Int)) = b at hin ⊢
    have hb' := b.isLt
    have hx' := x.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt] at hin ⊢
    omega
  cases i <;> simp only [storeOkB, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hs <;> try rfl
  all_goals
    obtain ⟨⟨rfl, h0⟩, h8⟩ := hs
    exact write64_of_not_inRange _ _ _ _ (key _ h0 h8)

/-- **The invariant along a run of a checked block.** A leaky run of a block accepted by
    `keepCheckB`, from an index and a state that satisfy `KeepInv` for the entry state `e`,
    returns in a state with the stack register of `e`, the registers of `e` outside `clob`
    and the bytes of `e` outside the frame. -/
theorem keepCheck_inv {q : List RInstr} {clob : String → Bool} {F : Nat}
    (hk : keepCheckB q clob F = true) {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    (e : AState) {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState}
    (h : RunL r ok q pc s t s') (hI : KeepInv q.length clob F e pc s) :
    s'.regs "%rsp" = e.regs "%rsp"
      ∧ (∀ r', r' ≠ "%rsp" → clob r' = false → s'.regs r' = e.regs r')
      ∧ ∀ x, ¬ InFrame (e.regs "%rsp") F x → s'.mem x = e.mem x := by
  simp only [keepCheckB, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨hn, hall⟩ := hk
  have hat : ∀ {pc : Nat} {ri : RInstr}, q[pc]? = some ri →
      instrOkB q.length clob F pc ri = true := fun {pc ri} hq => by
    simpa using allFrom_getElem? q 0 pc ri hall hq
  induction h with
  | @ret pc s hq =>
    have hc := hat hq
    obtain ⟨h1, h2, h3⟩ := hI
    have hpc : pc = 0 ∨ pc + 1 = q.length := by
      by_contra hne
      simp only [not_or] at hne
      simp only [instrOkB, hne.1, hne.2, if_false, isLeaRsp, bodyOkB] at hc
      split at hc <;> simp at hc
    rw [if_pos hpc] at h1
    exact ⟨h1, h2, h3⟩
  | @op pc s i t s' hq _ _ ih =>
    have hc := hat hq
    obtain ⟨h1, h2, h3⟩ := hI
    apply ih
    unfold instrOkB at hc
    by_cases h0 : pc = 0
    · rw [if_pos h0] at hc
      have hi := eq_of_isLeaRsp hc
      simp only [RInstr.op.injEq] at hi
      subst hi
      obtain ⟨hl, hlm⟩ := evalInstrA_leaFrame s (-(F : Int))
      rw [if_pos (Or.inl h0)] at h1
      refine ⟨?_, fun r' hr' hcl => ?_, fun x hx => ?_⟩
      · rw [hl, if_pos rfl, h1, if_neg (by omega)]
      · rw [hl, if_neg hr']; exact h2 r' hr' hcl
      · rw [hlm]; exact h3 x hx
    · rw [if_neg h0] at hc
      by_cases h2n : pc + 2 = q.length
      · rw [if_pos h2n] at hc
        have hi := eq_of_isLeaRsp hc
        simp only [RInstr.op.injEq] at hi
        subst hi
        obtain ⟨hl, hlm⟩ := evalInstrA_leaFrame s (F : Int)
        rw [if_neg (by omega)] at h1
        refine ⟨?_, fun r' hr' hcl => ?_, fun x hx => ?_⟩
        · rw [hl, if_pos rfl, h1, if_pos (Or.inr (by omega)), BitVec.add_assoc,
            ← BitVec.ofInt_add]
          simp
        · rw [hl, if_neg hr']; exact h2 r' hr' hcl
        · rw [hlm]; exact h3 x hx
      · rw [if_neg h2n] at hc
        by_cases h1n : pc + 1 = q.length
        · rw [if_pos h1n] at hc; simp at hc
        · rw [if_neg h1n] at hc
          simp only [bodyOkB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hc
          obtain ⟨hd, hst⟩ := hc
          rw [if_neg (by omega)] at h1
          have hreg : ∀ r', (evalInstrA s i).regs r' = (evalInstr s.view i).regs r' :=
            fun _ => rfl
          refine ⟨?_, fun r' hr' hcl => ?_, fun x hx => ?_⟩
          · rw [if_neg (by omega), hreg,
              evalInstr_regs_of_not_mem_dsts _ _ _ (fun hm => (hd _ hm).1 rfl)]
            exact h1
          · rw [hreg, evalInstr_regs_of_not_mem_dsts _ _ _ (fun hm => by
              have := (hd _ hm).2; rw [hcl] at this; cases this)]
            exact h2 r' hr' hcl
          · rw [evalInstrA_mem_of_storeOk hst h1 x hx]; exact h3 x hx
  | @jcc pc s cc tgt c t s' hq _ _ ih =>
    have hc := hat hq
    obtain ⟨h1, h2, h3⟩ := hI
    apply ih
    unfold instrOkB at hc
    by_cases h0 : pc = 0
    · rw [if_pos h0] at hc; simp [isLeaRsp] at hc
    · rw [if_neg h0] at hc
      by_cases h2n : pc + 2 = q.length
      · rw [if_pos h2n] at hc; simp [isLeaRsp] at hc
      · rw [if_neg h2n] at hc
        by_cases h1n : pc + 1 = q.length
        · rw [if_pos h1n] at hc; simp at hc
        · rw [if_neg h1n] at hc
          simp only [bodyOkB, Bool.and_eq_true, decide_eq_true_eq] at hc
          rw [if_neg (by omega)] at h1
          refine ⟨?_, h2, h3⟩
          rw [h1]
          split <;> rw [if_neg (by omega)]
  | @stack pc s ri ops t s' hq hops _ _ _ =>
    have hc := hat hq
    exfalso
    cases ri <;> simp only [RInstr.stackOps?, reduceCtorEq] at hops <;>
      (unfold instrOkB at hc; split_ifs at hc <;> simp [isLeaRsp, bodyOkB] at hc)
  | @call pc tgt s sc tc tr s' hq _ _ _ _ _ _ =>
    have hc := hat hq
    exfalso
    unfold instrOkB at hc
    split_ifs at hc <;> simp [isLeaRsp, bodyOkB] at hc

/-- **Soundness of the keep check.** Every leaky run of a block accepted by `keepCheckB`,
    from its first index to its `ret`, restores the stack register, keeps every register
    outside `clob` and keeps every byte outside the `F` bytes below the entry stack
    register. -/
theorem keepCheck_sound {q : List RInstr} {clob : String → Bool} {F : Nat}
    (hk : keepCheckB q clob F = true) {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {s : AState} {t : List CTLeak} {s' : AState} (h : RunL r ok q 0 s t s') :
    s'.regs "%rsp" = s.regs "%rsp"
      ∧ (∀ r', clob r' = false → s'.regs r' = s.regs r')
      ∧ ∀ x, ¬ InFrame (s.regs "%rsp") F x → s'.mem x = s.mem x := by
  obtain ⟨h1, h2, h3⟩ := keepCheck_inv hk s h
    ⟨by rw [if_pos (Or.inl rfl)], fun _ _ _ => rfl, fun _ _ => rfl⟩
  refine ⟨h1, fun r' hcl => ?_, h3⟩
  by_cases hr : r' = "%rsp"
  · rw [hr, h1]
  · exact h2 r' hr hcl

/-- A block accepted by `keepCheckB` holds no `call`. -/
theorem not_call_mem_of_keepCheck {q : List RInstr} {clob : String → Bool} {F : Nat}
    (hk : keepCheckB q clob F = true) (tg : Nat) : RInstr.call tg ∉ q := by
  simp only [keepCheckB, Bool.and_eq_true, decide_eq_true_eq] at hk
  intro hm
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  have hc : instrOkB q.length clob F j (.call tg) = true := by
    simpa using allFrom_getElem? q 0 j _ hk.2 hj
  unfold instrOkB at hc
  split_ifs at hc <;> simp [isLeaRsp, bodyOkB] at hc

/-! ## 5. The specification of a compiled scalar kernel -/

/-- **The specification of a compiled kernel from its three facts.** Let the decoded block
    `q` be accepted by `keepCheckB` with the clobber set of `c` and a frame of `F` bytes
    inside the footprint of `c`. Let `q` halt from every entry state that satisfies the
    precondition, in a state that satisfies the postcondition (the form of a value
    theorem), and let the leaky runs of `q` from publicly related entry states that satisfy
    the precondition have equal traces (the form of a constant-time theorem). Then the
    leaky run of `q` meets `c`. -/
theorem calleeSpec_of_keepCheck {r : DoitRegime} {q : List RInstr} {c : CalleeSig} {F : Nat}
    (hk : keepCheckB q c.clob F = true)
    (hfoot : ∀ s x, InFrame (s.regs "%rsp") F x → c.foot s x)
    (hrun : ∀ s, c.pre s → ∃ s', Halts aMachine q 0 s s' ∧ c.post s s')
    (hct : ConstantTimeRel (fun s₁ s₂ => c.pub s₁ s₂ ∧ c.pre s₁ ∧ c.pre s₂)
      (fun s t => ∃ s', RunL r (fun _ _ => True) q 0 s t s')) :
    CalleeSpec (runOf r q) c where
  halts s hs := by
    obtain ⟨s', hh, _⟩ := hrun s hs
    obtain ⟨t, ht⟩ := halts_runL r hh
    exact ⟨t, s', ht⟩
  rsp _ _ _ _ hX := (keepCheck_sound hk hX).1
  keep _ _ _ _ hX := (keepCheck_sound hk hX).2.1
  frame _ _ _ _ hX x hx := (keepCheck_sound hk hX).2.2 x (fun hf => hx (hfoot _ x hf))
  post s t s' hs hX := by
    obtain ⟨s₀, hh, hp⟩ := hrun s hs
    obtain ⟨t₀, ht₀⟩ := halts_runL r hh
    obtain ⟨_, rfl⟩ := runL_det ht₀ hX
    exact hp
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ := hct s₁ s₂ t₁ t₂ ⟨hp, h₁, h₂⟩ ⟨s₁', hX₁⟩ ⟨s₂', hX₂⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
