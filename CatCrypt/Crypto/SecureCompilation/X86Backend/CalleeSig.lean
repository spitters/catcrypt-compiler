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
`RInstrSemantics.HaltsNoCall` (`haltsO_empty_iff`); with an oracle whose answers are runs of a
block `q` it gives `RInstrSemantics.HaltsC` of the program linked with `q`
(`haltsC_linked_of_haltsO`, `haltsC_append_of_haltsO`).

## Main results

* `CalleeRun`, `CalleeSig`, `CalleeSpec`: a callee and its specification.
* `runOf`, `oracleAt`: the callee of a decoded block, and the oracle of one target.
* `HaltsO`: halting runs with calls answered by an oracle.
* `haltsO_empty_iff`: at the oracle that never answers, `HaltsO` is `HaltsNoCall`.
* `haltsC_of_haltsO`: an oracle whose answers are runs of the program gives `HaltsC`.
* `haltsO_of_haltsC`: `HaltsC` is `HaltsO` at the oracle of its own runs.
* `haltsC_linked_of_haltsO`, `haltsC_append_of_haltsO`, `haltsC_append_of_haltsO_runOf`:
  an oracle whose answers are runs of a block without `call` gives `HaltsC` of the program
  linked with a relocated copy of the block.
* `haltsO_call_of_spec`: a call to a specified callee continues after the call.
* `StorePol`, `KeepFoot`, `keepCheckWB`, `keepCheck_invW`, `keepCheck_soundW`: a Boolean
  check on a decoded block of the form
  `leaq -F(%rsp), %rsp ; body ; leaq F(%rsp), %rsp ; ret` under a store policy, which
  admits stores to the frame, to a red zone of at most `128` bytes below it and to out
  windows at fixed displacements from the entry values of their base registers; every leaky
  run restores the stack register, keeps the registers outside the clobber set and keeps
  the bytes outside the frame, the red zone and the out windows.
* `KFact`, `kstep`, `kstep_sound`, `kTable`, `kFacts`, `kFlowOkB`: the provenance of the
  entry values of the window base registers, a forward analysis over the block whose facts
  state that a register or a frame slot holds such a value; a store to an out window goes
  through a register that holds the entry value of the window's base register, so a base
  register may be spilled to the frame, overwritten and reloaded into another register.
* `keepCheckB`, `keepCheckB_eq`, `keepFoot_frame`: the keep check at the policy
  `StorePol.frame` of the frame alone, which needs no facts, and whose footprint is the `F`
  bytes below the entry stack register.
* `calleeSpec_of_keepCheckW`: `CalleeSpec` of the leaky run of a decoded block from the
  keep check, a halting run with a postcondition and equality of traces.
* `keptB`, `keepCands`, `keepPool`, `scratch_not_mem_keepPool`, `keepPool_eq_of_kept`,
  `keepPoolB`, `keepPoolB_spec`, `keepPoolB_keepPool`, `keepPoolB_keep`: the allocation pool
  of a caller, made of the general-purpose names kept across a call other than the reload
  scratches of the allocator, with `RDX` at index `3` when the callee keeps it, its check
  with soundness and completeness, and the preservation of the registers of a checked pool
  by a specified callee.
* `PubSummary`, `CalleeSpec.kept_agree`, `pubSummary_of_ct`, `pubSummary_of_checkCert`: the
  leakage summary of a callee, what a specified callee keeps equal between two runs, and
  the summary of a decoded block from equality of traces or from a certificate of the
  byte check.
* `OracleRun`, `tracedAt`, `tracedOf`, `oracleRun_of_haltsO`, `oracleRun_of_haltsO_oracleOf`,
  `runL_append_of_oracleRun`, `runL_append_blocks_of_oracleRun`: runs with leakage in which a
  call is answered by an oracle with traces, at one target or at the targets of several
  symbols, and the run with leakage of the linked program with the same trace.
* `SegRun`, `SegChain`, `segChain_of_oracleRun`, `segChain_trace_eq`: the segments of a
  caller between calls, and equality of the traces of two chains of segments.
* `oracleRun_trace_eqMap`, `oracleRun_trace_eq`, `linkedRun_trace_eq`,
  `linkedRun_constantTime`: equal leakage of a caller of summarised callees under the oracle,
  and constant time of the linked program.
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

/-- The oracle of the callees named `fs`: a call to the target `t` is answered by the
    callee `X f` of a symbol `f` of `fs` with `tgt f = t`, forgetting the trace. -/
def oracleOf (fs : List String) (tgt : String → Nat) (X : String → CalleeRun) :
    Nat → AState → AState → Prop :=
  fun t s s' => ∃ f ∈ fs, tgt f = t ∧ ∃ tr, X f s tr s'

/-- **The oracle of one callee.** At one symbol, a constant target and a constant callee,
    `oracleOf` answers as `oracleAt`. -/
theorem oracleOf_one (f : String) (tgt : Nat) (X : CalleeRun) (t : Nat) (s s' : AState) :
    oracleOf [f] (fun _ => tgt) (fun _ => X) t s s' ↔ oracleAt tgt X t s s' := by
  simp [oracleOf, oracleAt, eq_comm]

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

/-- **At the oracle that never answers, `HaltsO` is `HaltsNoCall`.** -/
theorem haltsO_empty_iff (M : Machine σ) (prog : List RInstr) (pc : Nat) (s s' : σ) :
    HaltsO M (fun _ _ _ => False) prog pc s s' ↔ HaltsNoCall M prog pc s s' := by
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
theorem haltsO_of_haltsNoCall {M : Machine σ} (O : Nat → σ → σ → Prop) {prog : List RInstr}
    {pc : Nat} {s s' : σ} (h : HaltsNoCall M prog pc s s') : HaltsO M O prog pc s s' :=
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

/-- **The linked program of a run under an oracle, callees in blocks.** In
    `pre ++ shiftProg pre.length Q ++ post`, let every answer of `O` at a target `t` be a
    run from index `0` of a block `q` without `call` such that `Q` is
    `A ++ shiftProg A.length q ++ B` and `t = pre.length + A.length`. A run of the linked
    program under `O` is a run of it through calls. -/
theorem haltsC_linked_of_haltsO_blocks (M : Machine σ) (pre Q post : List RInstr)
    {O : Nat → σ → σ → Prop}
    (hO : ∀ t s sc, O t s sc → ∃ A q B, Q = A ++ shiftProg A.length q ++ B ∧
      t = pre.length + A.length ∧ (∀ tg, RInstr.call tg ∉ q) ∧ HaltsC M q 0 s sc)
    {pc : Nat} {s s' : σ} (h : HaltsO M O (pre ++ shiftProg pre.length Q ++ post) pc s s') :
    HaltsC M (pre ++ shiftProg pre.length Q ++ post) pc s s' := by
  refine haltsC_of_haltsO (fun t s sc ho => ?_) h
  obtain ⟨A, q, B, rfl, rfl, hq, hrun⟩ := hO t s sc ho
  have e : pre ++ shiftProg pre.length (A ++ shiftProg A.length q ++ B) ++ post =
      (pre ++ shiftProg pre.length A) ++ shiftProg (pre ++ shiftProg pre.length A).length q ++
        (shiftProg pre.length B ++ post) := by
    simp [shiftProg_append, shiftProg_shiftProg]
  have hr := haltsC_relocated M (pre ++ shiftProg pre.length A) q
    (shiftProg pre.length B ++ post) hq hrun
  rw [e]
  simpa using hr

/-- **The linked program of a run under an oracle.** In
    `pre ++ shiftProg pre.length q ++ post` with `q` a block without `call`, let every
    answer of `O` be at the target `pre.length` and be a run of `q` from index `0`. A run
    of the linked program under `O` is a run of it through calls. -/
theorem haltsC_linked_of_haltsO (M : Machine σ) (pre q post : List RInstr)
    (hq : ∀ tg, RInstr.call tg ∉ q) {O : Nat → σ → σ → Prop}
    (hO : ∀ t s sc, O t s sc → t = pre.length ∧ HaltsC M q 0 s sc) {pc : Nat} {s s' : σ}
    (h : HaltsO M O (pre ++ shiftProg pre.length q ++ post) pc s s') :
    HaltsC M (pre ++ shiftProg pre.length q ++ post) pc s s' :=
  haltsC_linked_of_haltsO_blocks M pre q post (fun t s sc ho => by
    obtain ⟨rfl, hrun⟩ := hO t s sc ho
    exact ⟨[], q, [], by simp [shiftProg_zero], by simp, hq, hrun⟩) h

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

/-- **Linking a caller with callees in blocks.** Let `pre` run under an oracle `O` whose
    every answer at a target `t` is a run from index `0` of a block `q` without `call`,
    where `Q` is `A ++ shiftProg A.length q ++ B` and `t = pre.length + A.length`. Then
    `pre` followed by the relocated copy of `Q` runs through calls to the same state. -/
theorem haltsC_of_haltsO_blocks (M : Machine σ) (pre Q : List RInstr)
    {O : Nat → σ → σ → Prop}
    (hO : ∀ t s sc, O t s sc → ∃ A q B, Q = A ++ shiftProg A.length q ++ B ∧
      t = pre.length + A.length ∧ (∀ tg, RInstr.call tg ∉ q) ∧ HaltsC M q 0 s sc)
    {pc : Nat} {s s' : σ} (h : HaltsO M O pre pc s s') :
    HaltsC M (pre ++ shiftProg pre.length Q) pc s s' := by
  have h' := haltsC_linked_of_haltsO_blocks M pre Q [] hO
    (by simpa using h.append_left (shiftProg pre.length Q))
  simpa using h'

/-- **Linking a caller with its callee.** Let `p` run under an oracle `O` whose every
    answer is at the target `p.length` and is a run of the block `q` without `call`. Then
    `p` followed by the relocated copy of `q` runs through calls to the same state. The
    target `p.length` holds no instruction of `p`. -/
theorem haltsC_append_of_haltsO (M : Machine σ) (p q : List RInstr)
    (hq : ∀ tg, RInstr.call tg ∉ q) {O : Nat → σ → σ → Prop}
    (hO : ∀ t s sc, O t s sc → t = p.length ∧ HaltsC M q 0 s sc) {pc : Nat} {s s' : σ}
    (h : HaltsO M O p pc s s') : HaltsC M (p ++ shiftProg p.length q) pc s s' :=
  haltsC_of_haltsO_blocks M p q (fun t s sc ho => by
    obtain ⟨rfl, hrun⟩ := hO t s sc ho
    exact ⟨[], q, [], by simp [shiftProg_zero], by simp, hq, hrun⟩) h

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

/-- The store policy of a block: the stores it may make besides those to its frame. A store
    at the stack register may reach `red` bytes below the frame (the red zone), and a store
    at the base register `b` of an out window `(b, lo, hi)` is to a word at a displacement
    `o` from `b` with `lo ≤ o` and `o + 8 ≤ hi`. -/
structure StorePol where
  /-- The size of the red zone below the frame. -/
  red : Nat
  /-- The out windows: a base register and the bounds of the displacements from it. -/
  wins : List (String × Int × Int)

/-- The store policy of the frame alone: no red zone and no out windows. -/
def StorePol.frame : StorePol := ⟨0, []⟩

/-- The address `x` lies in the window of the displacements `lo, …, hi - 1` from `a`. -/
def InWin (a : BitVec 64) (lo hi : Int) (x : BitVec 64) : Prop :=
  (x - (a + BitVec.ofInt 64 lo)).toNat < (hi - lo).toNat

/-- The footprint of a block with a frame of `F` bytes under the store policy `P`, at the
    register file `ρ` of the entry state: the `F + P.red` bytes below the stack register
    (the frame and the red zone), and each out window of `P` at the value of its base
    register. -/
def KeepFoot (P : StorePol) (F : Nat) (ρ : String → BitVec 64) (x : BitVec 64) : Prop :=
  InFrame (ρ "%rsp") (F + P.red) x ∨ ∃ w ∈ P.wins, InWin (ρ w.1) w.2.1 w.2.2 x

/-- Under the policy of the frame alone, the footprint is the frame. -/
theorem keepFoot_frame {F : Nat} {ρ : String → BitVec 64} {x : BitVec 64} :
    KeepFoot .frame F ρ x ↔ InFrame (ρ "%rsp") F x := by
  grind only [= KeepFoot.eq_def, = StorePol.frame.eq_def, = InFrame.eq_def, ← List.not_mem_nil]

/-! ### Provenance of the entry values of the window base registers -/

/-- A location of a block: a register, or the word at a displacement from the stack
    register. -/
inductive KLoc where
  /-- The register `r`. -/
  | reg (r : String)
  /-- The eight bytes at the displacement `o` from the stack register. -/
  | slot (o : Int)
  deriving DecidableEq

/-- A provenance fact `(l, b)`: the location `l` holds the value of the register `b` at the
    entry of the block. -/
abbrev KFact : Type := KLoc × String

/-- The fact `f` holds in the state `s` of a run entered in the state `e`: its location, read
    in `s` (a slot as the little-endian word of `s.mem` at the stack register of `s`), holds
    the value of its register in `e`. -/
def KFact.Holds (e s : AState) (f : KFact) : Prop :=
  match f.1 with
  | .reg r => s.regs r = e.regs f.2
  | .slot o => read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 o) = e.regs f.2

/-- The eight-byte words at the displacements `o` and `o'` from one address are disjoint. -/
def disjB (o o' : Int) : Bool :=
  decide (8 ≤ (o - o').natAbs) && decide ((o - o').natAbs ≤ 2 ^ 64 - 8)

/-- The word at the displacement `o'` from the stack register is kept by the instruction:
    the instruction does not write the stack register, and a store of it is at the stack
    register to a word disjoint from that at `o'`. An indexed store keeps no slot. -/
def slotKeepB (i : JInstr 64) (o' : Int) : Bool :=
  !(dsts i).contains "%rsp" && (match i with
    | .storeMem b o _ => b == "%rsp" && disjB o o'
    | .addToMem b o _ => b == "%rsp" && disjB o o'
    | .storeMemIdx .. => false
    | _ => true)

/-- The load of the instruction from a slot: `(d, o)` for `movq o(%rsp), d`. -/
def slotLoad : JInstr 64 → Option (String × Int)
  | .loadMem d b o => if b = "%rsp" then some (d, o) else none
  | _ => none

/-- The store of the instruction of a register to a slot: `(o, r)` for `movq r, o(%rsp)`. -/
def slotStore : JInstr 64 → Option (Int × String)
  | .storeMem b o (.reg r) => if b = "%rsp" then some (o, r) else none
  | _ => none

theorem eq_of_slotLoad {i : JInstr 64} {d : String} {o : Int}
    (h : slotLoad i = some (d, o)) : i = .loadMem d "%rsp" o := by
  cases i <;> simp only [slotLoad, reduceCtorEq] at h
  split at h <;> simp_all

theorem eq_of_slotStore {i : JInstr 64} {o : Int} {r : String}
    (h : slotStore i = some (o, r)) : i = .storeMem "%rsp" o (.reg r) := by
  cases i <;> simp only [slotStore, reduceCtorEq] at h
  split at h <;> simp_all

/-- The facts of `A` at the location `l`, moved to the location `l'`. -/
def kMove (A : List KFact) (l l' : KLoc) : List KFact :=
  A.filterMap fun f => if f.1 = l then some (l', f.2) else none

/-- **The transfer of the provenance facts over an instruction.** A fact survives when the
    instruction does not write its location: a register outside `dsts i`, or a slot kept by
    `slotKeepB`. A register-to-register move copies the facts of its source to its
    destination, a load from a slot copies the facts of the slot to its destination, and a
    store of a register to a slot copies the facts of the register to the slot. -/
def kstep (A : List KFact) (i : JInstr 64) : List KFact :=
  A.filter (fun f => match f.1 with
      | .reg r => !(dsts i).contains r
      | .slot o => slotKeepB i o)
    ++ (match movSrc i with | some (d, r) => kMove A (.reg r) (.reg d) | none => [])
    ++ (match slotLoad i with | some (d, o) => kMove A (.slot o) (.reg d) | none => [])
    ++ (match slotStore i with | some (o, r) => kMove A (.reg r) (.slot o) | none => [])

/-- The intersection of two sets of facts. -/
def kMeet (A B : List KFact) : List KFact := A.filter (B.contains ·)

/-- The targets `t` of the backward branches `jcc _ t` at an index `j ≥ t` of `q`. -/
def backTargets (q : List RInstr) : List Nat :=
  q.zipIdx.filterMap fun p => match p.1 with
    | .jcc _ t => if t ≤ p.2 then some t else none
    | _ => none

/-- The forward pass computing the facts at each index from `k` on: the facts at an index are
    the intersection of those of its fall-through predecessor (`cur`) and those of the forward
    branches to it (`pend`), and `B0` at the target of a backward branch. -/
def kTableGo (B0 : List KFact) (backs : List Nat) :
    Nat → List RInstr → Option (List KFact) → List (Nat × List KFact) → List (List KFact)
  | _, [], _, _ => []
  | k, ri :: l, cur, pend =>
    let ins := (pend.filter (·.1 == k)).map (·.2)
    let st : List KFact :=
      if backs.contains k then B0
      else match cur, ins with
        | some c, _ => ins.foldl kMeet c
        | none, a :: r => r.foldl kMeet a
        | none, [] => []
    match ri with
    | .op i => st :: kTableGo B0 backs (k + 1) l (some (kstep st i)) pend
    | .jcc _ t =>
      st :: kTableGo B0 backs (k + 1) l (some st) (if k < t then (t, st) :: pend else pend)
    | _ => st :: kTableGo B0 backs (k + 1) l none pend

/-- The facts at each index of the block `q` under the policy `P`: at index `0` each window
    base register holds its own entry value, and at the target of a backward branch only the
    window base registers outside `clob` are known to. -/
def kTable (q : List RInstr) (clob : String → Bool) (P : StorePol) : List (List KFact) :=
  let E0 : List KFact := P.wins.map fun w => (.reg w.1, w.1)
  kTableGo (E0.filter fun f => !clob f.2) (backTargets q) 0 q (some E0) []

/-- The table of facts `kTable q clob P` as an array. -/
def kArr (q : List RInstr) (clob : String → Bool) (P : StorePol) : Array (List KFact) :=
  (kTable q clob P).toArray

/-- The facts at the indices of `q` as a function; no fact under a policy without windows. -/
def kFacts (q : List RInstr) (clob : String → Bool) (P : StorePol) : Nat → List KFact :=
  if P.wins.isEmpty then fun _ => []
  else
    let a := kArr q clob P
    fun k => a.getD k []

/-- A store at the base register `b` and the displacement `o` is to a word allowed by `P`
    for a frame of `F` bytes, with the facts `A`: at the stack register with `-P.red ≤ o`
    and `o + 8 ≤ F`, or inside an out window of `P` whose base register's entry value `b`
    holds by `A`. -/
def storeWinB (F : Nat) (P : StorePol) (A : List KFact) (b : String) (o : Int) : Bool :=
  (b == "%rsp" && decide (-(P.red : Int) ≤ o) && decide (o + 8 ≤ (F : Int)))
    || P.wins.any (fun w => A.contains (.reg b, w.1) && decide (w.2.1 ≤ o)
      && decide (o + 8 ≤ w.2.2))

/-- A store of the instruction, if any, is to a word allowed by `P` for a frame of `F`
    bytes with the facts `A` (`storeWinB`). An indexed store is refused. -/
def storeOkWB (F : Nat) (P : StorePol) (A : List KFact) : JInstr 64 → Bool
  | .storeMem b o _ => storeWinB F P A b o
  | .addToMem b o _ => storeWinB F P A b o
  | .storeMemIdx .. => false
  | _ => true

/-- The check of an instruction between the two frame instructions of a block of length
    `n` under the store policy `P` with the facts `A`: an `op` writes only registers of
    `clob` other than the stack register and stores only as `P` allows; a branch has its
    target among the indices `1, …, n - 2`; `ret`, `push`, `pop` and `call` are refused. -/
def bodyOkWB (n : Nat) (clob : String → Bool) (F : Nat) (P : StorePol) (A : List KFact) :
    RInstr → Bool
  | .op i => (dsts i).all (fun d => d != "%rsp" && clob d) && storeOkWB F P A i
  | .jcc _ t => decide (1 ≤ t) && decide (t + 2 ≤ n)
  | _ => false

/-- The check of the instruction at index `k` of a block of length `n` under the store
    policy `P` with the table of facts `T`: index `0` lowers the stack register by `F`,
    index `n - 2` raises it by `F`, index `n - 1` is `ret`, and every other index satisfies
    `bodyOkWB` with the facts `T k`. -/
def instrOkWB (n : Nat) (clob : String → Bool) (F : Nat) (P : StorePol)
    (T : Nat → List KFact) (k : Nat) (ri : RInstr) : Bool :=
  if k = 0 then isLeaRsp (-(F : Int)) ri
  else if k + 2 = n then isLeaRsp (F : Int) ri
  else if k + 1 = n then (match ri with | .ret => true | _ => false)
  else bodyOkWB n clob F P (T k) ri

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

/-- `allFrom f k l` holds when `f` holds everywhere. -/
theorem allFrom_of_forall {f : Nat → RInstr → Bool} (hf : ∀ k ri, f k ri = true) :
    ∀ (l : List RInstr) (k : Nat), allFrom f k l = true
  | [], _ => rfl
  | x :: l, k => by simp only [allFrom, hf, allFrom_of_forall hf l (k + 1), Bool.and_self]

/-- **The flow check of a table of facts** `T` on the block `q`: the facts at index `0` are
    of window base registers at themselves, the facts after an `op` follow from those before
    it by `kstep`, and the facts at both successors of a branch are among those at the
    branch. -/
def kFlowOkB (q : List RInstr) (T : Nat → List KFact) : Bool :=
  (T 0).all (fun f => f.1 == .reg f.2)
    && allFrom (fun k ri => match ri with
      | .op i => (T (k + 1)).all ((kstep (T k) i).contains ·)
      | .jcc _ t => (T t).all ((T k).contains ·) && (T (k + 1)).all ((T k).contains ·)
      | _ => true) 0 q

/-- The store policy `P` is admissible for the clobber set `clob`: its red zone has at most
    the `128` bytes of the System V red zone, and the base register of each out window is
    not the stack register. -/
def winsOkB (_clob : String → Bool) (P : StorePol) : Bool :=
  decide (P.red ≤ 128) && P.wins.all (fun w => w.1 != "%rsp")

/-- **The keep check under a store policy.** The block `q` has the form
    `leaq -F(%rsp), %rsp ; body ; leaq F(%rsp), %rsp ; ret`, the policy `P` satisfies
    `winsOkB`, the table of facts `kFacts q clob P` passes the flow check `kFlowOkB`, and
    every instruction of `body` satisfies `bodyOkWB` with the facts at its index: it writes
    no register outside `clob`, does not write the stack register, stores only to the `F`
    bytes of the frame, the `P.red` bytes below it and the out windows of `P` through a
    register that holds the entry value of the window's base register, branches inside
    `body ; leaq F(%rsp), %rsp`, and is not `ret`, `push`, `pop` or `call`. -/
def keepCheckWB (q : List RInstr) (clob : String → Bool) (F : Nat) (P : StorePol) : Bool :=
  let a := kArr q clob P
  let T : Nat → List KFact := if P.wins.isEmpty then fun _ => [] else fun k => a.getD k []
  decide (3 ≤ q.length) && winsOkB clob P && kFlowOkB q T
    && allFrom (instrOkWB q.length clob F P T) 0 q

/-- The unfolding lemma of `keepCheckWB`, with its table of facts stated as `kFacts`. -/
theorem keepCheckWB_eq (q : List RInstr) (clob : String → Bool) (F : Nat) (P : StorePol) :
    keepCheckWB q clob F P
      = (decide (3 ≤ q.length) && winsOkB clob P && kFlowOkB q (kFacts q clob P)
        && allFrom (instrOkWB q.length clob F P (kFacts q clob P)) 0 q) := rfl

/-- **The keep check.** `keepCheckWB` at the policy `StorePol.frame` of the frame alone: the
    block `q` has the form `leaq -F(%rsp), %rsp ; body ; leaq F(%rsp), %rsp ; ret`, and
    every instruction of `body` writes no register outside `clob`, does not write the stack
    register, stores only to the `F` bytes of the frame, branches inside
    `body ; leaq F(%rsp), %rsp`, and is not `ret`, `push`, `pop` or `call`. -/
def keepCheckB (q : List RInstr) (clob : String → Bool) (F : Nat) : Bool :=
  keepCheckWB q clob F .frame

/-- Under the policy of the frame alone the table of facts is empty, and the keep check is
    the check of the form of the block and of each instruction with no facts, whose stores
    are to the frame only. -/
theorem keepCheckB_eq (q : List RInstr) (clob : String → Bool) (F : Nat) :
    keepCheckB q clob F
      = (decide (3 ≤ q.length) && allFrom (instrOkWB q.length clob F .frame fun _ => []) 0 q) := by
  have hT : kFacts q clob .frame = fun _ => [] := rfl
  have hfl : kFlowOkB q (fun _ => []) = true := by
    simp only [kFlowOkB, List.all_nil, Bool.true_and]
    exact allFrom_of_forall (fun _ ri => by cases ri <;> rfl) q 0
  have hw : winsOkB clob .frame = true := rfl
  simp only [keepCheckB, keepCheckWB_eq, hT, hfl, hw, Bool.and_true]

/-- The invariant of a run of a block of length `n` checked under the store policy `P` with
    the table of facts `T`, entered in the state `e`: the stack register is that of `e` at
    index `0` and at the `ret`, and `F` below it at every other index; a register outside
    `clob` other than the stack register, and a byte outside the footprint
    `KeepFoot P F e.regs`, are those of `e`; and every fact of `T pc` holds
    (`KeepInvW.reg_eq`), so a register of a fact on the base register of an out window
    addresses that window. -/
def KeepInvW (n : Nat) (clob : String → Bool) (F : Nat) (P : StorePol)
    (T : Nat → List KFact) (e : AState) (pc : Nat) (s : AState) : Prop :=
  s.regs "%rsp" = (if pc = 0 ∨ pc + 1 = n then e.regs "%rsp"
      else e.regs "%rsp" + BitVec.ofInt 64 (-(F : Int)))
    ∧ (∀ r, r ≠ "%rsp" → clob r = false → s.regs r = e.regs r)
    ∧ (∀ x, ¬ KeepFoot P F e.regs x → s.mem x = e.mem x)
    ∧ ∀ f ∈ T pc, f.Holds e s

/-- Along a run that satisfies the invariant, a register of a fact at the current index
    holds the entry value of the fact's register. -/
theorem KeepInvW.reg_eq {n : Nat} {clob : String → Bool} {F : Nat} {P : StorePol}
    {T : Nat → List KFact} {e : AState} {pc : Nat} {s : AState}
    (hI : KeepInvW n clob F P T e pc s) {r b : String} (hm : (KLoc.reg r, b) ∈ T pc) :
    s.regs r = e.regs b :=
  hI.2.2.2 _ hm

theorem mem_kMove {A : List KFact} {l l' : KLoc} {f : KFact} (hf : f ∈ kMove A l l') :
    ∃ b, f = (l', b) ∧ (l, b) ∈ A := by
  grind only [kMove, = List.mem_filterMap]

/-- An instruction that keeps the slot at `o'` (`slotKeepB`) keeps the stack register and the
    word at the displacement `o'` from it. -/
theorem evalInstrA_slot_of_slotKeep {s : AState} {i : JInstr 64} {o' : Int}
    (hk : slotKeepB i o' = true) :
    (evalInstrA s i).regs "%rsp" = s.regs "%rsp"
      ∧ read64 (evalInstrA s i).mem (s.regs "%rsp" + BitVec.ofInt 64 o')
        = read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 o') := by
  simp only [slotKeepB, Bool.and_eq_true, Bool.not_eq_true'] at hk
  refine ⟨evalInstr_regs_of_not_mem_dsts s.view i _ (by simpa using hk.1), ?_⟩
  have hk2 := hk.2
  simp only [evalInstrA]
  split
  · rename_i a ha
    cases i <;> simp only [writeAddr, reduceCtorEq, Option.some.injEq] at ha
    all_goals simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at hk2
    all_goals
      obtain ⟨rfl, hd⟩ := hk2
      simp only [disjB, Bool.and_eq_true, decide_eq_true_eq] at hd
      subst ha
      exact read64_write64_of_disjoint _ _ _ _ (disjoint8_add_ofInt _ _ _ hd.1 hd.2)
  · rfl

/-- **Soundness of the transfer of facts.** The facts `kstep A i` hold after the instruction
    `i` when the facts `A` hold before it. -/
theorem kstep_sound {e s : AState} {A : List KFact} {i : JInstr 64}
    (h : ∀ f ∈ A, f.Holds e s) : ∀ f ∈ kstep A i, f.Holds e (evalInstrA s i) := by
  have hreg : ∀ r, r ∉ dsts i → (evalInstrA s i).regs r = s.regs r := fun r hr =>
    evalInstr_regs_of_not_mem_dsts s.view i r hr
  intro f hf
  simp only [kstep, List.mem_append] at hf
  rcases hf with ((hf | hf) | hf) | hf
  · obtain ⟨hA, hk⟩ := List.mem_filter.1 hf
    obtain ⟨l, b⟩ := f
    have hf0 := h _ hA
    cases l with
    | reg r =>
      grind only [= List.contains_eq_mem, KFact.Holds]
    | slot o' =>
      obtain ⟨h1, h2⟩ := evalInstrA_slot_of_slotKeep (s := s) hk
      simp only [KFact.Holds] at hf0 ⊢
      rw [h1, h2]
      exact hf0
  · split at hf
    · rename_i d r hm
      obtain rfl := eq_of_movSrc hm
      obtain ⟨b, rfl, hA⟩ := mem_kMove hf
      have hf0 := h _ hA
      simp only [KFact.Holds] at hf0 ⊢
      simpa [evalInstrA, evalInstr, JState.setReg, x86_MOV, AState.view] using hf0
    · simp at hf
  · split at hf
    · rename_i d o hm
      obtain rfl := eq_of_slotLoad hm
      obtain ⟨b, rfl, hA⟩ := mem_kMove hf
      have hf0 := h _ hA
      simp only [KFact.Holds] at hf0 ⊢
      grind only [DecodedLsemLoop.evalInstrA_loadMem_regs']
    · simp at hf
  · split at hf
    · rename_i o r hm
      obtain rfl := eq_of_slotStore hm
      obtain ⟨b, rfl, hA⟩ := mem_kMove hf
      have hf0 := h _ hA
      simp only [KFact.Holds] at hf0 ⊢
      rw [hreg _ (by simp [dsts])]
      simpa [evalInstrA, writeAddr, writeVal, read64_write64_same, x86_MOV, AState.view]
        using hf0
    · simp at hf

/-- The eight bytes at the displacement `o` from `a` lie in the window of the displacements
    `lo, …, hi - 1` from `a` when `lo ≤ o` and `o + 8 ≤ hi`. -/
theorem inWin_of_inRange8 {a x : BitVec 64} {lo hi o : Int} (h0 : lo ≤ o) (h8 : o + 8 ≤ hi)
    (hin : InRange8 (a + BitVec.ofInt 64 o) x) : InWin a lo hi x := by
  have hsplit : x - (a + BitVec.ofInt 64 lo)
      = (x - (a + BitVec.ofInt 64 o)) + BitVec.ofInt 64 (o - lo) := by
    grind only [BitVec.ofInt_add, BitVec.ofInt_mul]
  unfold InWin
  unfold InRange8 at hin
  rw [hsplit, BitVec.toNat_add, BitVec.toNat_ofInt]
  grind

/-- A store allowed by `P` with the facts `A`, from a state whose stack register is `F` below
    that of the register file `ρ` and in which each register of a fact of `A` holds the value
    in `ρ` of the fact's register, changes no byte outside the footprint `KeepFoot P F ρ`. -/
theorem evalInstrA_mem_of_storeOkW {F : Nat} {P : StorePol} {A : List KFact} {s : AState}
    {i : JInstr 64} {ρ : String → BitVec 64} (hs : storeOkWB F P A i = true)
    (hb : s.regs "%rsp" = ρ "%rsp" + BitVec.ofInt 64 (-(F : Int)))
    (hw : ∀ r b, (KLoc.reg r, b) ∈ A → s.regs r = ρ b)
    (x : BitVec 64) (hx : ¬ KeepFoot P F ρ x) : (evalInstrA s i).mem x = s.mem x := by
  have key : ∀ (b : String) (o : Int), storeWinB F P A b o = true →
      ¬ InRange8 (s.regs b + BitVec.ofInt 64 o) x := by
    intro b o hok hin
    apply hx
    simp only [storeWinB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.any_eq_true, List.contains_iff_mem] at hok
    rcases hok with ⟨⟨rfl, h0⟩, h8⟩ | ⟨w, hwm, ⟨hA, h0⟩, h8⟩
    · left
      rw [hb, BitVec.add_assoc, ← BitVec.ofInt_add] at hin
      have hw' := inWin_of_inRange8 (lo := -((F + P.red : Nat) : Int)) (hi := 0)
        (by omega) (by omega) hin
      unfold InWin at hw'
      unfold InFrame
      grind
    · right
      refine ⟨w, hwm, ?_⟩
      rw [hw _ _ hA] at hin
      exact inWin_of_inRange8 h0 h8 hin
  cases i <;> simp only [storeOkWB, Bool.false_eq_true] at hs <;> try rfl
  all_goals exact write64_of_not_inRange _ _ _ _ (key _ _ hs)

/-- **The invariant along a run of a block checked under a store policy.** A leaky run of a
    block accepted by `keepCheckWB` at the policy `P`, from an index and a state that
    satisfy `KeepInvW` for the entry state `e`, returns in a state with the stack register
    of `e`, the registers of `e` outside `clob` and the bytes of `e` outside the footprint
    `KeepFoot P F e.regs`. -/
theorem keepCheck_invW {q : List RInstr} {clob : String → Bool} {F : Nat} {P : StorePol}
    (hk : keepCheckWB q clob F P = true) {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    (e : AState) {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState}
    (h : RunL r ok q pc s t s') (hI : KeepInvW q.length clob F P (kFacts q clob P) e pc s) :
    s'.regs "%rsp" = e.regs "%rsp"
      ∧ (∀ r', r' ≠ "%rsp" → clob r' = false → s'.regs r' = e.regs r')
      ∧ ∀ x, ¬ KeepFoot P F e.regs x → s'.mem x = e.mem x := by
  simp only [keepCheckWB_eq, Bool.and_eq_true, decide_eq_true_eq] at hk
  generalize kFacts q clob P = T at hk hI
  obtain ⟨⟨⟨hn, _⟩, hfl⟩, hall⟩ := hk
  simp only [kFlowOkB, Bool.and_eq_true] at hfl
  have hat : ∀ {pc : Nat} {ri : RInstr}, q[pc]? = some ri →
      instrOkWB q.length clob F P T pc ri = true := fun {pc ri} hq => by
    simpa using allFrom_getElem? q 0 pc ri hall hq
  have hfop : ∀ {pc : Nat} {i : JInstr 64}, q[pc]? = some (.op i) →
      ∀ f ∈ T (pc + 1), f ∈ kstep (T pc) i := fun {pc i} hq f hf => by
    have := allFrom_getElem? q 0 pc _ hfl.2 hq
    simp only [Nat.zero_add, List.all_eq_true, List.contains_iff_mem] at this
    exact this f hf
  have hfjcc : ∀ {pc cc tg : Nat}, q[pc]? = some (.jcc cc tg) →
      (∀ f ∈ T tg, f ∈ T pc) ∧ ∀ f ∈ T (pc + 1), f ∈ T pc := fun {pc cc tg} hq => by
    have := allFrom_getElem? q 0 pc _ hfl.2 hq
    simpa only [Nat.zero_add, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
      using this
  induction h with
  | @ret pc s hq =>
    have hc := hat hq
    obtain ⟨h1, h2, h3, -⟩ := hI
    have hpc : pc = 0 ∨ pc + 1 = q.length := by
      by_contra hne
      simp only [not_or] at hne
      simp only [instrOkWB, hne.1, hne.2, ite_false, isLeaRsp, bodyOkWB] at hc
      split at hc <;> simp at hc
    rw [ite_eq_left hpc] at h1
    exact ⟨h1, h2, h3⟩
  | @op pc s i t s' hq _ _ ih =>
    have hc := hat hq
    obtain ⟨h1, h2, h3, h4⟩ := hI
    have h4' : ∀ f ∈ T (pc + 1), f.Holds e (evalInstrA s i) := fun f hf =>
      kstep_sound h4 f (hfop hq f hf)
    apply ih
    unfold instrOkWB at hc
    by_cases h0 : pc = 0
    · rw [ite_eq_left h0] at hc
      have hi := eq_of_isLeaRsp hc
      simp only [RInstr.op.injEq] at hi
      subst hi
      obtain ⟨hl, hlm⟩ := evalInstrA_leaFrame s (-(F : Int))
      rw [ite_eq_left (Or.inl h0)] at h1
      refine ⟨?_, fun r' hr' hcl => ?_, fun x hx => ?_, h4'⟩
      · rw [hl, ite_eq_left rfl, h1, ite_eq_right (by omega)]
      · rw [hl, ite_eq_right hr']; exact h2 r' hr' hcl
      · rw [hlm]; exact h3 x hx
    · rw [ite_eq_right h0] at hc
      by_cases h2n : pc + 2 = q.length
      · rw [ite_eq_left h2n] at hc
        have hi := eq_of_isLeaRsp hc
        simp only [RInstr.op.injEq] at hi
        subst hi
        obtain ⟨hl, hlm⟩ := evalInstrA_leaFrame s (F : Int)
        rw [ite_eq_right (by omega)] at h1
        refine ⟨?_, fun r' hr' hcl => ?_, fun x hx => ?_, h4'⟩
        · rw [hl, ite_eq_left rfl, h1, ite_eq_left (Or.inr (by omega)), BitVec.add_assoc,
            ← BitVec.ofInt_add]
          simp
        · rw [hl, ite_eq_right hr']; exact h2 r' hr' hcl
        · rw [hlm]; exact h3 x hx
      · rw [ite_eq_right h2n] at hc
        by_cases h1n : pc + 1 = q.length
        · rw [ite_eq_left h1n] at hc; simp at hc
        · rw [ite_eq_right h1n] at hc
          simp only [bodyOkWB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hc
          obtain ⟨hd, hst⟩ := hc
          rw [ite_eq_right (by omega)] at h1
          have hreg : ∀ r', (evalInstrA s i).regs r' = (evalInstr s.view i).regs r' :=
            fun _ => rfl
          refine ⟨?_, fun r' hr' hcl => ?_, fun x hx => ?_, h4'⟩
          · rw [ite_eq_right (by omega), hreg,
              evalInstr_regs_of_not_mem_dsts _ _ _ (fun hm => (hd _ hm).1 rfl)]
            exact h1
          · rw [hreg, evalInstr_regs_of_not_mem_dsts _ _ _ (fun hm => by
              have := (hd _ hm).2; rw [hcl] at this; cases this)]
            exact h2 r' hr' hcl
          · rw [evalInstrA_mem_of_storeOkW hst h1 (fun r b hm => h4 _ hm) x hx]
            exact h3 x hx
  | @jcc pc s cc tgt c t s' hq _ _ ih =>
    have hc := hat hq
    obtain ⟨h1, h2, h3, h4⟩ := hI
    obtain ⟨hjt, hjn⟩ := hfjcc hq
    apply ih
    unfold instrOkWB at hc
    by_cases h0 : pc = 0
    · rw [ite_eq_left h0] at hc; simp [isLeaRsp] at hc
    · rw [ite_eq_right h0] at hc
      by_cases h2n : pc + 2 = q.length
      · rw [ite_eq_left h2n] at hc; simp [isLeaRsp] at hc
      · rw [ite_eq_right h2n] at hc
        by_cases h1n : pc + 1 = q.length
        · rw [ite_eq_left h1n] at hc; simp at hc
        · rw [ite_eq_right h1n] at hc
          simp only [bodyOkWB, Bool.and_eq_true, decide_eq_true_eq] at hc
          rw [ite_eq_right (by omega)] at h1
          refine ⟨?_, h2, h3, ?_⟩
          · rw [h1]
            split <;> rw [ite_eq_right (by omega)]
          · split
            · exact fun f hf => h4 f (hjt f hf)
            · exact fun f hf => h4 f (hjn f hf)
  | @stack pc s ri ops t s' hq hops _ _ _ =>
    have hc := hat hq
    exfalso
    cases ri <;> simp only [RInstr.stackOps?, reduceCtorEq] at hops <;>
      (unfold instrOkWB at hc; split_ifs at hc <;> simp [isLeaRsp, bodyOkWB] at hc)
  | @call pc tgt s sc tc tr s' hq _ _ _ _ _ _ =>
    have hc := hat hq
    exfalso
    unfold instrOkWB at hc
    split_ifs at hc <;> simp [isLeaRsp, bodyOkWB] at hc

/-- **Soundness of the keep check under a store policy.** Every leaky run of a block
    accepted by `keepCheckWB` at the policy `P`, from its first index to its `ret`,
    restores the stack register, keeps every register outside `clob` and keeps every byte
    outside the footprint `KeepFoot P F` of the entry register file. -/
theorem keepCheck_soundW {q : List RInstr} {clob : String → Bool} {F : Nat} {P : StorePol}
    (hk : keepCheckWB q clob F P = true) {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {s : AState} {t : List CTLeak} {s' : AState} (h : RunL r ok q 0 s t s') :
    s'.regs "%rsp" = s.regs "%rsp"
      ∧ (∀ r', clob r' = false → s'.regs r' = s.regs r')
      ∧ ∀ x, ¬ KeepFoot P F s.regs x → s'.mem x = s.mem x := by
  have h0 : ∀ f ∈ kFacts q clob P 0, f.Holds s s := by
    simp only [keepCheckWB_eq, kFlowOkB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk
    intro f hf
    simp only [KFact.Holds, hk.1.2.1 f hf]
  obtain ⟨h1, h2, h3⟩ := keepCheck_invW hk s h
    ⟨by rw [ite_eq_left (Or.inl rfl)], fun _ _ _ => rfl, fun _ _ => rfl, h0⟩
  refine ⟨h1, fun r' hcl => ?_, h3⟩
  by_cases hr : r' = "%rsp"
  · rw [hr, h1]
  · exact h2 r' hr hcl

/-- A block accepted by `keepCheckWB` holds no `call`. -/
theorem not_call_mem_of_keepCheckW {q : List RInstr} {clob : String → Bool} {F : Nat}
    {P : StorePol} (hk : keepCheckWB q clob F P = true) (tg : Nat) : RInstr.call tg ∉ q := by
  simp only [keepCheckWB_eq, Bool.and_eq_true, decide_eq_true_eq] at hk
  intro hm
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  have hc : instrOkWB q.length clob F P (kFacts q clob P) j (.call tg) = true := by
    simpa using allFrom_getElem? q 0 j _ hk.2 hj
  unfold instrOkWB at hc
  split_ifs at hc <;> simp [isLeaRsp, bodyOkWB] at hc

/-! ## 5. The specification of a compiled scalar kernel -/

/-- **The specification of a compiled kernel under a store policy.** Let the decoded block
    `q` be accepted by `keepCheckWB` with the clobber set of `c`, a frame of `F` bytes and
    the policy `P`, with the footprint `KeepFoot P F` inside the footprint of `c`. Let `q`
    halt from every entry state that satisfies the precondition, in a state that satisfies
    the postcondition, and let the leaky runs of `q` from publicly related entry states that
    satisfy the precondition have equal traces. Then the leaky run of `q` meets `c`. -/
theorem calleeSpec_of_keepCheckW {r : DoitRegime} {q : List RInstr} {c : CalleeSig} {F : Nat}
    {P : StorePol} (hk : keepCheckWB q c.clob F P = true)
    (hfoot : ∀ s x, KeepFoot P F s.regs x → c.foot s x)
    (hrun : ∀ s, c.pre s → ∃ s', Halts aMachine q 0 s s' ∧ c.post s s')
    (hct : ConstantTimeRel (fun s₁ s₂ => c.pub s₁ s₂ ∧ c.pre s₁ ∧ c.pre s₂)
      (fun s t => ∃ s', RunL r (fun _ _ => True) q 0 s t s')) :
    CalleeSpec (runOf r q) c where
  halts s hs := by
    obtain ⟨s', hh, _⟩ := hrun s hs
    obtain ⟨t, ht⟩ := halts_runL r hh
    exact ⟨t, s', ht⟩
  rsp _ _ _ _ hX := (keepCheck_soundW hk hX).1
  keep _ _ _ _ hX := (keepCheck_soundW hk hX).2.1
  frame _ _ _ _ hX x hx := (keepCheck_soundW hk hX).2.2 x (fun hf => hx (hfoot _ x hf))
  post s t s' hs hX := by
    obtain ⟨s₀, hh, hp⟩ := hrun s hs
    obtain ⟨t₀, ht₀⟩ := halts_runL r hh
    obtain ⟨_, rfl⟩ := runL_det ht₀ hX
    exact hp
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ := hct s₁ s₂ t₁ t₂ ⟨hp, h₁, h₂⟩ ⟨s₁', hX₁⟩ ⟨s₂', hX₂⟩

/-! ## 6. The allocation pool of a caller -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpList gpOk phys)

/-- The general-purpose name `r` is kept across a call of `c`: its machine register is
    outside the clobber set, and it is neither an argument name nor the result name. -/
def keptB (c : CalleeSig) (r : String) : Bool :=
  gpOk r && !c.clob (phys r) && !c.args.contains r && (c.res != some r)

/-- The candidates of the allocation pool of a caller of `c`: the general-purpose names kept
    across a call of `c`, in the order of `gpList`, other than `RDX` and the reload scratches
    `R14` and `R15`. -/
def keepCands (c : CalleeSig) : List String :=
  gpList.filter fun r => keptB c r && r != "RDX" && r != "R14" && r != "R15"

/-- **The allocation pool of a caller of `c`**: the general-purpose names kept across a
    call of `c`, in the order of `gpList`, other than the reload scratches `R15` and `R14`
    of the allocator (`JasminLprogExport.reloadScratch`, `JasminLprogExport.reloadScratch2`),
    which the reload of a spilled name and the load of an array base write. `RDX` sits at
    index `3`, the index the allocator withholds for a body with a high multiplication
    (`JasminLprogExport.bodyReservedGP`), when `c` keeps it and at least three other names
    are kept; otherwise the pool is `keepCands c`, which does not contain `RDX`. -/
def keepPool (c : CalleeSig) : List String :=
  if keptB c "RDX" && decide (3 ≤ (keepCands c).length) then
    (keepCands c).take 3 ++ "RDX" :: (keepCands c).drop 3
  else keepCands c

/-- A member of `keepCands c` is kept across a call of `c` and is none of `RDX`, `R14`,
    `R15`. -/
theorem mem_keepCands {c : CalleeSig} {x : String} (hx : x ∈ keepCands c) :
    keptB c x = true ∧ x ≠ "RDX" ∧ x ≠ "R14" ∧ x ≠ "R15" := by
  have := (List.mem_filter.mp hx).2
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- `keepCands c` has no duplicate name. -/
theorem keepCands_nodup (c : CalleeSig) : (keepCands c).Nodup :=
  List.Nodup.sublist List.filter_sublist (by decide)

/-- A member of `keepPool c` is `RDX` or a member of `keepCands c`. -/
theorem mem_keepPool {c : CalleeSig} {x : String} (hx : x ∈ keepPool c) :
    x = "RDX" ∨ x ∈ keepCands c := by
  unfold keepPool at hx
  split at hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact .inr (List.mem_of_mem_take hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inl rfl
      · exact .inr (List.mem_of_mem_drop hx)
  · exact .inr hx

/-- The pool `keepPool c` holds neither reload scratch of the allocator. -/
theorem scratch_not_mem_keepPool (c : CalleeSig) :
    "R14" ∉ keepPool c ∧ "R15" ∉ keepPool c := by
  constructor <;> intro hm <;> rcases mem_keepPool hm with h | h
  · exact absurd h (by decide)
  · exact (mem_keepCands h).2.2.1 rfl
  · exact absurd h (by decide)
  · exact (mem_keepCands h).2.2.2 rfl

/-- **Where `c` keeps `RDX` and at least three other names, `keepPool c` places `RDX` at
    index `3` of `keepCands c`.** -/
theorem keepPool_eq_of_kept {c : CalleeSig} (hk : keptB c "RDX" = true)
    (hl : 3 ≤ (keepCands c).length) :
    keepPool c = (keepCands c).take 3 ++ "RDX" :: (keepCands c).drop 3 := by
  simp [keepPool, hk, hl]

/-- **The check of an allocation pool against a callee**: every name of the pool is kept
    across a call of `c`, `RDX`, when it occurs, sits at index `3`, and no name occurs
    twice. -/
def keepPoolB (c : CalleeSig) (pool : List String) : Bool :=
  pool.all (keptB c) && (!pool.contains "RDX" || decide (pool[3]? = some "RDX"))
    && decide pool.Nodup

/-- A kept name is a general-purpose name whose machine register is outside the clobber
    set, and is neither an argument name nor the result name. -/
theorem keptB_spec {c : CalleeSig} {r : String} (h : keptB c r = true) :
    gpOk r = true ∧ c.clob (phys r) = false ∧ r ∉ c.args ∧ c.res ≠ some r := by
  simpa [keptB, and_assoc] using h

/-- **Soundness of `keepPoolB`.** -/
theorem keepPoolB_spec {c : CalleeSig} {pool : List String} (h : keepPoolB c pool = true) :
    (∀ r ∈ pool, gpOk r = true ∧ c.clob (phys r) = false ∧ r ∉ c.args ∧ c.res ≠ some r)
      ∧ ("RDX" ∈ pool → pool[3]? = some "RDX") ∧ pool.Nodup := by
  simp only [keepPoolB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  exact ⟨fun r hr => keptB_spec (h.1.1 r hr),
    fun hm => h.1.2.resolve_left (fun hc => by simp [hm] at hc), h.2⟩

/-- **Completeness of `keepPoolB`**: the check accepts the pool `keepPool c` of every
    signature `c`. -/
theorem keepPoolB_keepPool (c : CalleeSig) : keepPoolB c (keepPool c) = true := by
  have hR : "RDX" ∉ keepCands c := fun h => (mem_keepCands h).2.1 rfl
  unfold keepPoolB keepPool
  split
  · rename_i hif
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hif
    have hlen : ((keepCands c).take 3).length = 3 := by simp [hif.2]
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true']
    refine ⟨⟨fun x hx => ?_, .inr ?_⟩, ?_⟩
    · rcases List.mem_append.mp hx with h | h
      · exact (mem_keepCands (List.mem_of_mem_take h)).1
      · rcases List.mem_cons.mp h with rfl | h
        · exact hif.1
        · exact (mem_keepCands (List.mem_of_mem_drop h)).1
    · rw [List.getElem?_append_right (by omega), hlen]
      rfl
    · rw [List.perm_middle.nodup_iff, List.nodup_cons, List.take_append_drop]
      exact ⟨hR, keepCands_nodup c⟩
  · simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true']
    exact ⟨⟨fun x hx => (mem_keepCands hx).1, .inl (by simpa using hR)⟩, keepCands_nodup c⟩

/-- **A register of the pool holds its entry value at every return of a specified
    callee.** -/
theorem keepPoolB_keep {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {pool : List String} (h : keepPoolB c pool = true) {s s' : AState} {t : List CTLeak}
    (hpre : c.pre s) (hrun : X s t s') {r : String} (hr : r ∈ pool) :
    s'.regs (phys r) = s.regs (phys r) :=
  hX.keep s t s' hpre hrun _ ((keepPoolB_spec h).1 r hr).2.1

/-! ## 7. The leakage summary of a callee -/

/-- **The leakage summary of a callee.** Two runs of `X` from entry states that satisfy the
    precondition of `c` and are related by `c.pub` have equal traces (`trace`) and return
    in states related by `out` (`exit`). The relation `out` is the agreement the callee
    establishes itself: the result register when the result is public, and the public
    bytes of its footprint. The agreement of the caller's own data after the return (the
    stack register, a register outside the clobber set, a byte outside the footprint) is
    not part of the summary; it follows from `CalleeSpec` (`CalleeSpec.kept_agree`). -/
structure PubSummary (X : CalleeRun) (c : CalleeSig) (out : AState → AState → Prop) : Prop where
  /-- Two runs from publicly related entry states have equal traces. -/
  trace : ∀ s₁ s₂ t₁ t₂ s₁' s₂', c.pre s₁ → c.pre s₂ → c.pub s₁ s₂ →
    X s₁ t₁ s₁' → X s₂ t₂ s₂' → t₁ = t₂
  /-- Two runs from publicly related entry states return in states related by `out`. -/
  exit : ∀ s₁ s₂ t₁ t₂ s₁' s₂', c.pre s₁ → c.pre s₂ → c.pub s₁ s₂ →
    X s₁ t₁ s₁' → X s₂ t₂ s₂' → out s₁' s₂'

/-- A specified callee has the leakage summary with the trivial exit relation. -/
theorem CalleeSpec.pubSummary {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) :
    PubSummary X c (fun _ _ => True) :=
  ⟨hX.ct, fun _ _ _ _ _ _ _ _ _ _ _ => trivial⟩

/-- **What a specified callee keeps public.** For two runs of a specified callee from entry
    states that satisfy the precondition: equal stack registers at the entries give equal
    stack registers at the returns; a register outside the clobber set that is equal at
    the entries is equal at the returns; a byte outside both footprints that is equal at
    the entries is equal at the returns. -/
theorem CalleeSpec.kept_agree {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {s₁ s₂ s₁' s₂' : AState} {t₁ t₂ : List CTLeak} (h₁ : c.pre s₁) (h₂ : c.pre s₂)
    (hX₁ : X s₁ t₁ s₁') (hX₂ : X s₂ t₂ s₂') :
    (s₁.regs "%rsp" = s₂.regs "%rsp" → s₁'.regs "%rsp" = s₂'.regs "%rsp")
      ∧ (∀ x, c.clob x = false → s₁.regs x = s₂.regs x → s₁'.regs x = s₂'.regs x)
      ∧ ∀ x, ¬ c.foot s₁ x → ¬ c.foot s₂ x → s₁.mem x = s₂.mem x → s₁'.mem x = s₂'.mem x := by
  refine ⟨fun h => ?_, fun x hx h => ?_, fun x hf₁ hf₂ h => ?_⟩
  · rw [hX.rsp _ _ _ h₁ hX₁, hX.rsp _ _ _ h₂ hX₂, h]
  · rw [hX.keep _ _ _ h₁ hX₁ x hx, hX.keep _ _ _ h₂ hX₂ x hx, h]
  · rw [hX.frame _ _ _ h₁ hX₁ x hf₁, hX.frame _ _ _ h₂ hX₂ x hf₂, h]

/-- **The summary of a decoded block from equality of traces.** If the leaky runs of `q`
    from publicly related entry states that satisfy the precondition have equal traces,
    the leaky run of `q` has the leakage summary with the trivial exit relation. -/
theorem pubSummary_of_ct {r : DoitRegime} {q : List RInstr} {c : CalleeSig}
    (hct : ConstantTimeRel (fun s₁ s₂ => c.pub s₁ s₂ ∧ c.pre s₁ ∧ c.pre s₂)
      (fun s t => ∃ s', RunL r (fun _ _ => True) q 0 s t s')) :
    PubSummary (runOf r q) c (fun _ _ => True) :=
  ⟨fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ =>
      hct s₁ s₂ t₁ t₂ ⟨hp, h₁, h₂⟩ ⟨s₁', hX₁⟩ ⟨s₂', hX₂⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ => trivial⟩

/-- **The summary of a decoded block from a certificate of the byte check.** Let `q` pass
    `checkCert` and `presCert` with a certificate that assigns index `0` the public set
    `a`, let entry states related by `c.pub` agree on `a`, and let the steps of every leaky
    run of `q` from an entry state satisfy `FrameSep F`. Then the leaky run of `q` has the
    leakage summary whose exit relation is agreement on the exit set of the function at
    index `0`. -/
theorem pubSummary_of_checkCert {r : DoitRegime} {F : List Int} {own : Nat → Nat}
    {Xs : Nat → PubA} {K : PresCtx} {q : List RInstr} {A : List (Option PubA)} {a : PubA}
    {c : CalleeSig} (hc : checkCert r F own Xs K q A = true)
    (hp : presCert F own K.Rp K.Pp q K.D = true) (ha : certAt A 0 = some a)
    (hpub : ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → c.pub s₁ s₂ → a.Agree s₁ s₂)
    (hsep : ∀ s t s', c.pre s → RunL r (fun _ _ => True) q 0 s t s' →
      RunL r (FrameSep F) q 0 s t s') :
    PubSummary (runOf r q) c (Xs (own 0)).Agree where
  trace _ _ _ _ _ _ h₁ h₂ hpb hX₁ hX₂ :=
    (checkCert_sound hc hp (hsep _ _ _ h₁ hX₁) ha (hpub _ _ h₁ h₂ hpb) (hsep _ _ _ h₂ hX₂)).1
  exit _ _ _ _ _ _ h₁ h₂ hpb hX₁ hX₂ :=
    (checkCert_sound hc hp (hsep _ _ _ h₁ hX₁) ha (hpub _ _ h₁ h₂ hpb) (hsep _ _ _ h₂ hX₂)).2

/-! ## 8. Runs with leakage, calls answered by an oracle -/

/-- The oracle with traces that answers a call to the target `tgt` by the callee `X` and
    answers no other target. -/
def tracedAt (tgt : Nat) (X : CalleeRun) : Nat → CalleeRun :=
  fun t s tr s' => t = tgt ∧ X s tr s'

/-- The oracle with traces of the callees named `fs`: a call to the target `t` is answered by
    the callee `X f` of a symbol `f` of `fs` with `tgt f = t`. -/
def tracedOf (fs : List String) (tgt : String → Nat) (X : String → CalleeRun) :
    Nat → CalleeRun :=
  fun t s tr s' => ∃ f ∈ fs, tgt f = t ∧ X f s tr s'

/-- **The oracle with traces of one callee.** At one symbol, a constant target and a constant
    callee, `tracedOf` is `tracedAt`. -/
theorem tracedOf_one (f : String) (tgt : Nat) (X : CalleeRun) :
    tracedOf [f] (fun _ => tgt) (fun _ => X) = tracedAt tgt X := by
  funext t s tr s'
  simp [tracedOf, tracedAt, eq_comm]

/-- A halting run of `prog` with leakage in which a `call t` is answered by the relation
    `O t`: the trace of the call is the leakage of `callOps`, the trace of the answer and
    the leakage of `retOps`. The other steps are those of `DecodedCT.RunL`; index `t` need
    not hold an instruction. -/
inductive OracleRun (r : DoitRegime) (ok : AState → JInstr 64 → Prop) (O : Nat → CalleeRun)
    (prog : List RInstr) : Nat → AState → List CTLeak → AState → Prop
  | ret {pc : Nat} {sa : AState} (h : prog[pc]? = some .ret) : OracleRun r ok O prog pc sa [] sa
  | op {pc : Nat} {sa : AState} {i : JInstr 64} {t : List CTLeak} {sa' : AState}
      (h : prog[pc]? = some (.op i)) (hok : ok sa i)
      (hr : OracleRun r ok O prog (pc + 1) (evalInstrA sa i) t sa') :
      OracleRun r ok O prog pc sa (opLeak r sa i ++ t) sa'
  | jcc {pc : Nat} {sa : AState} {cc tgt : Nat} {c : Condt} {t : List CTLeak} {sa' : AState}
      (h : prog[pc]? = some (.jcc cc tgt)) (hc : condtOfNibble cc = some c)
      (hr : OracleRun r ok O prog (if sa.view.condB c then tgt else pc + 1) sa t sa') :
      OracleRun r ok O prog pc sa (.branch (sa.view.condB c) :: t) sa'
  | stack {pc : Nat} {sa : AState} {ri : RInstr} {ops : List (JInstr 64)} {t : List CTLeak}
      {sa' : AState} (h : prog[pc]? = some ri) (hops : ri.stackOps? = some ops)
      (hok : BlockOk ok sa ops)
      (hr : OracleRun r ok O prog (pc + 1) (runBlockA sa ops) t sa') :
      OracleRun r ok O prog pc sa (blockLeakA r sa ops ++ t) sa'
  | call {pc tgt : Nat} {sa sc : AState} {tc tr : List CTLeak} {sa' : AState}
      (h : prog[pc]? = some (.call tgt)) (hok : BlockOk ok sa (callOps (pc + 1)))
      (hc : O tgt (runBlockA sa (callOps (pc + 1))) tc sc)
      (hokr : BlockOk ok sc retOps)
      (hr : OracleRun r ok O prog (pc + 1) (runBlockA sc retOps) tr sa') :
      OracleRun r ok O prog pc sa
        (blockLeakA r sa (callOps (pc + 1)) ++ tc ++ blockLeakA r sc retOps ++ tr) sa'

/-- A run with leakage under an oracle is a run under the oracle without traces. -/
theorem OracleRun.haltsO {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {O : Nat → CalleeRun} {prog : List RInstr} {pc : Nat} {sa : AState} {t : List CTLeak}
    {sa' : AState} (h : OracleRun r ok O prog pc sa t sa') :
    HaltsO aMachine (fun tg s s' => ∃ tr, O tg s tr s') prog pc sa sa' := by
  induction h with
  | ret h => exact .ret h
  | op h _ _ ih => exact .go (by simp [RInstrSemantics.step, h, aMachine]) ih
  | jcc h hc _ ih =>
    refine .go ?_ ih
    simp only [RInstrSemantics.step, h, hc, Option.map_some, aMachine]
    split <;> simp_all
  | @stack pc sa ri ops _ _ h hops _ _ ih =>
    refine .go ?_ ih
    cases ri <;> simp only [RInstr.stackOps?, reduceCtorEq, Option.some.injEq] at hops <;>
      subst hops <;> simp only [RInstrSemantics.step, h, foldl_aMachine_exec]
  | call h _ hc _ _ ih =>
    rw [← foldl_aMachine_exec] at ih hc
    exact .call h ⟨_, hc⟩ ih

/-- Every run under an oracle without traces has a leakage trace. -/
theorem oracleRun_of_haltsO (r : DoitRegime) {O : Nat → CalleeRun} {prog : List RInstr}
    {pc : Nat} {sa sa' : AState}
    (h : HaltsO aMachine (fun tg s s' => ∃ tr, O tg s tr s') prog pc sa sa') :
    ∃ t, OracleRun r (fun _ _ => True) O prog pc sa t sa' := by
  induction h with
  | ret hret => exact ⟨[], .ret hret⟩
  | call h hc _ ih =>
    obtain ⟨tc, htc⟩ := hc
    obtain ⟨tr, htr⟩ := ih
    rw [foldl_aMachine_exec] at htc htr
    exact ⟨_, .call h (blockOk_true _ _) htc (blockOk_true _ _) htr⟩
  | @go pc s pc₁ s₁ s₂ hs _ ih =>
    obtain ⟨t, ht⟩ := ih
    unfold RInstrSemantics.step at hs
    split at hs
    · exact absurd hs (by simp)
    · rename_i i hi
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨_, .op hi trivial ht⟩
    · simp at hs
    · rename_i cc tgt hj
      cases hc : condtOfNibble cc with
      | none => simp [hc] at hs
      | some c =>
        simp only [hc, Option.map_some, Option.some.injEq] at hs
        have hv : aMachine.view s = s.view := rfl
        rw [hv] at hs
        have hnext : (if s.view.condB c then tgt else pc + 1) = pc₁ ∧ s = s₁ := by
          split at hs <;> simp only [Next.go.injEq] at hs <;> obtain ⟨rfl, rfl⟩ := hs <;>
            simp_all
        obtain ⟨hp, rfl⟩ := hnext
        exact ⟨_, .jcc hj hc (hp ▸ ht)⟩
    · rename_i x hx
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [foldl_aMachine_exec] at ht
      exact ⟨_, .stack hx rfl (blockOk_true _ _) ht⟩
    · rename_i x hx
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [foldl_aMachine_exec] at ht
      exact ⟨_, .stack hx rfl (blockOk_true _ _) ht⟩
    · simp at hs

/-- A run under the oracle of the callees named `fs` has a leakage trace under the oracle with
    traces of these callees. -/
theorem oracleRun_of_haltsO_oracleOf (r : DoitRegime) {fs : List String} {tgt : String → Nat}
    {X : String → CalleeRun} {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    (h : HaltsO aMachine (oracleOf fs tgt X) prog pc sa sa') :
    ∃ t, OracleRun r (fun _ _ => True) (tracedOf fs tgt X) prog pc sa t sa' :=
  oracleRun_of_haltsO r (h.mono fun _ _ _ ⟨f, hf, ht, tr, hx⟩ => ⟨tr, f, hf, ht, hx⟩)

/-- A run under the oracle of one target has a leakage trace under the oracle with
    traces of that target: `oracleRun_of_haltsO_oracleOf` at one symbol. -/
theorem oracleRun_of_haltsO_oracleAt (r : DoitRegime) {tgt : Nat} {X : CalleeRun}
    {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    (h : HaltsO aMachine (oracleAt tgt X) prog pc sa sa') :
    ∃ t, OracleRun r (fun _ _ => True) (tracedAt tgt X) prog pc sa t sa' := by
  rw [← tracedOf_one ""]
  exact oracleRun_of_haltsO_oracleOf r (h.mono fun t s s' ho => (oracleOf_one "" tgt X t s s').2 ho)

/-- **An oracle whose answers are runs of the program.** If every answer of `O` at a
    target is a run with leakage of `prog` from that target, a run under `O` is a run with
    leakage of `prog` with the same trace. -/
theorem runL_of_oracleRun {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {O : Nat → CalleeRun} {prog : List RInstr}
    (hO : ∀ tg s tr sc, O tg s tr sc → RunL r ok prog tg s tr sc) {pc : Nat} {sa : AState}
    {t : List CTLeak} {sa' : AState} (h : OracleRun r ok O prog pc sa t sa') :
    RunL r ok prog pc sa t sa' := by
  induction h with
  | ret h => exact .ret h
  | op h hok _ ih => exact .op h hok ih
  | jcc h hc _ ih => exact .jcc h hc ih
  | stack h hops hok _ ih => exact .stack h hops hok ih
  | call h hok hc hokr _ ih => exact .call h hok (hO _ _ _ _ hc) hokr ih

/-- A run with leakage under an oracle is a run of the program with instructions
    appended. -/
theorem OracleRun.append_left {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {O : Nat → CalleeRun} {p : List RInstr} (ext : List RInstr) {pc : Nat} {sa : AState}
    {t : List CTLeak} {sa' : AState} (h : OracleRun r ok O p pc sa t sa') :
    OracleRun r ok O (p ++ ext) pc sa t sa' := by
  have hat : ∀ {k : Nat} {x : RInstr}, p[k]? = some x → (p ++ ext)[k]? = some x :=
    fun {k x} hk => by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]; exact hk
  induction h with
  | ret h => exact .ret (hat h)
  | op h hok _ ih => exact .op (hat h) hok ih
  | jcc h hc _ ih => exact .jcc (hat h) hc ih
  | stack h hops hok _ ih => exact .stack (hat h) hops hok ih
  | call h hok hc hokr _ ih => exact .call (hat h) hok hc hokr ih

/-- **The trace of the linked program, callees in blocks.** Let every answer of `O` at a target
    `t` be a leaky run from index `0` of a block `q` without `call` such that `Q` is
    `A ++ shiftProg A.length q ++ B` and `t = p.length + A.length`. A run with leakage of `p`
    under `O` is a run with leakage of `p` followed by the relocated copy of `Q`, with the same
    trace. -/
theorem runL_append_blocks_of_oracleRun {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    (p Q : List RInstr) {O : Nat → CalleeRun}
    (hO : ∀ t s tr sc, O t s tr sc → ∃ A q B, Q = A ++ shiftProg A.length q ++ B ∧
      t = p.length + A.length ∧ (∀ tg, RInstr.call tg ∉ q) ∧ RunL r ok q 0 s tr sc)
    {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState}
    (h : OracleRun r ok O p pc s t s') :
    RunL r ok (p ++ shiftProg p.length Q) pc s t s' := by
  refine runL_of_oracleRun (fun t s tr sc ho => ?_) (h.append_left _)
  obtain ⟨A, q, B, rfl, rfl, hq, hrun⟩ := hO t s tr sc ho
  have e : p ++ shiftProg p.length (A ++ shiftProg A.length q ++ B) =
      (p ++ shiftProg p.length A) ++ shiftProg (p ++ shiftProg p.length A).length q ++
        shiftProg p.length B := by
    simp [shiftProg_append, shiftProg_shiftProg]
  have hr := runL_relocated (p ++ shiftProg p.length A) q (shiftProg p.length B) hq hrun
  rw [e]
  simpa using hr

/-- **The trace of the linked program.** A run with leakage of `p` under the oracle of the
    leaky runs of a block `q` without `call`, at the target `p.length`, is a run with
    leakage of `p` followed by the relocated copy of `q`, with the same trace: the leakage
    of the caller with the trace of the callee at each call. This is
    `runL_append_blocks_of_oracleRun` at the one-block region `q`. -/
theorem runL_append_of_oracleRun {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    (p q : List RInstr) (hq : ∀ tg, RInstr.call tg ∉ q) {pc : Nat} {s : AState}
    {t : List CTLeak} {s' : AState}
    (h : OracleRun r ok (tracedAt p.length (fun s t s' => RunL r ok q 0 s t s')) p pc s t s') :
    RunL r ok (p ++ shiftProg p.length q) pc s t s' := by
  refine runL_append_blocks_of_oracleRun p q (fun t s tr sc ho => ?_) h
  obtain ⟨rfl, hrun⟩ := ho
  exact ⟨[], q, [], by simp [shiftProg_zero], rfl, hq, hrun⟩

/-- Under the regime `doitm`, the stack operations of a call from two states with equal
    stack registers have equal leakage. -/
theorem blockLeakA_callOps_of_rsp {a b : AState} (n : Nat)
    (h : a.regs "%rsp" = b.regs "%rsp") :
    blockLeakA .doitm a (callOps n) = blockLeakA .doitm b (callOps n) := by
  simp only [callOps, blockLeakA, opLeak, instrLeak, resolveEv, List.map_cons, List.map_nil,
    evalInstrA_rsp_lea, h, List.append_nil, JInstr.mnem, DoitRegime.leaksOperands,
    X86Mnem.timing, Bool.false_eq_true, ite_false]

/-- Under the regime `doitm`, the stack operation of a return has no leakage. -/
theorem blockLeakA_retOps_doitm (s : AState) : blockLeakA .doitm s retOps = [] := by
  simp [retOps, blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
    X86Mnem.timing]

/-! ## 9. Segments of a caller and the composition of leakage -/

/-- Where a segment of a decoded program stops: at a `ret` in a state, or at the index
    `pc` of a `call tgt` in the state before the stack operations of the call. -/
inductive SegEnd where
  | halt (s : AState)
  | site (pc tgt : Nat) (s : AState)

/-- Two segment ends are related along `E`: both are a `ret`, or both are the same call
    site with the same target and states related by `E` at that site. -/
def SegEnd.Rel (E : Nat → Nat → AState → AState → Prop) : SegEnd → SegEnd → Prop
  | .halt _, .halt _ => True
  | .site pc tgt a, .site pc' tgt' b => pc = pc' ∧ tgt = tgt' ∧ E pc tgt a b
  | _, _ => False

/-- A segment of `prog` with leakage: the steps of `DecodedCT.RunL` other than `call`,
    from index `pc` and state `sa` to the first `ret` or `call`. -/
inductive SegRun (r : DoitRegime) (ok : AState → JInstr 64 → Prop) (prog : List RInstr) :
    Nat → AState → List CTLeak → SegEnd → Prop
  | ret {pc : Nat} {sa : AState} (h : prog[pc]? = some .ret) :
      SegRun r ok prog pc sa [] (.halt sa)
  | site {pc tgt : Nat} {sa : AState} (h : prog[pc]? = some (.call tgt)) :
      SegRun r ok prog pc sa [] (.site pc tgt sa)
  | op {pc : Nat} {sa : AState} {i : JInstr 64} {t : List CTLeak} {e : SegEnd}
      (h : prog[pc]? = some (.op i)) (hok : ok sa i)
      (hr : SegRun r ok prog (pc + 1) (evalInstrA sa i) t e) :
      SegRun r ok prog pc sa (opLeak r sa i ++ t) e
  | jcc {pc : Nat} {sa : AState} {cc tgt : Nat} {c : Condt} {t : List CTLeak} {e : SegEnd}
      (h : prog[pc]? = some (.jcc cc tgt)) (hc : condtOfNibble cc = some c)
      (hr : SegRun r ok prog (if sa.view.condB c then tgt else pc + 1) sa t e) :
      SegRun r ok prog pc sa (.branch (sa.view.condB c) :: t) e
  | stack {pc : Nat} {sa : AState} {ri : RInstr} {ops : List (JInstr 64)} {t : List CTLeak}
      {e : SegEnd} (h : prog[pc]? = some ri) (hops : ri.stackOps? = some ops)
      (hok : BlockOk ok sa ops) (hr : SegRun r ok prog (pc + 1) (runBlockA sa ops) t e) :
      SegRun r ok prog pc sa (blockLeakA r sa ops ++ t) e

/-- A chain of segments of `prog` joined by answers of the oracle: a segment to a `ret`,
    or a segment to a call site, the answer of `O` on the state after `callOps`, and a
    chain from the next index on the state after `retOps`. -/
inductive SegChain (r : DoitRegime) (ok : AState → JInstr 64 → Prop) (O : Nat → CalleeRun)
    (prog : List RInstr) : Nat → AState → List CTLeak → AState → Prop
  | last {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState}
      (h : SegRun r ok prog pc s t (.halt s')) : SegChain r ok O prog pc s t s'
  | link {pc pcc tgt : Nat} {s a sc s' : AState} {t₀ tc tr : List CTLeak}
      (h : SegRun r ok prog pc s t₀ (.site pcc tgt a))
      (hc : O tgt (runBlockA a (callOps (pcc + 1))) tc sc)
      (hr : SegChain r ok O prog (pcc + 1) (runBlockA sc retOps) tr s') :
      SegChain r ok O prog pc s
        (t₀ ++ (blockLeakA r a (callOps (pcc + 1)) ++ tc ++ blockLeakA r sc retOps ++ tr)) s'

/-- **A run under an oracle is a chain of segments** with the same trace. -/
theorem segChain_of_oracleRun {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {O : Nat → CalleeRun} {prog : List RInstr} {pc : Nat} {sa : AState} {t : List CTLeak}
    {sa' : AState} (h : OracleRun r ok O prog pc sa t sa') :
    SegChain r ok O prog pc sa t sa' := by
  induction h with
  | ret h => exact .last (.ret h)
  | op h hok _ ih =>
    cases ih with
    | last hs => exact .last (.op h hok hs)
    | link hs hc hr =>
      have hl := SegChain.link (.op h hok hs) hc hr
      rwa [List.append_assoc] at hl
  | jcc h hcc _ ih =>
    cases ih with
    | last hs => exact .last (.jcc h hcc hs)
    | link hs hc hr => exact SegChain.link (.jcc h hcc hs) hc hr
  | stack h hops hok _ ih =>
    cases ih with
    | last hs => exact .last (.stack h hops hok hs)
    | link hs hc hr =>
      have hl := SegChain.link (.stack h hops hok hs) hc hr
      rwa [List.append_assoc] at hl
  | call h _ hc _ _ ih => exact SegChain.link (.site h) hc ih

/-- **Composition of leakage along a chain of segments.** Let `I pc` relate two states at
    the index `pc` where a segment starts and `E pc tgt` two states at a call site.

    * `hseg`, the hypothesis on the caller: two segments from states related by `I` have
      equal traces and stop at related ends, so both stop at a `ret` or both at the same
      call site with states related by `E`.
    * `hcall`, the hypothesis on the call: at a call site with states related by `E`, the
      stack operations of the call have equal leakage, two answers of the oracle have
      equal traces, the stack operation of the return has equal leakage on the two
      answers, and the states after it are related by `I` at the next index.

    Then two chains from states related by `I` have equal traces. -/
theorem segChain_trace_eq {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {O : Nat → CalleeRun} {prog : List RInstr} {I : Nat → AState → AState → Prop}
    {E : Nat → Nat → AState → AState → Prop}
    (hseg : ∀ pc s₁ s₂ t₁ t₂ e₁ e₂, I pc s₁ s₂ → SegRun r ok prog pc s₁ t₁ e₁ →
      SegRun r ok prog pc s₂ t₂ e₂ → t₁ = t₂ ∧ SegEnd.Rel E e₁ e₂)
    (hcall : ∀ pc tgt a b tc₁ tc₂ sc₁ sc₂, E pc tgt a b →
      O tgt (runBlockA a (callOps (pc + 1))) tc₁ sc₁ →
      O tgt (runBlockA b (callOps (pc + 1))) tc₂ sc₂ →
      blockLeakA r a (callOps (pc + 1)) = blockLeakA r b (callOps (pc + 1)) ∧ tc₁ = tc₂
        ∧ blockLeakA r sc₁ retOps = blockLeakA r sc₂ retOps
        ∧ I (pc + 1) (runBlockA sc₁ retOps) (runBlockA sc₂ retOps))
    {pc : Nat} {s₁ : AState} {t₁ : List CTLeak} {s₁' : AState}
    (h₁ : SegChain r ok O prog pc s₁ t₁ s₁') :
    ∀ {s₂ : AState} {t₂ : List CTLeak} {s₂' : AState}, I pc s₁ s₂ →
      SegChain r ok O prog pc s₂ t₂ s₂' → t₁ = t₂ := by
  induction h₁ with
  | last h =>
    intro s₂ t₂ s₂' hI h₂
    cases h₂ with
    | last h' => exact (hseg _ _ _ _ _ _ _ hI h h').1
    | link h' _ _ => exact False.elim (hseg _ _ _ _ _ _ _ hI h h').2
  | link h hc _ ih =>
    intro s₂ t₂ s₂' hI h₂
    cases h₂ with
    | last h' => exact False.elim (hseg _ _ _ _ _ _ _ hI h h').2
    | link h' hc' hr' =>
      obtain ⟨rfl, hE⟩ := hseg _ _ _ _ _ _ _ hI h h'
      obtain ⟨rfl, rfl, hE⟩ : _ ∧ _ ∧ E _ _ _ _ := hE
      obtain ⟨e₁, rfl, e₃, hI'⟩ := hcall _ _ _ _ _ _ _ _ hE hc hc'
      rw [e₁, e₃, ih hI' hr']

/-- **Composition of leakage for a caller of several summarised callees.** Let distinct symbols
    of `fs` have distinct targets, let the callee `X f` of each symbol `f` of `fs` have the
    leakage summary `PubSummary (X f) (c f) (out f)`, and let the caller `prog` satisfy:

    * `hseg`: two segments from states related by `I` have equal traces and stop at
      related ends;
    * `hsite`: at a call site with target `tgt f` and states related by `E`, the states after
      the stack operations of the call satisfy the precondition of `c f` and are related by
      `(c f).pub`, and those operations have equal leakage;
    * `hback`: two returns of `X f` from such states, related by `out f`, give equal leakage
      of the stack operation of the return and states related by `I` at the next index.

    Then two runs with leakage of `prog` under the oracle of the callees, from states related
    by `I`, have equal traces. -/
theorem oracleRun_trace_eqMap {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {fs : List String} {tgt : String → Nat} {X : String → CalleeRun} {c : String → CalleeSig}
    {out : String → AState → AState → Prop}
    (hinj : ∀ f ∈ fs, ∀ g ∈ fs, tgt f = tgt g → f = g)
    (hsum : ∀ f ∈ fs, PubSummary (X f) (c f) (out f))
    {prog : List RInstr} {I : Nat → AState → AState → Prop}
    {E : Nat → Nat → AState → AState → Prop}
    (hseg : ∀ pc s₁ s₂ t₁ t₂ e₁ e₂, I pc s₁ s₂ → SegRun r ok prog pc s₁ t₁ e₁ →
      SegRun r ok prog pc s₂ t₂ e₂ → t₁ = t₂ ∧ SegEnd.Rel E e₁ e₂)
    (hsite : ∀ pc, ∀ f ∈ fs, ∀ a b, E pc (tgt f) a b →
      (c f).pre (runBlockA a (callOps (pc + 1))) ∧ (c f).pre (runBlockA b (callOps (pc + 1)))
        ∧ (c f).pub (runBlockA a (callOps (pc + 1))) (runBlockA b (callOps (pc + 1)))
        ∧ blockLeakA r a (callOps (pc + 1)) = blockLeakA r b (callOps (pc + 1)))
    (hback : ∀ pc, ∀ f ∈ fs, ∀ a b t₁ t₂ sc₁ sc₂, E pc (tgt f) a b →
      X f (runBlockA a (callOps (pc + 1))) t₁ sc₁ →
      X f (runBlockA b (callOps (pc + 1))) t₂ sc₂ → out f sc₁ sc₂ →
      blockLeakA r sc₁ retOps = blockLeakA r sc₂ retOps
        ∧ I (pc + 1) (runBlockA sc₁ retOps) (runBlockA sc₂ retOps))
    {pc : Nat} {s₁ s₂ s₁' s₂' : AState} {t₁ t₂ : List CTLeak} (hI : I pc s₁ s₂)
    (h₁ : OracleRun r ok (tracedOf fs tgt X) prog pc s₁ t₁ s₁')
    (h₂ : OracleRun r ok (tracedOf fs tgt X) prog pc s₂ t₂ s₂') : t₁ = t₂ := by
  refine segChain_trace_eq hseg (fun pc tg a b tc₁ tc₂ sc₁ sc₂ hE ho₁ ho₂ => ?_)
    (segChain_of_oracleRun h₁) hI (segChain_of_oracleRun h₂)
  obtain ⟨f, hf, rfl, hx₁⟩ := ho₁
  obtain ⟨g, hg, hgf, hx₂⟩ := ho₂
  obtain rfl := hinj g hg f hf hgf
  obtain ⟨hp₁, hp₂, hpub, hl⟩ := hsite pc g hf a b hE
  obtain ⟨hb₁, hb₂⟩ := hback pc g hf a b tc₁ tc₂ sc₁ sc₂ hE hx₁ hx₂
    ((hsum g hf).exit _ _ _ _ _ _ hp₁ hp₂ hpub hx₁ hx₂)
  exact ⟨hl, (hsum g hf).trace _ _ _ _ _ _ hp₁ hp₂ hpub hx₁ hx₂, hb₁, hb₂⟩

/-- **Composition of leakage for a caller of one summarised callee.** Let the callee `X`
    have the leakage summary `PubSummary X c out`, and let the caller `prog` satisfy:

    * `hseg`: two segments from states related by `I` have equal traces and stop at
      related ends;
    * `hsite`: at a call site with states related by `E`, the states after the stack
      operations of the call satisfy the precondition of `c` and are related by `c.pub`,
      and those operations have equal leakage;
    * `hback`: two returns of the callee from such states, related by `out`, give equal
      leakage of the stack operation of the return and states related by `I` at the next
      index.

    Then two runs with leakage of `prog` under the oracle of `X`, from states related by
    `I`, have equal traces. This is `oracleRun_trace_eqMap` at one symbol. -/
theorem oracleRun_trace_eq {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {X : CalleeRun}
    {c : CalleeSig} {out : AState → AState → Prop} (hsum : PubSummary X c out)
    {prog : List RInstr} {tgt : Nat} {I : Nat → AState → AState → Prop}
    {E : Nat → Nat → AState → AState → Prop}
    (hseg : ∀ pc s₁ s₂ t₁ t₂ e₁ e₂, I pc s₁ s₂ → SegRun r ok prog pc s₁ t₁ e₁ →
      SegRun r ok prog pc s₂ t₂ e₂ → t₁ = t₂ ∧ SegEnd.Rel E e₁ e₂)
    (hsite : ∀ pc tg a b, E pc tg a b →
      c.pre (runBlockA a (callOps (pc + 1))) ∧ c.pre (runBlockA b (callOps (pc + 1)))
        ∧ c.pub (runBlockA a (callOps (pc + 1))) (runBlockA b (callOps (pc + 1)))
        ∧ blockLeakA r a (callOps (pc + 1)) = blockLeakA r b (callOps (pc + 1)))
    (hback : ∀ pc tg a b t₁ t₂ sc₁ sc₂, E pc tg a b →
      X (runBlockA a (callOps (pc + 1))) t₁ sc₁ → X (runBlockA b (callOps (pc + 1))) t₂ sc₂ →
      out sc₁ sc₂ →
      blockLeakA r sc₁ retOps = blockLeakA r sc₂ retOps
        ∧ I (pc + 1) (runBlockA sc₁ retOps) (runBlockA sc₂ retOps))
    {pc : Nat} {s₁ s₂ s₁' s₂' : AState} {t₁ t₂ : List CTLeak} (hI : I pc s₁ s₂)
    (h₁ : OracleRun r ok (tracedAt tgt X) prog pc s₁ t₁ s₁')
    (h₂ : OracleRun r ok (tracedAt tgt X) prog pc s₂ t₂ s₂') : t₁ = t₂ := by
  rw [← tracedOf_one ""] at h₁ h₂
  exact oracleRun_trace_eqMap (fs := [""]) (tgt := fun _ => tgt) (X := fun _ => X)
    (c := fun _ => c) (out := fun _ => out) (fun _ hf _ hg _ => by simp_all) (fun _ _ => hsum)
    hseg (fun pc _ _ a b hE => hsite pc _ a b hE)
    (fun pc _ _ a b _ _ _ _ hE hx₁ hx₂ ho => hback pc _ a b _ _ _ _ hE hx₁ hx₂ ho) hI h₁ h₂

/-- **Equal leakage of the linked program.** Let `q` be a block without `call` whose leaky
    run has the leakage summary `PubSummary (runOf r q) c out`, and let the caller `p`
    satisfy `hseg`, `hsite` and `hback` of `oracleRun_trace_eq`. If `p` halts under the
    oracle of `q` at the target `p.length` from two states related by `I 0`, every two
    runs with leakage of `p` followed by the relocated copy of `q` from these states have
    equal traces. -/
theorem linkedRun_trace_eq {r : DoitRegime} {p q : List RInstr}
    (hq : ∀ tg, RInstr.call tg ∉ q) {c : CalleeSig} {out : AState → AState → Prop}
    (hsum : PubSummary (runOf r q) c out) {I : Nat → AState → AState → Prop}
    {E : Nat → Nat → AState → AState → Prop}
    (hseg : ∀ pc s₁ s₂ t₁ t₂ e₁ e₂, I pc s₁ s₂ →
      SegRun r (fun _ _ => True) p pc s₁ t₁ e₁ →
      SegRun r (fun _ _ => True) p pc s₂ t₂ e₂ → t₁ = t₂ ∧ SegEnd.Rel E e₁ e₂)
    (hsite : ∀ pc tg a b, E pc tg a b →
      c.pre (runBlockA a (callOps (pc + 1))) ∧ c.pre (runBlockA b (callOps (pc + 1)))
        ∧ c.pub (runBlockA a (callOps (pc + 1))) (runBlockA b (callOps (pc + 1)))
        ∧ blockLeakA r a (callOps (pc + 1)) = blockLeakA r b (callOps (pc + 1)))
    (hback : ∀ pc tg a b t₁ t₂ sc₁ sc₂, E pc tg a b →
      runOf r q (runBlockA a (callOps (pc + 1))) t₁ sc₁ →
      runOf r q (runBlockA b (callOps (pc + 1))) t₂ sc₂ → out sc₁ sc₂ →
      blockLeakA r sc₁ retOps = blockLeakA r sc₂ retOps
        ∧ I (pc + 1) (runBlockA sc₁ retOps) (runBlockA sc₂ retOps))
    {s₁ s₂ s₁' s₂' : AState} (hI : I 0 s₁ s₂)
    (h₁ : HaltsO aMachine (oracleAt p.length (runOf r q)) p 0 s₁ s₁')
    (h₂ : HaltsO aMachine (oracleAt p.length (runOf r q)) p 0 s₂ s₂')
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState}
    (hr₁ : RunL r ok₁ (p ++ shiftProg p.length q) 0 s₁ t₁ e₁)
    (hr₂ : RunL r ok₂ (p ++ shiftProg p.length q) 0 s₂ t₂ e₂) : t₁ = t₂ := by
  obtain ⟨u₁, ho₁⟩ := oracleRun_of_haltsO_oracleAt r h₁
  obtain ⟨u₂, ho₂⟩ := oracleRun_of_haltsO_oracleAt r h₂
  obtain ⟨rfl, _⟩ := runL_det (runL_append_of_oracleRun p q hq ho₁) hr₁
  obtain ⟨rfl, _⟩ := runL_det (runL_append_of_oracleRun p q hq ho₂) hr₂
  exact oracleRun_trace_eq hsum hseg hsite hback hI ho₁ ho₂

/-- **Constant time of the linked program.** Under the hypotheses of
    `linkedRun_trace_eq`, the leaky runs of `p` followed by the relocated copy of `q` are
    constant time for the relation `I 0` on states from which `p` halts under the oracle
    of `q`. -/
theorem linkedRun_constantTime {r : DoitRegime} {p q : List RInstr}
    (hq : ∀ tg, RInstr.call tg ∉ q) {c : CalleeSig} {out : AState → AState → Prop}
    (hsum : PubSummary (runOf r q) c out) {I : Nat → AState → AState → Prop}
    {E : Nat → Nat → AState → AState → Prop}
    (hseg : ∀ pc s₁ s₂ t₁ t₂ e₁ e₂, I pc s₁ s₂ →
      SegRun r (fun _ _ => True) p pc s₁ t₁ e₁ →
      SegRun r (fun _ _ => True) p pc s₂ t₂ e₂ → t₁ = t₂ ∧ SegEnd.Rel E e₁ e₂)
    (hsite : ∀ pc tg a b, E pc tg a b →
      c.pre (runBlockA a (callOps (pc + 1))) ∧ c.pre (runBlockA b (callOps (pc + 1)))
        ∧ c.pub (runBlockA a (callOps (pc + 1))) (runBlockA b (callOps (pc + 1)))
        ∧ blockLeakA r a (callOps (pc + 1)) = blockLeakA r b (callOps (pc + 1)))
    (hback : ∀ pc tg a b t₁ t₂ sc₁ sc₂, E pc tg a b →
      runOf r q (runBlockA a (callOps (pc + 1))) t₁ sc₁ →
      runOf r q (runBlockA b (callOps (pc + 1))) t₂ sc₂ → out sc₁ sc₂ →
      blockLeakA r sc₁ retOps = blockLeakA r sc₂ retOps
        ∧ I (pc + 1) (runBlockA sc₁ retOps) (runBlockA sc₂ retOps)) :
    ConstantTimeRel
      (fun s₁ s₂ => I 0 s₁ s₂
        ∧ (∃ s', HaltsO aMachine (oracleAt p.length (runOf r q)) p 0 s₁ s')
        ∧ ∃ s', HaltsO aMachine (oracleAt p.length (runOf r q)) p 0 s₂ s')
      (fun s t => ∃ s', RunL r (fun _ _ => True) (p ++ shiftProg p.length q) 0 s t s') := by
  rintro s₁ s₂ t₁ t₂ ⟨hI, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ ⟨_, hr₁⟩ ⟨_, hr₂⟩
  exact linkedRun_trace_eq hq hsum hseg hsite hback hI h₁ h₂ hr₁ hr₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
