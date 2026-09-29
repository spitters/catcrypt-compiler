/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage
public import CatCrypt.Crypto.Jasmin.LowCTTypes

/-!
# Constant time of decoded programs on the address machine

A leakage semantics for decoded programs (`List RInstr`) on the address machine
`RInstrAddrMem.aMachine`, and a checker whose acceptance gives constant time in that
semantics.

## The leakage semantics

`RunL r ok prog pc sa t sa'` is a halting run of `prog` from index `pc` and state `sa`
with leakage trace `t` and final state `sa'`, in the event type `CT.CTLeak`:

* an `op i` emits `opLeak r sa i`: each memory access of `i` as an `addr` event whose
  offset is the effective address, the value of the base register plus the displacement
  or the scaled index (region `""`, the flat memory), followed by a `vt` event with the
  data operands when the regime `r` makes them observable;
* a `jcc` emits the `branch` event of its outcome;
* a `call` emits the leakage of `callOps`, the callee's trace as a nested run, and the
  leakage of `retOps`;
* `ret` ends the innermost run.

Each `op` step also satisfies the side condition `ok sa i`. `RunL.halts` and `haltsC_runL`
relate `RunL` with the trivial side condition to `RInstrSemantics.HaltsC` on `aMachine`,
and `halts_runL` covers the call-free `RInstrSemantics.Halts`.

## The checker

`PubA` is a set of public locations: registers, words `%rsp + o` of the frame given by
their offsets `o`, and the flags. `stepA P i` is the public set after `i`: a register is
public after a `mov` of a public operand, a `lea` of public registers, a two-address
arithmetic, logical or shift operation of public operands, or a load of a public frame
word; a frame word after a store of a public operand through `%rsp`, and at offset `o - k`
after `lea k(%rsp), %rsp` when it was public at `o`; the flags after a `cmp` of public
operands.

`checkCert r F own X prog A` checks a certificate `A` (a public set per index, `none` for
an index the analysis does not reach) under an owner map `own` (the entry of the function
each index belongs to) and exit sets `X` (one per function entry): at each index with a
public set, every frame word public there is in `F`; an `op` is quiet under `r` and
accesses memory through public base and index registers, and its successor's set is below
`stepA`; a `jcc` reads public flags and both successors' sets are below the current one;
every non-call successor has the owner of its predecessor; a `ret` is above the exit set
of its owner. A `call t` is checked against a callee summary: `callOps` are checked,
the callee entry `t` is below the set after them, and the successor is below the set
`retOps` leave from the exit set of `t`'s owner. `infer prog P` computes a certificate by
a forward analysis, and `bytesCTCheck r F P prog` checks it with the entry set below `P`,
the owners of the call targets (`ownerOf`) and the exit sets of the certificate
(`exitSet`).

## Separation

The address machine has one flat memory, so a store through a base other than `%rsp` can
overwrite a frame word. `FrameSep F sa i` is the hypothesis that it does not: every
address that `i` writes through a base other than `%rsp` is eight bytes apart from each
word `%rsp + o`, `o ∈ F`. The soundness theorems hold for runs whose steps all satisfy
`FrameSep F`.

## Main results

* `checkCert_sound`: under a passing certificate, two runs from an index, from states
  agreeing on its set, have equal traces and end agreeing on the exit set of the index's
  function; the `call` case composes the callee's run through that exit set.
* `bytesCTCheck_sound`: if `bytesCTCheck r F P prog` holds, two runs of `prog` from states
  agreeing on `P`, whose steps satisfy `FrameSep F`, have equal leakage traces.
* `bytesCTCheckFast_sound`: the same for the array form of the decision.

The acceptance of two shipped kernels, decided by the kernel, is in
`X86Backend.DecodedCTKernels`, so that this module imports no kernel.

## Frame words from the certificate and the public set from the ABI

`certCells A` is the list of frame words public somewhere in the certificate `A`, and
`bytesCTCheckAuto r P prog` is `bytesCTCheck` with the frame words of the inferred
certificate; `bytesCTCheckAuto_sound` is its soundness, under `FrameSep` for those
words. `abiPubA ps lt` is the public entry set of a function with parameters `ps`
under the level table `lt` and the System V calling convention: `%rsp`, the register
of each of the first six parameters that is a pointer or public in `lt`, and the
stack word `%rsp + 8 (k + 1)` of the parameter at position `6 + k` under the same
condition. `abiPubA_regs_iff` and `abiPubA_cells_iff` state its content. `failAt`
and `firstFailure` name the first index at which the check fails and why.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
  (RInstr pushOps popOps callOps retOps)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. The leakage semantics -/

/-- A memory event of `instrLeak` with its effective address resolved in `sa`. -/
def resolveEv (sa : AState) : MLeak → CTLeak
  | .branch => .branch true
  | .mem b o => .addr "" ((sa.regs b + BitVec.ofInt 64 o).toNat : Int)

/-- The leakage of one instruction on the address machine: its memory accesses at their
    effective addresses, then a `vt` event with its data operands when the regime makes
    them observable. -/
def opLeak (r : DoitRegime) (sa : AState) (i : JInstr 64) : List CTLeak :=
  (instrLeak sa.view i).map (resolveEv sa) ++
    (if r.leaksOperands i.mnem then [.vt i.mnem (i.dataArgs sa.view)] else [])

/-- The leakage of a straight-line block on the address machine, the state threaded by
    `evalInstrA`. -/
def blockLeakA (r : DoitRegime) (sa : AState) : List (JInstr 64) → List CTLeak
  | [] => []
  | i :: is => opLeak r sa i ++ blockLeakA r (evalInstrA sa i) is

/-- Every instruction of a straight-line block satisfies `ok` in the state it runs in. -/
def BlockOk (ok : AState → JInstr 64 → Prop) (sa : AState) : List (JInstr 64) → Prop
  | [] => True
  | i :: is => ok sa i ∧ BlockOk ok (evalInstrA sa i) is

theorem BlockOk.mono {ok ok' : AState → JInstr 64 → Prop} (hok : ∀ sa i, ok sa i → ok' sa i) :
    ∀ (ops : List (JInstr 64)) (sa : AState), BlockOk ok sa ops → BlockOk ok' sa ops
  | [], _, _ => trivial
  | _ :: is, _, ⟨h, hs⟩ => ⟨hok _ _ h, BlockOk.mono hok is _ hs⟩

theorem blockOk_true : ∀ (ops : List (JInstr 64)) (sa : AState), BlockOk (fun _ _ => True) sa ops
  | [], _ => trivial
  | _ :: is, _ => ⟨trivial, blockOk_true is _⟩

/-- The fold of `aMachine`'s step over a block is `runBlockA`. -/
theorem foldl_aMachine_exec (ops : List (JInstr 64)) :
    ∀ sa, ops.foldl aMachine.exec sa = runBlockA sa ops := by
  induction ops with
  | nil => intro sa; rfl
  | cons i is ih => intro sa; exact ih _

/-- A halting run of `prog` on the address machine from index `pc` and state `sa`, with
    leakage trace `t` and final state `sa'`, each instruction the run executes satisfying
    `ok`. A `push` or `pop` runs its straight-line effect (`RInstr.stackOps?`) and emits
    the leakage of that block. A `call tgt` runs `callOps`, then the callee from `tgt` to
    its `ret` as a nested run, then `retOps`, and continues at the next index; its trace
    is the leakage of the two blocks around the callee's trace. -/
inductive RunL (r : DoitRegime) (ok : AState → JInstr 64 → Prop) (prog : List RInstr) :
    Nat → AState → List CTLeak → AState → Prop
  | ret {pc : Nat} {sa : AState} (h : prog[pc]? = some .ret) : RunL r ok prog pc sa [] sa
  | op {pc : Nat} {sa : AState} {i : JInstr 64} {t : List CTLeak} {sa' : AState}
      (h : prog[pc]? = some (.op i)) (hok : ok sa i)
      (hr : RunL r ok prog (pc + 1) (evalInstrA sa i) t sa') :
      RunL r ok prog pc sa (opLeak r sa i ++ t) sa'
  | jcc {pc : Nat} {sa : AState} {cc tgt : Nat} {c : Condt} {t : List CTLeak} {sa' : AState}
      (h : prog[pc]? = some (.jcc cc tgt)) (hc : condtOfNibble cc = some c)
      (hr : RunL r ok prog (if sa.view.condB c then tgt else pc + 1) sa t sa') :
      RunL r ok prog pc sa (.branch (sa.view.condB c) :: t) sa'
  | stack {pc : Nat} {sa : AState} {ri : RInstr} {ops : List (JInstr 64)} {t : List CTLeak}
      {sa' : AState} (h : prog[pc]? = some ri) (hops : ri.stackOps? = some ops)
      (hok : BlockOk ok sa ops) (hr : RunL r ok prog (pc + 1) (runBlockA sa ops) t sa') :
      RunL r ok prog pc sa (blockLeakA r sa ops ++ t) sa'
  | call {pc tgt : Nat} {sa sc : AState} {tc tr : List CTLeak} {sa' : AState}
      (h : prog[pc]? = some (.call tgt)) (hok : BlockOk ok sa (callOps (pc + 1)))
      (hc : RunL r ok prog tgt (runBlockA sa (callOps (pc + 1))) tc sc)
      (hokr : BlockOk ok sc retOps)
      (hr : RunL r ok prog (pc + 1) (runBlockA sc retOps) tr sa') :
      RunL r ok prog pc sa
        (blockLeakA r sa (callOps (pc + 1)) ++ tc ++ blockLeakA r sc retOps ++ tr) sa'

/-- A run with leakage is a halting run of `aMachine` through calls. -/
theorem RunL.halts {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {prog : List RInstr}
    {pc : Nat} {sa : AState} {t : List CTLeak} {sa' : AState}
    (h : RunL r ok prog pc sa t sa') : HaltsC aMachine prog pc sa sa' := by
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
  | call h _ _ _ _ ihc ihr =>
    rw [← foldl_aMachine_exec] at ihc ihr
    exact .call h ihc ihr

/-- Every halting run of `aMachine` through calls has a leakage trace. -/
theorem haltsC_runL (r : DoitRegime) {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    (h : HaltsC aMachine prog pc sa sa') :
    ∃ t, RunL r (fun _ _ => True) prog pc sa t sa' := by
  induction h with
  | ret hret => exact ⟨[], .ret hret⟩
  | call h _ _ ihc ihr =>
    obtain ⟨tc, htc⟩ := ihc
    obtain ⟨tr, htr⟩ := ihr
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

/-- Every call-free halting run of `aMachine` has a leakage trace. -/
theorem halts_runL (r : DoitRegime) {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    (h : Halts aMachine prog pc sa sa') :
    ∃ t, RunL r (fun _ _ => True) prog pc sa t sa' :=
  haltsC_runL r (haltsC_of_halts h)

/-- `RunL` under a stronger side condition is `RunL` under a weaker one. -/
theorem RunL.mono {r : DoitRegime} {ok ok' : AState → JInstr 64 → Prop} {prog : List RInstr}
    (hok : ∀ sa i, ok sa i → ok' sa i) {pc : Nat} {sa : AState} {t : List CTLeak}
    {sa' : AState} (h : RunL r ok prog pc sa t sa') : RunL r ok' prog pc sa t sa' := by
  induction h with
  | ret h => exact .ret h
  | op h ho _ ih => exact .op h (hok _ _ ho) ih
  | jcc h hc _ ih => exact .jcc h hc ih
  | stack h hops ho _ ih => exact .stack h hops (BlockOk.mono hok _ _ ho) ih
  | call h ho _ hor _ ihc ihr =>
    exact .call h (BlockOk.mono hok _ _ ho) ihc (BlockOk.mono hok _ _ hor) ihr

/-! ## 2. Public sets -/

/-- A set of public locations: registers, words `%rsp + o` of the frame by offset, and
    the flags. -/
structure PubA where
  /-- The public registers. -/
  regs : List String
  /-- The offsets from `%rsp` of the public frame words. -/
  cells : List Int
  /-- Whether the flags are public. -/
  flags : Bool
  deriving DecidableEq, Repr

/-- The frame word at offset `o` from `%rsp`. -/
def cellAt (sa : AState) (o : Int) : BitVec 64 :=
  read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 o)

/-- Two address states agree on every location of `P`. -/
def PubA.Agree (P : PubA) (s₁ s₂ : AState) : Prop :=
  (∀ x ∈ P.regs, s₁.regs x = s₂.regs x) ∧ (∀ o ∈ P.cells, cellAt s₁ o = cellAt s₂ o) ∧
    (P.flags = true → s₁.flags = s₂.flags)

/-- `A.le B`: every location of `A` is a location of `B`. -/
def PubA.le (A B : PubA) : Bool :=
  A.regs.all B.regs.contains && A.cells.all B.cells.contains && (!A.flags || B.flags)

theorem PubA.agree_of_le {A B : PubA} (h : A.le B = true) {s₁ s₂ : AState}
    (hB : B.Agree s₁ s₂) : A.Agree s₁ s₂ := by
  simp only [PubA.le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hr, hc⟩, hf⟩ := h
  refine ⟨fun x hx => hB.1 x (hr x hx), fun o ho => hB.2.1 o (hc o ho), fun ha => ?_⟩
  rcases hf with hf | hf
  · simp [hf] at ha
  · exact hB.2.2 hf

/-- An operand whose value is determined by `P`. -/
def opPub (P : PubA) : JOperand → Bool
  | .reg x => P.regs.contains x
  | .imm _ => true

theorem opPub_eval {P : PubA} {o : JOperand} (h : opPub P o = true) {s₁ s₂ : AState}
    (hag : P.Agree s₁ s₂) : o.eval s₁.view = o.eval s₂.view := by
  cases o with
  | reg x =>
    simp only [opPub, List.contains_iff_mem] at h
    simp [AState.view, hag.1 x h]
  | imm v => rfl

/-! ## 3. The transfer function -/

/-- The base register of a memory access of `i`. -/
def memBase : JInstr 64 → Option String
  | .loadMem _ b _ | .storeMem b _ _ | .mulxMem _ _ _ b _ | .addMem _ b _
  | .adcxMem _ b _ | .adoxMem _ b _ | .imulMem _ b _ | .imulriMem _ b _ _
  | .addToMem b _ _ | .cmpMem _ b _ | .loadMemIdx _ b _ _ | .storeMemIdx b _ _ _ => some b
  | _ => none

/-- `i` writes memory through the base register `%rsp`. -/
def frameWrite : JInstr 64 → Bool
  | .storeMem b _ _ | .addToMem b _ _ | .storeMemIdx b _ _ _ => b == "%rsp"
  | _ => false

/-- `i` writes memory through a base other than `%rsp`: the writes `FrameSep` keeps apart
    from the frame words. -/
def sepWrite : JInstr 64 → Bool
  | .storeMem b _ _ | .addToMem b _ _ | .storeMemIdx b _ _ _ => b != "%rsp"
  | _ => false

/-- The frame words at offsets `o` and `o'` do not overlap. -/
def far (o o' : Int) : Bool := 8 ≤ (o - o').natAbs && (o - o').natAbs ≤ 2 ^ 64 - 8

/-- The registers `i` writes with a value determined by `P`. -/
def newRegs (P : PubA) : JInstr 64 → List String
  | .mov d src => if opPub P src then [d] else []
  | .loadMem d b o => if b == "%rsp" && P.cells.contains o then [d] else []
  | .lea d b x _ _ => if P.regs.contains b && P.regs.contains x then [d] else []
  | .add d src | .sub d src | .and_ d src | .or_ d src | .xor_ d src
  | .shl d src | .shr d src | .sar d src =>
      if P.regs.contains d && opPub P src then [d] else []
  | .neg d => if P.regs.contains d then [d] else []
  | _ => []

/-- The public frame words after `i`, when `i` does not write `%rsp`. -/
def newCells (P : PubA) : JInstr 64 → List Int
  | .storeMem b o src =>
      if b == "%rsp" then (if opPub P src then [o] else []) ++ P.cells.filter (far o)
      else P.cells
  | i => if frameWrite i then [] else P.cells

/-- The displacement `k` of the frame adjustment `lea k(%rsp), %rsp`: the one write of
    `%rsp` under which every frame word keeps its value, at an offset shifted by `-k`. -/
def rspShift : JInstr 64 → Option Int
  | .lea d b _ sc k => if d = "%rsp" ∧ b = "%rsp" ∧ sc = 0 then some k else none
  | _ => none

/-- The public set after `i`. -/
def stepA (P : PubA) (i : JInstr 64) : PubA where
  regs := newRegs P i ++ P.regs.filter (fun x => !(dstRegs i).contains x)
  cells := match rspShift i with
    | some k => P.cells.map (· - k)
    | none => if (dstRegs i).contains "%rsp" then [] else newCells P i
  flags := match i with
    | .cmp a o => P.regs.contains a && opPub P o
    | .cmpMem a b o => P.regs.contains a && b == "%rsp" && P.cells.contains o
    | _ => false

/-- The separation hypothesis: every address `i` writes through a base other than `%rsp`
    is eight bytes apart from each frame word `%rsp + o`, `o ∈ F`. -/
def FrameSep (F : List Int) (sa : AState) (i : JInstr 64) : Prop :=
  frameWrite i = false → ∀ a, writeAddr sa i = some a →
    ∀ o ∈ F, Disjoint8 a (sa.regs "%rsp" + BitVec.ofInt 64 o)

theorem evalInstrA_regs (sa : AState) (i : JInstr 64) (x : String) :
    (evalInstrA sa i).regs x = (evalInstr sa.view i).get x := rfl

theorem evalInstrA_regs_of_not_dst (sa : AState) (i : JInstr 64) (x : String)
    (h : x ∉ dstRegs i) : (evalInstrA sa i).regs x = sa.regs x := by
  rw [evalInstrA_regs, evalInstr_get_of_not_dst _ _ _ h]
  rfl

/-- A frame word that no write of `i` overlaps keeps its value. -/
theorem cellAt_preserved (sa : AState) (i : JInstr 64) (hrsp : "%rsp" ∉ dstRegs i) (o : Int)
    (hsep : ∀ a, writeAddr sa i = some a → Disjoint8 a (sa.regs "%rsp" + BitVec.ofInt 64 o)) :
    cellAt (evalInstrA sa i) o = cellAt sa o := by
  unfold cellAt
  rw [evalInstrA_regs_of_not_dst sa i _ hrsp]
  simp only [evalInstrA]
  split
  · rename_i a ha
    exact read64_write64_of_disjoint _ _ _ _ (hsep a ha)
  · rfl

theorem rspShift_eq {i : JInstr 64} {k : Int} (h : rspShift i = some k) :
    ∃ x, i = .lea "%rsp" "%rsp" x 0 k := by
  cases i with
  | lea d b x sc k' =>
    simp only [rspShift] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨x, rfl⟩
    · simp at h
  | _ => simp [rspShift] at h

/-- After `lea k(%rsp), %rsp` the frame word at offset `o - k` is the word that was at
    offset `o`. -/
theorem cellAt_rspShift (sa : AState) (x : String) (k o : Int) :
    cellAt (evalInstrA sa (.lea "%rsp" "%rsp" x 0 k)) (o - k) = cellAt sa o := by
  have ho : BitVec.ofInt 64 o = BitVec.ofInt 64 k + BitVec.ofInt 64 (o - k) := by
    rw [← BitVec.ofInt_add]
    congr 1
    omega
  simp [cellAt, evalInstrA, writeAddr, evalInstr, JState.setReg, JState.get, x86_LEA,
    AState.view, ho, BitVec.add_assoc]

theorem newRegs_sound (P : PubA) (i : JInstr 64) {s₁ s₂ : AState} (hag : P.Agree s₁ s₂) :
    ∀ x ∈ newRegs P i, (evalInstrA s₁ i).regs x = (evalInstrA s₂ i).regs x := by
  intro x hx
  rw [evalInstrA_regs, evalInstrA_regs]
  cases i with
  | mov d src =>
    simp only [newRegs] at hx
    split at hx
    · rename_i h
      simp only [List.mem_singleton] at hx
      subst hx
      simp only [evalInstr, JState.get_setReg_same, opPub_eval h hag]
    · simp at hx
  | loadMem d b o =>
    simp only [newRegs] at hx
    split at hx
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
      obtain ⟨rfl, h⟩ := h
      simp only [List.mem_singleton] at hx
      subst hx
      have := hag.2.1 o h
      simp only [cellAt] at this
      simp [evalInstr, JState.setReg, AState.view, this]
    · simp at hx
  | lea d b y sc off =>
    simp only [newRegs] at hx
    split at hx
    · rename_i h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      simp only [List.mem_singleton] at hx
      subst hx
      simp [evalInstr, JState.setReg, AState.view, hag.1 _ h.1, hag.1 _ h.2]
    · simp at hx
  | add d src | sub d src | and_ d src | or_ d src | xor_ d src | shl d src | shr d src
  | sar d src =>
    simp only [newRegs] at hx
    split at hx
    · rename_i h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      simp only [List.mem_singleton] at hx
      subst hx
      have hd : s₁.view.get x = s₂.view.get x := by simp [AState.view, hag.1 _ h.1]
      simp only [evalInstr, JState.writeB5W, JState.get]
      rw [show s₁.view.regs x = s₁.view.get x from rfl, show s₂.view.regs x = s₂.view.get x from rfl,
        hd, opPub_eval h.2 hag]
    · simp at hx
  | neg d =>
    simp only [newRegs] at hx
    split at hx
    · rename_i h
      simp only [List.contains_iff_mem] at h
      simp only [List.mem_singleton] at hx
      subst hx
      have hd : s₁.view.get x = s₂.view.get x := by simp [AState.view, hag.1 _ h]
      simp only [evalInstr, JState.writeB5W, JState.get]
      rw [show s₁.view.regs x = s₁.view.get x from rfl, show s₂.view.regs x = s₂.view.get x from rfl,
        hd]
    · simp at hx
  | _ => simp [newRegs] at hx

/-- **Soundness of one step.** Two states agreeing on `P`, each satisfying `FrameSep F`
    at `i`, with the frame words of `P` in `F`, agree on `stepA P i` after `i`. -/
theorem sepWrite_of_writeAddr {sa : AState} {i : JInstr 64} {a : BitVec 64}
    (h : writeAddr sa i = some a) (hfw : frameWrite i = false) : sepWrite i = true := by
  cases i <;> simp_all [writeAddr, frameWrite, sepWrite]

theorem stepA_sound (P : PubA) (i : JInstr 64) {F : List Int}
    (hF : sepWrite i = true → ∀ o ∈ P.cells, o ∈ F)
    {s₁ s₂ : AState} (hag : P.Agree s₁ s₂) (h₁ : FrameSep F s₁ i) (h₂ : FrameSep F s₂ i) :
    (stepA P i).Agree (evalInstrA s₁ i) (evalInstrA s₂ i) := by
  refine ⟨fun x hx => ?_, fun o ho => ?_, fun hf => ?_⟩
  · simp only [stepA, List.mem_append, List.mem_filter, Bool.not_eq_true'] at hx
    rcases hx with hx | ⟨hx, hnd⟩
    · exact newRegs_sound P i hag x hx
    · have hnd : x ∉ dstRegs i := by simpa using hnd
      rw [evalInstrA_regs_of_not_dst _ _ _ hnd, evalInstrA_regs_of_not_dst _ _ _ hnd]
      exact hag.1 x hx
  · simp only [stepA] at ho
    cases hsh : rspShift i with
    | some k =>
      rw [hsh] at ho
      obtain ⟨x, rfl⟩ := rspShift_eq hsh
      simp only [List.mem_map] at ho
      obtain ⟨o', ho', rfl⟩ := ho
      rw [cellAt_rspShift, cellAt_rspShift]
      exact hag.2.1 o' ho'
    | none =>
    rw [hsh] at ho
    simp only at ho
    split at ho
    · simp at ho
    · rename_i hrsp
      have hrsp' : "%rsp" ∉ dstRegs i := by simpa using hrsp
      -- a write not through `%rsp` misses every frame word of `F`
      have hpres : ∀ s : AState, FrameSep F s i → frameWrite i = false → ∀ o ∈ P.cells,
          cellAt (evalInstrA s i) o = cellAt s o := fun s hs hfw o ho =>
        cellAt_preserved s i hrsp' o fun a ha =>
          hs hfw a ha o (hF (sepWrite_of_writeAddr ha hfw) o ho)
      cases i with
      | storeMem b off src =>
        simp only [newCells] at ho
        by_cases hb : b = "%rsp"
        · subst hb
          simp only [beq_self_eq_true, if_true, List.mem_append, List.mem_filter] at ho
          have hw : ∀ s : AState, writeAddr s (.storeMem "%rsp" off src)
              = some (s.regs "%rsp" + BitVec.ofInt 64 off) := fun _ => rfl
          rcases ho with ho | ⟨ho, hfar⟩
          · split at ho
            · rename_i hs
              simp only [List.mem_singleton] at ho
              subst ho
              unfold cellAt
              rw [evalInstrA_regs_of_not_dst _ _ _ hrsp', evalInstrA_regs_of_not_dst _ _ _ hrsp']
              simp only [evalInstrA, hw, read64_write64_same, writeVal, opPub_eval hs hag]
            · simp at ho
          · simp only [far, Bool.and_eq_true, decide_eq_true_eq] at hfar
            have hd : ∀ s : AState, cellAt (evalInstrA s (.storeMem "%rsp" off src)) o
                = cellAt s o := fun s =>
              cellAt_preserved s _ hrsp' o fun a ha => by
                rw [hw, Option.some.injEq] at ha
                subst ha
                exact disjoint8_add_ofInt _ _ _ hfar.1 hfar.2
            rw [hd, hd]
            exact hag.2.1 o ho
        · have hfw : frameWrite (.storeMem b off src) = false := by simp [frameWrite, hb]
          simp only [show (b == "%rsp") = false from by simpa using hb] at ho
          rw [hpres s₁ h₁ hfw o ho, hpres s₂ h₂ hfw o ho]
          exact hag.2.1 o ho
      | _ =>
        simp only [newCells] at ho
        split at ho
        · simp at ho
        · rename_i hfw
          rw [Bool.not_eq_true] at hfw
          rw [hpres s₁ h₁ hfw o ho, hpres s₂ h₂ hfw o ho]
          exact hag.2.1 o ho
  · cases i with
    | cmp a o =>
      simp only [stepA, Bool.and_eq_true, List.contains_iff_mem] at hf
      have ha : s₁.view.get a = s₂.view.get a := by simp [AState.view, hag.1 _ hf.1]
      simp only [evalInstrA, evalInstr, JState.writeB5]
      rw [ha, opPub_eval hf.2 hag]
    | cmpMem a b o =>
      simp only [stepA, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hf
      obtain ⟨⟨ha, rfl⟩, ho⟩ := hf
      have ha' : s₁.view.get a = s₂.view.get a := by simp [AState.view, hag.1 _ ha]
      have hc := hag.2.1 o ho
      simp only [cellAt] at hc
      have hm : s₁.view.load "%rsp" o = s₂.view.load "%rsp" o := by
        simp [AState.view, JState.load, hc]
      simp only [evalInstrA, evalInstr, JState.writeB5]
      rw [ha', hm]
    | _ => simp [stepA] at hf

/-! ## 4. The checker -/

/-- The index register of the memory access of `i`, if any, is public. -/
def idxOk (P : PubA) (i : JInstr 64) : Bool :=
  match idxReg i with
  | some x => P.regs.contains x
  | none => true

/-- The base register of the memory access of `i`, if any, is public. -/
def baseOk (P : PubA) (i : JInstr 64) : Bool :=
  match memBase i with
  | some b => P.regs.contains b
  | none => true

/-- `i` is quiet under `r` and accesses memory through public base and index registers. -/
def opOk (r : DoitRegime) (P : PubA) (i : JInstr 64) : Bool :=
  !r.leaksOperands i.mnem && idxOk P i && baseOk P i

theorem opLeak_eq {r : DoitRegime} {P : PubA} {i : JInstr 64} (h : opOk r P i = true)
    {s₁ s₂ : AState} (hag : P.Agree s₁ s₂) : opLeak r s₁ i = opLeak r s₂ i := by
  simp only [opOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hq, hi⟩, hb⟩ := h
  simp only [opLeak, hq]
  have hr : ∀ x ∈ P.regs, s₁.regs x = s₂.regs x := hag.1
  cases i <;>
    simp_all [instrLeak, resolveEv, idxOk, baseOk, idxReg, memBase, AState.view]

/-- The public set the certificate assigns to index `pc`. -/
def certAt (A : List (Option PubA)) (pc : Nat) : Option PubA := A.getD pc none

/-- The certificate assigns index `s` a public set below `out`. -/
def succOk (A : List (Option PubA)) (s : Nat) (out : PubA) : Bool :=
  match certAt A s with
  | some b => b.le out
  | none => false

theorem succOk_spec {A : List (Option PubA)} {s : Nat} {out : PubA}
    (h : succOk A s out = true) : ∃ b, certAt A s = some b ∧ b.le out = true := by
  unfold succOk at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · simp at h

/-- The public set after a straight-line block. -/
def stepBlock (a : PubA) (ops : List (JInstr 64)) : PubA := ops.foldl stepA a

/-- Every instruction of a straight-line block passes `opOk` from the public set before
    it, whose frame words are in `F` when the instruction writes through a base other
    than `%rsp`. -/
def blockOkA (r : DoitRegime) (F : List Int) : PubA → List (JInstr 64) → Bool
  | _, [] => true
  | a, i :: is =>
      (!sepWrite i || a.cells.all F.contains) && opOk r a i && blockOkA r F (stepA a i) is

/-- **Soundness of the block check.** Two states agreeing on `a`, whose steps through
    the block satisfy `FrameSep F`, have equal block leakage and end agreeing on
    `stepBlock a ops`. -/
theorem blockOkA_sound {r : DoitRegime} {F : List Int} :
    ∀ (ops : List (JInstr 64)) (a : PubA) {s₁ s₂ : AState}, blockOkA r F a ops = true →
      a.Agree s₁ s₂ → BlockOk (FrameSep F) s₁ ops → BlockOk (FrameSep F) s₂ ops →
      blockLeakA r s₁ ops = blockLeakA r s₂ ops ∧
        (stepBlock a ops).Agree (runBlockA s₁ ops) (runBlockA s₂ ops)
  | [], _, _, _, _, hag, _, _ => ⟨rfl, hag⟩
  | i :: is, a, s₁, s₂, h, hag, ⟨h₁, hs₁⟩, ⟨h₂, hs₂⟩ => by
    simp only [blockOkA, Bool.and_eq_true] at h
    obtain ⟨⟨hF, hop⟩, hrest⟩ := h
    have hF : sepWrite i = true → ∀ o ∈ a.cells, o ∈ F := fun hsw o ho => by
      simp only [hsw, Bool.not_true, Bool.false_or] at hF
      simpa using List.all_eq_true.mp hF o ho
    obtain ⟨hl, hA⟩ := blockOkA_sound is (stepA a i) hrest (stepA_sound a i hF hag h₁ h₂) hs₁ hs₂
    refine ⟨?_, hA⟩
    simp only [blockLeakA, opLeak_eq hop hag, hl]

/-- The check at index `pc`, under the owner map `own` (the entry index of the function
    each index belongs to) and the exit sets `X` (the public set at every `ret` of the
    function with entry `e` is above `X e`). A non-call successor has the owner of `pc`;
    a `ret` is above the exit set of its owner; a `call t` runs `callOps`, enters `t`
    below the set after them, and continues after `retOps` from the exit set of `t`'s
    owner. -/
def checkAt (r : DoitRegime) (F : List Int) (own : Nat → Nat) (X : Nat → PubA)
    (prog : List RInstr) (A : List (Option PubA)) (pc : Nat) : Bool :=
  match certAt A pc with
  | none => true
  | some a => a.cells.all F.contains &&
    match prog[pc]? with
    | some (.op i) => opOk r a i && succOk A (pc + 1) (stepA a i) && own (pc + 1) == own pc
    | some (.jcc cc t) =>
        a.flags && (condtOfNibble cc).isSome && succOk A t a && succOk A (pc + 1) a
          && own t == own pc && own (pc + 1) == own pc
    | some (.push x) =>
        blockOkA r F a (pushOps x) && succOk A (pc + 1) (stepBlock a (pushOps x))
          && own (pc + 1) == own pc
    | some (.pop x) =>
        blockOkA r F a (popOps x) && succOk A (pc + 1) (stepBlock a (popOps x))
          && own (pc + 1) == own pc
    | some .ret => (X (own pc)).le a
    | some (.call t) =>
        blockOkA r F a (callOps (pc + 1)) && succOk A t (stepBlock a (callOps (pc + 1)))
          && blockOkA r F (X (own t)) retOps
          && succOk A (pc + 1) (stepBlock (X (own t)) retOps) && own (pc + 1) == own pc
    | none => true

/-- The check at every index of `prog`. -/
def checkCert (r : DoitRegime) (F : List Int) (own : Nat → Nat) (X : Nat → PubA)
    (prog : List RInstr) (A : List (Option PubA)) : Bool :=
  (List.range prog.length).all (checkAt r F own X prog A)

theorem checkAt_of_checkCert {r : DoitRegime} {F : List Int} {own : Nat → Nat}
    {X : Nat → PubA} {prog : List RInstr}
    {A : List (Option PubA)} (hc : checkCert r F own X prog A = true) {pc : Nat} {x : RInstr}
    (hx : prog[pc]? = some x) : checkAt r F own X prog A pc = true := by
  have hlt : pc < prog.length := (List.getElem?_eq_some_iff.mp hx).1
  exact List.all_eq_true.mp hc pc (List.mem_range.mpr hlt)

theorem condB_eq {s₁ s₂ : AState} (h : s₁.flags = s₂.flags) (c : Condt) :
    s₁.view.condB c = s₂.view.condB c := by
  unfold JState.condB JState.flagB
  simp [AState.view, h]

/-- **Soundness of a certificate.** If `checkCert r F own X prog A` holds, two runs of
    `prog` from index `pc`, whose steps satisfy `FrameSep F`, from states agreeing on the
    set the certificate assigns to `pc`, have equal traces and end in states agreeing on
    the exit set `X (own pc)` of the function containing `pc`. -/
theorem checkCert_sound {r : DoitRegime} {F : List Int} {own : Nat → Nat} {X : Nat → PubA}
    {prog : List RInstr}
    {A : List (Option PubA)} (hc : checkCert r F own X prog A = true) {pc : Nat} {s₁ : AState}
    {t₁ : List CTLeak} {s₁' : AState} (h₁ : RunL r (FrameSep F) prog pc s₁ t₁ s₁') :
    ∀ {a : PubA} {s₂ : AState} {t₂ : List CTLeak} {s₂' : AState}, certAt A pc = some a →
      a.Agree s₁ s₂ → RunL r (FrameSep F) prog pc s₂ t₂ s₂' →
        t₁ = t₂ ∧ (X (own pc)).Agree s₁' s₂' := by
  induction h₁ with
  | @ret pc s₁ h =>
    intro a s₂ t₂ s₂' hA hag h₂
    cases h₂ with
    | ret =>
      have hck := checkAt_of_checkCert hc h
      simp only [checkAt, hA, h, Bool.and_eq_true] at hck
      exact ⟨rfl, PubA.agree_of_le hck.2 hag⟩
    | op h' => simp_all
    | jcc h' => simp_all
    | stack h' hops' => simp_all [RInstr.stackOps?]
    | call h' => simp_all
  | @op pc s₁ i t₁ s₁' h hok hr ih =>
    intro a s₂ t₂ s₂' hA hag h₂
    have hck := checkAt_of_checkCert hc h
    simp only [checkAt, hA, h, Bool.and_eq_true, beq_iff_eq] at hck
    obtain ⟨hF, ⟨hop, hsucc⟩, hown⟩ := hck
    have hF : ∀ o ∈ a.cells, o ∈ F := fun o ho => by
      simpa using List.all_eq_true.mp hF o ho
    obtain ⟨b, hb, hle⟩ := succOk_spec hsucc
    cases h₂ with
    | ret h' => simp_all
    | jcc h' => simp_all
    | stack h' hops' => simp_all [RInstr.stackOps?]
    | call h' => simp_all
    | @op _ _ i' t₂ _ h' hok' hr' =>
      rw [h, Option.some.injEq, RInstr.op.injEq] at h'
      subst h'
      obtain ⟨ht, hs⟩ := ih hb (PubA.agree_of_le hle (stepA_sound a i (fun _ => hF) hag hok hok')) hr'
      rw [hown] at hs
      exact ⟨by rw [opLeak_eq hop hag, ht], hs⟩
  | @jcc pc s₁ cc tgt c t₁ s₁' h hcc hr ih =>
    intro a s₂ t₂ s₂' hA hag h₂
    have hck := checkAt_of_checkCert hc h
    simp only [checkAt, hA, h, Bool.and_eq_true, beq_iff_eq] at hck
    obtain ⟨_, ⟨⟨⟨⟨⟨hfl, _⟩, hst⟩, hsn⟩, hot⟩, hon⟩⟩ := hck
    cases h₂ with
    | ret h' => simp_all
    | op h' => simp_all
    | stack h' hops' => simp_all [RInstr.stackOps?]
    | call h' => simp_all
    | @jcc _ _ cc' tgt' c' t₂ _ h' hcc' hr' =>
      rw [h, Option.some.injEq, RInstr.jcc.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [hcc, Option.some.injEq] at hcc'
      subst hcc'
      have hcb := condB_eq (hag.2.2 hfl) c
      by_cases hcnd : s₂.view.condB c = true
      · obtain ⟨b, hb, hle⟩ := succOk_spec hst
        simp only [hcb, hcnd, if_true] at ih hr'
        obtain ⟨ht, hs⟩ := ih hb (PubA.agree_of_le hle hag) hr'
        rw [hot] at hs
        exact ⟨by rw [hcb, ht], hs⟩
      · obtain ⟨b, hb, hle⟩ := succOk_spec hsn
        simp only [hcb, hcnd, if_false, Bool.false_eq_true] at ih hr'
        obtain ⟨ht, hs⟩ := ih hb (PubA.agree_of_le hle hag) hr'
        rw [hon] at hs
        exact ⟨by rw [hcb, ht], hs⟩
  | @stack pc s₁ ri ops t₁ s₁' h hops hok hr ih =>
    intro a s₂ t₂ s₂' hA hag h₂
    have hck := checkAt_of_checkCert hc h
    have key : (blockOkA r F a ops = true ∧ succOk A (pc + 1) (stepBlock a ops) = true)
        ∧ own (pc + 1) = own pc := by
      cases ri <;> simp only [RInstr.stackOps?, reduceCtorEq, Option.some.injEq] at hops <;>
        subst hops <;> simp only [checkAt, hA, h, Bool.and_eq_true, beq_iff_eq] at hck <;>
        exact hck.2
    obtain ⟨⟨hbk, hsucc⟩, hown⟩ := key
    obtain ⟨b, hb, hle⟩ := succOk_spec hsucc
    cases h₂ with
    | ret h' =>
      rw [h, Option.some.injEq] at h'; subst h'; simp [RInstr.stackOps?] at hops
    | op h' =>
      rw [h, Option.some.injEq] at h'; subst h'; simp [RInstr.stackOps?] at hops
    | jcc h' =>
      rw [h, Option.some.injEq] at h'; subst h'; simp [RInstr.stackOps?] at hops
    | call h' =>
      rw [h, Option.some.injEq] at h'; subst h'; simp [RInstr.stackOps?] at hops
    | @stack _ _ ri' ops' t₂ _ h' hops' hok' hr' =>
      rw [h, Option.some.injEq] at h'
      subst h'
      rw [hops, Option.some.injEq] at hops'
      subst hops'
      obtain ⟨hl, hag'⟩ := blockOkA_sound ops a hbk hag hok hok'
      obtain ⟨ht, hs⟩ := ih hb (PubA.agree_of_le hle hag') hr'
      rw [hown] at hs
      exact ⟨by rw [hl, ht], hs⟩
  | @call pc tgt s₁ sc₁ tc₁ tr₁ s₁' h hok hcal hokr hret ihc ihr =>
    intro a s₂ t₂ s₂' hA hag h₂
    have hck := checkAt_of_checkCert hc h
    simp only [checkAt, hA, h, Bool.and_eq_true, beq_iff_eq] at hck
    obtain ⟨_, ⟨⟨⟨⟨hbk, hsc⟩, hbr⟩, hsr⟩, hown⟩⟩ := hck
    cases h₂ with
    | ret h' => simp_all
    | op h' => simp_all
    | jcc h' => simp_all
    | stack h' hops' => simp_all [RInstr.stackOps?]
    | @call _ tgt' _ sc₂ tc₂ tr₂ _ h' hok' hcal' hokr' hret' =>
      rw [h, Option.some.injEq, RInstr.call.injEq] at h'
      subst h'
      obtain ⟨hl1, hag1⟩ := blockOkA_sound _ a hbk hag hok hok'
      obtain ⟨b, hb, hle⟩ := succOk_spec hsc
      obtain ⟨htc, hX⟩ := ihc hb (PubA.agree_of_le hle hag1) hcal'
      obtain ⟨hl2, hag2⟩ := blockOkA_sound _ _ hbr hX hokr hokr'
      obtain ⟨b', hb', hle'⟩ := succOk_spec hsr
      obtain ⟨htr, hs⟩ := ihr hb' (PubA.agree_of_le hle' hag2) hret'
      rw [hown] at hs
      exact ⟨by rw [hl1, htc, hl2, htr], hs⟩

/-! ## 5. Inference and the decision -/

/-- The meet of two public sets: the locations public in both. -/
def meetA (a b : PubA) : PubA :=
  ⟨a.regs.filter b.regs.contains, a.cells.filter b.cells.contains, a.flags && b.flags⟩

/-- The meet with an unreached index (`none`) is the other set. -/
def meetO : Option PubA → PubA → Option PubA
  | none, b => some b
  | some a, b => some (meetA a b)

/-- The targets of the calls of `prog`: the entries of its callees. -/
def callTargets (prog : List RInstr) : List Nat :=
  prog.filterMap fun x => match x with
    | .call t => some t
    | _ => none

/-- The owner of index `pc` among the function entries `entries`: the greatest entry at
    or below `pc`, else `0`. The functions of a linked program lie contiguously from
    their entries; `checkAt` checks that every non-call edge keeps its owner. -/
def ownerOf (entries : List Nat) (pc : Nat) : Nat :=
  entries.foldl (fun m t => if t ≤ pc ∧ m < t then t else m) 0

/-- The meet of the public sets `A` assigns to the reached `ret`s owned by entry `e`,
    `none` when there is none. -/
def exitSet? (prog : List RInstr) (own : Nat → Nat) (A : List (Option PubA)) (e : Nat) :
    Option PubA :=
  (List.range prog.length).foldl (fun acc pc =>
    match prog[pc]?, certAt A pc with
    | some RInstr.ret, some a => if own pc = e then meetO acc a else acc
    | _, _ => acc) none

/-- The exit set of the function with entry `e`: `exitSet?`, nothing public when it has
    no reached `ret`. -/
def exitSet (prog : List RInstr) (own : Nat → Nat) (A : List (Option PubA)) (e : Nat) :
    PubA :=
  (exitSet? prog own A e).getD ⟨[], [], false⟩

/-- The successors of index `pc` with the public set each receives from `a`, under the
    owner map `own` and the partial exit sets `X?`. A call's return edge is added once
    its callee has a reached `ret`. -/
def succs (own : Nat → Nat) (X? : Nat → Option PubA) (prog : List RInstr) (pc : Nat)
    (a : PubA) : List (Nat × PubA) :=
  match prog[pc]? with
  | some (.op i) => [(pc + 1, stepA a i)]
  | some (.jcc _ t) => [(t, a), (pc + 1, a)]
  | some (.push x) => [(pc + 1, stepBlock a (pushOps x))]
  | some (.pop x) => [(pc + 1, stepBlock a (popOps x))]
  | some (.call t) =>
      (t, stepBlock a (callOps (pc + 1))) ::
        match X? (own t) with
        | some x => [(pc + 1, stepBlock x retOps)]
        | none => []
  | _ => []

/-- `a` with its frame words restricted to those `keep` accepts. -/
def restrictCells (keep : Int → Bool) (a : PubA) : PubA := { a with cells := a.cells.filter keep }

/-- One forward pass over the indices of `prog`, meeting each successor's set with what
    it receives, its frame words restricted to `keep`. -/
def sweep (keep : Int → Bool) (prog : List RInstr) (A : List (Option PubA)) :
    List (Option PubA) :=
  let own := ownerOf (callTargets prog)
  let X? := exitSet? prog own A
  (List.range prog.length).foldl (fun A pc =>
    match certAt A pc with
    | none => A
    | some a =>
        (succs own X? prog pc a).foldl (fun A so =>
          A.set so.1 (meetO (certAt A so.1) (restrictCells keep so.2))) A)
    A

/-- Passes until a pass changes nothing, at most `fuel` of them. -/
def sweepFix (keep : Int → Bool) (prog : List RInstr) :
    Nat → List (Option PubA) → List (Option PubA)
  | 0, A => A
  | fuel + 1, A =>
    let A' := sweep keep prog A; if A' = A then A else sweepFix keep prog fuel A'

/-- The certificate the forward analysis computes from the entry set `P`, keeping the
    frame words `keep` accepts. -/
def inferIn (keep : Int → Bool) (prog : List RInstr) (P : PubA) : List (Option PubA) :=
  sweepFix keep prog prog.length ((List.replicate prog.length none).set 0 (some P))

/-- The certificate the forward analysis computes from the entry set `P`. -/
def infer (prog : List RInstr) (P : PubA) : List (Option PubA) :=
  inferIn (fun _ => true) prog P

/-- **The decision.** The certificate inferred within the frame words `F` assigns the
    entry a set below `P` and passes `checkCert` under the owners of the call targets
    and the exit sets of the certificate. -/
def bytesCTCheck (r : DoitRegime) (F : List Int) (P : PubA) (prog : List RInstr) : Bool :=
  let A := inferIn F.contains prog P
  let own := ownerOf (callTargets prog)
  succOk A 0 P && checkCert r F own (exitSet prog own A) prog A

/-- **Soundness of the decision.** If `bytesCTCheck r F P prog` holds, two runs of `prog`
    from index `0` whose steps satisfy `FrameSep F`, from states agreeing on `P`, have
    equal leakage traces. -/
theorem bytesCTCheck_sound {r : DoitRegime} {F : List Int} {P : PubA} {prog : List RInstr}
    (h : bytesCTCheck r F P prog = true) :
    ConstantTimeRel P.Agree (fun sa t => ∃ sa', RunL r (FrameSep F) prog 0 sa t sa') := by
  intro s₁ s₂ t₁ t₂ hag ⟨_, h₁⟩ ⟨_, h₂⟩
  simp only [bytesCTCheck, Bool.and_eq_true] at h
  obtain ⟨b, hb, hle⟩ := succOk_spec h.1
  exact (checkCert_sound h.2 h₁ hb (PubA.agree_of_le hle hag) h₂).1

/-! ## 6. Frame words from the certificate, the public set from the ABI -/

/-- The frame words public at some index of the certificate. -/
def certCells (A : List (Option PubA)) : List Int :=
  A.flatMap fun o => match o with
    | some a => a.cells
    | none => []

/-- `bytesCTCheck` with the frame words of the inferred certificate. -/
def bytesCTCheckAuto (r : DoitRegime) (P : PubA) (prog : List RInstr) : Bool :=
  bytesCTCheck r (certCells (infer prog P)) P prog

/-- **Soundness of the decision with inferred frame words.** If `bytesCTCheckAuto r P
    prog` holds, two runs of `prog` from index `0` from states agreeing on `P`, whose
    steps satisfy `FrameSep` for the frame words of the inferred certificate, have equal
    leakage traces. -/
theorem bytesCTCheckAuto_sound {r : DoitRegime} {P : PubA} {prog : List RInstr}
    (h : bytesCTCheckAuto r P prog = true) :
    ConstantTimeRel P.Agree
      (fun sa t => ∃ sa', RunL r (FrameSep (certCells (infer prog P))) prog 0 sa t sa') :=
  bytesCTCheck_sound h

open CatCrypt.Crypto.Jasmin.LowCT (LevelTable SecretLevel)

/-- The kind of a parameter: a pointer, whose value is an address, or a scalar. -/
inductive ParamKind where
  | ptr
  | scalar
  deriving DecidableEq, Repr

/-- The System V registers of the first six integer parameters, in order. -/
def sysvRegs : List String := ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"]

/-- A parameter is public on entry when it is a pointer or its level in `lt` is
    `Public`. -/
def paramPub (lt : LevelTable) (p : String × ParamKind) : Bool :=
  p.2 == .ptr || lt p.1 == .Public

/-- The public entry set of a function with parameters `ps` under the level table `lt`:
    `%rsp`, the register of each public parameter among the first six, the stack word of
    each public parameter from the seventh on, and no flag. -/
def abiPubA (ps : List (String × ParamKind)) (lt : LevelTable) : PubA where
  regs := "%rsp" :: ((ps.zip sysvRegs).filter (fun q => paramPub lt q.1)).map (·.2)
  cells := (((ps.drop 6).zipIdx).filter (fun q => paramPub lt q.1)).map
    (fun q => 8 * ((q.2 : Int) + 1))
  flags := false

/-- The level table of a kernel without a hax secrecy record: every name secret, so
    that under `abiPubA` exactly the pointer parameters and `%rsp` are public. -/
def defaultLevels : LevelTable := fun _ => .Secret

/-- The registers of `abiPubA`: `%rsp` and the register of each public parameter among
    the first six. -/
theorem abiPubA_regs_iff (ps : List (String × ParamKind)) (lt : LevelTable) (x : String) :
    x ∈ (abiPubA ps lt).regs ↔
      x = "%rsp" ∨ ∃ (i : Nat) (p : String × ParamKind), ps[i]? = some p ∧
        sysvRegs[i]? = some x ∧ paramPub lt p = true := by
  simp only [abiPubA, List.mem_cons, List.mem_map, List.mem_filter]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨⟨p, y⟩, ⟨hz, hp⟩, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
    rw [List.getElem?_zip_eq_some] at hi
    exact ⟨i, p, hi.1, hi.2, hp⟩
  · rintro ⟨i, p, hp, hx, hpub⟩
    exact ⟨(p, x), ⟨List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr ⟨hp, hx⟩⟩,
      hpub⟩, rfl⟩

/-- The frame words of `abiPubA`: the stack word `8 (k + 1)` of each public parameter at
    position `6 + k`. -/
theorem abiPubA_cells_iff (ps : List (String × ParamKind)) (lt : LevelTable) (o : Int) :
    o ∈ (abiPubA ps lt).cells ↔
      ∃ (k : Nat) (p : String × ParamKind), ps[6 + k]? = some p ∧ o = 8 * ((k : Int) + 1) ∧
        paramPub lt p = true := by
  simp only [abiPubA, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨p, k⟩, ⟨hk, hp⟩, rfl⟩
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_drop] at hk
    exact ⟨k, p, hk, rfl, hp⟩
  · rintro ⟨k, p, hk, rfl, hp⟩
    refine ⟨(p, k), ⟨?_, hp⟩, rfl⟩
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_drop]
    exact hk

/-- The reason the check fails at index `pc` of `prog` under the certificate `A` and
    the frame words `F`, or `none` when it passes there. -/
def failAt (r : DoitRegime) (F : List Int) (own : Nat → Nat) (X : Nat → PubA)
    (prog : List RInstr) (A : List (Option PubA)) (pc : Nat) : Option String :=
  match certAt A pc with
  | none => none
  | some a =>
    if !(a.cells.all F.contains) then some "frame word outside the frame set" else
    match prog[pc]? with
    | some (.op i) =>
      if r.leaksOperands i.mnem then some "variable-time instruction"
      else if !idxOk a i then some "secret index register"
      else if !baseOk a i then some "secret base register"
      else if !succOk A (pc + 1) (stepA a i) then some "no post-fixpoint at the successor"
      else if own (pc + 1) != own pc then some "falls through into another function"
      else none
    | some (.jcc cc t) =>
      if !a.flags then some "branch on secret flags"
      else if !(condtOfNibble cc).isSome then some "unknown condition nibble"
      else if !(succOk A t a && succOk A (pc + 1) a) then some "no post-fixpoint at a successor"
      else if own t != own pc || own (pc + 1) != own pc then
        some "branch into another function"
      else none
    | some (.push x) =>
      if !blockOkA r F a (pushOps x) then some "push: secret base or variable-time step"
      else if !succOk A (pc + 1) (stepBlock a (pushOps x)) then
        some "no post-fixpoint at the successor"
      else if own (pc + 1) != own pc then some "falls through into another function"
      else none
    | some (.pop x) =>
      if !blockOkA r F a (popOps x) then some "pop: secret base or variable-time step"
      else if !succOk A (pc + 1) (stepBlock a (popOps x)) then
        some "no post-fixpoint at the successor"
      else if own (pc + 1) != own pc then some "falls through into another function"
      else none
    | some .ret =>
      if !(X (own pc)).le a then some "ret: set not above the function's exit set" else none
    | some (.call t) =>
      if !a.regs.contains "%rsp" then some "call: secret stack pointer"
      else if !blockOkA r F a (callOps (pc + 1)) then some "call: the return-address push fails"
      else if !succOk A t (stepBlock a (callOps (pc + 1))) then
        some "call: no post-fixpoint at the callee entry"
      else if !(X (own t)).regs.contains "%rsp" then
        some "call: secret stack pointer in the callee's exit set"
      else if !blockOkA r F (X (own t)) retOps then some "call: the return fails"
      else if !succOk A (pc + 1) (stepBlock (X (own t)) retOps) then
        some "call: no post-fixpoint after the return"
      else if own (pc + 1) != own pc then some "falls through into another function"
      else none
    | none => none

/-- The first index at which `bytesCTCheckAuto r P prog` fails, with the reason; `none`
    when no index fails and the entry set is below `P`. -/
def firstFailure (r : DoitRegime) (P : PubA) (prog : List RInstr) : Option (Nat × String) :=
  let A := infer prog P
  let own := ownerOf (callTargets prog)
  if !succOk A 0 P then some (0, "entry set not below the public set") else
  (List.range prog.length).findSome? fun pc =>
    (failAt r (certCells A) own (exitSet prog own A) prog A pc).map (pc, ·)

/-! ## 7. Array forms of the inference and the check

The list forms above index the program and the certificate by position, which costs
time linear in the index, and `sweep` rebuilds the certificate list at each update.
The forms below keep both in arrays and update the certificate in place. `checkCertA`
is `checkCert` on the arrays' lists (`checkCertA_eq`), so `bytesCTCheckFast_sound`
follows from `checkCert_sound`; `inferA` needs no proof, since the check validates
whatever certificate it computes. -/

/-- The public set the array certificate assigns to index `pc`. -/
def certAtA (A : Array (Option PubA)) (pc : Nat) : Option PubA := A.getD pc none

theorem certAtA_eq (A : Array (Option PubA)) (pc : Nat) : certAtA A pc = certAt A.toList pc := by
  simp only [certAtA, certAt, Array.getD, List.getD, Array.getElem?_toList]
  split <;> simp_all

/-- `succOk` on an array certificate. -/
def succOkA (A : Array (Option PubA)) (s : Nat) (out : PubA) : Bool :=
  match certAtA A s with
  | some b => b.le out
  | none => false

theorem succOkA_eq (A : Array (Option PubA)) (s : Nat) (out : PubA) :
    succOkA A s out = succOk A.toList s out := by
  simp only [succOkA, succOk, certAtA_eq]

/-- `checkAt` on an array program and an array certificate. -/
def checkAtA (r : DoitRegime) (F : List Int) (own : Nat → Nat) (X : Nat → PubA)
    (prog : Array RInstr) (A : Array (Option PubA)) (pc : Nat) : Bool :=
  match certAtA A pc with
  | none => true
  | some a => a.cells.all F.contains &&
    match prog[pc]? with
    | some (.op i) => opOk r a i && succOkA A (pc + 1) (stepA a i) && own (pc + 1) == own pc
    | some (.jcc cc t) =>
        a.flags && (condtOfNibble cc).isSome && succOkA A t a && succOkA A (pc + 1) a
          && own t == own pc && own (pc + 1) == own pc
    | some (.push x) =>
        blockOkA r F a (pushOps x) && succOkA A (pc + 1) (stepBlock a (pushOps x))
          && own (pc + 1) == own pc
    | some (.pop x) =>
        blockOkA r F a (popOps x) && succOkA A (pc + 1) (stepBlock a (popOps x))
          && own (pc + 1) == own pc
    | some .ret => (X (own pc)).le a
    | some (.call t) =>
        blockOkA r F a (callOps (pc + 1)) && succOkA A t (stepBlock a (callOps (pc + 1)))
          && blockOkA r F (X (own t)) retOps
          && succOkA A (pc + 1) (stepBlock (X (own t)) retOps) && own (pc + 1) == own pc
    | none => true

theorem checkAtA_eq (r : DoitRegime) (F : List Int) (own : Nat → Nat) (X : Nat → PubA)
    (prog : Array RInstr) (A : Array (Option PubA)) (pc : Nat) :
    checkAtA r F own X prog A pc = checkAt r F own X prog.toList A.toList pc := by
  simp only [checkAtA, checkAt, certAtA_eq, succOkA_eq, Array.getElem?_toList]

/-- `checkCert` on an array program and an array certificate. -/
def checkCertA (r : DoitRegime) (F : List Int) (own : Nat → Nat) (X : Nat → PubA)
    (prog : Array RInstr) (A : Array (Option PubA)) : Bool :=
  (List.range prog.size).all (checkAtA r F own X prog A)

theorem checkCertA_eq (r : DoitRegime) (F : List Int) (own : Nat → Nat) (X : Nat → PubA)
    (prog : Array RInstr) (A : Array (Option PubA)) :
    checkCertA r F own X prog A = checkCert r F own X prog.toList A.toList := by
  simp only [checkCertA, checkCert, Array.length_toList]
  congr 1
  funext pc
  exact checkAtA_eq r F own X prog A pc

/-- Meet the set at index `s` with `out`, reporting whether it changed. -/
def meetIntoA (A : Array (Option PubA)) (s : Nat) (out : PubA) : Array (Option PubA) × Bool :=
  let old := certAtA A s
  let new := meetO old out
  if new = old then (A, false) else (A.setIfInBounds s new, true)

/-- `exitSet?` on an array program and an array certificate. -/
def exitSetA? (prog : Array RInstr) (own : Nat → Nat) (A : Array (Option PubA)) (e : Nat) :
    Option PubA :=
  (List.range prog.size).foldl (fun acc pc =>
    match prog[pc]?, certAtA A pc with
    | some RInstr.ret, some a => if own pc = e then meetO acc a else acc
    | _, _ => acc) none

/-- `exitSet` on an array program and an array certificate. -/
def exitSetA (prog : Array RInstr) (own : Nat → Nat) (A : Array (Option PubA)) (e : Nat) :
    PubA :=
  (exitSetA? prog own A e).getD ⟨[], [], false⟩

/-- The successors of index `pc` of an array program with the set each receives. -/
def succsA (own : Nat → Nat) (X? : Nat → Option PubA) (prog : Array RInstr) (pc : Nat)
    (a : PubA) : List (Nat × PubA) :=
  match prog[pc]? with
  | some (.op i) => [(pc + 1, stepA a i)]
  | some (.jcc _ t) => [(t, a), (pc + 1, a)]
  | some (.push x) => [(pc + 1, stepBlock a (pushOps x))]
  | some (.pop x) => [(pc + 1, stepBlock a (popOps x))]
  | some (.call t) =>
      (t, stepBlock a (callOps (pc + 1))) ::
        match X? (own t) with
        | some x => [(pc + 1, stepBlock x retOps)]
        | none => []
  | _ => []

/-- One forward pass over the indices, updating the certificate in place, with a flag
    recording whether any set changed. -/
def sweepA (prog : Array RInstr) (A : Array (Option PubA)) : Array (Option PubA) × Bool :=
  let own := ownerOf (callTargets prog.toList)
  let X? := exitSetA? prog own A
  (List.range prog.size).foldl (fun acc pc =>
    let (B, ch) := acc
    match certAtA B pc with
    | none => (B, ch)
    | some a => (succsA own X? prog pc a).foldl (fun acc so =>
        let (B, ch) := acc
        let (B', c) := meetIntoA B so.1 so.2
        (B', ch || c)) (B, ch))
    (A, false)

/-- Passes until one changes nothing, at most `fuel` of them. -/
def sweepFixA (prog : Array RInstr) : Nat → Array (Option PubA) → Array (Option PubA)
  | 0, A => A
  | fuel + 1, A =>
    let (B, ch) := sweepA prog A
    if ch then sweepFixA prog fuel B else B

/-- The certificate of the forward analysis from the entry set `P`, on arrays. -/
def inferA (prog : Array RInstr) (P : PubA) : Array (Option PubA) :=
  sweepFixA prog prog.size ((Array.replicate prog.size none).setIfInBounds 0 (some P))

/-- The frame words public at some index of an array certificate. -/
def certCellsA (A : Array (Option PubA)) : List Int := certCells A.toList

/-- **The decision on arrays.** The array certificate `inferA` assigns the entry a set
    below `P` and passes `checkCertA` with its own frame words. -/
def bytesCTCheckFast (r : DoitRegime) (P : PubA) (prog : List RInstr) : Bool :=
  let pa := prog.toArray
  let A := inferA pa P
  let own := ownerOf (callTargets prog)
  succOkA A 0 P && checkCertA r (certCellsA A) own (exitSetA pa own A) pa A

/-- **Soundness of the decision on arrays.** If `bytesCTCheckFast r P prog` holds, two
    runs of `prog` from index `0` from states agreeing on `P`, whose steps satisfy
    `FrameSep` for the frame words of the certificate `inferA`, have equal leakage
    traces. -/
theorem bytesCTCheckFast_sound {r : DoitRegime} {P : PubA} {prog : List RInstr}
    (h : bytesCTCheckFast r P prog = true) :
    ConstantTimeRel P.Agree (fun sa t => ∃ sa',
      RunL r (FrameSep (certCellsA (inferA prog.toArray P))) prog 0 sa t sa') := by
  intro s₁ s₂ t₁ t₂ hag ⟨_, h₁⟩ ⟨_, h₂⟩
  simp only [bytesCTCheckFast, Bool.and_eq_true, succOkA_eq, checkCertA_eq] at h
  obtain ⟨b, hb, hle⟩ := succOk_spec h.1
  exact (checkCert_sound h.2 h₁ hb (PubA.agree_of_le hle hag) h₂).1

/-- `failAt` on an array program and an array certificate. -/
def failAtA (r : DoitRegime) (F : List Int) (own : Nat → Nat) (X : Nat → PubA)
    (prog : Array RInstr) (A : Array (Option PubA)) (pc : Nat) : Option String :=
  failAt r F own X prog.toList A.toList pc

/-- The first failing index of `bytesCTCheckFast` with the reason, on the certificate
    `A` computed by `inferA` for the array program `pa`, under the owners and exit sets
    `bytesCTCheckFast` uses. -/
def firstFailureA (r : DoitRegime) (P : PubA) (pa : Array RInstr) (A : Array (Option PubA)) :
    Option (Nat × String) :=
  let prog := pa.toList
  let AL := A.toList
  let own := ownerOf (callTargets prog)
  let X := exitSetA pa own A
  if !succOkA A 0 P then some (0, "entry set not below the public set") else
  (List.range pa.size).findSome? fun pc =>
    (failAt r (certCellsA A) own X prog AL pc).map (pc, ·)

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
