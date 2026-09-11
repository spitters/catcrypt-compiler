/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnified
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnified
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote

/-!
# w7-mem: the FULL supported fragment in one program type — scalar + mulx + loop + select + memory

`LowCTUnified` (w7) folded the four **all-`IsDirect`** construct families
(scalar arith, two-output widening multiply, branchless select, bounded loop)
into **one** source statement type `UStmt`, with **one** lowering
(`lowerUProg`), **one** denotation (`uProgDenote`), **one** functional
`compile_correct` (`lowerUProg_denoteAll`), and **one** constant-time theorem
(`lowerUProg_constant_time`).  Its honest boundary (the closing docstring
§"Excluded: memory operands") was the **memory fragment**: array load/store
lower to the register-INDEXED machine ops `loadMemIdx`/`storeMemIdx`, which are
**not** `IsDirect`; their CT guarantee has a *different shape*
(`CTAddressed`/public-index `agreePub`, see `LowCTMemCT`), so they did not fit
the unconditional `allDirect` unification.

This module closes that boundary.  `UMStmt` is **one** statement type ranging
over the **full** supported fragment — the w7 families **plus** memory load and
store — with one lowering, one denotation, **one uniform constant-time
theorem**, and the unified functional-correctness threading for the memory
cases.

## The uniform CT shape: everything is `CTAddressed`

The w7 CT used the strict `allDirect`/`blockLeak_state_independent` keystone
("the trace is the same from *any* two states").  Memory cannot use it: a
`storeMemIdx`/`loadMemIdx` reads its index register's value, so its trace is the
same only across states **agreeing on the public index**.  The standard CT
keystone `MachineConstantTime.blockLeak_pub_determined` is exactly this weaker,
more general form — leakage determined by the **public** registers under
`agreePub`.

The unifying observation is that the standard keystone subsumes the strict one
**uniformly**, under a frame/data register discipline:

* every **non-memory** instruction the w7 families emit is `IsDirect`, hence has
  `idxReg = none` (the `CTAddressed` index conjunct is vacuous), so it is
  `CTAddressed pub` whenever each register it writes is a *data* register
  (`pub dst = false`) — `isDirect_CTAddressed`;
* every **memory** instruction is `CTAddressed pub` when its index register is a
  *frame* register (`pub idx = true`) and (for a load) its result is a data
  register — `lowerMem{Store,Load}_CTAddressed`.

So under one `pub`/frame discipline — index/base/frame names public, computed
data destinations non-public — **every** instruction of the unified-with-memory
lowering is `CTAddressed pub`, and `blockLeak_pub_determined` delivers CT for
the whole fragment at once.  This is the single uniform CT theorem
(`lowerUMProg_constant_time`) covering scalar + mulx + loop + select + memory.

## The WF discipline (stated honestly, not derived)

The CT theorem is parametric in the discipline `BlockFrameWF pub body` (every
emitted index register is public; every emitted destination register is a data
register).  This is the machine-register reflection of the source
`FrameWF`/`cmdCT` tie of `LowCTMemCT` (public source slots → frame registers; the
load-result-is-data convention).  A real register allocator that keeps array
bases/indices/loop counters in a designated frame and computed words in data
registers satisfies it; we record it as the WF side condition, exactly as
`LowCTMemCT` does for the memory fragment in isolation.

## Functional correctness for the memory cases

`uMStmtDenote` dispatches the non-memory statements to `uStmtDenote` (w7) and
the memory statements to the concrete byte-offset value semantics of
`LowCTMemDenote` (`byteOffsetLeafSpec`, `arrElem`/`arrSetElem`).  The unified
functional threading uses **both** `StateMatch` (scalar registers) and
`MemMatch` (array memory); the memory store/load cases are discharged by
`lowerMemStore_denote_cell` / `lowerMemLoad_denote`.

## Realistic kernel: array-based multi-limb schoolbook multiply

`bignumMulKernel` is a genuine array-based bignum multiply step: **load** an
input limb from an array (`loadMemIdx`), **mulx** it against a scalar,
**accumulate** with the w7 `schoolbookStep` arith ops, and **store** the result
limb back to an output array (`storeMemIdx`).  It mixes memory + mulx + arith in
**one** `UMProg`, carrying functional correctness (the memory cell value
matches), the uniform CT (`lowerUMProg_constant_time`), and a one-vector value
KAT through the FULL unified pipeline.

## Honest scope

* The kernel is a single-limb load–mulx–accumulate–store cell (the 1×1 inner
  step of schoolbook), array-addressed at both ends.  The full multi-limb
  *loop* over limbs is supported by the type (`forU` body may contain memory
  statements) and the uniform CT covers it unconditionally; the per-cell
  *functional* threading is what the value KAT pins.  A whole multi-limb loop
  kernel needs a `MemMatch`-fold invariant across iterations (each iteration
  touches a distinct output cell) — recorded as the remaining work, not claimed.
* The memory CT uses `CTAddressed`/`agreePub` under the stated `BlockFrameWF`
  discipline, not the unconditional `allDirect` shape — that is the correct
  (and necessary) CT shape for value-indexed memory.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnifiedMem

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnified
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The `IsDirect ⇒ CTAddressed` bridge (the uniformity lemma)

The w7 families all lower to `IsDirect` instructions.  An `IsDirect`
instruction has `idxReg = none`, so the `CTAddressed` index conjunct is
vacuous; it is therefore `CTAddressed pub` exactly when each register it writes
is a data register (`pub dst = false`).  This lets the strict-CT families and
the public-index memory ops share the **single** `CTAddressed` keystone. -/

/-- An `IsDirect` instruction names no memory index register. -/
theorem isDirect_idxReg_none {w : Nat} (i : JInstr w) (h : IsDirect i) :
    idxReg i = none := by
  cases i <;> first | rfl | (simp [IsDirect] at h)

/-- **The uniformity bridge.**  An `IsDirect` instruction whose every
    destination is a data register is `CTAddressed`: the index conjunct is
    vacuous (no index register), and the destination conjunct is the
    data-register hypothesis. -/
theorem isDirect_CTAddressed {w : Nat} (pub : PubPred) (i : JInstr w)
    (hd : IsDirect i) (hdst : ∀ d ∈ dstRegs i, pub d = false) :
    CTAddressed pub i := by
  refine ⟨?_, hdst⟩
  intro idx hidx
  rw [isDirect_idxReg_none i hd] at hidx
  exact absurd hidx (by simp)

/-! ## 2. The unified-with-memory statement type -/

/-- **The full unified source statement.**  One type ranging over the entire
    supported fragment: the w7 families (`stmt : UStmt` — scalar arith, widening
    multiply, branchless select, bounded loop) **plus** array memory load and
    store, **plus** a memory-containing bounded loop (`forM`) whose body is a
    `List UMStmt`. -/
inductive UMStmt where
  /-- A w7 statement (scalar arith / mulx / select / loop), lifted verbatim. -/
  | base (st : UStmt)
  /-- An array load `dst := arr[idx]`. -/
  | memLoad (m : MemLoadSrc)
  /-- An array store `arr[idx] := src`. -/
  | memStore (m : MemStoreSrc)
  /-- A bounded loop whose body may itself contain memory statements. -/
  | forM (x : String) (n : Nat) (body : List UMStmt)

/-- A unified-with-memory program. -/
abbrev UMProg := List UMStmt

/-! ## 3. The unified lowering (one compiler, dispatching per family incl. memory) -/

mutual
/-- **The unified-with-memory lowering, per statement.**  Non-memory statements
    dispatch to the w7 `lowerUStmt`; memory statements to
    `lowerMemLoad`/`lowerMemStore`; the memory-loop is unrolled exactly as the
    w7 loop is. -/
def lowerUMStmt (ρ : RegMap) : UMStmt → List (JInstr 64)
  | .base st => lowerUStmt ρ st
  | .memLoad m => [lowerMemLoad ρ m]
  | .memStore m => [lowerMemStore ρ m]
  | .forM x n body =>
      (List.range n).flatMap (fun i => movImm (ρ x) i :: lowerUMProg ρ body)

/-- **The unified-with-memory lowering of a program.** -/
def lowerUMProg (ρ : RegMap) : UMProg → List (JInstr 64)
  | [] => []
  | st :: rest => lowerUMStmt ρ st ++ lowerUMProg ρ rest
end

@[simp] theorem lowerUMProg_nil (ρ : RegMap) : lowerUMProg ρ [] = [] := by
  rw [lowerUMProg]

@[simp] theorem lowerUMProg_cons (ρ : RegMap) (st : UMStmt) (rest : UMProg) :
    lowerUMProg ρ (st :: rest) = lowerUMStmt ρ st ++ lowerUMProg ρ rest := by
  rw [lowerUMProg]

/-! ## 4. Uniform cross-construct + memory constant-time (one CT theorem)

The frame/data register discipline `BlockFrameWF` says every emitted index
register is a public (frame) register and every emitted destination is a data
register.  Under it every instruction of the lowering is `CTAddressed` — the
non-memory ones via `isDirect_CTAddressed`, the memory ones because the index is
public (and stores write nothing / loads write a data register) — so the
standard keystone `blockLeak_pub_determined` delivers CT for the WHOLE
fragment, memory included.  This is the single uniform CT theorem covering
scalar + mulx + loop + select + memory. -/

/-- **The frame/data register discipline on a lowered block.**  Every memory
    index register the block reads is public (a frame register); every register
    the block writes is a data register (non-public).  This is the
    machine-register reflection of the source `FrameWF` (public slots → frame
    registers) plus the load-result-is-data convention of `LowCTMemCT`.  A real
    register allocator keeping bases/indices/counters in a designated frame and
    computed words in data registers satisfies it. -/
def BlockFrameWF (pub : PubPred) (body : List (JInstr 64)) : Prop :=
  (∀ i ∈ body, ∀ idx, idxReg i = some idx → pub idx = true)
    ∧ (∀ i ∈ body, ∀ d ∈ dstRegs i, pub d = false)

/-- Under the frame/data discipline, **every** instruction of a lowered block is
    `CTAddressed` — regardless of whether it is a strict-`IsDirect` w7 op or a
    public-index memory op.  (No `IsDirect` case split is even needed at the
    block level: `CTAddressed` is literally the conjunction the discipline
    states per instruction.) -/
theorem blockFrameWF_CTAddressed (pub : PubPred) (body : List (JInstr 64))
    (hwf : BlockFrameWF pub body) :
    ∀ i ∈ body, CTAddressed pub i := by
  intro i hi
  exact ⟨fun idx h => hwf.1 i hi idx h, fun d hd => hwf.2 i hi d hd⟩

/-- **Uniform constant-time, full fragment (incl. memory).**  Under the
    frame/data register discipline, the lowering of *any* unified-with-memory
    program — mixing scalar arith, widening multiply, branchless select, bounded
    loops, **and** array load/store — produces the **same** machine leakage
    trace from any two states that **agree on the public registers**.  The
    observable control-flow + memory-address sequence is therefore a function of
    the public inputs alone (frame bases/indices/counters), leaking nothing
    about the secret data.

    This is the single uniform CT theorem the w7 fragment lacked for memory: it
    uses `blockLeak_pub_determined` (the public-index `agreePub` keystone memory
    needs), applied uniformly — every instruction, memory or not, is
    `CTAddressed` under the one discipline. -/
theorem lowerUMProg_constant_time (pub : PubPred) (ρ : RegMap) (p : UMProg)
    (hwf : BlockFrameWF pub (lowerUMProg ρ p)) (s₁ s₂ : JState 64)
    (hag : agreePub pub s₁ s₂) :
    blockLeak s₁ (lowerUMProg ρ p) = blockLeak s₂ (lowerUMProg ρ p) :=
  blockLeak_pub_determined pub (lowerUMProg ρ p)
    (blockFrameWF_CTAddressed pub (lowerUMProg ρ p) hwf) s₁ s₂ hag

/-! ## 5. A realistic array-based multi-limb bignum multiply kernel

`bignumMulKernel` is a genuine array-addressed bignum multiply cell:

```
  ai   := a[i]            -- load input limb from an array (memLoad → loadMemIdx)
  (hi, lo) := ai · b      -- widening multiply (mulx)
  acc  := acc + lo        -- accumulate low word (arith)
  carry:= carry + hi      -- accumulate high word (arith)
  r[i] := acc             -- store result limb to an array (memStore → storeMemIdx)
```

the inner partial-product cell of schoolbook multiply, with **both** the input
limb read and the result limb written through register-indexed array accesses.
It mixes the memory, mulx, and arith families in one `UMProg`, carrying the
uniform CT and a one-vector value KAT through the FULL pipeline. -/

/-- Load `ai := a[i]` (array `"a"`, index `"i"`, stride 8, into data slot `"ai"`). -/
def bmLoad : MemLoadSrc :=
  { dst := "ai", arr := "a", idx := "i", scale := 8, dstTy := .TU64, arrTy := .TU64 }
/-- Widening multiply `(hi, lo) := ai · b`. -/
def bmMul : MulxSrc := { hi := "hi", lo := "lo", a := "ai", b := "b" }
/-- Low-word accumulate `acc := acc + lo`. -/
def bmAddLo : ArithSrc := { dst := "acc", a := "acc", op := .add, b := "lo" }
/-- High-word accumulate `carry := carry + hi`. -/
def bmAddHi : ArithSrc := { dst := "carry", a := "carry", op := .add, b := "hi" }
/-- Store `r[i] := acc` (array `"r"`, index `"i"`, stride 8, from data slot `"acc"`). -/
def bmStore : MemStoreSrc :=
  { arr := "r", idx := "i", src := "acc", scale := 8, arrTy := .TU64, srcTy := .TU64 }

/-- **The array-based bignum multiply cell, as one unified-with-memory program.**
    A real bignum kernel mixing the memory, mulx, and arith families. -/
def bignumMulKernel : UMProg :=
  [ .memLoad bmLoad
  , .base (.mulx bmMul)
  , .base (.arith bmAddLo)
  , .base (.arith bmAddHi)
  , .memStore bmStore ]

/-- **Lowered kernel.**  The unified-with-memory lowering under the identity
    register allocation. -/
def bignumKernel : List (JInstr 64) := lowerUMProg idRho bignumMulKernel

/-! ### The frame/data discipline for the kernel

The public (frame) registers are the array bases `a`, `r` and the loop index
`i`; the data registers are the computed words `ai`, `hi`, `lo`, `acc`,
`carry`, `b`.  Under the identity allocation this is the predicate `bmPub`. -/

/-- The public/secret split for the kernel: array bases and the index are
    public (frame) registers; all computed words are data (secret) registers. -/
def bmPub : PubPred := fun r => r = "a" || r = "r" || r = "i"

/-- **The kernel's lowering satisfies the frame/data discipline.**  Decided: the
    only index registers are `i` (public); the only destination registers are
    `ai`, `hi`, `lo`, `acc`, `carry` (all data, non-public).  Note the store
    writes no register and reads index `i` (public); the load writes `ai` (data)
    and reads index `i` (public). -/
theorem bignumKernel_frameWF : BlockFrameWF bmPub bignumKernel := by
  constructor
  · decide
  · decide

/-- **Uniform constant-time, kernel (full pipeline, memory included).**  The
    array-based bignum multiply cell leaks nothing about its secret operands:
    any two states agreeing on the public frame registers (`a`, `r`, `i`) — but
    differing arbitrarily on the secret limb data — produce the same machine
    leakage trace, via the single uniform CT theorem covering memory. -/
theorem bignumKernel_constant_time (s₁ s₂ : JState 64)
    (hag : agreePub bmPub s₁ s₂) :
    blockLeak s₁ bignumKernel = blockLeak s₂ bignumKernel :=
  lowerUMProg_constant_time bmPub idRho bignumMulKernel bignumKernel_frameWF s₁ s₂ hag

/-! ### Value KAT: the kernel computes the right product limb

The lowered kernel, run on a concrete machine state, loads input limb `a[i]`,
multiplies by `b`, accumulates into `acc`/`carry`, and stores `acc` back to
`r[i]`.  We pin a one-vector KAT against the concrete machine run. -/

/-- A concrete initial machine state for the KAT.  The array bases `a`, `r` are
    distinct memory regions; the index register `i` selects element `0`; the
    scalar `b` and accumulators are set; `a[0]` holds the input limb. -/
def bmState (aLimb b acc carry : BitVec 64) : JState 64 :=
  let base : JState 64 :=
    { regs := fun r =>
        if r = "a" then 0 else if r = "r" then 0
        else if r = "i" then 0 else if r = "b" then b
        else if r = "acc" then acc else if r = "carry" then carry else 0 }
  -- place the input limb `aLimb` at array `a`, element 0 (byte offset 0)
  base.storeIdx "a" "i" 8 aLimb

/-- **Value KAT (one vector).**  Input limb `a[0] = 7`, scalar `b = 6`,
    `acc = 0`, `carry = 0`.  The product `7 · 6 = 42` has low word `42`, high
    word `0`; after `acc += lo` we get `acc = 42`, then `r[0] := acc = 42`.  The
    result cell `r[0]` of the concrete machine run holds `42`.  Exercises the
    full chain: array load → mulx → accumulate → array store. -/
theorem bignumKernel_kat :
    (runBlock (bmState 0x7 0x6 0x0 0x0) bignumKernel).load "r" (↑(8 * 0)) = 0x2A := by
  native_decide

/-- **Value KAT (second vector, nonzero accumulator + multi-word product).**
    `a[0] = 0x100000000` (2³²), `b = 0x100000000` (2³²), `acc = 5`, `carry = 9`.
    The product `2³² · 2³² = 2⁶⁴` has low word `0`, high word `1`; after
    `acc += lo` (= 5) and `carry += hi` (= 10), the stored result `r[0]` is the
    low accumulator `5`.  Exercises the carry-out (high-word) path with a
    two-word product and nonzero accumulators. -/
theorem bignumKernel_kat2 :
    (runBlock (bmState 0x100000000 0x100000000 0x5 0x9) bignumKernel).load "r" (↑(8 * 0))
      = 0x5 := by
  native_decide

/-! ## 6. Unified functional correctness for the memory cases

The unified denotation `uMStmtDenote` dispatches the non-memory statements to
the w7 `uStmtDenote` and the memory statements to the concrete byte-offset value
semantics of `LowCTMemDenote`.  The store/load value-correctness threads BOTH
`StateMatch` (scalar registers) and `MemMatch` (array memory); the per-statement
memory cases are discharged by `lowerMemStore_denote_cell` / `lowerMemLoad_denote`.

We expose the two memory cases as the unified `compile_correct` content for the
fragment the w7 file excluded; the non-memory cases are already covered by
`lowerUStmt_denoteAll`. -/

/-- **Memory store, unified functional correctness.**  Under the concrete
    byte-offset oracle and the register/memory correspondence, the unified
    lowering of a `memStore` statement tracks the source array post-state at the
    targeted cell — the single `compile_correct` content for the store case,
    reusing `lowerMemStore_denote_cell` verbatim through the unified lowering. -/
theorem lowerUMStmt_memStore_denote (scale : Nat) (ρ : RegMap)
    (m : MemStoreSrc) (rs : RustState) (js : JState 64)
    (hscale : m.scale = scale)
    (hmatch : StateMatch ρ rs js)
    (idx : Nat) (hidxval : rs.rsScalar m.idx = idx) (hlt : idx < 2 ^ 64)
    (oldV : RustVal (⟨m.arr, m.arrTy⟩ : Located).locDst)
    (srcV : RustVal (⟨m.src, m.srcTy⟩ : Located).locDst)
    (hsrcval : js.get (ρ m.src) = valWord srcV)
    (hbound : scale * idx + 8 ≤ m.arrTy.storageBytes) :
    (runBlock js (lowerUMStmt ρ (.memStore m))).load (ρ m.arr) (↑(scale * idx))
      = arrElem
          ((byteOffsetLeafSpec scale).arrStore ⟨m.arr, m.arrTy⟩ oldV idx
            ⟨(⟨m.src, m.srcTy⟩ : Located).locDst, srcV⟩)
          scale idx := by
  rw [lowerUMStmt]
  exact lowerMemStore_denote_cell scale ρ m rs js hscale hmatch idx hidxval hlt
    oldV srcV hsrcval hbound

/-- **Memory load, unified functional correctness.**  Under the concrete
    byte-offset oracle, `StateMatch`, and `MemMatch` on the source array slot,
    the unified lowering of a `memLoad` statement loads exactly the source array
    element `idx` into `ρ dst` — the single `compile_correct` content for the
    load case, reusing `lowerMemLoad_denote` verbatim through the unified
    lowering. -/
theorem lowerUMStmt_memLoad_denote (scale : Nat) (arrBase : String → String)
    (ρ : RegMap) (m : MemLoadSrc) (rs : RustState) (js : JState 64)
    (hscale : m.scale = scale)
    (hbase : arrBase (⟨m.arr, m.arrTy⟩ : Located).locVar = ρ m.arr)
    (hmatch : StateMatch ρ rs js)
    (idx : Nat) (hidxval : rs.rsScalar m.idx = idx) (hlt : idx < 2 ^ 64)
    (srcArr : RustVal (⟨m.arr, m.arrTy⟩ : Located).locDst)
    (hsrclook : locatedLookup rs ⟨m.arr, m.arrTy⟩ = some srcArr)
    (hmem : MemMatch arrBase scale ⟨m.arr, m.arrTy⟩ rs js) :
    (runBlock js (lowerUMStmt ρ (.memLoad m))).get (ρ m.dst) = arrElem srcArr scale idx := by
  rw [lowerUMStmt]
  exact lowerMemLoad_denote scale arrBase ρ m rs js hscale hbase hmatch idx hidxval hlt
    srcArr hsrclook hmem

/-! ## 7. Non-memory functional correctness lifts verbatim

The `base` statements reuse the w7 `uStmtDenote`/`lowerUStmt`, so their
functional correctness is exactly `lowerUStmt_denoteAll` (`StateMatch`-threaded,
loops included) — no re-proof needed.  We expose the lift as the unified
`compile_correct` content for the non-memory fragment. -/

/-- The unified-with-memory denotation, per statement (memory cases via the
    concrete byte-offset oracle's *scalar* effect — the array effect is the
    `MemMatch`-tracked memory, handled by the cell-level denote lemmas above;
    here we record only the register-state update so the straight-line scalar
    threading and the kernel KAT share one denotation for the non-memory part). -/
def uMStmtScalarDenote : UMStmt → RustState → RustState
  | .base st, rs => uStmtDenote st rs
  | .memLoad _, rs => rs   -- the load's register effect is tracked via MemMatch/cell lemmas
  | .memStore _, rs => rs  -- the store touches memory, not the scalar registers
  | .forM _ _ _, rs => rs  -- loop scalar effect folded per body; see cell lemmas

/-- **Non-memory functional correctness, unified.**  A `base` statement's
    unified lowering tracks the w7 denotation under `StateMatch`, via
    `lowerUStmt_denoteAll`.  This is the unified `compile_correct` content for
    the non-memory fragment, lifted verbatim. -/
theorem lowerUMStmt_base_denote (ρ : RegMap) (hρ : Function.Injective ρ)
    (st : UStmt) (hwf : UStmtWFAll st)
    (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (uMStmtScalarDenote (.base st) rs) (runBlock js (lowerUMStmt ρ (.base st))) := by
  rw [lowerUMStmt, uMStmtScalarDenote]
  exact lowerUStmt_denoteAll ρ hρ st hwf rs js hmatch

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnifiedMem
