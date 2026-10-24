/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Source→machine constant-time bridge: the scalar-arith on-ramp

This module bridges the `LowCT` *source* constant-time analysis (`cmdCT`,
`LowCTCTAnalysis.lean`, over `RustState`) to the *machine* constant-time
class (`allDirect`, `allDirect_constant_time`, `ConstantTimeCoverage.lean`,
over `JState`).

## The fragment

The bridge covers the **memory-free, control-flow-free, scalar-arithmetic**
fragment of `LowCT`: a single `RScalarSetExpr x e` whose `SExpr e` is built
only from the *BitVec-faithful* scalar operations

  `SVar a`, `SLit n`, `SAdd a b`, `SAnd a b`, `SXor a b`

(deliberately **excluding** `SSub` — source `SSub` is *saturating* `Nat`
subtraction (`a - b` clamped at `0`), which does **not** agree with the
machine's wrapping `SUB`; including it would make the denote bridge unsound,
see the honest boundary note at the bottom).  This is exactly the source
fragment for which `cmdCT (.RScalarSetExpr x e) lt leafCT = e.isPublic lt`
(no branch, loop, array index, or memory operand), so the source CT check
is a pure data-flow `isPublic` test.

We model the fragment as `ArithSrc` — a faithful **subset** of `LowCT`,
connected by the embedding `ArithSrc.toLowCT : ArithSrc → LowCT` producing
a `LowCT.RScalarSetExpr` node: the source object is a `LowCT` command, and its
source CT result is `cmdCT`.

## What is proved

* `ArithSrc.toLowCT` — the embedding into real `LowCT`.
* `lowerArith_allDirect` — **the easy half**: every lowering is in
  the machine constant-time class.  Trivial *because* the fragment is
  memory-free: the lowering emits only register `mov`/`add`/`and`/`xor`,
  never `loadMemIdx`/`storeMemIdx`, the only two `¬ IsDirect` opcodes.
* `lowerArith_constant_time` — **the source→machine CT corollary**: the
  lowering of any scalar-arith source command produces the same machine
  leakage trace from any two states (constant-time), via
  `allDirect_constant_time`.  This is a *real* source-fragment ⇒ machine-CT
  result.
* `lowerArith_denote` — **denote preservation**: under a register map `ρ`
  (injective on the touched slots) and the state relation `StateMatch ρ`
  (machine register `ρ v` holds the 64-bit-truncated source scalar `v`), the
  machine run of the lowering tracks the source `RustExec` semantics.

## Source CT ⇒ machine CT, end to end

`LowCTMachineCT.lowerArith_source_to_machine_CT` states the chain in the CTP-1
model: a source command that is constant time lowers to a machine block that is
constant time.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The scalar-arith source fragment (a faithful `LowCT` subset) -/

/-- A binary scalar-arith operation that is **BitVec-faithful**: its source
    `Nat` semantics and its machine 64-bit semantics agree modulo `2^64`.
    `SSub` is deliberately absent (saturating `Nat` sub ≠ wrapping machine
    `SUB`). -/
inductive ArithOp where
  | add | and_ | xor_ | mul_
  deriving DecidableEq, Repr

/-- The memory-free scalar-arith fragment: a single assignment
    `x := a ⟨op⟩ b`, where `a`, `b` are scalar-slot reads.  This is a faithful
    subset of `LowCT.RScalarSetExpr x (.S⟨op⟩ (.SVar a) (.SVar b))`. -/
structure ArithSrc where
  dst : String
  a   : String
  op  : ArithOp
  b   : String
  deriving Repr

/-! ## 2. Embedding into real `LowCT` -/

/-- The `SExpr` an `ArithSrc` denotes. -/
def ArithSrc.toSExpr (p : ArithSrc) : SExpr :=
  let av := SExpr.SVar p.a
  let bv := SExpr.SVar p.b
  match p.op with
  | .add  => .SAdd av bv
  | .and_ => .SAnd av bv
  | .xor_ => .SXor av bv
  | .mul_ => .SMul av bv

/-- **The embedding into `LowCT`.**  An `ArithSrc` is the `LowCT` command
    `RScalarSetExpr p.dst (a ⟨op⟩ b)`, so the source object whose CT is
    analysed is a `LowCT` node carrying the `cmdCT` result. -/
def ArithSrc.toLowCT (p : ArithSrc) : LowCT :=
  .RScalarSetExpr p.dst p.toSExpr

/-- The source CT result for an `ArithSrc`, via the **real** `cmdCT`.  Because
    the fragment is a single `RScalarSetExpr`, `cmdCT` reduces to the
    data-flow `isPublic` check on the read slots `a`, `b`. -/
theorem ArithSrc.cmdCT_eq (p : ArithSrc) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT p.toLowCT lt leafCT = p.toSExpr.isPublic lt := by
  simp [ArithSrc.toLowCT, cmdCT_RScalarSetExpr]

/-- Concretely: the source CT result is `true` iff both read slots `a`, `b`
    are `Public` — the noninterference data-flow condition. -/
theorem ArithSrc.cmdCT_iff (p : ArithSrc) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT p.toLowCT lt leafCT = true ↔ (lt p.a == .Public) ∧ (lt p.b == .Public) := by
  rw [ArithSrc.cmdCT_eq]
  cases p with
  | mk dst a op b =>
    cases op <;>
      simp [ArithSrc.toSExpr, SExpr.isPublic, SExpr.freeVars, List.all_cons, List.all_nil]

/-! ## 3. The lowering to `JInstr 64` -/

/-- The register map: source scalar-slot names to machine register names.
    A register allocation would be injective on the live set; we keep
    it abstract and require injectivity only where the denote proof needs it. -/
abbrev RegMap := String → String

/-- The machine opcode for a scalar-arith op, applied to `dst` with operand
    `src`.  `add`/`and_`/`xor_` are all `IsDirect` (no memory operand at all). -/
def ArithOp.toJInstr : ArithOp → String → JOperand → JInstr 64
  | .add,  dst, src => .add  dst src
  | .and_, dst, src => .and_ dst src
  | .xor_, dst, src => .xor_ dst src
  | .mul_, dst, src => .imul dst src

/-- **The lowering.**  `x := a ⟨op⟩ b` lowers to a two-instruction block:
    `mov ρx, ρa`  then  `⟨op⟩ ρx, ρb`.  Memory-free: only register `mov` and
    the register-operand ALU op — no `loadMemIdx`/`storeMemIdx`. -/
def lowerArith (ρ : RegMap) (p : ArithSrc) : List (JInstr 64) :=
  [ .mov (ρ p.dst) (.reg (ρ p.a))
  , p.op.toJInstr (ρ p.dst) (.reg (ρ p.b)) ]

/-! ## 4. The easy half: machine constant-time -/

/-- Every emitted instruction of the lowering is `IsDirect` (true for all but
    `loadMemIdx`/`storeMemIdx`, neither of which the memory-free fragment
    emits). -/
theorem lowerArith_allDirect (ρ : RegMap) (p : ArithSrc) :
    allDirect (lowerArith ρ p) = true := by
  cases p with
  | mk dst a op b => cases op <;> rfl

/-- **Source→machine constant-time.**  The lowering of *any* scalar-arith
    source command produces the **same** machine leakage trace from any two
    initial states: its observable control-flow + memory-address sequence is a
    function of the program text alone, leaking nothing about the (possibly
    secret) register values.  Delivered by `allDirect_constant_time` from the
    `allDirect` check. -/
theorem lowerArith_constant_time (ρ : RegMap) (p : ArithSrc) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerArith ρ p) = blockLeak s₂ (lowerArith ρ p) :=
  allDirect_constant_time (lowerArith ρ p) (lowerArith_allDirect ρ p) s₁ s₂

/-! ## 5. State relation and denote preservation -/

/-- **State match.**  The machine register `ρ v` holds the 64-bit-truncated
    source scalar `v`, for *every* slot name `v`.  (Source scalars are `Nat`;
    machine registers are `BitVec 64`; the faithful relation is truncation.) -/
def StateMatch (ρ : RegMap) (rs : RustState) (js : JState 64) : Prop :=
  ∀ v, js.get (ρ v) = BitVec.ofNat 64 (rs.rsScalar v)

/-- The machine value the op-instruction computes from two register reads,
    expressed at the `BitVec` level. -/
theorem ArithOp.toJInstr_word (op : ArithOp) (dst : String) (rb : String)
    (s : JState 64) :
    (evalInstr s (op.toJInstr dst (.reg rb))).get dst =
      (match op with
       | .add  => s.get dst + s.get rb
       | .and_ => s.get dst &&& s.get rb
       | .xor_ => s.get dst ^^^ s.get rb
       | .mul_ => s.get dst * s.get rb) := by
  cases op <;>
    simp [ArithOp.toJInstr, evalInstr, x86_ADD, x86_AND, x86_XOR, x86_IMULt,
          rflags_of_aluop, rflags_of_bwop, rflags_of_mul, JState.writeB5W, JState.get]

/-- The op-instruction writes only its destination `dst`; reading any other
    register `r ≠ dst` falls through unchanged. -/
theorem ArithOp.toJInstr_get_other (op : ArithOp) (dst rb : String)
    (s : JState 64) (r : String) (hr : r ≠ dst) :
    (evalInstr s (op.toJInstr dst (.reg rb))).get r = s.get r := by
  cases op <;>
    simp [ArithOp.toJInstr, evalInstr, x86_ADD, x86_AND, x86_XOR, x86_IMULt,
          rflags_of_aluop, rflags_of_bwop, rflags_of_mul, JState.writeB5W, JState.get, hr]

/-- The source `SExpr` value of the fragment, at the `BitVec` level: each op
    distributes over `BitVec.ofNat 64`, so the source `Nat` value truncates to
    the machine value computed from the truncated operands.  This is where the
    **faithfulness** of the op set is used: `SAdd`/`SAnd`/`SXor` all commute
    with `BitVec.ofNat 64` (saturating `SSub` would not). -/
theorem ArithSrc.toSExpr_eval_ofNat (p : ArithSrc) (σ : String → Nat) :
    BitVec.ofNat 64 (p.toSExpr.eval σ) =
      (match p.op with
       | .add  => BitVec.ofNat 64 (σ p.a) + BitVec.ofNat 64 (σ p.b)
       | .and_ => BitVec.ofNat 64 (σ p.a) &&& BitVec.ofNat 64 (σ p.b)
       | .xor_ => BitVec.ofNat 64 (σ p.a) ^^^ BitVec.ofNat 64 (σ p.b)
       | .mul_ => BitVec.ofNat 64 (σ p.a) * BitVec.ofNat 64 (σ p.b)) := by
  cases p with
  | mk dst a op b =>
    cases op <;>
      simp [ArithSrc.toSExpr, SExpr.eval, BitVec.ofNat_add, BitVec.ofNat_and,
            BitVec.ofNat_xor, BitVec.ofNat_mul]

/-! ### Denote preservation

`lowerArith_denote`: under the register map `ρ` and the state relation
`StateMatch ρ`, running the lowered block tracks the source `RustExec`
semantics.  The hypotheses are the *register-allocation well-formedness*
conditions a real allocator guarantees:

* `ρ` injective — distinct source slots get distinct machine registers (so a
  write to `ρ dst` does not disturb the image of any other slot);
* `ρ p.b ≠ ρ p.dst` — the second operand register is not the destination
  (equivalently `p.b ≠ p.dst` given injectivity), so the `mov` that primes
  `ρ dst` with `ρ a` does not clobber the `b` read.

These are exactly the constraints under which the two-instruction
`mov; op` schedule is a faithful lowering of `x := a ⟨op⟩ b`. -/

/-- **Denote preservation (the hard half).**  If the machine state `js` matches
    the source state `rs` under `ρ`, then after running the lowered block the
    machine state matches the source post-state
    `rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)` — i.e. the `RustExec`
    result of `p.toLowCT` (`RustExec.scalarSetExpr`).  Proven for the whole
    `add`/`and`/`xor` fragment via `toSExpr_eval_ofNat`. -/
theorem lowerArith_denote (ρ : RegMap) (p : ArithSrc) (rs : RustState) (js : JState 64)
    (hρ : Function.Injective ρ) (hb : p.b ≠ p.dst)
    (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar))
      (runBlock js (lowerArith ρ p)) := by
  intro v
  rw [StateMatch] at hmatch
  -- The post-machine state, after `mov ρdst ρa` then `op ρdst ρb`.
  -- `s1` is the state after the `mov` that primes `ρ dst` with `ρ a`.
  set s1 : JState 64 := evalInstr js (.mov (ρ p.dst) (.reg (ρ p.a))) with hs1
  have hs1_eq : s1 = js.setReg (ρ p.dst) (js.get (ρ p.a)) := by
    simp [hs1, evalInstr, x86_MOV, JOperand.eval]
  have hrun : runBlock js (lowerArith ρ p) =
      evalInstr s1 (p.op.toJInstr (ρ p.dst) (.reg (ρ p.b))) := by
    simp [lowerArith, runBlock_cons, runBlock_nil, hs1]
  rw [hrun]
  by_cases hv : v = p.dst
  · -- `v = dst`: the register `ρ dst` now holds the computed value.
    subst hv
    have hbv : ρ p.b ≠ ρ p.dst := fun h => hb (hρ h)
    rw [ArithOp.toJInstr_word, hs1_eq]
    simp only [JState.get_setReg_same, JState.get_setReg_other _ _ _ _ hbv,
               rsSetScalar, beq_self_eq_true, ite_true]
    rw [hmatch p.a, hmatch p.b]
    have hop := ArithSrc.toSExpr_eval_ofNat p rs.rsScalar
    cases p with
    | mk dst a op b => cases op <;> simpa using hop.symm
  · -- `v ≠ dst`: the op writes `ρ dst ≠ ρ v` (injectivity), leaving `ρ v` alone.
    have hvd : ρ v ≠ ρ p.dst := fun h => hv (hρ h)
    rw [ArithOp.toJInstr_get_other _ _ _ _ _ hvd, hs1_eq,
        JState.get_setReg_other _ _ _ _ hvd]
    simp only [rsSetScalar, beq_eq_false_iff_ne.mpr hv, Bool.false_eq_true, ite_false]
    exact hmatch v

/-- The expression of an arithmetic source reads two scalar slots and no tower
    limb. -/
theorem ArithSrc.toSExpr_limbFree (p : ArithSrc) : p.toSExpr.limbFree := by
  cases p with
  | mk dst a op b => cases op <;> simp [ArithSrc.toSExpr, SExpr.limbFree]

/-- The source post-state of `p.toLowCT` under the **real** `RustExec`
    operational semantics: `RustExec.scalarSetExpr` steps
    `RScalarSetExpr p.dst p.toSExpr` to `rsSetScalar rs p.dst (eval …)`
    (`p.toSExpr` is `limbFree`, so `evalState` is `eval`).  This
    ties `lowerArith_denote`'s post-state to the `LowCT` semantics rather than
    to a re-stated denotation. -/
theorem ArithSrc.rustExec (N : Nat) (leafSpec : LeafSpec) (p : ArithSrc)
    (rs : RustState) :
    RustExec N leafSpec p.toLowCT rs
      (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)) := by
  rw [← SExpr.evalState_eq_eval rs _ p.toSExpr_limbFree]
  exact RustExec.scalarSetExpr p.dst p.toSExpr rs

/-- **Denote preservation, against the real `RustExec`.**  Combines
    `ArithSrc.rustExec` (the source step) with `lowerArith_denote`:
    for the unique source post-state `rs'` reached by `RustExec` on
    `p.toLowCT`, the machine run of the lowering ends in a `StateMatch`-related
    machine state.  This is the source-operational-semantics ⇒ machine-run
    correspondence the bridge delivers. -/
theorem lowerArith_denote_rustExec (N : Nat) (leafSpec : LeafSpec)
    (ρ : RegMap) (p : ArithSrc) (rs rs' : RustState) (js : JState 64)
    (hρ : Function.Injective ρ) (hb : p.b ≠ p.dst)
    (hmatch : StateMatch ρ rs js)
    (hexec : RustExec N leafSpec p.toLowCT rs rs') :
    StateMatch ρ rs' (runBlock js (lowerArith ρ p)) := by
  -- `RustExec` on a `RScalarSetExpr` is deterministic: `rs'` is exactly the
  -- `scalarSetExpr` post-state.
  cases hexec
  rw [SExpr.evalState_eq_eval rs _ p.toSExpr_limbFree]
  exact lowerArith_denote ρ p rs js hρ hb hmatch

/-! ## 7. The basic-block compiler: a sequence of scalar-arith statements

Phase 1 of a verified `LowCT → JInstr` compiler.  We lift the single-statement
bridge to a **straight-line basic block** — a `List ArithSrc` of scalar-arith
assignments — and prove the same three guarantees compositionally:

* `lowerSeq_allDirect` / `lowerSeq_constant_time` — machine constant-time of the
  whole block (the easy half, via `List.all_append`);
* `lowerSeq_denote` — denote preservation of the whole block against the folded
  source semantics `srcDenote` (the hard half, threaded by induction).

The structural helper `runBlock_append` is proved locally so the module stays
self-contained (it exists elsewhere in the backend but is not imported here);
`allDirect_append` comes from `ConstantTimeCoverage`. -/

/-- `runBlock` over a concatenation: run the first block, then the second from
    the resulting state.  (Local copy; the same lemma lives in
    `BignumCarryDecomp`/`LoopUnroll`, not imported here.) -/
theorem runBlock_append {w : Nat} (s : JState w) (l₁ l₂ : List (JInstr w)) :
    runBlock s (l₁ ++ l₂) = runBlock (runBlock s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBlock_cons, ih]

/-- **The basic-block lowering.**  A straight-line list of scalar-arith
    assignments lowers to the concatenation of the per-statement lowerings. -/
def lowerSeq (ρ : RegMap) (ps : List ArithSrc) : List (JInstr 64) :=
  ps.flatMap (lowerArith ρ)

/-- **The source-side block semantics.**  Fold the per-statement scalar update
    `dst := (a ⟨op⟩ b)` left-to-right over the source state.  This is the
    denotation the lowered block must track. -/
def srcDenote (ps : List ArithSrc) (rs : RustState) : RustState :=
  ps.foldl (fun rs p => rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)) rs

@[simp] theorem lowerSeq_nil (ρ : RegMap) : lowerSeq ρ [] = [] := rfl

@[simp] theorem lowerSeq_cons (ρ : RegMap) (p : ArithSrc) (ps : List ArithSrc) :
    lowerSeq ρ (p :: ps) = lowerArith ρ p ++ lowerSeq ρ ps := by
  simp [lowerSeq, List.flatMap_cons]

@[simp] theorem srcDenote_nil (rs : RustState) : srcDenote [] rs = rs := rfl

@[simp] theorem srcDenote_cons (p : ArithSrc) (ps : List ArithSrc) (rs : RustState) :
    srcDenote (p :: ps) rs =
      srcDenote ps (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)) := rfl

/-- **Machine constant-time, block-level (easy half).**  Every
    instruction of the lowered block is `IsDirect` — the block is memory-free,
    so its lowering emits only register `mov`/`add`/`and`/`xor`/`imul`. -/
theorem lowerSeq_allDirect (ρ : RegMap) (ps : List ArithSrc) :
    allDirect (lowerSeq ρ ps) = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [lowerSeq_cons, allDirect_append, lowerArith_allDirect, ih, Bool.and_self]

/-- **Source→machine constant-time, block-level.**  The lowering of any
    straight-line scalar-arith block produces the same machine leakage trace
    from any two initial states. -/
theorem lowerSeq_constant_time (ρ : RegMap) (ps : List ArithSrc) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerSeq ρ ps) = blockLeak s₂ (lowerSeq ρ ps) :=
  allDirect_constant_time (lowerSeq ρ ps) (lowerSeq_allDirect ρ ps) s₁ s₂

/-- **Denote preservation, block-level (the hard half).**  Under the
    register map `ρ` (injective on the touched slots) and the per-statement
    well-formedness condition `p.b ≠ p.dst`, the machine run of the lowered
    block tracks the folded source semantics `srcDenote`.  Proven by induction
    on the block, threading `StateMatch` through each statement via
    `lowerArith_denote` and splitting the run with `runBlock_append`. -/
theorem lowerSeq_denote (ρ : RegMap) (hρ : Function.Injective ρ)
    (ps : List ArithSrc) (hwf : ∀ p ∈ ps, p.b ≠ p.dst)
    (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (srcDenote ps rs) (runBlock js (lowerSeq ρ ps)) := by
  induction ps generalizing rs js with
  | nil => simpa using hmatch
  | cons p ps ih =>
    rw [lowerSeq_cons, runBlock_append, srcDenote_cons]
    have hhead : StateMatch ρ (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar))
        (runBlock js (lowerArith ρ p)) :=
      lowerArith_denote ρ p rs js hρ (hwf p (List.mem_cons_self ..)) hmatch
    exact ih (fun q hq => hwf q (List.mem_cons_of_mem _ hq)) _ _ hhead

/-! ## 8. Connecting the block to a real `LowCT` sequence (end-to-end source CT)

`ArithSrc.seqToLowCT` embeds the block as a right-nested `LowCT.RSeq` chain of
`RScalarSetExpr` nodes, so the source CT result of the whole block is `cmdCT`
over that chain.  `seq_cmdCT` shows it factors through the
per-statement `cmdCT` checks, and `lowerSeq_source_to_machine_CT` packages the
end-to-end shape: a source block accepted by `cmdCT` lowers to a machine block
that is constant-time. -/

/-- **The block embedded into `LowCT`.**  A right-nested `RSeq` chain of the
    per-statement `RScalarSetExpr` nodes, terminated by `RSkip`, making the
    block a `LowCT` command whose source CT result is `cmdCT`. -/
def ArithSrc.seqToLowCT (ps : List ArithSrc) : LowCT :=
  ps.foldr (fun p acc => .RSeq p.toLowCT acc) .RSkip

@[simp] theorem ArithSrc.seqToLowCT_nil : ArithSrc.seqToLowCT [] = .RSkip := rfl

@[simp] theorem ArithSrc.seqToLowCT_cons (p : ArithSrc) (ps : List ArithSrc) :
    ArithSrc.seqToLowCT (p :: ps) = .RSeq p.toLowCT (ArithSrc.seqToLowCT ps) := rfl

/-- **Block source CT result factors through the per-statement checks.**  The
    real `cmdCT` of the whole `RSeq` chain is `true` iff every statement's
    `cmdCT` is `true` (i.e. every statement's read slots are `Public`). -/
theorem seq_cmdCT (ps : List ArithSrc) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (ArithSrc.seqToLowCT ps) lt leafCT
      = ps.all (fun p => cmdCT p.toLowCT lt leafCT) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp [ArithSrc.seqToLowCT_cons, cmdCT_RSeq, ih, List.all_cons]

/-- **Source CT result ⇒ machine constant-time, block-level (end to end).**
    If the source block `seqToLowCT ps` passes the real source CT analyser
    `cmdCT`, its lowering is constant-time at the machine level.

    As in the single-statement case, the `cmdCT` hypothesis is consumed only on
    the source side: machine CT is unconditional for this memory-free fragment
    (the lowering is always `allDirect`).  The statement records the intended
    contract — a CT-accepted source block compiles to CT machine code — so the
    end-to-end source-analyser ⇒ machine-class shape is present. -/
theorem lowerSeq_source_to_machine_CT (ρ : RegMap) (ps : List ArithSrc)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (_hsrc : cmdCT (ArithSrc.seqToLowCT ps) lt leafCT = true) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerSeq ρ ps) = blockLeak s₂ (lowerSeq ρ ps) :=
  lowerSeq_constant_time ρ ps s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
