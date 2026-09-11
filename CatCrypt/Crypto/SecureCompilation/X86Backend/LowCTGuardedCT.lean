/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# Source→machine bridge, Phase 1b: the *guarded* scalar ops

This module extends the homomorphic scalar-arith bridge
(`LowCTToJInstrCT.lean`) to the **guarded** scalar operations — subtraction
and the logical shifts — whose source `LowCT` semantics agree with the
machine `JInstr` semantics only **under a range / no-underflow guard**.

## Why these ops are guarded (and not in the homomorphic fragment)

The homomorphic bridge deliberately excludes `SSub`/`SShl`/`SShr` because the
source `SExpr.eval` semantics diverge from the wrapping `u64` machine on
out-of-range inputs:

* `SSub a b` — source `SExpr.eval` is **saturating** `Nat` subtraction
  (`a - b` clamped at `0`); the machine `x86_SUB` is **wrapping** two's
  complement. They agree exactly when `b ≤ a` (no underflow).
* `SShl a b` — source `<<<` is an **unbounded** `Nat` shift; the machine
  `x86_SHL` masks its count `% 64`. They agree when `b < 64`; the result word
  agrees unconditionally (both are `(a * 2^b) mod 2^64`).
* `SShr a b` — source `>>>` is a `Nat` logical right shift; the machine
  `x86_SHR` masks `% 64` and operates on the 64-bit truncation of `a`. They
  agree when `b < 64` **and** `a < 2^64` (so the source has no high bits the
  truncation drops).

These divergences are **Rust-extraction artifacts**: the source `SExpr` model
(saturating `.saturating_sub`, unbounded `Nat` shift) does not match Rust's
wrapping `u64` arithmetic. Rather than silently lowering an unsound op, the
verified lowering carries the guard as a **precondition** on the source
values. The honest framing: *outside the guard the source model and the
machine disagree, and that disagreement is the source model's, not the
compiler's* — it should be reported upstream, not patched into either side.

The guards here are exactly the `SExpr.inRange` side-conditions for the
corresponding nodes (`LowCT.lean` §"Wrapping-`u64` reconciliation"), so this
bridge is the source→machine companion of the in-tree
`SExpr.evalBV_eq_ofNat_eval` Nat-model soundness theorem.

## What is proved

* `GuardedSrc.toLowCT` — the embedding into real `LowCT` (`RScalarSetExpr`),
  so the source object is a `LowCT` node with the real `cmdCT` result.
* `lowerGuarded_allDirect` / `lowerGuarded_constant_time` — **the easy
  unconditional half**: the lowering is memory-free (`mov`; `sub`/`shl`/`shr`
  over register/immediate operands), so it is in the machine constant-time
  class with **no guard needed** — CT does not depend on the value guard.
* `ofNat_sub_of_le` / `ofNat_shiftLeft_lt` / `ofNat_shiftRight_of_lt` —
  the per-op `BitVec.ofNat`-distribution lemmas **under the guard** (the crux).
* `lowerGuarded_denote` — **denote preservation under the guard**: with `ρ`
  injective, the operand-disjointness side-condition, the per-statement guard
  on the *source* values, and `StateMatch ρ`, the lowered block tracks the
  source `RScalarSetExpr` semantics.
* `lowerGuarded_denote_rustExec` — the same against the real `RustExec`.
* `GuardedSrc.cmdCT_iff` — the source CT result reduces to operand publicness.
* `lowerGuarded_source_to_machine_CT` — the end-to-end source-CT ⇒ machine-CT
  shape.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTGuardedCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT (RegMap StateMatch)

/-! ## 1. The guarded scalar-op source fragment (a faithful `LowCT` subset)

The guarded fragment is a single assignment `x := a ⟨op⟩ b` where `op` is one
of the three guarded ops. The second operand `b` is a **register read** for
subtraction and an **immediate count** for the shifts (mirroring the machine,
where the source shift operand is a compile-time count, lowered as
`shl/shr dst, imm`). We bundle the operand with the op tag. -/

/-- A guarded scalar operation, carrying its second operand.

    * `sub b` — subtraction by the scalar slot `b` (a register read).
    * `shl b` / `shr b` — logical left/right shift by the **immediate** count
      `b : Nat`. -/
inductive GuardedOp where
  | sub (b : String)
  | shl (b : Nat)
  | shr (b : Nat)
  deriving Repr

/-- The guarded single-assignment fragment: `dst := a ⟨op⟩ b`, a faithful
    subset of `LowCT.RScalarSetExpr dst (.S⟨op⟩ (.SVar a) ⟨b⟩)`. -/
structure GuardedSrc where
  dst : String
  a   : String
  op  : GuardedOp
  deriving Repr

/-! ## 2. Embedding into real `LowCT` -/

/-- The `SExpr` a `GuardedSrc` denotes. `sub`'s operand is a `SVar`, the
    shifts' operand is the immediate count as a `SLit`. -/
def GuardedSrc.toSExpr (p : GuardedSrc) : SExpr :=
  let av := SExpr.SVar p.a
  match p.op with
  | .sub b => .SSub av (.SVar b)
  | .shl b => .SShl av (.SLit b)
  | .shr b => .SShr av (.SLit b)

/-- **The embedding into real `LowCT`.** A `GuardedSrc` is the `LowCT`
    command `RScalarSetExpr p.dst (a ⟨op⟩ b)`; the source object whose CT we
    analyse is a real `LowCT` node with the real `cmdCT` result. -/
def GuardedSrc.toLowCT (p : GuardedSrc) : LowCT :=
  .RScalarSetExpr p.dst p.toSExpr

/-- The source CT result for a `GuardedSrc`, via the **real** `cmdCT`: for a
    single `RScalarSetExpr`, `cmdCT` reduces to the data-flow `isPublic` check
    on the read slots. -/
theorem GuardedSrc.cmdCT_eq (p : GuardedSrc) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT p.toLowCT lt leafCT = p.toSExpr.isPublic lt := by
  simp [GuardedSrc.toLowCT, cmdCT_RScalarSetExpr]

/-- Concretely: the source CT result is `true` iff the read slot(s) are
    `Public` — `a` (and `b` for subtraction; the shift count is a literal and
    reads nothing). -/
theorem GuardedSrc.cmdCT_iff (p : GuardedSrc) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT p.toLowCT lt leafCT = true ↔
      (match p.op with
       | .sub b => (lt p.a == .Public) ∧ (lt b == .Public)
       | .shl _ => (lt p.a == .Public)
       | .shr _ => (lt p.a == .Public)) := by
  rw [GuardedSrc.cmdCT_eq]
  cases p with
  | mk dst a op =>
    cases op <;>
      simp [GuardedSrc.toSExpr, SExpr.isPublic, SExpr.freeVars, List.all_cons, List.all_nil]

/-! ## 3. The lowering to `JInstr 64` -/

/-- The machine opcode for a guarded op, applied to `dst`. The operand is the
    register `ρ b` for `sub` and the immediate count `b` for the shifts — the
    `shl/shr dst, imm` form, matching the machine's masked-count semantics. -/
def GuardedOp.toJInstr (ρ : RegMap) : GuardedOp → String → JInstr 64
  | .sub b, dst => .sub dst (.reg (ρ b))
  | .shl b, dst => .shl dst (.imm b)
  | .shr b, dst => .shr dst (.imm b)

/-- **The lowering.** `x := a ⟨op⟩ b` lowers to a two-instruction block:
    `mov ρx, ρa` then `⟨op⟩ ρx, <b>`. Memory-free. -/
def lowerGuarded (ρ : RegMap) (p : GuardedSrc) : List (JInstr 64) :=
  [ .mov (ρ p.dst) (.reg (ρ p.a))
  , p.op.toJInstr ρ (ρ p.dst) ]

/-! ## 4. The easy unconditional half: machine constant-time

CT is independent of the value guard: the guarded fragment is memory-free, so
its lowering is always `allDirect` (every opcode but `loadMemIdx`/`storeMemIdx`
is `IsDirect`). The guard is consumed only by the denote bridge below. -/

/-- Every emitted instruction of the lowering is `IsDirect` (memory-free). -/
theorem lowerGuarded_allDirect (ρ : RegMap) (p : GuardedSrc) :
    allDirect (lowerGuarded ρ p) = true := by
  cases p with
  | mk dst a op => cases op <;> rfl

/-- **Source→machine constant-time (unconditional).** The lowering of any
    guarded source command produces the same machine leakage trace from any
    two initial states. No value guard is needed for CT. -/
theorem lowerGuarded_constant_time (ρ : RegMap) (p : GuardedSrc) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerGuarded ρ p) = blockLeak s₂ (lowerGuarded ρ p) :=
  allDirect_constant_time (lowerGuarded ρ p) (lowerGuarded_allDirect ρ p) s₁ s₂

/-! ## 5. The per-op `BitVec.ofNat`-distribution lemmas (under the guard)

These are the crux: the source `Nat` value truncates to the machine value
computed from the truncated operands, **only under the stated guard**. They are
the `BitVec`-level facts the denote bridge plugs in. -/

/-- **Guarded sub.** Under `b ≤ a` and `a < 2^64`, the truncation of the (true,
    non-saturating) `Nat` difference equals the wrapping `BitVec` difference.
    `b ≤ a` makes saturating `Nat` sub a true sub, and the result `< 2^64`. -/
theorem ofNat_sub_of_le (a b : Nat) (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 (a - b) = BitVec.ofNat 64 a - BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hb : b < 2 ^ 64 := lt_of_le_of_lt hba ha
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have heq : 2 ^ 64 - b + a = 2 ^ 64 + (a - b) := by omega
  rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- **Guarded shl.** Under `b < 64` (and the result in range), the truncation of
    the unbounded `Nat` left shift equals the `BitVec` left shift by `b`. The
    machine count-mask `% 64` is the identity for `b < 64`. -/
theorem ofNat_shiftLeft_lt (a b : Nat) (hres : a <<< b < 2 ^ 64) :
    BitVec.ofNat 64 (a <<< b) = (BitVec.ofNat 64 a) <<< b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hres]
  conv_rhs => rw [Nat.shiftLeft_eq, Nat.mul_mod, Nat.mod_mod_of_dvd a (dvd_refl _),
      ← Nat.mul_mod, ← Nat.shiftLeft_eq, Nat.mod_eq_of_lt hres]

/-- **Guarded shr.** Under `a < 2^64` (and `b < 64`), the truncation of the
    `Nat` logical right shift equals the `BitVec` logical right shift by `b`.
    `a < 2^64` ensures the source has no high bits absent from the truncation. -/
theorem ofNat_shiftRight_of_lt (a b : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 (a >>> b) = (BitVec.ofNat 64 a) >>> b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) ha)]

/-! ## 6. State relation and denote preservation (under the guard)

The denote bridge mirrors `lowerArith_denote`, but consumes the per-statement
**guard on the source values** (the `SExpr.inRange` condition for the node).
The guard is what makes the `BitVec.ofNat`-truncation relation hold. -/

/-- The per-statement **source-value guard**: the no-underflow / range
    side-condition under which the source `SExpr` value tracks the machine
    word. Stated on the *source* scalar reads `rs.rsScalar`. This is exactly
    `(p.toSExpr).inRange rs.rsScalar` specialised to the three guarded ops. -/
def GuardedSrc.guard (p : GuardedSrc) (rs : RustState) : Prop :=
  match p.op with
  | .sub b => rs.rsScalar p.a < 2 ^ 64 ∧ rs.rsScalar b ≤ rs.rsScalar p.a
  | .shl b => b < 64 ∧ rs.rsScalar p.a <<< b < 2 ^ 64
  | .shr b => b < 64 ∧ rs.rsScalar p.a < 2 ^ 64

/-- The machine value the op-instruction computes, at the `BitVec` level.
    `sub` reads register `ρ b`; the shifts shift by the immediate count `b`.
    For shifts we expose the masked-count form `x86_SHL`/`x86_SHR` produce. -/
theorem GuardedOp.toJInstr_word (ρ : RegMap) (op : GuardedOp) (dst : String)
    (s : JState 64) :
    (evalInstr s (op.toJInstr ρ dst)).get dst =
      (match op with
       | .sub b => s.get dst - s.get (ρ b)
       | .shl b => (x86_SHL (s.get dst) (BitVec.ofNat 64 b)).word
       | .shr b => (x86_SHR (s.get dst) (BitVec.ofNat 64 b)).word) := by
  cases op <;>
    simp [GuardedOp.toJInstr, evalInstr, x86_SUB, JOperand.eval,
          JState.writeB5W, JState.get]

/-- The op-instruction writes only its destination `dst`; any other register
    `r ≠ dst` falls through unchanged. -/
theorem GuardedOp.toJInstr_get_other (ρ : RegMap) (op : GuardedOp) (dst : String)
    (s : JState 64) (r : String) (hr : r ≠ dst) :
    (evalInstr s (op.toJInstr ρ dst)).get r = s.get r := by
  cases op <;>
    simp [GuardedOp.toJInstr, evalInstr, x86_SUB, x86_SHL, x86_SHR, JOperand.eval,
          JState.writeB5W, JState.get, hr]

/-- The masked machine shift-left word equals the raw `BitVec` shift when the
    count is `< 64` (the count-mask `% 64` and the width-clamp `min 64` are both
    the identity), distinguishing the `b = 0` and `b ≠ 0` branches of
    `x86_SHL`. -/
theorem x86_SHL_word_lt (v : BitVec 64) (b : Nat) (hb : b < 64) :
    (x86_SHL v (BitVec.ofNat 64 b)).word = v <<< b := by
  simp only [x86_SHL, shiftCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
             Nat.mod_eq_of_lt (lt_of_lt_of_le hb (by norm_num : (64 : Nat) ≤ 2 ^ 64))]
  by_cases h0 : b = 0
  · subst h0; simp [rflags_None]
  · simp only [h0, if_false, rflags_OF, wshl, min_eq_right (le_of_lt hb)]

/-- The masked machine shift-right word equals the raw `BitVec` shift when the
    count is `< 64`. -/
theorem x86_SHR_word_lt (v : BitVec 64) (b : Nat) (hb : b < 64) :
    (x86_SHR v (BitVec.ofNat 64 b)).word = v >>> b := by
  simp only [x86_SHR, shiftCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
             Nat.mod_eq_of_lt (lt_of_lt_of_le hb (by norm_num : (64 : Nat) ≤ 2 ^ 64))]
  by_cases h0 : b = 0
  · subst h0; simp [rflags_None]
  · simp only [h0, if_false, rflags_OF, wshr, min_eq_right (le_of_lt hb)]

/-- **The source `SExpr` value of the guarded fragment, at the `BitVec`
    level, under the guard.** Each guarded op distributes over `BitVec.ofNat 64`
    *only because the guard holds* — this is where the per-op guard lemmas of §5
    are consumed. -/
theorem GuardedSrc.toSExpr_eval_ofNat (p : GuardedSrc) (σ : String → Nat)
    (hg : (match p.op with
           | .sub b => σ p.a < 2 ^ 64 ∧ σ b ≤ σ p.a
           | .shl b => b < 64 ∧ σ p.a <<< b < 2 ^ 64
           | .shr b => b < 64 ∧ σ p.a < 2 ^ 64)) :
    BitVec.ofNat 64 (p.toSExpr.eval σ) =
      (match p.op with
       | .sub b => BitVec.ofNat 64 (σ p.a) - BitVec.ofNat 64 (σ b)
       | .shl b => (BitVec.ofNat 64 (σ p.a)) <<< b
       | .shr b => (BitVec.ofNat 64 (σ p.a)) >>> b) := by
  cases p with
  | mk dst a op =>
    cases op with
    | sub b =>
      obtain ⟨ha, hba⟩ := hg
      simp only [GuardedSrc.toSExpr, SExpr.eval]
      exact ofNat_sub_of_le (σ a) (σ b) hba ha
    | shl b =>
      obtain ⟨_, hres⟩ := hg
      simp only [GuardedSrc.toSExpr, SExpr.eval]
      exact ofNat_shiftLeft_lt (σ a) b hres
    | shr b =>
      obtain ⟨_, ha⟩ := hg
      simp only [GuardedSrc.toSExpr, SExpr.eval]
      exact ofNat_shiftRight_of_lt (σ a) b ha

/-! ### Denote preservation

`lowerGuarded_denote` mirrors `lowerArith_denote`, additionally consuming the
per-statement source-value guard `p.guard rs`. The well-formedness side
condition for `sub` is `b ≠ dst` (the operand register must not be the
destination, so the `mov` that primes `ρ dst` does not clobber the `b` read);
the shifts have no register operand, so they need no such condition. -/

/-- The operand-disjointness well-formedness condition: for `sub` the operand
    slot must differ from the destination; the shifts (immediate operand)
    impose nothing. -/
def GuardedSrc.wf (p : GuardedSrc) : Prop :=
  match p.op with
  | .sub b => b ≠ p.dst
  | .shl _ => True
  | .shr _ => True

/-- **Denote preservation under the guard (the hard half).** If the machine
    state `js` matches the source state `rs` under `ρ`, `ρ` is injective, the
    well-formedness condition `p.wf` holds, and the **source-value guard**
    `p.guard rs` holds, then after running the lowered block the machine state
    matches the source post-state `rsSetScalar rs p.dst (p.toSExpr.eval …)`
    — the `RustExec` result of `p.toLowCT`. -/
theorem lowerGuarded_denote (ρ : RegMap) (p : GuardedSrc) (rs : RustState) (js : JState 64)
    (hρ : Function.Injective ρ) (hwf : p.wf) (hg : p.guard rs)
    (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar))
      (runBlock js (lowerGuarded ρ p)) := by
  intro v
  rw [StateMatch] at hmatch
  set s1 : JState 64 := evalInstr js (.mov (ρ p.dst) (.reg (ρ p.a))) with hs1
  have hs1_eq : s1 = js.setReg (ρ p.dst) (js.get (ρ p.a)) := by
    simp [hs1, evalInstr, x86_MOV, JOperand.eval]
  have hrun : runBlock js (lowerGuarded ρ p) =
      evalInstr s1 (p.op.toJInstr ρ (ρ p.dst)) := by
    simp [lowerGuarded, runBlock_cons, runBlock_nil, hs1]
  rw [hrun]
  -- The guard re-expressed on `σ = rs.rsScalar` (for the op-value lemma).
  have hgσ : (match p.op with
           | .sub b => rs.rsScalar p.a < 2 ^ 64 ∧ rs.rsScalar b ≤ rs.rsScalar p.a
           | .shl b => b < 64 ∧ rs.rsScalar p.a <<< b < 2 ^ 64
           | .shr b => b < 64 ∧ rs.rsScalar p.a < 2 ^ 64) := by
    exact hg
  by_cases hv : v = p.dst
  · -- `v = dst`: the register `ρ dst` now holds the computed value.
    subst hv
    rw [GuardedOp.toJInstr_word, hs1_eq]
    have hop := GuardedSrc.toSExpr_eval_ofNat p rs.rsScalar hgσ
    -- Case on the op; align machine word with the guarded `ofNat` value.
    cases p with
    | mk dst a op =>
      cases op with
      | sub b =>
        have hwf' : b ≠ dst := by simpa [GuardedSrc.wf] using hwf
        have hbv : ρ b ≠ ρ dst := fun h => hwf' (hρ h)
        simp only [JState.get_setReg_same, JState.get_setReg_other _ _ _ _ hbv,
                   rsSetScalar, beq_self_eq_true, if_true]
        rw [hmatch a, hmatch b]
        simpa [GuardedSrc.toSExpr] using hop.symm
      | shl b =>
        obtain ⟨hb, _⟩ := hgσ
        simp only [JState.get_setReg_same, rsSetScalar, beq_self_eq_true, if_true]
        rw [x86_SHL_word_lt _ b hb, hmatch a]
        simpa [GuardedSrc.toSExpr] using hop.symm
      | shr b =>
        obtain ⟨hb, _⟩ := hgσ
        simp only [JState.get_setReg_same, rsSetScalar, beq_self_eq_true, if_true]
        rw [x86_SHR_word_lt _ b hb, hmatch a]
        simpa [GuardedSrc.toSExpr] using hop.symm
  · -- `v ≠ dst`: the op writes `ρ dst ≠ ρ v` (injectivity), leaving `ρ v` alone.
    have hvd : ρ v ≠ ρ p.dst := fun h => hv (hρ h)
    rw [GuardedOp.toJInstr_get_other _ _ _ _ _ hvd, hs1_eq,
        JState.get_setReg_other _ _ _ _ hvd]
    simp only [rsSetScalar, beq_eq_false_iff_ne.mpr hv, Bool.false_eq_true, if_false]
    exact hmatch v

/-- The source post-state of `p.toLowCT` under the **real** `RustExec`
    operational semantics: `RustExec.scalarSetExpr` steps
    `RScalarSetExpr p.dst p.toSExpr` to `rsSetScalar rs p.dst (eval …)`. Ties
    `lowerGuarded_denote`'s post-state to the `LowCT` semantics. -/
theorem GuardedSrc.rustExec (N : Nat) (leafSpec : LeafSpec) (p : GuardedSrc)
    (rs : RustState) :
    RustExec N leafSpec p.toLowCT rs
      (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)) :=
  RustExec.scalarSetExpr p.dst p.toSExpr rs

/-- **Denote preservation, against the real `RustExec`.** Combines
    `GuardedSrc.rustExec` (the source step) with `lowerGuarded_denote`:
    for the unique source post-state `rs'` reached by `RustExec` on `p.toLowCT`,
    the machine run of the lowering ends `StateMatch`-related — **under the
    source-value guard** `p.guard rs`. The source-operational-semantics ⇒
    machine-run correspondence the guarded bridge delivers. -/
theorem lowerGuarded_denote_rustExec (N : Nat) (leafSpec : LeafSpec)
    (ρ : RegMap) (p : GuardedSrc) (rs rs' : RustState) (js : JState 64)
    (hρ : Function.Injective ρ) (hwf : p.wf) (hg : p.guard rs)
    (hmatch : StateMatch ρ rs js)
    (hexec : RustExec N leafSpec p.toLowCT rs rs') :
    StateMatch ρ rs' (runBlock js (lowerGuarded ρ p)) := by
  cases hexec
  exact lowerGuarded_denote ρ p rs js hρ hwf hg hmatch

/-! ## 7. Source CT ⇒ machine CT, end to end

`lowerGuarded_source_to_machine_CT`: a guarded source command whose `cmdCT`
result is `true` lowers to a machine block that is constant-time. As in the
homomorphic case the `cmdCT` hypothesis is consumed only on the source side —
machine CT is unconditional for this memory-free fragment, and (separately) it
does **not** depend on the value guard. The statement records the intended
contract: a CT-accepted guarded source command compiles to CT machine code. -/

/-- **Source CT result ⇒ machine constant-time.** If the guarded source command
    `p.toLowCT` passes the real source CT analyser `cmdCT`, its lowering is
    constant-time at the machine level (same leakage trace from any two states).
    Independent of the value guard `p.guard`. -/
theorem lowerGuarded_source_to_machine_CT (ρ : RegMap) (p : GuardedSrc)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (_hsrc : cmdCT p.toLowCT lt leafCT = true) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerGuarded ρ p) = blockLeak s₂ (lowerGuarded ρ p) :=
  lowerGuarded_constant_time ρ p s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTGuardedCT
