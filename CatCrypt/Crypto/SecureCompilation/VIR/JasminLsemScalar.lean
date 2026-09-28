/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-!
# Widening the unconditional `correct ∧ robust` simulation to the uniform-width
# scalar op set — increment 4 of porting jasmin's `lsem`

Increments 1–3 (`JasminLsem`/`JasminLsemSimulation`/`JasminLsemRobust`) built the
straight-line linear machine and proved, **unconditionally**, a functional ∧
constant-time simulation for the `regArith`-only straight-line fragment
(`owned_lsem_correct_and_robust_straightline`). `Com jasminDialect` is
straight-line SSA (no control flow), so the remaining coverage axis at fixed
width is the **op set**: which `JasminOp`s of one binding the linear machine
models faithfully.

This module is **increment 4**: it widens that fragment from `regArith`-only to
the **uniform-width scalar op set** `regArith ∪ regConst`, and re-proves the
functional simulation, the leak state-independence, and the unconditional
capstone over the widened fragment
(`owned_lsem_correct_and_robust_scalar`). Increments 1–3 are left intact; the
widened predicate `UniformScalarArith` *subsumes* `UniformRegArith`
(`UniformScalarArith.of_regArith`), so every increment-3 result remains a
special case.

## What is in scope (and why), at uniform single width

The linear machine `Lstate w` is single-width (`String → BitVec w`), so a
binding is faithfully modelable here exactly when **all its operands and its
result have type `.reg w`** and the linear step computes its denotation with no
control flow and no value-dependent addressing.

* **`regArith bop w`** — `[reg w, reg w] → reg w`, binary register arithmetic.
  Already covered by increment 2/3; re-exposed here as a `UniformScalarArith`
  arm.
* **`regConst w n`** — `[] → reg w`, nullary materialisation of the compile-time
  literal `n`. `opToLinstrR` lowers it to `Lopn [.reg dst] (MOV-tagged) [.imm n]`
  — the immediate rides in the **operand** `.imm n`, which `evalOperand`
  evaluates to `BitVec.ofNat w n = (regConst w n).denote`, and the existing
  `applyOpn "MOV" [a] = some a` arm computes it. No control flow, no register
  read (the only source is the public compile-time immediate), so it is uniform
  width, value-deterministic, and its leak (`LLeak.opn "MOV" [reg dst]
  [imm n]`) carries only the public constant — never a register value.

This widens the op set of the unconditional simulation: `regConst` is the first
non-`regArith` op (a nullary constant materialiser) in the functional ∧
constant-time `lsem` simulation, with no new hypothesis and no `jasminc`/IR→x86
edge.

## Deferred ops and the technical reason for each

The remaining `JasminOp`s are outside this module's scope; each hits a concrete
obstruction against the single-width `Lstate w` model:

* **Non-uniform width** — break the single-width store, so they need a
  multi-width store model:
  - `select w`   — its condition operand is `.reg 1` (a 1-bit register), while
    the data operands/result are `.reg w`. A single-width store cannot hold a
    `BitVec 1` cond and a `BitVec w` datum at once. (The intended CT leak
    — leak the cond *register name*, never its value — is exactly what the
    multi-width leak arm will do; `linstrLeak` already leaks only `regShape`.)
  - `stackLoad w n` / `stackStore w n` — operate on `.stackArr w n` (a function
    type, not `BitVec w`) with a `.reg 64` index; `stackStore` even *returns* a
    `.stackArr w n`. The single-`BitVec w` store has no array cell, and the
    index is width 64 ≠ w. Needs the memory/array + multi-width increment.
  - `castW w w'` (`w ≠ w'`)  — input `.reg w`, output `.reg w'`; it changes
    the width.
  - `mulhi` / `addCarryLo` / `addCarryHi` — double-width / flag-coupled
    (`addCarryHi` returns `.reg 1`); the carry thread is width 1.
* **Immediate baked into the opcode mnemonic** — `rorImm w n` / `shrImm w n` /
  `sarImm w n` / `shlImm w n` are `[reg w] → reg w` (uniform width!), but
  `opToLinstrR` encodes the shift amount **in the opcode string**
  (`withWidthTag w ("SHR:" ++ toString n)` etc.), *not* in an operand. A
  faithful `lsemStep` sees only the `LinstrR`, so it would have to recover `n`
  by parsing `toString n` back out of the mnemonic — i.e. it needs
  `(toString n).toNat? = some n`, which has **no Lean/Mathlib round-trip lemma**
  and is **not** closable by `decide` for symbolic `n` (verified: `simp`
  reduces `toString n` to `n.repr` and stalls; `decide` rejects the free
  variable). Recovering the immediate is therefore the obstruction, not the
  width — deferred until a structured-immediate `LinstrR` (or an operand-carried
  shift amount) removes the string round-trip. (Contrast `regConst`, whose
  immediate rides in the `.imm` *operand*, so no parsing is needed.)
* **Opaque / vector / multi-result** — `extCall` (its meaning *is* the carried
  ABI leaf — opaque by design), `vpackZMM` (`.reg 512` SIMD lane vector),
  `callN` (multi-result call).

## Fidelity (trust-critical)

`regConst`'s `lsemStep` arm is the **same** `Lopn` arm of increment 1 (faithful
to Coq `eval_instr`'s `Lopn`): evaluate the source operands, run `exec_sopn`
(here the modeled `applyOpn "MOV"`), write the destination, advance the pc. Its
leak arm is increment 3's `linstrLeak` — a single `LLeak.opn` carrying the
opcode + operand *structure* (`reg dst`, `imm n`), reading **no** register value,
matching `MachineConstantTime.instrLeak`'s structural-only leak.

**All goals closed, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`.** The `lsem→bytes` encoder and Sail tables remain the
declared trusted base, as for every verified compiler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-! ## 1. The width tag round-trips on the `MOV` mnemonic

`regConst` lowers to `withWidthTag w "MOV"`, and `lsemStep` strips the tag before
`applyOpn`. The round-trip recovers the bare `"MOV"`, by kernel evaluation of the
concrete `String.endsWith` per width branch (same shape as
`stripWidthTag_withWidthTag_binOpName`). -/

/-- The width tag round-trips on the `MOV` mnemonic: `lsemStep` recovers `"MOV"`
    from the tagged mnemonic `opToLinstrR` emits for a `regConst`. -/
theorem stripWidthTag_withWidthTag_MOV (w : Nat) :
    stripWidthTag (withWidthTag w "MOV") = "MOV" := by
  unfold withWidthTag
  split <;> decide +kernel

/-! ## 2. The widened source predicate `UniformScalarArith`

Every binding is either a binary `regArith bop w` or a nullary `regConst w n`
over the uniform `.reg w` context, and the program returns a register. This
*subsumes* `UniformRegArith` (the `regArith`-only fragment of increments 2/3). -/

/-- The straight-line **uniform-width scalar** fragment: every binding is either
    a binary `regArith bop w` or a nullary `regConst w n` over the uniform
    context, and the program returns a register. Generalises
    `UniformRegArith` (which is the `regArith`-only sub-fragment). -/
inductive UniformScalarArith (w : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (.reg w)) :
      UniformScalarArith w (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : UniformScalarArith w body) :
      UniformScalarArith w (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | const {Γ : Ctxt jasminDialect} {s : JasminTy} (n : Nat)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : UniformScalarArith w body) :
      UniformScalarArith w (.var ⟨JasminOp.regConst w n, heq, args⟩ body)

/-- `UniformScalarArith` subsumes `UniformRegArith`: every `regArith`-only
    straight-line program is in the widened fragment. So every increment-3
    result is a special case of the increment-4 results below. -/
theorem UniformScalarArith.of_regArith {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (h : UniformRegArith w com) :
    UniformScalarArith w com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq args _ ih => exact .var bop heq args ih

/-- A uniform-scalar program returns a register: its result type is `.reg w`. -/
theorem UniformScalarArith.ret_ty {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformScalarArith w com) : t = .reg w := by
  induction hcom with
  | ret v => rfl
  | var _ _ _ _ ih => exact ih
  | const _ _ _ _ ih => exact ih

/-! ## 3. Per-op agreement for the `regConst` binding

A `regConst w n` binding lowers to `Lopn [.reg dst] (withWidthTag w "MOV")
[.imm n]` (the `srcs` argument is ignored by `opToLinstrR`'s `regConst` arm —
the immediate rides in the operand). `lsemStep` strips the tag, evaluates the
`.imm n` operand to `BitVec.ofNat w n`, and the `applyOpn "MOV" [a] = some a` arm
returns it — exactly `(regConst w n).denote`. -/

/-- The per-binding step for a `regConst` binding: from any store, `lsemStep`s to
    the state that writes `e.denote V = BitVec.ofNat w n` to `regName curDepth`
    and advances the pc. This is the `Lopn` arm of `eval_instr` computing the
    constant. (No `StoreAgrees` hypothesis is needed: a nullary const reads no
    operand register.) -/
theorem lsemStep_const {w nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : Lstate w}
    (n : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n))) :
    lsemStep
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  -- `opToLinstrR (regConst …)` hardcodes the source list `[.imm n]`, so the
  -- `exprArgs` (which is `[]`) is irrelevant.
  simp only [opToLinstrR, lsemStep, List.map_cons, List.map_nil,
    stripWidthTag_withWidthTag_MOV, evalOperand, applyOpn]
  -- LHS: `some (st.setReg … (BitVec.ofNat w n)).nextPc`; RHS denote is the same.
  rfl

/-! ## 4. The core straight-line simulation over `UniformScalarArith`

Same induction skeleton as increment 2's `lsemStraight_straightOps`, with the new
`const` arm closed by `lsemStep_const` + `StoreAgrees.step`. -/

/-- **Core simulation (parametrized by an agreeing start state), widened.** From
    any store `s` agreeing with `V` at depth `curDepth` (`Γ.length = curDepth`,
    `nArgs ≤ curDepth`), running the widened `.var`-chain `straightOps` succeeds,
    lands in a store agreeing with the binding-extended valuation, and reads
    `Com.denote com V` at the return register. -/
theorem lsemStraight_straightOps_scalar {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : UniformScalarArith w com) :
    ∀ {nArgs curDepth : Nat} {st : Lstate w} {V : Ctxt.Valuation Γ},
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgrees w nArgs curDepth st V →
      ∃ st', lsemStraight (straightOps nArgs com curDepth) st = some st' ∧
        evalOperand st' (.reg (comRetReg nArgs argName com curDepth)) =
          (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth st V hlen harg hagree
      refine ⟨st, rfl, ?_⟩
      have key : resolveVar curDepth nArgs argName (fun _ => none) v
          = LOperand.reg (comRetReg nArgs argName (Com.ret v) curDepth) := by
        simp only [comRetReg, resolveVar]
        split <;> rfl
      rw [← key]; exact hagree v rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      set val : BitVec w :=
        (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect _ (.reg w)).denote V with hval
      have hstep := lsemStep_var (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        bop heq args hagree
      have hagree' : StoreAgrees w nArgs (curDepth + 1)
          ((st.setReg (regName curDepth) val).nextPc) (V.extend (t := JasminTy.reg w) val) :=
        StoreAgrees.step val hlen harg hagree
      obtain ⟨st', hrun, hret⟩ :=
        ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · simp only [straightOps, lsemStraight_cons, hstep]
        exact hrun
      · simp only [comRetReg]
        rw [hret]
        rfl
  | const n heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      set val : BitVec w :=
        (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect _ (.reg w)).denote V with hval
      have hstep := lsemStep_const (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        n heq args
      have hagree' : StoreAgrees w nArgs (curDepth + 1)
          ((st.setReg (regName curDepth) val).nextPc) (V.extend (t := JasminTy.reg w) val) :=
        StoreAgrees.step val hlen harg hagree
      obtain ⟨st', hrun, hret⟩ :=
        ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · simp only [straightOps, lsemStraight_cons, hstep]
        exact hrun
      · simp only [comRetReg]
        rw [hret]
        rfl

/-! ## 5. The widened straight-line faithfulness theorem -/

/-- **Straight-line linearizer simulation, widened to the scalar op set.** For a
    uniform-width scalar straight-line `Com`, running the linearizer-emitted
    `.var`-chain `straightOps` from the encoded argument valuation and decoding
    the result register equals the source program's `Com.denote`. -/
theorem comToLprog_lsem_scalar {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformScalarArith w com)
    (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraight (straightOps Γ.length com Γ.length) (encode V) = some st' ∧
      decode st' (comRetReg Γ.length argName com Γ.length) =
        (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraight_straightOps_scalar hcom (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encode V) (V := V) rfl le_rfl (encode_StoreAgrees hu V)
  exact ⟨st', hrun, by rw [decode_eq_evalOperand]; exact hret⟩

/-- **Faithfulness (packaged), widened.** The widened straight-line body, run on
    the encoded inputs and decoded at the result register, equals the source
    denotation. -/
theorem comToLprog_faithful_scalar {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : UniformScalarArith w com)
    (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) :
    (lsemStraight (straightOps Γ.length com Γ.length) (encode V)).map
        (fun st' => decode st' (comRetReg Γ.length argName com Γ.length)) =
      some (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsem_scalar hcom hu V
  rw [hrun, Option.map_some, hdec]

/-! ## 6. The widened leak state-independence

A `regConst` head always `lsemStep`s successfully (its `applyOpn "MOV"` is
total), exactly like a `regArith` head, so the same state-independence induction
goes through for the widened fragment. The per-instruction `linstrLeak` is
unchanged (increment 3) — it reads only the instruction syntax. -/

/-- A `regConst` head always `lsemStep`s successfully, from **any** state: its
    `applyOpn "MOV" [BitVec.ofNat w n]` is total. (The `regConst` analogue of
    `lsemStep_regArith_succeeds`; why the state-independence below needs no
    agreement hypothesis.) -/
theorem lsemStep_const_succeeds {w nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    (n : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (st : Lstate w) :
    ∃ st', lsemStep (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))) st
      = some st' := by
  -- The `regConst` image is `Lopn [.reg dst] (MOV-tagged) [.imm n]`; `lsemStep`
  -- strips the tag and `applyOpn "MOV" [BitVec.ofNat w n]` is total.
  simp only [opToLinstrR, lsemStep, List.map_cons, List.map_nil,
    stripWidthTag_withWidthTag_MOV, evalOperand, applyOpn]
  exact ⟨_, rfl⟩

/-- **Robustness / constant-time main theorem (unconditional), widened.** The
    linear-IR leakage trace of the widened linearizer-emitted `.var`-chain
    `straightOps` is the **same from any two initial states**: every head is an
    `Lopn` whose `linstrLeak` reads only syntax (never `s.lvm`) and `lsemStep`s
    successfully from any state, so both states take the `some` branch and the
    tails are run on the same instruction list — closed by the unconditional IH.
    Widens `lsemLeak_straightOps_state_independent` to `regArith ∪ regConst`. -/
theorem lsemLeak_straightOps_state_independent_scalar {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : UniformScalarArith w com) :
    ∀ {nArgs curDepth : Nat} (s₁ s₂ : Lstate w),
      lsemLeak (straightOps nArgs com curDepth) s₁ =
        lsemLeak (straightOps nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth s₁ s₂
      rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth s₁ s₂
      obtain ⟨t₁, hstep1⟩ := lsemStep_regArith_succeeds (nArgs := nArgs) (curDepth := curDepth)
        bop heq args s₁
      obtain ⟨t₂, hstep2⟩ := lsemStep_regArith_succeeds (nArgs := nArgs) (curDepth := curDepth)
        bop heq args s₂
      simp only [straightOps, lsemLeak_cons, hstep1, hstep2]
      refine congrArg (linstrLeak _ ++ ·) ?_
      exact ih t₁ t₂
  | const n heq args hbody ih =>
      intro nArgs curDepth s₁ s₂
      obtain ⟨t₁, hstep1⟩ := lsemStep_const_succeeds (nArgs := nArgs) (curDepth := curDepth)
        n heq args s₁
      obtain ⟨t₂, hstep2⟩ := lsemStep_const_succeeds (nArgs := nArgs) (curDepth := curDepth)
        n heq args s₂
      simp only [straightOps, lsemLeak_cons, hstep1, hstep2]
      refine congrArg (linstrLeak _ ++ ·) ?_
      exact ih t₁ t₂

/-! ## 7. The unconditional widened capstone: `correct ∧ robust` -/

/-- **Unconditional `correct ∧ robust` for the uniform-width scalar fragment
    (`regArith ∪ regConst`).** For a uniform-width scalar straight-line `Com`:

    1. *(correct)* running the linearizer-emitted `.var`-chain `straightOps` on
       the encoded argument valuation and decoding the result register yields
       exactly `com.denote V`; and
    2. *(robust, syntactic leak model)* the linear-IR leakage trace
       `lsemLeak (straightOps …)` is the **same from any two initial states** —
       the attacker's control-flow + operand-structure view is a function of the
       emitted instruction list alone, never of a register value.

    This is **unconditional**: no IR→x86 faithfulness hypothesis, no
    `jasminc_preserves_ct`. Both conjuncts concern one and the same object — the
    widened linearizer-emitted straight-line body run by `lsemStraight`
    (functional) and observed by `lsemLeak` (CT). The `lsem→bytes` encoder and
    Sail encode/decode tables remain the declared trusted base. Widens
    `owned_lsem_correct_and_robust_straightline` to the scalar op set.

    The leak function reads no register value (an indexed access leaks the index
    register's name, not its value), so conjunct 2 holds for every program of the
    fragment and is not constant-time evidence. Constant-time evidence for emitted
    code is `AllocCTPreservation.toLprogPhysAbi_gather_constant_time` (straight-line
    gathered blocks) and the per-kernel `blockLeak` theorems. -/
theorem owned_lsem_correct_and_robust_scalar {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : UniformScalarArith w com)
    (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (§5)
    ((lsemStraight (straightOps Γ.length com Γ.length) (encode V)).map
        (fun st' => decode st' (comRetReg Γ.length argName com Γ.length)) =
      some (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§6)
    (∀ s₁ s₂ : Lstate w,
      lsemLeak (straightOps Γ.length com Γ.length) s₁ =
        lsemLeak (straightOps Γ.length com Γ.length) s₂) := by
  refine ⟨comToLprog_faithful_scalar hcom hu V, ?_⟩
  intro s₁ s₂
  exact lsemLeak_straightOps_state_independent_scalar hcom s₁ s₂

/-- The increment-3 capstone is a special case of the widened one: every
    `regArith`-only fragment satisfies the scalar capstone. (Sanity tie between
    the two increments; the conclusions coincide because `straightOps`,
    `lsemStraight`, `lsemLeak`, `encode`, `decode` are all op-agnostic.) -/
theorem owned_lsem_correct_and_robust_scalar_of_regArith {w : Nat}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t}
    (hcom : UniformRegArith w com) (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) :
    ((lsemStraight (straightOps Γ.length com Γ.length) (encode V)).map
        (fun st' => decode st' (comRetReg Γ.length argName com Γ.length)) =
      some ((UniformScalarArith.of_regArith hcom).ret_ty ▸ com.denote V :
        ⟦(JasminTy.reg w)⟧))
    ∧
    (∀ s₁ s₂ : Lstate w,
      lsemLeak (straightOps Γ.length com Γ.length) s₁ =
        lsemLeak (straightOps Γ.length com Γ.length) s₂) :=
  owned_lsem_correct_and_robust_scalar (UniformScalarArith.of_regArith hcom) hu V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar
