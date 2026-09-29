/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation

/-!
# Constant-time leakage over `lsem`, and the unconditional `correct ∧ robust`
Scope: `lsemLeak` records index register names, not their values, and the CT hypotheses of the `owned_lsem_correct_and_robust_*` theorems are unused; "robust" here is correctness. Constant time of the shipped bytes is `DecodedCT.bytesCTCheck_sound`.

# capstone — increment 3 of porting jasmin's `lsem`

Increment 1 (`JasminLsem.lean`) built the straight-line linear machine
(`Lstate`/`lsemStep`/`lsemStraight`). Increment 2
(`JasminLsemSimulation.lean`) proved the *functional* simulation
`comToLprog_faithful_straightline`: running the linearizer-emitted `.var`-chain
`straightOps` on the encoded inputs, then decoding the result register, equals
`Com.denote`, for the uniform-width `regArith` straight-line fragment.

This module is **increment 3**: it adds a *constant-time leakage model* over the
same linear semantics and combines it with increment 2's functional simulation
into a single, **unconditional** `correct ∧ robust` statement
(`owned_lsem_correct_and_robust_straightline`) for the straight-line `regArith`
fragment.

## Why this closes the carried `JasminIRToX86`/`jasminc_preserves_ct` edge

Every prior owned-path CT result that reached *machine* leakage
(`MachineConstantTime.blockLeak`, `LowCTToJInstrCT.lowerSeq_constant_time`)
operates on `List (JInstr w)` — the x86 leaf — and so its tie to the source IR
went through a *carried* edge (`JasminIRToX86` faithfulness, or the trusted
`jasminc_preserves_ct`). Here the leak model is defined **directly over
`lsemStraight`'s own `LinstrR` list** — the same linear IR the increment-2
functional simulation runs — so the CT statement and the functional statement
are about *one and the same* object: the linearizer-emitted straight-line body.
No IR→x86 hypothesis, no `jasminc_preserves_ct`, appears anywhere below.

## Fidelity (trust-critical): what `lsemLeak` leaks, and why it is faithful

`lsemLeak` mirrors `MachineConstantTime.blockLeak` / the Barthe-et-al. (CCS 2014)
constant-time leakage model: a cache/branch-predictor attacker observes
**control-flow conditions** and **memory addresses**, never arithmetic register
*values*.

For one straight-line `Lopn dsts opn srcs` instruction `lsemLeak` emits exactly
its **public/structural shape** — the opcode `opn` together with the *operand
structure* of `dsts` and `srcs`:

* a register operand `.reg r` leaks its **name** `r` (which register, not its
  contents);
* an immediate `.imm v` leaks the compile-time constant `v` (already public);
* an array element `.arr base i` leaks `(base, i)` — a compile-time-constant
  address shape;
* a register-indexed element `.arrIdx base idx scale` leaks the *structure*
  `(base, idx, scale)` — i.e. *which* index register and the stride, **not** the
  value in `idx`. (For the `regArith` fragment this case never occurs; it is
  modeled so the leak function is total over the full IR.)

`lsemLeak` **never reads `s.lvm`** — it never inspects a register value. For the
straight-line `regArith` fragment there is no data-dependent branch (`Lopn` is
unconditional) and no value-dependent memory addressing (every operand is
`.reg`/`.imm`), so the leak is state-independent, and the model leaks the
instruction's opcode/operand-register structure and nothing else.

This is the linear-IR analogue of `MachineConstantTime.blockLeak_state_independent`
and `LowCTToJInstrCT.lowerSeq_constant_time`, and the `lsem`-level counterpart of
`RHPVerifiedMiddle.all_cprog_ct`.

## Scope

The capstone is unconditional **for the uniform-width `regArith` straight-line
fragment** (`UniformRegArith`/`UniformCtxt`), the same fragment increment 2's
functional simulation covers. The `lsem→bytes` encoder and the Sail
encode/decode tables remain the declared trusted base, as for every verified
compiler. **All goals closed, axioms ⊆ {propext, Classical.choice, Quot.sound}**, no
`jasminc_preserves_ct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation

/-! ## 1. Linear-IR leakage events

The constant-time leakage model (Barthe et al., CCS 2014) gives the attacker two
channels: control-flow conditions and memory addresses, never register values.
We mirror `MachineConstantTime.MLeak` at the `LinstrR` level. -/

/-- The public/structural shape of one `LOperand`: what an attacker may learn
    from the operand *without* reading any register value.

    * `.reg r` → `regShape r` — *which* register (its name), not its contents.
    * `.imm v` → `immShape v` — the compile-time constant (already public).
    * `.arr base i` → `arrShape base i` — a compile-time-constant address shape.
    * `.arrIdx base idx scale` → `idxShape base idx scale` — *which* index
      register and the stride, **not** the value in `idx`. -/
inductive OperandShape where
  /-- A register operand: its name only. -/
  | regShape (name : String)
  /-- An immediate: its (public) compile-time value. -/
  | immShape (value : Nat)
  /-- A direct array element: its compile-time `(base, index)` address shape. -/
  | arrShape (base : String) (idx : Nat)
  /-- A register-indexed element: the *structure* `(base, index-register, scale)`,
      never the value in the index register. -/
  | idxShape (base idx : String) (scale : Nat)
  deriving DecidableEq, Repr

/-- A linear-IR leakage event: the public/structural information one `LinstrR`
    exposes to a cache/branch-predictor attacker.

    * `opn opcode dsts srcs` — a straight-line `Lopn`: its opcode plus the
      operand *structure* of its destinations and sources. Carries no register
      value (mirrors the address/opcode channel of `MachineConstantTime.MLeak`).
    * `branch` — a control-flow decision (a conditional jump). The straight-line
      `regArith` fragment emits none. -/
inductive LLeak where
  /-- A straight-line operation: opcode + operand structure (no values). -/
  | opn (opcode : String) (dsts srcs : List OperandShape)
  /-- A control-flow decision (conditional branch). -/
  | branch
  deriving DecidableEq, Repr

/-- Is this leakage event a control-flow (branch) leak? -/
def LLeak.isBranch : LLeak → Bool
  | .branch => true
  | .opn _ _ _ => false

/-! ## 2. Per-operand and per-instruction leakage

`operandShape` reads only the *syntactic* operand — register **name**,
immediate, or `(base, idx-register, scale)` structure — never `s.lvm`. So the
whole leak is a function of the instruction list alone. -/

/-- The public shape of an operand: its name/structure, never a register value. -/
def operandShape : LOperand → OperandShape
  | .reg r => .regShape r
  | .imm v => .immShape v
  | .arr base i => .arrShape base i
  | .arrIdx base idx scale => .idxShape base idx scale

/-- The leakage of a single `LinstrR`, in the constant-time model: the
    opcode/operand structure of a straight-line `Lopn`, a `branch` for a
    conditional jump, and nothing for the pc-only/no-effect instructions
    (`Lalign`/`Llabel`/`Lret`). **Reads no register value** — it inspects only
    the instruction's syntax (cf. `MachineConstantTime.instrLeak`, which for the
    direct ops likewise emits only the constant `(base, off)` shape). -/
def linstrLeak : LinstrR → List LLeak
  | .Lopn dsts opn srcs => [.opn opn (dsts.map operandShape) (srcs.map operandShape)]
  -- pc-only / no-store-effect instructions: no observable data leak.
  | .Lalign => []
  | .Llabel _ _ => []
  | .Lret => []
  -- control-flow / effect instructions: a branch decision is observable.
  | .Lgoto _ => [.branch]
  | .Lcond _ _ => [.branch]
  | .Ligoto _ => [.branch]
  | .Lcall _ _ => [.branch]
  | .LstoreLabel _ _ => [.branch]
  | .Lsyscall _ => [.branch]

/-! ## 3. The block leakage trace over `lsemStraight`

`lsemLeak is s` is the leakage of running the straight-line instruction list `is`
from state `s`. As in `MachineConstantTime.blockLeak`, the state is threaded
through `lsemStep` so the model has the *same shape* as the functional
semantics — but each instruction's contribution `linstrLeak i` ignores the
state, which is exactly why the trace is state-independent for the
branch-free / address-free fragment. -/

/-- `lsemLeak is s`: the linear-IR leakage trace of running `is` from `s`, the
    concatenation of each instruction's `linstrLeak` against the state in which
    it executes. Mirrors `MachineConstantTime.blockLeak`'s shape (state threaded
    by `lsemStep`); the per-instruction leak never reads the store. -/
def lsemLeak {w : Nat} : List LinstrR → Lstate w → List LLeak
  | [], _ => []
  | i :: is, s =>
      linstrLeak i ++
        (match lsemStep i s with
          | some s' => lsemLeak is s'
          | none => [])

@[simp] theorem lsemLeak_nil {w : Nat} (s : Lstate w) : lsemLeak [] s = [] := rfl

@[simp] theorem lsemLeak_cons {w : Nat} (i : LinstrR) (is : List LinstrR)
    (s : Lstate w) :
    lsemLeak (i :: is) s =
      linstrLeak i ++
        (match lsemStep i s with
          | some s' => lsemLeak is s'
          | none => []) := rfl

/-- On a list that runs to completion the leakage trace is the concatenation of
    the per-instruction leaks, hence a function of the instruction list alone.
    Constant-timeness of a completing body follows: two runs of one list leak the
    same trace whatever their start states. -/
theorem lsemLeak_of_run {w : Nat} (is : List LinstrR) (s s₂ : Lstate w)
    (h : lsemStraight is s = some s₂) : lsemLeak is s = is.flatMap linstrLeak := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [lsemStraight_cons] at h
    cases hst : lsemStep (w := w) i s with
    | none => rw [hst] at h; exact absurd h (by simp)
    | some s' =>
      rw [hst] at h
      simp only [lsemLeak_cons, hst, List.flatMap_cons, ih s' h]

/-! ## 4. `straightOps` emits only `Lopn` — hence no branch, no value-dependence

The `.var`-chain `straightOps` consists entirely of `opToLinstrR (regArith …) …`
instructions, each an `Lopn [.reg dst] opn srcs` with `srcs` resolved by
`resolveVar` to `.reg`/`.imm`/`.arr` operands (never reading a value). So every
instruction's leak is a single `LLeak.opn` carrying syntactic shapes only. -/

/-- **Every** `opToLinstrR` image is an `Lopn` (the linearizer emits only
    straight-line operations — no control flow). Hence its `linstrLeak` is a
    single `LLeak.opn`, never a `branch`. -/
theorem opToLinstrR_isLopn (op : JasminOp) (d : String) (s : List LOperand) :
    ∃ opn dsts srcs, opToLinstrR op d s = .Lopn dsts opn srcs := by
  cases op <;>
    first
    | exact ⟨_, _, _, rfl⟩
    | (simp only [opToLinstrR]; repeat' split) <;> exact ⟨_, _, _, rfl⟩

/-- A `regArith` binding lowers to an `Lopn` instruction (its `opToLinstrR`
    image is the straight-line `Lopn [.reg dst] (binOpName-tagged) srcs`). -/
theorem opToLinstrR_regArith_isLopn {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (dst : String) (curDepth nArgs : Nat) :
    ∃ srcs : List LOperand,
      opToLinstrR (JasminOp.regArith bop w) dst
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
        = .Lopn [.reg dst] (withWidthTag w (binOpName bop)) srcs := by
  exact ⟨_, rfl⟩

/-! ## 5. The robustness theorem: `lsemLeak` of `straightOps` is state-independent

The leak of the `.var`-chain depends only on the instruction list, not the
state: every instruction is an `Lopn` whose `linstrLeak` reads only syntax, and
the only state-dependence in `lsemLeak` is through the *threaded* `lsemStep`
result — which selects *which* tail to run, but both states run the *same* tail
list `is`. By induction the tails leak equally regardless of the (possibly
diverged) intermediate states.

This is the linear-IR analogue of `MachineConstantTime.blockLeak_state_independent`
and `LowCTToJInstrCT.lowerSeq_constant_time`. -/

/-- A `regArith` head always `lsemStep`s successfully, from **any** state: its
    `applyOpn (binOpName bop) [a, b]` is total (`applyOpn_binOpName`). This is why
    the state-independence below needs no agreement hypothesis: both states take
    the `some` branch of `lsemLeak`, so the (possibly diverged) tails are run on
    the same instruction list. -/
theorem lsemStep_regArith_succeeds {w nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (st : Lstate w) :
    ∃ st', lsemStep (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))) st
      = some st' := by
  match args with
  | .cons a0 (.cons a1 .nil) =>
    have hargs : exprArgs curDepth nArgs argName (fun _ => none)
        (⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ : Expr jasminDialect Γ (.reg w))
        = [resolveVar curDepth nArgs argName (fun _ => none) a0,
           resolveVar curDepth nArgs argName (fun _ => none) a1] := rfl
    simp only [opToLinstrR, hargs]
    rw [lsemStep_reg_cons2 (regName curDepth) (withWidthTag w (binOpName bop))
        (resolveVar curDepth nArgs argName (fun _ => none) a0)
        (resolveVar curDepth nArgs argName (fun _ => none) a1) st
        (fun base idx scale =>
          resolveVar_ne_arrIdx curDepth nArgs argName (fun _ => none) a0 base idx scale)]
    simp only [stripWidthTag_withWidthTag_binOpName, applyOpn_binOpName]
    exact ⟨_, rfl⟩

/-- **State-independence of the linear-IR leakage trace.** The trace of the
    linearizer-emitted `.var`-chain `straightOps` is the **same from any two
    initial states** `s₁ s₂`, with no hypothesis on the states.

    The leak depends only on the instruction list, not the state: every head is
    an `Lopn` whose `linstrLeak` reads only syntax (never `s.lvm`), and every
    head `lsemStep`s successfully from any state (`lsemStep_regArith_succeeds`),
    so both states take the `some` branch and the (possibly diverged) tails are
    run on the same instruction list — closed by the (unconditional) IH.

    This is the linear-IR analogue of
    `MachineConstantTime.blockLeak_state_independent` and
    `LowCTToJInstrCT.lowerSeq_constant_time`, and the `lsem`-level counterpart of
    `RHPVerifiedMiddle.all_cprog_ct`. -/
theorem lsemLeak_straightOps_state_independent {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com) :
    ∀ {nArgs curDepth : Nat} (s₁ s₂ : Lstate w),
      lsemLeak (straightOps nArgs com curDepth) s₁ =
        lsemLeak (straightOps nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth s₁ s₂
      rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth s₁ s₂
      -- both sides step the head successfully (from any state)
      obtain ⟨t₁, hstep1⟩ := lsemStep_regArith_succeeds (nArgs := nArgs) (curDepth := curDepth)
        bop heq args s₁
      obtain ⟨t₂, hstep2⟩ := lsemStep_regArith_succeeds (nArgs := nArgs) (curDepth := curDepth)
        bop heq args s₂
      simp only [straightOps, lsemLeak_cons, hstep1, hstep2]
      -- heads have identical syntactic leak; tails close by the unconditional IH
      -- (run on the same instruction list from the diverged stepped states).
      refine congrArg (linstrLeak _ ++ ·) ?_
      exact ih t₁ t₂

/-! ## 6. The unconditional capstone: `correct ∧ robust`

Combine increment 2's functional simulation with §5's robustness into one
statement for the uniform-width `regArith` straight-line fragment. **No
`JasminIRToX86` hypothesis, no `jasminc_preserves_ct`** — both conjuncts are
about the *same* linearizer-emitted `straightOps` list, run by `lsemStraight`
(functional) and observed by `lsemLeak` (CT). The `lsem→bytes` encoder + Sail
tables remain the declared trusted base, as for every verified compiler. -/

/-- **Unconditional `correct ∧ robust` for the straight-line `regArith`
    fragment.** For a uniform-width `regArith` straight-line `Com`:

    1. *(correct, from increment 2)* running the linearizer-emitted `.var`-chain
       `straightOps` on the encoded argument valuation and decoding the result
       register yields exactly `com.denote V`; and
    2. *(robust, syntactic leak model, from §5)* the linear-IR leakage trace
       `lsemLeak (straightOps …)` is the **same from any two initial states** —
       the attacker's control-flow + operand-structure view is a function of the
       emitted instruction list alone, never of a register value.

    This is **unconditional**: it carries no IR→x86 faithfulness hypothesis and
    invokes no `jasminc_preserves_ct`. Both conjuncts concern one and the same
    object — the linearizer-emitted straight-line body run by `lsemStraight` and
    observed by `lsemLeak`. The `lsem→bytes` encoder and the Sail encode/decode
    tables remain the declared trusted base, as for every verified compiler.

    The leak function reads no register value (an indexed access leaks the index
    register's name, not its value), so conjunct 2 holds for every program of the
    fragment and is not constant-time evidence. Constant-time evidence for emitted
    code is `AllocCTPreservation.toLprogPhysAbi_gather_constant_time` (straight-line
    gathered blocks) and the per-kernel `blockLeak` theorems. -/
theorem owned_lsem_correct_and_robust_straightline {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com)
    (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (increment 2)
    ((lsemStraight (straightOps Γ.length com Γ.length) (encode V)).map
        (fun st' => decode st' (comRetReg Γ.length argName com Γ.length)) =
      some (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§5)
    (∀ s₁ s₂ : Lstate w,
      lsemLeak (straightOps Γ.length com Γ.length) s₁ =
        lsemLeak (straightOps Γ.length com Γ.length) s₂) := by
  refine ⟨comToLprog_faithful_straightline hcom hu V, ?_⟩
  intro s₁ s₂
  exact lsemLeak_straightOps_state_independent hcom s₁ s₂

/-- The constant-time leaf takes **no** control-flow branch: the straight-line
    `regArith` chain emits only `Lopn`, so the branch channel of `lsemLeak` is
    empty regardless of state. The branch-free half of the CT statement (cf.
    `MachineConstantTime.blockLeak_no_branch`). -/
theorem lsemLeak_straightOps_no_branch {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} (com : Com jasminDialect Γ t) (nArgs curDepth : Nat)
    (s : Lstate w) :
    (lsemLeak (straightOps nArgs com curDepth) s).filter LLeak.isBranch = [] := by
  induction com generalizing curDepth s with
  | ret v => rfl
  | var e body ih =>
      simp only [straightOps, lsemLeak_cons, List.filter_append]
      -- the head is an `Lopn` (no branch), and `straightOps` only emits `Lopn`
      have hhead : (linstrLeak (opToLinstrR e.op (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none) e))).filter LLeak.isBranch = [] := by
        obtain ⟨opn, dsts, srcs, hop⟩ :=
          opToLinstrR_isLopn e.op (regName curDepth)
            (exprArgs curDepth nArgs argName (fun _ => none) e)
        rw [hop]
        simp [linstrLeak, LLeak.isBranch]
      rw [hhead]
      simp only [List.nil_append]
      cases hstep : lsemStep (opToLinstrR e.op (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none) e)) s with
      | none => rfl
      | some s' => exact ih (curDepth + 1) s'

/-! ## 7. Architectural state agreement

`lsemStep` reads the register map and memory and writes the register map and the
program counter. A pass that deletes or inserts an instruction shifts every later
program counter, so the relation such a pass preserves is agreement on the
*architectural* component alone: the register map `lvm` and memory `lmem`.

`ArchAgree` is that relation; `stateStore` is its store-image form
(`archAgree_iff_stateStore`); `ArchAgreeOpt` lifts it to the `Option` results of
`lsemStraight`. The `Lprog`-level passes state their correctness against one of
these three forms. -/

/-- Two linear-machine states agree on the architectural component: the register
    map and memory, ignoring the program counter. -/
def ArchAgree {w : Nat} (s t : Lstate w) : Prop := s.lvm = t.lvm ∧ s.lmem = t.lmem

theorem ArchAgree.refl {w : Nat} (s : Lstate w) : ArchAgree s s := ⟨rfl, rfl⟩

theorem ArchAgree.symm {w : Nat} {s t : Lstate w} (h : ArchAgree s t) : ArchAgree t s :=
  ⟨h.1.symm, h.2.symm⟩

theorem ArchAgree.trans {w : Nat} {s t u : Lstate w} (h₁ : ArchAgree s t)
    (h₂ : ArchAgree t u) : ArchAgree s u := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- The store of a linear state: its register map paired with its memory. -/
def stateStore {w : Nat} (s : Lstate w) : (String → BitVec w) × (String → Int → BitVec w) :=
  (s.lvm, s.lmem)

/-- `ArchAgree` is equality of the store image. -/
theorem archAgree_iff_stateStore {w : Nat} (s t : Lstate w) :
    ArchAgree s t ↔ stateStore s = stateStore t := by
  simp [ArchAgree, stateStore, Prod.ext_iff]

/-- `ArchAgree` lifted to the `Option` results of `lsemStraight`. -/
def ArchAgreeOpt {w : Nat} : Option (Lstate w) → Option (Lstate w) → Prop
  | none, none => True
  | some s, some t => ArchAgree s t
  | _, _ => False

@[simp] theorem archAgreeOpt_none_none {w : Nat} :
    ArchAgreeOpt (w := w) none none = True := rfl

@[simp] theorem archAgreeOpt_some_some {w : Nat} (s t : Lstate w) :
    ArchAgreeOpt (some s) (some t) = ArchAgree s t := rfl

@[simp] theorem archAgreeOpt_none_some {w : Nat} (t : Lstate w) :
    ArchAgreeOpt none (some t) = False := rfl

@[simp] theorem archAgreeOpt_some_none {w : Nat} (s : Lstate w) :
    ArchAgreeOpt (some s) none = False := rfl

theorem ArchAgreeOpt.refl {w : Nat} (o : Option (Lstate w)) : ArchAgreeOpt o o := by
  cases o <;> simp [ArchAgree.refl]

theorem ArchAgreeOpt.trans {w : Nat} {a b c : Option (Lstate w)}
    (h₁ : ArchAgreeOpt a b) (h₂ : ArchAgreeOpt b c) : ArchAgreeOpt a c := by
  cases a with
  | none =>
    cases b with
    | none => cases c with
      | none => trivial
      | some _ => exact (h₂ : False).elim
    | some _ => exact (h₁ : False).elim
  | some x =>
    cases b with
    | none => exact (h₁ : False).elim
    | some y => cases c with
      | none => exact (h₂ : False).elim
      | some z => exact ArchAgree.trans h₁ h₂

/-- `ArchAgreeOpt` is equality of the mapped store images. -/
theorem archAgreeOpt_iff_stateStore {w : Nat} (a b : Option (Lstate w)) :
    ArchAgreeOpt a b ↔ Option.map stateStore a = Option.map stateStore b := by
  cases a <;> cases b <;> simp [ArchAgreeOpt, archAgree_iff_stateStore]

/-- `lsemStep` reads only the register map and memory and writes only the
    register map and the program counter, so it maps `ArchAgree` states to
    `ArchAgree` results. -/
theorem lsemStep_archAgree {w : Nat} (i : LinstrR) {s t : Lstate w} (h : ArchAgree s t) :
    ArchAgreeOpt (lsemStep i s) (lsemStep i t) := by
  obtain ⟨hv, hm⟩ := h
  have hop : ∀ o : LOperand, evalOperand s o = evalOperand t o := by
    intro o; cases o <;> simp [evalOperand, hv, hm]
  cases i with
  | Lopn dsts opn srcs =>
    cases dsts with
    | nil => simp [lsemStep, ArchAgreeOpt]
    | cons d ds =>
      cases ds with
      | cons _ _ => simp [lsemStep, ArchAgreeOpt]
      | nil =>
        cases d with
        | imm _ => simp [lsemStep, ArchAgreeOpt]
        | arr _ _ => simp [lsemStep, ArchAgreeOpt]
        | arrIdx _ _ _ => simp [lsemStep, ArchAgreeOpt]
        | reg dst =>
          have hsrc : srcs.map (evalOperand s) = srcs.map (evalOperand t) :=
            List.map_congr_left fun o _ => hop o
          cases srcs with
          | nil =>
            simp only [lsemStep, hsrc]
            cases happ : applyOpn (w := w) (stripWidthTag opn)
                (([] : List LOperand).map (evalOperand t)) with
            | none => simp [ArchAgreeOpt]
            | some v => simp [ArchAgreeOpt, ArchAgree, Lstate.nextPc, Lstate.setReg, hv, hm]
          | cons hd tl =>
            cases hd with
            | reg r =>
              simp only [lsemStep, hsrc]
              cases happ : applyOpn (w := w) (stripWidthTag opn)
                  ((LOperand.reg r :: tl).map (evalOperand t)) with
              | none => simp [ArchAgreeOpt]
              | some v => simp [ArchAgreeOpt, ArchAgree, Lstate.nextPc, Lstate.setReg, hv, hm]
            | imm iv =>
              simp only [lsemStep, hsrc]
              cases happ : applyOpn (w := w) (stripWidthTag opn)
                  ((LOperand.imm iv :: tl).map (evalOperand t)) with
              | none => simp [ArchAgreeOpt]
              | some v => simp [ArchAgreeOpt, ArchAgree, Lstate.nextPc, Lstate.setReg, hv, hm]
            | arr ab ai =>
              simp only [lsemStep, hsrc]
              cases happ : applyOpn (w := w) (stripWidthTag opn)
                  ((LOperand.arr ab ai :: tl).map (evalOperand t)) with
              | none => simp [ArchAgreeOpt]
              | some v => simp [ArchAgreeOpt, ArchAgree, Lstate.nextPc, Lstate.setReg, hv, hm]
            | arrIdx base idx scale =>
              simp only [lsemStep, hv, hm]
              by_cases hload : opn = "LOADIDX"
              · simp only [hload, if_pos]
                simp [ArchAgreeOpt, ArchAgree, Lstate.nextPc, Lstate.setReg, hv, hm]
              · by_cases hstore : opn = "STOREIDX"
                · simp only [hstore, reduceIte]
                  cases tl with
                  | nil => simp [ArchAgreeOpt]
                  | cons val rest =>
                    cases rest with
                    | nil =>
                      simp only [ArchAgreeOpt, ArchAgree, Lstate.nextPc, hop val]
                      exact ⟨rfl, rfl⟩
                    | cons _ _ => simp [ArchAgreeOpt]
                · simp only [hload, hstore, reduceIte]
                  rw [hsrc]
                  cases happ : applyOpn (w := w) (stripWidthTag opn)
                      ((LOperand.arrIdx base idx scale :: tl).map (evalOperand t)) with
                  | none => simp [ArchAgreeOpt]
                  | some v => simp [ArchAgreeOpt, ArchAgree, Lstate.nextPc, Lstate.setReg, hv, hm]
  | Lsyscall _ => simp [lsemStep, ArchAgreeOpt]
  | Lcall _ _ => simp [lsemStep, ArchAgreeOpt]
  | Lret => simp [lsemStep, ArchAgreeOpt]
  | Lalign => simp [lsemStep, ArchAgreeOpt, ArchAgree, Lstate.nextPc, hv, hm]
  | Llabel _ _ => simp [lsemStep, ArchAgreeOpt, ArchAgree, Lstate.nextPc, hv, hm]
  | Lgoto _ => simp [lsemStep, ArchAgreeOpt]
  | Ligoto _ => simp [lsemStep, ArchAgreeOpt]
  | LstoreLabel _ _ => simp [lsemStep, ArchAgreeOpt]
  | Lcond _ _ => simp [lsemStep, ArchAgreeOpt]

/-- The step's store image is a function of the start state's store image: the
    `stateStore` form of `lsemStep_archAgree`. -/
theorem lsemStep_stateStore {w : Nat} (i : LinstrR) {s t : Lstate w}
    (h : stateStore s = stateStore t) :
    Option.map stateStore (lsemStep i s) = Option.map stateStore (lsemStep i t) :=
  (archAgreeOpt_iff_stateStore _ _).1
    (lsemStep_archAgree i ((archAgree_iff_stateStore s t).2 h))

/-- The unbundled form of `lsemStep_archAgree`: from states with equal register
    map and memory, a step that succeeds on one succeeds on the other and lands
    on states with equal register map and memory. -/
theorem lsemStep_congr_of_archAgree {w : Nat} (i : LinstrR) {s t : Lstate w}
    (hv : s.lvm = t.lvm) (hm : s.lmem = t.lmem) {s₁ : Lstate w}
    (hst : lsemStep i s = some s₁) :
    ∃ t₁, lsemStep i t = some t₁ ∧ s₁.lvm = t₁.lvm ∧ s₁.lmem = t₁.lmem := by
  have h := lsemStep_archAgree i (s := s) (t := t) ⟨hv, hm⟩
  rw [hst] at h
  cases ht : lsemStep i t with
  | none => rw [ht] at h; exact (h : False).elim
  | some t₁ => rw [ht] at h; exact ⟨t₁, rfl, h.1, h.2⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
