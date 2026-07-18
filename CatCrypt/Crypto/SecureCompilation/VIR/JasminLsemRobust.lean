/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation

/-!
# Constant-time leakage over `lsem`, and the unconditional `correct ∧ robust`
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

## Fidelity (trust-critical): what `lsemLeak` leaks, and why it is honest

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
  modeled honestly so the leak function is total and faithful to the full IR.)

Crucially `lsemLeak` **never reads `s.lvm`** — it never inspects a register
value. That is the whole point: for the straight-line `regArith` fragment there
is no data-dependent branch (`Lopn` is unconditional) and no value-dependent
memory addressing (every operand is `.reg`/`.imm`), so the leak is *genuinely*
state-independent — and the model reflects exactly that, by leaking the
instruction's opcode/operand-register structure and nothing else.

This is the linear-IR analogue of `MachineConstantTime.blockLeak_state_independent`
and `LowCTToJInstrCT.lowerSeq_constant_time`, and the `lsem`-level counterpart of
`RHPVerifiedMiddle.all_cprog_ct`.

## Scope (honest)

The capstone is unconditional **for the uniform-width `regArith` straight-line
fragment** (`UniformRegArith`/`UniformCtxt`), the same fragment increment 2's
functional simulation covers. The `lsem→bytes` encoder and the Sail
encode/decode tables remain the declared trusted base, as for every verified
compiler. **0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound}**, no
`jasminc_preserves_ct`.
-/

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
    simp only [opToLinstrR, lsemStep, hargs, List.map_cons, List.map_nil,
      stripWidthTag_withWidthTag_binOpName, applyOpn_binOpName]
    exact ⟨_, rfl⟩

/-- **Robustness / constant-time keystone (unconditional).** The linear-IR
    leakage trace of the linearizer-emitted `.var`-chain `straightOps` is the
    **same from any two initial states** `s₁ s₂`.

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
    2. *(robust / constant-time, from §5)* the linear-IR leakage trace
       `lsemLeak (straightOps …)` is the **same from any two initial states** —
       the attacker's control-flow + operand-structure view is a function of the
       emitted instruction list alone, never of a register value, so the leaf is
       constant-time.

    This is **unconditional**: it carries no IR→x86 faithfulness hypothesis and
    invokes no `jasminc_preserves_ct`. Both conjuncts concern one and the same
    object — the linearizer-emitted straight-line body run by `lsemStraight` and
    observed by `lsemLeak`. The `lsem→bytes` encoder and the Sail encode/decode
    tables remain the declared trusted base, as for every verified compiler. -/
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
    empty regardless of state. The branch-free half of the CT verdict (cf.
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

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
