/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutral
public import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
public import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm

/-!
# The de-Bruijn proof, shared across `ScalarTarget` backends

The `Com → RegProg` de-Bruijn faithfulness is stated once, against the
backend-independent `RegProg.denotePure`, and `com_machine_faithful` lifts it to
any `ScalarTarget` with a register projection `proj` whose `step` agrees with
`evalRegStmtPure` on every statement. This module instantiates it for AArch64
(`hstep_arm`). The package's other `ScalarTarget` instances are `rvTarget`
(`RISCVBackend/RegToRiscv.lean`) and `x86Target` (`ScalarLinX86Demo.lean`); their
step agreement holds only on a restricted set of statements (RISC-V: no
`zero`/`x0`/`xzr` names and `RvOk`; x86: no `xzr` names, destination distinct
from the sources, shift amounts below `2^64`),
so they use the restricted lift `ScalarTarget.compile_denote_pure_on` instead
(`MultiBackendDemo.com_riscv_e2e`, `ScalarLinX86Demo.com_x86_e2e`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

/-! ## 1. The generic statement: one de-Bruijn lemma for every `ScalarTarget`

Given a backend `T` with a projection `proj` whose `step` agrees with the neutral
semantics on all statements (`hstep`), and the backend-independent de-Bruijn
faithfulness `deBruijn` (the source value equals the flattened program's neutral
denotation at the result register), the backend's machine run computes that
value. The statement is generic over `T`; it applies to a backend whose step
agreement holds for every `RegStmt`, such as AArch64 below. -/
theorem com_machine_faithful
    (T : ScalarTarget) (proj : T.St → Env)
    (hstep : ∀ (s : T.St) (stmt : RegStmt),
      proj (T.step s stmt) = evalRegStmtPure (proj s) stmt)
    {Γ : Ctxt jasminDialect} {ty : JasminTy}
    (com : Com jasminDialect Γ ty) (depth : Nat) (s : T.St) (result : BitVec 64)
    (deBruijn :
      result = (RegProg.denotePure (comToRegProg com depth) (proj s)) (comRetName com depth)) :
    (proj (T.runOps s (T.compile (comToRegProg com depth)))) (comRetName com depth) = result := by
  rw [ScalarTarget.compile_denote_pure T proj hstep]
  exact deBruijn.symm

/-! ## 2. AArch64 plugs into the neutral semantics -/

/-- AArch64's `step` (`evalRegStmt`) agrees with the neutral semantics under the
    register projection `BState.regs` — by definitional unfolding (AArch64 and the
    neutral env share the `xzr` convention and the same `BitVec` op functions). -/
theorem hstep_arm (s : BState) (stmt : RegStmt) :
    (evalRegStmt s stmt).regs = evalRegStmtPure s.regs stmt := by
  cases stmt <;>
    simp only [evalRegStmt, evalRegStmtPure, BState.set, BState.get,
      Env.set, Env.get, opMul, opAnd64, opOrr64, opEor64, opUmulh, opLsr64, opLsl64,
      movkInsert, apply_ite BState.regs]

/-- **AArch64 instance of `com_machine_faithful`.** The compiled-and-run AArch64
    block, read at the result register, computes the source value, given the
    de-Bruijn equality `deBruijn`. (The RISC-V counterpart uses `rvTarget` and
    `RState64.regs` with the restricted lift `compile_denote_pure_on`, because
    `hstep_riscv` requires `RvFaithfulStmt`; see `MultiBackendDemo.com_riscv_e2e_of`.) -/
theorem com_arm_faithful
    {Γ : Ctxt jasminDialect} {ty : JasminTy}
    (com : Com jasminDialect Γ ty) (depth : Nat) (s : BState) (result : BitVec 64)
    (deBruijn :
      result = (RegProg.denotePure (comToRegProg com depth) s.regs) (comRetName com depth)) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg com depth))).regs)
        (comRetName com depth) = result :=
  com_machine_faithful ComToArm.armTarget (fun s => s.regs) hstep_arm com depth s result deBruijn

/-! ## 3. A concrete de-Bruijn lemma and its end-to-end instance

For the concrete `addCom` (`v2 := v0 + v1`), the de-Bruijn faithfulness is proved
directly (`deBruijn_addCom`): `Com.denote` equals the flattened program's neutral
denotation at the result register, for an environment with `e "v0" = x1` and
`e "v1" = x0`. Composing with `com_arm_faithful` gives `addCom_arm_e2e`: the
compiled AArch64 block, run from a state whose registers `v0`/`v1` hold these
values, computes `Com.denote addCom`. -/

theorem deBruijn_addCom (x0 x1 : BitVec 64) (e : Env)
    (h0 : e "v0" = x1) (h1 : e "v1" = x0) :
    Com.denote addCom (.cons x0 (.cons x1 .nil))
      = (RegProg.denotePure (comToRegProg addCom 2) e) (comRetName addCom 2) := by
  have hp : comToRegProg addCom 2 = [RegStmt.add "v2" "v0" "v1"] := by
    simp only [comToRegProg, comToReg_addCom]
  have hr : comRetName addCom 2 = "v2" := by
    simp only [comRetName, comToReg_addCom]
  rw [hp, hr, show Com.denote addCom (.cons x0 (.cons x1 .nil)) = x1 + x0 from rfl]
  simp only [RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure,
    Env.get, Env.set]
  simp [h0, h1]

theorem addCom_arm_e2e (x0 x1 : BitVec 64) (s : BState)
    (h0 : s.regs "v0" = x1) (h1 : s.regs "v1" = x0) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg addCom 2))).regs) (comRetName addCom 2)
      = Com.denote addCom (.cons x0 (.cons x1 .nil)) :=
  com_arm_faithful addCom 2 s _ (deBruijn_addCom x0 x1 s.regs h0 h1)

/-! ## 4. End-to-end for every `ComOK` kernel

`com_arm_faithful` (§2) takes the de-Bruijn equality as a hypothesis; for `addCom`
it is proved by `deBruijn_addCom`. For general `Com`s, `comToReg_faithful` proves
it from `ComOK` (every op is a `SupportedOp`) and `AllReg64` (the context is
all-`reg 64`). A kernel satisfying both therefore has an AArch64 correctness
theorem, `com_arm_e2e`, without a kernel-specific de-Bruijn proof. -/

/-- **Composition theorem.** For a straight-line `Com` with `ComOK com` over a
    context with `AllReg64 Γ`, started from a machine state with
    `s.regs = envOf Γ.length V`, the compiled-and-run AArch64 block read at the
    result register equals `Com.denote com V`. No kernel-specific de-Bruijn proof
    is needed. -/
theorem com_arm_e2e {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hok : ComOK com) (hΓ : AllReg64 Γ) (V : Ctxt.Valuation Γ) (s : BState)
    (hs : s.regs = envOf Γ.length V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg com Γ.length))).regs) (comRetName com Γ.length)
      = Com.denote com V := by
  apply com_arm_faithful com Γ.length s (Com.denote com V)
  rw [hs]; exact comToReg_faithful hok hΓ V

/-! ### A worked multi-op kernel: `mulhi(a,b) + K`

A three-binding kernel using a widening-high multiply (`mulhi`, covered by
`ScalarLinDeBruijn.opToStmts_mulhi_correct`), a materialised constant
(`regConst`, covered by `opToStmts_const_correct`) and an add (covered by
`opToStmts_bin_correct`). `ComOK` holds op by op (each op is a `SupportedOp`), and
`com_arm_e2e` gives the `Com → AArch64` theorem without a kernel-specific
de-Bruijn proof. -/

/-- `v2 := mulhi v0 v1 ; v3 := K ; v4 := v2 + v3 ; ret v4` over args `[a, b]`. -/
def mulhiAddKCom (K : Nat) : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .mulhi 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.var { op := .regConst 64 K, retTy_eq := rfl, args := .nil }
      (.var { op := .regArith .add 64, retTy_eq := rfl,
              args := .cons (.there .here) (.cons .here .nil) }
        (.ret .here)))

/-- `mulhiAddKCom` is in the supported fragment — one constructor per op. -/
theorem mulhiAddKCom_ok (K : Nat) : ComOK (mulhiAddKCom K) := by
  refine ComOK.var (Or.inr (Or.inl rfl)) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inr ⟨K, rfl⟩))) ?_
  exact ComOK.var (Or.inl ⟨.add, rfl, Or.inl rfl⟩) (ComOK.ret _)

/-- The two-element context is all-`reg 64`. -/
theorem allReg64_two : AllReg64 ([.reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu; rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · exact absurd h (List.not_mem_nil)

/-- **End-to-end for `mulhiAddKCom`.** The compiled AArch64 block for
    `mulhi(a,b)+K`, run from a state with `s.regs = envOf 2 V`, read at the result
    register, equals the source denotation; an instance of `com_arm_e2e`. -/
theorem mulhiAddKCom_arm_e2e (K : Nat) (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg (mulhiAddKCom K) 2))).regs)
        (comRetName (mulhiAddKCom K) 2)
      = Com.denote (mulhiAddKCom K) V :=
  com_arm_e2e (mulhiAddKCom_ok K) allReg64_two V s hs

end CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
