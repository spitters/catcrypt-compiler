/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutral
import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm

/-!
# The de-Bruijn proof, shared across all backends

The payoff of the neutral semantics: the `Com → RegProg` de-Bruijn faithfulness
is needed **once** (against `RegProg.denotePure`, backend-free), and
`com_machine_faithful` lifts it to *any* backend that plugs into the neutral
semantics — generically, over an abstract `ScalarTarget`. AArch64 is instantiated
here as a concrete witness (`hstep_arm`); RISC-V / x86 / GPU plug in identically
via their own register projection (RISC-V uses the `zero`/`x0` convention).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

/-! ## 1. The shared master: one de-Bruijn lemma ⟹ every backend

Given any backend `T` plugged into the neutral semantics (a projection `proj`
with `step`-agreement `hstep`) and the **single, backend-neutral** de-Bruijn
faithfulness `deBruijn` (the source value equals the flattened program's neutral
denotation at the result register), the backend's machine run computes that
value. Generic over `T` — so it serves AArch64, RISC-V, x86, GPU at once. -/
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

/-- **AArch64 instance of the master.** The compiled-and-run AArch64 block, read at
    the result register, computes the source value — given only the shared
    de-Bruijn lemma. (RISC-V is the same call with `rvTarget`, `RState64.regs`,
    and its own `hstep`.) -/
theorem com_arm_faithful
    {Γ : Ctxt jasminDialect} {ty : JasminTy}
    (com : Com jasminDialect Γ ty) (depth : Nat) (s : BState) (result : BitVec 64)
    (deBruijn :
      result = (RegProg.denotePure (comToRegProg com depth) s.regs) (comRetName com depth)) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg com depth))).regs)
        (comRetName com depth) = result :=
  com_machine_faithful ComToArm.armTarget (fun s => s.regs) hstep_arm com depth s result deBruijn

/-! ## 3. A concrete de-Bruijn lemma, discharged → end-to-end with no hypothesis

For the concrete `addCom` (`v2 := v0 + v1`), the de-Bruijn faithfulness holds
outright: `Com.denote` equals the flattened program's neutral denotation at the
result register. Composing with `com_arm_faithful` discharges its hypothesis,
giving a `sorry`-free end-to-end `Com → AArch64` correctness for this leaf —
proof that the whole architecture (flatten → compile → machine semantics)
computes the source, not just the scaffolding. -/

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

/-! ## 4. The Milestone-A payoff: end-to-end with NO per-kernel hand-discharge

`com_arm_faithful` (§2) takes the de-Bruijn equality as a *hypothesis*; for `addCom`
it was discharged by hand (`deBruijn_addCom`). With Milestone A complete,
`comToReg_faithful` discharges that hypothesis **mechanically** from `ComOK` (the op
is supported) and `AllReg64` (the context is all-`reg 64`) — so any kernel over the
field-leaf alphabet compiles to a verified AArch64 block with no bespoke proof. -/

/-- **Composition theorem.** For any supported straight-line `Com` over an all-`reg 64`
    context, started from a machine state whose registers match the valuation, the
    compiled-and-run AArch64 block reads back the source `Com.denote`. No per-kernel
    de-Bruijn proof — `ComOK` + `AllReg64` suffice. -/
theorem com_arm_e2e {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hok : ComOK com) (hΓ : AllReg64 Γ) (V : Ctxt.Valuation Γ) (s : BState)
    (hs : s.regs = envOf Γ.length V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg com Γ.length))).regs) (comRetName com Γ.length)
      = Com.denote com V := by
  apply com_arm_faithful com Γ.length s (Com.denote com V)
  rw [hs]; exact comToReg_faithful hok hΓ V

/-! ### A worked multi-op kernel: `mulhi(a,b) + K`

A two-binding kernel exercising the ops Milestone A unlocked — widening-high
multiply (`mulhi`, 5b) and a materialised constant (`regConst`, 5d) — composed with
an add (5a). `ComOK` is mechanical (each op is `SupportedOp`); `com_arm_e2e` then
gives sorry-free `Com → AArch64` faithfulness with no hand-written de-Bruijn proof. -/

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

/-- **End-to-end, sorry-free.** The compiled AArch64 block for `mulhi(a,b)+K`, run
    from a matching state, computes the source denotation — via `com_arm_e2e`, with
    zero bespoke de-Bruijn reasoning. -/
theorem mulhiAddKCom_arm_e2e (K : Nat) (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg (mulhiAddKCom K) 2))).regs)
        (comRetName (mulhiAddKCom K) 2)
      = Com.denote (mulhiAddKCom K) V :=
  com_arm_e2e (mulhiAddKCom_ok K) allReg64_two V s hs

end CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
