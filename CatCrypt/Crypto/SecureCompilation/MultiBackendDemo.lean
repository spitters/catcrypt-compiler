/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Core.Code
import all CatCrypt.Core.Heap
import all CatCrypt.Core.Location
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminOps
import all CatCrypt.Crypto.Jasmin.JasminTranslate
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.JasminVar
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
import all CatCrypt.Deep.Eval
import all CatCrypt.Deep.RawCode

public import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutral
public import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-!
# One kernel, two backends: AArch64 and RISC-V

A kernel written once as a `RegProg` in the shared `ScalarLin` intermediate
language, or flattened from a `Com`, compiles to AArch64 through `regToBOp` and
to RV64 through `regToROp`, each with a denotation theorem. This file proves:

* for the shift-free kernel `kernel` (`r := a·b + a`), that both compiled blocks
  compute the target's `denote` of the `RegProg` (`kernel_arm`, `kernel_riscv`);
* for `mulCom` (`v2 := v0 · v1`), that `comToRegProg` produces the expected
  `RegProg` (`mulCom_flatten`) and that both compiled blocks compute its
  `denote` (`mulCom_arm`, `mulCom_riscv`);
* for RISC-V, the end-to-end theorem from `Com.denote`: `com_riscv_e2e` for every
  `Com` with `ComOK` over an `AllReg64` context, run from a state with
  `regs = envOf Γ.length V`, and its instance `mulCom_riscv_e2e`.

The AArch64 end-to-end theorem from `Com.denote` is
`ScalarLinNeutralDemo.com_arm_e2e`.

The `ScalarTarget` end-to-end theorems of this module are legacy: they hold on the
register-only states `BState` and `RState64`, outside the `Lprog` back half, whose
RISC-V and AArch64 instances are `rvIsa` and `armIsa` with the assembly theorems
`rv_asm` and `arm_asm`. The reason they are kept is stated in
`ScalarLinNeutralDemo`, section "Status: legacy route".
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MultiBackendDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

/-- A shift-free arithmetic kernel as a `RegProg`: `r := a·b + a`. -/
def kernel : RegProg := [.mul "t" "a" "b", .add "r" "t" "a"]

/-- **AArch64**: the kernel compiles to a machine block computing its denotation. -/
theorem kernel_arm (s : BState) :
    runBBlock s (lowerBBlock (regToBOp kernel)) = armTarget.denote kernel s :=
  regToBOp_denote kernel s

/-- **RISC-V (RV64)**: the SAME kernel compiles to RV64 computing its denotation. -/
theorem kernel_riscv (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp kernel)) = rvTarget.denote kernel s :=
  regToROp_denote kernel s

/-! ## The `Com` front feeds the same waist

A high-level `Com` computing `v2 := v0 · v1` flattens to a `RegProg` that compiles
to both backends — `Com → RegProg → {AArch64, RISC-V}` as one composed function. -/

/-- `Com` over args `[r64, r64]`: `v2 := v0 · v1 ; ret v2`. -/
def mulCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .mul 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
        (.ret .here)

/-- The `Com` front yields the expected one-statement waist program. -/
theorem mulCom_flatten : comToRegProg mulCom 2 = [RegStmt.mul "v2" "v0" "v1"] := by
  rfl

/-- And that flattened program compiles to AArch64 with its denotation theorem —
    `Com → RegProg → AArch64`, end to end. -/
theorem mulCom_arm (s : BState) :
    runBBlock s (lowerBBlock (regToBOp (comToRegProg mulCom 2)))
      = armTarget.denote (comToRegProg mulCom 2) s :=
  regToBOp_denote (comToRegProg mulCom 2) s

/-- …and to RISC-V. -/
theorem mulCom_riscv (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg mulCom 2)))
      = rvTarget.denote (comToRegProg mulCom 2) s :=
  regToROp_denote (comToRegProg mulCom 2) s

/-! ## End-to-end on RISC-V: the compiled machine block computes `Com.denote`

The ARM end-to-end theorem (`ScalarLinNeutralDemo.com_arm_e2e`) is obtained from
the shared `comToReg_faithful`. RISC-V has the same shape: the RV64 machine run,
projected to the register environment, computes the source `Com.denote`. The RV64
state's `zero`/`x0` convention differs from the neutral `xzr`, but the de-Bruijn
names (`v0`, `v1`, …) avoid all three, so the projection agrees with the neutral
semantics on compiled programs (`comToRegProg_RvFaithful`). -/

/-- The registers a statement mentions (for the no-special-register side condition). -/
def regsOf : RegStmt → List String
  | RegStmt.add d a b | RegStmt.sub d a b | RegStmt.mul d a b | RegStmt.and d a b
  | RegStmt.orr d a b | RegStmt.eor d a b | RegStmt.umulh d a b => [d, a, b]
  | RegStmt.shrI d a _ | RegStmt.shlI d a _ | RegStmt.mov d a => [d, a]
  | RegStmt.movz d _ | RegStmt.loadImm d _ | RegStmt.movk d _ _ => [d]

/-- A statement RISC-V faithfully realises: it is `RvOk`-selectable and mentions no
    zero-register name (the RV `zero`/`x0` and neutral `xzr` conventions agree on
    every other name). -/
def RvFaithfulStmt (stmt : RegStmt) : Prop :=
  RvOk stmt = true ∧ ∀ r ∈ regsOf stmt, r ≠ "xzr" ∧ r ≠ "zero" ∧ r ≠ "x0"

/-- **RISC-V per-statement faithfulness.** For a faithful statement, the RV64 step
    projected to the registers equals the neutral `evalRegStmtPure`. -/
theorem hstep_riscv (s : RState64) (stmt : RegStmt) (h : RvFaithfulStmt stmt) :
    (evalRegStmtRV s stmt).regs = evalRegStmtPure s.regs stmt := by
  obtain ⟨hok, hreg⟩ := h
  cases stmt <;>
    simp_all [evalRegStmtRV, evalRegStmtPure, RState64.set, RState64.get, Env.set, Env.get,
      regsOf, RvOk]

/-! ### Automatic discharge: every compiled statement is `RvFaithful`

The side condition of `com_riscv_e2e_of` is automatic — the front emits no `movk`
and every register is a `lvlName` (`v_k`) name, which avoids all three zero-register
names. Proved by tracing membership through `exprSrcs.go` and `opToStmts`. -/

/-- Every name `exprSrcs.go` produces is a `lvlName`. -/
theorem exprSrcs_go_lvlName (depth : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ r ∈ exprSrcs.go (Γ := Γ) depth hv, ∃ k, r = lvlName k := by
  intro tys hv
  induction hv with
  | nil => intro r hr; simp [exprSrcs.go] at hr
  | cons v rest ih =>
      intro r hr
      rw [show exprSrcs.go (Γ := Γ) depth (HVector.cons v rest)
            = resolveName depth v :: exprSrcs.go (Γ := Γ) depth rest from rfl] at hr
      rcases List.mem_cons.mp hr with h | h
      · exact ⟨depth - 1 - varIndex v, h⟩
      · exact ih r h

/-- Every `exprSrcs` operand name avoids the zero-register names. -/
theorem exprSrcs_lvlName (depth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) :
    ∀ r ∈ exprSrcs depth e, r ≠ "xzr" ∧ r ≠ "zero" ∧ r ≠ "x0" := by
  intro r hr
  obtain ⟨k, rfl⟩ := exprSrcs_go_lvlName depth e.args r hr
  exact ⟨lvlName_ne_xzr k, lvlName_ne_zero k, lvlName_ne_x0 k⟩

/-- Every statement `opToStmts` emits (over `lvlName`-named operands) is `RvFaithful`. -/
theorem opToStmts_RvFaithful (d : Nat) (srcs : List String) (op : JasminOp)
    (hsrcs : ∀ r ∈ srcs, r ≠ "xzr" ∧ r ≠ "zero" ∧ r ≠ "x0") :
    ∀ stmt ∈ opToStmts (lvlName d) srcs op, RvFaithfulStmt stmt := by
  have hd : lvlName d ≠ "xzr" ∧ lvlName d ≠ "zero" ∧ lvlName d ≠ "x0" :=
    ⟨lvlName_ne_xzr d, lvlName_ne_zero d, lvlName_ne_x0 d⟩
  intro stmt hstmt
  cases op with
  | regArith bop w =>
      cases bop <;>
        (rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
          simp_all [opToStmts, RvFaithfulStmt, regsOf, RvOk])
  | mulhi w =>
      rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp_all [opToStmts, RvFaithfulStmt, regsOf, RvOk]
  | shrImm w n =>
      rcases srcs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
        simp_all [opToStmts, RvFaithfulStmt, regsOf, RvOk]
  | shlImm w n =>
      rcases srcs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
        simp_all [opToStmts, RvFaithfulStmt, regsOf, RvOk]
  | regConst w n =>
      simp_all [opToStmts, loadConstStmts, RvFaithfulStmt, regsOf, RvOk]
  | _ => simp_all [opToStmts]

/-- **Every compiled statement is `RvFaithful`** — the side condition, discharged
    for any `Com` by induction (no `ComOK` needed; unsupported ops emit nothing). -/
theorem comToRegProg_RvFaithful {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (depth : Nat) :
    ∀ stmt ∈ comToRegProg com depth, RvFaithfulStmt stmt := by
  induction com generalizing depth with
  | ret v =>
      intro stmt hstmt; simp only [comToRegProg_ret] at hstmt
      exact absurd hstmt (List.not_mem_nil)
  | var e body ih =>
      intro stmt hstmt
      rw [comToRegProg_var] at hstmt
      rcases List.mem_append.mp hstmt with h | h
      · exact opToStmts_RvFaithful _ _ _ (exprSrcs_lvlName _ e) stmt h
      · exact ih (depth + 1) stmt h

/-- `mulCom` is in the supported fragment. -/
theorem mulCom_ok : ComOK mulCom :=
  ComOK.var (Or.inl ⟨.mul, rfl, Or.inr (Or.inr (Or.inl rfl))⟩) (ComOK.ret _)

/-- The two-element context is all-`reg 64`. -/
theorem allReg64_two : AllReg64 ([.reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu; rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · exact absurd h List.not_mem_nil

/-- **General end-to-end RISC-V** (mirror of `com_arm_e2e`). For any supported `Com`
    over an all-`reg 64` context whose compiled statements RISC-V faithfully realises
    (`hf` — automatic in practice, the front emits no `movk` and only `v_k` names),
    the compiled-and-run RV64 block computes the source `Com.denote`. Composes the
    restricted lift `compile_denote_pure_on` with the shared axiom-clean
    `comToReg_faithful` — no RISC-V-specific de-Bruijn reasoning. Legacy, as
    `com_riscv_e2e`. -/
theorem com_riscv_e2e_of {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hok : ComOK com) (hΓ : AllReg64 Γ) (V : Ctxt.Valuation Γ) (s : RState64)
    (hs : s.regs = envOf Γ.length V)
    (hf : ∀ stmt ∈ comToRegProg com Γ.length, RvFaithfulStmt stmt) :
    (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))).regs
        (comRetName com Γ.length)
      = Com.denote com V := by
  rw [regToROp_denote]
  have key : (rvTarget.denote (comToRegProg com Γ.length) s).regs
      = RegProg.denotePure (comToRegProg com Γ.length) s.regs := by
    rw [← rvTarget.compile_denote (comToRegProg com Γ.length) s]
    exact ScalarTarget.compile_denote_pure_on rvTarget (fun s => s.regs) RvFaithfulStmt
      hstep_riscv (comToRegProg com Γ.length) hf s
  rw [congrFun key, hs]
  exact (comToReg_faithful hok hΓ V).symm

/-- **General end-to-end RISC-V** (counterpart of `com_arm_e2e`). For a `Com` with
    `ComOK com` over a context with `AllReg64 Γ`, run from a state with
    `s.regs = envOf Γ.length V`, the compiled-and-run RV64 block read at the result
    register equals `Com.denote com V`. The hypothesis `hf` of `com_riscv_e2e_of` is
    discharged by `comToRegProg_RvFaithful`. Legacy: a register-only `ScalarTarget`
    theorem outside the `Lprog` back half (`ScalarLinNeutralDemo`, section
    "Status: legacy route"). -/
theorem com_riscv_e2e {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hok : ComOK com) (hΓ : AllReg64 Γ) (V : Ctxt.Valuation Γ) (s : RState64)
    (hs : s.regs = envOf Γ.length V) :
    (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg com Γ.length)))).regs
        (comRetName com Γ.length)
      = Com.denote com V :=
  com_riscv_e2e_of hok hΓ V s hs (comToRegProg_RvFaithful com Γ.length)

/-- **End-to-end RISC-V on `mulCom`**, an instance of `com_riscv_e2e`. -/
theorem mulCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    (runRBlock64 s (lowerRBlock64 (regToROp (comToRegProg mulCom 2)))).regs
        (comRetName mulCom 2)
      = Com.denote mulCom V :=
  com_riscv_e2e mulCom_ok allReg64_two V s hs

end CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
