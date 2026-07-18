/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLin
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# `Com jasminDialect → RegProg`: the de-Bruijn flattening front

The literal front that turns a high-level `Com jasminDialect` straight-line leaf
(the `regArith` fragment: binary ALU, widening-high multiply, immediate shifts,
materialised constants) into the shared `ScalarLin.RegProg` waist — which every
backend (`ComToArm`, `RegToRiscv`, …) then lowers with its proved keystone.

It mirrors the x86 `JasminLprogExport.comToBody` exactly: walk the `Com`
(`.var e body` / `.ret v`), name each binding by its de-Bruijn **level**
(`curDepth`, so a binding's name is stable as the context grows), resolve each
`Expr` argument variable to its level name (`curDepth - 1 - varIndex`), and emit
the `RegStmt`(s) for the op. Composing `comToReg` with `ComToArm.regToBOp` /
`RegToRiscv.regToROp` gives `Com → AArch64`/`Com → RISC-V` as a single function.

The **denotation faithfulness theorem** (`Com.denote com V = run (compiled) …`) is
the dependently-typed de-Bruijn/`HVector` proof — the analogue of the proved
`ComLsemExportFaithful` semantic-faithfulness predicate over jasmin's `lsem`;
this file provides the executable front and a worked end-to-end demonstration,
leaving that theorem as the next obligation.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ScalarLinFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin

/-! ## 1. De-Bruijn variables → level names -/

/-- The de-Bruijn index of a variable (`here = 0`). -/
def varIndex {Γ : Ctxt jasminDialect} {τ : JasminTy} : Ctxt.Var Γ τ → Nat
  | .here => 0
  | .there v => varIndex v + 1

/-- The register name for a binding at de-Bruijn level `k`. -/
def lvlName (k : Nat) : String := "v" ++ toString k

/-- Resolve an argument variable to its level name at the current depth. -/
def resolveName (depth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) : String :=
  lvlName (depth - 1 - varIndex v)

/-- The source operand names of an `Expr`, in argument order. -/
def exprSrcs (depth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) : List String :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List String :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest => resolveName depth v :: go rest
  go e.args

/-! ## 2. `Expr` → `RegStmt`(s) -/

/-- Materialise a constant `n` into `dst`. Backend-neutral: emits a single
    `loadImm`; each backend lowers it to its own constant-load idiom (ARM
    `movz`/`movk`, RISC-V `li`). -/
def loadConstStmts (dst : String) (n : Nat) : List RegStmt :=
  [ .loadImm dst n ]

/-- Select the `RegStmt`(s) for an op with destination `dst` and source names
    `srcs`, over the `regArith` fragment. Unsupported ops yield no statement
    (the flattening front is partial, like the x86 `opToLinstrR` dispatch). -/
def opToStmts (dst : String) (srcs : List String) : JasminOp → List RegStmt
  | .regArith .add _ => match srcs with | [a, b] => [.add dst a b] | _ => []
  | .regArith .sub _ => match srcs with | [a, b] => [.sub dst a b] | _ => []
  | .regArith .mul _ => match srcs with | [a, b] => [.mul dst a b] | _ => []
  | .regArith .and _ => match srcs with | [a, b] => [.and dst a b] | _ => []
  | .regArith .or _  => match srcs with | [a, b] => [.orr dst a b] | _ => []
  | .regArith .xor _ => match srcs with | [a, b] => [.eor dst a b] | _ => []
  | .mulhi _ => match srcs with | [a, b] => [.umulh dst a b] | _ => []
  | .shrImm _ n => match srcs with | [a] => [.shrI dst a n] | _ => []
  | .shlImm _ n => match srcs with | [a] => [.shlI dst a n] | _ => []
  | .regConst _ n => loadConstStmts dst n
  | _ => []

/-! ## 3. The flattening -/

/-- Flatten a `Com jasminDialect` straight-line leaf to a `RegProg` plus the
    result register name. `depth` is the number of bindings already in scope. -/
def comToReg : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat → RegProg × String
  | _, _, .ret v, depth => ([], lvlName (depth - 1 - varIndex v))
  | _, _, .var e body, depth =>
      let stmts := opToStmts (lvlName depth) (exprSrcs depth e) e.op
      let (rest, retName) := comToReg body (depth + 1)
      (stmts ++ rest, retName)

/-- The flattened program (discarding the result name). -/
def comToRegProg {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (depth : Nat) : RegProg :=
  (comToReg c depth).1

/-- The result register name of a flattened program. -/
def comRetName {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (depth : Nat) : String :=
  (comToReg c depth).2

/-! ### Structural unfoldings (the shape the de-Bruijn induction recurses on) -/

@[simp] theorem comToRegProg_ret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (v : Ctxt.Var Γ t) (depth : Nat) : comToRegProg (Com.ret v) depth = [] := rfl

@[simp] theorem comRetName_ret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (v : Ctxt.Var Γ t) (depth : Nat) :
    comRetName (Com.ret v) depth = lvlName (depth - 1 - varIndex v) := rfl

@[simp] theorem comToRegProg_var {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s) (depth : Nat) :
    comToRegProg (Com.var e body) depth
      = opToStmts (lvlName depth) (exprSrcs depth e) e.op ++ comToRegProg body (depth + 1) := by
  simp only [comToRegProg, comToReg]

@[simp] theorem comRetName_var {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s) (depth : Nat) :
    comRetName (Com.var e body) depth = comRetName body (depth + 1) := by
  simp only [comRetName, comToReg]

/-! ## 4. Worked demonstration

A two-argument `Com` that binds `v2 := v0 + v1` and returns it. The flattening
recovers exactly the `RegProg` `[add v2 v0 v1]` with result name `v2` — the
de-Bruijn levels resolve correctly (`v0` = first arg, `v1` = second). -/

/-- `Com` over args `[r64, r64]`: `v2 := v0 + v1 ; ret v2`. -/
def addCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
        (.ret .here)

/-- The flattening produces the expected `RegProg` and result name. -/
theorem comToReg_addCom : comToReg addCom 2 = ([RegStmt.add "v2" "v0" "v1"], "v2") := by
  rfl

end CatCrypt.Crypto.SecureCompilation.ScalarLinFront
