/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminMonoSem
public import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
public import CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP

/-!
# Dialect-targeting Jasmin → SSA translation (`catCryptDialect`)

This file builds `translateMonoCmdD`, a Jasmin → SSA translator that emits
a `Com catCryptDialect Γ (.sword n)` **directly** from the Jasmin
`MonoCmd`/`InstrR` head: each `InstrR`/`PExpr` head is mapped straight to the
corresponding `catCryptDialect` op (`bvAdd64`/`bvXor`/`bvConst`/shift/…).

The translator also uses the *variable* translation
`DialectVarBridge.toVIRVar` (the de-Bruijn relabelling of the `CVar`s that the
`MonoVarMap` records) and the `MonoVarMap`/`monoAgrees`/`pureEvalMonoCmd`
reference layer from `JasminMonoSem`.

The reference-semantics correctness of this translator
(`Com.denoteSP (translateMonoCmdD …) = SPComp.pure (pureEvalMonoCmd …)`)
is proved by induction in
`JasminToSSADialectNative.lean` (`translateMonoCmdD_denoteSP_native`).

## Coverage

`translateMonoCmdD` covers, directly:

| arm | `translateMonoCmdD` |
|-----|---------------------|
| `[]` (return) | `Com.ret (toVIRVar cv)` |
| `Cassgn (.Lvar x) … (.Pvar gv)` (copy) | alias in map |
| `Cassgn (.Lvar x) … e` (op/const/shift/not) | `Com.var (dialect Expr) body` |
| `Copn … (.Oasm "ADD_64") …` | `Com.var (bvAdd64; fst; snd) body` |
| `Copn … (.Oasm "ADC_64") …` | `Com.var (bvAdc; fst; snd) body` |
| other (`Cif`/`Cfor`/`Cwhile`/`Ccall`/other `Copn`/non-`Lvar` lvals) | `none` |

The straight bignum ALU spine — the arms `S2NBignumSSA`'s ports actually use
(copy / add / sub / mul / and / xor / or / not / shifts / const / ret) plus
the `ADD_64`/`ADC_64` carry intrinsics — is fully covered.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.ToSSADialect

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.ToSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open scoped ENNReal

set_option autoImplicit false

noncomputable section

/-! ## The dialect-targeting translator -/

/-- Translate a Jasmin binary op on two `catCryptDialect` operand variables
    directly to a dialect `Expr`. Mirrors `JasminToSSA.translateBinOp`
    (`Olxor → .bvXor`, `Oland → .bvAnd`, `Olor → .bvOr`, `Oadd → .bvAdd`,
    `Osub → .bvSub`, `Omul → .bvMul`); declines every other op. -/
def translateBinOpD {Γ : Ctx} {n : Nat}
    (a b : Ctxt.Var (d := catCryptDialect) Γ (.sword n)) :
    SOp2 → Option (Expr catCryptDialect Γ (.sword n))
  | .Olxor _ => some { op := .bvXor n, retTy_eq := rfl, args := .cons a (.cons b .nil) }
  | .Oland _ => some { op := .bvAnd n, retTy_eq := rfl, args := .cons a (.cons b .nil) }
  | .Olor _ => some { op := .bvOr n, retTy_eq := rfl, args := .cons a (.cons b .nil) }
  | .Oadd _ => some { op := .bvAdd n, retTy_eq := rfl, args := .cons a (.cons b .nil) }
  | .Osub _ => some { op := .bvSub n, retTy_eq := rfl, args := .cons a (.cons b .nil) }
  | .Omul _ => some { op := .bvMul n, retTy_eq := rfl, args := .cons a (.cons b .nil) }
  | _ => none

/-- Translate a Jasmin expression directly to a `catCryptDialect` `Expr`.

    Emits the dialect op for each supported `PExpr` head straight from the
    Jasmin AST. Returns `none` on the heads
    `JasminToSSA.translateMonoExpr` declines (unsupported expression shapes,
    or operands not in the variable map). Mirrors `translateMonoExpr` arm for
    arm; the image is a `catCryptDialect` op record. -/
def translateMonoExprD {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) : PExpr → Option (Expr catCryptDialect Γ (.sword n))
  | .Pconst z =>
    some { op := .bvConst n (BitVec.ofInt n z), retTy_eq := rfl, args := .nil }
  | .Papp2 op (.Pvar x) (.Pvar y) =>
    match m x.gv.var, m y.gv.var with
    | some cvx, some cvy => translateBinOpD (toVIRVar cvx) (toVIRVar cvy) op
    | _, _ => none
  | .Papp1 (.Olnot _) (.Pvar x) =>
    match m x.gv.var with
    | some cvx =>
      some { op := .bvNot n, retTy_eq := rfl, args := .cons (toVIRVar cvx) .nil }
    | none => none
  | .Papp2 (.Olsl _) (.Pvar x) (.Pconst k) =>
    match m x.gv.var with
    | some cvx =>
      some { op := .bvShiftL n k.toNat, retTy_eq := rfl, args := .cons (toVIRVar cvx) .nil }
    | none => none
  | .Papp2 (.Olsr _) (.Pvar x) (.Pconst k) =>
    match m x.gv.var with
    | some cvx =>
      some { op := .bvShiftR n k.toNat, retTy_eq := rfl, args := .cons (toVIRVar cvx) .nil }
    | none => none
  | _ => none

/-- **Dialect-targeting Jasmin → SSA translator.** Builds a
    `Com catCryptDialect Γ (.sword n)` directly from the Jasmin command,
    mirroring each `InstrR` head to the corresponding `catCryptDialect` op.
    Covers the straight bignum ALU spine (return / copy / op-assignment) and
    the `ADD_64`/`ADC_64` carry intrinsics (`bvAdd64`/`bvAdc` + `fst`/`snd`
    destructuring); declines all control flow and other `Copn` heads, as
    `none`. -/
def translateMonoCmdD {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (retVar : Var) :
    List InstrR → Option (Com catCryptDialect Γ (.sword n))
  | [] =>
    match m retVar with
    | some cv => some (.ret (toVIRVar cv))
    | none => none
  | .Cassgn (.Lvar x) _ _ (.Pvar gv) :: rest =>
    match m gv.gv.var with
    | some cv =>
      translateMonoCmdD (fun w => if w = x.var then some cv else m w) retVar rest
    | none => none
  | .Cassgn (.Lvar x) _ _ e :: rest =>
    match translateMonoExprD m e with
    | some dexpr =>
      match translateMonoCmdD (m.extend x.var) retVar rest with
      | some body => some (.var dexpr body)
      | none => none
    | none => none
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADD_64"⟩) [.Pvar av, .Pvar bv] :: rest =>
    match m av.gv.var, m bv.gv.var with
    | some cva, some cvb =>
      let m' := m.extend2 cfv.var rv.var
      match translateMonoCmdD m' retVar rest with
      | some body =>
        some (.var { op := .bvAdd64 n, retTy_eq := rfl,
                     args := .cons (toVIRVar cva) (.cons (toVIRVar cvb) .nil) }
                (.var { op := .fst (.sword n) (.sword n), retTy_eq := rfl,
                        args := .cons .here .nil }
                  (.var { op := .snd (.sword n) (.sword n), retTy_eq := rfl,
                          args := .cons (.there .here) .nil } body)))
      | none => none
    | _, _ => none
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADC_64"⟩) [.Pvar av, .Pvar bv, .Pvar cinv] :: rest =>
    match m av.gv.var, m bv.gv.var, m cinv.gv.var with
    | some cva, some cvb, some cvcin =>
      let m' := m.extend2 cfv.var rv.var
      match translateMonoCmdD m' retVar rest with
      | some body =>
        some (.var { op := .bvAdc n, retTy_eq := rfl,
                     args := .cons (toVIRVar cva)
                       (.cons (toVIRVar cvb) (.cons (toVIRVar cvcin) .nil)) }
                (.var { op := .fst (.sword n) (.sword n), retTy_eq := rfl,
                        args := .cons .here .nil }
                  (.var { op := .snd (.sword n) (.sword n), retTy_eq := rfl,
                          args := .cons (.there .here) .nil } body)))
      | none => none
    | _, _, _ => none
  | _ :: _ => none

end

end CatCrypt.Crypto.Jasmin.ToSSADialect
