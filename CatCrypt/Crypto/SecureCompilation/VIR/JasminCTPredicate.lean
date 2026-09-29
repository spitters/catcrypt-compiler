/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin

/-!
# Constant-time predicate for the Jasmin VIR dialect

A static predicate `ctSafeJasmin` on `Com jasminDialect Γ t` that captures:
*this program performs no variable-time memory access*. For the Jasmin dialect
the only CT-relevant ops are `stackLoad` / `stackStore`: a load or store whose
**index** is derived from a secret value is a constant-time violation (the
classic cache-timing / variable-address leak). The remaining ops
(`regArith`, `castW`, `extCall`) are *oblivious*: they touch no
data-dependent address and the dialect has **no data-dependent branch op**, so
they are always CT-safe.

This mirrors `CTPredicate.lean`'s `ctSafeCom` exactly in shape (a recursion
over `Expr` / `Com` returning `Bool`, with the load/store index playing the
role that the `ite`/`ifBit` condition plays in the CatCrypt dialect).

## Modelling "public index"

`CTPredicate.lean` consumes a caller-asserted `SecretLevel` label scheme
(`ComR.ifBit` carries a `.Public` / `.Secret` tag). We reuse that scheme's
spirit. A **label context** `LabelCtxt Γ` assigns a `SecretLevel` to every
variable in scope. A `stackLoad` / `stackStore` is CT-safe under a label
context iff its index variable looks up to `.Public`; the other ops impose no
index constraint. This is the simplest faithful model of "the address argument
is a public value (a loop index / literal), not secret-derived".

## Headline: lowering is CT-safe by construction

`lowerLatticeToJasmin` (`LatticeToJasmin.lean`) lowers each *whole-poly*
lattice op (`ntt`, `invntt`, `basemul`, `polyAddN`, `polyMulC`) to a Jasmin
`extCall` leaf. The lattice dialect has **no data-dependent addressing** — its
ops act on entire polynomials, never on a scalar index — so the lowering emits
**no `stackLoad` / `stackStore` at all**. Consequently every lowered program is
`ctSafeJasmin` *for any label context whatsoever*: there are no addressed
memory accesses to constrain. This is the first robust-compilation artifact on
the Jasmin path: "the optimizer's output is constant-time by construction."

We prove the fully-general theorem `lowerLatticeToJasmin_ctSafeJasmin` by
induction on the source `Com latticeDialect`, plus concrete-program corollaries
for the smoke programs the lattice path actually emits
(`ntt_3329_256` / `ntt_basemul_3329_256` / `ntt_invntt_3329_256`).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. Label contexts

A label context tags every variable in scope with a `SecretLevel`, mirroring
the caller-asserted tag scheme used by `CTPredicate.ctSafeComR`. We model it as
an `HVector` of `SecretLevel`s, one per binding, so lookup is along the same de
Bruijn membership witness that `Ctxt.Var.lookup` uses. -/

/-- A label context for `Γ`: one `SecretLevel` per variable in scope. -/
abbrev LabelCtxt (Γ : Ctxt jasminDialect) : Type :=
  HVector (fun _ => SecretLevel) Γ

/-- Look up a variable's `SecretLevel` in a label context (same de Bruijn
    recursion as `Ctxt.Var.lookup`). -/
def labelOf {Γ : Ctxt jasminDialect} {s : JasminTy} :
    Ctxt.Var Γ s → LabelCtxt Γ → SecretLevel
  | .here, .cons l _ => l
  | .there v, .cons _ L => labelOf v L

/-- Extend a label context with the level of a new binding. -/
def LabelCtxt.extend {Γ : Ctxt jasminDialect} {t : JasminTy}
    (L : LabelCtxt Γ) (l : SecretLevel) : LabelCtxt (t :: Γ) :=
  .cons l L

/-- The join of the levels of a list of argument variables; `.Public` for the
    empty list. -/
def argsLevel {Γ : Ctxt jasminDialect} (L : LabelCtxt Γ) :
    {ts : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) ts → SecretLevel
  | [], .nil => SecretLevel.Public
  | _ :: _, .cons v rest => (labelOf v L).join (argsLevel L rest)

/-- The level of a let-bound expression: the join of the levels of its
    arguments. A result computed from a secret argument is secret. -/
def exprLevel {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (L : LabelCtxt Γ) : SecretLevel :=
  argsLevel L e.args

/-! ## 2. Per-op CT predicate

`stackLoad` / `stackStore` are the only index-bearing ops. Their second
argument (de Bruijn position 1 in the signature `[stackArr, reg 64, …]`) is the
index register. We flag the op CT-safe iff that index variable is labelled
`.Public`. All other ops are oblivious. -/

/-- Index argument of an op's argument `HVector`, as a `.Public` / `.Secret`
    judgement. For `stackLoad` / `stackStore` the index register is the second
    argument; for every other op there is no addressed access, so it is
    vacuously public. -/
def opIndexPublic {Γ : Ctxt jasminDialect} (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig op))
    (L : LabelCtxt Γ) : Bool :=
  match op, args with
  | .stackLoad _ _, .cons _ (.cons i _) =>
      decide (labelOf i L = SecretLevel.Public)
  | .stackStore _ _, .cons _ (.cons i _) =>
      decide (labelOf i L = SecretLevel.Public)
  | _, _ => true

/-! ## 3. Per-expression CT predicate -/

/-- An `Expr` is CT-safe under a label context iff its op's index argument (if
    any) is public. Mirrors `CTPredicate.ctSafeExpr`. -/
def ctSafeExprJasmin {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (L : LabelCtxt Γ) : Bool :=
  opIndexPublic e.op e.args L

/-! ## 4. Per-program CT predicate

Recursion over `Com`, mirroring `ctSafeCom`. At each `var` binding the
expression's index must be public; the body is checked in the label context
extended with `exprLevel e L`, the join of the argument levels, so an index
computed from a secret is labelled secret. -/

/-- A `Com jasminDialect` is CT-safe under a label context iff every let-bound
    expression's index argument is public, each binding labelled with the join
    of its argument levels. `ret` is oblivious. -/
def ctSafeJasmin {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → LabelCtxt Γ → Bool
  | .ret _, _ => true
  | .var e body, L =>
      ctSafeExprJasmin e L && ctSafeJasmin body (L.extend (exprLevel e L))

/-! ## 5. Decidability + Prop bridge -/

/-- Propositional form of CT-safety. -/
def ctSafePropJasmin {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (L : LabelCtxt Γ) : Prop :=
  ctSafeJasmin c L = true

instance {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (L : LabelCtxt Γ) :
    Decidable (ctSafePropJasmin c L) := by
  unfold ctSafePropJasmin; infer_instance

/-! ## 6. Definitional unfolding lemmas -/

@[simp]
theorem ctSafeJasmin_ret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (v : Ctxt.Var Γ t) (L : LabelCtxt Γ) :
    ctSafeJasmin (Com.ret v) L = true := rfl

@[simp]
theorem ctSafeJasmin_var {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s)
    (L : LabelCtxt Γ) :
    ctSafeJasmin (Com.var e body) L
      = (ctSafeExprJasmin e L
          && ctSafeJasmin body (L.extend (exprLevel e L))) := rfl

/-! ## 7. `extCall` expressions are always CT-safe

The lowering emits only `extCall` ops (see `LatticeToJasmin.jasminOpOf`), which
carry no addressed memory access, so `opIndexPublic` is `true` for them
unconditionally — regardless of arguments or label context. -/

@[simp]
theorem opIndexPublic_extCall {Γ : Ctxt jasminDialect}
    (name : String) (argTys : List JasminTy) (retTy : JasminTy)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (.extCall name argTys retTy)))
    (L : LabelCtxt Γ) :
    opIndexPublic (.extCall name argTys retTy) args L = true := rfl

/-- Any `extCall` expression is CT-safe under any label context. -/
theorem ctSafeExprJasmin_extCall {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t)
    (h : ∃ name argTys retTy, e.op = JasminOp.extCall name argTys retTy)
    (L : LabelCtxt Γ) :
    ctSafeExprJasmin e L = true := by
  obtain ⟨name, argTys, retTy, hop⟩ := h
  unfold ctSafeExprJasmin
  -- `opIndexPublic` matches on `e.op`; with `e.op = extCall …` the catch-all
  -- branch fires, giving `true`.
  cases e with
  | mk op retTy_eq args =>
    subst hop
    rfl

/-! ## 8. The headline: `lowerLatticeToJasmin` is CT-safe by construction

The lattice dialect has no data-dependent addressing — every op is whole-poly —
so `lowerLatticeToJasmin` lowers each op to a Jasmin `extCall` and never emits a
`stackLoad` / `stackStore`. Therefore the lowered program is `ctSafeJasmin`
under **any** label context.

`lowerExpr` always produces an `Expr` whose op is `jasminOpOf e.op`, which is by
definition an `extCall`, so each binding is CT-safe by
`ctSafeExprJasmin_extCall`; the proof is a straight induction on the source
`Com`. -/

/-- `jasminOpOf` always returns an `extCall` op. -/
theorem jasminOpOf_is_extCall (op : LatticeOp) :
    ∃ name argTys retTy, jasminOpOf op = JasminOp.extCall name argTys retTy :=
  ⟨leafName op,
    (DialectSignature.sig (d := latticeDialect) op).map tau,
    tau (DialectSignature.ret (d := latticeDialect) op), rfl⟩

/-- A lowered expression is always CT-safe (its op is an `extCall`). -/
theorem lowerExpr_ctSafe {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (e : Expr latticeDialect Γ t) (L : LabelCtxt (Γ.map tau)) :
    ctSafeExprJasmin (lowerExpr e) L = true := by
  apply ctSafeExprJasmin_extCall
  -- `(lowerExpr e).op = jasminOpOf e.op`, which is an `extCall`.
  exact jasminOpOf_is_extCall e.op

/-- **Headline theorem (general).** Lowering any lattice program to the Jasmin
    dialect yields a constant-time-safe program, under *any* label context: the
    lattice dialect has no data-dependent addressing, so the lowering emits no
    variable-index load / store. Proved by induction on the source `Com`. -/
theorem lowerLatticeToJasmin_ctSafeJasmin :
    ∀ {Γ : Ctxt latticeDialect} {t : LatticeTy}
      (c : Com latticeDialect Γ t) (L : LabelCtxt (Γ.map tau)),
      ctSafeJasmin (lowerLatticeToJasmin c) L = true
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, L => by
      rw [show lowerLatticeToJasmin (Com.var e body)
            = Com.var (lowerExpr e) (lowerLatticeToJasmin body) from rfl]
      rw [ctSafeJasmin_var, lowerExpr_ctSafe e L]
      simp only [Bool.true_and]
      exact lowerLatticeToJasmin_ctSafeJasmin body _

/-- Propositional form of the headline theorem. -/
theorem lowerLatticeToJasmin_ctSafePropJasmin
    {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (c : Com latticeDialect Γ t) (L : LabelCtxt (Γ.map tau)) :
    ctSafePropJasmin (lowerLatticeToJasmin c) L :=
  lowerLatticeToJasmin_ctSafeJasmin c L

/-! ## 9. Concrete-program corollaries

The lattice path emits, at ML-KEM-flavoured parameters `(q, n) = (3329, 256)`,
the NTT-expanded `tgtCom` (`ntt a; ntt b; basemul; invntt; ret`) and the
unexpanded `srcCom` (`poly_mul`). Both lower to CT-safe Jasmin programs. We
state these against the all-`Public` label context for the (two-input) lowered
parameter context. -/

/-- The all-`.Public` label context for the lowered two-input parameter context
    `(inCtxt 3329 256).map tau`. -/
def allPublic2 : LabelCtxt ((LatticeDialect.inCtxt 3329 256).map tau) :=
  .cons SecretLevel.Public (.cons SecretLevel.Public .nil)

/-- The lowered NTT-expanded target program (`ntt_3329_256` / `ntt_basemul_…` /
    `ntt_invntt_…`) is constant-time-safe. -/
theorem tgt_ctSafeJasmin :
    ctSafeJasmin (lowerLatticeToJasmin (LatticeDialect.tgtCom 3329 256))
      allPublic2 = true :=
  lowerLatticeToJasmin_ctSafeJasmin _ allPublic2

/-- The lowered unexpanded source program (`poly_mul`) is constant-time-safe. -/
theorem src_ctSafeJasmin :
    ctSafeJasmin (lowerLatticeToJasmin (LatticeDialect.srcCom 3329 256))
      allPublic2 = true :=
  lowerLatticeToJasmin_ctSafeJasmin _ allPublic2

/-! ## 10. Smoke: a hand-built `stackLoad` IS flagged when its index is secret

To confirm the predicate is *not* vacuously `true`, we exhibit a `stackLoad`
whose index variable is labelled `.Secret` and check it is flagged non-CT, and
the same load with a `.Public` index check CT-safe. This is the analogue of
`CTPredicate`'s `.Secret`-tagged `ifBit` smoke test. -/

/-- A context with a stack array (index 0) and a `reg 64` index (index 1). -/
abbrev loadCtxt : Ctxt jasminDialect := [.stackArr 16 8, .reg 64]

/-- A single `stackLoad` reading element `i` of array `arr`. The signature of
    `stackLoad 16 8` is `[.stackArr 16 8, .reg 64]`, so the array is the first
    argument (`.here`, index 0 of `loadCtxt`) and the index register is the
    second argument (`.there .here`, index 1 of `loadCtxt`). -/
def loadProg : Com jasminDialect loadCtxt (.reg 16) :=
  .var (.mk (.stackLoad 16 8) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- Label context tagging the index (`reg 64`, de Bruijn `there here`) as
    `.Secret`. -/
def secretIdxLabels : LabelCtxt loadCtxt :=
  .cons SecretLevel.Public (.cons SecretLevel.Secret .nil)

/-- Label context tagging the index as `.Public`. -/
def publicIdxLabels : LabelCtxt loadCtxt :=
  .cons SecretLevel.Public (.cons SecretLevel.Public .nil)

/-- A `stackLoad` with a *secret* index is flagged NON-CT: the predicate is not
    vacuously true. -/
theorem loadProg_secret_not_ctSafe :
    ctSafeJasmin loadProg secretIdxLabels = false := by
  native_decide

/-- The same `stackLoad` with a *public* index is CT-safe. -/
theorem loadProg_public_ctSafe :
    ctSafeJasmin loadProg publicIdxLabels = true := by
  native_decide

/-- A `stackLoad` whose index is a value computed from the index register
    (`castW 64 64` of it) rather than the register itself. -/
def derivedLoadProg : Com jasminDialect loadCtxt (.reg 16) :=
  .var (.mk (.castW 64 64) rfl (.cons (.there .here) .nil))
    (.var (.mk (.stackLoad 16 8) rfl
            (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- A load whose index is derived from a secret register is flagged: the
    derived binding carries the secret level of its argument. -/
theorem derivedLoadProg_secret_not_ctSafe :
    ctSafeJasmin derivedLoadProg secretIdxLabels = false := by
  decide

/-- The same derived-index load is CT-safe when the register is public. -/
theorem derivedLoadProg_public_ctSafe :
    ctSafeJasmin derivedLoadProg publicIdxLabels = true := by
  decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
