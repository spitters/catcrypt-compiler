/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
public import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext

/-!
# The THIR front lowering is robustly constant-time

`lowerThir : Com thirDialect Γ t → Com jasminDialect Γ t` produces a
constant-time-safe Jasmin program under **any** label context, and hence
(reusing the dialect-polymorphic robust-CT scaffolding in
`RobustSafetyContext`) is **robustly CT-safe against all linking contexts** —
`lowerThir_robustlyCTSafe_ctx`, the THIR-front analogue of the lattice front's
`lowerLatticeToJasmin_robustlyCTSafe_ctx`.

The argument is structural and reuses everything: `ctSafeJasmin` flags only
`stackLoad` / `stackStore` ops (the only index-bearing ones), and the THIR op
alphabet has *no memory op at all* — `lowerThir` therefore never emits a
load/store, so every binding is CT-safe by the `opIndexPublic` catch-all,
regardless of which inputs are secret. We capture this as a "no memory op"
invariant `jComNoMem`, prove it preserved by `Com.rename` (the only wrinkle, in
the `thBinLit` two-op expansion), established for every `lowerThir` output, and
discharging the robust-context obligation by the generic CT-compositionality
lemma `ctSafeJasmin_plug_of`.

This is the concrete answer to "does the THIR (compile-from-hax) front inherit
the robust-compilation result": yes — by one CT-safety induction plus the
3-line composition that the lattice front already uses, with no new
context/linking/back-translation machinery.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ThirCTSafe

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. A "no memory op" invariant -/

/-- An op is non-memory iff it is not `stackLoad` / `stackStore` — the only ops
    whose CT-safety depends on a (possibly secret) index register. -/
def jOpNoMem : JasminOp → Bool
  | .stackLoad _ _ => false
  | .stackStore _ _ => false
  | _ => true

/-- `opIndexPublic` is unconditionally `true` for a non-memory op: only the
    `stackLoad` / `stackStore` arms inspect an index; every other op falls to the
    catch-all `true`, regardless of arguments or label context. -/
theorem opIndexPublic_of_noMem {Γ : Ctxt jasminDialect} (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig op))
    (L : LabelCtxt Γ) (h : jOpNoMem op = true) :
    opIndexPublic op args L = true := by
  cases op <;> simp_all [jOpNoMem, opIndexPublic]

/-- A Jasmin `Com` has no memory op iff every let-bound expression's op is
    non-memory. -/
def jComNoMem {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Bool
  | .ret _ => true
  | .var e body => jOpNoMem e.op && jComNoMem body

/-- `Com.rename` preserves `jComNoMem`: renaming maps each binding's variables but
    keeps its op (`Expr.rename` sets `op := e.op`), so the no-memory-op invariant
    is renaming-invariant. (The one wrinkle in the `thBinLit` arm of `lowerThir`,
    which renames the body under an inserted `regConst` binding.) -/
@[simp] theorem jComNoMem_rename : {Γ Γ' : Ctxt jasminDialect} → {t : JasminTy} →
    (h : Ctxt.Hom Γ Γ') → (c : Com jasminDialect Γ t) →
    jComNoMem (Com.rename h c) = jComNoMem c
  | _, _, _, _, .ret _ => rfl
  | _, _, _, h, .var e body => by
      simp only [Com.rename, Expr.rename, jComNoMem]
      rw [jComNoMem_rename h.lift body]

/-- A `Com` with no memory op is CT-safe under any label context: every binding's
    expression is CT-safe by `opIndexPublic_of_noMem`, and `ret` is oblivious. -/
theorem noMem_ctSafeJasmin : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → (L : LabelCtxt Γ) →
    jComNoMem c = true → ctSafeJasmin c L = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, L, h => by
      simp only [jComNoMem, Bool.and_eq_true] at h
      rw [ctSafeJasmin_var]
      simp only [ctSafeExprJasmin]
      rw [opIndexPublic_of_noMem e.op e.args L h.1, Bool.true_and]
      exact noMem_ctSafeJasmin body _ h.2

/-! ## 2. `lowerThir` has no memory op -/

/-- Lowering one THIR op never introduces a memory op: every `lowerVarStep` arm
    emits only `regArith` / `regConst` / shift / rotate / cast / carry / select /
    `extCall` / `vpackZMM` bindings — never `stackLoad` / `stackStore`. (The
    `thBinLit` arm inserts a `regConst` + `regArith` pair and renames the body;
    `jComNoMem_rename` discharges the rename.) -/
theorem lowerVarStep_noMem {Γ : Ctxt jasminDialect} {t : JasminTy}
    (op : thirDialect.Op)
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty)
      (DialectSignature.sig (d := thirDialect) op))
    (bodyJ : Com jasminDialect (DialectSignature.ret (d := thirDialect) op :: Γ) t) :
    jComNoMem (lowerVarStep op args bodyJ) = jComNoMem bodyJ := by
  cases op <;>
    simp only [lowerVarStep, jComNoMem, jOpNoMem, Bool.true_and, jComNoMem_rename]

/-- **Every `lowerThir` output is memory-op-free.** Structural induction on the
    source `Com thirDialect`: `ret` is trivial; the `var` case combines the IH on
    the body with `lowerVarStep_noMem`. -/
theorem lowerThir_noMem : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com thirDialect Γ t) → jComNoMem (lowerThir c) = true
  | _, _, .ret _ => rfl
  | _, _, .var (Expr.mk op hret args) body => by
      have ih := lowerThir_noMem body
      subst hret
      show jComNoMem (lowerVarStep op args (lowerThir body)) = true
      rw [lowerVarStep_noMem]
      exact ih

/-! ## 3. The headline: `lowerThir` is robustly CT-safe against all contexts -/

/-- **`lowerThir` is constant-time-safe under any label context.** The THIR-front
    analogue of `lowerLatticeToJasmin_ctSafeJasmin`.

    **Scope (why this is unconditional, and what it does NOT claim).** The result
    holds for *every* labelling precisely because the THIR op alphabet is a
    constant-time-*by-construction* subset — it cannot express the leaky
    constructs:
    * no secret-dependent **branch** (the only conditional is `thSelect`, a
      branchless cmov that evaluates both arms);
    * no secret-dependent **loop bound** (`ThirForProg` carries a static *public*
      trip count; data-dependent `while`/rejection sampling is not expressible);
    * no **memory op at all** — and `ctSafeJasmin`'s only non-trivial check is that
      a `stackLoad`/`stackStore` index is public, so with no load/store that check
      is never exercised.

    The leakage model is therefore the standard constant-time one (leakage =
    memory addresses + control flow; variable-latency ALU ops assumed CT, as in
    the jasmin CT model), and leaf calls (`thExtCall`) are **assumed** CT — so the
    guarantee is "the front-generated glue is CT *modulo* CT leaves", exactly as
    the lattice front assumes. **When a runtime-indexed load/store (`gather`) front
    op is added, this theorem becomes *conditional* (the index must be public),
    not unconditional** — that is the point at which the CT checker does real
    work. -/
theorem lowerThir_ctSafeJasmin {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) (L : LabelCtxt Γ) :
    ctSafeJasmin (lowerThir c) L = true :=
  noMem_ctSafeJasmin (lowerThir c) L (lowerThir_noMem c)

/-- **Headline: the THIR front is robustly CT-safe against all linking contexts.**
    For every source `Com thirDialect`, the lowered Jasmin program wrapped in *any*
    CT-safe linking context is constant-time, under every labelling. The proof is
    the identical 3-line composition the lattice front uses
    (`lowerLatticeToJasmin_robustlyCTSafe_ctx`): CT-compositionality over linking
    (`ctSafeJasmin_plug_of`) reduces the linked-program obligation to (i) the
    context's own CT-safety (the hypothesis) and (ii) the lowered program's
    CT-safety in the propagated labelling (`lowerThir_ctSafeJasmin`). So the THIR
    (compile-from-hax) front inherits robust constant-time compilation by
    instantiating the dialect-polymorphic scaffolding — no new context / linking /
    back-translation machinery. -/
theorem lowerThir_robustlyCTSafe_ctx {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) :
    RobustlyCTSafeCtx (lowerThir c) := by
  intro Δ C L hC
  exact ctSafeJasmin_plug_of C (lowerThir c) L hC
    (lowerThir_ctSafeJasmin c (propagateLabel C L))

end CatCrypt.Crypto.SecureCompilation.VIR.ThirCTSafe
