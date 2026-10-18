/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate

/-!
# The THIR front lowering emits no memory op

`lowerThir : Com thirDialect Γ t → Com jasminDialect Γ t` never emits a
`stackLoad` or `stackStore`. The invariant is `jComNoMem`; it is preserved by
`Com.rename` (used in the `thBinLit` two-op expansion) and holds for every
`lowerThir` output.

The label checker `ctSafeJasmin` inspects only the index register of a
`stackLoad` / `stackStore`; every other op passes by the catch-all case of
`opIndexPublic`. A program without memory ops therefore passes the checker under
every labelling (`noMem_ctSafeJasmin`, `lowerThir_ctSafeJasmin`). These two
statements follow from the catch-all case alone and constrain no leakage of the
emitted code; `Dialects.ConstantTimeTrait` consumes them.

## Main results

* `lowerThir_noMem` — every `lowerThir` output satisfies `jComNoMem`.
* `jComNoMem_rename`, `lowerVarStep_noMem` — the invariant under renaming and
  under one lowering step.
* `noMem_ctSafeJasmin`, `lowerThir_ctSafeJasmin` — the checker accepts every
  program without memory ops, under every labelling.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ThirCTSafe

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate

/-! ## 1. A "no memory op" invariant -/

/-- An op is non-memory iff it is not `stackLoad` / `stackStore` — the only ops
    whose label check inspects an index register. -/
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

/-- The label checker accepts a `Com` with no memory op under any label context:
    every binding passes by `opIndexPublic_of_noMem`, and `ret` passes. -/
theorem noMem_ctSafeJasmin : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → (L : LabelCtxt Γ) →
    jComNoMem c = true → ctSafeJasmin c L = true
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, L, h => by
      simp_all [jComNoMem, ctSafeJasmin_var, ctSafeExprJasmin, opIndexPublic_of_noMem,
        noMem_ctSafeJasmin body]

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

/-! ## 3. The label checker accepts every `lowerThir` output -/

/-- The label checker `ctSafeJasmin` accepts every `lowerThir` output under every
    labelling, because the output has no memory op and every other op passes the
    catch-all case of `opIndexPublic`. -/
theorem lowerThir_ctSafeJasmin {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) (L : LabelCtxt Γ) :
    ctSafeJasmin (lowerThir c) L = true :=
  noMem_ctSafeJasmin (lowerThir c) L (lowerThir_noMem c)

end CatCrypt.Crypto.SecureCompilation.VIR.ThirCTSafe
