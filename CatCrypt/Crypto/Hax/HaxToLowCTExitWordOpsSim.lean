/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSignedOpsSim
public import CatCrypt.Crypto.Hax.HaxToLowCTExitWordOps

/-!
# Simulation of the marshalled word calls computed in the scalar heap

`scalarizeExitIn` (`HaxToLowCTExitWordOps`) replaces a marshalled word call of the typed
exit front whose result is copied into the scalar name `x` by the assignment
`RScalarSetExpr x se` of the scalar expression of the call.  The passes
`scalarizeWordOps`, `scalarizeNarrowIn` and `scalarizeSignedIn` assign the same
expressions inside `RLetU64Zero x`, and the step lemmas of their constructs (`step_word`,
`step_narrow`, `step_cast`, `step_not`, `step_signed`, `step_signedCast`,
`step_residueCast`, `step_signedCmp`) are stated on that shape.  An assignment whose
expression does not read `x`, with `x` not a temporary, runs in `semScalar` as it runs
inside `RLetU64Zero x` (`semScalar_setExpr_letU64`); by `exitOpSExpr_reads` the expression
of a call reads only its arguments, so the step lemma of each construct is the simulation
lemma of its lowering by `scalarizeExitIn` (`semScalar_exitOp_letU64`).  The signed form of
a comparison (`scalarizeExitIn_cmp`) reads the two compared names (`signedCmpFix_reads`),
and `step_signedCmp` is its simulation lemma by the same bridge.

## Main results

* `evalBV_congr_off` — an expression not reading `x` evaluates alike under readers
  agreeing off `x`.
* `semLowerSExpr_upd` — the scalar-expression lowering commutes with writing a name it
  does not read.
* `semScalar_setExpr_letU64` — a scalar assignment not reading its destination runs as it
  does after the destination is zeroed.
* `semScalar_exitOp_letU64` — the same for the assignment of `exitOpSExpr` to a name other
  than the arguments.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar semScalar semLowerSExpr binNode envReader envReadU64 isTmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)

/-- An expression that does not read `x` evaluates alike under two readers agreeing off
    `x`. -/
theorem evalBV_congr_off {x : String} {β β' : String → BitVec 64}
    (hβ : ∀ y, y ≠ x → β y = β' y) : ∀ e : SExpr, sexprReads x e = false →
      e.evalBV β = e.evalBV β' := by
  intro e he
  induction e <;> simp_all [sexprReads, SExpr.evalBV]

theorem envUpd_upd_same (σ : SEnvScalar) (x : String) {t t' : CryptoTy} (v : ⟦t⟧)
    (w : ⟦t'⟧) : (σ.upd x v).upd x w = σ.upd x w := by
  funext s; simp only [SEnvScalar.upd]; split <;> rfl

theorem envUpd_comm (σ : SEnvScalar) {x y : String} (h : x ≠ y) {t t' : CryptoTy}
    (v : ⟦t⟧) (w : ⟦t'⟧) : (σ.upd x v).upd y w = (σ.upd y w).upd x v := by
  funext s; simp only [SEnvScalar.upd]; split <;> split <;> simp_all

/-- A binary node on operand names other than `x`, with `x` not a temporary, commutes
    with writing `x`. -/
theorem binNode_upd {x : String} (w : BitVec 64) (hxT : ¬ isTmpName x) (e : SEnvScalar)
    {na nb : String} (ha : na ≠ x) (hb : nb ≠ x) (c : Nat)
    (f : BitVec 64 → BitVec 64 → BitVec 64) :
    binNode (e.upd x (t := .sword 64) w) na nb c f =
      (binNode e na nb c f).map (fun p => (p.1.upd x (t := .sword 64) w, p.2.1, p.2.2)) := by
  have hne : tmpName c ≠ x := fun h => hxT (h ▸ ⟨c, rfl⟩)
  simp only [binNode, envReadU64, SEnvScalar.upd, if_neg ha, if_neg hb]
  split <;> simp [envUpd_comm _ hne]

/-- **Frame of the scalar-expression lowering.** On an expression that does not read `x`,
    with `x` not a temporary, `semLowerSExpr` commutes with writing `x`, and its result
    name is not `x`. -/
theorem semLowerSExpr_upd {x : String} (w : BitVec 64) (hxT : ¬ isTmpName x) :
    ∀ (e : SExpr) (σ : SEnvScalar) (cnt : Nat), sexprReads x e = false →
      semLowerSExpr (σ.upd x (t := .sword 64) w) cnt e =
        (semLowerSExpr σ cnt e).map (fun p => (p.1.upd x (t := .sword 64) w, p.2.1, p.2.2)) ∧
      ∀ p, semLowerSExpr σ cnt e = some p → p.2.1 ≠ x := by
  intro e
  induction e with
  | SVar y =>
      intro σ cnt he
      simp only [sexprReads, beq_eq_false_iff_ne, ne_eq] at he
      simp only [semLowerSExpr, envReadU64, SEnvScalar.upd, if_neg he]
      constructor
      · split <;> simp
      · intro p hp
        split at hp
        · cases hp; exact he
        · cases hp
  | SLit n =>
      intro σ cnt _
      have hne : tmpName cnt ≠ x := fun h => hxT (h ▸ ⟨cnt, rfl⟩)
      refine ⟨by simp [semLowerSExpr, envUpd_comm _ hne], fun p hp => ?_⟩
      simp only [semLowerSExpr, Option.some.injEq] at hp
      subst hp; exact hne
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro σ cnt he
      simp only [sexprReads, Bool.or_eq_false_iff] at he
      obtain ⟨ha1, ha2⟩ := iha σ cnt he.1
      simp only [semLowerSExpr, ha1]
      constructor
      · rcases h1 : semLowerSExpr σ cnt a with _ | ⟨e1, na, c1⟩
        · simp
        · obtain ⟨hb1, hb2⟩ := ihb e1 c1 he.2
          simp only [Option.map_some, hb1]
          rcases h2 : semLowerSExpr e1 c1 b with _ | ⟨e2, nb, c2⟩
          · simp
          · simp only [Option.map_some]
            exact binNode_upd w hxT e2 (ha2 _ h1) (hb2 _ h2) c2 _
      · intro p hp
        rcases h1 : semLowerSExpr σ cnt a with _ | ⟨e1, na, c1⟩
        · simp [h1] at hp
        · rcases h2 : semLowerSExpr e1 c1 b with _ | ⟨e2, nb, c2⟩
          · simp [h1, h2] at hp
          · simp only [h1, h2, binNode] at hp
            split at hp
            · simp only [Option.some.injEq] at hp; subst hp
              exact fun h => hxT (h ▸ ⟨c2, rfl⟩)
            · cases hp
  | _ => intro σ cnt _; simp [semLowerSExpr]

/-- **A scalar assignment not reading its destination.** `RScalarSetExpr x se` with `se`
    not reading `x`, and `x` not a temporary, runs in `semScalar` as it runs inside
    `RLetU64Zero x`. -/
theorem semScalar_setExpr_letU64 {x : String} (hxT : ¬ isTmpName x) {se : SExpr}
    (hse : sexprReads x se = false) (c : LowCT) (σ : SEnvScalar) :
    semScalar (.RLetU64Zero x (.RSeq (.RScalarSetExpr x se) c)) σ =
      semScalar (.RSeq (.RScalarSetExpr x se) c) σ := by
  have hβ : ∀ y, y ≠ x →
      envReader (σ.upd x (t := .sword 64) (0 : BitVec 64)) y = envReader σ y :=
    fun y hy => by simp [envReader, SEnvScalar.upd, hy]
  simp only [semScalar, (semLowerSExpr_upd 0 hxT se σ 0 hse).1, evalBV_congr_off hβ se hse]
  rcases semLowerSExpr σ 0 se with _ | ⟨e2, nm, c2⟩
  · rfl
  · simp [envUpd_upd_same]

/-- **The lowering of a marshalled word call runs as the passes' binding.** The
    assignment of `exitOpSExpr W I f xs` to a name `x` outside `xs` that is not a
    temporary runs in `semScalar` as the binding `RLetU64Zero x` of the same assignment,
    on which the step lemma of the construct `f` is stated. -/
theorem semScalar_exitOp_letU64 {W I : List String} {f x : String} {xs : List String}
    {se : SExpr} (h : exitOpSExpr W I f xs = some se) (hx : x ∉ xs) (hxT : ¬ isTmpName x)
    (c : LowCT) (σ : SEnvScalar) :
    semScalar (.RSeq (.RScalarSetExpr x se) c) σ =
      semScalar (.RLetU64Zero x (.RSeq (.RScalarSetExpr x se) c)) σ :=
  (semScalar_setExpr_letU64 hxT (exitOpSExpr_reads h hx) c σ).symm

end CatCrypt.Crypto.Hax
