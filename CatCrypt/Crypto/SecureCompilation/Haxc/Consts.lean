/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxSpine
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

@[expose] public section

set_option autoImplicit false

/-!
# The constants of a layout bound in the source

A typed extraction reads a top-level constant of its crate (such as `ONES` in `mpn-hax`) as a
free variable, and the layout `σ` binds it in the source environment (`AbiLayout.consts`,
`AbiLayout.EnvOf`). `bindConsts σ.consts te` binds each constant whose value is an integer or a
Boolean at the head of `te` as a literal, `let k = lit; te`, typed as the occurrences of `k` in
`te` are typed. The typed front lowers such a binding to a scalar write, so the lowered body
reads no name the layout does not pass in a register.

From an environment that binds each constant to its value, the source reading of the bound
extraction is the source reading of `te` (`run_bindConsts`): the binding extends the
environment at a name by the value it already holds.

## Main results

* `constLit`, `bindConsts` — the literal of a constant and the binding of the constants.
* `bindConsts_nil` — no constant leaves the extraction unchanged.
* `run_bindConsts`, `run_bindConsts_of_envOf` — the source reading of the bound extraction is
  that of the extraction, from an environment binding every constant to its value.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open _root_.Hax (ImpExpr ImpLit TExpr TExprKind Value Env Builtins denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (tyAgree factNameTys texprFacts denoteSpine_letBind spineLetStep
  isLamE)

/-- The literal of a constant value: an integer or a Boolean. -/
def constLit : Value → Option ImpLit
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | _ => none

theorem ofLit_constLit {v : Value} {l : ImpLit} (h : constLit v = some l) : Value.ofLit l = v := by
  unfold constLit at h
  split at h <;> cases h <;> rfl

/-- The constants `cs` bound at the head of `te`: for each constant `(k, v)` with a literal,
    `let k = lit; te`, the literal typed by the types of the occurrences of `k` in `te`. -/
def bindConsts : List (String × Value) → TExpr → TExpr
  | [], te => te
  | (k, v) :: cs, te =>
    let te' := bindConsts cs te
    match constLit v with
    | some l => .mk (.letBind k (.mk (.lit l) (tyAgree (factNameTys (texprFacts te) k))) te')
        te'.ty
    | none => te'

theorem bindConsts_nil (te : TExpr) : bindConsts [] te = te := rfl

/-- An environment extended at a name by the value it holds there is unchanged. -/
theorem extend_of_eq {env : Env} {k : String} {v : Value} (h : env k = some v) :
    env.extend k v = env := by
  funext x
  simp only [Env.extend]
  split
  · rename_i hx
    rw [beq_iff_eq] at hx
    subst hx
    exact h.symm
  · rfl

/-- **The bound extraction reads as the extraction.** From an environment binding every
    constant of `cs` to its value, the source reading of `bindConsts cs te` is that of
    `te`. -/
theorem run_bindConsts (bi : Builtins) (fuel : Nat) (te : TExpr) :
    ∀ (cs : List (String × Value)) (env : Env), (∀ c ∈ cs, env c.1 = some c.2) →
      (denoteSpine bi fuel (bindConsts cs te).erase).run env =
        (denoteSpine bi fuel te.erase).run env
  | [], _, _ => rfl
  | (k, v) :: cs, env, hc => by
    have ih := run_bindConsts bi fuel te cs env fun c hc' => hc c (List.mem_cons_of_mem _ hc')
    simp only [bindConsts]
    split
    · rename_i l hl
      have hk : env k = some v := hc (k, v) List.mem_cons_self
      rw [TExpr.erase, TExpr.erase, denoteSpine_letBind bi fuel k _ _ rfl]
      unfold constLit at hl
      split at hl <;> cases hl <;> rw [denote']
      · show (denoteSpine bi fuel (bindConsts cs te).erase).run (env.extend k (.int _)) = _
        rw [extend_of_eq hk]
        exact ih
      · show (denoteSpine bi fuel (bindConsts cs te).erase).run (env.extend k (.bool _)) = _
        rw [extend_of_eq hk]
        exact ih
    · exact ih

/-- **The bound extraction reads as the extraction, at a layout.** From an environment the
    layout `σ` reads off an entry state, the source reading of `bindConsts σ.consts te` is that
    of `te`. -/
theorem run_bindConsts_of_envOf (bi : Builtins) (fuel : Nat) (te : TExpr) {σ : AbiLayout}
    {sa : CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState} {env : Env}
    (h : σ.EnvOf sa env) :
    (denoteSpine bi fuel (bindConsts σ.consts te).erase).run env =
      (denoteSpine bi fuel te.erase).run env :=
  run_bindConsts bi fuel te σ.consts env h.2.1

end CatCrypt.Crypto.SecureCompilation.Haxc
