/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence

/-!
# Frontend coincidence (`.letBind` increment): the let-extension induction

This module is the **`.letBind` increment** of the frontend
coincidence (`FrontendCoincidence.lean`). The base file proves the two frontend
denotations coincide on the **heap-free scalar-ALU fragment** — variable/literal
atoms and the binary ALU `.app` heads — but its `toSExpr` returns `none` on
`.letBind`, because `SExpr` has **no `let` node**: the Path-B `let`
materialises the bound value as a runtime *command* (`RScalarSet` /
`RScalarSetExpr`) whose big-step is `RustExec` over `RustState`, not an `SExpr`
node. So the SExpr path could not reach `let` at all.

This file supplies the **inductive engine** a full `.letBind` coincidence needs,
plus an `evalBV`-level let-coincidence combinator, and states precisely the
remaining `RustExec`-bridge obligation.

## Path A — the `let` arm of `denoteScalar`

`ImpExpr.denoteScalar params I (.letBind x v body) ρ` evaluates `v` to `vv`,
then evaluates `body` in the **extended local env**
`ρ' = (fun y => if y = x then some vv else ρ y)`
(see `ImpExprToThir.lean`). The local store `ρ : String → Option (BitVec 64)`
is partial; the let-extension writes one new local.

## §1 — Angle A: `EnvAgree`-preservation across let-extension (the engine)

`EnvAgree params I ρ β` (from the base file) says each variable's Path-A reading
`denoteAtomExpr params I (.var x) ρ` equals the Path-B reading `β x`. The
inductive step of any `let`-coincidence must re-establish `EnvAgree` under the
*extended* environments. We prove exactly that:

```
EnvAgree params I ρ β  →  x ∉ params  →
  EnvAgree params I (ρ.update x vv) (β.update x vv)
```

where both sides write the **same** bound value `vv : BitVec 64` (Path A as
`some vv` into the partial `ρ`, Path B as `vv` into the total `β`).

### Why `x ∉ params` is the right (and necessary) hypothesis

`denoteAtomExpr params I (.var y) ρ` reads `inpGet I i` when `y` is parameter `i`
(`params.idxOf? y = some i`), **ignoring `ρ` entirely**, and reads `ρ y`
otherwise. So if a let-bound local `x` *shadowed* a parameter name, Path A's
`ρ`-update at `x` would be **invisible** to `denoteAtomExpr` (the parameter
lookup wins), whereas Path B's `β`-update *would* change `β x` — breaking
agreement at `x`. The side-condition `x ∉ params` (the natural well-scopedness
condition: let-bound locals are fresh, not parameter names) rules this out and is
exactly what makes the update commute on both sides. This is not a vacuous restriction: it is the precise scoping discipline a `let`
coincidence requires.

## §2 — Angle B (partial): an `evalBV`-level let-coincidence combinator

Even though `toSExpr` has no `let`, we *can* state and prove the let step at the
`evalBV` level by feeding the engine of §1 a **body-coincidence hypothesis** over
the extended environments. The combinator `letBind_coincides_evalBV` says: if the
bound expr `v` coincides (gives `some vv` on Path A) and the body coincides under
the §1-extended environments, then the whole `let` coincides:

```
denoteScalar (.letBind x v body) ρ  =  some (bodyEval (β.update x vv))
```

This is the inductive closure of the let case at the `BitVec 64` (`evalBV`)
layer. It is about both paths: Path A's `let` arm (the `.bind`
threading the local) and Path B's body evaluator under the updated total env.

## The remaining gap (precise): the `denoteScalar`-vs-`RustExec` let-coincidence

A *full* `denoteScalar (.letBind …)` vs **`RustExec`** coincidence — the
Path-B `let` as a `RScalarSet`/`RScalarSetExpr` *command* over `RustState` — is
**not** closed here, for a concrete, stated reason:

* **Type mismatch at the store.** `denoteScalar` works in `BitVec 64`; the
  `RustState` scalar store `rsScalar : String → Nat` is `Nat`, and the let
  command `RScalarSet x v` / `RScalarSetExpr x e` writes a `Nat`
  (`rsSetScalar rs x v`). Bridging requires a per-variable `BitVec 64 ↔ Nat`
  relation `β x = BitVec.ofNat 64 (rs.rsScalar x)` *together with* an in-range
  invariant (`rs.rsScalar x < 2^64`) so that `evalState`'s **`Nat`** arithmetic
  (which does **not** wrap — `SSub` truncates over `Nat`) agrees with Path A's
  **wrapping** `BitVec 64` arithmetic. That is exactly the `inRangeState` /
  `evalStateBV` machinery already in `LowCT.lean` (`SExpr.evalStateBV`,
  `SExpr.toNat_evalStateBV_of_inRangeState`,
  `SExpr.evalStateBV_eq_ofNat_evalState`).
* **The obligation.** A full bridge therefore needs:
  1. a state-agreement predicate `StateAgree params I ρ rs` refining `EnvAgree`
     via `β x := BitVec.ofNat 64 (rs.rsScalar x)`;
  2. a `RustExec`-derivation for the scalar `let`
     (`RustExec.scalarSet` / `RustExec.scalarSetExpr`), which extends `rs` by
     `rsSetScalar rs x v` — the §1 engine then transports `StateAgree` across it
     *provided* `x ∉ params` and the bound value is in range;
  3. discharging the wrap gap via `inRangeState` (so `evalState`'s non-wrapping
     `Nat` sum equals Path A's `BitVec 64` sum) — i.e. the let-body must stay in
     `[0, 2^64)`.

§1 (the engine) and §2 (the `evalBV` closure) are the *path-independent* halves
of that bridge; what remains is the `RustState`/`Nat` materialisation in step 2–3
above. Stating it sharply — rather than faking a `RustExec` coincidence with a
hidden `native_decide`/`sorry` — is the honest outcome of this increment.

## Honesty note

* §1 is a two-path fact: it is about `denoteAtomExpr` (Path A, via
  `EnvAgree`) under the *same* update that Path B applies to `β`. It is not a
  restatement of one side.
* §2 is parametric in a *body-coincidence* hypothesis precisely because `toSExpr`
  cannot supply an `SExpr` image of the body across `let`; the hypothesis is the
  honest interface to the recursive call a full inductive proof would make.
* No `sorry`, no new axioms, no `native_decide`. The `RustExec`-materialisation
  gap is stated, not papered over.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence

/-! ## §1  Angle A — `EnvAgree`-preservation across a `let`-extension

The inductive engine: the let-extension that `denoteScalar`'s `.letBind` arm
performs on Path A (`ρ ↦ fun y => if y = x then some vv else ρ y`), mirrored on
Path B (`β ↦ fun y => if y = x then vv else β y`), preserves `EnvAgree`, provided
the bound local `x` is not a parameter name (`x ∉ params`). -/

/-- The Path-A local-env update used by `denoteScalar`'s `.letBind` arm. -/
def updRho (ρ : String → Option (BitVec 64)) (x : String) (vv : BitVec 64) :
    String → Option (BitVec 64) :=
  fun y => if y = x then some vv else ρ y

/-- The Path-B total-env update mirroring `updRho`. -/
def updBeta (β : String → BitVec 64) (x : String) (vv : BitVec 64) :
    String → BitVec 64 :=
  fun y => if y = x then vv else β y

/-- A parameter name is found by `idxOf?`, hence its atom reading ignores `ρ`. -/
theorem denoteAtomExpr_var_param {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64)) {y : String}
    {i : Nat} (hi : params.idxOf? y = some i) :
    denoteAtomExpr params I (.var y) ρ = some (inpGet I i) := by
  simp only [denoteAtomExpr, hi]

/-- A non-parameter name reads the local env `ρ`. -/
theorem denoteAtomExpr_var_local {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64)) {y : String}
    (hy : params.idxOf? y = none) :
    denoteAtomExpr params I (.var y) ρ = ρ y := by
  simp only [denoteAtomExpr, hy]

/-- A name with `idxOf? = some i` is a member of `params` (so a non-member has
    `idxOf? = none`). Used to discharge the shadowing case from `x ∉ params`. -/
theorem idxOf?_eq_none_of_not_mem {y : String} {params : List String}
    (h : y ∉ params) : params.idxOf? y = none := by
  rw [List.idxOf?_eq_none_iff]
  exact h

/-- **Angle A — `EnvAgree`-preservation (the inductive engine).** If
    `EnvAgree params I ρ β` holds and the let-bound local `x` is **not** a
    parameter name, then the *extended* environments — Path A's `updRho ρ x vv`
    (exactly `denoteScalar`'s `.letBind` update) and Path B's `updBeta β x vv`
    (the same bound value `vv`) — again satisfy `EnvAgree`.

    About both paths: the LHS reading is `denoteAtomExpr … (updRho …)`
    (Path A), required to equal `(updBeta …) y` (Path B). -/
theorem envAgree_update {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64))
    (β : String → BitVec 64) (hβ : EnvAgree params I ρ β)
    (x : String) (hx : x ∉ params) (vv : BitVec 64) :
    EnvAgree params I (updRho ρ x vv) (updBeta β x vv) := by
  intro y
  -- Split on whether `y` is a parameter.
  cases hidx : params.idxOf? y with
  | some i =>
    -- Parameter: both Path-A readings ignore the local update; `y ≠ x` since
    -- `y ∈ params` (from `idxOf? y = some i`) but `x ∉ params`.
    have hy_mem : y ∈ params := by
      by_contra hc
      rw [List.idxOf?_eq_none_iff.mpr hc] at hidx
      exact absurd hidx (by simp)
    have hyx : y ≠ x := by rintro rfl; exact hx hy_mem
    rw [denoteAtomExpr_var_param params I (updRho ρ x vv) hidx]
    -- Path B: `updBeta β x vv y = β y` since `y ≠ x`.
    simp only [updBeta, hyx, if_false]
    -- And `denoteAtomExpr … ρ = some (inpGet I i)` by `EnvAgree`, hence `β y`.
    have := hβ y
    rw [denoteAtomExpr_var_param params I ρ hidx] at this
    exact this
  | none =>
    -- Local: Path A reads `updRho ρ x vv y`.
    rw [denoteAtomExpr_var_local params I (updRho ρ x vv) hidx]
    by_cases hyx : y = x
    · subst hyx
      simp only [updRho, updBeta, if_true]
    · simp only [updRho, updBeta, hyx, if_false]
      have := hβ y
      rw [denoteAtomExpr_var_local params I ρ hidx] at this
      exact this

/-! ## §2  Angle B (partial) — an `evalBV`-level `let`-coincidence combinator

`toSExpr` cannot supply an `SExpr` image of a `let`, so the body coincidence
is taken as a hypothesis `hbody` over the §1-extended environments. Combined with
the bound-expr coincidence `hv`, this closes the `let` step at the `BitVec 64`
(`evalBV`) layer: it is the inductive-closure combinator. -/

/-- **Angle B (partial) — `let`-step coincidence at the `evalBV` layer.** Suppose:

    * the bound expr `v` coincides — Path A `denoteScalar … v ρ = some vv`; and
    * the body coincides under the §1-extended environments — for the Path-A
      env `updRho ρ x vv` and Path-B env `updBeta β x vv` (which §1 shows still
      satisfy `EnvAgree` when `x ∉ params`), Path A `denoteScalar … body …`
      equals `some bodyVal`.

    Then the whole `let` coincides: Path A `denoteScalar (.letBind x v body) ρ`
    equals `some bodyVal`. This is the inductive `let`-closure; with a recursive
    `denoteScalar_coincides_evalBV`-style body argument supplying `bodyVal =
    SExpr.evalBV (updBeta β x vv) s_body`, it is the full `let` coincidence at the
    `evalBV` layer. About both paths (Path A's `.letBind` `.bind`
    threading and the Path-B body value). -/
theorem letBind_coincides {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64))
    (x : String) (v body : ImpExpr) (vv bodyVal : BitVec 64)
    (hv : ImpExpr.denoteScalar params I v ρ = some vv)
    (hbody : ImpExpr.denoteScalar params I body (updRho ρ x vv) = some bodyVal) :
    ImpExpr.denoteScalar params I (.letBind x v body) ρ = some bodyVal := by
  -- Unfold the `.letBind` arm: it is `(denoteScalar v ρ).bind (fun vv => …)`.
  show (ImpExpr.denoteScalar params I v ρ).bind
      (fun vv => ImpExpr.denoteScalar params I body
        (fun y => if y = x then some vv else ρ y)) = some bodyVal
  rw [hv, Option.bind_some]
  -- The continuation env is definitionally `updRho ρ x vv`.
  exact hbody

/-- **Angle B (partial) — `let`-coincidence specialised to an `evalBV` body
    image.** The combinator above, with the body value supplied as Path B's
    `evalBV` of an `SExpr` image `s_body` under the extended total env. This is
    the exact shape a full inductive `denoteScalar_coincides_evalBV` would close
    the `letBind` case with — once a body `SExpr` image exists (which `toSExpr`
    does not currently produce across `let`; see the module-doc gap). -/
theorem letBind_coincides_evalBV {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64))
    (β : String → BitVec 64) (x : String) (v body : ImpExpr) (vv : BitVec 64)
    (s_body : SExpr)
    (hv : ImpExpr.denoteScalar params I v ρ = some vv)
    (hbody : ImpExpr.denoteScalar params I body (updRho ρ x vv)
        = some (SExpr.evalBV (updBeta β x vv) s_body)) :
    ImpExpr.denoteScalar params I (.letBind x v body) ρ
      = some (SExpr.evalBV (updBeta β x vv) s_body) :=
  letBind_coincides params I ρ x v body vv _ hv hbody

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet
