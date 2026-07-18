/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
import CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective

/-!
# Whole-function lowering of a multi-binder straight-line `Com`, with **both**
# carried side-conditions discharged

`JasminPrintSemCorrect.lean` proves `lowerComToProg_sem_eq`: running the lowered
single-function `JasminProg` equals `Com.denote` on the straight-line fragment.
That theorem carries **three** hypotheses:

* `hLeaf : LeafAgrees leafSem` — the opaque-leaf edge (`extCall` agreement),
  carried throughout the emit-correctness theory and *not* dischargeable here
  (it is the genuine assumption about the leaf semantics);
* `hInj : Function.Injective freshName` — distinct fresh-SSA counters give
  distinct `"v…"` names;
* `hPinj` — the *parameter* resolver is injective (distinct parameters get
  distinct `"p…"` names), which makes the seeded store agree with the input.

The roadmap's whole-function keystone (#5) asks for a verified lowering of a
**multi-binder straight-line** body — more than the single-op bodies the loop
passes (`LoopLowering`) cover — that does **not** leave the SSA-naming
side-conditions as open holes.

## What was already there (reused, not re-proved)

* `JasminPrint.lowerComToProg` — the whole-function lowering `Com → JasminProg`.
* `JasminPrintSemCorrect.runProg` / `lowerComToProg_sem_eq` — the run + its
  denote-correctness on the straight-line fragment (the *body* of the keystone).
* `FreshNameInjective.freshName_injective` — discharges `hInj` (proved in that
  file from the base-10 `Nat.toDigits` recursion; the honest hurdle the
  loop-lowering agents flagged).
* `JasminDialect.smokeProg` — a concrete **two-binder** straight-line `Com`
  (`regArith add` then `castW 32 64`), used as the worked whole-function example.

## What is genuinely new here

1. **`paramsAndMapFrom_name`** — the closed form of the parameter resolver: the
   variable at De Bruijn depth `d` in `paramsAndMapFrom base Γ` is named
   `"p" ++ toString (base + d)`. (`paramsAndMap` = `base = 0`.)

2. **`paramsAndMapFrom_injective` / `paramsAndMap_injective`** — the parameter
   resolver is injective, **discharging `hPinj`**. This is the last SSA-naming
   side-condition; like `hInj` it bottoms out at `toString : Nat → String`
   injectivity, supplied by `FreshNameInjective.natToString_injective`. Equal
   names force equal depth (strip the constant `"p"` prefix, then `toString`
   injectivity), and equal depth in the same context forces the variables equal
   (with type equality) — proved by induction on `Γ`.

3. **`lowerComToProg_sem_eq'`** — `lowerComToProg_sem_eq` with **both** naming
   side-conditions discharged: the *only* remaining hypothesis is the opaque-leaf
   edge `LeafAgrees`. This is the clean whole-function statement: for any
   straight-line `Com Γ t`, running its lowered `JasminProg` equals
   `Com.denote`.

4. A worked **multi-binder** (two-op) example: `smokeProg`'s lowered function run
   equals its `Com.denote`, with no naming side-conditions
   (`smokeProg_run_eq`), and a concrete KAT (`smokeProg_run_kat`: `7, 35 ↦ 42`).

## Scope (honest)

This is the *whole-function* analogue of `LoopLowering`'s single-op case: a
**fixed-length, loop-free** straight-line body (several `Lopn`/`regArith`/`castW`
bindings, single return). It composes any number of binders — `smokeProg` is
two; the statement is generic in the body. It does **not** yet cover: control
flow / branches (`StructuredControlFlow`), function calls (`extCall` leaves stay
opaque under `LeafAgrees`), the aliasing `stackStore` op (excluded by
`StraightLine`, see `stackStore_aliases_source`), or composing the loop passes
into the same function body (a whole *protocol* body interleaves straight-line
fragments with the counted loops of `LoopLowering` and the nested loops of
`JForProgNested`). Those are the remaining whole-protocol-body work.

0 sorries; the only remaining hypothesis on the worked example is the opaque-leaf
edge `LeafAgrees`, the same edge carried throughout the emit-correctness theory.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective
open CatCrypt.Crypto.Jasmin (JasminProg)

/-! ## 1. The parameter resolver's closed form

`paramsAndMapFrom base Γ` names the variable at De Bruijn depth `d` (`.here` is
depth `0`, `.there` adds one) as `"p" ++ toString (base + d)`. We prove this by
induction on the variable, which simultaneously inducts on `Γ`. -/

/-- The name `paramsAndMapFrom base Γ` assigns to a variable is `"p" ++ toString k`
    for a counter `k ≥ base` (the depth offset by `base`). The exact value is the
    `here ↦ base`, `there ↦ +1` recursion; this records the *form* (a `"p…"`
    name) and that the counter is `≥ base`. -/
theorem paramsAndMapFrom_name :
    ∀ {Γ : Ctxt jasminDialect} (base : Nat) (t : jasminDialect.Ty)
      (v : Ctxt.Var Γ t),
      ∃ k, base ≤ k ∧ (paramsAndMapFrom base Γ).2 t v = "p" ++ toString k
  | _ :: _, base, _, .here => ⟨base, Nat.le_refl base, rfl⟩
  | _ :: rest, base, t, .there v' => by
      obtain ⟨k, hk, hname⟩ := paramsAndMapFrom_name (base + 1) t v'
      exact ⟨k, by omega, hname⟩

/-! ## 2. The parameter resolver is injective — discharging `hPinj`

If two parameters share a name, strip the constant `"p"` prefix and apply
`natToString_injective` to force equal counters; equal counters in the same
context (with `base` shifting in lockstep) force the variables equal up to the
type-equality witness. Induction on `Γ`. -/

/-- **The parameter resolver is injective.** Distinct parameters of
    `paramsAndMapFrom base Γ` get distinct `"p…"` names. This is the witness
    `lowerComToProg_sem_eq` needs for `hPinj`, discharged from
    `natToString_injective` (the same `toString`-injectivity machinery that
    discharges `hInj`). -/
theorem paramsAndMapFrom_injective {Γ : Ctxt jasminDialect} (base : Nat)
    (t t' : jasminDialect.Ty) (v : Ctxt.Var Γ t) (v' : Ctxt.Var Γ t')
    (h : (paramsAndMapFrom base Γ).2 t v = (paramsAndMapFrom base Γ).2 t' v') :
    (∃ heq : t = t', heq ▸ v = v') := by
  induction Γ generalizing base t t' with
  | nil => cases v
  | cons hdTy rest ih =>
      cases v with
      | here =>
          cases v' with
          | here =>
              -- Both `.here`: same head type, same variable.
              exact ⟨rfl, rfl⟩
          | there v'' =>
              -- `.here ↦ "p{base}"`, `.there v'' ↦ "p{k}"`, `k ≥ base + 1`:
              -- distinct counters ⇒ distinct names, contradiction.
              exfalso
              obtain ⟨k, hk, hname⟩ := paramsAndMapFrom_name (base + 1) t' v''
              have hhere : (paramsAndMapFrom base (hdTy :: rest)).2 hdTy Ctxt.Var.here
                  = "p" ++ toString base := rfl
              have hthere : (paramsAndMapFrom base (hdTy :: rest)).2 t' (.there v'')
                  = (paramsAndMapFrom (base + 1) rest).2 t' v'' := rfl
              rw [hhere, hthere, hname] at h
              have hbk : base = k := by
                have hd := congrArg String.toList h
                rw [String.toList_append, String.toList_append] at hd
                exact natToString_injective (String.toList_injective (List.append_cancel_left hd))
              omega
      | there v'' =>
          cases v' with
          | here =>
              -- Symmetric to the previous case.
              exfalso
              obtain ⟨k, hk, hname⟩ := paramsAndMapFrom_name (base + 1) t v''
              have hhere : (paramsAndMapFrom base (hdTy :: rest)).2 hdTy Ctxt.Var.here
                  = "p" ++ toString base := rfl
              have hthere : (paramsAndMapFrom base (hdTy :: rest)).2 t (.there v'')
                  = (paramsAndMapFrom (base + 1) rest).2 t v'' := rfl
              rw [hhere, hthere, hname] at h
              have hbk : base = k := by
                have hd := congrArg String.toList h.symm
                rw [String.toList_append, String.toList_append] at hd
                exact natToString_injective (String.toList_injective (List.append_cancel_left hd))
              omega
          | there v''' =>
              -- Both deeper: the names are the `base + 1` resolver's; apply IH and
              -- lift `.there` injectively.
              have hshift : ∀ (s : jasminDialect.Ty) (w : Ctxt.Var rest s),
                  (paramsAndMapFrom base (hdTy :: rest)).2 s (.there w)
                    = (paramsAndMapFrom (base + 1) rest).2 s w := fun _ _ => rfl
              rw [hshift, hshift] at h
              obtain ⟨he, hv⟩ := ih (base + 1) t t' v'' v''' h
              cases he
              exact ⟨rfl, by simpa using congrArg Ctxt.Var.there hv⟩

/-- **`paramsAndMap` is injective** (the `base = 0` instance): the canonical
    parameter resolver `p0, p1, …` assigns distinct names to distinct
    parameters. Discharges `hPinj` for `lowerComToProg_sem_eq`. -/
theorem paramsAndMap_injective {Γ : Ctxt jasminDialect} :
    ∀ (t t' : jasminDialect.Ty) (v : Ctxt.Var Γ t) (v' : Ctxt.Var Γ t'),
      (paramsAndMap Γ).2 t v = (paramsAndMap Γ).2 t' v' →
      (∃ h : t = t', h ▸ v = v') :=
  fun t t' v v' h => paramsAndMapFrom_injective 0 t t' v v' h

/-! ## 3. The whole-function keystone with **both** naming side-conditions
discharged

`lowerComToProg_sem_eq` carries `hInj` and `hPinj`; we discharge both — `hInj`
by `FreshNameInjective.freshName_injective`, `hPinj` by `paramsAndMap_injective`
— leaving the opaque-leaf edge `LeafAgrees` as the *only* remaining hypothesis.
This is the clean statement the whole-function keystone names. -/

/-- **Whole-function lowering is denotation-preserving (naming side-conditions
    discharged).** For any straight-line `Com jasminDialect Γ t`, running its
    lowered single-function `JasminProg` under a word-level evaluator equals
    `Com.denote com V`, provided only the opaque-leaf edge `hLeaf`. Both
    SSA-naming side-conditions of `lowerComToProg_sem_eq` (`hInj`, `hPinj`) are
    discharged internally (`freshName_injective`, `paramsAndMap_injective`). -/
theorem lowerComToProg_sem_eq' {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) (hSL : StraightLine com)
    (V : Ctxt.Valuation Γ) :
    runProg leafSem com V = com.denote V :=
  lowerComToProg_sem_eq hLeaf freshName_injective com hSL
    paramsAndMap_injective V

/-! ## 4. Worked multi-binder example: the two-op `smokeProg`

`JasminDialect.smokeProg : Com jasminDialect [reg 32, reg 32] (reg 64)` is a
genuine *multi-binder* (two `var`) straight-line body:

    let s = regArith add a b   -- s : reg 32
    let t = castW 32 64 s      -- t : reg 64
    ret t

so `denote ⟨a, b⟩ = (a + b).zeroExtend 64`. Its lowered whole function runs to
exactly that, with **no** naming side-conditions remaining. -/

/-- `smokeProg` is straight-line (both binders are non-`stackStore`). Local
    re-derivation of `JasminPrintSemCorrect.smokeProg_straightLine` so this file
    is self-contained on the example. -/
theorem smokeProg_straightLine : StraightLine JasminDialect.smokeProg := by
  refine ⟨fun w n h => ?_, fun w n h => ?_, trivial⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Worked multi-binder example.** Running the lowered two-op `smokeProg`
    whole function equals its `Com.denote`, with the only hypothesis the
    opaque-leaf edge `hLeaf` (vacuous here — no `extCall`). Instance of
    `lowerComToProg_sem_eq'`. -/
theorem smokeProg_run_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (V : Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 32, JasminTy.reg 32]) :
    runProg leafSem JasminDialect.smokeProg V
      = JasminDialect.smokeProg.denote V :=
  lowerComToProg_sem_eq' hLeaf JasminDialect.smokeProg smokeProg_straightLine V

/-- **Worked multi-binder KAT.** On inputs `7, 35`, the lowered `smokeProg`
    whole function computes `(42 : BitVec 32).zeroExtend 64` — byte-for-byte the
    reference `denote`. Ties the whole-function keystone to a concrete value. -/
theorem smokeProg_run_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    runProg leafSem JasminDialect.smokeProg
        (.cons (7 : BitVec 32) (.cons (35 : BitVec 32) .nil))
      = ((42 : BitVec 32).zeroExtend 64) := by
  rw [smokeProg_run_eq hLeaf]; rfl

end CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
