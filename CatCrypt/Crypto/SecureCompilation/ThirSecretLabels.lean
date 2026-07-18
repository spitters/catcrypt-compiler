/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirCTByConstruction
import CatCrypt.Crypto.Optimizer.SecretType

/-!
# Information-flow (secret-level) labelling over the `thirDialect` front IR

This module is **Phase 2** of the secure-compilation stack: an
information-flow (IF) secret/public labelling propagated through the front IR's
ops, with the per-program guarantee that **combines with the by-construction
constant-time (CT) result** of `ThirCTByConstruction`.

## What the IF system is, and why its CT obligation is vacuous here

An information-flow type system is an *enforcement mechanism*: it labels each
value `pub`(lic) or `sec`(ret), propagates the labels along the dataflow
(`opOutLevel` = join of the input labels — a secret input taints the output),
and then **discharges a CT obligation**: no `sec` value may reach a *control
surface* (a branch condition, a loop bound, a memory index). On a
branch-admitting front IR this obligation is the real content of the system.

Over `thirDialect` the obligation is discharged **vacuously by the language
restriction**: `ThirCTByConstruction` proves that NO `ThirOp` is a
data-dependent control or addressing node (`op_all_dataflow`) and `Com` itself
is straight-line SSA — so there *is* no control surface for any label to reach.
This is the formal statement of "restrict the language ⇒ the IF policy holds for
free": the labelling can assign secrets however it likes, and the CT policy
still holds, because the enforcement check ranges over an empty set of control
sites.

So this file makes two things concrete:

1. the **labelling itself** (`LabelCtxt`, `opOutLevel`, `labelCom`), the seed a
   richer (branch-admitting) front IR would *need* to enforce CT, and the seed
   `lowerThir` / the backend would carry down to the machine `PubPred`
   (the Phase-0 `CompilableCT` / `MachineConstantTime` target); and
2. the **Phase-2 guarantee** (`thir_ct_for_any_labelling`): for *any* labelling
   and *any* `Com thirDialect`, the program is CT by construction — i.e. the IF
   system's enforcement obligation is met regardless of the labels, because the
   language has no control surface.

The labelling reuses the two-point lattice `SecretLevel` (`pub ⊑ sec`, `join`
the IF combine, `join_mono` monotone) from `Optimizer/SecretType.lean` — the
same lattice the `jasminDialect` taint pass uses — so this front-IR labelling
and the mid-IR taint pass speak one vocabulary.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirSecretLabels

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy)
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
open CatCrypt.Crypto.SecureCompilation.ThirCTByConstruction
open CatCrypt.Crypto.Optimizer.SecretType
open CatCrypt.Crypto.Optimizer.SecretType (SecretLevel)
open CatCrypt.Crypto.Optimizer.SecretType.SecretLevel (join leq)

/-! ## 1. The label context

`LabelCtxt Γ` assigns one `SecretLevel` to every variable in the De Bruijn
context `Γ : Ctxt thirDialect`, parallel in shape to `Γ`. It is seeded from the
function's secret-parameter labels (the input bindings) and extended at each
binder by the propagated output level. -/

/-- A secret-level labelling: one `SecretLevel` per binding in `Γ`. -/
inductive LabelCtxt : Ctxt thirDialect → Type where
  /-- The empty labelling. -/
  | nil : LabelCtxt []
  /-- Extend a labelling by a head level. -/
  | cons {t : JasminTy} {Γ : Ctxt thirDialect} :
      SecretLevel → LabelCtxt Γ → LabelCtxt (t :: Γ)

namespace LabelCtxt

/-- Look up the secrecy level recorded for a variable. -/
def lookup {Γ : Ctxt thirDialect} {t : JasminTy} :
    Ctxt.Var Γ t → LabelCtxt Γ → SecretLevel
  | .here,    .cons s _ => s
  | .there v, .cons _ L => lookup v L

end LabelCtxt

/-! ## 2. Per-op output label

The output label of an op given the labels of its arguments. The general rule is
the lattice join of the input labels (a `sec` input taints the output —
monotone via `SecretLevel.join_mono`). The exceptions:

* `thConst` is a nullary public compile-time constant ⇒ `pub`;
* `thEqLit a == k` compares against a *public* compile-time constant `k`, so its
  output carries exactly the label of its single argument (the join of one
  input);
* `thExtCall` is a leaf primitive call: conservatively the join of its inputs
  (the callee may *declassify*, but that is the callee's separate obligation, not
  something the front may assume — so the front never *lowers* below the join). -/

/-- Fold the lattice join over a `List SecretLevel` of input labels, starting from
    `pub` (the join identity). A `sec` anywhere makes the fold `sec`. -/
def joinLevels : List SecretLevel → SecretLevel
  | [] => .pub
  | s :: rest => join s (joinLevels rest)

/-- The output label of an op given its input labels. The join of the inputs
    (`sec` input ⇒ `sec` output), except `thConst`, which is a public constant. -/
def opOutLevel : ThirOp → List SecretLevel → SecretLevel
  | .thConst _ _, _ => .pub
  | _,            ins => joinLevels ins

/-! ### Basic facts about the output label -/

/-- `joinLevels` is monotone in each entry: a pointwise-`⊑ₛ` list of labels yields
    a `⊑ₛ` join. Used to show propagation is monotone. -/
theorem joinLevels_mono :
    ∀ {xs ys : List SecretLevel}, List.Forall₂ leq xs ys →
      leq (joinLevels xs) (joinLevels ys)
  | [], [], _ => SecretLevel.leq_refl _
  | _ :: _, _ :: _, .cons hh ht =>
      SecretLevel.join_mono hh (joinLevels_mono ht)

/-- A `thConst` output is always public, irrespective of (empty) inputs. -/
@[simp] theorem opOutLevel_const (w n : Nat) (ins : List SecretLevel) :
    opOutLevel (.thConst w n) ins = .pub := rfl

/-- For any non-`thConst` op the output label is the join of the inputs. -/
theorem opOutLevel_join (op : ThirOp) (ins : List SecretLevel)
    (h : ∀ w n, op ≠ .thConst w n) :
    opOutLevel op ins = joinLevels ins := by
  cases op <;> first | rfl | exact absurd rfl (h _ _)

/-- A public-only input list yields a public join — no taint is created from
    nothing (soundness of the public floor). -/
theorem joinLevels_all_pub :
    ∀ {xs : List SecretLevel}, (∀ s ∈ xs, s = .pub) → joinLevels xs = .pub
  | [], _ => rfl
  | s :: rest, h => by
      have hs : s = .pub := h s (by simp)
      have hr : joinLevels rest = .pub :=
        joinLevels_all_pub (fun x hx => h x (by simp [hx]))
      simp [joinLevels, hs, hr, SecretLevel.pub_join]

/-! ## 3. Argument labels and the per-expression output label

The labels of an op's argument variables, read off the label context, then fed to
`opOutLevel`. We collect the argument labels by folding lookup over the `HVector`
of argument variables (the same shape `argsTaint` uses in the jasmin pass). -/

/-- The list of secrecy levels of an `HVector` of argument variables. -/
def argLabels {Γ : Ctxt thirDialect} (L : LabelCtxt Γ) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → List SecretLevel
  | [], .nil => []
  | _ :: _, .cons v rest => (L.lookup v) :: (argLabels L rest)

/-- The output secrecy level of an expression under a labelling: feed its
    argument labels through `opOutLevel`. -/
def exprOutLevel {Γ : Ctxt thirDialect} {t : JasminTy}
    (L : LabelCtxt Γ) (e : Expr thirDialect Γ t) : SecretLevel :=
  opOutLevel e.op (argLabels L e.args)

/-! ## 4. Propagating labels through a straight-line program ⭐

`labelCom L c` returns the secrecy level of `c`'s result. It threads the
labelling down the `.var` chain: each binder extends the context with its
propagated output level `exprOutLevel L e`, and `.ret v` returns `v`'s label.
Total and monotone by construction (every binder's level is *defined* as the
join of its inputs). -/

/-- **Propagate secret labels through a straight-line `Com thirDialect`.** Each
    `.var e body` extends the labelling with the binder's output level
    `exprOutLevel L e` and recurses; `.ret v` returns `v`'s recorded label. -/
def labelCom {Γ : Ctxt thirDialect} {t : JasminTy}
    (L : LabelCtxt Γ) : Com thirDialect Γ t → SecretLevel
  | .ret v => L.lookup v
  | .var e body => labelCom (L.cons (exprOutLevel L e)) body

/-- The output label of a `.var` is `labelCom` of the body under the extended
    labelling — the defining unfold, exposed for downstream rewrites. -/
@[simp] theorem labelCom_var {Γ : Ctxt thirDialect} {t s : JasminTy}
    (L : LabelCtxt Γ) (e : Expr thirDialect Γ t) (body : Com thirDialect (t :: Γ) s) :
    labelCom L (.var e body) = labelCom (L.cons (exprOutLevel L e)) body := rfl

/-- The output label of a `.ret` is the returned variable's recorded label. -/
@[simp] theorem labelCom_ret {Γ : Ctxt thirDialect} {t : JasminTy}
    (L : LabelCtxt Γ) (v : Ctxt.Var Γ t) :
    labelCom L (.ret v) = L.lookup v := rfl

/-! ## 5. The Phase-2 guarantee ⭐

This is the formal statement that the IF system's CT obligation is discharged
*vacuously* by the language restriction. For **any** labelling and **any**
program, the program is constant-time by construction (`ComCTByConstruction`,
from `ThirCTByConstruction`) — because there is no control surface for any label
to reach. The labelling is computed (`labelCom`) but the CT verdict does not
depend on it: this is exactly "restrict the language ⇒ the IF policy holds for
free." -/

/-- **The Phase-2 guarantee: the IF CT obligation is vacuous over `thirDialect`.**
    For *any* label context `L` and *any* `Com thirDialect Γ t`, the program is
    constant-time by construction. The labelling `L` (and the propagated result
    label `labelCom L c`) is computed, but the CT verdict is independent of it:
    the front IR has no control surface, so no `sec` value can create a
    timing/address channel. This *combines* the by-construction CT result
    (`com_ct_by_construction`) with the IF labelling — the IF enforcement check
    ranges over an empty set of control sites and so succeeds for every labelling.
    The formal content of the "restrict the language to restrict branching and
    loops" security route. -/
theorem thir_ct_for_any_labelling {Γ : Ctxt thirDialect} {t : JasminTy}
    (L : LabelCtxt Γ) (c : Com thirDialect Γ t) : ComCTByConstruction c :=
  com_ct_by_construction c

/-- The label result is a genuine *function* of the labelling, while the CT
    verdict is *not* (Phase-2): for the *same* program two different labellings
    can give different result labels, yet both yield the *same* CT-by-construction
    proof. This pairing — `(labelCom L c, thir_ct_for_any_labelling L c)` — is the
    IF-system output: a propagated secrecy level plus the discharged CT
    obligation. -/
def labelAndCT {Γ : Ctxt thirDialect} {t : JasminTy}
    (L : LabelCtxt Γ) (c : Com thirDialect Γ t) :
    PProd SecretLevel (ComCTByConstruction c) :=
  ⟨labelCom L c, thir_ct_for_any_labelling L c⟩

/-! ## 6. The labelling is monotone (a `sec` seed only taints more) ⭐

The propagated result label is monotone in the seed labelling: raising an input
label can only raise (never lower) the result. This is the soundness property a
real IF system needs — declassification is the callee's job, the front never
silently lowers a secret. Proved from `opOutLevel`/`joinLevels` monotonicity and
threaded down the `.var` chain. -/

/-- Pointwise order on label contexts: `L ⊑ L'` if every variable's recorded
    level in `L` is `⊑ₛ` its level in `L'`. -/
def LabelLe {Γ : Ctxt thirDialect} (L L' : LabelCtxt Γ) : Prop :=
  ∀ {t : JasminTy} (v : Ctxt.Var Γ t), leq (L.lookup v) (L'.lookup v)

/-- `LabelLe` is reflexive. -/
theorem LabelLe.refl {Γ : Ctxt thirDialect} (L : LabelCtxt Γ) : LabelLe L L :=
  fun v => SecretLevel.leq_refl _

/-- Extending two ordered labellings by ordered head levels stays ordered. -/
theorem LabelLe.cons {Γ : Ctxt thirDialect} {th : JasminTy} {L L' : LabelCtxt Γ}
    {s s' : SecretLevel} (hs : leq s s') (hL : LabelLe L L') :
    LabelLe (Γ := th :: Γ) (L.cons s) (L'.cons s') := by
  intro u v
  cases v with
  | here => exact hs
  | there v' => exact hL v'

/-- `argLabels` is pointwise-monotone in the labelling. -/
theorem argLabels_mono {Γ : Ctxt thirDialect} {L L' : LabelCtxt Γ} (hL : LabelLe L L') :
    ∀ {tys : List JasminTy} (args : HVector (fun ty => Ctxt.Var Γ ty) tys),
      List.Forall₂ leq (argLabels L args) (argLabels L' args)
  | [], .nil => List.Forall₂.nil
  | _ :: _, .cons v rest => List.Forall₂.cons (hL v) (argLabels_mono hL rest)

/-- `opOutLevel` is monotone in the input labels (the join is monotone; `thConst`
    is the constant `pub`, trivially monotone). -/
theorem opOutLevel_mono (op : ThirOp) {ins ins' : List SecretLevel}
    (h : List.Forall₂ leq ins ins') :
    leq (opOutLevel op ins) (opOutLevel op ins') := by
  cases op <;>
    first
      | exact joinLevels_mono h
      | exact SecretLevel.leq_refl _

/-- `exprOutLevel` is monotone in the labelling. -/
theorem exprOutLevel_mono {Γ : Ctxt thirDialect} {t : JasminTy}
    {L L' : LabelCtxt Γ} (hL : LabelLe L L') (e : Expr thirDialect Γ t) :
    leq (exprOutLevel L e) (exprOutLevel L' e) :=
  opOutLevel_mono e.op (argLabels_mono hL e.args)

/-- **The propagated result label is monotone in the seed.** Raising the input
    labelling can only raise the program's result label — the IF soundness
    property: a more-secret seed never produces a less-secret result. Threaded
    down the `.var` chain, each binder's output level rises with the seed
    (`exprOutLevel_mono`), so the extended labelling stays ordered (`LabelLe.cons`)
    and the result label rises by induction. -/
theorem labelCom_mono {Γ : Ctxt thirDialect} {t : JasminTy} :
    ∀ {L L' : LabelCtxt Γ} (_ : LabelLe L L') (c : Com thirDialect Γ t),
      leq (labelCom L c) (labelCom L' c)
  | _, _, hL, .ret v => hL v
  | _, _, hL, .var e body =>
      labelCom_mono
        (LabelLe.cons (exprOutLevel_mono hL e) hL) body

/-! ## 7. Self-contained validation

A small `Com thirDialect [reg 32] (reg 32)`:

    let c0 = thConst 32 0        -- public constant
    let y  = thBin xor 32 x c0   -- y = x ^^^ 0,  label = sec ⊔ pub = sec
    ret y

With the single input `x` marked `sec`, the constant binder `c0` is labelled
`pub` (a `thConst`), and `y` is labelled `sec ⊔ pub = sec` (the secret `x`
taints it). The result label is `sec`. And — Phase 2 — the program is CT by
construction *regardless* of the labelling. -/

/-- The label context marking the single `[reg 32]` input `sec`. -/
def demoLabel : LabelCtxt [.reg 32] := .cons .sec .nil

/-- Demo program: `c0 = const 0; y = x xor c0; ret y` (over `[reg 32]`). -/
def demoLabelCom : Com thirDialect [.reg 32] (.reg 32) :=
  .var (.mk (.thConst 32 0) rfl .nil)
    (.var (.mk (.thBin .xor 32) rfl (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- The propagated result label of the demo is `sec`: the constant `c0` is `pub`,
    but the binder `y = x xor c0` joins the secret input `x`, so `y` (the result)
    is `sec`. -/
example : labelCom demoLabel demoLabelCom = .sec := by
  decide

/-- **Phase 2 on the demo: CT by construction holds regardless of the labelling.**
    The same `ComCTByConstruction` verdict holds whether the input is `sec`
    (`demoLabel`) or relabelled all-`pub` — the front IR has no control surface.
    Via `thir_ct_for_any_labelling`. -/
example : ComCTByConstruction demoLabelCom :=
  thir_ct_for_any_labelling demoLabel demoLabelCom

/-- The all-public relabelling gives a *different* result label (`pub`), yet the
    *same* CT verdict — making the Phase-2 independence concrete: the label is a
    function of the seed, the CT verdict is not. -/
example : labelCom (.cons .pub .nil) demoLabelCom = .pub := by
  decide

/-- The label functor is monotone on the demo: the all-public seed's result
    (`pub`) is `⊑ₛ` the `sec`-input seed's result (`sec`). Via `labelCom_mono`. -/
example :
    leq (labelCom (.cons .pub .nil) demoLabelCom) (labelCom demoLabel demoLabelCom) :=
  labelCom_mono (by
    intro u v
    cases v with
    | here => trivial
    | there v' => cases v') demoLabelCom

end CatCrypt.Crypto.SecureCompilation.ThirSecretLabels
