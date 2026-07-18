/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# A relational-compilation layer over the HIGH algebraic dialect (`fieldDialect`)

This module is the **one-level-up** analogue of `RelationalCompile.lean`. Where
that engine assembles "the emitted `Com jasminDialect` program denotes its spec"
proofs over the *low* register-file substrate (`Sha2Emit.emitOp`, the
slot/input `View`, `JasminBinOp`), this engine assembles "the emitted
`Com fieldDialect` program denotes its spec" proofs over the **high algebraic
substrate** — the prime-field / extension-tower op set
(`FieldDialect.FieldOp`: `fAdd`/`fMul`/`fInv`/`ext2Mul`/…), whose denotation is
the abstract field value (`ZMod p`, `Fp2Val p`, …).

The motivation (the architecture goal): rather than hand-authoring a kernel as a
`Com jasminDialect` register schedule, an author writes the kernel as an
**algebraic SPEC** and *relationally compiles* it to `Com fieldDialect` here —
the highest dialect — and only then regular-compiles down
(`FieldLowering → ModArith → … → jasmin`, the verified descent in
`DialectLoweringChain.lean`). This file provides the missing top layer of that
two-stage flow.

## The substrate difference vs the low engine

The low jasmin emitters are continuation-passing over a *mutable register file*:
a fragment writes a result to a slot index and is parameterised by an
environment, so it is genuinely context-polymorphic. The Field dialect's `Com`
instead grows a **De Bruijn context**: each `Com.var e body` binds the result of
`e` at index `0` and continues with the context extended by that result. So a
field-op fragment is **tied to the context its argument variables live in** (a
`Ctxt.Var Γ t` only makes sense at `Γ`); it is not `Γ`-polymorphic. The
"machine state" the spec transforms is the `Ctxt.Valuation` of that context, and
a fragment's effect is to *push one field value* (at De Bruijn index `0`) onto
the valuation.

We therefore model, **per starting context `Γ`**:

* `FView Γ := Ctxt.Valuation Γ` — the abstract machine state is the valuation.
* `FStateStep Γ t := FView Γ → FView (t :: Γ)` — a step pushes the field value
  computed by one op.
* `FRefines spec frag` says the CPS fragment `frag` (which binds one op and
  hands the extended context to its continuation) denotes its continuation
  applied to the spec-transformed valuation. Sequencing threads the context
  (`Γ → t₁ :: Γ → t₂ :: t₁ :: Γ → …`) explicitly.

## What is proved

* `FRefines.fieldOp` — the atomic compilation lemma: a single `bindOp`
  fragment refines `fOpStep`. (The high-dialect analogue of `Refines.arith`;
  here it is `rfl` because the Field `Com.denote` *is* the valuation extension.)
* `FRefines.seq` — the composition rule: sequencing two op-fragments composes
  their state-steps. (The analogue of `Refines.seq`.)
* `FRefines.skip` — the identity/base case.

## The demonstrated kernel

A two-element **field dot product** `dot a b c d = a*b + c*d` over `ZMod p`,
relationally compiled to a four-binding `Com fieldDialect` and proved (1) to
refine its algebraic state-step via the assembled `seq`/`fieldOp` lemmas, and
(2) to denote exactly `a*b + c*d` — a small, `rfl`/`#eval`-checkable closed-form
lemma (NOT a full-kernel `native_decide`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-! ## 1. Views and state-steps over the Field dialect

The high-dialect "machine view" is the De Bruijn valuation itself: the list of
field values currently in scope. A fragment that emits one op pushes that op's
result onto the view (at De Bruijn index `0`). -/

/-- The abstract machine view at context `Γ`: the valuation of all field values
    currently in scope. (The high-dialect counterpart of the low engine's
    register-file `View`.) -/
abbrev FView (Γ : Ctxt fieldDialect) : Type := Ctxt.Valuation Γ

/-- A `FStateStep Γ Δ` is what an emitted field-op fragment does to the abstract
    view: it consumes the in-scope valuation at context `Γ` and produces a
    valuation at the *output* context `Δ` (the context after the fragment's
    bindings — `Δ = t :: Γ` for one op, growing further as ops are sequenced).
    This is the denotational spec of a `Com.var …` chain. -/
abbrev FStateStep (Γ Δ : Ctxt fieldDialect) : Type :=
  FView Γ → FView Δ

/-- The atomic state-step of binding op `op` applied to argument variables
    `args`: push `op`'s abstract denotation (read through the current view) onto
    the valuation. This is exactly the spec of `Com.var (Expr.mk op rfl args) …`
    — and equals what the Field `Com.denote` does on that binding. -/
def fOpStep {Γ : Ctxt fieldDialect} (op : FieldOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
              (DialectSignature.sig (d := fieldDialect) op)) :
    FStateStep Γ (DialectSignature.ret (d := fieldDialect) op :: Γ) :=
  fun V => V.extend (DialectDenote.denote (d := fieldDialect) op (Expr.lookupArgs args V))

/-! ## 2. The `FRefines` relation (denotational, high-dialect)

`FRefines spec frag` says: the CPS fragment `frag`, which binds one field op and
continues over the extended context, denotes its continuation applied to the
spec-transformed view. Mirrors `RelationalCompile.Refines`, but over the
`Com fieldDialect` substrate, where "advancing the state" = extending the
De Bruijn valuation rather than overwriting a register slot.

Both `spec` and `frag` are indexed by the *starting* context `Γ` and the
*output* context `Δ` (after the fragment's bindings). The fragment is a CPS
builder `frag : Com fieldDialect Δ s → Com fieldDialect Γ s`. -/

/-- A CPS fragment over `Com fieldDialect` from context `Γ` to context `Δ`:
    given the continuation program over the output context `Δ`, it produces the
    program over the current context `Γ` (emitting `Δ`'s extra bindings). For one
    op, `Δ = t :: Γ`; sequencing grows `Δ` further. -/
abbrev FFrag (Γ Δ : Ctxt fieldDialect) : Type :=
  {s : FieldTy} → Com fieldDialect Δ s → Com fieldDialect Γ s

/-- `FRefines spec frag`: the fragment `frag` (from `Γ` to `Δ`) denotes its spec
    `FStateStep Γ Δ`.

    For every result type `s`, view (valuation) `V`, and continuation `k`,
    running `frag k` on `V` denotes the same as running `k` on the view advanced
    by `spec`. Because the Field `Com.denote` is exact
    (`Com.var e body` denotes `body` on `V.extend (e.denote V)`), the
    existential of the low engine collapses to a clean equality: the advanced
    view is *literally* `spec V`. -/
def FRefines {Γ Δ : Ctxt fieldDialect}
    (spec : FStateStep Γ Δ) (frag : FFrag Γ Δ) : Prop :=
  ∀ {s : FieldTy} (V : FView Γ) (k : Com fieldDialect Δ s),
    (frag k).denote V = k.denote (spec V)

/-! ## 3. The atomic compilation lemma — `fieldOp`

The single-op fragment `bindOp op args` emits one `Com.var` with the field op
and hands the continuation the extended context. It refines `fOpStep op args`.
This is the high-dialect analogue of `Refines.arith` — but here the proof is
definitional, because the Field `Com.denote` *exactly* extends the valuation by
the op's denotation (no register file ⇒ no slot-disjointness side conditions). -/

/-- The one-op fragment builder: bind `op args` and continue. -/
def bindOp {Γ : Ctxt fieldDialect} (op : FieldOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
              (DialectSignature.sig (d := fieldDialect) op)) :
    FFrag Γ (DialectSignature.ret (d := fieldDialect) op :: Γ) :=
  fun k => Com.var (Expr.mk op rfl args) k

/-- **Field-op compilation lemma** (the atomic refinement). A single `bindOp`
    fragment refines `fOpStep`. Proof: `rfl` — `(Com.var e k).denote V` reduces
    to `k.denote (V.extend (e.denote V))`, and `e.denote V` is exactly the op's
    denotation read through `V` (the `retTy_eq = rfl` cast vanishes), which is
    precisely `fOpStep op args V`. -/
theorem FRefines.fieldOp {Γ : Ctxt fieldDialect} (op : FieldOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig op)) :
    FRefines (fOpStep op args) (bindOp op args) := by
  intro s V k
  rfl

/-! ## 4. The composition rule — `seq`

Sequencing two op-fragments composes their state-steps. The second fragment
binds onto the context the first produced (`Δ₁`), so it runs `Δ₁ → Δ₂`; the
composite runs `Γ → Δ₂` with spec `spec₂ ∘ spec₁`. This is the high-dialect
analogue of `Refines.seq`, and the De Bruijn context grows by every binding
(`Γ → Δ₁ → Δ₂`). -/

/-- **Sequencing compilation lemma** — the composition rule. If `frag₁` refines
    `spec₁` (`Γ → Δ₁`) and `frag₂` refines `spec₂` (`Δ₁ → Δ₂`), then sequencing
    them — `fun k => frag₁ (frag₂ k)` — refines `spec₂ ∘ spec₁` (`Γ → Δ₂`).

    Proof: unfold both refinements. `(frag₁ (frag₂ k)).denote V` rewrites by
    `h₁` to `(frag₂ k).denote (spec₁ V)`, then by `h₂` to
    `k.denote (spec₂ (spec₁ V))`. No existential threading is needed — the
    valuation *is* the state. -/
theorem FRefines.seq {Γ Δ₁ Δ₂ : Ctxt fieldDialect}
    {spec₁ : FStateStep Γ Δ₁} {spec₂ : FStateStep Δ₁ Δ₂}
    {frag₁ : FFrag Γ Δ₁} {frag₂ : FFrag Δ₁ Δ₂}
    (h₁ : FRefines spec₁ frag₁) (h₂ : FRefines spec₂ frag₂) :
    FRefines (fun V => spec₂ (spec₁ V)) (fun {s} k => frag₁ (frag₂ k)) := by
  intro s V k
  rw [h₁ V (frag₂ k), h₂ (spec₁ V) k]

/-- **Identity/skip compilation lemma** (the base of a `seq`-fold). The empty
    fragment (apply the continuation directly) refines the identity step. -/
theorem FRefines.skip {Γ : Ctxt fieldDialect} :
    FRefines (Γ := Γ) (Δ := Γ) (fun V => V) (fun {s} k => k) := by
  intro s V k
  rfl

/-! ## 5. Minimal demonstration: a 2-element field dot product

The kernel `dot a b c d = a*b + c*d` over `ZMod p`, relationally compiled to
a four-binding `Com fieldDialect`:

    let m1 = fMul a b      -- index 0
    let m2 = fMul c d      -- index 0 (shifts m1 to 1)
    let s  = fAdd m1 m2
    ret s

Input context `Γ₀ = [fp p, fp p, fp p, fp p]` holding `a, b, c, d` at De Bruijn
indices `0, 1, 2, 3`. We (1) build it with the engine's `bindOp`, (2) show it
refines the composite state-step assembled from `fieldOp`+`seq`, and (3) prove
the closed form `denote = a*b + c*d`. -/

namespace Demo

variable {p : Nat}

/-- The starting context: four prime-field inputs `a, b, c, d`. -/
abbrev Γ₀ (p : Nat) : Ctxt fieldDialect :=
  [FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p]

/-- The output context after the three bindings `m1, m2, s`. -/
abbrev Δout (p : Nat) : Ctxt fieldDialect :=
  FieldTy.fp p :: FieldTy.fp p :: FieldTy.fp p :: Γ₀ p

/-- De Bruijn variables for the four inputs `a,b,c,d` (indices `0,1,2,3`). -/
def va : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .here
def vb : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .there .here
def vc : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .there (.there .here)
def vd : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .there (.there (.there .here))

/-- The relationally-compiled dot-product fragment, authored entirely through
    the engine's `bindOp` fragment builders. Each `bindOp` binds one `FieldOp`
    and threads the De Bruijn context (`Γ₀ → m1::Γ₀ → m2::m1::Γ₀ → Δout`).

    * `m1 = a*b`  binds at idx 0; afterwards `a,b,c,d` shift to `1,2,3,4`.
    * `m2 = c*d`  reads `c,d` at the shifted indices (`.there vc`, `.there vd`).
    * `s  = m1+m2` reads `m1` at idx 1 (`.there .here`), `m2` at idx 0 (`.here`).
    -/
def dotFrag (p : Nat) : FFrag (Γ₀ p) (Δout p) :=
  fun {s} k =>
    bindOp (.fMul p) (.cons va (.cons vb .nil))
      (bindOp (.fMul p) (.cons (.there vc) (.cons (.there vd) .nil))
        (bindOp (.fAdd p) (.cons (.there .here) (.cons .here .nil)) k))

/-- The full program: the fragment closed with `ret` of the sum (idx 0). -/
def dotProg (p : Nat) : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  dotFrag p (Com.ret .here)

/-- The composite algebraic state-step the kernel refines, assembled from the
    three atomic `fOpStep`s. -/
def dotStep (p : Nat) : FStateStep (Γ₀ p) (Δout p) :=
  fun V =>
    fOpStep (.fAdd p) (.cons (.there .here) (.cons .here .nil))
      (fOpStep (.fMul p) (.cons (.there vc) (.cons (.there vd) .nil))
        (fOpStep (.fMul p) (.cons va (.cons vb .nil)) V))

/-- **The kernel refines its assembled state-step** — proved purely by composing
    `FRefines.fieldOp` with `FRefines.seq` (no `Com.denote` blast). This is the
    high-dialect "rupicola" assembly: the spec is built bottom-up from the
    atomic op lemmas. -/
theorem dotFrag_refines (p : Nat) : FRefines (dotStep p) (dotFrag p) :=
  FRefines.seq (FRefines.fieldOp (.fMul p) (.cons va (.cons vb .nil)))
    (FRefines.seq
      (FRefines.fieldOp (.fMul p) (.cons (.there vc) (.cons (.there vd) .nil)))
      (FRefines.fieldOp (.fAdd p) (.cons (.there .here) (.cons .here .nil))))

/-- **Closed-form denotation lemma** (the small, `rfl`-checkable verification).
    On inputs `a, b, c, d : ZMod p`, the relationally-compiled program denotes
    exactly the field dot product `a*b + c*d`. -/
theorem dotProg_denote (p : Nat) (a b c d : ZMod p) :
    (dotProg p).denote
        ((.cons a (.cons b (.cons c (.cons d .nil)))) : Ctxt.Valuation (Γ₀ p))
      = a * b + c * d := by
  rfl

end Demo

/-! ## 6. Tiny `#eval` smoke check (one small instance, NOT a kernel KAT)

Over `ZMod 7` with `a,b,c,d = 2,3,4,5`: `2*3 + 4*5 = 6 + 20 = 26 = 5 (mod 7)`.
This is a single 4-element field evaluation — safe to `#eval` (it does not blow
up the shared LSP the way a full bignum/NTT kernel would). -/

/-- Sanity: the demo program evaluates `2*3 + 4*5 = 5 (mod 7)`. -/
example :
    (Demo.dotProg 7).denote
        (.cons (2 : ZMod 7) (.cons (3 : ZMod 7)
          (.cons (4 : ZMod 7) (.cons (5 : ZMod 7) .nil))))
      = (5 : ZMod 7) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
