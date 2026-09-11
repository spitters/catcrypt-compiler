/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
public import CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
public meta import CatCrypt.Crypto.SecureCompilation.VIR.MergeCom
public import CatCrypt.Crypto.SecureCompilation.VIR.MergeCom

/-!
# `RupicolaField`: a shift-free authoring layer over the high `fieldDialect`

`RelationalCompileHigh.lean` gives the relational-compilation *engine* over the
high algebraic dialect (`FieldOp` on `FieldTy.fp p`): the atomic op-fragment
`bindOp`, the state-step `fOpStep`, and the compilation lemmas
`FRefines.{fieldOp,seq,skip}`. But authoring a kernel *through* that engine today
means hand-composing `bindOp` chains while **manually tracking De Bruijn
shifts**: every `let`-binding pushes a value at index `0`, so all previously
bound variables move up by one, and the author must sprinkle `.there` over every
back-reference (see `RelationalCompileHigh.Demo.dotFrag` — `m2 = c*d` reads
`.there vc`/`.there vd`, and `s = m1+m2` reads `.there .here`/`.here`).

This module removes that bookkeeping. It is the high-dialect analogue of
`RelationalCompile.lean`'s `rupicola`/`scont_peel` driver, but instead of a
binder-re-association *tactic* it provides a **type-safe combinator API**
(`mul`/`add`/`sub`/`neg`/`ret` over a builder) that threads the De Bruijn growth
behind a `Ctxt.Hom` weakening, so the author **never writes a single `.there`**.

## The key abstraction: a portable variable reference (`FRef`)

A `Ctxt.Var Γ t` is tied to the *exact* context `Γ`; once the context grows to
`s :: Γ`, the same logical value is renamed `.there v`. We make references
**context-polymorphic**:

    FRef Γ t := {Δ} → Ctxt.Hom Γ Δ → Var Δ t

An `FRef` is "a variable that knows how to weaken itself into any extension of
`Γ`". A combinator hands each operand `FRef` the one-step weakening
`Ctxt.Hom.weakenOne` as the context grows, and the `FRef` applies it — *that* is
where the `.there` shifts now live, generated mechanically, never typed by the
author.

## The builder (`FBuilder`)

`FBuilder Γ` packages, for a starting context `Γ`:

* `Δ`        — the output context after this builder's bindings,
* `frag`     — the assembled CPS `FFrag Γ Δ`,
* `spec`     — the assembled algebraic `FStateStep Γ Δ`,
* `refines`  — a *proof* `FRefines spec frag`, assembled by `FRefines.seq`.

A bound value is referenced by an `FRef b.Δ t` — portable from the builder's
*current* output context. Each combinator (`mul`, `add`, …) takes its operands as
`FRef b.Δ`s, appends one `bindOp`, and returns the new builder whose output
context has grown by one. The freshly bound result is `FRef.head`; older refs are
re-weakened (one `.there`) by passing them through `FRef.shift` — both supplied
by the API, so the author never writes `.there`.

## Demonstrations

* `dotProg2` — the 2-element dot `a*b + c*d`, reproducing
  `RelationalCompileHigh.Demo` **without any `.there`**.
* `dotProg4` — a 4-element dot `a*b + c*d + e*f + g*h` (a larger example whose
  hand-written `.there` chain would be substantial), authored shift-free.

Each comes with the engine's `FRefines` proof (read off the builder) **and** a
small closed-form `denote = …` lemma, plus a single-element `ZMod 7`
`example` (one tiny field evaluation — safe for the shared LSP).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RupicolaField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh

/-! ## 1. Portable (context-polymorphic) variable references -/

/-- A **portable variable reference**: a variable of type `t` valid in context
    `Γ` that knows how to weaken itself into *any* extension `Δ` of `Γ` via a
    supplied homomorphism. This is the abstraction that hides the De Bruijn
    `.there` shifts: instead of carrying a fixed `Var Γ t` and re-shifting it by
    hand each time the context grows, an `FRef` is applied to the current
    weakening `Ctxt.Hom Γ Δ` and yields the correctly-shifted `Var Δ t`. -/
abbrev FRef (Γ : Ctxt fieldDialect) (t : FieldTy) : Type :=
  {Δ : Ctxt fieldDialect} → Ctxt.Hom Γ Δ → Ctxt.Var Δ t

/-- The portable reference for a variable already in context `Γ`: apply the
    weakening hom to its concrete `Var`. Used to introduce the kernel's inputs. -/
def FRef.ofVar {Γ : Ctxt fieldDialect} {t : FieldTy} (v : Ctxt.Var Γ t) :
    FRef Γ t :=
  fun h => h v

/-- The portable reference for the **most-recently bound** value (De Bruijn index
    `0`): weaken `.here`. This is what a combinator returns as the handle on the
    value it just bound. -/
def FRef.head {Γ : Ctxt fieldDialect} {s : FieldTy} :
    FRef (s :: Γ) s :=
  fun h => h .here

/-- Re-weaken a reference across **one** fresh binding `s`: turn an `FRef Γ t`
    into an `FRef (s :: Γ) t`. This is the single place a `.there` is introduced
    — through `Ctxt.Hom.weakenOne` composed under the hom — so authors thread old
    handles forward by `FRef.shift` instead of writing `.there` by hand. -/
def FRef.shift {Γ : Ctxt fieldDialect} {s t : FieldTy}
    (r : FRef Γ t) : FRef (s :: Γ) t :=
  fun h => r (h.comp (Ctxt.Hom.weakenOne Γ s))

/-! ## 2. The builder

`FBuilder Γ` is a straight-line `fieldDialect` program *under construction* from
context `Γ`, bundled with everything needed to keep authoring and to discharge
the refinement: the output context `Δ`, the CPS fragment, its algebraic spec, and
the assembled `FRefines` proof. -/

/-- A partially-built straight-line field program from context `Γ`. -/
structure FBuilder (Γ : Ctxt fieldDialect) where
  /-- The output context after the bindings emitted so far. -/
  Δ : Ctxt fieldDialect
  /-- The assembled CPS fragment (emits the `Δ`-extra bindings). -/
  frag : FFrag Γ Δ
  /-- The assembled algebraic state-step the fragment refines. -/
  spec : FStateStep Γ Δ
  /-- The refinement proof, assembled bottom-up by `FRefines.seq`. -/
  refines : FRefines spec frag

/-- The empty builder: emit nothing, identity spec. The base of every authored
    program; its output context is the input context unchanged. -/
def FBuilder.start (Γ : Ctxt fieldDialect) : FBuilder Γ where
  Δ := Γ
  frag := fun {_} k => k
  spec := fun V => V
  refines := FRefines.skip

/-! ## 3. The core combinator: bind one op

`bindStep` is the single internal engine move. Given a builder at `Δ`, an op, and
its arguments **as resolved `Var b.Δ`s**, it appends one `bindOp`, extends the
spec by the matching `fOpStep`, and extends the proof by
`FRefines.seq … (FRefines.fieldOp …)`. The output context grows by `ret op`. The
public combinators below resolve `FRef` operands (through the identity hom at
`b.Δ`) before calling this. -/

/-- Append one field op (arguments as resolved `Var b.Δ`s) to a builder,
    threading spec and proof automatically. The output context is
    `ret op :: b.Δ`. -/
def FBuilder.bindStep {Γ : Ctxt fieldDialect} (b : FBuilder Γ) (op : FieldOp)
    (args : HVector (fun ty => Ctxt.Var b.Δ ty)
              (DialectSignature.sig (d := fieldDialect) op)) :
    FBuilder Γ where
  Δ := DialectSignature.ret (d := fieldDialect) op :: b.Δ
  frag := fun {_} k => b.frag (bindOp op args k)
  spec := fun V => fOpStep op args (b.spec V)
  refines := FRefines.seq b.refines (FRefines.fieldOp op args)

/-- Resolve an `FRef` valid in the builder's output context to a concrete `Var`
    by applying the identity hom: `FRef b.Δ t → Var b.Δ t`. -/
def FRef.now {Γ : Ctxt fieldDialect} {t : FieldTy}
    (r : FRef Γ t) : Ctxt.Var Γ t :=
  r (Ctxt.Hom.id Γ)

/-! ## 4. Public algebraic combinators (shift-free)

Each combinator takes its operands as portable `FRef`s **valid in the builder's
current output context** `b.Δ`, resolves them with `FRef.now`, emits the op, and
returns the new builder. The freshly bound result is reachable as `FRef.head`;
operands needed again after this bind are carried forward by `FRef.shift`. No
caller ever writes `.there`. -/

/-- `b.mul x y`: bind `x * y : fp p`. -/
def FBuilder.mul {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp p)) : FBuilder Γ :=
  b.bindStep (.fMul p) (.cons x.now (.cons y.now .nil))

/-- `b.add x y`: bind `x + y : fp p`. -/
def FBuilder.add {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp p)) : FBuilder Γ :=
  b.bindStep (.fAdd p) (.cons x.now (.cons y.now .nil))

/-- `b.sub x y`: bind `x - y : fp p`. -/
def FBuilder.sub {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x y : FRef b.Δ (FieldTy.fp p)) : FBuilder Γ :=
  b.bindStep (.fSub p) (.cons x.now (.cons y.now .nil))

/-- `b.neg x`: bind `-x : fp p`. -/
def FBuilder.neg {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (x : FRef b.Δ (FieldTy.fp p)) : FBuilder Γ :=
  b.bindStep (.fNeg p) (.cons x.now .nil)

/-! ## 5. Closing the builder: read off the program + its proof

A built program returns its last binding (`ret .here`). `toProg` reads off the
`Com`, `toRefines` the assembled `FRefines` proof. The author writes neither a
`Com.denote` blast nor a spec — both are synthesized by the builder. -/

/-- Close a builder whose last bind has type `s` by returning that value:
    the full `Com fieldDialect Γ s`. -/
def FBuilder.toProg {Γ : Ctxt fieldDialect} {s : FieldTy}
    (b : FBuilder Γ) (hd : b.Δ = s :: b.Δ.tail) :
    Com fieldDialect Γ s :=
  b.frag (hd ▸ Com.ret .here)

/-! ## 6. Demonstration A — 2-element dot, shift-free

The kernel `a*b + c*d` over `ZMod p`, authored with the combinators. Compare
`RelationalCompileHigh.Demo.dotFrag`: there the author wrote `.there vc`,
`.there vd`, `.there .here`. Here references are `FRef`s, threaded by
`FRef.head`/`FRef.shift`; no `.there` appears. -/

namespace Demo2

variable {p : Nat}

/-- Inputs `a, b, c, d` in the base context `[fp,fp,fp,fp]`. -/
abbrev Γ₀ (p : Nat) : Ctxt fieldDialect :=
  [FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p]

def a : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar .here
def b : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there .here)
def c : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there (.there .here))
def d : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there (.there (.there .here)))

/-- The 2-element dot, built shift-free.

    * `b1 = mul a b`  binds `m1`; result handle is `FRef.head`.
    * `b2 = mul c d`  binds `m2`; `c`/`d` are shifted once (`FRef.shift`) past
      `m1`'s binding; result handle is `FRef.head`.
    * `add m1 m2`     where `m1` is `FRef.head` from `b1` shifted once past `m2`
      (`FRef.shift FRef.head`), `m2` is `FRef.head` of `b2`.

    Every reference is `FRef.head`/`FRef.ofVar`/`FRef.shift`. No `.there`. -/
def builder (p : Nat) : FBuilder (Γ₀ p) :=
  let b1 := (FBuilder.start (Γ₀ p)).mul a b
  let b2 := b1.mul (FRef.shift c) (FRef.shift d)
  b2.add (FRef.shift FRef.head) FRef.head

/-- The closed kernel program. -/
def dotProg2 (p : Nat) : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  (builder p).toProg rfl

/-- **The kernel refines its (auto-synthesized) state-step** — read straight off
    the builder. The spec was assembled by the combinators via `FRefines.seq` /
    `FRefines.fieldOp`; the author supplied no spec and no `.there`. -/
theorem dotProg2_refines (p : Nat) :
    FRefines (builder p).spec (builder p).frag :=
  (builder p).refines

/-- **Closed-form denotation** — the small `rfl`-checkable verification: on
    inputs `a,b,c,d : ZMod p`, the shift-free program denotes `a*b + c*d`. -/
theorem dotProg2_denote (p : Nat) (av bv cv dv : ZMod p) :
    (dotProg2 p).denote
        ((.cons av (.cons bv (.cons cv (.cons dv .nil)))) :
          Ctxt.Valuation (Γ₀ p))
      = av * bv + cv * dv := by
  rfl

end Demo2

/-! ## 7. Demonstration B — 4-element dot, shift-free (the larger example)

`a*b + c*d + e*f + g*h` over `ZMod p`. By hand this needs an eight-deep `.there`
chain whose indices change at every accumulation step — exactly the bookkeeping
the builder removes. -/

namespace Demo4

variable {p : Nat}

/-- Eight prime-field inputs `a..h`. -/
abbrev Γ₀ (p : Nat) : Ctxt fieldDialect :=
  [FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p,
   FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p]

def a : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar .here
def b : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there .here)
def c : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there (.there .here))
def d : FRef (Γ₀ p) (FieldTy.fp p) := FRef.ofVar (.there (.there (.there .here)))
def e : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar (.there (.there (.there (.there .here))))
def f : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar (.there (.there (.there (.there (.there .here)))))
def g : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar (.there (.there (.there (.there (.there (.there .here))))))
def h : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar (.there (.there (.there (.there (.there (.there (.there .here)))))))

/-- The 4-element dot, built shift-free. Each product `mul · ·` shifts its inputs
    past the bindings accumulated so far via repeated `FRef.shift`; each running
    sum reads the previous accumulator (`FRef.head` shifted once over the new
    product) and the new product (`FRef.head`). No `.there` anywhere. -/
def builder (p : Nat) : FBuilder (Γ₀ p) :=
  -- m1 = a*b
  let b1 := (FBuilder.start (Γ₀ p)).mul a b
  -- m2 = c*d  (shift c,d once past m1)
  let b2 := b1.mul (FRef.shift c) (FRef.shift d)
  -- acc1 = m1 + m2  (m1 = head of b1 shifted past m2; m2 = head of b2)
  let b3 := b2.add (FRef.shift FRef.head) FRef.head
  -- m3 = e*f  (shift e,f past m1,m2,acc1 — three binds)
  let b4 := b3.mul (FRef.shift (FRef.shift (FRef.shift e)))
                   (FRef.shift (FRef.shift (FRef.shift f)))
  -- acc2 = acc1 + m3  (acc1 = head of b3 shifted past m3; m3 = head of b4)
  let b5 := b4.add (FRef.shift FRef.head) FRef.head
  -- m4 = g*h  (shift g,h past five binds: m1,m2,acc1,m3,acc2)
  let b6 := b5.mul
    (FRef.shift (FRef.shift (FRef.shift (FRef.shift (FRef.shift g)))))
    (FRef.shift (FRef.shift (FRef.shift (FRef.shift (FRef.shift h)))))
  -- acc3 = acc2 + m4
  b6.add (FRef.shift FRef.head) FRef.head

/-- The closed 4-dot kernel. -/
def dotProg4 (p : Nat) : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  (builder p).toProg rfl

/-- **The 4-dot kernel refines its auto-synthesized state-step.** -/
theorem dotProg4_refines (p : Nat) :
    FRefines (builder p).spec (builder p).frag :=
  (builder p).refines

/-- **Closed-form denotation**: the shift-free program denotes the 4-element dot
    `a*b + c*d + e*f + g*h`. -/
theorem dotProg4_denote (p : Nat)
    (av bv cv dv ev fv gv hv : ZMod p) :
    (dotProg4 p).denote
        ((.cons av (.cons bv (.cons cv (.cons dv
          (.cons ev (.cons fv (.cons gv (.cons hv .nil)))))))) :
          Ctxt.Valuation (Γ₀ p))
      = av * bv + cv * dv + ev * fv + gv * hv := by
  rfl

end Demo4

/-! ## 8. Tiny `#eval`-style smoke checks (single small field elements)

One 4-element and one 8-element `ZMod 7` evaluation each — single field-element
computations, safe for the shared LSP (no bignum / NTT blow-up). -/

/-- `2*3 + 4*5 = 6 + 20 = 26 = 5 (mod 7)`. -/
example :
    (Demo2.dotProg2 7).denote
        (.cons (2 : ZMod 7) (.cons (3 : ZMod 7)
          (.cons (4 : ZMod 7) (.cons (5 : ZMod 7) .nil))))
      = (5 : ZMod 7) := by
  rfl

/-- `1*2 + 3*4 + 5*6 + 0*1 = 2 + 12 + 30 + 0 = 44 = 2 (mod 7)`. -/
example :
    (Demo4.dotProg4 7).denote
        (.cons (1 : ZMod 7) (.cons (2 : ZMod 7) (.cons (3 : ZMod 7)
          (.cons (4 : ZMod 7) (.cons (5 : ZMod 7) (.cons (6 : ZMod 7)
            (.cons (0 : ZMod 7) (.cons (1 : ZMod 7) .nil))))))))
      = (2 : ZMod 7) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.RupicolaField
