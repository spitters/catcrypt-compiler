/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering
public import Transfer.Congruence.HGCongr

/-!
# Closing the `rcongr` dispatch gaps with `@[hgcongr]` head-pair correspondences

## Scope

`RcongrLeafAutomation.lean` automated the **binary** arms of the
prime-field → ModArith op-lowering leaf `fpOpLowerTransports` with the
`Related`/`RelatedBinOp` cross-head rule `rcongrBinOp`, and documents
four dispatch gaps it could **not** close (its "Lessons" / §4):

1. the dependent `Expr`/`HVector` peel (`rcases e; cases op; match args`) is not
   relational congruence — it precedes any op-tree goal;
2. `rcongr`'s auto-descent tests `lhs.getAppNumArgs == 2`, which misses
   `modAddF a b` (3 app args including the implicit `{p}`);
3. `modAddF`/… are `@[reducible]`, so instance resolution unfolds them to `·+·`
   before keying, and the `modAddF`-keyed `RelatedBinOp` never fires;
4. the **unary** ops `fpNeg`/`fpInv` (`modNegF`/`byInverseF`) have **no**
   registry rule at all — the `Related` framework provides `RelatedBinOp` but no
   `RelatedUnaryOp`, so `rcongr` cannot strip a unary node; those two arms kept
   the dialect's hand `rw [mapVar_lookup]`.

This file closes the **congruence-dispatch** gaps (2)–(4) by registering the
dialect op-lowering correspondences as `@[hgcongr]` **head-pair** lemmas and
descending the leaves with `hgcongr` (`HGCongr.lean`). The head-pair key
`(relName, lhsHead, rhsHead)` is what sidesteps each gap:

* **Gap (4), unary — closed.** A `@[hgcongr]` lemma may have **any arity**:
  `modNegF a₁ = modNegF a₂` registers under the key `(Eq, modNegF, modNegF)` and
  `hgcongr` strips the unary node, leaving the single per-argument leaf. There is
  no binary-only restriction (no `RelatedUnaryOp` is needed — the attribute is
  arity-generic). This is the gap `rcongr` structurally could not reach.

* **Gap (2), implicit-arg dispatch — closed.** `hgcongr` does not use a
  `getAppNumArgs == 2` heuristic; it keys on the head pair read off the goal and
  recovers the varying argument pairs from the lemma's *hypotheses*
  (`makeHGCongrLemma`), so the implicit `{p}` (which makes `modAddF a b` a 3-arg
  application) is irrelevant — the lemma fires on `modAddF`.

* **Gap (3), `@[reducible]` head — sidestepped (with one caveat).** The
  head-pair key keys on the *pair* `(modNegF, modNegF)` / `(modAddF, modAddF)`,
  not on a single reducible head used for `RelatedBinOp` instance resolution, so
  it does not silently match the abstract `·+·` square with the wrong target.
  The caveat: because the leaf functions are `@[reducible]`, on the **diagonal,
  bare-variable** case (`modNegF a = modNegF a`) `gcongr` *also* succeeds (it
  unfolds to `Neg.neg` and its own homogeneous congruence fires). The
  separation from `gcongr` is the **differing-argument** dialect-leaf shape
  (`modNegF (transported-lookup) = modNegF (source-lookup)`): there `gcongr`
  makes **no progress** (no leaf to align under the unfolded head), while
  `hgcongr` descends to the per-argument coherence leaf. That is precisely the
  `fpOpLowerTransports` arm shape, demonstrated in §3.

**Gap (1) — the dependent `Expr`/`HVector` peel — is NOT closed here, and is not
a congruence-dispatch gap.** It is a *goal-shape* obstruction: the leaf starts as
`(lowerExpr e).denote (mapVal V) = transTy (e.denote V)`, an `Eq` of
`Expr.denote` applications, and only the `rcases e; subst; cases op; match args`
+ a body-`show` exposes a `modAddF …`/`modNegF …` op-tree. `hgcongr` — like
`rcongr`/`gcongr` — dispatches on the goal *head* and has no dependent-elimination
rule, so this prelude stays manual; `hgcongr` takes over **after** the `show`.
This file does not claim to close it.

So: `hgcongr`'s head-pair architecture closes the three congruence-dispatch gaps
`rcongr` documented — crucially the **unary** one — while the dependent peel
remains a goal-shape prelude. The deliverable below is the `@[hgcongr]` lemmas
(binary + unary) and a mixed binary/unary op-tree leaf discharged by `hgcongr`,
including the real `fpOpLowerTransports` arms.

**All goals closed**; ambient axiom set `{propext, Classical.choice, Quot.sound}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.HgcongrDialectLeaves

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
open Transfer

/-! ## 1. The dialect op-lowering correspondences as `@[hgcongr]` head-pair lemmas

Each prime-field op lowers 1:1 to its ModArith twin and the two denote to the
*same* leaf function (`fpAdd`↦`modAddF`, `fpNeg`↦`modNegF`, …), so under the
identity transport the op-lowering square is a **diagonal** head pair
`(modAddF, modAddF)` / `(modNegF, modNegF)`. The point is not that the heads
differ (they don't, on the 1:1 fragment) but that the **descent through the node
with differing arguments** — the transported-lookup vs source-lookup the dialect
leaf produces — needs a congruence rule that `rcongr` lacked for the unary ops
and mis-dispatched for the implicit-`{p}` binary ops.

Registering them `@[hgcongr]` keys each under `(Eq, head, head)` and makes
`hgcongr` strip the node at **any arity**: the two **unary** correspondences
(`modNegF`, `byInverseF`) are exactly what closes gap (4). -/

/-- **Binary** correspondence `modAddF` (key `(Eq, modAddF, modAddF)`). The
    implicit `{p}` that gave `rcongr` its 3-arg dispatch miss (gap 2) is
    irrelevant: `hgcongr` recovers the varying pairs from the hypotheses. -/
@[hgcongr]
theorem modAddF_hcongr {p : Nat} {a₁ b₁ a₂ b₂ : ZMod p}
    (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) : modAddF a₁ b₁ = modAddF a₂ b₂ := by
  subst h₁; subst h₂; rfl

/-- **Binary** correspondence `modSubF` (key `(Eq, modSubF, modSubF)`). -/
@[hgcongr]
theorem modSubF_hcongr {p : Nat} {a₁ b₁ a₂ b₂ : ZMod p}
    (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) : modSubF a₁ b₁ = modSubF a₂ b₂ := by
  subst h₁; subst h₂; rfl

/-- **Binary** correspondence `modMulF` (key `(Eq, modMulF, modMulF)`). -/
@[hgcongr]
theorem modMulF_hcongr {p : Nat} {a₁ b₁ a₂ b₂ : ZMod p}
    (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) : modMulF a₁ b₁ = modMulF a₂ b₂ := by
  subst h₁; subst h₂; rfl

/-- **Unary** correspondence `modNegF` (key `(Eq, modNegF, modNegF)`). This is the
    gap (4) closer: `rcongr` had **no** unary node rule (the `Related` framework
    has `RelatedBinOp` only, no `RelatedUnaryOp`), so it could not strip a
    `modNegF` node. The `@[hgcongr]` attribute is arity-generic — a single
    hypothesis registers the unary descent. -/
@[hgcongr]
theorem modNegF_hcongr {p : Nat} {a₁ a₂ : ZMod p} (h : a₁ = a₂) :
    modNegF a₁ = modNegF a₂ := by subst h; rfl

/-- **Unary** correspondence `byInverseF` (key `(Eq, byInverseF, byInverseF)`).
    The second gap-(4) closer — the `fpInv` lowering node, which `rcongr` also
    could not strip. -/
@[hgcongr]
theorem byInverseF_hcongr {p : Nat} {a₁ a₂ : ZMod p} (h : a₁ = a₂) :
    byInverseF a₁ = byInverseF a₂ := by subst h; rfl

/-! ## 2. `hgcongr` descends binary AND unary nodes — including a mixed op-tree

These exercise the registered head-pair correspondences. The new capability over
`rcongr` is the **unary** descent and the **mixed** (binary-over-unary) tree;
`rcongr` could host neither (no `RelatedUnaryOp`, so a `modNegF`/`byInverseF` node
had nothing to apply). -/

/-- **Unary node, differing arguments — the `rcongr` gap.** `hgcongr` strips the
    `modNegF` node and leaves the single per-argument relatedness leaf `f a = a`,
    closed here by `assumption`. This is the descent `rcongr` could not perform
    (no unary rule); the head-pair node strip is the new capability, the residual
    leaf is discharged by the project cascade. -/
example {p : Nat} (f : ZMod p → ZMod p) (a : ZMod p) (h : f a = a) :
    modNegF (f a) = modNegF a := by hgcongr; assumption

/-- **Unary `byInverseF` node, differing arguments.** The second unary op. -/
example {p : Nat} (f : ZMod p → ZMod p) (a : ZMod p) (h : f a = a) :
    byInverseF (f a) = byInverseF a := by hgcongr; assumption

/-- **Mixed binary/unary op-tree, one `hgcongr`.** A `modAddF` node whose left
    child is the **unary** `modNegF` node and whose right child is the **binary**
    `modMulF` node — the descent crosses both arities in a single call, leaving
    the three per-argument leaves (closed here by `assumption`). By hand this is a
    `congr`/`rw` cascade per layer; `rcongr` could not host the unary child at
    all. -/
example {p : Nat} (f : ZMod p → ZMod p) (a b c : ZMod p)
    (ha : f a = a) (hb : f b = b) (hc : f c = c) :
    modAddF (modNegF (f a)) (modMulF (f b) (f c))
      = modAddF (modNegF a) (modMulF b c) := by hgcongr <;> assumption

/-! ## 3. Discharging the real `fpOpLowerTransports` arms — unary AND binary — by
`hgcongr`

The dialect leaf, after the (manual, non-automatable — gap (1)) `Expr`
peel + a body-`show`, is an equation
`lowered-op (mapVar-lookups) = source-op (source-lookups)`. For the **unary**
`fpNeg` arm:

```
modNegF ((mapVar a).lookup (mapVal V)) = modNegF (a.lookup V)
```

the two sides share the head `modNegF` but the **arguments differ**
(transported-lookup vs source-lookup). `rcongr` had to keep the hand
`rw [mapVar_lookup]` here (gap (4): no unary rule). `hgcongr` strips the
`modNegF` node via `modNegF_hcongr`, leaving the per-argument leaf
`(mapVar a).lookup (mapVal V) = a.lookup V`, which is exactly `mapVar_lookup`.

We prove the **whole `fpOpLowerTransports` leaf** with **all five** arms — the
three binary (`fpAdd`/`fpSub`/`fpMul`) AND the two unary (`fpNeg`/`fpInv`) —
discharged by `hgcongr` whose residual per-argument leaves are closed by the
dialect coherence `mapVar_lookup`. The unary arms are the ones `rcongr` left to a
manual `rw`. -/

/-- **The Field→ModArith op leaf — ALL arms by `hgcongr`.** Same statement as
    `FieldToModArithLowering.fpOpLowerTransports` and
    `RcongrLeafAutomation.fpOpLowerTransports_by_rcongr`; the outer `Expr` peel
    (`rcases`/`cases op`/`match args` + the body-`show`) is the goal-shape prelude
    that stays manual (gap (1)). Each arm — **including the two unary ones**
    `fpNeg`/`fpInv` — is closed by `hgcongr` (the head-pair node strip) followed
    by `exact mapVar_lookup _ _` on the residual per-argument leaf. The unary
    arms are the ones `fpOpLowerTransports_by_rcongr` had to leave to a hand
    `rw [mapVar_lookup]` (gap (4)). -/
theorem fpOpLowerTransports_by_hgcongr :
    OpLowerTransports lowerFieldToModArith transTy mapVal := by
  intro Γ t e V
  rcases e with ⟨op, h, args⟩
  subst h
  cases op with
  | fpAdd p =>
      match args with
      | .cons a (.cons b .nil) =>
          show modAddF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
            = modAddF (a.lookup V) (b.lookup V)
          hgcongr <;> exact mapVar_lookup _ _
  | fpSub p =>
      match args with
      | .cons a (.cons b .nil) =>
          show modSubF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
            = modSubF (a.lookup V) (b.lookup V)
          hgcongr <;> exact mapVar_lookup _ _
  | fpMul p =>
      match args with
      | .cons a (.cons b .nil) =>
          show modMulF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
            = modMulF (a.lookup V) (b.lookup V)
          hgcongr <;> exact mapVar_lookup _ _
  | fpNeg p =>
      match args with
      | .cons a .nil =>
          show modNegF ((mapVar a).lookup (mapVal V)) = modNegF (a.lookup V)
          hgcongr
          exact mapVar_lookup _ _
  | fpInv p =>
      match args with
      | .cons a .nil =>
          show byInverseF ((mapVar a).lookup (mapVal V)) = byInverseF (a.lookup V)
          hgcongr
          exact mapVar_lookup _ _

/-- The `hgcongr`-automated leaf and the hand-proved original prove the **same**
    `Prop` (`OpLowerTransports lowerFieldToModArith transTy mapVal`), so this is a
    drop-in for the obligation `ComParametricityTransport.fundamental` consumes. -/
example : OpLowerTransports lowerFieldToModArith transTy mapVal :=
  fpOpLowerTransports_by_hgcongr

/-- **The whole-program transport, re-derived through the `hgcongr`-automated op
    leaf.** Feeding `fpOpLowerTransports_by_hgcongr` (**all five** arms by the
    head-pair descent, including the two unary ones `rcongr` could not reach) to
    `fundamental` alongside the existing variable / binding coherences yields the
    same `Com`-level denotation-preservation the hand leaf does. -/
theorem fpComLowerTransports_via_hgcongr {Γ : Ctxt fpDialect} {t : FpTy}
    (c : Com fpDialect Γ t) :
    ComLowerTransports lowerFieldToModArith transTy mapVal c :=
  fundamental lowerFieldToModArith transTy mapVal
    fpVarTransports fpOpLowerTransports_by_hgcongr fpMapValExtends c

/-! ## 4. The comparison: which gaps `hgcongr` closes that `rcongr` could not

| Gap (from `RcongrLeafAutomation` §4) | `rcongr` | `hgcongr` |
|---|---|---|
| (1) dependent `Expr`/`HVector` peel | manual prelude | **still manual** (goal-shape, not a congruence rule) |
| (2) implicit `{p}` ⇒ 3 app args | mis-dispatched (`getAppNumArgs == 2`) | **closed** (head-pair key, hyp-recovered pairs) |
| (3) `@[reducible]` head defeats instance keying | square never fires | **sidestepped** (keys on the head *pair*, not a single reducible head for instance resolution) |
| (4) **unary** `fpNeg`/`fpInv` — no `RelatedUnaryOp` | **no rule — hand `rw`** | **closed** (arity-generic `@[hgcongr]` lemma) |

The gain over `rcongr` is gap (4): the two unary arms of
`fpOpLowerTransports`, which `fpOpLowerTransports_by_rcongr` leaves to a
hand `rw [mapVar_lookup]`, are first-class head-pair descents
(`fpOpLowerTransports_by_hgcongr`, §3). Gaps (2)/(3) are sidestepped by keying on
the head pair rather than a `getAppNumArgs`/reducible-head heuristic. Gap (1) —
the dependent peel — is a goal-shape obstruction shared by `gcongr`/`rcongr`/
`hgcongr` alike and is **not** closed here. -/

-- **`gcongr` makes no progress on the unary dialect-leaf shape.** With
-- *differing arguments* (`f a` vs `a`, the transported-vs-source lookup shape),
-- `gcongr` cannot align a leaf even after unfolding `modNegF` to `Neg.neg`, so it
-- fails — this is the boundary `hgcongr` crosses with its head-pair unary descent.
-- (On the *diagonal bare-variable* case `modNegF a = modNegF a`, `gcongr` does
-- succeed via reducible unfolding; the separation is this
-- differing-argument shape, which is the dialect leaf.)
/-- error: gcongr did not make progress -/
#guard_msgs in
example {p : Nat} (f : ZMod p → ZMod p) (a : ZMod p) (h : f a = a) :
    modNegF (f a) = modNegF a := by gcongr

-- **`gcongr` makes no progress on the binary dialect-leaf shape either.** Same
-- differing-argument obstruction for `modAddF`.
/-- error: gcongr did not make progress -/
#guard_msgs in
example {p : Nat} (f : ZMod p → ZMod p) (a b : ZMod p) (h1 : f a = a) (h2 : f b = b) :
    modAddF (f a) (f b) = modAddF a b := by gcongr

end CatCrypt.Crypto.SecureCompilation.VIR.HgcongrDialectLeaves
