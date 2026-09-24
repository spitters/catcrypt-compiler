/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering
public import Transfer.Congruence.RCongr

/-!
# Automating the dialect-lowering per-op leaf squares with `rcongr` / `transfer`

## Scope

The prime-field → ModArith dialect lowering of
`FieldToModArithLowering.lean` proves its only op-specific
obligation, `fpOpLowerTransports` (the `OpLowerTransports` leaf the
`ComParametricityTransport.fundamental` lemma consumes), **by hand**: a
`cases op` over the five prime-field tags, an `HVector` argument peel
(`.cons … .cons … .nil`) per op, an explicit `show` of the
`modAddF …/modMulF …/…` goal, and a `rw [mapVar_lookup, mapVar_lookup]`
to align the two positionally-identical lookups. That is the recipe its
"Lessons" line flagged as the manual cost — roughly **30 source lines**
(five `cases` arms × ~5 lines: the `match` peel, the `show`, the `rw`).

This file shows the **Trocq cross-head congruence rule `rcongrBinOp` (the
move `rcongr` applies at each node) closes that same op-square content** on
the three binary arms, replacing the hand `rw [mapVar_lookup, mapVar_lookup]`
collapse with a first-class lemma-driven congruence step — and records the
two precise capability gaps the probe surfaced (the `Expr`/`HVector` peel,
and the registry's lack of a *unary* node rule).

### What the dialect leaf actually is, and why the op node fits `RelatedBinOp`

After the `cases op` + arg-peel + a body-`show`, every binary
`fpOpLowerTransports` arm is a **cross-head congruence over the registry**:
the lowered ModArith op's denotation (`modAddF`, `modSubF`, `modMulF`)
applied to the *transported* argument lookups must equal the source Field
op's denotation applied to the source lookups —
`modAddF ((mapVar a).lookup (mapVal V)) … = modAddF (a.lookup V) …`. The two
sides share the head but the **arguments differ**. Because the prime-field
fragment is 1:1 (Field's `fpAdd` denotes `modAddF`, its ModArith twin
`modAdd` *also* denotes `modAddF`, and `transTy`/`mapVal` are positional
identities), the op node is exactly the `Related.lean` shape
`enc (op x y) = bop (enc x) (enc y)` with `enc = id` and `op = bop` the
shared leaf function. The `rcongrBinOp` rule strips that node and leaves the
two per-argument relatedness leaves, each the variable coherence
`mapVar_lookup` wrapped in `Related.mk`.

### The layers, and the capability boundary (two gaps)

* **Binary op node (automated by the `rcongrBinOp` descent).** The op square
  is closed by `transferGround` (bridging `=` → `Related id`) then
  `rcongrBinOp _ _ _ ?_ ?_ <;> exact ⟨mapVar_lookup _ _⟩`. We also show, in
  isolation (§2), a differing-argument descent and multi-op tree
  composites closed by one `transfer`/`rcongr`.

* **Gap 1 — the `Expr`/`HVector` peel is not relational congruence.** The
  outer `rcases e with ⟨op, h, args⟩; subst h; cases op; match args with …`
  + the body-`show` runs **before** the goal is an op-tree over field values;
  `rcongr`/`transfer` dispatch on a `Related`/`Eq`/`Iff`/`∀` head and do
  **not** perform that dependent elimination. It stays manual.

* **Gap 2 — the registry has only `RelatedBinOp` (no unary rule), and the
  binary node needs the rule applied explicitly.** Plain
  `rcongr`/`transfer`/`inferInstance` does **not** auto-fire on the binary
  arm: `rcongr`'s `getAppNumArgs == 2` test misses `modAddF a b` (3 app args
  incl. implicit `{p}`), and reducible `modAddF`/`⟦t⟧`-vs-`ZMod p` defeat
  instance keying — so the rule is invoked explicitly (still the same
  cross-head move). The two **unary** ops (`fpNeg`/`fpInv`) have **no**
  registry rule at all (`RelatedBinOp` only — no `RelatedUnaryOp`), so those
  arms keep the dialect's `rw [mapVar_lookup]`.

**All goals closed**; axiom set is the ambient
`{propext, Classical.choice, Quot.sound}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RcongrLeafAutomation

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
open Transfer

/-! ## 1. The per-op leaf functions as registered `RelatedBinOp` squares

The five prime-field leaves are 1:1 with their ModArith twins and
definitionally equal (the fragment that makes the lowering a
program transport). With the identity encoding, each is the degenerate-but
real commuting square `id (op x y) = op (id x) (id y)`, i.e. a
`RelatedBinOp id op op`. Registering them puts the dialect op squares into
the same database `rcongr`/`transfer` already consume for the Baby Bear
field. -/

/-- `modAddF` realizes itself under the identity encoding — the prime-field
    `fpAdd` lowering square as a `RelatedBinOp`. -/
instance modAddRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) modAddF modAddF where
  comm _ _ := rfl

/-- `modSubF` realizes itself (the `fpSub` lowering square). -/
instance modSubRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) modSubF modSubF where
  comm _ _ := rfl

/-- `modMulF` realizes itself (the `fpMul` lowering square). -/
instance modMulRelated {p : Nat} :
    RelatedBinOp (id : ZMod p → ZMod p) modMulF modMulF where
  comm _ _ := rfl

/-- **The argument leaf as a registered `Related` instance.** The variable
    lookup coherence `mapVar_lookup` — `(mapVar v).lookup (mapVal V) =
    v.lookup V` — *is* the per-argument relatedness fact the descent bottoms
    out at: the transported lookup is the `id`-encoding of the source lookup.
    Registering it as an instance is what lets `rcongr`/`transfer` close the
    **whole** op arm (op square ∘ arg leaves) by instance resolution, with no
    `mapVar_lookup` rewrite named. (This is the dialect's counterpart of the
    Baby Bear `leafId` — the encoding-of-a-leaf fact the registry needs.) -/
instance lookupRelated {Γ : Ctxt fpDialect} {t : FpTy}
    (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ) :
    Related (id : ⟦t⟧ → ⟦t⟧) ((mapVar v).lookup (mapVal V)) (v.lookup V) where
  rel := mapVar_lookup _ _

/-! ## 2. `rcongr` / `transfer` close the ModArith op squares and composites

These exercise the tactics on the registered dialect leaf set — the
analogue of `RCongr.lean`'s Baby Bear demos, but on the ModArith ops the
Field→ModArith lowering actually emits. -/

/-- **Single dialect op square, by `rcongr`.** The registered `modAddF`
    square; with identical args the descent bottoms out at the `id`-leaf. -/
example {p : Nat} (a b : ZMod p) :
    Related (id : ZMod p → ZMod p) (modAddF a b) (modAddF a b) := by rcongr

/-- **Multi-op composite, by ONE `transfer`.** The nested
    `modAddF (modMulF a b) c` op-tree — the shape a two-instruction
    field-leaf schedule lowers to — transfers in a single call, the registry
    finding both squares. This is the dialect analogue of the
    `a * b + c = bbFieldAdd (bbFieldMul a b) c` field payoff. -/
example {p : Nat} (a b c : ZMod p) :
    modAddF (modMulF a b) c = modAddF (modMulF a b) c := by transfer

/-- **The same composite, by ONE `rcongr`**, descending structurally through
    both cross-head nodes (`modAddF` then `modMulF`). Replaces a manual
    `congr`-chain over the two op layers. -/
example {p : Nat} (a b c : ZMod p) :
    Related (id : ZMod p → ZMod p)
      (modAddF (modMulF a b) c) (modAddF (modMulF a b) c) := by rcongr

/-- **Three-op composite, by ONE `transfer`** — `(a*b - c) + d` over the
    ModArith leaves. A single call walks the whole tree; by hand this is a
    three-level `congr` cascade. -/
example {p : Nat} (a b c d : ZMod p) :
    modAddF (modSubF (modMulF a b) c) d = modAddF (modSubF (modMulF a b) c) d := by
  transfer

/-- **Non-trivial cross-head descent: the args differ.** Here the
    two sides are *not* syntactically equal — the left args are `f a`/`f b`,
    the right `a`/`b`, related by the local squares `hfa`/`hfb`. The
    `rcongrBinOp` rule (the move `rcongr` applies at each node) strips the
    `modAddF` head and leaves exactly the two per-argument relatedness
    subgoals, which the supplied leaves close. This is the descent the
    dialect op leaf needs (lowered-arg vs source-arg), in isolation. -/
example {p : Nat} (f : ZMod p → ZMod p) (a b : ZMod p)
    (hfa : Related (id : ZMod p → ZMod p) (f a) a)
    (hfb : Related (id : ZMod p → ZMod p) (f b) b) :
    modAddF (f a) (f b) = modAddF a b :=
  (rcongrBinOp id modAddF modAddF hfa hfb).rel

/-! ## 3. Discharging the real `fpOpLowerTransports` arm by the `rcongr` rule

The dialect leaf, after the (manual, non-automatable) `Expr` peel +
a `show` that exposes the body, is an equation
`lowered-op (mapVar-lookups) = source-op (source-lookups)` — e.g. for
`fpAdd`:

```
modAddF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
  = modAddF (a.lookup V) (b.lookup V)
```

The two sides share the head `modAddF` but the **arguments differ**
(transported-lookup vs source-lookup). This is exactly the cross-head /
differing-argument shape `rcongr` is for: the `rcongrBinOp` rule strips the
`modAddF` node and leaves the two per-argument relatedness leaves
`Related id ((mapVar a).lookup (mapVal V)) (a.lookup V)`, each of which is
the lookup coherence `mapVar_lookup` wrapped in `Related.mk`. So the hand
`show …F … ; rw [mapVar_lookup, mapVar_lookup]` (which closes by
`rw`-trailing `rfl`) becomes a `rcongrBinOp` descent whose two residual
leaves are the lookup facts — the Trocq cross-head congruence doing the op
node, the dialect's variable coherence doing the leaves.

We prove the **whole `fpOpLowerTransports` leaf** with the **three binary
arms (`fpAdd`/`fpSub`/`fpMul`) closed by the `rcongrBinOp` descent**, and
record at §4 why the **two unary arms (`fpNeg`/`fpInv`) cannot** use the
descent (no `RelatedUnaryOp` in the registry — `rcongr`/`transfer` host only
binary cross-head nodes). -/

/-- **The Field→ModArith op leaf — binary arms by the `rcongr` cross-head
    rule.** Same statement as `FieldToModArithLowering.fpOpLowerTransports`;
    the outer `Expr` peel (`rcases`/`cases op`/`match args` + the body-`show`)
    is structural and stays (the capability boundary — see §4). The three
    **binary** arms are closed by `transferGround` (bridging `=` to
    `Related id`) followed by the `rcongrBinOp` descent (the move `rcongr`
    applies at a node): it strips the `modAddF`/`modSubF`/`modMulF` head and
    leaves the two per-argument leaves, each the lookup coherence
    `⟨mapVar_lookup _ _⟩`. The two **unary** arms have no binary congruence
    rule to apply, so they retain the dialect's own `mapVar_lookup` rewrite
    (the gap is documented in §4). -/
theorem fpOpLowerTransports_by_rcongr :
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
          refine transferGround (h := ?_)
          refine rcongrBinOp _ _ _ ?_ ?_ <;> exact ⟨mapVar_lookup _ _⟩
  | fpSub p =>
      match args with
      | .cons a (.cons b .nil) =>
          show modSubF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
            = modSubF (a.lookup V) (b.lookup V)
          refine transferGround (h := ?_)
          refine rcongrBinOp _ _ _ ?_ ?_ <;> exact ⟨mapVar_lookup _ _⟩
  | fpMul p =>
      match args with
      | .cons a (.cons b .nil) =>
          show modMulF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
            = modMulF (a.lookup V) (b.lookup V)
          refine transferGround (h := ?_)
          refine rcongrBinOp _ _ _ ?_ ?_ <;> exact ⟨mapVar_lookup _ _⟩
  | fpNeg p =>
      -- Unary: no `RelatedBinOp` rule (see §4). Dialect lookup coherence directly.
      match args with
      | .cons a .nil =>
          show modNegF ((mapVar a).lookup (mapVal V)) = modNegF (a.lookup V)
          rw [mapVar_lookup]
  | fpInv p =>
      match args with
      | .cons a .nil =>
          show byInverseF ((mapVar a).lookup (mapVal V)) = byInverseF (a.lookup V)
          rw [mapVar_lookup]

/-! ## 4. The capability boundary, stated precisely (two real gaps)

Two **shape mismatches** between `rcongr`/`transfer` and the dialect leaf bound
the automation. Neither blocks the binary cross-head op node, which the
`rcongrBinOp` rule above automates; they are recorded here rather than forced.

### Gap 1 — the dependent `Expr`/`HVector` peel is not relational congruence.

`rcongr`/`transfer` dispatch on the goal **head** (`Related`/`Eq`/`Iff`/
`∀`/`λ`); their recursion descends an *op-tree of field values* driven by the
`RelatedBinOp` database. The dialect leaf does **not** start as such a tree:

* the goal is `(lowerExpr e).denote (mapVal V) = transTy (e.denote V)` — an
  `Eq`, but whose two sides are `Expr.denote` applications, **not** a
  `modAddF`/`modMulF` op-tree;
* exposing the `modAddF …` body requires `rcases e with ⟨op, retTy_eq,
  args⟩`, `subst retTy_eq`, `cases op` (the five tags), a per-op `HVector`
  `match args with | .cons … .nil`, **and** a `show` to definitionally
  re-expose the lowered op's denotation as `modAddF …`.

That prelude is **dependent pattern matching**, which the goal-head
dispatcher has no rule for. So it stays manual; `rcongr` takes over **after**
the `show`. This mirrors `transfer`'s own scope note (binder traversal + leaf
dispatch, *not* arbitrary recursor/motive elimination — the 3d-3 tail).

### Gap 2 — the registry has only `RelatedBinOp` (no unary node rule).

Even after the `show`, plain `rcongr`/`transfer`/`inferInstance` does **not**
auto-fire on the binary arm, for two compounding reasons found by probe:

* `rcongr`'s binary-node test is `lhs.getAppNumArgs == 2`, but `modAddF a b`
  has **three** app args (the implicit `{p}`), so the auto-descent skips it
  and falls to `inferInstance | rfl`;
* `modAddF`/`modMulF` are `@[reducible]`, so instance resolution unfolds them
  to `· + ·`/`· * ·` before matching, and the `modAddF`-keyed
  `RelatedBinOp` never fires (it would match the abstract `+` square instead,
  with the wrong target); the per-argument lookup leaf likewise fails to
  resolve because its registered encoding type is `⟦FpTy.fp p⟧` while the
  goal presents `id : ZMod p → ZMod p` (defeq, but instance resolution keys
  syntactically).

So the working form invokes the rule **explicitly** —
`refine transferGround (h := ?_); refine rcongrBinOp _ _ _ ?_ ?_ <;> exact
⟨mapVar_lookup _ _⟩` — which IS the move `rcongr` would make at a node, with
the operands left as the per-arg subgoals. The auto-dispatch heuristics do
not trigger on this term shape, but the underlying cross-head rule applies
cleanly.

And the **unary** ops (`fpNeg`/`fpInv`) have **no** registry rule at all: the
`Related` framework provides `RelatedBinOp` (binary) but no
`RelatedUnaryOp`. A unary cross-head node `modNegF (mapVar a).lookup =
modNegF a.lookup` has no `rcongrUnaryOp` to strip it, so those two arms keep
the dialect's own `rw [mapVar_lookup]`. Adding `RelatedUnaryOp` +
`rcongrUnaryOp` to the bridge would close this (a one-rule extension), but
the bridge is read-only here.

### Manual-lines comparison

The hand `fpOpLowerTransports` binary arm is `show …F (…lookup…) (…) = …F (…)
(…)` + `rw [mapVar_lookup, mapVar_lookup]` — the `rw` is the
line that closes the square by aligning both lookups (then trailing `rfl`).
The `rcongr` form swaps that closing `rw [mapVar_lookup, mapVar_lookup]`
with `refine transferGround (h := ?_); refine rcongrBinOp _ _ _ ?_ ?_ <;>
exact ⟨mapVar_lookup _ _⟩`: the op node becomes a **first-class lemma-driven
structural move** (`rcongrBinOp`) rather than a single definitional
collapse, with the two lookup leaves explicit. The `show` prelude and the
`cases op`/`match args` skeleton are unchanged in both (Gap 1). Net: the
automation reframes the op square as a registry congruence step on the three
binary arms; it does **not** shrink the line count (the dialect leaf is
lookup-aligned, so the hand `rw` is already a one-liner), and it does **not**
reach the unary arms. The *gain* of the automation shows on op-**tree**
composites (§2): a multi-op nesting closes in one `transfer`/`rcongr` where by
hand each layer needs its own `congr`/`rw` — but the 1:1 dialect leaf is a
single op, so that gain does not apply here. In summary: the
cross-head rule applies to the dialect op node, the line-count win lands on
composites, not on the already-flat 1:1 leaf. -/

/-- The automated leaf and the hand-proved original are proofs of the **same**
    `Prop` (`OpLowerTransports lowerFieldToModArith transTy mapVal`), so
    `fpOpLowerTransports_by_rcongr` is a drop-in for the obligation
    `ComParametricityTransport.fundamental` consumes — not a weaker
    restatement. -/
example :
    OpLowerTransports lowerFieldToModArith transTy mapVal :=
  fpOpLowerTransports_by_rcongr

/-- **The whole-program transport, re-derived through the `rcongr`-automated
    op leaf.** Feeding `fpOpLowerTransports_by_rcongr` (binary arms by the
    cross-head rule) to `fundamental` alongside the existing variable /
    binding coherences yields the same `Com`-level denotation-preservation
    the hand leaf does — the automation plugs into `fundamental` unchanged. -/
theorem fpComLowerTransports_via_rcongr {Γ : Ctxt fpDialect} {t : FpTy}
    (c : Com fpDialect Γ t) :
    ComLowerTransports lowerFieldToModArith transTy mapVal c :=
  fundamental lowerFieldToModArith transTy mapVal
    fpVarTransports fpOpLowerTransports_by_rcongr fpMapValExtends c

end CatCrypt.Crypto.SecureCompilation.VIR.RcongrLeafAutomation
