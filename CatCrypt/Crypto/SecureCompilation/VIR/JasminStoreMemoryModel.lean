/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-!
# A non-aliasing memory model for `stackStore` in the Jasmin dialect

`JasminPrintSemCorrect.lean` closes the semantic half of `lowerComToProg`
(`lowerComToProg_sem_eq`) on the **straight-line** fragment, which by
construction excludes the in-place `stackStore` binder: that op is the lone op
whose `resultName` reuses (aliases) its source-array name (recorded there in
`stackStore_aliases_source`), so the fresh-name freshness argument that powers
the straight-line proof does not apply to it.

This file builds the **foundation** for extending past straight-line to a
*non-aliasing* `stackStore`. It contributes three fully-closed pieces and one
worked instance:

1. **Buffer disjointness** (`BufDisjoint`): two `stackArr` buffers, identified
   by their `Ctxt.Var`, are disjoint exactly when they are distinct variables.
   At the `Com.denote` level a `stackStore` introduces a *new* De Bruijn binding
   holding the updated array, so every buffer already in scope is reached as a
   `.there` shift and is left untouched.

2. **The disjointness denotation lemma** (`stackStore_load_disjoint_denote`):
   storing into buffer `X` and then loading from a *distinct* buffer `Y` reads
   the same value `Y` held before the store. This is proved straight from
   `Com.denote` / the `jasminDenote` instance — the store binds a fresh `here`
   slot, the load's source resolves through `.there`, and `Var.lookup` on a
   `.there` ignores the new binding.

3. **`WellFormedStores`** — a predicate *weaker* than `StraightLine`. It permits
   `stackStore` binders, requiring only the non-aliasing condition that each
   store target is disjoint, in the post-store context, from every later load's
   source buffer. We prove `StraightLine com → WellFormedStores com` (a
   straight-line program has no stores, so the condition is vacuous).

4. **Worked instance** (`storeThenDisjointLoad_denote` /
   `storeThenDisjointLoad_wellFormed`): the denotation of a single `stackStore`
   followed by a `stackLoad` from a distinct buffer reduces, via the disjointness
   lemma, to the pre-store value of the loaded buffer; and that program is
   `WellFormedStores` under the non-aliasing precondition `ShapeDisjoint X Y`.

All four pieces have all goals closed; the only axioms are the standard
`propext` / `Quot.sound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminStoreMemoryModel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-! ## 1. Buffer disjointness

Two stack buffers in a context `Γ` are *disjoint* when, viewed as `Ctxt.Var`s,
they are not the same variable. Because `stackStore`/`stackLoad` model memory
functionally (each distinct `Ctxt.Var` is an independent value threaded by
`Com.denote`), distinctness of the variables *is* memory-disjointness: a write
to one cannot alias a read of the other.

We phrase `BufDisjoint` on buffers of the **same shape** (`stackArr w n`), where
disjointness is plain variable inequality `X ≠ Y`. Buffers of *different* shapes
are automatically disjoint — they are SSA variables of different dialect types,
so neither can alias the other — and that cross-shape case is handled at the use
site (`LoadDisjointFrom`) by simply imposing no obligation. This keeps the core
relation homogeneous, so its closure under De Bruijn shifting (`BufDisjoint.there`)
is ordinary constructor injectivity rather than a heterogeneous `HEq` argument. -/

/-- Two **same-shape** stack buffers `X Y : Var Γ (stackArr w n)` are *disjoint*
    when they are not the same variable. Distinct SSA variables hold independent
    arrays, so a write to one never aliases a read of the other. -/
def BufDisjoint {Γ : Ctxt jasminDialect} {w n : Nat}
    (X Y : Ctxt.Var Γ (.stackArr w n)) : Prop :=
  X ≠ Y

/-- Disjointness is symmetric. -/
theorem BufDisjoint.symm {Γ : Ctxt jasminDialect} {w n : Nat}
    {X Y : Ctxt.Var Γ (.stackArr w n)} (h : BufDisjoint X Y) : BufDisjoint Y X :=
  fun hYX => h hYX.symm

/-- A buffer is never disjoint from itself. -/
theorem BufDisjoint.irrefl {Γ : Ctxt jasminDialect} {w n : Nat}
    (X : Ctxt.Var Γ (.stackArr w n)) : ¬ BufDisjoint X X :=
  fun h => h rfl

/-- Disjointness is, by definition, variable inequality. -/
theorem BufDisjoint_iff_ne {Γ : Ctxt jasminDialect} {w n : Nat}
    (X Y : Ctxt.Var Γ (.stackArr w n)) : BufDisjoint X Y ↔ X ≠ Y := Iff.rfl

/-- Disjointness is preserved by shifting both buffers under a binder: if `X` and
    `Y` are disjoint in `Γ`, then `Ctxt.Var.there X` and `Ctxt.Var.there Y` are
    disjoint in `s :: Γ` (`.there` is injective, so equal shifts force equal
    originals). -/
theorem BufDisjoint.there {Γ : Ctxt jasminDialect} {w n : Nat}
    {s : jasminDialect.Ty} {X Y : Ctxt.Var Γ (.stackArr w n)}
    (h : BufDisjoint X Y) :
    BufDisjoint (Ctxt.Var.there (s := s) X) (Ctxt.Var.there (s := s) Y) := by
  intro hEq
  exact h (by injection hEq)

/-! ## 2. The disjointness denotation lemma

The structural fact behind non-aliasing: at the `Com.denote` level a
`stackStore` binder extends the valuation with the *updated* array as a brand new
`here` binding. Any buffer `Y` that was already in scope before the store is, in
the post-store context, reached as `Ctxt.Var.there Y`, and `Var.lookup` on a
`.there` discards the freshly bound array. So a later load from `Y` reads exactly
the pre-store value. We package this as a denotation lemma about the two-step
program "store into `X`, then continue reading `Y`". -/

/-- **Reading an earlier buffer is unperturbed by a store.** A `stackStore`
    binder extends the valuation with the updated array at the new `here` slot;
    a buffer `Y` already in scope is reached through `.there`, whose `lookup`
    ignores the new binding. Hence loading from `Y` after the store reads the
    same array as before. This is the denotation-level non-aliasing core. -/
theorem lookup_there_extend {Γ : Ctxt jasminDialect} {ty tEx : jasminDialect.Ty}
    (Y : Ctxt.Var Γ ty) (V : Ctxt.Valuation Γ) (x : ⟦tEx⟧) :
    Ctxt.Var.lookup (Ctxt.Var.there (s := tEx) Y) (V.extend x) = Y.lookup V :=
  rfl

/-- The denotation of a `stackStore` expression: it is the functional update
    `stackSet` of the source array at the index, with the value. -/
theorem stackStore_denote {Γ : Ctxt jasminDialect} {w n : Nat}
    (arr : Ctxt.Var Γ (.stackArr w n)) (idx : Ctxt.Var Γ (.reg 64))
    (val : Ctxt.Var Γ (.reg w)) (V : Ctxt.Valuation Γ) :
    (Expr.mk (JasminOp.stackStore w n) rfl
        (.cons arr (.cons idx (.cons val .nil)))).denote V
      = stackSet (arr.lookup V) (idx.lookup V).toNat (val.lookup V) := by
  rfl

/-- The denotation of a `stackLoad` expression: read element `idx` of the
    source array via the total `stackGet`. -/
theorem stackLoad_denote {Γ : Ctxt jasminDialect} {w n : Nat}
    (arr : Ctxt.Var Γ (.stackArr w n)) (idx : Ctxt.Var Γ (.reg 64))
    (V : Ctxt.Valuation Γ) :
    (Expr.mk (JasminOp.stackLoad w n) rfl (.cons arr (.cons idx .nil))).denote V
      = stackGet (arr.lookup V) (idx.lookup V).toNat := by
  rfl

/-- **Disjointness denotation lemma (the milestone's step 2).** Consider a
    program that first stores into buffer `X` (binding the updated array as the
    new `here` variable) and then loads from a *distinct* buffer `Y`, where `Y`
    was already in scope (so it appears in the post-store context as
    `Ctxt.Var.there Y`). The loaded value equals what loading from `Y` at the
    same index would have produced *before* the store: the store into `X` does
    not perturb the disjoint buffer `Y`.

    Stated directly on `Com.denote`: the two-instruction program
    `var (stackStore X i v) (ret (load from there-Y at there-j))` denotes to the
    `stackGet` of `Y`'s *pre-store* value — independent of `X`, `i`, `v`. -/
theorem stackStore_load_disjoint_denote {Γ : Ctxt jasminDialect}
    {wX nX wY : Nat} {nY : Nat}
    (X : Ctxt.Var Γ (.stackArr wX nX)) (iStore : Ctxt.Var Γ (.reg 64))
    (vStore : Ctxt.Var Γ (.reg wX))
    (Y : Ctxt.Var Γ (.stackArr wY nY)) (jLoad : Ctxt.Var Γ (.reg 64))
    (V : Ctxt.Valuation Γ) :
    (Com.var
        (Expr.mk (JasminOp.stackStore wX nX) rfl
          (.cons X (.cons iStore (.cons vStore .nil))))
        (Com.var
          (Expr.mk (JasminOp.stackLoad wY nY) rfl
            (.cons (Ctxt.Var.there Y) (.cons (Ctxt.Var.there jLoad) .nil)))
          (Com.ret Ctxt.Var.here))).denote V
      = stackGet (Y.lookup V) (jLoad.lookup V).toNat := by
  -- The two `Com.denote` steps reduce definitionally: the store binds the new
  -- `here` slot with `stackSet …`; the load reads `there Y` / `there jLoad`,
  -- whose `Var.lookup` (by `lookup_there_extend`) ignores the new binding and
  -- resolves to the pre-store `Y` / `jLoad`. So both sides are the same
  -- `stackGet (Y.lookup V) …` after reduction.
  rfl

/-! ## 3. `WellFormedStores`: a non-aliasing fragment weaker than `StraightLine`

`StraightLine` forbids `stackStore` outright. We relax it: a `stackStore` binder
is allowed provided its target buffer is disjoint, *in the post-store context*,
from every later load's source buffer. "Later" here means: relative to the body
that runs after the store binder. We capture "every later load's source is
disjoint from the store target" with the predicate `LaterLoadsDisjoint`
(built on the per-expression `LoadDisjointFrom`) over the body and the (shifted)
store target, then thread it through `WellFormedStores`.

The store target lives in the pre-store context `Γ`; inside the body it is the
shifted variable `.there target`. A load in the body reads a buffer `Y : Var Γ' _`
for the body's context `Γ'`; for the *immediately following* body `Γ' = stackArr … :: Γ`
and we compare `Y` against `.there target`. For deeper loads the comparison is
made after the intervening shifts, which `LaterLoadsDisjoint` tracks by recursion
over the body. -/

/-- `e` is a `stackStore` writing the buffer `target` (and equal, as a whole
    `Expr`, to the canonical `stackStore` shape with `target` as its first
    argument). This packages "`e` is a store into `target`" without a transport
    cast: it asserts `e` *is* the explicit constructor application, from which
    the target buffer is read off directly. -/
def ExprStoresInto {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (e : Expr jasminDialect Γ t) {w n : Nat}
    (target : Ctxt.Var Γ (.stackArr w n)) : Prop :=
  ∃ (htEq : t = JasminTy.stackArr w n) (idx : Ctxt.Var Γ (.reg 64))
    (val : Ctxt.Var Γ (.reg w)),
    e = htEq ▸ Expr.mk (JasminOp.stackStore w n) rfl
      (.cons target (.cons idx (.cons val .nil)))

/-- `e`'s op is `stackStore` (for some width/length). -/
def ExprIsStackStore {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (e : Expr jasminDialect Γ t) : Prop :=
  ∃ (w n : Nat), e.op = JasminOp.stackStore w n

/-- **Same-shape disjointness across a-priori different shapes.** Given buffers
    `X : Var Γ (stackArr wX nX)` and `src : Var Γ (stackArr w n)` whose shapes may
    differ, this is `True` when the shapes differ (different dialect types cannot
    alias) and `BufDisjoint X src` when they coincide. Defined by matching the
    two shapes so the homogeneous `BufDisjoint` only fires on equal shapes (where
    the `▸` cast is by a refl-equality and computes away). -/
def ShapeDisjoint {Γ : Ctxt jasminDialect} {wX nX w n : Nat}
    (X : Ctxt.Var Γ (.stackArr wX nX)) (src : Ctxt.Var Γ (.stackArr w n)) : Prop :=
  if h : wX = w ∧ nX = n then
    BufDisjoint (h.1 ▸ h.2 ▸ X) src
  else True

/-- `ShapeDisjoint` is preserved by shifting both buffers under a binder. When
    the shapes differ both sides are `True`; when they coincide it reduces to
    `BufDisjoint.there`. -/
theorem ShapeDisjoint.there {Γ : Ctxt jasminDialect} {wX nX w n : Nat}
    {s : jasminDialect.Ty}
    {X : Ctxt.Var Γ (.stackArr wX nX)} {src : Ctxt.Var Γ (.stackArr w n)}
    (h : ShapeDisjoint X src) :
    ShapeDisjoint (Ctxt.Var.there (s := s) X) (Ctxt.Var.there (s := s) src) := by
  unfold ShapeDisjoint at h ⊢
  by_cases hsh : wX = w ∧ nX = n
  · obtain ⟨rfl, rfl⟩ := hsh
    rw [dite_eq_left (And.intro (rfl : wX = wX) (rfl : nX = nX))]
    rw [dite_eq_left (And.intro (rfl : wX = wX) (rfl : nX = nX))] at h
    exact h.there
  · rw [dite_eq_right hsh]
    trivial

/-- **Load-source disjoint from a target buffer.** Given a stack buffer
    `X : Var Γ (stackArr wX nX)`, this expresses the non-aliasing requirement on
    a single expression `e` in the same context: *if* `e` is a `stackLoad` or a
    constant-index store `stackStoreImm`, its source buffer (the head of its args)
    must be `ShapeDisjoint` from `X` — automatically satisfied when the source's
    buffer shape differs from `X`'s (different dialect types cannot alias), and
    `BufDisjoint` when shapes coincide. Every other op carries no obligation
    (`True`). Matching on `e.op` (and the correspondingly-shaped `e.args`) extracts
    the source without a transport cast. -/
def LoadDisjointFrom {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    {wX nX : Nat} (X : Ctxt.Var Γ (.stackArr wX nX))
    (e : Expr jasminDialect Γ t) : Prop :=
  match e.op, e.args with
  | .stackLoad _ _, .cons src _ => ShapeDisjoint X src
  | .stackStoreImm _ _ _, .cons src _ => ShapeDisjoint X src
  | _, _ => True

/-- **Every later load in the body is disjoint from the store target.** Walks
    the body `Com`, tracking the store target `X` shifted by one `.there` per
    intervening binder. At each `var e' body'` step it requires `e'`'s load (if
    any) to be `LoadDisjointFrom` the current shifted target, then recurses into
    the body with the target shifted once more. The store target lives in the
    pre-binder context, so descending under a binder of type `tEx` shifts it to
    `Ctxt.Var.there X`. -/
def LaterLoadsDisjoint {Γ : Ctxt jasminDialect} {wX nX : Nat}
    (X : Ctxt.Var Γ (.stackArr wX nX)) :
    {t : jasminDialect.Ty} → Com jasminDialect Γ t → Prop
  | _, .ret _ => True
  | _, .var (t := tEx) e' body' =>
      LoadDisjointFrom X e' ∧ LaterLoadsDisjoint (Ctxt.Var.there (s := tEx) X) body'

/-- **Non-aliasing well-formedness.** A relaxation of `StraightLine` that admits
    `stackStore` binders. A `Com` is well-formed-for-stores when each binder is
    either:

    * **not** a `stackStore` (the straight-line case — `regArith`/`castW`/
      `stackLoad`/`extCall`), with a well-formed body; or
    * a `stackStore` into some `target` (witnessed by `ExprStoresInto e target`)
      whose `target`, shifted under the binder, is disjoint from **every later
      load's source** in the body — the non-aliasing condition, captured by
      `LaterLoadsDisjoint` applied to the shifted target `Ctxt.Var.there target`.

    In both cases the body is itself well-formed. `LaterLoadsDisjoint` walks the
    body and, for each `stackLoad` reachable, requires `ShapeDisjoint` between the
    (appropriately shifted) store target and that load's source buffer. -/
def WellFormedStores {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} :
    Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var (t := tEx) e body =>
      ((ExprNotStackStore e) ∨
        (∃ (w n : Nat) (target : Ctxt.Var Γ (.stackArr w n)),
          ExprStoresInto e target ∧
          LaterLoadsDisjoint (Ctxt.Var.there (s := tEx) target) body))
      ∧ WellFormedStores body

/-- **`StraightLine ⇒ WellFormedStores` (the milestone's step 3).** Straight-line
    is the special case of well-formed-for-stores with **no** `stackStore`
    binders: every binder is non-`stackStore`, so it takes the left disjunct
    (`ExprNotStackStore`), and the non-aliasing `LaterLoadsDisjoint` obligation is
    never even invoked. By structural induction over the program. -/
theorem WellFormedStores.of_straightLine {Γ : Ctxt jasminDialect}
    {t : jasminDialect.Ty} :
    (com : Com jasminDialect Γ t) → StraightLine com → WellFormedStores com
  | .ret _, _ => trivial
  | .var e body, hSL => by
      obtain ⟨hNS, hbody⟩ := hSL
      exact ⟨Or.inl hNS, WellFormedStores.of_straightLine body hbody⟩

/-! ## 4. Worked instance: a single non-aliasing `stackStore` then a `stackLoad`

We give the semantic-half theorem for the canonical non-aliasing shape: store
into buffer `X`, then load from a *distinct* buffer `Y`. The denotation side is
exactly `stackStore_load_disjoint_denote` (the store does not perturb `Y`); the
evaluator side threads the same two instructions through the named `Store`. -/

/-- A single `stackStore` into `X` followed by a `stackLoad` from a distinct `Y`,
    as a `Com`. The load reads the shifted (`.there`) `Y` / `jLoad` because they
    were in scope before the store binder. -/
def storeThenDisjointLoad {Γ : Ctxt jasminDialect} {wX nX wY nY : Nat}
    (X : Ctxt.Var Γ (.stackArr wX nX)) (iStore : Ctxt.Var Γ (.reg 64))
    (vStore : Ctxt.Var Γ (.reg wX))
    (Y : Ctxt.Var Γ (.stackArr wY nY)) (jLoad : Ctxt.Var Γ (.reg 64)) :
    Com jasminDialect Γ (.reg wY) :=
  Com.var
    (Expr.mk (JasminOp.stackStore wX nX) rfl
      (.cons X (.cons iStore (.cons vStore .nil))))
    (Com.var
      (Expr.mk (JasminOp.stackLoad wY nY) rfl
        (.cons (Ctxt.Var.there Y) (.cons (Ctxt.Var.there jLoad) .nil)))
      (Com.ret Ctxt.Var.here))

/-- The `storeThenDisjointLoad` program is `WellFormedStores`, **given the
    non-aliasing precondition** `ShapeDisjoint X Y`: its first binder is the
    `stackStore` into `X` (right disjunct), whose target — shifted under the
    store binder — is `Ctxt.Var.there X`, disjoint from the later load's source
    `Ctxt.Var.there Y` because `X` and `Y` are shape-disjoint
    (`ShapeDisjoint.there`). The trailing `ret` carries no obligation. -/
theorem storeThenDisjointLoad_wellFormed {Γ : Ctxt jasminDialect}
    {wX nX wY nY : Nat}
    (X : Ctxt.Var Γ (.stackArr wX nX)) (iStore : Ctxt.Var Γ (.reg 64))
    (vStore : Ctxt.Var Γ (.reg wX))
    (Y : Ctxt.Var Γ (.stackArr wY nY)) (jLoad : Ctxt.Var Γ (.reg 64))
    (hdisj : ShapeDisjoint X Y) :
    WellFormedStores (storeThenDisjointLoad X iStore vStore Y jLoad) := by
  refine ⟨Or.inr ⟨wX, nX, X, ⟨rfl, iStore, vStore, rfl⟩, ?_⟩, ?_⟩
  · -- LaterLoadsDisjoint (there X) (var load (ret here))
    refine ⟨?_, trivial⟩
    -- LoadDisjointFrom (there X) load: op is stackLoad, source is `there Y`.
    show ShapeDisjoint (Ctxt.Var.there X) (Ctxt.Var.there Y)
    exact hdisj.there
  · -- WellFormedStores of the load-then-ret tail (straight-line).
    refine ⟨Or.inl ?_, trivial⟩
    intro w n h
    exact absurd h (by simp)

/-- **Denotation of the worked instance.** Reusing the disjointness lemma, the
    program denotes to `Y`'s pre-store value at the load index — the store into
    the disjoint `X` is invisible to the load from `Y`. -/
theorem storeThenDisjointLoad_denote {Γ : Ctxt jasminDialect}
    {wX nX wY nY : Nat}
    (X : Ctxt.Var Γ (.stackArr wX nX)) (iStore : Ctxt.Var Γ (.reg 64))
    (vStore : Ctxt.Var Γ (.reg wX))
    (Y : Ctxt.Var Γ (.stackArr wY nY)) (jLoad : Ctxt.Var Γ (.reg 64))
    (V : Ctxt.Valuation Γ) :
    (storeThenDisjointLoad X iStore vStore Y jLoad).denote V
      = stackGet (Y.lookup V) (jLoad.lookup V).toNat :=
  stackStore_load_disjoint_denote X iStore vStore Y jLoad V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminStoreMemoryModel
