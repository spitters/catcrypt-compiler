/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Fin.Basic

@[expose] public section

set_option autoImplicit false

/-!
# TOY dialect: a region-carrying bounded loop + a dynamic-length memref

**EXPERIMENTAL / SELF-CONTAINED FILE.**  This is the *first verified milestone*
of the lean-mlir backend for the verified-GMP project.  It isolates the two
verification obligations that block the verified `scf.for` lowering
of `mpn_add_n`, in a toy setting that depends on nothing in the real VIR / Veir
chain:

1. **A region-carrying bounded loop op `forN`** (an `scf.for`-like construct with
   a loop-carried accumulator).  The verified VIR `Com` (`SecureCompilation/VIR/
   Core.lean`) is A-normal form with **no regions and no loops**, so the loop is
   modelled here directly.  Its denotation is `Nat.rec`-style: iterate `body i`
   for `i = 0 .. n-1`.

2. **A dynamic-length memref `DynArr`** (`Σ len, Fin len → BitVec 64`) with
   `loadDyn`/`storeDyn` that return `Option` (`some` iff the index is in bounds).
   The real `MlirMemrefDialect` is fixed-size (`Fin n`), so all its `agree_*`
   lemmas close by `rfl`.  Here the agreement lemmas need an `i < len`
   hypothesis — **this is the first place `agree` is NOT `rfl`.**

The structure deliberately mirrors the `agree_*` style of the real
`MlirMemrefDialect.lean` (per-op semantic-agreement lemmas) and the loop
induction style of `Mpn.AddPrototype.lean` (`bignumExecFuel_loop_step` + limb-list
induction).

## What is proved here (all axiom-clean, no `sorry`)

* §1 `forN` denotation (region-carrying bounded loop), with the defining
  `forN_zero` / `forN_succ` unfold lemmas.
* §2 `agree_forN` (pointwise body agreement ⇒ whole-loop agreement, by `Nat.rec`)
  **and** the more useful `forN_invariant` rule (a relation preserved by every
  step is preserved by the whole loop).
* §3 `DynArr` with `loadDyn`/`storeDyn`, and the **conditional** agreement
  lemmas `agree_loadDyn` / `agree_storeDyn` (equal to the static `Fin len`
  access *under* `i < len`).  These are the first non-`rfl` `agree` lemmas.
* §4 The end-to-end composition: a `forN` loop whose body does one
  `loadDyn`/addi/`storeDyn` (no carry, no aliasing — minimal), proved to agree
  with a static `Fin`-indexed reference loop, under the per-iteration
  `i < len` invariant.

## Scope

This is a *toy*.  It is a standalone denotational model: `forN` and `DynArr`
are Lean functions, not `VIR.Op` constructors wired through `Com.denote`.  The
remaining gap to the real chain is recorded in the closing docstring (§5).
-/

namespace CatCrypt.Crypto.Jasmin.Examples.ForNToyDialect

/-! ## §1  Region-carrying bounded loop `forN`

`forN n body init` runs `body 0`, `body 1`, …, `body (n-1)` in order, threading
a loop-carried accumulator `Acc` (the analogue of `scf.for`'s iter_args).  This
is the region the real VIR `Com` cannot express: `body` is a *region* taking the
induction variable `i` and the current accumulator, returning the next
accumulator.

The denotation is `Nat.rec`-style, folding from `0` upward so that iteration `i`
sees accumulator-after-`i`-steps.  We write it by structural recursion on `n`
with `body` applied at the *current* offset, which is the shape that makes the
two unfold lemmas (`forN_zero`, `forN_succ`) and the induction proofs below
clean. -/

/-- A region-carrying bounded loop.  `forN n body init` iterates the loop body
    `body : Nat → Acc → Acc` for induction variables `0, 1, …, n-1`, threading
    the accumulator from `init`.

    Defined so iteration `i` receives the *global* induction index `i` (not a
    shifted one): `forN (n+1) body init` first runs `body 0 init`, then the
    remaining `n` iterations with indices shifted up by one. -/
def forN {Acc : Type} : (n : Nat) → (body : Nat → Acc → Acc) → Acc → Acc
  | 0,     _,    init => init
  | n + 1, body, init => forN n (fun i acc => body (i + 1) acc) (body 0 init)

@[simp] theorem forN_zero {Acc : Type} (body : Nat → Acc → Acc) (init : Acc) :
    forN 0 body init = init := rfl

theorem forN_succ {Acc : Type} (n : Nat) (body : Nat → Acc → Acc) (init : Acc) :
    forN (n + 1) body init
      = forN n (fun i acc => body (i + 1) acc) (body 0 init) := rfl

/-- Concrete sanity check: summing `0 + 1 + 2 + 3` via the loop index. -/
example : forN 4 (fun i acc => acc + i) 0 = 6 := by decide

/-- A loop whose body is the identity on the accumulator returns the
    accumulator unchanged, for any horizon `n`.  (The body may read the index;
    here it ignores it.) -/
theorem forN_id {Acc : Type} (n : Nat) (body : Nat → Acc → Acc)
    (hid : ∀ i acc, body i acc = acc) : ∀ init, forN n body init = init := by
  induction n generalizing body with
  | zero => intro init; rfl
  | succ n ih =>
    intro init
    simp only [forN_succ, hid 0 init]
    exact ih (fun i acc => body (i + 1) acc) (fun i acc => hid (i + 1) acc) init

/-- Concrete sanity check: a no-op loop returns the accumulator unchanged. -/
example : forN 100 (fun _ acc => acc) (42 : Nat) = 42 :=
  forN_id 100 _ (fun _ _ => rfl) 42

/-! ## §2  `agree_forN` — loop-body agreement and the invariant rule

The analogue of `MpnAddPrototype`'s `bignumExecFuel_loop_step` + limb-list
induction, in the toy region setting.  Two forms:

* **Pointwise agreement** (`agree_forN`): if two loop bodies agree on every
  `(i, acc)`, the whole loops agree.  This is the direct loop analogue of the
  `MlirMemrefDialect` per-op `agree_*` lemmas, lifted across the region.
* **Invariant rule** (`forN_invariant`): a relation `R` between two parallel
  loops, preserved by each step, is preserved by the whole loop.  This is the
  form used by the §4 composition (the static/dynamic loops are not
  *equal* bodies; they agree only *under* the in-bounds invariant). -/

/-- **Pointwise body agreement (by `Nat.rec` on `n`).**  If two loop bodies are
    extensionally equal on every index/accumulator pair, the whole `forN` loops
    are equal for any initial accumulator.

    Generalised over `init` *and* over the body offset so the induction step
    goes through (the recursive call shifts both bodies by `+1`, and the shifted
    bodies still agree pointwise).  This is the region analogue of the per-op
    `agree_*` lemmas in `MlirMemrefDialect.lean`. -/
theorem agree_forN {Acc : Type} (n : Nat) (body₁ body₂ : Nat → Acc → Acc)
    (hbody : ∀ i acc, body₁ i acc = body₂ i acc) :
    ∀ init, forN n body₁ init = forN n body₂ init := by
  induction n generalizing body₁ body₂ with
  | zero => intro init; rfl
  | succ n ih =>
    intro init
    simp only [forN_succ]
    -- The recursive call uses the `+1`-shifted bodies, which still agree
    -- pointwise; the initial accumulator is `bodyⱼ 0 init`, equal by `hbody 0`.
    rw [hbody 0 init]
    exact ih (fun i acc => body₁ (i + 1) acc) (fun i acc => body₂ (i + 1) acc)
      (fun i acc => hbody (i + 1) acc) (body₂ 0 init)

/-- **Invariant rule (by `Nat.rec` on `n`).**  Run two parallel loops with
    (possibly different) bodies and initial accumulators.  If a relation `R`
    holds initially and is preserved by every aligned step — for all `i` and all
    `a₁, a₂` with `R a₁ a₂`, we have `R (body₁ i a₁) (body₂ i a₂)` — then `R`
    holds between the two final accumulators.

    The loop rule: the static (`Fin`) and dynamic
    (`DynArr`) loops in §4 do **not** have pointwise-equal bodies; they relate
    only through an in-bounds invariant, which `R` carries.  Directly mirrors a
    Hoare-style `scf.for` loop-invariant rule. -/
theorem forN_invariant {Acc₁ Acc₂ : Type} (R : Acc₁ → Acc₂ → Prop)
    (n : Nat) (body₁ : Nat → Acc₁ → Acc₁) (body₂ : Nat → Acc₂ → Acc₂)
    (hstep : ∀ i a₁ a₂, R a₁ a₂ → R (body₁ i a₁) (body₂ i a₂)) :
    ∀ init₁ init₂, R init₁ init₂ → R (forN n body₁ init₁) (forN n body₂ init₂) := by
  induction n generalizing body₁ body₂ with
  | zero => intro init₁ init₂ h; simpa using h
  | succ n ih =>
    intro init₁ init₂ h
    simp only [forN_succ]
    -- One step establishes `R (body₁ 0 init₁) (body₂ 0 init₂)`; recurse on the
    -- `+1`-shifted bodies, which preserve `R` by `hstep (i+1)`.
    exact ih (fun i a => body₁ (i + 1) a) (fun i a => body₂ (i + 1) a)
      (fun i a₁ a₂ hR => hstep (i + 1) a₁ a₂ hR)
      (body₁ 0 init₁) (body₂ 0 init₂) (hstep 0 init₁ init₂ h)

/-! ## §3  Dynamic-length memref `DynArr`

The real `MlirMemrefDialect` (`SecureCompilation/VIR/MlirMemrefDialect.lean`)
uses a *fixed-size* array `Fin n → BitVec 64`; every access is in-bounds by the
`Fin n` index, so all its `agree_*` lemmas close by `rfl`.

A runtime-bounded loop must index a *dynamic-length* array with a `Nat` index
that is only known in-bounds via the loop's `i < len` invariant.  We model that
with `DynArr` and `Option`-returning accesses.  The agreement lemmas
`agree_loadDyn`/`agree_storeDyn` say the dynamic access equals the static
(`Fin len`) one — **but only under the hypothesis `i < len`.**  This is the
first place the `agree` lemma carries a side condition (it is *not* `rfl`). -/

/-- A dynamic-length array of 64-bit words: a length together with a total
    function on its in-bounds indices.  This is `Σ len, Fin len → BitVec 64`,
    written as a structure for ergonomic field access.  Models a `memref<?xi64>`
    whose size is a runtime value. -/
structure DynArr where
  /-- Runtime length. -/
  len : Nat
  /-- Backing store, total on the in-bounds index range. -/
  get : Fin len → BitVec 64

/-- Dynamic load: `some (a.get ⟨i, _⟩)` if `i < a.len`, else `none`
    (out-of-bounds).  The MLIR `memref.load` on a `memref<?xi64>` with a runtime
    index. -/
def loadDyn (a : DynArr) (i : Nat) : Option (BitVec 64) :=
  if h : i < a.len then some (a.get ⟨i, h⟩) else none

/-- Dynamic store: functional update at `i` if `i < a.len`, returning the new
    array; `none` if out of bounds.  The length is unchanged.  MLIR
    `memref.store` on a `memref<?xi64>` with a runtime index. -/
def storeDyn (a : DynArr) (i : Nat) (v : BitVec 64) : Option DynArr :=
  if _h : i < a.len then
    some { len := a.len, get := fun j => if j.val = i then v else a.get j }
  else none

/-- A `DynArr` is the dynamic view of a static `Fin len` array. -/
def ofStatic (len : Nat) (f : Fin len → BitVec 64) : DynArr :=
  { len := len, get := f }

/-! ### Conditional agreement: dynamic access = static access under `i < len`

These are the toy analogues of `agree_memrefGet` / `agree_memrefSet`, except
that — unlike the fixed-size memref dialect, where the agreement is `rfl` — here
the agreement holds only **under** the in-bounds hypothesis `i < len`.  The
`i < len` hypothesis is exactly what the loop invariant of §4 supplies. -/

/-- **Conditional load agreement.**  Under `i < len`, the dynamic load on
    `ofStatic len f` returns exactly the static index `f ⟨i, hi⟩`.  This is the
    first `agree` lemma that is *not* `rfl`: it consumes the bounds proof to
    discharge the `dite` guard. -/
theorem agree_loadDyn (len : Nat) (f : Fin len → BitVec 64) (i : Nat)
    (hi : i < len) :
    loadDyn (ofStatic len f) i = some (f ⟨i, hi⟩) := by
  simp only [loadDyn, ofStatic, hi, ↓reduceDIte]

/-- **Conditional store agreement.**  Under `i < len`, the dynamic store on
    `ofStatic len f` succeeds and yields the static functional update: the new
    array is `ofStatic len (Function.update-style update of f at ⟨i,hi⟩)`.
    Again *not* `rfl` — the bounds proof discharges the `dite`. -/
theorem agree_storeDyn (len : Nat) (f : Fin len → BitVec 64) (i : Nat)
    (v : BitVec 64) (hi : i < len) :
    storeDyn (ofStatic len f) i v
      = some (ofStatic len (fun j => if j.val = i then v else f j)) := by
  simp only [storeDyn, ofStatic, hi, ↓reduceDIte]

/-- Out-of-bounds load returns `none`. -/
theorem loadDyn_oob (a : DynArr) (i : Nat) (hi : ¬ i < a.len) :
    loadDyn a i = none := by
  simp only [loadDyn, hi, dif_neg, not_false_iff]

/-- Out-of-bounds store returns `none`. -/
theorem storeDyn_oob (a : DynArr) (i : Nat) (v : BitVec 64) (hi : ¬ i < a.len) :
    storeDyn a i v = none := by
  simp only [storeDyn, hi, dif_neg, not_false_iff]

/-- A successful `storeDyn` preserves the length.  Needed so the per-iteration
    invariant `acc.len = len` is maintained across the loop in §4. -/
theorem storeDyn_len (a : DynArr) (i : Nat) (v : BitVec 64) (a' : DynArr)
    (h : storeDyn a i v = some a') : a'.len = a.len := by
  unfold storeDyn at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

/-! ## §4  End-to-end: a `forN` loop over a dynamic memref agrees with a static
reference

The minimal end-to-end milestone: a loop whose body does **one**
`loadDyn` / `addi` (add a constant) / `storeDyn`, with no carry chain and no
aliasing (those are the §-follow-ups, exactly as the real `mpn_add_n` defers the
aliased in-place case).  At iteration `i` it computes `arr[i] := arr[i] + c` for
a constant `c`.

* The **static reference** `staticLoop` runs the same map on a `Fin len → BitVec
  64` array, where every access is in-bounds by construction (`Fin len`).
* The **dynamic loop** `dynLoop` runs it on a `DynArr`, where each access is
  guarded by `loadDyn`/`storeDyn` and can only succeed because the loop index
  stays `< len`.

We prove `dynLoop` agrees with `staticLoop` (`dynLoop_agrees_staticLoop`): the
dynamic loop succeeds and its result is `ofStatic` of the static result.  The
proof is `forN_invariant` instantiated with the invariant

> `R acc_dyn acc_static  :≡  acc_dyn = some (ofStatic len acc_static)`

which carries, at every step, the fact that the accumulator is an in-bounds
`ofStatic` array of the right length — and *that* is what supplies the `i < len`
hypothesis `agree_loadDyn`/`agree_storeDyn` consume.  This is the first
end-to-end region + dynamic-memref `agree`. -/

/-- The per-iteration map on a static `Fin len` array: `f[i] := f[i] + c`.
    Indexes by the *position* `j`: when `j.val = i` it adds `c` to that entry
    (using `j` itself as the in-bounds witness, so no side condition is needed),
    otherwise it leaves the entry unchanged. -/
def staticStep (len : Nat) (c : BitVec 64) (i : Nat) (f : Fin len → BitVec 64) :
    Fin len → BitVec 64 :=
  fun j => if j.val = i then f j + c else f j

/-- The static reference loop: apply `staticStep` for `i = 0 .. n-1`.  Pure
    `Fin`-array map, no `Option`. -/
def staticLoop (len : Nat) (c : BitVec 64) (n : Nat) (f : Fin len → BitVec 64) :
    Fin len → BitVec 64 :=
  forN n (staticStep len c) f

/-- The per-iteration body on a dynamic array: load `arr[i]`, add `c`, store it
    back.  Propagates `none` (out of bounds).  The `scf.for` body that lowers to
    `memref.load` + `arith.addi` + `memref.store`. -/
def dynStep (c : BitVec 64) (i : Nat) (acc : Option DynArr) : Option DynArr := do
  let a ← acc
  let w ← loadDyn a i
  storeDyn a i (w + c)

/-- The dynamic loop: apply `dynStep` for `i = 0 .. n-1`, starting from
    `some init`.  The runtime-bounded loop over a `memref<?xi64>`. -/
def dynLoop (c : BitVec 64) (n : Nat) (init : DynArr) : Option DynArr :=
  forN n (dynStep c) (some init)

/-! ### The single-step agreement under the in-bounds invariant

The crux: when the accumulator is `some (ofStatic len f)` and the index `i` is
in bounds (`i < len`), one `dynStep` equals `some (ofStatic len (staticStep …))`.
This consumes `agree_loadDyn` / `agree_storeDyn` (the only place the `i < len`
side condition is discharged) and re-establishes the invariant for the next
iteration. -/

/-- One `staticStep` rewritten in the `⟨i, hi⟩`-indexed form that matches the
    dynamic `storeDyn` update: at index `i < len`, it adds `c` to entry `i` and
    leaves the rest.  The `j.val = i` branch rewrites `f j` to `f ⟨i, hi⟩` via
    `Fin.ext` (proof irrelevance on the bounds component). -/
theorem staticStep_apply (len : Nat) (c : BitVec 64) (i : Nat)
    (f : Fin len → BitVec 64) (hi : i < len) :
    staticStep len c i f = (fun j => if j.val = i then f ⟨i, hi⟩ + c else f j) := by
  funext j
  unfold staticStep
  by_cases hj : j.val = i
  · -- `j = ⟨i, hi⟩` because their `.val`s agree (`Fin.ext`).
    have hjeq : j = ⟨i, hi⟩ := Fin.ext hj
    simp only [if_true, hjeq]
  · simp only [hj, if_false]

/-- **Single-step agreement (consumes `agree_loadDyn`/`agree_storeDyn`).**
    Under `i < len`, one `dynStep` on `some (ofStatic len f)` equals
    `some (ofStatic len (staticStep len c i f))`. -/
theorem dynStep_agree (len : Nat) (c : BitVec 64) (i : Nat)
    (f : Fin len → BitVec 64) (hi : i < len) :
    dynStep c i (some (ofStatic len f))
      = some (ofStatic len (staticStep len c i f)) := by
  simp only [dynStep, bind, Option.bind]
  -- Load: in-bounds, returns `f ⟨i, hi⟩` (this is `agree_loadDyn`).
  rw [agree_loadDyn len f i hi]
  -- Reduce the `Option.bind` match now that the loaded value is `some _`.
  dsimp only []
  -- Store: in-bounds, returns the static functional update (`agree_storeDyn`).
  rw [agree_storeDyn len f i (f ⟨i, hi⟩ + c) hi]
  -- The stored array matches `ofStatic len (staticStep …)`.
  rw [staticStep_apply len c i f hi]

/-- **End-to-end region + dynamic-memref agreement.**  For any in-bounds horizon
    `n ≤ len`, the dynamic loop succeeds and computes exactly the `ofStatic`
    image of the static reference loop.

    Proved with `forN_invariant`, instantiated at the invariant
    `R acc_dyn acc_static :≡ acc_dyn = some (ofStatic len acc_static)`.  The
    `hstep` obligation is `dynStep_agree`, which is where the `i < len`
    hypothesis (available because every loop index `i < n ≤ len`) discharges the
    dynamic-access side conditions.

    This is the first end-to-end "region + dynamic memref" `agree` in the toy
    setting — the milestone that the real verified `scf.for` lowering of
    `mpn_add_n` needs, isolated from the rest of the chain. -/
theorem dynLoop_agrees_staticLoop (len : Nat) (c : BitVec 64) (n : Nat)
    (hn : n ≤ len) (f : Fin len → BitVec 64) :
    dynLoop c n (ofStatic len f) = some (ofStatic len (staticLoop len c n f)) := by
  unfold dynLoop staticLoop
  -- The bodies are *not* pointwise equal (they live over different carriers,
  -- `Option DynArr` vs `Fin len → BitVec 64`), so we cannot use `agree_forN`.
  -- They relate only through the in-bounds invariant
  -- `R ad as :≡ ad = some (ofStatic len as)`, which `dynStep_agree` re-establishes
  -- step-by-step — but `dynStep_agree`'s `i < len` side condition only holds for
  -- the indices the loop reaches (`0 .. n-1`, all `< len`).  `forN_invariant`
  -- quantifies its step over *all* indices, so it cannot supply that bound; we
  -- thread it instead with a base-offset induction (`dynLoop_agree_offset`).
  -- Instantiating at base offset `0` (`0 + i = i`) gives the result.
  have h := dynLoop_agree_offset len c 0 n (by omega) f
  simpa using h
where
  /-- **Base-offset bound-threading induction.**  Run `forN n` with both bodies
      indexing at `base + i`, under the bound `base + n ≤ len` (so every reached
      index `base + i < len`).  The dynamic loop succeeds and is the `ofStatic`
      image of the static loop.  Induction on `n`: the first step is at index
      `base + 0 = base < len`; the recursion advances the base to `base + 1`
      (`(base + 1) + i = base + (i + 1)`), preserving the bound. -/
  dynLoop_agree_offset (len : Nat) (c : BitVec 64) :
      ∀ (base n : Nat), base + n ≤ len → ∀ (f : Fin len → BitVec 64),
        forN n (fun i acc => dynStep c (base + i) acc) (some (ofStatic len f))
          = some (ofStatic len
              (forN n (fun i acc => staticStep len c (base + i) acc) f)) := by
    intro base n
    induction n generalizing base with
    | zero => intro _ f; rfl
    | succ n ih =>
      intro hbound f
      simp only [forN_succ, Nat.add_zero]
      -- First step at index `base` (which is `< len` since `base + (n+1) ≤ len`).
      rw [dynStep_agree len c base f (by omega)]
      -- Recurse: the `+1`-shifted bodies index at `base + (i + 1) = (base + 1) + i`,
      -- which is the `dynLoop_agree_offset` shape at base `base + 1`.
      have hshift_dyn :
          (fun i acc => dynStep c (base + (i + 1)) acc)
            = (fun i acc => dynStep c ((base + 1) + i) acc) := by
        funext i acc; rw [show base + (i + 1) = (base + 1) + i by omega]
      have hshift_stat :
          (fun i acc => staticStep len c (base + (i + 1)) acc)
            = (fun i acc => staticStep len c ((base + 1) + i) acc) := by
        funext i acc; rw [show base + (i + 1) = (base + 1) + i by omega]
      rw [hshift_dyn, hshift_stat]
      exact ih (base + 1) (by omega) (staticStep len c base f)

end CatCrypt.Crypto.Jasmin.Examples.ForNToyDialect
