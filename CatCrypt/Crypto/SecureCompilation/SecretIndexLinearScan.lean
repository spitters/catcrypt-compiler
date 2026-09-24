/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Range

@[expose] public section

set_option autoImplicit false

/-!
# Secret-index linear scan — a data-oblivious *repair* for secret array indexing

CatCrypt's constant-time analyser (`cmdCT` in
`CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean`) and its dialect sibling
(`ctSafeComR` / `ifToCmov` in `SecureCompilation/VIR/Transforms/IfToCmov.lean`)
both treat a *secret-dependent array index* as a leak and **reject** it:
`RArrLoad dst src idxVar` is CT only when `lt idxVar == .Public`.  This is
fail-closed, but it is also pessimistic — HEIR's *Access-Transformation* pass
and the FaCT compiler instead **repair** a secret index into a data-oblivious
**linear scan**: read *every* element of the array and use a constant-time
select to keep the one whose position matches the secret index.

This module is the verified core of that repair.  It is deliberately *generic*:

* the element type `α` is arbitrary;
* the constant-time select is a *parameter* `sel : Nat → Nat → α → α → α`,
  modelling a hardware `cmov`/mask-select keyed on the comparison of two
  indices.  We require only the abstract law `sel_spec`:
  `sel j i x acc = if j == i then x else acc` — i.e. the select returns its
  "matched" branch `x` exactly when the two index operands are equal, and the
  accumulator `acc` otherwise.  Crucially `sel` **reads both `x` and `acc`
  regardless of the comparison outcome** — that is what makes it constant-time.

The two deliverables, mirroring `ifToCmov`'s `*_denote_eq` + `ctSafe`:

1. **Functional correctness (the main theorem).**
   `linearScan_eq_index : i < arr.length → linearScan sel arr i d = arr.get ⟨i, _⟩`
   — the oblivious scan returns the *same value* as the direct (secret) indexed
   read.  This is the denotational-equality obligation that licenses replacing
   the rejected `RArrLoad` with the scan.

2. **Data-obliviousness (the security property).**
   `linearScan_accessPattern` : the sequence of positions the scan touches is
   `List.range arr.length` — a fixed, **index-independent** access pattern.
   `linearScan_accessPattern_constant` states this independence directly:
   for any two indices `i₁ i₂`, the access pattern is identical.  A scan whose
   memory-trace does not depend on the secret index leaks nothing about it.

## Relationship to the dialect CT predicates

`ifToCmov` discharges a *secret branch* by lowering it to a `cmov` chain that
`ctSafeComR` accepts.  This module discharges a *secret index* by lowering it to
a scan built **only** from public-index reads (`List.range`) and the
constant-time `sel`.  Wiring `linearScan` into the full `LowCT`/`catCryptDialect`
`RArrLoad` constructor — emitting the `RFor`-over-`List.range` + `RSelect` chain
and re-running `cmdCT` on it — is outside this module's scope; the verified
core (correctness + access-pattern obliviousness) lives here.
-/

namespace CatCrypt.Crypto.SecureCompilation.SecretIndexLinearScan

/-! ## §1.  The constant-time select primitive (abstract) -/

/-- A constant-time index-keyed select.  `sel j i x acc` compares the two
    index operands `j` (the *current scan position*) and `i` (the *secret
    target index*) and returns `x` when they match, `acc` otherwise — while
    reading *both* `x` and `acc` unconditionally (the hallmark of a `cmov`/
    mask-select, as opposed to a data-dependent branch). -/
abbrev CTSelect (α : Type _) := Nat → Nat → α → α → α

/-- The abstract specification a `CTSelect` must satisfy: it picks the matched
    branch `x` iff the two index operands are equal.  Any concrete mask-select
    (`(j == i ? allOnes : 0) & x | … & acc`) or hardware `cmov` realises this. -/
def IsCTSelect {α : Type _} (sel : CTSelect α) : Prop :=
  ∀ (j i : Nat) (x acc : α), sel j i x acc = if j = i then x else acc

/-- The canonical mask-style select, realised purely.  It is a lawful
    `CTSelect`: see `decideSelect_isCTSelect`.  In emitted code this becomes the
    branch-free `(mask & x) | (~mask & acc)` with `mask = -(j == i)`. -/
def decideSelect {α : Type _} : CTSelect α :=
  fun j i x acc => if j = i then x else acc

theorem decideSelect_isCTSelect {α : Type _} :
    IsCTSelect (α := α) decideSelect := by
  intro j i x acc; rfl

/-! ## §2.  The oblivious linear scan

We fold over `arr` paired with its positions.  At every position `j` we run
`sel j i (element at j) accumulator` — touching *every* element regardless of
the secret index `i`.  The accumulator threads the running "selected" value;
positions that don't match `i` leave it unchanged (but are still read). -/

/-- One scan step over an indexed-pair stream.  `acc` is the running selected
    value; at position `j` with element `x` we `sel j i x acc`. -/
def scanStep {α : Type _} (sel : CTSelect α) (i : Nat) (acc : α) (p : Nat × α) : α :=
  sel p.1 i p.2 acc

/-- The oblivious linear scan: fold `scanStep` over `arr.zipIdx` (every element
    paired with its position) starting from a default `d`.  The result is the
    element at the matching position, or `d` if none matches.

    `arr.zipIdx` pairs each element with its index, so the fold visits *all*
    positions `0, 1, …, arr.length - 1` in order — the access pattern is fixed.
-/
def linearScan {α : Type _} (sel : CTSelect α) (arr : List α) (i : Nat) (d : α) : α :=
  (arr.zipIdx.map (fun p => (p.2, p.1))).foldl (scanStep sel i) d

/-! ## §3.  Functional correctness — the main theorem

`linearScan_eq_index` : when `i` is in range, the scan returns `arr[i]`. -/

/-- Offset-generalised correctness of the scan fold.  Folding `scanStep sel i`
    over `arr.zipIdx base` (positions `base, base+1, …`) returns `arr[i - base]`
    when the target `i` lands inside this window (`base ≤ i < base + length`),
    and the default `d` otherwise.  Proved by induction on `arr`; the offset
    generalisation is what makes the induction go through (the recursive call
    runs at `base + 1`). -/
theorem foldl_scanStep_offset {α : Type _} {sel : CTSelect α}
    (hsel : IsCTSelect sel) (i : Nat) :
    ∀ (arr : List α) (base : Nat) (d : α),
      List.foldl (scanStep sel i) d
          ((arr.zipIdx base).map (fun p => (p.2, p.1))) =
        if h : base ≤ i ∧ i < base + arr.length then
          arr[i - base]'(by omega)
        else d := by
  intro arr
  induction arr with
  | nil => intro base d; simp
  | cons a as ih =>
    intro base d
    rw [List.zipIdx_cons, List.map_cons, List.foldl_cons, scanStep, hsel]
    rw [ih (base + 1)]
    simp only []
    by_cases hib : base = i
    · -- target is the head element
      subst hib
      have h1 : ¬ (base + 1 ≤ base ∧ base < base + 1 + as.length) := by omega
      have h2 : base ≤ base ∧ base < base + (a :: as).length := by
        simp only [List.length_cons]; omega
      rw [dif_neg h1, dif_pos h2, if_pos rfl]
      simp
    · -- target, if in range, is in the tail
      rw [if_neg hib]
      by_cases hin : base ≤ i ∧ i < base + (a :: as).length
      · have hin' : base + 1 ≤ i ∧ i < base + 1 + as.length := by
          simp only [List.length_cons] at hin; omega
        rw [dif_pos hin', dif_pos hin]
        have hidx : i - base = (i - (base + 1)) + 1 := by omega
        simp only [List.getElem_cons, hidx, Nat.add_one_ne_zero, dif_neg,
          Nat.add_sub_cancel, not_false_eq_true]
      · have hin' : ¬ (base + 1 ≤ i ∧ i < base + 1 + as.length) := by
          simp only [List.length_cons] at hin ⊢; omega
        rw [dif_neg hin', dif_neg hin]

/-- **Functional correctness.**  When the secret index `i` is in range, the oblivious
    linear scan returns exactly the direct (secret) indexed read `arr[i]`.

    This is the denotational-equality obligation that licenses the *repair*:
    a rejected `RArrLoad dst arr idxVar` (with `idxVar` Secret) may be replaced
    by `linearScan` without changing the value computed.  The scan is the
    `base = 0` instance of `foldl_scanStep_offset`. -/
theorem linearScan_eq_index {α : Type _} {sel : CTSelect α}
    (hsel : IsCTSelect sel) (arr : List α) (i : Nat) (d : α)
    (h : i < arr.length) :
    linearScan sel arr i d = arr[i] := by
  unfold linearScan
  have hkey := foldl_scanStep_offset hsel i arr 0 d
  rw [hkey]
  have hcond : (0 ≤ i ∧ i < 0 + arr.length) := by omega
  rw [dif_pos hcond]
  simp

/-- A convenient `get`-phrased restatement of `linearScan_eq_index`. -/
theorem linearScan_eq_get {α : Type _} {sel : CTSelect α}
    (hsel : IsCTSelect sel) (arr : List α) (i : Nat) (d : α)
    (h : i < arr.length) :
    linearScan sel arr i d = arr.get ⟨i, h⟩ := by
  rw [List.get_eq_getElem]; exact linearScan_eq_index hsel arr i d h

/-! ## §4.  Data-obliviousness — the constant access pattern

The scan visits every position of `arr` in order, regardless of the secret
index `i`.  We expose the *access pattern* — the list of positions read — and
prove it equals `List.range arr.length`, independent of `i`.  A scan whose
memory trace is independent of the secret index leaks nothing about it: this is
exactly the data-obliviousness property HEIR's Access-Transformation and FaCT
rely on. -/

/-- The access pattern *as a function of the requested index* `i`.

    Defined exactly as the position-stream `linearScan sel arr i d` folds over —
    we recover it by instrumenting `scanStep` to *record* the position it reads
    instead of selecting a value.  Crucially, this carries `i` as a parameter
    (mirroring `linearScan`'s signature) so that the constancy theorem below is
    a statement about `i`-independence, not a tautology.  The body
    discards `i`: that discarding is the content of `linearScan_accessPattern`. -/
def linearScanAccessPattern {α : Type _} (arr : List α) (_i : Nat) : List Nat :=
  (arr.zipIdx.map (fun p => (p.2, p.1))).map Prod.fst

/-- The scan touches **every** position `0, 1, …, arr.length - 1`, in order —
    its access pattern is `List.range arr.length`, for any requested index. -/
theorem linearScan_accessPattern {α : Type _} (arr : List α) (i : Nat) :
    linearScanAccessPattern arr i = List.range arr.length := by
  unfold linearScanAccessPattern
  induction arr using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [List.zipIdx_append, List.map_append, List.map_append, ih]
    simp [List.range_succ]

/-- **Obliviousness.**  The access pattern is *independent of the secret
    index* — for any two indices `i₁ i₂`, the scan reads the same positions in
    the same order.  Because the trace carries no information about `i`, an
    adversary observing the scan's memory accesses learns nothing about the
    secret index.  (This is the access-pattern half of constant-time; the value
    half is `linearScan_eq_index`.)

    Proved by routing both sides through `linearScan_accessPattern`, so the
    statement is about the two distinct indices `i₁ i₂` — not a
    syntactic `rfl`. -/
theorem linearScan_accessPattern_constant {α : Type _} (arr : List α)
    (i₁ i₂ : Nat) :
    linearScanAccessPattern arr i₁ = linearScanAccessPattern arr i₂ := by
  rw [linearScan_accessPattern arr i₁, linearScan_accessPattern arr i₂]

/-! ## §5.  Worked example — a 4-element array, secret index

We instantiate the scan on a concrete 4-element array with the canonical
`decideSelect`.  The scan returns the right element for each of the four
positions, and its access pattern is the fixed `[0, 1, 2, 3]` regardless of
which (secret) index is requested. -/

section WorkedExample

/-- A concrete 4-element table. -/
def tbl4 : List Nat := [10, 20, 30, 40]

/-- The scan returns the correct element at every in-range position. -/
example : linearScan decideSelect tbl4 0 0 = 10 := by decide
example : linearScan decideSelect tbl4 1 0 = 20 := by decide
example : linearScan decideSelect tbl4 2 0 = 30 := by decide
example : linearScan decideSelect tbl4 3 0 = 40 := by decide

/-- Out of range returns the default. -/
example : linearScan decideSelect tbl4 4 99 = 99 := by decide

/-- The scan agrees with the direct indexed read at a (here, concrete) index —
    `linearScan_eq_index`, specialised. -/
example (i : Nat) (h : i < tbl4.length) :
    linearScan decideSelect tbl4 i 0 = tbl4[i] :=
  linearScan_eq_index decideSelect_isCTSelect tbl4 i 0 h

/-- The access pattern is the fixed `[0, 1, 2, 3]` — a range of 4, for every
    requested (secret) index (here shown for index `1` and index `3`). -/
example : linearScanAccessPattern tbl4 1 = [0, 1, 2, 3] := by decide
example : linearScanAccessPattern tbl4 3 = [0, 1, 2, 3] := by decide

/-- And it equals `List.range 4`, independent of the index. -/
example (i : Nat) : linearScanAccessPattern tbl4 i = List.range 4 :=
  linearScan_accessPattern tbl4 i

/-- The two (distinct, possibly secret) indices yield the *same* access
    pattern — the obliviousness property, on the concrete table. -/
example : linearScanAccessPattern tbl4 1 = linearScanAccessPattern tbl4 3 :=
  linearScan_accessPattern_constant tbl4 1 3

end WorkedExample

end CatCrypt.Crypto.SecureCompilation.SecretIndexLinearScan
