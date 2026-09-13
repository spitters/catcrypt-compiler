/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
public import Mathlib.Data.List.GetD

/-!
# Register-allocation decisions for `JForProg`

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A `RegisterAllocation` is decision data over the binders of a `JForProg` body:
a slot map `slotOf : Nat → Nat` and a sequencing map `seqOf : Nat → Nat`. This
file computes such decisions with a linear scan over live ranges and proves
that the scan gives simultaneously live binders distinct slots.

`applyRA` returns its program argument and ignores the allocation. Every
theorem here that is stated over `applyRA` (`applyRA_denote_preserves`,
`linearScanRA_denote_preserves`) therefore holds for every allocation
(`applyRA_denote_preserves_of_any`) and states no property of the slot map.
Emit modules that read `seqOf` to name slots carry no theorem from this file
about the text they render. The register allocator with a semantic theorem is
`physScanSpill` (`toLprogPhysAbi_faithful_uniform`).

## Contents

* `RegisterAllocation` — the decision data (slot map and sequencing map).
* `RegisterAllocation.WellFormed` — injectivity of `slotOf` together with
  denotation preservation of `applyRA`; the second field holds by `rfl` for
  every allocation.
* `applyRA` — the identity on `JForProg`.
* `applyRA_denote_preserves` — denotation preservation under `WellFormed`;
  `applyRA_denote_preserves_of_any` is the same statement without the
  hypothesis.
* `RegisterAllocation.identity` and `identity_WellFormed` — the identity
  allocation.
* `linearScanRA_real` — the linear-scan allocation: live ranges from
  `computeLastUse`, lowest-free-slot assignment from `linearScanAssign`.
* `SlotOfInjectiveOnLive` and `linearScanRA_real_slotOfInjectiveOnLive` — the
  linear scan's guarantee, from the walker invariant in §7b: `busy` holds the
  pair of every allocated binder still live at the current position, and
  `linearScanStep` picks a slot outside it.
* `linearScanRA` and `linearScanRA_WellFormed` — the allocation with
  `slotOf := id` (`linearScanRA_slotOf_eq_id`) and the linear-scan slots in
  `seqOf`.

The sanity tests for `linearScanAssign` on small synthetic patterns use
`native_decide`; the definitions and theorems do not.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-! ## 1. The structural RA decision -/

/-- **A register-allocation decision.**

`slotOf k` assigns Com-variable index `k` (a fresh-SSA slot index `0, 1, …`
into the body's binder list) to a register slot identifier. `seqOf k` is a
second map over binder indices; `linearScanRA` stores the linear-scan slots
there, and emit modules such as `Sha2RaEmit` read it to name slots.
`linearScanRA` below constructs this structure from a `JForProg`. -/
structure RegisterAllocation where
  /-- `slotOf k` = register slot identifier for Com-binder index `k`. -/
  slotOf : Nat → Nat
  /-- `seqOf k` = sequencing order for Com-binder index `k`. -/
  seqOf : Nat → Nat

namespace RegisterAllocation

/-- **Identity register allocation**: every Com-binder is mapped to its own
slot, and the sequencing map is the identity. -/
def identity : RegisterAllocation where
  slotOf k := k
  seqOf k := k

/-! ## 2. `applyRA` -/

/-- **`applyRA p ra` is `p`.** The allocation argument is not read, so
`applyRA_denote_preserves` holds for every allocation
(`applyRA_denote_preserves_of_any`) and states no property of the slot map. -/
def applyRA {accTy : JasminTy} (p : JForProg accTy)
    (_ra : RegisterAllocation) : JForProg accTy :=
  p

/-- **Well-formedness predicate for a register allocation.**

The hypothesis of `applyRA_denote_preserves`. Its fields:

* `injOnLive`: global injectivity of `slotOf`. `linearScanRA` discharges it
  with `slotOf := id`; the live-range property of the linear scan is the
  separate `SlotOfInjectiveOnLive`.
* `preserves`: `applyRA p ra` denotes the same function as `p`; since
  `applyRA` is the identity, this holds by `rfl` for every allocation. -/
structure WellFormed (ra : RegisterAllocation) : Prop where
  /-- `slotOf` is globally injective. -/
  injOnLive : Function.Injective ra.slotOf
  /-- `applyRA` preserves `JForProg.denote` for any `JForProg` and initial
      accumulator; `rfl` for every allocation. -/
  preserves : ∀ {accTy : JasminTy} (p : JForProg accTy) (init : ⟦accTy⟧),
      (applyRA p ra).denote init = p.denote init

/-! ## 3. Denotation preservation of `applyRA` -/

/-- **Denotation preservation for a well-formed register allocation.**

For any `JForProg accTy` `p` and any `WellFormed` allocation `ra`,
`applyRA p ra` denotes the same function as `p`. The proof invokes the
`preserves` field. Because `applyRA` is the identity, the statement holds
without the hypothesis (`applyRA_denote_preserves_of_any`). -/
theorem applyRA_denote_preserves {accTy : JasminTy} (p : JForProg accTy)
    (ra : RegisterAllocation) (hwf : WellFormed ra) (init : ⟦accTy⟧) :
    (applyRA p ra).denote init = p.denote init :=
  hwf.preserves p init

/-! ## 4. Identity RA: well-formedness witness -/

/-- **The identity register allocation is well-formed.**

`slotOf k = k` is the identity function, hence injective. The
denotation-preservation witness is `rfl`, because `applyRA p identity = p`
definitionally. -/
theorem identity_WellFormed : WellFormed identity where
  injOnLive := fun _ _ h => h
  preserves := fun _ _ => rfl

/-! ## 5. Live-range analysis on the Com body

We model the loop body as a straight-line sequence of let-bindings (the
`Com.var … (Com.var … (Com.ret …))` chain). Each binder is identified by
its **position** `i` in left-to-right order, starting at `0`. The live
range of binder `i` is `(i, lastUse i)` where `lastUse i` is the position
of the latest later binder (or the `ret`-position) that uses the value
bound at `i`.

### Implementation strategy

We compute live ranges via a single forward pass that records, for each
binder position, the largest position at which the value is read. A
read at the `ret` is recorded as a use at position `numBinders p`.

### A note on intrinsic typing

`Com d Γ t` is intrinsically typed with De Bruijn indices: variables are
inhabitants of `Var Γ t`, not `Nat`. To compute live ranges we convert
each `Var` to its **De Bruijn level** (depth from the binder) via
`varToNat`. Combined with the *position* of the current `Com.var` node,
this gives the source binder's position in left-to-right order.

The result is a concrete linear-scan allocation: each binder gets the
lowest-numbered free slot, freeing slots as their last-use position
passes. This is the classical Poletto–Sarkar algorithm specialised to a
straight-line body. -/

/-- De Bruijn **depth** of a variable: `.here` is depth `0`, each
    `.there` adds `1`. This counts how many binders separate the use
    from the binding. -/
def varDepth {d : Dialect} : {Γ : Ctxt d} → {t : d.Ty} → Ctxt.Var Γ t → Nat
  | _, _, .here => 0
  | _ :: _, _, .there v => varDepth v + 1

/-- Largest De Bruijn depth reached by any variable in an `HVector`. -/
def hvectorMaxDepth {d : Dialect} {Γ : Ctxt d} :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var Γ ty) tys → Nat
  | [], .nil => 0
  | _ :: _, .cons v rest => max (varDepth v) (hvectorMaxDepth rest)

/-- Largest De Bruijn depth of any argument of `e`. -/
def exprMaxArgDepth {d : Dialect} [DialectSignature d]
    {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) : Nat :=
  hvectorMaxDepth e.args

/-- The `lastUse` array: a list of length `numBinders p` where the `i`-th
    entry is the latest position (binder index, or `numBinders p` for the
    `ret`) at which the value bound at position `i` is used.

    Implementation:
    - Walk the chain `Com.var e₀ (Com.var e₁ (… (Com.ret v)))` from
      position `0` upwards. The current position is the binder index
      `pos` we are about to introduce.
    - At each `Com.var e body`: for each argument variable `v` of `e`
      with `Var.toNat = d`, the value being read was bound at position
      `pos - 1 - d`. Record `pos` as a use of that position. Then recurse
      into the body at `pos + 1`.
    - At the terminal `Com.ret v`: record `numBinders` as a use of
      position `numBinders - 1 - v.toNat`.

    For binders that are never read after binding (dead code) the entry
    equals the binder's own position — they are dead and free
    immediately.

    The returned list has length `numBinders` and is indexed by binder
    position. -/
def computeLastUseAux {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (totalBinders : Nat) (pos : Nat) (uses : List Nat)
    (c : Com jasminDialect Γ t) : List Nat :=
  match c with
  | .ret v =>
      -- v is read at position `totalBinders` (the ret-position). The
      -- binder being read is `pos - 1 - varDepth v`. If `pos = 0`
      -- (the only var in scope is the accumulator) nothing to do.
      let d := varDepth v
      if d < pos then
        let bp := pos - 1 - d
        uses.set bp (max (uses.getD bp 0) totalBinders)
      else
        uses
  | .var e body =>
      -- For each argument of `e`, record the read at position `pos`.
      let argDepth := exprMaxArgDepth e
      let uses' :=
        -- We update every binder appearing in `e.args` (conservative
        -- over-approximation: walk depths `0..argDepth`, mark each as
        -- used at `pos` if `< pos`).
        (List.range (argDepth + 1)).foldl
          (fun acc d =>
            if d < pos then
              let bp := pos - 1 - d
              acc.set bp (max (acc.getD bp 0) pos)
            else acc) uses
      computeLastUseAux totalBinders (pos + 1) (uses' ++ [pos]) body

/-- The `lastUse` array for the body `p`. -/
def computeLastUse {accTy : JasminTy} (p : Com jasminDialect [accTy] accTy) :
    List Nat :=
  computeLastUseAux (Com.numBinders p) 0 [] p

/-- The live range of binder `i`: `some (start, lastUse)` if `i` is a
    valid binder position, `none` otherwise. `start` equals `i` (each
    binder is live from where it is bound). -/
def liveRange {accTy : JasminTy} (p : Com jasminDialect [accTy] accTy)
    (i : Nat) : Option (Nat × Nat) :=
  let lus := computeLastUse p
  lus[i]?.map (fun lu => (i, lu))

/-! ## 6. Concrete RA construction: `linearScanRA_real`

We run the classical linear-scan algorithm:

1. Compute `lastUse` for each binder (already done above).
2. Walk binders in position order `0, 1, …, n-1`. Maintain a
   `slotAt : Nat → Option Nat` map from "currently busy slot" to "binder
   whose live range owns it", and a `freeSlots : List Nat` of free slot
   numbers (sorted ascending).
3. At each binder `i`:
   - Reclaim any slots whose owning binder has `lastUse < i`.
   - Pop the lowest-numbered free slot (or allocate a fresh one if the
     free list is empty). Assign it to `i`.
   - Mark that slot busy until `lastUse i`.

The result is a `slotOf : Nat → Nat`. -/

/-- One step of the linear-scan walker.

    `busy : List (Nat × Nat)` is a list of `(slot, lastUse)` pairs: which
    slot is currently held by which "owner-last-use" timestamp. Slots are
    reclaimed (removed from `busy`) when their `lastUse < currentPos`.

    `nextFresh : Nat` is the smallest slot number never yet allocated.

    Returns the assigned slot for this binder, and the updated state. -/
def linearScanStep (currentPos : Nat) (lastUse : Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat) :
    Nat × List (Nat × Nat) × Nat :=
  -- Reclaim slots whose owner's last use is before currentPos.
  let busy' := busy.filter (fun p => p.2 ≥ currentPos)
  -- Find the lowest-numbered free slot. A slot s ∈ [0, nextFresh) is
  -- free iff it is not in busy'.
  let busySlots := busy'.map Prod.fst
  let free? := (List.range nextFresh).find? (fun s => !busySlots.contains s)
  match free? with
  | some s => (s, (s, lastUse) :: busy', nextFresh)
  | none   => (nextFresh, (nextFresh, lastUse) :: busy', nextFresh + 1)

/-- Run the linear-scan walker over the binder positions `[0, n)` and
    record the slot decision for each.

    Driven by a fuel `fuel` (initialised to `lastUse.length`); each step
    consumes one fuel unit. We walk the list `lastUse` left to right;
    `pos` is the current index. -/
def linearScanAssignAux (fuel pos : Nat) (lastUse : List Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat) (acc : List Nat) :
    List Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
      match lastUse[pos]? with
      | none => acc
      | some lu =>
          let (s, busy', nextFresh') := linearScanStep pos lu busy nextFresh
          linearScanAssignAux fuel' (pos + 1) lastUse busy' nextFresh' (acc ++ [s])

/-- Linear-scan slot assignment. -/
def linearScanAssign (lastUse : List Nat) : List Nat :=
  linearScanAssignAux lastUse.length 0 lastUse [] 0 []

/-- **Concrete linear-scan RA construction (real algorithm).**

For a program `p` with body `update : Com jasminDialect [accTy] accTy`:

1. Compute `lastUse` for each binder position via `computeLastUse`.
2. Run `linearScanAssign` to get a `List Nat` mapping binder index →
   slot number.
3. Expose this list via `slotOf` (with a default of `n` for
   out-of-range indices — i.e. positions past the last binder map to a
   fresh slot, never colliding with a live binder).

The `seqOf` order is the binder order (sequential by position). -/
def linearScanRA_real {accTy : JasminTy} (p : JForProg accTy) :
    RegisterAllocation :=
  let lu := computeLastUse p.update
  let slots := linearScanAssign lu
  { slotOf := fun k => slots.getD k (slots.length + k)
    seqOf := fun k => k }

/-! ## 7. The allocation's own property

`applyRA` and `applyRA_real` are the identity, so no theorem about them
constrains an allocation. No theorem in this file relates an emit pass that
reads `slotOf` or `seqOf` to the program it renders. -/

/-- **`applyRA_real p ra` is `p`**, on a single `Com` body; the allocation
    argument is not read. -/
def applyRA_real {accTy : JasminTy} (p : Com jasminDialect [accTy] accTy)
    (_ra : RegisterAllocation) : Com jasminDialect [accTy] accTy :=
  p

/-! ### The allocator's own obligation

`WellFormed` receives the injectivity of `id` (see `linearScanRA` in §8), and
its `preserves` field is `rfl` because `applyRA` is the identity. The `Prop`
below is the property that carries the allocator's
content; §7b proves it of `linearScanRA_real`. -/

/-- Two binders that are simultaneously live -- each still live at the other's
    position -- get distinct slots under the real allocation.
    `linearScanRA_real_slotOfInjectiveOnLive` proves it. -/
def SlotOfInjectiveOnLive {accTy : JasminTy} (p : JForProg accTy) : Prop :=
  ∀ k₁ k₂, k₁ ≠ k₂ →
    k₂ ≤ (computeLastUse p.update).getD k₁ 0 →
    k₁ ≤ (computeLastUse p.update).getD k₂ 0 →
    (linearScanRA_real p).slotOf k₁ ≠ (linearScanRA_real p).slotOf k₂

/-- `applyRA` is the identity, so denotation preservation holds for every
    allocation, well-formed or not; the `WellFormed` argument of
    `applyRA_denote_preserves` is not needed. -/
theorem applyRA_denote_preserves_of_any {accTy : JasminTy} (p : JForProg accTy)
    (ra : RegisterAllocation) (init : ⟦accTy⟧) :
    (applyRA p ra).denote init = p.denote init := rfl

/-! ### 7b. The linear scan gives simultaneously-live binders distinct slots

`linearScanAssignAux` walks the binder positions in increasing order. The
invariant carried below is that `busy` holds the `(slot, lastUse)` pair of every
already-allocated binder still live at the current position, and that every slot
in `busy` is smaller than `nextFresh`. `linearScanStep` picks a slot outside
`busy`, so a binder still live when a later binder is allocated keeps its slot to
itself. -/

/-- Fuel exhaustion returns the accumulator. -/
theorem linearScanAssignAux_zero (pos : Nat) (lastUse : List Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat) (acc : List Nat) :
    linearScanAssignAux 0 pos lastUse busy nextFresh acc = acc := rfl

/-- Past the last binder position the walk returns the accumulator. -/
theorem linearScanAssignAux_succ_none {fuel pos : Nat} {lastUse : List Nat}
    {busy : List (Nat × Nat)} {nextFresh : Nat} {acc : List Nat}
    (h : lastUse[pos]? = none) :
    linearScanAssignAux (fuel + 1) pos lastUse busy nextFresh acc = acc := by
  simp [linearScanAssignAux, h]

/-- One walk step: the slot chosen at `pos` is appended to the accumulator and
    the walk continues at `pos + 1` with the updated busy list. -/
theorem linearScanAssignAux_succ_some {fuel pos : Nat} {lastUse : List Nat}
    {busy : List (Nat × Nat)} {nextFresh lu : Nat} {acc : List Nat}
    (h : lastUse[pos]? = some lu) :
    linearScanAssignAux (fuel + 1) pos lastUse busy nextFresh acc =
      linearScanAssignAux fuel (pos + 1) lastUse
        (linearScanStep pos lu busy nextFresh).2.1
        (linearScanStep pos lu busy nextFresh).2.2
        (acc ++ [(linearScanStep pos lu busy nextFresh).1]) := by
  simp [linearScanAssignAux, h]

/-- The slot handed out at `currentPos` differs from the slot of every binder in
    `busy` that is still live at `currentPos`. -/
theorem linearScanStep_slot_ne_of_live (currentPos lu : Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat)
    (hbusy : ∀ q ∈ busy, q.1 < nextFresh)
    (q : Nat × Nat) (hq : q ∈ busy) (hlive : currentPos ≤ q.2) :
    q.1 ≠ (linearScanStep currentPos lu busy nextFresh).1 := by
  have hmem : q.1 ∈ (busy.filter (fun p => p.2 ≥ currentPos)).map Prod.fst :=
    List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simpa using hlive⟩, rfl⟩
  simp only [linearScanStep]
  cases hfind : (List.range nextFresh).find?
      (fun s => !((busy.filter (fun p => p.2 ≥ currentPos)).map Prod.fst).contains s) with
  | none => exact Nat.ne_of_lt (hbusy q hq)
  | some s =>
      dsimp only
      have hs := List.find?_some hfind
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hs
      intro hEq
      exact hs (hEq ▸ hmem)

/-- The pair allocated at `currentPos` is in the updated busy list. -/
theorem linearScanStep_mem_self (currentPos lu : Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat) :
    ((linearScanStep currentPos lu busy nextFresh).1, lu) ∈
      (linearScanStep currentPos lu busy nextFresh).2.1 := by
  simp only [linearScanStep]
  cases hfind : (List.range nextFresh).find?
      (fun s => !((busy.filter (fun p => p.2 ≥ currentPos)).map Prod.fst).contains s) with
  | none => simp
  | some s => simp

/-- A pair still live at `currentPos` survives the reclaim filter. -/
theorem linearScanStep_mem_of_live (currentPos lu : Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat)
    (q : Nat × Nat) (hq : q ∈ busy) (hlive : currentPos ≤ q.2) :
    q ∈ (linearScanStep currentPos lu busy nextFresh).2.1 := by
  have hmem : q ∈ busy.filter (fun p => p.2 ≥ currentPos) :=
    List.mem_filter.mpr ⟨hq, by simpa using hlive⟩
  simp only [linearScanStep]
  cases hfind : (List.range nextFresh).find?
      (fun s => !((busy.filter (fun p => p.2 ≥ currentPos)).map Prod.fst).contains s) with
  | none => simp [hmem]
  | some s => simp [hmem]

/-- Every slot in the updated busy list is below the updated `nextFresh`. -/
theorem linearScanStep_busy_lt (currentPos lu : Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat)
    (hbusy : ∀ q ∈ busy, q.1 < nextFresh) :
    ∀ q ∈ (linearScanStep currentPos lu busy nextFresh).2.1,
      q.1 < (linearScanStep currentPos lu busy nextFresh).2.2 := by
  simp only [linearScanStep]
  cases hfind : (List.range nextFresh).find?
      (fun s => !((busy.filter (fun p => p.2 ≥ currentPos)).map Prod.fst).contains s) with
  | none =>
      dsimp only
      intro q hq
      rcases List.mem_cons.mp hq with h | h
      · subst h; omega
      · exact Nat.lt_succ_of_lt (hbusy q (List.mem_of_mem_filter h))
  | some s =>
      have hs : s ∈ List.range nextFresh := List.mem_of_find?_eq_some hfind
      intro q hq
      rcases List.mem_cons.mp hq with h | h
      · subst h; simpa using List.mem_range.mp hs
      · exact hbusy q (List.mem_of_mem_filter h)

/-- The accumulator is a prefix of the walk's result. -/
theorem linearScanAssignAux_prefix (fuel : Nat) :
    ∀ (pos : Nat) (lastUse : List Nat) (busy : List (Nat × Nat))
      (nextFresh : Nat) (acc : List Nat),
      ∃ tail, linearScanAssignAux fuel pos lastUse busy nextFresh acc = acc ++ tail := by
  induction fuel with
  | zero =>
      intro pos lastUse busy nextFresh acc
      exact ⟨[], by simp [linearScanAssignAux_zero]⟩
  | succ fuel ih =>
      intro pos lastUse busy nextFresh acc
      cases hlu : lastUse[pos]? with
      | none => exact ⟨[], by simp [linearScanAssignAux_succ_none hlu]⟩
      | some lu =>
          obtain ⟨tail, htail⟩ := ih (pos + 1) lastUse
            (linearScanStep pos lu busy nextFresh).2.1
            (linearScanStep pos lu busy nextFresh).2.2
            (acc ++ [(linearScanStep pos lu busy nextFresh).1])
          refine ⟨(linearScanStep pos lu busy nextFresh).1 :: tail, ?_⟩
          rw [linearScanAssignAux_succ_some hlu, htail]
          simp

/-- Slots already recorded in the accumulator are unchanged by the rest of the
    walk. -/
theorem linearScanAssignAux_getD_of_lt {fuel pos : Nat} {lastUse : List Nat}
    {busy : List (Nat × Nat)} {nextFresh : Nat} {acc : List Nat} {k : Nat}
    (hk : k < acc.length) :
    (linearScanAssignAux fuel pos lastUse busy nextFresh acc).getD k 0 =
      acc.getD k 0 := by
  obtain ⟨tail, htail⟩ := linearScanAssignAux_prefix fuel pos lastUse busy nextFresh acc
  rw [htail, List.getD_append _ _ _ _ hk]

/-- **Slot injectivity on the live range, for the walker.** If binder `k₁` is
    still live at the position of a later binder `k₂`, the two get distinct
    slots. The busy list holds the pair of every allocated binder still live at
    the current position, so the step at `k₂` picks a slot that `k₁` does not
    hold. -/
theorem linearScanAssignAux_live_ne (fuel : Nat) :
    ∀ (pos : Nat) (lastUse : List Nat) (busy : List (Nat × Nat))
      (nextFresh : Nat) (acc : List Nat),
      acc.length = pos →
      (∀ j, j < pos → pos ≤ lastUse.getD j 0 →
        (acc.getD j 0, lastUse.getD j 0) ∈ busy) →
      (∀ q ∈ busy, q.1 < nextFresh) →
      lastUse.length ≤ pos + fuel →
      ∀ k₁ k₂, k₁ < k₂ → pos ≤ k₂ → k₂ < lastUse.length →
        k₂ ≤ lastUse.getD k₁ 0 →
        (linearScanAssignAux fuel pos lastUse busy nextFresh acc).getD k₁ 0 ≠
          (linearScanAssignAux fuel pos lastUse busy nextFresh acc).getD k₂ 0 := by
  induction fuel with
  | zero =>
      intro pos lastUse busy nextFresh acc _ _ _ hfuel k₁ k₂ _ hpos hk₂ _
      omega
  | succ fuel ih =>
      intro pos lastUse busy nextFresh acc hlen hinv hfresh hfuel k₁ k₂ hk12 hpos hk₂ hlive
      cases hlu : lastUse[pos]? with
      | none =>
          exact absurd (List.getElem?_eq_none_iff.mp hlu) (by omega)
      | some lu =>
          have hluD : lastUse.getD pos 0 = lu := by
            simp [List.getD_eq_getElem?_getD, hlu]
          rw [linearScanAssignAux_succ_some hlu]
          rcases Nat.lt_or_ge pos k₂ with hlt | hge
          · refine ih (pos + 1) lastUse (linearScanStep pos lu busy nextFresh).2.1
              (linearScanStep pos lu busy nextFresh).2.2
              (acc ++ [(linearScanStep pos lu busy nextFresh).1])
              (by simp [hlen]) ?_
              (linearScanStep_busy_lt pos lu busy nextFresh hfresh)
              (by omega) k₁ k₂ hk12 hlt hk₂ hlive
            intro j hj hjlive
            rcases Nat.lt_or_ge j pos with hjp | hjp
            · rw [List.getD_append _ _ _ _ (by omega)]
              exact linearScanStep_mem_of_live pos lu busy nextFresh _
                (hinv j hjp (by omega)) (by omega)
            · have hjeq : j = pos := by omega
              subst hjeq
              rw [List.getD_append_right _ _ _ _ (by omega), hluD]
              simpa [hlen] using linearScanStep_mem_self _ lu busy nextFresh
          · have hk2 : k₂ = pos := by omega
            subst hk2
            rw [linearScanAssignAux_getD_of_lt (by simp [hlen]; omega),
              linearScanAssignAux_getD_of_lt (by simp [hlen]),
              List.getD_append _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega)]
            simpa [hlen] using
              linearScanStep_slot_ne_of_live _ lu busy nextFresh hfresh
                (acc.getD k₁ 0, lastUse.getD k₁ 0) (hinv k₁ (by omega) hlive) hlive

/-- The slot handed out at a step is below the step's updated `nextFresh`. -/
theorem linearScanStep_slot_lt_next (currentPos lu : Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat) :
    (linearScanStep currentPos lu busy nextFresh).1 <
      (linearScanStep currentPos lu busy nextFresh).2.2 := by
  simp only [linearScanStep]
  cases hfind : (List.range nextFresh).find?
      (fun s => !((busy.filter (fun p => p.2 ≥ currentPos)).map Prod.fst).contains s) with
  | none => dsimp only; omega
  | some s =>
      have hs := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      dsimp only; omega

/-- A step raises `nextFresh` by at most one, and never lowers it. -/
theorem linearScanStep_next_bounds (currentPos lu : Nat)
    (busy : List (Nat × Nat)) (nextFresh : Nat) :
    nextFresh ≤ (linearScanStep currentPos lu busy nextFresh).2.2 ∧
      (linearScanStep currentPos lu busy nextFresh).2.2 ≤ nextFresh + 1 := by
  simp only [linearScanStep]
  cases hfind : (List.range nextFresh).find?
      (fun s => !((busy.filter (fun p => p.2 ≥ currentPos)).map Prod.fst).contains s) with
  | none => dsimp only; omega
  | some s => dsimp only; omega

/-- The walk assigns one slot per remaining binder position. -/
theorem linearScanAssignAux_length (fuel : Nat) :
    ∀ (pos : Nat) (lastUse : List Nat) (busy : List (Nat × Nat))
      (nextFresh : Nat) (acc : List Nat),
      acc.length = pos → pos + fuel = lastUse.length →
      (linearScanAssignAux fuel pos lastUse busy nextFresh acc).length =
        lastUse.length := by
  induction fuel with
  | zero =>
      intro pos lastUse busy nextFresh acc hlen hfuel
      rw [linearScanAssignAux_zero]; omega
  | succ fuel ih =>
      intro pos lastUse busy nextFresh acc hlen hfuel
      obtain ⟨lu, hlu⟩ : ∃ lu, lastUse[pos]? = some lu :=
        ⟨lastUse[pos]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      rw [linearScanAssignAux_succ_some hlu]
      exact ih (pos + 1) lastUse _ _ _ (by simp [hlen]) (by omega)

/-- Every slot the walk hands out is below the number of binders it has walked. -/
theorem linearScanAssignAux_lt_length (fuel : Nat) :
    ∀ (pos : Nat) (lastUse : List Nat) (busy : List (Nat × Nat))
      (nextFresh : Nat) (acc : List Nat),
      acc.length = pos → nextFresh ≤ pos → (∀ x ∈ acc, x < nextFresh) →
      ∀ x ∈ linearScanAssignAux fuel pos lastUse busy nextFresh acc,
        x < (linearScanAssignAux fuel pos lastUse busy nextFresh acc).length := by
  induction fuel with
  | zero =>
      intro pos lastUse busy nextFresh acc hlen hnext hacc x hx
      rw [linearScanAssignAux_zero] at hx ⊢
      exact Nat.lt_of_lt_of_le (hacc x hx) (by omega)
  | succ fuel ih =>
      intro pos lastUse busy nextFresh acc hlen hnext hacc x hx
      cases hlu : lastUse[pos]? with
      | none =>
          rw [linearScanAssignAux_succ_none hlu] at hx ⊢
          exact Nat.lt_of_lt_of_le (hacc x hx) (by omega)
      | some lu =>
          rw [linearScanAssignAux_succ_some hlu] at hx ⊢
          obtain ⟨hge, hle⟩ := linearScanStep_next_bounds pos lu busy nextFresh
          refine ih (pos + 1) lastUse _ _ _ (by simp [hlen]) (by omega) ?_ x hx
          intro y hy
          rcases List.mem_append.mp hy with h | h
          · exact Nat.lt_of_lt_of_le (hacc y h) hge
          · rw [List.mem_singleton.mp h]
            exact linearScanStep_slot_lt_next pos lu busy nextFresh

/-- **The linear scan gives simultaneously-live binders distinct slots.** If
    binder `k₁` is still live at the position of the later binder `k₂`, the two
    slots differ. -/
theorem linearScanAssign_live_ne (lastUse : List Nat) (k₁ k₂ : Nat)
    (hlt : k₁ < k₂) (hk₂ : k₂ < lastUse.length)
    (hlive : k₂ ≤ lastUse.getD k₁ 0) :
    (linearScanAssign lastUse).getD k₁ 0 ≠ (linearScanAssign lastUse).getD k₂ 0 :=
  linearScanAssignAux_live_ne lastUse.length 0 lastUse [] 0 [] rfl
    (by intro j hj; omega) (by simp) (by omega) k₁ k₂ hlt (Nat.zero_le _) hk₂ hlive

/-- The two binders of the `[1, 1]` last-use pattern are each live at the
    other's position, so the separation theorem applies to them. -/
example : (linearScanAssign [1, 1]).getD 0 0 ≠ (linearScanAssign [1, 1]).getD 1 0 :=
  linearScanAssign_live_ne [1, 1] 0 1 (by omega) (by decide) (by decide)

/-- The assignment has one entry per binder position. -/
theorem linearScanAssign_length (lastUse : List Nat) :
    (linearScanAssign lastUse).length = lastUse.length :=
  linearScanAssignAux_length lastUse.length 0 lastUse [] 0 [] rfl (by omega)

/-- Every assigned slot is below the number of binders. -/
theorem linearScanAssign_lt_length (lastUse : List Nat) :
    ∀ x ∈ linearScanAssign lastUse, x < (linearScanAssign lastUse).length :=
  linearScanAssignAux_lt_length lastUse.length 0 lastUse [] 0 [] rfl (by omega)
    (by simp)

/-- **Slot separation including the out-of-range fallback.** Two distinct
    indices, each still live at the other's position, get distinct values from
    the slot map `linearScanRA_real` exposes: in range they are separated by the
    linear scan, and out of range the fallback `length + k` is injective and
    above every assigned slot. -/
theorem linearScanAssign_getD_ne_of_live (lastUse : List Nat) (k₁ k₂ : Nat)
    (hne : k₁ ≠ k₂) (h₁ : k₂ ≤ lastUse.getD k₁ 0) (h₂ : k₁ ≤ lastUse.getD k₂ 0) :
    (linearScanAssign lastUse).getD k₁ ((linearScanAssign lastUse).length + k₁) ≠
      (linearScanAssign lastUse).getD k₂
        ((linearScanAssign lastUse).length + k₂) := by
  have hlen := linearScanAssign_length lastUse
  rcases Nat.lt_or_ge k₁ (linearScanAssign lastUse).length with hk₁ | hk₁ <;>
    rcases Nat.lt_or_ge k₂ (linearScanAssign lastUse).length with hk₂ | hk₂
  · rw [List.getD_eq_getElem _ _ hk₁, List.getD_eq_getElem _ _ hk₂,
      ← List.getD_eq_getElem _ 0 hk₁, ← List.getD_eq_getElem _ 0 hk₂]
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact linearScanAssign_live_ne lastUse k₁ k₂ h (by omega) h₁
    · exact (linearScanAssign_live_ne lastUse k₂ k₁ h (by omega) h₂).symm
  · rw [List.getD_eq_getElem _ _ hk₁, List.getD_eq_default _ _ hk₂]
    have : (linearScanAssign lastUse)[k₁] < (linearScanAssign lastUse).length :=
      linearScanAssign_lt_length lastUse _ (List.getElem_mem hk₁)
    omega
  · rw [List.getD_eq_getElem _ _ hk₂, List.getD_eq_default _ _ hk₁]
    have : (linearScanAssign lastUse)[k₂] < (linearScanAssign lastUse).length :=
      linearScanAssign_lt_length lastUse _ (List.getElem_mem hk₂)
    omega
  · rw [List.getD_eq_default _ _ hk₁, List.getD_eq_default _ _ hk₂]
    omega

/-- **The real linear-scan allocation is injective on the live range.** Two
    binders each still live at the other's position get distinct slots. -/
theorem linearScanRA_real_slotOfInjectiveOnLive {accTy : JasminTy}
    (p : JForProg accTy) : SlotOfInjectiveOnLive p :=
  fun k₁ k₂ hne h₁ h₂ =>
    linearScanAssign_getD_ne_of_live (computeLastUse p.update) k₁ k₂ hne h₁ h₂

/-! ## 8. `linearScanRA`

`linearScanRA` packages `linearScanRA_real` with `slotOf := id`, which
discharges `WellFormed.injOnLive`, and places the linear-scan slots in
`seqOf`. -/

/-- **The linear-scan allocation with identity `slotOf`.** `slotOf` is `id`;
`seqOf k` is the slot `linearScanRA_real` assigns to binder `k`. -/
def linearScanRA {accTy : JasminTy} (p : JForProg accTy) :
    RegisterAllocation :=
  -- `slotOf := id` discharges `injOnLive`; the linear-scan slot map is `seqOf`.
  let real := linearScanRA_real p
  { slotOf := id
    seqOf  := fun k => real.slotOf k }

/-- **`linearScanRA` is well-formed.** `injOnLive` is the injectivity of `id`;
`preserves` holds by `rfl` because `applyRA` is the identity (see
`linearScanRA_slotOf_eq_id`). -/
theorem linearScanRA_WellFormed {accTy : JasminTy} (p : JForProg accTy) :
    WellFormed (linearScanRA p) where
  injOnLive := fun _ _ h => h
  preserves := fun _ _ => rfl

/-- **`applyRA p (linearScanRA p)` denotes the same function as `p`.** It holds
because `applyRA` is the identity (`applyRA_denote_preserves_of_any`); it
states no property of the linear-scan slots. -/
theorem linearScanRA_denote_preserves {accTy : JasminTy} (p : JForProg accTy)
    (init : ⟦accTy⟧) :
    (applyRA p (linearScanRA p)).denote init = p.denote init :=
  applyRA_denote_preserves p (linearScanRA p) (linearScanRA_WellFormed p) init

/-- The `slotOf` of `linearScanRA` is the identity, so
    `linearScanRA_WellFormed`'s `injOnLive` is the injectivity of `id` and says
    nothing about `linearScanAssign`. The allocation's own guarantee is
    `SlotOfInjectiveOnLive`, proved of `linearScanRA_real` by
    `linearScanRA_real_slotOfInjectiveOnLive`. -/
theorem linearScanRA_slotOf_eq_id {accTy : JasminTy} (p : JForProg accTy) :
    (linearScanRA p).slotOf = id := rfl

/-! ## 9. Sanity tests for the live-range / slot-assignment infrastructure

These are `example` decls that confirm `computeLastUse` and
`linearScanAssign` behave correctly on simple synthetic patterns. -/

/-- The empty list of binders gets the empty slot assignment. -/
example : linearScanAssign [] = [] := by native_decide

/-- A single dead binder (last use = its own position) gets slot `0`. -/
example : linearScanAssign [0] = [0] := by native_decide

/-- Two binders, the first live until position 1, the second dead: the
    first gets slot 0, the second gets slot 1 (since slot 0 is still
    busy when the second is allocated). -/
example : linearScanAssign [1, 1] = [0, 1] := by native_decide

/-- Two binders, the first dead at its own position, the second live
    at position 1: the first gets slot 0, the second also gets slot 0
    (the slot was freed before the second binder is processed). -/
example : linearScanAssign [0, 1] = [0, 0] := by native_decide

end RegisterAllocation

end CatCrypt.Crypto.SecureCompilation.VIR
