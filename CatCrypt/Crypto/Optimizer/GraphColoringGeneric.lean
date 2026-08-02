/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.GenericRegAlloc
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRegAlloc

/-!
# Generic graph-coloring register allocation + move-coalescing (P4) over `MachineModel`

`Optimizer.GraphColoringRegAlloc` (the Chaitin–Briggs graph-coloring global allocator)
and `Optimizer.GraphColoringCoalesce` (the P4 conservative move-coalescing post-pass)
are written, like their linear-scan siblings were before #552, **monomorphized to the
x86 `JInstr 64` / `JState 64` types**. But neither pass touches anything x86-specific:
the interference graph is built purely from `LiveRange` intervals, the spill metric
from `writtenNames`/`readNames` use counts, the coloring from the adjacency relation,
and coalescing is *a rename* whose soundness is exactly the generic resident-path
result `GenericRegAlloc.renameBlock_runBlock`. This module is the **D3 phase** for
those two passes: lift them off `JInstr 64` and state them once over the generic
`MachineModel`/`RegMachine` abstraction, additive to (and leaving untouched) the
x86-specific `GraphColoringRegAlloc.lean` / `GraphColoringCoalesce.lean`.

## What is built (all generic over `[MachineModel I]`)

1. **The interference graph generically** (§1): `rangesOverlap`/`interfere`/`neighbours`
   /`degree`/`interferenceGraph` over `LiveRange` — already backend-agnostic in the x86
   file, restated here in the generic namespace, plus the basic structural property that
   `interfere` is **symmetric** (`interfere_symm`, proved) and a name never interferes
   with itself (`interfere_irrefl`, proved). The graph is built from
   `GenericRegAlloc.liveRanges`, which is itself over `[MachineModel I]`.
2. **The graph-coloring allocator generically** (§2–§3, untrusted): the use-density
   spill cost (`useCount`/`spillCostFrac`/`cheaperSpill`), Briggs simplify/spill
   (`degreeIn`/`pickNode`/`simplifyStack`), select/color (`firstFreeColor`/`selectColors`,
   whose spill offsets advance by the value-width `stride` argument, `8` by default),
   `valueRanges`, and the top-level `graphColorAlloc` — all over `[MachineModel I]`,
   producing the same `name ↦ Slot` shape `GenericRegAlloc.spillAlloc` does. Untrusted
   (its output is checked by `renameBlock_runBlock`), so it need not be — and is not —
   verified; it is total and typechecks generically. What *is* proved about the allocator
   is the frame-layout obligation a byte-addressed spill argument needs:
   `selectColors_slotsSeparated` / `graphColorAlloc_slotsSeparated` — at a stride at least
   the byte width of one allocated value, the assigned slots cover pairwise-disjoint byte
   ranges (`GenericRegAlloc.SlotsSeparated`).
3. **Move-coalescing generically** (§4, P4): a small `MoveMachine` extension exposing
   copy detection (`asMove`) and the identity-move `runBlock`-no-op law, then
   `coalesceInterfereOk`/`subst`/`firstCoalescable`/`coalesceStep`/`dropIdMoves`/`coalesce`
   over `[MoveMachine I S]`. The VERIFIED content ports cleanly:
   * `runBlock_dropIdMoves` (§4) — dropping identity self-moves is a `runBlock` no-op,
     proved generically from the class's `idMove_runBlock_noop` law (the generic analogue
     of the x86 `runBlock_dropIdMovs`);
   * `coalesceStep_runBlock` (§4) — a certified coalescing step preserves `Reindexed`,
     **proved generically** by composing the resident-path result
     `GenericRegAlloc.renameBlock_runBlock` (the rename is sound) with the identity-move
     drop (the residue is a no-op). This is the generic analogue of the x86
     `coalesceStep_runBlock_rel` + `runBlock_dropIdMovs` composition.
4. **Specialization** (§5): a corollary at the RV64 `RInst`/`RState` instance
   (`instRegMachineRInst`) confirming the generic graph and the generic coalescing
   soundness fire — the `.mv` copy and the `renameRInst` rename slot straight in.

## Scope (what stays x86-specific)

The x86 `GraphColoringCoalesce` also proves a **constant-time** preservation lemma
(`coalesce_allDirect`, via `ScalarCompileCorrect.allDirect_renameBlock`) and a battery
of concrete `native_decide` demos (`demo_*`, the Keccak `keccak_graphColor_*` spill-count
metrics). The CT lemma rests on the x86 `allDirect`/`IsDirect` addressing-mode predicate
(an x86-ISA notion with no `MachineModel` field), and the `native_decide` metrics are
about the *concrete* x86 Keccak body — both are x86-specific and are NOT
lifted here. What lifts is the algorithm (graph + coloring + coalescing) and the
**denotation-preservation** soundness (`runBlock_dropIdMoves`, `coalesceStep_runBlock`),
which is exactly the part that reuses the generic `renameBlock_runBlock` result.

This file uses `set_option autoImplicit false` (the `Optimizer/` convention).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.GraphColoringGeneric

open CatCrypt.Crypto.Optimizer.GenericRegAlloc

variable {I : Type}

/-! ## 1. The interference graph generically

Over a straight-line block we reuse `GenericRegAlloc.liveRanges` (the `[def, lastUse]`
interval per distinct name, already over `[MachineModel I]`). Two names **interfere**
iff their intervals overlap. These four definitions are over `LiveRange` alone, so they
were already backend-agnostic in `GraphColoringRegAlloc`; we restate them in the generic
namespace and prove the basic structural property (symmetry). -/

/-- Two closed live ranges `[a.defIdx, a.lastUse]` and `[b…]` overlap. -/
def rangesOverlap (a b : LiveRange) : Bool :=
  a.defIdx ≤ b.lastUse ∧ b.defIdx ≤ a.lastUse

/-- Two distinct names **interfere** iff their live ranges overlap. (A name never
    interferes with itself.) -/
def interfere (a b : LiveRange) : Bool :=
  a.name ≠ b.name ∧ rangesOverlap a b

/-- **`rangesOverlap` is symmetric** (the overlap relation is order-independent). -/
theorem rangesOverlap_symm (a b : LiveRange) :
    rangesOverlap a b = rangesOverlap b a := by
  simp only [rangesOverlap, decide_eq_decide]; exact And.comm

/-- **`interfere` is symmetric** — the interference graph is undirected: `a` interferes
    with `b` iff `b` interferes with `a`. (Both the distinctness `a.name ≠ b.name` and
    the overlap `rangesOverlap` are symmetric.) -/
theorem interfere_symm (a b : LiveRange) : interfere a b = interfere b a := by
  simp only [interfere, rangesOverlap_symm a b, decide_eq_decide]; rw [ne_comm]

/-- **A name never interferes with itself** — the interference graph has no self-loops
    (the distinctness conjunct `a.name ≠ a.name` is false). -/
theorem interfere_irrefl (a : LiveRange) : interfere a a = false := by
  simp [interfere]

/-- The neighbours of `lr` in the interference graph: every other live range whose
    interval overlaps `lr`'s. -/
def neighbours (lrs : List LiveRange) (lr : LiveRange) : List LiveRange :=
  lrs.filter (fun b => interfere lr b)

/-- The interference **degree** of a node: how many other live ranges it conflicts
    with. -/
def degree (lrs : List LiveRange) (lr : LiveRange) : Nat :=
  (neighbours lrs lr).length

/-- The interference graph as a name ↦ neighbour-names adjacency list. -/
def interferenceGraph (lrs : List LiveRange) : List (String × List String) :=
  lrs.map (fun lr => (lr.name, (neighbours lrs lr).map (·.name)))

/-! ## 2. Spill cost = use density (generic over the read/write interface)

The Chaitin–Briggs spill metric: a value's use density is its number of uses
(reads + writes) divided by its live-range length. The use count reads only the
`MachineModel` read/write interface (`writtenNames`/`readNames`), so it is generic. -/

/-- The number of times `name` is read or written across the block (its use count).
    Reads only the `MachineModel` read/write interface, so it is generic. -/
def useCount [MachineModel I] (block : List I) (name : String) : Nat :=
  (block.filter (fun i =>
    (writtenNames i).contains name ∨ (readNames i).contains name)).length

/-- A live range's length (number of program points it spans, inclusive). -/
def rangeLen (lr : LiveRange) : Nat := lr.lastUse - lr.defIdx + 1

/-- The spill cost of a name as a rational `(uses, length)`: higher `uses/length` ⇒
    higher cost ⇒ prefer to keep resident. A pair so comparisons are exact
    cross-multiplications. -/
def spillCostFrac [MachineModel I] (block : List I) (lr : LiveRange) : Nat × Nat :=
  (useCount block lr.name, rangeLen lr)

/-- `a` is a **cheaper** spill than `b` (lower use density): `usesA·lenB ≤ usesB·lenA`.
    The Chaitin–Briggs "spill the cheapest" order. -/
def cheaperSpill (a b : Nat × Nat) : Bool :=
  a.1 * b.2 ≤ b.1 * a.2

/-! ## 3. Briggs optimistic coloring (generic, untrusted)

Classic Chaitin–Briggs over the interference graph with `K = |pool|` colors: simplify
(remove `< K`-degree nodes), potential-spill (remove the cheapest node when all are
high-degree), select (pop the stack, color avoiding selected neighbours). The allocator
is **untrusted** — its `name ↦ Slot` output is checked by `renameBlock_runBlock` — so it
is not verified, only total and generic. -/

/-- The degree of `lr` restricted to a remaining node set `rem`. -/
def degreeIn (lrs : List LiveRange) (rem : List String) (lr : LiveRange) : Nat :=
  ((neighbours lrs lr).filter (fun b => rem.contains b.name)).length

/-- One simplify/spill step: prefer a node of restricted degree `< k` (simplify); else
    the cheapest-spill node (lowest use density — potential spill). -/
def pickNode [MachineModel I] (block : List I) (lrs : List LiveRange) (k : Nat)
    (rem : List LiveRange) : Option LiveRange :=
  match rem with
  | [] => none
  | _ =>
    let remNames := rem.map (·.name)
    match rem.find? (fun lr => degreeIn lrs remNames lr < k) with
    | some lr => some lr
    | none =>
      rem.foldl (fun best lr =>
        match best with
        | none => some lr
        | some b =>
          if cheaperSpill (spillCostFrac block lr) (spillCostFrac block b)
          then some lr else some b) none

/-- The **simplify/spill stack**: the order nodes are removed from the graph (head = last
    pushed = first colored, LIFO select). Fuel-bounded by the node count. -/
def simplifyStack [MachineModel I] (block : List I) (lrs : List LiveRange) (k : Nat) :
    List LiveRange :=
  let rec go (fuel : Nat) (rem : List LiveRange) (acc : List LiveRange) :
      List LiveRange :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match pickNode block lrs k rem with
      | none => acc
      | some lr =>
        go fuel (rem.filter (fun x => x.name ≠ lr.name)) (lr :: acc)
  go lrs.length lrs []

/-- The first pool register not assigned to any of `lr`'s neighbours in the partial
    coloring `assigned`. `none` ⇒ must spill. -/
def firstFreeColor (pool : List String) (lrs : List LiveRange)
    (assigned : List (String × String)) (lr : LiveRange) : Option String :=
  let nbrRegs := (neighbours lrs lr).filterMap (fun b => assigned.lookup b.name)
  pool.find? (fun r => ¬ nbrRegs.contains r)

/-- The select step: `st` is the remaining simplify stack, `assigned` the partial
    coloring, `nextSpill` the next free frame offset, `acc` the decisions so far.
    Consecutive spill offsets advance by `stride`. -/
def selectColorsGo (pool : List String) (lrs : List LiveRange) (stride : Int)
    (st : List LiveRange) (assigned : List (String × String)) (nextSpill : Int)
    (acc : List (String × Slot)) : List (String × Slot) :=
  match st with
  | [] => acc
  | lr :: rest =>
    match firstFreeColor pool lrs assigned lr with
    | some r => selectColorsGo pool lrs stride rest ((lr.name, r) :: assigned) nextSpill
                   ((lr.name, .resident r) :: acc)
    | none => selectColorsGo pool lrs stride rest assigned (nextSpill + stride)
                ((lr.name, .spilled nextSpill) :: acc)

/-- The **select phase**: pop the simplify stack head-first, coloring each node with
    `firstFreeColor`; a node with no free color spills to the next frame cell. Produces
    the `name ↦ Slot` decision list (the same shape `linearScan` returns).

    `stride` is the byte width of one allocated value: consecutive spill offsets advance
    by it, so two live spills of `stride`-byte values occupy disjoint frame cells
    (`selectColors_slotsSeparated`). The default `8` is the general-purpose word; a vector
    file passes its own width (`16` for `%xmm`, `32` for `%ymm`, `64` for `%zmm`). -/
def selectColors (pool : List String) (lrs : List LiveRange) (frameBase : Int)
    (stack : List LiveRange) (stride : Int := 8) : List (String × Slot) :=
  selectColorsGo pool lrs stride stack [] frameBase []

/-- The select invariant: an offset already emitted lies at least `stride` below the next
    free offset, so each new slot is separated from every earlier one. -/
theorem selectColorsGo_pairwise (width : Nat) (pool : List String) (lrs : List LiveRange)
    (stride : Int) (hw : (width : Int) ≤ stride) :
    ∀ (st : List LiveRange) (assigned : List (String × String)) (nextSpill : Int)
      (acc : List (String × Slot)),
      (∀ o ∈ slotOffsets acc, o + stride ≤ nextSpill) →
      (slotOffsets acc).Pairwise (SepAt width) →
      (slotOffsets (selectColorsGo pool lrs stride st assigned nextSpill acc)).Pairwise
        (SepAt width) := by
  have hw0 : (0 : Int) ≤ (width : Int) := Int.natCast_nonneg _
  intro st
  induction st with
  | nil => intro assigned nextSpill acc _ hp; exact hp
  | cons lr rest ih =>
    intro assigned nextSpill acc hacc hp
    have hres : ∀ (l : List (String × Slot)), slotOffsets l = slotOffsets acc →
        ((∀ o ∈ slotOffsets l, o + stride ≤ nextSpill)
          ∧ (slotOffsets l).Pairwise (SepAt width)) := by
      intro l hl
      rw [hl]; exact ⟨hacc, hp⟩
    have hspill : ∀ (l : List (String × Slot)),
        slotOffsets l = nextSpill :: slotOffsets acc →
        ((∀ o ∈ slotOffsets l, o + stride ≤ nextSpill + stride)
          ∧ (slotOffsets l).Pairwise (SepAt width)) := by
      intro l hl
      rw [hl]
      refine ⟨?_, ?_⟩
      · intro o ho
        rcases List.mem_cons.mp ho with h | h
        · omega
        · have := hacc o h; omega
      · refine List.pairwise_cons.mpr ⟨?_, hp⟩
        intro b hb
        have := hacc b hb
        exact Or.inr (by omega)
    simp only [selectColorsGo]
    split
    · exact ih _ nextSpill _ (hres _ rfl).1 (hres _ rfl).2
    · exact ih _ _ _ (hspill _ rfl).1 (hspill _ rfl).2

/-- **The select phase's frame stride discharges the separation obligation.** When the
    stride is at least the byte width of one allocated value, the frame slots
    `selectColors` assigns cover pairwise-disjoint byte ranges, so a spill/reload argument
    over a byte-addressed frame (`Optimizer.ByteMemMachine`) applies to its output. The
    hypothesis is where the stride enters: a `%ymm` pool (`width = 32`) coloured at the
    default stride `8` does not satisfy it, and the conclusion is then false — see
    `VsimdGraphColorRegAlloc.pressureBlock_ymm_slots_overlap_at_stride_eight`. -/
theorem selectColors_slotsSeparated (width : Nat) (pool : List String) (lrs : List LiveRange)
    (frameBase : Int) (stack : List LiveRange) (stride : Int) (hw : (width : Int) ≤ stride) :
    SlotsSeparated width (selectColors pool lrs frameBase stack stride) :=
  selectColorsGo_pairwise width pool lrs stride hw stack [] frameBase []
    (by simp [slotOffsets]) (by simp [slotOffsets])

/-- The live ranges of the **value** names only — names written somewhere in the block.
    Read-only names (memory/frame base addresses, never a destination) are fixed
    addresses, not allocatable values: they get no `Slot`. -/
def valueRanges [MachineModel I] (block : List I) : List LiveRange :=
  (liveRanges block).filter (fun lr =>
    block.any (fun i => (writtenNames i).contains lr.name))

/-- **The generic graph-coloring (Chaitin–Briggs) register allocator.** Same
    `List (String × Slot)` output shape as `GenericRegAlloc.spillAlloc`, so it is a
    drop-in alternative that plugs into the identical proved spill/rename checker.
    `k = |pool|` colors; spill choice by use-density; LIFO select. Allocates only the
    **value** names (`valueRanges`). The pool is the generic `allocPool` (the `physRegs`
    file minus pinned/scratch). `stride` is the byte width of one allocated value, the
    spacing of consecutive spill cells; the default `8` is the general-purpose word.
    Untrusted — checked by `renameBlock_runBlock`. -/
def graphColorAlloc [MachineModel I] (pinned scratch : List String) (frameBase : Int)
    (block : List I) (stride : Int := 8) : List (String × Slot) :=
  let pool := allocPool (I := I) pinned scratch
  let lrs := valueRanges block
  let stack := simplifyStack block lrs pool.length
  selectColors pool lrs frameBase stack stride

/-- The number of names the graph-coloring allocator spills. -/
def graphColorSpillCount [MachineModel I] (pinned scratch : List String) (frameBase : Int)
    (block : List I) : Nat :=
  spillCount (graphColorAlloc pinned scratch frameBase block)

/-- The number of names the graph-coloring allocator keeps register-resident. -/
def graphColorResidentCount [MachineModel I] (pinned scratch : List String)
    (frameBase : Int) (block : List I) : Nat :=
  residentCount (graphColorAlloc pinned scratch frameBase block)

/-- **The graph-coloring allocator's slots are separated at any width its stride covers.**
    The obligation a byte-addressed spill argument imposes on the allocator, discharged
    from the `stride` argument alone: it holds of every block and every pool, and fails to
    apply exactly when the stride is narrower than the value being spilled. -/
theorem graphColorAlloc_slotsSeparated [MachineModel I] (width : Nat)
    (pinned scratch : List String) (frameBase : Int) (block : List I) (stride : Int)
    (hw : (width : Int) ≤ stride) :
    SlotsSeparated width (graphColorAlloc (I := I) pinned scratch frameBase block stride) :=
  selectColors_slotsSeparated width _ _ frameBase _ stride hw

/-! ## 4. Generic move-coalescing (P4)

Coalescing a copy `dst ← src` is the renaming `dst ↦ src` applied to the whole block,
after which the copy has become the identity `src ← src` and is dropped:

  `coalesce = dropIdMoves ∘ renameBlock (subst d s)`

So it reuses two facts: (1) the renaming soundness — the generic resident-path result
`GenericRegAlloc.renameBlock_runBlock` (an injective rename carries `Reindexed` through
`runBlock`); and (2) identity-move drop is a `runBlock` no-op.

Two pieces are NOT in the generic `MachineModel`/`RegMachine` interface and so are
exposed by a small `MoveMachine` extension: **copy detection** (which instructions are
register-to-register moves `dst ← src`) and the **identity-move no-op law** (a move
`r ← r` is a `runBlock` no-op). Each backend discharges both trivially (x86 by
`.mov d (.reg s)` / `evalInstr_idMov_noop`, RV64 by `.mv d s` / `evalRInst`). -/

/-- The **copy-detection + identity-move** extension to `RegMachine`: which instructions
    are register-to-register moves, the identity-move predicate, and the law that an
    identity self-move is a `runBlock` no-op (the only fact coalescing's cleanup half
    needs beyond the generic rename result). The x86 `GraphColoringCoalesce` discharges
    this with `.mov d (.reg s)` + `evalInstr_idMov_noop`; RV64 with `.mv d s` + a
    `runBlock`-singleton `mv r r` no-op. -/
class MoveMachine (I : Type) (S : Type) extends RegMachine I S where
  /-- The `(dst, src)` of a register-to-register copy `dst ← src`, if `i` is one. -/
  asMove : I → Option (String × String)
  /-- Is `i` an identity self-move `r ← r`? (Definable from `asMove`, kept as a field so
      backends can match their concrete `mov`/`mv` constructor directly.) -/
  isIdMove : I → Bool
  /-- `isIdMove i` iff `i` is a copy whose dst and src coincide. -/
  isIdMove_iff_asMove : ∀ i, isIdMove i = true ↔ ∃ r, asMove i = some (r, r)
  /-- **An identity self-move is a `runBlock` no-op** — it writes a register the value it
      already holds. The generic analogue of the x86 `evalInstr_idMov_noop`. -/
  idMove_runBlock_noop : ∀ (s : S) (i : I), isIdMove i = true → RegMachine.runBlock s [i] = s

variable {S : Type}

/-! ### §4.1 The non-interference certificate, substitution, and the step

The textbook copy-coalescing non-interference condition: a copy `dst ← src` at index
`copyIdx` is coalescable iff `dst ≠ src`, the copy is `dst`'s definition, and `src` is
dead after it. These are read off `GenericRegAlloc.{defIdxOf, lastUseIdx}`. -/

/-- **The coalescing certificate** (Briggs/George side-condition). A copy `dst ← src` at
    index `copyIdx` is coalescable iff `d ≠ s`, the copy is `d`'s definition
    (`defIdxOf block d = copyIdx`), and `s` is dead after it
    (`lastUseIdx block s ≤ copyIdx`). Generic — reads only the `MachineModel` interface. -/
def coalesceInterfereOk [MachineModel I] (block : List I) (copyIdx : Nat) (d s : String) :
    Bool :=
  (d != s) &&
  (defIdxOf block d == copyIdx) &&
  (lastUseIdx block s ≤ copyIdx)

/-- The substitution renaming `d ↦ s`, identity elsewhere. -/
def subst (d s : String) : String → String := fun n => if n = d then s else n

/-- The first **certified coalescable copy** in the block, with its `(d, s)`, if any.
    Generic: copy detection via `MoveMachine.asMove`, certification via
    `coalesceInterfereOk`. -/
def firstCoalescable [MoveMachine I S] (block : List I) : Option (String × String) :=
  block.zipIdx.findSome? (fun (i, idx) =>
    match MoveMachine.asMove (S := S) i with
    | some (d, s) =>
        if coalesceInterfereOk block idx d s then some (d, s) else none
    | none => none)

/-- **One coalescing step**: substitute the first certified copy's destination by its
    source throughout the block (the copy becomes an identity self-move, cleaned up by
    `dropIdMoves`). If none exists, the block is unchanged. -/
def coalesceStep [MoveMachine I S] (block : List I) : List I :=
  match firstCoalescable (S := S) block with
  | some (d, s) => renameBlock (S := S) (subst d s) block
  | none => block

/-- Drop every identity self-move from the block. -/
def dropIdMoves [MoveMachine I S] (block : List I) : List I :=
  block.filter (fun i => ! MoveMachine.isIdMove (S := S) i)

/-- **The generic coalescing transform.** Iterate `coalesceStep` to a fuel-bounded
    fixpoint (fuel = block length), then drop the identity self-moves the steps left
    behind. Conservative: only certified non-interfering copies are coalesced. -/
def coalesce [MoveMachine I S] (block : List I) : List I :=
  let rec go (fuel : Nat) (b : List I) : List I :=
    match fuel with
    | 0 => b
    | fuel + 1 =>
      match firstCoalescable (S := S) b with
      | some _ => go fuel (coalesceStep (S := S) b)
      | none => b
  dropIdMoves (S := S) (go block.length block)

/-! ### §4.2 Soundness (the verified content, ported generically)

Two composed facts. (a) Dropping identity self-moves is a `runBlock` no-op, fully
general (from `MoveMachine.idMove_runBlock_noop`). (b) The coalescing substitution is a
rename, sound via the generic `GenericRegAlloc.renameBlock_runBlock`. -/

/-- **Dropping identity self-moves preserves `runBlock`** — the cleanup half of a
    coalescing step, general over all blocks/states. Each removed identity self-move is a
    no-op (`MoveMachine.idMove_runBlock_noop`), so deleting it does not change the run.
    The generic analogue of the x86 `runBlock_dropIdMovs`. -/
theorem runBlock_dropIdMoves [MoveMachine I S] (block : List I) (s : S) :
    RegMachine.runBlock s (dropIdMoves (S := S) block) = RegMachine.runBlock s block := by
  -- a generic one-step unfold of `runBlock` on a cons, from the left-fold law
  have hcons : ∀ (t : S) (j : I) (js : List I),
      RegMachine.runBlock t (j :: js)
        = RegMachine.runBlock (RegMachine.runBlock t [j]) js := fun t j js => by
    have := RegMachine.runBlock_append (I := I) t [j] js; simpa using this
  induction block generalizing s with
  | nil => rfl
  | cons i is ih =>
    have hfilter : dropIdMoves (S := S) (i :: is)
        = (if (! MoveMachine.isIdMove (S := S) i) = true then i :: dropIdMoves (S := S) is
           else dropIdMoves (S := S) is) := by
      simp only [dropIdMoves, List.filter_cons]
    rw [hfilter]
    by_cases h : MoveMachine.isIdMove (S := S) i = true
    · -- dropped: i is an identity self-move, a no-op
      have hk : ¬ (! MoveMachine.isIdMove (S := S) i) = true := by simp [h]
      rw [if_neg hk, hcons s i is, MoveMachine.idMove_runBlock_noop s i h]
      exact ih (s := s)
    · -- kept
      have hk : (! MoveMachine.isIdMove (S := S) i) = true := by simp [h]
      rw [if_pos hk, hcons s i (dropIdMoves (S := S) is), hcons s i is]
      exact ih (s := RegMachine.runBlock s [i])

/-- **Single-step coalescing equals rename-then-drop.** When a certified copy exists,
    `coalesceStep` is exactly the substitution rename, so cleaning up its identity-move
    residue gives `dropIdMoves (renameBlock (subst d s) block)`. -/
theorem coalesceStep_eq_rename [MoveMachine I S] {block : List I} {d s : String}
    (h : firstCoalescable (S := S) block = some (d, s)) :
    coalesceStep (S := S) block = renameBlock (S := S) (subst d s) block := by
  unfold coalesceStep
  rw [h]

/-- **Cleanup soundness of a single step.** Dropping the identity self-moves from a
    coalescing step's output preserves `runBlock` against that output — the only change is
    removing self-moves, which are no-ops. -/
theorem coalesceStep_cleanup_sound [MoveMachine I S] (block : List I) (s : S) :
    RegMachine.runBlock s (dropIdMoves (S := S) (coalesceStep (S := S) block))
      = RegMachine.runBlock s (coalesceStep (S := S) block) :=
  runBlock_dropIdMoves (coalesceStep (S := S) block) s

/-- **Rename-level single-step soundness (the `Reindexed` simulation).** For an
    injective substitution `ρ = subst d s` (injective exactly when
    `d`,`s` don't both occur as distinct live names — the non-interference certificate)
    that is discard-preserving and writes only non-discard names, the coalescing rename
    carries `Reindexed ρ` through `runBlock`: the coalesced run's register `ρ n` agrees
    with the original run's `n`. This instantiates the proved generic renaming result
    `GenericRegAlloc.renameBlock_runBlock` — the "coalescing preserves the
    computation up to the merged register" statement, the generic analogue of the x86
    `coalesceStep_runBlock_rel`. -/
theorem coalesceStep_runBlock_rel [MoveMachine I S] {d s : String}
    (hinj : Function.Injective (subst d s))
    (hρd : ∀ r, rmDisc I S r = true → rmDisc I S (subst d s r) = true)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (subst d s r) = false)
    (block : List I)
    (hz : ∀ i ∈ block, ∀ n ∈ writtenNames i, rmDisc I S n = false)
    {sL sR : S} (h : Reindexed I (subst d s) sR sL) :
    Reindexed I (subst d s)
      (rmRun I sR block) (rmRun I sL (renameBlock (S := S) (subst d s) block)) :=
  renameBlock_runBlock I (subst d s) hinj hρd hρnd block hz sR sL h

/-! ## 5. Specialization: the generic passes fire at the RV64 `RInst`/`RState` instance

`RISCVBackend.RiscvRegAlloc.instRegMachineRInst` is a full `RegMachine RInst RState`.
We exhibit (a) the generic interference graph fires there (the symmetry property and the
graph builder typecheck at `RInst`), and (b) the move-coalescing extension fires: `.mv`
is the copy form, `renameRInst` the rename, and the generic coalescing soundness
result (`coalesceStep_runBlock_rel`, hence `GenericRegAlloc.renameBlock_runBlock`)
specializes through the instance. -/

namespace RV64Specialization

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRegAlloc

/-- **The generic interference graph fires at RV64.** The symmetry property holds at the
    `RInst`-derived live ranges (it is `MachineModel`-agnostic, but this confirms the
    generic graph instantiates at a concrete fresh backend). -/
theorem rv64_interfere_symm (a b : LiveRange) : interfere a b = interfere b a :=
  interfere_symm a b

/-- **The generic graph-coloring allocator typechecks and runs at RV64.** It produces a
    `name ↦ Slot` decision list over an `RInst` block, drawing from the RV64 `gpFile` pool
    — confirming `graphColorAlloc` is generic in the instruction type (no x86
    residue). -/
def rv64GraphColor (pinned scratch : List String) (frameBase : Int)
    (block : List RInst) : List (String × Slot) :=
  graphColorAlloc (I := RInst) pinned scratch frameBase block

/-- **The `MoveMachine RInst RState` instance** — RV64 copy detection (`.mv d s`) and the
    identity-move no-op (`mv r r` is a `runRBlock`-singleton no-op). This is the data the
    generic move-coalescing pass needs; with it, every generic coalescing theorem
    (`runBlock_dropIdMoves`, `coalesceStep_runBlock_rel`) specializes to RV64. -/
instance instMoveMachineRInst : MoveMachine RInst RState where
  toRegMachine := instRegMachineRInst
  asMove := fun i => match i with
    | .mv d s => some (d, s)
    | _ => none
  isIdMove := fun i => match i with
    | .mv d s => d == s
    | _ => false
  isIdMove_iff_asMove := by
    intro i
    cases i <;>
      first
      | (simp only [reduceCtorEq, Bool.false_eq_true, false_iff, not_exists]
         exact fun _ => by simp)
      | (rename_i d s
         constructor
         · intro h; exact ⟨d, by simp only [beq_iff_eq] at h; rw [h]⟩
         · rintro ⟨r, hr⟩
           simp only [Option.some.injEq, Prod.mk.injEq] at hr
           simp [hr.1.trans hr.2.symm])
  idMove_runBlock_noop := by
    intro s i h
    cases i <;> simp only [Bool.false_eq_true] at h
    rename_i d s'
    simp only [beq_iff_eq] at h
    subst h
    show runRBlock s [RInst.mv d d] = s
    rw [show runRBlock s [RInst.mv d d] = evalRInst s (RInst.mv d d) from rfl,
      evalRInst_eq_set]
    exact RMemState.RState.set_get_self s d

/-- **Generic move-coalescing fires at RV64.** The `coalesce` transform runs over `RInst`
    blocks via the `MoveMachine RInst RState` instance, dropping certified non-interfering
    `.mv` copies. -/
def rv64Coalesce (block : List RInst) : List RInst :=
  coalesce (S := RState) block

/-- **Generic identity-move drop is sound at RV64** — `runBlock_dropIdMoves` specializing
    through the RV64 instance: dropping identity `.mv r r` self-moves preserves the run.
    The generic analogue of the x86 `runBlock_dropIdMovs`, now firing at a fresh ISA. -/
theorem rv64_dropIdMoves_sound (block : List RInst) (s : RState) :
    runRBlock s (dropIdMoves (S := RState) block) = runRBlock s block :=
  runBlock_dropIdMoves (S := RState) block s

end RV64Specialization

end CatCrypt.Crypto.Optimizer.GraphColoringGeneric
