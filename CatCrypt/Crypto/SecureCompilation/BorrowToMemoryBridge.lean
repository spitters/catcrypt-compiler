/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
import CatCrypt.Crypto.Jasmin.PointerBorrow
import CatCrypt.Crypto.Jasmin.MemoryModel
import CatCrypt.Crypto.Jasmin.LowCTToJasmin
import CatCrypt.Crypto.Jasmin.JasminSem
import CatCrypt.Crypto.Jasmin.Hoare

set_option autoImplicit false

/-!
# Compositional bridge: borrow check ↔ bedrock-style memory model

This file states, and partially proves, the compositional theorem that ties three
already-proved layers together:

1. `LowCTBorrowCheck.lean` — high-level `borrowOk` / `destsOf` / `seqFrame`.
2. `PointerBorrow.lean`    — middle bridge: `isPointerSafe`, `MemBasesIn`,
                             `disjointObligations_distinct`.
3. `MemoryModel.lean`      — low-level `Mem`, `Disjoint`, `array64`,
                             `array64_storeByte_disjoint`.

plus the Hoare skeleton in `Hoare.lean`, which supplies `JasminMemState`,
`StepRel`, `RespectsFootprint`, and `frame_array64`.

## Bridge theorem (informal)

> If a `LowCT` `c` satisfies `borrowOk c` (no aliasing at every call site), then
> any execution through a `RespectsFootprint`-respecting step relation preserves
> every `array64` invariant on a region disjoint from the body's write footprint.
> (Pointer safety of the lowering — `isPointerSafe` on the enclosing `FunDecl` —
> is the intended source-side side condition, but the formal theorem does not
> take it as a hypothesis; it consumes the footprint disjointness directly.)

`disjointObligations_distinct` guarantees the obligations the caller sees are
between syntactically distinct names (no `Disjoint A A` self-pairs). The
variable-level `seqFrame` shows the register state of every non-destination input
is preserved. Composing these with `frame_array64` from `Hoare.lean` yields the
memory invariant.

## What is proved, and what is assumed

- `borrowOk_implies_memory_invariants_preserved` elaborates against the existing
  types and its framing-level statement is proved, as are the structural cases
  (`RSkip`, `RSeq` of two preserved bodies).
- Proved sub-lemmas: `borrowOk_seqFrame_corollary` (variable-level corollary of
  `seqFrame`), `pointerSafe_disjointObligations_irreflexive` (wrap of
  `disjointObligations_distinct`), and `array64_preserved_by_disjoint_step` (the
  `array64` frame closure against `RespectsFootprint`).
- The operational arms (`RCall`, `RIfNz`, `RWhileNz`, `RCloneCall`, `RLimbStore`)
  are in **hypothesis-discharge form**: each takes its structural footprint shape
  (union for `RIfNz`, fixed point for `RWhileNz`, inner-call equivalence for
  `RCloneCall`) as a hypothesis and discharges the disjointness from it. The file
  contains no `sorry`, but it does not derive those hypotheses either.
- `bridge_smoke_RCall_fp_add` instantiates the theorem on a single
  `RCall "fp_add" out [x, y]` program with `borrowOk = true`, exercising the
  statement shape; its operational premise is taken as a hypothesis.

## Known gaps

- `jasminSem` has no `Mem` extension, so there is no operational glue linking
  `RustExec` / `jasminSem` to a concrete `step`. `StepSimulatesJasmin` is a
  placeholder: its body concludes `True`, so it constrains nothing. A constructive
  simulation witness must replace it before the operational arms carry content.
- `WriteFootprint` is an opaque `List InstrR → AddrSet` parameter. A concrete
  footprint function (for example `bignumStaticFootprint`) is what would let the
  per-`InstrR` arms unfold — in particular the `STORE64` byte range
  `[loc.base + 8·idx, loc.base + 8·idx + 8)`, which `footprint_RLimbStore_disjoint`
  currently only restates rather than derives.
- `BignumHoare`'s `Pload` / `Lmem` per-instruction frame proofs
  (`MemoryModel.Mem.loadByte_storeByte_other`) are not yet composed with
  `array64_preserved_by_disjoint_step` to give a body-level frame.
- `BorrowToMemoryBridgeRustState.lean` carries the follow-up that connects this
  bridge to the strengthened `RustStateInterp`, so that the memory frame becomes
  the rightmost arrow of the `RustExec → jasminSem → step` simulation chain.
-/

namespace CatCrypt.Crypto.SecureCompilation.BorrowToMemoryBridge

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.PointerBorrow
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.SemBridge
open CatCrypt.Crypto.Jasmin.Hoare

/-! ## §1. Tracked memory regions

A "tracked region" is a named buffer with a known size and base
address; the caller's WP-precondition asserts an `array64` on each
such region. The bridge theorem then concludes the same `array64`s
hold after the body runs.

The shape mirrors `disjointObligations` in `PointerBorrow.lean`:
each region corresponds to one parameter name. -/

/-- A tracked memory region: name, base address, and word count. -/
structure TrackedRegion where
  name  : String
  base  : UInt64
  words : Nat
  /-- Concrete contents at this region (caller-known). -/
  vals  : List UInt64
  /-- The contents have the right length. -/
  hLen  : vals.length = words

instance : Inhabited TrackedRegion where
  default :=
    { name := "", base := 0, words := 0, vals := [], hLen := rfl }

/-- A list of tracked regions has the disjoint-obligations property
    iff every distinct pair of bases gives disjoint footprints. -/
def TrackedRegions.PairwiseDisjoint (rs : List TrackedRegion) : Prop :=
  ∀ r1 ∈ rs, ∀ r2 ∈ rs, r1.name ≠ r2.name →
    MemoryModel.Disjoint (array64Footprint r1.base r1.words)
                          (array64Footprint r2.base r2.words)

/-- Initial-state predicate: every tracked region is laid out as
    its `array64` in `mem`. -/
def TrackedRegions.InitArrays (rs : List TrackedRegion) (mem : Mem) : Prop :=
  ∀ r ∈ rs, array64 r.base r.vals mem

/-! ## §2. Sub-lemma: borrowOk gives variable-level frame -/

/-- Corollary of `seqFrame`: a borrow-checked program preserves the
    lookup of any variable not in its write set.

    This is just `seqFrame` repackaged with the explicit `borrowOk`
    hypothesis in place of `loc.locVar ∉ destsOf c`. The two are
    independent; the lemma documents the intended composition. -/
theorem borrowOk_seqFrame_corollary
    (N : Nat) (leafSpec : LeafSpec)
    (c : LowCT) (rs rs' : RustState) (loc : Located)
    (_hBok  : borrowOk c = true)
    (hExec  : RustExec N leafSpec c rs rs')
    (hNotIn : loc.locVar ∉ destsOf c) :
    locatedLookup rs' loc = locatedLookup rs loc :=
  seqFrame N leafSpec c rs rs' loc hExec hNotIn

/-! ## §3. Sub-lemma: pointer-safe ⇒ obligations are irreflexive -/

/-- Wrap of `disjointObligations_distinct`. Promotes the syntactic
    statement to a "for every produced obligation" frame. -/
theorem pointerSafe_disjointObligations_irreflexive (fd : FunDecl)
    (_h : isPointerSafe fd = true)
    (p q : String) (hpq : (p, q) ∈ disjointObligations fd) :
    p ≠ q :=
  disjointObligations_distinct fd p q hpq

/-! ## §4. Sub-lemma: a step that respects a footprint preserves
    `array64` on a disjoint region.

    This is what `Hoare.frame_array64` already proves; we just
    specialise the binders to give the bridge a single named entry
    point. -/

/-- One-region preservation: if `step` respects `footprint`, and the
    region's footprint is disjoint, then the `array64` survives. -/
theorem array64_preserved_by_disjoint_step
    (step : StepRel) (footprint : WriteFootprint)
    (h_resp : RespectsFootprint step footprint)
    (body : List InstrR) (base : UInt64) (xs : List UInt64)
    (h_disj : MemoryModel.Disjoint (footprint body) (array64Footprint base xs.length))
    (s s' : JasminMemState)
    (h_arr  : array64 base xs s.mem)
    (h_step : step body s s') :
    array64 base xs s'.mem :=
  frame_array64 (step := step) (footprint := footprint) h_resp body base xs
    h_disj s s' h_arr h_step

/-! ## §5. The compositional bridge theorem

The full statement below combines:
- `borrowOk c`                           (variable-level no-aliasing)
- `isPointerSafe (toJasminCmd c)`        (memory bases are parameters)
- a step relation `step` that `RespectsFootprint footprint`,
- pairwise-disjointness of the tracked regions,
- and an `array64` precondition on every region.

It concludes that every region's `array64` survives the step.

Importantly, the **operational** glue (linking `RustExec` /
`jasminSem` to `step`) is currently wrapped in a per-arm hypothesis
`StepSimulatesJasmin` because the operational semantics that
ties `Mem` into `jasminSem` is future work. Once the operational
`Mem`-extension of `jasminSem` lands, that hypothesis discharges
automatically, and the per-arm cases specialise without changing
the statement. -/

/-- A step relation `simulates` `jasminSem` at a given fuel `N` if every
    `RustExec` derivation can be lifted to a `step` derivation on
    the corresponding `JasminMemState`. The lift is the operational
    `Mem`-extension of `jasminSem`. For the structural cases
    (skip / seq) the simulation is purely propagation, hence trivially
    provable below. -/
def StepSimulatesJasmin
    (step : StepRel) (leafSpec : LeafSpec) : Prop :=
  ∀ (N : Nat) (c : LowCT) (rs rs' : RustState) (mem mem' : Mem),
    RustExec N leafSpec c rs rs' →
    -- Hypothesis: the chosen `step` lifts the `RustExec`.
    -- For now this is the bridge's interface; the witness
    -- comes from the operational `Mem`-extension of `jasminSem`.
    step (toJasminCmd c)
         { regs := rs,  mem := mem }
         { regs := rs', mem := mem' } →
    True   -- placeholder discharger; a constructive simulation witness
           -- from the operational `Mem`-extension of `jasminSem` will
           -- replace this.

/-- Skip is trivially simulated. -/
theorem step_simulates_RSkip
    (step : StepRel) (_leafSpec : LeafSpec) :
    ∀ (rs : RustState) (mem : Mem),
      step (toJasminCmd .RSkip)
           { regs := rs, mem := mem }
           { regs := rs, mem := mem } →
      True := by
  intros; trivial

/-- **Bridge theorem (compositional form).** Given:

    * a `borrowOk` source program,
    * its lowered Jasmin program is `isPointerSafe`,
    * a step relation that respects the body's write footprint,
    * a list of pairwise-disjoint tracked regions, every footprint of
      which is disjoint from the body's write footprint,
    * an `array64` precondition on every region,

    the same `array64`s hold after a step.

    Status of the per-arm decomposition lemmas in §6 below:

    | Case          | Status                                      |
    |---------------|---------------------------------------------|
    | `RSkip`       | Qed (`footprint_RSkip_disjoint`)            |
    | `RSeq`        | Qed (`footprint_RSeq_disjoint`)             |
    | `RScalarSet`  | Qed (`footprint_RScalarSet_disjoint`)       |
    | `RLetZero`    | Qed (`footprint_RLetZero_disjoint`)         |
    | `RLetU64Zero` | Qed (`footprint_RLetU64Zero_disjoint`)      |
    | `RCall`       | Qed (`footprint_RCall_disjoint`, hypothesis-discharge form) |
    | `RLimbStore`  | Qed (`footprint_RLimbStore_disjoint`, identity form) |
    | `RIfNz`       | Qed (`footprint_RIfNz_disjoint`, hypothesis-discharge form) |
    | `RWhileNz`    | Qed (`footprint_RWhileNz_disjoint`, hypothesis-discharge form) |
    | `RCloneCall`  | Qed (`footprint_RCloneCall_disjoint`, hypothesis-discharge form) |

    The main theorem itself is `Qed` for any `step` /
    `footprint` / `regions` triple — the structural decomposition
    lives in the per-arm lemmas in §6. -/
theorem borrowOk_implies_memory_invariants_preserved
    (step : StepRel) (footprint : WriteFootprint)
    (h_resp : RespectsFootprint step footprint)
    (c : LowCT)
    (_h_borrow  : borrowOk c = true)
    (regions : List TrackedRegion)
    (_h_pairwise : TrackedRegions.PairwiseDisjoint regions)
    (h_disjoint_body :
        ∀ r ∈ regions,
          MemoryModel.Disjoint (footprint (toJasminCmd c))
                   (array64Footprint r.base r.words))
    (s s' : JasminMemState)
    (h_init  : TrackedRegions.InitArrays regions s.mem)
    (h_step  : step (toJasminCmd c) s s') :
    TrackedRegions.InitArrays regions s'.mem := by
  -- Structurally we just need: every region's array64 survives the step.
  -- That is exactly `array64_preserved_by_disjoint_step` applied
  -- per-region, given pairwise disjointness with the body footprint
  -- (which `h_disjoint_body` supplies).
  intro r hr
  have h_arr : array64 r.base r.vals s.mem := h_init r hr
  -- Convert h_disjoint_body's `r.words` indexing to `r.vals.length`
  -- via `r.hLen`.
  have h_disj :
      MemoryModel.Disjoint (footprint (toJasminCmd c))
               (array64Footprint r.base r.vals.length) := by
    rw [r.hLen]; exact h_disjoint_body r hr
  exact array64_preserved_by_disjoint_step
          step footprint h_resp (toJasminCmd c) r.base r.vals
          h_disj s s' h_arr h_step

/-! ## §6. Per-LowCT-arm structural decomposition

The framing-level theorem above is fully proved (no `sorry`) because
it consumes the body's `RespectsFootprint` evidence as a hypothesis.
The structural per-arm content — i.e. *how* one establishes that the
specific Jasmin lowering of a `borrowOk` source command actually
respects the footprint that `PointerBorrow.disjointObligations`
synthesises — is the work that decomposes by `LowCT` constructor.

Below we give one statement per constructor; each one is the natural
factor in the per-arm decomposition. The trivial structural cases
(`RSkip`, `RSeq`, `RLetZero`, `RLetU64Zero`, `RScalarSet`) close;
the operational cases (`RIfNz`, `RWhileNz`, `RCall`, `RCloneCall`,
`RLimbStore`) are stubbed because they need the operational
`Mem`-extension of `jasminSem`. -/

/-- The body's footprint of `RSkip` is empty, so it is disjoint from
    every region. -/
theorem footprint_RSkip_disjoint
    (footprint : WriteFootprint)
    (h_empty : ∀ a, ¬ footprint (toJasminCmd .RSkip) a)
    (region : TrackedRegion) :
    MemoryModel.Disjoint (footprint (toJasminCmd .RSkip))
             (array64Footprint region.base region.words) := by
  intro a ⟨ha, _⟩
  exact h_empty a ha

/-- For `RSeq c1 c2`, the body's footprint is the union of the two
    sub-bodies; disjointness lifts componentwise. -/
theorem footprint_RSeq_disjoint
    (footprint : WriteFootprint) (c1 c2 : LowCT)
    (h_union : ∀ a, footprint (toJasminCmd (.RSeq c1 c2)) a ↔
                    footprint (toJasminCmd c1) a ∨
                    footprint (toJasminCmd c2) a)
    (region : TrackedRegion)
    (h1 : MemoryModel.Disjoint (footprint (toJasminCmd c1))
                   (array64Footprint region.base region.words))
    (h2 : MemoryModel.Disjoint (footprint (toJasminCmd c2))
                   (array64Footprint region.base region.words)) :
    MemoryModel.Disjoint (footprint (toJasminCmd (.RSeq c1 c2)))
             (array64Footprint region.base region.words) := by
  intro a ⟨ha, hb⟩
  rcases (h_union a).mp ha with hl | hr
  · exact h1 a ⟨hl, hb⟩
  · exact h2 a ⟨hr, hb⟩

/-- `RScalarSet` writes only to the scalar register file, never memory,
    so any memory footprint is empty.

    This is a structural property of `toJasminCmd .RScalarSet`: it
    emits exactly one `Cassgn` to a `.sword .U64` lvalue (a register),
    not an `Lmem`. -/
theorem footprint_RScalarSet_disjoint
    (footprint : WriteFootprint) (x : String) (v : Nat)
    (h_empty : ∀ a, ¬ footprint (toJasminCmd (.RScalarSet x v)) a)
    (region : TrackedRegion) :
    MemoryModel.Disjoint (footprint (toJasminCmd (.RScalarSet x v)))
             (array64Footprint region.base region.words) := by
  intro a ⟨ha, _⟩
  exact h_empty a ha

/-- `RLetZero x t body` writes a fresh `Parr_init` slot then descends
    into `body`. The `Parr_init` is a register-local zero-init (an
    `.sarr` Lvar, not `Lmem`), so the memory footprint reduces to
    that of `body`. -/
theorem footprint_RLetZero_disjoint
    (footprint : WriteFootprint) (x : String) (t : TowerType) (body : LowCT)
    (h_reduce : ∀ a, footprint (toJasminCmd (.RLetZero x t body)) a ↔
                     footprint (toJasminCmd body) a)
    (region : TrackedRegion)
    (h_body : MemoryModel.Disjoint (footprint (toJasminCmd body))
                       (array64Footprint region.base region.words)) :
    MemoryModel.Disjoint (footprint (toJasminCmd (.RLetZero x t body)))
             (array64Footprint region.base region.words) := by
  intro a ⟨ha, hb⟩
  exact h_body a ⟨(h_reduce a).mp ha, hb⟩

/-- Same shape for `RLetU64Zero`. -/
theorem footprint_RLetU64Zero_disjoint
    (footprint : WriteFootprint) (x : String) (body : LowCT)
    (h_reduce : ∀ a, footprint (toJasminCmd (.RLetU64Zero x body)) a ↔
                     footprint (toJasminCmd body) a)
    (region : TrackedRegion)
    (h_body : MemoryModel.Disjoint (footprint (toJasminCmd body))
                       (array64Footprint region.base region.words)) :
    MemoryModel.Disjoint (footprint (toJasminCmd (.RLetU64Zero x body)))
             (array64Footprint region.base region.words) := by
  intro a ⟨ha, hb⟩
  exact h_body a ⟨(h_reduce a).mp ha, hb⟩

/-! ### Operational arms — hypothesis-discharge form (Qed)

Each of these needs the operational rule for the corresponding Jasmin
shape: `Cif` (`RIfNz`), `Cwhile` (`RWhileNz`), `Ccall` (`RCall`,
`RCloneCall`), and the `Oasm "STORE64"` `Copn` (`RLimbStore`). The
operational `Mem`-extension of `jasminSem` will discharge each of
the structural shape hypotheses
(`h_union`, `h_loop`, `h_clone`, `h_dest_disj`) directly from the
operational rules; here we discharge the disjointness consequence
modulo those hypotheses. -/

/-- `RCall f dest args` writes only to `dest`'s footprint; if every
    region's footprint is disjoint from `dest`, the call's memory
    footprint is contained in `dest`'s footprint plus whatever the
    leaf writes — both required to be disjoint. -/
theorem footprint_RCall_disjoint
    (footprint : WriteFootprint) (f : String)
    (dest : Located) (args : List Located)
    (region : TrackedRegion)
    (_h_dest_disj : ∀ a, footprint (toJasminCmd (.RCall f dest args)) a →
                        ¬ array64Footprint region.base region.words a) :
    MemoryModel.Disjoint (footprint (toJasminCmd (.RCall f dest args)))
             (array64Footprint region.base region.words) := by
  intro a ⟨ha, hb⟩
  exact _h_dest_disj a ha hb

/-- `RIfNz e ct cf` write footprint is the union of the two branches;
    the disjointness reduces to `ct` and `cf` separately. The
    union-shape (`h_union`) is the structural property that the
    operational `Mem`-extension of `jasminSem` will discharge for
    `Cif`; the framing-level lemma takes it as a hypothesis and closes
    the disjointness, mirroring `footprint_RSeq_disjoint`. -/
theorem footprint_RIfNz_disjoint
    (footprint : WriteFootprint) (e : String) (ct cf : LowCT)
    (h_union : ∀ a, footprint (toJasminCmd (.RIfNz e ct cf)) a ↔
                    footprint (toJasminCmd ct) a ∨
                    footprint (toJasminCmd cf) a)
    (region : TrackedRegion) :
    MemoryModel.Disjoint (footprint (toJasminCmd ct))
             (array64Footprint region.base region.words) →
    MemoryModel.Disjoint (footprint (toJasminCmd cf))
             (array64Footprint region.base region.words) →
    MemoryModel.Disjoint (footprint (toJasminCmd (.RIfNz e ct cf)))
             (array64Footprint region.base region.words) := by
  intro h1 h2 a ⟨ha, hb⟩
  rcases (h_union a).mp ha with hl | hr
  · exact h1 a ⟨hl, hb⟩
  · exact h2 a ⟨hr, hb⟩

/-- `RWhileNz e body` write footprint is `body`'s footprint (the loop
    closes over the same writable variables). The fixed-point shape
    (`h_loop`) is the structural property that the operational
    `Mem`-extension of `jasminSem` will discharge for `Cwhile`; here
    we take it as a hypothesis and discharge the disjointness
    directly. -/
theorem footprint_RWhileNz_disjoint
    (footprint : WriteFootprint) (e : String) (body : LowCT)
    (h_loop : ∀ a, footprint (toJasminCmd (.RWhileNz e body)) a ↔
                   footprint (toJasminCmd body) a)
    (region : TrackedRegion) :
    MemoryModel.Disjoint (footprint (toJasminCmd body))
             (array64Footprint region.base region.words) →
    MemoryModel.Disjoint (footprint (toJasminCmd (.RWhileNz e body)))
             (array64Footprint region.base region.words) := by
  intro h_body a ⟨ha, hb⟩
  exact h_body a ⟨(h_loop a).mp ha, hb⟩

/-- `RCloneCall` copies a tower slot then dispatches an inner call;
    its memory footprint coincides with the inner-call footprint
    (clone writes only to a fresh local register `cloneVar`, never
    memory). The shape (`h_clone`) is the structural property the
    operational `Mem`-extension of `jasminSem` will discharge for
    `CLONE_TOWER`; here we take it as a hypothesis and reduce to the
    inner-call disjointness. -/
theorem footprint_RCloneCall_disjoint
    (footprint : WriteFootprint)
    (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (innerF : String) (dest : Located) (args : List Located)
    (h_clone : ∀ a, footprint (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) a ↔
                    footprint (toJasminCmd (.RCall innerF dest args)) a)
    (region : TrackedRegion) :
    MemoryModel.Disjoint (footprint (toJasminCmd (.RCall innerF dest args)))
             (array64Footprint region.base region.words) →
    MemoryModel.Disjoint
      (footprint (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)))
      (array64Footprint region.base region.words) := by
  intro h_inner a ⟨ha, hb⟩
  exact h_inner a ⟨(h_clone a).mp ha, hb⟩

/-- `RLimbStore loc idx v` writes a single 64-bit word at `loc`'s
    footprint. **Identity form**: this lemma assumes exactly the disjointness it
    concludes. Deriving it needs a concrete `WriteFootprint` that fixes the
    STORE64 byte range to `[loc.base + 8·idx, loc.base + 8·idx + 8)`. -/
theorem footprint_RLimbStore_disjoint
    (footprint : WriteFootprint)
    (loc : Located) (idx : Nat) (v : BitVec 64)
    (region : TrackedRegion) :
    -- A concrete `WriteFootprint` would give us:
    -- `footprint (toJasminCmd (.RLimbStore loc idx v))`
    -- = `range (loc.base + UInt64.ofNat (8*idx)) 8`.
    MemoryModel.Disjoint (footprint (toJasminCmd (.RLimbStore loc idx v)))
             (array64Footprint region.base region.words) →
    MemoryModel.Disjoint (footprint (toJasminCmd (.RLimbStore loc idx v)))
             (array64Footprint region.base region.words) := by
  intro h
  exact h
  -- The non-trivial closure is the **derivation** of this Disjoint
  -- under STORE64's footprint shape — that awaits a concrete
  -- `WriteFootprint`.

/-! ## §6b. Hoare-triple form of the multi-region preservation

Compose the multi-region bridge with `BignumHoare.frame_array64`'s
HoareTriple shape. Given a step that respects a footprint, and a list
of regions all pairwise-disjoint and disjoint from the body's
footprint, the conjunction `∀ r ∈ regions, array64 r.base r.vals`
is preserved through the step in HoareTriple form. -/

/-- HoareTriple form of `borrowOk_implies_memory_invariants_preserved`.
The precondition asserts every tracked region's `array64` invariant;
the postcondition is the same conjunction post-step. -/
theorem hoare_multi_region_preserved
    (step : StepRel) (footprint : WriteFootprint)
    (h_resp : RespectsFootprint step footprint)
    (c : LowCT)
    (regions : List TrackedRegion)
    (h_disjoint_body :
        ∀ r ∈ regions,
          MemoryModel.Disjoint (footprint (toJasminCmd c))
                   (array64Footprint r.base r.words)) :
    HoareTriple step
      (fun s => TrackedRegions.InitArrays regions s.mem)
      (toJasminCmd c)
      (fun s => TrackedRegions.InitArrays regions s.mem) := by
  intro s s' h_init h_step
  intro r hr
  have h_arr : array64 r.base r.vals s.mem := h_init r hr
  have h_disj :
      MemoryModel.Disjoint (footprint (toJasminCmd c))
               (array64Footprint r.base r.vals.length) := by
    rw [r.hLen]; exact h_disjoint_body r hr
  exact array64_preserved_by_disjoint_step
          step footprint h_resp (toJasminCmd c) r.base r.vals
          h_disj s s' h_arr h_step

/-! ## §7. Smoke test

Instantiate the bridge on a single `RCall "fp_add" out [x, y]` with
`borrowOk = true`, two tracked regions for the inputs and one for the
output, all pairwise-disjoint. Exercises the statement shape; the
operational hypothesis is taken as a hypothesis (it awaits the
operational `Mem`-extension of `jasminSem` to handle `Ccall`).
-/

namespace Smoke

/-- Distinct names in our smoke example. -/
def out_loc : Located := { locVar := "out", locSrc := .TFp }
def x_loc   : Located := { locVar := "x",   locSrc := .TFp }
def y_loc   : Located := { locVar := "y",   locSrc := .TFp }

/-- The example program: `out := fp_add(x, y)`. -/
def prog : LowCT := .RCall "fp_add" out_loc [x_loc, y_loc]

/-- The borrow checker accepts: `out` is distinct from both `x` and `y`. -/
example : borrowOk prog = true := by decide

end Smoke

/-- Smoke instance: invoking the bridge on the `fp_add` call. The
    operational hypothesis (`step` lifts the call) is taken as a
    hypothesis for the smoke test, pending the operational
    `Mem`-extension of `jasminSem`. -/
theorem bridge_smoke_RCall_fp_add
    (step : StepRel) (footprint : WriteFootprint)
    (h_resp : RespectsFootprint step footprint)
    (regions : List TrackedRegion)
    (h_pairwise : TrackedRegions.PairwiseDisjoint regions)
    (h_disjoint_body :
        ∀ r ∈ regions,
          MemoryModel.Disjoint (footprint (toJasminCmd Smoke.prog))
                   (array64Footprint r.base r.words))
    (s s' : JasminMemState)
    (h_init  : TrackedRegions.InitArrays regions s.mem)
    (h_step  : step (toJasminCmd Smoke.prog) s s') :
    TrackedRegions.InitArrays regions s'.mem :=
  borrowOk_implies_memory_invariants_preserved
    step footprint h_resp Smoke.prog
    (by decide)        -- borrowOk Smoke.prog = true
    regions h_pairwise h_disjoint_body s s' h_init h_step

end CatCrypt.Crypto.SecureCompilation.BorrowToMemoryBridge
