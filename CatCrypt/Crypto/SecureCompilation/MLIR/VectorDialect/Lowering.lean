/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Denote
public import Mathlib.Data.List.FinRange

/-!
# MLIR `vector` dialect — Progressive lowering

This is the first lowering step in the progressive-lowering pipeline

```
VectorDialect.VectorOp                      -- abstract, this directory
  ↓  Lowering.lean              (here)
VectorDialect.ScalarExpansion              -- per-lane scalar ops
  ↓  CatCrypt Com / VIR pass     (emit files)
CatCrypt Com (BitVec / ZMod)
  ↓  ComToVeir / mlir-opt        (existing, see VIR/MlirArithDialect.lean)
LLVM / x86vector / arm_neon
```

The lowering here is *to* a small intermediate IR
(`ScalarExpansion α n`) that already does the per-lane fan-out — one entry per
lane. That keeps this file independent of the heavier `VIR/Core.lean`
`Com` machinery while still mirroring the MLIR-style "one op explodes into a
loop over lanes" transformation.

The intermediate IR is straightforward enough to denote in one step
(`runScalarExpansion`), and that denotation is shown to *agree* with the
abstract `denoteVectorOp` (`lower_*_correct`, `denoteVectorOp_eq_lower_*`).

This lowering does not produce `Com`. A `Com` lowering would reuse the
`VIR/MlirArithDialect` per-lane denotation (proven equivalent to the catCrypt
scalar IR); the remaining work is mechanical Var-bookkeeping.

## Selector abstraction

The `lower` function defined here commits to **one rule per `VectorOp`**.
For a real backend several equivalent lowerings exist for the same abstract
op (e.g. `VPADDQ_256` vs two `VPADDQ_128`s) and the *choice* between them is
a separate concern. That selector layer lives in
[`LoweringChoice.lean`](LoweringChoice.lean), which introduces
`LoweringEquivalenceClass` (a non-empty list of equivalent candidates) and
`lowerWithSelector` (a selector-driven variant of `lower`). The bridge
theorem `lowerWithSelector_eq_lower` shows that the abstracted form reduces
to `lower` when the build-function's head candidate matches the existing
direct rule, so the proven `denoteVectorOp_eq_lower_*` equivalences below
transport through unchanged. See the README for the design-choice rationale
(DialEgg vs eqsat papers).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The per-lane intermediate IR

An expanded program is a sequence of per-lane assignments, plus a final read
of the resulting vector / scalar. It is the smallest IR that has *one
instruction per lane* (which is what a real `vector → x86vector` lowering
emits before fusing back into a `__m256i` instruction). -/

/-- A *per-lane* instruction: write lane `i` to value `x`. -/
structure LaneStore (α : Type) (n : Nat) where
  /-- The lane being written. -/
  lane : Fin n
  /-- The value written into that lane. -/
  value : α

/-- The intermediate IR: a list of per-lane stores. `runScalarExpansion init
    stores` applies the stores left-to-right starting from the constant lane
    vector `init`. The resulting `Fin n → α` is the lowering's denotation. -/
@[reducible] def runLaneStores {α : Type} {n : Nat}
    (init : VectorTy α n) (stores : List (LaneStore α n)) : VectorTy α n :=
  stores.foldl (fun v s => VectorTy.insert v s.lane s.value) init

/-- A per-lane expansion of a vector op: a starting value and a list of
    lane stores. For pure pointwise ops every lane is touched exactly once,
    but the IR supports partial / re-stored programs (e.g. for `insert`,
    where only one lane is touched). -/
structure ScalarExpansion (α : Type) (n : Nat) where
  /-- Initial lane vector before stores. For pointwise ops this is unused
      because every lane gets overwritten; we still carry it so the IR can
      faithfully model `insert` (one store on top of an existing vector). -/
  init : VectorTy α n
  /-- The per-lane stores. -/
  stores : List (LaneStore α n)

/-- Denotation of the intermediate IR: apply the stores to the init vector. -/
@[reducible] def ScalarExpansion.denote {α : Type} {n : Nat}
    (p : ScalarExpansion α n) : VectorTy α n :=
  runLaneStores p.init p.stores

/-! ## 2. The lowering function

For each `VectorOp` constructor, the lowering builds an explicit per-lane
expansion. We focus on the **vector-result** ops; scalar-result ops
(`extract`, `reduce`) are not lowered here — their denotation IS a single
scalar and they have no per-lane fan-out. -/

/-- `defaultLane init` is the lane vector used when the lowering wants a
    fresh zero/init register. We use the broadcast of an explicit `init`
    so the IR stays element-type-polymorphic. -/
@[reducible] def defaultLane {α : Type} {n : Nat} (init : α) : VectorTy α n :=
  VectorTy.replicate init

/-- The lowering itself: convert a *vector-result* op to a `ScalarExpansion`.

    The function returns an `Option` because scalar-result ops (`extract` /
    `reduce`) have no vector lowering — those are returned as `none`. The
    lowering covers the vector-shape-preserving subset. -/
def lower {α : Type} {n : Nat} (init : α) : VectorOp α n → Option (ScalarExpansion α n)
  | .broadcast x =>
      -- One store per lane writing `x` (the canonical per-lane expansion
      -- the lowering needs to emit before fusing into `vbroadcastss`).
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, x⟩⟩
  | .extract _ _ => none
  | .insert v i x =>
      -- The expansion keeps `v` as the base and writes a single lane.
      some ⟨v, [⟨i, x⟩]⟩
  | .add op v w =>
      -- Per-lane stores: lane i ← op (v i) (w i).
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, op (v i) (w i)⟩⟩
  | .mul op v w =>
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, op (v i) (w i)⟩⟩
  | .fma addOp mulOp a b c =>
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, addOp (mulOp (a i) (b i)) (c i)⟩⟩
  | .shuffle v π =>
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, v (π i)⟩⟩
  | .reduce _ _ _ => none
  | .shiftL shf m v =>
      -- Per-lane stores: lane i ← shf (v i) m.
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, shf (v i) m⟩⟩
  | .shiftR shf m v =>
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, shf (v i) m⟩⟩
  | .mulHi op v w =>
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, op (v i) (w i)⟩⟩
  | .shiftRA shf m v =>
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, shf (v i) m⟩⟩
  | .affineByte aff v =>
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, aff (v i)⟩⟩
  | .aesRound rnd s k =>
      some ⟨defaultLane init,
            (List.finRange n).map fun i => ⟨i, rnd (s i) (k i)⟩⟩

/-! ## 3. Denotation-preservation theorems

For `broadcast` and `add` we prove
`denoteVectorOp op = .vec (lower init op).get.denote`.

These are exactly the "vector op = expanded per-lane program" equations a
correct lowering needs. -/

/-- Inserting at a different lane leaves the lookup unchanged. -/
@[simp] theorem VectorTy.insert_apply_ne {α : Type} {n : Nat}
    (v : VectorTy α n) (i j : Fin n) (x : α) (h : j ≠ i) :
    (VectorTy.insert v i x) j = v j := by
  unfold VectorTy.insert
  simp [h]

/-- Inserting at lane `i` and reading lane `i` gives back the stored value. -/
@[simp] theorem VectorTy.insert_apply_self {α : Type} {n : Nat}
    (v : VectorTy α n) (i : Fin n) (x : α) :
    (VectorTy.insert v i x) i = x := by
  unfold VectorTy.insert
  simp

/-- Folding a sequence of stores whose lanes don't include `i` is a no-op at
    lane `i`. -/
theorem foldl_insert_notMem
    {α : Type} {n : Nat} (i : Fin n) (f : Fin n → α) :
    ∀ (L : List (Fin n)) (w : VectorTy α n), i ∉ L →
      (L.map (fun j => ({ lane := j, value := f j } : LaneStore α n))).foldl
          (fun v s => VectorTy.insert v s.lane s.value) w i = w i
  | [], _, _ => rfl
  | head :: tail, w, hmem => by
      have hhead : head ≠ i := fun heq =>
        hmem (heq ▸ List.mem_cons_self)
      have htail : i ∉ tail := fun hin => hmem (List.mem_cons_of_mem _ hin)
      simp only [List.map_cons, List.foldl_cons]
      rw [foldl_insert_notMem i f tail _ htail]
      -- (insert w head (f head)) i = w i since head ≠ i.
      show (VectorTy.insert w head (f head)) i = w i
      exact VectorTy.insert_apply_ne w head i (f head) (Ne.symm hhead)

/-- The key bridge lemma: folding lane-by-lane stores produced from
    `List.finRange n` writes `f i` to lane `i`. -/
theorem runLaneStores_finRange_map
    {α : Type} {n : Nat} (init : VectorTy α n) (f : Fin n → α) :
    runLaneStores init ((List.finRange n).map fun i => ⟨i, f i⟩)
      = fun i => f i := by
  funext i
  -- Split `List.finRange n` at lane `i`'s position. We use a more general
  -- statement: for any list `L` containing `i` exactly once, the fold gives
  -- `f i` at lane `i`.
  have key : ∀ (L : List (Fin n)) (v : VectorTy α n),
      i ∈ L → L.Nodup →
      (L.map (fun j => ({ lane := j, value := f j } : LaneStore α n))).foldl
          (fun v s => VectorTy.insert v s.lane s.value) v i = f i := by
    intro L
    induction L with
    | nil => intro v hmem _; cases hmem
    | cons head tail ih =>
      intro v hmem hnodup
      simp only [List.map_cons, List.foldl_cons]
      rcases List.mem_cons.mp hmem with hh | ht
      · -- head = i; tail doesn't contain i (nodup), so the head's insert wins.
        -- `hh : i = head`; substitute head ↦ i.
        subst hh
        -- Note: after subst, `head` is gone and replaced everywhere by `i`.
        have hntail : i ∉ tail := List.nodup_cons.mp hnodup |>.1
        rw [foldl_insert_notMem i f tail _ hntail]
        show (VectorTy.insert v i (f i)) i = f i
        exact VectorTy.insert_apply_self v i (f i)
      · -- i is in the tail; recurse.
        exact ih _ ht (List.nodup_cons.mp hnodup |>.2)
  exact key (List.finRange n) init (List.mem_finRange i) (List.nodup_finRange _)

/-- **Lowering of `broadcast` preserves denotation.**
    The lowered program (one store per lane, all with value `x`) denotes to
    the constant vector `replicate x`, which is exactly the abstract
    denotation of `broadcast`. -/
theorem lower_broadcast_correct {α : Type} {n : Nat} (init : α) (x : α) :
    (lower init (.broadcast x : VectorOp α n)).map (·.denote)
      = some (VectorTy.replicate x) := by
  -- Reduce to runLaneStores_finRange_map with `f = fun _ => x`.
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init) (f := fun _ => x)]

/-- **Lowering of `add` preserves denotation.**
    The lowered program (one store per lane writing `op (v i) (w i)`)
    denotes to `map₂ op v w`, exactly the abstract denotation of `add op v w`. -/
theorem lower_add_correct {α : Type} {n : Nat} (init : α)
    (op : α → α → α) (v w : VectorTy α n) :
    (lower init (.add op v w : VectorOp α n)).map (·.denote)
      = some (VectorTy.map₂ op v w) := by
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => op (v i) (w i))]

/-- **Lowering of `shiftL` preserves denotation.**
    The lowered program (one store per lane writing `shf (v i) m`) denotes to
    `map₁imm shf m v`, exactly the abstract denotation of `shiftL shf m v`. -/
theorem lower_shiftL_correct {α : Type} {n : Nat} (init : α)
    (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lower init (.shiftL shf m v : VectorOp α n)).map (·.denote)
      = some (VectorTy.map₁imm shf m v) := by
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => shf (v i) m)]

/-- **Lowering of `shiftR` preserves denotation.** -/
theorem lower_shiftR_correct {α : Type} {n : Nat} (init : α)
    (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lower init (.shiftR shf m v : VectorOp α n)).map (·.denote)
      = some (VectorTy.map₁imm shf m v) := by
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => shf (v i) m)]

/-- **Lowering of `mul` preserves denotation.** Same binary
    lane-fan-out shape as `add`; the carried op is the multiply. -/
theorem lower_mul_correct {α : Type} {n : Nat} (init : α)
    (op : α → α → α) (v w : VectorTy α n) :
    (lower init (.mul op v w : VectorOp α n)).map (·.denote)
      = some (VectorTy.map₂ op v w) := by
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => op (v i) (w i))]

/-- **Lowering of `mulHi` preserves denotation.**
    The lowered program (one store per lane writing `op (v i) (w i)`) denotes
    to `map₂ op v w`, exactly the abstract denotation of `mulHi op v w`. The
    high-half-product op shares the binary-`map₂` lowering shape with `mul`. -/
theorem lower_mulHi_correct {α : Type} {n : Nat} (init : α)
    (op : α → α → α) (v w : VectorTy α n) :
    (lower init (.mulHi op v w : VectorOp α n)).map (·.denote)
      = some (VectorTy.map₂ op v w) := by
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => op (v i) (w i))]

/-- **Lowering of `shiftRA` (signed arithmetic shift) preserves
    denotation.** Same lane-fan-out shape as `shiftR`; the carried op is the
    arithmetic (sign-extending) shift. -/
theorem lower_shiftRA_correct {α : Type} {n : Nat} (init : α)
    (shf : α → Nat → α) (m : Nat) (v : VectorTy α n) :
    (lower init (.shiftRA shf m v : VectorOp α n)).map (·.denote)
      = some (VectorTy.map₁imm shf m v) := by
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => shf (v i) m)]

/-- **Lowering of `affineByte` (per-lane GF(2) affine) preserves
    denotation.** The lowered program (one store per lane writing `aff (v i)`)
    denotes to `map₁ aff v`, the abstract denotation of `affineByte aff v`.
    Same UNARY lane-fan-out shape as `shiftL`/`shiftR` (the matrix/bias are
    closed over in `aff`, so no immediate operand). -/
theorem lower_affineByte_correct {α : Type} {n : Nat} (init : α)
    (aff : α → α) (v : VectorTy α n) :
    (lower init (.affineByte aff v : VectorOp α n)).map (·.denote)
      = some (VectorTy.map₁ aff v) := by
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => aff (v i))]

/-- **Lowering of `aesRound` (per-lane AES round step) preserves
    denotation.** The lowered program (one store per lane writing
    `rnd (s i) (k i)`) denotes to `map₂ rnd s k`, the abstract denotation of
    `aesRound rnd s k`. Same binary-`map₂` lowering shape as `add`/`mul`. -/
theorem lower_aesRound_correct {α : Type} {n : Nat} (init : α)
    (rnd : α → α → α) (s k : VectorTy α n) :
    (lower init (.aesRound rnd s k : VectorOp α n)).map (·.denote)
      = some (VectorTy.map₂ rnd s k) := by
  show some _ = some _
  congr 1
  show runLaneStores _ _ = _
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => rnd (s i) (k i))]

/-- The lowering of a `broadcast x` is the obvious `ScalarExpansion`. -/
@[reducible] def loweredBroadcast {α : Type} (n : Nat) (init x : α) :
    ScalarExpansion α n :=
  ⟨defaultLane init, (List.finRange n).map fun i => ⟨i, x⟩⟩

/-- The lowering of an `add op v w` is the obvious `ScalarExpansion`. -/
@[reducible] def loweredAdd {α : Type} {n : Nat} (init : α)
    (op : α → α → α) (v w : VectorTy α n) : ScalarExpansion α n :=
  ⟨defaultLane init, (List.finRange n).map fun i => ⟨i, op (v i) (w i)⟩⟩

/-- Identity: `lower init (.broadcast x) = some (loweredBroadcast init x)`. -/
@[simp] theorem lower_broadcast_eq {α : Type} (n : Nat) (init x : α) :
    lower init (.broadcast x : VectorOp α n) = some (loweredBroadcast n init x) :=
  rfl

/-- Identity: `lower init (.add op v w) = some (loweredAdd init op v w)`. -/
@[simp] theorem lower_add_eq {α : Type} {n : Nat} (init : α)
    (op : α → α → α) (v w : VectorTy α n) :
    lower init (.add op v w : VectorOp α n) = some (loweredAdd init op v w) :=
  rfl

/-- **Bundled lowering theorem (broadcast).** The abstract denotation of `broadcast x`
    equals the vector denoted by its lowered `ScalarExpansion`. -/
theorem denoteVectorOp_eq_lower_broadcast {α : Type} (n : Nat) (init x : α) :
    denoteVectorOp (.broadcast x : VectorOp α n)
      = VectorOp.Result.vec (loweredBroadcast n init x).denote := by
  show VectorOp.Result.vec (VectorTy.replicate x)
       = VectorOp.Result.vec (loweredBroadcast n init x).denote
  congr 1
  show VectorTy.replicate x
       = runLaneStores (defaultLane init) ((List.finRange n).map fun i => ⟨i, x⟩)
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun (_ : Fin n) => x)]

/-- **Bundled lowering theorem (add).** The abstract denotation of `add op v w`
    equals the vector denoted by its lowered `ScalarExpansion`. -/
theorem denoteVectorOp_eq_lower_add {α : Type} {n : Nat} (init : α)
    (op : α → α → α) (v w : VectorTy α n) :
    denoteVectorOp (.add op v w : VectorOp α n)
      = VectorOp.Result.vec (loweredAdd init op v w).denote := by
  show VectorOp.Result.vec (VectorTy.map₂ op v w)
       = VectorOp.Result.vec (loweredAdd init op v w).denote
  congr 1
  show VectorTy.map₂ op v w
       = runLaneStores (defaultLane init)
           ((List.finRange n).map fun i => ⟨i, op (v i) (w i)⟩)
  rw [runLaneStores_finRange_map (init := defaultLane init)
        (f := fun i => op (v i) (w i))]

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
