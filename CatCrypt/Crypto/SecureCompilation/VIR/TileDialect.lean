/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Tile VIR dialect

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A minimal `VIR.Dialect` whose `Op`/`Ty` model the **tile** (GPU / Tile-IR)
fragment: a value is a *tile* — `n` lanes of `BitVec w`. This is the Tile-IR
analogue of `jasminDialect` (`JasminDialect.lean`): it makes "tile" a
first-class `Com` dialect so the front can lower **into** tile ops, exactly as
it already lowers into the word-level Jasmin dialect. The tile model thereby
becomes an actual backend dialect rather than a side semantics.

The shape mirrors NVIDIA's CUDA tile IR (`cuda_tile`), where the primitive
datum is a fixed-shape tile of scalars and the core compute ops are
elementwise/SIMT lane maps. We keep the dialect deliberately minimal — one tile
type and one elementwise binary op family — so it stays small and fully
provable, in the same spirit as the `jasminDialect` spike.

## Types (`TileTy`)

* `tile n w` — an `n`-lane tile of `w`-bit words, `⟦·⟧ = Fin n → BitVec w`.

This reuses the **same carrier** the Jasmin dialect already uses for its
`stackArr w n` type (`Fin n → BitVec w`): the VIR `Ty`/`TyDenote` framework is
open (any inductive with a `TyDenote` instance is a legal `Dialect.Ty`), so a
tile is represented by a *new* type constructor `.tile n w` denoting the lane
function — no edit to the shared framework, and no packing into a flat
`BitVec (n*w)` carrier is needed.

## Ops (`TileOp`)

* `tileBin (op) (n w)` — elementwise tile binary op: two `tile n w` operands,
  one `tile n w` result, applying the per-lane scalar `JasminBinOp` (reused
  from `JasminDialect`) independently in each lane. This is the SIMT lane map
  `fun i => op.apply (a i) (b i)` — the tile analogue of `regArith` (which is
  the single-lane / scalar case).
* `tilePermute (n w)` — data-dependent gather: lane `i` of the result reads lane
  `(idx[i] mod n)` of the data tile (the `cuda_tile.permute` image; what an NTT
  butterfly / Poseidon2 MDS shuffle needs).
* `tileBroadcast (n w) (lane)` — splat one lane across the whole tile
  (`cuda_tile.broadcast`).
* `tileReduce (n w)` — horizontal `+`-reduce-and-broadcast: every result lane
  holds `Σ_j a[j]` (`cuda_tile.reduce`).

These three are the **cross-tile (lane-moving)** ops, lifted into the dialect
from the operational `TileModel`'s `permxv`/`bcast`/`hadd` arms. They are still
pure functions of the lane carrier (no async copy / barrier, hence no
memory-consistency model), so each ties to its `TileModel` arm by `rfl`/`funext`
(`TileDialectModelTie.lean`). Op names mirror NVIDIA's tile dialect
(source: https://github.com/NVIDIA/cuda-tile, `Dialect/CudaTile/IR/Ops.td`); the
op set was rounded out after evaluating NVlabs' `cuda-oxide`
(source: https://github.com/NVlabs/cuda-oxide), which reaches the same GPU ops
via Rust intrinsics → Pliron → LLVM → PTX (unverified) rather than a pinned
tile-IR semantics.

## Pure-only

Like `jasminDialect`, this dialect lives in VIR's pure denotation: a tile is a
total lane function and `tileBin` is a total elementwise map, so the denotation
is total for every `n` (including the empty tile `n = 0`).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.TileDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)

/-! ## 1. Types -/

/-- The tile dialect's value-type alphabet: a single tile type. A `tile n w`
    is `n` lanes of `w`-bit words. -/
inductive TileTy where
  /-- An `n`-lane tile of `w`-bit words. -/
  | tile (n w : Nat)
  deriving DecidableEq

/-- Total denotation of `TileTy` into Lean types. A tile is a lane function
    `Fin n → BitVec w` (the same carrier `jasminDialect`'s `stackArr` uses). -/
@[reducible] instance : TyDenote TileTy where
  denote
    | .tile n w => Fin n → BitVec w

/-! ## 2. Op tags -/

/-- Operation tags for the tile dialect. A single elementwise binary op family;
    the scalar op is a `JasminBinOp` reused from `JasminDialect`. -/
inductive TileOp where
  /-- Elementwise (SIMT lane map) binary op on `tile n w`: applies the scalar
      `op` independently in each of the `n` lanes. The tile analogue of
      `JasminOp.regArith` (the single-lane case). -/
  | tileBin (op : JasminBinOp) (n w : Nat)
  /-- Cross-tile gather (`cuda_tile.permute`): two `tile n w` operands `idx`, `a`;
      result lane `i` is lane `(idx[i] mod n)` of `a`. -/
  | tilePermute (n w : Nat)
  /-- Cross-tile splat (`cuda_tile.broadcast`): one `tile n w` operand `a`;
      every result lane is lane `(lane mod n)` of `a`. -/
  | tileBroadcast (n w : Nat) (lane : Nat)
  /-- Cross-tile reduce (`cuda_tile.reduce`): one `tile n w` operand `a`; every
      result lane holds the horizontal sum `Σ_j a[j]`. -/
  | tileReduce (n w : Nat)
  deriving DecidableEq

/-! ## 3. The dialect -/

/-- The tile dialect: `Op` is `TileOp`, `Ty` is `TileTy`. -/
@[reducible] def tileDialect : Dialect :=
  { Op := TileOp, Ty := TileTy }

/-- Elementwise application of a `JasminBinOp` over two tiles: apply the scalar
    op per lane, no cross-lane interaction. The data effect of `tileBin`. -/
def tileBinApply {n w : Nat} (op : JasminBinOp) (a b : Fin n → BitVec w) :
    Fin n → BitVec w :=
  fun i => op.apply (a i) (b i)

/-- The data effect of `tilePermute`: lane `i` gathers lane `(idx[i] mod n)` of
    `a`. Mirrors `TileModel.evalTileOp`'s `.permxv` arm exactly (same index
    proof), so the dialect↔model tie is `rfl`. -/
def tilePermuteApply {n w : Nat} (idx a : Fin n → BitVec w) : Fin n → BitVec w :=
  fun i => a ⟨(idx i).toNat % n,
    Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0))⟩

/-- The data effect of `tileBroadcast`: every lane is lane `(lane mod n)` of `a`.
    Mirrors `TileModel.evalTileOp`'s `.bcast` arm. -/
def tileBroadcastApply {n w : Nat} (lane : Nat) (a : Fin n → BitVec w) :
    Fin n → BitVec w :=
  fun i => a ⟨lane % n,
    Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0))⟩

/-- The data effect of `tileReduce`: every lane holds the horizontal sum
    `Σ_j a[j]`. Mirrors `TileModel.evalTileOp`'s `.hadd` arm. -/
def tileReduceApply {n w : Nat} (a : Fin n → BitVec w) : Fin n → BitVec w :=
  fun _ => (List.finRange n).foldl (fun acc j => acc + a j) 0

/-! ## 4. Op signatures (arg types + return type) -/

instance : DialectSignature tileDialect where
  sig op := match op with
    | .tileBin _ n w => [.tile n w, .tile n w]
    | .tilePermute n w => [.tile n w, .tile n w]
    | .tileBroadcast n w _ => [.tile n w]
    | .tileReduce n w => [.tile n w]
  ret op := match op with
    | .tileBin _ n w => .tile n w
    | .tilePermute n w => .tile n w
    | .tileBroadcast n w _ => .tile n w
    | .tileReduce n w => .tile n w

/-! ## 5. Op denotation -/

instance tileDenote : DialectDenote tileDialect where
  denote op := match op with
    | .tileBin op n w => fun args =>
        let a : Fin n → BitVec w := args.head
        let b : Fin n → BitVec w := args.tail.head
        tileBinApply op a b
    | .tilePermute n w => fun args =>
        let idx : Fin n → BitVec w := args.head
        let a : Fin n → BitVec w := args.tail.head
        tilePermuteApply idx a
    | .tileBroadcast n w lane => fun args =>
        tileBroadcastApply lane (args.head : Fin n → BitVec w)
    | .tileReduce n w => fun args =>
        tileReduceApply (args.head : Fin n → BitVec w)

/-! ## 6. Smoke test

Build a tiny one-op `Com tileDialect` and check `Com.denote` computes the
expected per-lane value. On two input tiles `a b : tile 4 8`:

    let s = tileBin add a b   -- s i = a i + b i   : tile 4 8
    ret s

so `denote ⟨a, b⟩ = fun i => a i + b i`. We check it on a concrete pair of
tiles. -/

/-- One-op smoke program over `[tile 4 8, tile 4 8]`: a single elementwise add. -/
def smokeProg : Com tileDialect [.tile 4 8, .tile 4 8] (.tile 4 8) :=
  .var (.mk (.tileBin .add 4 8) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- A concrete 4-lane input tile of 8-bit words. -/
def tileA : Fin 4 → BitVec 8 := fun i => BitVec.ofNat 8 i.val          -- 0,1,2,3
/-- A second concrete 4-lane input tile of 8-bit words. -/
def tileB : Fin 4 → BitVec 8 := fun i => BitVec.ofNat 8 (10 + i.val)   -- 10,11,12,13

/-- The smoke program denotes to the per-lane sum `fun i => a i + b i` on the
    input valuation `⟨a, b⟩`; checked on concrete tiles `tileA`, `tileB` whose
    lane sums are `10, 12, 14, 16`. -/
example :
    smokeProg.denote (.cons tileA (.cons tileB .nil))
      = (fun i => tileA i + tileB i) := by
  rfl

/-- The same smoke check stated pointwise on concrete values, closed by
    `decide` (lane sums `10, 12, 14, 16`). -/
example :
    (smokeProg.denote (.cons tileA (.cons tileB .nil)) 0 = (10 : BitVec 8)) ∧
    (smokeProg.denote (.cons tileA (.cons tileB .nil)) 3 = (16 : BitVec 8)) := by
  decide

/-! ### 6a. Cross-tile smoke

A one-op `Com tileDialect` horizontal reduce, demonstrating a cross-tile
(lane-moving) op as a first-class `Com` node (not just an operational-model
arm). On `tileA = [0,1,2,3]` the reduce yields `0+1+2+3 = 6` in every lane. -/

/-- One-op reduce program over `[tile 4 8]`: `tileReduce`, the `cuda_tile.reduce`
    image, as a `Com tileDialect` node. -/
def reduceProg : Com tileDialect [.tile 4 8] (.tile 4 8) :=
  .var (.mk (.tileReduce 4 8) rfl (.cons .here .nil))
    (.ret .here)

/-- The reduce program denotes to the lane-uniform horizontal sum of its input. -/
example :
    reduceProg.denote (.cons tileA .nil)
      = (fun _ => (List.finRange 4).foldl (fun acc j => acc + tileA j) 0) :=
  rfl

/-- Pointwise: every lane holds `0+1+2+3 = 6`. -/
example :
    (reduceProg.denote (.cons tileA .nil) 0 = (6 : BitVec 8)) ∧
    (reduceProg.denote (.cons tileA .nil) 3 = (6 : BitVec 8)) := by
  decide

end CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
