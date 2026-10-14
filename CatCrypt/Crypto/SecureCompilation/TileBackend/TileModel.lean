/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect


@[expose] public section
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)

/-!
# Tile model — a tile-level semantics for the GPU backend

A small **tile-level operational semantics** in Lean for the
`Com → Tile → NVIDIA Tile IR` path: a tile is a lane vector, and a tile program is
a straight-line list of lane-wise and lane-moving ops over named tiles.

## Contents

* **Model**: a tile is `n` lanes of `BitVec w` (`Tile n w`); `TileOp` has
  elementwise integer ops (`add`/`sub`/`mul`/`and`/`orr`/`xorr`/`andn`/shifts/
  `const`/`mulhs`) and the lane-moving `permxv`/`bcast`/`hadd`; `evalTileOp` gives
  each op its per-lane `BitVec w` meaning.
* **`bbMul`**: the BabyBear Barrett multiply as a tile program (`bbMulTile`);
  `bbMulTile_denote` proves that its output lane `i` is `bbMulWord (a i) (b i)`,
  where `bbMulWord` is the branchless Barrett word function. No theorem here
  proves `bbMulWord a b = (a · b) mod p`; `bbMulTile_kat` checks it on four lanes.
* **Lowering**: `lowerRegBlock_denote` proves that the `RegInstr → TileOp`
  lowering preserves the `TileState` semantics for every block and every shape
  `(n, w)`. The source semantics `evalRegInstr` is defined lane-wise with the
  unmasked lane operation `JasminBinOp.applyLane`; no theorem here relates it to `Com.denote` or to an
  x86/ARM/RISC-V vector model (the bridges for those are `ZmmArithBridge` and
  `VectorBackendBridge`).

## Relation to `cuda_tile`

* The op set is the `CudaTile` integer-arithmetic subset
  (`github.com/NVIDIA/cuda-tile`, `Dialect/CudaTile/IR/Ops.td`): our `add`/`sub`/
  `mul`/`and`/`shr`/`const` are `cuda_tile.{addi,subi,muli,andi,shli/shrui,
  constant}`, all "Element-wise integer" ops, over the tile type
  `!cuda_tile.tile<8xi64>` (`Types.td`: shape × element, power-of-two dims). The
  correspondence of these names to `cuda_tile` semantics is by reading the
  dialect definition, not a theorem. The emitter is `ComToTileIR`.
* **No memory-consistency model.** Asynchronous copies and barriers (spec §7,
  Memory Model) are not modelled; every op is a pure function of the lane
  vectors.
* **No execution.** Nothing in this module runs on a GPU or checks emitted IR.
-/

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

set_option autoImplicit false

/-! ## 1. Tiles and tile state — the shape-generic SIMD lane model

A tile is `n` lanes of `BitVec w` — the **shape-polymorphic** lane abstraction
(`cuda_tile.tile<n × w>`). The fixed-shape vector lane types have this shape: ZMM
is `Tile 8 64`, AVX2 `Tile 4 64`, NEON `Tile 2 64`. The tile state is a register
file of named tiles. The lowering theorem of §6 is stated for arbitrary
`(n, w)`; relating a machine vector model to `TileState` is done in separate
bridge modules. -/

/-- A tile: `n` lanes of `BitVec w`. The shape-generic SIMD lane model. -/
abbrev Tile (n w : Nat) := Fin n → BitVec w

/-- The default spike shape: 8 lanes (the ZMM shape). -/
abbrev tileLen : Nat := 8

/-- A tile-state register file: named `n×w` tiles. -/
structure TileState (n w : Nat) where
  regs : String → Tile n w

/-- Read a named tile. -/
def TileState.get {n w : Nat} (s : TileState n w) (nm : String) : Tile n w := s.regs nm

/-- Write a named tile. -/
def TileState.set {n w : Nat} (s : TileState n w) (nm : String) (t : Tile n w) : TileState n w :=
  { regs := fun r => if r = nm then t else s.regs r }

/-! ## 2. The elementwise tile op alphabet + its semantics

Each elementwise op is the per-element integer operation over `BitVec w`. `shr`
carries an immediate; `const` is a lane-uniform broadcast. The meaning is fixed
by `evalTileOp`, independently of the Tile IR spec §8 mnemonics. -/

/-- A tile op over named tiles. The `add`/`sub`/`mul`/`and`/`orr`/`xorr`/
    `andn` are the **elementwise** two-operand `cuda_tile.{addi,subi,muli,andi,
    ori,xori,…}`; `shll`/`shrr` are the two-operand variable shifts (per lane by
    the second tile's `.toNat`), the faithful image of `regArith .shl`/`.shr`;
    `shr` keeps the immediate form for the field-leaf prototypes; `const` is a
    lane-uniform broadcast. Together they cover the full `JasminBinOp` source
    alphabet.

    `permxv`/`bcast`/`hadd` are the **cross-tile (lane-moving)** ops — the
    `cuda_tile.{permute,broadcast,reduce}` subset — that let a tile program
    express NTT butterflies / Poseidon2 MDS shuffles, not just elementwise
    arithmetic: `permxv` is a data-dependent gather (lane `i` of dst reads the
    lane of `a` named by lane `i` of the index tile, mod `n`), `bcast` splats
    one lane across the tile, `hadd` reduces all lanes by `+` and broadcasts the
    sum.

    `shl`/`sar`/`rotl`/`rotr` are the shifts and rotations by an immediate beside
    `shr`; `mulhu` is the unsigned high-half multiply; `shuffle` and `blend`
    select lanes of two tiles by a static index list and a static mask. -/
inductive TileOp where
  | add (dst a b : String)
  | sub (dst a b : String)
  | mul (dst a b : String)
  | and (dst a b : String)
  | orr (dst a b : String)
  | xorr (dst a b : String)
  | andn (dst a b : String)
  | shll (dst a b : String)
  | shrr (dst a b : String)
  | shr (dst a : String) (imm : Nat)
  | const (dst : String) (n : Nat)
  /-- Signed high-half multiply (`mulhs`): lane `i` of `dst` is the **high `w`
      bits** of the signed `BitVec w × BitVec w → BitVec (2w)` product of lanes
      `a i`, `b i`. The shape-generic image of the packed signed high-multiply
      each SIMD ISA exposes for the FIPS-203 ML-KEM NTT Montgomery butterfly:
      x86 `VPMULHW`, ARM `SQDMULH`-class, RISC-V `vmulh.vv` (at `SEW = 16`,
      `w = 16`). The elementwise op the `Tile 8 16` Montgomery path lowers to. -/
  | mulhs (dst a b : String)
  -- cross-tile (lane-moving) ops: the `cuda_tile.{permute,broadcast,reduce}`
  -- subset, needed for NTT butterflies / Poseidon2 MDS shuffles (not elementwise).
  | permxv (dst idx a : String)
  | bcast (dst a : String) (lane : Nat)
  | hadd (dst a : String)
  /-- Shift left by the immediate `imm`: lane `i` of `dst` is `a i <<< imm`. -/
  | shl (dst a : String) (imm : Nat)
  /-- Arithmetic shift right by the immediate `imm`: lane `i` of `dst` is
      `(a i).sshiftRight imm`. -/
  | sar (dst a : String) (imm : Nat)
  /-- Rotate left by the immediate `imm`: lane `i` of `dst` is
      `(a i).rotateLeft imm`. -/
  | rotl (dst a : String) (imm : Nat)
  /-- Rotate right by the immediate `imm`: lane `i` of `dst` is
      `(a i).rotateRight imm`. -/
  | rotr (dst a : String) (imm : Nat)
  /-- Unsigned high-half multiply: lane `i` of `dst` is the high `w` bits of the
      unsigned double-width product of `a i` and `b i`. -/
  | mulhu (dst a b : String)
  /-- Shuffle by the static index list `idx`: lane `i` of `dst` is lane
      `j = idx[i] mod 2n` of the concatenation of `a` and `b`, that is `a j` for
      `j < n` and `b (j - n)` otherwise; a lane without an entry in `idx` takes
      the index `i`. -/
  | shuffle (dst a b : String) (idx : List Nat)
  /-- Blend by the static mask `mask`: lane `i` of `dst` is `b i` when `mask[i]`
      is `true` and `a i` otherwise; a lane without an entry in `mask` takes
      `a i`. -/
  | blend (dst a b : String) (mask : List Bool)
  deriving Repr, DecidableEq

/-- The per-element semantics of one tile op at shape `n×w` (each a per-lane
    `BitVec w` op, matching `JasminBinOp.applyLane` for the two-operand arms). -/
def evalTileOp {n w : Nat} (s : TileState n w) : TileOp → TileState n w
  | .add d a b => s.set d (fun i => s.get a i + s.get b i)
  | .sub d a b => s.set d (fun i => s.get a i - s.get b i)
  | .mul d a b => s.set d (fun i => s.get a i * s.get b i)
  | .and d a b => s.set d (fun i => s.get a i &&& s.get b i)
  | .orr d a b => s.set d (fun i => s.get a i ||| s.get b i)
  | .xorr d a b => s.set d (fun i => s.get a i ^^^ s.get b i)
  | .andn d a b => s.set d (fun i => (~~~ s.get a i) &&& s.get b i)
  | .shll d a b => s.set d (fun i => s.get a i <<< (s.get b i).toNat)
  | .shrr d a b => s.set d (fun i => s.get a i >>> (s.get b i).toNat)
  | .shr d a imm => s.set d (fun i => s.get a i >>> imm)
  | .const d k => s.set d (fun _ => BitVec.ofNat w k)
  | .mulhs d a b =>
      s.set d (fun i =>
        (((s.get a i).signExtend (2 * w) * (s.get b i).signExtend (2 * w)).sshiftRight w).truncate w)
  | .permxv d idx a =>
      s.set d (fun i => s.get a ⟨(s.get idx i).toNat % n,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0))⟩)
  | .bcast d a k =>
      s.set d (fun i => s.get a ⟨k % n,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0))⟩)
  | .hadd d a => s.set d (fun _ => (List.finRange n).foldl (fun acc j => acc + s.get a j) 0)
  | .shl d a imm => s.set d (fun i => s.get a i <<< imm)
  | .sar d a imm => s.set d (fun i => (s.get a i).sshiftRight imm)
  | .rotl d a imm => s.set d (fun i => (s.get a i).rotateLeft imm)
  | .rotr d a imm => s.set d (fun i => (s.get a i).rotateRight imm)
  | .mulhu d a b =>
      s.set d (fun i => BitVec.ofNat w ((s.get a i).toNat * (s.get b i).toNat / 2 ^ w))
  | .shuffle d a b idx =>
      s.set d (fun i =>
        if h : idx.getD i.val i.val % (2 * n) < n then s.get a ⟨_, h⟩
        else s.get b ⟨idx.getD i.val i.val % (2 * n) - n, by
          have := Nat.mod_lt (idx.getD i.val i.val) (show 0 < 2 * n by have := i.isLt; omega)
          omega⟩)
  | .blend d a b mask => s.set d (fun i => if mask.getD i.val false then s.get b i else s.get a i)

/-- Run a straight-line tile block (a fold of `evalTileOp`). -/
def runTileBlock {n w : Nat} (s : TileState n w) (block : List TileOp) : TileState n w :=
  block.foldl evalTileOp s

/-! ### 2a. Cross-tile ops: denotation + a worked permute KAT

`permxv` is the data-dependent gather an NTT butterfly / MDS shuffle needs:
running `[.permxv "d" "idx" "a"]` writes into `"d"` the tile whose lane `i` is
lane `(idx[i] mod n)` of `a`. `permxv_denote` states exactly that, and the KAT
specialises it at `Tile 4 32` to a reversal (`idx = [3,2,1,0]`). -/

/-- **`permxv` denotation.** Running the single-op block `[.permxv "d" "idx" "a"]`
    writes into `"d"` the gathered tile `i ↦ a[(idx[i] mod n)]`. (The lane-moving
    analogue of `bbMulTile_denote`, for the cross-tile permute op.) -/
theorem permxv_denote {n w : Nat} (s : TileState n w) (d idx a : String) :
    (runTileBlock s [.permxv d idx a]).get d
      = fun i => s.get a ⟨(s.get idx i).toNat % n,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0))⟩ := by
  funext i
  simp [runTileBlock, evalTileOp, TileState.set, TileState.get]

/-- A `Tile 4 32` permute KAT input: `a = [10, 20, 30, 40]`, `idx = [3, 2, 1, 0]`
    (a lane reversal). -/
def permA : Tile 4 32 := fun i => (#[10, 20, 30, 40].getD i.val 0 : BitVec 32)
def permIdx : Tile 4 32 := fun i => (#[3, 2, 1, 0].getD i.val 0 : BitVec 32)

/-- The permute KAT initial state: `a`/`idx` populated, rest zero. -/
def permInit : TileState 4 32 :=
  { regs := fun r => if r = "a" then permA else if r = "idx" then permIdx else fun _ => 0 }

/-- **`permxv` reverses a 4-lane tile** when `idx = [3,2,1,0]`: the output lanes
    are `[40, 30, 20, 10]` — the gather reads `a` in reverse, as an NTT butterfly
    / MDS shuffle would. -/
theorem permxv_reverse_kat :
    let o := (runTileBlock permInit [.permxv "d" "idx" "a"]).get "d"
    (o 0 = 40) ∧ (o 1 = 30) ∧ (o 2 = 20) ∧ (o 3 = 10) := by native_decide

/-! ### 2b. `bcast` (splat) and `hadd` (horizontal reduce) denotations

`bcast`/`hadd` are the other two cross-tile (lane-moving) ops — the images of
`cuda_tile.{broadcast,reduce}` in NVIDIA's tile dialect
(source: https://github.com/NVIDIA/cuda-tile, `Dialect/CudaTile/IR/Ops.td`).
Like `permxv` they move data across lanes rather than acting elementwise, but
both are still **pure functions of the lane carrier** `Fin n → BitVec w`, so
their denotation ties are the same `funext`/`simp` shape as `permxv_denote` —
no memory-consistency model is needed (that enters only with async copy /
barrier, which this model does not have). These complete the cross-tile op denotation set
begun by `permxv_denote`. -/

/-- **`bcast` denotation (the defining splat property).** After `[.bcast d a k]`
    *every* lane of `d` holds the single source lane `a[k mod n]`, so all output
    lanes are equal. (The broadcast analogue of `permxv_denote`.) -/
theorem bcast_denote {n w : Nat} (s : TileState n w) (d a : String) (k : Nat)
    (i j : Fin n) :
    (runTileBlock s [.bcast d a k]).get d i
      = (runTileBlock s [.bcast d a k]).get d j := by
  simp [runTileBlock, evalTileOp, TileState.set, TileState.get]

/-- **`hadd` denotation.** After `[.hadd d a]`, every lane of `d` holds the full
    horizontal sum `Σ_j a[j]` of the input tile (the reduce-and-broadcast the
    `cuda_tile.reduce` op performs). -/
theorem hadd_denote {n w : Nat} (s : TileState n w) (d a : String) (i : Fin n) :
    (runTileBlock s [.hadd d a]).get d i
      = (List.finRange n).foldl (fun acc j => acc + s.get a j) 0 := by
  simp [runTileBlock, evalTileOp, TileState.set, TileState.get]

/-- A `Tile 4 32` input `a = [10, 20, 30, 40]` for the splat / reduce KATs. -/
def bcA : Tile 4 32 := fun i => (#[10, 20, 30, 40].getD i.val 0 : BitVec 32)

/-- The splat / reduce KAT initial state: `a` populated, rest zero. -/
def bcInit : TileState 4 32 :=
  { regs := fun r => if r = "a" then bcA else fun _ => 0 }

/-- **`bcast` KAT.** Splatting lane 2 of `[10,20,30,40]` fills every lane with
    `30`. -/
theorem bcast_splat_kat :
    let o := (runTileBlock bcInit [.bcast "d" "a" 2]).get "d"
    (o 0 = 30) ∧ (o 1 = 30) ∧ (o 2 = 30) ∧ (o 3 = 30) := by native_decide

/-- **`hadd` KAT.** Reducing `[10,20,30,40]` gives `100` in every lane. -/
theorem hadd_sum_kat :
    let o := (runTileBlock bcInit [.hadd "d" "a"]).get "d"
    (o 0 = 100) ∧ (o 1 = 100) ∧ (o 2 = 100) ∧ (o 3 = 100) := by native_decide

/-! ## 3. The BabyBear Barrett `bbMul` as a tile program

`bbMulWord` is the branchless Barrett multiply over BabyBear (`p = 2013265921`,
Barrett `MU = 2290649223`), intended to compute `(a·b) mod p` for `a, b < p`;
that identity is not proved in this module. The tile program applies it to every
lane of the tile. -/

/-- The branchless BabyBear Barrett `bbMul` on one word: shift-multiply-shift
    reduce + csub. The word reference the tile program is proved to compute lane
    for lane. -/
def bbMulWord (a b : BitVec 64) : BitVec 64 :=
  let x := a * b
  let q := (((x >>> 30) * BitVec.ofNat 64 2290649223) >>> 32) * BitVec.ofNat 64 2013265921
  let x := x - q
  let o := x - BitVec.ofNat 64 2013265921
  let m := BitVec.ofNat 64 0 - (o >>> 63)
  let m := m &&& BitVec.ofNat 64 2013265921
  o + m

/-- The `bbMul` tile program: the Barrett reduce + csub as elementwise tile ops,
    inputs in `a`/`b`, result in `o`. (Same op sequence as `bbMulWord`.) -/
def bbMulTile : List TileOp :=
  [ .const "MU" 2290649223, .const "P" 2013265921, .const "zero" 0
  , .mul "x" "a" "b", .shr "q" "x" 30, .mul "q" "q" "MU", .shr "q" "q" 32
  , .mul "q" "q" "P", .sub "x" "x" "q"
  , .sub "o" "x" "P", .shr "m" "o" 63, .sub "m" "zero" "m", .and "m" "m" "P"
  , .add "o" "o" "m" ]

/-- Initial tile state: the input tiles in `a`/`b`, everything else zero. Generic
    in the lane count `n` (BabyBear is a 64-bit field, so `w = 64`). -/
def bbMulInit {n : Nat} (a b : Tile n 64) : TileState n 64 :=
  { regs := fun r => if r = "a" then a else if r = "b" then b else fun _ => 0 }

/-! ## 4. The `bbMul` tile program computes `bbMulWord` lane-wise

Running the `bbMul` tile program on input tiles `a`, `b` computes, in `o`,
`o[i] = bbMulWord (a[i]) (b[i])` for every lane. -/

/-- **The `bbMul` tile program computes `bbMulWord` on every lane**, for a tile of
    any lane count `n`. -/
theorem bbMulTile_denote {n : Nat} (a b : Tile n 64) :
    (runTileBlock (bbMulInit a b) bbMulTile).get "o"
      = fun i => bbMulWord (a i) (b i) := by
  funext i
  simp only [bbMulTile, runTileBlock, List.foldl_cons, List.foldl_nil, evalTileOp,
    TileState.set, TileState.get, bbMulInit, bbMulWord, String.reduceEq, if_true,
    if_false]

/-! ## 5. KAT — the tile `bbMul` matches the field reference on a worked vector

On four concrete lanes the tile output equals `(a·b) mod p`, including
`7·9 = 63` (no reduce) and the high pair `(p-1)·(p-1) ≡ 1 (mod p)`. -/

/-- The KAT input tiles: `a = [7, p-1, 2, 3, …]`, `b = [9, p-1, 4, 5, …]` (8 lanes). -/
def katA : Tile 8 64 := fun i => (#[7, 2013265920, 2, 3, 0,0,0,0].getD i.val 0 : BitVec 64)
def katB : Tile 8 64 := fun i => (#[9, 2013265920, 4, 5, 0,0,0,0].getD i.val 0 : BitVec 64)

/-- **Tile `bbMul` KAT.** Lane 0 `7·9 = 63`; lane 1 `(p-1)² ≡ 1 (mod p)`; lane 2
    `2·4 = 8`; lane 3 `3·5 = 15`. On these four lanes the tile program's output
    equals `(a·b) mod p`. -/
theorem bbMulTile_kat :
    let o := (runTileBlock (bbMulInit katA katB) bbMulTile).get "o"
    (o 0 = 63) ∧ (o 1 = 1) ∧ (o 2 = 8) ∧ (o 3 = 15) := by native_decide

/-! ## 6. The lowering `regArith → Tile`

A lowering from a **source `regArith` alphabet** (`RegInstr`: `JasminBinOp`
two-address register arithmetic, constant loads and `mulhs`) into tile ops, with
a proof that it preserves the `TileState` semantics for every op and every
straight-line block. The source semantics `evalRegInstr` is defined here, lane
by lane, with the lane operation `JasminBinOp.applyLane` at width `w` (shift
counts unmasked, as in the vector shifts); no theorem in this module relates
`RegInstr` programs to `Com jasminDialect` programs or their denotation.

Unlike `bbMulTile` (a hand-written tile program proved for that one kernel), the
statement covers every `RegInstr` block. -/

/-- A source straight-line `regArith` instruction: a two-address binary op
    `dst := op(a, b)` over named registers, a constant load, or `mulhs`. The
    constructors mirror `Com jasminDialect`'s `regArith`/const ops; no theorem
    here relates the two. -/
inductive RegInstr where
  | bin (op : JasminBinOp) (dst a b : String)
  | const (dst : String) (n : Nat)
  /-- Signed high-half multiply (`mulhs`), the FIPS-203 ML-KEM NTT Montgomery
      primitive (x86 `VPMULHW` / ARM `SQDMULH` / RISC-V `vmulh.vv`). A dedicated
      arm, not a `JasminBinOp` constructor, that lowers `1:1` to
      `TileOp.mulhs`. -/
  | mulhs (dst a b : String)
  deriving DecidableEq

/-- The source per-lane semantics at shape `n×w`: each `bin` op applies
    `JasminBinOp.applyLane` to every lane; `const` broadcasts; `mulhs` takes the
    signed high half. The reference semantics the lowering preserves. -/
def evalRegInstr {n w : Nat} (s : TileState n w) : RegInstr → TileState n w
  | .bin op d a b => s.set d (fun i => op.applyLane (s.get a i) (s.get b i))
  | .const d k => s.set d (fun _ => BitVec.ofNat w k)
  | .mulhs d a b =>
      s.set d (fun i =>
        (((s.get a i).signExtend (2 * w) * (s.get b i).signExtend (2 * w)).sshiftRight w).truncate w)

/-- Run a source `regArith` block (fold of `evalRegInstr`). -/
def runRegBlock {n w : Nat} (s : TileState n w) (blk : List RegInstr) : TileState n w :=
  blk.foldl evalRegInstr s

/-- **The lowering**: each source `regArith` op to its tile op. The two-operand
    `JasminBinOp` arms map to the matching elementwise tile op; the variable
    shifts to `shll`/`shrr`; `const` to `const`. (One rule per source op.) -/
def lowerRegInstr : RegInstr → TileOp
  | .bin .add  d a b => .add d a b
  | .bin .sub  d a b => .sub d a b
  | .bin .mul  d a b => .mul d a b
  | .bin .and  d a b => .and d a b
  | .bin .or   d a b => .orr d a b
  | .bin .xor  d a b => .xorr d a b
  | .bin .andn d a b => .andn d a b
  | .bin .shl  d a b => .shll d a b
  | .bin .shr  d a b => .shrr d a b
  | .const d n => .const d n
  | .mulhs d a b => .mulhs d a b

/-- Lower a source block (map the per-op lowering). -/
def lowerRegBlock (blk : List RegInstr) : List TileOp := blk.map lowerRegInstr

/-- **Per-op correctness**: the tile semantics of a lowered op equals the source
    op's semantics — `evalTileOp ∘ lowerRegInstr = evalRegInstr`. Proved by cases
    on the op (each arm is definitionally the same per-lane `BitVec w` op). -/
theorem lowerRegInstr_denote {n w : Nat} (s : TileState n w) (i : RegInstr) :
    evalTileOp s (lowerRegInstr i) = evalRegInstr s i := by
  cases i with
  | bin op d a b => cases op <;> rfl
  | const d k => rfl
  | mulhs d a b => rfl

/-- **The lowering preserves the tile semantics for every block and every tile
    shape `(n, w)`.** Running the lowered tile program on any state computes the
    source `runRegBlock` result: `runTileBlock ∘ lowerRegBlock = runRegBlock`.
    Both sides are `TileState` semantics defined in this module; relating a
    machine vector model (ZMM, NEON, RVV) to `TileState` is the content of the
    separate bridge modules. -/
theorem lowerRegBlock_denote {n w : Nat} (s : TileState n w) (blk : List RegInstr) :
    runTileBlock s (lowerRegBlock blk) = runRegBlock s blk := by
  induction blk generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    simp only [lowerRegBlock, List.map_cons, runTileBlock, runRegBlock, List.foldl_cons]
    rw [lowerRegInstr_denote]
    exact ih (evalRegInstr s hd)

/-! ## 7. `bbMul` through the lowering

The BabyBear `bbMul` Barrett reduce, written in the source `regArith` alphabet
(`bbMulReg`), lowers through `lowerRegBlock` to a tile program whose output lane
`i` is `bbMulWord (a i) (b i)`. The proof rewrites with `lowerRegBlock_denote`
and unfolds the source run. -/

/-- `bbMul` in the source `regArith` alphabet: the same Barrett reduce + csub,
    with the shift amounts as constants and the variable-shift `regArith .shr`. -/
def bbMulReg : List RegInstr :=
  [ .const "MU" 2290649223, .const "P" 2013265921, .const "zero" 0
  , .const "c30" 30, .const "c32" 32, .const "c63" 63
  , .bin .mul "x" "a" "b", .bin .shr "q" "x" "c30", .bin .mul "q" "q" "MU"
  , .bin .shr "q" "q" "c32", .bin .mul "q" "q" "P", .bin .sub "x" "x" "q"
  , .bin .sub "o" "x" "P", .bin .shr "m" "o" "c63", .bin .sub "m" "zero" "m"
  , .bin .and "m" "m" "P", .bin .add "o" "o" "m" ]

/-- **The lowered `bbMul` tile program computes `bbMulWord` on every lane** —
    `(runTileBlock (lowerRegBlock bbMulReg)).get "o" i = bbMulWord (a i) (b i)`.
    Via `lowerRegBlock_denote` the tile run equals the source `regArith` run,
    which unfolds (`simp only`) to `bbMulWord` per lane. The statement does not
    say that `bbMulWord` is the field multiply. -/
theorem bbMulReg_lowered_denote {n : Nat} (a b : Tile n 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := by
  rw [lowerRegBlock_denote]
  funext i
  simp only [bbMulReg, runRegBlock, List.foldl_cons, List.foldl_nil, evalRegInstr,
    TileState.set, TileState.get, bbMulInit, bbMulWord, JasminBinOp.applyLane,
    String.reduceEq, if_true, if_false, BitVec.toNat_ofNat]

/-- **KAT for the lowered `bbMul`** — the worked vector of `bbMulTile_kat`,
    through the lowering: `7·9=63`, `(p-1)²≡1`, `2·4=8`, `3·5=15`. -/
theorem bbMulReg_lowered_kat :
    let o := (runTileBlock (bbMulInit katA katB) (lowerRegBlock bbMulReg)).get "o"
    (o 0 = 63) ∧ (o 1 = 1) ∧ (o 2 = 8) ∧ (o 3 = 15) := by native_decide

/-! ## 8. Instances at fixed shapes

`bbMulReg_lowered_denote` and `lowerRegBlock_denote` are stated for any lane
count, so they specialise to the ZMM (8 lanes), AVX2 (4), NEON (2) and 16-lane
shapes without a new proof. The instances below are statements about
`TileState n 64` at those shapes, not about the machine vector models. -/

/-- The ZMM shape (`Tile 8 64`). -/
example (a b : Tile 8 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := bbMulReg_lowered_denote a b

/-- The AVX2 shape (`Tile 4 64`). -/
example (a b : Tile 4 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := bbMulReg_lowered_denote a b

/-- The NEON shape (`Tile 2 64`). -/
example (a b : Tile 2 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := bbMulReg_lowered_denote a b

/-- A 16-lane tile (`Tile 16 64`). -/
example (a b : Tile 16 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := bbMulReg_lowered_denote a b

/-- `lowerRegBlock_denote` at an arbitrary shape `(n, w)`. -/
example {n w : Nat} (s : TileState n w) (blk : List RegInstr) :
    runTileBlock s (lowerRegBlock blk) = runRegBlock s blk := lowerRegBlock_denote s blk

end CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
