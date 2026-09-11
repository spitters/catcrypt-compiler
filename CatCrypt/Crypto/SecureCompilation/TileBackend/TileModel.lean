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
# Tile model — a tile-level semantics for the GPU backend (Phase 1 spike)

This is the Phase-1 skeleton of the `Com → Tile → NVIDIA Tile IR` plan.
It gives a small
**tile-level operational semantics** in Lean — the GPU analogue of `Avx512Model`'s
lane-function discipline, raised from per-lane to per-tile — against which a
`Com → Tile IR` lowering can later be proved denotation-preserving.

## Scope of THIS increment (the honest spike)

* **Models** a tile as a shaped array of `BitVec 64` lanes (`Tile`) and a tiny set
  of **elementwise** integer ops (`add`/`sub`/`mul`/`and`/`shr`/`const`) over named
  tiles — exactly the field-arithmetic `regArith` alphabet the BabyBear leaves use,
  lifted from a lane to a whole tile. `evalTileOp` is the obvious per-element
  integer op (auditable by eye, the same honest-anchor posture as the ZMM model).
* **Demonstrates** the verifiable core: the BabyBear Barrett `bbMul` as a tile
  program (`bbMulTile`), with `bbMulTile_denote` proving the tile semantics
  computes the field multiply on **every** lane — a mini denotation-preservation
  (the GPU analogue of `m4Block_eval` / `bignumBlock_lowering_denote`).

## What this is NOT yet (deferred, per the plan)

* **Grounded in NVIDIA/cuda-tile (the real MLIR dialect), names not yet emitted.**
  The op set here is the `CudaTile` integer-arithmetic subset
  (`github.com/NVIDIA/cuda-tile`, `Dialect/CudaTile/IR/Ops.td`): our `add`/`sub`/
  `mul`/`and`/`shr`/`const` are `cuda_tile.{addi,subi,muli,andi,shli/shrui,
  constant}`, all "Element-wise integer" ops, over the tile type
  `!cuda_tile.tile<8xi64>` (`Types.td`: shape × element, power-of-two dims). The
  cross-tile ops we will need next (`cuda_tile.{permute,reduce,broadcast,iota}`,
  and `mmaf` for MSM/tensor-core) are named there too. This file fixes the
  *semantics*; the `Com → cuda_tile` MLIR emit is Phase 3.
* **No memory-consistency model.** The elementwise core touches no cross-tile
  reduction/barrier, so spec §7 (Memory Model) is not exercised. It enters only
  with the reduction/permute ops (NTT/MDS/MSM, Phase 4b+) and is the genuinely new
  semantics work the plan scopes there.
* **No emit + no execution.** This is the semantics; the `Com → Tile IR` emitter
  and bytecode are Phase 3/4. (The thread-level NVPTX PoC `ComToNvptx` already
  proved the low-road emission path to clang-validated PTX.)
-/

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

set_option autoImplicit false

/-! ## 1. Tiles and tile state — the shape-generic SIMD lane model

A tile is `n` lanes of `BitVec w` — the **shape-polymorphic** lane abstraction
(`cuda_tile.tile<n × w>`). This is the unifying lane model the fixed-shape vector
backends are instances of: ZMM is `Tile 8 64`, AVX2 `Tile 4 64`, NEON `Tile 2 64`,
a wide GPU tile `Tile n w`. The tile state is a register file of named tiles
(mirrors `Avx512Model`'s `ZState`, which is exactly `Tile 8 64`). Proving the
lowering keystone over arbitrary `(n, w)` (§6) gives every SIMD width one proof. -/

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

Each op is the obvious per-element integer operation over `BitVec 64`. `shr`
carries an immediate; `const` is a lane-uniform broadcast. (The Tile IR spec §8
mnemonics are reconciled in Phase 0; the meaning is fixed here.) -/

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
    sum. -/
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
  deriving Repr, DecidableEq

/-- The per-element semantics of one tile op at shape `n×w` (each a per-lane
    `BitVec w` op, matching `JasminBinOp.apply` for the two-operand arms). -/
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
barrier, deferred to Phase 4b). These complete the cross-tile op denotation set
begun by `permxv_denote`.

This increment was prompted by evaluating NVlabs' `cuda-oxide`
(source: https://github.com/NVlabs/cuda-oxide): that compiler reaches the same
GPU ops through hand-written Rust intrinsics lowered via Pliron → LLVM → PTX;
here we instead pin the `cuda_tile` op *semantics* in Lean, so the emitted tile
IR has a denotation to be proved against rather than a trusted intrinsic. -/

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

`bbMulWord a b = (a·b) mod p` over BabyBear (`p = 2013265921`, Barrett
`MU = 2290649223`), branchless — the *same* word arithmetic the x86/ARM/ZMM field
leaves compute. The tile program applies it to every lane of the tile. -/

/-- The branchless BabyBear Barrett `bbMul` on one word (the reference the tile
    program must compute, lane for lane): shift-multiply-shift reduce + csub. -/
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

/-! ## 4. The denotation theorem (the Phase-1 keystone)

Running the `bbMul` tile program on input tiles `a`, `b` computes, in `o`, the
BabyBear `bbMul` of every lane — `o[i] = bbMulWord (a[i]) (b[i])`. This is the
tile-level denotation-preservation (the GPU analogue of `m4Block_eval`): the tile
semantics realises the field op the source program denotes, for the whole tile. -/

/-- **The `bbMul` tile program computes the field multiply on every lane** — for
    a tile of any lane count `n` (one proof; ZMM/AVX2/NEON are `n = 8/4/2`). -/
theorem bbMulTile_denote {n : Nat} (a b : Tile n 64) :
    (runTileBlock (bbMulInit a b) bbMulTile).get "o"
      = fun i => bbMulWord (a i) (b i) := by
  funext i
  simp only [bbMulTile, runTileBlock, List.foldl_cons, List.foldl_nil, evalTileOp,
    TileState.set, TileState.get, bbMulInit, bbMulWord, String.reduceEq, if_true,
    if_false]

/-! ## 5. KAT — the tile `bbMul` matches the field reference on a worked vector

`bbMulWord` on concrete BabyBear residues equals `(a·b) mod p`. Two lanes:
`7·9 = 63` (no reduce), and a high pair `(p-1)·(p-1) ≡ 1 (mod p)`. -/

/-- The KAT input tiles: `a = [7, p-1, 2, 3, …]`, `b = [9, p-1, 4, 5, …]` (8 lanes). -/
def katA : Tile 8 64 := fun i => (#[7, 2013265920, 2, 3, 0,0,0,0].getD i.val 0 : BitVec 64)
def katB : Tile 8 64 := fun i => (#[9, 2013265920, 4, 5, 0,0,0,0].getD i.val 0 : BitVec 64)

/-- **Tile `bbMul` KAT.** Lane 0 `7·9 = 63`; lane 1 `(p-1)² ≡ 1 (mod p)`; lane 2
    `2·4 = 8`; lane 3 `3·5 = 15` — the tile program's output equals `(a·b) mod p`
    on each lane, byte-identical to the BabyBear field multiply. -/
theorem bbMulTile_kat :
    let o := (runTileBlock (bbMulInit katA katB) bbMulTile).get "o"
    (o 0 = 63) ∧ (o 1 = 1) ∧ (o 2 = 8) ∧ (o 3 = 15) := by native_decide

/-! ## 6. The verified lowering `regArith → Tile` (the GPU keystone)

This is the GPU analogue of `avx512Block_lowering_denote` / `lowerLinstrR`: a
lowering from the **source `regArith` alphabet** (`JasminBinOp`, the two-address
register arithmetic the x86/ARM/ZMM field leaves are emitted from) into tile ops,
proved **denotation-preserving for every op and every straight-line block**. The
source semantics is `JasminBinOp.apply` at width 64 (the same word op the source
`Com jasminDialect` denotes); the lowering carries it lane-for-lane onto a tile.

Unlike `bbMulTile` (a hand-written tile program proved for that one kernel), this
proves the *lowering itself* correct — so any `regArith` straight-line kernel
(`bbMul`, the NTT/Merkle/FRI leaves, …) lowers to a tile program with the same
denotation, by instantiation, with no per-kernel proof. -/

/-- A source straight-line `regArith` instruction: a two-address binary op
    `dst := op(a, b)` over named registers, or a constant load. This is the
    elementwise (per-lane) image of `Com jasminDialect`'s `regArith`/const ops. -/
inductive RegInstr where
  | bin (op : JasminBinOp) (dst a b : String)
  | const (dst : String) (n : Nat)
  /-- Signed high-half multiply (`mulhs`), the FIPS-203 ML-KEM NTT Montgomery
      primitive (x86 `VPMULHW` / ARM `SQDMULH` / RISC-V `vmulh.vv`). Kept a
      dedicated arm rather than a `JasminBinOp` constructor: `JasminBinOp` is
      matched exhaustively across ~13 dialect/optimizer files, so the surgical
      route is a `RegInstr`/`TileOp` arm that lowers `1:1` to `TileOp.mulhs`. -/
  | mulhs (dst a b : String)
  deriving DecidableEq

/-- The source per-lane semantics at shape `n×w`: each `bin` op applies
    `JasminBinOp.apply` to every lane; `const` broadcasts. (The reference the
    lowering must preserve — the meaning a `regArith` `Com` program denotes,
    lifted to a tile.) -/
def evalRegInstr {n w : Nat} (s : TileState n w) : RegInstr → TileState n w
  | .bin op d a b => s.set d (fun i => op.apply (s.get a i) (s.get b i))
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
    on the op (each arm is definitionally the same per-lane `BitVec 64` op). -/
theorem lowerRegInstr_denote {n w : Nat} (s : TileState n w) (i : RegInstr) :
    evalTileOp s (lowerRegInstr i) = evalRegInstr s i := by
  cases i with
  | bin op d a b => cases op <;> rfl
  | const d k => rfl
  | mulhs d a b => rfl

/-- **The keystone — the lowering is denotation-preserving for every block AND
    every tile shape `(n, w)`.** Running the lowered tile program on any state
    computes exactly the source `regArith` block's result. The GPU analogue of
    `avx512Block_lowering_denote`, but *shape-generic*: `runTileBlock ∘
    lowerRegBlock = runRegBlock`. ZMM (`n=8, w=64`), AVX2 (`n=4`), NEON (`n=2`),
    and any GPU tile are instances of THIS ONE theorem — the per-backend lane
    models collapse to one proof. -/
theorem lowerRegBlock_denote {n w : Nat} (s : TileState n w) (blk : List RegInstr) :
    runTileBlock s (lowerRegBlock blk) = runRegBlock s blk := by
  induction blk generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    simp only [lowerRegBlock, List.map_cons, runTileBlock, runRegBlock, List.foldl_cons]
    rw [lowerRegInstr_denote]
    exact ih (evalRegInstr s hd)

/-! ## 7. `bbMul` as an instance of the verified lowering

The BabyBear `bbMul` Barrett reduce, written in the **source** `regArith` alphabet
(`bbMulReg`), lowers — via the verified `lowerRegBlock` — to a tile program whose
denotation is the field multiply on every lane. The correctness is now a
*corollary of the lowering keystone* + the source-level field identity, not a
hand proof about a hand-written tile program. -/

/-- `bbMul` in the source `regArith` alphabet: the same Barrett reduce + csub,
    with the shift amounts as constants and the variable-shift `regArith .shr`. -/
def bbMulReg : List RegInstr :=
  [ .const "MU" 2290649223, .const "P" 2013265921, .const "zero" 0
  , .const "c30" 30, .const "c32" 32, .const "c63" 63
  , .bin .mul "x" "a" "b", .bin .shr "q" "x" "c30", .bin .mul "q" "q" "MU"
  , .bin .shr "q" "q" "c32", .bin .mul "q" "q" "P", .bin .sub "x" "x" "q"
  , .bin .sub "o" "x" "P", .bin .shr "m" "o" "c63", .bin .sub "m" "zero" "m"
  , .bin .and "m" "m" "P", .bin .add "o" "o" "m" ]

/-- **The lowered `bbMul` tile program computes the field multiply on every lane**
    — `(runTileBlock (lowerRegBlock bbMulReg)).get "o" i = bbMulWord (a i) (b i)`.
    Via `lowerRegBlock_denote` the tile run equals the source `regArith` run; the
    rest is the source-level Barrett identity (`native_decide`-free `rfl` chain on
    the per-lane words). This ties the GPU lowering to the BabyBear field op. -/
theorem bbMulReg_lowered_denote {n : Nat} (a b : Tile n 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := by
  rw [lowerRegBlock_denote]
  funext i
  simp only [bbMulReg, runRegBlock, List.foldl_cons, List.foldl_nil, evalRegInstr,
    TileState.set, TileState.get, bbMulInit, bbMulWord, JasminBinOp.apply,
    String.reduceEq, if_true, if_false, BitVec.toNat_ofNat]

/-- **KAT for the lowered `bbMul`** — same worked vector as `bbMulTile_kat`, now
    through the verified lowering: `7·9=63`, `(p-1)²≡1`, `2·4=8`, `3·5=15`. -/
theorem bbMulReg_lowered_kat :
    let o := (runTileBlock (bbMulInit katA katB) (lowerRegBlock bbMulReg)).get "o"
    (o 0 = 63) ∧ (o 1 = 1) ∧ (o 2 = 8) ∧ (o 3 = 15) := by native_decide

/-! ## 8. The consolidation: one lowering proof, every SIMD width

The whole point of the shape-generic keystone — the *same* verified lowering and
the *same* `bbMul` correctness specialise to every fixed-shape vector backend with
**no new proof**. ZMM (8 lanes), AVX2 (4), NEON (2), and a wide GPU tile (16) are
all instances of `bbMulReg_lowered_denote` / `lowerRegBlock_denote`. This is the
per-backend lane models (`Avx512Model`'s `ZState = Tile 8 64`, an AVX2 `Tile 4 64`,
a NEON `Tile 2 64`) collapsing onto one parametric proof. -/

/-- ZMM (`Tile 8 64`) — the shape of `Avx512Model.ZState`. -/
example (a b : Tile 8 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := bbMulReg_lowered_denote a b

/-- AVX2 (`Tile 4 64`) — same lowering, no new proof. -/
example (a b : Tile 4 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := bbMulReg_lowered_denote a b

/-- NEON (`Tile 2 64`) — same lowering, no new proof. -/
example (a b : Tile 2 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := bbMulReg_lowered_denote a b

/-- A wide GPU tile (`Tile 16 64`) — same lowering, no new proof. -/
example (a b : Tile 16 64) :
    (runTileBlock (bbMulInit a b) (lowerRegBlock bbMulReg)).get "o"
      = fun i => bbMulWord (a i) (b i) := bbMulReg_lowered_denote a b

/-- And the lowering keystone itself, at an arbitrary shape — every `regArith`
    straight-line block lowers correctly at *any* lane count and width. -/
example {n w : Nat} (s : TileState n w) (blk : List RegInstr) :
    runTileBlock s (lowerRegBlock blk) = runRegBlock s blk := lowerRegBlock_denote s blk

end CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
