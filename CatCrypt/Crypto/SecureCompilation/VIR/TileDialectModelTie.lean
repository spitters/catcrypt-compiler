/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel

/-!
# Tying the tile `Com` dialect to the operational `TileModel`

`TileDialect.lean` makes "tile" a first-class `Com` dialect (`tileDialect`): a
value is a lane function `Fin n → BitVec w` and the single compute op
`tileBin op n w` is the elementwise SIMT lane map `fun i => op.apply (a i) (b i)`.
`TileModel.lean` gives the *operational* tile semantics (`evalTileOp`,
`runRegBlock`/`runTileBlock`) and the verified-lowering keystone
`lowerRegBlock_denote : runTileBlock ∘ lowerRegBlock = runRegBlock`.

This file is the **denotation keystone** connecting the two: it proves that the
`tileDialect` denotation of a `tileBin op` coincides, lane for lane, with the
operational model's per-lane semantics. Concretely:

* `tileBin_denote_eq_apply` — the `Com`-dialect op denotes to the bare per-lane
  function `fun i => op.apply (a i) (b i)` (the `tileBinApply` carrier).
* `tileBin_eq_evalTileOp` — for every two-operand `JasminBinOp`, that lane
  function is *the same function* the matching operational `evalTileOp` arm
  writes (e.g. `.add` writes `fun i => a i + b i = fun i => op.apply (a i) (b i)`).
  This makes the `Com`-dialect tile binop and the operational tile binop
  provably one and the same function — so the verified
  `lowerRegBlock_denote` keystone (stated over the operational model)
  transfers to the `Com` dialect.
* a smoke `example` running a one-op `Com tileDialect` add and showing its
  `Com.denote` equals running the corresponding `RegInstr.bin .add` through the
  operational `runRegBlock`/`evalRegInstr` path.

There is no `sorry` and no new axiom; the ties reduce to `rfl`/`funext`+`cases`
because both sides ultimately compute the bare `BitVec w` lane op.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.TileDialectModelTie

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
  (TileState evalTileOp evalRegInstr runRegBlock RegInstr)

/-! ## 1. The `Com`-dialect op denotes to the bare per-lane function

The `tileDialect`'s `DialectDenote` for `tileBin op n w` is exactly
`tileBinApply op`, which by definition is the SIMT lane map
`fun i => op.apply (a i) (b i)`. We state this as the named tie. -/

/-- **The `tileDialect` denotation of `tileBin op` is the per-lane `apply`.**
    Feeding the op's denotation the operand tiles `a b : Fin n → BitVec w`
    yields the bare lane function `fun i => op.apply (a i) (b i)` — i.e. the
    `Com`-dialect op computes the per-lane `JasminBinOp.apply`. -/
theorem tileBin_denote_eq_apply {n w : Nat} (op : JasminBinOp)
    (a b : Fin n → BitVec w) :
    (tileDenote.denote (TileOp.tileBin op n w)
        (.cons a (.cons b .nil)))
      = (fun i => op.apply (a i) (b i)) :=
  rfl

/-! ## 2. The dialect↔model tie: same function as `evalTileOp`'s arm

For each two-operand `JasminBinOp`, the dialect's per-lane function
`fun i => op.apply (a i) (b i)` equals the lane function the operational
`evalTileOp` writes for the matching tile op (`.add`/`.sub`/…). Both sides
reduce to the bare `BitVec w` op, so `cases op <;> rfl` closes it after
`funext`. -/

/-- The operational tile op `evalTileOp` writes for source `JasminBinOp` `op`
    (the same table as `TileModel.lowerRegInstr`, inlined here so the tie is
    self-contained). -/
def toTileOp (op : JasminBinOp) (d a b : String) :
    CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileOp :=
  match op with
  | .add  => .add d a b
  | .sub  => .sub d a b
  | .mul  => .mul d a b
  | .and  => .and d a b
  | .or   => .orr d a b
  | .xor  => .xorr d a b
  | .andn => .andn d a b
  | .shl  => .shll d a b
  | .shr  => .shrr d a b

/-- **The dialect↔model keystone.** For any two-operand `JasminBinOp` `op`, the
    `Com`-dialect tile op's per-lane function `fun i => op.apply (a i) (b i)`
    equals the lane function the operational `evalTileOp (toTileOp op d a b)`
    writes into `d`, when `a`/`b` are the named operand tiles. Both sides are the
    bare per-lane `BitVec w` op, so they are the SAME function — the `Com`-dialect
    binop and the operational binop coincide. -/
theorem tileBin_eq_evalTileOp {n w : Nat}
    (op : JasminBinOp) (s : TileState n w) (d a b : String) :
    (evalTileOp s (toTileOp op d a b)).get d
      = (fun i => op.apply (s.get a i) (s.get b i)) := by
  cases op <;>
    (funext i
     simp only [toTileOp, evalTileOp, JasminBinOp.apply,
       CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileState.set,
       CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileState.get,
       if_true])

/-- **Direct form: the `Com`-dialect denotation equals the operational lane
    function.** The `tileDenote` of `tileBin op` on `a`/`b` equals the lane
    function `evalTileOp` writes — the two paths produce one function. -/
theorem tileBin_denote_eq_evalTileOp {n w : Nat}
    (op : JasminBinOp) (s : TileState n w) (d a b : String) :
    (tileDenote.denote (TileOp.tileBin op n w)
        (.cons (s.get a) (.cons (s.get b) .nil)))
      = (evalTileOp s (toTileOp op d a b)).get d := by
  rw [tileBin_denote_eq_apply, tileBin_eq_evalTileOp]

/-! ## 3. Smoke: a one-op `Com tileDialect` add ties to the operational path

We take the `smokeProg` add from `TileDialect.lean` (a single `tileBin .add`)
on concrete tiles, and show its `Com.denote` equals running the corresponding
`RegInstr.bin .add "d" "a" "b"` through the operational `runRegBlock` /
`evalRegInstr` and reading lane-by-lane. This ties a concrete `Com` program to
the operational verified path. -/

/-- Operational initial state holding `tileA` in `"a"` and `tileB` in `"b"`. -/
def smokeInit : TileState 4 8 :=
  { regs := fun r => if r = "a" then tileA else if r = "b" then tileB else fun _ => 0 }

/-- **Smoke tie.** The `Com tileDialect` add (`smokeProg`) on `⟨tileA, tileB⟩`
    denotes to the very function the operational `runRegBlock [.bin .add "d" "a" "b"]`
    writes into `"d"`. The `Com` IR and the operational model agree. -/
example :
    smokeProg.denote (.cons tileA (.cons tileB .nil))
      = (runRegBlock smokeInit [RegInstr.bin .add "d" "a" "b"]).get "d" := by
  rfl

/-- Pointwise sanity (lane sums `10, 12, 14, 16`), through the operational path. -/
example :
    ((runRegBlock smokeInit [RegInstr.bin .add "d" "a" "b"]).get "d" 0 = (10 : BitVec 8)) ∧
    ((runRegBlock smokeInit [RegInstr.bin .add "d" "a" "b"]).get "d" 3 = (16 : BitVec 8)) := by
  decide

/-! ## 4. Cross-tile op ties: `permute` / `broadcast` / `reduce` ↔ model

The three cross-tile dialect ops (`tilePermute` / `tileBroadcast` /
`tileReduce`, lifted from `cuda_tile.{permute,broadcast,reduce}` — source:
https://github.com/NVIDIA/cuda-tile) denote to the very lane functions the
operational model's `evalTileOp` writes for `.permxv` / `.bcast` / `.hadd`.
Same `rfl`/`funext` shape as the binop ties: both sides compute the bare
gather / splat / reduce on the lane carrier, with no memory-consistency model
in play (these ops move data across lanes but perform no async copy / barrier).
This makes the cross-tile ops first-class `Com tileDialect` nodes whose
denotation is provably the operational tile semantics. -/

/-- `tilePermute`'s dialect denotation is the bare gather `tilePermuteApply`. -/
theorem tilePermute_denote_eq_apply {n w : Nat} (idx a : Fin n → BitVec w) :
    (tileDenote.denote (TileOp.tilePermute n w) (.cons idx (.cons a .nil)))
      = tilePermuteApply idx a :=
  rfl

/-- **`tilePermute` ↔ model `permxv`.** The dialect gather equals the lane
    function the operational `evalTileOp (.permxv d idx a)` writes into `d`. -/
theorem tilePermute_denote_eq_evalTileOp {n w : Nat}
    (s : TileState n w) (d idx a : String) :
    (tileDenote.denote (TileOp.tilePermute n w)
        (.cons (s.get idx) (.cons (s.get a) .nil)))
      = (evalTileOp s (.permxv d idx a)).get d := by
  rw [tilePermute_denote_eq_apply]
  funext i
  simp [tilePermuteApply, evalTileOp,
    CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileState.set,
    CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileState.get]

/-- `tileBroadcast`'s dialect denotation is the bare splat `tileBroadcastApply`. -/
theorem tileBroadcast_denote_eq_apply {n w : Nat} (lane : Nat)
    (a : Fin n → BitVec w) :
    (tileDenote.denote (TileOp.tileBroadcast n w lane) (.cons a .nil))
      = tileBroadcastApply lane a :=
  rfl

/-- **`tileBroadcast` ↔ model `bcast`.** -/
theorem tileBroadcast_denote_eq_evalTileOp {n w : Nat}
    (s : TileState n w) (d a : String) (lane : Nat) :
    (tileDenote.denote (TileOp.tileBroadcast n w lane) (.cons (s.get a) .nil))
      = (evalTileOp s (.bcast d a lane)).get d := by
  rw [tileBroadcast_denote_eq_apply]
  funext i
  simp [tileBroadcastApply, evalTileOp,
    CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileState.set,
    CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileState.get]

/-- `tileReduce`'s dialect denotation is the bare reduce `tileReduceApply`. -/
theorem tileReduce_denote_eq_apply {n w : Nat} (a : Fin n → BitVec w) :
    (tileDenote.denote (TileOp.tileReduce n w) (.cons a .nil))
      = tileReduceApply a :=
  rfl

/-- **`tileReduce` ↔ model `hadd`.** -/
theorem tileReduce_denote_eq_evalTileOp {n w : Nat}
    (s : TileState n w) (d a : String) :
    (tileDenote.denote (TileOp.tileReduce n w) (.cons (s.get a) .nil))
      = (evalTileOp s (.hadd d a)).get d := by
  rw [tileReduce_denote_eq_apply]
  funext i
  simp [tileReduceApply, evalTileOp,
    CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileState.set,
    CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel.TileState.get]

end CatCrypt.Crypto.SecureCompilation.VIR.TileDialectModelTie
