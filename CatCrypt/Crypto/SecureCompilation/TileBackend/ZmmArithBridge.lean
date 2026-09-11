/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridge

/-!
# The AVX-512 ZMM packed core is an instance of the shape-generic tile lowering

This is the `Tile 8 64` analogue of `VectorBackendBridge.lean` (which does the
three 128-bit backends at `Tile 4 32`). The shape-polymorphic `Tile n w` lane
model (`TileModel`) is the *one* SIMD lane abstraction the per-target backends
consolidate onto; here we make that concrete for the x86 **AVX-512 ZMM**
packed-lane semantics carried by the unified `Com jasminDialect` functions
(`zmmLane`/`zmmOfLanes`/`zmmPackQ` and the cross-lane gather `zmmPermXvar`), over
the packed `BitVec 512` carrier — **not** the bespoke per-ISA `Avx512Model`
register machine. Each ZMM packed-arithmetic and cross-lane-permute operation,
viewed lane-by-lane as a `Tile 8 64`, is exactly the shape-generic verified
lowering `evalTileOp ∘ lowerRegInstr` (resp. `evalTileOp`'s `.permxv` arm) of the
matching `regArith` op. So the AVX-512 ZMM packed core IS an instance of
`TileModel.lowerRegInstr_denote`, by these bridge theorems.

The packed `BitVec 512` carrier is not defeq to the lane-function `Tile 8 64`,
so the bridges cross the gap via the single packed↔lane round-trip lemma
`zmmOfLanes_zmmLane` (re-proved locally to keep this module import-light) and the
packed-to-tile view `zmmBvToTile` — exactly as the `TileS16HighMul` x86 leg
crosses the `BitVec 128 ↔ Tile 8 16` gap with `vpmulhw16W_lane`.

The arithmetic bridge (`zmmPackQ_is_tile_lowering`) covers the elementwise
two-operand alphabet (`vpaddq`/`vpsubq`/`vpandq`/`vpxorq`/`vporq` and the full
64-bit multiply `vpmullq`, i.e. the `JasminBinOp` arms). The cross-lane bridge
(`zmmPermXvar_is_tile_permxv`) covers the variable qword permute.

`zmmPermXvar` is a **denotation-level semantics function** (a plain
`BitVec 512 → BitVec 512` gather), not a `Com`-op constructor: a dedicated 512-bit
cross-lane-permute op constructor + emit is a deferred follow-up (no current
kernel consumer), so only the cross-ISA faithfulness against the shape-generic
tile `permxv` is ported here.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridge

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
  (JasminBinOp zmmLane zmmOfLanes zmmPackQ)

set_option autoImplicit false

/-! ## 0. Packed↔lane round-trip (re-proved locally)

`zmmOfLanes_zmmLane` is also proved in `Poseidon2Avx512Jasmin.lean`, but that
module is import-heavy (the full jasmin print/emit chain); to keep this bridge
light we re-prove the exact lemma here from `BitVec.eq_of_getLsbD_eq` and the
`getLsbD`-of-`extractLsb'`/`append` lemmas. The `VectorBackendBridge` import (the
same one the `TileS16HighMul` template carries) supplies `fin_cases`. -/

/-- Reading lane `k` of an assembled ZMM register recovers the `k`-th lane
    function value: `zmmLane (zmmOfLanes f) k = f k`. The little-endian
    concatenation places `f k` at bits `[64k, 64k+64)`, which is exactly what
    `zmmLane` extracts. -/
theorem zmmOfLanes_zmmLane (f : Fin 8 → BitVec 64) (k : Fin 8) :
    zmmLane (zmmOfLanes f) k = f k := by
  fin_cases k <;>
    · apply BitVec.eq_of_getLsbD_eq
      intro i
      by_cases hi : i < 64
      · simp only [zmmLane, zmmOfLanes, Fin.isValue, BitVec.getLsbD_extractLsb',
          BitVec.getLsbD_append, decide_eq_true_eq.mpr hi, Bool.true_and,
          Nat.mul_comm, Nat.zero_mul, Nat.zero_add, Nat.add_sub_cancel_left]
        split_ifs <;>
          (intro _
           first
             | omega
             | exact congrArg _ (by omega : _ = i))
      · intro h
        exact absurd h hi

/-! ## 1. The lane types coincide and the packed-to-tile view -/

/-- The x86 AVX-512 ZMM packed register, viewed as the `8×64` tile by reading each
    64-bit lane. The packed↔lane bridge between the unified op's carrier
    (`BitVec 512`) and the shape-generic tile carrier the lowering targets — the
    `Tile 8 64` analogue of `TileS16HighMul`'s `vpmulhw16BvToTile`. -/
def zmmBvToTile (v : BitVec 512) : Tile 8 64 := fun k => zmmLane v k

/-! ## 2. ARITHMETIC bridge — ZMM packed binop is the `regArith` tile lowering

The elementwise two-operand alphabet (`vpaddq`/`vpsubq`/`vpandq`/`vpxorq`/`vporq`
and the full 64-bit multiply `vpmullq`) is the unified-dialect packed binop
`zmmPackQ bop`. Viewed lane-by-lane it equals `evalTileOp` of the lowered
`regArith` op, at shape `8×64`. So the ZMM packed ALU is an instance of
`lowerRegInstr_denote`, not a separate semantics. -/

/-- **AVX-512 ZMM packed arithmetic is the shape-generic tile lowering.** For
    every `JasminBinOp`, viewing the packed `zmmPackQ bop a b` as a `Tile 8 64`
    equals `evalTileOp` of the lowered `RegInstr.bin bop` over the tile state whose
    `"a"`/`"b"` registers carry the lane views of `a`/`b`. This is the
    equal-strength replacement for the old `zinst_is_tile_lowering`, now riding the
    unified `zmmPackQ` semantics over the packed `BitVec 512` carrier rather than
    the bespoke `Avx512Model` machine. -/
theorem zmmPackQ_is_tile_lowering (bop : JasminBinOp) (a b : BitVec 512) :
    zmmBvToTile (zmmPackQ bop a b)
      = (evalTileOp ⟨fun nm => if nm = "b" then zmmBvToTile b else zmmBvToTile a⟩
           (lowerRegInstr (.bin bop "d" "a" "b"))).get "d" := by
  funext k
  rw [lowerRegInstr_denote]
  simp only [zmmBvToTile, zmmPackQ, TileState.get, TileState.set, evalRegInstr,
    String.reduceEq, if_true, if_false, zmmOfLanes_zmmLane]

/-! ## 3. CROSS-LANE bridge — ZMM variable qword permute is the tile `permxv`

The *cross-lane* gather is the other structural family. The x86 ZMM variable qword
permute (`vpermxvarq`) and the tile model's `permxv` are the same data-dependent
whole-lane gather: dst lane `i` reads src lane `(idx[i]).toNat % 8` of `a` in
both models. We express the ZMM permute as a unified-dialect **semantics
function** `zmmPermXvar` over the packed carrier (mirroring the bespoke
`lanePermXvar`/`permXvarSel`), then bridge it to the tile `permxv` arm at `n = 8`.
The two selectors are literally equal (the `% 8` is the hardware low-3-bit
selector mask, which is exactly `mod n` at `n = 8`); only the `Fin 8` source-index
*proof terms* differ, and those are irrelevant. -/

/-- The AVX-512 ZMM variable cross-lane qword permute, as a unified-dialect
    semantics function over the packed `BitVec 512` carrier: dst lane `i` reads src
    lane `(idx[i]).toNat % 8` of `a`. Mirrors the bespoke `Avx512Model`
    `lanePermXvar`/`permXvarSel` gather (`vpermxvarq`), but as a plain
    `BitVec 512 → BitVec 512` function — a Com-op constructor + emit for the
    512-bit cross-lane permute is a deferred follow-up (no current kernel
    consumer). -/
def zmmPermXvar (idx a : BitVec 512) : BitVec 512 :=
  zmmOfLanes (fun i => zmmLane a ⟨(zmmLane idx i).toNat % 8, Nat.mod_lt _ (by decide)⟩)

/-- **AVX-512 ZMM variable cross-lane permute is the tile model's `permxv`.**
    Viewing the packed `zmmPermXvar idx a` as a `Tile 8 64` equals `evalTileOp …
    (.permxv "d" "idx" "a")`: both are the whole-lane data-dependent gather where
    dst lane `i` reads src lane `(idx[i]).toNat % 8` of `a`. This is the
    equal-strength replacement for the old `zpermxv_is_tile_permxv`, now riding the
    unified `zmmPermXvar` semantics over the packed `BitVec 512` carrier. Together
    with `zmmPackQ_is_tile_lowering` it shows the ZMM bank's elementwise *and*
    lane-moving cores are both instances of the shape-generic tile semantics. -/
theorem zmmPermXvar_is_tile_permxv (idx a : BitVec 512) :
    zmmBvToTile (zmmPermXvar idx a)
      = (evalTileOp ⟨fun nm => if nm = "idx" then zmmBvToTile idx else zmmBvToTile a⟩
           (.permxv "d" "idx" "a")).get "d" := by
  funext i
  -- both sides reduce to `zmmLane a ⟨(zmmLane idx i).toNat % 8, _⟩`; only the
  -- `Fin 8` proof terms of the source index differ (proof-irrelevant).
  simp only [zmmBvToTile, zmmPermXvar, evalTileOp, TileState.get, TileState.set,
    String.reduceEq, if_true, if_false, zmmOfLanes_zmmLane]

/-! ## 4. The consolidation, stated

Together with `TileModel.lowerRegBlock_denote` (the shape-generic keystone, proven
for every `(n, w)`), these bridges mean: the AVX-512 ZMM packed lane semantics —
and the `Tile 4 32` AVX2 / NEON / RVV backends of `VectorBackendBridge.lean`, and
the `Tile 8 16` FIPS-203 high-mul of `TileS16HighMul.lean` — are **all** the same
shape-generic verified lowering, `Tile n w` at `(8,64)`, `(4,32)`, `(8,16)`, …,
both for the elementwise arithmetic (`zmmPackQ`/`evalTileOp ∘ lowerRegInstr`) and
for the cross-lane permute (`zmmPermXvar`/`evalTileOp`'s `.permxv` arm). The
per-backend lane models are instances of one proof, not separate semantics. -/

/-- The ZMM packed arithmetic core and the cross-lane permute both lower to the
    shape-generic tile semantics: the elementwise `zmmPackQ bop` targets
    `evalTileOp (lowerRegInstr (.bin bop …))`, and the gather `zmmPermXvar` targets
    `evalTileOp`'s `.permxv` arm — both over the packed `BitVec 512` carrier
    bridged to `Tile 8 64` by `zmmBvToTile`. -/
theorem zmm_core_consolidates (bop : JasminBinOp) (a b idx : BitVec 512) :
    zmmBvToTile (zmmPackQ bop a b)
        = (evalTileOp ⟨fun nm => if nm = "b" then zmmBvToTile b else zmmBvToTile a⟩
             (lowerRegInstr (.bin bop "d" "a" "b"))).get "d" ∧
    zmmBvToTile (zmmPermXvar idx a)
        = (evalTileOp ⟨fun nm => if nm = "idx" then zmmBvToTile idx else zmmBvToTile a⟩
             (.permxv "d" "idx" "a")).get "d" :=
  ⟨zmmPackQ_is_tile_lowering bop a b, zmmPermXvar_is_tile_permxv idx a⟩

end CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridge
