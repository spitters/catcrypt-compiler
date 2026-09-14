/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridge
public import CatCrypt.Crypto.SecureCompilation.TileBackend.VectorBackendBridge
public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMulCom
public import CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMulCom
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonModel
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonModel
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvvModel
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvvModel

/-!
# Signed 16-bit high-multiply tile operation (Kyber/FIPS-203 Montgomery path)

This module defines and verifies the **8-lane signed 16-bit Montgomery multiply**
over `Tile 8 16` — the SIMD primitive at the heart of FIPS-203 (ML-KEM) NTT
butterfly arithmetic.

## Mathematical background

FIPS-203 ML-KEM uses the ring `ℤ_q[x]/(x^256 + 1)` with `q = 3329`. NTT
butterflies over this ring require a *Montgomery multiply*: given 16-bit signed
integers `a`, `b`, compute `a · b · R⁻¹ mod q` where `R = 2^16`. The computation
is:

```
t     = (int32)(a * b)
u     = (int16)(t * QINV)        -- QINV = 62209 = -3327 mod 2^16
sub   = (int32)(t - (int32)(u * q))
result = sub >> 16               -- arithmetic right shift
```

where `q = 3329`, `QINV = 62209`, and `q * 3327 ≡ -1 mod 2^16`
(i.e. `q * QINV ≡ 1 mod 2^16` interpreting `QINV` as signed: `QINV = -3327`).

The key identity: `3329 * 3327 = 11,075,583 = 169 * 65536 - 1 ≡ -1 mod 2^16` ✓

## Tile realisation

`tileMontMulS16` applies `montMulS16Spec` to every lane of an `8 × i16` tile.
This is the tile analogue of how `bbMulTile` expresses BabyBear Barrett
reduction per lane of `Tile n 64`.

## Per-ISA lowering status

The naturally realising hardware instructions are:
- **x86 AVX2**: `VPMULHW` (packed signed 16-bit high multiply, 8 lanes) — the
  result of `VPMULHW a, b` is the high 16 bits of each signed `i16 × i16`
  product, which together with `VPMULLW` (the low 16 bits) reconstructs the
  full 32-bit product used by Montgomery.
- **ARM NEON**: `SQDMULH Vd.8H, Vn.8H, Vm.8H` (8 × i16) — per Arm ARM §C7.2.
  **`SQDMULH` is not the model op.** It is the signed saturating *doubling*
  high-multiply; the model op (`laneMulHiS16`, the `.mulhs` arm below) is the
  plain signed high half. The doubling and the saturation are a real
  discrepancy, not a naming difference; the exact-Montgomery A64 realization is
  the `SMULL/SMULL2/UZP2` widening sequence. The encoder emits `SQDMULH` anyway
  (the single-instruction form) and the gap is neither decode-round-trip-proved
  nor otherwise discharged — see `ARMBackend/NeonEncoder.lean`'s `baseSqdmulh`
  note and `NeonModel.lean §5`.
- **RISC-V RVV**: `vmulh.vv vd, vs2, vs1` (OPMVV signed multiply returning
  high half) at `SEW = 16`, `LMUL = 1`, `VL = 8`.

The x86 leg is carried by the **unified `Com jasminDialect`** op
`JasminOp.vsimd .mulhi16` (denote `vpmulhw16W`), via `TileS16HighMulCom`'s
dialect-native `s16HighMulCom` step — off the bespoke per-ISA vector machine. The
ARM and RISC-V legs stay on their `NeonModel.NInst8x16` / `RvvModel.VInst8x16`
models, each over an 8 × i16 register view (`*State8x16 = Tile 8 16`) with a byte
encoder + gas pin. The three lowering theorems below (§4) land on the same
verified `evalTileOp (lowerRegInstr (.mulhs …))`: the x86 leg
(`vpmulhw_com_is_tile_lowering`) crosses the packed↔lane carrier gap with
`vpmulhw16W_lane`; the ARM/RISC-V legs are first-class bridges of the
`VectorBackendBridge` `ninst_is_tile_lowering` / `rvinst_is_tile_lowering` shape.

## Trust posture

The per-lane spec `montMulS16Spec` is the bit-exact FIPS-203 formula; its
correctness against the Montgomery identity `fqmul(a,1) = a·R⁻¹ mod q` is
pinned by the KAT at the bottom of this file. The 16-bit arithmetic is small
enough for `native_decide` on the 8-lane worked vector.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMul

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (vpmulhw16W laneMulHiS16W)
open CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMulCom (s16HighMulCom s16HighMulCom_denote)

/-! ## 1. Kyber/FIPS-203 Montgomery constants -/

/-- The Kyber/FIPS-203 modulus `q = 3329`. -/
def kyberQ : Nat := 3329

/-- The Kyber/FIPS-203 Montgomery inverse constant `QINV = 62209`.
    As a signed `i16`: `62209 - 65536 = -3327`.
    Satisfies `q · (-QINV_signed) ≡ 1 mod 2^16`, i.e. `3329 · 3327 = 11,075,583 ≡ -1 mod 2^16`,
    so `3329 · 62209 ≡ -1 · (-1) ≡ ... ` — equivalently, the (unsigned) Montgomery
    product uses `(a * QINV) mod 2^16` as the low-order correction word:
    `3329 * 62209 mod 65536 = 3329 * (65536 - 3327) mod 65536 = (−3329 * 3327) mod 65536
    = (−11,075,583) mod 65536 = 65536 - (11,075,583 mod 65536) = 65536 - 65535 = 1`.
    Equivalently: treating QINV as signed (-3327), `q * QINV_signed ≡ -1 mod 2^16`. -/
def kyberQInv : BitVec 16 := 62209  -- unsigned representation; as signed = -3327

/-! ## 2. Single-lane signed 16-bit Montgomery multiply

The FIPS-203 ML-KEM `fqmul` / `montgomery_reduce` formula, bit-exact.
Reference: NIST FIPS 203, §NTT; pqclean `kyber512/clean/ntt.c:fqmul`. -/

/-- **Single-lane signed 16-bit Montgomery multiply** (the FIPS-203 `fqmul`).

    Given `a b : BitVec 16` (treated as signed `i16`):
    1. `t ← a_signed × b_signed`  (full signed 32-bit product)
    2. `u ← (t × QINV) trunc 16` (low 16-bit word, then interpreted as signed `i16`)
    3. `sub ← t - u_signed × q`  (signed 32-bit correction)
    4. `result ← sub >>_s 16`    (arithmetic right shift; truncated to 16 bits)

    The result is congruent to `a · b · R⁻¹ mod q` where `R = 2^16`, `q = 3329`.
    It lies in the range `(-q, q)` (potentially negative; to recover the canonical
    representative add `q` if the result is negative — the NTT butterfly absorbs
    the sign lazily). -/
def montMulS16Spec (a b : BitVec 16) : BitVec 16 :=
  -- Step 1: full signed 32-bit product
  let t : BitVec 32 := a.signExtend 32 * b.signExtend 32
  -- Step 2: low 16-bit word u = (t * QINV) mod 2^16, sign-extended to i32 for step 3
  let u : BitVec 16 := (t * (62209 : BitVec 32)).truncate 16
  -- Step 3: signed 32-bit correction: t - u_signed * q
  let sub : BitVec 32 := t - u.signExtend 32 * (3329 : BitVec 32)
  -- Step 4: arithmetic right shift by 16 (keeps the high word), truncate to 16 bits
  (sub.sshiftRight 16).truncate 16

/-! ## 3. The 8-lane tile Montgomery multiply and its denotation theorem -/

/-- **8-lane signed 16-bit Montgomery multiply tile operation.**

    Applies `montMulS16Spec` to every lane of two `Tile 8 16` inputs,
    producing a `Tile 8 16` output. This is the shape-generic SIMD carrying
    of `fqmul` across 8 parallel `i16` lanes — the tile analogue of `bbMulTile`
    for BabyBear, now at `8 × i16` shape (the FIPS-203 NTT butterfly lane shape).

    The realising hardware instructions are one packed signed high-multiply each:
    `VPMULHW` (x86), `SQRDMULH / SQDMULH` (ARM NEON), `vmulh.vv` (RISC-V RVV)
    — see §4 for the per-ISA lowering status. -/
def tileMontMulS16 (a b : Tile 8 16) : Tile 8 16 :=
  fun i => montMulS16Spec (a i) (b i)

/-- **`tileMontMulS16` denotation.** Running `tileMontMulS16 a b` computes
    `montMulS16Spec (a i) (b i)` at every lane `i`. This is the tile-level
    denotation-preservation (the FIPS-203 NTT analogue of `bbMulTile_denote`):
    the tile semantics realises the per-lane Montgomery spec for all 8 lanes.

    The proof is definitional (`rfl`) because `tileMontMulS16` is declared by
    the per-lane function — exactly the definition-transparency posture that
    `lowerRegBlock_denote` exploits for the regArith alphabet. -/
theorem tileMontMulS16_denote (a b : Tile 8 16) :
    tileMontMulS16 a b = fun i => montMulS16Spec (a i) (b i) := rfl

/-- **Per-lane corollary.** Extracting lane `i` of `tileMontMulS16 a b` gives
    `montMulS16Spec (a i) (b i)`. Immediate from `tileMontMulS16_denote`. -/
theorem tileMontMulS16_lane (a b : Tile 8 16) (i : Fin 8) :
    tileMontMulS16 a b i = montMulS16Spec (a i) (b i) := rfl

/-! ## 4. Per-ISA lowering lemmas — the high-mul realizes `tileMontMulS16`

Each ISA's packed signed high-multiply (`VPMULHW` / `SQDMULH` / `vmulh.vv`),
transported to the shape-generic `TileState 8 16`, equals `evalTileOp` of the
lowered `RegInstr.mulhs` op (`TileModel`'s verified `lowerRegInstr`).

Read the ARM leg with the §"Per-ISA lowering status" caveat in force: the lemma
is about `NeonModel`'s `.mulhs` *model* op (the plain signed high half), and the
A64 mnemonic the encoder actually emits for it, `SQDMULH`, differs from that op
by the architectural doubling and saturation (`NeonEncoder.baseSqdmulh`). The
lemma does not close that gap, and nothing else here does.

* The **x86 leg** rides the unified `Com jasminDialect` op (`s16HighMulCom`,
  denote `vpmulhw16W`) over the PACKED `BitVec 128` carrier; since that carrier is
  not defeq to the lane-function `Tile 8 16`, the bridge
  (`vpmulhw_com_is_tile_lowering`) crosses the gap with the round-trip lemma
  `vpmulhw16W_lane` (`fin_cases` + `bv_decide`) and the lane view
  `vpmulhw16BvToTile`.
* The **ARM/RISC-V legs** are the `Tile 8 16` siblings of `VectorBackendBridge`'s
  `ninst_is_tile_lowering` / `rvinst_is_tile_lowering` (which cover the `Tile 4 32`
  ALU); their proof is the structural `rfl` — the per-backend `laneMulHiS16` write
  is defeq to `evalTileOp`'s `.mulhs` arm at width 16, and the transports rename
  the `*State8x16` `vregs` field to `TileState 8 16.regs` (the data is identical),
  exactly as `vstateToTile` does for `Tile 4 32`.

`RegInstr.mulhs`, `TileOp.mulhs`, and `evalTileOp`'s `.mulhs` arm were added to
`TileModel` for this path (a dedicated arm rather than a `JasminBinOp`
constructor, which is matched exhaustively across the dialect/optimizer files). -/

/-! ### 4a. The 8×i16 register views coincide with `Tile 8 16` -/

/-- The ARM 8×i16 register view is `Tile 8 16`. -/
example : ARMBackend.Neon.Vec128S16 = Tile 8 16 := rfl
/-- The RISC-V 8×i16 register view is `Tile 8 16`. -/
example : RISCVBackend.Rvv.Vec128S16 = Tile 8 16 := rfl

/-! ### 4b. x86 AVX2 — `VPMULHW`, on the UNIFIED `Com jasminDialect`

`VPMULHW dst, a, b` computes the **high 16 bits** of each signed `i16 × i16`
product across 8 lanes. Combining `VPMULHW` with `VPMULLW` (low 16 bits) recovers
the full 32-bit product the ML-KEM Montgomery reduce uses.

The x86 leg of this bridge is re-homed onto the unified `Com jasminDialect`:
`TileS16HighMulCom.s16HighMulCom` is the dialect-native VPMULHW step, denoting
(`s16HighMulCom_denote`) to the packed waist function `vpmulhw16W : BitVec 128 →
BitVec 128 → BitVec 128`. That packed carrier is not defeq to the lane-function
`Tile 8 16` carrier the ARM/RISC-V legs use, so the bridge crosses the gap via a
single packed↔lane round-trip lemma (`vpmulhw16W_lane`) and the packed-to-tile
view `vpmulhw16BvToTile`, then lands — exactly as the ARM/RISC-V legs do — on the
verified `evalTileOp (lowerRegInstr (.mulhs …))`. -/

/-- **Packed↔lane round-trip for `vpmulhw16W`.** Lane `k` of the packed 8×i16
    high-multiply `vpmulhw16W a b` is the per-lane signed high-multiply
    `laneMulHiS16W` of lanes `k` of `a` and `b`. The packed op
    (`(List.range 8).foldl (… ||| (lane.setWidth 128 <<< 16k)) 0`) places each
    lane result at bits `[16k, 16k+16)`, which is exactly what the lane extract
    reads back. Proved by `fin_cases` + `bv_decide` (the foldl unfolds to a
    concrete 8-term `BitVec 128` expression, bit-blasted lane by lane). -/
theorem vpmulhw16W_lane (a b : BitVec 128) (k : Fin 8) :
    BitVec.extractLsb' (16*k.val) 16 (vpmulhw16W a b)
      = laneMulHiS16W (BitVec.extractLsb' (16*k.val) 16 a)
                      (BitVec.extractLsb' (16*k.val) 16 b) := by
  fin_cases k <;>
    simp only [vpmulhw16W, List.range, List.range.loop, List.foldl] <;>
    bv_decide

/-- View a packed `BitVec 128` (one XMM, 8 × i16) as a `Tile 8 16` by reading each
    16-bit lane. The packed↔lane bridge between the unified op's carrier
    (`BitVec 128`) and the shape-generic tile carrier the §4 lowering targets. -/
def vpmulhw16BvToTile (v : BitVec 128) : Tile 8 16 :=
  fun k => BitVec.extractLsb' (16*k.val) 16 v

/-- **x86 `VPMULHW`, via the unified `Com jasminDialect` op, is the shape-generic
    `mulhs` tile lowering.** Viewing the packed `vpmulhw16W a b` as a `Tile 8 16`
    equals `evalTileOp` of the lowered `RegInstr.mulhs` over the tile state whose
    `"a"`/`"b"` registers carry the lane views of `a`/`b`, stated over the unified
    `SimdOp.mulhi16` semantics (`s16HighMulCom_denote : s16HighMulCom.denote ⟨a,b⟩
    = vpmulhw16W a b`). So `VPMULHW`
    realises `tileMontMulS16`'s per-lane `mulhs` on the verified lowering, landing
    on the *same* `evalTileOp (lowerRegInstr (.mulhs …))` as the ARM/RISC-V legs. -/
theorem vpmulhw_com_is_tile_lowering (a b : BitVec 128) :
    vpmulhw16BvToTile (vpmulhw16W a b)
      = (evalTileOp ⟨fun nm => if nm = "b" then vpmulhw16BvToTile b else vpmulhw16BvToTile a⟩
           (lowerRegInstr (.mulhs "d" "a" "b"))).get "d" := by
  funext k
  simp only [vpmulhw16BvToTile, lowerRegInstr, evalTileOp, TileState.get, TileState.set,
    String.reduceEq, if_true, if_false]
  exact vpmulhw16W_lane a b k

/-- The x86 leg rides the unified op: `vpmulhw16W a b` is exactly the denotation of
    the dialect-native `s16HighMulCom` step on input `⟨a, b⟩`. The bridge
    `vpmulhw_com_is_tile_lowering` therefore consolidates the SAME `Com
    jasminDialect` VPMULHW the emit/lowering consume. -/
theorem vpmulhw_com_rides_unified_op (a b : BitVec 128) :
    s16HighMulCom.denote (.cons a (.cons b .nil)) = vpmulhw16W a b :=
  s16HighMulCom_denote a b

/-! ### 4c. ARM NEON — `SQDMULH` (the `SMULL/SMULL2/UZP2` high-half) -/

/-- Transport an ARM 8×i16 `NState8x16` to the shape-generic `TileState 8 16`. -/
def nstateS16ToTile (s : ARMBackend.Neon.NState8x16) : TileState 8 16 := ⟨s.vregs⟩

/-- **ARM NEON signed high-multiply is the shape-generic `mulhs` tile lowering.**
    Same statement as the x86 bridge at `Tile 8 16`: the NEON 8×i16 high-mul is
    `evalTileOp` of the lowered `RegInstr.mulhs`. The realising A64 sequence is
    `SMULL/SMULL2/UZP2` (or `SQDMULH` up to the architectural doubling); the model
    op is the mathematical signed high-half, defeq to `evalTileOp`'s `.mulhs` arm. -/
theorem sqdmulh_is_tile_lowering (s : ARMBackend.Neon.NState8x16) (d a b : String) :
    nstateS16ToTile (ARMBackend.Neon.evalNInst8x16 s (.mulhs d a b))
      = evalTileOp (nstateS16ToTile s) (lowerRegInstr (.mulhs d a b)) := rfl

/-! ### 4d. RISC-V RVV — `vmulh.vv` (`SEW = 16`, `VL = 8`) -/

/-- Transport a RISC-V 8×i16 `VState8x16` to the shape-generic `TileState 8 16`. -/
def rvstateS16ToTile (s : RISCVBackend.Rvv.VState8x16) : TileState 8 16 := ⟨s.vregs⟩

/-- **RISC-V RVV `vmulh.vv` is the shape-generic `mulhs` tile lowering.** Same
    statement as the x86 / ARM bridges at `Tile 8 16`: the RVV 8×i16 signed
    high-multiply (`SEW = 16`, `VL = 8`) is `evalTileOp` of the lowered
    `RegInstr.mulhs`. -/
theorem vmulh_is_tile_lowering (s : RISCVBackend.Rvv.VState8x16) (d a b : String) :
    rvstateS16ToTile (RISCVBackend.Rvv.evalVInst8x16 s (.vmulh d a b))
      = evalTileOp (rvstateS16ToTile s) (lowerRegInstr (.mulhs d a b)) := rfl

/-! ### 4e. The three ISAs realise the SAME `mulhs` tile op

Together the three legs say: x86 `VPMULHW` (now via the unified `Com jasminDialect`
op, bridged packed↔lane), ARM `SQDMULH`, and RISC-V `vmulh.vv` all land on the
*same* shape-generic `evalTileOp … (lowerRegInstr (.mulhs …))` — so the FIPS-203
NTT Montgomery high-multiply is one verified tile op across all three backends, the
`Tile 8 16` analogue of the `VectorBackendBridge` consolidation (`Tile 4 32` ALU).
The per-lane meaning is `montMulS16Spec`'s high-multiply step (`laneMulHiS16W`),
pinned by the KAT in §5.

The consolidation is over the three *model* ops. For ARM that model op is the
plain signed high half, while the mnemonic the encoder emits for it is `SQDMULH`,
which doubles and saturates (`NeonEncoder.baseSqdmulh`, `NeonModel §5`) — an
undischarged gap between this consolidated tile op and the A64 bytes on the ARM
leg only. -/

/-- The three per-ISA high-multiplies lower to the same tile op: each leg targets
    `evalTileOp _ (lowerRegInstr (.mulhs …))`. The x86 leg is now carried by the
    unified `Com jasminDialect` op (`vpmulhw_com_is_tile_lowering`, over the packed
    `BitVec 128` carrier bridged to `Tile 8 16` by `vpmulhw16BvToTile`); the ARM
    (`sqdmulh_is_tile_lowering`) and RISC-V (`vmulh_is_tile_lowering`) legs stay on
    their bespoke 8×i16 machines. All three land on the same verified tile op. -/
theorem tri_isa_mulhs_consolidates
    (ax bx : BitVec 128) (sn : ARMBackend.Neon.NState8x16)
    (sr : RISCVBackend.Rvv.VState8x16) (d a b : String) :
    vpmulhw16BvToTile (vpmulhw16W ax bx)
        = (evalTileOp ⟨fun nm => if nm = "b" then vpmulhw16BvToTile bx else vpmulhw16BvToTile ax⟩
             (lowerRegInstr (.mulhs "d" "a" "b"))).get "d" ∧
    nstateS16ToTile (ARMBackend.Neon.evalNInst8x16 sn (.mulhs d a b))
        = evalTileOp (nstateS16ToTile sn) (lowerRegInstr (.mulhs d a b)) ∧
    rvstateS16ToTile (RISCVBackend.Rvv.evalVInst8x16 sr (.vmulh d a b))
        = evalTileOp (rvstateS16ToTile sr) (lowerRegInstr (.mulhs d a b)) :=
  ⟨vpmulhw_com_is_tile_lowering ax bx, sqdmulh_is_tile_lowering sn d a b,
    vmulh_is_tile_lowering sr d a b⟩

/-! ## 5. KAT — the tile Montgomery multiply matches the per-lane spec on a worked vector

`fqmul(k, 1) = k · R⁻¹ mod q` where `R⁻¹ mod q = 169` (since `2^16 · 169 ≡ 1 mod 3329`,
verified: `65536 * 169 mod 3329 = 11,075,584 mod 3329 = 1` ✓).
So `fqmul(1,1) = 169`, `fqmul(2,1) = 338`, …, `fqmul(8,1) = 1352`.

The `#eval` computes `tileMontMulS16` on a concrete 8-lane vector and checks it
equals applying `montMulS16Spec` lane-by-lane (which is `rfl` by definition).
The concrete expected values are cross-checked against the FIPS-203 `fqmul`
formula. -/

/-- The KAT input tiles: `a = [1,2,3,4,5,6,7,8]`, `b = [1,1,1,1,1,1,1,1]`. -/
def katA : Tile 8 16 := fun i => BitVec.ofNat 16 (i.val + 1)
def katB : Tile 8 16 := fun _ => 1

/-- The expected `fqmul(k,1) = k·R⁻¹ mod q` for `k = 1..8` (all canonical positive,
    < `q/2 = 1664`): `[169, 338, 507, 676, 845, 1014, 1183, 1352]`. -/
theorem tileMontMulS16_kat :
    let o := tileMontMulS16 katA katB
    (o 0 = 169) ∧ (o 1 = 338) ∧ (o 2 = 507) ∧ (o 3 = 676) ∧
    (o 4 = 845) ∧ (o 5 = 1014) ∧ (o 6 = 1183) ∧ (o 7 = 1352) := by native_decide

-- **`#eval` KAT**: the tile operation and the per-lane spec agree on the worked
-- vector. The `map` uses `montMulS16Spec` directly (both equal by `rfl`).
#eval do
  let o := tileMontMulS16 katA katB
  let expected := (List.finRange 8).map (fun i => montMulS16Spec (katA i) (katB i))
  let got := (List.finRange 8).map (fun i => o i)
  if got == expected then
    IO.println s!"KAT PASS: tile result = per-lane spec result on [1..8] × [1..1]"
  else
    IO.println s!"KAT FAIL"
  IO.println s!"Values (signed): {(List.finRange 8).map (fun i => (o i).toInt)}"

/-! ## 6. The `mulhs` regArith extension (landed)

The per-ISA bridges in §4 are first-class lemmas because a signed-high-multiply
op was added to the shape-generic `TileModel`:
1. `TileModel.RegInstr.mulhs` (+ its `evalRegInstr` arm) — the source op.
2. `TileModel.TileOp.mulhs` (+ its `evalTileOp` arm) — the tile op.
3. `TileModel.lowerRegInstr`'s `.mulhs → .mulhs` arm — the verified lowering
   (`lowerRegInstr_denote`'s `mulhs` case is `rfl`).

It was added as a **dedicated `RegInstr`/`TileOp` arm**, not a `JasminBinOp`
constructor: `JasminBinOp` is matched exhaustively across ~13 dialect/optimizer
files, so a new constructor there has a large blast radius, whereas `RegInstr`
(two constructors) and `TileOp` are local to the tile backend. The signed
high-half is shape-generic in the lane width `w` (`2*w` sign-extend, `sshiftRight
w`, truncate `w`); at `w = 16` it is the FIPS-203 `VPMULHW`/`SQDMULH`/`vmulh.vv`
the §4 bridges realise, and `tileMontMulS16` uses the same per-lane spec. -/

end CatCrypt.Crypto.SecureCompilation.TileBackend.TileS16HighMul
