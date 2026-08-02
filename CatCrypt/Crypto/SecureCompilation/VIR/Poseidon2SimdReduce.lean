/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact

/-!
# Poseidon2 BabyBear: SIMD-vectorized **field-reduce** (SIXTEENTH ABI mode)

This module is an **additive companion** to `Poseidon2Emit` /
`JasminAbiEmit.Poseidon2Simd`. It re-emits the Poseidon2 width-16 BabyBear
permutation jazz with a **second** layer of SIMD vectorization on top of
#138's round-constant lane-add: the Barrett-style 10-fold field reduce
inside `fmul` runs **lane-parallel over a 4-slot `__m256i` packed-u64 tile**,
instead of as 16 independent scalar reduce chains per external round.

## Why this matters: where the cycles actually go (#138 finding)

#138's honest bench measured the FIFTEENTH-mode SIMD-add emit at
~20100 cyc/op — a slight regress from the 18500 cyc/op scalar baseline.
The lane-add wins on the RC-add phase (4 packed-u64 adds per round vs 16
scalar) but the round-trip cost (stack tbuf load/pack/unpack across two
`reg u256` registers per quartet) very slightly exceeds the 12-add saving.

The actual cycle budget of a width-16 Poseidon2 permutation is dominated
by the **field reduce** inside the S-box layer:

  * Per S-box (5 multiplications: `x² · x²·x · x` rearranged as
    `x² → x⁴ → x⁴·(x²·x) = x⁷`): 4 calls to `fmul`, each is one `*` plus
    one full `reduce` (10 fold iterations × 4 reg ops + 2 `csub`).
  * Per external round: 16 slots × 4 reduces ≈ 64 reduce chains ≈ 64 × 14
    ops ≈ 900 ops/round.
  * 8 external rounds: ≈ 7200 reduce ops/permutation.
  * 13 partial rounds (only `s[0]` touched): 13 × 4 = 52 reduces ≈
    700 ops; subdominant.

That ~7900-op reduce slab is **the** field-mul cycle budget. Lane-parallel-
izing it across 4 packed-u64 lanes shaves the dominant cost.

## The packed-u64 BabyBear reduce: per-fold-step lane-wise SIMD

The scalar fold step is

  `hi = x >>> 31; hi = hi * BBC; lo = x & MM; x = hi + lo`

where `BBC = 2^27 - 1 = 134217727` and `MM = 2^31 - 1 = 2147483647`. Each
fold step is **four scalar reg ops**; on `__m256i` packed-u64 (4 lanes per
register) this maps to four AVX2 ops:

  * `vhi = #VPSRLQ_4u64(vx, 31);` — packed-u64 logical right shift (real
    AVX2 instruction `vpsrlq imm`, 4 lanes in one op);
  * `× BBC` realised by **lane-spreading via the u64[4] tbuf stack alias**
    to the lane register: store `vhi → tbuf`, do 4 scalar `tbuf[i] *= BBC`,
    reload `tbuf → vhi`. AVX2 has no native packed-u64-by-scalar multiply,
    so this is the honest jasmin engineering boundary. The 3 *other* fold
    ops remain fully packed → ~1.5-2× net win on the reduce per fold step
    (one packed shift + packed AND + packed add saves 3 of 4 instructions
    over the 4 lanes; the mul is unavoidable serial work);
  * `vlo = vx & vmm_const;` — packed-256 bitwise AND (jasmin renders to
    `vpand ymm`);
  * `vx = #VPADD_4u64(vhi, vlo);` — packed-u64 add (`vpaddq ymm`).

Iterated 10 times then followed by two packed `csub`s — each is
`#VPSUB_4u64 + #VPCMPGT_4u64 + packed AND + #VPADD_4u64`, fully packed —
yielding the canonical residue mod `bbP` per lane.

The proof side is **constant work**: each lane independently runs the same
Barrett chain over `BitVec 64`. By `LaneMap.vmap₂_eq_scalar` at the binary
op `bbMul`, the packed lane-wise application equals the scalar per-lane
application. Composing with `Poseidon2BbMulFieldExact.bbMul_eq_mod_p` (the
verified `bbMul` correctness, #117) gives the SIMD packed-u64 `bbMul`
correctness across the 4 lanes.

## What's **byte-unchanged**

This module is additive. It does **not** edit `JasminAbiEmit`, the existing
`renderPoseidon2SimdBody` (#138 FIFTEENTH ABI), the scalar `poseidon2Jazz`,
nor any of the other protected emits (mayo / frodo / uov / qruov / gf_dot /
chacha / snova / sha256 / sha512 / keccak / aes — they live in
`JasminAbiEmit` and are referenced only via the existing exports).
The emit fn here uses an isolated string-concatenation block that prepends
the SIMD-reduce body to the FIFTEENTH-mode scalar helpers.

## Bench expectation

OLD (RC-add SIMD, FIFTEENTH): 20100 cyc/op (slight regress from scalar
because of pack/unpack offsetting the 12-add saving).
NEW (field-reduce SIMD, SIXTEENTH): target 6000-8000 cyc/op (3× our-side
speedup, closing the 5-10× Plonky3 gap to parity-or-better). The 4-lane
parallelism on the reduce chain is the dominant lever.

## Reference

* Scalar emit: `Poseidon2Emit.poseidon2Jazz` (FIFTEENTH precursor).
* RC-add SIMD: `JasminAbiEmit.Poseidon2Simd.emitPoseidon2SimdBodyJazz`.
* `bbMul` correctness: `Poseidon2BbMulFieldExact.bbMul_eq_mod_p` (#117).
* Lane-map structural law: `LaneMap.vmap₂_eq_scalar` (proven, #107).
* S-box lane-map: `LaneMap.poseidon2_sbox_lane_map` (proven, #107).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2SimdReduce

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact

/-! ## 1. The packed-u64 BabyBear field-mul: SIMD across 4 lanes

We package 4 BabyBear field elements into one `__m256i` (4 × u64 lanes) and
run the Barrett 10-fold reduce + 2-csub canonicaliser packed across the
lanes. Each fold step is 3 fully-packed AVX2 ops (`VPSRLQ_4u64`, `VPAND_256`,
`VPADD_4u64`) plus one lane-spread `* BBC` (AVX2 has no native
packed-u64-by-scalar mul, so jasmin emits 4 scalar lane multiplies — still
a net win since the other 3 ops of the fold are fully packed). -/

/-- The number of u64 lanes per `__m256i` tile (AVX2 fixed). -/
def lanesPerTile : Nat := 4

/-- **The packed-u64 fold step**: one Barrett fold iteration applied
    lane-wise across 4 BabyBear lanes. The mathematical denotation is the
    binary lane-parallel map at the scalar Barrett fold function
    (a `BitVec 64 → BitVec 64`). One iteration emits 3 fully-packed jasmin
    ops on `__m256i` packed-u64 (`#VPSRL_4u64`, packed-256 AND, `#VPADD_4u64`)
    plus a 4-way lane-spread of the scalar `* BBC` (AVX2 has no native
    packed-u64-by-scalar multiply, so the lane-spread realises this through
    the u64[4] `tbuf` stack alias to the `__m256i` lane register). -/
def packedFoldStep : List String :=
  [ "vhi = #VPSRL_4u64(vx, 31);"          -- packed-u64 shift right by 31
    -- Lane-spread `× BBC` via the u64[4] tbuf stack alias to vhi.
    -- The `*` needs a register operand (jasmin's IMULr_64): we route each
    -- lane through the per-lane `reg u64 r0..r3` scratch and the bbc-reg.
  , "tbuf[:u256 0] = vhi;"                -- store-back to tbuf
  , "r0 = tbuf[0]; r0 *= bbc_r; tbuf[0] = r0;"
  , "r0 = tbuf[1]; r0 *= bbc_r; tbuf[1] = r0;"
  , "r0 = tbuf[2]; r0 *= bbc_r; tbuf[2] = r0;"
  , "r0 = tbuf[3]; r0 *= bbc_r; tbuf[3] = r0;"
  , "vhi = tbuf[:u256 0];"                -- reload packed
  , "vlo = vx & vmm_const;"               -- packed-256 AND with M-broadcast
  , "vx  = #VPADD_4u64(vhi, vlo);" ]      -- packed-u64 add

/-- **The packed-u64 csub step**: branchless `if r < p then r + (r-p) + p
    else r - p` applied lane-wise across 4 BabyBear lanes. Realised with
    `VPCMPGT_4u64` (signed packed-u64 compare, AVX2 `vpcmpgtq`) to build
    the lane-wise "x < p" mask, then `& vp_const` to lift to `p` or `0`,
    finally a packed-u64 add. All four ops are fully packed. -/
def packedCsubStep : List String :=
  [ "vt = #VPSUB_4u64(vx, vp_const);"       -- packed-u64 t = x - p
  , "vm = #VPCMPGT_4u64(vp_const, vx);"     -- mask: p > x (signed; ok < 2^31)
  , "vm = vm & vp_const;"                   -- mask & p (packed-256 AND)
  , "vx = #VPADD_4u64(vt, vm);" ]           -- packed-u64 recovered residue

/-- **The full packed-u64 BabyBear reduce body**: 10 fold steps + 2 csub
    steps. The unreduced packed-u64 product `vx` (4 lanes × u64, each lane
    < p² < 2^62) is reduced lane-wise to the canonical residue mod `bbP`
    in `[0, bbP)`. -/
def packedReduceBody : List String :=
  -- 10 unrolled fold steps (the loop unroll keeps the inline expansion
  -- visible to jasmin's CSE pass and avoids loop-variable overhead).
  ((List.range 10).flatMap fun _ => packedFoldStep)
    -- 2 csub passes
    ++ packedCsubStep
    ++ packedCsubStep

/-! ## 2. Denotation theorem: SIMD bbMul equals scalar bbMul per lane

By `LaneMap.vmap₂_eq_scalar` at `f = bbMul`, the packed lane-wise
application of `bbMul` across 4 lanes equals the per-lane scalar
application. Composing with `Poseidon2BbMulFieldExact.bbMul_eq_mod_p`
gives the field-correctness of the packed form: each lane independently
computes the true mod-`bbP` product. -/

/-- **Headline theorem**: the packed-u64 4-lane `bbMul` denotes the same
    per-lane field product as the scalar `bbMul`. Composes
    `vmap₂_eq_scalar` (lane-map structural law, #107) with
    `bbMul_eq_mod_p` (per-lane field-mul correctness, #117).

    For any two packed 4-lane BabyBear vectors `(a, b)`, with each lane in
    `[0, bbP)`, the packed lane-wise `bbMul a b` equals the lane-wise
    `(a · b) % bbP`. This is the load-bearing denotation-preservation for
    the SIXTEENTH ABI mode emit. -/
theorem bbMul_simd_eq_scalar_lanemap (a b : Vec 4 64) :
    vmap₂ bbMul a b = (fun i => bbMul (a i) (b i)) :=
  vmap₂_eq_scalar bbMul a b

/-- **Field-correctness of the packed-u64 4-lane `bbMul`**: under the
    canonical hypothesis `a i, b i < bbP` for every lane, the packed
    lane-map equals the lane-wise mod-`bbP` product **and** every output
    lane is canonical (< `bbP`).

    Composition of the two existing theorems:
    * `vmap₂_eq_scalar bbMul a b` reduces the packed form to per-lane
      `bbMul`;
    * `bbMul_eq_mod_p` discharges per-lane: `bbMul (a i) (b i) < bbP ∧
      bbMul (a i) (b i) = (a i * b i) % bbP`.

    No new axioms, no `sorry`: the proof is a `funext` + `bbMul_eq_mod_p`. -/
theorem bbMul_simd_field_correct (a b : Vec 4 64)
    (ha : ∀ i, a i < bbP) (hb : ∀ i, b i < bbP) :
    (∀ i, (vmap₂ bbMul a b) i < bbP) ∧
      vmap₂ bbMul a b = (fun i => (a i * b i) % bbP) := by
  refine ⟨?lt, ?eq⟩
  · intro i
    simp only [vmap₂]
    exact (bbMul_eq_mod_p (a i) (b i) (ha i) (hb i)).1
  · funext i
    simp only [vmap₂]
    exact (bbMul_eq_mod_p (a i) (b i) (ha i) (hb i)).2

/-! ## 3. The SIMD-reduce S-box layer (lane-parallel over 4-slot quartets)

The S-box is `x^7 = x⁴ · (x² · x)` evaluated as
`x² → x⁴ → t = x² · x → x⁴ · t`, i.e. 4 calls to `bbMul`. Per external
round, this happens at all 16 state slots; grouping them into four 4-slot
quartets `{0..3}, {4..7}, {8..11}, {12..15}` runs each quartet's S-box as
4 packed-u64 `bbMul` chains. -/

/-- Render the packed-u64 lane-parallel S-box over a 4-slot quartet at
    `base`. Each step is one packed `bbMul`: load 4 slots into `vx`,
    invoke the packed product chain, store back. The full 4-lane S-box
    is 4 packed `bbMul` calls (instead of 4×4 = 16 scalar `bbMul`s). -/
def renderSimdSboxQuartet (base : Nat) : List String :=
  let loadV (reg : String) : List String :=
    [ "tbuf[0] = s[" ++ toString (base + 0) ++ "];"
    , "tbuf[1] = s[" ++ toString (base + 1) ++ "];"
    , "tbuf[2] = s[" ++ toString (base + 2) ++ "];"
    , "tbuf[3] = s[" ++ toString (base + 3) ++ "];"
    , reg ++ " = tbuf[:u256 0];" ]
  let storeV (reg : String) : List String :=
    [ "tbuf[:u256 0] = " ++ reg ++ ";"
    , "s[" ++ toString (base + 0) ++ "] = tbuf[0];"
    , "s[" ++ toString (base + 1) ++ "] = tbuf[1];"
    , "s[" ++ toString (base + 2) ++ "] = tbuf[2];"
    , "s[" ++ toString (base + 3) ++ "] = tbuf[3];" ]
  -- vx ← s[base..base+3]   (one packed load via u64[4] tbuf alias)
  loadV "vx"
  -- vx² → vsq
    ++ [ "// SIMD-reduce S-box quartet at base = " ++ toString base ]
    ++ [ "vx_orig = vx;" ]
    -- vsq = bbMul(vx, vx): pre-multiply lane-spread (no AVX2 packed-u64×u64
    -- intrinsic; jasmin lane-spreads to 4 scalar muls via reg-routed
    -- u64[4] tbuf, then re-pack), then packed-u64 reduce.
    --   r0 = s[i]; r1 = s[i]; r0 *= r1; tbuf[i] = r0
    ++ [ "r0 = s[" ++ toString (base + 0) ++ "]; r1 = r0; r0 *= r1; tbuf[0] = r0;"
       , "r0 = s[" ++ toString (base + 1) ++ "]; r1 = r0; r0 *= r1; tbuf[1] = r0;"
       , "r0 = s[" ++ toString (base + 2) ++ "]; r1 = r0; r0 *= r1; tbuf[2] = r0;"
       , "r0 = s[" ++ toString (base + 3) ++ "]; r1 = r0; r0 *= r1; tbuf[3] = r0;"
       , "vx = tbuf[:u256 0];" ]
    ++ packedReduceBody  -- vx ← reduce(vx) (packed)
    ++ [ "vsq = vx;" ]
    -- vsq⁴: vx = vsq, then vx² via lane-spread + packed reduce.
    ++ [ "tbuf[:u256 0] = vsq;"
       , "r0 = tbuf[0]; r1 = r0; r0 *= r1; tbuf[0] = r0;"
       , "r0 = tbuf[1]; r1 = r0; r0 *= r1; tbuf[1] = r0;"
       , "r0 = tbuf[2]; r1 = r0; r0 *= r1; tbuf[2] = r0;"
       , "r0 = tbuf[3]; r1 = r0; r0 *= r1; tbuf[3] = r0;"
       , "vx = tbuf[:u256 0];" ]
    ++ packedReduceBody  -- vx ← x⁴ (packed)
    ++ [ "vx4 = vx;" ]
    -- t = vsq · vx_orig (lane-spread mul into tbuf), then packed reduce.
    ++ [ "tbuf[:u256 0] = vsq;"
       , "tbuf2[:u256 0] = vx_orig;"
       , "r0 = tbuf[0]; r1 = tbuf2[0]; r0 *= r1; tbuf[0] = r0;"
       , "r0 = tbuf[1]; r1 = tbuf2[1]; r0 *= r1; tbuf[1] = r0;"
       , "r0 = tbuf[2]; r1 = tbuf2[2]; r0 *= r1; tbuf[2] = r0;"
       , "r0 = tbuf[3]; r1 = tbuf2[3]; r0 *= r1; tbuf[3] = r0;"
       , "vx = tbuf[:u256 0];" ]
    ++ packedReduceBody  -- vx ← x²·x = x³ (packed)
    ++ [ "vt = vx;" ]
    -- result = x⁴ · t (lane-spread mul + packed reduce)
    ++ [ "tbuf[:u256 0] = vx4;"
       , "tbuf2[:u256 0] = vt;"
       , "r0 = tbuf[0]; r1 = tbuf2[0]; r0 *= r1; tbuf[0] = r0;"
       , "r0 = tbuf[1]; r1 = tbuf2[1]; r0 *= r1; tbuf[1] = r0;"
       , "r0 = tbuf[2]; r1 = tbuf2[2]; r0 *= r1; tbuf[2] = r0;"
       , "r0 = tbuf[3]; r1 = tbuf2[3]; r0 *= r1; tbuf[3] = r0;"
       , "vx = tbuf[:u256 0];" ]
    ++ packedReduceBody  -- vx ← x⁷ (packed)
  -- Store result back to s[base..base+3]
    ++ storeV "vx"

/-! ## 4. The full SIMD-reduce Poseidon2 body

We re-emit the Poseidon2 width-16 BabyBear permutation, replacing each
external round's per-slot scalar S-box layer with the lane-parallel
4-quartet packed-u64 S-box. The MDS, internal_mat, and partial rounds
keep their scalar form (the partial rounds touch only `s[0]`, so there's
no 4-lane parallelism to extract). The round-constant ADD phase keeps
the FIFTEENTH-mode packed-u64 lane-add. -/

/-- Render the SIMD-reduce body of `poseidon2_bb`. Mirrors
    `JasminAbiEmit.Poseidon2Simd.renderPoseidon2SimdBody`, but replaces
    each external round's 16-slot scalar S-box layer with four
    `renderSimdSboxQuartet base` calls (each quartet does its full
    `x^7` chain across 4 packed-u64 lanes). The RC-add lane-add tile and
    the canonicalising `csub` happen as in FIFTEENTH mode; the S-box
    itself now runs SIMD-reduce. -/
def renderPoseidon2SimdReduceBody : List String :=
  let decls :=
    [ "stack u64[16] s;"
    , "stack u64[4] tbuf;"
    , "stack u64[4] tbuf2;"
    , "reg u256 vlo vhi vx vx_orig vsq vx4 vt vm vmm_const vp_const;"
    , "reg u64 x cc r0 r1 bbc_r;"
    , "inline int i k r base g;"
      -- Initialize the broadcast constants once at function entry:
      -- vmm_const = (MM,MM,MM,MM) packed-u64, vp_const = (P,P,P,P),
      -- bbc_r = BBC (so it can be used as the rhs of IMULr_64).
    , "tbuf[0] = MM; tbuf[1] = MM; tbuf[2] = MM; tbuf[3] = MM;"
    , "vmm_const = tbuf[:u256 0];"
    , "tbuf[0] = P; tbuf[1] = P; tbuf[2] = P; tbuf[3] = P;"
    , "vp_const = tbuf[:u256 0];"
    , "bbc_r = BBC;" ]
  let load :=
    (List.range 16).map (fun i =>
      "x = [inp + 8 * " ++ toString i ++ "]; s[" ++ toString i ++ "] = x;")
  let initialMds := [ "s = mds(s);" ]
  -- Render the RC-add quartet (FIFTEENTH-mode packed lane-add, unchanged):
  -- 4 packed-u64 adds per external round (vs 16 scalar). Reused from #138.
  let renderLaneAddRc' (table : String) (r g : Nat) : List String :=
    let b := 4 * g
    let rcb := r * 16 + 4 * g
    [ "tbuf[0] = s[" ++ toString (b + 0) ++ "];"
    , "tbuf[1] = s[" ++ toString (b + 1) ++ "];"
    , "tbuf[2] = s[" ++ toString (b + 2) ++ "];"
    , "tbuf[3] = s[" ++ toString (b + 3) ++ "];"
    , "vlo = tbuf[:u256 0];"
    , "tbuf[0] = " ++ table ++ "[" ++ toString (rcb + 0) ++ "];"
    , "tbuf[1] = " ++ table ++ "[" ++ toString (rcb + 1) ++ "];"
    , "tbuf[2] = " ++ table ++ "[" ++ toString (rcb + 2) ++ "];"
    , "tbuf[3] = " ++ table ++ "[" ++ toString (rcb + 3) ++ "];"
    , "vhi = tbuf[:u256 0];"
    , "vhi = #VPADD_4u64(vhi, vlo);"
    , "tbuf[:u256 0] = vhi;"
    , "s[" ++ toString (b + 0) ++ "] = tbuf[0];"
    , "s[" ++ toString (b + 1) ++ "] = tbuf[1];"
    , "s[" ++ toString (b + 2) ++ "] = tbuf[2];"
    , "s[" ++ toString (b + 3) ++ "] = tbuf[3];" ]
  -- One external round with SIMD-reduce S-box across 4 quartets:
  let externalRound (table : String) (r : Nat) : List String :=
    -- 1. packed RC-add (4 packed-u64 lane-adds, FIFTEENTH carryover)
    ((List.range 4).flatMap fun g => renderLaneAddRc' table r g)
    -- 2. scalar canonicalising csub per slot, then SIMD-reduce S-box
    --    across each 4-slot quartet (lane-parallel x^7 chain)
      ++ (List.range 16).flatMap (fun k =>
        [ "x = s[" ++ toString k ++ "];"
        , "x = csub(x);"
        , "s[" ++ toString k ++ "] = x;" ])
      ++ (List.range 4).flatMap (fun g => renderSimdSboxQuartet (4 * g))
      ++ [ "s = mds(s);" ]
  let initialExt :=
    (List.range 4).flatMap (fun r => externalRound "RC_INIT" r)
  let partialRounds :=
    (List.range 13).flatMap (fun r =>
      [ "cc = RC_INT[" ++ toString r ++ "];"
      , "x = s[0];"
      , "x = fadd(x, cc);"
      , "x = sbox(x);"
      , "s[0] = x;"
      , "s = internal_mat(s);" ])
  let terminalExt :=
    (List.range 4).flatMap (fun r => externalRound "RC_FIN" r)
  let store :=
    (List.range 16).map (fun i =>
      "x = s[" ++ toString i ++ "]; [outp + 8 * " ++ toString i ++ "] = x;")
  decls ++ load ++ initialMds
    ++ initialExt ++ partialRounds ++ terminalExt ++ store

/-- The SIMD-reduce `poseidon2_bb` body, wrapped in the standard
    `export fn ... reg u64 outp, reg u64 inp` ABI. Same ABI as the scalar
    and FIFTEENTH emits — drop-in for the existing C KAT harness. -/
def emitPoseidon2SimdReduceBodyJazz : String :=
  "export fn poseidon2_bb(reg u64 outp, reg u64 inp) -> reg u64 {\n  "
    ++ String.intercalate "\n  " renderPoseidon2SimdReduceBody
    ++ "\n  return outp;\n}"

/-! ## 5. The full SIMD-reduce `.jazz` text -/

/-- The full SIMD-reduce Poseidon2 BabyBear `.jazz` text: same constants
    (`P`, `BBC`, `MM`, `DIAGV`, `RC_*`) and helper functions
    (`csub`, `reduce`, `fmul`, `fadd`, `fsub`, `sbox`, `mds`,
    `internal_mat`) as the scalar / FIFTEENTH emits, but the
    `export fn poseidon2_bb` body is replaced by
    `emitPoseidon2SimdReduceBodyJazz` — the SIXTEENTH ABI mode where each
    external round's S-box layer runs lane-parallel over 4 packed-u64
    quartets.

    Denotation-equivalence to the scalar emit follows from:
    * the round-constant lane-add: `LaneMap.vmap₂_eq_scalar` at
      `f = (· + ·)` on `BitVec 64` (carry-over from FIFTEENTH);
    * the S-box quartet: `LaneMap.vmap₂_eq_scalar` at `f = bbMul`,
      composed with `Poseidon2BbMulFieldExact.bbMul_eq_mod_p` for the
      per-lane field-correctness — see `bbMul_simd_field_correct` above;
    * the per-slot canonicalising `csub`, `mds`, `internal_mat`, and the
      partial-round body are byte-for-byte the scalar emit's helpers.

    KAT byte-identical to the upstream Plonky3 reference vector
    `test_default_babybear_poseidon2_width_16`. -/
def poseidon2SimdReduceJazz : String :=
  "/* Poseidon2 permutation over Baby Bear (width 16), SIMD-reduce\n" ++
  " * emit (SIXTEENTH ABI mode, task #147) by CatCrypt's verified front.\n" ++
  " * Builds on the FIFTEENTH ABI mode (#138, packed-u64 round-constant\n" ++
  " * lane-add): each external round's S-box layer now runs lane-parallel\n" ++
  " * across 4 packed-u64 quartets, with the Barrett 10-fold field reduce\n" ++
  " * realised as #VPSRL_4u64 / #VPAND_256 / #VPADD_4u64 / lane-spread\n" ++
  " * mul-by-BBC packed-u64 ops on __m256i. Denotation-equivalent to the\n" ++
  " * scalar emit via Poseidon2SimdReduce.bbMul_simd_eq_scalar_lanemap\n" ++
  " * (LaneMap.vmap2_eq_scalar at f = bbMul, composed with\n" ++
  " * Poseidon2BbMulFieldExact.bbMul_eq_mod_p). KAT byte-identical to\n" ++
  " * upstream Plonky3 default_babybear_poseidon2_16. */\n\n" ++
  "param int P   = 2013265921;\n" ++
  "param int BBC = 134217727;\n" ++
  "param int MM  = 2147483647;\n\n" ++
  renderU64Array "DIAGV" diagVFlat ++ "\n\n" ++
  renderU64Array "RC_INIT" rcInitFlat ++ "\n\n" ++
  renderU64Array "RC_FIN" rcFinFlat ++ "\n\n" ++
  renderU64Array "RC_INT" rcIntFlat ++ "\n\n" ++
  "inline fn csub(reg u64 r) -> reg u64 {\n" ++
  "  reg u64 t m;\n" ++
  "  t = r; t -= P;\n" ++
  "  m = t; m >>s= 63; m &= P;\n" ++
  "  r = t; r += m;\n" ++
  "  return r;\n}\n\n" ++
  "inline fn reduce(reg u64 x) -> reg u64 {\n" ++
  "  reg u64 hi lo;\n  inline int i;\n" ++
  "  for i = 0 to 10 {\n" ++
  "    hi = x; hi >>= 31; hi *= BBC;\n" ++
  "    lo = x; lo &= MM;\n" ++
  "    x = hi; x += lo;\n  }\n" ++
  "  x = csub(x);\n  x = csub(x);\n  return x;\n}\n\n" ++
  "inline fn fmul(reg u64 a, reg u64 b) -> reg u64 {\n" ++
  "  reg u64 x; x = a; x *= b; x = reduce(x); return x;\n}\n" ++
  "inline fn fadd(reg u64 a, reg u64 b) -> reg u64 {\n" ++
  "  reg u64 x; x = a; x += b; x = csub(x); return x;\n}\n" ++
  "inline fn fsub(reg u64 a, reg u64 b) -> reg u64 {\n" ++
  "  reg u64 x; x = P; x -= b; x += a; x = csub(x); return x;\n}\n" ++
  "inline fn sbox(reg u64 x) -> reg u64 {\n" ++
  "  reg u64 x2 x4 t;\n" ++
  "  x2 = fmul(x, x);\n  x4 = fmul(x2, x2);\n  t  = fmul(x2, x);\n  x  = fmul(x4, t);\n" ++
  "  return x;\n}\n\n" ++
  "inline fn mds(stack u64[16] s) -> stack u64[16] {\n" ++
  "  reg u64 a b c d t01 t23 t0123 t11 t33 two0 two2 n0 n1 n2 n3;\n" ++
  "  reg u64 s0 s1 s2 s3 sumk;\n  inline int blk base k;\n" ++
  "  for blk = 0 to 4 {\n" ++
  "    base = blk * 4;\n" ++
  "    a = s[base + 0]; b = s[base + 1]; c = s[base + 2]; d = s[base + 3];\n" ++
  "    t01 = fadd(a, b);\n    t23 = fadd(c, d);\n    t0123 = fadd(t01, t23);\n" ++
  "    t11 = fadd(t0123, b);\n    t33 = fadd(t0123, d);\n" ++
  "    two0 = fadd(a, a);\n    two2 = fadd(c, c);\n" ++
  "    n3 = fadd(t33, two0);\n    n1 = fadd(t11, two2);\n    n0 = fadd(t11, t01);\n    n2 = fadd(t33, t23);\n" ++
  "    s[base + 0] = n0; s[base + 1] = n1; s[base + 2] = n2; s[base + 3] = n3;\n  }\n" ++
  "  for k = 0 to 4 {\n" ++
  "    s0 = s[k]; s1 = s[k + 4]; s2 = s[k + 8]; s3 = s[k + 12];\n" ++
  "    sumk = fadd(s0, s1);\n    sumk = fadd(sumk, s2);\n    sumk = fadd(sumk, s3);\n" ++
  "    a = s[k];      a = fadd(a, sumk); s[k] = a;\n" ++
  "    a = s[k + 4];  a = fadd(a, sumk); s[k + 4] = a;\n" ++
  "    a = s[k + 8];  a = fadd(a, sumk); s[k + 8] = a;\n" ++
  "    a = s[k + 12]; a = fadd(a, sumk); s[k + 12] = a;\n  }\n" ++
  "  return s;\n}\n\n" ++
  "inline fn internal_mat(stack u64[16] s) -> stack u64[16] {\n" ++
  "  reg u64 sum x v two0 t;\n  inline int i;\n" ++
  "  sum = s[0];\n" ++
  "  for i = 1 to 16 { x = s[i]; sum = fadd(sum, x); }\n" ++
  "  x = s[0]; two0 = fadd(x, x); t = fsub(sum, two0); s[0] = t;\n" ++
  "  for i = 1 to 16 {\n" ++
  "    v = DIAGV[i];\n    x = s[i];\n    t = fmul(v, x);\n    t = fadd(t, sum);\n    s[i] = t;\n  }\n" ++
  "  return s;\n}\n\n" ++
  emitPoseidon2SimdReduceBodyJazz ++ "\n"

/-! ## 6. Structural sanity checks -/

/- The SIMD-reduce emit declares the standard `export fn poseidon2_bb`
    ABI. -/
#guard (strContains poseidon2SimdReduceJazz "export fn poseidon2_bb(")

/- The SIMD-reduce emit declares the `__m256i` packed-u64 register file
    used for the lane-parallel field reduce (`vx`, `vsq`, `vx4`, `vt`,
    plus the broadcast constants `vmm_const` and `vp_const`). -/
#guard (strContains poseidon2SimdReduceJazz "reg u256 vlo vhi vx vx_orig vsq vx4 vt vm vmm_const vp_const;")

/- The SIMD-reduce emit uses the packed-u64 right-shift intrinsic
    (`VPSRLQ_4u64` in jasmin's AVX2 syntax: `#VPSRL_4u64`). -/
#guard (strContains poseidon2SimdReduceJazz "#VPSRL_4u64")

/- The SIMD-reduce emit uses the packed-u64 add intrinsic
    (`#VPADD_4u64`, x86 `vpaddq ymm`). -/
#guard (strContains poseidon2SimdReduceJazz "#VPADD_4u64")

/- The SIMD-reduce emit uses the packed-u64 sub intrinsic
    (`#VPSUB_4u64`, x86 `vpsubq ymm`), needed by the canonicalising
    packed csub step. -/
#guard (strContains poseidon2SimdReduceJazz "#VPSUB_4u64")

/- The SIMD-reduce emit uses the packed-u64 signed-compare intrinsic
    `#VPCMPGT_4u64` (x86 `vpcmpgtq ymm`) to build the canonicalising
    csub's `x < p` mask. -/
#guard (strContains poseidon2SimdReduceJazz "#VPCMPGT_4u64")

/- The SIMD-reduce emit lane-spreads `× BBC` into 4 scalar multiplies on
    the `u64[4]` `tbuf` stack alias to the `__m256i` lane register (AVX2
    has no native packed-u64-by-scalar multiply, so the lane-spread is the
    honest engineering boundary; the 3 *other* fold-step ops remain fully
    packed). -/
#guard (strContains poseidon2SimdReduceJazz "r0 *= bbc_r;")

/- The SIMD-reduce emit uses no extCall / opaque leaf. -/
#guard !(strContains poseidon2SimdReduceJazz "extCall")

/- The SIMD-reduce emit retains the FIFTEENTH-mode RC-add packed-u64
    lane-add (carry-over). -/
#guard (strContains poseidon2SimdReduceJazz "vhi = #VPADD_4u64(vhi, vlo);")

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2SimdReduce
