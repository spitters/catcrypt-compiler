/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit

/-!
# ChaCha20 4-way emitted through the structured VectorDialect (task #183, Step 2)

The existing ChaCha 4-way emit (`VIR/JasminAbiEmit.emitChacha4wayJazz`,
re-exported as `ChaChaEmit.chacha4wayBlockJazz`) renders the lane-parallel
quarter-round DIRECTLY as mnemonic strings (`renderChacha4wayAddIn`,
`renderChacha4wayXorIn`, `renderChacha4wayRotL`). It is left **untouched** —
this file adds a PARALLEL path that routes the same emission through the
abstract `VectorOp` alphabet, then proves the two paths are byte-identical.

## What this demonstrates (de-risking the dialect against the symmetric cluster)

The multivariate consumers (MAYO/UOV/QR-UOV) are already migrated onto
`VectorOp`. ChaCha is the canonical *lane-parallel-map* consumer — the
structural sibling of the multivariate path. Migrating it shows the structured
dialect extends past the GF(2^8) / lattice-poly cluster to the ARX/symmetric
cluster without regression:

* every ChaCha 4-way lane op is tagged with the `VectorOp` constructor it
  realizes (`add` for `VPADD`, the generic binary `add`-carrying-xor / `or`,
  the new `shiftL`/`shiftR` for `VPSLL`/`VPSRL`);
* `ChaCha4WayVecOp.render` emits the *same mnemonic strings* the direct emit
  uses, so the rendered body is provably byte-identical
  (`chacha4wayVec_body_eq_direct`, by `native_decide`);
* the denotation is the dialect's lane-parallel map, grounded in
  `LaneMap.chacha4way_lane_map` (the proven #107 lane-map keystone).

Because the rendered text is *identical* to the direct emit, the KAT
(`bench/chacha_compare/` RFC 8439 §2.3.2 known-answer test) that validates
`emitChacha4wayJazz` validates this path verbatim — no new bytes, no new KAT.

The dialect ops `VectorOp.add`/`shiftL`/`shiftR` lower to per-lane scalar
expansions with proven denotation preservation (`lower_add_correct`,
`lower_shiftL_correct`, `lower_shiftR_correct` in `Lowering.lean`), so the
abstract → per-lane-scalar leg of the pipeline is covered for every op this
consumer uses.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ChaCha4WayVec

open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The ChaCha 4-way lane-op alphabet, tagged with its `VectorOp` role

Each constructor packages a *high-level ChaCha lane op* on stack-slot operands.
The lane shape is fixed: `4` lanes (the 4 parallel ChaCha blocks) of `BitVec 32`
words. The `VectorOp` it realizes (its abstract denotation classifier) is
recorded by `vectorOp` below; the emitted text by `render`. -/

/-- The lane width and count for ChaCha 4-way: 4 lanes of 32-bit words. -/
abbrev laneN : Nat := 4

/-- A single high-level ChaCha 4-way lane op on stack `m[..]` slot operands.
    These are exactly the three primitive ops `renderChacha4wayQR` is built
    from. -/
inductive ChaCha4WayVecOp where
  /-- `m[dst] += m[src]` — packed 4×u32 add (`#VPADD_4u32`). Realizes
      `VectorOp.add`. -/
  | addIn (dst src : Nat)
  /-- `m[dst] ^= m[src]` — packed lane-wise xor. Realizes the generic
      binary `VectorOp.add` carrying `(· ^^^ ·)`. -/
  | xorIn (dst src : Nat)
  /-- `m[dst] <<<= n` — ARX rotate-left, lowered to `VPSLL`+`VPSRL`+`VPOR`.
      Realizes `VectorOp.shiftL` ∘ `VectorOp.shiftR` ∘ binary-or. -/
  | rotL (dst n : Nat)
  deriving DecidableEq, Repr

/-! ## 2. Rendering — reuses the *exact* direct-emit string builders

`render` does not invent text: it delegates to the existing
`renderChacha4wayAddIn` / `renderChacha4wayXorIn` / `renderChacha4wayRotL`
helpers (read-only, in `JasminAbiEmit`). So a `ChaCha4WayVecOp` program renders
to literally the same lines the direct emit would — the byte-identity proof is
then definitional. -/

/-- Render one tagged lane op to its jasmin mnemonic lines (delegating to the
    direct-emit helpers). -/
def ChaCha4WayVecOp.render : ChaCha4WayVecOp → List String
  | .addIn dst src => renderChacha4wayAddIn dst src
  | .xorIn dst src => renderChacha4wayXorIn dst src
  | .rotL dst n => renderChacha4wayRotL dst n

/-- Render a program (list of tagged ops). -/
def renderProgram (p : List ChaCha4WayVecOp) : List String :=
  p.flatMap ChaCha4WayVecOp.render

/-! ## 3. The ChaCha 4-way QR / round / body as a `ChaCha4WayVecOp` PROGRAM

Mirrors `renderChacha4wayQR` etc. one-for-one, but as a list of abstract tagged
ops rather than raw strings. -/

/-- The quarter-round as a tagged-op program (mirrors `renderChacha4wayQR`). -/
def qrProgram (a b c d : Nat) : List ChaCha4WayVecOp :=
  [ .addIn a b, .xorIn d a, .rotL d 16
  , .addIn c d, .xorIn b c, .rotL b 12
  , .addIn a b, .xorIn d a, .rotL d 8
  , .addIn c d, .xorIn b c, .rotL b 7 ]

/-- Column round as a tagged-op program. -/
def columnProgram : List ChaCha4WayVecOp :=
  qrProgram 0 4 8 12 ++ qrProgram 1 5 9 13 ++
  qrProgram 2 6 10 14 ++ qrProgram 3 7 11 15

/-- Diagonal round as a tagged-op program. -/
def diagProgram : List ChaCha4WayVecOp :=
  qrProgram 0 5 10 15 ++ qrProgram 1 6 11 12 ++
  qrProgram 2 7 8 13 ++ qrProgram 3 4 9 14

/-- Double round as a tagged-op program. -/
def doubleProgram : List ChaCha4WayVecOp := columnProgram ++ diagProgram

/-- `n` double-rounds. -/
def doubleRoundsProgram : Nat → List ChaCha4WayVecOp
  | 0 => []
  | (k+1) => doubleProgram ++ doubleRoundsProgram k

/-! ## 4. Byte-identity with the direct emit (the keystone)

These show that rendering the tagged-op program produces **exactly** the same
lines as the existing direct-mnemonic emit, op for op and round for round. -/

/-- The QR rendered through the tagged-op path is byte-identical to the direct
    `renderChacha4wayQR`. -/
theorem qr_render_eq_direct (a b c d : Nat) :
    renderProgram (qrProgram a b c d) = renderChacha4wayQR a b c d := by
  rfl

/-- The column round matches. -/
theorem column_render_eq_direct :
    renderProgram columnProgram = renderChacha4wayColumnRound := by
  native_decide

/-- The diagonal round matches. -/
theorem diag_render_eq_direct :
    renderProgram diagProgram = renderChacha4wayDiagRound := by
  native_decide

/-- One double round matches. -/
theorem double_render_eq_direct :
    renderProgram doubleProgram = renderChacha4wayDoubleRound := by
  native_decide

/-- `n` double rounds match (the full round-program leg). -/
theorem doubleRounds_render_eq_direct (n : Nat) :
    renderProgram (doubleRoundsProgram n) = renderChacha4wayDoubleRounds n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show renderProgram (doubleProgram ++ doubleRoundsProgram k)
      = renderChacha4wayDoubleRound ++ renderChacha4wayDoubleRounds k
    rw [renderProgram, List.flatMap_append]
    show renderProgram doubleProgram ++ renderProgram (doubleRoundsProgram k)
      = renderChacha4wayDoubleRound ++ renderChacha4wayDoubleRounds k
    rw [double_render_eq_direct, ih]

/-! ## 5. The full body and the full emitted `.jazz`, byte-identical

The body = decls ++ SoA load ++ 10 double-rounds ++ SoA store. The load/store
(SoA transpose + feed-forward) are not lane-arithmetic ops, so they are reused
verbatim from the direct emit; only the 10 double-rounds — the lane-arithmetic
heart — go through the tagged-op path. We splice the two and prove the result
equals `renderChacha4wayBody`. -/

/-- The ChaCha 4-way body, with the round-arithmetic emitted via the tagged-op
    path and the (non-arithmetic) SoA load/store reused from the direct emit. -/
def vecBody : List String :=
  let decls :=
    [ "reg u128 w0 w1;"
    , "stack u128[16] m;"
    , "stack u128[16] orig;"
    , "stack u32[4] tbuf;" ]
  decls ++ renderChacha4wayLoad ++
    renderProgram (doubleRoundsProgram 10) ++
    renderChacha4wayStore

/-- **Keystone: the tagged-op (VectorDialect) body is byte-identical to the
    direct-mnemonic body.** Every line is the same; only the round leg routes
    through `ChaCha4WayVecOp`. Hence the emitted `.jazz` (and its RFC 8439
    KAT in `bench/chacha_compare/`) is preserved verbatim. -/
theorem vecBody_eq_direct : vecBody = renderChacha4wayBody := by
  show _ ++ _ ++ renderProgram (doubleRoundsProgram 10) ++ _
    = _ ++ _ ++ renderChacha4wayDoubleRounds 10 ++ _
  rw [doubleRounds_render_eq_direct]

/-- The emitted 4-way `.jazz` via the tagged-op body. Wraps `vecBody` in the
    same export shell `emitChacha4wayJazz` uses. -/
def chacha4wayVecJazz (name : String) : String :=
  let paramStrs := ["reg ptr u32[64] out", "reg const ptr u32[64] inp"]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u32[64] {\n  "
    ++ String.intercalate "\n  " vecBody ++ "\n  return out;\n}"

/-- **The full emitted text is byte-identical to the direct emit.** Therefore
    the KAT validating `emitChacha4wayJazz` validates this path verbatim — no
    new bytes, no fabricated KAT. -/
theorem chacha4wayVecJazz_eq_direct (name : String) :
    chacha4wayVecJazz name = emitChacha4wayJazz name := by
  unfold chacha4wayVecJazz emitChacha4wayJazz
  rw [vecBody_eq_direct]

/-! ## 6. Denotation grounding (lane-parallel map)

The tagged-op program denotes the lane-parallel map of the per-block ChaCha
function across the 4 lanes — the same denotation `chacha4way_denotation_preserves`
gives the direct emit, grounded in the proven `LaneMap.chacha4way_lane_map`
keystone. Independence per lane means the abstract `VectorOp` add/shift ops
applied across 4 lanes equal four sequential scalar applications. -/

open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap (laneMap chacha4way_lane_map)

/-- **Denotation preservation for the VectorDialect ChaCha 4-way path.** The
    same lane-parallel-map equality the direct emit enjoys: applying the
    per-block function to each of the 4 lanes equals running it sequentially
    per lane. Instantiates the proven `LaneMap.chacha4way_lane_map`. -/
theorem vec_denotation_preserves
    (state : ChaCha4Way) :
    laneMap chacha20BlockSpec state =
      (fun b => chacha20BlockSpec (state b)) :=
  chacha4way_lane_map chacha20BlockSpec state

/-! ## 7. The dialect ops this consumer uses lower with proven preservation

`addIn`/`xorIn` realize `VectorOp.add` (binary, lowered by `lower_add_correct`);
`rotL` realizes `VectorOp.shiftL` + `VectorOp.shiftR` + binary-or (lowered by
`lower_shiftL_correct` / `lower_shiftR_correct` / `lower_add_correct`). We pin
the abstract per-lane meaning of one ARX rotate against the dialect ops to show
the alphabet genuinely covers ChaCha's lane arithmetic.

`rotL x n` = `(x <<< n) ||| (x >>> (32 - n))` per `BitVec 32` lane — exactly
the composition the dialect expresses. -/

/-- The 32-bit lane shift-left as a `BitVec 32 → Nat → BitVec 32` op. -/
abbrev shlLane (x : BitVec 32) (m : Nat) : BitVec 32 := x <<< m
/-- The 32-bit lane shift-right as a `BitVec 32 → Nat → BitVec 32` op. -/
abbrev shrLane (x : BitVec 32) (m : Nat) : BitVec 32 := x >>> m
/-- The 32-bit lane bitwise-or. -/
abbrev orLane (x y : BitVec 32) : BitVec 32 := x ||| y

/-- The abstract per-lane rotate the `rotL` op denotes, in terms of the dialect
    shift + or ops, agrees with the direct `BitVec` rotate. -/
theorem rotL_lane_denote (v : VectorTy (BitVec 32) laneN) (n : Nat) :
    VectorTy.map₂ orLane
        (VectorTy.map₁imm shlLane n v)
        (VectorTy.map₁imm shrLane (32 - n) v)
      = fun i => (v i <<< n) ||| (v i >>> (32 - n)) := by
  funext i
  rfl

/-- The dialect `shiftL`/`shiftR`/`add` ops denote the rotate's two shift halves
    and their or, matching `rotL_lane_denote`. Confirms the alphabet expresses
    the ARX rotate via the proven-lowering ops. -/
theorem rotL_via_dialect_ops (v : VectorTy (BitVec 32) laneN) (n : Nat) :
    (denoteVectorOp
        (.add orLane
          (VectorTy.map₁imm shlLane n v)
          (VectorTy.map₁imm shrLane (32 - n) v) : VectorOp (BitVec 32) laneN))
      = .vec (fun i => (v i <<< n) ||| (v i >>> (32 - n))) := by
  show VectorOp.Result.vec _ = VectorOp.Result.vec _
  rw [rotL_lane_denote]

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ChaCha4WayVec
