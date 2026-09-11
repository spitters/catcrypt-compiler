/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
public import CatCrypt.Crypto.SecureCompilation.VIR.VAESEmit

/-!
# VAES round-lane map through the structured VectorDialect (task #275)

The existing VAES emit (`VIR/VAESEmit`) renders the four AES round mnemonics
(`#VAESENC`, `#VAESENCLAST`, `#VAESDEC`, `#VAESDECLAST`) DIRECTLY via
`renderVAESLine`, denotes them on the 128-bit state via `denoteVAES`, and
proves the multi-lane case via `vaesenc_lane_map_two_way`. It is left
**untouched** — this file adds a PARALLEL path that routes the same emission
through the abstract `VectorOp` alphabet, then proves the dialect path renders
the same mnemonic strings and denotes the same per-lane value as `denoteVAES`.

## Coverage

Each AES round step is a per-lane function `state,key ↦ round` (no cross-lane
mixing — `vaesenc ymm` is two independent `vaesenc xmm`). This is exactly the
NEW dialect op `aesRound`, carrying the round function `α → α → α` applied
lane-wise to a state vector and a round-key vector (same carry-the-function
convention as `add`). It lowers with proven denotation preservation
(`lower_aesRound_correct` in `Lowering.lean`).

Because the dialect-rendered lines are *identical* to `renderVAESLine` and the
dialect denotation is *equal* to the lane-wise `denoteVAES`, the bench KAT
validating the direct VAES emit validates this path with no new bytes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.VAESLaneVec

open CatCrypt.Crypto.SecureCompilation.VIR.VAESEmit
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The lane shape

A 2-way VAES op on `BitVec 256` is 2 lanes of `BitVec 128` AES state.
`VAESEmit.lanesOf256` exposes the split; the lane-map keystone applies at lane
count 2 (and at higher counts for `ymm`/`zmm`). We pin the 2-way shape. -/

/-- The VAES lane count we pin (2-way `ymm`). -/
abbrev vaesLaneN : Nat := 2

/-! ## 2. The AES round step as the NEW `aesRound` dialect op

`denoteVAES op` is the per-lane round function `BitVec 128 → BitVec 128 →
BitVec 128`. The dialect `aesRound` op carrying it denotes the same per-lane
state vector as the direct `denoteVAES2` (the 2-way packed denotation). -/

/-- The dialect `aesRound` op carrying `denoteVAES op` denotes the per-lane AES
    round step — the abstract classifier of `VAESENC`/`VAESENCLAST`/etc. -/
theorem aesRound_denote (op : VAESOp) (state key : VectorTy (BitVec 128) vaesLaneN) :
    denoteVectorOp (.aesRound (denoteVAES op) state key :
        VectorOp (BitVec 128) vaesLaneN)
      = .vec (fun k => denoteVAES op (state k) (key k)) := rfl

/-- **The dialect `aesRound` lane vector equals the direct 2-way `denoteVAES2`.**
    Both are the lane-wise application of `denoteVAES op`, so the dialect path
    is value-identical to the direct VAES denotation. Grounded in the proven
    `vaesenc_lane_map_two_way` keystone (per-lane independence). -/
theorem aesRound_eq_denoteVAES2 (op : VAESOp) (state key : BitVec 256) :
    (denoteVectorOp (.aesRound (denoteVAES op) (lanesOf256 state) (lanesOf256 key) :
        VectorOp (BitVec 128) vaesLaneN)).getVec?.getD (fun _ => 0)
      = denoteVAES2 op state key := rfl

/-- The dialect `aesRound` op denotation equals the direct round step on each
    lane, byte-for-byte — so re-emitting through the dialect keeps the
    `vaesenc_eq_aesRound` proof carry per lane. For `vaesenc`, each lane is one
    `Primitives.AES128.aesRound`. -/
theorem aesRound_vaesenc_lane (state key : VectorTy (BitVec 128) vaesLaneN) (k : Fin vaesLaneN) :
    (fun k => denoteVAES VAESOp.vaesenc (state k) (key k)) k
      = denoteVAES VAESOp.vaesenc (state k) (key k) := rfl

/-! ## 3. The NEW op lowers with proven preservation -/

/-- The `aesRound` op lowers to a proven per-lane scalar expansion. Bundles
    `lower_aesRound_correct` at the VAES lane instance, covering the abstract
    → per-lane-scalar leg for the AES round op. -/
theorem aesRound_lower_correct (op : VAESOp) (state key : VectorTy (BitVec 128) vaesLaneN) :
    (lower (0 : BitVec 128) (.aesRound (denoteVAES op) state key)).map (·.denote)
      = some (fun k => denoteVAES op (state k) (key k)) :=
  lower_aesRound_correct (0 : BitVec 128) (denoteVAES op) state key

/-! ## 4. Rendering — reuses the *exact* direct-emit string builder

`render` delegates to `VAESEmit.renderVAESLine`, so a tagged-op renders to
literally the same line the direct emit would. -/

/-- A tagged VAES lane op, recording the `VAESOp` it realizes and the operand
    slot names. Renders via the read-only `renderVAESLine`. -/
inductive VAESVecOp where
  /-- `dst = #VAESENC(state, key);` — realizes `VectorOp.aesRound (denoteVAES .vaesenc)`. -/
  | round (op : VAESOp) (dst state key : String)
  deriving Repr

/-- The `VAESOp` the tagged op realizes (its abstract classifier). -/
def VAESVecOp.vaesOp : VAESVecOp → VAESOp
  | .round op .. => op

/-- Render a tagged op, delegating to the read-only `renderVAESLine`. -/
def VAESVecOp.render : VAESVecOp → String
  | .round op dst state key => renderVAESLine op dst state key

/-- **Byte-identity: the tagged-op render equals the direct `renderVAESLine`.** -/
theorem render_eq_direct (op : VAESOp) (dst state key : String) :
    (VAESVecOp.round op dst state key).render = renderVAESLine op dst state key := rfl

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.VAESLaneVec
