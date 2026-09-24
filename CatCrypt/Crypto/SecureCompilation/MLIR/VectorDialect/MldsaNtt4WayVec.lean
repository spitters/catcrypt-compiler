/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-!
# ML-DSA-65 / ML-KEM-768 4-way NTT through the structured VectorDialect
The lattice 4-way emit (`VIR/LatticeNttEmit.renderMldsaNtt4wayStage` /
`renderMlkemNtt4wayStage`) renders each batched Cooley–Tukey butterfly stage into
packed mnemonic strings (`#VPMULL`, `#VPADD`, `#VPSUB`). This file expresses the
stage arithmetic as ops tagged with their `VectorOp` role and proves that their
rendering equals the direct emit line for line.

## Coverage

* The butterfly ops `#VPADD`/`#VPSUB`/`#VPMULL` are the dialect `add` / `mul`
  constructors (binary pointwise).
* The dialect ops `mulHi` (`VPMULH`, high-half product) and `shiftRA` (`VPSRA`,
  signed arithmetic shift-right) used by Montgomery / Barrett reduction are given
  `BitVec`-lane semantics here, and lower with denotation preservation
  (`lower_mulHi_correct`, `lower_shiftRA_correct` in `Lowering.lean`). The 4-way
  stage does not use them.

The semantics of the rendered 4-way body is `LatticeNttEmit.runNtt4way`;
`mldsaVec_denotation_preserves` / `mlkemVec_denotation_preserves` identify the
tagged-op rendering with the program `LatticeNttEmit.ntt4wayBody`, whose run is
characterized by `LatticeNttEmit.mldsa_ntt_4way_denotation_preserves` /
`mlkem_ntt_4way_denotation_preserves`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec

open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. The 4-way lattice butterfly lane-op alphabet, tagged with its `VectorOp` role

Each constructor packages one packed AVX2 lane op of the batched butterfly
stage on `__m128i` chunk operands, recording the `VectorOp` it realizes and
rendering to the **same** mnemonic strings the direct emit uses. The lane
shape is 4 lanes of `u32` (ML-DSA) or 8 lanes of `u16` (ML-KEM); both are
covered by the same tagged-op alphabet (the mnemonic spelling differs only by
its width suffix). -/

/-- A single high-level lattice 4-way butterfly lane op. `mulPacked`/`addPacked`/
    `subPacked` are the three ops of one stage; they realize `VectorOp.mul`,
    `VectorOp.add` (with `(· + ·)`) and `VectorOp.add` (with `(· - ·)`)
    respectively. The `width` string (`"4u32"` for ML-DSA, `"8u16"` for ML-KEM)
    is carried so the render reproduces the direct emit's mnemonic spelling. -/
inductive LatticeNttVecOp where
  /-- `dst = #VPMULL_<w>(b, tw);` — packed lane multiply. Realizes
      `VectorOp.mul` carrying lane `(· * ·)`. -/
  | mulPacked (dst b tw width : String)
  /-- `dst = #VPADD_<w>(a, t);` — packed lane add. Realizes `VectorOp.add`. -/
  | addPacked (dst a t width : String)
  /-- `dst = #VPSUB_<w>(a, t);` — packed lane subtract. Realizes
      `VectorOp.add` carrying lane `(· - ·)`. -/
  | subPacked (dst a t width : String)
  deriving DecidableEq, Repr

/-! ## 2. Rendering — reproduces the *exact* direct-emit mnemonic strings

`render` produces literally the lines `renderMldsaNtt4wayStage` /
`renderMlkemNtt4wayStage` emit, so the byte-identity proof is definitional. -/

/-- Render one tagged lane op to its jasmin mnemonic line. -/
def LatticeNttVecOp.render : LatticeNttVecOp → String
  | .mulPacked dst b tw width => dst ++ " = #VPMULL_" ++ width ++ "(" ++ b ++ ", " ++ tw ++ ");"
  | .addPacked dst a t width  => dst ++ " = #VPADD_"  ++ width ++ "(" ++ a ++ ", " ++ t ++ ");"
  | .subPacked dst a t width  => dst ++ " = #VPSUB_"  ++ width ++ "(" ++ a ++ ", " ++ t ++ ");"

/-! ## 3. The 4-way stage as a `LatticeNttVecOp` program

Mirrors `renderMldsaNtt4wayStage` / `renderMlkemNtt4wayStage` one-for-one, but
as a list of abstract tagged ops + the (non-arithmetic) load/store/comment
lines reused verbatim. -/

/-- The ML-DSA stage arithmetic as a tagged-op program (the `t`/`c`/`d` lines of
    `renderMldsaNtt4wayStage`). -/
def mldsaStageArith : List LatticeNttVecOp :=
  [ .mulPacked "t" "b" "tw" "4u32"
  , .addPacked "c" "a" "t" "4u32"
  , .subPacked "d" "a" "t" "4u32" ]

/-- The ML-DSA full stage `s`, splicing the (non-arithmetic) load/comment/store
    lines from the direct emit around the tagged-op arithmetic. -/
def mldsaStageVec (s : Nat) : List String :=
  let chunkA : Nat := 2 * s
  let chunkB : Nat := 2 * s + 1
  [ "// stage " ++ toString s
  , "a = inp[:u128 " ++ toString chunkA ++ "];"
  , "b = inp[:u128 " ++ toString chunkB ++ "];" ]
  ++ mldsaStageArith.map LatticeNttVecOp.render
  ++ [ "out[:u128 " ++ toString chunkA ++ "] = c;"
     , "out[:u128 " ++ toString chunkB ++ "] = d;" ]

/-- The ML-KEM stage arithmetic as a tagged-op program (8u16 lanes). -/
def mlkemStageArith : List LatticeNttVecOp :=
  [ .mulPacked "t" "b" "tw" "8u16"
  , .addPacked "c" "a" "t" "8u16"
  , .subPacked "d" "a" "t" "8u16" ]

/-- The ML-KEM full stage `s`. -/
def mlkemStageVec (s : Nat) : List String :=
  let chunkA : Nat := 2 * s
  let chunkB : Nat := 2 * s + 1
  [ "// stage " ++ toString s
  , "a = inp[:u128 " ++ toString chunkA ++ "];"
  , "b = inp[:u128 " ++ toString chunkB ++ "];" ]
  ++ mlkemStageArith.map LatticeNttVecOp.render
  ++ [ "out[:u128 " ++ toString chunkA ++ "] = c;"
     , "out[:u128 " ++ toString chunkB ++ "] = d;" ]

/-! ## 4. Equality with the direct emit

The tagged-op stage renders to the same lines as the direct
`renderMldsaNtt4wayStage` / `renderMlkemNtt4wayStage`. -/

/-- The tagged-op ML-DSA stage equals the direct `renderMldsaNtt4wayStage` for
    every stage `s`. -/
theorem mldsaStageVec_eq_direct (s : Nat) :
    mldsaStageVec s = renderMldsaNtt4wayStage s := by
  rfl

/-- The tagged-op ML-KEM stage equals the direct `renderMlkemNtt4wayStage` for
    every stage `s`. -/
theorem mlkemStageVec_eq_direct (s : Nat) :
    mlkemStageVec s = renderMlkemNtt4wayStage s := by
  rfl

/-- The full ML-DSA body, rendered with each of the 8 stages routed through the
    tagged-op path, equals the direct `renderMldsaNtt4wayBody`. -/
def mldsaVecBody : List String :=
  [ "reg u128 a b c d t tw;" ] ++ [ "tw = inp[:u128 64];" ]
    ++ (List.range 8).flatMap mldsaStageVec

/-- The tagged-op ML-DSA body equals the direct `renderMldsaNtt4wayBody`. -/
theorem mldsaVecBody_eq_direct : mldsaVecBody = renderMldsaNtt4wayBody := by
  rfl

/-! ## 5. The listed butterfly ops as dialect `add`/`mul`

The dialect `add` / `mul` ops at `BitVec 32` lanes denote the pointwise lane
sum, difference and wrapping product that the packed ops of the ML-DSA stage
compute. -/

/-- The lattice-lane shape this consumer denotes over: 4 lanes (ML-DSA) of the
    coefficient word. We pin the alphabet against `BitVec 32` lanes. -/
abbrev mldsaLaneN : Nat := 4

/-- The packed add lane denotes the dialect `add` op pointwise. -/
theorem addPacked_denote (v w : VectorTy (BitVec 32) mldsaLaneN) :
    denoteVectorOp (.add (· + ·) v w : VectorOp (BitVec 32) mldsaLaneN)
      = .vec (fun i => v i + w i) := rfl

/-- The packed sub lane denotes the dialect `add` op carrying `(· - ·)`. -/
theorem subPacked_denote (v w : VectorTy (BitVec 32) mldsaLaneN) :
    denoteVectorOp (.add (· - ·) v w : VectorOp (BitVec 32) mldsaLaneN)
      = .vec (fun i => v i - w i) := rfl

/-- The packed mul lane denotes the dialect `mul` op pointwise. -/
theorem mulPacked_denote (v w : VectorTy (BitVec 32) mldsaLaneN) :
    denoteVectorOp (.mul (· * ·) v w : VectorOp (BitVec 32) mldsaLaneN)
      = .vec (fun i => v i * w i) := rfl

/-! ## 6. The NEW ops `mulHi` / `shiftRA` — Montgomery / Barrett reduction

The standard Montgomery reduction of a signed product `a` modulo `q` with
Montgomery factor `qinv` (mod `2^16`) on a `BitVec 16` lane is

  `m  = mullo (a, qinv)`        -- low-half product
  `t  = mulhi (m, q)`           -- high-half product   ← VPMULH
  `r  = (a >>>s 16) - t`        -- signed shift + sub   ← VPSRA

Barrett reduction is the dual shape (`mulhi` against a precomputed `⌊2^k/q⌋`,
then a `shiftRA` to take the quotient estimate). We pin the per-lane semantics
of the two NEW dialect ops against these standard recurrences. The lane ops are
the truncating high-half multiply and `BitVec.sshiftRight` (arithmetic). -/

/-- High-half `u16×u16 → u16` product on a `BitVec 16` lane (`VPMULHW`):
    take the full 32-bit product and keep its high 16 bits. -/
def mulHi16 (a b : BitVec 16) : BitVec 16 :=
  BitVec.extractLsb' 16 16 (a.setWidth 32 * b.setWidth 32)

/-- Signed (arithmetic) shift-right on a `BitVec 16` lane (`VPSRAW`). -/
def shiftRA16 (a : BitVec 16) (m : Nat) : BitVec 16 := a.sshiftRight m

/-- The dialect `mulHi` op denotes the per-lane high-half product
    `mulHi16` pointwise — the `VPMULH` leg of Montgomery / Barrett. Lowers
    with proven denotation preservation (`lower_mulHi_correct`). -/
theorem mulHi_denote (v w : VectorTy (BitVec 16) 8) :
    denoteVectorOp (.mulHi mulHi16 v w : VectorOp (BitVec 16) 8)
      = .vec (fun i => mulHi16 (v i) (w i)) := rfl

/-- The dialect `shiftRA` op denotes the per-lane signed arithmetic shift
    `shiftRA16` pointwise — the `VPSRA` leg of Montgomery / Barrett. Lowers
    with proven denotation preservation (`lower_shiftRA_correct`). -/
theorem shiftRA_denote (m : Nat) (v : VectorTy (BitVec 16) 8) :
    denoteVectorOp (.shiftRA shiftRA16 m v : VectorOp (BitVec 16) 8)
      = .vec (fun i => shiftRA16 (v i) m) := rfl

/-- The two NEW ops both lower to a proven per-lane scalar expansion. This
    bundles the `Lowering.lean` lowering theorems at the lattice-lane instances, so the
    abstract → per-lane-scalar leg is covered for the reduction ops too. -/
theorem newOps_lower_correct (v w : VectorTy (BitVec 16) 8) (m : Nat) :
    (lower (0 : BitVec 16) (.mulHi mulHi16 v w)).map (·.denote)
        = some (fun i => mulHi16 (v i) (w i))
      ∧ (lower (0 : BitVec 16) (.shiftRA shiftRA16 m v)).map (·.denote)
        = some (fun i => shiftRA16 (v i) m) := by
  refine ⟨?_, ?_⟩
  · exact lower_mulHi_correct (0 : BitVec 16) mulHi16 v w
  · exact lower_shiftRA_correct (0 : BitVec 16) shiftRA16 m v

/-! ## 7. The tagged-op bodies as `ntt4wayBody`

The tagged-op renderings are the renderings of the program
`LatticeNttEmit.ntt4wayBody`, whose semantics `runNtt4way` computes the
Cooley–Tukey butterflies (`mldsa_ntt_4way_denotation_preserves` /
`mlkem_ntt_4way_denotation_preserves`). -/

/-- The tagged-op ML-DSA body is the rendering of `ntt4wayBody 64`, and running
    that program on 4 lanes of `u32` writes the butterfly of input chunks `2p`,
    `2p+1` with the twiddle chunk 64 to output chunks `2p`, `2p+1` for `p < 8`. -/
theorem mldsaVec_denotation_preserves :
    mldsaVecBody = (ntt4wayBody 64).map (Ntt4wayInstr.render "4u32") ∧
    ∀ s0 : Ntt4wayState 4 32,
      (∀ p < 8, ∀ j : Fin 4,
        ((runNtt4way s0 (ntt4wayBody 64)).out (4 * (2 * p) + j),
          (runNtt4way s0 (ntt4wayBody 64)).out (4 * (2 * p + 1) + j))
        = CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass.ctButterfly
            (s0.inp (4 * 64 + j)) (s0.inp (4 * (2 * p) + j)) (s0.inp (4 * (2 * p + 1) + j))) ∧
      (∀ i, 4 * 16 ≤ i → (runNtt4way s0 (ntt4wayBody 64)).out i = s0.out i) :=
  ⟨mldsaVecBody_eq_direct.trans mldsa_ntt_4way_denotation_preserves.1.symm,
    mldsa_ntt_4way_denotation_preserves.2⟩

/-- Each tagged-op ML-KEM stage is the rendering of `ntt4wayStage s`, and running
    `ntt4wayBody 32` on 8 lanes of `u16` writes the butterfly of input chunks `2p`,
    `2p+1` with the twiddle chunk 32 to output chunks `2p`, `2p+1` for `p < 8`. -/
theorem mlkemVec_denotation_preserves :
    (∀ s, mlkemStageVec s = (ntt4wayStage s).map (Ntt4wayInstr.render "8u16")) ∧
    ∀ s0 : Ntt4wayState 8 16,
      (∀ p < 8, ∀ j : Fin 8,
        ((runNtt4way s0 (ntt4wayBody 32)).out (8 * (2 * p) + j),
          (runNtt4way s0 (ntt4wayBody 32)).out (8 * (2 * p + 1) + j))
        = CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass.ctButterfly
            (s0.inp (8 * 32 + j)) (s0.inp (8 * (2 * p) + j)) (s0.inp (8 * (2 * p + 1) + j))) ∧
      (∀ i, 8 * 16 ≤ i → (runNtt4way s0 (ntt4wayBody 32)).out i = s0.out i) :=
  ⟨fun s => (mlkemStageVec_eq_direct s).trans (ntt4wayStage_render_mlkem s).symm,
    mlkem_ntt_4way_denotation_preserves.2⟩

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec
