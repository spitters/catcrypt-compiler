# `MLIR/VectorDialect/`: directory index

This directory holds a carrier-polymorphic vector op alphabet `VectorOp α n` over
lane functions `VectorTy α n := Fin n → α`, its denotation, two lowerings of it (to
a per-lane store program `ScalarExpansion`, and to AVX-512 mnemonic instructions
`AVX512Inst`), a lowering-selector layer, an auto-vectorizer over a small surface
AST, consumer modules that restate existing SIMD emitters (ChaCha20 4-way, ML-DSA
and ML-KEM NTT stages, GFNI, VAES, Keccak ρ, Poseidon2, a 10-limb Curve25519 field)
through the alphabet, `BitVec` models of x86 SIMD intrinsics, and two leaf
simulations on `../../../Jasmin/JasminCoqSemMirror.lean`. None of the
lowerings here produces `Com`; a `BitVec`-lane `vector` dialect in the VIR
framework is `../../VIR/MlirVectorDialect.lean`.

Names below are relative to `CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect`.
`Types.lean`, `Ops.lean`, `Denote.lean`, `Lowering.lean`, `LoweringAVX512.lean` and
`LoweringChoice.lean` declare into this namespace itself (with the sub-namespaces
`VectorTy`, `VectorOp` and `AVX512Inst`); `X86Intrinsics.lean` into
`X86Intrinsics`; `AutoVectorize/Patterns.lean`, `AutoVectorize/Detection.lean` and
`AutoVectorize/Vectorize.lean` into `AutoVectorize`; `AutoVectorize/Demo.lean` into
`AutoVectorize.Demo`. The remaining modules declare into `<ModuleName>`.

## The dialect and its lowerings

| Module | Contents |
|---|---|
| `Types.lean`, `Ops.lean`, `Denote.lean` | `VectorTy`, `VectorOp` (broadcast, extract, insert, add, mul, fma, shuffle, reduce, shiftL, shiftR, mulHi, shiftRA, affineByte, aesRound), `Result`, `denoteVectorOp` and `denote_*` lemmas (none for fma, shuffle, reduce) |
| `Lowering.lean` | `lower init : VectorOp α n → Option (ScalarExpansion α n)`, one store per lane; `lower_*_correct` for broadcast, add, mul, shiftL, shiftR, mulHi, shiftRA, affineByte, aesRound; `denoteVectorOp_eq_lower_add`. `extract` and `reduce` lower to `none` |
| `LoweringAVX512.lean` | `lowerAVX512`, `renderAVX512`, `AVX512Inst.denote512` (semantics from mnemonic family and width), `AVX512Inst.valid`, `AVX512Inst.exts`; `lowerInst_denote`, `lowerAVX512_correct`, `lowerAVX512_map_denote`; `binMnem_laneSem_eq`, `shiftMnem_laneSem_eq`, `vpmulhw_laneSem`, `vpmulhuw_laneSem`; the rejections `lowerAVX512_mulHiS_w16u32`, `lowerAVX512_mulHiU_w8u64`, `lowerAVX512_mulLo_w64u8`, `lowerAVX512_shift_w64u8`; the feature requirements `exts_mulLo_w8u64`, `exts_add_w64u8`, `exts_perm_w64u8` |
| `LoweringAVX512Demo.lean` | `add_avx512_eq`, `add_avx2_avx512_agree`, `mldsa_mulHi_avx512_eq`, `mldsa_shiftRA_avx512_eq`, and the rendered lines `add_avx512_render`, `mldsa_reduction_avx512_render`, on lane operations of `MldsaNtt4WayVec.lean` |
| `LoweringChoice.lean` | `LoweringEquivalenceClass`, `selectLowering`, `selectLoweringX86` (cost from `../../../Optimizer/X86CostModel.lean`), `lowerWithSelector`; `lowerWithSelector_eq_lower`, `lowerWithSelector_denote_of_classEquiv`; demo fixtures marked `@bench-only` with `demo_autoPicks_vectorized` and `demo_denote_preserved` |
| `X86Intrinsics.lean` | `BitVec` functions for PXOR, PSHUFB (`pshufb_128`, `vpshufb_256`), byte shifts, compares, broadcasts and extracts, with sanity checks; consumed by `../../X86Backend/` modules, not by the lowerings above |

## Auto-vectorizer

- `AutoVectorize/Patterns.lean`: `VectorizablePattern` (lanewiseAdd, lanewiseMul,
  dotProduct, broadcast).
- `AutoVectorize/Detection.lean`: `SurfaceCom` and `detectPattern`; no theorem.
- `AutoVectorize/Vectorize.lean`: `vectorize` and
  `lanewiseAdd_vectorize_denotation_preserves`. The other three patterns are recorded
  as the propositions `Phase2LanewiseMulVectorizes`, `Phase2DotProductVectorizes` and
  `Phase2BroadcastVectorizes`; no module proves them or takes them as hypotheses, and
  `vectorizeWithStatus` reports `isProven = false` for those patterns.
- `AutoVectorize/Demo.lean`: `hmacXorPad_vectorize_correct` on a freestanding model
  of the HMAC pad XOR.

## Consumer modules

| Module | Text identity with the existing emitter | Denotation result |
|---|---|---|
| `ConsumerDemo.lean` | none | `vpadd4u32_abstract_eq`, `vpadd4u32_lowered_eq` |
| `ChaCha4WayVec.lean` | `chacha4wayVecJazz_eq_direct`, `vecBody_eq_direct` | `vec_denotation_preserves` (an instance of `LaneMap.chacha4way_lane_map`) |
| `MldsaNtt4WayVec.lean` | `mldsaStageVec_eq_direct`, `mldsaVecBody_eq_direct` | `mldsaVec_denotation_preserves` / `mlkemVec_denotation_preserves` (the rendering is `LatticeNttEmit.ntt4wayBody`, whose run writes Cooley–Tukey butterflies); `newOps_lower_correct` |
| `GfniLaneVec.lean` | `render_eq_direct_mulb` and the affine variants | `mulb_packs_to_denoteGfni` |
| `VAESLaneVec.lean` | `render_eq_direct` | `aesRound_eq_denoteVAES2` |
| `KeccakRhoVec.lean` | none | `rho_denotation_preserves` (lane map) |
| `Poseidon2LaneVec.lean` | none | `sbox_denotation_preserves` (lane map) |
| `RistrettoFieldVec.lean` | none | `eval2625_reduce19`, `mul2625_decode`, `mul2625x4_decode`, `edwardsAdd2625_decode` |
| `QruovLeafJasminSim.lean`, `UovLeafJasminSim.lean` | none | `gf127Mul_jasmin_sem_eq_smallInputs`, `gf256MulStep_jasmin_sem_eq_smallInputs` |

The lane-map results are `../../VIR/LaneMap.lean`
instances: applying a function to each lane equals applying it per lane. They do not
refer to the rendered text of the same module.

## Entry-point theorems

| Result | Declaration | Hypotheses and scope | File |
|---|---|---|---|
| Per-lane lowering | `lower_add_correct` and the other `lower_*_correct` | one constructor each, any carrier and lane count | `Lowering.lean` |
| Selector correctness | `lowerWithSelector_denote_of_classEquiv` | the selector returns a class member (`ClassMemberSelector`), `build op = some cls`, every candidate in `cls` denotes `spec` | `LoweringChoice.lean` |
| Vectorizing the `lanewiseAdd` pattern | `AutoVectorize.lanewiseAdd_vectorize_denotation_preserves` | the `lanewiseAdd` pattern only | `AutoVectorize/Vectorize.lean` |
| AVX-512 lowering | `lowerAVX512_correct` | the instruction semantics `denote512` is per lane, determined by mnemonic and width; `VGF2P8AFFINEQB` / `VAESENC` take the byte affine map and AES round as a `LeafSem` parameter | `LoweringAVX512.lean` |
| Packed field multiply | `RistrettoFieldVec.mul2625_decode` | integer limbs, no lane overflow | `RistrettoFieldVec.lean` |
| Packed Edwards addition | `RistrettoFieldVec.edwardsAdd2625_decode` | the limb vector `dL` decodes to `d` | `RistrettoFieldVec.lean` |

## Facts that are easy to misread

- No theorem relates the text of `renderAVX512` to `denote512`; masking, memory
  operands and the EVEX encoding are not modelled.
- The `*_eq_direct` theorems are string equalities with the existing emitters; no
  theorem in this directory relates that text to a machine model.
- The limbs of `RistrettoFieldVec` are unbounded integers, and no theorem connects
  them to the `BitVec 64` lane words of the same module. `ct_data_indep` states that
  the op list `mulReduceOps` contains no data-dependent op of the `PackedFieldOp`
  alphabet; the list is not derived from `mul2625`, and no leakage semantics is
  given.
- The two leaf simulations are `native_decide` checks of a Boolean agreement function
  on bounded inputs: all residues below 127 for QR-UOV, and 4-bit inputs for one round
  of the UOV GF(256) multiply.

See [AGENTS.md](../../AGENTS.md) for the compiler as a whole and
[CAPABILITIES.md](../../../../../CAPABILITIES.md) for per-primitive status.
