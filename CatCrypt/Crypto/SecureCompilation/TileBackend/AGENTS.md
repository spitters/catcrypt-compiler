# `TileBackend/`: directory index

This directory holds a shape-generic lane model `Tile n w := Fin n → BitVec w` with
named tile states and a small op set (`TileModel.lean`), a lowering into it from the
register-arithmetic alphabet `RegInstr` proved for every block and every shape, a
text emitter from tile programs to the NVIDIA `cuda_tile` MLIR dialect, and bridge
theorems stating that the packed SIMD operations of the x86 (AVX2, AVX-512), NEON
and RVV models, viewed lane by lane, are instances of that lowering. It also holds
the ML-KEM signed 16-bit high multiply across the three instruction sets, and
`Com jasminDialect` programs for the packed operations with an AT&T `%zmm` emitter.

Names below are relative to `CatCrypt.Crypto.SecureCompilation.TileBackend`. Every
module declares into `TileBackend.<ModuleName>`.

## Modules

| Module | Contents |
|---|---|
| `TileModel.lean` | `Tile`, `TileState`, `TileOp` (elementwise arithmetic and shifts, `mulhs`, and the lane-moving `permxv`, `bcast`, `hadd`), `evalTileOp`, `runTileBlock`; `permxv_denote`, `bcast_denote`, `hadd_denote`; `RegInstr`, `evalRegInstr`, `lowerRegInstr`, `lowerRegBlock` with `lowerRegInstr_denote` and `lowerRegBlock_denote`; the BabyBear multiply `bbMulTile`, `bbMulReg` with `bbMulTile_denote`, `bbMulReg_lowered_denote` and the KAT `bbMulTile_kat` |
| `ComToTileIR.lean` | `emitTileOp`, `emitTileFunc`, `bbMulTileIR` (the emitted text of `bbMulTile`); `ir_has_func_and_type`, `ir_has_field_ops` (substring checks by `native_decide`); `main` writes the text to a file |
| `TileVectorUnify.lean` | `tile_eq_vectorTy` (`Tile n w = VectorTy (BitVec w) n`, by `rfl`), `lane_add_eq_map₂`, `lane_mul_eq_map₂` |
| `VectorBackendBridge.lean` | 4×32 bridges: `v128Pack32_lane`, `vpadd32_com_is_tile_lowering`, `packAvx2Com_is_tile_lowering` (x86, packed `BitVec 128` carrier), `ninst_is_tile_lowering` (NEON), `rvinst_is_tile_lowering` (RVV) |
| `VectorBackendBridgeCom.lean` | `packAvx2Com` and its instances as `Com jasminDialect` over `reg 128`; `packAvx2Com_denote`, `avx2ArithCore_realized` |
| `ZmmArithBridge.lean` | 8×64 bridges: `zmmOfLanes_zmmLane`, `zmmPackQ_is_tile_lowering`, `zmmPermXvar` (a semantic function, no `Com` op) with `zmmPermXvar_is_tile_permxv`, `zmm_core_consolidates` |
| `ZmmArithBridgeCom.lean` | `packBinCom` and its instances over `reg 512`; `packBinCom_denote`, `zmmArithCore_realized`, `vpsllvqCom_denote`, `vpsrlvqCom_denote` |
| `ZmmArithBridgeComEmit.lean` | AT&T `.s` strings for these programs through `renderVpackZmmCom` and `frameAsmFunction`; `vpaddqBodyLines_eq`, `vpmullqBodyLines_eq`, `vpxorqCom_renders`, `vpsllvqCom_renders` (rendered lines, by `native_decide`) |
| `TileS16HighMul.lean` | `montMulS16Spec`, `tileMontMulS16` with `tileMontMulS16_denote` (by `rfl`) and `tileMontMulS16_kat`; `vpmulhw16W_lane`, `vpmulhw_com_is_tile_lowering`, `sqdmulh_is_tile_lowering`, `vmulh_is_tile_lowering`, `tri_isa_mulhs_consolidates` |
| `TileS16HighMulCom.lean` | `s16HighMulCom`, the `VPMULHW` step as `Com jasminDialect`; `s16HighMulCom_denote` |
| `TileDialectLower.lean` | `lowerCom` (straight-line `Com tileDialect` to a `TileOp` block over named registers) with `lowerCom_correct` for every program; `bbMulTileCom` (the BabyBear multiply as a `Com tileDialect` program) with `bbMulTileCom_denote`, `bbMulTileCom_lower_isSome`, `bbMulTileCom_lowered_denote`; `bbMulTileComIR`, its `cuda_tile` text emitted through the dialect |
| `TileArithCorrect.lean` | `bbMulWord_toNat` (`bbMulWord a b = a · b mod p` for `a, b < p`), `montMulS16Spec_exact`, `montMulS16Spec_mul_R_modEq` (`r · 2^16 ≡ a · b mod 3329`, all inputs), `montMulS16Spec_abs_lt` (`|r| < 3329` when `|a · b| < 3329 · 2^15`) |

## Entry-point theorems

| Result | Declaration | Hypotheses and scope | File |
|---|---|---|---|
| Lowering `RegInstr` to tiles | `TileModel.lowerRegBlock_denote` | every `(n, w)`, state and straight-line block: `runTileBlock s (lowerRegBlock blk) = runRegBlock s blk` | `TileModel.lean` |
| BabyBear multiply on every lane | `TileModel.bbMulReg_lowered_denote` | any lane count; the target is `bbMulWord` per lane | `TileModel.lean` |
| x86 AVX2 packed op as tile op | `VectorBackendBridge.vpadd32_com_is_tile_lowering` | every `JasminBinOp`, one instruction, inputs in registers `"a"`, `"b"` | `VectorBackendBridge.lean` |
| NEON and RVV ops as tile ops | `VectorBackendBridge.ninst_is_tile_lowering`, `VectorBackendBridge.rvinst_is_tile_lowering` | one instruction with `ninstToReg i = some r` (resp. `rvinstToReg`); shifts and moves map to `none` | `VectorBackendBridge.lean` |
| AVX-512 packed op and permute | `ZmmArithBridge.zmm_core_consolidates` | every `JasminBinOp`; the permute is `zmmPermXvar` | `ZmmArithBridge.lean` |
| High multiply on three ISAs | `TileS16HighMul.tri_isa_mulhs_consolidates` | one instruction per ISA, at `Tile 8 16` | `TileS16HighMul.lean` |

## What is not proved

- The three high-multiply bridges concern the high half `mulhs`, not
  `tileMontMulS16`.
- `sqdmulh_is_tile_lowering` holds by `rfl` for the NEON model op `mulhs`, the plain
  signed high half. The encoder emits `SQDMULH`, which doubles and saturates; no
  theorem relates the two.
- `ComToTileIR.lean` emits from a `TileOp` list (reached from `Com tileDialect`
  through `TileDialectLower.lowerCom`), with the tile type fixed to `8xi64`. No theorem in this directory relates the emitted text to
  `TileModel`, and the text is not checked by the `cuda_tile`
  toolchain in the package.
- No theorem in this directory relates the strings of `ZmmArithBridgeComEmit.lean`
  to a machine model.
- The bridges are per instruction; no theorem in this directory composes a block of
  packed operations with `lowerRegBlock_denote`.

See [AGENTS.md](../AGENTS.md) for the compiler as a whole,
[ARMBackend/AGENTS.md](../ARMBackend/AGENTS.md) and
[RISCVBackend/AGENTS.md](../RISCVBackend/AGENTS.md) for the NEON and RVV models, and
[CAPABILITIES.md](../../../../CAPABILITIES.md) for per-primitive status.
