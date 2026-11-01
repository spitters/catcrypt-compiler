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
| `ComToTileIR.lean` | `emitTileOp`, `emitTileFuncAt` (a `cuda_tile.module` with one `cuda_tile.entry` kernel at tile type `n × i w`: pointer arguments `%pa`, `%pb`, `%pr`, `load_ptr_tko`/`store_ptr_tko` of the input and result tiles), `emitTileFunc` (at `8xi64`), `emitTileFunc?` (`none` for a block with `permxv`, `bcast` or `hadd`), `bbMulTileIR`; `mulhs` is emitted as `mulhii` with sign corrections; `main` writes the text to a file |
| `TileVectorUnify.lean` | `tile_eq_vectorTy` (`Tile n w = VectorTy (BitVec w) n`, by `rfl`), `lane_add_eq_map₂`, `lane_mul_eq_map₂` |
| `VectorBackendBridge.lean` | 4×32 bridges: `v128Pack32_lane`, `vpadd32_com_is_tile_lowering`, `packAvx2Com_is_tile_lowering` (x86, packed `BitVec 128` carrier), `ninst_is_tile_lowering` (NEON), `rvinst_is_tile_lowering` (RVV) |
| `VectorBackendBridgeCom.lean` | `packAvx2Com` and its instances as `Com jasminDialect` over `reg 128`; `packAvx2Com_denote`, `avx2ArithCore_realized` |
| `ZmmArithBridge.lean` | 8×64 bridges: `zmmOfLanes_zmmLane`, `zmmPackQ_is_tile_lowering`, `zmmPermXvar` (a semantic function, no `Com` op) with `zmmPermXvar_is_tile_permxv`, `zmm_core_consolidates` |
| `ZmmArithBridgeCom.lean` | `packBinCom` and its instances over `reg 512`; `packBinCom_denote`, `zmmArithCore_realized`, `vpsllvqCom_denote`, `vpsrlvqCom_denote` |
| `ZmmArithBridgeComEmit.lean` | AT&T `.s` strings for these programs through `renderVpackZmmCom` and `frameAsmFunction`; `vpaddqBodyLines_eq`, `vpmullqBodyLines_eq`, `vpxorqCom_renders`, `vpsllvqCom_renders` (rendered lines, by `native_decide`) |
| `TileS16HighMul.lean` | `montMulS16Spec`, `tileMontMulS16` with `tileMontMulS16_denote` (by `rfl`) and `tileMontMulS16_kat`; `vpmulhw16W_lane`, `vpmulhw_com_is_tile_lowering`, `sqdmulh_is_tile_lowering`, `vmulh_is_tile_lowering`, `tri_isa_mulhs_consolidates` |
| `TileS16HighMulCom.lean` | `s16HighMulCom`, the `VPMULHW` step as `Com jasminDialect`; `s16HighMulCom_denote` |
| `TileDialectLower.lean` | `lowerCom` (straight-line `Com tileDialect` to a `TileOp` block over named registers) with `lowerCom_correct` for every program; `bbMulTileCom` (the BabyBear multiply as a `Com tileDialect` program) with `bbMulTileCom_denote`, `bbMulTileCom_lower_isSome`, `bbMulTileCom_lowered_denote`; `bbMulTileComIR`, its `cuda_tile` text emitted through the dialect |
| `CudaTileSemantics.lean` | an AST for the `cuda_tile` kernels `emitTileFuncAt` prints, their semantics per the CUDA Tile IR specification (sections cited per op) as a map from a memory and three pointers to the final memory, `print`, `parse`; `emitTileFuncAt_eq_print`, `emitTileFunc_eq_print`, `parse_print`, `print_injective`; `mulhs_eq_mulhu_sub` (signed high half from `mulhii`); `run_toAst` (for `SupportedFunc` blocks and `ShapeOk` shapes the kernel stores the `runTileBlock` result and changes nothing else), `emitTileFunc?_eq_some`; `bbMulAst_run`, `bbMulTileComIR_correct` (the emitted BabyBear text, as printed, stores `x i * y i mod p` at `pr + i`) |
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

## Facts that are easy to misread

- The three high-multiply bridges concern the high half `mulhs`, not
  `tileMontMulS16`.
- `sqdmulh_is_tile_lowering` holds by `rfl` for the NEON model op `mulhs`, the plain
  signed high half. The encoder emits `SQDMULH`, which doubles and saturates; no
  theorem relates the two.
- The lane-moving ops `permxv`, `bcast`, `hadd` have no `cuda_tile` form in the
  emitter: `emitTileFunc?` rejects a block containing one, and `emitTileFunc`
  prints no line for it and binds the destination to `%undef`.
- `CudaTileSemantics.Func.run` is the semantics of one tile block over a memory
  addressed in elements, with pointer arithmetic on unbounded naturals; the
  specification's undefined results on pointer overflow and its limits on tile
  size beyond `ShapeOk` are not modelled. Load and store sections are cited by
  anchor (`#cuda-tile-load-ptr-tko`, `#cuda-tile-store-ptr-tko`), not by number.
- The emitted text is not checked by the `cuda-tile` toolchain in the package.
- No theorem in this directory relates the strings of `ZmmArithBridgeComEmit.lean`
  to a machine model.
- The bridges are per instruction; no theorem in this directory composes a block of
  packed operations with `lowerRegBlock_denote`.

See [AGENTS.md](../AGENTS.md) for the compiler as a whole,
[ARMBackend/AGENTS.md](../ARMBackend/AGENTS.md) and
[RISCVBackend/AGENTS.md](../RISCVBackend/AGENTS.md) for the NEON and RVV models, and
[CAPABILITIES.md](../../../../CAPABILITIES.md) for per-primitive status.
