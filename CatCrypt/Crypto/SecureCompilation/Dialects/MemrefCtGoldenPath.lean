/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasminDenote


@[expose] public section
set_option autoImplicit false

/-!
# Public-indexed array access, lifted to the neutral `memref` dialect

The `CtMemoryGoldenPath` public-indexed coefficient load/store (`stackLoad`/`stackStore`
on a public index — the NTT/coefficient pattern) re-expressed one level up as
`Com memrefDialect`, connected down through the *proven* unconditional `memref → jasmin`
lowering. The neutral `memref` `load`/`store` ops denote *exactly* the jasmin
`stackGet`/`stackSet` image, so denote=spec ports by `rfl` and `lowerMemrefToJasmin_denote`
carries it to the jasmin layer.

This is the `memref`-dialect analogue of the `arith`-dialect lift: the array-access
primitive now lives above the waist, upstream-aligned. (As at the jasmin level, the
*backend emit* of array load/store is the documented gap — the neutral AArch64/RISC-V
`comToReg` backends lower the `reg`-only `SupportedOp` alphabet, not `stackLoad`; a
constant-time gather/scatter lowering closes it. The CT noninterference of the public-index
loop lives in `CtMemoryGoldenPath` via `ArrayLoopCT`.)
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.MemrefCtGoldenPath

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.Memref

/-- **The neutral-`memref` coefficient load.** `a[i]` over `[buf 16 256, i64]`,
    the upstream-aligned twin of `CtMemory.coeffLoadCom`. -/
def coeffLoadMemrefCom : Com memrefDialect [.buf 16 256, .int 64] (.int 16) :=
  .var (.mk (.load 16 256) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- Value proof — `rfl`: the load denotes the functional array read `stackGet a i`. -/
theorem coeffLoadMemrefCom_denote (src : Fin 256 → BitVec 16) (i : BitVec 64) :
    coeffLoadMemrefCom.denote (.cons src (.cons i .nil)) = stackGet src i.toNat := rfl

/-- **The neutral-`memref` coefficient store.** `a[i] := v` over `[buf 16 256, i64, i16]`,
    returning the updated buffer — the twin of `CtMemory.coeffStoreCom`. -/
def coeffStoreMemrefCom : Com memrefDialect [.buf 16 256, .int 64, .int 16] (.buf 16 256) :=
  .var (.mk (.store 16 256) rfl
      (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))
    (.ret .here)

/-- Value proof — `rfl`: the store denotes the functional update `stackSet a i v`. -/
theorem coeffStoreMemrefCom_denote (dst : Fin 256 → BitVec 16) (i : BitVec 64)
    (v : BitVec 16) :
    coeffStoreMemrefCom.denote (.cons dst (.cons i (.cons v .nil)))
      = stackSet dst i.toNat v := rfl

/-- **The spec carried to the jasmin layer** (load): the lowered jasmin kernel
    denotes `transTy` of the memref kernel's value, via the unconditional
    `lowerMemrefToJasmin_denote` — and that value is `stackGet src i` by
    `coeffLoadMemrefCom_denote`. -/
theorem coeffLoadMemrefCom_lowered_denote (src : Fin 256 → BitVec 16) (i : BitVec 64) :
    (lowerMemrefToJasmin coeffLoadMemrefCom).denote (mapVal (.cons src (.cons i .nil)))
      = transTy (coeffLoadMemrefCom.denote (.cons src (.cons i .nil))) :=
  lowerMemrefToJasmin_denote coeffLoadMemrefCom (.cons src (.cons i .nil))

/-- **The spec carried to the jasmin layer** (store). -/
theorem coeffStoreMemrefCom_lowered_denote (dst : Fin 256 → BitVec 16) (i : BitVec 64)
    (v : BitVec 16) :
    (lowerMemrefToJasmin coeffStoreMemrefCom).denote
        (mapVal (.cons dst (.cons i (.cons v .nil))))
      = transTy (coeffStoreMemrefCom.denote (.cons dst (.cons i (.cons v .nil)))) :=
  lowerMemrefToJasmin_denote coeffStoreMemrefCom (.cons dst (.cons i (.cons v .nil)))

end CatCrypt.Crypto.SecureCompilation.Dialects.MemrefCtGoldenPath
