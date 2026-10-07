/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.ArrayLoopCT

/-!
# Golden path: public-indexed array access (the NTT / coefficient pattern)

This file is the array and memory-op companion to `FieldEmitGoldenPath.lean`. It
packages **public-indexed array access** — `dst[i] := f(src[i])` over a public
loop counter `i`, the access shape every NTT / FRI / coefficient loop uses — at
the two levels where it is verified:

1. **Dialect level (value).** A `Com jasminDialect` built from the array ops
   `.stackLoad` / `.stackStore` on a public index register, whose `Com.denote`
   equals the functional array read (`stackGet`) and write (`stackSet`), proven
   by `rfl`. This is the array analogue of `fieldAddCom_denote`: the source is
   written once over the dialect's `stackLoad`/`stackStore` alphabet and its
   value is the functional spec, structurally.

2. **CT-analysis level (leakage).** The access is constant-time *because* the
   index is public. We do **not** re-derive this: we instantiate the existing
   `ArrayLoopCT` result (`arrMapLoop_isCT` / `arrMapLoop_noninterference`,
   themselves built on `cmdCT` / `cmdCT_sound`) on a concrete coefficient-loop
   instance, and dually show that swapping the public index for a *secret* one
   makes the very same `cmdCT` analyser reject it. A secret-indexed table
   lookup (the AES S-box class) leaks via the address trace; the public-index
   discipline is exactly what rules it out.

## Scope and the emit gap

The dialect denote (`stackGet`/`stackSet`) and the CT property (the real
`PublicEquiv`-noninterference statement of `ArrayLoopCT`, via `cmdCT_sound`) are
both proven; neither is vacuous. What is **not** here is a backend *emit* of
`.stackLoad` / `.stackStore`: the neutral AArch64 / RISC-V `comToReg` backends
that `FieldEmitGoldenPath` rides do not lower the array ops (they cover the
`reg`-only `SupportedOp` alphabet). So unlike the field-arithmetic kernels,
this pattern stops at the dialect + CT-analysis level — a constant-time
*gather/scatter* lowering (load/store with a register index, address computed
obliviously) would close it. The gap is the lowering, not the specification.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CtMemory


open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Dialect level: public-indexed array load / store, `denote = spec`

The NTT coefficient width is 16 bits and a degree-255 polynomial has 256
coefficients (ML-KEM / Kyber `n = 256`), so the array type is `stackArr 16 256`
and the index a `reg 64` — exactly the `stackLoad` / `stackStore` signature. -/

/-- **The array-read source.** Element load `src[i]` as a one-op
    `Com jasminDialect` over args `[src, i]` (`src : stackArr 16 256`,
    `i : reg 64`). This is the *source*; its value is the functional read. -/
def coeffLoadCom : Com jasminDialect [.stackArr 16 256, .reg 64] (.reg 16) :=
  .var { op := .stackLoad 16 256, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here)

/-- **Step value — `rfl`.** The load source denotes the functional array read
    `stackGet src i.toNat`: total (the index is reduced mod `n`), and equal to
    the underlying entry on an in-range index (`stackGet_id`). -/
theorem coeffLoadCom_denote (src : Fin 256 → BitVec 16) (i : BitVec 64) :
    Com.denote coeffLoadCom (.cons src (.cons i .nil)) = stackGet src i.toNat := rfl

/-- **The array-write source.** Element store `dst[i] := v` as a one-op
    `Com jasminDialect` over args `[dst, i, v]` (`dst : stackArr 16 256`,
    `i : reg 64`, `v : reg 16`), returning the updated array. -/
def coeffStoreCom : Com jasminDialect [.stackArr 16 256, .reg 64, .reg 16]
    (.stackArr 16 256) :=
  .var { op := .stackStore 16 256, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)) }
    (.ret .here)

/-- **Step value — `rfl`.** The store source denotes the functional array
    update `stackSet dst i.toNat v`. -/
theorem coeffStoreCom_denote (dst : Fin 256 → BitVec 16) (i : BitVec 64)
    (v : BitVec 16) :
    Com.denote coeffStoreCom (.cons dst (.cons i (.cons v .nil)))
      = stackSet dst i.toNat v := rfl

/-- **The read-write round trip on an in-range index.** Loading the value that
    is stored at the same in-range index `j : Fin 256` returns it. This is
    the functional coefficient-update law (`stackSet` then `stackGet` at the
    same in-range cell), composing the two `denote` specs — the value identity a
    coefficient loop relies on. -/
theorem coeffStoreThenLoad (dst : Fin 256 → BitVec 16) (j : Fin 256)
    (v : BitVec 16) :
    Com.denote coeffLoadCom
        (.cons (Com.denote coeffStoreCom
                  (.cons dst (.cons (BitVec.ofNat 64 j.val) (.cons v .nil))))
          (.cons (BitVec.ofNat 64 j.val) .nil))
      = v := by
  rw [coeffLoadCom_denote, coeffStoreCom_denote]
  have hj : (BitVec.ofNat 64 j.val).toNat = j.val := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hj, stackGet_id (stackSet dst j.val v) j]
  simp only [stackSet]
  rw [if_pos (Fin.ext (Nat.mod_eq_of_lt j.isLt).symm)]

/-! ## 2. CT-analysis level: the public-indexed coefficient loop is constant-time

We instantiate the generic `ArrayLoopCT` results on a concrete coefficient-loop
instance. The loop body is `arrMapBody src dst t`, i.e. `t := src["i"];
dst["i"] := t` with index the public loop counter `"i"`. We pick concrete slot
names and a `LevelTable` classifying them all `Public`; `arrMapLoop_isCT` then
gives `cmdCT = true`, and `arrMapLoop_noninterference` the
`PublicEquiv`-noninterference (via `cmdCT_sound`) — neither is re-derived here. -/

/-- Concrete slot for the source coefficient array. -/
def srcLoc : Located := { locVar := "src", locSrc := .TFp }
/-- Concrete slot for the destination coefficient array. -/
def dstLoc : Located := { locVar := "dst", locSrc := .TFp }
/-- Concrete slot for the per-iteration temporary. -/
def tmpLoc : Located := { locVar := "t", locSrc := .TFp }

/-- The all-public classification for the coefficient loop: the arrays, the
    temp, and the loop counter `"i"` are all `Public`. -/
def coeffLT : LevelTable := fun _ => .Public

/-- The concrete NTT/coefficient map loop `for i in 0..256 { t := src[i];
    dst[i] := t }` over the public counter `"i"`. -/
def coeffMapLoop : LowCT := .RFor "i" 256 (arrMapBody srcLoc dstLoc tmpLoc)

/-- **The public-indexed coefficient loop passes the CT analyser.** A direct
    instance of `ArrayLoopCT.arrMapLoop_isCT`: every slot (`src`, `dst`, `t`)
    and the loop index `"i"` are `Public`, so `cmdCT` returns `true`. -/
theorem coeffMapLoop_isCT (leafCT : LeafCTTable) :
    cmdCT coeffMapLoop coeffLT leafCT = true :=
  arrMapLoop_isCT srcLoc dstLoc tmpLoc 256 coeffLT leafCT rfl rfl rfl rfl

/-- **Robust-CT capstone for the concrete loop: it is noninterferent.** Two
    executions from `Public`-equivalent states reach `Public`-equivalent states
    — the public-indexed coefficient loop leaks nothing about secret inputs.
    A direct instance of `ArrayLoopCT.arrMapLoop_noninterference` (which is
    `cmdCT_sound` applied to `coeffMapLoop_isCT`); the CT property is the real
    `PublicEquiv` noninterference statement, not a metric swap. -/
theorem coeffMapLoop_noninterference
    (leafCT : LeafCTTable) (leafSpec : LeafSpec) (N : Nat)
    (hCMOV : CMOVInvariant coeffMapLoop)
    (rs1 rs2 rs1' rs2' : RustState)
    (hEq : PublicEquiv coeffLT rs1 rs2)
    (hExec1 : RustExec N leafSpec coeffMapLoop rs1 rs1')
    (hExec2 : RustExec N leafSpec coeffMapLoop rs2 rs2') :
    PublicEquiv coeffLT rs1' rs2' :=
  arrMapLoop_noninterference srcLoc dstLoc tmpLoc 256 coeffLT leafCT leafSpec N
    rfl rfl rfl rfl hCMOV rs1 rs2 rs1' rs2' hEq hExec1 hExec2

/-! ### 2½. The dual: a secret index is rejected by the same analyser

A *secret*-indexed access — the AES-S-box / data-dependent-table class — leaks
the index via the address trace. The same `cmdCT` analyser correctly rejects
it: with the index slot `"j"` classified `Secret`, the `RArrLoad` guard
`lt idxVar == .Public` fails, so `cmdCT = false`. This is the fail-closed
behaviour that distinguishes the constant-time coefficient loop above from a
secret table lookup. -/

/-- A level table identical to `coeffLT` except the index slot `"j"` is `Secret`. -/
def secretIdxLT : LevelTable := fun v => if v = "j" then .Secret else .Public

/-- A single secret-indexed load `t := src[j]` with `"j"` secret. -/
def secretIdxLoad : LowCT := .RArrLoad tmpLoc srcLoc "j"

/-- **The secret-indexed access is rejected.** With the index `"j"` classified
    `Secret`, the same `cmdCT` analyser returns `false`: a data-dependent array
    index is the canonical constant-time leak, and the public-index side
    condition catches it. (`cmdCT` is fail-closed — exactly the AES-S-box class
    the public-index discipline is there to exclude.) -/
theorem secretIdxLoad_rejected (leafCT : LeafCTTable) :
    cmdCT secretIdxLoad secretIdxLT leafCT = false := by
  simp only [secretIdxLoad, cmdCT_RArrLoad, secretIdxLT]
  decide

/-- The dual stated together: the public-indexed coefficient loop is accepted,
    and the secret-indexed load is rejected, by the **same** `cmdCT` analyser. -/
theorem coeffLoop_accept_secretIdx_reject (leafCT : LeafCTTable) :
    cmdCT coeffMapLoop coeffLT leafCT = true ∧
      cmdCT secretIdxLoad secretIdxLT leafCT = false :=
  ⟨coeffMapLoop_isCT leafCT, secretIdxLoad_rejected leafCT⟩

end CatCrypt.Crypto.SecureCompilation.CtMemory
