/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

@[expose] public section

set_option autoImplicit false

/-!
# Front-gap 3 (ConvertToVole): runtime-STRIDE row addressing via the front

`ConvertToVoleV204FrontEmit` (GAP 3) records that the dynamic-index memref arms
(`memrefGetDyn`/`memrefSetDyn`, the SIB `LOADIDX`/`STOREIDX`) index a memref by a
`.sword 64` **element** index, whereas `convert_to_vole`'s rows are runtime-length
`outlen`-word slabs whose per-row base is `base + idx * runtimeStride` (`r+j*outlen`,
`v+jd*outlen`, `sd+j*16`) with a **runtime** stride (a register). The SIB scale
field is a static immediate (1/2/4/8), so a runtime stride cannot ride the scale;
it needs a computed offset `off := idx * stride` (a reg×reg `MUL`) then the access
at `[base + off]` (an `ADD` folded into the memref element index).

## What closes the gap: compose the committed front arms (no new node)

The row-address arithmetic `idx * stride (+ k)` is exactly a scalar `SExpr`
(`SAdd (SMul (SVar idx) (SVar stride)) (SLit k)`), which the committed
`RScalarSetExpr` arm lowers to a real `bvMul` (→ jasmin `regArith .mul` → x86
`MUL:64`, a reg×reg multiply) followed by a real `bvAdd` (→ `regArith .add` →
`ADD:64`). Binding the result to a fresh `.sword 64` word `off`, the committed
`RArrLoad`/`RArrStore` arms then feed `off` as the runtime element index to the
existing `memrefGetDyn`/`memrefSetDyn` (SIB `LOADIDX`/`STOREIDX`). So the
runtime-stride row access is the compute-then-access sequence

```
  RScalarSetExpr "off" (SAdd (SMul (SVar "idx") (SVar "stride")) (SLit k))
       -->  bvMul (idx, stride)   -->  MUL:64   (reg × reg, stride READ from a reg)
       -->  bvAdd (·, k)          -->  ADD:64
  RArrLoad  ⟨w, TU64⟩ src "off"   -->  memrefGetDyn  -->  LOADIDX  [src + off]
  RArrStore out "off" ⟨w, TU64⟩   -->  memrefSetDyn  -->  STOREIDX [out + off]
```

The word memref carries the `base` (the array pointer / invariant seed); the
element index `off = idx*stride + k` is the runtime word offset from that base.
Wrapping this body in `TranslateDialectRuntimeLoop.rolledForLoopNRt` gives the
runtime-trip loop `for j < n: out[j*stride+k] := src[j*stride+k]` — one body copy,
a real back-edge, the stride and the trip both read from registers.

This module VALIDATEs that (native_decide): the body front-compiles, its emitted
physical body contains a real `MUL:64` and `ADD:64` (the offset compute) plus one
`LOADIDX`/`STOREIDX` (the access), and `denote = the independent row-address spec`
`out[j] = src[j] iff j ∈ { (i*stride+k) mod N : i < cnt }` — at TWO different
runtime strides on the SAME emitted program, so the stride is genuinely read from
its register (not baked into the emit).

Invoke:  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/RuntimeStrideRowFrontValidate.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RuntimeStrideRowFrontValidate

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 0. Dimensions

`paramN` is the FLAT memref word-capacity (rows live contiguously inside it). The
row width is a runtime stride (a `.reg 64` argument); the compile-time constant
offset within a row is `rowK`. Small enough for `native_decide`. -/

/-- The flat memref capacity in 64-bit words. -/
def paramN : Nat := 8

/-- The compile-time offset within a row (`+ k`); a runtime stride still dominates
    the address. Zero here (row base), but the `SLit` add is emitted regardless. -/
def rowK : Nat := 0

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ## 1. The runtime-stride row-copy body, authored as covered LowCT

Body context `Γbody = [out:.memref N, idx:.sword 64, src:.memref N, stride:.sword 64]`
(accumulator `out`; loop index `idx`; invariants `src`, `stride`). The body:

* `off := idx * stride + k`  (`RScalarSetExpr` → `bvMul`;`bvAdd`);
* `w := src[off]`            (`RArrLoad` → `memrefGetDyn`);
* `out[off] := w`            (`RArrStore` → `memrefSetDyn`). -/

/-- One trip of the runtime-stride row copy at the loop index `idx`. -/
def strideBodyLowCT : LowCT := seqAll [
  -- off := idx * stride + rowK   (real reg×reg MUL, then ADD)
  .RScalarSetExpr "off"
    (.SAdd (.SMul (.SVar "idx") (.SVar "stride")) (.SLit rowK)),
  -- w := src[off]   (dynamic memref load at the computed offset)
  .RArrLoad ⟨"w", .TU64⟩ ⟨"src", .TBytes (8 * paramN)⟩ "off",
  -- out[off] := w   (dynamic memref store at the computed offset)
  .RArrStore ⟨"out", .TBytes (8 * paramN)⟩ "off" ⟨"w", .TU64⟩ ]

/-! ## 2. Body context + VarMap

`Γbody = [out, idx, src, stride]` head-first: `out ↦ .here`, `idx ↦ .there .here`,
`src ↦ .there² .here`, `stride ↦ .there³ .here`. -/

/-- The body context: accumulator `out`, loop index `idx`, invariants `src`,
    `stride`. -/
def Γbody : Ctx := [.memref paramN, .sword 64, .memref paramN, .sword 64]

/-- The body VarMap (bind deepest-first so the last bind lands at `.here`). -/
def vmBody : VarMap Γbody :=
  ((((VarMap.empty.bind (t := .sword 64) "stride").bind
      (t := .memref paramN) "src").bind
      (t := .sword 64) "idx").bind (t := .memref paramN) "out")

/-! ## 3. The outer program: front body → genuine `ComL.forLoopNRt`

Outer context `[count, stride, src, out]` (newest-first) — jasmin types
`[.reg 64, .reg 64, .stackArr 64 N, .stackArr 64 N]`. ABI (deepest = `a0`):
`out = a0 (RDI)`, `src = a1 (RSI)`, `stride = a2 (RDX)`, `count = a3 (RCX)`.
The stride is a `.reg 64` ARGUMENT — read at run time, never an immediate. -/

/-- The outer (kernel-argument) jasmin context: `[count, stride, src, out]`. -/
def Γouter : Ctxt jasminDialect :=
  [.reg 64, .reg 64, .stackArr 64 paramN, .stackArr 64 paramN]

/-- The front-compiled runtime-trip, runtime-stride row-copy loop, or `none` if
    the front declines. `invCTys = [.memref N (src), .sword 64 (stride)]`. -/
def strideComL : Option (ComL Γouter (.stackArr 64 paramN)) :=
  rolledForLoopNRt (Γouter := Γouter) (accCTy := .memref paramN)
    (invCTys := [.memref paramN, .sword 64])
    vmBody "out" strideBodyLowCT
    (count := .here)
    (init := .there (.there (.there .here)))
    (invs := .cons (.there (.there .here)) (.cons (.there .here) .nil))

/-! ## 4. Gate: the front succeeds -/

/-- The runtime-stride row-copy body front-compiles to a genuine
    `ComL.forLoopNRt`. -/
theorem strideComL_isSome : strideComL.isSome := by native_decide

/-! ## 5. denote = independent row-address spec (at TWO runtime strides)

The spec is computed DIRECTLY from `stride`/`k`/`cnt` (an existential over the
loop index), NOT via the loop's own `memSetDyn` fold: cell `j` receives `src j`
exactly when some trip `i < cnt` addresses it (`(i*stride + k) mod N = j`),
otherwise the seed `init j` survives. Collisions are harmless (all writers store
`src j`). -/

/-- The independent runtime-stride row-address reference. -/
def strideSpec (src init : Fin paramN → BitVec 64) (stride cnt : Nat) :
    Fin paramN → BitVec 64 :=
  fun j =>
    if (List.range cnt).any (fun i => (i * stride + rowK) % paramN == j.val)
    then src j else init j

/-- Deterministic sample source stream. -/
def sampleSrc : Fin paramN → BitVec 64 := fun i => BitVec.ofNat 64 (0x1000 + i.val * 7)

/-- Deterministic sample accumulator seed (survives where no trip writes). -/
def sampleInit : Fin paramN → BitVec 64 := fun i => BitVec.ofNat 64 (0xff00 + i.val)

/-- The outer valuation `[count, stride, src, out-seed]` at `Γouter`. -/
def mkVal (cnt stride : BitVec 64) (src init : Fin paramN → BitVec 64) :
    Ctxt.Valuation Γouter :=
  .cons cnt (.cons stride (.cons src (.cons init .nil)))

/-- A memref row as a `List Nat` for `DecidableEq` comparison. -/
def rowList (f : Fin paramN → BitVec 64) : List Nat :=
  (List.finRange paramN).map (fun i => (f i).toNat)

/-- The denoted output row at runtime count `cnt` and runtime stride `stride`. -/
def strideDenoteRow (cnt stride : BitVec 64) (src init : Fin paramN → BitVec 64) :
    Option (List Nat) :=
  strideComL.map (fun c =>
    (List.finRange paramN).map (fun i =>
      (ComL.denote c (mkVal cnt stride src init) i).toNat))

/-- **denote = row-address spec at stride 2, count 3.** Cells `{0,2,4}` get `src`,
    the rest keep the seed. -/
theorem strideComL_denote_s2 :
    strideDenoteRow 3 2 sampleSrc sampleInit
      = some (rowList (strideSpec sampleSrc sampleInit 2 3)) := by native_decide

/-- **denote = row-address spec at stride 3, count 3 (SAME program).** Cells
    `{0,3,6}` get `src` — different addresses from stride 2, so the stride is
    genuinely read from its register, not baked into the emit. -/
theorem strideComL_denote_s3 :
    strideDenoteRow 3 3 sampleSrc sampleInit
      = some (rowList (strideSpec sampleSrc sampleInit 3 3)) := by native_decide

/-- **denote = row-address spec at stride 1, count 4.** Contiguous prefix copy
    `{0,1,2,3}` — the runtime stride specialises to a plain element index. -/
theorem strideComL_denote_s1 :
    strideDenoteRow 4 1 sampleSrc sampleInit
      = some (rowList (strideSpec sampleSrc sampleInit 1 4)) := by native_decide

/-- **The two strides genuinely disagree** (a sanity witness that the stride reg
    controls the addresses): stride 2 and stride 3 at count 3 produce DIFFERENT
    output rows on the same program. -/
theorem strideComL_stride_observable :
    strideDenoteRow 3 2 sampleSrc sampleInit
      ≠ strideDenoteRow 3 3 sampleSrc sampleInit := by native_decide

/-! ## 6. The emitted body carries the real offset compute + access

3-arg-plus-count ABI `stride_row_copy(out, src, stride, n)`
(`RDI=out, RSI=src, RDX=stride, RCX=n`). -/

/-- The physical body of the front-compiled runtime-stride copy loop. -/
def physBody : Option Lcmd :=
  strideComL.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1, argName 2]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]).lfd_body)

/-- **Real reg×reg `MUL:64` and `ADD:64` in the body** — the offset compute
    `idx*stride + k`, emitted as genuine multiply + add (the runtime-stride
    address arithmetic the static SIB scale cannot express). -/
theorem physBody_has_mul_add :
    physBody.map (fun b =>
      (b.any (fun i => match i.li_i with
          | .Lopn _ nm _ => strContains nm "MUL" | _ => false))
        && (b.any (fun i => match i.li_i with
          | .Lopn _ nm _ => strContains nm "ADD" | _ => false)))
      = some true := by native_decide

/-- **ONE indexed load and ONE indexed store** (`src[off]` / `out[off]`), at the
    computed offset — not `n` unrolled accesses. -/
theorem physBody_bounded_indexed :
    physBody.map (fun b =>
      ((b.filter (fun i => match i.li_i with
          | .Lopn _ "LOADIDX" _ => true | _ => false)).length,
       (b.filter (fun i => match i.li_i with
          | .Lopn _ "STOREIDX" _ => true | _ => false)).length))
      = some (1, 1) := by native_decide

/-- **Real back-edge preserved:** an internal `Llabel` + `Lcond` (`jne .L<d>`) —
    a genuine counted loop, not an unrolled chain. -/
theorem physBody_has_backedge :
    physBody.map (fun b =>
      (b.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
        && (b.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)))
      = some true := by native_decide

/-- The runtime-stride row-copy fragment renders to AT&T `.s`. -/
def strideKernelAsm : Option String :=
  strideComL.map (fun c =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
      (ComL.toLprogPhysAbi c "stride_row_copy" (argName 0) [argName 1, argName 2]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
        [64, 64, 64, 64]))

/-- The fragment renders. -/
theorem strideKernelAsm_isSome : strideKernelAsm.isSome := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.RuntimeStrideRowFrontValidate
