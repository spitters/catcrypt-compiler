/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

@[expose] public section

set_option autoImplicit false

/-!
# MAYO `N = 8` GF(16) quadratic-form `mayo_quadform_n8_rc`, FULLY FRONT-COMPILED

This module re-sources the MAYO rustcmd-ABI `N = 8` GF(16) quadratic-form kernel
`mayo_quadform_n8_rc` end-to-end through the verified `CProg`-free front, with NO
hand-built `Com` / `Lcmd` anywhere in the emit path. It combines the two now-closed
front arms:

* **Scalar `SExpr` field math** (`RScalarSetExpr` ⊂ `translateDialectControl`,
  `MAYO/KernelFromRustcmdFrontValidate.lean`): the whole GF(16) computation —
  nibble extract `(w >> 8k) & 0xf`, the branch-free bit-serial
  `GF(2)[x]/(x⁴+x+1)` multiply, the XOR accumulate — authored as `RScalarSetExpr`s.
* **Dynamic-index memref array access** (`RArrLoad` / `RArrStore` →
  `memrefGetDyn` / `memrefSetDyn` → real `stackLoad` / `stackStore` SIB
  `LOADIDX`/`STOREIDX`, `Dialects/MemrefArrayFrontValidate.lean`): the three
  `u64` buffers `out`, `s`, `mat` are `.memref` arrays bound to the three SysV
  argument pointers `RDI`/`RSI`/`RDX` via the owned multi-pointer memref ABI
  (`Com.toLprogPhysAbi` with `inLoadMap = none`, `outStoreMap = []`,
  `abiArgs = [RDI, RSI, RDX]` + `memrefBaseReload`, exactly as the SDitH/QRUOV-dot
  `ComL` route).

```
  mayoBody (LowCT: RArrLoad/RScalarSetExpr/RArrStore over .memref arrays)
    --(translateDialectControl)-->  Com catCryptDialect inΓ (.memref 1)
    --(cryptoDialectToJasminCom)-->  Com jasminDialect …      (stackLoad/stackStore)
    --(Com.toLprogPhysAbi, [RDI,RSI,RDX] memref ABI)-->  Lprog
    --(renderLprogAtt)-->  bench/mayo_compare/gen_com/mayo_kernel_from_rustcmd_front.s
```

The deployed ABI (the rustcmd KAT `bench/mayo_compare/kernel_from_rustcmd_kat.c`):

```c
extern uint64_t *mayo_quadform_n8_rc(uint64_t *out,        // RDI : 1 u64
                                     const uint64_t *p0,   // RSI : s, 8 nibbles, 1 u64
                                     const uint64_t *p1);  // RDX : mat, 8 u64 rows
//   out[0] = (Σ_{j,l} mat[j][l]·s[j]·s[l] over GF(16))  packed in the low nibble
```

The byte-packed `u64` buffers are byte-identical to a flat byte array, so the
`stackLoad`/`stackStore` cells (`u64` stride) read `s[0]`, `mat[0..7]`, `out[0]`
at their flat `u64` offsets, and the nibble extraction recovers byte `k`.

This is the pilot reroute recipe for the GF-MQ `KernelFromRustcmd` family
(SNOVA / UOV / QRUOV / SDitH).

Invoke (in-model gate):   lake env lean CatCrypt/Crypto/MAYO/KernelFromRustcmdFrontEmit.lean
Invoke (emit the `.s`):   lake env lean --run bench/mayo_compare/kernel_from_rustcmd_front_emit.lean
-/

namespace CatCrypt.Crypto.MAYO.KernelFromRustcmdFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 0. Dimension

The pipeline is parametric on the dimension `N`. The deployed kernel is
`paramN = 8`; the in-model `native_decide` gates run at `gateN = 3` because the
`VarMap`-based front's per-reference linear lookup makes the full `N = 8` unroll
(~1600 sequenced bindings) overflow the kernel/interpreter recursion stack — the
same budget wall `KernelFromRustcmdFrontValidate.lean` notes. The per-term field
arithmetic is dimension-independent (the `N = 8` body is the same `term j l`
generator over a wider range), so `gateN` faithfully validates the front-authored
computation; the `N = 8` kernel is emitted at runtime (`emit`, with a raised
`--tstack`) and gated by the external `N = 8` rustcmd KAT. -/

/-- The deployed MAYO quadform dimension `N = 8` (MAYO-1's oil dimension). -/
def paramN : Nat := 8
/-- The in-model `native_decide` gate dimension. -/
def gateN : Nat := 3

/-! ## 1. Tower types for the three memref arrays

`encodeTy (.TBytes (8·n)) = .memref n`. `s`/`out` are one `u64` cell; `mat` is
`N` `u64` cells (one packed row each). -/

/-- `s` / `out` array tower type: one `u64` cell (`encodeTy = .memref 1`). -/
def cellTy : TowerType := .TBytes 8
/-- `mat` array tower type: `N` `u64` cells (`encodeTy = .memref N`). -/
def matTy (N : Nat) : TowerType := .TBytes (8 * N)

/-! ## 2. The front-authored GF(16) field arithmetic (`RScalarSetExpr`/`SExpr`)

Identical to `KernelFromRustcmdFrontValidate.lean`'s field arithmetic — the
loaded words `sw` (the single packed `s` word) and `m0 … m_{N-1}` (the packed
matrix rows) feed nibble extraction `(w >> 8k) & 0xf` and the branch-free
bit-serial `GF(2)[x]/(x⁴+x+1)` multiply. The only change from the validate is
that `sw`/`m_j` are now `RArrLoad`-loaded from memref arrays rather than scalar
arguments. -/

/-- Matrix-row slot name. -/
def mName (j : Nat) : String := "m" ++ toString j
/-- Per-load index slot name (`ix_k := k`, materialised as `RScalarSetExpr`). -/
def ixName (k : Nat) : String := "ix" ++ toString k

/-- `0 − e` (the all-ones / zero mask of `e`'s low bit, via wrapping `SSub`). -/
def negMask (e : SExpr) : SExpr := .SSub (.SLit 0) e
/-- Bit `i` of named slot `nm`: `(nm >> i) & 1`. -/
def bitOf (nm : String) (i : Nat) : SExpr := .SAnd (.SShr (.SVar nm) (.SLit i)) (.SLit 1)
/-- Nibble `k` of the packed `s` word: `(sw >> 8k) & 0xf`. -/
def sNibE (k : Nat) : SExpr := .SAnd (.SShr (.SVar "sw") (.SLit (8 * k))) (.SLit 15)
/-- Nibble `mat[j][l]`: `(m_j >> 8l) & 0xf`. -/
def matNibE (j l : Nat) : SExpr := .SAnd (.SShr (.SVar (mName j)) (.SLit (8 * l))) (.SLit 15)

/-- One GF(16) accumulate step: `gr := gr ^ (ga & (0 − bit_i(gb)))`. -/
def gfAccStep (i : Nat) : LowCT :=
  .RScalarSetExpr "gr" (.SXor (.SVar "gr") (.SAnd (.SVar "ga") (negMask (bitOf "gb" i))))

/-- One `xtime`: `ga := ((ga << 1) ^ ((0 − bit3(ga)) & 3)) & 0xf` (reduce by `x⁴=x+1`). -/
def gfXtime : LowCT :=
  .RScalarSetExpr "ga"
    (.SAnd (.SXor (.SShl (.SVar "ga") (.SLit 1)) (.SAnd (negMask (bitOf "ga" 3)) (.SLit 3)))
      (.SLit 15))

/-- GF(16) multiply `dst := (aE & 0xf) · (bE & 0xf)` over `GF(2)[x]/(x⁴+x+1)`. -/
def gfMul (dst : String) (aE bE : SExpr) : LowCT :=
  .RSeq (.RScalarSetExpr "ga" (.SAnd aE (.SLit 15)))
  (.RSeq (.RScalarSetExpr "gb" bE)
  (.RSeq (.RScalarSetExpr "gr" (.SLit 0))
  (.RSeq (gfAccStep 0) (.RSeq gfXtime
  (.RSeq (gfAccStep 1) (.RSeq gfXtime
  (.RSeq (gfAccStep 2) (.RSeq gfXtime
  (.RSeq (gfAccStep 3)
  (.RScalarSetExpr dst (.SAnd (.SVar "gr") (.SLit 15))))))))))))

/-- One quadratic-form term `(j,l)`: `qacc ^= mat[j][l] · s[j] · s[l]`. -/
def term (j l : Nat) : LowCT :=
  .RSeq (gfMul "t1" (matNibE j l) (sNibE j))
  (.RSeq (gfMul "t2" (.SVar "t1") (sNibE l))
  (.RScalarSetExpr "qacc" (.SXor (.SVar "qacc") (.SVar "t2"))))

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ## 3. The whole memref body (loads → field arithmetic → store) -/

/-- The full front body for dimension `N`:

1. materialise `N` index constants `ix_0 … ix_{N-1}` (`RScalarSetExpr`);
2. load `sw := s[0]` and `m_j := mat[j]` (`RArrLoad` → `memrefGetDyn`);
3. run the GF(16) quadratic form (`RScalarSetExpr` field arithmetic) into `res`;
4. store `out[0] := res` (`RArrStore` → `memrefSetDyn`).

`s`/`mat`/`out` are the three `.memref` context arrays; everything else is an
internal binding. -/
def mayoBody (N : Nat) : LowCT :=
  seqAll (
    -- (1) index constants
    ((List.range N).map (fun k => (.RScalarSetExpr (ixName k) (.SLit k) : LowCT)))
    -- (2) loads
    ++ [(.RArrLoad ⟨"sw", .TU64⟩ ⟨"s", cellTy⟩ (ixName 0) : LowCT)]
    ++ ((List.range N).map (fun j =>
          (.RArrLoad ⟨mName j, .TU64⟩ ⟨"mat", matTy N⟩ (ixName j) : LowCT)))
    -- (3) field arithmetic
    ++ [(.RScalarSetExpr "qacc" (.SLit 0) : LowCT)]
    ++ ((List.range N).flatMap (fun j => (List.range N).map (fun l => term j l)))
    ++ [(.RScalarSetExpr "res" (.SAnd (.SVar "qacc") (.SLit 15)) : LowCT)]
    -- (4) store
    ++ [(.RArrStore ⟨"out", cellTy⟩ (ixName 0) ⟨"res", .TU64⟩ : LowCT)])

/-! ## 4. Input context + `VarMap`

Context order (head first): `out` (`.memref 1`), `s` (`.memref 1`), `mat`
(`.memref paramN`). The owned ABI materialises context slot `j` from `abiArgs[j]`,
so `[RDI, RSI, RDX]` binds `out ← RDI`, `s ← RSI`, `mat ← RDX`. -/

/-- The three memref input slots, **head-first = `mat`, `s`, `out`**.

    `comToLfundef` reverses context↔argument order: `argName j` is context entry
    `nArgs-1-j`, i.e. `argName 0` is the FIRST-bound (deepest) variable. To land
    `out ← argName 0 ← RDI`, `s ← argName 1 ← RSI`, `mat ← argName 2 ← RDX` (the
    KAT's `mayo_quadform_n8_rc(out, s, mat)` ABI), `out` must be bound first
    (deepest) and `mat` last (head). The context (head-first) is therefore
    `[mat, s, out]`. -/
def inΓ (N : Nat) : Ctx := [.memref N, .memref 1, .memref 1]

/-- `VarMap` binding `out` first (deepest → `argName 0` → RDI), then `s`, then
    `mat` (head → `argName 2` → RDX). -/
def inVM (N : Nat) : VarMap (inΓ N) :=
  ((VarMap.empty.bind "out").bind "s").bind "mat"

/-! ## 5. The front-emitted dialect program (returns the stored `out` array) -/

/-- Push `mayoBody N` through the `CProg`-free control front and cap with
    `ret out` (the post-store memref). `none` if the front declines. -/
def frontComResult (N : Nat) : Option (Com catCryptDialect (inΓ N) (.memref 1)) :=
  match translateDialectControl (inVM N) (mayoBody N) with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 1, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-! ## 6. Lowering to jasmin + the owned multi-pointer memref ABI export -/

/-- The front-emitted dialect program lowered to a `Com jasminDialect`
    (`memrefGetDyn`/`memrefSetDyn` → `stackLoad`/`stackStore`). -/
def frontJasmin (N : Nat) :
    Option (Σ Γ : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γ t) :=
  match frontComResult N with
  | some com =>
      match DialectToJasminCom.cryptoDialectToJasminCom com with
      | some jcom => some ⟨_, _, jcom⟩
      | none => none
  | none => none

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)

/-- The owned `Lprog` for `mayo_quadform_n8_rc` via the 3-pointer memref ABI
    (`inLoadMap = none`, `outStoreMap = []`, `abiArgs = [RDI, RSI, RDX]`), `none`
    if the front/lowering declines. -/
def kernelLprog (N : Nat) : Option Lprog :=
  (frontJasmin N).map (fun s =>
    Com.toLprogPhysAbi s.2.2 "mayo_quadform_n8_rc"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64]) (residence := none)
      (abiW := 0))

/-- The owned AT&T `.s` text (the front-generated `mayo_quadform_n8_rc`). -/
def kernelAsm (N : Nat) : Option String := (kernelLprog N).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-! ## 7. Independent schoolbook `GF(16)` reference (`mayo_kernel_ref.h`) -/

/-- Schoolbook `GF(16)` multiply over `GF(2)[x]/(x⁴+x+1)` (the C oracle, on `Nat`). -/
def gf16mulN (a b : Nat) : Nat := Id.run do
  let mut r := 0
  let mut sh := a &&& 0xf
  for i in [0:4] do
    if (b >>> i) &&& 1 == 1 then r := r ^^^ sh
    let carry := (sh >>> 3) &&& 1
    sh := (sh <<< 1) &&& 0xf
    if carry == 1 then sh := sh ^^^ 0x3
  return r &&& 0xf

/-- Schoolbook quadratic form `Σ_{j,l} mat[j][l]·s[j]·s[l]` on the packed words. -/
def quadRefN (N : Nat) (sw : BitVec 64) (m : Nat → BitVec 64) : Nat := Id.run do
  let s := fun k => ((sw.toNat) >>> (8 * k)) &&& 0xf
  let matN := fun j l => ((m j).toNat >>> (8 * l)) &&& 0xf
  let mut acc := 0
  for j in [0:N] do
    for l in [0:N] do
      let t1 := gf16mulN (matN j l) (s j)
      let t2 := gf16mulN t1 (s l)
      acc := acc ^^^ t2
  return acc &&& 0xf

/-- The reference as a `BitVec 64` (the low-nibble GF(16) scalar). -/
def quadRefBV (N : Nat) (sw : BitVec 64) (m : Nat → BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (quadRefN N sw m)

/-! ## 8. In-model `denote = spec`

The valuation: `out` (one cell, initial), `s` (one cell `= sw`), `mat`
(`paramN` cells `= m`). The denotation returns the post-store `out` memref; its
cell `0` is the GF(16) result word. -/

/-- Input valuation, head-first `[mat, s, out]` (matches `inΓ`). -/
def encodeVal (N : Nat) (sw : BitVec 64) (m : Fin N → BitVec 64) :
    @Ctxt.Valuation catCryptDialect _ (inΓ N) :=
  .cons m (.cons (fun _ => sw) (.cons (fun _ => (0 : BitVec 64)) .nil))

/-- Denote the front program and read out cell `0` of the returned `out` memref.
    `m` is the positional matrix-row word function (`m j = mat_pack[j]`). -/
def frontDenote (N : Nat) (sw : BitVec 64) (m : Nat → BitVec 64) : Option (BitVec 64) :=
  (frontComResult N).map (fun com =>
    com.denote (encodeVal N sw (fun j => m j.val)) ⟨0, by decide⟩)

/-! ## 9. Gates (at `gateN`; the field arithmetic is dimension-independent) -/

/-- The memref body translates through the `CProg`-free control front. -/
theorem mayoBody_translates :
    (translateDialectControlTop (inVM gateN) (mayoBody gateN)).isSome := by native_decide

/-- The front emits a result program (`ret out`). -/
theorem frontComResult_isSome : (frontComResult gateN).isSome := by native_decide

/-- The front-emitted dialect program lowers end-to-end to a `Com jasminDialect`
    (the GF(16) field arithmetic + the memref loads/stores reach the owned
    backend through `cryptoDialectToJasminCom`, no hand-built `Com`/`Lcmd`). -/
theorem frontJasmin_isSome : (frontJasmin gateN).isSome := by native_decide

/-- The owned 3-pointer memref ABI export renders a `.s` for the front program. -/
theorem kernelAsm_isSome : (kernelAsm gateN).isSome := by native_decide

/-! ### `denote = spec` on representative packed inputs (`N = gateN`) -/

/-- All-zero. -/
example : frontDenote gateN 0 (fun _ => 0) = some (quadRefBV gateN 0 (fun _ => 0)) := by
  native_decide

/-- All-nibble-`1`. -/
example :
    frontDenote gateN 0x0101010101010101 (fun _ => 0x0101010101010101)
      = some (quadRefBV gateN 0x0101010101010101 (fun _ => 0x0101010101010101)) := by
  native_decide

/-- All-nibble-`0xf`. -/
example :
    frontDenote gateN 0x0f0f0f0f0f0f0f0f (fun _ => 0x0f0f0f0f0f0f0f0f)
      = some (quadRefBV gateN 0x0f0f0f0f0f0f0f0f (fun _ => 0x0f0f0f0f0f0f0f0f)) := by
  native_decide

/-- Identity matrix, `s` ramp (`s[k] = k+1`). -/
example :
    frontDenote gateN 0x0807060504030201 (fun j => BitVec.ofNat 64 (1 <<< (8 * j)))
      = some (quadRefBV gateN 0x0807060504030201
          (fun j => BitVec.ofNat 64 (1 <<< (8 * j)))) := by native_decide

/-- Pseudo-random packed words. -/
example :
    frontDenote gateN 0x243f6a8885a308d3
        (fun j => BitVec.ofNat 64 (j * 0x9e3779b97f4a7c15 + 0x13198a2e03707344))
      = some (quadRefBV gateN 0x243f6a8885a308d3
          (fun j => BitVec.ofNat 64 (j * 0x9e3779b97f4a7c15 + 0x13198a2e03707344))) := by
  native_decide

/-! ## 10. Emit driver -/

/-- Write the front-generated `mayo_kernel_from_rustcmd_front.s` (`N = paramN`)
    into the MAYO bench directory. -/
def emit : IO Unit := do
  match kernelAsm paramN with
  | some asm =>
      IO.FS.createDirAll "bench/mayo_compare/gen_com"
      IO.FS.writeFile "bench/mayo_compare/gen_com/mayo_kernel_from_rustcmd_front.s" asm
      IO.println "wrote bench/mayo_compare/gen_com/mayo_kernel_from_rustcmd_front.s (front-compiled, no jasminc, no hand Com/Lcmd)"
  | none => throw (IO.userError "front-compile of mayo_quadform_n8_rc failed (front/lowering declined)")

end CatCrypt.Crypto.MAYO.KernelFromRustcmdFrontEmit
