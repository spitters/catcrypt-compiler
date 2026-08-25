/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul2FixedFrontEmit
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.ArrAbiOrch
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# 4×4 → 8-limb schoolbook multiply as a reg-ptr-out leaf-call schedule

`mpn_mul4_sched(out, inp)` computes `out[0..8) = ap[0..4) · bp[0..4)` (a full
256×256 → 512-bit product) as a straight-line orchestration of by-pointer leaf
calls through the array-ABI backend. The two C pointers are the canonical
2-pointer reg-ptr-out ABI `f(out = RDI, inp = RSI)`; `inp` points at the
concatenated input `[ap(4) | bp(4)]` (64 bytes), `out` at the 8-limb result
(64 bytes).

## Sub-buffer offset reads

The four 2×2 partial products are computed by the fixed leaf `probe_mul2`
(2-limb × 2-limb → 4-limb, `MpnMul2FixedFrontEmit`). Each product reads a
2-limb half of a 4-limb input, addressed by the array-ABI **sub-buffer byte
offset** (`ArrAbiOrch.ArrCallRec.argOffs` / `CallPhase.argOffs`): operand `i`
of a call is passed as `leaq base + argOffs[i]`, so `ap[2:4]` is `ap` at byte
offset `16`.

```
  p00 = probe_mul2(ap[0:2], bp[0:2])    argOffs [0, 0]
  p01 = probe_mul2(ap[0:2], bp[2:4])    argOffs [0, 16]
  p10 = probe_mul2(ap[2:4], bp[0:2])    argOffs [16, 0]
  p11 = probe_mul2(ap[2:4], bp[2:4])    argOffs [16, 16]
```

## Assembly (limb-column plan)

The product is `p00 + (p01+p10)·2^128 + p11·2^256`. Because `p00` (limbs 0..3)
and `p11` (limbs 4..7) do not overlap, they concatenate into the 8-limb base
`base = [p00 | p11]` with no carry. The two middle products are then added in
at limb offset 2, each carrying up through the top limbs:

```
  base = join8(p00, p11)                 base[0..4) = p00,  base[4..8) = p11
  t1   = addinto8_at2(base, p01)         base + p01·2^128   (carry into limbs 2..7)
  R    = addinto8_at2(t1,   p10)         + p10·2^128        (carry into limbs 2..7)
```

`R = p00 + p11·2^256 + (p01+p10)·2^128`, the full 512-bit product; no final
carry escapes limb 7 because the exact product is `< 2^512`.

The two assembly leaves are 8-limb-output kernels so the orchestration's single
returned buffer holds all 8 result limbs. Carry propagation stays *inside* each
8-limb leaf; the array-ABI writes every leaf result to its own scratch at
offset 0 (only operand *reads* carry a byte offset), so a cross-leaf carry limb
cannot be scattered into a sub-window of a larger result buffer — an 8-limb
accumulate leaf is the shape that keeps the result in one buffer. See the
report's gap note on `Com.toLprogArrAbi` and the offset field.

## Offset wiring

`Com.toLprogArrAbi` takes the schedule's per-call operand byte offsets
(`schedArgOffs mul4Schedule`) and threads them onto the array-ABI call records
before `emitOneCall` folds them into the operand `leaq` displacements. The
instruction emission stays in the verified backend; only the per-operand
displacement data is carried.

## ABI of the assembly leaves

```c
extern void probe_join8(uint64_t *rp, const uint64_t *lop, const uint64_t *hip);
extern void probe_addinto8_at2(uint64_t *rp, const uint64_t *basep, const uint64_t *addp);
```

`rp` (RDI), `lop`/`basep` (RSI), `hip`/`addp` (RDX); buffers-only, reg-ptr-out.

## Main results

* `probeJoin8Asm` / `probeAddInto8At2Asm` — the two new owned assembly leaves,
  front-compiled (`translateDialectControl` + `cryptoDialectToJasminCom`) and
  rendered through `Com.toLprogPhysAbi` / `renderOwned`.
* `mul4Schedule` / `mul4SchedCom` / the `#guard` on its `.isSome` — the 7-call
  reg-ptr-out schedule and its front-generated orchestration `Com`.
* `mul4SchedAsm` — the owned AT&T `.s`, via the offset-threading array-ABI
  lowering and `renderOwned`.
* `emitMain` — writes `mpn_mul4_sched_owned.s` and the leaf `.s` for the byte-KAT.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4SchedFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (seqAll ltuCmds sv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (renderOwned)

/-! ## 1. The `probe_join8` assembly leaf

`probe_join8(rp, lop, hip)` sets `rp[0..4) = lop[0..4)` and `rp[4..8) = hip[0..4)`
— a byte concatenation of two 4-limb buffers into an 8-limb buffer, with no
arithmetic. Used to seat the two non-overlapping corner products `p00` (low) and
`p11` (high) into the 8-limb accumulator base. -/

namespace Join8

/-- The output-array slot `rp` (8 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 8)⟩

/-- The low-half source `lop` (4 words → result limbs 0..3). -/
def lopLoc : Located := ⟨"lop", .TBytes (8 * 4)⟩

/-- The high-half source `hip` (4 words → result limbs 4..7). -/
def hipLoc : Located := ⟨"hip", .TBytes (8 * 4)⟩

/-- Index-constant slots `ix0..ix7`. -/
def idxInit : List LowCT :=
  (List.range 8).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `l0..l3` from `lop` and `h0..h3` from `hip`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"l0", .TU64⟩ lopLoc "ix0"
  , .RArrLoad ⟨"l1", .TU64⟩ lopLoc "ix1"
  , .RArrLoad ⟨"l2", .TU64⟩ lopLoc "ix2"
  , .RArrLoad ⟨"l3", .TU64⟩ lopLoc "ix3"
  , .RArrLoad ⟨"h0", .TU64⟩ hipLoc "ix0"
  , .RArrLoad ⟨"h1", .TU64⟩ hipLoc "ix1"
  , .RArrLoad ⟨"h2", .TU64⟩ hipLoc "ix2"
  , .RArrLoad ⟨"h3", .TU64⟩ hipLoc "ix3" ]

/-- Store the low half at limbs 0..3 and the high half at limbs 4..7. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"l0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"l1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"l2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"l3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"h0", .TU64⟩
  , .RArrStore rpLoc "ix5" ⟨"h1", .TU64⟩
  , .RArrStore rpLoc "ix6" ⟨"h2", .TU64⟩
  , .RArrStore rpLoc "ix7" ⟨"h3", .TU64⟩ ]

/-- The full straight-line `probe_join8` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ storeOutputs)

/-- Head-first kernel context `[hip, lop, rp]`. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 8]

/-- `rp` deepest (→ RDI), then `lop` (→ RSI), then `hip` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 8) "rp").bind
    (t := .memref 4) "lop").bind (t := .memref 4) "hip"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 8)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 8, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `probe_join8` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_join8` under the buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_join8"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_join8`. -/
def asm : Option String := lprog.map renderOwned

end Join8

/-- The `probe_join8` owned leaf `.s`. -/
def probeJoin8Asm : Option String := Join8.asm

/-! ## 2. The `probe_addinto8_at2` assembly leaf

`probe_addinto8_at2(rp, basep, addp)` sets `rp[0..8) = basep[0..8) + addp[0..4)·2^128`
— an 8-limb accumulator plus a 4-limb addend shifted left by two limbs, with the
carry rippling from limb 2 through limb 7. Limbs 0 and 1 pass through unchanged;
the final carry out of limb 7 is dropped (the partial product always fits in 8
limbs). Each column carry-out is the branch-free `ltuCmds` compare of a running
sum against its first summand, and a column with a carry-in adds in two `SAdd`
steps summing the two carry bits (the `add4Body` column shape). -/

namespace AddInto8At2

/-- The output-array slot `rp` (8 words). -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * 8)⟩

/-- The 8-limb accumulator `basep`. -/
def basepLoc : Located := ⟨"basep", .TBytes (8 * 8)⟩

/-- The 4-limb addend `addp` (added at limb offset 2). -/
def addpLoc : Located := ⟨"addp", .TBytes (8 * 4)⟩

/-- Index-constant slots `ix0..ix7`. -/
def idxInit : List LowCT :=
  (List.range 8).map (fun i => .RScalarSetExpr s!"ix{i}" (.SLit i))

/-- Load `b0..b7` from `basep` and `a0..a3` from `addp`. -/
def loadInputs : List LowCT :=
  [ .RArrLoad ⟨"b0", .TU64⟩ basepLoc "ix0"
  , .RArrLoad ⟨"b1", .TU64⟩ basepLoc "ix1"
  , .RArrLoad ⟨"b2", .TU64⟩ basepLoc "ix2"
  , .RArrLoad ⟨"b3", .TU64⟩ basepLoc "ix3"
  , .RArrLoad ⟨"b4", .TU64⟩ basepLoc "ix4"
  , .RArrLoad ⟨"b5", .TU64⟩ basepLoc "ix5"
  , .RArrLoad ⟨"b6", .TU64⟩ basepLoc "ix6"
  , .RArrLoad ⟨"b7", .TU64⟩ basepLoc "ix7"
  , .RArrLoad ⟨"a0", .TU64⟩ addpLoc "ix0"
  , .RArrLoad ⟨"a1", .TU64⟩ addpLoc "ix1"
  , .RArrLoad ⟨"a2", .TU64⟩ addpLoc "ix2"
  , .RArrLoad ⟨"a3", .TU64⟩ addpLoc "ix3" ]

/-- The carry-propagating column sums for `base + add·2^128`:

    * `r2 = b2 + a0`, carry `c2`;
    * `r3 = b3 + a1 + c2`, carry `c3 = c3a + c3b`;
    * `r4 = b4 + a2 + c3`, carry `c4 = c4a + c4b`;
    * `r5 = b5 + a3 + c4`, carry `c5 = c5a + c5b`;
    * `r6 = b6 + c5`, carry `c6`;
    * `r7 = b7 + c6` (final carry dropped).

    `r0 = b0`, `r1 = b1` pass through. -/
def columns : List LowCT :=
  [ .RScalarSetExpr "s2" (.SAdd (sv "b2") (sv "a0")) ]
  ++ ltuCmds "c2" (sv "s2") (sv "b2")
  ++ [ .RScalarSetExpr "t3" (.SAdd (sv "b3") (sv "a1")) ]
  ++ ltuCmds "c3a" (sv "t3") (sv "b3")
  ++ [ .RScalarSetExpr "s3" (.SAdd (sv "t3") (sv "c2")) ]
  ++ ltuCmds "c3b" (sv "s3") (sv "t3")
  ++ [ .RScalarSetExpr "c3" (.SAdd (sv "c3a") (sv "c3b"))
     , .RScalarSetExpr "t4" (.SAdd (sv "b4") (sv "a2")) ]
  ++ ltuCmds "c4a" (sv "t4") (sv "b4")
  ++ [ .RScalarSetExpr "s4" (.SAdd (sv "t4") (sv "c3")) ]
  ++ ltuCmds "c4b" (sv "s4") (sv "t4")
  ++ [ .RScalarSetExpr "c4" (.SAdd (sv "c4a") (sv "c4b"))
     , .RScalarSetExpr "t5" (.SAdd (sv "b5") (sv "a3")) ]
  ++ ltuCmds "c5a" (sv "t5") (sv "b5")
  ++ [ .RScalarSetExpr "s5" (.SAdd (sv "t5") (sv "c4")) ]
  ++ ltuCmds "c5b" (sv "s5") (sv "t5")
  ++ [ .RScalarSetExpr "c5" (.SAdd (sv "c5a") (sv "c5b"))
     , .RScalarSetExpr "s6" (.SAdd (sv "b6") (sv "c5")) ]
  ++ ltuCmds "c6" (sv "s6") (sv "b6")
  ++ [ .RScalarSetExpr "s7" (.SAdd (sv "b7") (sv "c6")) ]

/-- Store `r0..r7` through the `rp` pointer. -/
def storeOutputs : List LowCT :=
  [ .RArrStore rpLoc "ix0" ⟨"b0", .TU64⟩
  , .RArrStore rpLoc "ix1" ⟨"b1", .TU64⟩
  , .RArrStore rpLoc "ix2" ⟨"s2", .TU64⟩
  , .RArrStore rpLoc "ix3" ⟨"s3", .TU64⟩
  , .RArrStore rpLoc "ix4" ⟨"s4", .TU64⟩
  , .RArrStore rpLoc "ix5" ⟨"s5", .TU64⟩
  , .RArrStore rpLoc "ix6" ⟨"s6", .TU64⟩
  , .RArrStore rpLoc "ix7" ⟨"s7", .TU64⟩ ]

/-- The full straight-line `probe_addinto8_at2` body. -/
def body : LowCT := seqAll (idxInit ++ loadInputs ++ columns ++ storeOutputs)

/-- Head-first kernel context `[addp, basep, rp]`. -/
def inΓ : Ctx := [.memref 4, .memref 8, .memref 8]

/-- `rp` deepest (→ RDI), then `basep` (→ RSI), then `addp` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 8) "rp").bind
    (t := .memref 8) "basep").bind (t := .memref 4) "addp"

/-- Push `body` through the direct control front, cap with `ret rp`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 8)) :=
  match translateDialectControl inVM body with
  | some r =>
      match r.vm.lookup "rp" with
      | some ⟨.memref 8, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`. -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

-- The front translates and lowers `probe_addinto8_at2` end-to-end.
#guard loweredOpt.isSome

/-- The owned `Lprog` for `probe_addinto8_at2` under the buffers-only ABI. -/
def lprog : Option Lprog :=
  loweredOpt.map (fun s =>
    Com.toLprogPhysAbi s.2.2 "probe_addinto8_at2"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The owned AT&T `.s` text for `probe_addinto8_at2`. -/
def asm : Option String := lprog.map renderOwned

end AddInto8At2

/-- The `probe_addinto8_at2` owned leaf `.s`. -/
def probeAddInto8At2Asm : Option String := AddInto8At2.asm

/-! ## 3. Buffer types and the orchestration schedule

Root-order slots (`OrchestrationFront` §Slot convention): slot `0` is the tail
(oldest) element of the context, the highest slot its head. The array-ABI backend
packs argument buffer `j` at `inArgOff j` in root order, so with `ap` at slot 0
and `bp` at slot 1 the C input pointer addresses `[ap | bp]`. -/

/-- A 4-limb buffer (each input half, and every partial product), 32 bytes. -/
abbrev B4 : JasminTy := .stackArr 64 4

/-- The 8-limb result / accumulator buffer, 64 bytes. -/
abbrev B8 : JasminTy := .stackArr 64 8

/-- The orchestration argument context, newest-first `[bp, ap]`: `ap` is the tail
    (root slot 0), `bp` the head (root slot 1). -/
abbrev OrchΓ : Ctxt jasminDialect := [B4, B4]

/-- The 7-call reg-ptr-out multiply schedule. `nArgs = 2`, so call `k` binds its
    result at slot `2 + k`.

    * four `probe_mul2` products at sub-buffer offsets (slots 2..5);
    * `probe_join8(p00, p11)` seating the corner products (slot 6);
    * two `probe_addinto8_at2` adds of the middle products (slots 7, 8).

    Result slot 8 (type `B8`) is the full 512-bit product. -/
def mul4Schedule : List CallPhase :=
  [ { leaf := "probe_mul2", argTys := [B4, B4], retTy := B4, argSlots := [0, 1], argOffs := [0, 0] }
  , { leaf := "probe_mul2", argTys := [B4, B4], retTy := B4, argSlots := [0, 1], argOffs := [0, 16] }
  , { leaf := "probe_mul2", argTys := [B4, B4], retTy := B4, argSlots := [0, 1], argOffs := [16, 0] }
  , { leaf := "probe_mul2", argTys := [B4, B4], retTy := B4, argSlots := [0, 1], argOffs := [16, 16] }
  , { leaf := "probe_join8", argTys := [B4, B4], retTy := B8, argSlots := [2, 5] }
  , { leaf := "probe_addinto8_at2", argTys := [B8, B4], retTy := B8, argSlots := [6, 3] }
  , { leaf := "probe_addinto8_at2", argTys := [B8, B4], retTy := B8, argSlots := [7, 4] } ]

/-- The front-generated straight-line orchestration `Com`. Returns the slot-8
    result (type `B8`). `none` only on an ill-typed / out-of-range slot. -/
def mul4SchedCom : Option (Com jasminDialect OrchΓ B8) :=
  buildOrchCom OrchΓ mul4Schedule 8 B8

-- Generation gate: the schedule resolves to a well-typed orchestration `Com`
-- (front / dialect level, not the render).
#guard mul4SchedCom.isSome

/-! ## 4. Array-ABI export

`Com.toLprogArrAbi` threads the schedule's per-call operand byte offsets onto the
array-ABI call records before `emitOneCall` folds them into the operand `leaq`
displacements. `schedArgOffs mul4Schedule` is the `argOffs` of each phase in call
order. -/

/-- The owned AT&T `.s` for `mpn_mul4_sched`: the array-ABI orchestration with the
    schedule's operand byte offsets, rendered by the owned printer. -/
def mul4SchedAsm : Option String :=
  mul4SchedCom.map (fun c =>
    renderOwned (Com.toLprogArrAbi c "mpn_mul4_sched" (schedArgOffs mul4Schedule)))

/-! ## 5. Emit driver

The renders are written while this module elaborates, so `lake` owns them as
build outputs. The four `.s` — the orchestration and its three owned leaf
callees (`probe_mul2` reused from `MpnMul2FixedFrontEmit`) — link into the C
byte-KAT against a `__int128` concatenated-input reference. -/

/-- Write the orchestration and the leaf `.s` into the reg-ptr-out KAT gen
    directory. -/
def emitMain : IO Unit := do
  let dir := "bench/regptr_out_probe/gen_com"
  IO.FS.createDirAll dir
  match mul4SchedAsm with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_mul4_sched_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/mpn_mul4_sched_owned.s"
      IO.println "  array-ABI orchestration, sub-buffer offset reads, REAL call probe_mul2/join8/addinto8"
  | none => throw (IO.userError "buildOrchCom / offset lowering declined the mul4 schedule")
  match probeJoin8Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_join8_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_join8_owned.s"
  | none => IO.println "SKIP probe_join8: front declined"
  match probeAddInto8At2Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_addinto8_at2_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_addinto8_at2_owned.s"
  | none => IO.println "SKIP probe_addinto8_at2: front declined"
  match MpnMul2FixedFrontEmit.probeMul2Asm with
  | some s =>
      IO.FS.writeFile (dir ++ "/probe_mul2_owned.s") s
      IO.println "WROTE bench/regptr_out_probe/gen_com/probe_mul2_owned.s"
  | none => IO.println "SKIP probe_mul2: fixed-2 schoolbook multiply front declined"

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4SchedFrontEmit
