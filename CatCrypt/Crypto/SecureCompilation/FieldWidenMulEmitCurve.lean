/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit

/-!
# `128×64 → 192` widening multiply for a curve field, OWNED x86 (front-generated)

`(z2:z1:z0) = (a1·2^64 + a0)·b0`, three 64-bit output words — the CIOS core
schoolbook widening product. FRONT-GENERATED via `translateDialectControl` +
`cryptoDialectToJasminCom` over `SMul`/`SMulHiU` (low/high 64-bit products) + a
branch-free carry, rendered through the `fuseMulHiLprog` mulx post-pass:

```
  widenBody (LowCT)  --(translateDialectControl + cryptoDialectToJasminCom)-->
  curveWiden128Com (Com jasminDialect)  --(Com.toLprogPhysAbi, owned RA)-->  Lprog
                    --(fuseMulHiLprog saveRdx:=true; renderLprogAtt)-->  gen_com/curve_widen128.s
```

## Reference (matches `bench/secp256k1_compare/curve_widen128_kat.c`)

```
z0 = lo(a0·b0);  z1 = hi(a0·b0) + lo(a1·b0) (+carry);  z2 = hi(a1·b0) + carry
```
Carry-out of `h + l` is branch-free: `((h>>1)+(l>>1)+((h & l)&1)) >>> 63`.

## Two mulx-RA seams closed to reach byte-correctness

The two `mul`+`mulhi` pairs fuse to two `mulx`. Reaching a byte-correct emission
needed closing two owned-RA/mulx interaction seams:

* **Coincident mulx destinations** (`LprogAsmPrinter`): the owned RA homes a
  `mulx`'s LOW and HIGH outputs in the SAME physical register when the low word is
  redundant (`z0` is materialised by a separate `imul`), so `mulx s, r, r` clobbers
  the high word. The printer now routes the redundant low to a red-zone-saved
  scratch when `dst_lo == dst_hi`.
* **`%rdx`-homed high word across the next `mulx` pin** (`fuseMulHiLprog
  saveRdx := true`): the RA can home the first `mulx`'s high word (`hi00`) in
  `%rdx`, which the second `mulx`'s implicit-multiplicand `MOV RDX, a1` pin then
  clobbers. `saveRdx` brackets each pin with an `R15` save/restore and renames the
  later `%rdx` reads, so the high word survives.

## ABI

`curve_widen128(uint64_t *out, const uint64_t *inp)`, `inp[0]=a0, inp[1]=a1,
inp[2]=b0`, `out[0..2]=z0,z1,z2`. `RDI=out`, `RSI=inp`, `abiW := 64`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldWidenMulEmitCurve

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (Com.toLprogPhysAbi InLoadMap OutStoreMap Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- Number of input words loaded from `inp`: `a0, a1, b0`. -/
abbrev NIN : Nat := 3

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- `(z2:z1:z0) = (a1·2^64 + a0)·b0` as a covered `LowCT` chain, ending with three
    output copies `o0 := z0, o1 := z1, o2 := z2`. -/
def widenBody : LowCT := seqAll [
  .RScalarSetExpr "z0"    (.SMul (.SVar "a0") (.SVar "b0")),
  .RScalarSetExpr "hi00"  (.SMulHiU (.SVar "a0") (.SVar "b0")),
  .RScalarSetExpr "lo10"  (.SMul (.SVar "a1") (.SVar "b0")),
  .RScalarSetExpr "hi10"  (.SMulHiU (.SVar "a1") (.SVar "b0")),
  .RScalarSetExpr "z1"    (.SAdd (.SVar "hi00") (.SVar "lo10")),
  .RScalarSetExpr "chalf"
    (.SAdd (.SAdd (.SShr (.SVar "hi00") (.SLit 1)) (.SShr (.SVar "lo10") (.SLit 1)))
      (.SAnd (.SAnd (.SVar "hi00") (.SVar "lo10")) (.SLit 1))),
  .RScalarSetExpr "c"     (.SShr (.SVar "chalf") (.SLit 63)),
  .RScalarSetExpr "z2"    (.SAdd (.SVar "hi10") (.SVar "c")),
  .RScalarSetExpr "o0"    (.SVar "z0"),
  .RScalarSetExpr "o1"    (.SVar "z1"),
  .RScalarSetExpr "o2"    (.SVar "z2") ]

/-- The source context: 3 `u64` scalar inputs `a0, a1, b0`. -/
def srcCtx : Ctx := List.replicate NIN (.sword 64)

/-- The source `VarMap`: `b0` deepest, `a0` head → `a0 ← inp[0]`, `a1 ← inp[1]`,
    `b0 ← inp[2]`. -/
def srcVM : VarMap srcCtx :=
  ((VarMap.empty.bind "b0").bind "a1").bind "a0"

/-- Push `widenBody` through the front and cap with `ret <name>`. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM widenBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted widening mul lowered to the jasmin dialect (capped at `o2`). -/
def curveWiden128LoweredOpt :=
  (frontComAt "o2").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem curveWiden128Lowered_isSome : curveWiden128LoweredOpt.isSome := by native_decide

/-- The input context of the `Com`: the 3 `r64` input words `[a0, a1, b0]`. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate NIN r64

/-- **The widening-multiply kernel as a `Com jasminDialect`** — FRONT-GENERATED. -/
def curveWiden128Com : Com jasminDialect inCtxt r64 :=
  curveWiden128LoweredOpt.get curveWiden128Lowered_isSome

/-- **Provenance**: the front pipeline is DEFINITIONALLY the deployed `Com`. -/
theorem curveWiden128Com_provenance :
    (frontComAt "o2").bind DialectToJasminCom.cryptoDialectToJasminCom
      = some curveWiden128Com :=
  (Option.some_get curveWiden128Lowered_isSome).symm

/-- Input-load map: slot → `(base, byte-offset)`; input word `i = (NIN−1)−slot`
    from `inp[i]` at byte offset `8·i`. -/
def inLoadMap : InLoadMap := fun slot =>
  if slot ≤ NIN - 1 then some ("RSI", ((NIN - 1) - slot) * 8) else none

/-- Output-store map: `z0,z1,z2` to `out[0..2]`. -/
def outStoreMap : OutStoreMap := [("RDI", 0), ("RDI", 8), ("RDI", 16)]

/-- The `curve_widen128` kernel as an owned-RA two-address `Lprog`. -/
def curveWiden128Lprog : Lprog :=
  Com.toLprogPhysAbi curveWiden128Com "curve_widen128"
    (fun _ => none) (fun _ => none) inLoadMap outStoreMap
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (residence := none)
    (abiW := 64)

/-- The owned AT&T `.s`. `fuseMulHiLprog … saveRdx := true` protects a `%rdx`-homed
    high word across the next `mulx`'s multiplicand pin; the printer routes any
    `dst_lo == dst_hi` redundant low to a scratch. -/
def curveWiden128Asm : String :=
  renderLprogAtt
    (CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit.fuseMulHiLprog
      curveWiden128Lprog true)

/-- The byte-correct widening-mul owned-emit driver. -/
def emitWiden : IO Unit := do
  let path : System.FilePath := "bench/secp256k1_compare/gen_com/curve_widen128.s"
  IO.FS.writeFile path curveWiden128Asm
  IO.println s!"CURVE-WIDEN128 emit OK : {path} ({curveWiden128Asm.toUTF8.size} bytes, symbol curve_widen128)"

/-- Independent plain-`Nat` reference `(z2:z1:z0) = (a1·2^64 + a0)·b0`. -/
def widenRef (a0 a1 b0 : Nat) : Nat × Nat × Nat :=
  let p := (a1 * 2 ^ 64 + a0) * b0
  (p % 2 ^ 64, (p / 2 ^ 64) % 2 ^ 64, p / 2 ^ 128)

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitWiden

end CatCrypt.Crypto.SecureCompilation.FieldWidenMulEmitCurve
