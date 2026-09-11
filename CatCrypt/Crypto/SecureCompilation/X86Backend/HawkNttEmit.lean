/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.HawkPointwiseEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.HawkPointwiseEmit

/-!
# HAWK-512 NTT-domain kernels through the OWNED x86 backend (no jasminc)

The two mod-`18433` NTT butterflies (`hawk18433_ntt_bfly` /
`hawk18433_intt_bfly`) and the pointwise Montgomery multiply
(`hawk18433_pointwise_montymul`) rendered through the OWNED x86 backend, all
FRONT-COMPILED — **no hand-built `Com`, no jasminc**.

## Butterflies: straight-line front, two u32 lanes per u64 word

Each butterfly's twiddle `s` is a plain input register, so one butterfly is a
straight-line block — no loop, no twiddle indexing. Its LowCT body front-compiles
through the straight-line front and lowers to the owned backend:

```
  bflyBody (LowCT: RScalarSetExpr Montgomery butterfly + `& 0xFFFFFFFF` u32 wraps)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  Com jasminDialect (replicate 2 r64) r64
    --(Com.toLprogPhysAbi)-------->  Lprog (physical-register, two-address, SysV ABI)
    --(renderLprogAtt)------------>  AT&T `.s` (assembled by `as`/`cc`, no jasminc)
```

The front's scalar words are 64-bit (`RScalarSetExpr ↦ .sword 64 ↦ .reg 64`), so
the emitted loads/stores are 8-byte. `hawk_ntt_kat.c`'s arrays are `uint32_t`
(4-byte stride), so the kernel views them **as `uint64_t`**: each 64-bit word
holds two little-endian `uint32_t` coefficients. The forward-butterfly ABI
`inp[8] = { x1, x2, s, Q, Q0I, 16, Q, 1 }` viewed as `uint64_t[4]` is
`inp64[0] = { x1, x2 }`, `inp64[1] = { s, Q }`, so `x1 = inp64[0] & mask`,
`x2 = inp64[0] >> 32`, `s = inp64[1] & mask`; the modulus-arithmetic constants
(`Q`, `Q0I`, `16`, `1`, `HalfC`) are all front-materialised literals, never read
from memory. The two output lanes pack into `out64[0] = out0 ^ (out1 << 32)`,
byte-identical to the `uint32_t out[2]` the reference reads. The inverse
butterfly (`inp[10] = { x1, x2, s, Q, 0, Q0I, 16, Q, 1, (Q+1)/2 }`) reads the
same two packed words `inp64[0]`, `inp64[1]`.

The `uint32_t` wraparound of the reference (`modq.h`, `Q == 18433`) is reproduced
by masking each `Q − reg` / `a·b` / `a·Q0I` result with `& 0xFFFFFFFF` in the
64-bit words (the sign-bit-at-16 conditional field reductions rely on it).

## Pointwise: re-exported from the rolled front sibling

`hawk18433_pointwise_montymul` is re-exported from
`HawkPointwiseEmit.lean`, whose deployed `ComL` is a
`rolledForLoopN` (`translateDialectControl` + `cryptoDialectToJasminCom`, one
body copy + a real `jne` back-edge, 2-pointer packed ABI). This drops the
512-coeff *unrolled* hand-`Com` (which OOMs a 14 GB host on ABI export) in favour
of the memory-bounded rolled front emit.

## What is verified vs KAT-gated

* **Verified (front provenance)**: `ntt_front_provenance` / `intt_front_provenance`
  — the deployed butterfly `Com` IS the front pipeline's output
  (`translateDialectControl` → `cryptoDialectToJasminCom`); the pointwise
  provenance lives on `HawkPointwiseEmit.pw_provenance`.
* **Trusted (thin)**: `LprogAsmPrinter.renderLprogAtt` + `gas` + the SysV leaf
  ABI frame — the same surface every owned backend trusts; **no jasminc**, no
  `jasminc_preserves_ct`.
* **KAT-gated**: byte-identical to the HAWK reference `mq18433_NTT` /
  `mq18433_iNTT` / `mq18433_montymul` over random degree-512 polynomials
  (`bench/hawk_compare/hawk_ntt_kat.c`), driving the reference's own loop nest
  with these emitted kernels substituted for its inline arithmetic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.HawkNttEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 0. Dimensions, modulus, Montgomery constant, packing mask -/

/-- The `reg 64` dialect type (the front emit's word width). -/
abbrev r64 : JasminTy := .reg 64
/-- HAWK-512 modulus `q = 18433`. -/
abbrev Q : Nat := 18433
/-- `Q0I = -1/q mod 2³²` (`modq.h`, `Q == 18433`). -/
abbrev Q0I : Nat := 3955247103
/-- `(Q+1)/2 = 9217`, the `half` add-back constant. -/
abbrev HalfC : Nat := 9217
/-- `uint32_t` wrap mask `2³² − 1` (`& 0xFFFFFFFF` reproduces the reference's
    `uint32_t` wraparound and extracts the low lane). -/
abbrev u32Mask : Nat := 4294967295

/-! ## 1. The Montgomery / field ops as covered-LowCT statement builders

Every op keeps its values in `[1..q]` (`modq.h`'s representation) and reproduces
the reference's `uint32_t` wraparound by masking each wrapping intermediate with
`& u32Mask`. Fresh intermediates are `pfx`-prefixed to stay distinct. -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- Montgomery reduce `dstN := montyred(srcN) = ((((src·Q0I) mod 2³²) >> 16)·Q
    mod 2³²) >> 16) + 1`. -/
def montyredStmts (pfx srcN dstN : String) : List LowCT :=
  [ .RScalarSetExpr (pfx ++ "t1") (.SAnd (.SMul (.SVar srcN) (.SLit Q0I)) (.SLit u32Mask)),
    .RScalarSetExpr (pfx ++ "t1h") (.SShr (.SVar (pfx ++ "t1")) (.SLit 16)),
    .RScalarSetExpr (pfx ++ "t2") (.SAnd (.SMul (.SVar (pfx ++ "t1h")) (.SLit Q)) (.SLit u32Mask)),
    .RScalarSetExpr dstN (.SAdd (.SShr (.SVar (pfx ++ "t2")) (.SLit 16)) (.SLit 1)) ]

/-- Montgomery multiply `dstN := montymul(aN, bN) = montyred((a·b) mod 2³²)`. -/
def montymulStmts (pfx aN bN dstN : String) : List LowCT :=
  .RScalarSetExpr (pfx ++ "p") (.SAnd (.SMul (.SVar aN) (.SVar bN)) (.SLit u32Mask))
    :: montyredStmts pfx (pfx ++ "p") dstN

/-- Field add `dstN := add(x,y) = Q − ((Q − (x+y)) + (Q & ((Q−(x+y)) >> 16)))`. -/
def qaddStmts (pfx xN yN dstN : String) : List LowCT :=
  [ .RScalarSetExpr (pfx ++ "s") (.SAdd (.SVar xN) (.SVar yN)),
    .RScalarSetExpr (pfx ++ "a1") (.SAnd (.SSub (.SLit Q) (.SVar (pfx ++ "s"))) (.SLit u32Mask)),
    .RScalarSetExpr (pfx ++ "a2") (.SShr (.SVar (pfx ++ "a1")) (.SLit 16)),
    .RScalarSetExpr (pfx ++ "a3") (.SAnd (.SVar (pfx ++ "a2")) (.SLit Q)),
    .RScalarSetExpr (pfx ++ "a4")
      (.SAnd (.SAdd (.SVar (pfx ++ "a1")) (.SVar (pfx ++ "a3"))) (.SLit u32Mask)),
    .RScalarSetExpr dstN (.SAnd (.SSub (.SLit Q) (.SVar (pfx ++ "a4"))) (.SLit u32Mask)) ]

/-- Field sub `dstN := sub(x,y) = Q − ((y−x) + (Q & ((y−x) >> 16)))`. -/
def qsubStmts (pfx xN yN dstN : String) : List LowCT :=
  [ .RScalarSetExpr (pfx ++ "d") (.SAnd (.SSub (.SVar yN) (.SVar xN)) (.SLit u32Mask)),
    .RScalarSetExpr (pfx ++ "d2") (.SShr (.SVar (pfx ++ "d")) (.SLit 16)),
    .RScalarSetExpr (pfx ++ "d3") (.SAnd (.SVar (pfx ++ "d2")) (.SLit Q)),
    .RScalarSetExpr (pfx ++ "d4")
      (.SAnd (.SAdd (.SVar (pfx ++ "d")) (.SVar (pfx ++ "d3"))) (.SLit u32Mask)),
    .RScalarSetExpr dstN (.SAnd (.SSub (.SLit Q) (.SVar (pfx ++ "d4"))) (.SLit u32Mask)) ]

/-- Field half `dstN := half(x) = (x >> 1) + (((Q+1)/2) & −(x & 1))`. -/
def qhalfStmts (pfx xN dstN : String) : List LowCT :=
  [ .RScalarSetExpr (pfx ++ "lo") (.SAnd (.SVar xN) (.SLit 1)),
    .RScalarSetExpr (pfx ++ "neg") (.SAnd (.SSub (.SLit 0) (.SVar (pfx ++ "lo"))) (.SLit u32Mask)),
    .RScalarSetExpr (pfx ++ "m") (.SAnd (.SVar (pfx ++ "neg")) (.SLit HalfC)),
    .RScalarSetExpr (pfx ++ "hi") (.SShr (.SVar xN) (.SLit 1)),
    .RScalarSetExpr dstN (.SAdd (.SVar (pfx ++ "hi")) (.SVar (pfx ++ "m"))) ]

/-- Unpack the two packed input words: `x1 = inp64[0] & mask`,
    `x2 = inp64[0] >> 32`, `s = inp64[1] & mask` (`w0`/`w1` are the two `u64`
    input words). -/
def unpackStmts : List LowCT :=
  [ .RScalarSetExpr "x1" (.SAnd (.SVar "w0") (.SLit u32Mask)),
    .RScalarSetExpr "x2" (.SShr (.SVar "w0") (.SLit 32)),
    .RScalarSetExpr "s" (.SAnd (.SVar "w1") (.SLit u32Mask)) ]

/-! ## 2. The two butterfly bodies, authored as covered LowCT -/

/-- Forward CT butterfly: `prod = montymul(x2,s)`, `out0 = add(x1,prod)`,
    `out1 = sub(x1,prod)`, packed `out0 ^ (out1 << 32)`. -/
def nttBflyBody : LowCT := seqAll (
  unpackStmts
    ++ montymulStmts "mm" "x2" "s" "prod"
    ++ qaddStmts "qa" "x1" "prod" "out0"
    ++ qsubStmts "qs" "x1" "prod" "out1"
    ++ [ .RScalarSetExpr "packed" (.SXor (.SVar "out0") (.SShl (.SVar "out1") (.SLit 32))),
         .RScalarSetExpr "res" (.SVar "packed") ])

/-- Inverse GS butterfly: `sum = add(x1,x2)`, `diff = sub(x1,x2)`,
    `res0 = half(sum)`, `res1 = montymul(s,diff)`, packed `res0 ^ (res1 << 32)`. -/
def inttBflyBody : LowCT := seqAll (
  unpackStmts
    ++ qaddStmts "ia" "x1" "x2" "sum"
    ++ qsubStmts "is" "x1" "x2" "diff"
    ++ montymulStmts "im" "s" "diff" "res1"
    ++ qhalfStmts "ih" "sum" "res0"
    ++ [ .RScalarSetExpr "packed" (.SXor (.SVar "res0") (.SShl (.SVar "res1") (.SLit 32))),
         .RScalarSetExpr "res" (.SVar "packed") ])

/-! ## 3. Straight-line front-compilation

The body runs over `srcCtx = [w0, w1]` (two packed `u64` input words). The front
translates the covered LowCT and we cap with `ret "res"` (the packed output
word). -/

/-- Bind a name list onto a `replicate`-`sword 64` context, first name = head. -/
def bindAll : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindAll ns).bind n

/-- The two packed `u64` input words (`w0 = inp64[0] = {x1,x2}`,
    `w1 = inp64[1] = {s,·}`). -/
def wordNames : List String := ["w0", "w1"]

/-- The front source context: two `u64` scalar slots. -/
abbrev srcCtx : Ctx := List.replicate 2 (.sword 64)

/-- The source `VarMap` (word 0 = `w0` at the head). -/
def srcVM : VarMap srcCtx := bindAll wordNames

/-- Push a butterfly body through the `CProg`-free control front and cap with
    `ret "res"`. `none` if the front declines. -/
def frontComAt (body : LowCT) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM body with
  | some r =>
      match r.vm.lookup "res" with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- Front source, lowered to the jasmin dialect. -/
def loweredOpt (body : LowCT) :=
  (frontComAt body).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front emit's input context: two `r64` packed words. -/
abbrev inCtxtF : Ctxt jasminDialect := List.replicate 2 r64

/-- **Front gate (forward).** The packed forward-butterfly body front-compiles
    and lowers end to end. -/
theorem nttBflyLowered_isSome : (loweredOpt nttBflyBody).isSome := by native_decide

/-- **Front gate (inverse).** The packed inverse-butterfly body front-compiles
    and lowers end to end. -/
theorem inttBflyLowered_isSome : (loweredOpt inttBflyBody).isSome := by native_decide

/-- The **deployed** forward butterfly `Com` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
def nttBflyFrontCom : Com jasminDialect inCtxtF r64 :=
  (loweredOpt nttBflyBody).get nttBflyLowered_isSome

/-- The **deployed** inverse butterfly `Com` — FRONT-GENERATED. -/
def inttBflyFrontCom : Com jasminDialect inCtxtF r64 :=
  (loweredOpt inttBflyBody).get inttBflyLowered_isSome

/-- **Provenance (forward).** The front pipeline output IS the deployed forward
    butterfly `Com`. -/
theorem ntt_front_provenance : loweredOpt nttBflyBody = some nttBflyFrontCom :=
  (Option.some_get nttBflyLowered_isSome).symm

/-- **Provenance (inverse).** The front pipeline output IS the deployed inverse
    butterfly `Com`. -/
theorem intt_front_provenance : loweredOpt inttBflyBody = some inttBflyFrontCom :=
  (Option.some_get inttBflyLowered_isSome).symm

/-! ## 4. Owned-backend lowering (2-pointer packed ABI) + AT&T `.s`

2-pointer SysV ABI `(out, inp)` (`RDI = out`, `RSI = inp`). The two packed input
words load `w0` from `[RSI + 0]` (`inp64[0]`) and `w1` from `[RSI + 8]`
(`inp64[1]`); the single packed output word stores to `[RDI + 0]` (`out64[0]`).
`frontComAt`'s word 0 (`w0`) is the head binding, so its arg-slot is
`(nIn − 1) − 0 = 1` and `w1`'s is `0`. -/

/-- Load `w0` (arg-slot 1) from `[RSI + 0]`, `w1` (arg-slot 0) from `[RSI + 8]`. -/
def bflyInLoad : InLoadMap := fun s => if s ≤ 1 then some ("RSI", 8 * (1 - s)) else none

/-- Store the single packed output word to `[RDI + 0]` (`out64[0] = {out0,out1}`). -/
def bflyOut : OutStoreMap := [("RDI", 0)]

/-- The owned-backend forward butterfly `Lprog` (no jasminc). -/
def hawkNttBflyLprog : Lprog :=
  Com.toLprogPhysAbi nttBflyFrontCom "hawk18433_ntt_bfly"
    (fun _ => none) (fun _ => none) bflyInLoad bflyOut ["RDI", "RSI"] [64, 64]

/-- The owned-backend forward butterfly AT&T `.s` (no jasminc). -/
def hawkNttBflyAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned hawkNttBflyLprog

/-- The owned-backend inverse butterfly `Lprog` (no jasminc). -/
def hawkInttBflyLprog : Lprog :=
  Com.toLprogPhysAbi inttBflyFrontCom "hawk18433_intt_bfly"
    (fun _ => none) (fun _ => none) bflyInLoad bflyOut ["RDI", "RSI"] [64, 64]

/-- The owned-backend inverse butterfly AT&T `.s` (no jasminc). -/
def hawkInttBflyAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned hawkInttBflyLprog

/-! ## 5. Pointwise Montgomery multiply — the rolled front sibling

`hawk18433_pointwise_montymul` is the FRONT-COMPILED `rolledForLoopN` emit of
`HawkPointwiseEmit.lean` (one body copy + a real `jne` back-edge, 2-pointer
packed ABI). Re-exported here so this module still names the three NTT kernels;
its front provenance is `HawkPointwiseEmit.pw_provenance`. -/

/-- The owned-backend pointwise-montymul `Lprog` (rolled front, no jasminc). -/
def hawkPointwiseLprog : Lprog := HawkPointwiseEmit.hawkPointwiseLprog

/-- The owned-backend pointwise-montymul AT&T `.s` (rolled front, no jasminc). -/
def hawkPointwiseAsm : String := HawkPointwiseEmit.hawkPointwiseAsm

end CatCrypt.Crypto.SecureCompilation.X86Backend.HawkNttEmit
