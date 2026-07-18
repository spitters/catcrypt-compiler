/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# HAWK-512 NTT-domain pointwise Montgomery multiply, OWNED x86, 2-pointer packed ABI

`hawk_ntt_kat.c` calls the pointwise kernel with the **2-pointer** signature
`hawk18433_pointwise_montymul(out[512], inp[1028])` over `uint32_t` arrays: `inp`
holds both operand polynomials contiguously (`inp[0..511] = w1`,
`inp[512..1023] = w2`, the trailing `inp[1024..1027]` unused), and
`out[u] = mq18433_montymul(inp[u], inp[u+512])` for `u = 0 .. 511`.

## Front-compiled, NOT hand-authored — two u32 lanes per u64 word

The verified rolled-loop front (`rolledForLoopN` over `translateDialectControl`)
lowers a covered `LowCT` loop body to a genuine `ComL.forLoopN` (ONE body copy, a
real `jne` back-edge). Its array cells are 64-bit (`memref` ↦ `stackArr 64`), so
the emitted SIB stride is 8 bytes. The KAT's arrays are `uint32_t` (4-byte
stride), so the kernel views them **as `uint64_t`**: `out` as `uint64_t[256]`,
`inp` as `uint64_t[514]`, each 64-bit word holding two little-endian `uint32_t`
coefficients. Because the packed offset `512` (`uint32_t` units) is even, the two
`uint32_t` lanes at indices `2t` and `2t+1` share the same `uint64_t`-word offset
`256`, so one trip processes both lanes of word `t`:

```
  aw := inp[t]                         -- RArrLoad (SIB LOADIDX at the trip counter)
  bw := inp[t + 256]                   -- w2 word (uint64 offset 256 = 512 uint32)
  a0 := aw & 0xFFFFFFFF ; a1 := aw >> 32     -- w1 lanes 2t, 2t+1
  b0 := bw & 0xFFFFFFFF ; b1 := bw >> 32     -- w2 lanes 2t, 2t+1
  r0 := montymul(a0, b0)               -- lane 2t
  r1 := montymul(a1, b1)               -- lane 2t+1
  res := r0 ^ (r1 << 32)               -- disjoint fields, XOR = OR pack
  out[t] := res                        -- RArrStore (SIB STOREIDX at the trip counter)
```

The 256-trip loop writes `256` `uint64_t` = `512` `uint32_t` output cells,
byte-identical to the `uint32_t` reference. Lowered via `ComL.toLprogPhysAbi`
(2-pointer ABI `RDI = out`, `RSI = inp`) and rendered to AT&T `.s` through
`renderLprogAtt` — the same owned backend the NTT butterflies use, **no jasminc**.

## The Montgomery body (per lane), faithful u32 wrap in u64 words

Reference (`modq.h`, `Q == 18433`), all in `uint32_t` (each `*` wraps mod `2³²`):

```
  montyred(x)   = ((((x * Q0I) mod 2³²) >> 16) * Q mod 2³²) >> 16) + 1
  montymul(a,b) = montyred((a * b) mod 2³²)
```

with `Q0I = 3955247103 = -1/q mod 2³²`. The front's scalar words are `u64`; the
`uint32_t` wraparound is reproduced by masking each product with `& 0xFFFFFFFF`
(`x·Q0I < 2³⁰·2³² = 2⁶² < 2⁶⁴` never wraps in `u64`, so the mask IS the reduction;
the first product `a·b < q² ≈ 3.4·10⁸` never wraps at all).

## ABI

2-pointer SysV ABI `hawk18433_pointwise_montymul(out, inp)` (`RDI = out`,
`RSI = inp`), both passed as `uint32_t*` and addressed as `uint64_t` words.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.HawkPointwiseOwnedEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 0. Dimensions, modulus, Montgomery constant, packed offset -/

/-- Pointwise loop length in `u64` words (`2` coefficients per word, `512 / 2`). -/
abbrev N : Nat := 256
/-- Length of the packed input array in `u64` words (`inp = w1 ‖ w2 ‖ 4 consts`,
    `1028` `uint32_t` = `514` `uint64_t`). -/
abbrev NIN : Nat := 514
/-- The `u64` word working width (two `uint32_t` lanes per word). -/
abbrev W : Nat := 64
/-- The `uint32_t` wrap mask `2³² − 1` (`& 0xFFFFFFFF` reproduces the reference's
    `uint32_t` wraparound; it also extracts the low lane). -/
abbrev u32Mask : Nat := 4294967295
/-- `Q0I = -1/q mod 2³²` (`modq.h`, `Q == 18433`). -/
abbrev Q0I : Nat := 3955247103
/-- HAWK-512 modulus. -/
abbrev Q : Nat := 18433
/-- Packed offset in `u64` words: `w2`'s word for trip `t` is `inp[t + OFF]`
    (`512` `uint32_t` = `256` `uint64_t`; `512` even ⇒ both lanes share it). -/
abbrev OFF : Nat := 256

/-! ## 1. The two-lane Montgomery-multiply loop body, authored as covered LowCT

The loop body runs over `Γbody = [out:.memref nOut, idx:.sword 64,
inp:.memref nIn]` (accumulator first, loop index next, the single packed input
array as the one invariant). `idx` is the loop binder; `RArrLoad … idx` /
`RArrStore … idx` resolve it as the dynamic SIB index at the runtime trip
counter, and `idx` read as `.SVar "idx"` computes the packed `w2` word index. -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- One trip of the packed pointwise Montgomery multiply: read words `inp[idx]`
    (both `w1` lanes) and `inp[idx + off]` (both `w2` lanes), Montgomery-multiply
    the two lanes independently, pack `r0 ^ (r1 << 32)`, store to `out[idx]`. The
    `& 0xFFFFFFFF` masks are the reference's `uint32_t` wraps; the low mask and the
    `>> 32` shift split the two lanes. -/
def pwBodyLowCT (nOut nIn off : Nat) : LowCT := seqAll [
  .RArrLoad ⟨"aw", .TU64⟩ ⟨"inp", .TBytes (8 * nIn)⟩ "idx",
  .RScalarSetExpr "idx2" (.SAdd (.SVar "idx") (.SLit off)),
  .RArrLoad ⟨"bw", .TU64⟩ ⟨"inp", .TBytes (8 * nIn)⟩ "idx2",
  .RScalarSetExpr "a0" (.SAnd (.SVar "aw") (.SLit u32Mask)),
  .RScalarSetExpr "a1" (.SShr (.SVar "aw") (.SLit 32)),
  .RScalarSetExpr "b0" (.SAnd (.SVar "bw") (.SLit u32Mask)),
  .RScalarSetExpr "b1" (.SShr (.SVar "bw") (.SLit 32)),
  -- lane 0 = coefficient 2·idx
  .RScalarSetExpr "p0" (.SMul (.SVar "a0") (.SVar "b0")),
  .RScalarSetExpr "s0" (.SAnd (.SMul (.SVar "p0") (.SLit Q0I)) (.SLit u32Mask)),
  .RScalarSetExpr "s0h" (.SShr (.SVar "s0") (.SLit 16)),
  .RScalarSetExpr "m0" (.SAnd (.SMul (.SVar "s0h") (.SLit Q)) (.SLit u32Mask)),
  .RScalarSetExpr "m0h" (.SShr (.SVar "m0") (.SLit 16)),
  .RScalarSetExpr "r0" (.SAdd (.SVar "m0h") (.SLit 1)),
  -- lane 1 = coefficient 2·idx + 1
  .RScalarSetExpr "p1" (.SMul (.SVar "a1") (.SVar "b1")),
  .RScalarSetExpr "s1" (.SAnd (.SMul (.SVar "p1") (.SLit Q0I)) (.SLit u32Mask)),
  .RScalarSetExpr "s1h" (.SShr (.SVar "s1") (.SLit 16)),
  .RScalarSetExpr "m1" (.SAnd (.SMul (.SVar "s1h") (.SLit Q)) (.SLit u32Mask)),
  .RScalarSetExpr "m1h" (.SShr (.SVar "m1") (.SLit 16)),
  .RScalarSetExpr "r1" (.SAdd (.SVar "m1h") (.SLit 1)),
  -- pack: r0 in low 32 bits, r1 in high 32 bits — disjoint fields, XOR = OR
  .RScalarSetExpr "res" (.SXor (.SVar "r0") (.SShl (.SVar "r1") (.SLit 32))),
  .RArrStore ⟨"out", .TBytes (8 * nOut)⟩ "idx" ⟨"res", .TU64⟩ ]

/-- The body context: accumulator `out` (the output word array), loop index
    `idx`, invariant the single packed input `inp`. -/
abbrev Γbody (nOut nIn : Nat) : Ctx := [.memref nOut, .sword 64, .memref nIn]

/-- The body VarMap: `out ↦ .here`, `idx ↦ .there .here`, `inp` deeper. -/
def vmBody (nOut nIn : Nat) : VarMap (Γbody nOut nIn) :=
  (((VarMap.empty.bind (t := .memref nIn) "inp").bind
      (t := .sword 64) "idx").bind (t := .memref nOut) "out")

/-! ## 2. The outer program: front body → genuine `ComL.forLoopN`

Outer context `[out, inp]` (jasmin types `.stackArr 64 nOut`, `.stackArr 64 nIn`):
`out` is the accumulator seed (`.here`), `inp` the invariant seed (`.there .here`).
2-pointer ABI `hawk18433_pointwise_montymul(out, inp)`. -/

/-- The outer (kernel-argument) jasmin context: `[out, inp]`. -/
abbrev Γouter (nOut nIn : Nat) : Ctxt jasminDialect :=
  [.stackArr 64 nOut, .stackArr 64 nIn]

/-- The front-compiled rolled `ComL.forLoopN` (one body copy + back-edge), or
    `none` if the front declines. -/
def pwComLAt (nOut nIn off loopN : Nat) :
    Option (ComL (Γouter nOut nIn) (.stackArr 64 nOut)) :=
  rolledForLoopN (Γouter := Γouter nOut nIn) (accCTy := .memref nOut)
    (invCTys := [.memref nIn])
    loopN (vmBody nOut nIn) "out" (pwBodyLowCT nOut nIn off)
    (init := .here)
    (invs := .cons (.there .here) .nil)

/-- The deployed full-size (`N = 256` words = `512` coefficients) rolled loop. -/
def pwComLOpt : Option (ComL (Γouter N NIN) (.stackArr 64 N)) := pwComLAt N NIN OFF N

/-- **Front gate:** the packed pointwise body front-compiles to a genuine
    `ComL.forLoopN` at the deployed HAWK-512 size. -/
theorem pwComL_isSome : pwComLOpt.isSome := by native_decide

/-- The deployed rolled pointwise `ComL` — FRONT-GENERATED (`rolledForLoopN` over
    `translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
def pwComL : ComL (Γouter N NIN) (.stackArr 64 N) := pwComLOpt.get pwComL_isSome

/-- **Provenance.** The front pipeline, applied end to end, is DEFINITIONALLY the
    deployed pointwise `ComL`: a SINGLE `forLoopN` node. -/
theorem pw_provenance : pwComLOpt = some pwComL :=
  (Option.some_get pwComL_isSome).symm

/-! ## 3. Denote = the independent `montymul` spec (small packed instance)

The full-size loop denote is too heavy for `native_decide`; the body is a pure
per-word two-lane map, so a small packed instance (`sN = 4` words, `inp` length
`2·sN` words, word offset `sN`) certifies that the body computes the
`uint32_t`-faithful `montymul` at both lanes of every output word. -/

/-- INDEPENDENT plain-`Nat` `montyred`, faithful to the `uint32_t` `modq.h`
    arithmetic (`mod 2³²` after each multiply). -/
def montyredNat (x : Nat) : Nat :=
  let t1  := (x * Q0I) % 4294967296
  let t1h := t1 / 65536
  let t2  := (t1h * Q) % 4294967296
  t2 / 65536 + 1

/-- INDEPENDENT plain-`Nat` `montymul`: `montyred((a·b) mod 2³²)`. -/
def montymulNat (a b : Nat) : Nat := montyredNat ((a * b) % 4294967296)

/-- Small word-loop length for the in-kernel `native_decide` denote check. -/
abbrev sN : Nat := 4

/-- Deterministic residue stream in `[1..q]` for `uint32_t`-index `k`
    (the KAT seed shape lands in `[1..Q]`). -/
def coeffN (k : Nat) : Nat := (k * 37 + 5) % Q + 1

/-- Deterministic packed sample: `u64`-word `t` holds coefficients `2t` (low) and
    `2t+1` (high). Words `0..sN-1` are `w1`, words `sN..2·sN-1` are `w2`. -/
def sampleInp : Fin (2 * sN) → BitVec W := fun t =>
  BitVec.ofNat W (coeffN (2 * t.val) ||| (coeffN (2 * t.val + 1) <<< 32))

/-- INDEPENDENT packed spec for output word `t`: lane `2t` is
    `montymul(w1[2t], w2[2t])`, lane `2t+1` is `montymul(w1[2t+1], w2[2t+1])`,
    packed low/high (`w2`'s word is `t + sN`). -/
def pwSpecWord (t : Nat) : Nat :=
  montymulNat (coeffN (2 * t)) (coeffN (2 * (t + sN)))
    ||| (montymulNat (coeffN (2 * t + 1)) (coeffN (2 * (t + sN) + 1)) <<< 32)

/-- The small packed instance also front-compiles. -/
theorem pwSmall_isSome : (pwComLAt sN (2 * sN) sN sN).isSome := by native_decide

/-- The front-compiled small-instance rolled loop. -/
def pwProgS : ComL (Γouter sN (2 * sN)) (.stackArr 64 sN) :=
  (pwComLAt sN (2 * sN) sN sN).get pwSmall_isSome

/-- **Denote = montymul spec.** At every output word the front-compiled rolled
    packed loop denotes the independent `uint32_t`-faithful `montymul` of both
    lanes of the packed sample stream, packed low/high. -/
theorem pwProgS_denote :
    (ComL.denote pwProgS (.cons (fun _ => (0 : BitVec W)) (.cons sampleInp .nil)))
      = (fun t : Fin sN => BitVec.ofNat W (pwSpecWord t.val)) := by
  funext t; revert t; native_decide

/-! ## 4. Owned-backend lowering (2-pointer ABI) + AT&T `.s` -/

/-- The owned-backend pointwise-montymul `Lprog`, 2-pointer packed ABI
    (`RDI = out`, `RSI = inp`), no jasminc. -/
def hawkPointwiseLprog : Lprog :=
  ComL.toLprogPhysAbi pwComL "hawk18433_pointwise_montymul" (argName 0) [argName 1]
    (fun _ => none) (fun _ => none) ["RDI", "RSI"] [64, 64]

/-- The owned-backend pointwise-montymul AT&T `.s` (no jasminc). -/
def hawkPointwiseAsm : String := renderLprogAtt hawkPointwiseLprog

/-! ## 5. Shape checks on the emitted asm (value via the KAT) -/

/-- Local substring test. -/
def occursIn (needle hay : String) : Bool := (hay.splitOn needle).length ≥ 2

/-- The emitted asm carries the leaf label, the mod-18433 Montgomery constant
    `Q0I` (`$3955247103`), the modulus `$18433`, the `uint32_t` wrap mask
    (`$4294967295`), the packed-word offset add (`$256`), a real `jne` loop
    back-edge (rolled, NOT unrolled), and no unhandled-op sentinel. (Value: the
    `hawk_ntt_kat.c` byte-KAT.) -/
theorem pw_asm_shape :
    occursIn "hawk18433_pointwise_montymul" hawkPointwiseAsm = true
      ∧ occursIn "$3955247103" hawkPointwiseAsm = true
      ∧ occursIn "$18433" hawkPointwiseAsm = true
      ∧ occursIn "$4294967295" hawkPointwiseAsm = true
      ∧ occursIn "$256" hawkPointwiseAsm = true
      ∧ occursIn "jne" hawkPointwiseAsm = true
      ∧ occursIn "UNHANDLED" hawkPointwiseAsm = false := by native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.HawkPointwiseOwnedEmit
