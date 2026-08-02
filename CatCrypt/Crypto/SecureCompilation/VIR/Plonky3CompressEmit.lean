/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom

set_option autoImplicit false

/-!
# Plonky3 Merkle 2-to-1 compress, FRONT-COMPILED (`plonky3_merkle_compress_rc`)

The Plonky3 Merkle 2-to-1 compress leaf, sourced through the verified
`CProg`-free front — NO hand-built `Com` anywhere in the emit path:

```
  compressBody (LowCT: RScalarSetExpr u64 word math over the 15 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  compressComFinal : Com jasminDialect inCtxt r64
```

Consumers (`Plonky3EmitMain` / `Plonky3WholeProverEmit` /
`Plonky3OrchLoopsEmit` / `ZkSumCheckWholeProverEmit`) render
`compressComFinal` to owned AT&T `.s` via `Com.toLprogPhysAbi` (constants as
`immSlotMap` immediates, runtime words loaded from the `RSI` input pointer,
outputs stored via `stdOutStore 4`) under the export symbol
`plonky3_merkle_compress_rc`.

## Spec (matches `ref_compress` in `compress_from_rustcmd_kat.c`)

Per limb `i ∈ {0,1,2,3}` of two 4-limb digests `l`, `r` (wrapping u64):
```
  o[i] = ((l[i] + r[i]) * 0x9E + i) ^ (l[i] * 0x6D) ^ r[i]
```
then a serial diffusion pass for `j ∈ {1,2,3}`:
```
  o[j] = o[j] ^ (o[j-1] * 0xC5)      (with the already-diffused o[j-1])
```

## ABI (unchanged)

15 input words: `inp[0..3]` = left digest `l`, `inp[4..7]` = right digest `r`,
`inp[8..14]` = the constants `0x9E, 0x6D, 0xC5, 0, 1, 2, 3` (context words the
owned render materializes as immediates via `constNat`). 4 output words: the
**last four bindings** of the `Com` are the front's identity copies of
`o[0..3]` in order, matching `toLprogPhysAbi`'s last-`nOut` output convention.

## Gates

* In-model: the front translates + lowers (`compressLowered_isSome`); the four
  output-capped front programs denote the independent `refCompressList` spec on
  edge + pseudo-random vectors (`compress_denote_spec`); every binding is a
  pure scalar-arith op — no `extCall`/`stackLoad`/`stackStore`
  (`compress_is_purearith_only`); the last four bindings are the output copies
  (`compress_last_four_bindings_are_copies`).
* External: `bench/plonky3_compare/compress_from_rustcmd_kat.c` byte-checks the
  owned `.s` (`make plonky3-compress-rustcmd-kat`) against the self-contained C
  reference `ref_compress` over fixed + pseudo-random inputs.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3CompressEmit

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

/-- The `reg 64` dialect type, abbreviated. -/
abbrev r64 : JasminTy := .reg 64

/-! ## 0. Slot names and the constant table

Input words: `0..3` = `l0..l3`, `4..7` = `r0..r3`, `8` = `c9e` (`0x9E`),
`9` = `c6d` (`0x6D`), `10` = `cc5` (`0xC5`), `11..14` = `k0..k3` (the per-limb
index constants `0,1,2,3`). -/

/-- Left-digest slot name `l{i}`. -/
def lN (i : Nat) : String := "l" ++ toString i
/-- Right-digest slot name `r{i}`. -/
def rN (i : Nat) : String := "r" ++ toString i
/-- Output slot name `o{i}`. -/
def oN (i : Nat) : String := "o" ++ toString i
/-- Final output-copy slot name `q{i}` (the last-four-bindings convention). -/
def qN (i : Nat) : String := "q" ++ toString i
/-- Per-limb index-constant slot name `k{i}`. -/
def kN (i : Nat) : String := "k" ++ toString i

/-- The 7 constant input words (`0x9E=158, 0x6D=109, 0xC5=197, 0,1,2,3`),
    indexed by `word − 8`. Consumed by the owned renders' `immSlotMap`. -/
def constNat : Nat → Nat
  | 0 => 158 | 1 => 109 | 2 => 197
  | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 3
  | _ => 0

/-! ## 1. The straight-line `LowCT` body -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- Output limb `i`: `o[i] := ((l[i] + r[i]) * 0x9E + i) ^ (l[i] * 0x6D) ^ r[i]`
    (all constants read from their input-word slots). -/
def limbStmt (i : Nat) : LowCT :=
  .RScalarSetExpr (oN i)
    (.SXor
      (.SXor
        (.SAdd (.SMul (.SAdd (.SVar (lN i)) (.SVar (rN i))) (.SVar "c9e"))
          (.SVar (kN i)))
        (.SMul (.SVar (lN i)) (.SVar "c6d")))
      (.SVar (rN i)))

/-- Serial diffusion step `j ∈ {1,2,3}`: `o[j] := o[j] ^ (o[j-1] * 0xC5)`,
    reading the already-diffused `o[j-1]` (SSA rebinding). -/
def diffuseStmt (j : Nat) : LowCT :=
  .RScalarSetExpr (oN j)
    (.SXor (.SVar (oN j)) (.SMul (.SVar (oN (j - 1))) (.SVar "cc5")))

/-- The full compress body: four limb computations, three diffusion steps, then
    the four output copies `q[i] := o[i]` — each an identity `RScalarSetExpr`
    lowering to exactly ONE binding, so the **last four bindings** of the
    emitted `Com` carry `o[0..3]` in order (the `toLprogPhysAbi` last-`nOut`
    output convention). -/
def compressBody : LowCT := seqAll (
  (List.range 4).map limbStmt
  ++ (List.range 3).map (fun j => diffuseStmt (j + 1))
  ++ (List.range 4).map (fun i => .RScalarSetExpr (qN i) (.SVar (oN i))))

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `l0`) is the context head, word `14` (= `k3`) the
deepest entry — so input word `i` sits at De Bruijn index `i`, the layout the
consumers' `abiMaps 15 compressConstAt` expects. -/

/-- The source context: 15 `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate 15 (.sword 64)

/-- The source `VarMap`: word 14 (`k3`) bound first (deepest), word 0 (`l0`)
    last (head). -/
def srcVM : VarMap srcCtx :=
  (((((((((((((((VarMap.empty.bind "k3").bind "k2").bind "k1").bind
    "k0").bind "cc5").bind "c6d").bind "c9e").bind "r3").bind "r2").bind
    "r1").bind "r0").bind "l3").bind "l2").bind "l1").bind "l0")

/-! ## 3. The front-emitted programs -/

/-- Push `compressBody` through the `CProg`-free control front and cap with
    `ret <name>` (a `u64` slot of the final `VarMap`). `none` if the front
    declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM compressBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted compress, lowered to the jasmin dialect (capped at the
    final output copy `q3`, whose binding is the `Com`'s last). -/
def compressLoweredOpt :=
  (frontComAt (qN 3)).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem compressLowered_isSome : compressLoweredOpt.isSome := by native_decide

/-- The input context of the deployed `Com`: 15 `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 15 r64

/-- The deployed compress `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    Rendered to owned `.s` by `Plonky3EmitMain` (and inlined by the
    whole-prover / orchestration emits) under `plonky3_merkle_compress_rc`. -/
def compressComFinal : Com jasminDialect inCtxt r64 :=
  compressLoweredOpt.get compressLowered_isSome

/-! ## 4. `denote = spec` vs the independent reference

`refCompressList` is the direct Lean transcription of the self-contained C
reference `ref_compress` (`compress_from_rustcmd_kat.c`) — independent of the
`LowCT` body shape. -/

/-- The reference compress: the four output limbs (post-diffusion), in order. -/
def refCompressList (l r : Fin 4 → BitVec 64) : List (BitVec 64) :=
  let o : Fin 4 → BitVec 64 := fun i =>
    (((l i + r i) * (158 : BitVec 64) + BitVec.ofNat 64 i.val)
      ^^^ (l i * (109 : BitVec 64))) ^^^ r i
  let o1 := o 1 ^^^ (o 0 * (197 : BitVec 64))
  let o2 := o 2 ^^^ (o1 * (197 : BitVec 64))
  let o3 := o 3 ^^^ (o2 * (197 : BitVec 64))
  [o 0, o1, o2, o3]

/-- Sample digest pairs (8 words `l0..l3, r0..r3`): edges + pseudo-random. -/
def samples : List (List Nat) :=
  [ [0, 0, 0, 0, 0, 0, 0, 0],
    [1, 2, 3, 4, 5, 6, 7, 8],
    [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF,
     0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF],
    [0xDEADBEEF12345678, 0x0F0F0F0F0F0F0F0F, 0x123456789ABCDEF0, 0xCAFEBABE87654321,
     0x1111111122222222, 0x9E3779B97F4A7C15, 0x5555AAAA5555AAAA, 0x8000000000000001],
    [0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0, 0x082EFA98EC4E6C89,
     0x452821E638D01377, 0xBE5466CF34E90C6C, 0xC0AC29B7C97C50DD, 0x3F84D5B5B5470917] ]

/-- Left digest limb `i` of a sample. -/
def lOf (s : List Nat) (i : Fin 4) : BitVec 64 := BitVec.ofNat 64 (s.getD i.val 0)
/-- Right digest limb `i` of a sample. -/
def rOf (s : List Nat) (i : Fin 4) : BitVec 64 := BitVec.ofNat 64 (s.getD (4 + i.val) 0)

/-- The head-first source valuation of a sample: words `0..7` the digests,
    words `8..14` the constants `158,109,197,0,1,2,3`. -/
def valOf (s : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 (s.getD 0 0)) (.cons (BitVec.ofNat 64 (s.getD 1 0))
    (.cons (BitVec.ofNat 64 (s.getD 2 0)) (.cons (BitVec.ofNat 64 (s.getD 3 0))
    (.cons (BitVec.ofNat 64 (s.getD 4 0)) (.cons (BitVec.ofNat 64 (s.getD 5 0))
    (.cons (BitVec.ofNat 64 (s.getD 6 0)) (.cons (BitVec.ofNat 64 (s.getD 7 0))
    (.cons (158 : BitVec 64) (.cons (109 : BitVec 64) (.cons (197 : BitVec 64)
    (.cons (0 : BitVec 64) (.cons (1 : BitVec 64) (.cons (2 : BitVec 64)
    (.cons (3 : BitVec 64) .nil))))))))))))))

/-- All four output-capped front programs exist. -/
theorem frontComAt_q_isSome :
    (List.range 4).all (fun j => (frontComAt (qN j)).isSome) = true := by
  native_decide

/-- Denote the front program capped at slot `name` on a sample (result word). -/
def frontDenoteAt (name : String) (s : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf s))

/-- **denote = independent spec, all four output words.** The front program
    capped at output copy `q[j]` denotes limb `j` of `refCompressList` on every
    sample — the four values the owned render's last-four-bindings epilogue
    stores to `out[0..3]`. -/
theorem compress_denote_spec :
    samples.all (fun s =>
      (List.range 4).all (fun j =>
        frontDenoteAt (qN j) s
          == some ((refCompressList (lOf s) (rOf s)).getD j 0))) = true := by
  native_decide

/-! ## 5. Structural gates on the lowered `Com` -/

/-- Every binding is a pure scalar-arith op (`regArith`/`regConst`/immediate
    shift) — no `extCall`, no `stackLoad`/`stackStore` — so the denotation is
    the exact BitVec word arithmetic. -/
def allPureArith : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body =>
    (match e.op with
     | .regArith _ _ => true
     | .regConst _ _ => true
     | .shlImm _ _ => true
     | .shrImm _ _ => true
     | _ => false) && allPureArith body

theorem compress_is_purearith_only : allPureArith compressComFinal = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0` (the
    front's `RScalarSetExpr` result copy)? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last four bindings** are identity copies — the `q[0..3]` output
    copies the owned render's last-`nOut` epilogue stores to `out[0..3]`. -/
theorem compress_last_four_bindings_are_copies :
    ((copyFlags compressComFinal).drop ((copyFlags compressComFinal).length - 4))
      = [true, true, true, true] := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3CompressEmit
