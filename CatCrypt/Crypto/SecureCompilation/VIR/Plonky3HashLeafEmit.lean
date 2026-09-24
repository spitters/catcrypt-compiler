/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom


@[expose] public section
set_option autoImplicit false

/-!
# Plonky3 Merkle leaf-hash, FRONT-COMPILED (`plonky3_merkle_hash_leaf_rc`)

The Plonky3 Merkle leaf-hash (one Baby-Bear field word → 4-word digest),
sourced through the verified front — NO hand-built `Com` anywhere
in the emit path:

```
  hashBody (LowCT: RScalarSetExpr u64 word math over the 8 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  hashLeafCom : Com jasminDialect inCtxt r64
```

Consumers (`Plonky3EmitMain` / `Plonky3WholeProverEmit` /
`Plonky3OrchLoopsEmit` / `ZkSumCheckWholeProverEmit`) render
`hashLeafCom` to owned AT&T `.s` via `Com.toLprogPhysAbi` (constants as
`immSlotMap` immediates via `constNat`, the field word loaded from the `RSI`
input pointer, outputs stored via `stdOutStore 4`) under the export symbol
`plonky3_merkle_hash_leaf_rc`.

## Spec (matches `ref_hleaf` in `hash_leaf_from_rustcmd_kat.c`)

Chained lane mix with the golden-ratio / splittable-random multipliers
`G1 = 0x9E3779B97F4A7C15`, `G2 = 0xBF58476D1CE4E5B9` (wrapping u64):
```
  v ← inp[0]
  for i = 0..3:  o[i] = (v * G1 + i) * G2;  v = o[i]
```
then a serial `0xA3` diffusion pass:
```
  prev = o[0]
  for j = 1..3:  prev = prev * 0xA3;  o[j] = o[j] + prev;  prev = o[j]
```

## ABI (unchanged)

8 input words: `inp[0]` = the field word `v`, `inp[1..7]` = the constants
`G1, G2, 0xA3, 0, 1, 2, 3` (context words the owned render materializes as
immediates via `constNat`). 4 output words: the **last four bindings** of the
`Com` are the front's identity copies of `o[0..3]` in order, matching
`toLprogPhysAbi`'s last-`nOut` output convention.

## Gates

* In-model: the front translates + lowers (`hashLowered_isSome`); the four
  output-capped front programs denote the independent `refHashLeafList` spec on
  edge + pseudo-random vectors (`hash_denote_spec`); every binding is a pure
  scalar-arith op (`hash_is_purearith_only`); the last four bindings are the
  output copies (`hash_last_four_bindings_are_copies`).
* External: `bench/plonky3_compare/hash_leaf_from_rustcmd_kat.c` byte-checks
  the owned `.s` (`make plonky3-hash-leaf-rustcmd-kat`) against the
  self-contained C reference `ref_hleaf` over fixed + pseudo-random inputs.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HashLeafEmit

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

Input words: `0` = the field word `v`, `1` = `g1`, `2` = `g2`, `3` = `a3`
(`0xA3`), `4..7` = `k0..k3` (the per-lane index constants `0,1,2,3`). -/

/-- Output slot name `o{i}`. -/
def oN (i : Nat) : String := "o" ++ toString i
/-- Final output-copy slot name `q{i}` (the last-four-bindings convention). -/
def qN (i : Nat) : String := "q" ++ toString i
/-- Per-lane index-constant slot name `k{i}`. -/
def kN (i : Nat) : String := "k" ++ toString i

/-- The 7 constant input words (`G1 = 0x9E3779B97F4A7C15`,
    `G2 = 0xBF58476D1CE4E5B9`, `0xA3 = 163`, then `0,1,2,3`), indexed by
    `word − 1`. Consumed by the owned renders' `immSlotMap`. -/
def constNat : Nat → Nat
  | 0 => 0x9E3779B97F4A7C15 | 1 => 0xBF58476D1CE4E5B9 | 2 => 0xA3
  | 3 => 0 | 4 => 1 | 5 => 2 | 6 => 3
  | _ => 0

/-! ## 1. The straight-line `LowCT` body -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- Lane `i`: `o[i] := (src * G1 + i) * G2`, where `src` is the chaining input
    slot (`"v"` for lane 0, `o[i-1]` for lanes `1..3`). -/
def laneStmt (i : Nat) (src : String) : LowCT :=
  .RScalarSetExpr (oN i)
    (.SMul (.SAdd (.SMul (.SVar src) (.SVar "g1")) (.SVar (kN i))) (.SVar "g2"))

/-- Serial diffusion step `j ∈ {1,2,3}`: `o[j] := o[j] + (o[j-1] * 0xA3)`,
    reading the already-diffused `o[j-1]` (SSA rebinding). Matches the C
    reference's `prev` chain: after each step `prev = o[j]`, so the next step's
    `prev * 0xA3` is `o[j-1]' * 0xA3`. -/
def diffuseStmt (j : Nat) : LowCT :=
  .RScalarSetExpr (oN j)
    (.SAdd (.SVar (oN j)) (.SMul (.SVar (oN (j - 1))) (.SVar "a3")))

/-- The full leaf-hash body: four chained lanes, three diffusion steps, then
    the four output copies `q[i] := o[i]` — each lowering to exactly ONE
    binding, so the **last four bindings** of the emitted `Com` carry
    `o[0..3]` in order (the `toLprogPhysAbi` last-`nOut` output convention). -/
def hashBody : LowCT := seqAll (
  [ laneStmt 0 "v", laneStmt 1 (oN 0), laneStmt 2 (oN 1), laneStmt 3 (oN 2) ]
  ++ (List.range 3).map (fun j => diffuseStmt (j + 1))
  ++ (List.range 4).map (fun i => .RScalarSetExpr (qN i) (.SVar (oN i))))

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `v`) is the context head, word `7` (= `k3`) the
deepest entry — input word `i` at De Bruijn index `i`, the layout the
consumers' `abiMaps 8 hashLeafConstAt` expects. -/

/-- The source context: 8 `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate 8 (.sword 64)

/-- The source `VarMap`: word 7 (`k3`) bound first (deepest), word 0 (`v`)
    last (head). -/
def srcVM : VarMap srcCtx :=
  ((((((((VarMap.empty.bind "k3").bind "k2").bind "k1").bind "k0").bind
    "a3").bind "g2").bind "g1").bind "v")

/-! ## 3. The front-emitted programs -/

/-- Push `hashBody` through the control front and cap with
    `ret <name>`. `none` if the front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM hashBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted leaf-hash, lowered to the jasmin dialect (capped at the
    final output copy `q3`, whose binding is the `Com`'s last). -/
def hashLoweredOpt :=
  (frontComAt (qN 3)).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem hashLowered_isSome : hashLoweredOpt.isSome := by native_decide

/-- The input context of the deployed `Com`: 8 `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 8 r64

/-- The deployed leaf-hash `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    Rendered to owned `.s` by `Plonky3EmitMain` (and inlined by the
    whole-prover / orchestration emits) under `plonky3_merkle_hash_leaf_rc`. -/
def hashLeafCom : Com jasminDialect inCtxt r64 :=
  hashLoweredOpt.get hashLowered_isSome

/-! ## 4. `denote = spec` vs the independent reference

`refHashLeafList` is the direct Lean transcription of the self-contained C
reference `ref_hleaf` (`hash_leaf_from_rustcmd_kat.c`) — independent of the
`LowCT` body shape. -/

/-- The reference leaf-hash: the four digest words (post-diffusion), in order. -/
def refHashLeafList (v : BitVec 64) : List (BitVec 64) :=
  let g1 : BitVec 64 := 0x9E3779B97F4A7C15#64
  let g2 : BitVec 64 := 0xBF58476D1CE4E5B9#64
  let o0 := (v * g1 + 0) * g2
  let o1 := (o0 * g1 + 1) * g2
  let o2 := (o1 * g1 + 2) * g2
  let o3 := (o2 * g1 + 3) * g2
  let d1 := o1 + o0 * (163 : BitVec 64)
  let d2 := o2 + d1 * (163 : BitVec 64)
  let d3 := o3 + d2 * (163 : BitVec 64)
  [o0, d1, d2, d3]

/-- Sample field words: edges + pseudo-random. -/
def samples : List Nat :=
  [ 0, 1, 2, 2013265920, 0xFFFFFFFFFFFFFFFF, 0xDEADBEEF12345678,
    0x9E3779B97F4A7C15, 0x0123456789ABCDEF, 0x8000000000000000 ]

/-- The head-first source valuation of a sample: word `0` the field word,
    words `1..7` the constants `G1, G2, 163, 0, 1, 2, 3`. -/
def valOf (v : Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 v) (.cons (0x9E3779B97F4A7C15#64)
    (.cons (0xBF58476D1CE4E5B9#64) (.cons ((163 : BitVec 64))
    (.cons ((0 : BitVec 64)) (.cons ((1 : BitVec 64))
    (.cons ((2 : BitVec 64)) (.cons ((3 : BitVec 64)) .nil)))))))

/-- All four output-capped front programs exist. -/
theorem frontComAt_q_isSome :
    (List.range 4).all (fun j => (frontComAt (qN j)).isSome) = true := by
  native_decide

/-- Denote the front program capped at slot `name` on a sample (result word). -/
def frontDenoteAt (name : String) (v : Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf v))

/-- **denote = independent spec, all four output words.** The front program
    capped at output copy `q[j]` denotes word `j` of `refHashLeafList` on every
    sample — the four values the owned render's last-four-bindings epilogue
    stores to `out[0..3]`. -/
theorem hash_denote_spec :
    samples.all (fun v =>
      (List.range 4).all (fun j =>
        frontDenoteAt (qN j) v
          == some ((refHashLeafList (BitVec.ofNat 64 v)).getD j 0))) = true := by
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

theorem hash_is_purearith_only : allPureArith hashLeafCom = true := by
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
theorem hash_last_four_bindings_are_copies :
    ((copyFlags hashLeafCom).drop ((copyFlags hashLeafCom).length - 4))
      = [true, true, true, true] := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HashLeafEmit
