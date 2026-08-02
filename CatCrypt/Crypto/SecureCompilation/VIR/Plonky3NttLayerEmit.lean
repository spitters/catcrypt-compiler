/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw

set_option autoImplicit false

/-!
# Plonky3 BabyBear NTT layer (n = 8, last layer), FRONT-COMPILED (`plonky3_ntt_layer8_rc`)

One full radix-2 Cooley–Tukey NTT layer over BabyBear
(`p = 2013265921 = 2³¹ − 2²⁷ + 1`), sourced through the verified `CProg`-free
front — NO hand-built `Com` anywhere in the emit path:

```
  layerBody (LowCT: 4 × the Barrett/csub butterfly over the 18 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  layerCom : Com jasminDialect inCtxt r64
```

## Which layer

The **last layer of an `n = 8` NTT** (`Plonky3ProveEmit.nttLayer vals omega 8
2`): block size `size = 8`, `half = 4`, a single block, twiddle base
`wSize = omega^(8/8) = omega`. For `idx ∈ 0..7`:
```
  i < 4 :  out[i]   = bbAdd vals[i] (bbMul wSize^i vals[i+4])
  i ≥ 4 :  out[i]   = bbSub vals[i-4] (bbMul wSize^(i-4) vals[i])
```
i.e. four independent butterflies on pairs `(i, i+4)` for `i = 0..3`, each the
SAME Barrett/csub word math as the front-compiled single butterfly
(`Plonky3NttButterflyEmit.butterflyBody`), with twiddles `wSize^0..wSize^3`
supplied as **precomputed inputs** (the KAT supplies the spec-computed twiddle
values, so the emitted layer is checked against the exact `nttLayer` output).
The ∀-quantified reduction-correctness of the Barrett sequence is PROVED in
`Plonky3BarrettLaw` (`barrettMul_correct`) — reused, not re-proved; the
in-model gates below check the front program's denotation against the
independent `Nat` `% p` layer spec on sample residues.

## ABI (unchanged)

18 input words `[v0..v7, t0..t3, MU, p, 0, 30, 32, 63]`: values `0..7` and
twiddles `8..11` runtime, the six constants `12..17` immediates in the owned
render (via `constNat`; the shift amounts lower to immediate-count `shrImm`,
so words `14..17` are carried for ABI compatibility but not read). 8 output
words: the **last eight bindings** of the `Com` are the front's identity
copies of the transformed `v0..v7` in order, matching `toLprogPhysAbi`'s
last-`nOut` output convention.

Consumers (`Plonky3EmitMain` / `Plonky3WholeProverEmit` /
`Plonky3OrchLoopsEmit`) render `layerCom` to owned AT&T `.s` via
`Com.toLprogPhysAbi` under the export symbol `plonky3_ntt_layer8_rc`; the
external KAT is `bench/plonky3_compare/ntt_layer_from_rustcmd_kat.c`
(`make plonky3-ntt-layer-rustcmd-kat`) against the self-contained C
transcription of `nttLayer(8,2)`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit

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

/-- The BabyBear prime `p = 2013265921`. -/
def bbPNat : Nat := 2013265921

/-! ## 0. Slot names and the constant table

Input words: `0..7` = the values `v0..v7`, `8..11` = the twiddles `tw0..tw3`,
`12` = `mu` (the Barrett `MU`), `13` = `p`, `14..17` = the shift-amount words
`0, 30, 32, 63` (bound for ABI compatibility, not read — shifts lower to
immediate-count `shrImm`). -/

/-- Value slot name `v{i}`. -/
def vN (i : Nat) : String := "v" ++ toString i
/-- Twiddle slot name `tw{j}`. -/
def twN (j : Nat) : String := "tw" ++ toString j
/-- Final output-copy slot name `q{i}` (the last-eight-bindings convention). -/
def qN (i : Nat) : String := "q" ++ toString i

/-- Constant `j`'s literal `Nat` value (`MU, p, 0, 30, 32, 63`, indexed by
    `word − 12`). Consumed by the owned renders' `immSlotMap`. -/
def constNat : Nat → Nat
  | 0 => 2290649223 | 1 => 2013265921 | 2 => 0
  | 3 => 30 | 4 => 32 | 5 => 63
  | _ => 0

/-! ## 1. The straight-line `LowCT` body -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- The branchless conditional-subtract correction term of slot `s`:
    `(0 − (s >> 63)) & p` — all-ones-masked `p` iff the wrapping `s` is
    "negative" (top bit set). `p` is read from its input-word slot. -/
def csubMask (s : String) : SExpr :=
  .SAnd (.SSub (.SLit 0) (.SShr (.SVar s) (.SLit 63))) (.SVar "p")

/-- One radix-2 butterfly on the value pair `(v[lo], v[hi])` with twiddle slot
    `tw` — the SAME Barrett/csub word math as
    `Plonky3NttButterflyEmit.butterflyBody`, rebinding `v[hi] := bbSub v[lo] wb`
    then `v[lo] := bbAdd v[lo] wb` in place (`v[lo]` is read by both outputs
    before its own rebinding). -/
def butterflyStmts (lo hi : Nat) (tw : String) : List LowCT := [
  -- x = tw * v[hi]
  .RScalarSetExpr "x" (.SMul (.SVar tw) (.SVar (vN hi))),
  -- q = ((x >> 30) * MU) >> 32
  .RScalarSetExpr "q"
    (.SShr (.SMul (.SShr (.SVar "x") (.SLit 30)) (.SVar "mu")) (.SLit 32)),
  -- t = x − q·p   (∈ [0, 2p))
  .RScalarSetExpr "t" (.SSub (.SVar "x") (.SMul (.SVar "q") (.SVar "p"))),
  -- wb = csub(t):  s = t − p;  wb = s + ((0 − (s >> 63)) & p)
  .RScalarSetExpr "s" (.SSub (.SVar "t") (.SVar "p")),
  .RScalarSetExpr "wb" (.SAdd (.SVar "s") (csubMask "s")),
  -- v[hi] = bbSub v[lo] wb:  d = v[lo] − wb;  v[hi] = d + mask(d)
  .RScalarSetExpr "d" (.SSub (.SVar (vN lo)) (.SVar "wb")),
  .RScalarSetExpr (vN hi) (.SAdd (.SVar "d") (csubMask "d")),
  -- v[lo] = bbAdd v[lo] wb:  e = (v[lo] + wb) − p;  v[lo] = e + mask(e)
  .RScalarSetExpr "e" (.SSub (.SAdd (.SVar (vN lo)) (.SVar "wb")) (.SVar "p")),
  .RScalarSetExpr (vN lo) (.SAdd (.SVar "e") (csubMask "e")) ]

/-- The four-butterfly layer statements: pairs `(i, i+4)` with twiddle `tw{i}`,
    `i = 0..3`, rebinding `v0..v7` in place. (Exported so the fused two-layer
    emit `Plonky3NttLayerInlineEmit` can sequence them twice.) -/
def layerStmts : List LowCT :=
  butterflyStmts 0 4 (twN 0) ++ butterflyStmts 1 5 (twN 1) ++
  butterflyStmts 2 6 (twN 2) ++ butterflyStmts 3 7 (twN 3)

/-- The eight trailing output copies `q{i} := v{i}` — each lowering to exactly
    ONE binding, so the **last eight bindings** of the emitted `Com` carry the
    transformed `v0..v7` in order (the `toLprogPhysAbi` last-`nOut`
    convention). -/
def outCopies : List LowCT :=
  (List.range 8).map (fun i => .RScalarSetExpr (qN i) (.SVar (vN i)))

/-- The full NTT-layer body: four butterflies, then the eight output copies. -/
def layerBody : LowCT := seqAll (layerStmts ++ outCopies)

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `v0`) is the context head, word `17` (= the `63` shift
word) the deepest — input word `i` at De Bruijn index `i`, the layout the
consumers' `abiMaps 18 nttLayerConstAt` expects. -/

/-- The source context: 18 `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate 18 (.sword 64)

/-- The source `VarMap`: word 17 bound first (deepest), word 0 (`v0`) last. -/
def srcVM : VarMap srcCtx :=
  ((((((((((((((((((VarMap.empty.bind "sh63").bind "sh32").bind "sh30").bind
    "czero").bind "p").bind "mu").bind "tw3").bind "tw2").bind "tw1").bind
    "tw0").bind "v7").bind "v6").bind "v5").bind "v4").bind "v3").bind
    "v2").bind "v1").bind "v0")

/-! ## 3. The front-emitted programs -/

/-- Push a `LowCT` body through the `CProg`-free control front and cap with
    `ret <name>` (a `u64` slot of the final `VarMap`). `none` if the front
    declines. (Also used by `Plonky3NttLayerInlineEmit` on the fused body.) -/
def frontComOf (body : LowCT) (name : String) :
    Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The layer front program capped at slot `name`. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  frontComOf layerBody name

/-- The front-emitted layer, lowered to the jasmin dialect (capped at the final
    output copy `q7`, whose binding is the `Com`'s last). -/
def layerLoweredOpt :=
  (frontComAt (qN 7)).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem layerLowered_isSome : layerLoweredOpt.isSome := by native_decide

/-- The input context of the deployed `Com`: 18 `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 18 r64

/-- The deployed NTT-layer `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    Rendered to owned `.s` by `Plonky3EmitMain` (and inlined by the
    whole-prover / orchestration emits) under `plonky3_ntt_layer8_rc`. -/
def layerCom : Com jasminDialect inCtxt r64 :=
  layerLoweredOpt.get layerLowered_isSome

/-! ## 4. `denote = spec` vs the independent reference

`refNttLayerList` is the direct Lean transcription of the self-contained C
reference `ntt_layer` (`ntt_layer_from_rustcmd_kat.c`, the exact
`Plonky3ProveEmit.nttLayer vals omega 8 2` with the twiddle powers supplied) —
independent of the `LowCT` body shape. -/

/-- The reference layer on canonical residues (`Nat`, direct `%`): sample `s`
    is the 12 words `[v0..v7, tw0..tw3]`; output `j < 4` is
    `bbAdd v[j] (tw[j]·v[j+4] mod p)`, output `j ≥ 4` is
    `bbSub v[j−4] (tw[j−4]·v[j] mod p)`. -/
def refNttLayerList (s : List Nat) : List (BitVec 64) :=
  let v : Nat → Nat := fun i => s.getD i 0
  let tw : Nat → Nat := fun j => s.getD (8 + j) 0
  let wb : Nat → Nat := fun j => (tw j * v (j + 4)) % bbPNat
  (List.range 4).map (fun j => BitVec.ofNat 64 ((v j + wb j) % bbPNat))
    ++ (List.range 4).map (fun j =>
        BitVec.ofNat 64 ((v j + bbPNat - wb j) % bbPNat))

/-- Sample layer inputs (12 words `v0..v7, tw0..tw3`, canonical residues):
    edges + pseudo-random, twiddle word 0 = 1 (= `wSize^0`) on the structured
    rows as in the deployed twiddle tables. -/
def samples : List (List Nat) :=
  [ [0, 0, 0, 0, 0, 0, 0, 0,  1, 1, 1, 1],
    [1, 2, 3, 4, 5, 6, 7, 8,  1, 2, 3, 4],
    [2013265920, 2013265919, 2013265918, 2013265917, 1, 2, 3, 4,
     1, 2013265920, 1006632960, 1006632961],
    [123456789, 987654321, 1976543210, 31415926, 271828182, 1414213562,
     1234567890, 1006632960,  1, 1732050807, 1618033988, 141421356],
    [2013265920, 1, 2013265920, 2, 2013265919, 3, 2013265918, 4,
     577215664, 261497212, 1642492615, 2013265920] ]

/-- The head-first source valuation of a sample: words `0..11` the values +
    twiddles, words `12..17` the constants `MU, p, 0, 30, 32, 63`. -/
def valOf (s : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 (s.getD 0 0)) (.cons (BitVec.ofNat 64 (s.getD 1 0))
    (.cons (BitVec.ofNat 64 (s.getD 2 0)) (.cons (BitVec.ofNat 64 (s.getD 3 0))
    (.cons (BitVec.ofNat 64 (s.getD 4 0)) (.cons (BitVec.ofNat 64 (s.getD 5 0))
    (.cons (BitVec.ofNat 64 (s.getD 6 0)) (.cons (BitVec.ofNat 64 (s.getD 7 0))
    (.cons (BitVec.ofNat 64 (s.getD 8 0)) (.cons (BitVec.ofNat 64 (s.getD 9 0))
    (.cons (BitVec.ofNat 64 (s.getD 10 0)) (.cons (BitVec.ofNat 64 (s.getD 11 0))
    (.cons ((2290649223 : BitVec 64)) (.cons ((2013265921 : BitVec 64))
    (.cons ((0 : BitVec 64)) (.cons ((30 : BitVec 64))
    (.cons ((32 : BitVec 64)) (.cons ((63 : BitVec 64)) .nil)))))))))))))))))

/-- All eight output-capped front programs exist. -/
theorem frontComAt_q_isSome :
    (List.range 8).all (fun j => (frontComAt (qN j)).isSome) = true := by
  native_decide

/-- Denote the front program capped at slot `name` on a sample (result word). -/
def frontDenoteAt (name : String) (s : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf s))

/-- **denote = independent spec, all eight output words.** The front program
    capped at output copy `q[j]` denotes word `j` of `refNttLayerList` on every
    sample — the eight values the owned render's last-eight-bindings epilogue
    stores to `out[0..7]`. -/
theorem layer_denote_spec :
    samples.all (fun s =>
      (List.range 8).all (fun j =>
        frontDenoteAt (qN j) s
          == some ((refNttLayerList s).getD j 0))) = true := by
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

theorem layer_is_purearith_only : allPureArith layerCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0` (the
    front's `RScalarSetExpr` result copy)? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last eight bindings** are identity copies — the `q[0..7]` output
    copies the owned render's last-`nOut` epilogue stores to `out[0..7]`. -/
theorem layer_last_eight_bindings_are_copies :
    ((copyFlags layerCom).drop ((copyFlags layerCom).length - 8))
      = List.replicate 8 true := by native_decide

/-- Binding count of a `Com`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
