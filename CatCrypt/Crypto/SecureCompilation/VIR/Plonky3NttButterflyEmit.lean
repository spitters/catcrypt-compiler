/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw


@[expose] public section
set_option autoImplicit false

/-!
# Plonky3 BabyBear radix-2 NTT butterfly, FRONT-COMPILED

The radix-2 decimation-in-time NTT butterfly over BabyBear
(`p = 2013265921 = 2³¹ − 2²⁷ + 1`), sourced through the verified
front — NO hand-built `Com` anywhere:

```
  butterflyBody (LowCT: RScalarSetExpr Barrett/csub word math over the input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  butterflyCom : Com jasminDialect inCtxt r64
```

The per-butterfly map is `t = bbMul w b; (bbAdd a t, bbSub a t)` with `bbMul`
realised as the branchless Barrett reduction
```
  x = w * b;  q = ((x >> 30) * MU) >> 32;  t = x − q·p;  wb = csub(t)
  csub(y) = let s = y − p;  s + ((0 − (s >> 63)) & p)
```
(`MU = ⌊2⁶² / p⌋ = 2290649223`) and `bbAdd`/`bbSub` the same conditional-subtract
shape. The ∀-quantified reduction-correctness of this exact sequence is PROVED
in `Plonky3BarrettLaw` (`barrettReduceMU_correct` / `barrettMul_correct`) — it
is reused here, not re-proved; the in-model gates below check the front
program's denotation against the independent `Nat` `% p` spec on sample
residues.

## ABI (unchanged)

9 input words `[a, b, w, MU, p, 0, 30, 32, 63]` (words `0..2` runtime, word `3`
= `MU`, word `4` = `p`; the shift amounts lower to immediate-count shifts
`shrImm`, so words `5..8` are carried for ABI compatibility but not read).
2 output words: the **last two bindings** are the front's identity copies of
`(o0, o1) = (bbAdd a wb, bbSub a wb)` in order (`toLprogPhysAbi`'s last-`nOut`
convention).

## Deployment status

The DEPLOYED butterfly `.s` is the in-Lean x86-backend emit
`BarrettButterflyKernel` (`gen_com/ntt_butterfly_x86_from_lean.s`, proven
`butterfly_out0_spec`/`butterfly_out1_spec`, KAT
`make plonky3-ntt-butterfly-rustcmd-kat` under the `plonky3_ntt_butterfly_rc`
symbol). This module is the jasmin-dialect butterfly `Com`,
front-generated and denote-gated against the independent field spec.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttButterflyEmit

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

/-- The 6 constant input words `[MU, p, 0, 30, 32, 63]`, indexed by `word − 3`
    (the immediate table of the 9-word ABI). -/
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

/-- The full butterfly body:
    Barrett `wb = (w·b) mod p`, then `o1 = bbSub a wb`, `o0 = bbAdd a wb`,
    then the two output copies `q0 := o0`, `q1 := o1` (each lowering to exactly
    ONE binding — the last-two-bindings output convention). -/
def butterflyBody : LowCT := seqAll [
  -- x = w * b
  .RScalarSetExpr "x" (.SMul (.SVar "w") (.SVar "b")),
  -- q = ((x >> 30) * MU) >> 32
  .RScalarSetExpr "q"
    (.SShr (.SMul (.SShr (.SVar "x") (.SLit 30)) (.SVar "mu")) (.SLit 32)),
  -- t = x − q·p   (∈ [0, 2p))
  .RScalarSetExpr "t" (.SSub (.SVar "x") (.SMul (.SVar "q") (.SVar "p"))),
  -- wb = csub(t):  s = t − p;  wb = s + ((0 − (s >> 63)) & p)
  .RScalarSetExpr "s" (.SSub (.SVar "t") (.SVar "p")),
  .RScalarSetExpr "wb" (.SAdd (.SVar "s") (csubMask "s")),
  -- o1 = bbSub a wb:  d = a − wb;  o1 = d + ((0 − (d >> 63)) & p)
  .RScalarSetExpr "d" (.SSub (.SVar "a") (.SVar "wb")),
  .RScalarSetExpr "o1" (.SAdd (.SVar "d") (csubMask "d")),
  -- o0 = bbAdd a wb:  e = (a + wb) − p;  o0 = e + ((0 − (e >> 63)) & p)
  .RScalarSetExpr "e" (.SSub (.SAdd (.SVar "a") (.SVar "wb")) (.SVar "p")),
  .RScalarSetExpr "o0" (.SAdd (.SVar "e") (csubMask "e")),
  -- output copies: last two bindings = (o0, o1)
  .RScalarSetExpr "q0" (.SVar "o0"),
  .RScalarSetExpr "q1" (.SVar "o1") ]

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `a`) is the context head, word `8` (= the `63` shift
word) the deepest — input word `i` at De Bruijn index `i` (the 9-word
`[a,b,w,MU,p,0,30,32,63]` ABI). The shift-amount words `5..8` are bound but
not read (the shifts lower to immediate-count `shrImm`). -/

/-- The source context: 9 `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate 9 (.sword 64)

/-- The source `VarMap`: word 8 bound first (deepest), word 0 (`a`) last. -/
def srcVM : VarMap srcCtx :=
  (((((((((VarMap.empty.bind "sh63").bind "sh32").bind "sh30").bind
    "czero").bind "p").bind "mu").bind "w").bind "b").bind "a")

/-! ## 3. The front-emitted programs -/

/-- Push `butterflyBody` through the control front and cap with
    `ret <name>`. `none` if the front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM butterflyBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted butterfly, lowered to the jasmin dialect (capped at the
    final output copy `q1`, whose binding is the `Com`'s last). -/
def butterflyLoweredOpt :=
  (frontComAt "q1").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem butterflyLowered_isSome : butterflyLoweredOpt.isSome := by native_decide

/-- The input context of the `Com`: 9 `r64` words `[a,b,w,MU,p,0,30,32,63]`. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 9 r64

/-- The jasmin-dialect butterfly `Com` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
def butterflyCom : Com jasminDialect inCtxt r64 :=
  butterflyLoweredOpt.get butterflyLowered_isSome

/-! ## 4. `denote = spec` vs the independent `Nat` `% p` field spec -/

/-- The independent field butterfly on canonical residues (`Nat`, direct `%`):
    `[bbAdd a (w·b mod p), bbSub a (w·b mod p)]`. -/
def refButterflyList (a b w : Nat) : List (BitVec 64) :=
  let wb := (w * b) % bbPNat
  [ BitVec.ofNat 64 ((a + wb) % bbPNat),
    BitVec.ofNat 64 ((a + bbPNat - wb) % bbPNat) ]

/-- Sample canonical residues `(a, b, w)`: edges + pseudo-random. -/
def samples : List (Nat × Nat × Nat) :=
  [ (0, 0, 0), (0, 1, 1), (1, 1, 1),
    (2013265920, 2013265920, 2013265920),
    (2013265920, 1, 2013265919), (1006632960, 1006632961, 2),
    (123456789, 987654321, 1976543210), (31415926, 271828182, 1414213562),
    (1234567890, 1, 2013265920), (2, 1006632961, 1006632960) ]

/-- The head-first source valuation: words `0..2` = `a,b,w`, words `3..8` the
    ABI constants `MU, p, 0, 30, 32, 63`. -/
def valOf (a b w : Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 a) (.cons (BitVec.ofNat 64 b)
    (.cons (BitVec.ofNat 64 w) (.cons ((2290649223 : BitVec 64))
    (.cons ((2013265921 : BitVec 64)) (.cons ((0 : BitVec 64))
    (.cons ((30 : BitVec 64)) (.cons ((32 : BitVec 64))
    (.cons ((63 : BitVec 64)) .nil))))))))

/-- Denote the front program capped at slot `name` (result word). -/
def frontDenoteAt (name : String) (a b w : Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf a b w))

/-- Both output-capped front programs exist. -/
theorem frontComAt_q_isSome :
    (frontComAt "q0").isSome ∧ (frontComAt "q1").isSome := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **The Barrett product slot is the field product.** The front program capped
    at `wb` denotes `(w·b) mod p` on every sample — the numeric instance of the
    ∀-quantified `Plonky3BarrettLaw.barrettMul_correct` (proved there for every
    canonical `w, b < p`; reused, not re-proved). -/
theorem butterfly_wb_denote_spec :
    samples.all (fun (a, b, w) =>
      frontDenoteAt "wb" a b w
        == some (BitVec.ofNat 64 ((w * b) % bbPNat))) = true := by
  native_decide

/-- **denote = independent spec, both output words.** The front program capped
    at output copy `q[j]` denotes word `j` of the independent `Nat` `% p`
    butterfly on every sample. -/
theorem butterfly_denote_spec :
    samples.all (fun (a, b, w) =>
      (List.range 2).all (fun j =>
        frontDenoteAt ("q" ++ toString j) a b w
          == some ((refButterflyList a b w).getD j 0))) = true := by
  native_decide

/-! ## 5. Structural gates on the lowered `Com` -/

/-- Every binding is a pure scalar-arith op (`regArith`/`regConst`/immediate
    shift) — no `extCall`, no `stackLoad`/`stackStore`. -/
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

theorem butterfly_is_purearith_only : allPureArith butterflyCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last two bindings** are identity copies — the `(q0, q1)` output
    copies of `(bbAdd a wb, bbSub a wb)`. -/
theorem butterfly_last_two_bindings_are_copies :
    ((copyFlags butterflyCom).drop ((copyFlags butterflyCom).length - 2))
      = [true, true] := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttButterflyEmit
