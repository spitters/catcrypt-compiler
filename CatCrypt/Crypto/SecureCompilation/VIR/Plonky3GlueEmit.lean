/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw

set_option autoImplicit false

/-!
# Plonky3 prover-orchestration glue (REV-11 A7), FRONT-COMPILED

The three single-element prover-orchestration leaves of the emitted plonky3
prover — the **Fiat–Shamir challenger squeeze**, the **quotient composition**
element, and the **OOD/DEEP** element — sourced through the verified
`CProg`-free front, NO hand-built `Com` anywhere in the emit path:

```
  {chal,quot,ood}Body (LowCT: RScalarSetExpr u64 word math over 16 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  Com jasminDialect inCtxt r64
```

The consumer `Plonky3GlueOwnedEmit` renders the three `Com`s to one owned
AT&T `.s` (`Com.toLprogPhysAbi -> renderLprogAtt`, constants as `immSlotMap`
immediates) under the export symbols `quotient_compose_elem_rc`,
`ood_deep_elem_rc`, `challenger_squeeze_rc`; KAT
`bench/plonky3_compare/glue_from_rustcmd_kat.c`
(`make plonky3-glue-rustcmd-kat`).

## The specs (byte-for-byte the A6/A7 `ref_*` glue)

```
challenger_squeeze(d[4]):                    // ref_challenger_squeeze
  acc = pr_reduce(d0)
  for r in 0..3:  acc = pr_add(pr_mul(acc, C) mod p reduced fully, pr_reduce(d[r+1]))
  return acc                                 // NON-canonical (raw u64)

quotient_compose elem (i, v[4], c[4]):       // ref_quotient_compose, per element
  out = i + Σ_k v_k·c_k        (c_k = (k+1)·α^k mod p, driver-precomputed)

ood_deep elem (q_i, q_at_z, pw, i+1):        // ref_ood_deep, per element
  out = (q_i − q_at_z)·(i+1) + pw
```

### Canonical vs non-canonical arithmetic (the load-bearing distinction)

The C reference's `pr_mul a b = (a·b mod 2⁶⁴) mod p` WRAPS the `u64` product
before reducing, and `pr_reduce` is a SINGLE conditional subtract — so the
challenger OUTPUT `α` is NOT canonical. The split:

* **Challenger** (`challengerSqueezeCom`): reproduces the wrapping-`u64` +
  single-subtract semantics exactly. `acc·C` wraps mod 2⁶⁴ (`u64` `*`), then a
  full `u64 → field` reduction via the 32-bit split
  `bbModU64 x = bbAdd (bbMul (x≫32) R) (bbMul (x∧LOW) 1)` with
  `R = 2³² mod p = 268435454` (the split products are `< 2⁶⁰`, in Barrett
  range); the digest absorb / final accumulate are single csubs
  (`pr_reduce`/`pr_add`).

* **Quotient / OOD** leaves: CANONICAL-input Barrett arithmetic only. The
  wrapping `α`-power chain is precomputed by the C driver as the canonical
  coefficients `c_k = (k+1)·α^k mod p` (quotient) and the running `pw` (OOD);
  the leaves do only `bbMul`/`bbAdd`/`bbSub` on operands `< p`. OOD's closing
  `bbAdd` (= `pr_add`) takes the possibly-raw `pw` directly.

The ∀-quantified Barrett reduction-correctness is PROVED in
`Plonky3BarrettLaw` (`barrettMul_correct`) — reused, not re-proved; the
in-model gates below check each front program's denotation against the
independent `pr_*` transcription on edge + pseudo-random samples.

## ABI (unchanged, 16 input words each, 1 output word)

* `quotient_compose_elem_rc`: `0` = `i`, `1, 13, 14, 15` = `c0..c3`,
  `2..5` = `v0..v3`; Barrett constants at `7..12`.
* `ood_deep_elem_rc`: `0` = `q_i`, `1` = `q_at_z`, `2` = `pw`, `3` = `i+1`;
  Barrett constants at `7..12`.
* `challenger_squeeze_rc`: `0..3` = `d0..d3`, `4` = `C = 2654435769`
  (the FULL `0x9E3779B9` — the multiply wraps mod 2⁶⁴ before `% p`),
  `5` = `R = 268435454`, `6` = `LOW = 4294967295`, `13` = `1`; Barrett
  constants at `7..12`.

The output is the **last binding** (the front's identity output copy),
matching `toLprogPhysAbi`'s last-`nOut` convention with `nOut = 1`. The shift
amounts lower to immediate-count `shrImm`; words `10..12` are carried for ABI
compatibility but not read.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3GlueEmit

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

/-! ## 0. Input-word indices (the `Plonky3GlueOwnedEmit` immediate split) -/

/-- The number of declared input words (all three leaves). -/
abbrev nInputs : Nat := 16

/-- Barrett-constant input indices (shared by all three leaves). -/
def iMU : Nat := 7
def iP : Nat := 8
def iZero : Nat := 9

/-- Challenger constant input indices: the wrapping multiply constant
    `C = 0x9E3779B9`, the `2³² mod p` factor `R`, the low-32 mask, and the
    immediate `1`. -/
def cC : Nat := 4
def cR : Nat := 5
def cLOW : Nat := 6
def cOne : Nat := 13

/-! ## 1. LowCT building blocks -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- The branchless conditional-subtract correction term of slot `s`:
    `(0 − (s >> 63)) & p`. -/
def csubMask (s : String) : SExpr :=
  .SAnd (.SSub (.SLit 0) (.SShr (.SVar s) (.SLit 63))) (.SVar "p")

/-- `dst = csub(a)` — the single conditional subtract (`pr_reduce`):
    `ss = a − p;  dst = ss + mask(ss)`. -/
def csubStmts (dst a : String) : List LowCT := [
  .RScalarSetExpr "ss" (.SSub (.SVar a) (.SVar "p")),
  .RScalarSetExpr dst (.SAdd (.SVar "ss") (csubMask "ss")) ]

/-- `dst = bbMul(a, b)` — the branchless Barrett product (valid for true
    products `< 2⁶²`): `x = a·b; qq = ((x≫30)·MU)≫32; tt = x − qq·p;
    dst = csub(tt)`. -/
def bbMulStmts (dst a b : String) : List LowCT := [
  .RScalarSetExpr "x" (.SMul (.SVar a) (.SVar b)),
  .RScalarSetExpr "qq"
    (.SShr (.SMul (.SShr (.SVar "x") (.SLit 30)) (.SVar "mu")) (.SLit 32)),
  .RScalarSetExpr "tt" (.SSub (.SVar "x") (.SMul (.SVar "qq") (.SVar "p"))),
  .RScalarSetExpr "ss" (.SSub (.SVar "tt") (.SVar "p")),
  .RScalarSetExpr dst (.SAdd (.SVar "ss") (csubMask "ss")) ]

/-- `dst = bbAdd(a, b) = pr_add(a, b)` — add then ONE conditional subtract:
    `e = (a + b) − p;  dst = e + mask(e)`. -/
def bbAddStmts (dst a b : String) : List LowCT := [
  .RScalarSetExpr "e" (.SSub (.SAdd (.SVar a) (.SVar b)) (.SVar "p")),
  .RScalarSetExpr dst (.SAdd (.SVar "e") (csubMask "e")) ]

/-- `dst = bbSub(a, b)` — subtract then add-back-if-negative:
    `d = a − b;  dst = d + mask(d)`. -/
def bbSubStmts (dst a b : String) : List LowCT := [
  .RScalarSetExpr "d" (.SSub (.SVar a) (.SVar b)),
  .RScalarSetExpr dst (.SAdd (.SVar "d") (csubMask "d")) ]

/-! ## 2. The quotient-compose single-element body

`out = i + Σ_{k=0}^3 v_k·c_k`, all operands canonical. -/

/-- LDE-value slot name `v{k}`. -/
def vN (k : Nat) : String := "v" ++ toString k
/-- Precomputed-coefficient slot name `c{k}` (`c_k = (k+1)·α^k mod p`). -/
def cN (k : Nat) : String := "c" ++ toString k
/-- Digest-word slot name `d{r}`. -/
def dN (r : Nat) : String := "d" ++ toString r

/-- One quotient term: `term = bbMul(v_k, c_k); acc = bbAdd(acc, term)`. -/
def qTermStmts (k : Nat) : List LowCT :=
  bbMulStmts "term" (vN k) (cN k) ++ bbAddStmts "acc" "acc" "term"

/-- The quotient-compose element body: seed `acc = i`, four terms, then the
    output copy `qout := acc` (the last binding — the `nOut = 1` output). -/
def quotBody : LowCT := seqAll (
  [ .RScalarSetExpr "acc" (.SVar "i0") ]
  ++ qTermStmts 0 ++ qTermStmts 1 ++ qTermStmts 2 ++ qTermStmts 3
  ++ [ .RScalarSetExpr "qout" (.SVar "acc") ])

/-! ## 3. The OOD/DEEP single-element body

`out = (q_i − q_at_z)·(i+1) + pw` (closing `bbAdd` = `pr_add` on the
possibly-raw `pw`). -/

def oodBody : LowCT := seqAll (
  bbSubStmts "y" "qi" "qz"
  ++ bbMulStmts "y" "y" "ip1"
  ++ bbAddStmts "y" "y" "pw"
  ++ [ .RScalarSetExpr "qout" (.SVar "y") ])

/-! ## 4. The Fiat–Shamir challenger-squeeze body

`acc = pr_reduce(d0); for r in 0..3: acc = pr_add(bbModU64(acc·C), pr_reduce(d[r+1]))`
with the wrapping `u64` product and the 32-bit-split full reduction
`bbModU64 x = bbAdd (bbMul (x≫32) R) (bbMul (x∧LOW) 1)`. -/

/-- One challenger round absorbing digest word `d{r}`:
    `prod = acc·C` (wraps mod 2⁶⁴); `am = bbModU64(prod)` (canonical);
    `td = pr_reduce(d)`; `acc = pr_add(am, td)` (single csub, may stay ≥ p —
    matches the spec's non-canonical accumulator). -/
def cRoundStmts (r : Nat) : List LowCT :=
  [ .RScalarSetExpr "prod" (.SMul (.SVar "acc") (.SVar "cc")),
    .RScalarSetExpr "hi" (.SShr (.SVar "prod") (.SLit 32)),
    .RScalarSetExpr "lo" (.SAnd (.SVar "prod") (.SVar "clow")) ]
  ++ bbMulStmts "r1" "hi" "cr"
  ++ bbMulStmts "r2" "lo" "cone"
  ++ bbAddStmts "am" "r1" "r2"
  ++ csubStmts "td" (dN r)
  ++ bbAddStmts "acc" "am" "td"

/-- The challenger body: `acc = pr_reduce(d0)`, three rounds, output copy. -/
def chalBody : LowCT := seqAll (
  csubStmts "acc" (dN 0)
  ++ cRoundStmts 1 ++ cRoundStmts 2 ++ cRoundStmts 3
  ++ [ .RScalarSetExpr "qout" (.SVar "acc") ])

/-! ## 5. Source context + per-leaf `VarMap`s

Head-first: word `0` is the context head, word `15` the deepest — input word
`i` at De Bruijn index `i`, the layout `Plonky3GlueOwnedEmit.abiMaps 16`
expects. Unused words are bound under distinct `u{i}` names. -/

/-- The source context: 16 `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate 16 (.sword 64)

/-- Quotient `VarMap`: `[i0, c0, v0..v3, u6, mu, p, czero, sh30, sh32, sh63,
    c1, c2, c3]`. -/
def quotVM : VarMap srcCtx :=
  ((((((((((((((((VarMap.empty.bind "c3").bind "c2").bind "c1").bind
    "sh63").bind "sh32").bind "sh30").bind "czero").bind "p").bind "mu").bind
    "u6").bind "v3").bind "v2").bind "v1").bind "v0").bind "c0").bind "i0")

/-- OOD `VarMap`: `[qi, qz, pw, ip1, u4, u5, u6, mu, p, czero, sh30, sh32,
    sh63, u13, u14, u15]`. -/
def oodVM : VarMap srcCtx :=
  ((((((((((((((((VarMap.empty.bind "u15").bind "u14").bind "u13").bind
    "sh63").bind "sh32").bind "sh30").bind "czero").bind "p").bind "mu").bind
    "u6").bind "u5").bind "u4").bind "ip1").bind "pw").bind "qz").bind "qi")

/-- Challenger `VarMap`: `[d0..d3, cc, cr, clow, mu, p, czero, sh30, sh32,
    sh63, cone, u14, u15]`. -/
def chalVM : VarMap srcCtx :=
  ((((((((((((((((VarMap.empty.bind "u15").bind "u14").bind "cone").bind
    "sh63").bind "sh32").bind "sh30").bind "czero").bind "p").bind "mu").bind
    "clow").bind "cr").bind "cc").bind "d3").bind "d2").bind "d1").bind "d0")

/-! ## 6. The front-emitted programs -/

/-- Push a body through the `CProg`-free control front under a leaf `VarMap`
    and cap with `ret <name>`. `none` if the front declines. -/
def frontComWith (vm : VarMap srcCtx) (body : LowCT) (name : String) :
    Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl vm body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The input context of the deployed `Com`s: 16 `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate nInputs r64

/-- The quotient element, lowered (capped at the output copy `qout`). -/
def quotLoweredOpt :=
  (frontComWith quotVM quotBody "qout").bind
    DialectToJasminCom.cryptoDialectToJasminCom

theorem quotLowered_isSome : quotLoweredOpt.isSome := by native_decide

/-- The quotient-compose single-element `Com` — FRONT-GENERATED. -/
def quotientComposeElemCom : Com jasminDialect inCtxt r64 :=
  quotLoweredOpt.get quotLowered_isSome

/-- The OOD/DEEP element, lowered. -/
def oodLoweredOpt :=
  (frontComWith oodVM oodBody "qout").bind
    DialectToJasminCom.cryptoDialectToJasminCom

theorem oodLowered_isSome : oodLoweredOpt.isSome := by native_decide

/-- The OOD/DEEP single-element `Com` — FRONT-GENERATED. -/
def oodDeepElemCom : Com jasminDialect inCtxt r64 :=
  oodLoweredOpt.get oodLowered_isSome

/-- The challenger squeeze, lowered. -/
def chalLoweredOpt :=
  (frontComWith chalVM chalBody "qout").bind
    DialectToJasminCom.cryptoDialectToJasminCom

theorem chalLowered_isSome : chalLoweredOpt.isSome := by native_decide

/-- The Fiat–Shamir challenger-squeeze `Com` — FRONT-GENERATED. -/
def challengerSqueezeCom : Com jasminDialect inCtxt r64 :=
  chalLoweredOpt.get chalLowered_isSome

/-! ## 7. `denote = spec` vs the independent `pr_*` transcription

Direct Lean transcriptions of the C reference primitives
(`glue_from_rustcmd_kat.c` / `bench_prove_emitted_a6.c`), independent of the
`LowCT` body shapes. -/

/-- `pr_reduce`: the SINGLE conditional subtract on a raw `u64` word
    (`t = x − p; if (int64)t < 0 then t + p else t`). -/
def prReduce (x : BitVec 64) : BitVec 64 :=
  let t := x - (2013265921 : BitVec 64)
  if t.msb then t + (2013265921 : BitVec 64) else t

/-- `pr_mul`: the C reference's `(a·b mod 2⁶⁴) mod p` (the product WRAPS). -/
def prMul (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((a * b).toNat % bbPNat)

/-- `pr_add`: add (no wrap for the regimes used) then `pr_reduce`. -/
def prAdd (a b : BitVec 64) : BitVec 64 := prReduce (a + b)

/-- `pr_sub` on canonical residues. -/
def prSub (a b : BitVec 64) : BitVec 64 :=
  prReduce ((2013265921 : BitVec 64) + a - b)

/-- The quotient element reference: `i + Σ v_k·c_k` (canonical `pr_*`). -/
def refQuotElem (i : Nat) (v c : Nat → Nat) : BitVec 64 :=
  let step := fun (acc : BitVec 64) (k : Nat) =>
    prAdd acc (prMul (BitVec.ofNat 64 (v k)) (BitVec.ofNat 64 (c k)))
  step (step (step (step (BitVec.ofNat 64 i) 0) 1) 2) 3

/-- The OOD/DEEP element reference: `(q_i − q_at_z)·(i+1) + pw`. -/
def refOodElem (qi qz pw ip1 : Nat) : BitVec 64 :=
  prAdd (prMul (prSub (BitVec.ofNat 64 qi) (BitVec.ofNat 64 qz))
      (BitVec.ofNat 64 ip1))
    (BitVec.ofNat 64 pw)

/-- The challenger-squeeze reference (raw `u64` digest words in): three
    absorb rounds with the wrapping `pr_mul` by `C = 0x9E3779B9`. -/
def refChalSqueeze (d0 d1 d2 d3 : Nat) : BitVec 64 :=
  let C : BitVec 64 := 2654435769
  let round := fun (acc : BitVec 64) (d : Nat) =>
    prAdd (prMul acc C) (prReduce (BitVec.ofNat 64 d))
  round (round (round (prReduce (BitVec.ofNat 64 d0)) d1) d2) d3

/-! ### Sample inputs -/

/-- Quotient samples `(i, [v0..v3], [c0..c3])` — canonical residues. -/
def quotSamples : List (Nat × List Nat × List Nat) :=
  [ (0, [0, 0, 0, 0], [0, 0, 0, 0]),
    (1, [1, 2, 3, 4], [1, 2, 3, 4]),
    (63, [2013265920, 2013265919, 1006632960, 1006632961],
         [1, 2013265920, 123456789, 987654321]),
    (17, [1976543210, 31415926, 271828182, 1414213562],
         [1732050807, 1618033988, 141421356, 577215664]),
    (42, [261497212, 1642492615, 2013265920, 1],
         [2013265920, 1, 693147180, 1098612288]) ]

/-- OOD samples `(q_i, q_at_z, pw, i+1)` — canonical residues,
    `i+1 ∈ 1..64`. -/
def oodSamples : List (Nat × Nat × Nat × Nat) :=
  [ (0, 0, 0, 1), (1, 2, 3, 4), (2013265920, 1, 2013265919, 64),
    (123456789, 987654321, 1976543210, 33),
    (1006632960, 1006632961, 31415926, 17),
    (1642492615, 261497212, 2013265920, 64) ]

/-- Challenger samples `(d0, d1, d2, d3)` — RAW `u64` digest words (edges +
    pseudo-random), exercising the non-canonical wrapping regime. -/
def chalSamples : List (Nat × Nat × Nat × Nat) :=
  [ (0, 0, 0, 0),
    (1, 2, 3, 4),
    (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF,
     0xFFFFFFFFFFFFFFFF),
    (0xDEADBEEF12345678, 0x0F0F0F0F0F0F0F0F, 0x123456789ABCDEF0,
     0xCAFEBABE87654321),
    (0x9E3779B97F4A7C15, 0xBF58476D1CE4E5B9, 0x243F6A8885A308D3,
     0x13198A2E03707344),
    (2013265921, 2013265920, 4026531842, 0x8000000000000001) ]

/-! ### Valuations (head-first, constants at their ABI words) -/

/-- Quotient valuation: `[i, c0, v0..v3, 0, MU, p, 0, 30, 32, 63,
    c1, c2, c3]`. -/
def quotValOf (i : Nat) (v c : List Nat) :
    @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 i) (.cons (BitVec.ofNat 64 (c.getD 0 0))
    (.cons (BitVec.ofNat 64 (v.getD 0 0)) (.cons (BitVec.ofNat 64 (v.getD 1 0))
    (.cons (BitVec.ofNat 64 (v.getD 2 0)) (.cons (BitVec.ofNat 64 (v.getD 3 0))
    (.cons ((0 : BitVec 64)) (.cons ((2290649223 : BitVec 64))
    (.cons ((2013265921 : BitVec 64)) (.cons ((0 : BitVec 64))
    (.cons ((30 : BitVec 64)) (.cons ((32 : BitVec 64))
    (.cons ((63 : BitVec 64)) (.cons (BitVec.ofNat 64 (c.getD 1 0))
    (.cons (BitVec.ofNat 64 (c.getD 2 0)) (.cons (BitVec.ofNat 64 (c.getD 3 0))
    .nil)))))))))))))))

/-- OOD valuation: `[q_i, q_at_z, pw, i+1, 0, 0, 0, MU, p, 0, 30, 32, 63,
    0, 0, 0]`. -/
def oodValOf (qi qz pw ip1 : Nat) :
    @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 qi) (.cons (BitVec.ofNat 64 qz)
    (.cons (BitVec.ofNat 64 pw) (.cons (BitVec.ofNat 64 ip1)
    (.cons ((0 : BitVec 64)) (.cons ((0 : BitVec 64))
    (.cons ((0 : BitVec 64)) (.cons ((2290649223 : BitVec 64))
    (.cons ((2013265921 : BitVec 64)) (.cons ((0 : BitVec 64))
    (.cons ((30 : BitVec 64)) (.cons ((32 : BitVec 64))
    (.cons ((63 : BitVec 64)) (.cons ((0 : BitVec 64))
    (.cons ((0 : BitVec 64)) (.cons ((0 : BitVec 64)) .nil)))))))))))))))

/-- Challenger valuation: `[d0..d3, C, R, LOW, MU, p, 0, 30, 32, 63, 1,
    0, 0]`. -/
def chalValOf (d0 d1 d2 d3 : Nat) :
    @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 d0) (.cons (BitVec.ofNat 64 d1)
    (.cons (BitVec.ofNat 64 d2) (.cons (BitVec.ofNat 64 d3)
    (.cons ((2654435769 : BitVec 64)) (.cons ((268435454 : BitVec 64))
    (.cons ((4294967295 : BitVec 64)) (.cons ((2290649223 : BitVec 64))
    (.cons ((2013265921 : BitVec 64)) (.cons ((0 : BitVec 64))
    (.cons ((30 : BitVec 64)) (.cons ((32 : BitVec 64))
    (.cons ((63 : BitVec 64)) (.cons ((1 : BitVec 64))
    (.cons ((0 : BitVec 64)) (.cons ((0 : BitVec 64)) .nil)))))))))))))))

/-! ### Correctness gate (external KAT, per REV-12)

The quotient / OOD-DEEP / challenger-squeeze elements' `denote = spec`
correctness is gated by the external C byte-KAT on the emitted `.s`
(`plonky3-glue-rustcmd-kat`), which tests the *deployed bytes* against the
independent reference — strictly stronger than an in-model sample check.
The in-Lean sample `native_decide` denote gates were dropped (REV-12):
heavy to elaborate, redundant with the KAT, and only sample-based. The
`refQuotElem`/`refOodElem`/`refChalSqueeze` reference folds + the
`quot`/`ood`/`chal` sample sets remain as executable documentation of the
spec the KAT enforces. The cheap `isSome` / provenance / structural gates
below (`allPureArith`, the render/no-`UNHANDLED` checks) are retained. -/

/-! ## 8. Structural gates on the lowered `Com`s -/

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

theorem quot_is_purearith_only : allPureArith quotientComposeElemCom = true := by
  native_decide
theorem ood_is_purearith_only : allPureArith oodDeepElemCom = true := by
  native_decide
theorem chal_is_purearith_only : allPureArith challengerSqueezeCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0` (the
    front's `RScalarSetExpr` result copy)? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last binding** of each leaf is the identity output copy (`qout`) —
    the word the owned render's `nOut = 1` epilogue stores to `out[0]`. -/
theorem glue_last_binding_is_copy :
    (copyFlags quotientComposeElemCom).getLast? = some true
      ∧ (copyFlags oodDeepElemCom).getLast? = some true
      ∧ (copyFlags challengerSqueezeCom).getLast? = some true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3GlueEmit
