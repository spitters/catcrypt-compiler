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
# NTRU Prime sntrup761 `Z/4591` polynomial-multiply tile, FRONT-COMPILED

The `Z/q = Z/4591` coefficient arithmetic of sntrup761's polynomial multiply
(schoolbook width-16 tile + per-coefficient Barrett reduction), sourced through
the verified `CProg`-free front — NO hand-built `Com` anywhere:

```
  mulBody (LowCT: RScalarSetExpr schoolbook + Barrett word math over the 36 slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  sntrupMulCom : Com jasminDialect inCtxt r64
```

The consumer `JasminLprogExportSntrup` renders `sntrupMulCom` to owned AT&T
`.s` via `Com.toLprogPhysAbi` (`bench/sntrup_compare/sntrup_owned_emit.lean` →
`gen/sntrup_mul.s`, symbol `sntrup_mul`, no jasminc).

## Scope (stated plainly)

This is the `Z/4591` coefficient arithmetic (schoolbook product + Barrett
reduction) over a width-`N = 16` slice. The `x^761 − x − 1` ring fold and the
full degree `p = 761` are tiled by the C driver — out of scope for this
straight-line kernel.

## Kernel (matches `ref_mul` in `sntrup_mul_kat.c`)

Inputs `a[0..15]`, `b[0..15]` (coeffs `< q = 4591`), Barrett multiplier
`m = ⌊2²⁹/4591⌋ = 116939` and modulus `q` read from the input buffer. Outputs
the `2N − 1 = 31` coefficients `out[k] = Σ_{i+j=k} a[i]·b[j] mod q`. Each
pre-reduction accumulator is `≤ 16·4590² < 2²⁹`; the reduction per coefficient:
```
  y = x − ((x·m) >> 29)·q                  -- Barrett, y ∈ [0, 2q)
  d = y − q;  z = d + (d >> 63)·q          -- branchless cond-subtract
  e = z − q;  o = e + (e >> 63)·q          -- second block (robustness)
```
The shifts lower to immediate-count `shrImm`; `m`, `q` are register reads from
their input words.

## ABI (unchanged — the byte-identical KAT contract)

`inCtxt` = 36 `r64` words: `0..15` = `a`, `16..31` = `b`, `32` = `m`,
`33` = `q`, `34`/`35` = the shift words (carried for ABI compatibility; the
front lowers the shift amounts as immediates, so they are not read). The 31
output words are the **last 31 bindings** — the front's identity copies of
`o[0..30]` in order (`toLprogPhysAbi`'s last-`nOut` convention, map
`sntrupOutStoreMap`).

## Gates

* In-model: the front translates + lowers (`sntrupLowered_isSome`); the 31
  output-capped front programs denote the independent `Nat` schoolbook-`% q`
  spec on edge + pseudo-random coefficient vectors (`sntrup_denote_spec`);
  every binding is pure scalar arith (`sntrup_is_purearith_only`); the last 31
  bindings are the output copies (`sntrup_last_bindings_are_copies`).
* External: `make -C bench/sntrup_compare sntrup-mul-kat` byte-checks
  `gen/sntrup_mul.s` against the independent C schoolbook reference; the
  whole-KEM drivers (`owned-keygen`/`owned-encaps`/`owned-decaps`/
  `owned-roundtrip`) gate byte-identity vs liboqs (OpenSSH) end-to-end.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sntrup761MulEmit

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

/-- Polynomial width. -/
def width : Nat := 16
/-- Number of output coefficients (`2·width − 1`). -/
def outLen : Nat := 31
/-- The sntrup761 prime `q = 4591`. -/
def qNat : Nat := 4591
/-- The Barrett multiplier `m = ⌊2²⁹/4591⌋`. -/
def mNat : Nat := 116939
/-- The Barrett shift (`⌊·/2²⁹⌋` for `q = 4591`). -/
def barrettShift : Nat := 29

/-! ## 1. The straight-line `LowCT` body -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- `a`-coefficient slot name. -/
def aN (i : Nat) : String := "a" ++ toString i
/-- `b`-coefficient slot name. -/
def bN (i : Nat) : String := "b" ++ toString i

/-- The schoolbook accumulator expression for coefficient `k`:
    `Σ_{i+j=k, i,j < width} a[i]·b[j]` as a left-nested `SAdd` chain. -/
def coeffSum (k : Nat) : SExpr :=
  let terms := (List.range width).filterMap (fun i =>
    if i ≤ k ∧ k - i < width then
      some (SExpr.SMul (.SVar (aN i)) (.SVar (bN (k - i))))
    else none)
  match terms with
  | [] => .SLit 0
  | t :: ts => ts.foldl (fun acc t' => .SAdd acc t') t

/-- The statements for coefficient `k` (parametric in the Barrett `shift`):
    accumulate, Barrett step, two branchless conditional subtracts. -/
def coeffStmts (shift k : Nat) : List LowCT :=
  let x := "x" ++ toString k
  let y := "y" ++ toString k
  let d := "d" ++ toString k
  let z := "z" ++ toString k
  let e := "e" ++ toString k
  let o := "o" ++ toString k
  [ .RScalarSetExpr x (coeffSum k),
    .RScalarSetExpr y
      (.SSub (.SVar x)
        (.SMul (.SShr (.SMul (.SVar x) (.SVar "m")) (.SLit shift)) (.SVar "q"))),
    .RScalarSetExpr d (.SSub (.SVar y) (.SVar "q")),
    .RScalarSetExpr z
      (.SAdd (.SVar d) (.SMul (.SShr (.SVar d) (.SLit 63)) (.SVar "q"))),
    .RScalarSetExpr e (.SSub (.SVar z) (.SVar "q")),
    .RScalarSetExpr o
      (.SAdd (.SVar e) (.SMul (.SShr (.SVar e) (.SLit 63)) (.SVar "q"))) ]

/-- The full tile body (parametric in the Barrett `shift`): all 31 coefficient
    blocks, then the 31 output copies `f[k] := o[k]` — each lowering to exactly
    ONE binding, so the **last 31 bindings** carry `o[0..30]` in order. -/
def mulBody (shift : Nat) : LowCT := seqAll (
  ((List.range outLen).flatMap (coeffStmts shift))
  ++ (List.range outLen).map (fun k =>
      .RScalarSetExpr ("f" ++ toString k) (.SVar ("o" ++ toString k))))

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `a[0]`) is the context head, word `35` the deepest —
input word `i` at De Bruijn index `i`, the 36-word layout
`JasminLprogExportSntrup` maps (`a | b | m | q | shiftA | 63`). -/

/-- The input words, in word order (`0..35`). -/
def wordNames : List String :=
  (List.range width).map aN ++ (List.range width).map bN
    ++ ["m", "q", "shA", "sh63"]

/-- Bind a name list onto a `replicate`-`sword 64` context, first name = head. -/
def bindAll : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindAll ns).bind n

/-- The source context: 36 `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate 36 (.sword 64)

/-- The source `VarMap` (word 0 = `a[0]` at the head). -/
def srcVM : VarMap srcCtx := bindAll wordNames

/-! ## 3. The front-emitted programs -/

/-- Push `mulBody` through the `CProg`-free control front and cap with
    `ret <name>`. `none` if the front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM (mulBody barrettShift) with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted tile, lowered to the jasmin dialect (capped at the final
    output copy `f30`, whose binding is the `Com`'s last). -/
def sntrupLoweredOpt :=
  (frontComAt ("f" ++ toString (outLen - 1))).bind
    DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem sntrupLowered_isSome : sntrupLoweredOpt.isSome := by native_decide

/-- The input context: 36 `r64` words (16 `a` + 16 `b` + `m` + `q` + two shift
    words). -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 36 r64

/-- The deployed `Z/4591` tile `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    Rendered to owned `.s` by `bench/sntrup_compare/sntrup_owned_emit.lean`
    (maps in `JasminLprogExportSntrup`) under the `sntrup_mul` symbol. -/
def sntrupMulCom : Com jasminDialect inCtxt r64 :=
  sntrupLoweredOpt.get sntrupLowered_isSome

/-! ## 4. `denote = spec` vs the independent schoolbook-`% q` reference

`refCoeff` is the direct `Nat` transcription of `ref_mul` in
`sntrup_mul_kat.c` — independent of the emitted Barrett shape. -/

/-- The independent reference coefficient: `(Σ_{i+j=k} a[i]·b[j]) mod q`. -/
def refCoeff (a b : List Nat) (k : Nat) : Nat :=
  ((List.range width).foldl (fun acc i =>
    if i ≤ k ∧ k - i < width then acc + a.getD i 0 * b.getD (k - i) 0 else acc)
    0) % qNat

/-- Sample coefficient-vector pairs (each 16 coeffs `< q`): edges +
    pseudo-random. -/
def samples : List (List Nat × List Nat) :=
  [ ((List.range 16).map (fun _ => 0), (List.range 16).map (fun _ => 0)),
    ((List.range 16).map (fun _ => 4590), (List.range 16).map (fun _ => 4590)),
    ((List.range 16).map (fun i => (i * 1234 + 567) % 4591),
     (List.range 16).map (fun i => (i * 4321 + 89) % 4591)),
    ((List.range 16).map (fun i => (i * i * 991 + 17) % 4591),
     (List.range 16).map (fun i => (4590 - i * 273 % 4591) % 4591)) ]

/-- Build a head-first valuation from a value list. -/
def valOfList : (vs : List (BitVec 64)) →
    @Ctxt.Valuation catCryptDialect _ (List.replicate vs.length (.sword 64))
  | [] => .nil
  | v :: vs => .cons v (valOfList vs)

/-- The head-first source valuation of a sample: `a`, `b`, then
    `m, q, 29, 63`. -/
def valOf (a b : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  valOfList
    ((List.range 16).map (fun i => BitVec.ofNat 64 (a.getD i 0))
      ++ (List.range 16).map (fun i => BitVec.ofNat 64 (b.getD i 0))
      ++ ([mNat, qNat, barrettShift, 63].map (BitVec.ofNat 64)))

/-- Denote the front program capped at slot `name` on a sample (result word). -/
def frontDenoteAt (name : String) (a b : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf a b))

/-- **denote = independent spec, all 31 output coefficients.** The front
    program capped at output copy `f[k]` denotes the independent schoolbook
    `% q` reference on every sample — the 31 values the owned render's
    last-31-bindings epilogue stores to `out[0..30]`. -/
theorem sntrup_denote_spec :
    samples.all (fun (a, b) =>
      (List.range outLen).all (fun k =>
        frontDenoteAt ("f" ++ toString k) a b
          == some (BitVec.ofNat 64 (refCoeff a b k)))) = true := by
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

theorem sntrup_is_purearith_only : allPureArith sntrupMulCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last 31 bindings** are identity copies — the `f[0..30]` output
    copies the owned render's last-`nOut` epilogue stores to `out[0..30]`. -/
theorem sntrup_last_bindings_are_copies :
    ((copyFlags sntrupMulCom).drop ((copyFlags sntrupMulCom).length - outLen))
      = List.replicate outLen true := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Sntrup761MulEmit
