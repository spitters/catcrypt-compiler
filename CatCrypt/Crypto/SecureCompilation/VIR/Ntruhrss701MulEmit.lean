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
# NTRU (ntruhrss701) cyclic ring-multiply tile, FRONT-COMPILED

The `Z/8192[x]/(x^N − 1)` cyclic polynomial product of ntruhrss701 (schoolbook
width-`N = 16` tile + the single `& 8191` field mask), sourced through the
verified `CProg`-free front — NO hand-built `Com` anywhere:

```
  mulBody (LowCT: RScalarSetExpr schoolbook + mask word math over the coeff slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  ntruMulCom : Com jasminDialect inCtxt r64
```

The consumer `JasminLprogExportNtru` provides the ABI maps;
`bench/ntru_compare/ntru_mul_owned_emit.lean` renders `ntruMulCom` to owned
AT&T `.s` via `Com.toLprogPhysAbi` (`gen/ntru_mul.s`, symbol `ntru_mul`, no
jasminc).

## Scope (stated plainly)

ntruhrss701 works in `Z/q[x]/(x^n − 1)` with `q = 8192 = 2^13`, `n = 701`. This
is the complete ring multiply at degree `N = 16` (the same code at the true
`n = 701`, just larger `N` — tiled by the C drivers in `bench/ntru_compare/`,
out of scope for this straight-line kernel).

## Kernel (matches `ref_ntru_mul` in `ntru_mul_kat.c`)

Inputs `a[0..15]`, `b[0..15]` (coeffs `< q = 8192`). The cyclic fold
`x^N ≡ 1` makes the index map `(i + j) mod N = k` the reduction by `x^N − 1`:

  `out[k] = Σ_i a[i] · b[(k − i) mod N]   (mod 8192)`

Each pre-mask accumulator is `≤ 16·8191² < 2^31 ≪ 2^64` (exact at `w = 64`),
so the `Z/8192` reduction is the single mask `& 8191` per coefficient, lowered
from `SAnd … (SLit 8191)` (the mask constant is materialised in the body — the
input word `inp[32]` is carried for ABI compatibility and never read).

## ABI (the byte-identical KAT contract)

`inCtxt` = 33 `r64` words: `0..15` = `a`, `16..31` = `b`, `32` = unused. The 16
output words are the **last 16 bindings** — the front's identity copies of
`o[0..15]` in order (`toLprogPhysAbi`'s last-`nOut` convention, map
`ntruOutStoreMap`). C side: `uint64_t *ntru_mul(uint64_t *out, const uint64_t
*inp)` with 8-byte element stride.

## Gates

* In-model: the front translates + lowers (`ntruLowered_isSome`); the 16
  output-capped front programs denote the independent `Nat` cyclic-convolution
  `% q` spec on edge + pseudo-random coefficient vectors (`ntru_denote_spec`);
  every binding is pure scalar arith (`ntru_is_purearith_only`); the last 16
  bindings are the output copies (`ntru_last_bindings_are_copies`).
* External: `make -C bench/ntru_compare ntru-mul-kat` byte-checks
  `gen/ntru_mul.s` against the independent C cyclic-convolution reference; the
  whole-KEM drivers (`owned-keygen`/`owned-encaps`/`owned-decaps`/
  `owned-roundtrip`) gate byte-identity vs liboqs (PQClean) end-to-end.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit

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

/-- Ring degree of this tile (`x^N − 1`). The true ntruhrss701 degree is
    `n = 701`; this is the same code at `N = 16`. -/
abbrev N : Nat := 16

/-- The coefficient modulus is `q = 8192 = 2^13`; reduction is
    `& (q − 1) = & 8191`. -/
abbrev qMask : Nat := 8191

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

/-- The cyclic schoolbook accumulator expression for coefficient `k`:
    `Σ_{i < N} a[i]·b[(k − i) mod N]` as a left-nested `SAdd` chain (all `N`
    products contribute — the `x^N ≡ 1` ring fold). -/
def coeffSum (k : Nat) : SExpr :=
  let terms := (List.range N).map (fun i =>
    SExpr.SMul (.SVar (aN i)) (.SVar (bN ((k + N - i) % N))))
  match terms with
  | [] => .SLit 0
  | t :: ts => ts.foldl (fun acc t' => .SAdd acc t') t

/-- The statements for coefficient `k`: accumulate, then the single `& 8191`
    field mask (the mask constant is a literal — no input word is read for it). -/
def coeffStmts (k : Nat) : List LowCT :=
  let x := "x" ++ toString k
  let o := "o" ++ toString k
  [ .RScalarSetExpr x (coeffSum k),
    .RScalarSetExpr o (.SAnd (.SVar x) (.SLit qMask)) ]

/-- The full tile body: all `N` coefficient blocks, then the `N` output copies
    `f[k] := o[k]` — each lowering to exactly ONE binding, so the **last `N`
    bindings** carry `o[0..N−1]` in order. -/
def mulBody : LowCT := seqAll (
  ((List.range N).flatMap coeffStmts)
  ++ (List.range N).map (fun k =>
      .RScalarSetExpr ("f" ++ toString k) (.SVar ("o" ++ toString k))))

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `a[0]`) is the context head, word `32` the deepest —
input word `i` at De Bruijn index `i`, the 33-word layout
`JasminLprogExportNtru` maps (`a | b | unused`). -/

/-- The input words, in word order (`0..32`). -/
def wordNames : List String :=
  (List.range N).map aN ++ (List.range N).map bN ++ ["pad32"]

/-- Bind a name list onto a `replicate`-`sword 64` context, first name = head. -/
def bindAll : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindAll ns).bind n

/-- The source context: 33 `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate 33 (.sword 64)

/-- The source `VarMap` (word 0 = `a[0]` at the head). -/
def srcVM : VarMap srcCtx := bindAll wordNames

/-! ## 3. The front-emitted programs -/

/-- Push `mulBody` through the `CProg`-free control front and cap with
    `ret <name>`. `none` if the front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM mulBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted tile, lowered to the jasmin dialect (capped at the final
    output copy `f15`, whose binding is the `Com`'s last). -/
def ntruLoweredOpt :=
  (frontComAt ("f" ++ toString (N - 1))).bind
    DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem ntruLowered_isSome : ntruLoweredOpt.isSome := by native_decide

/-- The input context: 33 `r64` words (16 `a` + 16 `b` + 1 unused pad word). -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 33 r64

/-- The deployed `Z/8192` cyclic ring-multiply tile `Com jasminDialect` —
    FRONT-GENERATED (`translateDialectControl` + `cryptoDialectToJasminCom`),
    not hand-built. Rendered to owned `.s` by
    `bench/ntru_compare/ntru_mul_owned_emit.lean` (maps in
    `JasminLprogExportNtru`) under the `ntru_mul` symbol. -/
def ntruMulCom : Com jasminDialect inCtxt r64 :=
  ntruLoweredOpt.get ntruLowered_isSome

/-! ## 4. `denote = spec` vs the independent cyclic-convolution-`% q` reference

`refCoeff` is the direct `Nat` transcription of `ref_ntru_mul` in
`ntru_mul_kat.c` — independent of the emitted accumulation shape. -/

/-- The independent reference coefficient:
    `(Σ_{i < N} a[i]·b[(k − i) mod N]) mod 8192`. -/
def refCoeff (a b : List Nat) (k : Nat) : Nat :=
  ((List.range N).foldl (fun acc i =>
    acc + a.getD i 0 * b.getD ((k + N - i) % N) 0) 0) % 8192

/-- Sample coefficient-vector pairs (each 16 coeffs `< q`): edges +
    pseudo-random. -/
def samples : List (List Nat × List Nat) :=
  [ ((List.range N).map (fun _ => 0), (List.range N).map (fun _ => 0)),
    ((List.range N).map (fun _ => 8191), (List.range N).map (fun _ => 8191)),
    ((List.range N).map (fun i => (i * 1234 + 567) % 8192),
     (List.range N).map (fun i => (i * 4321 + 89) % 8192)),
    ((List.range N).map (fun i => (i * i * 991 + 17) % 8192),
     (List.range N).map (fun i => (8191 - i * 273 % 8192) % 8192)) ]

/-- Build a head-first valuation from a positional word function (entry `j` of
    the `replicate`-context gets `g j`). -/
def mkVal (g : Nat → BitVec 64) :
    (n : Nat) → @Ctxt.Valuation catCryptDialect _ (List.replicate n (.sword 64))
  | 0 => .nil
  | n + 1 => .cons (g 0) (mkVal (fun j => g (j + 1)) n)

/-- The head-first source valuation of a sample: `a`, `b`, then the unused pad
    word (`0`, matching the KAT harness's `inp[32] = 0`). -/
def valOf (a b : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  mkVal (fun i =>
    if i < 16 then BitVec.ofNat 64 (a.getD i 0)
    else if i < 32 then BitVec.ofNat 64 (b.getD (i - 16) 0)
    else 0) 33

/-- Denote the front program capped at slot `name` on a sample (result word). -/
def frontDenoteAt (name : String) (a b : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf a b))

/-- **denote = independent spec, all 16 output coefficients.** The front
    program capped at output copy `f[k]` denotes the independent cyclic
    convolution `% 8192` reference on every sample — the 16 values the owned
    render's last-16-bindings epilogue stores to `out[0..15]`. -/
theorem ntru_denote_spec :
    samples.all (fun (a, b) =>
      (List.range N).all (fun k =>
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

theorem ntru_is_purearith_only : allPureArith ntruMulCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last 16 bindings** are identity copies — the `f[0..15]` output
    copies the owned render's last-`nOut` epilogue stores to `out[0..15]`. -/
theorem ntru_last_bindings_are_copies :
    ((copyFlags ntruMulCom).drop ((copyFlags ntruMulCom).length - N))
      = List.replicate N true := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit
