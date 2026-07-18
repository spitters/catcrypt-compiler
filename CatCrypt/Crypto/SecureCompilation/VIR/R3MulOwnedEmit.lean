/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom

set_option autoImplicit false

/-!
# NTRU Prime sntrup761 trinary (`Z/3`) polynomial-multiply tile, FRONT-COMPILED

The `Z/3` coefficient arithmetic of sntrup761's `R3_mult` (the trinary decrypt
product `e · ginv` in decapsulation), sourced through the verified `CProg`-free
front — NO hand-built `Com` anywhere:

```
  mulBody (LowCT: RScalarSetExpr schoolbook + Barrett word math over the 36 slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  r3MulCom : Com jasminDialect inCtxt r64
```

The consumer `JasminLprogExportSntrup` renders `r3MulCom` to owned AT&T `.s`
via `Com.toLprogPhysAbi` (`bench/sntrup_compare/sntrup_owned_emit.lean` →
`gen/r3_mul.s`, symbol `r3_mul`, no jasminc).

## Scope (stated plainly)

This is the `Z/3` coefficient arithmetic (schoolbook product + Barrett
reduction modulo `q = 3`) over a width-`N = 16` slice. The `x^761 − x − 1`
ring fold, the full degree `p = 761`, and the signed `{-1,0,1} ↔ {0,1,2}`
recoding are tiled/handled by the C driver — out of scope for this
straight-line kernel.

## Kernel

Inputs `a[0..15]`, `b[0..15]` (coeffs in `{0,1,2}`, the unsigned trinary
representatives), Barrett multiplier `m = ⌊2¹⁶/3⌋ = 21845` and modulus `q = 3`
read from the input buffer. Outputs the `2N − 1 = 31` coefficients
`out[k] = Σ_{i+j=k} a[i]·b[j] mod 3`. Each pre-reduction accumulator is
`≤ 16·2² = 64 < 2¹⁶`; the per-coefficient reduction:
```
  y = x − ((x·m) >> 16)·q                  -- Barrett, y ∈ [0, 2q)
  d = y − q;  z = d + (d >> 63)·q          -- branchless cond-subtract
  e = z − q;  o = e + (e >> 63)·q          -- second block (robustness)
```
The shifts lower to immediate-count `shrImm`; `m`, `q` are register reads.

## ABI (unchanged — the byte-identical KAT contract)

`inCtxt` = 36 `r64` words, identical layout to `Sntrup761MulEmit`: `0..15` =
`a`, `16..31` = `b`, `32` = `m`, `33` = `q`, `34`/`35` = the shift words
(carried for ABI compatibility; not read — the shift amounts are immediates).
The 31 output words are the **last 31 bindings** (map `r3OutStoreMap`).

## Gates

* In-model: the front translates + lowers (`r3Lowered_isSome`); the 31
  output-capped front programs denote the independent `Nat` schoolbook-`% 3`
  spec on edge + pseudo-random trinary vectors (`r3_denote_spec`); every
  binding is pure scalar arith (`r3_is_purearith_only`); the last 31 bindings
  are the output copies (`r3_last_bindings_are_copies`).
* External: `gen/r3_mul.s` drives the `Z/3` ring product of
  `make -C bench/sntrup_compare owned-decaps` / `owned-roundtrip`, gated
  byte-identical (shared secret + implicit-reject) vs liboqs (OpenSSH).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.R3MulOwnedEmit

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
/-- The trinary modulus `q = 3`. -/
def qNat : Nat := 3
/-- The Barrett multiplier `m = ⌊2¹⁶/3⌋`. -/
def mNat : Nat := 21845
/-- The Barrett shift (`⌊·/2¹⁶⌋` for `q = 3`). -/
def barrettShift : Nat := 16

/-! ## 1. The straight-line `LowCT` body (the `Sntrup761MulEmit` shape at
`q = 3`) -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- `a`-coefficient slot name. -/
def aN (i : Nat) : String := "a" ++ toString i
/-- `b`-coefficient slot name. -/
def bN (i : Nat) : String := "b" ++ toString i

/-- The schoolbook accumulator expression for coefficient `k`. -/
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

/-- The full tile body: all 31 coefficient blocks, then the 31 output copies
    `f[k] := o[k]` (the **last 31 bindings**, in order). -/
def mulBody (shift : Nat) : LowCT := seqAll (
  ((List.range outLen).flatMap (coeffStmts shift))
  ++ (List.range outLen).map (fun k =>
      .RScalarSetExpr ("f" ++ toString k) (.SVar ("o" ++ toString k))))

/-! ## 2. Source context + `VarMap` (36 words, `a | b | m | q | shA | 63`) -/

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
def r3LoweredOpt :=
  (frontComAt ("f" ++ toString (outLen - 1))).bind
    DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem r3Lowered_isSome : r3LoweredOpt.isSome := by native_decide

/-- The input context: 36 `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 36 r64

/-- The deployed `Z/3` tile `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    Rendered to owned `.s` by `bench/sntrup_compare/sntrup_owned_emit.lean`
    (maps in `JasminLprogExportSntrup`) under the `r3_mul` symbol. -/
def r3MulCom : Com jasminDialect inCtxt r64 :=
  r3LoweredOpt.get r3Lowered_isSome

/-! ## 4. `denote = spec` vs the independent schoolbook-`% 3` reference -/

/-- The independent reference coefficient: `(Σ_{i+j=k} a[i]·b[j]) mod 3`. -/
def refCoeff (a b : List Nat) (k : Nat) : Nat :=
  ((List.range width).foldl (fun acc i =>
    if i ≤ k ∧ k - i < width then acc + a.getD i 0 * b.getD (k - i) 0 else acc)
    0) % qNat

/-- Sample trinary-vector pairs (each 16 coeffs in `{0,1,2}`): edges +
    pseudo-random. -/
def samples : List (List Nat × List Nat) :=
  [ ((List.range 16).map (fun _ => 0), (List.range 16).map (fun _ => 0)),
    ((List.range 16).map (fun _ => 2), (List.range 16).map (fun _ => 2)),
    ((List.range 16).map (fun i => i % 3), (List.range 16).map (fun i => (i + 1) % 3)),
    ((List.range 16).map (fun i => (i * 7 + 1) % 3),
     (List.range 16).map (fun i => (i * 5 + 2) % 3)) ]

/-- Build a head-first valuation from a value list. -/
def valOfList : (vs : List (BitVec 64)) →
    @Ctxt.Valuation catCryptDialect _ (List.replicate vs.length (.sword 64))
  | [] => .nil
  | v :: vs => .cons v (valOfList vs)

/-- The head-first source valuation of a sample: `a`, `b`, then
    `m, q, 16, 63`. -/
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
    `% 3` reference on every sample. -/
theorem r3_denote_spec :
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

theorem r3_is_purearith_only : allPureArith r3MulCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last 31 bindings** are identity copies — the `f[0..30]` output
    copies the owned render's last-`nOut` epilogue stores to `out[0..30]`. -/
theorem r3_last_bindings_are_copies :
    ((copyFlags r3MulCom).drop ((copyFlags r3MulCom).length - outLen))
      = List.replicate outLen true := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.R3MulOwnedEmit
