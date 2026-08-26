/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

set_option autoImplicit false

/-!
# Poly1305 MAC — FRONT-COMPILED owned x86-64 kernel (`5×26`-limb HACL field-dot)

The fixed-`NBlk` Poly1305 130-bit field MAC over `𝔽_{2¹³⁰−5}`, sourced through
the verified `CProg`-free front — NO hand-built `Com` anywhere in the emit path:

```
  macBody (LowCT: RScalarSetExpr u64 word math over the 55 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  poly1305MacCom : Com jasminDialect inCtxt r64
```

The emit drivers (`bench/chachapoly_compare/poly1305_owned_emit.lean`,
`poly1305_aead_owned_emit.lean`) render `poly1305MacCom` to owned AT&T `.s` via
`Com.toLprogPhysAbi` (#476 owned-RA, 2-pointer SysV; NO jasminc) under the
export symbols `poly1305_mac` / `poly1305_mac_hacl_r`.

## Field schedule (HACL `5×26`)

The HACL `r5i = 5·rᵢ` precompute, five staggered register diagonals
(`d{o} = Σ_{i<5} a_i · key(o,i)`, wrap `r5_j` when `i > o`, each product
`26 + ≤29 ≤ 55` bits so five terms sum `< 2⁵⁸` — no widening), and the carry
chain with the `2¹³⁰ ≡ 5` top-limb fold.

## ABI (matches the C KAT harness `poly1305_mac`)

`bench/chachapoly_compare/poly1305_kat.c` / `chachapoly_kat.c` declare

  `extern uint64_t *poly1305_mac(uint64_t *out, const uint64_t *inp);`

a FIXED `NBLK = 10`-block kernel: `out` (RDI) receives the 5×26-bit MAC
accumulator limbs; `inp` (RSI) holds the clamped key limbs `r[0..4]` (5 u64)
then `NBLK` pre-packed 5-limb message blocks (`inp[5 + 5·i + k]`). The harness
zero-pads short messages at the FRONT (leading all-zero blocks fold to a no-op:
`(0+0)·r = 0`), packs the limbs, calls `poly1305_mac`, then does the final
mod-`2¹³⁰−5` freeze, `+ s`, and serialization in C.

* `inLoadMap` : argument slot `s` is root-order input `i = (nIn-1) - s`, loaded
  from `RSI + 8·i`. All `5 + 5·NBLK = 55` inputs are runtime loads.
* `outStoreMap` : 5 stores `out[k] = a_k` at `RDI + 8·k` — the LAST 5 bindings
  of the `Com` are the front's identity copies of `a0..a4` in order.
* constants (`5`, the `0x3ffffff` 26-bit mask) are `SLit` literals, lowered to
  in-body `regConst` / immediate-shift ops by the front.

## Gates

* In-model (cheap, structural): the front translates + lowers
  (`poly1305MacLowered_isSome`); all five output-capped front programs exist
  (`frontComAt_q_isSome`); every binding is a pure scalar-arith op
  (`poly1305_is_purearith_only`); the last five bindings are the output copies
  (`poly1305_last_five_bindings_are_copies`).
* External: `bench/chachapoly_compare/poly1305_owned_refcheck.lean` `#eval`-checks
  the `Com` denotation against the INDEPENDENT plain-`Nat` RFC 8439 Horner
  reference mod `2¹³⁰−5` (§2.5.2 vector + pseudo-random cases), and the
  `poly1305-kat` / `chachapoly-kat` targets byte-check the owned `.s` against
  RFC 8439 vectors and HACL*.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poly1305Com

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

/-- The fixed Horner block count (`NBLK` in the C harness;
    RFC 8439 §2.8.2 = 1 AAD + 8 CT + 1 len). -/
abbrev NBlk : Nat := 10

/-- Number of `r64` input words: clamped key `r[0..4]` (5) then `NBlk` packed
    5-limb message blocks. -/
abbrev nIn : Nat := 5 + 5 * NBlk

/-- The 26-bit limb radix mask `2²⁶ − 1`. -/
abbrev limbMask : Nat := 0x3ffffff

/-! ## 0. Slot names

Input words: `0..4` = key limbs `r0..r4`, `5..54` = message limbs `m0..m49`
(`m{5·bi+k}` = limb `k` of block `bi`). Working slots: accumulator `a0..a4`,
wraps `r51..r54` (`5·rₖ`), diagonals `d0..d4`, scratch `c`,`t`, output copies
`q0..q4` (the last-five-bindings convention). -/

/-- Key-limb slot name `r{k}`. -/
def rN (k : Nat) : String := "r" ++ toString k
/-- Message-limb slot name `m{j}` (input word `5 + j`). -/
def mN (j : Nat) : String := "m" ++ toString j
/-- Accumulator slot name `a{k}`. -/
def aN (k : Nat) : String := "a" ++ toString k
/-- Wrap slot name `r5{k}` (`= 5·r{k}`). -/
def r5N (k : Nat) : String := "r5" ++ toString k
/-- Diagonal slot name `d{o}`. -/
def dN (o : Nat) : String := "d" ++ toString o
/-- Final output-copy slot name `q{k}` (the last-five-bindings convention). -/
def qN (k : Nat) : String := "q" ++ toString k

/-- Input word `i` name: `r{i}` for `i < 5`, else `m{i−5}`. -/
def inputName (i : Nat) : String := if i < 5 then rN i else mN (i - 5)

/-! ## 1. The straight-line `LowCT` body -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- The key-limb slot for diagonal `o`, term `i`: the wrap `r5_j` when `i > o`
    (natural position `i + j ≥ 5`), else `r_j`, with `j = (o + 5 − i) mod 5`. -/
def keyN (o i : Nat) : String :=
  let j := (o + 5 - i) % 5
  if i > o then r5N j else rN j

/-- Diagonal `o` as one `SExpr` tree: `Σ_{i=0}^{4} a_i · key(o,i)`. -/
def diagExpr (o : Nat) : SExpr :=
  (List.range 4).foldl
    (fun acc i' =>
      let i := i' + 1
      .SAdd acc (.SMul (.SVar (aN i)) (.SVar (keyN o i))))
    (.SMul (.SVar (aN 0)) (.SVar (keyN o 0)))

/-- The carry chain renormalizing `d0..d4` → `a0..a4`: low limbs `k = 0..3`
    (`c = d_k >> 26; a_k = d_k & mask; d_{k+1} += c`), then the `d4` top-limb
    `·5` fold (`2¹³⁰ ≡ 5`) and the `a0 → a1` settle. -/
def carryStmts : List LowCT :=
  ((List.range 4).flatMap (fun k =>
    [ .RScalarSetExpr "c" (.SShr (.SVar (dN k)) (.SLit 26)),
      .RScalarSetExpr (aN k) (.SAnd (.SVar (dN k)) (.SLit limbMask)),
      .RScalarSetExpr (dN (k+1)) (.SAdd (.SVar (dN (k+1))) (.SVar "c")) ]))
  ++ [ .RScalarSetExpr "c" (.SShr (.SVar (dN 4)) (.SLit 26)),
       .RScalarSetExpr (aN 4) (.SAnd (.SVar (dN 4)) (.SLit limbMask)),
       .RScalarSetExpr (aN 0) (.SAdd (.SVar (aN 0)) (.SMul (.SVar "c") (.SLit 5))),
       .RScalarSetExpr "t" (.SShr (.SVar (aN 0)) (.SLit 26)),
       .RScalarSetExpr (aN 0) (.SAnd (.SVar (aN 0)) (.SLit limbMask)),
       .RScalarSetExpr (aN 1) (.SAdd (.SVar (aN 1)) (.SVar "t")) ]

/-- One Horner block `bi`: add the five message limbs `m{5·bi+k}` into the
    accumulator, the five diagonals, the carry chain. -/
def blockStmts (bi : Nat) : List LowCT :=
  ((List.range 5).map (fun k =>
    .RScalarSetExpr (aN k) (.SAdd (.SVar (aN k)) (.SVar (mN (5 * bi + k))))))
  ++ ((List.range 5).map (fun o => .RScalarSetExpr (dN o) (diagExpr o)))
  ++ carryStmts

/-- The full fixed-`NBlk` MAC body: zero the accumulator, precompute the wraps
    `r5_k = 5·r_k`, fold the `NBlk` Horner blocks, then the five output copies
    `q_k := a_k` — each an identity `RScalarSetExpr` lowering to exactly ONE
    binding, so the **last five bindings** of the emitted `Com` carry `a0..a4`
    in order (the `toLprogPhysAbi` last-`nOut` output convention). -/
def macBody : LowCT := seqAll (
  ((List.range 5).map (fun k => .RScalarSetExpr (aN k) (.SLit 0)))
  ++ ((List.range 4).map (fun j =>
        .RScalarSetExpr (r5N (j+1)) (.SMul (.SVar (rN (j+1))) (.SLit 5))))
  ++ ((List.range NBlk).flatMap blockStmts)
  ++ ((List.range 5).map (fun k => .RScalarSetExpr (qN k) (.SVar (aN k)))))

/-! ## 2. Source context + `VarMap`

Head-first: input word `0` (= `r0`) is the context head, word `54` (= `m49`)
the deepest entry — so input word `i` sits at De Bruijn index `i`, the layout
the drivers' `inLoadMap` (`slot s ↦ RSI + 8·(nIn−1−s)`) expects. -/

/-- The source context: `nIn = 55` `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate nIn (.sword 64)

/-- Bind the deepest `k` input words (words `nIn−1` down to `nIn−k`). -/
def mkVMAux : (k : Nat) → VarMap (List.replicate k (.sword 64))
  | 0 => VarMap.empty
  | k + 1 => (mkVMAux k).bind (t := .sword 64) (inputName (nIn - 1 - k))

/-- The source `VarMap`: word `54` (`m49`) bound first (deepest), word `0`
    (`r0`) last (head). -/
def srcVM : VarMap srcCtx := mkVMAux nIn

/-! ## 3. The front-emitted programs -/

/-- Push `macBody` through the `CProg`-free control front and cap with
    `ret <name>` (a `u64` slot of the final `VarMap`). `none` if the front
    declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM macBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted MAC, lowered to the jasmin dialect (capped at the final
    output copy `q4`, whose binding is the `Com`'s last). -/
def poly1305MacLoweredOpt :=
  (frontComAt (qN 4)).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem poly1305MacLowered_isSome : poly1305MacLoweredOpt.isSome := by native_decide

/-- The input context of the deployed `Com`: `nIn = 55` `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate nIn r64

/-- **The whole fixed-`NBlk` Poly1305 MAC as a `Com jasminDialect`** —
    FRONT-GENERATED (`translateDialectControl` + `cryptoDialectToJasminCom`),
    not hand-built. Rendered to owned `.s` by the `bench/chachapoly_compare`
    emit drivers under `poly1305_mac` / `poly1305_mac_hacl_r`. -/
def poly1305MacCom : Com jasminDialect inCtxt r64 :=
  poly1305MacLoweredOpt.get poly1305MacLowered_isSome

/-! ## 4. Output-cap existence gate

The `denote = independent-spec` check on RFC 8439 vectors runs externally as a
`#eval` in `bench/chachapoly_compare/poly1305_owned_refcheck.lean` (over the
same `poly1305MacCom`), gated end-to-end by the `poly1305-kat` byte-check —
kept out of this module so the LSP stays light. -/

/-- All five output-capped front programs exist. -/
theorem frontComAt_q_isSome :
    (List.range 5).all (fun k => (frontComAt (qN k)).isSome) = true := by
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

theorem poly1305_is_purearith_only : allPureArith poly1305MacCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0` (the
    front's `RScalarSetExpr` result copy)? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last five bindings** are identity copies — the `q0..q4` output copies
    the owned render's last-`nOut` epilogue stores to `out[0..4]`. -/
theorem poly1305_last_five_bindings_are_copies :
    ((copyFlags poly1305MacCom).drop ((copyFlags poly1305MacCom).length - 5))
      = [true, true, true, true, true] := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Poly1305Com
