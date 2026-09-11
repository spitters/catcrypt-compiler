/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit


@[expose] public section
set_option autoImplicit false

/-!
# NTRU (ntruhrss701) core ring multiply via **2-way Karatsuba**, FRONT-COMPILED

The sub-quadratic companion to `Ntruhrss701MulEmit`. Where that module emits the
degree-`N = 16` cyclic ring multiply `Z/8192[x]/(x^N − 1)` by plain schoolbook
accumulation (`N² = 256` coefficient multiplies), this module emits the **same
ring multiply** with one level of 2-way Karatsuba over the linear product,
dropping the multiply count to `3·(N/2)² = 192`. The deployed `Com` is sourced
through the verified `CProg`-free front — NO hand-built `Com`:

```
  karaBody (LowCT: RScalarSetExpr Karatsuba word math over the coeff slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  ntruKaraCom : Com jasminDialect inCtxt r64
```

`ntruKaraCom` is then rendered to a `.jazz` export (`emitAbiOrchReg`, symbol
`ntru_mul_kara`) that is a drop-in for the schoolbook `ntru_mul` ABI.

## Algorithm (the math)

Split each operand at the midpoint `H = N/2 = 8`:

```
  a = aL + aH·y,   b = bL + bH·y,   y = x^H    (aL,aH,bL,bH width H)
```

The **linear** (acyclic) product `L = a·b` of degree `< 2N − 1 = 31` is

```
  P0 = aL·bL                            (deg 0..2H−2 = 0..14)
  P2 = aH·bH                            (deg 0..14)
  P1 = (aL+aH)·(bL+bH) − P0 − P2        (the Karatsuba middle term)
  L  = P0 + P1·y^H + P2·y^{2H}          i.e.  L[k] = P0[k] + P1[k−H] + P2[k−2H]
```

Each of `P0`, `P2`, and `(aL+aH)·(bL+bH)` is an `H×H = 8×8` schoolbook product
(`64` mul each, `192` total vs schoolbook's `256`). The cyclic fold `x^N ≡ 1`
recovers the ring product: `out[k] = (L[k] + L[k+N]) & 8191`.

## Soundness of the subtraction over `Z/8192`

The middle term needs `−P0 −P2`, which can be negative as an integer. Every
value is implicitly mod `2^64`, and `8192 = 2^13` divides `2^64`, so the final
`& 8191` reduction recovers the correct `Z/8192` coefficient regardless of
two's-complement wraparound in the intermediate subtractions. Each pre-mask
value is `≤ 16·(2·8191)² < 2^33 ≪ 2^64` (exact at `w = 64`).

## ABI (drop-in for the schoolbook `ntru_mul`)

`inCtxt` = 33 `r64` words: `0..15` = `a`, `16..31` = `b`, `32` = unused pad.
The 16 output words are the **last 16 bindings** — the front's identity copies
of `f[0..15]` (`emitAbiOrchReg`'s last-`nOut` convention). Export:
`export fn ntru_mul_kara(reg ptr u64[16] out, reg const ptr u64[33] inp)`. The
`& 8191` mask constant is front-materialised in the body (input word `inp[32]`
is carried for ABI compatibility and never read).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701KaratsubaEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- Karatsuba split point `H = N/2 = 8` (2-way, one level). -/
abbrev H : Nat := 8

/-! ## 1. The straight-line `LowCT` Karatsuba body

Slot-name conventions: `sa`/`sb` = the half sums, `p0x`/`p2x`/`psx` = the three
width-`H` half-products (15 coeffs each), `m` = the cross term, `c` = the full
degree-30 product, `kx`/`o` = the cyclic fold + mask, `f` = the output copies. -/

/-- Half-sum slot names. -/
def saN (i : Nat) : String := "sa" ++ toString i
def sbN (i : Nat) : String := "sb" ++ toString i
/-- Half-product / cross / full-coefficient slot names. -/
def p0N (t : Nat) : String := "p0x" ++ toString t
def p2N (t : Nat) : String := "p2x" ++ toString t
def psN (t : Nat) : String := "psx" ++ toString t
def mN (t : Nat) : String := "m" ++ toString t
def cN (t : Nat) : String := "c" ++ toString t

/-- Left-nested `SAdd` chain of a non-empty term list (`SLit 0` if empty). -/
def addChain : List SExpr → SExpr
  | [] => .SLit 0
  | t :: ts => ts.foldl (fun acc t' => .SAdd acc t') t

/-- Width-`H` half-product coefficient `t ∈ [0, 2H−2]` over the named factor
    slots: `Σ_{i+j=t, i,j<H} an(i)·bn(j)`. -/
def halfCoeff (an bn : Nat → String) (t : Nat) : SExpr :=
  addChain ((List.range H).filterMap (fun i =>
    if i ≤ t ∧ t - i < H then
      some (SExpr.SMul (.SVar (an i)) (.SVar (bn (t - i))))
    else none))

/-- The 16 half-sum bindings `sa[i] = a[i] + a[i+H]`, `sb[i] = b[i] + b[i+H]`. -/
def karaSums : List LowCT :=
  (List.range H).map (fun i =>
    .RScalarSetExpr (saN i) (.SAdd (.SVar (aN i)) (.SVar (aN (i + H)))))
  ++ (List.range H).map (fun i =>
    .RScalarSetExpr (sbN i) (.SAdd (.SVar (bN i)) (.SVar (bN (i + H)))))

/-- One width-`H` half-product: the `2H − 1 = 15` coefficient bindings. -/
def karaHalf (pfx : Nat → String) (an bn : Nat → String) : List LowCT :=
  (List.range (2 * H - 1)).map (fun t =>
    .RScalarSetExpr (pfx t) (halfCoeff an bn t))

/-- The cross term `m[t] = ps[t] − p0[t] − p2[t]` (exact in the backend's
    wrapping u64 arithmetic — see the module docstring). -/
def karaMid : List LowCT :=
  (List.range (2 * H - 1)).map (fun t =>
    .RScalarSetExpr (mN t)
      (.SSub (.SSub (.SVar (psN t)) (.SVar (p0N t))) (.SVar (p2N t))))

/-- Full-product coefficient `c[t]`, `t ∈ [0, 30]`:
    `c = p0 + x^H·m + x^{2H}·p2` — each summand present iff its index lies in
    the half-product range `[0, 2H−2]`. -/
def fullCoeff (t : Nat) : SExpr :=
  addChain (
    (if t < 2 * H - 1 then [SExpr.SVar (p0N t)] else [])
    ++ (if H ≤ t ∧ t < H + (2 * H - 1) then [SExpr.SVar (mN (t - H))] else [])
    ++ (if 2 * H ≤ t then [SExpr.SVar (p2N (t - 2 * H))] else []))

/-- The 31 full-product coefficient bindings. -/
def karaFull : List LowCT :=
  (List.range (2 * N - 1)).map (fun t => .RScalarSetExpr (cN t) (fullCoeff t))

/-- The cyclic `x^N ≡ 1` fold + `Z/8192` mask: `o[k] = (c[k] + c[k+N]) & 8191`
    (`c[31]` does not exist — the degree-30 product — so `o[15]` folds `c[15]`
    alone). -/
def karaCyc : List LowCT :=
  (List.range N).flatMap (fun k =>
    let folded : SExpr :=
      if k + N < 2 * N - 1 then .SAdd (.SVar (cN k)) (.SVar (cN (k + N)))
      else .SVar (cN k)
    [ .RScalarSetExpr ("kx" ++ toString k) folded,
      .RScalarSetExpr ("o" ++ toString k) (.SAnd (.SVar ("kx" ++ toString k)) (.SLit qMask)) ])

/-- The full Karatsuba tile body: half sums, the three half-products, the cross
    term, the full-product recombine, the cyclic fold + mask, then the `N`
    output copies `f[k] := o[k]` — each lowering to exactly ONE binding, so the
    **last `N` bindings** carry `o[0..N−1]` in order. -/
def karaBody : LowCT := seqAll (
  karaSums
  ++ karaHalf p0N aN bN
  ++ karaHalf p2N (fun i => aN (i + H)) (fun j => bN (j + H))
  ++ karaHalf psN saN sbN
  ++ karaMid
  ++ karaFull
  ++ karaCyc
  ++ (List.range N).map (fun k =>
      .RScalarSetExpr ("f" ++ toString k) (.SVar ("o" ++ toString k))))

/-! ## 2. The front-emitted `Com`

The source context + `VarMap` are shared with the schoolbook sibling
(`Ntruhrss701MulEmit.srcCtx`/`srcVM` — 33 head-first `u64` words `a | b | pad`). -/

/-- Push `karaBody` through the `CProg`-free control front and cap with
    `ret <name>`. `none` if the front declines. -/
def karaFrontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM karaBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted Karatsuba tile, lowered to the jasmin dialect (capped at
    the final output copy `f15`, whose binding is the `Com`'s last). -/
def karaLoweredOpt :=
  (karaFrontComAt ("f" ++ toString (N - 1))).bind
    DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem karaLowered_isSome : karaLoweredOpt.isSome := by native_decide

/-- The deployed `Z/8192` Karatsuba ring-multiply tile `Com jasminDialect` —
    FRONT-GENERATED (`translateDialectControl` + `cryptoDialectToJasminCom`),
    not hand-built. Rendered to a `.jazz` export below under the `ntru_mul_kara`
    symbol. -/
def ntruKaraCom : Com jasminDialect inCtxt r64 :=
  karaLoweredOpt.get karaLowered_isSome

/-- **Front provenance gate.** The rendered `Com` is exactly the front
    pipeline's output. -/
theorem ntruKara_front_provenance :
    (karaFrontComAt ("f" ++ toString (N - 1))).bind
        DialectToJasminCom.cryptoDialectToJasminCom
      = some ntruKaraCom :=
  (Option.some_get karaLowered_isSome).symm

/-! ## 3. Structural gates on the lowered `Com` -/

/-- Every binding is pure scalar arith (reusing the schoolbook sibling's checker). -/
theorem kara_is_purearith_only : allPureArith ntruKaraCom = true := by
  native_decide

/-- The **last 16 bindings** are identity copies — the `f[0..15]` output copies
    the render's last-`nOut` epilogue stores to `out[0..15]`. -/
theorem kara_last_bindings_are_copies :
    ((copyFlags ntruKaraCom).drop ((copyFlags ntruKaraCom).length - N))
      = List.replicate N true := by native_decide

/-- Count the multiply bindings of a lowered `Com`. -/
def mulCount : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var e body =>
    (match e.op with | .regArith .mul _ => 1 | _ => 0) + mulCount body

/-- **Karatsuba shape gate.** The lowered tile carries exactly the `3·H² = 192`
    multiplies of one 2-way Karatsuba level — vs the schoolbook sibling's 256. -/
theorem kara_mul_count_192 : mulCount ntruKaraCom = 192 := by native_decide

/-! ## 4. Binding count (register-file sizing) -/

/-- Binding count of a `Com`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-- The number of `regArith`/`regConst`/copy bindings of the lowered tile. -/
def karaBindingCount : Nat := comBindings ntruKaraCom

/-! ## 5. Emit the `.jazz` (register-arith mode) from the front `Com`.

`ntruKaraCom` is the front pipeline's output; `emitAbiOrchReg` renders it
structurally. Input word `i` is copied into register `in{i}`; binding `k` writes
register `t{k}` (fresh per binding — SSA). The `& 8191` mask constant is a body
literal (`regConst`), so no input word is read for it. -/

/-- Operand string for input word `i`: `a`/`b`/pad → the copied register `in{i}`. -/
def karaInName (i : Nat) : String := "in" ++ toString i

/-- The per-binding destination register `t{k}` (one per binding). -/
def karaDstName (k : Nat) : String := "t" ++ toString k

/-- The register file: the 33 input registers `in0..in32` and the per-binding
    result registers `t0..t{karaBindingCount−1}`. -/
def karaRegDecls : List String :=
  (List.range 33).map (fun i => "reg u64 in" ++ toString i)
    ++ (List.range karaBindingCount).map (fun k => "reg u64 t" ++ toString k)

/-- The emitted `.jazz` for the degree-`N` cyclic ring multiply via 2-way
    Karatsuba, rendered from the FRONT-GENERATED `ntruKaraCom`. ABI matches
    `ntru_mul` (drop-in): `reg ptr u64[16] out`, `reg const ptr u64[33] inp`. -/
def ntruKaraJazz : String :=
  JasminAbiEmit.emitAbiOrchReg "ntru_mul_kara" (w := 64) (nIn := 33) (nOut := N)
    (nCopy := 32) karaRegDecls karaInName karaDstName ntruKaraCom

/-! ### Structural sanity checks on the emitted text -/

/- The emitted `.jazz` carries the drop-in NTRU ring-multiply ABI (16-word out,
    33-word in), real multiplication (`*`, the half-products) and the Karatsuba
    middle-term subtraction (`-`), the front-materialised `& 8191` mask constant,
    and no skipped-op sentinel (every front-lowered binding renders to a real
    scalar assignment). -/
#guard (strContains ntruKaraJazz "export fn ntru_mul_kara(reg ptr u64[16] out, reg const ptr u64[33] inp)")
    && (strContains ntruKaraJazz " * ")
    && (strContains ntruKaraJazz " - ")
    && (strContains ntruKaraJazz "8191")
    && !(strContains ntruKaraJazz "non-regArith op skipped")

end CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701KaratsubaEmit
