/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2b
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2b

/-!
# BLAKE2b G as a `catCryptDialect → jasmin → x86` path

The RFC 7693 §3.1 BLAKE2b G mixing function is a *benchmarked* primitive
(`bench/blake3_compare` / HACL* BLAKE2). It is the width-64 ARX sibling of the
ChaCha20 quarter-round; besides this module it reaches owned x86 through the
compile-from-hax front (`CompileFromHaxBlake2b.lean`, which emits the four G
output words via `compileFromHax`). This module gives BLAKE2b coverage in the
high algebraic crypto-SSA surface `catCryptDialect`, mirroring
`Chacha20QRCatCryptEmit.lean`: it builds the G mixing function *natively* as a
straight-line `Com catCryptDialect` program over the dialect's width-64 word ops
(`bvAdd`/`bvXor`/`bvRor`), proves it denotes to the canonical RFC-7693 spec
(`CompileFromHaxBlake2b.blake2bG{a,b,c,d}Spec`), and lowers it through the
committed `catCryptDialect → jasminDialect` seam
(`DialectToJasminCom.cryptoDialectToJasminCom`), composing the seam's
denote-preservation so the *lowered jasmin program* denotes to the same RFC spec.
The lowered jasmin `Com` then prints to `.jazz` through the single Jasmin printer
(`JasminPrintText.emitJazzN`: `nfToJasmin` followed by the checked printer).

```
RFC-7693 §3.1 BLAKE2b G  (CompileFromHaxBlake2b.blake2bG{a,b,c,d}Spec, the spec)
        ▲                         ▲
        │ denote = spec           │ denote = spec  (via the seam)
   Com catCryptDialect ──cryptoDialectToJasminCom──▶ Com jasminDialect ──emitJazzN──▶ .jazz
```

## The 14-op straight-line block (`w = 64`)

BLAKE2b G (RFC 7693 §3.1) over four state words `(a,b,c,d)` and two message words
`(x,y)`, all arithmetic mod 2⁶⁴, `>>>` right-rotate:

```
a = a + b + x;   d = (d ^ a) >>> 32;
c = c + d;       b = (b ^ c) >>> 24;
a = a + b + y;   d = (d ^ a) >>> 16;
c = c + d;       b = (b ^ c) >>> 63;
```

The two three-operand adds (`a + b + x`, `a + b + y`) each split into two
`bvAdd` ops, giving **14** dialect ops: 6 `bvAdd`, 4 `bvXor`, 4 `bvRor`. Unlike
the ChaCha quarter-round (which rotates *left* and uses `rotl(x,n) = ror(x,w-n)`),
BLAKE2b G rotates *right*, so each rotate maps **directly** to `bvRor 64 n`
(`32/24/16/63`) — no rotate-direction bridge is needed; `bvRor` denotes to
`BitVec.rotateRight` and lowers to jasmin `rorImm`.

## Contents

* `blake2bGCatCrypt{A,B,C,D}` — the four output words of G as native
  `Com catCryptDialect` programs over the shared 14-op block.
* `blake2bG_catcrypt_denote{A,B,C,D}` — each catCrypt program denotes to the
  matching RFC-7693 spec component (`blake2bG{a,b,c,d}Spec`).
* `blake2bG_jasmin_*` — the seam lowers each program (returns `some`), and
  `blake2bG_jasmin_denote{A,B,C,D}` proves the lowered *jasmin* `Com` denotes to
  the same RFC spec component, composing the catCrypt denote with the seam's
  `cryptoDialectToJasminCom_denote_eq'`.
* `blake2bGSig`, `blake2bGJazzA` — the signature and the `.jazz` text of the lowered
  `a`-output program printed by `JasminPrintText.emitJazzN`; a returned text parses to
  the unit `nfToJasmin` returns (`JasminPrintText.emitJazzN_parse`). Checks pin that
  the text exists and carries `#ROR_64`, `+` and `^`, and the parameter and
  instruction counts of the lowered function.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Blake2bGCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy ctTransTy_sword)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2b
  (blake2bGaSpec blake2bGbSpec blake2bGcSpec blake2bGdSpec)

/-! ## 1. The dialect word type and the input context

G operates on six 64-bit words `(a, b, c, d, x, y)`. The input context is six
copies of `sword 64`; the input valuation `a :: b :: c :: d :: x :: y :: ∅`
binds `a` to de Bruijn `here`, `b` to `there here`, …, `y` to `there⁵ here`. -/

/-- The 64-bit machine-word dialect type. -/
abbrev T64 : CryptoTy := .sword 64

/-- The six-word input context `[a,b,c,d,x,y]`. -/
abbrev GCtx : Ctxt catCryptDialect := [T64,T64,T64,T64,T64,T64]

/-! ## 2. The 14 straight-line ops

Each op is built at its own De Bruijn context (the context grows by one binding
per op, at the front). Each is declared individually because the dialect's
`Expr` structure-literal does not parse inline inside a deeply nested `Com.var`
chain. -/

/-- `a1a = a + b`. Ctx `[a,b,c,d,x,y]`; `a = here`, `b = there here`. -/
abbrev g1 : Expr catCryptDialect GCtx T64 :=
  { op := .bvAdd 64, retTy_eq := rfl,
    args := HVector.cons .here (HVector.cons (.there .here) HVector.nil) }

/-- `a1 = a1a + x`. Ctx `[a1a,a,b,c,d,x,y]`; `a1a = here`, `x = there⁵ here`. -/
abbrev g2 : Expr catCryptDialect (T64 :: GCtx) T64 :=
  { op := .bvAdd 64, retTy_eq := rfl,
    args := HVector.cons .here
      (HVector.cons (.there (.there (.there (.there (.there .here))))) HVector.nil) }

/-- `d1x = d ^ a1`. Ctx `[a1,a1a,a,b,c,d,x,y]`; `d = there⁵ here`, `a1 = here`. -/
abbrev g3 : Expr catCryptDialect (T64 :: T64 :: GCtx) T64 :=
  { op := .bvXor 64, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there .here)))))
      (HVector.cons .here HVector.nil) }

/-- `d1 = ror d1x 32`. Ctx `[d1x,a1,a1a,a,b,c,d,x,y]`; `d1x = here`. -/
abbrev g4 : Expr catCryptDialect (T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvRor 64 32, retTy_eq := rfl,
    args := HVector.cons .here HVector.nil }

/-- `c1 = c + d1`. Ctx `[d1,d1x,a1,a1a,a,b,c,d,x,y]`; `c = there⁶ here`, `d1 = here`. -/
abbrev g5 : Expr catCryptDialect (T64 :: T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvAdd 64, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there (.there .here))))))
      (HVector.cons .here HVector.nil) }

/-- `b1x = b ^ c1`. Ctx `[c1,d1,d1x,a1,a1a,a,b,c,d,x,y]`; `b = there⁶ here`, `c1 = here`. -/
abbrev g6 : Expr catCryptDialect (T64 :: T64 :: T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvXor 64, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there (.there .here))))))
      (HVector.cons .here HVector.nil) }

/-- `b1 = ror b1x 24`. Ctx `[b1x,c1,d1,d1x,a1,a1a,a,b,c,d,x,y]`; `b1x = here`. -/
abbrev g7 : Expr catCryptDialect (T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvRor 64 24, retTy_eq := rfl,
    args := HVector.cons .here HVector.nil }

/-- `a2a = a1 + b1`. Ctx `[b1,b1x,c1,d1,d1x,a1,a1a,a,b,c,d,x,y]`;
    `a1 = there⁵ here`, `b1 = here`. -/
abbrev g8 : Expr catCryptDialect (T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvAdd 64, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there .here)))))
      (HVector.cons .here HVector.nil) }

/-- `a2 = a2a + y`. Ctx `[a2a,b1,b1x,c1,d1,d1x,a1,a1a,a,b,c,d,x,y]`;
    `a2a = here`, `y = there¹³ here`. -/
abbrev g9 : Expr catCryptDialect
    (T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvAdd 64, retTy_eq := rfl,
    args := HVector.cons .here
      (HVector.cons
        (.there (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there .here)))))))))))))
        HVector.nil) }

/-- `d2x = d1 ^ a2`. Ctx `[a2,a2a,b1,b1x,c1,d1,d1x,a1,a1a,a,b,c,d,x,y]`;
    `d1 = there⁵ here`, `a2 = here`. -/
abbrev g10 : Expr catCryptDialect
    (T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvXor 64, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there .here)))))
      (HVector.cons .here HVector.nil) }

/-- `d2 = ror d2x 16`. Ctx `[d2x,a2,a2a,b1,b1x,c1,d1,d1x,a1,a1a,a,b,c,d,x,y]`; `d2x = here`. -/
abbrev g11 : Expr catCryptDialect
    (T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvRor 64 16, retTy_eq := rfl,
    args := HVector.cons .here HVector.nil }

/-- `c2 = c1 + d2`. Ctx `[d2,d2x,a2,a2a,b1,b1x,c1,d1,d1x,a1,a1a,a,b,c,d,x,y]`;
    `c1 = there⁶ here`, `d2 = here`. -/
abbrev g12 : Expr catCryptDialect
    (T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: GCtx) T64 :=
  { op := .bvAdd 64, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there (.there .here))))))
      (HVector.cons .here HVector.nil) }

/-- `b2x = b1 ^ c2`. Ctx `[c2,d2,d2x,a2,a2a,b1,b1x,…]`; `b1 = there⁵ here`, `c2 = here`. -/
abbrev g13 : Expr catCryptDialect
    (T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: GCtx)
    T64 :=
  { op := .bvXor 64, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there .here)))))
      (HVector.cons .here HVector.nil) }

/-- `b2 = ror b2x 63`. Ctx `[b2x,c2,d2,d2x,a2,…]`; `b2x = here`. -/
abbrev g14 : Expr catCryptDialect
    (T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64
      :: GCtx)
    T64 :=
  { op := .bvRor 64 63, retTy_eq := rfl,
    args := HVector.cons .here HVector.nil }

/-! ## 3. The four output programs

After the 14-op block the context head order is
`[b2,b2x,c2,d2,d2x,a2,a2a,b1,b1x,c1,d1,d1x,a1,a1a,a,b,c,d,x,y]`, so the RFC
outputs are `a2 = there⁵ here`, `b2 = here`, `c2 = there² here`,
`d2 = there³ here`. The four `Com` programs share the same 14-op block and differ
only in the return variable. -/

/-- The final 20-binding context after the 14-op block (head-first). -/
abbrev GFinalCtx : Ctxt catCryptDialect :=
  T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64 :: T64
    :: GCtx

/-- The shared 14-op straight-line block, abstracted over the return variable
    (a `Var` of the final 20-binding context). -/
abbrev gBlock (ret : Ctxt.Var (d := catCryptDialect) GFinalCtx T64) :
    Com catCryptDialect GCtx T64 :=
  Com.var g1 (Com.var g2 (Com.var g3 (Com.var g4 (Com.var g5 (Com.var g6 (Com.var g7
    (Com.var g8 (Com.var g9 (Com.var g10 (Com.var g11 (Com.var g12 (Com.var g13 (Com.var g14
      (Com.ret ret))))))))))))))

/-- The `a` output (`a2 = a'`): RFC-7693 `blake2bGaSpec`. -/
abbrev blake2bGCatCryptA : Com catCryptDialect GCtx T64 :=
  gBlock (.there (.there (.there (.there (.there .here)))))

/-- The `b` output (`b2 = b'`): RFC-7693 `blake2bGbSpec`. -/
abbrev blake2bGCatCryptB : Com catCryptDialect GCtx T64 :=
  gBlock .here

/-- The `c` output (`c2 = c'`): RFC-7693 `blake2bGcSpec`. -/
abbrev blake2bGCatCryptC : Com catCryptDialect GCtx T64 :=
  gBlock (.there (.there .here))

/-- The `d` output (`d2 = d'`): RFC-7693 `blake2bGdSpec`. -/
abbrev blake2bGCatCryptD : Com catCryptDialect GCtx T64 :=
  gBlock (.there (.there (.there .here)))

/-! ## 4. `denote = spec` for the catCrypt programs

Each equation is closed by the same peel pattern as the ChaCha quarter-round:
(1) `rw [program, gBlock]` exposes the 14-op `Com.var` chain; (2) `rw` by the
per-op `rfl` step lemmas `denote_var_bvAdd64`/`bvXor64`/`bvRor64` (each peels one
binding to `body.denote (V.extend (op …))`); (3) `simp only [Com.denote,
lookup_*_extend]` resolves the peeled bindings' de-Bruijn lookups; (4)
`rw [blake2bG?Spec]` unfolds the spec, and a final `rfl` makes the two sides
structurally identical (BLAKE2b rotates RIGHT, so `bvRor` matches `rotateRight`
directly — no rotate-direction bridge). -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ### Waist functions and single-binding peel step lemmas (each `rfl`) -/

/-- `bvAdd` waist: the dialect add denotation (`w = 64`). -/
def gAddW (a b : BitVec 64) : BitVec 64 := a + b
/-- `bvXor` waist (`w = 64`). -/
def gXorW (a b : BitVec 64) : BitVec 64 := a ^^^ b
/-- `bvRor` waist (rotate-right by the immediate `n`, `w = 64`). -/
def gRorW (n : Nat) (a : BitVec 64) : BitVec 64 := a.rotateRight n

/-- Peel one `bvAdd 64` binding. -/
theorem denote_var_bvAdd64 {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvAdd 64) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (gAddW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvXor 64` binding. -/
theorem denote_var_bvXor64 {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (gXorW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvRor 64 n` binding. -/
theorem denote_var_bvRor64 {Γ : Ctxt catCryptDialect} {n : Nat} {s : CryptoTy}
    (va : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvRor 64 n) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (gRorW n (va.lookup V))) := rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head. -/
@[simp] theorem lookup_here_extend {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

/-- `Ctxt.Var.here.lookup` on a cons valuation reads the head. -/
@[simp] theorem lookup_here_cons {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (HVector.cons v V) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on a cons valuation skips the head. -/
@[simp] theorem lookup_there_cons {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (HVector.cons v V) = w.lookup V := rfl

/-- The valuation `a :: b :: c :: d :: x :: y :: ∅`. -/
abbrev inV (a b c d x y : BitVec 64) : Ctxt.Valuation (d := catCryptDialect) GCtx :=
  HVector.cons a (HVector.cons b (HVector.cons c (HVector.cons d
    (HVector.cons x (HVector.cons y HVector.nil)))))

/-- The 14-binding peel + lookup-resolve closer, shared by the four output
    proofs. The `rw` peels each binding; the `simp` resolves the peeled bindings'
    lookups; the spec unfold + `rfl` resolve the input-variable lookups and match
    `bvRor` to `rotateRight`. -/
macro "g_denote_close" specName:ident : tactic =>
  `(tactic|
    (rw [gBlock,
       denote_var_bvAdd64, denote_var_bvAdd64, denote_var_bvXor64, denote_var_bvRor64,
       denote_var_bvAdd64, denote_var_bvXor64, denote_var_bvRor64,
       denote_var_bvAdd64, denote_var_bvAdd64, denote_var_bvXor64, denote_var_bvRor64,
       denote_var_bvAdd64, denote_var_bvXor64, denote_var_bvRor64];
     simp only [Com.denote, lookup_here_extend, lookup_there_extend];
     rw [$specName:ident];
     simp only [gAddW, gXorW, gRorW];
     rfl))

/-- **`a` output.** The catCrypt BLAKE2b G program denotes to the RFC-7693
    `blake2bGaSpec` (`a' = a1 + b1 + y`). -/
theorem blake2bG_catcrypt_denoteA (a b c d x y : BitVec 64) :
    blake2bGCatCryptA.denote (inV a b c d x y) = blake2bGaSpec a b c d x y := by
  rw [blake2bGCatCryptA]; g_denote_close blake2bGaSpec

/-- **`b` output.** (`b' = (b1 ^ c2) >>> 63`). -/
theorem blake2bG_catcrypt_denoteB (a b c d x y : BitVec 64) :
    blake2bGCatCryptB.denote (inV a b c d x y) = blake2bGbSpec a b c d x y := by
  rw [blake2bGCatCryptB]; g_denote_close blake2bGbSpec

/-- **`c` output.** (`c' = c1 + d2`). -/
theorem blake2bG_catcrypt_denoteC (a b c d x y : BitVec 64) :
    blake2bGCatCryptC.denote (inV a b c d x y) = blake2bGcSpec a b c d x y := by
  rw [blake2bGCatCryptC]; g_denote_close blake2bGcSpec

/-- **`d` output.** (`d' = (d1 ^ a2) >>> 16`). -/
theorem blake2bG_catcrypt_denoteD (a b c d x y : BitVec 64) :
    blake2bGCatCryptD.denote (inV a b c d x y) = blake2bGdSpec a b c d x y := by
  rw [blake2bGCatCryptD]; g_denote_close blake2bGdSpec

/-! ## 5. Lowering through the `catCryptDialect → jasminDialect` seam

`cryptoDialectToJasminCom` lowers each program: every op
(`bvAdd`/`bvXor`/`bvRor`) is in the seam's covered fragment, so the lowering
returns `some`. -/

/-- The seam lowers the `a`-output program. -/
theorem blake2bG_jasmin_isSomeA : (cryptoDialectToJasminCom blake2bGCatCryptA).isSome := by
  native_decide

/-- The seam lowers the `b`-output program. -/
theorem blake2bG_jasmin_isSomeB : (cryptoDialectToJasminCom blake2bGCatCryptB).isSome := by
  native_decide

/-- The seam lowers the `c`-output program. -/
theorem blake2bG_jasmin_isSomeC : (cryptoDialectToJasminCom blake2bGCatCryptC).isSome := by
  native_decide

/-- The seam lowers the `d`-output program. -/
theorem blake2bG_jasmin_isSomeD : (cryptoDialectToJasminCom blake2bGCatCryptD).isSome := by
  native_decide

/-- The lowered jasmin `Com` for the `a` output. -/
def blake2bGJasminA : Com jasminDialect (mapCtx GCtx) (mapTy T64) :=
  (cryptoDialectToJasminCom blake2bGCatCryptA).get blake2bG_jasmin_isSomeA

/-- The lowered jasmin `Com` for the `b` output. -/
def blake2bGJasminB : Com jasminDialect (mapCtx GCtx) (mapTy T64) :=
  (cryptoDialectToJasminCom blake2bGCatCryptB).get blake2bG_jasmin_isSomeB

/-- The lowered jasmin `Com` for the `c` output. -/
def blake2bGJasminC : Com jasminDialect (mapCtx GCtx) (mapTy T64) :=
  (cryptoDialectToJasminCom blake2bGCatCryptC).get blake2bG_jasmin_isSomeC

/-- The lowered jasmin `Com` for the `d` output. -/
def blake2bGJasminD : Com jasminDialect (mapCtx GCtx) (mapTy T64) :=
  (cryptoDialectToJasminCom blake2bGCatCryptD).get blake2bG_jasmin_isSomeD

/-! ## 6. `denote = spec` for the lowered jasmin programs (via the seam)

The seam's denote-preservation `cryptoDialectToJasminCom_denote_eq'` states the
lowered jasmin denote equals `ctTransTy` of the catCrypt denote; on a `sword 64`
value `ctTransTy` is the identity. Composing with the catCrypt `denote = spec`
gives the jasmin `denote = spec`. -/

/-- **`a` output, lowered.** The jasmin program produced by the seam denotes to
    the RFC-7693 `blake2bGaSpec`. -/
theorem blake2bG_jasmin_denoteA (a b c d x y : BitVec 64) :
    blake2bGJasminA.denote (ctMapValD (inV a b c d x y)) = blake2bGaSpec a b c d x y := by
  have h := cryptoDialectToJasminCom_denote_eq' blake2bGCatCryptA (inV a b c d x y)
    blake2bGJasminA (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T64) _ = _
  rw [ctTransTy_sword (w := 64)]
  exact blake2bG_catcrypt_denoteA a b c d x y

/-- **`b` output, lowered.** -/
theorem blake2bG_jasmin_denoteB (a b c d x y : BitVec 64) :
    blake2bGJasminB.denote (ctMapValD (inV a b c d x y)) = blake2bGbSpec a b c d x y := by
  have h := cryptoDialectToJasminCom_denote_eq' blake2bGCatCryptB (inV a b c d x y)
    blake2bGJasminB (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T64) _ = _
  rw [ctTransTy_sword (w := 64)]
  exact blake2bG_catcrypt_denoteB a b c d x y

/-- **`c` output, lowered.** -/
theorem blake2bG_jasmin_denoteC (a b c d x y : BitVec 64) :
    blake2bGJasminC.denote (ctMapValD (inV a b c d x y)) = blake2bGcSpec a b c d x y := by
  have h := cryptoDialectToJasminCom_denote_eq' blake2bGCatCryptC (inV a b c d x y)
    blake2bGJasminC (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T64) _ = _
  rw [ctTransTy_sword (w := 64)]
  exact blake2bG_catcrypt_denoteC a b c d x y

/-- **`d` output, lowered.** -/
theorem blake2bG_jasmin_denoteD (a b c d x y : BitVec 64) :
    blake2bGJasminD.denote (ctMapValD (inV a b c d x y)) = blake2bGdSpec a b c d x y := by
  have h := cryptoDialectToJasminCom_denote_eq' blake2bGCatCryptD (inV a b c d x y)
    blake2bGJasminD (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T64) _ = _
  rw [ctTransTy_sword (w := 64)]
  exact blake2bG_catcrypt_denoteD a b c d x y

/-! ## 7. Emit: the lowered jasmin program prints to `.jazz`

`JasminPrintText.emitJazzN` lowers a jasmin `Com` with `nfToJasmin` and prints the
unit with the checked printer; a returned text parses back to that unit
(`JasminPrintText.emitJazzN_parse`). -/

open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin (JazzSig ptyOf nfToJasmin)

/-- The signature of a BLAKE2b G output word: the six `reg u64` parameters in the
    reverse order of the context, `y, x, d, c, b, a`, and a `reg u64` result. -/
def blake2bGSig : JazzSig (mapCtx GCtx) (mapTy T64) where
  params := ["y", "x", "d", "c", "b", "a"].map fun v => (v, .reg, ptyOf (.reg 64))
  result := (.reg, ptyOf (.reg 64))
  resultParam := none
  params_length := rfl

/-- The `.jazz` text of the lowered `a`-output BLAKE2b G word, symbol `blake2b_g_a`,
    printed by the single Jasmin printer; `none` when `nfToJasmin` or the checked
    printer refuses. -/
def blake2bGJazzA : Option String :=
  JasminPrintText.emitJazzN "blake2b_g_a" blake2bGSig blake2bGJasminA

-- The text exists and carries the rotate (`bvRor` lowered to `rorImm`, printed as
-- `#ROR_64`), the add and the xor.
set_option kat.ms 500 in
#kat blake2bGJazzA.any fun s => s.contains "ROR" && s.contains "+" && s.contains "^"

-- The lowered function has six parameters and a body of 29 instructions.
#kat (nfToJasmin blake2bGSig "blake2b_g_a" (NFProg.ofCom blake2bGJasminA)).any
  fun u => u.fns.map (fun f => (f.fd.params.length, f.fd.body.length)) == [(6, 29)]

end CatCrypt.Crypto.SecureCompilation.VIR.Blake2bGCatCryptEmit
