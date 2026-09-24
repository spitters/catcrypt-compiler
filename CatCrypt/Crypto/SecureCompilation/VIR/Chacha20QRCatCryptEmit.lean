/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public meta import CatCrypt.Crypto.Jasmin.ChaCha20QR
public import CatCrypt.Crypto.Jasmin.ChaCha20QR

/-!
# ChaCha20 quarter-round as a `catCryptDialect → jasmin → x86` path

The RFC-8439 §2.1 ChaCha20 quarter-round is a *benchmarked* primitive. Besides this
module it reaches owned x86 through the THIR front
(`X86Backend/ChaChaQRThirEmit.lean`). This module gives quarter-round coverage in
the high algebraic crypto-SSA surface `catCryptDialect`: it builds the
quarter-round *natively* as a straight-line `Com catCryptDialect` program over
the dialect's word ops (`bvAdd`/`bvXor`/`bvRor`), proves it denotes to the canonical
RFC spec `Jasmin.ChaCha20QR.quarterRound`, and lowers it through the committed
`catCryptDialect → jasminDialect` seam
(`DialectToJasminCom.cryptoDialectToJasminCom`), composing the seam's
denote-preservation (`cryptoDialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`)
so the *lowered jasmin program* denotes to the same RFC spec. The lowered jasmin
`Com` then emits to `.jazz`/x86 via the existing `JasminPrint.emitJazz` printer.

```
RFC-8439 §2.1 quarterRound  (Jasmin.ChaCha20QR.quarterRound, the spec)
        ▲                         ▲
        │ denote = spec           │ denote = spec  (via the seam)
   Com catCryptDialect ──cryptoDialectToJasminCom──▶ Com jasminDialect ──emitJazz──▶ .jazz/x86
```

## The 12-op straight-line block

The quarter-round `a+=b; d^=a; d<<<=16; c+=d; b^=c; b<<<=12; a+=b; d^=a; d<<<=8;
c+=d; b^=c; b<<<=7` is 12 dialect ops: 4 `bvAdd`, 4 `bvXor`, 4 rotates. The
dialect's scalar-jasmin-lowering rotate is `bvRor` (rotate-right by an immediate,
which lowers to jasmin `rorImm`); `bvRol` is denote-only in the seam (jasmin has
no native scalar left-rotate). RFC's quarter-round rotates *left*, so we use the
identity `rotl(x, n) = rotr(x, 32 - n)`:
`d<<<16 = ror d 16`, `b<<<12 = ror b 20`, `d<<<8 = ror d 24`, `b<<<7 = ror b 25`.

Each rotate-left equals the corresponding `bvRor` denotation, so the dialect
program — which uses only seam-lowering ops — denotes to the RFC quarter-round.

## Contents

* `chacha20QRCatCrypt{A,B,C,D}` — the four output words of the quarter-round as
  native `Com catCryptDialect` programs over the 12-op block.
* `chacha20QR_catcrypt_denote{A,B,C,D}` — each catCrypt program denotes to the
  matching component of the RFC-8439 `quarterRound`.
* `chacha20QR_jasmin_*` — the seam lowers each program (`cryptoDialectToJasminCom`
  returns `some`), and `chacha20QR_jasmin_denote{A,B,C,D}` proves the lowered
  *jasmin* `Com` denotes to the same RFC `quarterRound` component, by composing
  the catCrypt denote with the seam's `cryptoDialectToJasminCom_denote_eq'`.
* `chacha20QRJazzA*` — the lowered jasmin program emits to `.jazz` text through
  `JasminPrint.emitJazz`, with a render smoke pinning the op shape (the quarter-
  round's `#ROR_32`/`+`/`^` reach the printer) and the `(params, body) = (4, 12)`
  shape.

0 sorries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20QRCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy ctTransTy_sword)
open CatCrypt.Crypto.Jasmin.ChaCha20QR

/-! ## 1. The dialect word type and the input context

The quarter-round operates on four 32-bit words `(a, b, c, d)`. The input context
is `[sword 32, sword 32, sword 32, sword 32]`; the input valuation
`a :: b :: c :: d :: ∅` binds `a` to de Bruijn `here`, `b` to `there here`, etc. -/

/-- The 32-bit machine-word dialect type. -/
abbrev T32 : CryptoTy := .sword 32

/-! ## 2. The 12 straight-line ops

Each op is built at its own De Bruijn context (the context grows by one binding
per op, at the front). The expressions are declared individually because the
dialect's `Expr` structure-literal does not parse inline inside a deeply nested
`Com.var` chain. -/

/-- `a1 = a + b`. Ctx `[a,b,c,d]`; `a = here`, `b = there here`. -/
abbrev x1 : Expr catCryptDialect [T32,T32,T32,T32] T32 :=
  { op := .bvAdd 32, retTy_eq := rfl,
    args := HVector.cons .here (HVector.cons (.there .here) HVector.nil) }

/-- `d1 = d ^ a1`. Ctx `[a1,a,b,c,d]`; `d = there⁴ here`, `a1 = here`. -/
abbrev x2 : Expr catCryptDialect [T32,T32,T32,T32,T32] T32 :=
  { op := .bvXor 32, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there .here)))) (HVector.cons .here HVector.nil) }

/-- `d2 = ror d1 16` (= `d1 <<< 16`). Ctx `[d1,a1,a,b,c,d]`; `d1 = here`. -/
abbrev x3 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvRor 32 16, retTy_eq := rfl,
    args := HVector.cons .here HVector.nil }

/-- `c1 = c + d2`. Ctx `[d2,d1,a1,a,b,c,d]`; `c = there⁵ here`, `d2 = here`. -/
abbrev x4 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvAdd 32, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there .here))))) (HVector.cons .here HVector.nil) }

/-- `b1 = b ^ c1`. Ctx `[c1,d2,d1,a1,a,b,c,d]`; `b = there⁵ here`, `c1 = here`. -/
abbrev x5 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvXor 32, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there .here))))) (HVector.cons .here HVector.nil) }

/-- `b2 = ror b1 20` (= `b1 <<< 12`). Ctx `[b1,c1,d2,d1,a1,a,b,c,d]`; `b1 = here`. -/
abbrev x6 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvRor 32 20, retTy_eq := rfl,
    args := HVector.cons .here HVector.nil }

/-- `a2 = a1 + b2`. Ctx `[b2,b1,c1,d2,d1,a1,a,b,c,d]`; `a1 = there⁵ here`, `b2 = here`. -/
abbrev x7 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvAdd 32, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there .here))))) (HVector.cons .here HVector.nil) }

/-- `d3 = d2 ^ a2`. Ctx `[a2,b2,b1,c1,d2,d1,a1,a,b,c,d]`; `d2 = there⁴ here`, `a2 = here`. -/
abbrev x8 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvXor 32, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there .here)))) (HVector.cons .here HVector.nil) }

/-- `d4 = ror d3 24` (= `d3 <<< 8`). Ctx `[d3,a2,b2,b1,c1,d2,d1,a1,a,b,c,d]`; `d3 = here`. -/
abbrev x9 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvRor 32 24, retTy_eq := rfl,
    args := HVector.cons .here HVector.nil }

/-- `c2 = c1 + d4`. Ctx `[d4,d3,a2,b2,b1,c1,…]`; `c1 = there⁵ here`, `d4 = here`. -/
abbrev x10 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvAdd 32, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there .here))))) (HVector.cons .here HVector.nil) }

/-- `b3 = b2 ^ c2`. Ctx `[c2,d4,d3,a2,b2,…]`; `b2 = there⁴ here`, `c2 = here`. -/
abbrev x11 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvXor 32, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there .here)))) (HVector.cons .here HVector.nil) }

/-- `b4 = ror b3 25` (= `b3 <<< 7`). Ctx `[b3,c2,d4,d3,a2,…]`; `b3 = here`. -/
abbrev x12 : Expr catCryptDialect [T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32] T32 :=
  { op := .bvRor 32 25, retTy_eq := rfl,
    args := HVector.cons .here HVector.nil }

/-! ## 3. The four output programs

After the 12-op block the context head order is
`[b4,b3,c2,d4,d3,a2,b2,b1,c1,d2,d1,a1,a,b,c,d]`, so the RFC outputs are
`a2 = there⁵ here`, `b4 = here`, `c2 = there² here`, `d4 = there³ here`. The four
`Com` programs share the same 12-op block and differ only in the return variable.
-/

/-- The shared 12-op straight-line block, abstracted over the return variable
    (a `Var` of the final 16-binding context). -/
abbrev qrBlock
    (ret : Ctxt.Var (d := catCryptDialect)
      [T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32,T32] T32) :
    Com catCryptDialect [T32,T32,T32,T32] T32 :=
  Com.var x1 (Com.var x2 (Com.var x3 (Com.var x4 (Com.var x5 (Com.var x6
    (Com.var x7 (Com.var x8 (Com.var x9 (Com.var x10 (Com.var x11 (Com.var x12
      (Com.ret ret))))))))))))

/-- The `a` output (`a2`): RFC `(quarterRound a b c d).1`. -/
abbrev chacha20QRCatCryptA : Com catCryptDialect [T32,T32,T32,T32] T32 :=
  qrBlock (.there (.there (.there (.there (.there .here)))))

/-- The `b` output (`b4`): RFC `(quarterRound a b c d).2.1`. -/
abbrev chacha20QRCatCryptB : Com catCryptDialect [T32,T32,T32,T32] T32 :=
  qrBlock .here

/-- The `c` output (`c2`): RFC `(quarterRound a b c d).2.2.1`. -/
abbrev chacha20QRCatCryptC : Com catCryptDialect [T32,T32,T32,T32] T32 :=
  qrBlock (.there (.there .here))

/-- The `d` output (`d4`): RFC `(quarterRound a b c d).2.2.2`. -/
abbrev chacha20QRCatCryptD : Com catCryptDialect [T32,T32,T32,T32] T32 :=
  qrBlock (.there (.there (.there .here)))

/-! ## 4. `denote = spec` for the catCrypt programs

Each equation is closed by the `Chacha20DwordCom`/`OwnedKeccak…Com` peel
pattern: (1) `rw [program, qrBlock]` exposes the 12-op `Com.var` chain; (2) `rw` by
the per-op `rfl` step lemmas `denote_var_bvAdd`/`bvXor`/`bvRor` (each peels one
binding to `body.denote (V.extend (op …))`, the op a waist function
`qrAddW`/`qrXorW`/`qrRorW` returning `BitVec 32`); (3) `simp only [Com.denote,
lookup_here_extend, lookup_there_extend]` resolves the peeled bindings' de-Bruijn
lookups; (4) `rw [quarterRound]` and `simp only [waist defs, rotL32_to_ror_*]`
rewrite the spec's `rotL32` to `rotateRight` (`16/12/8/7 ↦ ror 16/20/24/25`, each
lemma a small standalone `bv_decide`), making the two sides structurally identical;
(5) a final `rfl` resolves the four input-register lookups into `inV`. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ### Waist functions and single-binding peel step lemmas (each `rfl`)

The catCrypt-dialect analogues of `Chacha20DwordCom.zmmPackD`/
`denote_var_vpackZMMd`. The waist functions return `BitVec 32` (= `⟦sword 32⟧`), so
`Ctxt.Valuation.extend` infers the bound type and the step lemmas elaborate. -/

/-- `bvAdd` waist: the dialect add denotation. -/
def qrAddW (a b : BitVec 32) : BitVec 32 := a + b
/-- `bvXor` waist. -/
def qrXorW (a b : BitVec 32) : BitVec 32 := a ^^^ b
/-- `bvRor` waist (rotate-right by the immediate `n`). -/
def qrRorW (n : Nat) (a : BitVec 32) : BitVec 32 := a.rotateRight n

/-- Peel one `bvAdd 32` binding. -/
theorem denote_var_bvAdd {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 32))
    (body : Com catCryptDialect (CryptoTy.sword 32 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvAdd 32) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (qrAddW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvXor 32` binding. -/
theorem denote_var_bvXor {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 32))
    (body : Com catCryptDialect (CryptoTy.sword 32 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvXor 32) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (qrXorW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvRor 32 n` binding. -/
theorem denote_var_bvRor {Γ : Ctxt catCryptDialect} {n : Nat} {s : CryptoTy}
    (va : Ctxt.Var Γ (CryptoTy.sword 32))
    (body : Com catCryptDialect (CryptoTy.sword 32 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvRor 32 n) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (qrRorW n (va.lookup V))) := rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head. -/
@[simp] theorem lookup_here_extend {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

/-- `Ctxt.Var.here.lookup` on a cons valuation reads the head (cons form, after
    `Ctxt.Valuation.extend` is unfolded to `HVector.cons`). -/
@[simp] theorem lookup_here_cons {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (HVector.cons v V) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on a cons valuation skips the head. -/
@[simp] theorem lookup_there_cons {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (HVector.cons v V) = w.lookup V := rfl

/-- `rotL32 x 16 = x.rotateRight 16` (RFC `d <<< 16`). -/
theorem rotL32_to_ror_16 (x : BitVec 32) : rotL32 x 16 = x.rotateRight 16 := by
  simp only [rotL32]; bv_decide

/-- `rotL32 x 12 = x.rotateRight 20` (RFC `b <<< 12`). -/
theorem rotL32_to_ror_12 (x : BitVec 32) : rotL32 x 12 = x.rotateRight 20 := by
  simp only [rotL32]; bv_decide

/-- `rotL32 x 8 = x.rotateRight 24` (RFC `d <<< 8`). -/
theorem rotL32_to_ror_8 (x : BitVec 32) : rotL32 x 8 = x.rotateRight 24 := by
  simp only [rotL32]; bv_decide

/-- `rotL32 x 7 = x.rotateRight 25` (RFC `b <<< 7`). -/
theorem rotL32_to_ror_7 (x : BitVec 32) : rotL32 x 7 = x.rotateRight 25 := by
  simp only [rotL32]; bv_decide

/-- The valuation `a :: b :: c :: d :: ∅`. -/
abbrev inV (a b c d : BitVec 32) :
    Ctxt.Valuation (d := catCryptDialect) [T32,T32,T32,T32] :=
  HVector.cons a (HVector.cons b (HVector.cons c (HVector.cons d HVector.nil)))

/-- The 12-binding peel + lookup-resolve + rotate-rewrite closer, shared by the four
    output proofs. The `rw` peels each binding; the first `simp` resolves the peeled
    bindings' lookups; `rw [quarterRound]` + the second `simp` rewrite `rotL32` to
    `rotateRight` and resolve the input-variable lookups. -/
macro "qr_denote_close" : tactic =>
  `(tactic|
    (rw [qrBlock,
       denote_var_bvAdd, denote_var_bvXor, denote_var_bvRor,
       denote_var_bvAdd, denote_var_bvXor, denote_var_bvRor,
       denote_var_bvAdd, denote_var_bvXor, denote_var_bvRor,
       denote_var_bvAdd, denote_var_bvXor, denote_var_bvRor];
     simp only [Com.denote, lookup_here_extend, lookup_there_extend];
     rw [quarterRound];
     simp only [qrAddW, qrXorW, qrRorW, rotL32_to_ror_16, rotL32_to_ror_12,
       rotL32_to_ror_8, rotL32_to_ror_7];
     rfl))

/-- **`a` output.** The catCrypt quarter-round program denotes to the RFC-8439
    `quarterRound` first component. -/
theorem chacha20QR_catcrypt_denoteA (a b c d : BitVec 32) :
    chacha20QRCatCryptA.denote (inV a b c d) = (quarterRound a b c d).1 := by
  rw [chacha20QRCatCryptA]; qr_denote_close

/-- **`b` output.** -/
theorem chacha20QR_catcrypt_denoteB (a b c d : BitVec 32) :
    chacha20QRCatCryptB.denote (inV a b c d) = (quarterRound a b c d).2.1 := by
  rw [chacha20QRCatCryptB]; qr_denote_close

/-- **`c` output.** -/
theorem chacha20QR_catcrypt_denoteC (a b c d : BitVec 32) :
    chacha20QRCatCryptC.denote (inV a b c d) = (quarterRound a b c d).2.2.1 := by
  rw [chacha20QRCatCryptC]; qr_denote_close

/-- **`d` output.** -/
theorem chacha20QR_catcrypt_denoteD (a b c d : BitVec 32) :
    chacha20QRCatCryptD.denote (inV a b c d) = (quarterRound a b c d).2.2.2 := by
  rw [chacha20QRCatCryptD]; qr_denote_close

/-! ## 5. Lowering through the `catCryptDialect → jasminDialect` seam

`cryptoDialectToJasminCom` lowers each program: every op (`bvAdd`/`bvXor`/`bvRor`)
is in the seam's covered fragment, so the lowering returns `some`. -/

/-- The seam lowers the `a`-output program. -/
theorem chacha20QR_jasmin_isSomeA :
    (cryptoDialectToJasminCom chacha20QRCatCryptA).isSome := by native_decide

/-- The seam lowers the `b`-output program. -/
theorem chacha20QR_jasmin_isSomeB :
    (cryptoDialectToJasminCom chacha20QRCatCryptB).isSome := by native_decide

/-- The seam lowers the `c`-output program. -/
theorem chacha20QR_jasmin_isSomeC :
    (cryptoDialectToJasminCom chacha20QRCatCryptC).isSome := by native_decide

/-- The seam lowers the `d`-output program. -/
theorem chacha20QR_jasmin_isSomeD :
    (cryptoDialectToJasminCom chacha20QRCatCryptD).isSome := by native_decide

/-- The lowered jasmin `Com` for the `a` output. -/
def chacha20QRJasminA : Com jasminDialect (mapCtx [T32,T32,T32,T32]) (mapTy T32) :=
  (cryptoDialectToJasminCom chacha20QRCatCryptA).get chacha20QR_jasmin_isSomeA

/-- The lowered jasmin `Com` for the `b` output. -/
def chacha20QRJasminB : Com jasminDialect (mapCtx [T32,T32,T32,T32]) (mapTy T32) :=
  (cryptoDialectToJasminCom chacha20QRCatCryptB).get chacha20QR_jasmin_isSomeB

/-- The lowered jasmin `Com` for the `c` output. -/
def chacha20QRJasminC : Com jasminDialect (mapCtx [T32,T32,T32,T32]) (mapTy T32) :=
  (cryptoDialectToJasminCom chacha20QRCatCryptC).get chacha20QR_jasmin_isSomeC

/-- The lowered jasmin `Com` for the `d` output. -/
def chacha20QRJasminD : Com jasminDialect (mapCtx [T32,T32,T32,T32]) (mapTy T32) :=
  (cryptoDialectToJasminCom chacha20QRCatCryptD).get chacha20QR_jasmin_isSomeD

/-! ## 6. `denote = spec` for the lowered jasmin programs (via the seam)

The seam's denote-preservation `cryptoDialectToJasminCom_denote_eq'` states the
lowered jasmin denote equals `ctTransTy` of the catCrypt denote; on a `sword 32`
value `ctTransTy` is the identity. Composing with the catCrypt `denote = spec`
gives the jasmin `denote = spec`. -/

/-- **`a` output, lowered.** The jasmin program produced by the seam denotes to
    the RFC-8439 `quarterRound` first component. -/
theorem chacha20QR_jasmin_denoteA (a b c d : BitVec 32) :
    chacha20QRJasminA.denote (ctMapValD (inV a b c d)) = (quarterRound a b c d).1 := by
  have h := cryptoDialectToJasminCom_denote_eq' chacha20QRCatCryptA (inV a b c d)
    chacha20QRJasminA (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T32) _ = _
  rw [ctTransTy_sword (w := 32)]
  exact chacha20QR_catcrypt_denoteA a b c d

/-- **`b` output, lowered.** -/
theorem chacha20QR_jasmin_denoteB (a b c d : BitVec 32) :
    chacha20QRJasminB.denote (ctMapValD (inV a b c d)) = (quarterRound a b c d).2.1 := by
  have h := cryptoDialectToJasminCom_denote_eq' chacha20QRCatCryptB (inV a b c d)
    chacha20QRJasminB (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T32) _ = _
  rw [ctTransTy_sword (w := 32)]
  exact chacha20QR_catcrypt_denoteB a b c d

/-- **`c` output, lowered.** -/
theorem chacha20QR_jasmin_denoteC (a b c d : BitVec 32) :
    chacha20QRJasminC.denote (ctMapValD (inV a b c d)) = (quarterRound a b c d).2.2.1 := by
  have h := cryptoDialectToJasminCom_denote_eq' chacha20QRCatCryptC (inV a b c d)
    chacha20QRJasminC (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T32) _ = _
  rw [ctTransTy_sword (w := 32)]
  exact chacha20QR_catcrypt_denoteC a b c d

/-- **`d` output, lowered.** -/
theorem chacha20QR_jasmin_denoteD (a b c d : BitVec 32) :
    chacha20QRJasminD.denote (ctMapValD (inV a b c d)) = (quarterRound a b c d).2.2.2 := by
  have h := cryptoDialectToJasminCom_denote_eq' chacha20QRCatCryptD (inV a b c d)
    chacha20QRJasminD (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T32) _ = _
  rw [ctTransTy_sword (w := 32)]
  exact chacha20QR_catcrypt_denoteD a b c d

/-! ## 7. Emit: the lowered jasmin program reaches `.jazz`/x86

`JasminPrint.emitJazz` lowers the jasmin `Com` to `.jazz` text through the
existing AST printer (the same path the bench emit uses). The render smoke pins
that the quarter-round's rotate and arithmetic ops survive to the printer. -/

/-- The `.jazz` text of the lowered `a`-output quarter-round. -/
def chacha20QRJazzA : String := JasminPrint.emitJazz "chacha20_qr_a" chacha20QRJasminA

/- **Render smoke: the rotate survives.** The emitted `.jazz` names the native
    scalar right-rotate asm op (`#ROR_32`) — the diagonal rotate of the
    quarter-round reaches the x86 printer through the whole
    `Com catCryptDialect → Com jasminDialect → .jazz` chain (the `bvRor` op lowered
    to jasmin `rorImm`, which the printer renders as `#ROR_32`). -/
#guard (JasminPrint.strContains chacha20QRJazzA "ROR")

/- **Render smoke: the add survives.** -/
#guard (JasminPrint.strContains chacha20QRJazzA "+")

/- **Render smoke: the xor survives.** -/
#guard (JasminPrint.strContains chacha20QRJazzA "^")

/-- **Shape: four `reg 32` inputs and 12 body instructions** — the same
    parameter/op count the catCrypt block carries (12 ops, no spilled binds),
    confirming the whole quarter-round block lands in the jasmin function. -/
theorem chacha20QRJasminA_shape :
    ((JasminPrint.lowerComToProg "chacha20_qr_a" chacha20QRJasminA).funcs.head?.map
      (fun fd => (fd.params.length, fd.body.length))) = some (4, 12) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20QRCatCryptEmit
