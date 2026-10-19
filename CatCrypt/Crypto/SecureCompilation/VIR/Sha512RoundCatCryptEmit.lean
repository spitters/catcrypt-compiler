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
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512Tie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512Tie
public meta import CatCrypt.Crypto.Util.Sha512Verified
public import CatCrypt.Crypto.Util.Sha512Verified

/-!
# SHA-512 compression-round components as a `catCryptDialect → jasmin → x86` path

The FIPS 180-4 §6.4 SHA-512 compression round is a *benchmarked* word primitive
(HACL*-class; the THIR / owned-emit pipelines emit it at `bench/sha2_compare/`).
This file is the **width-64** companion to `Sha256RoundCatCryptEmit.lean`: it
builds the four SHA-512 round-component logical functions — `Σ₀`, `Σ₁`, `Ch`,
`Maj` (FIPS 180-4 §4.1.3) — *natively* as straight-line `Com catCryptDialect`
programs over the dialect's 64-bit word ops (`bvRor`/`bvXor`/`bvAnd`/`andn`),
proves each denotes to the matching `BitVec 64`-native FIPS reference in
`CatCrypt.Util.Sha512Verified`, and lowers each through the committed
`catCryptDialect → jasminDialect` seam
(`DialectToJasminCom.cryptoDialectToJasminCom`), composing the seam's
denote-preservation
(`DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`) so the *lowered
jasmin program* denotes to the same FIPS reference. The lowered jasmin `Com` then
prints to `.jazz` through the single Jasmin printer (`JasminPrintText.emitJazzN`:
`nfToJasmin` followed by the checked printer).

```
FIPS 180-4 §4.1.3  Σ₀/Σ₁/Ch/Maj  (CatCrypt.Util.Sha512Verified.*, the spec)
        ▲                              ▲
        │ denote = spec                │ denote = spec  (via the seam)
   Com catCryptDialect ──cryptoDialectToJasminCom──▶ Com jasminDialect ──emitJazz──▶ .jazz/x86
```

## The op fragment used (SHA-512 §4.1.3 amounts)

* `Σ₀(a) = rotr a 28 ^ rotr a 34 ^ rotr a 39` and
  `Σ₁(e) = rotr e 14 ^ rotr e 18 ^ rotr e 41` use only `bvRor` (rotate-right by an
  immediate, the seam-lowering rotate ↦ jasmin `rorImm`) and `bvXor`. The FIPS
  reference `Sha512Verified.rotr` is the shift-or form
  `(x >>> n) ||| (x <<< (64 - n))`; for `n < 64` it equals `BitVec.rotateRight n`
  (`CompileFromHaxSha512Tie.rotateRight_eq_rotr`), the `bvRor` denotation.
* `Ch(e,f,g) = (e & f) ^ (¬e & g)`. The `¬e & g` is exactly the BMI1 `andn` idiom,
  so `Ch` is one `bvAnd`, one `andn`, one `bvXor` — no separate `bvNot`.
* `Maj(a,b,c) = (a & b) ^ (a & c) ^ (b & c)` is three `bvAnd` and two `bvXor`.

Together these are the **full T1/T2 round update** internals: the verified
single-round body `Sha512Verified.sha512RoundVerified` is
`t1 = h + Σ₁ e + Ch e f g + k + w`, `t2 = Σ₀ a + Maj a b c`, and the new
working words are `(t1+t2, a, b, c, d+t1, e, f, g)`. Σ₀/Σ₁/Ch/Maj are the
non-trivial word-mixing pieces; the surrounding additions are dialect `bvAdd`.

## Deliverables

* `sha512Sigma0Cat`, `sha512Sigma1Cat`, `sha512ChCat`, `sha512MajCat` — the four
  round-component logical functions as native `Com catCryptDialect` programs.
* `sha512_*_catcrypt_denote` — each catCrypt program denotes to the matching
  `Sha512Verified.{bigSigma0,bigSigma1,ch,maj}`.
* `sha512_*_jasmin_isSome` / `sha512*Jasmin` / `sha512_*_jasmin_denote` — the seam
  lowers each program (`cryptoDialectToJasminCom` returns `some`), and the lowered
  *jasmin* `Com` denotes to the same FIPS reference, by composing the catCrypt
  denote with `cryptoDialectToJasminCom_denote_eq'`.
* `sha512Sigma0Jazz`, `sha512ChJazz` — the `.jazz` texts of the lowered `Σ₀` and `Ch`
  programs printed by `JasminPrintText.emitJazzN`; a returned text parses to the unit
  `nfToJasmin` returns (`JasminPrintText.emitJazzN_parse`). Checks pin that the texts
  exist and carry `#ROR_64` and `^`, and the parameter and instruction counts of the
  lowered `Σ₀` function.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha512RoundCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy ctTransTy_sword)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha512Tie (rotateRight_eq_rotr)

/-! ## 1. The dialect word type. -/

/-- The 64-bit machine-word dialect type. -/
abbrev T64 : CryptoTy := .sword 64

/-! ## 2. Waist functions and single-binding peel step lemmas (each `rfl`)

The catCrypt-dialect analogues of the ChaCha QR file's `denote_var_*` lemmas: each
peels one `Com.var` binding to `body.denote (V.extend (op …))` where the op is a
waist function returning `BitVec 64`. -/

/-- `bvXor` waist: the dialect xor denotation. -/
def shXorW (a b : BitVec 64) : BitVec 64 := a ^^^ b
/-- `bvAnd` waist. -/
def shAndW (a b : BitVec 64) : BitVec 64 := a &&& b
/-- `andn` waist: `(~~~a) &&& b` (the BMI1 idiom, `¬a ∧ b`). -/
def shAndnW (a b : BitVec 64) : BitVec 64 := (~~~a) &&& b
/-- `bvRor` waist (rotate-right by the immediate `n`). -/
def shRorW (n : Nat) (a : BitVec 64) : BitVec 64 := a.rotateRight n

/-- Peel one `bvXor 64` binding. -/
theorem denote_var_bvXor {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (shXorW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvAnd 64` binding. -/
theorem denote_var_bvAnd {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvAnd 64) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (shAndW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `andn 64` binding. -/
theorem denote_var_andn {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.andn 64) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (shAndnW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvRor 64 n` binding. -/
theorem denote_var_bvRor {Γ : Ctxt catCryptDialect} {n : Nat} {s : CryptoTy}
    (va : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvRor 64 n) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (shRorW n (va.lookup V))) := rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head. -/
@[simp] theorem lookup_here_extend {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

/-- `Ctxt.Var.here.lookup` on a cons valuation reads the head — resolves the
    input-register lookups (`inV1`/`inV3` are `HVector.cons`, not `extend`). -/
@[simp] theorem lookup_here_cons {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (HVector.cons v V) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on a cons valuation skips the head. -/
@[simp] theorem lookup_there_cons {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (HVector.cons v V) = w.lookup V := rfl

/-! ## 3. The `Σ₀` / `Σ₁` programs (input `[a]`; only `bvRor` + `bvXor`)

The σ-functions read a single 64-bit word and compute three right-rotates XORed
together. The input context is `[T64]` (the word `a` at de Bruijn `here`). The
three rotates are emitted first (each reads `a`, skipping the already-bound
rotates), then two XORs combine them. -/

/-- `Σ₀` over `catCryptDialect`: `rotr a 28 ^ rotr a 34 ^ rotr a 39` (FIPS amounts
    `28/34/39`). Input context `[a]`. -/
def sha512Sigma0Cat : Com catCryptDialect [T64] T64 :=
  -- r28 = ror a 28;  ctx [a]
  Com.var (Expr.mk (CatCryptOp.bvRor 64 28) rfl (.cons .here .nil))
  -- r34 = ror a 34;  ctx [r28,a],  a = there here
  (Com.var (Expr.mk (CatCryptOp.bvRor 64 34) rfl (.cons (.there .here) .nil))
  -- r39 = ror a 39;  ctx [r34,r28,a],  a = there (there here)
  (Com.var (Expr.mk (CatCryptOp.bvRor 64 39) rfl (.cons (.there (.there .here)) .nil))
  -- t = r28 ^ r34;  ctx [r39,r34,r28,a],  r28 = there (there here),  r34 = there here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- out = t ^ r39;  ctx [t,r39,r34,r28,a],  t = here,  r39 = there here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (Com.ret .here)))))

/-- `Σ₁` over `catCryptDialect`: `rotr e 14 ^ rotr e 18 ^ rotr e 41` (FIPS amounts
    `14/18/41`). Input context `[e]`. -/
def sha512Sigma1Cat : Com catCryptDialect [T64] T64 :=
  Com.var (Expr.mk (CatCryptOp.bvRor 64 14) rfl (.cons .here .nil))
  (Com.var (Expr.mk (CatCryptOp.bvRor 64 18) rfl (.cons (.there .here) .nil))
  (Com.var (Expr.mk (CatCryptOp.bvRor 64 41) rfl (.cons (.there (.there .here)) .nil))
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (Com.ret .here)))))

/-! ## 4. The `Ch` program (input `[e,f,g]`; `bvAnd`, `andn`, `bvXor`)

`Ch e f g = (e & f) ^ (¬e & g)`. The `¬e & g` is the BMI1 `andn` idiom, one op. -/

/-- `Ch` over `catCryptDialect`: `(e & f) ^ ((¬e) & g)`. Input context `[e,f,g]`. -/
def sha512ChCat : Com catCryptDialect [T64,T64,T64] T64 :=
  -- p = e & f;  ctx [e,f,g],  e = here,  f = there here
  Com.var (Expr.mk (CatCryptOp.bvAnd 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- q = andn e g  (= ¬e & g);  ctx [p,e,f,g],  e = there here,  g = there³ here
  (Com.var (Expr.mk (CatCryptOp.andn 64) rfl
      (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))
  -- out = p ^ q;  ctx [q,p,e,f,g],  q = here,  p = there here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (Com.ret .here)))

/-! ## 5. The `Maj` program (input `[a,b,c]`; three `bvAnd`, two `bvXor`)

`Maj a b c = (a & b) ^ (a & c) ^ (b & c)`. -/

/-- `Maj` over `catCryptDialect`: `(a & b) ^ (a & c) ^ (b & c)`. Input context
    `[a,b,c]`. -/
def sha512MajCat : Com catCryptDialect [T64,T64,T64] T64 :=
  -- ab = a & b;  ctx [a,b,c],  a = here,  b = there here
  Com.var (Expr.mk (CatCryptOp.bvAnd 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- ac = a & c;  ctx [ab,a,b,c],  a = there here,  c = there³ here
  (Com.var (Expr.mk (CatCryptOp.bvAnd 64) rfl
      (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))
  -- bc = b & c;  ctx [ac,ab,a,b,c],  b = there³ here,  c = there⁴ here
  (Com.var (Expr.mk (CatCryptOp.bvAnd 64) rfl
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- t = ab ^ ac;  ctx [bc,ac,ab,a,b,c],  ab = there² here,  ac = there here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- out = t ^ bc;  ctx [t,bc,ac,ab,a,b,c],  t = here,  bc = there here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (Com.ret .here)))))

/-! ## 6. `denote = spec` against the FIPS-180-4 references

Each proof: (1) `simp only [program]` exposes the `Com.var` chain; (2) `rw` by the
per-op `rfl` step lemmas peels each binding; (3) `simp only [Com.denote, lookup_*]`
resolves the peeled lookups; (4) unfold the `Sha512Verified` spec and the waist
functions and rewrite `rotateRight` to the spec's `rotr` (`rotateRight_eq_rotr`).
`Ch`/`Maj` close by `rfl` after the waist unfolds; `Σ₀/Σ₁` need the rotate bridge. -/

set_option maxHeartbeats 1000000

/-- The single-word input valuation `a :: ∅`. -/
abbrev inV1 (a : BitVec 64) : Ctxt.Valuation (d := catCryptDialect) [T64] :=
  HVector.cons a HVector.nil

/-- The three-word input valuation `x :: y :: z :: ∅`. -/
abbrev inV3 (x y z : BitVec 64) :
    Ctxt.Valuation (d := catCryptDialect) [T64,T64,T64] :=
  HVector.cons x (HVector.cons y (HVector.cons z HVector.nil))

/-- **`Σ₀`.** The catCrypt program denotes to the FIPS reference
    `Sha512Verified.bigSigma0`. -/
theorem sha512_sigma0_catcrypt_denote (a : BitVec 64) :
    sha512Sigma0Cat.denote (inV1 a) = CatCrypt.Util.Sha512Verified.bigSigma0 a := by
  simp only [sha512Sigma0Cat]
  rw [denote_var_bvRor, denote_var_bvRor, denote_var_bvRor, denote_var_bvXor,
    denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend, lookup_here_cons, shRorW, shXorW]
  rw [CatCrypt.Util.Sha512Verified.bigSigma0,
    rotateRight_eq_rotr a (n := 28) (by omega),
    rotateRight_eq_rotr a (n := 34) (by omega),
    rotateRight_eq_rotr a (n := 39) (by omega)]

/-- **`Σ₁`.** The catCrypt program denotes to the FIPS reference
    `Sha512Verified.bigSigma1`. -/
theorem sha512_sigma1_catcrypt_denote (e : BitVec 64) :
    sha512Sigma1Cat.denote (inV1 e) = CatCrypt.Util.Sha512Verified.bigSigma1 e := by
  simp only [sha512Sigma1Cat]
  rw [denote_var_bvRor, denote_var_bvRor, denote_var_bvRor, denote_var_bvXor,
    denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend, lookup_here_cons, shRorW, shXorW]
  rw [CatCrypt.Util.Sha512Verified.bigSigma1,
    rotateRight_eq_rotr e (n := 14) (by omega),
    rotateRight_eq_rotr e (n := 18) (by omega),
    rotateRight_eq_rotr e (n := 41) (by omega)]

/-- **`Ch`.** The catCrypt program denotes to the FIPS reference
    `Sha512Verified.ch` (`(e & f) ^ (¬e & g)`). -/
theorem sha512_ch_catcrypt_denote (e f g : BitVec 64) :
    sha512ChCat.denote (inV3 e f g) = CatCrypt.Util.Sha512Verified.ch e f g := by
  simp only [sha512ChCat]
  rw [denote_var_bvAnd, denote_var_andn, denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend, lookup_here_cons, lookup_there_cons, shAndW, shAndnW,
    shXorW]
  rfl

/-- **`Maj`.** The catCrypt program denotes to the FIPS reference
    `Sha512Verified.maj` (`(a & b) ^ (a & c) ^ (b & c)`). -/
theorem sha512_maj_catcrypt_denote (a b c : BitVec 64) :
    sha512MajCat.denote (inV3 a b c) = CatCrypt.Util.Sha512Verified.maj a b c := by
  simp only [sha512MajCat]
  rw [denote_var_bvAnd, denote_var_bvAnd, denote_var_bvAnd, denote_var_bvXor,
    denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend, lookup_here_cons, lookup_there_cons, shAndW, shXorW]
  rfl

/-! ## 7. Lowering through the `catCryptDialect → jasminDialect` seam

`cryptoDialectToJasminCom` lowers each program: every op (`bvRor`/`bvXor`/`bvAnd`/
`andn`) is in the seam's covered fragment, so the lowering returns `some`. -/

/-- The seam lowers the `Σ₀` program. -/
theorem sha512_sigma0_jasmin_isSome :
    (cryptoDialectToJasminCom sha512Sigma0Cat).isSome := by native_decide

/-- The seam lowers the `Σ₁` program. -/
theorem sha512_sigma1_jasmin_isSome :
    (cryptoDialectToJasminCom sha512Sigma1Cat).isSome := by native_decide

/-- The seam lowers the `Ch` program. -/
theorem sha512_ch_jasmin_isSome :
    (cryptoDialectToJasminCom sha512ChCat).isSome := by native_decide

/-- The seam lowers the `Maj` program. -/
theorem sha512_maj_jasmin_isSome :
    (cryptoDialectToJasminCom sha512MajCat).isSome := by native_decide

/-- The lowered jasmin `Com` for `Σ₀`. -/
def sha512Sigma0Jasmin : Com jasminDialect (mapCtx [T64]) (mapTy T64) :=
  (cryptoDialectToJasminCom sha512Sigma0Cat).get sha512_sigma0_jasmin_isSome

/-- The lowered jasmin `Com` for `Σ₁`. -/
def sha512Sigma1Jasmin : Com jasminDialect (mapCtx [T64]) (mapTy T64) :=
  (cryptoDialectToJasminCom sha512Sigma1Cat).get sha512_sigma1_jasmin_isSome

/-- The lowered jasmin `Com` for `Ch`. -/
def sha512ChJasmin : Com jasminDialect (mapCtx [T64,T64,T64]) (mapTy T64) :=
  (cryptoDialectToJasminCom sha512ChCat).get sha512_ch_jasmin_isSome

/-- The lowered jasmin `Com` for `Maj`. -/
def sha512MajJasmin : Com jasminDialect (mapCtx [T64,T64,T64]) (mapTy T64) :=
  (cryptoDialectToJasminCom sha512MajCat).get sha512_maj_jasmin_isSome

/-! ## 8. `denote = spec` for the lowered jasmin programs (via the seam)

The seam's denote-preservation `cryptoDialectToJasminCom_denote_eq'` states the
lowered jasmin denote equals `ctTransTy` of the catCrypt denote; on a `sword 64`
value `ctTransTy` is the identity (`ctTransTy_sword`). Composing with the catCrypt
`denote = spec` gives the jasmin `denote = spec`. -/

/-- **`Σ₀`, lowered.** The jasmin program produced by the seam denotes to the FIPS
    reference `Sha512Verified.bigSigma0`. -/
theorem sha512_sigma0_jasmin_denote (a : BitVec 64) :
    sha512Sigma0Jasmin.denote (ctMapValD (inV1 a))
      = CatCrypt.Util.Sha512Verified.bigSigma0 a := by
  have h := cryptoDialectToJasminCom_denote_eq' sha512Sigma0Cat (inV1 a)
    sha512Sigma0Jasmin (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T64) _ = _
  rw [ctTransTy_sword (w := 64)]
  exact sha512_sigma0_catcrypt_denote a

/-- **`Σ₁`, lowered.** -/
theorem sha512_sigma1_jasmin_denote (e : BitVec 64) :
    sha512Sigma1Jasmin.denote (ctMapValD (inV1 e))
      = CatCrypt.Util.Sha512Verified.bigSigma1 e := by
  have h := cryptoDialectToJasminCom_denote_eq' sha512Sigma1Cat (inV1 e)
    sha512Sigma1Jasmin (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T64) _ = _
  rw [ctTransTy_sword (w := 64)]
  exact sha512_sigma1_catcrypt_denote e

/-- **`Ch`, lowered.** -/
theorem sha512_ch_jasmin_denote (e f g : BitVec 64) :
    sha512ChJasmin.denote (ctMapValD (inV3 e f g))
      = CatCrypt.Util.Sha512Verified.ch e f g := by
  have h := cryptoDialectToJasminCom_denote_eq' sha512ChCat (inV3 e f g)
    sha512ChJasmin (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T64) _ = _
  rw [ctTransTy_sword (w := 64)]
  exact sha512_ch_catcrypt_denote e f g

/-- **`Maj`, lowered.** -/
theorem sha512_maj_jasmin_denote (a b c : BitVec 64) :
    sha512MajJasmin.denote (ctMapValD (inV3 a b c))
      = CatCrypt.Util.Sha512Verified.maj a b c := by
  have h := cryptoDialectToJasminCom_denote_eq' sha512MajCat (inV3 a b c)
    sha512MajJasmin (Option.some_get _).symm
  rw [h]
  show ctTransTy (t := T64) _ = _
  rw [ctTransTy_sword (w := 64)]
  exact sha512_maj_catcrypt_denote a b c

/-! ## 9. Emit: the lowered jasmin programs print to `.jazz`

`JasminPrintText.emitJazzN` lowers a jasmin `Com` with `nfToJasmin` and prints the
unit with the checked printer; a returned text parses back to that unit
(`JasminPrintText.emitJazzN_parse`). -/

open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin (JazzSig ptyOf nfToJasmin)

/-- The signature of a SHA-512 round component over the named words: one `reg u64`
    parameter per word, in the reverse order of the context, and a `reg u64` result. -/
def sha512Sig (xs : List String) : JazzSig (mapCtx (xs.map fun _ => T64)) (mapTy T64) where
  params := xs.reverse.map fun x => (x, .reg, ptyOf (.reg 64))
  result := (.reg, ptyOf (.reg 64))
  resultParam := none
  params_length := by simp [mapCtx]

/-- The `.jazz` text of the lowered `Σ₀` component, symbol `sha512_sigma0`, printed by
    the single Jasmin printer; `none` when `nfToJasmin` or the checked printer
    refuses. -/
def sha512Sigma0Jazz : Option String :=
  JasminPrintText.emitJazzN "sha512_sigma0" (sha512Sig ["a"]) sha512Sigma0Jasmin

-- The `Σ₀` text exists and carries the rotate (`bvRor` lowered to `rorImm`, printed as
-- `#ROR_64`) and the xor.
set_option kat.ms 500 in
#kat sha512Sigma0Jazz.any fun s => s.contains "ROR" && s.contains "^"

-- The lowered `Σ₀` function has one parameter and a body of 11 instructions.
#kat (nfToJasmin (sha512Sig ["a"]) "sha512_sigma0" (NFProg.ofCom sha512Sigma0Jasmin)).any
  fun u => u.fns.map (fun f => (f.fd.params.length, f.fd.body.length)) == [(1, 11)]

/-- The `.jazz` text of the lowered `Ch` component, symbol `sha512_ch`, printed by the
    single Jasmin printer; `none` when `nfToJasmin` or the checked printer refuses. -/
def sha512ChJazz : Option String :=
  JasminPrintText.emitJazzN "sha512_ch" (sha512Sig ["e", "f", "g"]) sha512ChJasmin

-- The `Ch` text exists and carries the xor.
#kat sha512ChJazz.any fun s => s.contains "^"

end CatCrypt.Crypto.SecureCompilation.VIR.Sha512RoundCatCryptEmit
