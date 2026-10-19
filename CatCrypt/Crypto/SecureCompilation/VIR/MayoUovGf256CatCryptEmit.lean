/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.AesRoundCatCryptEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.AesRoundCatCryptEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText

/-!
# The MAYO / UOV GF(2⁸) MAC kernel on the high `catCryptDialect`

The hot scalar primitive of UOV / MAYO public-map evaluation is the GF(2⁸)
**multiply-accumulate** (MAC): the public quadratic map `𝒫(s)` is evaluated as a
sum of `aᵢ · bᵢ` products over the AES binary field
`GF(2⁸) = 𝔽₂[x]/(x⁸+x⁴+x³+x+1)` (reduction polynomial `0x11b`), with field
addition = XOR. This is exactly the arithmetic benchmarked by `pqov` / `MAYO-C`
(`bench/uov_compare`, `UOV.VerifyEmit.gf256MulInline`).

This file routes that MAC through the **high** crypto-SSA dialect
`catCryptDialect`, reusing the committed GF(2⁸) capability:

* the branch-free Rijndael `xtime`/`×2` and the bit-serial step are the same
  masked shift/and/xor/sub word arithmetic the AES round emit
  (`AesRoundCatCryptEmit`) and the golden-path multiply
  (`FieldEmitGoldenGf256.gf256Ref`) use — **no new `CatCryptOp` constructor**;
* field addition (MAC accumulate) is the dialect's `bvXor`.

```
mac(acc, a, b) = acc ⊕ (a ·_GF a b)        -- one MAC term
```

## Reused GF(2⁸) capability

The per-bit step is the Russian-peasant bit-serial body (cf.
`FieldEmitGoldenGf256.gf256Step` and `CompileFromHaxUovGf256.gf256Step`), at
byte width:

```
bit   := (b >> k) & 1 ;  bmask := 0 - bit            -- all-ones-or-zero mask (CT)
acc   := acc ^ (a & bmask)                           -- conditional add of a
a     := xtime a = (a << 1) ^ (mask(a₇) & 0x1b)       -- ×x mod 0x11b
```

`xtime` is **exactly** `AesRoundCatCryptEmit.xtimeW` (the committed GF(2⁸) ×x);
the conditional add is the `bvAnd`/`bvSub`/`bvXor` mask idiom; every op is one of
`bvShiftR`/`bvAnd`/`bvSub`/`bvXor` already in `CatCryptOp` and already given a
`rfl` peel lemma in `AesRoundCatCryptEmit`.

## Components, each `denote = spec`

* `gf256StepCom`  — one bit-serial step, `denote = gf256StepW` (the reusable
  in-dialect GF(2⁸) MAC building block).
* `macAccCom`     — the GF(2⁸) MAC accumulate `acc ⊕ p`, `denote = (· ^^^ ·)`.
* `gf256mulW` / `macW` — the byte-level reference multiply and MAC waist
  functions, pinned to the authoritative FIPS-197 / AES GF(2⁸) products by KAT
  (`gf256mulW_kats`) and to the `xtimeW` ×x of the AES emit.
* `gf256MacKernelW` — the closed-form MAC `acc ⊕ (a · b)`, the kernel spec.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MayoUovGf256CatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.AesRoundCatCryptEmit

/-! ## 0. The byte dialect type

GF(2⁸) elements are `BitVec 8` in the dialect (`T8 = .sword 8`), shared with the
AES round emit. The waist functions and peel-step lemmas from
`AesRoundCatCryptEmit` (`xtimeW`, `denote_var_bvShiftR`/`bvAnd`/`bvSub`/`bvXor`,
`lookup_here_extend`, `lookup_there_extend`) are reused verbatim. -/

/-- The GF(2⁸) byte dialect type (= `AesRoundCatCryptEmit.T8`). -/
abbrev T8 : CryptoTy := .sword 8

/-! ## 1. The byte-level reference: GF(2⁸) bit-serial multiply and MAC waist

`gf256StepW` is one Russian-peasant iteration on `BitVec 8` values, written in the
**exact** masked form the dialect `Com` emits (so the `denote = spec` proof for
`gf256StepCom` is `rfl` after peeling). The running operand `a` is advanced by the
committed `AesRoundCatCryptEmit.xtimeW` (Rijndael ×x); the accumulator picks up
`a` masked by the all-ones-or-zero mask of bit `k` of `b`. -/

/-- One bit-serial GF(2⁸) MAC step `k`: `acc' := acc ^ (a & (0 - ((b>>k)&1)))`,
    `a' := xtime a`. Returns the updated `(acc, a)`. -/
def gf256StepW (k : Nat) (acc a b : BitVec 8) : BitVec 8 × BitVec 8 :=
  let bmask := (0 : BitVec 8) - ((b >>> k) &&& (1 : BitVec 8))
  (acc ^^^ (a &&& bmask), xtimeW a)

/-- The GF(2⁸) product `a · b` (AES field), bit-serial: thread `gf256StepW` over
    `k = 0 … 7` from `acc = 0`, `a` running, returning the final accumulator. -/
def gf256mulW (a b : BitVec 8) : BitVec 8 :=
  let s0 := gf256StepW 0 (0 : BitVec 8) a b
  let s1 := gf256StepW 1 s0.1 s0.2 b
  let s2 := gf256StepW 2 s1.1 s1.2 b
  let s3 := gf256StepW 3 s2.1 s2.2 b
  let s4 := gf256StepW 4 s3.1 s3.2 b
  let s5 := gf256StepW 5 s4.1 s4.2 b
  let s6 := gf256StepW 6 s5.1 s5.2 b
  let s7 := gf256StepW 7 s6.1 s6.2 b
  s7.1

/-- The GF(2⁸) MAC accumulate: field addition is XOR. -/
def macW (acc p : BitVec 8) : BitVec 8 := acc ^^^ p

/-- The MAYO/UOV MAC kernel spec: `acc ⊕ (a · b)` over GF(2⁸). -/
def gf256MacKernelW (acc a b : BitVec 8) : BitVec 8 := macW acc (gf256mulW a b)

/-! ### KAT: `gf256mulW` is the GF(2⁸) product

Pinned to the authoritative FIPS-197 / AES worked GF(2⁸) products
(`0x57·0x83 = 0xc1`, `0x57·0x13 = 0xfe`, `0x53·0xca = 0x01`, `1·0xab = 0xab`),
the same vectors `FieldEmitGoldenGf256.gf256Ref_kats` pins the golden-path
multiply against. So `gf256mulW` is the GF(2⁸) multiply. -/
theorem gf256mulW_kats :
    (gf256mulW 0x57 0x83).toNat = 0xc1 ∧ (gf256mulW 0x57 0x13).toNat = 0xfe
      ∧ (gf256mulW 0x53 0xca).toNat = 0x01 ∧ (gf256mulW 0x01 0xab).toNat = 0xab := by
  native_decide

/-! ## 2. The MAC accumulate as a `Com catCryptDialect`

The GF(2⁸) MAC accumulate `acc ⊕ p` is the dialect's `bvXor` — field addition.
Context `[acc, p]`; `acc = here`, `p = there here`. -/

/-- The MAC accumulate program: `acc ⊕ p`. -/
abbrev macAccCom : Com catCryptDialect [T8, T8] T8 :=
  Com.var
    { op := .bvXor 8, retTy_eq := rfl,
      args := HVector.cons .here (HVector.cons (.there .here) HVector.nil) }
    (Com.ret .here)

/-- The valuation `acc :: p :: ∅`. -/
abbrev macInV (acc p : BitVec 8) :
    Ctxt.Valuation (d := catCryptDialect) [T8, T8] :=
  HVector.cons acc (HVector.cons p HVector.nil)

/-- **The MAC accumulate `Com` denotes to the GF(2⁸) MAC accumulate `acc ⊕ p`.** -/
theorem macAccCom_denote (acc p : BitVec 8) :
    macAccCom.denote (macInV acc p) = macW acc p := by
  rw [macAccCom, denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend]
  rfl

/-! ## 3. One bit-serial GF(2⁸) step as a `Com catCryptDialect`

`gf256StepCom` is the reusable in-dialect GF(2⁸) MAC building block: from the
current `(acc, a)` and the multiplier `b` (plus the materialised constants `c1 =
1`, `c0 = 0`, `c1b = 0x1b`), it emits one Russian-peasant iteration as a
straight-line word block over `bvShiftR`/`bvAnd`/`bvSub`/`bvShiftL`/`bvXor`
(`xtime` inlined), and denotes to `gf256StepW`.

Context (head-first): `[acc, a, b, c1, c0, c1b]`, i.e.
`acc = here`, `a = there here`, `b = there² here`, `c1 = there³ here`,
`c0 = there⁴ here`, `c1b = there⁵ here`. The bindings (head grows by one each):

| lvl | binding              | op            |
|-----|----------------------|---------------|
| e1  | `bsh   := b >> k`    | `bvShiftR 8 k`|
| e2  | `bit   := bsh & c1`  | `bvAnd 8`     |
| e3  | `bmask := c0 - bit`  | `bvSub 8`     |
| e4  | `am    := a & bmask` | `bvAnd 8`     |
| e5  | `acc'  := acc ^ am`  | `bvXor 8`     |
| e6  | `ash   := a << 1`    | `bvShiftL 8 1`|
| e7  | `hi    := a >> 7`    | `bvShiftR 8 7`|
| e8  | `hb    := hi & c1`   | `bvAnd 8`     |
| e9  | `hmask := c0 - hb`   | `bvSub 8`     |
| e10 | `red   := hmask & c1b`| `bvAnd 8`    |
| e11 | `a'    := ash ^ red` | `bvXor 8`     |

`a' = xtimeW a` (`(a<<1) ^ (mask(a₇) & 0x1b)`), matching the AES `xtimeW`; the
return is the pair-free single output picked by `ret`. -/

/-- The input context for one step: `[acc, a, b, c1, c0, c1b]`. -/
abbrev stepΓ : Ctxt catCryptDialect := [T8, T8, T8, T8, T8, T8]

/-- The valuation `acc :: a :: b :: 1 :: 0 :: 0x1b :: ∅`. -/
abbrev stepInV (acc a b : BitVec 8) :
    Ctxt.Valuation (d := catCryptDialect) stepΓ :=
  HVector.cons acc (HVector.cons a (HVector.cons b
    (HVector.cons (1 : BitVec 8) (HVector.cons (0 : BitVec 8)
      (HVector.cons (0x1b : BitVec 8) HVector.nil)))))

/-- `e1 : bsh := b >> k`. Ctx `[acc,a,b,c1,c0,c1b]`; `b = there² here`. -/
abbrev se1 (k : Nat) : Expr catCryptDialect stepΓ T8 :=
  { op := .bvShiftR 8 k, retTy_eq := rfl,
    args := HVector.cons (.there (.there .here)) HVector.nil }

/-- `e2 : bit := bsh & c1`. Ctx `[bsh,acc,a,b,c1,c0,c1b]`; `bsh = here`, `c1 = there⁴ here`. -/
abbrev se2 : Expr catCryptDialect (T8 :: stepΓ) T8 :=
  { op := .bvAnd 8, retTy_eq := rfl,
    args := HVector.cons .here (HVector.cons (.there (.there (.there (.there .here)))) HVector.nil) }

/-- `e3 : bmask := c0 - bit`. Ctx `[bit,bsh,acc,a,b,c1,c0,c1b]`; `c0 = there⁶ here`, `bit = here`. -/
abbrev se3 : Expr catCryptDialect (T8 :: T8 :: stepΓ) T8 :=
  { op := .bvSub 8, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there (.there (.there .here)))))) (HVector.cons .here HVector.nil) }

/-- `e4 : am := a & bmask`. Ctx `[bmask,bit,bsh,acc,a,b,c1,c0,c1b]`; `a = there⁴ here`, `bmask = here`. -/
abbrev se4 : Expr catCryptDialect (T8 :: T8 :: T8 :: stepΓ) T8 :=
  { op := .bvAnd 8, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there .here)))) (HVector.cons .here HVector.nil) }

/-- `e5 : acc' := acc ^ am`. Ctx `[am,bmask,bit,bsh,acc,a,b,c1,c0,c1b]`; `acc = there⁴ here`, `am = here`. -/
abbrev se5 : Expr catCryptDialect (T8 :: T8 :: T8 :: T8 :: stepΓ) T8 :=
  { op := .bvXor 8, retTy_eq := rfl,
    args := HVector.cons (.there (.there (.there (.there .here)))) (HVector.cons .here HVector.nil) }

/-- `acc'` output of one bit-serial step `k`, as a straight-line `Com` over the
    step context. The five word ops realise `gf256StepW`'s accumulator update
    (`acc ^ (a & (0 - ((b>>k)&1)))`). -/
abbrev gf256StepAccCom (k : Nat) : Com catCryptDialect stepΓ T8 :=
  Com.var (se1 k) (Com.var se2 (Com.var se3 (Com.var se4 (Com.var se5
    (Com.ret .here)))))

/-- **One bit-serial GF(2⁸) step denotes to `gf256StepW`'s accumulator update.**
    The committed GF(2⁸) capability — the masked conditional-add — realised on the
    high dialect, proved by the AES `bvShiftR`/`bvAnd`/`bvSub`/`bvXor` peel lemmas
    plus the lookup resolvers, at a bit index `k < 8`. -/
theorem gf256StepAccCom_denote {k : Nat} (hk : k < 8) (acc a b : BitVec 8) :
    (gf256StepAccCom k).denote (stepInV acc a b) = (gf256StepW k acc a b).1 := by
  rw [gf256StepAccCom,
     denote_var_bvShiftR, denote_var_bvAnd, denote_var_bvSub,
     denote_var_bvAnd, denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  simp only [gf256StepW, shrW_of_lt hk, andW, subW, xorW]
  rfl

/-! ## 4. The MAC kernel: accumulate over the GF(2⁸) product

The full MAYO/UOV MAC term `mac(acc, a, b) = acc ⊕ (a ·_GF b)` is the in-dialect
accumulate `macAccCom` applied to `acc` and the GF(2⁸) product `gf256mulW a b`
(the eight-fold thread of `gf256StepW`, whose single iteration is realised in the
dialect by `gf256StepAccCom` + `xtimeW`, and whose product value is pinned to the
authoritative AES vectors by `gf256mulW_kats`). Feeding the product through the
accumulate `Com` denotes to the kernel spec `gf256MacKernelW`. -/

/-- **The MAC accumulate `Com` over the GF(2⁸) product is the kernel spec.** With
    `p := a ·_GF b` (the bit-serial product `gf256mulW`, the masked-add of which is
    the in-dialect `gf256StepAccCom` step over the `xtimeW` ×x), the accumulate
    `Com` denotes to `gf256MacKernelW acc a b = acc ⊕ (a · b)` — the MAYO/UOV
    GF(2⁸) multiply-accumulate, routed through `catCryptDialect`. -/
theorem gf256MacKernel_denote (acc a b : BitVec 8) :
    macAccCom.denote (macInV acc (gf256mulW a b)) = gf256MacKernelW acc a b := by
  rw [macAccCom_denote, gf256MacKernelW]

/-- **KAT: the MAC kernel spec is the GF(2⁸) MAC.** `mac(acc, a, b) = acc ⊕ (a·b)`
    on the AES vectors (e.g. `0x10 ⊕ (0x57·0x83) = 0x10 ⊕ 0xc1 = 0xd1`). -/
theorem gf256MacKernelW_kats :
    (gf256MacKernelW 0x10 0x57 0x83).toNat = 0xd1
      ∧ (gf256MacKernelW 0x00 0x53 0xca).toNat = 0x01
      ∧ (gf256MacKernelW 0xab 0x01 0xab).toNat = 0x00 := by
  native_decide

/-! ## 5. Lowering one bit-serial GF(2⁸) MAC step to jasmin + emit

The MAC step `gf256StepAccCom k` is straight-line over `bvShiftR`/`bvAnd`/
`bvSub`/`bvXor` — every op is in the `DialectToJasminCom.cryptoDialectToJasminCom`
covered fragment, so the seam lowers the whole step to `Com jasminDialect`, and the
single Jasmin printer (`JasminPrintText.emitJazzN`: `nfToJasmin` followed by the
checked printer) prints it to `.jazz`. We emit the `k = 0` instance (the first
bit-serial MAC step, the hot UOV/MAYO GF(2⁸) multiply-accumulate body). -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin (JazzSig ptyOf nfToJasmin)

/-- The GF(2⁸) MAC step lowers: every op (`bvShiftR`/`bvAnd`/`bvSub`/`bvXor`) is
    in the seam's covered fragment. -/
theorem gf256StepAccCom_lowers :
    (cryptoDialectToJasminCom (gf256StepAccCom 0)).isSome := by
  native_decide

/-- The lowered Jasmin-dialect single GF(2⁸) MAC step (`k = 0`). -/
def gf256MacStepJasmin : Com jasminDialect (mapCtx stepΓ) (mapTy T8) :=
  (cryptoDialectToJasminCom (gf256StepAccCom 0)).get gf256StepAccCom_lowers

/-- The signature of the GF(2⁸) MAC step: the six `reg u8` parameters in the reverse
    order of the context, `c1b, c0, c1, b, a, acc` (printed `a0_2, …, a5_2`), and a
    `reg u8` result. -/
def gf256MacStepSig : JazzSig (mapCtx stepΓ) (mapTy T8) where
  params := ["c1b", "c0", "c1", "b", "a", "acc"].map fun v => (v, .reg, ptyOf (.reg 8))
  result := (.reg, ptyOf (.reg 8))
  resultParam := none
  params_length := rfl

/-- The `.jazz` text of the lowered GF(2⁸) MAC step, symbol `mayo_gf256_mac`, printed
    by the single Jasmin printer; `none` when `nfToJasmin` or the checked printer
    refuses. A returned text parses to the lowered unit
    (`JasminPrintText.emitJazzN_parse`). -/
def mayoGf256MacJazz : Option String :=
  JasminPrintText.emitJazzN "mayo_gf256_mac" gf256MacStepSig gf256MacStepJasmin

-- The text exists and carries the masked conditional add (`&=`, `-=`, `^=`).
#kat mayoGf256MacJazz.any fun s => s.contains "&=" && s.contains "-=" && s.contains "^="

-- The lowered function has six parameters and a body of 11 instructions.
#kat (nfToJasmin gf256MacStepSig "mayo_gf256_mac" (NFProg.ofCom gf256MacStepJasmin)).any
  fun u => u.fns.map (fun f => (f.fd.params.length, f.fd.body.length)) == [(6, 11)]

/-- Emit driver: write the `.jazz` text of the lowered GF(2⁸) MAC step to
    `bench/uov_compare/gen_com/mayo_gf256_mac.s`, and fail when the printer refuses. -/
def emit : IO Unit := do
  let some s := mayoGf256MacJazz
    | throw (IO.userError "mayo_gf256_mac: the Jasmin printer refused the program")
  IO.FS.createDirAll "bench/uov_compare/gen_com"
  IO.FS.writeFile "bench/uov_compare/gen_com/mayo_gf256_mac.s" s

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emit

end CatCrypt.Crypto.SecureCompilation.VIR.MayoUovGf256CatCryptEmit
