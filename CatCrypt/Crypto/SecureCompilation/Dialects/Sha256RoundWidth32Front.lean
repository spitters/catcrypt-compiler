/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype


@[expose] public section
set_option autoImplicit false

/-!
# SHA-256 round + message-schedule primitives, front-sourced at width 32

The state-resident SHA-256 compression (`VIR/Sha2Emit.lean`,
`compressCom sha256Spec`, deployed as `sha256_compress_resident(_wp)`) is built
by hand as a `Com jasminDialect` through the `emitOp` / `.regArith` CPS builders.
The front route for it is the width-parametric front leaf
`ScalarSExprWidth32Prototype.lowerSExprW`: every SHA-256
round op is pure `SXor`/`SAnd`/`SShr`/`SShl` + 32-bit `SAdd`, and `rotr32` is the
disjoint-halves shift pair — all inside `lowerSExprW`'s covered alphabet.

This module discharges the **capability gate** for that route: it
expresses every SHA-256 round primitive (`Σ0`, `Σ1`, `Ch`, `Maj`, `σ0`, `σ1`),
one full compression **round step** (`a' = T1+T2`, `e' = d+T1`), and one
**message-schedule step** (`W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`)
as `.sword 32` `SExpr`s, and checks computationally that each

1. lowers (`isSome`) through `lowerSExprW 32` to a `Com catCryptDialect` at
   width 32;
2. lowers on to a `Com jasminDialect` through
   `DialectToJasminCom.cryptoDialectToJasminCom` (reaches the owned x86 backend
   at 32-bit `reg`s);
3. denotes, with 32-bit wrap, to the FIPS 180-4 §6.2 spec on samples
   (including a 32-bit-wrap witness that a 64-bit add would miscompute);
4. `rotr32(x,k) = (x >>> k) ^ (x <<< (32-k))` equals the native
   `BitVec.rotateRight k` for every SHA-256 rotate amount (`bv_decide`,
   universal over all `2^32` inputs).

`rotr` (right rotate, SHA-256) is the mirror of the prototype's `rotl` (left
rotate, ChaCha): the two front-expressible shifted halves occupy disjoint bit
ranges at width 32, so their `^` reassembles the rotate.

**Scope note.** This validates the *front leaf* over the full SHA-256 round
alphabet at width 32. Wiring the deployed `compressCom sha256Spec` body through
the front additionally needs a width-parametric *statement* stepper (the `stepW`
combinator over `RScalarSetExpr`, the w32 twin of the 64-bit
`TranslateDialectDirectControl.translateDialectControl` that FriFold used) so the
~4000 named-intermediate assignments thread through `lowerSExprW 32`; that stepper
is outside this module, which covers the expression leaf.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Sha256RoundWidth32Front

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The SHA-256 round primitives as width-32 `SExpr`s

`rotr32(x,k)` has no `SExpr` constructor; at width 32 it is the disjoint shift
pair `(x >>> k) ^ (x <<< (32-k))`. Everything else is a direct `SExpr` over the
`SXor`/`SAnd`/`SShr`/`SShl`/`SAdd` alphabet `lowerSExprW` covers. `¬x` is
`x ^ 0xFFFFFFFF` (an `SLit` mask), matching the emit's `~x = x ^ allOnes`. -/

/-- `rotr32(x,k) = (x >>> k) ^ (x <<< (32-k))` as an `SExpr` (front-expressible). -/
def sRotr (x : SExpr) (k : Nat) : SExpr :=
  .SXor (.SShr x (.SLit k)) (.SShl x (.SLit (32 - k)))

/-- `Σ0(x) = rotr(x,2) ^ rotr(x,13) ^ rotr(x,22)` (FIPS 180-4 §4.1.2). -/
def sBigSig0 (x : SExpr) : SExpr := .SXor (.SXor (sRotr x 2) (sRotr x 13)) (sRotr x 22)

/-- `Σ1(x) = rotr(x,6) ^ rotr(x,11) ^ rotr(x,25)`. -/
def sBigSig1 (x : SExpr) : SExpr := .SXor (.SXor (sRotr x 6) (sRotr x 11)) (sRotr x 25)

/-- `σ0(x) = rotr(x,7) ^ rotr(x,18) ^ (x >> 3)`. -/
def sSmallSig0 (x : SExpr) : SExpr := .SXor (.SXor (sRotr x 7) (sRotr x 18)) (.SShr x (.SLit 3))

/-- `σ1(x) = rotr(x,17) ^ rotr(x,19) ^ (x >> 10)`. -/
def sSmallSig1 (x : SExpr) : SExpr := .SXor (.SXor (sRotr x 17) (sRotr x 19)) (.SShr x (.SLit 10))

/-- `¬x` at width 32, encoded `x ^ 0xFFFFFFFF` (the emit's `x ^ allOnes`). -/
def sNot (x : SExpr) : SExpr := .SXor x (.SLit 0xFFFFFFFF)

/-- `Ch(e,f,g) = (e & f) ^ (¬e & g)`. -/
def sCh (e f g : SExpr) : SExpr := .SXor (.SAnd e f) (.SAnd (sNot e) g)

/-- `Maj(a,b,c) = (a & b) ^ (a & c) ^ (b & c)`. -/
def sMaj (a b c : SExpr) : SExpr := .SXor (.SXor (.SAnd a b) (.SAnd a c)) (.SAnd b c)

/-! ## 2. Generic width-32 front lowering + denotation (mirror of the prototype) -/

/-- Lower an `SExpr` over a `.sword 32` context `Γ`/`VarMap vm` to the
    `Com catCryptDialect Γ (.sword 32)` returning the result word, through
    `lowerSExprW 32`. -/
def progOf {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) : Option (Com catCryptDialect Γ (.sword 32)) :=
  match ScalarSExprWidth32Prototype.lowerSExprW 32 vm 0 e with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword 32, v⟩ => r.1.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-! ### 2a. One compression round step (FIPS 180-4 §6.2.2)

Inputs: the eight working words `a..h`, the round constant `k`, and the schedule
word `w`. `T1 = h + Σ1(e) + Ch(e,f,g) + k + w`; `T2 = Σ0(a) + Maj(a,b,c)`; the
new head words are `a' = T1 + T2` and `e' = d + T1`. -/

/-- `T1 = h + Σ1(e) + Ch(e,f,g) + k + w`. -/
def sT1 : SExpr :=
  .SAdd (.SAdd (.SAdd (.SAdd (.SVar "h") (sBigSig1 (.SVar "e")))
    (sCh (.SVar "e") (.SVar "f") (.SVar "g"))) (.SVar "k")) (.SVar "w")

/-- `T2 = Σ0(a) + Maj(a,b,c)`. -/
def sT2 : SExpr := .SAdd (sBigSig0 (.SVar "a")) (sMaj (.SVar "a") (.SVar "b") (.SVar "c"))

/-- The new head word `a' = T1 + T2`. -/
def sNewA : SExpr := .SAdd sT1 sT2

/-- The new word `e' = d + T1`. -/
def sNewE : SExpr := .SAdd (.SVar "d") sT1

/-- The round context: ten `.sword 32` slots `a b c d e f g h k w`. -/
def roundΓ : Ctx :=
  [.sword 32, .sword 32, .sword 32, .sword 32, .sword 32,
   .sword 32, .sword 32, .sword 32, .sword 32, .sword 32]

/-- `VarMap` binding `a..h`, `k`, `w` to the ten round slots (`a` = `.here`). -/
def roundVM : VarMap roundΓ :=
  ((((((((((VarMap.empty.bind "w").bind "k").bind "h").bind "g").bind "f").bind "e").bind
      "d").bind "c").bind "b").bind "a")

/-- Denote a round `SExpr` at the ten working inputs. -/
def roundDenote (e : SExpr)
    (av bv cv dv ev fv gv hv kv wv : BitVec 32) : Option (BitVec 32) :=
  (progOf roundVM e).map (fun com =>
    com.denote (.cons av (.cons bv (.cons cv (.cons dv (.cons ev (.cons fv
      (.cons gv (.cons hv (.cons kv (.cons wv .nil)))))))))))

/-! ### 2b. One message-schedule step (FIPS 180-4 §6.2)

`W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`, over the four sliding-window
inputs `w2 = W[t-2]`, `w7 = W[t-7]`, `w15 = W[t-15]`, `w16 = W[t-16]`. -/

/-- `W[t] = σ1(w2) + w7 + σ0(w15) + w16`. -/
def sSchedStep : SExpr :=
  .SAdd (.SAdd (.SAdd (sSmallSig1 (.SVar "w2")) (.SVar "w7")) (sSmallSig0 (.SVar "w15")))
    (.SVar "w16")

/-- The schedule context: four `.sword 32` slots `w2 w7 w15 w16`. -/
def schedΓ : Ctx := [.sword 32, .sword 32, .sword 32, .sword 32]

/-- `VarMap` binding `w2 w7 w15 w16` to the four schedule slots. -/
def schedVM : VarMap schedΓ :=
  ((((VarMap.empty.bind "w16").bind "w15").bind "w7").bind "w2")

/-- Denote the schedule step at the four window inputs. -/
def schedDenote (w2 w7 w15 w16 : BitVec 32) : Option (BitVec 32) :=
  (progOf schedVM sSchedStep).map (fun com =>
    com.denote (.cons w2 (.cons w7 (.cons w15 (.cons w16 .nil)))))

/-! ## 3. The FIPS 180-4 §6.2 reference (native 32-bit rotate) -/

/-- `rotr32` via the native `BitVec.rotateRight`. -/
def rotr (x : BitVec 32) (k : Nat) : BitVec 32 := x.rotateRight k

/-- Reference `Σ0`. -/
def specBigSig0 (x : BitVec 32) : BitVec 32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
/-- Reference `Σ1`. -/
def specBigSig1 (x : BitVec 32) : BitVec 32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
/-- Reference `σ0`. -/
def specSmallSig0 (x : BitVec 32) : BitVec 32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
/-- Reference `σ1`. -/
def specSmallSig1 (x : BitVec 32) : BitVec 32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
/-- Reference `Ch`. -/
def specCh (e f g : BitVec 32) : BitVec 32 := (e &&& f) ^^^ ((~~~e) &&& g)
/-- Reference `Maj`. -/
def specMaj (a b c : BitVec 32) : BitVec 32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- Reference `T1` (`a b c d` unused — kept for a uniform round-arg list). -/
def specT1 (_a _b _c _d e f g h k w : BitVec 32) : BitVec 32 :=
  h + specBigSig1 e + specCh e f g + k + w
/-- Reference `T2`. -/
def specT2 (a b c : BitVec 32) : BitVec 32 := specBigSig0 a + specMaj a b c
/-- Reference new-`a` `= T1 + T2`. -/
def specNewA (a b c d e f g h k w : BitVec 32) : BitVec 32 :=
  specT1 a b c d e f g h k w + specT2 a b c
/-- Reference new-`e` `= d + T1`. -/
def specNewE (a b c d e f g h k w : BitVec 32) : BitVec 32 :=
  d + specT1 a b c d e f g h k w
/-- Reference schedule step. -/
def specSched (w2 w7 w15 w16 : BitVec 32) : BitVec 32 :=
  specSmallSig1 w2 + w7 + specSmallSig0 w15 + w16

/-! ## 4. `rotr32` faithfulness — universal over all inputs (`bv_decide`)

The identity: at width 32, `(x >>> k) ^ (x <<< (32-k))` equals the
native `BitVec.rotateRight k` for every SHA-256 rotate amount, over all `2^32`
inputs (SAT, not enumeration). These are the `sRotr` amounts
`{2,13,22,6,11,25,7,18,17,19}`. -/

theorem rotr32_2  (x : BitVec 32) : (x >>> 2)  ^^^ (x <<< 30) = x.rotateRight 2  := by bv_decide
theorem rotr32_13 (x : BitVec 32) : (x >>> 13) ^^^ (x <<< 19) = x.rotateRight 13 := by bv_decide
theorem rotr32_22 (x : BitVec 32) : (x >>> 22) ^^^ (x <<< 10) = x.rotateRight 22 := by bv_decide
theorem rotr32_6  (x : BitVec 32) : (x >>> 6)  ^^^ (x <<< 26) = x.rotateRight 6  := by bv_decide
theorem rotr32_11 (x : BitVec 32) : (x >>> 11) ^^^ (x <<< 21) = x.rotateRight 11 := by bv_decide
theorem rotr32_25 (x : BitVec 32) : (x >>> 25) ^^^ (x <<< 7)  = x.rotateRight 25 := by bv_decide
theorem rotr32_7  (x : BitVec 32) : (x >>> 7)  ^^^ (x <<< 25) = x.rotateRight 7  := by bv_decide
theorem rotr32_18 (x : BitVec 32) : (x >>> 18) ^^^ (x <<< 14) = x.rotateRight 18 := by bv_decide
theorem rotr32_17 (x : BitVec 32) : (x >>> 17) ^^^ (x <<< 15) = x.rotateRight 17 := by bv_decide
theorem rotr32_19 (x : BitVec 32) : (x >>> 19) ^^^ (x <<< 13) = x.rotateRight 19 := by bv_decide

/-! ## 5. Every SHA-256 round primitive lowers at width 32

`isSome` through `lowerSExprW 32` (reaches `Com catCryptDialect`), and on through
`cryptoDialectToJasminCom` (reaches `Com jasminDialect` — the owned x86 backend at
32-bit `reg`s). Shown for the round step words and the schedule step, whose
subexpressions cover all six of `Σ0/Σ1/Ch/Maj/σ0/σ1`. -/

theorem newA_isSome : (progOf roundVM sNewA).isSome := by native_decide
theorem newE_isSome : (progOf roundVM sNewE).isSome := by native_decide
theorem sched_isSome : (progOf schedVM sSchedStep).isSome := by native_decide

theorem newA_lowers :
    ((progOf roundVM sNewA).bind DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  native_decide
theorem newE_lowers :
    ((progOf roundVM sNewE).bind DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  native_decide
theorem sched_lowers :
    ((progOf schedVM sSchedStep).bind DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  native_decide

/-! ## 6. `denote = spec` with 32-bit wrap (the correctness gate)

The front-emitted round/schedule words denote to the FIPS 180-4 §6.2 reference on
samples. The first `sNewA` sample forces the 32-bit adds to WRAP (a 64-bit add
would change the result), witnessing that the emitted program computes mod `2^32`,
not mod `2^64`. -/

-- new-a with a wrap-forcing sample (h = w = 0x80000000 make T1 wrap).
example : roundDenote sNewA 0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a
            0x510e527f 0x9b05688c 0x1f83d9ab 0x80000000 0x428a2f98 0x80000000
        = some (specNewA 0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a
            0x510e527f 0x9b05688c 0x1f83d9ab 0x80000000 0x428a2f98 0x80000000) := by
  native_decide
example : roundDenote sNewA 0x12345678 0x9abcdef0 0x0f0f0f0f 0xf0f0f0f0
            0xdeadbeef 0xcafebabe 0x00ff00ff 0xff00ff00 0x71374491 0x243185be
        = some (specNewA 0x12345678 0x9abcdef0 0x0f0f0f0f 0xf0f0f0f0
            0xdeadbeef 0xcafebabe 0x00ff00ff 0xff00ff00 0x71374491 0x243185be) := by
  native_decide

-- new-e (= d + T1).
example : roundDenote sNewE 0x12345678 0x9abcdef0 0x0f0f0f0f 0xf0f0f0f0
            0xdeadbeef 0xcafebabe 0x00ff00ff 0xff00ff00 0x71374491 0x243185be
        = some (specNewE 0x12345678 0x9abcdef0 0x0f0f0f0f 0xf0f0f0f0
            0xdeadbeef 0xcafebabe 0x00ff00ff 0xff00ff00 0x71374491 0x243185be) := by
  native_decide

-- schedule step (σ1/σ0 + wrapping adds), incl. a wrap sample.
example : schedDenote 0x80000000 0x80000000 0x80000000 0x80000000
        = some (specSched 0x80000000 0x80000000 0x80000000 0x80000000) := by native_decide
example : schedDenote 0x12345678 0x9abcdef0 0x0f0f0f0f 0xf0f0f0f0
        = some (specSched 0x12345678 0x9abcdef0 0x0f0f0f0f 0xf0f0f0f0) := by native_decide
example : schedDenote 0xffffffff 0x00000001 0xdeadbeef 0xcafebabe
        = some (specSched 0xffffffff 0x00000001 0xdeadbeef 0xcafebabe) := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.Sha256RoundWidth32Front
