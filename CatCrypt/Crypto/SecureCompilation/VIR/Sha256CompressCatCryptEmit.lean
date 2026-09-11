/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha256RoundCatCryptEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha256RoundCatCryptEmit

/-!
# The whole SHA-256 compression routed through `catCryptDialect`

[`Sha256RoundCatCryptEmit.lean`](Sha256RoundCatCryptEmit.lean) builds the four
FIPS 180-4 §4.1.2 SHA-256 round-mixing functions — `Σ₀`, `Σ₁`, `Ch`, `Maj` —
natively as straight-line `Com catCryptDialect` programs and proves each denotes
to the matching `BitVec`-native FIPS reference in `CatCrypt.Util.Sha256Verified`.
But the round-mixing functions are *sub*-kernels; the **benchmarked** primitive
(`bench/sha2_compare`, vs HACL*) is the whole 64-round SHA-256 compression
function `compress(H, M)`.

This file closes that gap, mirroring `Chacha20BlockCatCryptEmit.lean`: it composes
the committed catCrypt-dialect round-mixing `Com`s into the **whole 64-round
compression** and proves the composite equals the FIPS 180-4 §6.2 whole-compress
reference (the message schedule `W[0..63]`, the 64 round updates over the eight
working words `(a..h)` driven by `T1`/`T2`, then the feed-forward add). So the
whole benchmarked SHA-256 primitive — not just a sub-kernel — now routes through
the high `catCryptDialect` surface.

## Structural composition (NOT a monolithic 64-round `rfl`)

A single straight-line `Com catCryptDialect` for the whole compression is
thousands of de-Bruijn-threaded ops (64 rounds × the round body + the 48-step
schedule expansion), which is neither hand-authorable nor `rfl`/`native_decide`-
closable at MCP heartbeats. Instead the compression is composed **structurally**,
mirroring `Chacha20BlockCatCryptEmit.lean`:

1. **`σ₀`/`σ₁` small-sigma `Com`s** (`§1`) — the message-schedule mixing
   functions `σ₀(x) = ror x 7 ^ ror x 18 ^ shr x 3` and
   `σ₁(x) = ror x 17 ^ ror x 19 ^ shr x 10` as native `Com catCryptDialect`
   programs (the analogues of the round file's `Σ₀/Σ₁`, but with one `bvShiftR`
   leg instead of a third rotate), each with a `denote = Sha256Verified.smallSigma{0,1}`
   lemma.

2. **The catCrypt-driven mixing wrappers** (`§2`) — `bigSigma0Cat`, `bigSigma1Cat`,
   `chCat`, `majCat`, `smallSigma0Cat`, `smallSigma1Cat`: each is the corresponding
   committed `Com catCryptDialect` program *evaluated* (`.denote` on the input
   valuation). The single point where the high dialect does the word arithmetic;
   the `*_eq` lemmas collapse each to its `Sha256Verified` reference by the
   committed denote lemmas.

3. **The round update + schedule + loop over the catCrypt wrappers** (`§3`) — the
   FIPS 180-4 §6.2 round update `(a..h) ↦ (a'..h')` (`T1 = h + Σ₁ e + Ch e f g +
   K[t] + W[t]`, `T2 = Σ₀ a + Maj a b c`, new state `(T1+T2, a, b, c, d+T1, e, f,
   g)`), the message schedule `W[16..63] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) +
   W[t-16]`, the 64-round fold, and the feed-forward add — all driven by the
   catCrypt wrappers.

4. **`sha256Compress_catcrypt_denote`** (`§4`) — the keystone: the whole catCrypt
   compression equals the FIPS 180-4 §6.2 reference compression (the SAME
   structure over the `Sha256Verified` reference mixing functions), proved by
   folding the six per-mixing-function `*_eq` lemmas through the round/schedule/
   loop structure (`funext` + `simp only`), NOT one monolithic `rfl`. Every
   round-mixing application in the whole compression is evaluated by the committed
   `Com catCryptDialect` program.

0 sorries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha256CompressCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256RoundCatCryptEmit
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie (rotateRight_eq_rotr)

/-! ## 1. The small-sigma `σ₀`/`σ₁` programs (input `[x]`; `bvRor`×2 + `bvShiftR`)

The message-schedule mixing functions read a single 32-bit word and combine two
right-rotates with one logical right-shift via XOR. The op fragment is the round
file's `Σ`-shape with the third rotate replaced by a `bvShiftR` (the seam-lowering
shift ↦ jasmin `shrImm`). The input context is `[T32]`. -/

/-- `σ₀` over `catCryptDialect`: `ror x 7 ^ ror x 18 ^ shr x 3`. Input context `[x]`. -/
def sha256SmallSigma0Cat : Com catCryptDialect [T32] T32 :=
  -- r7 = ror x 7;  ctx [x]
  Com.var (Expr.mk (CatCryptOp.bvRor 32 7) rfl (.cons .here .nil))
  -- r18 = ror x 18;  ctx [r7,x],  x = there here
  (Com.var (Expr.mk (CatCryptOp.bvRor 32 18) rfl (.cons (.there .here) .nil))
  -- s3 = shr x 3;  ctx [r18,r7,x],  x = there (there here)
  (Com.var (Expr.mk (CatCryptOp.bvShiftR 32 3) rfl (.cons (.there (.there .here)) .nil))
  -- t = r7 ^ r18;  ctx [s3,r18,r7,x],  r7 = there (there here),  r18 = there here
  (Com.var (Expr.mk (CatCryptOp.bvXor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- out = t ^ s3;  ctx [t,s3,r18,r7,x],  t = here,  s3 = there here
  (Com.var (Expr.mk (CatCryptOp.bvXor 32) rfl (.cons .here (.cons (.there .here) .nil)))
  (Com.ret .here)))))

/-- `σ₁` over `catCryptDialect`: `ror x 17 ^ ror x 19 ^ shr x 10`. Input context `[x]`. -/
def sha256SmallSigma1Cat : Com catCryptDialect [T32] T32 :=
  Com.var (Expr.mk (CatCryptOp.bvRor 32 17) rfl (.cons .here .nil))
  (Com.var (Expr.mk (CatCryptOp.bvRor 32 19) rfl (.cons (.there .here) .nil))
  (Com.var (Expr.mk (CatCryptOp.bvShiftR 32 10) rfl (.cons (.there (.there .here)) .nil))
  (Com.var (Expr.mk (CatCryptOp.bvXor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  (Com.var (Expr.mk (CatCryptOp.bvXor 32) rfl (.cons .here (.cons (.there .here) .nil)))
  (Com.ret .here)))))

/-- `bvShiftR` waist: the dialect logical-right-shift denotation. -/
def shShrW (k : Nat) (a : BitVec 32) : BitVec 32 := BitVec.ushiftRight a k

/-- Peel one `bvShiftR 32 k` binding. -/
theorem denote_var_bvShiftR {Γ : Ctxt catCryptDialect} {k : Nat} {s : CryptoTy}
    (va : Ctxt.Var Γ (CryptoTy.sword 32))
    (body : Com catCryptDialect (CryptoTy.sword 32 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvShiftR 32 k) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (shShrW k (va.lookup V))) := rfl

set_option maxHeartbeats 1000000

/-- **`σ₀`.** The catCrypt program denotes to the FIPS reference
    `Sha256Verified.smallSigma0`. -/
theorem sha256_smallsigma0_catcrypt_denote (x : BitVec 32) :
    sha256SmallSigma0Cat.denote (inV1 x) = CatCrypt.Util.Sha256Verified.smallSigma0 x := by
  simp only [sha256SmallSigma0Cat]
  rw [denote_var_bvRor, denote_var_bvRor, denote_var_bvShiftR, denote_var_bvXor,
    denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend, lookup_here_cons, shRorW,
    shShrW, shXorW]
  rw [CatCrypt.Util.Sha256Verified.smallSigma0,
    rotateRight_eq_rotr x (n := 7) (by omega),
    rotateRight_eq_rotr x (n := 18) (by omega)]
  rfl

/-- **`σ₁`.** The catCrypt program denotes to the FIPS reference
    `Sha256Verified.smallSigma1`. -/
theorem sha256_smallsigma1_catcrypt_denote (x : BitVec 32) :
    sha256SmallSigma1Cat.denote (inV1 x) = CatCrypt.Util.Sha256Verified.smallSigma1 x := by
  simp only [sha256SmallSigma1Cat]
  rw [denote_var_bvRor, denote_var_bvRor, denote_var_bvShiftR, denote_var_bvXor,
    denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend, lookup_here_cons, shRorW,
    shShrW, shXorW]
  rw [CatCrypt.Util.Sha256Verified.smallSigma1,
    rotateRight_eq_rotr x (n := 17) (by omega),
    rotateRight_eq_rotr x (n := 19) (by omega)]
  rfl

/-! ## 2. The catCrypt-driven mixing wrappers

Each wrapper runs the committed `Com catCryptDialect` mixing program on its input
valuation and returns the denotation. This is the single point where the high
dialect performs the SHA-256 word arithmetic; the `*_eq` lemmas collapse each to
its `Sha256Verified` reference by the committed denote lemmas. -/

/-- `Σ₀` computed by the committed catCrypt `Com`. -/
def bigSigma0Cat (a : BitVec 32) : BitVec 32 := sha256Sigma0Cat.denote (inV1 a)
/-- `Σ₁` computed by the committed catCrypt `Com`. -/
def bigSigma1Cat (e : BitVec 32) : BitVec 32 := sha256Sigma1Cat.denote (inV1 e)
/-- `Ch` computed by the committed catCrypt `Com`. -/
def chCat (e f g : BitVec 32) : BitVec 32 := sha256ChCat.denote (inV3 e f g)
/-- `Maj` computed by the committed catCrypt `Com`. -/
def majCat (a b c : BitVec 32) : BitVec 32 := sha256MajCat.denote (inV3 a b c)
/-- `σ₀` computed by the committed catCrypt `Com`. -/
def smallSigma0Cat (x : BitVec 32) : BitVec 32 := sha256SmallSigma0Cat.denote (inV1 x)
/-- `σ₁` computed by the committed catCrypt `Com`. -/
def smallSigma1Cat (x : BitVec 32) : BitVec 32 := sha256SmallSigma1Cat.denote (inV1 x)

@[simp] theorem bigSigma0Cat_eq (a : BitVec 32) :
    bigSigma0Cat a = CatCrypt.Util.Sha256Verified.bigSigma0 a :=
  sha256_sigma0_catcrypt_denote a
@[simp] theorem bigSigma1Cat_eq (e : BitVec 32) :
    bigSigma1Cat e = CatCrypt.Util.Sha256Verified.bigSigma1 e :=
  sha256_sigma1_catcrypt_denote e
@[simp] theorem chCat_eq (e f g : BitVec 32) :
    chCat e f g = CatCrypt.Util.Sha256Verified.ch e f g :=
  sha256_ch_catcrypt_denote e f g
@[simp] theorem majCat_eq (a b c : BitVec 32) :
    majCat a b c = CatCrypt.Util.Sha256Verified.maj a b c :=
  sha256_maj_catcrypt_denote a b c
@[simp] theorem smallSigma0Cat_eq (x : BitVec 32) :
    smallSigma0Cat x = CatCrypt.Util.Sha256Verified.smallSigma0 x :=
  sha256_smallsigma0_catcrypt_denote x
@[simp] theorem smallSigma1Cat_eq (x : BitVec 32) :
    smallSigma1Cat x = CatCrypt.Util.Sha256Verified.smallSigma1 x :=
  sha256_smallsigma1_catcrypt_denote x

/-! ## 3. The round update, message schedule, and 64-round loop over the wrappers

The FIPS 180-4 §6.2 compression structure, with every mixing application routed
through the catCrypt wrappers of `§2`. The `Sha256Verified.Sha256Working` eight
working words carry the state; a `Fin 64 → BitVec 32` block carries the 16 input
message words (`W[0..15]`) and is expanded to `W[0..63]` by the schedule. -/

open CatCrypt.Util.Sha256Verified (Sha256Working)

/-- One SHA-256 round, with `Σ₀/Σ₁/Ch/Maj` computed by the catCrypt `Com`s.
    Mirrors `Sha256Verified.sha256RoundVerified`. -/
def sha256RoundCat (s : Sha256Working) (kt wt : BitVec 32) : Sha256Working :=
  let t1 := s.h + bigSigma1Cat s.e + chCat s.e s.f s.g + kt + wt
  let t2 := bigSigma0Cat s.a + majCat s.a s.b s.c
  { a := t1 + t2, b := s.a, c := s.b, d := s.c, e := s.d + t1, f := s.e, g := s.f, h := s.g }

/-- The catCrypt round equals the FIPS reference round `sha256RoundVerified`. -/
theorem sha256RoundCat_eq (s : Sha256Working) (kt wt : BitVec 32) :
    sha256RoundCat s kt wt = CatCrypt.Util.Sha256Verified.sha256RoundVerified s kt wt := by
  simp only [sha256RoundCat, CatCrypt.Util.Sha256Verified.sha256RoundVerified,
    bigSigma0Cat_eq, bigSigma1Cat_eq, chCat_eq, majCat_eq]

/-- The message schedule `W[0..63]` from 16 input words, with `σ₀/σ₁` computed by
    the catCrypt `Com`s. `W[t] = M[t]` for `t < 16`; otherwise
    `W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`. -/
def wScheduleCat (m : Fin 16 → BitVec 32) : Fin 64 → BitVec 32
  | t =>
    if h : t.val < 16 then m ⟨t.val, h⟩
    else
      have h2 : t.val - 2 < t.val := by omega
      have h7 : t.val - 7 < t.val := by omega
      have h15 : t.val - 15 < t.val := by omega
      have h16 : t.val - 16 < t.val := by omega
      smallSigma1Cat (wScheduleCat m ⟨t.val - 2, by omega⟩) +
        wScheduleCat m ⟨t.val - 7, by omega⟩ +
        smallSigma0Cat (wScheduleCat m ⟨t.val - 15, by omega⟩) +
        wScheduleCat m ⟨t.val - 16, by omega⟩
  termination_by t => t.val

/-- The FIPS reference message schedule, with `σ₀/σ₁` the `Sha256Verified`
    references. Same structure as `wScheduleCat`. -/
def wScheduleSpec (m : Fin 16 → BitVec 32) : Fin 64 → BitVec 32
  | t =>
    if h : t.val < 16 then m ⟨t.val, h⟩
    else
      have h2 : t.val - 2 < t.val := by omega
      have h7 : t.val - 7 < t.val := by omega
      have h15 : t.val - 15 < t.val := by omega
      have h16 : t.val - 16 < t.val := by omega
      CatCrypt.Util.Sha256Verified.smallSigma1 (wScheduleSpec m ⟨t.val - 2, by omega⟩) +
        wScheduleSpec m ⟨t.val - 7, by omega⟩ +
        CatCrypt.Util.Sha256Verified.smallSigma0 (wScheduleSpec m ⟨t.val - 15, by omega⟩) +
        wScheduleSpec m ⟨t.val - 16, by omega⟩
  termination_by t => t.val

/-- The catCrypt message schedule equals the FIPS reference schedule. Proved by
    strong induction on the round index, folding the committed `σ₀/σ₁` denote
    lemmas at each expansion step. -/
theorem wScheduleCat_eq (m : Fin 16 → BitVec 32) (t : Fin 64) :
    wScheduleCat m t = wScheduleSpec m t := by
  have key : ∀ n : Nat, ∀ ht : n < 64, wScheduleCat m ⟨n, ht⟩ = wScheduleSpec m ⟨n, ht⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro ht
      rw [wScheduleCat, wScheduleSpec]
      by_cases h : n < 16
      · simp only [h, dif_pos]
      · simp only [h, dif_neg, not_false_iff]
        rw [ih (n - 2) (by omega) (by omega), ih (n - 7) (by omega) (by omega),
          ih (n - 15) (by omega) (by omega), ih (n - 16) (by omega) (by omega),
          smallSigma1Cat_eq, smallSigma0Cat_eq]
  exact key t.val t.isLt

/-- The catCrypt round constants `K[t]` reference (`Sha256Verified` has none;
    the constants are not part of the mixing — they are the input parameter
    threaded into the round). The compression is parametric over `K`. -/
abbrev RoundConst := Fin 64 → BitVec 32

/-- Run all 64 rounds over the catCrypt round update, given the expanded schedule
    `W[0..63]` and the round constants `K[0..63]`. -/
def runRoundsCat (k : RoundConst) (w : Fin 64 → BitVec 32) (s0 : Sha256Working) :
    Sha256Working :=
  Fin.foldl 64 (fun s t => sha256RoundCat s (k t) (w t)) s0

/-- Run all 64 rounds over the FIPS reference round update. -/
def runRoundsSpec (k : RoundConst) (w : Fin 64 → BitVec 32) (s0 : Sha256Working) :
    Sha256Working :=
  Fin.foldl 64 (fun s t => CatCrypt.Util.Sha256Verified.sha256RoundVerified s (k t) (w t)) s0

/-- The 64-round catCrypt fold equals the FIPS reference fold, by congruence on the
    fold body (`sha256RoundCat_eq`), NOT by unfolding the 64 rounds. -/
theorem runRoundsCat_eq (k : RoundConst) (w : Fin 64 → BitVec 32) (s0 : Sha256Working) :
    runRoundsCat k w s0 = runRoundsSpec k w s0 := by
  have hbody : (fun s t => sha256RoundCat s (k t) (w t))
      = (fun s t => CatCrypt.Util.Sha256Verified.sha256RoundVerified s (k t) (w t)) := by
    funext s t; exact sha256RoundCat_eq s (k t) (w t)
  simp only [runRoundsCat, runRoundsSpec, hbody]

/-- The feed-forward add of two working-word states (FIPS 180-4 §6.2.2 step 4). -/
def feedForward (s s0 : Sha256Working) : Sha256Working :=
  { a := s0.a + s.a, b := s0.b + s.b, c := s0.c + s.c, d := s0.d + s.d,
    e := s0.e + s.e, f := s0.f + s.f, g := s0.g + s.g, h := s0.h + s.h }

/-- The whole SHA-256 compression over the catCrypt `Com`s: expand the schedule,
    run 64 rounds, feed-forward. FIPS 180-4 §6.2. -/
def sha256CompressCat (k : RoundConst) (s0 : Sha256Working) (m : Fin 16 → BitVec 32) :
    Sha256Working :=
  feedForward (runRoundsCat k (wScheduleCat m) s0) s0

/-- The FIPS reference whole SHA-256 compression (same structure, reference mixing
    functions). -/
def sha256CompressSpec (k : RoundConst) (s0 : Sha256Working) (m : Fin 16 → BitVec 32) :
    Sha256Working :=
  feedForward (runRoundsSpec k (wScheduleSpec m) s0) s0

/-! ## 4. The whole catCrypt compression equals the FIPS 180-4 §6.2 reference

The keystone. The schedule equality (`wScheduleCat_eq`) and the 64-round fold
equality (`runRoundsCat_eq`) compose: the whole catCrypt compression equals the
FIPS reference compression. Every round-mixing application is evaluated by the
committed `Com catCryptDialect` program. -/

/-- **Whole-compression keystone.** The whole SHA-256 compression computed over the
    committed catCrypt-dialect round-mixing `Com`s equals the FIPS 180-4 §6.2
    reference compression. Every `Σ₀/Σ₁/Ch/Maj/σ₀/σ₁` application in the message
    schedule and the 64 rounds is evaluated by the committed `Com catCryptDialect`
    programs, so the whole benchmarked SHA-256 compression primitive routes through
    the high dialect. -/
theorem sha256Compress_catcrypt_denote (k : RoundConst) (s0 : Sha256Working)
    (m : Fin 16 → BitVec 32) :
    sha256CompressCat k s0 m = sha256CompressSpec k s0 m := by
  have hw : wScheduleCat m = wScheduleSpec m := funext (wScheduleCat_eq m)
  simp only [sha256CompressCat, sha256CompressSpec, hw, runRoundsCat_eq]

end CatCrypt.Crypto.SecureCompilation.VIR.Sha256CompressCatCryptEmit
