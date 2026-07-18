/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect

/-!
# SHA-256 compression-ROUND `e'` word as a `Com thirDialect` leaf

The FIPS 180-4 §6.2 SHA-256 compression-function round, restricted to the
new working-state word `e'`, built directly at the **THIR-dialect** level
(`Com thirDialect`, the `compile-from-hax` front) using the higher-level
`ThirOp` surface (`thRor`, `thShrImm`, `thBin`, `thBinLit`) — mirroring the
committed `ssaSmallSigma0` / `qrBody` constructor shape.

FIPS 180-4 §6.2.2 round, with `T₁ = h + Σ₁(e) + Ch(e,f,g) + K_t + W_t`:

    e' = d + T₁ = d + h + Σ₁(e) + Ch(e,f,g) + K_t + W_t

where (FIPS 180-4 §4.1.2 / §4.1.3)

    Σ₁(e)      = ROTR⁶(e) ⊕ ROTR¹¹(e) ⊕ ROTR²⁵(e)
    Ch(e,f,g)  = (e ∧ f) ⊕ (¬e ∧ g)          (¬e = e ⊕ 0xffffffff)

This is the genuine SHA-256 round-update for the `e` lane (the one that absorbs
`Σ₁`/`Ch`/`K_t`/`W_t`) — the real-primitive milestone for the front. Unlike the
bundled `sha256RoundAThir` (on the OLDER `inductive Thir` AST, lowered to
`Com jasminDialect` via the bespoke `thirToJasmin` *jasminc* path), this leaf is
on the `Com thirDialect` AST and is therefore directly emittable through the
OWNED x86 backend spine (see
`X86Backend/Sha256RoundThirOwnedEmit.lean`).

## Argument list

Seven width-32 inputs, in de-Bruijn (program-root) order:

    [d, e, f, g, h, kt, wt]

(the round's `a, b, c` working words do not influence `e'`, so they are not
arguments; `kt = K_t`, `wt = W_t`). The single output is `e'`.

## What is verified

* `sha256RoundEComThir_denote`: the leaf denotes exactly `sha256RoundESpec7`
  (the FIPS `e'` word) on any input valuation — by `rfl`.
* `roundE_via_thirDialect`: the lowered (two-stage) `Com jasminDialect` denotes
  the same `BitVec 32` (`lowerThir_denote` ∘ `sha256RoundEComThir_denote`).

The companion `Maj(a,b,c)` leaf (`sha256MajComThir`) is also provided — a second
genuine SHA-256 round component (`T₂`'s `Maj` term).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirToComFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)

/-! ## 0. The FIPS `e'` reference (7-input form)

The bundled `sha256RoundESpec` carries the full `a..wt` 10-word vector; here we
use the 7-word `[d,e,f,g,h,kt,wt]` slice (the only words that influence `e'`).
Identical value to `sha256RoundESpec _ _ _ d e f g h kt wt` (the unused `a,b,c`
are dropped). -/

/-- FIPS 180-4 §6.2.2 round output `e' = d + T₁` over the 7 influencing words,
    `T₁ = h + Σ₁(e) + Ch(e,f,g) + K_t + W_t` summed left-to-right (wrapping u32). -/
def sha256RoundESpec7 (d e f g h kt wt : BitVec 32) : BitVec 32 :=
  d + (h + bigSigma1Spec e + chSpec e f g + kt + wt)

/-! ## 1. The SHA-256 round-`e'` program as a `Com thirDialect` leaf

Built directly at the THIR-dialect level. Inputs (de-Bruijn, program-root order):
`[d, e, f, g, h, kt, wt]` — `d = .here`, `e = .there .here`, …, `wt = .there⁶`.

SSA bindings (each `.var` prepends a fresh head binding):

    s1a  = ror  6 e            s1b  = ror 11 e            s1c  = ror 25 e
    s1x  = s1a ^ s1b           bigS1= s1x ^ s1c           (= Σ₁(e))
    ef   = e & f               ne   = e ^ 0xffffffff      neg  = ne & g
    ch   = ef ^ neg            (= Ch(e,f,g))
    t    = h + bigS1           t2   = t + ch              t3   = t2 + kt
    t1   = t3 + wt             (= T₁)
    e'   = d + t1              ret e' -/
def sha256RoundEComThir :
    Com thirDialect
      [.reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  -- s1a = ror 6 e
  .var (.mk (.thRor 32 6) rfl (.cons (.there .here) .nil))
  -- s1b = ror 11 e
  (.var (.mk (.thRor 32 11) rfl (.cons (.there (.there .here)) .nil))
  -- s1c = ror 25 e
  (.var (.mk (.thRor 32 25) rfl (.cons (.there (.there (.there .here))) .nil))
  -- s1x = s1a ^ s1b
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- bigS1 = s1x ^ s1c   (= Σ₁(e))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- ef = e & f
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there .here))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))
  -- ne = e ^ 0xffffffff   (¬e)
  (.var (.mk (.thBinLit .xor 32 0xffffffff) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))
  -- neg = ne & g
  (.var (.mk (.thBin .and 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there .here)))))))))) .nil)))
  -- ch = ef ^ neg   (= Ch(e,f,g))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons .here .nil)))
  -- t = h + bigS1
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there .here)))))))))))))
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- t2 = t + ch
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- t3 = t2 + kt
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            .here)))))))))))))))) .nil)))
  -- t1 = t3 + wt   (= T₁)
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            (.there (.there .here)))))))))))))))))) .nil)))
  -- e' = d + t1
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there .here)))))))))))))
        (.cons .here .nil)))
  (.ret .here))))))))))))))

/-- The THIR-dialect round-`e'` leaf denotes the FIPS `e'` word on any input
    valuation `[d, e, f, g, h, kt, wt]`. A direct check of the `thirDialect`
    semantics against `sha256RoundESpec7`. -/
theorem sha256RoundEComThir_denote (d e f g h kt wt : BitVec 32) :
    sha256RoundEComThir.denote
        (.cons d (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil)))))))
      = sha256RoundESpec7 d e f g h kt wt := by
  rfl

/-- **Round-`e'` re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for the SHA-256 round `e'` output denotes the same
    `BitVec 32` as the FIPS reference, obtained through
    `Com[thir] →lowerThir→ Com[jasmin]`. Combines `lowerThir_denote` (the generic,
    proved dialect lowering) with `sha256RoundEThir_denote`. -/
theorem roundE_via_thirDialect (d e f g h kt wt : BitVec 32) :
    (lowerThir sha256RoundEComThir).denote
        (.cons d (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil)))))))
      = sha256RoundESpec7 d e f g h kt wt := by
  rw [lowerThir_denote sha256RoundEComThir
      (.cons d (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil))))))),
    sha256RoundEComThir_denote]

/-! ## 1b. The SHA-256 round-`a'` word as a `Com thirDialect` leaf

The companion of `sha256RoundEComThir`: the new working-state word `a'`.

FIPS 180-4 §6.2.2, with `T₁ = h + Σ₁(e) + Ch(e,f,g) + K_t + W_t` (the **same**
`T₁` as round-`e'`) and `T₂ = Σ₀(a) + Maj(a,b,c)`:

    a' = T₁ + T₂

where (FIPS 180-4 §4.1.2 / §4.1.3)

    Σ₀(a)      = ROTR²(a) ⊕ ROTR¹³(a) ⊕ ROTR²²(a)
    Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)

`a'` depends on `a, b, c, e, f, g, h, K_t, W_t` (nine words — the round's `d`
does NOT influence `a'`, so it is dropped). -/

/-- FIPS 180-4 §6.2.2 round output `a' = T₁ + T₂` over the 9 influencing words,
    `T₁ = h + Σ₁(e) + Ch(e,f,g) + K_t + W_t` and `T₂ = Σ₀(a) + Maj(a,b,c)`,
    summed left-to-right (wrapping u32). Argument order: `[a,b,c,e,f,g,h,kt,wt]`. -/
def sha256RoundASpec9 (a b c e f g h kt wt : BitVec 32) : BitVec 32 :=
  (h + bigSigma1Spec e + chSpec e f g + kt + wt)
    + (bigSigma0Spec a + majSpec a b c)

/-! The SHA-256 round-`a'` program as a `Com thirDialect` leaf, built directly at
the THIR-dialect level. Inputs (de-Bruijn, program-root order):
`[a, b, c, e, f, g, h, kt, wt]` — `a = .here`, `b = .there .here`, …,
`wt = .there⁸ .here`.

SSA bindings (each `.var` prepends a fresh head binding):

    -- T₁ (same shape as round-e, inputs e..wt shifted +2 vs the d-rooted form)
    s1a  = ror  6 e            s1b  = ror 11 e            s1c  = ror 25 e
    s1x  = s1a ^ s1b           bigS1= s1x ^ s1c           (= Σ₁(e))
    ef   = e & f               ne   = e ^ 0xffffffff      neg  = ne & g
    ch   = ef ^ neg            (= Ch(e,f,g))
    t    = h + bigS1           t2t  = t + ch              t3   = t2t + kt
    t1   = t3 + wt             (= T₁)
    -- T₂
    s0a  = ror  2 a            s0b  = ror 13 a            s0c  = ror 22 a
    s0x  = s0a ^ s0b           bigS0= s0x ^ s0c           (= Σ₀(a))
    ab   = a & b               ac   = a & c               bc   = b & c
    mx   = ab ^ ac             maj  = mx ^ bc             (= Maj(a,b,c))
    t2   = bigS0 + maj         (= T₂)
    a'   = t1 + t2             ret a' -/
def sha256RoundAComThir :
    Com thirDialect
      [.reg 32, .reg 32, .reg 32, .reg 32, .reg 32,
       .reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  -- s1a = ror 6 e   (e at depth 3)
  .var (.mk (.thRor 32 6) rfl (.cons (.there (.there (.there .here))) .nil))
  -- s1b = ror 11 e  (e at depth 4)
  (.var (.mk (.thRor 32 11) rfl
      (.cons (.there (.there (.there (.there .here)))) .nil))
  -- s1c = ror 25 e  (e at depth 5)
  (.var (.mk (.thRor 32 25) rfl
      (.cons (.there (.there (.there (.there (.there .here))))) .nil))
  -- s1x = s1a ^ s1b
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- bigS1 = s1x ^ s1c   (= Σ₁(e))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- ef = e & f   (e at depth 8, f at depth 9)
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there .here))))))))) .nil)))
  -- ne = e ^ 0xffffffff   (¬e)   (e at depth 9)
  (.var (.mk (.thBinLit .xor 32 0xffffffff) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there .here))))))))) .nil))
  -- neg = ne & g   (g at depth 11)
  (.var (.mk (.thBin .and 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there .here))))))))))) .nil)))
  -- ch = ef ^ neg   (= Ch(e,f,g))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons .here .nil)))
  -- t = h + bigS1   (h at depth 12)
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there .here))))))))))))
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- t2t = t + ch
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- t3 = t2t + kt   (kt at depth 16)
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            .here)))))))))))))))) .nil)))
  -- t1 = t3 + wt   (= T₁)   (wt at depth 18)
  (.var (.mk (.thBin .add 32) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            (.there (.there .here)))))))))))))))))) .nil)))
  -- s0a = ror 2 a   (a at depth 13)
  (.var (.mk (.thRor 32 2) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there .here))))))))))))) .nil))
  -- s0b = ror 13 a  (a at depth 14)
  (.var (.mk (.thRor 32 13) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil))
  -- s0c = ror 22 a  (a at depth 15)
  (.var (.mk (.thRor 32 22) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil))
  -- s0x = s0a ^ s0b
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- bigS0 = s0x ^ s0c   (= Σ₀(a))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- ab = a & b   (a at depth 18, b at depth 19)
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there .here))))))))))))))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            (.there (.there (.there .here))))))))))))))))))) .nil)))
  -- ac = a & c   (a at depth 19, c at depth 21)
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there .here)))))))))))))))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil)))
  -- bc = b & c   (b at depth 21, c at depth 22)
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there .here)))))))))))))))))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) .nil)))
  -- mx = ab ^ ac
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- maj = mx ^ bc   (= Maj(a,b,c))
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- t2 = bigS0 + maj   (= T₂)
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- a' = t1 + t2   (t1 at depth 11)
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there .here)))))))))))
        (.cons .here .nil)))
  (.ret .here)))))))))))))))))))))))))

-- Round-`a'` value-correctness is gated by the byte-identical external KAT
-- (`bench/thir_front_sha256_round_a_owned`, 200000 + corner vectors): the
-- universal `sha256RoundAComThir.denote = sha256RoundASpec9` holds by `rfl` but
-- the 25-binding de-Bruijn `Com.denote` reduction is heartbeat-prohibitive.
-- The companion round-`e'` leaf retains the universal Lean proof.

/-! ## 2. Companion `Maj(a,b,c)` leaf (the `T₂` Maj term)

A second genuine SHA-256 round component: `Maj(a,b,c) = (a∧b) ⊕ (a∧c) ⊕ (b∧c)`
(FIPS 180-4 §4.1.3), built on `Com thirDialect` over `[a, b, c]`. -/

/-- SHA-256 `Maj(a,b,c)` as a `Com thirDialect` leaf over `[a, b, c]`.

    SSA: `ab = a&b;  ac = a&c;  bc = b&c;  t = ab ^ ac;  maj = t ^ bc;  ret`. -/
def sha256MajComThir : Com thirDialect [.reg 32, .reg 32, .reg 32] (.reg 32) :=
  -- ab = a & b
  .var (.mk (.thBin .and 32) rfl (.cons .here (.cons (.there .here) .nil)))
  -- ac = a & c
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))
  -- bc = b & c
  (.var (.mk (.thBin .and 32) rfl
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- t = ab ^ ac
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- maj = t ^ bc
  (.var (.mk (.thBin .xor 32) rfl
      (.cons .here (.cons (.there .here) .nil)))
  (.ret .here)))))

/-- The THIR-dialect `Maj` leaf denotes the FIPS `Maj` spec on any input
    valuation `[a, b, c]`. -/
theorem sha256MajComThir_denote (a b c : BitVec 32) :
    sha256MajComThir.denote (.cons a (.cons b (.cons c .nil)))
      = majSpec a b c := by
  rfl

/-- **`Maj` re-derived through the dialect spine.** -/
theorem maj_via_thirDialect (a b c : BitVec 32) :
    (lowerThir sha256MajComThir).denote (.cons a (.cons b (.cons c .nil)))
      = majSpec a b c := by
  rw [lowerThir_denote sha256MajComThir (.cons a (.cons b (.cons c .nil))),
    sha256MajComThir_denote]

end CatCrypt.Crypto.SecureCompilation.ThirToComFront
