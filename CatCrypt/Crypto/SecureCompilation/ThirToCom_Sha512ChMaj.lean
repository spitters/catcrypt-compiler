/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect

/-!
# SHA-512 `Ch` and `Maj` (width 64) as `Com thirDialect` leaves

The two FIPS 180-4 §4.1.3 multi-input boolean round components of SHA-512,
built directly at the **THIR-dialect** level (`Com thirDialect`, the
`compile-from-hax` front) using the higher-level `ThirOp` surface
(`thBin .and 64` / `thBin .xor 64` / `thBinLit .xor 64 …`) — the width-64
siblings of the committed `sha256MajComThir` / the `Ch` sub-bindings of
`sha256RoundEComThir` (the SHA-256 width-32 leaves), widened to 64.

    Ch(e,f,g)  = (e ∧ f) ⊕ (¬e ∧ g)             (FIPS 180-4 §4.1.3)
    Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)    (FIPS 180-4 §4.1.3)

with `¬e` realised as `e ⊕ 0xffffffffffffffff` (`thBinLit .xor 64 …`).

These are SHA-512 primitives: `Ch` is the `T₁` choose term and `Maj`
is the `T₂` majority term of the SHA-512 compression round over `u64` words.
Each leaf is on the `Com thirDialect` AST and is therefore directly emittable
through the OWNED x86 backend spine (see
`X86Backend/Sha512ChMajThirEmit.lean`).

## Argument lists

Three width-64 inputs, in de-Bruijn (program-root) order:

    Ch  : [e, f, g]   (e = .here, f = .there .here, g = .there .there .here)
    Maj : [a, b, c]   (a = .here, b = .there .here, c = .there .there .here)

The single output is `Ch(e,f,g)` resp. `Maj(a,b,c)`.

## What is verified

* `sha512ChThir_denote` / `sha512MajThir_denote`: each leaf denotes exactly the
  FIPS reference (`sha512ChSpec` / `sha512MajSpec`) on any input valuation — by
  `rfl` (small leaves: a handful of bindings).
* `ch64_via_thirDialect` / `maj64_via_thirDialect`: the lowered (two-stage)
  `Com jasminDialect` denotes the same `BitVec 64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirToComFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)

/-! ## 0. FIPS 180-4 §4.1.3 SHA-512 `Ch`/`Maj` reference specs (width 64) -/

/-- FIPS 180-4 §4.1.3 Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g), with `¬e` as
    `e ⊕ 0xffffffffffffffff`. -/
def sha512ChSpec (e f g : BitVec 64) : BitVec 64 :=
  (e &&& f) ^^^ ((e ^^^ 0xffffffffffffffff) &&& g)

/-- FIPS 180-4 §4.1.3 Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c). -/
def sha512MajSpec (a b c : BitVec 64) : BitVec 64 :=
  (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-! ## 1. The SHA-512 `Ch` leaf as a `Com thirDialect` over `[e, f, g]`

Inputs (de-Bruijn, program-root order): `[e, f, g]` — `e = .here`,
`f = .there .here`, `g = .there .there .here`.

SSA bindings (each `.var` prepends a fresh head binding):

    ef  = e & f                ne  = e ^ 0xffffffffffffffff   (¬e)
    neg = ne & g               ch  = ef ^ neg                 (= Ch(e,f,g))
    ret ch -/
def sha512ChThir : Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- ef = e & f
  .var (.mk (.thBin .and 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- ne = e ^ 0xffffffffffffffff   (¬e)   (e at depth 1)
  (.var (.mk (.thBinLit .xor 64 0xffffffffffffffff) rfl
      (.cons (.there .here) .nil))
  -- neg = ne & g   (ne at depth 0, g at depth 4)
  (.var (.mk (.thBin .and 64) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- ch = ef ^ neg   (ef at depth 2, neg at depth 0)   (= Ch(e,f,g))
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there .here)) (.cons .here .nil)))
  (.ret .here))))

/-! ## 2. The SHA-512 `Maj` leaf as a `Com thirDialect` over `[a, b, c]`

Inputs (de-Bruijn, program-root order): `[a, b, c]` — `a = .here`,
`b = .there .here`, `c = .there .there .here`. The width-64 sibling of
`sha256MajComThir`.

SSA bindings:

    ab = a & b   ac = a & c   bc = b & c
    t  = ab ^ ac   maj = t ^ bc   (= Maj(a,b,c))
    ret maj -/
def sha512MajThir : Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- ab = a & b
  .var (.mk (.thBin .and 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- ac = a & c   (a at depth 1, c at depth 3)
  (.var (.mk (.thBin .and 64) rfl
      (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))
  -- bc = b & c   (b at depth 3, c at depth 4)
  (.var (.mk (.thBin .and 64) rfl
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- t = ab ^ ac
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- maj = t ^ bc   (= Maj(a,b,c))
  (.var (.mk (.thBin .xor 64) rfl
      (.cons .here (.cons (.there .here) .nil)))
  (.ret .here)))))

/-! ## 3. Value-correctness (by `rfl`) and dialect-spine re-derivation -/

/-- The THIR-dialect `Ch` leaf denotes the FIPS `Ch` spec on any input
    valuation `[e, f, g]`. -/
theorem sha512ChThir_denote (e f g : BitVec 64) :
    sha512ChThir.denote (.cons e (.cons f (.cons g .nil)))
      = sha512ChSpec e f g := by
  rfl

/-- The THIR-dialect `Maj` leaf denotes the FIPS `Maj` spec on any input
    valuation `[a, b, c]`. -/
theorem sha512MajThir_denote (a b c : BitVec 64) :
    sha512MajThir.denote (.cons a (.cons b (.cons c .nil)))
      = sha512MajSpec a b c := by
  rfl

/-- **`Ch` re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for `Ch` denotes the same `BitVec 64` as the FIPS
    `Ch` reference. -/
theorem ch64_via_thirDialect (e f g : BitVec 64) :
    (lowerThir sha512ChThir).denote (.cons e (.cons f (.cons g .nil)))
      = sha512ChSpec e f g := by
  rw [lowerThir_denote sha512ChThir (.cons e (.cons f (.cons g .nil))),
    sha512ChThir_denote]

/-- **`Maj` re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for `Maj` denotes the same `BitVec 64` as the FIPS
    `Maj` reference. -/
theorem maj64_via_thirDialect (a b c : BitVec 64) :
    (lowerThir sha512MajThir).denote (.cons a (.cons b (.cons c .nil)))
      = sha512MajSpec a b c := by
  rw [lowerThir_denote sha512MajThir (.cons a (.cons b (.cons c .nil))),
    sha512MajThir_denote]

end CatCrypt.Crypto.SecureCompilation.ThirToComFront
