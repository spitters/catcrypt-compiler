/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxHmac
public import CatCrypt.Crypto.SecureCompilation.VIR.HmacHkdfEmit

/-!
# #607 fan-out: functional tie — verified-compiler HMAC/HKDF bodies = the hand-emit word forms

This module wires the committed **compile-from-hax HMAC/HKDF leaves**
(`CompileFromHaxHmac.{xorPad4,xorPad4W64,expandSkel}_compiles`) onto the
**word-level forms the hand-authored emit** `VIR.HmacHkdfEmit` records:

* the HMAC XOR-pad word `K[j] ⊕ pad` (`HmacHkdfEmit.xorPadCom_denote`, whose
  result slot is `padInput V 15 ^^^ padInput V 16`), and
* the HKDF-Expand T-chaining skeleton's three-op `add`/`xor`/`or` chain
  (`HmacHkdfEmit.expandSkelBody`).

## What this is — and what it is NOT (honest framing)

This is a **functional-equality** tie, not a security claim.

- Each compile-from-hax leaf proves a *functional-correctness* fact: the artifact
  emitted by the verified compiler computes a closed-form ALU word.
- This file names those forms (`padWord`, `expandSkelWord`) so that "what the
  verified compiler emits" is literally "the word form the hand-authored
  `HmacHkdfEmit` emit denotes to". `padWord_eq_xorPadCom` shows the named pad word
  is exactly the RHS of `HmacHkdfEmit.xorPadCom_denote`.
- HMAC is a PRF / MAC and HKDF a KDF; this file makes **no** PRF/KDF security
  claim — only `<emit-form> = <hand-emit word form>`.

## Slice/width note (honest)

The leaf models the HMAC pad as a representative **4-word slice** returning
`K[3] ⊕ pad` (vs. the 16-word `xorPadCom`'s `K[15] ⊕ pad`) and the HKDF skeleton
at a representative scalar width `w = 32` (vs. the hand emit's wide `reg (8·hw)`
accumulator) — see the `CompileFromHaxHmac` module doc. Both sides are the
*same word function* (`padWord`, `expandSkelWord`); the slice index / register
width is the only delta, exactly as the leaf module documents.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxHmacTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxHmac
open CatCrypt.Crypto.SecureCompilation.VIR (Com Ctxt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.HmacHkdfEmit (xorPadCom xorPadCom_denote padInput padCtxt blockWords)

/-! ## §1  The shared HMAC pad word, and its agreement with the hand emit -/

/-- The HMAC XOR-pad word function: `padWord K pad = K ⊕ pad` — the one-`BitXor`
    word `out[j] = K[j] ^ pad` that the HMAC inner/outer pad block carries (RFC 2104). -/
def padWord {w : Nat} (k pad : BitVec w) : BitVec w := k ^^^ pad

/-- **The named pad word is the hand-emit's pad-slot value.** The RHS of
    `HmacHkdfEmit.xorPadCom_denote` (`padInput V 15 ^^^ padInput V 16`) is exactly
    `padWord` applied to key word `15` and the pad word `16`. -/
theorem padWord_eq_xorPadCom (V : Ctxt.Valuation padCtxt) :
    xorPadCom.denote V = padWord (padInput V (blockWords - 1)) (padInput V 16) := by
  rw [xorPadCom_denote]; rfl

/-! ## §2  Transport the emitted pad slices onto the named `padWord`

The emitted `w = 32` and `w = 64` pad slices (the leaf's representative `K[3] ⊕ pad`)
each compute `padWord k3 pad` — the same word function the hand emit's result slot
denotes. -/

/-- The emitted `w = 32` HMAC pad slice computes `padWord k3 pad`. -/
theorem xorPad4_emitted_eq_padWord :
    ∃ (c : Com jasminDialect (frontCtxt 32 5 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src = some c ∧
      ∀ (k0 k1 k2 k3 pad : BitVec 32),
        c.denote (inputValuation 32 5 ![k0, k1, k2, k3, pad]) = padWord k3 pad := by
  obtain ⟨c, hc, hden⟩ := xorPad4_compiles
  exact ⟨c, hc, fun k0 k1 k2 k3 pad => hden k0 k1 k2 k3 pad⟩

/-- The emitted `w = 64` HMAC pad slice (HMAC-SHA512/384) computes `padWord k3 pad`. -/
theorem xorPad4W64_emitted_eq_padWord :
    ∃ (c : Com jasminDialect (frontCtxt 64 5 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) ["k0", "k1", "k2", "k3", "pad"] xorPad4Src = some c ∧
      ∀ (k0 k1 k2 k3 pad : BitVec 64),
        c.denote (inputValuation 64 5 ![k0, k1, k2, k3, pad]) = padWord k3 pad := by
  obtain ⟨c, hc, hden⟩ := xorPad4W64_compiles
  exact ⟨c, hc, fun k0 k1 k2 k3 pad => hden k0 k1 k2 k3 pad⟩

/-! ## §3  The HKDF-Expand T-chaining skeleton word

`HmacHkdfEmit.expandSkelBody` is the three-op `add`/`xor`/`or` chain
`v0 = T+T; v1 = v0 ^ T; v2 = v1 | v0`; `expandSkelWord` names its value. -/

/-- The HKDF-Expand T-chaining skeleton word: `((T+T) ^ T) | (T+T)` — the value the
    hand-emit `HmacHkdfEmit.expandSkelBody`'s three-op `regArith` chain computes. -/
def expandSkelWord {w : Nat} (t : BitVec w) : BitVec w := ((t + t) ^^^ t) ||| (t + t)

/-- The leaf's `expandSkelSpec` equals the named `expandSkelWord`. -/
theorem expandSkelSpec_eq_word (t : BitVec 32) :
    expandSkelSpec t = expandSkelWord t := rfl

/-- The emitted HKDF-Expand skeleton body computes `expandSkelWord t` — the same
    `((T+T)^T)|(T+T)` chain the hand-emit `HmacHkdfEmit.expandSkelBody` denotes. -/
theorem expandSkel_emitted_eq_word :
    ∃ (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 1) ["t"] expandSkelSrc = some c ∧
      ∀ (t : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => t)) = expandSkelWord t := by
  obtain ⟨c, hc, hden⟩ := expandSkel_compiles
  exact ⟨c, hc, fun t => hden t⟩

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxHmacTie
