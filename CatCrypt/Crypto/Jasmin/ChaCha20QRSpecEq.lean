/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Std.Tactic.BVDecide
public import CatCrypt.Crypto.Jasmin.ChaCha20QR
public import CatCrypt.Crypto.Jasmin.ChaCha20QRSpec

/-!
# The two ChaCha20 quarter-round references are equal

Two definitions of the RFC 8439 §2.1 quarter-round agree as functions:

* `ThirToComFront.chachaQRSpec` (`ChaCha20QRSpec.lean`), written with
  `BitVec.rotateRight (32 - n)`;
* `ChaCha20QR.quarterRound`, the protocol/PRF-side reference, written with
  `rotL32 x n = (x <<< n) ||| (x >>> (32 - n))`.

`chachaQR_eq_quarterRound` is a pure functional fact; it says nothing about PRF
security.  The module imports no compiler front.  The declarations live in the
namespace `CatCrypt.Crypto.SecureCompilation.CompileFromHaxChachaTie`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxChachaTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (chachaQRSpec)
open CatCrypt.Crypto.Jasmin.ChaCha20QR (rotL32 quarterRound)

/-- The shift-or left-rotate used by the protocol-side reference equals the
    `rotateRight (32 - n)` form used by the front's emit-side reference, for the
    four ChaCha20 rotation counts `16, 12, 8, 7` (all `< 32`). -/
theorem rotL32_eq_rotateRight (x : BitVec 32) {n : Nat} (hn : n < 32) (hn0 : 0 < n) :
    rotL32 x n = x.rotateRight (32 - n) := by
  unfold rotL32
  interval_cases n <;> bv_decide

/-- **Functional equality of the two quarter-round references.** The front's
    emit-side reference `chachaQRSpec` (used by the verified-compiler leaf) and
    the protocol/PRF-side reference `quarterRound` (the building block of the
    ChaCha20 block function the PRF assumption quantifies over) compute the same
    `(a', b', c', d')`. This is a pure functional fact: it says nothing about
    PRF security. -/
theorem chachaQR_eq_quarterRound (a b c d : BitVec 32) :
    chachaQRSpec a b c d = quarterRound a b c d := by
  simp only [chachaQRSpec, quarterRound,
    rotL32_eq_rotateRight (n := 16) _ (by omega) (by omega),
    rotL32_eq_rotateRight (n := 12) _ (by omega) (by omega),
    rotL32_eq_rotateRight (n := 8) _ (by omega) (by omega),
    rotL32_eq_rotateRight (n := 7) _ (by omega) (by omega)]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxChachaTie
