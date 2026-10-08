/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# The ChaCha20 quarter-round in rotate-right form

`chachaQRSpec` is the RFC 8439 §2.1 quarter-round over four `BitVec 32` words,
with each left-rotate `rol(x, n)` written as `x.rotateRight (32 - n)`.  It is the
reference that the THIR front's quarter-round programs (`ThirToComFront`) and the
compile-from-hax quarter-round leaves (`CompileFromHaxChaCha`) denote to.  The
module imports no compiler front; `ChaCha20QRSpecEq` proves it equal to
`ChaCha20QR.quarterRound`.

The definition lives in the namespace
`CatCrypt.Crypto.SecureCompilation.ThirToComFront`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-- The reference ChaCha20 quarter-round (RFC 8439 §2.1) over four `BitVec 32`
    words, returning `(a', b', c', d')`. `rol(x,n)` is rendered as
    `x.rotateRight (32 - n)`, matching the `thRor (32 - n)` front encoding. -/
def chachaQRSpec (a b c d : BitVec 32) :
    (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) :=
  let a := a + b
  let d := (d ^^^ a).rotateRight (32 - 16)
  let c := c + d
  let b := (b ^^^ c).rotateRight (32 - 12)
  let a := a + b
  let d := (d ^^^ a).rotateRight (32 - 8)
  let c := c + d
  let b := (b ^^^ c).rotateRight (32 - 7)
  (a, b, c, d)

end CatCrypt.Crypto.SecureCompilation.ThirToComFront
