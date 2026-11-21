/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds
import CatCrypt.Crypto.Mpn.Extraction.Mpn_haxpipe

/-!
# The result type read off the spine, at a pair of an array and a word

Test inputs for `DeriveBounds.spineTy` at the result shape of `mpn_add_n` and `mpn_mul_1` of
`mpn-hax`: a function returning its array parameter and a carry word, `([u64; n], u64)`.

* On the typed extractions `Mpn.mpn_add_n_texpr` and `Mpn.mpn_mul_1_texpr` the result type is
  the tuple of the array type and `u64`.
* On a body of the same shape whose binding and sequence nodes carry the unknown type, the
  result type is read at the tuple node at the end of the spine.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBoundsTest

open _root_.Hax (TExpr ImpType ImpLit)
open DeriveBounds (spineTy)

example :
    spineTy Mpn.mpn_add_n_texpr = .tuple [.array (.uint .w64) 4, .uint .w64] := rfl

example :
    spineTy Mpn.mpn_mul_1_texpr = .tuple [.array (.uint .w64) 5, .uint .w64] := rfl

/-- The type `u64`. -/
abbrev u64T : ImpType := .uint .w64

/-- The type `usize`. -/
abbrev usizeT : ImpType := .uint .wsize

/-- The type `[u64; 4]`. -/
abbrev arrT : ImpType := .array u64T 4

/-- An `mpn_add_n`-shaped body whose binding and sequence nodes carry the unknown type:
    `let cy = 0; for i in 0..n { rp[i] = up[i]; cy = cy }; (rp, cy)`. -/
def addNShape : TExpr :=
  .mk (.letBind "cy" (.mk (.lit (.int 0)) u64T)
    (.mk (.seq
      (.mk (.forFold "i" (.mk (.lit (.int 0)) usizeT) (.mk (.var "n") usizeT)
        (.mk (.letBind "rp"
          (.mk (.app "array_update" [.mk (.var "rp") arrT, .mk (.var "i") usizeT,
            .mk (.app "index" [.mk (.var "up") arrT, .mk (.var "i") usizeT]) u64T]) arrT)
          (.mk (.letBind "cy" (.mk (.var "cy") u64T) (.mk .unitVal .unit)) .unknown))
          .unknown)) .unit)
      (.mk (.tuple [.mk (.var "rp") arrT, .mk (.var "cy") u64T]) (.tuple [arrT, u64T])))
      .unknown))
    .unknown

example : addNShape.ty = .unknown := rfl

example : spineTy addNShape = .tuple [.array (.uint .w64) 4, .uint .w64] := rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBoundsTest
