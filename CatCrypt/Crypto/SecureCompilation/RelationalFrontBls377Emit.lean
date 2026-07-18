/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# BLS12-377 base-field ops, routed through the owned compiler front

The relational-front BLS12-377 base-field results carry the **value** content of
the field operations:

* `RelationalFrontBls377Add` proves the `ZMod q` base-field addition `a + b`
  commutes with the `k = 6`-limb encoding (`encMLK_add_commutes`, the carrier-port
  capstone over the multi-limb value carrier).
* `RelationalFrontBls377Mul` proves the matching `ZMod q` multiplication square,
  reducing the product at the value level (Barrett-of-the-product).

Those results live over the abstract `ZMod q` field and its limb encoding — they
say *what the leaves compute*. This module supplies the orthogonal, **structural**
half: the same base-field `ADD` / `MUL` (and a small composed body) rendered as
straight-line `LowCT` field-op programs and routed through CatCrypt's owned
compiler front (`toJasminCmd`), with a proof that the front fully lowers each one
to a Jasmin call program — one `Ccall` per field op, no fall-through to an
unhandled construct.

This mirrors the `G1`-body routing in
`CatCrypt.Crypto.Pairing.Bls12381G1AUCurvesPort` §3 (`fpCall` / `g1AddBody` /
`g1AddJasmin` / `g1AddJasmin_length` / `g1AddJasmin_all_calls`): the bls12-377
field leaves route through the **same** owned front the bls12-381 `G1` body does,
tying the bls12-377 relational front to the backend.

## Honest scope

The claims here are purely **structural lowering**: that the owned front accepts
the rendered bls12-377 field-op bodies and emits one `Ccall` per op. We do **not**
claim the Jasmin program's denotation equals the `ZMod q` field value — that needs
the `LowCT` operational semantics, and the value content is exactly what the
relational-front Add/Mul files (above) carry. As with `g1AddBody`, this file
exhibits only that those same ops lower through the front to the `fp_add` /
`fp_mul` leaves.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Emit

/-- A base-field op call `dest := fn(a, b)` as a `LowCT` node over `TFp`.
    Mirrors `Bls12381G1AUCurvesPort.fpCall` — the bls12-377 base field reuses the
    same `TFp` leaf carrier the bls12-381 `G1` body routes through. -/
def fpCall (fn dest a b : String) : Jasmin.LowCT.LowCT :=
  .RCall fn ⟨dest, .TFp⟩ [⟨a, .TFp⟩, ⟨b, .TFp⟩]

/-- The BLS12-377 base-field **ADD** as a straight-line `LowCT` body: a single
    `fp_add` leaf call `r := fp_add(a, b)`. This is the structural image of the
    op whose `ZMod q` value content `RelationalFrontBls377Add.encMLK_add_commutes`
    proves. -/
def bls377AddBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_add" "r" "a" "b"

/-- The BLS12-377 base-field **MUL** as a straight-line `LowCT` body: a single
    `fp_mul` leaf call `r := fp_mul(a, b)`. The structural image of the op whose
    `ZMod q` value content the bls12-377 MUL relational square proves. -/
def bls377MulBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_mul" "r" "a" "b"

/-- A small **composed** bls12-377 base-field body — `r := a*b ; s := r+c` — two
    field-op leaves `RSeq`-chained, to show multi-op routing through the front
    (the same shape `g1AddBody` exercises at length 34). -/
def bls377ComposedBody : Jasmin.LowCT.LowCT :=
  (fpCall "fp_mul" "r" "a" "b").RSeq (fpCall "fp_add" "s" "r" "c")

open CatCrypt.Crypto.Jasmin.LowCT

/-- The BLS12-377 base-field ADD body, lowered through CatCrypt's owned front. -/
def bls377AddJasmin := toJasminCmd bls377AddBody

/-- The BLS12-377 base-field MUL body, lowered through CatCrypt's owned front. -/
def bls377MulJasmin := toJasminCmd bls377MulBody

/-- The composed BLS12-377 base-field body, lowered through CatCrypt's owned front. -/
def bls377ComposedJasmin := toJasminCmd bls377ComposedBody

/-- **The bls12-377 base-field ADD routes through the bridge front.** The single
    `fp_add` leaf lowers to a one-node Jasmin call program. -/
theorem bls377AddJasmin_length : bls377AddJasmin.length = 1 := by native_decide

/-- Every node the front emits for the bls12-377 ADD is a `Ccall` — the op is
    fully lowered (no fall-through to an unhandled construct). -/
theorem bls377AddJasmin_all_calls :
    bls377AddJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

/-- **The bls12-377 base-field MUL routes through the bridge front.** The single
    `fp_mul` leaf lowers to a one-node Jasmin call program. -/
theorem bls377MulJasmin_length : bls377MulJasmin.length = 1 := by native_decide

/-- Every node the front emits for the bls12-377 MUL is a `Ccall` — fully lowered. -/
theorem bls377MulJasmin_all_calls :
    bls377MulJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

/-- **A composed bls12-377 base-field body routes through the bridge front.** The
    two `RSeq`-chained field ops (`r := a*b ; s := r+c`) lower to a two-node Jasmin
    call program — one `Ccall` per op — showing multi-op routing, the same shape
    the 34-node `g1AddJasmin` exercises. -/
theorem bls377ComposedJasmin_length : bls377ComposedJasmin.length = 2 := by native_decide

/-- Every node the front emits for the composed bls12-377 body is a `Ccall` —
    both ops fully lowered. -/
theorem bls377ComposedJasmin_all_calls :
    bls377ComposedJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Emit
