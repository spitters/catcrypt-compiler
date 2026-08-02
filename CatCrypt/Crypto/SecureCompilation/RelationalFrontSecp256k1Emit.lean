/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# secp256k1 base-field ops, routed through the owned compiler front

The relational-front secp256k1 base-field results carry the **value** content of
the field operations:

* `RelationalFront.secp_add_commutes` proves the `ZMod secpQ` base-field
  addition `a + b` commutes with the field-value carrier.
* `RelationalFront.secp_mul_commutes` proves the matching `ZMod secpQ`
  multiplication, at the value level.

Those results live over the abstract `ZMod secpQ` field — they say *what the
leaves compute*. This module supplies the orthogonal, **structural** half: the
same base-field `ADD` / `MUL` (and a small composed body) rendered as
straight-line `LowCT` field-op programs and routed through CatCrypt's owned
compiler front (`toJasminCmd`), with a proof that the front fully lowers each one
to a Jasmin call program — one `Ccall` per field op, no fall-through to an
unhandled construct.

This mirrors the `G1`-body routing in
`CatCrypt.Crypto.Pairing.Bls12381G1AUCurvesPort` §3 (`fpCall` / `g1AddBody` /
`g1AddJasmin` / `g1AddJasmin_length` / `g1AddJasmin_all_calls`): the secp256k1
field leaves route through the **same** owned front the bls12-381 `G1` body does,
tying the secp256k1 relational front to the backend.

## Scope of the claims

The claims here are purely **structural lowering**: that the owned front accepts
the rendered secp256k1 field-op bodies and emits one `Ccall` per op. We do **not**
claim the Jasmin program's denotation equals the `ZMod secpQ` field value —
that needs the `LowCT` operational semantics, and the value content is exactly
what the relational-front Add/Mul results (`secp_add_commutes` /
`secp_mul_commutes`, above) carry. As with `g1AddBody`, this file exhibits only
that those same ops lower through the front to the `fp_add` / `fp_mul` leaves.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontSecp256k1Emit

/-- A base-field op call `dest := fn(a, b)` as a `LowCT` node over `TFp`.
    Mirrors `Bls12381G1AUCurvesPort.fpCall` — the secp256k1 base field reuses the
    same `TFp` leaf carrier the bls12-381 `G1` body routes through. -/
def fpCall (fn dest a b : String) : Jasmin.LowCT.LowCT :=
  .RCall fn ⟨dest, .TFp⟩ [⟨a, .TFp⟩, ⟨b, .TFp⟩]

/-- The secp256k1 base-field **ADD** as a straight-line `LowCT` body: a single
    `fp_add` leaf call `r := fp_add(a, b)`. This is the structural image of the
    op whose `ZMod secpQ` value content `RelationalFront.secp_add_commutes`
    proves. -/
def secpAddBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_add" "r" "a" "b"

/-- The secp256k1 base-field **MUL** as a straight-line `LowCT` body: a single
    `fp_mul` leaf call `r := fp_mul(a, b)`. The structural image of the op whose
    `ZMod secpQ` value content `RelationalFront.secp_mul_commutes` proves. -/
def secpMulBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_mul" "r" "a" "b"

/-- A small **composed** secp256k1 base-field body — `r := a*b ; s := r+c` — two
    field-op leaves `RSeq`-chained, to show multi-op routing through the front
    (the same shape `g1AddBody` exercises at length 34). -/
def secpComposedBody : Jasmin.LowCT.LowCT :=
  (fpCall "fp_mul" "r" "a" "b").RSeq (fpCall "fp_add" "s" "r" "c")

open CatCrypt.Crypto.Jasmin.LowCT

/-- The secp256k1 base-field ADD body, lowered through CatCrypt's owned front. -/
def secpAddJasmin := toJasminCmd secpAddBody

/-- The secp256k1 base-field MUL body, lowered through CatCrypt's owned front. -/
def secpMulJasmin := toJasminCmd secpMulBody

/-- The composed secp256k1 base-field body, lowered through CatCrypt's owned front. -/
def secpComposedJasmin := toJasminCmd secpComposedBody

/-- **The secp256k1 base-field ADD routes through the bridge front.** The single
    `fp_add` leaf lowers to a one-node Jasmin call program. -/
theorem secpAddJasmin_length : secpAddJasmin.length = 1 := rfl

/-- Every node the front emits for the secp256k1 ADD is a `Ccall` — the op is
    fully lowered (no fall-through to an unhandled construct). -/
theorem secpAddJasmin_all_calls :
    secpAddJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

/-- **The secp256k1 base-field MUL routes through the bridge front.** The single
    `fp_mul` leaf lowers to a one-node Jasmin call program. -/
theorem secpMulJasmin_length : secpMulJasmin.length = 1 := rfl

/-- Every node the front emits for the secp256k1 MUL is a `Ccall` — fully lowered. -/
theorem secpMulJasmin_all_calls :
    secpMulJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

/-- **A composed secp256k1 base-field body routes through the bridge front.** The
    two `RSeq`-chained field ops (`r := a*b ; s := r+c`) lower to a two-node Jasmin
    call program — one `Ccall` per op — showing multi-op routing, the same shape
    the 34-node `g1AddJasmin` exercises. -/
theorem secpComposedJasmin_length : secpComposedJasmin.length = 2 := rfl

/-- Every node the front emits for the composed secp256k1 body is a `Ccall` —
    both ops fully lowered. -/
theorem secpComposedJasmin_all_calls :
    secpComposedJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

end CatCrypt.Crypto.SecureCompilation.RelationalFrontSecp256k1Emit
