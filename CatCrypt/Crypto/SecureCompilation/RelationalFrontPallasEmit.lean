/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# Pallas base-field ops, routed through the owned compiler front

The relational-front Pallas base-field results carry the **value** content of
the field operations:

* `RelationalFront.pallas_add_commutes` proves the `ZMod pallasQ` base-field
  addition `a + b` commutes with the field-value carrier.
* `RelationalFront.pallas_mul_commutes` proves the matching `ZMod pallasQ`
  multiplication, at the value level.

Those results live over the abstract `ZMod pallasQ` field — they say *what the
leaves compute*. This module supplies the orthogonal, **structural** half: the
same base-field `ADD` / `MUL` (and a small composed body) rendered as
straight-line `LowCT` field-op programs and routed through CatCrypt's owned
compiler front (`toJasminCmd`), with a proof that the front fully lowers each one
to a Jasmin call program — one `Ccall` per field op, no fall-through to an
unhandled construct.

This mirrors the `G1`-body routing in
`CatCrypt.Crypto.Pairing.Bls12381G1AUCurvesPort` §3 (`fpCall` / `g1AddBody` /
`g1AddJasmin` / `g1AddJasmin_length` / `g1AddJasmin_all_calls`): the Pallas
field leaves route through the **same** owned front the bls12-381 `G1` body does,
tying the Pallas relational front to the backend.

## Honest scope

The claims here are purely **structural lowering**: that the owned front accepts
the rendered Pallas field-op bodies and emits one `Ccall` per op. We do **not**
claim the Jasmin program's denotation equals the `ZMod pallasQ` field value —
that needs the `LowCT` operational semantics, and the value content is exactly
what the relational-front Add/Mul results (`pallas_add_commutes` /
`pallas_mul_commutes`, above) carry. As with `g1AddBody`, this file exhibits only
that those same ops lower through the front to the `fp_add` / `fp_mul` leaves.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontPallasEmit

/-- A base-field op call `dest := fn(a, b)` as a `LowCT` node over `TFp`.
    Mirrors `Bls12381G1AUCurvesPort.fpCall` — the Pallas base field reuses the
    same `TFp` leaf carrier the bls12-381 `G1` body routes through. -/
def fpCall (fn dest a b : String) : Jasmin.LowCT.LowCT :=
  .RCall fn ⟨dest, .TFp⟩ [⟨a, .TFp⟩, ⟨b, .TFp⟩]

/-- The Pallas base-field **ADD** as a straight-line `LowCT` body: a single
    `fp_add` leaf call `r := fp_add(a, b)`. This is the structural image of the
    op whose `ZMod pallasQ` value content `RelationalFront.pallas_add_commutes`
    proves. -/
def pallasAddBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_add" "r" "a" "b"

/-- The Pallas base-field **MUL** as a straight-line `LowCT` body: a single
    `fp_mul` leaf call `r := fp_mul(a, b)`. The structural image of the op whose
    `ZMod pallasQ` value content `RelationalFront.pallas_mul_commutes` proves. -/
def pallasMulBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_mul" "r" "a" "b"

/-- A small **composed** Pallas base-field body — `r := a*b ; s := r+c` — two
    field-op leaves `RSeq`-chained, to show multi-op routing through the front
    (the same shape `g1AddBody` exercises at length 34). -/
def pallasComposedBody : Jasmin.LowCT.LowCT :=
  (fpCall "fp_mul" "r" "a" "b").RSeq (fpCall "fp_add" "s" "r" "c")

open CatCrypt.Crypto.Jasmin.LowCT

/-- The Pallas base-field ADD body, lowered through CatCrypt's owned front. -/
def pallasAddJasmin := toJasminCmd pallasAddBody

/-- The Pallas base-field MUL body, lowered through CatCrypt's owned front. -/
def pallasMulJasmin := toJasminCmd pallasMulBody

/-- The composed Pallas base-field body, lowered through CatCrypt's owned front. -/
def pallasComposedJasmin := toJasminCmd pallasComposedBody

/-- **The Pallas base-field ADD routes through the bridge front.** The single
    `fp_add` leaf lowers to a one-node Jasmin call program. -/
theorem pallasAddJasmin_length : pallasAddJasmin.length = 1 := by native_decide

/-- Every node the front emits for the Pallas ADD is a `Ccall` — the op is
    fully lowered (no fall-through to an unhandled construct). -/
theorem pallasAddJasmin_all_calls :
    pallasAddJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

/-- **The Pallas base-field MUL routes through the bridge front.** The single
    `fp_mul` leaf lowers to a one-node Jasmin call program. -/
theorem pallasMulJasmin_length : pallasMulJasmin.length = 1 := by native_decide

/-- Every node the front emits for the Pallas MUL is a `Ccall` — fully lowered. -/
theorem pallasMulJasmin_all_calls :
    pallasMulJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

/-- **A composed Pallas base-field body routes through the bridge front.** The
    two `RSeq`-chained field ops (`r := a*b ; s := r+c`) lower to a two-node Jasmin
    call program — one `Ccall` per op — showing multi-op routing, the same shape
    the 34-node `g1AddJasmin` exercises. -/
theorem pallasComposedJasmin_length : pallasComposedJasmin.length = 2 := by native_decide

/-- Every node the front emits for the composed Pallas body is a `Ccall` —
    both ops fully lowered. -/
theorem pallasComposedJasmin_all_calls :
    pallasComposedJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.RelationalFrontPallasEmit
