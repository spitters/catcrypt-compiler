/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# P-256 base-field ops, routed through the owned compiler front

The relational-front P-256 base-field results carry the **value** content of
the field operations:

* `RelationalFront.p256_add_commutes` proves the `ZMod p256Q` base-field
  addition `a + b` commutes with the field-value carrier.
* `RelationalFront.p256_mul_commutes` proves the matching `ZMod p256Q`
  multiplication, at the value level.

Those results live over the abstract `ZMod p256Q` field — they say *what the
leaves compute*. This module supplies the orthogonal, **structural** half: the
same base-field `ADD` / `MUL` (and a small composed body) rendered as
straight-line `LowCT` field-op programs and routed through CatCrypt's owned
compiler front (`toJasminCmd`), with a proof that the front fully lowers each one
to a Jasmin call program — one `Ccall` per field op, no fall-through to an
unhandled construct.

This mirrors the `G1`-body routing in
`CatCrypt.Crypto.Pairing.Bls12381G1AUCurvesPort` §3 (`fpCall` / `g1AddBody` /
`g1AddJasmin` / `g1AddJasmin_length` / `g1AddJasmin_all_calls`): the P-256
field leaves route through the **same** owned front the bls12-381 `G1` body does,
tying the P-256 relational front to the backend.

## Honest scope

The claims here are purely **structural lowering**: that the owned front accepts
the rendered P-256 field-op bodies and emits one `Ccall` per op. We do **not**
claim the Jasmin program's denotation equals the `ZMod p256Q` field value —
that needs the `LowCT` operational semantics, and the value content is exactly
what the relational-front Add/Mul results (`p256_add_commutes` /
`p256_mul_commutes`, above) carry. As with `g1AddBody`, this file exhibits only
that those same ops lower through the front to the `fp_add` / `fp_mul` leaves.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontP256Emit

/-- A base-field op call `dest := fn(a, b)` as a `LowCT` node over `TFp`.
    Mirrors `Bls12381G1AUCurvesPort.fpCall` — the P-256 base field reuses the
    same `TFp` leaf carrier the bls12-381 `G1` body routes through. -/
def fpCall (fn dest a b : String) : Jasmin.LowCT.LowCT :=
  .RCall fn ⟨dest, .TFp⟩ [⟨a, .TFp⟩, ⟨b, .TFp⟩]

/-- The P-256 base-field **ADD** as a straight-line `LowCT` body: a single
    `fp_add` leaf call `r := fp_add(a, b)`. This is the structural image of the
    op whose `ZMod p256Q` value content `RelationalFront.p256_add_commutes`
    proves. -/
def p256AddBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_add" "r" "a" "b"

/-- The P-256 base-field **MUL** as a straight-line `LowCT` body: a single
    `fp_mul` leaf call `r := fp_mul(a, b)`. The structural image of the op whose
    `ZMod p256Q` value content `RelationalFront.p256_mul_commutes` proves. -/
def p256MulBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_mul" "r" "a" "b"

/-- A small **composed** P-256 base-field body — `r := a*b ; s := r+c` — two
    field-op leaves `RSeq`-chained, to show multi-op routing through the front
    (the same shape `g1AddBody` exercises at length 34). -/
def p256ComposedBody : Jasmin.LowCT.LowCT :=
  (fpCall "fp_mul" "r" "a" "b").RSeq (fpCall "fp_add" "s" "r" "c")

open CatCrypt.Crypto.Jasmin.LowCT

/-- The P-256 base-field ADD body, lowered through CatCrypt's owned front. -/
def p256AddJasmin := toJasminCmd p256AddBody

/-- The P-256 base-field MUL body, lowered through CatCrypt's owned front. -/
def p256MulJasmin := toJasminCmd p256MulBody

/-- The composed P-256 base-field body, lowered through CatCrypt's owned front. -/
def p256ComposedJasmin := toJasminCmd p256ComposedBody

/-- **The P-256 base-field ADD routes through the bridge front.** The single
    `fp_add` leaf lowers to a one-node Jasmin call program. -/
theorem p256AddJasmin_length : p256AddJasmin.length = 1 := by native_decide

/-- Every node the front emits for the P-256 ADD is a `Ccall` — the op is
    fully lowered (no fall-through to an unhandled construct). -/
theorem p256AddJasmin_all_calls :
    p256AddJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

/-- **The P-256 base-field MUL routes through the bridge front.** The single
    `fp_mul` leaf lowers to a one-node Jasmin call program. -/
theorem p256MulJasmin_length : p256MulJasmin.length = 1 := by native_decide

/-- Every node the front emits for the P-256 MUL is a `Ccall` — fully lowered. -/
theorem p256MulJasmin_all_calls :
    p256MulJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

/-- **A composed P-256 base-field body routes through the bridge front.** The
    two `RSeq`-chained field ops (`r := a*b ; s := r+c`) lower to a two-node Jasmin
    call program — one `Ccall` per op — showing multi-op routing, the same shape
    the 34-node `g1AddJasmin` exercises. -/
theorem p256ComposedJasmin_length : p256ComposedJasmin.length = 2 := by native_decide

/-- Every node the front emits for the composed P-256 body is a `Ccall` —
    both ops fully lowered. -/
theorem p256ComposedJasmin_all_calls :
    p256ComposedJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.RelationalFrontP256Emit
