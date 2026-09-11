/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# P-384 base-field ops, routed through the owned compiler front

The relational-front P-384 base-field results carry the **value** content of
the field operations:

* `RelationalFront.p384_add_commutes` proves the P-384 base-field addition
  `a + b` commutes with the field-value carrier.
* `RelationalFront.p384_mul_commutes` proves the matching multiplication, at
  the value level.

Those results live over the abstract P-384 base field — they say *what the
leaves compute*. This module supplies the orthogonal, **structural** half: the
same base-field `ADD` / `MUL` (and a small composed body) rendered as
straight-line `LowCT` field-op programs and routed through CatCrypt's owned
compiler front (`toJasminCmd`), with a proof that the front fully lowers each one
to a Jasmin call program — one `Ccall` per field op, no fall-through to an
unhandled construct.

This mirrors the `G1`-body routing in
`CatCrypt.Crypto.Pairing.Bls12381G1AUCurvesPort` §3 (`fpCall` / `g1AddBody` /
`g1AddJasmin` / `g1AddJasmin_length` / `g1AddJasmin_all_calls`): the P-384
field leaves route through the **same** owned front the bls12-381 `G1` body does,
tying the P-384 relational front to the backend.

## Scope of the claims

The claims here are purely **structural lowering**: that the owned front accepts
the rendered P-384 field-op bodies and emits one `Ccall` per op. We do **not**
claim the Jasmin program's denotation equals the P-384 field value — that needs
the `LowCT` operational semantics, and the value content is exactly what the
relational-front Add/Mul results (`p384_add_commutes` / `p384_mul_commutes`,
above) carry. As with `g1AddBody`, this file exhibits only that those same ops
lower through the front to the `fp_add` / `fp_mul` leaves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontP384Emit

/-- A base-field op call `dest := fn(a, b)` as a `LowCT` node over `TFp`.
    Mirrors `Bls12381G1AUCurvesPort.fpCall` — the P-384 base field reuses the
    same `TFp` leaf carrier the bls12-381 `G1` body routes through. -/
def fpCall (fn dest a b : String) : Jasmin.LowCT.LowCT :=
  .RCall fn ⟨dest, .TFp⟩ [⟨a, .TFp⟩, ⟨b, .TFp⟩]

/-- The P-384 base-field **ADD** as a straight-line `LowCT` body: a single
    `fp_add` leaf call `r := fp_add(a, b)`. This is the structural image of the
    op whose P-384 field-value content `RelationalFront.p384_add_commutes`
    proves. -/
def p384AddBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_add" "r" "a" "b"

/-- The P-384 base-field **MUL** as a straight-line `LowCT` body: a single
    `fp_mul` leaf call `r := fp_mul(a, b)`. The structural image of the op whose
    P-384 field-value content `RelationalFront.p384_mul_commutes` proves. -/
def p384MulBody : Jasmin.LowCT.LowCT :=
  fpCall "fp_mul" "r" "a" "b"

/-- A small **composed** P-384 base-field body — `r := a*b ; s := r+c` — two
    field-op leaves `RSeq`-chained, to show multi-op routing through the front
    (the same shape `g1AddBody` exercises at length 34). -/
def p384ComposedBody : Jasmin.LowCT.LowCT :=
  (fpCall "fp_mul" "r" "a" "b").RSeq (fpCall "fp_add" "s" "r" "c")

open CatCrypt.Crypto.Jasmin.LowCT

/-- The P-384 base-field ADD body, lowered through CatCrypt's owned front. -/
def p384AddJasmin := toJasminCmd p384AddBody

/-- The P-384 base-field MUL body, lowered through CatCrypt's owned front. -/
def p384MulJasmin := toJasminCmd p384MulBody

/-- The composed P-384 base-field body, lowered through CatCrypt's owned front. -/
def p384ComposedJasmin := toJasminCmd p384ComposedBody

/-- **The P-384 base-field ADD routes through the bridge front.** The single
    `fp_add` leaf lowers to a one-node Jasmin call program. -/
theorem p384AddJasmin_length : p384AddJasmin.length = 1 := rfl

/-- Every node the front emits for the P-384 ADD is a `Ccall` — the op is
    fully lowered (no fall-through to an unhandled construct). -/
theorem p384AddJasmin_all_calls :
    p384AddJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

/-- **The P-384 base-field MUL routes through the bridge front.** The single
    `fp_mul` leaf lowers to a one-node Jasmin call program. -/
theorem p384MulJasmin_length : p384MulJasmin.length = 1 := rfl

/-- Every node the front emits for the P-384 MUL is a `Ccall` — fully lowered. -/
theorem p384MulJasmin_all_calls :
    p384MulJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

/-- **A composed P-384 base-field body routes through the bridge front.** The
    two `RSeq`-chained field ops (`r := a*b ; s := r+c`) lower to a two-node Jasmin
    call program — one `Ccall` per op — showing multi-op routing, the same shape
    the 34-node `g1AddJasmin` exercises. -/
theorem p384ComposedJasmin_length : p384ComposedJasmin.length = 2 := rfl

/-- Every node the front emits for the composed P-384 body is a `Ccall` —
    both ops fully lowered. -/
theorem p384ComposedJasmin_all_calls :
    p384ComposedJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

end CatCrypt.Crypto.SecureCompilation.RelationalFrontP384Emit
