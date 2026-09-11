/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit

/-!
# Generic EC-operation routing through the owned compiler front

This module lifts the field-agnostic field-op consolidation
(`RelationalFrontGenericEmit`) one level up the curve stack: from base-field
binary ops to **elliptic-curve point operations** (point-add, point-double,
scalar-mult ladder step).  Where `emitFieldBinop` renders one base-field op as a
straight-line `LowCT` call to an `fp_add`/`fp_mul` leaf, this module renders one
EC operation as a short straight-line `LowCT` body of calls to the curve's
`<curve>_point_add` / `<curve>_point_double` leaves, routed through CatCrypt's
owned front (`toJasminCmd`), with a proof that the front fully lowers it to a
Jasmin call program (one `Ccall` per emitted leaf call, no fall-through).

## EC-op leaf-call model

An affine EC point is a pair of base-field coordinates `(x, y)`.  An EC
operation therefore has *two* output coordinates, while the field-op `RCall`
shape writes a single destination.  We model each EC op as a two-node `RSeq` of
field-op-shaped calls — one call per output coordinate — to the curve's EC
leaf:

* `emitEcAdd leaf rx ry x1 y1 x2 y2`
  = `rx := leaf(x1, y1, x2, y2) ; ry := leaf(x1, y1, x2, y2)`
* `emitEcDouble leaf rx ry x y`
  = `rx := leaf(x, y) ; ry := leaf(x, y)`

This is the EC-level analogue of `composeFieldBinop`: a fixed-shape `RSeq` whose
node count is independent of the leaf name.  (A single-`Ccall` two-output model
via `RCallN` would also work, but the `RSeq`-of-`RCall`s form reuses the
field-op emitter's `RCall` lowering verbatim and makes the per-coordinate
addressing surface explicit, matching the dst-per-coordinate ABI of the
hand-written curve leaf shims.)

## What is generic here

* `emitEcAdd`     — one EC point-add, parametric in the leaf name.
* `emitEcDouble`  — one EC point-double, parametric in the leaf name.
* `emitEcLadderStep` — a composed double-then-add body (one scalar-mult
  ladder step), parametric in both leaf names.
* The lowering lemmas (`*_lowers_length` / `*_all_calls`) are proved
  **parametrically over an arbitrary leaf-name `String`**, *not* by
  `native_decide` on a concrete curve string.  Each EC body is an `RSeq`
  of `RCall`s; the front lowers `RSeq` to an append (`toJasminCmd_RSeq`) and
  each `RCall` to exactly one `Ccall` (`toJasminCmd_RCall`), both `rfl`
  `@[simp]` equations, so the length and all-`Ccall` facts close uniformly by
  `simp`.

## Consequence: a new curve costs zero new code

A new curve's EC ops route through the front by **applying** the generic lemmas
at its leaf names — no per-curve `native_decide`, no per-curve boilerplate.  The
§"Per-curve instances" `example`s below show that instantiating the generic
statements at `"bls377_point_add"` / `"bls377_point_double"` recovers exactly
the per-curve EC-routing facts, as one-line generic applications.

## Honest scope

As with the field-op consolidation, the claims here are purely **structural
lowering**: that the owned front accepts the rendered EC-op bodies and emits one
`Ccall` per leaf call.  This module does **not** claim the Jasmin program's
denotation equals the EC group law on `E(𝔽_q)`; that value content is carried by
the relational-front squares over the curve's group structure.  Here we exhibit
only that EC ops lower through the front to their `<curve>_point_*` leaves,
uniformly across curves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEcEmit

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit (isCcall)

/-- **The generic EC point-add emitter.** A point-add `(rx, ry) := leaf((x1,
    y1), (x2, y2))` rendered as a two-node `RSeq` of field-op-shaped calls — one
    call per output coordinate — to the curve's `<curve>_point_add` leaf,
    parametric in the leaf name.  Each operand/result coordinate is a `TFp`
    base-field slot; the four input coordinates are passed as the call's
    argument list. -/
def emitEcAdd (leaf rx ry x1 y1 x2 y2 : String) : Jasmin.LowCT.LowCT :=
  (Jasmin.LowCT.LowCT.RCall leaf ⟨rx, .TFp⟩
      [⟨x1, .TFp⟩, ⟨y1, .TFp⟩, ⟨x2, .TFp⟩, ⟨y2, .TFp⟩]).RSeq
    (Jasmin.LowCT.LowCT.RCall leaf ⟨ry, .TFp⟩
      [⟨x1, .TFp⟩, ⟨y1, .TFp⟩, ⟨x2, .TFp⟩, ⟨y2, .TFp⟩])

/-- **The generic EC point-double emitter.** A point-double `(rx, ry) :=
    leaf(x, y)` rendered as a two-node `RSeq` of field-op-shaped calls — one
    call per output coordinate — to the curve's `<curve>_point_double` leaf,
    parametric in the leaf name. -/
def emitEcDouble (leaf rx ry x y : String) : Jasmin.LowCT.LowCT :=
  (Jasmin.LowCT.LowCT.RCall leaf ⟨rx, .TFp⟩
      [⟨x, .TFp⟩, ⟨y, .TFp⟩]).RSeq
    (Jasmin.LowCT.LowCT.RCall leaf ⟨ry, .TFp⟩
      [⟨x, .TFp⟩, ⟨y, .TFp⟩])

/-- **The generic scalar-mult ladder-step builder.** A composed
    double-then-add body — the per-bit step of a Montgomery/double-and-add
    scalar multiplication — rendered as the `RSeq`-chaining of an EC
    point-double (into the intermediate `(tx, ty)`) followed by an EC
    point-add (of `(tx, ty)` with the addend `(ax, ay)`, into `(rx, ry)`),
    parametric in both leaf names. -/
def emitEcLadderStep
    (dblLeaf addLeaf tx ty rx ry x y ax ay : String) : Jasmin.LowCT.LowCT :=
  (emitEcDouble dblLeaf tx ty x y).RSeq
    (emitEcAdd addLeaf rx ry tx ty ax ay)

/-- The generic EC point-add body, lowered through CatCrypt's owned front. -/
def emitEcAddJasmin (leaf rx ry x1 y1 x2 y2 : String) : Jasmin.Cmd :=
  toJasminCmd (emitEcAdd leaf rx ry x1 y1 x2 y2)

/-- The generic EC point-double body, lowered through CatCrypt's owned front. -/
def emitEcDoubleJasmin (leaf rx ry x y : String) : Jasmin.Cmd :=
  toJasminCmd (emitEcDouble leaf rx ry x y)

/-- The generic ladder-step body, lowered through CatCrypt's owned front. -/
def emitEcLadderStepJasmin
    (dblLeaf addLeaf tx ty rx ry x y ax ay : String) : Jasmin.Cmd :=
  toJasminCmd (emitEcLadderStep dblLeaf addLeaf tx ty rx ry x y ax ay)

/-! ### Generic lowering lemmas (parametric in the leaf name)

Each holds for an **arbitrary** leaf-name `String`, closed by `simp` through the
`rfl` equations `toJasminCmd_RSeq` (RSeq ↦ append) and `toJasminCmd_RCall`
(RCall ↦ one `Ccall`) — no `native_decide` on any concrete curve string. -/

/-- **The front lowers a generic EC point-add to a two-node call program** —
    one `Ccall` per output-coordinate leaf call.  Parametric over `leaf`. -/
theorem emitEcAdd_lowers_length (leaf rx ry x1 y1 x2 y2 : String) :
    (emitEcAddJasmin leaf rx ry x1 y1 x2 y2).length = 2 := by
  simp [emitEcAddJasmin, emitEcAdd]

/-- **Every node the front emits for a generic EC point-add is a `Ccall`** — the
    op is fully lowered (no fall-through to an unhandled construct).  Parametric
    over `leaf`. -/
theorem emitEcAdd_all_calls (leaf rx ry x1 y1 x2 y2 : String) :
    (emitEcAddJasmin leaf rx ry x1 y1 x2 y2).all isCcall = true := by
  simp [emitEcAddJasmin, emitEcAdd, isCcall]

/-- **The front lowers a generic EC point-double to a two-node call program** —
    one `Ccall` per output-coordinate leaf call.  Parametric over `leaf`. -/
theorem emitEcDouble_lowers_length (leaf rx ry x y : String) :
    (emitEcDoubleJasmin leaf rx ry x y).length = 2 := by
  simp [emitEcDoubleJasmin, emitEcDouble]

/-- **Every node the front emits for a generic EC point-double is a `Ccall`** —
    fully lowered.  Parametric over `leaf`. -/
theorem emitEcDouble_all_calls (leaf rx ry x y : String) :
    (emitEcDoubleJasmin leaf rx ry x y).all isCcall = true := by
  simp [emitEcDoubleJasmin, emitEcDouble, isCcall]

/-- **The front lowers a generic ladder step to a four-node call program** —
    two `Ccall`s for the double, two for the add.  Parametric over both leaf
    names. -/
theorem emitEcLadderStep_lowers_length
    (dblLeaf addLeaf tx ty rx ry x y ax ay : String) :
    (emitEcLadderStepJasmin dblLeaf addLeaf tx ty rx ry x y ax ay).length = 4 := by
  simp [emitEcLadderStepJasmin, emitEcLadderStep, emitEcDouble, emitEcAdd]

/-- **Every node the front emits for a generic ladder step is a `Ccall`** — both
    the double and the add are fully lowered.  Parametric over both leaf
    names. -/
theorem emitEcLadderStep_all_calls
    (dblLeaf addLeaf tx ty rx ry x y ax ay : String) :
    (emitEcLadderStepJasmin dblLeaf addLeaf tx ty rx ry x y ax ay).all isCcall = true := by
  simp [emitEcLadderStepJasmin, emitEcLadderStep, emitEcDouble, emitEcAdd, isCcall]

/-! ### Per-curve instances

Instantiating the generic statements at a concrete curve's EC leaves
(`"bls377_point_add"` / `"bls377_point_double"`) recovers exactly the per-curve
EC-routing facts, as **one-line generic applications** — no per-curve
`native_decide`, no per-curve boilerplate.  Routing a new curve's EC ops through
the front is `@emitEcAdd "<curve>_point_add" …` and an application of the
generic lemmas. -/

/-- The per-curve **point-add** routing: `@emitEcAdd "bls377_point_add" …` is a
    point-add over the bls12-377 curve. -/
example (rx ry x1 y1 x2 y2 : String) : Jasmin.LowCT.LowCT :=
  emitEcAdd "bls377_point_add" rx ry x1 y1 x2 y2

/-- The per-curve **point-add** length fact, recovered generically. -/
example :
    (emitEcAddJasmin "bls377_point_add" "rx" "ry" "x1" "y1" "x2" "y2").length = 2 :=
  emitEcAdd_lowers_length "bls377_point_add" "rx" "ry" "x1" "y1" "x2" "y2"

/-- The per-curve **point-add** all-`Ccall` fact, recovered generically. -/
example :
    (emitEcAddJasmin "bls377_point_add" "rx" "ry" "x1" "y1" "x2" "y2").all isCcall = true :=
  emitEcAdd_all_calls "bls377_point_add" "rx" "ry" "x1" "y1" "x2" "y2"

/-- The per-curve **point-double** length fact, recovered generically. -/
example :
    (emitEcDoubleJasmin "bls377_point_double" "rx" "ry" "x" "y").length = 2 :=
  emitEcDouble_lowers_length "bls377_point_double" "rx" "ry" "x" "y"

/-- The per-curve **point-double** all-`Ccall` fact, recovered generically. -/
example :
    (emitEcDoubleJasmin "bls377_point_double" "rx" "ry" "x" "y").all isCcall = true :=
  emitEcDouble_all_calls "bls377_point_double" "rx" "ry" "x" "y"

/-- The per-curve **ladder-step** length fact (double-then-add lowers to four
    nodes), recovered generically. -/
example :
    (emitEcLadderStepJasmin "bls377_point_double" "bls377_point_add"
       "tx" "ty" "rx" "ry" "x" "y" "ax" "ay").length = 4 :=
  emitEcLadderStep_lowers_length "bls377_point_double" "bls377_point_add"
    "tx" "ty" "rx" "ry" "x" "y" "ax" "ay"

/-- The per-curve **ladder-step** all-`Ccall` fact, recovered generically. -/
example :
    (emitEcLadderStepJasmin "bls377_point_double" "bls377_point_add"
       "tx" "ty" "rx" "ry" "x" "y" "ax" "ay").all isCcall = true :=
  emitEcLadderStep_all_calls "bls377_point_double" "bls377_point_add"
    "tx" "ty" "rx" "ry" "x" "y" "ax" "ay"

end CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEcEmit
