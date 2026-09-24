/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# Generic field-op routing through the owned compiler front

This module is the **field-agnostic consolidation** of the per-curve
relational-front emit files (`RelationalFrontBls377Emit`, and its siblings for
Pallas / secp256k1 / BN254 / Curve25519 / P-256 / P-384). Those files each
hand-inline the *same* structural shape — a base-field binary op rendered as a
straight-line `LowCT` field-op call, routed through CatCrypt's owned front
(`toJasminCmd`), with a proof that the front fully lowers it to a Jasmin call
program (one `Ccall` per field op, no fall-through to an unhandled construct).

The per-curve clones differ **only** in the leaf-name string (`"fp_add"`,
`"fp_mul"`, …) and the destination/argument identifiers. They are otherwise
identical: every one is an instance of a single generic emitter.

## What is generic here

* `emitFieldBinop leaf dest a b` — one base-field op `dest := leaf(a, b)` over
  the `TFp` carrier, parametric in the leaf name.
* `composeFieldBinop leaf₁ leaf₂ …` — a two-op `RSeq`-chained composed body,
  parametric in both leaf names.
* The lowering lemmas — `emitFieldBinop_lowers_length` /
  `emitFieldBinop_all_calls` (and the composed pair) — are proved
  **parametrically over an arbitrary leaf-name `String`**, *not* by
  `native_decide` on a concrete string. The `RCall` arm of `toJasminCmd`
  (`toJasminCmd_RCall`, an `rfl` `@[simp]` equation) emits exactly one
  `Ccall .DoNotInline … { name := leaf } …` for *every* leaf name, so the
  length and all-`Ccall` facts close uniformly by `simp`.

## Consequence: a new curve costs zero new code

A new curve's base-field ops route through the front by **applying** the generic
lemmas at its leaf names — no per-curve `native_decide`, no per-curve
boilerplate. The §"Per-curve instances" `example`s below show that instantiating
the generic statements at `"fp_add"` / `"fp_mul"` recovers exactly the per-curve
`*Jasmin_length` / `*Jasmin_all_calls` statements the 7 clone files prove. Those
files are therefore `emitFieldBinop "fp_add" …` applications.

## Scope

As with the per-curve files, the claims here are purely **structural lowering**:
that the owned front accepts the rendered field-op bodies and emits one `Ccall`
per op. This module does **not** claim the Jasmin program's denotation equals
the `ZMod q` field value — that value content is carried by the per-curve
relational-front Add/Mul squares (e.g. `encMLK_add_commutes`). Here we exhibit
only that those same ops lower through the front to their `fp_add` / `fp_mul`
leaves, uniformly across curves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit

open CatCrypt.Crypto.Jasmin.LowCT

/-- The "fully lowered" predicate on an emitted Jasmin instruction: it is a
    `Ccall`. Matches the per-curve `*_all_calls` shape verbatim. -/
def isCcall (i : CatCrypt.Crypto.Jasmin.InstrR) : Bool :=
  match i with
  | .Ccall .. => true
  | _         => false

/-- **The generic field-op emitter.** A base-field op call `dest := leaf(a, b)`
    as a `LowCT` node over the `TFp` carrier, parametric in the leaf name.

    This is the single shape every per-curve `fpCall`/`*Body` instantiates: the
    bls12-377 `bls377AddBody` is `emitFieldBinop "fp_add" "r" "a" "b"`, the
    secp / Pallas / BN254 / … add bodies are the same with their own leaf, and
    every mul body is `emitFieldBinop "fp_mul" …`. -/
def emitFieldBinop (leaf dest a b : String) : Jasmin.LowCT.LowCT :=
  .RCall leaf ⟨dest, .TFp⟩ [⟨a, .TFp⟩, ⟨b, .TFp⟩]

/-- **The generic composed-body builder.** A two-op `RSeq`-chained base-field
    body `t := leaf₁(a, b) ; s := leaf₂(t, c)`, parametric in both leaf names.
    The structural image of a composed field expression (e.g. `a*b + c`),
    matching the per-curve `*ComposedBody`. -/
def composeFieldBinop (leaf₁ leaf₂ t s a b c : String) : Jasmin.LowCT.LowCT :=
  (emitFieldBinop leaf₁ t a b).RSeq (emitFieldBinop leaf₂ s t c)

/-- The generic field-op body, lowered through CatCrypt's owned front. -/
def emitFieldBinopJasmin (leaf dest a b : String) : Jasmin.Cmd :=
  toJasminCmd (emitFieldBinop leaf dest a b)

/-- The generic composed body, lowered through CatCrypt's owned front. -/
def composeFieldBinopJasmin (leaf₁ leaf₂ t s a b c : String) : Jasmin.Cmd :=
  toJasminCmd (composeFieldBinop leaf₁ leaf₂ t s a b c)

/-! ### Generic lowering lemmas (parametric in the leaf name)

These are the consolidation's payload: each holds for an **arbitrary** leaf-name
`String`, closed by `simp` through the `rfl` equation `toJasminCmd_RCall` — no
`native_decide` on any concrete string. -/

/-- **The front lowers a generic field op to a one-node call program.** For
    *every* leaf name, `toJasminCmd (emitFieldBinop leaf …)` is a one-instruction
    Jasmin command. Parametric over `leaf : String` — this is the whole point of
    the generic form. -/
theorem emitFieldBinop_lowers_length (leaf dest a b : String) :
    (emitFieldBinopJasmin leaf dest a b).length = 1 := by
  simp [emitFieldBinopJasmin, emitFieldBinop]

/-- **Every node the front emits for a generic field op is a `Ccall`** — the op
    is fully lowered (no fall-through to an unhandled construct). Parametric over
    `leaf : String`. -/
theorem emitFieldBinop_all_calls (leaf dest a b : String) :
    (emitFieldBinopJasmin leaf dest a b).all isCcall = true := by
  simp [emitFieldBinopJasmin, emitFieldBinop, isCcall]

/-- **The front lowers a generic composed body to a two-node call program** —
    one `Ccall` per field op. Parametric over both leaf names. -/
theorem composeFieldBinop_lowers_length
    (leaf₁ leaf₂ t s a b c : String) :
    (composeFieldBinopJasmin leaf₁ leaf₂ t s a b c).length = 2 := by
  simp [composeFieldBinopJasmin, composeFieldBinop, emitFieldBinop]

/-- **Every node the front emits for a generic composed body is a `Ccall`** —
    both ops fully lowered. Parametric over both leaf names. -/
theorem composeFieldBinop_all_calls
    (leaf₁ leaf₂ t s a b c : String) :
    (composeFieldBinopJasmin leaf₁ leaf₂ t s a b c).all isCcall = true := by
  simp [composeFieldBinopJasmin, composeFieldBinop, emitFieldBinop, isCcall]

/-! ### Per-curve instances

Instantiating the generic statements at the field leaves `"fp_add"` / `"fp_mul"`
recovers exactly the per-curve `*Jasmin_length` / `*Jasmin_all_calls` statements
the 7 clone files (`RelationalFrontBls377Emit`, Pallas, secp256k1, BN254,
Curve25519, P-256, P-384) prove with per-curve `native_decide`. With the generic
lemmas, those become one-line applications needing **no** per-curve
`native_decide`. -/

/-- The per-curve **ADD** length fact (`r := fp_add(a, b)` lowers to one node),
    recovered as a generic application — the form `bls377AddJasmin_length` &
    siblings prove per-curve. -/
example : (emitFieldBinopJasmin "fp_add" "r" "a" "b").length = 1 :=
  emitFieldBinop_lowers_length "fp_add" "r" "a" "b"

/-- The per-curve **ADD** all-`Ccall` fact, recovered generically. -/
example : (emitFieldBinopJasmin "fp_add" "r" "a" "b").all isCcall = true :=
  emitFieldBinop_all_calls "fp_add" "r" "a" "b"

/-- The per-curve **MUL** length fact, recovered generically. -/
example : (emitFieldBinopJasmin "fp_mul" "r" "a" "b").length = 1 :=
  emitFieldBinop_lowers_length "fp_mul" "r" "a" "b"

/-- The per-curve **MUL** all-`Ccall` fact, recovered generically. -/
example : (emitFieldBinopJasmin "fp_mul" "r" "a" "b").all isCcall = true :=
  emitFieldBinop_all_calls "fp_mul" "r" "a" "b"

/-- The per-curve **composed** length fact (`r := a*b ; s := r+c` lowers to two
    nodes), recovered generically — the form `bls377ComposedJasmin_length` &
    siblings prove per-curve. -/
example : (composeFieldBinopJasmin "fp_mul" "fp_add" "r" "s" "a" "b" "c").length = 2 :=
  composeFieldBinop_lowers_length "fp_mul" "fp_add" "r" "s" "a" "b" "c"

/-- The per-curve **composed** all-`Ccall` fact, recovered generically. -/
example :
    (composeFieldBinopJasmin "fp_mul" "fp_add" "r" "s" "a" "b" "c").all isCcall = true :=
  composeFieldBinop_all_calls "fp_mul" "fp_add" "r" "s" "a" "b" "c"

end CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit
