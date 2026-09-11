/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.TransferDwordTransport
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
public import Transfer.Statements.ParamTransferTac
public import Transfer.Integrations.ParamNormCast

/-!
# A NON-DIAGONAL `TransferDom` for a compiler carrier change (`lo32`)

Every `TransferDom` registered by the engine so far is **diagonal** (graph `Eq`):
the same-type field domain (`ParamCryptoDomains.instTransferDomBabyBear`), the
diagonal `paramDiag`, and the lone change-of-representation toy `Num ↦ ℕ`
(`ParamTrocq.instTransferDomNumNat`). The engine README names the extension point
explicitly (`Trocq/README.md` §"Scope & limitations"):

> **`TransferDom` domains are diagonal.** `param_transfer` resolves the diagonal
> and `Num↦ℕ`; the Baby Bear `TransferDom` is the field's diagonal. A
> non-diagonal representation domain (`F↔limbs`, `ZMod p↔limbs`, group↔bytes)
> needs a registered **backward decoder** and the **limb predicate** the `∀`-rule
> emits.

This file registers exactly such a non-diagonal domain for the **compiler carrier
change** `lo32 : BitVec 64 → BitVec 32` (the dword-lane projection `setWidth 32`
of `SecureCompilation/TransferDwordTransport.lean`), and transports a
carrier-changing lowering fact across it with `param_transfer` — recovering by the
`Param` engine what `TransferDwordTransport.{andHomLo,xorHomLo,addHomLo}` and
`chD_transports` currently do by hand via `BinOpHomOn2`/`OpHomOn`.

## The carrier change and its three pieces

The carrier change is the 64↔32 lane view `lo32 a := setWidth 32 a`. The
non-diagonal domain `paramLo32 : Param .map0 .map2a (BitVec 64) (BitVec 32)`
packages the three pieces the README asks for, in the `paramNumNat` mould:

* **forward encode** — the cast graph `R a b := (lo32 a = b)` (forward structure
  `map0`: the relation alone, no forward map field, exactly as `paramNumNat`);
* **backward decoder** — the section `dec b := setWidth 64 b` (zero-extend), at
  level `map2a` together with its `map_in_R`;
* **the width/range predicate** the `∀`-rule emits — the round-trip
  `lo32 (setWidth 64 b) = b`, i.e. `setWidth 32 (setWidth 64 b) = b`, which holds
  because truncating a zero-extension to a narrower width recovers the original
  (`32 ≤ 64`). This is the "limb predicate" content: the decoder is a genuine
  *right* inverse of the truncation, so the backward `map2a` `map_in_R` closes.

Because `R` is the graph of the forward map `lo32`, this is also literally the
`ParamNormCast` **cast-graph witness shape**: the lane homomorphisms
`lo32 (a ⊙₆₄ b) = lo32 a ⊙₃₂ lo32 b` are `RArrow R (RArrow R R)` binary witnesses
over this cast graph (`§4` below), the `setWidth`-level analogue of `Nat.cast_add`
being `addCastWit`.

## What `param_transfer` discharges, and what stays manual

Registering the domain makes `param_transfer` resolve the **domain `Param`**
automatically (no caller names `lo32`, the decoder, or the round-trip). It reduces
a goal `(∀ a : BitVec 64, P a) → (∀ b : BitVec 32, P' b)` to the **pointwise**
obligation `∀ a b, lo32 a = b → P a → P' b`. The engine supplies the binder
traversal, the `ULift`/`PLift` reflection, and the abstraction-theorem combinator.

The **lane homomorphism** (`andHomLo_realizes` etc.) is still applied **by hand at
the pointwise leaf**, against the limb predicate `P'` the caller writes — this is
the documented frontier (`ParamCryptoDomains` §"The non-diagonal frontier"): the
`∀`-rule phrases the obligation against `P'` but cannot *infer* `P'` from `P`
through the carrier (that is the annotation-inference gap — full `⟦t⟧` over
arbitrary terms with per-subterm levels). So the public API **suffices** to
register a genuine non-diagonal carrier domain and to auto-resolve it in
`param_transfer`; it does **not** auto-synthesize the limb predicate, which
remains the one hand step at the leaf. Honest verdict in `§5`.

## Scope

We register **one** non-diagonal carrier `TransferDom` — `lo32 : BitVec 64 →
BitVec 32` — with forward cast graph, backward zero-extend decoder, and the
round-trip predicate; and transport three carrier-changing bitwise/add facts
across it by `param_transfer`, each closing its leaf with the corresponding
`TransferDwordTransport` lane homomorphism. No engine file is modified: the domain is
built only from the public `Param`/`TransferDom` constructors and the
`ParamNormCast` `RArrow`/`paramWitOfCastHom` shape. The trust is the `BitVec`
lane-arithmetic the dword model already carries; no new primitive is introduced.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CarrierTransferDom

open Transfer.Param
open CatCrypt.Crypto.SecureCompilation.TransferDwordTransport
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane (chD)

/-! ## §1  The carrier change as a non-diagonal `TransferDom`

`paramLo32` is the `Param .map0 .map2a (BitVec 64) (BitVec 32)` the `∀`-rule
consumes — built in the exact mould of `ParamTransfer.paramNumNat` (the only
prior non-diagonal domain), but for a **compiler** carrier rather than a numeral
representation. -/

/-- **The non-diagonal carrier domain `lo32 : BitVec 64 → BitVec 32`.**

    * forward (`map0`): the cast graph `R a b := lo32 a = b`;
    * backward (`map2a`): the decoder `dec b := setWidth 64 b` (zero-extend) with
      `map_in_R` discharged by the round-trip `lo32 (setWidth 64 b) = b`
      (truncating a zero-extension to width 32 recovers `b`, since `32 ≤ 64`).

    This is the README's named extension point realized: a non-diagonal
    `representation` domain with a registered backward decoder, in the `paramNumNat`
    shape but carrying a genuine 64→32 compiler lane change. -/
def paramLo32 : Param .map0 .map2a (BitVec 64) (BitVec 32) where
  R := fun a b => lo32 a = b
  fwd := ⟨⟩
  bwd := ⟨fun b => BitVec.setWidth 64 b,
    fun b a (h : BitVec.setWidth 64 b = a) => by
      show lo32 a = b
      subst h
      simp [lo32]⟩

/-- **Registration.** With this instance, `param_transfer` resolves the carrier
    domain `Param` for any `(∀ a : BitVec 64, …) → (∀ b : BitVec 32, …)` goal —
    the caller names neither `lo32`, the decoder, nor the round-trip. This is the
    non-diagonal analogue of `instTransferDomNumNat` / `instTransferDomBabyBear`. -/
instance instTransferDomLo32 : TransferDom (BitVec 64) (BitVec 32) where
  dom := paramLo32

/-- The carrier domain resolved by `TransferDom` is exactly `paramLo32`
    (definitionally): the 64→32 lane change runs as the registered non-diagonal
    domain, not a diagonal fallback. -/
example : (TransferDom.dom (A := BitVec 64) (A' := BitVec 32)) = paramLo32 := rfl

/-- The resolved relation on related pairs is the cast graph `lo32 a = b` — the
    pointwise obligation `param_transfer` leaves is phrased against it. -/
example (a : BitVec 64) (b : BitVec 32) :
    (TransferDom.dom (A := BitVec 64) (A' := BitVec 32)).R a b = (lo32 a = b) := rfl

/-! ## §2  Carrier-changing facts transported by `param_transfer`

Each `example` transports a `∀`-statement from the 64-bit lane to the 32-bit lane
across the **registered non-diagonal domain** — the engine resolves the domain,
leaving the pointwise leaf, which we close with the matching `TransferDwordTransport`
lane homomorphism (`andHomLo_realizes` / `xorHomLo_realizes` / `addHomLo_realizes`).
These recover, *through the engine*, exactly what the hand `BinOpHomOn2` squares
deliver: the lowering fact passes from width 64 to width 32 along `lo32`. -/

/-- **Carrier transport — `&&&` idempotence (uses `andHomLo` at the leaf).**
    `(∀ a : BitVec 64, a &&& a = a) → (∀ b : BitVec 32, b &&& b = b)`. The domain
    `Param` is resolved by `instTransferDomLo32`; the pointwise leaf pushes the
    64-bit fact to 32 bits with `andHomLo_realizes` (`lo32 (a &&& a) =
    lo32 a &&& lo32 a`). This is `param_transfer` recovering `andHomLo.realizes`. -/
theorem and_idem_transport :
    (∀ a : BitVec 64, a &&& a = a) → (∀ b : BitVec 32, b &&& b = b) := by
  param_transfer
  intro a b (hab : lo32 a = b) (h : a &&& a = a)
  rw [← hab, ← andHomLo_realizes, h]

/-- **Carrier transport — `^^^` self-inverse (uses `xorHomLo` at the leaf).**
    `(∀ a : BitVec 64, a ^^^ a = 0) → (∀ b : BitVec 32, b ^^^ b = 0)`, domain
    auto-resolved; the leaf uses `xorHomLo_realizes`. Recovers `xorHomLo.realizes`
    through the engine. -/
theorem xor_self_transport :
    (∀ a : BitVec 64, a ^^^ a = 0) → (∀ b : BitVec 32, b ^^^ b = 0) := by
  param_transfer
  intro a b (hab : lo32 a = b) (h : a ^^^ a = 0)
  have hx : lo32 (a ^^^ a) = lo32 (0 : BitVec 64) := by rw [h]
  rw [xorHomLo_realizes] at hx
  rw [← hab]
  simp only [lo32] at hx ⊢
  exact hx

/-- **Carrier transport — additive `+ 0` (uses `addHomLo` at the leaf).**
    `(∀ a : BitVec 64, a + 0 = a) → (∀ b : BitVec 32, b + 0 = b)`, domain
    auto-resolved; the leaf uses `addHomLo_realizes` (the low 32 bits of the
    64-bit add ARE the 32-bit add, *unconditionally* — `setWidth_add`). Recovers
    `addHomLo.realizes` through the engine. -/
theorem add_zero_transport :
    (∀ a : BitVec 64, a + 0 = a) → (∀ b : BitVec 32, b + 0 = b) := by
  param_transfer
  intro a b (hab : lo32 a = b) (h : a + 0 = a)
  have ha : lo32 (a + 0) = lo32 a := by rw [h]
  rw [addHomLo_realizes] at ha
  rw [← hab]
  simp only [lo32] at ha ⊢
  exact ha

/-! ## §3  The relation is a `ParamNormCast` cast graph; the homs are its witnesses

The forward relation `R a b := lo32 a = b` is the **graph of the cast `lo32`** —
the same shape `ParamNormCast.NatIntR n i := (↑n = i)` has for `ℕ → ℤ`. So the
lane homomorphisms are `Param` binary witnesses over this cast graph, in the
`ParamNormCast` `RArrow`/`paramWitOfCastHom` mould: `lo32 (a ⊙₆₄ b) =
lo32 a ⊙₃₂ lo32 b` IS `RArrow R (RArrow R R) ⊙₆₄ ⊙₃₂`. This is the embedding-level
half (`§6` of the README): a `norm_cast`-style move lemma is a Param witness over
the cast graph — here the move lemma is `setWidth_and` rather than `Nat.cast_add`. -/

/-- The cast-graph relation of the carrier `lo32`, the forward `R` of `paramLo32`.
    Definitionally the `paramLo32.R`; named for the witness statements below. -/
def Lo32R (a : BitVec 64) (b : BitVec 32) : Prop := lo32 a = b

/-- `paramLo32.R` is exactly the cast graph `Lo32R`. -/
example : paramLo32.R = Lo32R := rfl

/-- **`&&&` as a `ParamNormCast` cast-graph witness.** `RArrow Lo32R (RArrow Lo32R
    Lo32R) (&&&₆₄) (&&&₃₂)`: the lane homomorphism `lo32 (a &&& b) =
    lo32 a &&& lo32 b` read as relatedness across the carrier cast graph — the
    `setWidth_and` analogue of `ParamNormCast.addCastWit`. -/
theorem andLo32Wit :
    RArrow Lo32R (RArrow Lo32R Lo32R)
      (fun a b => a &&& b : BitVec 64 → BitVec 64 → BitVec 64)
      (fun a b => a &&& b : BitVec 32 → BitVec 32 → BitVec 32) := by
  intro a a' ha b b' hb
  simp only [Lo32R] at *
  rw [andHomLo_realizes, ha, hb]

/-- **`^^^` cast-graph witness**, from `xorHomLo_realizes`. -/
theorem xorLo32Wit :
    RArrow Lo32R (RArrow Lo32R Lo32R)
      (fun a b => a ^^^ b : BitVec 64 → BitVec 64 → BitVec 64)
      (fun a b => a ^^^ b : BitVec 32 → BitVec 32 → BitVec 32) := by
  intro a a' ha b b' hb
  simp only [Lo32R] at *
  rw [xorHomLo_realizes, ha, hb]

/-- **`+` cast-graph witness**, from `addHomLo_realizes` (full domain, no no-wrap
    precondition — `setWidth_add` is exact for the low bits). -/
theorem addLo32Wit :
    RArrow Lo32R (RArrow Lo32R Lo32R)
      (fun a b => a + b : BitVec 64 → BitVec 64 → BitVec 64)
      (fun a b => a + b : BitVec 32 → BitVec 32 → BitVec 32) := by
  intro a a' ha b b' hb
  simp only [Lo32R] at *
  rw [addHomLo_realizes, ha, hb]

/-- **The generic `ParamNormCast` correspondence, on the carrier graph.** Any lane
    homomorphism `∀ a a', Lo32R a a' → ∀ b b', Lo32R b b' → Lo32R (op a b)
    (op' a' b')` *is* the curried `RArrow Lo32R (RArrow Lo32R Lo32R) op op'` witness
    — the same fact `ParamNormCast.paramWitOfCastHom` exhibits for `NatIntR`. Here
    instantiated to `&&&`, exhibiting `andLo32Wit` as a cast-hom. -/
theorem andLo32Wit_viaCastHom :
    RArrow Lo32R (RArrow Lo32R Lo32R)
      (fun a b => a &&& b : BitVec 64 → BitVec 64 → BitVec 64)
      (fun a b => a &&& b : BitVec 32 → BitVec 32 → BitVec 32) :=
  paramWitOfCastHom Lo32R _ _ <| by
    intro a a' ha b b' hb
    simp only [Lo32R] at *
    rw [andHomLo_realizes, ha, hb]

/-! ## §4  Recovering a hand `BinOpHomOn2`/`chD_transports` use through the engine

`TransferDwordTransport.chD_transports` proves `chD (lo32 x) (lo32 y) (lo32 z) =
lo32 (chQ x y z)` by hand, composing the `andHomLo`/`xorHomLo`/`notHomLo` squares.
The same recovery runs through the registered carrier domain: a 64-bit-lane
`Ch`-idempotence-style fact transports to the dword lane. We show the single-binder
shape (the genuine `param_transfer` payoff — a 3-binder version needs the nested
`∀`-rule `forallTransfer3`, the same hand composition `chD_transports` performs).

The point of comparison (`§5`): the *domain resolution* is now automatic, where the
hand `BinOpHomOn2` route names `lo32` and the `True` domain explicitly; what stays
manual either way is the **leaf homomorphism**, because the engine cannot synthesize
the limb predicate `P'` from `P` across the carrier. -/

/-- **A `chQ`-flavoured carrier transport.** Transport `∀ a : BitVec 64,
    chQ a a a = a` (the 64-bit `Ch` body collapsed on the diagonal — `chQ a a a =
    (a &&& a) ^^^ (~~~a &&& a) = a`) to the dword lane `∀ b : BitVec 32,
    chD b b b = b`, recovering the dword `Ch` collapse through the engine. The leaf
    uses `chD_transports` (itself the hand composition of `andHomLo`/`xorHomLo`/
    `notHomLo`), pushed across the auto-resolved carrier domain. -/
theorem chD_diag_transport :
    (∀ a : BitVec 64, chQ a a a = a) → (∀ b : BitVec 32, chD b b b = b) := by
  param_transfer
  intro a b (hab : lo32 a = b) (h : chQ a a a = a)
  have hc : chD (lo32 a) (lo32 a) (lo32 a) = lo32 (chQ a a a) :=
    chD_transports a a a
  rw [h] at hc
  rw [← hab, hc]

/-! ## §5  Comparison: non-diagonal `TransferDom` + `param_transfer` vs the hand route

| Step | Hand route (`BinOpHomOn2`/`OpHomOn`, `chD_transports`) | Engine route (this file) |
|---|---|---|
| name the carrier `lo32`, the decoder, the round-trip | **explicit** in every square / `chD_transports` proof | **automatic** — resolved by `instTransferDomLo32` |
| traverse the `∀`-binder, reflect through `ULift`/`PLift` | hand `fun a => …` / `forall_congr` plumbing | **automatic** — `forallTransferAuto` / `param_transfer` |
| the lane homomorphism at the leaf (`setWidth_and` etc.) | hand (`andHomLo.realizes`) | **hand** (`andHomLo_realizes`) — unchanged |
| infer the dword (limb) predicate `P'` from the 64-bit `P` | hand (the caller writes both sides) | **hand** — the engine cannot infer `P'` across the carrier |

So the non-diagonal `TransferDom` discharges the **domain-resolution and
binder-traversal** boilerplate that the hand `BinOpHomOn2`/`chD_transports` route
spells out, leaving exactly **one** manual step at each leaf: applying the lane
homomorphism against a caller-written limb predicate. That residual is the
README's documented frontier — *not* a defect of this registration.

## The honest verdict: did the public API suffice?

**Yes, for the domain.** The public `Param`/`TransferDom` constructors and the
`ParamNormCast` `RArrow`/`paramWitOfCastHom` shape are sufficient to register a
genuine **non-diagonal** carrier `TransferDom (BitVec 64) (BitVec 32)` — forward
cast graph, backward zero-extend decoder at `map2a`, round-trip predicate — and to
have `param_transfer` auto-resolve it (`§1`) and transport carrier-changing facts
across it (`§2`, `§4`). No engine edit was needed.

**The one thing the public API does NOT do** is emit/infer the **limb predicate**
`P'` automatically: the `∀`-rule phrases the pointwise obligation against `P'` but
leaves both `P'` and the leaf homomorphism to the caller. Wiring that — inferring
`P'` from `P` by pushing the carrier through the term structure — is the
annotation-inference frontier (`ParamCryptoDomains` §"The non-diagonal frontier";
`ParamTrocq` "named frontier": full `⟦t⟧` over arbitrary terms with per-subterm
levels). That is the precise "the public API needs X" finding: **X = automatic
limb-predicate synthesis in the `∀`-rule** (the `⟦t⟧` translator extended to carry
the carrier through `P`), which the engine does not currently expose. -/

end CatCrypt.Crypto.SecureCompilation.VIR.CarrierTransferDom
