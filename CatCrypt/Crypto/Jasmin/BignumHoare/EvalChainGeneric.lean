/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Field-parametric reflective evaluator framework

Generalises the Curve25519-specific evaluator from
`LowCTReflectiveEval.lean` to arbitrary fields with
multiplication mod a prime.  Same `ChainOp` constructors, same
`evalChain` walk, but parametric over:

* The Nat-level modulus `p` (e.g. `2²⁵⁵ − 19` for Curve25519,
  `2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1` for P-256, etc.).
* The field's representation as `Nat / p` (always works at the
  Nat level; concrete implementations may use Montgomery /
  unsaturated radix-51 / etc., which connect via separate
  representation soundness lemmas).

## Why generalise

Three concrete pay-offs:

1. **P-256 inverse chain reuses the framework.**  P-256 uses a
   different prime but the same Bernstein-style chain shape.
   Adding P-256 inverse becomes ~50 LoC (a chain literal +
   modulus parameter), not a new framework.

2. **BLS12-381 final exponentiation.**  BLS12 final-exp is a
   long chain (~10⁴ ops) modulo a 381-bit prime; same `ChainOp`
   primitives suffice.  Reuse via instantiation.

3. **Cross-curve agreement checking.**  Same `evalChain` walks
   different curves; protocol-level proofs that hold across
   curves (e.g. "DDH reduces to CDH for any prime-order group")
   apply uniformly.

## Trust set delta

This file adds **0 new axioms**.  All concrete instantiations
(Curve25519 in `LowCTReflectiveEval.lean`, P-256 / BLS12 in
future files) inherit the per-instance soundness axioms.

The generic framework is purely a refactoring of the abstract
chain semantics; it doesn't introduce new claims.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainGeneric

/-! ## §1  Generic ChainOp + state

Same ADT shape as the Curve25519 version, but parametric in
the location type `Loc` (so different chains can use different
offset schemes — e.g., named symbols for high-level chains,
Int offsets for SSA-level chains). -/

/-- Generic chain operation, parametric over the location type. -/
inductive ChainOp (Loc : Type) where
  /-- `dst := src² mod p`. -/
  | sqrStep (dstLoc srcLoc : Loc)
  /-- `dst := a · b mod p`. -/
  | mulStep (dstLoc aLoc bLoc : Loc)
  /-- `dst := src^(2^n) · other mod p`. -/
  | repeatedSqrThenMul (dstLoc srcLoc otherLoc : Loc) (n : Nat)
  deriving Repr

/-- Generic chain state: a list of (location, value) pairs. -/
abbrev ChainState (Loc : Type) := List (Loc × Nat)

/-! ## §2  Generic evaluator (parametric in modulus + location equality) -/

/-- Read the value at a given location, returning `0` if unmapped. -/
def ChainState.read {Loc : Type} [DecidableEq Loc] :
    ChainState Loc → Loc → Nat
  | [], _ => 0
  | (l, v) :: rest, loc =>
      if l = loc then v else ChainState.read rest loc

/-- Write a value at a given location. -/
def ChainState.write {Loc : Type} [DecidableEq Loc]
    (cs : ChainState Loc) (loc : Loc) (v : Nat) : ChainState Loc :=
  (loc, v) :: cs.filter (fun p => p.1 ≠ loc)

/-- Evaluate a single chain operation against the chain state.
    Parametric in the modulus `p`. -/
def evalChainOp {Loc : Type} [DecidableEq Loc] (p : Nat)
    (op : ChainOp Loc) (cs : ChainState Loc) : ChainState Loc :=
  match op with
  | .sqrStep dst src =>
      let v := cs.read src
      cs.write dst ((v * v) % p)
  | .mulStep dst a b =>
      let va := cs.read a
      let vb := cs.read b
      cs.write dst ((va * vb) % p)
  | .repeatedSqrThenMul dst src other n =>
      let v_src := cs.read src
      let v_other := cs.read other
      cs.write dst ((v_src ^ (2^n) * v_other) % p)

/-- Sequentially evaluate a list of chain operations. -/
def evalChain {Loc : Type} [DecidableEq Loc] (p : Nat) :
    List (ChainOp Loc) → ChainState Loc → ChainState Loc
  | [], cs => cs
  | op :: rest, cs => evalChain p rest (evalChainOp p op cs)

/-! ## §3  Per-curve instantiation pattern

To instantiate the generic framework for a specific curve:

```
namespace MyCurve
  abbrev Loc := Int  -- or a symbolic enum
  abbrev p : Nat := <curve modulus>
  def myChain : List (ChainOp Loc) := [...]
  def myChainResult (input : Nat) : Nat :=
    ((evalChain p myChain (initState input)).read OUTPUT_LOC)
  axiom myChain_sound : ...
end MyCurve
```

This is the pattern used by `LowCTReflectiveEval.lean`
(Curve25519 with `Loc := Int`); future P-256 / BLS12 chains
follow the same shape with their own `p`.

## §4  Sketched concrete instantiations -/

/-- P-256 modulus: `q = 2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1`. -/
def p256_q : Nat := 2^256 - 2^224 + 2^192 + 2^96 - 1

/-- secp256k1 modulus: `2²⁵⁶ − 2³² − 977`. -/
def secp256k1_p : Nat := 2^256 - 2^32 - 977

/-- BLS12-381 base-field modulus (`p` for the curve, 381 bits). -/
def bls12_381_p : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-! ## §5  Soundness axioms — instantiation pattern

For each concrete instantiation, the per-chain soundness axiom
follows the shape:

```
axiom myChain_sound (a : Nat) :
    myChainResult a = a ^ <chain-specific-exponent> % p
```

Where `<chain-specific-exponent>` is whatever exponent the
chain's prefix + tail composition computes.

The framework provides the **shape**; per-curve instantiations
provide the modulus + chain literal + soundness axiom.

## §6  Cross-instantiation properties

Two chains over the same modulus that compute the same exponent produce the
same result; this follows from their soundness axioms whenever both cite
that exponent, and is not stated as a lemma in this file. -/

/-! ## §7  What this enables for downstream curves

A worked example for a future P-256 inverse chain:

```
namespace P256
  open EvalChainGeneric

  abbrev Loc := Int
  abbrev p := p256_q

  -- Bernstein-style chain for P-256, exponent p − 2.
  def invChain : List (ChainOp Loc) :=
    -- ... 12-block prefix walking to p^(2²⁵⁰ − 1)-equivalent
    -- ... plus tail walking to (q − 2).
    []  -- (full chain literal here)

  def invResult (a : Nat) : Nat :=
    (evalChain p invChain (initState a)).read OUT_LOC

  axiom invChain_sound (a : Nat) :
      invResult a = a ^ (p - 2) % p
end P256
```

Per-curve instantiation cost: ~50 LoC (chain literal +
soundness axiom + initState helper).  vs. ~250 LoC for a
non-generic implementation that re-derives the framework.

## §8  Status

* The generic framework is **shipped** (this file).
* Curve25519 uses the *non-generic* version
  (`LowCTReflectiveEval.lean`) for backwards compatibility.
* A future PR can refactor Curve25519 onto the generic version
  by parameterising `Loc := Int` and `p := 2^255 - 19`; mostly
  mechanical re-binding.
* P-256 and BLS12-381 instantiations are the natural follow-up
  use cases.
-/

/-! ## Exponent semantics

`Exp.eChain` runs a chain on exponents instead of values: square doubles,
multiply adds, repeated square then multiply maps `(e, e')` to `e * 2^n + e'`.
`Exp.evalChain_read` states that the value chain computes `a ^ e % p` wherever
the exponent run assigns `e`, so a chain's soundness reduces to one equality of
concrete exponents. -/

namespace Exp

/-- Exponent read: the exponent held at `loc`, or `none` if unmapped. -/
def eRead {Loc : Type} [DecidableEq Loc] : List (Loc × Nat) → Loc → Option Nat
  | [], _ => none
  | (l, e) :: rest, loc => if l = loc then some e else eRead rest loc

/-- Exponent semantics of one chain operation: square doubles, multiply
    adds, repeated square then multiply maps `(e, e')` to `e * 2^n + e'`. -/
def eOp {Loc : Type} [DecidableEq Loc] (op : ChainOp Loc) (es : List (Loc × Nat)) :
    Option (List (Loc × Nat)) :=
  match op with
  | .sqrStep dst src => (eRead es src).map fun e => ChainState.write es dst (e * 2)
  | .mulStep dst x y =>
      (eRead es x).bind fun ex => (eRead es y).map fun ey =>
        ChainState.write es dst (ex + ey)
  | .repeatedSqrThenMul dst src other n =>
      (eRead es src).bind fun es_ => (eRead es other).map fun eo =>
        ChainState.write es dst (es_ * 2 ^ n + eo)

/-- Exponent semantics of a chain. -/
def eChain {Loc : Type} [DecidableEq Loc] :
    List (ChainOp Loc) → List (Loc × Nat) → Option (List (Loc × Nat))
  | [], es => some es
  | op :: rest, es => (eOp op es).bind (eChain rest)

/-- The value state denoted by an exponent state over base `a` mod `p`. -/
def denote {Loc : Type} (p a : Nat) (es : List (Loc × Nat)) : ChainState Loc :=
  es.map fun le => (le.1, a ^ le.2 % p)

theorem read_denote {Loc : Type} [DecidableEq Loc] (p a : Nat) :
    ∀ (es : List (Loc × Nat)) (loc : Loc) (e : Nat), eRead es loc = some e →
      (denote p a es).read loc = a ^ e % p
  | [], _, _, h => by simp [eRead] at h
  | (l, e') :: rest, loc, e, h => by
    by_cases hl : l = loc
    · simp_all [eRead, denote, ChainState.read]
    · simp only [eRead, hl, if_false] at h
      simpa [denote, ChainState.read, hl] using read_denote p a rest loc e h

theorem write_denote {Loc : Type} [DecidableEq Loc] (p a : Nat)
    (es : List (Loc × Nat)) (loc : Loc) (e : Nat) :
    (denote p a es).write loc (a ^ e % p) = denote p a (ChainState.write es loc e) := by
  simp [denote, ChainState.write, List.filter_map, Function.comp_def]

/-- One chain step commutes with `denote`. -/
theorem evalChainOp_denote {Loc : Type} [DecidableEq Loc] (p a : Nat)
    (op : ChainOp Loc) (es es' : List (Loc × Nat)) (h : eOp op es = some es') :
    evalChainOp p op (denote p a es) = denote p a es' := by
  cases op with
  | sqrStep dst src =>
    simp only [eOp, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    simp only [evalChainOp, read_denote p a es src e he, ← write_denote]
    rw [← Nat.mul_mod, ← Nat.pow_add, Nat.mul_two]
  | mulStep dst x y =>
    simp only [eOp, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ex, hx, ey, hy, rfl⟩ := h
    simp only [evalChainOp, read_denote p a es x ex hx, read_denote p a es y ey hy,
      ← write_denote, ← Nat.mul_mod, ← Nat.pow_add]
  | repeatedSqrThenMul dst src other n =>
    simp only [eOp, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨es_, hs, eo, ho, rfl⟩ := h
    simp only [evalChainOp, read_denote p a es src es_ hs, read_denote p a es other eo ho,
      ← write_denote]
    rw [Nat.mul_mod_mod, ← Nat.mod_mul_mod, ← Nat.pow_mod, Nat.mod_mul_mod,
      Nat.pow_add, Nat.pow_mul]

/-- A chain commutes with `denote` whenever its exponent run succeeds. -/
theorem evalChain_denote {Loc : Type} [DecidableEq Loc] (p a : Nat) :
    ∀ (ops : List (ChainOp Loc)) (es es' : List (Loc × Nat)), eChain ops es = some es' →
      evalChain p ops (denote p a es) = denote p a es'
  | [], es, es', h => by simp_all [eChain, evalChain]
  | op :: rest, es, es', h => by
    simp only [eChain, Option.bind_eq_some_iff] at h
    obtain ⟨es1, h1, h2⟩ := h
    simp only [evalChain, evalChainOp_denote p a op es es1 h1]
    exact evalChain_denote p a rest es1 es' h2

/-- Reading `loc` after a chain yields `a ^ e % p` when the exponent run
    assigns exponent `e` to `loc`. -/
theorem evalChain_read {Loc : Type} [DecidableEq Loc] (p a : Nat)
    (ops : List (ChainOp Loc)) (es : List (Loc × Nat)) (loc : Loc) (e : Nat)
    (h : (eChain ops es).bind (eRead · loc) = some e) :
    (evalChain p ops (denote p a es)).read loc = a ^ e % p := by
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨es', h1, h2⟩ := h
  rw [evalChain_denote p a ops es es' h1]
  exact read_denote p a es' loc e h2

end Exp

end CatCrypt.Crypto.Jasmin.BignumHoare.EvalChainGeneric
