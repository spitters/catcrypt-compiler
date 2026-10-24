/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.Jasmin.BignumExec

/-!
# Reflective evaluator for LowCT chains

A pure, reflectively-computable evaluator for chain-shaped
LowCT bodies (the bignum addition chains).  Operates at the
**abstract chain-step** level, eliding the SSA InstrR
machinery.

## Why reflective evaluation

Fiat-crypto's reflective approach achieves
spectacular per-LoC ratios for arithmetic-heavy proofs by
*concretely computing* the chain on a symbolic input via
`vm_compute`.

CatCrypt's `bignumExec` / `bignumExecFuel` interpreter goes
through `Cassgn` + `Ccall` SSA InstrRs.  For chain-level
reasoning, this is the wrong granularity — the *intent* of a
chain is "compute `dst := src² mod p_25519`", not "load source
into register, dispatch Ccall to montmul, store result."

This file provides a **higher-level reflective evaluator**
that captures the chain's intent directly:

```
ChainOp = SqrStep dstOff srcOff
        | MulStep dstOff aOff bOff
        | RepeatedSqrThenMul dstOff srcOff otherOff n
        | InvTail | PowP58Tail

evalChainOp : ChainOp → ChainState → ChainState
```

A `ChainState` is a finite map `OFF → Nat` (modelling the
buffer offsets named in the inv / pow_p58 chains).
`evalChainOp` is a pure function that updates the chain state
according to the abstract chain semantics, computing
multiplication / squaring mod `p_25519` directly.

## Soundness

`invChain_eval_sound` and `powP58Chain_eval_sound` state that the two chains
compute `a ^ (p - 2) % p` and `a ^ ((p - 5) / 8) % p` for every input `a`. The
proof runs the chain on exponents (`Exp.eChain`), shows that the value chain
agrees with the exponent run under `a ^ · % p` (`Exp.evalChain_init_read`), and
checks the resulting exponent equality in the kernel.

The relation between `evalChain` and the SSA body walked by `bignumExecFuel` is
not stated in this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.LowCTReflectiveEval

abbrev p_25519 : Nat := 2^255 - 19

/-! ## §1  Chain offsets

Mirror of `BignumInvP25519`'s `OFF_*` constants, exposed at
top-level, not file-private to `S2NBignumSSA.lean`.

Each offset names a buffer position in the chain's scratch
memory layout.  `OFF_op` and `OFF_ap` have special meaning:
`OFF_op` is the output buffer (offset 0 from the caller's
`op` pointer); `OFF_ap` is the input buffer (a virtual offset
of -1 marking "this is the caller's `ap`, not an `op`-based
offset"). -/

abbrev OFF_op : Int := 0
abbrev OFF_z2 : Int := 32
abbrev OFF_z9 : Int := 64
abbrev OFF_z11 : Int := 96
abbrev OFF_z2_5_0 : Int := 128
abbrev OFF_z2_10_0 : Int := 160
abbrev OFF_z2_20_0 : Int := 192
abbrev OFF_z2_40_0 : Int := 224
abbrev OFF_z2_50_0 : Int := 256
abbrev OFF_z2_100_0 : Int := 288
abbrev OFF_z2_200_0 : Int := 320
abbrev OFF_z2_250_0 : Int := 352
abbrev OFF_ap : Int := -1

/-! ## §2  Chain operations -/

/-- Abstract chain operation.  Each constructor models one step
    of an addition chain over `p_25519`. -/
inductive ChainOp where
  /-- `dst := src² mod p_25519`. -/
  | sqrStep (dstOff srcOff : Int)
  /-- `dst := a · b mod p_25519`. -/
  | mulStep (dstOff aOff bOff : Int)
  /-- `dst := src^(2^n) · other mod p_25519`. -/
  | repeatedSqrThenMul (dstOff srcOff otherOff : Int) (n : Nat)
  deriving Repr, DecidableEq

/-! ## §3  Chain state

Models the per-offset buffer values as a finite map.  In
practice the chain uses ~13 offsets, so a simple list-based
finite map suffices. -/

/-- Chain state: a partial map from offset to the Nat value
    held in that buffer, modulo `p_25519`. -/
abbrev ChainState := List (Int × Nat)

/-- Read the value at a given offset.  Returns 0 if the offset
    is unmapped (the chain assumes all offsets in scope have been
    initialised; callers should ensure this). -/
def ChainState.read : ChainState → Int → Nat
  | [], _ => 0
  | (o, v) :: rest, off => if o = off then v else ChainState.read rest off

/-- Write a value at a given offset.  Overwrites the existing
    binding if present, otherwise prepends. -/
def ChainState.write (cs : ChainState) (off : Int) (v : Nat) :
    ChainState :=
  (off, v) :: cs.eraseP (·.1 = off)

/-- Initialise the chain state from a concrete input value
    (the `ap` buffer's contents).  All other offsets unmapped
    until written. -/
def initChainState (a : Nat) : ChainState :=
  [(OFF_ap, a % p_25519)]

/-! ## §4  Evaluator -/

/-- Evaluate a single chain operation against the chain state. -/
def evalChainOp (op : ChainOp) (cs : ChainState) : ChainState :=
  match op with
  | .sqrStep dst src =>
      let v := cs.read src
      cs.write dst ((v * v) % p_25519)
  | .mulStep dst a b =>
      let va := cs.read a
      let vb := cs.read b
      cs.write dst ((va * vb) % p_25519)
  | .repeatedSqrThenMul dst src other n =>
      let v_src := cs.read src
      let v_other := cs.read other
      let result := (v_src ^ (2^n) * v_other) % p_25519
      cs.write dst result

/-- Evaluate a list of chain operations sequentially. -/
def evalChain : List ChainOp → ChainState → ChainState
  | [], cs => cs
  | op :: rest, cs => evalChain rest (evalChainOp op cs)

/-! ## §5  The inv and pow_p58 chains as `List ChainOp`

The two chains share a 12-block prefix; they differ only in the
final block (13a vs 13b).  This file's reflective evaluator
makes the prefix-sharing structurally evident. -/

/-- Shared 12-block prefix walking `z` to `z^(2²⁵⁰ − 1)`. -/
def prefixChain : List ChainOp :=
  [ .sqrStep OFF_z2 OFF_ap                            -- block 2: z2 = ap²
  , .repeatedSqrThenMul OFF_z9 OFF_z2 OFF_ap 2        -- block 3: z9 = (z2²)² · ap
  , .mulStep OFF_z11 OFF_z9 OFF_z2                    -- block 4: z11 = z9 · z2
  , .repeatedSqrThenMul OFF_z2_5_0 OFF_z11 OFF_z9 1   -- block 5
  , .repeatedSqrThenMul OFF_z2_10_0 OFF_z2_5_0 OFF_z2_5_0 5    -- block 6
  , .repeatedSqrThenMul OFF_z2_20_0 OFF_z2_10_0 OFF_z2_10_0 10 -- block 7
  , .repeatedSqrThenMul OFF_z2_40_0 OFF_z2_20_0 OFF_z2_20_0 20 -- block 8
  , .repeatedSqrThenMul OFF_z2_50_0 OFF_z2_40_0 OFF_z2_10_0 10 -- block 9
  , .repeatedSqrThenMul OFF_z2_100_0 OFF_z2_50_0 OFF_z2_50_0 50    -- block 10
  , .repeatedSqrThenMul OFF_z2_200_0 OFF_z2_100_0 OFF_z2_100_0 100 -- block 11
  , .repeatedSqrThenMul OFF_z2_250_0 OFF_z2_200_0 OFF_z2_50_0 50   -- block 12
  ]

/-- The inv chain: prefix + tail block 13a (`op := z2_250_0^32 · z11`). -/
def invChain : List ChainOp :=
  prefixChain ++
  [ .repeatedSqrThenMul OFF_op OFF_z2_250_0 OFF_z11 5 ]

/-- The pow_p58 chain: prefix + tail block 13b
    (`op := z2_250_0^4 · ap`). -/
def powP58Chain : List ChainOp :=
  prefixChain ++
  [ .repeatedSqrThenMul OFF_op OFF_z2_250_0 OFF_ap 2 ]

/-! ## §6  Headline correctness statements -/

/-- Run the inv chain on input `a` and read the output. -/
def invChainResult (a : Nat) : Nat :=
  (evalChain invChain (initChainState a)).read OFF_op

/-- Run the pow_p58 chain on input `a` and read the output. -/
def powP58ChainResult (a : Nat) : Nat :=
  (evalChain powP58Chain (initChainState a)).read OFF_op

/-! ## §7  Soundness of the chains

`Exp.eChain` runs a chain on exponents instead of values. `Exp.evalChain_init_read`
states that the value chain run from `initChainState a` computes
`a ^ e % p_25519` wherever the exponent run from `[(OFF_ap, 1)]` assigns `e`, so
each chain's soundness is one equality of concrete exponents, checked by the
kernel. -/

namespace Exp

/-- Exponent read: the exponent held at `off`, or `none` if unmapped. -/
def eRead : List (Int × Nat) → Int → Option Nat
  | [], _ => none
  | (o, e) :: rest, off => if o = off then some e else eRead rest off

/-- Exponent semantics of one chain operation. -/
def eOp (op : ChainOp) (es : List (Int × Nat)) : Option (List (Int × Nat)) :=
  match op with
  | .sqrStep dst src => (eRead es src).map fun e => ChainState.write es dst (e * 2)
  | .mulStep dst x y =>
      (eRead es x).bind fun ex => (eRead es y).map fun ey =>
        ChainState.write es dst (ex + ey)
  | .repeatedSqrThenMul dst src other n =>
      (eRead es src).bind fun es_ => (eRead es other).map fun eo =>
        ChainState.write es dst (es_ * 2 ^ n + eo)

/-- Exponent semantics of a chain. -/
def eChain : List ChainOp → List (Int × Nat) → Option (List (Int × Nat))
  | [], es => some es
  | op :: rest, es => (eOp op es).bind (eChain rest)

/-- The value state denoted by an exponent state over base `a` mod `p_25519`. -/
def denote (a : Nat) (es : List (Int × Nat)) : ChainState :=
  es.map fun le => (le.1, a ^ le.2 % p_25519)

theorem read_denote (a : Nat) :
    ∀ (es : List (Int × Nat)) (off : Int) (e : Nat), eRead es off = some e →
      (denote a es).read off = a ^ e % p_25519
  | [], _, _, h => by simp [eRead] at h
  | (o, e') :: rest, off, e, h => by
    by_cases ho : o = off
    · simp_all [eRead, denote, ChainState.read]
    · simp only [eRead, ho, ite_false] at h
      simpa [denote, ChainState.read, ho] using read_denote a rest off e h

theorem write_denote (a : Nat) (es : List (Int × Nat)) (off : Int) (e : Nat) :
    (denote a es).write off (a ^ e % p_25519) = denote a (ChainState.write es off e) := by
  simp [denote, ChainState.write, List.eraseP_map, Function.comp_def]

/-- One chain step commutes with `denote`. -/
theorem evalChainOp_denote (a : Nat) (op : ChainOp) (es es' : List (Int × Nat))
    (h : eOp op es = some es') :
    evalChainOp op (denote a es) = denote a es' := by
  cases op with
  | sqrStep dst src =>
    simp only [eOp, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    simp only [evalChainOp, read_denote a es src e he, ← write_denote]
    rw [← Nat.mul_mod, ← Nat.pow_add, Nat.mul_two]
  | mulStep dst x y =>
    simp only [eOp, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ex, hx, ey, hy, rfl⟩ := h
    simp only [evalChainOp, read_denote a es x ex hx, read_denote a es y ey hy,
      ← write_denote, ← Nat.mul_mod, ← Nat.pow_add]
  | repeatedSqrThenMul dst src other n =>
    simp only [eOp, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨es_, hs, eo, ho, rfl⟩ := h
    simp only [evalChainOp, read_denote a es src es_ hs, read_denote a es other eo ho,
      ← write_denote]
    rw [Nat.mul_mod_mod, ← Nat.mod_mul_mod, ← Nat.pow_mod, Nat.mod_mul_mod,
      Nat.pow_add, Nat.pow_mul]

/-- A chain commutes with `denote` whenever its exponent run succeeds. -/
theorem evalChain_denote (a : Nat) :
    ∀ (ops : List ChainOp) (es es' : List (Int × Nat)), eChain ops es = some es' →
      evalChain ops (denote a es) = denote a es'
  | [], es, es', h => by simp_all [eChain, evalChain]
  | op :: rest, es, es', h => by
    simp only [eChain, Option.bind_eq_some_iff] at h
    obtain ⟨es1, h1, h2⟩ := h
    simp only [evalChain, evalChainOp_denote a op es es1 h1]
    exact evalChain_denote a rest es1 es' h2

/-- Reading `off` after a chain run from `initChainState a` yields
    `a ^ e % p_25519` when the exponent run from `[(OFF_ap, 1)]` assigns
    exponent `e` to `off`. -/
theorem evalChain_init_read (a : Nat) (ops : List ChainOp) (off : Int) (e : Nat)
    (h : (eChain ops [(OFF_ap, 1)]).bind (eRead · off) = some e) :
    (evalChain ops (initChainState a)).read off = a ^ e % p_25519 := by
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨es', h1, h2⟩ := h
  have hinit : initChainState a = denote a [(OFF_ap, 1)] := by
    simp [initChainState, denote]
  rw [hinit, evalChain_denote a ops _ es' h1]
  exact read_denote a es' off e h2

end Exp

/-- The Curve25519 inversion chain computes `a ^ (p_25519 - 2) % p_25519`. -/
theorem invChain_eval_sound (a : Nat) :
    invChainResult a = a ^ (p_25519 - 2) % p_25519 :=
  Exp.evalChain_init_read a invChain OFF_op _ (by decide +kernel)

/-- The Curve25519 `pow_p58` chain computes `a ^ ((p_25519 - 5) / 8) % p_25519`. -/
theorem powP58Chain_eval_sound (a : Nat) :
    powP58ChainResult a = a ^ ((p_25519 - 5) / 8) % p_25519 :=
  Exp.evalChain_init_read a powP58Chain OFF_op _ (by decide +kernel)

/-! ## §8  Concrete-input verification via `decide` / `native_decide`

With the reflective evaluator, concrete-input proofs become
trivial — `vm_compute` runs the chain, `decide` compares the
output to the spec.

This is the fiat-crypto-style closure path. -/

/-- Smoke test: pow_p58 chain on input `a = 2`.  The expected
    output is `2^((p − 5) / 8) mod p` — a specific 256-bit Nat. -/
example :
    powP58ChainResult 2 = 2 ^ ((p_25519 - 5) / 8) % p_25519 :=
  powP58Chain_eval_sound 2

/-! ## §9  What this enables for downstream consumers

Three concrete improvements:

1. **Concrete diff-test discharge**: the bench harness's
   diff-test gets a
   pure Lean reference implementation: run `powP58ChainResult`
   on the test input, compare to the libcrux reference output
   bit-by-bit.  Closes the diff-test gate without needing the
   verified jasminc emit working.

2. **`vm_compute`-friendly chain expansion**: future Layer-A
   variants of the chain (e.g., a different exponent for some
   curve-specific routine) get instant Nat-level closure via
   the same evaluator + a different `chainOps` list.

3. **Decoupling Layer A from Layer B**: the current Layer A in
   `PowP58Algo.lean` uses 12 per-block `decide` proofs; with
   the reflective evaluator, the *full chain* closure becomes
   one application of `powP58Chain_eval_sound` plus an `Eq.refl`
   on the resulting `vm_compute`-able Nat expression.

The reflective evaluator is the **fiat-crypto-style shortcut**
mentioned in the self-review's Appendix A.  ~200 LoC for the
infrastructure (this file); ~50 LoC saved per future chain
that follows the same shape.
-/

end CatCrypt.Crypto.Jasmin.BignumHoare.LowCTReflectiveEval
