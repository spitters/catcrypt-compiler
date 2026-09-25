/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The Poseidon permutation

The permutation of Poseidon (Grassi, Khovratovich, Rechberger, Roy, Schofnegger,
USENIX Security 2021) of width `t` over `ZMod p`, for a record `Params` of the round
counts, the S-box exponent, the round constants and the MDS matrix. Round `k` adds
the round constants, applies `x ↦ x ^ alpha` to every lane in a full round and to
lane `0` in a partial round, and multiplies by the MDS matrix. The first and the last
`fullRounds / 2` rounds are full; the `partialRounds` rounds between them are
partial. This is the round structure of the circomlib reference `poseidon_reference.js`.

`permuteVec` evaluates the same rounds on `Vector (ZMod p) t`, materialising the
S-box layer and the state in every round; `permuteVec_get` states that it computes
`permute`.

## Main definitions

* `Params`: the parameter record.
* `sboxLayer`, `roundFn`: the S-box layer and one round.
* `permute P`: the permutation.
* `permuteVec P`: the permutation on vectors, for known-answer checks.

## Main results

* `permuteVec_get`: `permuteVec` computes `permute`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.Poseidon

/-- The parameters of a Poseidon permutation of width `t` over `ZMod p`. -/
structure Params (p t : Nat) where
  /-- The number of full rounds, half before and half after the partial rounds. -/
  fullRounds : Nat
  /-- The number of partial rounds. -/
  partialRounds : Nat
  /-- The S-box exponent. -/
  alpha : Nat
  /-- The round constant of round `k` at lane `i`. -/
  rc : Nat → Fin t → ZMod p
  /-- The MDS matrix. -/
  mds : Fin t → Fin t → ZMod p

variable {p t : Nat} (P : Params p t)

/-- Round `k` is full when it is among the first or the last `fullRounds / 2`. -/
def Params.isFull (k : Nat) : Bool :=
  k < P.fullRounds / 2 || P.fullRounds / 2 + P.partialRounds ≤ k

/-- The total number of rounds. -/
def Params.rounds : Nat := P.fullRounds + P.partialRounds

/-- The S-box layer of round `k` after the round constants: `x ↦ x ^ alpha` on every
    lane of a full round and on lane `0` of a partial round. -/
def sboxLayer (k : Nat) (s : Fin t → ZMod p) : Fin t → ZMod p :=
  fun j => if P.isFull k || j.val = 0 then (s j + P.rc k j) ^ P.alpha else s j + P.rc k j

/-- Round `k`: the round constants, the S-box layer and the MDS matrix. -/
def roundFn (k : Nat) (s : Fin t → ZMod p) : Fin t → ZMod p :=
  fun i => ∑ j, P.mds i j * sboxLayer P k s j

/-- **The Poseidon permutation**: rounds `0 … rounds - 1` in order. -/
def permute (s : Fin t → ZMod p) : Fin t → ZMod p :=
  (List.range P.rounds).foldl (fun s k => roundFn P k s) s

/-- `permute` on vectors, the S-box layer and the state materialised in every round. -/
def permuteVec (v : Vector (ZMod p) t) : Vector (ZMod p) t :=
  (List.range P.rounds).foldl (fun v k =>
    let w := Vector.ofFn (sboxLayer P k fun i => v[i])
    Vector.ofFn fun i => ∑ j, P.mds i j * w[j]) v

theorem permuteVec_get (v : Vector (ZMod p) t) (i : Fin t) :
    (permuteVec P v)[i] = permute P (fun j => v[j]) i := by
  unfold permuteVec permute
  generalize List.range P.rounds = l
  induction l generalizing v with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact congrArg (fun s => List.foldl (fun s k => roundFn P k s) s l i)
      (funext fun j => by simp [roundFn])

end CatCrypt.Crypto.Hash.Poseidon
