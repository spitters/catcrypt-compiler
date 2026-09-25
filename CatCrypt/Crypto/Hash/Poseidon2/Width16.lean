/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Poseidon2 at width 16, parameterised

The Poseidon2 permutation of Plonky3 at state width 16 over `ZMod p`, for a record
`Params` of the modulus, the S-box degree, the round counts, the round constants and
the internal diagonal. The layers are those of `p3-poseidon2`: an external MDS
pre-mix, `halfFullRounds` external rounds, `partialRounds` internal rounds and
`halfFullRounds` external rounds. An external round adds a constant vector, applies
the S-box `x ↦ x ^ sboxDeg` to every lane and applies the external MDS layer (the
4×4 block `circ(2, 3, 1, 1)` on each group of four lanes, then lane `i` plus the sum
of the lanes congruent to `i` modulo 4). An internal round adds a constant to lane
0, applies the S-box to lane 0 and applies `1·1ᵀ + Diag(diag)`.

`permuteVec` evaluates the same layers on `Vector (ZMod p) 16`, materialising the
state after every layer, so that an evaluation reads each lane of a layer a bounded
number of times; `permuteVec_computes` states that it computes `permute`.

## Main definitions

* `Params`: the parameter record.
* `externalMDS`, `internalMDS`, `externalRound`, `internalRound`: the layers.
* `permute P`: the permutation.
* `permuteNat P`: the permutation on canonical representatives, for known-answer
  checks.

## Main results

* `permuteVec_computes`: `permuteVec` computes `permute`.
* `permuteNat_eq`: `permuteNat` lists the values of `permute`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.Poseidon2.Width16

/-- The parameters of a width-16 Poseidon2 instance over `ZMod p`. -/
structure Params where
  /-- The field modulus. -/
  p : Nat
  /-- The S-box exponent. -/
  sboxDeg : Nat
  /-- The number of external rounds before, and after, the internal rounds. -/
  halfFullRounds : Nat
  /-- The number of internal rounds. -/
  partialRounds : Nat
  /-- The external round constants: rounds `0 .. halfFullRounds - 1` before the
      internal rounds, the rest after. -/
  rcExternal : Fin (2 * halfFullRounds) → Fin 16 → ZMod p
  /-- The internal round constants. -/
  rcInternal : Fin partialRounds → ZMod p
  /-- The diagonal `V` of the internal matrix `1·1ᵀ + Diag(V)`. -/
  diag : Fin 16 → ZMod p

variable (P : Params)

/-- The field of `P`. -/
abbrev F : Type := ZMod P.p

/-- The S-box. -/
def sbox (x : F P) : F P := x ^ P.sboxDeg

/-- The 4×4 external block `circ(2, 3, 1, 1)`. -/
def mat4 {P : Params} (x0 x1 x2 x3 : F P) : Fin 4 → F P :=
  ![2 * x0 + 3 * x1 + x2 + x3, x0 + 2 * x1 + 3 * x2 + x3,
    x0 + x1 + 2 * x2 + 3 * x3, 3 * x0 + x1 + x2 + 2 * x3]

/-- The 4×4 block applied to each group of four lanes. -/
def mdsPre {P : Params} (x : Fin 16 → F P) : Fin 16 → F P := fun i =>
  mat4 (x ⟨4 * (i.val / 4), by omega⟩) (x ⟨4 * (i.val / 4) + 1, by omega⟩)
    (x ⟨4 * (i.val / 4) + 2, by omega⟩) (x ⟨4 * (i.val / 4) + 3, by omega⟩)
    ⟨i.val % 4, by omega⟩

/-- Lane `i` plus the sum of the four lanes congruent to `i` modulo 4. -/
def colSumMap {P : Params} (s : Fin 16 → F P) : Fin 16 → F P := fun i =>
  s i + (s ⟨i.val % 4, by omega⟩ + s ⟨i.val % 4 + 4, by omega⟩ +
    s ⟨i.val % 4 + 8, by omega⟩ + s ⟨i.val % 4 + 12, by omega⟩)

/-- The external MDS layer. -/
def externalMDS {P : Params} (x : Fin 16 → F P) : Fin 16 → F P :=
  colSumMap (mdsPre x)

/-- The sum of the 16 lanes. -/
def sumAll {P : Params} (x : Fin 16 → F P) : F P :=
  x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 +
  x 8 + x 9 + x 10 + x 11 + x 12 + x 13 + x 14 + x 15

/-- The internal MDS layer: lane `i` is `Σ x + diag i · x i`. -/
def internalMDS (x : Fin 16 → F P) : Fin 16 → F P :=
  let s := sumAll x
  fun i => s + P.diag i * x i

/-- One external round: add `c`, S-box on every lane, external MDS. -/
def externalRound (x c : Fin 16 → F P) : Fin 16 → F P :=
  externalMDS fun i => sbox P (x i + c i)

/-- One internal round: add `c` to lane 0, S-box on lane 0, internal MDS. -/
def internalRound (x : Fin 16 → F P) (c : F P) : Fin 16 → F P :=
  internalMDS P fun i => if i.val = 0 then sbox P (x i + c) else x i

/-- The external round constants of the first half, round `r`. -/
def rcInitial (r : Fin P.halfFullRounds) : Fin 16 → F P :=
  P.rcExternal ⟨r.val, by omega⟩

/-- The external round constants of the second half, round `r`. -/
def rcFinal (r : Fin P.halfFullRounds) : Fin 16 → F P :=
  P.rcExternal ⟨P.halfFullRounds + r.val, by omega⟩

/-- **The Poseidon2 permutation.** -/
def permute (x : Fin 16 → F P) : Fin 16 → F P :=
  let s₀ := externalMDS x
  let s₁ := (List.finRange P.halfFullRounds).foldl
    (fun s r => externalRound P s (rcInitial P r)) s₀
  let s₂ := (List.finRange P.partialRounds).foldl
    (fun s r => internalRound P s (P.rcInternal r)) s₁
  (List.finRange P.halfFullRounds).foldl (fun s r => externalRound P s (rcFinal P r)) s₂

/-! ## Evaluation on vectors -/

/-- A state map on vectors computes `g` on the underlying lane functions. -/
def Computes (f : Vector (F P) 16 → Vector (F P) 16) (g : (Fin 16 → F P) → Fin 16 → F P) :
    Prop :=
  ∀ v i, (f v)[i] = g (fun j => v[j]) i

theorem Computes.comp {f₁ f₂ : Vector (F P) 16 → Vector (F P) 16}
    {g₁ g₂ : (Fin 16 → F P) → Fin 16 → F P} (h₁ : Computes P f₁ g₁) (h₂ : Computes P f₂ g₂) :
    Computes P (fun v => f₂ (f₁ v)) (fun x => g₂ (g₁ x)) := by
  intro v i
  rw [h₂]
  congr 1
  funext j
  exact h₁ v j

theorem Computes.ofFn (g : (Fin 16 → F P) → Fin 16 → F P) :
    Computes P (fun v => Vector.ofFn (g fun i => v[i])) g := by
  intro v i
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

theorem Computes.foldl {α : Type} (f : α → Vector (F P) 16 → Vector (F P) 16)
    (g : α → (Fin 16 → F P) → Fin 16 → F P) (h : ∀ a, Computes P (f a) (g a)) :
    ∀ l : List α, Computes P (fun v => l.foldl (fun v a => f a v) v)
      (fun x => l.foldl (fun s a => g a s) x)
  | [] => fun _ _ => rfl
  | a :: l => by
    simp only [List.foldl_cons]
    exact (h a).comp P (Computes.foldl f g h l)

/-- An external round on vectors, the S-box layer, the 4×4 blocks and the column sums
    each materialised. -/
def externalRoundVec (c : Fin 16 → F P) (v : Vector (F P) 16) : Vector (F P) 16 :=
  let stage : ((Fin 16 → F P) → Fin 16 → F P) → Vector (F P) 16 → Vector (F P) 16 :=
    fun g w => Vector.ofFn (g fun i => w[i])
  stage colSumMap (stage mdsPre (stage (fun x i => sbox P (x i + c i)) v))

theorem externalRoundVec_computes (c : Fin 16 → F P) :
    Computes P (externalRoundVec P c) (fun x => externalRound P x c) :=
  fun v i => by
    simp only [externalRoundVec, externalRound, externalMDS, Fin.getElem_fin,
      Vector.getElem_ofFn, Fin.eta]

/-- An internal round on vectors, the lane-0 S-box and the internal layer each
    materialised. -/
def internalRoundVec (c : F P) (v : Vector (F P) 16) : Vector (F P) 16 :=
  let stage : ((Fin 16 → F P) → Fin 16 → F P) → Vector (F P) 16 → Vector (F P) 16 :=
    fun g w => Vector.ofFn (g fun i => w[i])
  stage (internalMDS P) (stage (fun x i => if i.val = 0 then sbox P (x i + c) else x i) v)

theorem internalRoundVec_computes (c : F P) :
    Computes P (internalRoundVec P c) (fun x => internalRound P x c) :=
  fun v i => by
    simp only [internalRoundVec, internalRound, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- The permutation on vectors, each layer materialised. -/
def permuteVec (v : Vector (F P) 16) : Vector (F P) 16 :=
  let v₀ := Vector.ofFn (externalMDS fun i => v[i])
  let v₁ := (List.finRange P.halfFullRounds).foldl
    (fun v r => externalRoundVec P (rcInitial P r) v) v₀
  let v₂ := (List.finRange P.partialRounds).foldl
    (fun v r => internalRoundVec P (P.rcInternal r) v) v₁
  (List.finRange P.halfFullRounds).foldl (fun v r => externalRoundVec P (rcFinal P r) v) v₂

theorem permuteVec_computes : Computes P (permuteVec P) (permute P) :=
  ((((Computes.ofFn P _).comp P
    (Computes.foldl P _ _ (fun r => externalRoundVec_computes P (rcInitial P r)) _)).comp P
    (Computes.foldl P _ _ (fun r => internalRoundVec_computes P (P.rcInternal r)) _)).comp P
    (Computes.foldl P _ _ (fun r => externalRoundVec_computes P (rcFinal P r)) _))

/-- `P` with its round constants and diagonal read from the vectors `rcE`, `rcI`
    and `dg`. It is not inlined, so that its arguments are evaluated once. -/
@[noinline] def withConsts (rcE : Vector (Vector (F P) 16) (2 * P.halfFullRounds))
    (rcI : Vector (F P) P.partialRounds) (dg : Vector (F P) 16) : Params where
  p := P.p
  sboxDeg := P.sboxDeg
  halfFullRounds := P.halfFullRounds
  partialRounds := P.partialRounds
  rcExternal r i := rcE[r][i]
  rcInternal r := rcI[r]
  diag i := dg[i]

/-- `P` with its constants materialised as vectors. -/
def materialise : Params :=
  withConsts P (Vector.ofFn fun r => Vector.ofFn (P.rcExternal r))
    (Vector.ofFn P.rcInternal) (Vector.ofFn P.diag)

theorem materialise_eq : materialise P = P := by
  simp only [materialise, withConsts, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- The permutation on canonical representatives through `permuteVec`: entry `i` of
    `l` (or `0`) is lane `i`, and the result lists the values of the output lanes. -/
def permuteNatAt (l : List Nat) : List Nat :=
  (permuteVec P (Vector.ofFn fun i => ((l.getD i.val 0 : Nat) : F P))).toList.map ZMod.val

/-- `permuteNatAt` with the constants materialised once. -/
def permuteNat (l : List Nat) : List Nat := permuteNatAt (materialise P) l

theorem permuteNat_eq (l : List Nat) :
    permuteNat P l = List.ofFn fun i =>
      (permute P (fun j => ((l.getD j.val 0 : Nat) : F P)) i).val := by
  rw [permuteNat, materialise_eq]
  apply List.ext_getElem
  · simp [permuteNatAt]
  · intro n h₁ h₂
    simp only [permuteNatAt, List.getElem_map, Vector.getElem_toList, List.getElem_ofFn]
    have hn : n < 16 := by simpa using h₂
    have := permuteVec_computes P (Vector.ofFn fun i => ((l.getD i.val 0 : Nat) : F P)) ⟨n, hn⟩
    simp only [Fin.getElem_fin, Vector.getElem_ofFn] at this
    rw [this]

end CatCrypt.Crypto.Hash.Poseidon2.Width16
