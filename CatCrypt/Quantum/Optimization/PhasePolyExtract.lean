/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.PhasePolySemantics
public import CatCrypt.Quantum.Optimization.RotationMergingV2

/-!
# Phase-polynomial extraction against the matrix semantics

`extractPhasePolynomial` reads a `{CNOT, Rz-family}` gate list into a list of
parity-angle terms together with the list of `CNOT`s it met. This module gives
the polynomial a matrix meaning — the `CNOT` network times the product of the
terms' phase diagonals — and identifies it with the unitary of the gate list.

Parities are carried as vectors over `ZMod 2`, where the `CNOT` action is
linear. Two dual actions appear: `zcnot` is the contravariant action on a
parity being pushed through a `CNOT`, and `applyCNOTToParity` is the covariant
action on the extraction's parity state. `netPar_unitZ_eq` is where they meet.

## Main results

* `zPhase_eq_phaseDiag` — a `ZMod 2` parity vector denotes the phase diagonal
  of the `Bool` parity it corresponds to.
* `zPhase_mul_cnot` — a phase diagonal moves right past a `CNOT`, its parity
  vector transformed by `zcnot`.
* `netU_mul_zPhase` — the same across a whole `CNOT` network.
* `zOfList_toggleMember` — `toggleMember` adds the toggled index to the parity
  vector of a list.
* `extractPhasePolynomial_ppUnitary` — the extracted polynomial denotes the
  unitary of the gate list it was read from.
* `termsU_mergeTerms`, `termsU_removeZeroTerms` — merging same-parity terms and
  dropping zero-angle terms leave the product of term phases unchanged.
* `resynthesizeCircuit_circuitUnitary` — resynthesis realizes the polynomial's
  unitary, for terms whose parity lists do not repeat their first entry.
* `extractPhasePolynomial_terms_pairwise` — every parity the extraction records
  is a strictly sorted list, which is that realizability condition.
* `phasePolynomialOpt_unitaryCorrect` — the pass is `UnitaryCorrectQ`.

## References

* Amy, Maslov, Mosca — Polynomial-time T-depth optimization of Clifford+T
  circuits via matroid partitioning, IEEE Trans. on CAD, 2014
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit

noncomputable section

namespace CatCrypt.Quantum.Optimization.PhasePolyExtract

open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.Optimization.PhasePolySemantics
open CatCrypt.Quantum.Optimization.PhasePolynomial (Parity)
open CatCrypt.Quantum.Optimization.RotationMerging (isRzGate isRzFamily)
open CatCrypt.Quantum.Optimization.RotationMergingV2

variable {n : ℕ}

/-! ## Parity vectors over `ZMod 2` -/

/-- A parity as a vector over `ZMod 2`, the representation in which the `CNOT`
    action is linear. -/
abbrev ZPar (n : ℕ) := Fin n → ZMod 2

/-- The parity form of a `ZMod 2` parity vector at a basis index. -/
def zForm (v : ZPar n) (x : ℕ) : ZMod 2 := ∑ i : Fin n, v i * bitZ n i x

/-- The phase diagonal of a `ZMod 2` parity vector. -/
def zPhase (v : ZPar n) (θ : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal fun x => Complex.exp (Complex.I * (θ : ℂ) * ((zForm v x.val).val : ℂ))

/-- The `Bool` parity selecting the indices at which a `ZMod 2` vector is `1`. -/
def ofZ (v : ZPar n) : Parity n := fun i => decide (v i = 1)

/-- The `ZMod 2` vector of a `Bool` parity. -/
def toZ (p : Parity n) : ZPar n := fun i => if p i then 1 else 0

theorem toZ_ofZ (v : ZPar n) : toZ (ofZ v) = v := by
  funext i
  have h : ∀ a : ZMod 2, (if (decide (a = 1) : Bool) = true then (1 : ZMod 2) else 0) = a := by
    decide
  exact h (v i)

theorem zForm_toZ (p : Parity n) (x : ℕ) : zForm (toZ p) x = parityForm p x := by
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : p i <;> simp [toZ, h]

theorem zPhase_toZ (p : Parity n) (θ : ℝ) : zPhase (toZ p) θ = phaseDiag p θ := by
  unfold zPhase phaseDiag
  congr 1
  funext x
  rw [zForm_toZ]

/-- A `ZMod 2` parity vector denotes the phase diagonal of the `Bool` parity it
    corresponds to. -/
theorem zPhase_eq_phaseDiag (v : ZPar n) (θ : ℝ) : zPhase v θ = phaseDiag (ofZ v) θ := by
  rw [← zPhase_toZ, toZ_ofZ]

theorem zPhase_zero_vec (θ : ℝ) : zPhase (0 : ZPar n) θ = 1 := by
  unfold zPhase
  have h : (fun x : Fin (2 ^ n) =>
      Complex.exp (Complex.I * (θ : ℂ) * ((zForm (0 : ZPar n) x.val).val : ℂ)))
      = fun _ : Fin (2 ^ n) => (1 : ℂ) := by
    funext x
    simp [zForm]
  rw [h]
  exact Matrix.diagonal_one

/-- Any two phase diagonals commute. -/
theorem zPhase_comm (v w : ZPar n) (θ φ : ℝ) :
    zPhase v θ * zPhase w φ = zPhase w φ * zPhase v θ := by
  rw [zPhase_eq_phaseDiag, zPhase_eq_phaseDiag]
  exact phaseDiag_comm _ _ _ _

/-! ## The contravariant `CNOT` action -/

/-- The parity vector `v` pushed through a `CNOT` with control `c` and target
    `t`: the `t` component is added into the `c` component. -/
def zcnot (v : ZPar n) (c t : Fin n) : ZPar n := Function.update v c (v c + v t)

/-- The contravariant `CNOT` action, taking a coincident control and target to
    the identity. -/
def zcnotG (v : ZPar n) (c t : Fin n) : ZPar n := if c = t then v else zcnot v c t

theorem ofZ_zcnot (v : ZPar n) (c t : Fin n) :
    ofZ (zcnot v c t) = cnotParity (ofZ v) c t := by
  funext i
  by_cases h : i = c
  · subst h
    have key : ∀ a b : ZMod 2,
        (decide (a + b = 1) : Bool) = xor (decide (a = 1)) (decide (b = 1)) := by decide
    simp only [ofZ, zcnot, Function.update_self, cnotParity_self]
    exact key (v i) (v t)
  · simp only [ofZ, zcnot, Function.update_of_ne h, cnotParity_of_ne h]

theorem zcnot_add (v w : ZPar n) (c t : Fin n) :
    zcnot (v + w) c t = zcnot v c t + zcnot w c t := by
  funext i
  by_cases h : i = c
  · subst h; simp only [zcnot, Function.update_self, Pi.add_apply]; ring
  · simp only [zcnot, Function.update_of_ne h, Pi.add_apply]

theorem zcnotG_add (v w : ZPar n) (c t : Fin n) :
    zcnotG (v + w) c t = zcnotG v c t + zcnotG w c t := by
  unfold zcnotG
  by_cases h : c = t <;> simp [h, zcnot_add]

/-! ## Moving a phase diagonal past a `CNOT` -/

private theorem cnot_embed_sq {c t : Fin n} (hct : c ≠ t) :
    embedGate2 n c t cnot hct * embedGate2 n c t cnot hct = 1 := by
  rw [embedGate2_mul, cnot_sq, embedGate2_one]

/-- A phase diagonal moves to the right of a `CNOT`, its parity vector
    transformed by the contravariant action. -/
theorem zPhase_mul_cnot {c t : Fin n} (hct : c ≠ t) (v : ZPar n) (θ : ℝ) :
    zPhase v θ * embedGate2 n c t cnot hct
      = embedGate2 n c t cnot hct * zPhase (zcnot v c t) θ := by
  have hconj := cnot_conj_phaseDiag hct (ofZ v) θ
  rw [zPhase_eq_phaseDiag, zPhase_eq_phaseDiag, ofZ_zcnot, ← hconj, ← mul_assoc,
    ← mul_assoc, cnot_embed_sq, one_mul]

theorem gateEmbedding_cnot_ne {c t : Fin n} (h : c ≠ t) :
    gateEmbedding (Gate.CNOT c t) = embedGate2 n c t cnot h := by
  simp only [gateEmbedding, dite_eq_right h]

theorem gateEmbedding_cnot_self (c : Fin n) :
    gateEmbedding (Gate.CNOT c c) = 1 := by
  simp only [gateEmbedding, dite_true]

theorem zPhase_mul_gateEmbedding_cnot (c t : Fin n) (v : ZPar n) (θ : ℝ) :
    zPhase v θ * gateEmbedding (Gate.CNOT c t)
      = gateEmbedding (Gate.CNOT c t) * zPhase (zcnotG v c t) θ := by
  by_cases h : c = t
  · subst h
    rw [gateEmbedding_cnot_self, zcnotG, ite_eq_left rfl, mul_one, one_mul]
  · rw [gateEmbedding_cnot_ne h, zcnotG, ite_eq_right h, zPhase_mul_cnot h]

/-! ## The `CNOT` network -/

/-- The gate list of a `CNOT` structure, in application order. -/
def cnotList (cs : List (Fin n × Fin n)) : List (Gate n) :=
  cs.map (fun ct => Gate.CNOT ct.1 ct.2)

/-- The unitary of a `CNOT` structure. -/
def netU (cs : List (Fin n × Fin n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (RoutingPerm.circuitUnitary (Circuit.ofList (cnotList cs))).val

/-- The contravariant action of a `CNOT` structure on a parity vector: the last
    `CNOT` of the structure acts first. -/
def netPar : List (Fin n × Fin n) → ZPar n → ZPar n
  | [], v => v
  | ct :: rest, v => zcnotG (netPar rest v) ct.1 ct.2

@[simp]
theorem netU_nil : netU ([] : List (Fin n × Fin n)) = 1 := rfl

theorem netU_cons (ct : Fin n × Fin n) (cs : List (Fin n × Fin n)) :
    netU (ct :: cs) = netU cs * gateEmbedding (Gate.CNOT ct.1 ct.2) := rfl

theorem netU_append (cs ds : List (Fin n × Fin n)) :
    netU (cs ++ ds) = netU ds * netU cs := by
  unfold netU cnotList
  rw [List.map_append, circuitUnitary_ofList_append]
  rfl

theorem netPar_append (cs ds : List (Fin n × Fin n)) (v : ZPar n) :
    netPar (cs ++ ds) v = netPar cs (netPar ds v) := by
  induction cs with
  | nil => rfl
  | cons ct rest ih => simp only [List.cons_append, netPar, ih]

/-- A phase diagonal moves to the right of a whole `CNOT` network. -/
theorem netU_mul_zPhase (cs : List (Fin n × Fin n)) (v : ZPar n) (θ : ℝ) :
    zPhase v θ * netU cs = netU cs * zPhase (netPar cs v) θ := by
  induction cs with
  | nil => simp [netPar]
  | cons ct rest ih =>
    rw [netU_cons, ← mul_assoc, ih, mul_assoc, zPhase_mul_gateEmbedding_cnot,
      ← mul_assoc, netPar]

theorem netPar_add (cs : List (Fin n × Fin n)) (v w : ZPar n) :
    netPar cs (v + w) = netPar cs v + netPar cs w := by
  induction cs with
  | nil => rfl
  | cons ct rest ih => simp only [netPar, ih, zcnotG_add]

/-! ## Parity vectors of index lists -/

/-- The parity vector selecting exactly one index. -/
def unitZ (q : Fin n) : ZPar n := fun i => if i = q then 1 else 0

/-- The parity vector of a list of indices: the sum of their unit vectors, so
    an index contributes according to the parity of its multiplicity. -/
def zOfList : List (Fin n) → ZPar n
  | [] => 0
  | a :: l => unitZ a + zOfList l

theorem zpar_add_self (v : ZPar n) : v + v = 0 := by
  funext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  simpa using h (v i)

/-- `toggleMember` adds the toggled index to the parity vector of a list. -/
theorem zOfList_toggleMember (q : Fin n) (l : List (Fin n)) :
    zOfList (toggleMember q l) = unitZ q + zOfList l := by
  induction l with
  | nil => simp [toggleMember, zOfList]
  | cons a rest ih =>
    rw [toggleMember]
    by_cases h : (q == a) = true
    · rw [ite_eq_left h]
      have hqa : q = a := by simpa using h
      subst hqa
      rw [zOfList, ← add_assoc, zpar_add_self, zero_add]
    · rw [ite_eq_right h]
      by_cases h2 : (compare q a == Ordering.lt) = true
      · rw [ite_eq_left h2, zOfList]
      · rw [ite_eq_right h2, zOfList, ih, zOfList]
        ring

theorem zOfList_foldl_toggle (l base : List (Fin n)) :
    zOfList (l.foldl (fun acc q => toggleMember q acc) base)
      = zOfList l + zOfList base := by
  induction l generalizing base with
  | nil => simp [zOfList]
  | cons a rest ih =>
    rw [List.foldl_cons, ih, zOfList_toggleMember, zOfList]
    ring

/-! ## The covariant parity state -/

/-- The parity vector each wire of an extraction parity state carries. -/
def psZ (ps : ParityState n) : Fin n → ZPar n := fun i => zOfList (ps i)

theorem psZ_init (q : Fin n) : psZ (initParityState n) q = unitZ q := by
  simp [psZ, initParityState, zOfList]

theorem applyCNOTToParity_self (ps : ParityState n) (c : Fin n) :
    applyCNOTToParity ps c c = ps := by
  simp [applyCNOTToParity]

theorem psZ_applyCNOTToParity {c t : Fin n} (hct : c ≠ t) (ps : ParityState n)
    (i : Fin n) :
    psZ (applyCNOTToParity ps c t) i
      = if i = t then psZ ps t + psZ ps c else psZ ps i := by
  have hbeq : (c == t) = false := by simpa using hct
  by_cases hit : i = t
  · subst hit
    simp [psZ, applyCNOTToParity, hbeq, zOfList_foldl_toggle, add_comm]
  · simp [psZ, applyCNOTToParity, hbeq, hit]

/-! ## Where the two actions meet -/

theorem zcnotG_unitZ_of_ne {c t q : Fin n} (hqt : q ≠ t) :
    zcnotG (unitZ q) c t = unitZ q := by
  unfold zcnotG
  by_cases hct : c = t
  · rw [ite_eq_left hct]
  · rw [ite_eq_right hct]
    unfold zcnot
    have h0 : unitZ q t = 0 := by simp [unitZ, Ne.symm hqt]
    rw [h0, add_zero, Function.update_eq_self]

theorem zcnotG_unitZ_of_eq {c t : Fin n} (hct : c ≠ t) :
    zcnotG (unitZ t) c t = unitZ t + unitZ c := by
  unfold zcnotG zcnot
  rw [ite_eq_right hct]
  funext i
  have hc : unitZ (n := n) t c = 0 := by simp [unitZ, hct]
  have ht : unitZ (n := n) t t = 1 := by simp [unitZ]
  by_cases hic : i = c
  · subst hic
    simp [Function.update_self, unitZ]
  · simp [unitZ, hic]

/-! ## Rz-family gates as `Rz` matrices

The identities `tGate_eq_rzGate`, `tDaggerGate_eq_rzGate`, `phaseS_eq_rzGate` and
`pauliZ_eq_rzGate` are in `GateUnitarity`. -/

/-- A gate recognised by `isRzGate` embeds as the `Rz` matrix it stands for. -/
theorem isRzGate_gateEmbedding {g : Gate n} {q : Fin n} {θ : ℝ}
    (h : isRzGate g = some (q, θ)) :
    gateEmbedding g = embedGate1 n q (rzGate θ) := by
  cases g with
  | Z i =>
    simp only [isRzGate, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hq, hθ⟩ := h; subst hq; subst hθ
    simp only [gateEmbedding, pauliZ_eq_rzGate]
  | T i =>
    simp only [isRzGate, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hq, hθ⟩ := h; subst hq; subst hθ
    simp only [gateEmbedding, tGate_eq_rzGate]
  | Tdg i =>
    simp only [isRzGate, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hq, hθ⟩ := h; subst hq; subst hθ
    simp only [gateEmbedding, tDaggerGate_eq_rzGate]
  | S i =>
    simp only [isRzGate, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hq, hθ⟩ := h; subst hq; subst hθ
    simp only [gateEmbedding, phaseS_eq_rzGate]
  | Rz i α =>
    simp only [isRzGate, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hq, hθ⟩ := h; subst hq; subst hθ
    rfl
  | H i => simp [isRzGate] at h
  | RzQ i a =>
    simp only [isRzGate, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hq, hθ⟩ := h; subst hq; subst hθ
    rfl
  | X i => simp [isRzGate] at h
  | Y i => simp [isRzGate] at h
  | CNOT c t => simp [isRzGate] at h
  | CZ c t => simp [isRzGate] at h

/-- The embedded matrix of an `Rz`-family gate is the phase diagonal of the
    singleton parity vector at its wire. -/
theorem isRzGate_zPhase {g : Gate n} {q : Fin n} {θ : ℝ}
    (h : isRzGate g = some (q, θ)) :
    gateEmbedding g = zPhase (unitZ q) θ := by
  rw [isRzGate_gateEmbedding h, rz_embed_eq_phaseDiag, ← zPhase_toZ]
  congr 1
  funext i
  simp [toZ, unitZ, singletonParity]

theorem isPhasePolyGate_cases {g : Gate n} (h : isPhasePolyGate g = true) :
    (∃ q θ, isRzGate g = some (q, θ)) ∨ (∃ c t, g = Gate.CNOT c t) := by
  cases g <;>
    first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩
      | simp [isPhasePolyGate, isRzFamily] at h

/-! ## The matrix meaning of a phase polynomial -/

/-- The product of the phase diagonals of a term list. -/
def termsU : List (ParityTerm n) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | [] => 1
  | t :: ts => zPhase (zOfList t.parity) t.angle * termsU ts

/-- The unitary a phase polynomial denotes: its `CNOT` network times the
    product of its terms' phase diagonals. -/
def ppUnitary (pp : PhasePolynomial n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  netU pp.cnots * termsU pp.terms

theorem termsU_append (ts us : List (ParityTerm n)) :
    termsU (ts ++ us) = termsU ts * termsU us := by
  induction ts with
  | nil => simp [termsU]
  | cons t ts ih => simp only [List.cons_append, termsU, ih, mul_assoc]

theorem zPhase_mul_termsU (v : ZPar n) (θ : ℝ) (ts : List (ParityTerm n)) :
    zPhase v θ * termsU ts = termsU ts * zPhase v θ := by
  induction ts with
  | nil => simp [termsU]
  | cons t ts ih =>
    simp only [termsU, ← mul_assoc, zPhase_comm v (zOfList t.parity) θ t.angle]
    simp only [mul_assoc, ih]

theorem netU_singleton (ct : Fin n × Fin n) :
    netU [ct] = gateEmbedding (Gate.CNOT ct.1 ct.2) := by
  rw [netU_cons, netU_nil, one_mul]

theorem netPar_singleton (ct : Fin n × Fin n) (v : ZPar n) :
    netPar [ct] v = zcnotG v ct.1 ct.2 := rfl

/-! ## The extraction invariant -/

/-- The accumulator invariant of `extractPhasePolynomial.go`: with the linear
    part recorded by `cnots` matching the parity state `ps`, the polynomial the
    fold returns denotes the gate list's unitary composed with the unitary the
    accumulators already denote. -/
theorem go_ppUnitary : ∀ (gs : List (Gate n)) (ps : ParityState n)
    (terms : List (ParityTerm n)) (cnots : List (Fin n × Fin n)),
    (∀ g ∈ gs, isPhasePolyGate g = true) →
    (∀ q, netPar cnots.reverse (unitZ q) = psZ ps q) →
    ppUnitary (extractPhasePolynomial.go gs ps terms cnots)
      = (RoutingPerm.circuitUnitary (Circuit.ofList gs)).val *
          (netU cnots.reverse * termsU terms.reverse) := by
  intro gs
  induction gs with
  | nil =>
    intro ps terms cnots _ _
    show netU cnots.reverse * termsU terms.reverse
        = (RoutingPerm.circuitUnitary (Circuit.ofList ([] : List (Gate n)))).val * _
    rw [show (RoutingPerm.circuitUnitary (Circuit.ofList ([] : List (Gate n)))).val
        = 1 from rfl, one_mul]
  | cons g rest ih =>
    intro ps terms cnots hgs hinv
    have hg : isPhasePolyGate g = true := hgs g (List.mem_cons_self ..)
    have hrest : ∀ g' ∈ rest, isPhasePolyGate g' = true :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    have hU : (RoutingPerm.circuitUnitary (Circuit.ofList (g :: rest))).val
        = (RoutingPerm.circuitUnitary (Circuit.ofList rest)).val * gateEmbedding g := rfl
    rcases isPhasePolyGate_cases hg with ⟨q, θ, hrz⟩ | ⟨c, t, hgct⟩
    · have hstep : extractPhasePolynomial.go (g :: rest) ps terms cnots
          = extractPhasePolynomial.go rest ps (⟨ps q, θ⟩ :: terms) cnots := by
        simp only [extractPhasePolynomial.go, hrz]
      have h2 : zPhase (unitZ q) θ * netU cnots.reverse
          = netU cnots.reverse * zPhase (zOfList (ps q)) θ := by
        rw [netU_mul_zPhase, hinv q]
        rfl
      have key : gateEmbedding g * (netU cnots.reverse * termsU terms.reverse)
          = netU cnots.reverse * (termsU terms.reverse * zPhase (zOfList (ps q)) θ) := by
        calc gateEmbedding g * (netU cnots.reverse * termsU terms.reverse)
            = zPhase (unitZ q) θ * netU cnots.reverse * termsU terms.reverse := by
              rw [isRzGate_zPhase hrz, mul_assoc]
          _ = netU cnots.reverse * zPhase (zOfList (ps q)) θ * termsU terms.reverse := by
              rw [h2]
          _ = netU cnots.reverse * (zPhase (zOfList (ps q)) θ * termsU terms.reverse) := by
              rw [mul_assoc]
          _ = netU cnots.reverse * (termsU terms.reverse * zPhase (zOfList (ps q)) θ) := by
              rw [zPhase_mul_termsU]
      rw [hstep, ih ps _ cnots hrest hinv, hU, List.reverse_cons, termsU_append,
        mul_assoc, key]
      simp [termsU]
    · subst hgct
      have hstep : extractPhasePolynomial.go (Gate.CNOT c t :: rest) ps terms cnots
          = extractPhasePolynomial.go rest (applyCNOTToParity ps c t) terms
              ((c, t) :: cnots) := by
        simp only [extractPhasePolynomial.go, isRzGate]
      have hinv' : ∀ q, netPar ((c, t) :: cnots).reverse (unitZ q)
          = psZ (applyCNOTToParity ps c t) q := by
        intro q
        rw [List.reverse_cons, netPar_append, netPar_singleton]
        by_cases hct : c = t
        · subst hct
          rw [applyCNOTToParity_self, zcnotG, ite_eq_left rfl]
          exact hinv q
        · rw [psZ_applyCNOTToParity hct]
          by_cases hqt : q = t
          · subst hqt
            rw [zcnotG_unitZ_of_eq hct, netPar_add, hinv, hinv, ite_eq_left rfl]
          · rw [zcnotG_unitZ_of_ne hqt, hinv, ite_eq_right hqt]
      rw [hstep, ih _ terms _ hrest hinv', hU, List.reverse_cons, netU_append,
        netU_singleton]
      simp only [mul_assoc]

/-- Extraction preserves the unitary: on a gate list from the `{CNOT,
    Rz-family}` fragment, the extracted phase polynomial denotes the unitary of
    the list. -/
theorem extractPhasePolynomial_ppUnitary (gs : List (Gate n))
    (hgs : ∀ g ∈ gs, isPhasePolyGate g = true) :
    ppUnitary (extractPhasePolynomial gs)
      = (RoutingPerm.circuitUnitary (Circuit.ofList gs)).val := by
  have h := go_ppUnitary gs (initParityState n) [] [] hgs (fun q => (psZ_init q).symm)
  simpa [extractPhasePolynomial, termsU] using h

/-! ## Angle algebra on the term product -/

theorem zPhase_add (v : ZPar n) (θ₁ θ₂ : ℝ) :
    zPhase v (θ₁ + θ₂) = zPhase v θ₁ * zPhase v θ₂ := by
  rw [zPhase_eq_phaseDiag, zPhase_eq_phaseDiag, zPhase_eq_phaseDiag, phaseDiag_mul]

theorem zPhase_angle_zero (v : ZPar n) : zPhase v 0 = 1 := by
  rw [zPhase_eq_phaseDiag, phaseDiag_zero]

/-- The term product depends only on the multiset of terms. -/
theorem termsU_perm {ts us : List (ParityTerm n)} (h : ts.Perm us) :
    termsU ts = termsU us := by
  induction h with
  | nil => rfl
  | cons t _ ih => simp only [termsU, ih]
  | swap t u l => simp only [termsU, ← mul_assoc, zPhase_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem removeZeroTerms_cons_of_ne {t : ParityTerm n} (h : t.angle ≠ 0)
    (ts : List (ParityTerm n)) :
    removeZeroTerms (t :: ts) = t :: removeZeroTerms ts := by
  rw [removeZeroTerms, List.filter_cons]
  split
  · rfl
  · rename_i hc
    exact absurd (show (!(decide (t.angle = 0))) = true by simp [h]) hc

theorem removeZeroTerms_cons_of_eq {t : ParityTerm n} (h : t.angle = 0)
    (ts : List (ParityTerm n)) :
    removeZeroTerms (t :: ts) = removeZeroTerms ts := by
  rw [removeZeroTerms, List.filter_cons]
  split
  · rename_i hc
    exact absurd hc (show ¬((!(decide (t.angle = 0))) = true) by simp [h])
  · rfl

/-- Dropping a zero-angle term leaves the term product unchanged. -/
theorem termsU_removeZeroTerms (ts : List (ParityTerm n)) :
    termsU (removeZeroTerms ts) = termsU ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t.angle = 0
    · rw [removeZeroTerms_cons_of_eq h, ih, termsU, h, zPhase_angle_zero, one_mul]
    · rw [removeZeroTerms_cons_of_ne h, termsU, termsU, ih]

/-! ## Realizing a term as a `CNOT` ladder -/

theorem ofZ_toZ (p : Parity n) : ofZ (toZ p) = p := by
  funext i
  cases h : p i <;> simp [ofZ, toZ, h]

theorem toZ_cnotParity (p : Parity n) (c t : Fin n) :
    toZ (cnotParity p c t) = zcnot (toZ p) c t := by
  conv_lhs => rw [← ofZ_toZ p]
  rw [← ofZ_zcnot, toZ_ofZ]

theorem zOfList_apply_of_not_mem {q : Fin n} :
    ∀ {l : List (Fin n)}, q ∉ l → zOfList l q = 0
  | [], _ => rfl
  | a :: rest, h => by
      have hqa : q ≠ a := fun h' => h (h' ▸ List.mem_cons_self ..)
      have hrest : q ∉ rest := fun h' => h (List.mem_cons_of_mem a h')
      show unitZ a q + zOfList rest q = 0
      rw [zOfList_apply_of_not_mem hrest, add_zero]
      simp [unitZ, hqa]

/-- The ladder parity of a control list avoiding the rotation wire is the parity
    vector of that wire together with the controls. -/
theorem toZ_ladderParity (q : Fin n) :
    ∀ l : List (Fin n), (∀ r ∈ l, r ≠ q) → toZ (ladderParity q l) = zOfList (q :: l) := by
  intro l
  induction l with
  | nil =>
    intro _
    funext i
    simp [ladderParity, singletonParity, toZ, zOfList, unitZ]
  | cons r rest ih =>
    intro hq
    have hrq : r ≠ q := hq r (List.mem_cons_self ..)
    have hrest : ∀ s ∈ rest, s ≠ q := fun s hs => hq s (List.mem_cons_of_mem r hs)
    have hqnot : q ∉ rest := fun h => (hrest q h) rfl
    show toZ (cnotParity (ladderParity q rest) r q) = _
    rw [toZ_cnotParity, ih hrest]
    funext i
    have hqval : zOfList (q :: rest) q = 1 := by
      show unitZ q q + zOfList rest q = 1
      rw [zOfList_apply_of_not_mem hqnot, add_zero]
      simp [unitZ]
    by_cases hir : i = r
    · rw [hir]
      simp only [zcnot, Function.update_self, hqval]
      show unitZ q r + zOfList rest r + 1 = unitZ q r + (unitZ r r + zOfList rest r)
      have h1 : unitZ (n := n) r r = 1 := by simp [unitZ]
      rw [h1]
      ring
    · simp only [zcnot, Function.update_of_ne hir]
      show unitZ q i + zOfList rest i = unitZ q i + (unitZ r i + zOfList rest i)
      have h0 : unitZ (n := n) r i = 0 := by simp [unitZ, hir]
      rw [h0, zero_add]

/-- A parity term is realizable by a `CNOT` ladder when no entry after the first
    repeats the first. -/
def TermWF (t : ParityTerm n) : Prop :=
  ∀ q rest, t.parity = q :: rest → ∀ r ∈ rest, r ≠ q

theorem termToGates_circuitUnitary {t : ParityTerm n} (h : TermWF t) :
    (RoutingPerm.circuitUnitary (Circuit.ofList (termToGates t))).val
      = zPhase (zOfList t.parity) t.angle := by
  unfold termToGates
  match hp : t.parity with
  | [] =>
    show (RoutingPerm.circuitUnitary (Circuit.ofList ([] : List (Gate n)))).val = _
    rw [show (RoutingPerm.circuitUnitary (Circuit.ofList ([] : List (Gate n)))).val
        = 1 from rfl]
    rw [show zOfList ([] : List (Fin n)) = 0 from rfl, zPhase_zero_vec]
  | q :: rest =>
    have hr := h q rest hp
    show (RoutingPerm.circuitUnitary (Circuit.ofList (cnotLadder q rest t.angle))).val = _
    rw [cnotLadder_circuitUnitary q t.angle rest hr, ← zPhase_toZ,
      toZ_ladderParity q rest hr]

theorem phaseGates_circuitUnitary :
    ∀ ts : List (ParityTerm n), (∀ t ∈ ts, TermWF t) →
      (RoutingPerm.circuitUnitary (Circuit.ofList (ts.flatMap termToGates))).val
        = termsU ts := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons t ts ih =>
    intro h
    have ht : TermWF t := h t (List.mem_cons_self ..)
    have hts : ∀ u ∈ ts, TermWF u := fun u hu => h u (List.mem_cons_of_mem t hu)
    rw [List.flatMap_cons, circuitUnitary_ofList_append]
    show (RoutingPerm.circuitUnitary (Circuit.ofList (ts.flatMap termToGates))).val *
      (RoutingPerm.circuitUnitary (Circuit.ofList (termToGates t))).val = _
    rw [ih hts, termToGates_circuitUnitary ht, termsU, zPhase_mul_termsU]

/-- Resynthesis realizes the polynomial's unitary, provided each term's parity
    list does not repeat its first entry. -/
theorem resynthesizeCircuit_circuitUnitary (pp : PhasePolynomial n)
    (h : ∀ t ∈ pp.terms, TermWF t) :
    (RoutingPerm.circuitUnitary (Circuit.ofList (resynthesizeCircuit pp))).val
      = ppUnitary pp := by
  unfold resynthesizeCircuit ppUnitary
  rw [circuitUnitary_ofList_append]
  show netU pp.cnots *
      (RoutingPerm.circuitUnitary (Circuit.ofList (pp.terms.flatMap termToGates))).val = _
  rw [phaseGates_circuitUnitary _ h]

/-! ## Merging same-parity terms -/

/-- The phase diagonal a parity term denotes. -/
def termPhase (t : ParityTerm n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  zPhase (zOfList t.parity) t.angle

theorem termPhase_eq_termsU (t : ParityTerm n) : termPhase t = termsU [t] :=
  (mul_one _).symm

theorem termsU_mul_comm (l₁ l₂ : List (ParityTerm n)) :
    termsU l₁ * termsU l₂ = termsU l₂ * termsU l₁ := by
  rw [← termsU_append, ← termsU_append]
  exact termsU_perm List.perm_append_comm

/-- One step of the merge scan: the first term of the accumulator whose parity
    matches absorbs the angle, and the flag records that it did. -/
def mergeStep (t : ParityTerm n) :
    List (ParityTerm n) × Bool → ParityTerm n → List (ParityTerm n) × Bool :=
  fun p t' =>
    if !p.2 && (t.parity == t'.parity) then
      (⟨t'.parity, t'.angle + t.angle⟩ :: p.1, true)
    else (t' :: p.1, p.2)

theorem mergeTerms_go_nil (acc : List (ParityTerm n)) :
    mergeTerms.go [] acc = acc.reverse := rfl

theorem mergeTerms_go_cons (t : ParityTerm n) (rest acc : List (ParityTerm n)) :
    mergeTerms.go (t :: rest) acc
      = if (acc.foldl (mergeStep t) ([], false)).2 then
          mergeTerms.go rest (acc.foldl (mergeStep t) ([], false)).1.reverse
        else mergeTerms.go rest (t :: acc) := rfl

theorem mergeTerms_eq_go (ts : List (ParityTerm n)) :
    mergeTerms ts = mergeTerms.go ts [] := rfl

theorem termsU_cons (u : ParityTerm n) (l : List (ParityTerm n)) :
    termsU (u :: l) = termPhase u * termsU l := rfl

private theorem perm_append_singleton (l : List (ParityTerm n)) (u : ParityTerm n) :
    (l ++ [u]).Perm (u :: l) := by
  simp

/-- The merge scan carries the pending term's phase through the accumulator:
    either it has been absorbed into a matching term, or it is still pending. -/
theorem mergeStep_foldl_termsU (t : ParityTerm n) :
    ∀ (l a0 : List (ParityTerm n)) (b0 : Bool),
      termsU (List.foldl (mergeStep t) (a0, b0) l).1 *
          (if (List.foldl (mergeStep t) (a0, b0) l).2 then 1 else termPhase t)
        = termsU a0 * termsU l * (if b0 then 1 else termPhase t) := by
  intro l
  induction l with
  | nil => intro a0 b0; cases b0 <;> simp [termsU]
  | cons t' rest ih =>
    intro a0 b0
    rw [List.foldl_cons]
    by_cases hc : (!b0 && (t.parity == t'.parity)) = true
    · have hb0 : b0 = false := by
        cases b0
        · rfl
        · simp at hc
      have hpar : t.parity = t'.parity := by
        rw [hb0] at hc; simpa using hc
      have hstep : mergeStep t (a0, b0) t'
          = ((⟨t'.parity, t'.angle + t.angle⟩ : ParityTerm n) :: a0, true) := by
        simp only [mergeStep, ite_eq_left hc]
      have hmp : termPhase (⟨t'.parity, t'.angle + t.angle⟩ : ParityTerm n)
          = termPhase t' * termPhase t := by
        simp only [termPhase]
        rw [zPhase_add, hpar]
      rw [hstep, ih _ true, hb0]
      simp only [ite_true, reduceIte, Bool.false_eq_true, mul_one, termsU_cons, hmp]
      simp only [termPhase_eq_termsU, ← termsU_append]
      refine termsU_perm ?_
      refine ((List.Perm.append_right [t]
        (List.perm_middle (a := t') (l₁ := a0) (l₂ := rest))).trans
          (List.Perm.cons t' (perm_append_singleton (a0 ++ rest) t))).symm
    · have hstep : mergeStep t (a0, b0) t' = (t' :: a0, b0) := by
        simp only [mergeStep, ite_eq_right hc]
      rw [hstep, ih _ b0]
      congr 1
      rw [termsU_cons, termsU_cons, termPhase_eq_termsU]
      simp only [← termsU_append]
      exact termsU_perm List.perm_middle.symm

theorem mergeTerms_go_termsU : ∀ l acc : List (ParityTerm n),
    termsU (mergeTerms.go l acc) = termsU l * termsU acc := by
  intro l
  induction l with
  | nil =>
    intro acc
    rw [mergeTerms_go_nil, termsU_perm (List.reverse_perm acc)]
    show _ = termsU ([] : List (ParityTerm n)) * termsU acc
    rw [show termsU ([] : List (ParityTerm n)) = 1 from rfl, one_mul]
  | cons t rest ih =>
    intro acc
    rw [mergeTerms_go_cons]
    have hspec := mergeStep_foldl_termsU t acc [] false
    by_cases hf : (List.foldl (mergeStep t) ([], false) acc).2 = true
    · rw [ite_eq_left hf, ih, termsU_perm (List.reverse_perm _)]
      rw [hf] at hspec
      simp only [ite_true, reduceIte, Bool.false_eq_true, mul_one, show termsU ([] : List (ParityTerm n)) = 1 from rfl,
        one_mul] at hspec
      rw [hspec, termsU_cons, termPhase_eq_termsU]
      simp only [← termsU_append]
      refine termsU_perm ?_
      rw [← List.append_assoc]
      simpa using perm_append_singleton (rest ++ acc) t
    · rw [ite_eq_right hf, ih]
      rw [termsU_cons, termsU_cons, termPhase_eq_termsU]
      simp only [← termsU_append]
      exact termsU_perm List.perm_middle

/-- Merging same-parity terms leaves the term product unchanged. -/
theorem termsU_mergeTerms (ts : List (ParityTerm n)) :
    termsU (mergeTerms ts) = termsU ts := by
  rw [mergeTerms_eq_go, mergeTerms_go_termsU,
    show termsU ([] : List (ParityTerm n)) = 1 from rfl, mul_one]

/-! ## Sorted parity lists -/

/-- Every entry of `toggleMember x l` is either `x` or an entry of `l`. -/
theorem mem_toggleMember (x : Fin n) :
    ∀ (l : List (Fin n)) {y : Fin n}, y ∈ toggleMember x l → y = x ∨ y ∈ l := by
  intro l
  induction l with
  | nil => intro y h; simpa [toggleMember] using h
  | cons a rest ih =>
    intro y h
    rw [toggleMember] at h
    split at h
    · exact Or.inr (List.mem_cons_of_mem a h)
    · split at h
      · rcases List.mem_cons.mp h with h1 | h2
        · exact Or.inl h1
        · exact Or.inr h2
      · rcases List.mem_cons.mp h with h1 | h2
        · exact Or.inr (h1 ▸ List.mem_cons_self ..)
        · rcases ih h2 with h3 | h4
          · exact Or.inl h3
          · exact Or.inr (List.mem_cons_of_mem a h4)

/-- `toggleMember` preserves strict sortedness. -/
theorem toggleMember_sorted (x : Fin n) :
    ∀ l : List (Fin n), l.Pairwise (· < ·) → (toggleMember x l).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _; simp [toggleMember]
  | cons a rest ih =>
    intro h
    have hrest : rest.Pairwise (· < ·) := (List.pairwise_cons.mp h).2
    have hlt : ∀ b ∈ rest, a < b := (List.pairwise_cons.mp h).1
    rw [toggleMember]
    split
    · exact hrest
    · rename_i hne
      have hxa : x ≠ a := by simpa using hne
      split
      · rename_i hc
        have hlt' : x < a := compare_lt_iff_lt.mp (by simpa using hc)
        refine List.pairwise_cons.mpr ⟨?_, h⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hlt'
        · exact hlt'.trans (hlt b hb')
      · rename_i hc
        have hax : a < x := by
          have hnlt : ¬ (x < a) := fun hl => hc (by simpa using compare_lt_iff_lt.mpr hl)
          omega
        refine List.pairwise_cons.mpr ⟨?_, ih hrest⟩
        intro b hb
        rcases mem_toggleMember x rest hb with rfl | hb'
        · exact hax
        · exact hlt b hb'

/-- Toggling a list of indices into a sorted list keeps it sorted. -/
theorem foldl_toggleMember_sorted (l : List (Fin n)) :
    ∀ base : List (Fin n), base.Pairwise (· < ·) →
      (l.foldl (fun acc q => toggleMember q acc) base).Pairwise (· < ·) := by
  induction l with
  | nil => intro base h; exact h
  | cons a rest ih => intro base h; exact ih _ (toggleMember_sorted a base h)

theorem initParityState_sorted (i : Fin n) : (initParityState n i).Pairwise (· < ·) := by
  simp [initParityState]

/-- A `CNOT` step keeps every wire's parity list sorted. -/
theorem applyCNOTToParity_sorted {ps : ParityState n}
    (h : ∀ i, (ps i).Pairwise (· < ·)) (c t : Fin n) :
    ∀ i, (applyCNOTToParity ps c t i).Pairwise (· < ·) := by
  intro i
  by_cases hct : (c == t) = true
  · simp only [applyCNOTToParity, hct, ↓reduceIte]; exact h i
  · simp only [applyCNOTToParity, hct, Bool.false_eq_true, ↓reduceIte]
    by_cases hit : (i == t) = true
    · simp only [hit, ↓reduceIte]; exact foldl_toggleMember_sorted _ _ (h t)
    · simp only [hit, Bool.false_eq_true, ↓reduceIte]; exact h i

/-- A term whose parity list is strictly sorted is realizable by a `CNOT`
    ladder. -/
theorem termWF_of_sorted {t : ParityTerm n} (h : t.parity.Pairwise (· < ·)) : TermWF t := by
  intro q rest hp r hr
  rw [hp] at h
  exact ((List.pairwise_cons.mp h).1 r hr).ne'

/-! ## Sortedness through the pipeline -/

/-- Every parity the extraction fold records is a sorted list, given a sorted
    starting parity state and sorted accumulated terms. -/
theorem go_terms_pairwise : ∀ (gs : List (Gate n)) (ps : ParityState n)
    (terms : List (ParityTerm n)) (cnots : List (Fin n × Fin n)),
    (∀ g ∈ gs, isPhasePolyGate g = true) →
    (∀ i, (ps i).Pairwise (· < ·)) →
    (∀ u ∈ terms, u.parity.Pairwise (· < ·)) →
    ∀ u ∈ (extractPhasePolynomial.go gs ps terms cnots).terms,
      u.parity.Pairwise (· < ·) := by
  intro gs
  induction gs with
  | nil =>
    intro ps terms cnots _ _ hterms u hu
    have hgo : (extractPhasePolynomial.go ([] : List (Gate n)) ps terms cnots).terms
        = terms.reverse := rfl
    rw [hgo, List.mem_reverse] at hu
    exact hterms u hu
  | cons g rest ih =>
    intro ps terms cnots hgs hps hterms
    have hrest : ∀ g' ∈ rest, isPhasePolyGate g' = true :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    rcases isPhasePolyGate_cases (hgs g (List.mem_cons_self ..)) with ⟨q, θ, hrz⟩ | ⟨c, t, hgct⟩
    · have hstep : extractPhasePolynomial.go (g :: rest) ps terms cnots
          = extractPhasePolynomial.go rest ps (⟨ps q, θ⟩ :: terms) cnots := by
        simp only [extractPhasePolynomial.go, hrz]
      rw [hstep]
      refine ih ps _ cnots hrest hps ?_
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact hps q
      · exact hterms u hu'
    · subst hgct
      have hstep : extractPhasePolynomial.go (Gate.CNOT c t :: rest) ps terms cnots
          = extractPhasePolynomial.go rest (applyCNOTToParity ps c t) terms
              ((c, t) :: cnots) := by
        simp only [extractPhasePolynomial.go, isRzGate]
      rw [hstep]
      exact ih _ terms _ hrest (applyCNOTToParity_sorted hps c t) hterms

/-- Every parity the extraction records on a `{CNOT, Rz-family}` gate list is a
    sorted list. -/
theorem extractPhasePolynomial_terms_pairwise (gs : List (Gate n))
    (hgs : ∀ g ∈ gs, isPhasePolyGate g = true) :
    ∀ u ∈ (extractPhasePolynomial gs).terms, u.parity.Pairwise (· < ·) :=
  go_terms_pairwise gs (initParityState n) [] [] hgs initParityState_sorted
    (by simp)

/-- The merge scan only ever emits parities already present in the accumulator
    or in the scanned list. -/
theorem mergeStep_foldl_parity (t : ParityTerm n) (P : List (Fin n) → Prop) :
    ∀ (l a0 : List (ParityTerm n)) (b0 : Bool),
      (∀ u ∈ a0, P u.parity) → (∀ u ∈ l, P u.parity) →
      ∀ u ∈ (List.foldl (mergeStep t) (a0, b0) l).1, P u.parity := by
  intro l
  induction l with
  | nil => intro a0 b0 ha0 _ u hu; exact ha0 u hu
  | cons t' rest ih =>
    intro a0 b0 ha0 hl
    have ht' : P t'.parity := hl t' (List.mem_cons_self ..)
    have hrest : ∀ u ∈ rest, P u.parity := fun u hu => hl u (List.mem_cons_of_mem t' hu)
    rw [List.foldl_cons]
    by_cases hc : (!b0 && (t.parity == t'.parity)) = true
    · have hstep : mergeStep t (a0, b0) t'
          = ((⟨t'.parity, t'.angle + t.angle⟩ : ParityTerm n) :: a0, true) := by
        simp only [mergeStep, ite_eq_left hc]
      rw [hstep]
      refine ih _ true ?_ hrest
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact ht'
      · exact ha0 u hu'
    · have hstep : mergeStep t (a0, b0) t' = (t' :: a0, b0) := by
        simp only [mergeStep, ite_eq_right hc]
      rw [hstep]
      refine ih _ b0 ?_ hrest
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact ht'
      · exact ha0 u hu'

theorem mergeTerms_go_parity (P : List (Fin n) → Prop) :
    ∀ l acc : List (ParityTerm n), (∀ u ∈ l, P u.parity) → (∀ u ∈ acc, P u.parity) →
      ∀ u ∈ mergeTerms.go l acc, P u.parity := by
  intro l
  induction l with
  | nil =>
    intro acc _ hacc u hu
    rw [mergeTerms_go_nil, List.mem_reverse] at hu
    exact hacc u hu
  | cons t rest ih =>
    intro acc hl hacc
    have ht : P t.parity := hl t (List.mem_cons_self ..)
    have hrest : ∀ u ∈ rest, P u.parity := fun u hu => hl u (List.mem_cons_of_mem t hu)
    rw [mergeTerms_go_cons]
    split
    · refine ih _ hrest ?_
      intro u hu
      rw [List.mem_reverse] at hu
      exact mergeStep_foldl_parity t P acc [] false (by simp) hacc u hu
    · refine ih _ hrest ?_
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact ht
      · exact hacc u hu'

/-- Merging same-parity terms emits only parities that were already present. -/
theorem mergeTerms_parity (P : List (Fin n) → Prop) (ts : List (ParityTerm n))
    (h : ∀ u ∈ ts, P u.parity) : ∀ u ∈ mergeTerms ts, P u.parity := by
  rw [mergeTerms_eq_go]
  exact mergeTerms_go_parity P ts [] h (by simp)

/-- Every term of the optimized polynomial is realizable by a `CNOT` ladder,
    given that every input parity is sorted. -/
theorem optimizePhasePolynomial_termWF {pp : PhasePolynomial n}
    (h : ∀ u ∈ pp.terms, u.parity.Pairwise (· < ·)) :
    ∀ u ∈ (optimizePhasePolynomial pp).terms, TermWF u := by
  intro u hu
  have hu' : u ∈ mergeTerms pp.terms := by
    have : u ∈ removeZeroTerms (mergeTerms pp.terms) := hu
    rw [removeZeroTerms] at this
    exact List.mem_of_mem_filter this
  exact termWF_of_sorted
    (mergeTerms_parity (fun l => l.Pairwise (· < ·)) pp.terms h u hu')

/-! ## The optimization pass -/

/-- Optimizing a phase polynomial leaves the unitary it denotes unchanged. -/
theorem optimizePhasePolynomial_ppUnitary (pp : PhasePolynomial n) :
    ppUnitary (optimizePhasePolynomial pp) = ppUnitary pp := by
  show netU pp.cnots * termsU (removeZeroTerms (mergeTerms pp.terms))
      = netU pp.cnots * termsU pp.terms
  rw [termsU_removeZeroTerms, termsU_mergeTerms]

private theorem circuitUnitary_val_append (l₁ l₂ : List (Gate n)) :
    (RoutingPerm.circuitUnitary (Circuit.ofList (l₁ ++ l₂))).val
      = (RoutingPerm.circuitUnitary (Circuit.ofList l₂)).val *
          (RoutingPerm.circuitUnitary (Circuit.ofList l₁)).val := by
  rw [circuitUnitary_ofList_append]
  rfl

/-- Extracting, optimizing and resynthesizing a `{CNOT, Rz-family}` gate list
    preserves its unitary. -/
theorem segmentOpt_circuitUnitary (gs : List (Gate n))
    (hgs : ∀ g ∈ gs, isPhasePolyGate g = true) :
    (RoutingPerm.circuitUnitary (Circuit.ofList
        (resynthesizeCircuit (optimizePhasePolynomial (extractPhasePolynomial gs))))).val
      = (RoutingPerm.circuitUnitary (Circuit.ofList gs)).val := by
  rw [resynthesizeCircuit_circuitUnitary _
      (optimizePhasePolynomial_termWF (extractPhasePolynomial_terms_pairwise gs hgs)),
    optimizePhasePolynomial_ppUnitary, extractPhasePolynomial_ppUnitary gs hgs]

private theorem mem_takeWhile_isPhasePolyGate :
    ∀ (gs : List (Gate n)) {g : Gate n},
      g ∈ gs.takeWhile isPhasePolyGate → isPhasePolyGate g = true := by
  intro gs
  induction gs with
  | nil => intro g h; simp at h
  | cons a rest ih =>
    intro g h
    rw [List.takeWhile_cons] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h'
      · assumption
      · exact ih h'
    · simp at h

/-- The fuel-bounded segment recursion preserves the unitary of the gate list. -/
theorem optimizeSegments_circuitUnitary :
    ∀ (fuel : ℕ) (gs : List (Gate n)),
      (RoutingPerm.circuitUnitary (Circuit.ofList (optimizeSegments gs fuel))).val
        = (RoutingPerm.circuitUnitary (Circuit.ofList gs)).val := by
  intro fuel
  induction fuel with
  | zero => intro gs; rfl
  | succ fuel' ih =>
    intro gs
    cases gs with
    | nil => rfl
    | cons g gs0 =>
      by_cases hpg : isPhasePolyGate g = true
      · have hstep : optimizeSegments (g :: gs0) (fuel' + 1)
            = resynthesizeCircuit (optimizePhasePolynomial
                (extractPhasePolynomial ((g :: gs0).takeWhile isPhasePolyGate)))
              ++ optimizeSegments ((g :: gs0).dropWhile isPhasePolyGate) fuel' := by
          simp only [optimizeSegments, splitAtNonPhasePoly, List.takeWhile_cons,
            ite_eq_left hpg, List.isEmpty_cons, Bool.false_eq_true]
          simp
        have hgs : ∀ g' ∈ (g :: gs0).takeWhile isPhasePolyGate, isPhasePolyGate g' = true :=
          fun g' hg' => mem_takeWhile_isPhasePolyGate _ hg'
        rw [hstep, circuitUnitary_val_append, ih, segmentOpt_circuitUnitary _ hgs,
          ← circuitUnitary_val_append, List.takeWhile_append_dropWhile]
      · have hpg' : isPhasePolyGate g = false := by simpa using hpg
        have hstep : optimizeSegments (g :: gs0) (fuel' + 1)
            = g :: optimizeSegments gs0 fuel' := by
          simp only [optimizeSegments, splitAtNonPhasePoly, List.takeWhile_cons,
            hpg', Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_eq_left]
        rw [hstep]
        show (RoutingPerm.circuitUnitary (Circuit.ofList (optimizeSegments gs0 fuel'))).val *
            gateEmbedding g = _
        rw [ih]
        rfl

/-- The phase-polynomial pass preserves the unitary a circuit realizes. -/
theorem phasePolynomialOpt_circuitUnitary (c : Circuit n) :
    RoutingPerm.circuitUnitary (phasePolynomialOpt c) = RoutingPerm.circuitUnitary c := by
  show RoutingPerm.circuitUnitary (Circuit.ofList (optimizeSegments (circuitToList c) _)) = _
  rw [← MatrixSound.circuitUnitary_ofList_circuitToList c]
  exact Subtype.ext (optimizeSegments_circuitUnitary _ (circuitToList c))

/-- The phase-polynomial pass preserves the unitary-channel denotation. -/
theorem phasePolynomialOpt_unitaryDenote (c : Circuit n) :
    unitaryDenote (phasePolynomialOpt c) = unitaryDenote c := by
  rw [RoutingPerm.unitaryDenote_eq_channel, RoutingPerm.unitaryDenote_eq_channel,
    phasePolynomialOpt_circuitUnitary]

/-- The phase-polynomial pass is `UnitaryCorrectQ`. -/
theorem phasePolynomialOpt_unitaryCorrect :
    UnitaryCorrectQ (phasePolynomialOpt : Circuit n → Circuit n) :=
  fun c => (phasePolynomialOpt_unitaryDenote c).symm

end CatCrypt.Quantum.Optimization.PhasePolyExtract
