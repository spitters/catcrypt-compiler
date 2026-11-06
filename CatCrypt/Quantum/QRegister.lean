/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.AndAncilla

/-!
# Typed registers and the equality condition `with x == v`

A typed register (a quantum variable in the sense of Qrisp) of width `w` on `n` qubits is an
injective map `Fin w → Fin n`: position `i` of the register is the qubit `q i`. The value of
the register at a basis index `x` of the `n` qubits is the `w`-bit number formed by the bits of
`x` at the register's qubits, position `0` most significant. A QuantumBool is a register of
width one and a QuantumUInt a register of width `w`; a QuantumFloat or QuantumModulus is a
value reading of an unsigned register, with its arithmetic given as reversible circuits.

A gate list on `w` qubits is placed on the register by relabelling its qubits along the map;
its matrix is the register-local matrix tensored with the identity on the other qubits
(`Reg.listMatrix_place`). The condition environment `with x == v` of Qrisp computes the
predicate `x = v` into a clean ancilla by an `X` pattern and a multi-controlled `X`, controls a
block on the ancilla and uncomputes the predicate; on ancilla `|0⟩` it applies the block
exactly on the basis states where the register reads `v` (`listMatrix_withEq`). The
ancilla-free variant controls each gate of the block on every qubit of the register
(`listMatrix_withEqNoAnc`).

The matrix of a gate list is `QFT.listMatrix` (head gate applied first).

## Main definitions

* `bitEquiv n` — a basis index of `n` qubits as its bit string, qubit `0` most significant.
* `Reg n w` — a typed register; `QBool n`, `QUInt n w`.
* `Reg.window h` — the contiguous register `[start, start + w)`.
* `Reg.place r l` — the gate list `l` on `w` qubits placed on the qubits of `r`.
* `Reg.val r x` — the value of the register at the basis index `x`.
* `Reg.proj r v` — the projector onto the basis states where `r` reads `v`.
* `Reg.lift r M` — the matrix `M` on the register tensored with the identity elsewhere.
* `Reg.xPattern r v` — `X` on the qubits of `r` where the bit of `v` is `0`.
* `Reg.eqIntoGates r v a` — computes the predicate `r = v` into the qubit `a`.
* `Reg.withEq r v a body` — `body` under the condition `r == v`, with the ancilla `a`.
* `Reg.withEqNoAnc r v body` — `body` under the condition `r == v`, without ancilla.

## Main results

* `Reg.proj_eq_diagonal` — the projector is the diagonal indicator of `r.val x = v`.
* `Reg.listMatrix_place` — the matrix of a placed gate list is the lifted matrix.
* `Reg.listMatrix_eqIntoGates` — `eqIntoGates` is `1 + Π (X_a - 1)` with `Π = r.proj v`.
* `Reg.listMatrix_withEq` — on ancilla `|0⟩`, `withEq` applies `body` where `r` reads `v`.
* `Reg.listMatrix_withEqNoAnc` — `withEqNoAnc` is `1 + Π (U_body - 1)`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix Kronecker
open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.ControlledGates
open CatCrypt.Quantum.AndAncilla
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append mapGate)

noncomputable section

namespace CatCrypt.Quantum.QRegister

variable {n w : ℕ}

/-! ## Bits of a basis index -/

/-- A basis index of `n` qubits as its bit string: qubit `q` reads `gbit n q`, qubit `0`
    most significant. -/
def bitEquiv (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Fin 2) :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr Fin.revPerm (Equiv.refl _))

/-- The bit string of `x` at qubit `q` is `gbit n q x`. -/
theorem bitEquiv_apply (x : Fin (2 ^ n)) (q : Fin n) : bitEquiv n x q = gbit n q x.val := by
  apply Fin.ext
  simp [bitEquiv, finFunctionFinEquiv_symm_apply_val, gbit_val, pos]
  grind

/-- The basis index with bit string `f` reads `f q` at qubit `q`. -/
theorem gbit_bitEquiv_symm (f : Fin n → Fin 2) (q : Fin n) :
    gbit n q ((bitEquiv n).symm f).val = f q := by
  rw [← bitEquiv_apply, Equiv.apply_symm_apply]

/-- Two basis indices with the same bits are equal. -/
theorem eq_of_gbit {x y : Fin (2 ^ n)} (h : ∀ q, gbit n q x.val = gbit n q y.val) : x = y :=
  (bitEquiv n).injective (funext fun q => by rw [bitEquiv_apply, bitEquiv_apply, h])

/-- A basis index of `n` qubits has no bit at a position `p ≥ n`. -/
theorem testBit_of_le (x : Fin (2 ^ n)) {p : ℕ} (hp : n ≤ p) : x.val.testBit p = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hp))

/-- Two bits agree when their `gbit`s agree. -/
theorem testBit_eq_of_gbit {q : Fin n} {x y : ℕ} (h : gbit n q x = gbit n q y) :
    x.testBit (pos n q) = y.testBit (pos n q) := by
  have h' := congrArg Fin.val h
  rw [gbit_eq_testBit, gbit_eq_testBit] at h'
  revert h'
  cases x.testBit (pos n q) <;> cases y.testBit (pos n q) <;> simp

/-- `Match n q` in terms of the bits at the other qubits. -/
theorem match_iff_gbit (q : Fin n) (x y : Fin (2 ^ n)) :
    Match n q x.val y.val ↔ ∀ k, k ≠ q → gbit n k x.val = gbit n k y.val := by
  constructor
  · intro h k hk
    apply Fin.ext
    rw [gbit_eq_testBit, gbit_eq_testBit, h (pos n k) (pos_ne hk)]
  · intro h p hp
    by_cases hpn : p < n
    · have hk : pos n ⟨n - 1 - p, by omega⟩ = p := by simp only [pos]; omega
      rw [← hk]
      exact testBit_eq_of_gbit (h _ fun e => hp (by rw [← hk, e]))
    · rw [testBit_of_le x (by omega), testBit_of_le y (by omega)]

/-- `Match2 n i j` in terms of the bits at the other qubits. -/
theorem match2_iff_gbit (i j : Fin n) (x y : Fin (2 ^ n)) :
    Match2 n i j x.val y.val ↔ ∀ k, k ≠ i → k ≠ j → gbit n k x.val = gbit n k y.val := by
  constructor
  · intro h k hki hkj
    apply Fin.ext
    rw [gbit_eq_testBit, gbit_eq_testBit, h (pos n k) (pos_ne hki) (pos_ne hkj)]
  · intro h p hpi hpj
    by_cases hpn : p < n
    · have hk : pos n ⟨n - 1 - p, by omega⟩ = p := by simp only [pos]; omega
      rw [← hk]
      exact testBit_eq_of_gbit
        (h _ (fun e => hpi (by rw [← hk, e])) fun e => hpj (by rw [← hk, e]))
    · rw [testBit_of_le x (by omega), testBit_of_le y (by omega)]

/-! ## Typed registers -/

/-- A typed register (quantum variable) of width `w` on `n` qubits: position `i` of the
    register is the qubit `q i`, and distinct positions are distinct qubits. -/
structure Reg (n w : ℕ) where
  /-- The qubit at each position of the register. -/
  q : Fin w → Fin n
  /-- Distinct positions are distinct qubits. -/
  inj : Function.Injective q

/-- A QuantumBool: a register of one qubit. -/
abbrev QBool (n : ℕ) := Reg n 1

/-- A QuantumUInt: a register of `w` qubits read as an unsigned number, position `0` most
    significant. -/
abbrev QUInt (n w : ℕ) := Reg n w

namespace Reg

/-- The contiguous register `[start, start + w)`: position `i` is the qubit `start + i`. -/
def window {start : ℕ} (h : start + w ≤ n) : Reg n w where
  q i := ⟨start + i.val, by omega⟩
  inj i j hij := Fin.ext (by have := congrArg Fin.val hij; simp only at this; omega)

variable (r : Reg n w)

/-- The gate list `l` on `w` qubits placed on the qubits of the register. -/
def place (l : List (Gate w)) : List (Gate n) := l.map (mapGate r.q)

/-- The value of the register at the basis index `x`: the bits of `x` at the qubits of the
    register, position `0` most significant. -/
def val (x : Fin (2 ^ n)) : Fin (2 ^ w) := (bitEquiv w).symm fun i => gbit n (r.q i) x.val

/-- Bit `i` of the value of the register is the bit of its qubit `q i`. -/
theorem gbit_regVal (i : Fin w) (x : Fin (2 ^ n)) :
    gbit w i (r.val x).val = gbit n (r.q i) x.val :=
  gbit_bitEquiv_symm _ i

/-- The register reads `v` exactly when each of its qubits carries the bit of `v`. -/
theorem val_eq_iff (x : Fin (2 ^ n)) (v : Fin (2 ^ w)) :
    r.val x = v ↔ ∀ i, gbit n (r.q i) x.val = gbit w i v.val := by
  constructor
  · rintro rfl i
    exact (r.gbit_regVal i x).symm
  · intro h
    exact eq_of_gbit fun i => by rw [r.gbit_regVal, h]

end Reg

/-! ## Projectors onto register values -/

/-- The single-qubit projector onto `|b⟩`. -/
def bitProj (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := if b = 1 then proj1 else proj0

/-- The projector onto `|b⟩` is diagonal. -/
theorem isDiagonal_bitProj (b : Fin 2) : IsDiagonal (bitProj b) := by
  unfold bitProj
  split
  · exact isDiagonal_proj1
  · exact isDiagonal_proj0

/-- The diagonal of the projector onto `|b⟩` is the indicator of `b`. -/
theorem bitProj_apply_self (b c : Fin 2) : bitProj b c c = if c = b then 1 else 0 := by
  fin_cases b <;> fin_cases c <;> simp [bitProj, proj0, proj1]

/-- A product of diagonal matrices is the diagonal of the pointwise product. -/
theorem prod_map_diagonal {ι : Type} (l : List ι) (f : ι → Fin (2 ^ n) → ℂ) :
    (l.map fun i => Matrix.diagonal (f i)).prod
      = Matrix.diagonal fun x => (l.map fun i => f i x).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Matrix.diagonal_mul_diagonal]

namespace Reg

variable (r : Reg n w)

/-- The projector onto the basis states where the register reads `v`: the product over the
    positions `i` of the projector of qubit `q i` onto bit `i` of `v`. -/
def proj (v : Fin (2 ^ w)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  ((List.finRange w).map fun i => embedGate1 n (r.q i) (bitProj (gbit w i v.val))).prod

/-- **The register projector is diagonal**: its entry at `x` is `1` where the register reads
    `v` and `0` elsewhere. -/
theorem proj_eq_diagonal (v : Fin (2 ^ w)) :
    r.proj v = Matrix.diagonal fun x => if r.val x = v then 1 else 0 := by
  have h : ∀ i, embedGate1 n (r.q i) (bitProj (gbit w i v.val)) = Matrix.diagonal fun x =>
      if gbit n (r.q i) x.val = gbit w i v.val then 1 else 0 := fun i => by
    rw [embedGate1_eq_diagonal _ (isDiagonal_bitProj _)]
    simp only [bitProj_apply_self]
  rw [proj]
  simp only [h]
  rw [prod_map_diagonal]
  congr 1
  funext x
  rw [← Fin.prod_univ_def, Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  exact if_congr (r.val_eq_iff x v).symm rfl rfl

/-- The register projector is the projector of a predicate of the register's qubits. -/
theorem isPred_proj (v : Fin (2 ^ w)) : IsPred (List.ofFn r.q) (r.proj v) := by
  refine ⟨⟨_, r.proj_eq_diagonal v, fun x y h => ?_⟩, ?_⟩
  · have : r.val x = r.val y := eq_of_gbit fun i => by
      rw [r.gbit_regVal, r.gbit_regVal, h (r.q i) (List.mem_ofFn.mpr ⟨i, rfl⟩)]
    rw [this]
  · rw [r.proj_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    split <;> simp

/-! ## Placing a gate list on a register -/

/-- The qubits outside the register. -/
abbrev Rest := {c : Fin n // c ∉ Set.range r.q}

open Classical in
/-- A basis index of `n` qubits split into the value of the register and the bits of the
    qubits outside it. -/
def split : Fin (2 ^ n) ≃ Fin (2 ^ w) × (r.Rest → Fin 2) :=
  (bitEquiv n).trans <|
    (Equiv.arrowCongr (Equiv.sumCompl fun c => c ∈ Set.range r.q).symm (Equiv.refl _)).trans <|
      (Equiv.sumArrowEquivProdArrow _ _ _).trans <|
        Equiv.prodCongr
          ((Equiv.arrowCongr (Equiv.ofInjective r.q r.inj).symm (Equiv.refl _)).trans
            (bitEquiv w).symm)
          (Equiv.refl _)

/-- The first component of the split is the value of the register. -/
theorem split_fst (x : Fin (2 ^ n)) : (r.split x).1 = r.val x := by
  simp only [split, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_trans, Equiv.coe_refl,
    Prod.map_fst, Function.comp_apply, val, EmbeddingLike.apply_eq_iff_eq]
  funext i
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Equiv.symm_symm, Function.comp_apply,
    Equiv.ofInjective_apply, Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.sumCompl_apply_inl,
    bitEquiv_apply, id_eq]

/-- The second component of the split is the bits outside the register. -/
theorem split_snd (x : Fin (2 ^ n)) : (r.split x).2 = fun c => gbit n c.1 x.val := by
  funext c
  simp [split, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_apply_snd,
    Equiv.sumCompl_apply_inr, bitEquiv_apply]

/-- The matrix `M` on the register, tensored with the identity on the other qubits. -/
def lift (M : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (M ⊗ₖ (1 : Matrix (r.Rest → Fin 2) (r.Rest → Fin 2) ℂ)).submatrix r.split r.split

/-- The entries of a lifted matrix: those of `M` at the register values where the qubits
    outside the register agree, and `0` elsewhere. -/
theorem lift_apply (M : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ) (x y : Fin (2 ^ n)) :
    r.lift M x y = if ∀ c : r.Rest, gbit n c.1 x.val = gbit n c.1 y.val
      then M (r.val x) (r.val y) else 0 := by
  rw [lift, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, r.split_fst, r.split_fst,
    r.split_snd, r.split_snd, Matrix.one_apply]
  simp only [funext_iff]
  split_ifs <;> simp

/-- Lifting is multiplicative. -/
theorem lift_mul (M N : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ) :
    r.lift M * r.lift N = r.lift (M * N) := by
  rw [lift, lift, lift, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, one_mul]

/-- The lift of the identity is the identity. -/
theorem lift_one : r.lift 1 = 1 := by
  rw [lift, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-- `Match` at a register qubit: agreement off position `i` of the register and outside it. -/
theorem match_q_iff (i : Fin w) (x y : Fin (2 ^ n)) :
    Match n (r.q i) x.val y.val ↔ Match w i (r.val x).val (r.val y).val ∧
      ∀ c : r.Rest, gbit n c.1 x.val = gbit n c.1 y.val := by
  rw [match_iff_gbit, match_iff_gbit]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun c => h c.1 fun e => c.2 ⟨i, e.symm⟩⟩
    rw [r.gbit_regVal, r.gbit_regVal]
    exact h _ (r.inj.ne hj)
  · rintro ⟨h₁, h₂⟩ k hk
    by_cases hk' : k ∈ Set.range r.q
    · obtain ⟨j, rfl⟩ := hk'
      have := h₁ j fun e => hk (e ▸ rfl)
      rwa [r.gbit_regVal, r.gbit_regVal] at this
    · exact h₂ ⟨k, hk'⟩

/-- `Match2` at two register qubits. -/
theorem match2_q_iff (i j : Fin w) (x y : Fin (2 ^ n)) :
    Match2 n (r.q i) (r.q j) x.val y.val ↔ Match2 w i j (r.val x).val (r.val y).val ∧
      ∀ c : r.Rest, gbit n c.1 x.val = gbit n c.1 y.val := by
  rw [match2_iff_gbit, match2_iff_gbit]
  constructor
  · intro h
    refine ⟨fun k hki hkj => ?_, fun c => h c.1 (fun e => c.2 ⟨i, e.symm⟩)
      fun e => c.2 ⟨j, e.symm⟩⟩
    rw [r.gbit_regVal, r.gbit_regVal]
    exact h _ (r.inj.ne hki) (r.inj.ne hkj)
  · rintro ⟨h₁, h₂⟩ k hki hkj
    by_cases hk' : k ∈ Set.range r.q
    · obtain ⟨l, rfl⟩ := hk'
      have := h₁ l (fun e => hki (e ▸ rfl)) fun e => hkj (e ▸ rfl)
      rwa [r.gbit_regVal, r.gbit_regVal] at this
    · exact h₂ ⟨k, hk'⟩

/-- The lift of a single-qubit operator on position `i` is the operator on qubit `q i`. -/
theorem lift_embedGate1 (i : Fin w) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    r.lift (embedGate1 w i G) = embedGate1 n (r.q i) G := by
  ext x y
  rw [lift_apply, embedGate1_apply, embedGate1_apply, r.gbit_regVal, r.gbit_regVal]
  simp only [r.match_q_iff]
  split_ifs <;> simp_all

/-- The lift of a two-qubit operator on positions `i`, `j` is the operator on `q i`, `q j`. -/
theorem lift_embedGate2 {i j : Fin w} (hij : i ≠ j) (G : Matrix (Fin 4) (Fin 4) ℂ) :
    r.lift (embedGate2 w i j G hij) = embedGate2 n (r.q i) (r.q j) G (r.inj.ne hij) := by
  have hidx : ∀ x : Fin (2 ^ n), idx4 w i j (r.val x).val = idx4 n (r.q i) (r.q j) x.val :=
    fun x => Fin.ext (by simp only [idx4, r.gbit_regVal])
  ext x y
  rw [lift_apply, embedGate2_apply, embedGate2_apply, hidx, hidx]
  simp only [r.match2_q_iff]
  split_ifs <;> simp_all

/-- The matrix of a relabelled gate is the lift of the matrix of the gate. -/
theorem gateEmbedding_mapGate (g : Gate w) :
    gateEmbedding (mapGate r.q g) = r.lift (gateEmbedding g) := by
  cases g with
  | CNOT i j =>
    by_cases hij : i = j
    · subst hij
      simp [mapGate, gateEmbedding, lift_one]
    · simp [mapGate, gateEmbedding, hij, r.inj.ne hij, lift_embedGate2]
  | CZ i j =>
    by_cases hij : i = j
    · subst hij
      simp [mapGate, gateEmbedding, lift_one]
    · simp [mapGate, gateEmbedding, hij, r.inj.ne hij, lift_embedGate2]
  | _ => simp only [mapGate, gateEmbedding, lift_embedGate1]

/-- **Placing a gate list on a register**: its matrix is the matrix of the list on `w`
    qubits, lifted to the register. -/
theorem listMatrix_place (l : List (Gate w)) :
    listMatrix (r.place l) = r.lift (listMatrix l) := by
  induction l with
  | nil => rw [place, List.map_nil, listMatrix_nil, listMatrix_nil, lift_one]
  | cons g l ih =>
    rw [place, List.map_cons, listMatrix_cons, ← place, ih, listMatrix_cons, gateEmbedding_mapGate,
      lift_mul]

end Reg

/-! ## `X` layers -/

/-- An `X` layer commutes with every matrix that commutes with the operators on its qubits. -/
theorem commute_listMatrix_X {qs : List (Fin n)} {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ q ∈ qs, CommOn q M) : Commute (listMatrix (qs.map Gate.X)) M := by
  induction qs with
  | nil => rw [List.map_nil, listMatrix_nil]; exact Commute.one_left M
  | cons q qs ih =>
    rw [List.map_cons, listMatrix_cons]
    exact (ih fun q' hq' => h q' (List.mem_cons_of_mem q hq')).mul_left
      (h q List.mem_cons_self pauliX)

/-- An `X` layer on distinct qubits avoids every qubit outside it. -/
theorem commOn_listMatrix_X {qs : List (Fin n)} {c : Fin n} (hc : c ∉ qs) :
    CommOn c (listMatrix (qs.map Gate.X)) :=
  commOn_listMatrix fun g hg => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    exact fun e => hc (e ▸ hq)

/-- An `X` layer on distinct qubits is an involution. -/
theorem listMatrix_mapX_mul_self {qs : List (Fin n)} (hnd : qs.Nodup) :
    listMatrix (qs.map Gate.X) * listMatrix (qs.map Gate.X) = 1 := by
  induction qs with
  | nil => rw [List.map_nil, listMatrix_nil, one_mul]
  | cons q qs ih =>
    obtain ⟨hq, hnd'⟩ := List.nodup_cons.mp hnd
    have hc : Commute (listMatrix (qs.map Gate.X)) (embedGate1 n q pauliX) :=
      ((commOn_listMatrix_X hq) pauliX).symm
    rw [List.map_cons, listMatrix_cons]
    change listMatrix (qs.map Gate.X) * embedGate1 n q pauliX *
      (listMatrix (qs.map Gate.X) * embedGate1 n q pauliX) = 1
    rw [mul_assoc, ← mul_assoc (embedGate1 n q pauliX), ← hc.eq, mul_assoc, embedGate1_mul,
      pauliX_sq, embedGate1_one, mul_one, ih hnd']

/-- Conjugating a single-qubit operator by an `X` layer on distinct qubits conjugates it by
    `X` where the layer acts. -/
theorem listMatrix_X_conj_embedGate1 {qs : List (Fin n)} (hnd : qs.Nodup) (c : Fin n)
    (G : Matrix (Fin 2) (Fin 2) ℂ) :
    listMatrix (qs.map Gate.X) * embedGate1 n c G * listMatrix (qs.map Gate.X)
      = embedGate1 n c (if c ∈ qs then pauliX * G * pauliX else G) := by
  induction qs generalizing G with
  | nil => simp [listMatrix_nil]
  | cons q qs ih =>
    obtain ⟨hq, hnd'⟩ := List.nodup_cons.mp hnd
    have hc : listMatrix (qs.map Gate.X) * embedGate1 n q pauliX
        = embedGate1 n q pauliX * listMatrix (qs.map Gate.X) :=
      ((commOn_listMatrix_X hq) pauliX).symm
    rw [List.map_cons, listMatrix_cons]
    change listMatrix (qs.map Gate.X) * embedGate1 n q pauliX * embedGate1 n c G *
      (listMatrix (qs.map Gate.X) * embedGate1 n q pauliX) = _
    by_cases hcq : c = q
    · subst hcq
      have hih := ih hnd' (pauliX * G * pauliX)
      rw [ite_eq_right hq] at hih
      rw [ite_eq_left List.mem_cons_self, ← hih, ← embedGate1_mul, ← embedGate1_mul]
      nth_rewrite 2 [hc]
      simp only [mul_assoc]
    · have hXE : embedGate1 n q pauliX * embedGate1 n c G
          = embedGate1 n c G * embedGate1 n q pauliX :=
        (commOn_embedGate1 (Ne.symm hcq) pauliX G).symm
      have hmem : (c ∈ q :: qs) ↔ (c ∈ qs) := by simp [hcq]
      rw [if_congr hmem rfl rfl, ← ih hnd', mul_assoc _ (embedGate1 n q pauliX), hXE, hc]
      simp only [mul_assoc]
      rw [← mul_assoc (embedGate1 n q pauliX) (embedGate1 n q pauliX), embedGate1_mul,
        pauliX_sq, embedGate1_one, one_mul]

/-- In a monoid, conjugation by an involution is multiplicative over a list product. -/
theorem conj_involution_prod {M : Type*} [Monoid M] {h : M} (hh : h * h = 1) {ι : Type}
    (l : List ι) (f : ι → M) : h * (l.map f).prod * h = (l.map fun i => h * f i * h).prod := by
  induction l with
  | nil => simp [hh]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, conj_involution_mul hh, ih, List.map_cons, List.prod_cons]

/-- In a ring, conjugation of `1 + P (M - 1)` by an involution commuting with `M`. -/
theorem conj_one_add {R : Type*} [Ring R] {h P M : R} (hh : h * h = 1) (hM : Commute h M) :
    h * (1 + P * (M - 1)) * h = 1 + h * P * h * (M - 1) := by
  have hM1 : Commute h (M - 1) := hM.sub_right (Commute.one_right h)
  simp only [mul_add, add_mul, mul_one, hh, mul_assoc]
  rw [← hM1.eq]

/-- In a ring, `1 + P (A - 1)` is multiplicative in `A` for an idempotent `P` commuting
    with `A`. -/
theorem one_add_mul_one_add {R : Type*} [Ring R] {P A B : R} (hP : P * P = P)
    (hPA : Commute P A) : (1 + P * (A - 1)) * (1 + P * (B - 1)) = 1 + P * (A * B - 1) := by
  have h1 : P * (A - 1) * (P * (B - 1)) = P * ((A - 1) * (B - 1)) := by
    rw [← mul_assoc, mul_assoc P (A - 1) P,
      ← (hPA.sub_right (Commute.one_right P)).eq, ← mul_assoc, hP, mul_assoc]
  rw [add_mul, one_mul, mul_add, mul_one, h1]
  noncomm_ring

/-! ## The condition `with x == v` -/

namespace Reg

variable (r : Reg n w)

/-- The qubits of the register where the bit of `v` is `0`. -/
def xQubits (v : Fin (2 ^ w)) : List (Fin n) :=
  ((List.finRange w).filter fun i => gbit w i v.val = 0).map r.q

/-- `X` on the qubits of the register where the bit of `v` is `0`: it maps the basis states
    where the register reads `v` to those where it reads all ones. -/
def xPattern (v : Fin (2 ^ w)) : List (Gate n) := (r.xQubits v).map Gate.X

/-- The qubits of an `X` pattern are distinct. -/
theorem nodup_xQubits (v : Fin (2 ^ w)) : (r.xQubits v).Nodup :=
  ((List.nodup_finRange w).filter _).map r.inj

/-- The qubit `q i` is in the `X` pattern of `v` exactly when bit `i` of `v` is `0`. -/
theorem mem_xQubits (v : Fin (2 ^ w)) (i : Fin w) :
    r.q i ∈ r.xQubits v ↔ gbit w i v.val = 0 := by
  simp [xQubits, r.inj.eq_iff]

/-- The `X` pattern is an involution. -/
theorem xPattern_mul_self (v : Fin (2 ^ w)) :
    listMatrix (r.xPattern v) * listMatrix (r.xPattern v) = 1 :=
  listMatrix_mapX_mul_self (r.nodup_xQubits v)

/-- The `X` pattern conjugates the projector onto all ones into the projector onto `v`. -/
theorem xPattern_conj_prod_proj1 (v : Fin (2 ^ w)) :
    listMatrix (r.xPattern v) * ((List.ofFn r.q).map fun c => embedGate1 n c proj1).prod
        * listMatrix (r.xPattern v) = r.proj v := by
  rw [List.ofFn_eq_map, List.map_map, xPattern,
    conj_involution_prod (listMatrix_mapX_mul_self (r.nodup_xQubits v)), proj]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, listMatrix_X_conj_embedGate1 (r.nodup_xQubits v)]
  simp only [mem_xQubits]
  rcases Fin.exists_fin_two.mp ⟨gbit w i v.val, rfl⟩ with h | h <;>
    simp [h, bitProj, pauliX_proj1_pauliX]

/-- The circuit computing the predicate `r = v` into the qubit `a`: the `X` pattern of `v`,
    `X a` controlled on every qubit of the register, and the `X` pattern again. -/
def eqIntoGates (v : Fin (2 ^ w)) (a : Fin n) : List (Gate n) :=
  r.xPattern v ++ mctrlGates (List.ofFn r.q) (.X a) ++ r.xPattern v

/-- **Computing `r = v` into an ancilla**: the circuit is `1 + Π (X_a - 1)` with `Π` the
    projector onto the basis states where the register reads `v`. -/
theorem listMatrix_eqIntoGates {v : Fin (2 ^ w)} {a : Fin n} (ha : a ∉ Set.range r.q) :
    listMatrix (r.eqIntoGates v a) = 1 + r.proj v * (embedGate1 n a pauliX - 1) := by
  have hnd : (List.ofFn r.q).Nodup := List.nodup_ofFn.mpr r.inj
  have hav : ∀ c ∈ List.ofFn r.q, Avoids c (Gate.X a) := fun c hc e =>
    ha (e ▸ List.mem_ofFn.mp hc)
  have hX : Commute (listMatrix (r.xPattern v)) (gateEmbedding (Gate.X a)) :=
    commute_listMatrix_X fun q hq => commOn_embedGate1 (fun e => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
      exact ha ⟨i, e.symm⟩) pauliX
  rw [eqIntoGates, listMatrix_append, listMatrix_append, listMatrix_mctrlGates hnd hav,
    mctrlMatrix_eq, ← mul_assoc,
    conj_one_add (r.xPattern_mul_self v) hX, xPattern_conj_prod_proj1]
  rfl

/-- `body` under the condition `r == v`: compute `r = v` into the clean ancilla `a`, `body`
    controlled on `a`, and uncompute. -/
def withEq (v : Fin (2 ^ w)) (a : Fin n) (body : List (Gate n)) : List (Gate n) :=
  ancillaCtrlGates (r.eqIntoGates v a) a body

/-- **The condition environment `with x == v`.** On ancilla `|0⟩`, `withEq` applies `body`
    exactly on the basis states where the register reads `v`. -/
theorem listMatrix_withEq {v : Fin (2 ^ w)} {a : Fin n} {body : List (Gate n)}
    (ha : a ∉ Set.range r.q) (hb : ∀ g ∈ body, Avoids a g ∧ ∀ i, Avoids (r.q i) g) :
    listMatrix (r.withEq v a body) * embedGate1 n a proj0
      = (1 + r.proj v * (listMatrix body - 1)) * embedGate1 n a proj0 :=
  listMatrix_predAncilla_conj (fun hc => ha (List.mem_ofFn.mp hc)) (r.isPred_proj v)
    (phaseOn_one _) (by rw [r.listMatrix_eqIntoGates ha, one_mul]) fun g hg =>
      ⟨(hb g hg).1, fun c hc => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        exact (hb g hg).2 i⟩

/-- Each gate of a list controlled on every qubit of `cs`: the matrix of the list controlled
    on `cs`. -/
theorem listMatrix_flatMap_mctrlGates {cs : List (Fin n)} (hnd : cs.Nodup) :
    ∀ {body : List (Gate n)}, (∀ g ∈ body, ∀ c ∈ cs, Avoids c g) →
      listMatrix (body.flatMap (mctrlGates cs)) = mctrlMatrix cs (listMatrix body)
  | [], _ => by
    rw [List.flatMap_nil, listMatrix_nil, mctrlMatrix_eq, sub_self, mul_zero, add_zero]
  | g :: body, hb => by
    have hb' : ∀ g' ∈ body, ∀ c ∈ cs, Avoids c g' := fun g' hg' =>
      hb g' (List.mem_cons_of_mem g hg')
    have hPU := commute_of_phaseOn (isPred_prod_proj1 cs).1 hb'
    rw [List.flatMap_cons, listMatrix_append, listMatrix_flatMap_mctrlGates hnd hb',
      listMatrix_mctrlGates hnd (hb g List.mem_cons_self), mctrlMatrix_eq, mctrlMatrix_eq,
      one_add_mul_one_add (isPred_prod_proj1 cs).2 hPU, listMatrix_cons, mctrlMatrix_eq]

/-- `body` under the condition `r == v` without ancilla: the `X` pattern of `v`, each gate of
    `body` controlled on every qubit of the register, and the `X` pattern again. -/
def withEqNoAnc (v : Fin (2 ^ w)) (body : List (Gate n)) : List (Gate n) :=
  r.xPattern v ++ body.flatMap (mctrlGates (List.ofFn r.q)) ++ r.xPattern v

/-- **The ancilla-free condition environment.** `withEqNoAnc` applies `body` exactly on the
    basis states where the register reads `v`. -/
theorem listMatrix_withEqNoAnc {v : Fin (2 ^ w)} {body : List (Gate n)}
    (hb : ∀ g ∈ body, ∀ i, Avoids (r.q i) g) :
    listMatrix (r.withEqNoAnc v body) = 1 + r.proj v * (listMatrix body - 1) := by
  have hnd : (List.ofFn r.q).Nodup := List.nodup_ofFn.mpr r.inj
  have hb' : ∀ g ∈ body, ∀ c ∈ List.ofFn r.q, Avoids c g := fun g hg c hc => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact hb g hg i
  have hC : Commute (listMatrix (r.xPattern v)) (listMatrix body) :=
    commute_listMatrix_X fun q hq => commOn_listMatrix fun g hg => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
      exact hb g hg i
  rw [withEqNoAnc, listMatrix_append, listMatrix_append, listMatrix_flatMap_mctrlGates hnd hb',
    mctrlMatrix_eq, ← mul_assoc,
    conj_one_add (r.xPattern_mul_self v) hC, xPattern_conj_prod_proj1]

end Reg

end CatCrypt.Quantum.QRegister
