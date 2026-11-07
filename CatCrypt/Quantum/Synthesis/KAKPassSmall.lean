/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.KAKSmall
public import CatCrypt.Quantum.Synthesis.KAKPass
public import CatCrypt.Quantum.Synthesis.ParMap

/-!
# Two-qubit block resynthesis by the smallest KAK template

`kakPassSmall cls` cuts a gate list into the two-qubit blocks of `KAKPass.collectBlocks`. An
untrusted classifier `cls` assigns each block matrix a class `k ∈ {0, 1, 2, 3}`; a block with
more than `k` CNOTs is replaced by the `k`-CNOT template of `KAKSmall` (`kak0Gates`,
`kak1Gates`, `kak2Gates`) or of `KAK` (`kak3Gates`), with symbolic angles. The `m`-th
template takes the angle vector `ρ m`; the templates of classes `0`, `1` and `2` read its first
`6`, `12` and `14` entries in the angle order documented at `kak0`, `kak1` and `kak2`.

## Main results

* `kakPassSmall_correct` — if every block matrix lies in the class `cls` assigns
  (`ClassifierSound`), some valuation of the angles makes the realized circuit denote the
  channel of the input circuit.
* `cnotCount_realizeS_kakPassSmall_le` — under every valuation and for every classifier the
  realized circuit has at most as many CNOTs as the input.

`kakEmit fit l` is the computable pass on a gate list with exact angles: an untrusted
fitter `fit`, evaluated once per block of `collectBlocks l` by `blockEmit`, proposes a class,
`PiLin` angles and a payload; a replaced block is emitted as `tmplGatesQ` of `Gate.RzQ` gates
and contributes its payload. Its value is the pair of the gates and the payloads.
`blockItemsS` is `blockItemsB` under the block classifier that reads the block matrix.

* `map_rzQToRz_tmplGatesQ` — the exact template read through `rzQToRz` is the real template
  at the real angles.
* `cnotCount_kakEmit_le` — the gates of `kakEmit fit l` have at most as many CNOTs as `l`.
* `listMatrix_kakEmit` — under `FitSound fit l`, the matrix of the gates of `kakEmit fit l` is
  that of `l` up to a global phase.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix Complex
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.GateUnitarity CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.OpenQASMImportGates CatCrypt.Quantum.Synthesis.ZYZ
open CatCrypt.Quantum.Synthesis.KAK
open CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Synthesis.KAKPass
open CatCrypt.Quantum.Synthesis.KAKSmall
open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil listMatrix_append)

namespace CatCrypt.Quantum.Synthesis.KAKPassSmall

variable {n : ℕ}

/-! ## The templates by class -/

/-- An angle vector of length `m ≤ 15` padded with zeros to length `15`. -/
def extendAngles {m : ℕ} (θ : Fin m → ℝ) : Fin 15 → ℝ :=
  fun x => if hx : x.val < m then θ ⟨x.val, hx⟩ else 0

theorem extendAngles_castLE {m : ℕ} (h : m ≤ 15) (θ : Fin m → ℝ) :
    (fun x : Fin m => extendAngles θ (Fin.castLE h x)) = θ := by
  funext x
  simp [extendAngles, x.isLt]

/-- The template for class `k` with angles `θ` over an angle carrier `α`, with the rotation
`rz` and the angles `hp`, `nhp` for `π/2`, `−π/2`: `kak0GatesA`, `kak1GatesA` and
`kak2GatesA` read the first `6`, `12` and `14` angles, `kak3GatesA` all `15`. -/
@[simp] def tmplGatesA {α : Type*} (rz : Fin n → α → Gate n) (hp nhp : α) (k : Fin 4)
    (i j : Fin n) (θ : Fin 15 → α) : List (Gate n) :=
  ![kak0GatesA rz nhp i j (fun x => θ (Fin.castLE (by norm_num) x)),
    kak1GatesA rz nhp i j (fun x => θ (Fin.castLE (by norm_num) x)),
    kak2GatesA rz nhp i j (fun x => θ (Fin.castLE (by norm_num) x)),
    kak3GatesA rz hp nhp i j θ] k

/-- The template for class `k` with angles `θ`: `kak0Gates`, `kak1Gates` and `kak2Gates`
read the first `6`, `12` and `14` angles, `kak3Gates` all `15`. -/
def tmplGates (k : Fin 4) (i j : Fin n) (θ : Fin 15 → ℝ) : List (Gate n) :=
  tmplGatesA Gate.Rz (Real.pi / 2) (-(Real.pi / 2)) k i j θ

/-- The template for class `k` with the exact angles `θ` carried by `Gate.RzQ`. -/
def tmplGatesQ (k : Fin 4) (i j : Fin n) (θ : Fin 15 → PiLin) : List (Gate n) :=
  tmplGatesA Gate.RzQ (PiLin.ofPi (1 / 2)) (PiLin.ofPi (-(1 / 2))) k i j θ

/-- Naturality of `tmplGatesA` along `rzQToRz`. -/
theorem map_rzQToRz_tmplGatesA {α β : Type*} {rz : Fin n → α → Gate n}
    {rz' : Fin n → β → Gate n} {t : α → β} (hrz : ∀ q a, rzQToRz (rz q a) = rz' q (t a))
    (hp nhp : α) (k : Fin 4) (i j : Fin n) (θ : Fin 15 → α) :
    (tmplGatesA rz hp nhp k i j θ).map rzQToRz = tmplGatesA rz' (t hp) (t nhp) k i j (t ∘ θ) := by
  fin_cases k
  · exact map_rzQToRz_kak0GatesA hrz nhp i j (fun x => θ (Fin.castLE (by norm_num) x))
  · exact map_rzQToRz_kak1GatesA hrz nhp i j (fun x => θ (Fin.castLE (by norm_num) x))
  · exact map_rzQToRz_kak2GatesA hrz nhp i j (fun x => θ (Fin.castLE (by norm_num) x))
  · exact map_rzQToRz_kak3GatesA hrz hp nhp i j θ

/-- The exact template `tmplGatesQ`, read through `rzQToRz`, is `tmplGates` at the real
angles. -/
theorem map_rzQToRz_tmplGatesQ (k : Fin 4) (i j : Fin n) (θ : Fin 15 → PiLin) :
    (tmplGatesQ k i j θ).map rzQToRz = tmplGates k i j (PiLin.toReal ∘ θ) := by
  rw [tmplGatesQ, map_rzQToRz_tmplGatesA (rz' := Gate.Rz) (fun _ _ => rfl),
    toReal_ofPi_half, toReal_ofPi_neg_half, tmplGates]

/-- The exact template `tmplGatesQ` has the matrix of `tmplGates` at the real angles. -/
theorem listMatrix_tmplGatesQ (k : Fin 4) (i j : Fin n) (θ : Fin 15 → PiLin) :
    listMatrix (tmplGatesQ k i j θ) = listMatrix (tmplGates k i j (PiLin.toReal ∘ θ)) := by
  rw [← map_rzQToRz_tmplGatesQ, listMatrix_map_rzQToRz]

/-- A unitary of class `k` is, up to a global phase, the matrix of the template `k`. -/
theorem exists_listMatrix_tmplGates {i j : Fin n} (hij : i ≠ j) {U : Matrix (Fin 4) (Fin 4) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (k : Fin 4) (h : InClass k U) :
    ∃ (φ : ℝ) (θ : Fin 15 → ℝ),
      listMatrix (tmplGates k i j θ) = Complex.exp (φ * I) • embedGate2 n i j U hij := by
  fin_cases k
  · obtain ⟨φ, θ, hθ⟩ := kak0_exists_listMatrix hij h
    refine ⟨φ, extendAngles θ, ?_⟩
    simpa only [tmplGates, tmplGatesA, kak0Gates, Fin.zero_eta, Matrix.cons_val_zero,
      extendAngles_castLE] using hθ
  · obtain ⟨φ, θ, hθ⟩ := kak1_exists_listMatrix hij h
    refine ⟨φ, extendAngles θ, ?_⟩
    simpa only [tmplGates, tmplGatesA, kak1Gates, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, extendAngles_castLE] using hθ
  · obtain ⟨φ, θ, hθ⟩ := kak2_exists_listMatrix hij h
    refine ⟨φ, extendAngles θ, ?_⟩
    simpa only [tmplGates, tmplGatesA, kak2Gates, Fin.reduceFinMk, Matrix.cons_val,
      extendAngles_castLE] using hθ
  · exact kak3_exists_listMatrix hij hU

theorem cnotCount_tmplGates (k : Fin 4) (i j : Fin n) (θ : Fin 15 → ℝ) :
    cnotCount (tmplGates k i j θ) = k.val := by
  fin_cases k <;> simp [tmplGates, cnotCount, isCNOT, List.countP_cons]

/-- `rzQToRz` preserves the CNOT count of a gate list. -/
theorem cnotCount_map_rzQToRz (l : List (Gate n)) : cnotCount (l.map rzQToRz) = cnotCount l := by
  simp only [cnotCount, List.countP_map]
  congr 1
  funext g
  cases g <;> rfl

/-- The exact template of class `k` has `k` CNOTs. -/
theorem cnotCount_tmplGatesQ (k : Fin 4) (i j : Fin n) (θ : Fin 15 → PiLin) :
    cnotCount (tmplGatesQ k i j θ) = k.val := by
  rw [← cnotCount_map_rzQToRz, map_rzQToRz_tmplGatesQ, cnotCount_tmplGates]

/-! ## The pass -/

/-- An output item: a gate, or the template of class `k` on `(i, j)` replacing the block
`gs`. -/
inductive SItem (n : ℕ) where
  | gate : Gate n → SItem n
  | tmpl : Fin 4 → Fin n → Fin n → List (Gate n) → SItem n

/-- The items of a segment under a block classifier `cls`: a block `gs` on `(i, j)` with
`cls i j gs = some k` and `k` smaller than its CNOT count becomes the template of class `k`;
every other segment stays its gates. -/
def blockItemsB (cls : Fin n → Fin n → List (Gate n) → Option (Fin 4)) :
    Block n → List (SItem n)
  | .gate g => [.gate g]
  | .pair i j gs =>
    match cls i j gs with
    | some k => if k.val < cnotCount gs then [.tmpl k i j gs] else gs.map .gate
    | none => gs.map .gate

/-- The items of a segment: a block whose class `k = cls M` (for its matrix `M`) is smaller
than its CNOT count becomes the template of class `k`. -/
noncomputable def blockItemsS (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4) :
    Block n → List (SItem n) :=
  blockItemsB fun i j gs => some (cls (blockMat i j gs))

/-- The small-template KAK pass on a circuit, with the classifier `cls`. -/
noncomputable def kakPassSmall (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4) (c : Circuit n) :
    List (SItem n) :=
  (collectBlocks (OpenQASM.toGateList c)).flatMap (blockItemsS cls)

/-- Instantiate the templates: the `m`-th template takes the angles `ρ m`. -/
noncomputable def realizeS (ρ : ℕ → Fin 15 → ℝ) : List (SItem n) → List (Gate n)
  | [] => []
  | .gate g :: l => g :: realizeS ρ l
  | .tmpl k i j _ :: l => tmplGates k i j (ρ 0) ++ realizeS (fun m => ρ (m + 1)) l

/-- The gates an item stands for. -/
def SItem.orig : SItem n → List (Gate n)
  | .gate g => [g]
  | .tmpl _ _ _ gs => gs

/-- An item is valid when each template of class `k` stands for a block on distinct qubits
`(i, j)` with more than `k` CNOTs whose matrix is of class `k`. -/
def SItem.Valid : SItem n → Prop
  | .gate _ => True
  | .tmpl k i j gs => i ≠ j ∧ (∀ g ∈ gs, onPair i j g = true) ∧ k.val < cnotCount gs ∧
      InClass k (blockMat i j gs)

theorem exists_listMatrix_realizeS (l : List (SItem n)) (hl : ∀ x ∈ l, x.Valid) :
    ∃ (ρ : ℕ → Fin 15 → ℝ) (φ : ℝ),
      listMatrix (realizeS ρ l) = Complex.exp (φ * I) • listMatrix (l.flatMap SItem.orig) := by
  induction l with
  | nil => exact ⟨fun _ _ => 0, 0, by simp [realizeS, listMatrix_nil]⟩
  | cons x l ih =>
    obtain ⟨ρ, φ, h⟩ := ih fun y hy => hl y (List.mem_cons_of_mem x hy)
    cases x with
    | gate g =>
      refine ⟨ρ, φ, ?_⟩
      simp only [realizeS, List.flatMap_cons, SItem.orig, List.singleton_append,
        listMatrix_cons, h, Matrix.smul_mul]
    | tmpl k i j gs =>
      obtain ⟨hij, hgs, _, hk⟩ := hl _ List.mem_cons_self
      obtain ⟨ψ, θ, hθ⟩ :=
        exists_listMatrix_tmplGates hij (blockMat_mem_unitaryGroup i j gs) k hk
      refine ⟨fun m => Nat.casesOn m θ ρ, φ + ψ, ?_⟩
      simp only [realizeS, List.flatMap_cons, SItem.orig, listMatrix_append]
      change listMatrix (realizeS ρ l) * listMatrix (tmplGates k i j θ) = _
      rw [h, hθ, ← listMatrix_eq_embedGate2 hij hgs, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, ← Complex.exp_add]
      push_cast
      ring_nf

/-- Each template of class `k` stands for a block with more than `k` CNOTs. -/
def SItem.Small : SItem n → Prop
  | .gate _ => True
  | .tmpl k _ _ gs => k.val < cnotCount gs

theorem cnotCount_realizeS_le (l : List (SItem n)) (hl : ∀ x ∈ l, x.Small)
    (ρ : ℕ → Fin 15 → ℝ) :
    cnotCount (realizeS ρ l) ≤ cnotCount (l.flatMap SItem.orig) := by
  induction l generalizing ρ with
  | nil => simp [realizeS]
  | cons x l ih =>
    have ih' := fun ρ' => ih (fun y hy => hl y (List.mem_cons_of_mem x hy)) ρ'
    cases x with
    | gate g =>
      have := ih' ρ
      simp only [realizeS, List.flatMap_cons, SItem.orig, cnotCount, List.countP_cons,
        List.singleton_append] at this ⊢
      omega
    | tmpl k i j gs =>
      have hk : k.val < cnotCount gs := hl _ List.mem_cons_self
      have := ih' (fun m => ρ (m + 1))
      have hc := cnotCount_tmplGates k i j (ρ 0)
      simp only [realizeS, List.flatMap_cons, SItem.orig, cnotCount,
        List.countP_append] at this hk hc ⊢
      omega

/-- The items of a segment stand for its gates, whatever the block classifier answers. -/
theorem flatMap_orig_blockItemsB (cls : Fin n → Fin n → List (Gate n) → Option (Fin 4))
    (b : Block n) : (blockItemsB cls b).flatMap SItem.orig = b.gates := by
  cases b with
  | gate g => simp [blockItemsB, SItem.orig, Block.gates]
  | pair i j gs =>
    rcases h : cls i j gs with _ | k
    · simp [blockItemsB, h, List.flatMap_map, SItem.orig, Block.gates]
    · by_cases hk : k.val < cnotCount gs
      · simp [blockItemsB, h, hk, SItem.orig, Block.gates]
      · simp [blockItemsB, h, hk, List.flatMap_map, SItem.orig, Block.gates]

/-- The items of a list of segments stand for its gates. -/
theorem flatMap_blockItemsB (cls : Fin n → Fin n → List (Gate n) → Option (Fin 4))
    (l : List (Block n)) :
    (l.flatMap (blockItemsB cls)).flatMap SItem.orig = l.flatMap Block.gates := by
  rw [List.flatMap_assoc]
  exact List.flatMap_congr fun b _ => flatMap_orig_blockItemsB cls b

theorem flatMap_blockItemsS (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4) (l : List (Block n)) :
    (l.flatMap (blockItemsS cls)).flatMap SItem.orig = l.flatMap Block.gates :=
  flatMap_blockItemsB _ l

/-- The hypothesis of the small-template pass: every block of `c` has a matrix of the class
that `cls` assigns to it. -/
def ClassifierSound (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4) (c : Circuit n) : Prop :=
  ∀ i j gs, Block.pair i j gs ∈ collectBlocks (OpenQASM.toGateList c) →
    InClass (cls (blockMat i j gs)) (blockMat i j gs)

theorem valid_kakPassSmall (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4) (c : Circuit n)
    (hcls : ClassifierSound cls c) : ∀ x ∈ kakPassSmall cls c, x.Valid := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hx
  have hv := valid_collectBlocks _ b hb
  cases b with
  | gate g =>
    simp only [blockItemsS, blockItemsB, List.mem_singleton] at hxb
    subst hxb; trivial
  | pair i j gs =>
    obtain ⟨hij, hgs⟩ := hv i j gs rfl
    by_cases hk : (cls (blockMat i j gs)).val < cnotCount gs
    · simp only [blockItemsS, blockItemsB, hk, ite_true, List.mem_singleton] at hxb
      subst hxb; exact ⟨hij, hgs, hk, hcls i j gs hb⟩
    · simp only [blockItemsS, blockItemsB, hk, ite_false, List.mem_map] at hxb
      obtain ⟨g, _, rfl⟩ := hxb
      trivial

theorem small_kakPassSmall (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4) (c : Circuit n) :
    ∀ x ∈ kakPassSmall cls c, x.Small := by
  intro x hx
  obtain ⟨b, _, hxb⟩ := List.mem_flatMap.mp hx
  cases b with
  | gate g =>
    simp only [blockItemsS, blockItemsB, List.mem_singleton] at hxb
    subst hxb; trivial
  | pair i j gs =>
    by_cases hk : (cls (blockMat i j gs)).val < cnotCount gs
    · simp only [blockItemsS, blockItemsB, hk, ite_true, List.mem_singleton] at hxb
      subst hxb; exact hk
    · simp only [blockItemsS, blockItemsB, hk, ite_false, List.mem_map] at hxb
      obtain ⟨g, _, rfl⟩ := hxb
      trivial

theorem listMatrix_flatMap_kakPassSmall (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4)
    (c : Circuit n) :
    listMatrix ((kakPassSmall cls c).flatMap SItem.orig) =
      (Optimization.RoutingPerm.circuitUnitary c).val := by
  rw [kakPassSmall, flatMap_blockItemsS, listMatrix_collectBlocks, listMatrix_toGateList]

/-- **Correctness of the small-template KAK pass.** If every block of `c` has a matrix of the
class that `cls` assigns (`ClassifierSound`), some valuation of the template angles makes the
realized circuit denote the channel of `c`. The classifier is untrusted: the numeric side
checks this hypothesis per block by fitting the template of the assigned class and testing the
residual. Class `3` holds for every block (`inClass_three`), so a classifier that answers `3`
on a block is always sound there. -/
theorem kakPassSmall_correct (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4) (c : Circuit n)
    (hcls : ClassifierSound cls c) :
    ∃ ρ : ℕ → Fin 15 → ℝ,
      unitaryDenote (Circuit.ofList (realizeS ρ (kakPassSmall cls c))) = unitaryDenote c := by
  obtain ⟨ρ, φ, h⟩ := exists_listMatrix_realizeS (kakPassSmall cls c)
    (valid_kakPassSmall cls c hcls)
  refine ⟨ρ, ?_⟩
  rw [Optimization.RoutingPerm.unitaryDenote_eq_channel,
    Optimization.RoutingPerm.unitaryDenote_eq_channel]
  exact unitaryChannel_eq_of_val_eq_smul φ (h.trans (by rw [listMatrix_flatMap_kakPassSmall]))

/-- **CNOT count of the small-template KAK pass.** Under every valuation of the angles the
realized circuit has at most as many CNOTs as `c`, whatever the classifier answers. -/
theorem cnotCount_realizeS_kakPassSmall_le (cls : Matrix (Fin 4) (Fin 4) ℂ → Fin 4)
    (c : Circuit n) (ρ : ℕ → Fin 15 → ℝ) :
    cnotCount (realizeS ρ (kakPassSmall cls c)) ≤ cnotCount (OpenQASM.toGateList c) := by
  refine (cnotCount_realizeS_le _ (small_kakPassSmall cls c) ρ).trans (le_of_eq ?_)
  rw [kakPassSmall, flatMap_blockItemsS, cnotCount_collectBlocks]

/-! ## The pass with exact fitted angles -/

/-- A block fitter with payloads in `β`: for a block `gs` on `(i, j)` it proposes a class,
exact angles and a payload (for instance the global phase of its floating-point fit), or
nothing. -/
abbrev BlockFit (n : ℕ) (β : Type) :=
  Fin n → Fin n → List (Gate n) → Option (Fin 4 × (Fin 15 → PiLin) × β)

variable {β : Type}

/-- One segment of the exact KAK pass, with the fitter evaluated once on it: a block `gs` on
`(i, j)` with `fit i j gs = some (k, θ, p)` and `k` smaller than its CNOT count gives
`tmplGatesQ k i j θ` and the payload list `[p]`; every other segment gives its gates and no
payload. -/
def blockEmit (fit : BlockFit n β) : Block n → List (Gate n) × List β
  | .gate g => ([g], [])
  | .pair i j gs =>
    match fit i j gs with
    | some (k, θ, p) => if k.val < cnotCount gs then (tmplGatesQ k i j θ, [p]) else (gs, [])
    | none => (gs, [])

/-- The KAK pass with exact angles: over `collectBlocks l`, the gates and the payloads of
`blockEmit fit` on each segment, concatenated (the payloads are those of the replaced blocks,
in order). The fitter is evaluated once per segment, one task per segment (`parMap`). -/
def kakEmit (fit : BlockFit n β) (l : List (Gate n)) : List (Gate n) × List β :=
  let r := parMap (blockEmit fit) (collectBlocks l)
  (r.flatMap Prod.fst, r.flatMap Prod.snd)

/-- The gates of `kakEmit fit l` are the gates of `blockEmit fit` over `collectBlocks l`. -/
theorem kakEmit_fst (fit : BlockFit n β) (l : List (Gate n)) :
    (kakEmit fit l).1 = (collectBlocks l).flatMap fun b => (blockEmit fit b).1 := by
  simp [kakEmit, List.flatMap_map]

/-- **CNOT count of the exact KAK pass.** The gates of `kakEmit fit l` have at most as many
CNOTs as `l`, whatever the fitter answers. -/
theorem cnotCount_kakEmit_le (fit : BlockFit n β) (l : List (Gate n)) :
    cnotCount (kakEmit fit l).1 ≤ cnotCount l := by
  rw [← cnotCount_collectBlocks l, kakEmit_fst]
  refine cnotCount_flatMap_le _ _ _ fun b _ => ?_
  cases b with
  | gate g => exact le_rfl
  | pair i j gs =>
    rcases h : fit i j gs with _ | ⟨k, θ, p⟩
    · simp [blockEmit, h, Block.gates]
    · by_cases hk : k.val < cnotCount gs
      · simp only [blockEmit, h, hk, ite_true, Block.gates, cnotCount_tmplGatesQ]
        exact hk.le
      · simp [blockEmit, h, hk, Block.gates]

/-- The hypothesis of the exact KAK pass: on every block of `l` where `fit` proposes a class
`k` smaller than the CNOT count, the template of class `k` at the proposed angles has the
matrix of the block up to a global phase. The numeric side checks it per block by the
residual of the floating-point fit. -/
def FitSound (fit : BlockFit n β) (l : List (Gate n)) : Prop :=
  ∀ i j gs k θ p, Block.pair i j gs ∈ collectBlocks l → fit i j gs = some (k, θ, p) →
    k.val < cnotCount gs →
      ∃ φ : ℝ, listMatrix (tmplGatesQ k i j θ) = Complex.exp (φ * I) • listMatrix gs

/-- **Correctness of the exact KAK pass.** Under `FitSound fit l`, the matrix of the gates of
`kakEmit fit l` is the matrix of `l` up to a global phase. -/
theorem listMatrix_kakEmit (fit : BlockFit n β) (l : List (Gate n)) (hfit : FitSound fit l) :
    ∃ φ : ℝ, listMatrix (kakEmit fit l).1 = Complex.exp (φ * I) • listMatrix l := by
  rw [← listMatrix_collectBlocks l, kakEmit_fst]
  refine exists_listMatrix_flatMap _ _ _ fun b hb => ?_
  cases b with
  | gate g => exact ⟨0, by simp [blockEmit, Block.gates]⟩
  | pair i j gs =>
    rcases h : fit i j gs with _ | ⟨k, θ, p⟩
    · exact ⟨0, by simp [blockEmit, h, Block.gates]⟩
    · by_cases hk : k.val < cnotCount gs
      · simp only [blockEmit, h, hk, ite_true, Block.gates]
        exact hfit i j gs k θ p hb h hk
      · exact ⟨0, by simp [blockEmit, h, hk, Block.gates]⟩

end CatCrypt.Quantum.Synthesis.KAKPassSmall
