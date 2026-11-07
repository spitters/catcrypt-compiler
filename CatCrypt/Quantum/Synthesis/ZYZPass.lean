/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.KAKPass
public import CatCrypt.Quantum.Synthesis.ParMap

/-!
# One-qubit run resynthesis by the ZYZ template

`collectRuns` cuts a gate list into maximal runs of one-qubit gates, with runs open on several
qubits at once. One left-to-right pass keeps, for every qubit `q`, the open run on `q`. A
one-qubit gate on `q` extends the run on `q`. Any other gate closes the runs on the qubits it
acts on, which are emitted in qubit order, and is emitted plain. The runs still open at the
end are emitted in qubit order. The output reorders the input only by moving gates past gates
on other qubits, so it denotes the same unitary (`listMatrix_collectRuns`).

`zyzEmit fit l` replaces each run `gs` on `q` for which an untrusted fitter `fit` proposes
an axis `a` and exact angles `θ` by the template `runTemplate a q θ`: the ZYZ template
`zyzGatesQ q θ` or the XYX template `xyxGatesQ q θ`, whose rotations `Rx(a)` are the gates
`H, RzQ a, H`. The fitter decides which runs are worth replacing and with which template, and
is evaluated once per run. The value of
`zyzEmit fit l` is the pair of the gates and the payloads the fitter returns with the replaced
runs.

## Main results

* `listMatrix_collectRuns` — the segments of `collectRuns l` compose to the matrix of `l`.
* `cnotCount_zyzEmit` — the gates of `zyzEmit fit l` have as many CNOTs as `l`, whatever `fit`
  answers.
* `listMatrix_zyzEmit` — under `ZFitSound fit l`, the matrix of the gates of `zyzEmit fit l`
  is that of `l` up to a global phase.
-/

@[expose] public section

set_option autoImplicit false

open Matrix Complex
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Synthesis.KAK CatCrypt.Quantum.Synthesis.KAKPass
open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil listMatrix_append)
open CatCrypt.Quantum.Optimization.CommutationRules (targetQubits)
open CatCrypt.Quantum.OpenQASMImportGates (rxMatrix ryMatrix listMatrix_rxGates
  phaseS_hadamard_rz_hadamard_sdg)

namespace CatCrypt.Quantum.Synthesis.ZYZPass

variable {n : ℕ}

/-! ## One-qubit gates -/

/-- The qubit of a one-qubit gate; `none` for `CNOT` and `CZ`. -/
def oneQ? : Gate n → Option (Fin n)
  | .H i | .X i | .Y i | .Z i | .T i | .Tdg i | .S i | .Rz i _ | .RzQ i _ => some i
  | .CNOT _ _ | .CZ _ _ => none

theorem oneQ?_spec {g : Gate n} {q : Fin n} (h : oneQ? g = some q) :
    targetQubits g = [q] ∧ ∃ M, gateEmbedding g = embedGate1 n q M := by
  cases g <;> simp only [oneQ?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact ⟨rfl, _, rfl⟩

theorem isCNOT_of_oneQ? {g : Gate n} {q : Fin n} (h : oneQ? g = some q) : isCNOT g = false := by
  cases g <;> simp_all [oneQ?, isCNOT]

/-- A one-qubit gate on `q` commutes with every gate that does not act on `q`. -/
theorem commute_of_oneQ? {x y : Gate n} {q : Fin n} (hx : oneQ? x = some q)
    (hy : q ∉ targetQubits y) : Commute (gateEmbedding x) (gateEmbedding y) := by
  obtain ⟨-, M, hM⟩ := oneQ?_spec hx
  rw [hM]
  cases y <;> simp only [targetQubits, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hy <;> simp only [gateEmbedding]
  all_goals first
    | exact Optimization.DisjointCommute.embedGate1_disjoint_comm hy _ _
    | split
  all_goals first
    | exact Commute.one_right _
    | exact Optimization.MixedCommute.embedGate1_embedGate2_disjoint_comm hy.1 hy.2 _ _ _

/-! ## Segments and the run scan -/

/-- A segment of a gate list: a gate outside any run, or a run of one-qubit gates on `q`. -/
inductive Seg (n : ℕ) where
  | gate : Gate n → Seg n
  | run : Fin n → List (Gate n) → Seg n

/-- The gates of a segment. -/
def Seg.gates : Seg n → List (Gate n)
  | .gate g => [g]
  | .run _ gs => gs

/-- The open runs of a scan state, qubit by qubit; each run holds its gates last gate first. -/
def stFun (v : Vector (List (Gate n)) n) (q : Fin n) : List (Gate n) := v[q]

/-- The gates of the open runs `F q` for the qubits `q` of `L`, in the order of `L`. -/
def stGatesOn (F : Fin n → List (Gate n)) (L : List (Fin n)) : List (Gate n) :=
  L.flatMap fun q => (F q).reverse

/-- The segments emitted when the runs `F q` for the qubits `q` with `p q` close, in qubit
order. -/
def emitRuns (F : Fin n → List (Gate n)) (p : Fin n → Bool) : List (Seg n) :=
  ((List.finRange n).filter p).map fun q => .run q (F q).reverse

/-- The segments emitted when the runs `F q` for the qubits `q` of `L` close, in the order
of `L`. -/
def emitRunsL (F : Fin n → List (Gate n)) (L : List (Fin n)) : List (Seg n) :=
  L.map fun q => .run q (F q).reverse

/-- The qubits `a` and `b` in increasing order, without repetition. -/
def pairAsc (a b : Fin n) : List (Fin n) :=
  if a < b then [a, b] else if b < a then [b, a] else [a]

/-- The qubits of a gate in increasing order, without repetition. -/
def qubitsAsc : Gate n → List (Fin n)
  | .CNOT c t => pairAsc c t
  | .CZ c t => pairAsc c t
  | g => targetQubits g

/-- The state `v` with the open runs on the qubits of `L` cleared. -/
def clearOn (v : Vector (List (Gate n)) n) (L : List (Fin n)) : Vector (List (Gate n)) n :=
  L.foldl (fun w (p : Fin n) => w.set p []) v

/-- The run scan over the state `v`, which holds the open run on each qubit. A one-qubit gate
on `q` extends the run on `q`. Any other gate closes the runs on its qubits, which are
emitted in qubit order, and is emitted plain. At the end every open run is emitted. Each step
updates the state in place at the qubits of its gate. -/
def runAux : Vector (List (Gate n)) n → List (Gate n) → List (Seg n)
  | v, [] => emitRuns (stFun v) fun _ => true
  | v, g :: gs =>
    match oneQ? g with
    | some q => runAux (v.set q (g :: v[q])) gs
    | none =>
      let L := qubitsAsc g
      emitRunsL (stFun v) L ++ .gate g :: runAux (clearOn v L) gs

/-- Maximal runs of one-qubit gates of a gate list, on several qubits at once. -/
def collectRuns (l : List (Gate n)) : List (Seg n) := runAux (Vector.replicate n []) l

/-! ## The scan preserves the matrix -/

/-- The invariant of the scan: the open run on `q` holds one-qubit gates on `q`. -/
def RunInv (F : Fin n → List (Gate n)) : Prop := ∀ q, ∀ g ∈ F q, oneQ? g = some q

theorem stFun_set (v : Vector (List (Gate n)) n) (q : Fin n) (x : List (Gate n)) :
    stFun (v.set q x) = fun p => if p = q then x else stFun v p := by
  funext p
  simp only [stFun]
  grind

theorem stFun_clearOn (L : List (Fin n)) :
    ∀ v : Vector (List (Gate n)) n,
      stFun (clearOn v L) = fun p => if p ∈ L then [] else stFun v p := by
  induction L with
  | nil => intro v; simp [clearOn]
  | cons a L ih =>
    intro v
    simp only [clearOn, List.foldl_cons] at ih ⊢
    rw [ih, stFun_set]
    funext p
    grind

theorem filter_finRange_eq (q : Fin n) :
    (List.finRange n).filter (fun p => decide (p = q)) = [q] := by
  rw [List.filter_eq, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange q)]
  rfl

theorem filter_finRange_pair (a b : Fin n) :
    (List.finRange n).filter (fun p => decide (p ∈ [a, b])) = pairAsc a b := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·))
    ((List.sortedLT_finRange n).pairwise.filter _) ?_ fun p => ?_
  · unfold pairAsc
    split_ifs <;> simp_all
  · unfold pairAsc
    split_ifs <;> simp <;> omega

/-- The qubits of `g` in increasing order are the qubits of `targetQubits g` in the order of
`List.finRange n`. -/
theorem filter_finRange_targetQubits (g : Gate n) :
    (List.finRange n).filter (fun p => decide (p ∈ targetQubits g)) = qubitsAsc g := by
  cases g with
  | CNOT c t => exact filter_finRange_pair c t
  | CZ c t => exact filter_finRange_pair c t
  | _ =>
    simp only [targetQubits, qubitsAsc, List.mem_singleton]
    exact filter_finRange_eq _

theorem mem_qubitsAsc {g : Gate n} {p : Fin n} : p ∈ qubitsAsc g ↔ p ∈ targetQubits g := by
  rw [← filter_finRange_targetQubits]
  simp

theorem emitRunsL_qubitsAsc (F : Fin n → List (Gate n)) (g : Gate n) :
    emitRunsL F (qubitsAsc g) = emitRuns F fun p => decide (p ∈ targetQubits g) := by
  rw [emitRuns, filter_finRange_targetQubits, emitRunsL]

theorem stFun_clearOn_qubitsAsc (v : Vector (List (Gate n)) n) (g : Gate n) :
    stFun (clearOn v (qubitsAsc g)) = fun p => if p ∈ targetQubits g then [] else stFun v p := by
  rw [stFun_clearOn]
  simp only [mem_qubitsAsc]

theorem flatMap_emitRuns (F : Fin n → List (Gate n)) (p : Fin n → Bool) :
    (emitRuns F p).flatMap Seg.gates = stGatesOn F ((List.finRange n).filter p) := by
  simp [emitRuns, stGatesOn, Seg.gates, List.flatMap_map]

theorem stGatesOn_ite (F : Fin n → List (Gate n)) (P : Fin n → Prop) [DecidablePred P]
    (L : List (Fin n)) :
    stGatesOn (fun q => if P q then [] else F q) L =
      stGatesOn F (L.filter fun q => !decide (P q)) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    by_cases hx : P x <;> simp_all [stGatesOn]

theorem commute_stGatesOn {F : Fin n → List (Gate n)} (hF : RunInv F) {L : List (Fin n)}
    {g : Gate n} (hg : ∀ q ∈ L, q ∉ targetQubits g) :
    Commute (gateEmbedding g) (listMatrix (stGatesOn F L)) := by
  apply commute_listMatrix
  intro x hx
  obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hx
  exact (commute_of_oneQ? (hF q x (List.mem_reverse.mp hxq)) (hg q hq)).symm

/-- The open runs may be emitted in the order of any partition of the qubits, since runs on
distinct qubits commute. -/
theorem listMatrix_stGatesOn_filter {F : Fin n → List (Gate n)} (hF : RunInv F)
    (p : Fin n → Bool) {L : List (Fin n)} (hL : L.Nodup) :
    listMatrix (stGatesOn F L) =
      listMatrix (stGatesOn F (L.filter p) ++ stGatesOn F (L.filter fun q => !p q)) := by
  induction L with
  | nil => rfl
  | cons x r ih =>
    rw [List.nodup_cons] at hL
    have ih' := ih hL.2
    have hc : Commute (listMatrix (F x).reverse) (listMatrix (stGatesOn F (r.filter p))) := by
      apply commute_listMatrix_listMatrix
      intro a ha b hb
      obtain ⟨y, hy, hby⟩ := List.mem_flatMap.mp hb
      have hyx : y ≠ x := fun h => hL.1 (h ▸ (List.mem_filter.mp hy).1)
      refine commute_of_oneQ? (hF x a (List.mem_reverse.mp ha)) ?_
      rw [(oneQ?_spec (hF y b (List.mem_reverse.mp hby))).1]
      simpa using hyx.symm
    by_cases hpx : p x = true
    · simp only [stGatesOn, List.filter_cons, hpx, Bool.not_true, ite_true,
        List.flatMap_cons, listMatrix_append] at ih' ⊢
      grind only
    · simp only [stGatesOn, List.filter_cons, hpx, Bool.not_false, ite_true,
        List.flatMap_cons, listMatrix_append] at ih' hc ⊢
      simp only [Bool.false_eq_true, ite_false]
      rw [ih', Matrix.mul_assoc, Matrix.mul_assoc, hc.eq]

theorem runInv_extend {F : Fin n → List (Gate n)} (hF : RunInv F) {g : Gate n} {q : Fin n}
    (hq : oneQ? g = some q) : RunInv (fun p => if p = q then g :: F q else F p) := by
  intro p x hx
  by_cases hp : p = q
  · subst hp
    simp only [ite_true, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hq
    · exact hF p x hx
  · simp only [hp, ite_false] at hx
    exact hF p x hx

theorem runInv_clear {F : Fin n → List (Gate n)} (hF : RunInv F) (P : Fin n → Prop)
    [DecidablePred P] : RunInv (fun p => if P p then [] else F p) := by
  intro p x hx
  simp only at hx
  split at hx
  · simp at hx
  · exact hF p x hx

theorem cnotCount_stGatesOn {F : Fin n → List (Gate n)} (hF : RunInv F) (L : List (Fin n)) :
    cnotCount (stGatesOn F L) = 0 := by
  simp only [cnotCount, List.countP_eq_zero]
  intro x hx
  obtain ⟨q, -, hxq⟩ := List.mem_flatMap.mp hx
  simp [isCNOT_of_oneQ? (hF q x (List.mem_reverse.mp hxq))]

theorem listMatrix_runAux (l : List (Gate n)) :
    ∀ v : Vector (List (Gate n)) n, RunInv (stFun v) →
      listMatrix ((runAux v l).flatMap Seg.gates) =
        listMatrix (stGatesOn (stFun v) (List.finRange n) ++ l) := by
  induction l with
  | nil => intro v _; simp [runAux, flatMap_emitRuns]
  | cons g gs ih =>
    intro v hv
    simp only [runAux]
    split
    · next q hq =>
      have hF' := runInv_extend hv hq
      have hL := List.nodup_finRange n
      rw [ih _ (by rw [stFun_set]; exact hF'), stFun_set, show v[q] = stFun v q from rfl,
        List.append_cons, listMatrix_append,
        listMatrix_append (_ ++ [g])]
      congr 1
      rw [listMatrix_stGatesOn_filter hF' (fun p => decide (p = q)) hL,
        listMatrix_append (stGatesOn (stFun v) _),
        listMatrix_stGatesOn_filter hv (fun p => decide (p = q)) hL, filter_finRange_eq]
      have hB : stGatesOn (fun p => if p = q then g :: stFun v q else stFun v p)
          ((List.finRange n).filter fun p => !decide (p = q)) =
          stGatesOn (stFun v) ((List.finRange n).filter fun p => !decide (p = q)) := by
        simp only [stGatesOn]
        refine List.flatMap_congr fun p hp => ?_
        simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not] at hp
        simp [hp.2]
      have hc := commute_stGatesOn hv (g := g)
        (L := (List.finRange n).filter fun p => !decide (p = q)) fun p hp => by
          rw [(oneQ?_spec hq).1]
          simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] at hp
          simpa using hp.2
      rw [hB]
      simp only [stGatesOn, List.flatMap_cons, List.flatMap_nil, ite_true, List.reverse_cons,
        List.append_nil, listMatrix_append, listMatrix_cons, listMatrix_nil] at hc ⊢
      rw [Matrix.one_mul, ← Matrix.mul_assoc, ← hc.eq, Matrix.mul_assoc]
    · next hq =>
      have hF' := runInv_clear hv (· ∈ targetQubits g)
      have hL := List.nodup_finRange n
      rw [emitRunsL_qubitsAsc,
        List.flatMap_append, List.flatMap_cons, flatMap_emitRuns, listMatrix_append,
        listMatrix_append, ih _ (by rw [stFun_clearOn_qubitsAsc]; exact hF'),
        stFun_clearOn_qubitsAsc, stGatesOn_ite,
        listMatrix_append, listMatrix_append (stGatesOn (stFun v) (List.finRange n)),
        listMatrix_stGatesOn_filter hv (fun p => decide (p ∈ targetQubits g)) hL]
      have hc := commute_stGatesOn hv (g := g)
        (L := (List.finRange n).filter fun p => !decide (p ∈ targetQubits g)) fun p hp => by
          simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] at hp
          exact hp.2
      simp only [Seg.gates, listMatrix_append, listMatrix_cons, listMatrix_nil, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (gateEmbedding g), hc.eq]
      simp only [Matrix.mul_assoc]

/-- The segments of `collectRuns l` compose to the matrix of `l`. -/
theorem listMatrix_collectRuns (l : List (Gate n)) :
    listMatrix ((collectRuns l).flatMap Seg.gates) = listMatrix l := by
  rw [collectRuns, listMatrix_runAux l _ (by simp [RunInv, stFun]),
    show stGatesOn (stFun (Vector.replicate n [])) (List.finRange n) = [] by
      simp [stGatesOn, stFun, List.flatMap_eq_nil_iff], List.nil_append]

/-! ## Validity and CNOT counts of the segments -/

/-- A run segment holds one-qubit gates on its qubit. -/
def Seg.Valid : Seg n → Prop
  | .gate _ => True
  | .run q gs => ∀ g ∈ gs, oneQ? g = some q

theorem valid_runAux (l : List (Gate n)) :
    ∀ v : Vector (List (Gate n)) n, RunInv (stFun v) → ∀ s ∈ runAux v l, s.Valid := by
  induction l with
  | nil =>
    intro v hv s hs
    simp only [runAux, emitRuns, List.mem_map] at hs
    obtain ⟨q, -, rfl⟩ := hs
    exact fun g hg => hv q g (List.mem_reverse.mp hg)
  | cons g gs ih =>
    intro v hv s hs
    simp only [runAux] at hs
    split at hs
    · next q hq =>
      exact ih _ (by rw [stFun_set]; exact runInv_extend hv hq) s hs
    · rcases List.mem_append.mp hs with hs | hs
      · simp only [emitRunsL, List.mem_map] at hs
        obtain ⟨q, -, rfl⟩ := hs
        exact fun x hx => hv q x (List.mem_reverse.mp hx)
      · rcases List.mem_cons.mp hs with rfl | hs
        · trivial
        · exact ih _
            (by rw [stFun_clearOn_qubitsAsc]; exact runInv_clear hv (· ∈ targetQubits g)) s hs

theorem valid_collectRuns (l : List (Gate n)) : ∀ s ∈ collectRuns l, s.Valid :=
  valid_runAux l _ (by simp [RunInv, stFun])

theorem cnotCount_eq_zero {q : Fin n} {gs : List (Gate n)} (h : ∀ g ∈ gs, oneQ? g = some q) :
    cnotCount gs = 0 := by
  simp only [cnotCount, List.countP_eq_zero]
  intro g hg
  simp [isCNOT_of_oneQ? (h g hg)]

theorem cnotCount_runAux (l : List (Gate n)) :
    ∀ v : Vector (List (Gate n)) n, RunInv (stFun v) →
      cnotCount ((runAux v l).flatMap Seg.gates) = cnotCount l := by
  induction l with
  | nil =>
    intro v hv
    simp only [runAux, flatMap_emitRuns, cnotCount_stGatesOn hv]
    rfl
  | cons g gs ih =>
    intro v hv
    simp only [runAux]
    split
    · next q hq =>
      rw [ih _ (by rw [stFun_set]; exact runInv_extend hv hq)]
      simp [cnotCount, isCNOT_of_oneQ? hq]
    · rw [emitRunsL_qubitsAsc, List.flatMap_append, List.flatMap_cons, flatMap_emitRuns]
      have h0 := cnotCount_stGatesOn hv
        ((List.finRange n).filter fun p => decide (p ∈ targetQubits g))
      have h1 := ih (clearOn v (qubitsAsc g))
        (by rw [stFun_clearOn_qubitsAsc]; exact runInv_clear hv (· ∈ targetQubits g))
      simp only [cnotCount, Seg.gates, List.countP_append, List.countP_cons,
        List.countP_nil] at h0 h1 ⊢
      omega

theorem cnotCount_collectRuns (l : List (Gate n)) :
    cnotCount ((collectRuns l).flatMap Seg.gates) = cnotCount l :=
  cnotCount_runAux l _ (by simp [RunInv, stFun])

/-! ## The XYX template -/

/-- The XYX product `Rx(β) · Ry(γ) · Rx(δ)`. -/
noncomputable def xyx (β γ δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := rxMatrix β * ryMatrix γ * rxMatrix δ

/-- The XYX template `Rx(β) · Ry(γ) · Rx(δ)` on qubit `q` with the exact angles
`(β, γ, δ) = (θ 0, θ 1, θ 2)`: `Rx(a)` is `H, RzQ a, H` and `Ry(γ)` is the gates of
`ryGatesA` with `ofPi (-(1 / 2))` for `−π/2`. -/
def xyxGatesQ (q : Fin n) (θ : Fin 3 → PiLin) : List (Gate n) :=
  OpenQASMImport.rxGates q (θ 2) ++ ryGatesA Gate.RzQ (PiLin.ofPi (-(1 / 2))) q (θ 1) ++
    OpenQASMImport.rxGates q (θ 0)

/-- The XYX template holds no CNOT. -/
theorem cnotCount_xyxGatesQ (q : Fin n) (θ : Fin 3 → PiLin) : cnotCount (xyxGatesQ q θ) = 0 := by
  simp [xyxGatesQ, OpenQASMImport.rxGates, cnotCount, isCNOT]

/-- The gates of `ryGatesA` over `Gate.RzQ` realise `Ry(γ)` times the global phase
`e^{i γ / 2}`. -/
theorem listMatrix_ryGatesQ (q : Fin n) (γ : PiLin) :
    listMatrix (ryGatesA Gate.RzQ (PiLin.ofPi (-(1 / 2))) q γ) =
      Complex.exp (I * ((γ.toReal / 2 : ℝ) : ℂ)) • embedGate1 n q (ryMatrix γ.toReal) := by
  simp only [ryGatesA, listMatrix_cons, listMatrix_nil, Matrix.one_mul, gateEmbedding,
    GateUnitarity.embedGate1_mul, toReal_ofPi_neg_half]
  rw [rzGate_neg_pi_div_two, phaseS_hadamard_rz_hadamard_sdg, GateUnitarity.embedGate1_smul]

/-- The XYX template has the matrix `xyx` at the real angles, times the global phase
`e^{i (β + γ + δ) / 2}`. -/
theorem listMatrix_xyxGatesQ (q : Fin n) (θ : Fin 3 → PiLin) :
    listMatrix (xyxGatesQ q θ) =
      Complex.exp (I * ((((θ 0).toReal + (θ 1).toReal + (θ 2).toReal) / 2 : ℝ) : ℂ)) •
        embedGate1 n q (xyx (θ 0).toReal (θ 1).toReal (θ 2).toReal) := by
  rw [xyxGatesQ, listMatrix_append, listMatrix_append, listMatrix_rxGates, listMatrix_rxGates,
    listMatrix_ryGatesQ]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, GateUnitarity.embedGate1_mul, xyx,
    Matrix.mul_assoc]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The pass -/

/-- The axes of a one-qubit run template: `zyz` for `Rz · Ry · Rz`, `xyx` for `Rx · Ry · Rx`. -/
inductive Axis where
  | zyz
  | xyx
  deriving DecidableEq, Repr

/-- The run template of an axis choice on qubit `q` at the exact angles `θ`. -/
def runTemplate : Axis → Fin n → (Fin 3 → PiLin) → List (Gate n)
  | .zyz => zyzGatesQ
  | .xyx => xyxGatesQ

/-- A run template holds no CNOT. -/
theorem cnotCount_runTemplate (a : Axis) (q : Fin n) (θ : Fin 3 → PiLin) :
    cnotCount (runTemplate a q θ) = 0 := by
  cases a
  · exact cnotCount_zyzGatesQ q θ
  · exact cnotCount_xyxGatesQ q θ

/-- A run fitter with payloads in `β`: for the segment at position `i` of `collectRuns l`, a
run `gs` on `q`, it proposes a template axis, exact angles and a payload (for instance the
global phase of its floating-point fit), or nothing. The position lets the fitter read the
neighbouring segments, for instance to choose the axis from the two-qubit gates around the
run. -/
abbrev ZFit (n : ℕ) (β : Type) :=
  ℕ → Fin n → List (Gate n) → Option (Axis × (Fin 3 → PiLin) × β)

variable {β : Type}

/-- One segment of the run pass at position `i`: a run `gs` on `q` with
`fit i q gs = some (a, θ, p)` gives `runTemplate a q θ` and the payload list `[p]`; every
other segment gives its gates and no payload. -/
def segEmit (fit : ZFit n β) (i : ℕ) : Seg n → List (Gate n) × List β
  | .gate g => ([g], [])
  | .run q gs =>
    match fit i q gs with
    | some (a, θ, p) => (runTemplate a q θ, [p])
    | none => (gs, [])

/-- The run pass with exact angles: over the segments of `collectRuns l` with their positions,
the gates and the payloads of `segEmit fit` on each segment, concatenated (the payloads are
those of the replaced runs, in order). The fitter is evaluated once per segment, one task per
segment (`parMap`). -/
def zyzEmit (fit : ZFit n β) (l : List (Gate n)) : List (Gate n) × List β :=
  let r := parMap (fun si => segEmit fit si.2 si.1) (collectRuns l).zipIdx
  (r.flatMap Prod.fst, r.flatMap Prod.snd)

/-- The gates of `zyzEmit fit l` are the gates of `segEmit fit` over the segments of
`collectRuns l` with their positions. -/
theorem zyzEmit_fst (fit : ZFit n β) (l : List (Gate n)) :
    (zyzEmit fit l).1 =
      (collectRuns l).zipIdx.flatMap fun si => (segEmit fit si.2 si.1).1 := by
  simp [zyzEmit, List.flatMap_map]

/-- A flat map over `zipIdx` that ignores the positions is the flat map over the list. -/
private theorem flatMap_zipIdx_fst {α γ : Type} (L : List α) (f : α → List γ) :
    L.zipIdx.flatMap (fun si => f si.1) = L.flatMap f := by
  rw [← List.flatMap_map (f := Prod.fst) (g := f), List.zipIdx_map_fst]

/-- A member `(s, i)` of `L.zipIdx` is the entry of `L` at `i`. -/
private theorem getElem?_of_mem_zipIdx {α : Type} {L : List α} {s : α} {i : ℕ}
    (h : (s, i) ∈ L.zipIdx) : L[i]? = some s := by
  grind [List.mem_zipIdx']

/-- **CNOT count of the run pass.** The gates of `zyzEmit fit l` have as many CNOTs as `l`,
whatever the fitter answers. -/
theorem cnotCount_zyzEmit (fit : ZFit n β) (l : List (Gate n)) :
    cnotCount (zyzEmit fit l).1 = cnotCount l := by
  rw [zyzEmit_fst, ← cnotCount_collectRuns l, ← flatMap_zipIdx_fst (collectRuns l) Seg.gates]
  refine cnotCount_flatMap _ _ _ fun si hsi => ?_
  obtain ⟨s, i⟩ := si
  have hv := valid_collectRuns l s (List.mem_of_getElem? (getElem?_of_mem_zipIdx hsi))
  cases s with
  | gate g => rfl
  | run q gs =>
    simp only [Seg.Valid] at hv
    simp only [segEmit, Seg.gates, cnotCount_eq_zero hv]
    split
    · exact cnotCount_runTemplate _ q _
    · exact cnotCount_eq_zero hv

/-- The hypothesis of the run pass: on every run `gs` on `q` at position `i` of
`collectRuns l` where `fit` proposes the axis `a` and angles `θ`, the template
`runTemplate a q θ` has the matrix of the run up to a global phase. The numeric side checks it
per run by the residual of the floating-point fit. -/
def ZFitSound (fit : ZFit n β) (l : List (Gate n)) : Prop :=
  ∀ i q gs a θ p, (collectRuns l)[i]? = some (Seg.run q gs) → fit i q gs = some (a, θ, p) →
    ∃ φ : ℝ, listMatrix (runTemplate a q θ) = Complex.exp (φ * I) • listMatrix gs

/-- **Correctness of the run pass.** Under `ZFitSound fit l`, the matrix of the gates of
`zyzEmit fit l` is the matrix of `l` up to a global phase. -/
theorem listMatrix_zyzEmit (fit : ZFit n β) (l : List (Gate n)) (hfit : ZFitSound fit l) :
    ∃ φ : ℝ, listMatrix (zyzEmit fit l).1 = Complex.exp (φ * I) • listMatrix l := by
  rw [zyzEmit_fst, ← listMatrix_collectRuns l, ← flatMap_zipIdx_fst (collectRuns l) Seg.gates]
  refine exists_listMatrix_flatMap _ _ _ fun si hsi => ?_
  obtain ⟨s, i⟩ := si
  cases s with
  | gate g => exact ⟨0, by simp [segEmit, Seg.gates]⟩
  | run q gs =>
    simp only [segEmit, Seg.gates]
    split
    · next a θ p hf => exact hfit i q gs a θ p (getElem?_of_mem_zipIdx hsi) hf
    · exact ⟨0, by simp⟩

end CatCrypt.Quantum.Synthesis.ZYZPass
