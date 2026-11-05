/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.RewriteFixpoint
public import CatCrypt.Quantum.Optimization.UnitarySoundFull
public import CatCrypt.Quantum.Optimization.FusionSound
public import CatCrypt.Quantum.Optimization.CommuteSound
public import CatCrypt.Quantum.Optimization.CommuteMergeSound
public import CatCrypt.Quantum.Optimization.NotPropSound
public import CatCrypt.Quantum.Optimization.Embed2Commute

/-!
# Real-semantics soundness of the Level-4 rewrite rules

The Level-4 optimizer `rewriteFixpointOptimize` (`RewriteFixpoint.lean`)
rewrites a gate list to a fixpoint with a fixed library of local rewrite rules
(`allCircuitRules`).  Each rule is a `CircuitRule`: it matches a
prefix window of the gate list and, when it fires, returns
`some (matchLen, replacement)`.

A `CircuitRule` carries no soundness obligation in its data: soundness is
established here, separately from the definition, because these matrix-level
proofs depend on `unitaryDenote` and the full commutation/fusion
infrastructure, which in turn depend on `RewriteFixpoint.lean`.  This file
states the soundness of every rule against the unitary-channel semantics
`unitaryDenote` (ρ ↦ UρU†): whenever a rule fires on
`gs` returning `(m, repl)`, the denotation of the matched window `gs.take m`
equals the denotation of `repl`.  We package this as the predicate `SoundU`
and discharge it for all 19 rules in `allCircuitRules`, culminating in

* `rewriteFixpointRules_soundU` — every rule in `allCircuitRules n` is `SoundU`.

`EGraphSound` combines `rewriteFixpointRules_soundU` with the splice lemma
`unitaryDenote_ofList_append` into the soundness of the rewriting loop
`saturateCircuit` and of `rewriteFixpointOptimize`.

## How each rule is discharged

Almost every rule is exactly one of the matrix identities already proven in the
committed infrastructure:

* self-inverse cancellations (`HH/XX/YY/ZZ/CNOT/CZ/T·Tdg/Tdg·T`) — the
  `template*_correct` / `cancelCNOT_correctU` facts (`gateEmbedding · = 1`);
* merges (`TT→S`, `SS→Z`, `Tdg·Tdg→RzQ(-1/2)`) — `templateTT/SS_correct`,
  `mergeTdgTdg_correctU` (`tDaggerGate_sq`), with `gateEmbedding_RzQ_neg_half`
  identifying the exact rotation `RzQ(-1/2)` with `Rz(-π/2)`;
* Hadamard conjugations (`HXH→Z`, `HZH→X`) — `templateHXH/HZH_correct`;
* X-on-target past CNOT — `embedGate1_X_cnot_target_comm` (`NotPropSound`);
* disjoint commutation and the disjoint commute-then-merge — the disjoint
  embedding-commutation lemmas plus the merge facts;
* the *control* commute-then-merge (`tControlCommuteMerge`) — a fresh fact that
  a diagonal gate on the CNOT **control** commutes past the CNOT
  (`embedHigh_diag_cnot_comm`), since CNOT permutes only within the
  control-`1` block and a diagonal `embedHigh` matrix is constant there.

The `xCommuteCNOTControl_rule` never fires (its `apply` is `fun _ => none`), so
its soundness is vacuous.

## Main results

* `udL` — the unitary-channel denotation of a gate list.
* `SoundU` — whenever a rewrite rule fires, the matched window and its replacement have the
  same `udL` denotation.
* `rewriteFixpointRules_soundU` — every rule of `allCircuitRules n` satisfies `SoundU`.
* `commuteMerge_soundU`, `commuteDisjoint_soundU` — the commute-then-merge and the
  disjoint-commutation rules satisfy `SoundU`.
* `tControlCommuteMerge_soundU` — the rule moving a diagonal gate past a CNOT on its control
  wire and merging it satisfies `SoundU`.
* `gateEmbedding_disjoint_comm` — the embeddings of two gates on disjoint qubits commute.
* `gateEmbedding_RzQ_neg_half` — the exact rotation `RzQ q (-1/2)` embeds as `Rz q (-π/2)`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.TemplateMatching
open CatCrypt.Quantum.Optimization.UnitarySound
open CatCrypt.Quantum.Optimization.UnitarySoundFull
open CatCrypt.Quantum.Optimization.FusionSound
open CatCrypt.Quantum.Optimization.CommuteSound
open CatCrypt.Quantum.Optimization.CommuteMergeSound
open CatCrypt.Quantum.Optimization.NotPropSound
open CatCrypt.Quantum.Optimization.MixedCommute
open CatCrypt.Quantum.Optimization.ControlCommute
open CatCrypt.Quantum.Optimization.CommutationRules (targetQubits disjointQubits)
open CatCrypt.Quantum.UnitaryChannel
open scoped Matrix

namespace CatCrypt.Quantum.Optimization.EGraphRuleSound

open CatCrypt.Quantum.Optimization.RewriteFixpoint

variable {n : ℕ}

/-! ## The list-level soundness predicate -/

/-- `unitaryDenote` of a gate list (via `Circuit.ofList`). -/
noncomputable def udL (gs : List (Gate n)) : QComp (2 ^ n) Unit :=
  unitaryDenote (Circuit.ofList gs)

/-- A `CircuitRule` is **unitary-sound** when, on every gate list it fires on,
the matched window and the replacement have the same `unitaryDenote`.  Splicing
the replacement into the surrounding circuit then preserves the denotation by
`unitaryDenote_ofList_append`. -/
def SoundU (r : CircuitRule n) : Prop :=
  ∀ (gs : List (Gate n)) (m : ℕ) (repl : List (Gate n)),
    r.apply gs = some (m, repl) → udL (gs.take m) = udL repl

/-! ## Window bridges: gate-list windows as `Circuit.seq` chains

Every committed `CorrectU` / `*_correctU` fact is phrased on a `Circuit.seq`
chain of `Circuit.single`s.  These bridges rewrite the gate-list windows the
rewrite rules produce into that `seq` shape so the proven facts drop in. -/

@[simp] theorem udL_nil : udL ([] : List (Gate n)) = QComp.qpure () := rfl

theorem udL_single (g : Gate n) : udL [g] = denoteGateU g := by
  simp only [udL, Circuit.ofList]
  exact unitaryDenote_single g

/-- A two-gate window equals the `seq` of the two singletons. -/
theorem udL_two (a b : Gate n) :
    udL [a, b] = unitaryDenote ((Circuit.single a).seq (Circuit.single b)) := by
  rw [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_single]
  show QComp.qbind (denoteGateU a) (fun _ => QComp.qbind (denoteGateU b) (fun _ => QComp.qpure ()))
     = QComp.qbind (denoteGateU a) (fun _ => denoteGateU b)
  have hb : (fun (_ : Unit) => QComp.qpure (d := 2 ^ n) ()) = QComp.qpure :=
    funext (fun () => rfl)
  rw [hb, QComp.qbind_qpure]

/-- A three-gate window equals the nested `seq` of the three singletons. -/
theorem udL_three (a b c : Gate n) :
    udL [a, b, c] =
      unitaryDenote ((Circuit.single a).seq ((Circuit.single b).seq (Circuit.single c))) := by
  rw [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_seq,
    unitaryDenote_single, unitaryDenote_single]
  show QComp.qbind (denoteGateU a)
        (fun _ => QComp.qbind (denoteGateU b)
          (fun _ => QComp.qbind (denoteGateU c) (fun _ => QComp.qpure ())))
     = QComp.qbind (denoteGateU a) (fun _ => QComp.qbind (denoteGateU b) (fun _ => denoteGateU c))
  have hc : (fun (_ : Unit) => QComp.qpure (d := 2 ^ n) ()) = QComp.qpure :=
    funext (fun () => rfl)
  rw [hc, QComp.qbind_qpure]

/-! ## Self-inverse cancellation rules

Each fires on a same-qubit pair and replaces it by the empty list.  The window
identity is the corresponding `template*_correct` / `cancelCNOT_correctU` fact
(`udL [g, g] = QComp.qpure () = udL []`). -/

theorem cancelHH_soundU : SoundU (cancelHH_rule n) := by
  rintro gs m repl h
  simp only [cancelHH_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two]; exact templateHH_correct q

theorem cancelXX_soundU : SoundU (cancelXX_rule n) := by
  rintro gs m repl h
  simp only [cancelXX_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two]; exact templateXX_correct q

theorem cancelYY_soundU : SoundU (cancelYY_rule n) := by
  rintro gs m repl h
  simp only [cancelYY_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two]; exact templateYY_correct q

theorem cancelZZ_soundU : SoundU (cancelZZ_rule n) := by
  rintro gs m repl h
  simp only [cancelZZ_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two]; exact templateZZ_correct q

theorem cancelTTdg_soundU : SoundU (cancelTTdg_rule n) := by
  rintro gs m repl h
  simp only [cancelTTdg_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two]; exact templateTTdg_correct q

theorem cancelTdgT_soundU : SoundU (cancelTdgT_rule n) := by
  rintro gs m repl h
  simp only [cancelTdgT_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two]; exact templateTdgT_correct q

theorem cancelCNOT_soundU : SoundU (cancelCNOT_rule n) := by
  rintro gs m repl h
  simp only [cancelCNOT_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i c t c' t' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two]
  by_cases hct : c = t
  · subst hct
    -- CNOT c c is the identity, so [CNOT c c, CNOT c c] denotes the identity too.
    show unitaryDenote ((Circuit.single (Gate.CNOT c c)).seq (Circuit.single (Gate.CNOT c c)))
      = unitaryDenote (Circuit.ofList [])
    simp only [unitaryDenote_single, Circuit.ofList, unitaryDenote]
    have heta : (fun (_ : Unit) => denoteGateU (Gate.CNOT c c : Gate n))
              = (fun () => denoteGateU (Gate.CNOT c c)) := funext (fun () => rfl)
    rw [heta, denoteGateU_compose]
    have hmat : gateEmbedding (Gate.CNOT c c : Gate n) * gateEmbedding (Gate.CNOT c c) = 1 := by
      rw [gateEmbedding_CNOT_self]; simp
    rw [show gateEmbedding_unitaryGroup (Gate.CNOT c c : Gate n)
          * gateEmbedding_unitaryGroup (Gate.CNOT c c) = 1 from Subtype.ext hmat,
      unitaryChannel_one_eq_qpure]
  · exact cancelCNOT_correctU hct

theorem cancelCZ_soundU : SoundU (cancelCZ_rule n) := by
  rintro gs m repl h
  simp only [cancelCZ_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i c t c' t' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two]
  show unitaryDenote ((Circuit.single (Gate.CZ c t)).seq (Circuit.single (Gate.CZ c t)))
    = unitaryDenote (Circuit.ofList [])
  simp only [unitaryDenote_single, Circuit.ofList, unitaryDenote]
  have heta : (fun (_ : Unit) => denoteGateU (Gate.CZ c t : Gate n))
            = (fun () => denoteGateU (Gate.CZ c t)) := funext (fun () => rfl)
  rw [heta, denoteGateU_compose]
  have hmat : gateEmbedding (Gate.CZ c t : Gate n) * gateEmbedding (Gate.CZ c t) = 1 := by
    by_cases hct : c = t
    · subst hct; rw [gateEmbedding_CZ_self]; simp
    · simp only [gateEmbedding, dite_eq_right hct]
      rw [embedGate2_mul]
      have : czGate * czGate = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [czGate, Matrix.mul_apply, Fin.sum_univ_four]
      rw [this, embedGate2_one]
  rw [show gateEmbedding_unitaryGroup (Gate.CZ c t : Gate n)
        * gateEmbedding_unitaryGroup (Gate.CZ c t) = 1 from Subtype.ext hmat,
    unitaryChannel_one_eq_qpure]

/-! ## T-count merging rules

`T;T → S`, `S;S → Z`, `Tdg;Tdg → RzQ(-1/2)`.  The window identity is the
`templateTT/SS_correct` / `mergeTdgTdg_correctU` matrix fact, with the singleton
replacement rewritten by `udL_single` and, for `RzQ(-1/2)`, by
`udL_RzQ_neg_half`. -/

/-- Replacing a window's denotation against a single-gate replacement. -/
theorem udL_single' (g : Gate n) :
    udL [g] = unitaryDenote (Circuit.single g) := by
  rw [udL_single, unitaryDenote_single]

theorem mergeTT_soundU : SoundU (mergeTT_rule n) := by
  rintro gs m repl h
  simp only [mergeTT_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two, udL_single']
  exact templateTT_correct q

theorem mergeSS_soundU : SoundU (mergeSS_rule n) := by
  rintro gs m repl h
  simp only [mergeSS_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_two, udL_single']
  exact templateSS_correct q

/-- The exact rotation `RzQ q (-1/2)` embeds as the real rotation `Rz q (-π/2)`. -/
theorem gateEmbedding_RzQ_neg_half (q : Fin n) :
    gateEmbedding (Gate.RzQ q (-(1 / 2)) : Gate n)
      = gateEmbedding (Gate.Rz q (-(Real.pi / 2))) := by
  change embedGate1 n q (rzGate (CatCrypt.Quantum.PiLin.toReal (-(1 / 2))))
    = embedGate1 n q (rzGate (-(Real.pi / 2)))
  rw [show CatCrypt.Quantum.PiLin.toReal (-(1 / 2)) = -(Real.pi / 2) by
    simp only [PiLin.one_eq_ofPi, PiLin.ofNat_eq_ofPi, PiLin.ofPi_div_ofPi, PiLin.neg_ofPi,
      PiLin.toReal_ofPi]
    push_cast; ring]

/-- The one-gate windows `[RzQ q (-1/2)]` and `[Rz q (-π/2)]` denote the same
channel. -/
theorem udL_RzQ_neg_half (q : Fin n) :
    udL [(Gate.RzQ q (-(1 / 2)) : Gate n)] = udL [Gate.Rz q (-(Real.pi / 2))] := by
  have hemb : gateEmbedding_unitaryGroup (Gate.RzQ q (-(1 / 2)) : Gate n)
      = gateEmbedding_unitaryGroup (Gate.Rz q (-(Real.pi / 2))) :=
    Subtype.ext (gateEmbedding_RzQ_neg_half q)
  rw [udL_single, udL_single]
  simp only [denoteGateU, hemb]

theorem mergeTdgTdg_soundU : SoundU (mergeTdgTdg_rule n) := by
  rintro gs m repl h
  simp only [mergeTdgTdg_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q q' _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [decide_eq_true_eq] at hq; subst hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_RzQ_neg_half, udL_two, udL_single']
  exact tdgTdg_unitaryDenote q

/-! ## Hadamard conjugation rules

`H;X;H → Z` and `H;Z;H → X`, three-gate windows discharged by
`templateHXH/HZH_correct`. -/

theorem hxhToZ_soundU : SoundU (hxhToZ_rule n) := by
  rintro gs m repl h
  simp only [hxhToZ_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q₁ q₂ q₃ _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_three, udL_single']
  exact templateHXH_correct q₁

theorem hzhToX_soundU : SoundU (hzhToX_rule n) := by
  rintro gs m repl h
  simp only [hzhToX_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q₁ q₂ q₃ _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  rw [udL_three, udL_single']
  exact templateHZH_correct q₁

/-! ## Commutation helper

A matrix-level commutation `gateEmbedding b * gateEmbedding a =
gateEmbedding a * gateEmbedding b` lifts to a window swap
`udL [a, b] = udL [b, a]`.  This is the `GateCommutesU` mechanism of
`CommuteMergeSound`, specialized to closed two-gate windows. -/

theorem udL_swap_of_emb {a b : Gate n}
    (hcomm : gateEmbedding b * gateEmbedding a = gateEmbedding a * gateEmbedding b) :
    udL [a, b] = udL [b, a] := by
  rw [udL_two, udL_two]
  simp only [unitaryDenote_seq, unitaryDenote_single]
  have ea : (fun (_ : Unit) => denoteGateU (n := n) b) = (fun () => denoteGateU b) :=
    funext (fun () => rfl)
  have eb : (fun (_ : Unit) => denoteGateU (n := n) a) = (fun () => denoteGateU a) :=
    funext (fun () => rfl)
  rw [ea, denoteGateU_compose, eb, denoteGateU_compose]
  congr 1
  exact Subtype.ext hcomm

/-! ## X-on-target commutes past CNOT

`X(t); CNOT(c,t) → CNOT(c,t); X(t)` when `t ≠ c`.  Window identity via
`embedGate1_X_cnot_target_comm` (`NotPropSound`). -/

theorem xCommuteCNOTTarget_soundU : SoundU (xCommuteCNOTTarget_rule n) := by
  rintro gs m repl h
  simp only [xCommuteCNOTTarget_rule] at h
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i q c t _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hq
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hq
  obtain ⟨rfl, hqc⟩ := hq
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  have hct : c ≠ q := fun he => hqc (he.symm)
  refine udL_swap_of_emb ?_
  -- gateEmbedding (CNOT c q) * gateEmbedding (X q) = gateEmbedding (X q) * gateEmbedding (CNOT c q)
  rw [gateEmbedding_X, show gateEmbedding (Gate.CNOT c q : Gate n)
        = embedGate2 n c q Programs.Qubit.cnot hct from by simp [gateEmbedding, hct]]
  exact (embedGate1_X_cnot_target_comm hct).symm

/-- The disabled control-propagation rule never fires, so its soundness is
vacuous. -/
theorem xCommuteCNOTControl_soundU : SoundU (xCommuteCNOTControl_rule n) := by
  rintro gs m repl h
  simp only [xCommuteCNOTControl_rule] at h
  exact absurd h (by simp)

/-! ## Window-to-matrix reductions

`udL` of a 2- or 3-gate window equals `unitaryChannel` of the (reversed-order)
matrix product of the gate embeddings.  Then every commute/merge rule reduces to
a single `gateEmbedding` matrix equation. -/

theorem udL_two_channel (a b : Gate n) :
    udL [a, b] = unitaryChannel (gateEmbedding_unitaryGroup b * gateEmbedding_unitaryGroup a) := by
  rw [udL_two, unitaryDenote_seq, unitaryDenote_single, unitaryDenote_single]
  have ea : (fun (_ : Unit) => denoteGateU (n := n) b) = (fun () => denoteGateU b) :=
    funext (fun () => rfl)
  rw [ea, denoteGateU_compose]

theorem udL_three_channel (a b c : Gate n) :
    udL [a, b, c] = unitaryChannel
      (gateEmbedding_unitaryGroup c * gateEmbedding_unitaryGroup b
        * gateEmbedding_unitaryGroup a) := by
  have hbody : udL [a, b, c]
      = QComp.qbind (denoteGateU a) (fun _ => QComp.qbind (denoteGateU b)
          (fun _ => QComp.qbind (denoteGateU c) (fun _ => QComp.qpure ()))) := rfl
  rw [hbody, qbind3_fold]
  have hk : (fun (_ : Unit) => QComp.qpure (d := 2 ^ n) ()) = QComp.qpure :=
    funext (fun () => rfl)
  rw [hk, QComp.qbind_qpure]

/-- A window-3 → window-2 identity in matrix form: if the reversed embedding
products agree, the windows agree under `udL`. -/
theorem udL_three_eq_two_of_emb {a b c x y : Gate n}
    (hmat : gateEmbedding_unitaryGroup c * gateEmbedding_unitaryGroup b
              * gateEmbedding_unitaryGroup a
          = gateEmbedding_unitaryGroup y * gateEmbedding_unitaryGroup x) :
    udL [a, b, c] = udL [x, y] := by
  rw [udL_three_channel, udL_two_channel, hmat]

/-- A window-3 → singleton identity in matrix form. -/
theorem udL_three_eq_one_of_emb {a b c x : Gate n}
    (hmat : gateEmbedding_unitaryGroup c * gateEmbedding_unitaryGroup b
              * gateEmbedding_unitaryGroup a = gateEmbedding_unitaryGroup x) :
    udL [a, b, c] = udL [x] := by
  rw [udL_three_channel, hmat, udL_single]
  rfl

/-- `gateEmbedding_unitaryGroup` of a product is the matrix product (component
form), so subtype-level embedding equations follow from raw matrix equations. -/
theorem ug_val_mul (a b : Gate n) :
    ((gateEmbedding_unitaryGroup a * gateEmbedding_unitaryGroup b :
        Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : Matrix _ _ ℂ)
      = gateEmbedding a * gateEmbedding b := rfl

/-- Window-3 → window-2 from a **raw** matrix equation. -/
theorem udL_three_eq_two_of_rawEmb {a b c x y : Gate n}
    (hmat : gateEmbedding c * gateEmbedding b * gateEmbedding a
          = gateEmbedding y * gateEmbedding x) :
    udL [a, b, c] = udL [x, y] := by
  refine udL_three_eq_two_of_emb (Subtype.ext ?_)
  show gateEmbedding c * gateEmbedding b * gateEmbedding a
     = gateEmbedding y * gateEmbedding x
  exact hmat

/-- Window-3 → singleton from a **raw** matrix equation. -/
theorem udL_three_eq_one_of_rawEmb {a b c x : Gate n}
    (hmat : gateEmbedding c * gateEmbedding b * gateEmbedding a = gateEmbedding x) :
    udL [a, b, c] = udL [x] := by
  refine udL_three_eq_one_of_emb (Subtype.ext ?_)
  show gateEmbedding c * gateEmbedding b * gateEmbedding a = gateEmbedding x
  exact hmat

/-! ## Diagonality of the basic phase-gate matrices -/

theorem isDiagonal_tGate : MixedCommute.IsDiagonal Programs.Qubit.tGate := by
  intro r c hrc; fin_cases r <;> fin_cases c <;> simp_all [Programs.Qubit.tGate]

theorem isDiagonal_tDaggerGate : MixedCommute.IsDiagonal tDaggerGate := by
  intro r c hrc; fin_cases r <;> fin_cases c <;> simp_all [tDaggerGate]

theorem isDiagonal_phaseS : MixedCommute.IsDiagonal Programs.Qubit.phaseS := by
  intro r c hrc; fin_cases r <;> fin_cases c <;> simp_all [Programs.Qubit.phaseS]

/-! ## Gate-level control commute: a diagonal single-qubit gate on the control
of `CNOT c t` (with `c ≠ t`) commutes past it
(`ControlCommute.gateEmbedding_cnot_diag_control_comm`). -/

/-- Master control commute-then-merge step (to a single merged gate).  `g₁` and
`g₃` are diagonal single-qubit gates on the control `c`; their merge matrix
`D₃ * D₁` equals the merged gate `x`'s embedding matrix. -/
theorem tControl_merge_two {c t : Fin n} (hct : c ≠ t)
    {g₁ g₃ x : Gate n} {D₁ D₃ : Matrix (Fin 2) (Fin 2) ℂ}
    (h₁ : gateEmbedding g₁ = embedGate1 n c D₁) (hD₁ : MixedCommute.IsDiagonal D₁)
    (h₃ : gateEmbedding g₃ = embedGate1 n c D₃)
    (hx : gateEmbedding x = embedGate1 n c (D₃ * D₁)) :
    udL [g₁, Gate.CNOT c t, g₃] = udL [Gate.CNOT c t, x] := by
  refine udL_three_eq_two_of_rawEmb ?_
  rw [h₃, h₁, hx]
  -- emb g₃ * emb CNOT * emb g₁ = emb x * emb CNOT
  rw [mul_assoc, gateEmbedding_cnot_diag_control_comm hct hD₁, ← mul_assoc,
    embedGate1_mul]

/-- Master control commute-then-cancel step (to just the CNOT). -/
theorem tControl_merge_one {c t : Fin n} (hct : c ≠ t)
    {g₁ g₃ : Gate n} {D₁ D₃ : Matrix (Fin 2) (Fin 2) ℂ}
    (h₁ : gateEmbedding g₁ = embedGate1 n c D₁) (hD₁ : MixedCommute.IsDiagonal D₁)
    (h₃ : gateEmbedding g₃ = embedGate1 n c D₃)
    (hcancel : D₃ * D₁ = 1) :
    udL [g₁, Gate.CNOT c t, g₃] = udL [Gate.CNOT c t] := by
  refine udL_three_eq_one_of_rawEmb ?_
  rw [h₃, h₁]
  rw [mul_assoc, gateEmbedding_cnot_diag_control_comm hct hD₁, ← mul_assoc,
    embedGate1_mul, hcancel, embedGate1_one, one_mul]

/-! ## Disjoint commute-then-merge (diagonal gate on a qubit disjoint from the
two-qubit gate) -/

/-- A single-qubit gate on qubit `q` disjoint from the CNOT's qubits commutes
past `CNOT c t` (`q ≠ c`, `q ≠ t`; no diagonality needed). -/
theorem gateEmbedding_cnot_disjoint_comm {q c t : Fin n} (hqc : q ≠ c) (hqt : q ≠ t)
    (D : Matrix (Fin 2) (Fin 2) ℂ) :
    gateEmbedding (Gate.CNOT c t : Gate n) * embedGate1 n q D
      = embedGate1 n q D * gateEmbedding (Gate.CNOT c t) := by
  by_cases hct : c = t
  · subst hct; rw [gateEmbedding_CNOT_self]; simp
  · rw [show gateEmbedding (Gate.CNOT c t : Gate n)
          = embedGate2 n c t Programs.Qubit.cnot hct from by simp [gateEmbedding, hct]]
    exact (MixedCommute.embedGate1_embedGate2_disjoint_comm hqc hqt hct D
      Programs.Qubit.cnot).symm

/-- A single-qubit gate on qubit `q` disjoint from the CZ's qubits commutes past
`CZ c t`. -/
theorem gateEmbedding_cz_disjoint_comm {q c t : Fin n} (hqc : q ≠ c) (hqt : q ≠ t)
    (D : Matrix (Fin 2) (Fin 2) ℂ) :
    gateEmbedding (Gate.CZ c t : Gate n) * embedGate1 n q D
      = embedGate1 n q D * gateEmbedding (Gate.CZ c t) := by
  by_cases hct : c = t
  · subst hct; rw [gateEmbedding_CZ_self]; simp
  · rw [show gateEmbedding (Gate.CZ c t : Gate n)
          = embedGate2 n c t czGate hct from by simp [gateEmbedding, hct]]
    exact (MixedCommute.embedGate1_embedGate2_disjoint_comm hqc hqt hct D czGate).symm

/-- Disjoint commute-then-merge to a single merged gate, parameterized by the
gate-level commutation `hcomm` of the two-qubit gate `g₂` past `embedGate1 q ·`. -/
theorem disjoint_merge_two {q : Fin n} {g₁ g₂ g₃ x : Gate n}
    {D₁ D₃ : Matrix (Fin 2) (Fin 2) ℂ}
    (h₁ : gateEmbedding g₁ = embedGate1 n q D₁)
    (h₃ : gateEmbedding g₃ = embedGate1 n q D₃)
    (hx : gateEmbedding x = embedGate1 n q (D₃ * D₁))
    (hcomm : gateEmbedding g₂ * embedGate1 n q D₁ = embedGate1 n q D₁ * gateEmbedding g₂) :
    udL [g₁, g₂, g₃] = udL [g₂, x] := by
  refine udL_three_eq_two_of_rawEmb ?_
  rw [h₃, h₁, hx, mul_assoc, hcomm, ← mul_assoc, embedGate1_mul]

/-- Disjoint commute-then-cancel to just `g₂`. -/
theorem disjoint_merge_one {q : Fin n} {g₁ g₂ g₃ : Gate n}
    {D₁ D₃ : Matrix (Fin 2) (Fin 2) ℂ}
    (h₁ : gateEmbedding g₁ = embedGate1 n q D₁)
    (h₃ : gateEmbedding g₃ = embedGate1 n q D₃)
    (hcancel : D₃ * D₁ = 1)
    (hcomm : gateEmbedding g₂ * embedGate1 n q D₁ = embedGate1 n q D₁ * gateEmbedding g₂) :
    udL [g₁, g₂, g₃] = udL [g₂] := by
  refine udL_three_eq_one_of_rawEmb ?_
  rw [h₃, h₁, mul_assoc, hcomm, ← mul_assoc, embedGate1_mul, hcancel,
    embedGate1_one, one_mul]

/-! ## The control commute-then-merge rule -/

theorem tControlCommuteMerge_soundU : SoundU (tControlCommuteMerge_rule n) := by
  rintro gs m repl h
  simp only [tControlCommuteMerge_rule] at h
  -- Peel the three-gate head and the diagonal-on-control guard.
  split at h <;> rename_i heq <;>
    [skip; skip; skip; skip; skip; skip; skip; exact absurd h (by simp)]
  all_goals (
    split at h <;> [skip; exact absurd h (by simp)]
    rename_i hguard
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      decide_eq_true_eq] at hguard
    obtain ⟨⟨rfl, rfl⟩, hct⟩ := hguard
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.take])
  · -- T ; CNOT ; T  →  CNOT ; S
    rename_i t c
    exact tControl_merge_two hct (g₁ := Gate.T c) (g₃ := Gate.T c) (x := Gate.S c)
      (D₁ := Programs.Qubit.tGate) (D₃ := Programs.Qubit.tGate)
      rfl isDiagonal_tGate rfl
      (by rw [show Programs.Qubit.tGate * Programs.Qubit.tGate = Programs.Qubit.phaseS
            from tGate_sq_eq_phaseS]; rfl)
  · -- T ; CNOT ; Tdg  →  CNOT
    rename_i t c
    exact tControl_merge_one hct (g₁ := Gate.T c) (g₃ := Gate.Tdg c)
      (D₁ := Programs.Qubit.tGate) (D₃ := tDaggerGate)
      rfl isDiagonal_tGate rfl tDaggerGate_mul_tGate
  · -- Tdg ; CNOT ; T  →  CNOT
    rename_i t c
    exact tControl_merge_one hct (g₁ := Gate.Tdg c) (g₃ := Gate.T c)
      (D₁ := tDaggerGate) (D₃ := Programs.Qubit.tGate)
      rfl isDiagonal_tDaggerGate rfl tGate_mul_tDaggerGate
  · -- Tdg ; CNOT ; Tdg  →  CNOT ; RzQ(-1/2)
    rename_i t c
    exact tControl_merge_two hct (g₁ := Gate.Tdg c) (g₃ := Gate.Tdg c)
      (x := Gate.RzQ c (-(1 / 2)))
      (D₁ := tDaggerGate) (D₃ := tDaggerGate)
      rfl isDiagonal_tDaggerGate rfl
      (by rw [gateEmbedding_RzQ_neg_half, tDaggerGate_sq]; rfl)
  · -- S ; CNOT ; S  →  CNOT ; Z
    rename_i t c
    exact tControl_merge_two hct (g₁ := Gate.S c) (g₃ := Gate.S c) (x := Gate.Z c)
      (D₁ := Programs.Qubit.phaseS) (D₃ := Programs.Qubit.phaseS)
      rfl isDiagonal_phaseS rfl
      (by rw [show Programs.Qubit.phaseS * Programs.Qubit.phaseS = Programs.Qubit.pauliZ
            from phaseS_sq_eq_pauliZ]; rfl)
  · -- Z ; CNOT ; Z  →  CNOT
    rename_i t c
    exact tControl_merge_one hct (g₁ := Gate.Z c) (g₃ := Gate.Z c)
      (D₁ := Programs.Qubit.pauliZ) (D₃ := Programs.Qubit.pauliZ)
      rfl isDiagonal_pauliZ rfl Programs.Qubit.pauliZ_sq
  · -- Rz α ; CNOT ; Rz β  →  CNOT ; Rz (α+β)
    rename_i α tgt ctrl β
    refine tControl_merge_two hct (g₁ := Gate.Rz ctrl α) (g₃ := Gate.Rz ctrl β)
      (x := Gate.Rz ctrl (α + β))
      (D₁ := rzGate α) (D₃ := rzGate β)
      rfl (isDiagonal_rzGate α) rfl ?_
    show gateEmbedding (Gate.Rz ctrl (α + β) : Gate n) = embedGate1 n ctrl (rzGate β * rzGate α)
    rw [show rzGate β * rzGate α = rzGate (α + β) from by rw [rzGate_mul]; ring_nf]
    rfl

/-! ## General disjoint commutation (the `commuteDisjoint` rule)

We classify each gate's embedding as either a single-qubit `embedGate1 q M`
(targeting `[q]`) or a two-qubit `embedGate2 c t M` / identity (targeting
`[c, t]`).  Disjointness then lets the existing `embedGate1_disjoint_comm` /
`embedGate1_embedGate2_disjoint_comm` lemmas commute every combination *except*
two two-qubit gates on four disjoint qubits, for which the supporting
`embedGate2 × embedGate2` disjoint-commutation lemma is not yet in the
`MixedCommute` infrastructure (see `SORRY` below). -/

/-- Embedding of a single-qubit gate, with its (single) target. -/
def SingleEmbed (g : Gate n) : Prop :=
  ∃ (q : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ),
    gateEmbedding g = embedGate1 n q M ∧ targetQubits g = [q]

/-- Embedding of a two-qubit gate (or its degenerate identity), with its two
nominal targets. -/
def TwoEmbed (g : Gate n) : Prop :=
  ∃ (c t : Fin n),
    targetQubits g = [c, t] ∧
    (c = t ∧ gateEmbedding g = 1 ∨
      ∃ (M : Matrix (Fin 4) (Fin 4) ℂ) (h : c ≠ t), gateEmbedding g = embedGate2 n c t M h)

theorem gate_single_or_two (g : Gate n) : SingleEmbed g ∨ TwoEmbed g := by
  cases g with
  | H q => exact Or.inl ⟨q, _, rfl, rfl⟩
  | X q => exact Or.inl ⟨q, _, rfl, rfl⟩
  | Y q => exact Or.inl ⟨q, _, rfl, rfl⟩
  | Z q => exact Or.inl ⟨q, _, rfl, rfl⟩
  | T q => exact Or.inl ⟨q, _, rfl, rfl⟩
  | Tdg q => exact Or.inl ⟨q, _, rfl, rfl⟩
  | S q => exact Or.inl ⟨q, _, rfl, rfl⟩
  | Rz q θ => exact Or.inl ⟨q, _, rfl, rfl⟩
  | RzQ q a => exact Or.inl ⟨q, _, rfl, rfl⟩
  | CNOT c t =>
    refine Or.inr ⟨c, t, rfl, ?_⟩
    by_cases h : c = t
    · exact Or.inl ⟨h, by simp [gateEmbedding, h]⟩
    · exact Or.inr ⟨Programs.Qubit.cnot, h, by simp [gateEmbedding, h]⟩
  | CZ c t =>
    refine Or.inr ⟨c, t, rfl, ?_⟩
    by_cases h : c = t
    · exact Or.inl ⟨h, by simp [gateEmbedding, h]⟩
    · exact Or.inr ⟨czGate, h, by simp [gateEmbedding, h]⟩

/-- Membership of a qubit in `targetQubits` for the single / two cases lets us
extract the disequalities forced by `disjointQubits`. -/
theorem disjoint_not_mem {g₁ g₂ : Gate n} (hdis : disjointQubits g₁ g₂ = true)
    {q : Fin n} (hq : q ∈ targetQubits g₁) : q ∉ targetQubits g₂ := by
  simp only [disjointQubits, List.all_eq_true] at hdis
  have := hdis q (by simpa using hq)
  simpa using this

theorem disjointQubits_symm {g₁ g₂ : Gate n} (hdis : disjointQubits g₁ g₂ = true) :
    disjointQubits g₂ g₁ = true := by
  have key : ∀ x ∈ targetQubits g₂, x ∉ targetQubits g₁ :=
    fun x hx => fun hx' => disjoint_not_mem hdis hx' hx
  simp only [disjointQubits, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not]
  intro x hx
  exact key x hx

/-- **General disjoint-commutation of gate embeddings.**  The single×single,
single×two and two×single cases are discharged by the committed
`embedGate1`-commutation lemmas; the two×two case is the documented gap. -/
theorem gateEmbedding_disjoint_comm {g₁ g₂ : Gate n}
    (hdis : disjointQubits g₁ g₂ = true) :
    gateEmbedding g₂ * gateEmbedding g₁ = gateEmbedding g₁ * gateEmbedding g₂ := by
  rcases gate_single_or_two g₁ with ⟨q₁, M₁, he₁, ht₁⟩ | ⟨c₁, t₁, ht₁, hg₁⟩ <;>
  rcases gate_single_or_two g₂ with ⟨q₂, M₂, he₂, ht₂⟩ | ⟨c₂, t₂, ht₂, hg₂⟩
  · -- single × single
    have hq : q₁ ≠ q₂ := by
      have := disjoint_not_mem hdis (q := q₁) (by rw [ht₁]; simp)
      rw [ht₂] at this; simpa using this
    rw [he₁, he₂, DisjointCommute.embedGate1_disjoint_comm hq.symm]
  · -- single × two
    rcases hg₂ with ⟨_, hg₂⟩ | ⟨M₂, hct₂, hg₂⟩
    · rw [hg₂]; simp
    · have hnm : q₁ ∉ targetQubits g₂ := disjoint_not_mem hdis (by rw [ht₁]; simp)
      rw [ht₂] at hnm
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnm
      obtain ⟨hqc, hqt⟩ := hnm
      rw [he₁, hg₂, MixedCommute.embedGate1_embedGate2_disjoint_comm hqc hqt hct₂ M₁ M₂]
  · -- two × single
    rcases hg₁ with ⟨_, hg₁⟩ | ⟨M₁, hct₁, hg₁⟩
    · rw [hg₁]; simp
    · have hnm : q₂ ∉ targetQubits g₁ :=
        disjoint_not_mem (disjointQubits_symm hdis) (by rw [ht₂]; simp)
      rw [ht₁] at hnm
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnm
      obtain ⟨hqc, hqt⟩ := hnm
      rw [he₂, hg₁, ← MixedCommute.embedGate1_embedGate2_disjoint_comm hqc hqt hct₁ M₂ M₁]
  · -- two × two: two 2-qubit gates on disjoint pairs commute
    rcases hg₁ with ⟨_, hg₁⟩ | ⟨M₁, hct₁, hg₁⟩
    · rw [hg₁]; simp
    · rcases hg₂ with ⟨_, hg₂⟩ | ⟨M₂, hct₂, hg₂⟩
      · rw [hg₂]; simp
      · have hnm1 : c₁ ∉ targetQubits g₂ := disjoint_not_mem hdis (by rw [ht₁]; simp)
        have hnm2 : t₁ ∉ targetQubits g₂ := disjoint_not_mem hdis (by rw [ht₁]; simp)
        rw [ht₂] at hnm1 hnm2
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnm1 hnm2
        obtain ⟨hc₁c₂, hc₁t₂⟩ := hnm1
        obtain ⟨ht₁c₂, ht₁t₂⟩ := hnm2
        rw [hg₁, hg₂]
        exact (Embed2Commute.embedGate2_embedGate2_disjoint_comm hct₁ hct₂
          hc₁c₂ hc₁t₂ ht₁c₂ ht₁t₂ M₁ M₂).symm

/-! ## The disjoint commute-then-merge rule -/

theorem commuteMerge_soundU : SoundU (commuteMerge_rule n) := by
  rintro gs m repl h
  simp only [commuteMerge_rule] at h
  split at h <;> rename_i heq <;>
    [skip; skip; skip; skip; skip; skip; skip; skip; exact absurd h (by simp)]
  all_goals (
    split at h <;> [skip; exact absurd h (by simp)]
    rename_i hguard
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      decide_eq_true_eq] at hguard
    obtain ⟨⟨rfl, hqc⟩, hqt⟩ := hguard
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.take])
  · -- T ; CNOT ; T  →  CNOT ; S
    rename_i q c t
    exact disjoint_merge_two (g₁ := Gate.T q) (g₂ := Gate.CNOT c t) (g₃ := Gate.T q)
      (x := Gate.S q) (D₁ := Programs.Qubit.tGate) (D₃ := Programs.Qubit.tGate)
      rfl rfl
      (by rw [show Programs.Qubit.tGate * Programs.Qubit.tGate = Programs.Qubit.phaseS
            from tGate_sq_eq_phaseS]; rfl)
      (gateEmbedding_cnot_disjoint_comm hqc hqt _)
  · -- T ; CNOT ; Tdg  →  CNOT
    rename_i q c t
    exact disjoint_merge_one (g₁ := Gate.T q) (g₂ := Gate.CNOT c t) (g₃ := Gate.Tdg q)
      (D₁ := Programs.Qubit.tGate) (D₃ := tDaggerGate)
      rfl rfl tDaggerGate_mul_tGate
      (gateEmbedding_cnot_disjoint_comm hqc hqt _)
  · -- Tdg ; CNOT ; T  →  CNOT
    rename_i q c t
    exact disjoint_merge_one (g₁ := Gate.Tdg q) (g₂ := Gate.CNOT c t) (g₃ := Gate.T q)
      (D₁ := tDaggerGate) (D₃ := Programs.Qubit.tGate)
      rfl rfl tGate_mul_tDaggerGate
      (gateEmbedding_cnot_disjoint_comm hqc hqt _)
  · -- Tdg ; CNOT ; Tdg  →  CNOT ; RzQ(-1/2)
    rename_i q c t
    refine disjoint_merge_two (g₁ := Gate.Tdg q) (g₂ := Gate.CNOT c t) (g₃ := Gate.Tdg q)
      (x := Gate.RzQ q (-(1 / 2))) (D₁ := tDaggerGate) (D₃ := tDaggerGate)
      rfl rfl ?_ (gateEmbedding_cnot_disjoint_comm hqc hqt _)
    rw [gateEmbedding_RzQ_neg_half, tDaggerGate_sq]; rfl
  · -- S ; CNOT ; S  →  CNOT ; Z
    rename_i q c t
    exact disjoint_merge_two (g₁ := Gate.S q) (g₂ := Gate.CNOT c t) (g₃ := Gate.S q)
      (x := Gate.Z q) (D₁ := Programs.Qubit.phaseS) (D₃ := Programs.Qubit.phaseS)
      rfl rfl
      (by rw [show Programs.Qubit.phaseS * Programs.Qubit.phaseS = Programs.Qubit.pauliZ
            from phaseS_sq_eq_pauliZ]; rfl)
      (gateEmbedding_cnot_disjoint_comm hqc hqt _)
  · -- Z ; CNOT ; Z  →  CNOT
    rename_i q c t
    exact disjoint_merge_one (g₁ := Gate.Z q) (g₂ := Gate.CNOT c t) (g₃ := Gate.Z q)
      (D₁ := Programs.Qubit.pauliZ) (D₃ := Programs.Qubit.pauliZ)
      rfl rfl Programs.Qubit.pauliZ_sq
      (gateEmbedding_cnot_disjoint_comm hqc hqt _)
  · -- T ; CZ ; T  →  CZ ; S
    rename_i q c t
    exact disjoint_merge_two (g₁ := Gate.T q) (g₂ := Gate.CZ c t) (g₃ := Gate.T q)
      (x := Gate.S q) (D₁ := Programs.Qubit.tGate) (D₃ := Programs.Qubit.tGate)
      rfl rfl
      (by rw [show Programs.Qubit.tGate * Programs.Qubit.tGate = Programs.Qubit.phaseS
            from tGate_sq_eq_phaseS]; rfl)
      (gateEmbedding_cz_disjoint_comm hqc hqt _)
  · -- T ; CZ ; Tdg  →  CZ
    rename_i q c t
    exact disjoint_merge_one (g₁ := Gate.T q) (g₂ := Gate.CZ c t) (g₃ := Gate.Tdg q)
      (D₁ := Programs.Qubit.tGate) (D₃ := tDaggerGate)
      rfl rfl tDaggerGate_mul_tGate
      (gateEmbedding_cz_disjoint_comm hqc hqt _)

/-! ## The general disjoint-commutation rule -/

theorem commuteDisjoint_soundU : SoundU (commuteDisjoint_rule n) := by
  rintro gs m repl h
  simp only [commuteDisjoint_rule] at h
  -- gs = g₁ :: g₂ :: rest
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i g₁ g₂ rest
  -- disjointQubits guard
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i hdis
  -- rest = g₃ :: _
  split at h <;> [skip; exact absurd h (by simp)]
  rename_i g₃ rest'
  -- targetQubits g₁ == targetQubits g₃ guard
  split at h <;> [skip; exact absurd h (by simp)]
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.take]
  exact udL_swap_of_emb (gateEmbedding_disjoint_comm hdis)

/-! ## Aggregate: every rewrite rule is unitary-sound

`rewriteFixpointRules_soundU` states that each rule in the optimizer's library
`allCircuitRules` preserves `unitaryDenote` on the window it rewrites;
`EGraphSound` lifts it from windows to the rewriting loop with
`unitaryDenote_ofList_append`. -/

theorem rewriteFixpointRules_soundU : ∀ r ∈ allCircuitRules n, SoundU r := by
  intro r hr
  simp only [allCircuitRules, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tControlCommuteMerge_soundU
  · exact commuteMerge_soundU
  · exact cancelHH_soundU
  · exact cancelXX_soundU
  · exact cancelYY_soundU
  · exact cancelZZ_soundU
  · exact cancelCNOT_soundU
  · exact cancelCZ_soundU
  · exact cancelTTdg_soundU
  · exact cancelTdgT_soundU
  · exact mergeTT_soundU
  · exact mergeSS_soundU
  · exact mergeTdgTdg_soundU
  · exact hxhToZ_soundU
  · exact hzhToX_soundU
  · exact xCommuteCNOTTarget_soundU
  · exact xCommuteCNOTControl_soundU
  · exact commuteDisjoint_soundU

@[deprecated rewriteFixpointRules_soundU (since := "2026-10-10")]
alias eGraphRules_soundU := rewriteFixpointRules_soundU

end CatCrypt.Quantum.Optimization.EGraphRuleSound
