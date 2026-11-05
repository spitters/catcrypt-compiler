/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QrunchFuse

/-!
# Rotations commuted backward across `cx`

`QrunchFuse.fuseQ` moves every pending rotation forward: a diagonal rotation (`p`, `rz`) passes
the control of a `cx` and an `rx` its target, toward the later statements. `commuteQ` is the
same scan run backward: it reads the statement list from its end, so a rotation that commutes
with a `cx` moves across it toward the earlier statements and joins the one-qubit run before
it, merging with a rotation about the same axis there. The pass is
`commuteQ l = (fuseQ l.reverse).reverse`.

Its exactness is the mirror of `qelibListMatrix_fuseQ`: reading the matrix of a reversed list,
`qelibListMatrix l.reverse`, a scan step from `v` realises the input statement before the
pending rotations of `v` (`step_reverse_spec`), so the scan of the reversed list realises the
matrix of the list (`qelibListMatrix_commuteQ`). The rewrites are those of `fuseQ`: rotations
about one axis compose by adding angles, rotations on distinct qubits commute, and the
commutations `commute_cx_ctrlKeep` and `commute_cx_tgtKeep` of a `cx` with a diagonal rotation
on its control and an `rx` on its target.

## Main results

* `commuteQ` — the backward pass.
* `qelibListMatrix_commuteQ` — `qelibListMatrix (commuteQ l) = qelibListMatrix l`.
* `length_commuteQ_le` — the pass emits at most as many statements as it reads.
* `cxCount_commuteQ` — it emits exactly the `cx` statements it reads.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.Qelib
open CatCrypt.Quantum.QrunchFuse

namespace CatCrypt.Quantum.QrunchCommute

variable {n : ℕ}

/-- The backward commutation pass: the scan of `fuseQ` on the reversed statement list. -/
def commuteQ (l : List (QGate n)) : List (QGate n) := (fuseQ l.reverse).reverse

/-! ## Matrices of reversed lists -/

/-- The matrix of a reversed concatenation: the first part applied last. -/
theorem qelibListMatrix_reverse_append (l₁ l₂ : List (QGate n)) :
    qelibListMatrix (l₁ ++ l₂).reverse
      = qelibListMatrix l₁.reverse * qelibListMatrix l₂.reverse := by
  rw [List.reverse_append, QrunchBasis.qelibListMatrix_append]

/-- The matrix of a reversed list with a head statement: the head applied last. -/
theorem qelibListMatrix_reverse_cons (g : QGate n) (l : List (QGate n)) :
    qelibListMatrix (g :: l).reverse = qelibMatrix g * qelibListMatrix l.reverse := by
  rw [List.reverse_cons, QrunchBasis.qelibListMatrix_append]
  simp [qelibListMatrix]

/-- An emitted rotation is a list of at most one statement, its own reverse. -/
theorem emit_reverse (q : Fin n) (e : Pend) : (emit q e).reverse = emit q e := by
  rcases e with _ | ⟨A, a⟩
  · rfl
  · by_cases h : isId A a = true <;> simp [emit, h]

/-- The reversed flushed statements realise the product of the pending rotations, which
commute. -/
theorem qelibListMatrix_reverse_flushOn (F : Fin n → Pend) {L : List (Fin n)} (hL : L.Nodup) :
    qelibListMatrix (flushOn F L).reverse = prodOn F L := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    rw [List.nodup_cons] at hL
    have hc : Commute (entryMat q (F q)) (prodOn F L) :=
      commute_prodOn fun i hi => commute_entryMat (fun h => hL.1 (by subst h; exact hi)) _ _
    rw [flushOn, List.flatMap_cons, qelibListMatrix_reverse_append, ← flushOn, ih hL.2,
      emit_reverse, qelibListMatrix_emit, prodOn, hc.eq]

/-- The kept and emitted parts of a rotation on the target of a `cx` commute: one of them is
absent. -/
theorem commute_tgtKeep_tgtEmit (t : Fin n) (e : Pend) :
    Commute (entryMat t (tgtKeep e)) (entryMat t (tgtEmit e)) := by
  rcases e with _ | ⟨_ | _ | _ | _, a⟩ <;> simp [tgtKeep, tgtEmit, entryMat]

/-- The kept and emitted parts of a rotation on the control of a `cx` commute: one of them is
absent. -/
theorem commute_ctrlKeep_ctrlEmit (c : Fin n) (e : Pend) :
    Commute (entryMat c (ctrlKeep e)) (entryMat c (ctrlEmit e)) := by
  rcases e with _ | ⟨_ | _ | _ | _, a⟩ <;> simp [ctrlKeep, ctrlEmit, entryMat]

/-- The rearrangement of a `cx` step read backward, in a monoid: the emitted parts `et`, `ec`
after the `cx` `g` after the rest `r` and the kept parts `kt`, `kc` equal the rest, the
rotations `kt * et` and `kc * ec`, and then `g`. -/
theorem cx_reverse_rearrange {M : Type*} [Monoid M] {g r kt et kc ec : M}
    (hg : Commute g (r * kt * kc)) (htr : Commute et r) (hcr : Commute ec r)
    (hck : Commute ec kt) (ht : Commute kt et) (hc : Commute kc ec) :
    et * ec * g * (r * kt * kc) = r * (kt * et) * (kc * ec) * g := by
  calc et * ec * g * (r * kt * kc) = et * (ec * (r * (kt * (kc * g)))) := by
        rw [mul_assoc (et * ec) g, hg.eq]; simp only [mul_assoc]
    _ = r * (et * (ec * (kt * (kc * g)))) := by rw [hcr.left_comm, htr.left_comm]
    _ = r * (kt * (et * (kc * (ec * g)))) := by
        rw [hck.left_comm, ht.symm.left_comm, hc.symm.left_comm]
    _ = r * (kt * et) * (kc * ec) * g := by simp only [mul_assoc]

/-! ## The scan read backward -/

/-- One scan step read backward: the reversed emitted statements after the next pending
rotations realise the pending rotations of `v` after the input statement. -/
theorem step_reverse_spec (v : Vector Pend n) (g : QGate n) :
    qelibListMatrix (step v g).1.reverse * prodOn (stF (step v g).2) (List.finRange n)
      = prodOn (stF v) (List.finRange n) * qelibMatrix g := by
  have hL := List.nodup_finRange n
  unfold step
  split
  · next q A a hg =>
    rw [eq_mkQ_of_axis? hg, qelibMatrix_mkQ, ← entryMat_some]
    have hc := commute_prodOn_setF_none q (some (A, a)) (stF v) (List.finRange n)
    have hx := prodOn_extract (stF v) hL (List.mem_finRange q)
    split
    · next B b hv =>
      have hv' : stF v q = some (B, b) := hv
      split
      · next hAB =>
        subst hAB
        have hm := entryMat_merge q A a b
        have hab : entryMat q (some (A, a)) * entryMat q (some (A, b))
            = entryMat q (some (A, b)) * entryMat q (some (A, a)) := by
          rw [← hm, ← entryMat_merge q A b a]
          simp only [entryMat_some, PiLin.toReal_add, add_comm]
        rw [List.reverse_nil, qelibListMatrix, one_mul, stF_setQ, prodOn_setF, hx, hv', hm, hab,
          mul_assoc]
      · have hb := commute_prodOn_setF_none q (some (B, b)) (stF v) (List.finRange n)
        rw [emit_reverse, stF_setQ, prodOn_setF, qelibListMatrix_emit, hx, hv', ← mul_assoc,
          hb.eq]
    · next hv =>
      have hv' : stF v q = none := hv
      rw [List.reverse_nil, qelibListMatrix, one_mul, stF_setQ, prodOn_setF, hx, hv', entryMat,
        mul_one]
  · next hg =>
    split
    · next c t =>
      split
      · rw [qelibListMatrix_reverse_append, qelibListMatrix_reverse_flushOn _ hL]
        simp [stF_replicate, prodOn_none, qelibListMatrix]
      · next hct =>
        set F := stF v
        have hF : stF (setQ (setQ v t (tgtKeep v[t])) c (ctrlKeep v[c]))
            = setF c (ctrlKeep (F c)) (setF t (tgtKeep (F t)) F) := by
          rw [stF_setQ, stF_setQ]; rfl
        have hxc := prodOn_extract F hL (List.mem_finRange c)
        have hxt := prodOn_extract (setF c none F) hL (List.mem_finRange t)
        have htc : setF c none F t = F t := by simp [setF, Ne.symm hct]
        rw [htc] at hxt
        have hR := setF_comm hct none (tgtKeep (F t)) F
        set R2 := prodOn (setF t none (setF c none F)) (List.finRange n)
        set CX := qelibMatrix (QGate.cx c t)
        have hR2 : Commute CX R2 := commute_prodOn fun i _ => by
          by_cases hic : i = c
          · subst hic; simp [setF, entryMat]
          · by_cases hit : i = t
            · subst hit; simp [setF, entryMat]
            · exact commute_cx_entryMat hct hic hit _
        have hK : Commute CX _ := commute_cx_ctrlKeep hct (F c)
        have hKt : Commute CX _ := commute_cx_tgtKeep hct (F t)
        have htr : Commute (entryMat t (tgtEmit (F t))) R2 :=
          commute_prodOn_setF_none t _ (setF c none F) _
        have hcr : Commute (entryMat c (ctrlEmit (F c))) R2 := by
          have h2 : setF t none (setF c none F) = setF c none (setF t none F) :=
            (setF_comm hct none none F).symm
          change Commute _ (prodOn (setF t none (setF c none F)) (List.finRange n))
          rw [h2]
          exact commute_prodOn_setF_none c _ (setF t none F) _
        have hck := commute_entryMat (Ne.symm hct) (ctrlEmit (F c)) (tgtKeep (F t))
        rw [hF, prodOn_setF _ c, hR, prodOn_setF (setF c none F) t, hxc, hxt,
          qelibListMatrix_reverse_append, qelibListMatrix_reverse_append, emit_reverse,
          emit_reverse, qelibListMatrix_emit, qelibListMatrix_emit, entryMat_tgt t (F t),
          entryMat_ctrl c (F c)]
        rw [show qelibListMatrix [QGate.cx c t].reverse = CX by simp [qelibListMatrix, CX]]
        exact cx_reverse_rearrange ((hR2.mul_right hKt).mul_right hK) htr hcr hck
          (commute_tgtKeep_tgtEmit t (F t)) (commute_ctrlKeep_ctrlEmit c (F c))
    · rw [qelibListMatrix_reverse_append, qelibListMatrix_reverse_flushOn _ hL]
      simp [stF_replicate, prodOn_none, qelibListMatrix]

/-- The scan from `v` read backward realises the pending rotations of `v` after the reversed
input. -/
theorem qelibListMatrix_reverse_fuseAux (l : List (QGate n)) :
    ∀ v : Vector Pend n,
      qelibListMatrix (fuseAux v l).reverse
        = prodOn (stF v) (List.finRange n) * qelibListMatrix l.reverse := by
  induction l with
  | nil =>
    intro v
    simp [fuseAux, qelibListMatrix, qelibListMatrix_reverse_flushOn _ (List.nodup_finRange n)]
  | cons g gs ih =>
    intro v
    simp only [fuseAux, qelibListMatrix_reverse_append, ih, qelibListMatrix_reverse_cons,
      ← mul_assoc, step_reverse_spec]

/-! ## The pass -/

/-- **The pass is exact**: the commuted statements have the matrix of the input. -/
theorem qelibListMatrix_commuteQ (l : List (QGate n)) :
    qelibListMatrix (commuteQ l) = qelibListMatrix l := by
  rw [commuteQ, fuseQ, qelibListMatrix_reverse_fuseAux, stF_replicate, prodOn_none, one_mul,
    List.reverse_reverse]

/-- **The pass does not lengthen the list.** -/
theorem length_commuteQ_le (l : List (QGate n)) : (commuteQ l).length ≤ l.length := by
  simpa [commuteQ] using length_fuseQ_le l.reverse

/-- **The pass keeps every `cx` statement.** -/
theorem cxCount_commuteQ (l : List (QGate n)) : cxCount (commuteQ l) = cxCount l := by
  have h := cxCount_fuseQ l.reverse
  simp only [commuteQ, cxCount, List.countP_reverse] at h ⊢
  exact h

end CatCrypt.Quantum.QrunchCommute
