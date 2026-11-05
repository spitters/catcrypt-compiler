/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheckComplete
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

@[expose] public section

set_option autoImplicit false

/-!
# The index check on linear combinations and through the moves of the export frames

The index check `IdxInvCheck.idxInvCheckB` reads an upper bound on a sum of terms off the
linear forms of the terms (`linAlts`): atoms and a constant whose sum bounds the term. This
module proves that entailment is complete on linear combinations: when each term of a sum has
a linear form, the sum is entailed by the combination of the forms, either because one fact
bounds a sum containing all their atoms or because the bounds `hiOf` of the atoms, with the
constants, sum to within the bound. The bound of a trip index by the pair fact of its counter
is the instance used by a counted loop.

The frames of the export `ExportRegions.exportR` (`forFrame`, `whileFrame`, `ifFrame`,
`forArrFrame`) move words between registers: seeds, the two stages of a parallel assignment,
the shift of a carried block, the moves of immediates. The symbolic step of a register move
`movI d (.reg s)` sets `d` to the term of `s`, and the step of an immediate move
`movI d (.imm k)` sets `d` to the immediate at width `64`, with no guard. So a successor fact
read after a list of register moves is its renaming read before them, a fact that mentions
no written register is read unchanged, and the facts of a block that its symbolic run leaves
in place are entailed at its successors.

## Main results

* `mem_sumAlts_of_forms`: the sum of chosen linear forms of the terms is a form of the sum.
* `entails_le_of_form_sub`: a sum whose forms' atoms one fact contains is entailed.
* `entails_le_of_forms`, `entails_le_of_comb`: a sum whose forms have bounded atoms is
  entailed by the combination of the bounds.
* `entails_le_of_pair`: the trip-index bound `x ≤ b - k` from `x + c ≤ b` and `c ≥ k`.
* `symStep_movI_reg`, `symStep_movI_imm`, `symRun_movI_reg_cons`, `symRun_movI_imm_cons`,
  `symRun_regMoves`, `symRun_shiftMoves`: the symbolic run of the moves of the frames.
* `IdxFact.toS_setR_of_not_mem`, `succOk_setR_of_not_mem`: a fact that does not mention the
  written register is read unchanged.
* `succOk_foldl_setR`, `succOk_regMoves`: the facts of a successor after register moves are
  their renamings before them.
* `entails_startF_mem`, `succOk_of_keep`: the facts of a block that its final symbolic state
  reads as at the block entry are entailed at the successor.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
  (movI regMoves shiftMoves)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-! ## 1. Entailment on linear combinations -/

/-- **A sum of chosen forms is a form of the sum**: when `π t` is a linear form of each term
    `t` of `ts`, the concatenation of their atoms with the sum of their constants is one of
    the forms `sumAlts` of `ts`. -/
theorem mem_sumAlts_of_forms (F : List SFact) (π : STerm → List STerm × Int) :
    ∀ {ts : List STerm}, (∀ t ∈ ts, π t ∈ linAlts F t) →
      (ts.flatMap fun t => (π t).1, (ts.map fun t => (π t).2).sum) ∈ sumAlts F ts
  | [], _ => by simp [sumAlts]
  | t :: ts, h =>
      mem_altsAdd.mpr ⟨π t, h t List.mem_cons_self, _,
        mem_sumAlts_of_forms F π fun u hu => h u (List.mem_cons_of_mem _ hu), by simp⟩

/-- **A sum whose forms one fact contains is entailed**: when each term `t` of `ts` has the
    linear form `π t`, a fact `.le fs b` contains all their atoms (with the remaining terms
    `R`), and `b` less the lower bounds of `R` plus the constants of the forms is at most
    `b'`. -/
theorem entails_le_of_form_sub {F : List SFact} {ts fs R : List STerm} {b b' : Nat}
    (π : STerm → List STerm × Int) (hπ : ∀ t ∈ ts, π t ∈ linAlts F t)
    (hf : SFact.le fs b ∈ F) (hR : eraseAll fs (ts.flatMap fun t => (π t).1) = some R)
    (hb : (b : Int) - lbSum F R + (ts.map fun t => (π t).2).sum ≤ b') :
    entails F (.le ts b') = true := by
  have hl : leLin F ts b' = true := by
    simp only [leLin, List.any_eq_true]
    refine ⟨_, mem_sumAlts_of_forms F π hπ, ?_⟩
    simp only [leForm, Bool.or_eq_true, List.any_eq_true]
    refine Or.inr ⟨_, hf, ?_⟩
    simp only [leBy, hR, decide_eq_true_eq]
    omega
  simp [entails, hl]

/-- **A sum whose forms have bounded atoms is entailed**: when each term `t` of `ts` has the
    linear form `π t` and the bounds `formHi` of the forms sum to at most `b'`. -/
theorem entails_le_of_forms {F : List SFact} {ts : List STerm} {b' : Nat}
    (π : STerm → List STerm × Int) (hπ : ∀ t ∈ ts, π t ∈ linAlts F t)
    (hb : (ts.map fun t => formHi F (π t)).sum ≤ b') : entails F (.le ts b') = true := by
  have key : ∀ us : List STerm, (∀ t ∈ us, π t ∈ linAlts F t) →
      (us.map (hiNe F)).sum ≤ (us.map fun t => formHi F (π t)).sum := by
    intro us
    induction us with
    | nil => simp
    | cons t us ih =>
        intro h
        have h1 : hiNe F t ≤ termHi F t := by unfold hiNe; split <;> omega
        have h2 := termHi_le_form (h t List.mem_cons_self)
        have h3 := ih fun u hu => h u (List.mem_cons_of_mem _ hu)
        simp only [List.map_cons, List.sum_cons]
        omega
  have hl : hiLe F ts b' = true := by
    simp only [hiLe, decide_eq_true_eq]
    exact (key ts hπ).trans hb
  simp [entails, hl]

/-- `formHi` is at most the combination of upper bounds of the atoms of the form. -/
theorem formHi_le_of_bounds (F : List SFact) (u : STerm → Nat) {p : List STerm × Int}
    (h : ∀ a ∈ p.1, hiOf F F a ≤ u a) :
    formHi F p ≤ (((p.1.map u).sum : Int) + p.2).toNat := by
  have key : (p.1.map (hiOf F F)).sum ≤ (p.1.map u).sum := List.sum_le_sum h
  unfold formHi
  omega

/-- **Entailment is complete on linear combinations**: when each term `t` of `ts` has the
    linear form `π t`, every atom `a` of these forms has an upper bound `hiOf F F a ≤ u a`,
    and the combination of the bounds with the constants is at most `b'`, the sum of `ts` is
    entailed to be at most `b'`. -/
theorem entails_le_of_comb {F : List SFact} {ts : List STerm} {b' : Nat}
    (π : STerm → List STerm × Int) (u : STerm → Nat)
    (hπ : ∀ t ∈ ts, π t ∈ linAlts F t) (hu : ∀ t ∈ ts, ∀ a ∈ (π t).1, hiOf F F a ≤ u a)
    (hb : (ts.map fun t => ((((π t).1.map u).sum : Int) + (π t).2).toNat).sum ≤ b') :
    entails F (.le ts b') = true :=
  entails_le_of_forms π hπ ((List.sum_le_sum fun t ht =>
    formHi_le_of_bounds F u (hu t ht)).trans hb)

/-- **The trip-index bound**: a fact `.le [x, c] b` and a fact `.ge c k` entail `x ≤ b'`
    for every `b' ≥ b - k`. -/
theorem entails_le_of_pair {F : List SFact} {x c : STerm} {b k b' : Nat}
    (hle : SFact.le [x, c] b ∈ F) (hge : SFact.ge c k ∈ F) (hb : b - k ≤ b') :
    entails F (.le [x] b') = true :=
  entails_le_of_hiOf (by simpa using (hiOf_le_of_pair F hle hge).trans hb)

/-! ## 2. The symbolic run of the moves of the frames -/

/-- **The symbolic step of a register move** sets the target to the term of the source. -/
theorem symStep_movI_reg (ss : SSt) (d s : String) :
    symStep (movI d (.reg s)) ss = .ok (ss.setR d (ss.regs s)) [] := rfl

/-- **The symbolic step of an immediate move** sets the target to the immediate at width
    `64`. -/
theorem symStep_movI_imm (ss : SSt) (d : String) (k : Nat) :
    symStep (movI d (.imm k)) ss = .ok (ss.setR d (.immW 64 k)) [] := rfl

/-- A step with no guard followed by a run is the run from the state after the step. -/
theorem symRun_cons_of_ok {i : LinstrRM} {ss ss1 : SSt} (is : List LinstrRM)
    (h : symStep i ss = .ok ss1 []) : symRun (i :: is) ss = symRun is ss1 := by
  simp only [symRun, h]
  cases symRun is ss1 <;> simp

theorem symRun_movI_reg_cons (ss : SSt) (d s : String) (is : List LinstrRM) :
    symRun (movI d (.reg s) :: is) ss = symRun is (ss.setR d (ss.regs s)) :=
  symRun_cons_of_ok is (symStep_movI_reg ss d s)

theorem symRun_movI_imm_cons (ss : SSt) (d : String) (k : Nat) (is : List LinstrRM) :
    symRun (movI d (.imm k) :: is) ss = symRun is (ss.setR d (.immW 64 k)) :=
  symRun_cons_of_ok is (symStep_movI_imm ss d k)

/-- The symbolic state after the register moves `ms` (target, source), in order. -/
def movesSt (ss : SSt) (ms : List (String × String)) : SSt :=
  ms.foldl (fun s p => s.setR p.1 (s.regs p.2)) ss

/-- **The symbolic run of register moves** followed by `is` is the run of `is` from the
    state after the moves. -/
theorem symRun_regMoves :
    ∀ (ms : List (String × String)) (is : List LinstrRM) (ss : SSt),
      symRun (regMoves ms ++ is) ss = symRun is (movesSt ss ms)
  | [], is, ss => by simp [regMoves, movesSt]
  | p :: ms, is, ss => by
      have ih := symRun_regMoves ms is (ss.setR p.1 (ss.regs p.2))
      simp only [regMoves, List.map_cons, List.cons_append] at ih ⊢
      rw [symRun_movI_reg_cons]
      exact ih

/-- The shift of a carried block is a list of register moves. -/
theorem shiftMoves_eq_regMoves (d nCar : Nat) :
    shiftMoves d nCar = regMoves ((List.range nCar).map fun k =>
      (regName (d + k), regName (d + 1 + k))) := by
  simp [shiftMoves, regMoves]

/-- **The symbolic run of the shift of a carried block.** -/
theorem symRun_shiftMoves (d nCar : Nat) (is : List LinstrRM) (ss : SSt) :
    symRun (shiftMoves d nCar ++ is) ss =
      symRun is (movesSt ss ((List.range nCar).map fun k =>
        (regName (d + k), regName (d + 1 + k)))) := by
  rw [shiftMoves_eq_regMoves, symRun_regMoves]

/-! ## 3. Facts through the moves -/

/-- The registers a fact mentions. -/
def IdxFact.regs : IdxFact → List String
  | .le rs _ => rs
  | .ge r _ => [r]
  | .ale _ _ => []
  | .w64 r => [r]

/-- **A fact that does not mention the written register** is read unchanged through the
    state after the write. -/
theorem IdxFact.toS_setR_of_not_mem (ss : SSt) (d : String) (t : STerm) {f : IdxFact}
    (hd : d ∉ f.regs) :
    f.toS (ss.setR d t).regs (ss.setR d t).arrs = f.toS ss.regs ss.arrs := by
  have ea : (ss.setR d t).arrs = ss.arrs := rfl
  cases f with
  | le rs b =>
      simp only [IdxFact.regs] at hd
      simp only [IdxFact.toS, SFact.le.injEq, and_true]
      refine List.map_congr_left fun r hr => ?_
      have hr' : r ≠ d := by rintro rfl; exact hd hr
      simp [SSt.setR_regs, hr']
  | ge r k =>
      simp only [IdxFact.regs, List.mem_singleton] at hd
      simp [IdxFact.toS, SSt.setR_regs, Ne.symm hd]
  | ale a b => simp only [IdxFact.toS, ea]
  | w64 r =>
      simp only [IdxFact.regs, List.mem_singleton] at hd
      simp [IdxFact.toS, SSt.setR_regs, Ne.symm hd]

/-- **The successor check through a write of an unmentioned register** is unchanged. -/
theorem succOk_setR_of_not_mem (F : List SFact) (ss : SSt) (d : String) (t : STerm)
    {fs : List IdxFact} (hd : ∀ f ∈ fs, d ∉ f.regs) :
    succOk F (ss.setR d t) fs = succOk F ss fs := by
  simp only [succOk]
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp only [List.all_cons]
      rw [IdxFact.toS_setR_of_not_mem ss d t (hd f List.mem_cons_self),
        ih fun g hg => hd g (List.mem_cons_of_mem _ hg)]

/-- The renaming of a fact through the register moves `ms`: the fact read after the moves is
    the renamed fact read before them. -/
def IdxFact.renameAll (ms : List (String × String)) (f : IdxFact) : IdxFact :=
  ms.foldr (fun p g => g.rename p.1 p.2) f

/-- **The successor check through register moves**: the facts of a successor follow through
    the state after the moves exactly when their renamings follow through the state before
    them. -/
theorem succOk_foldl_setR (F : List SFact) :
    ∀ (ms : List (String × String)) (ss : SSt) (fs : List IdxFact),
      succOk F (movesSt ss ms) fs = succOk F ss (fs.map (IdxFact.renameAll ms))
  | [], ss, fs => by
      have e : IdxFact.renameAll [] = id := rfl
      simp [movesSt, e]
  | p :: ms, ss, fs => by
      have ih := succOk_foldl_setR F ms (ss.setR p.1 (ss.regs p.2)) fs
      simp only [movesSt, List.foldl_cons] at ih ⊢
      rw [ih, succOk_setR, List.map_map]
      rfl

/-- **The successor check after a block ending in register moves**: when the symbolic run of
    the block is the run of `is` followed by the moves `ms`, its successor facts are checked
    as their renamings at the state after `is`. -/
theorem succOk_regMoves (F : List SFact) {is : List LinstrRM} {ms : List (String × String)}
    {ss ss' : SSt} {gs : List SG} (hr : symRun is ss = .ok ss' gs) (fs : List IdxFact) :
    symRun (is ++ regMoves ms) ss = .ok (movesSt ss' ms) gs ∧
      succOk F (movesSt ss' ms) fs = succOk F ss' (fs.map (IdxFact.renameAll ms)) := by
  refine ⟨?_, succOk_foldl_setR F ms ss' fs⟩
  have happ : ∀ (xs : List LinstrRM) (s : SSt) (s1 : SSt) (g1 : List SG),
      symRun xs s = .ok s1 g1 →
        symRun (xs ++ regMoves ms) s = .ok (movesSt s1 ms) g1 := by
    intro xs
    induction xs with
    | nil =>
        intro s s1 g1 h
        simp only [symRun, SOut.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [symRun] using symRun_regMoves ms [] s
    | cons i xs ih =>
        intro s s1 g1 h
        simp only [List.cons_append, symRun] at h ⊢
        cases h2 : symStep i s with
        | ok s2 g2 =>
            cases h3 : symRun xs s2 with
            | ok s3 g3 =>
                simp only [h2, h3, SOut.ok.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [ih s2 s3 g3 h3]
            | fail => simp [h2, h3] at h
            | unk => simp [h2, h3] at h
        | fail => simp [h2] at h
        | unk => simp [h2] at h
  exact happ is ss ss' gs hr

/-- **A fact of the block is entailed by the facts of the block**, read at the block entry. -/
theorem entails_startF_mem {fs : List IdxFact} {f : IdxFact} (hf : f ∈ fs) :
    entails (startF fs) (f.toS STerm.reg SArr.cell) = true := by
  have hm : f.toS STerm.reg SArr.cell ∈ startF fs := List.mem_map.mpr ⟨f, hf, rfl⟩
  cases f with
  | le rs b =>
      exact entails_le_of_mem hm fun t ht => by
        obtain ⟨r, -, rfl⟩ := List.mem_map.mp ht
        exact reg_mem_linAlts _ r
  | ge r k => exact entails_ge_of_mem hm
  | ale a b => exact entails_ale_of_mem hm
  | w64 r => exact entails_w64_of_mem hm rfl

/-- **The facts a block leaves in place pass to its successor**: when every fact of `fs` is a
    fact of the block (`fs ⊆ fb`) and the final symbolic state `ss` reads it as at the block
    entry, the successor check of `fs` at `ss` accepts from the facts of the block and any
    further facts `E` (the facts of an edge). -/
theorem succOk_of_keep {fb fs : List IdxFact} (E : List SFact) {ss : SSt}
    (hsub : ∀ f ∈ fs, f ∈ fb)
    (hk : ∀ f ∈ fs, f.toS ss.regs ss.arrs = f.toS STerm.reg SArr.cell) :
    succOk (startF fb ++ E) ss fs = true := by
  simp only [succOk, List.all_eq_true]
  intro f hf
  rw [hk f hf]
  exact entails_mono (fun g hg => List.mem_append_left _ hg) _
    (entails_startF_mem (hsub f hf))

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
