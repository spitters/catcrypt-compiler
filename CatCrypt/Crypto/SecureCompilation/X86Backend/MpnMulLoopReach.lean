/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics

@[expose] public section

set_option autoImplicit false

/-!
# Counted loops of a decoded program, by an invariant

`RInstrSemantics.reaches_xloop` runs a loop whose body is a straight segment. A loop whose
body contains another loop (the nested `mpn_mul_basecase` loop) is run here by an invariant:
if every trip from the loop head reaches the back-edge branch `jne head` with the zero flag
set exactly at the last trip, the loop reaches the index after the branch.

## Main results

* `step_jne`, `step_je`: one step at a `jne` / `je` branch.
* `reaches_doWhile`: the trips of a do-while loop compose to a run past its back edge.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulLoopReach

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)

variable {σ : Type}

/-- A `jne t` step: to `t` while the zero flag is clear, past the branch when it is set. -/
theorem step_jne (M : Machine σ) (prog : List RInstr) (j t : Nat) (s : σ)
    (hj : prog[j]? = some (.jcc 5 t)) :
    RInstrSemantics.step M prog j s
      = some (if (M.view s).flagB (·.zf) then Next.go (j + 1) s else Next.go t s) := by
  simp only [RInstrSemantics.step, hj, condtOfNibble_five, Option.map_some, condB_ne]
  by_cases h : (M.view s).flagB (·.zf) = true <;> simp [h]

/-- A `je t` step: to `t` when the zero flag is set, past the branch otherwise. -/
theorem step_je (M : Machine σ) (prog : List RInstr) (j t : Nat) (s : σ)
    (hj : prog[j]? = some (.jcc 4 t)) :
    RInstrSemantics.step M prog j s
      = some (if (M.view s).flagB (·.zf) then Next.go t s else Next.go (j + 1) s) := by
  simp only [RInstrSemantics.step, hj, condtOfNibble_four, Option.map_some, condB_e]
  by_cases h : (M.view s).flagB (·.zf) = true <;> simp [h]

/-- **A do-while loop by its invariant.** The loop occupies the indices from `h` to the
    back edge `jne h` at `j`. If every trip `k < m` from a state satisfying `Inv k` reaches
    `j` in a state satisfying `Inv (k + 1)` whose zero flag is set exactly when `k + 1 = m`,
    then from `Inv k` the machine reaches `j + 1` in a state satisfying `Inv m`. -/
theorem reaches_doWhile (M : Machine σ) (prog : List RInstr) (h j : Nat)
    (hj : prog[j]? = some (.jcc 5 h)) (Inv : Nat → σ → Prop) (m : Nat)
    (hbody : ∀ k s, k < m → Inv k s → ∃ s', Reaches M prog h s j s' ∧
        (M.view s').flagB (·.zf) = decide (k + 1 = m) ∧ Inv (k + 1) s') :
    ∀ k s, k < m → Inv k s → ∃ s', Reaches M prog h s (j + 1) s' ∧ Inv m s' := by
  intro k
  induction hk : m - k generalizing k with
  | zero => intro s hlt; omega
  | succ d ih =>
    intro s hlt hI
    obtain ⟨s', hr, hz, hI'⟩ := hbody k s hlt hI
    by_cases hlast : k + 1 = m
    · refine ⟨s', hr.trans (.single ?_), hlast ▸ hI'⟩
      rw [step_jne M prog j h s' hj, hz, decide_eq_true hlast]; rfl
    · obtain ⟨s'', hr', hI''⟩ := ih (k + 1) (by omega) s' (by omega) hI'
      refine ⟨s'', hr.trans (.next ?_ hr'), hI''⟩
      rw [step_jne M prog j h s' hj, hz, decide_eq_false hlast]; rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulLoopReach
