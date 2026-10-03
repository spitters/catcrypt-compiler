/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# The loop namespace: index, counter and body temporaries are distinct names

The physical loop export keys three families of register names on the loop depth
`d`: the index `loopIdx d = "Lidx" ++ toString d`, the trip counter
`loopCtr d = "Lctr" ++ toString d`, and the body temporaries
`loopReg d k = "L" ++ toString d ++ "_r" ++ toString k`. The renaming side
conditions of the export simulations ask for these to be pairwise distinct.

The index and the counter differ in their second character. A temporary differs
from both by the same character position: after the shared `'L'` a temporary
continues with the first digit of `toString d`, and `Nat.toDigits 10` produces a
`Nat.digitChar` of a value below ten, which is neither `'i'` nor `'c'`.

The chain registers `regName k = "r" ++ toString k`, which also name the carried
registers of the carried-register loops (`ComLJ`), start with `'r'` and so differ from
all three loop families in their first character.

## Main results

* `loopIdx_ne_loopCtr`, `loopIdx_ne_loopReg`, `loopCtr_ne_loopReg` — the loop families
  are pairwise distinct.
* `regName_ne_loopIdx`, `regName_ne_loopCtr`, `regName_ne_loopReg` — a chain register is
  none of them.
-/

public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The decimal digits of a natural number start with the digit character of a
    value below ten. -/
theorem toDigits_ten_eq_cons (n : Nat) :
    ∃ m cs, m < 10 ∧ Nat.toDigits 10 n = Nat.digitChar m :: cs := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 10 with hn | hn
    · exact ⟨n, [], hn, by rw [Nat.toDigits_of_lt_base hn]⟩
    · obtain ⟨m, cs, hm, hcs⟩ := ih (n / 10) (Nat.div_lt_self (by omega) (by omega))
      refine ⟨m, cs ++ [Nat.digitChar (n % 10)], hm, ?_⟩
      rw [Nat.toDigits_of_base_le (by omega) hn, hcs, List.cons_append]

/-- A digit character of a value below ten is a decimal digit, so it is none of
    the letters the loop-name prefixes use. -/
theorem digitChar_ne_of_lt_ten {m : Nat} (hm : m < 10) (c : Char)
    (hc : ∀ k, k < 10 → Nat.digitChar k ≠ c) : Nat.digitChar m ≠ c :=
  hc m hm

/-- The character list of `toString n` starts with a decimal digit character. -/
theorem toString_toList_eq_cons (n : Nat) :
    ∃ m cs, m < 10 ∧ (toString n).toList = Nat.digitChar m :: cs := by
  obtain ⟨m, cs, hm, hcs⟩ := toDigits_ten_eq_cons n
  refine ⟨m, cs, hm, ?_⟩
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList, hcs]

/-- The loop index and the trip counter of a depth are distinct names: they
    differ in their second character. -/
theorem loopIdx_ne_loopCtr (d : Nat) : loopIdx d ≠ loopCtr d := by
  intro h
  have hd := congrArg String.toList h
  simp only [loopIdx, loopCtr, String.toList_append] at hd
  simp at hd

/-- A loop body temporary is not the loop index: after the shared `'L'` the
    temporary continues with a digit and the index with `'i'`. -/
theorem loopIdx_ne_loopReg (d d' k : Nat) : loopIdx d ≠ loopReg d' k := by
  intro h
  have hd := congrArg String.toList h
  obtain ⟨m, cs, hm, hcs⟩ := toString_toList_eq_cons d'
  simp only [loopIdx, loopReg, String.toList_append, hcs, List.cons_append,
    List.append_assoc] at hd
  interval_cases m <;> simp [Nat.digitChar] at hd

/-- A loop body temporary is not the trip counter: after the shared `'L'` the
    temporary continues with a digit and the counter with `'c'`. -/
theorem loopCtr_ne_loopReg (d d' k : Nat) : loopCtr d ≠ loopReg d' k := by
  intro h
  have hd := congrArg String.toList h
  obtain ⟨m, cs, hm, hcs⟩ := toString_toList_eq_cons d'
  simp only [loopCtr, loopReg, String.toList_append, hcs, List.cons_append,
    List.append_assoc] at hd
  interval_cases m <;> simp [Nat.digitChar] at hd

/-- A chain register is not a loop index: the first is `'r'`, the second `'L'`. -/
theorem regName_ne_loopIdx (k d : Nat) : regName k ≠ loopIdx d := by
  intro h
  have hd := congrArg String.toList h
  simp [regName, loopIdx, String.toList_append] at hd

/-- A chain register is not a trip counter: the first is `'r'`, the second `'L'`. -/
theorem regName_ne_loopCtr (k d : Nat) : regName k ≠ loopCtr d := by
  intro h
  have hd := congrArg String.toList h
  simp [regName, loopCtr, String.toList_append] at hd

/-- A chain register is not a loop body temporary: the first is `'r'`, the second
    `'L'`. -/
theorem regName_ne_loopReg (k d j : Nat) : regName k ≠ loopReg d j := by
  intro h
  have hd := congrArg String.toList h
  simp [regName, loopReg, String.toList_append] at hd

end CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
