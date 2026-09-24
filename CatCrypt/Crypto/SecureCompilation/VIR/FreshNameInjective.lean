/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-!
# `freshName` is injective — discharging the carried hypothesis

`JasminPrintSemCorrect.lean` (§"Why `freshName` injectivity is carried as a
hypothesis") carries `hInj : Function.Injective freshName` as an explicit
side-condition on its whole-`Com` preservation theorem `execCom_eq`, because on
the **old** toolchain no `Nat.repr` / `toString` injectivity lemma — and no
`Nat.toDigits` roundtrip lemma — existed.

The **4.29.1** toolchain still ships no `toDigits` left-inverse / `ofDigitChars`
roundtrip lemma (the `Nat.ofDigitChars_*` family loogle reports is from a *newer*
core than the installed one). But it does ship the digit *recursion* lemmas in
`Init.Data.Nat.ToString`:

* `Nat.toString_eq_ofList_toDigits : toString n = String.ofList (Nat.toDigits 10 n)`
* `Nat.toDigits_eq_if`, `Nat.toDigits_of_lt_base`, `Nat.toDigits_of_base_le`,
  `Nat.length_toDigits_pos`

plus `String.ofList_injective`. So we prove `Nat.toDigits 10` injective *directly*
by strong induction on the base-10 recursion (`Nat.toDigits_eq_if`): the last
digit determines `n % 10`, the prefix determines `n / 10` by the IH, and
`n = 10 * (n / 10) + n % 10`. Then `toString` is injective
(`String.ofList ∘ Nat.toDigits 10`), and prefixing the constant `"v"` is
left-cancellable, so `freshName n = "v" ++ toString n` is injective.

This file proves `freshName_injective` cleanly (no `sorry`, no new axioms). Any
caller of `execCom_eq` (in particular the multi-op loop theorem of
`JForProgMultiOp.lean`) discharges the carried `hInj` with this lemma, removing
the last side-condition from the straight-line whole-`Com` preservation path.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-! ## 1. `Nat.digitChar` is injective on `{0, …, 9}`

For `a, b < 10`, `digitChar a = digitChar b` forces `a = b` — decidable on the
ten explicit cases. -/

/-- `Nat.digitChar` is injective on the decimal digits `{0, …, 9}`. -/
theorem digitChar_injOn_lt_ten {a b : Nat} (ha : a < 10) (hb : b < 10)
    (h : Nat.digitChar a = Nat.digitChar b) : a = b := by
  interval_cases a <;> interval_cases b <;> simp_all [Nat.digitChar]

/-! ## 2. `Nat.toDigits 10` is injective

By strong induction on `n`. `Nat.toDigits_eq_if` exposes the base-10 recursion:
for `n < 10` the digit list is `[digitChar n]`; for `n ≥ 10` it is
`toDigits 10 (n / 10) ++ [digitChar (n % 10)]`. Two equal digit lists therefore
have equal last digit (⇒ equal `% 10`) and equal prefix (⇒ equal `/ 10` by the
IH), so the numbers agree by `n = 10 * (n / 10) + n % 10`. The mixed
length-1-vs-length-≥2 cases are impossible by `length_toDigits_pos`. -/

/-- `Nat.toDigits 10` is injective: distinct naturals have distinct decimal digit
    lists. Proved directly from the base-10 recursion (no `ofDigitChars`
    roundtrip lemma is needed / available in this toolchain). -/
theorem toDigits_ten_injective : Function.Injective (Nat.toDigits 10) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b hab
    rcases Nat.lt_or_ge a 10 with ha | ha <;> rcases Nat.lt_or_ge b 10 with hb | hb
    · -- both `< 10`: `[digitChar a] = [digitChar b]`.
      rw [Nat.toDigits_of_lt_base ha, Nat.toDigits_of_lt_base hb] at hab
      have : Nat.digitChar a = Nat.digitChar b := by
        simpa using hab
      exact digitChar_injOn_lt_ten ha hb this
    · -- `a < 10 ≤ b`: lengths `1` vs `≥ 2`, impossible.
      rw [Nat.toDigits_of_lt_base ha, Nat.toDigits_of_base_le (by omega) hb] at hab
      have hlen := congrArg List.length hab
      simp only [List.length_singleton, List.length_append] at hlen
      have := @Nat.length_toDigits_pos 10 (b / 10)
      omega
    · -- `b < 10 ≤ a`: symmetric, impossible.
      rw [Nat.toDigits_of_lt_base hb, Nat.toDigits_of_base_le (by omega) ha] at hab
      have hlen := congrArg List.length hab
      simp only [List.length_singleton, List.length_append] at hlen
      have := @Nat.length_toDigits_pos 10 (a / 10)
      omega
    · -- both `≥ 10`: append form; split the single trailing digit.
      rw [Nat.toDigits_of_base_le (by omega) ha, Nat.toDigits_of_base_le (by omega) hb] at hab
      rw [List.append_singleton_inj] at hab
      obtain ⟨hpre, hlast⟩ := hab
      -- prefix ⇒ `a / 10 = b / 10` (IH); last digit ⇒ `a % 10 = b % 10`.
      have hdiv : a / 10 = b / 10 := ih (a / 10) (Nat.div_lt_self (by omega) (by omega)) hpre
      have hmod : a % 10 = b % 10 :=
        digitChar_injOn_lt_ten (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hlast
      calc a = 10 * (a / 10) + a % 10 := by rw [Nat.div_add_mod]
        _ = 10 * (b / 10) + b % 10 := by rw [hdiv, hmod]
        _ = b := by rw [Nat.div_add_mod]

/-! ## 3. `toString : Nat → String` is injective

`toString n = String.ofList (Nat.toDigits 10 n)` (`Nat.toString_eq_ofList_toDigits`),
and `String.ofList` is injective (`String.ofList_injective`), so `toString` is
the composite of two injective maps. -/

/-- `toString : Nat → String` is injective: it is `String.ofList ∘ Nat.toDigits 10`,
    a composite of two injective maps. -/
theorem natToString_injective :
    Function.Injective (fun n : Nat => toString n) := by
  intro a b hab
  simp only [Nat.toString_eq_ofList_toDigits] at hab
  exact toDigits_ten_injective (String.ofList_injective hab)

/-! ## 4. `freshName` is injective

`freshName n = "v" ++ toString n`. Prefixing with the constant `"v"` is
left-cancellable (working through `String.toList`/`List.append_cancel_left`), so
`freshName` is injective. -/

/-- **`freshName` is injective.** Distinct fresh-SSA counters give distinct
    SSA names. This discharges the `hInj : Function.Injective freshName`
    hypothesis carried by `JasminPrintSemCorrect.execCom_eq`. -/
theorem freshName_injective : Function.Injective freshName := by
  intro a b hab
  unfold freshName at hab
  -- Strip the constant prefix `"v"` via the `String.toList`/`List` representation.
  apply natToString_injective
  have hd := congrArg String.toList hab
  simp only [String.toList_append] at hd
  exact String.toList_injective (List.append_cancel_left hd)

end CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective
