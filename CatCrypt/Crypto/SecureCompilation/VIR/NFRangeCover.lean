/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFRangeLoop

/-!
# The interval checker on a subdivided input range

`checkCover S p n As` runs the interval checker `check S` on each abstract environment of the
list `As`; an environment the checker refuses is bisected at its widest word interval
(`AEnv.bisect`) and both halves are checked in its place, within a budget of `n` checks in all.
An environment that holds of a valuation has a half that holds of it (`AEnv.sat_bisect`), so
acceptance gives a value of the program at every valuation that one environment of `As` holds
of (`checkCover_sound`).

## Main results

* `AEnv.bisect`, `checkCover`: the bisection and the checker on a subdivided range.
* `AEnv.sat_bisect`: a valuation in an environment is in one of its halves.
* `checkCover_sound`: the soundness of `checkCover`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFRange

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-! ## Bisection -/

/-- The width `hi - lo` of the interval of a word; `0` at every other type. -/
def AVal.width : (t : NfTy) → AVal t → Int
  | .word _, a => a.2 - a.1
  | _, _ => 0

/-- The two halves of the interval of a word of width `m > 0`, split at its midpoint. -/
def AVal.bisect (m : Int) : (t : NfTy) → AVal t → Option (AVal t × AVal t)
  | .word _, a =>
    if 0 < m ∧ a.2 - a.1 = m then
      some (((a.1, (a.1 + a.2) / 2) : Iv), (((a.1 + a.2) / 2 + 1, a.2) : Iv))
    else none
  | _, _ => none

namespace AVals

/-- The greatest width of the word intervals of a list of abstract values. -/
def maxWidth : {ts : List NfTy} → AVals ts → Int
  | [], .nil => 0
  | t :: _, .cons a as => max (AVal.width t a) (maxWidth as)

/-- The two lists with the first word interval of width `m` replaced by each of its halves. -/
def bisect (m : Int) : {ts : List NfTy} → AVals ts → Option (AVals ts × AVals ts)
  | [], .nil => none
  | t :: _, .cons a as =>
    match AVal.bisect m t a with
    | some (a₁, a₂) => some (.cons a₁ as, .cons a₂ as)
    | none => (bisect m as).map fun B => (.cons a B.1, .cons a B.2)

end AVals

/-- The two halves of an abstract environment at its widest word interval. -/
def AEnv.bisect {Γ : Ctxt nfDialect} (A : AEnv Γ) : Option (AEnv Γ × AEnv Γ) :=
  AVals.bisect (AVals.maxWidth A) A

/-- **The checker on a subdivided range**: each environment of the list is accepted by
    `check S`, or is bisected and both halves are accepted in its place, within `n` checks. -/
def checkCover (S : NameSpec) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Nat → List (AEnv Γ) → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, A :: As =>
    if (check S A p).isSome then checkCover S p n As
    else match A.bisect with
      | some (A₁, A₂) => checkCover S p n (A₁ :: A₂ :: As)
      | none => false

/-! ## Soundness -/

/-- A value in the abstract value `a` is in one of its halves. -/
theorem AVal.mem_bisect {m : Int} :
    ∀ (t : NfTy) {a a₁ a₂ : AVal t} (x : t.denote), AVal.bisect m t a = some (a₁, a₂) →
      AVal.Mem t a x → AVal.Mem t a₁ x ∨ AVal.Mem t a₂ x
  | .word _, a, a₁, a₂, x, h, hx => by
    simp only [AVal.bisect] at h
    split_ifs at h
    cases h
    simp only [AVal.Mem, Iv.Has] at hx ⊢
    omega
  | .bit, _, _, _, _, h, _ | .arr _ _, _, _, _, _, h, _ | .unit, _, _, _, _, h, _
  | .pair _ _, _, _, _, _, h, _ | .uint _, _, _, _, _, h, _ | .sint _, _, _, _, _, h, _
  | .int, _, _, _, _, h, _ | .tnil, _, _, _, _, h, _ | .tcons _ _, _, _, _, _, h, _
  | .slice _, _, _, _, _, h, _ => by simp [AVal.bisect] at h

/-- The halves of an abstract value are no bits. -/
theorem AVal.bitArg_bisect {m : Int} :
    ∀ (t : NfTy) {a a₁ a₂ : AVal t}, AVal.bisect m t a = some (a₁, a₂) →
      bitArg t a₁ = bitArg t a ∧ bitArg t a₂ = bitArg t a
  | .word _, _, _, _, _ => ⟨rfl, rfl⟩
  | .bit, _, _, _, h | .arr _ _, _, _, _, h | .unit, _, _, _, h | .pair _ _, _, _, _, h
  | .uint _, _, _, _, h | .sint _, _, _, _, h | .int, _, _, _, h | .tnil, _, _, _, h
  | .tcons _ _, _, _, _, h | .slice _, _, _, _, h => by simp [AVal.bisect] at h

/-- The halves of a list of abstract values have its bits. -/
theorem AVals.bitAt_bisect {m : Int} :
    ∀ {Γ : Ctxt nfDialect} {A B₁ B₂ : AEnv Γ}, AVals.bisect m A = some (B₁, B₂) →
      ∀ n, B₁.bitAt n = A.bitAt n ∧ B₂.bitAt n = A.bitAt n
  | [], .nil, _, _, h, _ => by simp [AVals.bisect] at h
  | t :: _, .cons a as, B₁, B₂, h, n => by
    simp only [AVals.bisect] at h
    split at h
    · rename_i a₁ a₂ ha
      cases h
      cases n with
      | zero => exact AVal.bitArg_bisect t ha
      | succ n => exact ⟨rfl, rfl⟩
    · obtain ⟨⟨C₁, C₂⟩, hC, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      cases n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n => exact AVals.bitAt_bisect hC n

/-- A valuation in a list of abstract values is in one of its halves. -/
theorem AVals.mem_bisect {m : Int} :
    ∀ {ts : List NfTy} {A B₁ B₂ : AVals ts} (V : HVector NfTy.denote ts),
      AVals.bisect m A = some (B₁, B₂) → AVals.Mem A V → AVals.Mem B₁ V ∨ AVals.Mem B₂ V
  | [], .nil, _, _, _, h, _ => by simp [AVals.bisect] at h
  | t :: _, .cons a as, B₁, B₂, .cons x V, h, hV => by
    simp only [AVals.bisect] at h
    obtain ⟨hx, hV⟩ := hV
    split at h
    · rename_i a₁ a₂ ha
      cases h
      rcases AVal.mem_bisect t x ha hx with h1 | h1
      · exact .inl ⟨h1, hV⟩
      · exact .inr ⟨h1, hV⟩
    · obtain ⟨⟨C₁, C₂⟩, hC, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      rcases AVals.mem_bisect V hC hV with h1 | h1
      · exact .inl ⟨hx, h1⟩
      · exact .inr ⟨hx, h1⟩

/-- **A valuation in an environment is in one of its halves.** -/
theorem AEnv.sat_bisect {Γ : Ctxt nfDialect} {A A₁ A₂ : AEnv Γ} {V : Valuation Γ}
    (h : A.bisect = some (A₁, A₂)) (hV : A.Sat V) : A₁.Sat V ∨ A₂.Sat V := by
  obtain ⟨hm, hf⟩ := hV
  have hb := AVals.bitAt_bisect h
  rcases AVals.mem_bisect V h hm with h1 | h1
  · exact .inl ⟨h1, fun n a b ha => hf n a b ((hb n).1 ▸ ha)⟩
  · exact .inr ⟨h1, fun n a b ha => hf n a b ((hb n).2 ▸ ha)⟩

/-- **Soundness of the checker on a subdivided range.** When the name specification `S` is
    sound for the leaf table `T` and `checkCover` accepts `p` on the list `As`, the program
    denotes, from every valuation that one environment of `As` holds of, at every fuel, results
    `W`. -/
theorem checkCover_sound {S : NameSpec} {T : NfLeafTable} (hS : S.SoundAt T)
    {Γ : Ctxt nfDialect} {ts : List NfTy} {p : NFProg nfDialect Γ ts} {V : Valuation Γ} :
    ∀ (n : Nat) (As : List (AEnv Γ)), checkCover S p n As = true → ∀ A ∈ As, A.Sat V →
      ∃ W : Valuation (d := nfDialect) ts,
        ∀ fuel, @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts p V = some W
  | _, [], _, _, hA, _ => by simp at hA
  | 0, _ :: _, h, _, _, _ => by simp [checkCover] at h
  | n + 1, B :: As, h, A, hA, hV => by
    simp only [checkCover] at h
    split_ifs at h with hc
    · rcases List.mem_cons.1 hA with rfl | hA
      · obtain ⟨W, hW, -⟩ := check_sound' hS (Option.some_get hc).symm hV
        exact ⟨W, hW⟩
      · exact checkCover_sound hS n As h A hA hV
    · split at h
      · rename_i B₁ B₂ hB
        rcases List.mem_cons.1 hA with rfl | hA
        · rcases AEnv.sat_bisect hB hV with h1 | h1
          · exact checkCover_sound hS n _ h B₁ (by simp) h1
          · exact checkCover_sound hS n _ h B₂ (by simp) h1
        · exact checkCover_sound hS n _ h A (by simp [hA]) hV
      · simp at h

end CatCrypt.Crypto.SecureCompilation.VIR.NFRange
