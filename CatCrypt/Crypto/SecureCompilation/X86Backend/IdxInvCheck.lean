/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

@[expose] public section

set_option autoImplicit false

/-!
# A checked bounds invariant for runs of `lsemFuelMemF`

The checker `ownedCheckMC` relates bounds-checked runs (`lsemFuelMemFk true`); a halting run
of `lsemFuelMemF` is one exactly when every state it steps from is in bounds at the
instruction it fetches (`RunIdxOk`). This module decides `RunIdxOk` of the halting runs of a
body from an entry state satisfying a list of facts.

A fact (`IdxFact`) bounds the sum of the `64`-bit values of a list of registers from above
or the value of one register from below. An annotation assigns a list of facts to each
block of the control-flow graph `cfgOf`; it is untrusted. `idxInvCheckB` checks, for every
block, along its symbolic run `symRun` from the block entry:

* every index obligation `symObl` of the block (an index term with the length of its array)
  follows from the facts of the block;
* the facts of every successor block, read through the final symbolic registers, follow
  from the facts of the block and from the condition of the edge (`edgeFacts`: a branch on
  the zero flag of a comparison with `0`, or on a register being non-zero);
* the entry facts give the facts of block `0`.

Entailment (`entails`) is syntactic: an upper bound on a sum is read off one fact after
normalising additions and subtractions of immediates (`linOf`), with the lower bounds of the
remaining summands; a lower bound is read off a fact on the same term. A sum whose linear
form is one product with an immediate at width `64` plus a constant is bounded through a
bound on the other factor (`mulLe`); with the immediate as the first factor the other factor
must have width `64`, which a width fact states. The index obligations of a block are
checked from its facts and the width facts of the guards of its symbolic run (`guardW64`).

`idxAnnot` computes an annotation by restricting candidate facts to a fixed point; the
bounds of its candidates are those of the entry facts, the array lengths of the index
obligations and the immediates the blocks leave in the candidate registers (`seedImms`).
The check does not depend on it. `boundFacts` reads the facts of a System V layout's register
bounds, which hold at every entry state satisfying `AbiLayout.Regions`.

## Main definitions

* `IdxFact`, `SFact`, `entails`, `linOf`, `edgeFacts`: facts and their entailment.
* `blockInvOk`, `idxInvCheckB`: the check.
* `idxAnnot`: the annotation by restriction to a fixed point.
* `boundFacts`: the facts of a layout's register bounds.

## Main results

* `entails_sound`, `edgeFacts_sound`: entailment and edge facts are sound.
* `runIdxOk_of_idxInvCheckB`: every halting run of `lsemFuelMemF` on an accepted body from
  pc `0` and a state satisfying the entry facts is in bounds.
* `lsemFuelMemFk_of_idxInvCheckB`: such a run is a halting checked run.
* `ownedCheckMC_sound_of_idxInv`: `ownedCheckMC` with an accepted source body relates every
  halting run of `lsemFuelMemF` on the source to a halting checked run of the rewritten
  body.
* `boundFacts_holds`: the facts of a layout's register bounds hold at a separated entry.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

/-! ## 1. Facts -/

/-- The value of a width-tagged word read at width `64`, as a natural number; `0` on a
    width mismatch. -/
def wval (x : Σ w, BitVec w) : Nat := (castW x 64).toNat

theorem wval_lt (x : Σ w, BitVec w) : wval x < 2 ^ 64 := (castW x 64).isLt

theorem castW_ne {x : Σ w, BitVec w} (h : x.1 ≠ 64) : castW x 64 = 0 := by
  simp [castW, h]

/-- A fact over the registers at a block entry: the sum of the values of the registers `rs`
    is at most `b`, or the value of the register `r` is at least `k`. -/
inductive IdxFact where
  | le (rs : List String) (b : Nat)
  | ge (r : String) (k : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A fact over symbolic words: the sum of the values of the terms `ts` is at most `b`, the
    value of the term `t` is at least `k`, or the term `t` has width `64`. -/
inductive SFact where
  | le (ts : List STerm) (b : Nat)
  | ge (t : STerm) (k : Nat)
  | w64 (t : STerm)
  deriving DecidableEq

section Eval

variable (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)

/-- The sum of the values of a list of symbolic words. -/
def tsum (ts : List STerm) : Nat := (ts.map fun t => wval (t.ev V A C O)).sum

/-- A symbolic fact holds, for the start registers `V`, arrays `A` and flags `C`, `O`. -/
def SFact.holds : SFact → Prop
  | .le ts b => tsum V A C O ts ≤ b
  | .ge t k => k ≤ wval (t.ev V A C O)
  | .w64 t => (t.ev V A C O).1 = 64

end Eval

/-- A fact holds at the registers `V`. -/
def IdxFact.holds (V : String → Σ w, BitVec w) : IdxFact → Prop
  | .le rs b => (rs.map fun r => wval (V r)).sum ≤ b
  | .ge r k => k ≤ wval (V r)

/-- A fact read through the symbolic registers `R`. -/
def IdxFact.toS (R : String → STerm) : IdxFact → SFact
  | .le rs b => .le (rs.map R) b
  | .ge r k => .ge (R r) k

theorem IdxFact.toS_holds {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    (R : String → STerm) (f : IdxFact) :
    (f.toS R).holds V A C O ↔ f.holds (fun r => (R r).ev V A C O) := by
  cases f <;> simp [IdxFact.toS, IdxFact.holds, SFact.holds, tsum, Function.comp_def]

theorem tsum_append (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (xs ys : List STerm) : tsum V A C O (xs ++ ys) = tsum V A C O xs + tsum V A C O ys := by
  simp [tsum]

/-! ## 2. Entailment -/

/-- The largest lower bound a list of facts states for the term `t`. -/
def lbOf : List SFact → STerm → Nat
  | [], _ => 0
  | .ge t' k :: F, t => if t' = t then max k (lbOf F t) else lbOf F t
  | .le _ _ :: F, t => lbOf F t
  | .w64 _ :: F, t => lbOf F t

theorem lbOf_le {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} :
    ∀ (F : List SFact) (t : STerm), (∀ f ∈ F, f.holds V A C O) →
      lbOf F t ≤ wval (t.ev V A C O)
  | [], _, _ => Nat.zero_le _
  | .le _ _ :: F, t, h => lbOf_le F t (fun g hg => h g (List.mem_cons_of_mem _ hg))
  | .w64 _ :: F, t, h => lbOf_le F t (fun g hg => h g (List.mem_cons_of_mem _ hg))
  | .ge t' k :: F, t, h => by
      have ih := lbOf_le F t (fun g hg => h g (List.mem_cons_of_mem _ hg))
      simp only [lbOf]
      split
      · rename_i he
        subst he
        exact max_le (h (.ge t' k) List.mem_cons_self) ih
      · exact ih

/-- The sum of the lower bounds of a list of terms. -/
def lbSum (F : List SFact) (ts : List STerm) : Nat := (ts.map (lbOf F)).sum

theorem lbSum_le {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ ts : List STerm, lbSum F ts ≤ tsum V A C O ts
  | [] => by simp [lbSum, tsum]
  | t :: ts => by
      have := lbSum_le hF ts
      have := lbOf_le F t hF
      simp only [lbSum, tsum, List.map_cons, List.sum_cons] at *
      omega

/-- **The linear form of a term**: atoms and a constant whose sum bounds the value of the
    term from above. An immediate at width `64` is a constant; an addition of an immediate
    adds it; a subtraction of an immediate below the lower bound of its source subtracts
    it; a conjunction `AND x y` and a disjunction `OR x x` take the form of `x`, which
    bounds them; every other term is an atom. -/
def linOf (F : List SFact) : STerm → List STerm × Int
  | .immW w n => if w = 64 then ([], ((n % 2 ^ 64 : Nat) : Int)) else ([.immW w n], 0)
  | .bin m x (.immW w k) =>
      if w = 64 ∧ m = "ADD" then ((linOf F x).1, (linOf F x).2 + k)
      else if w = 64 ∧ m = "SUB" ∧ k ≤ lbOf F x then ((linOf F x).1, (linOf F x).2 - k)
      else if m = "AND" then linOf F x
      else ([.bin m x (.immW w k)], 0)
  | .bin m x y => if m = "AND" ∨ (m = "OR" ∧ x = y) then linOf F x else ([.bin m x y], 0)
  | t => ([t], 0)

theorem wval_bin (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (m : String) (x y : STerm) :
    wval ((STerm.bin m x y).ev V A C O) =
      if (x.ev V A C O).1 = 64 then
        (binW 64 m (castW (x.ev V A C O) 64) (extW (y.ev V A C O) 64)).toNat
      else 0 := by
  simp only [STerm.ev, wval]
  generalize x.ev V A C O = p
  obtain ⟨w, a⟩ := p
  by_cases hw : w = 64
  · subst hw
    simp [castW]
  · simp [castW, hw]

theorem wval_add_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (x : STerm) (k : Nat) :
    wval ((STerm.bin "ADD" x (.immW 64 k)).ev V A C O) ≤ wval (x.ev V A C O) + k := by
  rw [wval_bin]
  split
  · simp only [binW, STerm.ev, extW, BitVec.setWidth_eq]
    simp only [show ("ADD" = "MULXHI") = False by decide, if_false, applyOpnN,
      Option.getD_some, BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold wval
    have := Nat.mod_le (k) (2 ^ 64)
    have := Nat.mod_le ((castW (x.ev V A C O) 64).toNat + k % 2 ^ 64) (2 ^ 64)
    omega
  · omega

theorem wval_sub_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (x : STerm) (k : Nat) (hk : k ≤ wval (x.ev V A C O)) :
    wval ((STerm.bin "SUB" x (.immW 64 k)).ev V A C O) + k ≤ wval (x.ev V A C O) := by
  rw [wval_bin]
  have hlt := wval_lt (x.ev V A C O)
  split
  · simp only [binW, STerm.ev, extW, BitVec.setWidth_eq]
    simp only [show ("SUB" = "MULXHI") = False by decide, if_false, applyOpnN,
      Option.getD_some]
    unfold wval at hk hlt ⊢
    have hkn : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hkn]; exact hk), hkn]
    omega
  · omega

/-- A conjunction `AND x y` and a disjunction `OR x x` are at most `x`. -/
theorem wval_andOr_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    {m : String} {x y : STerm} (h : m = "AND" ∨ (m = "OR" ∧ x = y)) :
    wval ((STerm.bin m x y).ev V A C O) ≤ wval (x.ev V A C O) := by
  rw [wval_bin]
  split
  · rename_i hw
    unfold wval
    rcases h with rfl | ⟨rfl, rfl⟩
    · simp only [binW, show ("AND" = "MULXHI") = False by decide, if_false, applyOpnN,
        Option.getD_some, BitVec.toNat_and]
      exact Nat.and_le_left
    · simp only [binW, show ("OR" = "MULXHI") = False by decide, if_false, applyOpnN,
        Option.getD_some, extW_of_eq hw, BitVec.or_self, le_refl]
  · exact Nat.zero_le _

theorem linOf_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    (wval (t.ev V A C O) : Int) ≤ (tsum V A C O (linOf F t).1 : Int) + (linOf F t).2 := by
  fun_induction linOf F t with
  | case1 n => simp [tsum, wval, STerm.ev, castW]
  | case2 => simp [tsum]
  | case3 m x w k h ih =>
      obtain ⟨rfl, rfl⟩ := h
      have := wval_add_le V A C O x k
      dsimp only
      omega
  | case4 m x w k _ h ih =>
      obtain ⟨rfl, rfl, hk⟩ := h
      have := wval_sub_le V A C O x k (le_trans hk (lbOf_le F x hF))
      dsimp only
      omega
  | case5 x w k _ _ ih =>
      have := wval_andOr_le V A C O (x := x) (y := .immW w k) (Or.inl rfl)
      omega
  | case6 => simp [tsum]
  | case7 m x y _ h ih =>
      have := wval_andOr_le V A C O h
      omega
  | case8 => simp [tsum]
  | case9 => simp [tsum]

/-- The linear form of a sum of terms. -/
def sumLin (F : List SFact) : List STerm → List STerm × Int
  | [] => ([], 0)
  | t :: ts => ((linOf F t).1 ++ (sumLin F ts).1, (linOf F t).2 + (sumLin F ts).2)

theorem sumLin_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ ts : List STerm,
      (tsum V A C O ts : Int) ≤ (tsum V A C O (sumLin F ts).1 : Int) + (sumLin F ts).2
  | [] => by simp [tsum, sumLin]
  | t :: ts => by
      have h1 := linOf_sound hF t
      have h2 := sumLin_sound hF ts
      have e1 : tsum V A C O (t :: ts) = wval (t.ev V A C O) + tsum V A C O ts := by
        simp [tsum]
      simp only [sumLin, tsum_append, e1, Nat.cast_add]
      omega

/-- The list `ts` with one occurrence of each term of `as` removed, when each occurs. -/
def eraseAll (ts : List STerm) : List STerm → Option (List STerm)
  | [] => some ts
  | a :: as => if a ∈ ts then eraseAll (ts.erase a) as else none

theorem eraseAll_sum (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) :
    ∀ (as ts R : List STerm), eraseAll ts as = some R →
      tsum V A C O ts = tsum V A C O as + tsum V A C O R
  | [], ts, R, h => by
      simp only [eraseAll, Option.some.injEq] at h
      subst h
      simp [tsum]
  | a :: as, ts, R, h => by
      simp only [eraseAll] at h
      split at h
      · rename_i ha
        have ih := eraseAll_sum V A C O as (ts.erase a) R h
        have hp := ((List.perm_cons_erase ha).map fun t => wval (t.ev V A C O)).sum_eq
        simp only [tsum, List.map_cons, List.sum_cons] at hp ih ⊢
        omega
      · cases h

/-- The fact `f` bounds the sum of the atoms `as` plus `K` by `b'`. -/
def leBy (F : List SFact) (as : List STerm) (K : Int) (b' : Nat) : SFact → Bool
  | .le ts b =>
      match eraseAll ts as with
      | some R => decide ((b : Int) - (lbSum F R : Int) + K ≤ b')
      | none => false
  | .ge _ _ => false
  | .w64 _ => false

/-- The sum of `ts` is at most `b'` by its linear form: the form is a constant within the
    bound, or one fact bounds a sum containing its atoms. -/
def leLin (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  (decide ((sumLin F ts).1 = []) && decide ((sumLin F ts).2 ≤ b'))
    || F.any (leBy F (sumLin F ts).1 (sumLin F ts).2 b')

theorem leLin_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {ts : List STerm} {b' : Nat}
    (h : leLin F ts b' = true) : tsum V A C O ts ≤ b' := by
  have hs := sumLin_sound hF ts
  simp only [leLin, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h with ⟨he, hk⟩ | ⟨f, hf, hl⟩
  · have h0 : tsum V A C O [] = 0 := rfl
    rw [he, h0] at hs
    omega
  · cases f with
    | ge _ _ => simp [leBy] at hl
    | w64 _ => simp [leBy] at hl
    | le ts0 b =>
        simp only [leBy] at hl
        split at hl
        · rename_i R hR
          simp only [decide_eq_true_eq] at hl
          have h0 : tsum V A C O ts0 ≤ b := hF _ hf
          have h1 := eraseAll_sum V A C O _ _ _ hR
          have h2 := lbSum_le hF R
          omega
        · cases hl

/-- The term `t` has width `64` by its outermost constructors or by a width fact of `F`. -/
def widOk (F : List SFact) (t : STerm) : Bool :=
  decide (t.wbase.wknown = some 64) || decide (SFact.w64 t.wbase ∈ F)

theorem widOk_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {t : STerm} (h : widOk F t = true) :
    (t.ev V A C O).1 = 64 := by
  rw [← STerm.wbase_ev]
  simp only [widOk, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact STerm.wknown_ev V A C O h
  · exact hF _ h

/-- The immediate factor `c` and the other factor `x` of a product at width `64` whose value
    is at most `c` times the value of `x`: a product `MUL x c`, or a product `MUL c x` whose
    factor `x` has width `64` (`widOk`). -/
def mulParts (F : List SFact) : STerm → Option (Nat × STerm)
  | .bin m x y =>
      if m = "MUL" then
        match y with
        | .immW w c => if w = 64 then some (c, x) else none
        | _ =>
            match x with
            | .immW w c => if w = 64 ∧ widOk F y = true then some (c, y) else none
            | _ => none
      else none
  | _ => none

theorem mulImm_mod_le (a c : Nat) : a * (c % 2 ^ 64) % 2 ^ 64 ≤ c * a :=
  (Nat.mod_le _ _).trans ((Nat.mul_le_mul_left a (Nat.mod_le c _)).trans (Nat.mul_comm a c).le)

/-- A product with an immediate as the second factor is at most the product of the values. -/
theorem wval_mulImm_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (x : STerm) (c : Nat) :
    wval ((STerm.bin "MUL" x (.immW 64 c)).ev V A C O) ≤ c * wval (x.ev V A C O) := by
  rw [wval_bin]
  split
  · simp only [binW, STerm.ev, extW, BitVec.setWidth_eq]
    simp only [show ("MUL" = "MULXHI") = False by decide, if_false, applyOpnN,
      Option.getD_some, BitVec.toNat_mul, BitVec.toNat_ofNat]
    exact mulImm_mod_le _ _
  · exact Nat.zero_le _

/-- A product with an immediate as the first factor and a second factor of width `64` is at
    most the product of the values. -/
theorem wval_immMul_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (y : STerm) (c : Nat) (hy : (y.ev V A C O).1 = 64) :
    wval ((STerm.bin "MUL" (.immW 64 c) y).ev V A C O) ≤ c * wval (y.ev V A C O) := by
  rw [wval_bin]
  simp only [STerm.ev, if_true, binW, show ("MUL" = "MULXHI") = False by decide, if_false,
    applyOpnN, Option.getD_some, extW_of_eq hy, BitVec.toNat_mul]
  unfold wval
  simp only [castW, dite_true, BitVec.toNat_ofNat]
  rw [Nat.mul_comm]
  exact mulImm_mod_le _ _

theorem mulParts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {a x : STerm} {c : Nat}
    (h : mulParts F a = some (c, x)) : wval (a.ev V A C O) ≤ c * wval (x.ev V A C O) := by
  unfold mulParts at h
  split at h
  · split at h
    · rename_i hm
      subst hm
      split at h
      · split at h
        · rename_i hw
          subst hw
          cases h
          exact wval_mulImm_le V A C O _ _
        · cases h
      · split at h
        · split at h
          · rename_i hw
            obtain ⟨rfl, hw⟩ := hw
            cases h
            exact wval_immMul_le V A C O _ _ (widOk_sound hF hw)
          · cases h
        · cases h
    · cases h
  · cases h

/-- If `x ≤ (b' - K) / c` and `K ≤ b'` then `c * x + K ≤ b'`. -/
theorem mulLe_arith {c x : Nat} {K : Int} {b' : Nat} (hK : K ≤ b')
    (hx : x ≤ ((b' : Int) - K).toNat / c) : ((c * x : Nat) : Int) + K ≤ b' := by
  have h1 : c * x ≤ ((b' : Int) - K).toNat :=
    (Nat.mul_le_mul_left c hx).trans (Nat.mul_div_le _ _)
  have h2 : ((c * x : Nat) : Int) ≤ ((((b' : Int) - K).toNat : Nat) : Int) :=
    Int.ofNat_le.mpr h1
  rw [Int.toNat_of_nonneg (by omega)] at h2
  omega

/-- The sum of `ts` is at most `b'` by a product: its linear form is one atom `mulParts`
    reads as `c` times `x`, plus a constant `K ≤ b'`, and `x` is at most `(b' - K) / c` by
    `leLin`. -/
def mulLe (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  match (sumLin F ts).1 with
  | [a] =>
      match mulParts F a with
      | some (c, x) =>
          decide ((sumLin F ts).2 ≤ b') &&
            leLin F [x] (((b' : Int) - (sumLin F ts).2).toNat / c)
      | none => false
  | _ => false

theorem mulLe_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {ts : List STerm} {b' : Nat}
    (h : mulLe F ts b' = true) : tsum V A C O ts ≤ b' := by
  have hs := sumLin_sound hF ts
  unfold mulLe at h
  split at h
  · rename_i a ha
    split at h
    · rename_i c x hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h1 := mulParts_sound (V := V) (A := A) (C := C) (O := O) hF hp
      have h2 := leLin_sound hF h.2
      have e1 : tsum V A C O [x] = wval (x.ev V A C O) := by simp [tsum]
      have e2 : tsum V A C O [a] = wval (a.ev V A C O) := by simp [tsum]
      rw [e1] at h2
      rw [ha, e2] at hs
      have h3 := mulLe_arith h.1 h2
      have h4 : ((wval (a.ev V A C O) : Nat) : Int) ≤ ((c * wval (x.ev V A C O) : Nat) : Int) :=
        Int.ofNat_le.mpr h1
      omega
    · cases h
  · cases h

/-- The upper bound the first fact of `F` on the single term `t` states. -/
def ubOf : List SFact → STerm → Option Nat
  | [], _ => none
  | .le [t'] b :: F, t => if t' = t then some b else ubOf F t
  | _ :: F, t => ubOf F t

theorem ubOf_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} :
    ∀ (F : List SFact) (t : STerm) (u : Nat), (∀ f ∈ F, f.holds V A C O) →
      ubOf F t = some u → wval (t.ev V A C O) ≤ u
  | [], _, _, _, h => by cases h
  | .le [t'] b :: F, t, u, hF, h => by
      simp only [ubOf] at h
      split at h
      · rename_i he
        subst he
        cases h
        have := hF (.le [t'] b) List.mem_cons_self
        simpa [SFact.holds, tsum] using this
      · exact ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .le [] _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .le (_ :: _ :: _) _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .ge _ _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .w64 _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h

/-- The sum of the upper bounds `ubOf` of a list of terms, when each has one. -/
def ubSum (F : List SFact) : List STerm → Option Nat
  | [] => some 0
  | t :: ts =>
      match ubOf F t, ubSum F ts with
      | some u, some v => some (u + v)
      | _, _ => none

theorem ubSum_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ (ts : List STerm) (u : Nat), ubSum F ts = some u → tsum V A C O ts ≤ u
  | [], u, h => by
      simp only [ubSum, Option.some.injEq] at h
      subst h
      simp [tsum]
  | t :: ts, u, h => by
      simp only [ubSum] at h
      split at h
      · rename_i a b ha hb
        cases h
        have h1 := ubOf_sound F t a hF ha
        have h2 := ubSum_sound hF ts b hb
        simp only [tsum, List.map_cons, List.sum_cons] at h2 ⊢
        omega
      · cases h

/-- The terms `ts` of a fact with the terms of `as` that occur in them removed, and the
    terms of `as` that do not occur. -/
def peel (ts : List STerm) : List STerm → List STerm × List STerm
  | [] => (ts, [])
  | a :: as => if a ∈ ts then peel (ts.erase a) as else ((peel ts as).1, a :: (peel ts as).2)

theorem peel_sum (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) :
    ∀ (as ts : List STerm),
      tsum V A C O as + tsum V A C O (peel ts as).1 =
        tsum V A C O ts + tsum V A C O (peel ts as).2
  | [], ts => by simp [peel, tsum]
  | a :: as, ts => by
      simp only [peel]
      split
      · rename_i ha
        have ih := peel_sum V A C O as (ts.erase a)
        have hp := ((List.perm_cons_erase ha).map fun t => wval (t.ev V A C O)).sum_eq
        simp only [tsum, List.map_cons, List.sum_cons] at hp ih ⊢
        omega
      · have ih := peel_sum V A C O as ts
        simp only [tsum, List.map_cons, List.sum_cons] at ih ⊢
        omega

/-- A sum `ADD x y` of a term of width `64` is at most the sum of the values. -/
theorem wval_addR_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (x y : STerm) (hy : (y.ev V A C O).1 = 64) :
    wval ((STerm.bin "ADD" x y).ev V A C O) ≤ wval (x.ev V A C O) + wval (y.ev V A C O) := by
  rw [wval_bin]
  split
  · simp only [binW, show ("ADD" = "MULXHI") = False by decide, if_false, applyOpnN,
      Option.getD_some, BitVec.toNat_add, extW_of_eq hy]
    unfold wval
    exact Nat.mod_le _ _
  · omega

/-- An atom `ADD x y` with `y` of width `64` as the linear forms of `x` and `y`; every other
    atom is itself. -/
def splitAdd (F : List SFact) : STerm → List STerm × Int
  | .bin m x y =>
      if m = "ADD" ∧ widOk F y then
        ((linOf F x).1 ++ (linOf F y).1, (linOf F x).2 + (linOf F y).2)
      else ([.bin m x y], 0)
  | t => ([t], 0)

theorem splitAdd_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    (wval (t.ev V A C O) : Int) ≤ (tsum V A C O (splitAdd F t).1 : Int) + (splitAdd F t).2 := by
  unfold splitAdd
  split
  · rename_i m x y
    split
    · rename_i h
      obtain ⟨rfl, hw⟩ := h
      have h0 := wval_addR_le V A C O x y (widOk_sound hF hw)
      have h1 := linOf_sound hF x
      have h2 := linOf_sound hF y
      simp only [tsum_append, Nat.cast_add]
      omega
    · simp [tsum]
  · simp [tsum]

/-- `splitAdd` over a list of atoms. -/
def splitAdds (F : List SFact) : List STerm → List STerm × Int
  | [] => ([], 0)
  | t :: ts => ((splitAdd F t).1 ++ (splitAdds F ts).1, (splitAdd F t).2 + (splitAdds F ts).2)

theorem splitAdds_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ ts : List STerm,
      (tsum V A C O ts : Int) ≤ (tsum V A C O (splitAdds F ts).1 : Int) + (splitAdds F ts).2
  | [] => by simp [tsum, splitAdds]
  | t :: ts => by
      have h1 := splitAdd_sound hF t
      have h2 := splitAdds_sound hF ts
      have e1 : tsum V A C O (t :: ts) = wval (t.ev V A C O) + tsum V A C O ts := by
        simp [tsum]
      simp only [splitAdds, tsum_append, e1, Nat.cast_add]
      omega

/-- The fact `f` bounds the atoms `as` it contains, and single-term facts bound the atoms it
    does not contain: the sum of `as` plus `K` is at most `b'`. -/
def leMixBy (F : List SFact) (as : List STerm) (K : Int) (b' : Nat) : SFact → Bool
  | .le ts b =>
      match ubSum F (peel ts as).2 with
      | some u => decide ((b : Int) - (lbSum F (peel ts as).1 : Int) + u + K ≤ b')
      | none => false
  | .ge _ _ => false
  | .w64 _ => false

/-- The sum of `ts` is at most `b'` by its linear form, one fact for the atoms it contains and
    single-term facts for the others (an index `off + i` with a bound on `off` and a loop
    invariant on `i`). -/
def leMix (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  F.any (leMixBy F (splitAdds F (sumLin F ts).1).1
    ((sumLin F ts).2 + (splitAdds F (sumLin F ts).1).2) b')

theorem leMix_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {ts : List STerm} {b' : Nat}
    (h : leMix F ts b' = true) : tsum V A C O ts ≤ b' := by
  have hs0 := sumLin_sound hF ts
  have hs1 := splitAdds_sound hF (sumLin F ts).1
  have hs : (tsum V A C O ts : Int) ≤ (tsum V A C O (splitAdds F (sumLin F ts).1).1 : Int) +
      ((sumLin F ts).2 + (splitAdds F (sumLin F ts).1).2) := by omega
  simp only [leMix, List.any_eq_true] at h
  obtain ⟨f, hf, hl⟩ := h
  cases f with
  | ge _ _ => simp [leMixBy] at hl
  | w64 _ => simp [leMixBy] at hl
  | le ts0 b =>
      simp only [leMixBy] at hl
      split at hl
      · rename_i u hu
        simp only [decide_eq_true_eq] at hl
        have h0 : tsum V A C O ts0 ≤ b := hF _ hf
        have h1 := peel_sum V A C O (splitAdds F (sumLin F ts).1).1 ts0
        have h2 := lbSum_le hF (peel ts0 (splitAdds F (sumLin F ts).1).1).1
        have h3 := ubSum_sound hF _ u hu
        omega
      · cases hl

/-- **Entailment**: an upper bound on a sum holds when its linear form is a constant within
    the bound, when one fact bounds a sum containing its atoms (`leLin`), or when the form
    is a product with an immediate whose other factor is bounded (`mulLe`); a lower bound
    holds when a fact states it; a width holds by `widOk`. -/
def entails (F : List SFact) : SFact → Bool
  | .le ts b' => leLin F ts b' || mulLe F ts b'
  | .ge t k => decide (k ≤ lbOf F t)
  | .w64 t => widOk F t

/-- **Entailment is sound.** -/
theorem entails_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ g : SFact, entails F g = true → g.holds V A C O
  | .ge t k, h => by
      simp only [entails, decide_eq_true_eq] at h
      exact le_trans h (lbOf_le F t hF)
  | .le ts b', h => by
      simp only [entails, Bool.or_eq_true] at h
      rcases h with h | h
      · exact leLin_sound hF h
      · exact mulLe_sound hF h
  | .w64 t, h => widOk_sound hF h

/-- The width facts a guard of a symbolic run gives: a term of width `64`, or a term whose
    width is that of a term of width `64`, each at its width base `STerm.wbase`. -/
def guardW64 : SG → List SFact
  | .wid t w => if w = 64 then [.w64 t.wbase] else []
  | .eqW x y =>
      if x.wbase.wknown = some 64 then [.w64 y.wbase]
      else if y.wbase.wknown = some 64 then [.w64 x.wbase]
      else []
  | .shp _ _ _ => []

/-- The width facts of guards that hold, hold. -/
theorem guardW64_holds {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {gs : List SG} (h : AllG V A C O gs) : ∀ f ∈ gs.flatMap guardW64, f.holds V A C O := by
  intro f hf
  obtain ⟨g, hg, hfg⟩ := List.mem_flatMap.mp hf
  have hh := h g hg
  cases g with
  | wid t w =>
      simp only [guardW64] at hfg
      split at hfg
      · rename_i hw
        subst hw
        simp only [List.mem_singleton] at hfg
        subst hfg
        exact (STerm.wbase_ev V A C O t).trans hh
      · simp at hfg
  | eqW x y =>
      simp only [guardW64] at hfg
      have hx := STerm.wbase_ev V A C O x
      have hy := STerm.wbase_ev V A C O y
      have he : (x.ev V A C O).1 = (y.ev V A C O).1 := hh
      split at hfg
      · rename_i hk
        simp only [List.mem_singleton] at hfg
        subst hfg
        have := STerm.wknown_ev V A C O hk
        exact hy.trans (he.symm.trans (hx.symm.trans this))
      · split at hfg
        · rename_i hk
          simp only [List.mem_singleton] at hfg
          subst hfg
          have := STerm.wknown_ev V A C O hk
          exact hx.trans (he.trans (hy.symm.trans this))
        · simp at hfg
  | shp _ _ _ => simp [guardW64] at hfg

/-! ## 3. Edge facts -/

/-- The facts the condition `d` gives on the edge it takes (`taken`) or falls through: a
    branch on the zero flag of a comparison with `0` that the zero flag does not select, or
    a taken branch on a non-zero register, gives the lower bound `1`. -/
def edgeFacts (d : SDec) (taken : Bool) : List SFact :=
  match d with
  | .flag pol (.cmp x (.immW 64 0)) => if taken = pol then [] else [.ge x 1]
  | .nz t => if taken then [.ge t 1] else []
  | _ => []

theorem one_le_wval {x : Σ w, BitVec w} (h : castW x 64 ≠ 0#64) : 1 ≤ wval x := by
  unfold wval
  have : (castW x 64).toNat ≠ 0 := by
    intro h0
    exact h (BitVec.eq_of_toNat_eq (by simpa using h0))
  omega

/-- **Edge facts are sound.** -/
theorem edgeFacts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {d : SDec} {taken : Bool} (h : d.ev V A C O Z = taken) :
    ∀ f ∈ edgeFacts d taken, f.holds V A C O := by
  unfold edgeFacts
  split
  · rename_i pol x
    split
    · simp
    · rename_i hne
      simp only [List.mem_singleton, forall_eq]
      apply one_le_wval
      simp only [SDec.ev, SFlag.ev, STerm.ev] at h
      intro h0
      have hc : castW (⟨64, BitVec.ofNat 64 0⟩ : Σ w, BitVec w) 64 = 0#64 := by simp [castW]
      rw [h0, hc] at h
      cases pol <;> cases taken <;> simp_all
  · rename_i t
    split
    · simp only [List.mem_singleton, forall_eq]
      apply one_le_wval
      simp only [SDec.ev] at h
      split at h <;> simp_all
    · simp
  · simp

/-! ## 4. The check -/

/-- The facts of block `k` under the annotation `ann`. -/
def annAt (ann : List (List IdxFact)) (k : Nat) : List IdxFact := ann.getD k []

/-- Facts over the registers at a block entry, as symbolic facts at that entry. -/
def startF (fs : List IdxFact) : List SFact := fs.map (IdxFact.toS STerm.reg)

theorem startF_holds {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {fs : List IdxFact} (h : ∀ f ∈ fs, f.holds V) : ∀ g ∈ startF fs, g.holds V A C O := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  exact (IdxFact.toS_holds STerm.reg f).mpr (h f hf)

/-- The facts `fs` of a successor follow, through the final symbolic registers of `ss`, from
    the facts `F`. -/
def succOk (F : List SFact) (ss : SSt) (fs : List IdxFact) : Bool :=
  fs.all fun f => entails F (f.toS ss.regs)

theorem succOk_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {F : List SFact} {ss : SSt} {fs : List IdxFact} (h : succOk F ss fs = true)
    (hF : ∀ f ∈ F, f.holds V A C O) {u : LstateMF} (hu : Holds V A C O Z ss u) :
    ∀ f ∈ fs, f.holds u.prog.base.reg.lvm := by
  intro f hf
  simp only [succOk, List.all_eq_true] at h
  have := (IdxFact.toS_holds (V := V) (A := A) (C := C) (O := O) ss.regs f).mp
    (entails_sound hF _ (h f hf))
  have he : u.prog.base.reg.lvm = fun r => (ss.regs r).ev V A C O := funext hu.1
  rw [he]
  exact this

/-- Every index obligation follows from the facts `F`: its index is below the length, by
    `entails` or by `leMix`. -/
def oblsOk (F : List SFact) (os : List SObl) : Bool :=
  os.all fun o => decide (0 < o.2) &&
    (entails F (.le [o.1] (o.2 - 1)) || leMix F [o.1] (o.2 - 1))

theorem oblsOk_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} {os : List SObl} (h : oblsOk F os = true)
    (hF : ∀ f ∈ F, f.holds V A C O) : ∀ o ∈ os, o.holds V A C O := by
  intro o ho _
  simp only [oblsOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, he⟩ := h o ho
  have : (SFact.le [o.1] (o.2 - 1)).holds V A C O := by
    rcases Bool.or_eq_true_iff.mp he with he | he
    · exact entails_sound hF _ he
    · exact leMix_sound hF he
  simp only [SFact.holds, tsum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at this
  unfold wval at this
  omega

/-- The successor facts of a block with terminator `T`, last instruction `z` and final
    symbolic state `ss` follow from the facts `F` of the block. -/
def termInvOk (ann : List (List IdxFact)) (F : List SFact) (ss : SSt) (T : Term)
    (z : Option LinstrRM) : Bool :=
  match T with
  | .fall (some j) => succOk F ss (annAt ann j)
  | .fall none => true
  | .goto tg => succOk F ss (annAt ann tg)
  | .cond tg nx =>
      match z with
      | some (.Lcond c _, _) =>
          succOk (F ++ edgeFacts (symDec ss c) true) ss (annAt ann tg) &&
            match nx with
            | some j => succOk (F ++ edgeFacts (symDec ss c) false) ss (annAt ann j)
            | none => true
      | _ => false
  | .ret => true

/-- **The check of block `k`**: a block ending in `Lret`, or whose symbolic run fails, is
    accepted; otherwise its symbolic run is in the fragment, its index obligations follow
    from its facts and the width facts `guardW64` of the guards of the run, and the facts of
    its successors follow. -/
def blockInvOk (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG) (k : Nat) : Bool :=
  match (G.blk k).term with
  | .ret => true
  | T =>
      match symRun (bodyAt B (G.blk k) T) SSt.start with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          oblsOk (startF (annAt ann k) ++ gs.flatMap guardW64)
              (symObl (bodyAt B (G.blk k) T) SSt.start) &&
            termInvOk ann (startF (annAt ann k)) ss T B[(G.blk k).stop - 1]?

/-- **The bounds-invariant check** of the body `B` under the annotation `ann`, from the
    entry facts `entry`: the body has a control-flow graph, every block passes
    `blockInvOk`, and the entry facts give the facts of block `0`. -/
def idxInvCheckB (entry : List IdxFact) (ann : List (List IdxFact)) (B : List LinstrRM) :
    Bool :=
  match cfgOf (B.map Prod.fst) with
  | some G =>
      (List.range G.blocks.size).all (blockInvOk ann B G) &&
        (annAt ann 0).all fun f => entails (startF entry) (f.toS STerm.reg)
  | none => false

/-! ## 5. Soundness -/

section Sound

variable {ann : List (List IdxFact)} {B : List LinstrRM} {G : CFG} {fn : String}

/-- The invariant up to the measure `N`: a halting run from a block entry at which the
    facts of the block hold is in bounds. -/
def InvAt (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG) (fn : String) (N : Nat) :
    Prop :=
  ∀ (fuel k : Nat) (s t : LstateMF),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    EntryAt B (G.blk k) s.prog.base.reg.lpc → s.prog.lfn = fn →
    (∀ f ∈ annAt ann k, f.holds s.prog.base.reg.lvm) →
    lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    RunIdxOk (singletonProgM fn B) fuel s

theorem inv_step (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOk ann B G k = true) {N : Nat}
    (ih : InvAt ann B G fn N) : InvAt ann B G fn (N + 1) := by
  intro fuel k s t hN hk hE hfn hinv hrun
  have F := blockFacts hG hk
  obtain ⟨hs1, hle⟩ := entry_le hG hk hE
  have hplain := body_plain hG hk hs1
  obtain ⟨u, f, hf, hu, hru⟩ :=
    fuel_runL _ _ s t fuel hfn (drop_split B hle) hplain hrun
  obtain ⟨hul, hup⟩ := runL_frame _ s u hplain hu
  have hbstop : bstopOf (G.blk k).term (G.blk k) ≤ B.length := by
    unfold bstopOf; split <;> have := F.le <;> simp at this <;> omega
  simp only [List.length_take, List.length_drop] at hup hf
  have hupc : u.prog.base.reg.lpc = bstopOf (G.blk k).term (G.blk k) := by
    rw [hup]; omega
  have hul' : u.prog.lfn = fn := hul.trans hfn
  have hlt : (G.blk k).stop - 1 < B.length := by have := F.le; have := F.lt; simp at *; omega
  obtain ⟨z, hz⟩ : ∃ z, B[(G.blk k).stop - 1]? = some z :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hterm := F.term
  rw [List.getElem?_map, hz, Option.map_some] at hterm
  -- a block ending in `Lret` is never left by a halting run
  by_cases hret : (G.blk k).term = .ret
  · rcases termOk_spec hterm with ⟨_, hT, _⟩ | ⟨_, _, _, hT, _⟩ | ⟨_, _, _, _, hT, _⟩ | ⟨_, hzr⟩
    all_goals try (rw [hret] at hT; cases hT)
    have hupc2 : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by
      rw [hupc]; simp [bstopOf, hret]
    obtain ⟨_, _, _, he, _⟩ :=
      run_inv hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [evalInstrPMemF_ret] at he
    cases he
  -- the symbolic run of the block body
  have hD := symRun_sound (singletonProgM fn B) ((B.drop s.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s
    (holds_start s)
  rw [symRun_entry hE hle] at hD
  have hbk := hb k hk
  unfold blockInvOk at hbk
  have hbk' : (match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          oblsOk (startF (annAt ann k) ++ gs.flatMap guardW64)
              (symObl (bodyAt B (G.blk k) (G.blk k).term) SSt.start) &&
            termInvOk ann (startF (annAt ann k)) ss (G.blk k).term
              B[(G.blk k).stop - 1]?) = true := by
    revert hbk
    cases hT : (G.blk k).term with
    | ret => exact absurd hT hret
    | _ => exact id
  cases hS : symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
  | fail =>
      rw [hS] at hD
      simp only [SOut.DescN] at hD
      rw [hD] at hu
      cases hu
  | unk => rw [hS] at hbk'; cases hbk'
  | ok ss gs =>
  rw [hS] at hD hbk'
  simp only [Bool.and_eq_true] at hbk'
  obtain ⟨hobl, hti⟩ := hbk'
  obtain ⟨hgs, hH, -⟩ := hD.1 u hu
  have hF0 := startF_holds (A := s.prog.base.larr) (C := s.prog.base.cf) (O := s.prog.base.of)
    hinv
  have hF1 : ∀ g ∈ startF (annAt ann k) ++ gs.flatMap guardW64,
      g.holds s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf s.prog.base.of := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hF0 g hg
    · exact guardW64_holds hgs g hg
  -- the stretch is in bounds
  have hlS : RunLOk (singletonProgM fn B) ((B.drop s.prog.base.reg.lpc).take
      (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) s := by
    refine (symObl_sound (singletonProgM fn B) _ SSt.start _ _ _ _ _ s u (holds_start s)
      ⟨ss, gs, by rw [symRun_entry hE hle]; exact hS⟩ hu).mpr fun o ho => ?_
    rw [symObl_entry hE hle] at ho
    exact oblsOk_sound hobl hF1 o ho
  have hokJ : ∀ f0, RunIdxOk (singletonProgM fn B) f0 u →
      RunIdxOk (singletonProgM fn B) (((B.drop s.prog.base.reg.lpc).take
        (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)).length + f0) s :=
    fun f0 h0 => runIdxOk_of_runL _ _ s u f0 hfn (drop_split B hle) hplain hu hlS h0
  simp only [List.length_take, List.length_drop] at hokJ
  rw [hf]
  have hlen : min (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)
      (B.length - s.prog.base.reg.lpc) = bstopOf (G.blk k).term (G.blk k)
        - s.prog.base.reg.lpc := by omega
  rw [hlen] at hokJ
  rw [hlen]
  apply hokJ
  have hfle : f ≤ fuel := by omega
  obtain ⟨zi, zt⟩ := z
  rw [hz] at hti
  simp only at hterm
  rcases termOk_spec hterm with ⟨nx, hT, _, hnx⟩ | ⟨tg, x, l, hT, hzi, htg, hl⟩ |
      ⟨tg, nx, c, l, hT, hzi, htg, hl, hnx⟩ | ⟨hT, _⟩
  · -- fall through
    have hw : u.prog.base.reg.lpc = (G.blk k).stop := by rw [hupc, hT]; rfl
    rw [hT] at hti
    cases nx with
    | none =>
        have e1 := (stop_next hG hk).1 hnx.symm
        exact runIdxOk_halt (by rw [findInstrMem_single hul', hw, e1]; simp) f
    | some j =>
        obtain ⟨hj, hjlt, e1⟩ := (stop_next hG hk).2 j hnx.symm
        subst hj
        exact ih f (k + 1) u t (measure_le hN hfle hk) hjlt (Or.inl (hw.trans e1)) hul'
          (succOk_sound hti hF0 hH) hru
  · -- jump
    subst hzi
    rw [hT] at hti
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lgoto (x, l), zt) := by
      rw [findInstrMem_single hul', hw, hz]
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv hru hfetch
    have he0 := he
    rw [evalInstrPMemF_goto] at he
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [if_pos hx, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      subst hf1
      exact runIdxOk_step hfetch (idxOkB_goto _ _ _ _) he0
        (ih f1 tg _ t (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
          (Or.inr ⟨rfl, label_at hl⟩) hul' (succOk_sound hti hF0 hH) hr1)
    · rw [if_neg hx] at he
      cases he
  · -- branch
    subst hzi
    rw [hT] at hti
    simp only [termInvOk, Bool.and_eq_true] at hti
    obtain ⟨htk, hnt⟩ := hti
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lcond c l, zt) := by
      rw [findInstrMem_single hul', hw, hz]
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv hru hfetch
    have he0 := he
    subst hf1
    have hdec := decC_eq hH c
    rw [evalInstrPMemF_cond] at he
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    by_cases hd : decC u c = true
    · rw [if_pos hd, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have hE' : ∀ g ∈ startF (annAt ann k) ++ edgeFacts (symDec ss c) true,
          g.holds s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf s.prog.base.of := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF0 g hg
        · exact edgeFacts_sound (hdec.symm.trans hd) g hg
      exact runIdxOk_step hfetch (idxOkB_cond _ _ _ _) he0
        (ih f1 tg _ t (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
          (Or.inr ⟨rfl, label_at hl⟩) hul' (succOk_sound htk hE' hH) hr1)
    · rw [if_neg hd] at he
      simp only [Option.some.injEq] at he
      subst he
      have hE' : ∀ g ∈ startF (annAt ann k) ++ edgeFacts (symDec ss c) false,
          g.holds s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf s.prog.base.of := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF0 g hg
        · exact edgeFacts_sound (by rw [← hdec]; simpa using hd) g hg
      refine runIdxOk_step hfetch (idxOkB_cond _ _ _ _) he0 ?_
      have hw1 : u.prog.base.reg.lpc + 1 = (G.blk k).stop := by omega
      cases nx with
      | none =>
          have e1 := (stop_next hG hk).1 hnx.symm
          exact runIdxOk_halt (by
            rw [findInstrMem_single (s := ⟨⟨u.prog.base.nextPc, u.prog.lfn⟩, u.zf⟩) hul']
            show B[u.prog.base.reg.lpc + 1]? = none
            rw [hw1, e1]; simp) f1
      | some j =>
          obtain ⟨hj, hjlt, e1⟩ := (stop_next hG hk).2 j hnx.symm
          subst hj
          exact ih f1 (k + 1) _ t (measure_le hN (show f1 ≤ fuel by omega) hk) hjlt
            (Or.inl (hw1.trans e1)) hul' (succOk_sound hnt hE' hH) hr1
  · exact absurd hT hret

theorem invAt_all (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOk ann B G k = true) : ∀ N, InvAt ann B G fn N
  | 0 => fun _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => inv_step hG hb (invAt_all hG hb N)

end Sound

/-- **Soundness of the bounds-invariant check.** If `idxInvCheckB entry ann B` accepts,
    every halting run of `lsemFuelMemF` on the singleton program over `B` from a state at
    pc `0` of that function whose registers satisfy the entry facts is in bounds. -/
theorem runIdxOk_of_idxInvCheckB {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} (h : idxInvCheckB entry ann B = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    RunIdxOk (singletonProgM fn B) fuel s := by
  unfold idxInvCheckB at h
  split at h
  · rename_i G hG
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    obtain ⟨hb, h0⟩ := h
    by_cases hB : B.map Prod.fst = []
    · have hBn : B = [] := by simpa using hB
      subst hBn
      exact runIdxOk_halt (by rw [findInstrMem_single hfn]; simp) fuel
    obtain ⟨hpos, hs0⟩ := cfgOf_start_zero hG hB
    have hF := startF_holds (A := s.prog.base.larr) (C := s.prog.base.cf)
      (O := s.prog.base.of) hent
    have hinv : ∀ f ∈ annAt ann 0, f.holds s.prog.base.reg.lvm := fun f hf =>
      (IdxFact.toS_holds STerm.reg f).mp (entails_sound hF _ (h0 f hf))
    exact invAt_all hG hb _ fuel 0 s t (Nat.lt_succ_self _) hpos
      (Or.inl (hpc.trans hs0.symm)) hfn hinv hrun
  · cases h

/-- **A halting run of an accepted body is a halting checked run.** -/
theorem lsemFuelMemFk_of_idxInvCheckB {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} (h : idxInvCheckB entry ann B = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    lsemFuelMemFk true (singletonProgM fn B) fuel s = some t :=
  lsemFuelMemFk_of_runIdxOk true _ fuel s t hrun
    (runIdxOk_of_idxInvCheckB h fn s t hfn hpc hent fuel hrun)

/-- **The checker on runs of an accepted source body.** If `ownedCheckMC outs B B'` and
    `idxInvCheckB entry ann B` accept, every halting run of `lsemFuelMemF` on `B` from a
    state at pc `0` whose registers satisfy the entry facts is matched by a halting checked
    run of `B'` from the same state, the end states agreeing on `outs`, the arrays and the
    word memory. -/
theorem ownedCheckMC_sound_of_idxInv {outs : List String} {B B' : List LinstrRM}
    {entry : List IdxFact} {ann : List (List IdxFact)} (h : ownedCheckMC outs B B' = true)
    (hi : idxInvCheckB entry ann B = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' :=
  ownedCheckMC_sound h fn s t hfn hpc fuel
    (lsemFuelMemFk_of_idxInvCheckB hi fn s t hfn hpc hent fuel hrun)

/-! ## 6. Annotation by restriction to a fixed point -/

/-- The registers an index obligation, a branch condition or an entry fact of `B` reads:
    the candidates of the annotation. -/
def annRegs (entry : List IdxFact) (B : List LinstrRM) (G : CFG) : List String :=
  let fromEntry := entry.flatMap fun | .le rs _ => rs | .ge r _ => [r]
  let fromBlocks := (List.range G.blocks.size).flatMap fun k =>
    match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
    | .ok ss _ =>
        (symObl (bodyAt B (G.blk k) (G.blk k).term) SSt.start).flatMap (·.1.vars)
          ++ match B[(G.blk k).stop - 1]? with
            | some (.Lcond c _, _) => (symDec ss c).vars
            | _ => []
    | _ => []
  (fromEntry ++ fromBlocks).eraseDups

/-- The candidate facts over the registers `rs` with the bounds `bs`: each register and each
    pair of distinct registers bounded by each bound, and each register at least `1`. -/
def annCands (rs : List String) (bs : List Nat) : List IdxFact :=
  let pairs := rs.flatMap fun r => (rs.dropWhile (· ≠ r)).drop 1 |>.map fun r' => [r, r']
  (bs.flatMap fun b => (rs.map fun r => .le [r] b) ++ pairs.map fun p => .le p b)
    ++ rs.map fun r => .ge r 1

/-- One restriction pass: for every block in order, the facts of each successor that do not
    follow from the facts of the block (with the condition of the edge) are dropped. -/
def annPass (B : List LinstrRM) (G : CFG) (ann : List (List IdxFact)) :
    List (List IdxFact) :=
  (List.range G.blocks.size).foldl (fun ann k =>
    match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
    | .ok ss _ =>
        let F := startF (annAt ann k)
        let keep (F' : List SFact) (ann : List (List IdxFact)) (j : Nat) :=
          ann.set j ((annAt ann j).filter fun f => entails F' (f.toS ss.regs))
        match (G.blk k).term with
        | .fall (some j) => keep F ann j
        | .goto tg => keep F ann tg
        | .cond tg nx =>
            match B[(G.blk k).stop - 1]? with
            | some (.Lcond c _, _) =>
                let ann := keep (F ++ edgeFacts (symDec ss c) true) ann tg
                match nx with
                | some j => keep (F ++ edgeFacts (symDec ss c) false) ann j
                | none => ann
            | _ => ann
        | _ => ann
    | _ => ann) ann

/-- The array lengths of the index obligations of the blocks of `B`. -/
def oblLens (B : List LinstrRM) (G : CFG) : List Nat :=
  (List.range G.blocks.size).flatMap fun k =>
    (symObl (bodyAt B (G.blk k) (G.blk k).term) SSt.start).map (·.2)

/-- The immediates at width `64` that the symbolic run of a block of `B` leaves in a register
    of `rs`: the values a counter is seeded with. -/
def seedImms (B : List LinstrRM) (G : CFG) (rs : List String) : List Nat :=
  (List.range G.blocks.size).flatMap fun k =>
    match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
    | .ok ss _ =>
        rs.filterMap fun r =>
          match ss.regs r with
          | .immW w n => if w = 64 then some n else none
          | _ => none
    | _ => []

/-- **The annotation by restriction**: block `0` holds the candidates the entry facts give,
    every other block all candidates, restricted by `annPass` to a fixed point (within a
    bound on the number of passes). The bounds of the candidates are the bounds of the
    entry facts, the array lengths `oblLens` of the index obligations and the immediates
    `seedImms` the blocks leave in the candidate registers, so a counter seeded with an
    immediate is bounded by that immediate and by the length of the array its index reads.
    `idxInvCheckB` checks the result. -/
def idxAnnot (entry : List IdxFact) (B : List LinstrRM) : List (List IdxFact) :=
  match cfgOf (B.map Prod.fst) with
  | some G =>
      let rs := annRegs entry B G
      let bs := ((entry.filterMap fun | .le _ b => some b | .ge _ _ => none)
        ++ oblLens B G ++ seedImms B G rs).eraseDups
      let cs := annCands rs bs
      let a0 := (List.range G.blocks.size).map fun k =>
        if k = 0 then cs.filter fun f => entails (startF entry) (f.toS STerm.reg) else cs
      (List.range (G.blocks.size * cs.length + 1)).foldl (fun a _ => annPass B G a) a0
  | none => []

/-! ## 7. The facts of a layout's register bounds -/

open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- The facts of the register bounds of `σ`, each register named by `nm`. -/
def boundFacts (σ : AbiLayout) (nm : String → String) : List IdxFact :=
  σ.bounds.map fun b => .le [nm b.1] b.2

/-- **The facts of a layout's register bounds hold** at registers `V` that hold each bounded
    register of a separated entry state at width `64` under its name. -/
theorem boundFacts_holds {σ : AbiLayout} {sa : AState} (hR : σ.Regions sa)
    {nm : String → String} {V : String → Σ w, BitVec w}
    (hV : ∀ b ∈ σ.bounds, V (nm b.1) = ⟨64, sa.regs b.1⟩) :
    ∀ f ∈ boundFacts σ nm, f.holds V := by
  intro f hf
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
  simp only [IdxFact.holds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, wval, hV b hb]
  exact hR.1 b hb

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
