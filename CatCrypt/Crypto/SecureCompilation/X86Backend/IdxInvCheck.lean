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

A fact (`IdxFact`) bounds the sum of the `64`-bit values of a list of registers from above,
the value of one register from below, every element of a named array from above
(`ArrLe`), or states that a register has width `64`; a symbolic fact (`SFact`) may also exclude one value of a term. An annotation
assigns a list of facts to each
block of the control-flow graph `cfgOf`; it is untrusted. `idxInvCheckB` checks, for every
block, along its symbolic run `symRun` from the block entry:

* every index obligation `symObl` of the block (an index term with the length of its array)
  follows from the facts of the block;
* the facts of every successor block, read through the final symbolic registers, follow
  from the facts of the block and from the condition of the edge (`edgeFacts`: a branch on
  the zero flag of a comparison with an immediate gives the value of the other operand on
  the equal edge and excludes it on the other, and a branch on a register bounds it);
* the entry facts give the facts of block `0`.

Entailment (`entails`) is syntactic: an upper bound on a sum is read off one fact after
normalising additions and subtractions of immediates in one of the ways `linAlts` lists, with
the lower bounds of the remaining summands, or from the upper bounds of its terms (`hiLe`: the
facts containing the term, a conjunction with an immediate mask, an element bound of the array
a load reads, and an excluded bound); a lower bound is read off a fact on the same term. An
element bound of an array holds by a fact on it, and across a store when the stored word is
within the bound (`arrOk`). A sum with a linear form that is one product with an immediate at
width `64` plus a constant is bounded through a bound on the other factor (`mulLe`); with the
immediate as the first factor the other factor must have width `64`, which a width fact
states. The index obligations of a block are
checked from its facts and the width facts of the guards of its symbolic run (`guardW64`).
Every reader of a form tries each form the arms admit (`linAlts`, `splitAlts`, `affAlts`), so
that a form a fact enables does not replace one the reader needed: the check is monotone in
the fact list (`IdxInvCheckComplete.entails_mono`, `oblsOk_mono`, `succOk_mono`).

`idxAnnot` computes an annotation by restricting candidate facts to a fixed point; the
bounds of its candidates are those of the entry facts, the array lengths of the index
obligations and the immediates the blocks leave in the candidate registers (`seedImms`).
The check does not depend on it. `boundFacts` reads the facts of a System V layout's register
bounds, which hold at every entry state satisfying `AbiLayout.Regions`.

## Main definitions

* `IdxFact`, `SFact`, `entails`, `linAlts`, `edgeFacts`: facts and their entailment.
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
* `SymLaws.runIdxOk_of_idxInvCheckB`, `SymLaws.lsemFuelMemFk_of_idxInvCheckB`,
  `SymLaws.ownedCheckMC_sound_of_idxInv`: the three soundness theorems at an instruction set
  `I` and a symbolic step and branch condition satisfying `SymLaws`; the x86 statements are
  their instances at `symLaws_x86`.

The check takes the symbolic step `sym` and the symbolic branch condition `dec` as
parameters, by default the x86 ones `symStep` and `symDec`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackSet)
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
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
  (x86Isa x86Isa_lsemFuelMemF x86Isa_RunIdxOk x86Isa_lsemFuelMemFk)

/-! ## 1. Facts -/

/-- The value of a width-tagged word read at width `64`, as a natural number; `0` on a
    width mismatch. -/
def wval (x : Σ w, BitVec w) : Nat := (castW x 64).toNat

theorem wval_lt (x : Σ w, BitVec w) : wval x < 2 ^ 64 := (castW x 64).isLt

theorem castW_ne {x : Σ w, BitVec w} (h : x.1 ≠ 64) : castW x 64 = 0 := by
  simp [castW, h]

/-- Every element of the array cell `c`, read at width `64` (`wval`), is at most `b`. -/
def ArrLe (c : ArrCell) (b : Nat) : Prop := ∀ i : Fin c.2.1, wval ⟨c.1, c.2.2 i⟩ ≤ b

theorem ArrLe.mono {c : ArrCell} {b b' : Nat} (h : ArrLe c b) (hb : b ≤ b') : ArrLe c b' :=
  fun i => (h i).trans hb

/-- A word cast to its own width is at most its value at width `64`. -/
theorem wval_castW_le (x : Σ w, BitVec w) (w : Nat) : wval ⟨w, castW x w⟩ ≤ wval x := by
  by_cases hw : w = 64
  · subst hw
    exact le_refl _
  · simp [wval, castW, hw]

theorem wval_zero (w : Nat) : wval ⟨w, (0 : BitVec w)⟩ = 0 := by
  by_cases hw : w = 64
  · subst hw
    simp [wval, castW]
  · simp [wval, castW, hw]

/-- Every element of an array cell cast to the shape `(w, n)` obeys the bound of the cell. -/
theorem castA_le {c : ArrCell} {b : Nat} (h : ArrLe c b) (w n : Nat) (i : Fin n) :
    wval ⟨w, castA c w n i⟩ ≤ b := by
  obtain ⟨w', n', f⟩ := c
  unfold castA
  by_cases hw : w' = w
  · subst hw
    by_cases hn : n' = n
    · subst hn
      simpa using h i
    · rw [dite_eq_left rfl, dite_eq_right hn]
      exact (wval_zero _).trans_le (Nat.zero_le b)
  · rw [dite_eq_right hw]
    exact (wval_zero _).trans_le (Nat.zero_le b)

/-- An element read by `stackGet` from an array cell cast to the shape `(w, n)` obeys the
    bound of the cell. -/
theorem stackGet_castA_le {c : ArrCell} {b : Nat} (h : ArrLe c b) (w n k : Nat) :
    wval ⟨w, stackGet (castA c w n) k⟩ ≤ b := by
  cases n with
  | zero => exact (wval_zero _).trans_le (Nat.zero_le b)
  | succ m => exact castA_le h w (m + 1) _

/-- An array cell cast to the shape `(w, n)` with one element set to the word `v` obeys a
    bound that the cell and the value of `v` obey. -/
theorem arrLe_stackSet {c : ArrCell} {b : Nat} (h : ArrLe c b) (w n k : Nat)
    (v : Σ w, BitVec w) (hv : wval v ≤ b) :
    ArrLe ⟨w, n, stackSet (castA c w n) k (castW v w)⟩ b := by
  intro i
  cases n with
  | zero => exact i.elim0
  | succ m =>
      simp only [stackSet]
      split
      · exact (wval_castW_le v w).trans hv
      · exact castA_le h w (m + 1) i

/-- A fact over the registers and arrays at a block entry: the sum of the values of the
    registers `rs` is at most `b`, the value of the register `r` is at least `k`, every
    element of the array `a` at width `64` is at most `b`, or the register `r` has width
    `64`. -/
inductive IdxFact where
  | le (rs : List String) (b : Nat)
  | ge (r : String) (k : Nat)
  | ale (a : String) (b : Nat)
  | w64 (r : String)
  deriving DecidableEq, Repr, Inhabited

/-- A fact over symbolic words: the sum of the values of the terms `ts` is at most `b`, the
    value of the term `t` is at least `k`, the term `t` has width `64`, the value of the
    term `t` is not `c`, or every element of the symbolic array `a` at width `64` is at
    most `b`. -/
inductive SFact where
  | le (ts : List STerm) (b : Nat)
  | ge (t : STerm) (k : Nat)
  | w64 (t : STerm)
  | ne (t : STerm) (c : Nat)
  | ale (a : SArr) (b : Nat)
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
  | .ne t c => wval (t.ev V A C O) ≠ c
  | .ale a b => ArrLe (a.ev V A C O) b

end Eval

/-- A fact holds at the registers `V` and the arrays `A`. -/
def IdxFact.holds (V : String → Σ w, BitVec w) (A : String → ArrCell) : IdxFact → Prop
  | .le rs b => (rs.map fun r => wval (V r)).sum ≤ b
  | .ge r k => k ≤ wval (V r)
  | .ale a b => ArrLe (A a) b
  | .w64 r => (V r).1 = 64

/-- A fact read through the symbolic registers `R` and the symbolic arrays `Ar`. -/
def IdxFact.toS (R : String → STerm) (Ar : String → SArr) : IdxFact → SFact
  | .le rs b => .le (rs.map R) b
  | .ge r k => .ge (R r) k
  | .ale a b => .ale (Ar a) b
  | .w64 r => .w64 (R r)

theorem IdxFact.toS_holds {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    (R : String → STerm) (Ar : String → SArr) (f : IdxFact) :
    (f.toS R Ar).holds V A C O ↔
      f.holds (fun r => (R r).ev V A C O) (fun a => (Ar a).ev V A C O) := by
  cases f <;> simp [IdxFact.toS, IdxFact.holds, SFact.holds, tsum, Function.comp_def]

theorem tsum_append (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (xs ys : List STerm) : tsum V A C O (xs ++ ys) = tsum V A C O xs + tsum V A C O ys := by
  simp [tsum]

/-! ## 2. Entailment -/

/-- The value of an immediate at width `64`, and `0` for every other term: a lower bound on
    the value of the term. -/
def immLb : STerm → Nat
  | .immW w n => if w = 64 then n % 2 ^ 64 else 0
  | _ => 0

theorem immLb_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (t : STerm) : immLb t ≤ wval (t.ev V A C O) := by
  unfold immLb
  split
  · split
    · rename_i w n hw
      subst hw
      simp [wval, STerm.ev, castW]
    · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- The largest lower bound a list of facts states for the term `t`, and at least the value
    of `t` when it is an immediate at width `64` (`immLb`). -/
def lbOf : List SFact → STerm → Nat
  | [], t => immLb t
  | .ge t' k :: F, t => if t' = t then max k (lbOf F t) else lbOf F t
  | .le _ _ :: F, t => lbOf F t
  | .w64 _ :: F, t => lbOf F t
  | .ne _ _ :: F, t => lbOf F t
  | .ale _ _ :: F, t => lbOf F t

theorem lbOf_le {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool} :
    ∀ (F : List SFact) (t : STerm), (∀ f ∈ F, f.holds V A C O) →
      lbOf F t ≤ wval (t.ev V A C O)
  | [], t, _ => immLb_le V A C O t
  | .le _ _ :: F, t, h => lbOf_le F t (fun g hg => h g (List.mem_cons_of_mem _ hg))
  | .w64 _ :: F, t, h => lbOf_le F t (fun g hg => h g (List.mem_cons_of_mem _ hg))
  | .ne _ _ :: F, t, h => lbOf_le F t (fun g hg => h g (List.mem_cons_of_mem _ hg))
  | .ale _ _ :: F, t, h => lbOf_le F t (fun g hg => h g (List.mem_cons_of_mem _ hg))
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
    bounds them; every other term is an atom. It is one of the forms `linAlts` lists. -/
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
    simp only [show ("ADD" = "MULXHI") = False by decide, ite_false, applyOpnN,
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
    simp only [show ("SUB" = "MULXHI") = False by decide, ite_false, applyOpnN,
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
    · simp only [binW, show ("AND" = "MULXHI") = False by decide, ite_false, applyOpnN,
        Option.getD_some, BitVec.toNat_and]
      exact Nat.and_le_left
    · simp only [binW, show ("OR" = "MULXHI") = False by decide, ite_false, applyOpnN,
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
  | .ne _ _ => false
  | .ale _ _ => false

/-- The sums of a form of `P` and a form of `Q`. -/
def altsAdd (P Q : List (List STerm × Int)) : List (List STerm × Int) :=
  P.flatMap fun p => Q.map fun q => (p.1 ++ q.1, p.2 + q.2)

theorem mem_altsAdd {P Q : List (List STerm × Int)} {r : List STerm × Int} :
    r ∈ altsAdd P Q ↔ ∃ p ∈ P, ∃ q ∈ Q, r = (p.1 ++ q.1, p.2 + q.2) := by
  simp only [altsAdd, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩

/-- **The linear forms of a term**: every list of atoms and constant whose sum bounds the
    value of the term from above by the arms of `linOf`, where a subtraction of an immediate
    has both the form of `linOf` and the term itself as an atom. The forms of `linOf` are
    among them (`IdxInvCheckComplete.linOf_mem_linAlts`), and the list does not lose a form
    when facts are added (`IdxInvCheckComplete.linAlts_mono`). -/
def linAlts (F : List SFact) : STerm → List (List STerm × Int)
  | .immW w n => if w = 64 then [([], ((n % 2 ^ 64 : Nat) : Int))] else [([.immW w n], 0)]
  | .bin m x (.immW w k) =>
      if w = 64 ∧ m = "ADD" then (linAlts F x).map fun p => (p.1, p.2 + k)
      else if w = 64 ∧ m = "SUB" then
        if k ≤ lbOf F x then
          ([.bin m x (.immW w k)], 0) :: (linAlts F x).map fun p => (p.1, p.2 - k)
        else [([.bin m x (.immW w k)], 0)]
      else if m = "AND" then linAlts F x
      else [([.bin m x (.immW w k)], 0)]
  | .bin m x y =>
      if m = "AND" ∨ (m = "OR" ∧ x = y) then linAlts F x else [([.bin m x y], 0)]
  | t => [([t], 0)]

theorem linAlts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    ∀ p ∈ linAlts F t, (wval (t.ev V A C O) : Int) ≤ (tsum V A C O p.1 : Int) + p.2 := by
  fun_induction linAlts F t with
  | case1 n => simp [tsum, wval, STerm.ev, castW]
  | case2 => simp [tsum]
  | case3 m x w k h ih =>
      obtain ⟨rfl, rfl⟩ := h
      have := wval_add_le V A C O x k
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have := ih q hq
      dsimp only
      omega
  | case4 m x w k _ h hk ih =>
      obtain ⟨rfl, rfl⟩ := h
      have := wval_sub_le V A C O x k (le_trans hk (lbOf_le F x hF))
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [tsum]
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have := ih q hq
        dsimp only
        omega
  | case5 => simp [tsum]
  | case6 x w k _ _ ih =>
      have := wval_andOr_le V A C O (x := x) (y := .immW w k) (Or.inl rfl)
      intro p hp
      have := ih p hp
      omega
  | case7 => simp [tsum]
  | case8 m x y _ h ih =>
      have := wval_andOr_le V A C O h
      intro p hp
      have := ih p hp
      omega
  | case9 => simp [tsum]
  | case10 => simp [tsum]

/-- The linear forms of a sum of terms: the sums of a form of each term. -/
def sumAlts (F : List SFact) : List STerm → List (List STerm × Int)
  | [] => [([], 0)]
  | t :: ts => altsAdd (linAlts F t) (sumAlts F ts)

theorem sumAlts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ (ts : List STerm), ∀ p ∈ sumAlts F ts,
      (tsum V A C O ts : Int) ≤ (tsum V A C O p.1 : Int) + p.2
  | [] => by simp [tsum, sumAlts]
  | t :: ts => by
      intro r hr
      obtain ⟨p, hp, q, hq, rfl⟩ := mem_altsAdd.mp hr
      have h1 := linAlts_sound hF t p hp
      have h2 := sumAlts_sound hF ts q hq
      have e1 : tsum V A C O (t :: ts) = wval (t.ev V A C O) + tsum V A C O ts := by
        simp [tsum]
      simp only [tsum_append, e1, Nat.cast_add]
      omega

/-- The sum of the atoms of the linear form `p` plus its constant is at most `b'`: the form is
    a constant within the bound, or one fact bounds a sum containing its atoms. -/
def leForm (F : List SFact) (b' : Nat) (p : List STerm × Int) : Bool :=
  (decide (p.1 = []) && decide (p.2 ≤ b')) || F.any (leBy F p.1 p.2 b')

theorem leForm_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {p : List STerm × Int} {b' : Nat}
    (h : leForm F b' p = true) : (tsum V A C O p.1 : Int) + p.2 ≤ b' := by
  simp only [leForm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h with ⟨he, hk⟩ | ⟨f, hf, hl⟩
  · have h0 : tsum V A C O [] = 0 := rfl
    rw [he, h0]
    omega
  · cases f with
    | ge _ _ => simp [leBy] at hl
    | w64 _ => simp [leBy] at hl
    | ne _ _ => simp [leBy] at hl
    | ale _ _ => simp [leBy] at hl
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

/-- The sum of `ts` is at most `b'` by one of its linear forms (`sumAlts`, `leForm`). -/
def leLin (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  (sumAlts F ts).any (leForm F b')

theorem leLin_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {ts : List STerm} {b' : Nat}
    (h : leLin F ts b' = true) : tsum V A C O ts ≤ b' := by
  simp only [leLin, List.any_eq_true] at h
  obtain ⟨p, hp, hl⟩ := h
  have hs := sumAlts_sound hF ts p hp
  have := leForm_sound hF hl
  omega

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
    simp only [show ("MUL" = "MULXHI") = False by decide, ite_false, applyOpnN,
      Option.getD_some, BitVec.toNat_mul, BitVec.toNat_ofNat]
    exact mulImm_mod_le _ _
  · exact Nat.zero_le _

/-- A product with an immediate as the first factor and a second factor of width `64` is at
    most the product of the values. -/
theorem wval_immMul_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (y : STerm) (c : Nat) (hy : (y.ev V A C O).1 = 64) :
    wval ((STerm.bin "MUL" (.immW 64 c) y).ev V A C O) ≤ c * wval (y.ev V A C O) := by
  rw [wval_bin]
  simp only [STerm.ev, ite_true, binW, show ("MUL" = "MULXHI") = False by decide, ite_false,
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

/-- The linear form `p` is one atom `mulParts` reads as `c` times `x`, plus a constant
    `K ≤ b'`, and `x` is at most `(b' - K) / c` by `leLin`. -/
def mulForm (F : List SFact) (b' : Nat) (p : List STerm × Int) : Bool :=
  match p.1 with
  | [a] =>
      match mulParts F a with
      | some (c, x) => decide (p.2 ≤ b') && leLin F [x] (((b' : Int) - p.2).toNat / c)
      | none => false
  | _ => false

theorem mulForm_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {p : List STerm × Int} {b' : Nat}
    (h : mulForm F b' p = true) : (tsum V A C O p.1 : Int) + p.2 ≤ b' := by
  unfold mulForm at h
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
      rw [ha, e2]
      have h3 := mulLe_arith h.1 h2
      have h4 : ((wval (a.ev V A C O) : Nat) : Int) ≤ ((c * wval (x.ev V A C O) : Nat) : Int) :=
        Int.ofNat_le.mpr h1
      omega
    · cases h
  · cases h

/-- The sum of `ts` is at most `b'` by a product: one of its linear forms is a product with an
    immediate plus a constant (`mulForm`). -/
def mulLe (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  (sumAlts F ts).any (mulForm F b')

theorem mulLe_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {ts : List STerm} {b' : Nat}
    (h : mulLe F ts b' = true) : tsum V A C O ts ≤ b' := by
  simp only [mulLe, List.any_eq_true] at h
  obtain ⟨p, hp, hl⟩ := h
  have hs := sumAlts_sound hF ts p hp
  have := mulForm_sound hF hl
  omega

/-- The least upper bound the single-term facts `.le [t] b` of `F` state for the term `t`,
    when `F` has one. The value does not depend on the order of `F` and does not grow when
    facts are added (`IdxInvCheckComplete.ubOf_mono`). -/
def ubOf : List SFact → STerm → Option Nat
  | [], _ => none
  | .le [t'] b :: F, t => if t' = t then some (min b ((ubOf F t).getD b)) else ubOf F t
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
        have h0 := hF (.le [t'] b) List.mem_cons_self
        simp only [SFact.holds, tsum, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero] at h0
        cases hu : ubOf F t' with
        | none => simpa using h0
        | some v =>
            have := ubOf_sound F t' v (fun g hg => hF g (List.mem_cons_of_mem _ hg)) hu
            simpa using le_min h0 this
      · exact ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .le [] _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .le (_ :: _ :: _) _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .ge _ _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .w64 _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .ne _ _ :: F, t, u, hF, h =>
      ubOf_sound F t u (fun g hg => hF g (List.mem_cons_of_mem _ hg)) h
  | .ale _ _ :: F, t, u, hF, h =>
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
  · simp only [binW, show ("ADD" = "MULXHI") = False by decide, ite_false, applyOpnN,
      Option.getD_some, BitVec.toNat_add, extW_of_eq hy]
    unfold wval
    exact Nat.mod_le _ _
  · omega

/-- An atom `ADD x y` with `y` of width `64` as the linear forms `linOf` of `x` and `y`; every
    other atom is itself. It is one of the splittings `splitAlts` lists. -/
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

/-- The splittings of an atom: the atom itself, and for an atom `ADD x y` with `y` of width `64`
    the sums of a linear form of `x` and one of `y`. -/
def splitAlts (F : List SFact) : STerm → List (List STerm × Int)
  | .bin m x y =>
      if m = "ADD" ∧ widOk F y then ([.bin m x y], 0) :: altsAdd (linAlts F x) (linAlts F y)
      else [([.bin m x y], 0)]
  | t => [([t], 0)]

theorem splitAlts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    ∀ p ∈ splitAlts F t, (wval (t.ev V A C O) : Int) ≤ (tsum V A C O p.1 : Int) + p.2 := by
  unfold splitAlts
  split
  · rename_i m x y
    split
    · rename_i h
      obtain ⟨rfl, hw⟩ := h
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp [tsum]
      · obtain ⟨p, hp, q, hq, rfl⟩ := mem_altsAdd.mp hr
        have h0 := wval_addR_le V A C O x y (widOk_sound hF hw)
        have h1 := linAlts_sound hF x p hp
        have h2 := linAlts_sound hF y q hq
        simp only [tsum_append, Nat.cast_add]
        omega
    · simp [tsum]
  · simp [tsum]

/-- The splittings of a list of atoms: the sums of a splitting of each. -/
def splitsAlts (F : List SFact) : List STerm → List (List STerm × Int)
  | [] => [([], 0)]
  | t :: ts => altsAdd (splitAlts F t) (splitsAlts F ts)

theorem splitsAlts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ (ts : List STerm), ∀ p ∈ splitsAlts F ts,
      (tsum V A C O ts : Int) ≤ (tsum V A C O p.1 : Int) + p.2
  | [] => by simp [tsum, splitsAlts]
  | t :: ts => by
      intro r hr
      obtain ⟨p, hp, q, hq, rfl⟩ := mem_altsAdd.mp hr
      have h1 := splitAlts_sound hF t p hp
      have h2 := splitsAlts_sound hF ts q hq
      have e1 : tsum V A C O (t :: ts) = wval (t.ev V A C O) + tsum V A C O ts := by
        simp [tsum]
      simp only [tsum_append, e1, Nat.cast_add]
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
  | .ne _ _ => false
  | .ale _ _ => false

/-- The sum of `ts` is at most `b'` by a splitting of one of its linear forms, one fact for the
    atoms it contains and single-term facts for the others (an index `off + i` with a bound on
    `off` and a loop invariant on `i`). -/
def leMix (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  (sumAlts F ts).any fun p => (splitsAlts F p.1).any fun q => F.any (leMixBy F q.1 (p.2 + q.2) b')

theorem leMixBy_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {as : List STerm} {K : Int} {b' : Nat}
    {f : SFact} (hf : f ∈ F) (hl : leMixBy F as K b' f = true) :
    (tsum V A C O as : Int) + K ≤ b' := by
  cases f with
  | ge _ _ => simp [leMixBy] at hl
  | w64 _ => simp [leMixBy] at hl
  | ne _ _ => simp [leMixBy] at hl
  | ale _ _ => simp [leMixBy] at hl
  | le ts0 b =>
      simp only [leMixBy] at hl
      split at hl
      · rename_i u hu
        simp only [decide_eq_true_eq] at hl
        have h0 : tsum V A C O ts0 ≤ b := hF _ hf
        have h1 := peel_sum V A C O as ts0
        have h2 := lbSum_le hF (peel ts0 as).1
        have h3 := ubSum_sound hF _ u hu
        omega
      · cases hl

theorem leMix_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {ts : List STerm} {b' : Nat}
    (h : leMix F ts b' = true) : tsum V A C O ts ≤ b' := by
  simp only [leMix, List.any_eq_true] at h
  obtain ⟨p, hp, q, hq, f, hf, hl⟩ := h
  have h0 := sumAlts_sound hF ts p hp
  have h1 := splitsAlts_sound hF p.1 q hq
  have h2 := leMixBy_sound hF hf hl
  omega

/-- The value of an immediate at width `64`, and `2 ^ 64 - 1` for every other term: an upper
    bound on the value of the term. -/
def maskOf : STerm → Nat
  | .immW w n => if w = 64 then n % 2 ^ 64 else 2 ^ 64 - 1
  | _ => 2 ^ 64 - 1

theorem maskOf_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (t : STerm) : wval (t.ev V A C O) ≤ maskOf t := by
  have := wval_lt (t.ev V A C O)
  unfold maskOf
  split
  · split
    · rename_i w n hw
      subst hw
      simp [wval, STerm.ev, castW]
    · omega
  · omega

/-- An immediate operand `y` of a conjunction is at most `maskOf y` at width `64`. -/
theorem extW_maskOf_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (y : STerm) : (extW (y.ev V A C O) 64).toNat ≤ maskOf y := by
  have := (extW (y.ev V A C O) 64).isLt
  unfold maskOf
  split
  · split
    · rename_i w n hw
      subst hw
      simp [STerm.ev, extW_of_eq, castW]
    · omega
  · omega

/-- An upper bound on the value of a term by its structure: an immediate at width `64` is its
    value, and a conjunction `AND x y` is at most the bound of `x` and at most an immediate
    mask `y` (`maskOf`). -/
def immHi : STerm → Nat
  | .bin m x y => if m = "AND" then min (immHi x) (maskOf y) else 2 ^ 64 - 1
  | t => maskOf t

/-- A conjunction `AND x y` is at most the values of `x` and of `y` at width `64`. -/
theorem wval_and_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (x y : STerm) :
    wval ((STerm.bin "AND" x y).ev V A C O) ≤ wval (x.ev V A C O) ∧
      wval ((STerm.bin "AND" x y).ev V A C O) ≤ (extW (y.ev V A C O) 64).toNat := by
  rw [wval_bin]
  split
  · rename_i hw
    simp only [binW, show ("AND" = "MULXHI") = False by decide, ite_false, applyOpnN,
      Option.getD_some, BitVec.toNat_and]
    exact ⟨Nat.and_le_left, Nat.and_le_right⟩
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem immHi_le (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) :
    ∀ t : STerm, wval (t.ev V A C O) ≤ immHi t
  | .bin m x y => by
      have := wval_lt ((STerm.bin m x y).ev V A C O)
      simp only [immHi]
      split
      · rename_i hm
        subst hm
        have h1 := wval_and_le V A C O x y
        have h2 := immHi_le V A C O x
        have h3 := extW_maskOf_le V A C O y
        exact le_min (by omega) (by omega)
      · omega
  | .reg _ | .immW _ _ | .immAt _ _ | .un _ _ | .shImm _ _ _ | .aget _ _ _ _ | .cin _
  | .aluF _ _ _ _ _ | .carryW _ _ _ _ | .carryF _ _ _ _ _ | .mulx _ _ _ | .cout _ _ _ _
  | .sel _ _ _ | .setcc _ _ _ | .ref _ => by
      simp only [immHi]
      exact maskOf_le V A C O _

/-- The symbolic array a load term reads, and `none` for every other term. -/
def loadArr : STerm → Option SArr
  | .aget a _ _ _ => some a
  | _ => none

/-- A load from an array whose elements obey a bound obeys it. -/
theorem wval_load_le {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {t : STerm} {a : SArr} {b : Nat} (ht : loadArr t = some a) (h : ArrLe (a.ev V A C O) b) :
    wval (t.ev V A C O) ≤ b := by
  cases t <;> simp only [loadArr, reduceCtorEq, Option.some.injEq] at ht
  subst ht
  exact stackGet_castA_le h _ _ _

/-- An upper bound on the value of the term `t`: the least `b - lbSum F (ts.erase t)` over
    the facts `.le ts b` of `G` with `t ∈ ts`, the least bound `b` of the facts `.ale a b`
    of `G` on the array `a` that `t` loads from, and at most the bound `immHi t` of its
    structure. -/
def hiOf (F : List SFact) : List SFact → STerm → Nat
  | [], t => immHi t
  | .le ts b :: G, t =>
      if t ∈ ts then min (b - lbSum F (ts.erase t)) (hiOf F G t) else hiOf F G t
  | .ge _ _ :: G, t => hiOf F G t
  | .w64 _ :: G, t => hiOf F G t
  | .ne _ _ :: G, t => hiOf F G t
  | .ale a b :: G, t => if loadArr t = some a then min b (hiOf F G t) else hiOf F G t

theorem hiOf_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ (G : List SFact) (t : STerm), (∀ f ∈ G, f.holds V A C O) →
      wval (t.ev V A C O) ≤ hiOf F G t
  | [], t, _ => immHi_le V A C O t
  | .ge _ _ :: G, t, hG => hiOf_sound hF G t (fun g hg => hG g (List.mem_cons_of_mem _ hg))
  | .w64 _ :: G, t, hG => hiOf_sound hF G t (fun g hg => hG g (List.mem_cons_of_mem _ hg))
  | .ne _ _ :: G, t, hG => hiOf_sound hF G t (fun g hg => hG g (List.mem_cons_of_mem _ hg))
  | .ale a b :: G, t, hG => by
      have ih := hiOf_sound hF G t (fun g hg => hG g (List.mem_cons_of_mem _ hg))
      simp only [hiOf]
      split
      · rename_i ht
        exact le_min (wval_load_le ht (hG (.ale a b) List.mem_cons_self)) ih
      · exact ih
  | .le ts b :: G, t, hG => by
      have ih := hiOf_sound hF G t (fun g hg => hG g (List.mem_cons_of_mem _ hg))
      simp only [hiOf]
      split
      · rename_i ht
        have h0 : tsum V A C O ts ≤ b := hG (.le ts b) List.mem_cons_self
        have hp := ((List.perm_cons_erase ht).map fun t => wval (t.ev V A C O)).sum_eq
        have h1 := lbSum_le hF (ts.erase t)
        simp only [tsum, List.map_cons, List.sum_cons] at hp h0 h1
        exact le_min (by omega) ih
      · exact ih

/-- The value of an affine form: the sum of the coefficients times the values of the atoms. -/
def affEv (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) :
    List (STerm × Int) → Int
  | [] => 0
  | p :: L => p.2 * (wval (p.1.ev V A C O) : Int) + affEv V A C O L

/-- The affine form `L` plus the coefficient `p.2` on the atom `p.1`, merged into the entry of
    `p.1` when `L` has one. -/
def affAdd1 (p : STerm × Int) : List (STerm × Int) → List (STerm × Int)
  | [] => [p]
  | q :: L => if q.1 = p.1 then (q.1, q.2 + p.2) :: L else q :: affAdd1 p L

theorem affEv_add1 (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (p : STerm × Int) :
    ∀ L, affEv V A C O (affAdd1 p L) = p.2 * (wval (p.1.ev V A C O) : Int) + affEv V A C O L
  | [] => by simp [affAdd1, affEv]
  | q :: L => by
      simp only [affAdd1]
      split
      · rename_i h
        rw [← h]
        simp only [affEv]
        ring
      · simp only [affEv, affEv_add1 V A C O p L]
        ring

/-- The sum of two affine forms, with the coefficients of a common atom merged. -/
def affAdd : List (STerm × Int) → List (STerm × Int) → List (STerm × Int)
  | [], M => M
  | p :: L, M => affAdd1 p (affAdd L M)

theorem affEv_add (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) :
    ∀ L M, affEv V A C O (affAdd L M) = affEv V A C O L + affEv V A C O M
  | [], M => by simp [affAdd, affEv]
  | p :: L, M => by
      simp only [affAdd, affEv_add1, affEv, affEv_add V A C O L M]
      ring

/-- An affine form times the integer `c`. -/
def affScale (c : Int) (L : List (STerm × Int)) : List (STerm × Int) :=
  L.map fun p => (p.1, c * p.2)

theorem affEv_scale (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (c : Int) : ∀ L, affEv V A C O (affScale c L) = c * affEv V A C O L
  | [] => by simp [affScale, affEv]
  | p :: L => by
      have := affEv_scale V A C O c L
      simp only [affScale, List.map_cons, affEv] at this ⊢
      rw [this]
      ring

/-- An upper bound on the value of an affine form: an atom with a non-negative coefficient at
    its upper bound `hiOf`, one with a negative coefficient at its lower bound `lbOf`. -/
def affHi (F : List SFact) : List (STerm × Int) → Int
  | [] => 0
  | p :: L =>
      (if 0 ≤ p.2 then p.2 * (hiOf F F p.1 : Int) else p.2 * (lbOf F p.1 : Int)) + affHi F L

/-- A lower bound on the value of an affine form: an atom with a non-negative coefficient at
    its lower bound `lbOf`, one with a negative coefficient at its upper bound `hiOf`. -/
def affLo (F : List SFact) : List (STerm × Int) → Int
  | [] => 0
  | p :: L =>
      (if 0 ≤ p.2 then p.2 * (lbOf F p.1 : Int) else p.2 * (hiOf F F p.1 : Int)) + affLo F L

theorem affHi_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ L, affEv V A C O L ≤ affHi F L
  | [] => by simp [affEv, affHi]
  | p :: L => by
      have ih := affHi_sound hF L
      have hh : ((wval (p.1.ev V A C O) : Nat) : Int) ≤ (hiOf F F p.1 : Int) :=
        Int.ofNat_le.mpr (hiOf_sound hF F p.1 hF)
      have hl : ((lbOf F p.1 : Nat) : Int) ≤ (wval (p.1.ev V A C O) : Int) :=
        Int.ofNat_le.mpr (lbOf_le F p.1 hF)
      simp only [affEv, affHi]
      split
      · rename_i hc
        have := Int.mul_le_mul_of_nonneg_left hh hc
        omega
      · rename_i hc
        have := Int.mul_le_mul_of_nonpos_left (by omega : p.2 ≤ 0) hl
        omega

theorem affLo_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ L, affLo F L ≤ affEv V A C O L
  | [] => by simp [affEv, affLo]
  | p :: L => by
      have ih := affLo_sound hF L
      have hh : ((wval (p.1.ev V A C O) : Nat) : Int) ≤ (hiOf F F p.1 : Int) :=
        Int.ofNat_le.mpr (hiOf_sound hF F p.1 hF)
      have hl : ((lbOf F p.1 : Nat) : Int) ≤ (wval (p.1.ev V A C O) : Int) :=
        Int.ofNat_le.mpr (lbOf_le F p.1 hF)
      simp only [affEv, affLo]
      split
      · rename_i hc
        have := Int.mul_le_mul_of_nonneg_left hl hc
        omega
      · rename_i hc
        have := Int.mul_le_mul_of_nonpos_left (by omega : p.2 ≤ 0) hh
        omega

/-- The operation `m` on two terms of width `64` at width `64`. -/
theorem wval_bin64 (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (m : String) (x y : STerm) (hx : (x.ev V A C O).1 = 64) (hy : (y.ev V A C O).1 = 64) :
    wval ((STerm.bin m x y).ev V A C O) =
      (binW 64 m (castW (x.ev V A C O) 64) (castW (y.ev V A C O) 64)).toNat := by
  rw [wval_bin, ite_eq_left hx, extW_of_eq hy]

/-- A product `MUL x y` of two terms of width `64` whose affine forms bound the product of
    their values below `2 ^ 64` is the product of the values. -/
theorem affEv_mulW {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {x y : STerm}
    {Lx Ly : List (STerm × Int)} {Kx Ky : Int} (hw : widOk F x = true ∧ widOk F y = true)
    (hlt : (affHi F Lx + Kx) * (affHi F Ly + Ky) < 2 ^ 64)
    (ihx : (wval (x.ev V A C O) : Int) = affEv V A C O Lx + Kx)
    (ihy : (wval (y.ev V A C O) : Int) = affEv V A C O Ly + Ky) :
    (wval ((STerm.bin "MUL" x y).ev V A C O) : Int) =
      (wval (x.ev V A C O) : Int) * wval (y.ev V A C O) := by
  have bx := affHi_sound hF Lx
  have bY := affHi_sound hF Ly
  rw [wval_bin64 V A C O _ x y (widOk_sound hF hw.1) (widOk_sound hF hw.2)]
  simp only [binW, show ("MUL" = "MULXHI") = False by decide, ite_false, applyOpnN,
    Option.getD_some, BitVec.toNat_mul]
  change (((wval (x.ev V A C O) * wval (y.ev V A C O)) % 2 ^ 64 : Nat) : Int) = _
  have hm : (wval (x.ev V A C O) : Int) * wval (y.ev V A C O) < 2 ^ 64 :=
    lt_of_le_of_lt (Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)) hlt
  have hm' : wval (x.ev V A C O) * wval (y.ev V A C O) < 2 ^ 64 := by exact_mod_cast hm
  rw [Nat.mod_eq_of_lt hm']
  push_cast
  rfl

/-- **The affine form of a term**: atoms with integer coefficients and a constant whose sum is
    the value of the term. An immediate at width `64` is a constant; a sum `ADD`, a difference
    `SUB` and a product `MUL` with one constant factor, of two terms of width `64` (`widOk`),
    combine the forms of their operands when the bounds `affHi`, `affLo` of the forms exclude
    a wrap-around at width `64`; every other term is an atom with coefficient `1`. It is one of
    the forms `affAlts` lists. -/
def affOf (F : List SFact) : STerm → List (STerm × Int) × Int
  | .immW w n => if w = 64 then ([], ((n % 2 ^ 64 : Nat) : Int)) else ([(.immW w n, 1)], 0)
  | .bin m x y =>
      if widOk F x ∧ widOk F y then
        if m = "ADD" ∧ affHi F (affOf F x).1 + (affOf F x).2 +
            (affHi F (affOf F y).1 + (affOf F y).2) < 2 ^ 64 then
          (affAdd (affOf F x).1 (affOf F y).1, (affOf F x).2 + (affOf F y).2)
        else if m = "SUB" ∧ 0 ≤ affLo F (affAdd (affOf F x).1 (affScale (-1) (affOf F y).1)) +
            ((affOf F x).2 - (affOf F y).2) then
          (affAdd (affOf F x).1 (affScale (-1) (affOf F y).1), (affOf F x).2 - (affOf F y).2)
        else if m = "MUL" ∧ (affHi F (affOf F x).1 + (affOf F x).2) *
            (affHi F (affOf F y).1 + (affOf F y).2) < 2 ^ 64 then
          if (affOf F y).1 = [] then
            (affScale (affOf F y).2 (affOf F x).1, (affOf F x).2 * (affOf F y).2)
          else if (affOf F x).1 = [] then
            (affScale (affOf F x).2 (affOf F y).1, (affOf F x).2 * (affOf F y).2)
          else ([(.bin m x y, 1)], 0)
        else ([(.bin m x y, 1)], 0)
      else ([(.bin m x y, 1)], 0)
  | t => ([(t, 1)], 0)

theorem affOf_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    (wval (t.ev V A C O) : Int) = affEv V A C O (affOf F t).1 + (affOf F t).2 := by
  fun_induction affOf F t with
  | case1 n => simp [affEv, wval, STerm.ev, castW]
  | case3 m x y hw h ihx ihy =>
      obtain ⟨rfl, hlt⟩ := h
      have bx := affHi_sound hF (affOf F x).1
      have bY := affHi_sound hF (affOf F y).1
      rw [wval_bin64 V A C O _ x y (widOk_sound hF hw.1) (widOk_sound hF hw.2)]
      simp only [binW, show ("ADD" = "MULXHI") = False by decide, ite_false, applyOpnN,
        Option.getD_some, BitVec.toNat_add]
      change (((wval (x.ev V A C O) + wval (y.ev V A C O)) % 2 ^ 64 : Nat) : Int) = _
      rw [Nat.mod_eq_of_lt (by omega), affEv_add]
      push_cast
      omega
  | case4 m x y hw _ h ihx ihy =>
      obtain ⟨rfl, hle⟩ := h
      have bl := affLo_sound hF (affAdd (affOf F x).1 (affScale (-1) (affOf F y).1))
      rw [affEv_add, affEv_scale] at bl
      rw [wval_bin64 V A C O _ x y (widOk_sound hF hw.1) (widOk_sound hF hw.2)]
      simp only [binW, show ("SUB" = "MULXHI") = False by decide, ite_false, applyOpnN,
        Option.getD_some]
      have hyx : wval (y.ev V A C O) ≤ wval (x.ev V A C O) := by omega
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hyx)]
      change ((wval (x.ev V A C O) - wval (y.ev V A C O) : Nat) : Int) = _
      rw [affEv_add, affEv_scale]
      omega
  | case5 m x y hw _ _ h hy ihx ihy =>
      obtain ⟨rfl, hlt⟩ := h
      rw [affEv_mulW hF hw hlt ihx ihy, affEv_scale, ihx, ihy, hy]
      simp only [affEv]
      ring
  | case6 m x y hw _ _ h _ hx ihx ihy =>
      obtain ⟨rfl, hlt⟩ := h
      rw [affEv_mulW hF hw hlt ihx ihy, affEv_scale, ihx, ihy, hx]
      simp only [affEv]
      ring
  | _ => simp [affEv]

/-- A product `MUL x y` of two terms of width `64` whose affine forms bound the values by
    numbers whose non-negative parts have a product below `2 ^ 64` is the product of the
    values. -/
theorem affEv_mulW_max {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {x y : STerm}
    {Lx Ly : List (STerm × Int)} {Kx Ky : Int} (hw : widOk F x = true ∧ widOk F y = true)
    (hlt : max 0 (affHi F Lx + Kx) * max 0 (affHi F Ly + Ky) < 2 ^ 64)
    (ihx : (wval (x.ev V A C O) : Int) = affEv V A C O Lx + Kx)
    (ihy : (wval (y.ev V A C O) : Int) = affEv V A C O Ly + Ky) :
    (wval ((STerm.bin "MUL" x y).ev V A C O) : Int) =
      (wval (x.ev V A C O) : Int) * wval (y.ev V A C O) := by
  have bx := affHi_sound hF Lx
  have bY := affHi_sound hF Ly
  rw [wval_bin64 V A C O _ x y (widOk_sound hF hw.1) (widOk_sound hF hw.2)]
  simp only [binW, show ("MUL" = "MULXHI") = False by decide, ite_false, applyOpnN,
    Option.getD_some, BitVec.toNat_mul]
  change (((wval (x.ev V A C O) * wval (y.ev V A C O)) % 2 ^ 64 : Nat) : Int) = _
  have hm : (wval (x.ev V A C O) : Int) * wval (y.ev V A C O) < 2 ^ 64 :=
    lt_of_le_of_lt (Int.mul_le_mul (le_max_of_le_right (by omega)) (le_max_of_le_right
      (by omega)) (by omega) (le_max_left _ _)) hlt
  have hm' : wval (x.ev V A C O) * wval (y.ev V A C O) < 2 ^ 64 := by exact_mod_cast hm
  rw [Nat.mod_eq_of_lt hm']
  push_cast
  rfl

/-- The affine form of `m x y` from the forms `L` of `x` and `M` of `y`, when the bounds
    `affHi`, `affLo` of the forms exclude a wrap-around at width `64`: their sum for `ADD`,
    their difference for `SUB`, and for `MUL` the scaling of one by the constant of the other
    when that other has no atom. -/
def affComb (F : List SFact) (m : String) (L M : List (STerm × Int) × Int) :
    Option (List (STerm × Int) × Int) :=
  if m = "ADD" then
    if affHi F L.1 + L.2 + (affHi F M.1 + M.2) < 2 ^ 64 then some (affAdd L.1 M.1, L.2 + M.2)
    else none
  else if m = "SUB" then
    if 0 ≤ affLo F (affAdd L.1 (affScale (-1) M.1)) + (L.2 - M.2) then
      some (affAdd L.1 (affScale (-1) M.1), L.2 - M.2)
    else none
  else if m = "MUL" then
    if max 0 (affHi F L.1 + L.2) * max 0 (affHi F M.1 + M.2) < 2 ^ 64 then
      if M.1 = [] then some (affScale M.2 L.1, L.2 * M.2)
      else if L.1 = [] then some (affScale L.2 M.1, L.2 * M.2)
      else none
    else none
  else none

theorem affComb_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {m : String} {x y : STerm}
    {L M r : List (STerm × Int) × Int} (hw : widOk F x = true ∧ widOk F y = true)
    (ihx : (wval (x.ev V A C O) : Int) = affEv V A C O L.1 + L.2)
    (ihy : (wval (y.ev V A C O) : Int) = affEv V A C O M.1 + M.2)
    (h : affComb F m L M = some r) :
    (wval ((STerm.bin m x y).ev V A C O) : Int) = affEv V A C O r.1 + r.2 := by
  unfold affComb at h
  split at h
  · rename_i hm
    subst hm
    split at h
    · rename_i hlt
      cases h
      have bx := affHi_sound hF L.1
      have bY := affHi_sound hF M.1
      rw [wval_bin64 V A C O _ x y (widOk_sound hF hw.1) (widOk_sound hF hw.2)]
      simp only [binW, show ("ADD" = "MULXHI") = False by decide, ite_false, applyOpnN,
        Option.getD_some, BitVec.toNat_add]
      change (((wval (x.ev V A C O) + wval (y.ev V A C O)) % 2 ^ 64 : Nat) : Int) = _
      rw [Nat.mod_eq_of_lt (by omega), affEv_add]
      push_cast
      omega
    · cases h
  · split at h
    · rename_i _ hm
      subst hm
      split at h
      · rename_i hle
        cases h
        have bl := affLo_sound hF (affAdd L.1 (affScale (-1) M.1))
        rw [affEv_add, affEv_scale] at bl
        rw [wval_bin64 V A C O _ x y (widOk_sound hF hw.1) (widOk_sound hF hw.2)]
        simp only [binW, show ("SUB" = "MULXHI") = False by decide, ite_false, applyOpnN,
          Option.getD_some]
        have hyx : wval (y.ev V A C O) ≤ wval (x.ev V A C O) := by omega
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hyx)]
        change ((wval (x.ev V A C O) - wval (y.ev V A C O) : Nat) : Int) = _
        rw [affEv_add, affEv_scale]
        omega
      · cases h
    · split at h
      · rename_i _ _ hm
        subst hm
        split at h
        · rename_i hlt
          have hmul := affEv_mulW_max hF hw hlt ihx ihy
          split at h
          · rename_i hy
            cases h
            rw [hmul, affEv_scale, ihx, ihy, hy]
            simp only [affEv]
            ring
          · split at h
            · rename_i hx
              cases h
              rw [hmul, affEv_scale, ihx, ihy, hx]
              simp only [affEv]
              ring
            · cases h
        · cases h
      · cases h

/-- **The affine forms of a term**: lists of atoms with integer coefficients and a constant
    whose sum is the value of the term. An immediate at width `64` is a constant; an
    operation on two terms of width `64` (`widOk`) is an atom with coefficient `1`, and the
    combination `affComb` of a form of each operand; every other term is an atom with
    coefficient `1`. The form of `affOf` is among them
    (`IdxInvCheckComplete.affOf_mem_affAlts`), and the list does not lose a form when facts
    are added (`IdxInvCheckComplete.affAlts_mono`). -/
def affAlts (F : List SFact) : STerm → List (List (STerm × Int) × Int)
  | .immW w n => if w = 64 then [([], ((n % 2 ^ 64 : Nat) : Int))] else [([(.immW w n, 1)], 0)]
  | .bin m x y =>
      if widOk F x ∧ widOk F y then
        ([(.bin m x y, 1)], 0) ::
          (affAlts F x).flatMap fun L => (affAlts F y).filterMap (affComb F m L)
      else [([(.bin m x y, 1)], 0)]
  | t => [([(t, 1)], 0)]

theorem affAlts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    ∀ p ∈ affAlts F t, (wval (t.ev V A C O) : Int) = affEv V A C O p.1 + p.2 := by
  fun_induction affAlts F t with
  | case1 n => simp [affEv, wval, STerm.ev, castW]
  | case3 m x y hw ihy ihx =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp [affEv]
      · simp only [List.mem_flatMap, List.mem_filterMap] at hr
        obtain ⟨L, hL, M, hM, hc⟩ := hr
        exact affComb_sound hF hw (ihx L hL) (ihy M hM) hc
  | _ => simp [affEv]

/-- The index term `t` is at most `b'` by the upper bound `affHi` of one of its affine
    forms. -/
def affLe (F : List SFact) (t : STerm) (b' : Nat) : Bool :=
  (affAlts F t).any fun p => decide (affHi F p.1 + p.2 ≤ b')

theorem affLe_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {t : STerm} {b' : Nat}
    (h : affLe F t b' = true) : wval (t.ev V A C O) ≤ b' := by
  simp only [affLe, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp, hl⟩ := h
  have h1 := affAlts_sound hF t p hp
  have h2 := affHi_sound hF p.1
  omega

/-- The sum of the bounds `hiOf` of a list of terms bounds the sum of their values. -/
theorem tsum_le_hiOf {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ ts : List STerm, tsum V A C O ts ≤ (ts.map (hiOf F F)).sum
  | [] => by simp [tsum]
  | t :: ts => by
      have h1 := hiOf_sound hF F t hF
      have h2 := tsum_le_hiOf hF ts
      simp only [tsum, List.map_cons, List.sum_cons] at h2 ⊢
      omega

/-- The bounds `hiOf` of the atoms of the linear form `p` plus its constant. -/
def formHi (F : List SFact) (p : List STerm × Int) : Nat :=
  (((p.1.map (hiOf F F)).sum : Int) + p.2).toNat

/-- An upper bound on the value of the term `t`: the least of the bound `hiOf` of `t` and the
    bounds `formHi` of its linear forms `linAlts`. -/
def termHi (F : List SFact) (t : STerm) : Nat :=
  (linAlts F t).foldr (fun p u => min (formHi F p) u) (hiOf F F t)

theorem termHi_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    wval (t.ev V A C O) ≤ termHi F t := by
  have key : ∀ P : List (List STerm × Int), (∀ p ∈ P,
      (wval (t.ev V A C O) : Int) ≤ (tsum V A C O p.1 : Int) + p.2) →
      wval (t.ev V A C O) ≤ P.foldr (fun p u => min (formHi F p) u) (hiOf F F t) := by
    intro P
    induction P with
    | nil => intro _; exact hiOf_sound hF F t hF
    | cons p P ih =>
        intro hP
        have h1 := hP p List.mem_cons_self
        have h2 := ih fun q hq => hP q (List.mem_cons_of_mem _ hq)
        have h3 := tsum_le_hiOf hF p.1
        have e : formHi F p = (((p.1.map (hiOf F F)).sum : Int) + p.2).toNat := rfl
        rw [List.foldr_cons, e]
        omega
  exact key _ (linAlts_sound hF t)

/-- The upper bound `termHi` of `t`, less one when a fact of `F` excludes the bound. -/
def hiNe (F : List SFact) (t : STerm) : Nat :=
  if SFact.ne t (termHi F t) ∈ F then termHi F t - 1 else termHi F t

theorem hiNe_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    wval (t.ev V A C O) ≤ hiNe F t := by
  have h1 := termHi_sound hF t
  unfold hiNe
  split
  · rename_i hm
    have h2 : wval (t.ev V A C O) ≠ termHi F t := hF _ hm
    omega
  · exact h1

/-- The lower bound `lbOf` of `t`, plus one when a fact of `F` excludes the bound. -/
def lbNe (F : List SFact) (t : STerm) : Nat :=
  if SFact.ne t (lbOf F t) ∈ F then lbOf F t + 1 else lbOf F t

theorem lbNe_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) (t : STerm) :
    lbNe F t ≤ wval (t.ev V A C O) := by
  have h1 := lbOf_le F t hF
  unfold lbNe
  split
  · rename_i hm
    have h2 : wval (t.ev V A C O) ≠ lbOf F t := hF _ hm
    omega
  · exact h1

/-- The sum of `ts` is at most `b'` by the sum of the upper bounds `hiNe` of its terms. -/
def hiLe (F : List SFact) (ts : List STerm) (b' : Nat) : Bool :=
  decide ((ts.map (hiNe F)).sum ≤ b')

theorem hiLe_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {ts : List STerm} {b' : Nat}
    (h : hiLe F ts b' = true) : tsum V A C O ts ≤ b' := by
  simp only [hiLe, decide_eq_true_eq] at h
  have key : ∀ ts : List STerm, tsum V A C O ts ≤ (ts.map (hiNe F)).sum := by
    intro ts
    induction ts with
    | nil => simp [tsum]
    | cons t ts ih =>
        have := hiNe_sound hF t
        simp only [tsum, List.map_cons, List.sum_cons] at ih ⊢
        omega
  exact (key ts).trans h

/-- A fact of `F` bounds the elements of the symbolic array `a` by at most `b`. -/
def arrIn (F : List SFact) (a : SArr) (b : Nat) : Bool :=
  F.any fun
    | .ale a' b' => decide (a' = a) && decide (b' ≤ b)
    | _ => false

theorem arrIn_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {a : SArr} {b : Nat}
    (h : arrIn F a b = true) : ArrLe (a.ev V A C O) b := by
  simp only [arrIn, List.any_eq_true] at h
  obtain ⟨g, hg, hb⟩ := h
  cases g with
  | ale a' b' =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨rfl, hb⟩ := hb
      exact (hF _ hg : ArrLe _ b').mono hb
  | le _ _ | ge _ _ | w64 _ | ne _ _ => simp at hb

/-- Every element of the symbolic array `a` is at most `b`: a fact of `F` states it
    (`arrIn`), or `a` sets one element of an array that obeys the bound to a word whose
    upper bound `hiNe` is within it, or `a` is the zero array. -/
def arrOk (F : List SFact) (b : Nat) : SArr → Bool
  | .cell r => arrIn F (.cell r) b
  | .zero _ _ => true
  | .aset a w n i v => arrIn F (.aset a w n i v) b || (arrOk F b a && decide (hiNe F v ≤ b))

theorem arrOk_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) {b : Nat} :
    ∀ a : SArr, arrOk F b a = true → ArrLe (a.ev V A C O) b
  | .cell r, h => arrIn_sound hF h
  | .zero w n, _ => fun _ => by
      show wval ⟨w, 0⟩ ≤ b
      simp only [wval, castW]
      split <;> rename_i h <;> [subst h; skip] <;> simp
  | .aset a w n i v, h => by
      simp only [arrOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨ha, hv⟩
      · exact arrIn_sound hF h
      · exact arrLe_stackSet (arrOk_sound hF a ha) w n _ _ ((hiNe_sound hF v).trans hv)

/-- **Entailment**: an upper bound on a sum holds when its linear form is a constant within
    the bound, when one fact bounds a sum containing its atoms (`leLin`), when the form is a
    product with an immediate whose other factor is bounded (`mulLe`), or when the upper
    bounds `hiNe` of its terms sum to within the bound (`hiLe`); a lower bound holds by
    `lbNe`; a width holds by `widOk`; a value `c` is excluded when it lies outside the bounds
    of the term or a fact excludes it; a bound on the elements of an array holds by
    `arrOk`. -/
def entails (F : List SFact) : SFact → Bool
  | .le ts b' => leLin F ts b' || mulLe F ts b' || hiLe F ts b'
  | .ge t k => decide (k ≤ lbNe F t)
  | .w64 t => widOk F t
  | .ne t c => decide (c < lbOf F t) || decide (hiNe F t < c) || decide (SFact.ne t c ∈ F)
  | .ale a b => arrOk F b a

/-- **Entailment is sound.** -/
theorem entails_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} (hF : ∀ f ∈ F, f.holds V A C O) :
    ∀ g : SFact, entails F g = true → g.holds V A C O
  | .ge t k, h => by
      simp only [entails, decide_eq_true_eq] at h
      exact le_trans h (lbNe_sound hF t)
  | .le ts b', h => by
      simp only [entails, Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact leLin_sound hF h
      · exact mulLe_sound hF h
      · exact hiLe_sound hF h
  | .w64 t, h => widOk_sound hF h
  | .ne t c, h => by
      simp only [entails, Bool.or_eq_true, decide_eq_true_eq] at h
      have h1 := lbOf_le F t hF
      have h2 := hiNe_sound hF t
      rcases h with (h | h) | h
      · show wval (t.ev V A C O) ≠ c
        omega
      · show wval (t.ev V A C O) ≠ c
        omega
      · exact hF _ h
  | .ale a b, h => arrOk_sound hF a h

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

/-! ## 2a. Thresholds of upper bounds

The entailment of an upper bound `.le ts b` holds exactly from a threshold on `b` on: each of
its readers `leLin`, `mulLe` and `hiLe` compares a value computed from `F` and `ts` with `b`.
`entLeThr` computes the least such value, so the bounds `b` of the facts with the same terms
are decided by one computation (`entails_le_thr`). -/

/-- An optional threshold at a bound: `some v` passes the bounds of at least `v`, `none`
    passes no bound. -/
def thrOk : Option Int → Nat → Bool
  | some v, b => decide (v ≤ (b : Int))
  | none, _ => false

/-- The lesser of two optional thresholds, `none` the greatest. -/
def thrMin : Option Int → Option Int → Option Int
  | some v, some w => some (min v w)
  | some v, none => some v
  | none, o => o

theorem thrOk_thrMin (o o' : Option Int) (b : Nat) :
    thrOk (thrMin o o') b = (thrOk o b || thrOk o' b) := by
  cases o <;> cases o' <;> simp only [thrOk, thrMin, Bool.or_false, Bool.false_or]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  omega

/-- The least of the thresholds `g x` over the members `x` of a list. -/
def thrAny {α : Type} (g : α → Option Int) (l : List α) : Option Int :=
  l.foldr (fun x o => thrMin (g x) o) none

theorem thrOk_thrAny {α : Type} (g : α → Option Int) (b : Nat) :
    ∀ l : List α, thrOk (thrAny g l) b = l.any fun x => thrOk (g x) b
  | [] => rfl
  | x :: l => by
      rw [thrAny, List.foldr_cons, thrOk_thrMin, List.any_cons, ← thrOk_thrAny g b l]
      rfl

/-- The threshold of `leBy`: the bound of an upper-bound fact on a sum containing the atoms
    `as`, less the lower bounds of the other terms, plus `K`. -/
def leByThr (F : List SFact) (as : List STerm) (K : Int) : SFact → Option Int
  | .le ts b =>
      match eraseAll ts as with
      | some R => some ((b : Int) - (lbSum F R : Int) + K)
      | none => none
  | .ge _ _ => none
  | .w64 _ => none
  | .ne _ _ => none
  | .ale _ _ => none

theorem thrOk_leByThr (F : List SFact) (as : List STerm) (K : Int) (b' : Nat) (f : SFact) :
    thrOk (leByThr F as K f) b' = leBy F as K b' f := by
  cases f with
  | le ts b =>
      simp only [leByThr, leBy]
      split <;> rfl
  | _ => rfl

/-- The threshold of `leForm`: the constant of a form without atoms, and the thresholds
    `leByThr` of the facts. -/
def leFormThr (F : List SFact) (p : List STerm × Int) : Option Int :=
  thrMin (if p.1 = [] then some p.2 else none) (thrAny (leByThr F p.1 p.2) F)

theorem thrOk_leFormThr (F : List SFact) (b' : Nat) (p : List STerm × Int) :
    thrOk (leFormThr F p) b' = leForm F b' p := by
  rw [leFormThr, thrOk_thrMin, thrOk_thrAny, leForm]
  congr 1
  · by_cases h : p.1 = [] <;> simp [h, thrOk]
  · simp only [thrOk_leByThr]

/-- The threshold of `leLin`: the least threshold `leFormThr` of the linear forms. -/
def leLinThr (F : List SFact) (ts : List STerm) : Option Int :=
  thrAny (leFormThr F) (sumAlts F ts)

theorem thrOk_leLinThr (F : List SFact) (ts : List STerm) (b' : Nat) :
    thrOk (leLinThr F ts) b' = leLin F ts b' := by
  rw [leLinThr, thrOk_thrAny, leLin]
  simp only [thrOk_leFormThr]

/-- The threshold of `mulForm`: for a form `c * x + K` with `x` from the threshold `v` of
    `leLin` on, the bounds from `K + v * c` on (from `K` on when `c = 0` and `v ≤ 0`). -/
def mulFormThr (F : List SFact) (p : List STerm × Int) : Option Int :=
  match p.1 with
  | [a] =>
      match mulParts F a with
      | some (c, x) =>
          match leLinThr F [x] with
          | some v =>
              if c = 0 then (if v ≤ 0 then some p.2 else none)
              else some (p.2 + ((v.toNat * c : Nat) : Int))
          | none => none
      | none => none
  | _ => none

theorem thrOk_mulFormThr (F : List SFact) (b' : Nat) (p : List STerm × Int) :
    thrOk (mulFormThr F p) b' = mulForm F b' p := by
  unfold mulFormThr mulForm
  split
  · split
    · rename_i c x _
      rw [← thrOk_leLinThr]
      cases leLinThr F [x] with
      | none => simp [thrOk]
      | some v =>
          dsimp only
          rw [Bool.eq_iff_iff]
          by_cases hc : c = 0
          · subst hc
            by_cases hv : v ≤ 0 <;> simp [hv, thrOk]
          · simp only [hc, ite_false, thrOk, Bool.and_eq_true, decide_eq_true_eq]
            have hc' : 0 < c := Nat.pos_of_ne_zero hc
            constructor
            · intro h
              refine ⟨by omega, ?_⟩
              have h1 : v.toNat * c ≤ ((b' : Int) - p.2).toNat := by omega
              have h2 := (Nat.le_div_iff_mul_le hc').mpr h1
              omega
            · rintro ⟨h0, h1⟩
              have h2 : v.toNat ≤ ((b' : Int) - p.2).toNat / c := by
                generalize ((b' : Int) - p.2).toNat / c = m at h1 ⊢
                omega
              have h3 := (Nat.le_div_iff_mul_le hc').mp h2
              omega
    · rfl
  · rfl

/-- The threshold of `mulLe`: the least threshold `mulFormThr` of the linear forms. -/
def mulLeThr (F : List SFact) (ts : List STerm) : Option Int :=
  thrAny (mulFormThr F) (sumAlts F ts)

theorem thrOk_mulLeThr (F : List SFact) (ts : List STerm) (b' : Nat) :
    thrOk (mulLeThr F ts) b' = mulLe F ts b' := by
  rw [mulLeThr, thrOk_thrAny, mulLe]
  simp only [thrOk_mulFormThr]

/-- **The threshold of an upper bound** on the sum of `ts` under the facts `F`: the least of
    the thresholds of `leLin`, `mulLe` and `hiLe`. -/
def entLeThr (F : List SFact) (ts : List STerm) : Option Int :=
  thrMin (leLinThr F ts) (thrMin (mulLeThr F ts) (some ((ts.map (hiNe F)).sum : Int)))

/-- **The entailment of an upper bound is its threshold.** -/
theorem entails_le_thr (F : List SFact) (ts : List STerm) (b : Nat) :
    entails F (.le ts b) = thrOk (entLeThr F ts) b := by
  rw [entLeThr, thrOk_thrMin, thrOk_thrMin, thrOk_leLinThr, thrOk_mulLeThr, entails,
    Bool.or_assoc]
  simp only [thrOk, hiLe]
  congr 2
  exact decide_eq_decide.mpr Int.ofNat_le.symm

/-- The register lists of the upper-bound facts of `fs`, without repetition. -/
def leKeys (fs : List IdxFact) : List (List String) :=
  (fs.filterMap fun
    | .le rs _ => some rs
    | _ => none).eraseDups

/-- The thresholds `entLeThr` of the register lists `ks` read through `R`, under `F`. -/
def thrTab (F : List SFact) (R : String → STerm) (ks : List (List String)) :
    List (List String × Option Int) :=
  ks.map fun rs => (rs, entLeThr F (rs.map R))

theorem lookup_thrTab {F : List SFact} {R : String → STerm} {rs : List String}
    {o : Option Int} : ∀ {ks : List (List String)}, (thrTab F R ks).lookup rs = some o →
      o = entLeThr F (rs.map R)
  | [], h => by simp [thrTab] at h
  | k :: ks, h => by
      simp only [thrTab, List.map_cons, List.lookup_cons] at h
      split at h
      · rename_i hk
        rw [beq_iff_eq] at hk
        subst hk
        exact (Option.some.inj h).symm
      · exact lookup_thrTab h

/-- The entailment of the fact `f` read through `R` and `Ar` from `F`, an upper bound
    decided by its threshold in the table `tab` when the table has its register list. -/
def entailsT (F : List SFact) (R : String → STerm) (Ar : String → SArr)
    (tab : List (List String × Option Int)) (f : IdxFact) : Bool :=
  match f with
  | .le rs b =>
      match tab.lookup rs with
      | some o => thrOk o b
      | none => entails F (f.toS R Ar)
  | _ => entails F (f.toS R Ar)

theorem entailsT_thrTab (F : List SFact) (R : String → STerm) (Ar : String → SArr)
    (ks : List (List String)) (f : IdxFact) :
    entailsT F R Ar (thrTab F R ks) f = entails F (f.toS R Ar) := by
  cases f with
  | le rs b =>
      simp only [entailsT]
      split
      · rename_i o ho
        rw [lookup_thrTab ho, IdxFact.toS, entails_le_thr]
      · rfl
  | _ => rfl

/-- **The facts of `fs` that follow from `F`** read through `R` and `Ar`: `fs` filtered by
    `entailsT` at the thresholds of the register lists of its upper bounds, computed once. -/
def filterEnt (F : List SFact) (R : String → STerm) (Ar : String → SArr)
    (fs : List IdxFact) : List IdxFact :=
  fs.filter (entailsT F R Ar (thrTab F R (leKeys fs)))

theorem filterEnt_eq (F : List SFact) (R : String → STerm) (Ar : String → SArr)
    (fs : List IdxFact) : filterEnt F R Ar fs = fs.filter fun f => entails F (f.toS R Ar) := by
  rw [filterEnt]
  exact List.filter_congr fun f _ => entailsT_thrTab F R Ar _ f

/-- Every fact of `fs` follows from `F` read through `R` and `Ar`, decided by `entailsT` at
    the thresholds of the register lists of its upper bounds, computed once. -/
def allEnt (F : List SFact) (R : String → STerm) (Ar : String → SArr)
    (fs : List IdxFact) : Bool :=
  fs.all (entailsT F R Ar (thrTab F R (leKeys fs)))

theorem allEnt_eq (F : List SFact) (R : String → STerm) (Ar : String → SArr)
    (fs : List IdxFact) : allEnt F R Ar fs = fs.all fun f => entails F (f.toS R Ar) := by
  rw [allEnt]
  congr 1
  funext f
  exact entailsT_thrTab F R Ar _ f

/-! ## 3. Edge facts -/

/-- The facts a comparison of the term `x` with the value `c` gives: on equality the bounds
    `c` from above and below; otherwise `x ≠ c`, and the lower bound `1` when `c = 0`. -/
def cmpFacts (x : STerm) (c : Nat) : Bool → List SFact
  | true => [.le [x] c, .ge x c]
  | false => [.ge x (if c = 0 then 1 else 0), .ne x c]

theorem cmpFacts_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {x : STerm} {c : Nat} {e : Bool} (h : decide (wval (x.ev V A C O) = c) = e) :
    ∀ f ∈ cmpFacts x c e, f.holds V A C O := by
  cases e with
  | true =>
      simp only [decide_eq_true_eq] at h
      simp [cmpFacts, SFact.holds, tsum, h]
  | false =>
      simp only [decide_eq_false_iff_not] at h
      simp only [cmpFacts, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
        forall_eq, SFact.holds]
      refine ⟨?_, h⟩
      split <;> omega

/-- The zero flag of a comparison with an immediate at width `64` is the equality of the value
    of the other operand with the value of the immediate. -/
theorem castW_beq_imm (x : Σ w, BitVec w) (n : Nat) :
    (castW x 64 == BitVec.ofNat 64 n) = decide (wval x = n % 2 ^ 64) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  unfold wval
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)

/-- The facts the condition `d` gives on the edge it takes (`taken`) or falls through: a
    branch on the zero flag of a comparison with an immediate at width `64` gives the facts
    `cmpFacts` of the other operand, and a branch on a register gives the lower bound `1`
    when taken and the upper bound `0` otherwise. -/
def edgeFacts (d : SDec) (taken : Bool) : List SFact :=
  match d with
  | .flag pol (.cmp x (.immW 64 n)) => cmpFacts x (n % 2 ^ 64) (taken == pol)
  | .flag pol (.cmp (.immW 64 n) y) => cmpFacts y (n % 2 ^ 64) (taken == pol)
  | .nz t => if taken then [.ge t 1] else [.le [t] 0]
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
  have hpol : ∀ a pol : Bool, (a == pol) = taken → a = (taken == pol) := by
    intro a pol h'
    subst h'
    cases a <;> cases pol <;> rfl
  have hc : ∀ n : Nat, castW (⟨64, BitVec.ofNat 64 n⟩ : Σ w, BitVec w) 64 = BitVec.ofNat 64 n :=
    fun n => by simp [castW]
  unfold edgeFacts
  split
  · rename_i pol x n
    apply cmpFacts_sound
    simp only [SDec.ev, SFlag.ev, STerm.ev, hc] at h
    rw [← castW_beq_imm]
    exact hpol _ _ h
  · rename_i pol n y _
    apply cmpFacts_sound
    simp only [SDec.ev, SFlag.ev, STerm.ev, hc] at h
    rw [← castW_beq_imm, BEq.comm]
    exact hpol _ _ h
  · rename_i t
    split
    · simp only [List.mem_singleton, forall_eq]
      apply one_le_wval
      simp only [SDec.ev] at h
      split at h <;> simp_all
    · rename_i hn
      simp only [List.mem_singleton, forall_eq, SFact.holds, tsum, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Nat.le_zero]
      simp only [SDec.ev] at h
      unfold wval
      split at h
      · simp only [decide_eq_false_iff_not, not_not, hn] at h
        simp [h]
      · rename_i hw
        simp [castW, hw]
  · simp

/-! ## 4. The check -/

/-- The facts of block `k` under the annotation `ann`. -/
def annAt (ann : List (List IdxFact)) (k : Nat) : List IdxFact := ann.getD k []

/-- Facts over the registers and arrays at a block entry, as symbolic facts at that
    entry. -/
def startF (fs : List IdxFact) : List SFact := fs.map (IdxFact.toS STerm.reg SArr.cell)

theorem startF_holds {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {fs : List IdxFact} (h : ∀ f ∈ fs, f.holds V A) : ∀ g ∈ startF fs, g.holds V A C O := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  exact (IdxFact.toS_holds STerm.reg SArr.cell f).mpr (h f hf)

/-- The facts `fs` of a successor follow, through the final symbolic registers and arrays of
    `ss`, from the facts `F`. -/
def succOk (F : List SFact) (ss : SSt) (fs : List IdxFact) : Bool :=
  fs.all fun f => entails F (f.toS ss.regs ss.arrs)

/-- `succOk` with the upper bounds decided by their thresholds (`allEnt`). -/
def succOkT (F : List SFact) (ss : SSt) (fs : List IdxFact) : Bool :=
  allEnt F ss.regs ss.arrs fs

/-- The compiled code of `succOk` is `succOkT`. -/
@[csimp] theorem succOk_eq_succOkT : @succOk = @succOkT := by
  funext F ss fs
  rw [succOk, succOkT, allEnt_eq]

theorem succOk_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {F : List SFact} {ss : SSt} {fs : List IdxFact} (h : succOk F ss fs = true)
    (hF : ∀ f ∈ F, f.holds V A C O) {u : LstateMF} (hu : Holds V A C O Z ss u) :
    ∀ f ∈ fs, f.holds u.prog.base.reg.lvm u.prog.base.larr := by
  intro f hf
  simp only [succOk, List.all_eq_true] at h
  have := (IdxFact.toS_holds (V := V) (A := A) (C := C) (O := O) ss.regs ss.arrs f).mp
    (entails_sound hF _ (h f hf))
  have he : u.prog.base.reg.lvm = fun r => (ss.regs r).ev V A C O := funext hu.1
  have ha : u.prog.base.larr = fun a => (ss.arrs a).ev V A C O := funext hu.2.1
  rw [he, ha]
  exact this

/-- Every index obligation follows from the facts `F`: its index is below the length, by
    `entails`, by `leMix` or by the affine form of the index (`affLe`). -/
def oblsOk (F : List SFact) (os : List SObl) : Bool :=
  os.all fun o => decide (0 < o.2) &&
    (entails F (.le [o.1] (o.2 - 1)) || leMix F [o.1] (o.2 - 1) || affLe F o.1 (o.2 - 1))

theorem oblsOk_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {F : List SFact} {os : List SObl} (h : oblsOk F os = true)
    (hF : ∀ f ∈ F, f.holds V A C O) : ∀ o ∈ os, o.holds V A C O := by
  intro o ho _
  simp only [oblsOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, he⟩ := h o ho
  have : (SFact.le [o.1] (o.2 - 1)).holds V A C O := by
    rcases Bool.or_eq_true_iff.mp he with he | he
    · rcases Bool.or_eq_true_iff.mp he with he | he
      · exact entails_sound hF _ he
      · exact leMix_sound hF he
    · simpa [SFact.holds, tsum] using affLe_sound hF he
  simp only [SFact.holds, tsum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at this
  unfold wval at this
  omega

/-- The successor facts of a block with terminator `T`, last instruction `z` and final
    symbolic state `ss` follow from the facts `F` of the block, the condition of a branch
    read by the symbolic branch condition `dec` (by default the x86 one, `symDec`). -/
def termInvOk (ann : List (List IdxFact)) (F : List SFact) (ss : SSt) (T : Term)
    (z : Option LinstrRM) (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match T with
  | .fall (some j) => succOk F ss (annAt ann j)
  | .fall none => true
  | .goto tg => succOk F ss (annAt ann tg)
  | .cond tg nx =>
      match z with
      | some (.Lcond c _, _) =>
          succOk (F ++ edgeFacts (dec ss c) true) ss (annAt ann tg) &&
            match nx with
            | some j => succOk (F ++ edgeFacts (dec ss c) false) ss (annAt ann j)
            | none => true
      | _ => false
  | .ret => true

/-- **The check of block `k`** under the symbolic step `sym` and the symbolic branch
    condition `dec` (by default the x86 ones, `symStep` and `symDec`): a block ending in
    `Lret`, or whose symbolic run fails, is accepted; otherwise its symbolic run is in the
    fragment, its index obligations follow from its facts and the width facts `guardW64` of
    the guards of the run, and the facts of its successors follow. -/
def blockInvOk (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG) (k : Nat)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) :
    Bool :=
  match (G.blk k).term with
  | .ret => true
  | T =>
      match symRun (bodyAt B (G.blk k) T) SSt.start sym with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          oblsOk (startF (annAt ann k) ++ gs.flatMap guardW64)
              (symObl (bodyAt B (G.blk k) T) SSt.start sym) &&
            termInvOk ann (startF (annAt ann k)) ss T B[(G.blk k).stop - 1]? dec

/-- **The bounds-invariant check** of the body `B` under the annotation `ann`, from the
    entry facts `entry`, under the symbolic step `sym` and the symbolic branch condition
    `dec` (by default the x86 ones): the body has a control-flow graph, every block passes
    `blockInvOk`, and the entry facts give the facts of block `0`. -/
def idxInvCheckB (entry : List IdxFact) (ann : List (List IdxFact)) (B : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) :
    Bool :=
  match cfgOf (B.map Prod.fst) with
  | some G =>
      (List.range G.blocks.size).all (fun k => blockInvOk ann B G k sym dec) &&
        (annAt ann 0).all fun f => entails (startF entry) (f.toS STerm.reg SArr.cell)
  | none => false

/-! ## 5. Soundness -/

section Sound

variable {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
variable {ann : List (List IdxFact)} {B : List LinstrRM} {G : CFG} {fn : String}

/-- The invariant up to the measure `N` for the instruction set `I`: a halting run from a
    block entry at which the facts of the block hold is in bounds. -/
def InvAt (I : Isa) (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG) (fn : String)
    (N : Nat) : Prop :=
  ∀ (fuel k : Nat) (s t : LstateMF),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    EntryAt B (G.blk k) s.prog.base.reg.lpc → s.prog.lfn = fn →
    (∀ f ∈ annAt ann k, f.holds s.prog.base.reg.lvm s.prog.base.larr) →
    I.lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    I.RunIdxOk (singletonProgM fn B) fuel s

theorem inv_step (hL : SymLaws I sym dec) (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOk ann B G k sym dec = true) {N : Nat}
    (ih : InvAt I ann B G fn N) : InvAt I ann B G fn (N + 1) := by
  intro fuel k s t hN hk hE hfn hinv hrun
  have F := blockFacts hG hk
  obtain ⟨hs1, hle⟩ := entry_le hG hk hE
  have hplain := body_plain hG hk hs1
  obtain ⟨u, f, hf, hu, hru⟩ :=
    fuel_runL_at hL.plain _ _ s t fuel hfn (drop_split B hle) hplain hrun
  obtain ⟨hul, hup⟩ := runL_frame_at hL.plain _ s u hplain hu
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
      run_inv_at hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [hL.ret] at he
    cases he
  -- the symbolic run of the block body
  have hD := symRun_sound_at hL.step_sound (singletonProgM fn B)
    ((B.drop s.prog.base.reg.lpc).take
      (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s
    (holds_start s)
  rw [symRun_entry_at hL.label hE hle] at hD
  have hbk := hb k hk
  unfold blockInvOk at hbk
  have hbk' : (match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start sym with
      | .fail => true
      | .unk => false
      | .ok ss gs =>
          oblsOk (startF (annAt ann k) ++ gs.flatMap guardW64)
              (symObl (bodyAt B (G.blk k) (G.blk k).term) SSt.start sym) &&
            termInvOk ann (startF (annAt ann k)) ss (G.blk k).term
              B[(G.blk k).stop - 1]? dec) = true := by
    revert hbk
    cases hT : (G.blk k).term with
    | ret => exact absurd hT hret
    | _ => exact id
  cases hS : symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start sym with
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
      (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) s I := by
    refine (symObl_sound_at hL.step_sound (singletonProgM fn B) _ SSt.start _ _ _ _ _ s u
      (holds_start s) ⟨ss, gs, by rw [symRun_entry_at hL.label hE hle]; exact hS⟩ hu).mpr
      fun o ho => ?_
    rw [symObl_entry_at hL.label hE hle] at ho
    exact oblsOk_sound hobl hF1 o ho
  have hokJ : ∀ f0, I.RunIdxOk (singletonProgM fn B) f0 u →
      I.RunIdxOk (singletonProgM fn B) (((B.drop s.prog.base.reg.lpc).take
        (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)).length + f0) s :=
    fun f0 h0 =>
      runIdxOk_of_runL_at hL.plain _ _ s u f0 hfn (drop_split B hle) hplain hu hlS h0
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
        exact runIdxOk_halt_at I (by rw [findInstrMem_single hul', hw, e1]; simp) f
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
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv_at hru hfetch
    have he0 := he
    rw [I.step_goto] at he
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [ite_eq_left hx, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      subst hf1
      exact runIdxOk_step_at hfetch (idxOkB_goto _ _ _ _) he0
        (ih f1 tg _ t (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
          (Or.inr ⟨rfl, label_at hl⟩) hul' (succOk_sound hti hF0 hH) hr1)
    · rw [ite_eq_right hx] at he
      cases he
  · -- branch
    subst hzi
    rw [hT] at hti
    simp only [termInvOk, Bool.and_eq_true] at hti
    obtain ⟨htk, hnt⟩ := hti
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lcond c l, zt) := by
      rw [findInstrMem_single hul', hw, hz]
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv_at hru hfetch
    have he0 := he
    subst hf1
    have hdec := hL.dec_sound hH c
    rw [I.step_cond] at he
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    by_cases hd : I.condEval u c = true
    · rw [ite_eq_left hd, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have hE' : ∀ g ∈ startF (annAt ann k) ++ edgeFacts (dec ss c) true,
          g.holds s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf s.prog.base.of := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF0 g hg
        · exact edgeFacts_sound (hdec.symm.trans hd) g hg
      exact runIdxOk_step_at hfetch (idxOkB_cond _ _ _ _) he0
        (ih f1 tg _ t (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
          (Or.inr ⟨rfl, label_at hl⟩) hul' (succOk_sound htk hE' hH) hr1)
    · rw [ite_eq_right hd] at he
      simp only [Option.some.injEq] at he
      subst he
      have hE' : ∀ g ∈ startF (annAt ann k) ++ edgeFacts (dec ss c) false,
          g.holds s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf s.prog.base.of := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF0 g hg
        · exact edgeFacts_sound (by rw [← hdec]; simpa using hd) g hg
      refine runIdxOk_step_at hfetch (idxOkB_cond _ _ _ _) he0 ?_
      have hw1 : u.prog.base.reg.lpc + 1 = (G.blk k).stop := by omega
      cases nx with
      | none =>
          have e1 := (stop_next hG hk).1 hnx.symm
          exact runIdxOk_halt_at I (by
            rw [findInstrMem_single (s := ⟨⟨u.prog.base.nextPc, u.prog.lfn⟩, u.zf⟩) hul']
            show B[u.prog.base.reg.lpc + 1]? = none
            rw [hw1, e1]; simp) f1
      | some j =>
          obtain ⟨hj, hjlt, e1⟩ := (stop_next hG hk).2 j hnx.symm
          subst hj
          exact ih f1 (k + 1) _ t (measure_le hN (show f1 ≤ fuel by omega) hk) hjlt
            (Or.inl (hw1.trans e1)) hul' (succOk_sound hnt hE' hH) hr1
  · exact absurd hT hret

theorem invAt_all (hL : SymLaws I sym dec) (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOk ann B G k sym dec = true) :
    ∀ N, InvAt I ann B G fn N
  | 0 => fun _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => inv_step hL hG hb (invAt_all hL hG hb N)

end Sound

/-- **Soundness of the bounds-invariant check over an instruction set.** If the symbolic
    step `sym` and the symbolic branch condition `dec` satisfy `SymLaws I sym dec` and
    `idxInvCheckB entry ann B sym dec` accepts, every halting run of `I` on the singleton
    program over `B` from a state at pc `0` of that function whose registers and arrays
    satisfy the entry facts is in bounds. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV.SymLaws.runIdxOk_of_idxInvCheckB
    {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec) {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} (h : idxInvCheckB entry ann B sym dec = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    I.RunIdxOk (singletonProgM fn B) fuel s := by
  unfold idxInvCheckB at h
  split at h
  · rename_i G hG
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    obtain ⟨hb, h0⟩ := h
    by_cases hB : B.map Prod.fst = []
    · have hBn : B = [] := by simpa using hB
      subst hBn
      exact runIdxOk_halt_at I (by rw [findInstrMem_single hfn]; simp) fuel
    obtain ⟨hpos, hs0⟩ := cfgOf_start_zero hG hB
    have hF := startF_holds (A := s.prog.base.larr) (C := s.prog.base.cf)
      (O := s.prog.base.of) hent
    have hinv : ∀ f ∈ annAt ann 0, f.holds s.prog.base.reg.lvm s.prog.base.larr :=
      fun f hf => (IdxFact.toS_holds STerm.reg SArr.cell f).mp (entails_sound hF _ (h0 f hf))
    exact invAt_all hL hG hb _ fuel 0 s t (Nat.lt_succ_self _) hpos
      (Or.inl (hpc.trans hs0.symm)) hfn hinv hrun
  · cases h

/-- **A halting run of an accepted body over an instruction set is a halting checked
    run.** -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV.SymLaws.lsemFuelMemFk_of_idxInvCheckB
    {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec) {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} (h : idxInvCheckB entry ann B sym dec = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    I.lsemFuelMemFk true (singletonProgM fn B) fuel s = some t :=
  I.lsemFuelMemFk_of_runIdxOk true _ fuel s t hrun
    (hL.runIdxOk_of_idxInvCheckB h fn s t hfn hpc hent fuel hrun)

/-- **The checker on runs of an accepted source body, over an instruction set.** If the
    symbolic step `sym` and the symbolic branch condition `dec` satisfy `SymLaws I sym dec`
    and `SymSubst sym dec`, and `ownedCheckMC outs B B' sym dec` and
    `idxInvCheckB entry ann B sym dec` accept, every halting run of `I` on `B` from a state
    at pc `0` whose registers and arrays satisfy the entry facts is matched by a halting
    checked run of `I` on `B'` from the same state, the end states agreeing on `outs`, the
    arrays and the word memory. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV.SymLaws.ownedCheckMC_sound_of_idxInv
    {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec) (hS : SymSubst sym dec) {outs : List String}
    {B B' : List LinstrRM} {entry : List IdxFact} {ann : List (List IdxFact)}
    (h : ownedCheckMC outs B B' sym dec = true) (hi : idxInvCheckB entry ann B sym dec = true)
    (fn : String) (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' :=
  ownedCheckMC_sound_at hL hS h fn s t hfn hpc fuel
    (hL.lsemFuelMemFk_of_idxInvCheckB hi fn s t hfn hpc hent fuel hrun)

/-- **Soundness of the bounds-invariant check.** If `idxInvCheckB entry ann B` accepts,
    every halting run of `lsemFuelMemF` on the singleton program over `B` from a state at
    pc `0` of that function whose registers and arrays satisfy the entry facts is in
    bounds. -/
theorem runIdxOk_of_idxInvCheckB {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} (h : idxInvCheckB entry ann B = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    RunIdxOk (singletonProgM fn B) fuel s := by
  rw [← x86Isa_lsemFuelMemF] at hrun
  rw [← x86Isa_RunIdxOk]
  exact symLaws_x86.runIdxOk_of_idxInvCheckB h fn s t hfn hpc hent fuel hrun

/-- **A halting run of an accepted body is a halting checked run.** -/
theorem lsemFuelMemFk_of_idxInvCheckB {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} (h : idxInvCheckB entry ann B = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    lsemFuelMemFk true (singletonProgM fn B) fuel s = some t := by
  rw [← x86Isa_lsemFuelMemF] at hrun
  rw [← x86Isa_lsemFuelMemFk]
  exact symLaws_x86.lsemFuelMemFk_of_idxInvCheckB h fn s t hfn hpc hent fuel hrun

/-- **The checker on runs of an accepted source body.** If `ownedCheckMC outs B B'` and
    `idxInvCheckB entry ann B` accept, every halting run of `lsemFuelMemF` on `B` from a
    state at pc `0` whose registers and arrays satisfy the entry facts is matched by a
    halting checked run of `B'` from the same state, the end states agreeing on `outs`, the
    arrays and the word memory. -/
theorem ownedCheckMC_sound_of_idxInv {outs : List String} {B B' : List LinstrRM}
    {entry : List IdxFact} {ann : List (List IdxFact)} (h : ownedCheckMC outs B B' = true)
    (hi : idxInvCheckB entry ann B = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  rw [← x86Isa_lsemFuelMemF] at hrun
  simpa only [x86Isa_lsemFuelMemFk] using
    symLaws_x86.ownedCheckMC_sound_of_idxInv symSubst_x86 h hi fn s t hfn hpc hent fuel hrun

/-! ## 6. Annotation by restriction to a fixed point -/

/-- The registers an index obligation, a branch condition or an entry fact of `B` reads:
    the candidates of the annotation. -/
def annRegs (entry : List IdxFact) (B : List LinstrRM) (G : CFG) : List String :=
  let fromEntry := entry.flatMap fun
    | .le rs _ => rs | .ge r _ => [r] | .w64 r => [r] | .ale _ _ => []
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
    pair of distinct registers bounded by each bound, each register at least `1`, and each
    register of width `64`. -/
def annCands (rs : List String) (bs : List Nat) : List IdxFact :=
  let pairs := rs.flatMap fun r => (rs.dropWhile (· ≠ r)).drop 1 |>.map fun r' => [r, r']
  (bs.flatMap fun b => (rs.map fun r => .le [r] b) ++ pairs.map fun p => .le p b)
    ++ rs.map (fun r => .ge r 1) ++ rs.map .w64

/-- One restriction pass: for every block in order, the facts of each successor that do not
    follow from the facts of the block (with the condition of the edge) are dropped. -/
def annPass (B : List LinstrRM) (G : CFG) (ann : List (List IdxFact)) :
    List (List IdxFact) :=
  (List.range G.blocks.size).foldl (fun ann k =>
    match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
    | .ok ss _ =>
        let F := startF (annAt ann k)
        let keep (F' : List SFact) (ann : List (List IdxFact)) (j : Nat) :=
          ann.set j ((annAt ann j).filter fun f => entails F' (f.toS ss.regs ss.arrs))
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

/-- The restriction edges of block `k` of `B`: each successor `j` with the facts its edge
    condition adds and the final symbolic state of the block, as `annPass` uses them. -/
def annEdges (B : List LinstrRM) (G : CFG) (k : Nat) : List (Nat × List SFact × SSt) :=
  match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
  | .ok ss _ =>
      match (G.blk k).term with
      | .fall (some j) => [(j, [], ss)]
      | .goto tg => [(tg, [], ss)]
      | .cond tg nx =>
          match B[(G.blk k).stop - 1]? with
          | some (.Lcond c _, _) =>
              (tg, edgeFacts (symDec ss c) true, ss) ::
                match nx with
                | some j => [(j, edgeFacts (symDec ss c) false, ss)]
                | none => []
          | _ => []
      | _ => []
  | _ => []

/-- One worklist step of the restriction at block `k`: the facts of each successor that do
    not follow from the facts `F` of the block (with the condition of the edge) are dropped,
    and each successor whose facts shrank is queued unless it is pending. -/
def annVisit (F : List SFact) (es : List (Nat × List SFact × SSt))
    (st : Array (List IdxFact) × Array Bool × Std.Queue Nat) :
    Array (List IdxFact) × Array Bool × Std.Queue Nat :=
  es.foldl (fun (a, pend, q) (j, ex, ss) =>
    let old := a.getD j []
    let new := old.filter fun f => entails (F ++ ex) (f.toS ss.regs ss.arrs)
    if new.length < old.length then
      if pend.getD j false then (a.set! j new, pend, q)
      else (a.set! j new, pend.set! j true, q.enqueue j)
    else (a, pend, q)) st

/-- `annVisit` with the successor facts filtered by `filterEnt`: the thresholds of the upper
    bounds of each successor are computed once per edge. -/
def annVisitT (F : List SFact) (es : List (Nat × List SFact × SSt))
    (st : Array (List IdxFact) × Array Bool × Std.Queue Nat) :
    Array (List IdxFact) × Array Bool × Std.Queue Nat :=
  es.foldl (fun (a, pend, q) (j, ex, ss) =>
    let old := a.getD j []
    let new := filterEnt (F ++ ex) ss.regs ss.arrs old
    if new.length < old.length then
      if pend.getD j false then (a.set! j new, pend, q)
      else (a.set! j new, pend.set! j true, q.enqueue j)
    else (a, pend, q)) st

/-- The compiled code of `annVisit` is `annVisitT`. -/
@[csimp] theorem annVisit_eq_annVisitT : @annVisit = @annVisitT := by
  funext F es st
  simp only [annVisit, annVisitT, filterEnt_eq]

/-- The restriction by a worklist, within `fuel` visits: a block is visited when it is
    dequeued, and queued again only when its facts shrank. -/
def annWork (E : Array (List (Nat × List SFact × SSt))) :
    Nat → Array (List IdxFact) × Array Bool × Std.Queue Nat → Array (List IdxFact)
  | 0, (a, _, _) => a
  | fuel + 1, (a, pend, q) =>
      match q.dequeue? with
      | none => a
      | some (k, q) =>
          annWork E fuel (annVisit (startF (a.getD k [])) (E.getD k []) (a, pend.set! k false, q))

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

/-- The candidate facts of the annotation of `B` from the entry facts `entry`: the candidates
    `annCands` over the registers `annRegs` with the bounds of the entry facts, the array
    lengths `oblLens` of the index obligations and the immediates `seedImms` the blocks leave
    in the candidate registers, and the element bounds `.ale` of the entry facts. -/
def idxCands (entry : List IdxFact) (B : List LinstrRM) (G : CFG) : List IdxFact :=
  let rs := annRegs entry B G
  let bs := ((entry.filterMap fun | .le _ b => some b | _ => none)
    ++ oblLens B G ++ seedImms B G rs).eraseDups
  annCands rs bs ++ entry.filter fun | .ale _ _ => true | _ => false

/-- **The annotation by restriction**: block `0` holds the candidates the entry facts give,
    every other block all candidates, restricted along the edges `annEdges` of the blocks
    by the worklist `annWork` to a fixed point (within a bound on the number of visits:
    every visit after the first of each block follows the removal of a fact). The bounds
    of the candidates are the bounds of the entry facts, the array lengths `oblLens` of the
    index obligations and the immediates `seedImms` the blocks leave in the candidate
    registers, so a counter seeded with an immediate is bounded by that immediate and by
    the length of the array its index reads. The element bounds `.ale` of the entry facts
    are candidates as well. `idxInvCheckB` checks the result. -/
def idxAnnot (entry : List IdxFact) (B : List LinstrRM) : List (List IdxFact) :=
  match cfgOf (B.map Prod.fst) with
  | some G =>
      let nb := G.blocks.size
      let cs := idxCands entry B G
      let a0 := (Array.range nb).map fun k =>
        if k = 0 then cs.filter fun f => entails (startF entry) (f.toS STerm.reg SArr.cell)
        else cs
      let E := (Array.range nb).map (annEdges B G)
      let q0 := (List.range nb).foldl (fun q k => q.enqueue k) Std.Queue.empty
      (annWork E (nb * (cs.length + 1) + 1) (a0, Array.replicate nb true, q0)).toList
  | none => []

/-! ## 7. The facts of a layout's register bounds -/

open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- The facts of the register bounds of `σ`, each register named by `nm`. -/
def boundFacts (σ : AbiLayout) (nm : String → String) : List IdxFact :=
  σ.bounds.map fun b => .le [nm b.1] b.2

/-- **The facts of a layout's register bounds hold** at registers `V` that hold each bounded
    register of a separated entry state at width `64` under its name, and at every array
    state `A`. -/
theorem boundFacts_holds {σ : AbiLayout} {sa : AState} (hR : σ.Regions sa)
    {nm : String → String} {V : String → Σ w, BitVec w} {A : String → ArrCell}
    (hV : ∀ b ∈ σ.bounds, V (nm b.1) = ⟨64, sa.regs b.1⟩) :
    ∀ f ∈ boundFacts σ nm, f.holds V A := by
  intro f hf
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
  simp only [IdxFact.holds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, wval, hV b hb]
  exact hR.1 b hb

end CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
