/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTExitArr

@[expose] public section

set_option autoImplicit false

/-!
# The bounds condition of a counted loop over word arrays

`ArrRunL` asks that every element index a run loads or stores is an element index of the
array it accesses. For a runtime-count loop `RForRuntime x (SVar n) body` whose trip body
indexes only through copies of the loop index `x`, and whose accessed arrays have at least `m`
words and are written only at a type of at least `m` words, every access of every trip is in
bounds as soon as the count `n` is at most `m`: the index of trip `t` is `t < n ≤ m`.

`inbB A m I c` is the Boolean check of a trip body: the arrays accessed are among `A`, every
index name is in the list `I` of names known to hold a trip index, and `c` writes a name of
`A` only by an element store at a type of at least `m` words. It returns the index names after
`c`. `loopInbB A m n` checks a program of word binders around one such loop over the count
variable `n`.

## Main definitions

* `ArrLong`, `IdxBelow` — the arrays of `A` hold at least `m` words; the names of `I` hold
  values below `m`.
* `idxCopyB`, `longTyB`, `inbB`, `loopInbB` — the Boolean checks.

## Main results

* `inbB_sound` — an accepted trip body runs in bounds and keeps `ArrLong`.
* `arrRunL_of_loopInbB` — **the bounds lemma**: an accepted loop program runs in bounds from
  every state whose count is at most `m` and whose arrays of `A` hold at least `m` words.
-/

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCT

variable {N : Nat} {L : LeafSpec}

/-- Every array named in `A` holds at least `m` words at `rs`. -/
def ArrLong (A : List String) (m : Nat) (rs : RustState) : Prop :=
  ∀ a ∈ A, ∀ (n : Nat) (v : RustVal (.TArr n .TU64)),
    rs.rsTower a = some ⟨.TArr n .TU64, v⟩ → m ≤ n

/-- Every name of `I` holds a value below `m` at `rs`. -/
def IdxBelow (I : List String) (m : Nat) (rs : RustState) : Prop :=
  ∀ y ∈ I, rs.rsScalar y < m

/-- The expression is a copy of a name of `I`: the name itself, or the name plus `0`. -/
def idxCopyB (I : List String) : SExpr → Bool
  | .SVar z => decide (z ∈ I)
  | .SAdd (.SVar z) (.SLit 0) => decide (z ∈ I)
  | _ => false

theorem idxCopyB_sound {I : List String} {m : Nat} {rs : RustState} {e : SExpr}
    (h : idxCopyB I e = true) (hI : IdxBelow I m rs) : e.evalState rs < m := by
  unfold idxCopyB at h
  split at h
  · rename_i z
    exact hI z (of_decide_eq_true h)
  · rename_i z
    simpa [SExpr.evalState] using hI z (of_decide_eq_true h)
  · cases h

/-- The type is an array of at least `m` words. -/
def longTyB (m : Nat) : TowerType → Bool
  | .TArr n .TU64 => decide (m ≤ n)
  | _ => false

/-- **The bounds check of a trip body** from the index names `I`: the index names after the
    command, or `none`. An element load or store indexes by a name of `I` into an array of
    `A`; a load writes no name of `A`; a store writes at a type of at least `m` words; a zeroed
    tower slot and a limb store write no name of `A`; a scalar write removes its name from
    `I`, and adds it back when it copies a name of `I`. Every other command is refused. -/
def inbB (A : List String) (m : Nat) : List String → LowCT → Option (List String)
  | I, .RSkip => some I
  | I, .RSeq a b => (inbB A m I a).bind fun I' => inbB A m I' b
  | I, .RLetU64Zero y b => inbB A m (I.filter (· != y)) b
  | I, .RLetZero y _ b => if y ∈ A then none else inbB A m I b
  | I, .RScalarSet y _ => some (I.filter (· != y))
  | I, .RScalarSetExpr y e =>
      if idxCopyB I e then some (y :: I.filter (· != y)) else some (I.filter (· != y))
  | I, .RArrLoad dst src i =>
      if i ∈ I ∧ src.locVar ∈ A ∧ dst.locVar ∉ A then some I else none
  | I, .RArrStore arr i _ =>
      if i ∈ I ∧ arr.locVar ∈ A ∧ longTyB m arr.locDst = true then some I else none
  | I, .RLimbStoreExpr loc _ _ => if loc.locVar ∈ A then none else some I
  | _, _ => none

section Lemmas

variable {A : List String} {m : Nat}

theorem idxBelow_filter {I : List String} {rs : RustState} (h : IdxBelow I m rs) (y : String)
    (v : Nat) : IdxBelow (I.filter (· != y)) m (rsSetScalar rs y v) := by
  intro z hz
  have hz' := List.mem_filter.mp hz
  have hne : z ≠ y := by simpa using hz'.2
  simpa [rsSetScalar, hne] using h z hz'.1

theorem idxBelow_cons {I : List String} {rs : RustState} (h : IdxBelow I m rs) (y : String)
    {v : Nat} (hv : v < m) : IdxBelow (y :: I.filter (· != y)) m (rsSetScalar rs y v) := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · simpa [rsSetScalar] using hv
  · exact idxBelow_filter h y v z hz

theorem arrLong_setScalar {rs : RustState} (h : ArrLong A m rs) (y : String) (v : Nat) :
    ArrLong A m (rsSetScalar rs y v) := h

theorem arrLong_setTower_not {rs : RustState} (h : ArrLong A m rs) {y : String} (hy : y ∉ A)
    (v : Σ t : TowerType, RustVal t) : ArrLong A m (rsSetTower rs y v) := by
  intro a ha n w hw
  have hne : a ≠ y := fun e => hy (e ▸ ha)
  simp only [rsSetTower, beq_iff_eq, hne, if_false] at hw
  exact h a ha n w hw

theorem idxBelow_setTower {I : List String} {rs : RustState} (h : IdxBelow I m rs) (y : String)
    (v : Σ t : TowerType, RustVal t) : IdxBelow I m (rsSetTower rs y v) := h

theorem arrLong_setTower_long {rs : RustState} (h : ArrLong A m rs) (y : String)
    {t : TowerType} (ht : longTyB m t = true) (v : RustVal t) :
    ArrLong A m (rsSetTower rs y ⟨t, v⟩) := by
  intro a ha n w hw
  by_cases hay : a = y
  · subst hay
    simp only [rsSetTower, beq_self_eq_true, if_true, Option.some.injEq] at hw
    have e := (Sigma.mk.inj_iff.mp hw).1
    subst e
    simpa [longTyB] using ht
  · simp only [rsSetTower, beq_iff_eq, hay, if_false] at hw
    exact h a ha n w hw

end Lemmas

/-- **Soundness of the trip-body check.** Let `inbB A m I c = some I'`, and let the view
    accept every index below the length of the array. From a state whose names of `I` hold
    values below `m` and whose arrays of `A` hold at least `m` words, every access of a run of
    `c` is in bounds (`ArrRun`), and every final state of `c` keeps both properties, at the
    index names `I'`. -/
theorem inbB_sound (V : ArrView L) (hV : ∀ n v k, k < n → V.inb n v k) {A : List String}
    {m : Nat} : ∀ (c : LowCT) (I I' : List String) (rs : RustState), inbB A m I c = some I' →
    IdxBelow I m rs → ArrLong A m rs →
    ArrRun (N := N) V c rs ∧
      ∀ rs', RustExec N L c rs rs' → IdxBelow I' m rs' ∧ ArrLong A m rs' := by
  intro c
  induction c with
  | RSkip =>
      intro I I' rs h hI hA
      simp only [inbB, Option.some.injEq] at h
      subst h
      refine ⟨trivial, fun rs' hx => ?_⟩
      cases hx
      exact ⟨hI, hA⟩
  | RSeq a b iha ihb =>
      intro I I' rs h hI hA
      simp only [inbB, Option.bind_eq_some_iff] at h
      obtain ⟨I1, h1, h2⟩ := h
      obtain ⟨ra, pa⟩ := iha I I1 rs h1 hI hA
      refine ⟨⟨ra, fun r1 hr1 => (ihb I1 I' r1 h2 (pa r1 hr1).1 (pa r1 hr1).2).1⟩,
        fun rs' hx => ?_⟩
      cases hx with
      | seq _ _ _ r1 _ hx1 hx2 =>
          obtain ⟨hI1, hA1⟩ := pa r1 hx1
          exact (ihb I1 I' r1 h2 hI1 hA1).2 rs' hx2
  | RLetU64Zero y b ih =>
      intro I I' rs h hI hA
      simp only [inbB] at h
      obtain ⟨rb, pb⟩ := ih _ I' _ h (idxBelow_filter hI y 0) (arrLong_setScalar hA y 0)
      refine ⟨rb, fun rs' hx => ?_⟩
      cases hx with
      | letU64Zero _ _ _ _ hb => exact pb rs' hb
  | RLetZero y t b ih =>
      intro I I' rs h hI hA
      simp only [inbB] at h
      split at h
      · cases h
      · rename_i hy
        obtain ⟨rb, pb⟩ := ih I I' _ h (idxBelow_setTower hI y _)
          (arrLong_setTower_not hA hy _)
        refine ⟨rb, fun rs' hx => ?_⟩
        cases hx with
        | letZero _ _ _ _ _ hb => exact pb rs' hb
  | RScalarSet y k =>
      intro I I' rs h hI hA
      simp only [inbB, Option.some.injEq] at h
      subst h
      refine ⟨trivial, fun rs' hx => ?_⟩
      cases hx
      exact ⟨idxBelow_filter hI y _, arrLong_setScalar hA y _⟩
  | RScalarSetExpr y e =>
      intro I I' rs h hI hA
      refine ⟨trivial, fun rs' hx => ?_⟩
      cases hx
      simp only [inbB] at h
      split at h
      · rename_i he
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨idxBelow_cons hI y (idxCopyB_sound he hI), arrLong_setScalar hA y _⟩
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨idxBelow_filter hI y _, arrLong_setScalar hA y _⟩
  | RArrLoad dst src i =>
      intro I I' rs h hI hA
      simp only [inbB] at h
      split at h
      · rename_i hc
        obtain ⟨hi, hs, hd⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun n v hv => hV n v _ (Nat.lt_of_lt_of_le (hI i hi) (hA _ hs n v hv)),
          fun rs' hx => ?_⟩
        cases hx
        exact ⟨idxBelow_setTower hI _ _, arrLong_setTower_not hA hd _⟩
      · cases h
  | RArrStore arr i src =>
      intro I I' rs h hI hA
      simp only [inbB] at h
      split at h
      · rename_i hc
        obtain ⟨hi, hs, hl⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun n v hv => hV n v _ (Nat.lt_of_lt_of_le (hI i hi) (hA _ hs n v hv)),
          fun rs' hx => ?_⟩
        cases hx
        exact ⟨idxBelow_setTower hI _ _, arrLong_setTower_long hA _ hl _⟩
      · cases h
  | RLimbStoreExpr loc k e =>
      intro I I' rs h hI hA
      simp only [inbB] at h
      split at h
      · cases h
      · rename_i hl
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨trivial, fun rs' hx => ?_⟩
        cases hx
        exact ⟨idxBelow_setTower hI _ _, arrLong_setTower_not hA hl _⟩
  | _ => intro I I' rs h; simp [inbB] at h

/-- **The loop check**: word binders on no name `n`, around `RForRuntime x (SVar n) body` whose
    trip body passes `inbB` from the index `x`. -/
def loopInbB (A : List String) (m : Nat) (n : String) : LowCT → Bool
  | .RLetU64Zero y b => y != n && loopInbB A m n b
  | .RForRuntime x (.SVar n') body => n' == n && (inbB A m [x] body).isSome
  | _ => false

/-- Every state a run of `k ≤ m` trips of an accepted trip body reaches keeps `ArrLong`. -/
theorem arrLong_rFor (V : ArrView L) (hV : ∀ n v k, k < n → V.inb n v k) {A : List String}
    {m : Nat} {x : String} {body : LowCT} {I' : List String}
    (hb : inbB A m [x] body = some I') :
    ∀ (k : Nat) (rs r : RustState), k ≤ m → ArrLong A m rs →
      RustExec N L (.RFor x k body) rs r → ArrLong A m r := by
  intro k
  induction k with
  | zero =>
      intro rs r _ hA hx
      cases hx
      exact hA
  | succ k ih =>
      intro rs r hk hA hx
      cases hx with
      | forSucc _ _ _ _ r1 _ hx1 hx2 =>
          have hA1 := ih rs r1 (by omega) hA hx1
          have hI : IdxBelow [x] m (rsSetScalar r1 x k) := by
            intro z hz
            rw [List.mem_singleton.mp hz]
            simpa [rsSetScalar] using (show k < m by omega)
          exact ((inbB_sound (N := N) V hV body [x] I' _ hb hI
            (arrLong_setScalar hA1 x k)).2 r hx2).2

/-- **The bounds lemma.** Let the program pass `loopInbB A m n`, and let the view accept every
    index below the length of the array. From every state whose count `n` is at most `m` and
    whose arrays of `A` hold at least `m` words, the run of the program is in bounds
    (`ArrRunL`): trip `t` indexes by `t < n ≤ m`. -/
theorem arrRunL_of_loopInbB (V : ArrView L) (hV : ∀ n v k, k < n → V.inb n v k)
    {A : List String} {m : Nat} {n : String} :
    ∀ (c : LowCT) (rs : RustState), loopInbB A m n c = true → rs.rsScalar n ≤ m →
      ArrLong A m rs → ArrRunL (N := N) V c rs := by
  intro c
  induction c with
  | RLetU64Zero y b ih =>
      intro rs h hn hA
      simp only [loopInbB, Bool.and_eq_true] at h
      refine ih _ h.2 ?_ (arrLong_setScalar hA y 0)
      have hne : n ≠ y := fun e => by simp [e] at h
      simpa [rsSetScalar, hne] using hn
  | RForRuntime x bd body _ =>
      intro rs h hn hA
      cases bd with
      | SVar n' =>
          simp only [loopInbB, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨rfl, hs⟩ := h
          obtain ⟨I', hb⟩ := Option.isSome_iff_exists.mp hs
          intro t ht r hx
          simp only [SExpr.evalState] at ht
          have hA' := arrLong_rFor (N := N) V hV hb t rs r (by omega) hA hx
          have hI : IdxBelow [x] m (rsSetScalar r x t) := by
            intro z hz
            rw [List.mem_singleton.mp hz]
            simpa [rsSetScalar] using (show t < m by omega)
          exact (inbB_sound (N := N) V hV body [x] I' _ hb hI (arrLong_setScalar hA' x t)).1
      | _ => simp [loopInbB] at h
  | _ => intro rs h; simp [loopInbB] at h

end CatCrypt.Crypto.Hax
