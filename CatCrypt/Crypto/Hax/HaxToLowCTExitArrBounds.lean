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
array it accesses, and that every sum of a word and a literal it assigns stays below `2^64`
(`offRange`). For a runtime-count loop `RForRuntime x (SVar n) body` every access of every trip
is in bounds as soon as the count `n` is at most `m`, when the trip body indexes only through
the loop index `x` plus a literal offset `d`, and each array `a` it accesses at offset `d` has
at least `m + δ a` words with `d ≤ δ a`: the index of trip `t` plus `d` is below `m + d`.

`inbB A m δ I c` is the Boolean check of a trip body: the arrays accessed are among `A`, every
index name is in the list `I` of names holding a trip index plus a known offset, an access at
offset `d` goes to an array `a` with `d ≤ δ a`, and `c` writes a name of `A` only by an
element store at a type of at least `m + δ a` words. It returns the index names after `c`.
`loopInbB A m δ n` checks a program of word binders around one such loop over the count
variable `n`.

## Main definitions

* `ArrLong`, `IdxBelow` — each array `a` of `A` holds at least `m + δ a` words; each name of
  `I` holds a value below `m` plus its offset.
* `idxOf`, `idxOff`, `longTyB`, `inbB`, `loopInbB` — the offset of an index name or
  expression, and the Boolean checks.

## Main results

* `inbB_sound` — an accepted trip body runs in bounds and keeps `ArrLong`.
* `arrRunL_of_loopInbB` — **the bounds lemma**: an accepted loop program runs in bounds from
  every state whose count is at most `m` and whose arrays `a` of `A` hold at least `m + δ a`
  words.
-/

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCT

variable {N : Nat} {L : LeafSpec}

/-- Every array `a` named in `A` holds at least `m + δ a` words at `rs`. -/
def ArrLong (A : List String) (m : Nat) (δ : String → Nat) (rs : RustState) : Prop :=
  ∀ a ∈ A, ∀ (n : Nat) (v : RustVal (.TArr n .TU64)),
    rs.rsTower a = some ⟨.TArr n .TU64, v⟩ → m + δ a ≤ n

/-- Every name `y` of `I`, with its offset `d`, holds a value below `m + d` at `rs`. -/
def IdxBelow (I : List (String × Nat)) (m : Nat) (rs : RustState) : Prop :=
  ∀ p ∈ I, rs.rsScalar p.1 < m + p.2

/-- The offset of the first entry of `I` named `z`. -/
def idxOf (I : List (String × Nat)) (z : String) : Option Nat :=
  (I.find? (·.1 == z)).map (·.2)

/-- The offset of an index expression: a name of `I`, or a name of `I` plus a literal. -/
def idxOff (I : List (String × Nat)) : SExpr → Option Nat
  | .SVar z => idxOf I z
  | .SAdd (.SVar z) (.SLit k) => (idxOf I z).map (· + k)
  | _ => none

theorem idxOf_sound {I : List (String × Nat)} {m : Nat} {rs : RustState} {z : String}
    {d : Nat} (h : idxOf I z = some d) (hI : IdxBelow I m rs) : rs.rsScalar z < m + d := by
  unfold idxOf at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hz : p.1 = z := by simpa using List.find?_some hp
  rw [← hz]
  exact hI p (List.mem_of_find?_eq_some hp)

theorem idxOff_sound {I : List (String × Nat)} {m : Nat} {rs : RustState} {e : SExpr} {d : Nat}
    (h : idxOff I e = some d) (hI : IdxBelow I m rs) : e.evalState rs < m + d := by
  unfold idxOff at h
  split at h
  · exact idxOf_sound h hI
  · rename_i z k
    obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp h
    have := idxOf_sound hd0 hI
    simp only [SExpr.evalState]
    omega
  · cases h

/-- An index expression with an offset meets `offRange` when `m` plus the offset is at most
    `2^64`. -/
theorem offRange_of_idxOff {I : List (String × Nat)} {m : Nat} {rs : RustState} {e : SExpr}
    {d : Nat} (h : idxOff I e = some d) (hI : IdxBelow I m rs) (hm : m + d ≤ 2 ^ 64) :
    offRange e rs := by
  unfold idxOff at h
  split at h
  · trivial
  · rename_i z k
    obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp h
    have := idxOf_sound hd0 hI
    show rs.rsScalar z + k < 2 ^ 64
    omega
  · cases h

theorem offRange_of_not_isOffB {e : SExpr} (h : isOffB e = false) (rs : RustState) :
    offRange e rs := by
  unfold offRange
  split
  · simp [isOffB] at h
  · trivial

/-- The type is an array of at least `m` words. -/
def longTyB (m : Nat) : TowerType → Bool
  | .TArr n .TU64 => decide (m ≤ n)
  | _ => false

/-- **The bounds check of a trip body** from the index names `I` with their offsets: the index
    names after the command, or `none`. An element load or store indexes by a name of `I` at an
    offset `d` into an array `a` of `A` with `d ≤ δ a`; a load writes no name of `A`; a store
    writes at a type of at least `m + δ a` words; a zeroed tower slot, a limb store and a call
    write no name of `A`; a scalar write removes its name from `I`, and adds it back with its
    offset when it assigns a name of `I` plus a literal with `m` plus the offset at most `2^64`;
    a sum of a word and a literal outside `I` is refused. Every other command is refused. -/
def inbB (A : List String) (m : Nat) (δ : String → Nat) :
    List (String × Nat) → LowCT → Option (List (String × Nat))
  | I, .RSkip => some I
  | I, .RSeq a b => (inbB A m δ I a).bind fun I' => inbB A m δ I' b
  | I, .RLetU64Zero y b => inbB A m δ (I.filter (·.1 != y)) b
  | I, .RLetZero y _ b => if y ∈ A then none else inbB A m δ I b
  | I, .RScalarSet y _ => some (I.filter (·.1 != y))
  | I, .RScalarSetExpr y e =>
      match idxOff I e with
      | some d => if m + d ≤ 2 ^ 64 then some ((y, d) :: I.filter (·.1 != y)) else none
      | none => if isOffB e then none else some (I.filter (·.1 != y))
  | I, .RArrLoad dst src i =>
      if (idxOf I i).any (· ≤ δ src.locVar) ∧ src.locVar ∈ A ∧ dst.locVar ∉ A then some I
      else none
  | I, .RArrStore arr i _ =>
      if (idxOf I i).any (· ≤ δ arr.locVar) ∧ arr.locVar ∈ A ∧
          longTyB (m + δ arr.locVar) arr.locDst = true then some I
      else none
  | I, .RLimbStoreExpr loc _ _ => if loc.locVar ∈ A then none else some I
  | I, .RCall _ d _ => if d.locVar ∈ A then none else some I
  | _, _ => none

section Lemmas

variable {A : List String} {m : Nat} {δ : String → Nat}

theorem idxBelow_filter {I : List (String × Nat)} {rs : RustState} (h : IdxBelow I m rs)
    (y : String) (v : Nat) : IdxBelow (I.filter (·.1 != y)) m (rsSetScalar rs y v) := by
  intro p hp
  have hp' := List.mem_filter.mp hp
  have hne : p.1 ≠ y := by simpa using hp'.2
  simpa [rsSetScalar, hne] using h p hp'.1

theorem idxBelow_cons {I : List (String × Nat)} {rs : RustState} (h : IdxBelow I m rs)
    (y : String) {v d : Nat} (hv : v < m + d) :
    IdxBelow ((y, d) :: I.filter (·.1 != y)) m (rsSetScalar rs y v) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simpa [rsSetScalar] using hv
  · exact idxBelow_filter h y v p hp

theorem arrLong_setScalar {rs : RustState} (h : ArrLong A m δ rs) (y : String) (v : Nat) :
    ArrLong A m δ (rsSetScalar rs y v) := h

theorem arrLong_setTower_not {rs : RustState} (h : ArrLong A m δ rs) {y : String} (hy : y ∉ A)
    (v : Σ t : TowerType, RustVal t) : ArrLong A m δ (rsSetTower rs y v) := by
  intro a ha n w hw
  have hne : a ≠ y := fun e => hy (e ▸ ha)
  simp only [rsSetTower, beq_iff_eq, hne, if_false] at hw
  exact h a ha n w hw

theorem idxBelow_setTower {I : List (String × Nat)} {rs : RustState} (h : IdxBelow I m rs)
    (y : String) (v : Σ t : TowerType, RustVal t) : IdxBelow I m (rsSetTower rs y v) := h

theorem arrLong_setTower_long {rs : RustState} (h : ArrLong A m δ rs) (y : String)
    {t : TowerType} (ht : longTyB (m + δ y) t = true) (v : RustVal t) :
    ArrLong A m δ (rsSetTower rs y ⟨t, v⟩) := by
  intro a ha n w hw
  by_cases hay : a = y
  · subst hay
    simp only [rsSetTower, beq_self_eq_true, if_true, Option.some.injEq] at hw
    have e := (Sigma.mk.inj_iff.mp hw).1
    subst e
    simpa [longTyB] using ht
  · simp only [rsSetTower, beq_iff_eq, hay, if_false] at hw
    exact h a ha n w hw

/-- An access at an index name of offset `d ≤ δ a` into an array `a` of `A` is in bounds. -/
theorem inb_of_idxOf (V : ArrView L) (hV : ∀ n v k, k < n → V.inb n v k)
    {I : List (String × Nat)} {rs : RustState} {i a : String}
    (hi : (idxOf I i).any (· ≤ δ a) = true) (hI : IdxBelow I m rs) (hA : ArrLong A m δ rs)
    (ha : a ∈ A) (n : Nat) (v : RustVal (.TArr n .TU64))
    (hv : rs.rsTower a = some ⟨.TArr n .TU64, v⟩) : V.inb n v (rs.rsScalar i) := by
  cases hd : idxOf I i with
  | none => rw [hd] at hi; cases hi
  | some d =>
      rw [hd] at hi
      have hdle : d ≤ δ a := by simpa using hi
      have h1 := idxOf_sound hd hI
      have h2 := hA a ha n v hv
      exact hV n v _ (by omega)

end Lemmas

/-- **Soundness of the trip-body check.** Let `inbB A m δ I c = some I'`, and let the view
    accept every index below the length of the array. From a state whose names of `I` hold
    values below `m` plus their offsets and whose arrays `a` of `A` hold at least `m + δ a`
    words, every access of a run of `c` is in bounds (`ArrRun`), and every final state of `c`
    keeps both properties, at the index names `I'`. -/
theorem inbB_sound (V : ArrView L) (hV : ∀ n v k, k < n → V.inb n v k) {A : List String}
    {m : Nat} {δ : String → Nat} : ∀ (c : LowCT) (I I' : List (String × Nat)) (rs : RustState),
    inbB A m δ I c = some I' → IdxBelow I m rs → ArrLong A m δ rs →
    ArrRun (N := N) V c rs ∧
      ∀ rs', RustExec N L c rs rs' → IdxBelow I' m rs' ∧ ArrLong A m δ rs' := by
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
      simp only [inbB] at h
      split at h
      · rename_i d he
        split at h
        · rename_i hm
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨offRange_of_idxOff he hI hm, fun rs' hx => ?_⟩
          cases hx
          exact ⟨idxBelow_cons hI y (idxOff_sound he hI), arrLong_setScalar hA y _⟩
        · cases h
      · split at h
        · cases h
        · rename_i hoff
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨offRange_of_not_isOffB (by simpa using hoff) rs, fun rs' hx => ?_⟩
          cases hx
          exact ⟨idxBelow_filter hI y _, arrLong_setScalar hA y _⟩
  | RArrLoad dst src i =>
      intro I I' rs h hI hA
      simp only [inbB] at h
      split at h
      · rename_i hc
        obtain ⟨hi, hs, hd⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun n v hv => inb_of_idxOf V hV hi hI hA hs n v hv, fun rs' hx => ?_⟩
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
        refine ⟨fun n v hv => inb_of_idxOf V hV hi hI hA hs n v hv, fun rs' hx => ?_⟩
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
  | RCall f d args =>
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
    trip body passes `inbB` from the index `x` at offset `0`. -/
def loopInbB (A : List String) (m : Nat) (δ : String → Nat) (n : String) : LowCT → Bool
  | .RLetU64Zero y b => y != n && loopInbB A m δ n b
  | .RForRuntime x (.SVar n') body => n' == n && (inbB A m δ [(x, 0)] body).isSome
  | _ => false

theorem idxBelow_trip {m t : Nat} (x : String) (r : RustState) (ht : t < m) :
    IdxBelow [(x, 0)] m (rsSetScalar r x t) := by
  intro p hp
  rw [List.mem_singleton.mp hp]
  simpa [rsSetScalar] using ht

/-- Every state a run of `k ≤ m` trips of an accepted trip body reaches keeps `ArrLong`. -/
theorem arrLong_rFor (V : ArrView L) (hV : ∀ n v k, k < n → V.inb n v k) {A : List String}
    {m : Nat} {δ : String → Nat} {x : String} {body : LowCT} {I' : List (String × Nat)}
    (hb : inbB A m δ [(x, 0)] body = some I') :
    ∀ (k : Nat) (rs r : RustState), k ≤ m → ArrLong A m δ rs →
      RustExec N L (.RFor x k body) rs r → ArrLong A m δ r := by
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
          exact ((inbB_sound (N := N) V hV body [(x, 0)] I' _ hb
            (idxBelow_trip x r1 (by omega)) (arrLong_setScalar hA1 x k)).2 r hx2).2

/-- **The bounds lemma.** Let the program pass `loopInbB A m δ n`, and let the view accept every
    index below the length of the array. From every state whose count `n` is at most `m` and
    whose arrays `a` of `A` hold at least `m + δ a` words, the run of the program is in bounds
    (`ArrRunL`): trip `t` indexes by `t + d < n + d ≤ m + δ a`. -/
theorem arrRunL_of_loopInbB (V : ArrView L) (hV : ∀ n v k, k < n → V.inb n v k)
    {A : List String} {m : Nat} {δ : String → Nat} {n : String} :
    ∀ (c : LowCT) (rs : RustState), loopInbB A m δ n c = true → rs.rsScalar n ≤ m →
      ArrLong A m δ rs → ArrRunL (N := N) V c rs := by
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
          exact (inbB_sound (N := N) V hV body [(x, 0)] I' _ hb
            (idxBelow_trip x r (by omega)) (arrLong_setScalar hA' x t)).1
      | _ => simp [loopInbB] at h
  | _ => intro rs h; simp [loopInbB] at h

end CatCrypt.Crypto.Hax
