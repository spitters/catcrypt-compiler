/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit

/-!
# The image class under the rewrites of a pass

The image check `physImgB slotArr body` (`JasminLsemAddrImage`) reads a body at each position
`k` through two scans of the prefix `body.take k`: the reload scan `reloadOf` behind `accArr`,
which `accOkB` reads at an indexed access, and the entry scan `entryRegB`, which `slotWriteB`
reads at a write of an array slot. This module gives the lemmas by which a pass that deletes,
rewrites, inserts or expands instructions keeps the class.

The reload scan of a body `a ++ c` from a position inside `c` either ends inside `c`, with the
result of the scan of `c` alone, or leaves `c` carrying a name `y` and continues as the scan of
`a` for `y` (`scanExit`, `reloadOf_append_scanExit`). A pass keeps the class when every scan
of an access in its output resolves whenever the corresponding scan of its input resolves,
and every entry scan of its output holds whenever the corresponding one of its input holds
(`physImgB_of_embed`).

A pass that deletes instructions is described by its marks `M : List (Linstr × Bool)`, the
input `M.map Prod.fst` and the output `(M.filter (fun p => !p.2)).map Prod.fst` (the
instructions marked `false`). The entry scan of the output is a sublist of that of the input,
so only the reload scans need a condition on the deleted instructions.

## Main results

* `scanExit`, `reloadOf_append_scanExit`: the reload scan of a concatenation.
* `reloadOf_drop`, `reloadOf_drop_of_not_movInto`: deleting an instruction that is not a move
  into the name the scan carries across it keeps the result of the scan.
* `physImgB_of_embed`: the class of a body each of whose positions either is no access and
  no unchecked slot write, or corresponds to a position of a body in the class at which the
  scans resolve at least as often.
* `physImgB_kept_of_transparent`: deleting instructions after each of which every reload scan
  gives a result already found in front of it (a redundant reload, an instruction that writes
  no name a scan resolves) keeps the class.
* `physImgB_kept_of_passed`: deleting instructions that are no moves into a name the reload
  scan of a kept access carries across them keeps the class.
* `physImgB_sublist_of`: a sublist of a body in the class that keeps every move is in the
  class.
* `physImgB_flatMap`, `physImgB_movePrefix_flatMap`: a body expanded block by block, each
  block resolving its accesses inside itself and writing no array slot, after a prefix of
  saves.
* `physImgB_replace`: a segment replaced by one with no access and no array-slot destination,
  in front of a rest that writes no array slot, when every name a later scan carries out of the
  rest resolves after the new segment whenever it resolves after the old one.
* `physImgB_rewrite`, `physImgB_insert`: an instruction rewritten into, or inserted as, a
  non-move operation with no access and no array-slot destination that writes no name a later
  scan carries across it, ahead of a rest that writes no array slot.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The reload scan of a concatenation -/

/-- The name that the reload scan `reloadOf slotArr c k x` carries when it reaches the start
    of `c`, or `none` when the scan ends inside `c` (at a reload, at an instruction writing
    the carried name or an array slot, or at an instruction other than an `Lopn`). The steps
    are those of `reloadOf`. -/
def scanExit (slotArr : String → Option (String × Nat)) (c : Lcmd) : Nat → String →
    Option String
  | 0, x => some x
  | k + 1, x =>
      match c[k]? with
      | some j =>
          match slotMov? j.li_i with
          | some (d, q) =>
              if d = x then
                (if (slotArr q).isNone && gpNameB q then scanExit slotArr c k q else none)
              else if (slotArr d).isNone then scanExit slotArr c k x else none
          | none =>
              match j.li_i with
              | .Lopn ds _ _ =>
                  if ds.any (dstHitB slotArr x) then none else scanExit slotArr c k x
              | _ => none
      | none => none

/-- **The reload scan of a concatenation.** The scan of `a ++ c` from position `k` of `c` is
    the scan of `a` for the name the scan of `c` carries out of `c`, or, when the scan ends
    inside `c`, the scan of `c` alone. -/
theorem reloadOf_append_scanExit (slotArr : String → Option (String × Nat)) (a c : Lcmd) :
    ∀ (k : Nat) (x : String), reloadOf slotArr (a ++ c) (a.length + k) x =
      match scanExit slotArr c k x with
      | some y => reloadOf slotArr a a.length y
      | none => reloadOf slotArr c k x
  | 0, x => by
    simpa [scanExit] using reloadOf_append_left slotArr a c a.length x le_rfl
  | k + 1, x => by
    have ih := reloadOf_append_scanExit slotArr a c k
    have hg : (a ++ c)[a.length + k]? = c[k]? := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rw [show a.length + (k + 1) = (a.length + k) + 1 from rfl]
    simp only [reloadOf, scanExit, hg]
    cases c[k]? with
    | none => rfl
    | some j =>
      simp only
      cases slotMov? j.li_i with
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only
        split_ifs <;> first | exact ih _ | rfl
      | none =>
        simp only
        cases j.li_i with
        | Lopn ds o ss =>
          simp only
          split_ifs
          · rfl
          · exact ih _
        | _ => rfl

/-- The reload scan of a body with a final instruction `j`, read through one step of the scan
    at `j`. -/
theorem reloadOf_snoc (slotArr : String → Option (String × Nat)) (a : Lcmd) (j : Linstr)
    (x : String) : reloadOf slotArr (a ++ [j]) (a.length + 1) x =
      match scanExit slotArr [j] 1 x with
      | some y => reloadOf slotArr a a.length y
      | none => reloadOf slotArr [j] 1 x :=
  reloadOf_append_scanExit slotArr a [j] 1 x

/-- One step of the scan at an instruction that is no move into the carried name `y`: the scan
    passes it carrying `y`, or ends without a result. -/
theorem scanStep_of_not_movInto {j : Linstr} {y : String}
    (hj : ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ y) :
    (scanExit slotArr [j] 1 y = some y ∨ scanExit slotArr [j] 1 y = none) ∧
      reloadOf slotArr [j] 1 y = none := by
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d, s⟩ := p
    have hd := hj d s hm
    simp only [scanExit, reloadOf, List.getElem?_cons_zero, hm, if_neg hd]
    split_ifs <;> simp
  | none =>
    simp only [scanExit, reloadOf, List.getElem?_cons_zero, hm]
    cases j.li_i with
    | Lopn ds o ss => simp only; split_ifs <;> simp
    | _ => simp

/-- A final instruction that is no move into `y` adds no result to the scan for `y`. -/
theorem reloadOf_snoc_of_not_movInto {a : Lcmd} {j : Linstr} {y q : String}
    (hj : ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ y)
    (h : reloadOf slotArr (a ++ [j]) (a.length + 1) y = some q) :
    reloadOf slotArr a a.length y = some q := by
  rw [reloadOf_snoc] at h
  obtain ⟨hs | hs, hr⟩ := scanStep_of_not_movInto (slotArr := slotArr) hj
  · rwa [hs] at h
  · rw [hs, hr] at h; cases h

/-- **Deleting an instruction.** Let the scan of `c` from position `k` carry every name `y`
    it carries out of `c` to the instruction `j` in front of `c` such that `j` adds no result
    for `y`. Then deleting `j` from `a ++ j :: c` keeps the result of the scan from the
    corresponding position. -/
theorem reloadOf_drop {a c : Lcmd} {j : Linstr} {k : Nat} {x q : String}
    (hj : ∀ y, scanExit slotArr c k x = some y → ∀ q', reloadOf slotArr (a ++ [j])
      (a.length + 1) y = some q' → reloadOf slotArr a a.length y = some q')
    (h : reloadOf slotArr (a ++ j :: c) (a.length + 1 + k) x = some q) :
    reloadOf slotArr (a ++ c) (a.length + k) x = some q := by
  have e : a ++ j :: c = (a ++ [j]) ++ c := by simp
  rw [e, show a.length + 1 + k = (a ++ [j]).length + k by simp,
    reloadOf_append_scanExit] at h
  rw [reloadOf_append_scanExit]
  cases hs : scanExit slotArr c k x with
  | none => rw [hs] at h; exact h
  | some y =>
    rw [hs] at h
    rw [List.length_append, List.length_singleton] at h
    exact hj y hs q h

/-- Deleting an instruction that is no move into any name the scan carries across it keeps
    the result of the scan. -/
theorem reloadOf_drop_of_not_movInto {a c : Lcmd} {j : Linstr} {k : Nat} {x q : String}
    (hj : ∀ y, scanExit slotArr c k x = some y →
      ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ y)
    (h : reloadOf slotArr (a ++ j :: c) (a.length + 1 + k) x = some q) :
    reloadOf slotArr (a ++ c) (a.length + k) x = some q :=
  reloadOf_drop (fun y hy _ h' => reloadOf_snoc_of_not_movInto (hj y hy) h') h

/-- The carried name of a scan up to position `k` reads only the first `k` instructions. -/
theorem scanExit_append_left (slotArr : String → Option (String × Nat)) (a c : Lcmd) :
    ∀ (k : Nat) (x : String), k ≤ a.length →
      scanExit slotArr (a ++ c) k x = scanExit slotArr a k x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    have ih := fun y => scanExit_append_left slotArr a c k y (by omega)
    simp only [scanExit, List.getElem?_append_left (by omega : k < a.length), ih]

/-- The carried name of a scan of a segment with a final instruction `j`, read through one step
    of the scan at `j`. -/
theorem scanExit_snoc (slotArr : String → Option (String × Nat)) (c : Lcmd) (j : Linstr)
    (x : String) : scanExit slotArr (c ++ [j]) (c.length + 1) x =
      match scanExit slotArr [j] 1 x with
      | some y => scanExit slotArr c c.length y
      | none => none := by
  have hg : (c ++ [j])[c.length]? = some j := by simp
  have e := fun y => scanExit_append_left slotArr c [j] c.length y le_rfl
  simp only [scanExit, hg, List.getElem?_cons_zero, e]
  cases slotMov? j.li_i with
  | some p =>
    obtain ⟨d, q⟩ := p
    simp only
    split_ifs <;> rfl
  | none =>
    simp only
    cases j.li_i with
    | Lopn ds o ss => simp only; split_ifs <;> rfl
    | _ => rfl

/-! ## 2. Positions that correspond -/

theorem accArr_append_left (slotArr : String → Option (String × Nat)) (a c : Lcmd) (k : Nat)
    (x : String) (hk : k ≤ a.length) : accArr slotArr (a ++ c) k x = accArr slotArr a k x := by
  simp [accArr, reloadOf_append_left slotArr a c k x hk]

/-- The array scan of a body with a final instruction `j` is monotone in the scan of the body
    in front of `j`. -/
theorem accArr_snoc_mono {A B : Lcmd} {j : Linstr}
    (hAB : ∀ y, (accArr slotArr A A.length y).isSome = true →
      (accArr slotArr B B.length y).isSome = true) (x : String)
    (h : (accArr slotArr (A ++ [j]) (A.length + 1) x).isSome = true) :
    (accArr slotArr (B ++ [j]) (B.length + 1) x).isSome = true := by
  simp only [accArr] at hAB h ⊢
  rw [reloadOf_snoc] at h ⊢
  cases hs : scanExit slotArr [j] 1 x with
  | some y => rw [hs] at h; exact hAB y h
  | none => rw [hs] at h; exact h

/-- `accOkB` reads the body only through the array scan of the base of an access. -/
theorem accOkB_of_base {b1 b2 : Lcmd} {k1 k2 : Nat} {i : LinstrR}
    (hmono : ∀ x, (∃ ds o y ss, i = .Lopn ds o (.arrIdx x y 8 :: ss)) →
      (accArr slotArr b1 k1 x).isSome = true → (accArr slotArr b2 k2 x).isSome = true)
    (h : accOkB slotArr b1 k1 i = true) : accOkB slotArr b2 k2 i = true := by
  revert h hmono
  unfold accOkB
  split
  · rename_i ds o ss
    split_ifs
    · split
      · rename_i heq
        intro hm h; exact hm _ ⟨_, _, _, _, heq⟩ h
      · simp
    · split
      · intro hm h
        rw [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, hm _ ⟨_, _, _, _, rfl⟩ h.2⟩
      · simp
    · simp
  · simp

/-- `slotWriteB` reads the body only through the entry scan `entryRegB`. -/
theorem slotWriteB_mono {b1 b2 : Lcmd} {k1 k2 : Nat}
    (he : ∀ R, entryRegB b1 k1 R = true → entryRegB b2 k2 R = true) (i : LinstrR)
    (h : slotWriteB slotArr b1 k1 i = true) : slotWriteB slotArr b2 k2 i = true := by
  cases i with
  | Lopn ds o ss =>
    simp only [slotWriteB, List.all_eq_true] at h ⊢
    intro x hx
    have hx' := h x hx
    cases x with
    | reg q =>
      simp only [Bool.or_eq_true] at hx' ⊢
      refine hx'.imp id fun h' => ?_
      revert h'
      cases slotMov? (.Lopn ds o ss) with
      | none => simp
      | some p => simp only [Bool.and_eq_true]; exact fun ⟨h1, h2⟩ => ⟨h1, he _ h2⟩
    | _ => exact hx'
  | _ => rfl

/-- The entry scan holds at a position whose prefix is a sublist of a prefix at which it
    holds. -/
theorem entryRegB_of_take_sublist {b1 b2 : Lcmd} {k1 k2 : Nat}
    (hs : (b2.take k2).Sublist (b1.take k1))
    {R : String} (h : entryRegB b1 k1 R = true) : entryRegB b2 k2 R = true := by
  unfold entryRegB at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun j hj => h j (hs.subset hj)

/-- **The class through corresponding positions.** Let every instruction of `b'` either be no
    access with a satisfied `slotWriteB`, or occur at a position `m` of `b` at which the array
    scan of each base of the instruction resolves in `b` only if it resolves in `b'`, and the
    entry scan holds in `b` only if it holds in `b'`. Then `physImgB slotArr b` gives
    `physImgB slotArr b'`. -/
theorem physImgB_of_embed {b b' : Lcmd} (h : physImgB slotArr b = true)
    (hk : ∀ k i, b'[k]? = some i →
      (isAccB i.li_i = false ∧ slotWriteB slotArr b' k i.li_i = true) ∨
      ∃ m, b[m]? = some i ∧
        (∀ x, (∃ ds o y ss, i.li_i = .Lopn ds o (.arrIdx x y 8 :: ss)) →
          (accArr slotArr b m x).isSome = true → (accArr slotArr b' k x).isSome = true) ∧
        ((∀ R, entryRegB b m R = true → entryRegB b' k R = true) ∨
          slotWriteB slotArr b' k i.li_i = true)) :
    physImgB slotArr b' = true := by
  have hb : ∀ m i, b[m]? = some i →
      accOkB slotArr b m i.li_i = true ∧ slotWriteB slotArr b m i.li_i = true := by
    intro m i hm
    have hlt : m < b.length := (List.getElem?_eq_some_iff.mp hm).1
    have := List.all_eq_true.mp h m (List.mem_range.mpr hlt)
    rw [hm] at this
    simpa using this
  unfold physImgB
  rw [List.all_eq_true]
  intro k _
  cases hk' : b'[k]? with
  | none => rfl
  | some i =>
    simp only [Bool.and_eq_true]
    rcases hk k i hk' with ⟨ha, hw⟩ | ⟨m, hm, hacc, hent⟩
    · exact ⟨accOkB_of_not_acc _ _ _ ha, hw⟩
    · obtain ⟨h1, h2⟩ := hb m i hm
      exact ⟨accOkB_of_base hacc h1, hent.elim (fun he => slotWriteB_mono he _ h2) id⟩

/-! ## 3. Deleting marked instructions -/

/-- A kept instruction of a marked body: the marks split at it, with the kept instructions in
    front of it numbering its position in the output. -/
theorem kept_getElem?_split : ∀ (M : List (Linstr × Bool)) (k : Nat) (i : Linstr),
    ((M.filter (fun p => !p.2)).map Prod.fst)[k]? = some i →
      ∃ M₁ M₂, M = M₁ ++ (i, false) :: M₂ ∧
        ((M₁.filter (fun p => !p.2)).map Prod.fst).length = k
  | [], k, i, h => by simp at h
  | (j, true) :: M, k, i, h => by
    simp only [List.filter_cons, Bool.not_true, Bool.false_eq_true, if_false] at h
    obtain ⟨M₁, M₂, rfl, hl⟩ := kept_getElem?_split M k i h
    exact ⟨(j, true) :: M₁, M₂, rfl, by simpa using hl⟩
  | (j, false) :: M, 0, i, h => by
    simp only [List.filter_cons, Bool.not_false, if_true, List.map_cons,
      List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨[], M, rfl, rfl⟩
  | (j, false) :: M, k + 1, i, h => by
    simp only [List.filter_cons, Bool.not_false, if_true, List.map_cons,
      List.getElem?_cons_succ] at h
    obtain ⟨M₁, M₂, rfl, hl⟩ := kept_getElem?_split M k i h
    exact ⟨(j, false) :: M₁, M₂, rfl, by simp [hl]⟩

/-- **The class of the kept instructions, by prefixes.** Let `M` mark a body in the class, and
    let the array scan of each base of every kept instruction resolve in front of it in the
    output whenever it resolves in front of it in the input. Then the output is in the
    class. -/
theorem physImgB_kept_of_prefix {M : List (Linstr × Bool)}
    (h : physImgB slotArr (M.map Prod.fst) = true)
    (hpre : ∀ M₁ M₂ i, M = M₁ ++ (i, false) :: M₂ → ∀ x,
      (∃ ds o y ss, i.li_i = .Lopn ds o (.arrIdx x y 8 :: ss)) →
      (accArr slotArr (M₁.map Prod.fst) M₁.length x).isSome = true →
      (accArr slotArr ((M₁.filter (fun p => !p.2)).map Prod.fst)
        ((M₁.filter (fun p => !p.2)).map Prod.fst).length x).isSome = true) :
    physImgB slotArr ((M.filter (fun p => !p.2)).map Prod.fst) = true := by
  refine physImgB_of_embed h fun k i hk => Or.inr ?_
  obtain ⟨M₁, M₂, rfl, hl⟩ := kept_getElem?_split M k i hk
  have hs : (M₁ ++ (i, false) :: M₂).map Prod.fst =
      M₁.map Prod.fst ++ i :: M₂.map Prod.fst := by
    simp
  have hk' : ((M₁ ++ (i, false) :: M₂).filter (fun p => !p.2)).map Prod.fst =
      (M₁.filter (fun p => !p.2)).map Prod.fst ++ i :: (M₂.filter (fun p => !p.2)).map
        Prod.fst := by
    simp [List.filter_append]
  have hl1 : (M₁.map Prod.fst).length = M₁.length := List.length_map _
  refine ⟨M₁.length, ?_, fun x hx ha => ?_, Or.inl fun R hR => ?_⟩
  · rw [hs, List.getElem?_append_right (by omega), hl1, Nat.sub_self]; rfl
  · rw [hs, accArr_append_left _ _ _ _ _ (by omega)] at ha
    rw [hk', ← hl, accArr_append_left _ _ _ _ _ le_rfl]
    exact hpre M₁ M₂ i rfl x hx ha
  · refine entryRegB_of_take_sublist ?_ hR
    rw [hs, hk', List.take_left' hl, List.take_left' hl1]
    exact (List.filter_sublist).map _

/-- The array scans of the kept instructions of a marked body, when every deleted instruction
    adds no resolving scan: whenever a scan for some name resolves after a deleted instruction,
    it resolves in front of it. -/
theorem accArr_kept_of_transparent : ∀ (M N : List (Linstr × Bool)),
    (∀ p j, M[p]? = some (j, true) → ∀ y,
      (accArr slotArr ((M ++ N).map Prod.fst) (p + 1) y).isSome = true →
      (accArr slotArr ((M ++ N).map Prod.fst) p y).isSome = true) →
    ∀ x, (accArr slotArr (M.map Prod.fst) M.length x).isSome = true →
      (accArr slotArr ((M.filter (fun p => !p.2)).map Prod.fst)
        ((M.filter (fun p => !p.2)).map Prod.fst).length x).isSome = true := by
  intro M
  induction M using List.reverseRecOn with
  | nil => intro N _ x h; simp [accArr, reloadOf] at h
  | append_singleton M e ih =>
    intro N htr x h
    obtain ⟨j, b⟩ := e
    have hl1 : (M.map Prod.fst).length = M.length := List.length_map _
    have htr' : ∀ p j', M[p]? = some (j', true) → ∀ y,
        (accArr slotArr ((M ++ (j, b) :: N).map Prod.fst) (p + 1) y).isSome = true →
        (accArr slotArr ((M ++ (j, b) :: N).map Prod.fst) p y).isSome = true := by
      intro p j' hp y hy
      have hlt : p < M.length := (List.getElem?_eq_some_iff.mp hp).1
      have hp' : (M ++ [(j, b)])[p]? = some (j', true) := by
        rw [List.getElem?_append_left hlt]; exact hp
      have e : M ++ (j, b) :: N = (M ++ [(j, b)]) ++ N := by simp
      rw [e] at hy ⊢
      exact htr p j' hp' y hy
    have ih' := ih ((j, b) :: N) htr'
    have hsrc : (M ++ [(j, b)]).map Prod.fst = M.map Prod.fst ++ [j] := by simp
    rw [hsrc, List.length_append, List.length_singleton, ← hl1] at h
    cases b with
    | true =>
      have hkept : ((M ++ [(j, true)]).filter (fun p => !p.2)).map Prod.fst =
          (M.filter (fun p => !p.2)).map Prod.fst := by simp [List.filter_append]
      rw [hkept]
      have hfull : ((M ++ [(j, true)]) ++ N).map Prod.fst =
          (M.map Prod.fst ++ [j]) ++ N.map Prod.fst := by simp
      have h2 := htr M.length j (by simp) x (by
        rw [hfull, accArr_append_left _ _ _ _ _ (by simp)]; rwa [← hl1])
      rw [hfull, accArr_append_left _ _ _ _ _ (by simp),
        accArr_append_left _ _ _ _ _ (by simp)] at h2
      exact ih' x h2
    | false =>
      have hkept : ((M ++ [(j, false)]).filter (fun p => !p.2)).map Prod.fst =
          (M.filter (fun p => !p.2)).map Prod.fst ++ [j] := by simp [List.filter_append]
      rw [hkept, List.length_append, List.length_singleton]
      exact accArr_snoc_mono (fun y hy => ih' y (by rwa [hl1] at hy)) x h

/-- **Deleting transparent instructions.** Let `M` mark a body in the class such that after
    every deleted instruction (at position `p`) a scan for a name resolves only if it resolves
    in front of the instruction. Then the kept instructions form a body in the class. -/
theorem physImgB_kept_of_transparent {M : List (Linstr × Bool)}
    (h : physImgB slotArr (M.map Prod.fst) = true)
    (htr : ∀ p j, M[p]? = some (j, true) → ∀ y,
      (accArr slotArr (M.map Prod.fst) (p + 1) y).isSome = true →
      (accArr slotArr (M.map Prod.fst) p y).isSome = true) :
    physImgB slotArr ((M.filter (fun p => !p.2)).map Prod.fst) = true := by
  refine physImgB_kept_of_prefix h fun M₁ M₂ i hM x _ ha => ?_
  subst hM
  refine accArr_kept_of_transparent M₁ ((i, false) :: M₂) (fun p j hp y hy => ?_) x ha
  have hlt : p < M₁.length := (List.getElem?_eq_some_iff.mp hp).1
  exact htr p j (by rw [List.getElem?_append_left hlt]; exact hp) y hy

/-- An instruction that is no move into `y` adds no resolving scan for `y`. -/
theorem accArr_succ_of_not_movInto {b : Lcmd} {p : Nat} {j : Linstr} {y : String}
    (hb : b[p]? = some j) (hj : ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ y)
    (h : (accArr slotArr b (p + 1) y).isSome = true) :
    (accArr slotArr b p y).isSome = true := by
  unfold accArr at h ⊢
  cases hm : slotMov? j.li_i with
  | some ds =>
    obtain ⟨d, s⟩ := ds
    rw [reloadOf_succ_some hb hm, if_neg (hj d s hm)] at h
    split_ifs at h
    · exact h
    · simp at h
  | none =>
    cases hx : j.li_i with
    | Lopn ds o ss =>
      rw [reloadOf_succ_lopn hb hm hx] at h
      split_ifs at h
      · simp at h
      · exact h
    | _ =>
      rw [reloadOf_succ_other hb hm (by intro ds o ss he; rw [hx] at he; cases he)] at h
      simp at h

/-- The array scans of the kept instructions of a marked body, when no deleted instruction is a
    move into the name the scan of the input carries across it. -/
theorem accArr_kept_of_passed : ∀ (M : List (Linstr × Bool)) (x : String),
    (∀ p j, M[p]? = some (j, true) → ∀ y,
      scanExit slotArr ((M.map Prod.fst).drop (p + 1)) (M.length - (p + 1)) x = some y →
      ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ y) →
    (accArr slotArr (M.map Prod.fst) M.length x).isSome = true →
    (accArr slotArr ((M.filter (fun p => !p.2)).map Prod.fst)
      ((M.filter (fun p => !p.2)).map Prod.fst).length x).isSome = true := by
  intro M
  induction M using List.reverseRecOn with
  | nil => intro x _ h; simp [accArr, reloadOf] at h
  | append_singleton M e ih =>
    intro x hps h
    obtain ⟨j, b⟩ := e
    have hl1 : (M.map Prod.fst).length = M.length := List.length_map _
    have hsrc : (M ++ [(j, b)]).map Prod.fst = M.map Prod.fst ++ [j] := by simp
    have tr : ∀ y', scanExit slotArr [j] 1 x = some y' → ∀ p j', M[p]? = some (j', true) →
        ∀ y, scanExit slotArr ((M.map Prod.fst).drop (p + 1)) (M.length - (p + 1)) y' = some y →
        ∀ d s, slotMov? j'.li_i = some (d, s) → d ≠ y := by
      intro y' hy' p j' hp y hy
      have hlt : p < M.length := (List.getElem?_eq_some_iff.mp hp).1
      refine hps p j' (by rw [List.getElem?_append_left hlt]; exact hp) y ?_
      have hd : ((M ++ [(j, b)]).map Prod.fst).drop (p + 1) =
          (M.map Prod.fst).drop (p + 1) ++ [j] := by
        rw [hsrc, List.drop_append_of_le_length (by omega)]
      have hn : (M ++ [(j, b)]).length - (p + 1) =
          ((M.map Prod.fst).drop (p + 1)).length + 1 := by simp; omega
      rw [hd, hn, scanExit_snoc, hy']
      rwa [List.length_drop, hl1]
    rw [hsrc] at h
    unfold accArr at h
    rw [List.length_append, List.length_singleton, ← hl1, reloadOf_snoc] at h
    cases b with
    | true =>
      have hkept : ((M ++ [(j, true)]).filter (fun p => !p.2)).map Prod.fst =
          (M.filter (fun p => !p.2)).map Prod.fst := by simp [List.filter_append]
      rw [hkept]
      have hj := hps M.length j (by simp) x (by simp [scanExit])
      obtain ⟨hs | hs, hr⟩ := scanStep_of_not_movInto (slotArr := slotArr) hj
      · simp only [hs] at h
        exact ih x (tr x hs) (by unfold accArr; rwa [hl1] at h)
      · simp only [hs, hr] at h; simp at h
    | false =>
      have hkept : ((M ++ [(j, false)]).filter (fun p => !p.2)).map Prod.fst =
          (M.filter (fun p => !p.2)).map Prod.fst ++ [j] := by simp [List.filter_append]
      rw [hkept]
      unfold accArr
      rw [List.length_append, List.length_singleton, reloadOf_snoc]
      cases hs : scanExit slotArr [j] 1 x with
      | some y' =>
        simp only [hs] at h ⊢
        have := ih y' (tr y' hs) (by unfold accArr; rwa [hl1] at h)
        exact this
      | none => simp only [hs] at h ⊢; exact h

/-- **Deleting instructions the scans pass.** Let `M` mark a body in the class such that no
    deleted instruction is a move into a name that the reload scan of a base of a later kept
    instruction carries across it. Then the kept instructions form a body in the class. -/
theorem physImgB_kept_of_passed {M : List (Linstr × Bool)}
    (h : physImgB slotArr (M.map Prod.fst) = true)
    (hps : ∀ m i, M[m]? = some (i, false) → ∀ x,
      (∃ ds o y ss, i.li_i = .Lopn ds o (.arrIdx x y 8 :: ss)) →
      (accArr slotArr (M.map Prod.fst) m x).isSome = true →
      ∀ p j, p < m → M[p]? = some (j, true) → ∀ y,
        scanExit slotArr (((M.map Prod.fst).take m).drop (p + 1)) (m - (p + 1)) x = some y →
        ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ y) :
    physImgB slotArr ((M.filter (fun p => !p.2)).map Prod.fst) = true := by
  refine physImgB_kept_of_prefix h fun M₁ M₂ i hM x hx ha => ?_
  subst hM
  have hl1 : (M₁.map Prod.fst).length = M₁.length := List.length_map _
  have hs : (M₁ ++ (i, false) :: M₂).map Prod.fst =
      M₁.map Prod.fst ++ i :: M₂.map Prod.fst := by
    simp
  refine accArr_kept_of_passed M₁ x (fun p j hp y hy => ?_) ha
  have hlt : p < M₁.length := (List.getElem?_eq_some_iff.mp hp).1
  refine hps M₁.length i (by simp) x hx ?_ p j hlt
    (by rw [List.getElem?_append_left hlt]; exact hp) y ?_
  · rw [hs, accArr_append_left _ _ _ _ _ (by omega)]; exact ha
  · rw [hs, List.take_left' hl1]; exact hy

/-- A sublist is the output of a marking of the body. -/
theorem marks_of_sublist {b' b : Lcmd} (h : b'.Sublist b) :
    ∃ M : List (Linstr × Bool), M.map Prod.fst = b ∧
      (M.filter (fun p => !p.2)).map Prod.fst = b' := by
  induction h with
  | slnil => exact ⟨[], rfl, rfl⟩
  | cons a _ ih =>
    obtain ⟨M, h1, h2⟩ := ih
    exact ⟨(a, true) :: M, by simp [h1], by simp [h2]⟩
  | cons_cons a _ ih =>
    obtain ⟨M, h1, h2⟩ := ih
    exact ⟨(a, false) :: M, by simp [h1], by simp [h2]⟩

/-- The instructions of a marked body that satisfy `P` are those kept and those deleted. -/
theorem marks_filter_length (P : Linstr → Bool) : ∀ M : List (Linstr × Bool),
    ((M.map Prod.fst).filter P).length =
      (((M.filter (fun p => !p.2)).map Prod.fst).filter P).length +
        (((M.filter (fun p => p.2)).map Prod.fst).filter P).length
  | [] => rfl
  | (j, b) :: M => by
    have ih := marks_filter_length P M
    cases b <;> cases hP : P j <;> simp [hP, ih] <;> omega

/-- **A sublist that keeps every move.** A sublist `b'` of a body in the class with the moves
    (`slotMov?`) of `b` is in the class. -/
theorem physImgB_sublist_of {b' b : Lcmd} (hsub : b'.Sublist b)
    (hmov : b'.filter (fun j => (slotMov? j.li_i).isSome) =
      b.filter (fun j => (slotMov? j.li_i).isSome))
    (h : physImgB slotArr b = true) : physImgB slotArr b' = true := by
  obtain ⟨M, rfl, rfl⟩ := marks_of_sublist hsub
  refine physImgB_kept_of_transparent h fun p j hp y hy => ?_
  have hc := marks_filter_length (fun j => (slotMov? j.li_i).isSome) M
  rw [← hmov] at hc
  have h0 : (((M.filter (fun p => p.2)).map Prod.fst).filter
      (fun j => (slotMov? j.li_i).isSome)) = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hmem : j ∈ (M.filter (fun p => p.2)).map Prod.fst :=
    List.mem_map.mpr ⟨(j, true), List.mem_filter.mpr ⟨List.mem_of_getElem? hp, rfl⟩, rfl⟩
  have hnm : (slotMov? j.li_i).isSome = false := by
    rw [List.filter_eq_nil_iff] at h0
    simpa using h0 j hmem
  refine accArr_succ_of_not_movInto (j := j) (by simp [hp]) (fun d s hs => ?_) hy
  simp [hs] at hnm

/-! ## 4. Expanding and replacing instructions -/

/-- An instruction none of whose destinations is an array slot (`DstOk`) passes `slotWriteB`
    at every position. -/
theorem slotWriteB_of_dstOk {r : LinstrR} (h : DstOk slotArr r) (b : Lcmd) (k : Nat) :
    slotWriteB slotArr b k r = true := by
  cases r with
  | Lopn ds o ss =>
    unfold slotWriteB
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨h1, h2, h3⟩ := h ds o ss rfl x hx
    cases x with
    | reg q => simp [h1 q rfl]
    | arr q n => simp [h2 q n rfl]
    | arrIdx q j sc => simp [h3 q j sc rfl]
    | imm _ => rfl
  | _ => rfl

/-- **A body expanded block by block, after a prefix of saves.** Let the prefix `pre` meet the
    conditions of `physImgB_of_movePrefix`, and let every block `f a` resolve its accesses
    inside itself (`AccLocal`) and write no array slot (`DstOk`). Then
    `pre ++ l.flatMap f` is in the class. -/
theorem physImgB_movePrefix_flatMap {α : Type} {pre : Lcmd} {l : List α} {f : α → Lcmd}
    (hpre : ∀ j ∈ pre, (slotMov? j.li_i).isSome = true)
    (hsave : ∀ (k : Nat) (j : Linstr) (d R : String), pre[k]? = some j →
      slotMov? j.li_i = some (d, R) → (slotArr d).isSome = true → d = slotOfReg R ∧
        ∀ (m : Nat) (j' : Linstr) (d' s' : String), m < k → pre[m]? = some j' →
          slotMov? j'.li_i = some (d', s') → d' ≠ R)
    (hblk : ∀ a ∈ l, AccLocal slotArr (f a) ∧ ∀ r ∈ f a, DstOk slotArr r.li_i) :
    physImgB slotArr (pre ++ l.flatMap f) = true := by
  have hloc : AccLocal slotArr (l.flatMap f) := accLocal_flatMap fun a ha => (hblk a ha).1
  refine physImgB_of_movePrefix hpre hsave (fun j hj ds o ss hx x hxd => ?_) ?_
  · obtain ⟨a, ha, hj'⟩ := List.mem_flatMap.mp hj
    exact (hblk a ha).2 j hj' ds o ss hx x hxd
  · intro k i hk hb
    rw [List.getElem?_append_right hk] at hb
    refine accOkB_mono (accArr_isSome_mono ?_) _ (hloc (k - pre.length) i hb)
    intro x q hx
    have := reloadOf_append_right slotArr pre (l.flatMap f) _ x q hx
    rwa [Nat.add_sub_cancel' hk] at this

/-- **A body expanded block by block** (`physPositionEmit` and the allocator): every block
    resolving its accesses inside itself and writing no array slot gives the class. -/
theorem physImgB_flatMap {α : Type} {l : List α} {f : α → Lcmd}
    (hblk : ∀ a ∈ l, AccLocal slotArr (f a) ∧ ∀ r ∈ f a, DstOk slotArr r.li_i) :
    physImgB slotArr (l.flatMap f) = true := by
  simpa using physImgB_movePrefix_flatMap (pre := []) (by simp) (by simp) hblk

/-- The array scan of a body with a concatenation, by `reloadOf_append_scanExit`. -/
theorem accArr_append_scanExit (slotArr : String → Option (String × Nat)) (a c : Lcmd)
    (k : Nat) (x : String) : accArr slotArr (a ++ c) (a.length + k) x =
      match scanExit slotArr c k x with
      | some y => accArr slotArr a a.length y
      | none => accArr slotArr c k x := by
  unfold accArr
  rw [reloadOf_append_scanExit]
  cases scanExit slotArr c k x <;> rfl

/-- **Replacing a segment.** Let `A ++ L ++ C` be in the class, let the segment `L'` have no
    access and write no array slot, let `C` write no array slot, and let every name that the
    scan of a base of an instruction of `C` carries out of `C` resolve after `A ++ L'` whenever
    it resolves after `A ++ L`. Then `A ++ L' ++ C` is in the class. -/
theorem physImgB_replace {A L L' C : Lcmd} (h : physImgB slotArr (A ++ L ++ C) = true)
    (hL' : ∀ r ∈ L', isAccB r.li_i = false ∧ DstOk slotArr r.li_i)
    (hC : ∀ r ∈ C, DstOk slotArr r.li_i)
    (hscan : ∀ k i x, C[k]? = some i →
      (∃ ds o y ss, i.li_i = .Lopn ds o (.arrIdx x y 8 :: ss)) → ∀ y, scanExit slotArr C k x = some y →
      (accArr slotArr (A ++ L) (A ++ L).length y).isSome = true →
      (accArr slotArr (A ++ L') (A ++ L').length y).isSome = true) :
    physImgB slotArr (A ++ L' ++ C) = true := by
  refine physImgB_of_embed h fun k i hk => ?_
  rcases Nat.lt_or_ge k A.length with hA | hA
  · have e1 : (A ++ L' ++ C)[k]? = A[k]? := by
      rw [List.append_assoc, List.getElem?_append_left hA]
    refine Or.inr ⟨k, ?_, fun x _ ha => ?_, Or.inl fun R hR => ?_⟩
    · rw [List.append_assoc, List.getElem?_append_left hA, ← e1]; exact hk
    · rw [List.append_assoc, accArr_append_left _ _ _ _ _ hA.le] at ha
      rw [List.append_assoc, accArr_append_left _ _ _ _ _ hA.le]
      exact ha
    · refine entryRegB_of_take_sublist ?_ hR
      rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length hA.le,
        List.take_append_of_le_length hA.le]
  rcases Nat.lt_or_ge k (A ++ L').length with hL | hL
  · rw [List.append_assoc, List.getElem?_append_right hA,
      List.getElem?_append_left (by simp at hL; omega)] at hk
    obtain ⟨h1, h2⟩ := hL' i (List.mem_of_getElem? hk)
    exact Or.inl ⟨h1, slotWriteB_of_dstOk h2 _ _⟩
  · obtain ⟨k₀, rfl⟩ : ∃ k₀, k = (A ++ L').length + k₀ :=
      ⟨k - (A ++ L').length, by omega⟩
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hk
    refine Or.inr ⟨(A ++ L).length + k₀, ?_, fun x hx ha => ?_,
      Or.inr (slotWriteB_of_dstOk (hC i (List.mem_of_getElem? hk)) _ _)⟩
    · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hk
    · rw [accArr_append_scanExit] at ha ⊢
      cases hs : scanExit slotArr C k₀ x with
      | some y => rw [hs] at ha; exact hscan k₀ i x hk hx y hs ha
      | none => rw [hs] at ha; exact ha

/-- The array scan after an operation that is no move and writes neither `y` nor an array slot
    is the array scan in front of it. -/
theorem accArr_snoc_of_pass {a : Lcmd} {j : Linstr} {ds : List LOperand} {o : String}
    {ss : List LOperand} {y : String} (hm : slotMov? j.li_i = none)
    (hx : j.li_i = .Lopn ds o ss) (hd : ds.any (dstHitB slotArr y) = false) :
    accArr slotArr (a ++ [j]) (a.length + 1) y = accArr slotArr a a.length y := by
  unfold accArr
  rw [reloadOf_succ_lopn (by simp) hm hx, if_neg (by simp [hd]),
    reloadOf_append_left _ _ _ _ _ le_rfl]

/-- **Rewriting an instruction.** Let `A ++ i :: C` be in the class, let `i'` be an operation
    that is no move, no access and writes no array slot, and let `C` write no array slot. If at
    every name `y` that the scan of a base of an instruction of `C` carries out of `C`, the
    instruction `i` is no move into `y` and `i'` writes no `y`, then `A ++ i' :: C` is in the
    class. -/
theorem physImgB_rewrite {A C : Lcmd} {i i' : Linstr} {ds : List LOperand} {o : String}
    {ss : List LOperand} (h : physImgB slotArr (A ++ i :: C) = true)
    (hm : slotMov? i'.li_i = none) (hx : i'.li_i = .Lopn ds o ss) (hacc : isAccB i'.li_i = false)
    (hdst : DstOk slotArr i'.li_i) (hC : ∀ r ∈ C, DstOk slotArr r.li_i)
    (hscan : ∀ k i₀ x, C[k]? = some i₀ →
      (∃ ds o y ss, i₀.li_i = .Lopn ds o (.arrIdx x y 8 :: ss)) →
      ∀ y, scanExit slotArr C k x = some y →
        (∀ d s, slotMov? i.li_i = some (d, s) → d ≠ y) ∧
          ds.any (dstHitB slotArr y) = false) :
    physImgB slotArr (A ++ i' :: C) = true := by
  have h' : physImgB slotArr (A ++ [i] ++ C) = true := by simpa using h
  have := physImgB_replace (L' := [i']) h' (by simp [hacc, hdst]) hC
    (fun k i₀ x hk hb y hs ha => by
      obtain ⟨hmv, hd⟩ := hscan k i₀ x hk hb y hs
      simp only [List.length_append, List.length_singleton] at ha ⊢
      rw [accArr_snoc_of_pass hm hx hd]
      have := accArr_succ_of_not_movInto (b := A ++ [i]) (p := A.length) (j := i) (by simp) hmv ha
      rwa [accArr_append_left _ _ _ _ _ le_rfl] at this)
  simpa using this

/-- **Inserting an instruction.** Let `A ++ C` be in the class, let `i'` be an operation that
    is no move, no access and writes no array slot, and let `C` write no array slot. If `i'`
    writes no name that the scan of a base of an instruction of `C` carries out of `C`, then
    `A ++ i' :: C` is in the class. -/
theorem physImgB_insert {A C : Lcmd} {i' : Linstr} {ds : List LOperand} {o : String}
    {ss : List LOperand} (h : physImgB slotArr (A ++ C) = true)
    (hm : slotMov? i'.li_i = none) (hx : i'.li_i = .Lopn ds o ss) (hacc : isAccB i'.li_i = false)
    (hdst : DstOk slotArr i'.li_i) (hC : ∀ r ∈ C, DstOk slotArr r.li_i)
    (hscan : ∀ k i₀ x, C[k]? = some i₀ →
      (∃ ds o y ss, i₀.li_i = .Lopn ds o (.arrIdx x y 8 :: ss)) →
      ∀ y, scanExit slotArr C k x = some y → ds.any (dstHitB slotArr y) = false) :
    physImgB slotArr (A ++ i' :: C) = true := by
  have h' : physImgB slotArr (A ++ [] ++ C) = true := by simpa using h
  have := physImgB_replace (L' := [i']) h' (by simp [hacc, hdst]) hC
    (fun k i₀ x hk hb y hs ha => by
      simp only [List.append_nil, List.length_append, List.length_singleton] at ha ⊢
      rw [accArr_snoc_of_pass hm hx (hscan k i₀ x hk hb y hs)]
      exact ha)
  simpa using this

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
