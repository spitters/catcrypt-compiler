/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomChainAlias

/-!
# The store-chain shape of the code with the result copy

At an array result of a region export without callee, the gate reads the exported code
followed by the result copy `resCopyCode src D m`, which copies the returned array `src`
word by word into the result buffer `D` through the versions `copyName D j`. The copy is a
second chain of stores: its alias steps send every version `copyName D (j + 1)` to the root of
`D` (`getD_foldl_resCopyCode`), each store consumes the current version, and the loads read
`src`. When the code has the store-chain shape with `src` read after it, the names of the copy
are fresh in the code, `D` is not consumed by the code, and the roots of the names the code
writes and of `src` differ from the root of `D`, the code with the copy has the shape under
the alias table of the whole, with the last version read after it.

## Main results

* `resCopyCode_at`, `wrAt_resCopyCode`, `readAt_resCopyCode`, `consumedAt_resCopyCode`: the
  instructions, writes, reads and consumptions of the result copy.
* `getD_foldl_resCopyCode`: the alias table after the result copy.
* `readAt_append`, `wrAt_append`, `consumedAt_append`: reads, writes and consumptions of an
  appended body.
* `chainShape_resCopy`: the store-chain shape of the code followed by the result copy.
* `chainShape_regionCoCode`, `chainShape_regionCoCode_none`: the same in the form of the gate,
  with and without a result copy.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainShape rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)

section Copy

variable (src D : String) (m j : Nat)

theorem rdArr_copyMov : rdArr (fun _ _ => none) (movImmI copyIdx j) = [] := rfl
theorem wrArr_copyMov : wrArr (fun _ => none) (movImmI copyIdx j) = none := rfl
theorem rdArr_copyLoad : rdArr (fun _ _ => none)
    ((.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m) : LinstrRM) = [src] := rfl
theorem wrArr_copyLoad : wrArr (fun _ => none)
    ((.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m) : LinstrRM) = none := rfl
theorem rdArr_copyStore : rdArr (fun _ _ => none)
    ((.Lopn [.reg (copyName D (j + 1))] "STOREIDX" [.arrIdx (copyName D j) copyIdx 8, .reg copyTmp],
      .store 64 m) : LinstrRM) = [copyName D j] := rfl
theorem wrArr_copyStore : wrArr (fun _ => none)
    ((.Lopn [.reg (copyName D (j + 1))] "STOREIDX" [.arrIdx (copyName D j) copyIdx 8, .reg copyTmp],
      .store 64 m) : LinstrRM) = some (copyName D (j + 1)) := rfl

end Copy

section Index

variable {α : Type} (f : Nat → List α)

/-- The length of a concatenation of lists of length three. -/
theorem length_flatMap_range3 (hf : ∀ j, (f j).length = 3) :
    ∀ n, ((List.range n).flatMap f).length = 3 * n
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range3 hf n]
      simp [hf]
      omega

/-- The entry at `3 * j + i` of a concatenation of lists of length three. -/
theorem getElem?_flatMap_range3 (hf : ∀ j, (f j).length = 3) :
    ∀ n j i, j < n → i < 3 → ((List.range n).flatMap f)[3 * j + i]? = (f j)[i]?
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, i, hj, hi => by
      rw [List.range_succ, List.flatMap_append]
      rcases Nat.lt_or_ge j n with h | h
      · rw [List.getElem?_append_left (by rw [length_flatMap_range3 f hf]; omega)]
        exact getElem?_flatMap_range3 hf n j i h hi
      · obtain rfl : j = n := by omega
        rw [List.getElem?_append_right (by rw [length_flatMap_range3 f hf]; omega),
          length_flatMap_range3 f hf]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        congr 1
        omega

end Index

/-- The result copy has three instructions per word. -/
theorem length_resCopyCode (src D : String) (m : Nat) :
    (resCopyCode src D m).length = 3 * m :=
  length_flatMap_range3 _ (fun _ => rfl) m

/-- The instructions of the result copy, by word and by place in the word. -/
theorem getElem?_resCopyCode (src D : String) {m j i : Nat} (hj : j < m) (hi : i < 3) :
    (resCopyCode src D m)[3 * j + i]? = (resCopyStep src D m j)[i]? :=
  getElem?_flatMap_range3 _ (fun _ => rfl) m j i hj hi

/-- The versions of the result buffer are distinct. -/
theorem copyName_inj {D : String} {i j : Nat} (h : copyName D i = copyName D j) : i = j := by
  have h2 : "#c".length = 2 := rfl
  unfold copyName at h
  split at h <;> split at h
  · omega
  · have := congrArg String.length h
    simp only [String.length_append] at this
    omega
  · have := congrArg String.length h
    simp only [String.length_append] at this
    omega
  · have h' := congrArg String.toList h
    simp only [String.toList_append, List.append_assoc, List.append_cancel_left_eq] at h'
    exact Nat.repr_inj.mp (String.toList_injective h')

section CopyFacts

variable {src D : String} {m : Nat}

/-- The instruction of the result copy at a position: the move of the index, the load of
    `src`, or the store of the next version. -/
theorem resCopyCode_at {p : Nat} (hp : p < 3 * m) :
    ∃ j, j < m ∧ ((p = 3 * j ∧ (resCopyCode src D m)[p]? = some (movImmI copyIdx j))
      ∨ (p = 3 * j + 1 ∧ (resCopyCode src D m)[p]? =
          some (.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m))
      ∨ (p = 3 * j + 2 ∧ (resCopyCode src D m)[p]? =
          some (.Lopn [.reg (copyName D (j + 1))] "STOREIDX"
            [.arrIdx (copyName D j) copyIdx 8, .reg copyTmp], .store 64 m))) := by
  refine ⟨p / 3, by omega, ?_⟩
  have hp' : p = 3 * (p / 3) + p % 3 := (Nat.div_add_mod p 3).symm
  have hm : p % 3 < 3 := Nat.mod_lt _ (by omega)
  have hg := getElem?_resCopyCode src D (m := m) (j := p / 3) (i := p % 3) (by omega) hm
  rw [← hp'] at hg
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
  · rw [h] at hg; exact Or.inl ⟨by omega, hg⟩
  · rw [h] at hg; exact Or.inr (Or.inl ⟨by omega, hg⟩)
  · rw [h] at hg; exact Or.inr (Or.inr ⟨by omega, hg⟩)

/-- **The writes of the result copy**: the store of each word writes the next version. -/
theorem wrAt_resCopyCode {w : Nat} {r : String}
    (h : WrAt (resCopyCode src D m) (fun _ => none) w r) :
    ∃ j, j < m ∧ w = 3 * j + 2 ∧ r = copyName D (j + 1) := by
  obtain ⟨i, hi, hw⟩ := h
  have hlt : w < 3 * m := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    rwa [length_resCopyCode] at this
  obtain ⟨j, hj, h | h | h⟩ := resCopyCode_at (src := src) (D := D) hlt
  · rw [h.2] at hi; cases hi; cases hw
  · rw [h.2] at hi; cases hi; cases hw
  · rw [h.2] at hi; cases hi
    cases hw
    exact ⟨j, hj, h.1, rfl⟩

/-- The store of the word `j` writes the version `copyName D (j + 1)`. -/
theorem wrAt_resCopyCode_store {j : Nat} (hj : j < m) :
    WrAt (resCopyCode src D m) (fun _ => none) (3 * j + 2) (copyName D (j + 1)) :=
  ⟨_, getElem?_resCopyCode src D hj (by omega : 2 < 3), rfl⟩

/-- **The reads of the result copy**: the loads read `src`, the stores read the current
    version, and after the copy the names `obs` are read. -/
theorem readAt_resCopyCode {obs : List String} {p : Nat} {r : String}
    (h : ReadAt (resCopyCode src D m) (fun _ _ => none) obs p r) :
    (∃ j, j < m ∧ p = 3 * j + 1 ∧ r = src)
      ∨ (∃ j, j < m ∧ p = 3 * j + 2 ∧ r = copyName D j)
      ∨ (p = 3 * m ∧ r ∈ obs) := by
  rcases h with ⟨i, hi, hr⟩ | ⟨hp, hr⟩
  · have hlt : p < 3 * m := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      rwa [length_resCopyCode] at this
    obtain ⟨j, hj, h | h | h⟩ := resCopyCode_at (src := src) (D := D) hlt
    · rw [h.2] at hi; cases hi; cases hr
    · rw [h.2] at hi; cases hi
      simp only [rdArr_copyLoad, List.mem_singleton] at hr
      exact Or.inl ⟨j, hj, h.1, hr⟩
    · rw [h.2] at hi; cases hi
      simp only [rdArr_copyStore, List.mem_singleton] at hr
      exact Or.inr (Or.inl ⟨j, hj, h.1, hr⟩)
  · rw [length_resCopyCode] at hp
    exact Or.inr (Or.inr ⟨hp, hr⟩)

/-- **The consumptions of the result copy**: the store of the word `j` consumes the version
    `copyName D j`. -/
theorem consumedAt_resCopyCode {c : Nat} {r : String}
    (h : ConsumedAt (resCopyCode src D m) (fun _ _ => none) (fun _ => none) c r) :
    ∃ j, j < m ∧ c = 3 * j + 2 ∧ r = copyName D j := by
  obtain ⟨i, d, hi, hr, hw, -⟩ := h
  obtain ⟨j, hj, hc, hd⟩ := wrAt_resCopyCode ⟨i, hi, hw⟩
  refine ⟨j, hj, hc, ?_⟩
  rw [hc, getElem?_resCopyCode src D hj (by omega : 2 < 3)] at hi
  cases hi
  simpa only [rdArr_copyStore, List.mem_singleton] using hr

/-- The store of the word `j` consumes the version `copyName D j`. -/
theorem consumedAt_resCopyCode_store {j : Nat} (hj : j < m) :
    ConsumedAt (resCopyCode src D m) (fun _ _ => none) (fun _ => none) (3 * j + 2)
      (copyName D j) :=
  ⟨_, _, getElem?_resCopyCode src D hj (by omega : 2 < 3), by simp [rdArr_copyStore], rfl,
    fun h => by have := copyName_inj (D := D) (i := j + 1) (j := j) h; omega⟩

end CopyFacts

section CopyAlias

variable {src D : String} {m : Nat}

/-- The alias steps of one word of the result copy: the move and the load keep the table, and
    the store sends the next version to the root of the current one. -/
theorem foldl_resCopyStep (M : Std.HashMap String String) (j : Nat) :
    (resCopyStep src D m j).foldl (aliasStepO []) M =
      M.insert (copyName D (j + 1)) (M.getD (copyName D j) (copyName D j)) := rfl

/-- **The alias table after the result copy**: the versions `copyName D (j + 1)` are sent to
    the root of `D`, and every other name keeps its root. -/
theorem getD_foldl_resCopyCode (M : Std.HashMap String String) (n : String) :
    ((resCopyCode src D m).foldl (aliasStepO []) M).getD n n =
      if ∃ j, j < m ∧ n = copyName D (j + 1) then M.getD D D else M.getD n n := by
  suffices h : ∀ k n, (((List.range k).flatMap (resCopyStep src D m)).foldl
      (aliasStepO []) M).getD n n =
        if ∃ j, j < k ∧ n = copyName D (j + 1) then M.getD D D else M.getD n n from h m n
  intro k
  induction k with
  | zero => intro n; simp
  | succ k ih =>
      intro n
      rw [List.range_succ, List.flatMap_append, List.foldl_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [foldl_resCopyStep, Std.HashMap.getD_insert]
      have hk : (((List.range k).flatMap (resCopyStep src D m)).foldl (aliasStepO []) M).getD
          (copyName D k) (copyName D k) = M.getD D D := by
        rw [ih]
        split
        · rfl
        · rename_i hne
          cases k with
          | zero => rfl
          | succ k => exact absurd ⟨k, by omega, rfl⟩ hne
      split
      · rename_i heq
        have heq' : n = copyName D (k + 1) := (beq_iff_eq.mp heq).symm
        rw [hk, ite_eq_left ⟨k, by omega, heq'⟩]
      · rename_i hne
        rw [ih]
        have hiff : (∃ j, j < k ∧ n = copyName D (j + 1)) ↔
            (∃ j, j < k + 1 ∧ n = copyName D (j + 1)) := by
          constructor
          · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
          · rintro ⟨j, hj, h⟩
            rcases Nat.lt_or_ge j k with hj' | hj'
            · exact ⟨j, hj', h⟩
            · obtain rfl : j = k := by omega
              exact absurd (beq_iff_eq.mpr h.symm) hne
        simp only [hiff]

end CopyAlias

section Append

variable {C E : List LinstrRM} {aa : String → Nat → Option Nat} {ao : String → Option Nat}

/-- A read of an appended body is a read of an instruction of the first part, or a read of
    the second part. -/
theorem readAt_append {obs : List String} {j : Nat} {r : String}
    (h : ReadAt (C ++ E) aa obs j r) :
    (j < C.length ∧ ∃ i, C[j]? = some i ∧ r ∈ rdArr aa i)
      ∨ (C.length ≤ j ∧ ReadAt E aa obs (j - C.length) r) := by
  rcases h with ⟨i, hi, hr⟩ | ⟨hj, hr⟩
  · rcases Nat.lt_or_ge j C.length with hj | hj
    · rw [List.getElem?_append_left hj] at hi
      exact Or.inl ⟨hj, i, hi, hr⟩
    · rw [List.getElem?_append_right hj] at hi
      exact Or.inr ⟨hj, Or.inl ⟨i, hi, hr⟩⟩
  · rw [List.length_append] at hj
    exact Or.inr ⟨by omega, Or.inr ⟨by omega, hr⟩⟩

/-- A write of an appended body is a write of one of its parts. -/
theorem wrAt_append {w : Nat} {r : String} (h : WrAt (C ++ E) ao w r) :
    (w < C.length ∧ WrAt C ao w r) ∨ (C.length ≤ w ∧ WrAt E ao (w - C.length) r) := by
  obtain ⟨i, hi, hr⟩ := h
  rcases Nat.lt_or_ge w C.length with hw | hw
  · rw [List.getElem?_append_left hw] at hi
    exact Or.inl ⟨hw, i, hi, hr⟩
  · rw [List.getElem?_append_right hw] at hi
    exact Or.inr ⟨hw, i, hi, hr⟩

/-- A consumption in an appended body is a consumption in one of its parts. -/
theorem consumedAt_append {c : Nat} {r : String} (h : ConsumedAt (C ++ E) aa ao c r) :
    (c < C.length ∧ ConsumedAt C aa ao c r)
      ∨ (C.length ≤ c ∧ ConsumedAt E aa ao (c - C.length) r) := by
  obtain ⟨i, d, hi, hr, hw, hd⟩ := h
  rcases Nat.lt_or_ge c C.length with hc | hc
  · rw [List.getElem?_append_left hc] at hi
    exact Or.inl ⟨hc, i, d, hi, hr, hw, hd⟩
  · rw [List.getElem?_append_right hc] at hi
    exact Or.inr ⟨hc, i, d, hi, hr, hw, hd⟩

/-- A consumption in the first part is one in the appended body. -/
theorem consumedAt_append_left {c : Nat} {r : String} (h : ConsumedAt C aa ao c r) :
    ConsumedAt (C ++ E) aa ao c r := by
  obtain ⟨i, d, hi, hr, hw, hd⟩ := h
  exact ⟨i, d, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1 ▸ hi, hr, hw, hd⟩

/-- A consumption in the second part is one in the appended body, shifted. -/
theorem consumedAt_append_right {c : Nat} {r : String} (h : ConsumedAt E aa ao c r) :
    ConsumedAt (C ++ E) aa ao (C.length + c) r := by
  obtain ⟨i, d, hi, hr, hw, hd⟩ := h
  refine ⟨i, d, ?_, hr, hw, hd⟩
  rw [List.getElem?_append_right (by omega)]
  simpa using hi

/-- A write of the first part is one of the appended body. -/
theorem wrAt_append_left {w : Nat} {r : String} (h : WrAt C ao w r) : WrAt (C ++ E) ao w r := by
  obtain ⟨i, hi, hr⟩ := h
  exact ⟨i, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1 ▸ hi, hr⟩

/-- A write of the second part is one of the appended body, shifted. -/
theorem wrAt_append_right {w : Nat} {r : String} (h : WrAt E ao w r) :
    WrAt (C ++ E) ao (C.length + w) r := by
  obtain ⟨i, hi, hr⟩ := h
  refine ⟨i, ?_, hr⟩
  rw [List.getElem?_append_right (by omega)]
  simpa using hi

end Append

section Shape

/-- **The store-chain shape of the code followed by the result copy.** When the code `C` has
    the shape under its alias table with `src` read after it, the versions `copyName D (k + 1)`
    of the result buffer are neither read nor written in `C`, `D` is not consumed in `C`, and
    the roots of the names `C` writes and of `src` differ from the root of `D`, then `C`
    followed by the copy `resCopyCode src D m` of `src` into `D` has the shape under its alias
    table, with the last version `copyName D m` read after it. -/
theorem chainShape_resCopy {C : List LinstrRM} {src D : String} {m : Nat}
    (hC : ChainShape (fun n => (C.foldl (aliasStepO []) {}).getD n n) C (fun _ _ => none)
      (fun _ => none) [src])
    (hfr : ∀ (j : Nat) (i : LinstrRM) (r : String) (k : Nat), C[j]? = some i →
      r ∈ rdArr (fun _ _ => none) i → r ≠ copyName D (k + 1))
    (hfw : ∀ w r k, WrAt C (fun _ => none) w r → r ≠ copyName D (k + 1))
    (hsrc : ∀ k, k < m → src ≠ copyName D (k + 1)) (hsD : src ≠ D)
    (hDc : ∀ c, ¬ ConsumedAt C (fun _ _ => none) (fun _ => none) c D)
    (hTD : ∀ w d, WrAt C (fun _ => none) w d →
      (C.foldl (aliasStepO []) {}).getD d d ≠ (C.foldl (aliasStepO []) {}).getD D D)
    (hTsrc : (C.foldl (aliasStepO []) {}).getD src src ≠ (C.foldl (aliasStepO []) {}).getD D D) :
    ChainShape (fun n => ((C ++ resCopyCode src D m).foldl (aliasStepO []) {}).getD n n)
      (C ++ resCopyCode src D m) (fun _ _ => none) (fun _ => none) [copyName D m] := by
  obtain ⟨h1, h2, h3⟩ := hC
  have hσ : ∀ n, ((C ++ resCopyCode src D m).foldl (aliasStepO []) {}).getD n n =
      if ∃ j, j < m ∧ n = copyName D (j + 1) then (C.foldl (aliasStepO []) {}).getD D D
      else (C.foldl (aliasStepO []) {}).getD n n := by
    intro n
    rw [List.foldl_append, getD_foldl_resCopyCode]
  have rdC : ∀ j i r, C[j]? = some i → r ∈ rdArr (fun _ _ => none) i →
      ReadAt C (fun _ _ => none) [src] j r := fun j i r hi hr => Or.inl ⟨i, hi, hr⟩
  have hD0 : copyName D 0 = D := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro j r w hR hW
    rcases readAt_append hR with ⟨hj, i, hi, hr⟩ | ⟨hj, hR'⟩ <;>
      rcases wrAt_append hW with ⟨hw, hW'⟩ | ⟨hw, hW'⟩
    · exact h1 j r w (rdC j i r hi hr) hW'
    · obtain ⟨k, -, -, rfl⟩ := wrAt_resCopyCode hW'
      exact absurd rfl (hfr j i _ k hi hr)
    · omega
    · obtain ⟨k, hk, hwk, rfl⟩ := wrAt_resCopyCode hW'
      rcases readAt_resCopyCode hR' with ⟨k', -, -, hr⟩ | ⟨k', -, hjk, hr⟩ | ⟨hjk, hr⟩
      · exact absurd hr.symm (hsrc k hk)
      · have := copyName_inj hr
        omega
      · simp only [List.mem_singleton] at hr
        have := copyName_inj hr
        omega
  · intro c r j hc hR
    rcases consumedAt_append hc with ⟨hcl, hc'⟩ | ⟨hcl, hc'⟩
    · rcases readAt_append hR with ⟨hj, i, hi, hr⟩ | ⟨hj, hR'⟩
      · exact h2 c r j hc' (rdC j i r hi hr)
      · exfalso
        have hcopy : ∀ k, r = copyName D k → False := by
          intro k hk
          subst hk
          cases k with
          | zero => exact hDc c hc'
          | succ k =>
              obtain ⟨i, d, hi, hr, -, -⟩ := hc'
              exact hfr c i _ k hi hr rfl
        rcases readAt_resCopyCode hR' with ⟨k', -, -, rfl⟩ | ⟨k', -, -, hr⟩ | ⟨-, hr⟩
        · have := h2 c _ C.length hc' (Or.inr ⟨rfl, by simp⟩)
          omega
        · exact hcopy k' hr
        · simp only [List.mem_singleton] at hr
          exact hcopy m hr
    · obtain ⟨k, hk, hck, rfl⟩ := consumedAt_resCopyCode hc'
      rcases readAt_append hR with ⟨hj, -, -, -⟩ | ⟨hj, hR'⟩
      · omega
      · rcases readAt_resCopyCode hR' with ⟨k', -, -, hr⟩ | ⟨k', -, hjk, hr⟩ | ⟨-, hr⟩
        · cases k with
          | zero => exact absurd hr.symm hsD
          | succ k => exact absurd hr.symm (hsrc k (by omega))
        · have := copyName_inj hr
          omega
        · simp only [List.mem_singleton] at hr
          have := copyName_inj hr
          omega
  · intro k d r hW hσrd hne hbefore
    simp only [hσ] at hσrd
    rcases wrAt_append hW with ⟨hk, hW'⟩ | ⟨hk, hW'⟩
    · have hd : ¬ ∃ j, j < m ∧ d = copyName D (j + 1) := fun ⟨j, _, hj⟩ =>
        hfw k d j hW' hj
      rw [ite_eq_right_of_eq_false _ _ (eq_false hd)] at hσrd
      by_cases hr : ∃ j, j < m ∧ r = copyName D (j + 1)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at hσrd
        exact absurd hσrd.symm (hTD k d hW')
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at hσrd
        have hbC : ∀ w, WrAt C (fun _ => none) w r → w < k := fun w hw =>
          hbefore w (wrAt_append_left hw)
        rcases h3 k d r hW' hσrd hne hbC with ⟨c, hck, hc⟩ | hnr
        · exact Or.inl ⟨c, hck, consumedAt_append_left hc⟩
        · right
          have hrD : r ≠ D := fun h => hTD k d hW' (by rw [← hσrd, h])
          have hcopy : ∀ j, j ≤ m → r = copyName D j → False := by
            intro j hjm hj
            cases j with
            | zero => exact hrD hj
            | succ j => exact hr ⟨j, by omega, hj⟩
          intro j hkj hR
          rcases readAt_append hR with ⟨hj, i, hi, hrr⟩ | ⟨hj, hR'⟩
          · exact hnr j hkj (rdC j i r hi hrr)
          · rcases readAt_resCopyCode hR' with
              ⟨k', -, -, h'⟩ | ⟨k', hk', -, h'⟩ | ⟨-, h'⟩
            · exact hnr C.length hk (Or.inr ⟨rfl, by simp [h']⟩)
            · exact hcopy k' (by omega) h'
            · simp only [List.mem_singleton] at h'
              exact hcopy m le_rfl h'
    · obtain ⟨i, hi, hki, rfl⟩ := wrAt_resCopyCode hW'
      have hdc : ∃ j, j < m ∧ copyName D (i + 1) = copyName D (j + 1) := ⟨i, hi, rfl⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hdc)] at hσrd
      by_cases hr : ∃ j, j < m ∧ r = copyName D (j + 1)
      · obtain ⟨i', hi', rfl⟩ := hr
        have hw' := hbefore _ (wrAt_append_right (C := C) (wrAt_resCopyCode_store (src := src) hi'))
        have hii : i' ≠ i := fun h => hne (by rw [h])
        left
        refine ⟨C.length + (3 * (i' + 1) + 2), by omega, ?_⟩
        exact consumedAt_append_right (consumedAt_resCopyCode_store (src := src) (by omega))
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at hσrd
        by_cases hrD : r = D
        · left
          subst hrD
          refine ⟨C.length + (3 * 0 + 2), by omega, ?_⟩
          exact consumedAt_append_right (consumedAt_resCopyCode_store (src := src) (by omega))
        · right
          intro j hkj hR
          rcases readAt_append hR with ⟨hj, -, -, -⟩ | ⟨hj, hR'⟩
          · omega
          · have hcopy : ∀ j, j ≤ m → r = copyName D j → False := by
              intro j hjm hj
              cases j with
              | zero => exact hrD hj
              | succ j => exact hr ⟨j, by omega, hj⟩
            rcases readAt_resCopyCode hR' with
              ⟨k', -, -, h'⟩ | ⟨k', hk', -, h'⟩ | ⟨-, h'⟩
            · subst h'
              exact hTsrc hσrd
            · exact hcopy k' (by omega) h'
            · simp only [List.mem_singleton] at h'
              exact hcopy m le_rfl h'

end Shape

section Region

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (zeroDst? aliasTab)

/-- The result copy zeroes no array. -/
theorem zeroDst?_resCopyCode {src D : String} {m : Nat} :
    ∀ i ∈ resCopyCode src D m, zeroDst? i = none := by
  intro i hi
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> rfl

/-- **The store-chain shape of the code with the result copy of a region export**, in the form
    of the gate: the code `C` without a zeroing, of the store-chain shape with its returned
    array `src` read after it, followed by the copy `(src, D, m)` that `regionCopy` chooses,
    under the alias table of the region export and with the last version of the result buffer
    read after it. -/
theorem chainShape_regionCoCode {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {C : List LinstrRM} {res : List LOperand} {src D : String} {m : Nat}
    (hcp : regionCopy σ nm t none C res = some (src, D, m))
    (hz : ∀ i ∈ C, zeroDst? i = none)
    (hC : ChainShape (fun n => (C.foldl (aliasStepO []) {}).getD n n) C (fun _ _ => none)
      (fun _ => none) [src])
    (hfr : ∀ (j : Nat) (i : LinstrRM) (r : String) (k : Nat), C[j]? = some i →
      r ∈ rdArr (fun _ _ => none) i → r ≠ copyName D (k + 1))
    (hfw : ∀ w r k, WrAt C (fun _ => none) w r → r ≠ copyName D (k + 1))
    (hsD : src ≠ D)
    (hDc : ∀ c, ¬ ConsumedAt C (fun _ _ => none) (fun _ => none) c D)
    (hTD : ∀ w d, WrAt C (fun _ => none) w d →
      (C.foldl (aliasStepO []) {}).getD d d ≠ (C.foldl (aliasStepO []) {}).getD D D)
    (hTsrc : (C.foldl (aliasStepO []) {}).getD src src ≠ (C.foldl (aliasStepO []) {}).getD D D) :
    ChainShape (canonMemrefName (regionAliasTab σ nm t none res
        (regionCoCode σ nm t C res (some (src, D, m)))))
      (regionCoCode σ nm t C res (some (src, D, m))) (calleeAAT none) (calleeAOT none)
      (regionCoObs t (regionOut (some (src, D, m)) res)) := by
  obtain ⟨-, rfl, ⟨op, rfl, hop⟩, -, -, hsrc⟩ := regionCopy_some hcp
  have hcode : regionCoCode σ nm (.stackArr 64 m) C [op] (some (src, D, m)) =
      C ++ resCopyCode src D m := by
    simp [regionCoCode, regionRet, JasminLsemRenameLoop.movesOf]
  rw [hcode, regionAliasTab_eq_of_noZero _ _ _ _ _ (by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact hz i h
    · exact zeroDst?_resCopyCode i h)]
  exact chainShape_resCopy hC hfr hfw (fun k hk => hsrc k hk) hsD hDc hTD hTsrc

/-- **Without a result copy**, the code of a region export at an array result type with the
    store-chain shape keeps it in the form of the gate. -/
theorem chainShape_regionCoCode_none {σ : AbiLayout} {nm : String → String} {w n : Nat}
    {C : List LinstrRM} {res : List LOperand} (hz : ∀ i ∈ C, zeroDst? i = none)
    (hC : ChainShape (fun x => (C.foldl (aliasStepO []) {}).getD x x) C (fun _ _ => none)
      (fun _ => none) (res.map JasminLsemWidthN.operandName)) :
    ChainShape (canonMemrefName (regionAliasTab σ nm (.stackArr w n) none res
        (regionCoCode σ nm (.stackArr w n) C res none)))
      (regionCoCode σ nm (.stackArr w n) C res none) (calleeAAT none) (calleeAOT none)
      (regionCoObs (.stackArr w n) (regionOut none res)) := by
  have hcode : regionCoCode σ nm (.stackArr w n) C res none = C := by
    simp [regionCoCode, regionRet, JasminLsemRenameLoop.movesOf]
  rw [hcode, regionAliasTab_eq_of_noZero _ _ _ _ _ hz]
  exact hC

end Region

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
