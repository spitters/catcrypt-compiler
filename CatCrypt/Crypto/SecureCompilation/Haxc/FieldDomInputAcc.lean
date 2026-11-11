/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomNameAlloc
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomResultName
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomExportClass
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSide

/-!
# The access form of the allocator input on the field domain

The allocator input of the region back end is the code of the webs of the export, followed by
its result copy, renamed by the coalescing renaming of its alias table. Its accesses have the
form `AccP P` when the renaming sends every indexed base into `P`
(`RegionPhysImgArg.accP_regionAllocBody`). The export defines every indexed base before use
from the parameter names (`RegionPhysImgArg.exportR_idxOk`); the webs rename the array names
position by position, and on a straight body the check `webB` makes the web name of a live
array the name itself when no instruction before writes it, and otherwise the renamed write of
the last instruction before that writes it. So the webs define every indexed base before use
from the same names, and the renaming sends every base to a parameter.

## Main results

* `idxOk_iff_forall`: definition before use, position by position.
* `webB_lastWrite`: the web name of a live array on a straight body accepted by `webB`.
* `idxOk_webRen`, `afterDst_webRen`: the webs of a straight body keep definition before use
  and the names defined after it that are read after it.
* `accFacts`: the indexed bases and the stores of an instruction of the export.
* `arrW64B_loadsChainS`: loads and a chain of stores over `64`-bit word arrays pass the width
  condition.
* `webs_aliasRoots`: the coalescing renaming of the webs sends every array name to a
  word-array parameter with a save slot.
* `allocInputAcc_of_fieldDomB'`: the access form `AllocInputAcc` of the allocator input of a
  member of `fieldDomB'`.
* `fieldDom_cellNamesRB'`: the stage `G20` on `fieldDomB'` without hypothesis.
* `stackReadFreeB_fieldDom`: the printed body of a member reads no stack-argument name, the
  stack half of the prologue facts of `G19`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (zeroDst?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webRen webB webB_instr webInstrB
  webSuccs webB_live_pred stepRen webB_entry webB_exit webB_obs)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (IdxIn IdxOk addDst afterDst
  stDst idxIn_mono)

/-! ## 1. Definition before use, position by position -/

section Pos

/-- The names of `S` and the destinations of the stores and zeroings of `C` at the positions
    below `k`. -/
def DstBelow (S : String → Prop) (C : List LinstrRM) (k : Nat) (x : String) : Prop :=
  S x ∨ ∃ j < k, ∃ i, C[j]? = some i ∧ (stDst i = some x ∨ zeroDst? i = some x)

theorem dstBelow_cons_zero {S : String → Prop} {i : LinstrRM} {c : List LinstrRM} {x : String} :
    DstBelow S (i :: c) 0 x ↔ S x := by
  simp [DstBelow]

theorem dstBelow_cons_succ {S : String → Prop} {i : LinstrRM} {c : List LinstrRM} {k : Nat}
    {x : String} : DstBelow S (i :: c) (k + 1) x ↔ DstBelow (addDst S i) c k x := by
  constructor
  · rintro (h | ⟨j, hj, i', hi', hd⟩)
    · exact .inl (.inl h)
    · cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi'
          subst hi'
          exact .inl (.inr hd)
      | succ j =>
          simp only [List.getElem?_cons_succ] at hi'
          exact .inr ⟨j, by omega, i', hi', hd⟩
  · rintro ((h | h) | ⟨j, hj, i', hi', hd⟩)
    · exact .inl h
    · exact .inr ⟨0, by omega, i, rfl, h⟩
    · exact .inr ⟨j + 1, by omega, i', by simpa using hi', hd⟩

/-- **Definition before use, position by position**: along `C`, every indexed base of the
    instruction at `k` is in `S` or a destination of a store or a zeroing below `k`. -/
theorem idxOk_iff_forall {S : String → Prop} {C : List LinstrRM} :
    IdxOk S C ↔ ∀ k i, C[k]? = some i → IdxIn (DstBelow S C k) i := by
  induction C generalizing S with
  | nil => simp [IdxOk]
  | cons i c ih =>
      simp only [IdxOk]
      rw [ih]
      constructor
      · rintro ⟨h0, h⟩ k i' hi'
        cases k with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi'
            subst hi'
            exact idxIn_mono (fun x hx => dstBelow_cons_zero.mpr hx) h0
        | succ k =>
            simp only [List.getElem?_cons_succ] at hi'
            exact idxIn_mono (fun x hx => dstBelow_cons_succ.mpr hx) (h k i' hi')
      · intro h
        refine ⟨idxIn_mono (fun x hx => dstBelow_cons_zero.mp hx) (h 0 i rfl), fun k i' hi' => ?_⟩
        exact idxIn_mono (fun x hx => dstBelow_cons_succ.mp hx) (h (k + 1) i' (by simpa using hi'))

/-- The names defined after `C` are those below its length. -/
theorem afterDst_iff {S : String → Prop} {C : List LinstrRM} {x : String} :
    afterDst S C x ↔ DstBelow S C C.length x := by
  induction C generalizing S with
  | nil => simp [afterDst, DstBelow]
  | cons i c ih =>
      rw [List.length_cons, dstBelow_cons_succ, ← ih]
      rfl

end Pos

/-! ## 2. The web name of a live array -/

section Web

variable {w : Nat → String → String} {C : List LinstrRM} {L : Nat → List String}
  {obs : List String}

/-- **The web name of a live array on a straight body**: at a body of straight instructions
    accepted by `webB`, an array `y` live at `k` is renamed at `k` to itself when no
    instruction below `k` writes it, and otherwise to the name the last instruction below `k`
    that writes it writes. -/
theorem webB_lastWrite (hacc : webB w C L obs (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), C[k]? = some i → StraightOp i) :
    ∀ k, k ≤ C.length → ∀ y ∈ L k,
      (w k y = y ∧ ∀ j < k, ∀ i, C[j]? = some i → wrArr (fun _ => none) i ≠ some y) ∨
      ∃ j < k, ∃ i, C[j]? = some i ∧ wrArr (fun _ => none) i = some y ∧ w (j + 1) y = w k y
  | 0, _, y, hy => .inl ⟨webB_entry hacc y hy, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | k + 1, hk, y, hy => by
      obtain ⟨i, hi⟩ : ∃ i, C[k]? = some i := ⟨C[k], List.getElem?_eq_getElem (by omega)⟩
      by_cases hw : wrArr (fun _ => none) i = some y
      · exact .inr ⟨k, by omega, i, hi, hw, rfl⟩
      have hyk := (webB_live hacc hi (hst k i hi).1).2 y hy hw
      obtain ⟨ds, o, ss, hop⟩ := (hst k i hi).2
      have hsucc : k + 1 ∈ webSuccs C k i := by
        unfold webSuccs
        rw [hop]
        exact List.mem_singleton_self _
      have he := (webB_live_pred hacc hi hsucc hy).1 hw
      rcases webB_lastWrite hacc hst k (by omega) y hyk with ⟨h1, h2⟩ | ⟨j, hj, i', h1, h2, h3⟩
      · refine .inl ⟨he ▸ h1, fun j hj i' hi' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h2 j hj i' hi'
        · rw [hi] at hi'
          cases hi'
          exact hw
      · exact .inr ⟨j, by omega, i', h1, h2, h3.trans he⟩

/-- The renaming of an instruction by its position renames an array live before it as the
    position map at that position. -/
theorem stepRen_live (hacc : webB w C L obs (fun _ _ => none) (fun _ => none) = true)
    {k : Nat} {i : LinstrRM} (hi : C[k]? = some i) {y : String} (hy : y ∈ L k) :
    stepRen w (fun _ => none) k i y = w k y := by
  have h := webB_instr hacc hi
  unfold webInstrB at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1.1.2 y hy

/-- The renaming of an instruction by its position renames the array it writes as the position
    map after it. -/
theorem stepRen_wr {k : Nat} {i : LinstrRM} {y : String}
    (hw : wrArr (fun _ => none) i = some y) :
    stepRen w (fun _ => none) k i y = w (k + 1) y := by
  simp [stepRen, hw]

end Web

/-! ## 3. Definition before use on the webs -/

section Webs

variable {w : Nat → String → String} {C : List LinstrRM} {L : Nat → List String}
  {obs : List String} {S : String → Prop}

/-- **The webs of a straight body define every indexed base before use** from the names the
    body defines them from, when the indexed bases of each instruction and of each renaming of
    it are its array reads, and its stores and zeroings write the array it writes and, renamed,
    the renamed array. -/
theorem idxOk_webRen (hacc : webB w C L obs (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), C[k]? = some i → StraightOp i)
    (hplain : ∀ i ∈ C, PlainTag i)
    (hread : ∀ i ∈ C, ∀ T, IdxIn T i → ∀ b ∈ rdArr (fun _ _ => none) i, T b)
    (hbase : ∀ i ∈ C, ∀ (ρ : String → String) (T : String → Prop),
      (∀ b ∈ rdArr (fun _ _ => none) (renArr ρ i), T b) → IdxIn T (renArr ρ i))
    (hdst : ∀ i ∈ C, ∀ x, (stDst i = some x ∨ zeroDst? i = some x) →
      wrArr (fun _ => none) i = some x)
    (hdst' : ∀ i ∈ C, ∀ (ρ : String → String) d, wrArr (fun _ => none) i = some d →
      stDst (renArr ρ i) = some (ρ d))
    (hI : IdxOk S C) : IdxOk S (webRen w (fun _ => none) C) := by
  rw [idxOk_iff_forall] at hI ⊢
  intro k i' hi'
  rw [getElem?_webRen] at hi'
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
  have hmem := List.mem_of_getElem? hi
  have hk : k ≤ C.length := (List.getElem?_eq_some_iff.mp hi).1.le
  refine hbase i hmem _ _ fun b' hb' => ?_
  rw [(rdArr_wrArr_renArr _ i (hplain i hmem)).1] at hb'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
  have hbL := (webB_live hacc hi (hst k i hi).1).1 b hb
  rw [stepRen_live hacc hi hbL]
  have horig := hread i hmem _ (hI k i hi) b hb
  rcases webB_lastWrite hacc hst k hk b hbL with ⟨h1, h2⟩ | ⟨j, hj, i0, hi0, hw0, he⟩
  · rw [h1]
    rcases horig with hS | ⟨j, hj, i0, hi0, hd⟩
    · exact .inl hS
    · exact absurd (hdst i0 (List.mem_of_getElem? hi0) b hd) (h2 j hj i0 hi0)
  · refine .inr ⟨j, hj, renArr (stepRen w (fun _ => none) j i0) i0,
      by rw [getElem?_webRen, hi0]; rfl, .inl ?_⟩
    rw [hdst' i0 (List.mem_of_getElem? hi0) _ b hw0, stepRen_wr hw0, he]

/-- **The webs of a straight body keep the names defined after it that are read after it.** -/
theorem afterDst_webRen (hacc : webB w C L obs (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), C[k]? = some i → StraightOp i)
    (hdst : ∀ i ∈ C, ∀ x, (stDst i = some x ∨ zeroDst? i = some x) →
      wrArr (fun _ => none) i = some x)
    (hdst' : ∀ i ∈ C, ∀ (ρ : String → String) d, wrArr (fun _ => none) i = some d →
      stDst (renArr ρ i) = some (ρ d))
    {y : String} (hy : y ∈ obs) (h : afterDst S C y) :
    afterDst S (webRen w (fun _ => none) C) y := by
  rw [afterDst_iff] at h ⊢
  have hlen : (webRen w (fun _ => none) C).length = C.length := by simp [webRen]
  rw [hlen]
  have hyL := webB_obs hacc y hy
  have hfix := webB_exit hacc y hy
  rcases webB_lastWrite hacc hst C.length le_rfl y hyL with ⟨-, h2⟩ | ⟨j, hj, i0, hi0, hw0, he⟩
  · rcases h with hS | ⟨j, hj, i0, hi0, hd⟩
    · exact .inl hS
    · exact absurd (hdst i0 (List.mem_of_getElem? hi0) y hd) (h2 j hj i0 hi0)
  · refine .inr ⟨j, hj, renArr (stepRen w (fun _ => none) j i0) i0,
      by rw [getElem?_webRen, hi0]; rfl, .inl ?_⟩
    rw [hdst' i0 (List.mem_of_getElem? hi0) _ y hw0, stepRen_wr hw0, he, hfix]

end Webs


/-! ## 4. The classes of the instructions of the export -/

section Class

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (AccCode ImmCode stPair)

/-- The renaming of the array positions keeps the tag. -/
theorem renArr_snd (ρ : String → String) (i : LinstrRM) : (renArr ρ i).2 = i.2 := by
  obtain ⟨w, t⟩ := i
  cases t <;> rfl

/-- **The three classes of an instruction of the access form with a plain tag**: an indexed
    load, an indexed store, or an operation that is no indexed access, no constant-index store
    and no zeroing and has no indexed operand. -/
theorem accCode_cases {i : LinstrRM} (hc : AccCode i) (hm : ImmCode i) (hp : PlainTag i) :
    (∃ d b y w n, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b y 8], .load w n)) ∨
    (∃ d b y v w n, i = (.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n)) ∨
    (∀ ds o ss, i.1 = .Lopn ds o ss → o ≠ "LOADIDX" ∧ o ≠ "STOREIDX" ∧ o ≠ "STOREIMM" ∧
      o ≠ "ZEROARR" ∧ ∀ b y s, LOperand.arrIdx b y s ∉ ds ++ ss) := by
  by_cases hl : ∃ ds o ss, i.1 = .Lopn ds o ss
  · obtain ⟨ds, o, ss, he⟩ := hl
    by_cases hL : o = "LOADIDX"
    · subst hL
      exact .inl (hc.1 ds ss he)
    by_cases hS : o = "STOREIDX"
    · subst hS
      exact .inr (.inl (hc.2.1 ds ss he))
    by_cases hI : o = "STOREIMM"
    · subst hI
      obtain ⟨_, _, _, _, _, _, rfl⟩ := hm.2 ds ss he
      exact absurd hp id
    by_cases hZ : o = "ZEROARR"
    · subst hZ
      obtain ⟨_, _, _, _, _, rfl⟩ := hm.1 ds ss he
      exact absurd hp id
    refine .inr (.inr fun ds' o' ss' he' => ?_)
    rw [he] at he'
    simp only [LinstrR.Lopn.injEq] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    exact ⟨hL, hS, hI, hZ, hc.2.2 ds o ss he hL hS⟩
  · refine .inr (.inr fun ds o ss he => absurd ⟨ds, o, ss, he⟩ hl)

/-- The class of the operations without indexed access. -/
def NoAcc (i : LinstrRM) : Prop :=
  ∀ ds o ss, i.1 = .Lopn ds o ss → o ≠ "LOADIDX" ∧ o ≠ "STOREIDX" ∧ o ≠ "STOREIMM" ∧
    o ≠ "ZEROARR" ∧ ∀ b y s, LOperand.arrIdx b y s ∉ ds ++ ss

/-- The renaming of the array positions keeps the class `NoAcc`. -/
theorem noAcc_renArr (ρ : String → String) {i : LinstrRM} (h : NoAcc i) : NoAcc (renArr ρ i) := by
  intro ds o ss he
  obtain ⟨ds0, ss0, hi, hm⟩ := RegionPhysImgArg.renArr_lopn ρ he
  obtain ⟨h1, h2, h3, h4, h5⟩ := h ds0 o ss0 hi
  refine ⟨h1, h2, h3, h4, fun b y s hb => ?_⟩
  obtain ⟨b0, hb0⟩ := hm b y s hb
  exact h5 b0 y s hb0

/-- An operation of the class `NoAcc` with a plain tag reads and writes no array. -/
theorem rdArr_wrArr_noAcc {i : LinstrRM} (h : NoAcc i) (hp : PlainTag i) :
    rdArr (fun _ _ => none) i = [] ∧ wrArr (fun _ => none) i = none := by
  obtain ⟨wire, tag⟩ := i
  cases tag with
  | reg c => exact rdArr_wrArr_regTag wire c _ _ (fun _ _ => rfl) (fun _ => rfl)
  | load w m =>
      refine rdArr_wrArr_load_none wire w m ?_
      unfold JasminLsemMem.loadStruct?
      split
      · rename_i dst opn base idx sc
        have := (h _ _ _ rfl).1
        simp [this]
      · rfl
  | store w m =>
      refine rdArr_wrArr_store_none wire w m ?_
      unfold JasminLsemMem.storeStruct?
      split
      · rename_i dst opn base idx sc val
        have := (h _ _ _ rfl).2.1
        simp [this]
      · rfl
  | _ => exact absurd hp id

/-- An operation of the class `NoAcc` stores into no array and zeroes none. -/
theorem stDst_zeroDst_noAcc {i : LinstrRM} (h : NoAcc i) :
    stDst i = none ∧ zeroDst? i = none := by
  constructor
  · unfold stDst stPair
    split
    · rfl
    · split
      · rename_i dst opn base y s rest heq
        exact absurd (List.mem_append_right _ List.mem_cons_self) ((h _ _ _ heq).2.2.2.2 base y s)
      · rename_i dst opn base rest heq
        have := (h _ _ _ heq).2.2.1
        simp [this]
      · rfl
  · unfold zeroDst?
    split
    · rename_i d opn ss heq
      have := (h _ _ _ heq).2.2.2.1
      simp [this]
    · rfl

/-- An operation of the class `NoAcc` has no indexed base. -/
theorem idxIn_noAcc {i : LinstrRM} (h : NoAcc i) (T : String → Prop) : IdxIn T i :=
  fun ds o ss he => ⟨fun b y s hb => absurd (List.mem_append_right _ hb) ((h ds o ss he).2.2.2.2 b y s),
    fun ho => absurd ho (h ds o ss he).2.2.1⟩

/-- **The facts of definition before use of an instruction of the access form with a plain
    tag**: its indexed bases are its array reads, also under every renaming of its array
    positions, and its stores write the array it writes, renamed under a renaming. -/
theorem accFacts {i : LinstrRM} (hc : AccCode i) (hm : ImmCode i) (hp : PlainTag i) :
    (∀ T, IdxIn T i → ∀ b ∈ rdArr (fun _ _ => none) i, T b) ∧
    (∀ (ρ : String → String) (T : String → Prop),
      (∀ b ∈ rdArr (fun _ _ => none) (renArr ρ i), T b) → IdxIn T (renArr ρ i)) ∧
    (∀ x, (stDst i = some x ∨ zeroDst? i = some x) → wrArr (fun _ => none) i = some x) ∧
    (∀ (ρ : String → String) d, wrArr (fun _ => none) i = some d →
      stDst (renArr ρ i) = some (ρ d)) := by
  rcases accCode_cases hc hm hp with ⟨d, b, y, w, n, rfl⟩ | ⟨d, b, y, v, w, n, rfl⟩ | h3
  · refine ⟨fun T hT b' hb' => ?_, fun ρ T hT => ?_, fun x hx => ?_, fun ρ d' hd' => ?_⟩
    · have hr : rdArr (fun _ _ => none)
          ((.Lopn [.reg d] "LOADIDX" [.arrIdx b y 8], .load w n) : LinstrRM) = [b] := rfl
      rw [hr, List.mem_singleton] at hb'
      subst hb'
      exact (hT _ _ _ rfl).1 _ y 8 List.mem_cons_self
    · have hR : renArr ρ ((.Lopn [.reg d] "LOADIDX" [.arrIdx b y 8], .load w n) : LinstrRM) =
          (.Lopn [.reg d] "LOADIDX" [.arrIdx (ρ b) y 8], .load w n) := by
        simp [renArr, X86Backend.ImageCoalesceCfg.renLoad]
      rw [hR] at hT ⊢
      have hr : rdArr (fun _ _ => none)
          ((.Lopn [.reg d] "LOADIDX" [.arrIdx (ρ b) y 8], .load w n) : LinstrRM) = [ρ b] := rfl
      rw [hr] at hT
      intro ds o ss he
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨fun b' y' s' hb' => ?_, fun ho => absurd ho (by decide)⟩
      simp only [List.mem_singleton, LOperand.arrIdx.injEq] at hb'
      rw [hb'.1]
      exact hT _ List.mem_cons_self
    · have h1 : stDst ((.Lopn [.reg d] "LOADIDX" [.arrIdx b y 8], .load w n) : LinstrRM) = none :=
        rfl
      have h2 : zeroDst? ((.Lopn [.reg d] "LOADIDX" [.arrIdx b y 8], .load w n) : LinstrRM) =
        none := rfl
      rw [h1, h2] at hx
      simp at hx
    · have h1 : wrArr (fun _ => none)
          ((.Lopn [.reg d] "LOADIDX" [.arrIdx b y 8], .load w n) : LinstrRM) = none := rfl
      rw [h1] at hd'
      cases hd'
  · refine ⟨fun T hT b' hb' => ?_, fun ρ T hT => ?_, fun x hx => ?_, fun ρ d' hd' => ?_⟩
    · have hr : rdArr (fun _ _ => none)
          ((.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n) : LinstrRM) = [b] :=
        rfl
      rw [hr, List.mem_singleton] at hb'
      subst hb'
      exact (hT _ _ _ rfl).1 _ y 8 List.mem_cons_self
    · have hR : renArr ρ
          ((.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n) : LinstrRM) =
          (.Lopn [.reg (ρ d)] "STOREIDX" [.arrIdx (ρ b) y 8, .reg v], .store w n) := by
        simp [renArr, X86Backend.ImageCoalesceCfg.renStore]
      rw [hR] at hT ⊢
      have hr : rdArr (fun _ _ => none)
          ((.Lopn [.reg (ρ d)] "STOREIDX" [.arrIdx (ρ b) y 8, .reg v], .store w n) : LinstrRM) =
          [ρ b] := rfl
      rw [hr] at hT
      intro ds o ss he
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨fun b' y' s' hb' => ?_, fun ho => absurd ho (by decide)⟩
      simp only [List.mem_cons, LOperand.arrIdx.injEq, reduceCtorEq, List.not_mem_nil,
        or_false] at hb'
      rw [hb'.1]
      exact hT _ List.mem_cons_self
    · have h1 : stDst ((.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n) :
          LinstrRM) = some d := rfl
      have h2 : zeroDst? ((.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n) :
          LinstrRM) = none := rfl
      have h3 : wrArr (fun _ => none)
          ((.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n) : LinstrRM) =
          some d := rfl
      rw [h1, h2] at hx
      rw [h3]
      simpa using hx
    · have h3 : wrArr (fun _ => none)
          ((.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n) : LinstrRM) =
          some d := rfl
      rw [h3] at hd'
      cases hd'
      have hR : renArr ρ
          ((.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n) : LinstrRM) =
          (.Lopn [.reg (ρ d)] "STOREIDX" [.arrIdx (ρ b) y 8, .reg v], .store w n) := by
        simp [renArr, X86Backend.ImageCoalesceCfg.renStore]
      rw [hR]
      rfl
  · have hrw := rdArr_wrArr_noAcc h3 hp
    have hsz := stDst_zeroDst_noAcc h3
    refine ⟨fun T _ b hb => ?_, fun ρ T _ => idxIn_noAcc (noAcc_renArr ρ h3) T,
      fun x hx => ?_, fun ρ d hd => ?_⟩
    · rw [hrw.1] at hb
      cases hb
    · rw [hsz.1, hsz.2] at hx
      simp at hx
    · rw [hrw.2] at hd
      cases hd

end Class


/-! ## 5. The width of the accesses -/

section Width

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (regionExportableB
  bindMemNB)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (arrW64B opW64B)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree)

/-- Every array type of the context is of `64`-bit words. -/
def CtxW64 (Γ : Ctxt jasminDialect) : Prop := ∀ w m, JasminTy.stackArr w m ∈ Γ → w = 64

/-- A memory-free binding the region export accepts is of a register type and passes the
    width condition. -/
theorem memFree_bind {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (he : jMemFree e.op = true) (hb : bindMemNB e = true) :
    opW64B e.op = true ∧ ∀ w m, t ≠ .stackArr w m := by
  obtain ⟨op, heq, args⟩ := e
  subst heq
  unfold bindMemNB at hb
  cases op <;> simp_all [jMemFree, opW64B, X86Backend.ExportCertFragment.opMemB,
    DialectSignature.ret]

/-- **A chain of stores over a context of `64`-bit word arrays passes the width condition.** -/
theorem arrW64B_chainTail {Γ : Ctxt jasminDialect} {w m : Nat} {v : Ctxt.Var Γ (.stackArr w m)}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (h : ChainTail v p)
    (hE : regionExportableB p = true) (hΓ : CtxW64 Γ) : arrW64B p = true := by
  induction h with
  | free v e k he _ ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      obtain ⟨h1, h2⟩ := memFree_bind e he hE.1
      simp only [arrW64B, h1, Bool.true_and]
      refine ih hE.2 fun w' m' hm => ?_
      rcases List.mem_cons.mp hm with hm | hm
      · exact absurd hm.symm (h2 w' m')
      · exact hΓ w' m' hm
  | store v i x k _ ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      have hw := hΓ _ _ (mem_of_var v)
      subst hw
      simp only [arrW64B, opW64B, beq_self_eq_true, Bool.true_and]
      refine ih hE.2 fun w' m' hm => ?_
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        rfl
      · exact hΓ w' m' hm
  | ret v => rfl

/-- **Loads and a chain of stores over a context of `64`-bit word arrays pass the width
    condition.** -/
theorem arrW64B_loadsChainS {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) (hE : regionExportableB p = true)
    (hΓ : CtxW64 Γ) : arrW64B p = true := by
  induction h with
  | free e k he _ ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      obtain ⟨h1, h2⟩ := memFree_bind e he hE.1
      simp only [arrW64B, h1, Bool.true_and]
      refine ih hE.2 fun w' m' hm => ?_
      rcases List.mem_cons.mp hm with hm | hm
      · exact absurd hm.symm (h2 w' m')
      · exact hΓ w' m' hm
  | load a i k _ ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      have hw := hΓ _ _ (mem_of_var a)
      subst hw
      simp only [arrW64B, opW64B, beq_self_eq_true, Bool.true_and]
      refine ih hE.2 fun w' m' hm => ?_
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
      · exact hΓ w' m' hm
  | store v i x k hk =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      have hw := hΓ _ _ (mem_of_var v)
      subst hw
      simp only [arrW64B, opW64B, beq_self_eq_true, Bool.true_and]
      refine arrW64B_chainTail hk hE.2 fun w' m' hm => ?_
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        rfl
      · exact hΓ w' m' hm

end Width


/-! ## 6. The access form of the allocator input -/

section Input

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (NoCArr)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (AccP AccCode ImmCode UntagP
  ArgSlotName NoArrImm)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSide (IdxAcc)

/-- The predicate of the access form `InputAcc` on the base of an access: no frame-slot name,
    paired with an argument register that has a save slot. -/
def InBase (pairs : List (String × String)) (b : String) : Prop :=
  isFrameSlotName b = false ∧ ∃ p ∈ pairs, p.1 = b ∧ (abiSlotOfExt p.2).isSome = true

/-- **The access form `InputAcc` from `AccP`**, without register-indexed operand outside the
    accesses and without compile-time array operand. -/
theorem inputAcc_of_accP {pairs : List (String × String)} {w : LinstrR}
    (hA : AccP (InBase pairs) w) (hI : IdxAcc w) (hN : NoCArr w) : InputAcc pairs w := by
  intro ds o ss he
  subst he
  have h := hA ds o ss rfl
  by_cases hL : o = "LOADIDX"
  · obtain ⟨d, b, y, rfl, rfl⟩ := h.1 hL
    obtain ⟨h1, h2⟩ := h.2.2.1 b y 8 (by simp)
    exact .inr (.inl ⟨d, b, y, hL, rfl, rfl, h1, h2⟩)
  by_cases hS : o = "STOREIDX"
  · obtain ⟨d, b, y, v, rfl, rfl⟩ := h.2.1 hS
    obtain ⟨h1, h2⟩ := h.2.2.1 b y 8 (by simp)
    exact .inr (.inr ⟨d, b, y, v, hS, rfl, rfl, h1, h2⟩)
  refine .inl fun a ha => ?_
  cases a with
  | reg x => exact .inl ⟨x, rfl⟩
  | imm v => exact .inr ⟨v, rfl⟩
  | arr b k => exact absurd rfl (hN _ ha b k)
  | arrIdx b y s => exact absurd ha (hI ds o ss rfl hL hS b y s)

/-- The first entry of `l.zipIdx s` at the argument name of `j` is the entry at `j`. -/
theorem find?_zipIdx_argName : ∀ (l : List String) (s j : Nat) (h1 : s ≤ j)
    (h2 : j < s + l.length),
    (l.zipIdx s).find? (fun q => argName q.2 == argName j) = some (l[j - s]'(by omega), j)
  | [], s, j, h1, h2 => by simp at h2; omega
  | x :: l, s, j, h1, h2 => by
      rw [List.zipIdx_cons, List.find?_cons]
      by_cases hj : s = j
      · subst hj
        simp
      · have hne : (argName s == argName j) = false := by
          simpa using fun h => hj (argName_inj h)
        rw [hne]
        dsimp only
        rw [find?_zipIdx_argName l (s + 1) j (by omega) (by simp at h2; omega)]
        have he : j - s = j - (s + 1) + 1 := by omega
        simp only [he, List.getElem_cons_succ]

/-- **An array parameter with a save slot is a base of the access form** at the pairs of the
    argument bases of the direct route. -/
theorem inBase_of_argSlotName {σ : AbiLayout} (fname : String) {x : String}
    (h : ArgSlotName σ x) :
    InBase (argBasePairs true (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
      (nfAbiNames fname σ).abiArgs) x := by
  obtain ⟨j, rfl, a, n, ha, hk, hs⟩ := h
  refine ⟨RegionPhysImg.isFrameSlotName_argName j, (argName j, exportReg a.reg), ?_, rfl, hs⟩
  have hj : j < σ.args.length := (List.getElem?_eq_some_iff.mp ha).1
  have hmem : argName j ∈ (nfAbiNames fname σ).outArg :: (nfAbiNames fname σ).inArgs := by
    by_cases ho : nfOutIdx σ = some j
    · simp [nfAbiNames, ho]
    · refine List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨(a, j), ?_, ?_⟩)
      · exact List.mem_zipIdx_iff_getElem?.mpr ha
      · simp [hk, ho]
  simp only [argBasePairs, argBasePairsPos]
  refine List.mem_filterMap.mpr ⟨argName j, hmem, ?_⟩
  have hf : ((nfAbiNames fname σ).abiArgs.zipIdx.find? fun q => argName q.2 == argName j) =
      some (exportReg a.reg, j) := by
    have h := find?_zipIdx_argName (nfAbiNames fname σ).abiArgs 0 j (Nat.zero_le _)
      (by simp [nfAbiNames, hj])
    rw [h]
    simp [nfAbiNames, List.getElem_map, (List.getElem?_eq_some_iff.mp ha).2]
  rw [hf]
  rfl

end Input


/-! ## 7. The roots of the webs -/

section Roots

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (AccCode ImmCode ArgSlotName
  RootIn ResNamed ArrNamed wordsSlotB exportR_idxOk exportR_accCode exportR_immCode_copy
  idxOk_regionLprogCopy idxOk_append le_afterDst outArg_argSlotName
  canonMemrefName_aliasTab_of_idxOk zeroDst?_of_noArrImm noArrImm_regionLprogCopy)

/-- The array variables of the widened context are those of the context. -/
theorem arrNamed_map_wideTy {S : String → Prop} {nArgs d : Nat} {Γ : Ctxt jasminDialect}
    (h : ArrNamed S nArgs d Γ) : ArrNamed S nArgs d (Γ.map NarrowWords.wideTy) := by
  intro i w m hi
  rw [List.getElem?_map] at hi
  obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hi
  cases t with
  | stackArr w' m' =>
      simp only [NarrowWords.wideTy, JasminTy.stackArr.injEq] at he
      exact h i w' m' ht
  | reg w' => simp [NarrowWords.wideTy] at he
  | inlineInt => simp [NarrowWords.wideTy] at he
  | bool => simp [NarrowWords.wideTy] at he

/-- **The coalescing renaming of the webs sends every array name to a parameter with a save
    slot**: for a program of the shape `LoadsChainS` of the region route over a context whose
    array variables are named by such parameters, at the width condition, the array names
    (`RootIn`) of every instruction of the webs of the export followed by their result copy
    are sent by the renaming at the result alias to a word-array parameter with a save slot. -/
theorem webs_aliasRoots (fname : String) (σ : AbiLayout) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true) (hL : LoadsChainS p)
    (hσ : wordsSlotB σ = true) (hA : ArrNamed (ArgSlotName σ) Γ.length Γ.length Γ)
    {r0 : Exported} (hr0 : exportR Γ.length fname p Γ.length 0 x86Data = some r0)
    (ex : List String) :
    ∀ i ∈ (regionWebs ex r0).code ++ regionLprogCopy (nfAbiNames fname σ) none ts
        (regionWebs ex r0).code (regionWebs ex r0).res,
      RootIn (fun x => ArgSlotName σ (canonMemrefName (resAliasTab []
        (resAliasOf none (some (nfAbiNames fname σ).outArg) ts (regionWebs ex r0).res)
        ((regionWebs ex r0).code ++ regionLprogCopy (nfAbiNames fname σ) none ts
          (regionWebs ex r0).code (regionWebs ex r0).res)) x)) i := by
  obtain ⟨k1, k2⟩ := exportR_idxOk _ fname p hp hc _ 0 r0 hr0 le_rfl (ArgSlotName σ) hA
  obtain ⟨⟨x, hE⟩, -⟩ := loadsChainS_export_class (fn := fname) hL le_rfl hr0
  have hAcc := exportR_accCode _ _ p hc hw _ _ r0 hr0
  have hImm : ∀ i ∈ r0.code, ImmCode i := fun i hi =>
    exportR_immCode_copy (nfAbiNames fname σ) p hc hr0 i (List.mem_append_left _ hi)
  have hplain : ∀ i ∈ r0.code, PlainTag i := fun i hi => by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact (hE k i hk).1
  have hsh := (regionExp_of_exportR ex hr0).noShadow hp hc
  have hst : ∀ (k : Nat) (i : LinstrRM), r0.code[k]? = some i → StraightOp i := fun k i hk =>
    straightOp_of_lopn (hsh i (List.mem_of_getElem? hk)) (hE k i hk).2.1
  have hF := fun i hi => accFacts (hAcc i hi) (hImm i hi) (hplain i hi)
  have hW : IdxOk (ArgSlotName σ) (regionWebs ex r0).code ∧
      ResNamed (afterDst (ArgSlotName σ) (regionWebs ex r0).code) ts r0.res := by
    rcases RegionExportDefInit.regionWebs_webB ex r0 with he | ⟨w, hacc, he⟩ <;> rw [he]
    · exact ⟨k1, k2⟩
    · refine ⟨idxOk_webRen hacc hst hplain (fun i hi => (hF i hi).1) (fun i hi => (hF i hi).2.1)
        (fun i hi => (hF i hi).2.2.1) (fun i hi => (hF i hi).2.2.2) k1, fun j w' m hj => ?_⟩
      obtain ⟨o, ho, hS⟩ := k2 j w' m hj
      refine ⟨o, ho, afterDst_webRen hacc hst (fun i hi => (hF i hi).2.2.1)
        (fun i hi => (hF i hi).2.2.2) ?_ hS⟩
      simp only [regionWebsObs, List.mem_append, List.mem_map]
      exact .inl ⟨o, List.mem_of_getElem? ho, rfl⟩
  rw [regionWebs_res]
  have hcopy := idxOk_regionLprogCopy (code := (regionWebs ex r0).code) (nfAbiNames fname σ) ts
    hW.2 fun h => le_afterDst _ (outArg_argSlotName hσ fname h)
  have hok := idxOk_append hW.1 (fun _ h => h) hcopy
  have hz : ∀ i ∈ (regionWebs ex r0).code ++ regionLprogCopy (nfAbiNames fname σ) none ts
      (regionWebs ex r0).code r0.res, zeroDst? i = none := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · refine (forall_mem_regionWebs
        (P := fun i => PlainTag i ∧ RegionCoComplete.NoShadow i ∧ zeroDst? i = none)
        (fun ρ i hi => ⟨by rw [PlainTag, renArr_snd]; exact hi.1,
          RegionCoComplete.noShadow_renArr ρ hi.2.1, zeroDst?_renArr ρ hi.1 hi.2.1 hi.2.2⟩)
        ex r0 _ _ (fun i hi => ?_) i hi).2.2
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
      exact ⟨hplain i hi, hsh i hi, (hE k i hk).2.2.1⟩
    · exact zeroDst?_of_noArrImm (noArrImm_regionLprogCopy _ ts _ _ i hi)
  rw [resAliasTab_eq_of_noZero _ _ hz]
  exact canonMemrefName_aliasTab_of_idxOk (ArgSlotName σ) hok (fun _ h => h)
    fun i hi z hz' => by rw [hz i hi] at hz'; cases hz'

end Roots


/-! ## 8. The field domain -/

section Field

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (NoCArr)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (AccCode ImmCode UntagP NoArrImm
  ArgSlotName wordsSlotB rootIn_mono immCode_of_noArrImm noArrImm_regionLprogCopy
  untagP_regionLprogCopy exportR_untagP exportR_noCArr noCArr_renArr noCArr_regionAllocCode
  noCArr_canonicalizeMemrefThread noCArr_regionLprogCopy noCArr_livepin noCArr_livepin_range
  accP_regionAllocBody arrNamed_nfCtx)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSide (idxAcc_regionAllocBody)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)

/-- The renaming of the array positions writes no zeroing and no constant-index store of an
    instruction of the form `ImmCode` with a plain tag. -/
theorem noArrImm_renArr_plain (ρ : String → String) {i : LinstrRM} (hm : ImmCode i)
    (hp : PlainTag i) : NoArrImm (renArr ρ i).1 := by
  intro ds o ss he
  obtain ⟨ds0, ss0, hi, -⟩ := RegionPhysImgArg.renArr_lopn ρ he
  constructor
  · rintro rfl
    obtain ⟨_, _, _, _, _, rfl⟩ := hm.1 ds0 ss0 hi
    exact absurd hp id
  · rintro rfl
    obtain ⟨_, _, _, _, _, _, rfl⟩ := hm.2 ds0 ss0 hi
    exact absurd hp id

/-- The renaming of the array positions keeps an untagged mnemonic. -/
theorem untagP_renArr (ρ : String → String) {i : LinstrRM} (h : UntagP i.1) :
    UntagP (renArr ρ i).1 := by
  intro ds o ss he
  obtain ⟨ds0, ss0, hi, -⟩ := RegionPhysImgArg.renArr_lopn ρ he
  exact h ds0 o ss0 hi

/-- **No instruction of the allocator input body has a compile-time array operand** when no
    instruction of the code does, at a result other than one register. -/
theorem noCArr_regionAllocBody_of (a : AbiNames) (nArgs : Nat) {ts : List JasminTy}
    {r : Exported} (hN : ∀ i ∈ r.code, NoCArr i.1) (hts : ∀ w, ts ≠ [.reg w]) :
    ∀ i ∈ regionAllocBody a nArgs ts r, NoCArr i.li_i := by
  have hac : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
      (resAliasOf none (some a.outArg) ts r.res),
      NoCArr i.1 := by
    refine noCArr_regionAllocCode fun i hi => ?_
    rcases List.mem_append.mp hi with hi | hi
    · exact hN i hi
    · exact noCArr_regionLprogCopy a ts r.code r.res i hi
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · exact absurd rfl (hts _)
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact noCArr_livepin_range _
      · cases hi
    · refine noCArr_canonicalizeMemrefThread (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]; exact noCArr_livepin _
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
          exact hac l hl
        · rw [List.mem_singleton.mp hj]; trivial

/-- The context of the direct route, widened, is of `64`-bit word arrays. -/
theorem ctxW64_nfCtx (σ : AbiLayout) : CtxW64 ((nfCtx σ).map NarrowWords.wideTy) := by
  intro w m hm
  simp only [nfCtx, CryptoToJasminCom.mapCtx, CatCrypt.Crypto.Hax.ImpToNF.entryCtx,
    NFToRoute.abiEntry, CatCrypt.Crypto.Hax.NFToCat.abiParamsArr, List.map_reverse, List.map_map,
    List.mem_reverse, List.mem_map, Function.comp_apply] at hm
  obtain ⟨a, -, ha⟩ := hm
  cases hk : a.kind <;>
    simp [hk, CatCrypt.Crypto.Hax.NFToCat.abiKindArr, CatCrypt.Crypto.Hax.NFToCat.catTy,
      CryptoToJasminCom.mapTy, NarrowWords.wideTy, NarrowWords.wideW] at ha
  grind

/-- The word-array parameters of the field layout have save slots. -/
theorem wordsSlotB_fieldAbi {k n : Nat} (hk : k = 1 ∨ k = 2) : wordsSlotB (fieldAbi k n) = true := by
  have x0 : exportReg "%rdi" = "RDI" := by decide
  have x1 : exportReg "%rsi" = "RSI" := by decide
  have x2 : exportReg "%rdx" = "RDX" := by decide
  have s0 : (abiSlotOfExt "RDI").isSome = true := by decide
  have s1 : (abiSlotOfExt "RSI").isSome = true := by decide
  have s2 : (abiSlotOfExt "RDX").isSome = true := by decide
  rcases hk with rfl | rfl <;>
    simp [wordsSlotB, fieldAbi, List.range_succ, FieldRoute.fieldArgReg, x0, x1, x2, s0, s1, s2]

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String}

/-- **The access form of the allocator input of a member of `fieldDomB'`**: the result is no
    register, and every instruction of the allocator input of the webs of the export has the
    access form `InputAcc` at the pairs of the argument bases. -/
theorem allocInputAcc_of_fieldDomB' (h : fieldDomB' e σ = true) : AllocInputAcc e σ fname := by
  intro t0 q q' r0 hq hq' hr0
  have hd := fieldDomB_of_fieldDomB' h
  obtain ⟨k, n, hk, rfl, -⟩ := fieldDomB'_layout h
  have hk' := fieldDomE_k hk
  have ht0 : t0 = .stackArr 64 n := fieldDom_chainTy hd hq hk' rfl
  subst ht0
  have hts : ∀ w, NarrowWords.wideTy (.stackArr 64 n) ≠ .reg w := fun w h' => by
    simp [NarrowWords.wideTy] at h'
  refine ⟨hts, ?_⟩
  have hts' : ∀ w, [NarrowWords.wideTy (.stackArr 64 n)] ≠ [.reg w] := fun w h' =>
    hts w (List.cons.inj h').1
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal hd) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree hd hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hL := fieldDom_legalize_loadsChainS hd hq hq'
  have hw := arrW64B_loadsChainS hL hEx (ctxW64_nfCtx _)
  have hσ := wordsSlotB_fieldAbi (n := n) hk'
  have hA : RegionPhysImgArg.ArrNamed (ArgSlotName (fieldAbi k n))
      ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy).length
      ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy).length
      ((nfCtx (fieldAbi k n)).map NarrowWords.wideTy) := by
    rw [List.length_map]
    exact arrNamed_map_wideTy (arrNamed_nfCtx hσ)
  have hX : RegionExp fname (legalizeRegion q') (regionWebsEx (fieldAbi k n) exportReg)
      (regionWebs (regionWebsEx (fieldAbi k n) exportReg) r0) := regionExp_webs _ hr0
  rw [regionWebsAt_none]
  set ex := regionWebsEx (fieldAbi k n) exportReg
  set a := nfAbiNames fname (fieldAbi k n)
  have hC := RegionExp.accCode_copy (a := a) (ts := [NarrowWords.wideTy (.stackArr 64 n)]) hcf
    hw hX
  have hAcc := RegionPhysImgArg.exportR_accCode _ _ _ hcf hw _ _ r0 hr0
  obtain ⟨⟨x, hE⟩, -⟩ := loadsChainS_export_class (fn := fname) hL le_rfl hr0
  have hplain : ∀ i ∈ r0.code, PlainTag i := fun i hi => by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact (hE k i hk).1
  have hImm0 : ∀ i ∈ r0.code, ImmCode i := fun i hi =>
    RegionPhysImgArg.exportR_immCode_copy a _ hcf hr0 i (List.mem_append_left _ hi)
  have hI : ∀ i ∈ (regionWebs ex r0).code ++ regionLprogCopy a none
      [NarrowWords.wideTy (.stackArr 64 n)] (regionWebs ex r0).code (regionWebs ex r0).res,
      ImmCode i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · refine (forall_mem_regionWebs (P := fun i => ImmCode i ∧ PlainTag i)
        (fun ρ i hi => ⟨immCode_of_noArrImm (noArrImm_renArr_plain ρ hi.1 hi.2),
          by rw [PlainTag, renArr_snd]; exact hi.2⟩)
        ex r0 _ _ (fun i hi => ⟨hImm0 i hi, hplain i hi⟩) i hi).1
    · exact immCode_of_noArrImm (noArrImm_regionLprogCopy _ _ _ _ i hi)
  have hU : ∀ i ∈ (regionWebs ex r0).code ++ regionLprogCopy a none
      [NarrowWords.wideTy (.stackArr 64 n)] (regionWebs ex r0).code (regionWebs ex r0).res,
      UntagP i.1 := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact forall_mem_regionWebs (P := fun i => UntagP i.1) (fun ρ i hi => untagP_renArr ρ hi)
        ex r0 _ _ (exportR_untagP _ _ _ hcf _ _ r0 hr0) i hi
    · exact untagP_regionLprogCopy _ _ _ _ i hi
  have hN : ∀ i ∈ (regionWebs ex r0).code, NoCArr i.1 :=
    forall_mem_regionWebs (P := fun i => NoCArr i.1) (fun ρ i hi => noCArr_renArr ρ hi)
      ex r0 _ _ (exportR_noCArr _ _ _ hcf _ _ r0 hr0)
  have hroot := webs_aliasRoots fname (fieldAbi k n) _ hEx hcf hw hL hσ hA hr0 ex
  intro i hi
  refine inputAcc_of_accP ?_ (idxAcc_regionAllocBody _ _ _ hts' hC i hi)
    (noCArr_regionAllocBody_of _ _ hN hts' i hi)
  exact accP_regionAllocBody _ _ _ _ hts' hC hI
    (fun i hi => rootIn_mono (fun x hx => inBase_of_argSlotName fname hx) (hroot i hi)) hU i hi

/-- **Stage `G20` on `fieldDomB'`**, without hypothesis. -/
theorem fieldDom_cellNamesRB' {b : Lcmd} {t : JasminTy} {r : Exported}
    {cert : List (String × String)} (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellNamesRB" :=
  fieldDom_cellNamesRB_of_allocInputAcc h hB (allocInputAcc_of_fieldDomB' h)

/-- **The printed body of a member of `fieldDomB'` reads no stack-argument name.** -/
theorem stackReadFreeB_fieldDom {b : Lcmd} {t : JasminTy} {r : Exported}
    {cert : List (String × String)} (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    X86Backend.ImageAddrRoute.stackReadFreeB b = true :=
  stackReadFreeB_of_allocInputAcc h hB (allocInputAcc_of_fieldDomB' h)

end Field

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
