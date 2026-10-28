/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-!
# The image of a physical body as a typed body

`JasminLsemAddrImage.virtImg sl b` maps instruction `k` of the body `b` without its final
instruction to `imgInstr sl b k`, an instruction with a memory tag. `OwnedLprogTV.typeBody tag c`
types each instruction of `c` with `tag`, a function of the instruction alone. This module
states when the image is a typed body: `imgL sl b` is the body of the image instructions
followed by a return, and the image is `dropRet (typeBody T (imgL sl b))` for some `T` exactly
when equal image instructions carry equal tags (`ImgTagFun`).

## Main results

* `exists_map_fst_eq_iff`: a list of pairs is the graph of a function on its first components
  exactly when equal first components carry equal second components.
* `dropRet_typeBody_imgL`: the typed body of `imgL sl b` without its return is the image with
  each tag replaced by the tag of its instruction.
* `virtImg_eq_typeBody`: under `ImgTagFun sl b`, `virtImg sl b` is
  `dropRet (typeBody (imgTag sl b) (imgL sl b))`.
* `exists_virtImg_eq_typeBody_iff`: the image is a typed body of `imgL sl b` exactly when
  `ImgTagFun sl b` holds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (typeBody dropRet)

/-! ## 1. Lists of pairs that are graphs -/

/-- Equal first components of members of `l` carry equal second components. -/
def FstFun {α β : Type} (l : List (α × β)) : Prop :=
  ∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 → p.2 = q.2

open Classical in
/-- The second component that `l` pairs with `a`, and `d` when no member of `l` has first
    component `a`. -/
noncomputable def graphFn {α β : Type} (d : β) (l : List (α × β)) (a : α) : β :=
  if h : ∃ p ∈ l, p.1 = a then (Classical.choose h).2 else d

/-- Under `FstFun l`, `graphFn d l` maps the first component of each member of `l` to its
    second component. -/
theorem graphFn_mem {α β : Type} (d : β) {l : List (α × β)} (hl : FstFun l) {p : α × β}
    (hp : p ∈ l) : graphFn d l p.1 = p.2 := by
  have h : ∃ q ∈ l, q.1 = p.1 := ⟨p, hp, rfl⟩
  simp only [graphFn, h, dite_true]
  obtain ⟨hq, hq1⟩ := Classical.choose_spec h
  exact hl _ hq p hp hq1

/-- A list of pairs is the graph of a function on its first components exactly when equal
    first components carry equal second components. -/
theorem exists_map_fst_eq_iff {α β : Type} [Inhabited β] (l : List (α × β)) :
    (∃ T : α → β, l = l.map fun p => (p.1, T p.1)) ↔ FstFun l := by
  constructor
  · rintro ⟨T, hT⟩
    have h2 : ∀ p ∈ l, p.2 = T p.1 := by
      intro p hp
      rw [hT] at hp
      obtain ⟨r, -, hr⟩ := List.mem_map.mp hp
      grind
    intro p hp q hq hpq
    rw [h2 p hp, h2 q hq, hpq]
  · intro hl
    refine ⟨graphFn default l, ?_⟩
    conv_lhs => rw [← List.map_id l]
    refine List.map_congr_left fun p hp => ?_
    rw [graphFn_mem default hl hp]
    rfl

/-! ## 2. The image body -/

/-- The body of the image instructions of `virtImg sl b`, followed by a return when `b` is not
    empty. -/
def imgL (sl : String → Option (String × Nat)) (b : Lcmd) : Lcmd :=
  (b.dropLast.mapIdx fun k i => { i with li_i := (imgInstr sl b k i.li_i).1 }) ++
    (b.getLast?.map fun j => { j with li_i := .Lret }).toList

/-- The typed body of `imgL sl b` without its return is `virtImg sl b` with each tag replaced
    by the tag `T` of its instruction. -/
theorem dropRet_typeBody_imgL (sl : String → Option (String × Nat)) (b : Lcmd)
    (T : LinstrR → MemTag) :
    dropRet (typeBody T (imgL sl b)) = (virtImg sl b).map fun p => (p.1, T p.1) := by
  have hmid : typeBody T (b.dropLast.mapIdx fun k i =>
      ({ i with li_i := (imgInstr sl b k i.li_i).1 } : Linstr)) =
      (virtImg sl b).map fun p => (p.1, T p.1) := by
    apply List.ext_getElem?
    intro n
    simp [typeBody, virtImg, List.getElem?_mapIdx, Function.comp_def]
  cases hb : b.getLast? with
  | none =>
      have : b = [] := List.getLast?_eq_none_iff.mp hb
      subst this
      simp [dropRet, typeBody, imgL, virtImg]
  | some j =>
      simp only [imgL, hb, Option.map_some, Option.toList_some, typeBody, List.map_append,
        List.map_cons, List.map_nil]
      rw [show (List.map (fun i : Linstr => (i.li_i, T i.li_i)) (b.dropLast.mapIdx fun k i =>
          ({ i with li_i := (imgInstr sl b k i.li_i).1 } : Linstr))) =
          (virtImg sl b).map fun p => (p.1, T p.1) from hmid]
      simp [dropRet]

/-! ## 3. The image as a typed body -/

/-- Equal instructions of the image `virtImg sl b` carry equal tags. -/
def ImgTagFun (sl : String → Option (String × Nat)) (b : Lcmd) : Prop :=
  FstFun (virtImg sl b)

/-- The tag of an image instruction of `virtImg sl b`, and `.reg none` off the image. -/
noncomputable def imgTag (sl : String → Option (String × Nat)) (b : Lcmd) :
    LinstrR → MemTag :=
  graphFn (.reg none) (virtImg sl b)

/-- **The image as a typed body.** When equal image instructions carry equal tags,
    `virtImg sl b` is the typed body of `imgL sl b` at the tag `imgTag sl b`, without its
    return. -/
theorem virtImg_eq_typeBody {sl : String → Option (String × Nat)} {b : Lcmd}
    (h : ImgTagFun sl b) : virtImg sl b = dropRet (typeBody (imgTag sl b) (imgL sl b)) := by
  rw [dropRet_typeBody_imgL]
  conv_lhs => rw [← List.map_id (virtImg sl b)]
  refine List.map_congr_left fun p hp => ?_
  rw [imgTag, graphFn_mem _ h hp]
  rfl

/-- The image `virtImg sl b` is a typed body of `imgL sl b` without its return, at some tag,
    exactly when equal image instructions carry equal tags. -/
theorem exists_virtImg_eq_typeBody_iff (sl : String → Option (String × Nat)) (b : Lcmd) :
    (∃ T : LinstrR → MemTag, virtImg sl b = dropRet (typeBody T (imgL sl b))) ↔
      ImgTagFun sl b := by
  have : Inhabited MemTag := ⟨.reg none⟩
  simp only [dropRet_typeBody_imgL]
  exact exists_map_fst_eq_iff (virtImg sl b)

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSem
