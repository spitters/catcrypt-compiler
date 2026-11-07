/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVComplete
public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg

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
* `imgL_eq_dropLast_append`, `dropRet_typeBody_imgL_eq_dropLast`: the image body ends with a
  return, and its typed form without the return is the typed form of its other instructions.
* `tagShape_shapeTag`, `tagFirstSrc_shapeTag`: the tag `shapeTag l`, read from the members of
  `l` by the destinations and the mnemonic of an instruction, has the shape conditions of the
  typed pass theorems.
* `virtImg_eq_typeBody_shapeTag`: when the tags of `l` are functions of the instruction shape
  (`shapeFunB`) and `l` holds the image, `virtImg sl b` is the typed body of `imgL sl b` at
  `shapeTag l`, without its return.
* `virtImg_eq_typeBody_of_imgL_eq`: when the image body of `c` is a pass `f` applied to the
  image body of `b`, the images of `b` and `c` are the typed bodies of `imgL sl b` and of
  `f (imgL sl b)` at one tag of the instruction shape, so a theorem of `f` on typed bodies
  under the shape conditions holds between the two images.
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

/-- The image body of the empty body is empty. -/
@[simp] theorem imgL_nil (sl : String → Option (String × Nat)) : imgL sl [] = [] := rfl

/-- The image body of a body whose last instruction is `j` is its instructions before the
    return followed by the return at the position of `j`. -/
theorem imgL_eq_dropLast_append {sl : String → Option (String × Nat)} {b : Lcmd} {j : Linstr}
    (hj : b.getLast? = some j) :
    imgL sl b = (imgL sl b).dropLast ++ [⟨j.li_ii, .Lret⟩] := by
  simp [imgL, hj]

/-- The typed image body without its return is the typed image body without its last
    instruction. -/
theorem dropRet_typeBody_imgL_eq_dropLast (sl : String → Option (String × Nat)) (b : Lcmd)
    (T : LinstrR → MemTag) :
    dropRet (typeBody T (imgL sl b)) = typeBody T (imgL sl b).dropLast := by
  cases hj : b.getLast? with
  | none =>
      rw [List.getLast?_eq_none_iff.mp hj]
      rfl
  | some j =>
      rw [imgL_eq_dropLast_append hj]
      simp [dropRet, typeBody, List.getLast?_append]

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

/-! ## 4. A tag of the instruction shape

The typed pass theorems take a tag that is a function of the destinations and the mnemonic of
an instruction (`LsemBridgePass.CopyPropCfg.TagShape`). `shapeTag l` reads such a tag from the
members of a list of typed instructions; `shapeFunB l` decides that the tags of `l` are
functions of the instruction shape, and then `shapeTag l` gives every member of `l` its own
tag. -/

/-- The instruction is an `Lopn` with the destinations `d` and the mnemonic `o`. -/
def sameShapeB (d : List LOperand) (o : String) : LinstrR → Bool
  | .Lopn d' o' _ => d' == d && o' == o
  | _ => false

/-- The tag that the typed instructions `l` give the shape of `i`: for an `Lopn` with
    destinations `d` and mnemonic `o`, the tag of the first member of `l` whose instruction has
    that shape (`sameShapeB`), and `.reg none` when there is none; `.reg none` for every other
    instruction. -/
def shapeTag (l : List LinstrRM) (i : LinstrR) : MemTag :=
  match i with
  | .Lopn d o _ => ((l.find? fun p => sameShapeB d o p.1).map Prod.snd).getD (.reg none)
  | _ => .reg none

/-- **The tags of `l` are functions of the instruction shape**: two members whose instructions
    are `Lopn`s with equal destinations and mnemonic carry equal tags, and every member whose
    instruction is not an `Lopn` carries `.reg none`. -/
def shapeFunB (l : List LinstrRM) : Bool :=
  l.all fun p => match p.1 with
    | .Lopn d o _ => l.all fun q => !sameShapeB d o q.1 || q.2 == p.2
    | _ => p.2 == .reg none

/-- The tag `shapeTag l` depends on the destinations and the mnemonic of an `Lopn` only. -/
theorem tagShape_shapeTag (l : List LinstrRM) :
    LsemBridgePass.CopyPropCfg.TagShape (shapeTag l) := fun _ _ _ _ => rfl

/-- The tag `shapeTag l` does not read the first source of an `Lopn`. -/
theorem tagFirstSrc_shapeTag (l : List LinstrRM) : OwnedLprogTV.TagFirstSrc (shapeTag l) :=
  fun _ _ _ _ _ => rfl

/-- **Under `shapeFunB l` the tag `shapeTag l` gives every member of `l` its tag.** -/
theorem shapeTag_of_mem {l : List LinstrRM} (h : shapeFunB l = true) {p : LinstrRM}
    (hp : p ∈ l) : shapeTag l p.1 = p.2 := by
  obtain ⟨i, tg⟩ := p
  have hp' := List.all_eq_true.mp h _ hp
  cases i with
  | Lopn d o s =>
      simp only at hp'
      cases hf : l.find? (fun p => sameShapeB d o p.1) with
      | none =>
          have := List.find?_eq_none.mp hf _ hp
          simp [sameShapeB] at this
      | some q =>
          have hq := List.mem_of_find?_eq_some hf
          have hsq := List.find?_some hf
          have := List.all_eq_true.mp hp' q hq
          simp only [hsq, Bool.not_true, Bool.false_or, beq_iff_eq] at this
          simp only [shapeTag, hf, Option.map_some, Option.getD_some, this]
  | _ => exact ((by simpa using hp') : tg = .reg none).symm

/-- **The image as a typed body at a tag of the instruction shape.** When the tags of `l` are
    functions of the instruction shape and every instruction of the image `virtImg sl b` is a
    member of `l`, the image is the typed body of `imgL sl b` at `shapeTag l`, without its
    return. -/
theorem virtImg_eq_typeBody_shapeTag {sl : String → Option (String × Nat)} {b : Lcmd}
    {l : List LinstrRM} (h : shapeFunB l = true) (hsub : ∀ p ∈ virtImg sl b, p ∈ l) :
    virtImg sl b = dropRet (typeBody (shapeTag l) (imgL sl b)) := by
  rw [dropRet_typeBody_imgL]
  conv_lhs => rw [← List.map_id (virtImg sl b)]
  refine List.map_congr_left fun p hp => ?_
  rw [shapeTag_of_mem h (hsub p hp)]
  rfl

/-- **The images of a body and of its pass as typed bodies at one tag.** Let the image body of
    `c` be the pass `f` applied to the image body of `b`, and let the tags of the two images
    together be functions of the instruction shape. At the tag `T := shapeTag` of the two
    images, which satisfies `TagShape` and `TagFirstSrc`, the image of `b` is the typed body
    of `imgL sl b` and the image of `c` the typed body of `f (imgL sl b)`, both without their
    return. A theorem of `f` between typed bodies at a tag of the instruction shape therefore
    holds between the images of `b` and `c`. -/
theorem virtImg_eq_typeBody_of_imgL_eq {sl : String → Option (String × Nat)} {b c : Lcmd}
    {f : Lcmd → Lcmd} (hc : imgL sl c = f (imgL sl b))
    (h : shapeFunB (virtImg sl b ++ virtImg sl c) = true) :
    virtImg sl b = dropRet (typeBody (shapeTag (virtImg sl b ++ virtImg sl c)) (imgL sl b))
      ∧ virtImg sl c
        = dropRet (typeBody (shapeTag (virtImg sl b ++ virtImg sl c)) (f (imgL sl b))) := by
  refine ⟨virtImg_eq_typeBody_shapeTag h fun p hp => List.mem_append_left _ hp, ?_⟩
  rw [← hc]
  exact virtImg_eq_typeBody_shapeTag h fun p hp => List.mem_append_right _ hp

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSem
