/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

@[expose] public section

set_option autoImplicit false

/-!
# The decoded program of a function body's bytes

`DecodeGen.decodeLprog_encodeLfundefBytes_gen` decodes the function bytes of a body whose
per-instruction shapes are computed (`DecodeGen.shapesOf`, sound by `DecodeGen.shapeOf_ok`),
under the frame and branch hypotheses of `PhysAbiShape.decodeLprog_encodeLfundefBytes_shapes`.
This module collects those hypotheses into one Boolean class of bodies, `decodableLcmd`, and
names the program they decode to, `fundefLayout`, a function of the body alone.

`decodableLcmd body` holds when every instruction of `body` has a computed shape, the body
saves no register by `push`, its frame is non-zero and in `rel32` range, and the branches of
its item list that have a target label are well formed (`branchOKL`: every such branch
targets a defined label followed by an instruction, at the byte offset its displacement
names). A call of a named symbol has the shape `callSym`, which has no target label, so the
check reads no label at it; the relocating encoder resolves it against the symbol
(`LprogBytesLinkReloc.itemsFromReloc`). The class is a property of the body; no decoder runs
over the function's byte stream.

## Main results

* `decodeLprog_encodeLfundefBytes`: for every body in the class `decodableLcmd` whose item
  list denotes a program `p` (`fundefLayout body = some p`), the function bytes
  `encodeLfundefBytes body` decode to `p`.
* `decodeLprog_of_encodeChecked`: the same for the bytes of the gated encoder
  `encodeLfundefBytesChecked`.
* `decodeLprog_of_decodesToB`: bytes of the gated encoder decode to every program `p` that
  the Boolean test `decodesToB body p` accepts.
* `branchOK_of_branchOKL`: the branch check `branchOKL` is `LprogBytesDecode.branchOK` on an
  item list that denotes a program; `branchOK_of_branchOKL_noSym` on an item list with no call
  without target label, which `fundefItemsL_noSym` gives at shapes without `callSym`.
* `shapeOf_callSym`, `branchOKL_cons_callSym`: a call of a named symbol has the shape
  `callSym` whatever its label, and its item adds no condition to `branchOKL`.
* `target_fundefItems`: every target label that `branchOKL` reads on the item list of a body
  with computed shapes is the label of a conditional branch or of a call to a label of the
  body, never the label of a call of a named symbol.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lcmd Linstr LLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (dispOk32)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

/-- The item list of the function bytes of `body` over its computed shapes: the frame `leaq`,
    the items of the body, the closing `leaq` and `ret`. -/
def fundefItems (body : Lcmd) : List Item :=
  fundefItemsL body (shapesD (Params.ofBody body) body)

/-- The program the function bytes of `body` decode to: the program its item list denotes,
    each branch resolved to the index of the instruction after its target label. -/
def fundefLayout (body : Lcmd) : Option (List RInstr) :=
  expectedFrom (fundefItems body) (fundefItems body)

/-- **The branch check of the decodable bodies.** `LprogBytesDecode.branchOK` at every item
    of `items`, laid out from offset `off` inside `all`, except a call without target label,
    which it does not check. -/
def branchOKL (all : List Item) : Nat → List Item → Bool
  | _, [] => true
  | off, it :: rest =>
      (match it.dec, it.target with
        | some (.call _), none => true
        | _, _ => branchOK all off [it])
      && branchOKL all (off + it.bytes.length) rest

theorem branchOK_cons (all : List Item) (off : Nat) (it : Item) (rest : List Item) :
    branchOK all off (it :: rest)
      = (branchOK all off [it] && branchOK all (off + it.bytes.length) rest) := by
  simp [branchOK]

/-- The item of a call without target label adds no condition to `branchOKL`. -/
theorem branchOKL_cons_callSym (all : List Item) (off : Nat) {it : Item} (rest : List Item)
    {d : Int} (hd : it.dec = some (.call d)) (ht : it.target = none) :
    branchOKL all off (it :: rest) = branchOKL all (off + it.bytes.length) rest := by
  simp [branchOKL, hd, ht]

/-- `branchOKL` is `branchOK` at an item that is not a call without target label. -/
theorem branchOKL_cons_of_ne (all : List Item) (off : Nat) {it : Item} (rest : List Item)
    (hn : it.target = none → ∀ d, it.dec ≠ some (.call d)) :
    branchOKL all off (it :: rest)
      = (branchOK all off [it] && branchOKL all (off + it.bytes.length) rest) := by
  rcases hd : it.dec with _ | x
  · simp [branchOKL, hd]
  · cases x <;> cases ht : it.target <;> simp_all [branchOKL]

/-- **`branchOKL` is `branchOK` without calls without target label.** -/
theorem branchOK_of_branchOKL_noSym (all : List Item) :
    ∀ (items : List Item) (off : Nat),
      (∀ it ∈ items, it.target = none → ∀ d, it.dec ≠ some (.call d)) →
      branchOKL all off items = true → branchOK all off items = true := by
  intro items
  induction items with
  | nil => intro _ _ _; rfl
  | cons it rest ih =>
    intro off hn hb
    rw [branchOKL_cons_of_ne all off rest (hn it List.mem_cons_self), Bool.and_eq_true] at hb
    rw [branchOK_cons, hb.1, Bool.true_and]
    exact ih _ (fun j hj => hn j (List.mem_cons_of_mem _ hj)) hb.2

/-- An item list that denotes a program has no call without target label. -/
theorem noSym_of_expectedFrom (all : List Item) :
    ∀ (items : List Item), (expectedFrom all items).isSome = true →
      ∀ it ∈ items, it.target = none → ∀ d, it.dec ≠ some (.call d) := by
  intro items
  induction items with
  | nil => intro _ it hit; cases hit
  | cons x rest ih =>
    intro he it hit ht d hd
    have htail : (expectedFrom all rest).isSome = true := by
      simp only [expectedFrom] at he
      split at he <;> (try split at he) <;> simp_all
    rcases List.mem_cons.mp hit with rfl | hit
    · simp [expectedFrom, hd, ht] at he
    · exact ih htail it hit ht d hd

/-- **`branchOKL` is `branchOK` on an item list that denotes a program.** -/
theorem branchOK_of_branchOKL (all : List Item) (items : List Item) (off : Nat)
    (hb : branchOKL all off items = true) (he : (expectedFrom all items).isSome = true) :
    branchOK all off items = true :=
  branchOK_of_branchOKL_noSym all items off (noSym_of_expectedFrom all items he) hb

/-- An item of an instruction of shape `sh` that has no target label is no call, unless `sh`
    is the shape `callSym`. -/
theorem noSym_dItems (P : Params) (off : Nat) (i : Linstr) (sh : DShape)
    (hs : ∀ l, sh ≠ .one (.callSym l)) :
    ∀ it ∈ dItems P off i sh, it.target = none → ∀ d, it.dec ≠ some (.call d) := by
  intro it hit ht d hd
  cases sh with
  | one s =>
    simp only [dItems, List.mem_singleton] at hit
    subst hit
    cases s with
    | callSym l => exact hs l rfl
    | _ => simp_all [Shape.dec, Shape.target]
  | ops pcs =>
    simp only [dItems, List.mem_map] at hit
    obtain ⟨p, -, rfl⟩ := hit
    simp at hd

theorem noSym_itemsFromL (P : Params) :
    ∀ (b : Lcmd) (shs : List DShape) (off : Nat), (∀ sh ∈ shs, ∀ l, sh ≠ .one (.callSym l)) →
      ∀ it ∈ itemsFromL P off b shs, it.target = none → ∀ d, it.dec ≠ some (.call d) := by
  intro b
  induction b with
  | nil => intro shs off _ it hit; cases shs <;> cases hit
  | cons i b ih =>
    intro shs off hs it hit
    cases shs with
    | nil => cases hit
    | cons sh shs =>
      simp only [itemsFromL, List.mem_append] at hit
      rcases hit with hit | hit
      · exact noSym_dItems P off i sh (hs sh List.mem_cons_self) it hit
      · exact ih shs _ (fun s hm => hs s (List.mem_cons_of_mem _ hm)) it hit

/-- **The item list of a body at shapes without `callSym` has no call without target
    label.** -/
theorem fundefItemsL_noSym (body : Lcmd) (shs : List DShape)
    (hs : ∀ sh ∈ shs, ∀ l, sh ≠ .one (.callSym l)) :
    ∀ it ∈ fundefItemsL body shs, it.target = none → ∀ d, it.dec ≠ some (.call d) := by
  intro it hit
  simp only [fundefItemsL, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hit
  rcases hit with rfl | hit | rfl | rfl
  · simp [mkLea]
  · exact noSym_itemsFromL _ body shs 0 hs it hit
  · simp [mkLea]
  · simp [mkRet]

/-- **The decodable bodies.** Every instruction has a computed shape, no register is saved by
    `push`, the frame is non-zero with both frame displacements in `rel32` range, and the
    branches of the item list that have a target label are well formed (`branchOKL`). -/
def decodableLcmd (body : Lcmd) : Bool :=
  (shapesOf (Params.ofBody body) body).isSome
    && (calleeSavedToSave body).isEmpty
    && (Params.ofBody body).frame != 0
    && dispOk32 (Int.ofNat (Params.ofBody body).frame)
    && dispOk32 (-(Int.ofNat (Params.ofBody body).frame))
    && branchOKL (fundefItems body) 0 (fundefItems body)

/-- **The decode equation of a decodable body.** The function bytes of every body in the class
    `decodableLcmd` whose item list denotes the program `p` decode to `p`. -/
theorem decodeLprog_encodeLfundefBytes {body : Lcmd} {p : List RInstr}
    (h : decodableLcmd body = true) (hp : fundefLayout body = some p) :
    decodeLprog (encodeLfundefBytes body) = some p := by
  simp only [decodableLcmd, Bool.and_eq_true, List.isEmpty_iff, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hsh, hsaves⟩, hF0⟩, hF⟩, hF'⟩, hbr⟩ := h
  rw [← hp]
  exact decodeLprog_encodeLfundefBytes_gen body hsh hsaves (Int.ofNat_ne_zero.mpr hF0) hF hF'
    (branchOK_of_branchOKL _ _ _ hbr (by rw [← fundefItems, ← fundefLayout, hp]; rfl))

/-- The bytes of the gated encoder of a decodable body decode to the program `p` its item
    list denotes. -/
theorem decodeLprog_of_encodeChecked {body : Lcmd} {bytes : List (BitVec 8)} {p : List RInstr}
    (he : encodeLfundefBytesChecked body = some bytes) (h : decodableLcmd body = true)
    (hp : fundefLayout body = some p) :
    decodeLprog bytes = some p := by
  rw [encodeLfundefBytesChecked_eq he]
  exact decodeLprog_encodeLfundefBytes h hp

/-- The body is decodable and `p` is its decoded program `fundefLayout body`. -/
def decodesToB (body : Lcmd) (p : List RInstr) : Bool :=
  decodableLcmd body && decide (fundefLayout body = some p)

/-- Bytes of the gated encoder at a body that `decodesToB` accepts at `p` decode to `p`. -/
theorem decodeLprog_of_decodesToB {body : Lcmd} {bytes : List (BitVec 8)} {p : List RInstr}
    (he : encodeLfundefBytesChecked body = some bytes) (h : decodesToB body p = true) :
    decodeLprog bytes = some p := by
  simp only [decodesToB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact decodeLprog_of_encodeChecked he h.1 h.2

/-! ## Calls of a named symbol -/

/-- **A call of a named symbol has the shape `callSym`**, whatever its label. -/
theorem shapeOf_callSym (P : Params) (ra : Option String) {f : String} (hf : f ≠ "")
    (l : LLabel) : shapeOf P (.Lcall ra (f, l)) = some (.one (.callSym l)) := by
  simp [shapeOf, String.isEmpty_iff, hf]

/-- The target label of an item of an instruction with a computed shape is the label of a
    conditional branch or of a call to a label of the body. -/
theorem target_dItems {P : Params} {i : Linstr} {sh : DShape}
    (hs : shapeOf P i.li_i = some sh) (off : Nat) {it : Item} (hit : it ∈ dItems P off i sh)
    {l : LLabel} (ht : it.target = some l) :
    (∃ cc, i.li_i = .Lcond (.reg cc) l) ∨ ∃ ra, i.li_i = .Lcall ra ("", l) := by
  cases sh with
  | ops pcs =>
    simp only [dItems, List.mem_map] at hit
    obtain ⟨p, -, rfl⟩ := hit
    cases ht
  | one s =>
    simp only [dItems, List.mem_singleton] at hit
    subst hit
    simp only at ht
    obtain ⟨ii, li⟩ := i
    simp only at hs ⊢
    cases li with
    | Lopn ds o ss =>
      rcases shapeOfBytes_ok hs with ⟨q, he, -⟩ | ⟨pcs, he, -⟩
      · cases he
        cases ht
      · cases he
    | Lcond c l' =>
      cases c with
      | reg cc =>
        simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at hs
        subst hs
        simp only [Shape.target, Option.some.injEq] at ht
        exact Or.inl ⟨cc, by rw [ht]⟩
      | _ => simp [shapeOf] at hs
    | Lcall ra t =>
      obtain ⟨f, l'⟩ := t
      simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at hs
      subst hs
      split at ht
      · rename_i hf
        simp only [Shape.target, Option.some.injEq] at ht
        rw [String.isEmpty_iff] at hf
        exact Or.inr ⟨ra, by rw [hf, ht]⟩
      · simp [Shape.target] at ht
    | Llabel k l' =>
      simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at hs
      subst hs; cases ht
    | Lret =>
      simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at hs
      subst hs; cases ht
    | Lalign =>
      simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at hs
      subst hs; cases ht
    | _ => simp [shapeOf] at hs

theorem target_itemsFromL (P : Params) :
    ∀ (b : Lcmd) (shs : List DShape) (off : Nat), shapesOf P b = some shs →
      ∀ it ∈ itemsFromL P off b shs, ∀ l, it.target = some l →
        ∃ i ∈ b, (∃ cc, i.li_i = .Lcond (.reg cc) l) ∨ ∃ ra, i.li_i = .Lcall ra ("", l) := by
  intro b
  induction b with
  | nil => intro shs off _ it hit; cases shs <;> cases hit
  | cons i b ih =>
    intro shs off hs it hit l ht
    simp only [shapesOf] at hs
    split at hs
    · rename_i sh s' h1 h2
      simp only [Option.some.injEq] at hs
      subst hs
      simp only [itemsFromL, List.mem_append] at hit
      rcases hit with hit | hit
      · exact ⟨i, List.mem_cons_self, target_dItems h1 off hit ht⟩
      · obtain ⟨j, hj, hr⟩ := ih s' _ h2 it hit l ht
        exact ⟨j, List.mem_cons_of_mem _ hj, hr⟩
    · cases hs

/-- **The labels the branch check reads.** On the item list of a body with computed shapes,
    every target label is the label of a conditional branch or of a call to a label of the
    body. The label of a call of a named symbol is read by no conjunct of `branchOKL`, so a
    calling body passes `decodableLcmd` whether or not it defines that label. -/
theorem target_fundefItems {body : Lcmd} {shs : List DShape}
    (hs : shapesOf (Params.ofBody body) body = some shs) :
    ∀ it ∈ fundefItemsL body shs, ∀ l, it.target = some l →
      ∃ i ∈ body, (∃ cc, i.li_i = .Lcond (.reg cc) l) ∨ ∃ ra, i.li_i = .Lcall ra ("", l) := by
  intro it hit l ht
  simp only [fundefItemsL, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hit
  rcases hit with rfl | hit | rfl | rfl
  · cases ht
  · exact target_itemsFromL _ body shs 0 hs it hit l ht
  · cases ht
  · cases ht

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
