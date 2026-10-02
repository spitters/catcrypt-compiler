/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun

@[expose] public section

set_option autoImplicit false

/-!
# The name-keyed image of a physical body

A printed physical body reaches a word array through a pointer: the pointer of the array is
kept in a frame slot, reloaded into a register, and the indexed access `(%b, %idx, 8)` reads
or writes the memory word at `b + 8 · idx`. The address machine `JasminLsemAddrRun.runA`
runs such a body. The name-keyed machine `lsemFuelMemF` keys its arrays by name; on the
physical body it would read the array named by the base register, a name that stands for a
different array at each reload.

The image of a physical body is the body with every indexed access rewritten to the
name-keyed access of the array whose pointer its base register holds, at the length of that
array. The array of an access is read off the last reload `MOVQ b, q` (or `MOV:64 b, q`) of
the base register `b` from the frame slot `q` in front of it (`reloadOf`), past moves into
names other than `b` and the array slots and past instructions writing neither `b` nor an
array slot, following copies between general-purpose names back to their reload, with
`slotArr q` the array whose pointer `q` holds. Every other instruction is kept, at the
tag of the address machine (`tagAt`: the one-bit tag for a carry constant, the register tag
otherwise), with the widening multiply read at its width (`normA`). The image has the
length and the program counters of the body without its final return.

## The class

`physImgB slotArr body` is decided on the body: every indexed access at scale `8` follows a
reload of its base register from the slot of an array, and every write to the slot of an
array is a save `MOVQ qsave.R, R` of the register `R` that the slot name names, preceded only
by moves (`slotMov?`) none of which writes `R`, so `R` still holds its entry value.

## Main results

* `slotOfReg`, `reloadOf`, `accArr`, `imgInstr`, `virtImg`: the array of an access and the
  image.
* `isSaveB`, `entryRegB`, `slotWriteB`, `accOkB`, `physImgB`: the class.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun

/-! ## 1. The image -/

/-- The frame slot `qsave.R` of the register `R`. -/
def slotOfReg (R : String) : String := "qsave." ++ R

/-- A general-purpose name of a printed body other than the stack register: the names of
    `X86Backend.DecodePrinted.gpOk`. A copy between two such names carries a pointer from
    register to register. -/
def gpNameB (r : String) : Bool :=
  ["RAX", "RCX", "RDX", "RBX", "RBP", "RSI", "RDI", "R8", "R9", "R10", "R11", "R12", "R13",
    "R14", "R15"].contains r

/-- The destination operand `x` names `b` or the slot of an array. -/
def dstHitB (slotArr : String → Option (String × Nat)) (b : String) (x : LOperand) : Bool :=
  match x with
  | .reg q => q == b || (slotArr q).isSome
  | .arrIdx q i _ => q == b || i == b || (slotArr q).isSome || (slotArr i).isSome
  | _ => false

/-- The frame slot whose word the register `b` holds before instruction `k` of `body`,
    scanning back from instruction `k - 1`: past a move (`slotMov?`) into a name other than
    `b` and the array slots, and past any other `Lopn` none of whose destinations is `b` or
    an array slot; at a move of `q` into `b`, the slot `q`, or, for a general-purpose `q`
    that is not an array slot, the frame slot whose word `q` holds before that move. The
    result is `none` when the scan meets an `Lopn` writing `b` or an array slot, a move into
    an array slot, an instruction other than an `Lopn`, or the start of the body. -/
def reloadOf (slotArr : String → Option (String × Nat)) (body : Lcmd) : Nat → String →
    Option String
  | 0, _ => none
  | k + 1, b =>
      match body[k]? with
      | some j =>
          match slotMov? j.li_i with
          | some (d, q) =>
              if d = b then
                (if (slotArr q).isNone && gpNameB q then reloadOf slotArr body k q else some q)
              else if (slotArr d).isNone then reloadOf slotArr body k b else none
          | none =>
              match j.li_i with
              | .Lopn ds _ _ =>
                  if ds.any (dstHitB slotArr b) then none else reloadOf slotArr body k b
              | _ => none
      | none => none

theorem reloadOf_zero (slotArr : String → Option (String × Nat)) (body : Lcmd) (b : String) :
    reloadOf slotArr body 0 b = none := rfl

theorem reloadOf_succ_some {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {j : Linstr} {d q : String} (hb : body[k]? = some j) (hm : slotMov? j.li_i = some (d, q))
    (b : String) :
    reloadOf slotArr body (k + 1) b =
      if d = b then
        (if (slotArr q).isNone && gpNameB q then reloadOf slotArr body k q else some q)
      else if (slotArr d).isNone then reloadOf slotArr body k b else none := by
  simp [reloadOf, hb, hm]

theorem reloadOf_succ_lopn {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {j : Linstr} (hb : body[k]? = some j) (hm : slotMov? j.li_i = none)
    {ds : List LOperand} {o : String} {ss : List LOperand} (hx : j.li_i = .Lopn ds o ss)
    (b : String) :
    reloadOf slotArr body (k + 1) b =
      if ds.any (dstHitB slotArr b) then none else reloadOf slotArr body k b := by
  rw [hx] at hm
  simp only [reloadOf, hb, hx, hm]

theorem reloadOf_succ_other {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {j : Linstr} (hb : body[k]? = some j) (hm : slotMov? j.li_i = none)
    (hx : ∀ ds o ss, j.li_i ≠ .Lopn ds o ss) (b : String) :
    reloadOf slotArr body (k + 1) b = none := by
  cases hj : j.li_i with
  | Lopn ds o ss => exact absurd hj (hx ds o ss)
  | _ => rw [hj] at hm; simp only [reloadOf, hb, hj, hm]

/-- The scan of `reloadOf` past a non-move `Lopn` writing neither `b` nor an array slot. -/
theorem reloadOf_succ_none_eq {slotArr : String → Option (String × Nat)} {body : Lcmd}
    {k : Nat} {j : Linstr} (hb : body[k]? = some j) (hm : slotMov? j.li_i = none) (b : String)
    {q : String} (h : reloadOf slotArr body (k + 1) b = some q) :
    ∃ ds o ss, j.li_i = .Lopn ds o ss ∧ ds.any (dstHitB slotArr b) = false
      ∧ reloadOf slotArr body k b = some q := by
  cases hx : j.li_i with
  | Lopn ds o ss =>
      rw [reloadOf_succ_lopn hb hm hx] at h
      split_ifs at h with hd
      exact ⟨ds, o, ss, rfl, Bool.eq_false_iff.mpr hd, h⟩
  | _ => rw [reloadOf_succ_other hb hm (by intro ds o ss he; rw [hx] at he; cases he)] at h; cases h

/-- The instruction that `reloadOf` finds: a move of `q` into a name before instruction
    `k`. -/
theorem reloadOf_spec {slotArr : String → Option (String × Nat)} {body : Lcmd} :
    ∀ {k : Nat} {b q : String}, reloadOf slotArr body k b = some q →
      ∃ j i b', j < k ∧ body[j]? = some i ∧ slotMov? i.li_i = some (b', q)
  | 0, _, _, h => by cases h
  | k + 1, b, q, h => by
      cases hb : body[k]? with
      | none => simp [reloadOf, hb] at h
      | some i =>
          cases hm : slotMov? i.li_i with
          | none =>
              obtain ⟨-, -, -, -, -, h'⟩ := reloadOf_succ_none_eq hb hm b h
              obtain ⟨j, i', b', hj, hi', hm'⟩ := reloadOf_spec h'
              exact ⟨j, i', b', Nat.lt_succ_of_lt hj, hi', hm'⟩
          | some p =>
              obtain ⟨d, q'⟩ := p
              rw [reloadOf_succ_some hb hm] at h
              split_ifs at h with h1 h2 h3
              · obtain ⟨j, i', b', hj, hi', hm'⟩ := reloadOf_spec h
                exact ⟨j, i', b', Nat.lt_succ_of_lt hj, hi', hm'⟩
              · cases h
                exact ⟨k, i, d, Nat.lt_succ_self k, hb, hm⟩
              · obtain ⟨j, i', b', hj, hi', hm'⟩ := reloadOf_spec h
                exact ⟨j, i', b', Nat.lt_succ_of_lt hj, hi', hm'⟩

/-- The array, with its length, whose pointer the register `b` holds at instruction `k` of
    `body`: the array of the slot `q` from which `b` was last reloaded (`reloadOf`). -/
def accArr (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) (b : String) :
    Option (String × Nat) :=
  (reloadOf slotArr body k b).bind slotArr

/-- The image of instruction `k` of `body`: an indexed load or store at scale `8` through a
    register that holds the pointer of the array `A` of length `n` is the name-keyed load or
    store on `A` at the shape `(64, n)`; every other instruction is `normA` of it at the
    tag `tagAt` of its position. -/
def imgInstr (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : LinstrR) : LinstrRM :=
  match i with
  | .Lopn [.reg d] o [.arrIdx b idx 8] =>
      if o = "LOADIDX" then
        match accArr slotArr body k b with
        | some (A, n) => (.Lopn [.reg d] "LOADIDX" [.arrIdx A idx 8], .load 64 n)
        | none => (normA i, .reg none)
      else (normA i, .reg none)
  | .Lopn [.reg _] o [.arrIdx b idx 8, .reg v] =>
      if o = "STOREIDX" then
        match accArr slotArr body k b with
        | some (A, n) => (.Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v], .store 64 n)
        | none => (normA i, .reg none)
      else (normA i, .reg none)
  | _ => (normA i, tagAt body k i)

/-- **The image of a physical body**: `imgInstr` at each instruction of the body without its
    final instruction (the return of a printed body). -/
def virtImg (slotArr : String → Option (String × Nat)) (body : Lcmd) : List LinstrRM :=
  body.dropLast.mapIdx fun k i => imgInstr slotArr body k i.li_i

theorem virtImg_length (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    (virtImg slotArr body).length = body.length - 1 := by
  simp [virtImg]

theorem virtImg_getElem? (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) :
    (virtImg slotArr body)[k]? = (body.dropLast[k]?).map fun i => imgInstr slotArr body k i.li_i
    := by
  simp [virtImg, List.getElem?_mapIdx]

/-! ## 2. The class -/

/-- The instruction is the save `MOVQ qsave.R, R` of a register into its slot. -/
def isSaveB (i : LinstrR) : Bool :=
  match slotMov? i with
  | some (q, R) => q == slotOfReg R
  | none => false

/-- The register `R` holds its entry value at instruction `k`: every instruction before `k`
    is a move (`slotMov?`) whose destination is not `R`. -/
def entryRegB (body : Lcmd) (k : Nat) (R : String) : Bool :=
  (body.take k).all fun j =>
    match slotMov? j.li_i with
    | some (d, _) => d != R
    | none => false

/-- The instruction writes the slot of an array only as a save of a register at its entry
    value: an `Lopn` with a destination naming an array slot is a save `MOVQ qsave.R, R` with
    `entryRegB` at its position. -/
def slotWriteB (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : LinstrR) : Bool :=
  match i with
  | .Lopn ds _ _ =>
      ds.all fun
        | .reg q => (slotArr q).isNone ||
            (match slotMov? i with
              | some (q', R) => q' == slotOfReg R && entryRegB body k R
              | none => false)
        | .arr q _ => (slotArr q).isNone
        | .arrIdx q _ _ => (slotArr q).isNone
        | .imm _ => true
  | _ => true

/-- An indexed access of the body resolves to an array: an `LOADIDX` or `STOREIDX` is at
    scale `8` and its base register holds the pointer of an array (`accArr`). -/
def accOkB (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : LinstrR) : Bool :=
  match i with
  | .Lopn _ o srcs =>
      if o = "LOADIDX" then
        match i with
        | .Lopn [.reg _] _ [.arrIdx b _ 8] => (accArr slotArr body k b).isSome
        | _ => false
      else if o = "STOREIDX" then
        match srcs with
        | [.arrIdx b _ 8, .reg _] =>
            (match i with | .Lopn [.reg _] _ _ => true | _ => false)
              && (accArr slotArr body k b).isSome
        | _ => false
      else true
  | _ => true

/-- **The class of the image**: every indexed access resolves to an array (`accOkB`) and
    every write to an array slot is a save of a register at its entry value (`slotWriteB`). -/
def physImgB (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  (List.range body.length).all fun k =>
    match body[k]? with
    | some i => accOkB slotArr body k i.li_i && slotWriteB slotArr body k i.li_i
    | none => true

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
