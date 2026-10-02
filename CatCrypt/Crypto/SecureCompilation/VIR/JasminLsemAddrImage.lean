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
array. The array of an access is read off the instruction in front of it: a reload
`MOVQ b, q` (or `MOV:64 b, q`) of the base register `b` from the frame slot `q`, with
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

* `slotOfReg`, `accArr`, `imgInstr`, `virtImg`: the array of an access and the image.
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

/-- The array, with its length, whose pointer the register `b` holds at instruction `k` of
    `body`: the array of the slot `q` when instruction `k - 1` reloads `b` from `q`. -/
def accArr (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) (b : String) :
    Option (String × Nat) :=
  match k with
  | 0 => none
  | k + 1 =>
      match body[k]? with
      | some j =>
          match slotMov? j.li_i with
          | some (d, q) => if d = b then slotArr q else none
          | none => none
      | none => none

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
