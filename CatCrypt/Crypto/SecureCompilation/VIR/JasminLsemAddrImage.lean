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
* `cellIdxStore?`, `cellIdxStore?_spec`, `imgInstr_cellIdxStore`: the indexed store through
  a cell `mem.D.0` whose base `D` is the address `LEA:64 D, (B, X, 8)` of a word of an array,
  and its image, the name-keyed store at the frame slot from which `X` was reloaded.
* `arrImmImg`, `imgInstr_zeroArr`, `imgInstr_storeImm`: the image of an array zeroing
  `ZEROARR` and of a constant-index store `STOREIMM` through the pointer of an array.
* `isSaveB`, `entryRegB`, `slotWriteB`, `accOkB`, `physImgB`: the class.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (untagCaret
  untagCaret_of_caret_free)

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

/-- The scan `reloadOf` over a body held as an array, indexed in constant time. -/
def reloadOfA (slotArr : String → Option (String × Nat)) (body : Array Linstr) : Nat → String →
    Option String
  | 0, _ => none
  | k + 1, b =>
      match body[k]? with
      | some j =>
          match slotMov? j.li_i with
          | some (d, q) =>
              if d = b then
                (if (slotArr q).isNone && gpNameB q then reloadOfA slotArr body k q else some q)
              else if (slotArr d).isNone then reloadOfA slotArr body k b else none
          | none =>
              match j.li_i with
              | .Lopn ds _ _ =>
                  if ds.any (dstHitB slotArr b) then none else reloadOfA slotArr body k b
              | _ => none
      | none => none

/-- The array scan at the array of a body is the list scan. -/
theorem reloadOfA_toArray (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    ∀ (k : Nat) (b : String), reloadOfA slotArr body.toArray k b = reloadOf slotArr body k b
  | 0, _ => rfl
  | k + 1, b => by
      simp only [reloadOfA, reloadOf, List.getElem?_toArray, reloadOfA_toArray slotArr body k]

/-- `reloadOf` evaluated on the array of the body. -/
def reloadOfImpl (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (b : String) : Option String :=
  reloadOfA slotArr body.toArray k b

/-- The scan `reloadOf` is evaluated as `reloadOfImpl`. -/
@[csimp] theorem reloadOf_eq_impl : @reloadOf = @reloadOfImpl := by
  funext slotArr body k b
  exact (reloadOfA_toArray slotArr body k b).symm

/-- The array, with its length, whose pointer the register `b` holds at instruction `k` of
    `body`: the array of the slot `q` from which `b` was last reloaded (`reloadOf`). -/
def accArr (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) (b : String) :
    Option (String × Nat) :=
  (reloadOf slotArr body k b).bind slotArr

/-- `accArr` over a body held as an array. -/
def accArrA (slotArr : String → Option (String × Nat)) (body : Array Linstr) (k : Nat)
    (b : String) : Option (String × Nat) :=
  (reloadOfA slotArr body k b).bind slotArr

/-- `accArrA` at the array of a body is `accArr`. -/
theorem accArrA_toArray (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (b : String) : accArrA slotArr body.toArray k b = accArr slotArr body k b := by
  simp only [accArrA, accArr, reloadOfA_toArray]

/-- The instruction at position `k` of `body` is a stored carry constant: a 64-bit immediate
    move `MOV:64 d, #n` with `n < 2` into a name `d` that is neither a cell name nor a
    general-purpose name, whose next use is a carry-in (`carryInNext`); as `(d, n)`. The
    machine stores the word `n`, whose low bit, the bit a carry-in reads of a frame word
    (`JasminLsemAddrMem.bitA`), is `n`. -/
def bitStore? (body : Lcmd) (k : Nat) : LinstrR → Option (String × Nat)
  | .Lopn [.reg d] o [.imm n] =>
      if o = "MOV:64" ∧ n < 2 ∧ hasPrefix d "mem." = false ∧ gpNameB d = false
          ∧ carryInNext body k d = true then some (d, n)
      else none
  | _ => none

/-- The instruction at position `k` of `body` is a stored carry constant (`bitStore?`). -/
def bitStoreB (body : Lcmd) (k : Nat) (i : LinstrR) : Bool := (bitStore? body k i).isSome

/-- A stored carry constant is the move `MOV:64 d, #n` of `0` or `1` into a name that is
    neither a cell name nor a general-purpose name, whose next use is a carry-in. -/
theorem bitStore?_spec {body : Lcmd} {k : Nat} {i : LinstrR} {d : String} {n : Nat}
    (h : bitStore? body k i = some (d, n)) :
    i = .Lopn [.reg d] "MOV:64" [.imm n] ∧ n < 2 ∧ hasPrefix d "mem." = false
      ∧ gpNameB d = false ∧ carryInNext body k d = true := by
  unfold bitStore? at h
  split at h
  · split_ifs at h with hc
    cases h
    obtain ⟨rfl, h1, h2, h3, h4⟩ := hc
    exact ⟨rfl, h1, h2, h3, h4⟩
  · cases h

/-- An instruction other than a 64-bit immediate move is no stored carry constant. -/
theorem bitStore?_of_ne {body : Lcmd} {k : Nat} {i : LinstrR}
    (h : ∀ d n, i ≠ .Lopn [.reg d] "MOV:64" [.imm n]) : bitStore? body k i = none := by
  cases hb : bitStore? body k i with
  | none => rfl
  | some p => exact absurd (bitStore?_spec hb).1 (h p.1 p.2)

theorem bitStoreB_eq_false {body : Lcmd} {k : Nat} {i : LinstrR}
    (h : bitStore? body k i = none) : bitStoreB body k i = false := by
  simp [bitStoreB, h]

theorem bitStore?_of_bitStoreB {body : Lcmd} {k : Nat} {i : LinstrR}
    (h : bitStoreB body k i = false) : bitStore? body k i = none := by
  simpa [bitStoreB] using h

/-- The instruction at position `k` of `body` is an indexed store through a cell: the store
    `MOV:64 mem.D.0, v` of a register `v` other than `D`, whose base `D` is written two
    instructions before by `LEA:64 D, (B, X, 8)` with `B` the pointer of the array `A` of
    length `n` (`accArr` at the address), whose index register `X` is reloaded three
    instructions before from the frame slot `q` by a move (`slotMov?`), `q` a name that is
    neither a general-purpose name nor an array slot nor `D`, and whose instruction in
    between is a move (`slotMov?`) into a name other than `D` and `q`; as `(A, n, q, v)`. The
    store writes `v` at the word `8 · q` of `A`. -/
def cellIdxStore? (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) :
    LinstrR → Option (String × Nat × String × String)
  | .Lopn [.reg c] o [.reg v] =>
      match cellParts? c, body[k - 2]?, body[k - 3]?, body[k - 1]? with
      | some (D, off), some l, some r, some m =>
          match l.li_i, slotMov? r.li_i, slotMov? m.li_i with
          | .Lopn [.reg D'] o' [.arrIdx B X 8], some (X', q), some (d1, _) =>
              if o = "MOV:64" ∧ 3 ≤ k ∧ off = 0 ∧ v ≠ D ∧ o' = "LEA:64" ∧ D' = D ∧ X' = X
                  ∧ d1 ≠ D ∧ d1 ≠ q ∧ D ≠ q ∧ gpNameB q = false ∧ (slotArr q).isNone = true then
                (accArr slotArr body (k - 2) B).map fun p => (p.1, p.2, q, v)
              else none
          | _, _, _ => none
      | _, _, _, _ => none
  | _ => none

/-- Off the shape `MOV:64 c, v` between names the instruction is no indexed store through a
    cell. -/
theorem cellIdxStore?_of_ne (slotArr : String → Option (String × Nat)) {body : Lcmd}
    {k : Nat} {i : LinstrR} (h : ∀ c v, i ≠ .Lopn [.reg c] "MOV:64" [.reg v]) :
    cellIdxStore? slotArr body k i = none := by
  unfold cellIdxStore?
  split
  · rename_i c o v
    split
    · split
      · split_ifs with hc
        · exact absurd (by rw [hc.1]) (h c v)
        · rfl
      · rfl
    · rfl
  · rfl

/-- **The indexed store through a cell** (`cellIdxStore?`): the store `MOV:64 c, v` with `c`
    the cell `mem.D.0`, the address `LEA:64 D, (B, X, 8)` at `k - 2` with `B` the pointer of
    `A`, the reload of `X` from `q` at `k - 3` and the move into `d1` at `k - 1`. -/
theorem cellIdxStore?_spec {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : LinstrR} {A q v : String} {n : Nat}
    (h : cellIdxStore? slotArr body k i = some (A, n, q, v)) :
    ∃ c D B X d1 s l r m, i = .Lopn [.reg c] "MOV:64" [.reg v] ∧ cellParts? c = some (D, 0)
      ∧ 3 ≤ k ∧ v ≠ D
      ∧ body[k - 2]? = some l ∧ l.li_i = .Lopn [.reg D] "LEA:64" [.arrIdx B X 8]
      ∧ body[k - 3]? = some r ∧ slotMov? r.li_i = some (X, q)
      ∧ body[k - 1]? = some m ∧ slotMov? m.li_i = some (d1, s)
      ∧ d1 ≠ D ∧ d1 ≠ q ∧ D ≠ q ∧ gpNameB q = false ∧ slotArr q = none
      ∧ accArr slotArr body (k - 2) B = some (A, n) := by
  unfold cellIdxStore? at h
  split at h
  · rename_i c o v'
    split at h
    · rename_i D off l r m hc hl hr hm
      split at h
      · rename_i D' o' B X X' q' d1 s hli hr' hm'
        split_ifs at h with hcond
        obtain ⟨rfl, h3, rfl, hv, rfl, rfl, rfl, hd1, hd1q, hDq, hgp, hsl⟩ := hcond
        obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        exact ⟨c, _, B, _, d1, s, l, r, m, rfl, hc, h3, hv, hl, hli, hr, hr', hm, hm', hd1,
          hd1q, hDq, hgp, Option.isNone_iff_eq_none.mp hsl, hp⟩
      · cases h
    · cases h
  · cases h

/-- The image of an array zeroing or a constant-index store through a register `b` that holds
    the pointer of the array `A` of length `n` (`accArr`): the zeroing
    `ZEROARR [], [b, #n', #w']` is the name-keyed zeroing of `A` at the tag `.zero 64 n`, and
    the store `STOREIMM d, [b, v, #k]` is the name-keyed store `STOREIMM A, [A, v, #k]` at the
    tag `.storeImm 64 n`; `none` for every other instruction and for a base register without
    an array. The mnemonic is read through `untagCaret`, as `tagA` reads it. -/
def arrImmImg (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) :
    LinstrR → Option LinstrRM
  | .Lopn [] o [.reg b, .imm n', .imm w'] =>
      if untagCaret o = "ZEROARR" then
        match accArr slotArr body k b with
        | some (A, n) => some (.Lopn [.reg A] "ZEROARR" [.imm n', .imm w'], .zero 64 n)
        | none => none
      else none
  | .Lopn [.reg _] o [.reg b, .reg v, .imm j] =>
      if untagCaret o = "STOREIMM" then
        match accArr slotArr body k b with
        | some (A, n) => some (.Lopn [.reg A] "STOREIMM" [.reg A, .reg v, .imm j], .storeImm 64 n)
        | none => none
      else none
  | _ => none

/-- An instruction whose `untagCaret` is neither `ZEROARR` nor `STOREIMM` has no image by
    `arrImmImg`. -/
theorem arrImmImg_of_ne (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {ds : List LOperand} {o : String} {ss : List LOperand} (h1 : untagCaret o ≠ "ZEROARR")
    (h2 : untagCaret o ≠ "STOREIMM") : arrImmImg slotArr body k (.Lopn ds o ss) = none := by
  grind only [= arrImmImg.eq_def]

/-- `arrImmImg_of_ne` at a mnemonic without `^`. -/
theorem arrImmImg_of_ne_of_caret_free (slotArr : String → Option (String × Nat)) (body : Lcmd)
    (k : Nat) {ds : List LOperand} {o : String} {ss : List LOperand} (h1 : o ≠ "ZEROARR")
    (h2 : o ≠ "STOREIMM") (hc : '^' ∉ o.toList := by decide) :
    arrImmImg slotArr body k (.Lopn ds o ss) = none :=
  arrImmImg_of_ne slotArr body k (by rwa [untagCaret_of_caret_free hc])
    (by rwa [untagCaret_of_caret_free hc])

/-- `arrImmImg` reads the body only through the array scan of the base register of the
    instruction. -/
theorem arrImmImg_isSome_mono {slotArr : String → Option (String × Nat)} {b1 b2 : Lcmd}
    {k1 k2 : Nat} {i : LinstrR}
    (hmono : ∀ x, (∃ ds o ss, i = .Lopn ds o (.reg x :: ss)) →
      (accArr slotArr b1 k1 x).isSome = true → (accArr slotArr b2 k2 x).isSome = true)
    (h : (arrImmImg slotArr b1 k1 i).isSome = true) :
    (arrImmImg slotArr b2 k2 i).isSome = true := by
  grind only [= arrImmImg.eq_def, = Option.isSome_some, = Option.isSome_none]

/-- An image by `arrImmImg` is an `Lopn`. -/
theorem arrImmImg_lopn {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : LinstrR} {r : LinstrRM} (h : arrImmImg slotArr body k i = some r) :
    ∃ ds o ss, r.1 = .Lopn ds o ss := by
  grind only [= arrImmImg.eq_def]

/-- **The reload of the base of an address computation**: the instruction at position `k` of
    `body` is a move `MOVQ b, q` or `MOV:64 b, q` from a name `q` that holds an array pointer
    (`slotArr q` is defined), and the instruction at `k + 2` is `LEA:64 D, (b, X, 8)`; as
    `(b, q)`. Such a move is the source of the width guard on `q` that the address
    computation reads. -/
def baseReload? (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) :
    LinstrR → Option (String × String)
  | .Lopn [.reg b] o [.reg q] =>
      match body[k + 2]? with
      | some l =>
          match l.li_i with
          | .Lopn [.reg _] o' [.arrIdx B _ 8] =>
              if (o = "MOVQ" ∨ o = "MOV:64") ∧ o' = "LEA:64" ∧ B = b ∧ (slotArr q).isSome = true
              then some (b, q) else none
          | _ => none
      | none => none
  | _ => none

/-- Off the shape of a move between names the instruction is no reload of a base. -/
theorem baseReload?_of_ne (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {i : LinstrR} (h : ∀ b o q, i ≠ .Lopn [.reg b] o [.reg q]) :
    baseReload? slotArr body k i = none := by
  grind only [= baseReload?.eq_def]

/-- A reload of a base is a move from a name that holds an array pointer. -/
theorem baseReload?_spec {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {i : LinstrR} {b q : String} (h : baseReload? slotArr body k i = some (b, q)) :
    (i = .Lopn [.reg b] "MOVQ" [.reg q] ∨ i = .Lopn [.reg b] "MOV:64" [.reg q])
      ∧ (slotArr q).isSome = true := by
  unfold baseReload? at h
  grind

/-- A move from a name that holds no array pointer is no reload of a base. -/
theorem baseReload?_of_slot_none (slotArr : String → Option (String × Nat)) (body : Lcmd)
    (k : Nat) {b o q : String} (h : slotArr q = none) :
    baseReload? slotArr body k (.Lopn [.reg b] o [.reg q]) = none := by
  cases hr : baseReload? slotArr body k (.Lopn [.reg b] o [.reg q]) with
  | none => rfl
  | some p =>
      obtain ⟨b', q'⟩ := p
      have ⟨h1, h2⟩ := baseReload?_spec hr
      grind

/-- The image of instruction `k` of `body`: an indexed load or store at scale `8` through a
    register that holds the pointer of the array `A` of length `n` is the name-keyed load or
    store on `A` at the shape `(64, n)`; a stored carry constant `MOV:64 d, #n` (`bitStore?`)
    is the untagged move `MOV d, #n` at the one-bit tag `.reg (some 1)`, the write of the bit
    `n`; an indexed store through a cell (`cellIdxStore?`) of `v` at the word `8 · q` of the
    array `A` of length `n` is the name-keyed store `STOREIDX A[q] := v` at the shape
    `(64, n)`; an array zeroing or a constant-index store through the pointer of an array is
    its image by `arrImmImg`; the reload of the base of an address computation
    (`baseReload?`) is the cast `CASTW_64_64 b, q` at the tag `.reg (some 64)`, which reads the
    word of `q` as a word of width `64`, so the address computation has no width guard on a
    name that only the image holds; every other instruction is `normA` of it at the tag
    `tagAt` of its position. The mnemonic of an indexed access is read through `untagCaret`. -/
def imgInstr (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : LinstrR) : LinstrRM :=
  match i with
  | .Lopn [.reg d] o [.arrIdx b idx 8] =>
      if untagCaret o = "LOADIDX" then
        match accArr slotArr body k b with
        | some (A, n) => (.Lopn [.reg d] "LOADIDX" [.arrIdx A idx 8], .load 64 n)
        | none => (normA i, .reg none)
      else (normA i, .reg none)
  | .Lopn [.reg _] o [.arrIdx b idx 8, .reg v] =>
      if untagCaret o = "STOREIDX" then
        match accArr slotArr body k b with
        | some (A, n) => (.Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v], .store 64 n)
        | none => (normA i, .reg none)
      else (normA i, .reg none)
  | _ =>
      match bitStore? body k i with
      | some (d, n) => (.Lopn [.reg d] "MOV" [.imm n], .reg (some 1))
      | none =>
          match cellIdxStore? slotArr body k i with
          | some (A, n, q, v) => (.Lopn [.reg A] "STOREIDX" [.arrIdx A q 8, .reg v], .store 64 n)
          | none =>
              match arrImmImg slotArr body k i with
              | some r => r
              | none =>
                  match baseReload? slotArr body k i with
                  | some (b, q) => (.Lopn [.reg b] "CASTW_64_64" [.reg q], .reg (some 64))
                  | none => (normA i, tagAt body k i)

/-- The image of a reload of the base of an address computation is the cast of the word. -/
theorem imgInstr_baseReload (slotArr : String → Option (String × Nat)) {body : Lcmd} {k : Nat}
    {i : LinstrR} {b q : String} (h : baseReload? slotArr body k i = some (b, q))
    (h1 : bitStore? body k i = none) (h2 : cellIdxStore? slotArr body k i = none)
    (h3 : arrImmImg slotArr body k i = none) :
    imgInstr slotArr body k i = (.Lopn [.reg b] "CASTW_64_64" [.reg q], .reg (some 64)) := by
  obtain ⟨hi, -⟩ := baseReload?_spec h
  rcases hi with rfl | rfl <;> simp only [imgInstr, h1, h2, h3, h]

/-- The image of a stored carry constant `MOV:64 d, #n` is the one-bit move `MOV d, #n`. -/
theorem imgInstr_bitStore (slotArr : String → Option (String × Nat)) {body : Lcmd} {k : Nat}
    {i : LinstrR} {d : String} {n : Nat} (h : bitStore? body k i = some (d, n)) :
    imgInstr slotArr body k i = (.Lopn [.reg d] "MOV" [.imm n], .reg (some 1)) := by
  obtain ⟨rfl, -⟩ := bitStore?_spec h
  simp only [imgInstr, h]

/-- The image of an indexed store through a cell (`cellIdxStore?`) of `v` at the word `8 · q`
    of the array `A` of length `n` is the name-keyed store `STOREIDX A[q] := v`. -/
theorem imgInstr_cellIdxStore (slotArr : String → Option (String × Nat)) {body : Lcmd}
    {k : Nat} {i : LinstrR} {A q v : String} {n : Nat}
    (h : cellIdxStore? slotArr body k i = some (A, n, q, v)) :
    imgInstr slotArr body k i = (.Lopn [.reg A] "STOREIDX" [.arrIdx A q 8, .reg v], .store 64 n)
    := by
  obtain ⟨c, -, -, -, -, -, -, -, -, rfl, -⟩ := cellIdxStore?_spec h
  have hb : bitStore? body k (.Lopn [.reg c] "MOV:64" [.reg v]) = none :=
    bitStore?_of_ne (by simp)
  simp only [imgInstr, hb, h]

/-- The image of the array zeroing `ZEROARR [], [b, #n', #w']` through a register `b` that
    holds the pointer of the array `A` of length `n` is the zeroing of `A` at `.zero 64 n`. -/
theorem imgInstr_zeroArr (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {b A : String} {n' w' n : Nat} (h : accArr slotArr body k b = some (A, n)) :
    imgInstr slotArr body k (.Lopn [] "ZEROARR" [.reg b, .imm n', .imm w'])
      = (.Lopn [.reg A] "ZEROARR" [.imm n', .imm w'], .zero 64 n) := by
  simp [imgInstr, bitStore?, cellIdxStore?, arrImmImg, h, width_tag]

/-- The image of the constant-index store `STOREIMM d, [b, v, #j]` through a register `b` that
    holds the pointer of the array `A` of length `n` is the store `STOREIMM A, [A, v, #j]` at
    `.storeImm 64 n`. -/
theorem imgInstr_storeImm (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {d b v A : String} {j n : Nat} (h : accArr slotArr body k b = some (A, n)) :
    imgInstr slotArr body k (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm j])
      = (.Lopn [.reg A] "STOREIMM" [.reg A, .reg v, .imm j], .storeImm 64 n) := by
  simp [imgInstr, bitStore?, cellIdxStore?, arrImmImg, h, width_tag]

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
    scale `8` and its base register holds the pointer of an array (`accArr`), and a `ZEROARR`
    or `STOREIMM` has an image by `arrImmImg` (its form, with a base register that holds the
    pointer of an array). The mnemonic is read through `untagCaret`. -/
def accOkB (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : LinstrR) : Bool :=
  match i with
  | .Lopn _ o srcs =>
      if untagCaret o = "LOADIDX" then
        match i with
        | .Lopn [.reg _] _ [.arrIdx b _ 8] => (accArr slotArr body k b).isSome
        | _ => false
      else if untagCaret o = "STOREIDX" then
        match srcs with
        | [.arrIdx b _ 8, .reg _] =>
            (match i with | .Lopn [.reg _] _ _ => true | _ => false)
              && (accArr slotArr body k b).isSome
        | _ => false
      else if untagCaret o = "ZEROARR" ∨ untagCaret o = "STOREIMM" then
        (arrImmImg slotArr body k i).isSome
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
