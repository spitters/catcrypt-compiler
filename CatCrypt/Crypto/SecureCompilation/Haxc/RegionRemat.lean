/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
public import Std.Data.HashMap

/-!
# Rematerialization of constant array indices before allocation

The linear scan spills a register that holds a constant array index when its live range is
long, and the spilled index is reloaded from its frame slot at each access. The constant-index
fold forgets frame slots, so such an access stays register-indexed and its array keeps a shape
guard that the reference lacks. `rematIdxCode` places a copy of the immediate move of the index
into a fresh name directly before each indexed access, so the index of the access has a live
range of two instructions and its value stays known.

The pass runs on the code given to the allocation (`List LinstrRM`). It has no semantic
theorem: the validator of the allocated body checks the result.

## Main definitions

* `idxReg?`, `withIdxReg` — the index register of a `LOADIDX`/`STOREIDX` access, and the
  access with another index register.
* `rematTable`, `rematDef?` — the body registers `r<k>` written exactly once, by an immediate
  move, with that move.
* `rematIdxWith`, `rematIdxCode` — the code with a fresh copy of the move before each access
  whose index has such a definition.

## Main results

* `rematIdxCode_nil` — the empty code is unchanged.
* `rematIdxWith_eq_self`, `rematIdxCode_eq_self`, `rematIdxWith_none` — code in which no
  indexed access has a constant index is unchanged.
* `rematIdxWith_length_le`, `rematIdxCode_length_le` — the code at most doubles in length.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionRemat

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

/-- The index register `idx` of an indexed access: of a load
    `Lopn [.reg dst] "LOADIDX" [.arrIdx base idx s]` or of a store
    `Lopn [.reg dst] "STOREIDX" [.arrIdx base idx s, .reg val]`; `none` otherwise. -/
def idxReg? : LinstrR → Option String
  | .Lopn [.reg _] opn [.arrIdx _ idx _] => if opn = "LOADIDX" then some idx else none
  | .Lopn [.reg _] opn [.arrIdx _ idx _, .reg _] =>
      if opn = "STOREIDX" then some idx else none
  | _ => none

/-- The instruction with index register `y` in its leading `.arrIdx` source operand. -/
def withIdxReg (y : String) : LinstrR → LinstrR
  | .Lopn ds opn (.arrIdx b _ s :: rest) => .Lopn ds opn (.arrIdx b y s :: rest)
  | i => i

/-- A body register name `r<k>` (`regName k`). -/
def isBodyRegName (n : String) : Bool := n.startsWith "r" && (strDropToNat? n 1).isSome

/-- The destination `x` of an immediate move `Lopn [.reg x] opn [.imm c]` whose mnemonic is
    `MOV` up to its width tag (`stripWidthTag`); `none` otherwise. -/
def immMovDst? : LinstrR → Option String
  | .Lopn [.reg x] opn [.imm _] => if stripWidthTag opn = "MOV" then some x else none
  | _ => none

/-- The register names an instruction writes: the `.reg` destinations of an `Lopn`. -/
def regWrites : LinstrR → List String
  | .Lopn ds _ _ => ds.filterMap fun | .reg d => some d | _ => none
  | _ => []

/-- One step of `rematTable`: the write count of each register the instruction writes is
    incremented, and an immediate move is recorded as the definition of its destination. -/
def rematTableStep (m : Std.HashMap String (Nat × Option LinstrRM)) (i : LinstrRM) :
    Std.HashMap String (Nat × Option LinstrRM) :=
  let m := (regWrites i.1).foldl
    (fun m d => m.alter d fun
      | none => some (1, none)
      | some (n, e) => some (n + 1, e)) m
  match immMovDst? i.1 with
  | some x => m.modify x fun (n, _) => (n, some i)
  | none => m

/-- For each register written in `code`, the number of its writes and its last immediate
    move. -/
def rematTable (code : List LinstrRM) : Std.HashMap String (Nat × Option LinstrRM) :=
  code.foldl rematTableStep ∅

/-- The immediate move defining `x`, when `x` is a body register `r<k>` with exactly one write
    in the table's code and that write is an immediate move; `none` otherwise. -/
def rematDef? (tbl : Std.HashMap String (Nat × Option LinstrRM)) (x : String) :
    Option LinstrRM :=
  if isBodyRegName x then
    match tbl[x]? with
    | some (1, some i) => some i
    | _ => none
  else none

/-- The fresh register name of the copy placed before the instruction at position `n`. The
    prefix `#remat` is not produced by the export (body registers `r<k>`, arguments `a<j>`,
    pins `%livepin`, frame slots `k.N`/`kv.N`/`qsave.X`/`mem.*`, webs `D#c<j>`), and source
    identifiers do not begin with `#`, so the name occurs nowhere else in the code. -/
def rematName (n : Nat) : String := "#remat" ++ toString n

/-- The instruction with its single register destination replaced by `y`. -/
def renameDst (y : String) : LinstrRM → LinstrRM
  | (.Lopn [.reg _] opn srcs, t) => (.Lopn [.reg y] opn srcs, t)
  | i => i

/-- The image of the instruction `p.1` at position `p.2`: when it is an indexed access whose
    index has the definition `d`, the copy of `d` into `rematName p.2` followed by the access
    with index `rematName p.2`; otherwise the instruction itself. -/
def rematStep (def? : String → Option LinstrRM) (p : LinstrRM × Nat) : List LinstrRM :=
  match (idxReg? p.1.1).bind def? with
  | some d => [renameDst (rematName p.2) d, (withIdxReg (rematName p.2) p.1.1, p.1.2)]
  | none => [p.1]

/-- The code with a fresh copy of the definition `def? x` before each indexed access whose
    index register `x` has one, at the positions counted from `n`. -/
def rematIdxWith (def? : String → Option LinstrRM) (code : List LinstrRM) (n : Nat := 0) :
    List LinstrRM :=
  (code.zipIdx n).flatMap (rematStep def?)

/-- **Rematerialization of constant indices**: before each `LOADIDX`/`STOREIDX` whose index
    is a body register written exactly once in `code`, by an immediate move, a copy of that
    move into a fresh register, which the access then uses as its index. -/
def rematIdxCode (code : List LinstrRM) : List LinstrRM :=
  rematIdxWith (rematDef? (rematTable code)) code

/-- The empty code is unchanged, at any definitions and start position. -/
@[simp] theorem rematIdxWith_nil (def? : String → Option LinstrRM) (n : Nat) :
    rematIdxWith def? [] n = [] := by
  simp [rematIdxWith]

/-- The empty code is unchanged. -/
@[simp] theorem rematIdxCode_nil : rematIdxCode [] = [] := by
  simp [rematIdxCode]

/-- Code in which no indexed access has an index with a definition is unchanged. -/
theorem rematIdxWith_eq_self (def? : String → Option LinstrRM) (code : List LinstrRM)
    (n : Nat) (h : ∀ i ∈ code, ∀ x, idxReg? i.1 = some x → def? x = none) :
    rematIdxWith def? code n = code := by
  induction code generalizing n with
  | nil => simp
  | cons i is ih =>
    simp only [rematIdxWith] at ih ⊢
    have h0 : rematStep def? (i, n) = [i] := by
      simp only [rematStep]
      cases hx : idxReg? i.1 <;> simp_all
    rw [List.zipIdx_cons, List.flatMap_cons, h0, ih (n + 1) (fun j hj => h j (by simp [hj]))]
    rfl

/-- Without definitions the code is unchanged. -/
theorem rematIdxWith_none (code : List LinstrRM) (n : Nat) :
    rematIdxWith (fun _ => none) code n = code :=
  rematIdxWith_eq_self _ code n (by grind)

/-- **The code is unchanged when no indexed access has a constant index.** -/
theorem rematIdxCode_eq_self (code : List LinstrRM)
    (h : ∀ i ∈ code, ∀ x, idxReg? i.1 = some x → rematDef? (rematTable code) x = none) :
    rematIdxCode code = code :=
  rematIdxWith_eq_self _ code 0 h

/-- The code at most doubles in length. -/
theorem rematIdxWith_length_le (def? : String → Option LinstrRM) (code : List LinstrRM)
    (n : Nat) : (rematIdxWith def? code n).length ≤ 2 * code.length := by
  induction code generalizing n with
  | nil => simp
  | cons i is ih =>
    simp only [rematIdxWith] at ih ⊢
    have h0 : (rematStep def? (i, n)).length ≤ 2 := by
      simp only [rematStep]
      split <;> simp
    have := ih (n + 1)
    simp only [List.zipIdx_cons, List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- **The rematerialized code is at most twice as long as the input.** -/
theorem rematIdxCode_length_le (code : List LinstrRM) :
    (rematIdxCode code).length ≤ 2 * code.length :=
  rematIdxWith_length_le _ code 0

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionRemat
