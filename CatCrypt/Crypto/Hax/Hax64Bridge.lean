/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.Hax64Table
public import CatCrypt.Crypto.Hax.WordOpTable
public import CatCrypt.Crypto.Hax.ExitTowerDefs
public import CatCrypt.Crypto.Jasmin.TowerLimbStore

/-!
# Bridges and leaf semantics at hax-lean's `u64` table

The bridges relating hax values to tower slots and the leaf semantics computing the calls of
`hax64Exit` and `hax64WExit` (`Hax64Table`) on slots:

* `hax64Bridge` relates a scalar word to a slot whose limb `0` is its decoding
  (`hax64ScalarRel`), and an array of scalar words to a slot whose limb `0` is its length
  and whose limb `i + 1` is the decoding of element `i` (`hax64ArrRel`).
* `hax64LeafSpec` computes each admitted call on the words of its argument slots
  (`hax64Call`), writes a word into limb `i` of a slot (`towerLimbSet`), and loads and stores
  array elements at limb `i + 1`.
* `hax64AdmitName` is the Boolean test of the call names `hax64Exit` can admit.
* `hax64WBridge` holds an array at a type of static length with no length limb: at
  `.TArr n t` for a word type `t`, an array of `n` words in limbs `0, …, n - 1`; at
  `.TArr n e` for a non-word type `e` and at the containers `TFp2`, `TFp6`, `TFp12`, an
  array of values in consecutive chunks of the element type's storage. Every other type
  keeps the length-limb layout of `hax64Bridge`.
* `hax64WLeafSpec` reads the length through `wArrLen`, loads and stores the elements of an
  array of words at limb `k + wArrOff t` and those of an array of tower values in chunk `k`,
  builds `repeat` and `array_lit` in the limbs or the chunks of the array slot, and compares
  two argument slots as arrays of words for `eq#arr` and `ne#arr` (`eqArrCall`).

The leaf conditions of the typed exit front at these bridges and leaf semantics are proved in
`HaxFrontHax64` and `HaxFrontHax64W`.

## Main results

* `hax64Exit_mulhi`: `hax64Exit` computes `mulhi#64` on two words as the high word of the
  product
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (Value Builtins hax64Builtins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType RustVal LeafSpec CallSpec rustValByte towerLimb towerLimbSet sexprMulHiU
   sexprMulHiU_lt)

/-! ## The bridge of the `u64` table -/

/-- A scalar word whose decoding is limb `0` of the slot. -/
def hax64ScalarRel {t : TowerType} (v : Value) (r : RustVal t) : Prop :=
  ScalarValN v ∧ valueToScalar v = some (towerLimb r 0)

/-- An array of scalar words held in a slot of a type whose elements are words: limb `0`
    is its length, limb `i + 1` the decoding of element `i`, and the slot holds the length
    and every element. -/
def hax64ArrRel (t : TowerType) (v : Value) (r : RustVal t) : Prop :=
  ∃ vs : List Value, v = .array vs ∧ exitElemTower t = none ∧
    (vs.length + 1) * 8 ≤ t.storageBytes ∧ towerLimb r 0 = vs.length ∧
    ∀ i (h : i < vs.length), ScalarValN vs[i] ∧ valueToScalar vs[i] = some (towerLimb r (i + 1))

/-- The bridge of the `u64` table: a scalar word or an array of scalar words. -/
def hax64Bridge : ValueTowerBridge := fun t v r => hax64ScalarRel v r ∨ hax64ArrRel t v r

/-! ## The leaf semantics of the `u64` table -/

/-- The integer of limb `0` of an argument slot. -/
def hax64CanonArg (p : Σ t : TowerType, RustVal t) : Value := .int (towerLimb p.2 0)

/-- The call semantics of the `u64` table: `len` writes limb `0` of its argument slot, the
    array length, into limb `0`; an operation of `hax64ScalarOp` on two slots writes
    `scalarOpNatT` of their limbs `0` into limb `0`; `Not` writes `1` minus limb `0` of its
    argument slot into limb `0`; any other call writes the decoding of
    `hax64Exit` on the integers of the limbs `0` of its argument slots into limb `0`, and
    keeps the destination when the table refuses. -/
def hax64Call : CallSpec := fun f _ _ old args =>
  if f = "len" then
    match args with
    | [p] => towerLimbSet old 0 (BitVec.ofNat 64 (towerLimb p.2 0))
    | _ => old
  else if hax64ScalarOp f then
    match args with
    | [p, q] =>
        towerLimbSet old 0 (BitVec.ofNat 64 (scalarOpNatT f (towerLimb p.2 0) (towerLimb q.2 0)))
    | _ => old
  else if f = "Not" then
    match args with
    | [p] => towerLimbSet old 0 (BitVec.ofNat 64 (1 - towerLimb p.2 0))
    | _ => old
  else
    match hax64Exit f (args.map hax64CanonArg) with
    | some r => towerLimbSet old 0 (BitVec.ofNat 64 ((valueToScalar r).getD 0))
    | none => old

/-- **The leaf semantics of the `u64` table.**  Calls by `hax64Call`; a limb store writes
    the word into limb `i` (`towerLimbSet`); an element load copies limb `k + 1` of the
    array slot into limb `0` of the destination; an element store writes limb `0` of the
    source slot into limb `k + 1` of the array slot when `k` is below the length in limb
    `0`, and keeps the array slot otherwise. -/
def hax64LeafSpec : LeafSpec where
  call := hax64Call
  limbStore _ old i w := towerLimbSet old i w
  arrLoad _ old src k := towerLimbSet old 0 (BitVec.ofNat 64 (towerLimb src.2 (k + 1)))
  arrStore _ old k src :=
    if k < towerLimb old 0 then towerLimbSet old (k + 1) (BitVec.ofNat 64 (towerLimb src.2 0))
    else old

/-! ## The names the table admits -/

/-- The scalar call names on which `Hax.hax64Builtins` is defined: the arms of
    `Hax.hax64WordOps`, `Hax.hax64NarrowOps` and `Hax.hax64CmpOps`. -/
def hax64ScalarNames : List String :=
  ["wrapping_add#64", "wrapping_sub#64", "wrapping_mul#64", "mulhi#64", "BitAnd#64",
   "BitOr#64", "BitXor#64", "Shl#64", "shl#64", "Shr#64", "shr#64", "Add", "cast#64",
   "cast#128", "Mul", "Shr#128", "Rem", "Div", "mulmod#64", "cast#8", "cast#32",
   "wrapping_add#8", "wrapping_sub#8", "wrapping_mul#8", "BitAnd#8", "BitOr#8", "BitXor#8",
   "Shl#8", "Shr#8", "wrapping_add#32", "wrapping_sub#32", "wrapping_mul#32", "BitAnd#32",
   "BitOr#32", "BitXor#32", "Shl#32", "Shr#32",
   "cast#16", "cast#size", "wrapping_add#16", "wrapping_sub#16", "wrapping_mul#16",
   "BitAnd#16", "BitOr#16", "BitXor#16", "Shl#16", "Shr#16", "wrapping_add#size",
   "wrapping_sub#size", "wrapping_mul#size", "BitAnd#size", "BitOr#size", "BitXor#size",
   "Shl#size", "Shr#size", "rotate_right#8", "rotate_right#16", "rotate_right#32",
   "rotate_right#64", "rotate_right#size", "rotate_left#8", "rotate_left#16",
   "rotate_left#32", "rotate_left#64", "rotate_left#size", "Not#8", "Not#16", "Not#32",
   "Not#64", "Not#size",
   "Lt", "lt", "Gt", "gt", "Le", "le", "Ge", "ge", "Eq", "eq", "Ne", "ne", "&&", "and", "||",
   "or", "add", "Sub", "sub", "Not", "cast#u32", "cast#u64", "cast#usize", "wrapping_neg#64"]

/-- A call name that `hax64Exit` can admit: an array operation, or a scalar call of
    `Hax.hax64Builtins` with a scalar result at a call tower type holding a word. -/
def hax64AdmitName (f : String) : Bool :=
  ["len", "index", "array_update"].contains f ||
    (hax64ScalarNames.contains f && exitScalarRes f && exitMarshalOk (towerOfCallName f))

/-! ## Static lengths -/

/-- The static length of an array type: `n` at `.TArr n t`, `2`, `3`, `2` at the
    containers `TFp2`, `TFp6`, `TFp12`, `none` at every other type. -/
def wordArrLen? : TowerType → Option Nat
  | .TArr n _ => some n
  | .TFp2 => some 2
  | .TFp6 => some 3
  | .TFp12 => some 2
  | _ => none

/-- The limb of element `0` of a word array held at `t`: `0` at a type of static length,
    `1` at every other type, whose limb `0` holds the length. -/
def wArrOff (t : TowerType) : Nat := if (wordArrLen? t).isSome then 0 else 1

/-- The length of the array a slot of type `t` holds: the static length of `t`, or
    limb `0`. -/
def wArrLen {t : TowerType} (r : RustVal t) : Nat := (wordArrLen? t).getD (towerLimb r 0)

/-! ## Chunks -/

/-- The `i`-th chunk of `e.storageBytes` bytes of `r`, as a value of type `e`. -/
def chunkGet {t : TowerType} (r : RustVal t) (e : TowerType) (i : Nat) : RustVal e :=
  fun j => rustValByte r (i * e.storageBytes + j.val)

/-- `r` with its `i`-th chunk of `e.storageBytes` bytes replaced by `s`. -/
def chunkSet {t : TowerType} (r : RustVal t) (i : Nat) {e : TowerType} (s : RustVal e) :
    RustVal t :=
  fun j => if i * e.storageBytes ≤ j.val ∧ j.val < i * e.storageBytes + e.storageBytes then
      rustValByte s (j.val - i * e.storageBytes) else r j

/-- The slot of type `dt` whose `i`-th chunk of `e.storageBytes` bytes holds the bytes of the
    `i`-th slot of `args`. -/
def litChunks (dt e : TowerType) (args : List (Σ t : TowerType, RustVal t)) : RustVal dt :=
  fun j => match args[j.val / e.storageBytes]? with
    | some p => rustValByte p.2 (j.val % e.storageBytes)
    | none => 0

/-- The slot of type `dt` whose every chunk of `e.storageBytes` bytes holds the bytes of the
    slot `p`. -/
def fillChunks (dt e : TowerType) (p : Σ t : TowerType, RustVal t) : RustVal dt :=
  fun j => rustValByte p.2 (j.val % e.storageBytes)

/-! ## Arrays of tower values -/

/-- The length and the element type of a type whose elements are tower values: `(n, e)` at
    `.TArr n e` for a non-word type `e`, `(2, TFp)`, `(3, TFp2)`, `(2, TFp6)` at the
    containers `TFp2`, `TFp6`, `TFp12`, `none` at every other type. -/
def towArrElem? : TowerType → Option (Nat × TowerType)
  | .TArr n e => if exitWordTower e then none else some (n, e)
  | .TFp2 => some (2, .TFp)
  | .TFp6 => some (3, .TFp2)
  | .TFp12 => some (2, .TFp6)
  | _ => none

/-! ## The bridge with static array types -/

/-- An array of fewer than `2^64` scalar words held in a slot of type `t` whose elements are
    words: the slot holds its length (`wArrLen`) and element `i` in limb `i + wArrOff t`. -/
def hax64WArrRel (t : TowerType) (v : Value) (r : RustVal t) : Prop :=
  ∃ vs : List Value, v = .array vs ∧ exitElemTower t = none ∧ vs.length < 2 ^ 64 ∧
    (vs.length + wArrOff t) * 8 ≤ t.storageBytes ∧ wArrLen r = vs.length ∧
    ∀ i (h : i < vs.length), ScalarValN vs[i] ∧
      valueToScalar vs[i] = some (towerLimb r (i + wArrOff t))

/-- A scalar word or an array of scalar words by `hax64WArrRel`. -/
def hax64WBase (t : TowerType) (v : Value) (r : RustVal t) : Prop :=
  hax64ScalarRel v r ∨ hax64WArrRel t v r

/-- An array of `n < 2^64` values whose element `i` is related by `R` to chunk `i` of the
    slot, the chunks of type `e`. -/
def hax64WCont {t : TowerType} (n : Nat) (e : TowerType) (R : Value → RustVal e → Prop)
    (v : Value) (r : RustVal t) : Prop :=
  ∃ vs : List Value, v = .array vs ∧ vs.length = n ∧ n < 2 ^ 64 ∧
    ∀ i (h : i < vs.length), R vs[i] (chunkGet r e i)

/-- The bridge at `TFp2`: a scalar word, or two values related at `TFp`. -/
def hax64WFp2Rel (v : Value) (r : RustVal .TFp2) : Prop :=
  hax64ScalarRel v r ∨ hax64WCont 2 .TFp (hax64WBase .TFp) v r

/-- The bridge at `TFp6`: a scalar word, or three values related at `TFp2`. -/
def hax64WFp6Rel (v : Value) (r : RustVal .TFp6) : Prop :=
  hax64ScalarRel v r ∨ hax64WCont 3 .TFp2 hax64WFp2Rel v r

/-- The bridge at `TFp12`: a scalar word, or two values related at `TFp6`. -/
def hax64WFp12Rel (v : Value) (r : RustVal .TFp12) : Prop :=
  hax64ScalarRel v r ∨ hax64WCont 2 .TFp6 hax64WFp6Rel v r

/-- **The bridge of the `u64` table with static array types.**  A scalar word; an array of
    scalar words by `hax64WArrRel`; at `.TArr n e` of a non-word type `e`, an array of `n`
    values related at `e` chunk by chunk; at the containers, their arrays chunk by chunk. -/
def hax64WBridge : (t : TowerType) → Value → RustVal t → Prop
  | .TArr n e, v, r => hax64ScalarRel v r ∨ hax64WArrRel (.TArr n e) v r ∨
      (exitWordTower e = false ∧ hax64WCont n e (hax64WBridge e) v r)
  | .TFp2, v, r => hax64WFp2Rel v r
  | .TFp6, v, r => hax64WFp6Rel v r
  | .TFp12, v, r => hax64WFp12Rel v r
  | t, v, r => hax64WBase t v r

/-- The array relation of `hax64WBridge` at a type of `towArrElem?`. -/
def hax64WTowRel (t : TowerType) (v : Value) (r : RustVal t) : Prop :=
  ∃ n e, towArrElem? t = some (n, e) ∧ hax64WCont n e (hax64WBridge e) v r

/-! ## The leaf semantics with static array types -/

/-- `old` with limbs `0, …, n - 1` set to the word `w`. -/
def fillLimbs {t : TowerType} (old : RustVal t) (w : Nat) : Nat → RustVal t
  | 0 => old
  | n + 1 => towerLimbSet (fillLimbs old w n) n (BitVec.ofNat 64 w)

/-- `old` with limb `i + j` set to limb `0` of the `j`-th slot of `ps`. -/
def litLimbs {t : TowerType} (old : RustVal t) (i : Nat) :
    List (Σ t : TowerType, RustVal t) → RustVal t
  | [] => old
  | p :: ps => litLimbs (towerLimbSet old i (BitVec.ofNat 64 (towerLimb p.2 0))) (i + 1) ps

/-- The words an argument slot holds as an array: at a type of `towArrElem?` with `n`
    elements of type `e`, limb `0` of each of its `n` chunks; at any other type, its
    `wArrLen` elements at limbs `i + wArrOff t`. -/
def slotWords (p : Σ t : TowerType, RustVal t) : List Nat :=
  match towArrElem? p.1 with
  | some (n, e) => (List.range n).map fun i => towerLimb (chunkGet p.2 e i) 0
  | none => (List.range (wArrLen p.2)).map fun i => towerLimb p.2 (i + wArrOff p.1)

/-- The Boolean `c`, negated when `neg` holds. -/
def eqArrBool (neg c : Bool) : Bool :=
  match neg with
  | true => !c
  | false => c

/-- The comparison of two argument slots as arrays of words (`slotWords`), negated when
    `neg` holds, written into limb `0` of the destination as `1` or `0`; the destination
    is kept on any other argument list. -/
def eqArrCall {dt : TowerType} (neg : Bool) (old : RustVal dt)
    (args : List (Σ t : TowerType, RustVal t)) : RustVal dt :=
  match args with
  | [p, q] => towerLimbSet old 0 (BitVec.ofNat 64 (eqArrBool neg (slotWords p == slotWords q)).toNat)
  | _ => old

/-- The call semantics with static array types: `len` writes the length `wArrLen` of its
    argument slot into limb `0`; `repeat` writes the bytes of its fill slot into every chunk
    of a type of tower values (`fillChunks`), and limb `0` of its fill slot into limbs
    `0, …, n - 1` of an array type `.TArr n t` of words; `array_lit` at a type of tower values
    writes its argument slots into consecutive chunks (`litChunks`), and at an array type of
    words limb `0` of its `j`-th argument slot into limb `j`; `eq#arr` and `ne#arr` compare
    their two argument slots as arrays of words (`eqArrCall`); every other call is
    `hax64Call`. -/
def hax64WCall : CallSpec := fun f dt ds old args =>
  if f = "len" then
    match args with
    | [p] => towerLimbSet old 0 (BitVec.ofNat 64 (wArrLen p.2))
    | _ => old
  else if f = "repeat" then
    match args with
    | p :: _ =>
      match towArrElem? dt with
      | some (_, e) => fillChunks dt e p
      | none =>
        match wordArrLen? dt with
        | some n => fillLimbs old (towerLimb p.2 0) n
        | none => old
    | [] => old
  else if f = "array_lit" then
    match towArrElem? dt with
    | some (_, e) => litChunks dt e args
    | none => if (wordArrLen? dt).isSome then litLimbs old 0 args else old
  else if f = "eq#arr" then eqArrCall false old args
  else if f = "ne#arr" then eqArrCall true old args
  else hax64Call f dt ds old args

/-- **The leaf semantics of the `u64` table with static array types.**  Calls by
    `hax64WCall`; a limb store writes the word into limb `i`; an element load from an array
    of tower values copies chunk `k` into the destination, and from any other array copies
    limb `k + wArrOff t` of the array slot of type `t` into limb `0` of the destination; an
    element store with `k` below the length `wArrLen` writes the source slot into chunk `k`
    of an array of tower values, and limb `0` of the source slot into limb `k + wArrOff t`
    of any other array, and keeps the array slot when `k` is not below the length. -/
def hax64WLeafSpec : LeafSpec where
  call := hax64WCall
  limbStore _ old i w := towerLimbSet old i w
  arrLoad dst old src k :=
    match towArrElem? src.1 with
    | some _ => chunkGet src.2 dst.locDst k
    | none => towerLimbSet old 0 (BitVec.ofNat 64 (towerLimb src.2 (k + wArrOff src.1)))
  arrStore loc old k src :=
    if k < wArrLen old then
      match towArrElem? loc.locDst with
      | some _ => chunkSet old k src.2
      | none => towerLimbSet old (k + wArrOff loc.locDst) (BitVec.ofNat 64 (towerLimb src.2 0))
    else old

/-! ## The high word of a product -/

/-- The `u64` table computes `mulhi#64` on two words as the high word of the product. -/
theorem hax64Exit_mulhi {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    hax64Exit "mulhi#64" [.int a, .int b] = some (.int (sexprMulHiU a b : Nat)) := by
  have hbi : hax64Builtins "mulhi#64" [.int a, .int b] = some (.int (sexprMulHiU a b : Nat)) := by
    unfold hax64Builtins
    rw [_root_.Hax.hax64WordOps_mulhi, _root_.Hax.u64BinOp_natCast ha hb,
      sexprMulHiU_of_lt ha hb]
    rfl
  have hop : hax64ScalarOp "mulhi#64" = false := by
    simp [hax64ScalarOp, scalarOpExprT, widthOpOf]
  have hto : towerOfCallName "mulhi#64" = .TFp := by
    simp [towerOfCallName, TowerOfCallNameInst.callTower, towerOfCallName_default]
  have hres : exitScalarRes "mulhi#64" = true := by simp [exitScalarRes, exitScalarCall]
  have hne : ("mulhi#64" != "len") = true := by simp
  have hargs : hax64IntArgs [.int a, .int b] = true := by
    simp [hax64IntArgs]
    omega
  have hval : scalarValNB (.int (sexprMulHiU a b : Nat)) = true := by
    have := sexprMulHiU_lt a b
    simp [scalarValNB]
    omega
  refine hax64Exit_of_scalarAdmit hbi rfl ?_
  simp only [hax64ScalarAdmit, hres, hne, hax64ArgsShape, hop, hargs, hto, hval,
    Bool.false_eq_true, ite_false, Bool.true_and, Bool.and_true]
  simp only [exitMarshalOk, CatCrypt.Crypto.Jasmin.LowCT.TowerType.storageBytes]
  decide

end CatCrypt.Crypto.Hax
