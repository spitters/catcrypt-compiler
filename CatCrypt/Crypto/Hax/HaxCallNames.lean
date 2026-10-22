/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTTypes
public import CatCrypt.Crypto.Jasmin.LowCTTypes
public import CatCrypt.Crypto.Jasmin.LowCTSExpr
public import HaxLean.Value

/-!
# Call-name, width and slot-name tables of the hax front

The tables the hax front reads off call names and values, over `TowerType`, `SExpr` and
hax-lean's `Value` only. They are shared by the legacy front `haxToLowCT`, which re-exports
this module, and by the leakage analysis of `compileA`'s front, which imports it without the
legacy front.

## Main definitions

* the destination tower type of a leaf call (`TowerOfCallNameInst`, `towerOfCallName`,
  `towerOfCallName_default`) and the array-constructor names `repeat_<v>_<n>`
  (`arrCtorLenL`, `arrCtorLen`, `arrCtorName`, `arrCtorTower`);
* the scalar operations (`scalarOpExpr`, `scalarOpExprT`), the width-tagged word calls
  `op#w` (`WidthOp`, `widthOpOf`, `widthMask`, `WidthOp.sexpr`) and the calls with a
  scalar result (`exitScalarCalls`, `exitScalarCall`, `exitScalarRes`);
* the word and element tower types (`exitWordTower`, `exitElemTower`, `exitContainer`,
  `exitMarshalOk`);
* the scalar values (`valueToScalar`, `ScalarValN`, `scalarValNB`);
* the reserved and component slot names (`exitResName`, `exitReserved`,
  `structCompName`).

## Main results

* `widthOpOf_spec`: a width-tagged call name is an operation name, `#` and a tag `8`, `16`,
  `32`, `64` or `size`.
* `exitMarshalOk_of_arrCtorLen`: the default call tower type of a name that is no array
  constructor holds a word.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (Value)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType SExpr)

/-! ## §1  Tower type from leaf-call name

The H1 `callWhitelist` lumps all leaf calls together; H2 must additionally
decide which tower type each call's destination has.  For the prefix-based
naming convention used by hax-extracted shims, this is mechanical.

### Per-protocol override pattern

A single hard-coded prefix dispatch cannot disambiguate cross-protocol
name collisions: for example, `scalar_add` legitimately means *different*
tower types in different protocols (Curve25519's `.TFpL25519` vs BLS's
BLS-scalar field).

The dispatch is the typeclass `TowerOfCallNameInst`.  The
*default* dispatch (`towerOfCallName_default`) is the prefix-based
dispatch and is registered as the default instance.  Protocols that need a
different mapping for a name collision provide their own typeclass
instance scoped to their bridge namespace.

An Ed25519-specific override has this shape:

```lean
namespace CatCrypt.Crypto.EdDSA

instance edDSA_TowerOfCallNameInst :
    CatCrypt.Crypto.Hax.TowerOfCallNameInst :=
  ⟨fun f => match f with
    | "scalar_add" => .TFpL25519  -- Ed25519 scalar (= default)
    | _            => CatCrypt.Crypto.Hax.towerOfCallName_default f⟩

end CatCrypt.Crypto.EdDSA
```

The same shape works for BLS to remap `scalar_*`, `g2_*`, `bbs_*`, and
`*_be_bytes` to BLS-correct tower types.  -/

/-! ### Array constructors

A hax `repeat(v, n)` with literal fill value `v` and literal count `n` is an
array constructor.  The source pass `ctorNorm` (dev `HaxToLowCT_ArithCtor.lean`)
names the call `repeat_<v>_<n>` with no arguments, so both literals are part of
the call name and the located type of the destination is the word-array type
`.TArr n .TFp`.  The name family is decoded by `arrCtorLen`, which the dispatch
on call names consults first. -/

/-- The value of a list of decimal digits accumulated onto `acc`; `none` at a character that
    is no decimal digit. -/
@[simp] def decDigitsAcc : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
      if '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat then
        decDigitsAcc cs (acc * 10 + (c.toNat - '0'.toNat))
      else none

/-- The value of a non-empty list of decimal digits. -/
@[simp] def digitsVal? : List Char → Option Nat
  | [] => none
  | c :: cs => decDigitsAcc (c :: cs) 0

/-- The list `l` without its prefix `p`, when `p` is a prefix of `l`. -/
@[simp] def stripPrefixL : List Char → List Char → Option (List Char)
  | [], l => some l
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p = c then stripPrefixL ps cs else none

/-- The characters before and after the first `'_'` of a list. -/
@[simp] def splitUnderscore : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if c = '_' then some ([], cs) else (splitUnderscore cs).map fun p => (c :: p.1, p.2)

/-- The prefix of the array-constructor call names. -/
@[simp] def arrCtorPrefix : String := "repeat_"

/-- The array-constructor call name for the literal fill value `v` and count `n`. -/
def arrCtorName (v n : Nat) : String := arrCtorPrefix ++ Nat.repr v ++ "_" ++ Nat.repr n

/-- The fill value and count of an array-constructor call name `repeat_<v>_<n>`,
    on the characters of the name. -/
@[simp] def arrCtorLenL (l : List Char) : Option (Nat × Nat) :=
  match stripPrefixL arrCtorPrefix.toList l with
  | some rest =>
      match splitUnderscore rest with
      | some (ds, es) =>
          match digitsVal? ds, digitsVal? es with
          | some v, some n => some (v, n)
          | _, _ => none
      | none => none
  | none => none

/-- The fill value and count of an array-constructor call name `repeat_<v>_<n>`;
    `none` on every other name. -/
@[simp] def arrCtorLen (f : String) : Option (Nat × Nat) := arrCtorLenL f.toList

/-- The located type of the destination of an array-constructor call: the
    word-array type of the count. -/
def arrCtorTower (f : String) : Option TowerType :=
  (arrCtorLen f).map fun p => .TArr p.2 .TFp

theorem arrCtorTower_of_arrCtorLen {f : String} {v n : Nat} (h : arrCtorLen f = some (v, n)) :
    arrCtorTower f = some (.TArr n .TFp) := by
  simp only [arrCtorTower, h, Option.map_some]

theorem arrCtorTower_of_arrCtorLen_none {f : String} (h : arrCtorLen f = none) :
    arrCtorTower f = none := by
  simp only [arrCtorTower, h, Option.map_none]

/-- Default dispatch from leaf-call names to `TowerType`: an array-constructor
    name `repeat_<v>_<n>` is dispatched to the word-array type `.TArr n .TFp`, and
    every other name by its prefix.  It is the default instance of
    `TowerOfCallNameInst` below.

    Falls back to `.TFp` for unrecognised names; the H1 filter restricts the
    reachable names to the whitelist, so every reachable string here is one of the
    documented prefixes.

    The EdDSA extraction emits abstract leaf names (`group_*`, `scalar_*`,
    `hash_*`, `generator`); point operations are dispatched to `.TFp25519`, scalar
    operations and hash challenges to `.TFpL25519`. -/
def towerOfCallName_default (f : String) : TowerType :=
  match arrCtorLen f with
  | some p => .TArr p.2 .TFp
  | none =>
  if f.startsWith "fp12_" then .TFp12
  else if f.startsWith "fp6_" then .TFp6
  else if f.startsWith "fp2_" then .TFp2
  else if f.startsWith "fp25519_" then .TFp25519
  else if f.startsWith "scalar25519_" then .TFpL25519
  else if f.startsWith "fpP256_" then .TFpP256
  else if f.startsWith "u64_" then .TU64
  else if f.startsWith "fp_" then .TFp
  -- Ed25519 abstract leaves
  else if f.startsWith "group_" then .TFp25519
  else if f.startsWith "scalar_" then .TFpL25519
  else if f.startsWith "hash_" then .TFpL25519
  else if f = "generator" then .TFp25519
  else .TFp

/-- Per-protocol mapping from leaf call names to the destination
    `TowerType` that `haxToLowCT` uses.  Protocols override this
    with their own instances to handle name collisions (e.g.,
    `scalar_add` differs between Curve25519, BLS12-381, P-256).

    The default instance wraps `towerOfCallName_default`. -/
class TowerOfCallNameInst where
  /-- The dispatch function. -/
  callTower : String → TowerType

/-- Default instance: the prefix-based dispatch, at low priority, so that a
    protocol-local instance shadows it. -/
instance (priority := low) defaultTowerOfCallNameInst :
    TowerOfCallNameInst :=
  ⟨towerOfCallName_default⟩

/-- Dispatch from leaf-call names to `TowerType`, parametrised
    by a `TowerOfCallNameInst` instance.  It is `towerOfCallName_default` when no
    protocol override is in scope (via `defaultTowerOfCallNameInst`). -/
@[reducible] def towerOfCallName [inst : TowerOfCallNameInst]
    (f : String) : TowerType :=
  inst.callTower f

/-! ### Grind-database lemmas for `towerOfCallName`

The `String.startsWith` checks in `towerOfCallName_default` are not
reducible by `decide` (only by `native_decide`).  Per-prefix
`@[grind =]` rewrite lemmas let `grind` discharge
`towerOfCallName "..." = ...` goals without invoking `decide`.

Each lemma proves `towerOfCallName <concrete-name> = <tower-type>` by
`native_decide`; the `@[grind =]` makes the equation a rewrite rule
for the grind database.

The lemmas are stated against `towerOfCallName` (the typeclass form),
which under the default instance reduces to `towerOfCallName_default`.
When a protocol installs its own `TowerOfCallNameInst` instance, these
lemmas do not apply; the protocol bridge supplies its own per-leaf lemmas. -/

@[grind =] theorem towerOfCallName_generator :
    towerOfCallName "generator" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_group_add :
    towerOfCallName "group_add" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_group_mul :
    towerOfCallName "group_mul" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_scalar_add :
    towerOfCallName "scalar_add" = .TFpL25519 := by native_decide

@[grind =] theorem towerOfCallName_scalar_mul :
    towerOfCallName "scalar_mul" = .TFpL25519 := by native_decide

@[grind =] theorem towerOfCallName_hash_challenge :
    towerOfCallName "hash_challenge" = .TFpL25519 := by native_decide

@[grind =] theorem towerOfCallName_fp25519_add :
    towerOfCallName "fp25519_add" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_fp25519_mul :
    towerOfCallName "fp25519_mul" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_fp25519_sq :
    towerOfCallName "fp25519_sq" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_fp25519_inv :
    towerOfCallName "fp25519_inv" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_scalar25519_reduce :
    towerOfCallName "scalar25519_reduce" = .TFpL25519 := by native_decide

/-- Under the default instance, the typeclass-dispatched `towerOfCallName` agrees
    with `towerOfCallName_default` pointwise: the default instance's `callTower`
    field is `towerOfCallName_default`. -/
theorem towerOfCallName_default_eq (f : String) :
    towerOfCallName f = towerOfCallName_default f := rfl

/-- An array-constructor call name `repeat_<v>_<n>` is dispatched to the
    word-array type `.TArr n .TFp`. -/
theorem towerOfCallName_of_arrCtorLen {f : String} {v n : Nat}
    (h : arrCtorLen f = some (v, n)) : towerOfCallName f = .TArr n .TFp := by
  rw [towerOfCallName_default_eq]
  unfold towerOfCallName_default
  rw [h]

/-! ## §2  Scalar operations -/

/-- The `SExpr` of hax-lean's unsigned operation `op` on the scalars `a` and
    `b`.  Over `Nat`, `lt`, `gt`, `le`, `ge`, `eq` and `ne` are exact (each
    `SLt` is `0` or `1`, and `SSub` truncates at `0`); `add` and `sub` agree with
    hax-lean's wrapping `u64` operations when `a + b < 2^64` and `b ≤ a`. -/
def scalarOpExpr (op : String) (a b : SExpr) : Option SExpr :=
  match op with
  | "lt"  => some (.SLt a b)
  | "gt"  => some (.SLt b a)
  | "le"  => some (.SSub (.SLit 1) (.SLt b a))
  | "ge"  => some (.SSub (.SLit 1) (.SLt a b))
  | "eq"  => some (.SSub (.SSub (.SLit 1) (.SLt a b)) (.SLt b a))
  | "ne"  => some (.SAdd (.SLt a b) (.SLt b a))
  | "add" => some (.SAdd a b)
  | "sub" => some (.SSub a b)
  | _     => none

/-- The two-operand operations of hax-lean's width-tagged word calls `op#w`. -/
inductive WidthOp where
  | add | sub | mul | and | or | xor | shl | shr | rotr | rotl
  deriving DecidableEq, Repr

/-- The width and operation of a width-tagged call name `op#w`: the operations
    `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `BitAnd`, `BitOr`, `BitXor`, `Shl`,
    `Shr`, `rotate_right`, `rotate_left` at the tags `8`, `16`, `32`, `64` and `size`
    (width `64`). -/
def widthOpOf : String → Option (Nat × WidthOp)
  | "wrapping_add#8" => some (8, .add)
  | "wrapping_add#16" => some (16, .add)
  | "wrapping_add#32" => some (32, .add)
  | "wrapping_add#64" => some (64, .add)
  | "wrapping_add#size" => some (64, .add)
  | "wrapping_sub#8" => some (8, .sub)
  | "wrapping_sub#16" => some (16, .sub)
  | "wrapping_sub#32" => some (32, .sub)
  | "wrapping_sub#64" => some (64, .sub)
  | "wrapping_sub#size" => some (64, .sub)
  | "wrapping_mul#8" => some (8, .mul)
  | "wrapping_mul#16" => some (16, .mul)
  | "wrapping_mul#32" => some (32, .mul)
  | "wrapping_mul#64" => some (64, .mul)
  | "wrapping_mul#size" => some (64, .mul)
  | "BitAnd#8" => some (8, .and)
  | "BitAnd#16" => some (16, .and)
  | "BitAnd#32" => some (32, .and)
  | "BitAnd#64" => some (64, .and)
  | "BitAnd#size" => some (64, .and)
  | "BitOr#8" => some (8, .or)
  | "BitOr#16" => some (16, .or)
  | "BitOr#32" => some (32, .or)
  | "BitOr#64" => some (64, .or)
  | "BitOr#size" => some (64, .or)
  | "BitXor#8" => some (8, .xor)
  | "BitXor#16" => some (16, .xor)
  | "BitXor#32" => some (32, .xor)
  | "BitXor#64" => some (64, .xor)
  | "BitXor#size" => some (64, .xor)
  | "Shl#8" => some (8, .shl)
  | "Shl#16" => some (16, .shl)
  | "Shl#32" => some (32, .shl)
  | "Shl#64" => some (64, .shl)
  | "Shl#size" => some (64, .shl)
  | "Shr#8" => some (8, .shr)
  | "Shr#16" => some (16, .shr)
  | "Shr#32" => some (32, .shr)
  | "Shr#64" => some (64, .shr)
  | "Shr#size" => some (64, .shr)
  | "rotate_right#8" => some (8, .rotr)
  | "rotate_right#16" => some (16, .rotr)
  | "rotate_right#32" => some (32, .rotr)
  | "rotate_right#64" => some (64, .rotr)
  | "rotate_right#size" => some (64, .rotr)
  | "rotate_left#8" => some (8, .rotl)
  | "rotate_left#16" => some (16, .rotl)
  | "rotate_left#32" => some (32, .rotl)
  | "rotate_left#64" => some (64, .rotl)
  | "rotate_left#size" => some (64, .rotl)
  | _ => none

/-- A name `widthOpOf` reads is an operation name, `#` and a tag `8`, `16`, `32`, `64` or
    `size`. -/
theorem widthOpOf_spec {f : String} {r : Nat × WidthOp} (h : widthOpOf f = some r) :
    ∃ op ∈ ["wrapping_add", "wrapping_sub", "wrapping_mul", "BitAnd", "BitOr", "BitXor", "Shl",
        "Shr", "rotate_right", "rotate_left"],
      ∃ tag ∈ ["8", "16", "32", "64", "size"], f = op ++ "#" ++ tag := by
  unfold widthOpOf at h
  split at h <;> (try cases h) <;> decide

/-- `e` masked to its low `w` bits: `e &&& (2^w - 1)`, which over `Nat` is
    `e % 2^w`. -/
def widthMask (w : Nat) (e : SExpr) : SExpr := .SAnd e (.SLit (2 ^ w - 1))

/-- The bitwise disjunction as `(a ^^^ b) ^^^ (a &&& b)`, exact over `Nat`. -/
def orExprN (a b : SExpr) : SExpr := .SXor (.SXor a b) (.SAnd a b)

/-- The rotation amount `b` modulo a width `w` that is a power of two:
    `b &&& (w - 1)`. -/
def widthAmt (w : Nat) (b : SExpr) : SExpr := .SAnd b (.SLit (w - 1))

/-- The scalar expression of the width-tagged operation `op` at width `w` on `a`
    and `b`, with `x % 2^w` written as `widthMask w x`, `n % w` as `widthAmt w n` and
    `|||` as `orExprN`. The difference is `((a % 2^w + (2^w - 1)) - b % 2^w) + 1` masked, whose
    literals are words at every width `w ≤ 64`. -/
def WidthOp.sexpr (w : Nat) : WidthOp → SExpr → SExpr → SExpr
  | .add, a, b => widthMask w (.SAdd a b)
  | .sub, a, b => widthMask w
      (.SAdd (.SSub (.SAdd (widthMask w a) (.SLit (2 ^ w - 1))) (widthMask w b)) (.SLit 1))
  | .mul, a, b => widthMask w (.SMul a b)
  | .and, a, b => .SAnd (widthMask w a) (widthMask w b)
  | .or, a, b => orExprN (widthMask w a) (widthMask w b)
  | .xor, a, b => .SXor (widthMask w a) (widthMask w b)
  | .shl, a, b => widthMask w (.SShl (widthMask w a) b)
  | .shr, a, b => .SShr (widthMask w a) b
  | .rotr, a, b => widthMask w (orExprN (.SShr (widthMask w a) (widthAmt w b))
      (.SShl (widthMask w a) (.SSub (.SLit w) (widthAmt w b))))
  | .rotl, a, b => widthMask w (orExprN (.SShl (widthMask w a) (widthAmt w b))
      (.SShr (widthMask w a) (.SSub (.SLit w) (widthAmt w b))))

/-- The `SExpr` of a scalar operation on the scalars `a` and `b`: the operations of
    `scalarOpExpr`, their capitalised forms, the checked additions and subtractions at the
    unsigned tags `8`, `16`, `32`, `64` and `size` (`Add#w`, `Sub#w`) as `Add` and `Sub`, the
    Boolean connectives `&&`, `and` as `SAnd` and `||`, `or` as `orExprN` (exact on the
    decodings `0` and `1` of two Booleans), and the width-tagged calls of `widthOpOf`. A
    checked operation at a tag is defined only where its result lies below `2 ^ w`, so its
    value is the unmasked sum or difference. -/
def scalarOpExprT (op : String) (a b : SExpr) : Option SExpr :=
  match op with
  | "lt" | "Lt" => some (.SLt a b)
  | "gt" | "Gt" => some (.SLt b a)
  | "le" | "Le" => some (.SSub (.SLit 1) (.SLt b a))
  | "ge" | "Ge" => some (.SSub (.SLit 1) (.SLt a b))
  | "eq" | "Eq" => some (.SSub (.SSub (.SLit 1) (.SLt a b)) (.SLt b a))
  | "ne" | "Ne" => some (.SAdd (.SLt a b) (.SLt b a))
  | "add" | "Add" | "Add#8" | "Add#16" | "Add#32" | "Add#64" | "Add#size" => some (.SAdd a b)
  | "sub" | "Sub" | "Sub#8" | "Sub#16" | "Sub#32" | "Sub#64" | "Sub#size" => some (.SSub a b)
  | "&&" | "and" => some (.SAnd a b)
  | "||" | "or" => some (orExprN a b)
  | _ => (widthOpOf op).map fun p => p.2.sexpr p.1 a b

/-- The call names whose result is a scalar besides the width-tagged ones; `declassify` is
    the identity on a word. -/
def exitScalarCalls : List String :=
  ["len", "lt", "gt", "le", "ge", "eq", "ne", "add", "sub",
   "Lt", "Gt", "Le", "Ge", "Eq", "Ne", "Add", "Sub", "Mul", "Div", "Rem",
   "BitAnd", "BitOr", "BitXor", "Shl", "Shr", "Not", "Neg", "&&", "||", "and", "or",
   "range_incl_end", "declassify"]

/-- A call whose result is held in the scalar heap: a name of `exitScalarCalls` or a
    width-tagged name (containing `#`). -/
def exitScalarCall (f : String) : Bool := exitScalarCalls.contains f || f.contains '#'

/-- The leaf calls whose arguments are held in towers and whose result is a scalar: the
    zero and identity predicates of field elements and curve points and the infinity
    flags `infinity`, `g2_inf` of a point, used as conditions, and the accessors `k`,
    `l`, `ctilde_len` (ML-DSA parameters), `height` and `depth` (a trace and a Merkle
    tree), used as loop bounds.  Each is a leaf whose specification returns a word,
    not an element of the tower. -/
def exitTowerScalarNames : List String :=
  ["is_zero", "fe_is_zero", "fp_is_zero", "fp2_is_zero", "h2c_p256_is_zero",
   "point_is_identity", "g1_proj_is_identity", "g2_proj_is_identity", ".infinity",
   ".g2_inf", ".k", ".l", "ctilde_len", ".height", ".depth"]

/-- A leaf call of `exitTowerScalarNames`. -/
def exitTowerScalarCall (f : String) : Bool := exitTowerScalarNames.contains f

/-- A call whose result the typed lowering copies from limb `0` of the call slot into the
    scalar heap: a scalar call or a leaf call of `exitTowerScalarNames`. -/
def exitScalarRes (f : String) : Bool := exitScalarCall f || exitTowerScalarCall f

theorem exitScalarRes_index : exitScalarRes "index" = false := by
  simp [exitScalarRes, exitScalarCall, exitScalarCalls, exitTowerScalarCall, exitTowerScalarNames]

theorem exitScalarRes_arrayLit : exitScalarRes "array_lit" = false := by
  simp [exitScalarRes, exitScalarCall, exitScalarCalls, exitTowerScalarCall, exitTowerScalarNames]

theorem exitScalarRes_declassify : exitScalarRes "declassify" = true := by
  simp [exitScalarRes, exitScalarCall, exitScalarCalls]

/-! ## §3  Word and element tower types -/

/-- A tower type holding one scalar word: `TU64`, `TU32`, `TU8`. -/
def exitWordTower : TowerType → Bool
  | .TU64 | .TU32 | .TU8 => true
  | _ => false

/-- The element tower type of a tower type whose elements are tower values: an element of
    `TFp2` is a `TFp`, of `TFp6` a `TFp2`, of `TFp12` a `TFp6`, and of `TArr n t` a `t`
    when `t` is not a word type (`exitWordTower`).  `none` for a tower type whose elements
    are scalar words. -/
def exitElemTower : TowerType → Option TowerType
  | .TFp2 => some .TFp
  | .TFp6 => some .TFp2
  | .TFp12 => some .TFp6
  | .TArr _ t => if exitWordTower t then none else some t
  | _ => none

/-- The tower type of an array whose elements are held at the tower type `t`: the inverse
    of `exitElemTower`. -/
def exitContainer : TowerType → Option TowerType
  | .TFp => some .TFp2
  | .TFp2 => some .TFp6
  | .TFp6 => some .TFp12
  | _ => none

theorem exitElemTower_of_container {t c : TowerType} (h : exitContainer t = some c) :
    exitElemTower c = some t := by
  cases t <;> simp only [exitContainer, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

/-- The marshalling of a scalar word into limb `0` of a tower slot of type `dt` needs a
    slot of at least `8` bytes. -/
def exitMarshalOk (dt : TowerType) : Bool := decide (8 ≤ dt.storageBytes)

/-- The default call tower type of a name that is no array constructor holds a word. -/
theorem exitMarshalOk_of_arrCtorLen {f : String} (h : arrCtorLen f = none) :
    exitMarshalOk (towerOfCallName f) = true := by
  show exitMarshalOk (towerOfCallName_default f) = true
  unfold towerOfCallName_default
  rw [h]
  dsimp only
  (repeat' split) <;> rfl

/-! ## §4  Scalar values -/

/-- Decode a Hax `Value` to a LowCT scalar: `int n` (when `n ≥ 0`),
    the width-indexed `uint _ n`, `bool`, and `unit`.  Signed and array
    values, towers, bytes, tuples and options have no scalar decoding. -/
def valueToScalar : Value → Option Nat
  | .int n => if 0 ≤ n then some n.toNat else none
  | .uint _ n => some n
  | .bool true => some 1
  | .bool false => some 0
  | .unit => some 0
  | _ => none

/-- A scalar value: an unsigned word below `2^64` of any width, a bool, an integer in
    `[0, 2^64)`, or the unit. -/
def ScalarValN : Value → Prop
  | .uint _ n => n < 2 ^ 64
  | .bool _ => True
  | .int n => 0 ≤ n ∧ n < 2 ^ 64
  | .unit => True
  | _ => False

/-- The four shapes of a scalar value. -/
theorem ScalarValN.cases {v : Value} (h : ScalarValN v) :
    (∃ w n, v = .uint w n ∧ n < 2 ^ 64) ∨ (∃ b, v = .bool b) ∨
      (∃ n : Int, v = .int n ∧ 0 ≤ n ∧ n < 2 ^ 64) ∨ v = .unit := by
  match v, h with
  | .uint w n, h => exact Or.inl ⟨w, n, rfl, h⟩
  | .bool b, _ => exact Or.inr (Or.inl ⟨b, rfl⟩)
  | .int n, h => exact Or.inr (Or.inr (Or.inl ⟨n, rfl, h⟩))
  | .unit, _ => exact Or.inr (Or.inr (Or.inr rfl))

/-- `ScalarValN` as a Boolean test. -/
def scalarValNB : Value → Bool
  | .uint _ n => decide (n < 2 ^ 64)
  | .bool _ => true
  | .int n => decide (0 ≤ n) && decide (n < 2 ^ 64)
  | .unit => true
  | _ => false

theorem scalarValNB_iff (v : Value) : scalarValNB v = true ↔ ScalarValN v := by
  cases v <;> simp [scalarValNB, ScalarValN]

/-! ## §5  Reserved and component slot names -/

/-- The function's result slot. -/
def exitResName : String := "__exit_res"

/-- A name is reserved when it starts with `"__exit_"`. -/
def exitReserved (name : String) : Bool := "__exit_".toList.isPrefixOf name.toList

/-- The variable holding field `f` of the flattened struct variable `s`: `s.f`. -/
def structCompName (s f : String) : String := s ++ "." ++ f

end CatCrypt.Crypto.Hax
