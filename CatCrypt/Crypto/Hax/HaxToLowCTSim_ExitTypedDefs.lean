/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit
public import HaxLean.Phase.InlineLocalClosures

/-!
# The exit-flag lowering with one heap per name: definitions

The first of four parts of the typed exit-flag lowering; the overview is the docstring of
`HaxToLowCTSim_ExitTyped.lean`.  This part holds §1–§6: the placements `ExitTowers` and
the reserved tower slots (`exitCallName`, `exitMarshalName`), the scalar operations
(`scalarOpExprT`, `WidthOp`, `widthOpOf`), the heads of a `letBind` (`callMarshal`,
`callHeadAt`, `callHeadT`, `arrLitHeadN`, `letHeadT`), the translator (`haxToLowCTKT`,
`haxToLowCTFnT`, `haxToLowCTFnI`, and the counted loops with bounds read at run time,
`forBoundsV`, `exitForLoopV`), placement inference (`exitTowers`, `exitResultPlace`) and
the fragment (`exitSimOkT`, `exitSimWhyT`, `exitSimWhyT_eq_none_iff`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit IntWidth Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT Located SExpr RustState RustExec LeafSpec rsSetScalar)

/-! ## §1  Placements and reserved tower slots -/

/-- A placement: the names held in the tower heap, each with its tower type.  A name
    absent from the list is held in the scalar heap. -/
abbrev ExitTowers := List (String × TowerType)

/-- The tower slot a call or an element load writes before its result is copied to
    the bound name. -/
def exitCallName : String := "__exit_call"

/-- The tower slot holding the scalar `x` as a call argument. -/
def exitMarshalName (x : String) : String := "__exit_m" ++ x

/-- The slot of component `i` of a function result that is a tuple:
    `"__exit_rc"` followed by `i` bars. -/
def exitResCompName (i : Nat) : String := "__exit_rc" ++ String.ofList (List.replicate i '|')

/-- The placement of a function result: a scalar in the scalar result slot, a tower value
    of type `t` in the tower result slot, a tuple whose component `i` is held in the
    slot `exitResCompName i`, or an `Option` as a tag and a payload. -/
inductive ExitRes where
  | scalar
  | tower (t : TowerType)
  | tuple
  /-- An `Option` whose payload is held under the placement `p`: the tag in the scalar
      result slot, the payload in the slot `exitResCompName 0`. -/
  | option (p : Option TowerType)
  deriving DecidableEq

/-- The result placement of a value held under the placement `p` of a name. -/
def ExitRes.ofPlace : Option TowerType → ExitRes
  | none => .scalar
  | some t => .tower t

/-- The result placement of two tails: the first, except that a first tail `None` takes the
    payload placement of a second tail that is an `Option`. -/
def ExitRes.optJoin : ExitRes → ExitRes → ExitRes
  | .option none, .option p => .option p
  | r, _ => r

/-- The placement is an `Option`. -/
def ExitRes.isOption : ExitRes → Bool
  | .option _ => true
  | _ => false

/-! ## §2  Scalar operations -/

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
    `scalarOpExpr`, their capitalised forms, the Boolean connectives `&&`, `and` as
    `SAnd` and `||`, `or` as `orExprN` (exact on the decodings `0` and `1` of two
    Booleans), and the width-tagged calls of `widthOpOf`. -/
def scalarOpExprT (op : String) (a b : SExpr) : Option SExpr :=
  match op with
  | "lt" | "Lt" => some (.SLt a b)
  | "gt" | "Gt" => some (.SLt b a)
  | "le" | "Le" => some (.SSub (.SLit 1) (.SLt b a))
  | "ge" | "Ge" => some (.SSub (.SLit 1) (.SLt a b))
  | "eq" | "Eq" => some (.SSub (.SSub (.SLit 1) (.SLt a b)) (.SLt b a))
  | "ne" | "Ne" => some (.SAdd (.SLt a b) (.SLt b a))
  | "add" | "Add" => some (.SAdd a b)
  | "sub" | "Sub" => some (.SSub a b)
  | "&&" | "and" => some (.SAnd a b)
  | "||" | "or" => some (orExprN a b)
  | _ => (widthOpOf op).map fun p => p.2.sexpr p.1 a b

/-- The call names whose result is a scalar besides the width-tagged ones. -/
def exitScalarCalls : List String :=
  ["len", "lt", "gt", "le", "ge", "eq", "ne", "add", "sub",
   "Lt", "Gt", "Le", "Ge", "Eq", "Ne", "Add", "Sub", "Mul", "Div", "Rem",
   "BitAnd", "BitOr", "BitXor", "Shl", "Shr", "Not", "Neg", "&&", "||", "and", "or"]

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

/-- A call name the typed lowering admits: every name except a wide field head, a tagged
    field head `m#p` (`Hax.FieldTag.fieldTag?`) at a modulus `p ≥ 2^64`, whose operands and
    result `Hax.FieldTag.fieldCall` holds as arrays of `Hax.FieldTag.fieldLimbs p` limbs. -/
def exitAdmits (f : String) : Bool :=
  match _root_.Hax.FieldTag.fieldTag? f with
  | some (_, p) => decide (p < 2 ^ 64)
  | none => true

/-- A name without `#` is admitted: it is no tagged field head. -/
theorem exitAdmits_of_not_hash {f : String} (h : f.contains '#' = false) :
    exitAdmits f = true := by
  unfold exitAdmits
  rcases ht : _root_.Hax.FieldTag.fieldTag? f with _ | ⟨m, p⟩
  · rfl
  · have hm := _root_.Hax.FieldTag.mem_toList_of_fieldTag? ht
    simp [String.contains_char_eq, hm] at h

/-- A call outside `exitScalarRes` is admitted: a tagged field head contains `#` and is a
    scalar call. -/
theorem exitAdmits_of_scalarRes_false {f : String} (h : exitScalarRes f = false) :
    exitAdmits f = true := by
  apply exitAdmits_of_not_hash
  simp only [exitScalarRes, exitScalarCall, Bool.or_eq_false_iff] at h
  exact h.1.2

theorem exitScalarRes_index : exitScalarRes "index" = false := by
  simp [exitScalarRes, exitScalarCall, exitScalarCalls, exitTowerScalarCall, exitTowerScalarNames]

theorem exitScalarRes_arrayLit : exitScalarRes "array_lit" = false := by
  simp [exitScalarRes, exitScalarCall, exitScalarCalls, exitTowerScalarCall, exitTowerScalarNames]

/-! ## §3  The heads of a `letBind` -/

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

/-- The type of the elements an element store writes into an array held at `t`: the
    element tower type of `exitElemTower`, and `t.elemType` for an array of words. -/
def exitElem (t : TowerType) : TowerType := (exitElemTower t).getD t.elemType

/-- The marshalling of a scalar word into limb `0` of a tower slot of type `dt` needs a
    slot of at least `8` bytes. -/
def exitMarshalOk (dt : TowerType) : Bool := decide (8 ≤ dt.storageBytes)

/-- The argument slots of a call, and the context storing its scalar arguments: an
    argument held in a tower is read in place at its tower type; a scalar argument `x` is
    stored into limb `0` of the fresh tower slot `exitMarshalName x` of type `dt`, which
    `exitMarshalOk dt` requires to hold a word.  `none` when an argument is not a
    variable. -/
def callMarshal (A : ExitTowers) (dt : TowerType) :
    List ImpExpr → Option ((LowCT → LowCT) × List Located)
  | [] => some (id, [])
  | .var x :: as =>
      match callMarshal A dt as with
      | none => none
      | some (ctx, ls) =>
        match A.lookup x with
        | some t => some (ctx, ⟨x, t⟩ :: ls)
        | none =>
          if exitMarshalOk dt then
            some (fun c => .RLetZero (exitMarshalName x) dt
              (.RSeq (.RLimbStoreExpr ⟨exitMarshalName x, dt⟩ 0 (.SVar x)) (ctx c)),
              ⟨exitMarshalName x, dt⟩ :: ls)
          else none
  | _ :: _ => none

/-- The `SExpr` of a scalar operation `f` on two scalar variables bound to a scalar
    name `n`. -/
def scalarOpHeadT (A : ExitTowers) (n f : String) : List ImpExpr → Option SExpr
  | [.var a, .var b] =>
      if A.lookup n = none ∧ A.lookup a = none ∧ A.lookup b = none then
        scalarOpExprT f (.SVar a) (.SVar b)
      else none
  | _ => none

/-- The head of `let n = index(arr, idx)` with `arr` in a tower at `t` and `idx` scalar.
    For an array of words (`exitElemTower t = none`) and a scalar `n`: load the element
    into `exitCallName` and copy its limb `0` into `n`.  For an array of tower values of
    type `t'` (`exitElemTower t = some t'`) and `n` placed at `t'`: load the element into
    `exitCallName` at `t'` and copy it into the tower slot `n`. -/
def indexHeadT (A : ExitTowers) (n : String) : List ImpExpr → Option (LowCT → LowCT)
  | [.var arr, .var idx] =>
      match A.lookup arr with
      | some t =>
          if A.lookup idx = none then
            match exitElemTower t with
            | none =>
                if A.lookup n = none then
                  some fun b => .RLetZero exitCallName .TFp
                    (.RSeq (.RArrLoad ⟨exitCallName, .TFp⟩ ⟨arr, t⟩ idx)
                      (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b))
                else none
            | some t' =>
                if A.lookup n = some t' then
                  some fun b => .RLetZero exitCallName t'
                    (.RSeq (.RArrLoad ⟨exitCallName, t'⟩ ⟨arr, t⟩ idx)
                      (.RSeq (.RCopy ⟨n, t'⟩ ⟨exitCallName, t'⟩) b))
                else none
          else none
      | none => none
  | _ => none

/-- The head of `let arr = array_update(arr, idx, src)` with `arr` in a tower of type
    `t` and `idx` scalar: store `src` at element `idx` of `arr`.  For an array of words
    (`exitElemTower t = none`), `src` is scalar and is marshalled at `t.elemType`; for an
    array of tower values of type `t'`, `src` is held at `t'` or is a scalar marshalled at
    `t'`. -/
def updateHeadT (A : ExitTowers) (n : String) : List ImpExpr → Option (LowCT → LowCT)
  | [.var arr, .var idx, .var src] =>
      match A.lookup arr with
      | some t =>
          if n = arr ∧ A.lookup idx = none ∧
              ((exitElemTower t).isNone → A.lookup src = none) then
            match callMarshal A (exitElem t) [.var src] with
            | some (ctx, [srcLoc]) =>
                if srcLoc.locSrc = exitElem t then
                  some fun b => .RSeq (ctx (.RArrStore ⟨arr, t⟩ idx srcLoc)) b
                else none
            | _ => none
          else none
      | none => none
  | _ => none

/-- The head of `let n = f(args)` for a call lowered to `RCall` whose scalar arguments are
    marshalled at the tower type `dt` and whose result slot has the tower type `dr`: the
    call writes `exitCallName` at `dr` from the slots of `callMarshal A dt`; for a scalar
    `n` its limb `0` is copied into the scalar slot `n`, for `n` placed at `dr` it is
    copied into the tower slot `n`. -/
def callHeadAt (A : ExitTowers) (n f : String) (dt dr : TowerType) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  match callMarshal A dt args with
  | none => none
  | some (ctx, ls) =>
    let callC : LowCT := .RLetZero exitCallName dr (ctx (.RCall f ⟨exitCallName, dr⟩ ls))
    match A.lookup n with
    | none => some fun b => .RSeq callC (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b)
    | some t =>
      if t = dr then some fun b => .RSeq callC (.RSeq (.RCopy ⟨n, dr⟩ ⟨exitCallName, dr⟩) b)
      else none

/-- The reserved name under which a placement records the declared result type of the
    calls of `f`. -/
def exitCallKey (f : String) : String := "__exit_ty:" ++ f

/-- The reserved name under which a placement records the payload placement of the calls
    of `f` returning an `Option`. -/
def exitOptKey (f : String) : String := "__exit_ty;" ++ f

/-- A name of the form `exitCallKey f` or `exitOptKey f`. -/
def exitIsCallKey (s : String) : Bool := "__exit_ty".toList.isPrefixOf s.toList

/-- The declared result types of the calls recorded in the placement `A`: the type at
    `exitCallKey f`.  A declared result of the word type `TU64` is a scalar word. -/
def exitCallTys (A : ExitTowers) (f : String) : Option TowerType := A.lookup (exitCallKey f)

/-- The declared payload placements of the calls returning an `Option` recorded in the
    placement `A`: the type at `exitOptKey f`, the word type `TU64` for a scalar payload. -/
def exitOptTys (A : ExitTowers) (f : String) : Option TowerType := A.lookup (exitOptKey f)

/-- The reserved name under which a placement records the result type of a linked callee
    `f`. -/
def exitCalleeKey (f : String) : String := "__exit_ty!" ++ f

/-- The reserved name under which a placement records the slot type of argument `i` of a
    linked callee `f`. -/
def exitArgKey (f : String) (i : Nat) : String := "__exit_ty?" ++ (toString i ++ "!" ++ f)

/-- The slot types recorded in `A` for the arguments `i, i + 1, …` of `f`, up to the first
    argument without one, at most `fuel` of them. -/
def exitArgTys (A : ExitTowers) (f : String) : Nat → Nat → List TowerType
  | 0, _ => []
  | fuel + 1, i =>
      match A.lookup (exitArgKey f i) with
      | some t => t :: exitArgTys A f fuel (i + 1)
      | none => []

/-- The largest number of arguments of a linked callee `exitCalleeTys` reads. -/
def exitArgMax : Nat := 64

/-- The argument slot types and the result type of a linked callee `f` recorded in the
    placement `A`: the type at `exitCalleeKey f`, and the types at `exitArgKey f i` for the
    first arguments with one, at most `exitArgMax` of them. -/
def exitCalleeTys (A : ExitTowers) (f : String) : Option (List TowerType × TowerType) :=
  (A.lookup (exitCalleeKey f)).map fun dr => (exitArgTys A f exitArgMax 0, dr)

/-- The head of a call.  A call of `exitScalarRes` with an admitted name (`exitAdmits`)
    bound to a scalar name runs at its tower type `towerOfCallName f`.  A call of a linked callee with argument slot types `ts` and
    result type `dr` (`exitCalleeTys A f`), declaring no other type, runs at `dr` when its
    argument slots, the scalar arguments marshalled at `TU64`, have the types `ts`.  A call
    with a declared result type `dr` (`exitCallTys A f`) runs at `dr`, its scalar arguments
    marshalled at `TU64`.  In both cases its result is copied into the tower slot of a name
    placed at `dr`, or, for `dr = TU64`, from limb `0` into the scalar slot of a scalar
    name.  A call without a declared result type runs at `towerOfCallName f` into a name
    placed there. -/
def callHeadT (A : ExitTowers) (n f : String) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  if exitScalarRes f then
    if A.lookup n = none ∧ exitAdmits f = true then
      callHeadAt A n f (towerOfCallName f) (towerOfCallName f) args
    else none
  else
    match exitCalleeTys A f with
    | some (ts, dr) =>
        if (exitCallTys A f).isSome ∨ (exitOptTys A f).isSome ∨
            (A.lookup n = none ∧ dr ≠ .TU64) ∨
            (callMarshal A .TU64 args).map (fun cl => cl.2.map (·.locDst)) ≠ some ts then none
        else callHeadAt A n f .TU64 dr args
    | none =>
    match exitCallTys A f with
    | some dr =>
        if (exitOptTys A f).isSome ∨ (A.lookup n = none ∧ dr ≠ .TU64) then none
        else callHeadAt A n f .TU64 dr args
    | none =>
        if A.lookup n = some (towerOfCallName f) then
          callHeadAt A n f (towerOfCallName f) (towerOfCallName f) args
        else none

/-- The tower type of the first argument held in a tower. -/
def exitFirstTower (A : ExitTowers) : List ImpExpr → Option TowerType
  | [] => none
  | .var x :: as =>
      match A.lookup x with
      | some t => some t
      | none => exitFirstTower A as
  | _ :: as => exitFirstTower A as

/-- The number of elements of an array type: `n` for `TArr n t`, and `2`, `3`, `2` for the
    containers `TFp2`, `TFp6`, `TFp12` of `exitContainer`. -/
def exitArrLen : TowerType → Option Nat
  | .TArr n _ => some n
  | .TFp2 => some 2
  | .TFp6 => some 3
  | .TFp12 => some 2
  | _ => none

/-- Every argument variable held in a tower is placed at `dt`. -/
def exitArgsAt (A : ExitTowers) (dt : TowerType) (args : List ImpExpr) : Bool :=
  args.all fun a =>
    match a with
    | .var x =>
        match A.lookup x with
        | some t => decide (t = dt)
        | none => true
    | _ => true

/-- The head of `let n = array_lit(args)` with `n` placed at an array type `c` of
    `args.length` elements (`exitArrLen`) whose element type holds a word (`exitMarshalOk`),
    and every argument held in a tower placed at the element type `exitElem c`
    (`exitArgsAt`): the scalar arguments are marshalled at `exitElem c`, the result is held
    at `c`. -/
def arrLitHeadN (A : ExitTowers) (n : String) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  match A.lookup n with
  | some c =>
      -- On the Bls, plonky3, Libcrux_specs and Mldsa extractions every tower argument of
      -- an array literal is placed at `exitElem c`, so `exitArgsAt` refuses no site there.
      if exitArrLen c = some args.length ∧ exitMarshalOk (exitElem c) = true ∧
          exitArgsAt A (exitElem c) args = true then
        callHeadAt A n "array_lit" (exitElem c) c args
      else none
  | none => none

/-- The head of `let n = repeat(v, l)` with a literal count `l` decoding to `k` and `n`
    placed at an array type `c` of `k` elements (`exitArrLen`) whose element type holds a
    word: the call reads only `v`, marshalled at the element type `exitElem c` when
    scalar, and writes its result at `c`. -/
def repeatHeadT (A : ExitTowers) (n : String) : List ImpExpr → Option (LowCT → LowCT)
  | [.var v, .lit l] =>
      match A.lookup n, valueToScalar (Value.ofLit l) with
      | some c, some k =>
          if exitArrLen c = some k ∧ exitMarshalOk (exitElem c) = true then
            callHeadAt A n "repeat" (exitElem c) c [.var v]
          else none
      | _, _ => none
  | _ => none

/-- The head of `let n = f(args)`: a scalar operation, an element load, an element
    store, an array literal at the placed array type of its bound name (`arrLitHeadN`), a
    `repeat` with a literal count at the placed array type of its bound name
    (`repeatHeadT`), or a call. -/
def appHeadT (A : ExitTowers) (n f : String) (args : List ImpExpr) :
    Option (LowCT → LowCT) :=
  match scalarOpHeadT A n f args with
  | some se => some fun b => .RSeq (.RScalarSetExpr n se) b
  | none =>
    if f = "index" then indexHeadT A n args
    else if f = "array_update" then updateHeadT A n args
    else if f = "array_lit" then arrLitHeadN A n args
    else if f = "repeat" then repeatHeadT A n args
    else callHeadT A n f args

/-- The head of `let n = val` under the placement `A`: a literal bound to a scalar
    name as in `letHead`; a literal bound to a name placed in a tower at `t` with
    `exitMarshalOk t` as the zero slot of type `t` with the literal's word stored into its
    limb `0`; a copy between two scalar names as in `letHead`, between two tower names of
    one type by `RCopy`; a call by `appHeadT`. -/
def letHeadT (A : ExitTowers) (n : String) : ImpExpr → Option (LowCT → LowCT)
  | .lit l =>
      match A.lookup n with
      | none => letHead n (.lit l)
      | some t =>
          if exitMarshalOk t then
            (valueToScalar (Value.ofLit l)).map fun kk b =>
              .RLetZero n t (.RSeq (.RLimbStoreExpr ⟨n, t⟩ 0 (.SLit kk)) b)
          else none
  | .var s =>
      match A.lookup n, A.lookup s with
      | none, none => letHead n (.var s)
      | some t, some t' =>
          if t = t' then
            if n = s then some id
            else some fun b => .RSeq (.RCopy ⟨n, t⟩ ⟨s, t⟩) b
          else none
      | _, _ => none
  | .app f args => appHeadT A n f args
  | _ => none

/-! ## §4  The translator -/

/-- The stores of the components of a tuple of variables from component `i` on: the
    variable of component `i` copied into the slot `exitResCompName i`, in the scalar heap
    or at its tower type.  `none` when a component is not a variable. -/
def tupleStoreT (A : ExitTowers) : Nat → List ImpExpr → Option LowCT
  | _, [] => some .RSkip
  | i, .var x :: es => (tupleStoreT A (i + 1) es).map fun rest =>
      match A.lookup x with
      | none => .RSeq (.RScalarSetExpr (exitResCompName i) (.SVar x)) rest
      | some t => .RSeq (.RCopy ⟨exitResCompName i, t⟩ ⟨x, t⟩) rest
  | _, _ :: _ => none

/-- The lowered tail value `e`: a scalar value stored into the scalar result slot as
    by `resultStore`, a tower variable copied into the tower slot `exitResName`, a tuple
    of variables stored component by component (`tupleStoreT`). -/
def resultStoreT (A : ExitTowers) : ImpExpr → Option LowCT
  | .var x =>
      match A.lookup x with
      | some t => some (.RCopy ⟨exitResName, t⟩ ⟨x, t⟩)
      | none => resultStore (.var x)
  | .tuple es => tupleStoreT A 0 es
  | .app "None" [] => some (.RScalarSet exitResName 0)
  | .app "Some" [.var x] =>
      some (.RSeq (match A.lookup x with
        | none => .RScalarSetExpr (exitResCompName 0) (.SVar x)
        | some t => .RCopy ⟨exitResCompName 0, t⟩ ⟨x, t⟩) (.RScalarSet exitResName 1))
  | e => resultStore e

/-- The tail stores of `resultStoreT` at a call: `None()`, `Some(x)`, and otherwise the
    store of `resultStore`. -/
theorem resultStoreT_app_cases (A : ExitTowers) {f : String} {args : List ImpExpr}
    {s : LowCT} (h : resultStoreT A (.app f args) = some s) :
    (f = "None" ∧ args = [] ∧ s = .RScalarSet exitResName 0) ∨
      (∃ x, f = "Some" ∧ args = [.var x] ∧
        s = .RSeq (match A.lookup x with
          | none => .RScalarSetExpr (exitResCompName 0) (.SVar x)
          | some t => .RCopy ⟨exitResCompName 0, t⟩ ⟨x, t⟩) (.RScalarSet exitResName 1)) ∨
      resultStore (.app f args) = some s := by
  unfold resultStoreT at h
  split at h
  · simp_all
  · simp_all
  · rename_i heq
    obtain ⟨rfl, rfl⟩ := ImpExpr.app.inj heq
    exact Or.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩
  · rename_i heq
    obtain ⟨rfl, rfl⟩ := ImpExpr.app.inj heq
    exact Or.inr (Or.inl ⟨_, rfl, rfl, (Option.some.inj h).symm⟩)
  · exact Or.inr (Or.inr h)

/-- The reserved tower slot receiving the tag of a call returning an `Option`. -/
def exitOptTagName : String := "__exit_otag"

/-- The reserved tower slot receiving the payload of a call returning an `Option`. -/
def exitOptPayName : String := "__exit_opay"

/-- The reserved scalar slot holding the tag of a call returning an `Option`. -/
def exitOptTagS : String := "__exit_otags"

/-- The call and the payload binding of `match f(args) [Some p => … | None => …]` for a call
    `f` with the declared `Option` payload type `t` (`exitOptTys`): the two-output call
    `RCallN f [tag, payload]` on the slots of `callMarshal A TU64 args`, the tag copied from
    limb `0` into the scalar slot `exitOptTagS`, and the binding of `p` to the payload: from
    limb `0` for a scalar `p` and `t = TU64`, by `RCopy` for `p` placed at `t ≠ TU64`. -/
def optHeadT (A : ExitTowers) (f : String) (args : List ImpExpr) (p : String) :
    Option (LowCT × LowCT) :=
  if exitScalarRes f || f == "index" || f == "array_update" || f == "array_lit" ||
      f == "repeat" then none
  else
  match exitOptTys A f with
  | none => none
  | some t =>
    match callMarshal A .TU64 args with
    | none => none
    | some (ctx, ls) =>
      let callC : LowCT := .RSeq (.RLetZero exitOptTagName .TU64 (.RLetZero exitOptPayName t
        (ctx (.RCallN f [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩] ls))))
        (.RScalarSetExpr exitOptTagS (.SLimb exitOptTagName 0))
      match A.lookup p with
      | none =>
          if t = .TU64 then some (callC, .RScalarSetExpr p (.SLimb exitOptPayName 0)) else none
      | some tp =>
          if tp = t ∧ t ≠ .TU64 then some (callC, .RCopy ⟨p, t⟩ ⟨exitOptPayName, t⟩) else none

/-- `x` is held in the scalar heap under `A`. -/
def exitSc (A : ExitTowers) (x : String) : Bool := (A.lookup x).isNone

/-- A variable `e` is held in the scalar heap under `A`; any other expression passes. -/
def exitScE (A : ExitTowers) : ImpExpr → Bool
  | .var x => exitSc A x
  | _ => true

/-- The runtime upper bound of a counted loop (`forBoundsRt lo hi`), if any, is held in
    the scalar heap under `A`. -/
def exitScRt (A : ExitTowers) (lo hi : ImpExpr) : Bool :=
  match forBoundsRt lo hi with
  | some (_, h) => exitSc A h
  | none => true

/-- A literal whose value is a scalar word: an unsigned literal of width at most `64`,
    an integer in `[0, 2^64)`, a bool or the unit. -/
def exitLitOk : ImpLit → Bool
  | .uintLit w _ => w != .w128
  | .int k => decide (0 ≤ k) && decide (k < 2 ^ 64)
  | .bool _ => true
  | .unit => true
  | _ => false

/-- The scalar expression of a counted-loop bound read from the scalar heap under `A`: a
    literal of `exitLitOk`, a non-reserved variable held in the scalar heap, or a scalar
    operation of `scalarOpExprT` on two such bounds. -/
def boundSE (A : ExitTowers) : ImpExpr → Option SExpr
  | .lit l => if exitLitOk l then (valueToScalar (Value.ofLit l)).map .SLit else none
  | .var x => if !exitReserved x && exitSc A x then some (.SVar x) else none
  | .app op [a, b] =>
      match boundSE A a, boundSE A b with
      | some sa, some sb => scalarOpExprT op sa sb
      | _, _ => none
  | _ => none

/-- The lower bound of a counted loop with counter `i` and body `body` read at run time:
    `boundSE` of a literal, or of a variable other than `i` that `body` does not bind
    (`frameOk`), so that the variable holds the bound on every trip. -/
def loBoundSE (A : ExitTowers) (i : String) (body : ImpExpr) : ImpExpr → Option SExpr
  | .lit l => boundSE A (.lit l)
  | .var x =>
      if x != i && _root_.Hax.InlineLocalClosures.frameOk (fun _ => true) (fun n => n != x)
          (fun _ => true) body then boundSE A (.var x)
      else none
  | _ => none

/-- The bounds of a counted loop that the typed lowering reads at run time: `loBoundSE` of
    the lower bound and `boundSE` of the upper bound. -/
def forBoundsV (A : ExitTowers) (i : String) (body lo hi : ImpExpr) :
    Option (SExpr × SExpr) :=
  match loBoundSE A i body lo, boundSE A hi with
  | some l, some h => some (l, h)
  | _, _ => none

theorem forBoundsV_some {A : ExitTowers} {i : String} {body lo hi : ImpExpr} {l h : SExpr}
    (hb : forBoundsV A i body lo hi = some (l, h)) :
    loBoundSE A i body lo = some l ∧ boundSE A hi = some h := by
  unfold forBoundsV at hb
  split at hb
  · simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rename_i h1 h2
    exact ⟨h1, h2⟩
  · cases hb

/-- One trip of a counted loop whose lower bound is the scalar expression `lo`: as
    `exitForTrip`, with the counter `i` bound to `run + lo`. -/
def exitForTripV (run i : String) (lo : SExpr) (bC : LowCT) : LowCT :=
  exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i (.SAdd (.SVar run) lo)) bC))

/-- The lowered counted loop with the bounds `lo` and `hi` read at run time: zero the flag
    and the payload slot, and run `hi - lo` trips of `exitForTripV`, the trip count read
    on entry (`RForRuntime`). -/
def exitForLoopV (run i : String) (lo hi : SExpr) (bC : LowCT) : LowCT :=
  .RLetU64Zero exitRetName (.RLetU64Zero exitValName
    (.RForRuntime run (.SSub hi lo) (exitForTripV run i lo bC)))

/-- The statements `haxToLowCTKT` lowers outside tail position by `haxToLowCT`: a
    variable and the unit, both lowered to `RSkip`. -/
def exitStmtOk : ImpExpr → Bool
  | .var _ => true
  | .unitVal => true
  | _ => false

/-- The exit-flag lowering under the placement `A`: `haxToLowCTK true` with the heads
    of `letHeadT A`, the tail store `resultStoreT A`, and, in an exit context, every
    counted loop with the bounds of `forBounds`, `forBoundsRt` or, read at run time,
    `forBoundsV` (`exitForLoopV`), every downward counted
    loop with the bounds of `forBounds`, and every `while` loop on a variable lowered to
    the exit-flag loop followed by `breakLoop`.  Every name the lowering reads from the
    scalar heap is placed there: the guard of a conditional or of a `while` loop, the
    counter and the runtime bound of a counted loop, and a variable `break` payload are
    refused when `A` places them in a tower (`exitSc`, `exitScE`, `exitScRt`); outside
    tail position only a variable or the unit is lowered by `haxToLowCT`
    (`exitStmtOk`). -/
def haxToLowCTKT (A : ExitTowers) : Bool → Option String → ImpExpr → Option (LowCT × Bool)
  | tl, fl, .letBind name val body =>
      match letHeadT A name val, haxToLowCTKT A tl fl body with
      | some k, some (bC, x) => some (k bC, x)
      | _, _ => none
  | tl, fl, .seq a b =>
      match haxToLowCTKT A false fl a, haxToLowCTKT A tl fl b with
      | some (aC, xa), some (bC, xb) =>
          some (if xa then .RSeq aC (exitGuard bC) else .RSeq aC bC, xa || xb)
      | _, _ => none
  | tl, fl, .ifThenElse (.var v) t e =>
      if exitSc A v then
        match haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
        | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
        | _, _ => none
      else none
  | tl, fl, .typeAscription e _ => haxToLowCTKT A tl fl e
  | tl, fl, .match_ (.app f args) [(.somePat (.varPat p), t), (.nonePat, e)] =>
      match optHeadT A f args p, haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (callC, bindP), some (tC, xt), some (eC, xe) =>
          some (.RSeq callC (.RIfNz exitOptTagS (.RSeq bindP tC) eC), xt || xe)
      | _, _, _ => none
  | tl, fl, .match_ (.app f args) [(.nonePat, e), (.somePat (.varPat p), t)] =>
      match optHeadT A f args p, haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (callC, bindP), some (tC, xt), some (eC, xe) =>
          some (.RSeq callC (.RIfNz exitOptTagS (.RSeq bindP tC) eC), xt || xe)
      | _, _, _ => none
  | false, fl, .whileFoldReturn (.var c) body =>
      if exitSc A c then
        match haxToLowCTKT A false (some (exitRunName fl)) body with
        | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
        | none => none
      else none
  | false, fl, .forFoldReturn i lo hi body =>
      if exitSc A i && exitScRt A lo hi then
        match forBounds lo hi, forBoundsRt lo hi,
            haxToLowCTKT A false (some (exitRunName fl)) body with
        | some (l, h), _, some (bC, _) => some (exitForLoop (exitRunName fl) i l h bC, true)
        | none, some (l, h), some (bC, _) =>
            some (exitForLoopRt (exitRunName fl) i l h bC, true)
        | none, none, some (bC, _) =>
            (forBoundsV A i body lo hi).map fun p =>
              (exitForLoopV (exitRunName fl) i p.1 p.2 bC, true)
        | _, _, _ => none
      else none
  | false, fl, .forFoldRevReturn i lo hi body =>
      if exitSc A i then
        match forBounds lo hi, haxToLowCTKT A false (some (exitRunName fl)) body with
        | some (l, h), some (bC, _) => some (exitForLoopRev (exitRunName fl) i l h bC, true)
        | _, _ => none
      else none
  | false, some r, .forFold i lo hi body =>
      if exitSc A i && exitScRt A lo hi then
        match forBounds lo hi, forBoundsRt lo hi,
            haxToLowCTKT A false (some (exitRunName (some r))) body with
        | some (l, h), _, some (bC, _) =>
            some (breakLoop (exitForLoop (exitRunName (some r)) i l h bC), false)
        | none, some (l, h), some (bC, _) =>
            some (breakLoop (exitForLoopRt (exitRunName (some r)) i l h bC), false)
        | none, none, some (bC, _) =>
            (forBoundsV A i body lo hi).map fun p =>
              (breakLoop (exitForLoopV (exitRunName (some r)) i p.1 p.2 bC), false)
        | _, _, _ => none
      else none
  | false, some r, .forFoldRev i lo hi body =>
      if exitSc A i then
        match forBounds lo hi, haxToLowCTKT A false (some (exitRunName (some r))) body with
        | some (l, h), some (bC, _) =>
            some (breakLoop (exitForLoopRev (exitRunName (some r)) i l h bC), false)
        | _, _ => none
      else none
  | false, some r, .whileFold (.var c) body =>
      if exitSc A c then
        match haxToLowCTKT A false (some (exitRunName (some r))) body with
        | some (bC, _) => some (breakLoop (exitLoop (exitRunName (some r)) c bC), false)
        | none => none
      else none
  | _, some _, .cfBreak e =>
      if exitScE A e then (exitStore e).map fun s => (s, true) else none
  | true, _, e => (resultStoreT A e).map fun s => (s, false)
  | false, _, e => if exitStmtOk e then (haxToLowCT e).map fun c => (c, false) else none

/-- The lowering of a function body under the placement `A`: `haxToLowCTKT A` in tail
    position in the function context, inside the frame `exitFunction`. -/
def haxToLowCTFnT (A : ExitTowers) (e : ImpExpr) : Option LowCT :=
  (haxToLowCTKT A true (some exitFnSlot) e).map fun p => exitFunction p.1

/-! ## §5  Placement inference -/

/-- The variables of an argument list. -/
def exitArgNames : List ImpExpr → List String
  | [] => []
  | .var x :: as => x :: exitArgNames as
  | _ :: as => exitArgNames as

/-- The names a body binds by a call with a tower result: a call other than a call of
    `exitScalarRes`, `index`, `array_update` and `len`. -/
def exitTowerBound : ImpExpr → List String
  | .letBind n v b =>
      let here := match v with
        | .app f _ =>
            if exitScalarRes f || f = "index" || f = "array_update" || f = "len" then []
            else [n]
        | _ => []
      here ++ exitTowerBound b
  | .seq a b => exitTowerBound a ++ exitTowerBound b
  | .ifThenElse _ t e => exitTowerBound t ++ exitTowerBound e
  | .typeAscription e _ => exitTowerBound e
  | .whileFoldReturn _ b => exitTowerBound b
  | .forFoldReturn _ _ _ b => exitTowerBound b
  | .forFoldRevReturn _ _ _ b => exitTowerBound b
  | .forFold _ _ _ b => exitTowerBound b
  | .forFoldRev _ _ _ b => exitTowerBound b
  | .whileFold _ b => exitTowerBound b
  | _ => []

/-- The `letBind`s of a body at statement positions and in loop bodies, in order. -/
def exitBinds : ImpExpr → List (String × ImpExpr)
  | .letBind n v b => (n, v) :: exitBinds b
  | .seq a b => exitBinds a ++ exitBinds b
  | .ifThenElse _ t e => exitBinds t ++ exitBinds e
  | .typeAscription e _ => exitBinds e
  | .whileFoldReturn _ b => exitBinds b
  | .forFoldReturn _ _ _ b => exitBinds b
  | .forFoldRevReturn _ _ _ b => exitBinds b
  | .forFold _ _ _ b => exitBinds b
  | .forFoldRev _ _ _ b => exitBinds b
  | .whileFold _ b => exitBinds b
  | _ => []

/-- A call on field elements: a name with the prefix `fp_`, `fp2_`, `fp6_` or `fp12_`,
    whose arguments and result are tower values. -/
def exitFieldCall (f : String) : Bool :=
  f.startsWith "fp_" || f.startsWith "fp2_" || f.startsWith "fp6_" || f.startsWith "fp12_"

/-- The names one binding shows to hold tower values, given the names `T` known to: the
    array argument of `index`, `len` and `array_update` and the result of `array_update`;
    the stored value of `array_update` when it is in `T`; the arguments and the result of
    an `array_lit` with an argument in `T`; the arguments of a leaf of
    `exitTowerScalarNames`; the arguments and the result of a call of `exitFieldCall`;
    both sides of a copy with a side in `T`. -/
def exitTowerUse (T : List String) : String × ImpExpr → List String
  | (n, .app f args) =>
      if f = "index" ∨ f = "len" then
        match args with
        | .var a :: _ => [a]
        | _ => []
      else if f = "array_update" then
        match args with
        | [.var a, _, .var s] => a :: n :: (if T.contains s then [s] else [])
        | _ => []
      else if f = "array_lit" then
        if (exitArgNames args).any T.contains then n :: exitArgNames args else []
      else if exitTowerScalarCall f then exitArgNames args
      else if exitFieldCall f then n :: exitArgNames args
      else []
  | (n, .var s) => if T.contains n || T.contains s then [n, s] else []
  | _ => []

/-- The arrays one binding shows to hold tower values, given the names `T` holding tower
    values: the array of an element load bound to a name in `T`, and the array of an
    element store of a value in `T`. -/
def exitContainerUse (T : List String) : String × ImpExpr → List String
  | (n, .app "index" (.var a :: _)) => if T.contains n then [a] else []
  | (_, .app "array_update" [.var a, _, .var s]) => if T.contains s then [a] else []
  | _ => []

/-- The element loads from an array of `C`. -/
def exitElemUse (C : List String) : String × ImpExpr → List String
  | (n, .app "index" (.var a :: _)) => if C.contains a then [n] else []
  | _ => []

/-- `k` rounds of the closure of the names holding tower values over the bindings `bs`,
    from `T`: `exitTowerUse`, the arrays of `exitContainerUse`, and their element loads. -/
def exitTowerNamesAux (bs : List (String × ImpExpr)) : Nat → List String → List String
  | 0, T => T
  | k + 1, T =>
      let C := bs.flatMap (exitContainerUse T)
      exitTowerNamesAux bs k (T ++ bs.flatMap (exitTowerUse T) ++ C ++ bs.flatMap (exitElemUse C))

/-- The names of a body holding tower values: six rounds of `exitTowerNamesAux`. -/
def exitTowerNames (e : ImpExpr) : List String :=
  let bs := exitBinds e
  exitTowerNamesAux bs 6 (bs.flatMap (exitTowerUse []))

/-- The names a body binds or reads as scalars, given the names `tb` bound by a call with
    a tower result and the names `tu` holding tower values: literal bindings of a name
    outside `tb`, results of calls of `exitScalarRes`, element loads bound to a name
    outside `tu`, loop counters and bounds, and conditions. -/
def exitScalarNames (tb tu : List String) : ImpExpr → List String
  | .letBind n v b =>
      let here := match v with
        | .lit _ => if tb.contains n then [] else [n]
        | .app f _ =>
            if exitScalarRes f then [n] else if f = "index" && !tu.contains n then [n] else []
        | _ => []
      here ++ exitScalarNames tb tu b
  | .seq a b => exitScalarNames tb tu a ++ exitScalarNames tb tu b
  | .ifThenElse (.var c) t e => c :: (exitScalarNames tb tu t ++ exitScalarNames tb tu e)
  | .ifThenElse _ t e => exitScalarNames tb tu t ++ exitScalarNames tb tu e
  | .typeAscription e _ => exitScalarNames tb tu e
  | .whileFoldReturn (.var c) b => c :: exitScalarNames tb tu b
  | .forFoldReturn i _ (.var h) b => i :: h :: exitScalarNames tb tu b
  | .forFoldReturn i _ _ b => i :: exitScalarNames tb tu b
  | .forFoldRevReturn i _ _ b => i :: exitScalarNames tb tu b
  | .forFold i _ (.var h) b => i :: h :: exitScalarNames tb tu b
  | .forFold i _ _ b => i :: exitScalarNames tb tu b
  | .forFoldRev i _ _ b => i :: exitScalarNames tb tu b
  | .whileFold (.var c) b => c :: exitScalarNames tb tu b
  | .whileFold _ b => exitScalarNames tb tu b
  | _ => []

/-- `(x, t) :: A` when `x` is neither placed in `A` nor a scalar name of `sc`. -/
def exitPlaceAt (sc : List String) (A : ExitTowers) (x : String) (t : TowerType) :
    ExitTowers :=
  if (A.lookup x).isNone && !sc.contains x then (x, t) :: A else A

/-- The count `k > 0` of the arguments `[v, l]` of `repeat(v, l)` with a scalar name `v` of
    `sc` and a literal count `l` decoding to `k`. -/
def exitRepeatWords (sc : List String) : List ImpExpr → Option Nat
  | [.var v, .lit l] =>
      match valueToScalar (Value.ofLit l) with
      | some k => if sc.contains v && 0 < k then some k else none
      | none => none
  | _ => none

/-- The number `k > 0` of the arguments of an `array_lit` whose arguments are all scalar
    names of `sc`. -/
def exitLitWords (sc : List String) (args : List ImpExpr) : Option Nat :=
  let xs := exitArgNames args
  if 0 < args.length && xs.length = args.length && xs.all sc.contains then some args.length
  else none

/-- One step of placement inference at a binding, from the scalar names `sc`.  An element
    load placed at `t'` places its array at `exitContainer t'`; an element store of a
    value placed at `t'` places its array at `exitContainer t'`; an `array_lit` with an
    argument placed at `t'` places its arguments at `t'` and its result at
    `exitContainer t'`; a `repeat` of a scalar name with a literal count `k > 0`
    (`exitRepeatWords`) places its result at the array of `k` words `.TArr k .TU64`; the
    result and the arguments of any other call other than a scalar call are placed at the
    call's tower type; a copy between names takes the placement of the placed side.  With
    `dflt`, an `array_lit` of `k > 0` scalar names (`exitLitWords`) is placed at
    `.TArr k .TU64`, and the arrays of element loads of scalars, element stores of scalars
    and `len`, and any other `array_lit` without a placed argument with its arguments, are
    placed at `.TFp`. -/
def exitTowersStep (sc : List String) (dflt : Bool) (A : ExitTowers) :
    String × ImpExpr → ExitTowers
  | (n, .app f args) =>
      if f = "index" then
        match args with
        | .var arr :: _ =>
            match A.lookup n with
            | some t' =>
                match exitContainer t' with
                | some c => exitPlaceAt sc A arr c
                | none => A
            | none => if sc.contains n || dflt then exitPlaceAt sc A arr .TFp else A
        | _ => A
      else if f = "array_update" then
        match args with
        | [.var arr, _, .var src] =>
            match A.lookup src with
            | some t' =>
                match exitContainer t' with
                | some c => exitPlaceAt sc A arr c
                | none => A
            | none => if sc.contains src || dflt then exitPlaceAt sc A arr .TFp else A
        | _ => A
      else if f = "len" then
        match args with
        | .var arr :: _ => if dflt then exitPlaceAt sc A arr .TFp else A
        | _ => A
      else if f = "array_lit" then
        match exitFirstTower A args with
        | some t' =>
            match exitContainer t' with
            | some c =>
                exitPlaceAt sc ((exitArgNames args).foldl (fun A x => exitPlaceAt sc A x t') A) n c
            | none => A
        | none =>
            if dflt then
              match exitLitWords sc args with
              | some k => exitPlaceAt sc A n (.TArr k .TU64)
              | none =>
                exitPlaceAt sc ((exitArgNames args).foldl (fun A x => exitPlaceAt sc A x .TFp) A)
                  n .TFp
            else A
      else if exitScalarCall f then A
      else
        match (if f = "repeat" then exitRepeatWords sc args else none) with
        | some k => exitPlaceAt sc A n (.TArr k .TU64)
        | none =>
          let dt := towerOfCallName f
          exitPlaceAt sc ((exitArgNames args).foldl (fun A x => exitPlaceAt sc A x dt) A) n dt
  | (n, .var s) =>
      match A.lookup n, A.lookup s with
      | some t, none => exitPlaceAt sc A s t
      | none, some t => exitPlaceAt sc A n t
      | _, _ => A
  | _ => A

/-- The inferred placement of a body: from its scalar names (`exitScalarNames`, where a
    literal binding of a name that a call with a tower result also binds does not make the
    name scalar, and an element load bound to a name of `exitTowerNames` is not scalar),
    three passes of `exitTowersStep` over its bindings, then two passes with the default
    placements; the names of the form `exitCallKey f` are left out, so that the placement
    declares no call result type (`exitCallTys_exitTowers`). -/
def exitTowers (e : ImpExpr) : ExitTowers :=
  let bs := exitBinds e
  let sc := exitScalarNames (exitTowerBound e) (exitTowerNames e) e
  let pass (dflt : Bool) (A : ExitTowers) : ExitTowers := bs.foldl (exitTowersStep sc dflt) A
  (pass true (pass true (pass false (pass false (pass false []))))).filter
    fun p => !exitIsCallKey p.1

theorem exitIsCallKey_callKey (f : String) : exitIsCallKey (exitCallKey f) = true := by
  simp [exitIsCallKey, exitCallKey, String.toList_append]

theorem exitIsCallKey_optKey (f : String) : exitIsCallKey (exitOptKey f) = true := by
  simp [exitIsCallKey, exitOptKey, String.toList_append]

/-- A placement with the names of `exitIsCallKey` left out declares nothing at such a
    name. -/
theorem lookup_isCallKey_filter (l : ExitTowers) {k : String} (hk : exitIsCallKey k = true) :
    (l.filter fun p => !exitIsCallKey p.1).lookup k = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', b⟩ := p
    by_cases hp : exitIsCallKey k' = true
    · simp [hp, ih]
    · have hne : (k == k') = false := by
        simpa using fun h : k = k' => hp (h ▸ hk)
      simp [hp, List.lookup_cons, hne, ih]

/-- A placement with the names of the form `exitCallKey` left out declares no call result
    type. -/
theorem lookup_callKey_filter (l : ExitTowers) (f : String) :
    (l.filter fun p => !exitIsCallKey p.1).lookup (exitCallKey f) = none :=
  lookup_isCallKey_filter l (exitIsCallKey_callKey f)

theorem exitCallTys_exitTowers (e : ImpExpr) (f : String) :
    exitCallTys (exitTowers e) f = none :=
  lookup_callKey_filter _ f

theorem exitOptTys_exitTowers (e : ImpExpr) (f : String) :
    exitOptTys (exitTowers e) f = none :=
  lookup_isCallKey_filter _ (exitIsCallKey_optKey f)

theorem exitCallKey_inj {f g : String} (h : exitCallKey f = exitCallKey g) : f = g := by
  unfold exitCallKey at h
  have := congrArg String.toList h
  simp [String.toList_append] at this
  exact String.toList_inj.mp this

theorem exitOptKey_inj {f g : String} (h : exitOptKey f = exitOptKey g) : f = g := by
  unfold exitOptKey at h
  have := congrArg String.toList h
  simp [String.toList_append] at this
  exact String.toList_inj.mp this

theorem exitOptKey_ne_callKey (f g : String) : exitOptKey f ≠ exitCallKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitOptKey, exitCallKey, String.toList_append] at this

/-- A lookup at `key f` in the entries `key g ↦ d` of the names `fs` with `M g = some d`,
    followed by `rest` declaring nothing at `key f`, finds only `M f`. -/
theorem lookup_keyed {key : String → String} (hinj : ∀ {f g}, key f = key g → f = g)
    (M : String → Option TowerType) (fs : List String) (rest : ExitTowers) {f : String}
    {d : TowerType} (hrest : rest.lookup (key f) = none)
    (h : ((fs.filterMap fun g => (M g).map fun d => (key g, d)) ++ rest).lookup (key f) =
      some d) : M f = some d := by
  induction fs with
  | nil => simp [hrest] at h
  | cons g fs ih =>
    rcases hg : M g with _ | e
    · simp only [List.filterMap_cons, hg, Option.map_none] at h
      exact ih h
    · simp only [List.filterMap_cons, hg, Option.map_some, List.cons_append,
        List.lookup_cons] at h
      by_cases he : key f = key g
      · simp only [he, beq_self_eq_true] at h
        rw [hinj he, hg]
        exact h
      · have : (key f == key g) = false := by simpa using he
        simp only [this] at h
        exact ih h

/-- The entries `key g ↦ d` declare nothing at a name no `key g` equals. -/
theorem lookup_keyed_other {key : String → String} (M : String → Option TowerType)
    (fs : List String) (rest : ExitTowers) {k : String} (hk : ∀ g, key g ≠ k) :
    ((fs.filterMap fun g => (M g).map fun d => (key g, d)) ++ rest).lookup k =
      rest.lookup k := by
  induction fs with
  | nil => rfl
  | cons g fs ih =>
    rcases hg : M g with _ | e
    · simp only [List.filterMap_cons, hg, Option.map_none]
      exact ih
    · simp only [List.filterMap_cons, hg, Option.map_some, List.cons_append,
        List.lookup_cons]
      have : (k == key g) = false := by simpa using fun h : k = key g => hk g h.symm
      simp only [this]
      exact ih

/-- The placement `rest` with the declared result types `D` and the declared payload
    placements `DO` of the call names `fs` recorded under `exitCallKey` and `exitOptKey`,
    and the names of those forms in `rest` left out. -/
def exitWithCallKeys (D DO : String → Option TowerType) (fs : List String)
    (rest : ExitTowers) : ExitTowers :=
  (fs.filterMap fun g => (D g).map fun d => (exitCallKey g, d)) ++
    ((fs.filterMap fun g => (DO g).map fun d => (exitOptKey g, d)) ++
      rest.filter (fun p => !exitIsCallKey p.1))

/-- `exitWithCallKeys D DO fs rest` declares only result types of `D`. -/
theorem exitCallTys_withCallKeys {D DO : String → Option TowerType} {fs : List String}
    {rest : ExitTowers} {f : String} {dr : TowerType}
    (h : exitCallTys (exitWithCallKeys D DO fs rest) f = some dr) : D f = some dr := by
  unfold exitCallTys exitWithCallKeys at h
  refine lookup_keyed exitCallKey_inj D fs _ ?_ h
  rw [lookup_keyed_other DO fs _ (fun g => exitOptKey_ne_callKey g f)]
  exact lookup_callKey_filter _ f

/-- `exitWithCallKeys D DO fs rest` declares only payload placements of `DO`. -/
theorem exitOptTys_withCallKeys {D DO : String → Option TowerType} {fs : List String}
    {rest : ExitTowers} {f : String} {t : TowerType}
    (h : exitOptTys (exitWithCallKeys D DO fs rest) f = some t) : DO f = some t := by
  unfold exitOptTys exitWithCallKeys at h
  rw [lookup_keyed_other D fs _ (fun g => (exitOptKey_ne_callKey f g).symm)] at h
  exact lookup_keyed exitOptKey_inj DO fs _ (lookup_isCallKey_filter _ (exitIsCallKey_optKey f)) h

theorem exitIsCallKey_calleeKey (f : String) : exitIsCallKey (exitCalleeKey f) = true := by
  simp [exitIsCallKey, exitCalleeKey, String.toList_append, List.isPrefixOf]

theorem exitCalleeKey_ne_callKey (f g : String) : exitCalleeKey f ≠ exitCallKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitCalleeKey, exitCallKey, String.toList_append] at this

theorem exitCalleeKey_ne_optKey (f g : String) : exitCalleeKey f ≠ exitOptKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitCalleeKey, exitOptKey, String.toList_append] at this

/-- The placement `exitTowers e` records no linked callee. -/
theorem exitCalleeTys_exitTowers (e : ImpExpr) (f : String) :
    exitCalleeTys (exitTowers e) f = none := by
  unfold exitCalleeTys
  rw [show (exitTowers e).lookup (exitCalleeKey f) = none from
    lookup_isCallKey_filter _ (exitIsCallKey_calleeKey f)]
  rfl

/-- `exitWithCallKeys D DO fs rest` records no linked callee. -/
theorem exitCalleeTys_withCallKeys (D DO : String → Option TowerType) (fs : List String)
    (rest : ExitTowers) (f : String) :
    exitCalleeTys (exitWithCallKeys D DO fs rest) f = none := by
  unfold exitCalleeTys exitWithCallKeys
  rw [lookup_keyed_other D fs _ (fun g => (exitCalleeKey_ne_callKey f g).symm),
    lookup_keyed_other DO fs _ (fun g => (exitCalleeKey_ne_optKey f g).symm),
    lookup_isCallKey_filter _ (exitIsCallKey_calleeKey f)]
  rfl

theorem exitIsCallKey_argPrefix (x : String) : exitIsCallKey ("__exit_ty?" ++ x) = true := by
  simp [exitIsCallKey, String.toList_append, List.isPrefixOf]

theorem exitIsCallKey_argKey (f : String) (i : Nat) : exitIsCallKey (exitArgKey f i) = true :=
  exitIsCallKey_argPrefix _

theorem argPrefix_ne_callKey (x g : String) : "__exit_ty?" ++ x ≠ exitCallKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitCallKey, String.toList_append] at this

theorem argPrefix_ne_optKey (x g : String) : "__exit_ty?" ++ x ≠ exitOptKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitOptKey, String.toList_append] at this

theorem argPrefix_ne_calleeKey (x g : String) : "__exit_ty?" ++ x ≠ exitCalleeKey g := by
  intro h
  have := congrArg String.toList h
  simp [exitCalleeKey, String.toList_append] at this

theorem exitArgKey_ne_callKey (f g : String) (i : Nat) : exitArgKey f i ≠ exitCallKey g :=
  argPrefix_ne_callKey _ g

theorem exitArgKey_ne_optKey (f g : String) (i : Nat) : exitArgKey f i ≠ exitOptKey g :=
  argPrefix_ne_optKey _ g

theorem exitArgKey_ne_calleeKey (f g : String) (i : Nat) : exitArgKey f i ≠ exitCalleeKey g :=
  argPrefix_ne_calleeKey _ g

/-- `exitWithCallKeys D DO fs rest` holds nothing at `exitCalleeKey f`. -/
theorem lookup_calleeKey_withCallKeys (D DO : String → Option TowerType) (fs : List String)
    (rest : ExitTowers) (f : String) :
    (exitWithCallKeys D DO fs rest).lookup (exitCalleeKey f) = none := by
  unfold exitWithCallKeys
  rw [lookup_keyed_other D fs _ (fun g => (exitCalleeKey_ne_callKey f g).symm),
    lookup_keyed_other DO fs _ (fun g => (exitCalleeKey_ne_optKey f g).symm)]
  exact lookup_isCallKey_filter _ (exitIsCallKey_calleeKey f)

/-- `exitWithCallKeys D DO fs rest` holds nothing at `exitArgKey f i`. -/
theorem lookup_argKey_withCallKeys (D DO : String → Option TowerType) (fs : List String)
    (rest : ExitTowers) (f : String) (i : Nat) :
    (exitWithCallKeys D DO fs rest).lookup (exitArgKey f i) = none := by
  unfold exitWithCallKeys
  rw [lookup_keyed_other D fs _ (fun g => (exitArgKey_ne_callKey f g i).symm),
    lookup_keyed_other DO fs _ (fun g => (exitArgKey_ne_optKey f g i).symm)]
  exact lookup_isCallKey_filter _ (exitIsCallKey_argKey f i)

theorem lookup_append_of_none {l r : ExitTowers} {k : String} (h : r.lookup k = none) :
    (l ++ r).lookup k = l.lookup k := by
  induction l with
  | nil => simpa using h
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    cases hk : (k == k') <;> simp [List.lookup, hk, ih]

theorem exitArgTys_append {l r : ExitTowers} {f : String}
    (h : ∀ i, r.lookup (exitArgKey f i) = none) :
    ∀ fuel i, exitArgTys (l ++ r) f fuel i = exitArgTys l f fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    simp only [exitArgTys, lookup_append_of_none (h i), exitArgTys_append h fuel (i + 1)]

/-- The linked callees recorded in `l ++ r` are those of `l` when `r` holds nothing at the
    keys of `f`. -/
theorem exitCalleeTys_append {l r : ExitTowers} {f : String}
    (hc : r.lookup (exitCalleeKey f) = none) (ha : ∀ i, r.lookup (exitArgKey f i) = none) :
    exitCalleeTys (l ++ r) f = exitCalleeTys l f := by
  unfold exitCalleeTys
  rw [lookup_append_of_none hc, exitArgTys_append ha]

/-- The entries of the argument slot types `ts` of `g`, from argument `i` on. -/
def argEntries (g : String) : Nat → List TowerType → ExitTowers
  | _, [] => []
  | i, t :: ts => (exitArgKey g i, t) :: argEntries g (i + 1) ts

/-- The placement `rest` with the linked callees `sig` (name, argument slot types, result
    type) recorded under `exitCalleeKey` and `exitArgKey`. -/
def exitWithCallees (sig : List (String × List TowerType × TowerType)) (rest : ExitTowers) :
    ExitTowers :=
  sig.flatMap (fun s => (exitCalleeKey s.1, s.2.2) :: argEntries s.1 0 s.2.1) ++ rest

/-- The linked callees of `exitWithCallees sig rest` are those `sig` records, when `rest`
    holds nothing at their keys. -/
theorem exitCalleeTys_withCallees (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) (f : String) (hc : rest.lookup (exitCalleeKey f) = none)
    (ha : ∀ i, rest.lookup (exitArgKey f i) = none) :
    exitCalleeTys (exitWithCallees sig rest) f = exitCalleeTys (exitWithCallees sig []) f := by
  unfold exitWithCallees
  rw [exitCalleeTys_append hc ha, List.append_nil]

theorem lookup_append_of_left_none {l r : ExitTowers} {k : String} (h : l.lookup k = none) :
    (l ++ r).lookup k = r.lookup k := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k', v⟩ := p
    cases hk : (k == k')
    · simp only [List.cons_append, List.lookup, hk] at h ⊢
      exact ih h
    · simp [List.lookup, hk] at h

theorem lookup_argEntries_other (g : String) {k : String} (hk : ∀ i, exitArgKey g i ≠ k) :
    ∀ i ts, (argEntries g i ts).lookup k = none
  | _, [] => rfl
  | i, t :: ts => by
    have h1 : (k == exitArgKey g i) = false := by
      simpa using fun h : k = exitArgKey g i => hk i h.symm
    simp only [argEntries, List.lookup, h1]
    exact lookup_argEntries_other g hk (i + 1) ts

/-- A lookup in `exitWithCallees sig rest` at a name of neither form `exitCalleeKey g` nor
    `exitArgKey g i` is a lookup in `rest`. -/
theorem lookup_withCallees_other (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) {k : String} (hc : ∀ g, exitCalleeKey g ≠ k)
    (ha : ∀ g i, exitArgKey g i ≠ k) :
    (exitWithCallees sig rest).lookup k = rest.lookup k := by
  unfold exitWithCallees
  induction sig with
  | nil => rfl
  | cons s sig ih =>
    have h1 : (k == exitCalleeKey s.1) = false := by
      simpa using fun h : k = exitCalleeKey s.1 => hc s.1 h.symm
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc, List.lookup, h1]
    rw [lookup_append_of_left_none (lookup_argEntries_other s.1 (fun i => ha s.1 i) 0 s.2.1)]
    exact ih

theorem exitCallTys_withCallees (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) (f : String) :
    exitCallTys (exitWithCallees sig rest) f = exitCallTys rest f :=
  lookup_withCallees_other sig rest (fun g => exitCalleeKey_ne_callKey g f)
    (fun g i => exitArgKey_ne_callKey g f i)

theorem exitOptTys_withCallees (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) (f : String) :
    exitOptTys (exitWithCallees sig rest) f = exitOptTys rest f :=
  lookup_withCallees_other sig rest (fun g => exitCalleeKey_ne_optKey g f)
    (fun g i => exitArgKey_ne_optKey g f i)

theorem exitReserved_calleeKey (g : String) : exitReserved (exitCalleeKey g) = true := by
  simp [exitReserved, exitCalleeKey, String.toList_append, List.isPrefixOf]

theorem exitReserved_argPrefix (x : String) : exitReserved ("__exit_ty?" ++ x) = true := by
  simp [exitReserved, String.toList_append, List.isPrefixOf]

/-- `exitWithCallees sig rest` places a name outside the reserved names as `rest` does. -/
theorem lookup_withCallees_nonreserved (sig : List (String × List TowerType × TowerType))
    (rest : ExitTowers) {n : String} (hn : exitReserved n = false) :
    (exitWithCallees sig rest).lookup n = rest.lookup n :=
  lookup_withCallees_other sig rest
    (fun g h => by rw [← h, exitReserved_calleeKey] at hn; cases hn)
    (fun g i h => by rw [← h] at hn; rw [exitArgKey, exitReserved_argPrefix] at hn; cases hn)

/-- The placement of the tail value of a body under `A`, read from its first tail: the
    placement of a tail variable, `tuple` for a tail tuple, and `scalar` otherwise. -/
def exitResultPlace (A : ExitTowers) : ImpExpr → ExitRes
  | .letBind _ _ b => exitResultPlace A b
  | .seq _ b => exitResultPlace A b
  | .ifThenElse _ t e => ExitRes.optJoin (exitResultPlace A t) (exitResultPlace A e)
  | .typeAscription e _ => exitResultPlace A e
  | .match_ _ [(_, a), (_, b)] => ExitRes.optJoin (exitResultPlace A a) (exitResultPlace A b)
  | .var x => ExitRes.ofPlace (A.lookup x)
  | .tuple _ => .tuple
  | .app "None" [] => .option none
  | .app "Some" [.var x] => .option (A.lookup x)
  | _ => .scalar

/-- The function lowering under the inferred placement. -/
def haxToLowCTFnI (e : ImpExpr) : Option LowCT := haxToLowCTFnT (exitTowers e) e

/-! ## §6  The fragment -/

/-- Every argument is a non-reserved variable. -/
def exitArgsOk : List ImpExpr → Bool
  | [] => true
  | .var x :: as => !exitReserved x && exitArgsOk as
  | _ :: _ => false

/-- The runtime bounds `forBoundsRt` accepts, with a non-reserved scalar upper-bound
    variable. -/
def forBoundsRtOkT (A : ExitTowers) (lo hi : ImpExpr) : Bool :=
  match forBoundsRt lo hi with
  | some (_, h) => !exitReserved h && exitSc A h
  | none => false

/-- The bounds of a counted loop of the fragment have a scalar runtime bound. -/
theorem exitScRt_of_ok {A : ExitTowers} {lo hi : ImpExpr}
    (h : ((forBounds lo hi).isSome || forBoundsRtOkT A lo hi) = true) :
    exitScRt A lo hi = true := by
  unfold exitScRt
  rcases hRt : forBoundsRt lo hi with _ | ⟨l, x⟩
  · rfl
  · obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
    simp only [forBoundsRtOkT, hRt, forBounds, Option.isSome_none, Bool.false_or,
      Bool.and_eq_true] at h
    exact h.2

/-- The bounds of an upward counted loop of the fragment, with counter `i` and body `body`:
    literal bounds (`forBounds`), a literal lower bound and a scalar variable upper bound
    (`forBoundsRtOkT`), or bounds read at run time (`forBoundsV`). -/
def forBoundsOkT (A : ExitTowers) (i : String) (body lo hi : ImpExpr) : Bool :=
  (forBounds lo hi).isSome || forBoundsRtOkT A lo hi || (forBoundsV A i body lo hi).isSome

/-- A variable upper bound of the bounds of `forBoundsOkT` is a non-reserved name held in
    the scalar heap. -/
theorem forBoundsOkT_rt {A : ExitTowers} {i : String} {body lo hi : ImpExpr} {l : Nat}
    {h : String} (hok : forBoundsOkT A i body lo hi = true)
    (hRt : forBoundsRt lo hi = some (l, h)) : exitReserved h = false ∧ exitSc A h = true := by
  obtain ⟨rfl, rfl⟩ := forBoundsRt_some hRt
  simp only [forBoundsOkT, forBoundsRtOkT, hRt, forBounds, Option.isSome_none,
    Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hok
  rcases hok with hok | hok
  · exact hok
  · rcases hV : forBoundsV A i body (.lit (.int (l : Int))) (.var h) with _ | ⟨a, b⟩
    · rw [hV] at hok; cases hok
    · have hb := (forBoundsV_some hV).2
      simp only [boundSE] at hb
      split at hb
      · rename_i hc
        simpa only [Bool.and_eq_true, Bool.not_eq_true'] using hc
      · cases hb

/-- The bounds of `forBoundsOkT` have a scalar runtime bound. -/
theorem exitScRt_of_okT {A : ExitTowers} {i : String} {body lo hi : ImpExpr}
    (h : forBoundsOkT A i body lo hi = true) : exitScRt A lo hi = true := by
  unfold exitScRt
  rcases hRt : forBoundsRt lo hi with _ | ⟨l, x⟩
  · rfl
  · exact (forBoundsOkT_rt h hRt).2

/-- The arguments of `repeat(v, l)`: a non-reserved variable and a literal of `exitLitOk`. -/
def exitRepeatArgsOk : List ImpExpr → Bool
  | [.var v, .lit l] => !exitReserved v && exitLitOk l
  | _ => false

/-- The arguments of a call `f` the fragment admits: non-reserved variables
    (`exitArgsOk`), or, for `repeat`, a variable and a literal count (`exitRepeatArgsOk`). -/
def exitArgsOkT (f : String) (args : List ImpExpr) : Bool :=
  exitArgsOk args || (f == "repeat" && exitRepeatArgsOk args)

/-- A scalar payload of a `cfBreak`: a variable held in the scalar heap, a literal of
    `exitLitOk`, or `unitVal`. -/
def exitPayloadOk (A : ExitTowers) : ImpExpr → Bool
  | .var x => !exitReserved x && exitSc A x
  | .lit l => exitLitOk l
  | .unitVal => true
  | _ => false

theorem exitScE_of_payloadOk {A : ExitTowers} {p : ImpExpr} (h : exitPayloadOk A p = true) :
    exitScE A p = true := by
  cases p <;> simp_all [exitPayloadOk, exitScE]

/-- The fragment the typed simulation covers under the placement `A` with result
    placement `R`, at tail position `tl` and loop context `il`: every name is
    non-reserved; conditions, loop counters, runtime bounds and break payloads are
    scalar; a literal is a scalar word; a copy keeps the placement; a call
    has a head of `appHeadT`; a tail variable has placement `R`, a tail literal or
    `unitVal` needs `R = scalar`, and a tail tuple of non-reserved variables needs
    `R = tuple`. -/
def exitSimOkT (A : ExitTowers) (R : ExitRes) : Bool → Bool → ImpExpr → Bool
  | tl, il, .letBind n (.lit l) body =>
      exitLitOk l && !exitReserved n && exitSimOkT A R tl il body
  | tl, il, .letBind n (.var s) body =>
      !exitReserved n && !exitReserved s && decide (A.lookup n = A.lookup s) &&
        exitSimOkT A R tl il body
  | tl, il, .letBind n (.app f args) body =>
      !exitReserved n && exitArgsOkT f args && (appHeadT A n f args).isSome &&
        exitSimOkT A R tl il body
  | tl, il, .seq a b => exitSimOkT A R false il a && exitSimOkT A R tl il b
  | tl, il, .ifThenElse (.var v) t e =>
      !exitReserved v && exitSc A v && exitSimOkT A R tl il t && exitSimOkT A R tl il e
  | tl, il, .typeAscription e _ => exitSimOkT A R tl il e
  | tl, il, .match_ (.app f args) [(.somePat (.varPat p), t), (.nonePat, e)] =>
      !exitReserved p && exitArgsOk args && (optHeadT A f args p).isSome &&
        exitSimOkT A R tl il t && exitSimOkT A R tl il e
  | tl, il, .match_ (.app f args) [(.nonePat, e), (.somePat (.varPat p), t)] =>
      !exitReserved p && exitArgsOk args && (optHeadT A f args p).isSome &&
        exitSimOkT A R tl il t && exitSimOkT A R tl il e
  | false, _, .whileFoldReturn (.var c) body =>
      !exitReserved c && exitSc A c && exitSimOkT A R false true body
  | false, _, .forFoldReturn i lo hi body =>
      forBoundsOkT A i body lo hi && !exitReserved i &&
        exitSc A i && exitSimOkT A R false true body
  | false, _, .forFoldRevReturn i lo hi body =>
      (forBounds lo hi).isSome && !exitReserved i && exitSc A i &&
        exitSimOkT A R false true body
  | false, true, .forFold i lo hi body =>
      forBoundsOkT A i body lo hi && !exitReserved i &&
        exitSc A i && exitSimOkT A R false true body
  | false, true, .forFoldRev i lo hi body =>
      (forBounds lo hi).isSome && !exitReserved i && exitSc A i &&
        exitSimOkT A R false true body
  | false, true, .whileFold (.var c) body =>
      !exitReserved c && exitSc A c && exitSimOkT A R false true body
  | _, true, .cfBreak p => exitPayloadOk A p
  | tl, _, .var x => !exitReserved x && (!tl || decide (ExitRes.ofPlace (A.lookup x) = R))
  | tl, _, .unitVal => !tl || decide (R = .scalar)
  | true, _, .lit l => exitLitOk l && decide (R = .scalar)
  | true, _, .tuple es => decide (R = .tuple) && exitArgsOk es
  | true, _, .app "None" [] => R.isOption
  | true, _, .app "Some" [.var x] => !exitReserved x && decide (R = .option (A.lookup x))
  | _, _, _ => false

/-- The `match` of the fragment: a call scrutinee with a `Some p` arm and a `None` arm, in
    either order. -/
def exitMatchShape : ImpExpr → List (_root_.Hax.ImpPat × ImpExpr) → Bool
  | .app _ _, [(.somePat (.varPat _), _), (.nonePat, _)] => true
  | .app _ _, [(.nonePat, _), (.somePat (.varPat _), _)] => true
  | _, _ => false

theorem exitMatchShape_cases {s : ImpExpr} {arms : List (_root_.Hax.ImpPat × ImpExpr)}
    (h : exitMatchShape s arms = true) :
    (∃ f args p t e, s = .app f args ∧ arms = [(.somePat (.varPat p), t), (.nonePat, e)]) ∨
      (∃ f args p t e, s = .app f args ∧ arms = [(.nonePat, e), (.somePat (.varPat p), t)]) := by
  unfold exitMatchShape at h
  split at h
  · exact Or.inl ⟨_, _, _, _, _, rfl, rfl⟩
  · exact Or.inr ⟨_, _, _, _, _, rfl, rfl⟩
  · cases h

theorem exitMatchShape_of_ok (A : ExitTowers) (R : ExitRes) {tl il : Bool} {s : ImpExpr}
    {arms : List (_root_.Hax.ImpPat × ImpExpr)}
    (h : exitSimOkT A R tl il (.match_ s arms) = true) : exitMatchShape s arms = true := by
  unfold exitSimOkT at h
  split at h <;> simp_all [exitMatchShape]

/-- The first construct of `e` outside the fragment `exitSimOkT A R tl il`, with the
    reason; `none` when `e` lies in the fragment. -/
def exitSimWhyT (A : ExitTowers) (R : ExitRes) :
    Bool → Bool → ImpExpr → Option String
  | tl, il, .letBind n (.lit l) body =>
      if !exitLitOk l then some "literal not a scalar word"
      else if exitReserved n then some "reserved name" else exitSimWhyT A R tl il body
  | tl, il, .letBind n (.var s) body =>
      if exitReserved n || exitReserved s then some "reserved name"
      else if !decide (A.lookup n = A.lookup s) then some "copy across placements"
      else exitSimWhyT A R tl il body
  | tl, il, .letBind n (.app f args) body =>
      if exitReserved n || !exitArgsOkT f args then
        some "reserved name or non-variable argument"
      else if (appHeadT A n f args).isNone then some s!"letBind app {f}/{args.length} placement"
      else exitSimWhyT A R tl il body
  | tl, il, .seq a b =>
      match exitSimWhyT A R false il a with
      | some r => some r
      | none => exitSimWhyT A R tl il b
  | tl, il, .ifThenElse (.var v) t e =>
      if exitReserved v then some "reserved name"
      else if !exitSc A v then some "condition placed in a tower"
      else
        match exitSimWhyT A R tl il t with
        | some r => some r
        | none => exitSimWhyT A R tl il e
  | tl, il, .typeAscription e _ => exitSimWhyT A R tl il e
  | tl, il, .match_ (.app f args) [(.somePat (.varPat p), t), (.nonePat, e)] =>
      if exitReserved p || !exitArgsOk args then some "reserved name or non-variable argument"
      else if (optHeadT A f args p).isNone then some s!"match {f} option placement"
      else
        match exitSimWhyT A R tl il t with
        | some r => some r
        | none => exitSimWhyT A R tl il e
  | tl, il, .match_ (.app f args) [(.nonePat, e), (.somePat (.varPat p), t)] =>
      if exitReserved p || !exitArgsOk args then some "reserved name or non-variable argument"
      else if (optHeadT A f args p).isNone then some s!"match {f} option placement"
      else
        match exitSimWhyT A R tl il t with
        | some r => some r
        | none => exitSimWhyT A R tl il e
  | false, _, .whileFoldReturn (.var c) body =>
      if exitReserved c then some "reserved name"
      else if !exitSc A c then some "condition placed in a tower"
      else exitSimWhyT A R false true body
  | false, _, .forFoldReturn i lo hi body =>
      if !forBoundsOkT A i body lo hi then some "forFoldReturn bounds"
      else if exitReserved i then some "reserved name"
      else if !exitSc A i then some "counter placed in a tower"
      else exitSimWhyT A R false true body
  | false, _, .forFoldRevReturn i lo hi body =>
      if (forBounds lo hi).isNone then some "forFoldRevReturn bounds"
      else if exitReserved i then some "reserved name"
      else if !exitSc A i then some "counter placed in a tower"
      else exitSimWhyT A R false true body
  | false, true, .forFold i lo hi body =>
      if !forBoundsOkT A i body lo hi then some "forFold bounds"
      else if exitReserved i then some "reserved name"
      else if !exitSc A i then some "counter placed in a tower"
      else exitSimWhyT A R false true body
  | false, true, .forFoldRev i lo hi body =>
      if (forBounds lo hi).isNone then some "forFoldRev bounds"
      else if exitReserved i then some "reserved name"
      else if !exitSc A i then some "counter placed in a tower"
      else exitSimWhyT A R false true body
  | false, true, .whileFold (.var c) body =>
      if exitReserved c then some "reserved name"
      else if !exitSc A c then some "condition placed in a tower"
      else exitSimWhyT A R false true body
  | _, true, .cfBreak p => if exitPayloadOk A p then none else some "break payload not scalar"
  | tl, _, .var x =>
      if exitReserved x then some "reserved name"
      else if tl && !decide (ExitRes.ofPlace (A.lookup x) = R) then some "tail placement"
      else none
  | tl, _, .unitVal => if !tl || decide (R = .scalar) then none else some "tail placement"
  | true, _, .lit l =>
      if exitLitOk l && decide (R = .scalar) then none else some "tail literal"
  | true, _, .tuple es =>
      if decide (R = .tuple) && exitArgsOk es then none else some "tail tuple"
  | true, _, .app "None" [] => if R.isOption then none else some "tail None"
  | true, _, .app "Some" [.var x] =>
      if !exitReserved x && decide (R = .option (A.lookup x)) then none else some "tail Some"
  | _, _, .letBind _ v _ => some s!"letBind {exitWhyHead v}"
  | tl, il, e => some s!"{exitWhyHead e} (tail {tl}, loop {il})"

theorem exitSimWhyT_eq_none_iff (A : ExitTowers) (R : ExitRes) (tl il : Bool)
    (e : ImpExpr) : exitSimWhyT A R tl il e = none ↔ exitSimOkT A R tl il e = true := by
  fun_induction exitSimWhyT A R tl il e <;>
    (try simp_all [exitSimOkT, Option.isSome_iff_ne_none]) <;>
    (try intros) <;> (try first | omega | tauto | simp_all)
  rename_i tl _ x _ h
  cases tl
  · exact Or.inl rfl
  · exact Or.inr (h rfl)

end CatCrypt.Crypto.Hax
