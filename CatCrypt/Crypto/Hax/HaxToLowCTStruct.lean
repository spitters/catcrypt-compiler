/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit
public import CatCrypt.Hax.ListBlocks

/-!
# Flat structs and `Option` of a word in the hax front

hax-lean extracts a Rust struct as a nested tuple, a field read `s.f` as the call
`.app ".f" [s]` and a field write as `let s = struct_update#S#i#n(s, x)`; an
`Option` is built by the calls `Some`/`None` and read by a `match` with a
`somePat` and a `nonePat` arm.  `haxToLowCT` and `haxToLowCTFn` lower none of
these.  This module is a source-to-source pass on `ImpExpr` that runs before
A-normalisation and rewrites them into constructs the front lowers.

**Structs.**  A struct variable `s` whose fields are words or arrays is flattened
into one variable per field, `s.f` (`structCompName`).  The struct variables of a
function body and the field names of each struct are given (`StructVars`,
`StructLayout`).  A field call on `s` is the variable `s.f`; an update rebinds
`s.f`; a struct literal `let s = S(x₁, …, xₖ)` binds the components in field
order; hax-lean's parameter alias `let s = s` is dropped; `s` as an argument of
any other call is its component variables in field order, and elsewhere the
tuple of them.  A function returning a struct thus ends in the tuple of the
component variables, which `haxToLowCT` lowers as the aggregate tuple tail of
named results: the fields stay in their component variables.  The printer makes a
one-field struct the field itself, and `HaxEnc` encodes a type that is not a
product as itself; the value of a struct is `structVal`, the field for one field
and the tuple of the fields otherwise, and a one-field struct variable is its
component variable wherever it is read (`structRef`) and is bound directly to a
call result.

**`Option` of a word.**  An `Option` variable `o` is the pair of a bool tag
`o#tag` and a payload word `o#val`.  `let o = Some x` binds `o#val` to `x` and
`o#tag` to `true`, `let o = None` binds `o#tag` to `false`.
`match o { None => e1, Some v => e2 }` is
the branch on the tag, with `o#val` in place of `v` in `e2`; the tag is read as
a public branch condition (whether a secret-dependent branch is admissible is
the business of the constant-time theorems, not of the front).  A function
returning an `Option` returns its tag in a variable `T` and its payload as the
result (`optRet`): `Some x` and `None` in tail position and as the payload of a
`cfBreak` (hax-lean's early return) set `T` and return `x` or the word `0`, so
the early return goes through the function-exit lowering `haxToLowCTFn` with a
word payload.

**Call results, copies and tuple returns.**  `let s = f(args)` of a struct
variable binds the call's tuple result to `s#tup` and reads its components into
the component variables (`callBindArm`).  A variable bound to a component or to an
`Option` payload is copied through the scalar builtin `copyName` (`rhsCopy`),
since the front lowers a `letBind` of one variable to another to nothing.  A
function returning a tuple whose components are variables and flattened structs
returns its result in those variables (`namedRet`): each such tuple in tail
position becomes the unit value and each such `cfBreak` payload `cfBreak ()`, so
the early return goes through `haxToLowCTFn`.

**Simulation.**  Field calls, update calls and `Some`/`None` are builtin calls
of `Hax.denote'`.  `FieldSound`, `UpdateSound` and `OptionSound` state that the
builtin table reads a struct as the flat tuple of its fields and builds `Option`
values; `StructFlatAt` and `OptFlatAt` relate the source environment to the
environment of the flattened program.  Each arm of the pass is simulated
against `denote'`.

## Main definitions

* `flatE` — the struct and `Option`-match flattening pass.
* `optBindArm`, `structLitArm` — the `Option` binding and struct literal arms.
* `optRet` — the `Option` return lowering.
* `structVal`, `structRef` — the value of a struct from its fields, and a flattened
  struct variable as an expression.
* `callBindArm`, `rhsCopy` — the call result arm and the copy of a variable.
* `retVars`, `tailRet`, `namedRet` — the named tuple return.
* `renameVar`, `renameSafe`, `varAbsent` — renaming a variable, and the syntactic
  conditions under which the `Option` match arm renames.
* `RenRel`, `RenSim` — the environments and state computations related by a
  renaming.

## Main results

* `flatE_proj`, `flatE_update` — the projection and update arms of `flatE`.
* `flatProj_sim` — a field call and its component variable evaluate to the same
  value.
* `flatUpdate_sim` — an update and its component rebinding run the continuation
  from environments in which the struct stays flattened.
* `optBreak_some_sim`, `optBreak_none_sim`, `optReturn_some_sim`,
  `optReturn_none_sim` — an `Option` early return or tail value and its lowering
  return the same payload, with the tag in `T`.
* `optMatch_sim` — the `Option` match and the branch on the tag dispatch to the
  same arm.
* `denote'_renameVar` — under `renameSafe v w` and `varAbsent w`, a program and
  its renaming `v ↦ w` return the same result from environments related by the
  renaming.
* `optMatch_some_renamed_sim` — on `some x`, the lowered `Option` match runs as the
  flattened `Some` arm with its binder bound to `x`.
* `optBind_some_sim`, `optBind_none_sim` — `let o = Some x` and `let o = None`
  and their lowering leave `o` flattened.
* `callBind_sim`, `callBind1_sim` — a struct bound to a call result and its
  lowering leave the struct flattened, for a struct with other than one field and
  with one field.
* `flatUpdateCopy_sim` — an update with a variable and its copy into the component
  leave the struct flattened.
* `namedRet_tuple_run`, `namedRet_break_sim` — a returned tuple with the
  variables `rs` is determined by `rs`, and its lowering returns the unit value
  from the same environment.

**Arrays of structs** (§3a, §10).  `ArrDecl`, `ArrVars` declare the array variables;
`flatIdx` is the flat index `i * k + off`; `arrLetKind`, `arrLetBuild`,
`elemFieldKind`, `arrCallArm` are the arms; `bindElems`, `storeElems` the loads and
stores of one element.  `ArrStructFlatAt` relates an array of tuples to its flat
array; `ArrIndexSound`, `ArrUpdateSound`, `LenSound`, `IdxArithSound` state the
builtins the arms use.

* `flatE_app`, `flatE_letBind` — the unfolding of `flatE` on a call and a binding.
* `flatE_elemField`, `flatE_elemBind`, `flatE_arrUpdate`, `flatE_len` — the array
  arms of `flatE`.
* `flatElemField_sim` — the field call on an element and the flat read evaluate to
  the same value.
* `flatElemBind_sim` — the element read into a struct variable and its loads leave
  the struct flattened.
* `flatArrUpdate_sim` — the element write and its stores leave the array flattened.
* `flatLen_sim` — `len` of an array of type `[T; N]` and the literal `N`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat Value Env Outcome Builtins denote')

/-! ## §1  Layouts and component names -/

/-- A struct layout: each struct name with its field names in declaration order. -/
abbrev StructLayout := List (String × List String)

/-- The struct-typed variables of a function body, each with its struct name. -/
abbrev StructVars := List (String × String)

/-- The variable holding field `f` of the flattened struct variable `s`: `s.f`. -/
def structCompName (s f : String) : String := s ++ "." ++ f

/-- The value of a struct whose fields hold `vs`, for a struct with `n` fields: the
    field itself for a one-field struct (the printer's encoding, and `HaxEnc` of a
    type that is not a product), the tuple of the fields otherwise. -/
def structVal : Nat → List Value → Value
  | 1, vs => vs.headD .unit
  | _, vs => .tuple vs

/-- For a struct without exactly one field, the value is the tuple of the fields. -/
theorem structVal_of_ne_one {n : Nat} (h : n ≠ 1) (vs : List Value) :
    structVal n vs = .tuple vs := by
  match n, h with
  | 0, _ => rfl
  | 1, h => exact absurd rfl h
  | _ + 2, _ => rfl

/-- A struct value whose fields are not control flow is not control flow. -/
theorem structVal_not_cf {n : Nat} {vs : List Value}
    (h : ∀ w ∈ vs, w.isControlFlow = false) : (structVal n vs).isControlFlow = false := by
  by_cases hn : n = 1
  · subst hn
    cases vs with
    | nil => rfl
    | cons w ws => exact h w List.mem_cons_self
  · rw [structVal_of_ne_one hn]; rfl

/-- The fields of the struct variable `s`: those of its struct in the layout. -/
def structFields (L : StructLayout) (sv : StructVars) (s : String) : Option (List String) :=
  (List.lookup s sv).bind fun S => List.lookup S L

/-- The component variables of the struct variable `s` with fields `fs`, in field
    order. -/
def structComps (s : String) (fs : List String) : List ImpExpr :=
  fs.map fun f => .var (structCompName s f)

/-- The flattened struct variable `s` with fields `fs` as a value: the component
    variable of a one-field struct, the tuple of the component variables otherwise. -/
def structRef (s : String) (fs : List String) : ImpExpr :=
  match fs with
  | [f] => .var (structCompName s f)
  | _ => .tuple (structComps s fs)

/-- The component read by the field call `c` on the struct variable `s`: the
    component variable of the field `f` with `c = "." ++ f`. -/
def projArm (L : StructLayout) (sv : StructVars) (c s : String) : Option String :=
  (structFields L sv s).bind fun fs => (fs.find? fun f => "." ++ f == c).map (structCompName s)

/-- The component rebound by the update call `c` on the struct variable `s`: the
    component variable of field `i` when `c = struct_update#S#i#n` for the struct
    `S` of `s` with `n` fields. -/
def updateArm (L : StructLayout) (sv : StructVars) (c s : String) : Option String :=
  (List.lookup s sv).bind fun S => (List.lookup S L).bind fun fs =>
    ((List.range fs.length).find? fun i =>
      c == _root_.Hax.structUpdateHead S i fs.length).bind fun i =>
      fs[i]?.map (structCompName s)

/-- The builtin that copies a word: the scalar `&` of a variable with itself,
    which the front lowers to the scalar assignment `comp := y & y`. -/
def copyName : String := "scalar#BitAnd"

/-- The copy of the variable `y`: `scalar#BitAnd(y, y)`. -/
def copyExpr (y : String) : ImpExpr := .app copyName [.var y, .var y]

/-- The right-hand side bound to the variable `comp`: a variable `y` other than
    `comp` is the copy `copyExpr y` (a `letBind` of one variable to another is an
    alias, which the front lowers to nothing); every other expression is itself. -/
def rhsCopy (comp : String) : ImpExpr → ImpExpr
  | .var y => if y == comp then .var y else copyExpr y
  | e => e

/-- The variable holding the tuple returned by a call bound to the struct variable
    `s`: `s#tup`. -/
def structTupName (s : String) : String := s ++ "#tup"

/-- The tag variable of the flattened `Option` variable `o`: a bool, `true` for
    `Some`. -/
def optTagName (o : String) : String := o ++ "#tag"

/-- The payload variable of the flattened `Option` variable `o`. -/
def optValName (o : String) : String := o ++ "#val"

/-! ## §2  Renaming a variable -/

mutual

/-- `renameSafe v w e`: no binder of `e` is `v` or `w`, and `e` contains no `match_`
    and no `lam` (whose pattern binders are not inspected).  Under it every
    occurrence of `var v` in `e` reads the binding of `v` in force when `e`
    starts. -/
def renameSafe (v w : String) : ImpExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .letBind n val body => n != v && n != w && renameSafe v w val && renameSafe v w body
  | .lam _ _ => false
  | .app _ args => renameSafeList v w args
  | .tuple es => renameSafeList v w es
  | .proj e _ => renameSafe v w e
  | .ifThenElse c t e => renameSafe v w c && renameSafe v w t && renameSafe v w e
  | .match_ _ _ => false
  | .unitVal => true
  | .seq a b => renameSafe v w a && renameSafe v w b
  | .borrow e => renameSafe v w e
  | .deref e => renameSafe v w e
  | .assign n r => n != v && n != w && renameSafe v w r
  | .forLoop i lo hi b =>
      i != v && i != w && renameSafe v w lo && renameSafe v w hi && renameSafe v w b
  | .forLoopRev i lo hi b =>
      i != v && i != w && renameSafe v w lo && renameSafe v w hi && renameSafe v w b
  | .whileLoop c b => renameSafe v w c && renameSafe v w b
  | .break_ none => true
  | .break_ (some e) => renameSafe v w e
  | .continue_ => true
  | .earlyReturn e => renameSafe v w e
  | .questionMark e => renameSafe v w e
  | .forFold i lo hi b =>
      i != v && i != w && renameSafe v w lo && renameSafe v w hi && renameSafe v w b
  | .forFoldRev i lo hi b =>
      i != v && i != w && renameSafe v w lo && renameSafe v w hi && renameSafe v w b
  | .whileFold c b => renameSafe v w c && renameSafe v w b
  | .forFoldReturn i lo hi b =>
      i != v && i != w && renameSafe v w lo && renameSafe v w hi && renameSafe v w b
  | .forFoldRevReturn i lo hi b =>
      i != v && i != w && renameSafe v w lo && renameSafe v w hi && renameSafe v w b
  | .whileFoldReturn c b => renameSafe v w c && renameSafe v w b
  | .cfBreak e => renameSafe v w e
  | .cfContinue e => renameSafe v w e
  | .cfBreakContinue e => renameSafe v w e
  | .typeAscription e _ => renameSafe v w e

/-- `renameSafe` on every expression of a list. -/
def renameSafeList (v w : String) : List ImpExpr → Bool
  | [] => true
  | e :: es => renameSafe v w e && renameSafeList v w es

end

mutual

/-- Replace every `var v` by `var w`.  `match_` and `lam` are left unchanged
    (`renameSafe` excludes them). -/
def renameVar (v w : String) : ImpExpr → ImpExpr
  | .lit l => .lit l
  | .var x => if x == v then .var w else .var x
  | .letBind n val body => .letBind n (renameVar v w val) (renameVar v w body)
  | .lam ps b => .lam ps b
  | .app f args => .app f (renameVarList v w args)
  | .tuple es => .tuple (renameVarList v w es)
  | .proj e i => .proj (renameVar v w e) i
  | .ifThenElse c t e => .ifThenElse (renameVar v w c) (renameVar v w t) (renameVar v w e)
  | .match_ s arms => .match_ s arms
  | .unitVal => .unitVal
  | .seq a b => .seq (renameVar v w a) (renameVar v w b)
  | .borrow e => .borrow (renameVar v w e)
  | .deref e => .deref (renameVar v w e)
  | .assign n r => .assign n (renameVar v w r)
  | .forLoop i lo hi b => .forLoop i (renameVar v w lo) (renameVar v w hi) (renameVar v w b)
  | .forLoopRev i lo hi b =>
      .forLoopRev i (renameVar v w lo) (renameVar v w hi) (renameVar v w b)
  | .whileLoop c b => .whileLoop (renameVar v w c) (renameVar v w b)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (renameVar v w e))
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (renameVar v w e)
  | .questionMark e => .questionMark (renameVar v w e)
  | .forFold i lo hi b => .forFold i (renameVar v w lo) (renameVar v w hi) (renameVar v w b)
  | .forFoldRev i lo hi b =>
      .forFoldRev i (renameVar v w lo) (renameVar v w hi) (renameVar v w b)
  | .whileFold c b => .whileFold (renameVar v w c) (renameVar v w b)
  | .forFoldReturn i lo hi b =>
      .forFoldReturn i (renameVar v w lo) (renameVar v w hi) (renameVar v w b)
  | .forFoldRevReturn i lo hi b =>
      .forFoldRevReturn i (renameVar v w lo) (renameVar v w hi) (renameVar v w b)
  | .whileFoldReturn c b => .whileFoldReturn (renameVar v w c) (renameVar v w b)
  | .cfBreak e => .cfBreak (renameVar v w e)
  | .cfContinue e => .cfContinue (renameVar v w e)
  | .cfBreakContinue e => .cfBreakContinue (renameVar v w e)
  | .typeAscription e t => .typeAscription (renameVar v w e) t

/-- `renameVar` on every expression of a list. -/
def renameVarList (v w : String) : List ImpExpr → List ImpExpr
  | [] => []
  | e :: es => renameVar v w e :: renameVarList v w es

end

mutual

/-- `varAbsent w e`: the variable `w` does not occur in `e`, and `e` contains no
    `match_` and no `lam`. -/
def varAbsent (w : String) : ImpExpr → Bool
  | .lit _ => true
  | .var x => x != w
  | .letBind _ val body => varAbsent w val && varAbsent w body
  | .lam _ _ => false
  | .app _ args => varAbsentList w args
  | .tuple es => varAbsentList w es
  | .proj e _ => varAbsent w e
  | .ifThenElse c t e => varAbsent w c && varAbsent w t && varAbsent w e
  | .match_ _ _ => false
  | .unitVal => true
  | .seq a b => varAbsent w a && varAbsent w b
  | .borrow e => varAbsent w e
  | .deref e => varAbsent w e
  | .assign _ r => varAbsent w r
  | .forLoop _ lo hi b => varAbsent w lo && varAbsent w hi && varAbsent w b
  | .forLoopRev _ lo hi b => varAbsent w lo && varAbsent w hi && varAbsent w b
  | .whileLoop c b => varAbsent w c && varAbsent w b
  | .break_ none => true
  | .break_ (some e) => varAbsent w e
  | .continue_ => true
  | .earlyReturn e => varAbsent w e
  | .questionMark e => varAbsent w e
  | .forFold _ lo hi b => varAbsent w lo && varAbsent w hi && varAbsent w b
  | .forFoldRev _ lo hi b => varAbsent w lo && varAbsent w hi && varAbsent w b
  | .whileFold c b => varAbsent w c && varAbsent w b
  | .forFoldReturn _ lo hi b => varAbsent w lo && varAbsent w hi && varAbsent w b
  | .forFoldRevReturn _ lo hi b => varAbsent w lo && varAbsent w hi && varAbsent w b
  | .whileFoldReturn c b => varAbsent w c && varAbsent w b
  | .cfBreak e => varAbsent w e
  | .cfContinue e => varAbsent w e
  | .cfBreakContinue e => varAbsent w e
  | .typeAscription e _ => varAbsent w e

/-- `varAbsent` on every expression of a list. -/
def varAbsentList (w : String) : List ImpExpr → Bool
  | [] => true
  | e :: es => varAbsent w e && varAbsentList w es

end

/-! ## §3  The flattening pass -/

/-- The projection arm on a call `c args`: `some comp` when `args` is one struct
    variable and `c` reads the field held by `comp`. -/
def projArgs (L : StructLayout) (sv : StructVars) (c : String) : List ImpExpr → Option String
  | [.var s] => projArm L sv c s
  | _ => none

/-- The `letBind n val body` arm, given the flattened right-hand side `val'` and
    body `body'`:
    * `let s = s; body` of a struct variable `s` (hax-lean's parameter alias) is
      `body'`;
    * `let s = struct_update#S#i#n(s, x); body` is `let s.f = rhsCopy s.f x'; body'`
      for the field `f` of index `i`, where `x'` is the last argument of `val'`
      (a variable `x'` other than `s.f` is copied);
    * a `letBind` of a struct variable to any other right-hand side is refused;
    * every other `letBind` is `let n = val'; body'`. -/
def letArm (L : StructLayout) (sv : StructVars) (n : String) (val val' body' : ImpExpr) :
    Option ImpExpr :=
  match val with
  | .var s =>
      if n == s && (structFields L sv s).isSome then some body'
      else if (structFields L sv n).isSome then none
      else some (.letBind n val' body')
  | .app c [.var s, _] =>
      match (if n == s then updateArm L sv c s else none), val' with
      | some comp, .app _ args' =>
          match args'.getLast? with
          | some x' => some (.letBind comp (rhsCopy comp x') body')
          | none => none
      | _, _ =>
          if (structFields L sv n).isSome then none else some (.letBind n val' body')
  | _ => if (structFields L sv n).isSome then none else some (.letBind n val' body')

/-- The `Option` match arm on the flattened `Option` variable `o`, given the
    flattened arm bodies `e2'` (for `Some v`) and `e1'` (for `None`): the branch on
    the tag `o#tag`, with the payload `o#val` in place of `v` in `e2'`.  The tag is
    read as a public branch condition.  Refused unless `o` is a flattened `Option`
    variable and `renameSafe v o#val e2'`. -/
def optMatchArm (ov : List String) (o v : String) (e2' e1' : ImpExpr) : Option ImpExpr :=
  if ov.contains o && renameSafe v (optValName o) e2' then
    some (.ifThenElse (.var (optTagName o)) (renameVar v (optValName o) e2') e1')
  else none

/-- hax-lean's parameter alias `let o = o` of an `Option` variable `o`. -/
def optAlias (ov : List String) (n : String) : ImpExpr → Bool
  | .var o => n == o && ov.contains o
  | _ => false

/-- The binding `let o = Some x` or `let o = None` of the flattened `Option`
    variable `o`, given the flattened right-hand side `val'` and body `body'`:
    `Some x'` binds the payload `o#val` to `rhsCopy o#val x'` (a variable payload
    is copied) and then the tag `o#tag` to `true`, `None` binds the tag to
    `false`.  `none` on any other right-hand side. -/
def optBindArm (o : String) (val val' body' : ImpExpr) : Option ImpExpr :=
  match val with
  | .app _ [_] =>
      match val' with
      | .app c [x'] =>
          if c == "Some" then
            some (.letBind (optValName o) (rhsCopy (optValName o) x')
              (.letBind (optTagName o) (.lit (.bool true)) body'))
          else none
      | _ => none
  | .app _ [] =>
      match val' with
      | .app c [] =>
          if c == "None" then some (.letBind (optTagName o) (.lit (.bool false)) body') else none
      | _ => none
  | _ => none

/-- Whether `e` is a variable. -/
def isVarExpr : ImpExpr → Bool
  | .var _ => true
  | _ => false

/-- Whether `e` is a struct variable. -/
def isStructVar (L : StructLayout) (sv : StructVars) : ImpExpr → Bool
  | .var s => (structFields L sv s).isSome
  | _ => false

/-- The bindings of the variables `ns` to the expressions `es` in order, around
    `body`. -/
def bindComps : List String → List ImpExpr → ImpExpr → ImpExpr
  | n :: ns, e :: es, body => .letBind n e (bindComps ns es body)
  | _, _, body => body

/-- The struct literal arm: `let s = S(x₁, …, xₖ); body` of a struct variable `s`
    whose struct `S` has the fields `f₁ … fₖ` is
    `let s.f₁ = x₁'; …; let s.fₖ = xₖ'; body'`, where `S(x₁', …, xₖ')` is the
    flattened right-hand side.  `none` unless no `xᵢ` is a struct variable, no
    `xᵢ'` is a variable (a `letBind` of one variable to another is an alias) and no
    component variable of `s` occurs in any `xᵢ'`. -/
def structLitArm (L : StructLayout) (sv : StructVars) (n : String) (val val' body' : ImpExpr) :
    Option ImpExpr :=
  match val, val' with
  | .app c args, .app _ args' =>
      match List.lookup n sv with
      | some S =>
          match List.lookup S L with
          | some fs =>
              if c == S && !(args.any (isStructVar L sv)) && args'.length == fs.length &&
                  args'.all (fun a => !isVarExpr a &&
                    fs.all fun f => varAbsent (structCompName n f) a) then
                some (bindComps (fs.map (structCompName n)) args' body')
              else none
          | none => none
      | none => none
  | _, _ => none

/-- The bindings of the variables `ns` to the components `i`, `i + 1`, … of the
    tuple variable `t`, around `body`. -/
def bindProjs (t : String) : Nat → List String → ImpExpr → ImpExpr
  | _, [], body => body
  | i, n :: ns, body => .letBind n (.proj (.var t) i) (bindProjs t (i + 1) ns body)

/-- The call result arm: `let s = f(args); body` of a struct variable `s` whose
    struct `S` has the fields `f₁ … fₖ` is
    `let s#tup = f(args'); let s.f₁ = s#tup.0; …; let s.fₖ = s#tup.(k-1); body'`,
    where `f(args')` is the flattened right-hand side: the call's tuple result is
    destructured into the component variables through the front's tuple-component
    reads.  A function returning a flat struct returns the tuple of its fields.  A
    one-field struct is its field: `let s = f(args); body` binds `s.f₁` to the call.
    `none` for a struct literal (`f = S`) and an update call. -/
def callBindArm (L : StructLayout) (sv : StructVars) (n : String) (val val' body' : ImpExpr) :
    Option ImpExpr :=
  match val, val' with
  | .app c _, .app c' args' =>
      match List.lookup n sv with
      | some S =>
          match List.lookup S L with
          | some fs =>
              if c != S && !c.startsWith "struct_update#" then
                match fs with
                | [f] => some (.letBind (structCompName n f) (.app c' args') body')
                | _ =>
                  some (.letBind (structTupName n) (.app c' args')
                    (bindProjs (structTupName n) 0 (fs.map (structCompName n)) body'))
              else none
          | none => none
      | none => none
  | _, _ => none

/-! ## §3a  Arrays of structs

An array `arr : [S; n]` of a struct `S` with `k` word fields is one word array of
length `n * k`: `arr[i].f` is `arr[i * k + off_f]` with `off_f` the position of the
field, matching Rust's layout for word fields.  The declared array variables
(`ArrVars`) are parameters (layout fixed by the caller), locals and the component
variables of array fields of struct variables.  The pass rewrites
* the element field read `.f (index (arr, i))` to `index (arr, i * k + off_f)`;
* `let c = index (arr, i)` of a struct variable `c` to the binding of `c#idx` and one
  load per component of `c`;
* `let arr = array_update (arr, i, x)` of a struct value `x` to the binding of
  `arr#idx` and one store per field;
* `len (arr)` of an array of type `[T; N]` to the literal `N`; `len` of a slice of
  structs and every other array operation on an array of structs are refused. -/

/-- The declaration of an array variable: the struct of its elements (`none` for
    words) and the length `N` of an array of type `[T; N]` (`none` for a slice). -/
structure ArrDecl where
  /-- The struct of the elements, `none` for words. -/
  elem : Option String
  /-- The length `N` of an array of type `[T; N]`, `none` for a slice. -/
  size : Option Nat

/-- The array variables of a function body with their declarations, keyed by the
    variable of the flattened program: a parameter or local `a`, or the component
    variable `s.f` of an array field of a struct variable. -/
abbrev ArrVars := List (String × ArrDecl)

/-- The fields of the elements of the array variable `a`, when they are structs of
    the layout. -/
def arrFields (L : StructLayout) (av : ArrVars) (a : String) : Option (List String) :=
  (List.lookup a av).bind fun d => d.elem.bind fun S => List.lookup S L

/-- The flattened variable an array expression reads: a variable is itself, and a
    field call on a struct variable is its component variable. -/
def arrRef (L : StructLayout) (sv : StructVars) : ImpExpr → Option String
  | .var a => some a
  | .app c [.var s] => projArm L sv c s
  | _ => none

/-- The index `i * k + off` of field `off` of element `i` in the flat array of an
    array of `k`-field structs: `Add(Mul(i, k), off)`. -/
def flatIdx (i : ImpExpr) (k off : Nat) : ImpExpr :=
  .app "Add" [.app "Mul" [i, .lit (.int k)], .lit (.int off)]

/-- The position among the fields `fs` of the field read by the field call `c`. -/
def fieldIdx (fs : List String) (c : String) : Option Nat :=
  (List.range fs.length).find? fun j => fs[j]?.map (fun f => "." ++ f) == some c

/-- The element field read `c (index r i)` of an array of structs: the flattened
    array variable of `r`, the field count `k` of the elements and the position
    `off` of the field. -/
def elemFieldKind (L : StructLayout) (sv : StructVars) (av : ArrVars) (c : String) :
    List ImpExpr → Option (String × Nat × Nat)
  | [.app g [r, _]] =>
      match arrRef L sv r with
      | some a =>
          match arrFields L av a with
          | some fs =>
              if g == "index" then (fieldIdx fs c).map fun off => (a, fs.length, off) else none
          | none => none
      | none => none
  | _ => none

/-- The array operations other than `len`. -/
def isArrOp (c : String) : Bool := c == "index" || c == "index_mut" || c == "array_update"

/-- A call `c (r :: rest)` on a declared array `r`: `len` of an array of type
    `[T; N]` is `some (some N)`; `len` of a slice of structs and every other array
    operation on an array of structs are refused, `some none`; every other call is
    `none`. -/
def arrCallArm (L : StructLayout) (sv : StructVars) (av : ArrVars) (c : String) :
    List ImpExpr → Option (Option ImpExpr)
  | r :: rest =>
      match arrRef L sv r with
      | some a =>
          match List.lookup a av with
          | some d =>
              if c == "len" && rest.isEmpty then
                match d.size with
                | some N => some (some (.lit (.int N)))
                | none => if (arrFields L av a).isSome then some none else none
              else if isArrOp c && (arrFields L av a).isSome then some none
              else none
          | none => none
      | none => none
  | [] => none

/-- An array binding of the flattening pass. -/
inductive ArrLet where
  /-- `let n = index(r, i)` of a struct variable `n` with the fields `fs`, read
      from the flattened array variable `a`. -/
  | elem (a : String) (fs : List String)
  /-- `let a = array_update(a, i, x)` of an array variable `a` of structs `S` with
      the fields `fs`. -/
  | update (S : String) (fs : List String)

/-- The array binding `let n = val`: an element read into a struct variable, or an
    element write of an array of structs. -/
def arrLetKind (L : StructLayout) (sv : StructVars) (av : ArrVars) (n : String) :
    ImpExpr → Option ArrLet
  | .app g [r, _] =>
      match arrRef L sv r with
      | some a =>
          match arrFields L av a with
          | some fs =>
              if g == "index" && structFields L sv n == some fs then some (.elem a fs) else none
          | none => none
      | none => none
  | .app g [.var a, _, _] =>
      match (List.lookup a av).bind ArrDecl.elem, arrFields L av a with
      | some S, some fs => if g == "array_update" && n == a then some (.update S fs) else none
      | _, _ => none
  | _ => none

/-- The variable holding the element index of an array binding of `n`: `n#idx`. -/
def elemIdxName (n : String) : String := n ++ "#idx"

/-- The loads of the components `ms`, from field `j` on, of the element at the
    index held by `x` of the flat array `a` of `k`-field structs, around `body`. -/
def bindElems (a x : String) (k : Nat) : Nat → List String → ImpExpr → ImpExpr
  | _, [], body => body
  | j, m :: ms, body =>
      .letBind m (.app "index" [.var a, flatIdx (.var x) k j]) (bindElems a x k (j + 1) ms body)

/-- The stores of the values `vs`, from field `j` on, into the element at the
    index held by `x` of the flat array `a` of `k`-field structs, around `body`. -/
def storeElems (a x : String) (k : Nat) : Nat → List ImpExpr → ImpExpr → ImpExpr
  | _, [], body => body
  | j, v :: vs, body =>
      .letBind a (.app "array_update" [.var a, flatIdx (.var x) k j, v])
        (storeElems a x k (j + 1) vs body)

/-- The field values of a flattened struct value: a tuple (a flattened struct
    variable) or a literal of the struct `S`. -/
def storeVals (S : String) : ImpExpr → Option (List ImpExpr)
  | .tuple vs => some vs
  | .app c vs => if c == S then some vs else none
  | _ => none

/-- An operand of a store: a literal, or a variable other than the array `a` and
    the index variable `x`. -/
def storeAtom (a x : String) : ImpExpr → Bool
  | .lit _ => true
  | .var y => y != a && y != x
  | _ => false

/-- Whether `e` is the variable `n`. -/
def isVarNamed (n : String) : ImpExpr → Bool
  | .var x => x == n
  | _ => false

/-- The lowering of an array binding of `n`, given the flattened arguments `args'`
    of its right-hand side and the flattened body `body'`:
    * an element read binds `n#idx` to the index and loads each component of `n`
      from the flat array;
    * an element write binds `a#idx` to the index and stores each field value into
      the flat array; refused unless the value has one operand per field, each a
      literal or a variable other than `a` and `a#idx`. -/
def arrLetBuild (n : String) : ArrLet → List ImpExpr → ImpExpr → Option ImpExpr
  | .elem a fs, [_, i'], body' =>
      some (.letBind (elemIdxName n) i'
        (bindElems a (elemIdxName n) fs.length 0 (fs.map (structCompName n)) body'))
  | .update S fs, [_, i', x'], body' =>
      match storeVals S x' with
      | some vs =>
          if vs.length == fs.length && vs.all (storeAtom n (elemIdxName n)) then
            some (.letBind (elemIdxName n) i' (storeElems n (elemIdxName n) fs.length 0 vs body'))
          else none
      | none => none
  | _, _, _ => none

mutual

/-- Flatten the struct variables `sv` (layout `L`), the arrays of structs and the
    fixed-size arrays `av` (§3a), and match on the `Option` variables `ov`:
    * a field call `.f s` on a struct variable is the component variable `s.f`;
    * a field call `.f (index (arr, i))` on an element of an array of structs is
      the read of the flat array at `i * k + off_f`; `let c = index (arr, i)` of a
      struct variable binds `c#idx` and loads the components of `c`;
      `let arr = array_update (arr, i, x)` binds `arr#idx` and stores the fields of
      `x`; `len (arr)` of an array of type `[T; N]` is `N` (`arrLetBuild`,
      `arrCallArm`);
    * `let s = struct_update#S#i#n(s, x)` rebinds the component of field `i`, a
      variable `x` through a copy (`rhsCopy`);
    * a struct literal `let s = S(x₁, …, xₖ)` binds the components of `s` in field
      order (`structLitArm`);
    * `let s = f(args)` of a struct variable binds the call's tuple result and
      reads its components into those of `s` (`callBindArm`);
    * `let o = Some x` and `let o = None` of an `Option` variable bind its payload
      and tag (`optBindArm`);
    * hax-lean's parameter alias `let s = s` of a struct or `Option` variable is
      dropped;
    * a struct variable as an argument of any other call is its component
      variables in field order, and elsewhere the tuple of its component
      variables, or its one component variable for a one-field struct
      (`structRef`);
    * `match o { None => e1, Some v => e2 }` on an `Option` variable is the branch
      on its tag `o#tag`, with the payload `o#val` for `v` (`optMatchArm`).
    Returns `none` where a struct or `Option` variable occurs in a form the pass
    does not flatten. -/
def flatE (L : StructLayout) (sv : StructVars) (av : ArrVars) (ov : List String) :
    ImpExpr → Option ImpExpr
  | .lit l => some (.lit l)
  | .var s =>
      match structFields L sv s with
      | some fs => some (structRef s fs)
      | none => if ov.contains s then none else some (.var s)
  | .letBind n val body =>
      if optAlias ov n val then flatE L sv av ov body
      else
        match arrLetKind L sv av n val with
        | some k =>
            match val with
            | .app _ args => do
                let args' ← flatList L sv av ov args
                let body' ← flatE L sv av ov body
                arrLetBuild n k args' body'
            | _ => none
        | none =>
            if (arrFields L av n).isSome && !isVarNamed n val then none
            else do
              let val' ← flatE L sv av ov val
              let body' ← flatE L sv av ov body
              match (if ov.contains n then optBindArm n val val' body' else none) with
              | some e => some e
              | none =>
                  match letArm L sv n val val' body' with
                  | some e => some e
                  | none =>
                      match structLitArm L sv n val val' body' with
                      | some e => some e
                      | none => callBindArm L sv n val val' body'
  | .lam ps b => do let b' ← flatE L sv av ov b; pure (.lam ps b')
  | .app c args =>
      match projArgs L sv c args with
      | some comp => some (.var comp)
      | none =>
          match elemFieldKind L sv av c args with
          | some (a, k, off) =>
              match args with
              | [.app _ [_, i]] => do
                  let i' ← flatE L sv av ov i
                  pure (.app "index" [.var a, flatIdx i' k off])
              | _ => none
          | none =>
              match arrCallArm L sv av c args with
              | some r => r
              | none => do let args' ← flatCallArgs L sv av ov args; pure (.app c args')
  | .tuple es => do let es' ← flatList L sv av ov es; pure (.tuple es')
  | .proj e i => do let e' ← flatE L sv av ov e; pure (.proj e' i)
  | .ifThenElse c t e => do
      let c' ← flatE L sv av ov c
      let t' ← flatE L sv av ov t
      let e' ← flatE L sv av ov e
      pure (.ifThenElse c' t' e')
  | .match_ (.var o) [(.somePat (.varPat v), e2), (.nonePat, e1)] => do
      let e2' ← flatE L sv av ov e2
      let e1' ← flatE L sv av ov e1
      optMatchArm ov o v e2' e1'
  | .match_ (.var o) [(.nonePat, e1), (.somePat (.varPat v), e2)] => do
      let e2' ← flatE L sv av ov e2
      let e1' ← flatE L sv av ov e1
      optMatchArm ov o v e2' e1'
  | .match_ s arms => do
      let s' ← flatE L sv av ov s
      let arms' ← flatArms L sv av ov arms
      pure (.match_ s' arms')
  | .unitVal => some .unitVal
  | .seq a b => do
      let a' ← flatE L sv av ov a
      let b' ← flatE L sv av ov b
      pure (.seq a' b')
  | .borrow e => do let e' ← flatE L sv av ov e; pure (.borrow e')
  | .deref e => do let e' ← flatE L sv av ov e; pure (.deref e')
  | .assign n r =>
      if (structFields L sv n).isSome || ov.contains n || (arrFields L av n).isSome then none
      else do let r' ← flatE L sv av ov r; pure (.assign n r')
  | .forLoop i lo hi b => do
      let lo' ← flatE L sv av ov lo
      let hi' ← flatE L sv av ov hi
      let b' ← flatE L sv av ov b
      pure (.forLoop i lo' hi' b')
  | .forLoopRev i lo hi b => do
      let lo' ← flatE L sv av ov lo
      let hi' ← flatE L sv av ov hi
      let b' ← flatE L sv av ov b
      pure (.forLoopRev i lo' hi' b')
  | .whileLoop c b => do
      let c' ← flatE L sv av ov c
      let b' ← flatE L sv av ov b
      pure (.whileLoop c' b')
  | .break_ none => some (.break_ none)
  | .break_ (some e) => do let e' ← flatE L sv av ov e; pure (.break_ (some e'))
  | .continue_ => some .continue_
  | .earlyReturn e => do let e' ← flatE L sv av ov e; pure (.earlyReturn e')
  | .questionMark e => do let e' ← flatE L sv av ov e; pure (.questionMark e')
  | .forFold i lo hi b => do
      let lo' ← flatE L sv av ov lo
      let hi' ← flatE L sv av ov hi
      let b' ← flatE L sv av ov b
      pure (.forFold i lo' hi' b')
  | .forFoldRev i lo hi b => do
      let lo' ← flatE L sv av ov lo
      let hi' ← flatE L sv av ov hi
      let b' ← flatE L sv av ov b
      pure (.forFoldRev i lo' hi' b')
  | .whileFold c b => do
      let c' ← flatE L sv av ov c
      let b' ← flatE L sv av ov b
      pure (.whileFold c' b')
  | .forFoldReturn i lo hi b => do
      let lo' ← flatE L sv av ov lo
      let hi' ← flatE L sv av ov hi
      let b' ← flatE L sv av ov b
      pure (.forFoldReturn i lo' hi' b')
  | .forFoldRevReturn i lo hi b => do
      let lo' ← flatE L sv av ov lo
      let hi' ← flatE L sv av ov hi
      let b' ← flatE L sv av ov b
      pure (.forFoldRevReturn i lo' hi' b')
  | .whileFoldReturn c b => do
      let c' ← flatE L sv av ov c
      let b' ← flatE L sv av ov b
      pure (.whileFoldReturn c' b')
  | .cfBreak e => do let e' ← flatE L sv av ov e; pure (.cfBreak e')
  | .cfContinue e => do let e' ← flatE L sv av ov e; pure (.cfContinue e')
  | .cfBreakContinue e => do let e' ← flatE L sv av ov e; pure (.cfBreakContinue e')
  | .typeAscription e t => do let e' ← flatE L sv av ov e; pure (.typeAscription e' t)

/-- `flatE` on every expression of a list. -/
def flatList (L : StructLayout) (sv : StructVars) (av : ArrVars) (ov : List String) :
    List ImpExpr → Option (List ImpExpr)
  | [] => some []
  | e :: es => do
      let e' ← flatE L sv av ov e
      let es' ← flatList L sv av ov es
      pure (e' :: es')

/-- The arguments of a call: a struct variable is its component variables in field
    order, any other argument is flattened by `flatE`. -/
def flatCallArgs (L : StructLayout) (sv : StructVars) (av : ArrVars) (ov : List String) :
    List ImpExpr → Option (List ImpExpr)
  | [] => some []
  | e :: es => do
      let es' ← flatCallArgs L sv av ov es
      match e with
      | .var s =>
          match structFields L sv s with
          | some fs => pure (structComps s fs ++ es')
          | none => do let e' ← flatE L sv av ov e; pure (e' :: es')
      | _ => do let e' ← flatE L sv av ov e; pure (e' :: es')

/-- `flatE` on every arm body of a match. -/
def flatArms (L : StructLayout) (sv : StructVars) (av : ArrVars) (ov : List String) :
    List (ImpPat × ImpExpr) → Option (List (ImpPat × ImpExpr))
  | [] => some []
  | (p, e) :: rest => do
      let e' ← flatE L sv av ov e
      let rest' ← flatArms L sv av ov rest
      pure ((p, e') :: rest')

end

/-! ## §4  Returning an `Option` -/

/-- The `Option` value `x` returned into the tag variable `T` and the payload:
    `Some x` sets `T` to `true` and returns `x`, `None` sets `T` to `false` and
    returns the word `0`; `none` for any other expression. -/
def optReturn (T : String) : ImpExpr → Option ImpExpr
  | .app "Some" [x] => some (.seq (.assign T (.lit (.bool true))) x)
  | .app "None" [] => some (.seq (.assign T (.lit (.bool false))) (.lit (.uintLit .w64 0)))
  | _ => none

/-- An early return of an `Option`: `cfBreak (Some x)` sets `T` to `true` and
    breaks with `x`, `cfBreak None` sets `T` to `false` and breaks with the word
    `0`. -/
def optBreak (T : String) : ImpExpr → Option ImpExpr
  | .app "Some" [x] => some (.seq (.assign T (.lit (.bool true))) (.cfBreak x))
  | .app "None" [] =>
      some (.seq (.assign T (.lit (.bool false))) (.cfBreak (.lit (.uintLit .w64 0))))
  | _ => none

/-- The body of a function returning `Option` of a word, with the returned tag in
    the variable `T`: every `Option` in tail position goes through `optReturn`
    and every `cfBreak` payload at function level or in the body of a
    `whileFoldReturn`, `forFoldReturn` or `forFoldRevReturn` goes through
    `optBreak`.  The pass descends through `letBind` bodies, both statements of a
    `seq`, the branches of an `ifThenElse`, a type ascription and the bodies of
    the returning loops; `tl` records tail position.  Refused on a tail value or
    payload that is not `Some x` or `None`. -/
def optRet (T : String) : Bool → ImpExpr → Option ImpExpr
  | tl, .letBind n val body => do let b ← optRet T tl body; pure (.letBind n val b)
  | tl, .seq a b => do
      let a' ← optRet T false a
      let b' ← optRet T tl b
      pure (.seq a' b')
  | tl, .ifThenElse c t e => do
      let t' ← optRet T tl t
      let e' ← optRet T tl e
      pure (.ifThenElse c t' e')
  | tl, .typeAscription e _ => optRet T tl e
  | _, .cfBreak e => optBreak T e
  | _, .forFoldReturn i lo hi b => do let b' ← optRet T false b; pure (.forFoldReturn i lo hi b')
  | _, .forFoldRevReturn i lo hi b => do
      let b' ← optRet T false b; pure (.forFoldRevReturn i lo hi b')
  | _, .whileFoldReturn c b => do let b' ← optRet T false b; pure (.whileFoldReturn c b')
  | true, e => optReturn T e
  | false, e => some e

/-! ## §4b  Returning a tuple in named variables -/

/-- The names of a list of variables; `none` if an element is not a variable. -/
def varsOf : List ImpExpr → Option (List String)
  | [] => some []
  | .var x :: es => (varsOf es).map (x :: ·)
  | _ :: _ => none

/-- The variables of a returned tuple, with the component variables of a flattened
    struct (a tuple of variables) in place: `(x, (a, b), y)` has the variables
    `x, a, b, y`.  `none` on any other component. -/
def retVars : List ImpExpr → Option (List String)
  | [] => some []
  | .var x :: es => (retVars es).map (x :: ·)
  | .tuple ys :: es => do
      let xs ← varsOf ys
      let rs ← retVars es
      pure (xs ++ rs)
  | _ :: _ => none

/-- The variables of the tuple in tail position of a function body, through
    `letBind` bodies, the second statement of a `seq` and type ascriptions. -/
def tailRet : ImpExpr → Option (List String)
  | .letBind _ _ b => tailRet b
  | .seq _ b => tailRet b
  | .typeAscription e _ => tailRet e
  | .tuple es => retVars es
  | _ => none

/-- The body of a function returning a tuple whose components are held in the
    variables `rs`: every tuple in tail position and every `cfBreak` payload at
    function level or in the body of a returning loop must be a tuple with the
    variables `rs` (`retVars`), and becomes the unit value; the result is read from
    `rs`.  The traversal is that of `optRet`; `tl` records tail position.  Refused
    on any other tail value or `cfBreak` payload. -/
def namedRet (rs : List String) : Bool → ImpExpr → Option ImpExpr
  | tl, .letBind n val body => do let b ← namedRet rs tl body; pure (.letBind n val b)
  | tl, .seq a b => do
      let a' ← namedRet rs false a
      let b' ← namedRet rs tl b
      pure (.seq a' b')
  | tl, .ifThenElse c t e => do
      let t' ← namedRet rs tl t
      let e' ← namedRet rs tl e
      pure (.ifThenElse c t' e')
  | tl, .typeAscription e _ => namedRet rs tl e
  | _, .cfBreak (.tuple es) => if retVars es == some rs then some (.cfBreak .unitVal) else none
  | _, .cfBreak _ => none
  | _, .forFoldReturn i lo hi b => do
      let b' ← namedRet rs false b; pure (.forFoldReturn i lo hi b')
  | _, .forFoldRevReturn i lo hi b => do
      let b' ← namedRet rs false b; pure (.forFoldRevReturn i lo hi b')
  | _, .whileFoldReturn c b => do let b' ← namedRet rs false b; pure (.whileFoldReturn c b')
  | true, .tuple es => if retVars es == some rs then some .unitVal else none
  | true, _ => none
  | false, e => some e

/-! ## §5  The arms -/

/-- The projection arm reads the component of a field of the struct variable. -/
theorem projArm_spec {L : StructLayout} {sv : StructVars} {c s comp : String}
    (h : projArm L sv c s = some comp) :
    ∃ (fs : List String) (f : String) (i : Nat), structFields L sv s = some fs ∧
      fs[i]? = some f ∧ c = "." ++ f ∧ comp = structCompName s f := by
  unfold projArm at h
  cases hfs : structFields L sv s with
  | none => simp [hfs] at h
  | some fs =>
    simp only [hfs, Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨f, hf, rfl⟩ := h
    have hp := List.find?_some hf
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (List.mem_of_find?_eq_some hf)
    exact ⟨fs, f, i, rfl, hi, (beq_iff_eq.1 hp).symm, rfl⟩

/-- The update arm rebinds the component of the updated field. -/
theorem updateArm_spec {L : StructLayout} {sv : StructVars} {c s comp : String}
    (h : updateArm L sv c s = some comp) :
    ∃ (S : String) (fs : List String) (i : Nat) (f : String), List.lookup s sv = some S ∧
      List.lookup S L = some fs ∧ c = _root_.Hax.structUpdateHead S i fs.length ∧
      fs[i]? = some f ∧
      comp = structCompName s f := by
  unfold updateArm at h
  cases hS : List.lookup s sv with
  | none => simp [hS] at h
  | some S =>
    cases hL : List.lookup S L with
    | none => simp [hS, hL] at h
    | some fs =>
      simp only [hS, hL, Option.bind_some] at h
      cases hi : (List.range fs.length).find? fun i =>
          c == _root_.Hax.structUpdateHead S i fs.length with
      | none => simp [hi] at h
      | some i =>
        simp only [hi, Option.bind_some, Option.map_eq_some_iff] at h
        obtain ⟨f, hf, rfl⟩ := h
        have hc := List.find?_some hi
        exact ⟨S, fs, i, f, rfl, by simp [hL], beq_iff_eq.1 hc, hf, rfl⟩

/-- Component names of one struct variable are distinct for distinct fields. -/
theorem structCompName_inj {s f g : String} (h : structCompName s f = structCompName s g) :
    f = g := by
  unfold structCompName at h
  simpa using h

/-- `flatE` on a call: the projection arm, the element field read, the array calls,
    and the call on the flattened arguments. -/
theorem flatE_app (L : StructLayout) (sv : StructVars) (av : ArrVars) (ov : List String)
    (c : String) (args : List ImpExpr) :
    flatE L sv av ov (.app c args) =
      (match projArgs L sv c args with
      | some comp => some (.var comp)
      | none =>
          match elemFieldKind L sv av c args with
          | some (a, k, off) =>
              match args with
              | [.app _ [_, i]] => do
                  let i' ← flatE L sv av ov i
                  pure (.app "index" [.var a, flatIdx i' k off])
              | _ => none
          | none =>
              match arrCallArm L sv av c args with
              | some r => r
              | none => do let args' ← flatCallArgs L sv av ov args; pure (.app c args')) := by
  rw [flatE]

/-- `flatE` on a binding: the `Option` alias, the array bindings, the refusal of
    any other binding of an array of structs, and the binding arms. -/
theorem flatE_letBind (L : StructLayout) (sv : StructVars) (av : ArrVars) (ov : List String)
    (n : String) (val body : ImpExpr) :
    flatE L sv av ov (.letBind n val body) =
      (if optAlias ov n val then flatE L sv av ov body
      else
        match arrLetKind L sv av n val with
        | some k =>
            match val with
            | .app _ args => do
                let args' ← flatList L sv av ov args
                let body' ← flatE L sv av ov body
                arrLetBuild n k args' body'
            | _ => none
        | none =>
            if (arrFields L av n).isSome && !isVarNamed n val then none
            else do
              let val' ← flatE L sv av ov val
              let body' ← flatE L sv av ov body
              match (if ov.contains n then optBindArm n val val' body' else none) with
              | some e => some e
              | none =>
                  match letArm L sv n val val' body' with
                  | some e => some e
                  | none =>
                      match structLitArm L sv n val val' body' with
                      | some e => some e
                      | none => callBindArm L sv n val val' body') := by
  rw [flatE]

/-- `flatE` on a field call of a struct variable is the component variable. -/
theorem flatE_proj {L : StructLayout} {sv : StructVars} (av : ArrVars) (ov : List String)
    {c s comp : String} (h : projArm L sv c s = some comp) :
    flatE L sv av ov (.app c [.var s]) = some (.var comp) := by
  rw [flatE_app]; simp only [projArgs, h]

/-- `flatE` on an update of a struct variable (not a declared array) rebinds the
    component of the updated field to the flattened new value `x'`, a variable
    through a copy. -/
theorem flatE_update {L : StructLayout} {sv : StructVars} (av : ArrVars) (ov : List String)
    {c s comp : String} {fs : List String} {x x' body body' : ImpExpr}
    (h : updateArm L sv c s = some comp) (hs : structFields L sv s = some fs)
    (ha : List.lookup s av = none)
    (hxs : ∀ y, x = .var y → structFields L sv y = none)
    (hx : flatE L sv av ov x = some x') (hb : flatE L sv av ov body = some body') :
    flatE L sv av ov (.letBind s (.app c [.var s, x]) body) =
      some (.letBind comp (rhsCopy comp x') body') := by
  have hfx : flatCallArgs L sv av ov [x] = some [x'] := by
    cases x <;> simp_all [flatCallArgs]
  have hpa : projArgs L sv c [.var s, x] = none := rfl
  have hca : flatCallArgs L sv av ov [.var s, x] = some (structComps s fs ++ [x']) := by
    rw [flatCallArgs, hfx]; simp [hs]
  have hal : optAlias ov s (.app c [.var s, x]) = false := rfl
  have hob : ∀ v' b', optBindArm s (.app c [.var s, x]) v' b' = none := fun _ _ => rfl
  have haf : arrFields L av s = none := by simp [arrFields, ha]
  have hak : arrLetKind L sv av s (.app c [.var s, x]) = none := by
    simp only [arrLetKind, arrRef, haf]
  have hek : elemFieldKind L sv av c [.var s, x] = none := rfl
  have hcc : arrCallArm L sv av c [.var s, x] = none := by
    simp only [arrCallArm, arrRef, ha]
  have hv : flatE L sv av ov (.app c [.var s, x]) = some (.app c (structComps s fs ++ [x'])) := by
    rw [flatE_app]; simp only [hpa, hek, hcc, hca, Option.bind_eq_bind, Option.bind_some]; rfl
  rw [flatE_letBind]
  simp only [hal, hak, haf, hv, hb, hob, ite_self, Option.bind_eq_bind,
    Option.bind_some, Option.isSome_none, Bool.false_and, Bool.false_eq_true, if_false]
  simp [letArm, h]

/-- `flatE` on a field call of an element of an array of structs is the read of the
    flat array at the flat index. -/
theorem flatE_elemField {L : StructLayout} {sv : StructVars} {av : ArrVars} {ov : List String}
    {c a : String} {k off : Nat} {r i i' : ImpExpr}
    (hk : elemFieldKind L sv av c [.app "index" [r, i]] = some (a, k, off))
    (hi : flatE L sv av ov i = some i') :
    flatE L sv av ov (.app c [.app "index" [r, i]]) = some (.app "index" [.var a, flatIdx i' k off]) := by
  rw [flatE_app]; simp only [projArgs, hk, hi, Option.bind_eq_bind, Option.bind_some]; rfl

/-- `flatE` on the binding of a struct variable to an element of an array of structs
    binds the index and loads the components. -/
theorem flatE_elemBind {L : StructLayout} {sv : StructVars} {av : ArrVars} {ov : List String}
    {n a : String} {fs : List String} {r r' i i' body body' : ImpExpr}
    (hk : arrLetKind L sv av n (.app "index" [r, i]) = some (.elem a fs))
    (hr : flatE L sv av ov r = some r') (hi : flatE L sv av ov i = some i')
    (hb : flatE L sv av ov body = some body') :
    flatE L sv av ov (.letBind n (.app "index" [r, i]) body) =
      some (.letBind (elemIdxName n) i'
        (bindElems a (elemIdxName n) fs.length 0 (fs.map (structCompName n)) body')) := by
  have hal : optAlias ov n (.app "index" [r, i]) = false := rfl
  have hl : flatList L sv av ov [r, i] = some [r', i'] := by
    simp only [flatList, hr, hi, Option.bind_eq_bind, Option.bind_some]; rfl
  rw [flatE_letBind]
  simp only [hal, hk, hl, hb, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, if_false]
  rfl

/-- `flatE` on the write of a struct value into an array of structs binds the index
    and stores the field operands. -/
theorem flatE_arrUpdate {L : StructLayout} {sv : StructVars} {av : ArrVars} {ov : List String}
    {a S : String} {fs : List String} {a' i i' x x' body body' : ImpExpr} {vs : List ImpExpr}
    (hk : arrLetKind L sv av a (.app "array_update" [.var a, i, x]) = some (.update S fs))
    (ha : flatE L sv av ov (.var a) = some a') (hi : flatE L sv av ov i = some i')
    (hx : flatE L sv av ov x = some x') (hb : flatE L sv av ov body = some body')
    (hvs : storeVals S x' = some vs) (hlen : vs.length = fs.length)
    (hat : vs.all (storeAtom a (elemIdxName a)) = true) :
    flatE L sv av ov (.letBind a (.app "array_update" [.var a, i, x]) body) =
      some (.letBind (elemIdxName a) i' (storeElems a (elemIdxName a) fs.length 0 vs body')) := by
  have hal : optAlias ov a (.app "array_update" [.var a, i, x]) = false := rfl
  have hl : flatList L sv av ov [.var a, i, x] = some [a', i', x'] := by
    simp only [flatList, ha, hi, hx, Option.bind_eq_bind, Option.bind_some]; rfl
  rw [flatE_letBind]
  simp only [hal, hk, hl, hb, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, if_false]
  simp [arrLetBuild, hvs, hlen, hat]

/-- `flatE` on `len` of a declared array of type `[T; N]` is the literal `N`. -/
theorem flatE_len {L : StructLayout} {sv : StructVars} {av : ArrVars} {ov : List String}
    {r : ImpExpr} {N : Nat} (hp : projArgs L sv "len" [r] = none)
    (he : elemFieldKind L sv av "len" [r] = none)
    (h : arrCallArm L sv av "len" [r] = some (some (.lit (.int N)))) :
    flatE L sv av ov (.app "len" [r]) = some (.lit (.int N)) := by
  rw [flatE_app]; simp only [hp, he, h]

/-! ## §6  Simulation of the arms against `denote'`

The flattened program runs in an environment `envF` holding the components of
each struct variable in its component variables (`StructFlatAt`) and the tag and
payload of each `Option` variable (`OptFlatAt`).  Field calls, update calls and
`Some`/`None` are builtins of `denote'`; `FieldSound`, `UpdateSound` and
`OptionSound` state that the builtin table reads a struct as the value
`structVal` of its fields and builds `Option` values. -/

/-- The field calls of the layout `fs` read their component of the struct value with
    one component per field. -/
def FieldSound (bi : Builtins) (fs : List String) : Prop :=
  ∀ (vs : List Value) (i : Nat) (f : String), vs.length = fs.length → fs[i]? = some f →
    bi ("." ++ f) [structVal fs.length vs] = vs[i]?

/-- The update calls of the struct `S` with fields `fs` replace one component of the
    struct value with one component per field. -/
def UpdateSound (bi : Builtins) (S : String) (fs : List String) : Prop :=
  ∀ (vs : List Value) (i : Nat) (v : Value), vs.length = fs.length → i < fs.length →
    bi (_root_.Hax.structUpdateHead S i fs.length) [structVal fs.length vs, v] =
      some (structVal fs.length (vs.set i v))

/-- The builtin table builds `Option` values with `Some` and `None`. -/
def OptionSound (bi : Builtins) : Prop :=
  (∀ v, bi "Some" [v] = some (.option (some v))) ∧ bi "None" [] = some (.option none)

/-- The struct variable `s` with fields `fs` holds in `env` the struct value of
    components `vs`, one per field and none control flow, and `envF` binds the
    component variable of each field to its component. -/
def StructFlatAt (fs : List String) (s : String) (env envF : Env) : Prop :=
  ∃ vs : List Value, env s = some (structVal fs.length vs) ∧ vs.length = fs.length ∧
    (∀ (i : Nat) (f : String), fs[i]? = some f → envF (structCompName s f) = vs[i]?) ∧
    ∀ w ∈ vs, w.isControlFlow = false

/-- The `Option` variable `o` holds `ov` in `env`, and `envF` binds its tag to
    `ov.isSome` and, for `ov = some x`, its payload to `x`. -/
def OptFlatAt (o : String) (env envF : Env) : Prop :=
  ∃ ov : Option Value, env o = some (.option ov) ∧
    envF (optTagName o) = some (.bool ov.isSome) ∧
    ∀ x, ov = some x → envF (optValName o) = some x

section ArmSim

variable (bi : Builtins) (fuel : Nat)

/-- **Projection arm.**  A field call on a flattened struct variable and the
    component variable the arm produces evaluate to the same value, without
    changing either environment. -/
theorem flatProj_sim (L : StructLayout) (sv : StructVars) (c s comp : String)
    (fs : List String) (env envF : Env) (hp : projArm L sv c s = some comp)
    (hfs : structFields L sv s = some fs) (hsf : StructFlatAt fs s env envF)
    (hF : FieldSound bi fs) :
    ∃ v, (denote' bi fuel (.app c [.var s])).run env = (.val v, env) ∧
      (denote' bi fuel (.var comp)).run envF = (.val v, envF) := by
  obtain ⟨fs', f, i, hfs', hi, rfl, rfl⟩ := projArm_spec hp
  rw [hfs] at hfs'
  cases hfs'
  obtain ⟨vs, hs, hlen, hc, hcf⟩ := hsf
  have hlt : i < vs.length := by
    rw [hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
  refine ⟨vs[i], ?_, ?_⟩
  · exact _root_.Hax.Ascent.denote'_app bi fuel
      (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hs)
        (structVal_not_cf hcf) (_root_.Hax.Ascent.denoteArgs'_nil bi fuel env))
      ((hF vs i f hlen hi).trans (List.getElem?_eq_getElem hlt))
  · rw [denote'_var_run, hc i f hi, List.getElem?_eq_getElem hlt]

/-- **Update arm.**  `let s = struct_update#S#i#n(s, x); body` runs `body` from an
    environment in which `s` is the updated tuple, and the flattened
    `let s.f = x'; body'` runs `body'` from an environment binding the component
    of field `f` to the new value; the struct stays flattened.  `x` and its
    flattening `x'` evaluate to the same value, and `x'` writes no component
    variable of another field of `s`. -/
theorem flatUpdate_sim (S s f : String) (fs : List String) (i : Nat) (x x' body body' : ImpExpr)
    (env env1 envF envF1 : Env) (v : Value) (hU : UpdateSound bi S fs)
    (hi : fs[i]? = some f) (huniq : ∀ j, fs[j]? = some f → j = i)
    (hsf : StructFlatAt fs s env envF)
    (hx : (denote' bi fuel x).run env = (.val v, env1)) (hv : v.isControlFlow = false)
    (hx' : (denote' bi fuel x').run envF = (.val v, envF1))
    (hkeep : ∀ g, g ∈ fs → g ≠ f → envF1 (structCompName s g) = envF (structCompName s g)) :
    ∃ env2 envF2,
      (denote' bi fuel (.letBind s
          (.app (_root_.Hax.structUpdateHead S i fs.length) [.var s, x]) body)).run env =
        (denote' bi fuel body).run env2 ∧
      (denote' bi fuel (.letBind (structCompName s f) x' body')).run envF =
          (denote' bi fuel body').run envF2 ∧
      StructFlatAt fs s env2 envF2 := by
  obtain ⟨vs, hs, hlen, hc, hcf⟩ := hsf
  have hifs : i < fs.length := (List.getElem?_eq_some_iff.1 hi).1
  have hcf' : ∀ w ∈ vs.set i v, w.isControlFlow = false := fun w hw => by
    rcases List.mem_or_eq_of_mem_set hw with h | h
    · exact hcf w h
    · rw [h]; exact hv
  have hhead : (denote' bi fuel
      (.app (_root_.Hax.structUpdateHead S i fs.length) [.var s, x])).run env =
      (.val (structVal fs.length (vs.set i v)), env1) :=
    _root_.Hax.Ascent.denote'_app bi fuel
      (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hs)
        (structVal_not_cf hcf)
        (_root_.Hax.Ascent.denoteArgs'_cons bi fuel hx hv
          (_root_.Hax.Ascent.denoteArgs'_nil bi fuel env1)))
      (hU vs i v hlen hifs)
  refine ⟨env1.extend s (structVal fs.length (vs.set i v)),
    envF1.extend (structCompName s f) v,
    denote'_letBind_run_val bi fuel _ _ _ _ _ _ hhead (structVal_not_cf hcf'),
    denote'_letBind_run_val bi fuel _ _ _ _ _ _ hx' hv, vs.set i v,
    _root_.Hax.Env.extend_same _ _ _, by rw [List.length_set, hlen], ?_, hcf'⟩
  intro j g hj
  by_cases hg : g = f
  · subst hg
    have hji : j = i := huniq j hj
    subst hji
    have hlt : j < vs.length := by rw [hlen]; exact hifs
    simp [_root_.Hax.Env.extend, List.getElem?_set_self hlt]
  · have hne : structCompName s g ≠ structCompName s f := fun h => hg (structCompName_inj h)
    have hji : j ≠ i := by
      rintro rfl; rw [hi] at hj; exact hg (Option.some.inj hj).symm
    simp only [_root_.Hax.Env.extend, beq_iff_eq, hne, if_false]
    rw [hkeep g (List.mem_of_getElem? hj) hg, hc j g hj, List.getElem?_set_ne hji.symm]

/-- **`Option` early return, `Some`.**  `cfBreak (Some y)` breaks with the `Option`
    value of `y`; its lowering `optBreak T` sets the tag `T` to `true` and breaks
    with the value of `y`. -/
theorem optBreak_some_sim (T y : String) (env : Env) (v : Value) (e' : ImpExpr)
    (hO : OptionSound bi) (hy : env y = some v) (hv : v.isControlFlow = false) (hT : y ≠ T)
    (he : optBreak T (.app "Some" [.var y]) = some e') :
    (denote' bi fuel (.cfBreak (.app "Some" [.var y]))).run env =
        (.val (.controlFlow true (.option (some v))), env) ∧
      (denote' bi fuel e').run env = (.val (.controlFlow true v), env.extend T (.bool true)) := by
  cases he
  constructor
  · rw [denote'_cfBreak_run', denote'_app_run, denoteArgs'_cons_run, denote'_var_run, hy]
    cases v <;> simp at hv <;> simp only [denoteArgs'_nil_run, Option.map_some, hO.1]
  · have ha : (denote' bi fuel (.assign T (.lit (.bool true)))).run env =
        (.val .unit, env.extend T (.bool true)) := by
      simp only [denote']; rfl
    rw [denote'_seq_run_val bi fuel _ _ _ _ _ ha rfl, denote'_cfBreak_run', denote'_var_run]
    have : (env.extend T (.bool true)) y = some v := by simp [_root_.Hax.Env.extend, hT, hy]
    rw [this]; cases v <;> simp at hv <;> rfl

/-- **`Option` early return, `None`.**  `cfBreak None` breaks with `none`; its
    lowering `optBreak T` sets the tag `T` to `false` and breaks with the word
    `0`. -/
theorem optBreak_none_sim (T : String) (env : Env) (e' : ImpExpr) (hO : OptionSound bi)
    (he : optBreak T (.app "None" []) = some e') :
    (denote' bi fuel (.cfBreak (.app "None" []))).run env =
        (.val (.controlFlow true (.option none)), env) ∧
      (denote' bi fuel e').run env =
        (.val (.controlFlow true (Value.ofLit (.uintLit .w64 0))), env.extend T (.bool false)) := by
  cases he
  constructor
  · rw [denote'_cfBreak_run', denote'_app_run, denoteArgs'_nil_run]
    simp only [hO.2]
  · have ha : (denote' bi fuel (.assign T (.lit (.bool false)))).run env =
        (.val .unit, env.extend T (.bool false)) := by
      simp only [denote']; rfl
    rw [denote'_seq_run_val bi fuel _ _ _ _ _ ha rfl, denote'_cfBreak_run', denote'_lit_run]
    rfl

/-- **`Option` tail value, `Some`.**  `Some y` in tail position is the `Option`
    value of `y`; its lowering `optReturn T` sets the tag `T` to `true` and returns
    the value of `y`. -/
theorem optReturn_some_sim (T y : String) (env : Env) (v : Value) (e' : ImpExpr)
    (hO : OptionSound bi) (hy : env y = some v) (hv : v.isControlFlow = false) (hT : y ≠ T)
    (he : optReturn T (.app "Some" [.var y]) = some e') :
    (denote' bi fuel (.app "Some" [.var y])).run env = (.val (.option (some v)), env) ∧
      (denote' bi fuel e').run env = (.val v, env.extend T (.bool true)) := by
  cases he
  constructor
  · rw [denote'_app_run, denoteArgs'_cons_run, denote'_var_run, hy]
    cases v <;> simp at hv <;> simp only [denoteArgs'_nil_run, Option.map_some, hO.1]
  · have ha : (denote' bi fuel (.assign T (.lit (.bool true)))).run env =
        (.val .unit, env.extend T (.bool true)) := by
      simp only [denote']; rfl
    rw [denote'_seq_run_val bi fuel _ _ _ _ _ ha rfl, denote'_var_run]
    have : (env.extend T (.bool true)) y = some v := by simp [_root_.Hax.Env.extend, hT, hy]
    rw [this]

/-- **`Option` tail value, `None`.**  `None` in tail position is `none`; its
    lowering `optReturn T` sets the tag `T` to `false` and returns the word `0`. -/
theorem optReturn_none_sim (T : String) (env : Env) (e' : ImpExpr) (hO : OptionSound bi)
    (he : optReturn T (.app "None" []) = some e') :
    (denote' bi fuel (.app "None" [])).run env = (.val (.option none), env) ∧
      (denote' bi fuel e').run env =
        (.val (Value.ofLit (.uintLit .w64 0)), env.extend T (.bool false)) := by
  cases he
  constructor
  · rw [denote'_app_run, denoteArgs'_nil_run]
    simp only [hO.2]
  · have ha : (denote' bi fuel (.assign T (.lit (.bool false)))).run env =
        (.val .unit, env.extend T (.bool false)) := by
      simp only [denote']; rfl
    rw [denote'_seq_run_val bi fuel _ _ _ _ _ ha rfl, denote'_lit_run]

/-- **`Option` match.**  On an `Option` variable `o` holding `ov`, the match runs
    `e2` with `v` bound to the payload when `ov = some x` and `e1` when `ov = none`;
    the lowering `optMatchArm` branches on the tag `o#tag` (read as a public
    condition) to the arm body with the payload variable `o#val` in place of `v`,
    or to `e1'`. -/
theorem optMatch_sim (ov : List String) (o v : String) (e2 e1 e2' e1' e' : ImpExpr)
    (env envF : Env) (h : optMatchArm ov o v e2' e1' = some e') (hof : OptFlatAt o env envF) :
    ∃ ox : Option Value, env o = some (.option ox) ∧
      (denote' bi fuel (.match_ (.var o) [(.somePat (.varPat v), e2), (.nonePat, e1)])).run env =
        (match ox with
         | some x => (denote' bi fuel e2).run (env.extend v x)
         | none => (denote' bi fuel e1).run env) ∧
      (denote' bi fuel e').run envF =
        (match ox with
         | some _ => (denote' bi fuel (renameVar v (optValName o) e2')).run envF
         | none => (denote' bi fuel e1').run envF) ∧
      ∀ x, ox = some x → envF (optValName o) = some x := by
  unfold optMatchArm at h
  split at h
  · cases h
    obtain ⟨ox, hs, ht, hv⟩ := hof
    refine ⟨ox, hs, ?_, ?_, hv⟩
    · cases ox <;> simp [denote', _root_.Hax.denoteMatchArms', _root_.Hax.matchPat, hs]
    · rw [denote'_ifThenElse_var_run_bool bi fuel _ _ _ _ _ ht]
      cases ox <;> rfl
  · cases h

end ArmSim

/-! ## §7  Preservation of the renaming

`RenRel v w env envF` relates the environment of a program to the environment of
its renaming `v ↦ w`, and `RenSim` lifts it to state computations.
`denote'_renameVar` is the logical-relation argument over the structure of the
program, with one lemma per loop helper of `denote'` by induction on the fuel. -/

open _root_.Hax (denoteArgs' denoteForLoop' denoteForLoopRev' denoteWhile' denoteForLoop'Return
  denoteForLoopRev'Return denoteWhile'Return denoteForLoopOrig' denoteForLoopRevOrig'
  denoteWhileOrig')

/-- The environments of a program and of its renaming `v ↦ w`: `v` is bound in
    `env`, `envF` holds its value at `w`, and the two agree at every name other
    than `v` and `w`. -/
def RenRel (v w : String) (env envF : Env) : Prop :=
  (∃ x, env v = some x ∧ envF w = some x) ∧ ∀ y, y ≠ v → y ≠ w → envF y = env y

/-- Two state computations related by the renaming `v ↦ w`: from `RenRel`-related
    environments they return the same result and end in `RenRel`-related
    environments. -/
def RenSim (v w : String) {α : Type} (m m' : StateM Env α) : Prop :=
  ∀ env envF, RenRel v w env envF →
    (m.run env).1 = (m'.run envF).1 ∧ RenRel v w (m.run env).2 (m'.run envF).2

/-- Binding a name other than `v` and `w` to the same value on both sides keeps the
    environments related. -/
theorem RenRel.extend {v w : String} {env envF : Env} (h : RenRel v w env envF) {k : String}
    (hkv : k ≠ v) (hkw : k ≠ w) (x : Value) :
    RenRel v w (env.extend k x) (envF.extend k x) := by
  obtain ⟨⟨y, hy1, hy2⟩, ho⟩ := h
  refine ⟨⟨y, ?_, ?_⟩, fun z hzv hzw => ?_⟩
  · rw [_root_.Hax.Env.extend_other _ _ _ _ (Ne.symm hkv)]; exact hy1
  · rw [_root_.Hax.Env.extend_other _ _ _ _ (Ne.symm hkw)]; exact hy2
  · by_cases hz : z = k
    · subst hz; simp only [_root_.Hax.Env.extend_same]
    · rw [_root_.Hax.Env.extend_other _ _ _ _ hz, _root_.Hax.Env.extend_other _ _ _ _ hz]
      exact ho z hzv hzw

/-- A pure computation is related to itself. -/
theorem RenSim.pure {v w : String} {α : Type} (a : α) :
    RenSim v w (Pure.pure a : StateM Env α) (Pure.pure a) :=
  fun _ _ h => ⟨rfl, h⟩

/-- Related computations followed by pointwise related continuations are related. -/
theorem RenSim.bind {v w : String} {α β : Type} {m m' : StateM Env α}
    {f f' : α → StateM Env β} (hm : RenSim v w m m') (hf : ∀ a, RenSim v w (f a) (f' a)) :
    RenSim v w (m >>= f) (m' >>= f') := by
  intro env envF h
  obtain ⟨h1, h2⟩ := hm env envF h
  have e1 : (m >>= f).run env = (f (m.run env).1).run (m.run env).2 := rfl
  have e2 : (m' >>= f').run envF = (f' (m'.run envF).1).run (m'.run envF).2 := rfl
  rw [e1, e2, h1]
  exact hf _ _ _ h2

/-- Binding a name other than `v` and `w` on both sides is related to itself. -/
theorem RenSim.modify_extend {v w k : String} (hkv : k ≠ v) (hkw : k ≠ w) (x : Value) :
    RenSim v w (modify (_root_.Hax.Env.extend · k x) : StateM Env PUnit)
      (modify (_root_.Hax.Env.extend · k x)) :=
  fun _ _ h => ⟨rfl, h.extend hkv hkw x⟩

/-- Case on an outcome and, for a value, on its constructor (and on the bool of a
    `bool`, `result` or `controlFlow` value). -/
local macro "ren_outcome" : tactic => `(tactic|
  (intro r
   rcases r with (x | _ | _ | _ | _)
   all_goals try (rcases x with (⟨_ | _⟩ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _, _⟩ | ⟨_ | _, _⟩))
   all_goals try dsimp only))

/-- `ren_outcome`, also casing on the payload of a `controlFlow` value. -/
local macro "ren_outcome2" : tactic => `(tactic|
  (intro r
   rcases r with (x | _ | _ | _ | _)
   all_goals try (rcases x with (⟨_ | _⟩ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _, _⟩ | ⟨_ | _, p⟩))
   all_goals try (rcases p with (⟨_ | _⟩ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _, _⟩ | ⟨_ | _, _⟩))
   all_goals try dsimp only))

section Rename

variable (bi : Builtins) {v w : String}

/-- Reading `v` and reading `w` in the renaming are related. -/
theorem renSim_var_ren (fuel : Nat) :
    RenSim v w (denote' bi fuel (.var v)) (denote' bi fuel (.var w)) := by
  intro env envF hR
  obtain ⟨y, hy1, hy2⟩ := hR.1
  rw [denote'_var_run, denote'_var_run, hy1, hy2]
  exact ⟨rfl, hR⟩

/-- Reading a name other than `v` and `w` is related to itself. -/
theorem renSim_var_keep (fuel : Nat) {x : String} (hxv : x ≠ v) (hxw : x ≠ w) :
    RenSim v w (denote' bi fuel (.var x)) (denote' bi fuel (.var x)) := by
  intro env envF hR
  rw [denote'_var_run, denote'_var_run, hR.2 x hxv hxw]
  cases env x <;> exact ⟨rfl, hR⟩

theorem renameSafeList_mem : ∀ {es : List ImpExpr}, renameSafeList v w es = true →
    ∀ a ∈ es, renameSafe v w a = true
  | [], _, a, ha => by simp at ha
  | e :: es, h, a, ha => by
    simp only [renameSafeList, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h.1
    · exact renameSafeList_mem h.2 a ha

theorem varAbsentList_mem : ∀ {es : List ImpExpr}, varAbsentList w es = true →
    ∀ a ∈ es, varAbsent w a = true
  | [], _, a, ha => by simp at ha
  | e :: es, h, a, ha => by
    simp only [varAbsentList, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h.1
    · exact varAbsentList_mem h.2 a ha

/-- The argument lists of a call and of its renaming are related when each argument
    is. -/
theorem renSim_args (fuel : Nat) : ∀ (es : List ImpExpr),
    (∀ a ∈ es, RenSim v w (denote' bi fuel a) (denote' bi fuel (renameVar v w a))) →
    RenSim v w (denoteArgs' bi fuel es) (denoteArgs' bi fuel (renameVarList v w es))
  | [], _ => by simp only [renameVarList, denoteArgs']; exact RenSim.pure _
  | e :: es, h => by
    simp only [renameVarList, denoteArgs']
    apply RenSim.bind (h e List.mem_cons_self)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (renSim_args fuel es fun a ha => h a (List.mem_cons_of_mem _ ha))
         intro _; exact RenSim.pure _)

variable {b : ImpExpr}
  (hb : ∀ fuel, RenSim v w (denote' bi fuel b) (denote' bi fuel (renameVar v w b)))
include hb

theorem renSim_forLoop' {i : String} (hiv : i ≠ v) (hiw : i ≠ w) :
    ∀ fuel lo hi, RenSim v w (denoteForLoop' bi fuel i lo hi b)
      (denoteForLoop' bi fuel i lo hi (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoop'; split <;> exact RenSim.pure _
  | succ k ih =>
    intro lo hi
    unfold denoteForLoop'
    split
    · exact RenSim.pure _
    · split
      · exact RenSim.pure _
      · apply RenSim.bind (RenSim.modify_extend hiv hiw _)
        intro _
        apply RenSim.bind (hb (k + 1))
        ren_outcome
        all_goals first | exact RenSim.pure _ | exact ih _ _

theorem renSim_forLoopRev' {i : String} (hiv : i ≠ v) (hiw : i ≠ w) :
    ∀ fuel lo hi, RenSim v w (denoteForLoopRev' bi fuel i lo hi b)
      (denoteForLoopRev' bi fuel i lo hi (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoopRev'; split <;> exact RenSim.pure _
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopRev'
    split
    · exact RenSim.pure _
    · split
      · exact RenSim.pure _
      · apply RenSim.bind (RenSim.modify_extend hiv hiw _)
        intro _
        apply RenSim.bind (hb (k + 1))
        ren_outcome
        all_goals first | exact RenSim.pure _ | exact ih _ _

theorem renSim_forLoopOrig' {i : String} (hiv : i ≠ v) (hiw : i ≠ w) :
    ∀ fuel lo hi, RenSim v w (denoteForLoopOrig' bi fuel i lo hi b)
      (denoteForLoopOrig' bi fuel i lo hi (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoopOrig'; split <;> exact RenSim.pure _
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopOrig'
    split
    · exact RenSim.pure _
    · split
      · exact RenSim.pure _
      · apply RenSim.bind (RenSim.modify_extend hiv hiw _)
        intro _
        apply RenSim.bind (hb (k + 1))
        ren_outcome
        all_goals first | exact RenSim.pure _ | exact ih _ _

theorem renSim_forLoopRevOrig' {i : String} (hiv : i ≠ v) (hiw : i ≠ w) :
    ∀ fuel lo hi, RenSim v w (denoteForLoopRevOrig' bi fuel i lo hi b)
      (denoteForLoopRevOrig' bi fuel i lo hi (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoopRevOrig'; split <;> exact RenSim.pure _
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopRevOrig'
    split
    · exact RenSim.pure _
    · split
      · exact RenSim.pure _
      · apply RenSim.bind (RenSim.modify_extend hiv hiw _)
        intro _
        apply RenSim.bind (hb (k + 1))
        ren_outcome
        all_goals first | exact RenSim.pure _ | exact ih _ _

theorem renSim_forLoop'Return {i : String} (hiv : i ≠ v) (hiw : i ≠ w) :
    ∀ fuel lo hi, RenSim v w (denoteForLoop'Return bi fuel i lo hi b)
      (denoteForLoop'Return bi fuel i lo hi (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoop'Return; split <;> exact RenSim.pure _
  | succ k ih =>
    intro lo hi
    unfold denoteForLoop'Return
    split
    · exact RenSim.pure _
    · split
      · exact RenSim.pure _
      · apply RenSim.bind (RenSim.modify_extend hiv hiw _)
        intro _
        apply RenSim.bind (hb (k + 1))
        ren_outcome2
        all_goals first | exact RenSim.pure _ | exact ih _ _

theorem renSim_forLoopRev'Return {i : String} (hiv : i ≠ v) (hiw : i ≠ w) :
    ∀ fuel lo hi, RenSim v w (denoteForLoopRev'Return bi fuel i lo hi b)
      (denoteForLoopRev'Return bi fuel i lo hi (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoopRev'Return; split <;> exact RenSim.pure _
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopRev'Return
    split
    · exact RenSim.pure _
    · split
      · exact RenSim.pure _
      · apply RenSim.bind (RenSim.modify_extend hiv hiw _)
        intro _
        apply RenSim.bind (hb (k + 1))
        ren_outcome2
        all_goals first | exact RenSim.pure _ | exact ih _ _

variable {c : ImpExpr}
  (hc : ∀ fuel, RenSim v w (denote' bi fuel c) (denote' bi fuel (renameVar v w c)))
include hc

theorem renSim_while' : ∀ fuel, RenSim v w (denoteWhile' bi fuel c b)
    (denoteWhile' bi fuel (renameVar v w c) (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhile'; split <;> first | exact RenSim.pure _ | omega
  | succ k ih =>
    unfold denoteWhile'
    split
    · omega
    · apply RenSim.bind (hc (k + 1))
      ren_outcome
      all_goals first
        | exact RenSim.pure _
        | (apply RenSim.bind (hb (k + 1)); ren_outcome
           all_goals first | exact RenSim.pure _ | exact ih)

theorem renSim_whileOrig' : ∀ fuel, RenSim v w (denoteWhileOrig' bi fuel c b)
    (denoteWhileOrig' bi fuel (renameVar v w c) (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileOrig'; split <;> first | exact RenSim.pure _ | omega
  | succ k ih =>
    unfold denoteWhileOrig'
    split
    · omega
    · apply RenSim.bind (hc (k + 1))
      ren_outcome
      all_goals first
        | exact RenSim.pure _
        | (apply RenSim.bind (hb (k + 1)); ren_outcome
           all_goals first | exact RenSim.pure _ | exact ih)

theorem renSim_while'Return : ∀ fuel, RenSim v w (denoteWhile'Return bi fuel c b)
    (denoteWhile'Return bi fuel (renameVar v w c) (renameVar v w b)) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhile'Return; split <;> first | exact RenSim.pure _ | omega
  | succ k ih =>
    unfold denoteWhile'Return
    split
    · omega
    · apply RenSim.bind (hc (k + 1))
      ren_outcome
      all_goals first
        | exact RenSim.pure _
        | (apply RenSim.bind (hb (k + 1)); ren_outcome2
           all_goals first | exact RenSim.pure _ | exact ih)

end Rename

/-- Unpack the Boolean side conditions of one `renameSafe`/`varAbsent` step. -/
local macro "ren_hyps" : tactic => `(tactic|
  (simp only [renameSafe, varAbsent, Bool.and_eq_true, bne_iff_ne, ne_eq] at *))

/-- **Renaming preserves the run.**  When no binder of `e` is `v` or `w`, `e`
    contains no `match_` and no `lam` (`renameSafe v w e`), and `w` does not occur
    in `e` (`varAbsent w e`), the run of `e` and the run of `renameVar v w e` from
    `RenRel v w`-related environments return the same result and end in
    `RenRel v w`-related environments. -/
theorem denote'_renameVar (bi : Builtins) (v w : String) (e : ImpExpr) :
    renameSafe v w e = true → varAbsent w e = true → ∀ fuel,
      RenSim v w (denote' bi fuel e) (denote' bi fuel (renameVar v w e)) := by
  induction e using _root_.Hax.ImpExpr.ind with
  | lit l => intro _ _ fuel; simp only [renameVar, denote']; exact RenSim.pure _
  | var x =>
    intro _ ha fuel
    simp only [varAbsent, bne_iff_ne, ne_eq] at ha
    simp only [renameVar]
    by_cases hx : x = v
    · subst hx; simp only [beq_self_eq_true, if_true]; exact renSim_var_ren bi fuel
    · simp only [beq_iff_eq, hx, if_false]; exact renSim_var_keep bi fuel hx ha
  | letBind n val body ihv ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ihv hs.1.2 ha.1 fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (RenSim.modify_extend hs.1.1.1 hs.1.1.2 _); intro _
         exact ihb hs.2 ha.2 fuel)
  | lam _ _ _ => intro hs; simp [renameSafe] at hs
  | app f args ih =>
    intro hs ha fuel
    simp only [renameSafe] at hs
    simp only [varAbsent] at ha
    simp only [renameVar, denote', _root_.Hax.denoteApp']
    apply RenSim.bind (renSim_args bi fuel args fun a h =>
      ih a h (renameSafeList_mem hs a h) (varAbsentList_mem ha a h) fuel)
    intro r
    rcases r with _ | vals
    · exact RenSim.pure _
    · dsimp only; split <;> exact RenSim.pure _
  | tuple es ih =>
    intro hs ha fuel
    simp only [renameSafe] at hs
    simp only [varAbsent] at ha
    simp only [renameVar, denote']
    apply RenSim.bind (renSim_args bi fuel es fun a h =>
      ih a h (renameSafeList_mem hs a h) (varAbsentList_mem ha a h) fuel)
    intro r
    rcases r with _ | vals <;> exact RenSim.pure _
  | proj e i ih =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ih hs ha fuel)
    ren_outcome
    all_goals first | exact RenSim.pure _ | (split <;> exact RenSim.pure _)
  | ifThenElse c t e ihc iht ihe =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ihc hs.1.1 ha.1.1 fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _ | exact iht hs.1.2 ha.1.2 fuel | exact ihe hs.2 ha.2 fuel
  | match_ _ _ _ _ => intro hs; simp [renameSafe] at hs
  | unitVal => intro _ _ fuel; simp only [renameVar, denote']; exact RenSim.pure _
  | seq a b iha ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (iha hs.1 ha.1 fuel)
    ren_outcome
    all_goals first | exact RenSim.pure _ | exact ihb hs.2 ha.2 fuel
  | borrow e ih =>
    intro hs ha fuel; ren_hyps; simp only [renameVar, denote']; exact ih hs ha fuel
  | deref e ih =>
    intro hs ha fuel; ren_hyps; simp only [renameVar, denote']; exact ih hs ha fuel
  | assign n r ih =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ih hs.2 ha fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (RenSim.modify_extend hs.1.1 hs.1.2 _); intro _
         exact RenSim.pure _)
  | forLoop i lo hi b ihl ihh ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ihl hs.1.1.2 ha.1.1 fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (ihh hs.1.2 ha.1.2 fuel); ren_outcome
         all_goals first
           | exact RenSim.pure _
           | exact renSim_forLoopOrig' bi (fun f => ihb hs.2 ha.2 f) hs.1.1.1.1 hs.1.1.1.2 _ _ _)
  | forLoopRev i lo hi b ihl ihh ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ihl hs.1.1.2 ha.1.1 fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (ihh hs.1.2 ha.1.2 fuel); ren_outcome
         all_goals first
           | exact RenSim.pure _
           | exact renSim_forLoopRevOrig' bi (fun f => ihb hs.2 ha.2 f) hs.1.1.1.1
               hs.1.1.1.2 _ _ _)
  | whileLoop c b ihc ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    exact renSim_whileOrig' bi (fun f => ihb hs.2 ha.2 f) (fun f => ihc hs.1 ha.1 f) fuel
  | break_none => intro _ _ fuel; simp only [renameVar, denote']; exact RenSim.pure _
  | break_some e ih =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ih hs ha fuel)
    ren_outcome
    all_goals exact RenSim.pure _
  | continue_ => intro _ _ fuel; simp only [renameVar, denote']; exact RenSim.pure _
  | earlyReturn e ih =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ih hs ha fuel)
    ren_outcome
    all_goals exact RenSim.pure _
  | questionMark e ih =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ih hs ha fuel)
    ren_outcome
    all_goals exact RenSim.pure _
  | forFold i lo hi b ihl ihh ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ihl hs.1.1.2 ha.1.1 fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (ihh hs.1.2 ha.1.2 fuel); ren_outcome
         all_goals first
           | exact RenSim.pure _
           | exact renSim_forLoop' bi (fun f => ihb hs.2 ha.2 f) hs.1.1.1.1 hs.1.1.1.2 _ _ _)
  | forFoldRev i lo hi b ihl ihh ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ihl hs.1.1.2 ha.1.1 fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (ihh hs.1.2 ha.1.2 fuel); ren_outcome
         all_goals first
           | exact RenSim.pure _
           | exact renSim_forLoopRev' bi (fun f => ihb hs.2 ha.2 f) hs.1.1.1.1
               hs.1.1.1.2 _ _ _)
  | whileFold c b ihc ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    exact renSim_while' bi (fun f => ihb hs.2 ha.2 f) (fun f => ihc hs.1 ha.1 f) fuel
  | forFoldReturn i lo hi b ihl ihh ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ihl hs.1.1.2 ha.1.1 fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (ihh hs.1.2 ha.1.2 fuel); ren_outcome
         all_goals first
           | exact RenSim.pure _
           | exact renSim_forLoop'Return bi (fun f => ihb hs.2 ha.2 f) hs.1.1.1.1
               hs.1.1.1.2 _ _ _)
  | forFoldRevReturn i lo hi b ihl ihh ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ihl hs.1.1.2 ha.1.1 fuel)
    ren_outcome
    all_goals first
      | exact RenSim.pure _
      | (apply RenSim.bind (ihh hs.1.2 ha.1.2 fuel); ren_outcome
         all_goals first
           | exact RenSim.pure _
           | exact renSim_forLoopRev'Return bi (fun f => ihb hs.2 ha.2 f) hs.1.1.1.1
               hs.1.1.1.2 _ _ _)
  | whileFoldReturn c b ihc ihb =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    exact renSim_while'Return bi (fun f => ihb hs.2 ha.2 f) (fun f => ihc hs.1 ha.1 f) fuel
  | cfBreak e ih =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ih hs ha fuel)
    ren_outcome
    all_goals exact RenSim.pure _
  | cfContinue e ih =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ih hs ha fuel)
    ren_outcome
    all_goals exact RenSim.pure _
  | cfBreakContinue e ih =>
    intro hs ha fuel
    ren_hyps
    simp only [renameVar, denote']
    apply RenSim.bind (ih hs ha fuel)
    ren_outcome
    all_goals exact RenSim.pure _
  | typeAscription e t ih =>
    intro hs ha fuel; ren_hyps; simp only [renameVar, denote']; exact ih hs ha fuel

/-- **`Option` match, `Some` arm, with the renaming.**  On an `Option` variable `o`
    holding `some x`, the lowering `optMatchArm` of the match runs as the flattened
    arm `e2'` with `v` bound to `x`: the same result, and final environments related
    by the renaming `v ↦ o#val`.  The side condition is that `o#val` does not occur
    in `e2'`.  With `optMatch_sim`, which runs the source match as `e2` with `v`
    bound to `x`, this is the `Some` case of the match arm of `flatE`. -/
theorem optMatch_some_renamed_sim (bi : Builtins) (fuel : Nat) (ov : List String)
    (o v : String) (e2' e1' e' : ImpExpr) (env envF : Env) (x : Value)
    (h : optMatchArm ov o v e2' e1' = some e') (hof : OptFlatAt o env envF)
    (ho : env o = some (.option (some x))) (hfresh : varAbsent (optValName o) e2' = true) :
    ((denote' bi fuel e').run envF).1 = ((denote' bi fuel e2').run (envF.extend v x)).1 ∧
      RenRel v (optValName o) ((denote' bi fuel e2').run (envF.extend v x)).2
        ((denote' bi fuel e').run envF).2 := by
  obtain ⟨ox, hs, ht, hv⟩ := hof
  rw [ho] at hs
  cases hs
  unfold optMatchArm at h
  split at h
  · cases h
    rename_i hc
    simp only [Bool.and_eq_true] at hc
    rw [denote'_ifThenElse_var_run_bool bi fuel _ _ _ _ _ ht]
    have hR : RenRel v (optValName o) (envF.extend v x) envF :=
      ⟨⟨x, _root_.Hax.Env.extend_same _ _ _, hv x rfl⟩,
        fun y hy _ => (_root_.Hax.Env.extend_other _ _ _ _ hy).symm⟩
    obtain ⟨h1, h2⟩ := denote'_renameVar bi v (optValName o) e2' hc.2 hfresh fuel _ _ hR
    exact ⟨h1.symm, h2⟩
  · cases h

/-- The tag and payload variables of an `Option` variable are distinct. -/
theorem optTagName_ne_optValName (o : String) : optTagName o ≠ optValName o := by
  simp [optTagName, optValName]

section OptBind

variable (bi : Builtins) (fuel : Nat)

/-- **`Option` binding, `Some`.**  `let o = Some x; body` runs `body` with `o` bound
    to `some v`; its lowering `optBindArm` runs `body'` with the payload `o#val`
    bound to `v` (the value of `rhsCopy o#val x'`) and the tag `o#tag` to `true`,
    so `o` is flattened in the two environments. -/
theorem optBind_some_sim (o : String) (x x' body body' e' : ImpExpr)
    (env env1 envF envF1 : Env) (v : Value) (hO : OptionSound bi)
    (he : optBindArm o (.app "Some" [x]) (.app "Some" [x']) body' = some e')
    (hx : (denote' bi fuel x).run env = (.val v, env1)) (hv : v.isControlFlow = false)
    (hx' : (denote' bi fuel (rhsCopy (optValName o) x')).run envF = (.val v, envF1)) :
    (denote' bi fuel (.letBind o (.app "Some" [x]) body)).run env =
        (denote' bi fuel body).run (env1.extend o (.option (some v))) ∧
      (denote' bi fuel e').run envF =
        (denote' bi fuel body').run
          ((envF1.extend (optValName o) v).extend (optTagName o) (.bool true)) ∧
      OptFlatAt o (env1.extend o (.option (some v)))
        ((envF1.extend (optValName o) v).extend (optTagName o) (.bool true)) := by
  have he' : e' = .letBind (optValName o) (rhsCopy (optValName o) x')
      (.letBind (optTagName o) (.lit (.bool true)) body') := by
    simp only [optBindArm, beq_self_eq_true, if_true] at he
    exact (Option.some.inj he).symm
  subst he'
  have hS : (denote' bi fuel (.app "Some" [x])).run env = (.val (.option (some v)), env1) := by
    rw [denote'_app_run, denoteArgs'_cons_run, hx]
    cases v <;> simp at hv <;> simp only [denoteArgs'_nil_run, Option.map_some, hO.1]
  refine ⟨denote'_letBind_run_val bi fuel _ _ _ _ _ _ hS rfl, ?_, ?_⟩
  · rw [denote'_letBind_run_val bi fuel _ _ _ _ _ _ hx' hv,
      denote'_letBind_run_val bi fuel _ _ _ _ _ _ (denote'_lit_run bi fuel _ _) rfl]
    rfl
  · refine ⟨some v, _root_.Hax.Env.extend_same _ _ _, _root_.Hax.Env.extend_same _ _ _, ?_⟩
    intro y hy
    cases hy
    rw [_root_.Hax.Env.extend_other _ _ _ _ (optTagName_ne_optValName o).symm,
      _root_.Hax.Env.extend_same]

/-- **`Option` binding, `None`.**  `let o = None; body` runs `body` with `o` bound to
    `none`; its lowering `optBindArm` runs `body'` with the tag `o#tag` bound to
    `false`, so `o` is flattened in the two environments. -/
theorem optBind_none_sim (o : String) (body body' e' : ImpExpr) (env envF : Env)
    (hO : OptionSound bi)
    (he : optBindArm o (.app "None" []) (.app "None" []) body' = some e') :
    (denote' bi fuel (.letBind o (.app "None" []) body)).run env =
        (denote' bi fuel body).run (env.extend o (.option none)) ∧
      (denote' bi fuel e').run envF =
        (denote' bi fuel body').run (envF.extend (optTagName o) (.bool false)) ∧
      OptFlatAt o (env.extend o (.option none)) (envF.extend (optTagName o) (.bool false)) := by
  have he' : e' = .letBind (optTagName o) (.lit (.bool false)) body' := by
    simp only [optBindArm, beq_self_eq_true, if_true] at he
    exact (Option.some.inj he).symm
  subst he'
  have hN : (denote' bi fuel (.app "None" [])).run env = (.val (.option none), env) := by
    rw [denote'_app_run, denoteArgs'_nil_run]
    simp only [hO.2]
  refine ⟨denote'_letBind_run_val bi fuel _ _ _ _ _ _ hN rfl, ?_, ?_⟩
  · rw [denote'_letBind_run_val bi fuel _ _ _ _ _ _ (denote'_lit_run bi fuel _ _) rfl]
    rfl
  · exact ⟨none, _root_.Hax.Env.extend_same _ _ _, _root_.Hax.Env.extend_same _ _ _,
      fun _ h => by cases h⟩

end OptBind

/-! ## §9  Call results, copies and named tuple returns -/

/-- A tuple-component read of a variable bound to a tuple returns the component. -/
theorem denote'_proj_var_run (bi : Builtins) (fuel : Nat) (t : String) (i : Nat) (env : Env)
    (vs : List Value) (v : Value) (ht : env t = some (.tuple vs)) (hv : vs[i]? = some v) :
    (denote' bi fuel (.proj (.var t) i)).run env = (.val v, env) := by
  simp only [denote', StateT.run, bind, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, Pure.pure, StateT.pure, ht, Value.projIdx, hv]

/-- `env` extended by the bindings of the names `ns` to the values `ws` in order
    (up to the shorter of the two lists). -/
def extendList (env : Env) : List String → List Value → Env
  | n :: ns, v :: vs => extendList (env.extend n v) ns vs
  | _, _ => env

/-- `extendList` leaves a name outside `ns` unchanged. -/
theorem extendList_other : ∀ (ns : List String) (ws : List Value) (env : Env) (x : String),
    x ∉ ns → extendList env ns ws x = env x
  | [], _, _, _, _ => by simp [extendList]
  | _ :: _, [], _, _, _ => by simp [extendList]
  | n :: ns, w :: ws, env, x, hx => by
    simp only [List.mem_cons, not_or] at hx
    rw [extendList, extendList_other ns ws _ x hx.2, _root_.Hax.Env.extend_other _ _ _ _ hx.1]

/-- `extendList` with distinct names binds the `k`-th name to the `k`-th value. -/
theorem extendList_get : ∀ (ns : List String) (ws : List Value) (env : Env) (k : Nat)
    (n : String), ns.Nodup → ns.length ≤ ws.length → ns[k]? = some n →
    extendList env ns ws n = ws[k]?
  | [], _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, hl, _ => by simp at hl
  | m :: ns, w :: ws, env, k, n, hnd, hl, hk => by
    rw [List.nodup_cons] at hnd
    rw [extendList]
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      rw [extendList_other ns ws _ m hnd.1, _root_.Hax.Env.extend_same]; rfl
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk ⊢
      exact extendList_get ns ws _ k n hnd.2 (by simpa using hl) hk

/-- The component reads `bindProjs t i ns body` of a tuple variable `t` not among
    `ns` bind `ns` to the components from index `i` on and run `body`. -/
theorem bindProjs_run (bi : Builtins) (fuel : Nat) (t : String) (vs : List Value)
    (hcf : ∀ v ∈ vs, v.isControlFlow = false) (body : ImpExpr) :
    ∀ (ns : List String) (i : Nat) (env : Env), env t = some (.tuple vs) → t ∉ ns →
      i + ns.length ≤ vs.length →
      (denote' bi fuel (bindProjs t i ns body)).run env =
        (denote' bi fuel body).run (extendList env ns (vs.drop i))
  | [], i, env, _, _, _ => by simp [bindProjs, extendList]
  | n :: ns, i, env, ht, hn, hl => by
    simp only [List.mem_cons, not_or] at hn
    simp only [List.length_cons] at hl
    have hi : i < vs.length := by omega
    rw [bindProjs, denote'_letBind_run_val bi fuel _ _ _ _ _ _
      (denote'_proj_var_run bi fuel t i env vs vs[i] ht (List.getElem?_eq_getElem hi))
      (hcf _ (List.getElem_mem hi))]
    rw [bindProjs_run bi fuel t vs hcf body ns (i + 1) _
      (by rw [_root_.Hax.Env.extend_other _ _ _ _ hn.1]; exact ht) hn.2 (by omega)]
    rw [List.drop_eq_getElem_cons hi, extendList]

/-- The tuple variable of a struct variable is none of its component variables. -/
theorem structTupName_ne (n f : String) : structTupName n ≠ structCompName n f := by
  simp only [structTupName, structCompName, String.append_assoc, ne_eq]
  intro h
  have := congrArg String.toList h
  simp at this

/-- **Call result arm.**  When the call `val` returns the struct value of the
    components `vs`, one per field, and its flattening `val'` returns the tuple `vs`,
    `let n = val; body` runs `body` with `n` bound to the struct value, and the
    lowering `callBindArm` of a struct with other than one field runs `body'` from an
    environment in which `n` is flattened; the lowering changes no variable other
    than `n#tup` and the component variables of `n`. -/
theorem callBind_sim (bi : Builtins) (fuel : Nat) (n : String) (fs : List String)
    (val val' body body' : ImpExpr) (env env1 envF envF1 : Env) (vs : List Value)
    (hnd : fs.Nodup) (hlen : vs.length = fs.length) (hcf : ∀ v ∈ vs, v.isControlFlow = false)
    (hx : (denote' bi fuel val).run env = (.val (structVal fs.length vs), env1))
    (hx' : (denote' bi fuel val').run envF = (.val (.tuple vs), envF1)) :
    ∃ envF2,
      (denote' bi fuel (.letBind n val body)).run env =
          (denote' bi fuel body).run (env1.extend n (structVal fs.length vs)) ∧
      (denote' bi fuel (.letBind (structTupName n) val'
          (bindProjs (structTupName n) 0 (fs.map (structCompName n)) body'))).run envF =
          (denote' bi fuel body').run envF2 ∧
      StructFlatAt fs n (env1.extend n (structVal fs.length vs)) envF2 ∧
      ∀ x, x ≠ structTupName n → (∀ f ∈ fs, x ≠ structCompName n f) → envF2 x = envF1 x := by
  refine ⟨extendList (envF1.extend (structTupName n) (.tuple vs)) (fs.map (structCompName n)) vs,
    denote'_letBind_run_val bi fuel _ _ _ _ _ _ hx (structVal_not_cf hcf), ?_, ?_, ?_⟩
  · rw [denote'_letBind_run_val bi fuel _ _ _ _ _ _ hx' rfl,
      bindProjs_run bi fuel _ vs hcf body' _ 0 _ (_root_.Hax.Env.extend_same _ _ _)
        (by simp only [List.mem_map, not_exists, not_and]; exact fun f _ h =>
          structTupName_ne n f h.symm)
        (by simp [hlen]), List.drop_zero]
  · refine ⟨vs, _root_.Hax.Env.extend_same _ _ _, hlen, fun i f hi => ?_, hcf⟩
    exact extendList_get _ vs _ i _ (hnd.map fun _ _ h => structCompName_inj h)
      (by simp [hlen]) (by simp [hi])
  · intro x hx1 hx2
    rw [extendList_other _ _ _ x (by
      simp only [List.mem_map, not_exists, not_and]; exact fun f hf h => hx2 f hf h.symm),
      _root_.Hax.Env.extend_other _ _ _ _ hx1]

/-- **Call result arm, one field.**  When the call `val` and its flattening `val'`
    return the same value `v`, `let n = val; body` runs `body` with `n` bound to `v`,
    and the lowering `callBindArm` of a one-field struct, the binding of the
    component variable to `val'`, runs `body'` from an environment in which `n` is
    flattened. -/
theorem callBind1_sim (bi : Builtins) (fuel : Nat) (n f : String) (val val' body body' : ImpExpr)
    (env env1 envF envF1 : Env) (v : Value) (hv : v.isControlFlow = false)
    (hx : (denote' bi fuel val).run env = (.val v, env1))
    (hx' : (denote' bi fuel val').run envF = (.val v, envF1)) :
    (denote' bi fuel (.letBind n val body)).run env =
        (denote' bi fuel body).run (env1.extend n v) ∧
      (denote' bi fuel (.letBind (structCompName n f) val' body')).run envF =
        (denote' bi fuel body').run (envF1.extend (structCompName n f) v) ∧
      StructFlatAt [f] n (env1.extend n v) (envF1.extend (structCompName n f) v) := by
  refine ⟨denote'_letBind_run_val bi fuel _ _ _ _ _ _ hx hv,
    denote'_letBind_run_val bi fuel _ _ _ _ _ _ hx' hv,
    [v], _root_.Hax.Env.extend_same _ _ _, rfl, fun i g hg => ?_, by simpa using hv⟩
  cases i with
  | zero =>
    cases hg
    exact _root_.Hax.Env.extend_same _ _ _
  | succ i => simp at hg

/-- The copy of a variable holding `v` returns `v` when the builtin table copies
    `v`. -/
theorem copyExpr_run (bi : Builtins) (fuel : Nat) (y : String) (env : Env) (v : Value)
    (hy : env y = some v) (hv : v.isControlFlow = false) (hc : bi copyName [v, v] = some v) :
    (denote' bi fuel (copyExpr y)).run env = (.val v, env) := by
  rw [copyExpr, denote'_app_run, denoteArgs'_cons_run, denote'_var_run, hy]
  cases v <;> simp at hv <;>
    simp only [denoteArgs'_cons_run, denote'_var_run, hy, denoteArgs'_nil_run, Option.map_some,
      hc]

/-- `rhsCopy comp` on a variable holding `v` returns `v`. -/
theorem rhsCopy_var_run (bi : Builtins) (fuel : Nat) (comp y : String) (env : Env) (v : Value)
    (hy : env y = some v) (hv : v.isControlFlow = false) (hc : bi copyName [v, v] = some v) :
    (denote' bi fuel (rhsCopy comp (.var y))).run env = (.val v, env) := by
  simp only [rhsCopy]
  split
  · rw [denote'_var_run, hy]
  · exact copyExpr_run bi fuel y env v hy hv hc

/-- **Update arm with a variable.**  `let s = struct_update#S#i#n(s, y); body` and its
    lowering, the copy of `y` into the component of field `f`, run `body` and
    `body'` from environments in which `s` stays flattened, when `y` holds the same
    value `v` on both sides and the builtin table copies `v`. -/
theorem flatUpdateCopy_sim (bi : Builtins) (fuel : Nat) (S s f y : String) (fs : List String)
    (i : Nat) (body body' : ImpExpr) (env envF : Env) (v : Value) (hU : UpdateSound bi S fs)
    (hi : fs[i]? = some f) (huniq : ∀ j, fs[j]? = some f → j = i)
    (hsf : StructFlatAt fs s env envF) (hy : env y = some v) (hyF : envF y = some v)
    (hv : v.isControlFlow = false) (hc : bi copyName [v, v] = some v) :
    ∃ env2 envF2,
      (denote' bi fuel (.letBind s
          (.app (_root_.Hax.structUpdateHead S i fs.length) [.var s, .var y]) body)).run env =
        (denote' bi fuel body).run env2 ∧
      (denote' bi fuel (.letBind (structCompName s f) (rhsCopy (structCompName s f) (.var y))
          body')).run envF = (denote' bi fuel body').run envF2 ∧
      StructFlatAt fs s env2 envF2 :=
  flatUpdate_sim bi fuel S s f fs i (.var y) _ body body' env env envF envF v hU hi huniq hsf
    (by rw [denote'_var_run, hy]) hv (rhsCopy_var_run bi fuel _ y envF v hyF hv hc)
    (fun _ _ _ => rfl)

/-- The variables `rs` are bound in `env` to values that are not control flow, and
    `env'` agrees with `env` on them. -/
def RetAt (rs : List String) (env env' : Env) : Prop :=
  ∀ x ∈ rs, (∃ v, env x = some v ∧ v.isControlFlow = false) ∧ env' x = env x

/-- `RetAt` on the first part of an append. -/
theorem RetAt.of_append_left {xs rs : List String} {env env' : Env}
    (h : RetAt (xs ++ rs) env env') : RetAt xs env env' :=
  fun x hx => h x (List.mem_append_left _ hx)

/-- `RetAt` on the second part of an append. -/
theorem RetAt.of_append_right {xs rs : List String} {env env' : Env}
    (h : RetAt (xs ++ rs) env env') : RetAt rs env env' :=
  fun x hx => h x (List.mem_append_right _ hx)

/-- `RetAt` on the tail of a list. -/
theorem RetAt.tail {x : String} {rs : List String} {env env' : Env}
    (h : RetAt (x :: rs) env env') : RetAt rs env env' :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- Evaluating a variable at the head of an argument list. -/
theorem denoteArgs'_var_cons (bi : Builtins) (fuel : Nat) (x : String) (es : List ImpExpr)
    (env : Env) (v : Value) (hx : env x = some v) (hv : v.isControlFlow = false) :
    (_root_.Hax.denoteArgs' bi fuel (.var x :: es)).run env =
      (((_root_.Hax.denoteArgs' bi fuel es).run env).1.map (v :: ·),
        ((_root_.Hax.denoteArgs' bi fuel es).run env).2) := by
  rw [denoteArgs'_cons_run, denote'_var_run, hx]
  cases v <;> simp at hv <;> rfl

/-- A list of variables evaluates to the same values from two environments that
    agree on them, changing neither. -/
theorem denoteArgs'_varsOf (bi : Builtins) (fuel : Nat) :
    ∀ (ys : List ImpExpr) (xs : List String), varsOf ys = some xs → ∀ env env',
      RetAt xs env env' → ∃ vals,
        (_root_.Hax.denoteArgs' bi fuel ys).run env = (some vals, env) ∧
        (_root_.Hax.denoteArgs' bi fuel ys).run env' = (some vals, env')
  | [], xs, h, env, env', _ => ⟨[], denoteArgs'_nil_run bi fuel env, denoteArgs'_nil_run bi fuel env'⟩
  | e :: es, xs, h, env, env', hR => by
    cases e
    case var x =>
      simp only [varsOf, Option.map_eq_some_iff] at h
      obtain ⟨xs', hxs', rfl⟩ := h
      obtain ⟨⟨v, hv, hcf⟩, he'⟩ := hR x List.mem_cons_self
      obtain ⟨vals, h1, h2⟩ := denoteArgs'_varsOf bi fuel es xs' hxs' env env' hR.tail
      refine ⟨v :: vals, ?_, ?_⟩
      · rw [denoteArgs'_var_cons bi fuel x es env v hv hcf, h1]; rfl
      · rw [denoteArgs'_var_cons bi fuel x es env' v (he'.trans hv) hcf, h2]; rfl
    all_goals simp [varsOf] at h

/-- A tuple whose components evaluate to `vals` evaluates to `.tuple vals`. -/
theorem denote'_tuple_run_some (bi : Builtins) (fuel : Nat) (ys : List ImpExpr) (env e1 : Env)
    (vals : List Value) (h : (_root_.Hax.denoteArgs' bi fuel ys).run env = (some vals, e1)) :
    (denote' bi fuel (.tuple ys)).run env = (.val (.tuple vals), e1) := by
  simp only [denote', StateT.run, bind, Bind.bind, StateT.bind] at h ⊢
  rw [h]
  rfl

/-- The components of a returned tuple with the variables `rs` evaluate to the same
    values from two environments that agree on `rs`, changing neither. -/
theorem denoteArgs'_retVars (bi : Builtins) (fuel : Nat) :
    ∀ (es : List ImpExpr) (rs : List String), retVars es = some rs → ∀ env env',
      RetAt rs env env' → ∃ vals,
        (_root_.Hax.denoteArgs' bi fuel es).run env = (some vals, env) ∧
        (_root_.Hax.denoteArgs' bi fuel es).run env' = (some vals, env')
  | [], rs, h, env, env', _ => ⟨[], denoteArgs'_nil_run bi fuel env, denoteArgs'_nil_run bi fuel env'⟩
  | e :: es, rs, h, env, env', hR => by
    cases e
    case var x =>
      simp only [retVars, Option.map_eq_some_iff] at h
      obtain ⟨rs', hrs', rfl⟩ := h
      obtain ⟨⟨v, hv, hcf⟩, he'⟩ := hR x List.mem_cons_self
      obtain ⟨vals, h1, h2⟩ := denoteArgs'_retVars bi fuel es rs' hrs' env env' hR.tail
      refine ⟨v :: vals, ?_, ?_⟩
      · rw [denoteArgs'_var_cons bi fuel x es env v hv hcf, h1]; rfl
      · rw [denoteArgs'_var_cons bi fuel x es env' v (he'.trans hv) hcf, h2]; rfl
    case tuple ys =>
      simp only [retVars, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨xs, hxs, rs', hrs', rfl⟩ := h
      obtain ⟨vs1, h1, h2⟩ := denoteArgs'_varsOf bi fuel ys xs hxs env env' hR.of_append_left
      obtain ⟨vals, h3, h4⟩ :=
        denoteArgs'_retVars bi fuel es rs' hrs' env env' hR.of_append_right
      refine ⟨.tuple vs1 :: vals, ?_, ?_⟩
      · rw [denoteArgs'_cons_run, denote'_tuple_run_some bi fuel ys env env vs1 h1]
        simp only [h3]; rfl
      · rw [denoteArgs'_cons_run, denote'_tuple_run_some bi fuel ys env' env' vs1 h2]
        simp only [h4]; rfl
    all_goals simp [retVars] at h

/-- **Named tuple return.**  A returned tuple with the variables `rs` (`retVars`)
    evaluates to a tuple `vals` without changing the environment, and to the same
    tuple from every environment that agrees on `rs`: the result is determined by
    the variables `rs`. -/
theorem namedRet_tuple_run (bi : Builtins) (fuel : Nat) (es : List ImpExpr) (rs : List String)
    (env : Env) (h : retVars es = some rs)
    (hb : ∀ x ∈ rs, ∃ v, env x = some v ∧ v.isControlFlow = false) :
    ∃ vals, (denote' bi fuel (.tuple es)).run env = (.val (.tuple vals), env) ∧
      ∀ env', (∀ x ∈ rs, env' x = env x) →
        (denote' bi fuel (.tuple es)).run env' = (.val (.tuple vals), env') := by
  obtain ⟨vals, h1, -⟩ := denoteArgs'_retVars bi fuel es rs h env env fun x hx => ⟨hb x hx, rfl⟩
  refine ⟨vals, denote'_tuple_run_some bi fuel es env env vals h1, fun env' he => ?_⟩
  obtain ⟨vals', h1', h2'⟩ :=
    denoteArgs'_retVars bi fuel es rs h env env' fun x hx => ⟨hb x hx, he x hx⟩
  rw [h1] at h1'
  cases h1'
  exact denote'_tuple_run_some bi fuel es env' env' vals h2'

/-- **Named tuple early return.**  `cfBreak` of a tuple with the variables `rs`
    breaks with a tuple `vals` determined by `rs`; its lowering `cfBreak ()` breaks
    with the unit value from the same environment, which holds the result in
    `rs`. -/
theorem namedRet_break_sim (bi : Builtins) (fuel : Nat) (es : List ImpExpr) (rs : List String)
    (env : Env) (h : retVars es = some rs)
    (hb : ∀ x ∈ rs, ∃ v, env x = some v ∧ v.isControlFlow = false) :
    ∃ vals,
      (denote' bi fuel (.cfBreak (.tuple es))).run env =
          (.val (.controlFlow true (.tuple vals)), env) ∧
      (denote' bi fuel (.cfBreak .unitVal)).run env = (.val (.controlFlow true .unit), env) ∧
      ∀ env', (∀ x ∈ rs, env' x = env x) →
        (denote' bi fuel (.tuple es)).run env' = (.val (.tuple vals), env') := by
  obtain ⟨vals, h1, h2⟩ := namedRet_tuple_run bi fuel es rs env h hb
  refine ⟨vals, ?_, ?_, h2⟩
  · rw [denote'_cfBreak_run', h1]
  · rw [denote'_cfBreak_run', denote'_unitVal_run]

/-- `namedRet` lowers a `cfBreak` of a tuple with the variables `rs` to `cfBreak ()`. -/
theorem namedRet_cfBreak (rs : List String) (tl : Bool) (es : List ImpExpr)
    (h : retVars es = some rs) :
    namedRet rs tl (.cfBreak (.tuple es)) = some (.cfBreak .unitVal) := by
  cases tl <;> simp [namedRet, h]

/-- `namedRet` lowers a tail tuple with the variables `rs` to the unit value. -/
theorem namedRet_tuple (rs : List String) (es : List ImpExpr) (h : retVars es = some rs) :
    namedRet rs true (.tuple es) = some .unitVal := by
  simp [namedRet, h]

/-! ## §10  Arrays of structs

The flattened program holds an array of `k`-field structs as the flat array of the
components of its elements (`ArrStructFlatAt`).  The arms read and write the flat
array through the builtins `index`, `array_update`, `Add` and `Mul`, whose readings
the predicates below state; each arm of §3a is simulated against `denote'`. -/

/-- `index` reads the element of an array at a natural index in range. -/
def ArrIndexSound (bi : Builtins) : Prop :=
  ∀ (vs : List Value) (m : Nat) (v : Value), vs[m]? = some v →
    bi "index" [.array vs, .int m] = some v

/-- `array_update` replaces the element of an array at a natural index (and leaves
    the array unchanged at an index out of range). -/
def ArrUpdateSound (bi : Builtins) : Prop :=
  ∀ (vs : List Value) (m : Nat) (v : Value),
    bi "array_update" [.array vs, .int m, v] = some (.array (vs.set m v))

/-- `len` returns the length of an array as an integer. -/
def LenSound (bi : Builtins) : Prop :=
  ∀ vs : List Value, bi "len" [.array vs] = some (.int vs.length)

/-- `Add` and `Mul` are the sum and the product of integers. -/
def IdxArithSound (bi : Builtins) : Prop :=
  ∀ x y : Int, bi "Add" [.int x, .int y] = some (.int (x + y)) ∧
    bi "Mul" [.int x, .int y] = some (.int (x * y))

/-- The array variable `a` of structs with `k` fields holds in `env` the array of
    the struct values of `rows`, each with `k` components, and in `envF` the flat
    array of their components. -/
def ArrStructFlatAt (k : Nat) (a : String) (env envF : Env) : Prop :=
  ∃ rows : List (List Value), env a = some (.array (rows.map (structVal k))) ∧
    (∀ r ∈ rows, r.length = k) ∧ envF a = some (.array rows.flatten)

/-- The value of an operand of a store: a literal or a bound variable. -/
def atomVal (env : Env) : ImpExpr → Option Value
  | .lit l => some (Value.ofLit l)
  | .var y => env y
  | _ => none

/-- A field position read by the field call `c`. -/
theorem fieldIdx_spec {fs : List String} {c : String} {off : Nat} (h : fieldIdx fs c = some off) :
    ∃ f, fs[off]? = some f ∧ c = "." ++ f := by
  unfold fieldIdx at h
  have hp := List.find?_some h
  cases hf : fs[off]? with
  | none => simp [hf] at hp
  | some f => simp only [hf, Option.map_some, beq_iff_eq, Option.some.injEq] at hp
              exact ⟨f, rfl, hp.symm⟩

/-- The index variable of an array binding of `n` is none of its component
    variables. -/
theorem elemIdxName_ne (n f : String) : elemIdxName n ≠ structCompName n f := by
  simp only [elemIdxName, structCompName, String.append_assoc, ne_eq]
  intro h
  have := congrArg String.toList h
  simp at this

section ArrSim

open _root_.Hax.ListBlocks

variable (bi : Builtins) (fuel : Nat)

/-- A call whose arguments evaluate to `vals` without changing the environment
    returns the builtin's value. -/
theorem app_run_of_args (f : String) (args : List ImpExpr) (vals : List Value) (v : Value)
    (env : Env) (h : (_root_.Hax.denoteArgs' bi fuel args).run env = (some vals, env))
    (hf : bi f vals = some v) : (denote' bi fuel (.app f args)).run env = (.val v, env) := by
  rw [denote'_app_run, h]; simp only [hf]

/-- An argument evaluating to a value that is not control flow, without changing the
    environment, prepends its value to the values of the remaining arguments. -/
theorem args_cons_of_val (e : ImpExpr) (es : List ImpExpr) (v : Value) (vals : List Value)
    (env : Env) (he : (denote' bi fuel e).run env = (.val v, env)) (hv : v.isControlFlow = false)
    (hes : (_root_.Hax.denoteArgs' bi fuel es).run env = (some vals, env)) :
    (_root_.Hax.denoteArgs' bi fuel (e :: es)).run env = (some (v :: vals), env) := by
  rw [denoteArgs'_cons_run, he]
  cases v <;> simp at hv <;> simp only [hes, Option.map_some]

/-- The flat index `Add(Mul(i, k), off)` of an index `i` holding the natural `j` is
    `j * k + off`. -/
theorem flatIdx_run (hA : IdxArithSound bi) (i : ImpExpr) (k off j : Nat) (env : Env)
    (hi : (denote' bi fuel i).run env = (.val (.int j), env)) :
    (denote' bi fuel (flatIdx i k off)).run env = (.val (.int ((j * k + off : Nat) : Int)), env) := by
  have hm : (denote' bi fuel (.app "Mul" [i, .lit (.int k)])).run env =
      (.val (.int ((j : Int) * k)), env) :=
    app_run_of_args bi fuel _ _ _ _ _
      (args_cons_of_val bi fuel _ _ _ _ _ hi rfl
        (args_cons_of_val bi fuel _ _ _ _ _ (denote'_lit_run bi fuel _ _) rfl
          (denoteArgs'_nil_run bi fuel env))) (hA _ _).2
  refine app_run_of_args bi fuel _ _ _ _ _
    (args_cons_of_val bi fuel _ _ _ _ _ hm rfl
      (args_cons_of_val bi fuel _ _ _ _ _ (denote'_lit_run bi fuel _ _) rfl
        (denoteArgs'_nil_run bi fuel env))) ?_
  simp only [Value.ofLit, (hA _ _).1, Nat.cast_add, Nat.cast_mul]

/-- **Element field read.**  The field call `c (index r i)` on element `j` of an
    array of structs and its lowering, the read of the flat array `a` at
    `j * k + off`, evaluate to the same value, changing neither environment.  The
    components of the element are not control flow. -/
theorem flatElemField_sim (hI : ArrIndexSound bi) (hA : IdxArithSound bi) (c a : String)
    (fs : List String) (off : Nat) (r i i' : ImpExpr) (env envF : Env)
    (rows : List (List Value)) (j : Nat) (hF : FieldSound bi fs) (hoff : fieldIdx fs c = some off)
    (hrow : ∀ w ∈ rows, w.length = fs.length) (hj : j < rows.length)
    (hcf : ∀ w ∈ rows[j], w.isControlFlow = false)
    (hr : (denote' bi fuel r).run env = (.val (.array (rows.map (structVal fs.length))), env))
    (haF : envF a = some (.array rows.flatten))
    (hi : (denote' bi fuel i).run env = (.val (.int j), env))
    (hi' : (denote' bi fuel i').run envF = (.val (.int j), envF)) :
    ∃ w, (denote' bi fuel (.app c [.app "index" [r, i]])).run env = (.val w, env) ∧
      (denote' bi fuel (.app "index" [.var a, flatIdx i' fs.length off])).run envF =
        (.val w, envF) := by
  obtain ⟨f, hf, rfl⟩ := fieldIdx_spec hoff
  have ho : off < fs.length := (List.getElem?_eq_some_iff.1 hf).1
  have hlen : (rows[j]).length = fs.length := hrow _ (List.getElem_mem hj)
  have hw : (rows[j])[off]? = some (rows[j])[off] := List.getElem?_eq_getElem (by omega)
  refine ⟨(rows[j])[off], ?_, ?_⟩
  · have hidx : (denote' bi fuel (.app "index" [r, i])).run env =
        (.val (structVal fs.length rows[j]), env) :=
      app_run_of_args bi fuel _ _ _ _ _
        (args_cons_of_val bi fuel _ _ _ _ _ hr rfl
          (args_cons_of_val bi fuel _ _ _ _ _ hi rfl (denoteArgs'_nil_run bi fuel env)))
        (hI _ _ _ (by simp [hj]))
    exact app_run_of_args bi fuel _ _ _ _ _
      (args_cons_of_val bi fuel _ _ _ _ _ hidx (structVal_not_cf hcf)
        (denoteArgs'_nil_run bi fuel env))
      ((hF _ off f hlen hf).trans hw)
  · refine app_run_of_args bi fuel _ _ _ _ _
      (args_cons_of_val bi fuel _ _ _ _ _ (by rw [denote'_var_run, haF]) rfl
        (args_cons_of_val bi fuel _ _ _ _ _ (flatIdx_run bi fuel hA i' _ off j envF hi') rfl
          (denoteArgs'_nil_run bi fuel envF))) (hI _ _ _ ?_)
    rw [flatten_getElem?_mul_add rows hrow hj ho, hw]

/-- The loads `bindElems a x k t ms body` of the components of the row `row` at
    index `j` of the flat array held by `a` bind `ms` to the components from `t` on
    and run `body`. -/
theorem bindElems_run (hI : ArrIndexSound bi) (hA : IdxArithSound bi) (a x : String) (k j : Nat)
    (flat row : List Value) (body : ImpExpr) (hflat : ∀ t < k, flat[j * k + t]? = row[t]?)
    (hrow : row.length = k) (hcf : ∀ w ∈ row, w.isControlFlow = false) :
    ∀ (ms : List String) (t : Nat) (envX : Env), envX a = some (.array flat) →
      envX x = some (.int j) → a ∉ ms → x ∉ ms → t + ms.length ≤ k →
      (denote' bi fuel (bindElems a x k t ms body)).run envX =
        (denote' bi fuel body).run (extendList envX ms (row.drop t))
  | [], t, envX, _, _, _, _, _ => by simp [bindElems, extendList]
  | m :: ms, t, envX, ha, hx, ham, hxm, hl => by
    simp only [List.mem_cons, not_or] at ham hxm
    simp only [List.length_cons] at hl
    have ht : t < row.length := by omega
    have hload : (denote' bi fuel (.app "index" [.var a, flatIdx (.var x) k t])).run envX =
        (.val row[t], envX) :=
      app_run_of_args bi fuel _ _ _ _ _
        (args_cons_of_val bi fuel _ _ _ _ _ (by rw [denote'_var_run, ha]) rfl
          (args_cons_of_val bi fuel _ _ _ _ _
            (flatIdx_run bi fuel hA _ k t j envX (by rw [denote'_var_run, hx])) rfl
            (denoteArgs'_nil_run bi fuel envX)))
        (hI _ _ _ (by rw [hflat t (by omega), List.getElem?_eq_getElem ht]))
    rw [bindElems, denote'_letBind_run_val bi fuel _ _ _ _ _ _ hload (hcf _ (List.getElem_mem ht)),
      bindElems_run hI hA a x k j flat row body hflat hrow hcf ms (t + 1) _
        (by rw [_root_.Hax.Env.extend_other _ _ _ _ ham.1]; exact ha)
        (by rw [_root_.Hax.Env.extend_other _ _ _ _ hxm.1]; exact hx)
        ham.2 hxm.2 (by omega),
      List.drop_eq_getElem_cons ht, extendList]

/-- **Element read into a struct variable.**  `let n = index(r, i); body` on element
    `j` of an array of structs runs `body` with `n` bound to the element, and its
    lowering, the binding of `n#idx` and the loads of the components of `n` from the
    flat array `a`, runs `body'` from an environment in which `n` is flattened; the
    lowering changes no variable other than `n#idx` and the components of `n`. -/
theorem flatElemBind_sim (hI : ArrIndexSound bi) (hA : IdxArithSound bi) (n a : String)
    (fs : List String) (r i i' body body' : ImpExpr) (env envF : Env)
    (rows : List (List Value)) (j : Nat) (hnd : fs.Nodup)
    (hrow : ∀ w ∈ rows, w.length = fs.length) (hj : j < rows.length)
    (hcf : ∀ w ∈ rows[j], w.isControlFlow = false)
    (hr : (denote' bi fuel r).run env = (.val (.array (rows.map (structVal fs.length))), env))
    (haF : envF a = some (.array rows.flatten))
    (hi : (denote' bi fuel i).run env = (.val (.int j), env))
    (hi' : (denote' bi fuel i').run envF = (.val (.int j), envF))
    (hna : a ≠ elemIdxName n) (hac : ∀ f ∈ fs, a ≠ structCompName n f) :
    ∃ envF2,
      (denote' bi fuel (.letBind n (.app "index" [r, i]) body)).run env =
          (denote' bi fuel body).run (env.extend n (structVal fs.length rows[j])) ∧
      (denote' bi fuel (.letBind (elemIdxName n) i'
          (bindElems a (elemIdxName n) fs.length 0 (fs.map (structCompName n)) body'))).run envF =
          (denote' bi fuel body').run envF2 ∧
      StructFlatAt fs n (env.extend n (structVal fs.length rows[j])) envF2 ∧
      ∀ y, y ≠ elemIdxName n → (∀ f ∈ fs, y ≠ structCompName n f) → envF2 y = envF y := by
  have hlen : (rows[j]).length = fs.length := hrow _ (List.getElem_mem hj)
  have hidx : (denote' bi fuel (.app "index" [r, i])).run env =
      (.val (structVal fs.length rows[j]), env) :=
    app_run_of_args bi fuel _ _ _ _ _
      (args_cons_of_val bi fuel _ _ _ _ _ hr rfl
        (args_cons_of_val bi fuel _ _ _ _ _ hi rfl (denoteArgs'_nil_run bi fuel env)))
      (hI _ _ _ (by simp [hj]))
  have hnm : elemIdxName n ∉ fs.map (structCompName n) := by
    simp only [List.mem_map, not_exists, not_and]; exact fun f _ h => elemIdxName_ne n f h.symm
  refine ⟨extendList (envF.extend (elemIdxName n) (.int j)) (fs.map (structCompName n)) rows[j],
    denote'_letBind_run_val bi fuel _ _ _ _ _ _ hidx (structVal_not_cf hcf), ?_, ?_, ?_⟩
  · rw [denote'_letBind_run_val bi fuel _ _ _ _ _ _ hi' rfl,
      bindElems_run bi fuel hI hA a (elemIdxName n) fs.length j rows.flatten rows[j] body'
        (fun t ht => flatten_getElem?_mul_add rows hrow hj ht) hlen hcf _ 0 _
        (by rw [_root_.Hax.Env.extend_other _ _ _ _ hna]; exact haF)
        (_root_.Hax.Env.extend_same _ _ _)
        (by simp only [List.mem_map, not_exists, not_and]; exact fun f hf h => hac f hf h.symm)
        hnm (by simp), List.drop_zero]
  · refine ⟨rows[j], _root_.Hax.Env.extend_same _ _ _, hlen, fun t f ht => ?_, hcf⟩
    exact extendList_get _ _ _ t _ (hnd.map fun _ _ h => structCompName_inj h)
      (by simp [hlen]) (by simp [ht])
  · intro y hy1 hy2
    rw [extendList_other _ _ _ y (by
      simp only [List.mem_map, not_exists, not_and]; exact fun f hf h => hy2 f hf h.symm),
      _root_.Hax.Env.extend_other _ _ _ _ hy1]

/-- A store operand evaluates to its value without changing the environment. -/
theorem storeAtom_run (a x : String) (e : ImpExpr) (env : Env) (w : Value)
    (hat : storeAtom a x e = true) (hw : atomVal env e = some w) :
    (denote' bi fuel e).run env = (.val w, env) := by
  cases e <;> simp only [storeAtom, reduceCtorEq] at hat
  · simp only [atomVal, Option.some.injEq] at hw; subst hw; exact denote'_lit_run bi fuel _ _
  · simp only [atomVal] at hw; rw [denote'_var_run, hw]

/-- Rebinding the array `a` leaves the value of a store operand unchanged. -/
theorem atomVal_extend (a x : String) (e : ImpExpr) (env : Env) (v : Value)
    (hat : storeAtom a x e = true) : atomVal (env.extend a v) e = atomVal env e := by
  cases e <;> simp only [storeAtom, reduceCtorEq] at hat
  · rfl
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hat
    simp only [atomVal]; exact _root_.Hax.Env.extend_other _ _ _ _ hat.1

/-- Rebinding the index variable `x` leaves the value of a store operand unchanged. -/
theorem atomVal_extend_idx (a x : String) (e : ImpExpr) (env : Env) (v : Value)
    (hat : storeAtom a x e = true) : atomVal (env.extend x v) e = atomVal env e := by
  cases e <;> simp only [storeAtom, reduceCtorEq] at hat
  · rfl
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hat
    simp only [atomVal]; exact _root_.Hax.Env.extend_other _ _ _ _ hat.2

/-- The stores `storeElems a x k t vs body` of the operands `vs` into row `j` of the
    flat array held by `a`, whose row `j` is `cur` and agrees with `ws` below `t`,
    run `body` from an environment in which `a` holds the flat array with row `j`
    replaced by `ws`, and which agrees with the start environment off `a`. -/
theorem storeElems_run (hU : ArrUpdateSound bi) (hA : IdxArithSound bi) (a x : String)
    (k j : Nat) (rows : List (List Value)) (hk : ∀ r ∈ rows, r.length = k) (hj : j < rows.length)
    (ws : List Value) (hws : ws.length = k) (hcf : ∀ w ∈ ws, w.isControlFlow = false)
    (body : ImpExpr) :
    ∀ (vs : List ImpExpr) (t : Nat) (cur : List Value) (envX : Env),
      t + vs.length = k → cur.length = k → (∀ s < t, cur[s]? = ws[s]?) →
      envX a = some (.array (rows.set j cur).flatten) → envX x = some (.int j) → a ≠ x →
      (∀ v ∈ vs, storeAtom a x v = true) →
      (∀ s (h : s < vs.length), atomVal envX vs[s] = ws[t + s]?) →
      ∃ envX', (denote' bi fuel (storeElems a x k t vs body)).run envX =
          (denote' bi fuel body).run envX' ∧
        envX' a = some (.array (rows.set j ws).flatten) ∧ ∀ y, y ≠ a → envX' y = envX y
  | [], t, cur, envX, hl, hc, hag, ha, _, _, _, _ => by
    refine ⟨envX, rfl, ?_, fun _ _ => rfl⟩
    have : cur = ws := List.ext_getElem? fun s => by
      by_cases hs : s < t
      · exact hag s hs
      · rw [List.getElem?_eq_none (by simp at hl; omega), List.getElem?_eq_none (by simp at hl; omega)]
    rw [ha, this]
  | v :: vs, t, cur, envX, hl, hc, hag, ha, hx, hax, hat, hvs => by
    simp only [List.length_cons] at hl
    have ht : t < k := by omega
    have htw : t < ws.length := by omega
    have hv0 : atomVal envX v = some ws[t] := by
      have := hvs 0 (by simp); simpa [List.getElem?_eq_getElem htw] using this
    have hrows' : ∀ r ∈ rows.set j cur, r.length = k := by
      intro r hr
      rcases List.mem_or_eq_of_mem_set hr with h | h
      · exact hk r h
      · rw [h]; exact hc
    have hj' : j < (rows.set j cur).length := by simpa using hj
    have hstore : (denote' bi fuel (.app "array_update" [.var a, flatIdx (.var x) k t, v])).run
        envX = (.val (.array (rows.set j (cur.set t ws[t])).flatten), envX) := by
      refine app_run_of_args bi fuel _ _ _ _ _
        (args_cons_of_val bi fuel _ _ _ _ _ (by rw [denote'_var_run, ha]) rfl
          (args_cons_of_val bi fuel _ _ _ _ _
            (flatIdx_run bi fuel hA _ k t j envX (by rw [denote'_var_run, hx])) rfl
            (args_cons_of_val bi fuel _ _ _ _ _
              (storeAtom_run bi fuel a x v envX _ (hat v List.mem_cons_self) hv0)
              (hcf _ (List.getElem_mem htw)) (denoteArgs'_nil_run bi fuel envX)))) ?_
      rw [hU, flatten_set_mul_add _ _ hrows' hj' (by omega)]
      simp [List.set_set]
    obtain ⟨envX', h1, h2, h3⟩ := storeElems_run hU hA a x k j rows hk hj ws hws hcf body vs
      (t + 1) (cur.set t ws[t]) (envX.extend a (.array (rows.set j (cur.set t ws[t])).flatten))
      (by omega) (by simp [hc])
      (fun s hs => by
        by_cases hst : s = t
        · subst hst; simp [List.getElem?_eq_getElem htw, hc, ht]
        · rw [List.getElem?_set_ne (Ne.symm hst)]; exact hag s (by omega))
      (_root_.Hax.Env.extend_same _ _ _)
      (by rw [_root_.Hax.Env.extend_other _ _ _ _ (Ne.symm hax)]; exact hx) hax
      (fun w hw => hat w (List.mem_cons_of_mem _ hw))
      (fun s hs => by
        rw [atomVal_extend a x _ envX _ (hat _ (List.mem_cons_of_mem _ (List.getElem_mem hs)))]
        have := hvs (s + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 s] using this)
    refine ⟨envX', ?_, h2, fun y hy => by rw [h3 y hy, _root_.Hax.Env.extend_other _ _ _ _ hy]⟩
    rw [storeElems, denote'_letBind_run_val bi fuel _ _ _ _ _ _ hstore rfl, h1]

/-- **Element write.**  `let a = array_update(a, i, x); body` of element `j` of an
    array of structs with the value `x` of fields `ws` runs `body` with row `j`
    replaced, and its lowering, the binding of `a#idx` and the stores of the
    operands `vs` of the fields, runs `body'` from an environment in which `a`
    holds the flat array with row `j` replaced; the lowering changes no variable
    other than `a` and `a#idx`. -/
theorem flatArrUpdate_sim (hU : ArrUpdateSound bi) (hA : IdxArithSound bi) (a : String)
    (k : Nat) (i i' x body body' : ImpExpr) (vs : List ImpExpr) (env envF : Env)
    (rows : List (List Value)) (j : Nat) (ws : List Value)
    (hrow : ∀ r ∈ rows, r.length = k) (hj : j < rows.length) (hws : ws.length = k)
    (hcf : ∀ w ∈ ws, w.isControlFlow = false)
    (ha : env a = some (.array (rows.map (structVal k))))
    (haF : envF a = some (.array rows.flatten))
    (hi : (denote' bi fuel i).run env = (.val (.int j), env))
    (hi' : (denote' bi fuel i').run envF = (.val (.int j), envF))
    (hx : (denote' bi fuel x).run env = (.val (structVal k ws), env))
    (hlen : vs.length = k) (hat : ∀ v ∈ vs, storeAtom a (elemIdxName a) v = true)
    (hvs : ∀ s (h : s < vs.length), atomVal envF vs[s] = ws[s]?)
    (hax : a ≠ elemIdxName a) :
    ∃ envF2,
      (denote' bi fuel (.letBind a (.app "array_update" [.var a, i, x]) body)).run env =
          (denote' bi fuel body).run
            (env.extend a (.array ((rows.set j ws).map (structVal k)))) ∧
      (denote' bi fuel (.letBind (elemIdxName a) i'
          (storeElems a (elemIdxName a) k 0 vs body'))).run envF =
          (denote' bi fuel body').run envF2 ∧
      envF2 a = some (.array (rows.set j ws).flatten) ∧
      ∀ y, y ≠ a → y ≠ elemIdxName a → envF2 y = envF y := by
  have hsrc : (denote' bi fuel (.app "array_update" [.var a, i, x])).run env =
      (.val (.array ((rows.set j ws).map (structVal k))), env) := by
    refine app_run_of_args bi fuel _ _ _ _ _
      (args_cons_of_val bi fuel _ _ _ _ _ (by rw [denote'_var_run, ha]) rfl
        (args_cons_of_val bi fuel _ _ _ _ _ hi rfl
          (args_cons_of_val bi fuel _ _ _ _ _ hx (structVal_not_cf hcf)
            (denoteArgs'_nil_run bi fuel env)))) ?_
    rw [hU, List.map_set]
  have hrj : (rows[j]).length = k := hrow _ (List.getElem_mem hj)
  obtain ⟨envF2, h1, h2, h3⟩ := storeElems_run bi fuel hU hA a (elemIdxName a) k j rows hrow hj
    ws hws hcf body' vs 0 rows[j] (envF.extend (elemIdxName a) (.int j)) (by omega) hrj
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (by rw [_root_.Hax.Env.extend_other _ _ _ _ hax, List.set_getElem_self]; exact haF)
    (_root_.Hax.Env.extend_same _ _ _) hax hat
    (fun s hs => by
      rw [atomVal_extend_idx a (elemIdxName a) _ envF _ (hat _ (List.getElem_mem hs)),
        Nat.zero_add]
      exact hvs s hs)
  refine ⟨envF2, denote'_letBind_run_val bi fuel _ _ _ _ _ _ hsrc rfl, ?_, h2, fun y hy1 hy2 => ?_⟩
  · rw [denote'_letBind_run_val bi fuel _ _ _ _ _ _ hi' rfl, h1]
  · rw [h3 y hy1, _root_.Hax.Env.extend_other _ _ _ _ hy2]

/-- **Length.**  `len r` of an array of length `N` and its lowering, the literal
    `N`, evaluate to the same value. -/
theorem flatLen_sim (hL : LenSound bi) (r : ImpExpr) (N : Nat) (env envF : Env)
    (vs : List Value) (hN : vs.length = N)
    (hr : (denote' bi fuel r).run env = (.val (.array vs), env)) :
    (denote' bi fuel (.app "len" [r])).run env = (.val (.int N), env) ∧
      (denote' bi fuel (.lit (.int N))).run envF = (.val (.int N), envF) :=
  ⟨app_run_of_args bi fuel _ _ _ _ _
      (args_cons_of_val bi fuel _ _ _ _ _ hr rfl (denoteArgs'_nil_run bi fuel env))
      (by rw [hL, hN]),
    denote'_lit_run bi fuel _ _⟩

end ArrSim

end CatCrypt.Crypto.Hax
