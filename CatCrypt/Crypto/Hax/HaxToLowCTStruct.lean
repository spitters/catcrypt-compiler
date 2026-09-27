/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit

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
`s.f`; hax-lean's parameter alias `let s = s` is dropped; `s` as an argument of
any other call is its component variables in field order, and elsewhere the
tuple of them.

**`Option` of a word.**  An `Option` variable `o` is the pair of a bool tag
`o#tag` and a payload word `o#val`.  `match o { None => e1, Some v => e2 }` is
the branch on the tag, with `o#val` in place of `v` in `e2`; the tag is read as
a public branch condition (whether a secret-dependent branch is admissible is
the business of the constant-time theorems, not of the front).  A function
returning an `Option` returns its tag in a variable `T` and its payload as the
result (`optRet`): `Some x` and `None` in tail position and as the payload of a
`cfBreak` (hax-lean's early return) set `T` and return `x` or the word `0`, so
the early return goes through the function-exit lowering `haxToLowCTFn` with a
word payload.

**Simulation.**  Field calls, update calls and `Some`/`None` are builtin calls
of `Hax.denote'`.  `FieldSound`, `UpdateSound` and `OptionSound` state that the
builtin table reads a struct as the flat tuple of its fields and builds `Option`
values; `StructFlatAt` and `OptFlatAt` relate the source environment to the
environment of the flattened program.  Each arm of the pass is simulated
against `denote'`.

## Main definitions

* `flatE` — the struct and `Option`-match flattening pass.
* `optRet` — the `Option` return lowering.
* `renameVar`, `renameSafe` — renaming a variable, and the syntactic condition
  under which the `Option` match arm renames.

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

The renaming step of the `Option` match arm (`renameVar` under `renameSafe`) has
no preservation theorem here.
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

/-- hax-lean's call name for the update of field `i` of the `n`-field struct `S`:
    `struct_update#S#i#n`. -/
def structUpdateName (S : String) (i n : Nat) : String :=
  "struct_update#" ++ S ++ "#" ++ toString i ++ "#" ++ toString n

/-- The fields of the struct variable `s`: those of its struct in the layout. -/
def structFields (L : StructLayout) (sv : StructVars) (s : String) : Option (List String) :=
  (List.lookup s sv).bind fun S => List.lookup S L

/-- The component variables of the struct variable `s` with fields `fs`, in field
    order. -/
def structComps (s : String) (fs : List String) : List ImpExpr :=
  fs.map fun f => .var (structCompName s f)

/-- The component read by the field call `c` on the struct variable `s`: the
    component variable of the field `f` with `c = "." ++ f`. -/
def projArm (L : StructLayout) (sv : StructVars) (c s : String) : Option String :=
  (structFields L sv s).bind fun fs => (fs.find? fun f => "." ++ f == c).map (structCompName s)

/-- The component rebound by the update call `c` on the struct variable `s`: the
    component variable of field `i` when `c = struct_update#S#i#n` for the struct
    `S` of `s` with `n` fields. -/
def updateArm (L : StructLayout) (sv : StructVars) (c s : String) : Option String :=
  (List.lookup s sv).bind fun S => (List.lookup S L).bind fun fs =>
    ((List.range fs.length).find? fun i => c == structUpdateName S i fs.length).bind fun i =>
      fs[i]?.map (structCompName s)

/-- A flattened update right-hand side that the rebinding accepts: anything but a
    variable other than the component itself (a `letBind` of one variable to
    another is an alias, which the front lowers to nothing). -/
def updateRhsOk (comp : String) : ImpExpr → Bool
  | .var x => x == comp
  | _ => true

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
    * `let s = struct_update#S#i#n(s, x); body` is `let s.f = x'; body'` for the
      field `f` of index `i`, where `x'` is the last argument of `val'`; refused
      when `x'` is a variable other than `s.f`;
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
          | some x' => if updateRhsOk comp x' then some (.letBind comp x' body') else none
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

mutual

/-- Flatten the struct variables `sv` (layout `L`) and match on the `Option`
    variables `ov`:
    * a field call `.f s` on a struct variable is the component variable `s.f`;
    * `let s = struct_update#S#i#n(s, x)` rebinds the component of field `i`;
    * hax-lean's parameter alias `let s = s` of a struct or `Option` variable is
      dropped;
    * a struct variable as an argument of any other call is its component
      variables in field order, and elsewhere the tuple of its component
      variables;
    * `match o { None => e1, Some v => e2 }` on an `Option` variable is the branch
      on its tag `o#tag`, with the payload `o#val` for `v` (`optMatchArm`).
    Returns `none` where a struct or `Option` variable occurs in a form the pass
    does not flatten. -/
def flatE (L : StructLayout) (sv : StructVars) (ov : List String) : ImpExpr → Option ImpExpr
  | .lit l => some (.lit l)
  | .var s =>
      match structFields L sv s with
      | some fs => some (.tuple (structComps s fs))
      | none => if ov.contains s then none else some (.var s)
  | .letBind n val body =>
      if optAlias ov n val then flatE L sv ov body
      else do
        let val' ← flatE L sv ov val
        let body' ← flatE L sv ov body
        letArm L sv n val val' body'
  | .lam ps b => do let b' ← flatE L sv ov b; pure (.lam ps b')
  | .app c args =>
      match projArgs L sv c args with
      | some comp => some (.var comp)
      | none => do let args' ← flatCallArgs L sv ov args; pure (.app c args')
  | .tuple es => do let es' ← flatList L sv ov es; pure (.tuple es')
  | .proj e i => do let e' ← flatE L sv ov e; pure (.proj e' i)
  | .ifThenElse c t e => do
      let c' ← flatE L sv ov c
      let t' ← flatE L sv ov t
      let e' ← flatE L sv ov e
      pure (.ifThenElse c' t' e')
  | .match_ (.var o) [(.somePat (.varPat v), e2), (.nonePat, e1)] => do
      let e2' ← flatE L sv ov e2
      let e1' ← flatE L sv ov e1
      optMatchArm ov o v e2' e1'
  | .match_ (.var o) [(.nonePat, e1), (.somePat (.varPat v), e2)] => do
      let e2' ← flatE L sv ov e2
      let e1' ← flatE L sv ov e1
      optMatchArm ov o v e2' e1'
  | .match_ s arms => do
      let s' ← flatE L sv ov s
      let arms' ← flatArms L sv ov arms
      pure (.match_ s' arms')
  | .unitVal => some .unitVal
  | .seq a b => do
      let a' ← flatE L sv ov a
      let b' ← flatE L sv ov b
      pure (.seq a' b')
  | .borrow e => do let e' ← flatE L sv ov e; pure (.borrow e')
  | .deref e => do let e' ← flatE L sv ov e; pure (.deref e')
  | .assign n r =>
      if (structFields L sv n).isSome || ov.contains n then none
      else do let r' ← flatE L sv ov r; pure (.assign n r')
  | .forLoop i lo hi b => do
      let lo' ← flatE L sv ov lo
      let hi' ← flatE L sv ov hi
      let b' ← flatE L sv ov b
      pure (.forLoop i lo' hi' b')
  | .forLoopRev i lo hi b => do
      let lo' ← flatE L sv ov lo
      let hi' ← flatE L sv ov hi
      let b' ← flatE L sv ov b
      pure (.forLoopRev i lo' hi' b')
  | .whileLoop c b => do
      let c' ← flatE L sv ov c
      let b' ← flatE L sv ov b
      pure (.whileLoop c' b')
  | .break_ none => some (.break_ none)
  | .break_ (some e) => do let e' ← flatE L sv ov e; pure (.break_ (some e'))
  | .continue_ => some .continue_
  | .earlyReturn e => do let e' ← flatE L sv ov e; pure (.earlyReturn e')
  | .questionMark e => do let e' ← flatE L sv ov e; pure (.questionMark e')
  | .forFold i lo hi b => do
      let lo' ← flatE L sv ov lo
      let hi' ← flatE L sv ov hi
      let b' ← flatE L sv ov b
      pure (.forFold i lo' hi' b')
  | .forFoldRev i lo hi b => do
      let lo' ← flatE L sv ov lo
      let hi' ← flatE L sv ov hi
      let b' ← flatE L sv ov b
      pure (.forFoldRev i lo' hi' b')
  | .whileFold c b => do
      let c' ← flatE L sv ov c
      let b' ← flatE L sv ov b
      pure (.whileFold c' b')
  | .forFoldReturn i lo hi b => do
      let lo' ← flatE L sv ov lo
      let hi' ← flatE L sv ov hi
      let b' ← flatE L sv ov b
      pure (.forFoldReturn i lo' hi' b')
  | .forFoldRevReturn i lo hi b => do
      let lo' ← flatE L sv ov lo
      let hi' ← flatE L sv ov hi
      let b' ← flatE L sv ov b
      pure (.forFoldRevReturn i lo' hi' b')
  | .whileFoldReturn c b => do
      let c' ← flatE L sv ov c
      let b' ← flatE L sv ov b
      pure (.whileFoldReturn c' b')
  | .cfBreak e => do let e' ← flatE L sv ov e; pure (.cfBreak e')
  | .cfContinue e => do let e' ← flatE L sv ov e; pure (.cfContinue e')
  | .cfBreakContinue e => do let e' ← flatE L sv ov e; pure (.cfBreakContinue e')
  | .typeAscription e t => do let e' ← flatE L sv ov e; pure (.typeAscription e' t)

/-- `flatE` on every expression of a list. -/
def flatList (L : StructLayout) (sv : StructVars) (ov : List String) :
    List ImpExpr → Option (List ImpExpr)
  | [] => some []
  | e :: es => do
      let e' ← flatE L sv ov e
      let es' ← flatList L sv ov es
      pure (e' :: es')

/-- The arguments of a call: a struct variable is its component variables in field
    order, any other argument is flattened by `flatE`. -/
def flatCallArgs (L : StructLayout) (sv : StructVars) (ov : List String) :
    List ImpExpr → Option (List ImpExpr)
  | [] => some []
  | e :: es => do
      let es' ← flatCallArgs L sv ov es
      match e with
      | .var s =>
          match structFields L sv s with
          | some fs => pure (structComps s fs ++ es')
          | none => do let e' ← flatE L sv ov e; pure (e' :: es')
      | _ => do let e' ← flatE L sv ov e; pure (e' :: es')

/-- `flatE` on every arm body of a match. -/
def flatArms (L : StructLayout) (sv : StructVars) (ov : List String) :
    List (ImpPat × ImpExpr) → Option (List (ImpPat × ImpExpr))
  | [] => some []
  | (p, e) :: rest => do
      let e' ← flatE L sv ov e
      let rest' ← flatArms L sv ov rest
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
      List.lookup S L = some fs ∧ c = structUpdateName S i fs.length ∧ fs[i]? = some f ∧
      comp = structCompName s f := by
  unfold updateArm at h
  cases hS : List.lookup s sv with
  | none => simp [hS] at h
  | some S =>
    cases hL : List.lookup S L with
    | none => simp [hS, hL] at h
    | some fs =>
      simp only [hS, hL, Option.bind_some] at h
      cases hi : (List.range fs.length).find? fun i => c == structUpdateName S i fs.length with
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

/-- `flatE` on a field call of a struct variable is the component variable. -/
theorem flatE_proj {L : StructLayout} {sv : StructVars} (ov : List String) {c s comp : String}
    (h : projArm L sv c s = some comp) :
    flatE L sv ov (.app c [.var s]) = some (.var comp) := by
  simp only [flatE, projArgs, h]

/-- `flatE` on an update of a struct variable whose flattened new value `x'` is
    accepted rebinds the component of the updated field. -/
theorem flatE_update {L : StructLayout} {sv : StructVars} (ov : List String)
    {c s comp : String} {fs : List String} {x x' body body' : ImpExpr}
    (h : updateArm L sv c s = some comp) (hs : structFields L sv s = some fs)
    (hxs : ∀ y, x = .var y → structFields L sv y = none)
    (hx : flatE L sv ov x = some x') (hb : flatE L sv ov body = some body')
    (hok : updateRhsOk comp x' = true) :
    flatE L sv ov (.letBind s (.app c [.var s, x]) body) =
      some (.letBind comp x' body') := by
  have hfx : flatCallArgs L sv ov [x] = some [x'] := by
    cases x <;> simp_all [flatCallArgs]
  have hpa : projArgs L sv c [.var s, x] = none := rfl
  have hca : flatCallArgs L sv ov [.var s, x] = some (structComps s fs ++ [x']) := by
    rw [flatCallArgs, hfx]; simp [hs]
  have hal : optAlias ov s (.app c [.var s, x]) = false := rfl
  simp only [flatE, hal, hpa, hca, hb, Option.bind_eq_bind, Option.bind_some]
  simp [letArm, h, hok]

/-! ## §6  Simulation of the arms against `denote'`

The flattened program runs in an environment `envF` holding the components of
each struct variable in its component variables (`StructFlatAt`) and the tag and
payload of each `Option` variable (`OptFlatAt`).  Field calls, update calls and
`Some`/`None` are builtins of `denote'`; `FieldSound`, `UpdateSound` and
`OptionSound` state that the builtin table reads a struct as the tuple of its
fields and builds `Option` values. -/

/-- The field calls of the layout `fs` read their component of a tuple with one
    component per field. -/
def FieldSound (bi : Builtins) (fs : List String) : Prop :=
  ∀ (vs : List Value) (i : Nat) (f : String), vs.length = fs.length → fs[i]? = some f →
    bi ("." ++ f) [.tuple vs] = vs[i]?

/-- The update calls of the struct `S` with fields `fs` replace one component of a
    tuple with one component per field. -/
def UpdateSound (bi : Builtins) (S : String) (fs : List String) : Prop :=
  ∀ (vs : List Value) (i : Nat) (v : Value), vs.length = fs.length → i < fs.length →
    bi (structUpdateName S i fs.length) [.tuple vs, v] = some (.tuple (vs.set i v))

/-- The builtin table builds `Option` values with `Some` and `None`. -/
def OptionSound (bi : Builtins) : Prop :=
  (∀ v, bi "Some" [v] = some (.option (some v))) ∧ bi "None" [] = some (.option none)

/-- The struct variable `s` with fields `fs` is a tuple with one component per
    field in `env`, and `envF` binds the component variable of each field to its
    component. -/
def StructFlatAt (fs : List String) (s : String) (env envF : Env) : Prop :=
  ∃ vs : List Value, env s = some (.tuple vs) ∧ vs.length = fs.length ∧
    ∀ (i : Nat) (f : String), fs[i]? = some f → envF (structCompName s f) = vs[i]?

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
  obtain ⟨vs, hs, hlen, hc⟩ := hsf
  have hlt : i < vs.length := by
    rw [hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
  refine ⟨vs[i], ?_, ?_⟩
  · rw [denote'_app_run, denoteArgs'_cons_run, denote'_var_run, hs]
    simp only [denoteArgs'_nil_run, Option.map_some]
    rw [hF vs i f hlen hi, List.getElem?_eq_getElem hlt]
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
      (denote' bi fuel (.letBind s (.app (structUpdateName S i fs.length) [.var s, x]) body)).run
          env = (denote' bi fuel body).run env2 ∧
      (denote' bi fuel (.letBind (structCompName s f) x' body')).run envF =
          (denote' bi fuel body').run envF2 ∧
      StructFlatAt fs s env2 envF2 := by
  obtain ⟨vs, hs, hlen, hc⟩ := hsf
  have hifs : i < fs.length := (List.getElem?_eq_some_iff.1 hi).1
  have hhead : (denote' bi fuel (.app (structUpdateName S i fs.length) [.var s, x])).run env =
      (.val (.tuple (vs.set i v)), env1) := by
    rw [denote'_app_run, denoteArgs'_cons_run, denote'_var_run, hs]
    simp only
    rw [denoteArgs'_cons_run, hx]
    cases v <;> simp at hv <;>
      simp only [denoteArgs'_nil_run, Option.map_some, hU vs i _ hlen hifs]
  refine ⟨env1.extend s (.tuple (vs.set i v)), envF1.extend (structCompName s f) v,
    denote'_letBind_run_val bi fuel _ _ _ _ _ _ hhead rfl,
    denote'_letBind_run_val bi fuel _ _ _ _ _ _ hx' hv, vs.set i v, ?_, ?_, ?_⟩
  · simp [_root_.Hax.Env.extend]
  · rw [List.length_set, hlen]
  · intro j g hj
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

end CatCrypt.Crypto.Hax
