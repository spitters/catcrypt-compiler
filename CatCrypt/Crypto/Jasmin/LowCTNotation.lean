/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import CatCrypt.Crypto.Jasmin.LowCTSyntax

/-!
# Notation for `LowCT` programs

`lowct% s` is a term of type `LowCT` and `sexpr% e` is a term of type `SExpr`.
Both are macros over the constructors: the notation expands to the constructor
term, so a definition written in the notation is syntactically the term a
theorem about the constructors mentions.

```text
def arithK : LowCT := lowct% t := a + b; r := t * c
```

expands to
`.RSeq (.RScalarSetExpr "t" (.SAdd (.SVar "a") (.SVar "b")))
  (.RScalarSetExpr "r" (.SMul (.SVar "t") (.SVar "c")))`.

An identifier in the notation denotes the name string of an object-language
variable: `t` stands for `"t"`, never for a Lean variable. A Lean term is
spliced in with `↑`: `↑body` in statement position is the `LowCT` term `body`,
`↑e` in expression position is an `SExpr` term, `↑x` in name position is a
`String` term and `↑n` in numeral position is a `Nat` term.

## Main definitions

* `lowctName`: the syntax category of variable names. An identifier or a string
  literal gives the name string; `↑t` gives the Lean term `t`.
* `lowctNat`: the syntax category of meta-level naturals: a numeral or `↑t`.
* `lowctLoc`: the syntax category of typed slots: `(x : τ)` is `⟨"x", τ⟩` and
  `↑t` is the `Located` term `t`.
* `lowctExpr`: the syntax category of scalar expressions, mapped to `SExpr`.
  Binary operators bind as in Rust: `*`, then `+` and `-`, then `<<` and `>>`,
  then `&`, then `^`, then `<`; all associate to the left.
* `lowctStmt`: the syntax category of commands, mapped to `LowCT`. `;` is
  `RSeq` and associates to the right.
* `sexpr% e` and `lowct% s`: the term-level entries.
* The `app_unexpander` functions print constructor terms in the notation in
  goals and hovers. A constructor without notation prints as a `↑` splice of
  its constructor term.

## Statement forms

| Notation | Constructor |
|---|---|
| `skip` | `RSkip` |
| `s₁; s₂` | `RSeq` |
| `let x; s` | `RLetU64Zero` |
| `let x : τ; s` | `RLetZero` |
| `x := lit n` | `RScalarSet` |
| `x := e` | `RScalarSetExpr` |
| `if x { s₁ } else { s₂ }` | `RIfNz` |
| `while x { s }` | `RWhileNz` |
| `for x < n { s }` | `RFor` |
| `for x < dyn e { s }` | `RForRuntime` |
| `(d : τ) := call f((a : τ), …)` | `RCall` |
| `[(d : τ), …] := call f((a : τ), …)` | `RCallN` |
| `(d : τ) := copy (s : τ)` | `RCopy` |
| `(d : τ) := (s : σ)[i]` | `RArrLoad` |
| `(d : τ) := (s : σ)[lit n]` | `RArrLoadLit` |
| `(a : σ)[i] := (s : τ)` | `RArrStore` |
| `(a : σ)[lit n] := (s : τ)` | `RArrStoreLit` |
| `(s)` | grouping, no constructor |
| `↑t` | the `LowCT` term `t` |

## Expression forms

| Notation | Constructor |
|---|---|
| `x` | `SVar` |
| `7` | `SLit` |
| `a + b`, `a - b`, `a * b` | `SAdd`, `SSub`, `SMul` |
| `a << b`, `a >> b` | `SShl`, `SShr` |
| `a & b`, `a ^ b` | `SAnd`, `SXor` |
| `a < b` | `SLt` |
| `asr(a, b)` | `SAsr` |
| `smul(a, b)` | `SMulS` |
| `mulhi(a, b)`, `mulhis(a, b)` | `SMulHiU`, `SMulHiS` |
| `x[n]` | `SLimb` |
| `(e)` | grouping, no constructor |
| `↑t` | the `SExpr` term `t` |

The words `lit`, `dyn`, `call`, `copy`, `asr`, `smul`, `mulhi` and `mulhis` are
matched as identifiers and are not reserved: they stay usable as Lean
identifiers and as object-language variable names.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCTNotation

open CatCrypt.Crypto.Jasmin.LowCT
open Lean

/-! ## Names, naturals and typed slots -/

/-- A variable name: an identifier or a string literal for the name string, or
    `↑t` for a Lean term `t : String`. -/
declare_syntax_cat lowctName
@[inherit_doc Lean.Parser.Category.lowctName]
syntax (name := nmIdent) ident : lowctName
@[inherit_doc Lean.Parser.Category.lowctName]
syntax (name := nmStr) str : lowctName
@[inherit_doc Lean.Parser.Category.lowctName]
syntax (name := nmTerm) "↑" term:max : lowctName

/-- A meta-level natural: a numeral, or `↑t` for a Lean term `t : Nat`. -/
declare_syntax_cat lowctNat
@[inherit_doc Lean.Parser.Category.lowctNat]
syntax (name := natNum) num : lowctNat
@[inherit_doc Lean.Parser.Category.lowctNat]
syntax (name := natTerm) "↑" term:max : lowctNat

/-- A typed slot: `(x : τ)` for `⟨"x", τ⟩`, or `↑t` for a Lean term
    `t : Located`. -/
declare_syntax_cat lowctLoc
@[inherit_doc Lean.Parser.Category.lowctLoc]
syntax (name := locMk) "(" lowctName " : " term ")" : lowctLoc
@[inherit_doc Lean.Parser.Category.lowctLoc]
syntax (name := locTerm) "↑" term:max : lowctLoc

/-- `lowctName% x` is the `String` a name denotes. -/
syntax:max "lowctName% " lowctName : term
/-- `lowctNat% n` is the `Nat` a meta-level natural denotes. -/
syntax:max "lowctNat% " lowctNat : term
/-- `lowctLoc% l` is the `Located` a typed slot denotes. -/
syntax:max "lowctLoc% " lowctLoc : term

macro_rules
  | `(lowctName% $x:ident) =>
      pure (Syntax.mkStrLit (x.getId.eraseMacroScopes.toString (escape := false)))
  | `(lowctName% $s:str) => pure s
  | `(lowctName% ↑$t) => pure t

macro_rules
  | `(lowctNat% $n:num) => pure n
  | `(lowctNat% ↑$t) => pure t

macro_rules
  | `(lowctLoc% ($x:lowctName : $t)) => `(Located.mk (lowctName% $x) $t)
  | `(lowctLoc% ↑$t) => pure t

/-! ## Scalar expressions -/

/-- A scalar expression, mapped to `SExpr`. -/
declare_syntax_cat lowctExpr (behavior := both)

/-- A variable read `SVar`, by identifier or by string literal. -/
syntax:max (name := exVar) ident : lowctExpr
@[inherit_doc exVar]
syntax:max (name := exVarStr) str : lowctExpr
/-- A literal `SLit`. -/
syntax:max (name := exLit) num : lowctExpr
/-- A Lean term of type `SExpr`. -/
syntax:max (name := exTerm) "↑" term:max : lowctExpr
/-- Grouping. -/
syntax:max (name := exParen) "(" lowctExpr ")" : lowctExpr
/-- The limb read `SLimb x n`. With a spliced name the bracket is set off by a
    space, `↑x [n]`, since `↑x[n]` splices the Lean term `x[n]`. -/
syntax:max (name := exLimb) lowctName "[" lowctNat "]" : lowctExpr
/-- The arithmetic shift right `SAsr`. -/
syntax:max (name := exAsr) &"asr" noWs "(" lowctExpr ", " lowctExpr ")" : lowctExpr
/-- The signed multiplication `SMulS`. -/
syntax:max (name := exMulS) &"smul" noWs "(" lowctExpr ", " lowctExpr ")" : lowctExpr
/-- The high word of the unsigned product, `SMulHiU`. -/
syntax:max (name := exMulHiU) &"mulhi" noWs "(" lowctExpr ", " lowctExpr ")" : lowctExpr
/-- The high word of the signed product, `SMulHiS`. -/
syntax:max (name := exMulHiS) &"mulhis" noWs "(" lowctExpr ", " lowctExpr ")" : lowctExpr
/-- The binary operators of `SExpr`, left associative, with the precedence
    order of Rust. -/
syntax:70 (name := exMul) lowctExpr:70 " * " lowctExpr:71 : lowctExpr
@[inherit_doc exMul]
syntax:65 (name := exAdd) lowctExpr:65 " + " lowctExpr:66 : lowctExpr
@[inherit_doc exMul]
syntax:65 (name := exSub) lowctExpr:65 " - " lowctExpr:66 : lowctExpr
@[inherit_doc exMul]
syntax:60 (name := exShl) lowctExpr:60 " << " lowctExpr:61 : lowctExpr
@[inherit_doc exMul]
syntax:60 (name := exShr) lowctExpr:60 " >> " lowctExpr:61 : lowctExpr
@[inherit_doc exMul]
syntax:58 (name := exAnd) lowctExpr:58 " & " lowctExpr:59 : lowctExpr
@[inherit_doc exMul]
syntax:57 (name := exXor) lowctExpr:57 " ^ " lowctExpr:58 : lowctExpr
@[inherit_doc exMul]
syntax:50 (name := exLt) lowctExpr:50 " < " lowctExpr:51 : lowctExpr

/-- `sexpr% e` is the `SExpr` term the scalar expression `e` denotes. -/
syntax:min (name := sexprTerm) "sexpr% " lowctExpr : term

macro_rules
  | `(sexpr% $x:ident) => `(SExpr.SVar (lowctName% $x:ident))
  | `(sexpr% $s:str) => `(SExpr.SVar $s)
  | `(sexpr% $n:num) => `(SExpr.SLit $n)
  | `(sexpr% ↑$t) => pure t
  | `(sexpr% ($e)) => `(sexpr% $e)
  | `(sexpr% $x:lowctName[$n]) => `(SExpr.SLimb (lowctName% $x) (lowctNat% $n))
  | `(sexpr% asr($a, $b)) => `(SExpr.SAsr (sexpr% $a) (sexpr% $b))
  | `(sexpr% smul($a, $b)) => `(SExpr.SMulS (sexpr% $a) (sexpr% $b))
  | `(sexpr% mulhi($a, $b)) => `(SExpr.SMulHiU (sexpr% $a) (sexpr% $b))
  | `(sexpr% mulhis($a, $b)) => `(SExpr.SMulHiS (sexpr% $a) (sexpr% $b))
  | `(sexpr% $a * $b) => `(SExpr.SMul (sexpr% $a) (sexpr% $b))
  | `(sexpr% $a + $b) => `(SExpr.SAdd (sexpr% $a) (sexpr% $b))
  | `(sexpr% $a - $b) => `(SExpr.SSub (sexpr% $a) (sexpr% $b))
  | `(sexpr% $a << $b) => `(SExpr.SShl (sexpr% $a) (sexpr% $b))
  | `(sexpr% $a >> $b) => `(SExpr.SShr (sexpr% $a) (sexpr% $b))
  | `(sexpr% $a & $b) => `(SExpr.SAnd (sexpr% $a) (sexpr% $b))
  | `(sexpr% $a ^ $b) => `(SExpr.SXor (sexpr% $a) (sexpr% $b))
  | `(sexpr% $a < $b) => `(SExpr.SLt (sexpr% $a) (sexpr% $b))

/-! ## Commands -/

/-- A command, mapped to `LowCT`. -/
declare_syntax_cat lowctStmt

/-- The empty command `RSkip`. -/
syntax:max (name := stSkip) "skip" : lowctStmt
/-- A Lean term of type `LowCT`. -/
syntax:max (name := stTerm) "↑" term:max : lowctStmt
/-- Grouping. -/
syntax:max (name := stParen) "(" lowctStmt ")" : lowctStmt
/-- The scalar assignment `RScalarSetExpr x e`. -/
syntax:max (name := stSet) lowctName " := " lowctExpr : lowctStmt
/-- The constant scalar assignment `RScalarSet x n`. -/
syntax:max (name := stSetLit) lowctName " := " &"lit " lowctNat : lowctStmt
/-- The conditional `RIfNz x s₁ s₂`: `s₁` when the scalar `x` is nonzero. -/
syntax:max (name := stIf)
  "if " lowctName " {" lowctStmt "}" " else " "{" lowctStmt "}" : lowctStmt
/-- The loop `RWhileNz x s`. -/
syntax:max (name := stWhile) "while " lowctName " {" lowctStmt "}" : lowctStmt
/-- The counted loop `RFor x n s`: `x` runs over `0, …, n - 1`. -/
syntax:max (name := stFor) "for " lowctName " < " lowctNat " {" lowctStmt "}" : lowctStmt
/-- The counted loop `RForRuntime x e s`, whose trip count is the value of the
    expression `e` in the entry state. -/
syntax:max (name := stForDyn)
  "for " lowctName " < " &"dyn " lowctExpr " {" lowctStmt "}" : lowctStmt
/-- The leaf call `RCall f d args`. -/
syntax:max (name := stCall)
  lowctLoc " := " &"call " lowctName noWs "(" lowctLoc,* ")" : lowctStmt
/-- The leaf call with several destinations, `RCallN f ds args`. -/
syntax:max (name := stCallN)
  "[" lowctLoc,* "]" " := " &"call " lowctName noWs "(" lowctLoc,* ")" : lowctStmt
/-- The whole-slot copy `RCopy d s`. -/
syntax:max (name := stCopy) lowctLoc " := " &"copy " lowctLoc : lowctStmt
/-- The array read `RArrLoad d s i` at the index held by the scalar `i`. -/
syntax:max (name := stArrLoad) lowctLoc " := " lowctLoc "[" lowctName "]" : lowctStmt
/-- The array read `RArrLoadLit d s n` at the constant index `n`. -/
syntax:max (name := stArrLoadLit)
  lowctLoc " := " lowctLoc "[" &"lit " lowctNat "]" : lowctStmt
/-- The array write `RArrStore a i s` at the index held by the scalar `i`. -/
syntax:max (name := stArrStore) lowctLoc "[" lowctName "]" " := " lowctLoc : lowctStmt
/-- The array write `RArrStoreLit a n s` at the constant index `n`. -/
syntax:max (name := stArrStoreLit)
  lowctLoc "[" &"lit " lowctNat "]" " := " lowctLoc : lowctStmt
/-- The scalar declaration `RLetU64Zero x s`; `s` extends to the end of the
    enclosing sequence. -/
syntax:1 (name := stLetU64) "let " lowctName "; " lowctStmt:1 : lowctStmt
/-- The typed declaration `RLetZero x τ s`; `s` extends to the end of the
    enclosing sequence. -/
syntax:1 (name := stLet) "let " lowctName " : " term:max "; " lowctStmt:1 : lowctStmt
/-- Sequencing `RSeq s₁ s₂`, right associative. -/
syntax:1 (name := stSeq) lowctStmt:2 "; " lowctStmt:1 : lowctStmt

/-- `lowct% s` is the `LowCT` term the command `s` denotes. -/
syntax:min (name := lowctTerm) "lowct% " lowctStmt : term

macro_rules
  | `(lowct% skip) => `(LowCT.RSkip)
  | `(lowct% ↑$t) => pure t
  | `(lowct% ($s)) => `(lowct% $s)
  | `(lowct% $x:lowctName := $e:lowctExpr) =>
      `(LowCT.RScalarSetExpr (lowctName% $x) (sexpr% $e))
  | `(lowct% $x:lowctName := lit $n:lowctNat) =>
      `(LowCT.RScalarSet (lowctName% $x) (lowctNat% $n))
  | `(lowct% if $x { $s } else { $t }) =>
      `(LowCT.RIfNz (lowctName% $x) (lowct% $s) (lowct% $t))
  | `(lowct% while $x { $s }) => `(LowCT.RWhileNz (lowctName% $x) (lowct% $s))
  | `(lowct% for $x < $n:lowctNat { $s }) =>
      `(LowCT.RFor (lowctName% $x) (lowctNat% $n) (lowct% $s))
  | `(lowct% for $x < dyn $e:lowctExpr { $s }) =>
      `(LowCT.RForRuntime (lowctName% $x) (sexpr% $e) (lowct% $s))
  | `(lowct% $d:lowctLoc := call $f:lowctName($args,*)) => do
      let as ← args.getElems.mapM fun a => `(lowctLoc% $a)
      `(LowCT.RCall (lowctName% $f) (lowctLoc% $d) [$as,*])
  | `(lowct% [$ds,*] := call $f:lowctName($args,*)) => do
      let ds ← ds.getElems.mapM fun a => `(lowctLoc% $a)
      let as ← args.getElems.mapM fun a => `(lowctLoc% $a)
      `(LowCT.RCallN (lowctName% $f) [$ds,*] [$as,*])
  | `(lowct% $d:lowctLoc := copy $s:lowctLoc) =>
      `(LowCT.RCopy (lowctLoc% $d) (lowctLoc% $s))
  | `(lowct% $d:lowctLoc := $s:lowctLoc[$i:lowctName]) =>
      `(LowCT.RArrLoad (lowctLoc% $d) (lowctLoc% $s) (lowctName% $i))
  | `(lowct% $d:lowctLoc := $s:lowctLoc[lit $n:lowctNat]) =>
      `(LowCT.RArrLoadLit (lowctLoc% $d) (lowctLoc% $s) (lowctNat% $n))
  | `(lowct% $a:lowctLoc[$i:lowctName] := $s:lowctLoc) =>
      `(LowCT.RArrStore (lowctLoc% $a) (lowctName% $i) (lowctLoc% $s))
  | `(lowct% $a:lowctLoc[lit $n:lowctNat] := $s:lowctLoc) =>
      `(LowCT.RArrStoreLit (lowctLoc% $a) (lowctNat% $n) (lowctLoc% $s))
  | `(lowct% let $x:lowctName; $s) => `(LowCT.RLetU64Zero (lowctName% $x) (lowct% $s))
  | `(lowct% let $x:lowctName : $t; $s) =>
      `(LowCT.RLetZero (lowctName% $x) $t (lowct% $s))
  | `(lowct% $s; $t) => `(LowCT.RSeq (lowct% $s) (lowct% $t))

/-! ## Printing -/

open Lean.PrettyPrinter

meta section

/-- The words that a name string must avoid to print as an identifier. -/
def nameKeywords : List String :=
  ["skip", "if", "else", "while", "for", "let", "lit", "dyn", "call", "copy", "asr", "smul",
   "mulhi", "mulhis", "in", "do", "fun", "then", "at", "from", "have", "show", "by"]

/-- The identifier a name string prints as, when the string is a letter
    followed by letters, digits and underscores and is not a keyword. -/
def nameIdent? (s : String) : Option Ident :=
  match s.toList with
  | [] => none
  | c :: cs =>
    if c.isAlpha && cs.all (fun d => d.isAlphanum || d == '_') && !nameKeywords.contains s then
      some (mkIdent (Name.mkSimple s))
    else none

/-- The name syntax of a printed `String` term. -/
def nameOfTerm (t : Term) : UnexpandM (TSyntax `lowctName) :=
  match t with
  | `($s:str) =>
    match nameIdent? s.getString with
    | some x => `(lowctName| $x:ident)
    | none => `(lowctName| $s:str)
  | _ => `(lowctName| ↑$t)

/-- The numeral syntax of a printed `Nat` term. -/
def natOfTerm (t : Term) : UnexpandM (TSyntax `lowctNat) :=
  match t with
  | `($n:num) => `(lowctNat| $n:num)
  | _ => `(lowctNat| ↑$t)

/-- The slot syntax of a printed `Located` term. -/
def locOfTerm (t : Term) : UnexpandM (TSyntax `lowctLoc) := do
  match t with
  | `(⟨$x, $ty⟩) => let x ← nameOfTerm x; `(lowctLoc| ($x : $ty))
  | `({ locVar := $x, locSrc := $ty }) => let x ← nameOfTerm x; `(lowctLoc| ($x : $ty))
  | _ => `(lowctLoc| ↑$t)

/-- The slot syntax of the elements of a printed `List Located` term. -/
def locsOfTerm (t : Term) : UnexpandM (Array (TSyntax `lowctLoc)) :=
  match t with
  | `([$xs,*]) => xs.getElems.mapM locOfTerm
  | _ => throw ()

/-- The expression syntax of a printed `SExpr` term. -/
def exprOfTerm (t : Term) : UnexpandM (TSyntax `lowctExpr) :=
  match t with
  | `(sexpr% $e) => pure e
  | _ => `(lowctExpr| ↑$t)

/-- The command syntax of a printed `LowCT` term. -/
def stmtOfTerm (t : Term) : UnexpandM (TSyntax `lowctStmt) :=
  match t with
  | `(lowct% $s) => pure s
  | _ => `(lowctStmt| ↑$t)

/-- The precedence of an expression syntax node. -/
def exprPrec (e : Syntax) : Nat :=
  let k := e.getKind
  if k == ``exMul then 70
  else if k == ``exAdd || k == ``exSub then 65
  else if k == ``exShl || k == ``exShr then 60
  else if k == ``exAnd then 58
  else if k == ``exXor then 57
  else if k == ``exLt then 50
  else 1024

/-- Parenthesise an expression whose precedence is below `p`. -/
def parenExpr (p : Nat) (e : TSyntax `lowctExpr) : UnexpandM (TSyntax `lowctExpr) :=
  if exprPrec e < p then `(lowctExpr| ($e)) else pure e

/-- Parenthesise a command that is a sequence or a declaration. -/
def parenStmt (s : TSyntax `lowctStmt) : UnexpandM (TSyntax `lowctStmt) :=
  let k := s.raw.getKind
  if k == ``stSeq || k == ``stLet || k == ``stLetU64 then `(lowctStmt| ($s)) else pure s

/-- The unexpander of a left-associative binary operator of precedence `p`. -/
def unexpandBin (p : Nat)
    (mk : TSyntax `lowctExpr → TSyntax `lowctExpr → UnexpandM (TSyntax `lowctExpr)) :
    Unexpander
  | `($_ $a $b) => do
    let a ← parenExpr p (← exprOfTerm a)
    let b ← parenExpr (p + 1) (← exprOfTerm b)
    let e ← mk a b
    `(sexpr% $e)
  | _ => throw ()

/-- The unexpander of a binary operator written as a function. -/
def unexpandFn
    (mk : TSyntax `lowctExpr → TSyntax `lowctExpr → UnexpandM (TSyntax `lowctExpr)) :
    Unexpander
  | `($_ $a $b) => do
    let e ← mk (← exprOfTerm a) (← exprOfTerm b)
    `(sexpr% $e)
  | _ => throw ()

/-- `SExpr.SVar` with a literal name prints as the name. -/
@[app_unexpander SExpr.SVar] def unexpandSVar : Unexpander
  | `($_ $s:str) =>
    match nameIdent? s.getString with
    | some x => `(sexpr% $x:ident)
    | none => `(sexpr% $s:str)
  | _ => throw ()

/-- `SExpr.SLit` with a numeral prints as the numeral. -/
@[app_unexpander SExpr.SLit] def unexpandSLit : Unexpander
  | `($_ $n:num) => `(sexpr% $n:num)
  | _ => throw ()

/-- `SExpr.SLimb x n` with a literal name prints as `x[n]`. -/
@[app_unexpander SExpr.SLimb] def unexpandSLimb : Unexpander
  | `($_ $x:str $n) => do
    let x ← nameOfTerm x
    let n ← natOfTerm n
    `(sexpr% $x:lowctName[$n])
  | _ => throw ()

@[app_unexpander SExpr.SMul, inherit_doc unexpandBin] def unexpandSMul : Unexpander :=
  unexpandBin 70 fun a b => `(lowctExpr| $a * $b)
@[app_unexpander SExpr.SAdd, inherit_doc unexpandBin] def unexpandSAdd : Unexpander :=
  unexpandBin 65 fun a b => `(lowctExpr| $a + $b)
@[app_unexpander SExpr.SSub, inherit_doc unexpandBin] def unexpandSSub : Unexpander :=
  unexpandBin 65 fun a b => `(lowctExpr| $a - $b)
@[app_unexpander SExpr.SShl, inherit_doc unexpandBin] def unexpandSShl : Unexpander :=
  unexpandBin 60 fun a b => `(lowctExpr| $a << $b)
@[app_unexpander SExpr.SShr, inherit_doc unexpandBin] def unexpandSShr : Unexpander :=
  unexpandBin 60 fun a b => `(lowctExpr| $a >> $b)
@[app_unexpander SExpr.SAnd, inherit_doc unexpandBin] def unexpandSAnd : Unexpander :=
  unexpandBin 58 fun a b => `(lowctExpr| $a & $b)
@[app_unexpander SExpr.SXor, inherit_doc unexpandBin] def unexpandSXor : Unexpander :=
  unexpandBin 57 fun a b => `(lowctExpr| $a ^ $b)
@[app_unexpander SExpr.SLt, inherit_doc unexpandBin] def unexpandSLt : Unexpander :=
  unexpandBin 50 fun a b => `(lowctExpr| $a < $b)
@[app_unexpander SExpr.SAsr, inherit_doc unexpandFn] def unexpandSAsr : Unexpander :=
  unexpandFn fun a b => `(lowctExpr| asr($a, $b))
@[app_unexpander SExpr.SMulS, inherit_doc unexpandFn] def unexpandSMulS : Unexpander :=
  unexpandFn fun a b => `(lowctExpr| smul($a, $b))
@[app_unexpander SExpr.SMulHiU, inherit_doc unexpandFn] def unexpandSMulHiU : Unexpander :=
  unexpandFn fun a b => `(lowctExpr| mulhi($a, $b))
@[app_unexpander SExpr.SMulHiS, inherit_doc unexpandFn] def unexpandSMulHiS : Unexpander :=
  unexpandFn fun a b => `(lowctExpr| mulhis($a, $b))

/-- `LowCT.RSkip` prints as `skip`. -/
@[app_unexpander LowCT.RSkip] def unexpandRSkip : Unexpander
  | `($_) => `(lowct% skip)

/-- `LowCT.RSeq` prints as `s₁; s₂`. -/
@[app_unexpander LowCT.RSeq] def unexpandRSeq : Unexpander
  | `($_ $a $b) => do
    let a ← parenStmt (← stmtOfTerm a)
    let b ← stmtOfTerm b
    `(lowct% $a; $b)
  | _ => throw ()

/-- `LowCT.RScalarSetExpr` prints as `x := e`. -/
@[app_unexpander LowCT.RScalarSetExpr] def unexpandRScalarSetExpr : Unexpander
  | `($_ $x $e) => do
    let x ← nameOfTerm x
    let e ← exprOfTerm e
    `(lowct% $x:lowctName := $e:lowctExpr)
  | _ => throw ()

/-- `LowCT.RScalarSet` prints as `x := lit n`. -/
@[app_unexpander LowCT.RScalarSet] def unexpandRScalarSet : Unexpander
  | `($_ $x $n) => do
    let x ← nameOfTerm x
    let n ← natOfTerm n
    `(lowct% $x:lowctName := lit $n:lowctNat)
  | _ => throw ()

/-- `LowCT.RIfNz` prints as `if x { s₁ } else { s₂ }`. -/
@[app_unexpander LowCT.RIfNz] def unexpandRIfNz : Unexpander
  | `($_ $x $s $t) => do
    let x ← nameOfTerm x
    let s ← stmtOfTerm s
    let t ← stmtOfTerm t
    `(lowct% if $x { $s } else { $t })
  | _ => throw ()

/-- `LowCT.RWhileNz` prints as `while x { s }`. -/
@[app_unexpander LowCT.RWhileNz] def unexpandRWhileNz : Unexpander
  | `($_ $x $s) => do
    let x ← nameOfTerm x
    let s ← stmtOfTerm s
    `(lowct% while $x { $s })
  | _ => throw ()

/-- `LowCT.RFor` prints as `for x < n { s }`. -/
@[app_unexpander LowCT.RFor] def unexpandRFor : Unexpander
  | `($_ $x $n $s) => do
    let x ← nameOfTerm x
    let n ← natOfTerm n
    let s ← stmtOfTerm s
    `(lowct% for $x < $n:lowctNat { $s })
  | _ => throw ()

/-- `LowCT.RForRuntime` prints as `for x < dyn e { s }`. -/
@[app_unexpander LowCT.RForRuntime] def unexpandRForRuntime : Unexpander
  | `($_ $x $e $s) => do
    let x ← nameOfTerm x
    let e ← exprOfTerm e
    let s ← stmtOfTerm s
    `(lowct% for $x < dyn $e:lowctExpr { $s })
  | _ => throw ()

/-- `LowCT.RLetU64Zero` prints as `let x; s`. -/
@[app_unexpander LowCT.RLetU64Zero] def unexpandRLetU64Zero : Unexpander
  | `($_ $x $s) => do
    let x ← nameOfTerm x
    let s ← stmtOfTerm s
    `(lowct% let $x:lowctName; $s)
  | _ => throw ()

/-- `LowCT.RLetZero` prints as `let x : τ; s`. -/
@[app_unexpander LowCT.RLetZero] def unexpandRLetZero : Unexpander
  | `($_ $x $t $s) => do
    let x ← nameOfTerm x
    let s ← stmtOfTerm s
    `(lowct% let $x:lowctName : $t; $s)
  | _ => throw ()

/-- `LowCT.RCall` prints as `d := call f(args)`. -/
@[app_unexpander LowCT.RCall] def unexpandRCall : Unexpander
  | `($_ $f $d $args) => do
    let f ← nameOfTerm f
    let d ← locOfTerm d
    let as ← locsOfTerm args
    `(lowct% $d:lowctLoc := call $f:lowctName($as,*))
  | _ => throw ()

/-- `LowCT.RCallN` prints as `[ds] := call f(args)`. -/
@[app_unexpander LowCT.RCallN] def unexpandRCallN : Unexpander
  | `($_ $f $ds $args) => do
    let f ← nameOfTerm f
    let ds ← locsOfTerm ds
    let as ← locsOfTerm args
    `(lowct% [$ds,*] := call $f:lowctName($as,*))
  | _ => throw ()

/-- `LowCT.RCopy` prints as `d := copy s`. -/
@[app_unexpander LowCT.RCopy] def unexpandRCopy : Unexpander
  | `($_ $d $s) => do
    let d ← locOfTerm d
    let s ← locOfTerm s
    `(lowct% $d:lowctLoc := copy $s:lowctLoc)
  | _ => throw ()

/-- `LowCT.RArrLoad` prints as `d := s[i]`. -/
@[app_unexpander LowCT.RArrLoad] def unexpandRArrLoad : Unexpander
  | `($_ $d $s $i) => do
    let d ← locOfTerm d
    let s ← locOfTerm s
    let i ← nameOfTerm i
    `(lowct% $d:lowctLoc := $s:lowctLoc[$i:lowctName])
  | _ => throw ()

/-- `LowCT.RArrLoadLit` prints as `d := s[lit n]`. -/
@[app_unexpander LowCT.RArrLoadLit] def unexpandRArrLoadLit : Unexpander
  | `($_ $d $s $n) => do
    let d ← locOfTerm d
    let s ← locOfTerm s
    let n ← natOfTerm n
    `(lowct% $d:lowctLoc := $s:lowctLoc[lit $n:lowctNat])
  | _ => throw ()

/-- `LowCT.RArrStore` prints as `a[i] := s`. -/
@[app_unexpander LowCT.RArrStore] def unexpandRArrStore : Unexpander
  | `($_ $a $i $s) => do
    let a ← locOfTerm a
    let i ← nameOfTerm i
    let s ← locOfTerm s
    `(lowct% $a:lowctLoc[$i:lowctName] := $s:lowctLoc)
  | _ => throw ()

/-- `LowCT.RArrStoreLit` prints as `a[lit n] := s`. -/
@[app_unexpander LowCT.RArrStoreLit] def unexpandRArrStoreLit : Unexpander
  | `($_ $a $n $s) => do
    let a ← locOfTerm a
    let n ← natOfTerm n
    let s ← locOfTerm s
    `(lowct% $a:lowctLoc[lit $n:lowctNat] := $s:lowctLoc)
  | _ => throw ()

end            -- meta section

/-! ## The notation expands to the constructor terms -/

example : (sexpr% (a + b) * c - 1) =
    .SSub (.SMul (.SAdd (.SVar "a") (.SVar "b")) (.SVar "c")) (.SLit 1) := rfl
example : (sexpr% a + b * c << 2 & d ^ e < f) =
    .SLt (.SXor (.SAnd (.SShl (.SAdd (.SVar "a") (.SMul (.SVar "b") (.SVar "c"))) (.SLit 2))
      (.SVar "d")) (.SVar "e")) (.SVar "f") := rfl
example : (sexpr% a - b - c) = .SSub (.SSub (.SVar "a") (.SVar "b")) (.SVar "c") := rfl
example : (sexpr% a >> 7) = .SShr (.SVar "a") (.SLit 7) := rfl
example : (sexpr% "a b" + x[3]) = .SAdd (.SVar "a b") (.SLimb "x" 3) := rfl
example : (sexpr% asr(a, 1) + smul(a, b)) =
    .SAdd (.SAsr (.SVar "a") (.SLit 1)) (.SMulS (.SVar "a") (.SVar "b")) := rfl
example : (sexpr% mulhi(a, b) + mulhis(a, b)) =
    .SAdd (.SMulHiU (.SVar "a") (.SVar "b")) (.SMulHiS (.SVar "a") (.SVar "b")) := rfl
example (e : SExpr) (x : String) (n : Nat) :
    (sexpr% ↑e + ↑(SExpr.SVar x) + ↑x [↑n]) =
      .SAdd (.SAdd e (.SVar x)) (.SLimb x n) := rfl

example : (lowct% skip) = .RSkip := rfl
example : (lowct% t := a + b; r := t * c) =
    .RSeq (.RScalarSetExpr "t" (.SAdd (.SVar "a") (.SVar "b")))
      (.RScalarSetExpr "r" (.SMul (.SVar "t") (.SVar "c"))) := rfl
example : (lowct% a := lit 1; b := lit 2; skip) =
    .RSeq (.RScalarSet "a" 1) (.RSeq (.RScalarSet "b" 2) .RSkip) := rfl
example : (lowct% (a := lit 1; b := lit 2); skip) =
    .RSeq (.RSeq (.RScalarSet "a" 1) (.RScalarSet "b" 2)) .RSkip := rfl
example (x : String) (n : Nat) (s : LowCT) :
    (lowct% ↑x := lit ↑(n % 2); "a b" := 0; ↑s) =
      .RSeq (.RScalarSet x (n % 2)) (.RSeq (.RScalarSetExpr "a b" (.SLit 0)) s) := rfl
example : (lowct% if c { x := lit 1 } else { skip }) =
    .RIfNz "c" (.RScalarSet "x" 1) .RSkip := rfl
example : (lowct% while n { n := n - 1 }) =
    .RWhileNz "n" (.RScalarSetExpr "n" (.SSub (.SVar "n") (.SLit 1))) := rfl
example (n : Nat) : (lowct% for i < 4 { for j < ↑n { skip } }) =
    .RFor "i" 4 (.RFor "j" n .RSkip) := rfl
example : (lowct% for i < dyn n + 1 { acc := acc + i }) =
    .RForRuntime "i" (.SAdd (.SVar "n") (.SLit 1))
      (.RScalarSetExpr "acc" (.SAdd (.SVar "acc") (.SVar "i"))) := rfl
example : (lowct% let x; let y : .TFp; x := lit 1; skip) =
    .RLetU64Zero "x" (.RLetZero "y" .TFp (.RSeq (.RScalarSet "x" 1) .RSkip)) := rfl
example : (lowct% (c : .TFp) := call fp_add((a : .TFp), (b : .TFp))) =
    .RCall "fp_add" ⟨"c", .TFp⟩ [⟨"a", .TFp⟩, ⟨"b", .TFp⟩] := rfl
example (l : Located) : (lowct% [(c : .TFp), ↑l] := call f((a : .TFp))) =
    .RCallN "f" [⟨"c", .TFp⟩, l] [⟨"a", .TFp⟩] := rfl
example : (lowct% (d : .TFp) := copy (s : .TFp)) = .RCopy ⟨"d", .TFp⟩ ⟨"s", .TFp⟩ := rfl
example : (lowct% (d : .TFp) := (s : .TArr 4 .TFp)[i]; (d : .TFp) := (s : .TArr 4 .TFp)[lit 2]) =
    .RSeq (.RArrLoad ⟨"d", .TFp⟩ ⟨"s", .TArr 4 .TFp⟩ "i")
      (.RArrLoadLit ⟨"d", .TFp⟩ ⟨"s", .TArr 4 .TFp⟩ 2) := rfl
example : (lowct% (a : .TArr 4 .TFp)[i] := (s : .TFp); (a : .TArr 4 .TFp)[lit 2] := (s : .TFp)) =
    .RSeq (.RArrStore ⟨"a", .TArr 4 .TFp⟩ "i" ⟨"s", .TFp⟩)
      (.RArrStoreLit ⟨"a", .TArr 4 .TFp⟩ 2 ⟨"s", .TFp⟩) := rfl

/-! ## Constructor terms print in the notation -/

/-- info: lowct% t := a + b; r := (t + 1) * c : LowCT -/
#guard_msgs in
#check LowCT.RSeq (.RScalarSetExpr "t" (.SAdd (.SVar "a") (.SVar "b")))
  (.RScalarSetExpr "r" (.SMul (.SAdd (.SVar "t") (.SLit 1)) (.SVar "c")))

/-- info: fun s => lowct% if c {↑s} else {skip}; while k {k := k - 1} : LowCT → LowCT -/
#guard_msgs in
#check fun s : LowCT => LowCT.RSeq (.RIfNz "c" s .RSkip)
  (.RWhileNz "k" (.RScalarSetExpr "k" (.SSub (.SVar "k") (.SLit 1))))

/-- info: sexpr% asr("if", 1) + smul(a, mulhis(a, b)) : SExpr -/
#guard_msgs in
#check SExpr.SAdd (.SAsr (.SVar "if") (.SLit 1))
  (.SMulS (.SVar "a") (.SMulHiS (.SVar "a") (.SVar "b")))

end CatCrypt.Crypto.Jasmin.LowCTNotation
