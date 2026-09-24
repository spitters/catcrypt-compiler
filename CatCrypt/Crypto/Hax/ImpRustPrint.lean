/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AST
public import Mathlib.Data.Nat.Digits.Defs

/-!
# A Rust printer for hax-lean's `ImpExpr`, with its parser

`ppImpRust ty e` is Rust source text for the hax expression `e`, with `ty` the
Rust types of the locals it binds, and `parseImpRust` reads such text back;
`parse_ppImpRust` states `parseImpRust (ppImpRust ty e) = e` for every printable
`e`, so the printer is injective.  `ppImpRustFn` prints a Rust `fn` around a
printed body, with the parameter types and the local types given as inputs,
since an `ImpExpr` carries no Rust slot types; `parse_ppImpRustFn` is its round
trip.  A type is a single whitespace-free token, such as `&mut[u8;48]`.
`ppImpRustFnRet` prints a `fn` with a return type, whose body is a statement
sequence ending in a variable or a tuple of variables — the returned value.

The printer covers the statement fragment below, which contains every shape
in the table of `lowCTToImp` (`CatCrypt.Crypto.Hax.LowCTToHax`); every other
expression maps to `none`.  The last column is the node the hax frontend (the
JSON adapter `Hax.HaxAdapter.parseHaxExpr` on the output of `cargo hax`) reads
the Rust form as, and the normalisation that relates it to the printed node.

| `ImpExpr` | Rust | read by the hax frontend as |
|---|---|---|
| `unitVal` | `()` | `unitVal` |
| `var x` | `x` | the tail expression of a block, `var x` |
| `seq a b` | `a ; b`, and `{ a } ; b` when `a` is a `seq` or a `letBind` | `Block` of statements, `seq` |
| `letBind x v b` | `let mut x : T = v ; b`, with `: T` when `ty x = some T` | `Let`, the continuation placed in the body |
| `letBind x (array_update(x, i, s)) b` | `x [ i ] = s ; b` | `Assign` of `Index`: `assign x (array_update(x, i, s))`; `localMutation` rebinds it |
| `assign x v` | `x = v` | `Assign`, `assign` |
| `ifThenElse (var c) t e` | `if c { t } else { e }` | `If`, `ifThenElse` |
| `whileLoop (var c) b` | `while c { b }` | `Loop`, `whileLoop` |
| `forFold x lo hi b` | `for x in lo .. hi { b }` | `forLoop` (`reconstructForLoops`), `forFold` after `functionalizeLoops` |
| `match_ (f(args)) [((x, y), b)]` | `match f ( args ) { ( x , y ) => { b } }` | `Match`, `match_` with a `tuplePat` |
| `tuple [var a₁, var a₂, …]`, two or more components | `( a₁ , a₂ , … )` | `Tuple`, `tuple` |

A right-hand side `v` of a binding or an assignment is one of:

| `ImpExpr` | Rust | read as |
|---|---|---|
| `app f [var a₁, …]` | `f ( a₁ , … )` | `Call`, `app f`; for `f = Some`, `Adt`, `app "Some"` |
| `app "None" []` | `None` | `Adt`, `app "None"` |
| `app "index" [var s, var i]` | `s [ i ]` | `Index`, `app "index"` |
| `proj (var s) i` | `s . i` | `TupleField`, `proj` |
| `lit (int k)` | `k` | `Literal`, `lit (int k)` |
| `app "scalar#Op" [var a, var b]` | `a op b` | `Binary`, `app "Op"`; `scalarNorm` renames it to `scalar#Op` |
| `app "scalar#Sub" [var a, var b]` | `a . saturating_sub ( b )` | `Call` of the method `saturating_sub` |

with `op` one of `+ * & ^ < > <= >= == !=` for `Add`, `Mul`, `BitAnd`,
`BitXor`, `Lt`, `Gt`, `Le`, `Ge`, `Eq`, `Ne`.  `scalar#Sub` is the subtraction
truncated at `0` (`SExpr.eval` of `SSub`), which is `u64::saturating_sub`; the
frontend reads it as a method call, which `scalarNorm` does not rename.  A
comparison binding has the Rust type `bool`, as the comparisons of
`scalarSrcBuiltins` return booleans.  A loop bound is a variable, an integer
literal, or `app "Add" [a, b]`, `app "Sub" [a, b]`, `app "Mul" [a, b]` of
bounds, printed parenthesised as `( a + b )`, `( a - b )`, `( a * b )`, which
the frontend reads as `Binary`.  Loops are printed over ranges only, never over
iterators.

Every name printed as a variable, a binder or a callee satisfies `validIdent`:
an ASCII identifier that is not a Rust keyword.  The frontend adds a bit width
to the width-sensitive operators (`BitAnd#64`), and a call name is the path the
frontend gives the callee; both are outside this syntax-only printer.

`lowCTToImp_simulates` (`CatCrypt.Crypto.Hax.LowCTToHaxSim`) does not cover the
`match_` of a two-destination call, nor a `forFold` whose bound is an `Add`,
`Sub` or `Mul`; a printed program using either has the round trip of this
module and no semantic theorem.

## Layout

The text is a sequence of tokens, each followed by one whitespace character: a
line break after `;`, `{` and `}`, a space otherwise.  `lex` splits text at
whitespace, and `lex_renderChars` shows it recovers the tokens.  `parseSeq` is a
recursive-descent parser over tokens, with the token count as fuel.

## Main definitions

* `ppToks`, `ppImpRust`, `ppImpRustFn`, `ppImpRustFnRet` — the printer.
* `lex`, `parseSeq`, `parseImpRust`, `parseImpRustFn`, `parseImpRustFnRet` — the
  parser.

## Main results

* `parseSeq_ppToks` — the token-level round trip.
* `parse_ppImpRust`, `parse_ppImpRustFn`, `parse_ppImpRustFnRet` — the
  text-level round trips.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpRust

open _root_.Hax (ImpExpr ImpLit ImpPat)

/-- A token: a nonempty word without whitespace. -/
abbrev Tok := String

/-! ## §1  Names and numerals -/

/-- The Rust keywords, and `_`. -/
def rustKeywords : List String :=
  ["as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum",
   "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move",
   "mut", "pub", "ref", "return", "self", "Self", "static", "struct", "super", "trait", "true",
   "type", "unsafe", "use", "where", "while", "abstract", "become", "box", "do", "final",
   "macro", "override", "priv", "typeof", "unsized", "virtual", "yield", "try", "_"]

/-- An ASCII letter or `_`. -/
def identStart (c : Char) : Bool :=
  (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122) || c.toNat == 95

/-- An ASCII letter, digit or `_`. -/
def identChar (c : Char) : Bool := identStart c || (48 ≤ c.toNat && c.toNat ≤ 57)

/-- `s` is an ASCII identifier other than a Rust keyword. -/
def validIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => identStart c && cs.all identChar && !(rustKeywords.contains s)

/-- The decimal digit `d`. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The value of a decimal digit. -/
def charDigit (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48) else none

/-- The decimal numeral of `n`. -/
def natChars (n : Nat) : List Char :=
  if n = 0 then ['0'] else ((Nat.digits 10 n).reverse.map digitChar)

/-- The value of a decimal numeral. -/
def natOfChars : List Char → Option Nat
  | [] => none
  | c :: cs => ((c :: cs).mapM charDigit).map fun ds => Nat.ofDigits 10 ds.reverse

/-- The numeral of an integer, with a leading `-` when it is negative. -/
def intChars : Int → List Char
  | .ofNat n => natChars n
  | .negSucc n => '-' :: natChars (n + 1)

/-- The value of an integer numeral. -/
def intOfChars : List Char → Option Int
  | [] => none
  | c :: cs =>
      if c = '-' then
        match natOfChars cs with
        | some (n + 1) => some (Int.negSucc n)
        | _ => none
      else (natOfChars (c :: cs)).map Int.ofNat

/-- The numeral token of `n`. -/
def natTok (n : Nat) : Tok := String.ofList (natChars n)

/-- The numeral token of `k`. -/
def intTok (k : Int) : Tok := String.ofList (intChars k)

/-! ## §2  Operators -/

/-- The Rust operator of a call computed in the scalar heap, other than
    `scalar#Sub`. -/
def scalarSym (f : String) : Option Tok :=
  if f = "scalar#Add" then some "+"
  else if f = "scalar#Mul" then some "*"
  else if f = "scalar#BitAnd" then some "&"
  else if f = "scalar#BitXor" then some "^"
  else if f = "scalar#Lt" then some "<"
  else if f = "scalar#Gt" then some ">"
  else if f = "scalar#Le" then some "<="
  else if f = "scalar#Ge" then some ">="
  else if f = "scalar#Eq" then some "=="
  else if f = "scalar#Ne" then some "!="
  else none

/-- The call computed in the scalar heap of a Rust operator. -/
def symScalar (t : Tok) : Option String :=
  if t = "+" then some "scalar#Add"
  else if t = "*" then some "scalar#Mul"
  else if t = "&" then some "scalar#BitAnd"
  else if t = "^" then some "scalar#BitXor"
  else if t = "<" then some "scalar#Lt"
  else if t = ">" then some "scalar#Gt"
  else if t = "<=" then some "scalar#Le"
  else if t = ">=" then some "scalar#Ge"
  else if t = "==" then some "scalar#Eq"
  else if t = "!=" then some "scalar#Ne"
  else none

/-- The Rust operator of a loop-bound operation. -/
def boundSym (f : String) : Option Tok :=
  if f = "Add" then some "+" else if f = "Sub" then some "-"
  else if f = "Mul" then some "*" else none

/-- The loop-bound operation of a Rust operator. -/
def symBound (t : Tok) : Option String :=
  if t = "+" then some "Add" else if t = "-" then some "Sub"
  else if t = "*" then some "Mul" else none

/-! ## §3  The printer -/

/-- The arguments of a call on variables, each followed by `,` and the last by
    `)`. -/
def argToks : List ImpExpr → Option (List Tok)
  | [] => some [")"]
  | [.var x] => if validIdent x then some [x, ")"] else none
  | .var x :: a :: as =>
      if validIdent x then (argToks (a :: as)).map fun t => [x, ","] ++ t else none
  | _ => none

/-- The call `f ( args )`. -/
def callToks (f : String) (args : List ImpExpr) : Option (List Tok) :=
  if validIdent f then (argToks args).map fun t => [f, "("] ++ t else none

/-- The right-hand side of a binding or an assignment. -/
def rhsToks : ImpExpr → Option (List Tok)
  | .app f args =>
      if f = "None" ∧ args = [] then some ["None"]
      else if f = "scalar#Sub" then
        match args with
        | [.var a, .var b] =>
            if validIdent a && validIdent b then some [a, ".", "saturating_sub", "(", b, ")"]
            else none
        | _ => none
      else
      match scalarSym f with
      | some op =>
          match args with
          | [.var a, .var b] => if validIdent a && validIdent b then some [a, op, b] else none
          | _ => none
      | none =>
          if f = "index" then
            match args with
            | [.var s, .var i] =>
                if validIdent s && validIdent i then some [s, "[", i, "]"] else none
            | _ => callToks f args
          else callToks f args
  | .proj (.var s) i => if validIdent s then some [s, ".", natTok i] else none
  | .lit (.int k) => some [intTok k]
  | _ => none

/-- A loop bound: a variable, a literal, or a parenthesised `+`, `-`, `*` of
    bounds. -/
def boundToks : ImpExpr → Option (List Tok)
  | .var x => if validIdent x then some [x] else none
  | .lit (.int k) => some [intTok k]
  | .app f [a, b] =>
      match boundSym f, boundToks a, boundToks b with
      | some op, some ta, some tb => some (["("] ++ ta ++ [op] ++ tb ++ [")"])
      | _, _, _ => none
  | _ => none

/-- The index and the source of an array update of `x` in place. -/
def arrUpdateArgs (x : String) : ImpExpr → Option (String × String)
  | .app f [.var a, .var i, .var s] =>
      if f = "array_update" ∧ a = x ∧ validIdent i = true ∧ validIdent s = true then
        some (i, s)
      else none
  | _ => none

/-- A binding, a sequence or a variable, printed in braces on the left of `;`. -/
def needsBrace : ImpExpr → Bool
  | .letBind .. => true
  | .seq .. => true
  | .var .. => true
  | _ => false

/-- The type annotation `: T` of a binder with the type `T` in `ty`. -/
def tyAnn (ty : String → Option Tok) (x : String) : List Tok :=
  match ty x with
  | some t => [":", t]
  | none => []

/-- The tokens of a statement sequence, with `ty` the Rust types of the bound
    locals. -/
def ppToks (ty : String → Option Tok) : ImpExpr → Option (List Tok)
  | .letBind x v b =>
      if validIdent x then
        match ppToks ty b with
        | none => none
        | some tb =>
            match arrUpdateArgs x v with
            | some (i, s) => some ([x, "[", i, "]", "=", s, ";"] ++ tb)
            | none => (rhsToks v).map fun tv =>
                ["let", "mut", x] ++ tyAnn ty x ++ ["="] ++ tv ++ [";"] ++ tb
      else none
  | .seq a b =>
      match ppToks ty a, ppToks ty b with
      | some ta, some tb =>
          some ((if needsBrace a then ["{"] ++ ta ++ ["}"] else ta) ++ [";"] ++ tb)
      | _, _ => none
  | .unitVal => some ["(", ")"]
  | .var x => if validIdent x then some [x] else none
  | .assign x v => if validIdent x then (rhsToks v).map fun tv => [x, "="] ++ tv else none
  | .ifThenElse (.var c) t e =>
      if validIdent c then
        match ppToks ty t, ppToks ty e with
        | some tt, some te => some (["if", c, "{"] ++ tt ++ ["}", "else", "{"] ++ te ++ ["}"])
        | _, _ => none
      else none
  | .whileLoop (.var c) b =>
      if validIdent c then (ppToks ty b).map fun tb => ["while", c, "{"] ++ tb ++ ["}"] else none
  | .forFold x lo hi b =>
      if validIdent x then
        match boundToks lo, boundToks hi, ppToks ty b with
        | some tl, some th, some tb =>
            some (["for", x, "in"] ++ tl ++ [".."] ++ th ++ ["{"] ++ tb ++ ["}"])
        | _, _, _ => none
      else none
  | .match_ (.app f args) [(.tuplePat [.varPat x, .varPat y], b)] =>
      if validIdent x && validIdent y then
        match callToks f args, ppToks ty b with
        | some tc, some tb =>
            some (["match"] ++ tc ++ ["{", "(", x, ",", y, ")", "=>", "{"] ++ tb ++ ["}", "}"])
        | _, _ => none
      else none
  | .tuple (a :: b :: cs) => (argToks (a :: b :: cs)).map fun t => "(" :: t
  | _ => none

/-! ## §4  Rendering and lexing -/

/-- The whitespace characters. -/
def isWs (c : Char) : Bool := c = ' ' || c = '\n' || c = '\t' || c = '\r'

/-- A token is nonempty and has no whitespace. -/
def tokOK (t : Tok) : Bool := !t.toList.isEmpty && t.toList.all fun c => !isWs c

/-- The separator after a token: a line break after `;`, `{` and `}`, a space
    otherwise. -/
def sepAfter (t : Tok) : Char := if t = ";" ∨ t = "{" ∨ t = "}" then '\n' else ' '

/-- The text of a token list, each token followed by its separator. -/
def renderChars : List Tok → List Char
  | [] => []
  | t :: ts => t.toList ++ sepAfter t :: renderChars ts

/-- Split at whitespace, with the reversed characters of the current word. -/
def lexAux : List Char → List Char → List Tok
  | [], acc => if acc.isEmpty then [] else [String.ofList acc.reverse]
  | c :: cs, acc =>
      if isWs c then
        if acc.isEmpty then lexAux cs [] else String.ofList acc.reverse :: lexAux cs []
      else lexAux cs (c :: acc)

/-- The words of a text. -/
def lex (cs : List Char) : List Tok := lexAux cs []

/-! ## §5  The parser -/

/-- Consume the given tokens. -/
def expects : List Tok → List Tok → Option (List Tok)
  | [], r => some r
  | t :: ts, u :: r => if u = t then expects ts r else none
  | _ :: _, [] => none

/-- The value of an integer token. -/
def intOfTok (t : Tok) : Option Int := intOfChars t.toList

/-- The value of a natural-number token. -/
def natOfTok (t : Tok) : Option Nat := natOfChars t.toList

/-- Call arguments up to and including `)`. -/
def parseArgs : List Tok → Option (List ImpExpr × List Tok)
  | [] => none
  | t :: r =>
      if t = ")" then some ([], r)
      else
        match r with
        | [] => none
        | u :: r' =>
            if u = ")" then some ([.var t], r')
            else if u = "," then (parseArgs r').map fun p => (.var t :: p.1, p.2)
            else none

/-- A right-hand side of one token followed by `r`: an integer literal, or the
    constructor `None`. -/
def parseAtom (a : Tok) (r : List Tok) : Option (ImpExpr × List Tok) :=
  match intOfTok a with
  | some k => some (.lit (.int k), r)
  | none => if a = "None" then some (.app "None" [], r) else none

/-- A right-hand side. -/
def parseRhs : List Tok → Option (ImpExpr × List Tok)
  | [] => none
  | [a] => parseAtom a []
  | a :: t :: r =>
      if t = "(" then (parseArgs r).map fun p => (.app a p.1, p.2)
      else if t = "[" then
        match r with
        | i :: u :: r' => if u = "]" then some (.app "index" [.var a, .var i], r') else none
        | _ => none
      else if t = "." then
        match r with
        | k :: r' =>
            if k = "saturating_sub" then
              match r' with
              | u :: b :: w :: r'' =>
                  if u = "(" ∧ w = ")" then some (.app "scalar#Sub" [.var a, .var b], r'')
                  else none
              | _ => none
            else (natOfTok k).map fun n => (.proj (.var a) n, r')
        | [] => none
      else
        match symScalar t, r with
        | some f, b :: r' => some (.app f [.var a, .var b], r')
        | _, _ => parseAtom a (t :: r)

/-- A loop bound, with fuel. -/
def parseBound : Nat → List Tok → Option (ImpExpr × List Tok)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, t :: r =>
      if t = "(" then
        match parseBound n r with
        | some (a, op :: r1) =>
            match symBound op, parseBound n r1 with
            | some f, some (b, c :: r2) => if c = ")" then some (.app f [a, b], r2) else none
            | _, _ => none
        | _ => none
      else
        match intOfTok t with
        | some k => some (.lit (.int k), r)
        | none => some (.var t, r)

/-- A statement other than a binding or a braced sequence, with `p` the parser
    of the blocks. -/
def parseStmt (p : List Tok → Option (ImpExpr × List Tok)) :
    List Tok → Option (ImpExpr × List Tok)
  | [] => none
  | t :: r =>
    if t = "(" then
      match r with
      | u :: r' =>
          if u = ")" then some (.unitVal, r')
          else (parseArgs r).map fun q => (.tuple q.1, q.2)
      | [] => none
    else if t = "if" then
      match r with
      | c :: r1 => do
          let r2 ← expects ["{"] r1
          let (th, r3) ← p r2
          let r4 ← expects ["}", "else", "{"] r3
          let (el, r5) ← p r4
          let r6 ← expects ["}"] r5
          pure (.ifThenElse (.var c) th el, r6)
      | [] => none
    else if t = "while" then
      match r with
      | c :: r1 => do
          let r2 ← expects ["{"] r1
          let (b, r3) ← p r2
          let r4 ← expects ["}"] r3
          pure (.whileLoop (.var c) b, r4)
      | [] => none
    else if t = "for" then
      match r with
      | x :: r1 => do
          let r2 ← expects ["in"] r1
          let (lo, r3) ← parseBound r2.length r2
          let r4 ← expects [".."] r3
          let (hi, r5) ← parseBound r4.length r4
          let r6 ← expects ["{"] r5
          let (b, r7) ← p r6
          let r8 ← expects ["}"] r7
          pure (.forFold x lo hi b, r8)
      | [] => none
    else if t = "match" then
      match r with
      | f :: r1 => do
          let r2 ← expects ["("] r1
          let (args, r3) ← parseArgs r2
          let r4 ← expects ["{", "("] r3
          match r4 with
          | x :: r5 => do
              let r6 ← expects [","] r5
              match r6 with
              | y :: r7 => do
                  let r8 ← expects [")", "=>", "{"] r7
                  let (b, r9) ← p r8
                  let r10 ← expects ["}", "}"] r9
                  pure (.match_ (.app f args) [(.tuplePat [.varPat x, .varPat y], b)], r10)
              | [] => none
          | [] => none
      | [] => none
    else
      match r with
      | u :: r1 =>
          if u = "=" then (parseRhs r1).map fun q => (.assign t q.1, q.2)
          else if u = ";" ∨ u = "}" then some (.var t, r)
          else none
      | [] => some (.var t, [])

/-- The `=` of a binding, after an optional type annotation `: T`. -/
def skipAnn : List Tok → Option (List Tok)
  | [] => none
  | e :: r =>
      if e = "=" then some r
      else if e = ":" then
        match r with
        | _ :: e2 :: r2 => if e2 = "=" then some r2 else none
        | _ => none
      else none

/-- A statement sequence, with fuel. -/
def parseSeq : Nat → List Tok → Option (ImpExpr × List Tok)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, t :: r =>
    if t = "let" then
      match r with
      | m :: x :: r0 =>
          if m = "mut" then do
            let r1 ← skipAnn r0
            let (v, r2) ← parseRhs r1
            let r3 ← expects [";"] r2
            let (b, r4) ← parseSeq n r3
            pure (.letBind x v b, r4)
          else none
      | _ => none
    else if t = "{" then do
      let (a, r1) ← parseSeq n r
      let r2 ← expects ["}", ";"] r1
      let (b, r3) ← parseSeq n r2
      pure (.seq a b, r3)
    else if r.head? = some "[" then
      match r with
      | _ :: i :: r1 => do
          let r2 ← expects ["]", "="] r1
          match r2 with
          | s :: r3 => do
              let r4 ← expects [";"] r3
              let (b, r5) ← parseSeq n r4
              pure (.letBind t (.app "array_update" [.var t, .var i, .var s]) b, r5)
          | [] => none
      | _ => none
    else
      match parseStmt (parseSeq n) (t :: r) with
      | some (a, u :: r1) =>
          if u = ";" then (parseSeq n r1).map fun q => (.seq a q.1, q.2) else some (a, u :: r1)
      | res => res

/-! ## §6  Lexing recovers the tokens -/

theorem isWs_sepAfter (t : Tok) : isWs (sepAfter t) = true := by
  unfold sepAfter; split <;> decide

theorem lexAux_append (w acc : List Char) (c : Char) (rest : List Char)
    (hw : w.all (fun c => !isWs c) = true) (hc : isWs c = true)
    (hne : (w.reverse ++ acc).isEmpty = false) :
    lexAux (w ++ c :: rest) acc = String.ofList (acc.reverse ++ w) :: lexAux rest [] := by
  induction w generalizing acc with
  | nil =>
    simp only [List.reverse_nil, List.nil_append] at hne
    simp [lexAux, hc, hne]
  | cons d w ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
    have := ih (d :: acc) hw.2 (by simp)
    simp [lexAux, hw.1, this]

/-- `lex` recovers a list of tokens from its text. -/
theorem lex_renderChars (ts : List Tok) (h : ts.all tokOK = true) : lex (renderChars ts) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ht, hts⟩ := h
    simp only [tokOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.isEmpty_eq_false_iff] at ht
    have hne : (t.toList.reverse ++ []).isEmpty = false := by
      simpa [List.isEmpty_eq_false_iff] using ht.1
    unfold lex at ih ⊢
    rw [renderChars, lexAux_append _ _ _ _ ht.2 (isWs_sepAfter t) hne, ih hts]
    simp

/-! ## §7  Numerals -/

theorem charDigit_digitChar : ∀ d, d < 10 → charDigit (digitChar d) = some d := by decide

theorem mapM_charDigit (l : List Nat) (h : ∀ d ∈ l, d < 10) :
    (l.map digitChar).mapM charDigit = some l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [List.mapM_cons, charDigit_digitChar d h.1, ih h.2]

theorem natOfChars_eq (cs : List Char) (h : cs ≠ []) :
    natOfChars cs = (cs.mapM charDigit).map fun ds => Nat.ofDigits 10 ds.reverse := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c cs => rfl

theorem natChars_ne_nil (n : Nat) : natChars n ≠ [] := by
  unfold natChars
  split
  · simp
  · simp [Nat.digits_ne_nil_iff_ne_zero, *]

theorem natOfChars_natChars (n : Nat) : natOfChars (natChars n) = some n := by
  rw [natOfChars_eq _ (natChars_ne_nil n)]
  unfold natChars
  split
  · subst_vars; rfl
  · have h10 : ∀ d ∈ (Nat.digits 10 n).reverse, d < 10 := fun d hd =>
      Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd)
    rw [mapM_charDigit _ h10]
    simp [Nat.ofDigits_digits]

theorem charDigit_isSome_of_mem_natChars (n : Nat) (c : Char) (hc : c ∈ natChars n) :
    (charDigit c).isSome = true := by
  unfold natChars at hc
  split at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; decide
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    rw [charDigit_digitChar d (Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd))]
    rfl

theorem intOfChars_intChars (k : Int) : intOfChars (intChars k) = some k := by
  cases k with
  | ofNat n =>
    simp only [intChars]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (natChars_ne_nil n)
    have hc : c ≠ '-' := by
      rintro rfl
      have := charDigit_isSome_of_mem_natChars n '-' (by simp [hcs])
      revert this; decide
    rw [hcs]
    simp only [intOfChars, hc, if_false]
    rw [← hcs, natOfChars_natChars]
    rfl
  | negSucc n =>
    simp [intChars, intOfChars, natOfChars_natChars]

theorem natOfTok_natTok (n : Nat) : natOfTok (natTok n) = some n := by
  simp [natOfTok, natTok, natOfChars_natChars]

theorem intOfTok_intTok (k : Int) : intOfTok (intTok k) = some k := by
  simp [intOfTok, intTok, intOfChars_intChars]

theorem charDigit_eq_none_of_identStart (c : Char) (h : identStart c = true) :
    charDigit c = none := by
  simp only [identStart, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  unfold charDigit
  rw [if_neg]
  omega

theorem intOfTok_eq_none_of_validIdent (x : String) (h : validIdent x = true) :
    intOfTok x = none := by
  unfold validIdent at h
  unfold intOfTok
  cases hx : x.toList with
  | nil => simp [hx] at h
  | cons c cs =>
    simp only [hx, Bool.and_eq_true] at h
    have hd := charDigit_eq_none_of_identStart c h.1.1
    have hc : c ≠ '-' := by rintro rfl; have := h.1.1; revert this; decide
    simp [intOfChars, hc, natOfChars, List.mapM_cons, hd]

/-- The tokens the parser dispatches on are not names. -/
theorem validIdent_ne (x : String) (h : validIdent x = true) :
    x ≠ "(" ∧ x ≠ ")" ∧ x ≠ "{" ∧ x ≠ "}" ∧ x ≠ "[" ∧ x ≠ "]" ∧ x ≠ "," ∧ x ≠ ";" ∧
    x ≠ "." ∧ x ≠ ".." ∧ x ≠ "=" ∧ x ≠ "=>" ∧ x ≠ "let" ∧ x ≠ "mut" ∧ x ≠ "if" ∧
    x ≠ "else" ∧ x ≠ "while" ∧ x ≠ "for" ∧ x ≠ "in" ∧ x ≠ "match" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rintro rfl; revert h; decide)

/-! ## §8  The parser inverts the printer -/

theorem expects_append (ts r : List Tok) : expects ts (ts ++ r) = some r := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [expects, ih]

theorem parseArgs_argToks (args : List ImpExpr) (ta : List Tok) (h : argToks args = some ta)
    (rest : List Tok) : parseArgs (ta ++ rest) = some (args, rest) := by
  induction args generalizing ta with
  | nil =>
    simp only [argToks, Option.some.injEq] at h
    subst h; simp [parseArgs.eq_def]
  | cons a as ih =>
    cases a
    case var x =>
      cases as with
      | nil =>
        simp only [argToks] at h
        split at h
        · rename_i hx
          simp only [Option.some.injEq] at h
          subst h
          have := validIdent_ne x hx
          simp [parseArgs.eq_def, this]
        · simp at h
      | cons b bs =>
        simp only [argToks] at h
        split at h
        · rename_i hx
          cases ht : argToks (b :: bs) with
          | none => simp [ht] at h
          | some t =>
            simp only [ht, Option.map_some, Option.some.injEq] at h
            subst h
            have := validIdent_ne x hx
            rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append,
              parseArgs.eq_def]
            simp [this, ih t ht]
        · simp at h
    all_goals simp [argToks] at h

theorem argToks_cons_head (a : ImpExpr) (as : List ImpExpr) (ta : List Tok)
    (h : argToks (a :: as) = some ta) : ∃ x r, ta = x :: r ∧ validIdent x = true := by
  cases a
  case var x =>
    cases as with
    | nil =>
      simp only [argToks] at h
      split at h
      · rename_i hx
        simp only [Option.some.injEq] at h
        exact ⟨x, _, h.symm, hx⟩
      · simp at h
    | cons b bs =>
      simp only [argToks] at h
      split at h
      · rename_i hx
        cases ht : argToks (b :: bs) with
        | none => simp [ht] at h
        | some t =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          exact ⟨x, _, h.symm, hx⟩
      · simp at h
  all_goals simp [argToks] at h

/-- The right-hand-side follow set: end of input, `;` or `}`. -/
def stmtStop : List Tok → Prop
  | [] => True
  | t :: _ => t = "}" ∨ t = ";"

/-- The sequence follow set: end of input or `}`. -/
def seqStop : List Tok → Prop
  | [] => True
  | t :: _ => t = "}"

theorem stmtStop_of_seqStop (r : List Tok) (h : seqStop r) : stmtStop r := by
  cases r with
  | nil => trivial
  | cons t r => exact Or.inl h

theorem scalarSym_symScalar (f op : String) (h : scalarSym f = some op) :
    symScalar op = some f := by
  unfold scalarSym at h
  repeat (split at h; (simp only [Option.some.injEq] at h; subst_vars; rfl))
  simp at h

theorem scalarSym_ne (f op : String) (h : scalarSym f = some op) :
    op ≠ "(" ∧ op ≠ "[" ∧ op ≠ "." := by
  unfold scalarSym at h
  repeat (split at h; (simp only [Option.some.injEq] at h; subst_vars; decide))
  simp at h

theorem callToks_eq (f : String) (args : List ImpExpr) (tc : List Tok)
    (h : callToks f args = some tc) :
    validIdent f = true ∧ ∃ ta, argToks args = some ta ∧ tc = f :: "(" :: ta := by
  unfold callToks at h
  split at h
  · rename_i hf
    cases ha : argToks args with
    | none => simp [ha] at h
    | some ta =>
      simp only [ha, Option.map_some, Option.some.injEq] at h
      exact ⟨hf, ta, rfl, h.symm⟩
  · simp at h

theorem parseRhs_callToks (f : String) (args : List ImpExpr) (tc : List Tok)
    (h : callToks f args = some tc) (rest : List Tok) :
    parseRhs (tc ++ rest) = some (.app f args, rest) := by
  obtain ⟨_, ta, ha, rfl⟩ := callToks_eq f args tc h
  rw [List.cons_append, List.cons_append, parseRhs.eq_def]
  simp [parseArgs_argToks args ta ha rest]

theorem natTok_ne_sat (n : Nat) : natTok n ≠ "saturating_sub" := by
  intro h
  have := natOfTok_natTok n
  have h2 : natOfTok "saturating_sub" = none := by decide
  rw [h, h2] at this
  simp at this

theorem parseRhs_rhsToks (v : ImpExpr) (tv : List Tok) (h : rhsToks v = some tv)
    (rest : List Tok) (hr : stmtStop rest) : parseRhs (tv ++ rest) = some (v, rest) := by
  cases v
  case app f args =>
    unfold rhsToks at h
    by_cases hnone : f = "None" ∧ args = []
    · obtain ⟨rfl, rfl⟩ := hnone
      simp only [and_self, if_true, Option.some.injEq] at h
      subst h
      have hn : intOfTok "None" = none := by decide
      cases rest with
      | nil => simp [parseRhs.eq_def, parseAtom, hn]
      | cons t r =>
        simp only [stmtStop] at hr
        rcases hr with rfl | rfl <;> simp [parseRhs.eq_def, parseAtom, hn, symScalar]
    simp only [hnone, if_false] at h
    by_cases hsub : f = "scalar#Sub"
    · subst hsub
      simp only [if_true] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          simp only [List.cons_append, List.nil_append]
          rw [parseRhs.eq_def]
          simp
        · simp at h
      · simp at h
    simp only [hsub, if_false] at h
    cases hs : scalarSym f with
    | some op =>
      simp only [hs] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := scalarSym_ne f op hs
          rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append,
            parseRhs.eq_def]
          simp [h1, h2, h3, scalarSym_symScalar f op hs]
        · simp at h
      · simp at h
    | none =>
      simp only [hs] at h
      split at h
      · subst_vars
        split at h
        · rename_i s i
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append,
              List.nil_append, parseRhs.eq_def]
            simp
          · simp at h
        · exact parseRhs_callToks _ _ _ h rest
      · exact parseRhs_callToks _ _ _ h rest
  case proj e i =>
    cases e
    case var s =>
      simp only [rhsToks] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append,
          parseRhs.eq_def]
        simp [natOfTok_natTok, natTok_ne_sat]
      · simp at h
    all_goals simp [rhsToks] at h
  case lit l =>
    cases l
    case int k =>
      simp only [rhsToks, Option.some.injEq] at h
      subst h
      cases rest with
      | nil => simp [parseRhs.eq_def, parseAtom, intOfTok_intTok]
      | cons t r =>
        simp only [stmtStop] at hr
        rcases hr with rfl | rfl <;>
          simp [parseRhs.eq_def, parseAtom, intOfTok_intTok, symScalar]
    all_goals simp [rhsToks] at h
  all_goals simp [rhsToks] at h

theorem boundSym_symBound (f op : String) (h : boundSym f = some op) :
    symBound op = some f := by
  unfold boundSym at h
  repeat (split at h; (simp only [Option.some.injEq] at h; subst_vars; rfl))
  simp at h

theorem intTok_ne_lparen (k : Int) : intTok k ≠ "(" := by
  intro h
  have := intOfTok_intTok k
  have h2 : intOfTok "(" = none := by decide
  rw [h, h2] at this
  simp at this

theorem parseBound_boundToks (e : ImpExpr) : ∀ tb, boundToks e = some tb →
    ∀ n rest, tb.length ≤ n → parseBound n (tb ++ rest) = some (e, rest) := by
  induction e using ImpExpr.ind
  case var x =>
    intro tb h n rest hn
    simp only [boundToks] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      have := validIdent_ne x hx
      simp [parseBound, this, intOfTok_eq_none_of_validIdent x hx]
    · simp at h
  case lit l =>
    intro tb h n rest hn
    cases l
    case int k =>
      simp only [boundToks, Option.some.injEq] at h
      subst h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      simp [parseBound, intTok_ne_lparen, intOfTok_intTok]
    all_goals simp [boundToks] at h
  case app f args ih =>
    intro tb h n rest hn
    match args, ih with
    | [a, b], ih =>
      simp only [boundToks] at h
      cases hs : boundSym f <;> cases ha : boundToks a <;> cases hb : boundToks b <;>
        simp only [hs, ha, hb, reduceCtorEq, Option.some.injEq] at h
      rename_i op ta tb'
      subst h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      simp only [List.length_append, List.length_cons, List.length_nil] at hn
      have iha := ih a (by simp) ta ha m (op :: (tb' ++ ")" :: rest)) (by omega)
      have ihb := ih b (by simp) tb' hb m (")" :: rest) (by omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      simp [parseBound, iha, ihb, boundSym_symBound f op hs]
    | [], _ => simp [boundToks] at h
    | [_], _ => simp [boundToks] at h
    | _ :: _ :: _ :: _, _ => simp [boundToks] at h
  all_goals intro tb h; simp [boundToks] at h

/-! ### Steps of the statement parser -/

section Steps

variable (p : List Tok → Option (ImpExpr × List Tok))

theorem parseStmt_unit (r : List Tok) : parseStmt p ("(" :: ")" :: r) = some (.unitVal, r) := by
  simp [parseStmt]

theorem parseStmt_tuple (x : String) (r r' : List Tok) (args : List ImpExpr) (hx : x ≠ ")")
    (ha : parseArgs (x :: r) = some (args, r')) :
    parseStmt p ("(" :: x :: r) = some (.tuple args, r') := by
  simp [parseStmt, hx, ha]

theorem parseStmt_if (c : String) (r1 r2 r3 : List Tok) (t e : ImpExpr)
    (ht : p r1 = some (t, "}" :: "else" :: "{" :: r2)) (he : p r2 = some (e, "}" :: r3)) :
    parseStmt p ("if" :: c :: "{" :: r1) = some (.ifThenElse (.var c) t e, r3) := by
  simp [parseStmt, expects, ht, he]

theorem parseStmt_while (c : String) (r1 r2 : List Tok) (b : ImpExpr)
    (hb : p r1 = some (b, "}" :: r2)) :
    parseStmt p ("while" :: c :: "{" :: r1) = some (.whileLoop (.var c) b, r2) := by
  simp [parseStmt, expects, hb]

theorem parseStmt_for (x : String) (r1 r2 r3 r4 : List Tok) (lo hi b : ImpExpr)
    (hlo : parseBound r1.length r1 = some (lo, ".." :: r2))
    (hhi : parseBound r2.length r2 = some (hi, "{" :: r3))
    (hb : p r3 = some (b, "}" :: r4)) :
    parseStmt p ("for" :: x :: "in" :: r1) = some (.forFold x lo hi b, r4) := by
  simp [parseStmt, expects, hlo, hhi, hb]

theorem parseStmt_match (f x y : String) (args : List ImpExpr) (r1 r2 r3 : List Tok)
    (b : ImpExpr)
    (ha : parseArgs r1 = some (args, "{" :: "(" :: x :: "," :: y :: ")" :: "=>" :: "{" :: r2))
    (hb : p r2 = some (b, "}" :: "}" :: r3)) :
    parseStmt p ("match" :: f :: "(" :: r1) =
      some (.match_ (.app f args) [(.tuplePat [.varPat x, .varPat y], b)], r3) := by
  simp [parseStmt, expects, ha, hb]

theorem parseStmt_assign (x : String) (r r' : List Tok) (v : ImpExpr) (hx : validIdent x = true)
    (hv : parseRhs r = some (v, r')) :
    parseStmt p (x :: "=" :: r) = some (.assign x v, r') := by
  have hx' := validIdent_ne x hx
  have h1 : x ≠ "if" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 : x ≠ "while" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h3 : x ≠ "for" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h4 : x ≠ "match" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  simp [parseStmt, hx'.1, h1, h2, h3, h4, hv]

theorem parseStmt_var (x : String) (r : List Tok) (hx : validIdent x = true)
    (hr : stmtStop r) : parseStmt p (x :: r) = some (.var x, r) := by
  have hx' := validIdent_ne x hx
  have h1 : x ≠ "if" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 : x ≠ "while" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h3 : x ≠ "for" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h4 : x ≠ "match" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  cases r with
  | nil => simp [parseStmt, hx'.1, h1, h2, h3, h4]
  | cons u r1 =>
    simp only [stmtStop] at hr
    rcases hr with rfl | rfl <;> simp [parseStmt, hx'.1, h1, h2, h3, h4]

end Steps

/-- The first two tokens of a statement: not `let` or `{`, and no `[` second. -/
def StmtHead : List Tok → Prop
  | t :: u :: _ => t ≠ "let" ∧ t ≠ "{" ∧ u ≠ "["
  | _ => False

theorem StmtHead_append (ts r : List Tok) (h : StmtHead ts) : StmtHead (ts ++ r) := by
  match ts, h with
  | _ :: _ :: _, h => exact h

theorem skipAnn_tyAnn (ty : String → Option Tok) (x : String) (r : List Tok) :
    skipAnn (tyAnn ty x ++ "=" :: r) = some r := by
  unfold tyAnn
  split <;> simp [skipAnn]

theorem parseSeq_let (n : Nat) (x : String) (r0 r r3 rest : List Tok) (v b : ImpExpr)
    (ha : skipAnn r0 = some r)
    (hv : parseRhs r = some (v, ";" :: r3)) (hb : parseSeq n r3 = some (b, rest)) :
    parseSeq (n + 1) ("let" :: "mut" :: x :: r0) = some (.letBind x v b, rest) := by
  rw [parseSeq.eq_def]
  simp [ha, hv, hb, expects]

theorem parseSeq_brace (n : Nat) (r r2 rest : List Tok) (a b : ImpExpr)
    (ha : parseSeq n r = some (a, "}" :: ";" :: r2)) (hb : parseSeq n r2 = some (b, rest)) :
    parseSeq (n + 1) ("{" :: r) = some (.seq a b, rest) := by
  rw [parseSeq.eq_def]
  simp [ha, hb, expects]

theorem parseSeq_arr (n : Nat) (x i s : String) (r rest : List Tok) (b : ImpExpr)
    (hx : validIdent x = true) (hb : parseSeq n r = some (b, rest)) :
    parseSeq (n + 1) (x :: "[" :: i :: "]" :: "=" :: s :: ";" :: r) =
      some (.letBind x (.app "array_update" [.var x, .var i, .var s]) b, rest) := by
  have hx' := validIdent_ne x hx
  have h1 : x ≠ "let" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [parseSeq.eq_def]
  simp [hx'.2.2.1, h1, hb, expects]

theorem parseSeq_var (n : Nat) (x : String) (rest : List Tok) (hx : validIdent x = true)
    (hr : seqStop rest) : parseSeq (n + 1) (x :: rest) = some (.var x, rest) := by
  have hx' := validIdent_ne x hx
  have h1 : x ≠ "let" := hx'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst : stmtStop rest := stmtStop_of_seqStop rest hr
  have hp := parseStmt_var (parseSeq n) x rest hx hst
  rw [parseSeq.eq_def]
  cases rest with
  | nil => simp [h1, hx'.2.2.1, hp]
  | cons u r1 =>
    simp only [seqStop] at hr
    subst hr
    simp [h1, hx'.2.2.1, hp]

theorem parseSeq_of_stmt (n : Nat) (ts rest : List Tok) (e : ImpExpr) (hh : StmtHead ts)
    (hs : parseStmt (parseSeq n) ts = some (e, rest)) (hr : seqStop rest) :
    parseSeq (n + 1) ts = some (e, rest) := by
  match ts, hh with
  | t :: u :: r, ⟨h1, h2, h3⟩ =>
    rw [parseSeq.eq_def]
    cases rest with
    | nil => simp [h1, h2, h3, hs]
    | cons v r1 =>
      simp only [seqStop] at hr
      subst hr
      simp [h1, h2, h3, hs]

theorem parseSeq_of_stmt_semi (n : Nat) (ts r1 rest : List Tok) (a b : ImpExpr)
    (hh : StmtHead ts) (hs : parseStmt (parseSeq n) ts = some (a, ";" :: r1))
    (hb : parseSeq n r1 = some (b, rest)) :
    parseSeq (n + 1) ts = some (.seq a b, rest) := by
  match ts, hh with
  | t :: u :: r, ⟨h1, h2, h3⟩ =>
    rw [parseSeq.eq_def]
    simp [h1, h2, h3, hs, hb]

theorem arrUpdateArgs_eq (x : String) (v : ImpExpr) (i s : String)
    (h : arrUpdateArgs x v = some (i, s)) :
    v = .app "array_update" [.var x, .var i, .var s] ∧ validIdent i = true ∧
      validIdent s = true := by
  unfold arrUpdateArgs at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, hi, hs⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hi, hs⟩
    · simp at h
  · simp at h

/-- A statement sequence parses back from its tokens followed by `}` or the end
    of input; a statement that is not a binding or a sequence also parses back
    as a statement, followed by `;`, `}` or the end of input. -/
theorem parseSeq_ppToks (ty : String → Option Tok) (e : ImpExpr) :
    ∀ ts, ppToks ty e = some ts →
    (∀ n rest, ts.length < n → seqStop rest → parseSeq n (ts ++ rest) = some (e, rest)) ∧
    (needsBrace e = false → ∀ n rest, ts.length ≤ n → stmtStop rest →
      StmtHead (ts ++ rest) ∧ parseStmt (parseSeq n) (ts ++ rest) = some (e, rest)) := by
  have ofStmt : ∀ (e : ImpExpr) (ts : List Tok),
      (∀ n rest, ts.length ≤ n → stmtStop rest →
        StmtHead (ts ++ rest) ∧ parseStmt (parseSeq n) (ts ++ rest) = some (e, rest)) →
      ∀ n rest, ts.length < n → seqStop rest → parseSeq n (ts ++ rest) = some (e, rest) := by
    intro e ts hs n rest hn hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨hh, hp⟩ := hs m rest (by omega) (stmtStop_of_seqStop rest hr)
    exact parseSeq_of_stmt m _ rest e hh hp hr
  have both : ∀ (e : ImpExpr) (ts : List Tok), StmtHead ts →
      (∀ n rest, ts.length ≤ n → stmtStop rest →
        parseStmt (parseSeq n) (ts ++ rest) = some (e, rest)) →
      (∀ n rest, ts.length < n → seqStop rest → parseSeq n (ts ++ rest) = some (e, rest)) ∧
      (needsBrace e = false → ∀ n rest, ts.length ≤ n → stmtStop rest →
        StmtHead (ts ++ rest) ∧ parseStmt (parseSeq n) (ts ++ rest) = some (e, rest)) := by
    intro e ts hh hs
    have hb : ∀ n rest, ts.length ≤ n → stmtStop rest →
        StmtHead (ts ++ rest) ∧ parseStmt (parseSeq n) (ts ++ rest) = some (e, rest) :=
      fun n rest hn hr => ⟨StmtHead_append _ _ hh, hs n rest hn hr⟩
    exact ⟨ofStmt _ _ hb, fun _ => hb⟩
  induction e using ImpExpr.ind
  case letBind x v b _ ihb =>
    intro ts h
    refine ⟨?_, fun hnb => by simp [needsBrace] at hnb⟩
    intro n rest hn hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [ppToks] at h
    split at h
    · rename_i hx
      cases htb : ppToks ty b with
      | none => simp [htb] at h
      | some tb =>
        simp only [htb] at h
        cases ha : arrUpdateArgs x v with
        | some p =>
          obtain ⟨i, s⟩ := p
          simp only [ha, Option.some.injEq] at h
          subst h
          obtain ⟨rfl, _, _⟩ := arrUpdateArgs_eq x v i s ha
          simp only [List.length_append, List.length_cons, List.length_nil] at hn
          have := (ihb tb htb).1 m rest (by omega) hr
          simp only [List.cons_append, List.nil_append]
          exact parseSeq_arr m x i s _ rest b hx this
        | none =>
          simp only [ha] at h
          cases hv : rhsToks v with
          | none => simp [hv] at h
          | some tv =>
            simp only [hv, Option.map_some, Option.some.injEq] at h
            subst h
            simp only [List.length_append, List.length_cons, List.length_nil] at hn
            have hbp := (ihb tb htb).1 m rest (by omega) hr
            have hvp := parseRhs_rhsToks v tv hv (";" :: (tb ++ rest)) (Or.inr rfl)
            simp only [List.cons_append, List.nil_append, List.append_assoc]
            exact parseSeq_let m x _ _ _ rest v b (skipAnn_tyAnn ty x _) hvp hbp
    · simp at h
  case seq a b iha ihb =>
    intro ts h
    refine ⟨?_, fun hnb => by simp [needsBrace] at hnb⟩
    intro n rest hn hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [ppToks] at h
    cases hta : ppToks ty a <;> cases htb : ppToks ty b <;>
      simp only [hta, htb, reduceCtorEq, Option.some.injEq] at h
    rename_i ta tb
    subst h
    have hbp := (ihb tb htb).1 m rest
    cases hnb : needsBrace a with
    | true =>
      simp only [hnb, if_true, List.length_append, List.length_cons, List.length_nil] at hn ⊢
      have hap := (iha ta hta).1 m ("}" :: ";" :: (tb ++ rest)) (by omega) rfl
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      exact parseSeq_brace m _ _ rest a b hap (hbp (by omega) hr)
    | false =>
      simp only [hnb, Bool.false_eq_true, if_false, List.length_append, List.length_cons,
        List.length_nil] at hn ⊢
      obtain ⟨hh, hap⟩ := (iha ta hta).2 hnb m (";" :: (tb ++ rest)) (by omega) (Or.inr rfl)
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      exact parseSeq_of_stmt_semi m _ _ rest a b hh hap (hbp (by omega) hr)
  case unitVal =>
    intro ts h
    simp only [ppToks, Option.some.injEq] at h
    subst h
    have hs : ∀ n rest, (["(", ")"] : List Tok).length ≤ n → stmtStop rest →
        parseStmt (parseSeq n) (["(", ")"] ++ rest) = some (.unitVal, rest) :=
      fun n rest _ _ => parseStmt_unit _ rest
    have hh : StmtHead ["(", ")"] := by simp [StmtHead]
    exact both _ _ hh hs
  case var x =>
    intro ts h
    refine ⟨?_, fun hnb => by simp [needsBrace] at hnb⟩
    intro n rest hn hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [ppToks] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      simpa using parseSeq_var m x rest hx hr
    · simp at h
  case assign x v _ =>
    intro ts h
    simp only [ppToks] at h
    split at h
    · rename_i hx
      cases hv : rhsToks v with
      | none => simp [hv] at h
      | some tv =>
        simp only [hv, Option.map_some, Option.some.injEq] at h
        subst h
        have hx' := validIdent_ne x hx
        have hs : ∀ n rest, ([x, "="] ++ tv).length ≤ n → stmtStop rest →
            parseStmt (parseSeq n) ([x, "="] ++ tv ++ rest) = some (.assign x v, rest) := by
          intro n rest _ hr
          simp only [List.cons_append, List.nil_append]
          exact parseStmt_assign _ x _ rest v hx (parseRhs_rhsToks v tv hv rest hr)
        have hh : StmtHead ([x, "="] ++ tv) := by
          simp [StmtHead, hx'.2.2.2.2.2.2.2.2.2.2.2.2.1, hx'.2.2.1]
        exact both _ _ hh hs
    · simp at h
  case ifThenElse c t e ihc iht ihe =>
    intro ts h
    clear ihc
    cases c
    case var v =>
      simp only [ppToks] at h
      split at h
      · rename_i hvi
        cases htt : ppToks ty t <;> cases hte : ppToks ty e <;>
          simp only [htt, hte, reduceCtorEq, Option.some.injEq] at h
        rename_i tt te
        subst h
        have hs : ∀ n rest, (["if", v, "{"] ++ tt ++ ["}", "else", "{"] ++ te ++ ["}"]).length ≤ n →
            stmtStop rest → parseStmt (parseSeq n)
              ((["if", v, "{"] ++ tt ++ ["}", "else", "{"] ++ te ++ ["}"]) ++ rest) =
              some (.ifThenElse (.var v) t e, rest) := by
          intro n rest hn _
          simp only [List.length_append, List.length_cons, List.length_nil] at hn
          simp only [List.cons_append, List.nil_append, List.append_assoc]
          exact parseStmt_if _ v _ _ rest t e
            ((iht tt htt).1 n _ (by omega) rfl) ((ihe te hte).1 n _ (by omega) rfl)
        have hh : StmtHead (["if", v, "{"] ++ tt ++ ["}", "else", "{"] ++ te ++ ["}"]) := by
          simp [StmtHead, (validIdent_ne v hvi).2.2.2.2.1]
        exact both _ _ hh hs
      · simp at h
    all_goals simp [ppToks] at h
  case whileLoop c b ihc ihb =>
    intro ts h
    clear ihc
    cases c
    case var v =>
      simp only [ppToks] at h
      split at h
      · rename_i hvi
        cases htb : ppToks ty b <;> simp only [htb, Option.map_none, Option.map_some,
          reduceCtorEq, Option.some.injEq] at h
        rename_i tb
        subst h
        have hs : ∀ n rest, (["while", v, "{"] ++ tb ++ ["}"]).length ≤ n →
            stmtStop rest → parseStmt (parseSeq n) ((["while", v, "{"] ++ tb ++ ["}"]) ++ rest) =
              some (.whileLoop (.var v) b, rest) := by
          intro n rest hn _
          simp only [List.length_append, List.length_cons, List.length_nil] at hn
          simp only [List.cons_append, List.nil_append, List.append_assoc]
          exact parseStmt_while _ v _ rest b ((ihb tb htb).1 n _ (by omega) rfl)
        have hh : StmtHead (["while", v, "{"] ++ tb ++ ["}"]) := by
          simp [StmtHead, (validIdent_ne v hvi).2.2.2.2.1]
        exact both _ _ hh hs
      · simp at h
    all_goals simp [ppToks] at h
  case forFold x lo hi b _ _ ihb =>
    intro ts h
    simp only [ppToks] at h
    split at h
    · rename_i hx
      cases hl : boundToks lo <;> cases hh : boundToks hi <;> cases htb : ppToks ty b <;>
        simp only [hl, hh, htb, reduceCtorEq, Option.some.injEq] at h
      rename_i tl th tb
      subst h
      have hx' := validIdent_ne x hx
      have hs : ∀ n rest,
          (["for", x, "in"] ++ tl ++ [".."] ++ th ++ ["{"] ++ tb ++ ["}"]).length ≤ n →
          stmtStop rest → parseStmt (parseSeq n)
            ((["for", x, "in"] ++ tl ++ [".."] ++ th ++ ["{"] ++ tb ++ ["}"]) ++ rest) =
            some (.forFold x lo hi b, rest) := by
        intro n rest hn _
        simp only [List.length_append, List.length_cons, List.length_nil] at hn
        simp only [List.cons_append, List.nil_append, List.append_assoc]
        exact parseStmt_for _ x _ _ _ rest lo hi b
          (parseBound_boundToks lo tl hl _ _ (by simp))
          (parseBound_boundToks hi th hh _ _ (by simp))
          ((ihb tb htb).1 n _ (by omega) rfl)
      have hh : StmtHead (["for", x, "in"] ++ tl ++ [".."] ++ th ++ ["{"] ++ tb ++ ["}"]) := by
        simp [StmtHead, hx'.2.2.2.2.1]
      exact both _ _ hh hs
    · simp at h
  case match_ scrut arms ihs iharms =>
    intro ts h
    clear ihs
    rcases arms with _ | ⟨⟨pat, b⟩, _ | ⟨_, _⟩⟩
    case cons.nil =>
      have ihb := iharms (pat, b) (by simp)
      cases scrut
      case app f args =>
        rcases pat with _ | _ | _ | pats | _ | _ | _ | _ | _
        case tuplePat =>
          rcases pats with _ | ⟨p1, _ | ⟨p2, _ | _⟩⟩
          case cons.cons.nil =>
            cases p1
            case varPat x =>
              cases p2
              case varPat y =>
                simp only [ppToks] at h
                split at h
                · rename_i hxy
                  simp only [Bool.and_eq_true] at hxy
                  cases hc : callToks f args <;> cases htb : ppToks ty b <;>
                    simp only [hc, htb, reduceCtorEq, Option.some.injEq] at h
                  rename_i tc tb
                  subst h
                  obtain ⟨hf, ta, hta, rfl⟩ := callToks_eq f args tc hc
                  have hf' := validIdent_ne f hf
                  have hs : ∀ n rest, (["match"] ++ (f :: "(" :: ta) ++
                        ["{", "(", x, ",", y, ")", "=>", "{"] ++ tb ++ ["}", "}"]).length ≤ n →
                      stmtStop rest → parseStmt (parseSeq n)
                        ((["match"] ++ (f :: "(" :: ta) ++
                          ["{", "(", x, ",", y, ")", "=>", "{"] ++ tb ++ ["}", "}"]) ++ rest) =
                        some (.match_ (.app f args) [(.tuplePat [.varPat x, .varPat y], b)],
                          rest) := by
                    intro n rest hn _
                    simp only [List.length_append, List.length_cons, List.length_nil] at hn
                    simp only [List.cons_append, List.nil_append, List.append_assoc]
                    exact parseStmt_match _ f x y args _ _ rest b
                      (parseArgs_argToks args ta hta _)
                      ((ihb tb htb).1 n _ (by omega) rfl)
                  have hh : StmtHead (["match"] ++ (f :: "(" :: ta) ++
                      ["{", "(", x, ",", y, ")", "=>", "{"] ++ tb ++ ["}", "}"]) := by
                    simp [StmtHead, hf'.2.2.2.2.1]
                  exact both _ _ hh hs
                · simp at h
              all_goals simp [ppToks] at h
            all_goals simp [ppToks] at h
          all_goals simp [ppToks] at h
        all_goals simp [ppToks] at h
      all_goals simp [ppToks] at h
    all_goals simp [ppToks] at h
  case tuple es _ =>
    intro ts h
    rcases es with _ | ⟨a, _ | ⟨b, cs⟩⟩
    · simp [ppToks] at h
    · simp [ppToks] at h
    · simp only [ppToks] at h
      cases hta : argToks (a :: b :: cs) with
      | none => simp [hta] at h
      | some ta =>
        simp only [hta, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨x, r, rfl, hx⟩ := argToks_cons_head a (b :: cs) _ hta
        have hx' := validIdent_ne x hx
        have hs : ∀ n rest, ("(" :: x :: r).length ≤ n → stmtStop rest →
            parseStmt (parseSeq n) (("(" :: x :: r) ++ rest) =
              some (.tuple (a :: b :: cs), rest) := by
          intro n rest _ _
          have ha := parseArgs_argToks _ _ hta rest
          simp only [List.cons_append] at ha ⊢
          exact parseStmt_tuple _ x _ rest _ hx'.2.1 ha
        have hh : StmtHead ("(" :: x :: r) := by simp [StmtHead, hx'.2.2.2.2.1]
        exact both _ _ hh hs
  all_goals intro ts h; simp [ppToks] at h

/-! ## §9  Function signatures -/

/-- The parameters `x : T` of a function, separated by `,` and closed by `)`. -/
def paramToks : List (String × Tok) → Option (List Tok)
  | [] => some [")"]
  | [(x, t)] => if validIdent x then some [x, ":", t, ")"] else none
  | (x, t) :: p :: ps =>
      if validIdent x then (paramToks (p :: ps)).map fun r => [x, ":", t, ","] ++ r else none

/-- Function parameters up to and including `)`. -/
def parseParams : List Tok → Option (List (String × Tok) × List Tok)
  | [] => none
  | x :: r =>
      if x = ")" then some ([], r)
      else
        match r with
        | c :: t :: u :: r' =>
            if c = ":" then
              if u = ")" then some ([(x, t)], r')
              else if u = "," then (parseParams r').map fun q => ((x, t) :: q.1, q.2)
              else none
            else none
        | _ => none

theorem parseParams_paramToks (ps : List (String × Tok)) (pt : List Tok)
    (h : paramToks ps = some pt) (rest : List Tok) :
    parseParams (pt ++ rest) = some (ps, rest) := by
  induction ps generalizing pt with
  | nil =>
    simp only [paramToks, Option.some.injEq] at h
    subst h; simp [parseParams.eq_def]
  | cons p ps ih =>
    obtain ⟨x, t⟩ := p
    cases ps with
    | nil =>
      simp only [paramToks] at h
      split at h
      · rename_i hx
        simp only [Option.some.injEq] at h
        subst h
        simp [parseParams.eq_def, (validIdent_ne x hx).2.1]
      · simp at h
    | cons q qs =>
      simp only [paramToks] at h
      split at h
      · rename_i hx
        cases hq : paramToks (q :: qs) with
        | none => simp [hq] at h
        | some r =>
          simp only [hq, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [List.cons_append, List.nil_append]
          rw [parseParams.eq_def]
          simp [(validIdent_ne x hx).2.1, ih r hq]
      · simp at h

end CatCrypt.Crypto.Hax.ImpRust

/-! ## §10  Text -/

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr)
open ImpRust

/-- The Rust text of a statement sequence, with `ty` the Rust types of the bound
    locals, or `none` outside the printed fragment. -/
def ppImpRust (ty : String → Option Tok) (e : ImpExpr) : Option String :=
  (ppToks ty e).bind fun ts =>
    if ts.all tokOK then some (String.ofList (renderChars ts)) else none

/-- The statement sequence of a Rust text in the printed fragment. -/
def parseImpRust (s : String) : Option ImpExpr :=
  let ts := lex s.toList
  match parseSeq (ts.length + 1) ts with
  | some (e, []) => some e
  | _ => none

/-- **Round trip.**  The parser reads a printed statement sequence back. -/
theorem parse_ppImpRust (ty : String → Option Tok) (e : ImpExpr) (s : String)
    (h : ppImpRust ty e = some s) : parseImpRust s = some e := by
  unfold ppImpRust at h
  cases hp : ppToks ty e with
  | none => simp [hp] at h
  | some ts =>
    simp only [hp, Option.bind_some] at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      have hseq := (parseSeq_ppToks ty e ts hp).1 (ts.length + 1) [] (by omega) trivial
      simp only [List.append_nil] at hseq
      simp [parseImpRust, lex_renderChars ts hok, hseq]
    · simp at h

/-- The Rust function `pub fn name(x₁ : T₁, …) { body }`, with the parameter
    types `Tᵢ` and the local types `ty` given, each type a single token. -/
def ppImpRustFn (name : String) (params : List (String × Tok)) (ty : String → Option Tok)
    (body : ImpExpr) : Option String :=
  if validIdent name then
    match paramToks params, ppToks ty body with
    | some pt, some tb =>
        let ts := ["pub", "fn", name, "("] ++ pt ++ ["{"] ++ tb ++ ["}"]
        if ts.all tokOK then some (String.ofList (renderChars ts)) else none
    | _, _ => none
  else none

/-- The name, the parameters and the body of a Rust function in the printed
    fragment. -/
def parseImpRustFn (s : String) : Option (String × List (String × Tok) × ImpExpr) :=
  match lex s.toList with
  | p :: f :: name :: r =>
      if p = "pub" ∧ f = "fn" then do
        let r1 ← expects ["("] r
        let (ps, r2) ← parseParams r1
        let r3 ← expects ["{"] r2
        match parseSeq r3.length r3 with
        | some (b, [c]) => if c = "}" then some (name, ps, b) else none
        | _ => none
      else none
  | _ => none

/-- **Round trip.**  The parser reads a printed function back. -/
theorem parse_ppImpRustFn (name : String) (params : List (String × Tok))
    (ty : String → Option Tok) (body : ImpExpr) (s : String)
    (h : ppImpRustFn name params ty body = some s) :
    parseImpRustFn s = some (name, params, body) := by
  unfold ppImpRustFn at h
  split at h
  · cases hp : paramToks params <;> cases hb : ppToks ty body <;>
      simp only [hp, hb, reduceCtorEq] at h
    rename_i pt tb
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      have hseq := (parseSeq_ppToks ty body tb hb).1 (tb ++ ["}"]).length ["}"]
        (by simp) rfl
      simp only [List.length_append, List.length_singleton] at hseq
      simp only [parseImpRustFn, String.toList_ofList, lex_renderChars _ hok]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      simp [expects, parseParams_paramToks params pt hp, hseq]
    · simp at h
  · simp at h

/-! ## §11  Functions with a return type -/

/-- The Rust function `pub fn name(x₁ : T₁, …) -> T { body }`, with `T` the
    return type; the tail of `body` is the returned expression. -/
def ppImpRustFnRet (name : String) (params : List (String × Tok)) (retTy : Tok)
    (ty : String → Option Tok) (body : ImpExpr) : Option String :=
  if validIdent name then
    match paramToks params, ppToks ty body with
    | some pt, some tb =>
        let ts := ["pub", "fn", name, "("] ++ pt ++ ["->", retTy, "{"] ++ tb ++ ["}"]
        if ts.all tokOK then some (String.ofList (renderChars ts)) else none
    | _, _ => none
  else none

/-- The name, the parameters, the return type and the body of a Rust function
    with a return type, in the printed fragment. -/
def parseImpRustFnRet (s : String) :
    Option (String × List (String × Tok) × Tok × ImpExpr) :=
  match lex s.toList with
  | p :: f :: name :: r =>
      if p = "pub" ∧ f = "fn" then do
        let r1 ← expects ["("] r
        let (ps, r2) ← parseParams r1
        match r2 with
        | a :: retTy :: r3 =>
            if a = "->" then do
              let r4 ← expects ["{"] r3
              match parseSeq r4.length r4 with
              | some (b, [c]) => if c = "}" then some (name, ps, retTy, b) else none
              | _ => none
            else none
        | _ => none
      else none
  | _ => none

/-- **Round trip.**  The parser reads a printed function with a return type
    back. -/
theorem parse_ppImpRustFnRet (name : String) (params : List (String × Tok)) (retTy : Tok)
    (ty : String → Option Tok) (body : ImpExpr) (s : String)
    (h : ppImpRustFnRet name params retTy ty body = some s) :
    parseImpRustFnRet s = some (name, params, retTy, body) := by
  unfold ppImpRustFnRet at h
  split at h
  · cases hp : paramToks params <;> cases hb : ppToks ty body <;>
      simp only [hp, hb, reduceCtorEq] at h
    rename_i pt tb
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      have hseq := (parseSeq_ppToks ty body tb hb).1 (tb ++ ["}"]).length ["}"]
        (by simp) rfl
      simp only [List.length_append, List.length_singleton] at hseq
      simp only [parseImpRustFnRet, String.toList_ofList, lex_renderChars _ hok]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      simp [expects, parseParams_paramToks params pt hp, hseq]
    · simp at h
  · simp at h

end CatCrypt.Crypto.Hax
