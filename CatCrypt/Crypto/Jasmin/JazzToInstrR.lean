/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminAST
public meta import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCryptCore.Tactics.KatGuard

@[expose] public section
set_option autoImplicit false

/-!
# `.jazz` text → `InstrR` parser

A recursive-descent parser from Jasmin surface syntax to the `JasminAST` types
(`FunDecl`, `InstrR`, `PExpr`, `LVal`) interpreted by `bignumExec`. The accepted
subset is the one the `S2NBignumSSA` ports and their printer
`Emit.emitFunDecl` use. Every function is total: recursion is bounded by a fuel
argument proportional to the input length, so the parser also reduces in the
kernel.

## Accepted subset

* Top level: function declarations `[#[…]] [export | inline] fn f(params)
  [-> types] { body }`. Annotations `#[…]` and the return-type list are read and
  discarded; the results are the names of the final `return x, y;`.
* Parameters and declarations: `reg | stack | inline`, an optional `ptr`,
  `mut` or `const` qualifier, and a type `uNN`, `uNN[k]`, `bool` or `int`; a
  declaration lists one or more names, separated by spaces or commas. A type
  `uNN[k]` is the array type `sarr (k * bytes uNN)` with element width `uNN`.
* Statements:
  - `lv = e;` (`Cassgn`, tag `AT_none`, type the declared type of `lv`);
  - `lv OP= e;` for `OP` in `+ - * & | ^ << >> >>s`, read as `lv = lv OP e`;
  - `lv₁, …, lvₙ = #OP(args);` (`Copn` with `Oasm ⟨OP⟩`), and `#OP(args);`;
  - `lv₁, …, lvₙ = f(args);` and `f(args);` (`Ccall .DoNotInline`);
  - `if e { … } else { … }` (the `else` part optional);
  - `for i = lo to hi { … }` with numeral bounds;
  - `while e { … }`, `while { … } e { … }` and `while { … } e`.
* L-values: `x`, `_` (`Lnone {} (.sword .U64)`), `x[e]` (`Laset .AAscale`)
  and `[:uNN x + e]` or `[x + e]` (`Lmem`, width `U64` when omitted).
* Expressions: decimal and `0x` numerals (`Pconst`), `-k` (`Pconst (-k)`),
  `true`, `false`, variables, `x[e]` (`Pget .AAscale`), memory reads
  `[:uNN x + e]` (`Pload`), `-e` (`0 - e`), `!e` (`Olnot`), the cast `(NNu) e`
  (`Ozeroext`), parentheses, and the binary operators
  `|| && | ^ & == != < <= > >= <s <=s >s >=s << >> >>s + - *` with C precedence
  and left associativity. The width of a binary operator is the width of its
  left operand when that is a word-typed variable, load, array read or cast, and
  otherwise the width of the assignment target.
* Comments `// …` and `/* … */`.

Any other construct (`require`, `param`, globals, string literals, `downto`
loops, `else if`, calls or intrinsics inside an expression, undeclared
variables) is a parse error naming the construct.

## Main definitions

* `tokenize`: the lexer.
* `parseJazz`: `.jazz` text → `List FunDecl`.
* `parseJazzProg`: `.jazz` text → `JasminProg`.
* `parseJazzBody`: a statement sequence under a given declaration environment
  → `List InstrR`.
* `instrsBEq`, `funDeclBEq`, `parsesTo`: structural equality of the AST and the
  check that a text parses to given declarations.

The `RoundTrip` section checks, by `#kat`, that the text `Emit.emitFunDecl`
prints for the `bignum_add_4` port parses to that port's `FunDecl` (with the
carry variable `cf` typed `sbool`, as its `reg bool` declaration in the text
states), and that a statement sequence using the control constructs parses to
its AST.
-/

namespace CatCrypt.Crypto.Jasmin.JazzToInstrR

open CatCrypt.Crypto.Jasmin

/-! ## Tokens -/

/-- Binary arithmetic and bitwise operator tokens, also used in compound
    assignments `x OP= e`. -/
inductive BinTok where
  | add | sub | mul | land | lor | lxor | shl | shr | sar
  deriving Repr, DecidableEq, Inhabited

/-- Comparison tokens; `lts`… are the signed forms `<s`, `<=s`, `>s`, `>=s`. -/
inductive CmpTok where
  | eq | ne | lt | le | gt | ge | lts | les | gts | ges
  deriving Repr, DecidableEq, Inhabited

/-- A token of the accepted `.jazz` subset. -/
inductive Token where
  | ident (s : String)
  | num (n : Nat)
  | lparen | rparen | lbrace | rbrace | lbrack | rbrack
  | semi | comma | colon | assign | hash | bang | arrow
  | bin (o : BinTok)
  | binEq (o : BinTok)
  | cmp (c : CmpTok)
  | andAnd | orOr
  deriving Repr, DecidableEq, Inhabited

/-! ## Lexer -/

/-- The value of a hexadecimal (or decimal) digit character; the same function as
    `hexDigitValue`, restated here so that the `#kat` checks below run
    without native code for the `.jinc` parser. -/
def hexDigitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else (c.toLower.toNat - 'a'.toNat) + 10

/-- Split off the leading identifier (alphanumerics and `_`); the same function as
    `readIdent`. -/
def readIdent (cs : List Char) : String × List Char :=
  (String.ofList (cs.takeWhile (fun c => c.isAlphanum || c == '_')),
   cs.dropWhile (fun c => c.isAlphanum || c == '_'))

/-- A hexadecimal digit. -/
def isHexChar (c : Char) : Bool :=
  c.isDigit || (c.toLower ≥ 'a' && c.toLower ≤ 'f')

/-- The value of a digit string in base `base`. -/
def digitsVal (base : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun a c => a * base + hexDigitValue c) 0

/-- Read a decimal or `0x` hexadecimal numeral from the front of the input. -/
def readNumber : List Char → Nat × List Char
  | '0' :: 'x' :: rest => (digitsVal 16 (rest.takeWhile isHexChar), rest.dropWhile isHexChar)
  | '0' :: 'X' :: rest => (digitsVal 16 (rest.takeWhile isHexChar), rest.dropWhile isHexChar)
  | cs => (digitsVal 10 (cs.takeWhile Char.isDigit), cs.dropWhile Char.isDigit)

/-- The input after the `*/` closing a block comment, or `none` if there is none. -/
def dropBlockComment : List Char → Option (List Char)
  | '*' :: '/' :: rest => some rest
  | _ :: rest => dropBlockComment rest
  | [] => none

/-- The lexer loop. Each step consumes at least one character, so fuel
    `cs.length + 1` suffices. -/
def lexF : Nat → List Char → List Token → Except String (List Token)
  | 0, _, _ => .error "JazzToInstrR.lex: fuel exhausted"
  | _ + 1, [], acc => .ok acc.reverse
  | f + 1, c :: cs, acc =>
    if c.isWhitespace then lexF f cs acc else
    match c, cs with
    | '/', '/' :: rest => lexF f (rest.dropWhile (· ≠ '\n')) acc
    | '/', '*' :: rest =>
        match dropBlockComment rest with
        | some r => lexF f r acc
        | none => .error "JazzToInstrR.lex: unterminated block comment"
    | '>', '>' :: 's' :: '=' :: rest => lexF f rest (.binEq .sar :: acc)
    | '>', '>' :: '=' :: rest => lexF f rest (.binEq .shr :: acc)
    | '<', '<' :: '=' :: rest => lexF f rest (.binEq .shl :: acc)
    | '>', '>' :: 's' :: rest => lexF f rest (.bin .sar :: acc)
    | '>', '>' :: rest => lexF f rest (.bin .shr :: acc)
    | '<', '<' :: rest => lexF f rest (.bin .shl :: acc)
    | '<', '=' :: 's' :: rest => lexF f rest (.cmp .les :: acc)
    | '>', '=' :: 's' :: rest => lexF f rest (.cmp .ges :: acc)
    | '<', '=' :: rest => lexF f rest (.cmp .le :: acc)
    | '>', '=' :: rest => lexF f rest (.cmp .ge :: acc)
    | '<', 's' :: rest => lexF f rest (.cmp .lts :: acc)
    | '>', 's' :: rest => lexF f rest (.cmp .gts :: acc)
    | '<', rest => lexF f rest (.cmp .lt :: acc)
    | '>', rest => lexF f rest (.cmp .gt :: acc)
    | '=', '=' :: rest => lexF f rest (.cmp .eq :: acc)
    | '!', '=' :: rest => lexF f rest (.cmp .ne :: acc)
    | '&', '&' :: rest => lexF f rest (.andAnd :: acc)
    | '|', '|' :: rest => lexF f rest (.orOr :: acc)
    | '+', '=' :: rest => lexF f rest (.binEq .add :: acc)
    | '-', '=' :: rest => lexF f rest (.binEq .sub :: acc)
    | '*', '=' :: rest => lexF f rest (.binEq .mul :: acc)
    | '&', '=' :: rest => lexF f rest (.binEq .land :: acc)
    | '|', '=' :: rest => lexF f rest (.binEq .lor :: acc)
    | '^', '=' :: rest => lexF f rest (.binEq .lxor :: acc)
    | '-', '>' :: rest => lexF f rest (.arrow :: acc)
    | '+', rest => lexF f rest (.bin .add :: acc)
    | '-', rest => lexF f rest (.bin .sub :: acc)
    | '*', rest => lexF f rest (.bin .mul :: acc)
    | '&', rest => lexF f rest (.bin .land :: acc)
    | '|', rest => lexF f rest (.bin .lor :: acc)
    | '^', rest => lexF f rest (.bin .lxor :: acc)
    | '(', rest => lexF f rest (.lparen :: acc)
    | ')', rest => lexF f rest (.rparen :: acc)
    | '{', rest => lexF f rest (.lbrace :: acc)
    | '}', rest => lexF f rest (.rbrace :: acc)
    | '[', rest => lexF f rest (.lbrack :: acc)
    | ']', rest => lexF f rest (.rbrack :: acc)
    | ';', rest => lexF f rest (.semi :: acc)
    | ',', rest => lexF f rest (.comma :: acc)
    | ':', rest => lexF f rest (.colon :: acc)
    | '=', rest => lexF f rest (.assign :: acc)
    | '#', rest => lexF f rest (.hash :: acc)
    | '!', rest => lexF f rest (.bang :: acc)
    | '"', _ => .error "JazzToInstrR.lex: string literals (require, param) are not in the subset"
    | c, rest =>
        if c.isAlpha || c == '_' then
          let (id, rest') := readIdent (c :: rest)
          lexF f rest' (.ident id :: acc)
        else if c.isDigit then
          let (n, rest') := readNumber (c :: rest)
          lexF f rest' (.num n :: acc)
        else .error s!"JazzToInstrR.lex: unexpected character '{c}'"

/-- Tokenize a `.jazz` text. -/
def tokenize (s : String) : Except String (List Token) :=
  let cs := s.toList
  lexF (cs.length + 1) cs []

/-! ## Parser state -/

/-- A declared variable: its name, its type, and its word width (the element
    width for an array, `U64` for `bool` and `int`). -/
structure VDecl where
  name : String
  ty : SType
  ews : WSize
  deriving Inhabited

/-- Parser state: remaining tokens, the declarations in scope, and the fuel
    bound given to every recursive parsing function. -/
structure St where
  toks : List Token
  env : List VDecl := []
  fuel : Nat
  deriving Inhabited

/-- The parser monad. -/
abbrev P := StateT St (Except String)

/-- Fail with a message. -/
def fail {α : Type} (msg : String) : P α := throwThe String ("JazzToInstrR: " ++ msg)

/-- The next token. -/
def peek : P (Option Token) := do return (← get).toks.head?

/-- The token after the next one. -/
def peek2 : P (Option Token) := do return (← get).toks.tail.head?

/-- Consume one token. -/
def advance : P Unit := modify fun st => { st with toks := st.toks.tail }

/-- Consume the token `t`, failing on any other. -/
def expect (t : Token) : P Unit := do
  match ← peek with
  | some t' => if t' = t then advance else fail s!"expected {repr t}, found {repr t'}"
  | none => fail s!"expected {repr t}, found end of input"

/-- Consume an identifier. -/
def expectIdent : P String := do
  match ← peek with
  | some (.ident s) => advance; return s
  | some t => fail s!"expected identifier, found {repr t}"
  | none => fail "expected identifier, found end of input"

/-- Consume a numeral. -/
def expectNum : P Nat := do
  match ← peek with
  | some (.num n) => advance; return n
  | some t => fail s!"expected numeral, found {repr t}"
  | none => fail "expected numeral, found end of input"

/-- The declaration of a variable in scope. -/
def lookupVar (x : String) : P VDecl := do
  match (← get).env.find? (·.name == x) with
  | some d => return d
  | none => fail s!"undeclared variable '{x}'"

/-- Bring a declaration into scope. -/
def declare (d : VDecl) : P Unit := modify fun st => { st with env := d :: st.env }

/-- The variable of a declaration. -/
def VDecl.varI (d : VDecl) : VarI := { var := { vname := d.name, vtype := d.ty } }

/-- The local-variable expression of a declaration. -/
def VDecl.pvar (d : VDecl) : PExpr := .Pvar { gv := d.varI, gs := false }

/-- The word size named `uNN`. -/
def wsizeOfName : String → Option WSize
  | "u8" => some .U8 | "u16" => some .U16 | "u32" => some .U32
  | "u64" => some .U64 | "u128" => some .U128 | "u256" => some .U256
  | "u512" => some .U512 | _ => none

/-- The word size with `n` bits. -/
def wsizeOfBits : Nat → Option WSize
  | 8 => some .U8 | 16 => some .U16 | 32 => some .U32 | 64 => some .U64
  | 128 => some .U128 | 256 => some .U256 | 512 => some .U512 | _ => none

/-- Parse a type `uNN`, `uNN[k]`, `bool` or `int`, returning the type and its
    word width. -/
def parseType : P (SType × WSize) := do
  let s ← expectIdent
  match s with
  | "bool" => return (.sbool, .U64)
  | "int" => return (.sint, .U64)
  | _ =>
    match wsizeOfName s with
    | none => fail s!"unsupported type '{s}'"
    | some ws =>
      if (← peek) = some .lbrack then
        advance
        let k ← expectNum
        expect .rbrack
        return (.sarr (k * ws.bytes), ws)
      else return (.sword ws, ws)

/-- Skip the storage qualifiers `ptr`, `mut` and `const` (at most two). -/
def skipQualifiers : P Unit := do
  for _ in [0, 1] do
    match ← peek with
    | some (.ident "ptr") | some (.ident "mut") | some (.ident "const") => advance
    | _ => pure ()

/-- Parse the names of a declaration up to its `;`, declaring each. -/
def parseDeclNamesF : Nat → SType → WSize → P Unit
  | 0, _, _ => fail "fuel exhausted in a declaration"
  | f + 1, ty, ws => do
    let x ← expectIdent
    declare { name := x, ty := ty, ews := ws }
    match ← peek with
    | some .semi => advance
    | some .comma => advance; parseDeclNamesF f ty ws
    | some (.ident _) => parseDeclNamesF f ty ws
    | some t => fail s!"expected ',' or ';' in a declaration, found {repr t}"
    | none => fail "unterminated declaration"

/-- Parse a declaration `reg|stack|inline [ptr] type names;` (the storage
    keyword is the next token). -/
def parseDecl : P Unit := do
  advance
  skipQualifiers
  let (ty, ws) ← parseType
  parseDeclNamesF (← get).fuel ty ws

/-! ## Expressions -/

/-- What `parseExprF` parses: an expression at precedence level `n`, the
    continuation of a level-`n` expression after its left operand `lhs`, or an
    atom. -/
inductive EGoal where
  | lvl (n : Nat)
  | rest (n : Nat) (lhs : PExpr)
  | atom

/-- The binary operator a token denotes at precedence level `n` (0 binds
    loosest), as a function of the operator width. -/
def opOf : Nat → Token → Option (WSize → SOp2)
  | 0, .orOr => some fun _ => .Oor
  | 1, .andAnd => some fun _ => .Oand
  | 2, .bin .lor => some .Olor
  | 3, .bin .lxor => some .Olxor
  | 4, .bin .land => some .Oland
  | 5, .cmp .eq => some .Oeq
  | 5, .cmp .ne => some .Oneq
  | 6, .cmp .lt => some (.Olt .Uextend)
  | 6, .cmp .le => some (.Ole .Uextend)
  | 6, .cmp .gt => some (.Ogt .Uextend)
  | 6, .cmp .ge => some (.Oge .Uextend)
  | 6, .cmp .lts => some (.Olt .Sextend)
  | 6, .cmp .les => some (.Ole .Sextend)
  | 6, .cmp .gts => some (.Ogt .Sextend)
  | 6, .cmp .ges => some (.Oge .Sextend)
  | 7, .bin .shl => some .Olsl
  | 7, .bin .shr => some .Olsr
  | 7, .bin .sar => some .Oasr
  | 8, .bin .add => some .Oadd
  | 8, .bin .sub => some .Osub
  | 9, .bin .mul => some .Omul
  | _, _ => none

/-- The number of binary precedence levels. -/
def nLevels : Nat := 10

/-- The word width of an expression, when it is evident from the expression. -/
def exprWidth : PExpr → Option WSize
  | .Pvar gv => match gv.gv.var.vtype with
    | .sword w => some w
    | _ => none
  | .Pload w _ _ => some w
  | .Pget _ w _ _ => some w
  | .Papp1 (.Ozeroext w _) _ => some w
  | .Papp1 (.Olnot w) _ => some w
  | _ => none

/-- Parse an expression; `ctx` is the width of the assignment target, used for
    operators whose left operand has no evident width. -/
def parseExprF : Nat → WSize → EGoal → P PExpr
  | 0, _, _ => fail "fuel exhausted in an expression"
  | f + 1, ctx, .lvl n =>
    if n ≥ nLevels then parseExprF f ctx .atom
    else do
      let l ← parseExprF f ctx (.lvl (n + 1))
      parseExprF f ctx (.rest n l)
  | f + 1, ctx, .rest n l => do
    match ← peek with
    | some t =>
      match opOf n t with
      | some mk =>
        advance
        let r ← parseExprF f ctx (.lvl (n + 1))
        parseExprF f ctx (.rest n (.Papp2 (mk ((exprWidth l).getD ctx)) l r))
      | none => return l
    | none => return l
  | f + 1, ctx, .atom => do
    match ← peek with
    | some (.num k) => advance; return .Pconst k
    | some (.bin .sub) =>
      advance
      match ← peek with
      | some (.num k) => advance; return .Pconst (-(k : Int))
      | _ =>
        let e ← parseExprF f ctx .atom
        return .Papp2 (.Osub ((exprWidth e).getD ctx)) (.Pconst 0) e
    | some .bang =>
      advance
      let e ← parseExprF f ctx .atom
      return .Papp1 (.Olnot ((exprWidth e).getD ctx)) e
    | some .lparen =>
      advance
      match (← get).toks with
      | .num k :: .ident "u" :: .rparen :: _ =>
        advance; advance; advance
        match wsizeOfBits k with
        | none => fail s!"cast to an unsupported width {k}"
        | some wso =>
          let e ← parseExprF f ctx .atom
          return .Papp1 (.Ozeroext wso ((exprWidth e).getD ctx)) e
      | _ =>
        let e ← parseExprF f ctx (.lvl 0)
        expect .rparen
        return e
    | some .lbrack =>
      advance
      let ws ← (do
        if (← peek) = some .colon then
          advance
          let s ← expectIdent
          match wsizeOfName s with
          | some ws => return ws
          | none => fail s!"unsupported memory width '{s}'"
        else return WSize.U64)
      let d ← lookupVar (← expectIdent)
      let off ← (do
        match ← peek with
        | some (.bin .add) => advance; parseExprF f .U64 (.lvl 0)
        | _ => return PExpr.Pconst 0)
      expect .rbrack
      return .Pload ws d.varI off
    | some (.ident "true") => advance; return .Pbool true
    | some (.ident "false") => advance; return .Pbool false
    | some (.ident x) =>
      advance
      match ← peek with
      | some .lbrack =>
        advance
        let d ← lookupVar x
        let idx ← parseExprF f .U64 (.lvl 0)
        expect .rbrack
        return .Pget .AAscale d.ews { gv := d.varI, gs := false } idx
      | some .lparen => fail s!"call of '{x}' inside an expression is not in the subset"
      | _ => return (← lookupVar x).pvar
    | some .hash => fail "intrinsic inside an expression is not in the subset"
    | some t => fail s!"expected an expression, found {repr t}"
    | none => fail "expected an expression, found end of input"

/-- Parse an expression with target width `ctx`. -/
def parseExpr (ctx : WSize) : P PExpr := do
  parseExprF (← get).fuel ctx (.lvl 0)

/-- Parse the arguments of a call after its `(`, through the closing `)`. -/
def parseArgsF : Nat → P (List PExpr)
  | 0 => fail "fuel exhausted in an argument list"
  | f + 1 => do
    if (← peek) = some .rparen then advance; return []
    let e ← parseExpr .U64
    match ← peek with
    | some .comma => advance; return e :: (← parseArgsF f)
    | some .rparen => advance; return [e]
    | some t => fail s!"expected ',' or ')' in an argument list, found {repr t}"
    | none => fail "unterminated argument list"

/-- Parse an argument list starting at its `(`. -/
def parseArgs : P (List PExpr) := do
  expect .lparen
  parseArgsF (← get).fuel

/-! ## L-values and statements -/

/-- Parse one l-value. -/
def parseLval : P LVal := do
  match ← peek with
  | some (.ident "_") => advance; return .Lnone {} (.sword .U64)
  | some (.ident x) =>
    advance
    let d ← lookupVar x
    if (← peek) = some .lbrack then
      advance
      let idx ← parseExpr .U64
      expect .rbrack
      return .Laset .AAscale d.ews d.varI idx
    else return .Lvar d.varI
  | some .lbrack =>
    match ← parseExpr .U64 with
    | .Pload ws x off => return .Lmem ws x off
    | _ => fail "malformed memory l-value"
  | some t => fail s!"expected an l-value, found {repr t}"
  | none => fail "expected an l-value, found end of input"

/-- Parse a comma-separated list of l-values. -/
def parseLvalsF : Nat → P (List LVal)
  | 0 => fail "fuel exhausted in an l-value list"
  | f + 1 => do
    let lv ← parseLval
    if (← peek) = some .comma then
      advance
      return lv :: (← parseLvalsF f)
    else return [lv]

/-- The type an assignment to an l-value carries. -/
def lvalTy : LVal → SType
  | .Lnone _ t => t
  | .Lvar x => x.var.vtype
  | .Lmem ws _ _ => .sword ws
  | .Laset _ ws _ _ => .sword ws
  | .Lasub _ ws _ _ _ => .sword ws

/-- The word width of an l-value (`U64` when it is not a word). -/
def lvalWs (lv : LVal) : WSize :=
  match lvalTy lv with
  | .sword w => w
  | _ => .U64

/-- The operator of a compound-assignment token at width `w`. -/
def binTokOp (o : BinTok) (w : WSize) : SOp2 :=
  match o with
  | .add => .Oadd w | .sub => .Osub w | .mul => .Omul w
  | .land => .Oland w | .lor => .Olor w | .lxor => .Olxor w
  | .shl => .Olsl w | .shr => .Olsr w | .sar => .Oasr w

/-- Parse a sequence of statements, stopping before `}`, `return` or the end of
    the input. -/
def parseStmtsF : Nat → P (List InstrR)
  | 0 => fail "fuel exhausted in a statement sequence"
  | f + 1 => do
    match ← peek with
    | none | some .rbrace | some (.ident "return") => return []
    | some (.ident "reg") | some (.ident "stack") | some (.ident "inline") =>
      parseDecl
      parseStmtsF f
    | some (.ident "if") =>
      advance
      let c ← parseExpr .U64
      expect .lbrace
      let th ← parseStmtsF f
      expect .rbrace
      let el ← (do
        if (← peek) = some (.ident "else") then
          advance
          if (← peek) = some .lbrace then
            advance
            let el ← parseStmtsF f
            expect .rbrace
            return el
          else fail "'else' without a block (else if) is not in the subset"
        else return [])
      return .Cif c th el :: (← parseStmtsF f)
    | some (.ident "for") =>
      advance
      let x ← expectIdent
      let v : VarI := match (← get).env.find? (·.name == x) with
        | some d => d.varI
        | none => { var := { vname := x, vtype := .sint } }
      expect .assign
      let lo ← expectNum
      let dir ← expectIdent
      if dir ≠ "to" then fail s!"loop direction '{dir}' is not in the subset"
      let hi ← expectNum
      expect .lbrace
      let body ← parseStmtsF f
      expect .rbrace
      return .Cfor v { dir := .UpTo, lo := lo, hi := hi } body :: (← parseStmtsF f)
    | some (.ident "while") =>
      advance
      let pre ← (do
        if (← peek) = some .lbrace then
          advance
          let b ← parseStmtsF f
          expect .rbrace
          return b
        else return [])
      let c ← parseExpr .U64
      let post ← (do
        if (← peek) = some .lbrace then
          advance
          let b ← parseStmtsF f
          expect .rbrace
          return b
        else return [])
      return .Cwhile pre c post :: (← parseStmtsF f)
    | some .hash =>
      advance
      let op ← expectIdent
      let args ← parseArgs
      expect .semi
      return .Copn [] .AT_none (.Oasm ⟨op⟩) args :: (← parseStmtsF f)
    | some (.ident g) =>
      if (← peek2) = some .lparen then
        advance
        let args ← parseArgs
        expect .semi
        return .Ccall .DoNotInline [] { name := g } args :: (← parseStmtsF f)
      else
        let i ← parseAssign f
        return i :: (← parseStmtsF f)
    | some .lbrack =>
      let i ← parseAssign f
      return i :: (← parseStmtsF f)
    | some t => fail s!"unsupported statement starting with {repr t}"
where
  /-- Parse an assignment statement through its `;`. -/
  parseAssign (f : Nat) : P InstrR := do
    let lvs ← parseLvalsF f
    match ← peek with
    | some (.binEq o) =>
      advance
      match lvs with
      | [.Lvar x] =>
        let w := lvalWs (.Lvar x)
        let rhs ← parseExpr w
        expect .semi
        return .Cassgn (.Lvar x) .AT_none x.var.vtype
          (.Papp2 (binTokOp o w) (.Pvar { gv := x, gs := false }) rhs)
      | _ => fail "a compound assignment needs a single variable target"
    | some .assign =>
      advance
      match ← peek with
      | some .hash =>
        advance
        let op ← expectIdent
        let args ← parseArgs
        expect .semi
        return .Copn lvs .AT_none (.Oasm ⟨op⟩) args
      | some (.ident g) =>
        if (← peek2) = some .lparen then
          advance
          let args ← parseArgs
          expect .semi
          return .Ccall .DoNotInline lvs { name := g } args
        else parseSimple lvs
      | _ => parseSimple lvs
    | some t => fail s!"expected an assignment operator, found {repr t}"
    | none => fail "expected an assignment operator, found end of input"
  /-- Parse the right-hand side of `lv = e;`. -/
  parseSimple (lvs : List LVal) : P InstrR := do
    match lvs with
    | [lv] =>
      let rhs ← parseExpr (lvalWs lv)
      expect .semi
      return .Cassgn lv .AT_none (lvalTy lv) rhs
    | _ => fail "an expression assignment needs a single target"

/-! ## Functions -/

/-- Parse the parameters of a function after its `(`, through the `)`,
    declaring each. -/
def parseParamsF : Nat → P (List FunParam)
  | 0 => fail "fuel exhausted in a parameter list"
  | f + 1 => do
    if (← peek) = some .rparen then advance; return []
    match ← peek with
    | some (.ident "reg") | some (.ident "stack") => advance
    | some t => fail s!"expected 'reg' or 'stack' in a parameter, found {repr t}"
    | none => fail "unterminated parameter list"
    skipQualifiers
    let (ty, ws) ← parseType
    let x ← expectIdent
    let d : VDecl := { name := x, ty := ty, ews := ws }
    declare d
    match ← peek with
    | some .comma => advance; return ⟨d.varI⟩ :: (← parseParamsF f)
    | some .rparen => advance; return [⟨d.varI⟩]
    | some t => fail s!"expected ',' or ')' in a parameter list, found {repr t}"
    | none => fail "unterminated parameter list"

/-- Skip tokens up to (not including) the next `{`. -/
def skipToBraceF : Nat → P Unit
  | 0 => fail "fuel exhausted in a return-type list"
  | f + 1 => do
    match ← peek with
    | some .lbrace => pure ()
    | some _ => advance; skipToBraceF f
    | none => fail "missing function body"

/-- Skip an annotation body up to and including its `]`. -/
def skipAnnotF : Nat → P Unit
  | 0 => fail "fuel exhausted in an annotation"
  | f + 1 => do
    match ← peek with
    | some .rbrack => advance
    | some _ => advance; skipAnnotF f
    | none => fail "unterminated annotation"

/-- Parse the names of a `return` statement through its `;`. -/
def parseReturnF : Nat → P (List VarI)
  | 0 => fail "fuel exhausted in a return statement"
  | f + 1 => do
    let d ← lookupVar (← expectIdent)
    match ← peek with
    | some .comma => advance; return d.varI :: (← parseReturnF f)
    | some .semi => advance; return [d.varI]
    | some t => fail s!"expected ',' or ';' in a return statement, found {repr t}"
    | none => fail "unterminated return statement"

/-- Parse the function declarations up to the end of the input. -/
def parseFunsF : Nat → P (List FunDecl)
  | 0 => fail "fuel exhausted at top level"
  | f + 1 => do
    match ← peek with
    | none => return []
    | some .hash =>
      advance
      expect .lbrack
      skipAnnotF f
      parseFunsF f
    | some (.ident "export") | some (.ident "inline") =>
      advance
      parseFunsF f
    | some (.ident "fn") =>
      advance
      let name ← expectIdent
      modify fun st => { st with env := [] }
      expect .lparen
      let params ← parseParamsF f
      if (← peek) = some .arrow then skipToBraceF f
      expect .lbrace
      let body ← parseStmtsF f
      let results ← (do
        if (← peek) = some (.ident "return") then
          advance
          parseReturnF f
        else return [])
      expect .rbrace
      let fd : FunDecl := { name := { name := name }, params := params, body := body,
                            results := results }
      return fd :: (← parseFunsF f)
    | some t => fail s!"unsupported top-level construct starting with {repr t}"

/-! ## Entry points -/

/-- Parse a `.jazz` text into its function declarations. -/
def parseJazz (s : String) : Except String (List FunDecl) := do
  let toks ← tokenize s
  let fuel := 16 * (toks.length + 1)
  let (fds, _) ← (parseFunsF fuel).run { toks := toks, fuel := fuel }
  return fds

/-- Parse a `.jazz` text into a `JasminProg`. -/
def parseJazzProg (s : String) : Except String JasminProg :=
  (parseJazz s).map fun fs => { funcs := fs }

/-- Parse a statement sequence under the declarations `env` (name, type and
    word width); the whole text must be consumed. -/
def parseJazzBody (env : List VDecl) (s : String) : Except String (List InstrR) := do
  let toks ← tokenize s
  let fuel := 16 * (toks.length + 1)
  let (body, st) ← (parseStmtsF fuel).run { toks := toks, env := env, fuel := fuel }
  match st.toks with
  | [] => return body
  | t :: _ => throw s!"JazzToInstrR: unexpected {repr t} after the statements"

/-! ## Structural equality

`JasminAST` derives no equality for its nested inductives; these Boolean
equalities compare two terms constructor by constructor, so a parse result can
be compared with an expected AST by evaluation or by `decide`. -/

/-- Equality of variables with source info. -/
def varIBEq (x y : VarI) : Bool := decide (x.var = y.var) && decide (x.info = y.info)

/-- Equality of global-variable references. -/
def gvarBEq (x y : GVar) : Bool := varIBEq x.gv y.gv && x.gs == y.gs

mutual
/-- Structural equality of expressions. -/
def pexprBEq : PExpr → PExpr → Bool
  | .Pconst a, .Pconst b => a == b
  | .Pbool a, .Pbool b => a == b
  | .Parr_init a, .Parr_init b => a == b
  | .Pvar a, .Pvar b => gvarBEq a b
  | .Pget aa ws x i, .Pget aa' ws' x' i' =>
    decide (aa = aa') && decide (ws = ws') && gvarBEq x x' && pexprBEq i i'
  | .Psub aa ws n x i, .Psub aa' ws' n' x' i' =>
    decide (aa = aa') && decide (ws = ws') && n == n' && gvarBEq x x' && pexprBEq i i'
  | .Pload ws x o, .Pload ws' x' o' => decide (ws = ws') && varIBEq x x' && pexprBEq o o'
  | .Papp1 o e, .Papp1 o' e' => decide (o = o') && pexprBEq e e'
  | .Papp2 o a b, .Papp2 o' a' b' => decide (o = o') && pexprBEq a a' && pexprBEq b b'
  | .PappN o es, .PappN o' es' => decide (o = o') && pexprsBEq es es'
  | .Pif t c a b, .Pif t' c' a' b' =>
    decide (t = t') && pexprBEq c c' && pexprBEq a a' && pexprBEq b b'
  | _, _ => false
/-- Structural equality of expression lists. -/
def pexprsBEq : List PExpr → List PExpr → Bool
  | [], [] => true
  | a :: as, b :: bs => pexprBEq a b && pexprsBEq as bs
  | _, _ => false
end

/-- Structural equality of l-values. -/
def lvalBEq : LVal → LVal → Bool
  | .Lnone i t, .Lnone i' t' => decide (i = i') && decide (t = t')
  | .Lvar x, .Lvar x' => varIBEq x x'
  | .Lmem ws x o, .Lmem ws' x' o' => decide (ws = ws') && varIBEq x x' && pexprBEq o o'
  | .Laset aa ws x i, .Laset aa' ws' x' i' =>
    decide (aa = aa') && decide (ws = ws') && varIBEq x x' && pexprBEq i i'
  | .Lasub aa ws n x i, .Lasub aa' ws' n' x' i' =>
    decide (aa = aa') && decide (ws = ws') && n == n' && varIBEq x x' && pexprBEq i i'
  | _, _ => false

/-- Structural equality of l-value lists. -/
def lvalsBEq : List LVal → List LVal → Bool
  | [], [] => true
  | a :: as, b :: bs => lvalBEq a b && lvalsBEq as bs
  | _, _ => false

mutual
/-- Structural equality of instructions. -/
def instrBEq : InstrR → InstrR → Bool
  | .Cassgn lv t ty e, .Cassgn lv' t' ty' e' =>
    lvalBEq lv lv' && decide (t = t') && decide (ty = ty') && pexprBEq e e'
  | .Copn lvs t o es, .Copn lvs' t' o' es' =>
    lvalsBEq lvs lvs' && decide (t = t') && decide (o = o') && pexprsBEq es es'
  | .Cif c th el, .Cif c' th' el' => pexprBEq c c' && instrsBEq th th' && instrsBEq el el'
  | .Cfor v r b, .Cfor v' r' b' =>
    varIBEq v v' && decide (r.dir = r'.dir) && r.lo == r'.lo && r.hi == r'.hi &&
      instrsBEq b b'
  | .Cwhile pre c post, .Cwhile pre' c' post' =>
    instrsBEq pre pre' && pexprBEq c c' && instrsBEq post post'
  | .Ccall ii lvs fn args, .Ccall ii' lvs' fn' args' =>
    decide (ii = ii') && lvalsBEq lvs lvs' && decide (fn = fn') && pexprsBEq args args'
  | _, _ => false
/-- Structural equality of instruction lists. -/
def instrsBEq : List InstrR → List InstrR → Bool
  | [], [] => true
  | a :: as, b :: bs => instrBEq a b && instrsBEq as bs
  | _, _ => false
end

/-- Structural equality of function declarations. -/
def funDeclBEq (f g : FunDecl) : Bool :=
  decide (f.name = g.name) &&
  (f.params.map (·.var)).length == (g.params.map (·.var)).length &&
  ((f.params.map (·.var)).zip (g.params.map (·.var))).all (fun p => varIBEq p.1 p.2) &&
  instrsBEq f.body g.body &&
  f.results.length == g.results.length &&
  (f.results.zip g.results).all (fun p => varIBEq p.1 p.2)

/-- Whether `s` parses to exactly the declarations `fds`. -/
def parsesTo (s : String) (fds : List FunDecl) : Bool :=
  match parseJazz s with
  | .ok fs => fs.length == fds.length && (fs.zip fds).all (fun p => funDeclBEq p.1 p.2)
  | .error _ => false

/-! ## Round trip on the `bignum_add_4` port

`bignumAdd4Jazz` is the text `Emit.emitFunDecl` prints for
`S2NBignumSSA.BignumAdd4.fd`. `bignumAdd4Fd` is that port's `FunDecl` with the
carry variable `cf` typed `sbool`: the printer declares it `reg bool`, which is
the type the parser reads, whereas the port types it `sword U64`. -/

namespace RoundTrip

/-- A `u64` variable. -/
def u (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `bool` variable. -/
def b (s : String) : Var := { vname := s, vtype := .sbool }

/-- The l-value of a variable. -/
def lv (x : Var) : LVal := .Lvar { var := x }

/-- The expression of a local variable. -/
def pv (x : Var) : PExpr := .Pvar { gv := { var := x }, gs := false }

/-- A discarded flag output. -/
def nn : LVal := .Lnone {} (.sword .U64)

/-- `x = [:u64 base + k];` -/
def load (x base : String) (k : Int) : InstrR :=
  .Cassgn (lv (u x)) .AT_none (.sword .U64) (.Pload .U64 { var := u base } (.Pconst k))

/-- `[:u64 base + k] = src;` -/
def store (base : String) (k : Int) (src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := u base } (.Pconst k)) .AT_none (.sword .U64) (pv (u src))

/-- `_, cf, _, _, _, r = #op(args);` -/
def carry (op r : String) (args : List PExpr) : InstrR :=
  .Copn [nn, lv (b "cf"), nn, nn, nn, lv (u r)] .AT_none (.Oasm ⟨op⟩) args

/-- The text `Emit.emitFunDecl` prints for the `bignum_add_4` port. -/
def bignumAdd4Jazz : String :=
  "// Auto-generated from CatCrypt Jasmin AST. Do not edit by hand.
export fn bignum_add_4(reg u64 op, reg u64 ap, reg u64 bp)
{
  reg bool of cf sf pf zf;
  reg u64 a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3;

  a0 = [:u64 ap + 0];
  a1 = [:u64 ap + 8];
  a2 = [:u64 ap + 16];
  a3 = [:u64 ap + 24];
  b0 = [:u64 bp + 0];
  b1 = [:u64 bp + 8];
  b2 = [:u64 bp + 16];
  b3 = [:u64 bp + 24];
  _, cf, _, _, _, r0 = #ADD_64(a0, b0);
  _, cf, _, _, _, r1 = #ADC_64(a1, b1, cf);
  _, cf, _, _, _, r2 = #ADC_64(a2, b2, cf);
  _, cf, _, _, _, r3 = #ADC_64(a3, b3, cf);
  [:u64 op + 0] = r0;
  [:u64 op + 8] = r1;
  [:u64 op + 16] = r2;
  [:u64 op + 24] = r3;
}
"

/-- The `bignum_add_4` port with `cf : bool`. -/
def bignumAdd4Fd : FunDecl where
  name := { name := "bignum_add_4" }
  params := [⟨{ var := u "op" }⟩, ⟨{ var := u "ap" }⟩, ⟨{ var := u "bp" }⟩]
  body :=
    [ load "a0" "ap" 0, load "a1" "ap" 8, load "a2" "ap" 16, load "a3" "ap" 24
    , load "b0" "bp" 0, load "b1" "bp" 8, load "b2" "bp" 16, load "b3" "bp" 24
    , carry "ADD_64" "r0" [pv (u "a0"), pv (u "b0")]
    , carry "ADC_64" "r1" [pv (u "a1"), pv (u "b1"), pv (b "cf")]
    , carry "ADC_64" "r2" [pv (u "a2"), pv (u "b2"), pv (b "cf")]
    , carry "ADC_64" "r3" [pv (u "a3"), pv (u "b3"), pv (b "cf")]
    , store "op" 0 "r0", store "op" 8 "r1", store "op" 16 "r2", store "op" 24 "r3" ]
  results := []

-- The printed `bignum_add_4` text parses to the port's `FunDecl`.
#kat parsesTo bignumAdd4Jazz [bignumAdd4Fd]

/-- An array variable of `k` bytes. -/
def arr (s : String) (k : Nat) : Var := { vname := s, vtype := .sarr k }

/-- `x = e;` at type `u64`. -/
def asg (x : String) (e : PExpr) : InstrR := .Cassgn (lv (u x)) .AT_none (.sword .U64) e

/-- The declarations in scope for `controlBody`. -/
def controlEnv : List VDecl :=
  [ { name := "x", ty := .sword .U64, ews := .U64 }
  , { name := "y", ty := .sword .U64, ews := .U64 }
  , { name := "n", ty := .sword .U64, ews := .U64 }
  , { name := "t", ty := .sarr 32, ews := .U64 }
  , { name := "i", ty := .sint, ews := .U64 } ]

/-- A statement sequence with compound assignments, nested arithmetic, array
    accesses and the three control constructs. -/
def controlBody : String :=
  "x = y;
  x ^= 0xff;
  x = (x + y) & 3;
  n = -y;
  t[1] = x;
  while (n != 0) { n -= 1; }
  if (x < y) { x = t[1]; } else { x = !x; }
  for i = 0 to 4 { x <<= 1; }"

/-- The AST of `controlBody`. -/
def controlAst : List InstrR :=
  [ asg "x" (pv (u "y"))
  , asg "x" (.Papp2 (.Olxor .U64) (pv (u "x")) (.Pconst 255))
  , asg "x" (.Papp2 (.Oland .U64) (.Papp2 (.Oadd .U64) (pv (u "x")) (pv (u "y"))) (.Pconst 3))
  , asg "n" (.Papp2 (.Osub .U64) (.Pconst 0) (pv (u "y")))
  , .Cassgn (.Laset .AAscale .U64 { var := arr "t" 32 } (.Pconst 1)) .AT_none (.sword .U64)
      (pv (u "x"))
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv (u "n")) (.Pconst 0))
      [asg "n" (.Papp2 (.Osub .U64) (pv (u "n")) (.Pconst 1))]
  , .Cif (.Papp2 (.Olt .Uextend .U64) (pv (u "x")) (pv (u "y")))
      [asg "x" (.Pget .AAscale .U64 { gv := { var := arr "t" 32 }, gs := false } (.Pconst 1))]
      [asg "x" (.Papp1 (.Olnot .U64) (pv (u "x")))]
  , .Cfor { var := { vname := "i", vtype := .sint } } { dir := .UpTo, lo := 0, hi := 4 }
      [asg "x" (.Papp2 (.Olsl .U64) (pv (u "x")) (.Pconst 1))] ]

-- `controlBody` parses to `controlAst`.
#kat match parseJazzBody controlEnv controlBody with
  | .ok is => instrsBEq is controlAst
  | .error _ => false

end RoundTrip

end CatCrypt.Crypto.Jasmin.JazzToInstrR
