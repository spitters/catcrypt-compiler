/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JincToCom

/-!
# Jasmin source partial evaluator: `.jinc` text to a straight-line `JFun`

Parses a Jasmin source unit (the required `.jinc` texts, concatenated) into a
surface AST (`Prog`) and partially evaluates one function of it into the
straight-line fragment of `JincToCom` (`JFun`), which `JincElab.elabFun`
elaborates to a `Com jasminDialect`.

## Surface fragment

`param int` constants; global `uW[n]` tables and `uW` constants; `inline fn`, `fn`
and `export fn` definitions with `inline int`, `reg`, `reg ptr` and `stack`
parameters and locals; expressions with C precedence over
`+ - * / % & | ^ << >> == != < <= > >= && ||`, unary `!` and `-`, casts `(64u) e`
and `(u64) e`, `c ? a : b`, array indexing, calls to source functions and to the
intrinsics `#ROL_64`, `#ROR_64`, `#swap`, `#spill` and `#unspill`; tuple
assignments with `_` and `()`, compound assignments, `if`/`else`, `for v = lo to hi`,
`while { pre } (c) { post }`, and a final `return`. `#[…]` annotations and
`require` lines are skipped; the caller supplies the required units in the text.

## Evaluation

* An `inline int`, a `param int`, a comparison, and a `reg` word whose value is
  known at compile time are folded (constant propagation). The conditions of `if`
  and `?:`, loop bounds and `while` guards must fold; a data-dependent branch is
  rejected, and so a `while` whose guard folds is unrolled.
* `importFunRolled` keeps a loop rolled instead when its unrolling is `rollable`
  (at least two trips, and `rollMinTrips` trips or `rollMinStmts` statements per
  trip): a `for`, or a `while { pre } (c) {}` whose trips advance one
  compile-time counter by a fixed step (`affineCounter`). The loop is emitted as
  `for idx = 0 to n { body }` over a run-time trip index `idx`, with the counter
  at `c0 + step · idx`. `tryRoll` evaluates the body with the names a trip writes
  unassigned, so a body that reads a value an earlier trip left, or stores into
  other than exactly one array, is unrolled; so is a loop inside a rolled body.
* A read of a memory array or of a global table at a run-time index is a `load`
  (a global table only under `importFunRolled`, from the base `b = @SYM` of its
  `.rodata` copy); a store into a memory array at a run-time index is a
  `storeAt`.
* Every call to a source function is inlined, `fn` as well as `inline fn`.
* A `reg` or `stack` array is one value per cell (scalar replacement), and every
  index into it must fold. A `reg ptr` array parameter of the evaluated function
  is a memory array: a read is a `load` and a write a `store`, in source order,
  so a call whose array arguments alias computes what the source computes.
* A register copy emits no statement: the destination names the source's value.
* `!a & b` with `a` a run-time word is `BinKind.andn`; `#ROL_64(x, i)` and
  `#ROR_64(x, i)` are `Rhs.ror`.
* Every word is 64 bits wide; a `reg` or array type of another width is rejected.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JincInline

open CatCrypt.Crypto.Jasmin.JincToCom (Stmt Rhs Operand BinKind JTy Param JFun)

/-! ## 1. Tokens -/

/-- A token: an identifier (intrinsics keep their leading `#`), a numeral, a
    string literal, or a punctuation symbol. -/
inductive Tok where
  | id (s : String)
  | num (n : Nat)
  | str (s : String)
  | sym (s : String)
  deriving Repr, BEq, Inhabited

/-- Characters as the tokenizer consumes them. -/
abbrev Cs := List Char

/-- The text after a `#[ … ]` annotation, given the text after its `#[` and the
    number of `[` opened inside it. -/
def dropAnnot (d : Nat) : Cs → Cs
  | [] => []
  | ']' :: r => if d = 0 then r else dropAnnot (d - 1) r
  | '[' :: r => dropAnnot (d + 1) r
  | _ :: r => dropAnnot d r

/-- The three-character symbols. -/
def syms3 : List String := ["<<=", ">>="]

/-- The two-character symbols. -/
def syms2 : List String :=
  ["<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=", "*=", "&=", "|=", "^=", "->"]

/-- The one-character symbols. -/
def syms1 : List Char := "(){}[];,=+-*/%&|^!<>?:".toList

/-- A character that continues an identifier. -/
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The tokens of `cs`, appended to `acc`. -/
partial def tokenizeGo (cs : Cs) (acc : Array Tok) : Except String (Array Tok) :=
  match JincToCom.skipWhite cs with
  | [] => .ok acc
  | '#' :: '[' :: r => tokenizeGo (dropAnnot 0 r) acc
  | '"' :: r =>
      tokenizeGo ((r.dropWhile (· ≠ '"')).drop 1)
        (acc.push (.str (String.ofList (r.takeWhile (· ≠ '"')))))
  | cs0@(c :: r) =>
      if c.isAlpha || c == '_' || c == '#' then
        tokenizeGo (r.dropWhile isIdChar)
          (acc.push (.id (String.ofList (c :: r.takeWhile isIdChar))))
      else if c.isDigit then
        match cs0 with
        | '0' :: x :: r' =>
            if x == 'x' || x == 'X' then
              let h := r'.takeWhile JincToCom.isHexDigit
              tokenizeGo (r'.dropWhile JincToCom.isHexDigit)
                (acc.push (.num (h.foldl (fun a d => a * 16 + JincToCom.hexVal d) 0)))
            else
              tokenizeGo (cs0.dropWhile Char.isDigit)
                (acc.push (.num (String.ofList (cs0.takeWhile Char.isDigit)).toNat!))
        | _ =>
            tokenizeGo (cs0.dropWhile Char.isDigit)
              (acc.push (.num (String.ofList (cs0.takeWhile Char.isDigit)).toNat!))
      else
        let s3 := String.ofList (cs0.take 3)
        let s2 := String.ofList (cs0.take 2)
        if syms3.contains s3 then tokenizeGo (cs0.drop 3) (acc.push (.sym s3))
        else if syms2.contains s2 then tokenizeGo (cs0.drop 2) (acc.push (.sym s2))
        else if syms1.contains c then tokenizeGo r (acc.push (.sym (String.singleton c)))
        else .error s!"tokenize: unexpected character '{c}'"

/-- The tokens of a source text. -/
def tokenize (src : String) : Except String (Array Tok) := tokenizeGo src.toList #[]

/-! ## 2. Surface AST -/

/-- A surface expression. `bin` carries the source operator symbol. -/
inductive E where
  | num (n : Int)
  | var (s : String)
  | idx (a : String) (i : E)
  | call (f : String) (args : List E)
  | bin (op : String) (a b : E)
  | neg (a : E)
  | not (a : E)
  | cast (w : Nat) (a : E)
  | cond (c t f : E)
  deriving Repr, Inhabited

/-- An assignment destination: `_`, a variable, or an array cell. -/
inductive LV where
  | wild
  | var (s : String)
  | idx (a : String) (i : E)
  deriving Repr, Inhabited

/-- A declared type: `int` (also `bool`), a word `uW`, or an array `uW[n]`. -/
inductive Ty where
  | int
  | word (w : Nat)
  | arr (w : Nat) (n : E)
  deriving Repr, Inhabited

/-- A surface statement. `decl` records whether an array is a `ptr`; `opAssign`
    carries the binary operator of a compound assignment. -/
inductive S where
  | decl (ty : Ty) (ptr : Bool) (names : List String)
  | assign (lhs : List LV) (rhs : E)
  | opAssign (op : String) (lhs : LV) (rhs : E)
  | ite (c : E) (t f : List S)
  | forTo (v : String) (lo hi : E) (body : List S)
  | while (pre : List S) (c : E) (post : List S)
  deriving Repr, Inhabited

/-- A function: its parameters (type, `ptr` flag, name), body and returned
    expressions. -/
structure Fn where
  name : String
  params : List (Ty × Bool × String)
  body : List S
  ret : List E
  deriving Repr, Inhabited

/-- A source unit: `param int` constants, global tables and constants, and
    functions. A later definition of a name shadows an earlier one. -/
structure Prog where
  params : List (String × E) := []
  globs : List (String × List E) := []
  gconsts : List (String × E) := []
  fns : List Fn := []
  deriving Repr, Inhabited

/-! ## 3. Parser -/

/-- The parser monad over the remaining tokens. -/
abbrev P := StateT (List Tok) (Except String)

/-- The next token, not consumed. -/
def peek : P (Option Tok) := return (← get).head?

/-- Consume the next token. -/
def next : P Tok := do
  match ← get with
  | [] => throw "parse: unexpected end of input"
  | t :: r => set r; return t

/-- Whether the next token is the symbol `s`. -/
def isSym (s : String) : P Bool := return (← peek) == some (.sym s)

/-- Whether the next token is the identifier `s`. -/
def isId (s : String) : P Bool := return (← peek) == some (.id s)

/-- Consume the symbol `s`. -/
def expectSym (s : String) : P Unit := do
  let t ← next
  unless t == .sym s do throw s!"parse: expected '{s}', got {repr t}"

/-- Consume the identifier `s`. -/
def expectId (s : String) : P Unit := do
  let t ← next
  unless t == .id s do throw s!"parse: expected '{s}', got {repr t}"

/-- Consume an identifier. -/
def ident : P String := do
  match ← next with
  | .id s => return s
  | t => throw s!"parse: expected an identifier, got {repr t}"

/-- The width of a word type keyword. -/
def wordWidth? : String → Option Nat
  | "u8" => some 8 | "u16" => some 16 | "u32" => some 32 | "u64" => some 64
  | "u128" => some 128 | "u256" => some 256
  | "ui8" => some 8 | "ui16" => some 16 | "ui32" => some 32 | "ui64" => some 64
  | "si8" => some 8 | "si16" => some 16 | "si32" => some 32 | "si64" => some 64
  | _ => none

/-- The binding strength of a binary operator symbol, C order. -/
def binPrec : String → Option Nat
  | "||" => some 1 | "&&" => some 2 | "|" => some 3 | "^" => some 4 | "&" => some 5
  | "==" => some 6 | "!=" => some 6
  | "<" => some 7 | "<=" => some 7 | ">" => some 7 | ">=" => some 7
  | "<<" => some 8 | ">>" => some 8
  | "+" => some 9 | "-" => some 9
  | "*" => some 10 | "/" => some 10 | "%" => some 10
  | _ => none

/-- The binary operator of a compound-assignment symbol. -/
def opOfAssign : String → Option String
  | "+=" => some "+" | "-=" => some "-" | "*=" => some "*" | "&=" => some "&"
  | "|=" => some "|" | "^=" => some "^" | "<<=" => some "<<" | ">>=" => some ">>"
  | _ => none

mutual

/-- A primary expression: a numeral, a cast, a parenthesised expression, a call,
    an array cell or a variable. -/
partial def parsePrimary : P E := do
  match ← next with
  | .num n => return .num n
  | .sym "(" =>
      match ← get with
      | .num w :: .id "u" :: .sym ")" :: r => set r; return .cast w (← parseUnary)
      | .num w :: .id "s" :: .sym ")" :: r => set r; return .cast w (← parseUnary)
      | .id s :: .sym ")" :: r =>
          match wordWidth? s with
          | some w => set r; return .cast w (← parseUnary)
          | none => let e ← parseExpr; expectSym ")"; return e
      | _ => let e ← parseExpr; expectSym ")"; return e
  | .id s =>
      if (← isSym "(") then
        let _ ← next
        return .call s (← parseArgs)
      else if (← isSym "[") then
        let _ ← next
        let i ← parseExpr
        expectSym "]"
        return .idx s i
      else return .var s
  | t => throw s!"parse: expected an expression, got {repr t}"

/-- A unary expression. -/
partial def parseUnary : P E := do
  if (← isSym "!") then
    let _ ← next
    return .not (← parseUnary)
  else if (← isSym "-") then
    let _ ← next
    return .neg (← parseUnary)
  else parsePrimary

/-- The binary operators binding at least as tightly as `minPrec`, applied
    left-associatively to `lhs`. -/
partial def parseBinRhs (minPrec : Nat) (lhs : E) : P E := do
  match ← peek with
  | some (.sym op) =>
      match binPrec op with
      | some p =>
          if p < minPrec then return lhs
          else
            let _ ← next
            let rhs ← parseBinRhs (p + 1) (← parseUnary)
            parseBinRhs minPrec (.bin op lhs rhs)
      | none => return lhs
  | _ => return lhs

/-- An expression, with a trailing `? t : f`. -/
partial def parseExpr : P E := do
  let e ← parseBinRhs 1 (← parseUnary)
  if (← isSym "?") then
    let _ ← next
    let t ← parseExpr
    expectSym ":"
    let f ← parseExpr
    return .cond e t f
  else return e

/-- Call arguments up to and including the closing `)`. -/
partial def parseArgs : P (List E) := do
  if (← isSym ")") then
    let _ ← next
    return []
  else
    let e ← parseExpr
    if (← isSym ",") then
      let _ ← next
      return e :: (← parseArgs)
    else
      expectSym ")"
      return [e]

end

/-- A type: `int`, `bool`, `uW` or `uW[n]`. -/
def parseTy : P Ty := do
  let s ← ident
  if s == "int" || s == "bool" then return .int
  match wordWidth? s with
  | some w =>
      if (← isSym "[") then
        let _ ← next
        let n ← parseExpr
        expectSym "]"
        return .arr w n
      else return .word w
  | none => throw s!"parse: expected a type, got '{s}'"

/-- A storage class and type, with whether the storage is a `ptr`. -/
def parseStorTy : P (Ty × Bool) := do
  let s ← ident
  match s with
  | "inline" | "param" => return (← parseTy, false)
  | "reg" | "stack" =>
      if (← isId "mut") then let _ ← next
      if (← isId "const") then let _ ← next
      let ptr ← if (← isId "ptr") then do let _ ← next; pure true else pure false
      return (← parseTy, ptr)
  | _ => throw s!"parse: expected a storage class, got '{s}'"

/-- Identifiers up to the next non-identifier; with `commas`, also separated by
    commas (a declaration statement, where no storage class follows a comma). -/
partial def parseNames (commas : Bool) : P (List String) := do
  match ← peek with
  | some (.id s) =>
      let _ ← next
      if commas && (← isSym ",") then let _ ← next
      return s :: (← parseNames commas)
  | _ => return []

/-- An assignment destination. -/
def parseLV : P LV := do
  let s ← ident
  if s == "_" then return .wild
  if (← isSym "[") then
    let _ ← next
    let i ← parseExpr
    expectSym "]"
    return .idx s i
  return .var s

/-- Assignment destinations separated by commas. -/
partial def parseLVs : P (List LV) := do
  let l ← parseLV
  if (← isSym ",") then
    let _ ← next
    return l :: (← parseLVs)
  return [l]

/-- Expressions separated by commas. -/
partial def parseExprList : P (List E) := do
  let e ← parseExpr
  if (← isSym ",") then
    let _ ← next
    return e :: (← parseExprList)
  return [e]

mutual

/-- A statement (a declaration yields one `decl`). -/
partial def parseStmt : P (List S) := do
  match ← peek with
  | some (.id "reg") | some (.id "stack") | some (.id "inline") =>
      let (ty, ptr) ← parseStorTy
      let names ← parseNames true
      expectSym ";"
      return [.decl ty ptr names]
  | some (.id "if") =>
      let _ ← next
      let c ← parseExpr
      let t ← parseBlock
      if (← isId "else") then
        let _ ← next
        if (← isId "if") then return [.ite c t (← parseStmt)]
        return [.ite c t (← parseBlock)]
      return [.ite c t []]
  | some (.id "for") =>
      let _ ← next
      let v ← ident
      expectSym "="
      let lo ← parseExpr
      expectId "to"
      let hi ← parseExpr
      return [.forTo v lo hi (← parseBlock)]
  | some (.id "while") =>
      let _ ← next
      let pre ← if (← isSym "{") then parseBlock else pure []
      expectSym "("
      let c ← parseExpr
      expectSym ")"
      let post ← if (← isSym "{") then parseBlock else pure []
      return [.while pre c post]
  | some (.sym "(") =>
      let _ ← next
      expectSym ")"
      expectSym "="
      let e ← parseExpr
      expectSym ";"
      return [.assign [] e]
  | _ =>
      let lvs ← parseLVs
      match ← next with
      | .sym "=" =>
          let e ← parseExpr
          expectSym ";"
          return [.assign lvs e]
      | .sym s =>
          match opOfAssign s, lvs with
          | some op, [l] =>
              let e ← parseExpr
              expectSym ";"
              return [.opAssign op l e]
          | _, _ => throw s!"parse: unexpected '{s}' after an assignment destination"
      | t => throw s!"parse: unexpected {repr t} after an assignment destination"

/-- A braced block, `{` included. -/
partial def parseBlock : P (List S) := do
  expectSym "{"
  parseStmts

/-- Statements up to and including the closing `}`. -/
partial def parseStmts : P (List S) := do
  if (← isSym "}") then
    let _ ← next
    return []
  let s ← parseStmt
  return s ++ (← parseStmts)

end

/-- A function body after its `{`: statements, then an optional `return`, then `}`. -/
partial def parseFnBody : P (List S × List E) := do
  if (← isId "return") then
    let _ ← next
    let rs ← if (← isSym ";") then pure [] else parseExprList
    expectSym ";"
    expectSym "}"
    return ([], rs)
  if (← isSym "}") then
    let _ ← next
    return ([], [])
  let s ← parseStmt
  let (b, r) ← parseFnBody
  return (s ++ b, r)

/-- Parameters after the opening `(`, up to and including the closing `)`. -/
partial def parseParams : P (List (Ty × Bool × String)) := do
  if (← isSym ")") then
    let _ ← next
    return []
  let (ty, ptr) ← parseStorTy
  let names ← parseNames false
  if (← isSym ",") then let _ ← next
  return names.map (fun nm => (ty, ptr, nm)) ++ (← parseParams)

/-- Result types after `->`, separated by commas. -/
partial def parseRetTys : P Unit := do
  let _ ← parseStorTy
  if (← isSym ",") then
    let _ ← next
    parseRetTys

/-- A function definition. -/
def parseFn : P Fn := do
  if (← isId "inline") then let _ ← next
  if (← isId "export") then let _ ← next
  expectId "fn"
  let nm ← ident
  expectSym "("
  let ps ← parseParams
  if (← isSym "->") then
    let _ ← next
    parseRetTys
  expectSym "{"
  let (body, ret) ← parseFnBody
  return { name := nm, params := ps, body, ret }

/-- The top-level items, added to `p`. -/
partial def parseTop (p : Prog) : P Prog := do
  match ← peek with
  | none => return p
  | some (.id "from") =>
      let _ ← next
      let _ ← ident
      expectId "require"
      let _ ← next
      parseTop p
  | some (.id "require") =>
      let _ ← next
      let _ ← next
      parseTop p
  | some (.id "param") =>
      let _ ← next
      let _ ← parseTy
      let n ← ident
      expectSym "="
      let e ← parseExpr
      expectSym ";"
      parseTop { p with params := (n, e) :: p.params }
  | some (.id "inline") | some (.id "export") | some (.id "fn") =>
      let f ← parseFn
      parseTop { p with fns := f :: p.fns }
  | some (.id _) =>
      let ty ← parseTy
      let n ← ident
      expectSym "="
      match ty with
      | .arr _ _ =>
          expectSym "{"
          let es ← parseExprList
          expectSym "}"
          expectSym ";"
          parseTop { p with globs := (n, es) :: p.globs }
      | _ =>
          let e ← parseExpr
          expectSym ";"
          parseTop { p with gconsts := (n, e) :: p.gconsts }
  | some t => throw s!"parse: unexpected {repr t} at top level"

/-- Parse a source unit. -/
def parseProg (src : String) : Except String Prog := do
  let toks ← tokenize src
  let (p, _) ← (parseTop {}).run toks.toList
  return p

/-! ## 4. Values -/

/-- The word modulus. -/
def w64 : Nat := 2 ^ 64

/-- An integer as a 64-bit word. -/
def toW (n : Int) : Nat := (n % (w64 : Int)).toNat

/-- A value during evaluation: unassigned, a compile-time integer, a compile-time
    word, a run-time word held by an emitted name, a register array (one value per
    cell), a memory array named by an emitted array name, or the read-only global
    table `nm` with its words. -/
inductive V where
  | undef
  | int (n : Int)
  | cw (n : Nat)
  | w (nm : String)
  | ra (els : Array V)
  | mem (nm : String) (n : Nat)
  | gtab (nm : String) (els : Array Nat)
  deriving Repr, Inhabited, BEq

/-- The kind of a declared name. -/
inductive Kind where
  | int
  | word
  | arr
  deriving Repr, BEq, Inhabited

/-- A function frame: each declared name with its kind and value, newest first. -/
abbrev Env := List (String × Kind × V)

/-- A name's kind and value in a frame. -/
def Env.get? (env : Env) (x : String) : Option (Kind × V) :=
  (env.find? (·.1 == x)).map (·.2)

/-- A frame with the newest declaration of `x` holding `v`. -/
def Env.set : Env → String → V → Env
  | [], _, _ => []
  | (y, k, u) :: r, x, v => if y == x then (y, k, v) :: r else (y, k, u) :: Env.set r x v

/-- The evaluation state: the emitted statements, the emitted names that need a
    declaration, and the fresh-name counter; whether loops may be kept rolled,
    whether evaluation is inside a rolled loop body, the statements to place ahead
    of that loop, the base name bound for each global table read at a run-time
    index, the tables so read, and the array names with their cell counts. -/
structure EvSt where
  out : Array Stmt := #[]
  decls : Array String := #[]
  fresh : Nat := 0
  roll : Bool := false
  inBody : Bool := false
  hoist : Array Stmt := #[]
  gbases : List (String × String) := []
  tables : Array (String × List Nat) := #[]
  adecls : Array (String × Nat) := #[]
  deriving Inhabited

/-- The evaluation monad. -/
abbrev M := StateT EvSt (Except String)

/-- The shared index register of the emitted loads: bound immediately before
    each `load` that reads it. -/
def kiName : String := "%ki"

/-- A fresh emitted name. -/
def fresh : M String :=
  modifyGet fun s => ("%j" ++ toString s.fresh, { s with fresh := s.fresh + 1 })

/-- Append a statement. -/
def emit (st : Stmt) : M Unit := modify fun s => { s with out := s.out.push st }

/-- The right-hand side `src` rotated right by `n`. -/
def rorRhs (n : Nat) (src : String) : Rhs := .ror n src

/-- The right-hand side `(~a) & b`. -/
def andnRhs (a b : String) : Rhs := .bin .andn a (.var b)

/-- A name holding the word `v`, emitting a constant binding for a compile-time
    word. -/
def wordName : V → M String
  | .w nm => pure nm
  | .cw n => do
      let t ← fresh
      modify fun s => { s with decls := s.decls.push t }
      emit (.assign t (.imm n))
      pure t
  | .int n => do
      let t ← fresh
      modify fun s => { s with decls := s.decls.push t }
      emit (.assign t (.imm (toW n)))
      pure t
  | v => throw s!"eval: expected a 64-bit word, got {repr v}"

/-- The operand of a word value. -/
def operandOf : V → M Operand
  | .w nm => pure (.var nm)
  | .cw n => pure (.lit n)
  | .int n => pure (.lit (toW n))
  | v => throw s!"eval: expected a 64-bit word, got {repr v}"

/-- A value that folds to a natural number (an index, a count). -/
def constNat : V → M Nat
  | .int n => if n ≥ 0 then pure n.toNat else throw s!"eval: negative index {n}"
  | .cw n => pure n
  | v => throw s!"eval: expected a compile-time integer, got {repr v}"

/-- The truth of a folded condition. -/
def truth? : V → Option Bool
  | .int n => some (n != 0)
  | .cw n => some (n != 0)
  | _ => none

/-- A boolean as an integer. -/
def ofBool (b : Bool) : V := .int (if b then 1 else 0)

/-- A binary operator on compile-time integers. -/
def intBin (op : String) (a b : Int) : Option V :=
  match op with
  | "+" => some (.int (a + b))
  | "-" => some (.int (a - b))
  | "*" => some (.int (a * b))
  | "/" => if b == 0 then none else some (.int (a / b))
  | "%" => if b == 0 then none else some (.int (a % b))
  | "==" => some (ofBool (a == b))
  | "!=" => some (ofBool (a != b))
  | "<" => some (ofBool (a < b))
  | "<=" => some (ofBool (a ≤ b))
  | ">" => some (ofBool (a > b))
  | ">=" => some (ofBool (a ≥ b))
  | "&&" => some (ofBool (a != 0 && b != 0))
  | "||" => some (ofBool (a != 0 || b != 0))
  | "&" => if a ≥ 0 && b ≥ 0 then some (.int (a.toNat &&& b.toNat : Nat)) else none
  | "|" => if a ≥ 0 && b ≥ 0 then some (.int (a.toNat ||| b.toNat : Nat)) else none
  | "^" => if a ≥ 0 && b ≥ 0 then some (.int (a.toNat ^^^ b.toNat : Nat)) else none
  | "<<" => if b ≥ 0 then some (.int (a * 2 ^ b.toNat)) else none
  | ">>" => if b ≥ 0 then some (.int (a / 2 ^ b.toNat)) else none
  | _ => none

/-- A binary operator on compile-time 64-bit words. Comparisons are unsigned and
    shift counts are taken modulo 64. -/
def wordBin (op : String) (a b : Nat) : Option V :=
  match op with
  | "+" => some (.cw ((a + b) % w64))
  | "-" => some (.cw ((a + w64 - b % w64) % w64))
  | "*" => some (.cw ((a * b) % w64))
  | "&" => some (.cw (a &&& b))
  | "|" => some (.cw (a ||| b))
  | "^" => some (.cw (a ^^^ b))
  | "<<" => some (.cw ((a <<< (b % 64)) % w64))
  | ">>" => some (.cw (a >>> (b % 64)))
  | "==" => some (ofBool (a == b))
  | "!=" => some (ofBool (a != b))
  | "<" => some (ofBool (a < b))
  | "<=" => some (ofBool (a ≤ b))
  | ">" => some (ofBool (a > b))
  | ">=" => some (ofBool (a ≥ b))
  | _ => none

/-- The emitted operator of a source operator on run-time words. -/
def binKind? : String → Option BinKind
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "&" => some .and
  | "|" => some .or | "^" => some .xor | "<<" => some .shl | ">>" => some .shr
  | _ => none

/-- Whether an emitted operator is commutative. -/
def commutes : BinKind → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- A compile-time value as a word. -/
def constWord? : V → Option Nat
  | .int n => some (toW n)
  | .cw n => some n
  | _ => none

/-- A binary operator applied to two values: folded when both are compile-time,
    emitted otherwise. -/
def binV (op : String) (a b : V) : M V := do
  match a, b with
  | .int x, .int y =>
      match intBin op x y with
      | some v => pure v
      | none => throw s!"eval: cannot fold {x} {op} {y}"
  | .w x, _ =>
      let some k := binKind? op | throw s!"eval: '{op}' on a run-time word"
      let t ← fresh
      emit (.assign t (.bin k x (← operandOf b)))
      pure (.w t)
  | _, .w y =>
      let some k := binKind? op | throw s!"eval: '{op}' on a run-time word"
      let t ← fresh
      if commutes k then
        emit (.assign t (.bin k y (← operandOf a)))
      else
        let x ← wordName a
        emit (.assign t (.bin k x (.var y)))
      pure (.w t)
  | _, _ =>
      match constWord? a, constWord? b with
      | some x, some y =>
          match wordBin op x y with
          | some v => pure v
          | none => throw s!"eval: cannot fold {x} {op} {y}"
      | _, _ => throw s!"eval: '{op}' on {repr a} and {repr b}"

/-- `!v`: logical negation of a compile-time integer, bitwise complement of a
    word. -/
def notV : V → M V
  | .int n => pure (ofBool (n == 0))
  | .cw n => pure (.cw (w64 - 1 - n))
  | .w x => do
      let t ← fresh
      emit (.assign t (.bin .xor x (.lit (w64 - 1))))
      pure (.w t)
  | v => throw s!"eval: '!' on {repr v}"

/-- `-v`. -/
def negV : V → M V
  | .int n => pure (.int (-n))
  | .cw n => pure (.cw ((w64 - n) % w64))
  | .w x => do
      let z ← wordName (.cw 0)
      let t ← fresh
      emit (.assign t (.bin .sub z (.var x)))
      pure (.w t)
  | v => throw s!"eval: '-' on {repr v}"

/-- `(~a) & b` with `a` a run-time word. -/
def andnV (a : String) (b : V) : M V := do
  let bn ← wordName b
  let t ← fresh
  emit (.assign t (andnRhs a bn))
  pure (.w t)

/-- `x` rotated right by `r` (`0 ≤ r < 64`). -/
def rotV (x : V) (r : Nat) : M V := do
  if r == 0 then return x
  match x with
  | .w nm =>
      let t ← fresh
      emit (.assign t (rorRhs r nm))
      pure (.w t)
  | _ =>
      match constWord? x with
      | some n => pure (.cw (((n >>> r) ||| (n <<< (64 - r))) % w64))
      | none => throw s!"eval: rotate of {repr x}"

/-- A value converted to the kind of the name it is stored in. -/
def coerce (k : Kind) (v : V) : M V :=
  match k, v with
  | .int, .int n => pure (.int n)
  | .int, .cw n => pure (.int n)
  | .word, .int n => pure (.cw (toW n))
  | .word, .cw n => pure (.cw n)
  | .word, .w x => pure (.w x)
  | .arr, .ra els => pure (.ra els)
  | .arr, .mem nm n => pure (.mem nm n)
  | .arr, .gtab nm els => pure (.gtab nm els)
  | _, _ => throw s!"eval: cannot store {repr v} in a {repr k}"

/-- A cell value: words only, an integer taken as a word. -/
def cellVal : V → M V
  | .int n => pure (.cw (toW n))
  | .cw n => pure (.cw n)
  | .w x => pure (.w x)
  | v => throw s!"eval: cannot store {repr v} in an array cell"

/-- The kind of a declared type; words and arrays must be 64-bit. -/
def kindOf : Ty → M Kind
  | .int => pure .int
  | .word 64 => pure .word
  | .arr 64 _ => pure .arr
  | ty => throw s!"eval: unsupported type {repr ty} (words are 64-bit)"

/-- Cell `k` of an array value: the cell of a register array, or an emitted
    `load` of a memory array. -/
def readCell (av : V) (k : Nat) : M V := do
  match av with
  | .ra els =>
      match els[k]? with
      | some .undef => throw s!"eval: read of unassigned cell {k}"
      | some v => pure v
      | none => throw s!"eval: index {k} out of bounds"
  | .mem nm n =>
      unless k < n do throw s!"eval: index {k} out of bounds of {nm}"
      let t ← fresh
      emit (.assign kiName (.imm k))
      emit (.assign t (.load nm kiName))
      pure (.w t)
  | .gtab nm els =>
      match els[k]? with
      | some x => pure (.cw x)
      | none => throw s!"eval: index {k} out of bounds of {nm}"
  | v => throw s!"eval: indexing {repr v}"

/-- The name holding the base address of the global table `nm`, binding it on
    first use as `b = @nm` (`Rhs.glob` of the `@`-prefixed symbol). Inside a
    rolled loop body the binding goes to the statements placed ahead of the
    loop. The table joins the tables read at a run-time index. -/
def globBase (nm : String) (els : Array Nat) : M String := do
  match (← get).gbases.lookup nm with
  | some b => pure b
  | none =>
      let b := "%g" ++ nm
      let st : Stmt := .assign b (.glob ("@" ++ nm))
      modify fun s =>
        { s with gbases := (nm, b) :: s.gbases, adecls := s.adecls.push (b, els.size),
                 tables := if s.tables.any (·.1 == nm) then s.tables
                           else s.tables.push (nm, els.toList) }
      if (← get).inBody then modify fun s => { s with hoist := s.hoist.push st }
      else emit st
      pure b

/-- A cell of an array value at the run-time index held by `x`: an emitted `load`
    of a memory array, or of a global table when loops may be kept rolled. A
    register array is one value per cell, so its index must fold. -/
def readCellAt (av : V) (x : String) : M V := do
  let src ← match av with
    | .mem nm _ => pure nm
    | .gtab nm els =>
        if (← get).roll then globBase nm els
        else throw s!"eval: run-time index into the global table {nm}"
    | v => throw s!"eval: run-time index into {repr v}"
  let t ← fresh
  emit (.assign t (.load src x))
  pure (.w t)

/-! ## 5. Evaluator -/

/-- The bound on the iterations of one `while`. -/
def whileFuel : Nat := 1000000

/-- The trip count from which a loop is kept rolled whatever its body. -/
def rollMinTrips : Nat := 64

/-- The statements one iteration emits from which a loop is kept rolled. -/
def rollMinStmts : Nat := 64

/-- Whether a loop of `n` trips whose unrolling emits `emitted` statements is
    kept rolled: at least two trips, and either `rollMinTrips` trips or
    `rollMinStmts` statements per trip. -/
def rollable (n emitted : Nat) : Bool :=
  n ≥ 2 && (n ≥ rollMinTrips || emitted / n ≥ rollMinStmts)

/-- Whether a value names no emitted run-time word, so that it stays valid
    outside the loop that computed it. -/
partial def isCt : V → Bool
  | .w _ => false
  | .ra els => els.all isCt
  | _ => true

/-- A value with every scalar and every cell unassigned. -/
def undefLike : V → V
  | .ra els => .ra (els.map fun _ => .undef)
  | _ => .undef

/-- The names of `env` whose value in `env'` differs. -/
def changedNames (env env' : Env) : List String :=
  env.filterMap fun (x, _, v) =>
    match env'.get? x with
    | some (_, v') => if v' == v then none else some x
    | none => none

/-- `env` with each of `xs` unassigned. -/
def undefAll (env : Env) (xs : List String) : Env :=
  env.map fun (x, k, v) => if xs.contains x then (x, k, undefLike v) else (x, k, v)

/-- The arrays a statement list stores into, without repetition. -/
def storedArrays (ss : Array Stmt) : List String :=
  ss.foldl (fun acc s =>
    match s with
    | .store a _ _ | .storeAt a _ _ => if acc.contains a then acc else acc ++ [a]
    | _ => acc) []

/-- A statement list less each assignment to a name no later statement reads. -/
def dropDead (ss : Array Stmt) : Array Stmt :=
  (ss.foldr (fun s (acc, live) =>
    let keep := match s with
      | .assign l _ => live.contains l
      | _ => true
    if keep then (s :: acc, JincToCom.stmtReads s ++ live) else (acc, live))
    (([] : List Stmt), ([] : List String))).1.toArray

/-- The value `c0 + stride · idx` of a loop counter at the run-time trip index
    `idx`, emitting the multiplication (an addition for `stride = 2`, a shift for
    another power of two) and the addition that are not the identity. -/
def ctrValue (idx : String) (c0 stride : Int) : M V := do
  let t1 ← if stride == 1 then pure idx else do
    let t ← fresh
    let s := toW stride
    if s == 2 then emit (.assign t (.bin .add idx (.var idx)))
    else if s != 0 && 2 ^ s.log2 == s then emit (.assign t (.bin .shl idx (.lit s.log2)))
    else emit (.assign t (.bin .mul idx (.lit s)))
    pure t
  if c0 == 0 then return .w t1
  let t2 ← fresh
  emit (.assign t2 (.bin .add t1 (.lit (toW c0))))
  pure (.w t2)

/-- The frame after a rolled loop: the unrolled frame `envU`, with each name the
    loop body writes (`d`) unassigned where its unrolled value names a run-time
    word the rolled loop does not bind. -/
def postRollEnv (envU : Env) (d : List String) : Env :=
  envU.map fun (x, k, v) => if d.contains x && !isCt v then (x, k, undefLike v) else (x, k, v)

/-- The compile-time counter of a `while` traced by its iteration-start frames:
    the first name holding a compile-time scalar that advances by the same
    nonzero step at every trip, with its entry value and step. -/
def affineCounter (starts : List Env) : Option (String × Int × Int) :=
  let asInt : V → Option Int
    | .int n => some n
    | .cw n => some n
    | _ => none
  match starts with
  | e0 :: e1 :: _ =>
      e0.findSome? fun (x, _, v0) => do
        let a ← asInt v0
        let b ← asInt ((e1.get? x).map (·.2) |>.getD .undef)
        let st := b - a
        if st == 0 then none
        let ok := starts.zipIdx.all fun (e, k) =>
          (e.get? x).bind (fun kv => asInt kv.2) == some (a + st * k)
        if ok then some (x, a, st) else none
  | _ => none

mutual

/-- The value of a name: a frame variable, a `param int`, a global constant or a
    global table. -/
partial def lookupVar (p : Prog) (env : Env) (x : String) : M V := do
  match env.get? x with
  | some (_, .undef) => throw s!"eval: read of unassigned '{x}'"
  | some (_, v) => pure v
  | none =>
      match p.params.find? (·.1 == x) with
      | some (_, e) => evalE p [] e
      | none =>
          match p.gconsts.find? (·.1 == x) with
          | some (_, e) => do cellVal (← evalE p [] e)
          | none =>
              match p.globs.find? (·.1 == x) with
              | some (_, es) => do
                  let vs ← es.mapM (fun e => do cellVal (← evalE p [] e))
                  let ws := vs.filterMap constWord?
                  if ws.length == vs.length then pure (.gtab x ws.toArray)
                  else pure (.ra vs.toArray)
              | none => throw s!"eval: unknown name '{x}'"

/-- The value of an expression, emitting the statements of its run-time part. -/
partial def evalE (p : Prog) (env : Env) : E → M V
  | .num n => pure (.int n)
  | .var x => lookupVar p env x
  | .idx a i => do
      match ← evalE p env i with
      | .w x => readCellAt (← lookupVar p env a) x
      | vi => readCell (← lookupVar p env a) (← constNat vi)
  | .call f args => do
      match ← evalCall p env f args with
      | [v] => pure v
      | vs => throw s!"eval: '{f}' returns {vs.length} values in an expression"
  | .bin "&" (.not a) b => do
      let va ← evalE p env a
      let vb ← evalE p env b
      match va with
      | .w x => andnV x vb
      | _ => binV "&" (← notV va) vb
  | .bin "&" b (.not a) => do
      let vb ← evalE p env b
      let va ← evalE p env a
      match va with
      | .w x => andnV x vb
      | _ => binV "&" vb (← notV va)
  | .bin op a b => do
      let va ← evalE p env a
      let vb ← evalE p env b
      binV op va vb
  | .neg a => do negV (← evalE p env a)
  | .not a => do notV (← evalE p env a)
  | .cast w a => do
      unless w == 64 do throw s!"eval: cast to u{w} (words are 64-bit)"
      let v ← evalE p env a
      match v with
      | .int n => pure (.cw (toW n))
      | _ => pure v
  | .cond c t f => do
      match truth? (← evalE p env c) with
      | some true => evalE p env t
      | some false => evalE p env f
      | none => throw "eval: data-dependent '?:'"

/-- The results of a call: an intrinsic, or an inlined source function. -/
partial def evalCall (p : Prog) (env : Env) (f : String) (args : List E) : M (List V) := do
  let vs ← args.mapM (evalE p env)
  match f, vs with
  | "#ROL_64", [x, i] => do
      let r ← rotV x ((64 - (← constNat i) % 64) % 64)
      pure [.undef, .undef, r]
  | "#ROR_64", [x, i] => do
      let r ← rotV x ((← constNat i) % 64)
      pure [.undef, .undef, r]
  | "#swap", [a, b] => pure [b, a]
  | "#spill", _ => pure []
  | "#unspill", _ => pure []
  | _, _ =>
      match p.fns.find? (·.name == f) with
      | some fn => callFn p fn vs
      | none => throw s!"eval: unknown function or intrinsic '{f}' with {vs.length} arguments"

/-- An inlined call: the parameters bound to the argument values in a fresh
    frame, the body run, the returned expressions evaluated. -/
partial def callFn (p : Prog) (fn : Fn) (vs : List V) : M (List V) := do
  unless fn.params.length == vs.length do
    throw s!"eval: '{fn.name}' takes {fn.params.length} arguments, given {vs.length}"
  let mut env : Env := []
  for ((ty, _, nm), v) in fn.params.zip vs do
    let k ← kindOf ty
    env := (nm, k, ← coerce k v) :: env
  let env' ← execBlock p env fn.body
  fn.ret.mapM (evalE p env')

/-- The frame after an assignment. -/
partial def assignLV (p : Prog) (env : Env) (lv : LV) (v : V) : M Env := do
  match lv with
  | .wild => pure env
  | .var x =>
      match env.get? x with
      | some (k, _) => pure (env.set x (← coerce k v))
      | none => throw s!"eval: assignment to undeclared '{x}'"
  | .idx a i =>
      let vi ← evalE p env i
      if let .w x := vi then
        match env.get? a with
        | some (_, .mem nm _) =>
            let y ← wordName v
            emit (.storeAt nm (.var x) (.glob y))
            return env
        | _ => throw s!"eval: store into '{a}' at a run-time index"
      let k ← constNat vi
      match env.get? a with
      | some (_, .gtab _ els) =>
          unless k < els.size do throw s!"eval: index {k} out of bounds of '{a}'"
          pure (env.set a (.ra ((els.map V.cw).setIfInBounds k (← cellVal v))))
      | some (_, .ra els) =>
          unless k < els.size do throw s!"eval: index {k} out of bounds of '{a}'"
          pure (env.set a (.ra (els.setIfInBounds k (← cellVal v))))
      | some (_, .mem nm n) =>
          unless k < n do throw s!"eval: index {k} out of bounds of '{a}'"
          let x ← wordName v
          emit (.store nm k x)
          pure env
      | _ => throw s!"eval: store into '{a}', which holds no array"

/-- The frame after a statement. -/
partial def execS (p : Prog) (env : Env) : S → M Env
  | .decl ty ptr names => do
      let k ← kindOf ty
      let init ← match ty, ptr with
        | .arr _ n, false => do
            let m ← constNat (← evalE p env n)
            pure (V.ra (Array.replicate m .undef))
        | _, _ => pure V.undef
      pure (names.foldl (fun e nm => (nm, k, init) :: e) env)
  | .assign lvs e => do
      let vs ← match e with
        | .call f args => evalCall p env f args
        | _ => do pure [← evalE p env e]
      if lvs.isEmpty then return env
      unless lvs.length == vs.length do
        throw s!"eval: {lvs.length} destinations for {vs.length} values"
      (lvs.zip vs).foldlM (fun en (lv, v) => assignLV p en lv v) env
  | .opAssign op lv e => do
      let cur : E := match lv with
        | .idx a i => .idx a i
        | .var x => .var x
        | .wild => .num 0
      let v ← evalE p env (.bin op cur e)
      assignLV p env lv v
  | .ite c t f => do
      match truth? (← evalE p env c) with
      | some true => execBlock p env t
      | some false => execBlock p env f
      | none => throw "eval: data-dependent 'if'"
  | .forTo v lo hi body => do
      let l ← evalE p env lo
      let h ← evalE p env hi
      match l, h with
      | .int l, .int h =>
          unless (env.get? v).isSome do throw s!"eval: undeclared loop counter '{v}'"
          forStmt p v l h body env
      | _, _ => throw "eval: loop bounds not known at compile time"
  | .while pre c post => whileStmt p pre c post env

/-- One trip of a loop body evaluated into its own statement list: `setup` (run
    inside that list, so the statements it emits open the body) gives the entry
    frame. Returns the exit frame, the body statements and the statements to
    place ahead of the loop; the enclosing statement list is left as it was. -/
partial def rollBody (p : Prog) (setup : M Env) (block : List S) :
    M (Env × Array Stmt × Array Stmt) := do
  let s ← get
  set { s with out := #[], hoist := #[], inBody := true }
  let env ← setup
  let env' ← execBlock p env block
  let s' ← get
  set { s' with out := s.out, hoist := s.hoist, inBody := s.inBody }
  pure (env', s'.out, s'.hoist)

/-- Emit `block` as a rolled loop of `n` trips: the statements ahead of the loop,
    then `for idx = 0 to n { body }` with `idx` the run-time trip index and the
    counter `ctr` at `c0 + stride · idx`, less the assignments nothing in the body
    reads (`dropDead`).

    The body is evaluated once to find the names a trip writes, then again from
    a frame in which those names are unassigned, so a body that reads a value an
    earlier trip left fails; so does a body that stores into other than exactly
    one array (the loop accumulator). The result frame is `envU`, the frame of
    the unrolled loop, less the run-time values the rolled loop does not bind. -/
partial def tryRoll (p : Prog) (n : Nat) (ctr : String) (c0 stride : Int)
    (block : List S) (env envU : Env) : M Env := do
  let idx ← fresh
  let setup (undefs : List String) : M Env := do
    let cv ← ctrValue idx c0 stride
    pure ((undefAll env undefs).set ctr cv)
  let s0 ← get
  let (env1, _, _) ← rollBody p (setup []) block
  let d := changedNames env env1
  set s0
  let (_, body, hoisted) ← rollBody p (setup d) block
  unless (storedArrays body).length == 1 do
    throw "eval: a rolled loop body stores into other than one array"
  hoisted.forM emit
  emit (.forTo idx 0 n (dropDead body).toList)
  pure (postRollEnv envU d)

/-- The frame after `for v = i to h { body }`, kept rolled when `rollable` and
    `tryRoll` succeeds, unrolled otherwise. -/
partial def forStmt (p : Prog) (v : String) (i h : Int) (body : List S) (env : Env) :
    M Env := do
  let s0 ← get
  let envU ← forLoop p v i h body env
  let s1 ← get
  let n := (h - i).toNat
  if !s0.roll || s0.inBody || !rollable n (s1.out.size - s0.out.size) then return envU
  tryCatch (do set s0; tryRoll p n v i 1 body env envU) (fun _ => pure envU)

/-- The iteration-start frames of `while { pre } (c) {}` unrolled, and its exit
    frame. -/
partial def whileTrace (p : Prog) (pre : List S) (c : E) (fuel : Nat) (env : Env)
    (acc : List Env) : M (List Env × Env) := do
  let env' ← execBlock p env pre
  match truth? (← evalE p env' c) with
  | some false => pure ((env :: acc).reverse, env')
  | some true =>
      if fuel == 0 then throw "eval: 'while' exceeds the unrolling bound"
      whileTrace p pre c (fuel - 1) env' (env :: acc)
  | none => throw "eval: data-dependent 'while' guard"

/-- The frame after `while { pre } (c) { post }`. With an empty `post`, a loop
    whose unrolling is `rollable` and whose trips advance one compile-time
    counter by a fixed step (`affineCounter`) is kept rolled when `tryRoll`
    succeeds; every other loop is unrolled. -/
partial def whileStmt (p : Prog) (pre : List S) (c : E) (post : List S) (env : Env) :
    M Env := do
  let s0 ← get
  if !s0.roll || s0.inBody || !post.isEmpty then
    return ← whileLoop p pre c post whileFuel env
  let (starts, envU) ← whileTrace p pre c whileFuel env []
  let s1 ← get
  let n := starts.length
  if !rollable n (s1.out.size - s0.out.size) then return envU
  match affineCounter starts with
  | some (x, c0, st) =>
      tryCatch (do set s0; tryRoll p n x c0 st pre env envU) (fun _ => pure envU)
  | none => pure envU

/-- The frame after `for v = i to h { body }`. -/
partial def forLoop (p : Prog) (v : String) (i h : Int) (body : List S) (env : Env) :
    M Env := do
  if i < h then
    let env' ← execBlock p (env.set v (.int i)) body
    forLoop p v (i + 1) h body env'
  else pure env

/-- The frame after `while { pre } (c) { post }`, unrolled while `c` folds to true. -/
partial def whileLoop (p : Prog) (pre : List S) (c : E) (post : List S) (fuel : Nat)
    (env : Env) : M Env := do
  let env ← execBlock p env pre
  match truth? (← evalE p env c) with
  | some false => pure env
  | some true =>
      if fuel == 0 then throw "eval: 'while' exceeds the unrolling bound"
      let env ← execBlock p env post
      whileLoop p pre c post (fuel - 1) env
  | none => throw "eval: data-dependent 'while' guard"

/-- The frame after a block. -/
partial def execBlock (p : Prog) (env : Env) (ss : List S) : M Env :=
  ss.foldlM (execS p) env

end

/-! ## 6. Import -/

/-- Evaluate `fn` over its parameters: a `reg ptr` array of 64-bit cells is a
    memory array named by the parameter, a `reg u64` a run-time word. Returns the
    `JFun` parameters and the returned values. -/
def importFnM (p : Prog) (fn : Fn) : M (List Param × List V) := do
  let mut env : Env := []
  let mut params : Array Param := #[]
  for (ty, _, nm) in fn.params do
    match ty with
    | .arr 64 n =>
        let m ← constNat (← evalE p [] n)
        env := (nm, .arr, .mem nm m) :: env
        params := params.push ⟨.arr 64 m, nm⟩
    | .word 64 =>
        env := (nm, .word, .w nm) :: env
        params := params.push ⟨.reg 64, nm⟩
    | ty => throw s!"import: unsupported parameter type {repr ty} of '{nm}'"
  let env' ← execBlock p env fn.body
  let rs ← fn.ret.mapM (evalE p env')
  pure (params.toList, rs)

/-- The imported `JFun` of function `f` of the source unit `src`, and the global
    tables it reads at a run-time index (symbol and words), with loops kept
    rolled when `roll` holds. -/
def importWith (roll : Bool) (src : String) (f : String) :
    Except String (JFun × List (String × List Nat)) := do
  let p ← parseProg src
  let some fn := p.fns.find? (·.name == f) | throw s!"import: no function '{f}'"
  let ((params, rs), st) ← (importFnM p fn).run { roll }
  let decls : List (JTy × String) :=
    (.reg 64, kiName) :: st.decls.toList.map (fun t => (.reg 64, t))
      ++ st.adecls.toList.map (fun (b, n) => (.arr 64 n, b))
  let fn : JFun ← match rs with
    | [.mem nm n] =>
        pure { name := f, params, retTy := .arr 64 n, decls, inlineInts := [],
               body := st.out.toList ++ [.ret nm] }
    | [.w nm] =>
        pure { name := f, params, retTy := .reg 64, decls, inlineInts := [],
               body := st.out.toList ++ [.ret nm] }
    | _ => throw s!"import: '{f}' must return one array parameter or one run-time word"
  pure (fn, st.tables.toList)

/-- The straight-line `JFun` of function `f` of the source unit `src`: every call
    inlined, every compile-time value folded, one statement per emitted operation. -/
def importFun (src : String) (f : String) : Except String JFun :=
  (importWith false src f).map (·.1)

/-- A `JFun` imported with loops kept rolled, and the global tables it reads at a
    run-time index. -/
structure RolledImport where
  /-- The imported function. A rolled loop is `for idx = 0 to n { body }`, `idx`
      a run-time 64-bit trip index; `b = @SYM` binds `b` to the base of the
      global table `SYM`. -/
  fn : JFun
  /-- Each global table read at a run-time index: its symbol and its words. -/
  tables : List (String × List Nat)

/-- `importFun` with every loop that is `rollable` and passes `tryRoll` kept as a
    rolled loop. -/
def importFunRolled (src : String) (f : String) : Except String RolledImport :=
  (importWith true src f).map fun (fn, tables) => { fn, tables }

end CatCrypt.Crypto.Jasmin.JincInline
