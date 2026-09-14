/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror


@[expose] public section
set_option autoImplicit false

/-!
# `.jinc` text → `JasminCoqSemMirror.Cmd` parser

A minimal hand-rolled recursive-descent parser for the **straight-line
subset** of jasmin surface syntax used by the "Easy"-tier verified leaves
(UOV, QR-UOV, and the inner round body of MAYO's `gf16_mul_scalar`).

## Subset covered

* Register declarations: `reg u8 x;`, `reg u8 x y z;`, `reg u64 v;`,
  `reg u128 w;`  (recorded into a name → `WSize` env, **no IR output**).
* Assignment with simple RHS: `x = expr;`
* Compound assignment: `x >>= e;` (lowered to `x = x >> e;`),
  `x <<= e;`, `x &= e;`, `x ^= e;`, `x |= e;`
* Expressions:
  - variable reference: `x`
  - hex constant: `0x1F`
  - decimal constant: `42`
  - unary: `-x`
  - binary: `e & e`, `e ^ e`, `e | e`, `e >> e`, `e << e`
    (only one operator per RHS; no precedence climbing — this is enough
    for the `.jinc` bodies we care about because they're already written
    in a-normal form: every line is `lvar op rvar` or `lvar = const`).
* Line comments: `// ...` to end-of-line.

## What is NOT covered

* `for`, `if`, `while` (deferred — caller can run the post-unrolling IR).
* Function declarations / `inline fn` bodies (caller hands in just the
  body lines).
* Function calls (`x = my_func(a, b);`).
* Array indexing (`x[i]`, `inp[:u128 k]`).
* SIMD intrinsics (`#VPSHUFB_256(...)` etc.).
* `return` statement (caller strips it).

This is the **Easy** tier of `.jinc` constructs: straight-line `Cassgn`, `Copn`
and word arithmetic.

## Output

A `JasminCoqSemMirror.Cmd` (= `List Instr`).  Each parsed statement
becomes one `Cassgn` instruction with `AT_none` tag and `aword sz` type
where `sz` is the declared width of the LHS register.

## Smoke test

`CatCrypt/Crypto/Jasmin/Examples/JincParserDemo.lean` parses the inner round
body of `gf16_mul_scalar` and compares the result with a reference AST defined
there, by instruction count, constructor shape, left-hand-side names and
right-hand-side operator tags.
-/

namespace CatCrypt.Crypto.Jasmin.JincParser

open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## §1. Tokenizer -/

/-- One token.  We model both punctuation and lexemes as a flat enum so
    the parser core is a simple pattern-match. -/
inductive Token where
  | ident   (s : String) : Token
  | num     (n : Nat) : Token         -- decimal or hex literal
  | lparen  : Token                   -- `(`
  | rparen  : Token                   -- `)`
  | semi    : Token                   -- `;`
  | comma   : Token                   -- `,`
  | assign  : Token                   -- `=`
  | shrEq   : Token                   -- `>>=`
  | shlEq   : Token                   -- `<<=`
  | andEq   : Token                   -- `&=`
  | xorEq   : Token                   -- `^=`
  | orEq    : Token                   -- `|=`
  | shr     : Token                   -- `>>`
  | shl     : Token                   -- `<<`
  | amp     : Token                   -- `&`
  | bar     : Token                   -- `|`
  | caret   : Token                   -- `^`
  | minus   : Token                   -- `-`
  deriving Repr, BEq, Inhabited

/-- Hex digit value. -/
def hexDigitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else (c.toLower.toNat - 'a'.toNat) + 10

/-- Convert a hex digit string to a Nat. -/
def hexStrToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexDigitValue c) 0

/-- Tokenizer state: input characters indexed by position. We work on a
    `List Char` for clean recursion (no `String.Pos` arithmetic). -/
abbrev Cs := List Char

/-- Skip whitespace and `// ...` line comments. -/
partial def skipWhite : Cs → Cs
  | [] => []
  | '/' :: '/' :: rest =>
      let rest' := rest.dropWhile (· ≠ '\n')
      skipWhite rest'
  | c :: rest =>
      if c.isWhitespace then skipWhite rest else c :: rest

/-- Read an identifier `[A-Za-z_][A-Za-z0-9_]*`.  Caller has already
    verified that the first char is a valid start. -/
def readIdent (cs : Cs) : String × Cs :=
  let chars := cs.takeWhile (fun c => c.isAlphanum || c == '_')
  let rest  := cs.dropWhile (fun c => c.isAlphanum || c == '_')
  (String.ofList chars, rest)

/-- Read a number: decimal or `0x...` hex.  Caller has verified the
    first char is a digit. -/
def readNum : Cs → Nat × Cs
  | '0' :: 'x' :: rest =>
      let hex  := rest.takeWhile (fun c => c.isDigit ||
        (c.toLower >= 'a' && c.toLower <= 'f'))
      let rest := rest.dropWhile (fun c => c.isDigit ||
        (c.toLower >= 'a' && c.toLower <= 'f'))
      (hexStrToNat (String.ofList hex), rest)
  | '0' :: 'X' :: rest =>
      let hex  := rest.takeWhile (fun c => c.isDigit ||
        (c.toLower >= 'a' && c.toLower <= 'f'))
      let rest := rest.dropWhile (fun c => c.isDigit ||
        (c.toLower >= 'a' && c.toLower <= 'f'))
      (hexStrToNat (String.ofList hex), rest)
  | cs =>
      let dig  := cs.takeWhile Char.isDigit
      let rest := cs.dropWhile Char.isDigit
      ((String.ofList dig).toNat!, rest)

/-- One-shot tokenizer: produces `List Token` from the input string.
    Returns `Except String` on tokenization error. -/
partial def tokenize (s : String) : Except String (List Token) := do
  let rec go (cs : Cs) (acc : List Token) : Except String (List Token) := do
    match skipWhite cs with
    | [] => return acc.reverse
    | '>' :: '>' :: '=' :: rest => go rest (.shrEq :: acc)
    | '<' :: '<' :: '=' :: rest => go rest (.shlEq :: acc)
    | '>' :: '>' :: rest        => go rest (.shr   :: acc)
    | '<' :: '<' :: rest        => go rest (.shl   :: acc)
    | '&' :: '=' :: rest        => go rest (.andEq :: acc)
    | '^' :: '=' :: rest        => go rest (.xorEq :: acc)
    | '|' :: '=' :: rest        => go rest (.orEq  :: acc)
    | '(' :: rest               => go rest (.lparen :: acc)
    | ')' :: rest               => go rest (.rparen :: acc)
    | ';' :: rest               => go rest (.semi  :: acc)
    | ',' :: rest               => go rest (.comma :: acc)
    | '=' :: rest               => go rest (.assign :: acc)
    | '&' :: rest               => go rest (.amp   :: acc)
    | '|' :: rest               => go rest (.bar   :: acc)
    | '^' :: rest               => go rest (.caret :: acc)
    | '-' :: rest               => go rest (.minus :: acc)
    | cs@(c :: _) =>
        if c.isAlpha || c == '_' then
          let (id, rest) := readIdent cs
          go rest (.ident id :: acc)
        else if c.isDigit then
          let (n, rest) := readNum cs
          go rest (.num n :: acc)
        else
          throw s!"JincParser.tokenize: unexpected character '{c}'"
  go s.toList []

/-! ## §2. Parser

We expose a single function `parseBody : String → Except String Cmd`
that consumes a body fragment (zero or more `reg` declarations followed
by a sequence of straight-line assignments). -/

/-- Parser state: remaining tokens + the variable type environment
    built up from `reg <ty> x y z;` declarations. -/
structure St where
  toks : List Token
  env  : List (String × WSize) := []
  deriving Inhabited

/-- The parser monad: `Except String` over `St`. -/
abbrev P := StateT St (Except String)

/-- Peek the next token without consuming. -/
def peek : P (Option Token) := do
  let st ← get
  return st.toks.head?

/-- Consume one token. -/
def advance : P Unit := do
  let st ← get
  match st.toks with
  | _ :: rest => set { st with toks := rest }
  | []        => throwThe String "JincParser: unexpected end of input"

/-- Consume the next token and assert it matches `expected`. -/
def expect (t : Token) : P Unit := do
  match (← peek) with
  | some t' =>
      if t' == t then advance
      else throwThe String s!"JincParser: expected {repr t}, got {repr t'}"
  | none    => throwThe String s!"JincParser: expected {repr t}, got EOF"

/-- Consume an identifier and return its lexeme. -/
def expectIdent : P String := do
  match (← peek) with
  | some (.ident s) => advance; return s
  | some t          => throwThe String s!"JincParser: expected identifier, got {repr t}"
  | none            => throwThe String "JincParser: expected identifier, got EOF"

/-- Lookup an identifier's declared type in the env. -/
def lookupType (s : String) : P WSize := do
  let st ← get
  match st.env.find? (fun p => p.fst == s) with
  | some (_, sz) => return sz
  | none         => throwThe String s!"JincParser: undeclared variable '{s}'"

/-- Add `(name, size)` to the env. -/
def addDecl (name : String) (sz : WSize) : P Unit := do
  modify fun st => { st with env := (name, sz) :: st.env }

/-- Parse a type keyword (`u8`, `u16`, `u32`, `u64`, `u128`, `u256`). -/
def parseWSize : P WSize := do
  let s ← expectIdent
  match s with
  | "u8"   => return .U8
  | "u16"  => return .U16
  | "u32"  => return .U32
  | "u64"  => return .U64
  | "u128" => return .U128
  | "u256" => return .U256
  | _      => throwThe String s!"JincParser: expected width keyword (u8/.../u256), got '{s}'"

/-- Build a u8 constant `Pexpr` (`Papp1 (Oword_of_int sz) (Pconst n)`). -/
def mkConst (sz : WSize) (n : Nat) : Pexpr :=
  .Papp1 (.Oword_of_int sz) (.Pconst (Int.ofNat n))

/-- Parse an atom: either a variable reference (Pvar) or a numeric
    literal (lifted via `mkConst` using the *LHS register width*). -/
def parseAtom (lhsSz : WSize) : P Pexpr := do
  match (← peek) with
  | some (.ident s) =>
      advance
      let _sz ← lookupType s  -- check declared, but the Pvar carries the Var
      return .Pvar (mkLvar { v_var := { vtype := .aword _sz, vname := s } })
  | some (.num n) =>
      advance
      return mkConst lhsSz n
  | some t => throwThe String s!"JincParser: expected variable or number, got {repr t}"
  | none   => throwThe String "JincParser: expected expression, got EOF"

/-- Parse a single RHS expression: atom, or `- atom`, or `atom OP atom`.
    Returns the `Pexpr`.  `lhsSz` is used to size numeric literals
    (constants take the destination's width). -/
def parseExpr (lhsSz : WSize) : P Pexpr := do
  -- Unary `-` (must be followed by a single atom)
  if (← peek) == some .minus then
    advance
    let inner ← parseAtom lhsSz
    return .Papp1 (.Oneg (.Op_w lhsSz)) inner
  -- Else: atom; then maybe a binary operator
  let lhs ← parseAtom lhsSz
  match (← peek) with
  | some .amp   => advance
                   let rhs ← parseAtom lhsSz
                   return .Papp2 (.Oland lhsSz) lhs rhs
  | some .bar   => advance
                   let rhs ← parseAtom lhsSz
                   return .Papp2 (.Olor lhsSz) lhs rhs
  | some .caret => advance
                   let rhs ← parseAtom lhsSz
                   return .Papp2 (.Olxor lhsSz) lhs rhs
  | some .shr   => advance
                   let rhs ← parseAtom lhsSz
                   return .Papp2 (.Olsr lhsSz) lhs rhs
  | some .shl   => advance
                   let rhs ← parseAtom lhsSz
                   -- jasmin's `<<` corresponds to `Olsl (.Op_w sz)` (kind
                   -- carries the width as an `OpKind`).
                   return .Papp2 (.Olsl (.Op_w lhsSz)) lhs rhs
  | _ => return lhs

/-- Build the `Cassgn` instruction for `dst = expr;`. -/
def mkAssign (dst : String) (sz : WSize) (rhs : Pexpr) : Instr :=
  .MkI ()
    (.Cassgn (.Lvar { v_var := { vtype := .aword sz, vname := dst } })
      .AT_none (.aword sz) rhs)

/-- Consume one or more identifiers all of the given width into the env,
    terminating at a `;`.  Used by `reg <sz> a b c;` declarations. -/
partial def consumeRegList (sz : WSize) : P Unit := do
  let nm ← expectIdent
  addDecl nm sz
  match (← peek) with
  | some .semi => expect .semi
  | some (.ident _) => consumeRegList sz
  | some t => throwThe String s!"JincParser: expected identifier or ';' in reg decl, got {repr t}"
  | none   => throwThe String "JincParser: expected identifier or ';' in reg decl, got EOF"

/-- Parse one statement.  Returns:
    * `none` if it was a `reg <ty> ...;` declaration (no IR output)
    * `some i` for an assignment (one `Instr`) -/
def parseStmt : P (Option Instr) := do
  match (← peek) with
  | some (.ident "reg") =>
      advance
      let sz ← parseWSize
      consumeRegList sz
      return none
  | some (.ident name) =>
      advance
      let sz ← lookupType name
      let lvar : Pexpr := .Pvar (mkLvar { v_var := { vtype := .aword sz, vname := name } })
      match (← peek) with
      | some .assign =>
          advance
          let rhs ← parseExpr sz
          expect .semi
          return some (mkAssign name sz rhs)
      | some .shrEq =>
          advance
          let rhs ← parseAtom sz
          expect .semi
          return some (mkAssign name sz (.Papp2 (.Olsr sz) lvar rhs))
      | some .shlEq =>
          advance
          let rhs ← parseAtom sz
          expect .semi
          return some (mkAssign name sz (.Papp2 (.Olsl (.Op_w sz)) lvar rhs))
      | some .andEq =>
          advance
          let rhs ← parseAtom sz
          expect .semi
          return some (mkAssign name sz (.Papp2 (.Oland sz) lvar rhs))
      | some .xorEq =>
          advance
          let rhs ← parseAtom sz
          expect .semi
          return some (mkAssign name sz (.Papp2 (.Olxor sz) lvar rhs))
      | some .orEq =>
          advance
          let rhs ← parseAtom sz
          expect .semi
          return some (mkAssign name sz (.Papp2 (.Olor sz) lvar rhs))
      | some t => throwThe String s!"JincParser: expected assignment operator after '{name}', got {repr t}"
      | none   => throwThe String s!"JincParser: expected assignment operator after '{name}', got EOF"
  | some t => throwThe String s!"JincParser: expected 'reg' or identifier at start of statement, got {repr t}"
  | none   => throwThe String "JincParser: unexpected EOF mid-body"

/-- Parse a sequence of statements until EOF. -/
partial def parseStmts : P (List Instr) := do
  match (← peek) with
  | none => return []
  | some _ =>
      let mi ← parseStmt
      let rest ← parseStmts
      match mi with
      | some i => return i :: rest
      | none   => return rest

/-! ## §3. Top-level entry point -/

/-- Parse a `.jinc` body fragment (sequence of `reg` decls + assignments)
    into a `JasminCoqSemMirror.Cmd`. -/
def parseBody (s : String) : Except String Cmd := do
  let toks ← tokenize s
  let (cmd, _) ← (parseStmts.run { toks := toks } : Except String (List Instr × St))
  return cmd

/-- Same as `parseBody` but with a pre-declared environment.  Useful for
    bodies that reference outer-scope variables (e.g., function args). -/
def parseBodyWithEnv (env : List (String × WSize)) (s : String) :
    Except String Cmd := do
  let toks ← tokenize s
  let (cmd, _) ← (parseStmts.run { toks := toks, env := env } :
                  Except String (List Instr × St))
  return cmd

end CatCrypt.Crypto.Jasmin.JincParser
