/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# `.jinc` straight-line leaf parser (front: text → untyped AST)

Parses the straight-line fragment of a hand-written Jasmin `.jinc` leaf into an
untyped AST (`JFun`). The fragment covers `inline fn`/`fn` headers with `reg`/
`reg ptr` parameters, local `reg`/`reg ptr` declarations, width casts `(Wu)x`,
binary `*`/`+`/`-`/`&`/`|`/`^`/`<<`/`>>` with a register or literal operand,
compound `+=`, variable-indexed loads `tbl[idx]`, const-indexed stores
`out[k] = v`, a global-table assignment
`name = GLOBAL`, and `return name`. The elaborator (`JincToCom` §elab) turns a
`JFun` into a `Com jasminDialect`; this module is the textual front.

Targets the straight-line `ec_leaves.jinc` leaves (`ec_dlog`, `ec_pow_store`).
Data-dependent `if`/`else`, runtime `while`, and inter-leaf calls are not in the
fragment.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JincToCom

/-! ## 1. Tokens -/

inductive Tok where
  | ident (s : String)
  | num (n : Nat)
  | lparen | rparen | lbrace | rbrace | lbrack | rbrack
  | semi | comma | assign | plus | minus | star | arrow | plusEq
  | question | colon
  | amp | pipe | caret | shl | shr
  deriving Repr, BEq, Inhabited

abbrev Cs := List Char

/-- Skip whitespace and `//` / `/* */` comments. -/
partial def skipWhite : Cs → Cs
  | [] => []
  | '/' :: '/' :: rest => skipWhite (rest.dropWhile (· ≠ '\n'))
  | '/' :: '*' :: rest =>
      let rec dropBlock : Cs → Cs
        | [] => []
        | '*' :: '/' :: r => r
        | _ :: r => dropBlock r
      skipWhite (dropBlock rest)
  | c :: rest => if c.isWhitespace then skipWhite rest else c :: rest

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else (c.toLower.toNat - 'a'.toNat) + 10

def isHexDigit (c : Char) : Bool :=
  c.isDigit || (c.toLower ≥ 'a' && c.toLower ≤ 'f')

/-- Tokenize the `.jinc` fragment. -/
partial def tokenize (s : String) : Except String (List Tok) := do
  let rec go (cs : Cs) (acc : List Tok) : Except String (List Tok) := do
    match skipWhite cs with
    | [] => return acc.reverse
    | '+' :: '=' :: rest => go rest (.plusEq :: acc)
    | '-' :: '>' :: rest => go rest (.arrow :: acc)
    | '<' :: '<' :: rest => go rest (.shl :: acc)
    | '>' :: '>' :: rest => go rest (.shr :: acc)
    | '&' :: rest => go rest (.amp :: acc)
    | '|' :: rest => go rest (.pipe :: acc)
    | '^' :: rest => go rest (.caret :: acc)
    | '(' :: rest => go rest (.lparen :: acc)
    | ')' :: rest => go rest (.rparen :: acc)
    | '{' :: rest => go rest (.lbrace :: acc)
    | '}' :: rest => go rest (.rbrace :: acc)
    | '[' :: rest => go rest (.lbrack :: acc)
    | ']' :: rest => go rest (.rbrack :: acc)
    | ';' :: rest => go rest (.semi :: acc)
    | ',' :: rest => go rest (.comma :: acc)
    | '?' :: rest => go rest (.question :: acc)
    | ':' :: rest => go rest (.colon :: acc)
    | '=' :: rest => go rest (.assign :: acc)
    | '+' :: rest => go rest (.plus :: acc)
    | '-' :: rest => go rest (.minus :: acc)
    | '*' :: rest => go rest (.star :: acc)
    | cs0@(c :: _) =>
        if c.isAlpha || c == '_' then
          let id := String.ofList (cs0.takeWhile (fun c => c.isAlphanum || c == '_'))
          go (cs0.dropWhile (fun c => c.isAlphanum || c == '_')) (.ident id :: acc)
        else if c.isDigit then
          match cs0 with
          | '0' :: x :: rest' =>
              if x == 'x' || x == 'X' then
                let h := rest'.takeWhile isHexDigit
                let v := h.foldl (fun a d => a * 16 + hexVal d) 0
                go (rest'.dropWhile isHexDigit) (.num v :: acc)
              else
                let d := cs0.takeWhile Char.isDigit
                go (cs0.dropWhile Char.isDigit) (.num (String.ofList d).toNat! :: acc)
          | _ =>
              let d := cs0.takeWhile Char.isDigit
              go (cs0.dropWhile Char.isDigit) (.num (String.ofList d).toNat! :: acc)
        else throw s!"tokenize: unexpected character '{c}'"
  go s.toList []

/-! ## 2. Untyped AST -/

/-- A Jasmin width-tagged type in the fragment: a register `reg w` or a pointer
    to a byte array `ptr u8[n]` (modelled as a stack array). -/
inductive JTy where
  | reg (w : Nat)
  | arr (w n : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

inductive BinKind where
  | add | sub | mul | and | or | xor | shl | shr
  deriving Repr, BEq, Inhabited

/-- A binary right-hand operand: a variable or a literal. -/
inductive Operand where
  | var (s : String)
  | lit (n : Nat)
  deriving Repr, BEq, Inhabited

inductive Rhs where
  | cast (w : Nat) (src : String)            -- `(Wu) src`
  | bin (op : BinKind) (a : String) (b : Operand)  -- `a * b`, `a + b`
  | glob (name : String)                     -- `= GLOBAL`
  | load (arr : String) (idx : String)       -- `arr[idx]`
  | select (cond t f : String)               -- `cond ? t : f` (branchless cmov)
  deriving Repr, BEq, Inhabited

inductive Stmt where
  | assign (lhs : String) (rhs : Rhs)
  | compound (op : BinKind) (lhs : String) (rhs : Operand)  -- `lhs += rhs`
  | store (arr : String) (idx : Nat) (val : String)         -- `arr[k] = val`
  | ret (name : String)
  deriving Repr, BEq, Inhabited

structure Param where
  ty : JTy
  name : String
  deriving Repr, BEq, Inhabited

structure JFun where
  name : String
  params : List Param
  retTy : JTy
  decls : List (JTy × String)
  body : List Stmt
  deriving Repr, BEq, Inhabited

/-! ## 3. Parser -/

structure St where
  toks : List Tok
  deriving Inhabited

abbrev P := StateT St (Except String)

def peek : P (Option Tok) := do return (← get).toks.head?

def advance : P (Option Tok) := do
  let st ← get
  match st.toks with
  | [] => return none
  | t :: rest => set { st with toks := rest }; return some t

def expect (t : Tok) : P Unit := do
  match ← advance with
  | some t' => if t' == t then pure () else throw s!"expected {repr t}, got {repr t'}"
  | none => throw s!"expected {repr t}, got end of input"

def ident : P String := do
  match ← advance with
  | some (.ident s) => return s
  | other => throw s!"expected identifier, got {repr other}"

/-- Parse a width type: `u8`/`u16`/…/`u64` → `reg w`; an array suffix `[n]`
    promotes it to `arr w n`. -/
def parseTy : P JTy := do
  let id ← ident
  let w ← match id with
    | "u8" => pure 8 | "u16" => pure 16 | "u32" => pure 32
    | "u64" => pure 64 | "u128" => pure 128
    | "bool" => pure 1                       -- a 1-bit condition register
    | _ => throw s!"unknown width type '{id}'"
  match ← peek with
  | some .lbrack =>
      let _ ← advance
      let n ← match ← advance with
        | some (.num n) => pure n
        | other => throw s!"expected array length, got {repr other}"
      expect .rbrack
      return .arr w n
  | _ => return .reg w

/-- Parse one storage-qualified declaration head `reg [ptr] TYPE`, returning the
    type (storage class is dropped — `reg`/`reg ptr` both map to the value/array
    type). -/
def parseStorageTy : P JTy := do
  expect (.ident "reg")
  match ← peek with
  | some (.ident "ptr") => let _ ← advance; parseTy
  | _ => parseTy

/-- An operand: identifier or literal. -/
def parseOperand : P Operand := do
  match ← advance with
  | some (.ident s) => return .var s
  | some (.num n) => return .lit n
  | other => throw s!"expected operand, got {repr other}"

/-- Parse one statement (the token stream is positioned at the start of a
    statement inside the body; declarations are parsed separately). -/
def parseBinTail (lhs a : String) (k : BinKind) : P Stmt := do
  let _ ← advance
  let b ← parseOperand
  expect .semi
  return .assign lhs (.bin k a b)

def parseStmt : P Stmt := do
  match ← advance with
  | some (.ident "return") =>
      let r ← ident
      expect .semi
      return .ret r
  | some (.ident lhs) =>
      match ← advance with
      | some .assign =>
          match ← peek with
          | some .lparen =>
              let _ ← advance
              let w ← match ← advance with
                | some (.num w) => pure w
                | other => throw s!"expected cast width, got {repr other}"
              let _ ← ident                -- the `u` suffix tokenizes as ident "u"
              expect .rparen
              let src ← ident
              expect .semi
              return .assign lhs (.cast w src)
          | some (.ident a) =>
              let _ ← advance
              match ← peek with
              | some .lbrack =>
                  let _ ← advance
                  let idx ← ident
                  expect .rbrack
                  expect .semi
                  return .assign lhs (.load a idx)
              | some .star => parseBinTail lhs a .mul
              | some .plus => parseBinTail lhs a .add
              | some .minus => parseBinTail lhs a .sub
              | some .amp => parseBinTail lhs a .and
              | some .pipe => parseBinTail lhs a .or
              | some .caret => parseBinTail lhs a .xor
              | some .shl => parseBinTail lhs a .shl
              | some .shr => parseBinTail lhs a .shr
              | some .question =>                        -- `lhs = a ? t : f`
                  let _ ← advance
                  let t ← ident
                  expect .colon
                  let f ← ident
                  expect .semi
                  return .assign lhs (.select a t f)
              | some .semi =>
                  let _ ← advance
                  return .assign lhs (.glob a)            -- bare `lhs = NAME;`
              | other => throw s!"unexpected token after RHS identifier: {repr other}"
          | other => throw s!"unexpected RHS start: {repr other}"
      | some .plusEq =>
          let b ← parseOperand
          expect .semi
          return .compound .add lhs b
      | some .lbrack =>
          let k ← match ← advance with
            | some (.num k) => pure k
            | other => throw s!"expected store index, got {repr other}"
          expect .rbrack
          expect .assign
          let v ← ident
          expect .semi
          return .store lhs k v
      | other => throw s!"unexpected token after lhs '{lhs}': {repr other}"
  | other => throw s!"expected statement, got {repr other}"

/-- Parse the leading run of `reg …;` declarations of a body. -/
partial def parseDecls (acc : List (JTy × String)) : P (List (JTy × String)) := do
  match ← peek with
  | some (.ident "reg") =>
      let ty ← parseStorageTy
      let nm ← ident
      expect .semi
      parseDecls ((ty, nm) :: acc)
  | _ => return acc.reverse

/-- Parse the body: declarations, then statements until `}`. -/
partial def parseBody (acc : List Stmt) : P (List Stmt) := do
  match ← peek with
  | some .rbrace => return acc.reverse
  | none => throw "unexpected end of input in body"
  | _ => let s ← parseStmt; parseBody (s :: acc)

/-- Parse one parameter `reg [ptr] TYPE name`. -/
def parseParam : P Param := do
  let ty ← parseStorageTy
  let nm ← ident
  return ⟨ty, nm⟩

/-- Parse a `,`-separated parameter list up to `)`. -/
partial def parseParams (acc : List Param) : P (List Param) := do
  match ← peek with
  | some .rparen => return acc.reverse
  | _ =>
      let p ← parseParam
      match ← peek with
      | some .comma => let _ ← advance; parseParams (p :: acc)
      | _ => return (p :: acc).reverse

/-- Parse one `inline? fn name(params) -> ret { decls; body }`. -/
def parseFun : P JFun := do
  -- optional `inline`
  match ← peek with
  | some (.ident "inline") => let _ ← advance
  | _ => pure ()
  expect (.ident "fn")
  let nm ← ident
  expect .lparen
  let params ← parseParams []
  expect .rparen
  expect .arrow
  let retTy ← parseStorageTy
  expect .lbrace
  let decls ← parseDecls []
  let body ← parseBody []
  expect .rbrace
  return ⟨nm, params, retTy, decls, body⟩

/-- Parse a single `.jinc` function from a source string. -/
def parseJincFun (src : String) : Except String JFun := do
  let toks ← tokenize src
  let (f, _) ← (parseFun).run ⟨toks⟩
  return f

/-! ## 4. The two straight-line `ec_leaves.jinc` leaves (parse self-check) -/

/-- `ec_dlog` verbatim from `bench/msm_compare/ec_leaves.jinc`. -/
def ecDlogSrc : String :=
  "inline fn ec_dlog(reg u8 x, reg u8 y) -> reg u64 {
     reg ptr u8[529] tbl;
     reg u64 idx;
     reg u64 xx;
     reg u64 yy;
     reg u8 d;
     reg u64 r;
     tbl = EC_DLOG;
     xx = (64u)x;
     yy = (64u)y;
     idx = xx * 23;
     idx += yy;
     d = tbl[idx];
     r = (64u)d;
     return r;
   }"

/-- `ec_pow_store` verbatim from `bench/msm_compare/ec_leaves.jinc`. -/
def ecPowStoreSrc : String :=
  "inline fn ec_pow_store(reg ptr u8[2] out, reg u64 m) -> reg ptr u8[2] {
     reg ptr u8[56] tbl;
     reg u64 base;
     reg u8 v;
     tbl = EC_POW;
     base = m * 2;
     v = tbl[base];
     out[0] = v;
     base += 1;
     v = tbl[base];
     out[1] = v;
     return out;
   }"

/-- `ec_dlog` parses: 2 params, `reg 64` return, 6 decls, 8 body statements. -/
theorem ecDlog_parses :
    (parseJincFun ecDlogSrc).toOption.map (fun f => (f.params.length, f.retTy, f.decls.length, f.body.length))
      = some (2, .reg 64, 6, 8) := by native_decide

/-- `ec_pow_store` parses: 2 params, `arr 8 2` return, 3 decls, 8 body statements. -/
theorem ecPowStore_parses :
    (parseJincFun ecPowStoreSrc).toOption.map (fun f => (f.params.length, f.retTy, f.decls.length, f.body.length))
      = some (2, .arr 8 2, 3, 8) := by native_decide

/-! ## 5. A control-flow leaf: branchless constant-time select -/

/-- `ct_select(c, a, b) = c ? a : b`, the branch-free conditional move (`CMOVcc`
    data effect): the constant-time form of an `if`, with the condition a public
    `reg bool` input. -/
def ctSelectSrc : String :=
  "inline fn ct_select(reg bool c, reg u64 a, reg u64 b) -> reg u64 {
     reg u64 r;
     r = c ? a : b;
     return r;
   }"

/-- `ct_select` parses: 3 params, `reg 64` return, 1 decl, 2 body statements (the
    select assignment + the return). -/
theorem ctSelect_parses :
    (parseJincFun ctSelectSrc).toOption.map (fun f => (f.params.length, f.retTy, f.decls.length, f.body.length))
      = some (3, .reg 64, 1, 2) := by native_decide

/-! ## 6. Scalar-op leaves: subtraction, bitwise `&`/`|`/`^`, shift-by-literal -/

/-- `sub(a, b) = a - b`. -/
def subSrc : String :=
  "inline fn sub(reg u64 a, reg u64 b) -> reg u64 {
     reg u64 r;
     r = a - b;
     return r;
   }"

/-- `bit_and(a, b) = a & b`. -/
def andSrc : String :=
  "inline fn bit_and(reg u64 a, reg u64 b) -> reg u64 {
     reg u64 r;
     r = a & b;
     return r;
   }"

/-- `bit_or(a, b) = a | b`. -/
def orSrc : String :=
  "inline fn bit_or(reg u64 a, reg u64 b) -> reg u64 {
     reg u64 r;
     r = a | b;
     return r;
   }"

/-- `bit_xor(a, b) = a ^ b`. -/
def xorSrc : String :=
  "inline fn bit_xor(reg u64 a, reg u64 b) -> reg u64 {
     reg u64 r;
     r = a ^ b;
     return r;
   }"

/-- `shl3(a) = a << 3` (shift by a literal amount). -/
def shlSrc : String :=
  "inline fn shl3(reg u64 a) -> reg u64 {
     reg u64 r;
     r = a << 3;
     return r;
   }"

/-- `shr2(a) = a >> 2` (shift by a literal amount). -/
def shrSrc : String :=
  "inline fn shr2(reg u64 a) -> reg u64 {
     reg u64 r;
     r = a >> 2;
     return r;
   }"

/-- The four register-operand scalar leaves (`-`, `&`, `|`, `^`) each parse to a
    2-parameter, 1-declaration, 2-statement `reg 64` function. -/
theorem scalarBinOps_parse :
    [subSrc, andSrc, orSrc, xorSrc].all (fun s =>
      (parseJincFun s).toOption.map
        (fun f => (f.params.length, f.retTy, f.decls.length, f.body.length))
        == some (2, .reg 64, 1, 2)) = true := by native_decide

/-- The two shift-by-literal leaves (`<<`, `>>`) each parse to a 1-parameter,
    1-declaration, 2-statement `reg 64` function. -/
theorem scalarShiftOps_parse :
    [shlSrc, shrSrc].all (fun s =>
      (parseJincFun s).toOption.map
        (fun f => (f.params.length, f.retTy, f.decls.length, f.body.length))
        == some (1, .reg 64, 1, 2)) = true := by native_decide

end CatCrypt.Crypto.Jasmin.JincToCom
