/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# `.jinc` leaf parser (front: text → untyped AST)

Parses a Jasmin leaf's text into an untyped AST (`JFun`). The fragment covers
`inline fn`/`export fn`/`fn` headers with `reg`/`reg ptr` parameters,
`reg`/`reg ptr` declarations binding several names at once, `inline int`
counters, width casts `(Wu)x` and `(Wu)arr[idx]`, binary
`*`/`+`/`-`/`&`/`|`/`^`/`<<`/`>>` with a register or literal operand, the
compound assignments `+=`/`-=`/`*=`/`&=`/`|=`/`^=`/`<<=`/`>>=`, literal
assignments `x = n`, variable-indexed loads `tbl[idx]`, stores `out[idx] = v`
at a literal or variable index and with a cast right-hand side, a global-table
assignment `name = GLOBAL`, `while (v != 0) { … }`, `for v = lo to hi { … }`,
and `return name`. The elaborator (`JincElab`) turns a `JFun` into a
`Com jasminDialect`; this module is the textual front. The rotate `Rhs.ror` and
the operator `BinKind.andn`, the external call `Rhs.call` and the run-time loop
`Stmt.forRt` have no syntax in this parser; `JincInline`, the partial evaluator
for full Jasmin source units, produces them. `ArgSlot` records where a
function parameter's value comes from at entry.

Targets the straight-line `ec_leaves.jinc` leaves (`ec_dlog`, `ec_pow_store`)
and the two loop forms of the `.jazz` printer's output. Data-dependent
`if`/`else` and inter-leaf calls are not in the fragment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JincToCom

/-! ## 1. Tokens -/

inductive Tok where
  | ident (s : String)
  | num (n : Nat)
  | lparen | rparen | lbrace | rbrace | lbrack | rbrack
  | semi | comma | assign | plus | minus | star | arrow | plusEq
  | question | colon | neq
  | amp | pipe | caret | shl | shr
  | minusEq | starEq | ampEq | pipeEq | caretEq | shlEq | shrEq
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
    | '!' :: '=' :: rest => go rest (.neq :: acc)
    | '<' :: '<' :: '=' :: rest => go rest (.shlEq :: acc)
    | '>' :: '>' :: '=' :: rest => go rest (.shrEq :: acc)
    | '-' :: '=' :: rest => go rest (.minusEq :: acc)
    | '*' :: '=' :: rest => go rest (.starEq :: acc)
    | '&' :: '=' :: rest => go rest (.ampEq :: acc)
    | '|' :: '=' :: rest => go rest (.pipeEq :: acc)
    | '^' :: '=' :: rest => go rest (.caretEq :: acc)
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

/-- A binary operator. `andn a b` is `(~a) & b`, the BMI1 `ANDN`. -/
inductive BinKind where
  | add | sub | mul | and | or | xor | shl | shr | andn
  deriving Repr, BEq, Inhabited

/-- A binary right-hand operand: a variable or a literal. -/
inductive Operand where
  | var (s : String)
  | lit (n : Nat)
  deriving Repr, BEq, Inhabited

inductive Rhs where
  | cast (w : Nat) (src : String)            -- `(Wu) src`
  | bin (op : BinKind) (a : String) (b : Operand)  -- `a * b`, `a + b`
  | glob (name : String)                     -- a bare name: `= GLOBAL` or `= v`
  | load (arr : String) (idx : String)       -- `arr[idx]`
  | select (cond t f : String)               -- `cond ? t : f` (branchless cmov)
  | imm (n : Nat)                            -- `= 0`
  | castLoad (w : Nat) (arr : String) (idx : String)  -- `(Wu) arr[idx]`
  /-- `src` rotated right by the immediate `n` (`#ROR_64`; `#ROL_64 i` is
      `ror (64 - i)`). -/
  | ror (n : Nat) (src : String)
  /-- A call to the external symbol `sym` with the named arguments; the bound
      name receives the callee's result. -/
  | call (sym : String) (args : List String)
  deriving Repr, BEq, Inhabited

inductive Stmt where
  | assign (lhs : String) (rhs : Rhs)
  | compound (op : BinKind) (lhs : String) (rhs : Operand)  -- `lhs += rhs`
  | store (arr : String) (idx : Nat) (val : String)         -- `arr[k] = val`
  | ret (name : String)
  /-- `arr[idx] = rhs` at a variable or literal index and a general right-hand
      side. -/
  | storeAt (arr : String) (idx : Operand) (val : Rhs)
  /-- `while (cond != 0) { body }`. -/
  | whileNz (cond : String) (body : List Stmt)
  /-- `for v = lo to hi { body }` over an `inline int` counter. -/
  | forTo (v : String) (lo hi : Nat) (body : List Stmt)
  /-- `for v = 0 to count { body }` with the trip count `count` a run-time
      64-bit word and `v` the run-time trip index. -/
  | forRt (v : String) (count : String) (body : List Stmt)
  deriving Repr, BEq, Inhabited

structure Param where
  ty : JTy
  name : String
  deriving Repr, BEq, Inhabited

/-- Where the value of a function parameter comes from at entry: the `j`-th
    System V argument register, or the region at byte offset `off` of the
    function's own frame. -/
inductive ArgSlot where
  | abi (j : Nat)
  | frame (off : Nat)
  deriving Repr, BEq, Inhabited

structure JFun where
  name : String
  params : List Param
  retTy : JTy
  decls : List (JTy × String)
  /-- The `inline int` counters declared in the body, in source order. -/
  inlineInts : List String
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

/-- A numeric literal. -/
def number : P Nat := do
  match ← advance with
  | some (.num n) => return n
  | other => throw s!"expected number, got {repr other}"

/-- The binary operation a compound-assignment token denotes. -/
def compoundKind : Tok → Option BinKind
  | .plusEq => some .add
  | .minusEq => some .sub
  | .starEq => some .mul
  | .ampEq => some .and
  | .pipeEq => some .or
  | .caretEq => some .xor
  | .shlEq => some .shl
  | .shrEq => some .shr
  | _ => none

/-- Parse a width-cast right-hand side with the opening `(` already consumed:
    `Wu) src` or `Wu) arr[idx]`. -/
def parseCastRhs : P Rhs := do
  let w ← number
  let _ ← ident                -- the `u` suffix tokenizes as ident "u"
  expect .rparen
  let src ← ident
  match ← peek with
  | some .lbrack =>
      let _ ← advance
      let idx ← ident
      expect .rbrack
      return .castLoad w src idx
  | _ => return .cast w src

/-- Parse the right-hand side of a store: a bare name or a width cast. -/
def parseStoreRhs : P Rhs := do
  match ← peek with
  | some .lparen => let _ ← advance; parseCastRhs
  | _ => return .glob (← ident)

/-- Parse one statement (the token stream is positioned at the start of a
    statement inside the body; declarations are parsed separately). -/
def parseBinTail (lhs a : String) (k : BinKind) : P Stmt := do
  let _ ← advance
  let b ← parseOperand
  expect .semi
  return .assign lhs (.bin k a b)

mutual

partial def parseStmt : P Stmt := do
  match ← advance with
  | some (.ident "return") =>
      let r ← ident
      expect .semi
      return .ret r
  | some (.ident "while") =>
      expect .lparen
      let c ← ident
      expect .neq
      expect (.num 0)
      expect .rparen
      expect .lbrace
      let body ← parseBody []
      expect .rbrace
      return .whileNz c body
  | some (.ident "for") =>
      let v ← ident
      expect .assign
      let lo ← number
      expect (.ident "to")
      let hi ← number
      expect .lbrace
      let body ← parseBody []
      expect .rbrace
      return .forTo v lo hi body
  | some (.ident lhs) =>
      match ← advance with
      | some .assign =>
          match ← peek with
          | some .lparen =>
              let _ ← advance
              let r ← parseCastRhs
              expect .semi
              return .assign lhs r
          | some (.num n) =>
              let _ ← advance
              expect .semi
              return .assign lhs (.imm n)
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
      | some .lbrack =>
          let idx ← parseOperand
          expect .rbrack
          expect .assign
          let v ← parseStoreRhs
          expect .semi
          match idx, v with
          | .lit k, .glob nm => return .store lhs k nm
          | _, _ => return .storeAt lhs idx v
      | some t =>
          match compoundKind t with
          | some k =>
              let b ← parseOperand
              expect .semi
              return .compound k lhs b
          | none => throw s!"unexpected token after lhs '{lhs}': {repr t}"
      | none => throw s!"unexpected end of input after lhs '{lhs}'"
  | other => throw s!"expected statement, got {repr other}"

/-- Parse statements until `}`. -/
partial def parseBody (acc : List Stmt) : P (List Stmt) := do
  match ← peek with
  | some .rbrace => return acc.reverse
  | none => throw "unexpected end of input in body"
  | _ => let s ← parseStmt; parseBody (s :: acc)

end

/-- Parse the `,`-free name list of a declaration, up to its `;`. -/
partial def parseNames (acc : List String) : P (List String) := do
  let n ← ident
  match ← peek with
  | some .semi => let _ ← advance; return (n :: acc).reverse
  | _ => parseNames (n :: acc)

/-- Parse the leading run of declarations of a body: `reg [ptr] TYPE n₁ … nₖ;`
    declares every listed name at that type, and `inline int n₁ … nₖ;` declares
    compile-time counters. -/
partial def parseDecls (acc : List (JTy × String)) (ints : List String) :
    P (List (JTy × String) × List String) := do
  match ← peek with
  | some (.ident "reg") =>
      let ty ← parseStorageTy
      let nms ← parseNames []
      parseDecls ((nms.map (fun n => (ty, n))).reverse ++ acc) ints
  | some (.ident "inline") =>
      let _ ← advance
      expect (.ident "int")
      let nms ← parseNames []
      parseDecls acc (nms.reverse ++ ints)
  | _ => return (acc.reverse, ints.reverse)

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

/-- Parse one `(inline | export)? fn name(params) -> ret { decls; body }`. -/
def parseFun : P JFun := do
  match ← peek with
  | some (.ident "inline") => let _ ← advance
  | some (.ident "export") => let _ ← advance
  | _ => pure ()
  expect (.ident "fn")
  let nm ← ident
  expect .lparen
  let params ← parseParams []
  expect .rparen
  expect .arrow
  let retTy ← parseStorageTy
  expect .lbrace
  let (decls, ints) ← parseDecls [] []
  let body ← parseBody []
  expect .rbrace
  return ⟨nm, params, retTy, decls, ints, body⟩

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

/-! ## 7. The two loop forms of the emitted `.jazz` printer -/

/-- `mldsa_expand_a_real` verbatim from
    `bench/mldsa_compare/gen/mldsa_expand_a_real.jazz`: rejection sampling under a
    `while (cont != 0)` guard. -/
def mldsaExpandASrc : String :=
  "// Auto-generated from CatCrypt Jasmin AST. Do not edit by hand.
export fn mldsa_expand_a_real(reg ptr u32[256] out, reg ptr u32[2016] buf) -> reg ptr u32[256]
{
  reg u64 pp b0 b1 b2 t t1 q lt ctr pos cont;

  pp = 0;
  b0 = 0;
  b1 = 0;
  b2 = 0;
  t = 0;
  t1 = 0;
  q = 0;
  lt = 0;
  ctr = 0;
  pos = 0;
  cont = ctr;
  cont -= 256;
  cont >>= 63;
  while (cont != 0) {
    b0 = (64u) buf[pos];
    pp = pos;
    pp += 1;
    b1 = (64u) buf[pp];
    pp = pos;
    pp += 2;
    b2 = (64u) buf[pp];
    pos += 3;
    t1 = b1;
    t1 <<= 8;
    t = b0;
    t += t1;
    t1 = b2;
    t1 <<= 16;
    t += t1;
    t &= 8388607;
    q = 8380417;
    lt = t;
    lt -= q;
    lt >>= 63;
    out[ctr] = (32u) t;
    ctr += lt;
    cont = ctr;
    cont -= 256;
    cont >>= 63;
  }

  return out;
}
"

/-- `mldsa_expand_mask_real` verbatim from
    `bench/mldsa_compare/gen/mldsa_expand_mask_real.jazz`: a `for` loop over an
    `inline int` counter. -/
def mldsaExpandMaskSrc : String :=
  "// Auto-generated from CatCrypt Jasmin AST. Do not edit by hand.
export fn mldsa_expand_mask_real(reg ptr u32[256] out, reg ptr u32[640] buf) -> reg ptr u32[256]
{
  reg u64 base oi oi1 p a0 a1 a2 a3 a4 f0 f1 t1 g c0 c1;
  inline int i;

  base = 0;
  oi = 0;
  oi1 = 0;
  p = 0;
  a0 = 0;
  a1 = 0;
  a2 = 0;
  a3 = 0;
  a4 = 0;
  f0 = 0;
  f1 = 0;
  t1 = 0;
  g = 0;
  c0 = 0;
  c1 = 0;
  for i = 0 to 128 {
    base = i;
    base *= 5;
    oi = i;
    oi *= 2;
    p = base;
    a0 = (64u) buf[p];
    p = base;
    p += 1;
    a1 = (64u) buf[p];
    p = base;
    p += 2;
    a2 = (64u) buf[p];
    p = base;
    p += 3;
    a3 = (64u) buf[p];
    p = base;
    p += 4;
    a4 = (64u) buf[p];
    f0 = a0;
    t1 = a1;
    t1 <<= 8;
    f0 += t1;
    t1 = a2;
    t1 <<= 16;
    f0 += t1;
    f0 &= 1048575;
    f1 = a2;
    f1 >>= 4;
    t1 = a3;
    t1 <<= 4;
    f1 += t1;
    t1 = a4;
    t1 <<= 12;
    f1 += t1;
    g = 524288;
    c0 = g;
    c0 -= f0;
    c1 = g;
    c1 -= f1;
    out[oi] = (32u) c0;
    oi1 = oi;
    oi1 += 1;
    out[oi1] = (32u) c1;
  }

  return out;
}
"

/-- The statement count of a loop body, `0` for a statement that is not a loop. -/
def loopBodyLength : Stmt → Nat
  | .whileNz _ body => body.length
  | .forTo _ _ _ body => body.length
  | .forRt _ _ body => body.length
  | _ => 0

/-- The guard variable of a `while (v != 0)` statement. -/
def whileGuard : Stmt → Option String
  | .whileNz c _ => some c
  | _ => none

/-- The counter and bounds of a `for v = lo to hi` statement. -/
def forRange : Stmt → Option (String × Nat × Nat)
  | .forTo v lo hi _ => some (v, lo, hi)
  | _ => none

/-- The names an operand reads. -/
def operandReads : Operand → List String
  | .var s => [s]
  | .lit _ => []

/-- The names a right-hand side reads. The base of a `.rodata` table, `@SYM`
    (`JincInline`), reads none. -/
def rhsReads : Rhs → List String
  | .cast _ src => [src]
  | .bin _ a b => a :: operandReads b
  | .glob g => if g.startsWith "@" then [] else [g]
  | .load arr idx => [arr, idx]
  | .select c t f => [c, t, f]
  | .imm _ => []
  | .castLoad _ arr idx => [arr, idx]
  | .ror _ src => [src]
  | .call _ args => args

/-- The names a straight-line statement reads; a loop statement is taken to
    read none of its body's names, and a run-time loop reads its trip count. -/
def stmtReads : Stmt → List String
  | .assign _ r => rhsReads r
  | .compound _ lhs o => lhs :: operandReads o
  | .store arr _ v => [arr, v]
  | .storeAt arr i v => arr :: operandReads i ++ rhsReads v
  | .ret nm => [nm]
  | .whileNz _ _ => []
  | .forTo _ _ _ _ => []
  | .forRt _ c _ => [c]

/-- The name a statement binds. -/
def stmtDefs : Stmt → List String
  | .assign lhs _ => [lhs]
  | .compound _ lhs _ => [lhs]
  | _ => []

/-! `mldsa_expand_a_real` parses: 2 params, `arr 32 256` return, 11 declarations,
no `inline int` counter, 15 body statements. -/
#guard
  (parseJincFun mldsaExpandASrc).toOption.map (fun f =>
      (f.params.length, f.retTy, f.decls.length, f.inlineInts.length, f.body.length))
    == some (2, .arr 32 256, 11, 0, 15)

/-! Body statement 13 of `mldsa_expand_a_real` is the `while` guarded by `cont`,
with a 25-statement body. -/
#guard
  ((parseJincFun mldsaExpandASrc).toOption.bind (fun f => f.body[13]?)).map
      (fun s => (whileGuard s, loopBodyLength s))
    == some (some "cont", 25)

/-! `mldsa_expand_mask_real` parses: 2 params, `arr 32 256` return, 15
declarations, the `inline int` counter `i`, 17 body statements. -/
#guard
  (parseJincFun mldsaExpandMaskSrc).toOption.map (fun f =>
      (f.params.length, f.retTy, f.decls.length, f.inlineInts, f.body.length))
    == some (2, .arr 32 256, 15, ["i"], 17)

/-! Body statement 15 of `mldsa_expand_mask_real` is the `for` loop `i = 0 to 128`,
with a 43-statement body. -/
#guard
  ((parseJincFun mldsaExpandMaskSrc).toOption.bind (fun f => f.body[15]?)).map
      (fun s => (forRange s, loopBodyLength s))
    == some (some ("i", 0, 128), 43)

end CatCrypt.Crypto.Jasmin.JincToCom
