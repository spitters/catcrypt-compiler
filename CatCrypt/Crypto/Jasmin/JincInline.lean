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

`param int` constants; `type` aliases; global `uW[n]` tables and `uW` constants;
`inline fn`, `fn` and `export fn` definitions with `inline int`, `reg`, `reg ptr`
and `stack` parameters and locals; expressions with C precedence over
`+ - * / % & | ^ << >> == != < <= > >=` (with the signed and unsigned forms `<s`,
`<=u`, `>>s`, …), `&& ||`, unary `!` and `-`, casts `(64u) e`, `(u64) e` and
`(uint) e`, `c ? a : b`, array indexing, width-typed cells `a[:uW e]`, memory
words `[:uW e]`, array views `a.[:uW e]`, vector packs `(kuW)[e, …]`, binary
operators with a width annotation (`^256u`, `+4u64`), calls to source functions,
to the intrinsics `#ROL_64`, `#ROR_64`, `#swap`, `#spill` and `#unspill`, and to
the 256-bit intrinsics of `ymmBinIntrinsic?`, `ymmUnIntrinsic?`,
`ymmImmIntrinsic?` and `ymmBinImmIntrinsic?` and to `#VPBROADCAST_4u64`; tuple
assignments with `_`, `()`, a parenthesised destination list and the flags
destination `?{…}`, declarations with an initial value, conditional assignments
`x = e if c;` (an `if` without `else`), compound assignments, `if`/`else`,
`for v = lo to hi`, `while { pre } (c) { post }`, and a final `return`.
Sub-arrays `a[e : n]` and `a[:uW e : n]`, packs of 1-, 2- and 4-bit lanes
(`(4u2)[…]`, the first lane the most significant), the casts `(64ui)` and
`(64si)` and the alignment annotations `#unaligned` / `#aligned` of an access
are parsed. Block comments nest, as in Jasmin. `namespace N { … }` qualifies
each name its items define, and each reference to it from inside, as `N::x`
(`qualifyNamespace`). `#[…]` annotations and `require` lines are skipped; the
caller supplies the required units in the text, a unit required inside a
namespace inside that namespace.

## Evaluation

* An `inline int`, a `param int`, a comparison, and a `reg` word whose value is
  known at compile time are folded (constant propagation). The conditions of `if`
  and `?:`, loop bounds and `while` guards must fold; a data-dependent branch is
  rejected, and so a `while` whose guard folds is unrolled.
* `importFunRolled` keeps a loop rolled instead when its unrolling is `rollable`
  (at least two trips, and `rollMinTrips` trips or `rollMinStmts` statements per
  trip): a `for`, or a `while { pre } (c) {}` or `while (c) { post }` whose trips
  advance one compile-time counter by a fixed step (`affineCounter`). The loop is emitted as
  `for idx = 0 to n { body }` over a run-time trip index `idx`, with the counter
  at `c0 + step · idx`. `tryRoll` evaluates the body with the names a trip writes
  unassigned, so a body that reads a value an earlier trip left, or stores into
  other than exactly one array, is unrolled; so is a loop inside a rolled body.
* Under `importFunRolled`, `while (v < n) { body }` with `v` holding `0` and `n` a
  run-time word is a run-time loop (`tryRtLoop`): `Stmt.forRt idx n body`, the body
  advancing `v` by one per trip and storing into exactly one array.
* A read of a memory array or of a global table at a run-time index is a `load`
  (a global table only under `importFunRolled`, from the base `b = @SYM` of its
  `.rodata` copy); a store into a memory array at a run-time index is a
  `storeAt`.
* A 64-bit word parameter may serve as a pointer: a run-time word derived from it
  by adding offsets carries its address (`Addr`), and a memory word `[:uW e]` at
  such an address is cell `off / (W / 8)` of the `W`-bit *view* of the parameter,
  an extra `JFun` parameter held in the same argument register. A run-time
  offset must be known to be a multiple of `W / 8` (`alignOf`).
* A narrow (`u8`, `u16`, `u32`) value is held zero-extended (`V.nw`); it is read
  from memory or from an array view only under a `(64u)` cast, arithmetic on it
  is rejected, and a store writes its low bits. An array view `a.[:uW e]` of an
  array of 64-bit cells reads or merges the `W`-bit field at byte offset `e`.
* `x / d` and `x % d` for a run-time word `x` and a compile-time `d` are a shift
  and a mask for a power of two and a multiply-high by `divMagic d` otherwise.
* Every call to a source function is inlined, `fn` as well as `inline fn`,
  except a call to one of the functions named in `callFns`, which is kept as a
  call (`callExt`).
* A `reg` or `stack` array is one value per cell (scalar replacement), and every
  index into it must fold; a `stack` array declared in the imported function's
  own body is instead a memory array in its frame. A `reg ptr` array parameter of
  the evaluated function is a memory array: a read is a `load` and a write a
  `store`, in source order, so a call whose array arguments alias computes what
  the source computes.
* A register copy emits no statement: the destination names the source's value.
* `!a & b` with `a` a run-time word is `BinKind.andn`; `#ROL_64(x, i)` and
  `#ROR_64(x, i)` are `Rhs.ror`.
* A scalar word is 64 bits wide. A `u256` word is a vector value (`V.vw` at run
  time, `V.vc` at compile time): `^`, `|`, `&` and the lane-annotated `+` and `-`
  on it, and the 256-bit intrinsics, are `Rhs.ymm`. A compile-time `u256` value
  an op reads is a `load` of a one-cell `.rodata` table holding it
  (`vecConstName`). `#VPBROADCAST_4u64(T[i])` of a global `u64` table `T` at a
  run-time index is a `load` of the table `T_bcast4u64` whose cell `k` is word
  `k` of `T` in each of its four lanes; at a compile-time index or of a
  compile-time word it is a compile-time `u256` value. A `reg ptr u256[n]`
  parameter is a memory array of 256-bit cells. `#VPBROADCAST_8u32`,
  `#VPBROADCAST_16u16` and `#VPBROADCAST_2u128` of a compile-time value are
  compile-time `u256` values, as are a pack and `#set0_256`.
* A `reg ptr` array parameter of `u8`, `u16` or `u32` cells is a memory array
  whose cells are read and written only through views: `a[:uW e]` and
  `a.[:uW e]` are cells of the `W`-bit view of `a` (`memView`), the same
  argument register. A `W`-bit view of a global table of other cells is its
  little-endian bytes: a compile-time value at a compile-time offset, a `load`
  from a derived `.rodata` table at a run-time one (`gtabView`).
* A lane-annotated shift of a vector word by a compile-time count is an
  immediate shift, by a vector word a per-lane shift; `!a & b` on vector words
  is `vpandn`.
* `#init_msf`, `#update_msf`, `#protect` and `#declassify` have their
  architectural meaning: the misspeculation flag is `0` and `#protect` returns
  its argument.
* A sub-array of a register array or global table at compile-time bounds is a
  register array of its cells; a sub-array of a memory array is rejected.
* Every other width of a `reg` or array type is rejected.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JincInline

open CatCrypt.Crypto.Jasmin.JincToCom (Stmt Rhs Operand BinKind JTy Param JFun ArgSlot)
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect (YmmOp)

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

/-- The three-character symbols: the shift assignments, the signed and unsigned
    comparisons `<=s`, `<=u`, `>=s`, `>=u` and the arithmetic shift `>>s`. -/
def syms3 : List String := ["<<=", ">>=", "<=s", "<=u", ">=s", ">=u", ">>s"]

/-- The two-character symbols, with the signed and unsigned comparisons `<s`,
    `<u`, `>s`, `>u`. -/
def syms2 : List String :=
  ["<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=", "*=", "&=", "|=", "^=", "->",
   "<s", "<u", ">s", ">u"]

/-- The one-character symbols, with the `.` of an array view `a.[e]`. -/
def syms1 : List Char := "(){}[];,=+-*/%&|^!<>?:.".toList

/-- A character that continues an identifier. -/
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The text after a block comment, given the text after its `/*` and the
    number of enclosing comments opened inside it: Jasmin block comments nest. -/
def dropComment (d : Nat) : Cs → Cs
  | [] => []
  | '*' :: '/' :: r => if d = 0 then r else dropComment (d - 1) r
  | '/' :: '*' :: r => dropComment (d + 1) r
  | _ :: r => dropComment d r

/-- The text with leading whitespace, `//` comments and nested `/* */` comments
    removed. -/
partial def skipWhite : Cs → Cs
  | [] => []
  | '/' :: '/' :: rest => skipWhite (rest.dropWhile (· ≠ '\n'))
  | '/' :: '*' :: rest => skipWhite (dropComment 0 rest)
  | c :: rest => if c.isWhitespace then skipWhite rest else c :: rest

/-- The namespace qualifiers `::x::y` that continue an identifier, and the text
    after them. -/
partial def qualTail : Cs → Cs × Cs
  | cs@(':' :: ':' :: c :: r) =>
      if c.isAlpha || c == '_' then
        let (q, rest) := qualTail (r.dropWhile isIdChar)
        (':' :: ':' :: c :: r.takeWhile isIdChar ++ q, rest)
      else ([], cs)
  | cs => ([], cs)

/-- The tokens of `cs`, appended to `acc`. A qualified name `N::x` is one
    identifier. -/
partial def tokenizeGo (cs : Cs) (acc : Array Tok) : Except String (Array Tok) :=
  match skipWhite cs with
  | [] => .ok acc
  | '#' :: '[' :: r => tokenizeGo (dropAnnot 0 r) acc
  | '"' :: r =>
      tokenizeGo ((r.dropWhile (· ≠ '"')).drop 1)
        (acc.push (.str (String.ofList (r.takeWhile (· ≠ '"')))))
  | cs0@(c :: r) =>
      if c.isAlpha || c == '_' || c == '#' then
        let (q, rest) := qualTail (r.dropWhile isIdChar)
        tokenizeGo rest
          (acc.push (.id (String.ofList (c :: r.takeWhile isIdChar ++ q))))
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

/-- The tokens `toks` with every `type N = T;` declaration removed and each later
    identifier `N` replaced by the tokens of `T`. -/
def expandTypeAliases (toks : Array Tok) : Array Tok := Id.run do
  let mut out : Array Tok := #[]
  let mut al : List (String × Array Tok) := []
  let mut i := 0
  while i < toks.size do
    match toks[i]!, toks[i+1]?, toks[i+2]? with
    | .id "type", some (.id n), some (.sym "=") =>
        let mut j := i + 3
        let mut ty : Array Tok := #[]
        while j < toks.size && toks[j]! != .sym ";" do
          ty := ty.push toks[j]!
          j := j + 1
        al := (n, ty) :: al
        i := j + 1
    | .id s, _, _ =>
        match al.lookup s with
        | some ty => out := out ++ ty
        | none => out := out.push (.id s)
        i := i + 1
    | t, _, _ =>
        out := out.push t
        i := i + 1
  return out

/-- The tokens of a source text, type aliases expanded. -/
def tokenize (src : String) : Except String (Array Tok) :=
  (tokenizeGo src.toList #[]).map expandTypeAliases

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
  /-- `[:uW e]`: the `W`-bit word in memory at the address `e`. -/
  | mem (w : Nat) (addr : E)
  /-- `a.[:uW e]`: the `W`-bit field at byte offset `e` of the array `a`. -/
  | view (a : String) (w : Nat) (off : E)
  /-- `a[e : n]` (`w = 0`): the `n` cells of the array `a` from cell `e`;
      `a[:uW e : n]`: the `n` `W`-bit cells of `a` from `W`-bit cell `e`. -/
  | slice (a : String) (w : Nat) (off len : E)
  deriving Repr, Inhabited

/-- An assignment destination: `_`, a variable, an array cell, a memory word, an
    array view, a sub-array `a[e : n]` or `a[:uW e : n]`, or the flags `?{…}`,
    which stand for all the flags an intrinsic returns ahead of its value. -/
inductive LV where
  | wild
  | var (s : String)
  | idx (a : String) (i : E)
  | mem (w : Nat) (addr : E)
  | view (a : String) (w : Nat) (off : E)
  | slice (a : String) (w : Nat) (off len : E)
  | flags
  deriving Repr, Inhabited

/-- A declared type: `int` (also `bool`), a word `uW`, or an array `uW[n]`. -/
inductive Ty where
  | int
  | word (w : Nat)
  | arr (w : Nat) (n : E)
  deriving Repr, Inhabited

/-- A surface statement. `decl` records whether an array is a `ptr` and whether
    its storage class is `stack`; `opAssign` carries the binary operator of a
    compound assignment. -/
inductive S where
  | decl (ty : Ty) (ptr stack : Bool) (names : List String)
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
  /-- The cell width of each global table. -/
  globWidths : List (String × Nat) := []
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

/-- The binding strength of a binary operator symbol, C order; a signed or
    unsigned comparison binds as its plain form. -/
def binPrec : String → Option Nat
  | "||" => some 1 | "&&" => some 2 | "|" => some 3 | "^" => some 4 | "&" => some 5
  | "==" => some 6 | "!=" => some 6
  | "<" => some 7 | "<=" => some 7 | ">" => some 7 | ">=" => some 7
  | "<s" => some 7 | "<=s" => some 7 | ">s" => some 7 | ">=s" => some 7
  | "<u" => some 7 | "<=u" => some 7 | ">u" => some 7 | ">=u" => some 7
  | "<<" => some 8 | ">>" => some 8 | ">>s" => some 8
  | "+" => some 9 | "-" => some 9
  | "*" => some 10 | "/" => some 10 | "%" => some 10
  | _ => none

/-- The binary operator of a compound-assignment symbol. -/
def opOfAssign : String → Option String
  | "+=" => some "+" | "-=" => some "-" | "*=" => some "*" | "&=" => some "&"
  | "|=" => some "|" | "^=" => some "^" | "<<=" => some "<<" | ">>=" => some ">>"
  | _ => none

/-- The lane width of a vector pack `(kuW)[…]`: a word width, or `1`, `2` or `4`
    for the packed immediates `(8u1)`, `(4u2)` and `(2u4)`. -/
def packWidth? : String → Option Nat
  | "u1" => some 1 | "u2" => some 2 | "u4" => some 4
  | s => wordWidth? s

/-- Whether the next token opens a width-typed access: `:` or an alignment
    annotation `#unaligned` / `#aligned`. -/
def isAccessStart : P Bool := do
  return (← isSym ":") || (← isId "#unaligned") || (← isId "#aligned")

/-- The width of a memory access after its `[`: `:uW` when present, `64`
    otherwise. An alignment annotation ahead of the width is skipped. -/
def parseAccessWidth : P Nat := do
  if (← isId "#unaligned") || (← isId "#aligned") then let _ ← next
  if (← isSym ":") then
    let _ ← next
    let s ← ident
    match wordWidth? s with
    | some w => return w
    | none => throw s!"parse: expected an access width, got '{s}'"
  else return 64

/-- The operator symbol `op` with the width annotation that follows it appended
    (`^` then `256u` gives `^256u`, `+` then `4u64` gives `+4u64`); `op` when no
    annotation follows. -/
def parseOpAnnot (op : String) : P String := do
  match ← get with
  | .num n :: .id s :: r =>
      if s == "u" || s == "s" || (wordWidth? s).isSome then
        set r
        return op ++ toString n ++ s
      else return op
  | _ => return op

/-- The cell `i` of the `W`-bit view of the array `a`, `a[:uW i]`, as the view
    field at byte offset `(W / 8) · i`. -/
def cellView (a : String) (w : Nat) (i : E) : E :=
  .view a w (.bin "*" i (.num (w / 8 : Nat)))

mutual

/-- A primary expression: a numeral, a memory word, a cast, a vector pack, a
    parenthesised expression, a call, an array cell, an array view or a
    variable. -/
partial def parsePrimary : P E := do
  match ← next with
  | .num n => return .num n
  | .sym "[" =>
      let w ← parseAccessWidth
      let a ← parseExpr
      expectSym "]"
      return .mem w a
  | .sym "(" =>
      match ← get with
      | .num w :: .id "u" :: .sym ")" :: r => set r; return .cast w (← parseUnary)
      | .num w :: .id "s" :: .sym ")" :: r => set r; return .cast w (← parseUnary)
      | .num w :: .id "ui" :: .sym ")" :: r => set r; return .cast w (← parseUnary)
      | .num w :: .id "si" :: .sym ")" :: r => set r; return .cast w (← parseUnary)
      | .num k :: .id s :: .sym ")" :: .sym "[" :: r =>
          -- a vector pack `(kuW)[e₁, …, eₖ]`, the intrinsic `#pack` with the
          -- lane count and the lane width ahead of the lanes
          match packWidth? s with
          | some w =>
            set r
            let mut es : List E := [← parseExpr]
            while (← isSym ",") do
              let _ ← next
              es := es ++ [← parseExpr]
            expectSym "]"
            return .call "#pack" (.num k :: .num w :: es)
          | none => throw s!"parse: unexpected '({k}{s})'"
      | .id s :: .sym ")" :: r =>
          if s == "int" || s == "uint" || s == "sint" then
            set r
            parseUnary
          else
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
        if (← isAccessStart) then
          let w ← parseAccessWidth
          let i ← parseExpr
          if (← isSym ":") then
            let _ ← next
            let n ← parseExpr
            expectSym "]"
            return .slice s w i n
          expectSym "]"
          return cellView s w i
        let i ← parseExpr
        if (← isSym ":") then
          let _ ← next
          let n ← parseExpr
          expectSym "]"
          return .slice s 0 i n
        expectSym "]"
        return .idx s i
      else if (← isSym ".") then
        let _ ← next
        expectSym "["
        let w ← parseAccessWidth
        let off ← parseExpr
        expectSym "]"
        return .view s w off
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
            let opA ← parseOpAnnot op
            let rhs ← parseBinRhs (p + 1) (← parseUnary)
            parseBinRhs minPrec (.bin opA lhs rhs)
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

/-- A storage class and type, with whether the storage is a `ptr` and whether
    the storage class is `stack`. -/
def parseStorTy : P (Ty × Bool × Bool) := do
  let s ← ident
  match s with
  | "inline" | "param" => return (← parseTy, false, false)
  | "reg" | "stack" =>
      if (← isId "mut") then let _ ← next
      if (← isId "const") then let _ ← next
      let ptr ← if (← isId "ptr") then do let _ ← next; pure true else pure false
      return (← parseTy, ptr, s == "stack")
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

/-- An assignment destination: `_`, a variable, an array cell `a[e]`, a memory
    word `[:uW e]` or an array view `a.[:uW e]`. -/
def parseLV : P LV := do
  if (← isSym "[") then
    let _ ← next
    let w ← parseAccessWidth
    let a ← parseExpr
    expectSym "]"
    return .mem w a
  if (← isSym "?") then
    let _ ← next
    expectSym "{"
    while !(← isSym "}") do let _ ← next
    let _ ← next
    return .flags
  let s ← ident
  if s == "_" then return .wild
  if (← isSym "[") then
    let _ ← next
    if (← isAccessStart) then
      let w ← parseAccessWidth
      let i ← parseExpr
      if (← isSym ":") then
        let _ ← next
        let n ← parseExpr
        expectSym "]"
        return .slice s w i n
      expectSym "]"
      return .view s w (.bin "*" i (.num (w / 8 : Nat)))
    let i ← parseExpr
    if (← isSym ":") then
      let _ ← next
      let n ← parseExpr
      expectSym "]"
      return .slice s 0 i n
    expectSym "]"
    return .idx s i
  if (← isSym ".") then
    let _ ← next
    expectSym "["
    let w ← parseAccessWidth
    let off ← parseExpr
    expectSym "]"
    return .view s w off
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
      let (ty, ptr, stk) ← parseStorTy
      let names ← parseNames true
      if (← isSym "=") then
        -- a declaration with an initial value, `reg uW x = e;`
        let _ ← next
        let e ← parseExpr
        expectSym ";"
        return [.decl ty ptr stk names, .assign (names.map LV.var) e]
      expectSym ";"
      return [.decl ty ptr stk names]
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
      -- `() = e;`, or a parenthesised tuple of destinations `(x, y) = e;`
      let _ ← next
      let lvs ← if (← isSym ")") then pure [] else parseLVs
      expectSym ")"
      expectSym "="
      let e ← parseExpr
      expectSym ";"
      return [.assign lvs e]
  | _ =>
      let lvs ← parseLVs
      match ← next with
      | .sym "=" =>
          let e ← parseExpr
          if (← isId "if") then
            -- a conditional assignment `x = e if c;`
            let _ ← next
            let c ← parseExpr
            expectSym ";"
            return [.ite c [.assign lvs e] []]
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
  let (ty, ptr, _) ← parseStorTy
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

/-- `e` with every referenced name `x` (variable, array, called function)
    replaced by `f x`. -/
partial def E.rename (f : String → String) : E → E
  | .num n => .num n
  | .var x => .var (f x)
  | .idx a i => .idx (f a) (i.rename f)
  | .call g args => .call (f g) (args.map (E.rename f))
  | .bin op a b => .bin op (a.rename f) (b.rename f)
  | .neg a => .neg (a.rename f)
  | .not a => .not (a.rename f)
  | .cast w a => .cast w (a.rename f)
  | .cond c t e => .cond (c.rename f) (t.rename f) (e.rename f)
  | .mem w a => .mem w (a.rename f)
  | .view a w o => .view (f a) w (o.rename f)
  | .slice a w o n => .slice (f a) w (o.rename f) (n.rename f)

/-- `lv` with every referenced name `x` replaced by `f x`. -/
def LV.rename (f : String → String) : LV → LV
  | .wild => .wild
  | .flags => .flags
  | .var x => .var (f x)
  | .idx a i => .idx (f a) (i.rename f)
  | .mem w a => .mem w (a.rename f)
  | .view a w o => .view (f a) w (o.rename f)
  | .slice a w o n => .slice (f a) w (o.rename f) (n.rename f)

/-- `s` with every referenced name `x` replaced by `f x`; declared names and
    loop counters are kept. -/
partial def S.rename (f : String → String) : S → S
  | .decl ty ptr stk ns => .decl ty ptr stk ns
  | .assign lvs e => .assign (lvs.map (LV.rename f)) (e.rename f)
  | .opAssign op lv e => .opAssign op (lv.rename f) (e.rename f)
  | .ite c t e => .ite (c.rename f) (t.map (S.rename f)) (e.map (S.rename f))
  | .forTo v lo hi b => .forTo v (lo.rename f) (hi.rename f) (b.map (S.rename f))
  | .while pre c post => .while (pre.map (S.rename f)) (c.rename f) (post.map (S.rename f))

/-- The names a statement list declares, nested blocks included. -/
partial def declaredNames (ss : List S) : List String :=
  ss.flatMap fun
    | .decl _ _ _ ns => ns
    | .ite _ t e => declaredNames t ++ declaredNames e
    | .forTo v _ _ b => v :: declaredNames b
    | .while pre _ post => declaredNames pre ++ declaredNames post
    | _ => []

/-- The items of the namespace `ns`, parsed into `q`, as items of the
    enclosing unit: each name `x` the namespace defines is `ns::x`, and so is
    each reference to it from inside the namespace, except where a function's
    parameter or local declaration of the same name is in scope. -/
def qualifyNamespace (ns : String) (q : Prog) : Prog :=
  let defs := q.params.map (·.1) ++ q.globs.map (·.1) ++ q.gconsts.map (·.1) ++ q.fns.map (·.name)
  let qual (x : String) : String := if defs.contains x then ns ++ "::" ++ x else x
  let fnRename (fn : Fn) : Fn :=
    let locals := fn.params.map (·.2.2) ++ declaredNames fn.body
    let g (x : String) : String := if locals.contains x then x else qual x
    { name := qual fn.name, params := fn.params
      body := fn.body.map (S.rename g), ret := fn.ret.map (E.rename g) }
  { params := q.params.map fun (n, e) => (qual n, e.rename qual)
    globs := q.globs.map fun (n, es) => (qual n, es.map (E.rename qual))
    gconsts := q.gconsts.map fun (n, e) => (qual n, e.rename qual)
    fns := q.fns.map fnRename
    globWidths := q.globWidths.map fun (n, w) => (qual n, w) }

/-- The top-level items, added to `p`, up to the end of the input or a `}`
    that closes a namespace. -/
partial def parseTop (p : Prog) : P Prog := do
  match ← peek with
  | none => return p
  | some (.sym "}") => return p
  | some (.id "namespace") =>
      let _ ← next
      let ns ← ident
      expectSym "{"
      let q := qualifyNamespace ns (← parseTop {})
      expectSym "}"
      parseTop { params := q.params ++ p.params, globs := q.globs ++ p.globs
                 gconsts := q.gconsts ++ p.gconsts, fns := q.fns ++ p.fns
                 globWidths := q.globWidths ++ p.globWidths }
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
      | .arr w _ =>
          expectSym "{"
          let es ← parseExprList
          expectSym "}"
          expectSym ";"
          parseTop { p with globs := (n, es) :: p.globs, globWidths := (n, w) :: p.globWidths }
      | .word w =>
          -- a constant wider than 64 bits keeps its width as a cast
          let e ← parseExpr
          expectSym ";"
          let e := if w > 64 then E.cast w e else e
          parseTop { p with gconsts := (n, e) :: p.gconsts }
      | _ =>
          let e ← parseExpr
          expectSym ";"
          parseTop { p with gconsts := (n, e) :: p.gconsts }
  | some t => throw s!"parse: unexpected {repr t} at top level"

/-- Parse a source unit. -/
def parseProg (src : String) : Except String Prog := do
  let toks ← tokenize src
  let (p, rest) ← (parseTop {}).run toks.toList
  unless rest.isEmpty do throw s!"parse: unexpected {repr rest.head!} at top level"
  return p

/-! ## 4. Values -/

/-- The word modulus. -/
def w64 : Nat := 2 ^ 64

/-- An integer as a 64-bit word. -/
def toW (n : Int) : Nat := (n % (w64 : Int)).toNat

/-- A value during evaluation: unassigned, a compile-time integer, a compile-time
    word, a run-time word held by an emitted name, a run-time `w`-bit word
    (`w < 64`) held zero-extended by an emitted name, a register array (one value
    per cell), a memory array named by an emitted array name, the read-only
    global table `nm` with its words, a run-time `w`-bit vector word (`w > 64`)
    held by an emitted name, or a compile-time `w`-bit vector word. -/
inductive V where
  | undef
  | int (n : Int)
  | cw (n : Nat)
  | w (nm : String)
  | nw (w : Nat) (nm : String)
  | ra (els : Array V)
  | mem (nm : String) (n : Nat)
  | gtab (nm : String) (els : Array Nat)
  | vw (w : Nat) (nm : String)
  | vc (w : Nat) (n : Nat)
  deriving Repr, Inhabited, BEq

/-- The kind of a declared name: an `inline int`, a 64-bit word, an array, or a
    `w`-bit vector word. -/
inductive Kind where
  | int
  | word
  | arr
  | vword (w : Nat)
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

/-- The address of a run-time word that points into a pointer parameter: the
    parameter `base`, plus the run-time word `rt` when present, plus the byte
    offset `off`. -/
structure Addr where
  base : String
  rt : Option String
  off : Int
  deriving Repr, Inhabited, BEq

/-- The evaluation state: the emitted statements, the emitted names that need a
    declaration, and the fresh-name counter; whether loops may be kept rolled,
    whether evaluation is inside a rolled loop body, the statements to place ahead
    of that loop, the base name bound for each global table read at a run-time
    index, the tables so read, and the array names with their cell counts; the
    call depth, the functions whose calls are kept, the address and the known
    alignment of run-time words, the memory views and frame arrays used, the
    shifts already emitted, the cell widths of the arrays of wider cells, and the
    names holding vector constants. -/
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
  /-- The call depth: `0` while the imported function's own body runs. -/
  depth : Nat := 0
  /-- The source functions whose calls are kept as calls. -/
  callFns : List String := []
  /-- The address of each run-time word that points into a pointer parameter. -/
  addrs : List (String × Addr) := []
  /-- A known power-of-two divisor (its exponent) of run-time words. -/
  aligns : List (String × Nat) := []
  /-- The memory views read or written, as (pointer parameter, width). -/
  views : Array (String × Nat) := #[]
  /-- The arrays in the imported function's frame, with their cell counts. -/
  frames : Array (String × Nat) := #[]
  /-- The names holding `x >>> k`, keyed by `(x, k)`. -/
  shrs : List ((String × Nat) × String) := []
  /-- The cell width of each memory array and table base whose cells are not
      64-bit. -/
  widths : List (String × Nat) := []
  /-- The names holding a compile-time vector word, keyed by its width and value,
      within a loop body or the function body. -/
  vcs : List ((Nat × Nat) × String) := []
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
  | .vc _ n => pure n
  | v => throw s!"eval: expected a compile-time integer, got {repr v}"

/-- The cell width of the memory array or table base `nm`: `64` unless another
    width is recorded. -/
def cellWidth (nm : String) : M Nat := return ((← get).widths.lookup nm).getD 64

/-- Record the cell width `w` of the memory array or table base `nm`. -/
def setWidth (nm : String) (w : Nat) : M Unit :=
  if w == 64 then pure () else modify fun s => { s with widths := (nm, w) :: s.widths }

/-- Whether a value is a vector word. -/
def isVec : V → Bool
  | .vw _ _ => true
  | .vc _ _ => true
  | _ => false

/-- The operator symbol of a source operator and its width annotation:
    `^256u` is `("^", "256u")`, `+4u64` is `("+", "4u64")`, `<<` is `("<<", "")`. -/
def splitOp (op : String) : String × String :=
  (String.ofList (op.toList.takeWhile (fun c => !c.isDigit)),
   String.ofList (op.toList.dropWhile (fun c => !c.isDigit)))

/-- The 64-bit words of the `w`-bit value `n`, least significant first. -/
def limbs64 (w n : Nat) : List Nat :=
  (List.range (w / 64)).map fun i => n / 2 ^ (64 * i) % w64

/-- The 256-bit word with the 64-bit word `n` in each of its four lanes. -/
def bcast4u64 (n : Nat) : Nat := n * (1 + 2 ^ 64 + 2 ^ 128 + 2 ^ 192)

/-- The truth of a folded condition. -/
def truth? : V → Option Bool
  | .int n => some (n != 0)
  | .cw n => some (n != 0)
  | _ => none

/-- A boolean as an integer. -/
def ofBool (b : Bool) : V := .int (if b then 1 else 0)

/-- A binary operator on compile-time integers; a signed or unsigned comparison
    is the plain one. -/
def intBin (op : String) (a b : Int) : Option V :=
  match op with
  | "+" => some (.int (a + b))
  | "-" => some (.int (a - b))
  | "*" => some (.int (a * b))
  | "/" => if b == 0 then none else some (.int (a / b))
  | "%" => if b == 0 then none else some (.int (a % b))
  | "==" => some (ofBool (a == b))
  | "!=" => some (ofBool (a != b))
  | "<" | "<s" | "<u" => some (ofBool (a < b))
  | "<=" | "<=s" | "<=u" => some (ofBool (a ≤ b))
  | ">" | ">s" | ">u" => some (ofBool (a > b))
  | ">=" | ">=s" | ">=u" => some (ofBool (a ≥ b))
  | "&&" => some (ofBool (a != 0 && b != 0))
  | "||" => some (ofBool (a != 0 || b != 0))
  | "&" => if a ≥ 0 && b ≥ 0 then some (.int (a.toNat &&& b.toNat : Nat)) else none
  | "|" => if a ≥ 0 && b ≥ 0 then some (.int (a.toNat ||| b.toNat : Nat)) else none
  | "^" => if a ≥ 0 && b ≥ 0 then some (.int (a.toNat ^^^ b.toNat : Nat)) else none
  | "<<" => if b ≥ 0 then some (.int (a * 2 ^ b.toNat)) else none
  | ">>" | ">>s" => if b ≥ 0 then some (.int (a / 2 ^ b.toNat)) else none
  | _ => none

/-- A 64-bit word read as a two's-complement integer. -/
def signed64 (a : Nat) : Int := if a < 2 ^ 63 then a else (a : Int) - w64

/-- A binary operator on compile-time 64-bit words. Plain and `u`-suffixed
    comparisons are unsigned and `s`-suffixed ones signed, `/` and `%` are
    unsigned, and shift counts are taken modulo 64. -/
def wordBin (op : String) (a b : Nat) : Option V :=
  match op with
  | "+" => some (.cw ((a + b) % w64))
  | "-" => some (.cw ((a + w64 - b % w64) % w64))
  | "*" => some (.cw ((a * b) % w64))
  | "/" => if b == 0 then none else some (.cw (a / b))
  | "%" => if b == 0 then none else some (.cw (a % b))
  | "&" => some (.cw (a &&& b))
  | "|" => some (.cw (a ||| b))
  | "^" => some (.cw (a ^^^ b))
  | "<<" => some (.cw ((a <<< (b % 64)) % w64))
  | ">>" => some (.cw (a >>> (b % 64)))
  | ">>s" => some (.cw (toW (signed64 a / 2 ^ (b % 64))))
  | "==" => some (ofBool (a == b))
  | "!=" => some (ofBool (a != b))
  | "<" | "<u" => some (ofBool (a < b))
  | "<=" | "<=u" => some (ofBool (a ≤ b))
  | ">" | ">u" => some (ofBool (a > b))
  | ">=" | ">=u" => some (ofBool (a ≥ b))
  | "<s" => some (ofBool (signed64 a < signed64 b))
  | "<=s" => some (ofBool (signed64 a ≤ signed64 b))
  | ">s" => some (ofBool (signed64 a > signed64 b))
  | ">=s" => some (ofBool (signed64 a ≥ signed64 b))
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

/-- The number of trailing zero bits of a 64-bit word, `64` for zero. -/
def ctz64 (n : Nat) : Nat :=
  ((List.range 64).find? (fun i => n / 2 ^ i % 2 == 1)).getD 64

/-- A compile-time value as a signed byte displacement. -/
def constDisp? : V → Option Int
  | .int n => some n
  | .cw n => some (signed64 n)
  | _ => none

/-- The known alignment exponent of a word value: `ctz64` of a compile-time
    word, the recorded exponent of a run-time word, `0` when unknown. -/
def alignOf (v : V) : M Nat := do
  match v with
  | .w x => return ((← get).aligns.lookup x).getD 0
  | .int n => return ctz64 (toW n)
  | .cw n => return ctz64 n
  | _ => return 0

/-- Record that the run-time word `x` is a multiple of `2 ^ a`. -/
def setAlign (x : String) (a : Nat) : M Unit :=
  if a == 0 then pure () else modify fun s => { s with aligns := (x, min a 64) :: s.aligns }

/-- The address a word value points to, if any. -/
def addrOfV : V → M (Option Addr)
  | .w x => return (← get).addrs.lookup x
  | _ => return none

/-- Record the address of the run-time word `x`. -/
def setAddr (x : String) (a : Addr) : M Unit :=
  modify fun s => { s with addrs := (x, a) :: s.addrs }

/-- Emit `t = a op b` for a run-time word `a`, returning `t`. -/
def emitOp (k : BinKind) (a : String) (b : Operand) : M String := do
  let t ← fresh
  emit (.assign t (.bin k a b))
  pure t

/-- `A + v` for an address `A` and a non-address word `v`: a compile-time `v`
    moves the byte offset, a run-time `v` joins the run-time part. -/
def addrPlus (A : Addr) (v : V) : M Addr := do
  match constDisp? v with
  | some k => return { A with off := A.off + k }
  | none =>
      match v with
      | .w y =>
          match A.rt with
          | none => return { A with rt := some y }
          | some r =>
              let r' ← emitOp .add r (.var y)
              setAlign r' (min (← alignOf (.w r)) (← alignOf (.w y)))
              return { A with rt := some r' }
      | _ => throw s!"eval: pointer arithmetic with {repr v}"

/-- Record the address and the alignment of the emitted `t = a op b`. -/
def noteArith (op : String) (a b : V) (t : String) : M Unit := do
  match op with
  | "+" =>
      match ← addrOfV a, ← addrOfV b with
      | some A, none => setAddr t (← addrPlus A b)
      | none, some B => setAddr t (← addrPlus B a)
      | _, _ => pure ()
  | "-" =>
      match ← addrOfV a, constDisp? b with
      | some A, some k => setAddr t { A with off := A.off - k }
      | _, _ => pure ()
  | _ => pure ()
  let aa ← alignOf a
  let ab ← alignOf b
  let al : Nat := match op, constWord? b with
    | "*", _ => aa + ab
    | "<<", some k => aa + k
    | "+", _ | "-", _ => min aa ab
    | "&", _ => max aa ab
    | _, _ => 0
  setAlign t al

/-- The magic multiplier and shift of unsigned 64-bit division by a constant
    `d` that is not a power of two (Granlund and Montgomery, Fig. 4.1):
    `l = ⌈log₂ d⌉` and `m = ⌊2⁶⁴ (2ˡ - d) / d⌋ + 1`, so that with
    `t = ⌊m x / 2⁶⁴⌋` the quotient `⌊x / d⌋` is `(t + ((x - t) >>> 1)) >>> (l - 1)`. -/
def divMagic (d : Nat) : Nat × Nat :=
  let l := Nat.log2 (d - 1) + 1
  (w64 * (2 ^ l - d) / d + 1, l)

/-- `⌊m x / 2⁶⁴⌋` for a run-time word `x` and a compile-time `m < 2⁶⁴`, from
    the four 32 × 32-bit partial products. -/
def mulhiConst (x : String) (m : Nat) : M String := do
  let lo32 (y : String) : M String := do emitOp .shr (← emitOp .shl y (.lit 32)) (.lit 32)
  let xl ← lo32 x
  let xh ← emitOp .shr x (.lit 32)
  let ml := m % 2 ^ 32
  let mh := m / 2 ^ 32
  let p0 ← emitOp .mul xl (.lit ml)
  let p1 ← emitOp .mul xh (.lit ml)
  let p2 ← emitOp .mul xl (.lit mh)
  let p3 ← emitOp .mul xh (.lit mh)
  let mid ← emitOp .add (← emitOp .shr p0 (.lit 32)) (.var (← lo32 p1))
  let mid ← emitOp .add mid (.var (← lo32 p2))
  let hi ← emitOp .add p3 (.var (← emitOp .shr p1 (.lit 32)))
  let hi ← emitOp .add hi (.var (← emitOp .shr p2 (.lit 32)))
  emitOp .add hi (.var (← emitOp .shr mid (.lit 32)))

/-- `x / d` or `x % d` for a run-time word `x` and a compile-time `d > 0`: a
    shift or a mask for a power of two, `divMagic` otherwise. -/
def divModConst (op : String) (x : String) (d : Nat) : M V := do
  if d == 0 then throw "eval: division by zero"
  if 2 ^ d.log2 == d then
    if op == "/" then return .w (← emitOp .shr x (.lit d.log2))
    else return .w (← emitOp .and x (.lit (d - 1)))
  let (m, l) := divMagic d
  let t ← mulhiConst x m
  let u ← emitOp .shr (← emitOp .sub x (.var t)) (.lit 1)
  let q ← emitOp .shr (← emitOp .add u (.var t)) (.lit (l - 1))
  if op == "/" then return .w q
  let qd ← emitOp .mul q (.lit d)
  return .w (← emitOp .sub x (.var qd))

/-- The name holding the base address of the global table `nm` of `cells` cells
    of `w` bits, whose 64-bit words are `words`, binding it on first use as
    `b = @nm` (`Rhs.glob` of the `@`-prefixed symbol). Inside a rolled loop body
    the binding goes to the statements placed ahead of the loop. The table joins
    the tables read at a run-time index. -/
def globBaseW (nm : String) (w : Nat) (words : List Nat) (cells : Nat) : M String := do
  match (← get).gbases.lookup nm with
  | some b => pure b
  | none =>
      let b := "%g" ++ nm
      let st : Stmt := .assign b (.glob ("@" ++ nm))
      modify fun s =>
        { s with gbases := (nm, b) :: s.gbases, adecls := s.adecls.push (b, cells),
                 tables := if s.tables.any (·.1 == nm) then s.tables
                           else s.tables.push (nm, words) }
      setWidth b w
      if (← get).inBody then modify fun s => { s with hoist := s.hoist.push st }
      else emit st
      pure b

/-- The name holding the base address of the global table `nm` of 64-bit words
    `els` (`globBaseW`). -/
def globBase (nm : String) (els : Array Nat) : M String :=
  globBaseW nm 64 els.toList els.size

/-- A name holding the compile-time `w`-bit word `n`: cell `0` of the one-cell
    `.rodata` table `jinc_c{w}_{n in base 16}`, loaded once per loop body or
    function body. Only under `importFunRolled`, whose rendering carries the
    tables. -/
def vecConstName (w n : Nat) : M String := do
  match (← get).vcs.lookup (w, n) with
  | some t => pure t
  | none =>
      unless (← get).roll do throw s!"eval: a u{w} constant outside importFunRolled"
      let sym := "jinc_c" ++ toString w ++ "_" ++ String.ofList (Nat.toDigits 16 n)
      let b ← globBaseW sym w (limbs64 w n) 1
      let t ← fresh
      emit (.assign kiName (.imm 0))
      emit (.assign t (.load b kiName))
      modify fun s => { s with vcs := ((w, n), t) :: s.vcs }
      pure t

/-- A name holding the `w`-bit vector word `v`. -/
def vecName (w : Nat) : V → M String
  | .vw w' x => if w' == w then pure x else throw s!"eval: u{w'} word where u{w} is expected"
  | .vc w' n => if w' == w then vecConstName w n
      else throw s!"eval: u{w'} word where u{w} is expected"
  | v => throw s!"eval: expected a u{w} vector word, got {repr v}"

/-- Emit `t = op(args)` for the 256-bit op `op`, returning `t`. -/
def emitYmm (op : YmmOp) (args : List V) : M V := do
  let ns ← args.mapM (vecName 256)
  let t ← fresh
  emit (.assign t (.ymm op ns))
  pure (.vw 256 t)

/-- The 256-bit op of a source operator on vector words: `^`, `|` and `&` at any
    annotation, and `+` and `-` with the lane annotation `4u64`, `8u32` or
    `16u16`. -/
def vecBinOp? (base ann : String) : Option YmmOp :=
  match base, ann with
  | "^", _ => some .vpxor
  | "|", _ => some .vpor
  | "&", _ => some .vpand
  | "+", "4u64" => some .vpaddq
  | "+", "8u32" => some .vpaddd
  | "+", "16u16" => some .vpaddw
  | "-", "4u64" => some .vpsubq
  | "-", "8u32" => some .vpsubd
  | "-", "16u16" => some .vpsubw
  | "<<", "4u64" => some .vpsllvq
  | ">>", "4u64" => some .vpsrlvq
  | "<<", "8u32" => some .vpsllvd
  | ">>", "8u32" => some .vpsrlvd
  | _, _ => none

/-- The 256-bit op of a lane-annotated shift of a vector word by a compile-time
    count. -/
def vecShiftImm? (base ann : String) : Option (Nat → YmmOp) :=
  match base, ann with
  | "<<", "4u64" => some .vpsllq
  | ">>", "4u64" => some .vpsrlq
  | "<<", "8u32" => some .vpslld
  | ">>", "8u32" => some .vpsrld
  | ">>s", "8u32" => some .vpsrad
  | "<<", "16u16" => some .vpsllw
  | ">>", "16u16" => some .vpsrlw
  | ">>s", "16u16" => some .vpsraw
  | _, _ => none

/-- A binary operator on vector words: the bitwise operators folded on two
    compile-time words, a lane shift by a compile-time count an immediate shift,
    every other application emitted as its 256-bit op. -/
def vecBin (op base ann : String) (a b : V) : M V := do
  if let (some mk, some c) := (vecShiftImm? base ann, constWord? b) then
    return ← emitYmm (mk c) [a]
  let some k := vecBinOp? base ann | throw s!"eval: '{op}' on a vector word"
  match a, b with
  | .vc w x, .vc w' y =>
      if w == w' && base == "^" then pure (.vc w (x ^^^ y))
      else if w == w' && base == "|" then pure (.vc w (x ||| y))
      else if w == w' && base == "&" then pure (.vc w (x &&& y))
      else emitYmm k [a, b]
  | _, _ => emitYmm k [a, b]

/-- `#VPBROADCAST_4u64` of a compile-time 64-bit word: the compile-time 256-bit
    word with it in each lane. -/
def bcast64V (v : V) : M V :=
  match constWord? v with
  | some n => pure (.vc 256 (bcast4u64 n))
  | none => throw s!"eval: broadcast of the run-time word {repr v}"

/-- The value of the pack `(kuW)[e₁, …, eₖ]` of the `w`-bit lanes `lanes`:
    the first lane is the most significant, as Jasmin writes packs, so
    `(4u2)[2,1,0,3]` is `0b10_01_00_11`. -/
def packLanes (w : Nat) (lanes : List Nat) : Nat :=
  lanes.foldl (fun acc e => acc * 2 ^ w + e % 2 ^ w) 0

/-- A compile-time pack of `n` bits: a word up to 64 bits, a vector word above. -/
def packV (n v : Nat) : V := if n ≤ 64 then .cw v else .vc n v

/-- The 256-bit word with the compile-time `w`-bit value `v` in each of its
    `256 / w` lanes (`#VPBROADCAST_8u32`, `#VPBROADCAST_16u16`,
    `#VPBROADCAST_2u128`). -/
def bcastV (w : Nat) (v : V) : M V := do
  let some n := (match v with
    | .vc _ n => some n
    | v => constWord? v) | throw s!"eval: broadcast of the run-time value {repr v}"
  let x := n % 2 ^ w
  pure (.vc 256 ((List.range (256 / w)).foldl (fun acc i => acc + x * 2 ^ (w * i)) 0))

/-- The two-operand 256-bit intrinsics and their ops. -/
def ymmBinIntrinsic? : String → Option YmmOp
  | "#VPAND_256" => some .vpand
  | "#VPANDN_256" => some .vpandn
  | "#VPOR_256" => some .vpor
  | "#VPXOR_256" => some .vpxor
  | "#VPSHUFB_256" => some .vpshufb
  | "#VPADD_4u64" => some .vpaddq
  | "#VPSUB_4u64" => some .vpsubq
  | "#VPADD_8u32" => some .vpaddd
  | "#VPSUB_8u32" => some .vpsubd
  | "#VPADD_16u16" => some .vpaddw
  | "#VPSUB_16u16" => some .vpsubw
  | "#VPMULL_16u16" => some .vpmullw
  | "#VPMULH_16u16" => some .vpmulhw
  | "#VPMULL_8u32" => some .vpmulld
  | "#VPMADDWD_256" => some .vpmaddwd
  | "#VPUNPCKL_4u64" => some .vpunpcklqdq
  | "#VPUNPCKH_4u64" => some .vpunpckhqdq
  | "#VPUNPCKL_8u32" => some .vpunpckldq
  | "#VPUNPCKH_8u32" => some .vpunpckhdq
  | "#VPSLLV_4u64" => some .vpsllvq
  | "#VPSRLV_4u64" => some .vpsrlvq
  | "#VPSLLV_8u32" => some .vpsllvd
  | "#VPSRLV_8u32" => some .vpsrlvd
  | "#VPMUL_4u64" => some .vpmuldq
  | "#VPMULU_4u64" => some .vpmuludq
  | "#VPCMPGT_16u16" => some .vpcmpgtw
  | "#VPCMPGT_8u32" => some .vpcmpgtd
  | "#VPCMPEQ_8u32" => some .vpcmpeqd
  | "#VPACKSS_16u16" => some .vpacksswb
  | "#VPACKSS_8u32" => some .vpackssdw
  | "#VPERMD" => some .vpermd
  | "#VPSIGN_8u32" => some .vpsignd
  | "#VPMULHRS_16u16" => some .vpmulhrsw
  | "#VPMADDUBSW_256" => some .vpmaddubsw
  | "#VPACKUS_16u16" => some .vpackuswb
  | "#VPACKUS_8u32" => some .vpackusdw
  | "#VPADD_32u8" => some .vpaddb
  | "#VPSUB_32u8" => some .vpsubb
  | "#VPUNPCKL_32u8" => some .vpunpcklbw
  | "#VPUNPCKH_32u8" => some .vpunpckhbw
  | "#VPUNPCKL_16u16" => some .vpunpcklwd
  | "#VPUNPCKH_16u16" => some .vpunpckhwd
  | _ => none

/-- The one-operand 256-bit intrinsics without an immediate, and their ops. -/
def ymmUnIntrinsic? : String → Option YmmOp
  | "#VMOVSLDUP_256" => some .vmovsldup
  | "#VMOVSHDUP_256" => some .vmovshdup
  | "#VPABS_8u32" => some .vpabsd
  | _ => none

/-- The one-operand 256-bit intrinsics with an immediate, and their ops. -/
def ymmImmIntrinsic? : String → Option (Nat → YmmOp)
  | "#VPSLL_4u64" => some .vpsllq
  | "#VPSRL_4u64" => some .vpsrlq
  | "#VPSLL_8u32" => some .vpslld
  | "#VPSRL_8u32" => some .vpsrld
  | "#VPSRA_8u32" => some .vpsrad
  | "#VPSLL_16u16" => some .vpsllw
  | "#VPSRL_16u16" => some .vpsrlw
  | "#VPSRA_16u16" => some .vpsraw
  | "#VPERMQ" => some .vpermq
  | "#VPSHUFD_256" => some .vpshufd
  | "#VPSRLDQ_256" => some .vpsrldq
  | "#VPSLLDQ_256" => some .vpslldq
  | _ => none

/-- The two-operand 256-bit intrinsics with an immediate, and their ops. -/
def ymmBinImmIntrinsic? : String → Option (Nat → YmmOp)
  | "#VPERM2I128" => some .vperm2i128
  | "#VPBLEND_8u32" => some .vpblendd
  | "#VPBLEND_16u16" => some .vpblendw
  | _ => none

/-- A binary operator applied to two values: folded when both are compile-time,
    emitted otherwise. A narrow word is rejected as an operand; an operator on a
    vector word is `vecBin`, and a width annotation on a scalar operator must be
    `64u` or `64s`. -/
def binV (op0 : String) (a b : V) : M V := do
  let (op, ann) := splitOp op0
  if isVec a || isVec b then return ← vecBin op0 op ann a b
  unless ann.isEmpty || ann == "64u" || ann == "64s" do
    throw s!"eval: '{op0}' on 64-bit words"
  match a, b with
  | .nw _ _, _ | _, .nw _ _ => throw s!"eval: '{op}' on a narrow word"
  | .int x, .int y =>
      match intBin op x y with
      | some v => pure v
      | none => throw s!"eval: cannot fold {x} {op} {y}"
  | .w x, _ =>
      if op == "/" || op == "%" then
        match constWord? b with
        | some d => return ← divModConst op x d
        | none => throw s!"eval: '{op}' by a run-time word"
      let some k := binKind? op | throw s!"eval: '{op}' on a run-time word"
      let t ← fresh
      emit (.assign t (.bin k x (← operandOf b)))
      noteArith op a b t
      pure (.w t)
  | _, .w y =>
      let some k := binKind? op | throw s!"eval: '{op}' on a run-time word"
      let t ← fresh
      if commutes k then
        emit (.assign t (.bin k y (← operandOf a)))
      else
        let x ← wordName a
        emit (.assign t (.bin k x (.var y)))
      noteArith op a b t
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
  | .vword w, .vw w' x =>
      if w == w' then pure (.vw w x) else throw s!"eval: cannot store {repr v} in a {repr k}"
  | .vword w, .vc w' n =>
      if w == w' then pure (.vc w n) else throw s!"eval: cannot store {repr v} in a {repr k}"
  | .vword w, .int n => pure (.vc w (n % (2 ^ w : Nat)).toNat)
  | .vword w, .cw n => pure (.vc w n)
  | _, _ => throw s!"eval: cannot store {repr v} in a {repr k}"

/-- A cell value: words only, an integer taken as a word. -/
def cellVal : V → M V
  | .int n => pure (.cw (toW n))
  | .cw n => pure (.cw n)
  | .w x => pure (.w x)
  | .vw w x => pure (.vw w x)
  | .vc w n => pure (.vc w n)
  | v => throw s!"eval: cannot store {repr v} in an array cell"

/-- The kind of a declared type; words and arrays are 64-bit or 256-bit. -/
def kindOf : Ty → M Kind
  | .int => pure .int
  | .word 64 => pure .word
  | .word 256 => pure (.vword 256)
  | .arr 8 _ | .arr 16 _ | .arr 32 _ | .arr 64 _ | .arr 256 _ => pure .arr
  | ty => throw s!"eval: unsupported type {repr ty} (words are 64-bit or 256-bit)"

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
      if (← cellWidth nm) < 64 then throw s!"eval: read of a narrow cell of {nm}"
      let t ← fresh
      emit (.assign kiName (.imm k))
      emit (.assign t (.load nm kiName))
      let w ← cellWidth nm
      pure (if w == 64 then .w t else .vw w t)
  | .gtab nm els =>
      match els[k]? with
      | some x => pure (.cw x)
      | none => throw s!"eval: index {k} out of bounds of {nm}"
  | v => throw s!"eval: indexing {repr v}"

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
  if (← cellWidth src) < 64 then throw s!"eval: read of a narrow cell of {src}"
  let t ← fresh
  emit (.assign t (.load src x))
  let w ← cellWidth src
  pure (if w == 64 then .w t else .vw w t)

/-- A name holding `v` for a store into a cell of the array `arr`: a 64-bit word
    for an array of 64-bit cells, a vector word otherwise. -/
def cellName (arr : String) (v : V) : M String := do
  let w ← cellWidth arr
  if w == 64 then wordName v else vecName w v

/-! ## 5. Memory words and array views -/

/-- The nominal cell count of a memory view: the extent of a buffer whose
    length is a run-time value. -/
def viewCells : Nat := 2 ^ 32

/-- The name of the `w`-bit memory view of the pointer parameter `base`,
    recorded on first use. -/
def viewOf (base : String) (w : Nat) : M String := do
  let nm := base ++ "@" ++ toString w
  unless (← get).views.contains (base, w) do
    modify fun s => { s with views := s.views.push (base, w) }
  pure nm

/-- `x >>> k` for a run-time word `x`, emitted once per `(x, k)` within a loop
    body or the function body. -/
def shrOnce (x : String) (k : Nat) : M String := do
  if k == 0 then return x
  match (← get).shrs.lookup (x, k) with
  | some t => pure t
  | none =>
      let t ← emitOp .shr x (.lit k)
      modify fun s => { s with shrs := ((x, k), t) :: s.shrs }
      pure t

/-- The `w`-bit view and the cell index of the memory word at the address `va`:
    a compile-time index when the address has no run-time part, a run-time word
    otherwise. The byte offset must be a multiple of `w / 8`. -/
def memAt (w : Nat) (va : V) : M (String × V) := do
  unless w == 8 || w == 16 || w == 32 || w == 64 do throw s!"eval: memory access of width {w}"
  let x ← match va with
    | .w x => pure x
    | v => throw s!"eval: memory address {repr v} is not a pointer"
  let some A ← addrOfV (.w x) | throw s!"eval: memory address '{x}' has no pointer base"
  let vn ← viewOf A.base w
  let scale : Nat := w / 8
  unless A.off % (scale : Int) == 0 do
    throw s!"eval: byte offset {A.off} of a u{w} access into '{A.base}' is unaligned"
  let k := A.off / (scale : Int)
  match A.rt with
  | none =>
      unless k ≥ 0 do throw s!"eval: negative offset into '{A.base}'"
      pure (vn, .int k)
  | some r =>
      let lg := scale.log2
      unless (← alignOf (.w r)) ≥ lg do
        throw s!"eval: run-time offset of a u{w} access into '{A.base}' is not known aligned"
      let ri ← shrOnce r lg
      if k == 0 then pure (vn, .w ri)
      else pure (vn, .w (← emitOp .add ri (.lit (toW k))))

/-- Read cell `idx` of the view `vn`: a 64-bit `load`, or a zero-extending
    `castLoad` of a narrow cell. -/
def viewLoad (w : Nat) (vn : String) (idx : V) : M V := do
  let i ← match idx with
    | .w i => pure i
    | v => do
        emit (.assign kiName (.imm (← constNat v)))
        pure kiName
  let t ← fresh
  if w == 64 then emit (.assign t (.load vn i))
  else emit (.assign t (.castLoad 64 vn i))
  pure (.w t)

/-- Store the word `v` into cell `idx` of the `w`-bit view `vn`; a narrow store
    writes the low `w` bits of a narrow or compile-time value. -/
def viewStore (w : Nat) (vn : String) (idx : V) (v : V) : M Unit := do
  let y ← match v with
    | .nw w' y => if w' ≤ w then pure y else throw s!"eval: u{w'} value in a u{w} cell"
    | .w y => if w == 64 then pure y else throw s!"eval: u64 value in a u{w} cell"
    | v => wordName v
  let rhs : Rhs := if w == 64 then .glob y else .cast w y
  match idx with
  | .w i => emit (.storeAt vn (.var i) rhs)
  | v =>
      let k ← constNat v
      if w == 64 then emit (.store vn k y) else emit (.storeAt vn (.lit k) rhs)

/-- The `w`-bit view of the memory array `nm` and the cell index of the byte
    offset `off` in it: a compile-time index, or a run-time word for a run-time
    offset known to be a multiple of `w / 8`. -/
def memView (nm : String) (w : Nat) (off : V) : M (String × V) := do
  let vn ← viewOf nm w
  setWidth vn w
  let scale : Nat := w / 8
  match off with
  | .w x =>
      unless (← alignOf (.w x)) ≥ scale.log2 do
        throw s!"eval: run-time offset of a u{w} view of '{nm}' is not known aligned"
      pure (vn, .w (← shrOnce x scale.log2))
  | o =>
      let k ← constNat o
      unless k % scale == 0 do throw s!"eval: byte offset {k} of a u{w} view is unaligned"
      pure (vn, .int (k / scale))

/-- Read cell `idx` of the `w`-bit view `vn`: `viewLoad` for a word, a vector
    `load` for `w > 64`. -/
def viewLoadAny (w : Nat) (vn : String) (idx : V) : M V := do
  if w ≤ 64 then return ← viewLoad w vn idx
  let i ← match idx with
    | .w i => pure i
    | v => do
        emit (.assign kiName (.imm (← constNat v)))
        pure kiName
  let t ← fresh
  emit (.assign t (.load vn i))
  pure (.vw w t)

/-- Store `v` into cell `idx` of the `w`-bit view `vn`: `viewStore` for a word,
    a vector store for `w > 64`. -/
def viewStoreAny (w : Nat) (vn : String) (idx : V) (v : V) : M Unit := do
  if w ≤ 64 then return ← viewStore w vn idx v
  let y ← vecName w v
  match idx with
  | .w i => emit (.storeAt vn (.var i) (.glob y))
  | k => emit (.store vn (← constNat k) y)

/-- The `w`-bit field at byte offset `off` of the global table `nm` of
    `cw`-bit cells `els`, stored little-endian: a compile-time word (`w ≤ 64`)
    or vector word at a compile-time offset; at a run-time offset, a multiple of
    `w / 8`, a `load` from the `.rodata` table `nm_u{w}` of the same bytes in
    `w`-bit cells (`w ≥ 64`, only under `importFunRolled`). -/
def gtabView (nm : String) (cw : Nat) (els : Array Nat) (w : Nat) (off : V) : M V := do
  let big : Nat := (els.toList.zip (List.range els.size)).foldl
    (fun acc (e, i) => acc + e % 2 ^ cw * 2 ^ (cw * i)) 0
  match off with
  | .w x =>
      unless (← get).roll do throw s!"eval: run-time index into the global table {nm}"
      unless w ≥ 64 do throw s!"eval: run-time u{w} view of the global table {nm}"
      unless (← alignOf (.w x)) ≥ (w / 8).log2 do
        throw s!"eval: run-time offset of a u{w} view of {nm} is not known aligned"
      let cells := els.size * cw / w
      let words := (List.range cells).flatMap fun j => limbs64 w (big / 2 ^ (w * j) % 2 ^ w)
      let b ← globBaseW (nm ++ "_u" ++ toString w) w words cells
      let i ← shrOnce x (w / 8).log2
      let t ← fresh
      emit (.assign t (.load b i))
      pure (if w == 64 then .w t else .vw w t)
  | o =>
      let k ← constNat o
      let v := big / 2 ^ (8 * k) % 2 ^ w
      pure (if w ≤ 64 then .cw v else .vc w v)

/-- Whether the `w`-bit field of the array value `av` is read or written through
    a view: `av` is a memory array whose cells are not 64-bit, or `w > 64`. -/
def viaView (av : V) (w : Nat) : M (Option String) := do
  match av with
  | .mem nm _ => if w > 64 || (← cellWidth nm) != 64 then pure (some nm) else pure none
  | _ => pure none

/-- The zero-extended `w`-bit field at byte offset `off` of an array of 64-bit
    cells: cell `off / 8`, shifted right by `8 (off mod 8)` and masked. A field of
    a memory array of other cells, or wider than 64 bits, is cell `off / (w / 8)`
    of the `w`-bit view of the array (`memView`). -/
def fieldRead (av : V) (w : Nat) (off : V) : M V := do
  if let some nm ← viaView av w then
    let (vn, idx) ← memView nm w off
    return ← viewLoadAny w vn idx
  if w > 64 then throw s!"eval: u{w} view of {repr av}"
  let mask : Nat := 2 ^ w - 1
  match off with
  | .w x =>
      unless (← alignOf (.w x)) ≥ (w / 8).log2 do
        throw s!"eval: run-time offset of a u{w} view is not known aligned"
      let cell ← readCellAt av (← shrOnce x 3)
      if w == 64 then return cell
      let sh ← binV "<<" (← binV "&" (.w x) (.cw 7)) (.cw 3)
      binV "&" (← binV ">>" cell sh) (.cw mask)
  | v =>
      let k ← constNat v
      unless k % (w / 8) == 0 do throw s!"eval: byte offset {k} of a u{w} view is unaligned"
      let cell ← readCell av (k / 8)
      if w == 64 then return cell
      binV "&" (← binV ">>" cell (.cw (8 * (k % 8)))) (.cw mask)

/-- The `w`-bit field at byte offset `off` of the array `a` of `p` holding
    `av`: `gtabView` for a global table of other than 64-bit cells or a field of
    other than 64 bits, `fieldRead` otherwise. -/
def readField (p : Prog) (a : String) (av : V) (w : Nat) (off : V) : M V := do
  match av with
  | .gtab nm els =>
      let cw := (p.globWidths.lookup a).getD 64
      if cw != 64 || w != 64 then gtabView nm cw els w off else fieldRead av w off
  | _ => fieldRead av w off

/-! ## 6. Evaluator -/

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
  | .nw _ _ => false
  | .vw _ _ => false
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

/-- A statement list less each assignment to a name no later statement reads; a
    call is kept. -/
def dropDead (ss : Array Stmt) : Array Stmt :=
  (ss.foldr (fun s (acc, live) =>
    let keep := match s with
      | .assign _ (.call _ _) => true
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

/-- The compound operators whose low `w` bits depend only on the low `w` bits of
    their operands: the ones a compound assignment to a narrow field applies. -/
def lowBitsOp (op : String) : Bool :=
  ["+", "-", "*", "&", "|", "^", "<<"].contains op

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

/-- The value of an expression, emitting the statements of its run-time part. A
    narrow memory word or view field is read only under a `(64u)` cast, which
    zero-extends it; a cast to `u8`, `u16` or `u32` masks. -/
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
      | .vw 256 _ => emitYmm .vpandn [va, vb]
      | _ => binV "&" (← notV va) vb
  | .bin "&" b (.not a) => do
      let vb ← evalE p env b
      let va ← evalE p env a
      match va with
      | .w x => andnV x vb
      | .vw 256 _ => emitYmm .vpandn [va, vb]
      | _ => binV "&" vb (← notV va)
  | .bin op a b => do
      let va ← evalE p env a
      let vb ← evalE p env b
      binV op va vb
  | .neg a => do negV (← evalE p env a)
  | .not a => do notV (← evalE p env a)
  | .mem w a => do
      unless w == 64 do throw s!"eval: u{w} memory read outside a (64u) cast"
      let (vn, idx) ← memAt w (← evalE p env a)
      viewLoad w vn idx
  | .view a w off => do
      let av ← lookupVar p env a
      unless w == 64 || w == 128 || w == 256 || (match av with | .gtab _ _ => true | _ => false) do
        throw s!"eval: u{w} view read outside a (64u) cast"
      readField p a av w (← evalE p env off)
  | .cast w a => do
      if w == 64 then
        match a with
        | .mem mw ad =>
            let (vn, idx) ← memAt mw (← evalE p env ad)
            viewLoad mw vn idx
        | .view arr vw off => readField p arr (← lookupVar p env arr) vw (← evalE p env off)
        | _ =>
            match ← evalE p env a with
            | .int n => pure (.cw (toW n))
            | .nw _ x => pure (.w x)
            | v => pure v
      else if w == 8 || w == 16 || w == 32 then
        let mask : Nat := 2 ^ w - 1
        match ← evalE p env a with
        | .int n => pure (.cw (toW n % 2 ^ w))
        | .cw n => pure (.cw (n % 2 ^ w))
        | .w x => pure (.nw w (← emitOp .and x (.lit mask)))
        | .nw w' x =>
            if w' ≤ w then pure (.nw w' x) else pure (.nw w (← emitOp .and x (.lit mask)))
        | v => throw s!"eval: cast to u{w} of {repr v}"
      else if w == 128 || w == 256 then
        match ← evalE p env a with
        | .int n => pure (.vc w (n % (2 ^ w : Nat)).toNat)
        | .cw n => pure (.vc w n)
        | .vc _ n => pure (.vc w (n % 2 ^ w))
        | .vw w' x =>
            if w' == w then pure (.vw w x) else throw s!"eval: cast of a u{w'} word to u{w}"
        | v => throw s!"eval: cast to u{w} of {repr v}"
      else throw s!"eval: cast to u{w}"
  | .cond c t f => do
      match truth? (← evalE p env c) with
      | some true => evalE p env t
      | some false => evalE p env f
      | none => throw "eval: data-dependent '?:'"
  | .slice a w o n => do
      unless w == 0 do throw s!"eval: u{w} slice of '{a}'"
      let off ← constNat (← evalE p env o)
      let len ← constNat (← evalE p env n)
      match ← lookupVar p env a with
      | .ra els =>
          unless off + len ≤ els.size do throw s!"eval: slice of '{a}' out of bounds"
          pure (.ra (els.extract off (off + len)))
      | .gtab _ els =>
          unless off + len ≤ els.size do throw s!"eval: slice of '{a}' out of bounds"
          pure (.ra ((els.extract off (off + len)).map V.cw))
      | v => throw s!"eval: slice of '{a}', which holds {repr v}"

/-- The results of a call: an intrinsic, a call kept as a call, or an inlined
    source function. `#VPBROADCAST_4u64(T[i])` of a global table `T` at a
    run-time index `i` is a `load` of cell `i` of the table `T_bcast4u64`, whose
    cell `k` holds word `k` of `T` in each of its four lanes. -/
partial def evalCall (p : Prog) (env : Env) (f : String) (args : List E) : M (List V) := do
  if f == "#VPBROADCAST_4u64" then
    let [arg] := args | throw s!"eval: '{f}' takes one argument"
    match arg with
    | .idx a i =>
        let av ← lookupVar p env a
        match av, ← evalE p env i with
        | .gtab nm els, .w x =>
            unless (← get).roll do throw s!"eval: run-time index into the global table {nm}"
            let b ← globBaseW (nm ++ "_bcast4u64") 256
              (els.toList.flatMap fun e => [e, e, e, e]) els.size
            let t ← fresh
            emit (.assign t (.load b x))
            return [.vw 256 t]
        | _, .w x => return [← bcast64V (← readCellAt av x)]
        | _, vi => return [← bcast64V (← readCell av (← constNat vi))]
    | e => return [← bcast64V (← evalE p env e)]
  let vs ← args.mapM (evalE p env)
  if let some op := ymmBinIntrinsic? f then
    let [a, b] := vs | throw s!"eval: '{f}' takes two arguments"
    return [← emitYmm op [a, b]]
  if let some op := ymmUnIntrinsic? f then
    let [a] := vs | throw s!"eval: '{f}' takes one argument"
    return [← emitYmm op [a]]
  if let some mk := ymmImmIntrinsic? f then
    let [a, n] := vs | throw s!"eval: '{f}' takes two arguments"
    return [← emitYmm (mk (← constNat n)) [a]]
  if let some mk := ymmBinImmIntrinsic? f then
    let [a, b, n] := vs | throw s!"eval: '{f}' takes three arguments"
    return [← emitYmm (mk (← constNat n)) [a, b]]
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
  | "#pack", .int k :: .int w :: es => do
      unless es.length == k.toNat do throw s!"eval: pack of {es.length} lanes as {k}"
      let lanes ← es.mapM constNat
      pure [packV (k.toNat * w.toNat) (packLanes w.toNat lanes)]
  | "#set0_256", [] => pure [.vc 256 0]
  | "#set0_128", [] => pure [.vc 128 0]
  | "#set0", [] | "#set0_64", [] | "#set0_32", [] =>
      pure [.undef, .undef, .undef, .undef, .undef, .cw 0]
  -- the speculative-load-hardening intrinsics: outside misspeculation the
  -- misspeculation flag is `0` and `#protect` returns its argument
  | "#init_msf", [] => pure [.cw 0]
  | "#update_msf", [_, m] => pure [m]
  | "#protect", [x, _] => pure [x]
  | "#declassify", _ => pure []
  | "#VPBROADCAST_8u32", [v] => pure [← bcastV 32 v]
  | "#VPBROADCAST_16u16", [v] => pure [← bcastV 16 v]
  | "#VPBROADCAST_2u128", [v] => pure [← bcastV 128 v]
  | _, _ =>
      match p.fns.find? (·.name == f) with
      | some fn =>
          if (← get).callFns.contains fn.name then callExt fn vs else callFn p fn vs
      | none => throw s!"eval: unknown function or intrinsic '{f}' with {vs.length} arguments"

/-- A call kept as a call to the symbol `fn.name`: array arguments are passed by
    name, words by value. Every returned expression of `fn` must be one of its
    array parameters, and the call's result for it is the corresponding
    argument: the callee updates that array in place. -/
partial def callExt (fn : Fn) (vs : List V) : M (List V) := do
  unless fn.params.length == vs.length do
    throw s!"eval: '{fn.name}' takes {fn.params.length} arguments, given {vs.length}"
  let pv := fn.params.zip vs
  let args ← pv.mapM fun ((ty, _, nm), v) => do
    match ty, v with
    | .arr _ _, .mem an _ => pure an
    | .word 64, v => wordName v
    | _, _ => throw s!"eval: argument '{nm}' of the call to '{fn.name}' is {repr v}"
  let rs ← fn.ret.mapM fun e => do
    match e with
    | .var r =>
        match pv.find? (fun ((_, _, nm), _) => nm == r) with
        | some ((.arr _ _, _, _), v@(.mem _ _)) => pure v
        | _ => throw s!"eval: '{fn.name}' returns '{r}', not an array parameter"
    | _ => throw s!"eval: '{fn.name}' returns an expression, not an array parameter"
  let n ← match (rs.head? : Option V) with
    | some (.mem _ n) => pure n
    | _ => throw s!"eval: '{fn.name}' returns no array"
  let t ← fresh
  modify fun s => { s with adecls := s.adecls.push (t, n) }
  emit (.assign t (.call fn.name args))
  pure rs

/-- An inlined call: the parameters bound to the argument values in a fresh
    frame, the body run one call level deeper, the returned expressions
    evaluated. -/
partial def callFn (p : Prog) (fn : Fn) (vs : List V) : M (List V) := do
  unless fn.params.length == vs.length do
    throw s!"eval: '{fn.name}' takes {fn.params.length} arguments, given {vs.length}"
  let mut env : Env := []
  for ((ty, _, nm), v) in fn.params.zip vs do
    let k ← kindOf ty
    env := (nm, k, ← coerce k v) :: env
  modify fun s => { s with depth := s.depth + 1 }
  let env' ← execBlock p env fn.body
  let rs ← fn.ret.mapM (evalE p env')
  modify fun s => { s with depth := s.depth - 1 }
  pure rs

/-- Write the `w`-bit field at byte offset `off` of the array `a` of 64-bit
    cells: a narrow field is merged into its cell,
    `(cell & ~(mask << sh)) | ((v & mask) << sh)`. A field of a memory array of
    other cells, or wider than 64 bits, is a store into cell `off / (w / 8)` of
    the `w`-bit view of the array (`memView`). -/
partial def fieldWrite (p : Prog) (env : Env) (a : String) (w : Nat) (off v : V) : M Env := do
  if let some nm ← viaView (← lookupVar p env a) w then
    let (vn, idx) ← memView nm w off
    viewStoreAny w vn idx v
    return env
  if w > 64 then throw s!"eval: u{w} view of '{a}'"
  let mask : Nat := 2 ^ w - 1
  let (cellIdx, cell, sh) ← match off with
    | .w x => do
        unless (← alignOf (.w x)) ≥ (w / 8).log2 do
          throw s!"eval: run-time offset of a u{w} view is not known aligned"
        let wi ← shrOnce x 3
        let cell ← readCellAt (← lookupVar p env a) wi
        let sh ← binV "<<" (← binV "&" (.w x) (.cw 7)) (.cw 3)
        pure (V.w wi, cell, sh)
    | o => do
        let k ← constNat o
        unless k % (w / 8) == 0 do throw s!"eval: byte offset {k} of a u{w} view is unaligned"
        pure (V.cw (k / 8), ← readCell (← lookupVar p env a) (k / 8), V.cw (8 * (k % 8)))
  let v64 : V := match v with
    | .nw _ y => .w y
    | v => v
  let new ← if w == 64 then pure v64 else do
    let vm ← binV "<<" (← binV "&" v64 (.cw mask)) sh
    let hole ← match sh with
      | .w _ =>
          let msh ← binV "<<" (.cw mask) sh
          match msh with
          | .w m => andnV m cell
          | _ => binV "&" cell (← notV msh)
      | _ => binV "&" cell (← notV (← binV "<<" (.cw mask) sh))
    binV "|" hole vm
  match cellIdx with
  | .w wi =>
      match ← lookupVar p env a with
      | .mem nm _ =>
          let y ← wordName new
          emit (.storeAt nm (.var wi) (.glob y))
          pure env
      | _ => throw s!"eval: store into '{a}' at a run-time index"
  | ci => assignLV p env (.idx a (.num (← constNat ci))) new

/-- The frame after an assignment. -/
partial def assignLV (p : Prog) (env : Env) (lv : LV) (v : V) : M Env := do
  match lv with
  | .wild => pure env
  | .flags => pure env
  | .slice a w o n =>
      unless w == 0 do throw s!"eval: store into a u{w} slice of '{a}'"
      let off ← constNat (← evalE p env o)
      let len ← constNat (← evalE p env n)
      match env.get? a, v with
      | some (_, .ra els), .ra vs =>
          unless off + len ≤ els.size && vs.size == len do
            throw s!"eval: slice of '{a}' out of bounds"
          let els' := (List.range len).foldl (fun acc j => acc.setIfInBounds (off + j) vs[j]!) els
          pure (env.set a (.ra els'))
      | _, _ => throw s!"eval: store into the slice of '{a}' of {repr v}"
  | .var x =>
      match env.get? x with
      | some (k, _) => pure (env.set x (← coerce k v))
      | none => throw s!"eval: assignment to undeclared '{x}'"
  | .mem w a =>
      let (vn, idx) ← memAt w (← evalE p env a)
      viewStore w vn idx v
      pure env
  | .view a w off => fieldWrite p env a w (← evalE p env off) v
  | .idx a i =>
      let vi ← evalE p env i
      if let .w x := vi then
        match env.get? a with
        | some (_, .mem nm _) =>
            let y ← cellName nm v
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
          let x ← cellName nm v
          emit (.store nm k x)
          pure env
      | _ => throw s!"eval: store into '{a}', which holds no array"

/-- The frame after a statement. A `stack` array declared in the imported
    function's own body is a memory array of its frame. -/
partial def execS (p : Prog) (env : Env) : S → M Env
  | .decl ty ptr stk names => do
      let k ← kindOf ty
      let depth := (← get).depth
      let mut e := env
      for nm in names do
        let init ← match ty, ptr with
          | .arr w n, false => do
              let m ← constNat (← evalE p env n)
              if stk && depth == 0 then
                unless w == 64 do throw s!"eval: frame array '{nm}' of u{w} cells"
                modify fun s => { s with frames := s.frames.push (nm, m) }
                pure (V.mem nm m)
              else pure (V.ra (Array.replicate m .undef))
          | _, _ => pure V.undef
        e := (nm, k, init) :: e
      pure e
  | .assign lvs e => do
      let vs ← match e with
        | .call f args => evalCall p env f args
        | _ => do pure [← evalE p env e]
      if lvs.isEmpty then return env
      -- one `?{…}` destination takes every value the others leave
      let nFlags := lvs.countP (fun | .flags => true | _ => false)
      let lvs := if nFlags == 1 && lvs.length ≤ vs.length then
          lvs.flatMap fun
            | .flags => List.replicate (vs.length + 1 - lvs.length) LV.wild
            | l => [l]
        else lvs
      unless lvs.length == vs.length do
        throw s!"eval: {lvs.length} destinations for {vs.length} values"
      (lvs.zip vs).foldlM (fun en (lv, v) => assignLV p en lv v) env
  | .opAssign op (.view a w off) e => do
      unless w == 64 || lowBitsOp op do throw s!"eval: '{op}=' on a u{w} view"
      let offV ← evalE p env off
      let cur ← fieldRead (← lookupVar p env a) w offV
      let rhs ← match ← evalE p env e with
        | .nw _ y => pure (V.w y)
        | v => pure v
      fieldWrite p env a w offV (← binV op cur rhs)
  | .opAssign op lv e => do
      let cur : E := match lv with
        | .idx a i => .idx a i
        | .var x => .var x
        | .mem w a => .cast 64 (.mem w a)
        | .view a w o => .view a w o
        | .slice a w o n => .slice a w o n
        | .wild | .flags => .num 0
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
  set { s with out := #[], hoist := #[], inBody := true, shrs := [], vcs := [] }
  let env ← setup
  let env' ← execBlock p env block
  let s' ← get
  set { s' with out := s.out, hoist := s.hoist, inBody := s.inBody, shrs := s.shrs,
                vcs := s.vcs }
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

/-- The frames at the start of each trip of `while (c) { post }` unrolled, and its
    exit frame. -/
partial def whileTracePost (p : Prog) (c : E) (post : List S) (fuel : Nat) (env : Env)
    (acc : List Env) : M (List Env × Env) := do
  match truth? (← evalE p env c) with
  | some false => pure (acc.reverse, env)
  | some true =>
      if fuel == 0 then throw "eval: 'while' exceeds the unrolling bound"
      let env' ← execBlock p env post
      whileTracePost p c post (fuel - 1) env' (env :: acc)
  | none => throw "eval: data-dependent 'while' guard"

/-- `while (v < n) { body }` with `v` holding `0` and `n` a run-time word, as
    `Stmt.forRt idx n body` over a run-time trip index `idx` standing for `v`;
    `none` when the loop is not of that shape. The body must advance `v` by one
    per trip and store into exactly one array; it is evaluated as in `tryRoll`,
    and after the loop `v` holds `n` and every other name the body writes is
    unassigned. -/
partial def tryRtLoop (p : Prog) (c : E) (body : List S) (env : Env) : M (Option Env) := do
  let .bin op (.var v) bound := c | return none
  unless op == "<" || op == "<u" do return none
  let some (_, v0) := env.get? v | return none
  unless constWord? v0 == some 0 do return none
  let s0 ← get
  let n ← match ← evalE p env bound with
    | .w n => pure n
    | _ => set s0; return none
  let idx ← fresh
  let s1 ← get
  let (env1, _, _) ← rollBody p (pure (env.set v (.w idx))) body
  let d := changedNames env env1
  set s1
  let (env2, out, hoisted) ← rollBody p (pure ((undefAll env d).set v (.w idx))) body
  let step : Bool := match env2.get? v with
    | some (_, .w k) => out.any (· == .assign k (.bin .add idx (.lit 1)))
    | _ => false
  unless step do throw s!"eval: the counter '{v}' of a run-time loop must advance by one per trip"
  unless (storedArrays out).length == 1 do
    throw "eval: a run-time loop body stores into other than one array"
  hoisted.forM emit
  emit (.forRt idx n (dropDead out).toList)
  return some ((undefAll env d).set v (.w n))

/-- The frame after `while { pre } (c) { post }`. Under `importFunRolled` a loop
    of the `tryRtLoop` shape is a run-time loop. Otherwise, with one of `pre` and
    `post` empty, a loop whose unrolling is `rollable` and whose trips advance
    one compile-time counter by a fixed step (`affineCounter`) is kept rolled
    when `tryRoll` succeeds, a trip being the non-empty block; every other loop is
    unrolled. -/
partial def whileStmt (p : Prog) (pre : List S) (c : E) (post : List S) (env : Env) :
    M Env := do
  let s0 ← get
  if s0.roll && !s0.inBody && pre.isEmpty then
    if let some env' ← tryRtLoop p c post env then return env'
  if !s0.roll || s0.inBody || !(post.isEmpty || pre.isEmpty) then
    return ← whileLoop p pre c post whileFuel env
  let (block, (starts, envU)) ← if post.isEmpty then
      do pure (pre, ← whileTrace p pre c whileFuel env [])
    else do pure (post, ← whileTracePost p c post whileFuel env [])
  let s1 ← get
  let n := starts.length
  if !rollable n (s1.out.size - s0.out.size) then return envU
  match affineCounter starts with
  | some (x, c0, st) =>
      tryCatch (do set s0; tryRoll p n x c0 st block env envU) (fun _ => pure envU)
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

/-! ## 7. Import -/

/-- Evaluate `fn` over its parameters: a `reg ptr` array of 64-bit or 256-bit
    cells is a memory array named by the parameter, a `reg u64` a run-time word
    that may serve as a pointer. Returns the `JFun` parameters and the returned
    values. -/
def importFnM (p : Prog) (fn : Fn) : M (List Param × List V) := do
  let mut env : Env := []
  let mut params : Array Param := #[]
  for (ty, _, nm) in fn.params do
    match ty with
    | .arr w n =>
        unless w == 8 || w == 16 || w == 32 || w == 64 || w == 256 do
          throw s!"import: unsupported parameter type {repr ty} of '{nm}'"
        let m ← constNat (← evalE p [] n)
        env := (nm, .arr, .mem nm m) :: env
        params := params.push ⟨.arr w m, nm⟩
        setWidth nm w
    | .word 64 =>
        env := (nm, .word, .w nm) :: env
        params := params.push ⟨.reg 64, nm⟩
        setAddr nm { base := nm, rt := none, off := 0 }
    | ty => throw s!"import: unsupported parameter type {repr ty} of '{nm}'"
  let env' ← execBlock p env fn.body
  let rs ← fn.ret.mapM (evalE p env')
  pure (params.toList, rs)

/-- A `JFun` imported with loops kept rolled, the global tables it reads at a
    run-time index, and the entry slot of each of its parameters. -/
structure RolledImport where
  /-- The imported function. A rolled loop is `for idx = 0 to n { body }`, `idx`
      a run-time 64-bit trip index, or `Stmt.forRt idx n body` for a run-time
      `n`; `b = @SYM` binds `b` to the base of the global table `SYM`. -/
  fn : JFun
  /-- Each global table read at a run-time index: its symbol and its words. -/
  tables : List (String × List Nat)
  /-- The entry slot of each parameter of `fn`, in order. -/
  slots : List ArgSlot

/-- The imported `JFun` of function `f` of the source unit `src`, with loops kept
    rolled when `roll` holds and the calls to `callFns` kept as calls. Its
    parameters are the source parameters (argument `j` in slot `abi j`), then each
    memory view (in the slot of its pointer parameter), then each array of the
    function's own frame (in its frame region, 8-byte cells). -/
def importWith (roll : Bool) (callFns : List String) (src : String) (f : String) :
    Except String RolledImport := do
  let p ← parseProg src
  let some fn := p.fns.find? (·.name == f) | throw s!"import: no function '{f}'"
  let ((params, rs), st) ← (importFnM p fn).run { roll, callFns }
  let viewParams : List Param := st.views.toList.map fun (b, w) =>
    ⟨.arr w viewCells, b ++ "@" ++ toString w⟩
  let viewSlots ← st.views.toList.mapM fun (b, _) =>
    match params.findIdx? (·.name == b) with
    | some j => pure (ArgSlot.abi j)
    | none => throw s!"import: view of '{b}', which is not a parameter"
  let (frameParams, frameSlots, _) := st.frames.toList.foldl
    (fun (ps, ss, off) (nm, n) =>
      (ps ++ [(⟨.arr 64 n, nm⟩ : Param)], ss ++ [ArgSlot.frame off], off + 8 * n))
    (([] : List Param), ([] : List ArgSlot), 0)
  let decls : List (JTy × String) :=
    (.reg 64, kiName) :: st.decls.toList.map (fun t => (.reg 64, t))
      ++ st.adecls.toList.map (fun (b, n) => (.arr ((st.widths.lookup b).getD 64) n, b))
  let allParams := params ++ viewParams ++ frameParams
  let slots := (List.range params.length).map ArgSlot.abi ++ viewSlots ++ frameSlots
  let jf : JFun ← match rs with
    | [.mem nm n] =>
        pure { name := f, params := allParams, retTy := .arr ((st.widths.lookup nm).getD 64) n,
               decls, inlineInts := [],
               body := st.out.toList ++ [.ret nm] }
    | [.w nm] =>
        pure { name := f, params := allParams, retTy := .reg 64, decls, inlineInts := [],
               body := st.out.toList ++ [.ret nm] }
    | _ => throw s!"import: '{f}' must return one array parameter or one run-time word"
  pure { fn := jf, tables := st.tables.toList, slots }

/-- The straight-line `JFun` of function `f` of the source unit `src`: every call
    inlined, every compile-time value folded, one statement per emitted operation. -/
def importFun (src : String) (f : String) : Except String JFun :=
  (importWith false [] src f).map (·.fn)

/-- `importFun` with every loop that is `rollable` and passes `tryRoll` kept as a
    rolled loop, and every `tryRtLoop`-shaped loop a run-time loop. -/
def importFunRolled (src : String) (f : String) : Except String RolledImport :=
  importWith true [] src f

/-- `importFunRolled` with the calls to the source functions `callFns` kept as
    calls to their symbols. -/
def importFunRolledWith (callFns : List String) (src : String) (f : String) :
    Except String RolledImport :=
  importWith true callFns src f

end CatCrypt.Crypto.Jasmin.JincInline
