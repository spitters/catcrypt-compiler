/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminAST
public meta import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.Jasmin.JazzUnit
public meta import CatCrypt.Crypto.Jasmin.JazzUnit
public import CatCryptCore.Tactics.KatGuard
public import Std.Data.HashMap

@[expose] public section
set_option autoImplicit false

/-!
# `.jazz` text → `InstrR` parser

A recursive-descent parser from Jasmin surface syntax to the `JasminAST` types
(`FunDecl`, `InstrR`, `PExpr`, `LVal`) interpreted by `bignumExec`, and to the
compilation units `Jazz.JazzUnit` that carry the surface information of a text.
The accepted subset is the one the `S2NBignumSSA` ports, their printer
`Emit.emitFunDecl` and the unit printer `Jazz.print` use. Every function is
total: recursion is bounded by a fuel argument proportional to the input length.
The declarations in scope are a `VEnv`, a list with a hash map from each name to its
latest declaration, so a variable is found in constant expected time.

## Accepted subset

* Top level: function declarations `[#[…]]… [export | inline] fn f(params)
  [-> types] { body }`, each preceded by any number of `//` comment lines and
  `require "path"` lines. The annotations, the function kind, the comment lines
  (the preamble of the next function), the `require` paths and the storage and
  type of each result are recorded in the `JazzFn` of `parseUnit`; the results
  are the names of the final `return x, y;`.
* Parameters and declarations: `reg | stack | inline`, the qualifiers `ptr`,
  `mut` and `const`, and a type `uNN`, `uNN[k]`, `bool` or `int`; a declaration
  lists one or more names, separated by spaces or commas. A type `uNN[k]` is the
  array type `sarr (k * bytes uNN)` with element width `uNN`. The storage class is
  `reg`, `reg ptr` (`regPtr false`, also for `reg const ptr`), `reg mut ptr`
  (`regPtr true`), `stack`, `stack ptr` or `inline`.
* Statements:
  - `lv = e;` (`Cassgn`, tag `AT_none`, type the declared type of `lv`);
  - `lv OP= e;` for `OP` in `+ - * & | ^ << >> >>s`, read as `lv = lv OP e`;
  - `lv₁, …, lvₙ = #OP(args);` (`Copn` with `Oasm ⟨OP⟩`), and `#OP(args);`;
  - `lv₁, …, lvₙ = f(args);` and `f(args);` (`Ccall .DoNotInline`);
  - `if e { … } else { … }` (the `else` part optional);
  - `for i = lo to hi { … }` and `for i = hi downto lo { … }` with numeral bounds;
  - `while e { … }`, `while { … } e { … }` and `while { … } e`.
* L-values: `x`, `_` (`Lnone {} (.sword .U64)`; `parseUnit` types the `_` outputs
  of an intrinsic by `asmOutTys`), `x[e]` (`Laset .AAscale`) and `[:uNN x + e]` or
  `[x + e]` (`Lmem`, width `U64` when omitted).
* Expressions: decimal and `0x` numerals (`Pconst`), `-k` (`Pconst (-k)`),
  `true`, `false`, variables, `x[e]` (`Pget .AAscale`), memory reads
  `[:uNN x + e]` (`Pload`), `-e` (`0 - e`), the sized negation `-NNu e` (`Oneg`),
  `!e` (`Olnot`), the cast `(NNu) e` (`Ozeroext`), the cast `(uint) e`
  (`Oint_of_word`, at the width of `e`), parentheses, the conditional `c ? a : b` (`Pif`, at the type
  `uNN` of the width of `a`, else of the target), and the binary operators
  `|| && | ^ & == != < <= > >= <s <=s >s >=s << >> >>s + - *` with C precedence
  and left associativity. The width of a binary operator is the width of its
  left operand when that is a word-typed variable, load, array read or cast, and
  otherwise the width of the assignment target.
* Comments `// …` and `/* … */`; a `//` line outside every function body is a
  preamble line, any other comment is whitespace.

Any other construct (`param`, globals, `else if`, calls or intrinsics inside an
expression, undeclared variables) is a parse error naming the construct.

## Main definitions

* `tokenize`: the lexer.
* `asmOutTys`, `retypeOpnLvs`: the output types of an intrinsic and the typing of
  the `_` outputs of an intrinsic call by them.
* `parseUnit`: `.jazz` text → `Jazz.JazzUnit`.
* `parseJazz`: `.jazz` text → `List FunDecl`.
* `parseJazzProg`: `.jazz` text → `JasminProg`.
* `parseJazzBody`: a statement sequence under a given declaration environment
  → `List InstrR`.
* `pexprBEq`, `instrsBEq`, `funDeclBEq`, `parsesTo`: structural equality of the AST
  and the check that a text parses to given declarations.

`lookupVar_eq_lookupVarRef` states that the lookup in a `VEnv` is the search of its
list of declarations.

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
  | question
  /-- A string literal, without its quotes. -/
  | str (s : String)
  /-- A `//` comment line outside every brace pair, `//` included. -/
  | lcomment (s : String)
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
def radixVal (base : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun a c => a * base + hexDigitValue c) 0

/-- Read a decimal or `0x` hexadecimal numeral from the front of the input. -/
def readNumber : List Char → Nat × List Char
  | '0' :: 'x' :: rest => (radixVal 16 (rest.takeWhile isHexChar), rest.dropWhile isHexChar)
  | '0' :: 'X' :: rest => (radixVal 16 (rest.takeWhile isHexChar), rest.dropWhile isHexChar)
  | cs => (radixVal 10 (cs.takeWhile Char.isDigit), cs.dropWhile Char.isDigit)

/-- The input after the `*/` closing a block comment, or `none` if there is none. -/
def dropBlockComment : List Char → Option (List Char)
  | '*' :: '/' :: rest => some rest
  | _ :: rest => dropBlockComment rest
  | [] => none

/-- The lexer loop; `d` is the brace depth, and a `//` line at depth `0` is an
    `lcomment` token. Each step consumes at least one character, so fuel
    `cs.length + 1` suffices. -/
def lexF : Nat → Nat → List Char → List Token → Except String (List Token)
  | 0, _, _, _ => .error "JazzToInstrR.lex: fuel exhausted"
  | _ + 1, _, [], acc => .ok acc.reverse
  | f + 1, d, c :: cs, acc =>
    if c.isWhitespace then lexF f d cs acc else
    match c, cs with
    | '/', '/' :: rest =>
        let rest' := rest.dropWhile (· ≠ '\n')
        if d = 0 then
          lexF f d rest' (.lcomment ("//" ++ String.ofList (rest.takeWhile (· ≠ '\n'))) :: acc)
        else lexF f d rest' acc
    | '/', '*' :: rest =>
        match dropBlockComment rest with
        | some r => lexF f d r acc
        | none => .error "JazzToInstrR.lex: unterminated block comment"
    | '>', '>' :: 's' :: '=' :: rest => lexF f d rest (.binEq .sar :: acc)
    | '>', '>' :: '=' :: rest => lexF f d rest (.binEq .shr :: acc)
    | '<', '<' :: '=' :: rest => lexF f d rest (.binEq .shl :: acc)
    | '>', '>' :: 's' :: rest => lexF f d rest (.bin .sar :: acc)
    | '>', '>' :: rest => lexF f d rest (.bin .shr :: acc)
    | '<', '<' :: rest => lexF f d rest (.bin .shl :: acc)
    | '<', '=' :: 's' :: rest => lexF f d rest (.cmp .les :: acc)
    | '>', '=' :: 's' :: rest => lexF f d rest (.cmp .ges :: acc)
    | '<', '=' :: rest => lexF f d rest (.cmp .le :: acc)
    | '>', '=' :: rest => lexF f d rest (.cmp .ge :: acc)
    | '<', 's' :: rest => lexF f d rest (.cmp .lts :: acc)
    | '>', 's' :: rest => lexF f d rest (.cmp .gts :: acc)
    | '<', rest => lexF f d rest (.cmp .lt :: acc)
    | '>', rest => lexF f d rest (.cmp .gt :: acc)
    | '=', '=' :: rest => lexF f d rest (.cmp .eq :: acc)
    | '!', '=' :: rest => lexF f d rest (.cmp .ne :: acc)
    | '&', '&' :: rest => lexF f d rest (.andAnd :: acc)
    | '|', '|' :: rest => lexF f d rest (.orOr :: acc)
    | '+', '=' :: rest => lexF f d rest (.binEq .add :: acc)
    | '-', '=' :: rest => lexF f d rest (.binEq .sub :: acc)
    | '*', '=' :: rest => lexF f d rest (.binEq .mul :: acc)
    | '&', '=' :: rest => lexF f d rest (.binEq .land :: acc)
    | '|', '=' :: rest => lexF f d rest (.binEq .lor :: acc)
    | '^', '=' :: rest => lexF f d rest (.binEq .lxor :: acc)
    | '-', '>' :: rest => lexF f d rest (.arrow :: acc)
    | '+', rest => lexF f d rest (.bin .add :: acc)
    | '-', rest => lexF f d rest (.bin .sub :: acc)
    | '*', rest => lexF f d rest (.bin .mul :: acc)
    | '&', rest => lexF f d rest (.bin .land :: acc)
    | '|', rest => lexF f d rest (.bin .lor :: acc)
    | '^', rest => lexF f d rest (.bin .lxor :: acc)
    | '(', rest => lexF f d rest (.lparen :: acc)
    | ')', rest => lexF f d rest (.rparen :: acc)
    | '{', rest => lexF f (d + 1) rest (.lbrace :: acc)
    | '}', rest => lexF f (d - 1) rest (.rbrace :: acc)
    | '?', rest => lexF f d rest (.question :: acc)
    | '[', rest => lexF f d rest (.lbrack :: acc)
    | ']', rest => lexF f d rest (.rbrack :: acc)
    | ';', rest => lexF f d rest (.semi :: acc)
    | ',', rest => lexF f d rest (.comma :: acc)
    | ':', rest => lexF f d rest (.colon :: acc)
    | '=', rest => lexF f d rest (.assign :: acc)
    | '#', rest => lexF f d rest (.hash :: acc)
    | '!', rest => lexF f d rest (.bang :: acc)
    | '"', rest =>
        match rest.dropWhile (· ≠ '"') with
        | _ :: rest' => lexF f d rest' (.str (String.ofList (rest.takeWhile (· ≠ '"'))) :: acc)
        | [] => .error "JazzToInstrR.lex: unterminated string literal"
    | c, rest =>
        if c.isAlpha || c == '_' then
          let (id, rest') := readIdent (c :: rest)
          lexF f d rest' (.ident id :: acc)
        else if c.isDigit then
          let (n, rest') := readNumber (c :: rest)
          lexF f d rest' (.num n :: acc)
        else .error s!"JazzToInstrR.lex: unexpected character '{c}'"

/-- Tokenize a `.jazz` text. -/
def tokenize (s : String) : Except String (List Token) :=
  let cs := s.toList
  lexF (cs.length + 1) 0 cs []

/-! ## Parser state -/

/-- A declared variable: its name, its type, its word width (the element
    width for an array, `U64` for `bool` and `int`), and the storage class and
    surface type of its declaration. -/
structure VDecl where
  name : String
  ty : SType
  ews : WSize
  storage : Jazz.Storage := .reg
  pty : Jazz.PType := .word .U64
  deriving Inhabited

/-- The declarations in scope, last first, with a hash map from each name to its
    latest declaration. -/
structure VEnv where
  /-- The declarations, last first. -/
  decls : List VDecl
  /-- The latest declaration of each name. -/
  tab : Std.HashMap String VDecl
  /-- The entry of a name is its first declaration in `decls`. -/
  tab_eq : ∀ x, tab[x]? = decls.find? (·.name == x)

/-- No declarations. -/
def VEnv.empty : VEnv := ⟨[], ∅, by simp⟩

/-- The declaration `d` in front of `e`. -/
def VEnv.cons (d : VDecl) (e : VEnv) : VEnv :=
  ⟨d :: e.decls, e.tab.insert d.name d, fun x => by
    rw [Std.HashMap.getElem?_insert, e.tab_eq x, List.find?_cons]
    cases d.name == x <;> rfl⟩

/-- The declarations `l`, the first one last declared. -/
def VEnv.ofList : List VDecl → VEnv
  | [] => .empty
  | d :: l => .cons d (ofList l)

theorem VEnv.ofList_decls : ∀ l : List VDecl, (VEnv.ofList l).decls = l
  | [] => rfl
  | d :: l => congrArg (d :: ·) (VEnv.ofList_decls l)

/-- The latest declaration of the name `x`. -/
def VEnv.find? (e : VEnv) (x : String) : Option VDecl := e.tab[x]?

/-- `VEnv.find?` is the first declaration of the name in the list of declarations. -/
theorem VEnv.find?_eq (e : VEnv) (x : String) :
    e.find? x = e.decls.find? (·.name == x) := e.tab_eq x

instance : Inhabited VEnv := ⟨.empty⟩

/-- Parser state: remaining tokens, the declarations in scope, the local
    declarations of the current function (last first), whether the `_` outputs of
    an intrinsic are typed by `asmOutTys`, and the fuel bound given to every
    recursive parsing function. -/
structure St where
  toks : List Token
  env : VEnv := .empty
  decls : List Jazz.Decl := []
  retype : Bool := false
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
  match (← get).env.find? x with
  | some d => return d
  | none => fail s!"undeclared variable '{x}'"

/-- `lookupVar` by a search of the list of declarations. -/
def lookupVarRef (x : String) : P VDecl := do
  match (← get).env.decls.find? (·.name == x) with
  | some d => return d
  | none => fail s!"undeclared variable '{x}'"

theorem lookupVar_eq_lookupVarRef : lookupVar = lookupVarRef := by
  funext x
  simp only [lookupVar, lookupVarRef, VEnv.find?_eq]

/-- Bring a declaration into scope. -/
def declare (d : VDecl) : P Unit := modify fun st => { st with env := st.env.cons d }

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

/-! ## Output types of intrinsics -/

/-- The output types of the intrinsic `OP_NN` (`NN` the bit width), flags first, for
    the x86 intrinsics whose flag outputs a `.jazz` text discards with `_`: the
    five flags `of cf sf pf zf` and the result of `ADD`, `SUB`, `ADC`, `SBB`, `NEG`,
    `AND`, `ANDN`, `OR`, `XOR`, `SHL`, `SHR`, `SAR`, `LZCNT`, `TZCNT`, `POPCNT`; the
    flags `of sf pf zf` and the result of `INC`, `DEC`; the five flags of `CMP`,
    `TEST`; the five flags, the high and the low word of `MUL`, `IMUL`; the carry
    and the result of `ADCX`, `ADOX`; `of cf` and the result of `ROL`, `ROR`; the low
    and the high word of `MULX_lo_hi_NN`. -/
def asmOutTys (op : String) : Option (List SType) :=
  match op.splitOn "_" with
  | ["MULX", "lo", "hi", bits] =>
    (bits.toNat?.bind wsizeOfBits).map fun w => [.sword w, .sword w]
  | [nm, bits] =>
    match bits.toNat?.bind wsizeOfBits with
    | none => none
    | some w =>
      let fl (n : Nat) : List SType := List.replicate n .sbool
      match nm with
      | "ADD" | "SUB" | "ADC" | "SBB" | "NEG" | "AND" | "ANDN" | "OR" | "XOR"
      | "SHL" | "SHR" | "SAR" | "LZCNT" | "TZCNT" | "POPCNT" => some (fl 5 ++ [.sword w])
      | "INC" | "DEC" => some (fl 4 ++ [.sword w])
      | "CMP" | "TEST" => some (fl 5)
      | "MUL" | "IMUL" => some (fl 5 ++ [.sword w, .sword w])
      | "ADCX" | "ADOX" => some [.sbool, .sword w]
      | "ROL" | "ROR" => some [.sbool, .sbool, .sword w]
      | _ => none
  | _ => none

/-- The types of the `_` outputs of an `n`-output call of `op`: `asmOutTys op` when
    it lists `n` types, else none. -/
def opnNoneTys (op : String) (n : Nat) : List SType :=
  match asmOutTys op with
  | some tys => if tys.length = n then tys else []
  | none => []

/-- Type the `_` output at position `k`, `k + 1`, … by `tys` (`u64` past its end). -/
def retypeGo (tys : List SType) : Nat → List LVal → List LVal
  | _, [] => []
  | k, .Lnone _ _ :: lvs => .Lnone {} ((tys[k]?).getD (.sword .U64)) :: retypeGo tys (k + 1) lvs
  | k, lv :: lvs => lv :: retypeGo tys (k + 1) lvs

/-- The outputs of a call of the intrinsic `op` with each `_` typed by `asmOutTys`
    (`u64` when the table has no entry of that length). -/
def retypeOpnLvs (op : String) (lvs : List LVal) : List LVal :=
  retypeGo (opnNoneTys op lvs.length) 0 lvs

/-- The surface type `uNN`, `uNN[k]`, `bool` or `int`. -/
def parsePType : P Jazz.PType := do
  let s ← expectIdent
  match s with
  | "bool" => return .bool
  | "int" => return .int
  | _ =>
    match wsizeOfName s with
    | none => fail s!"unsupported type '{s}'"
    | some ws =>
      if (← peek) = some .lbrack then
        advance
        let k ← expectNum
        expect .rbrack
        return .arr ws k
      else return .word ws

/-- The word width of a surface type: the element width of an array, `U64` for
    `bool` and `int`. -/
def ptypeWs : Jazz.PType → WSize
  | .word ws => ws
  | .arr ws _ => ws
  | _ => .U64

/-- Parse a type `uNN`, `uNN[k]`, `bool` or `int`, returning the type and its
    word width. -/
def parseType : P (SType × WSize) := do
  let t ← parsePType
  return (t.toSType, ptypeWs t)

/-- Read one qualifier `ptr`, `mut` or `const`, recording whether `ptr` and `mut`
    were read. -/
def qualStep (q : Bool × Bool) : P (Bool × Bool) := do
  match ← peek with
  | some (.ident "ptr") => advance; return (true, q.2)
  | some (.ident "mut") => advance; return (q.1, true)
  | some (.ident "const") => advance; return q
  | _ => return q

/-- Parse a storage class `reg | stack | inline` with at most two qualifiers among
    `ptr`, `mut` and `const`. -/
def parseStorage : P Jazz.Storage := do
  let kw ← expectIdent
  let q ← qualStep (false, false)
  let (ptr, mutbl) ← qualStep q
  match kw with
  | "reg" => return if ptr then .regPtr mutbl else .reg
  | "stack" => return if ptr then .stackPtr else .stack
  | "inline" => return .inlineVar
  | _ => fail s!"unknown storage class '{kw}'"

/-- The declaration of a name with a storage class and a surface type. -/
def mkVDecl (x : String) (sto : Jazz.Storage) (t : Jazz.PType) : VDecl :=
  { name := x, ty := t.toSType, ews := ptypeWs t, storage := sto, pty := t }

/-- Parse the names of a declaration up to its `;`, declaring each. -/
def parseDeclNamesF : Nat → Jazz.Storage → Jazz.PType → P (List String)
  | 0, _, _ => fail "fuel exhausted in a declaration"
  | f + 1, sto, t => do
    let x ← expectIdent
    declare (mkVDecl x sto t)
    match ← peek with
    | some .semi => advance; return [x]
    | some .comma => advance; return x :: (← parseDeclNamesF f sto t)
    | some (.ident _) => return x :: (← parseDeclNamesF f sto t)
    | some t => fail s!"expected ',' or ';' in a declaration, found {repr t}"
    | none => fail "unterminated declaration"

/-- Parse a declaration `reg|stack|inline [qualifiers] type names;` and record it
    among the local declarations. -/
def parseDecl : P Unit := do
  let sto ← parseStorage
  let t ← parsePType
  let names ← parseDeclNamesF (← get).fuel sto t
  modify fun st => { st with decls := { storage := sto, ty := t, names := names } :: st.decls }

/-! ## Expressions -/

/-- What `parseExprF` parses: an expression with an optional conditional
    `? a : b`, an expression at precedence level `n`, the continuation of a
    level-`n` expression after its left operand `lhs`, or an atom. -/
inductive EGoal where
  | top
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
  | .Papp1 (.Oneg w) _ => some w
  | _ => none

/-- Parse an expression; `ctx` is the width of the assignment target, used for
    operators whose left operand has no evident width. -/
def parseExprF : Nat → WSize → EGoal → P PExpr
  | 0, _, _ => fail "fuel exhausted in an expression"
  | f + 1, ctx, .top => do
    let c ← parseExprF f ctx (.lvl 0)
    if (← peek) = some .question then
      advance
      let a ← parseExprF f ctx .top
      expect .colon
      let b ← parseExprF f ctx .top
      return .Pif (.sword ((exprWidth a).getD ctx)) c a b
    else return c
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
      match (← get).toks with
      | .num k :: .ident "u" :: _ =>
        advance; advance
        match wsizeOfBits k with
        | none => fail s!"negation at an unsupported width {k}"
        | some ws =>
          let e ← parseExprF f ctx .atom
          return .Papp1 (.Oneg ws) e
      | .num k :: _ => advance; return .Pconst (-(k : Int))
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
      | .ident "uint" :: .rparen :: _ =>
        advance; advance
        let e ← parseExprF f ctx .atom
        return .Papp1 (.Oint_of_word ((exprWidth e).getD ctx)) e
      | _ =>
        let e ← parseExprF f ctx .top
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
        | some (.bin .add) => advance; parseExprF f .U64 .top
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
        let idx ← parseExprF f .U64 .top
        expect .rbrack
        return .Pget .AAscale d.ews { gv := d.varI, gs := false } idx
      | some .lparen => fail s!"call of '{x}' inside an expression is not in the subset"
      | _ => return (← lookupVar x).pvar
    | some .hash => fail "intrinsic inside an expression is not in the subset"
    | some t => fail s!"expected an expression, found {repr t}"
    | none => fail "expected an expression, found end of input"

/-- Parse an expression with target width `ctx`. -/
def parseExpr (ctx : WSize) : P PExpr := do
  parseExprF (← get).fuel ctx .top

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
    | some (.lcomment _) => advance; parseStmtsF f
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
      let v : VarI := match (← get).env.find? x with
        | some d => d.varI
        | none => { var := { vname := x, vtype := .sint } }
      expect .assign
      let start ← expectNum
      let dir ← expectIdent
      let range ← (do
        match dir with
        | "to" => return Range.mk .UpTo start (← expectNum)
        | "downto" => return Range.mk .DownTo (← expectNum) start
        | _ => fail s!"loop direction '{dir}' is not in the subset")
      expect .lbrace
      let body ← parseStmtsF f
      expect .rbrace
      return .Cfor v range body :: (← parseStmtsF f)
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
        let lvs' := if (← get).retype then retypeOpnLvs op lvs else lvs
        return .Copn lvs' .AT_none (.Oasm ⟨op⟩) args
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
    declaring each; each parameter comes with its storage class and surface type. -/
def parseParamsF : Nat → P (List (FunParam × (Jazz.Storage × Jazz.PType)))
  | 0 => fail "fuel exhausted in a parameter list"
  | f + 1 => do
    if (← peek) = some .rparen then advance; return []
    let sto ← parseStorage
    let t ← parsePType
    let x ← expectIdent
    let d := mkVDecl x sto t
    declare d
    match ← peek with
    | some .comma => advance; return (⟨d.varI⟩, (sto, t)) :: (← parseParamsF f)
    | some .rparen => advance; return [(⟨d.varI⟩, (sto, t))]
    | some t => fail s!"expected ',' or ')' in a parameter list, found {repr t}"
    | none => fail "unterminated parameter list"

/-- Parse the result types `storage type, …` after `->`, up to the `{`. -/
def parseResultTysF : Nat → P (List (Jazz.Storage × Jazz.PType))
  | 0 => fail "fuel exhausted in a return-type list"
  | f + 1 => do
    let sto ← parseStorage
    let t ← parsePType
    if (← peek) = some .comma then
      advance
      return (sto, t) :: (← parseResultTysF f)
    else return [(sto, t)]

/-- The text of an annotation token. -/
def annotTokText : Token → Option String
  | .ident s => some s
  | .num n => some (toString n)
  | .assign => some "="
  | .comma => some ","
  | .colon => some ":"
  | .str s => some ("\"" ++ s ++ "\"")
  | _ => none

/-- Read an annotation body up to and including its `]`, returning its tokens'
    text without separators. -/
def parseAnnotF : Nat → P String
  | 0 => fail "fuel exhausted in an annotation"
  | f + 1 => do
    match ← peek with
    | some .rbrack => advance; return ""
    | some t =>
      match annotTokText t with
      | some s => advance; return s ++ (← parseAnnotF f)
      | none => fail s!"unsupported token {repr t} in an annotation"
    | none => fail "unterminated annotation"

/-- Read the string literals of a `require` line. -/
def parseRequireF : Nat → P (List String)
  | 0 => fail "fuel exhausted in a require line"
  | f + 1 => do
    match ← peek with
    | some (.str s) => advance; return s :: (← parseRequireF f)
    | _ => return []

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

/-- Parse a function after its `fn` keyword: its name, parameters, result types,
    body and `return` statement, with the preamble lines `pre`, the `require`
    paths `reqs` and the kind `kind` read before it. -/
def parseFn (f : Nat) (pre reqs : List String) (kind : Jazz.FnKind) : P Jazz.JazzFn := do
  let name ← expectIdent
  modify fun st => { st with env := .empty, decls := [] }
  expect .lparen
  let params ← parseParamsF f
  let resultTys ← (do
    if (← peek) = some .arrow then
      advance
      parseResultTysF f
    else return [])
  expect .lbrace
  let body ← parseStmtsF f
  let results ← (do
    if (← peek) = some (.ident "return") then
      advance
      parseReturnF f
    else return [])
  expect .rbrace
  let decls := (← get).decls.reverse
  return { preamble := pre, requires := reqs, kind := kind,
           fd := { name := { name := name }, params := params.map (·.1), body := body,
                   results := results },
           paramTys := params.map (·.2), resultTys := resultTys, decls := decls }

/-- Parse the functions up to the end of the input; `pre`, `reqs` and `annots` are
    the preamble lines, `require` paths and annotations read so far for the next
    function, last first. Comment lines after the last function are dropped. -/
def parseFnsF : Nat → List String → List String → List String → P (List Jazz.JazzFn)
  | 0, _, _, _ => fail "fuel exhausted at top level"
  | f + 1, pre, reqs, annots => do
    match ← peek with
    | none =>
      if reqs.isEmpty && annots.isEmpty then return []
      else fail "a require line or an annotation without a function"
    | some (.lcomment s) => advance; parseFnsF f (s :: pre) reqs annots
    | some (.ident "require") =>
      advance
      let ps ← parseRequireF f
      if ps.isEmpty then fail "a require line without a path"
      parseFnsF f pre (ps.reverse ++ reqs) annots
    | some .hash =>
      advance
      expect .lbrack
      let a ← parseAnnotF f
      parseFnsF f pre reqs (a :: annots)
    | some (.ident "export") | some (.ident "inline") | some (.ident "fn") =>
      let kind ← (do
        match ← peek with
        | some (.ident "export") => advance; expect (.ident "fn"); return Jazz.FnKind.exportFn
        | some (.ident "inline") => advance; expect (.ident "fn"); return .inlineFn
        | _ => advance; return .localFn annots.reverse)
      if !annots.isEmpty && !(kind matches .localFn _) then
        fail "an annotation on an export or inline function"
      let fn ← parseFn f pre.reverse reqs.reverse kind
      return fn :: (← parseFnsF f [] [] [])
    | some t => fail s!"unsupported top-level construct starting with {repr t}"

/-! ## Entry points -/

/-- Parse a `.jazz` text into a unit; `retype` types the `_` outputs of an
    intrinsic by `asmOutTys`. -/
def parseUnitWith (retype : Bool) (s : String) : Except String Jazz.JazzUnit := do
  let toks ← tokenize s
  let fuel := 16 * (toks.length + 1)
  let (fns, _) ← (parseFnsF fuel [] [] []).run { toks := toks, fuel := fuel, retype := retype }
  return { fns := fns }

/-- Parse a `.jazz` text into a compilation unit: per function its preamble lines,
    `require` paths, kind, `FunDecl`, the storage class and surface type of each
    parameter and result, and its local declarations in text order. The `_` outputs
    of an intrinsic are typed by `asmOutTys`; the unit has no extern signatures. -/
def parseUnit (s : String) : Except String Jazz.JazzUnit :=
  parseUnitWith true s

/-- Parse a `.jazz` text into its function declarations. -/
def parseJazz (s : String) : Except String (List FunDecl) := do
  let u ← parseUnitWith false s
  return u.fns.map (·.fd)

/-- Parse a `.jazz` text into a `JasminProg`. -/
def parseJazzProg (s : String) : Except String JasminProg :=
  (parseJazz s).map fun fs => { funcs := fs }

/-- Parse a statement sequence under the declarations `env` (name, type and
    word width); the whole text must be consumed. -/
def parseJazzBody (env : List VDecl) (s : String) : Except String (List InstrR) := do
  let toks ← tokenize s
  let fuel := 16 * (toks.length + 1)
  let (body, st) ← (parseStmtsF fuel).run { toks := toks, env := .ofList env, fuel := fuel }
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

-- The cast `(uint) e` reads as `Oint_of_word`, the sized negation `-64u e` as `Oneg`,
-- and `-e` as `0 - e`.
#kat match parseJazzBody controlEnv "x = t[(uint) y]; t[(uint) n] = x; x = -64u y; n = -y;" with
  | .ok is => instrsBEq is
      [ asg "x" (.Pget .AAscale .U64 { gv := { var := arr "t" 32 }, gs := false }
          (.Papp1 (.Oint_of_word .U64) (pv (u "y"))))
      , .Cassgn (.Laset .AAscale .U64 { var := arr "t" 32 }
          (.Papp1 (.Oint_of_word .U64) (pv (u "n")))) .AT_none (.sword .U64) (pv (u "x"))
      , asg "x" (.Papp1 (.Oneg .U64) (pv (u "y")))
      , asg "n" (.Papp2 (.Osub .U64) (.Pconst 0) (pv (u "y"))) ]
  | .error _ => false

end RoundTrip

end CatCrypt.Crypto.Jasmin.JazzToInstrR
