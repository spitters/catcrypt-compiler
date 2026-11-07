/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JincInline
public import CatCrypt.Crypto.Jasmin.JazzToInstrR
public meta import CatCrypt.Crypto.Jasmin.JincToCom
public meta import CatCrypt.Crypto.Jasmin.JincInline
public meta import CatCrypt.Crypto.Jasmin.JazzToInstrR
public import CatCryptCore.Tactics.KatGuard

/-!
# Jasmin grammar fidelity of the `.jinc` parsers

Known-answer checks that the hand-written parsers of the Jasmin importer read an
expression with the meaning Jasmin's grammar (`compiler/src/parser.mly` of
jasmin-lang/jasmin) gives it, that array assignment into a `stack` array copies,
and that the forms the importer does not implement are refused.

* Precedence (`JincInline.parseProg`): Jasmin's levels, loosest first, are `?:`,
  `||`, `&&`, `== !=`, the comparisons, `|`, `^`, `&`, the shifts, `+ -`,
  `* / %`, `!`; so `| ^ &` bind tighter than the comparisons, against C. A unary
  `-` has the precedence of the binary `-`, so it takes the products that follow
  it: `-a / b` is `-(a / b)`. Each check compares the parse of `x = e;` with a
  hand AST.
* The same levels in `JazzToInstrR.parseJazzBody`.
* Array assignment (`JincInline.importFun`): `b = a` into a `stack` array `b`
  reads every cell of `a` at the assignment, so a later write to `a` does not
  reach `b`; into a `reg ptr` array it makes `b` refer to `a`.
* Refusals: the casts `(Ns)`, `(Nsi)` and `(sint)`, the types `siN`, and the
  signed annotation `64s` on a comparison, a division or a right shift are
  errors naming the construct. The forms kept are `(Nui)` and `uiN` (read as
  their unsigned word) and `(uint)` / `(int)` (the unsigned value of a word).

Each check is a static pin of the parser's reading of a fixed text: a change of
the grammar the parsers implement fails the build here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JincGrammarDemo

open CatCrypt.Crypto.Jasmin.JincInline
open CatCrypt.Crypto.Jasmin.JincToCom (Stmt Rhs Operand)

/-! ## `JincInline`: precedence -/

/-- The expression `e` of the one-statement function `fn f() { x = e; }`, as
    `parseProg` reads it, or the parse error. -/
def exprOf (src : String) : Except String E := do
  let p ← parseProg ("fn f() { x = " ++ src ++ "; }")
  match p.fns with
  | [fn] =>
      match fn.body with
      | [.assign [.var "x"] e] => pure e
      | _ => throw "not one assignment"
  | _ => throw "not one function"

/-- Whether `src` parses to the expression `e`. -/
def parsesTo (src : String) (e : E) : Bool :=
  match exprOf src with
  | .ok e' => e' == e
  | .error _ => false

/-- The variable `s`. -/
abbrev v (s : String) : E := .var s

-- `& | ^` bind tighter than `== != <`.
#kat parsesTo "a & b == c" (.bin "==" (.bin "&" (v "a") (v "b")) (v "c"))
#kat parsesTo "a | b < c" (.bin "<" (.bin "|" (v "a") (v "b")) (v "c"))
#kat parsesTo "a ^ b != c" (.bin "!=" (.bin "^" (v "a") (v "b")) (v "c"))
#kat parsesTo "a == b & c" (.bin "==" (v "a") (.bin "&" (v "b") (v "c")))
#kat parsesTo "a <s b | c" (.bin "<s" (v "a") (.bin "|" (v "b") (v "c")))
#kat parsesTo "a & b >=u c" (.bin ">=u" (.bin "&" (v "a") (v "b")) (v "c"))
-- `== !=` bind looser than `< <= > >=`, and `&&` looser than both.
#kat parsesTo "a == b < c" (.bin "==" (v "a") (.bin "<" (v "b") (v "c")))
#kat parsesTo "a && b | c" (.bin "&&" (v "a") (.bin "|" (v "b") (v "c")))
-- `|` below `^` below `&` below the shifts below `+ -` below `* / %`.
#kat parsesTo "a | b ^ c & d"
  (.bin "|" (v "a") (.bin "^" (v "b") (.bin "&" (v "c") (v "d"))))
#kat parsesTo "a & b << c + d * e"
  (.bin "&" (v "a") (.bin "<<" (v "b") (.bin "+" (v "c") (.bin "*" (v "d") (v "e")))))
-- Left associativity.
#kat parsesTo "a - b - c" (.bin "-" (.bin "-" (v "a") (v "b")) (v "c"))
-- A unary `-` takes the products that follow it; `!` takes a unary expression.
#kat parsesTo "-a / b" (.neg (.bin "/" (v "a") (v "b")))
#kat parsesTo "-a * b + c" (.bin "+" (.neg (.bin "*" (v "a") (v "b"))) (v "c"))
#kat parsesTo "a * -b % c" (.bin "*" (v "a") (.neg (.bin "%" (v "b") (v "c"))))
#kat parsesTo "!a & b" (.bin "&" (.not (v "a")) (v "b"))
-- A cast binds tightest.
#kat parsesTo "(64u) a & b" (.bin "&" (.cast 64 (v "a")) (v "b"))
-- `?:` is loosest.
#kat parsesTo "a | b == c ? d : e"
  (.cond (.bin "==" (.bin "|" (v "a") (v "b")) (v "c")) (v "d") (v "e"))

/-! ## `JincInline`: casts and word-int types -/

/-- Whether the parse of `src` fails with a message containing `frag`. -/
def refuses (src : String) (frag : String) : Bool :=
  match exprOf src with
  | .ok _ => false
  | .error msg => (msg.splitOn frag).length > 1

/-- Whether `parseProg` of the text fails with a message containing `frag`. -/
def progRefuses (src frag : String) : Bool :=
  match parseProg src with
  | .ok _ => false
  | .error msg => (msg.splitOn frag).length > 1

-- Refused: the sign-extending and signed casts, and the signed word-int types.
#kat refuses "(64s) a" "(64s)"
#kat refuses "(32si) a" "(32si)"
#kat refuses "(sint) a" "(sint)"
#kat refuses "(si64) a" "si64"
#kat progRefuses "fn f() { reg si64 y; y = 0; }" "si64"
#kat progRefuses "fn f(reg si32 y) { }" "si32"
-- Kept: `(Nui)` as `(Nu)`, `(uint)` and `(int)` as the unsigned value, `uiN` as `uN`.
#kat parsesTo "(64ui) a" (.cast 64 (v "a"))
#kat parsesTo "(uint) a + 1" (.bin "+" (.cast 0 (v "a")) (.num 1))
#kat parsesTo "(int) a" (.cast 0 (v "a"))
#kat match parseProg "fn f() { reg ui64 y; y = 0; }" with
  | .ok p => match p.fns with
    | [fn] => match fn.body with
      | [.decl (.word 64) false false ["y"], _] => true
      | _ => false
    | _ => false
  | .error _ => false

-- `(uint)` of a compile-time word is its unsigned value as an integer: `0 - 1`
-- folds to `-1`, and the comparison with `0` is false; with word arithmetic it
-- would wrap to `2^64 - 1`.
#kat match importFun "export fn f(reg u64 a) -> reg u64 {
    reg u64 z; reg u64 r; inline int k;
    z = 0; k = (uint) z - 1;
    if (k < 0) { r = a + 1; } else { r = a + 2; }
    return r; }" "f" with
  | .ok fn => fn.body.any fun
      | .assign _ (.bin .add "a" (.lit 1)) => true
      | _ => false
  | .error _ => false

-- The signed annotation `64s` on an operator whose signed meaning differs.
#kat match importFun "export fn f(reg u64 a, reg u64 b) -> reg u64 {
    reg u64 r; r = a >>64s b; return r; }" "f" with
  | .ok _ => false
  | .error msg => (msg.splitOn ">>64s").length > 1

/-! ## `JincInline`: array assignment -/

/-- `b = a` into the `stack` array `b`, then a write to `a`, then a read of `b`. -/
def copySrc : String :=
  "export fn f(reg ptr u64[2] a) -> reg u64 {
    stack u64[2] b;
    reg u64 r;
    b = a;
    a[0] = 5;
    r = b[0];
    return r;
  }"

/-- The same through a `reg ptr` array `b`, which refers to `a`. -/
def aliasSrc : String :=
  "export fn f(reg ptr u64[2] a) -> reg u64 {
    reg ptr u64[2] b;
    reg u64 r;
    b = a;
    a[0] = 5;
    r = b[0];
    return r;
  }"

/-- The statements of the import of `f` from `src`, or none. -/
def bodyOf (src : String) : Option (List Stmt) :=
  match importFun src "f" with
  | .ok fn => some fn.body
  | .error _ => none

-- The copy: both cells of `a` are loaded and stored into the frame array `b`
-- before `a[0] = 5`, and `r = b[0]` loads from `b`, so `f` returns the old `a[0]`.
#kat bodyOf copySrc == some
  [ .assign "%ki" (.imm 0), .assign "%j0" (.load "a" "%ki"),
    .storeAt "b" (.lit 0) (.glob "%j0"),
    .assign "%ki" (.imm 1), .assign "%j1" (.load "a" "%ki"),
    .storeAt "b" (.lit 1) (.glob "%j1"),
    .assign "%j2" (.imm 5), .store "a" 0 "%j2",
    .assign "%ki" (.imm 0), .assign "%j3" (.load "b" "%ki"),
    .ret "%j3" ]

-- The alias: `r = b[0]` loads from `a` after `a[0] = 5`, so `f` returns `5`.
#kat bodyOf aliasSrc == some
  [ .assign "%j0" (.imm 5), .store "a" 0 "%j0",
    .assign "%ki" (.imm 0), .assign "%j1" (.load "a" "%ki"),
    .ret "%j1" ]


/-! ## `JazzToInstrR`: precedence -/

section JazzLevels

open CatCrypt.Crypto.Jasmin.JazzToInstrR
open CatCrypt.Crypto.Jasmin.JazzToInstrR.RoundTrip

-- `&` binds tighter than `==`, `|` tighter than `<`, and `^` looser than `&`.
#kat match parseJazzBody controlEnv "x = y & n == x; x = y | n < x; x = y ^ n & x;" with
  | .ok is => instrsBEq is
      [ asg "x" (.Papp2 (.Oeq .U64) (.Papp2 (.Oland .U64) (pv (u "y")) (pv (u "n"))) (pv (u "x")))
      , asg "x" (.Papp2 (.Olt .Uextend .U64)
          (.Papp2 (.Olor .U64) (pv (u "y")) (pv (u "n"))) (pv (u "x")))
      , asg "x" (.Papp2 (.Olxor .U64) (pv (u "y"))
          (.Papp2 (.Oland .U64) (pv (u "n")) (pv (u "x")))) ]
  | .error _ => false

end JazzLevels

end CatCrypt.Crypto.Jasmin.JincGrammarDemo
