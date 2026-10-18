/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JazzUnit

/-!
# The Jasmin printer of compilation units

`print` renders a `JazzUnit` as `.jazz` text in the surface syntax of `Emit.emitFunDecl`:
for every instruction shape that printer renders, `printJazzInstr` renders the same text,
and a function is laid out as there (preamble lines, `require` lines and a blank line,
the kind prefix, the signature, the declarations, a blank line, the body, the `return`
statement). The printer is pure and total. An AST form without surface syntax
(`Psub`, `PappN`, a unary or binary operator without a token, a direct array access,
`Lasub`, the storage class `global`) prints as a token `#!…` that the parser
`JazzToInstrR.parseUnit` rejects, so the gate `printChecked` of `JazzRoundTrip` refuses
the unit.

Expressions print fully parenthesised (`(a OP b)`, `(c ? a : b)`), so every printed
expression is an atom of the parser's grammar. An assignment `x = x OP y` with `y` a
variable or a constant prints as `x OP= y;`, `x = 0 - y` with `y` a variable as
`x = -y;`, and `x = Parr_init n` as the comment `// x : zero-init array (omitted)`,
which the parser reads as whitespace. The storage class `regPtr false` prints `reg ptr`
and `regPtr true` prints `reg mut ptr`.

## Main definitions

* `printExpr`, `printLval`: expressions and l-values.
* `printJazzInstr`, `printCmd`: an instruction at an indentation, and the lines of a command.
* `printFn`: a function with its preamble, `require` lines and declarations.
* `print`: a unit, the concatenation of its functions.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Jazz

open CatCrypt.Crypto.Jasmin

/-! ## Tokens -/

/-- The token printed for an AST form `what` without surface syntax; the parser rejects
it in every position. -/
def noSyntax (what : String) : String := "#!" ++ what

/-- The word-type token `u8` … `u512`. -/
def wsTok : WSize → String
  | .U8 => "u8" | .U16 => "u16" | .U32 => "u32"
  | .U64 => "u64" | .U128 => "u128" | .U256 => "u256" | .U512 => "u512"

/-- The infix token of a binary operator with surface syntax. -/
def binOpTok : SOp2 → Option String
  | .Oor => some "||"
  | .Oand => some "&&"
  | .Oadd _ => some "+"
  | .Osub _ => some "-"
  | .Omul _ => some "*"
  | .Oland _ => some "&"
  | .Olor _ => some "|"
  | .Olxor _ => some "^"
  | .Olsl _ => some "<<"
  | .Olsr _ => some ">>"
  | .Oasr _ => some ">>s"
  | .Oeq _ => some "=="
  | .Oneq _ => some "!="
  | .Olt .Uextend _ => some "<"
  | .Ole .Uextend _ => some "<="
  | .Ogt .Uextend _ => some ">"
  | .Oge .Uextend _ => some ">="
  | .Olt .Sextend _ => some "<s"
  | .Ole .Sextend _ => some "<=s"
  | .Ogt .Sextend _ => some ">s"
  | .Oge .Sextend _ => some ">=s"
  | _ => none

/-- The token of a binary operator with a compound assignment `x OP= e`. -/
def compoundTok : SOp2 → Option String
  | .Oadd _ => some "+"
  | .Osub _ => some "-"
  | .Omul _ => some "*"
  | .Oland _ => some "&"
  | .Olor _ => some "|"
  | .Olxor _ => some "^"
  | .Olsl _ => some "<<"
  | .Olsr _ => some ">>"
  | .Oasr _ => some ">>s"
  | _ => none

/-! ## Expressions and l-values -/

/-- An expression; binary operators and conditionals are parenthesised, so the text is
an atom of the parser's grammar. -/
def printExpr : PExpr → String
  | .Pconst z => toString z
  | .Pbool b => if b then "true" else "false"
  | .Parr_init _ => noSyntax "arr_init"
  | .Pvar x => x.gv.var.vname
  | .Pget .AAscale _ x i => x.gv.var.vname ++ "[" ++ printExpr i ++ "]"
  | .Pget .AAdirect _ _ _ => noSyntax "direct_access"
  | .Psub .. => noSyntax "sub_array"
  | .Pload ws x o => "[:" ++ wsTok ws ++ " " ++ x.var.vname ++ " + " ++ printExpr o ++ "]"
  | .Papp1 (.Oword_of_int _) (.Pconst k) => toString k
  | .Papp1 (.Ozeroext wso _) e => "(" ++ toString wso.bits ++ "u) " ++ printExpr e
  | .Papp1 (.Olnot _) e => "!" ++ printExpr e
  | .Papp1 _ _ => noSyntax "unary_operator"
  | .Papp2 op a b =>
    match binOpTok op with
    | some t => "(" ++ printExpr a ++ " " ++ t ++ " " ++ printExpr b ++ ")"
    | none => noSyntax "binary_operator"
  | .PappN .. => noSyntax "nary_operator"
  | .Pif _ c a b => "(" ++ printExpr c ++ " ? " ++ printExpr a ++ " : " ++ printExpr b ++ ")"

/-- An l-value. -/
def printLval : LVal → String
  | .Lnone _ _ => "_"
  | .Lvar x => x.var.vname
  | .Lmem ws x o => "[:" ++ wsTok ws ++ " " ++ x.var.vname ++ " + " ++ printExpr o ++ "]"
  | .Laset .AAscale _ x i => x.var.vname ++ "[" ++ printExpr i ++ "]"
  | .Laset .AAdirect _ _ _ => noSyntax "direct_access"
  | .Lasub .. => noSyntax "sub_array"

/-- The right-hand side of an assignment `lhs = rhs;` and the compound form `x OP= y;`
when `e` is `x OP y` with `y` a variable or a constant. -/
def printAssign (ind : String) (lv : LVal) (e : PExpr) : String :=
  let general := ind ++ printLval lv ++ " = " ++ printExpr e ++ ";"
  match lv, e with
  | .Lvar x, .Parr_init _ => ind ++ "// " ++ x.var.vname ++ " : zero-init array (omitted)"
  | .Lvar x, .Papp2 (.Osub _) (.Pconst 0) (.Pvar y) =>
    ind ++ x.var.vname ++ " = -" ++ y.gv.var.vname ++ ";"
  | .Lvar x, .Papp2 op (.Pvar y) b =>
    let simple := match b with
      | .Pvar _ | .Pconst _ => true
      | _ => false
    match compoundTok op with
    | some t =>
      if simple && y.gv.var.vname == x.var.vname then
        ind ++ x.var.vname ++ " " ++ t ++ "= " ++ printExpr b ++ ";"
      else general
    | none => general
  | _, _ => general

/-- A comma-separated list of expressions. -/
def printJazzArgs (es : List PExpr) : String := String.intercalate ", " (es.map printExpr)

/-- `lhs = rhs;`, or `rhs;` when there is no output. -/
def printOutputs (ind : String) (lvs : List LVal) (rhs : String) : String :=
  if lvs.isEmpty then ind ++ rhs ++ ";"
  else ind ++ String.intercalate ", " (lvs.map printLval) ++ " = " ++ rhs ++ ";"

/-! ## Instructions -/

mutual
/-- An instruction at the indentation `ind`; a block's body is indented two more
spaces. -/
def printJazzInstr (ind : String) : InstrR → String
  | .Cassgn lv _ _ e => printAssign ind lv e
  | .Copn lvs _ (.Oasm op) es => printOutputs ind lvs ("#" ++ op.name ++ "(" ++ printJazzArgs es ++ ")")
  | .Cif c th el =>
    ind ++ "if " ++ printExpr c ++ " {\n" ++
      String.intercalate "\n" (printCmd (ind ++ "  ") th) ++ "\n" ++ ind ++ "} else {\n" ++
      String.intercalate "\n" (printCmd (ind ++ "  ") el) ++ "\n" ++ ind ++ "}"
  | .Cfor v r b =>
    let bounds := match r.dir with
      | .UpTo => toString r.lo ++ " to " ++ toString r.hi
      | .DownTo => toString r.hi ++ " downto " ++ toString r.lo
    ind ++ "for " ++ v.var.vname ++ " = " ++ bounds ++ " {\n" ++
      String.intercalate "\n" (printCmd (ind ++ "  ") b) ++ "\n" ++ ind ++ "}"
  | .Cwhile pre c post =>
    let head := if pre.isEmpty then ind ++ "while "
      else ind ++ "while {\n" ++ String.intercalate "\n" (printCmd (ind ++ "  ") pre) ++ "\n" ++
        ind ++ "} "
    head ++ printExpr c ++ " {\n" ++
      String.intercalate "\n" (printCmd (ind ++ "  ") post) ++ "\n" ++ ind ++ "}"
  | .Ccall _ lvs fn args => printOutputs ind lvs (fn.name ++ "(" ++ printJazzArgs args ++ ")")

/-- The lines of a command at the indentation `ind`. -/
def printCmd (ind : String) : List InstrR → List String
  | [] => []
  | i :: is => printJazzInstr ind i :: printCmd ind is
end

/-! ## Functions and units -/

/-- A storage class: `reg`, `reg ptr`, `reg mut ptr`, `stack`, `stack ptr`, `inline`. -/
def storageTok : Storage → String
  | .reg => "reg"
  | .stack => "stack"
  | .regPtr false => "reg ptr"
  | .regPtr true => "reg mut ptr"
  | .stackPtr => "stack ptr"
  | .inlineVar => "inline"
  | .global => noSyntax "global"

/-- A surface type: `uNN`, `bool`, `int` or `uNN[len]`. -/
def ptypeTok : PType → String
  | .word ws => wsTok ws
  | .bool => "bool"
  | .int => "int"
  | .arr ws len => wsTok ws ++ "[" ++ toString len ++ "]"

/-- A storage class followed by a surface type. -/
def slotTok (q : Storage × PType) : String := storageTok q.1 ++ " " ++ ptypeTok q.2

/-- The text before a function's name: one `#[a]` line per annotation and `fn `, or
`export fn `, or `inline fn `. -/
def kindPrefix : FnKind → String
  | .exportFn => "export fn "
  | .inlineFn => "inline fn "
  | .localFn annots => String.join (annots.map fun a => "#[" ++ a ++ "]\n") ++ "fn "

/-- A local declaration line `  storage type n₁ n₂ …;`. -/
def printDecl (d : Decl) : String :=
  "  " ++ slotTok (d.storage, d.ty) ++ " " ++ String.intercalate " " d.names ++ ";\n"

/-- A function: its preamble lines, its `require` lines followed by a blank line, the kind
prefix and signature, the declarations, a blank line, the body and the `return`
statement. -/
def printFn (f : JazzFn) : String :=
  let requires :=
    if f.requires.isEmpty then ""
    else String.intercalate "\n" (f.requires.map fun p => "require \"" ++ p ++ "\"") ++ "\n\n"
  let params := String.intercalate ", "
    ((f.fd.params.zip f.paramTys).map fun q => slotTok q.2 ++ " " ++ q.1.var.var.vname)
  let sigArrow :=
    if f.resultTys.isEmpty then "" else " -> " ++ String.intercalate ", " (f.resultTys.map slotTok)
  let retStmt :=
    if f.fd.results.isEmpty then ""
    else "\n\n  return " ++ String.intercalate ", " (f.fd.results.map (·.var.vname)) ++ ";"
  String.join (f.preamble.map (· ++ "\n")) ++ requires ++
    kindPrefix f.kind ++ f.fd.name.name ++ "(" ++ params ++ ")" ++ sigArrow ++ "\n" ++
    "{\n" ++ String.join (f.decls.map printDecl) ++ "\n" ++
    String.intercalate "\n" (printCmd "  " f.fd.body) ++ retStmt ++ "\n}\n"

/-- A unit: the concatenation of its functions. Extern signatures have no text. -/
def print (u : JazzUnit) : String := String.join (u.fns.map printFn)

end CatCrypt.Crypto.Jasmin.Jazz
