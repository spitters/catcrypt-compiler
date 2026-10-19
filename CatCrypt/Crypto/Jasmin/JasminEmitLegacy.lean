/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.JasminEmit

/-!
# The string renderer of `FunDecl`s

The renderer that formats each instruction shape of a `FunDecl` as a string, kept for
comparison with `Emit.emitFunDeclWithKind`, which prints through `Jazz.print`. The two
agree on every `FunDecl` they both render, except that this renderer prints an
assignment `x = Parr_init n` as the line `// x : zero-init array (omitted)` and an
intrinsic call without outputs as ` = #OP(..);`.

## Main definitions

* `ppArithExpr`, `emitInstr`, `emitBody`: expressions, instructions and bodies.
* `emitFunDeclCore`, `emitRequires`: the signature, declarations and body of a function,
  and its `require` lines.
* `emitFunDeclWithKind`, `emitFunDecl`, `emitFunDeclSpill`, `emitFunDeclRastack`,
  `emitFunDeclRastackSpill`, `emitFunDeclRaw`: a whole function.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Emit.Legacy

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Emit

set_option autoImplicit false

/-- A `PExpr` as a parenthesised Jasmin arithmetic expression: variables, constants,
    `Oword_of_int` constants, `Ozeroext` casts, the binary operators of `binOpStr` and
    `Olt`, and `AAscale` array reads; `none` otherwise. -/
partial def ppArithExpr : PExpr → Option String
  | .Pvar gv => some gv.gv.var.vname
  | .Pconst k => some (toString k)
  | .Papp1 (.Oword_of_int _) (.Pconst k) => some (toString k)
  | .Papp1 (.Ozeroext wso _) e => do
      let es ← ppArithExpr e
      some ("(" ++ toString (wsizeBits wso) ++ "u) " ++ es)
  | .Papp2 op a b => do
      let opS ← (match op with
        | .Olt _ _ => some "<"
        | _ => binOpStr op)
      let as ← ppArithExpr a
      let bs ← ppArithExpr b
      some ("(" ++ as ++ " " ++ opS ++ " " ++ bs ++ ")")
  | .Pget .AAscale _ arr idx => do
      let is ← ppArithExpr idx
      some (arr.gv.var.vname ++ "[" ++ is ++ "]")
  | _ => none

/-- One instruction as one or two Jasmin statements at the indentation `ind`; `none`
    for a shape outside the rendered subset. -/
partial def emitInstr (ind : String) : InstrR → Option String
  | .Cassgn (.Lvar x) _ _ (.Parr_init _) =>
      some (ind ++ "// " ++ x.var.vname ++ " : zero-init array (omitted)")
  | .Cassgn (.Lvar x) _ _ (.Pconst z) =>
      some (ind ++ x.var.vname ++ " = " ++ toString z ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp1 (.Oword_of_int _) (.Pconst z)) =>
      some (ind ++ x.var.vname ++ " = " ++ toString z ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Pvar y) =>
      some (ind ++ x.var.vname ++ " = " ++ y.gv.var.vname ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Pload ws base (.Pconst k)) =>
      some (ind ++ x.var.vname ++ " = [:" ++ wsizeTok ws ++ " " ++ base.var.vname ++
            " + " ++ toString k ++ "];")
  | .Cassgn (.Lmem ws base (.Pconst k)) _ _ (.Pvar src) =>
      some (ind ++ "[:" ++ wsizeTok ws ++ " " ++ base.var.vname ++ " + " ++ toString k ++
            "] = " ++ src.gv.var.vname ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp1 (.Olnot _) (.Pvar y)) =>
      let xn := x.var.vname
      let yn := y.gv.var.vname
      some (ind ++ xn ++ " = " ++ yn ++ ";\n" ++
            ind ++ xn ++ " = !" ++ xn ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp1 (.Ozeroext wso _) (.Pvar y)) =>
      some (ind ++ x.var.vname ++ " = (" ++ toString (wsizeBits wso) ++ "u) " ++
            y.gv.var.vname ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp2 op (.Pvar y) (.Pvar z)) =>
      match binOpStr op with
      | none =>
          (ppArithExpr (.Papp2 op (.Pvar y) (.Pvar z))).map
            (fun es => ind ++ x.var.vname ++ " = " ++ es ++ ";")
      | some opS =>
        let xn := x.var.vname
        let yn := y.gv.var.vname
        let zn := z.gv.var.vname
        if xn = yn then
          some (ind ++ xn ++ " " ++ opS ++ "= " ++ zn ++ ";")
        else if xn = zn then
          some (ind ++ xn ++ " = (" ++ yn ++ " " ++ opS ++ " " ++ zn ++ ");")
        else
          some (ind ++ xn ++ " = " ++ yn ++ ";\n" ++
                ind ++ xn ++ " " ++ opS ++ "= " ++ zn ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp2 op (.Pvar y) (.Pconst k)) =>
      match binOpStr op with
      | none =>
          (ppArithExpr (.Papp2 op (.Pvar y) (.Pconst k))).map
            (fun es => ind ++ x.var.vname ++ " = " ++ es ++ ";")
      | some opS =>
        let xn := x.var.vname
        let yn := y.gv.var.vname
        if xn = yn then
          some (ind ++ xn ++ " " ++ opS ++ "= " ++ toString k ++ ";")
        else
          some (ind ++ xn ++ " = " ++ yn ++ ";\n" ++
                ind ++ xn ++ " " ++ opS ++ "= " ++ toString k ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp2 (.Osub _) (.Pconst 0) (.Pvar y)) =>
      some (ind ++ x.var.vname ++ " = -" ++ y.gv.var.vname ++ ";")
  | .Cassgn (.Lvar x) _ _ (.Papp2 op (.Pconst k) (.Pvar y)) =>
      match binOpStr op with
      | none =>
          (ppArithExpr (.Papp2 op (.Pconst k) (.Pvar y))).map
            (fun es => ind ++ x.var.vname ++ " = " ++ es ++ ";")
      | some opS =>
        let xn := x.var.vname
        let yn := y.gv.var.vname
        if xn = yn then
          some (ind ++ xn ++ " = (" ++ toString k ++ " " ++ opS ++ " " ++ yn ++ ");")
        else
          some (ind ++ xn ++ " = " ++ toString k ++ ";\n" ++
                ind ++ xn ++ " " ++ opS ++ "= " ++ yn ++ ";")
  | .Copn lvs _ (.Oasm op) args => do
      let lvStrs ← lvs.mapM (fun
        | .Lnone _ _ => some "_"
        | .Lvar x    => some x.var.vname
        | _ => none)
      let argStrs ← args.mapM (fun
        | .Pvar gv => some gv.gv.var.vname
        | .Pconst k => some (toString k)
        | .Pload ws base (.Pconst k) =>
            some ("[:" ++ wsizeTok ws ++ " " ++ base.var.vname ++ " + " ++ toString k ++ "]")
        | _ => none)
      let lhs := String.intercalate ", " lvStrs
      let argStr := String.intercalate ", " argStrs
      some (ind ++ lhs ++ " = #" ++ op.name ++ "(" ++ argStr ++ ");")
  | .Cfor vi range body =>
      match range.dir with
      | .UpTo => do
        let bodyStrs ← body.mapM (emitInstr (ind ++ "  "))
        let bodyStr := String.intercalate "\n" bodyStrs
        some (ind ++ "for " ++ vi.var.vname ++ " = " ++
              toString range.lo ++ " to " ++ toString range.hi ++ " {\n" ++
              bodyStr ++ "\n" ++ ind ++ "}")
      | .DownTo => none
  | .Cwhile [] (.Papp2 (.Oneq _) (.Pvar gv) (.Pconst 0)) cafter =>
      do
      let bodyStrs ← cafter.mapM (emitInstr (ind ++ "  "))
      let bodyStr := String.intercalate "\n" bodyStrs
      some (ind ++ "while (" ++ gv.gv.var.vname ++ " != 0) {\n" ++
            bodyStr ++ "\n" ++ ind ++ "}")
  | .Cwhile [] (.Papp2 (.Oneq _) (.Pvar gv)
                  (.Papp1 (.Oword_of_int _) (.Pconst 0))) cafter =>
      do
      let bodyStrs ← cafter.mapM (emitInstr (ind ++ "  "))
      let bodyStr := String.intercalate "\n" bodyStrs
      some (ind ++ "while (" ++ gv.gv.var.vname ++ " != 0) {\n" ++
            bodyStr ++ "\n" ++ ind ++ "}")
  | .Cif (.Papp2 (.Oneq _) (.Pvar gv) (.Pconst 0)) th el => do
      let thStrs ← th.mapM (emitInstr (ind ++ "  "))
      let elStrs ← el.mapM (emitInstr (ind ++ "  "))
      let thStr := String.intercalate "\n" thStrs
      let elStr := String.intercalate "\n" elStrs
      some (ind ++ "if (" ++ gv.gv.var.vname ++ " != 0) {\n" ++
            thStr ++ "\n" ++ ind ++ "} else {\n" ++
            elStr ++ "\n" ++ ind ++ "}")
  | .Ccall _ii [.Lvar dst] fn [.Pvar a, .Pvar b] =>
      match binOpNameStr fn.name with
      | some opS =>
          let xn := dst.var.vname
          let yn := a.gv.var.vname
          let zn := b.gv.var.vname
          if xn = yn then
            some (ind ++ xn ++ " " ++ opS ++ "= " ++ zn ++ ";")
          else
            some (ind ++ xn ++ " = " ++ yn ++ ";\n" ++
                  ind ++ xn ++ " " ++ opS ++ "= " ++ zn ++ ";")
      | none =>
          some (ind ++ dst.var.vname ++ " = " ++ fn.name ++
                "(" ++ a.gv.var.vname ++ ", " ++ b.gv.var.vname ++ ");")
  | .Ccall _ii lvs fn args => do
      let lvStrs ← lvs.mapM (fun
        | .Lnone _ _ => some "_"
        | .Lvar x    => some x.var.vname
        | _ => none)
      let argStrs ← args.mapM (fun
        | .Pvar gv => some gv.gv.var.vname
        | .Pconst k => some (toString k)
        | .Pload ws base (.Pconst k) =>
            some ("[:" ++ wsizeTok ws ++ " " ++ base.var.vname ++ " + " ++ toString k ++ "]")
        | _ => none)
      let argStr := String.intercalate ", " argStrs
      if lvs.isEmpty then
        some (ind ++ fn.name ++ "(" ++ argStr ++ ");")
      else
        let lhs := String.intercalate ", " lvStrs
        some (ind ++ lhs ++ " = " ++ fn.name ++ "(" ++ argStr ++ ");")
  | .Cassgn (.Laset _ _ arr (.Pconst i)) _ _ (.Pvar src) =>
      some (ind ++ arr.var.vname ++ "[" ++ toString i ++ "] = " ++
            src.gv.var.vname ++ ";")
  | .Cassgn (.Lvar dst) _ _ (.Pget _ _ arr (.Pconst i)) =>
      some (ind ++ dst.var.vname ++ " = " ++ arr.gv.var.vname ++ "[" ++
            toString i ++ "];")
  | .Cassgn (.Laset .AAscale _ arr idx) _ _ (.Pvar src) => do
      let is ← ppArithExpr idx
      some (ind ++ arr.var.vname ++ "[" ++ is ++ "] = " ++ src.gv.var.vname ++ ";")
  | .Cassgn (.Laset .AAscale _ arr idx) _ _ (.Papp1 (.Ozeroext wso _) src) => do
      let is ← ppArithExpr idx
      let ss ← ppArithExpr src
      some (ind ++ arr.var.vname ++ "[" ++ is ++ "] = (" ++
            toString (wsizeBits wso) ++ "u) " ++ ss ++ ";")
  | .Cassgn (.Lvar dst) _ _ (.Pget .AAscale _ arr idx) => do
      let is ← ppArithExpr idx
      some (ind ++ dst.var.vname ++ " = " ++ arr.gv.var.vname ++ "[" ++ is ++ "];")
  | .Cassgn (.Lvar x) _ _ rhs => do
      let es ← ppArithExpr rhs
      some (ind ++ x.var.vname ++ " = " ++ es ++ ";")
  | _ => none

/-- All instructions, separated by newlines. -/
def emitBody (ind : String) (body : List InstrR) : Option String :=
  body.mapM (emitInstr ind) |>.map (String.intercalate "\n")

/-- The signature, the declarations, the body block and the body of a function, after
    `optimize` and `expandFlagCaptures`. -/
def emitFunDeclCore (fd : FunDecl) (spillScalars : Bool := false) :
    Option (String × String × String × String) := do
  let liveOutIn := fd.results.map (·.var)
  let (optBody0, optLO) := optimize liveOutIn fd.body
  let gprUsed := gprUsedNames optBody0
  let carryRegs := dedup (materializedCarryNames gprUsed optBody0)
  let limbWS := bodyLimbWidth optBody0
  let optBody := expandFlagCaptures limbWS gprUsed optBody0
  let body ← emitBody "  " optBody
  let declWidths := collectDeclWidths optBody
  let u32Scaled : List String :=
    let rec exprS : PExpr → List String
      | .Pget .AAscale .U32 arr idx => arr.gv.var.vname :: exprS idx
      | .Pget _ _ _ idx => exprS idx
      | .Psub .AAscale .U32 _ arr idx => arr.gv.var.vname :: exprS idx
      | .Papp1 _ e => exprS e
      | .Papp2 _ a b => exprS a ++ exprS b
      | .Pif _ c t e => exprS c ++ exprS t ++ exprS e
      | .Pload _ _ off => exprS off
      | _ => []
    let lvS : LVal → List String
      | .Laset .AAscale .U32 x idx => x.var.vname :: exprS idx
      | .Lasub .AAscale .U32 _ x idx => x.var.vname :: exprS idx
      | _ => []
    let rec goS : List InstrR → List String
      | [] => []
      | .Cassgn lv _ _ e :: rest => lvS lv ++ exprS e ++ goS rest
      | .Copn lvs _ _ es :: rest => lvs.flatMap lvS ++ es.flatMap exprS ++ goS rest
      | .Ccall _ lvs _ es :: rest => lvs.flatMap lvS ++ es.flatMap exprS ++ goS rest
      | .Cfor _ _ b :: rest => goS b ++ goS rest
      | .Cwhile cb _ ca :: rest => goS cb ++ goS ca ++ goS rest
      | .Cif _ th el :: rest => goS th ++ goS el ++ goS rest
    dedup (goS optBody)
  let ccallSarrU64 : List String :=
    let rec goC : List InstrR → List String
      | [] => []
      | .Ccall _ lvs _ es :: rest =>
          let lvN : LVal → List String
            | .Lvar x => match x.var.vtype with
                         | .sarr n => if n % 8 == 0 then [x.var.vname] else []
                         | _ => []
            | _ => []
          let esN : PExpr → List String
            | .Pvar gv => match gv.gv.var.vtype with
                          | .sarr n => if n % 8 == 0 then [gv.gv.var.vname] else []
                          | _ => []
            | _ => []
          lvs.flatMap lvN ++ es.flatMap esN ++ goC rest
      | .Cfor _ _ b :: rest => goC b ++ goC rest
      | .Cwhile cb _ ca :: rest => goC cb ++ goC ca ++ goC rest
      | .Cif _ th el :: rest => goC th ++ goC el ++ goC rest
      | _ :: rest => goC rest
    (goC optBody).filter (fun n => !u32Scaled.contains n)
  let u64Names := dedup (u64AccessedArrays optBody ++ ccallSarrU64)
  let ptrArrayTok : String → Nat → String := fun nm n =>
    if u64Names.contains nm ∧ n % 8 == 0 then "reg ptr u64[" ++ toString (n / 8) ++ "]"
    else if keccakU64ArrayBytes n then "reg ptr u64[" ++ toString (n / 8) ++ "]"
    else if n % 4 == 0 then "reg ptr u32[" ++ toString (n / 4) ++ "]"
    else "reg ptr u8[" ++ toString n ++ "]"
  let paramStr := String.intercalate ", "
    (fd.params.map (fun p =>
      match p.var.var.vtype with
      | .sword ws => "reg " ++ wsizeTok ws ++ " " ++ p.var.var.vname
      | .sarr n   => ptrArrayTok p.var.var.vname n ++ " " ++ p.var.var.vname
      | _         => "reg u64 " ++ p.var.var.vname))
  let retTypes := String.intercalate ", "
    (optLO.map (fun v => match v.vtype with
      | .sword ws => "reg " ++ wsizeTok ws
      | .sarr n   => ptrArrayTok v.vname n
      | _ => "reg u64"))
  let retNames := String.intercalate ", " (optLO.map (·.vname))
  let paramNames := fd.params.map (·.var.var.vname)
  let needsFlags := hasFlagCopn optBody
  let flagBank : List String := if needsFlags then ["of", "cf", "sf", "pf", "zf"] else []
  let flagNames : List String := flagBank.filter (fun n => !gprUsed.contains n)
  let carryFlagTmps := carryRegs.map carryFlagTmp
  let carryByteTmps := carryRegs.map carryByteTmp
  let loopIdxNames := dedup (collectLoopIdxNames optBody)
  let tmpNames := carryFlagTmps ++ carryByteTmps
  let arrayLocalsAll := collectArrayLocals optBody
  let arrayNames : List String :=
    dedup (arrayLocalsAll.map (·.1)) |>.filter
      (fun n => !paramNames.contains n && !flagNames.contains n
                && !loopIdxNames.contains n && !tmpNames.contains n)
  let locals := dedup (lhsNames optBody) |>.filter
                  (fun n => !paramNames.contains n && !flagNames.contains n
                            && !loopIdxNames.contains n && !tmpNames.contains n
                            && !arrayNames.contains n)
  let widthOrder : List WSize := [.U256, .U128, .U64, .U32, .U16, .U8]
  let resultNames := optLO.map (·.vname)
  let mkGroups (cls : String) (ns : List String) : String :=
    String.intercalate "" <| widthOrder.filterMap (fun w =>
      let names := ns.filter (fun n => declWidthOf declWidths n == w)
      if names.isEmpty then none
      else some ("  " ++ cls ++ wsizeTok w ++ " " ++ String.intercalate " " names ++ ";\n"))
  let localDecl :=
    if locals.isEmpty then ""
    else if spillScalars then
      let forced := dedup (regForcedNames optBody)
      let keepReg := fun n => resultNames.contains n || forced.contains n
      let regKeep := locals.filter keepReg
      let stackSpill := locals.filter (fun n => !keepReg n)
      mkGroups "reg " regKeep ++ mkGroups "stack " stackSpill
    else
      mkGroups "reg " locals
  let u32Arrays := dedup (u32AccessedArrays optBody) |>.filter
                     (fun n => !u64Names.contains n)
  let arrayDecl :=
    String.intercalate "" <| arrayNames.map (fun name =>
      let n := (arrayLocalsAll.find? (·.1 = name)).map (·.2) |>.getD 0
      stackArrDeclW (u32Arrays.contains name) name n)
  let loopIdxDecl :=
    if loopIdxNames.isEmpty then ""
    else "  inline int " ++ String.intercalate " " loopIdxNames ++ ";\n"
  let boolNames := flagNames ++ carryFlagTmps
  let flagDecl :=
    if boolNames.isEmpty then ""
    else "  reg bool " ++ String.intercalate " " boolNames ++ ";\n"
  let byteDecl :=
    if carryByteTmps.isEmpty then ""
    else "  reg u8 " ++ String.intercalate " " carryByteTmps ++ ";\n"
  let sigArrow := if optLO.isEmpty then "" else " -> " ++ retTypes
  let retStmt  := if optLO.isEmpty then "" else "\n\n  return " ++ retNames ++ ";"
  let header := "(" ++ paramStr ++ ")" ++ sigArrow
  let decls  := flagDecl ++ byteDecl ++ localDecl ++ arrayDecl ++ loopIdxDecl
  let bodyBlock := "{\n" ++ decls ++ "\n" ++ body ++ retStmt ++ "\n}\n"
  some (header, decls, bodyBlock, body)

/-- The `require "..."` lines of a body, one per distinct callee with an entry in
    `kernelRequireMap`, followed by a blank line; empty when there is none. -/
def emitRequires (body : List InstrR) : String :=
  let names := dedup (collectCallNames body)
  let paths := names.filterMap kernelRequireMap
  if paths.isEmpty then ""
  else
    String.intercalate "\n" (paths.map (fun p => "require \"" ++ p ++ "\"")) ++ "\n\n"

/-- A function with the banner line, its `require` lines and the prefix of `kind`. -/
def emitFunDeclWithKind (kind : FnKind) (fd : FunDecl)
    (spillScalars : Bool := false) : Option String := do
  let (header, _decls, bodyBlock, _body) ← emitFunDeclCore fd spillScalars
  let requires := emitRequires fd.body
  some <|
    "// Auto-generated from CatCrypt Jasmin AST. Do not edit by hand.\n" ++
    requires ++
    fnKindPrefix kind ++ fd.name.name ++ header ++ "\n" ++ bodyBlock

/-- An `export fn`. -/
def emitFunDecl (fd : FunDecl) : Option String :=
  emitFunDeclWithKind .Export fd

/-- An `export fn` with stack-spilled scalar locals. -/
def emitFunDeclSpill (fd : FunDecl) : Option String :=
  emitFunDeclWithKind .Export fd (spillScalars := true)

/-- A `#[returnaddress=stack] fn`. -/
def emitFunDeclRastack (fd : FunDecl) : Option String :=
  emitFunDeclWithKind .SubroutineRastack fd

/-- A `#[returnaddress=stack] fn` with stack-spilled scalar locals. -/
def emitFunDeclRastackSpill (fd : FunDecl) : Option String :=
  emitFunDeclWithKind .SubroutineRastack fd (spillScalars := true)

/-- An `export fn` rendered without `optimize`, every parameter and local `reg u64`. -/
def emitFunDeclRaw (fd : FunDecl) : Option String := do
  let body ← emitBody "  " fd.body
  let paramStr := String.intercalate ", "
    (fd.params.map (fun p => "reg u64 " ++ p.var.var.vname))
  let paramNames := fd.params.map (·.var.var.vname)
  let locals := dedup (lhsNames fd.body) |>.filter
                  (fun n => !paramNames.contains n)
  let localDecl :=
    if locals.isEmpty then ""
    else "  reg u64 " ++ String.intercalate " " locals ++ ";\n\n"
  let retName := (fd.results.head?).map (·.var.vname) |>.getD "r"
  some <|
    "// Auto-generated (raw, no optimization) from CatCrypt Jasmin AST.\n" ++
    "export fn " ++ fd.name.name ++ "(" ++ paramStr ++ ") -> reg u64\n" ++
    "{\n" ++ localDecl ++ body ++ "\n\n  return " ++ retName ++ ";\n}\n"

end CatCrypt.Crypto.Jasmin.Emit.Legacy
