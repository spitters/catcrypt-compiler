/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST

/-!
# Jasmin AST → safe-Rust source emitter

Sibling to `RustEmit.lean` (which emits from `LowCT`).  This module
takes a `Jasmin.FunDecl` / `Jasmin.JasminProg` and produces a Rust
source string.  Used to lift libjade-style Jasmin sources (SHA-256,
HMAC, ChaCha20, ML-KEM) into the wasm component without a separate
C-extraction step.

Coverage: handles the subset of the AST used by libjade hash / KEM /
scalar primitives — `Pconst`, `Pvar`, `Papp1`, `Papp2`, `Pget`,
`Pload`; `Lvar`, `Lmem`, `Laset`; `Cassgn`, `Copn` (asm rotate /
shift / bswap), `Cif`, `Cfor`, `Ccall`.  SIMD ops, `Cwhile`, `PappN`
emit a placeholder comment.
-/

namespace CatCrypt.Crypto.Jasmin.JasminToRustEmit

open CatCrypt.Crypto.Jasmin

/-! ## §1.  String helpers -/

private def LF : String := "\n"

/-- `n` spaces.  (Reimplemented locally because `String.replicate`'s
    visibility varies across Lean stdlib versions.) -/
private def spaces : Nat → String
  | 0     => ""
  | n + 1 => " " ++ spaces n

private def indent (n : Nat) (s : String) : String := spaces n ++ s

/-- Map a `WSize` to the Rust integer type name. -/
def rustWSize : WSize → String
  | .U8   => "u8"
  | .U16  => "u16"
  | .U32  => "u32"
  | .U64  => "u64"
  | .U128 => "u128"
  | .U256 => "[u8; 32]"
  | .U512 => "[u8; 64]"

/-- Map a Jasmin `SType` to a Rust type. -/
def rustSType : SType → String
  | .sbool      => "bool"
  | .sint       => "i64"
  | .sarr n     => "[u8; " ++ toString n ++ "]"
  | .sword ws   => rustWSize ws

/-- Variable-name escape (avoid Rust keywords). -/
def rustVar (v : Var) : String :=
  match v.vname with
  | "in"   => "in_"
  | "fn"   => "fn_"
  | "let"  => "let_"
  | "mut"  => "mut_"
  | "ref"  => "ref_"
  | "type" => "type_"
  | "match" => "match_"
  | "loop" => "loop_"
  | "move" => "move_"
  | "self" => "self_"
  | "use"  => "use_"
  | "mod"  => "mod_"
  | n      => n

def rustVarI (vi : VarI) : String := rustVar vi.var
def rustGVar (g : GVar) : String := rustVarI g.gv

/-! ## §2.  Operator dispatch -/

/-- Unary op: returns `(prefix, suffix)` so emit is `prefix expr suffix`. -/
def rustSOp1 : SOp1 → String × String
  | .Onot         => ("!(", ")")
  | .Olnot _      => ("!(", ")")
  | .Oneg ws      => ("(", ").wrapping_neg() as " ++ rustWSize ws)
  | .Oword_of_int ws => ("(", " as " ++ rustWSize ws ++ ")")
  | .Oint_of_word _  => ("(", " as i64)")
  | .Osignext wso _  => ("(", " as " ++ rustWSize wso ++ ")")
  | .Ozeroext wso _  => ("(", " as " ++ rustWSize wso ++ ")")

/-- Binary op: returns `none` for unhandled, `some (sym, isMethodLike)`
    where if isMethodLike then we emit `(e1).symm(e2)` else `(e1 sym e2)`. -/
def rustSOp2 : SOp2 → Option (String × Bool)
  | .Obeq         => some ("==", false)
  | .Oand         => some ("&&", false)
  | .Oor          => some ("||", false)
  | .Oadd _       => some (".wrapping_add", true)
  | .Osub _       => some (".wrapping_sub", true)
  | .Omul _       => some (".wrapping_mul", true)
  | .Oland _      => some ("&", false)
  | .Olor _       => some ("|", false)
  | .Olxor _      => some ("^", false)
  | .Olsr _       => some (">>", false)
  | .Olsl _       => some ("<<", false)
  | .Oasr _       => some (">>", false)
  | .Oeq _        => some ("==", false)
  | .Oneq _       => some ("!=", false)
  | .Olt _ _      => some ("<", false)
  | .Ole _ _      => some ("<=", false)
  | .Ogt _ _      => some (">", false)
  | .Oge _ _      => some (">=", false)
  | _             => none

/-! ## §3.  Expression printer -/

def ppPExpr : PExpr → String
  | .Pconst z     => toString z
  | .Pbool b      => if b then "true" else "false"
  | .Parr_init n  => "[0u8; " ++ toString n ++ "]"
  | .Pvar v       => rustGVar v
  | .Pget _ _ x idx =>
      rustGVar x ++ "[(" ++ ppPExpr idx ++ ") as usize]"
  | .Psub _ _ _ x idx =>
      rustGVar x ++ "[(" ++ ppPExpr idx ++ ") as usize..]"
  | .Pload _ x off =>
      "unsafe { *((" ++ rustVarI x ++ " + " ++ ppPExpr off ++ ") as *const _) }"
  | .Papp1 op e =>
      let (pre, post) := rustSOp1 op
      pre ++ ppPExpr e ++ post
  | .Papp2 op e1 e2 =>
      match rustSOp2 op with
      | none => "/* unhandled SOp2 */"
      | some (sym, true)  =>
          "(" ++ ppPExpr e1 ++ ")" ++ sym ++ "(" ++ ppPExpr e2 ++ ")"
      | some (sym, false) =>
          "(" ++ ppPExpr e1 ++ " " ++ sym ++ " " ++ ppPExpr e2 ++ ")"
  | .PappN _ _    => "/* unhandled PappN */"
  | .Pif _ c et ef =>
      "if " ++ ppPExpr c ++ " { " ++ ppPExpr et ++ " } else { " ++ ppPExpr ef ++ " }"

/-! ## §4.  L-value printer -/

def ppLVal : LVal → Option String
  | .Lnone _ _      => none
  | .Lvar x         => some (rustVarI x)
  | .Lmem _ x off   => some ("unsafe { *((" ++ rustVarI x ++ " + " ++ ppPExpr off ++ ") as *mut _) }")
  | .Laset _ _ x idx => some (rustVarI x ++ "[(" ++ ppPExpr idx ++ ") as usize]")
  | .Lasub _ _ _ x idx => some (rustVarI x ++ "[(" ++ ppPExpr idx ++ ") as usize..]")

/-- Returns `true` iff this LVal is a fresh `Lvar` (so we should emit
    `let mut name : T =` instead of plain assignment). -/
def isFreshLvar : LVal → Bool
  | .Lvar _ => true
  | _       => false

/-! ## §5.  Asm-op handling

libjade hashes use `#ROR_n`, `#SHR_n`, `#BSWAP_n` asm ops.  Detect by
asm-op name and emit the appropriate Rust intrinsic.  Anything else
emits a placeholder comment so a human can audit.
-/

/-- Word size encoded in the asm-op name: `#ROR_32` → "u32", etc.
    Defaults to "u64" if not recognised. -/
def asmOpWordTy (opName : String) : String :=
  if opName.endsWith "_32" then "u32"
  else if opName.endsWith "_16" then "u16"
  else if opName.endsWith "_8"  then "u8"
  else "u64"

/-- Format an assignment to `lv` of value `expr`.  If `lv` is a fresh
    `Lvar`, emit `let mut name : T = expr;` (with `T` inferred from
    `wordTy`); otherwise emit `lhs = expr;`. -/
def ppAsmAssign (lv : LVal) (wordTy : String) (expr : String) : String :=
  match ppLVal lv, lv with
  | none, _      => "let _ : " ++ wordTy ++ " = " ++ expr ++ ";"
  | some _,  .Lvar x => "let mut " ++ rustVarI x ++ " : " ++ wordTy ++ " = " ++ expr ++ ";"
  | some lhs, _      => lhs ++ " = " ++ expr ++ ";"

def ppAsmCopn (lvs : List LVal) (op : AsmOp) (es : List PExpr) : String :=
  let dest1 := lvs.head?
  let arg1  := es.head?.map ppPExpr
  let arg2  := (es.tail?.bind (·.head?)).map ppPExpr
  let ty    := asmOpWordTy op.name
  match op.name, dest1, arg1, arg2 with
  | "#ROR_32", some lv, some a, some c =>
      ppAsmAssign lv ty ("(" ++ a ++ ").rotate_right((" ++ c ++ ") as u32)")
  | "#ROR_64", some lv, some a, some c =>
      ppAsmAssign lv ty ("(" ++ a ++ ").rotate_right((" ++ c ++ ") as u32)")
  | "#ROL_32", some lv, some a, some c =>
      ppAsmAssign lv ty ("(" ++ a ++ ").rotate_left((" ++ c ++ ") as u32)")
  | "#ROL_64", some lv, some a, some c =>
      ppAsmAssign lv ty ("(" ++ a ++ ").rotate_left((" ++ c ++ ") as u32)")
  | "#SHR_32", some lv, some a, some c =>
      ppAsmAssign lv ty ("(" ++ a ++ ") >> (" ++ c ++ ")")
  | "#SHR_64", some lv, some a, some c =>
      ppAsmAssign lv ty ("(" ++ a ++ ") >> (" ++ c ++ ")")
  | "#BSWAP_32", some lv, some a, _ =>
      ppAsmAssign lv ty ("(" ++ a ++ ").swap_bytes()")
  | "#BSWAP_64", some lv, some a, _ =>
      ppAsmAssign lv ty ("(" ++ a ++ ").swap_bytes()")
  | name, _, _, _ =>
      "/* unhandled asm op " ++ name ++ " */"

/-! ## §6.  Instruction printer (with declared-name threading)

For Cassgn / Copn / Ccall to a variable, we need to know whether the
target has already been declared (so we emit `name = expr;`) or is
fresh (`let mut name : T = expr;`).  Without this, Rust scoping makes
every `let mut` inside a `for`-body a per-iteration shadow that
doesn't persist — wrong for SHA-256-style state mutation across
rounds.

`declared` is the set of names already in scope at the current
program point.  Function entry seeds it with `paramNames ++
resultNames` (results may or may not be pre-declared depending on
how the FunDecl is shaped).  `for`-loop variables are added on
entry to the body; bodies don't pollute the outer `declared`. -/

/-- Helper: emit a single line and (if the LVal is a fresh Lvar) add
    its name to `declared`.  Returns (line, updated declared). -/
private def ppOneLineAssign (declared : List String) (ind : Nat)
    (lv : LVal) (rhsTy : String) (rhsExpr : String) : String × List String :=
  match lv with
  | .Lvar x =>
      let name := rustVarI x
      if declared.contains name then
        (indent ind (name ++ " = " ++ rhsExpr ++ ";") ++ LF, declared)
      else
        (indent ind ("let mut " ++ name ++ " : " ++ rhsTy ++ " = " ++ rhsExpr ++ ";") ++ LF,
         name :: declared)
  | _ =>
      match ppLVal lv with
      | none      => (indent ind ("let _ : " ++ rhsTy ++ " = " ++ rhsExpr ++ ";") ++ LF, declared)
      | some lhs  => (indent ind (lhs ++ " = " ++ rhsExpr ++ ";") ++ LF, declared)

/-- Asm-op assignment (re-uses ppAsmCopn for the RHS expression but
    with assignment-vs-declaration aware of `declared`). -/
private def ppAsmStateful (declared : List String) (ind : Nat)
    (lvs : List LVal) (op : AsmOp) (es : List PExpr) : String × List String :=
  match lvs.head? with
  | none => (indent ind "/* asm op with no destination */" ++ LF, declared)
  | some (.Lvar x) =>
      let name := rustVarI x
      let ty := asmOpWordTy op.name
      let arg1 := es.head?.map ppPExpr
      let arg2 := (es.tail?.bind (·.head?)).map ppPExpr
      let rhsExpr :=
        match op.name, arg1, arg2 with
        | "#ROR_32", some a, some c => "(" ++ a ++ ").rotate_right((" ++ c ++ ") as u32)"
        | "#ROR_64", some a, some c => "(" ++ a ++ ").rotate_right((" ++ c ++ ") as u32)"
        | "#ROL_32", some a, some c => "(" ++ a ++ ").rotate_left((" ++ c ++ ") as u32)"
        | "#ROL_64", some a, some c => "(" ++ a ++ ").rotate_left((" ++ c ++ ") as u32)"
        | "#SHR_32", some a, some c => "(" ++ a ++ ") >> (" ++ c ++ ")"
        | "#SHR_64", some a, some c => "(" ++ a ++ ") >> (" ++ c ++ ")"
        | "#BSWAP_32", some a, _    => "(" ++ a ++ ").swap_bytes()"
        | "#BSWAP_64", some a, _    => "(" ++ a ++ ").swap_bytes()"
        | n, _, _ => "/* unhandled asm op " ++ n ++ " */"
      if declared.contains name then
        (indent ind (name ++ " = " ++ rhsExpr ++ ";") ++ LF, declared)
      else
        (indent ind ("let mut " ++ name ++ " : " ++ ty ++ " = " ++ rhsExpr ++ ";") ++ LF, name :: declared)
  | some lv =>
      -- Lmem / Laset / Lasub: write to existing slot.
      (indent ind (ppAsmCopn lvs op es) ++ LF, declared)

-- Foldl over a `Cmd`, threading `declared`.
mutual

partial def ppInstrSt (declared : List String) (ind : Nat) : InstrR → String × List String
  | .Cassgn lv _ ty e =>
      ppOneLineAssign declared ind lv (rustSType ty) (ppPExpr e)
  | .Copn lvs _ (.Oasm op) es =>
      ppAsmStateful declared ind lvs op es
  | .Cif cond cthen celse =>
      -- Each branch is scope-local; we discard the inner `declared`
      -- additions when leaving the block.
      let header := indent ind ("if " ++ ppPExpr cond ++ " {") ++ LF
      let (bodyT, _) := ppCmdSt declared (ind + 4) cthen
      let (bodyE, _) := ppCmdSt declared (ind + 4) celse
      let res :=
        if celse.isEmpty then
          header ++ bodyT ++ indent ind "}" ++ LF
        else
          header ++ bodyT ++ indent ind "} else {" ++ LF ++ bodyE ++ indent ind "}" ++ LF
      (res, declared)
  | .Cfor v range body =>
      let loopVar := rustVarI v
      let bodyDecl := loopVar :: declared
      let (body', _) := ppCmdSt bodyDecl (ind + 4) body
      -- Emit the range with the loop variable's word-size suffix so
      -- arithmetic methods like `.wrapping_sub` resolve unambiguously.
      let suf :=
        match v.var.vtype with
        | .sword ws => rustWSize ws
        | _         => "u32"
      let res :=
        indent ind ("for " ++ loopVar ++ " in " ++ toString range.lo ++ suf ++ ".." ++ toString range.hi ++ suf ++ " {") ++ LF ++
        body' ++
        indent ind "}" ++ LF
      (res, declared)
  | .Cwhile _ _ _ =>
      (indent ind "/* unhandled Cwhile */" ++ LF, declared)
  | .Ccall _ lvs fn args =>
      let argStr := String.intercalate ", " (args.map ppPExpr)
      let dests := lvs.filterMap (fun lv =>
        match lv with | .Lvar x => some x | _ => none)
      match dests with
      | [] =>
          (indent ind (fn.name ++ "(" ++ argStr ++ ");") ++ LF, declared)
      | [x] =>
          let name := rustVarI x
          if declared.contains name then
            (indent ind (name ++ " = " ++ fn.name ++ "(" ++ argStr ++ ");") ++ LF, declared)
          else
            (indent ind ("let mut " ++ name ++ " = " ++ fn.name ++ "(" ++ argStr ++ ");") ++ LF, name :: declared)
      | xs =>
          let names := xs.map rustVarI
          let nameStr := String.intercalate ", " names
          let allDeclared := names.all declared.contains
          if allDeclared then
            (indent ind ("(" ++ nameStr ++ ") = " ++ fn.name ++ "(" ++ argStr ++ ");") ++ LF, declared)
          else
            -- New tuple destruct.  All become declared.
            (indent ind ("let (" ++ nameStr ++ ") = " ++ fn.name ++ "(" ++ argStr ++ ");") ++ LF,
             names ++ declared)

partial def ppCmdSt (declared : List String) (ind : Nat) : Cmd → String × List String
  | []      => ("", declared)
  | i :: is =>
      let (s, d') := ppInstrSt declared ind i
      let (rest, d'') := ppCmdSt d' ind is
      (s ++ rest, d'')

end

/-- Backward-compat wrapper that discards declared-tracking. -/
def ppInstr (ind : Nat) (i : InstrR) : String :=
  (ppInstrSt [] ind i).1

/-! ## §7.  Function and program printer -/

/-- Look up a per-name Rust-type override; returns `none` if absent. -/
def lookupOverride (overrides : List (String × String)) (name : String) :
    Option String :=
  overrides.lookup name

/-- Emit a `FunDecl` as a Rust `pub fn`.

    `paramTypeOverrides` and `resultTypeOverrides` map variable names
    to verbatim Rust-type strings, used when the auto-derived type
    from `SType` is too coarse (e.g., `sarr 256` should emit as
    `&[u32; 64]` for SHA-256's W array, not `&[u8; 256]`).

    `attrs` is a list of attribute strings (e.g., `["#[inline]"]`)
    inserted before `pub fn`. -/
def ppFunDeclWith (paramTypeOverrides : List (String × String) := [])
                  (resultTypeOverrides : List (String × String) := [])
                  (attrs : List String := [])
                  (fd : FunDecl) : String :=
  let paramTy (p : FunParam) : String :=
    match lookupOverride paramTypeOverrides (rustVarI p.var) with
    | some t => t
    | none   => rustSType p.var.var.vtype
  let resultTy (r : VarI) : String :=
    match lookupOverride resultTypeOverrides (rustVarI r) with
    | some t => t
    | none   => rustSType r.var.vtype
  let paramStr := String.intercalate ", "
    (fd.params.map (fun p => rustVarI p.var ++ " : " ++ paramTy p))
  let resultTys := fd.results.map resultTy
  let retSig :=
    match resultTys with
    | []  => ""
    | [t] => " -> " ++ t
    | ts  => " -> (" ++ String.intercalate ", " ts ++ ")"
  -- Function parameters are pre-declared (they bind on entry); results
  -- are NOT — they're produced by the body's `let mut`s and named in
  -- the return tuple at the end.
  let initialDecl := fd.params.map (fun p => rustVarI p.var)
  let (body, _) := ppCmdSt initialDecl 4 fd.body
  let retLine :=
    match fd.results with
    | []  => ""
    | [r] => indent 4 (rustVarI r) ++ LF
    | rs  =>
        let names := String.intercalate ", " (rs.map rustVarI)
        indent 4 ("(" ++ names ++ ")") ++ LF
  let attrLines := String.intercalate "" (attrs.map (· ++ LF))
  attrLines ++
  "pub fn " ++ fd.name.name ++ "(" ++ paramStr ++ ")" ++ retSig ++ " {" ++ LF ++
  body ++
  retLine ++
  "}"

/-- Default emit (no overrides, no attrs).  Backward compatible. -/
def ppFunDecl (fd : FunDecl) : String := ppFunDeclWith [] [] [] fd

/-- Emit a whole `JasminProg` as concatenated `pub fn`s. -/
def ppJasminProg (p : JasminProg) : String :=
  String.intercalate (LF ++ LF) (p.funcs.map ppFunDecl)

/-- Write a `JasminProg` to a Rust source file. -/
def writeJasminProg (filename : String) (p : JasminProg) : IO Unit := do
  IO.FS.writeFile filename (ppJasminProg p)

end CatCrypt.Crypto.Jasmin.JasminToRustEmit
