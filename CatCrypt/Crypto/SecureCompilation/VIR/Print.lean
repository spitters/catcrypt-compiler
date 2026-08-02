/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom

/-!
# Textual MLIR emission for VIR programs

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`Com.printModule` renders a `Com d Γ t` into a textual-MLIR `func.func`
module. Callers provide a `DialectPrint` instance for their dialect
giving per-op and per-type textual names.

Minimal subset compared to upstream opencompl/lean-mlir's
`Framework/Print.lean`:
- Single-result operations (mirrors our single-return `Com`).
- No regions.
- Function-level `func.func @f(%a : T, ...) -> R { ...; return %k }`.

Output example (for an arith-add of two i8 constants):
```mlir
func.func @main() -> i8 {
  %0 = "arith.constant"() {value = 3 : i8} : () -> i8
  %1 = "arith.constant"() {value = 4 : i8} : () -> i8
  %2 = "arith.addi"(%0, %1) : (i8, i8) -> i8
  return %2 : i8
}
```
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. DialectPrint typeclass -/

/-- A dialect's textual rendering:
    - `printOp` returns the quoted op name only (e.g., `"arith.addi"`)
    - `printAttrs` returns an attribute dict like ` {value = 3 : i8}`
      (with leading space) or empty string. -/
class DialectPrint (d : Dialect) [DialectSignature d] where
  printOp : d.Op → String
  printAttrs : d.Op → String := fun _ => ""
  printTy : d.Ty → String

/-! ## 2. SSA-name environment

A `PrintEnv` records the current SSA name counter and a mapping from
De Bruijn variables to SSA name indices. Printing traverses the `Com`
tree, incrementing the counter at each `var` binding. -/

namespace PrintEnv

/-- Per-variable SSA name map. Index 0 = most-recent binding. Names
    are strings so function arguments can use `arg0` while body values
    use `0`, `1`, ... (both prefixed with `%` at rendering time). -/
abbrev Names {d : Dialect} (Γ : Ctxt d) : Type := List String

/-- Initial: empty context. -/
def empty {d : Dialect} : Names (d := d) [] := []

/-- Extend names by a fresh SSA name. -/
def push {d : Dialect} {Γ : Ctxt d} {t : d.Ty} (names : Names Γ) (nm : String) :
    Names (t :: Γ) := nm :: names

/-- Look up a variable's SSA name (without `%` prefix). -/
def get {d : Dialect} {Γ : Ctxt d} {t : d.Ty} :
    (v : Ctxt.Var Γ t) → Names Γ → String
  | .here, n :: _ => n
  | .there v, _ :: rest => get v rest
  | _, [] => "0"

end PrintEnv

/-! ## 3. Printing expressions and programs -/

namespace Expr

/-- Print an argument list: `%0, %1, ...`. -/
def printArgs {d : Dialect} [DialectSignature d] {Γ : Ctxt d}
    {tys : List d.Ty} (args : HVector (fun ty => Ctxt.Var Γ ty) tys)
    (names : PrintEnv.Names Γ) : String :=
  let rec go : {tys : List d.Ty} → HVector (fun ty => Ctxt.Var Γ ty) tys →
      List String
    | [], .nil => []
    | _ :: _, .cons v rest => s!"%{PrintEnv.get v names}" :: go rest
  String.intercalate ", " (go args)

/-- Print the argument-types annotation: `(i8, i8)`. -/
def printArgTys {d : Dialect} [DialectSignature d] [DialectPrint d]
    (tys : List d.Ty) : String :=
  "(" ++ String.intercalate ", " (tys.map DialectPrint.printTy) ++ ")"

/-- Print an `Expr` as a line `%k = "dialect.op"(%a, %b) : (T, T) -> R`. -/
def printLine {d : Dialect} [DialectSignature d] [DialectPrint d]
    {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (names : PrintEnv.Names Γ)
    (resultName : String) : String :=
  let argStr := printArgs e.args names
  let argTys := printArgTys (DialectSignature.sig e.op)
  let retTy := DialectPrint.printTy t
  let attrs := DialectPrint.printAttrs e.op
  s!"  %{resultName} = {DialectPrint.printOp e.op}({argStr}){attrs} : {argTys} -> {retTy}"

end Expr

namespace Com

/-- Render a `Com` as a sequence of MLIR operation lines ending in
    `return`. Returns `(body_text, result_ssa_name)`. -/
def printBody {d : Dialect} [DialectSignature d] [DialectPrint d] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → PrintEnv.Names Γ → Nat →
    (String × String)
  | _, _, .ret v, names, _ => ("", PrintEnv.get v names)
  | _, _, .var e body, names, nextId =>
      let nm := toString nextId
      let line := Expr.printLine e names nm
      let (rest, retNm) := printBody body (PrintEnv.push names nm) (nextId + 1)
      (line ++ "\n" ++ rest, retNm)

/-- Render a `Com d [] t` as a complete `func.func` module. The function
    takes no arguments (empty context) and returns one value of type `t`. -/
def printModule {d : Dialect} [DialectSignature d] [DialectPrint d]
    {t : d.Ty} (c : Com d [] t) (funcName : String := "main") : String :=
  let retTy := DialectPrint.printTy t
  let (body, retNm) := printBody c PrintEnv.empty 0
  let nl := "\n"
  "func.func @" ++ funcName ++ "() -> " ++ retTy ++ " {" ++ nl
    ++ body ++ "  return %" ++ retNm ++ " : " ++ retTy ++ nl
    ++ "}" ++ nl

/-- Render a `Com d Γ t` as a `func.func` taking one argument per
    context entry. Argument SSA names are `%arg0, %arg1, ...` starting
    with the context's oldest binding (rightmost in the De Bruijn list). -/
def printModuleArgs {d : Dialect} [DialectSignature d] [DialectPrint d] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → (funcName : String) → String
  | Γ, t, c, funcName => Id.run do
    -- Build argument signature. Γ is innermost-first (De Bruijn).
    -- Convention: `.here` (index 0) is the LAST arg (newest push),
    -- so when listed oldest-first in the signature, `.here` = argN-1.
    let nArgs := Γ.length
    -- Argument declarations "%arg0 : T0, %arg1 : T1, ..." in oldest-first order.
    let rec buildArgDecls : Ctxt d → Nat → List String
      | [], _ => []
      | ty :: rest, i =>
          let rest' := buildArgDecls rest (i + 1)
          rest' ++ ["%arg" ++ toString (nArgs - 1 - i) ++ " : " ++ DialectPrint.printTy ty]
    let argDecls := buildArgDecls Γ 0
    -- Names list parallels `Γ`: index 0 = .here = newest = argN-1.
    let names : List String := (List.range nArgs).map (fun i => "arg" ++ toString i)
    -- Body SSA names start at 0 (distinct from arg* namespace).
    let (body, retNm) := printBody c names 0
    let retTy := DialectPrint.printTy t
    let nl := "\n"
    let argSig := String.intercalate ", " argDecls
    return "func.func @" ++ funcName ++ "(" ++ argSig ++ ") -> " ++ retTy ++ " {" ++ nl
      ++ body ++ "  return %" ++ retNm ++ " : " ++ retTy ++ nl
      ++ "}" ++ nl

/-- Print a full module including any `func.func` declarations for the
    external oracle leaves used by `extCall`s. -/
def printModuleWithExterns {d : Dialect} [DialectSignature d] [DialectPrint d]
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (funcName : String)
    (externs : List String) : String := Id.run do
    let nl := "\n"
    let externBlock := String.intercalate nl externs
    return externBlock ++ (if externs.isEmpty then "" else nl ++ nl)
      ++ printModuleArgs c funcName

end Com

/-! ## Multi-return printing (D2.3)

Print a `MultiReturnCom d Γ ts` as a `func.func` whose return type
is a tuple `(T₁, T₂, …)`. The body is a sequence of let-binds (same
shape as single-return) followed by `return %a, %b, … : T₁, T₂, …`.

This is the printer side of the multi-return VIR refactor that
addresses the writeup §5.5 CSE trap: emitting two correlated outputs
from a single `func.func` lets LLVM CSE shared work rather than
duplicating it across separate function boundaries. -/

namespace MultiReturnCom

open Ctxt (Var)

/-- Resolve an HVector of variables to a list of SSA names. -/
def lookupNames {d : Dialect} {Γ : Ctxt d} :
    {ts : List d.Ty} → HVector (fun ty => Var Γ ty) ts →
    PrintEnv.Names Γ → List String
  | [], .nil, _ => []
  | _ :: _, .cons v rest, names =>
    PrintEnv.get v names :: lookupNames rest names

/-- Render a `MultiReturnCom` as `(body_text, result_ssa_names)`. The
SSA-name list is in the same order as the `ts` index list. -/
def printBody {d : Dialect} [DialectSignature d] [DialectPrint d] :
    {Γ : Ctxt d} → {ts : List d.Ty} →
    MultiReturnCom d Γ ts → PrintEnv.Names Γ → Nat →
    (String × List String)
  | _, _, .ret vs, names, _ =>
    ("", lookupNames vs names)
  | _, _, .var e body, names, nextId =>
    let nm := toString nextId
    let line := Expr.printLine e names nm
    let (rest, retNms) := printBody body (PrintEnv.push names nm) (nextId + 1)
    (line ++ "\n" ++ rest, retNms)

/-- Render a `MultiReturnCom d [] ts` as a complete `func.func`
module with multi-return signature. -/
def printModule {d : Dialect} [DialectSignature d] [DialectPrint d]
    {ts : List d.Ty} (c : MultiReturnCom d [] ts)
    (funcName : String := "main") : String :=
  let retTys := ts.map DialectPrint.printTy
  let retTyStr := match retTys with
    | []    => "()"
    | [t]   => t
    | _     => "(" ++ String.intercalate ", " retTys ++ ")"
  let (body, retNms) := printBody c PrintEnv.empty 0
  let nl := "\n"
  let returnLine := match retNms, retTys with
    | [], _    => "  return"
    | nms, tys =>
      let valSig := String.intercalate ", " (nms.map ("%" ++ ·))
      let tySig := String.intercalate ", " tys
      "  return " ++ valSig ++ " : " ++ tySig
  "func.func @" ++ funcName ++ "() -> " ++ retTyStr ++ " {" ++ nl
    ++ body ++ returnLine ++ nl ++ "}" ++ nl

/-- Render a `MultiReturnCom d Γ ts` as a `func.func` taking one argument
per context entry and returning a tuple. Argument SSA names are
`%arg0, %arg1, ...` starting with the context's oldest binding
(rightmost in the De Bruijn list). Mirrors `Com.printModuleArgs` shape. -/
def printModuleArgs {d : Dialect} [DialectSignature d] [DialectPrint d] :
    {Γ : Ctxt d} → {ts : List d.Ty} →
    MultiReturnCom d Γ ts → (funcName : String) → String
  | Γ, ts, c, funcName => Id.run do
    let nArgs := Γ.length
    let rec buildArgDecls : Ctxt d → Nat → List String
      | [], _ => []
      | ty :: rest, i =>
          let rest' := buildArgDecls rest (i + 1)
          rest' ++ ["%arg" ++ toString (nArgs - 1 - i) ++ " : " ++ DialectPrint.printTy ty]
    let argDecls := buildArgDecls Γ 0
    let names : List String := (List.range nArgs).map (fun i => "arg" ++ toString i)
    let (body, retNms) := printBody c names 0
    let retTys := ts.map DialectPrint.printTy
    let retTyStr := match retTys with
      | []    => "()"
      | [t]   => t
      | _     => "(" ++ String.intercalate ", " retTys ++ ")"
    let nl := "\n"
    let argSig := String.intercalate ", " argDecls
    let returnLine := match retNms, retTys with
      | [], _    => "  return"
      | nms, tys =>
        let valSig := String.intercalate ", " (nms.map ("%" ++ ·))
        let tySig := String.intercalate ", " tys
        "  return " ++ valSig ++ " : " ++ tySig
    return "func.func @" ++ funcName ++ "(" ++ argSig ++ ") -> " ++ retTyStr ++ " {" ++ nl
      ++ body ++ returnLine ++ nl ++ "}" ++ nl

/-! Smoke note: `SmokeTest.pair` from `MultiReturnCom.lean` (a
two-output identity program `(x₀, x₁) ↦ (x₀, x₁)`) would print as
a `func.func @smoke() -> (bit, bit)` with a comma-separated return,
once a `DialectPrint` instance is supplied for `SmokeTest.D`. The
structural correctness of `printModule` is what's demonstrated by
the build alone. -/

end MultiReturnCom

end CatCrypt.Crypto.SecureCompilation.VIR
