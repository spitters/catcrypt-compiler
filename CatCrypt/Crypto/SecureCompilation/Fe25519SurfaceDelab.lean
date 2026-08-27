/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# `orch%` DELABORATOR — the inverse of the orchestration-surface elaborator

`Fe25519OrchestrationSyntax.lean` / `…Surface.lean` elaborate a Rust-like
concrete syntax (`orch% for … {| … |}`, the `{| … |}` block over `ostmt`, the
`scalar …` `SExpr` grammar) into the `LowCT` orchestration IR. This file builds
the **inverse**: `@[delab]` handlers that render a `LowCT` term back as that
surface, so an existing orchestration **displays** as the reviewable notation.

## Surface provenance (temporary local mirror)

The canonical surface lives in `Fe25519OrchestrationSyntax`/`…Surface`, but both
transitively `import Fe25519OrchestrationExample`, whose §3 `extCall`-denote
`rfl`s are orphan-rotted in the current tree (commit `7da1e2513` reverted the
`fe25519_add` `jasminExtSem` arm), so neither module builds. A delaborator needs
the target notations **declared** for its quotations to parse, so §1 re-declares
a byte-faithful mirror of exactly the surface fragment the two capstones
(`macAccumulate`, `ladderStep`) use. When the `Example` orphan is repaired, this
file re-points at the canonical surface by swapping the import and deleting §1's
re-declarations; the `@[delab]` handlers (§2) are unchanged.

## What is covered

`RFor` renders as the top-level `orch% for s in 0.. n {| … |}` (its `Nat` bound
may be a *variable*, which only the `term`-bound `orch%` form accepts); every
other constructor renders inside a `{| … |}` block: `RSeq` (flattened to the
`;`-list), `RCallN`, `RCall`, `RCallSwap`, `RScalarSet`, `RScalarSetExpr` (with
its `SExpr` sub-tree), `RIfNz`, `RForRuntime` (over `SVar`), `RSkip`. A
`Located ⟨name, _⟩` renders as its bare `"name"`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519SurfaceDelab

open CatCrypt.Crypto.Jasmin.LowCT
open Lean

/-! ## 1. Local mirror of the orchestration surface (see provenance note above) -/

/-- Right-fold a statement list into `RSeq`. -/
def orchSeq : List LowCT → LowCT
  | []      => .RSkip
  | [c]     => c
  | c :: cs => .RSeq c (orchSeq cs)

/-! ### 1a. The `SExpr` sub-syntax -/

declare_syntax_cat orchSExpr
syntax:max str : orchSExpr
syntax:max num : orchSExpr
syntax:max "(" orchSExpr ")" : orchSExpr
syntax:max "mulhi" "(" orchSExpr "," orchSExpr ")" : orchSExpr
syntax:70 orchSExpr:70 " * "  orchSExpr:71 : orchSExpr
syntax:69 orchSExpr:69 " & "  orchSExpr:70 : orchSExpr
syntax:68 orchSExpr:68 " << " orchSExpr:69 : orchSExpr
syntax:68 orchSExpr:68 " >> " orchSExpr:69 : orchSExpr
syntax:65 orchSExpr:65 " + "  orchSExpr:66 : orchSExpr
syntax:65 orchSExpr:65 " - "  orchSExpr:66 : orchSExpr
syntax:60 orchSExpr:60 " ^ "  orchSExpr:61 : orchSExpr

syntax:max "osexpr% " orchSExpr : term

macro_rules
  | `(osexpr% $s:str)          => `(SExpr.SVar $s)
  | `(osexpr% $n:num)          => `(SExpr.SLit $n)
  | `(osexpr% ( $e ))          => `(osexpr% $e)
  | `(osexpr% mulhi( $a , $b )) => `(SExpr.SMulHiU (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a * $b)         => `(SExpr.SMul (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a & $b)         => `(SExpr.SAnd (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a << $b)        => `(SExpr.SShl (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a >> $b)        => `(SExpr.SShr (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a + $b)         => `(SExpr.SAdd (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a - $b)         => `(SExpr.SSub (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a ^ $b)         => `(SExpr.SXor (osexpr% $a) (osexpr% $b))

/-! ### 1b. Orchestration statements + block term -/

declare_syntax_cat ostmt
syntax:min str ":=" "callN" ident "(" str,* ")" : ostmt
syntax:min str ":=" "call" ident "(" str,* ")" : ostmt
syntax:min "cswap" ident str str "(" str,* ")" : ostmt
syntax:min str ":=" "lit" num : ostmt
syntax:min str ":=" "scalar" orchSExpr : ostmt
syntax:min "if" str "!=" num term " else " term : ostmt
syntax:min "for" str "in" num ".." num term : ostmt
syntax:min "for" str "in" num ".." str term : ostmt
syntax:min "skip" : ostmt

syntax (name := orchBlockTerm) "{|" sepBy1(ostmt, ";") "|}" : term

macro_rules
  | `(ostmt| $dst:str := callN $fn:ident ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCallN $fnName
          [(⟨$dst, TowerType.TFp25519⟩ : Located)]
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])
  | `(ostmt| $dst:str := call $fn:ident ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCall $fnName
          (⟨$dst, TowerType.TFp25519⟩ : Located)
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])
  | `(ostmt| cswap $fn:ident $d1:str $d2:str ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCallSwap $fnName
          (⟨$d1, TowerType.TFp25519⟩ : Located)
          (⟨$d2, TowerType.TFp25519⟩ : Located)
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])
  | `(ostmt| $x:str := lit $n:num) => `(LowCT.RScalarSet $x $n)
  | `(ostmt| $x:str := scalar $e:orchSExpr) => `(LowCT.RScalarSetExpr $x (osexpr% $e))
  | `(ostmt| if $c:str != $_z:num $thenB:term else $elseB:term) =>
      `(LowCT.RIfNz $c $thenB $elseB)
  | `(ostmt| for $i:str in $_lo:num .. $n:num $body:term) =>
      `(LowCT.RFor $i $n $body)
  | `(ostmt| for $i:str in $_lo:num .. $b:str $body:term) =>
      `(LowCT.RForRuntime $i (SExpr.SVar $b) $body)
  | `(ostmt| skip) => `(LowCT.RSkip)
  | `({| $[$stmts];* |}) => do
      let stmtsT : Array (TSyntax `term) := stmts.map (fun s => ⟨s.raw⟩)
      `(orchSeq [$[$stmtsT],*])

/-! ### 1c. The top-level `orch%` loop form (variable bound) -/

declare_syntax_cat orchStmt
syntax:min str ":=" "callN" ident "(" str,* ")" : orchStmt
syntax:min str ":=" "call" ident "(" str,* ")" : orchStmt

macro_rules
  | `(orchStmt| $dst:str := callN $fn:ident ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCallN $fnName
          [(⟨$dst, TowerType.TFp25519⟩ : Located)]
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])
  | `(orchStmt| $dst:str := call $fn:ident ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCall $fnName
          (⟨$dst, TowerType.TFp25519⟩ : Located)
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])

syntax (name := orchFor) "orch% " "for " str " in " num ".." term:max " {|" sepBy1(orchStmt, ";") "|}" : term

macro_rules
  | `(orch% for $i:str in $_lo:num .. $n:term {| $[$stmts];* |}) => do
      let stmtsT : Array (TSyntax `term) := stmts.map (fun s => ⟨s.raw⟩)
      `(LowCT.RFor $i $n (orchSeq [$[$stmtsT],*]))

/-! ## 2. The delaborators (from the `LowCT` Expr) -/

open Lean.PrettyPrinter Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

/-- A string-literal Expr's value. -/
private def strLit? (e : Lean.Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- A `Located.mk name ty` Expr's bare name. -/
private def locName? (e : Lean.Expr) : Option String :=
  if e.getAppFn.constName? == some ``Located.mk then strLit? e.getAppArgs[0]! else none

/-- Flatten a `List.cons … List.nil` Expr into element Exprs. -/
private partial def listArgs (e : Lean.Expr) : List Lean.Expr :=
  match e.getAppFn.constName? with
  | some ``List.cons => let a := e.getAppArgs; a[1]! :: listArgs a[2]!
  | _ => []

/-- The `str` literals for a `List Located` Expr. -/
private def locNames (e : Lean.Expr) : Option (List String) :=
  (listArgs e).mapM locName?

/-- Make a `str` syntax literal. -/
private def mkStr (s : String) : TSyntax `str := Syntax.mkStrLit s

/-- Delaborate a `SExpr` Expr into the `orchSExpr` grammar. -/
private partial def delabSExpr (e : Lean.Expr) : DelabM (TSyntax `orchSExpr) := do
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``SExpr.SVar => do
      let some s := strLit? args[0]! | failure
      `(orchSExpr| $(mkStr s):str)
  | some ``SExpr.SLit => do
      let some n := args[0]!.nat? | failure
      `(orchSExpr| $(Syntax.mkNumLit (toString n)):num)
  | some ``SExpr.SAdd => do let a ← delabSExpr args[0]!; let b ← delabSExpr args[1]!; `(orchSExpr| $a + $b)
  | some ``SExpr.SSub => do let a ← delabSExpr args[0]!; let b ← delabSExpr args[1]!; `(orchSExpr| $a - $b)
  | some ``SExpr.SMul => do let a ← delabSExpr args[0]!; let b ← delabSExpr args[1]!; `(orchSExpr| $a * $b)
  | some ``SExpr.SShl => do let a ← delabSExpr args[0]!; let b ← delabSExpr args[1]!; `(orchSExpr| $a << $b)
  | some ``SExpr.SShr => do let a ← delabSExpr args[0]!; let b ← delabSExpr args[1]!; `(orchSExpr| $a >> $b)
  | some ``SExpr.SAnd => do let a ← delabSExpr args[0]!; let b ← delabSExpr args[1]!; `(orchSExpr| $a & $b)
  | some ``SExpr.SXor => do let a ← delabSExpr args[0]!; let b ← delabSExpr args[1]!; `(orchSExpr| $a ^ $b)
  | some ``SExpr.SMulHiU => do let a ← delabSExpr args[0]!; let b ← delabSExpr args[1]!; `(orchSExpr| mulhi($a, $b))
  | _ => failure

mutual

/-- Delaborate a `LowCT` Expr into one-or-more `ostmt`s (flattening `RSeq`). -/
private partial def delabOStmts (e : Lean.Expr) : DelabM (Array (TSyntax `ostmt)) := do
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``LowCT.RSeq => do
      let l ← delabOStmts args[0]!; let r ← delabOStmts args[1]!; return l ++ r
  | some ``LowCT.RSkip => return #[← `(ostmt| skip)]
  | some ``LowCT.RCallN => do
      let some fn := strLit? args[0]! | failure
      let some dsts := locNames args[1]! | failure
      let some srcs := locNames args[2]! | failure
      let some dst := dsts[0]? | failure
      let fnI := mkIdent (Name.mkSimple fn)
      let srcS := (srcs.map mkStr).toArray
      return #[← `(ostmt| $(mkStr dst):str := callN $fnI($srcS,*))]
  | some ``LowCT.RCall => do
      let some fn := strLit? args[0]! | failure
      let some dst := locName? args[1]! | failure
      let some srcs := locNames args[2]! | failure
      let fnI := mkIdent (Name.mkSimple fn)
      let srcS := (srcs.map mkStr).toArray
      return #[← `(ostmt| $(mkStr dst):str := call $fnI($srcS,*))]
  | some ``LowCT.RCallSwap => do
      let some fn := strLit? args[0]! | failure
      let some d1 := locName? args[1]! | failure
      let some d2 := locName? args[2]! | failure
      let some srcs := locNames args[3]! | failure
      let fnI := mkIdent (Name.mkSimple fn)
      let srcS := (srcs.map mkStr).toArray
      return #[← `(ostmt| cswap $fnI $(mkStr d1):str $(mkStr d2):str ($srcS,*))]
  | some ``LowCT.RScalarSet => do
      let some x := strLit? args[0]! | failure
      let some n := args[1]!.nat? | failure
      return #[← `(ostmt| $(mkStr x):str := lit $(Syntax.mkNumLit (toString n)):num)]
  | some ``LowCT.RScalarSetExpr => do
      let some x := strLit? args[0]! | failure
      let se ← delabSExpr args[1]!
      return #[← `(ostmt| $(mkStr x):str := scalar $se)]
  | some ``LowCT.RIfNz => do
      let some c := strLit? args[0]! | failure
      let thenB ← delabBlock args[1]!
      let elseB ← delabBlock args[2]!
      return #[← `(ostmt| if $(mkStr c):str != 0 $thenB else $elseB)]
  | some ``LowCT.RForRuntime => do
      let some x := strLit? args[0]! | failure
      -- surface expresses only `SVar b` bounds
      let bE := args[1]!
      unless bE.getAppFn.constName? == some ``SExpr.SVar do failure
      let some b := strLit? bE.getAppArgs[0]! | failure
      let body ← delabBlock args[2]!
      return #[← `(ostmt| for $(mkStr x):str in 0.. $(mkStr b):str $body)]
  | some ``LowCT.RFor => do
      -- literal-bound loop nested inside a block
      let some x := strLit? args[0]! | failure
      let some n := args[1]!.nat? | failure
      let body ← delabBlock args[2]!
      return #[← `(ostmt| for $(mkStr x):str in 0.. $(Syntax.mkNumLit (toString n)):num $body)]
  | _ => failure

/-- Delaborate a `LowCT` Expr into a `{| … |}` block term. -/
private partial def delabBlock (e : Lean.Expr) : DelabM Term := do
  let stmts ← delabOStmts e
  `({| $[$stmts];* |})

end

/-- Delaborate `RCallN`/`RCall` into an `orchStmt` (for the `orch%` loop body). -/
private def delabOrchStmt (e : Lean.Expr) : DelabM (TSyntax `orchStmt) := do
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``LowCT.RCallN => do
      let some fn := strLit? args[0]! | failure
      let some dsts := locNames args[1]! | failure
      let some srcs := locNames args[2]! | failure
      let some dst := dsts[0]? | failure
      let fnI := mkIdent (Name.mkSimple fn)
      let srcS := (srcs.map mkStr).toArray
      `(orchStmt| $(mkStr dst):str := callN $fnI($srcS,*))
  | some ``LowCT.RCall => do
      let some fn := strLit? args[0]! | failure
      let some dst := locName? args[1]! | failure
      let some srcs := locNames args[2]! | failure
      let fnI := mkIdent (Name.mkSimple fn)
      let srcS := (srcs.map mkStr).toArray
      `(orchStmt| $(mkStr dst):str := call $fnI($srcS,*))
  | _ => failure

/-- Flatten an `RSeq`/leaf body into `orchStmt`s (for the `orch%` loop body). -/
private partial def delabOrchStmts (e : Lean.Expr) : DelabM (Array (TSyntax `orchStmt)) := do
  match e.getAppFn.constName? with
  | some ``LowCT.RSeq =>
      let a := e.getAppArgs
      let l ← delabOrchStmts a[0]!; let r ← delabOrchStmts a[1]!; return l ++ r
  | _ => return #[← delabOrchStmt e]

/-- Top-level: an `RFor` renders as the `orch%` loop; its `Nat` bound is
    delaborated as a `term` (so a variable bound like `n` is admissible). -/
private def delabForTop : Delab := do
  let e ← getExpr
  unless e.getAppFn.constName? == some ``LowCT.RFor do failure
  let args := e.getAppArgs
  let some s := strLit? args[0]! | failure
  let nStx ← withNaryArg 1 delab
  let stmts ← delabOrchStmts args[2]!
  `(orch% for $(mkStr s):str in 0.. $nStx {| $[$stmts];* |})

/-- Top-level: any non-`RFor` orchestration constructor renders as a `{| … |}`
    block. -/
private def delabBlockTop : Delab := do
  let e ← getExpr
  delabBlock e

attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RFor] delabForTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RSeq] delabBlockTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RCall] delabBlockTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RCallN] delabBlockTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RCallSwap] delabBlockTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RScalarSet] delabBlockTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RScalarSetExpr] delabBlockTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RIfNz] delabBlockTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RForRuntime] delabBlockTop
attribute [delab app.CatCrypt.Crypto.Jasmin.LowCT.LowCT.RSkip] delabBlockTop

/-! ## 3. The fixed samples (copied ASTs; canonical defs live in the rot-blocked
`Example`/`Surface` modules) + round-trips -/

/-- `macAccumulate` — the mul-then-add loop (Example's shape). -/
def macAccumulate (n : Nat) : LowCT :=
  .RFor "i" n
    (.RSeq
      (.RCallN "fe25519_mul" [⟨"p", .TFp25519⟩] [⟨"a_i", .TFp25519⟩, ⟨"b_i", .TFp25519⟩])
      (.RCall "fe25519_add" ⟨"acc", .TFp25519⟩ [⟨"p", .TFp25519⟩]))

/-- `ladderStep` — the Montgomery-ladder inner step (Surface's shape). -/
def ladderStep : LowCT :=
  .RSeq
    (.RIfNz "swap"
      (.RSeq
        (.RCallSwap "fe25519_cswap" ⟨"x2", .TFp25519⟩ ⟨"x3", .TFp25519⟩ [⟨"swap", .TFp25519⟩])
        (.RCallSwap "fe25519_cswap" ⟨"z2", .TFp25519⟩ ⟨"z3", .TFp25519⟩ [⟨"swap", .TFp25519⟩]))
      .RSkip)
    (.RSeq (.RCallN "fe25519_add" [⟨"a", .TFp25519⟩] [⟨"x2", .TFp25519⟩, ⟨"z2", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_sub" [⟨"b", .TFp25519⟩] [⟨"x2", .TFp25519⟩, ⟨"z2", .TFp25519⟩])
      (.RScalarSetExpr "pos" (.SAdd (.SVar "i") (.SLit 1)))))

/-! ### Round-trip: `elab (delab t) = t` — the surface below is what the
delaborator renders; re-elaborating it returns the original term (`rfl`). -/

/-- **Round-trip (macAccumulate).** The delaborated `orch%` loop re-elaborates to
    `macAccumulate n`. -/
theorem macAccumulate_roundtrip (n : Nat) :
    (orch% for "i" in 0.. n {|
        "p"   := callN fe25519_mul("a_i", "b_i");
        "acc" := call  fe25519_add("p")
      |}) = macAccumulate n := rfl

/-- **Round-trip (ladderStep).** The delaborated `{| … |}` block re-elaborates to
    `ladderStep`. -/
theorem ladderStep_roundtrip :
    ({| if "swap" != 0 {|
           cswap fe25519_cswap "x2" "x3" ("swap");
           cswap fe25519_cswap "z2" "z3" ("swap")
         |} else {|
           skip
         |};
       "a" := callN fe25519_add("x2", "z2");
       "b" := callN fe25519_sub("x2", "z2");
       "pos" := scalar "i" + 1 |}) = ladderStep := rfl

/-! ### Display pins — the delaborator renders the raw `LowCT` as the surface. -/

set_option pp.unicode.fun true in
/--
info: def CatCrypt.Crypto.SecureCompilation.Fe25519SurfaceDelab.macAccumulate : ℕ → LowCT :=
fun n ↦ orch% for "i" in 0..n {|"p":=callN fe25519_mul("a_i", "b_i");"acc":=call fe25519_add("p")|}
-/
#guard_msgs (whitespace := lax) in
#print macAccumulate

/--
info: def CatCrypt.Crypto.SecureCompilation.Fe25519SurfaceDelab.ladderStep : LowCT :=
{|if"swap"!=0{|cswap fe25519_cswap"x2""x3"("swap");cswap fe25519_cswap"z2""z3"("swap")|} else
    {|skip|};"a":=callN fe25519_add("x2", "z2");"b":=callN fe25519_sub("x2", "z2");"pos":=scalar"i" + 1|}
-/
#guard_msgs (whitespace := lax) in
#print ladderStep

end CatCrypt.Crypto.SecureCompilation.Fe25519SurfaceDelab
