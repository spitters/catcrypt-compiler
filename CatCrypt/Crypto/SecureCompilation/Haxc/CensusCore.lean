/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegions
import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainPre
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionStages
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionDiag
import HaxLean.TExpr
import HaxLean.FreeVars

set_option autoImplicit false
set_option compiler.extract_closed false

/-!
# The census of the hax compiler over crate functions: the stages and the table

The part of the census of `compileA` that names no extracted crate, imported by the emit
registry `EmitRegistry` (the row `census` of `lake exe catcrypt-emit`) and by the root
`HaxcMain` of `lake exe haxc`. A
crate (`Crate`) is a value: its name, its literal constants, the names of its declarations
and its functions with their typed extractions. For a function of a crate the module
records its role features, a role label, the first stage of `compileA` that refuses it, and
the firings of the optimiser rules along the stages it reaches.

## Main definitions

* `crateModule`: the module of a crate function, the input of `compileA`.
* `deriveAbi`: the System V layout of an extraction.
* `pipeRun`: the outcome of `compileA` on a module under a layout, with the place of a
  refusal.
* `censusRow`: the census line of one crate function (role, refusing stage, rule firings).
* `header`, `Row.render`, `summaries`: the table and its summary lines.

## Stages

`censusRow` runs the stages of `ComposeV1.compileA` in order:

1. the System V layout `deriveAbi` reads off the parameter prelude and the result type of the
   extraction: unsigned scalars of at most `64` bits in registers, arrays of `u64` words by
   pointer, the result in `%rax` or in an array parameter of its length (a `&mut` parameter
   first, otherwise a further output parameter), the result `()` of a body ending by reading
   its `&mut` array parameter (`tailVar`) in that parameter, the pair `([u64; n], u64)` of a
   body ending in `let y = a[k]; (a, y)` as the words of `a` and its word at `k`, the
   literal constants of the
   crate bound by `bindConsts`; any other parameter or result type is a refusal at stage `ABI`, and the
   stages are then run under the widened layout that admits signed and narrow scalars,
   Booleans and arrays of narrow words (columns `wideStage`, `wideConstruct`);
2. the module `crateModule c te` (the entry, the census functions of the crate it reaches by
   calls, each as `ModFn.ofTExpr` makes it, and the length of the longest chain of calls, at
   most `inlineRounds`, as depth), then the translation `haxToNF` of the module in its order:
   `crateArrOk` and `haxFrontShapeOk` on each callee (stage `module`), `haxFrontShapeOk` on
   the entry (stage `front`), `nfSrcProgC` at the call typing of the prepared callees (stage
   `impToNF`), and the inlining `HaxModule.inline?` (stage `inline`, with `inlineDiag`);
3. the chain `extChain` at the declared procedures `linkedDecls` of the module (stage
   `chain<i>:<name>`, the index from `0` and the name of the first refusing step that
   `Chain.runTrace` reports): `flattenTuples`, `outTy`, `dce`, `nfToCat`, `aegraph` at `catRules`, `map?`
   along `catToJasmin`, `fieldDialect` (a tagged field call at a modulus without a
   template), `lowerSelects`, `range`, `aegraph` at `jasminRules`;
4. the region back half `RegionBackend.compileRegion` under the export names `nfAbiNames`
   (`regionStage`): `resultTy` (the result type is neither `reg 64` nor `stackArr 64 m`),
   `regionExportableB`, `callFree`, `exportR`, `regionLprog`, `firstBody`,
   `encodeLfundefBytesChecked`, the first conjunct of the gate `regionCoB` that is `false`
   (`RegionBackend.regionCoStage`: `coClass`, `coCfgB`, `coEntryFix`, `renB`,
   `coResultName`, `coResultCopy`, `regionResultB`, `regMerge`, `regionNopB`, `fuseOKL`,
   `fuseResultName`, then the conjuncts of `renImageB`: `ownedCheckMC`, `idxInvCheckB`,
   `regionPrintedB`, `physImgB`, `regionImgB`, `frameOkB`, `entryB`), and the constant-time
   check `regionCtB` of the printed body.

The column `stage` is `accepted` exactly when `compileA` returns bytes on the module under the
layout; the stages name the place of a refusal (`pipeRun`).

The construct of a refusal by `haxToNF` is the refusal `HaxModule.refusal?` returns: at
`module` and `front` the side condition of `haxFrontShapeOk` the extraction fails
(`shapeCond`: `aNormTDenoteOk` of the prepared extraction, else `prepShapeB` of the form
chosen); at `impToNF` the first construct of the prepared body `nfBody` outside the domain of the front
(`FrontDomain.frontOut`); at `nfToCat` it is the first
operation of the program that `nfToCat` does not translate, or else the loop or literal whose
reading is a literal; at `map?` it is the list of operations of `catCryptDialect` that
`toJExprD` refuses (`mapDiag`); at a stage of `compileRegion` and at an accepted function it
is `-`.
Names free in the extraction that are neither parameters nor bound
constants are appended to the construct after `unbound:`.

## Rule firings

The firing columns are measured on the run of the layout the stages use (the derived layout,
else the widened one; column `layout`), on the programs the steps of the chain produce. A
group whose input program the run does not reach is `-` in every column.

* Groups `cat` (the program `nfToCat` returns, the input of the `aegraph` step at `catRules`)
  and `jas` (the program the step `range` returns, the input of the `aegraph` step at
  `jasminRules`) count over the
  let-bindings the pass `AegraphNF.aegraphOptNF` traverses, under the state the pass holds
  at each binding:
  - `bind`: the bindings;
  - `gvn`: value-numbering merges, the bindings whose hash-consed form `reduceOne` is an
    earlier variable;
  - `toVar`: the bindings whose extracted form `choose` is a variable (merges by value
    numbering or through a rule alternative);
  - `rewr`: the bindings whose extracted form is one binding of another operation or other
    arguments, or two bindings;
  - one column per rule of the rule set, named after it (`catRuleNames`,
    `jasminRuleNames`): the bindings at which the rule produces at least one alternative.

## Role features

One traversal of the typed extraction counts, over the syntactic occurrences of each call
`app f args` (a call inside a loop counts once):

* `crateCalls`: calls whose head `f` is a declaration of the crate's extraction, that is a
  name `f` with a declaration `f_texpr` in the extraction module (`crate_fns%`). This test
  comes first, so a crate function named `add` (as in `mlkem-hax`) is a crate call;
* `fieldOps`: calls whose head is one of the bare `primeir_hax::Field` method names that
  `PrimeirBuiltins.primeirBuiltins` interprets, `add`, `sub`, `mul`, `neg`, `square`,
  `double`, `inv`, and that is not a crate declaration. Integer arithmetic is never one of
  these: the extraction renders it under the capitalised trait names (`Add`, `Mul`,
  `BitXor#64`) or the width-suffixed method names (`wrapping_add#32`);
* `wordOps`, `idxOps`: calls whose head, with any `#<width>` suffix removed, is one of
  `Add`, `Sub`, `Mul`, `Div`, `Rem`, `Shl`, `Shr`, `BitAnd`, `BitOr`, `BitXor`, `Not`,
  `Neg`, `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_neg`, `overflowing_add`,
  `overflowing_sub`, `rotate_left`, `rotate_right`, `leading_zeros`, `trailing_zeros`,
  `count_ones`; the call counts in `idxOps` when its result type is `usize` (index and
  counter arithmetic) and in `wordOps` otherwise, including results of the unbounded type
  `int` that some extractions give Rust integers;
* `loops`: the loop nodes (`forLoop`, `forLoopRev`, `whileLoop`, `forFold`, `forFoldRev`,
  `whileFold` and their `Return` forms);
* `arrReads`: calls of `index`; `arrWrites`: calls of `array_update`, `index_mut`,
  `slice_update`, `copy_from_slice`;
* `earlyExit`: `1` when the body contains `earlyReturn`, `questionMark`, `break`,
  `cfBreak`, `cfBreakContinue` or a loop with return; `optResult`: `1` when the result type
  is an `Option` or a `Result`.

## Role rule

With `C = crateCalls`, `F = fieldOps`, `W = wordOps` and the threshold `T = 4`:

* `kernel` when `C = 0` and `F = 0` (a leaf; it includes a leaf with no arithmetic, such as
  a pure data move);
* `algebra` when `C = 0`, `F ≥ 1` and `W ≤ T` (a field operation or a thin wrapper of one);
* `orchestration` when `C ≥ 1` and `W ≤ T`;
* `mixed` when `C + F ≥ 1` and `W > T`.

## Output

A header line, then one tab-separated line per function, sorted by crate and then function,
with the columns `crate`, `function`, `crateCalls`, `fieldOps`, `wordOps`, `idxOps`, `loops`,
`arrReads`, `arrWrites`, `earlyExit`, `optResult`, `role`, `stage`, `construct`,
`wideStage`, `wideConstruct` (`-` on a row whose layout is derived), `layout` (`narrow`,
`wide` or `-`), then the firing columns `<group>.<column>` in the order of the groups `cat`
and `jas` above (`firingHeader`). Summary lines
follow, each beginning with
`summary`: functions accepted out of functions per role label; refusals per stage (the
stages of `compileA` before the chain, the chain steps by index and name, and the stages of
`compileRegion`); refusals per stage among the functions labelled `orchestration`; and the
total of each firing column over the functions that reach its group.

The column after the firing columns, `regionWhy`, is filled on a line whose run refuses at
the stage `ownedCheckMC`, `regionPrintedB`, `regionExportableB` or a stage of
`regionCoStages` of `compileRegion` and is empty on every other line. It is the first
component of that check that is `false` (`regionWhy`): `RegionDiag.ownedWhy` on the
reference `CoParts.ref` of the gate and the image of the printed body under the
renamed slot map, `RegionDiag.printedWhy` on the printed body, or
`RegionDiag.exportableWhy` on the structured program.

## A given layout

`censusRow` takes an optional layout; when it is supplied the stages run under it and the
column `layout` is `given`.

Closed-term extraction is off in this module, so module initialisation runs no stage of the
compiler; a root passes its population through the opaque identity `rt` at a runtime
value.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.Census

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.Hax.ImpToNF (impToNF hax64SigOf entryEnv litInt boundOk tupTy
  hax64NFScalar CrateFn crateSigOf entryCtx)
open CatCrypt.Crypto.Hax.NFToCat (nfToCat TRd)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionStages (regionStage regionCoStages)
open CatCrypt.Crypto.Hax.NFInline (crateLib noCrateCall crateInline?)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (RuleSet Tbl Defs Alt choose reduceOne
  stVar stOne stTwo consHom wk2 argLvls varLvl)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (homLiftApp aegraphOptNF)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open _root_.Hax (TExpr TExprKind ImpExpr ImpType ImpLit IntWidth Value)

/-! ## The declarations of an extraction module -/

open Lean Elab Term in
/-- `crate_fns% M` is the sorted list of names `f` such that the imported module `M` declares
    a constant whose last name component is `f_texpr`. -/
elab "crate_fns%" m:ident : term => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "module {m.getId} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let fs := names.toList.filterMap fun n =>
    match n with
    | .str _ s => if s.endsWith "_texpr" then some (s.take (s.length - 6)).toString else none
    | _ => none
  return toExpr (fs.eraseDups.mergeSort (· ≤ ·))

/-! ## Printing -/

/-- A short rendering of a source type. -/
def tyStr : Nat → ImpType → String
  | 0, _ => "_"
  | _ + 1, .bool => "bool"
  | _ + 1, .int => "int"
  | _ + 1, .uint w => w.toSuffix
  | _ + 1, .sint w => s!"i{w.bits}"
  | _ + 1, .unit => "()"
  | _ + 1, .str => "str"
  | n + 1, .tuple ts => "(" ++ ", ".intercalate (ts.map (tyStr n)) ++ ")"
  | n + 1, .option t => "Option<" ++ tyStr n t ++ ">"
  | n + 1, .result a b => "Result<" ++ tyStr n a ++ ", " ++ tyStr n b ++ ">"
  | _ + 1, .controlFlow _ _ => "ControlFlow"
  | _ + 1, .adt nm _ => nm
  | _ + 1, .fn _ _ => "fn"
  | n + 1, .ref t m => (if m then "&mut " else "&") ++ tyStr n t
  | n + 1, .slice t => "[" ++ tyStr n t ++ "]"
  | n + 1, .array t k => "[" ++ tyStr n t ++ "; " ++ toString k ++ "]"
  | _ + 1, .typeVar nm => nm
  | _ + 1, .unknown => "?"

/-- A short rendering of a type of `nfDialect`. -/
def nfTyStr : NfTy → String
  | .bit => "bit"
  | .unit => "unit"
  | .word w => s!"w{w}"
  | .arr n t => s!"[{nfTyStr t}; {n}]"
  | .pair a b => s!"({nfTyStr a}, {nfTyStr b})"
  | .uint W => W.toSuffix
  | .sint W => s!"i{W.bits}"
  | .int => "int"
  | .tnil => "()"
  | .tcons h t => s!"({nfTyStr h} :: {nfTyStr t})"
  | .slice t => s!"[{nfTyStr t}]"

/-- The name of the constructor of an expression, as a construct of the source. -/
def ctorName : ImpExpr → String
  | .lit _ => "literal"
  | .var _ => "variable"
  | .letBind .. => "let"
  | .lam .. => "closure"
  | .app .. => "call"
  | .tuple _ => "tuple"
  | .proj .. => "tuple projection"
  | .ifThenElse .. => "if-then-else"
  | .match_ .. => "match"
  | .unitVal => "unit"
  | .seq .. => "seq"
  | .borrow _ => "borrow"
  | .deref _ => "deref"
  | .assign .. => "assign"
  | .forLoop .. => "for loop"
  | .forLoopRev .. => "reverse for loop"
  | .whileLoop .. => "while loop"
  | .break_ _ => "break"
  | .continue_ => "continue"
  | .earlyReturn _ => "early return"
  | .questionMark _ => "question mark"
  | .forFold .. => "forFold"
  | .forFoldRev .. => "reverse forFold"
  | .whileFold .. => "whileFold"
  | .forFoldReturn .. => "forFold with return"
  | .forFoldRevReturn .. => "reverse forFold with return"
  | .whileFoldReturn .. => "whileFold with return"
  | .cfBreak _ => "cfBreak"
  | .cfContinue _ => "cfContinue"
  | .cfBreakContinue _ => "cfBreakContinue"
  | .typeAscription .. => "type ascription"

/-- A string with each tab and line break replaced by a space, so it fits one table cell. -/
def cell (s : String) : String :=
  s.map fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c

/-! ## Role features -/

/-- The role features of a function; the fields are the columns of the same names. -/
structure Feat where
  crateCalls : Nat := 0
  fieldOps : Nat := 0
  wordOps : Nat := 0
  idxOps : Nat := 0
  loops : Nat := 0
  arrReads : Nat := 0
  arrWrites : Nat := 0
  earlyExit : Bool := false
  optResult : Bool := false
  deriving Inhabited

/-- The bare `primeir_hax::Field` method names `PrimeirBuiltins.primeirBuiltins` interprets. -/
def fieldOpNames : List String := ["add", "sub", "mul", "neg", "square", "double", "inv"]

/-- The word-level arithmetic and bit operations, by head without its width suffix. -/
def wordOpNames : List String :=
  ["Add", "Sub", "Mul", "Div", "Rem", "Shl", "Shr", "BitAnd", "BitOr", "BitXor", "Not", "Neg",
    "wrapping_add", "wrapping_sub", "wrapping_mul", "wrapping_neg", "overflowing_add",
    "overflowing_sub", "rotate_left", "rotate_right", "leading_zeros", "trailing_zeros",
    "count_ones"]

/-- The array writes, by head. -/
def writeNames : List String := ["array_update", "index_mut", "slice_update", "copy_from_slice"]

/-- A call head without its `#<width>` suffix. -/
def headBase (f : String) : String := (f.splitOn "#").headD f

/-- Whether a type is `usize`. -/
def isUsize : ImpType → Bool
  | .uint .wsize => true
  | _ => false

/-- The immediate subexpressions of an expression. -/
def children : TExprKind → List TExpr
  | .lit _ | .var _ | .unitVal | .continue_ | .break_ none => []
  | .letBind _ v b => [v, b]
  | .lam _ b => [b]
  | .app _ as => as
  | .tuple es => es
  | .proj e _ => [e]
  | .ifThenElse c t e => [c, t, e]
  | .match_ s arms => s :: arms.map (·.2)
  | .seq a b => [a, b]
  | .borrow e | .deref e | .earlyReturn e | .questionMark e | .cfBreak e | .cfContinue e
  | .cfBreakContinue e | .ann e | .namedProj _ e | .break_ (some e) => [e]
  | .assign _ r => [r]
  | .forLoop _ lo hi b | .forLoopRev _ lo hi b | .forFold _ lo hi b | .forFoldRev _ lo hi b
  | .forFoldReturn _ lo hi b | .forFoldRevReturn _ lo hi b => [lo, hi, b]
  | .whileLoop c b | .whileFold c b | .whileFoldReturn c b => [c, b]

/-- Whether an expression node is a loop. -/
def isLoop : TExprKind → Bool
  | .forLoop .. | .forLoopRev .. | .whileLoop .. | .forFold .. | .forFoldRev .. | .whileFold ..
  | .forFoldReturn .. | .forFoldRevReturn .. | .whileFoldReturn .. => true
  | _ => false

/-- Whether an expression node is an early exit. -/
def isExit : TExprKind → Bool
  | .earlyReturn _ | .questionMark _ | .break_ _ | .cfBreak _ | .cfBreakContinue _
  | .forFoldReturn .. | .forFoldRevReturn .. | .whileFoldReturn .. => true
  | _ => false

/-- The features of one expression node, added to `a`; `defs` are the crate's declarations. -/
def stepFeat (defs : List String) (a : Feat) (k : TExprKind) (ty : ImpType) : Feat :=
  let a := if isLoop k then { a with loops := a.loops + 1 } else a
  let a := if isExit k then { a with earlyExit := true } else a
  match k with
  | .app f _ =>
      if defs.contains f then { a with crateCalls := a.crateCalls + 1 }
      else if fieldOpNames.contains f then { a with fieldOps := a.fieldOps + 1 }
      else if wordOpNames.contains (headBase f) then
        if isUsize ty then { a with idxOps := a.idxOps + 1 }
        else { a with wordOps := a.wordOps + 1 }
      else if f == "index" then { a with arrReads := a.arrReads + 1 }
      else if writeNames.contains (headBase f) then { a with arrWrites := a.arrWrites + 1 }
      else a
  | _ => a

/-- The features of an expression added to `a`, to depth `n`. -/
def featsAux (defs : List String) : Nat → Feat → TExpr → Feat
  | 0, a, _ => a
  | n + 1, a, .mk k ty => (children k).foldl (featsAux defs n) (stepFeat defs a k ty)

/-- The role features of an extraction, given the declarations of its crate. -/
def feats (defs : List String) (te : TExpr) : Feat :=
  let f := featsAux defs 100000 {} te
  let optRes := match te.ty with
    | .option _ | .result _ _ => true
    | _ => false
  { f with optResult := optRes }

/-- The threshold `T` of the role rule on `wordOps`. -/
def roleThreshold : Nat := 4

/-- The role label of a function from its features, by the rule of the module docstring. -/
def role (f : Feat) : String :=
  if f.crateCalls == 0 && f.fieldOps == 0 then "kernel"
  else if f.wordOps ≤ roleThreshold then
    if f.crateCalls == 0 then "algebra" else "orchestration"
  else "mixed"

/-- The role labels, in the order of the summary lines. -/
def roles : List String := ["kernel", "algebra", "orchestration", "mixed"]

/-! ## The layout of a function -/

/-- The System V argument registers, in order. -/
def regs : List String := ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"]

/-- The parameters of an extraction: its leading bindings `let x = x`, with their types. -/
def prelude : Nat → TExpr → List (String × ImpType)
  | 0, _ => []
  | n + 1, .mk (.letBind x (.mk (.var y) τ) b) _ => if x == y then (x, τ) :: prelude n b else []
  | _ + 1, _ => []

/-- The value of a constant whose extraction is a literal. -/
def constVal (c : TExpr) : Option Value :=
  match c.erase with
  | .lit (.int n) => some (.int n)
  | .lit (.uintLit _ n) => some (.int (n : Int))
  | .lit (.sintLit _ n) => some (.int n)
  | .lit (.bool b) => some (.bool b)
  | _ => none

/-- An element type of a word array: `u64` and `usize`, and, in the widened layout, every
    integer type of at most `64` bits. -/
def elemWord (wide : Bool) : ImpType → Bool
  | .uint .w64 => true
  | .uint .wsize => true
  | .uint w => wide && decide (w.bits ≤ 64)
  | .sint w => wide && decide (w.bits ≤ 64)
  | _ => false

/-- How a parameter of a type is passed: an unsigned scalar of at most `64` bits in a
    register, an array of words by pointer; in the widened layout also a signed scalar and a
    Boolean in a register. -/
def argKind? (wide : Bool) : ImpType → Option ArgKind
  | .uint w => if w.bits ≤ 64 then some .scalar else none
  | .sint w => if wide && decide (w.bits ≤ 64) then some .scalar else none
  | .bool => if wide then some .scalar else none
  | .array t n => if elemWord wide t then some (.words n) else none
  | .ref (.array t n) _ => if elemWord wide t then some (.words n) else none
  | _ => none

/-- The parameters of a layout, each in the next argument register. -/
def mkArgs (wide : Bool) : List (String × ImpType) → List String → Except String (List AbiArg)
  | [], _ => .ok []
  | _ :: _, [] => .error "more than 6 parameters"
  | (x, τ) :: ps, r :: rs =>
      match argKind? wide τ with
      | some k => (mkArgs wide ps rs).map fun l => (⟨x, r, k⟩ : AbiArg) :: l
      | none => .error s!"{x} : {tyStr 8 τ}"

/-- The read-back of a result of type `τ`: a scalar in `%rax`; an array of `n` words in a
    `&mut` parameter of length `n`, else in a parameter of length `n`, else in a further
    output parameter `_out`, the result buffer into which the back half copies a returned
    array that is not the buffer (`RegionBackend.regionCopy`); for the result `()` of a body that ends by reading its `&mut`
    array parameter `x` of length `n` (`tail = some x`, the in-place form), the `n` words at
    the pointer of `x`, whose source value is the final binding of `x`
    (`tailVar_denoteSpine`); for a pair result `([u64; n], u64)` of a body whose spine ends in
    `let y = a[k]; (a, y)` (`pair = some (a, k)`, `spineArrTail`) with `a` an array parameter
    of length `n` and `k` a scalar parameter, the pair `.tuple [.words r n, .wordAt r i]` of
    the words at the register `r` of `a` and the word at the index in the register `i` of `k`,
    which the pair stage of `compileA` reads back (`pairStage`). -/
def mkResult (wide : Bool) (ps : List (String × ImpType)) (args : List AbiArg)
    (tail : Option String) (pair : Option (String × String)) (τ : ImpType) :
    Except String (List AbiArg × ResultKind) :=
  match argKind? wide τ with
  | some .scalar => .ok (args, .reg "%rax")
  | some (.words n) =>
      let isMutN : String × ImpType → Bool := fun p =>
        match p.2 with
        | .ref (.array _ k) true => k == n
        | _ => false
      match ((ps.find? isMutN).bind fun p => args.find? (·.name == p.1)) <|>
          args.find? (·.kind == .words n) with
      | some a => .ok (args, .words a.reg n)
      | none =>
          match regs[args.length]? with
          | some r => .ok (args ++ [⟨"_out", r, .words n⟩], .words r n)
          | none => .error "no register for the output array"
  | none =>
      let inPlace : Option ResultKind := do
        if τ != .unit then none
        let x ← tail
        let p ← ps.find? (·.1 == x)
        let a ← args.find? (·.name == x)
        match p.2, a.kind with
        | .ref (.array _ n) true, .words k => if n == k then some (.words a.reg n) else none
        | _, _ => none
      let pairRes : Option ResultKind := do
        let (x, k) ← pair
        match τ with
        | .tuple [ta, tw] =>
            let a ← args.find? (·.name == x)
            let i ← args.find? (·.name == k)
            match argKind? wide ta, argKind? wide tw, a.kind, i.kind with
            | some (.words n), some .scalar, .words n', .scalar =>
                if n == n' then some (.tuple [.words a.reg n, .wordAt a.reg i.reg]) else none
            | _, _, _, _ => none
        | _ => none
      match inPlace <|> pairRes with
      | some rk => .ok (args, rk)
      | none => .error s!"result {tyStr 8 τ}"

/-- The System V layout of an extraction, with the literal constants of `consts` that occur
    free in it. -/
def deriveAbi (wide : Bool) (consts : List (String × TExpr)) (te : TExpr) :
    Except String AbiLayout := do
  let ps := prelude 64 te
  let args ← mkArgs wide ps regs
  let (args', rk) ← mkResult wide ps args (tailVar te.erase) (spineArrTail te.erase) te.ty
  let free := (_root_.Hax.freeVars te.erase).eraseDups
  let cs := consts.filterMap fun c =>
    if free.contains c.1 && !(ps.any (·.1 == c.1)) then (constVal c.2).map fun v => (c.1, v)
    else none
  pure (AbiLayout.mk args' cs rk [] (-256) (-8) [])

/-! ## The constructs of a refusal -/

/-- The first construct of the body `e` that `impToNF` refuses at the call typing `sig` from
    the parameters `ps` (`FrontDomain.frontRefusal?`). -/
def refusalStr (sig : String → List NfTy → Option NfTy) (ps : List (String × NfTy))
    (e : ImpExpr) : String :=
  match CatCrypt.Crypto.Hax.FrontDomain.frontRefusal? sig none (entryEnv ps) e with
  | some r => toString r
  | none => "no fragment obstacle"

/-- A loop whose trip count reads as a literal (a literal bound, or a name bound to a
    literal) or whose lower bound is not `0`: the loops `nfToCat` refuses. -/
def loopWarn : Nat → List String → ImpExpr → Option String
  | 0, _, _ => none
  | n + 1, ls, .letBind x (.lit _) b => loopWarn n (x :: ls) b
  | n + 1, ls, .letBind _ v b => loopWarn n ls v <|> loopWarn n ls b
  | n + 1, ls, .seq a b => loopWarn n ls a <|> loopWarn n ls b
  | n + 1, ls, .assign _ r => loopWarn n ls r
  | n + 1, ls, .typeAscription e _ => loopWarn n ls e
  | n + 1, ls, .forFold _ lo hi body =>
      match lo with
      | .lit (.int l) =>
          if l == 0 then
            match hi with
            | .lit _ => some "loop with a constant trip count"
            | .var y =>
                if ls.contains y then some "loop with a constant trip count"
                else loopWarn n ls body
            | _ => loopWarn n ls body
          else some "loop with a nonzero lower bound"
      | _ => some "loop with a nonzero lower bound"
  | _ + 1, _, _ => none

/-- The operations of a program of `nfDialect`. -/
def nfOps : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts → List NfOp
  | _, _, .ret _ => []
  | _, _, .var e k => (e.op : NfOp) :: nfOps k
  | _, _, .forLoop _ _ body k => nfOps body ++ nfOps k
  | _, _, .ifThenElse _ thn els k => nfOps thn ++ nfOps els ++ nfOps k
  | _, _, .whileLoop _ body k => nfOps body ++ nfOps k
  | _, _, .call _ _ k => nfOps k

/-- The reason `nfToCat` refuses an operation regardless of the readings of its arguments. -/
def catOpBad : NfOp → Option String
  | .named _ op => catOpBad op
  | .call f as _ =>
      if (hax64NFScalar ()).contains f || f == "select" then none
      else if f == "index" || f == "array_update" then
        match as with
        | .arr _ _ :: _ => none
        | t :: _ => some s!"{f} on {nfTyStr t}"
        | [] => some f
      else some s!"call {f}"
  | .ilit t v =>
      if (t = .int ∨ t = .word 64) ∧ 0 ≤ v ∧ v < 2 ^ 64 then none else some s!"literal {v} : {nfTyStr t}"
  | .ctr => none
  | .trip _ => none
  | .boundInt _ => none
  | .constUnit => some "unit value"
  | .constBit _ => some "bit literal"
  | op => some s!"operation {reprStr op}"

/-- The construct of a refusal by `nfToCat`. -/
def catDiag {Γ : Ctxt nfDialect} {ts : List NfTy} (q : NFProg nfDialect Γ ts) (e : ImpExpr) :
    String :=
  match (nfOps q).findSome? catOpBad with
  | some s => s
  | none =>
      match loopWarn 100000 [] e with
      | some s => s
      | none => "literal reading at a call"

/-- The bound on the depth of the module of a census function. -/
def inlineRounds : Nat := 4

/-- The reason the library of the crate `fs` has no body for the call of an operation: the
    construct `impToNF` refuses in the body of the callee, or the argument types or the
    result type of the call that differ from those of the callee. -/
def inlineOpDiag (fs : List CrateFn) : NfOp → Option String
  | .named _ o => inlineOpDiag fs o
  | .call f as r =>
      (fs.find? (·.name == f)).map fun c =>
        let sig := crateSigOf fs hax64SigOf
        match impToNF sig none (entryEnv c.params) c.body with
        | none => s!"{f}: {refusalStr sig c.params c.body}"
        | some o =>
            if entryCtx c.params ≠ as then
              s!"{f}({", ".intercalate (as.map nfTyStr)}) at parameters " ++
                s!"({", ".intercalate ((entryCtx c.params).map nfTyStr)})"
            else if o.t ≠ r then s!"{f}: result {nfTyStr o.t} at {nfTyStr r}"
            else s!"{f}: call left after the rounds of the module"
  | _ => none

/-- The construct of a refusal of the rounds of inlining at the library of `fs`: the first
    call of a function of `fs` in the program `p` after the rounds, with `inlineOpDiag`. -/
def inlineDiag (fs : List CrateFn) (n : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : String :=
  match (nfOps (p.inlineIter (crateLib fs) n)).findSome? (inlineOpDiag fs) with
  | some s => s
  | none => "a round of inlining refuses"

/-- The name of an operation of `catCryptDialect` in a refusal of the lowering to
    `jasminDialect`. -/
def catOpStr : CatCryptOp → String
  | .bvNot w => s!"bvNot {w}"
  | .not => "not"
  | .xor => "xor"
  | .and => "and"
  | .or => "or"
  | .eqBit => "eqBit"
  | .constBit _ => "constBit"
  | .constUnit => "constUnit"
  | .bvRol w _ => s!"bvRol {w}"
  | .bvAdd64 w => s!"bvAdd64 {w}"
  | .bvAdc w => s!"bvAdc {w}"
  | .bitToSword n => s!"bitToSword {n}"
  | .ite _ => "ite"
  | .extCall f _ _ => s!"extCall {f}"
  | _ => "operation"

/-- The let-bound operations of a program of `catCryptDialect` and of its regions that the
    lowering `toJExprD` refuses, by name. -/
def mapBad : {Γ : Ctxt catCryptDialect} → {ts : List CryptoSSA.CryptoTy} →
    NFProg catCryptDialect Γ ts → List String
  | _, _, .ret _ => []
  | _, _, .var e k =>
      (if (DialectToJasminCom.toJExprD e).isSome then [] else [catOpStr e.op]) ++ mapBad k
  | _, _, .forLoop _ _ body k => mapBad body ++ mapBad k
  | _, _, .ifThenElse _ thn els k => mapBad thn ++ mapBad els ++ mapBad k
  | _, _, .whileLoop _ body k => mapBad body ++ mapBad k
  | _, _, .call _ _ k => mapBad k

/-- The construct of a refusal by the step `map?`: the operations of the program the step
    receives (`nfToCat` on `NFProg.dce`, then the e-graph pass at `catRules`) that
    `toJExprD` refuses. -/
def mapDiag {Γ : Ctxt nfDialect} {ts : List NfTy} (q : NFProg nfDialect Γ ts) : String :=
  match nfToCat (NFProg.dce q) TRd.id with
  | none => "-"
  | some p =>
      let l := (mapBad (aegraphOptNF catRules p)).eraseDups
      if l.isEmpty then "-" else ",".intercalate l

/-! ## Rule firings of the e-graph pass -/

/-- The names of the rules of `catRules`, in order. -/
def catRuleNames : List String :=
  ["xor", "and", "or", "add", "sub", "mul", "shiftZero", "not", "idempotent", "selfCancel",
    "constFold"]

/-- The names of the rules of `jasminRules`, in order. -/
def jasminRuleNames : List String := ["bin", "constFold", "copy", "cmpOne"]

/-- The column names of `n` rules: the names `names`, then `rule<i>` for every further rule. -/
def ruleCols (names : List String) (n : Nat) : List String :=
  (List.range n).map fun i => names.getD i s!"rule{i}"

/-- The counts of a traversal of the e-graph pass: the columns `bind`, `gvn`, `toVar`, `rewr`
    of a group, and the count of each rule by its index. -/
structure Fire where
  bind : Nat := 0
  gvn : Nat := 0
  toVar : Nat := 0
  rewr : Nat := 0
  rules : List Nat := []
  deriving Inhabited

section Fire

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]

/-- The indices of the rules of `R` that produce at least one alternative for `e` under the
    definition table `D`. -/
def firedRules (R : RuleSet d) (D : Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    List Nat :=
  (R.rules.zipIdx.filter fun p => !(p.1.apply D e).isEmpty).map (·.2)

/-- The counts of the binding `e` under the state `S` of the pass, added to `a`. -/
def fireStep (R : RuleSet d) (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s)
    (a : Fire) : Fire :=
  let rules := (firedRules R S.2 e).foldl (fun l i => l.set i (l.getD i 0 + 1)) a.rules
  let gvn := match reduceOne R.pure S.1 e with
    | .var _ => 1
    | _ => 0
  let (tv, rw) := match choose R S e with
    | .var _ => (1, 0)
    | .one e2 => (0, if e2.op != e.op || argLvls e2.args != argLvls e.args then 1 else 0)
    | .two _ _ => (0, 1)
  { bind := a.bind + 1, gvn := a.gvn + gvn, toVar := a.toVar + tv, rewr := a.rewr + rw,
    rules := rules }

/-- The counts of the traversal `AegraphNF.nfGo R ρ S p`, added to `a`: each let-binding is
    counted under the state the traversal holds at it, and the traversal continues as
    `nfGo` does. -/
def nfFire (R : RuleSet d) : {Γ Δ : Ctxt d} → {ts : List d.Ty} → Ctxt.Hom Γ Δ →
    Tbl d × Defs d → NFProg d Γ ts → Fire → Fire
  | _, _, _, _, _, .ret _, a => a
  | _, Δ, _, ρ, S, .var (t := s) e k, a =>
      let a := fireStep R S (e.rename ρ) a
      match choose R S (e.rename ρ) with
      | .var w => nfFire R (consHom w ρ) (stVar R S (e.rename ρ) w) k a
      | .one e2 => nfFire R (Ctxt.Hom.lift ρ) (stOne R S (e.rename ρ) e2 Δ.length) k a
      | .two (s1 := s1) e1 e2 =>
          nfFire R (consHom (Ctxt.Var.here : Ctxt.Var (s :: s1 :: Δ) s) (wk2 ρ))
            (stTwo R S (e.rename ρ) e1 e2 Δ.length) k a
  | _, _, _, ρ, S, .forLoop (cs := cs) _ _ body k, a =>
      nfFire R (homLiftApp cs ρ) S k (nfFire R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body a)
  | _, _, _, ρ, S, .ifThenElse (rs := rs) _ thn els k, a =>
      nfFire R (homLiftApp rs ρ) S k (nfFire R ρ S els (nfFire R ρ S thn a))
  | _, _, _, ρ, S, .whileLoop (cs := cs) _ body k, a =>
      nfFire R (homLiftApp cs ρ) S k (nfFire R (homLiftApp cs ρ) S body a)
  | _, _, _, ρ, S, .call (rs := rs) _ _ k, a =>
      nfFire R (homLiftApp rs ρ) S k a

/-- The zero counts at the rule set `R`. -/
def Fire.zero (R : RuleSet d) : Fire := { rules := List.replicate R.rules.length 0 }

/-- The counts of the pass `aegraphOptNF R p`. -/
def aegraphFire (R : RuleSet d) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) : Fire :=
  nfFire R (Ctxt.Hom.id Γ) (∅, ∅) p (Fire.zero R)

end Fire

/-- The counts of the e-graph steps of `nfChain` on `p`, as `nfChain_run` states the chain:
    group `cat` on the program `nfToCat` returns from `NFProg.dce p`, group `jas` on the
    program the step `range` returns after the `aegraph` step at `catRules`, `map?` and
    `lowerSelects`. -/
def chainFire {Γ : Ctxt nfDialect} {t : NfTy} (p : NFProg nfDialect Γ [t]) :
    Option Fire × Option Fire :=
  if outTyB t = false then (none, none)
  else
    match nfToCat (NFProg.dce p) TRd.id with
    | none => (none, none)
    | some p' =>
        let c := some (aegraphFire catRules p')
        match NFProg.map? catToJasmin catToJasmin_regionTypes (aegraphOptNF catRules p')
            (fun v => v) with
        | none => (c, none)
        | some q =>
            (c, some (aegraphFire jasminRules
              (CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeNF (NFProg.lowerSelects q))))

/-! ## The stages of the region back half -/

section Region

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameNames frameMark
  frameOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (imgGateB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot
  boundFacts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute


/-- The reason for a refusal of `compileRegion σ a p` at the stage `stage`, one of
    `regionExportableB`, `regionPrintedB`, `ownedCheckMC` and the stages `regionCoStages`:
    `RegionDiag.exportableWhy` on `p`, or `RegionDiag.regionCoWhy` on the arguments of
    `regionCoB` (the code and returned operands of the webs `regionWebsAt` of the export) at
    the printed body and the allocation certificate of `regionLprogC`. The empty string at every other stage and when the
    export or the printed body does not exist. -/
def regionWhyBody (stage : String) (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) : String :=
  if stage == "regionExportableB" then (RegionDiag.exportableWhy p).getD ""
  else if stage == "regionPrintedB" || stage == "ownedCheckMC"
      || regionCoStages.contains stage then
    match exportR Γ.length a.fname p Γ.length 0,
        regionLprogC a p none (regionWebsEx σ exportReg) with
    | some r0, some (P, cert) =>
        let r := regionWebsAt (regionWebsEx σ exportReg) none r0
        match firstBody (regionPrinted P) with
        | none => ""
        | some b => RegionDiag.regionCoWhy stage σ exportReg b t r.code r.res cert
    | _, _ => ""
  else ""

/-- `regionWhyBody` at the result types `regionStage` passes to
    `RegionStages.regionTraceBody`; the empty
    string at every other result type. -/
def regionWhy (stage : String) (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} :
    {t : JasminTy} → NFProg jasminDialect Γ [t] → String
  | .stackArr 64 _, p => regionWhyBody stage σ a p
  | .reg 64, p => regionWhyBody stage σ a p
  | _, _ => ""

end Region

/-- The outcome of the stages on one function under one layout: the refusing stage (or
    `accepted`) with its construct, the counts of the firing groups the run reaches, and the
    reason `regionWhy` when the stage is a refusal of `compileRegion` at `ownedCheckMC`,
    `regionPrintedB`, `regionExportableB` or a stage of `regionCoStages` (empty
    otherwise). -/
structure Run where
  stage : String
  construct : String
  regionWhy : String := ""
  cat : Option Fire := none
  jas : Option Fire := none
  deriving Inhabited

/-- The stages after the source program, on the program `prog` of the result type `t`
    translated from the body `body`, in the order of `compileA`: the chain `extChain` at the
    declared procedures `D`, then the region back half `compileRegion` under the export
    names `nfAbiNames fname σ` (`regionStage`), with the firing counts. -/
def lateRun (fname : String) (σ : AbiLayout) (D : List CatCrypt.Crypto.Hax.NFToCat.ExtDecl)
    (body : ImpExpr) (t : NfTy)
    (prog : NFProg nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (abiEntry σ)) [t]) : Run :=
  let fires := chainFire prog
  match (extChain D _ t).runTrace prog with
  | .error (i, n) =>
      let con :=
        if n == "outTy" then s!"result {nfTyStr t}"
        else if n == "nfToCat" then catDiag (NFProg.dce prog) body
        else if n == "map?" then mapDiag prog
        else "-"
      { stage := s!"chain{i}:{n}", construct := con, cat := fires.1, jas := fires.2 }
  | .ok q =>
      let a := nfAbiNames fname σ
      let reg := regionStage σ a q
      let why : String :=
        if reg == "ownedCheckMC" || reg == "regionPrintedB" || reg == "regionExportableB"
            || regionCoStages.contains reg then regionWhy reg σ a q
        else ""
      { stage := reg, construct := "-", regionWhy := why, cat := fires.1, jas := fires.2 }

/-- The outcome of `compileA` on the module `m` under the layout `σ`, with the place of a
    refusal. The stage is `accepted` exactly when `compileA m σ fname` returns bytes. The
    stages before the chain are those of `HaxModule.refusal?`, in the order of `haxToNF`: `module` (`crateArrOk` on the
    prepared callees, `haxFrontShapeOk` on the extraction of each callee), `front`
    (`haxFrontShapeOk` on the entry with the constants of the layout bound), `impToNF`
    (`nfSrcProgC` at the call typing of the prepared callees), `inline` (`HaxModule.inline?`),
    then `lateRun`. The stages run on the module and the layout of the first stage of
    `compileA`, the pair stage `pairStage`. When `compileA` refuses and the stages name no
    refusal the stage is `compileA`; when `compileA` accepts and the stages name a refusal the
    construct reports it. -/
def pipeRun (m₀ : CatCrypt.Crypto.Hax.HaxModule) (fname : String) (σ₀ : AbiLayout) : Run :=
  let m := (pairStage m₀ σ₀).1
  let σ := (pairStage m₀ σ₀).2
  let te := m.entry
  let fs := m.prepared nfBody
  let tk := bindConsts σ.consts te
  let ps := abiEntry σ
  let body := nfBody tk
  let sig := crateSigOf (fs ++ m.linkedFns) hax64SigOf
  let free := (_root_.Hax.freeVars te.erase).eraseDups
  let unb := free.filter fun x => !(σ.args.any (·.name == x)) && !(σ.consts.any (·.1 == x))
  let tail := if unb.isEmpty then "" else s!"; unbound: {",".intercalate unb}"
  let d : Run :=
    match m.refusal? σ with
    | some (.inline _) =>
        match nfSrcProgC (fs ++ m.linkedFns) σ tk with
        | some ⟨_, prog⟩ => { stage := "inline", construct := inlineDiag fs m.depth prog }
        | none => { stage := "inline", construct := "-" }
    | some (.entryShape c) =>
        { stage := "front", construct := s!"{c}; nf: {refusalStr sig ps body}" }
    | some r => { stage := r.stage, construct := toString r }
    | none =>
        match haxToNF σ m with
        | some ⟨t, p⟩ =>
            lateRun fname σ (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) body t p
        | none => { stage := "haxToNF", construct := "-" }
  let acc := (compileA m₀ σ₀ fname).isSome
  let r : Run :=
    if acc then
      if d.stage == "accepted" then d
      else
        { d with stage := "accepted",
                 construct := s!"stages refuse at {d.stage}: {d.construct}" }
    else if d.stage == "accepted" then
      { d with stage := "compileA", construct := s!"stages accept: {d.construct}" }
    else d
  { r with construct := r.construct ++ tail }

/-! ## The census -/

/-- An extracted crate: its name, its literal constants, the names of its extraction's
    declarations, the census functions with their extractions, and the linked functions that
    stand for crate functions of the same name in the module of a census function. -/
structure Crate where
  name : String
  consts : List (String × TExpr)
  defs : List String
  fns : List (String × TExpr)
  linked : List CatCrypt.Crypto.Hax.LinkedFn := []

/-- One line of the census. -/
structure Row where
  crate : String
  fname : String
  feat : Feat
  role : String
  stage : String
  construct : String
  wideStage : String
  wideConstruct : String
  layout : String
  run : Option Run

/-- The heads of the calls `app f args` of an extraction, to depth `n`. -/
def callHeads : Nat → TExpr → List String
  | 0, _ => []
  | n + 1, .mk k _ =>
      (match k with
        | .app f _ => [f]
        | _ => []) ++ (children k).flatMap (callHeads n)

/-- The constants of a crate whose extraction is a literal, with their values. -/
def constVals (consts : List (String × TExpr)) : List (String × Value) :=
  consts.filterMap fun c => (constVal c.2).map fun v => (c.1, v)

/-- The census functions of the crate `c` that the extraction `te` calls, each once. -/
def calleesOf (c : Crate) (te : TExpr) : List String :=
  ((callHeads 100000 te).filter fun g => (c.fns.lookup g).isSome).eraseDups

/-- The levels of calls below the functions `level`, at most `n` of them: `level` when it is
    not empty, then the census functions the functions of `level` call, and so on. A function
    is in the level of each length of a chain of calls that reaches it, so the number of levels
    is the length of the longest chain, or `n` when a chain is longer. -/
def callLevels (c : Crate) : Nat → List String → List (List String)
  | 0, _ => []
  | n + 1, level =>
      if level.isEmpty then []
      else
        level :: callLevels c n
          (level.flatMap fun g => ((c.fns.lookup g).map (calleesOf c)).getD []).eraseDups

/-- **The module of a census function before linking**: the entry `te`, the census functions
    of the crate `c` the entry reaches by calls, each as `ModFn.ofTExprE` makes it with the
    literal constants of the crate (`modFnsE`), and as depth the length of the longest chain of
    calls, at most `inlineRounds`; or the refusal `ModuleRefusal.calleeShape` of the first
    reached function `ModFn.ofTExprE` does not make. A function that calls no census function
    has the module of a single function. The linked functions of `c` are not read. -/
def crateModuleBase (c : Crate) (te : TExpr) :
    Except CatCrypt.Crypto.Hax.FrontDomain.ModuleRefusal CatCrypt.Crypto.Hax.HaxModule :=
  let levels := callLevels c (inlineRounds + 1) (calleesOf c te)
  let cs := constVals c.consts
  let gs := (levels.flatMap fun l => l).eraseDups.filterMap fun g =>
    (c.fns.lookup g).map fun tg => (g, tg)
  (modFnsE cs gs).map fun fns =>
    { entry := te, fns := fns, depth := min levels.length inlineRounds }

/-- The module `m` with each linked function of `ls` whose name is that of a function of `m`
    linked in turn by `HaxModule.linkFn`. -/
def linkReached (ls : List CatCrypt.Crypto.Hax.LinkedFn) (m : CatCrypt.Crypto.Hax.HaxModule) :
    CatCrypt.Crypto.Hax.HaxModule :=
  (ls.filter fun l => m.fns.any (·.name == l.name)).foldl CatCrypt.Crypto.Hax.HaxModule.linkFn m

/-- **The module of a census function**: the module `crateModuleBase c te` with the linked
    functions of `c` that it reaches linked (`linkReached`). The entry is never linked. -/
def crateModule (c : Crate) (te : TExpr) :
    Except CatCrypt.Crypto.Hax.FrontDomain.ModuleRefusal CatCrypt.Crypto.Hax.HaxModule :=
  (crateModuleBase c te).map (linkReached c.linked)

/-- A crate with no linked functions has as module of a census function the module before
    linking. -/
theorem crateModule_linked_nil (c : Crate) (te : TExpr) (h : c.linked = []) :
    crateModule c te = crateModuleBase c te := by
  unfold crateModule
  rw [h]
  cases crateModuleBase c te <;> rfl

/-- **The module of a census function is a fold of `HaxModule.linkFn`** over the module of the
    crate without linked functions, the hypothesis shape of `compileModule_correct`. -/
theorem crateModule_eq_foldl (c : Crate) (te : TExpr) :
    crateModule c te = (crateModule { c with linked := [] } te).map fun m =>
      (c.linked.filter fun l => m.fns.any (·.name == l.name)).foldl
        CatCrypt.Crypto.Hax.HaxModule.linkFn m := by
  unfold crateModule
  show (crateModuleBase c te).map _ = ((crateModuleBase c te).map _).map _
  cases crateModuleBase c te <;> rfl

/-- The outcome of `compileA` on the module `crateModule c te` under the layout `σ`: `pipeRun`
    on the module, or the stage and the rendering of the refusal of `crateModule`. -/
def crateRun (c : Crate) (te : TExpr) (fname : String) (σ : AbiLayout) : Run :=
  match crateModule c te with
  | .ok m => pipeRun m fname σ
  | .error r => { stage := r.stage, construct := toString r }

/-- The census line of a function of a crate. The column `stage` is the outcome of
    `compileA` on the module `crateModule c te` (`crateRun`). The stages run under the
    layout `given` when it is supplied (column `layout` is then `given`), and otherwise under
    the layout `deriveAbi` reads off the extraction. -/
def censusRow (c : Crate) (fname : String) (te : TExpr) («given» : Option AbiLayout := none) :
    Row :=
  let f := feats c.defs te
  match «given» with
  | some σg =>
      let r := crateRun c te fname σg
      Row.mk c.name fname f (role f) r.stage r.construct "-" "-" "given" (some r)
  | none =>
  match deriveAbi false c.consts te with
  | .ok σ =>
      let r := crateRun c te fname σ
      Row.mk c.name fname f (role f) r.stage r.construct "-" "-" "narrow" (some r)
  | .error abi =>
      match deriveAbi true c.consts te with
      | .ok σw =>
          let r := crateRun c te fname σw
          Row.mk c.name fname f (role f) "ABI" abi r.stage r.construct "wide" (some r)
      | .error e => Row.mk c.name fname f (role f) "ABI" abi "ABI" e "-" none

/-- A flag as `0` or `1`. -/
def bit (b : Bool) : String := if b then "1" else "0"

/-- The columns `bind`, `gvn`, `toVar`, `rewr` of an e-graph group. -/
def fireBaseCols : List String := ["bind", "gvn", "toVar", "rewr"]

/-- The values of an e-graph group with `n` rules: `none` in every column when the group is
    not reached. -/
def fireVals (n : Nat) : Option Fire → List (Option Nat)
  | none => List.replicate (4 + n) none
  | some f =>
      [f.bind, f.gvn, f.toVar, f.rewr].map some ++
        (List.range n).map fun i => some (f.rules.getD i 0)

/-- The names of the firing columns, `<group>.<column>`. -/
def firingHeader : List String :=
  let catN := catRules.rules.length
  let jasN := jasminRules.rules.length
  (fireBaseCols ++ ruleCols catRuleNames catN).map ("cat." ++ ·) ++
    (fireBaseCols ++ ruleCols jasminRuleNames jasN).map ("jas." ++ ·)

/-- The values of the firing columns of a census line, in the order of `firingHeader`. -/
def Row.firing (r : Row) : List (Option Nat) :=
  let catN := catRules.rules.length
  let jasN := jasminRules.rules.length
  fireVals catN (r.run.bind (·.cat)) ++ fireVals jasN (r.run.bind (·.jas))

/-- A count, or `-` when its group is not reached. -/
def optStr : Option Nat → String
  | none => "-"
  | some n => toString n

/-- The tab-separated rendering of a census line. -/
def Row.render (r : Row) : String :=
  "\t".intercalate <|
    [r.crate, r.fname, toString r.feat.crateCalls, toString r.feat.fieldOps,
      toString r.feat.wordOps, toString r.feat.idxOps, toString r.feat.loops,
      toString r.feat.arrReads, toString r.feat.arrWrites, bit r.feat.earlyExit,
      bit r.feat.optResult, r.role, r.stage, cell r.construct, r.wideStage,
      cell r.wideConstruct, r.layout] ++ r.firing.map optStr ++
      [cell ((r.run.map (·.regionWhy)).getD "")]

/-- The column header of the table. -/
def header : String :=
  "\t".intercalate <|
    ["crate", "function", "crateCalls", "fieldOps", "wordOps", "idxOps", "loops", "arrReads",
      "arrWrites", "earlyExit", "optResult", "role", "stage", "construct", "wideStage",
      "wideConstruct", "layout"] ++ firingHeader ++
      ["regionWhy"]

/-- The stages of `compileA` that can refuse, in pipeline order: before the chain, the steps
    of `extChain` by index and name, and the stages of `compileRegion` before its gate
    `regionCoB` (`regionStage`); a conjunct of the gate that refuses is counted under its
    own name. -/
def stages : List String :=
  ["ABI", "module", "front", "impToNF", "inline", "chain0:flattenTuples", "chain1:outTy",
    "chain2:dce", "chain3:nfToCat", "chain4:aegraph", "chain5:map?", "chain6:montify",
    "chain7:fieldDialect", "chain8:lowerSelects", "chain9:range", "chain10:aegraph",
    "resultTy", "regionExportableB", "callFree", "exportR", "regionLprog", "firstBody",
    "encodeLfundefBytesChecked", "regionCtB"]

/-- The summary line of functions accepted out of functions per role label. -/
def acceptedByRole (rows : List Row) : String :=
  "\t".intercalate <| ["summary", "acceptedByRole"] ++ roles.map fun l =>
    let rs := rows.filter (·.role == l)
    s!"{l}={(rs.filter (·.stage == "accepted")).length}/{rs.length}"

/-- The summary line of refusals per stage, over the lines `rows`, labelled `label`. -/
def refusalsByStage (label : String) (rows : List Row) : String :=
  let other := ((rows.map (·.stage)).filter fun s => s != "accepted" && !stages.contains s)
    |>.eraseDups
  "\t".intercalate <| ["summary", label] ++ (stages ++ other).map fun s =>
    s!"{s}={(rows.filter (·.stage == s)).length}"

/-- The summary line of the total of each firing column over the lines that reach its
    group. -/
def firingTotals (rows : List Row) : String :=
  let tot := rows.foldl (fun acc r => List.zipWith (fun s v => s + v.getD 0) acc r.firing)
    (firingHeader.map fun _ => 0)
  "\t".intercalate <| ["summary", "firingTotals"] ++
    (List.zipWith (fun h n => s!"{h}={n}") firingHeader tot)

/-- The census lines sorted by crate and then function. -/
def sortRows (rows : List Row) : List Row :=
  rows.mergeSort fun a b =>
    decide (a.crate < b.crate) || (a.crate == b.crate && decide (a.fname ≤ b.fname))

/-- The summary lines of the table. -/
def summaries (rows : List Row) : List String :=
  [acceptedByRole rows, refusalsByStage "refusalsByStage" rows,
    refusalsByStage "refusalsByStageOrchestration" (rows.filter (·.role == "orchestration")),
    firingTotals rows]

/-- The identity, kept opaque to the compiler; the first argument makes each call distinct. -/
@[noinline] def rt {α : Type} (_ : Nat) (x : α) : α := x

end CatCrypt.Crypto.SecureCompilation.Haxc.Census
