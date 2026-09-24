/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import CatCrypt.Crypto.Jasmin.JincToCom
public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce

/-!
# `.jinc` leaf to `LowCT` (front: untyped AST → rolled-loop source)

Translates a parsed Jasmin leaf (`JincToCom.JFun`) into `LowCT`, the source form
of the rolled-loop front. A source `for` becomes `LowCT.RFor` and a source
`while` becomes `LowCT.RWhileNz`, so a loop reaches the owned backend as a loop
node. `JincElab` is the other target for the same `JFun` and unrolls its `for`
into a binding per iteration.

`renderJFunLeaf` carries a leaf through
`FrontRoutePlan.compileLoop` → `frontLoopBodyJ` → `cryptoDialectToJasminCom` →
`ComL.toLprogPhysAbi` → `LprogOptPipeline.renderOwned`, the route
`CatCrypt.Crypto.MLDSA.PolyLeafFrontEmit` uses.

## Representation

Every array cell is one 64-bit word, whatever the source element width: an
index `a[i]` addresses word `i` of a `memref`. A caller of a rendered leaf
therefore passes `uint64_t *` where the `.jinc` header says `u32[n]`. Source
width casts `(Wu) x` become a mask to `W` bits, which is the value the narrower
slot would hold.

## What the loop body may read

`frontLoopBodyJ` compiles a body over the context `acc :: idx :: invs`: the
accumulator array, the loop index and the invariant arrays, of which only the
accumulator crosses the back-edge. A scalar is otherwise local to one
iteration, so a body that reads a scalar it has not yet written in that
iteration — a loop-carried counter — needs that scalar to ride the
accumulator. `withCarried` puts it there: the accumulator is a state array
with one cell per carried scalar, and the body opens by loading each name from
its cell and closes by storing it back. A leaf's carried names are the scalars
its loop body reads before it writes them, and the caller seeds the state array
with the entry values the source's pre-loop initialisations assign. A body that
writes every scalar before reading it carries nothing and keeps the two-array
ABI.

## Main definitions

* `stmtToLowCT` / `stmtsToLowCT`: the statement translation.
* `jfunToLowCT`: a whole `JFun` body as one `LowCT`.
* `jfunLeaf`: a leaf's loop, its ABI names, its trip count and its carried
  scalars.
* `carryLoad` / `carryStore` / `withCarried`: a body's carried scalars read
  from and written back to the state array.
* `rbwGo` / `carriedOf`: the scalars a loop body reads before it writes them.
* `renderFor2` / `renderWhile2`: a counted loop and a countdown loop through
  the front to owned AT&T x86.
* `renderForCarried` / `renderWhileCarried`: the same two over the state-array
  ABI, for a loop with carried scalars.
* `renderJFunLeaf`: `jfunLeaf` followed by the matching renderer.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JincToLowCT

open CatCrypt.Crypto.Jasmin.JincToCom
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. The name environment -/

/-- The scalar and array names a leaf declares, with each array's cell count. -/
structure Env where
  scalars : List String
  arrays : List (String × Nat)

/-- Whether `x` is a declared scalar (a `reg` parameter, a `reg` declaration or
    an `inline int` counter). -/
def Env.isScalar (e : Env) (x : String) : Bool := e.scalars.contains x

/-- The cell count of the array named `x`. -/
def Env.arraySize (e : Env) (x : String) : Option Nat :=
  (e.arrays.find? (fun p => p.1 == x)).map Prod.snd

/-- The environment of a parsed leaf. -/
def envOfJFun (f : JFun) : Env :=
  let tys := f.params.map (fun p => (p.ty, p.name)) ++ f.decls.map (fun d => (d.1, d.2))
  { scalars := tys.filterMap (fun t => match t.1 with
                                       | .reg _ => some t.2
                                       | _ => none) ++ f.inlineInts
    arrays := tys.filterMap (fun t => match t.1 with
                                      | .arr _ n => some (t.2, n)
                                      | _ => none) }

/-- The scalar slot a literal array index is materialised into. -/
def tmpIdx : String := "__jinc_idx"

/-- The scalar slot a stored right-hand side is materialised into. -/
def tmpVal : String := "__jinc_val"

/-- The loop index slot of a loop whose source counter is not the index itself:
    a countdown loop, or a `for` whose lower bound is not zero. -/
def tripName : String := "__jinc_trip"

/-! ## 2. Expressions -/

/-- The `SExpr` of a source binary operator. `SExpr` has no bitwise-or
    constructor and `a ||| b = a + b - (a &&& b)` holds over both of its
    evaluators. -/
def opExpr : BinKind → SExpr → SExpr → SExpr
  | .add, a, b => .SAdd a b
  | .sub, a, b => .SSub a b
  | .mul, a, b => .SMul a b
  | .and, a, b => .SAnd a b
  | .xor, a, b => .SXor a b
  | .shl, a, b => .SShl a b
  | .shr, a, b => .SShr a b
  | .or, a, b => .SSub (.SAdd a b) (.SAnd a b)

/-- The `SExpr` of a binary right-hand operand. -/
def operandExpr : Operand → SExpr
  | .var s => .SVar s
  | .lit n => .SLit n

/-- `e` masked to `w` bits, the identity at `w ≥ 64`. -/
def truncate (w : Nat) (e : SExpr) : SExpr :=
  if w ≥ 64 then e else .SAnd e (.SLit (2 ^ w - 1))

/-- The `SExpr` of a right-hand side that reads no memory.

    `none` on four right-hand sides. `load` and `castLoad` become `RArrLoad` in
    `assignRhs`. `select` has no translation: `cond ? t : f` is branch-free only
    when `cond` is known to be `0` or `1`, which the untyped AST does not
    record. A `glob` naming something other than a declared scalar is a
    global-table binding (`tbl = EC_DLOG`); `LowCT` reaches a table as a loop
    invariant array parameter, not as a bound name. -/
def rhsExpr (env : Env) : Rhs → Option SExpr
  | .bin op a b => some (opExpr op (.SVar a) (operandExpr b))
  | .imm n => some (.SLit n)
  | .glob v => if env.isScalar v then some (.SVar v) else none
  | .cast w src => some (truncate w (.SVar src))
  | .load _ _ => none
  | .castLoad _ _ _ => none
  | .select _ _ _ => none

/-- The `Located` of a declared array, as 64-bit words. -/
def arrLoc (env : Env) (a : String) : Option Located :=
  (env.arraySize a).map (fun n => { locVar := a, locSrc := .TBytes (8 * n) })

/-- The `Located` of a scalar slot. -/
def u64Loc (x : String) : Located := { locVar := x, locSrc := .TU64 }

/-- The translation of `lhs = rhs`. A load becomes `RArrLoad`, a cast load a
    load followed by the mask, and every other right-hand side an
    `RScalarSetExpr`. -/
def assignRhs (env : Env) (lhs : String) : Rhs → Option LowCT
  | .load arr idx => do
      let l ← arrLoc env arr
      pure (.RArrLoad (u64Loc lhs) l idx)
  | .castLoad w arr idx => do
      let l ← arrLoc env arr
      let ld : LowCT := .RArrLoad (u64Loc lhs) l idx
      pure (if w ≥ 64 then ld
            else .RSeq ld (.RScalarSetExpr lhs (truncate w (.SVar lhs))))
  | r => (rhsExpr env r).map (fun e => LowCT.RScalarSetExpr lhs e)

/-- The scalar holding an array index, with the command that sets it. A literal
    index goes through `tmpIdx`, since `RArrLoad`/`RArrStore` read the index
    from a scalar slot. -/
def indexName (env : Env) : Operand → Option (String × LowCT)
  | .var v => if env.isScalar v then some (v, .RSkip) else none
  | .lit k => some (tmpIdx, .RScalarSetExpr tmpIdx (.SLit k))

/-- `RSeq` with `RSkip` absorbed on either side. -/
def seq2 : LowCT → LowCT → LowCT
  | .RSkip, b => b
  | a, .RSkip => a
  | a, b => .RSeq a b

/-! ## 3. Statements -/

mutual

/-- One source statement as `LowCT`.

    `return` is `RSkip`: the returned name is the accumulator the front threads
    through the loop, and carries no command of its own. A `for` with a nonzero
    lower bound runs over `tripName` and rebinds the source counter from it.

    `none` when a statement names an array that is not declared, indexes by a
    name that is not a declared scalar, or stores a `select` right-hand side
    (see `rhsExpr`). -/
def stmtToLowCT (env : Env) : Stmt → Option LowCT
  | .assign lhs rhs => assignRhs env lhs rhs
  | .compound op lhs rhs =>
      some (.RScalarSetExpr lhs (opExpr op (.SVar lhs) (operandExpr rhs)))
  | .store arr idx val => do
      let l ← arrLoc env arr
      pure (seq2 (.RScalarSetExpr tmpIdx (.SLit idx)) (.RArrStore l tmpIdx (u64Loc val)))
  | .storeAt arr idx val => do
      let l ← arrLoc env arr
      let (iname, ipre) ← indexName env idx
      match val with
      | .glob v =>
          if env.isScalar v then pure (seq2 ipre (.RArrStore l iname (u64Loc v))) else none
      | _ => do
          let vpre ← assignRhs env tmpVal val
          pure (seq2 ipre (seq2 vpre (.RArrStore l iname (u64Loc tmpVal))))
  | .ret _ => some .RSkip
  | .whileNz c body => (stmtsToLowCT env body).map (LowCT.RWhileNz c)
  | .forTo v lo hi body => do
      let b ← stmtsToLowCT env body
      if lo = 0 then pure (.RFor v hi b)
      else pure (.RFor tripName (hi - lo)
        (.RSeq (.RScalarSetExpr v (.SAdd (.SVar tripName) (.SLit lo))) b))

/-- A statement list as an `RSeq` chain, `RSkip` when empty. -/
def stmtsToLowCT (env : Env) : List Stmt → Option LowCT
  | [] => some .RSkip
  | s :: rest => do
      let a ← stmtToLowCT env s
      let b ← stmtsToLowCT env rest
      pure (seq2 a b)

end

/-- A whole leaf body as one `LowCT`. -/
def jfunToLowCT (f : JFun) : Option LowCT := stmtsToLowCT (envOfJFun f) f.body

/-- `for` at lower bound zero is `RFor` over the source counter. -/
theorem stmtToLowCT_forTo_zero (env : Env) (v : String) (hi : Nat) (body : List Stmt)
    (b : LowCT) (h : stmtsToLowCT env body = some b) :
    stmtToLowCT env (.forTo v 0 hi body) = some (.RFor v hi b) := by
  simp [stmtToLowCT, h]

/-- `while (c != 0)` is `RWhileNz` at the source guard. -/
theorem stmtToLowCT_whileNz (env : Env) (c : String) (body : List Stmt) :
    stmtToLowCT env (.whileNz c body) = (stmtsToLowCT env body).map (LowCT.RWhileNz c) := by
  simp [stmtToLowCT]

/-! ## 4. The leaf shape -/

/-- Whether a statement is a scalar initialisation, the only prologue
    `jfunLeaf` accepts. -/
def isScalarInit (env : Env) : Stmt → Bool
  | .assign x (.imm _) => env.isScalar x
  | .assign x (.glob _) => env.isScalar x
  | .compound _ x _ => env.isScalar x
  | _ => false

/-- `r` extended with those of `vs` that are neither already written nor
    already recorded as read. -/
def addReads (w r : List String) (vs : List String) : List String :=
  vs.foldl (fun r v => if w.contains v || r.contains v then r else r ++ [v]) r

/-- One step of the read-before-write walk: the written names and the
    read-before-written names after running `c` from the given pair.

    Reads are the index and value slots of an array access, the free variables
    of a scalar expression, and a guard or bound. Writes are the targets of a
    scalar set and of an array load, plus a loop binder inside its own body. A
    body that may not run — a loop body, an `RIfNz` branch — contributes its
    reads and none of its writes, so a name it writes still counts as carried.

    The arms are those `stmtsToLowCT` produces; any other constructor
    contributes nothing. -/
def rbwGo : LowCT → List String × List String → List String × List String
  | .RSkip, st => st
  | .RSeq a b, st => rbwGo b (rbwGo a st)
  | .RScalarSet x _, (w, r) => (x :: w, r)
  | .RScalarSetExpr x e, (w, r) => (x :: w, addReads w r e.freeVars)
  | .RArrLoad dst _ idx, (w, r) => (dst.locVar :: w, addReads w r [idx])
  | .RArrStore _ idx src, (w, r) => (w, addReads w r [idx, src.locVar])
  | .RWhileNz g b, (w, r) => (w, (rbwGo b (w, addReads w r [g])).2)
  | .RFor x _ b, (w, r) => (w, (rbwGo b (x :: w, r)).2)
  | .RForRuntime x bd b, (w, r) =>
      (w, (rbwGo b (x :: w, addReads w r bd.freeVars)).2)
  | .RIfNz g t e, (w, r) =>
      let r₁ := (rbwGo t (w, addReads w r [g])).2
      (w, (rbwGo e (w, r₁)).2)
  | _, st => st

/-- The scalars `body` reads before it writes them, in first-read order, less
    the loop binder `idxName`, which the loop supplies. These are the names
    whose value has to reach the next iteration, so they are the ones the loop
    carries. A scalar the body writes before reading is local to an iteration
    and is not carried, whatever the source assigns it before the loop. -/
def carriedOf (idxName : String) (body : LowCT) : List String :=
  ((rbwGo body ([], [])).2).filter (fun x => x ≠ idxName)

/-- Whether a statement is a loop. -/
def isLoopStmt : Stmt → Bool
  | .whileNz _ _ => true
  | .forTo _ _ _ _ => true
  | _ => false

/-- A leaf's loop as the rolled route takes it: the in-place accumulator array,
    the loop-invariant input array, the index slot, the body and the trip form
    (`some n` for a counted loop, `none` for a countdown loop). -/
structure JLeaf where
  accName : String
  accWords : Nat
  invName : String
  invWords : Nat
  idxName : String
  body : LowCT
  trips : Option Nat
  /-- The scalars the prologue initialises, which the loop carries across
      iterations through the state array. -/
  carried : List String

/-- The loop of a leaf with two array parameters, the first rewritten in place
    and the second read.

    `none` unless the body is a prologue of scalar initialisations, then one
    loop, then `return`s. The leaf's `carried` names are the scalars the loop
    body reads before it writes them; the prologue supplies their entry values.
    A prologue that only zeroes slots the body overwrites leaves `carried`
    empty, so such a leaf keeps the two-array ABI. -/
def jfunLeaf (f : JFun) : Option JLeaf := do
  let env := envOfJFun f
  match f.params with
  | [⟨.arr _ nAcc, acc⟩, ⟨.arr _ nInv, inv⟩] =>
      let (pre, rest) := f.body.span (fun s => !isLoopStmt s)
      if !pre.all (isScalarInit env) then none else
      match rest with
      | loop :: post =>
          if !post.all (fun s => match s with | .ret _ => true | _ => false) then none else
          match loop with
          | .forTo v lo hi b => do
              let c ← stmtsToLowCT env b
              if lo = 0 then
                pure { accName := acc, accWords := nAcc, invName := inv, invWords := nInv,
                       idxName := v, body := c, trips := some hi,
                       carried := carriedOf v c }
              else
                let c' : LowCT :=
                  .RSeq (.RScalarSetExpr v (.SAdd (.SVar tripName) (.SLit lo))) c
                pure { accName := acc, accWords := nAcc, invName := inv, invWords := nInv,
                       idxName := tripName, body := c', trips := some (hi - lo),
                       carried := carriedOf tripName c' }
          | .whileNz _ b => do
              let c ← stmtsToLowCT env b
              pure { accName := acc, accWords := nAcc, invName := inv, invWords := nInv,
                     idxName := tripName, body := c, trips := none,
                     carried := carriedOf tripName c }
          | _ => none
      | [] => none
  | _ => none

/-! ## 5. Loop-carried scalars

`frontLoopBodyJ` threads exactly one value across the back-edge: the
accumulator slot of `Γbody = acc :: idx :: invs`. A scalar the body reads
before it writes therefore has no image, which is what declines a rejection
loop whose counters advance across iterations.

A carried scalar reaches the next iteration by riding a cell of the
accumulator. The accumulator is a dedicated state array with one cell per
carried scalar; the body opens by loading each name from its cell and closes
by storing it back, and the arrays the loop reads and writes are loop
invariants, written through `RArrStore`. `MpnLoopFrontEmit`'s carry family is
the one-scalar case of the same shape, with the output array as a loop
invariant and the carried value as the accumulator.

The state array holds each carried scalar's entry value on entry and its exit
value on return, so the caller seeds it with the values the source's pre-loop
initialisations assign. -/

/-- The name of the loop-state array that holds the carried scalars. -/
def stateName : String := "__jinc_st"

/-- The scalar slot a state-array cell index is materialised into. -/
def stateIdx : String := "__jinc_st_i"

/-- The `Located` of the `k`-cell loop-state array. -/
def stateLoc (k : Nat) : Located := { locVar := stateName, locSrc := .TBytes (8 * k) }

/-- Reads of the carried scalars from their state cells, cell `j` holding
    `names[j]`. -/
def carryLoad (names : List String) : LowCT :=
  names.zipIdx.foldr (fun p rest =>
    seq2 (.RScalarSetExpr stateIdx (.SLit p.2))
      (seq2 (.RArrLoad (u64Loc p.1) (stateLoc names.length) stateIdx) rest)) .RSkip

/-- Writes of the carried scalars back to their state cells, cell `j` holding
    `names[j]`. -/
def carryStore (names : List String) : LowCT :=
  names.zipIdx.foldr (fun p rest =>
    seq2 (.RScalarSetExpr stateIdx (.SLit p.2))
      (seq2 (.RArrStore (stateLoc names.length) stateIdx (u64Loc p.1)) rest)) .RSkip

/-- `body` with the carried scalars read from the state array on entry and
    written back on exit, so each iteration sees the previous iteration's
    values. -/
def withCarried (names : List String) (body : LowCT) : LowCT :=
  seq2 (carryLoad names) (seq2 body (carryStore names))

/-! ## 6. Owned x86 renders -/

/-- The owned render of a leaf: the basic-block pipeline, then two rounds of
    register-copy coalescing (`LprogCopyCoalesce.coalesceRounds`, which preserves
    the stored state by `coalesceBody_stateStore`), then the printer. The front
    binds every source statement to a fresh name, so a rolled loop body carries a
    copy per binding that the basic-block pipeline alone leaves in place. -/
def renderLeaf (p : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog) : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt
    (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce.coalesceRounds 2
      (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.optimizeLprogBasicBlocks p))

/-- A counted loop rendered to owned AT&T x86.

    The accumulator is `%rdi` and the invariant input `%rsi`, matching
    `T *sym(uint64_t *acc, const uint64_t *inv)`. -/
def renderFor2 (sym : String) (wAcc wInv : Nat) (accName idxName invName : String)
    (trips : Nat) (body : LowCT) : Option String :=
  (compileLoop (Γouter := [.stackArr 64 wAcc, .stackArr 64 wInv])
      (accCTy := .memref wAcc) (invCTys := [.memref wInv]) .plain (.static trips)
      (((VarMap.empty.bind (t := .memref wInv) invName).bind
          (t := .sword 64) idxName).bind (t := .memref wAcc) accName)
      accName body (init := .here) (invs := .cons (.there .here) .nil)).map
    (fun c =>
      renderLeaf
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1]
          (fun _ => none) (fun _ => none) ["RDI", "RSI"] [64, 64]))

/-- A countdown loop rendered to owned AT&T x86.

    `ComL.whileNz` reads its trip from an in-scope 64-bit seed register, so the
    rendered leaf takes it as a third argument: `%rdi` the accumulator, `%rsi`
    the invariant input, `%rdx` the countdown seed. The source guard variable is
    not the seed — it is a body scalar, and the loop the render performs is the
    seed's countdown. -/
def renderWhile2 (sym : String) (wAcc wInv : Nat) (accName idxName invName : String)
    (body : LowCT) : Option String :=
  (compileLoop (Γouter := [.stackArr 64 wAcc, .stackArr 64 wInv, .reg 64])
      (accCTy := .memref wAcc) (invCTys := [.memref wInv]) .plain
      (.countdown (.there (.there .here)))
      (((VarMap.empty.bind (t := .memref wInv) invName).bind
          (t := .sword 64) idxName).bind (t := .memref wAcc) accName)
      accName body (init := .here) (invs := .cons (.there .here) .nil)).map
    (fun c =>
      renderLeaf
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1, argName 2]
          (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]))

/-- A counted loop with loop-carried scalars rendered to owned AT&T x86.

    The accumulator is the state array in `%rdi`, and the two source arrays are
    loop invariants in `%rsi` and `%rdx`, matching
    `T *sym(uint64_t *state, uint64_t *acc, const uint64_t *inv)`. The caller
    seeds `state` with the carried scalars' entry values and reads their exit
    values from it. -/
def renderForCarried (sym : String) (carried : List String) (wAcc wInv : Nat)
    (accName idxName invName : String) (trips : Nat) (body : LowCT) : Option String :=
  (compileLoop
      (Γouter := [.stackArr 64 carried.length, .stackArr 64 wAcc, .stackArr 64 wInv])
      (accCTy := .memref carried.length) (invCTys := [.memref wAcc, .memref wInv])
      .plain (.static trips)
      ((((VarMap.empty.bind (t := .memref wInv) invName).bind
          (t := .memref wAcc) accName).bind
          (t := .sword 64) idxName).bind (t := .memref carried.length) stateName)
      stateName (withCarried carried body) (init := .here)
      (invs := .cons (.there .here) (.cons (.there (.there .here)) .nil))).map
    (fun c =>
      renderLeaf
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1, argName 2]
          (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]))

/-- A countdown loop with loop-carried scalars rendered to owned AT&T x86.

    `ComL.whileNz` reads its trip from an in-scope 64-bit seed register, so the
    rendered leaf takes it as a fourth argument: `%rdi` the state array, `%rsi`
    and `%rdx` the two source arrays, `%rcx` the countdown seed. The source
    guard variable is a body scalar; the loop the render performs is the seed's
    countdown, so the seed is an iteration bound and the body's own guard is
    what stops the carried counters advancing past their target. -/
def renderWhileCarried (sym : String) (carried : List String) (wAcc wInv : Nat)
    (accName idxName invName : String) (body : LowCT) : Option String :=
  (compileLoop
      (Γouter := [.stackArr 64 carried.length, .stackArr 64 wAcc, .stackArr 64 wInv,
                  .reg 64])
      (accCTy := .memref carried.length) (invCTys := [.memref wAcc, .memref wInv])
      .plain (.countdown (.there (.there (.there .here))))
      ((((VarMap.empty.bind (t := .memref wInv) invName).bind
          (t := .memref wAcc) accName).bind
          (t := .sword 64) idxName).bind (t := .memref carried.length) stateName)
      stateName (withCarried carried body) (init := .here)
      (invs := .cons (.there .here) (.cons (.there (.there .here)) .nil))).map
    (fun c =>
      renderLeaf
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1, argName 2, argName 3]
          (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]))

/-- A parsed leaf rendered to owned AT&T x86 under the symbol `sym`, `none` when
    `jfunLeaf` rejects the shape or the body front declines the body.

    A leaf whose prologue initialises no scalar has no carried value and renders
    over the two-array ABI; one that does renders over the state-array ABI of
    `renderForCarried` / `renderWhileCarried`. -/
def renderJFunLeaf (sym : String) (f : JFun) : Option String := do
  let l ← jfunLeaf f
  match l.carried, l.trips with
  | [], some n => renderFor2 sym l.accWords l.invWords l.accName l.idxName l.invName n l.body
  | [], none => renderWhile2 sym l.accWords l.invWords l.accName l.idxName l.invName l.body
  | c, some n =>
      renderForCarried sym c l.accWords l.invWords l.accName l.idxName l.invName n l.body
  | c, none =>
      renderWhileCarried sym c l.accWords l.invWords l.accName l.idxName l.invName l.body

end CatCrypt.Crypto.Jasmin.JincToLowCT
