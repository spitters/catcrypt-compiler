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
`ComL.toLprogPhysAbi` → `renderLeafLprog` → `LprogAsmPrinter.renderLprogAtt`.

## Constant time of the rendered program

§7 states constant time for the `Lprog` the printer receives, after the
basic-block pipeline and copy coalescing. The observation model is
`rolledLeak`: each instruction executed, the effective address
`(base register value, scale · index register value)` of every register-indexed
operand, and the direction of the counted loop's back-edge. `rolledLprogCheck`
is a flow-sensitive public-register analysis of the program; when it accepts,
`rolledLprog_pub_determined` states that the trace is the same from any two
states that agree on the entry registers it was given, for any memory contents
and any values in the other registers. Registers and memory evolve by
`JasminLsem.lsemStep`. That model has no flags, so the back-edge's
`CMP ctr, 0; jnz` is given its x86 meaning directly (branch while the counter is
non-zero), and the model's memory is keyed by base register name, which the
analysis never trusts: every loaded value is secret. The printer's rendering of
the `qsave.*` spill registers as fixed stack slots, and the printer itself, are
outside the statement.

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
* `for2Lprog` / `while2Lprog`: a counted loop and a countdown loop through
  the front to the program the owned printer receives.
* `forCarriedLprog` / `whileCarriedLprog`: the same two over the state-array
  ABI, for a loop with carried scalars.
* `jfunLeafLprog` / `renderJFunLeaf`: `jfunLeaf` followed by the matching
  compiler, and that program printed as AT&T x86.
* `rolledLprogCheck` / `rolledLprog_pub_determined`: a public-register check of
  a compiled rolled leaf, and the constant-time theorem it implies over the
  address-leak trace of the program the printer receives.
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

/-- The program the printer receives for a leaf: the basic-block pipeline, then
    two rounds of register-copy coalescing (`LprogCopyCoalesce.coalesceRounds`,
    which preserves the stored state by `coalesceBody_stateStore`). The front
    binds every source statement to a fresh name, so a rolled loop body carries a
    copy per binding that the basic-block pipeline alone leaves in place. -/
def renderLeafLprog (p : Lprog) : Lprog :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce.coalesceRounds 2
    (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.optimizeLprogBasicBlocks p)

/-- The owned render of a leaf: `renderLeafLprog`, then the printer. -/
def renderLeaf (p : Lprog) : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt
    (renderLeafLprog p)

/-- A counted loop compiled to the program the owned printer receives.

    The accumulator is `%rdi` and the invariant input `%rsi`, matching
    `T *sym(uint64_t *acc, const uint64_t *inv)`. -/
def for2Lprog (sym : String) (wAcc wInv : Nat) (accName idxName invName : String)
    (trips : Nat) (body : LowCT) : Option Lprog :=
  (compileLoop (Γouter := [.stackArr 64 wAcc, .stackArr 64 wInv])
      (accCTy := .memref wAcc) (invCTys := [.memref wInv]) .plain (.static trips)
      (((VarMap.empty.bind (t := .memref wInv) invName).bind
          (t := .sword 64) idxName).bind (t := .memref wAcc) accName)
      accName body (init := .here) (invs := .cons (.there .here) .nil)).map
    (fun c =>
      renderLeafLprog
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1]
          (fun _ => none) (fun _ => none) ["RDI", "RSI"] [64, 64]))

/-- A countdown loop compiled to the program the owned printer receives.

    `ComL.whileNz` reads its trip from an in-scope 64-bit seed register, so the
    rendered leaf takes it as a third argument: `%rdi` the accumulator, `%rsi`
    the invariant input, `%rdx` the countdown seed. The source guard variable is
    not the seed — it is a body scalar, and the loop the render performs is the
    seed's countdown. -/
def while2Lprog (sym : String) (wAcc wInv : Nat) (accName idxName invName : String)
    (body : LowCT) : Option Lprog :=
  (compileLoop (Γouter := [.stackArr 64 wAcc, .stackArr 64 wInv, .reg 64])
      (accCTy := .memref wAcc) (invCTys := [.memref wInv]) .plain
      (.countdown (.there (.there .here)))
      (((VarMap.empty.bind (t := .memref wInv) invName).bind
          (t := .sword 64) idxName).bind (t := .memref wAcc) accName)
      accName body (init := .here) (invs := .cons (.there .here) .nil)).map
    (fun c =>
      renderLeafLprog
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1, argName 2]
          (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]))

/-- A counted loop with loop-carried scalars compiled to the program the owned
    printer receives.

    The accumulator is the state array in `%rdi`, and the two source arrays are
    loop invariants in `%rsi` and `%rdx`, matching
    `T *sym(uint64_t *state, uint64_t *acc, const uint64_t *inv)`. The caller
    seeds `state` with the carried scalars' entry values and reads their exit
    values from it. -/
def forCarriedLprog (sym : String) (carried : List String) (wAcc wInv : Nat)
    (accName idxName invName : String) (trips : Nat) (body : LowCT) : Option Lprog :=
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
      renderLeafLprog
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1, argName 2]
          (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]))

/-- A countdown loop with loop-carried scalars compiled to the program the owned
    printer receives.

    `ComL.whileNz` reads its trip from an in-scope 64-bit seed register, so the
    rendered leaf takes it as a fourth argument: `%rdi` the state array, `%rsi`
    and `%rdx` the two source arrays, `%rcx` the countdown seed. The source
    guard variable is a body scalar; the loop the render performs is the seed's
    countdown, so the seed is an iteration bound and the body's own guard is
    what stops the carried counters advancing past their target. -/
def whileCarriedLprog (sym : String) (carried : List String) (wAcc wInv : Nat)
    (accName idxName invName : String) (body : LowCT) : Option Lprog :=
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
      renderLeafLprog
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1, argName 2, argName 3]
          (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]))

/-- The program the owned printer receives for a parsed leaf under the symbol
    `sym`, `none` when `jfunLeaf` rejects the shape or the body front declines
    the body.

    A leaf whose prologue initialises no scalar has no carried value and compiles
    over the two-array ABI; one that does compiles over the state-array ABI of
    `forCarriedLprog` / `whileCarriedLprog`. -/
def jfunLeafLprog (sym : String) (f : JFun) : Option Lprog := do
  let l ← jfunLeaf f
  match l.carried, l.trips with
  | [], some n => for2Lprog sym l.accWords l.invWords l.accName l.idxName l.invName n l.body
  | [], none => while2Lprog sym l.accWords l.invWords l.accName l.idxName l.invName l.body
  | c, some n =>
      forCarriedLprog sym c l.accWords l.invWords l.accName l.idxName l.invName n l.body
  | c, none =>
      whileCarriedLprog sym c l.accWords l.invWords l.accName l.idxName l.invName l.body

/-- A parsed leaf rendered to owned AT&T x86 under the symbol `sym`: the printer
    applied to `jfunLeafLprog`. -/
def renderJFunLeaf (sym : String) (f : JFun) : Option String :=
  (jfunLeafLprog sym f).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt

/-! ## 7. Constant time of a rolled render -/

namespace RolledCT

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-! ### Operations `applyOpn` defines at every argument -/

/-- The single-source mnemonics `applyOpn` matches by name before its
    count-tagged shift arm. -/
def unaryNamed : List String := ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX"]

/-- The two-source word operations of `applyOpn`. -/
def binaryOps : List String := ["ADD", "SUB", "MUL", "AND", "OR", "XOR"]

/-- The stripped mnemonics whose `applyOpn` arm is defined at every source list
    of the given length. -/
def totalOp (op : String) : Nat → Bool
  | 1 => (op == "MOV" || op == "MOVQ")
      || (!decide (op ∈ unaryNamed) && (parseImmShiftMnem op).isSome)
  | 2 => decide (op ∈ binaryOps)
  | _ => false

theorem shift_isSome {w : Nat} (op : String) (a : BitVec w)
    (hn : op ∉ unaryNamed) (h : (parseImmShiftMnem op).isSome = true) :
    (applyOpn op [a]).isSome := by
  simp only [unaryNamed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hn
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  unfold applyOpn
  split <;> simp_all

theorem totalOp_isSome {w : Nat} (op : String) (xs : List (BitVec w))
    (h : totalOp op xs.length = true) : (applyOpn op xs).isSome := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [totalOp] at h
  · simp only [totalOp, List.length, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      Bool.not_eq_true', decide_eq_false_iff_not] at h
    rcases h with (h | h) | ⟨hn, h⟩
    · subst h; rfl
    · subst h; rfl
    · exact shift_isSome op a hn h
  · simp only [totalOp, List.length, decide_eq_true_eq] at h
    simp only [binaryOps, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> subst h <;> rfl
  · simp [totalOp] at h

/-! ### The address-leak trace of a straight-line list -/

/-- An observation of the address-leak model: the instruction executed, the
    effective address `(base value, byte offset)` of a register-indexed memory
    operand, or the direction of a conditional branch. -/
inductive AddrEvent (w : Nat) where
  | instr (i : LinstrR)
  | mem (base : BitVec w) (off : Nat)
  | branch (taken : Bool)

/-- The effective address a register-indexed operand touches in state `s`. -/
def operandAddr {w : Nat} (s : Lstate w) : LOperand → List (AddrEvent w)
  | .arrIdx base idx scale => [.mem (s.lvm base) (scale * (s.lvm idx).toNat)]
  | _ => []

/-- The observations of executing `i` in state `s`: the instruction, then the
    effective address of each register-indexed operand. -/
def instrAddrLeak {w : Nat} (s : Lstate w) (i : LinstrR) : List (AddrEvent w) :=
  .instr i :: (match i with
    | .Lopn ds _ ss => (ds ++ ss).flatMap (operandAddr s)
    | _ => [])

/-- One straight-line step: `lsemStep`, with an instruction `lsemStep` does not
    model (a flag-only compare) leaving registers and memory unchanged. -/
def stepT {w : Nat} (i : LinstrR) (s : Lstate w) : Lstate w :=
  (lsemStep i s).getD s.nextPc

/-- The address-leak trace and final state of a straight-line instruction list. -/
def runLeak {w : Nat} : List LinstrR → Lstate w → List (AddrEvent w) × Lstate w
  | [], s => ([], s)
  | i :: is, s =>
      let r := runLeak is (stepT i s)
      (instrAddrLeak s i ++ r.1, r.2)

/-! ### The public-register analysis -/

/-- Two states agree on the registers of `P`. -/
def Agree {w : Nat} (P : List String) (s₁ s₂ : Lstate w) : Prop :=
  ∀ r ∈ P, s₁.lvm r = s₂.lvm r

/-- A source operand whose value is a function of the registers in `P`. -/
def pubOperand (P : List String) : LOperand → Bool
  | .reg r => decide (r ∈ P)
  | .imm _ => true
  | _ => false

/-- A register-indexed operand whose base and index registers are in `P`. -/
def addrOK (P : List String) : LOperand → Bool
  | .arrIdx base idx _ => decide (base ∈ P) && decide (idx ∈ P)
  | _ => true

/-- `P` without the register `d`. -/
def kill (P : List String) (d : String) : List String := P.filter (· != d)

/-- The public-register transfer of one straight-line instruction: `none` when
    it addresses memory through a register outside `P` or is a control-flow
    instruction, otherwise the registers public after it. A destination becomes
    public when every source is public and the operation writes it (or it was
    public already); a loaded value is never public. -/
def pubInstr (P : List String) : LinstrR → Option (List String)
  | .Lopn ds op ss =>
      if (ds ++ ss).all (addrOK P) then
        match ds, ss with
        | [.reg d], .arrIdx _ _ _ :: _ => if op = "STOREIDX" then some P else some (kill P d)
        | [.reg d], ss =>
            if ss.all (pubOperand P) && (decide (d ∈ P) || totalOp (stripWidthTag op) ss.length)
            then some (d :: P) else some (kill P d)
        | _, _ => some P
      else none
  | .Lalign => some P
  | .Lret => some P
  | _ => none

/-- The public-register transfer of a straight-line list. -/
def pubRun (P : List String) : List LinstrR → Option (List String)
  | [] => some P
  | i :: is => (pubInstr P i).bind (fun P' => pubRun P' is)

theorem agree_of_lvm {w : Nat} {P : List String} {s₁ s₂ t₁ t₂ : Lstate w}
    (h : Agree P s₁ s₂) (h₁ : t₁.lvm = s₁.lvm) (h₂ : t₂.lvm = s₂.lvm) : Agree P t₁ t₂ := by
  intro r hr; rw [h₁, h₂]; exact h r hr

theorem agree_mono {w : Nat} {P Q : List String} {s₁ s₂ : Lstate w}
    (hPQ : ∀ r ∈ P, r ∈ Q) (h : Agree Q s₁ s₂) : Agree P s₁ s₂ :=
  fun r hr => h r (hPQ r hr)

theorem agree_kill {w : Nat} {P : List String} {s₁ s₂ t₁ t₂ : Lstate w} (d : String)
    (h : Agree P s₁ s₂)
    (h₁ : ∀ r, r ≠ d → t₁.lvm r = s₁.lvm r) (h₂ : ∀ r, r ≠ d → t₂.lvm r = s₂.lvm r) :
    Agree (kill P d) t₁ t₂ := by
  intro r hr
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hr
  rw [h₁ r hr.2, h₂ r hr.2]; exact h r hr.1

theorem agree_setReg {w : Nat} {P : List String} {s₁ s₂ : Lstate w} (d : String)
    (v : BitVec w) (h : Agree P s₁ s₂) :
    Agree (d :: P) (s₁.setReg d v).nextPc (s₂.setReg d v).nextPc := by
  intro r hr
  simp only [Lstate.nextPc, Lstate.lvm_setReg]
  by_cases hrd : r = d
  · simp [hrd]
  · simp only [hrd, if_false]
    exact h r (by simpa [hrd] using hr)

theorem evalOperand_agree {w : Nat} {P : List String} {s₁ s₂ : Lstate w}
    (h : Agree P s₁ s₂) (o : LOperand) (ho : pubOperand P o = true) :
    evalOperand s₁ o = evalOperand s₂ o := by
  cases o with
  | reg r => simp only [pubOperand, decide_eq_true_eq] at ho; simp [evalOperand, h r ho]
  | imm v => rfl
  | arr _ _ => simp [pubOperand] at ho
  | arrIdx _ _ _ => simp [pubOperand] at ho

theorem operandAddr_agree {w : Nat} {P : List String} {s₁ s₂ : Lstate w}
    (h : Agree P s₁ s₂) (o : LOperand) (ho : addrOK P o = true) :
    operandAddr s₁ o = operandAddr s₂ o := by
  cases o with
  | arrIdx b ix sc =>
      simp only [addrOK, Bool.and_eq_true, decide_eq_true_eq] at ho
      simp [operandAddr, h b ho.1, h ix ho.2]
  | _ => rfl

theorem instrAddrLeak_agree {w : Nat} {P : List String} {s₁ s₂ : Lstate w}
    (h : Agree P s₁ s₂) (ds : List LOperand) (op : String) (ss : List LOperand)
    (hok : (ds ++ ss).all (addrOK P) = true) :
    instrAddrLeak s₁ (.Lopn ds op ss) = instrAddrLeak s₂ (.Lopn ds op ss) := by
  simp only [instrAddrLeak, List.cons.injEq, true_and]
  apply List.flatMap_congr
  intro o ho
  exact operandAddr_agree h o (List.all_eq_true.mp hok o ho)

/-- Over a source list not headed by a register-indexed operand, a
    single-register-destination step writes `applyOpn`'s result, or nothing. -/
theorem stepT_reg {w : Nat} (s : Lstate w) (d op : String) (ss : List LOperand)
    (hss : ∀ b ix sc rest, ss ≠ .arrIdx b ix sc :: rest) :
    stepT (.Lopn [.reg d] op ss) s
      = match applyOpn (stripWidthTag op) (ss.map (evalOperand s)) with
        | some v => (s.setReg d v).nextPc
        | none => s.nextPc := by
  rcases ss with _ | ⟨o, rest⟩
  · simp only [stepT, lsemStep]
    split <;> (rename_i h; simp only [h, Option.getD_some, Option.getD_none])
  · cases o with
    | arrIdx b ix sc => exact absurd rfl (hss b ix sc rest)
    | _ =>
        simp only [stepT, lsemStep]
        split <;> (rename_i h; simp only [h, Option.getD_some, Option.getD_none])

/-- A step headed by a register-indexed operand changes no register but `d`,
    and changes none when the opcode is `STOREIDX`. -/
theorem stepT_arrIdx_lvm {w : Nat} (s : Lstate w) (d op b ix : String) (sc : Nat)
    (rest : List LOperand) :
    (∀ r, r ≠ d → (stepT (.Lopn [.reg d] op (.arrIdx b ix sc :: rest)) s).lvm r = s.lvm r)
      ∧ (op = "STOREIDX" →
          (stepT (.Lopn [.reg d] op (.arrIdx b ix sc :: rest)) s).lvm = s.lvm) := by
  refine ⟨fun r hr => ?_, fun hop => ?_⟩
  · simp only [stepT, lsemStep]
    split_ifs
    · simp [Lstate.nextPc, hr]
    · split <;> rfl
    · split <;> simp [Lstate.nextPc, hr]
  · subst hop
    simp only [stepT, lsemStep, if_neg (by decide : ("STOREIDX" : String) ≠ "LOADIDX"), if_true]
    split <;> rfl

/-- One accepted instruction leaks the same observations from two states that
    agree on `P`, and leaves them agreeing on the transferred set. -/
theorem pubInstr_sound {w : Nat} {P P' : List String} {s₁ s₂ : Lstate w} (i : LinstrR)
    (hi : pubInstr P i = some P') (h : Agree P s₁ s₂) :
    instrAddrLeak s₁ i = instrAddrLeak s₂ i ∧ Agree P' (stepT i s₁) (stepT i s₂) := by
  cases i with
  | Lopn ds op ss =>
      simp only [pubInstr] at hi
      by_cases hok : (ds ++ ss).all (addrOK P) = true
      · rw [if_pos hok] at hi
        refine ⟨instrAddrLeak_agree h ds op ss hok, ?_⟩
        by_cases hd : ∃ d, ds = [.reg d]
        · obtain ⟨d, rfl⟩ := hd
          by_cases hss : ∃ b ix sc rest, ss = .arrIdx b ix sc :: rest
          · obtain ⟨b, ix, sc, rest, rfl⟩ := hss
            obtain ⟨h₁a, h₁b⟩ := stepT_arrIdx_lvm s₁ d op b ix sc rest
            obtain ⟨h₂a, h₂b⟩ := stepT_arrIdx_lvm s₂ d op b ix sc rest
            by_cases hop : op = "STOREIDX"
            · simp only [hop, if_true, Option.some.injEq] at hi; subst hi
              exact agree_of_lvm h (h₁b hop) (h₂b hop)
            · simp only [hop, if_false, Option.some.injEq] at hi; subst hi
              exact agree_kill d h h₁a h₂a
          · push Not at hss
            have hi' : (if (ss.all (pubOperand P) &&
                (decide (d ∈ P) || totalOp (stripWidthTag op) ss.length)) = true
                then some (d :: P) else some (kill P d)) = some P' := by
              rcases ss with _ | ⟨o, rest⟩
              · exact hi
              · cases o with
                | arrIdx b ix sc => exact absurd rfl (hss b ix sc rest)
                | _ => exact hi
            rw [stepT_reg s₁ d op ss hss, stepT_reg s₂ d op ss hss]
            by_cases hpub : (ss.all (pubOperand P) &&
                (decide (d ∈ P) || totalOp (stripWidthTag op) ss.length)) = true
            · rw [if_pos hpub, Option.some.injEq] at hi'; subst hi'
              simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hpub
              have hv : ss.map (evalOperand s₁) = ss.map (evalOperand s₂) :=
                List.map_congr_left (fun o ho =>
                  evalOperand_agree h o (List.all_eq_true.mp hpub.1 o ho))
              rw [hv]
              cases hR : applyOpn (stripWidthTag op) (ss.map (evalOperand s₂)) with
              | some v => exact agree_setReg d v h
              | none =>
                  have hdP : d ∈ P := by
                    rcases hpub.2 with hdP | htot
                    · exact hdP
                    · have := totalOp_isSome (stripWidthTag op) (ss.map (evalOperand s₂))
                        (by rw [List.length_map]; exact htot)
                      rw [hR] at this; exact absurd this (by simp)
                  intro r hr
                  rcases List.mem_cons.mp hr with rfl | hr
                  · exact h r hdP
                  · exact h r hr
            · rw [if_neg hpub, Option.some.injEq] at hi'; subst hi'
              refine agree_kill d h (fun r hr => ?_) (fun r hr => ?_) <;>
                (split <;> simp [Lstate.nextPc, hr])
        · push Not at hd
          have hst : ∀ s : Lstate w, stepT (.Lopn ds op ss) s = s.nextPc := by
            intro s
            rcases ds with _ | ⟨o, _ | ⟨o2, rest⟩⟩
            · rfl
            · cases o with
              | reg d => exact absurd rfl (hd d)
              | _ => rfl
            · cases o <;> rfl
          have hP : P' = P := by
            rcases ds with _ | ⟨o, _ | ⟨o2, rest⟩⟩
            · simpa using hi.symm
            · cases o with
              | reg d => exact absurd rfl (hd d)
              | _ => simpa using hi.symm
            · simpa using hi.symm
          rw [hst, hst, hP]
          exact agree_of_lvm h rfl rfl
      · rw [if_neg hok] at hi; exact absurd hi (by simp)
  | Lalign =>
      simp only [pubInstr, Option.some.injEq] at hi; subst hi
      exact ⟨rfl, agree_of_lvm h rfl rfl⟩
  | Lret =>
      simp only [pubInstr, Option.some.injEq] at hi; subst hi
      exact ⟨rfl, agree_of_lvm h rfl rfl⟩
  | _ => simp [pubInstr] at hi

/-- An accepted straight-line list leaks the same observations from two states
    that agree on `P`, and leaves them agreeing on the transferred set. -/
theorem pubRun_sound {w : Nat} :
    ∀ (is : List LinstrR) {P P' : List String} {s₁ s₂ : Lstate w},
      pubRun P is = some P' → Agree P s₁ s₂ →
      (runLeak is s₁).1 = (runLeak is s₂).1 ∧ Agree P' (runLeak is s₁).2 (runLeak is s₂).2
  | [], P, P', s₁, s₂, hr, h => by
      simp only [pubRun, Option.some.injEq] at hr; subst hr; exact ⟨rfl, h⟩
  | i :: is, P, P', s₁, s₂, hr, h => by
      simp only [pubRun, Option.bind_eq_some_iff] at hr
      obtain ⟨Q, hQ, hr⟩ := hr
      obtain ⟨hl, hs⟩ := pubInstr_sound i hQ h
      obtain ⟨hl', hs'⟩ := pubRun_sound is hr hs
      simp only [runLeak]
      exact ⟨by rw [hl, hl'], hs'⟩

/-! ### The rolled counted loop -/

/-- A function body split as a counted loop: a prologue, the loop label, the
    loop body, the back-edge `CMP ctr, 0; jnz top`, and an epilogue. -/
structure RolledShape where
  pre : List LinstrR
  top : LLabel
  body : List LinstrR
  ctr : String
  post : List LinstrR

/-- The back-edge compare of the counter against zero. -/
def cmpZero (ctr : String) : LinstrR := .Lopn [.reg ctr] "CMP:64" [.reg ctr, .imm 0]

/-- The back-edge branch. -/
def backEdge (top : LLabel) : LinstrR := .Lcond (.reg "NZ") top

/-- The instruction list a `RolledShape` denotes. -/
def RolledShape.toBody (r : RolledShape) : List LinstrR :=
  r.pre ++ .Llabel .internal r.top :: (r.body ++ cmpZero r.ctr :: backEdge r.top :: r.post)

/-- The loop's address-leak trace with at most `fuel` iterations: each
    iteration runs the body and the compare, then branches back exactly when
    the counter register is non-zero (`CMP ctr, 0` sets the zero flag, `jnz`
    reads it). -/
def loopLeak {w : Nat} (r : RolledShape) : Nat → Lstate w → List (AddrEvent w) × Lstate w
  | 0, s => ([], s)
  | fuel + 1, s =>
      let b := runLeak (r.body ++ [cmpZero r.ctr]) s
      if b.2.lvm r.ctr ≠ 0 then
        let q := loopLeak r fuel b.2
        (b.1 ++ .instr (backEdge r.top) :: .branch true :: q.1, q.2)
      else (b.1 ++ [.instr (backEdge r.top), .branch false], b.2)

/-- The address-leak trace of the whole rolled function with at most `fuel`
    loop iterations. -/
def rolledLeak {w : Nat} (r : RolledShape) (fuel : Nat) (s : Lstate w) :
    List (AddrEvent w) :=
  let a := runLeak r.pre s
  let b := loopLeak r fuel a.2
  a.1 ++ b.1 ++ (runLeak r.post b.2).1

/-- A candidate set of registers public at the loop head: `P0` intersected `k`
    times with the set public after one iteration. -/
def headSet (P0 : List String) (blk : List LinstrR) : Nat → List String
  | 0 => P0
  | k + 1 =>
      let P := headSet P0 blk k
      match pubRun P blk with
      | some P1 => P.filter (fun x => decide (x ∈ P1))
      | none => P

/-- The public-register check of a rolled function from the entry set `Pin`:
    the prologue is accepted; a loop-head set `H` contained in the prologue's
    result is accepted by one iteration and contained in its result, which
    also holds the counter; and the epilogue is accepted from `H`. -/
def rolledCheck (Pin : List String) (r : RolledShape) : Bool :=
  match pubRun Pin r.pre with
  | none => false
  | some P0 =>
      let H := headSet P0 (r.body ++ [cmpZero r.ctr]) 4
      match pubRun H (r.body ++ [cmpZero r.ctr]) with
      | none => false
      | some P1 => H.all (fun x => decide (x ∈ P0)) && H.all (fun x => decide (x ∈ P1))
          && decide (r.ctr ∈ P1) && (pubRun H r.post).isSome

theorem loopLeak_sound {w : Nat} (r : RolledShape) {P0 P1 : List String}
    (h1 : pubRun P0 (r.body ++ [cmpZero r.ctr]) = some P1)
    (hsub : ∀ x ∈ P0, x ∈ P1) (hctr : r.ctr ∈ P1) :
    ∀ (fuel : Nat) {s₁ s₂ : Lstate w}, Agree P0 s₁ s₂ →
      (loopLeak r fuel s₁).1 = (loopLeak r fuel s₂).1
        ∧ Agree P0 (loopLeak r fuel s₁).2 (loopLeak r fuel s₂).2
  | 0, s₁, s₂, h => ⟨rfl, h⟩
  | fuel + 1, s₁, s₂, h => by
      obtain ⟨hl, hs⟩ := pubRun_sound _ h1 h
      have hc := hs r.ctr hctr
      obtain ⟨hl', hs'⟩ := loopLeak_sound r h1 hsub hctr fuel (agree_mono hsub hs)
      simp only [loopLeak]
      rw [hc]
      split
      · simp only [hl, hl', true_and]; exact hs'
      · simp only [hl, true_and]; exact agree_mono hsub hs

/-- **Constant time of an accepted rolled function.** If `rolledCheck Pin r`
    holds, the address-leak trace of the rolled function is the same from any two
    states that agree on the registers `Pin`, for every iteration bound: the
    instructions executed, every register-indexed effective address and every
    branch direction are functions of the registers `Pin` alone, whatever the
    memory holds. -/
theorem rolledLeak_pub_determined {w : Nat} (Pin : List String) (r : RolledShape)
    (hchk : rolledCheck Pin r = true) (fuel : Nat) {s₁ s₂ : Lstate w}
    (h : Agree Pin s₁ s₂) : rolledLeak r fuel s₁ = rolledLeak r fuel s₂ := by
  unfold rolledCheck at hchk
  split at hchk
  · exact absurd hchk (by simp)
  rename_i P0 h0
  dsimp only at hchk
  split at hchk
  · exact absurd hchk (by simp)
  rename_i P1 h1
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hH0, hsub⟩, hctr⟩, hpost⟩ := hchk
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hpost
  obtain ⟨ha, has⟩ := pubRun_sound _ h0 h
  obtain ⟨hb, hbs⟩ := loopLeak_sound r h1 hsub hctr fuel (agree_mono hH0 has)
  obtain ⟨hc, -⟩ := pubRun_sound _ hQ hbs
  simp only [rolledLeak]
  rw [ha, hb, hc]

/-! ### Recognising the rolled shape of a compiled function -/

/-- Split a list at its first internal label. -/
def splitAtLabel : List LinstrR → Option (List LinstrR × LLabel × List LinstrR)
  | [] => none
  | .Llabel .internal top :: rest => some ([], top, rest)
  | i :: rest => (splitAtLabel rest).map (fun x => (i :: x.1, x.2.1, x.2.2))

theorem splitAtLabel_eq : ∀ (L : List LinstrR) {a : List LinstrR} {t : LLabel}
    {b : List LinstrR}, splitAtLabel L = some (a, t, b) → L = a ++ .Llabel .internal t :: b
  | [], _, _, _, h => by simp [splitAtLabel] at h
  | i :: rest, a, t, b, h => by
      by_cases hi : ∃ top, i = .Llabel .internal top
      · obtain ⟨top, rfl⟩ := hi
        simp only [splitAtLabel, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      · have hs : splitAtLabel (i :: rest)
            = (splitAtLabel rest).map (fun x => (i :: x.1, x.2.1, x.2.2)) := by
          cases i with
          | Llabel k top =>
              cases k
              · exact absurd ⟨top, rfl⟩ hi
              · rfl
          | _ => rfl
        rw [hs] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨a', t', b'⟩, hx, hy⟩ := h
        simp only [Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl, rfl⟩ := hy
        rw [splitAtLabel_eq rest hx]; rfl

/-- Recognise `CMP ctr, 0; jnz top` at the head of `i :: rest`. -/
def backEdgeAt? : LinstrR → List LinstrR → Option (String × LLabel × List LinstrR)
  | .Lopn [.reg c] op [.reg c', .imm 0], .Lcond (.reg nz) t :: post =>
      if op = "CMP:64" ∧ c' = c ∧ nz = "NZ" then some (c, t, post) else none
  | _, _ => none

theorem backEdgeAt?_eq {i : LinstrR} {rest : List LinstrR} {c : String} {t : LLabel}
    {post : List LinstrR} (h : backEdgeAt? i rest = some (c, t, post)) :
    i :: rest = cmpZero c :: backEdge t :: post := by
  unfold backEdgeAt? at h
  split at h
  · split_ifs at h with hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp at h

/-- Split a list at its first counter back-edge. -/
def splitAtBack : List LinstrR → Option (List LinstrR × String × LLabel × List LinstrR)
  | [] => none
  | i :: rest =>
      match backEdgeAt? i rest with
      | some (c, t, post) => some ([], c, t, post)
      | none => (splitAtBack rest).map (fun x => (i :: x.1, x.2))

theorem splitAtBack_eq : ∀ (L : List LinstrR) {a : List LinstrR} {c : String} {t : LLabel}
    {p : List LinstrR}, splitAtBack L = some (a, c, t, p) →
      L = a ++ cmpZero c :: backEdge t :: p
  | [], _, _, _, _, h => by simp [splitAtBack] at h
  | i :: rest, a, c, t, p, h => by
      unfold splitAtBack at h
      split at h
      · rename_i c' t' post' hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact backEdgeAt?_eq hb
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨a', x⟩, hx, hy⟩ := h
        simp only [Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        rw [splitAtBack_eq rest hx]; rfl

/-- Recognise a function body as a rolled counted loop. -/
def rolledShape? (L : List LinstrR) : Option RolledShape := do
  let (pre, top, rest) ← splitAtLabel L
  let (body, c, t, post) ← splitAtBack rest
  if t = top then some ⟨pre, top, body, c, post⟩ else none

theorem rolledShape?_toBody {L : List LinstrR} {r : RolledShape}
    (h : rolledShape? L = some r) : r.toBody = L := by
  simp only [rolledShape?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨pre, top, rest⟩, h1, ⟨body, c, t, post⟩, h2, h3⟩ := h
  split_ifs at h3 with ht
  subst ht
  simp only [Option.some.injEq] at h3
  subst h3
  rw [splitAtLabel_eq L h1, splitAtBack_eq rest h2]
  simp [RolledShape.toBody]

/-- Every function of `p` is a rolled counted loop accepted by `rolledCheck`
    from the entry set `Pin`. -/
def rolledLprogCheck (Pin : List String) (p : Lprog) : Bool :=
  p.lp_funcs.all fun f =>
    match rolledShape? (f.2.lfd_body.map (·.li_i)) with
    | some r => rolledCheck Pin r
    | none => false

/-- **Constant time of an accepted compiled program.** When
    `rolledLprogCheck Pin p` holds, every function body of `p` is a rolled
    counted loop `r`, and its address-leak trace `rolledLeak r` is the same from
    any two states that agree on the registers `Pin`, at every word width and
    every iteration bound. -/
theorem rolledLprog_pub_determined (Pin : List String) (p : Lprog)
    (hchk : rolledLprogCheck Pin p = true) :
    ∀ f ∈ p.lp_funcs, ∃ r : RolledShape, r.toBody = f.2.lfd_body.map (·.li_i) ∧
      ∀ (w fuel : Nat) (s₁ s₂ : Lstate w), Agree Pin s₁ s₂ →
        rolledLeak r fuel s₁ = rolledLeak r fuel s₂ := by
  intro f hf
  have hf' := List.all_eq_true.mp hchk f hf
  split at hf'
  · rename_i r hr
    exact ⟨r, rolledShape?_toBody hr, fun w fuel s₁ s₂ h =>
      rolledLeak_pub_determined Pin r hf' fuel h⟩
  · exact absurd hf' (by simp)

/-! ### Non-vacuity -/

/-- A rolled loop whose load index is the counter image `RBX`. -/
def publicIndexLoop : RolledShape where
  pre := [.Lopn [.reg "RBX"] "MOV:64" [.imm 0], .Lopn [.reg "RCX"] "MOV:64" [.imm 4]]
  top := 1
  body := [.Lopn [.reg "RAX"] "LOADIDX" [.arrIdx "RDI" "RBX" 8],
           .Lopn [.reg "RBX"] "ADD:64" [.reg "RBX", .imm 1],
           .Lopn [.reg "RCX"] "SUB:64" [.reg "RCX", .imm 1]]
  ctr := "RCX"
  post := [.Lret]

/-- The same loop with a second load indexed by the loaded value `RAX`. -/
def secretIndexLoop : RolledShape :=
  { publicIndexLoop with
    body := publicIndexLoop.body ++ [.Lopn [.reg "RDX"] "LOADIDX" [.arrIdx "RDI" "RAX" 8]] }

/-- The analysis accepts the counter-indexed loop from the public pointer `RDI`. -/
theorem publicIndexLoop_accepted : rolledCheck ["RDI"] publicIndexLoop = true := by decide

/-- The analysis rejects a load indexed by a loaded (secret) value. -/
theorem secretIndexLoop_rejected : rolledCheck ["RDI"] secretIndexLoop = false := by decide

end RolledCT

end CatCrypt.Crypto.Jasmin.JincToLowCT
