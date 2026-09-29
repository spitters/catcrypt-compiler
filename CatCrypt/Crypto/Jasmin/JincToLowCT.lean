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

§8 states constant time for the `Lprog` the printer receives, after the
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

## A source `while` under a countdown

A source `while (g != 0)` runs as a countdown loop whose trip count is a
caller-supplied seed, so the rendered body runs `seed` times whatever the guard
holds. The guard rides the state array with the other carried scalars, and each
iteration is gated by it without a branch (`gatedIter`): every array access goes
through a mask that is all ones while the guard is non-zero and zero once it is
zero, and under the zero mask every access addresses cell `0` and every store
writes back the word it read. `gatedIter_frame` states that, under the
word-cell reading `WExec`, an iteration whose guard cell holds zero leaves every
array unchanged, and `gatedFor_frame` that any number of such iterations do, so
a seed at least the source's iteration count gives the source's result.

## Main definitions

* `stmtToLowCT` / `stmtsToLowCT`: the statement translation.
* `jfunToLowCT`: a whole `JFun` body as one `LowCT`.
* `jfunLeaf`: a leaf's loop, its ABI names, its trip count and its carried
  scalars.
* `carryLoad` / `carryStore` / `withCarried`: a body's carried scalars read
  from and written back to the state array.
* `rbwGo` / `carriedOf`: the scalars a loop body reads before it writes them.
* `for2Lprog`: a counted loop through the front to the program the owned
  printer receives.
* `forCarriedLprog` / `whileCarriedLprog`: a counted loop and a countdown loop
  over the state-array ABI, for a loop with carried scalars; the countdown form
  runs `gatedIter`.
* `maskExpr` / `gateAccess` / `gatedIter`: an iteration of a countdown loop
  gated by the source guard.
* `WExec` / `gatedIter_frame` / `gatedFor_frame`: the word-cell reading of the
  translated constructors, and the statement that an iteration with a zero
  guard changes no array.
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
  | .andn, a, b => .SAnd (.SXor a (.SLit (2 ^ 64 - 1))) b

/-- The `SExpr` of `e` rotated right by `n` within 64 bits: `e >>> n` or-ed with
    `e <<< (64 - n)` masked to 64 bits, and `e` itself when `n` is a multiple of 64. -/
def rorExpr (n : Nat) (e : SExpr) : SExpr :=
  if n % 64 = 0 then e
  else opExpr .or (.SShr e (.SLit (n % 64)))
    (.SAnd (.SShl e (.SLit (64 - n % 64))) (.SLit (2 ^ 64 - 1)))

/-- The `SExpr` of a binary right-hand operand. -/
def operandExpr : Operand → SExpr
  | .var s => .SVar s
  | .lit n => .SLit n

/-- `e` masked to `w` bits, the identity at `w ≥ 64`. -/
def truncate (w : Nat) (e : SExpr) : SExpr :=
  if w ≥ 64 then e else .SAnd e (.SLit (2 ^ w - 1))

/-- The `SExpr` of a right-hand side that reads no memory.

    `none` on six right-hand sides. `load` and `castLoad` become `RArrLoad` in
    `assignRhs`. `select` has no translation: `cond ? t : f` is branch-free only
    when `cond` is known to be `0` or `1`, which the untyped AST does not
    record. A `glob` naming something other than a declared scalar is a
    global-table binding (`tbl = EC_DLOG`); `LowCT` reaches a table as a loop
    invariant array parameter, not as a bound name. An external `call` and a
    256-bit vector op `ymm` have no `LowCT` image. -/
def rhsExpr (env : Env) : Rhs → Option SExpr
  | .bin op a b => some (opExpr op (.SVar a) (operandExpr b))
  | .imm n => some (.SLit n)
  | .glob v => if env.isScalar v then some (.SVar v) else none
  | .cast w src => some (truncate w (.SVar src))
  | .load _ _ => none
  | .castLoad _ _ _ => none
  | .select _ _ _ => none
  | .ror n src => some (rorExpr n (.SVar src))
  | .call _ _ => none
  | .ymm _ _ => none

/-- The `or` translation denotes bitwise or over wrapping 64-bit words. -/
theorem evalBV_opExpr_or (β : String → BitVec 64) (a b : SExpr) :
    (opExpr .or a b).evalBV β = a.evalBV β ||| b.evalBV β := by
  simp only [opExpr, SExpr.evalBV]
  generalize a.evalBV β = x
  generalize b.evalBV β = y
  bv_decide

/-- The `andn` translation denotes `(~a) & b` over wrapping 64-bit words. -/
theorem evalBV_opExpr_andn (β : String → BitVec 64) (a b : SExpr) :
    (opExpr .andn a b).evalBV β = ~~~(a.evalBV β) &&& b.evalBV β := by
  simp only [opExpr, SExpr.evalBV]
  generalize a.evalBV β = x
  generalize b.evalBV β = y
  bv_decide

/-- The rotate translation denotes `BitVec.rotateRight` over wrapping 64-bit
    words. -/
theorem evalBV_rorExpr (β : String → BitVec 64) (n : Nat) (e : SExpr) :
    (rorExpr n e).evalBV β = (e.evalBV β).rotateRight n := by
  unfold rorExpr
  split
  · rename_i h
    rw [BitVec.rotateRight_def, h]
    simp
  · rename_i h
    rw [evalBV_opExpr_or, BitVec.rotateRight_def]
    simp only [SExpr.evalBV]
    have hk : n % 64 < 64 := Nat.mod_lt _ (by decide)
    have h1 : (BitVec.ofNat 64 (n % 64)).toNat = n % 64 := by
      simp only [BitVec.toNat_ofNat]; omega
    have h2 : (BitVec.ofNat 64 (64 - n % 64)).toNat = 64 - n % 64 := by
      simp only [BitVec.toNat_ofNat]; omega
    rw [h1, h2]
    generalize e.evalBV β = x
    congr 1
    generalize x <<< (64 - n % 64) = y
    bv_decide

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
    (see `rhsExpr`), and on a run-time loop `forRt`. -/
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
  | .forRt _ _ _ => none

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

/-- The scalar the guard's state cell is read into. -/
def gateWord : String := "__jinc_gw"

/-- The scalar holding an iteration's mask. -/
def maskName : String := "__jinc_mask"

/-- The scalar holding a gated array index. -/
def gateIdx : String := "__jinc_gi"

/-- The scalar holding the cell a gated store reads before writing. -/
def gateOld : String := "__jinc_old"

/-- The scalar holding the word a gated store writes. -/
def gateSel : String := "__jinc_sel"

/-- The scalar slots the gating of a countdown iteration reserves. -/
def gateNames : List String := [gateWord, maskName, gateIdx, gateOld, gateSel]

/-- The scalar slots written by the constructors `WExec` gives a meaning to. -/
def scalarWrites : LowCT → List String
  | .RSeq a b => scalarWrites a ++ scalarWrites b
  | .RScalarSetExpr x _ => [x]
  | .RArrLoad dst _ _ => [dst.locVar]
  | .RFor x _ b => x :: scalarWrites b
  | .RWhileNz _ b => scalarWrites b
  | _ => []

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
  /-- The scalars the loop carries across iterations through the state array:
      those the body reads before it writes them, and a countdown loop's guard. -/
  carried : List String
  /-- The source guard of a countdown loop. -/
  guard : Option String := none

/-- The loop of a leaf with two array parameters, the first rewritten in place
    and the second read.

    `none` unless the body is a prologue of scalar initialisations, then one
    loop, then `return`s. The leaf's `carried` names are the scalars the loop
    body reads before it writes them, headed by the guard for a `while`; the
    prologue supplies their entry values. A `for` whose prologue only zeroes
    slots the body overwrites leaves `carried` empty, so such a leaf keeps the
    two-array ABI. A `while` is declined when the leaf declares a scalar with
    one of the `gateNames` or its body writes `maskName`, the slots its gating
    reserves. -/
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
          | .whileNz g b => do
              let c ← stmtsToLowCT env b
              if gateNames.any env.scalars.contains || (scalarWrites c).contains maskName then
                none
              else
                pure { accName := acc, accWords := nAcc, invName := inv, invWords := nInv,
                       idxName := tripName, body := c, trips := none,
                       carried := carriedOf tripName (.RWhileNz g c), guard := some g }
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

/-! ## 6. Gating a countdown iteration by the source guard

The countdown loop of `whileCarriedLprog` runs its body as many times as the
caller's seed says, and the source loop runs it while its guard is non-zero.
`gatedIter` turns an iteration after the guard has become zero into a no-op
without a branch. It reads the guard's state cell, forms `maskExpr` of it (all
ones when the guard is non-zero, zero when it is zero), and `gateAccess` routes
every array access of the body and of the carried-scalar write-back through the
mask: a load reads cell `idx &&& mask`, and a store reads cell `idx &&& mask`
and writes back `old ^^^ ((old ^^^ v) &&& mask)`. Under the all-ones mask these
are the source's accesses and words; under the zero mask every access
addresses cell `0` and every store writes back the word it read.

The mask is built from `SSub`, `SAnd` and `SShr`, which the front lowers, and
its value is the one `SExpr.evalBV` gives over wrapping 64-bit words. The
truncating `SExpr.eval` sends `0 - 1` to `0`, so the all-ones case does not
hold over it. The zero case is `evalBV_maskExpr_zero`.

`WExec` is the word-cell reading of the constructors the translation emits:
scalars are 64-bit words evaluated by `SExpr.evalBV`, and each array is a map
from cell index to 64-bit word, the representation of the module header.
`gatedIter_frame` states that under it an iteration whose guard cell holds zero
changes no array, the state array holding the carried scalars included, and
`gatedFor_frame` extends that to any number of iterations. -/

/-- `1` when `g` is non-zero and `0` when it is zero, over 64-bit words:
    `0 - (g &&& (0 - g))` is `g ||| (0 - g)`, whose bit 63 is set exactly when
    `g ≠ 0`. -/
def nzBit (g : SExpr) : SExpr :=
  .SShr (.SSub (.SLit 0) (.SAnd g (.SSub (.SLit 0) g))) (.SLit 63)

/-- The all-ones word when `g` is non-zero and the zero word when it is zero. -/
def maskExpr (g : SExpr) : SExpr := .SSub (.SLit 0) (nzBit g)

/-- `maskExpr` over `SExpr.evalBV` is the zero word at a zero guard. -/
theorem evalBV_maskExpr_zero (β : String → BitVec 64) (x : String) (h : β x = 0) :
    (maskExpr (.SVar x)).evalBV β = 0 := by
  simp only [maskExpr, nzBit, SExpr.evalBV, h]
  decide

/-- The word a gated store writes: the cell's old word where the mask is zero
    and the source word `src` where it is all ones. -/
def gatedSel (src : String) : SExpr :=
  .SXor (.SVar gateOld) (.SAnd (.SXor (.SVar gateOld) (.SVar src)) (.SVar maskName))

/-- `gateIdx` set to `idx` under the mask. -/
def gateIndex (idx : String) : LowCT :=
  .RScalarSetExpr gateIdx (.SAnd (.SVar idx) (.SVar maskName))

/-- Every array access of `c` routed through the mask in `maskName`. A load
    reads cell `idx &&& mask`; a store reads cell `idx &&& mask` into `gateOld`
    and writes `gatedSel` back to it. Loop bodies are gated in place; every
    other constructor is left as it is. -/
def gateAccess : LowCT → LowCT
  | .RSeq a b => .RSeq (gateAccess a) (gateAccess b)
  | .RArrLoad dst l idx => .RSeq (gateIndex idx) (.RArrLoad dst l gateIdx)
  | .RArrStore l idx src =>
      .RSeq (gateIndex idx) (.RSeq (.RArrLoad (u64Loc gateOld) l gateIdx)
        (.RSeq (.RScalarSetExpr gateSel (gatedSel src.locVar))
          (.RArrStore l gateIdx (u64Loc gateSel))))
  | .RFor x n b => .RFor x n (gateAccess b)
  | .RWhileNz g b => .RWhileNz g (gateAccess b)
  | c => c

/-- Read the guard `g`'s state cell into `gateWord` and set `maskName` from it. -/
def maskLoad (g : String) (names : List String) : LowCT :=
  .RSeq (.RScalarSetExpr stateIdx (.SLit (names.idxOf g)))
    (.RSeq (.RArrLoad (u64Loc gateWord) (stateLoc names.length) stateIdx)
      (.RScalarSetExpr maskName (maskExpr (.SVar gateWord))))

/-- One iteration of a countdown loop gated by the source guard `g`: the
    carried scalars read from the state array, the mask formed from `g`'s cell,
    then the body and the write-back of the carried scalars with every array
    access gated. -/
def gatedIter (g : String) (names : List String) (body : LowCT) : LowCT :=
  .RSeq (carryLoad names) (.RSeq (maskLoad g names) (gateAccess (seq2 body (carryStore names))))

/-- A state of the word-cell reading: 64-bit scalar slots, and each array a map
    from cell index to 64-bit word. -/
structure WState where
  sc : String → BitVec 64
  arr : String → Nat → BitVec 64

/-- `s` with the scalar `x` set to `v`. -/
def WState.setSc (s : WState) (x : String) (v : BitVec 64) : WState :=
  ⟨Function.update s.sc x v, s.arr⟩

/-- `s` with cell `i` of the array `a` set to `v`. -/
def WState.setCell (s : WState) (a : String) (i : Nat) (v : BitVec 64) : WState :=
  ⟨s.sc, Function.update s.arr a (Function.update (s.arr a) i v)⟩

@[simp] theorem WState.setSc_arr (s : WState) (x : String) (v : BitVec 64) :
    (s.setSc x v).arr = s.arr := rfl

@[simp] theorem WState.setSc_sc (s : WState) (x y : String) (v : BitVec 64) :
    (s.setSc x v).sc y = if y = x then v else s.sc y := by
  simp [WState.setSc, Function.update_apply]

@[simp] theorem WState.setCell_sc (s : WState) (a : String) (i : Nat) (v : BitVec 64) :
    (s.setCell a i v).sc = s.sc := rfl

/-- The word-cell big-step reading of the constructors the translation emits.
    Expressions evaluate by `SExpr.evalBV`, over wrapping 64-bit words; a load
    reads the cell its index scalar names and a store writes the source
    scalar's word to that cell. Other constructors have no rule. -/
inductive WExec : LowCT → WState → WState → Prop where
  | skip (s : WState) : WExec .RSkip s s
  | seq (a b : LowCT) (s t u : WState) : WExec a s t → WExec b t u → WExec (.RSeq a b) s u
  | set (x : String) (e : SExpr) (s : WState) :
      WExec (.RScalarSetExpr x e) s (s.setSc x (e.evalBV s.sc))
  | load (dst l : Located) (idx : String) (s : WState) :
      WExec (.RArrLoad dst l idx) s (s.setSc dst.locVar (s.arr l.locVar (s.sc idx).toNat))
  | store (l : Located) (idx : String) (src : Located) (s : WState) :
      WExec (.RArrStore l idx src) s (s.setCell l.locVar (s.sc idx).toNat (s.sc src.locVar))
  | forZero (x : String) (b : LowCT) (s : WState) : WExec (.RFor x 0 b) s s
  | forSucc (x : String) (n : Nat) (b : LowCT) (s t u : WState) :
      WExec (.RFor x n b) s t → WExec b (t.setSc x (BitVec.ofNat 64 n)) u →
      WExec (.RFor x (n + 1) b) s u
  | whileFalse (g : String) (b : LowCT) (s : WState) : s.sc g = 0 → WExec (.RWhileNz g b) s s
  | whileTrue (g : String) (b : LowCT) (s t u : WState) :
      s.sc g ≠ 0 → WExec b s t → WExec (.RWhileNz g b) t u → WExec (.RWhileNz g b) s u

/-- Running `c` from a state whose mask is zero leaves every array unchanged and
    the mask zero. -/
def MaskFrame (c : LowCT) : Prop :=
  ∀ s s', WExec c s s' → s.sc maskName = 0 → s'.arr = s.arr ∧ s'.sc maskName = 0

theorem maskFrame_seq {a b : LowCT} (ha : MaskFrame a) (hb : MaskFrame b) :
    MaskFrame (.RSeq a b) := by
  intro s s' h hm
  cases h with
  | seq _ _ _ t _ h1 h2 =>
    obtain ⟨h1a, h1m⟩ := ha _ _ h1 hm
    obtain ⟨h2a, h2m⟩ := hb _ _ h2 h1m
    exact ⟨h2a.trans h1a, h2m⟩

theorem maskFrame_set {x : String} (e : SExpr) (hx : x ≠ maskName) :
    MaskFrame (.RScalarSetExpr x e) := by
  intro s s' h hm
  cases h
  exact ⟨rfl, by simp [Ne.symm hx, hm]⟩

theorem maskFrame_load {dst : Located} (l : Located) (idx : String)
    (hx : dst.locVar ≠ maskName) : MaskFrame (.RArrLoad dst l idx) := by
  intro s s' h hm
  cases h
  exact ⟨rfl, by simp [Ne.symm hx, hm]⟩

/-- A gated store under a zero mask writes cell `0` of its array with the word
    it read there. -/
theorem maskFrame_gatedStore (l : Located) (idx : String) (src : Located) :
    MaskFrame (gateAccess (.RArrStore l idx src)) := by
  intro s s' h hm
  simp only [gateAccess, gateIndex] at h
  cases h with | seq _ _ _ t₁ _ h1 h =>
  cases h with | seq _ _ _ t₂ _ h2 h =>
  cases h with | seq _ _ _ t₃ _ h3 h4 =>
  cases h1; cases h2; cases h3; cases h4
  have hgi : gateIdx ≠ maskName := by decide
  have hgo : gateOld ≠ maskName := by decide
  have hgs : gateSel ≠ maskName := by decide
  have h1 : gateOld ≠ gateIdx := by decide
  have h2 : gateSel ≠ gateOld := by decide
  have h3 : gateSel ≠ gateIdx := by decide
  refine ⟨?_, ?_⟩
  · simp only [u64Loc, WState.setSc_sc, WState.setSc_arr, SExpr.evalBV, gatedSel,
      if_true, h1, h2, h3, h1.symm, h3.symm, hgi.symm, hgo.symm, if_false, hm]
    simp [WState.setCell]
  · simp [u64Loc, WState.setCell, hgi.symm, hgo.symm, hgs.symm, hm]

theorem maskFrame_for {x : String} {b : LowCT} (hx : x ≠ maskName) (hb : MaskFrame b) :
    ∀ n, MaskFrame (.RFor x n b) := by
  intro n s s' h
  generalize hC : LowCT.RFor x n b = C at h
  induction h generalizing n with
  | forZero => intro hm; exact ⟨rfl, hm⟩
  | forSucc x' n' b' s t u h1 h2 ih1 _ =>
      cases hC
      intro hm
      obtain ⟨h1a, h1m⟩ := ih1 n' rfl hm
      obtain ⟨h2a, h2m⟩ := hb _ _ h2 (by simp [Ne.symm hx, h1m])
      exact ⟨h2a.trans h1a, h2m⟩
  | _ => cases hC

theorem maskFrame_while {g : String} {b : LowCT} (hb : MaskFrame b) :
    MaskFrame (.RWhileNz g b) := by
  intro s s' h
  generalize hC : LowCT.RWhileNz g b = C at h
  induction h with
  | whileFalse => intro hm; exact ⟨rfl, hm⟩
  | whileTrue g' b' s t u _ h1 _ _ ih2 =>
      cases hC
      intro hm
      obtain ⟨h1a, h1m⟩ := hb _ _ h1 hm
      obtain ⟨h2a, h2m⟩ := ih2 rfl h1m
      exact ⟨h2a.trans h1a, h2m⟩
  | _ => cases hC

/-- **The gated program keeps the arrays under a zero mask.** When `c` writes no
    scalar named `maskName`, running `gateAccess c` from a state whose mask is
    zero changes no array and leaves the mask zero. -/
theorem gateAccess_maskFrame : ∀ (c : LowCT), maskName ∉ scalarWrites c →
    MaskFrame (gateAccess c)
  | .RSeq a b, hc => by
      simp only [scalarWrites, List.mem_append, not_or] at hc
      exact maskFrame_seq (gateAccess_maskFrame a hc.1) (gateAccess_maskFrame b hc.2)
  | .RArrLoad dst l idx, hc => by
      simp only [scalarWrites, List.mem_singleton] at hc
      exact maskFrame_seq (maskFrame_set _ (by decide)) (maskFrame_load l _ (Ne.symm hc))
  | .RArrStore l idx src, _ => maskFrame_gatedStore l idx src
  | .RFor x n b, hc => by
      simp only [scalarWrites, List.mem_cons, not_or] at hc
      exact maskFrame_for (Ne.symm hc.1) (gateAccess_maskFrame b hc.2) n
  | .RWhileNz g b, hc => by
      simp only [scalarWrites] at hc
      exact maskFrame_while (gateAccess_maskFrame b hc)
  | .RScalarSetExpr x e, hc => by
      simp only [scalarWrites, List.mem_singleton] at hc
      exact maskFrame_set e (Ne.symm hc)
  | .RSkip, _ => fun s s' h hm => by cases h; exact ⟨rfl, hm⟩
  | .RLetZero .., _ | .RLetU64Zero .., _ | .RScalarSet .., _ | .RCall .., _
  | .RCallSwap .., _ | .RCloneCall .., _ | .RIfNz .., _ | .RLimbStore .., _
  | .RLimbStoreExpr .., _ | .RCallN .., _ | .RSelect .., _ | .RAssert .., _
  | .RBlock .., _ | .RFnDef .., _ | .RFnCall .., _ | .RTupleLoad .., _
  | .RArrStoreLit .., _ | .RArrLoadLit .., _ | .RCallDstThreaded .., _
  | .RForRuntime .., _ | .RCopy .., _ => fun _ _ h _ => by cases h

theorem scalarWrites_seq2 (a b : LowCT) (x : String) (h : x ∈ scalarWrites (seq2 a b)) :
    x ∈ scalarWrites a ∨ x ∈ scalarWrites b := by
  unfold seq2 at h
  split at h <;> simp_all [scalarWrites]

/-- The write-back of the carried scalars writes no scalar but `stateIdx`. -/
theorem scalarWrites_carryStore (names : List String) (x : String)
    (h : x ∈ scalarWrites (carryStore names)) : x = stateIdx := by
  unfold carryStore at h
  generalize names.zipIdx = L at h
  induction L with
  | nil => simp [scalarWrites] at h
  | cons p L ih =>
      rcases scalarWrites_seq2 _ _ x h with h | h
      · simpa [scalarWrites] using h
      · rcases scalarWrites_seq2 _ _ x h with h | h
        · simp [scalarWrites] at h
        · exact ih h

/-- Running `c` leaves every array unchanged. -/
def ArrFrame (c : LowCT) : Prop := ∀ s s', WExec c s s' → s'.arr = s.arr

theorem arrFrame_seq2 {a b : LowCT} (ha : ArrFrame a) (hb : ArrFrame b) :
    ArrFrame (seq2 a b) := by
  unfold seq2
  split
  · exact hb
  · exact ha
  · intro s s' h
    cases h with | seq _ _ _ t _ h1 h2 => exact (hb _ _ h2).trans (ha _ _ h1)

/-- Reading the carried scalars changes no array. -/
theorem carryLoad_arrFrame (names : List String) : ArrFrame (carryLoad names) := by
  unfold carryLoad
  generalize names.zipIdx = L
  induction L with
  | nil => intro s s' h; cases h; rfl
  | cons p L ih =>
      refine arrFrame_seq2 (fun s s' h => by cases h; rfl)
        (arrFrame_seq2 (fun s s' h => by cases h; rfl) ih)

/-- **A gated iteration with a zero guard cell changes no array.** Under the
    word-cell reading `WExec`, one iteration `gatedIter g names body` from a
    state whose state-array cell for the guard `g` holds zero leaves every array
    unchanged: the state array, whose cells hold the carried scalars, and every
    array the body reads or writes. -/
theorem gatedIter_frame (g : String) (names : List String) (body : LowCT)
    (hbody : maskName ∉ scalarWrites body) (hlen : names.length < 2 ^ 64)
    {s s' : WState} (h : WExec (gatedIter g names body) s s')
    (h0 : s.arr stateName (names.idxOf g) = 0) : s'.arr = s.arr := by
  cases h with | seq _ _ _ t₁ _ hl h =>
  cases h with | seq _ _ _ t₂ _ hm h =>
  have hl' := carryLoad_arrFrame names _ _ hl
  simp only [maskLoad] at hm
  cases hm with | seq _ _ _ u₁ _ hm1 hm =>
  cases hm with | seq _ _ _ u₂ _ hm2 hm3 =>
  cases hm1; cases hm2; cases hm3
  have hlt := lt_of_le_of_lt (List.idxOf_le_length (a := g) (l := names)) hlen
  have hidx : (names.idxOf g) % 18446744073709551616 = names.idxOf g :=
    Nat.mod_eq_of_lt (by simpa using hlt)
  have hmask : maskName ∉ scalarWrites (seq2 body (carryStore names)) := by
    intro hw
    rcases scalarWrites_seq2 _ _ _ hw with hw | hw
    · exact hbody hw
    · exact absurd (scalarWrites_carryStore names _ hw) (by decide)
  refine ((gateAccess_maskFrame _ hmask _ _ h ?_).1).trans hl'
  simp only [WState.setSc_sc, if_true]
  exact evalBV_maskExpr_zero _ _ (by simp [u64Loc, stateLoc, hl', hidx, h0, SExpr.evalBV])

/-- **Iterations after the source loop's exit are no-ops.** Any number `k` of
    gated iterations from a state whose guard cell holds zero leave every array
    unchanged, whatever the loop index slot `x` is set to. -/
theorem gatedFor_frame (g x : String) (names : List String) (body : LowCT)
    (hbody : maskName ∉ scalarWrites body) (hlen : names.length < 2 ^ 64) (k : Nat)
    {s s' : WState} (h : WExec (.RFor x k (gatedIter g names body)) s s')
    (h0 : s.arr stateName (names.idxOf g) = 0) : s'.arr = s.arr := by
  generalize hC : LowCT.RFor x k (gatedIter g names body) = C at h
  induction h generalizing k with
  | forZero => rfl
  | forSucc x' n' b' s t u h1 h2 ih1 _ =>
      cases hC
      have ht := ih1 n' h0 rfl
      have hu := gatedIter_frame g names body hbody hlen h2 (by simpa [ht] using h0)
      exact hu.trans ht
  | _ => cases hC

/-! ## 7. Owned x86 renders -/

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
    printer receives, each iteration gated by the source guard `guard`
    (`gatedIter`).

    `ComL.whileNz` reads its trip from an in-scope 64-bit seed register, so the
    rendered leaf takes it as a fourth argument: `%rdi` the state array, `%rsi`
    and `%rdx` the two source arrays, `%rcx` the countdown seed, matching
    `T *sym(uint64_t *state, uint64_t *acc, const uint64_t *inv, uint64_t seed)`.
    The body runs `seed` times, at least once; an iteration after the guard's
    state cell holds zero changes no array (`gatedIter_frame`), so any seed at
    least the source loop's iteration count gives the source's arrays and
    carried exit values. The seed is the head of `Γouter` because
    `JasminLprogExport.resolveVar` numbers a context variable's argument slot
    from the end of the context. -/
def whileCarriedLprog (sym guard : String) (carried : List String) (wAcc wInv : Nat)
    (accName idxName invName : String) (body : LowCT) : Option Lprog :=
  (compileLoop
      (Γouter := [.reg 64, .stackArr 64 carried.length, .stackArr 64 wAcc,
                  .stackArr 64 wInv])
      (accCTy := .memref carried.length) (invCTys := [.memref wAcc, .memref wInv])
      .plain (.countdown .here)
      ((((VarMap.empty.bind (t := .memref wInv) invName).bind
          (t := .memref wAcc) accName).bind
          (t := .sword 64) idxName).bind (t := .memref carried.length) stateName)
      stateName (gatedIter guard carried body) (init := .there .here)
      (invs := .cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))).map
    (fun c =>
      renderLeafLprog
        (ComL.toLprogPhysAbi c sym (argName 0) [argName 1, argName 2, argName 3]
          (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]))

/-- The program the owned printer receives for a parsed leaf under the symbol
    `sym`, `none` when `jfunLeaf` rejects the shape or the body front declines
    the body.

    A counted loop with no carried scalar compiles over the two-array ABI and
    one with carried scalars over the state-array ABI of `forCarriedLprog`. A
    countdown loop carries at least its guard and compiles over the state-array
    ABI of `whileCarriedLprog`. -/
def jfunLeafLprog (sym : String) (f : JFun) : Option Lprog := do
  let l ← jfunLeaf f
  match l.carried, l.trips, l.guard with
  | [], some n, _ =>
      for2Lprog sym l.accWords l.invWords l.accName l.idxName l.invName n l.body
  | c, some n, _ =>
      forCarriedLprog sym c l.accWords l.invWords l.accName l.idxName l.invName n l.body
  | c, none, some g =>
      whileCarriedLprog sym g c l.accWords l.invWords l.accName l.idxName l.invName l.body
  | _, none, none => none

/-- A parsed leaf rendered to owned AT&T x86 under the symbol `sym`: the printer
    applied to `jfunLeafLprog`. -/
def renderJFunLeaf (sym : String) (f : JFun) : Option String :=
  (jfunLeafLprog sym f).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt

/-! ## 8. Constant time of a rolled render -/

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
