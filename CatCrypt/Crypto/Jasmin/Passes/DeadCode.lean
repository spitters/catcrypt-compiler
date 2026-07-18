/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.PassFramework

/-!
# Dead Code Elimination Pass

Remove assignments to variables that are never subsequently read.

## Main definitions

* `exprVars` — Collect variables read by an expression
* `instrReads` / `instrWrites` — Variables read/written by an instruction
* `liveAfterCmd` — Backward liveness analysis
* `deadCodeElim` — Remove dead assignments

## Design

This implements a simplified backward liveness analysis:
1. Start from the set of "live-out" variables (those needed after the command)
2. Walk backwards through instructions
3. An assignment `v := e` is dead if `v` is not live after the assignment

The correctness proof requires a "heap frame" property: writing to a location
that is never subsequently read does not affect the result. This property
requires location tracking through the SPComp monad, which we axiomatize.
-/

namespace CatCrypt.Crypto.Jasmin

set_option autoImplicit false

/-! ## Variable Collection -/

/-- Collect variables referenced by an expression. -/
def exprVars : PExpr → List Var
  | .Pvar gv => [gv.gv.var]
  | .Pget _ _ x idx => x.gv.var :: exprVars idx
  | .Psub _ _ _ x idx => x.gv.var :: exprVars idx
  | .Pload _ x off => x.var :: exprVars off
  | .Papp1 _ e => exprVars e
  | .Papp2 _ e₁ e₂ => exprVars e₁ ++ exprVars e₂
  | .PappN _ es => (es.map exprVars).flatten
  | .Pif _ c et ef => exprVars c ++ exprVars et ++ exprVars ef
  | _ => []  -- Pconst, Pbool, Parr_init

/-- Variables written by an l-value. -/
def lvalWrites : LVal → List Var
  | .Lvar x => [x.var]
  | .Laset _ _ x _ => [x.var]
  | .Lasub _ _ _ x _ => [x.var]
  | _ => []  -- Lnone, Lmem

/-- Variables read by an l-value (from index expressions). -/
def lvalReads : LVal → List Var
  | .Lmem _ x off => x.var :: exprVars off
  | .Laset _ _ _ idx => exprVars idx
  | .Lasub _ _ _ _ idx => exprVars idx
  | _ => []

/-! ## Instruction-Level Analysis -/

/-- Variables written by an instruction (simplified: only Cassgn to Lvar). -/
def instrWrites : InstrR → List Var
  | .Cassgn lv _ _ _ => lvalWrites lv
  | .Copn lvs _ _ _ => (lvs.map lvalWrites).flatten
  | _ => []

/-- Variables read by an instruction. -/
def instrReads : InstrR → List Var
  | .Cassgn lv _ _ e => lvalReads lv ++ exprVars e
  | .Copn lvs _ _ es => (lvs.map lvalReads).flatten ++ (es.map exprVars).flatten
  | .Cif c th el => exprVars c ++ cmdReads th ++ cmdReads el
  | .Cfor _ _ body => cmdReads body
  | .Cwhile cb cond ca => cmdReads cb ++ exprVars cond ++ cmdReads ca
  | .Ccall _ lvs _ args => (lvs.map lvalReads).flatten ++ (args.map exprVars).flatten
where
  cmdReads : Cmd → List Var
    | [] => []
    | i :: is => instrReads i ++ cmdReads is

/-! ## Liveness Analysis

Variable equality for liveness is **name-only**. A slot is identified by its
`vname`; the `vtype` field can differ between SSA writes and reads of the
same logical location (e.g. a top-level `Cassgn` may carry `sword U64` while
a downstream `Ccall` argument reads the same slot at `sarr 8`). Using
structural `Var` equality (which compares both `vname` and `vtype`) would
cause the backward liveness walker to miss those reads, allowing legitimate
initializers to be eliminated. Liveness tracking is concerned with "is this
named slot read", not with the type-bookkeeping artifact attached to each
occurrence. -/

/-- Membership test for the liveness sets: compares variables by `vname` only. -/
def varListContainsName (xs : List Var) (v : Var) : Bool :=
  xs.any fun w => w.vname == v.vname

/-- Compute the set of live variables before a command,
    given the live variables after.
    Walk backwards: for each instruction, add reads and remove writes
    (if the write is to a variable that is not live after).
    Membership tests use `varListContainsName` (name-only) so SSA writes
    and downstream reads of the same slot at different `vtype`s match. -/
def liveBeforeCmd : Cmd → List Var → List Var
  | [], live => live
  | i :: is, liveOut =>
    let liveAfterRest := liveBeforeCmd is liveOut
    let reads := instrReads i
    let writes := instrWrites i
    reads ++ (liveAfterRest.filter fun v => !varListContainsName writes v)

/-! ## Dead Code Elimination -/

/-- Check if an instruction is dead (writes only to non-live variables
    and has no side effects). Only eliminates `Cassgn` to `Lvar`.
    Liveness lookup is by `vname` only (see `varListContainsName`). -/
def isDeadInstr (liveAfter : List Var) : InstrR → Bool
  | .Cassgn (.Lvar x) _ _ _ => !varListContainsName liveAfter x.var
  | _ => false

/-- Remove dead assignments from a command, given the live-out variables.

    The walk is backward: for each instruction `i`, compute the live-set
    immediately after `i` from the tail's liveness, decide whether `i` is
    a dead leaf assignment, and (if not) recurse into any nested cmds it
    carries (`Cwhile` / `Cif` / `Cfor`).

    Liveness flowing into a nested body:
    * `Cif cond th el`: the live-out of each branch is the live-out of the
      whole `Cif` (`liveAfterI`).
    * `Cwhile cb cond ca` and `Cfor _ _ body`: a loop body iterates, so any
      variable read anywhere inside the loop is live at body-entry on every
      iteration. We over-approximate as `liveAfterI ++ instrReads i`, which
      already folds in `cmdReads` of both `cb` and `ca` (for `Cwhile`) or
      `body` (for `Cfor`). This is conservative — it never deletes a write
      that a subsequent iteration might still read.

    `Ccall` carries no Cmd body in this AST, so it passes through unchanged. -/
def deadCodeElim (liveOut : List Var) : Cmd → Cmd
  | [] => []
  | i :: is =>
    let restElim := deadCodeElim liveOut is
    let liveAfterI := liveBeforeCmd is liveOut
    if isDeadInstr liveAfterI i then restElim
    else
      let i' :=
        match i with
        | .Cif cond th el =>
          .Cif cond (deadCodeElim liveAfterI th) (deadCodeElim liveAfterI el)
        | .Cfor v range body =>
          .Cfor v range (deadCodeElim (liveAfterI ++ instrReads i) body)
        | .Cwhile cb cond ca =>
          let liveLoop := liveAfterI ++ instrReads i
          .Cwhile (deadCodeElim liveLoop cb) cond (deadCodeElim liveLoop ca)
        | other => other
      i' :: restElim

/-! ## Correctness

Dead code elimination does **not** satisfy `CmdPassCorrect` because that predicate
requires full `SPComp` equality including output heap state:
```
CmdPassCorrect pass ↔
  ∀ env sid fuel cmd, (translateCmd env (pass cmd) ...).code.eval =
                      (translateCmd env cmd ...).code.eval
```
where `SPComp α = Heap → SDistr (α × Heap)`. Since DCE removes writes to dead
variables, the output heaps differ at those locations. This makes `CmdPassCorrect`
**false** for DCE.

The correct property is *contextual equivalence* restricted to live locations:
any continuation that only reads live-out variables observes the same behavior.
Formalizing this requires:

1. **Location independence**: Showing that a computation is independent of a set
   of heap locations (neither reads nor writes affect observable behavior)
2. **Frame property**: Writing to an independent location then running independent
   code yields the same observable output distribution
3. **Translation tracking**: `translateCmd` only accesses locations corresponding
   to variables in the command's read/write sets

These properties are standard in separation logic and verified compilers (e.g.,
Jasmin/EasyCrypt uses a frame rule on module memories). The definitions above
(`exprVars`, `instrReads`, `instrWrites`, `liveBeforeCmd`, `deadCodeElim`) are
the complete DCE implementation — only the correctness proof is omitted.

No axiom is introduced: the pass is available as an unverified optimization.
The constant folding and nop elimination passes are fully verified. -/

end CatCrypt.Crypto.Jasmin
