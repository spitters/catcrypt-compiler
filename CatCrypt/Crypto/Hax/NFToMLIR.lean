/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.NF

/-!
# The MLIR image of the normal form `NF`

A translation from the monadic A-normal form of `ImpExpr` (the fragment `Hax.isNFK`
accepts) to MLIR operations in generic form over the upstream dialects `func`,
`scf`, `arith`, and the algebraic dialect `field` for the field builtins. The
image is an operation tree `MOp` together with a printer to MLIR text.

Every variable of the source is mapped to its current SSA value by an environment
`SEnv`. A `letBind` or an `assign` binds its name to the value of the right-hand
side. A branch `ifThenElse` is an `scf.if` whose results are the value of the
branch and the variables of the enclosing scope written by either branch. A loop
carries as iteration arguments exactly the variables of the enclosing scope its
body writes (`accs`): a `forFold` without an exit and a `forFoldRev` are an
`scf.for`; a `forFold` with an exit, a `whileLoop` and a `whileFold` are an
`scf.while`, where an exit is an `i1` flag carried beside the accumulators.

The translation is partial. It accepts the constructors `letBind`, `assign`,
atoms, `unitVal`, `tuple`, `typeAscription`, `seq`, `ifThenElse`, the pair
`match_`, `forFold`, `forFoldRev`, `whileLoop`, `whileFold`, and `cfBreak` and
`cfContinue` in tail position of a loop body. It rejects `proj`,
`forFoldReturn`, `forFoldRevReturn`, `whileFoldReturn`, `cfBreakContinue` and an
exit in the first component of a `seq`. The value of a loop is the unit value,
so the payload of a `cfBreak` is not carried.

## Main definitions

* `MVal`, `MOp` — SSA values and generic-form operations
* `wsOps` — every operand of every operation is defined before its use, by an
  earlier operation of the same block, a block argument or an enclosing scope
* `translate` — the image of an expression in a mode (`Mode.val`, `Mode.stmt`,
  `Mode.exit`)
* `nfToFunc`, `printModule` — the image of a function body as a `func.func` and
  its MLIR text

## Main results

* `translate_ws` — the image of an expression under an environment whose values
  are in scope is well scoped, and its output environment and results are in scope
* `nfToFunc_ws` — the image of a function is well scoped
* `translate_forFold_carries`, `translate_whileLoop_carries` — the loop operation
  of a `forFold` or `whileLoop` carries exactly the values of the accumulators
  `accs σ b` after its control values, and the output environment maps each
  accumulator to a result of the loop
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToMLIR

open _root_.Hax (ImpExpr ImpLit ImpPat IntWidth)

/-! ## Generic-form operations -/

/-- An SSA value: its name, printed after `%`, and its MLIR type. -/
structure MVal where
  /-- The name, printed after `%`. -/
  name : String
  /-- The MLIR type. -/
  ty : String
  deriving DecidableEq, Repr

/-- A generic-form MLIR operation: results, operation name, operands, properties,
    and regions, each region a single block given by its arguments and its
    operations. -/
inductive MOp where
  | mk (res : List MVal) (name : String) (args : List MVal)
      (props : List (String × String)) (regions : List (List MVal × List MOp))

/-- The results of an operation. -/
def MOp.res : MOp → List MVal
  | .mk r .. => r

/-- The operands of an operation. -/
def MOp.args : MOp → List MVal
  | .mk _ _ a .. => a

mutual
/-- `wsOps sc ops`: in the block `ops` under the scope `sc`, every operand is in
    scope, every region is well scoped under its block arguments and the scope of
    its operation, and the results of an operation are in scope for the operations
    after it. -/
def wsOps : List MVal → List MOp → Bool
  | _, [] => true
  | sc, .mk res _ args _ regs :: rest =>
      args.all (fun a => sc.contains a) && wsRegions sc regs && wsOps (res ++ sc) rest

/-- `wsRegions sc regs`: every region of `regs` is well scoped under its block
    arguments and `sc`. -/
def wsRegions : List MVal → List (List MVal × List MOp) → Bool
  | _, [] => true
  | sc, (bargs, ops) :: rs => wsOps (bargs ++ sc) ops && wsRegions sc rs
end

/-- The scope after a block: the results of its operations, the latest first, and
    the scope before it. -/
def scopeAfter : List MVal → List MOp → List MVal
  | sc, [] => sc
  | sc, op :: rest => scopeAfter (op.res ++ sc) rest

/-! ## Operation builders -/

/-- The fresh SSA value number `n` of type `ty`. -/
def fresh (n : Nat) (ty : String) : MVal := ⟨"t" ++ toString n, ty⟩

/-- Fresh SSA values numbered from `n`, one per type. -/
def freshList : Nat → List String → List MVal
  | _, [] => []
  | n, t :: ts => fresh n t :: freshList (n + 1) ts

/-- The types of a list of values. -/
def tysOf (ms : List MVal) : List String := ms.map (·.ty)

/-- `arith.constant` with the value attribute `v`. -/
def constOp (m : MVal) (v : String) : MOp := .mk [m] "arith.constant" [] [("value", v)] []

/-- A binary operation without properties. -/
def binOp (r : MVal) (op : String) (a b : MVal) : MOp := .mk [r] op [a, b] [] []

/-- `arith.cmpi` with predicate `p`. -/
def cmpOp (r : MVal) (p : Nat) (a b : MVal) : MOp :=
  .mk [r] "arith.cmpi" [a, b] [("predicate", toString p ++ " : i64")] []

/-- `func.call` of the symbol `f`. -/
def callOp (res : List MVal) (f : String) (args : List MVal) : MOp :=
  .mk res "func.call" args [("callee", "@\"" ++ f ++ "\"")] []

/-- `scf.yield`. -/
def yieldOp (ys : List MVal) : MOp := .mk [] "scf.yield" ys [] []

/-- `scf.condition`. -/
def condOp (c : MVal) (as : List MVal) : MOp := .mk [] "scf.condition" (c :: as) [] []

/-- `scf.if` with the two branches and their yielded values. -/
def ifOp (res : List MVal) (c : MVal) (thenOps : List MOp) (thenYs : List MVal)
    (elseOps : List MOp) (elseYs : List MVal) : MOp :=
  .mk res "scf.if" [c] [] [([], thenOps ++ [yieldOp thenYs]), ([], elseOps ++ [yieldOp elseYs])]

/-- `scf.for` from `lb` to `ub` by `step` with initial iteration values `inits`; the
    body block has the induction variable `iv` and the iteration arguments `bargs`,
    and yields `ys`. -/
def forOp (res : List MVal) (lb ub step : MVal) (inits : List MVal) (iv : MVal)
    (bargs : List MVal) (body : List MOp) (ys : List MVal) : MOp :=
  .mk res "scf.for" (lb :: ub :: step :: inits) [] [(iv :: bargs, body ++ [yieldOp ys])]

/-- `scf.while` with initial values `inits`; the before block has arguments `bargsB`,
    runs `beforeOps` and passes its arguments on under the condition `c`; the after
    block has arguments `bargsA`, runs `afterOps` and yields `ys`. -/
def whileOp (res inits bargsB : List MVal) (beforeOps : List MOp) (c : MVal)
    (bargsA : List MVal) (afterOps : List MOp) (ys : List MVal) : MOp :=
  .mk res "scf.while" inits []
    [(bargsB, beforeOps ++ [condOp c bargsB]), (bargsA, afterOps ++ [yieldOp ys])]

/-! ## Configuration -/

/-- The result type of an operation of the builtin table: the type of the first
    operand, or `i1`. -/
inductive ResTy where
  | arg0
  | bool

/-- An entry of the builtin table: the MLIR operation, its properties and its
    result type. -/
structure OpSpec where
  /-- The MLIR operation name. -/
  op : String
  /-- The properties. -/
  props : List (String × String) := []
  /-- The result type. -/
  resTy : ResTy := .arg0

/-- The `arith.cmpi` entry with predicate `p`. -/
def cmpSpec (p : Nat) : OpSpec := ⟨"arith.cmpi", [("predicate", toString p ++ " : i64")], .bool⟩

/-- The builtin table over signed `arith` operations and the `field` dialect. -/
def defaultOps : String → Option OpSpec
  | "add" | "Add" => some ⟨"arith.addi", [], .arg0⟩
  | "sub" | "Sub" => some ⟨"arith.subi", [], .arg0⟩
  | "mul" | "Mul" => some ⟨"arith.muli", [], .arg0⟩
  | "div" => some ⟨"arith.divsi", [], .arg0⟩
  | "rem" | "Rem" => some ⟨"arith.remsi", [], .arg0⟩
  | "bitand" | "and" => some ⟨"arith.andi", [], .arg0⟩
  | "bitor" | "or" => some ⟨"arith.ori", [], .arg0⟩
  | "bitxor" => some ⟨"arith.xori", [], .arg0⟩
  | "shl" => some ⟨"arith.shli", [], .arg0⟩
  | "shr" => some ⟨"arith.shrsi", [], .arg0⟩
  | "min" => some ⟨"arith.minsi", [], .arg0⟩
  | "max" => some ⟨"arith.maxsi", [], .arg0⟩
  | "eq" => some (cmpSpec 0)
  | "ne" => some (cmpSpec 1)
  | "lt" => some (cmpSpec 2)
  | "le" => some (cmpSpec 3)
  | "gt" => some (cmpSpec 4)
  | "ge" => some (cmpSpec 5)
  | "fp_add" => some ⟨"field.add", [], .arg0⟩
  | "fp_sub" => some ⟨"field.sub", [], .arg0⟩
  | "fp_mul" => some ⟨"field.mul", [], .arg0⟩
  | "fp_neg" => some ⟨"field.negate", [], .arg0⟩
  | "fp_square" => some ⟨"field.square", [], .arg0⟩
  | "fp_inv" => some ⟨"field.inverse", [], .arg0⟩
  | _ => none

/-- The configuration of the translation: the type of an integer literal without a
    width, and the builtin table. A builtin outside the table is a `func.call` with
    results of the integer type. -/
structure Cfg where
  /-- The type of an integer literal without a width, and of a call result. -/
  intTy : String := "i64"
  /-- The builtin table. -/
  ops : String → Option OpSpec := defaultOps

/-! ## Environments -/

/-- An environment: each variable with its current SSA value, the latest binding
    first. -/
abbrev SEnv := List (String × MVal)

/-- The current value of a variable. -/
def lookup (σ : SEnv) (x : String) : Option MVal :=
  match σ.find? (fun p => p.1 == x) with
  | some p => some p.2
  | none => none

/-- The current values of a list of variables. -/
def lookupAll (σ : SEnv) : List String → Option (List MVal)
  | [] => some []
  | x :: xs =>
    match lookup σ x, lookupAll σ xs with
    | some m, some ms => some (m :: ms)
    | _, _ => none

/-- The variables an expression binds or assigns, including the loop variables of
    its loops. -/
def writes : ImpExpr → List String
  | .letBind x _ b => x :: writes b
  | .assign x _ => [x]
  | .seq a b => writes a ++ writes b
  | .ifThenElse _ t e => writes t ++ writes e
  | .match_ _ [(.tuplePat [.varPat x, .varPat y], b)] => x :: y :: writes b
  | .forFold v _ _ b => v :: writes b
  | .forFoldRev v _ _ b => v :: writes b
  | .forFoldReturn v _ _ b => v :: writes b
  | .forFoldRevReturn v _ _ b => v :: writes b
  | .whileLoop _ b => writes b
  | .whileFold _ b => writes b
  | .whileFoldReturn _ b => writes b
  | .typeAscription e _ => writes e
  | _ => []

/-- The accumulators of `e` under `σ`: the variables bound in `σ` that `e` binds or
    assigns, without repetition. -/
def accs (σ : SEnv) (e : ImpExpr) : List String :=
  (writes e).eraseDups.filter (fun x => (lookup σ x).isSome)

/-- `e` contains a `cfBreak` that exits the innermost enclosing loop. -/
def hasBreak : ImpExpr → Bool
  | .cfBreak _ => true
  | .letBind _ _ b => hasBreak b
  | .seq a b => hasBreak a || hasBreak b
  | .ifThenElse _ t e => hasBreak t || hasBreak e
  | .match_ _ [(_, b)] => hasBreak b
  | .typeAscription e _ => hasBreak e
  | _ => false

/-! ## Atoms and right-hand sides -/

/-- The constant of a literal and its value; `none` for the unit literal. -/
def litConst (cfg : Cfg) (n : Nat) : ImpLit → Option (MVal × MOp)
  | .bool b => some (fresh n "i1", constOp (fresh n "i1") (if b then "true" else "false"))
  | .int k => some (fresh n cfg.intTy, constOp (fresh n cfg.intTy) (toString k ++ " : " ++ cfg.intTy))
  | .uintLit w k =>
    some (fresh n ("i" ++ toString w.bits),
      constOp (fresh n ("i" ++ toString w.bits)) (toString k ++ " : i" ++ toString w.bits))
  | .sintLit w k =>
    some (fresh n ("i" ++ toString w.bits),
      constOp (fresh n ("i" ++ toString w.bits)) (toString k ++ " : i" ++ toString w.bits))
  | .unit => none

/-- The value of an atom: the current value of a variable, or a fresh constant. -/
def emitAtom (cfg : Cfg) (σ : SEnv) (n : Nat) : ImpExpr → Option (Nat × List MOp × MVal)
  | .var x =>
    match lookup σ x with
    | some m => some (n, [], m)
    | none => none
  | .lit l =>
    match litConst cfg n l with
    | some (m, op) => some (n + 1, [op], m)
    | none => none
  | _ => none

/-- The values of a list of atoms. -/
def emitAtoms (cfg : Cfg) (σ : SEnv) : Nat → List ImpExpr → Option (Nat × List MOp × List MVal)
  | n, [] => some (n, [], [])
  | n, a :: as =>
    match emitAtom cfg σ n a with
    | none => none
    | some (n1, o1, m) =>
      match emitAtoms cfg σ n1 as with
      | none => none
      | some (n2, o2, ms) => some (n2, o1 ++ o2, m :: ms)

/-- The result type of a table entry on the given operands. -/
def specResTy (sp : OpSpec) (ms : List MVal) : Option String :=
  match sp.resTy with
  | .bool => some "i1"
  | .arg0 => ms.head?.map (·.ty)

/-- The value of a right-hand side: a builtin call on atoms, or an atom. -/
def emitRhs (cfg : Cfg) (σ : SEnv) (n : Nat) : ImpExpr → Option (Nat × List MOp × MVal)
  | .app f args =>
    match emitAtoms cfg σ n args with
    | none => none
    | some (n1, o1, ms) =>
      match cfg.ops f with
      | some sp =>
        match specResTy sp ms with
        | some ty => some (n1 + 1, o1 ++ [.mk [fresh n1 ty] sp.op ms sp.props []], fresh n1 ty)
        | none => none
      | none => some (n1 + 1, o1 ++ [callOp [fresh n1 cfg.intTy] f ms], fresh n1 cfg.intTy)
  | e => emitAtom cfg σ n e

/-- The `arith` operation of a counted-loop bound operator. -/
def boundOp : String → Option String
  | "Add" | "add" => some "arith.addi"
  | "Sub" | "sub" => some "arith.subi"
  | "Mul" | "mul" => some "arith.muli"
  | "min" => some "arith.minsi"
  | _ => none

/-- The value of a counted-loop bound. -/
def emitBound (cfg : Cfg) (σ : SEnv) (n : Nat) : ImpExpr → Option (Nat × List MOp × MVal)
  | .app f [a, b] =>
    match boundOp f, emitBound cfg σ n a with
    | some op, some (n1, o1, ma) =>
      match emitBound cfg σ n1 b with
      | some (n2, o2, mb) =>
        some (n2 + 1, o1 ++ o2 ++ [binOp (fresh n2 ma.ty) op ma mb], fresh n2 ma.ty)
      | none => none
    | _, _ => none
  | e => emitAtom cfg σ n e

/-! ## The translation -/

/-- The mode of a position: `val` returns the value of the expression and rejects
    an exit; `stmt` is the body of a loop without an exit, returns no value and
    accepts `cfContinue` in tail position; `exit` is the body of a loop with an
    exit and returns the exit flag, `true` after a `cfBreak`. -/
inductive Mode where
  | val
  | stmt
  | exit
  deriving DecidableEq

/-- The result of a tail position that neither exits nor continues. -/
def leaf : Mode → SEnv → Nat → List MOp → List MVal → Nat × List MOp × SEnv × List MVal
  | .val, σ, n, ops, vals => (n, ops, σ, vals)
  | .stmt, σ, n, ops, _ => (n, ops, σ, [])
  | .exit, σ, n, ops, _ => (n + 1, ops ++ [constOp (fresh n "i1") "false"], σ, [fresh n "i1"])

/-- The image of `e` in mode `md` under `σ` with fresh values numbered from `n`: the
    next fresh number, the operations, the output environment and the results
    (the value in mode `val`, the exit flag in mode `exit`). -/
def translate (cfg : Cfg) (md : Mode) (σ : SEnv) (n : Nat) :
    ImpExpr → Option (Nat × List MOp × SEnv × List MVal)
  | .letBind x v b =>
    match emitRhs cfg σ n v with
    | none => none
    | some (n1, o1, m) =>
      match translate cfg md ((x, m) :: σ) n1 b with
      | none => none
      | some (n2, o2, σ2, out) => some (n2, o1 ++ o2, σ2, out)
  | .assign x r =>
    match emitRhs cfg σ n r with
    | none => none
    | some (n1, o1, m) => some (leaf md ((x, m) :: σ) n1 o1 [])
  | .var x =>
    match lookup σ x with
    | some m => some (leaf md σ n [] [m])
    | none => none
  | .lit l =>
    match litConst cfg n l with
    | some (m, op) => some (leaf md σ (n + 1) [op] [m])
    | none => some (leaf md σ n [] [])
  | .unitVal => some (leaf md σ n [] [])
  | .tuple es =>
    match emitAtoms cfg σ n es with
    | some (n1, o1, ms) => some (leaf md σ n1 o1 ms)
    | none => none
  | .typeAscription e _ => translate cfg md σ n e
  | .cfBreak _ =>
    if md = .exit then some (n + 1, [constOp (fresh n "i1") "true"], σ, [fresh n "i1"]) else none
  | .cfContinue _ =>
    if md = .val then none else some (leaf md σ n [] [])
  | .seq a b =>
    match translate cfg .val σ n a with
    | none => none
    | some (n1, o1, σ1, _) =>
      match translate cfg md σ1 n1 b with
      | none => none
      | some (n2, o2, σ2, out) => some (n2, o1 ++ o2, σ2, out)
  | .ifThenElse (.var c) t e =>
    match lookup σ c, translate cfg md σ n t with
    | some mc, some (n1, ot, σt, outT) =>
      match translate cfg md σ n1 e with
      | some (n2, oe, σe, outE) =>
        match lookupAll σ (accs σ (.seq t e)), lookupAll σt (accs σ (.seq t e)),
            lookupAll σe (accs σ (.seq t e)) with
        | some js, some yt, some ye =>
          if tysOf outT == tysOf outE && tysOf yt == tysOf js && tysOf ye == tysOf js then
            some (n2 + (tysOf outT ++ tysOf js).length,
              [ifOp (freshList n2 (tysOf outT ++ tysOf js)) mc ot (outT ++ yt) oe (outE ++ ye)],
              (accs σ (.seq t e)).zip ((freshList n2 (tysOf outT ++ tysOf js)).drop outT.length)
                ++ σ,
              (freshList n2 (tysOf outT ++ tysOf js)).take outT.length)
          else none
        | _, _, _ => none
      | none => none
    | _, _ => none
  | .match_ (.app f args) [(.tuplePat [.varPat x, .varPat y], b)] =>
    match emitAtoms cfg σ n args with
    | none => none
    | some (n1, o1, ms) =>
      match translate cfg md ((x, fresh n1 cfg.intTy) :: (y, fresh (n1 + 1) cfg.intTy) :: σ)
          (n1 + 2) b with
      | none => none
      | some (n2, o2, σ2, out) =>
        some (n2, o1 ++ [callOp [fresh n1 cfg.intTy, fresh (n1 + 1) cfg.intTy] f ms] ++ o2, σ2, out)
  | .forFold v lo hi b =>
    match emitAtom cfg σ n lo with
    | none => none
    | some (n1, o1, mlo) =>
    match emitBound cfg σ n1 hi with
    | none => none
    | some (n2, o2, mhi) =>
    match lookupAll σ (accs σ b) with
    | none => none
    | some inits =>
    if hasBreak b then
      match translate cfg .exit
          ((v, fresh (n2 + 2 + inits.length + 4) mlo.ty) ::
            (accs σ b).zip (freshList (n2 + 2 + inits.length + 6) (tysOf inits)) ++ σ)
          (n2 + 2 + inits.length + 6 + inits.length) b with
      | some (n5, ob, σb, [brk]) =>
        match lookupAll σb (accs σ b) with
        | some ys =>
          if tysOf ys == tysOf inits then
            some (leaf md
              ((accs σ b).zip ((freshList (n5 + 3) (mlo.ty :: "i1" :: tysOf inits)).drop 2) ++
                σ.filter (fun p => p.1 != v))
              (n5 + 3 + (mlo.ty :: "i1" :: tysOf inits).length)
              (o1 ++ o2 ++ [constOp (fresh (n5 + 2) "i1") "false",
                whileOp (freshList (n5 + 3) (mlo.ty :: "i1" :: tysOf inits))
                  (mlo :: fresh (n5 + 2) "i1" :: inits)
                  (fresh n2 mlo.ty :: fresh (n2 + 1) "i1" :: freshList (n2 + 2) (tysOf inits))
                  [cmpOp (fresh (n2 + 2 + inits.length) "i1") 2 (fresh n2 mlo.ty) mhi,
                   constOp (fresh (n2 + 2 + inits.length + 1) "i1") "true",
                   binOp (fresh (n2 + 2 + inits.length + 2) "i1") "arith.xori"
                     (fresh (n2 + 1) "i1") (fresh (n2 + 2 + inits.length + 1) "i1"),
                   binOp (fresh (n2 + 2 + inits.length + 3) "i1") "arith.andi"
                     (fresh (n2 + 2 + inits.length) "i1") (fresh (n2 + 2 + inits.length + 2) "i1")]
                  (fresh (n2 + 2 + inits.length + 3) "i1")
                  (fresh (n2 + 2 + inits.length + 4) mlo.ty ::
                    fresh (n2 + 2 + inits.length + 5) "i1" ::
                    freshList (n2 + 2 + inits.length + 6) (tysOf inits))
                  (ob ++ [constOp (fresh n5 mlo.ty) ("1 : " ++ mlo.ty),
                    binOp (fresh (n5 + 1) mlo.ty) "arith.addi"
                      (fresh (n2 + 2 + inits.length + 4) mlo.ty) (fresh n5 mlo.ty)])
                  (fresh (n5 + 1) mlo.ty :: brk :: ys)])
              [])
          else none
        | none => none
      | _ => none
    else
      match translate cfg .stmt
          ((v, fresh n2 mlo.ty) :: (accs σ b).zip (freshList (n2 + 1) (tysOf inits)) ++ σ)
          (n2 + 1 + inits.length) b with
      | some (n4, ob, σb, _) =>
        match lookupAll σb (accs σ b) with
        | some ys =>
          if tysOf ys == tysOf inits then
            some (leaf md
              ((accs σ b).zip (freshList (n4 + 1) (tysOf inits)) ++ σ.filter (fun p => p.1 != v))
              (n4 + 1 + inits.length)
              (o1 ++ o2 ++ [constOp (fresh n4 mlo.ty) ("1 : " ++ mlo.ty),
                forOp (freshList (n4 + 1) (tysOf inits)) mlo mhi (fresh n4 mlo.ty) inits
                  (fresh n2 mlo.ty) (freshList (n2 + 1) (tysOf inits)) ob ys])
              [])
          else none
        | none => none
      | none => none
  | .forFoldRev v lo hi b =>
    match emitAtom cfg σ n lo with
    | none => none
    | some (n1, o1, mlo) =>
    match emitAtom cfg σ n1 hi with
    | none => none
    | some (n2, o2, mhi) =>
    match lookupAll σ (accs σ b) with
    | none => none
    | some inits =>
      match translate cfg .stmt
          ((v, fresh (n2 + 4 + inits.length) mlo.ty) ::
            (accs σ b).zip (freshList (n2 + 4) (tysOf inits)) ++ σ)
          (n2 + 5 + inits.length) b with
      | some (n4, ob, σb, _) =>
        match lookupAll σb (accs σ b) with
        | some ys =>
          if tysOf ys == tysOf inits then
            some (leaf md
              ((accs σ b).zip (freshList n4 (tysOf inits)) ++ σ.filter (fun p => p.1 != v))
              (n4 + inits.length)
              (o1 ++ o2 ++
                [constOp (fresh n2 mlo.ty) ("1 : " ++ mlo.ty),
                 binOp (fresh (n2 + 1) mlo.ty) "arith.addi" mlo mhi,
                 binOp (fresh (n2 + 2) mlo.ty) "arith.subi" (fresh (n2 + 1) mlo.ty)
                   (fresh n2 mlo.ty),
                 forOp (freshList n4 (tysOf inits)) mlo mhi (fresh n2 mlo.ty) inits
                  (fresh (n2 + 3) mlo.ty) (freshList (n2 + 4) (tysOf inits))
                  (binOp (fresh (n2 + 4 + inits.length) mlo.ty) "arith.subi"
                    (fresh (n2 + 2) mlo.ty) (fresh (n2 + 3) mlo.ty) :: ob) ys])
              [])
          else none
        | none => none
      | none => none
  | .whileLoop (.var c) b =>
    match lookupAll σ (accs σ b) with
    | none => none
    | some inits =>
    match lookup ((accs σ b).zip (freshList n (tysOf inits)) ++ σ) c with
    | none => none
    | some mc =>
      match translate cfg .stmt ((accs σ b).zip (freshList (n + inits.length) (tysOf inits)) ++ σ)
          (n + inits.length + inits.length) b with
      | some (n3, ob, σb, _) =>
        match lookupAll σb (accs σ b) with
        | some ys =>
          if tysOf ys == tysOf inits && mc.ty == "i1" then
            some (leaf md ((accs σ b).zip (freshList n3 (tysOf inits)) ++ σ)
              (n3 + inits.length)
              [whileOp (freshList n3 (tysOf inits)) inits (freshList n (tysOf inits)) [] mc
                (freshList (n + inits.length) (tysOf inits)) ob ys]
              [])
          else none
        | none => none
      | none => none
  | .whileFold (.var c) b =>
    match lookupAll σ (accs σ b) with
    | none => none
    | some inits =>
    match lookup ((accs σ b).zip (freshList (n + 1) (tysOf inits)) ++ σ) c with
    | none => none
    | some mc =>
      match translate cfg (if hasBreak b then .exit else .stmt)
          ((accs σ b).zip (freshList (n + inits.length + 5) (tysOf inits)) ++ σ)
          (n + inits.length + 5 + inits.length) b with
      | some (n3, ob, σb, out) =>
        match lookupAll σb (accs σ b) with
        | some ys =>
          if tysOf ys == tysOf inits && mc.ty == "i1" && (!hasBreak b || out.length == 1) then
            some (leaf md ((accs σ b).zip (freshList (n3 + 2) (tysOf inits)) ++ σ)
              (n3 + 2 + inits.length)
              [constOp (fresh (n3 + 1) "i1") "false",
               whileOp (fresh n3 "i1" :: freshList (n3 + 2) (tysOf inits))
                (fresh (n3 + 1) "i1" :: inits)
                (fresh n "i1" :: freshList (n + 1) (tysOf inits))
                [constOp (fresh (n + 1 + inits.length) "i1") "true",
                 binOp (fresh (n + 2 + inits.length) "i1") "arith.xori" (fresh n "i1")
                   (fresh (n + 1 + inits.length) "i1"),
                 binOp (fresh (n + 3 + inits.length) "i1") "arith.andi" mc
                   (fresh (n + 2 + inits.length) "i1")]
                (fresh (n + 3 + inits.length) "i1")
                (fresh (n + inits.length + 4) "i1" ::
                  freshList (n + inits.length + 5) (tysOf inits))
                ob ((if hasBreak b then out else [fresh (n + inits.length + 4) "i1"]) ++ ys)]
              [])
          else none
        | none => none
      | none => none
  | _ => none
termination_by e => sizeOf e
decreasing_by all_goals (simp_wf; try omega)

/-! ## Functions and printing -/

/-- The MLIR function type with the given argument and result values. -/
def fnTy (args res : List MVal) : String :=
  "(" ++ ", ".intercalate (tysOf args) ++ ") -> " ++
    match res with
    | [m] => m.ty
    | _ => "(" ++ ", ".intercalate (tysOf res) ++ ")"

/-- The image of a function body with parameters `params` (name and type) as a
    `func.func` named `fname`, returning the value of the body. -/
def nfToFunc (cfg : Cfg) (fname : String) (params : List (String × String)) (e : ImpExpr) :
    Option MOp :=
  match translate cfg .val (params.map fun p => (p.1, ⟨"a_" ++ p.1, p.2⟩)) 0 e with
  | none => none
  | some (_, ops, _, out) =>
    some (.mk [] "func.func" []
      [("function_type", fnTy (params.map fun p => ⟨"a_" ++ p.1, p.2⟩) out),
       ("sym_name", "\"" ++ fname ++ "\"")]
      [(params.map fun p => ⟨"a_" ++ p.1, p.2⟩, ops ++ [.mk [] "func.return" out [] []])])

/-- A value as an operand: `%name`. -/
def pv (m : MVal) : String := "%" ++ m.name

/-- The properties of an operation in generic form. -/
def propsStr : List (String × String) → String
  | [] => ""
  | ps => " <{" ++ ", ".intercalate (ps.map fun p => p.1 ++ " = " ++ p.2) ++ "}>"

mutual
/-- An operation in generic form at indentation `ind`. -/
def printOp (ind : String) : MOp → String
  | .mk res name args props regs =>
    ind ++ (if res.isEmpty then "" else ", ".intercalate (res.map pv) ++ " = ") ++
      "\"" ++ name ++ "\"(" ++ ", ".intercalate (args.map pv) ++ ")" ++ propsStr props ++
      (if regs.isEmpty then "" else " (" ++ printRegions ind regs ++ ")") ++
      " : " ++ fnTy args res

/-- A block of operations, one per line. -/
def printOps (ind : String) : List MOp → String
  | [] => ""
  | op :: ops => printOp ind op ++ "\n" ++ printOps ind ops

/-- A list of regions, separated by commas. -/
def printRegions (ind : String) : List (List MVal × List MOp) → String
  | [] => ""
  | [(bargs, ops)] => printRegion ind bargs ops
  | (bargs, ops) :: rs => printRegion ind bargs ops ++ ", " ++ printRegions ind rs

/-- A single-block region with block arguments `bargs`. -/
def printRegion (ind : String) (bargs : List MVal) (ops : List MOp) : String :=
  "{\n" ++
    (if bargs.isEmpty then ""
     else ind ++ "^bb0(" ++ ", ".intercalate (bargs.map fun m => pv m ++ ": " ++ m.ty) ++ "):\n") ++
    printOps (ind ++ "  ") ops ++ ind ++ "}"
end

/-- The MLIR text of a module holding the given operations. -/
def printModule (ops : List MOp) : String :=
  printOp "" (.mk [] "builtin.module" [] [] [([], ops)]) ++ "\n"

/-! ## Scoping -/

theorem scopeAfter_append : ∀ (sc : List MVal) (xs ys : List MOp),
    scopeAfter sc (xs ++ ys) = scopeAfter (scopeAfter sc xs) ys
  | _, [], _ => rfl
  | _, _ :: xs, ys => scopeAfter_append _ xs ys

theorem wsOps_append : ∀ (sc : List MVal) (xs ys : List MOp),
    wsOps sc (xs ++ ys) = (wsOps sc xs && wsOps (scopeAfter sc xs) ys)
  | _, [], _ => by simp [wsOps, scopeAfter]
  | sc, .mk res nm args ps regs :: xs, ys => by
    simp [wsOps, scopeAfter, MOp.res, wsOps_append _ xs ys, Bool.and_assoc]

theorem mem_scopeAfter : ∀ {sc : List MVal} (ops : List MOp) {m : MVal},
    m ∈ sc → m ∈ scopeAfter sc ops
  | _, [], _, h => h
  | _, _ :: ops, _, h => mem_scopeAfter ops (List.mem_append_right _ h)

theorem scopeAfter_single (sc : List MVal) (op : MOp) : scopeAfter sc [op] = op.res ++ sc := rfl

theorem wsOps_single (sc : List MVal) (res : List MVal) (nm : String) (args : List MVal)
    (ps : List (String × String)) (regs : List (List MVal × List MOp)) :
    wsOps sc [.mk res nm args ps regs] = true ↔
      (∀ a ∈ args, a ∈ sc) ∧ wsRegions sc regs = true := by
  simp [wsOps]

theorem wsRegions_cons (sc bargs : List MVal) (ops : List MOp) (rs : List (List MVal × List MOp)) :
    wsRegions sc ((bargs, ops) :: rs) = (wsOps (bargs ++ sc) ops && wsRegions sc rs) := by
  simp [wsRegions]

theorem wsRegions_nil (sc : List MVal) : wsRegions sc [] = true := by simp [wsRegions]

theorem wsOps_nil (sc : List MVal) : wsOps sc [] = true := by simp [wsOps]

/-- The values of an environment are in the scope `sc`. -/
def EnvIn (σ : SEnv) (sc : List MVal) : Prop := ∀ p ∈ σ, p.2 ∈ sc

theorem EnvIn.mono {σ : SEnv} {sc sc' : List MVal} (h : EnvIn σ sc) (hs : ∀ m ∈ sc, m ∈ sc') :
    EnvIn σ sc' := fun p hp => hs _ (h p hp)

theorem EnvIn.scopeAfter {σ : SEnv} {sc : List MVal} (h : EnvIn σ sc) (ops : List MOp) :
    EnvIn σ (scopeAfter sc ops) := h.mono fun _ hm => mem_scopeAfter ops hm

theorem EnvIn.cons {σ : SEnv} {sc : List MVal} {x : String} {m : MVal} (h : EnvIn σ sc)
    (hm : m ∈ sc) : EnvIn ((x, m) :: σ) sc := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hm
  · exact h p hp

theorem EnvIn.zip_append {σ : SEnv} {sc : List MVal} (xs : List String) (ms : List MVal)
    (hms : ∀ m ∈ ms, m ∈ sc) (h : EnvIn σ sc) : EnvIn (xs.zip ms ++ σ) sc := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hms _ (List.of_mem_zip hp).2
  · exact h p hp

theorem EnvIn.filter {σ : SEnv} {sc : List MVal} (h : EnvIn σ sc) (f : String × MVal → Bool) :
    EnvIn (σ.filter f) sc := fun p hp => h p (List.mem_filter.1 hp).1

theorem lookup_in {σ : SEnv} {sc : List MVal} {x : String} {m : MVal} (hσ : EnvIn σ sc)
    (h : lookup σ x = some m) : m ∈ sc := by
  unfold lookup at h
  split at h
  · rename_i p hp
    cases h
    exact hσ p (List.mem_of_find?_eq_some hp)
  · cases h

theorem lookupAll_in {σ : SEnv} {sc : List MVal} (hσ : EnvIn σ sc) :
    ∀ {xs : List String} {ms : List MVal}, lookupAll σ xs = some ms → ∀ m ∈ ms, m ∈ sc
  | [], ms, h => by simp [lookupAll] at h; subst h; simp
  | x :: xs, ms, h => by
    unfold lookupAll at h
    split at h
    · rename_i m ms' h1 h2
      cases h
      intro m' hm'
      rcases List.mem_cons.1 hm' with rfl | hm'
      · exact lookup_in hσ h1
      · exact lookupAll_in hσ h2 m' hm'
    · cases h

theorem litConst_ws {cfg : Cfg} {n : Nat} {l : ImpLit} {m : MVal} {op : MOp}
    (h : litConst cfg n l = some (m, op)) (sc : List MVal) :
    wsOps sc [op] = true ∧ m ∈ scopeAfter sc [op] := by
  cases l <;> simp [litConst] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    simp [constOp, wsOps, wsRegions, scopeAfter, MOp.res]

theorem emitAtom_ws {cfg : Cfg} {σ : SEnv} {n : Nat} {e : ImpExpr} {n' : Nat} {ops : List MOp}
    {m : MVal} (h : emitAtom cfg σ n e = some (n', ops, m)) {sc : List MVal} (hσ : EnvIn σ sc) :
    wsOps sc ops = true ∧ m ∈ scopeAfter sc ops := by
  unfold emitAtom at h
  split at h
  · split at h
    · cases h; exact ⟨wsOps_nil sc, lookup_in hσ ‹_›⟩
    · cases h
  · split at h
    · cases h; exact litConst_ws ‹_› sc
    · cases h
  · cases h

theorem emitAtoms_ws {cfg : Cfg} {σ : SEnv} {sc : List MVal} (hσ : EnvIn σ sc) :
    ∀ {n : Nat} {es : List ImpExpr} {n' : Nat} {ops : List MOp} {ms : List MVal},
      emitAtoms cfg σ n es = some (n', ops, ms) →
      wsOps sc ops = true ∧ ∀ m ∈ ms, m ∈ scopeAfter sc ops
  | n, [], n', ops, ms, h => by
    simp [emitAtoms] at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp [wsOps]
  | n, a :: as, n', ops, ms, h => by
    unfold emitAtoms at h
    split at h
    · cases h
    · rename_i n1 o1 m h1
      split at h
      · cases h
      · rename_i n2 o2 ms' h2
        cases h
        obtain ⟨w1, m1⟩ := emitAtom_ws h1 hσ
        obtain ⟨w2, m2⟩ := emitAtoms_ws (hσ.scopeAfter o1) h2
        refine ⟨by simp [wsOps_append, w1, w2], ?_⟩
        intro m' hm'
        rw [scopeAfter_append]
        rcases List.mem_cons.1 hm' with rfl | hm'
        · exact mem_scopeAfter _ m1
        · exact m2 m' hm'

theorem emitRhs_ws {cfg : Cfg} {σ : SEnv} {n : Nat} {e : ImpExpr} {n' : Nat} {ops : List MOp}
    {m : MVal} (h : emitRhs cfg σ n e = some (n', ops, m)) {sc : List MVal} (hσ : EnvIn σ sc) :
    wsOps sc ops = true ∧ m ∈ scopeAfter sc ops := by
  unfold emitRhs at h
  split at h
  · split at h
    · cases h
    · rename_i n1 o1 ms h1
      obtain ⟨w1, m1⟩ := emitAtoms_ws hσ h1
      split at h
      · split at h
        · cases h
          refine ⟨by simp [wsOps_append, w1, wsOps, wsRegions]; exact m1, ?_⟩
          simp [scopeAfter_append, scopeAfter, MOp.res]
        · cases h
      · cases h
        refine ⟨by simp [wsOps_append, w1, callOp, wsOps, wsRegions]; exact m1, ?_⟩
        simp [scopeAfter_append, scopeAfter, MOp.res, callOp]
  · exact emitAtom_ws h hσ

theorem emitBound_ws (cfg : Cfg) (σ : SEnv) (n : Nat) (e : ImpExpr) :
    ∀ {n' : Nat} {ops : List MOp} {m : MVal}, emitBound cfg σ n e = some (n', ops, m) →
      ∀ {sc : List MVal}, EnvIn σ sc → wsOps sc ops = true ∧ m ∈ scopeAfter sc ops := by
  fun_induction emitBound cfg σ n e <;> intro n' ops m h sc hσ
  · rename_i op n1 o1 ma h1 hop n2 o2 mb h2 ih1 ih2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨w1, m1⟩ := ih1 h1 hσ
    obtain ⟨w2, m2⟩ := ih2 h2 (hσ.scopeAfter o1)
    have ha : ma ∈ scopeAfter sc (o1 ++ o2) := by
      rw [scopeAfter_append]; exact mem_scopeAfter _ m1
    have hb : mb ∈ scopeAfter sc (o1 ++ o2) := by rw [scopeAfter_append]; exact m2
    refine ⟨?_, ?_⟩
    · rw [wsOps_append, wsOps_append, w1, w2]
      simp [binOp, wsOps, wsRegions, ha, hb]
    · rw [scopeAfter_append]; simp [scopeAfter, binOp, MOp.res]
  · simp at h
  · simp at h
  · exact emitAtom_ws h hσ

/-- The operations of a result are well scoped under `sc`, and its output
    environment and its results are in the scope after them. -/
def Good (sc : List MVal) (r : Nat × List MOp × SEnv × List MVal) : Prop :=
  wsOps sc r.2.1 = true ∧ EnvIn r.2.2.1 (scopeAfter sc r.2.1) ∧
    ∀ m ∈ r.2.2.2, m ∈ scopeAfter sc r.2.1

theorem leaf_good (md : Mode) (σ : SEnv) (n : Nat) (ops : List MOp) (vals : List MVal)
    {sc : List MVal} (hw : wsOps sc ops = true) (hσ : EnvIn σ (scopeAfter sc ops))
    (hv : ∀ m ∈ vals, m ∈ scopeAfter sc ops) : Good sc (leaf md σ n ops vals) := by
  cases md
  · exact ⟨hw, hσ, hv⟩
  · exact ⟨hw, hσ, by simp [leaf]⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [leaf, wsOps_append, hw, constOp, wsOps, wsRegions]
    · simpa [leaf, scopeAfter_append] using hσ.scopeAfter [constOp (fresh n "i1") "false"]
    · simp [leaf, scopeAfter_append, scopeAfter, constOp, MOp.res]

theorem Good.prefix {sc : List MVal} {o1 o2 : List MOp} {n : Nat} {σ : SEnv} {out : List MVal}
    (w1 : wsOps sc o1 = true) (g : Good (scopeAfter sc o1) (n, o2, σ, out)) :
    Good sc (n, o1 ++ o2, σ, out) := by
  obtain ⟨w2, e2, v2⟩ := g
  exact ⟨by simp [wsOps_append, w1, w2], by simpa [scopeAfter_append] using e2,
    by simpa [scopeAfter_append] using v2⟩

theorem wsOps_yield (T : List MVal) (body : List MOp) (ys : List MVal) :
    wsOps T (body ++ [yieldOp ys]) = true ↔
      wsOps T body = true ∧ ∀ y ∈ ys, y ∈ scopeAfter T body := by
  simp [wsOps_append, yieldOp, wsOps, wsRegions]

theorem wsOps_const_cons (S : List MVal) (m : MVal) (v : String) (rest : List MOp) :
    wsOps S (constOp m v :: rest) = wsOps (m :: S) rest := by
  simp [constOp, wsOps, wsRegions]

theorem ifOp_ws {S res : List MVal} {c : MVal} {tOps eOps : List MOp} {tYs eYs : List MVal}
    (hc : c ∈ S) (ht : wsOps S tOps = true) (hty : ∀ m ∈ tYs, m ∈ scopeAfter S tOps)
    (he : wsOps S eOps = true) (hey : ∀ m ∈ eYs, m ∈ scopeAfter S eOps) :
    wsOps S [ifOp res c tOps tYs eOps eYs] = true := by
  simp only [ifOp, wsOps_single, wsRegions_cons, wsRegions_nil, List.nil_append,
    Bool.and_true, Bool.and_eq_true, wsOps_yield]
  exact ⟨by simpa using hc, ⟨ht, hty⟩, he, hey⟩

theorem forOp_ws {S res : List MVal} {lb ub step : MVal} {inits : List MVal} {iv : MVal}
    {bargs : List MVal} {body : List MOp} {ys : List MVal}
    (hl : lb ∈ S) (hu : ub ∈ S) (hs : step ∈ S) (hi : ∀ m ∈ inits, m ∈ S)
    (hb : wsOps (iv :: bargs ++ S) body = true)
    (hy : ∀ m ∈ ys, m ∈ scopeAfter (iv :: bargs ++ S) body) :
    wsOps S [forOp res lb ub step inits iv bargs body ys] = true := by
  simp only [forOp, wsOps_single, wsRegions_cons, wsRegions_nil, Bool.and_true, wsOps_yield]
  refine ⟨?_, ?_, hy⟩
  · intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | ha
    · exact hl
    · exact hu
    · exact hs
    · exact hi a ha
  · simpa using hb

theorem whileOp_ws {S res inits bargsB : List MVal} {beforeOps : List MOp} {c : MVal}
    {bargsA : List MVal} {afterOps : List MOp} {ys : List MVal}
    (hi : ∀ m ∈ inits, m ∈ S) (hb : wsOps (bargsB ++ S) beforeOps = true)
    (hc : c ∈ scopeAfter (bargsB ++ S) beforeOps) (ha : wsOps (bargsA ++ S) afterOps = true)
    (hy : ∀ m ∈ ys, m ∈ scopeAfter (bargsA ++ S) afterOps) :
    wsOps S [whileOp res inits bargsB beforeOps c bargsA afterOps ys] = true := by
  simp only [whileOp, wsOps_single, wsRegions_cons, wsRegions_nil, Bool.and_true,
    Bool.and_eq_true, wsOps_yield]
  refine ⟨hi, ⟨?_, ha, hy⟩⟩
  simp only [condOp, wsOps_append, hb, Bool.true_and, wsOps_single, wsRegions_nil, and_true,
    List.mem_cons, forall_eq_or_imp]
  exact ⟨hc, fun a h => mem_scopeAfter _ (List.mem_append_left _ h)⟩

theorem mem_freshList_append {k : Nat} {tys : List String} {S : List MVal} {m : MVal}
    (h : m ∈ freshList k tys) : m ∈ freshList k tys ++ S := List.mem_append_left _ h

theorem wsOps_bin_cons {S : List MVal} {r a b : MVal} {op : String} {rest : List MOp}
    (ha : a ∈ S) (hb : b ∈ S) (h : wsOps (r :: S) rest = true) :
    wsOps S (binOp r op a b :: rest) = true := by
  simp [binOp, wsOps, wsRegions, h, ha, hb]

/-- The facts about the operations before a counted loop: the operations of the
    lower and the upper bound are well scoped, and the bounds and the scope before them
    are in the scope after them. -/
theorem bounds_ws {sc : List MVal} {o1 o2 : List MOp} {ml mh : MVal}
    (w1 : wsOps sc o1 = true) (m1 : ml ∈ scopeAfter sc o1)
    (w2 : wsOps (scopeAfter sc o1) o2 = true) (m2 : mh ∈ scopeAfter (scopeAfter sc o1) o2) :
    wsOps sc (o1 ++ o2) = true ∧ ml ∈ scopeAfter sc (o1 ++ o2) ∧
      mh ∈ scopeAfter sc (o1 ++ o2) ∧ ∀ m ∈ sc, m ∈ scopeAfter sc (o1 ++ o2) := by
  refine ⟨by rw [wsOps_append, w1, w2]; rfl, ?_, ?_, fun m hm => mem_scopeAfter _ hm⟩
  · rw [scopeAfter_append]; exact mem_scopeAfter _ m1
  · rw [scopeAfter_append]; exact m2

theorem envIn_after_loop {σ : SEnv} {sc : List MVal} {pre post : List MOp} {v : String}
    (xs : List String) (res : List MVal) (h : EnvIn σ sc)
    (hsc : ∀ m ∈ sc, m ∈ scopeAfter sc pre) (hres : ∀ m ∈ res, m ∈ scopeAfter sc (pre ++ post)) :
    EnvIn (xs.zip res ++ σ.filter (fun p => p.1 != v)) (scopeAfter sc (pre ++ post)) := by
  refine EnvIn.zip_append _ _ hres ((h.filter _).mono fun m hm => ?_)
  rw [scopeAfter_append]; exact mem_scopeAfter _ (hsc m hm)

theorem translate_ws (cfg : Cfg) (md : Mode) (σ : SEnv) (n : Nat) (e : ImpExpr) :
    ∀ {r}, translate cfg md σ n e = some r → ∀ {sc : List MVal}, EnvIn σ sc → Good sc r := by
  fun_induction translate cfg md σ n e
  all_goals first
    | (intro r h; simp at h; done)
    | skip
  case case3 md σ n x v b n1 o1 m hv n2 o2 σ2 out hb ih =>
    intro r h sc hσ; cases h
    obtain ⟨w1, m1⟩ := emitRhs_ws hv hσ
    exact Good.prefix w1 (ih hb ((hσ.scopeAfter o1).cons m1))
  case case5 md σ n x r n1 o1 m hr =>
    intro r' h sc hσ; cases h
    obtain ⟨w1, m1⟩ := emitRhs_ws hr hσ
    exact leaf_good _ _ _ _ _ w1 ((hσ.scopeAfter o1).cons m1) (by simp)
  case case6 md σ n x m hl =>
    intro r h sc hσ; cases h
    exact leaf_good _ _ _ _ _ (wsOps_nil sc) hσ (by simpa [scopeAfter] using lookup_in hσ hl)
  case case8 md σ n l m op hl =>
    intro r h sc hσ; cases h
    obtain ⟨w1, m1⟩ := litConst_ws hl sc
    exact leaf_good _ _ _ _ _ w1 (hσ.scopeAfter _) (by simpa using m1)
  case case9 md σ n l hl =>
    intro r h sc hσ; cases h
    exact leaf_good _ _ _ _ _ (wsOps_nil sc) hσ (by simp)
  case case10 md σ n =>
    intro r h sc hσ; cases h
    exact leaf_good _ _ _ _ _ (wsOps_nil sc) hσ (by simp)
  case case11 md σ n es n1 o1 ms h1 =>
    intro r h sc hσ; cases h
    obtain ⟨w1, m1⟩ := emitAtoms_ws hσ h1
    exact leaf_good _ _ _ _ _ w1 (hσ.scopeAfter _) m1
  case case13 md σ n e ty ih => exact ih
  case case14 σ n e =>
    intro r h sc hσ; cases h
    refine ⟨by simp [constOp, wsOps, wsRegions], hσ.scopeAfter _, ?_⟩
    simp [scopeAfter, constOp, MOp.res]
  case case17 md σ n e hmd =>
    intro r h sc hσ; cases h
    exact leaf_good _ _ _ _ _ (wsOps_nil sc) hσ (by simp)
  case case20 md σ n a b n1 o1 σ1 out1 ha n2 o2 σ2 out hb iha ihb =>
    intro r h sc hσ; cases h
    obtain ⟨w1, e1, _⟩ := iha ha hσ
    exact Good.prefix w1 (ihb hb e1)
  case case21 md σ n c t e mc n1 ot σt outT ht hc n2 oe σe outE he js yt ye hye hyt hjs hty
      iht ihe =>
    intro r h sc hσ; cases h
    obtain ⟨wt, et, vt⟩ := iht ht hσ
    obtain ⟨we, ee, ve⟩ := ihe he hσ
    have hres : ∀ m, m ∈ freshList n2 (tysOf outT ++ tysOf js) →
        m ∈ scopeAfter sc [ifOp (freshList n2 (tysOf outT ++ tysOf js)) mc ot (outT ++ yt) oe
          (outE ++ ye)] := by
      intro m hm
      simp [scopeAfter, ifOp, MOp.res, hm]
    refine ⟨?_, ?_, ?_⟩
    · refine ifOp_ws (lookup_in hσ hc) wt ?_ we ?_
      · intro m hm
        rcases List.mem_append.1 hm with hm | hm
        · exact vt m hm
        · exact lookupAll_in et hyt m hm
      · intro m hm
        rcases List.mem_append.1 hm with hm | hm
        · exact ve m hm
        · exact lookupAll_in ee hye m hm
    · exact EnvIn.zip_append _ _ (fun m hm => hres m (List.mem_of_mem_drop hm))
        (hσ.scopeAfter _)
    · exact fun m hm => hres m (List.mem_of_mem_take hm)
  case case28 md σ n f args x y b n1 o1 ms ha n2 o2 σ2 out hb ih =>
    intro r h sc hσ; cases h
    obtain ⟨w1, m1⟩ := emitAtoms_ws hσ ha
    rw [List.append_assoc]
    refine Good.prefix w1 (Good.prefix ?_ (ih hb ?_))
    · simp only [callOp, wsOps_single, wsRegions_nil, and_true]
      exact m1
    · simp only [scopeAfter_single, callOp, MOp.res]
      exact ((((hσ.scopeAfter o1).mono fun _ h => List.mem_append_right _ h).cons
        (by simp)).cons (by simp))
  case case32 md σ n v lo hi b n1' o1' mlo hlo n1 o1 mhi hhi inits hinit hbrk n5 ob σb brk
      hbody ys hys hty ih =>
    intro r h sc hσ; cases h
    obtain ⟨w1, m1⟩ := emitAtom_ws hlo hσ
    obtain ⟨w2, m2⟩ := emitBound_ws cfg σ n1' hi hhi (hσ.scopeAfter o1')
    obtain ⟨w12, m1', m2', hS⟩ := bounds_ws w1 m1 w2 m2
    have hinS := fun m hm => hS m (lookupAll_in hσ hinit m hm)
    obtain ⟨wb, eb, vb⟩ := ih hbody (sc := fresh (n1 + 2 + inits.length + 4) mlo.ty ::
        fresh (n1 + 2 + inits.length + 5) "i1" ::
          freshList (n1 + 2 + inits.length + 6) (tysOf inits) ++
            (fresh (n5 + 2) "i1" :: scopeAfter sc (o1' ++ o1)))
      (EnvIn.cons (EnvIn.zip_append _ _
        (fun m hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
        (hσ.mono fun m hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_of_mem _ (hS m hm))))))
        List.mem_cons_self)
    apply leaf_good
    · rw [wsOps_append, w12, Bool.true_and, wsOps_const_cons]
      refine whileOp_ws ?_ ?_ ?_ ?_ ?_
      · intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with rfl | rfl | hm
        · exact List.mem_cons_of_mem _ m1'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hinS m hm)
      · simp [cmpOp, binOp, constOp, wsOps, wsRegions, m2']
      · simp [scopeAfter, cmpOp, binOp, constOp, MOp.res]
      · rw [wsOps_append, wb, Bool.true_and, wsOps_const_cons]
        exact wsOps_bin_cons (List.mem_cons_of_mem _ (mem_scopeAfter _ List.mem_cons_self))
          List.mem_cons_self (wsOps_nil _)
      · intro m hm
        simp only [List.mem_cons] at hm
        rw [scopeAfter_append]
        rcases hm with rfl | rfl | hm
        · simp [scopeAfter, binOp, constOp, MOp.res]
        · exact mem_scopeAfter _ (vb _ List.mem_cons_self)
        · exact mem_scopeAfter _ (lookupAll_in eb hys m hm)
    · refine envIn_after_loop _ _ hσ hS fun m hm => ?_
      rw [scopeAfter_append]
      simp only [scopeAfter, whileOp, constOp, MOp.res]
      exact List.mem_append_left _ (List.mem_of_mem_drop hm)
    · simp
  case case36 md σ n v lo hi b n1' o1' mlo hlo n1 o1 mhi hhi inits hinit hbrk n2 oe σe outE
      hbody ys hys hty ih =>
    intro r h sc hσ; cases h
    obtain ⟨w1, m1⟩ := emitAtom_ws hlo hσ
    obtain ⟨w2, m2⟩ := emitBound_ws cfg σ n1' hi hhi (hσ.scopeAfter o1')
    obtain ⟨w12, m1', m2', hS⟩ := bounds_ws w1 m1 w2 m2
    have hinS := fun m hm => hS m (lookupAll_in hσ hinit m hm)
    obtain ⟨wb, eb, _⟩ := ih hbody (sc := fresh n1 mlo.ty ::
        freshList (n1 + 1) (tysOf inits) ++ (fresh n2 mlo.ty :: scopeAfter sc (o1' ++ o1)))
      (EnvIn.cons (EnvIn.zip_append _ _
        (fun m hm => List.mem_cons_of_mem _ (List.mem_append_left _ hm))
        (hσ.mono fun m hm => List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_of_mem _ (hS m hm)))))
        List.mem_cons_self)
    apply leaf_good
    · rw [wsOps_append, w12, Bool.true_and, wsOps_const_cons]
      exact forOp_ws (List.mem_cons_of_mem _ m1') (List.mem_cons_of_mem _ m2') List.mem_cons_self
        (fun m hm => List.mem_cons_of_mem _ (hinS m hm)) wb
        (fun m hm => lookupAll_in eb hys m hm)
    · refine envIn_after_loop _ _ hσ hS fun m hm => ?_
      rw [scopeAfter_append]
      simp only [scopeAfter, forOp, constOp, MOp.res]
      exact List.mem_append_left _ hm
    · simp
  case case43 md σ n v lo hi b n1' o1' mlo hlo n1 o1 mhi hhi inits hinit n2 oe σe outE
      hbody ys hys hty ih =>
    intro r h sc hσ; cases h
    obtain ⟨w1, m1⟩ := emitAtom_ws hlo hσ
    obtain ⟨w2, m2⟩ := emitAtom_ws hhi (hσ.scopeAfter o1')
    obtain ⟨w12, m1', m2', hS⟩ := bounds_ws w1 m1 w2 m2
    have hinS := fun m hm => hS m (lookupAll_in hσ hinit m hm)
    obtain ⟨wb, eb, _⟩ := ih hbody (sc := fresh (n1 + 4 + inits.length) mlo.ty ::
        fresh (n1 + 3) mlo.ty :: freshList (n1 + 4) (tysOf inits) ++
          (fresh (n1 + 2) mlo.ty :: fresh (n1 + 1) mlo.ty :: fresh n1 mlo.ty ::
            scopeAfter sc (o1' ++ o1)))
      (EnvIn.cons (EnvIn.zip_append _ _
        (fun m hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
        (hσ.mono fun m hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (hS m hm))))))))
        List.mem_cons_self)
    have hin3 : ∀ {m}, m ∈ scopeAfter sc (o1' ++ o1) →
        m ∈ fresh (n1 + 2) mlo.ty :: fresh (n1 + 1) mlo.ty :: fresh n1 mlo.ty ::
          scopeAfter sc (o1' ++ o1) :=
      fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    apply leaf_good
    · rw [wsOps_append, w12, Bool.true_and, wsOps_const_cons]
      refine wsOps_bin_cons (List.mem_cons_of_mem _ m1') (List.mem_cons_of_mem _ m2') ?_
      refine wsOps_bin_cons List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) ?_
      refine forOp_ws (hin3 m1') (hin3 m2')
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (fun m hm => hin3 (hinS m hm)) ?_ (fun m hm => lookupAll_in eb hys m hm)
      exact wsOps_bin_cons
        (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
        List.mem_cons_self wb
    · refine envIn_after_loop _ _ hσ hS fun m hm => ?_
      rw [scopeAfter_append]
      simp only [scopeAfter, forOp, binOp, constOp, MOp.res]
      exact List.mem_append_left _ hm
    · simp
  case case49 md σ n c b inits hinit mc hc n2 oe σe outE hbody ys hys hty ih =>
    intro r h sc hσ; cases h
    obtain ⟨wb, eb, _⟩ := ih hbody (EnvIn.zip_append _ _
      (fun m hm => mem_freshList_append hm) (hσ.mono fun m hm => List.mem_append_right _ hm))
    apply leaf_good
    · refine whileOp_ws (lookupAll_in hσ hinit) (wsOps_nil _) ?_ wb
        (fun m hm => lookupAll_in eb hys m hm)
      exact lookup_in (EnvIn.zip_append _ _ (fun m hm => mem_freshList_append hm)
        (hσ.mono fun m hm => List.mem_append_right _ hm)) hc
    · exact EnvIn.zip_append _ _ (fun m hm => by simp [scopeAfter, whileOp, MOp.res, hm])
        (hσ.scopeAfter _)
    · simp
  case case55 md σ n c b inits hinit mc hc n2 oe σe outE hbody ys hys hty ih =>
    intro r h sc hσ; cases h
    have hσA : EnvIn ((accs σ b).zip (freshList (n + inits.length + 5) (tysOf inits)) ++ σ)
        (fresh (n + inits.length + 4) "i1" :: freshList (n + inits.length + 5) (tysOf inits) ++
          (fresh (n2 + 1) "i1" :: sc)) :=
      EnvIn.zip_append _ _ (fun m hm => List.mem_cons_of_mem _ (List.mem_append_left _ hm))
        (hσ.mono fun m hm => List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_of_mem _ hm)))
    obtain ⟨wb, eb, vb⟩ := ih hbody hσA
    have hmc : mc ∈ fresh n "i1" :: freshList (n + 1) (tysOf inits) ++
        (fresh (n2 + 1) "i1" :: sc) :=
      lookup_in (EnvIn.zip_append _ _
        (fun m hm => List.mem_cons_of_mem _ (List.mem_append_left _ hm))
        (hσ.mono fun m hm => List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_cons_of_mem _ hm)))) hc
    apply leaf_good
    · rw [wsOps_const_cons]
      refine whileOp_ws ?_ ?_ ?_ wb ?_
      · intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (lookupAll_in hσ hinit m hm)
      · rw [wsOps_const_cons]
        refine wsOps_bin_cons (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self ?_
        exact wsOps_bin_cons (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmc))
          List.mem_cons_self (wsOps_nil _)
      · simp [scopeAfter, constOp, binOp, MOp.res]
      · intro m hm
        rcases List.mem_append.1 hm with hm | hm
        · split at hm
          · exact vb m hm
          · simp only [List.mem_singleton] at hm
            subst hm
            exact mem_scopeAfter _ (by simp)
        · exact lookupAll_in eb hys m hm
    · exact EnvIn.zip_append _ _ (fun m hm => by simp [scopeAfter, whileOp, MOp.res, hm])
        (hσ.scopeAfter _)
    · simp

/-- The image of a function is well scoped: the operations of its body use only its
    parameters and values defined before them. -/
theorem nfToFunc_ws {cfg : Cfg} {fname : String} {params : List (String × String)}
    {e : ImpExpr} {op : MOp} (h : nfToFunc cfg fname params e = some op) :
    wsOps [] [op] = true := by
  unfold nfToFunc at h
  split at h
  · cases h
  · rename_i n' ops σ' out ht
    cases h
    have hσ : EnvIn (params.map fun p => (p.1, (⟨"a_" ++ p.1, p.2⟩ : MVal)))
        ((params.map fun p => (⟨"a_" ++ p.1, p.2⟩ : MVal)) ++ []) := by
      intro q hq
      simp only [List.mem_map] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      simp only [List.append_nil, List.mem_map]
      exact ⟨p, hp, rfl⟩
    obtain ⟨w, _, v⟩ := translate_ws cfg .val _ 0 e ht hσ
    simp only [wsOps_single, List.not_mem_nil, imp_false, wsRegions_cons, wsRegions_nil,
      Bool.and_true]
    refine ⟨fun _ h => by simp at h, ?_⟩
    rw [wsOps_append, w, Bool.true_and]
    simp only [wsOps_single, wsRegions_nil, and_true]
    exact v

theorem leaf_env (md : Mode) (σ : SEnv) (n : Nat) (ops : List MOp) (vals : List MVal) :
    (leaf md σ n ops vals).2.2.1 = σ := by
  cases md <;> rfl

theorem leaf_ops (md : Mode) (σ : SEnv) (n : Nat) (ops : List MOp) (vals : List MVal) :
    ∃ post, (leaf md σ n ops vals).2.1 = ops ++ post := by
  cases md
  · exact ⟨[], by simp [leaf]⟩
  · exact ⟨[], by simp [leaf]⟩
  · exact ⟨_, rfl⟩

theorem append_pair_append (A : List MOp) (c w : MOp) (post : List MOp) :
    A ++ [c, w] ++ post = (A ++ [c]) ++ w :: post := by simp

theorem lookupAll_length {σ : SEnv} :
    ∀ {xs : List String} {ms : List MVal}, lookupAll σ xs = some ms → ms.length = xs.length
  | [], ms, h => by simp [lookupAll] at h; subst h; rfl
  | x :: xs, ms, h => by
    unfold lookupAll at h
    split at h
    · rename_i m ms' _ h2
      cases h
      simp [lookupAll_length h2]
    · cases h

theorem freshList_length : ∀ (k : Nat) (tys : List String), (freshList k tys).length = tys.length
  | _, [] => rfl
  | k, _ :: ts => by simp [freshList, freshList_length (k + 1) ts]

theorem lookup_zip_append (σ : SEnv) :
    ∀ {xs : List String} {ms : List MVal}, xs.length = ms.length → ∀ {x : String}, x ∈ xs →
      ∃ m ∈ ms, lookup (xs.zip ms ++ σ) x = some m
  | [], _, _, _, hx => by simp at hx
  | _ :: _, [], hl, _, _ => by simp at hl
  | y :: ys, m :: ms, hl, x, hx => by
    by_cases hxy : y = x
    · subst hxy
      exact ⟨m, List.mem_cons_self, by simp [lookup]⟩
    · have hx' : x ∈ ys := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hxy
        · exact h
      obtain ⟨m', hm', hl'⟩ := lookup_zip_append σ (by simpa using hl) hx'
      refine ⟨m', List.mem_cons_of_mem _ hm', ?_⟩
      simpa [lookup, List.find?, hxy] using hl'

/-- The loop of a `forFold` carries exactly the accumulators: its image contains an
    operation whose operands are control values (bounds and step, or the counter and
    the exit flag) followed by the current values of `accs σ b`, and the output
    environment maps every accumulator to a result of that operation. -/
theorem translate_forFold_carries {cfg : Cfg} {md : Mode} {σ : SEnv} {n : Nat} {v : String}
    {lo hi b : ImpExpr} {r : Nat × List MOp × SEnv × List MVal}
    (h : translate cfg md σ n (.forFold v lo hi b) = some r) :
    ∃ inits, lookupAll σ (accs σ b) = some inits ∧
      ∃ pre post op ctl, r.2.1 = pre ++ op :: post ∧ op.args = ctl ++ inits ∧
        ctl.length ≤ 3 ∧ ∀ x ∈ accs σ b, ∃ m ∈ op.res, lookup r.2.2.1 x = some m := by
  rw [translate] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i inits hinit
  refine ⟨inits, hinit, ?_⟩
  have hlen := lookupAll_length hinit
  split at h
  · split at h
    · split at h
      · split at h
        · cases h
          obtain ⟨post, hpost⟩ := leaf_ops md _ _ _ []
          refine ⟨_, post, _, [_, _], hpost.trans (append_pair_append _ _ _ _), rfl,
            by simp, ?_⟩
          intro x hx
          rw [leaf_env]
          obtain ⟨m, hm, hl⟩ := lookup_zip_append (σ.filter fun p => p.1 != v)
            (ms := (freshList _ (_ :: "i1" :: tysOf inits)).drop 2)
            (by simp [freshList_length, tysOf, hlen]) hx
          exact ⟨m, List.mem_of_mem_drop hm, hl⟩
        · cases h
      · cases h
    · cases h
  · split at h
    · split at h
      · split at h
        · cases h
          obtain ⟨post, hpost⟩ := leaf_ops md _ _ _ []
          refine ⟨_, post, _, [_, _, _], hpost.trans (append_pair_append _ _ _ _), rfl,
            by simp, ?_⟩
          intro x hx
          rw [leaf_env]
          exact lookup_zip_append (σ.filter fun p => p.1 != v)
            (by simp [freshList_length, tysOf, hlen, forOp, MOp.res]) hx
        · cases h
      · cases h
    · cases h

/-- The `scf.while` of a `whileLoop` carries exactly the accumulators: its operands
    are the current values of `accs σ b`, and the output environment maps every
    accumulator to a result of the loop. -/
theorem translate_whileLoop_carries {cfg : Cfg} {md : Mode} {σ : SEnv} {n : Nat} {c : String}
    {b : ImpExpr} {r : Nat × List MOp × SEnv × List MVal}
    (h : translate cfg md σ n (.whileLoop (.var c) b) = some r) :
    ∃ inits, lookupAll σ (accs σ b) = some inits ∧
      ∃ post op, r.2.1 = op :: post ∧ op.args = inits ∧
        ∀ x ∈ accs σ b, ∃ m ∈ op.res, lookup r.2.2.1 x = some m := by
  rw [translate] at h
  split at h
  · cases h
  rename_i inits hinit
  refine ⟨inits, hinit, ?_⟩
  have hlen := lookupAll_length hinit
  split at h
  · cases h
  split at h
  · split at h
    · split at h
      · cases h
        obtain ⟨post, hpost⟩ := leaf_ops md _ _ _ []
        refine ⟨post, _, hpost, rfl, ?_⟩
        intro x hx
        rw [leaf_env]
        exact lookup_zip_append σ (by simp [freshList_length, tysOf, hlen, whileOp, MOp.res]) hx
      · cases h
    · cases h
  · cases h

end CatCrypt.Crypto.Hax.NFToMLIR
