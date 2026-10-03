/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi

/-!
# Loops with a carried register tuple (`ComLJ`) and their export to `Linear.lprog`

`ComLJ Γ t` is a layer above `ComL`: every `ComL` program is a `ComLJ` program
(`ComLJ.lift`), and two loop nodes carry a tuple of registers `cs` across the back-edge,
with a straight-line multi-result body `MultiReturnCom`:

* `forLoopRegs update count inits invs body` runs `update` for the trip indices
  `0, …, count - 1` over the context `cs ++ reg 64 :: invTys` (carried tuple, trip index,
  invariants) and returns the next tuple; the continuation `body` sees the final tuple.
* `whileRegs update inits invs body` runs `update` over `cs ++ invTys` and returns a
  continue bit `reg 1` followed by the next tuple; the loop stops at the first `false` bit
  and runs at least once.

These are the `forLoop` and `whileLoop` nodes of `NFProg jasminDialect` with a
straight-line body. `ComLJ.denote fuel` is partial: the do-while is iterated by
`NFProg.whileIter` and is `none` when the fuel runs out, so that the bisimulation with the
source `NFProg.denote` is `NFProgRel.whileIter_rel` at the step
`ComLJ.whileStep update invsV`; the counted loop is the `List.range` fold of
`ComLJ.forStep`, which `NFProgRel.foldlM_rel` meets against the source fold through
`some`.

The export to `Lprog` names carried binder `j` of a loop at depth `d` (the number of
bindings in scope) `regName (d + (cs.length - 1 - j))`, which is the name the continuation
reads it under, so the carried registers form no new name family. The body walk
`loopBodyWalkR` resolves the invariants to their operands at the node, the trip index to
`loopIdx d`, the carried binders to their `regName`s and the body temporaries to
`loopReg d k`. One frame per node:

```
counted (regsLoopFrame)            do-while (whileRegsFrame)
  MOV  c_j, init_j  (each j)         MOV  c_j, init_j  (each j)
  MOV  Lidx, #0                    .L<d>:
  MOV  Lctr, count                   <body copy>
  CMP  Lctr, #0                      <feedback MOV c_j, ret_j>
  Lcond Z  endL                      CMP  flag, inv  (each invariant base)
.L<d>:                               CMP  flag, #0
  <body copy>                        Lcond NZ .L<d>
  <feedback MOV c_j, ret_j>
  ADD  Lidx, #1
  SUB  Lctr, #1
  CMP  Lctr, inv  (each invariant base)
  CMP  Lctr, #0
  Lcond NZ .L<d>
endL:
```

The feedback moves are a parallel assignment: a returned operand that is another carried
register is first copied to a body temporary `loopReg d k` above the body's own
temporaries (`feedbackStage`). The continue bit is a `reg 1` value that the comparison
operations materialise as `0` or `1` in a register (`SET<cc>`), tested by the flag-`CMP`
and the condition-code `Lcond` that `JasminLsemMemFlagGuard.cmpArgs?` and `flagCondCC?`
recognise. With one carried binder, `regsLoopFrame` is `blockLoopFrame`
(`regsLoopFrame_single`).

## Main definitions

* `ComLJ` — the layered loop language; `ComLJ.forStep`, `ComLJ.whileStep`,
  `ComLJ.denote`.
* `loopResolveVarR`, `loopBodyWalkR` — the body walk over a carried tuple.
* `feedbackStage`, `feedbackMoves`, `regsLoopFrame`, `whileRegsFrame`,
  `forLoopRegsLcmd`, `whileRegsLcmd` — the frames.
* `comLJToBody`, `comLJRetReg`, `ComLJ.toLfundef` — the virtual export.
* `ComLJ.loopArgBaseNames`, `ComLJ.loopAccRegs`, `ComLJ.toLfundefPhysAbi`,
  `ComLJ.toLprogPhysAbi` — the physical export with the SysV ABI.

## Main results

* `ComLJ.denote_lift` — a lifted `ComL` program denotes `some` of its denotation.
* `ComLJ.forLoopRegs_single` — a counted loop carrying one value with the body
  `u.toMulti` denotes as `ComL.forLoopNRt u`.
* `regsLoopFrame_single` — with one carried binder the counted frame is `blockLoopFrame`.
* `ComLJ.toLfundef_lift`, `ComLJ.toLfundefPhysAbi_lift` — a lifted `ComL` program
  exports exactly as the `ComL` program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)

/-! ## 1. The language -/

/-- `ComL` with loop nodes that carry a tuple of registers `cs`, over a straight-line
    multi-result body.

    * `lift c` — a `ComL` program.
    * `var e body` — let-bind `e` and continue with `body`.
    * `forLoopRegs update count inits invs body` — a counted loop from the carried tuple
      `inits`: `update` runs over the carried tuple, the trip index and the invariants
      `invs`, and returns the next tuple; `body` sees the final tuple.
    * `whileRegs update inits invs body` — a do-while from the carried tuple `inits`:
      `update` runs over the carried tuple and the invariants and returns a continue bit
      in front of the next tuple; `body` sees the tuple after the first `false` bit. -/
inductive ComLJ : Ctxt jasminDialect → JasminTy → Type where
  /-- A `ComL` program. -/
  | lift {Γ t} (c : ComL Γ t) : ComLJ Γ t
  /-- Let-bind a straight-line expression. -/
  | var {Γ t s} (e : Expr jasminDialect Γ t) (body : ComLJ (t :: Γ) s) : ComLJ Γ s
  /-- A counted loop carrying the register tuple `cs`. -/
  | forLoopRegs {Γ s} {cs invTys : Ctxt jasminDialect}
      (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
      (count : Ctxt.Var Γ (JasminTy.reg 64))
      (inits : HVector (fun ty => Ctxt.Var Γ ty) cs)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComLJ (cs ++ Γ) s) : ComLJ Γ s
  /-- A do-while carrying the register tuple `cs`, stopped by a `reg 1` continue bit. -/
  | whileRegs {Γ s} {cs invTys : Ctxt jasminDialect}
      (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
      (inits : HVector (fun ty => Ctxt.Var Γ ty) cs)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComLJ (cs ++ Γ) s) : ComLJ Γ s

namespace ComLJ

/-- One trip of a counted carried-register loop at the trip index `i`: `update` on the
    carried tuple `acc`, the index `ofNat i` and the invariant values `invsV`. -/
def forStep {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invsV : Ctxt.Valuation invTys) (acc : Ctxt.Valuation cs) (i : Nat) :
    Ctxt.Valuation cs :=
  update.denote (hvAppend acc (.cons (BitVec.ofNat 64 i) invsV))

/-- One run of a do-while body: `update` on the carried tuple `acc` and the invariant
    values `invsV`, returning the continue bit and the next tuple. It always succeeds; it
    is the step `NFProg.whileIter` iterates. -/
def whileStep {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invsV : Ctxt.Valuation invTys) (acc : Ctxt.Valuation cs) :
    Option (Ctxt.Valuation (HasBitType.bit (d := jasminDialect) :: cs)) :=
  some (update.denote (hvAppend acc invsV))

/-- Denotation of a `ComLJ` program at the fuel `fuel`, which bounds the runs of each
    do-while body. A lifted program denotes `some` of its `ComL` denotation; a counted
    loop is the `List.range` fold of `forStep`, which always succeeds; a do-while is
    `NFProg.whileIter` of `whileStep`, `none` when the fuel runs out. -/
def denote (fuel : Nat) : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComLJ Γ t → Ctxt.Valuation Γ → Option ⟦t⟧
  | _, _, .lift c, V => some (c.denote V)
  | _, _, .var e body, V => body.denote fuel (V.extend (e.denote V))
  | _, _, .forLoopRegs update count inits invs body, V =>
      body.denote fuel (hvAppend
        ((List.range (count.lookup V).toNat).foldl
          (forStep update (Expr.lookupArgs invs V)) (Expr.lookupArgs inits V)) V)
  | _, _, .whileRegs update inits invs body, V =>
      NFProg.whileIter (d := jasminDialect) (whileStep update (Expr.lookupArgs invs V)) fuel
          (Expr.lookupArgs inits V) >>= fun acc =>
        body.denote fuel (hvAppend acc V)

/-- A lifted `ComL` program denotes `some` of its denotation, at every fuel. -/
theorem denote_lift {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) (fuel : Nat)
    (V : Ctxt.Valuation Γ) : (ComLJ.lift c).denote fuel V = some (c.denote V) := rfl

/-- The fold of `forStep` over the body `u.toMulti` of one carried value is the fold of
    `JLoopBodyN.stepC u`. -/
theorem foldl_forStep_toMulti {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (u : Com jasminDialect (accTy :: JasminTy.reg 64 :: invTys) accTy)
    (invsV : Ctxt.Valuation invTys) :
    (L : List Nat) → (a : ⟦accTy⟧) →
    L.foldl (forStep (cs := [accTy]) u.toMulti invsV) (.cons a .nil) =
      .cons (L.foldl (fun acc t => JLoopBodyN.stepC u invsV t acc) a) .nil
  | [], _ => rfl
  | i :: L, a => by
      simp only [List.foldl_cons]
      have h : forStep (cs := [accTy]) u.toMulti invsV (.cons a .nil) i =
          .cons (JLoopBodyN.stepC u invsV i a) .nil :=
        Com.denote_toMulti u _
      rw [h]
      exact foldl_forStep_toMulti u invsV L _

/-- **The bridge to `ComL.forLoopNRt`.** A counted loop carrying one value whose body is
    `u.toMulti` and whose continuation is a lifted `ComL` program denotes `some` of the
    denotation of `ComL.forLoopNRt u`, at every fuel. -/
theorem forLoopRegs_single {Γ : Ctxt jasminDialect} {s accTy : JasminTy}
    {invTys : Ctxt jasminDialect}
    (u : Com jasminDialect (accTy :: JasminTy.reg 64 :: invTys) accTy)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (k : ComL (accTy :: Γ) s)
    (fuel : Nat) (V : Ctxt.Valuation Γ) :
    (ComLJ.forLoopRegs (cs := [accTy]) u.toMulti count (.cons init .nil) invs
        (.lift k)).denote fuel V =
      some ((ComL.forLoopNRt u count init invs k).denote V) := by
  show some (k.denote (hvAppend ((List.range (count.lookup V).toNat).foldl
      (forStep (cs := [accTy]) u.toMulti (Expr.lookupArgs invs V))
      (.cons (init.lookup V) .nil)) V)) = _
  rw [foldl_forStep_toMulti]
  rfl

end ComLJ

/-! ## 2. The body walk over a carried tuple -/

/-- Resolve a variable of a carried-register loop body at depth `d`. The body context is
    `cs ++ idx ++ invTys` with `nCar = cs.length` carried binders, the trip index
    present exactly when `idx = some idxReg`, and one operand of `invOps` per invariant
    (in `invTys` order). By root slot (`slot = curDepth - 1 - deBruijn`): an invariant
    (slot `< nInv`) is its operand, the index (slot `nInv`, when present) is `idxReg`, a
    carried binder is `regName (base + k)` for its position `k` counted from the bottom of
    `cs`, and a deeper slot is the body temporary `loopReg d slot`. -/
def loopResolveVarR (d base nCar : Nat) (idx : Option String) (invOps : List LOperand)
    (curDepth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    LOperand :=
  let nInv := invOps.length
  let nIdx := if idx.isSome then 1 else 0
  let slot := curDepth - 1 - varIndex v
  if slot < nInv then invOps.getD (nInv - 1 - slot) (.reg (loopReg d slot))
  else
    match idx with
    | some r =>
        if slot = nInv then .reg r
        else if slot < nInv + nIdx + nCar then .reg (regName (base + (slot - nInv - nIdx)))
        else .reg (loopReg d slot)
    | none =>
        if slot < nInv + nCar then .reg (regName (base + (slot - nInv)))
        else .reg (loopReg d slot)

/-- Resolve a vector of variables of a carried-register loop body (`loopResolveVarR`). -/
def loopVarsR (d base nCar : Nat) (idx : Option String) (invOps : List LOperand)
    (curDepth : Nat) {Γ : Ctxt jasminDialect} :
    {tys : Ctxt jasminDialect} → HVector (fun ty => Ctxt.Var Γ ty) tys → List LOperand
  | [], _ => []
  | _ :: _, .cons v rest =>
      loopResolveVarR d base nCar idx invOps curDepth v
        :: loopVarsR d base nCar idx invOps curDepth rest

/-- Walk a straight-line multi-result loop body into one single-iteration `Lcmd`, the
    operands of its returned variables, and the depth after its last binding. Each binding
    writes the body temporary `loopReg d curDepth`. -/
def loopBodyWalkR (d base nCar : Nat) (idx : Option String) (invOps : List LOperand) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    MultiReturnCom jasminDialect Γ ts → (curDepth : Nat) → (Lcmd × List LOperand × Nat)
  | _, _, .ret vs, curDepth => ([], loopVarsR d base nCar idx invOps curDepth vs, curDepth)
  | _, _, .var e body, curDepth =>
      let r := loopBodyWalkR d base nCar idx invOps body (curDepth + 1)
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (loopVarsR d base nCar idx invOps curDepth e.args)⟩ :: r.1, r.2.1, r.2.2)

/-! ## 3. The frames -/

/-- The staging of a parallel feedback assignment: the `i`-th returned operand that is a
    carried register other than its own target `targets[i]` is copied first to the body
    temporary `loopReg d (tmp0 + i)`, and its source becomes that temporary. Returns the
    staging copies and the sources of the final moves. -/
def feedbackStage (d tmp0 : Nat) (targets : List String) :
    List LOperand → Nat → Lcmd × List LOperand
  | [], _ => ([], [])
  | op :: ops, i =>
      let r := feedbackStage d tmp0 targets ops (i + 1)
      match op with
      | .reg x =>
          if targets.contains x && !(targets[i]? == some x) then
            (⟨0, .Lopn [.reg (loopReg d (tmp0 + i))] (withWidthTag 64 "MOV") [.reg x]⟩ :: r.1,
              .reg (loopReg d (tmp0 + i)) :: r.2)
          else (r.1, op :: r.2)
      | _ => (r.1, op :: r.2)

/-- The final feedback moves `MOV target, src`, omitting a move of a register onto
    itself. -/
def feedbackMoves : List String → List LOperand → Lcmd
  | t :: ts, s :: ss =>
      let rest := feedbackMoves ts ss
      match s with
      | .reg x => if x == t then rest else ⟨0, .Lopn [.reg t] (withWidthTag 64 "MOV") [s]⟩ :: rest
      | _ => ⟨0, .Lopn [.reg t] (withWidthTag 64 "MOV") [s]⟩ :: rest
  | _, _ => []

/-- The counted back-edge frame of a carried-register loop at depth `d` around one
    pre-walked body copy `bodyW`. `accs` lists, per carried binder, its register, its
    seed operand and the body's returned operand; `tmp0` is the first body temporary
    index above the body's own. Seeds every carried register, then the index, counter,
    zero-trip guard, label, body copy, the parallel feedback (`feedbackStage`,
    `feedbackMoves`), index advance, counter decrement, invariant-base touches and the
    `Lctr`/`CMP`/`Lcond NZ` back-edge: `blockLoopFrame` with a tuple of accumulators. -/
def regsLoopFrame (d : Nat) (accs : List (String × LOperand × LOperand))
    (idxReg ctr : String) (countOp : LOperand) (invRegs : List String) (bodyW : Lcmd)
    (tmp0 : Nat) : Lcmd :=
  let targets := accs.map (·.1)
  let stage := feedbackStage d tmp0 targets (accs.map (·.2.2)) 0
  let feedback : Lcmd := stage.1 ++ feedbackMoves targets stage.2
  let seeds : Lcmd := accs.map fun a => ⟨0, .Lopn [.reg a.1] (withWidthTag 64 "MOV") [a.2.1]⟩
  let top : LLabel := d
  let endL : LLabel := d + 0x40000000
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
  seeds ++
  [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [countOp]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
  , ⟨0, .Lcond (.reg "Z") endL⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") top⟩
     , ⟨0, .Llabel .internal endL⟩ ]

/-- With one carried binder, the counted frame is `blockLoopFrame`. -/
theorem regsLoopFrame_single (d : Nat) (accReg idxReg ctr : String)
    (initOp countOp : LOperand) (invRegs : List String) (bodyW : Lcmd) (retReg : String)
    (tmp0 : Nat) :
    regsLoopFrame d [(accReg, initOp, .reg retReg)] idxReg ctr countOp invRegs bodyW tmp0 =
      blockLoopFrame d accReg idxReg ctr initOp countOp invRegs bodyW retReg := by
  by_cases h : retReg = accReg
  · subst h
    simp [regsLoopFrame, blockLoopFrame, feedbackStage, feedbackMoves]
  · have h' : (accReg == retReg) = false := by simp [Ne.symm h]
    simp [regsLoopFrame, blockLoopFrame, feedbackStage, feedbackMoves, h, h']

/-- The do-while back-edge frame of a carried-register loop at depth `d` around one
    pre-walked body copy `bodyW` whose continue bit is the operand `flagOp`. Seeds every
    carried register, then the label, body copy, the parallel feedback (the bit is staged
    with the returned operands, so a feedback move never overwrites it), the
    invariant-base touches and the bottom test `CMP r, #0 ; Lcond NZ top` on the body
    temporary `r := loopReg d (tmp0 + accs.length + 1)`, which holds the bit as a 64-bit
    word: a bit in a register `f` is selected into it by `MOV r, #1 ; MOV z, #0 ;
    CMOV r, [f, r, z]` (`z := loopReg d (tmp0 + accs.length + 2)`), and a bit that is not
    a register is moved into it. No counter and no zero-trip guard: the body runs at
    least once. -/
def whileRegsFrame (d : Nat) (accs : List (String × LOperand × LOperand))
    (flagOp : LOperand) (invRegs : List String) (bodyW : Lcmd) (tmp0 : Nat) : Lcmd :=
  let targets := accs.map (·.1)
  let stage := feedbackStage d tmp0 targets (accs.map (·.2.2) ++ [flagOp]) 0
  let flagSrc := stage.2.getD accs.length flagOp
  let feedback : Lcmd := stage.1 ++ feedbackMoves targets stage.2
  let flagMat : String × Lcmd :=
    let r := loopReg d (tmp0 + accs.length + 1)
    match flagSrc with
    | .reg f =>
        let z := loopReg d (tmp0 + accs.length + 2)
        (r, [ ⟨0, .Lopn [.reg r] (withWidthTag 64 "MOV") [.imm 1]⟩
            , ⟨0, .Lopn [.reg z] (withWidthTag 64 "MOV") [.imm 0]⟩
            , ⟨0, .Lopn [.reg r] (withWidthTag 64 "CMOV") [.reg f, .reg r, .reg z]⟩ ])
    | op => (r, [⟨0, .Lopn [.reg r] (withWidthTag 64 "MOV") [op]⟩])
  let flagReg := flagMat.1
  let seeds : Lcmd := accs.map fun a => ⟨0, .Lopn [.reg a.1] (withWidthTag 64 "MOV") [a.2.1]⟩
  let top : LLabel := d
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, .Lopn [.reg flagReg] (withWidthTag 64 "CMP") [.reg flagReg, .reg r]⟩)
  seeds ++ [⟨0, .Llabel .internal top⟩]
  ++ bodyW ++ feedback ++ flagMat.2
  ++ invTouch
  ++ [ ⟨0, .Lopn [.reg flagReg] (withWidthTag 64 "CMP") [.reg flagReg, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") top⟩ ]

/-- The register names of the carried binders of a loop at depth `d` with `nCar`
    carried binders, in `cs` order: binder `j` is `regName (d + (nCar - 1 - j))`. -/
def carriedRegs (d nCar : Nat) : List String :=
  (List.range nCar).map fun j => regName (d + (nCar - 1 - j))

/-- The `Lcmd` of a counted carried-register loop node at depth `d`: the seed operands
    `initOps` (one per carried binder), the count operand and the invariant operands
    `invOps`, resolved against the enclosing context; the body walked at the start depth
    `invTys.length + 1 + cs.length`. -/
def forLoopRegsLcmd (d : Nat) (initOps : List LOperand) (countOp : LOperand)
    {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) : Lcmd :=
  let nCar := cs.length
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let w := loopBodyWalkR d d nCar (some idxReg) invOps update (invTys.length + 1 + nCar)
  regsLoopFrame d ((carriedRegs d nCar).zip (initOps.zip w.2.1)) idxReg (loopCtr d) countOp
    invRegs w.1 w.2.2

/-- The `Lcmd` of a do-while carried-register loop node at depth `d`: the seed operands
    `initOps` and the invariant operands `invOps`, resolved against the enclosing context;
    the body walked at the start depth `invTys.length + cs.length`. The body returns the
    continue bit first, then the next tuple. -/
def whileRegsLcmd (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) : Lcmd :=
  let nCar := cs.length
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let w := loopBodyWalkR d d nCar none invOps update (invTys.length + nCar)
  whileRegsFrame d ((carriedRegs d nCar).zip (initOps.zip w.2.1.tail))
    (w.2.1.headD (.imm 0)) invRegs w.1 w.2.2

/-! ## 4. The virtual export -/

/-- Walk a `ComLJ` program into its `Lcmd` body at the depth `curDepth`. A lifted program
    is `comLToBody`; a let-binding is as in `comLToBody`; a loop node splices its frame
    and continues at the depth after its carried binders. -/
def comLJToBody (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComLJ Γ t → (curDepth : Nat) → Lcmd
  | _, _, .lift c, curDepth => comLToBody nArgs argNames immSlotMap c curDepth
  | _, _, .var e body, curDepth =>
      ⟨0, opToLinstrR e.op (regName curDepth)
            (exprArgs curDepth nArgs argNames immSlotMap e)⟩
        :: comLJToBody nArgs argNames immSlotMap body (curDepth + 1)
  | _, _, .forLoopRegs (cs := cs) update count inits invs body, curDepth =>
      forLoopRegsLcmd curDepth (exprArgsHV curDepth nArgs argNames immSlotMap inits)
          (resolveVar curDepth nArgs argNames immSlotMap count) update
          (exprArgsHV curDepth nArgs argNames immSlotMap invs)
        ++ comLJToBody nArgs argNames immSlotMap body (curDepth + cs.length)
  | _, _, .whileRegs (cs := cs) update inits invs body, curDepth =>
      whileRegsLcmd curDepth (exprArgsHV curDepth nArgs argNames immSlotMap inits) update
          (exprArgsHV curDepth nArgs argNames immSlotMap invs)
        ++ comLJToBody nArgs argNames immSlotMap body (curDepth + cs.length)

/-- The register name of a `ComLJ` program's final return value. -/
def comLJRetReg (nArgs : Nat) (argNames : Nat → String) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComLJ Γ t → (curDepth : Nat) → String
  | _, _, .lift c, curDepth => comLRetReg nArgs argNames c curDepth
  | _, _, .var _ body, curDepth => comLJRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopRegs (cs := cs) _ _ _ _ body, curDepth =>
      comLJRetReg nArgs argNames body (curDepth + cs.length)
  | _, _, .whileRegs (cs := cs) _ _ _ body, curDepth =>
      comLJRetReg nArgs argNames body (curDepth + cs.length)

/-- The virtual `lfundef` of a `ComLJ` program over the argument context `Γ`. -/
def ComLJ.toLfundef {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lfundef :=
  let nArgs := Γ.length
  { lfd_info := 0
    lfd_align := 1
    lfd_tyin := Γ.reverse.map tyWidth
    lfd_arg := (List.range nArgs).map argName
    lfd_body := comLJToBody nArgs argName immSlotMap c nArgs
    lfd_tyout := [tyWidth t]
    lfd_res := [comLJRetReg nArgs argName c nArgs]
    lfd_export := true
    lfd_callee_saved := []
    lfd_stk_max := 0
    lfd_frame_size := 0
    lfd_align_args := [] }

/-- A lifted `ComL` program has the virtual `lfundef` of the `ComL` program. -/
theorem ComLJ.toLfundef_lift {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (immSlotMap : ImmSlotMap) :
    (ComLJ.lift c).toLfundef immSlotMap = c.toLfundef immSlotMap := rfl

/-! ## 5. The physical export with the SysV ABI -/

/-- The position of the first array-typed entry of a list of types. -/
def arrPos? : List JasminTy → Option Nat
  | [] => none
  | .stackArr _ _ :: _ => some 0
  | _ :: tys => (arrPos? tys).map (· + 1)

/-- The resolved register name of the first array-typed seed of a vector of variables. -/
def arrSeedName? (curDepth nArgs : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    {tys : Ctxt jasminDialect} → HVector (fun ty => Ctxt.Var Γ ty) tys → Option String
  | [], _ => none
  | ty :: _, .cons v rest =>
      match ty, resolveVar curDepth nArgs argName immSlotMap v with
      | .stackArr _ _, LOperand.reg n => some n
      | .stackArr _ _, _ => none
      | _, _ => arrSeedName? curDepth nArgs immSlotMap rest

/-- The canonical loop-argument base names of a `ComLJ` program: the `ComL` names of a
    lifted program, and for a carried-register loop the resolved seed of its first
    array-typed carried binder (the output array) with the array-typed invariant base
    names. -/
def ComLJ.loopArgBaseNames (nArgs : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t) (curDepth : Nat) :
    Option (String × List String) :=
  match c with
  | .lift c => ComL.loopArgBaseNames nArgs immSlotMap c curDepth
  | .var _ body => ComLJ.loopArgBaseNames nArgs immSlotMap body (curDepth + 1)
  | .forLoopRegs _ _ inits invs _ =>
      (arrSeedName? curDepth nArgs immSlotMap inits).map fun o =>
        (o, arrArgNamesHV curDepth nArgs immSlotMap invs)
  | .whileRegs _ inits invs _ =>
      (arrSeedName? curDepth nArgs immSlotMap inits).map fun o =>
        (o, arrArgNamesHV curDepth nArgs immSlotMap invs)

/-- The virtual-register indices of the loop accumulators that carry the output array, in
    spine order: the `ComL` accumulators of a lifted program, and for a carried-register
    loop at depth `depth` the index `depth + (cs.length - 1 - j)` of its first array-typed
    carried binder `j`. -/
def ComLJ.loopAccRegs {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComLJ Γ t) (depth : Nat) : List Nat :=
  match c with
  | .lift c => ComL.loopAccRegs c depth
  | .var _ body => ComLJ.loopAccRegs body (depth + 1)
  | .forLoopRegs (cs := cs) _ _ _ _ body =>
      ((arrPos? cs).map fun j => depth + (cs.length - 1 - j)).toList
        ++ ComLJ.loopAccRegs body (depth + cs.length)
  | .whileRegs (cs := cs) _ _ _ body =>
      ((arrPos? cs).map fun j => depth + (cs.length - 1 - j)).toList
        ++ ComLJ.loopAccRegs body (depth + cs.length)

/-- The 2-pointer-ABI physical `lfundef` of a `ComLJ` program: `lfundefPhysAbiOfVirt` at
    the virtual export `ComLJ.toLfundef`, the derived base names (the caller's
    `outArg`/`inArgs` when the program has no loop node) and the loop accumulators. -/
def ComLJ.toLfundefPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t)
    (outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : Lfundef :=
  let nArgs := Γ.length
  let derived : String × List String :=
    match ComLJ.loopArgBaseNames nArgs immSlotMap c nArgs with
    | some (o, ins) => (o, ins)
    | none => (outArg, inArgs)
  lfundefPhysAbiOfVirt (ComLJ.toLfundef c immSlotMap) derived.1 derived.2
    ((ComLJ.loopAccRegs c nArgs).map regName) shiftImm abiArgs abiTyin

/-- A lifted `ComL` program has the physical `lfundef` of the `ComL` program. -/
theorem ComLJ.toLfundefPhysAbi_lift {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (outArg : String) (inArgs : List String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (abiArgs : List String) (abiTyin : List Nat) :
    (ComLJ.lift c).toLfundefPhysAbi outArg inArgs shiftImm immSlotMap abiArgs abiTyin =
      c.toLfundefPhysAbi outArg inArgs shiftImm immSlotMap abiArgs abiTyin := rfl

/-- Export a `ComLJ` program to a 2-pointer-ABI physical `Lprog` with one function. -/
def ComLJ.toLprogPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, ComLJ.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs abiTyin)] }

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
