/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
public import CatCrypt.Crypto.SecureCompilation.VIR.X86IsaData
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoopsJ
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfgTactic

/-!
# The export of a structured program by recursion over its regions

`exportR` maps a structured program `NFProg jasminDialect Γ ts` to labelled typed linear
code `List LinstrRM`, by structural recursion on the program: a straight binding is one
instruction, and each control construct is a frame around the exports of its regions.
Regions nest to any depth, and two regions never share a label.

## Design

* **Recursion.** `exportR` is defined by structural recursion on `NFProg`, with one
  equation per constructor. The eliminator `NFProg.regionRec` of `NFRegionSig` presents the
  four control constructors as one case with a list of regions; each construct here has
  its own frame, so the uniform case would be split again by the operation, and the
  structural definition gives each equation by `rfl`.
* **Label supply.** A counter `n` is threaded through the export. A construct takes its
  own labels from the counter (`forLoop`: `n`, `n + 1`; `whileLoop`: `n`; `ifThenElse`:
  `n`, `n + 1`, `n + 2`), then exports its regions and its continuation one after the
  other, each from the counter the previous one returned. The labels of a region are
  therefore the interval between the counter it receives and the counter it returns, and
  the intervals of sibling and nested regions are disjoint.
* **Registers.** Every variable of the context `Γ` at depth `d = Γ.length` is read as
  `resolveVar d nArgs argName`, and a binding at depth `d` writes `regName d`. This is the
  naming of the straight-line export `straightOpsMem`, and the naming under which the
  store agreement `StoreAgreesM nArgs d` is stated, so the same agreement is the invariant
  at the entry of every region. A region binds its parameters at the next depths: the
  body of `forLoop` at depth `d` reads the trip index at `regName d` and the carried
  tuple at the block above it.
* **Results of a region.** `exportR` returns, beside the code, the operands of the
  returned variables and the depth at the return. The enclosing frame moves the operands
  into the registers of its binders in two stages (`parMoves`): first into temporaries
  above the depth at the return, then into the targets, so that a result that is itself a
  target is read before it is overwritten.
* **Loop counter.** The trip counter of the loop with top label `n` is `loopCtr n`. It is
  outside the `regName` family, so no binding of the body writes it, and the label makes it
  distinct from the counter of every other region.
* **Instruction set.** The zero-trip guard, the back-edge guard and the select that widens
  a one-bit value are those of the parameter `I : IsaData`. The branch of `ifThenElse`
  uses the zero-trip guard of `I` as the test "jump to the second label when the register
  is zero, reach the first otherwise".

## The frames

```
forLoop (forFrame), labels n, n+1         whileLoop (whileFrame), label n
  MOV  r(d+1+k), init_k   (each k)          MOV  r(d+k), init_k   (each k)
  MOV  r(d), #0                           .n:
  MOV  ctr, count                           <body at depth d + |cs|>
  <zero-trip guard ctr n (n+1)>             <flag word of the returned bit>
.n:                                         <parMoves of the returned tuple>
  <body at depth d + 1 + |cs|>              <back-edge guard flag n>
  <parMoves of the returned tuple>
  ADD  r(d), r(d), #1                     ifThenElse (ifFrame), labels n, n+1, n+2
  SUB  ctr, ctr, #1                         <flag word of the condition bit>
  <back-edge guard ctr n>                   <zero-trip guard flag n (n+1)>
.n+1:                                     .n:
  MOV  r(d+k), r(d+1+k)   (each k)          <then at depth d> <parMoves> GOTO n+2
                                          .n+1:
                                            <else at depth d> <parMoves>
                                          .n+2:
```

A `call` is refused.

## The simulation statement

`ExportRSim nArgs fn p` states that the code of `p`, placed anywhere in the body of a
program, simulates the denotation of `p` on the x86 flag machine: from a state at the first
instruction of the code whose store agrees with a valuation `V` (`StoreAgreesM`), if
`p.denote fuel V = some v` then a run of steps reaches the counter after the code in a
state whose store agrees with a valuation at the returned depth under which the returned
operands are variables denoting `v` (`ResAgrees`), and which differs from the entry state
only at the registers a region at this depth and label may write (`RegionFrame`). The
hypotheses on the placement are that the body is `pre ++ code ++ post` and that `pre`
declares no label from the counter on.

The statement is the same for a program and for each of its regions, so each construct has
a frame rule from the statement for its regions and its continuation to the statement for
the construct. The rules for a return and a binding are proved here.

The frame rules of the two loops are proved for carried types held in register cells
(`RegTys`): the copies of a frame move register cells, and a carried stack array is not
moved by them. The rule for a counted loop inducts on the trips left, with the invariant
at the counter after the top label: the store agrees with the entry valuation, the trip
index and the counter are in their registers, and the carried tuple is in the carried
block. The rule for an exit-flag loop inducts on the runs of `NFProg.whileIter`.

The frame rule of a branch runs the head (the widening of the condition bit and the
compare), then the selected branch and the assignment of its results to the result block,
and joins the two runs at the counter after the join label.

`RegionExportable` collects the hypotheses of the rules: no `call`, every binding in
`BindMemN`, and register carried and result types. `exportR_sim` is the induction over the
program. `exportR` returns `none` exactly on a program with a `call`
(`exportR_eq_none_iff`).

## Main definitions

* `labelI`, `condI`, `gotoI`, `movI`, `movImmI` — the instructions of the frames.
* `seedMoves`, `shiftMoves`, `advanceOps` — the seeds, the shift and the advance of a loop.
* `stageMoves`, `commitMoves`, `parMoves` — the two-stage parallel assignment.
* `flagWord` — the widening of a one-bit operand to a word.
* `forFrame`, `whileFrame`, `ifFrame` — the frames.
* `bindOps` — the instruction of one binding, the element `straightOpsMem` emits.
* `Exported`, `exportR` — the export.
* `exportRBody`, `exportRLfundef` — the wire body and the virtual function of a program.
* `labelsOf`, `targetsOf` — the labels a code declares and the labels its jumps name.
* `GuardsPlain` — the guards of an instruction set declare no label and jump only to the
  labels they are given.
* `LabelsOK` — the label facts of an export.
* `RegionFrame d n s s'` — `s'` reads as `s` at every register and array name outside the
  registers `regName k`, `d ≤ k`, and the counters `loopCtr l`, `n ≤ l`.
* `ResAgrees`, `BindMemN`, `ExportRSim`, `StraightMemN` — the returned-operand agreement,
  the fragment of a binding, the simulation statement, and returns under bindings.
* `isRegTy`, `RegTys` — the types held in a register cell, and the lists of such types.
* `RegionExportable` — the programs the export simulates.

## Main results

* `exportR_labelsOK` — the four label facts below, by induction on the program.
* `StoreAgreesM.of_regionFrame` — a region frame keeps the store agreement at its depth.
* `exportRSim_ret`, `exportRSim_var` — the statement for a return, and the frame rule of a
  binding.
* `exportR_sim_straight` — the statement for every return under bindings of the fragment.
* `steps_moves`, `steps_parMoves` — register copies as an assignment, and the two-stage
  parallel assignment.
* `storeAgreesM_append` — the store agreement under a block of binders.
* `forLoop_trips`, `forFrame_sim` — the trips of a counted loop, and its frame rule.
* `whileLoop_trips`, `whileFrame_sim` — the trips of an exit-flag loop, and its frame rule.
* `flagWord_steps`, `resMoves_steps`, `ifFrame_sim` — the widening of a bit, the assignment
  of the results of a region, and the frame rule of a branch.
* `exportR_sim` — the simulation statement for every program of `RegionExportable`.
* `exportR_eq_some_iff`, `exportR_eq_none_iff` — the export succeeds exactly on the
  programs without a `call`.
* `exportRSim_lsemFuelMemF` — the code of an export, as a whole body, halts under the
  fuelled interpreter `lsemFuelMemF` in a state that agrees with the denotation.
* `exportR_lsemFuelMemF` — the same run for a whole program of `RegionExportable`, from the
  depth of its argument context and the label `0`.
* `exportR_next_le` — the counter does not decrease.
* `exportR_labels_range` — the labels of the export lie between the counter it receives
  and the counter it returns.
* `exportR_labels_nodup` — no label is declared twice.
* `exportR_targets_declared` — every jump of the export names a label of the export.
* `exportR_findLabelMem_none` — the export declares no label outside its interval.
* `findLabelMem_eq_none_iff` — `findLabelMem` fails exactly on the labels not declared.
* `x86Data_guardsPlain` — the guards of x86 satisfy `GuardsPlain`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data x86Data_loopGuard
  x86Data_zeroTripGuard)

/-! ## 1. The instructions of the frames -/

/-- The declaration of the label `l`. -/
def labelI (l : LLabel) : LinstrRM := (.Llabel .internal l, .reg none)

/-- The conditional jump to `l` on the condition `c`. -/
def condI (c : LOperand) (l : LLabel) : LinstrRM := (.Lcond c l, .reg none)

/-- The jump to the label `l` of the function `fn`. -/
def gotoI (fn : String) (l : LLabel) : LinstrRM := (.Lgoto (fn, l), .reg none)

/-- The move `MOV dst, src`. -/
def movI (dst : String) (src : LOperand) : LinstrRM :=
  (.Lopn [.reg dst] (withWidthTag 64 "MOV") [src], .reg none)

/-- The move of the immediate `k` into `dst`. -/
def movImmI (dst : String) (k : Nat) : LinstrRM := movI dst (.imm k)

/-- An instruction of an instruction-set guard, with the register tag. -/
def guardI (i : LinstrR) : LinstrRM := (i, .reg none)

/-- The first stage of a parallel assignment: operand `i` of `ops` is copied to the
    temporary `regName (D + i)`. -/
def stageMoves (D : Nat) (ops : List LOperand) : List LinstrRM :=
  ops.zipIdx.map fun p => movI (regName (D + p.2)) p.1

/-- The second stage of a parallel assignment: target `i` of `tgts` is written from the
    temporary `regName (D + i)`. -/
def commitMoves (D : Nat) (tgts : List String) : List LinstrRM :=
  tgts.zipIdx.map fun p => movI p.1 (.reg (regName (D + p.2)))

/-- The parallel assignment of the operands `ops` to the registers `tgts` through the
    temporaries `regName D`, `regName (D + 1)`, …. -/
def parMoves (D : Nat) (tgts : List String) (ops : List LOperand) : List LinstrRM :=
  stageMoves D ops ++ commitMoves D tgts

/-- The widening of a one-bit operand to a word in the register `r`. A bit in a register
    `f` is selected by `MOV r, #1 ; MOV z, #0 ; m r, [f, r, z]` with the select mnemonic
    `I.selectMnemonic = some m`; an instruction set without a select has no instructions
    for it. An operand that is not a register is moved into `r`. -/
def flagWord (I : IsaData) (r z : String) : LOperand → List LinstrRM
  | .reg f =>
      match I.selectMnemonic with
      | some m =>
          [ movImmI r 1, movImmI z 0
          , (.Lopn [.reg r] (withWidthTag 64 m) [.reg f, .reg r, .reg z], .reg none) ]
      | none => []
  | op => [movI r op]

/-- The seeds of a block of registers: `MOV car_k, op_k` for each pair. -/
def seedMoves (car : List String) (ops : List LOperand) : List LinstrRM :=
  (car.zip ops).map fun p => movI p.1 p.2

/-- The moves of the block of `nCar` registers above `regName d` down one register:
    `MOV r(d+k), r(d+1+k)` for `k = 0, …, nCar - 1`. -/
def shiftMoves (d nCar : Nat) : List LinstrRM :=
  (List.range nCar).map fun k => movI (regName (d + k)) (.reg (regName (d + 1 + k)))

/-- The advance of a counted loop: the trip index `idx` is incremented and the counter
    `ctr` decremented. -/
def advanceOps (idx ctr : String) : List LinstrRM :=
  [ (.Lopn [.reg idx] (withWidthTag 64 "ADD") [.reg idx, .imm 1], .reg none)
  , (.Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1], .reg none) ]

/-! ## 2. The frames -/

/-- The frame of a counted loop at depth `d` with the labels `n` (top) and `n + 1` (exit)
    around the exported body `bodyC`, whose returned operands are `bodyOps` at the depth
    `bodyD`. The carried tuple of `nCar` values is seeded from `initOps` into the block
    `carriedRegs (d + 1) nCar`, the trip index `regName d` from `0`, and the counter
    `loopCtr n` from `countOp`; after the exit label the tuple is moved down one register,
    to the block `carriedRegs d nCar` where the continuation reads it. -/
def forFrame (d n nCar : Nat) (initOps : List LOperand) (countOp : LOperand)
    (bodyC : List LinstrRM) (bodyOps : List LOperand) (bodyD : Nat)
    (I : IsaData := x86Data) : List LinstrRM :=
  let ctr := loopCtr n
  let car := carriedRegs (d + 1) nCar
  seedMoves car initOps
  ++ (seedMoves [regName d, ctr] [.imm 0, countOp]
  ++ ((I.zeroTripGuard ctr n (n + 1)).map guardI
  ++ (labelI n
  :: (bodyC
  ++ (parMoves bodyD car bodyOps
  ++ (advanceOps (regName d) ctr
  ++ ((I.loopGuard ctr n).map guardI
  ++ (labelI (n + 1)
  :: shiftMoves d nCar))))))))

/-- The frame of a loop in exit-flag form at depth `d` with the label `n` around the
    exported body `bodyC`, whose returned operands at the depth `bodyD` are the continue
    bit `flagOp` and the next tuple `bodyOps`. The carried tuple lives in the block
    `carriedRegs d nCar`, where the body and the continuation read it. The bit is widened
    into `regName (bodyD + nCar)` before the tuple is assigned. -/
def whileFrame (d n nCar : Nat) (initOps : List LOperand)
    (bodyC : List LinstrRM) (flagOp : LOperand) (bodyOps : List LOperand) (bodyD : Nat)
    (I : IsaData := x86Data) : List LinstrRM :=
  let car := carriedRegs d nCar
  let flag := regName (bodyD + nCar)
  seedMoves car initOps
  ++ (labelI n
  :: (bodyC
  ++ (flagWord I flag (regName (bodyD + nCar + 1)) flagOp
  ++ (parMoves bodyD car bodyOps
  ++ (I.loopGuard flag n).map guardI))))

/-- The frame of a branch at depth `d` with the labels `n` (then), `n + 1` (else) and
    `n + 2` (join) in the function `fn`, around the exported branches `thnC` and `elsC`
    with the returned operands `thnOps` at depth `thnD` and `elsOps` at depth `elsD`. The
    condition bit `condOp` is widened into `regName d`; each branch assigns its results to
    the block `carriedRegs d nRes`, where the continuation reads them. The temporaries of
    the assignment of a branch start `nRes` registers above the depth at its return, which
    is above the block: a branch may return at the depth `d` itself. -/
def ifFrame (fn : String) (d n nRes : Nat) (condOp : LOperand)
    (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat)
    (I : IsaData := x86Data) : List LinstrRM :=
  let res := carriedRegs d nRes
  flagWord I (regName d) (regName (d + 1)) condOp
  ++ ((I.zeroTripGuard (regName d) n (n + 1)).map guardI
  ++ (labelI n
  :: (thnC
  ++ (parMoves (thnD + nRes) res thnOps
  ++ (gotoI fn (n + 2)
  :: labelI (n + 1)
  :: (elsC
  ++ (parMoves (elsD + nRes) res elsOps
  ++ [labelI (n + 2)])))))))

/-! ## 3. The export -/

/-- The instruction of the binding `e` at depth `d`: the element the straight-line export
    `straightOpsMem` emits for it, writing `regName d`. -/
def bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : List LinstrRM :=
  straightOpsMem nArgs (Com.var e (Com.ret Ctxt.Var.here)) d

/-- The export of a program or region: its code, the operands of its returned variables,
    the depth at its return, and the next unused label. -/
structure Exported where
  /-- The typed linear code. -/
  code : List LinstrRM
  /-- The operands of the returned variables, in the order of the result types. -/
  res : List LOperand
  /-- The number of bindings in scope at the return. -/
  depth : Nat
  /-- The next unused label. -/
  next : Nat

/-- The export with the code `c` placed in front. -/
def Exported.prepend (c : List LinstrRM) (r : Exported) : Exported :=
  { r with code := c ++ r.code }

/-- **The export of a structured program by recursion over its regions.** `d` is the
    number of bindings in scope, `n` the first unused label, `nArgs` the number of
    arguments of the function and `fn` its name. A `call` is refused. -/
def exportR (nArgs : Nat) (fn : String) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
    (d n : Nat) → (I : IsaData := x86Data) → Option Exported
  | _, _, .ret vs, d, n, _ =>
      some ⟨[], exprArgsHV d nArgs argName (fun _ => none) vs, d, n⟩
  | _, _, .var e k, d, n, I =>
      (exportR nArgs fn k (d + 1) n I).map (Exported.prepend (bindOps nArgs e d))
  | _, _, .forLoop (cs := cs) count inits body k, d, n, I =>
      (exportR nArgs fn body (d + 1 + cs.length) (n + 2) I).bind fun b =>
      (exportR nArgs fn k (d + cs.length) b.next I).map
        (Exported.prepend
          (forFrame d n cs.length (exprArgsHV d nArgs argName (fun _ => none) inits)
            (resolveVar d nArgs argName (fun _ => none) count) b.code b.res b.depth I))
  | _, _, .ifThenElse (rs := rs) cond thn els k, d, n, I =>
      (exportR nArgs fn thn d (n + 3) I).bind fun t =>
      (exportR nArgs fn els d t.next I).bind fun e =>
      (exportR nArgs fn k (d + rs.length) e.next I).map
        (Exported.prepend
          (ifFrame fn d n rs.length (resolveVar d nArgs argName (fun _ => none) cond)
            t.code t.res t.depth e.code e.res e.depth I))
  | _, _, .whileLoop (cs := cs) inits body k, d, n, I =>
      (exportR nArgs fn body (d + cs.length) (n + 1) I).bind fun b =>
      (exportR nArgs fn k (d + cs.length) b.next I).map
        (Exported.prepend
          (whileFrame d n cs.length (exprArgsHV d nArgs argName (fun _ => none) inits)
            b.code (b.res.headD (.imm 0)) b.res.tail b.depth I))
  | _, _, .call _ _ _, _, _, _ => none

/-- The wire body of a program over the argument context `Γ`: the wire projection of its
    export from the depth `Γ.length` and the label `0`, followed by the return. -/
def exportRBody (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (I : IsaData := x86Data) : Option Lcmd :=
  (exportR Γ.length fn p Γ.length 0 I).map fun r =>
    r.code.map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]

/-- The virtual `lfundef` of a program over the argument context `Γ`, with the result
    registers read off the returned operands. -/
def exportRLfundef (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (I : IsaData := x86Data) : Option Lfundef :=
  (exportR Γ.length fn p Γ.length 0 I).map fun r =>
    { lfd_info := 0
      lfd_align := 1
      lfd_tyin := Γ.reverse.map tyWidth
      lfd_arg := (List.range Γ.length).map argName
      lfd_body := r.code.map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]
      lfd_tyout := ts.map tyWidth
      lfd_res := r.res.map operandName
      lfd_export := true
      lfd_callee_saved := []
      lfd_stk_max := 0
      lfd_frame_size := 0
      lfd_align_args := [] }

/-! ## 4. Labels and jump targets of a code -/

/-- The label an instruction declares. -/
def labelOf? : LinstrR → Option LLabel
  | .Llabel _ l => some l
  | _ => none

/-- The label a jump names. -/
def jumpTarget? : LinstrR → Option LLabel
  | .Lcond _ l => some l
  | .Lgoto (_, l) => some l
  | _ => none

/-- The labels a code declares, in order. -/
def labelsOf (code : List LinstrRM) : List LLabel := code.filterMap fun i => labelOf? i.1

/-- The labels the jumps of a code name, in order. -/
def targetsOf (code : List LinstrRM) : List LLabel := code.filterMap fun i => jumpTarget? i.1

@[simp] theorem labelsOf_nil : labelsOf [] = [] := rfl

@[simp] theorem targetsOf_nil : targetsOf [] = [] := rfl

@[simp] theorem labelsOf_append (xs ys : List LinstrRM) :
    labelsOf (xs ++ ys) = labelsOf xs ++ labelsOf ys := List.filterMap_append

@[simp] theorem targetsOf_append (xs ys : List LinstrRM) :
    targetsOf (xs ++ ys) = targetsOf xs ++ targetsOf ys := List.filterMap_append

theorem labelsOf_cons (x : LinstrRM) (xs : List LinstrRM) :
    labelsOf (x :: xs) = (labelOf? x.1).toList ++ labelsOf xs := by
  simp only [labelsOf, List.filterMap_cons]
  cases labelOf? x.1 <;> rfl

theorem targetsOf_cons (x : LinstrRM) (xs : List LinstrRM) :
    targetsOf (x :: xs) = (jumpTarget? x.1).toList ++ targetsOf xs := by
  simp only [targetsOf, List.filterMap_cons]
  cases jumpTarget? x.1 <;> rfl

/-- An instruction declares `l` exactly when `isLabel l` holds of it. -/
theorem isLabel_eq_true_iff (l : LLabel) (i : LinstrR) :
    isLabel l i = true ↔ labelOf? i = some l := by
  cases i with
  | Llabel k l' =>
      simp only [isLabel, labelOf?, beq_iff_eq, Option.some.injEq]
      exact eq_comm
  | _ => simp [isLabel, labelOf?]

/-- **`findLabelMem` fails exactly on the labels a code does not declare.** -/
theorem findLabelMem_eq_none_iff (l : LLabel) (code : List LinstrRM) :
    findLabelMem l code = none ↔ l ∉ labelsOf code := by
  simp only [findLabelMem, findLabel, List.findIdx?_eq_none_iff, List.mem_map, labelsOf,
    List.mem_filterMap, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_exists,
    not_and]
  refine forall₂_congr fun i _ => ?_
  rw [← isLabel_eq_true_iff]
  simp

/-- A code of `Lopn` instructions declares no label and has no jump. -/
theorem labelsOf_of_isLopn {xs : List LinstrRM} (h : ∀ i ∈ xs, IsLopn i) : labelsOf xs = [] := by
  simp only [labelsOf, List.filterMap_eq_nil_iff]
  intro i hi
  obtain ⟨d, o, s, hx⟩ := h i hi
  rw [hx]
  rfl

theorem targetsOf_of_isLopn {xs : List LinstrRM} (h : ∀ i ∈ xs, IsLopn i) :
    targetsOf xs = [] := by
  simp only [targetsOf, List.filterMap_eq_nil_iff]
  intro i hi
  obtain ⟨d, o, s, hx⟩ := h i hi
  rw [hx]
  rfl

theorem isLopn_movI (dst : String) (src : LOperand) : IsLopn (movI dst src) := ⟨_, _, _, rfl⟩

theorem isLopn_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    ∀ i ∈ parMoves D tgts ops, IsLopn i := by
  intro i hi
  simp only [parMoves, stageMoves, commitMoves, List.mem_append, List.mem_map] at hi
  rcases hi with ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ <;> exact isLopn_movI _ _

theorem isLopn_flagWord (I : IsaData) (r z : String) (op : LOperand) :
    ∀ i ∈ flagWord I r z op, IsLopn i := by
  intro i hi
  cases op with
  | reg f =>
      simp only [flagWord] at hi
      cases hm : I.selectMnemonic with
      | none => simp [hm] at hi
      | some m =>
          simp only [hm, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  | arr b k => simp only [flagWord, List.mem_singleton] at hi; subst hi; exact isLopn_movI _ _
  | imm v => simp only [flagWord, List.mem_singleton] at hi; subst hi; exact isLopn_movI _ _
  | arrIdx b k s =>
      simp only [flagWord, List.mem_singleton] at hi; subst hi; exact isLopn_movI _ _

theorem isLopn_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : ∀ i ∈ bindOps nArgs e d, IsLopn i :=
  JasminLsemMemSourceTie.straightOpsMem_isLopn _ nArgs d

/-! ## 5. Guards without labels -/

/-- The guards of an instruction set declare no label, and their jumps name only the labels
    they are given. -/
structure GuardsPlain (I : IsaData) : Prop where
  /-- The zero-trip guard declares no label. -/
  zeroTrip_labels : ∀ (c : String) (t e : LLabel),
    labelsOf ((I.zeroTripGuard c t e).map guardI) = []
  /-- The back-edge guard declares no label. -/
  loop_labels : ∀ (c : String) (t : LLabel), labelsOf ((I.loopGuard c t).map guardI) = []
  /-- The zero-trip guard jumps only to its two labels. -/
  zeroTrip_targets : ∀ (c : String) (t e : LLabel),
    ∀ l ∈ targetsOf ((I.zeroTripGuard c t e).map guardI), l = t ∨ l = e
  /-- The back-edge guard jumps only to its label. -/
  loop_targets : ∀ (c : String) (t : LLabel),
    ∀ l ∈ targetsOf ((I.loopGuard c t).map guardI), l = t

/-- The guards of x86 satisfy `GuardsPlain`. -/
theorem x86Data_guardsPlain : GuardsPlain x86Data where
  zeroTrip_labels c t e := by
    rw [x86Data_zeroTripGuard]; rfl
  loop_labels c t := by
    rw [x86Data_loopGuard]; rfl
  zeroTrip_targets c t e l hl := by
    rw [x86Data_zeroTripGuard] at hl
    simp [targetsOf, guardI, jumpTarget?] at hl
    exact Or.inr hl
  loop_targets c t l hl := by
    rw [x86Data_loopGuard] at hl
    simpa [targetsOf, guardI, jumpTarget?] using hl

/-! ## 6. Labels and jump targets of the frames -/

theorem isLopn_seedMoves (car : List String) (ops : List LOperand) :
    ∀ i ∈ seedMoves car ops, IsLopn i := fun i hi => by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hi
  exact isLopn_movI _ _

theorem isLopn_shiftMoves (d nCar : Nat) : ∀ i ∈ shiftMoves d nCar, IsLopn i := fun i hi => by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hi
  exact isLopn_movI _ _

theorem isLopn_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, IsLopn i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩

@[simp] theorem labelsOf_seedMoves (car : List String) (ops : List LOperand) :
    labelsOf (seedMoves car ops) = [] := labelsOf_of_isLopn (isLopn_seedMoves car ops)

@[simp] theorem targetsOf_seedMoves (car : List String) (ops : List LOperand) :
    targetsOf (seedMoves car ops) = [] := targetsOf_of_isLopn (isLopn_seedMoves car ops)

@[simp] theorem labelsOf_shiftMoves (d nCar : Nat) : labelsOf (shiftMoves d nCar) = [] :=
  labelsOf_of_isLopn (isLopn_shiftMoves d nCar)

@[simp] theorem targetsOf_shiftMoves (d nCar : Nat) : targetsOf (shiftMoves d nCar) = [] :=
  targetsOf_of_isLopn (isLopn_shiftMoves d nCar)

@[simp] theorem labelsOf_advanceOps (idx ctr : String) : labelsOf (advanceOps idx ctr) = [] :=
  labelsOf_of_isLopn (isLopn_advanceOps idx ctr)

@[simp] theorem targetsOf_advanceOps (idx ctr : String) :
    targetsOf (advanceOps idx ctr) = [] := targetsOf_of_isLopn (isLopn_advanceOps idx ctr)

@[simp] theorem labelsOf_cons_labelI (l : LLabel) (xs : List LinstrRM) :
    labelsOf (labelI l :: xs) = l :: labelsOf xs := rfl

@[simp] theorem targetsOf_cons_labelI (l : LLabel) (xs : List LinstrRM) :
    targetsOf (labelI l :: xs) = targetsOf xs := rfl

@[simp] theorem labelsOf_cons_gotoI (fn : String) (l : LLabel) (xs : List LinstrRM) :
    labelsOf (gotoI fn l :: xs) = labelsOf xs := rfl

@[simp] theorem targetsOf_cons_gotoI (fn : String) (l : LLabel) (xs : List LinstrRM) :
    targetsOf (gotoI fn l :: xs) = l :: targetsOf xs := rfl

@[simp] theorem labelsOf_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    labelsOf (parMoves D tgts ops) = [] := labelsOf_of_isLopn (isLopn_parMoves D tgts ops)

@[simp] theorem targetsOf_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    targetsOf (parMoves D tgts ops) = [] := targetsOf_of_isLopn (isLopn_parMoves D tgts ops)

@[simp] theorem labelsOf_flagWord (I : IsaData) (r z : String) (op : LOperand) :
    labelsOf (flagWord I r z op) = [] := labelsOf_of_isLopn (isLopn_flagWord I r z op)

@[simp] theorem targetsOf_flagWord (I : IsaData) (r z : String) (op : LOperand) :
    targetsOf (flagWord I r z op) = [] := targetsOf_of_isLopn (isLopn_flagWord I r z op)

@[simp] theorem labelsOf_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : labelsOf (bindOps nArgs e d) = [] :=
  labelsOf_of_isLopn (isLopn_bindOps nArgs e d)

@[simp] theorem targetsOf_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : targetsOf (bindOps nArgs e d) = [] :=
  targetsOf_of_isLopn (isLopn_bindOps nArgs e d)

/-- The counted frame declares its top label, the labels of the body and its exit label. -/
theorem labelsOf_forFrame {I : IsaData} (hI : GuardsPlain I) (d n nCar : Nat)
    (initOps : List LOperand) (countOp : LOperand) (bodyC : List LinstrRM)
    (bodyOps : List LOperand) (bodyD : Nat) :
    labelsOf (forFrame d n nCar initOps countOp bodyC bodyOps bodyD I)
      = n :: (labelsOf bodyC ++ [n + 1]) := by
  simp only [forFrame, labelsOf_append, labelsOf_seedMoves, hI.zeroTrip_labels,
    hI.loop_labels, labelsOf_cons_labelI, labelsOf_parMoves, labelsOf_advanceOps,
    labelsOf_shiftMoves, List.nil_append]

/-- The jumps of the counted frame name its two labels or are jumps of the body. -/
theorem targetsOf_forFrame {I : IsaData} (hI : GuardsPlain I) (d n nCar : Nat)
    (initOps : List LOperand) (countOp : LOperand) (bodyC : List LinstrRM)
    (bodyOps : List LOperand) (bodyD : Nat) :
    ∀ l ∈ targetsOf (forFrame d n nCar initOps countOp bodyC bodyOps bodyD I),
      l = n ∨ l = n + 1 ∨ l ∈ targetsOf bodyC := by
  intro l hl
  simp only [forFrame, targetsOf_append, targetsOf_seedMoves, targetsOf_parMoves,
    targetsOf_cons_labelI, targetsOf_advanceOps, targetsOf_shiftMoves, List.nil_append,
    List.append_nil, List.mem_append] at hl
  rcases hl with hl | hl | hl
  · exact (hI.zeroTrip_targets _ _ _ l hl).elim Or.inl fun h => Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hl)
  · exact Or.inl (hI.loop_targets _ _ l hl)

/-- The exit-flag frame declares its label and the labels of the body. -/
theorem labelsOf_whileFrame {I : IsaData} (hI : GuardsPlain I) (d n nCar : Nat)
    (initOps : List LOperand) (bodyC : List LinstrRM) (flagOp : LOperand)
    (bodyOps : List LOperand) (bodyD : Nat) :
    labelsOf (whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD I)
      = n :: labelsOf bodyC := by
  simp only [whileFrame, labelsOf_append, labelsOf_seedMoves, hI.loop_labels,
    labelsOf_cons_labelI, labelsOf_parMoves, labelsOf_flagWord, List.nil_append,
    List.append_nil]

/-- The jumps of the exit-flag frame name its label or are jumps of the body. -/
theorem targetsOf_whileFrame {I : IsaData} (hI : GuardsPlain I) (d n nCar : Nat)
    (initOps : List LOperand) (bodyC : List LinstrRM) (flagOp : LOperand)
    (bodyOps : List LOperand) (bodyD : Nat) :
    ∀ l ∈ targetsOf (whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD I),
      l = n ∨ l ∈ targetsOf bodyC := by
  intro l hl
  simp only [whileFrame, targetsOf_append, targetsOf_seedMoves, targetsOf_parMoves,
    targetsOf_flagWord, targetsOf_cons_labelI, List.nil_append, List.mem_append] at hl
  rcases hl with hl | hl
  · exact Or.inr hl
  · exact Or.inl (hI.loop_targets _ _ l hl)

/-- The branch frame declares its three labels and the labels of the two branches. -/
theorem labelsOf_ifFrame {I : IsaData} (hI : GuardsPlain I) (fn : String) (d n nRes : Nat)
    (condOp : LOperand) (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat) :
    labelsOf (ifFrame fn d n nRes condOp thnC thnOps thnD elsC elsOps elsD I)
      = n :: (labelsOf thnC ++ (n + 1) :: (labelsOf elsC ++ [n + 2])) := by
  simp only [ifFrame, labelsOf_append, hI.zeroTrip_labels, labelsOf_cons_labelI,
    labelsOf_cons_gotoI, labelsOf_parMoves, labelsOf_flagWord, labelsOf_nil,
    List.nil_append]

/-- The jumps of the branch frame name its three labels or are jumps of a branch. -/
theorem targetsOf_ifFrame {I : IsaData} (hI : GuardsPlain I) (fn : String) (d n nRes : Nat)
    (condOp : LOperand) (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat) :
    ∀ l ∈ targetsOf (ifFrame fn d n nRes condOp thnC thnOps thnD elsC elsOps elsD I),
      l = n ∨ l = n + 1 ∨ l = n + 2 ∨ l ∈ targetsOf thnC ∨ l ∈ targetsOf elsC := by
  intro l hl
  simp only [ifFrame, targetsOf_append, targetsOf_parMoves, targetsOf_flagWord,
    targetsOf_cons_labelI, targetsOf_cons_gotoI, targetsOf_nil, List.nil_append,
    List.append_nil, List.mem_append, List.mem_cons] at hl
  rcases hl with hl | hl | hl | hl
  · exact (hI.zeroTrip_targets _ _ _ l hl).elim Or.inl fun h => Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hl)))
  · exact Or.inr (Or.inr (Or.inl hl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hl)))

/-! ## 7. The labels of the export -/

/-- The label facts of an export from the counter `n`: the counter does not decrease, the
    declared labels lie between the two counters and are pairwise distinct, and every jump
    names a declared label. -/
structure LabelsOK (n : Nat) (r : Exported) : Prop where
  /-- The counter does not decrease. -/
  le : n ≤ r.next
  /-- The declared labels lie between the two counters. -/
  range : ∀ l : Nat, l ∈ labelsOf r.code → n ≤ l ∧ l < r.next
  /-- No label is declared twice. -/
  nodup : (labelsOf r.code).Nodup
  /-- Every jump names a declared label. -/
  closed : ∀ l ∈ targetsOf r.code, l ∈ labelsOf r.code

/-- **The label facts of the export.** -/
theorem exportR_labelsOK (nArgs : Nat) (fn : String) {I : IsaData} (hI : GuardsPlain I)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r → LabelsOK n r := by
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      exact ⟨le_rfl, by simp, by simp, by simp⟩
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      have := ih _ _ _ hk
      exact ⟨this.le, by simpa [Exported.prepend] using this.range,
        by simpa [Exported.prepend] using this.nodup,
        by simpa [Exported.prepend] using this.closed⟩
  | forLoop count inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hB := ihb _ _ _ hb
      have hK := ihk _ _ _ hk
      have hBle := hB.le
      have hKle := hK.le
      refine ⟨by simp only [Exported.prepend]; omega, ?_, ?_, ?_⟩
      · intro l hl
        simp only [Exported.prepend, labelsOf_append, labelsOf_forFrame hI, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with (rfl | hl | rfl) | hl
        · omega
        · have := hB.range l hl; omega
        · omega
        · have := hK.range l hl; omega
      · simp only [Exported.prepend, labelsOf_append, labelsOf_forFrame hI]
        refine List.Nodup.append ?_ hK.nodup ?_
        · rw [List.nodup_cons]
          refine ⟨?_, List.Nodup.append hB.nodup (List.nodup_singleton _) ?_⟩
          · intro hm
            rcases List.mem_append.mp hm with hm | hm
            · have := hB.range _ hm; omega
            · simp at hm
          · intro a ha ha'
            have := hB.range a ha
            obtain rfl := List.mem_singleton.mp ha'
            omega
        · intro a ha ha'
          have h2 := hK.range a ha'
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil,
            or_false] at ha
          rcases ha with rfl | ha | rfl
          · omega
          · have := hB.range a ha; omega
          · omega
      · intro l hl
        simp only [Exported.prepend, targetsOf_append, List.mem_append] at hl
        simp only [Exported.prepend, labelsOf_append, labelsOf_forFrame hI, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false]
        rcases hl with hl | hl
        · rcases targetsOf_forFrame hI _ _ _ _ _ _ _ _ l hl with rfl | rfl | hl
          · simp
          · simp
          · exact Or.inl (Or.inr (Or.inl (hB.closed l hl)))
        · exact Or.inr (hK.closed l hl)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      have hT := iht _ _ _ ht
      have hE := ihe _ _ _ he
      have hK := ihk _ _ _ hk
      have hTle := hT.le
      have hEle := hE.le
      have hKle := hK.le
      refine ⟨by simp only [Exported.prepend]; omega, ?_, ?_, ?_⟩
      · intro l hl
        simp only [Exported.prepend, labelsOf_append, labelsOf_ifFrame hI, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with (rfl | hl | rfl | hl | rfl) | hl
        · omega
        · have := hT.range l hl; omega
        · omega
        · have := hE.range l hl; omega
        · omega
        · have := hK.range l hl; omega
      · simp only [Exported.prepend, labelsOf_append, labelsOf_ifFrame hI]
        refine List.Nodup.append ?_ hK.nodup ?_
        · rw [List.nodup_cons]
          refine ⟨?_, List.Nodup.append hT.nodup ?_ ?_⟩
          · intro hm
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with hm | h1 | hm | h1
            · have := hT.range _ hm; omega
            · exact Nat.ne_of_lt (by omega) h1
            · have := hE.range _ hm; omega
            · exact Nat.ne_of_lt (by omega) h1
          · rw [List.nodup_cons]
            refine ⟨?_, List.Nodup.append hE.nodup (List.nodup_singleton _) ?_⟩
            · intro hm
              simp only [List.mem_append, List.mem_singleton] at hm
              rcases hm with hm | h1
              · have := hE.range _ hm; omega
              · exact Nat.ne_of_lt (by omega) h1
            · intro a ha ha'
              have := hE.range a ha
              obtain rfl := List.mem_singleton.mp ha'
              omega
          · intro a ha ha'
            have := hT.range a ha
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil,
              or_false] at ha'
            rcases ha' with rfl | ha' | rfl
            · omega
            · have := hE.range a ha'; omega
            · omega
        · intro a ha ha'
          have h2 := hK.range a ha'
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil,
            or_false] at ha
          rcases ha with rfl | ha | rfl | ha | rfl
          · omega
          · have := hT.range a ha; omega
          · omega
          · have := hE.range a ha; omega
          · omega
      · intro l hl
        simp only [Exported.prepend, targetsOf_append, List.mem_append] at hl
        simp only [Exported.prepend, labelsOf_append, labelsOf_ifFrame hI, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false]
        rcases hl with hl | hl
        · rcases targetsOf_ifFrame hI _ _ _ _ _ _ _ _ _ _ _ l hl with rfl | rfl | rfl | hl | hl
          · simp
          · simp
          · simp
          · exact Or.inl (Or.inr (Or.inl (hT.closed l hl)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (hE.closed l hl)))))
        · exact Or.inr (hK.closed l hl)
  | whileLoop inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hB := ihb _ _ _ hb
      have hK := ihk _ _ _ hk
      have hBle := hB.le
      have hKle := hK.le
      refine ⟨by simp only [Exported.prepend]; omega, ?_, ?_, ?_⟩
      · intro l hl
        simp only [Exported.prepend, labelsOf_append, labelsOf_whileFrame hI, List.mem_append,
          List.mem_cons] at hl ⊢
        rcases hl with (rfl | hl) | hl
        · omega
        · have := hB.range l hl; omega
        · have := hK.range l hl; omega
      · simp only [Exported.prepend, labelsOf_append, labelsOf_whileFrame hI]
        refine List.Nodup.append ?_ hK.nodup ?_
        · rw [List.nodup_cons]
          exact ⟨fun hm => by have := hB.range _ hm; omega, hB.nodup⟩
        · intro a ha ha'
          have h2 := hK.range a ha'
          rcases List.mem_cons.mp ha with rfl | ha
          · omega
          · have := hB.range a ha; omega
      · intro l hl
        simp only [Exported.prepend, targetsOf_append, List.mem_append] at hl
        simp only [Exported.prepend, labelsOf_append, labelsOf_whileFrame hI, List.mem_append,
          List.mem_cons]
        rcases hl with hl | hl
        · rcases targetsOf_whileFrame hI _ _ _ _ _ _ _ _ l hl with rfl | hl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr (hB.closed l hl))
        · exact Or.inr (hK.closed l hl)
  | call f args k _ =>
      intro d n r h
      simp [exportR] at h

/-- The counter does not decrease. -/
theorem exportR_next_le (nArgs : Nat) (fn : String) {I : IsaData} (hI : GuardsPlain I)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {d n : Nat} {r : Exported} (h : exportR nArgs fn p d n I = some r) : n ≤ r.next :=
  (exportR_labelsOK nArgs fn hI p d n r h).le

/-- **The labels of the export lie in its interval** `[n, r.next)`. -/
theorem exportR_labels_range (nArgs : Nat) (fn : String) {I : IsaData} (hI : GuardsPlain I)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {d n : Nat} {r : Exported} (h : exportR nArgs fn p d n I = some r) :
    ∀ l : Nat, l ∈ labelsOf r.code → n ≤ l ∧ l < r.next :=
  (exportR_labelsOK nArgs fn hI p d n r h).range

/-- **No label of the export is declared twice.** -/
theorem exportR_labels_nodup (nArgs : Nat) (fn : String) {I : IsaData} (hI : GuardsPlain I)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {d n : Nat} {r : Exported} (h : exportR nArgs fn p d n I = some r) :
    (labelsOf r.code).Nodup :=
  (exportR_labelsOK nArgs fn hI p d n r h).nodup

/-- **Every jump of the export names a label the export declares.** -/
theorem exportR_targets_declared (nArgs : Nat) (fn : String) {I : IsaData}
    (hI : GuardsPlain I) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (h : exportR nArgs fn p d n I = some r) :
    ∀ l ∈ targetsOf r.code, findLabelMem l r.code ≠ none := fun l hl =>
  fun hn => (findLabelMem_eq_none_iff l r.code).mp hn
    ((exportR_labelsOK nArgs fn hI p d n r h).closed l hl)

/-- **The export declares no label outside its interval.** -/
theorem exportR_findLabelMem_none (nArgs : Nat) (fn : String) {I : IsaData}
    (hI : GuardsPlain I) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (h : exportR nArgs fn p d n I = some r) (l : Nat) (hl : l < n ∨ r.next ≤ l) :
    findLabelMem l r.code = none :=
  (findLabelMem_eq_none_iff l r.code).mpr fun hm => by
    have := exportR_labels_range nArgs fn hI h l hm
    omega

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (straightOpsMem_plain
  scalarMemN_comOpsPlain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (loopCtr_ne_argName
  loopCtr_ne_regName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg

/-! ## 8. The frame of a region -/

/-- **The frame of a region** at depth `d` and label `n`: `s'` reads as `s` at every
    register and array name that is neither a register `regName k` with `d ≤ k` nor a
    counter `loopCtr l` with `n ≤ l`. -/
def RegionFrame (d n : Nat) (s s' : LstateM) : Prop :=
  (∀ (r : String) (w : Nat), (∀ k, d ≤ k → r ≠ regName k) → (∀ l, n ≤ l → r ≠ loopCtr l) →
      s'.reg.getW r w = s.reg.getW r w)
  ∧ (∀ (r : String) (w m : Nat), (∀ k, d ≤ k → r ≠ regName k) →
      (∀ l, n ≤ l → r ≠ loopCtr l) → s'.getArr r w m = s.getArr r w m)

theorem RegionFrame.refl (d n : Nat) (s : LstateM) : RegionFrame d n s s :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- A write frame of the straight-line export is a region frame at every label. -/
theorem RegionFrame.of_writeFrame {d : Nat} {s s' : LstateM} (n : Nat)
    (h : WriteFrame d s s') : RegionFrame d n s s' :=
  ⟨fun r w hr _ => h.1 r w hr, fun r w m hr _ => h.2 r w m hr⟩

/-- Region frames compose, at the smaller depth and label. -/
theorem RegionFrame.trans {d d' n n' : Nat} {s s1 s2 : LstateM} (h1 : RegionFrame d n s s1)
    (h2 : RegionFrame d' n' s1 s2) (hd : d ≤ d') (hn : n ≤ n') : RegionFrame d n s s2 :=
  ⟨fun r w hr hl => (h2.1 r w (fun k hk => hr k (by omega)) (fun l hl' => hl l (by omega))).trans
      (h1.1 r w hr hl),
    fun r w m hr hl =>
      (h2.2 r w m (fun k hk => hr k (by omega)) (fun l hl' => hl l (by omega))).trans
        (h1.2 r w m hr hl)⟩

/-- The flags an instruction writes are outside the frame. -/
theorem RegionFrame.withALUFlags {d n : Nat} {s s' : LstateM} (i : LinstrRM) (s0 : LstateM)
    (h : RegionFrame d n s s') : RegionFrame d n s (withALUFlags i s0 s') :=
  ⟨fun r w hr hl => by rw [withALUFlags_reg]; exact h.1 r w hr hl,
    fun r w m hr hl => by rw [getArr_withALUFlags]; exact h.2 r w m hr hl⟩

/-- The name of an in-scope variable is no loop counter. -/
theorem resolveVar_operandName_ne_loopCtr {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (v : Ctxt.Var Γ τ) (l : Nat) :
    operandName (resolveVar curDepth nArgs argName (fun _ => none) v) ≠ loopCtr l := by
  simp only [resolveVar, operandName]
  by_cases hsa : curDepth - 1 - varIndex v < nArgs
  · simp only [hsa, if_true]
    exact fun h => loopCtr_ne_argName l _ h.symm
  · simp only [hsa, if_false]
    exact fun h => loopCtr_ne_regName l _ h.symm

/-- **A region frame keeps the store agreement at its depth.** -/
theorem StoreAgreesM.of_regionFrame {nArgs d n : Nat} {Γ : Ctxt jasminDialect}
    {s s' : LstateM} {V : Ctxt.Valuation Γ} (hlen : Γ.length = d)
    (hagree : StoreAgreesM nArgs d s V) (hframe : RegionFrame d n s s') :
    StoreAgreesM nArgs d s' V := by
  refine ⟨?_, ?_⟩
  · intro w' v
    have hv : varIndex v < d := hlen ▸ JasminLsemSimulation.varIndex_lt v
    rw [evalOperandN_resolveVar, hframe.1 _ _
      (fun k hk => resolveVar_operandName_ne_regName v hv k hk)
      (fun l _ => resolveVar_operandName_ne_loopCtr v l),
      ← evalOperandN_resolveVar]
    exact hagree.reg v
  · intro w' n' v
    have hv : varIndex v < d := hlen ▸ JasminLsemSimulation.varIndex_lt v
    rw [hframe.2 _ _ _ (fun k hk => resolveVar_operandName_ne_regName v hv k hk)
      (fun l _ => resolveVar_operandName_ne_loopCtr v l)]
    exact hagree.arr v

/-- The store agreement reads the register file and the array carrier, which the flags of
    an instruction leave unchanged. -/
theorem StoreAgreesM.withALUFlags {nArgs d : Nat} {Γ : Ctxt jasminDialect} {s : LstateM}
    {V : Ctxt.Valuation Γ} (i : LinstrRM) (s0 : LstateM) (h : StoreAgreesM nArgs d s V) :
    StoreAgreesM nArgs d (withALUFlags i s0 s) V := by
  refine ⟨?_, ?_⟩
  · rw [withALUFlags_reg]; exact h.1
  · intro w n v; rw [getArr_withALUFlags]; exact h.2 v

/-! ## 9. The simulation statement -/

/-- The store `s` agrees with a valuation `W` at depth `D` under which `ops` are the
    operands of variables denoting `v`. -/
def ResAgrees (nArgs D : Nat) (s : LstateM) {ts : List JasminTy} (ops : List LOperand)
    (v : Ctxt.Valuation (d := jasminDialect) ts) : Prop :=
  ∃ (Δ : Ctxt jasminDialect) (W : Ctxt.Valuation Δ) (vs : HVector (fun t => Ctxt.Var Δ t) ts),
    Δ.length = D ∧ StoreAgreesM nArgs D s W
      ∧ ops = exprArgsHV D nArgs argName (fun _ => none) vs ∧ v = Expr.lookupArgs vs W

/-- The binding `e` is in the stack-memory fragment: the program that binds `e` and
    returns some register is a `ScalarMemN` program. -/
def BindMemN {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) : Prop :=
  ∃ (w : Nat) (v : Ctxt.Var (t :: Γ) (.reg w)), ScalarMemN (Com.var e (Com.ret v))

/-- **The simulation statement of the region export.** For every export of `p` at the
    depth of its context, placed in the body of `P` after a prefix that declares no label
    from the counter on: from a state at the first instruction whose store agrees with `V`,
    if `p` denotes `v` at `V` then a run of steps of `P` on the x86 flag machine reaches the
    counter after the code in a state that agrees with the returned operands at `v` and
    differs from the entry state within the frame of the region. -/
def ExportRSim (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : Prop :=
  ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n = some r → Γ.length = d → nArgs ≤ d →
  ∀ (P : LprogM) (pre post : List LinstrRM), P.lfn = fn → P.body = pre ++ r.code ++ post →
    (∀ l, n ≤ l → findLabelMem l pre = none) →
  ∀ (fuel : Nat) (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (m : LstateMF),
    p.denote fuel V = some v → atPc P pre.length m → StoreAgreesM nArgs d m.prog.base V →
    ∃ (k : Nat) (m' : LstateMF), Steps x86Isa P k m m'
      ∧ atPc P (pre.length + r.code.length) m'
      ∧ ResAgrees nArgs r.depth m'.prog.base r.res v
      ∧ RegionFrame d n m.prog.base m'.prog.base

/-! ## 10. The return and the binding -/

/-- **The statement for a return.** The code is empty and the returned operands are the
    returned variables at the entry valuation. -/
theorem exportRSim_ret (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts) :
    ExportRSim nArgs fn (NFProg.ret (d := jasminDialect) vs) := by
  intro d n r h hlen _ P pre post _ _ _ fuel V v m hden hat hag
  simp only [exportR, Option.some.injEq] at h
  subst h
  rw [NFProg.denote_ret, Option.some.injEq] at hden
  exact ⟨0, m, Steps.refl x86Isa P m, by simpa using hat,
    ⟨Γ, V, vs, hlen, hag, rfl, hden.symm⟩, RegionFrame.refl d n _⟩

/-- The code of a binding is one instruction. -/
theorem bindOps_eq_singleton (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : ∃ i, bindOps nArgs e d = [i] :=
  ⟨_, rfl⟩

/-- **The frame rule of a binding.** The statement for the continuation gives the
    statement for a binding of the fragment in front of it. -/
theorem exportRSim_var (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {ts : List JasminTy} (e : Expr jasminDialect Γ t)
    (k : NFProg jasminDialect (t :: Γ) ts) (he : BindMemN e)
    (hk : ExportRSim nArgs fn k) : ExportRSim nArgs fn (NFProg.var e k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V v m hden hat hag
  simp only [exportR, Option.map_eq_some_iff] at h
  obtain ⟨rk, hrk, rfl⟩ := h
  simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
    Option.bind_some] at hden
  obtain ⟨w, v0, hmem⟩ := he
  obtain ⟨st', hrun, hAg, hFr⟩ :=
    lsemStraightMem_straightOps_store (nArgs := nArgs) hmem hlen harg hag
  have hplain : PlainLopnBody (bindOps nArgs e d) :=
    straightOpsMem_plain nArgs _ (scalarMemN_comOpsPlain hmem) d
  obtain ⟨i, hi⟩ := bindOps_eq_singleton nArgs e d
  have hrun' : lsemStraightMem [i] m.prog.base = some st' := hi ▸ hrun
  have hstep : lsemStepMem i m.prog.base = some st' := by
    rw [lsemStraightMem_cons] at hrun'
    cases hs : lsemStepMem i m.prog.base with
    | none => rw [hs] at hrun'; cases hrun'
    | some b => rw [hs] at hrun'; exact hrun'
  obtain ⟨hl, hc, hm⟩ := hplain i (by rw [hi]; exact List.mem_singleton_self i)
  have hcode : (Exported.prepend (bindOps nArgs e d) rk).code = i :: rk.code := by
    simp only [Exported.prepend, hi, List.singleton_append]
  rw [hcode] at hbody
  have hfetch : P.body[pre.length]? = some i := by
    rw [hbody, List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  obtain ⟨hs1, hat1⟩ := x86_steps_mem hat hfetch hl hc hm hstep
  have hAg' : StoreAgreesM nArgs (d + 1) st' (V.extend (e.denote V)) := hAg
  have hlab : ∀ l, n ≤ l → findLabelMem l (pre ++ [i]) = none := by
    intro l hl'
    rw [findLabelMem_eq_none_iff, labelsOf_append,
      labelsOf_of_isLopn (xs := [i]) (fun j hj => by
        rw [List.mem_singleton.mp hj]; exact hl),
      List.append_nil, ← findLabelMem_eq_none_iff]
    exact hpre l hl'
  obtain ⟨k', m', hs2, hat2, hres, hfr2⟩ := hk (d + 1) n rk hrk
    (by rw [List.length_cons, hlen]) (by omega) P (pre ++ [i]) post hfn
    (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hlab
    fuel _ v (setBase m (withALUFlags i m.prog.base st')) hden
    (by rw [List.length_append, List.length_singleton]; exact hat1)
    (StoreAgreesM.withALUFlags i m.prog.base hAg')
  refine ⟨1 + k', m', hs1.trans hs2, ?_, hres, ?_⟩
  · rw [hcode, List.length_cons]
    rw [List.length_append, List.length_singleton] at hat2
    rwa [show pre.length + (rk.code.length + 1) = pre.length + 1 + rk.code.length by omega]
  · exact ((RegionFrame.of_writeFrame n hFr).withALUFlags i _).trans hfr2 (by omega) le_rfl

/-! ## 11. Returns under bindings -/

/-- A return under bindings of the stack-memory fragment. -/
inductive StraightMemN : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Prop where
  /-- A return. -/
  | ret {Γ ts} (vs : HVector (fun t => Ctxt.Var Γ t) ts) :
      StraightMemN (NFProg.ret (d := jasminDialect) vs)
  /-- A binding of the fragment in front of a straight program. -/
  | var {Γ t ts} (e : Expr jasminDialect Γ t) {k : NFProg jasminDialect (t :: Γ) ts}
      (he : BindMemN e) (hk : StraightMemN k) : StraightMemN (NFProg.var e k)

/-- **The simulation of a return under bindings** of the stack-memory fragment. -/
theorem exportR_sim_straight (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : StraightMemN p) :
    ExportRSim nArgs fn p := by
  induction hp with
  | ret vs => exact exportRSim_ret nArgs fn vs
  | var e he _ ih => exact exportRSim_var nArgs fn e _ he ih

/-! ## 12. Register cells and the steps of the frame instructions -/

/-- A state with the array carrier of `s` whose register cells are those of `s` outside
    the registers `regName k`, `d ≤ k`, and the counters `loopCtr l`, `n ≤ l`, is within the
    frame of the region. -/
theorem RegionFrame.of_cells {d n : Nat} {s s' : LstateM} (harr : s'.larr = s.larr)
    (hreg : ∀ r, (∀ k, d ≤ k → r ≠ regName k) → (∀ l, n ≤ l → r ≠ loopCtr l) →
      s'.reg.lvm r = s.reg.lvm r) : RegionFrame d n s s' :=
  ⟨fun r w hr hl => getW_congr w (hreg r hr hl),
    fun r w m _ _ => by unfold LstateM.getArr; rw [harr]⟩

/-- A region frame keeps the register cells outside its registers and counters. -/
theorem RegionFrame.lvm_eq {d n : Nat} {s s' : LstateM} (h : RegionFrame d n s s') (r : String)
    (hr : ∀ k, d ≤ k → r ≠ regName k) (hl : ∀ l, n ≤ l → r ≠ loopCtr l) :
    s'.reg.lvm r = s.reg.lvm r := by
  have := h.1 r (s.reg.lvm r).1 hr hl
  rw [getW_of_lvm s.reg r (s.reg.lvm r).2 rfl] at this
  exact getW_eq_some_iff.mp this

/-- A region frame at a larger depth and label is a region frame at a smaller one. -/
theorem RegionFrame.mono {d d' n n' : Nat} {s s' : LstateM} (h : RegionFrame d' n' s s')
    (hd : d ≤ d') (hn : n ≤ n') : RegionFrame d n s s' :=
  (RegionFrame.refl d n s).trans h hd hn

/-- **A register copy** `MOV dst, src` is one step that writes the cell of `src` to `dst`. -/
theorem steps_movReg {P : LprogM} {k : Nat} {s : LstateMF} {dst src : String}
    (hat : atPc P k s) (hi : P.body[k]? = some (movI dst (.reg src))) :
    ∃ t, Steps x86Isa P 1 s t ∧ atPc P (k + 1) t ∧ t.prog.base.larr = s.prog.base.larr
      ∧ ∀ r, t.prog.base.reg.lvm r
          = if r = dst then s.prog.base.reg.lvm src else s.prog.base.reg.lvm r := by
  refine ⟨setBase s (s.prog.base.setReg dst (s.prog.base.reg.lvm src).2).nextPc,
    Steps.one ?_, ⟨hat.1, ?_⟩, rfl, fun r => ?_⟩
  · rw [lsemStepPMemF_of_atPc x86Isa hat hi, X86Backend.X86Isa.x86Isa_step, movI,
      JasminLsemExportRewrites.evalInstrPMemF_movReg]
    rfl
  · rw [setBase_base, JasminLsemMemLoop.LstateM.lpc_nextPc]
    exact congrArg (· + 1) hat.2
  · simp only [setBase_base, LstateM.nextPc, LstateM.setReg, LstateN.lvm_nextPc,
      LstateN.lvm_setReg]

/-- **An `Lopn` step that writes one register.** At counter `k` holding an `Lopn`
    instruction `i` that is neither the flag compare nor a register copy and that
    `lsemStepMem` steps to the write of `v` to `dst`, one step writes the cell of `v` to
    `dst`. -/
theorem steps_setReg {P : LprogM} {k : Nat} {s : LstateMF} {i : LinstrRM} {dst : String}
    {w : Nat} (v : BitVec w) (hat : atPc P k s) (hi : P.body[k]? = some i) (hl : IsLopn i)
    (hc : cmpArgs? i = none) (hm : movRegArgs? i = none)
    (h : lsemStepMem i s.prog.base = some (s.prog.base.setReg dst v).nextPc) :
    ∃ t, Steps x86Isa P 1 s t ∧ atPc P (k + 1) t ∧ t.prog.base.larr = s.prog.base.larr
      ∧ ∀ r, t.prog.base.reg.lvm r = if r = dst then ⟨w, v⟩ else s.prog.base.reg.lvm r := by
  obtain ⟨hs, hat'⟩ := x86_steps_mem hat hi hl hc hm h
  refine ⟨_, hs, hat', ?_, fun r => ?_⟩
  · rw [setBase_base, withALUFlags_larr]
    rfl
  · rw [setBase_base, withALUFlags_reg]
    simp only [LstateM.nextPc, LstateM.setReg, LstateN.lvm_nextPc, LstateN.lvm_setReg]

/-- **The move of an immediate** `MOV dst, #c` is one step that writes `c` at width `64`. -/
theorem steps_movImm {P : LprogM} {k : Nat} {s : LstateMF} {dst : String} {c : Nat}
    (hat : atPc P k s) (hi : P.body[k]? = some (movImmI dst c)) :
    ∃ t, Steps x86Isa P 1 s t ∧ atPc P (k + 1) t ∧ t.prog.base.larr = s.prog.base.larr
      ∧ ∀ r, t.prog.base.reg.lvm r
          = if r = dst then ⟨64, BitVec.ofNat 64 c⟩ else s.prog.base.reg.lvm r :=
  steps_setReg (BitVec.ofNat 64 c) hat hi ⟨_, _, _, rfl⟩ rfl rfl
    (Ascent.IsaCfg.lsemStepMem_movI dst c s.prog.base)

/-- **The increment of the trip index** `ADD dst, a, #c` is one step. -/
theorem steps_addImm {P : LprogM} {k : Nat} {s : LstateMF} {dst a : String} {c : Nat}
    {va : BitVec 64} (hat : atPc P k s)
    (hi : P.body[k]? = some (.Lopn [.reg dst] (withWidthTag 64 "ADD") [.reg a, .imm c],
      .reg none))
    (ha : s.prog.base.reg.lvm a = ⟨64, va⟩) :
    ∃ t, Steps x86Isa P 1 s t ∧ atPc P (k + 1) t ∧ t.prog.base.larr = s.prog.base.larr
      ∧ ∀ r, t.prog.base.reg.lvm r
          = if r = dst then ⟨64, va + BitVec.ofNat 64 c⟩ else s.prog.base.reg.lvm r :=
  steps_setReg (va + BitVec.ofNat 64 c) hat hi ⟨_, _, _, rfl⟩
    (by unfold cmpArgs?; exact if_neg (by decide)) rfl
    (lsemStepMem_addI dst a c s.prog.base va ha)

/-- **The decrement of the counter** `SUB dst, a, #c` is one step. -/
theorem steps_subImm {P : LprogM} {k : Nat} {s : LstateMF} {dst a : String} {c : Nat}
    {va : BitVec 64} (hat : atPc P k s)
    (hi : P.body[k]? = some (.Lopn [.reg dst] (withWidthTag 64 "SUB") [.reg a, .imm c],
      .reg none))
    (ha : s.prog.base.reg.lvm a = ⟨64, va⟩) :
    ∃ t, Steps x86Isa P 1 s t ∧ atPc P (k + 1) t ∧ t.prog.base.larr = s.prog.base.larr
      ∧ ∀ r, t.prog.base.reg.lvm r
          = if r = dst then ⟨64, va - BitVec.ofNat 64 c⟩ else s.prog.base.reg.lvm r :=
  steps_setReg (va - BitVec.ofNat 64 c) hat hi ⟨_, _, _, rfl⟩
    (by unfold cmpArgs?; exact if_neg (by decide)) rfl
    (lsemStepMem_subI dst a c s.prog.base va ha)

/-- **The compare with zero** `CMP r, #0` is one step that sets the zero flag to the test
    of the register against zero and keeps the store. -/
theorem steps_cmpZero {P : LprogM} {k : Nat} {s : LstateMF} {r : String} {v : BitVec 64}
    (hat : atPc P k s)
    (hi : P.body[k]? = some (guardI (.Lopn [.reg r] (withWidthTag 64 "CMP") [.reg r, .imm 0])))
    (hv : s.prog.base.reg.lvm r = ⟨64, v⟩) :
    ∃ t, Steps x86Isa P 1 s t ∧ atPc P (k + 1) t ∧ t.prog.base.larr = s.prog.base.larr
      ∧ t.prog.base.reg.lvm = s.prog.base.reg.lvm ∧ t.zf = (v == 0#64) := by
  refine ⟨{ prog := { s.prog with base := s.prog.base.nextPc }, zf := v == 0#64 },
    Steps.one ?_, ⟨hat.1, ?_⟩, rfl, rfl, rfl⟩
  · rw [lsemStepPMemF_of_atPc x86Isa hat hi, X86Backend.X86Isa.x86Isa_step, guardI,
      evalInstrPMemF_cmp P _ r _ s v (getW_of_lvm _ r v hv)]
  · rw [JasminLsemMemLoop.LstateM.lpc_nextPc]
    exact congrArg (· + 1) hat.2

/-- **A conditional jump on a condition code**, taken: one step to the counter after the
    label. `pol` is the value of the zero flag on which the jump is taken. -/
theorem steps_cc_taken {P : LprogM} {k q : Nat} {s : LstateMF} {cc : String} {l : LLabel}
    {pol : Bool} (hcc : flagCondCC? (condI (.reg cc) l) = some (pol, l)) (hat : atPc P k s)
    (hi : P.body[k]? = some (condI (.reg cc) l)) (hz : s.zf = pol)
    (hl : findLabelMem l P.body = some q) :
    Steps x86Isa P 1 s (goto s (q + 1)) ∧ atPc P (q + 1) (goto s (q + 1)) := by
  refine ⟨Steps.one ?_, atPc_goto (q + 1) hat⟩
  rw [lsemStepPMemF_of_atPc x86Isa hat hi, X86Backend.X86Isa.x86Isa_step]
  unfold evalInstrPMemF
  rw [show cmpArgs? (condI (.reg cc) l) = none from rfl,
    show movRegArgs? (condI (.reg cc) l) = none from rfl, hcc]
  simp only [if_pos hz]
  exact evalJumpMem_of_findLabelMem hl s

/-- **A conditional jump on a condition code**, not taken: one step to the next counter. -/
theorem steps_cc_fall {P : LprogM} {k : Nat} {s : LstateMF} {cc : String} {l : LLabel}
    {pol : Bool} (hcc : flagCondCC? (condI (.reg cc) l) = some (pol, l)) (hat : atPc P k s)
    (hi : P.body[k]? = some (condI (.reg cc) l)) (hz : s.zf ≠ pol) :
    Steps x86Isa P 1 s (next s) ∧ atPc P (k + 1) (next s) := by
  refine ⟨Steps.one ?_, atPc_next hat⟩
  rw [lsemStepPMemF_of_atPc x86Isa hat hi, X86Backend.X86Isa.x86Isa_step]
  unfold evalInstrPMemF
  rw [show cmpArgs? (condI (.reg cc) l) = none from rfl,
    show movRegArgs? (condI (.reg cc) l) = none from rfl, hcc]
  simp only [if_neg hz]
  rfl

/-- **Register copies as an assignment.** The copies `MOV T j, S j` for `j < m`, with
    pairwise distinct targets and no source that is the target of an earlier copy, write at
    each target the cell its source held before the run and keep every other cell and the
    array carrier. -/
theorem steps_moves (P : LprogM) (T S : Nat → String) :
    ∀ (m : Nat) (pre post : List LinstrRM) (s : LstateMF),
      P.body = pre ++ (List.range m).map (fun j => movI (T j) (.reg (S j))) ++ post →
      atPc P pre.length s → (∀ i j, i < j → j < m → T i ≠ T j) →
      (∀ i j, i < j → j < m → S j ≠ T i) →
      ∃ t, Steps x86Isa P m s t ∧ atPc P (pre.length + m) t
        ∧ t.prog.base.larr = s.prog.base.larr
        ∧ (∀ j, j < m → t.prog.base.reg.lvm (T j) = s.prog.base.reg.lvm (S j))
        ∧ (∀ r, (∀ j, j < m → r ≠ T j) → t.prog.base.reg.lvm r = s.prog.base.reg.lvm r) := by
  intro m
  induction m with
  | zero =>
      intro pre post s _ hat _ _
      exact ⟨s, Steps.refl x86Isa P s, hat, rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
        fun _ _ => rfl⟩
  | succ m ih =>
      intro pre post s hbody hat hT hS
      rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc,
        List.append_assoc] at hbody
      obtain ⟨t, hs, hat1, harr, hmov, hoth⟩ := ih pre _ s
        (by rw [hbody, List.append_assoc]) hat
        (fun i j hij hj => hT i j hij (by omega)) (fun i j hij hj => hS i j hij (by omega))
      have hfetch : P.body[pre.length + m]? = some (movI (T m) (.reg (S m))) := by
        rw [hbody, List.getElem?_append_right (by omega),
          List.getElem?_append_right (by simp)]
        simp
      obtain ⟨t', hs', hat2, harr', hcell⟩ := steps_movReg hat1 hfetch
      refine ⟨t', hs.trans hs', hat2, harr'.trans harr, fun j hj => ?_, fun r hr => ?_⟩
      · rw [hcell]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
        · rw [if_neg (hT j m hj' (Nat.lt_succ_self m)), hmov j hj']
        · rw [if_pos rfl]
          exact hoth _ fun i hi => hS i j hi (Nat.lt_succ_self j)
      · rw [hcell, if_neg (hr m (Nat.lt_succ_self m))]
        exact hoth r fun j hj => hr j (by omega)

/-! ## 13. The moves of a frame as copies by index -/

open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend inlHom inrHom hvToHom
  lookup_inlHom lookup_inrHom)

/-- A variable of an appended context is the left or the right injection of a variable. -/
theorem var_append_cases {xs ys : Ctxt jasminDialect} {t : JasminTy} :
    ∀ v : Ctxt.Var (xs ++ ys) t,
      (∃ u : Ctxt.Var xs t, v = inlHom ys u) ∨ (∃ u : Ctxt.Var ys t, v = inrHom xs u) := by
  induction xs with
  | nil => intro v; exact Or.inr ⟨v, rfl⟩
  | cons x xs ih =>
      intro v
      cases v with
      | here => exact Or.inl ⟨.here, rfl⟩
      | there v =>
          rcases ih v with ⟨u, rfl⟩ | ⟨u, rfl⟩
          · exact Or.inl ⟨.there u, rfl⟩
          · exact Or.inr ⟨u, rfl⟩

theorem varIndex_inlHom {xs : Ctxt jasminDialect} (ys : Ctxt jasminDialect) {t : JasminTy} :
    ∀ u : Ctxt.Var xs t, varIndex (inlHom ys u) = varIndex u
  | .here => rfl
  | .there u => congrArg (· + 1) (varIndex_inlHom ys u)

theorem varIndex_inrHom : ∀ (xs : Ctxt jasminDialect) {ys : Ctxt jasminDialect} {t : JasminTy}
    (u : Ctxt.Var ys t), varIndex (inrHom xs u) = xs.length + varIndex u
  | [], _, _, u => by simp [inrHom]
  | _ :: xs, _, _, u => by
      show varIndex (inrHom xs u) + 1 = _
      rw [varIndex_inrHom xs u, List.length_cons]
      omega

/-- The type of a variable is a member of its context. -/
theorem var_mem {Γ : Ctxt jasminDialect} {t : JasminTy} : Ctxt.Var Γ t → t ∈ Γ
  | .here => List.mem_cons_self
  | .there v => List.mem_cons_of_mem _ (var_mem v)

/-- The operand list of a variable vector at the position of a variable of its type list. -/
theorem exprArgsHV_getD {Γ : Ctxt jasminDialect} (cd nArgs : Nat) :
    ∀ {ts : List JasminTy} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts) {t : JasminTy}
      (u : Ctxt.Var ts t),
      (exprArgsHV cd nArgs argName (fun _ => none) vs).getD (varIndex u) (.imm 0)
        = resolveVar cd nArgs argName (fun _ => none) (hvToHom vs u)
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ rest, _, .there u => by
      show (exprArgsHV cd nArgs argName (fun _ => none) rest).getD (varIndex u) (.imm 0) = _
      exact exprArgsHV_getD cd nArgs rest u

theorem carriedRegs_length (d nCar : Nat) : (carriedRegs d nCar).length = nCar := by
  simp [carriedRegs]

theorem carriedRegs_getD (d nCar j : Nat) (hj : j < nCar) :
    (carriedRegs d nCar).getD j "" = regName (d + (nCar - 1 - j)) := by
  simp [carriedRegs, List.getD_eq_getElem?_getD, hj]

/-- The seeds of register operands are the copies of the operand names by index. -/
theorem seedMoves_eq_range (car : List String) (ops : List LOperand)
    (hlen : ops.length = car.length) (hreg : ∀ o ∈ ops, o = .reg (operandName o)) :
    seedMoves car ops = (List.range car.length).map fun j =>
      movI (car.getD j "") (.reg (operandName (ops.getD j (.imm 0)))) := by
  apply List.ext_getElem
  · simp [seedMoves, hlen]
  · intro j h1 h2
    simp only [List.length_map, List.length_range] at h2
    have hj : j < ops.length := by omega
    simp only [seedMoves, List.getElem_map, List.getElem_zip, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, List.getElem?_eq_getElem hj,
      Option.getD_some]
    rw [← hreg _ (List.getElem_mem hj)]

/-- The first stage of a parallel assignment of register operands, by index. -/
theorem stageMoves_eq_range (D : Nat) (ops : List LOperand)
    (hreg : ∀ o ∈ ops, o = .reg (operandName o)) :
    stageMoves D ops = (List.range ops.length).map fun j =>
      movI (regName (D + j)) (.reg (operandName (ops.getD j (.imm 0)))) := by
  apply List.ext_getElem
  · simp [stageMoves]
  · intro j h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [stageMoves, List.getElem_map, List.getElem_zipIdx, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some, Nat.zero_add]
    rw [← hreg _ (List.getElem_mem h2)]

/-- The second stage of a parallel assignment, by index. -/
theorem commitMoves_eq_range (D : Nat) (tgts : List String) :
    commitMoves D tgts = (List.range tgts.length).map fun j =>
      movI (tgts.getD j "") (.reg (regName (D + j))) := by
  apply List.ext_getElem
  · simp [commitMoves]
  · intro j h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [commitMoves, List.getElem_map, List.getElem_zipIdx, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some, Nat.zero_add]

theorem exprArgsHV_length {Γ : Ctxt jasminDialect} (cd nArgs : Nat) :
    ∀ {ts : List JasminTy} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts),
      (exprArgsHV cd nArgs argName (fun _ => none) vs).length = ts.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (· + 1) (exprArgsHV_length cd nArgs rest)

/-- The operands of in-scope variables are registers below the depth. -/
theorem exprArgsHV_reg {Γ : Ctxt jasminDialect} {cd : Nat} (nArgs : Nat) (hlen : Γ.length = cd) :
    ∀ {ts : List JasminTy} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts),
      ∀ o ∈ exprArgsHV cd nArgs argName (fun _ => none) vs,
        o = .reg (operandName o) ∧ ∀ k, cd ≤ k → operandName o ≠ regName k
  | [], .nil, o, h => by simp [exprArgsHV] at h
  | _ :: _, .cons v rest, o, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨resolveVar_isReg v, fun k hk =>
          resolveVar_operandName_ne_regName v (hlen ▸ JasminLsemSimulation.varIndex_lt v) k hk⟩
      · exact exprArgsHV_reg nArgs hlen rest o h'

/-- Looking up a position of a vector of looked-up variables is looking up the variable at
    that position. -/
theorem lookup_lookupArgs {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    ∀ {ts : List JasminTy} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts) {t : JasminTy}
      (u : Ctxt.Var ts t), u.lookup (Expr.lookupArgs vs V) = (hvToHom vs u).lookup V
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ rest, _, .there u => lookup_lookupArgs V rest u

/-- A type held in a register cell: every type other than a stack array. The store
    agreement constrains the register cell of a `reg` variable and the array carrier of a
    `stackArr` variable; the copies of a frame move register cells only. -/
def isRegTy : JasminTy → Bool
  | .stackArr _ _ => false
  | _ => true

/-- Every type of the list is held in a register cell. -/
def RegTys (cs : List JasminTy) : Prop := ∀ t ∈ cs, isRegTy t = true

instance (cs : List JasminTy) : Decidable (RegTys cs) :=
  inferInstanceAs (Decidable (∀ t ∈ cs, isRegTy t = true))

/-- **The agreement under a block of binders.** A state that agrees with `V` at depth `D`
    and reads the tuple `acc` of register types at the block of `cs.length` registers from
    `regName D`, in the order of `carriedRegs`, agrees with `acc` appended to `V` at depth
    `D + cs.length`. -/
theorem storeAgreesM_append {nArgs D : Nat} {Γ cs : Ctxt jasminDialect} (hcs : RegTys cs)
    {s : LstateM} {V : Ctxt.Valuation Γ} {acc : Ctxt.Valuation cs} (harg : nArgs ≤ D)
    (hag : StoreAgreesM nArgs D s V)
    (hblk : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      s.reg.getW (regName (D + (cs.length - 1 - varIndex u))) w = some (u.lookup acc)) :
    StoreAgreesM nArgs (D + cs.length) s (hvAppend acc V) := by
  have hres : ∀ {t : JasminTy} (u : Ctxt.Var Γ t),
      resolveVar (D + cs.length) nArgs argName (fun _ => none) (inrHom cs u)
        = resolveVar D nArgs argName (fun _ => none) u := by
    intro t u
    simp only [resolveVar, varIndex_inrHom]
    rw [show D + cs.length - 1 - (cs.length + varIndex u) = D - 1 - varIndex u by omega]
  refine ⟨fun {w} v => ?_, fun {w n} v => ?_⟩
  · rcases var_append_cases v with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rw [lookup_inlHom]
      have hu := JasminLsemSimulation.varIndex_lt u
      simp only [resolveVar, varIndex_inlHom]
      rw [if_neg (by omega), evalOperandN,
        show D + cs.length - 1 - varIndex u = D + (cs.length - 1 - varIndex u) by omega]
      exact hblk u
    · rw [lookup_inrHom, hres]
      exact hag.1 u
  · rcases var_append_cases v with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact absurd (hcs _ (var_mem u)) (by simp [isRegTy])
    · rw [lookup_inrHom, hres]
      exact hag.2 u

/-- The label `l` declared after a code that does not declare it is found at the length
    of that code. -/
theorem findLabelMem_append_labelI (l : LLabel) (xs ys : List LinstrRM)
    (h : l ∉ labelsOf xs) : findLabelMem l (xs ++ labelI l :: ys) = some xs.length := by
  induction xs with
  | nil =>
      unfold findLabelMem findLabel
      simp [labelI, List.findIdx?_cons, isLabel]
  | cons x xs ih =>
      rw [labelsOf_cons, List.mem_append, not_or] at h
      have hx : isLabel l x.1 = false := by
        rw [← Bool.not_eq_true, isLabel_eq_true_iff]
        intro he
        exact h.1 (by rw [he]; simp)
      have ih' := ih h.2
      unfold findLabelMem findLabel at ih' ⊢
      rw [List.cons_append, List.map_cons, List.findIdx?_cons, hx]
      simp only [Bool.false_eq_true, if_false]
      rw [ih']
      simp

/-- The depth at the return of an export is at least the depth at its entry. -/
theorem exportR_depth_le (nArgs : Nat) (fn : String) {I : IsaData} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r → d ≤ r.depth := by
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      exact le_rfl
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      have := ih _ _ _ hk
      simp only [Exported.prepend]
      omega
  | forLoop count inits body k _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, _, rk, hk, rfl⟩ := h
      have := ihk _ _ _ hk
      simp only [Exported.prepend]
      omega
  | ifThenElse cond thn els k _ _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, _, e, _, rk, hk, rfl⟩ := h
      have := ihk _ _ _ hk
      simp only [Exported.prepend]
      omega
  | whileLoop inits body k _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, _, rk, hk, rfl⟩ := h
      have := ihk _ _ _ hk
      simp only [Exported.prepend]
      omega
  | call f args k _ =>
      intro d n r h
      simp [exportR] at h

/-! ## 14. The parallel assignment and the tail of a counted trip -/

/-- The instruction at the length of a prefix of the body. -/
theorem fetch_of_body {P : LprogM} {xs ys : List LinstrRM} {i : LinstrRM} {k : Nat}
    (hb : P.body = xs ++ i :: ys) (hk : xs.length = k) : P.body[k]? = some i := by
  subst hk
  rw [hb]
  simp

theorem mem_carriedRegs {d nCar : Nat} {r : String} :
    r ∈ carriedRegs d nCar ↔ ∃ j, j < nCar ∧ r = regName (d + (nCar - 1 - j)) := by
  simp only [carriedRegs, List.mem_map, List.mem_range]
  exact ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩, fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩⟩

theorem carriedRegs_nodup (d nCar : Nat) : (carriedRegs d nCar).Nodup := by
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
  have := JasminLsemSimulation.regName_injective hab
  rw [List.mem_range] at ha hb
  omega

/-- A carried register of a block from `regName d` is no register `regName k` above the
    block. -/
theorem carriedRegs_ne_regName {d nCar : Nat} {r : String} (hr : r ∈ carriedRegs d nCar)
    (k : Nat) (hk : d + nCar ≤ k) : r ≠ regName k := by
  obtain ⟨j, hj, rfl⟩ := mem_carriedRegs.mp hr
  intro he
  have := JasminLsemSimulation.regName_injective he
  omega

@[simp] theorem parMoves_length (D : Nat) (tgts : List String) (ops : List LOperand) :
    (parMoves D tgts ops).length = ops.length + tgts.length := by
  simp [parMoves, stageMoves, commitMoves]

/-- **The parallel assignment.** `parMoves D tgts ops`, for register operands below the
    depth `D` and pairwise distinct targets below `D`, writes at each target the cell its
    operand held before the run, and keeps the array carrier and every cell that is
    neither a target nor a temporary `regName (D + j)`. -/
theorem steps_parMoves {P : LprogM} (D : Nat) (tgts : List String) (ops : List LOperand)
    (pre post : List LinstrRM) (s : LstateMF)
    (hbody : P.body = pre ++ parMoves D tgts ops ++ post) (hat : atPc P pre.length s)
    (hlen : ops.length = tgts.length)
    (hops : ∀ o ∈ ops, o = .reg (operandName o) ∧ ∀ k, D ≤ k → operandName o ≠ regName k)
    (hnd : tgts.Nodup) (htg : ∀ r ∈ tgts, ∀ k, D ≤ k → r ≠ regName k) :
    ∃ t, Steps x86Isa P (2 * tgts.length) s t ∧ atPc P (pre.length + 2 * tgts.length) t
      ∧ t.prog.base.larr = s.prog.base.larr
      ∧ (∀ j, j < tgts.length → t.prog.base.reg.lvm (tgts.getD j "")
          = s.prog.base.reg.lvm (operandName (ops.getD j (.imm 0))))
      ∧ (∀ r, r ∉ tgts → (∀ j, j < tgts.length → r ≠ regName (D + j)) →
          t.prog.base.reg.lvm r = s.prog.base.reg.lvm r) := by
  have hget : ∀ j, j < tgts.length → tgts.getD j "" ∈ tgts := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  have hgetO : ∀ j, j < ops.length → ops.getD j (.imm 0) ∈ ops := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  rw [parMoves, stageMoves_eq_range D ops (fun o ho => (hops o ho).1),
    commitMoves_eq_range D tgts, List.append_assoc, List.append_assoc] at hbody
  obtain ⟨t1, hs1, hat1, ha1, hm1, ho1⟩ := steps_moves P (fun j => regName (D + j))
    (fun j => operandName (ops.getD j (.imm 0))) ops.length pre _ s
    (by rw [hbody, List.append_assoc]) hat
    (fun i j hij _ he => by have := JasminLsemSimulation.regName_injective he; omega)
    (fun i j _ hj => (hops _ (hgetO j hj)).2 _ (Nat.le_add_right D i))
  obtain ⟨t2, hs2, hat2, ha2, hm2, ho2⟩ := steps_moves P (fun j => tgts.getD j "")
    (fun j => regName (D + j)) tgts.length (pre ++ (List.range ops.length).map fun j =>
      movI (regName (D + j)) (.reg (operandName (ops.getD j (.imm 0))))) post t1
    (by rw [hbody]; simp only [List.append_assoc])
    (by rw [List.length_append, List.length_map, List.length_range]; exact hat1)
    (fun i j hij hj he => by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : i < tgts.length), List.getElem?_eq_getElem hj,
        Option.getD_some, Option.getD_some] at he
      have := (List.Nodup.getElem_inj_iff hnd).mp he
      omega)
    (fun i j hij hj he => htg _ (hget i (by omega)) _ (Nat.le_add_right D j) he.symm)
  refine ⟨t2, ?_, ?_, ha2.trans ha1, fun j hj => ?_, fun r hr hk => ?_⟩
  · have := hs1.trans hs2
    rwa [hlen, ← Nat.two_mul] at this
  · rw [List.length_append, List.length_map, List.length_range, hlen] at hat2
    rwa [Nat.two_mul, ← Nat.add_assoc]
  · rw [hm2 j hj]
    exact hm1 j (by omega)
  · rw [ho2 r fun j hj he => hr (he ▸ hget j hj)]
    exact ho1 r fun j hj => hk j (hlen ▸ hj)

/-- **The tail of a counted trip**: the parallel assignment of the returned operands to the
    carried block, the advance of the trip index and the counter, and the compare of the
    counter with zero. -/
theorem forTail_steps {P : LprogM} {d n nCar bD : Nat} {ops : List LOperand}
    (pre post : List LinstrRM) (s : LstateMF) {x c : BitVec 64}
    (hbody : P.body = pre ++ parMoves bD (carriedRegs (d + 1) nCar) ops
      ++ (advanceOps (regName d) (loopCtr n)
      ++ guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])
        :: post))
    (hat : atPc P pre.length s) (hlen : ops.length = nCar) (hD : d + 1 + nCar ≤ bD)
    (hops : ∀ o ∈ ops, o = .reg (operandName o) ∧ ∀ k, bD ≤ k → operandName o ≠ regName k)
    (hx : s.prog.base.reg.lvm (regName d) = ⟨64, x⟩)
    (hc : s.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩) :
    ∃ t, Steps x86Isa P (2 * nCar + 3) s t ∧ atPc P (pre.length + 2 * nCar + 3) t
      ∧ t.prog.base.larr = s.prog.base.larr ∧ t.zf = (c - 1#64 == 0#64)
      ∧ t.prog.base.reg.lvm (regName d) = ⟨64, x + 1#64⟩
      ∧ t.prog.base.reg.lvm (loopCtr n) = ⟨64, c - 1#64⟩
      ∧ (∀ j, j < nCar → t.prog.base.reg.lvm (regName (d + 1 + (nCar - 1 - j)))
          = s.prog.base.reg.lvm (operandName (ops.getD j (.imm 0))))
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) → r ≠ loopCtr n →
          t.prog.base.reg.lvm r = s.prog.base.reg.lvm r) := by
  have hcar := carriedRegs_length (d + 1) nCar
  have hnc : ∀ k, loopCtr n ∉ carriedRegs k nCar := fun k hm => by
    obtain ⟨j, _, he⟩ := mem_carriedRegs.mp hm
    exact loopCtr_ne_regName n _ he
  obtain ⟨t1, hs1, hat1, ha1, hm1, ho1⟩ := steps_parMoves bD (carriedRegs (d + 1) nCar) ops
    pre _ s hbody hat (by rw [hlen, hcar]) hops (carriedRegs_nodup _ _)
    (fun r hr k hk => carriedRegs_ne_regName hr k (by omega))
  rw [hcar] at hs1 hat1 hm1
  have hidx1 : t1.prog.base.reg.lvm (regName d) = ⟨64, x⟩ := by
    rw [ho1 _ (fun hm => by
        obtain ⟨j, _, he⟩ := mem_carriedRegs.mp hm
        have := JasminLsemSimulation.regName_injective he
        omega)
      (fun j _ he => by have := JasminLsemSimulation.regName_injective he; omega)]
    exact hx
  have hctr1 : t1.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩ := by
    rw [ho1 _ (hnc _) (fun j _ => loopCtr_ne_regName n _)]
    exact hc
  have hlenP : (pre ++ parMoves bD (carriedRegs (d + 1) nCar) ops).length
      = pre.length + 2 * nCar := by
    rw [List.length_append, parMoves_length, hlen, hcar]
    omega
  obtain ⟨t2, hs2, hat2, ha2, hm2⟩ := steps_addImm (va := x) hat1
    (fetch_of_body (by rw [hbody]; rfl) hlenP) hidx1
  obtain ⟨t3, hs3, hat3, ha3, hm3⟩ := steps_subImm (va := c) (dst := loopCtr n)
    (a := loopCtr n) (c := 1) hat2
    (fetch_of_body (xs := pre ++ parMoves bD (carriedRegs (d + 1) nCar) ops
        ++ [(.Lopn [.reg (regName d)] (withWidthTag 64 "ADD") [.reg (regName d), .imm 1],
          .reg none)])
      (by rw [hbody]; simp only [advanceOps, List.append_assoc, List.cons_append,
        List.nil_append]; rfl)
      (by rw [List.length_append, hlenP]; rfl))
    (by rw [hm2, if_neg (loopCtr_ne_regName n d)]; exact hctr1)
  obtain ⟨t4, hs4, hat4, ha4, hm4, hz4⟩ := steps_cmpZero (v := c - 1#64) (r := loopCtr n) hat3
    (fetch_of_body (xs := pre ++ parMoves bD (carriedRegs (d + 1) nCar) ops
        ++ advanceOps (regName d) (loopCtr n))
      (by rw [hbody]; simp only [List.append_assoc]; rfl)
      (by rw [List.length_append, hlenP]; rfl))
    (by rw [hm3, if_pos rfl])
  have hri : regName d ≠ loopCtr n := (loopCtr_ne_regName n d).symm
  refine ⟨t4, ((hs1.trans hs2).trans hs3).trans hs4, hat4, ((ha4.trans ha3).trans ha2).trans ha1,
    hz4, ?_, ?_, fun j hj => ?_, fun r hr hrc => ?_⟩
  · rw [hm4, hm3, if_neg hri, hm2, if_pos rfl]
  · rw [hm4, hm3, if_pos rfl]
  · have hne : regName (d + 1 + (nCar - 1 - j)) ≠ regName d := fun he => by
      have := JasminLsemSimulation.regName_injective he
      omega
    rw [hm4, hm3, if_neg (fun he => loopCtr_ne_regName n _ he.symm), hm2, if_neg hne,
      ← carriedRegs_getD (d + 1) nCar j hj]
    exact hm1 j hj
  · rw [hm4, hm3, if_neg hrc, hm2, if_neg (hr d le_rfl)]
    exact ho1 r (fun hm => by
        obtain ⟨j, _, he⟩ := mem_carriedRegs.mp hm
        exact hr _ (by omega) he)
      (fun j _ => hr _ (by omega))

/-! ## 15. The trips of a counted loop -/

theorem loopCtr_injective : Function.Injective loopCtr := by
  intro a b hab
  unfold loopCtr at hab
  apply FreshNameInjective.natToString_injective
  have hd := congrArg String.toList hab
  simp only [String.toList_append] at hd
  exact String.toList_injective (List.append_cancel_left hd)

/-- Registers with the same cell read the same at every width. -/
theorem getW_of_lvm_eq {s s' : LstateN} {r r' : String} (w : Nat) (h : s.lvm r = s'.lvm r') :
    s.getW r w = s'.getW r' w := by
  unfold LstateN.getW
  rw [h]

section ForLoop

variable (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
  (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs) (hcs : RegTys cs)
  (hsim : ExportRSim nArgs fn body) {d n : Nat} {b : Exported}
  (hb : exportR nArgs fn body (d + 1 + cs.length) (n + 2) = some b) (hlen : Γ.length = d)
  (harg : nArgs ≤ d) {P : LprogM} {A R Z : List LinstrRM} (hfn : P.lfn = fn)
  (hbody : P.body = A ++ labelI n :: (b.code ++ R))
  (hR : R = parMoves b.depth (carriedRegs (d + 1) cs.length) b.res
    ++ (advanceOps (regName d) (loopCtr n)
    ++ guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])
      :: condI (.reg "NZ") n :: Z))
  (hA : ∀ l, n ≤ l → findLabelMem l A = none) (fuel : Nat) (V : Ctxt.Valuation Γ)

include hcs hsim hb hlen harg hfn hbody hR hA in
/-- **One trip of a counted loop**, from the counter after the top label to the back-edge
    jump: the body, the assignment of the returned tuple to the carried block, the advance
    and the compare. -/
theorem forLoop_trip (i : Nat) (acc acc1 : Ctxt.Valuation cs) (m : LstateMF) (c : BitVec 64)
    (hden : body.denote fuel (hvAppend acc
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ))) = some acc1)
    (hat : atPc P (A.length + 1) m) (hag : StoreAgreesM nArgs d m.prog.base V)
    (hidx : m.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i⟩)
    (hctr : m.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩)
    (hblk : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) :
    ∃ (k : Nat) (t : LstateMF), Steps x86Isa P k m t
      ∧ atPc P ((A ++ labelI n :: b.code).length + 2 * cs.length + 3) t
      ∧ RegionFrame d n m.prog.base t.prog.base ∧ t.zf = (c - 1#64 == 0#64)
      ∧ t.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i + 1#64⟩
      ∧ t.prog.base.reg.lvm (loopCtr n) = ⟨64, c - 1#64⟩
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          t.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup acc1))
      ∧ b.res.length = cs.length := by
  have hag1 : StoreAgreesM nArgs (d + 1) m.prog.base
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ)) :=
    storeAgreesM_append (cs := [JasminTy.reg 64])
      (acc := (HVector.cons (BitVec.ofNat 64 i) HVector.nil :
        Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 64]))
      (fun t ht => by rw [List.mem_singleton.mp ht]; rfl) harg hag
      (fun {w} u => by
        cases u with
        | here => exact getW_of_lvm _ _ _ hidx
        | there u => cases u)
  have hag2 : StoreAgreesM nArgs (d + 1 + cs.length) m.prog.base (hvAppend acc
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ))) :=
    storeAgreesM_append hcs (by omega) hag1 hblk
  have hbd := exportR_depth_le nArgs fn body _ _ _ hb
  obtain ⟨k1, m1, hs1, hat1, ⟨Δ, W, vs, hΔ, hagW, hops, hacc⟩, hfr1⟩ :=
    hsim (d + 1 + cs.length) (n + 2) b hb
      (by simp only [List.length_append, List.length_cons, hlen]; omega) (by omega) P
      (A ++ [labelI n]) R hfn
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
      (fun l hl => by
        rw [findLabelMem_eq_none_iff, labelsOf_append]
        simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
          not_or]
        exact ⟨(findLabelMem_eq_none_iff l A).mp (hA l (by omega)),
          fun he => by have : (l : Nat) = n := he; omega⟩)
      fuel _ acc1 m hden
      (by rw [List.length_append, List.length_singleton]; exact hat) hag2
  have hres_len : b.res.length = cs.length := by rw [hops, exprArgsHV_length]
  have hat1' : atPc P (A ++ labelI n :: b.code).length m1 := by
    rw [List.length_append, List.length_singleton] at hat1
    rw [List.length_append, List.length_cons]
    rwa [show A.length + (b.code.length + 1) = A.length + 1 + b.code.length by omega]
  obtain ⟨t, hs2, hat2, harr, hz, hidx', hctr', hblk', hoth⟩ :=
    forTail_steps (d := d) (n := n) (nCar := cs.length) (bD := b.depth) (ops := b.res)
      (A ++ labelI n :: b.code) (condI (.reg "NZ") n :: Z) m1 (x := BitVec.ofNat 64 i) (c := c)
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append]) hat1' hres_len hbd
      (by rw [hops]; exact exprArgsHV_reg nArgs hΔ vs)
      (by
        rw [hfr1.lvm_eq _
          (fun k hk he => by have := JasminLsemSimulation.regName_injective he; omega)
          (fun l _ he => loopCtr_ne_regName l d he.symm)]
        exact hidx)
      (by
        rw [hfr1.lvm_eq _ (fun k _ => loopCtr_ne_regName n k)
          (fun l hl he => by have := loopCtr_injective he; omega)]
        exact hctr)
  refine ⟨k1 + (2 * cs.length + 3), t, hs1.trans hs2, hat2, ?_, hz, hidx', hctr',
    fun {w} u => ?_, hres_len⟩
  · exact (hfr1.mono (by omega) (by omega)).trans
      (RegionFrame.of_cells harr fun r hr hl => hoth r hr (hl n le_rfl)) le_rfl le_rfl
  · have hu := JasminLsemSimulation.varIndex_lt u
    rw [getW_of_lvm_eq w (hblk' (varIndex u) hu), hops, exprArgsHV_getD,
      ← evalOperandN_resolveVar, hacc, lookup_lookupArgs]
    exact hagW.1 (hvToHom vs u)

include hcs hsim hb hlen harg hfn hbody hR hA in
/-- **The trips of a counted loop.** From the counter after the top label with `rem + 1`
    trips left, the trip index `i` in its register and the carried tuple in the carried
    block, the run reaches the counter after the back-edge jump with the tuple of the fold
    in the carried block, within the frame of the region. -/
theorem forLoop_trips : ∀ (rem i : Nat) (acc accN : Ctxt.Valuation cs) (m : LstateMF)
    (c : BitVec 64),
    (List.range' i (rem + 1)).foldlM (fun acc i => body.denote fuel (hvAppend acc
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ)))) acc
        = some accN →
    c.toNat = rem + 1 → atPc P (A.length + 1) m → StoreAgreesM nArgs d m.prog.base V →
    m.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i⟩ →
    m.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩ →
    (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) →
    ∃ (k : Nat) (m' : LstateMF), Steps x86Isa P k m m'
      ∧ atPc P ((A ++ labelI n :: b.code).length + 2 * cs.length + 3 + 1) m'
      ∧ RegionFrame d n m.prog.base m'.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          m'.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN)) := by
  have hcc : flagCondCC? (condI (.reg "NZ") n) = some (false, n) := rfl
  have hfetch : b.res.length = cs.length →
      P.body[(A ++ labelI n :: b.code).length + 2 * cs.length + 3]?
        = some (condI (.reg "NZ") n) := fun hres =>
    fetch_of_body (xs := (A ++ labelI n :: b.code)
        ++ parMoves b.depth (carriedRegs (d + 1) cs.length) b.res
        ++ advanceOps (regName d) (loopCtr n)
        ++ [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
          [.reg (loopCtr n), .imm 0])])
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by
        simp only [List.length_append, parMoves_length, carriedRegs_length, hres, advanceOps,
          List.length_cons, List.length_nil]
        omega)
  intro rem
  induction rem with
  | zero =>
      intro i acc accN m c hfold hc hat hag hidx hctr hblk
      rw [List.range'_succ, List.foldlM_cons] at hfold
      obtain ⟨acc1, hden, hrest⟩ := Option.bind_eq_some_iff.mp hfold
      rw [List.range'_zero, List.foldlM_nil] at hrest
      obtain rfl : acc1 = accN := Option.some.inj hrest
      obtain ⟨k, t, hs, hat2, hfr, hz, _, _, hblk', hres⟩ :=
        forLoop_trip nArgs fn body hcs hsim hb hlen harg hfn hbody hR hA fuel V i acc acc1 m c
          hden hat hag hidx hctr hblk
      have hc1 : c - 1#64 = 0#64 := by bv_omega
      obtain ⟨hs', hat'⟩ := steps_cc_fall hcc hat2 (hfetch hres)
        (by rw [hz, hc1]; decide)
      exact ⟨k + 1, next t, hs.trans hs', hat', hfr, fun {w} u => hblk' u⟩
  | succ rem ih =>
      intro i acc accN m c hfold hc hat hag hidx hctr hblk
      rw [List.range'_succ, List.foldlM_cons] at hfold
      obtain ⟨acc1, hden, hrest⟩ := Option.bind_eq_some_iff.mp hfold
      obtain ⟨k, t, hs, hat2, hfr, hz, hidx', hctr', hblk', hres⟩ :=
        forLoop_trip nArgs fn body hcs hsim hb hlen harg hfn hbody hR hA fuel V i acc acc1 m c
          hden hat hag hidx hctr hblk
      have hc1 : c - 1#64 ≠ 0#64 := by bv_omega
      have hl : findLabelMem n P.body = some A.length := by
        rw [hbody]
        exact findLabelMem_append_labelI n A _ ((findLabelMem_eq_none_iff n A).mp (hA n le_rfl))
      obtain ⟨hs', hat'⟩ := steps_cc_taken hcc hat2 (hfetch hres)
        (by rw [hz]; simpa using hc1) hl
      have hfr' : RegionFrame d n m.prog.base (goto t (A.length + 1)).prog.base :=
        hfr.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      obtain ⟨k', m', hs'', hat'', hfr'', hblk''⟩ := ih (i + 1) acc1 accN
        (goto t (A.length + 1)) (c - 1#64) hrest (by bv_omega) hat'
        (StoreAgreesM.of_regionFrame hlen hag hfr')
        (by rw [BitVec.ofNat_add]; exact hidx') hctr' (fun {w} u => hblk' u)
      exact ⟨k + 1 + k', m', (hs.trans hs').trans hs'', hat'',
        hfr'.trans hfr'' le_rfl le_rfl, fun {w} u => hblk'' u⟩

end ForLoop

/-! ## 16. The frame rule of a counted loop -/

theorem getD_mem_of_lt {α : Type} {l : List α} {j : Nat} (a : α) (hj : j < l.length) :
    l.getD j a ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

theorem getD_ne_of_nodup {l : List String} (h : l.Nodup) {i j : Nat} (hij : i < j)
    (hj : j < l.length) : l.getD i "" ≠ l.getD j "" := by
  intro he
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega : i < l.length), List.getElem?_eq_getElem hj,
    Option.getD_some, Option.getD_some] at he
  have := (List.Nodup.getElem_inj_iff h).mp he
  omega

/-- The returned operands of an export are as many as its result types. -/
theorem exportR_res_length (nArgs : Nat) (fn : String) {I : IsaData} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r → r.res.length = ts.length := by
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      exact exprArgsHV_length d nArgs vs
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      exact ih _ _ rk hk
  | forLoop count inits body k _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, _, rk, hk, rfl⟩ := h
      exact ihk _ _ rk hk
  | ifThenElse cond thn els k _ _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, _, e, _, rk, hk, rfl⟩ := h
      exact ihk _ _ rk hk
  | whileLoop inits body k _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, _, rk, hk, rfl⟩ := h
      exact ihk _ _ rk hk
  | call f args k _ =>
      intro d n r h
      simp [exportR] at h

/-- **The head of a counted loop**: the seeds of the carried block, of the trip index and
    of the counter, and the compare of the counter with zero. -/
theorem forHead_steps {P : LprogM} {d n nCar : Nat} {ops : List LOperand} {cn : String}
    (pre post : List LinstrRM) (s : LstateMF) {cnt : BitVec 64}
    (hbody : P.body = pre ++ seedMoves (carriedRegs (d + 1) nCar) ops
      ++ (movImmI (regName d) 0 :: movI (loopCtr n) (.reg cn)
        :: guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])
        :: post))
    (hat : atPc P pre.length s) (hlen : ops.length = nCar)
    (hops : ∀ o ∈ ops, o = .reg (operandName o) ∧ ∀ k, d ≤ k → operandName o ≠ regName k)
    (hcn : ∀ k, d ≤ k → cn ≠ regName k) (hcnt : s.prog.base.reg.lvm cn = ⟨64, cnt⟩) :
    ∃ t, Steps x86Isa P (nCar + 3) s t ∧ atPc P (pre.length + nCar + 3) t
      ∧ t.prog.base.larr = s.prog.base.larr ∧ t.zf = (cnt == 0#64)
      ∧ t.prog.base.reg.lvm (regName d) = ⟨64, 0#64⟩
      ∧ t.prog.base.reg.lvm (loopCtr n) = ⟨64, cnt⟩
      ∧ (∀ j, j < nCar → t.prog.base.reg.lvm (regName (d + 1 + (nCar - 1 - j)))
          = s.prog.base.reg.lvm (operandName (ops.getD j (.imm 0))))
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) → r ≠ loopCtr n →
          t.prog.base.reg.lvm r = s.prog.base.reg.lvm r) := by
  have hcar := carriedRegs_length (d + 1) nCar
  obtain ⟨S, hS⟩ : ∃ S, S = (List.range nCar).map fun j =>
      movI ((carriedRegs (d + 1) nCar).getD j "") (.reg (operandName (ops.getD j (.imm 0)))) :=
    ⟨_, rfl⟩
  have hSlen : S.length = nCar := by rw [hS, List.length_map, List.length_range]
  rw [seedMoves_eq_range _ _ (by rw [hlen, hcar]) (fun o ho => (hops o ho).1), hcar, ← hS]
    at hbody
  obtain ⟨t1, hs1, hat1, ha1, hm1, ho1⟩ := steps_moves P
    (fun j => (carriedRegs (d + 1) nCar).getD j "")
    (fun j => operandName (ops.getD j (.imm 0))) nCar pre _ s (by rw [hbody, hS]) hat
    (fun i j hij hj => getD_ne_of_nodup (carriedRegs_nodup _ _) hij (by rw [hcar]; exact hj))
    (fun i j hij hj he => by
      rw [carriedRegs_getD _ _ _ (by omega)] at he
      exact (hops _ (getD_mem_of_lt _ (hlen ▸ hj))).2 _ (by omega) he)
  obtain ⟨t2, hs2, hat2, ha2, hm2⟩ := steps_movImm (dst := regName d) (c := 0) hat1
    (fetch_of_body (xs := pre ++ S) hbody (by rw [List.length_append, hSlen]))
  obtain ⟨t3, hs3, hat3, ha3, hm3⟩ := steps_movReg (dst := loopCtr n) (src := cn) hat2
    (fetch_of_body (xs := pre ++ S ++ [movImmI (regName d) 0])
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append, List.length_append, hSlen]; rfl))
  have hc3 : t3.prog.base.reg.lvm (loopCtr n) = ⟨64, cnt⟩ := by
    rw [hm3, if_pos rfl, hm2, if_neg (hcn d le_rfl),
      ho1 cn fun j hj => by rw [carriedRegs_getD _ _ _ hj]; exact hcn _ (by omega)]
    exact hcnt
  obtain ⟨t4, hs4, hat4, ha4, hm4, hz4⟩ := steps_cmpZero (r := loopCtr n) (v := cnt) hat3
    (fetch_of_body (xs := pre ++ S ++ [movImmI (regName d) 0, movI (loopCtr n) (.reg cn)])
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append, List.length_append, hSlen]; rfl))
    hc3
  have hri : regName d ≠ loopCtr n := (loopCtr_ne_regName n d).symm
  refine ⟨t4, ((hs1.trans hs2).trans hs3).trans hs4, hat4, ((ha4.trans ha3).trans ha2).trans ha1,
    hz4, ?_, ?_, fun j hj => ?_, fun r hr hrc => ?_⟩
  · rw [hm4, hm3, if_neg hri, hm2, if_pos rfl]
  · rw [hm4]
    exact hc3
  · have hne : regName (d + 1 + (nCar - 1 - j)) ≠ regName d := fun he => by
      have := JasminLsemSimulation.regName_injective he
      omega
    rw [hm4, hm3, if_neg (fun he => loopCtr_ne_regName n _ he.symm), hm2, if_neg hne,
      ← carriedRegs_getD (d + 1) nCar j hj]
    exact hm1 j hj
  · rw [hm4, hm3, if_neg hrc, hm2, if_neg (hr d le_rfl)]
    exact ho1 r fun j hj => by rw [carriedRegs_getD _ _ _ hj]; exact hr _ (by omega)

/-- **The frame rule of a counted loop.** For carried types held in register cells, the
    statement for the body and for the continuation gives the statement for the loop. -/
theorem forFrame_sim (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
    {ts : List JasminTy} (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts) (hcs : RegTys cs)
    (hbsim : ExportRSim nArgs fn body) (hksim : ExportRSim nArgs fn k) :
    ExportRSim nArgs fn (NFProg.forLoop count inits body k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V v m hden hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rk, hrk, rfl⟩ := h
  rw [NFProg.denote_forLoop] at hden
  obtain ⟨accN, hfold, hkden⟩ := Option.bind_eq_some_iff.mp hden
  have hbody0 := hbody
  have hLab := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ _ hb
  have hreslen := exportR_res_length nArgs fn body _ _ _ hb
  -- the count and the seeds
  obtain ⟨cn, hcn⟩ : ∃ cn, cn = operandName (resolveVar d nArgs argName (fun _ => none) count) :=
    ⟨_, rfl⟩
  have hcreg : resolveVar d nArgs argName (fun _ => none) count = .reg cn := by
    rw [hcn]
    exact resolveVar_isReg count
  obtain ⟨cnt, hcd⟩ : ∃ cnt : BitVec 64, count.lookup V = cnt := ⟨_, rfl⟩
  have hcnt : m.prog.base.reg.lvm cn = ⟨64, cnt⟩ := by
    have := hag.1 count
    rw [evalOperandN_resolveVar, ← hcn, hcd] at this
    exact getW_eq_some_iff.mp this
  have hcnk : ∀ k, d ≤ k → cn ≠ regName k := fun k hk => by
    rw [hcn]
    exact resolveVar_operandName_ne_regName count
      (hlen ▸ JasminLsemSimulation.varIndex_lt count) k hk
  obtain ⟨ops, hops⟩ : ∃ ops, ops = exprArgsHV d nArgs argName (fun _ => none) inits := ⟨_, rfl⟩
  have hopslen : ops.length = cs.length := by rw [hops, exprArgsHV_length]
  have hopsreg := exprArgsHV_reg nArgs hlen inits
  rw [← hops] at hopsreg
  -- the layout of the body
  obtain ⟨cmp, hcmp⟩ : ∃ cmp, cmp = guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
      [.reg (loopCtr n), .imm 0]) := ⟨_, rfl⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs, Zs = labelI (n + 1) :: (shiftMoves d cs.length ++ (rk.code ++ post)) :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = parMoves b.depth (carriedRegs (d + 1) cs.length) b.res
      ++ (advanceOps (regName d) (loopCtr n) ++ cmp :: condI (.reg "NZ") n :: Zs) := ⟨_, rfl⟩
  have hF : forFrame d n cs.length ops (.reg cn) b.code b.res b.depth
      = seedMoves (carriedRegs (d + 1) cs.length) ops
        ++ (movImmI (regName d) 0 :: movI (loopCtr n) (.reg cn) :: cmp
          :: condI (.reg "Z") (n + 1) :: labelI n :: (b.code
          ++ (parMoves b.depth (carriedRegs (d + 1) cs.length) b.res
          ++ (advanceOps (regName d) (loopCtr n) ++ (cmp :: condI (.reg "NZ") n
          :: labelI (n + 1) :: shiftMoves d cs.length))))) := by
    rw [hcmp]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hcreg, ← hops, hF]
    at hbody
  have hbodyH : P.body = pre ++ seedMoves (carriedRegs (d + 1) cs.length) ops
      ++ (movImmI (regName d) 0 :: movI (loopCtr n) (.reg cn) :: cmp
        :: (condI (.reg "Z") (n + 1) :: labelI n :: (b.code ++ R))) := by
    rw [hbody, hR, hZs]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ seedMoves (carriedRegs (d + 1) cs.length) ops
      ++ [movImmI (regName d) 0, movI (loopCtr n) (.reg cn), cmp, condI (.reg "Z") (n + 1)] :=
    ⟨_, rfl⟩
  have hbodyL : P.body = A ++ labelI n :: (b.code ++ R) := by
    rw [hbodyH, hAd]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hAlen : A.length = pre.length + cs.length + 3 + 1 := by
    rw [hAd]
    simp only [List.length_append, seedMoves, List.length_map, List.length_zip,
      carriedRegs_length, hopslen, Nat.min_self, List.length_cons, List.length_nil]
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, hcmp, labelsOf_append, labelsOf_append, labelsOf_seedMoves, List.append_nil]
    exact List.append_nil _
  have hAlab : ∀ l, n ≤ l → findLabelMem l A = none := fun l hl => by
    rw [findLabelMem_eq_none_iff, hAlabs, ← findLabelMem_eq_none_iff]
    exact hpre l hl
  obtain ⟨X, hX⟩ : ∃ X, X = A ++ labelI n :: (b.code
      ++ (parMoves b.depth (carriedRegs (d + 1) cs.length) b.res
      ++ (advanceOps (regName d) (loopCtr n) ++ [cmp, condI (.reg "NZ") n]))) := ⟨_, rfl⟩
  have hbodyX : P.body = X ++ labelI (n + 1) :: (shiftMoves d cs.length ++ (rk.code ++ post)) := by
    rw [hbodyL, hR, hZs, hX]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hXlen : X.length = (A ++ labelI n :: b.code).length + 2 * cs.length + 3 + 1 := by
    rw [hX]
    simp only [List.length_append, List.length_cons, parMoves_length, carriedRegs_length,
      hreslen, advanceOps, List.length_nil]
    omega
  have hXlabs : labelsOf X = labelsOf pre ++ n :: labelsOf b.code := by
    rw [hX, hcmp, labelsOf_append, hAlabs, labelsOf_cons_labelI, labelsOf_append,
      labelsOf_append, labelsOf_parMoves, labelsOf_append, labelsOf_advanceOps]
    simp only [List.nil_append]
    rw [show labelsOf [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
      [.reg (loopCtr n), .imm 0]), condI (.reg "NZ") n] = [] from rfl, List.append_nil]
  have hl1 : findLabelMem (n + 1) P.body = some X.length := by
    rw [hbodyX]
    refine findLabelMem_append_labelI (n + 1) X _ ?_
    rw [hXlabs, List.mem_append, List.mem_cons, not_or, not_or]
    refine ⟨(findLabelMem_eq_none_iff _ pre).mp (hpre _ (by omega)), fun he => ?_, fun hm => ?_⟩
    · have : (n + 1 : Nat) = n := he
      omega
    · have := hLab.range _ hm
      omega
  -- the head
  obtain ⟨t0, hs0, hat0, ha0, hz0, hidx0, hctr0, hblk0, hoth0⟩ :=
    forHead_steps (d := d) (n := n) (nCar := cs.length) (ops := ops) (cn := cn) pre _ m
      (cnt := cnt) (by rw [hbodyH, hcmp]) hat hopslen hopsreg hcnk hcnt
  have hfr0 : RegionFrame d n m.prog.base t0.prog.base :=
    RegionFrame.of_cells ha0 fun r hr hl => hoth0 r hr (hl n le_rfl)
  have hblkI : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      t0.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup (Expr.lookupArgs inits V)) := fun {w} u => by
    have hu := JasminLsemSimulation.varIndex_lt u
    rw [getW_of_lvm_eq w (hblk0 (varIndex u) hu), hops, exprArgsHV_getD,
      ← evalOperandN_resolveVar, lookup_lookupArgs]
    exact hag.1 (hvToHom inits u)
  have hfetchZ : P.body[pre.length + cs.length + 3]? = some (condI (.reg "Z") (n + 1)) :=
    fetch_of_body (xs := pre ++ seedMoves (carriedRegs (d + 1) cs.length) ops
        ++ [movImmI (regName d) 0, movI (loopCtr n) (.reg cn), cmp])
      (by rw [hbodyH]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by
        simp only [List.length_append, seedMoves, List.length_map, List.length_zip,
          carriedRegs_length, hopslen, Nat.min_self, List.length_cons, List.length_nil])
  have hfold' : (List.range cnt.toNat).foldlM (fun acc i => body.denote fuel (hvAppend acc
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ))))
      (Expr.lookupArgs inits V) = some accN := by
    rw [← hcd]
    exact hfold
  -- the trips, to the counter after the exit label
  have hexit : ∃ (kE : Nat) (mE : LstateMF), Steps x86Isa P kE m mE ∧ atPc P (X.length + 1) mE
      ∧ RegionFrame d n m.prog.base mE.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          mE.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN)) := by
    cases hN : cnt.toNat with
    | zero =>
        rw [hN, List.range_zero, List.foldlM_nil] at hfold'
        obtain rfl : Expr.lookupArgs inits V = accN := Option.some.inj hfold'
        have hc0 : cnt = 0#64 := by bv_omega
        obtain ⟨hs1, hat1⟩ := steps_cc_taken (pol := true) rfl hat0 hfetchZ
          (by rw [hz0, hc0]; rfl) hl1
        exact ⟨_, _, hs0.trans hs1, hat1,
          hfr0.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl,
          fun {w} u => hblkI u⟩
    | succ rem =>
        rw [hN, List.range_eq_range'] at hfold'
        have hc0 : cnt ≠ 0#64 := by bv_omega
        obtain ⟨hs1, hat1⟩ := steps_cc_fall (pol := true) rfl hat0 hfetchZ
          (by rw [hz0]; simpa using hc0)
        rw [← hAlen] at hat1
        obtain ⟨hs2, hat2⟩ := steps_label x86Isa (kind := .internal) (l := n) (tag := .reg none)
          hat1 (fetch_of_body hbodyL rfl)
        have hfr2 : RegionFrame d n m.prog.base (next (next t0)).prog.base :=
          hfr0.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
        obtain ⟨k3, m3, hs3, hat3, hfr3, hblk3⟩ :=
          forLoop_trips nArgs fn body hcs hbsim hb hlen harg hfn hbodyL (by rw [hR, hcmp]) hAlab
            fuel V rem 0 (Expr.lookupArgs inits V) accN (next (next t0)) cnt hfold' hN hat2
            (StoreAgreesM.of_regionFrame hlen hag hfr2) hidx0 hctr0 (fun {w} u => hblkI u)
        rw [← hXlen] at hat3
        obtain ⟨hs4, hat4⟩ := steps_label x86Isa (kind := .internal) (l := n + 1)
          (tag := .reg none) hat3 (fetch_of_body hbodyX rfl)
        exact ⟨_, _, (((hs0.trans hs1).trans hs2).trans hs3).trans hs4, hat4,
          (hfr2.trans hfr3 le_rfl le_rfl).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl)
            le_rfl le_rfl,
          fun {w} u => hblk3 u⟩
  obtain ⟨kE, mE, hsE, hatE, hfrE, hblkE⟩ := hexit
  -- the shift of the carried block
  obtain ⟨mS, hsS, hatS, haS, hmS, hoS⟩ := steps_moves P (fun j => regName (d + j))
    (fun j => regName (d + 1 + j)) cs.length (X ++ [labelI (n + 1)]) (rk.code ++ post) mE
    (by
      rw [hbodyX]
      simp only [shiftMoves, List.append_assoc, List.cons_append, List.nil_append])
    (by rw [List.length_append, List.length_singleton]; exact hatE)
    (fun i j hij _ he => by have := JasminLsemSimulation.regName_injective he; omega)
    (fun i j hij _ he => by have := JasminLsemSimulation.regName_injective he; omega)
  have hfrS : RegionFrame d n m.prog.base mS.prog.base :=
    hfrE.trans (RegionFrame.of_cells haS fun r hr _ => hoS r fun j _ => hr _ (by omega))
      le_rfl le_rfl
  have hagS : StoreAgreesM nArgs (d + cs.length) mS.prog.base (hvAppend accN V) :=
    storeAgreesM_append hcs harg (StoreAgreesM.of_regionFrame hlen hag hfrS) fun {w} u => by
      have hu := JasminLsemSimulation.varIndex_lt u
      rw [getW_of_lvm_eq w (hmS (cs.length - 1 - varIndex u) (by omega))]
      exact hblkE u
  -- the continuation
  have hnext := hLab.le
  obtain ⟨kK, m', hsK, hatK, hresK, hfrK⟩ := hksim (d + cs.length) b.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P
    (X ++ labelI (n + 1) :: shiftMoves d cs.length) post hfn
    (by rw [hbodyX]; simp only [List.append_assoc, List.cons_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append, hXlabs, labelsOf_cons_labelI,
        labelsOf_shiftMoves]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨⟨(findLabelMem_eq_none_iff l pre).mp (hpre l (by omega)), fun he => ?_,
        fun hm => ?_⟩, fun he => ?_⟩
      · have : (l : Nat) = n := he
        omega
      · have := hLab.range _ hm
        omega
      · have : (l : Nat) = n + 1 := he
        omega)
    fuel _ v mS hkden
    (by
      rw [List.length_append, List.length_singleton] at hatS
      simp only [List.length_append, List.length_cons, shiftMoves, List.length_map,
        List.length_range]
      rwa [Nat.add_comm cs.length 1, ← Nat.add_assoc])
    hagS
  have hlenEq : pre.length + (Exported.prepend (forFrame d n cs.length
      (exprArgsHV d nArgs argName (fun _ => none) inits)
      (resolveVar d nArgs argName (fun _ => none) count) b.code b.res b.depth) rk).code.length
      = (X ++ labelI (n + 1) :: shiftMoves d cs.length).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyX] at h1
    simp only [List.length_append, List.length_cons] at h1 ⊢
    omega
  refine ⟨kE + cs.length + kK, m', (hsE.trans hsS).trans hsK, ?_, hresK,
    hfrS.trans hfrK (by omega) (by omega)⟩
  rw [hlenEq]
  exact hatK

/-! ## 17. The exit-flag loop -/

theorem exprArgsHV_isReg {Γ : Ctxt jasminDialect} (cd nArgs : Nat) :
    ∀ {ts : List JasminTy} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts),
      ∀ o ∈ exprArgsHV cd nArgs argName (fun _ => none) vs, o = .reg (operandName o)
  | [], .nil, o, h => by simp [exprArgsHV] at h
  | _ :: _, .cons v rest, o, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact resolveVar_isReg v
      · exact exprArgsHV_isReg cd nArgs rest o h'

/-- The returned operands of an export are registers. -/
theorem exportR_res_isReg (nArgs : Nat) (fn : String) {I : IsaData} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r →
      ∀ o ∈ r.res, o = .reg (operandName o) := by
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      exact exprArgsHV_isReg d nArgs vs
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      exact ih _ _ rk hk
  | forLoop count inits body k _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, _, rk, hk, rfl⟩ := h
      exact ihk _ _ rk hk
  | ifThenElse cond thn els k _ _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, _, e, _, rk, hk, rfl⟩ := h
      exact ihk _ _ rk hk
  | whileLoop inits body k _ ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, _, rk, hk, rfl⟩ := h
      exact ihk _ _ rk hk
  | call f args k _ =>
      intro d n r h
      simp [exportR] at h

/-- The step of the select `CMOV dst, [c, a, b]` on a one-bit condition and two words. -/
theorem lsemStepMem_select (dst c a b : String) (s : LstateM) (vc : BitVec 1)
    (va vb : BitVec 64) (hc : s.reg.lvm c = ⟨1, vc⟩) (ha : s.reg.lvm a = ⟨64, va⟩)
    (hb : s.reg.lvm b = ⟨64, vb⟩) :
    lsemStepMem (.Lopn [.reg dst] (withWidthTag 64 "CMOV") [.reg c, .reg a, .reg b], .reg none) s
      = some (s.setReg dst (selectW vc va vb)).nextPc := by
  have key : ∀ L : LinstrR,
      L = .Lopn [.reg dst] (withWidthTag 64 "CMOV") [.reg c, .reg a, .reg b] →
      JasminLsemMulCarry.mulhiStruct? L = none ∧ JasminLsemMulCarry.adcxStruct? L = none
        ∧ JasminLsemMulCarry.adcxhiStruct? L = none ∧ JasminLsemMulCarry.sbbStruct? L = none
        ∧ JasminLsemMulCarry.sbbhiStruct? L = none ∧ JasminLsemShift.sarStruct? L = none := by
    intro L hL
    subst hL
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      JasminLsemMulCarry.struct?_select (w := 64) dst [.reg c, .reg a, .reg b]
    exact ⟨h1, h2, h3, h4, h5, JasminLsemShift.sarStruct?_select (w := 64) dst _⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := key _ rfl
  rw [lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
    JasminLsemMulCarry.lsemStepMC_of_delegate _ _ h1 h2 h3 h4 h5,
    JasminLsemShift.lsemStepSh_of_not_sar _ _ h6]
  simp only [lsemStepN, stripWidthTag_withWidthTag_CMOV, if_pos, operandName,
    getW_of_lvm _ _ _ hc, readReg, ha, evalOperandN, getW_of_lvm _ _ _ hb, Option.map_some]
  rfl

/-- **The widening of a bit.** `MOV r, #1 ; MOV z, #0 ; CMOV r, [f, r, z]` writes at `r` the
    word `1` when the bit in `f` is set and the word `0` otherwise, and keeps the array
    carrier and every cell other than `r` and `z`. -/
theorem flagWord_steps {P : LprogM} {r z f : String} (pre post : List LinstrRM) (s : LstateMF)
    {bit : BitVec 1}
    (hbody : P.body = pre ++ (movImmI r 1 :: movImmI z 0
      :: (.Lopn [.reg r] (withWidthTag 64 "CMOV") [.reg f, .reg r, .reg z], .reg none) :: post))
    (hat : atPc P pre.length s) (hrz : r ≠ z) (hfr : f ≠ r) (hfz : f ≠ z)
    (hbit : s.prog.base.reg.lvm f = ⟨1, bit⟩) :
    ∃ t, Steps x86Isa P 3 s t ∧ atPc P (pre.length + 3) t
      ∧ t.prog.base.larr = s.prog.base.larr
      ∧ t.prog.base.reg.lvm r = ⟨64, selectW bit (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)⟩
      ∧ (∀ q, q ≠ r → q ≠ z → t.prog.base.reg.lvm q = s.prog.base.reg.lvm q) := by
  obtain ⟨t1, hs1, hat1, ha1, hm1⟩ := steps_movImm (dst := r) (c := 1) hat
    (fetch_of_body (xs := pre) hbody rfl)
  obtain ⟨t2, hs2, hat2, ha2, hm2⟩ := steps_movImm (dst := z) (c := 0) hat1
    (fetch_of_body (xs := pre ++ [movImmI r 1])
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append]; rfl))
  have hflag2 : t2.prog.base.reg.lvm r = ⟨64, BitVec.ofNat 64 1⟩ := by
    rw [hm2, if_neg hrz, hm1, if_pos rfl]
  have hz2 : t2.prog.base.reg.lvm z = ⟨64, BitVec.ofNat 64 0⟩ := by
    rw [hm2, if_pos rfl]
  have hf2 : t2.prog.base.reg.lvm f = ⟨1, bit⟩ := by
    rw [hm2, if_neg hfz, hm1, if_neg hfr]
    exact hbit
  obtain ⟨t3, hs3, hat3, ha3, hm3⟩ := steps_setReg (dst := r)
    (selectW bit (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)) hat2
    (fetch_of_body (xs := pre ++ [movImmI r 1, movImmI z 0])
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append]; rfl))
    ⟨_, _, _, rfl⟩ rfl rfl
    (lsemStepMem_select _ f _ _ t2.prog.base bit _ _ hf2 hflag2 hz2)
  refine ⟨t3, (hs1.trans hs2).trans hs3, hat3, (ha3.trans ha2).trans ha1, ?_,
    fun q hqr hqz => ?_⟩
  · rw [hm3, if_pos rfl]
  · rw [hm3, if_neg hqr, hm2, if_neg hqz, hm1, if_neg hqr]

/-- **The tail of a trip of an exit-flag loop**: the widening of the continue bit, the
    parallel assignment of the returned tuple to the carried block, and the compare of the
    widened bit with zero. -/
theorem whileTail_steps {P : LprogM} {d nCar bD : Nat} {ops : List LOperand} {f : String}
    (pre post : List LinstrRM) (s : LstateMF) {bit : BitVec 1}
    (hbody : P.body = pre ++ (movImmI (regName (bD + nCar)) 1
      :: movImmI (regName (bD + nCar + 1)) 0
      :: (.Lopn [.reg (regName (bD + nCar))] (withWidthTag 64 "CMOV")
        [.reg f, .reg (regName (bD + nCar)), .reg (regName (bD + nCar + 1))], .reg none)
      :: (parMoves bD (carriedRegs d nCar) ops
        ++ guardI (.Lopn [.reg (regName (bD + nCar))] (withWidthTag 64 "CMP")
          [.reg (regName (bD + nCar)), .imm 0]) :: post)))
    (hat : atPc P pre.length s) (hlen : ops.length = nCar) (hD : d + nCar ≤ bD)
    (hops : ∀ o ∈ ops, o = .reg (operandName o) ∧ ∀ k, bD ≤ k → operandName o ≠ regName k)
    (hf : ∀ k, bD ≤ k → f ≠ regName k) (hbit : s.prog.base.reg.lvm f = ⟨1, bit⟩) :
    ∃ (k : Nat) (t : LstateMF), Steps x86Isa P k s t ∧ atPc P (pre.length + 2 * nCar + 4) t
      ∧ t.prog.base.larr = s.prog.base.larr ∧ t.zf = !decide (bit = 1#1)
      ∧ (∀ j, j < nCar → t.prog.base.reg.lvm (regName (d + (nCar - 1 - j)))
          = s.prog.base.reg.lvm (operandName (ops.getD j (.imm 0))))
      ∧ (∀ r, (∀ k, d ≤ k → r ≠ regName k) →
          t.prog.base.reg.lvm r = s.prog.base.reg.lvm r) := by
  have hcar := carriedRegs_length d nCar
  have hzf : regName (bD + nCar) ≠ regName (bD + nCar + 1) := fun he => by
    have := JasminLsemSimulation.regName_injective he
    omega
  obtain ⟨t3, hs3, hat3, ha3, hflag3, ho3⟩ := flagWord_steps (r := regName (bD + nCar))
    (z := regName (bD + nCar + 1)) (f := f) pre _ s hbody hat hzf (hf _ (by omega))
    (hf _ (by omega)) hbit
  obtain ⟨t4, hs4, hat4, ha4, hm4, ho4⟩ := steps_parMoves bD (carriedRegs d nCar) ops
    (pre ++ [movImmI (regName (bD + nCar)) 1, movImmI (regName (bD + nCar + 1)) 0,
      (.Lopn [.reg (regName (bD + nCar))] (withWidthTag 64 "CMOV")
        [.reg f, .reg (regName (bD + nCar)), .reg (regName (bD + nCar + 1))], .reg none)])
    _ t3 (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
    (by rw [List.length_append]; exact hat3) (by rw [hlen, hcar]) hops (carriedRegs_nodup _ _)
    (fun r hr k hk => carriedRegs_ne_regName hr k (by omega))
  rw [hcar] at hs4 hat4 hm4 ho4
  have hflag4 : t4.prog.base.reg.lvm (regName (bD + nCar))
      = ⟨64, selectW bit (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)⟩ := by
    rw [ho4 _ (fun hm => carriedRegs_ne_regName hm _ (by omega) rfl)
      (fun j hj he => by have := JasminLsemSimulation.regName_injective he; omega), hflag3]
  obtain ⟨t5, hs5, hat5, ha5, hm5, hz5⟩ := steps_cmpZero (r := regName (bD + nCar))
    (v := selectW bit (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)) hat4
    (fetch_of_body (xs := pre ++ [movImmI (regName (bD + nCar)) 1,
        movImmI (regName (bD + nCar + 1)) 0,
        (.Lopn [.reg (regName (bD + nCar))] (withWidthTag 64 "CMOV")
          [.reg f, .reg (regName (bD + nCar)), .reg (regName (bD + nCar + 1))], .reg none)]
        ++ parMoves bD (carriedRegs d nCar) ops)
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by
        simp only [List.length_append, parMoves_length, hlen, hcar, List.length_cons,
          List.length_nil]
        omega))
    hflag4
  have hsrc : ∀ r, (∀ k, bD ≤ k → r ≠ regName k) →
      t3.prog.base.reg.lvm r = s.prog.base.reg.lvm r := fun r hr =>
    ho3 r (hr _ (by omega)) (hr _ (by omega))
  refine ⟨_, t5, (hs3.trans hs4).trans hs5, ?_, (ha5.trans ha4).trans ha3, ?_, fun j hj => ?_,
    fun r hr => ?_⟩
  · rw [List.length_append] at hat5
    rw [show pre.length + 2 * nCar + 4 = pre.length + 3 + 2 * nCar + 1 by omega]
    exact hat5
  · rw [hz5]
    unfold selectW
    by_cases hb : bit = 1#1 <;> simp [hb]
  · rw [hm5, ← carriedRegs_getD d nCar j hj, hm4 j hj]
    exact hsrc _ (hops _ (getD_mem_of_lt _ (hlen ▸ hj))).2
  · rw [hm5, ho4 r (fun hm => by
        obtain ⟨j, _, he⟩ := mem_carriedRegs.mp hm
        exact hr _ (by omega) he)
      (fun j _ => hr _ (by omega))]
    exact hsrc r fun k hk => hr k (by omega)

section WhileLoop

variable (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
  (body : NFProg jasminDialect (cs ++ Γ) (JasminTy.reg 1 :: cs)) (hcs : RegTys cs)
  (hsim : ExportRSim nArgs fn body) {d n : Nat} {b : Exported}
  (hb : exportR nArgs fn body (d + cs.length) (n + 1) = some b) (hlen : Γ.length = d)
  (harg : nArgs ≤ d) {P : LprogM} {A R Z : List LinstrRM} {fname : String} (hfn : P.lfn = fn)
  (hbody : P.body = A ++ labelI n :: (b.code ++ R))
  (hfh : b.res.headD (.imm 0) = .reg fname)
  (hR : R = movImmI (regName (b.depth + cs.length)) 1
    :: movImmI (regName (b.depth + cs.length + 1)) 0
    :: (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
      [.reg fname, .reg (regName (b.depth + cs.length)),
        .reg (regName (b.depth + cs.length + 1))], .reg none)
    :: (parMoves b.depth (carriedRegs d cs.length) b.res.tail
      ++ guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
        [.reg (regName (b.depth + cs.length)), .imm 0]) :: condI (.reg "NZ") n :: Z))
  (hA : ∀ l, n ≤ l → findLabelMem l A = none) (fuel : Nat) (V : Ctxt.Valuation Γ)

include hcs hsim hb hlen harg hfn hbody hfh hR hA in
/-- **One trip of an exit-flag loop**, from the counter after the label to the back-edge
    jump. The zero flag is the negation of the continue bit. -/
theorem whileLoop_trip (acc : Ctxt.Valuation cs)
    (r : Ctxt.Valuation (d := jasminDialect) (JasminTy.reg 1 :: cs)) (m : LstateMF)
    (hden : body.denote fuel (hvAppend acc V) = some r)
    (hat : atPc P (A.length + 1) m) (hag : StoreAgreesM nArgs d m.prog.base V)
    (hblk : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) :
    ∃ (k : Nat) (t : LstateMF), Steps x86Isa P k m t
      ∧ atPc P ((A ++ labelI n :: b.code).length + 2 * cs.length + 4) t
      ∧ RegionFrame d n m.prog.base t.prog.base
      ∧ t.zf = !(HasBoolBit.toBool (d := jasminDialect) r.head)
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          t.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
            = some (u.lookup r.tail)) := by
  have hag2 : StoreAgreesM nArgs (d + cs.length) m.prog.base (hvAppend acc V) :=
    storeAgreesM_append hcs harg hag hblk
  have hbd := exportR_depth_le nArgs fn body _ _ _ hb
  obtain ⟨k1, m1, hs1, hat1, ⟨Δ, W, vs, hΔ, hagW, hops, hr⟩, hfr1⟩ :=
    hsim (d + cs.length) (n + 1) b hb
      (by rw [List.length_append, hlen]; omega) (by omega) P
      (A ++ [labelI n]) R hfn
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
      (fun l hl => by
        rw [findLabelMem_eq_none_iff, labelsOf_append]
        simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
          not_or]
        exact ⟨(findLabelMem_eq_none_iff l A).mp (hA l (by omega)),
          fun he => by have : (l : Nat) = n := he; omega⟩)
      fuel _ r m hden
      (by rw [List.length_append, List.length_singleton]; exact hat) hag2
  subst hr
  cases vs with
  | cons v0 vrest =>
  have hops' : b.res = resolveVar b.depth nArgs argName (fun _ => none) v0
      :: exprArgsHV b.depth nArgs argName (fun _ => none) vrest := hops
  have hfh' : resolveVar b.depth nArgs argName (fun _ => none) v0 = .reg fname := by
    rw [hops'] at hfh
    exact hfh
  have hfname : fname = operandName (resolveVar b.depth nArgs argName (fun _ => none) v0) := by
    rw [hfh']
    rfl
  have hbit : m1.prog.base.reg.lvm fname = ⟨1, v0.lookup W⟩ := by
    have := hagW.1 v0
    rw [hfh'] at this
    exact getW_eq_some_iff.mp this
  have hat1' : atPc P (A ++ labelI n :: b.code).length m1 := by
    rw [List.length_append, List.length_singleton] at hat1
    rw [List.length_append, List.length_cons]
    rwa [show A.length + (b.code.length + 1) = A.length + 1 + b.code.length by omega]
  obtain ⟨k2, t, hs2, hat2, harr, hz, hblk', hoth⟩ :=
    whileTail_steps (d := d) (nCar := cs.length) (bD := b.depth) (ops := b.res.tail)
      (f := fname) (A ++ labelI n :: b.code) (condI (.reg "NZ") n :: Z) m1 (bit := v0.lookup W)
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append])
      hat1' (by rw [hops', List.tail_cons, exprArgsHV_length]) (by omega)
      (by rw [hops', List.tail_cons]; exact exprArgsHV_reg nArgs hΔ vrest)
      (fun k hk => by
        rw [hfname]
        exact resolveVar_operandName_ne_regName v0
          (hΔ ▸ JasminLsemSimulation.varIndex_lt v0) k hk)
      hbit
  refine ⟨k1 + k2, t, hs1.trans hs2, hat2, ?_, hz, fun {w} u => ?_⟩
  · exact (hfr1.mono (by omega) (by omega)).trans
      (RegionFrame.of_cells harr fun r hr _ => hoth r hr) le_rfl le_rfl
  · have hu := JasminLsemSimulation.varIndex_lt u
    rw [getW_of_lvm_eq w (hblk' (varIndex u) hu), hops', List.tail_cons, exprArgsHV_getD,
      ← evalOperandN_resolveVar]
    exact (hagW.1 (hvToHom vrest u)).trans (congrArg some (lookup_lookupArgs W vrest u).symm)

include hcs hsim hb hlen harg hfn hbody hfh hR hA in
/-- **The trips of an exit-flag loop.** From the counter after the label with the carried
    tuple in the carried block, if the iteration of the body within `f` runs returns
    `accN`, the run reaches the counter after the back-edge jump with `accN` in the carried
    block, within the frame of the region. -/
theorem whileLoop_trips : ∀ (f : Nat) (acc accN : Ctxt.Valuation cs) (m : LstateMF),
    NFProg.whileIter (d := jasminDialect) (fun acc => body.denote fuel (hvAppend acc V)) f acc
      = some accN →
    atPc P (A.length + 1) m → StoreAgreesM nArgs d m.prog.base V →
    (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) →
    ∃ (k : Nat) (m' : LstateMF), Steps x86Isa P k m m'
      ∧ atPc P ((A ++ labelI n :: b.code).length + 2 * cs.length + 4 + 1) m'
      ∧ RegionFrame d n m.prog.base m'.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          m'.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN)) := by
  have hcc : flagCondCC? (condI (.reg "NZ") n) = some (false, n) := rfl
  have hreslen := exportR_res_length nArgs fn body _ _ _ hb
  have hfetch : P.body[(A ++ labelI n :: b.code).length + 2 * cs.length + 4]?
      = some (condI (.reg "NZ") n) :=
    fetch_of_body (xs := (A ++ labelI n :: b.code)
        ++ [movImmI (regName (b.depth + cs.length)) 1,
          movImmI (regName (b.depth + cs.length + 1)) 0,
          (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
            [.reg fname, .reg (regName (b.depth + cs.length)),
              .reg (regName (b.depth + cs.length + 1))], .reg none)]
        ++ parMoves b.depth (carriedRegs d cs.length) b.res.tail
        ++ [guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
          [.reg (regName (b.depth + cs.length)), .imm 0])])
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by
        simp only [List.length_append, parMoves_length, carriedRegs_length, List.length_tail,
          hreslen, List.length_cons, List.length_nil]
        omega)
  have hl : findLabelMem n P.body = some A.length := by
    rw [hbody]
    exact findLabelMem_append_labelI n A _ ((findLabelMem_eq_none_iff n A).mp (hA n le_rfl))
  intro f
  induction f with
  | zero =>
      intro acc accN m h
      rw [NFProg.whileIter_zero] at h
      cases h
  | succ f ih =>
      intro acc accN m h hat hag hblk
      have h' : (body.denote fuel (hvAppend acc V)).bind (fun r =>
          if HasBoolBit.toBool (d := jasminDialect) r.head then
            NFProg.whileIter (d := jasminDialect)
              (fun acc => body.denote fuel (hvAppend acc V)) f r.tail
          else some r.tail) = some accN := h
      obtain ⟨r, hden, hrest⟩ := Option.bind_eq_some_iff.mp h'
      obtain ⟨k, t, hs, hat2, hfr, hz, hblk'⟩ :=
        whileLoop_trip nArgs fn body hcs hsim hb hlen harg hfn hbody hfh hR hA fuel V acc r m
          hden hat hag hblk
      by_cases hbt : HasBoolBit.toBool (d := jasminDialect) r.head = true
      · rw [if_pos hbt] at hrest
        obtain ⟨hs', hat'⟩ := steps_cc_taken hcc hat2 hfetch (by rw [hz, hbt]; rfl) hl
        have hfr' : RegionFrame d n m.prog.base (goto t (A.length + 1)).prog.base :=
          hfr.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
        obtain ⟨k', m', hs'', hat'', hfr'', hblk''⟩ := ih r.tail accN (goto t (A.length + 1))
          hrest hat' (StoreAgreesM.of_regionFrame hlen hag hfr') (fun {w} u => hblk' u)
        exact ⟨k + 1 + k', m', (hs.trans hs').trans hs'', hat'',
          hfr'.trans hfr'' le_rfl le_rfl, fun {w} u => hblk'' u⟩
      · rw [if_neg hbt] at hrest
        obtain rfl : r.tail = accN := Option.some.inj hrest
        obtain ⟨hs', hat'⟩ := steps_cc_fall hcc hat2 hfetch
          (by rw [hz, Bool.not_eq_true] at *; rw [hbt]; decide)
        exact ⟨k + 1, next t, hs.trans hs', hat', hfr, fun {w} u => hblk' u⟩

end WhileLoop

/-- **The frame rule of an exit-flag loop.** For carried types held in register cells, the
    statement for the body and for the continuation gives the statement for the loop. -/
theorem whileFrame_sim (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
    {ts : List JasminTy} (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ Γ) (JasminTy.reg 1 :: cs))
    (k : NFProg jasminDialect (cs ++ Γ) ts) (hcs : RegTys cs)
    (hbsim : ExportRSim nArgs fn body) (hksim : ExportRSim nArgs fn k) :
    ExportRSim nArgs fn (NFProg.whileLoop inits body k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V v m hden hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rk, hrk, rfl⟩ := h
  rw [NFProg.denote_whileLoop] at hden
  obtain ⟨accN, hiter, hkden⟩ := Option.bind_eq_some_iff.mp hden
  have hbody0 := hbody
  have hLab := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ _ hb
  have hreslen := exportR_res_length nArgs fn body _ _ _ hb
  have hisreg := exportR_res_isReg nArgs fn body _ _ _ hb
  obtain ⟨fname, hfh⟩ : ∃ fname, b.res.headD (.imm 0) = .reg fname := by
    cases hres : b.res with
    | nil => rw [hres] at hreslen; simp at hreslen
    | cons o rest => exact ⟨operandName o, hisreg o (by rw [hres]; exact List.mem_cons_self)⟩
  have htail : b.res.tail.length = cs.length := by
    rw [List.length_tail, hreslen]
    rfl
  obtain ⟨ops, hops⟩ : ∃ ops, ops = exprArgsHV d nArgs argName (fun _ => none) inits := ⟨_, rfl⟩
  have hopslen : ops.length = cs.length := by rw [hops, exprArgsHV_length]
  have hopsreg := exprArgsHV_reg nArgs hlen inits
  rw [← hops] at hopsreg
  -- the layout of the body
  obtain ⟨T, hT⟩ : ∃ T, T = movImmI (regName (b.depth + cs.length)) 1
      :: movImmI (regName (b.depth + cs.length + 1)) 0
      :: (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
        [.reg fname, .reg (regName (b.depth + cs.length)),
          .reg (regName (b.depth + cs.length + 1))], .reg none)
      :: (parMoves b.depth (carriedRegs d cs.length) b.res.tail
        ++ [guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
          [.reg (regName (b.depth + cs.length)), .imm 0]), condI (.reg "NZ") n]) := ⟨_, rfl⟩
  have hTlen : T.length = 2 * cs.length + 4 + 1 := by
    rw [hT]
    simp only [List.length_cons, List.length_append, parMoves_length, carriedRegs_length,
      htail, List.length_nil]
    omega
  have hTlabs : labelsOf T = [] := by
    rw [hT]
    show labelsOf (parMoves b.depth (carriedRegs d cs.length) b.res.tail ++ [_, _]) = []
    rw [labelsOf_append, labelsOf_parMoves]
    rfl
  have hF : whileFrame d n cs.length ops b.code (.reg fname) b.res.tail b.depth
      = seedMoves (carriedRegs d cs.length) ops ++ labelI n :: (b.code ++ T) := by
    rw [hT]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hfh, ← hops, hF]
    at hbody
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ seedMoves (carriedRegs d cs.length) ops := ⟨_, rfl⟩
  have hbodyL : P.body = A ++ labelI n :: (b.code ++ (T ++ (rk.code ++ post))) := by
    rw [hbody, hAd]
    simp only [List.append_assoc, List.cons_append]
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, labelsOf_append, labelsOf_seedMoves, List.append_nil]
  have hAlab : ∀ l, n ≤ l → findLabelMem l A = none := fun l hl => by
    rw [findLabelMem_eq_none_iff, hAlabs, ← findLabelMem_eq_none_iff]
    exact hpre l hl
  have hcar := carriedRegs_length d cs.length
  -- the seeds
  have hbodyS : P.body = pre ++ (List.range cs.length).map (fun j =>
      movI ((carriedRegs d cs.length).getD j "") (.reg (operandName (ops.getD j (.imm 0)))))
      ++ labelI n :: (b.code ++ (T ++ (rk.code ++ post))) := by
    rw [hbodyL, hAd, seedMoves_eq_range _ _ (by rw [hopslen, hcar])
      (fun o ho => (hopsreg o ho).1), hcar]
  obtain ⟨t0, hs0, hat0, ha0, hm0, ho0⟩ := steps_moves P
    (fun j => (carriedRegs d cs.length).getD j "")
    (fun j => operandName (ops.getD j (.imm 0))) cs.length pre _ m hbodyS hat
    (fun i j hij hj => getD_ne_of_nodup (carriedRegs_nodup _ _) hij (by rw [hcar]; exact hj))
    (fun i j hij hj he => by
      rw [carriedRegs_getD _ _ _ (by omega)] at he
      exact (hopsreg _ (getD_mem_of_lt _ (hopslen ▸ hj))).2 _ (by omega) he)
  have hAlen : A.length = pre.length + cs.length := by
    rw [hAd, List.length_append]
    simp only [seedMoves, List.length_map, List.length_zip, hcar, hopslen, Nat.min_self]
  rw [← hAlen] at hat0
  obtain ⟨hs1, hat1⟩ := steps_label x86Isa (kind := .internal) (l := n) (tag := .reg none)
    hat0 (fetch_of_body hbodyL rfl)
  have hfr1 : RegionFrame d n m.prog.base (next t0).prog.base :=
    RegionFrame.of_cells ha0 fun r hr _ => ho0 r fun j hj => by
      rw [carriedRegs_getD _ _ _ hj]
      exact hr _ (by omega)
  have hblkI : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      (next t0).prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup (Expr.lookupArgs inits V)) := fun {w} u => by
    have hu := JasminLsemSimulation.varIndex_lt u
    have h1 := hm0 (varIndex u) hu
    rw [carriedRegs_getD _ _ _ hu] at h1
    rw [show (next t0).prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = t0.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w from rfl,
      getW_of_lvm_eq w h1, hops, exprArgsHV_getD, ← evalOperandN_resolveVar, lookup_lookupArgs]
    exact hag.1 (hvToHom inits u)
  -- the trips
  obtain ⟨k3, m3, hs3, hat3, hfr3, hblk3⟩ :=
    whileLoop_trips nArgs fn body hcs hbsim hb hlen harg hfn hbodyL hfh
      (Z := rk.code ++ post) (by rw [hT]; simp only [List.append_assoc, List.cons_append,
        List.nil_append]) hAlab fuel V fuel (Expr.lookupArgs inits V) accN (next t0) hiter hat1
      (StoreAgreesM.of_regionFrame hlen hag hfr1) (fun {w} u => hblkI u)
  have hfrS : RegionFrame d n m.prog.base m3.prog.base := hfr1.trans hfr3 le_rfl le_rfl
  have hagS : StoreAgreesM nArgs (d + cs.length) m3.prog.base (hvAppend accN V) :=
    storeAgreesM_append hcs harg (StoreAgreesM.of_regionFrame hlen hag hfrS)
      (fun {w} u => hblk3 u)
  -- the continuation
  have hnext := hLab.le
  obtain ⟨kK, m', hsK, hatK, hresK, hfrK⟩ := hksim (d + cs.length) b.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P
    (A ++ labelI n :: (b.code ++ T)) post hfn
    (by rw [hbodyL]; simp only [List.append_assoc, List.cons_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append, hAlabs, labelsOf_cons_labelI,
        labelsOf_append, hTlabs, List.append_nil]
      simp only [List.mem_append, List.mem_cons, not_or]
      refine ⟨(findLabelMem_eq_none_iff l pre).mp (hpre l (by omega)), fun he => ?_,
        fun hm => ?_⟩
      · have : (l : Nat) = n := he
        omega
      · have := hLab.range _ hm
        omega)
    fuel _ v m3 hkden
    (by
      simp only [List.length_append, List.length_cons, hTlen] at hat3 ⊢
      rwa [show A.length + (b.code.length + (2 * cs.length + 4 + 1) + 1)
        = A.length + (b.code.length + 1) + 2 * cs.length + 4 + 1 by omega])
    hagS
  have hlenEq : pre.length + (Exported.prepend (whileFrame d n cs.length
      (exprArgsHV d nArgs argName (fun _ => none) inits) b.code (b.res.headD (.imm 0))
      b.res.tail b.depth) rk).code.length
      = (A ++ labelI n :: (b.code ++ T)).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyL] at h1
    simp only [List.length_append, List.length_cons] at h1 ⊢
    omega
  refine ⟨_, m', (((hs0.trans hs1).trans hs3).trans hsK), ?_, hresK,
    hfrS.trans hfrK (by omega) (by omega)⟩
  rw [hlenEq]
  exact hatK

/-! ## 18. The branch -/

/-- **The assignment of the results of a region.** From a state that agrees with the
    returned operands `ops` at the value `rv` at depth `D`, the parallel assignment of `ops`
    to the block `carriedRegs d rs.length` through the temporaries from
    `regName (D + rs.length)` puts `rv` in the block, within the frame of the depth `d` at
    every label. -/
theorem resMoves_steps {P : LprogM} {nArgs d D : Nat} {rs : Ctxt jasminDialect}
    {ops : List LOperand} (pre post : List LinstrRM) (s : LstateMF)
    {rv : Ctxt.Valuation rs}
    (hbody : P.body = pre ++ parMoves (D + rs.length) (carriedRegs d rs.length) ops ++ post)
    (hat : atPc P pre.length s) (hD : d ≤ D) (hres : ResAgrees nArgs D s.prog.base ops rv) :
    ∃ t, Steps x86Isa P (2 * rs.length) s t ∧ atPc P (pre.length + 2 * rs.length) t
      ∧ (∀ n, RegionFrame d n s.prog.base t.prog.base)
      ∧ (∀ {w : Nat} (u : Ctxt.Var rs (.reg w)),
          t.prog.base.reg.getW (regName (d + (rs.length - 1 - varIndex u))) w
            = some (u.lookup rv)) := by
  obtain ⟨Δ, W, vs, hΔ, hagW, hops, hrv⟩ := hres
  have hcar := carriedRegs_length d rs.length
  obtain ⟨t, hs, hat', harr, hm, ho⟩ := steps_parMoves (D + rs.length)
    (carriedRegs d rs.length) ops pre post s hbody hat
    (by rw [hops, exprArgsHV_length, hcar])
    (fun o ho => by
      rw [hops] at ho
      exact ⟨(exprArgsHV_reg nArgs hΔ vs o ho).1,
        fun k hk => (exprArgsHV_reg nArgs hΔ vs o ho).2 k (by omega)⟩)
    (carriedRegs_nodup _ _) (fun r hr k hk => carriedRegs_ne_regName hr k (by omega))
  rw [hcar] at hs hat' hm ho
  refine ⟨t, hs, hat', fun n => RegionFrame.of_cells harr fun r hr _ => ?_, fun {w} u => ?_⟩
  · exact ho r (fun hm' => by
        obtain ⟨j, _, he⟩ := mem_carriedRegs.mp hm'
        exact hr _ (by omega) he)
      (fun j _ => hr _ (by omega))
  · have hu := JasminLsemSimulation.varIndex_lt u
    have h1 := hm (varIndex u) hu
    rw [carriedRegs_getD _ _ _ hu] at h1
    rw [getW_of_lvm_eq w h1, hops, exprArgsHV_getD, ← evalOperandN_resolveVar, hrv,
      lookup_lookupArgs]
    exact hagW.1 (hvToHom vs u)

/-- **The head of a branch**: the widening of the condition bit into `regName d` and the
    compare of the word with zero. The zero flag is the negation of the bit, and the state
    is within the frame of the depth `d` at every label. -/
theorem ifHead_steps {P : LprogM} {d : Nat} {f : String} (pre post : List LinstrRM)
    (s : LstateMF) {bit : BitVec 1}
    (hbody : P.body = pre ++ (movImmI (regName d) 1 :: movImmI (regName (d + 1)) 0
      :: (.Lopn [.reg (regName d)] (withWidthTag 64 "CMOV")
        [.reg f, .reg (regName d), .reg (regName (d + 1))], .reg none)
      :: guardI (.Lopn [.reg (regName d)] (withWidthTag 64 "CMP") [.reg (regName d), .imm 0])
      :: post))
    (hat : atPc P pre.length s) (hf : ∀ k, d ≤ k → f ≠ regName k)
    (hbit : s.prog.base.reg.lvm f = ⟨1, bit⟩) :
    ∃ t, Steps x86Isa P 4 s t ∧ atPc P (pre.length + 4) t ∧ t.zf = !decide (bit = 1#1)
      ∧ ∀ n, RegionFrame d n s.prog.base t.prog.base := by
  obtain ⟨t3, hs3, hat3, ha3, hflag3, ho3⟩ := flagWord_steps (r := regName d)
    (z := regName (d + 1)) (f := f) pre _ s hbody hat
    (fun he => by have := JasminLsemSimulation.regName_injective he; omega) (hf _ le_rfl)
    (hf _ (by omega)) hbit
  obtain ⟨t4, hs4, hat4, ha4, hm4, hz4⟩ := steps_cmpZero (r := regName d)
    (v := selectW bit (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)) hat3
    (fetch_of_body (xs := pre ++ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0,
        (.Lopn [.reg (regName d)] (withWidthTag 64 "CMOV")
          [.reg f, .reg (regName d), .reg (regName (d + 1))], .reg none)])
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append]; rfl))
    hflag3
  refine ⟨t4, hs3.trans hs4, hat4, ?_,
    fun n => RegionFrame.of_cells (ha4.trans ha3) fun r hr _ => ?_⟩
  · rw [hz4]
    unfold selectW
    by_cases hb : bit = 1#1 <;> simp [hb]
  · rw [hm4]
    exact ho3 r (hr _ le_rfl) (hr _ (by omega))

/-- **The frame rule of a branch.** For result types held in register cells, the statement
    for the two branches and for the continuation gives the statement for the branch. -/
theorem ifFrame_sim (nArgs : Nat) (fn : String) {Γ rs : Ctxt jasminDialect}
    {ts : List JasminTy} (cond : Ctxt.Var Γ (JasminTy.reg 1))
    (thn els : NFProg jasminDialect Γ rs) (k : NFProg jasminDialect (rs ++ Γ) ts)
    (hrs : RegTys rs) (htsim : ExportRSim nArgs fn thn) (hesim : ExportRSim nArgs fn els)
    (hksim : ExportRSim nArgs fn k) :
    ExportRSim nArgs fn (NFProg.ifThenElse cond thn els k) := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V v m hden hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, e, he, rk, hrk, rfl⟩ := h
  rw [NFProg.denote_ifThenElse] at hden
  obtain ⟨rv, hbr, hkden⟩ := Option.bind_eq_some_iff.mp hden
  have hbody0 := hbody
  have hLT := exportR_labelsOK nArgs fn x86Data_guardsPlain thn _ _ _ ht
  have hLE := exportR_labelsOK nArgs fn x86Data_guardsPlain els _ _ _ he
  have hTle := hLT.le
  have hEle := hLE.le
  have htd := exportR_depth_le nArgs fn thn _ _ _ ht
  have hed := exportR_depth_le nArgs fn els _ _ _ he
  have htl := exportR_res_length nArgs fn thn _ _ _ ht
  have hel := exportR_res_length nArgs fn els _ _ _ he
  -- the condition
  obtain ⟨cn, hcn⟩ : ∃ cn, cn = operandName (resolveVar d nArgs argName (fun _ => none) cond) :=
    ⟨_, rfl⟩
  have hcreg : resolveVar d nArgs argName (fun _ => none) cond = .reg cn := by
    rw [hcn]
    exact resolveVar_isReg cond
  have hbit : m.prog.base.reg.lvm cn = ⟨1, cond.lookup V⟩ := by
    have := hag.1 cond
    rw [evalOperandN_resolveVar, ← hcn] at this
    exact getW_eq_some_iff.mp this
  have hcnk : ∀ k, d ≤ k → cn ≠ regName k := fun k hk => by
    rw [hcn]
    exact resolveVar_operandName_ne_regName cond
      (hlen ▸ JasminLsemSimulation.varIndex_lt cond) k hk
  -- the layout of the body
  obtain ⟨cmov, hcmov⟩ : ∃ cmov : LinstrRM, cmov = (.Lopn [.reg (regName d)]
      (withWidthTag 64 "CMOV") [.reg cn, .reg (regName d), .reg (regName (d + 1))], .reg none) :=
    ⟨_, rfl⟩
  obtain ⟨cmp, hcmp⟩ : ∃ cmp, cmp = guardI (.Lopn [.reg (regName d)] (withWidthTag 64 "CMP")
      [.reg (regName d), .imm 0]) := ⟨_, rfl⟩
  obtain ⟨TM, hTM⟩ : ∃ TM, TM = parMoves (t.depth + rs.length) (carriedRegs d rs.length) t.res :=
    ⟨_, rfl⟩
  obtain ⟨EM, hEM⟩ : ∃ EM, EM = parMoves (e.depth + rs.length) (carriedRegs d rs.length) e.res :=
    ⟨_, rfl⟩
  have hTMlen : TM.length = 2 * rs.length := by
    rw [hTM, parMoves_length, htl, carriedRegs_length]
    omega
  have hEMlen : EM.length = 2 * rs.length := by
    rw [hEM, parMoves_length, hel, carriedRegs_length]
    omega
  have hTMlab : labelsOf TM = [] := by rw [hTM]; exact labelsOf_parMoves _ _ _
  have hEMlab : labelsOf EM = [] := by rw [hEM]; exact labelsOf_parMoves _ _ _
  have hF : ifFrame fn d n rs.length (.reg cn) t.code t.res t.depth e.code e.res e.depth
      = movImmI (regName d) 1 :: movImmI (regName (d + 1)) 0 :: cmov :: cmp
        :: condI (.reg "Z") (n + 1) :: labelI n :: (t.code ++ (TM ++ (gotoI fn (n + 2)
        :: labelI (n + 1) :: (e.code ++ (EM ++ [labelI (n + 2)]))))) := by
    rw [hcmov, hcmp, hTM, hEM]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hcreg, hF]
    at hbody
  have hbodyH : P.body = pre ++ (movImmI (regName d) 1 :: movImmI (regName (d + 1)) 0 :: cmov
      :: cmp :: condI (.reg "Z") (n + 1) :: labelI n :: (t.code ++ (TM ++ (gotoI fn (n + 2)
      :: labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post))))))) := by
    rw [hbody]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0, cmov,
      cmp, condI (.reg "Z") (n + 1)] := ⟨_, rfl⟩
  have hbodyA : P.body = A ++ labelI n :: (t.code ++ (TM ++ (gotoI fn (n + 2)
      :: labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post)))))) := by
    rw [hbodyH, hAd]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hAlen : A.length = pre.length + 4 + 1 := by
    rw [hAd, List.length_append]
    rfl
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, hcmov, hcmp, labelsOf_append]
    exact List.append_nil _
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = A ++ labelI n :: (t.code ++ (TM ++ [gotoI fn (n + 2)])) := ⟨_, rfl⟩
  have hbodyY : P.body = Y ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2)
      :: (rk.code ++ post))) := by
    rw [hbodyA, hYd]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hYlabs : labelsOf Y = labelsOf pre ++ n :: labelsOf t.code := by
    simp only [hYd, labelsOf_append, hAlabs, labelsOf_cons_labelI, labelsOf_cons_gotoI, hTMlab,
      labelsOf_nil, List.append_nil]
  obtain ⟨X, hXd⟩ : ∃ X, X = Y ++ labelI (n + 1) :: (e.code ++ EM) := ⟨_, rfl⟩
  have hbodyX : P.body = X ++ labelI (n + 2) :: (rk.code ++ post) := by
    rw [hbodyY, hXd]
    simp only [List.append_assoc, List.cons_append]
  have hXlabs : labelsOf X
      = labelsOf pre ++ n :: (labelsOf t.code ++ (n + 1) :: labelsOf e.code) := by
    simp only [hXd, labelsOf_append, hYlabs, labelsOf_cons_labelI, hEMlab, List.append_nil,
      List.append_assoc, List.cons_append]
  have hXlen : X.length = (Y ++ labelI (n + 1) :: e.code).length + 2 * rs.length := by
    rw [hXd]
    simp only [List.length_append, List.length_cons, hEMlen]
    omega
  have hpreL : ∀ l, n ≤ l → l ∉ labelsOf pre := fun l hl =>
    (findLabelMem_eq_none_iff l pre).mp (hpre l hl)
  have hYnot : ∀ l : Nat, n + 1 ≤ l → l ∉ labelsOf t.code → l ∉ labelsOf Y := by
    intro l hl ht' hm
    rw [hYlabs, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm
    · exact hpreL l (by omega) hm
    · omega
    · exact ht' hm
  have hXnot : ∀ l : Nat, n + 2 ≤ l → l ∉ labelsOf t.code → l ∉ labelsOf e.code →
      l ∉ labelsOf X := by
    intro l hl ht' he' hm
    rw [hXlabs, List.mem_append, List.mem_cons, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm | hm | hm
    · exact hpreL l (by omega) hm
    · omega
    · exact ht' hm
    · omega
    · exact he' hm
  have hl1 : findLabelMem (n + 1) P.body = some Y.length := by
    rw [hbodyY]
    exact findLabelMem_append_labelI (n + 1) Y _
      (hYnot (n + 1) le_rfl fun hm => by have := hLT.range _ hm; omega)
  have hl2 : findLabelMem (n + 2) P.body = some X.length := by
    rw [hbodyX]
    exact findLabelMem_append_labelI (n + 2) X _
      (hXnot (n + 2) le_rfl (fun hm => by have := hLT.range _ hm; omega)
        fun hm => by have := hLE.range _ hm; omega)
  -- the head
  obtain ⟨t0, hs0, hat0, hz0, hfr0⟩ := ifHead_steps (d := d) (f := cn) pre _ m
    (bit := cond.lookup V) (by rw [hbodyH, hcmov, hcmp]) hat hcnk hbit
  have hz0' : t0.zf = !(HasBoolBit.toBool (d := jasminDialect) (cond.lookup V)) := hz0
  have hfetchZ : P.body[pre.length + 4]? = some (condI (.reg "Z") (n + 1)) :=
    fetch_of_body (xs := pre ++ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0, cmov, cmp])
      (by rw [hbodyH]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append]; rfl)
  -- the selected branch, to the counter after the join label
  have hjoin : ∃ (kJ : Nat) (mJ : LstateMF), Steps x86Isa P kJ m mJ ∧ atPc P (X.length + 1) mJ
      ∧ RegionFrame d n m.prog.base mJ.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var rs (.reg w)),
          mJ.prog.base.reg.getW (regName (d + (rs.length - 1 - varIndex u))) w
            = some (u.lookup rv)) := by
    by_cases hbt : HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) = true
    · rw [if_pos hbt] at hbr
      obtain ⟨hs1, hat1⟩ := steps_cc_fall (pol := true) rfl hat0 hfetchZ
        (by rw [hz0', hbt]; decide)
      rw [← hAlen] at hat1
      obtain ⟨hs2, hat2⟩ := steps_label x86Isa (kind := .internal) (l := n) (tag := .reg none)
        hat1 (fetch_of_body hbodyA rfl)
      have hfr2 : RegionFrame d n m.prog.base (next (next t0)).prog.base :=
        (hfr0 n).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      obtain ⟨k3, m3, hs3, hat3, hres3, hfr3⟩ := htsim d (n + 3) t ht hlen harg P
        (A ++ [labelI n]) (TM ++ (gotoI fn (n + 2) :: labelI (n + 1) :: (e.code ++ (EM
          ++ labelI (n + 2) :: (rk.code ++ post))))) hfn
        (by rw [hbodyA]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        (fun l hl => by
          rw [findLabelMem_eq_none_iff, labelsOf_append, hAlabs]
          simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
            not_or]
          exact ⟨hpreL l (by omega), fun he => by have : (l : Nat) = n := he; omega⟩)
        fuel V rv (next (next t0)) hbr
        (by rw [List.length_append, List.length_singleton]; exact hat2)
        (StoreAgreesM.of_regionFrame hlen hag hfr2)
      have hat3' : atPc P (A ++ labelI n :: t.code).length m3 := by
        rw [List.length_append, List.length_singleton] at hat3
        rw [List.length_append, List.length_cons]
        rwa [show A.length + (t.code.length + 1) = A.length + 1 + t.code.length by omega]
      obtain ⟨m4, hs4, hat4, hfr4, hblk4⟩ := resMoves_steps (nArgs := nArgs) (d := d)
        (D := t.depth) (rs := rs) (ops := t.res) (A ++ labelI n :: t.code)
        (gotoI fn (n + 2) :: labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2)
          :: (rk.code ++ post)))) m3 (rv := rv)
        (by rw [hbodyA, hTM]; simp only [List.append_assoc, List.cons_append])
        hat3' htd hres3
      obtain ⟨hs5, -⟩ := steps_goto x86Isa (l := n + 2) (tag := .reg none) hat4
        (fetch_of_body (xs := A ++ labelI n :: (t.code ++ TM)) (i := gotoI P.lfn (n + 2))
          (by rw [hbodyA, hfn]; simp only [List.append_assoc, List.cons_append]; rfl)
          (by simp only [List.length_append, List.length_cons, hTMlen]; omega))
        hl2
      exact ⟨_, _, ((((hs0.trans hs1).trans hs2).trans hs3).trans hs4).trans hs5,
        atPc_goto (X.length + 1) hat4,
        (((hfr2.trans hfr3 le_rfl (by omega)).trans (hfr4 n) le_rfl le_rfl).trans
          (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl),
        fun {w} u => hblk4 u⟩
    · rw [if_neg hbt] at hbr
      rw [Bool.not_eq_true] at hbt
      obtain ⟨hs1, hat1⟩ := steps_cc_taken (pol := true) rfl hat0 hfetchZ
        (by rw [hz0', hbt]; rfl) hl1
      have hfr1 : RegionFrame d n m.prog.base (goto t0 (Y.length + 1)).prog.base :=
        (hfr0 n).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      obtain ⟨k3, m3, hs3, hat3, hres3, hfr3⟩ := hesim d t.next e he hlen harg P
        (Y ++ [labelI (n + 1)]) (EM ++ labelI (n + 2) :: (rk.code ++ post)) hfn
        (by rw [hbodyY]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        (fun l hl => by
          rw [findLabelMem_eq_none_iff, labelsOf_append]
          simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
            not_or]
          exact ⟨hYnot l (by omega) fun hm => by have := hLT.range l hm; omega,
            fun he => by have : (l : Nat) = n + 1 := he; omega⟩)
        fuel V rv (goto t0 (Y.length + 1)) hbr
        (by rw [List.length_append, List.length_singleton]; exact hat1)
        (StoreAgreesM.of_regionFrame hlen hag hfr1)
      have hat3' : atPc P (Y ++ labelI (n + 1) :: e.code).length m3 := by
        rw [List.length_append, List.length_singleton] at hat3
        rw [List.length_append, List.length_cons]
        rwa [show Y.length + (e.code.length + 1) = Y.length + 1 + e.code.length by omega]
      obtain ⟨m4, hs4, hat4, hfr4, hblk4⟩ := resMoves_steps (nArgs := nArgs) (d := d)
        (D := e.depth) (rs := rs) (ops := e.res) (Y ++ labelI (n + 1) :: e.code)
        (labelI (n + 2) :: (rk.code ++ post)) m3 (rv := rv)
        (by rw [hbodyY, hEM]; simp only [List.append_assoc, List.cons_append])
        hat3' hed hres3
      rw [← hXlen] at hat4
      obtain ⟨hs5, hat5⟩ := steps_label x86Isa (kind := .internal) (l := n + 2)
        (tag := .reg none) hat4 (fetch_of_body hbodyX rfl)
      exact ⟨_, _, (((hs0.trans hs1).trans hs3).trans hs4).trans hs5, hat5,
        (((hfr1.trans hfr3 le_rfl (by omega)).trans (hfr4 n) le_rfl le_rfl).trans
          (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl),
        fun {w} u => hblk4 u⟩
  obtain ⟨kJ, mJ, hsJ, hatJ, hfrJ, hblkJ⟩ := hjoin
  have hagJ : StoreAgreesM nArgs (d + rs.length) mJ.prog.base (hvAppend rv V) :=
    storeAgreesM_append hrs harg (StoreAgreesM.of_regionFrame hlen hag hfrJ)
      (fun {w} u => hblkJ u)
  -- the continuation
  obtain ⟨kK, m', hsK, hatK, hresK, hfrK⟩ := hksim (d + rs.length) e.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P (X ++ [labelI (n + 2)]) post hfn
    (by rw [hbodyX]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append]
      simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
        not_or]
      exact ⟨hXnot l (by omega) (fun hm => by have := hLT.range l hm; omega)
          fun hm => by have := hLE.range l hm; omega,
        fun he => by have : (l : Nat) = n + 2 := he; omega⟩)
    fuel _ v mJ hkden
    (by rw [List.length_append, List.length_singleton]; exact hatJ) hagJ
  have hlenEq : pre.length + (Exported.prepend (ifFrame fn d n rs.length
      (resolveVar d nArgs argName (fun _ => none) cond) t.code t.res t.depth e.code e.res
      e.depth) rk).code.length = (X ++ [labelI (n + 2)]).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyX] at h1
    simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
    omega
  refine ⟨kJ + kK, m', hsJ.trans hsK, ?_, hresK, hfrJ.trans hfrK (by omega) (by omega)⟩
  rw [hlenEq]
  exact hatK

/-! ## 19. The simulation of the export -/

/-- **The programs the region export simulates.** No node is a `call`, every binding is in
    the stack-memory fragment (`BindMemN`), and the carried types of every loop and the
    result types of every branch are held in register cells (`RegTys`). -/
def RegionExportable : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Prop
  | _, _, .ret _ => True
  | _, _, .var e k => BindMemN e ∧ RegionExportable k
  | _, _, .forLoop (cs := cs) _ _ body k =>
      RegTys cs ∧ RegionExportable body ∧ RegionExportable k
  | _, _, .ifThenElse (rs := rs) _ thn els k =>
      RegTys rs ∧ RegionExportable thn ∧ RegionExportable els ∧ RegionExportable k
  | _, _, .whileLoop (cs := cs) _ body k =>
      RegTys cs ∧ RegionExportable body ∧ RegionExportable k
  | _, _, .call _ _ _ => False

/-- **The simulation theorem of the region export.** Every program of `RegionExportable`
    satisfies the simulation statement, by the rules of the return, the binding, the two
    loops and the branch. -/
theorem exportR_sim (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p) : ExportRSim nArgs fn p := by
  induction p with
  | ret vs => exact exportRSim_ret nArgs fn vs
  | var e k ih => exact exportRSim_var nArgs fn e k hp.1 (ih hp.2)
  | forLoop count inits body k ihb ihk =>
      exact forFrame_sim nArgs fn count inits body k hp.1 (ihb hp.2.1) (ihk hp.2.2)
  | ifThenElse cond thn els k iht ihe ihk =>
      exact ifFrame_sim nArgs fn cond thn els k hp.1 (iht hp.2.1) (ihe hp.2.2.1) (ihk hp.2.2.2)
  | whileLoop inits body k ihb ihk =>
      exact whileFrame_sim nArgs fn inits body k hp.1 (ihb hp.2.1) (ihk hp.2.2)
  | call f args k _ => exact hp.elim

/-- **The export succeeds exactly on the programs without a `call`**, at every depth, label
    and instruction set. -/
theorem exportR_eq_some_iff (nArgs : Nat) (fn : String) {I : IsaData}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat), (∃ r, exportR nArgs fn p d n I = some r) ↔ p.callFree = true := by
  induction p with
  | ret vs => exact fun d n => ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | var e k ih =>
      intro d n
      simp only [exportR, Option.map_eq_some_iff, NFProg.callFree]
      rw [← ih (d + 1) n]
      exact ⟨fun ⟨_, rk, hk, _⟩ => ⟨rk, hk⟩, fun ⟨rk, hk⟩ => ⟨_, rk, hk, rfl⟩⟩
  | forLoop count inits body k ihb ihk =>
      intro d n
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff, NFProg.callFree,
        Bool.and_eq_true]
      refine ⟨fun ⟨_, b, hb, rk, hk, _⟩ => ⟨(ihb _ _).mp ⟨b, hb⟩, (ihk _ _).mp ⟨rk, hk⟩⟩,
        fun ⟨h1, h2⟩ => ?_⟩
      obtain ⟨b, hb⟩ := (ihb _ _).mpr h1
      obtain ⟨rk, hk⟩ := (ihk _ _).mpr h2
      exact ⟨_, b, hb, rk, hk, rfl⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff, NFProg.callFree,
        Bool.and_eq_true]
      refine ⟨fun ⟨_, t, ht, e, he, rk, hk, _⟩ =>
          ⟨⟨(iht _ _).mp ⟨t, ht⟩, (ihe _ _).mp ⟨e, he⟩⟩, (ihk _ _).mp ⟨rk, hk⟩⟩,
        fun ⟨⟨h1, h2⟩, h3⟩ => ?_⟩
      obtain ⟨t, ht⟩ := (iht _ _).mpr h1
      obtain ⟨e, he⟩ := (ihe _ _).mpr h2
      obtain ⟨rk, hk⟩ := (ihk _ _).mpr h3
      exact ⟨_, t, ht, e, he, rk, hk, rfl⟩
  | whileLoop inits body k ihb ihk =>
      intro d n
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff, NFProg.callFree,
        Bool.and_eq_true]
      refine ⟨fun ⟨_, b, hb, rk, hk, _⟩ => ⟨(ihb _ _).mp ⟨b, hb⟩, (ihk _ _).mp ⟨rk, hk⟩⟩,
        fun ⟨h1, h2⟩ => ?_⟩
      obtain ⟨b, hb⟩ := (ihb _ _).mpr h1
      obtain ⟨rk, hk⟩ := (ihk _ _).mpr h2
      exact ⟨_, b, hb, rk, hk, rfl⟩
  | call f args k _ =>
      intro d n
      simp [exportR, NFProg.callFree]

/-- **The export refuses exactly the programs with a `call`.** -/
theorem exportR_eq_none_iff (nArgs : Nat) (fn : String) {I : IsaData}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (d n : Nat) :
    exportR nArgs fn p d n I = none ↔ p.callFree = false := by
  rw [← Bool.not_eq_true, ← exportR_eq_some_iff nArgs fn (I := I) p d n,
    Option.eq_none_iff_forall_ne_some]
  exact ⟨fun h ⟨r, hr⟩ => h r hr, fun h r hr => h ⟨r, hr⟩⟩

/-- A program of `RegionExportable` has no `call`. -/
theorem RegionExportable.callFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p) : p.callFree = true := by
  induction p with
  | ret vs => rfl
  | var e k ih => exact ih hp.2
  | forLoop count inits body k ihb ihk =>
      exact Bool.and_eq_true_iff.mpr ⟨ihb hp.2.1, ihk hp.2.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      exact Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr ⟨iht hp.2.1, ihe hp.2.2.1⟩, ihk hp.2.2.2⟩
  | whileLoop inits body k ihb ihk =>
      exact Bool.and_eq_true_iff.mpr ⟨ihb hp.2.1, ihk hp.2.2⟩
  | call f args k _ => exact hp.elim

/-- **The export of a program of `RegionExportable` succeeds.** -/
theorem RegionExportable.exportR_eq_some {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p) (nArgs : Nat) (fn : String)
    (d n : Nat) (I : IsaData := x86Data) : ∃ r, exportR nArgs fn p d n I = some r :=
  (exportR_eq_some_iff nArgs fn p d n).mpr hp.callFree

/-! ## 20. The run of an export under the fuelled semantics -/

/-- **The export as a whole body halts under `lsemFuelMemF`.** For a program satisfying the
    simulation statement, the code of its export as the body of a one-function program,
    run by the fuelled flag-machine interpreter from a state at counter `0` whose store
    agrees with `V`, halts at every fuel from some bound on, in a state that agrees with
    the returned operands at the denotation and differs from the entry state within the
    frame of the region. -/
theorem exportRSim_lsemFuelMemF {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hsim : ExportRSim nArgs fn p)
    {d n : Nat} {r : Exported} (hr : exportR nArgs fn p d n = some r) (hlen : Γ.length = d)
    (harg : nArgs ≤ d) (fuel : Nat) (V : Ctxt.Valuation Γ)
    (v : Ctxt.Valuation (d := jasminDialect) ts) (hden : p.denote fuel V = some v)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (hag : StoreAgreesM nArgs d b0 V) :
    ∃ (k : Nat) (t : LstateMF),
      (∀ j, lsemFuelMemF (singletonProgM fn r.code) (k + j)
        { prog := { base := b0, lfn := fn }, zf := zf } = some t)
      ∧ ResAgrees nArgs r.depth t.prog.base r.res v ∧ RegionFrame d n b0 t.prog.base := by
  obtain ⟨k, t, hs, hat, hres, hfr⟩ := hsim d n r hr hlen harg (singletonProgM fn r.code) [] []
    rfl (by rw [List.nil_append, List.append_nil]; rfl)
    (fun l _ => (findLabelMem_eq_none_iff l []).mpr (by simp)) fuel V v
    { prog := { base := b0, lfn := fn }, zf := zf } hden ⟨rfl, hpc⟩ hag
  refine ⟨k, t, fun j => ?_, hres, hfr⟩
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF]
  exact lsemFuelMemF_of_steps x86Isa _ hs
    (halted_of_atPc hat (by rw [List.length_nil, Nat.zero_add]; exact le_rfl)) j

/-- **The run of a whole program.** A program of `RegionExportable` over the argument
    context `Γ` has an export from the depth `Γ.length` and the label `0`, the export
    `exportRBody` projects to the wire. Its code as the body of a one-function program, run
    by `lsemFuelMemF` from a state at counter `0` whose store agrees with the arguments `V`,
    halts at every fuel from some bound on whenever the program denotes `v` at `V`, in a
    state that agrees with the returned operands at `v` and reads as the entry state at
    every argument register. -/
theorem exportR_lsemFuelMemF (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p) (fuel : Nat)
    (V : Ctxt.Valuation Γ) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (hden : p.denote fuel V = some v) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hag : StoreAgreesM Γ.length Γ.length b0 V) :
    ∃ r, exportR Γ.length fn p Γ.length 0 = some r ∧ ∃ (k : Nat) (t : LstateMF),
      (∀ j, lsemFuelMemF (singletonProgM fn r.code) (k + j)
        { prog := { base := b0, lfn := fn }, zf := zf } = some t)
      ∧ ResAgrees Γ.length r.depth t.prog.base r.res v
      ∧ RegionFrame Γ.length 0 b0 t.prog.base := by
  obtain ⟨r, hr⟩ := hp.exportR_eq_some Γ.length fn Γ.length 0
  exact ⟨r, hr, exportRSim_lsemFuelMemF (exportR_sim Γ.length fn hp) hr rfl le_rfl fuel V v hden
    b0 zf hpc hag⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
