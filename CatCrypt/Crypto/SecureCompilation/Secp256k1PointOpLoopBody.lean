/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop

/-!
# The secp256k1 Jacobian point-op step in the counted-loop body context

`Secp256k1PointOpFront` builds `jacDbl` / `jacAdd` as WHOLE-OP fronts over the
outer argument context `[P, out]` / `[P2, P1, out]`. `ComL.forLoopNRt` consumes a
per-trip body of type `Com jasminDialect (accTy :: .reg 64 :: invTys) accTy`
(`VIR/JasminLprogExport.lean`). This module states the point-op step in that
context and front-compiles it:

```
  ladderStepBody   (LowCT over Gbody = [.memref 12, .sword 64, .memref ND, .memref NT])
    --(translateDialectControl)--------> Com catCryptDialect Gbody (.memref 12)
    --(cryptoDialectToJasminCom)-------> Com jasminDialect (AP :: .reg 64 :: [AD, AT]) AP
    --(ComL.forLoopNRt)----------------> ComL Gouter AP   (one body copy + back-edge)
```

The reshape is a change of the body's binding context, not of the field
arithmetic: every brick is the phase-1 `Secp256k1FeMulFront` generator reused
through `Secp256k1PointOpFront.runSchedule`, and the front is the same
`translateDialectControl` + `cryptoDialectToJasminCom` pair.

## The loop-body context

```
  Gbody = .memref NP :: .sword 64 :: [.memref ND, .memref NT]
            accumulator   trip index    digit stream, table
```

* the accumulator is the 12-cell Jacobian point frame `X‖Y‖Z`, bound under the
  name `out` (the name `Secp256k1PointOpFront.storeField` writes to);
* the trip index is the `.sword 64` loop binder, bound as `t`, and is the
  `RArrLoad` index of the per-trip digit read;
* the digit stream `dig` (`ND` cells, one per trip) and the odd-multiple table
  `tbl` (`NT = 12 * ladderTableEntries` cells) are read-only invariants.

## The per-trip step

`ladderStepBody` is, in order: the reduction constants and the frame cell
indices; the accumulator load `out → (X, Y, Z)`; the `dbl-2009-l` schedule; the
digit read `dgt := dig[t]`; the masked table scan-select; the `add-2007-bl`
schedule on the doubled accumulator and the selected point; the accumulator
store.

The scan-select reads every table entry and combines them under an equality
mask, so the trip's memory trace is independent of the digit. The mask of entry
`e` is `((d ⊕ −d) ⊕ (d ∧ −d)) >>> 63 − 1` for `d = dgt ⊕ e`, which is all-ones
exactly when `dgt = e`; `⊕`/`∧` build the disjunction because `SExpr` has no
bitwise-or constructor.

The digit is read as an unsigned table index. Sign handling of a signed-digit
recoding is not part of this body.

## Gates

`ladderSelectBody` — the trip's operand-preparation phase, 497 `LowCT` commands
— is gated by `#guard`: the front accepts it and the emitted spine is a
`ComL.forLoopNRt` node. That covers the loop-body plumbing this module
introduces (the memref accumulator carried across the back-edge, the `RArrLoad`
at the loop binder, the constant-index table reads, the `VarMap` over
`Gbody`). The field bricks it composes with are gated at single-field-op scale
in `Secp256k1FeMulFront` and `Secp256k1PointOpFront`.

`dblStepBody` (3960 commands) and `ladderStepBody` (11730) carry no `#guard`:
evaluating the front over a body of that size exhausts the evaluator, measured
at ~30 s to termination on a 14 GB host.

`ladderProg_denote` states the rolled program's denotation as the
`JLoopBodyN.denote` fold of whatever the front compiles `ladderStepBody` to, and
carries the front-compilation as a hypothesis.

The value tie — that the emitted trip computes the point-op step of the `Nat`
spec `Secp256k1PointOpFront.jacDblSpec` / `jacAddSpec` — needs the scalar
front-preservation homomorphism recorded in `Secp256k1PointOpCompositional`, and
is not established here.

## Main results

* `Gbody`: the per-trip body context `accTy :: .sword 64 :: invTys`, whose
  `mapCtx` image is the `ComL.forLoopNRt` body shape.
* `ladderSelectBody`: the accumulator load, digit read at the loop binder,
  constant-time table scan-select and store, as covered `LowCT`.
* `ladderProg`, `ladderProg_denote`: the front-compiled loop node and its fold law.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpLoopBody

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (sv seqAll)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp constInit idxInit loadField storeField runSchedule jacDblSchedule jacAddSchedule)

/-! ## 1. Sizes -/

/-- Cells of a Jacobian point frame: `X‖Y‖Z`, four little-endian `u64` each. -/
abbrev NP : Nat := 12

/-- Odd-multiple table entries the per-trip scan-select ranges over. -/
abbrev ladderTableEntries : Nat := 8

/-- Cells of the odd-multiple table: `ladderTableEntries` point frames. -/
abbrev NT : Nat := NP * ladderTableEntries

/-- Cells of the digit stream: one `u64` digit per ladder trip. -/
abbrev ND : Nat := 129

/-! ## 2. The per-trip body as covered `LowCT` -/

/-- Bind the constant table cell indices `tix0 .. tix{NT-1}`. -/
def tblIdxInit : List LowCT :=
  (List.range NT).map (fun i => (.RScalarSetExpr s!"tix{i}" (.SLit i) : LowCT))

/-- Read the per-trip digit from the invariant stream at the loop binder `t`. -/
def digitRead : List LowCT :=
  [ (.RArrLoad ⟨"dgt", .TU64⟩ ⟨"dig", .TBytes (8 * ND)⟩ "t" : LowCT) ]

/-- The all-ones-iff-equal mask of table entry `e` against the digit `dgt`,
    bound as `msk{e}`. `d = dgt ⊕ e` and `n = −d`; `(d ⊕ n) ⊕ (d ∧ n)` is `d ∨ n`,
    whose top bit is set exactly when `d ≠ 0`, so the shifted bit minus one is
    all-ones exactly when `dgt = e`. -/
def entryMask (e : Nat) : List LowCT :=
  [ (.RScalarSetExpr s!"eqd{e}" (.SXor (sv "dgt") (.SLit e)) : LowCT)
  , (.RScalarSetExpr s!"eqn{e}" (.SSub (.SLit 0) (sv s!"eqd{e}")) : LowCT)
  , (.RScalarSetExpr s!"eqo{e}"
      (.SXor (.SXor (sv s!"eqd{e}") (sv s!"eqn{e}"))
             (.SAnd (sv s!"eqd{e}") (sv s!"eqn{e}"))) : LowCT)
  , (.RScalarSetExpr s!"eqb{e}" (.SShr (sv s!"eqo{e}") (.SLit 63)) : LowCT)
  , (.RScalarSetExpr s!"msk{e}" (.SSub (sv s!"eqb{e}") (.SLit 1)) : LowCT) ]

/-- The masked table scan-select: zero the twelve selected cells `selc0..selc11`,
    then for every table entry load its twelve cells, mask them with that entry's
    equality mask and fold them in. Every entry is read on every trip. -/
def scanSelect : List LowCT :=
  (List.range NP).map (fun c => (.RScalarSetExpr s!"selc{c}" (.SLit 0) : LowCT))
  ++ (List.range ladderTableEntries).flatMap (fun e =>
      entryMask e
      ++ (List.range NP).flatMap (fun c =>
          [ (.RArrLoad ⟨s!"tl{e}_{c}", .TU64⟩ ⟨"tbl", .TBytes (8 * NT)⟩
              s!"tix{NP * e + c}" : LowCT)
          , (.RScalarSetExpr s!"tm{e}_{c}"
              (.SAnd (sv s!"tl{e}_{c}") (sv s!"msk{e}")) : LowCT)
          , (.RScalarSetExpr s!"selc{c}"
              (.SXor (sv s!"selc{c}") (sv s!"tm{e}_{c}")) : LowCT) ]))

/-- Split the four selected `u64` cells at offset `o` into the eight 32-bit
    half-limbs of field element `fe`, the representation the field bricks read. -/
def splitSelected (o : Nat) (fe : String) : List LowCT :=
  (List.range 4).flatMap (fun j =>
    [ (.RScalarSetExpr s!"{fe}h{2*j}"
        (.SAnd (sv s!"selc{o + j}")
          (.SLit CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront.mask32)) : LowCT)
    , (.RScalarSetExpr s!"{fe}h{2*j+1}" (.SShr (sv s!"selc{o + j}") (.SLit 32)) : LowCT) ])

/-- Rename an `add-2007-bl` field-element name for the composed step: the first
    addend is the doubled accumulator (`X1/Y1/Z1 ↦ Xp/Yp/Zp`), the second is the
    scan-selected point (`X2/Y2/Z2 ↦ Sx/Sy/Sz`), and every other name is prefixed
    `a` so the add schedule's cells never collide with the doubling's. -/
def addName : String → String
  | "X1" => "Xp" | "Y1" => "Yp" | "Z1" => "Zp"
  | "X2" => "Sx" | "Y2" => "Sy" | "Z2" => "Sz"
  | n => "a" ++ n

/-- Apply `addName` to a field-op call. -/
def substFOp : FOp → FOp
  | .mul o a b => .mul (addName o) (addName a) (addName b)
  | .add o a b => .add (addName o) (addName a) (addName b)
  | .sub o a b => .sub (addName o) (addName a) (addName b)

/-- The composed field-op schedule of one ladder trip: the `dbl-2009-l` doubling
    of the accumulator, then the `add-2007-bl` addition of the scan-selected
    point to it. One `runSchedule` pass, so every brick gets a distinct private
    prefix. -/
def ladderStepSchedule : List FOp :=
  jacDblSchedule ++ jacAddSchedule.map substFOp

/-- The per-trip ladder body over `Gbody`: constants and cell indices, the
    accumulator load, the composed doubling/addition schedule with the digit read
    and scan-select between them, and the accumulator store. -/
def ladderStepBody : LowCT :=
  seqAll (idxInit ++ tblIdxInit ++ constInit
    ++ loadField (8 * NP) "out" 0 "X" ++ loadField (8 * NP) "out" 4 "Y"
    ++ loadField (8 * NP) "out" 8 "Z"
    ++ digitRead ++ scanSelect
    ++ splitSelected 0 "Sx" ++ splitSelected 4 "Sy" ++ splitSelected 8 "Sz"
    ++ runSchedule ladderStepSchedule
    ++ storeField (8 * NP) 0 "aXp" ++ storeField (8 * NP) 4 "aYp"
    ++ storeField (8 * NP) 8 "aZp")

/-- The operand-preparation phase of one trip, as a body in its own right: the
    accumulator load, the digit read at the loop binder, the masked table
    scan-select, and the store of the twelve selected cells into the accumulator
    frame. Carries the whole loop-body plumbing — the memref accumulator read and
    written across the back-edge, the `RArrLoad` at the loop binder, and the
    constant-index table reads — with no field arithmetic. -/
def ladderSelectBody : LowCT :=
  seqAll (idxInit ++ tblIdxInit
    ++ loadField (8 * NP) "out" 0 "X" ++ loadField (8 * NP) "out" 4 "Y"
    ++ loadField (8 * NP) "out" 8 "Z"
    ++ digitRead ++ scanSelect
    ++ (List.range NP).map (fun c =>
        (.RArrStore ⟨"out", .TBytes (8 * NP)⟩ s!"ix{c}" ⟨s!"selc{c}", .TU64⟩ : LowCT)))

/-- The doubling-only per-trip body: the same reshape without the digit read,
    scan-select and addition. -/
def dblStepBody : LowCT :=
  seqAll (idxInit ++ constInit
    ++ loadField (8 * NP) "out" 0 "X" ++ loadField (8 * NP) "out" 4 "Y"
    ++ loadField (8 * NP) "out" 8 "Z"
    ++ runSchedule jacDblSchedule
    ++ storeField (8 * NP) 0 "Xp" ++ storeField (8 * NP) 4 "Yp"
    ++ storeField (8 * NP) 8 "Zp")

/-! ## 3. The loop-body context and its `VarMap` -/

/-- The read-only loop invariants: the digit stream and the odd-multiple table. -/
def Ginv : Ctx := [.memref ND, .memref NT]

/-- The per-trip body context: accumulator point frame, trip index, invariants. -/
def Gbody : Ctx := .memref NP :: .sword 64 :: Ginv

/-- The body `VarMap`: `tbl` bound deepest, then `dig`, the trip index `t`, and
    the accumulator `out` at `.here`. -/
def vmBody : VarMap Gbody :=
  (((VarMap.empty.bind (t := .memref NT) "tbl").bind
      (t := .memref ND) "dig").bind
      (t := .sword 64) "t").bind (t := .memref NP) "out"

/-! ## 4. The outer context and the rolled loop -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The accumulator point frame as a jasmin type. -/
abbrev AP : JasminTy := .stackArr 64 NP

/-- The digit stream as a jasmin type. -/
abbrev AD : JasminTy := .stackArr 64 ND

/-- The odd-multiple table as a jasmin type. -/
abbrev AT : JasminTy := .stackArr 64 NT

/-- The kernel's outer argument context, newest first: `acc` (RDI), `dig` (RSI),
    `tbl` (RDX), `count` (RCX). -/
abbrev Gouter : Ctxt jasminDialect := [r64, AT, AD, AP]

/-- The runtime trip count (RCX). -/
def ladderCount : Ctxt.Var Gouter r64 := .here

/-- The accumulator seed: the point frame `acc` (RDI). -/
def ladderInit : Ctxt.Var Gouter AP := .there (.there (.there .here))

/-- The loop invariants: `dig` (RSI) and `tbl` (RDX). -/
def ladderInvs : HVector (fun ty => Ctxt.Var Gouter ty) [AD, AT] :=
  .cons (.there (.there .here)) (.cons (.there .here) .nil)

/-- The front-compiled rolled ladder: one copy of the per-trip point-op step
    behind a `jne` back-edge, the trip counter seeded from the runtime `count`
    register, the accumulator point frame threaded as the loop accumulator and
    `dig`/`tbl` as loop invariants. `none` if the front declines the body. -/
def ladderProgOpt : Option (ComL Gouter AP) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NP) (invCTys := Ginv)
    vmBody "out" ladderStepBody ladderCount ladderInit ladderInvs

/-- The front-compiled rolled doubling ladder, over `dblStepBody`. -/
def dblProgOpt : Option (ComL Gouter AP) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NP) (invCTys := Ginv)
    vmBody "out" dblStepBody ladderCount ladderInit ladderInvs

/-- The front-compiled rolled operand-preparation phase, over
    `ladderSelectBody`. -/
def ladderSelectProgOpt : Option (ComL Gouter AP) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NP) (invCTys := Ginv)
    vmBody "out" ladderSelectBody ladderCount ladderInit ladderInvs

-- The front accepts the operand-preparation body and wraps it in a runtime-trip
-- loop node, so the emit is one body copy behind a back-edge and not an
-- unrolled trip chain.
#guard (ladderSelectProgOpt.map (fun c => match c with
  | .forLoopNRt _ _ _ _ _ => true
  | _ => false)) = some true


/-! ## 5. The rolled ladder's denotation -/

/-- **The rolled ladder's denotation is the `JLoopBodyN.denote` fold of the
    front-compiled trip body.** Whenever the front compiles `ladderStepBody` to
    `update`, the program's denotation at any valuation is the fold of `update`
    over the runtime trip count, seeded by the `acc` argument and threading
    `dig`/`tbl`. The instance of `rolledForLoopNRt_denote` at this kernel. -/
theorem ladderProg_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NP :: .sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NP))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NP) (Γbody := CryptoTy.memref NP :: .sword 64 :: Ginv)
      vmBody "out" ladderStepBody = some update)
    (V : Ctxt.Valuation Gouter) :
    ladderProgOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(ladderCount.lookup V).toNat, update⟩
                (Expr.lookupArgs ladderInvs V) (ladderInit.lookup V)) :=
  rolledForLoopNRt_denote vmBody "out" ladderStepBody ladderCount ladderInit
    ladderInvs hupd V

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpLoopBody
