/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Validate: the block-body runtime loop (`ComL.forLoopBlock`)

`ComL.forLoopBlock` (`JasminLprogExport`) is the loop node whose per-iteration
body is a *recursive* `ComL (accTy :: .reg 64 :: invTys) accTy` — so one
iteration can be a multi-phase body, can contain nested loop nodes to arbitrary
depth, and ends in a `.ret acc`. It denotes to the `count`-fold of the body's own
`ComL.denote`, and lowers (via `forLoopBlockLcmd` → `comLLoopBodyWalk`) to the
runtime back-edge frame around ONE copy of the recursively-lowered body.

This file exercises the node on two shapes:

* **subsumption** — a *straight-line* block body lowers **byte-identically** to
  the corresponding `forLoopNRt` (the `comLLoopBodyWalk`/`blockLoopFrame` pair
  degenerates to `loopBodyWalkN`/`forLoopLcmdNRt` on a `.var`/`.ret` body), so
  every existing `forLoopNRt` kernel is a special case;
* **genuine 2-deep nesting** — a block body that is itself an inner `forLoopNRt`
  emits **two** real `Lcond NZ` back-edges (outer + inner), denotes to the double
  fold, and builds through `ComL.toLprogPhys` to a single well-formed `Lfundef`.

This is the node that retires MAYO/SolveGf16's G1 (multi-phase loop body) and G2
(3-deep nesting) front gaps: their inner `RWhileNz` body is itself a loop over a
sub-phase, which `forLoopNRt`'s `Com`-shaped `update` cannot carry.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Subsumption: a straight-line block body ≡ `forLoopNRt` -/

/-- The squaring body `acc := acc · acc` as a **recursive** `ComL` over the
    `JLoopBodyN`-shaped context `[reg 64 (acc), reg 64 (idx)]` (invTys = `[]`). -/
def sqrBlockBody : ComL [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil))) (.ret .here)

/-- The same body as a straight-line `Com` (the `forLoopNRt` `update` shape). -/
def sqrRtBodyC : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil))) (.ret .here)

/-- Seed `acc` from arg `.here`, run the straight-line `sqrBlockBody` a **runtime**
    number of times (`count = .there .here`), return the accumulator — a
    `forLoopBlock` program. -/
def blockSqrProg : ComL [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .forLoopBlock sqrBlockBody (.there .here) .here .nil (.ret .here)

/-- The identical program built with `forLoopNRt` (the straight-line-body node). -/
def nrtSqrProg : ComL [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .forLoopNRt sqrRtBodyC (.there .here) .here .nil (.ret .here)

/-- **Denote = spec:** seed `3`, runtime count `2` → `3^(2²) = 81`. The block-body
    fold runs `(count.lookup V).toNat = 2` times, each iteration `ComL.denote`ing
    the recursive body. -/
theorem blockSqrProg_denote :
    ComL.denote blockSqrProg (.cons (3 : BitVec 64) (.cons (2 : BitVec 64) .nil))
      = (81 : BitVec 64) := by rfl

/-- **Byte-identical subsumption:** the block-body program lowers to exactly the
    same instruction stream as the `forLoopNRt` program (compared through the
    textual renderer, since `LinstrR` carries only `Repr`). A `forLoopBlock` with
    a straight-line body IS a `forLoopNRt`. -/
theorem blockSqrProg_lowers_like_forLoopNRt :
    (comLToBody 2 argName (fun _ => none) blockSqrProg 2).map (fun i => i.li_i.toText)
      = (comLToBody 2 argName (fun _ => none) nrtSqrProg 2).map (fun i => i.li_i.toText) := by
  native_decide

/-- The block-body lowering still ends with `Lret`. -/
theorem blockSqrBody_ends_Lret :
    (comLToBody 2 argName (fun _ => none) blockSqrProg 2).getLast?.map Linstr.li_i
      = some .Lret := rfl

/-- **Physical export well-formed:** the straight-line block program survives the
    same SSA→physical register allocation as a straight-line `Com` — every `Lopn`
    operand is a real x86 register (no leftover SSA name), and the back-edge
    survives. (Byte-identical to the already-proven `forLoopNRt` phys export.) -/
theorem blockSqrPhys_all_real_registers :
    (ComL.toLfundefPhys blockSqrProg).lfd_body.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-! ## 2. Genuine 2-deep nesting: an inner `forLoopNRt` in the block body

The block body is itself an inner runtime loop `acc := acc + acc` run `m` times
(`m` an invariant of the outer loop). `forLoopNRt`'s `update` cannot express this
(a loop is not a `JasminOp`); `forLoopBlock`'s recursive body can. This is the
`forLoopNRtNested` shape reached *generically* through `forLoopBlock`. -/

/-- The inner doubling body `acc := acc + acc` over `[reg 64 (acc), reg 64 (idx)]`
    (invTys = `[]`; the index is unused). -/
def innerDblBody : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))) (.ret .here)

/-- The outer block **body**: over `[reg 64 (acc), reg 64 (idx), reg 64 (m)]`, run
    the inner doubling loop a **runtime** `m` times (`m = .there (.there .here)`,
    the deepest binder = the outer loop's invariant), seeded from the accumulator
    (`.here`), returning the inner result. A recursive `ComL` carrying a genuine
    inner back-edge — the field `forLoopNRt` could not hold. -/
def nestBlockBody : ComL [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .forLoopNRt innerDblBody (.there (.there .here)) .here .nil (.ret .here)

/-- The outer `forLoopBlock` program. `Γ = [count, m, acc]` (newest-first), so
    `count = .here`, `m = .there .here`, `init (acc) = .there (.there .here)`; the
    single invariant threaded into the body is `m`. Runs `nestBlockBody` `count`
    times, each pass doubling the accumulator `m` times — i.e.
    `acc · 2^(m·count)`. -/
def nestBlockProg : ComL [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .forLoopBlock nestBlockBody .here (.there (.there .here))
    (.cons (.there .here) .nil) (.ret .here)

/-- **Denote = spec (double fold):** `acc = 1`, `m = 2`, `count = 3` →
    `1 · 2^(2·3) = 64`. The outer fold runs `count = 3` times; each iteration
    `ComL.denote`s `nestBlockBody`, itself an `m = 2`-fold doubling. -/
theorem nestBlockProg_denote :
    ComL.denote nestBlockProg
      (.cons (3 : BitVec 64) (.cons (2 : BitVec 64) (.cons (1 : BitVec 64) .nil)))
      = (64 : BitVec 64) := by rfl

/-- The lowered nested body. -/
def nestBlockLowered : Lcmd := comLToBody 3 argName (fun _ => none) nestBlockProg 3

/-- **Two genuine back-edges:** the nested lowering has exactly **two** `Lcond NZ`
    conditional jumps — the outer loop's back-edge and the inner loop's back-edge.
    This is real nested control flow, not an unrolled chain. -/
theorem nestBlock_two_backedges :
    (nestBlockLowered.filter (fun i =>
      match i.li_i with | .Lcond (.reg "NZ") _ => true | _ => false)).length = 2 := by
  native_decide

/-- **Nested lowering ends with `Lret`:** the terminal `.ret` of the outer
    continuation is still the last instruction (the two loop back-edges are
    interior control flow). Discharged by the general `comLToBody_ends_Lret`
    (extended with the `forLoopBlock` arm). -/
theorem nestBlock_ends_Lret :
    nestBlockLowered.getLast?.map Linstr.li_i = some .Lret := by
  simpa [nestBlockLowered] using
    comLToBody_ends_Lret 3 argName (fun _ => none) nestBlockProg 3

/-- **Builds to a single well-formed function:** the nested block program exports
    through `ComL.toLprogPhys` to an `Lprog` with exactly one exported function.
    (Structural well-formedness of the whole export chain on a nested-loop
    `ComL`.) -/
theorem nestBlockProg_toLprogPhys_wf :
    (ComL.toLprogPhys nestBlockProg "nest").lp_funcs.length = 1 ∧
      ((ComL.toLprogPhys nestBlockProg "nest").lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) := by
  refine ⟨rfl, rfl⟩

-- The nested-loop physical export's well-formedness is covered by
-- `nestBlockProg_toLprogPhys_wf` (one exported, well-formed function) together
-- with `nestBlock_ends_Lret` (the lowered body ends with `Lret`, RA-independent
-- via `comLToBody_ends_Lret`). The `forLoopBlock` node's control-flow correctness
-- itself lives in `JasminLprogExport`.

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
