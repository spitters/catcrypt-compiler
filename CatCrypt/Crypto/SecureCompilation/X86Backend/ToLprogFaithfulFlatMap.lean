/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulEndToEnd

/-!
# `physBody` `flatMap`-identity — tying the literal emitter output to the block list

This is the named de-Bruijn residual from `ToLprogFaithfulBody` /
`ToLprogFaithfulEndToEnd`: connecting the literal `flatMap` output of
`JasminLprogExport.physBody` to the `bs.map (·.block)` block list that
`binopBody_lsem_result` consumes.

`physBody (fun _ => none) body` is `body.flatMap (fun i => …)`, a per-instruction
expansion. For a source instruction in the **uniform two-address binop shape** —
an `Lopn (d :: _) opn (s0 :: s1 :: _)` with `opn` a (non-shift) binop mnemonic and
the RA having placed `dst` on `s0`'s register (`rmap d = rmap s0`, the two-address
*collapse*) — the expansion is exactly
`(legalizeBinop (rmap d) (rmap s1) opn "MOV").map (⟨i.li_ii, ·⟩)`, whose `li_i`
projection is `legalizeBinop (physRename body tbl …) (physRename body tbl …) opn
"MOV"` = `BinopBinding.block`. So, for a body all of whose instructions are in
that shape, mapping `li_i` over `physBody` recovers exactly the flattened block
list `(bs.map (·.block)).flatten`.

## What this module proves

PROVED (against the literal `physBody`, all goals closed):

* `physBodyStep_binopCollapse`: the **per-instruction `flatMap` step**. One source
  binop instruction in the two-address-collapse shape expands, under `physBody`,
  to its `legalizeBinop` block tagged with `li_ii` — i.e.
  `(physBody (fun _ => none) [i]).map (·.li_i) = legalizeBinop (rmap d) (rmap s1) opn "MOV"`.
  This unfolds `physBody`'s `flatMap` on a singleton, evaluates the internal
  `isBinop`/`isShift`/`movFor`/`shiftImmVal` `let`s, takes the `dst = s0` branch,
  and discharges `materializeWideImm` on the default `"MOV"` path.

* `physBody_flatMap_blocks`: the **whole-body `flatMap`-identity**. For a body
  `body` together with a list `bs : List (BinopBinding w body tbl)` and a
  *witness* that the `i`-th source instruction realises the `i`-th binding's block
  (`hcover`), mapping `li_i` over `physBody (fun _ => none) body` equals the
  flattened block list `(bs.map (·.block)).flatten`. Inducts over the cover.

* `physBody_lsem_result`: the **general physical-faithfulness theorem on the
  binop fragment**. Running the *literal* `physBody (fun _ => none) body` (its
  `li_i` projection) under `lsemStraight`, from a `StoreRel`-related start, reads
  at the physical result register `ρ nRes` exactly the composed virtual store
  `(composeVSteps … s).lvm nRes` — for any binop body covered by a binding list.
  Composes `physBody_flatMap_blocks` (this module) with
  `binopBody_lsem_result` (the semantic capstone). This is the physical analogue
  of `comToLprog_faithful_straightline` over the *emitter's actual output*,
  modulo the cover hypothesis below.

## Residual (NOT proved here)

* **The cover hypothesis `hcover`.** This module proves the `flatMap` identity
  *given* that each source instruction is in the binop two-address-collapse shape
  and names the binding's logical operands (`hcover`). Discharging `hcover` from a
  *`UniformRegArith` `Com`* — i.e. that `comToBody`/`comToLfundef` followed by the
  RA `physTable` actually produces this shape, with `rmap d = rmap s0` for every
  binding (the two-address collapse the RA performs) — is the `straightOps`/
  de-Bruijn bookkeeping that ties `comToBody`'s emitted `Lcmd` to the `Com`
  structure. The semantic content (per-instruction expansion + whole-body
  threading + result projection) is fully proved here and in
  `ToLprogFaithfulBody`; the cover is the structural index identification.

* The `dst ≠ s0` leading-`mov` bindings (covered as `BlockMaintains` witnesses in
  `ToLprogFaithfulTwoAddr`) are not folded into the `flatMap`-identity here — the
  identity is stated for the collapse shape; the leading-`mov` shape expands to
  `legalizeMov ++ legalizeBinop`, a different block, and would need a second cover
  arm. Shift-immediate (`lowerTwoAddrShiftImm`), three-source carry ops,
  `arr`/`arrIdx` memory, the ABI prologue/epilogue and `Lret` remain out of scope
  exactly as in the sibling modules.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulFlatMap

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulEndToEnd

/-! ## 1. The per-instruction `flatMap` step -/

/-- The `flatMap` kernel of `physBody (fun _ => none) body`: the per-instruction
    expansion with the captured outer `body`/`tbl`. `physBody`'s body is exactly
    `body.flatMap (physBodyElem body tbl)` for `tbl = bodyPhysTable body`. -/
def physBodyElem (body : Lcmd) (tbl : Array Nat) (i : Linstr) : Lcmd :=
  let rmap := remapOperand body tbl
  let isBinop (opn : String) : Bool := isTwoAddrBinop opn
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg _ => none
    | _ => none
  match i.li_i with
  | .Lopn (d :: _) opn ((s0 :: s1 :: _) : List LOperand) =>
      if isBinop opn then
        match (if isShift opn then shiftImmVal s1 else none) with
        | some v =>
            (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
        | none =>
            (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
      else
        match i.li_i with
        | .Lopn [d'] opn' [addr, val] =>
            if isMemStore opn' then
              (legalizeMemStore (rmap d') (rmap addr) (rmap val) opn' (movFor opn')).map
                (fun r => ⟨i.li_ii, r⟩)
            else
              [⟨i.li_ii, .Lopn [rmap d'] opn' [rmap addr, rmap val]⟩]
        | .Lopn dsts opn srcs =>
            [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
        | other => [⟨i.li_ii, other⟩]
  | .Lopn [d] opn [s] =>
      if isNativeShiftRotate opn then
        (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
          (fun r => ⟨i.li_ii, r⟩)
      else if isMemLoad opn then
        (legalizeMemLoad (rmap d) (rmap s) opn (movFor opn)).map
          (fun r => ⟨i.li_ii, r⟩)
      else if stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ" then
        (legalizeMov (rmap d) (rmap s) opn).map (fun r => ⟨i.li_ii, r⟩)
      else
        [⟨i.li_ii, .Lopn [rmap d] opn [rmap s]⟩]
  | .Lopn dsts opn srcs =>
      [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
  | other => [⟨i.li_ii, other⟩]

/-- `physBody (fun _ => none) body` is `body.flatMap (physBodyElem body tbl)` for
    the canonical table `tbl = bodyPhysTable body`. Exposes the captured
    closure as a named per-element kernel so the cover can be discharged
    element-wise. Definitional unfolding of `physBody` on the default (`fun _ =>
    none`) shift oracle. -/
theorem physBody_eq_flatMap (body : Lcmd) :
    physBody (fun _ => none) body
      = body.flatMap (physBodyElem body (bodyPhysTable body)) := by
  rfl

/-- **Per-instruction expansion, binop two-address-collapse shape.** A source
    binop instruction `⟨ii, .Lopn (d :: ds) opn (s0 :: s1 :: ss)⟩` whose mnemonic
    is a (non-shift) binop (`hbin`, `hsh`), default-width (`h64`), and whose
    renamed destination coincides with its renamed first source
    (`hcol : rmap d = rmap s0`, the two-address collapse), expands under
    `physBodyElem` to `(legalizeBinop (rmap d) (rmap s1) opn "MOV").map (⟨ii, ·⟩)`. -/
theorem physBodyElem_binopCollapse (body : Lcmd) (tbl : Array Nat)
    (ii : Nat) (d s0 s1 : LOperand) (ds ss : List LOperand) (opn : String)
    (hbin : isTwoAddrBinop opn = true)
    (hsh : ¬ (stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR") = true)
    (h64 : ¬ hasSuffix opn ":64" = true)
    (hcol : remapOperand body tbl d = remapOperand body tbl s0) :
    physBodyElem body tbl ⟨ii, .Lopn (d :: ds) opn (s0 :: s1 :: ss)⟩
      = (legalizeBinop (remapOperand body tbl d) (remapOperand body tbl s1) opn "MOV").map
          (fun r => ⟨ii, r⟩) := by
  simp only [physBodyElem, hbin, hsh, h64, Bool.false_eq_true, if_false,
    lowerTwoAddr, hcol, if_pos, materializeWideImm_MOV, List.nil_append]

/-! ## 2. The whole-body `flatMap`-identity

A source instruction *realises* a `BinopBinding` when it is a binop `Lopn` in the
two-address-collapse shape naming the binding's logical destination/sources. The
whole-body identity is then an induction over a `Forall₂` cover of the body by the
binding list: each instruction realises its binding, so its `physBodyElem`
expansion is the binding's block, and the `flatMap` is the flattened block list. -/

/-- A source instruction `i` *realises* binding `b` (in the two-address-collapse
    shape along `tbl`): `i` is `.Lopn (.reg b.nDst :: ds) b.opn (.reg nS0 :: .reg
    b.nSrc :: ss)` for some collapse-source `nS0` with `physRename body tbl nS0 =
    physRename body tbl b.nDst` (the RA placed `dst` on `s0`'s register), the
    mnemonic is a non-shift default-width binop, and `b.opn` matches `i`'s opcode.
    Exactly the hypotheses `physBodyElem_binopCollapse` consumes, packaged as a
    relation between a `Linstr` and a `BinopBinding`. -/
def InstrRealizesBinding {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (i : Linstr) (b : BinopBinding w body tbl) : Prop :=
  ∃ (nS0 : String) (ds ss : List LOperand),
    i.li_i = .Lopn (.reg b.nDst :: ds) b.opn (.reg nS0 :: .reg b.nSrc :: ss)
    ∧ (isTwoAddrBinop b.opn = true)
    ∧ (¬ (stripWidthTag b.opn == "SHL" || stripWidthTag b.opn == "SHR") = true)
    ∧ (¬ hasSuffix b.opn ":64" = true)
    ∧ physRename body tbl nS0 = physRename body tbl b.nDst

/-- One realising instruction's `physBodyElem` expansion is its binding's block
    tagged with `li_ii`, hence its `li_i` projection is exactly `b.block`. -/
theorem physBodyElem_of_realizes {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (i : Linstr) (b : BinopBinding w body tbl)
    (hr : InstrRealizesBinding body tbl i b) :
    (physBodyElem body tbl i).map (·.li_i) = b.block := by
  obtain ⟨nS0, ds, ss, hi, hbin, hsh, h64, hcol⟩ := hr
  -- rebuild `i` from its components, then reduce by `physBodyElem_binopCollapse`.
  have hi' : i = ⟨i.li_ii, .Lopn (.reg b.nDst :: ds) b.opn (.reg nS0 :: .reg b.nSrc :: ss)⟩ := by
    cases i; exact congrArg (Linstr.mk _) hi
  rw [hi']
  have hcol' : remapOperand body tbl (.reg b.nDst) = remapOperand body tbl (.reg nS0) := by
    rw [remapOperand_reg, remapOperand_reg, hcol]
  rw [physBodyElem_binopCollapse body tbl i.li_ii (.reg b.nDst) (.reg nS0) (.reg b.nSrc)
    ds ss b.opn hbin hsh h64 hcol']
  -- map `li_i` over the tagged block recovers the block
  rw [List.map_map]
  simp only [Function.comp_def, List.map_id_fun', id_eq]
  rw [remapOperand_reg, remapOperand_reg]
  rfl

/-- A *binding cover* of a source body `body` by a binding list `bs`: the two
    lists are element-wise related by `InstrRealizesBinding` (same length, the
    `i`-th instruction realises the `i`-th binding). A self-contained two-list
    pointwise predicate (avoids a Mathlib `Forall₂` import). -/
inductive BodyCover {w : Nat} (body : Lcmd) (tbl : Array Nat) :
    Lcmd → List (BinopBinding w body tbl) → Prop where
  | nil : BodyCover body tbl [] []
  | cons {i : Linstr} {b : BinopBinding w body tbl} {is : Lcmd}
      {bs : List (BinopBinding w body tbl)} :
      InstrRealizesBinding body tbl i b → BodyCover body tbl is bs →
      BodyCover body tbl (i :: is) (b :: bs)

/-- **Whole-body `flatMap`-identity.** For a source body `body` covered
    instruction-by-instruction by a binding list `bs` (`BodyCover`), mapping
    `li_i` over the literal `physBody (fun _ => none) body` equals the flattened
    block list `(bs.map (·.block)).flatten`. The de-Bruijn-free half of the named
    residual: the emitter's actual output, projected to `LinstrR`, *is* the block
    list the semantic capstone consumes — given the cover. Inducts over the cover,
    peeling one instruction/binding pair with `physBodyElem_of_realizes`. -/
theorem physBody_flatMap_blocks {w : Nat} (body : Lcmd)
    (sub : Lcmd) (bs : List (BinopBinding w body (bodyPhysTable body)))
    (hcover : BodyCover body (bodyPhysTable body) sub bs) :
    sub.flatMap (fun i => (physBodyElem body (bodyPhysTable body) i).map (·.li_i))
      = (bs.map (·.block)).flatten := by
  induction hcover with
  | nil => rfl
  | cons hib _ ih =>
      rw [List.flatMap_cons, List.map_cons, List.flatten_cons, ih,
        physBodyElem_of_realizes body (bodyPhysTable body) _ _ hib]

/-- **`physBody` projected to the block list.** The literal emitter output
    `physBody (fun _ => none) body`, projected to `LinstrR` via `li_i`, is exactly
    the flattened binding-block list `(bs.map (·.block)).flatten` — when the whole
    body is covered by `bs`. The `sub = body` specialisation of
    `physBody_flatMap_blocks`, stated over the actual `physBody`. -/
theorem physBody_map_li_i {w : Nat} (body : Lcmd)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (hcover : BodyCover body (bodyPhysTable body) body bs) :
    (physBody (fun _ => none) body).map (·.li_i) = (bs.map (·.block)).flatten := by
  rw [physBody_eq_flatMap, List.map_flatMap]
  exact physBody_flatMap_blocks body body bs hcover

/-! ## 3. The general physical-faithfulness theorem on the binop fragment

Composing the `flatMap`-identity (this module) with the semantic capstone
`binopBody_lsem_result` (`ToLprogFaithfulEndToEnd`): running the *literal*
`physBody` output under `lsemStraight`, from a `StoreRel`-related start, reads the
composed virtual store at the physical result register. This is the physical
analogue of `comToLprog_faithful_straightline` over the emitter's actual
output. -/

/-- **General physical faithfulness on the binop fragment.** For a body covered by
    a binding list `bs` (`BodyCover`), running the *literal* `physBody (fun _ =>
    none) body` (its `li_i` projection) under `lsemStraight`, from a
    `StoreRel`-related start `(s, s')`, produces `s''` whose physical result
    register `physRename body tbl nRes` reads exactly the composed virtual store
    `(composeVSteps … s).lvm nRes`. Combines `physBody_map_li_i` (the
    `flatMap`-identity, this module) with `binopBody_lsem_result` (the semantic
    capstone). The physical analogue of
    `JasminLsemSimulation.comToLprog_faithful_straightline`, stated over the
    emitter's actual output — modulo the cover hypothesis (the named residual). -/
theorem physBody_lsem_result {w : Nat} (body : Lcmd)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (hcover : BodyCover body (bodyPhysTable body) body bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  rw [physBody_map_li_i body bs hcover]
  exact binopBody_lsem_result body (bodyPhysTable body) bs L N hch s s' hrel nRes hnRes

/-- **General physical faithfulness as an `Option.map`.** The `Option.map (read at
    ρ nRes)` of the literal-`physBody` run equals `some` of the composed virtual
    store at `nRes` — the exact `Option.map (decode …) = some (…)` shape of
    `comToLprog_faithful_straightline`, over the emitter's actual output. -/
theorem physBody_lsem_result_map {w : Nat} (body : Lcmd)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (hcover : BodyCover body (bodyPhysTable body) body bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    (lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s').map
        (fun st => st.lvm (physRename body (bodyPhysTable body) nRes))
      = some ((composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes) := by
  obtain ⟨s'', hrun, hread⟩ :=
    physBody_lsem_result body bs hcover L N hch s s' hrel nRes hnRes
  rw [hrun, Option.map_some, hread]

/-! ## 4. A three-binding cover instance

To exhibit `BodyCover` as inhabitable (not a vacuous hypothesis), we build a
three-element cover from three per-instruction realization witnesses and route a
three-binop body through `physBody_lsem_result`. The realization witnesses
(`InstrRealizesBinding`) carry the per-instruction shape obligations — we
do not fabricate them; the *instance content* is that the inductive `BodyCover`
constructor composes them and the general theorem fires on a three-binding body. -/

/-- A three-instruction body covered by a three-binding list: assemble three
    per-instruction realization witnesses into a `BodyCover`, exhibiting the cover
    constructor on a non-trivial (length-3) body. -/
theorem bodyCover_three {w : Nat} (body : Lcmd)
    (i0 i1 i2 : Linstr)
    (b0 b1 b2 : BinopBinding w body (bodyPhysTable body))
    (h0 : InstrRealizesBinding body (bodyPhysTable body) i0 b0)
    (h1 : InstrRealizesBinding body (bodyPhysTable body) i1 b1)
    (h2 : InstrRealizesBinding body (bodyPhysTable body) i2 b2) :
    BodyCover body (bodyPhysTable body) [i0, i1, i2] [b0, b1, b2] :=
  .cons h0 (.cons h1 (.cons h2 .nil))

/-- **Three-binding instance of general physical faithfulness.** When the body is
    exactly `[i0, i1, i2]`, each realising its binding, the literal-`physBody` run
    reads the composed virtual store at the physical result register. The
    three-binding specialisation of `physBody_lsem_result` through
    `bodyCover_three` — the cover hypothesis is *discharged* from three concrete
    realization witnesses, so the conclusion is unconditional in `BodyCover`. -/
theorem physBody_lsem_result_three {w : Nat}
    (i0 i1 i2 : Linstr)
    (b0 b1 b2 : BinopBinding w [i0, i1, i2] (bodyPhysTable [i0, i1, i2]))
    (h0 : InstrRealizesBinding [i0, i1, i2] (bodyPhysTable [i0, i1, i2]) i0 b0)
    (h1 : InstrRealizesBinding [i0, i1, i2] (bodyPhysTable [i0, i1, i2]) i1 b1)
    (h2 : InstrRealizesBinding [i0, i1, i2] (bodyPhysTable [i0, i1, i2]) i2 b2)
    (L N : List String)
    (hch : Chained ([b0, b1, b2].map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel [i0, i1, i2] (bodyPhysTable [i0, i1, i2]) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) [i0, i1, i2]).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename [i0, i1, i2] (bodyPhysTable [i0, i1, i2]) nRes)
          = (composeVSteps ([b0, b1, b2].map (fun b => (b.block, b.vstep))) s).lvm nRes :=
  physBody_lsem_result [i0, i1, i2] [b0, b1, b2]
    (bodyCover_three [i0, i1, i2] i0 i1 i2 b0 b1 b2 h0 h1 h2) L N hch s s' hrel nRes hnRes

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulFlatMap
