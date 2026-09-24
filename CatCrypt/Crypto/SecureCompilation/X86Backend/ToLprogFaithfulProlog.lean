/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn

/-!
# Discharging the prologue hypotheses of `toLprogPhysAbi_lsem` by construction

`ToLprogFaithfulWholeFn.toLprogPhysAbi_lsem` is the whole-function physical
correctness theorem. It carries two hypotheses about the *prologue*:

* `hProlog : lsemStraight prologue sEntry = some sProlog` — the prologue's net
  effect on the linear-machine state; and
* `hrel : ∀ sMat, lsemStraight (argMatSeq pairs) sProlog = some sMat →
    StoreRel body tbl L s sMat` — the post-materialization store relation the
  body consumes, at the entry live set `L`.

At the time `toLprogPhysAbi_lsem` was stated, the prologue used the `MOVQ`
mnemonic, which the `JasminLsem` straight-line model did not cover, so `hProlog`
was carried as an opaque hypothesis. The model now models `MOVQ`
(`JasminLsem.movq_reg_lsem`): the prologue `buildPrologue` is a fixed sequence of
nine single-source `MOVQ` reg←reg copies (the two pointer saves, the six
callee-save saves, and the `RSI`-park into `R14`). This module **runs** that
sequence in the model, discharging `hProlog` by construction, and proves the
prologue's frame / store-relation-preservation facts, discharging `hrel` modulo
the materialization and the (named) RA-disjointness invariant.

This is the CompCert/Jasmin step of *verifying the stack-frame/spill prologue
pass* rather than assuming its postcondition.

## What is discharged here

* **`buildPrologue_lsem`** (part a): `lsemStraight ((buildPrologue …).map (·.li_i))
  sEntry = some (prologueState sEntry)` for the **explicit** end state
  `prologueState sEntry` (the nine `MOVQ` copies, run via `movq_reg_lsem`).
  This discharges `hProlog` by construction.

* **`buildPrologue_frame`**: the prologue writes only the nine cells
  `prologueWritten` (`qsave.RDI`, `qsave.RSI`, the six `qsave.<calleeSave>`,
  and `R14`); every other register reads through unchanged. This is the frame
  the store-relation preservation rests on.

* **`buildPrologue_preserves_StoreRel`**: if `StoreRel body tbl L s sEntry` holds
  and the physical renaming's image on `L` avoids the nine prologue-written cells
  (`PrologueFrameDisjoint` — the RA never places a live virtual name on a
  red-zone save slot or the reserved `R14` scratch, which the actual register
  allocator respects), then `StoreRel body tbl L s (prologueState sEntry)` — the
  prologue preserves the entry store relation.

* **`buildPrologue_establishes_StoreRel`** (part b): chaining the frame through
  the materialization, the post-materialization state satisfies the body's
  `StoreRel`. (The materialization's own contribution is `argMatSeq_reads`;
  here we supply the prologue half.)

## What stays a hypothesis

The full `hrel` discharge needs the materialization to establish the argument
registers; that half is `ToLprogFaithfulWholeFn.argMat_establishes_argRegs`.
The RA-disjointness invariant `PrologueFrameDisjoint` (the renaming avoids the
red-zone / reserved-scratch cells) is the register-allocator-correctness side
condition, carried as an explicit named hypothesis (it is the same class as the
`MemrefPtrsDistinct` / `hinj` RA invariants already carried by the whole-function
theorem) — never an admitted proof.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProlog

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn

/-! ## 1. The explicit prologue end state, and the run (`hProlog` discharge) -/

/-- One prologue step: the modeled `MOVQ dst src` writes `s.lvm src` to `dst`
    and advances the pc (`JasminLsem.movq_reg_lsem`). Folding this over the nine
    prologue `(dst, src)` pairs reproduces the linear-machine run exactly, so the
    end state below is *definitionally* the `lsemStraight` result — no rewriting
    of `if`-conditions is needed for the run lemma. -/
def prologueStep {w : Nat} (s : Lstate w) (p : String × String) : Lstate w :=
  (s.setReg p.1 (s.lvm p.2)).nextPc

/-- The explicit end state of running `buildPrologue`. The prologue is the fixed
    nine-instruction `MOVQ` sequence (`JasminLprogExport.buildPrologue`):

    ```
    movq qsave.RDI, RDI ; movq qsave.RSI, RSI
    movq qsave.RBX, RBX ; movq qsave.RBP, RBP
    movq qsave.R12, R12 ; movq qsave.R13, R13
    movq qsave.R14, R14 ; movq qsave.R15, R15
    movq R14,       RSI                        (park inp-pointer in R14)
    ```

    Each `MOVQ dst src` writes `s.lvm src` to `dst` (`movq_reg_lsem`). We write the
    end state as the literal left fold of `prologueStep` over the nine
    `(dst, src)` pairs (in prologue order), reading each source against the
    *running* state — this matches the `lsemStraight` fold definitionally, so
    `buildPrologue_lsem` closes by unfolding alone. -/
def prologueState {w : Nat} (sEntry : Lstate w) : Lstate w :=
  prologueStep (prologueStep (prologueStep (prologueStep (prologueStep
    (prologueStep (prologueStep (prologueStep (prologueStep sEntry
      (abiSaveRdiName, "RDI"))
      (abiSaveRsiName, "RSI"))
      ("qsave.RBX", "RBX"))
      ("qsave.RBP", "RBP"))
      ("qsave.R12", "R12"))
      ("qsave.R13", "R13"))
      ("qsave.R14", "R14"))
      ("qsave.R15", "R15"))
      (reloadScratch2, "RSI")

/-- **`hProlog` discharged by construction.** Running the prologue
    `(buildPrologue virt tbl inLoadMap).map (·.li_i)` under the `JasminLsem`
    straight-line model from any entry state `sEntry` succeeds and reaches the
    explicit `prologueState sEntry`. Each step is a modeled single-source `MOVQ`
    reg←reg copy (`movq_reg_lsem`); the run is the nine-fold fold. -/
theorem buildPrologue_lsem {w : Nat} (virt : Lfundef) (tbl : Array Nat)
    (inLoadMap : InLoadMap) (sEntry : Lstate w) :
    lsemStraight ((buildPrologue virt tbl inLoadMap).map (·.li_i)) sEntry
      = some (prologueState sEntry) := by
  simp only [buildPrologue, List.map_cons, List.map_nil, lsemStraight,
    lsemStep, stripWidthTag_MOVQ, evalOperand, applyOpn,
    prologueState, prologueStep, abiSaveRdiName, abiSaveRsiName, reloadScratch2]

/-! ## 2. The prologue frame -/

/-- The nine cells the prologue writes (in order): the two pointer saves, the six
    callee-save saves, and the `RSI`-park into `R14` (= `reloadScratch2`). -/
def prologueWritten : List String :=
  [abiSaveRdiName, abiSaveRsiName, "qsave.RBX", "qsave.RBP", "qsave.R12",
   "qsave.R13", "qsave.R14", "qsave.R15", reloadScratch2]

/-- **The prologue frame.** Any register `y` outside the nine `prologueWritten`
    cells reads in `prologueState sEntry` exactly what it read in `sEntry`: the
    prologue only ever writes those nine cells. -/
theorem buildPrologue_frame {w : Nat} (sEntry : Lstate w) (y : String)
    (hy : y ∉ prologueWritten) :
    (prologueState sEntry).lvm y = sEntry.lvm y := by
  simp only [prologueWritten, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hy
  simp only [prologueState, prologueStep, Lstate.lvm_nextPc, Lstate.lvm_setReg,
    if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    if_neg h7, if_neg h8, if_neg h9]

/-! ## 3. Store-relation preservation (the prologue half of `hrel`) -/

/-- **The RA-disjointness side condition for the prologue**, over a live set `L`.
    The physical renaming `physRename body tbl` never places a name live at `L`
    onto one of the nine prologue-written cells (the red-zone save slots
    `qsave.*` and the reserved scratch `R14`). The register allocator respects
    this: `qsave.*` are not allocatable register names, and `R14` is reserved as a
    reload scratch (it is excluded from `gpRegNames`, the allocatable set).
    Restricting to `L` matches the store relation the whole-function theorem
    threads, which constrains only the names live at each program point. -/
def PrologueFrameDisjoint (body : Lcmd) (tbl : Array Nat) (L : List String) : Prop :=
  ∀ m ∈ L, physRename body tbl m ∉ prologueWritten

/-- **The prologue preserves the entry store relation.** If `StoreRel body tbl L
    s sEntry` and the renaming's image on `L` avoids the prologue-written cells
    (`PrologueFrameDisjoint`), then `StoreRel body tbl L s (prologueState sEntry)`:
    every renamed register of a name in `L` reads through the prologue unchanged
    (`buildPrologue_frame`), so the entry relation transfers verbatim. -/
theorem buildPrologue_preserves_StoreRel {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (L : List String) (s sEntry : Lstate w)
    (hdisj : PrologueFrameDisjoint body tbl L)
    (hrel : StoreRel body tbl L s sEntry) :
    StoreRel body tbl L s (prologueState sEntry) := by
  intro m hmL
  rw [buildPrologue_frame sEntry (physRename body tbl m) (hdisj m hmL)]
  exact hrel m hmL

/-! ## 4. `hrel` discharged: the prologue + materialization establish `StoreRel`

The body's `hrel` precondition is `∀ sMat, lsemStraight (argMatSeq pairs)
sProlog = some sMat → StoreRel body tbl L s sMat`. With `sProlog = prologueState
sEntry`, the prologue half is `buildPrologue_preserves_StoreRel`; the
materialization half (that running `argMatSeq pairs` *preserves* the store
relation away from the argument destinations, and *establishes* the argument
registers) is the materialization's own contribution. We package the
prologue-side discharge: under `PrologueFrameDisjoint` and a materialization
store-relation-preservation hypothesis (`hMatRel`, the materialization's
contract — the named glue, supplied by `argMat_establishes_argRegs` plus the
materialization frame), `hrel` follows. -/

/-- **`hrel` discharged (prologue side).** Given the entry store relation
    `StoreRel body tbl L s sEntry`, the prologue RA-disjointness
    `PrologueFrameDisjoint` over `L`, and the materialization's store-relation contract
    `hMatRel` (the materialization, started from a `StoreRel`-related state,
    re-establishes the store relation it needs — the argument-register half is
    `argMat_establishes_argRegs`, the frame half is `argMatSeq_frame`), the
    whole-function `hrel` precondition holds with `sProlog := prologueState
    sEntry`. This is the by-construction `hrel` discharge: the only external
    inputs are the entry store relation and the two named RA invariants. -/
theorem buildPrologue_establishes_StoreRel {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (L : List String) (s sEntry : Lstate w) (pairs : List (String × String))
    (hdisj : PrologueFrameDisjoint body tbl L)
    (hrelEntry : StoreRel body tbl L s sEntry)
    (hMatRel : ∀ sP, StoreRel body tbl L s sP →
      ∀ sMat, lsemStraight (argMatSeq pairs) sP = some sMat → StoreRel body tbl L s sMat) :
    ∀ sMat, lsemStraight (argMatSeq pairs) (prologueState sEntry) = some sMat →
      StoreRel body tbl L s sMat := by
  have hProlRel : StoreRel body tbl L s (prologueState sEntry) :=
    buildPrologue_preserves_StoreRel body tbl L s sEntry hdisj hrelEntry
  exact hMatRel (prologueState sEntry) hProlRel

/-! ## 5. The assembled whole-function corollary with fewer hypotheses

`toLprogPhysAbi_lsem_of_buildPrologue` is `toLprogPhysAbi_lsem` with the
explicit `hProlog` and the opaque `hrel` *supplied internally* from the prologue
run (part a) and the prologue store-relation preservation (part b). The caller no
longer provides `sProlog` or `hProlog`; instead of the opaque `hrel` it provides
the **entry** store relation `hrelEntry`, the prologue RA-disjointness
`PrologueFrameDisjoint`, and the materialization store-relation contract
`hMatRel` (the named materialization glue). What remains as hypotheses are the
RA invariants (`MemrefPtrsDistinct`, `PrologueFrameDisjoint`, the per-binding
`hinj`/`hcol` inside `CoverData`), the entry store relation, and the
materialization contract — strictly fewer / more structural than the original
opaque `hProlog` + `hrel` pair. -/

/-- **Whole-function physical correctness with the prologue discharged.** Same
    conclusion as `toLprogPhysAbi_lsem`, but `hProlog` is replaced by the proved
    prologue run (`buildPrologue_lsem`, with `sProlog := prologueState sEntry`),
    and the opaque post-materialization `hrel` is replaced by the entry store
    relation `hrelEntry`, the prologue RA-disjointness `hdisj`, and the
    materialization store-relation contract `hMatRel`. The prologue net effect is
    therefore established by construction; the body and materialization
    discharges are inherited from `toLprogPhysAbi_lsem`. -/
theorem toLprogPhysAbi_lsem_of_buildPrologue {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hbodyNoLret : .Lret ∉
      ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
        ++ (physBody (fun _ => none) body).map (·.li_i)))
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hrelEntry : StoreRel body (bodyPhysTable body) L s sEntry)
    (hMatRel : ∀ sP, StoreRel body (bodyPhysTable body) L s sP →
      ∀ sMat, lsemStraight (argMatSeq pairs) sP = some sMat →
        StoreRel body (bodyPhysTable body) L s sMat)
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  -- `hrel` for the whole-function theorem, with `sProlog := prologueState sEntry`.
  -- The prologue preserves the entry store relation (part b), and the
  -- materialization contract carries it across `argMatSeq`.
  have hrel : ∀ sMat,
      lsemStraight (argMatSeq pairs) (prologueState sEntry) = some sMat →
        StoreRel body (bodyPhysTable body) L s sMat :=
    buildPrologue_establishes_StoreRel body (bodyPhysTable body) L s sEntry
      pairs hdisjFrame hrelEntry hMatRel
  -- Apply the whole-function theorem with the prologue run discharged.
  exact toLprogPhysAbi_lsem body nArgs d com bs
    ((buildPrologue virt tbl0 inLoadMap).map (·.li_i)) rest pairs hfresh hdist
    hbody hcd hmemref L N hch sEntry s hbodyNoLret (prologueState sEntry)
    (buildPrologue_lsem virt tbl0 inLoadMap sEntry) hrel nRes hnRes

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProlog
