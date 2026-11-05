/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalfBase
public import CatCrypt.Crypto.SecureCompilation.Haxc.AndnLegal
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsAbi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOutChain
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeStackRoom
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAllocLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopWLeak
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegionsCallOut
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHiFast
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebsLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrStore
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak
public import CatCrypt.Crypto.SecureCompilation.SepLogic.Abi
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgNarrowPrep

@[expose] public section

set_option autoImplicit false

/-!
# The back half on a region-exported program

`compileRegion σ a p` takes a structured program `p : NFProg jasminDialect Γ [t]` to the
printed `Lprog` and the `.text` bytes of its function, or `none` when a stage declines or a
check refuses. It tests `regionExportableB` on `p`, runs the narrow-word stages
`VIR.NarrowWords.narrowPrep` (each word of width `8`, `16` or `32` held zero extended in a
64-bit register or array slot, redundant masks and dead bindings removed), and then the
stages `regionBack` on the widened program. The stages of `regionBack` are, in order:

0. the region legalisation `legalizeRegion`, which rewrites each and-not into its and-xor
   block (`legalizeAndn`), and keeps the denotation and the leakage run; a rotate by an
   immediate is kept and compiled to the machine rotate;
1. the test `regionExportableB` of the legalised program, and the test `NFProg.callFree` that
   it has no `call`;
2. the region export `exportR` from the depth `Γ.length` and the label `0`, and its virtual
   function `exportRLfundef` (the code followed by a return);
3. the physical-ABI allocation `lfundefPhysAbiOfVirt` of the virtual function, with each array
   base paired with the register of its own argument slot and the array bases live together
   at entry (`arrBasePins`), followed by the fusion post-pass `regionPostFuse`
   (`regionLprog`);
4. the printed program `printedLprog` (the owned back end `LprogOptPipeline.ownedLprog` and
   the reload `CmpSpillReload.cmpReload` of spilled compare operands) and the gated encoder
   `LprogBytes.encodeLfundefBytesChecked` on its first function body;
5. the check `regionCoB` of the reference of the export against the printed body, and the
   constant-time check `regionCtB` of the printed body: the check of the events
   `regionLeakB`, the printed class `printedAddrWB` and the image gate with carry chains
   and indexed stores through a cell `imgGateCW` of the cell body at the frame marks with
   the cells, the hypotheses of
   `regionWide_bytes_ct`.

## A calling body

`compileRegion` takes a list of linked functions (`CalleeData`), empty by default. A program
with a `call` whose shadow instructions name symbols of the list, with a word-array result,
is compiled at the table of the linked functions of these symbols (`regionCallee`), and each
stage is a function of the optional table that is the stage above without one:

* the allocation `calleeAlloc`: the pool of the names the callee keeps, the shadow
  instruction left in the input of the allocation and expanded on the allocated body;
* the reference of the gate from the exported code on the common names of the callee
  (`calleeCode`), checked against the image `calleeImg` of a calling body at the call sites
  `calleeSiteAt` (at each call, as operands, the argument names at the scalar parameters and
  the arrays whose frame slots the argument registers reload before the call at the array
  parameters; as destination, the result register for a word result and the operand at the
  destination position for an out result), with the one image check `calleeImgBT` of both
  routes: `regionImgCB` at the frame and the symbols of the table, which adds to the
  conjuncts of `regionImgB` that every call names a symbol of the table (`callsTabB`) and
  admits calls of these symbols in the class and the gate;
* two conjuncts of `regionCoB` of the form `callee.all _`: the rewriting onto the common
  names with its freshness check, and the checks `calleeBodyB` of the printed body (the
  check `calleeCodeB` of the code of the callee, the cut programs, the call sites, the table `deadTab` of dead names and live flags with the
  operands of the call (`calleeDeadB`), and the
  bounds check with calls of the reference, and the checks of the segments at the export
  name); the cut checks run at the empty function name and give the soundness of the
  validation by segments at every function name (`calleeCutB_soundK`), and the checks of
  the segments give the simulation it takes (`calleeBody_imgRun`);
* the bytes `calleeBytes`: the relocating encoder at the symbol map `calleeSym`, under the
  checks `calleeLinkB`, followed by the code of the table; the entry of each function after
  the first is an instruction of the decoded code of the table (`CalleeTab.regionB`), and
  the code of the table is a region of the blocks of the functions
  (`CalleeTab.regionBlocks`, `calleeBytes_decode`);
* the constant-time check `calleeCtB`: the decision with calls of linked callees
  `AbiLayout.ctCheckRXT` on the program `calleeProg` of the function, at the clobber set
  `CalleeTab.clobB`, the public argument registers `CalleeTab.ctIfc` and the destinations
  `CalleeTab.ctDst` at the call targets, and the frame of the table; at one function this is
  the decision `AbiLayout.ctCheckRXO` at the data of that function (`calleeCtB_one`). At
  distinct entry indices (`CalleeTab.entryIdx_inj`) the interface at the entry of the
  function of a symbol is that of the function (`CalleeTab.ctIfc_entry`,
  `CalleeTab.ctDst_entry`, `CalleeTab.clob_of_clobB`).

The callee of these stages is an optional table `CalleeTab` (`regionCallee_tab`). Without a
table each
reduces by `rfl` (`calleeImgT_none`, `calleeCodeT_none`, `calleeAlloc_none`, `calleeBytes_none`, `calleeCtB_none`,
`regionCoB_none`), except the image check, which is `regionImgB` by `calleeImgBT_none`
(`regionImgCB_nil`), and a program without `call` has no callee at every list
(`compileRegion_of_callFree`). The result of a calling body is gated; no correctness
theorem of this module covers it.

## The multiplication fusion

A high multiplication `MULXHI` of the export has no bytes of its own; the post-pass
`FuseMulHi.fuseMulHiLprog` of the allocation replaces it by the two-output `MULX`
with `RDX` saved in `R15`, and leaves a program without such a multiplication unchanged.
The reference of the gate carries the same fusion `JasminLsemFuseMulHi.fuseMulHiRM` on its
code behind the copies, as its last step, when that code has a site of the fusion
(`fuseSites`); code without a site is the reference as it is.
`JasminLsemFuseMulHi.fuseMulHi_lsemFuelMemF_pre` transfers a run of the unfused code to the
fused one under the decided check `fuseOKL`; the final states agree on every register and
array other than `R15`, and the gate checks that the result names are other than `R15`
(`regionSitesB`). The register merge and the array self-moves are checked on the unfused
code, which has no `MULX`.

## The image check of a virtual body

`renImageB σ nm ps R outs body B` is the part of `ImageAddrRoute.routeB` that does not read
the shape of the virtual body: the register allocation check `ownedCheckMC` of `B` against
the image of the cell body of the printed body, the bounds invariant of `B` from the
register bounds, the cell body in the image class, the printed class with the gate of its
image simulation (`regionImgB`), the frame check and the entry check, with the array names
of the slot map renamed by the pairs `ps`, and the checks of the cell arrays `R`. A body of
`printedAddrWB` is gated, at its cell body, by the gate with carry chains and indexed stores
through a cell `imgGateCW`, under which a general-purpose name may hold a one-bit carry. `renImage_bytes` states that every
halting run of `B` under `lsemFuelMemF` from the entry state `emptiedEntry` is matched by a
halting run of the decoded bytes of the printed body, at the end of which every array
parameter that is no cell array is in memory at its entry base and every observed cell
name holds the word of its cell. The virtual body is any list of typed instructions.

## Cell accesses

The owned back end prints an access of an array at a literal index as an access of a cell
at a constant displacement from the array pointer. The arrays the printed body accesses
this way are its cell arrays (`cellArrsOf`). The reference of the gate reads and writes
such an array through cell names: the last step of the reference is the cell fold
`CellFoldLReg.cellFoldLR` at the cell arrays, and the image check reads the printed body
through its cell body `ImageAddrCells.cellBody`, in which a cell access is a move of the
cell name. `CellFoldLReg.lsemFuelMemF_cellFoldLR` transfers a halting run of the code to
the folded code from the entry state with the cell arrays emptied and their words in the
cell names. An array accessed at literal indices only is covered; a body that indexes one
array by a loop counter and at literal indices is refused by the fold. A printed body with
no cell access has no cell array, and every part is the part without cells:
`cellArrsOf_of_cellFreeB`, `regionImgB_of_cellFreeB`, `renImageB_of_cellFreeB`,
`regionCoParts_of_cellFreeB`, `regionCoB_of_cellFreeB`.

## The virtual body of a region export

The virtual body of a region export is the copies `argBind σ nm` of the parameter registers
into the argument names, followed by the code of the export. `regionVirt_run` runs it from
`entryV`: the copies leave the entry state unchanged, and the simulation statement
`ExportRegions.exportR_sim` of the export, placed after the copies, runs the code to a state
that agrees with the returned operands at the denotation.

## The coalesced and renamed reference

The export writes every array store to a fresh name and names its registers by depth; the
allocated body stores in place and holds a value in one location across a block boundary.
The register allocation check compares the two bodies under the same names at block exits,
so the reference of the gate starts from the exported code with its array versions merged by
the alias map of `regionAliasTab` (the coalescing renaming `chainAlias`, which also sends the
result root of the returned array to the result buffer) at the array positions of its
instructions (`renArr`: a name of
the export names a register cell and an array cell, and the alias moves the array cell
only) and its registers renamed by pairs `ps`, behind the copies `movesOf ps`:
`argBind σ nm ++ movesOf ps ++ (C.map (renArr ρ)).map (renRM (renOf ps))`.
The liveness certificate `liveArrCert` is synthesised and the pairs `certArgs` are the
allocation certificate of `regionLprogC` at the argument names; neither carries trust:
`ImageCoalesceCfg.coCfgB` checks the liveness certificate and `ImageAddrRoute.renB` the
pairs. `regionRef_run` transfers a run of `argBind σ nm ++ C` to
the reference by `ImageCoalesceCfg.lsemFuelMemF_coalesce` and
`ImageAddrSrcFuel.renameLoop_sim_fuel`.

## The register merge

The pairs `ps` rename injectively, so each machine register is the partner of one name of
the export. A linear-scan allocation gives one machine register to two names of the export
whose live ranges are disjoint, such as the index registers of two loops in sequence. The
reference of the gate is therefore the renamed code with its remaining names merged into
machine registers by a second renaming `renOf ts` that need not be injective:
`argBind σ nm ++ movesOf ps ++ ((C.map (renArr ρ)).map (renRM (renOf ps))).map (renRM (renOf ts))`.
The merge pairs `certMerge` are the allocation certificate at the other names that some
block, or some piece of a block between two calls, reads before it writes them
(`crossNames`), and the
register liveness table `liveRegTab` is synthesised; neither carries trust. `regCoB`
checks them: the names an instruction reads are
live before it, a name live after a write is the written name or has an image other than
the image of the written name, the names live after the label of a jump are live at the
jump, and the merge fixes the names live at the entry and the array names.
`liveCert_of_regCoB` turns an accepted merge into the certificate
`JasminLsemExportRegAlloc.LiveCert`, and `regCo_run` transfers a run of the renamed
reference to the merged one by `JasminLsemExportRegAlloc.lsemFuelMemF_live`. A merge
that fails its check is a refusal of the gate (`regionMergeB`).

## The array self-moves

The export moves each carried array at the entry and the exit of a region. After the
coalescing such a move is the load `LOADIDX t, a[z]` followed by the store
`STOREIDX a, a[z], t` of the loaded word to the place it was read from. The allocation
input has, at the positions of such a pair, the liveness instructions `LIVEPIN` that write
`t` from `a` and `z` and read `a`, `z` and `t` (`pinSelfMoves`). `selfNop` replaces both
instructions of such a pair, in place, by the copy `MOV:64 z, z` of the index register onto itself, when
the scratch register `t` is other than `z` and is not live after the pair (`selfPairB`,
against a liveness table). Positions, labels and jump targets are those of the code, and
the replaced positions access no array. `lsemFuelMemF_selfNop` transfers a halting run of
the code to a halting run of `selfNop` of it with the same fuel under a liveness
certificate `JasminLsemExportRegAlloc.LiveCert` of the identity renaming: the two steps
of a pair keep every array and every register other than `t` (`selfMove_steps`), and
every other step is `JasminLsemExportRegAlloc.evalInstrPMemF_live`. The run of the pair
is the hypothesis, so the statement needs no bound on the index. The code `nop` of the
parts is `selfNop` of `regionCoRef` at the synthesised table `liveRegTab` checked by
`regCoB id` (`regionNopB`).

## The parts of the reference

`regionCoParts` computes the pairs, the prefix, the renamed and the merged code, the two
liveness tables, the code without its array self-moves and the reference of the image
check in one record `CoParts`. The steps of the reference are, in order: the coalescing of
the array names, the renaming by the pairs, the register merge, the replacement of the
array self-moves, the multiplication fusion, and the cell fold. `regionCoB` and
`regionCoStage` bind the record once and pass it to `regionMergeB`, `regionNopB`,
`regionSitesB` and `regionFoldB`. A liveness table is an array of name lists, read by
`tabAt`.

## Main definitions

* `regionPrintedB`: the covered printed bodies, `printedAddrWB`.
* `cellArrsOf`: the arrays a printed body accesses through cells.
* `regionCells`: the cell arrays of a region export, those of `cellArrsOf` and the arrays the
  reference accesses at known indices only.
* `restoreB`: the restoration check of the callee-saved registers on the wire of an image:
  the first save `qsave.X := X` of each callee-saved register `X`, no other write to
  `qsave.X`, and the restores `X := qsave.X` as the last six instructions.
* `regionImgCoreB`: the printed class of a body with the gate of the image simulation of
  that class: the class `printedAddrWB`, the checks of its cell accesses and, at its cell
  body, the gate with carry chains `imgGateCW` with the observed names outside its width
  analysis at the return (`retOutsB`).
* `regionImgB`: `regionImgCoreB` and `restoreB` on the image of the cell body.
* `callsTabB`: every call of a body names a symbol of a list.
* `regionImgCB`: the image check at a table, at its frame and its symbols: `callsTabB`, the
  class `decodableLcmd` with `ImageAddrCallW.printedAddrCWB`, the cell checks, the gate of a
  calling body `ImageAddrCallW.imgGateCBW` and `retOutsB` at the cell body, `restoreB`, and
  no observed frame-array name.
* `emptiedEntry`: the entry state of a virtual body with cells.
* `regionFoldB`: the check of the cell fold of the parts.
* `liveArrTab`, `liveArrCert`: the synthesised liveness table of the array names and the
  certificate that reads it (`tabAt`).
* `regionWebsObs`, `regionWebs`, `regionWebsEx`, `regionWebsAt`: the array names read after
  the exported code, the exported code with its array names split into webs
  (`ArrWebs.webRen` under the check `ArrWebs.webB`, the code itself when the check fails),
  the result buffer read after it, and the webs at a callee and the export without one.
* `certArgs`, `crossNames`, `certMerge`: the register pairs and the merge pairs of the
  parts, the allocation certificate at the argument names and at the other names that some
  block reads before it writes them.
* `renImageB`: the image check of a virtual body against a printed body, under a renaming
  of the array names of the slot map.
* `regCoB`, `liveRegTab`: the check of a merge of register names against a liveness
  certificate, and the synthesised liveness table.
* `regCallB`, `callArrNames`, `calleeAA`, `calleeAO`, `calleeOuts`: the call check of a
  merge, the array names of the calls of a body, the array positions and result lengths of
  the symbol of an optional callee, and its out symbols, at which the alias map
  `chainAliasO` sends the destination of a call to its operand at the destination position.
* `CoParts`, `regionCoParts`: the parts of the reference of a region export, with the
  register merge and the liveness tables of the renamed and of the merged code.
* `regionMergeB`: the check of the register merge of the parts.
* `selfMoveB`, `selfPairB`, `selfNop`: an array move of an array onto itself, a position
  of such a move whose scratch register is dead after it, and the code with each such
  move replaced in place by copies of its index register onto itself.
* `regionCoRef`, `regionNopB`: the coalesced, renamed and merged code of the parts and the
  check of its liveness table.
* `fuseSites`, `regionFuse`, `regionSitesB`: the test for a site of the multiplication
  fusion, the fusion as a step of the reference, and the check of the fusion of the parts.
* `regionCoB`, `regionCoStage`: the check of the reference of a region export, and the
  first conjunct of the check that is `false`.
* `regionResultB`: the returned operand is an array parameter of the result's length whose
  register is the result register of the layout.
* `regionCopy`, `resCopyCode`: the array result copy, an `n`-word load and store copy of a
  returned array that is not the result buffer into the result buffer `regionResBuf`;
  the gate checks `regionResultB` at the last version of the buffer after the copy.
* `regionAllocCode`: the code given to the allocation, with liveness instructions in
  place of the array moves of an array onto itself (`pinSelfMoves`) and at the back edges
  (`backEdgePins`).
* `arrBasePins`: the liveness instruction that keeps the array bases and the argument names
  live at entry live together from entry on the array-result allocation
  (`entryPins_live`).
* `backEdgePins_live`: the liveness instruction at a back edge reads every name of the
  register liveness table at its target.
* `regionPostFuse`: the fusion post-pass on an allocated program.
* `regionLprog`: the allocated one-function program of a region export.
* `regionEncode`: the stages after the allocation.
* `regionCtB`, `calleeCtB`: the constant-time check of a printed body, and the check at an
  optional callee.
* `regionBack`: the stages after the narrow-word stages.
* `compileRegion`: the back half: the gate `regionExportableB`, the narrow-word stages
  `narrowPrep` (widening of narrow words, mask elimination, dead-binding elimination), then
  `regionBack` on the widened program.
* `narrowArrB`: the array types of narrow words.
* `layoutMem`: the bytes of the stack words and of the pointer regions of a layout.

## Main results

* `restoreB_sound`: a halting run of an image whose wire passes the restoration check
  `restoreB` ends with every callee-saved register at its entry value;
  `restoreB_of_shape`: the wire of the printer's save prologue, a middle part that writes no
  save slot of a callee-saved register, and the restore epilogue passes `restoreB`.
* `regionPrintedB_of_regionImgB`: a body that passes `regionImgB` is in `regionPrintedB`.
* `regionImgCoreB_of_narrowB`: a body of the narrow class `printedAddrB` with no cell access
  that passes `imgGateB`, and whose indexed stores write to no frame-array name, passes
  `regionImgCoreB` at no cell array.
* `callsTabB_iff`: `callsTabB` holds exactly when every call names a symbol of the list.
* `printedAddrWB_eq`: `printedAddrWB` is `callsTabB []` with `decodableLcmd` and the calling
  class `printedAddrCWB` at every frame.
* `regionImgCB_nil`: at no symbol the image check `regionImgCB` is `regionImgB`, at every
  frame.
* `halts_det`: a halting run of a decoded program has one final state.
* `imgStores_export`: the accesses of the image simulation lie in `layoutMem`, the stack
  words and the pointer regions of the layout.
* `regionImg_sim`: a halting checked run of the image of a printed body that passes
  `regionImgB`, on the decoded bytes of the body, by the simulation of its printed class,
  with the stack register, the callee-saved registers, the bytes outside the accesses and
  the red-zone word, and the accesses of the run of the address machine.
* `regionImg_restore`: every halting run of the decoded bytes of a body that passes
  `regionImgB` ends with the stack register and the callee-saved registers at their entry
  values.
* `regionVirt_run`: the run of the virtual body of a region export from `entryV`.
* `steps_resCopy`, `regionVirt_run_copy`, `regionVirt_memFCT_copy`: the run and the
  events of the result copy, and the virtual body with it.
* `renImage_bytes`: a halting run of a virtual body from `emptiedEntry` on the decoded
  bytes of its printed body, under a renaming of the array names of the slot map.
* `renImage_entry`, `renImage_entry_nil`, `entryA_acorr`: the separation, the entry relation
  of the image and the entry correspondence after the prologue, at any callee; at no cell
  array in the form of the hypotheses of `CheckedIsaCall.haltsC_of_linkedChecksKW`.
* `regionImgB_of_cellFreeB`, `renImageB_of_cellFreeB`, `regionCoParts_of_cellFreeB`,
  `regionCoB_of_cellFreeB`: on a printed body with no cell access the image gate, the image
  check, the parts and the gate are those without cells.
* `regionRef_run`: the run of the coalesced and renamed reference.
* `regionWebs_run`: a halting run of the exported code is matched by a halting run of the
  code of its webs `regionWebs`.
* `regionVirt_steps_webs`, `regionVirt_run_webs`, `regionVirt_run_copy_webs`: the virtual
  body of the webs of a region export from `entryV`, whose state at the end of the webs has
  the variable registers and the arrays at `regionWebsObs` of a state agreeing with the
  returned operands; `regionVirt_run_of_regionExp`, `regionVirt_run_copy_of_regionExp` at
  an exported code of `RegionExp`.
* `liveCert_of_regCoB`, `liveCalls_of_regCoB`, `regCo_run`: an accepted merge of register
  names is a liveness certificate that meets the call condition, and a run of the code is matched by a run of the merged code.
* `selfMove_steps`, `lsemFuelMemF_selfNop`, `selfNop_run`: the two steps of an array
  self-move, and a halting run of code under a liveness certificate matched by a halting
  run of `selfNop` of the code; `lsemFuelMemF_selfNop_calls`, `selfNop_run_calls` at an
  instruction set whose steps beyond `x86Isa` are local calls on words with word results.
* `coRef_bytes_of_regionExp`, `coRef_bytes`: a region export on the decoded bytes through a
  reference behind the coalesced and renamed one, at an exported code of `RegionExp` and at
  the export.
* `regionCo_bytes_of_regionExp`, `regionCo_bytes`: a region export accepted by `regionCoB`
  on the decoded bytes, at an exported code of `RegionExp` and at the export;
  `regionCo_bytes_of_regionExp_virt` with the run of the virtual body behind the final
  machine state (`RegionVirtCells`), and `regionCoB_renImage`, the image check behind
  `regionCoB`.
* `regionVirt_leak`, `regionVirt_memFCT`: every terminating traced run of the virtual body
  of a region export from `entryV` has the events `machRun` of the program, and a program
  that is constant time at the source events has a virtual body that is constant time on
  the traced flag machine between the entry states of `RegionVirtPub`.
* `stepsL_of_lsemFuelMemFLeak`, `stepsL_relocate`: a halting traced run is a traced run of
  steps, and a traced run of steps of a body is one of the body placed between a prefix and
  a suffix.
* `regionVirt_stepsL_webs`, `regionVirt_leak_webs`, `regionVirt_leak_copy_webs`: the
  traced runs of the virtual body of the webs of a region export, whose traces are computed
  by `ArrWebsLeak.webG` along a run of the exported code with the source events.
* `regionWebsLeakB`, `RegionWebsLeak`, `regionExp_webs_cases`: the event check of the webs
  of an exported code, and the two shapes of an exported code that passes it.
* `regionVirt_memFCT_of_regionExp`, `regionVirt_memFCT_copy_of_regionExp`,
  `regionVirtPub_simPub_of_regionExp`, `regionFused_memFCT_of_regionExp`,
  `regionRef_memFCT_of_regionExp`, `regionImage_memFCT_of_regionExp`,
  `regionWide_bytes_ct_of_regionExp`: the constant-time theorems at an exported code of
  `RegionExp` that passes `RegionWebsLeak`; the theorems without the suffix are their
  instances at the export.
* `regionVirtPub_simPub`, `renStart_entryV`: two states of `RegionVirtPub` are states at
  position `0` with terminating runs of the virtual body, and the entry state meets the
  array condition of the renaming by pairs.
* `selfNop_leak_step`, `lsemFuelMemFLeak_selfNop`, `selfNop_memFCT`: two halting traced
  runs of code with one trace are matched by halting traced runs of `selfNop` of the code
  with one trace, and constant time of the code gives constant time of `selfNop` of it.
* `regionFused_memFCT`, `prefixFold_gtr`, `regionRef_memFCT`: constant time of the fused
  code of the gate, the trace of a quiet prefix followed by a cell fold, and constant time
  of the reference of the gate between the entry states of `RegionImgPub`.
* `regionImage_memFCT`: constant time of the image of the cell body of the printed body.
* `regionCell_entry`: the facts of the image simulation at the entry with cells.
* `regionWide_bytes_ct`: the decoded bytes of a printed body that passes `regionCoB` and
  the three checks of `regionCtB` are constant time between states of `RegionBytePub`.
* `calleeCutB_soundK`: the cut checks of a calling body at the empty function name give
  `LprogCallCut.CutCheckSoundI` on `CheckedIsaCall.x86IsaK` at every function name.
* `calleeBody_imgRun`: under the checks `calleeBodyB`, a halting run of the reference of a
  calling body is matched by a halting run of the bounds-checked instruction set on its
  image.
* `outDestB_iff`, `outDestB_of_callParamsB`: the check that the destination operand of an
  out callee is no other array operand, decided, and implied by `callParamsB`.
* `calleeSite_dest`: at a call of an out callee the destination of its call site is an array
  of the slot map; that the operands pass the parameters of the callee is
  `RegionLinkRoute.callParamsB_forall₂W`.
* `decodeSites_spec`, `decodeSites_isSome`, `bodyCallSymsB_of_decodeSites`: the decode
  `decodeSites` of a calling body lists, at the positions of its calls, the symbol, the
  destination and the operands of each call, and succeeds exactly when every call names a
  symbol of the table of callees.
* `siteFn_lookup`, `shadows_callImg`: the site function `siteFn` at the table of one callee
  is its call site at every call, and the shadow instructions of the image at `siteFn` are
  the shadows of the decoded sites, in order.
* `CalleeTab`, `CalleeTab.lookup`, `.names`, `.tab`, `.frame`, `.pool`, `.outs`, `.common`,
  `.sigOf`, `.outOf`: a table of linked functions and its derived data, with the `_one` lemmas
  at the table `CalleeTab.one c` of one function.
* `calleeImgT`, `calleeCodeT`, `calleeAAT`, `calleeAOT`, `calleeOutsT`, `calleeImgBT`,
  `callParamsBT`, `calleeDeadBT`, `calleeCodeBT`: the callee-dependent functions at an optional
  table. `calleeAA`, `calleeAO`, `calleeOuts`, `callParamsB`, `calleeImgB` are applications
  of these forms at one function; `calleeImgT_one`, `calleeCodeT_one`, `calleeDeadBT_one`,
  `calleeCodeBT_one` relate the others.
* `calleeCodeBT_keep`, `calleeCodeBT_sound`: the code of each function of a table passes the
  keep check `Callee.keepCheckAtB` at its clobber set, its frame and its declared store policy
  (`CalleeData.pol`), so it holds no `call` and, from an entry state whose out windows are
  separate from its frame, keeps the stack register, the registers outside its clobber set and
  the bytes outside its frame and its out windows.
* `CalleeTab.bytes`, `.symPos`, `.entryOff`, `.entryIdx`, `.linkMap`: the code of a table, the
  position of a symbol, the byte offset and the instruction index of the entry of a function
  in that code, and the target map of the symbols of a table behind a caller; the entry of the
  first function is at offset and index `0`, read without decoding the code.
* `calleeLinkB_one`, `calleeProg_one`, `calleeCtB_one`, `calleeSym_one`: the bytes stages at the
  table of one function.
* `CalleeTab.tgtPos?`, `CalleeTab.ctIfc`, `CalleeTab.ctDst`, `CalleeTab.clobB`: the interface of
  a table at the call targets behind a caller, with their forms at one function
  (`CalleeTab.ctIfc_one`, `CalleeTab.ctDst_one`, `CalleeTab.clobB_one`) and at the entry of
  the function of a symbol (`CalleeTab.entryIdx_inj`, `CalleeTab.tgtPos?_entry`,
  `CalleeTab.ctIfc_entry`, `CalleeTab.ctDst_entry`, `CalleeTab.clob_of_clobB`).
* `calleeCtB_tab`: a table at which the constant-time check holds gives the program of the
  function, which passes `AbiLayout.ctCheckRXT` at the interface of the table.
* `CalleeTab.regionB`, `CalleeTab.regionB_spec`: the check that the entries of the functions of
  a table are instructions of the decoded code of the table.
* `CalleeTab.regionEntries`, `CalleeTab.regionBlocks`, `CalleeTab.regionCode_lookup`: the code
  of a table is a region of the blocks of its functions, at the entry offsets and indices of
  the table.
* `codeCallSyms`, `regionCallee_tab`, `regionCallee_some_stackArr`, `regionCallee_sublist`,
  `regionCallee_self`, `regionCallee_singleton`: the called symbols of an exported code and the
  table `regionCallee` finds, the linked functions of these symbols.
* `symTgt_linkMap_regionTgt`, `calleeBytes_decode`, `calleeBytes_decode_one`: the bytes of a
  calling body at a table decode to the program of the function followed by the region of the
  code of the table.
* `calleeChecksB`, `CalleeChecksOK`, `calleeChecksB_spec`: the checks of a calling body at the
  data its callees give. `calleeBodyB`, `CalleeBodyOK` take that data from one function and
  `calleeBodyBT`, `CalleeBodyOKT` from a table; `calleeBodyBT_one`, `calleeBodyB_of_one` relate
  them on a body that decodes at the function and ends in the return.
* `calleeBodyB_spec`, `CalleeBodyOK.shapeImg`, `calleeBodyB_nodup`: the checks `calleeBodyB`
  are the fields of `CalleeBodyOK`; under them the image has the shape of the call sites,
  and the operands of each call of a callee whose code does not decode are pairwise
  distinct.
* `calleeBody_stackRoom`, `calleeBody_callerSep`: under the checks `calleeBodyB`, the stack
  room and frame checks at the frame of the callee, and the caller separation
  `ImageAddrCall.CallerSep` from the entry conditions of the layout.
* `regionBack_spec`: the checks a result of `regionBack` passed.
* `regionBack_correct`: for a result `(P, bytes)` of `regionBack σ a p`, from every
  entry state satisfying `σ.Regions`, at every valuation the layout reads off it at which
  `p` denotes a value at some fuel, the bytes decode to a program that halts on the machine
  in a state from which `σ` reads back that value, with the entry stack register, the entry
  bytes outside the stack words and the pointer regions, and a halting run of the address
  machine whose accesses lie in `layoutMem`.
* `abiValOf_widen`, `denVal_wideTy_transTy`: a valuation the layout reads holds 64-bit
  words, so the layout reads its widening; the widened value of a result other than a narrow
  array is its value.
* `compileRegion_eq_some`, `compileRegion_spec`: a result of `compileRegion` is a result of
  `regionBack` on the widened program, with the checks it passed.
* `compileRegion_correct`: `regionBack_correct` through the narrow-word stages, at the
  widened valuation `mapVal V` (narrow arguments in 64-bit slots with zero high bits) and
  the widened result.
* `compileRegion_correct_wide`: the same statement as `regionBack_correct` for
  `compileRegion` at a valuation of 64-bit words and a result other than a narrow array.
* `compileRegion_wide`, `compileRegion_ctx`: over a context (and result type) of 64-bit
  words, the back half runs on the widened program carried back to them, which denotes the
  (widened) denotation of the source.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (lsemFuelMemF_segF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf_isLopn movesOf_length)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf AbiEntryM
  storeAgreesM_of_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody cellBody_getElem?
  cellMove_of_none CellNoSlot CellFrames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameNames frameMark frameOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (imgGateB cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW retOutsB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx (imgGateCW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots isArrB isCellB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (cellIdx frameC slotArrC
  frameMarkC emptyArrs cellAccB cellNoSlotB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW (cellArrsR baseR cellNamesRB
  slotArrC_nil)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg (cellFoldLR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (runA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (AccessIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrStore (imgStores)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-! ## 1. The image check of a virtual body -/

/-- No instruction of `body` is a cell access (`JasminLsemAddrMem.cellA?`). -/
def cellFreeB (body : Lcmd) : Bool :=
  body.all fun i => (JasminLsemAddrMem.cellA? i.li_i).isNone

/-- **The covered printed bodies of a region export**: the class with carry chains, untagged
    immediate moves and cell accesses `DecodePrintedAddrW.printedAddrWB`, which contains the
    class `DecodePrintedCFG.printedAddrB` (`ImageAddrCallW.printedAddrWB_of_printedAddrB`). -/
def regionPrintedB (body : Lcmd) : Bool :=
  printedAddrWB body

/-- **The cell arrays of a printed body**: the arrays of `all` that some cell access of
    `body` reaches, an access whose base register holds the pointer of the array at the
    slot map `sl` (`JasminLsemAddrImage.accArr`). -/
def cellArrsOf (sl : String → Option (String × Nat)) (all : Slots) (body : Lcmd) : Slots :=
  all.filter fun p => (List.range body.length).any fun k =>
    match body[k]? with
    | some i =>
        match JasminLsemAddrMem.cellA? i.li_i with
        | some (.ld _ B _) => (JasminLsemAddrImage.accArr sl body k B).any (·.1 == p.1)
        | some (.st B _ _) => (JasminLsemAddrImage.accArr sl body k B).any (·.1 == p.1)
        | _ => false
    | none => false

/-- The array, with its length, that the cell access at position `k` of the array `a` of a
    body reaches (`JasminLsemAddrImage.accArrA`); `none` at a position with no cell access. -/
def cellArrAt (sl : String → Option (String × Nat)) (a : Array Linstr) (k : Nat) :
    Option (String × Nat) :=
  match a[k]? with
  | some i =>
      match JasminLsemAddrMem.cellA? i.li_i with
      | some (.ld _ B _) => JasminLsemAddrImage.accArrA sl a k B
      | some (.st B _ _) => JasminLsemAddrImage.accArrA sl a k B
      | _ => none
  | none => none

/-- `cellArrsOf` with the arrays reached by the cell accesses of the body (`cellArrAt`)
    computed once, on the array of the body. -/
def cellArrsOfImpl (sl : String → Option (String × Nat)) (all : Slots) (body : Lcmd) :
    Slots :=
  let a := body.toArray
  let acc := (List.range a.size).map (cellArrAt sl a)
  all.filter fun p => acc.any fun o => o.any (·.1 == p.1)

/-- The cell arrays `cellArrsOf` are evaluated as `cellArrsOfImpl`. -/
@[csimp] theorem cellArrsOf_eq_impl : @cellArrsOf = @cellArrsOfImpl := by
  funext sl all body
  simp only [cellArrsOf, cellArrsOfImpl, List.size_toArray, List.any_map]
  congr 1
  funext p
  congr 1
  funext k
  simp only [Function.comp_apply, cellArrAt, List.getElem?_toArray,
    JasminLsemAddrImage.accArrA_toArray]
  split <;> split <;> simp_all

/-- A body with no cell access has no cell array. -/
theorem cellArrsOf_of_cellFreeB (sl : String → Option (String × Nat)) (all : Slots)
    {body : Lcmd} (h : cellFreeB body = true) : cellArrsOf sl all body = [] := by
  unfold cellArrsOf
  rw [List.filter_eq_nil_iff]
  intro p _
  rw [Bool.not_eq_true, List.any_eq_false]
  intro k _
  cases hb : body[k]? with
  | none => simp
  | some i =>
      have hi := Option.isNone_iff_eq_none.mp
        (List.all_eq_true.mp h i (List.mem_of_getElem? hb))
      simp [hi]

/-- A body with no cell access passes the check `cellAccB` of its cell accesses, at every
    cell arrays. -/
theorem cellAccB_of_cellFreeB (sl : String → Option (String × Nat)) (R : Slots) {body : Lcmd}
    (h : cellFreeB body = true) : cellAccB sl R body = true := by
  unfold cellAccB
  rw [List.all_eq_true]
  intro k _
  cases hb : body[k]? with
  | none => rfl
  | some i =>
      have hi := Option.isNone_iff_eq_none.mp
        (List.all_eq_true.mp h i (List.mem_of_getElem? hb))
      simp [hi]

/-- A body with no cell access passes the check `cellNoSlotB`. -/
theorem cellNoSlotB_of_cellFreeB (sl : String → Option (String × Nat)) {body : Lcmd}
    (h : cellFreeB body = true) : cellNoSlotB sl body = true := by
  unfold cellNoSlotB
  rw [List.all_eq_true]
  intro k _
  cases hb : body[k]? with
  | none => rfl
  | some i =>
      have hi := List.all_eq_true.mp h i (List.mem_of_getElem? hb)
      simp [hi]

/-- The cell body of a body with no cell access is the body. -/
theorem cellBody_of_cellFreeB (sl : String → Option (String × Nat)) {body : Lcmd}
    (h : cellFreeB body = true) : cellBody sl body = body := by
  refine List.ext_getElem? fun k => ?_
  rw [cellBody_getElem?]
  cases hk : body[k]? with
  | none => rfl
  | some i =>
      have hi := List.all_eq_true.mp h i (List.mem_of_getElem? hk)
      simp only [Option.map_some, cellMove_of_none (Option.isNone_iff_eq_none.mp hi)]

/-- A body with no cell access has no slot name in a cell move. -/
theorem cellNoSlot_of_cellFreeB (sl : String → Option (String × Nat)) {body : Lcmd}
    (h : cellFreeB body = true) : CellNoSlot sl body := fun _ i _ _ hk _ hc =>
  (hc (Option.isNone_iff_eq_none.mp
    (List.all_eq_true.mp h i (List.mem_of_getElem? hk)))).elim

/-- A body with no cell access meets the conditions on the frames of its cell accesses. -/
theorem cellFrames_of_cellFreeB (frame : String → Option (BitVec 64))
    (sl : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    {body : Lcmd} (h : cellFreeB body = true) : CellFrames frame sl base rsp body := by
  have hn : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi →
      JasminLsemAddrMem.cellA? bi.li_i = none := fun k bi hk =>
    Option.isNone_iff_eq_none.mp (List.all_eq_true.mp h bi (List.mem_of_getElem? hk))
  constructor
  · intro k bi D B off hk hc
    rw [hn k bi hk] at hc
    cases hc
  · intro k bi B off S hk hc _
    rw [hn k bi hk] at hc
    cases hc
  · intro k bi D B off hk hc
    rw [hn k bi hk] at hc
    cases hc
  · intro k bi B off S hk hc _
    rw [hn k bi hk] at hc
    cases hc

/-! ### Restoration of the callee-saved registers

The printer saves each callee-saved register `X` into its frame slot `qsave.X` in its
prologue (`ExportPhysAbi.buildPrologue`) and restores it in its epilogue
(`ExportPhysAbi.calleeSaveRestoreEpilogue`). `restoreB` checks this shape on the wire of the
image of a body, and `restoreB_sound` gives the restoration on every halting run of the
image. -/

section RestoreCheck

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel findLabel_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedRegs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (NextPc evalInstrPMemF_next)

/-- The instruction is an `Lopn`. -/
def isLopnR : LinstrR → Bool
  | .Lopn .. => true
  | _ => false

/-- The instruction is an `Lopn`, a label, a jump or a conditional jump. -/
def restKindB : LinstrR → Bool
  | .Lopn .. | .Llabel .. | .Lgoto .. | .Lcond .. => true
  | _ => false

/-- The instruction is a 64-bit move (`slotMov?`) of the register `X` into its frame slot
    `qsave.X`. -/
def saveOfB (X : String) (x : LinstrR) : Bool := slotMov? x == some (slotOfReg X, X)

/-- A 64-bit move of `slotMov?` is an `Lopn` with one register destination and one register
    source, at the mnemonic `MOVQ` or `MOV:64`. -/
theorem slotMov?_lopn {x : LinstrR} {d s : String} (h : slotMov? x = some (d, s)) :
    ∃ o, x = .Lopn [.reg d] o [.reg s] ∧ (o = "MOVQ" ∨ o = "MOV:64") := by
  unfold slotMov? at h
  split at h
  · split_ifs at h with h1 h2
    cases h
    exact ⟨_, rfl, h1⟩
  · cases h

/-- A step of a 64-bit move `d := s` writes the value of `s` to `d`. -/
theorem evalInstrPMemF_slotMov (P : LprogM) {x : LinstrR} {d s : String}
    (h : slotMov? x = some (d, s)) (tag : MemTag) {st st' : LstateMF}
    (he : evalInstrPMemF P (x, tag) st = some st') :
    st'.prog.base.reg.lvm d = st.prog.base.reg.lvm s := by
  obtain ⟨o, rfl, ho⟩ := slotMov?_lopn h
  have hm : movRegArgs? (LinstrR.Lopn [.reg d] o [.reg s], tag) = some (d, s) := by
    rcases ho with rfl | rfl
    · simp [movRegArgs?]
    · simp [movRegArgs?]
      decide
  simp only [evalInstrPMemF, cmpArgs?, hm, readReg] at he
  cases he
  simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc]

/-- A label, a jump or a conditional jump keeps every register. -/
theorem evalInstrPMemF_lvm_ctl (P : LprogM) {x : LinstrR} (hk : restKindB x = true)
    (hl : isLopnR x = false) (tag : MemTag) {s t : LstateMF}
    (h : evalInstrPMemF P (x, tag) s = some t) :
    t.prog.base.reg.lvm = s.prog.base.reg.lvm := by
  cases x <;> simp only [restKindB, isLopnR, Bool.false_eq_true, reduceCtorEq] at hk hl
  · rw [JasminLsemMemFlagNestJoin.evalInstrPMemF_label] at h
    cases h
    rfl
  · rename_i tg
    obtain ⟨f, l⟩ := tg
    have he : evalInstrPMemL P (.Lgoto (f, l), tag) s.prog
        = if f = P.lfn then evalJumpMem P l s.prog else none := rfl
    simp only [evalInstrPMemF, cmpArgs?, movRegArgs?, flagCondCC?, he, carryArgs?,
      wideArgs?, withALUFlags, aluFlagOp?] at h
    split_ifs at h
    split at h
    · rename_i p hp
      cases h
      unfold evalJumpMem at hp
      split at hp <;> cases hp
      rfl
    · cases h
  · rename_i c l
    simp only [evalInstrPMemF, cmpArgs?, movRegArgs?] at h
    split at h
    · split at h
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
        unfold evalJumpMem at hp
        split at hp <;> cases hp
        rfl
      · cases h
        rfl
    · split at h
      · rename_i p hp
        cases h
        have hw : withALUFlags (LinstrR.Lcond c l, tag) s.prog.base p.base = p.base := by
          simp [withALUFlags, aluFlagOp?]
        simp only [hw]
        simp only [evalInstrPMemL] at hp
        split at hp
        · unfold evalJumpMem at hp
          split at hp <;> cases hp
          rfl
        · cases hp
          rfl
      · simp [carryArgs?, wideArgs?] at h

/-- A step of an instruction of `restKindB` keeps every name outside its destinations. -/
theorem evalInstrPMemF_keep (P : LprogM) {x : LinstrR} (hk : restKindB x = true)
    (tag : MemTag) {s t : LstateMF} (h : evalInstrPMemF P (x, tag) s = some t) {y : String}
    (hy : y ∉ dstNames x) : t.prog.base.reg.lvm y = s.prog.base.reg.lvm y := by
  cases hl : isLopnR x
  · rw [evalInstrPMemF_lvm_ctl P hk hl tag h]
  · have hi : JasminLsemMemLoop.IsLopn (x, tag) := by
      cases x <;> simp only [isLopnR, Bool.false_eq_true] at hl
      exact ⟨_, _, _, rfl⟩
    exact X86Backend.ImageAddrSim.evalInstrPMemF_lvm_of_not_dst P hi h hy

/-- The successor of an `Lopn` is the next instruction. -/
theorem nextPc_lopn {wl : List LinstrR} {x : LinstrR} (hl : isLopnR x = true) {pc pc' : Nat}
    (h : NextPc wl x pc pc') : pc' = pc + 1 := by
  cases x <;> simp_all [isLopnR, NextPc]

/-- The successor of an instruction of `restKindB` is the next instruction or the
    instruction after a label of `wl`. -/
theorem nextPc_restKind {wl : List LinstrR} {x : LinstrR} (hk : restKindB x = true)
    {pc pc' : Nat} (h : NextPc wl x pc pc') :
    pc' = pc + 1 ∨ ∃ q y, wl[q]? = some y ∧ isLopnR y = false ∧ pc' = q + 1 := by
  have hlab : ∀ l q, findLabel l wl = some q → ∃ y, wl[q]? = some y ∧ isLopnR y = false := by
    intro l q hq
    obtain ⟨y, hy, hl⟩ := findLabel_sound l wl q hq
    refine ⟨y, hy, ?_⟩
    cases y <;> simp_all [JasminLsemLabeled.isLabel, isLopnR]
  cases x <;> simp only [restKindB, Bool.false_eq_true] at hk <;>
    simp only [NextPc] at h
  · exact Or.inl h
  · exact Or.inl h
  · obtain ⟨q, hq, rfl⟩ := h
    obtain ⟨y, hy, hl⟩ := hlab _ q hq
    exact Or.inr ⟨q, y, hy, hl, rfl⟩
  · rcases h with h | ⟨q, hq, rfl⟩
    · exact Or.inl h
    · obtain ⟨y, hy, hl⟩ := hlab _ q hq
      exact Or.inr ⟨q, y, hy, hl, rfl⟩

/-- The facts of a wire `w` from which the restoration of the register `X` follows: the save
    of `X` at `i`, preceded only by `Lopn`s that do not write `X`; no other instruction writes
    `qsave.X`, and every instruction is of `restKindB`; the restore of `X` at `r > i`, from
    which on every instruction is an `Lopn` and none after `r` writes `X`. -/
structure RestoreFacts (w : List LinstrR) (X : String) (i r : Nat) : Prop where
  /-- The save precedes the restore. -/
  lt : i < r
  /-- The restore is an instruction of `w`. -/
  rlt : r < w.length
  /-- Every instruction before the save is an `Lopn` that does not write `X`. -/
  pre : ∀ k x, w[k]? = some x → k < i → isLopnR x = true ∧ X ∉ dstNames x
  /-- The save of `X` at `i`. -/
  save : ∃ x, w[i]? = some x ∧ slotMov? x = some (slotOfReg X, X)
  /-- Every other instruction is of `restKindB` and does not write `qsave.X`. -/
  mid : ∀ k x, w[k]? = some x → k ≠ i → restKindB x = true ∧ slotOfReg X ∉ dstNames x
  /-- The restore of `X` at `r`. -/
  rest : ∃ x, w[r]? = some x ∧ slotMov? x = some (X, slotOfReg X)
  /-- From the restore on every instruction is an `Lopn`. -/
  post : ∀ k x, w[k]? = some x → r ≤ k → isLopnR x = true
  /-- No instruction after the restore writes `X`. -/
  postX : ∀ k x, w[k]? = some x → r < k → X ∉ dstNames x

/-- The invariant of the restoration of `X` along a run, at the entry value `X0`. -/
def RInv (w : List LinstrR) (X : String) (i r : Nat) (X0 : Σ n, BitVec n) (fn : String)
    (s : LstateMF) : Prop :=
  s.prog.lfn = fn ∧ s.prog.base.lpc ≤ w.length
    ∧ (s.prog.base.lpc ≤ i → s.prog.base.reg.lvm X = X0)
    ∧ (i < s.prog.base.lpc → s.prog.base.reg.lvm (slotOfReg X) = X0)
    ∧ (r < s.prog.base.lpc → s.prog.base.reg.lvm X = X0)

/-- A step of the checked machine keeps the invariant `RInv`. -/
theorem rinv_step {img : List LinstrRM} {X : String} {i r : Nat} {X0 : Σ n, BitVec n}
    {fn : String} (F : RestoreFacts (img.map Prod.fst) X i r) {ck : Bool} {s s' : LstateMF}
    {x : LinstrRM} (hI : RInv (img.map Prod.fst) X i r X0 fn s)
    (hf : findInstrMem (singletonProgM fn img) s.prog = some x)
    (he : evalInstrPMemFk ck (singletonProgM fn img) x s = some s') :
    RInv (img.map Prod.fst) X i r X0 fn s' := by
  obtain ⟨hfn, -, h1, h2, h3⟩ := hI
  have he' := evalInstrPMemF_of_k he
  obtain ⟨hfn', hnext⟩ := evalInstrPMemF_next _ x s s' he'
  have hx : img[s.prog.base.lpc]? = some x := by
    simpa [findInstrMem, singletonProgM, hfn] using hf
  have hw : (img.map Prod.fst)[s.prog.base.lpc]? = some x.1 := by simp [hx]
  have hlt : s.prog.base.lpc < (img.map Prod.fst).length :=
    (List.getElem?_eq_some_iff.mp hw).1
  obtain ⟨x1, tag⟩ := x
  simp only [singletonProgM] at hnext
  have hstep : evalInstrPMemF (singletonProgM fn img) (x1, tag) s = some s' := he'
  refine ⟨hfn'.trans hfn, ?_⟩
  simp only [List.length_map] at hlt ⊢
  rcases Nat.lt_trichotomy s.prog.base.lpc i with hpi | hpi | hpi
  · obtain ⟨hl, hX⟩ := F.pre _ x1 hw hpi
    have hn := nextPc_lopn hl hnext
    have hk : restKindB x1 = true := by cases x1 <;> simp_all [isLopnR, restKindB]
    have hkeep := evalInstrPMemF_keep _ hk tag hstep hX
    have := F.lt
    exact ⟨by omega, fun _ => hkeep.trans (h1 hpi.le), fun h => by omega, fun h => by omega⟩
  · subst hpi
    obtain ⟨y, hy, hsv⟩ := F.save
    rw [hw] at hy
    cases hy
    have hl : isLopnR x1 = true := by
      obtain ⟨o, rfl, -⟩ := slotMov?_lopn hsv
      rfl
    have hn := nextPc_lopn hl hnext
    have := F.lt
    exact ⟨by omega, fun h => by omega,
      fun _ => (evalInstrPMemF_slotMov _ hsv tag hstep).trans (h1 le_rfl), fun h => by omega⟩
  · obtain ⟨hk, hq⟩ := F.mid _ x1 hw (by omega)
    have hQ : s'.prog.base.reg.lvm (slotOfReg X) = X0 :=
      (evalInstrPMemF_keep _ hk tag hstep hq).trans (h2 hpi)
    rcases Nat.lt_trichotomy s.prog.base.lpc r with hpr | hpr | hpr
    · rcases nextPc_restKind hk hnext with hn | ⟨q, y, hy, hl, hn⟩
      · exact ⟨by omega, fun h => by omega, fun _ => hQ, fun h => by omega⟩
      · have hqlt : q < img.length := by
          simpa using (List.getElem?_eq_some_iff.mp hy).1
        have hqi : i < q := by
          by_contra hc
          rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hc) with hc | hc
          · rw [(F.pre q y hy hc).1] at hl
            cases hl
          · subst hc
            obtain ⟨z, hz, hsv⟩ := F.save
            rw [hy] at hz
            cases hz
            obtain ⟨o, rfl, -⟩ := slotMov?_lopn hsv
            cases hl
        have hqr : q < r := by
          by_contra hc
          rw [F.post q y hy (by omega)] at hl
          cases hl
        exact ⟨by omega, fun h => by omega, fun _ => hQ, fun h => by omega⟩
    · subst hpr
      obtain ⟨y, hy, hsv⟩ := F.rest
      rw [hw] at hy
      cases hy
      have hn := nextPc_lopn (F.post _ x1 hw le_rfl) hnext
      exact ⟨by omega, fun h => by omega, fun _ => hQ,
        fun _ => (evalInstrPMemF_slotMov _ hsv tag hstep).trans (h2 hpi)⟩
    · have hn := nextPc_lopn (F.post _ x1 hw hpr.le) hnext
      have hkX := evalInstrPMemF_keep _ hk tag hstep (F.postX _ x1 hw hpr)
      exact ⟨by omega, fun h => by omega, fun _ => hQ, fun _ => hkX.trans (h3 hpr)⟩

/-- A halting run of the checked machine keeps the invariant `RInv` and ends where no
    instruction is fetched. -/
theorem rinv_run {img : List LinstrRM} {X : String} {i r : Nat} {X0 : Σ n, BitVec n}
    {fn : String} (F : RestoreFacts (img.map Prod.fst) X i r) {ck : Bool} {t : LstateMF} :
    ∀ (f : Nat) (s : LstateMF), RInv (img.map Prod.fst) X i r X0 fn s →
      lsemFuelMemFk ck (singletonProgM fn img) f s = some t →
      RInv (img.map Prod.fst) X i r X0 fn t
        ∧ findInstrMem (singletonProgM fn img) t.prog = none
  | 0, s, hI, h => by
      simp only [lsemFuelMemFk] at h
      split at h
      · cases h
        exact ⟨hI, ‹_›⟩
      · cases h
  | f + 1, s, hI, h => by
      simp only [lsemFuelMemFk] at h
      split at h
      · cases h
        exact ⟨hI, ‹_›⟩
      · rename_i x hx
        split at h
        · rename_i s' hs'
          exact rinv_run F f s' (rinv_step F hI hx hs') h
        · cases h

/-- **A halting run keeps `X`** under the facts `RestoreFacts`: from program counter `0`,
    the final state holds at `X` the value of the entry state. -/
theorem restore_of_facts {img : List LinstrRM} {X : String} {i r : Nat}
    (F : RestoreFacts (img.map Prod.fst) X i r) {ck : Bool} {fn : String} {f : Nat}
    {s t : LstateMF} (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (h : lsemFuelMemFk ck (singletonProgM fn img) f s = some t) :
    t.prog.base.reg.lvm X = s.prog.base.reg.lvm X := by
  have hI : RInv (img.map Prod.fst) X i r (s.prog.base.reg.lvm X) fn s :=
    ⟨hfn, by omega, fun _ => rfl, fun h => by omega, fun h => by omega⟩
  obtain ⟨⟨htfn, hle, -, -, h3⟩, hnone⟩ := rinv_run F f s hI h
  have hge : img.length ≤ t.prog.base.lpc := by
    simpa [findInstrMem, singletonProgM, htfn] using hnone
  have := F.rlt
  simp only [List.length_map] at hle this
  exact h3 (by omega)

/-- **The restoration check of the register `X`** on the wire `w` of an image: the first
    save of `X` (`saveOfB`) is at an index `i` with `i + 6 < w.length`; every instruction
    before `i` is an `Lopn` that does not write `X`; every other instruction is of
    `restKindB` and does not write `qsave.X`. -/
def restoreRegB (w : List LinstrR) (X : String) : Bool :=
  match w.findIdx? (saveOfB X) with
  | none => false
  | some i =>
      decide (i + 6 < w.length) &&
      (List.range w.length).all fun k =>
        match w[k]? with
        | some x =>
            (!decide (k < i) || (isLopnR x && !(dstNames x).contains X))
              && (k == i || (restKindB x && !(dstNames x).contains (slotOfReg X)))
        | none => true

/-- **The callee-saved restoration check** on the wire `w` of an image: its last six
    instructions are the restores `X := qsave.X` of the callee-saved registers
    `calleeSavedRegs`, in order, and each of them passes `restoreRegB`. -/
def restoreB (w : List LinstrR) : Bool :=
  decide (6 ≤ w.length)
    && ((w.drop (w.length - 6)).map slotMov?
      == calleeSavedRegs.map fun X => some (X, slotOfReg X))
    && calleeSavedRegs.all (restoreRegB w)

/-- The conditions `restoreRegB` checks: the first save of `X` at `i`, the instructions
    before it, and every other instruction. -/
theorem restoreRegB_spec {w : List LinstrR} {X : String} (h : restoreRegB w X = true) :
    ∃ i, i + 6 < w.length
      ∧ (∃ x, w[i]? = some x ∧ slotMov? x = some (slotOfReg X, X))
      ∧ (∀ k x, w[k]? = some x → k < i → isLopnR x = true ∧ X ∉ dstNames x)
      ∧ (∀ k x, w[k]? = some x → k ≠ i → restKindB x = true ∧ slotOfReg X ∉ dstNames x) := by
  unfold restoreRegB at h
  split at h
  · cases h
  · rename_i i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨hlt, hall⟩ := h
    obtain ⟨hil, hsv, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
    have hat : ∀ k x, w[k]? = some x →
        ((!decide (k < i) || (isLopnR x && !(dstNames x).contains X))
          && (k == i || (restKindB x && !(dstNames x).contains (slotOfReg X)))) = true := by
      intro k x hk
      have := hall k (List.getElem?_eq_some_iff.mp hk).1
      rwa [hk] at this
    refine ⟨i, hlt, ⟨w[i], List.getElem?_eq_getElem hil, by simpa [saveOfB] using hsv⟩,
      fun k x hk hki => ?_, fun k x hk hki => ?_⟩
    · have := hat k x hk
      simp only [hki, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.not_eq_true'] at this
      exact ⟨this.1.1, by simpa using this.1.2⟩
    · have := hat k x hk
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, hki, false_or,
        Bool.not_eq_true'] at this
      exact ⟨this.2.1, by simpa using this.2.2⟩

/-- The only destination of a 64-bit move of `slotMov?` is its destination register. -/
theorem dstNames_slotMov {x : LinstrR} {d s : String} (h : slotMov? x = some (d, s)) :
    dstNames x = [d] ∧ isLopnR x = true := by
  obtain ⟨o, rfl, -⟩ := slotMov?_lopn h
  simp [dstNames, isLopnR, JasminLsemExportRewrites.opNames]

/-- **The facts of the restoration of a callee-saved register** on a wire that passes
    `restoreB`: the save of `X` at its first save and the restore of `X` in the last six
    instructions. -/
theorem restoreB_facts {w : List LinstrR} (h : restoreB w = true) {X : String}
    (hX : X ∈ calleeSavedRegs) : ∃ i r, RestoreFacts w X i r := by
  simp only [restoreB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
    at h
  obtain ⟨⟨h6, hep⟩, hall⟩ := h
  obtain ⟨i, hi6, hsv, hpre, hmid⟩ := restoreRegB_spec (hall X hX)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hX
  have hcs : calleeSavedRegs.length = 6 := rfl
  have hnd : calleeSavedRegs.Nodup := by decide
  have E : ∀ m (hm : m < 6), ∃ x, w[w.length - 6 + m]? = some x
      ∧ slotMov? x = some (calleeSavedRegs[m], slotOfReg calleeSavedRegs[m]) := by
    intro m hm
    have := congrArg (·[m]?) hep
    simp only [List.getElem?_map, List.getElem?_drop] at this
    cases hw : w[w.length - 6 + m]? with
    | none =>
        rw [hw] at this
        simp at this
        omega
    | some x =>
        rw [hw] at this
        refine ⟨x, rfl, ?_⟩
        simp only [List.getElem?_eq_getElem (show m < calleeSavedRegs.length by omega),
          Option.map_some, Option.some.injEq] at this
        exact this
  refine ⟨i, w.length - 6 + j, ⟨by omega, by omega, hpre, hsv, hmid, E j (by omega),
    fun k x hk hrk => ?_, fun k x hk hrk => ?_⟩⟩
  · have hkl := (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨y, hy, hm⟩ := E (k - (w.length - 6)) (by omega)
    rw [show w.length - 6 + (k - (w.length - 6)) = k by omega, hk] at hy
    cases hy
    exact (dstNames_slotMov hm).2
  · have hkl := (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨y, hy, hm⟩ := E (k - (w.length - 6)) (by omega)
    rw [show w.length - 6 + (k - (w.length - 6)) = k by omega, hk] at hy
    cases hy
    rw [(dstNames_slotMov hm).1, List.mem_singleton]
    intro he
    have := (hnd.getElem_inj_iff).mp he
    omega

/-- **Soundness of the restoration check.** A halting run of an image whose wire passes
    `restoreB`, from program counter `0`, ends with every callee-saved register at its
    entry value. -/
theorem restoreB_sound {img : List LinstrRM} (h : restoreB (img.map Prod.fst) = true)
    {ck : Bool} {fn : String} {f : Nat} {s t : LstateMF} (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 0)
    (hr : lsemFuelMemFk ck (singletonProgM fn img) f s = some t) :
    ∀ X ∈ calleeSavedRegs, t.prog.base.reg.lvm X = s.prog.base.reg.lvm X := by
  intro X hX
  obtain ⟨i, r, F⟩ := restoreB_facts h hX
  exact restore_of_facts F hfn hpc hr

/-- `restoreRegB` on a wire `A ++ B` whose first save of `X` is at `i` in `A`: the conditions
    of the check on the instructions of `A` and of `B`. -/
theorem restoreRegB_append {A B : List LinstrR} {X : String} {i : Nat}
    (hi : A.findIdx? (saveOfB X) = some i) (h6 : i + 6 < A.length + B.length)
    (hA : (List.range A.length).all (fun k =>
      match A[k]? with
      | some x =>
          (!decide (k < i) || (isLopnR x && !(dstNames x).contains X))
            && (k == i || (restKindB x && !(dstNames x).contains (slotOfReg X)))
      | none => true) = true)
    (hB : ∀ x ∈ B, (restKindB x && !(dstNames x).contains (slotOfReg X)) = true) :
    restoreRegB (A ++ B) X = true := by
  have hiA : i < A.length := (List.findIdx?_eq_some_iff_getElem.mp hi).1
  unfold restoreRegB
  rw [List.findIdx?_append, hi]
  simp only [Option.some_or, Bool.and_eq_true, decide_eq_true_eq, List.length_append,
    List.all_eq_true, List.mem_range]
  refine ⟨h6, fun k hk => ?_⟩
  by_cases hkA : k < A.length
  · rw [List.getElem?_append_left hkA]
    exact List.all_eq_true.mp hA k (List.mem_range.mpr hkA)
  · rw [List.getElem?_append_right (by omega)]
    have hkB : k - A.length < B.length := by omega
    rw [List.getElem?_eq_getElem hkB]
    have := hB _ (List.getElem_mem hkB)
    simp only [Bool.and_eq_true] at this
    simp only [show ¬ k < i by omega, show (k == i) = false by simp; omega, this.1,
      decide_false, Bool.not_false, Bool.true_or, Bool.false_or, Bool.true_and]
    exact this.2

/-- **Completeness of the restoration check on the printer's frame.** A wire that is the
    save prologue `buildPrologue` of the printer, a middle part, and the restore epilogue
    `calleeSaveRestoreEpilogue` passes `restoreB` when every instruction of the middle part is
    of `restKindB` and writes no save slot `qsave.X` of a callee-saved register `X`. -/
theorem restoreB_of_shape (v : Lfundef) (tb : Array Nat) (m : InLoadMap)
    {mid : List LinstrR}
    (hmid : ∀ x ∈ mid, restKindB x = true ∧ ∀ X ∈ calleeSavedRegs, slotOfReg X ∉ dstNames x) :
    restoreB ((buildPrologue v tb m).map Linstr.li_i ++ mid
      ++ calleeSaveRestoreEpilogue.map Linstr.li_i) = true := by
  have hpro : (buildPrologue v tb m).map Linstr.li_i
      = (buildPrologue {} #[] (fun _ => none)).map Linstr.li_i := rfl
  rw [hpro]
  have hP : ((buildPrologue {} #[] (fun _ => none)).map Linstr.li_i).length = 9 := rfl
  have hE : (calleeSaveRestoreEpilogue.map Linstr.li_i).length = 6 := rfl
  have hEp : ∀ X ∈ calleeSavedRegs, ∀ x ∈ calleeSaveRestoreEpilogue.map Linstr.li_i,
      (restKindB x && !(dstNames x).contains (slotOfReg X)) = true := by decide
  have hB : ∀ X ∈ calleeSavedRegs, ∀ x ∈ mid ++ calleeSaveRestoreEpilogue.map Linstr.li_i,
      (restKindB x && !(dstNames x).contains (slotOfReg X)) = true := by
    intro X hX x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h1, h2⟩ := hmid x hx
      simpa [h1] using h2 X hX
    · exact hEp X hX x hx
  have h6 : ∀ i, i ≤ 7 → i + 6 < ((buildPrologue {} #[] (fun _ => none)).map Linstr.li_i).length
      + (mid ++ calleeSaveRestoreEpilogue.map Linstr.li_i).length := by
    intro i hi
    simp only [List.length_append, hP, hE]
    omega
  unfold restoreB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.length_append, hP, hE]
  refine ⟨⟨by omega, ?_⟩, fun X hX => ?_⟩
  · rw [show 9 + mid.length + 6 - 6
        = ((buildPrologue {} #[] (fun _ => none)).map Linstr.li_i ++ mid).length by
          simp only [List.length_append, hP]; omega, List.drop_left]
    decide
  · rw [List.append_assoc]
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
    · exact restoreRegB_append (i := 2) (by decide) (h6 2 (by omega)) (by decide)
        (hB _ (by decide))
    · exact restoreRegB_append (i := 3) (by decide) (h6 3 (by omega)) (by decide)
        (hB _ (by decide))
    · exact restoreRegB_append (i := 4) (by decide) (h6 4 (by omega)) (by decide)
        (hB _ (by decide))
    · exact restoreRegB_append (i := 5) (by decide) (h6 5 (by omega)) (by decide)
        (hB _ (by decide))
    · exact restoreRegB_append (i := 6) (by decide) (h6 6 (by omega)) (by decide)
        (hB _ (by decide))
    · exact restoreRegB_append (i := 7) (by decide) (h6 7 (by omega)) (by decide)
        (hB _ (by decide))

end RestoreCheck

/-- **The printed class of a body with the gate of the image simulation of that class**, at
    the slot map `sl`, the cell arrays `R` and the observed names `outs`: the body is in the
    class `printedAddrWB`, its cell accesses reach cells of `R` through general-purpose base
    registers (`cellAccB`), no frame-word move of a cell names an array slot (`cellNoSlotB`),
    and its cell body `ImageAddrCells.cellBody` passes, at the frame marks with the cells
    `frameMarkC`, the gate with carry chains and indexed stores through a cell
    `ImageAddrCidx.imgGateCW` together with `ImageAddrSimW.retOutsB`, which places each
    observed name outside the width analysis at the return. On a body with no cell access, at
    no cell array, the cell conditions hold and the cell body and the frame marks are those of
    the body (`regionImgB_of_cellFreeB`). A body of the narrow class `printedAddrB` that passes
    `imgGateB` at the frame marks of the body, whose indexed stores have destinations that are
    no frame-array names, passes the gate (`regionImgCoreB_of_narrowB`). -/
def regionImgCoreB (sl : String → Option (String × Nat)) (R : Slots) (outs : List String)
    (body : Lcmd) : Bool :=
  printedAddrWB body && cellAccB sl R body && cellNoSlotB sl body
    && imgGateCW (frameMarkC R body) sl (cellBody sl body)
    && retOutsB (frameMarkC R body) (cellBody sl body) outs

/-- **The gate of the image simulation with the restoration of the callee-saved
    registers**: the gate `regionImgCoreB` of the printed class of the body, the
    restoration check `restoreB` on the wire of the image `virtImg sl (cellBody sl body)`, and
    no observed name a frame-array name (`faB`). -/
def regionImgB (sl : String → Option (String × Nat)) (R : Slots) (outs : List String)
    (body : Lcmd) : Bool :=
  regionImgCoreB sl R outs body && restoreB ((virtImg sl (cellBody sl body)).map Prod.fst)
    && outs.all (fun r => !faB r)

/-- A body that passes `regionImgB` passes the gate of its printed class `regionImgCoreB`. -/
theorem regionImgCoreB_of_regionImgB {sl : String → Option (String × Nat)} {R : Slots}
    {outs : List String} {body : Lcmd} (h : regionImgB sl R outs body = true) :
    regionImgCoreB sl R outs body = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

/-- The image of a body that passes `regionImgB` passes the restoration check `restoreB`. -/
theorem restoreB_of_regionImgB {sl : String → Option (String × Nat)} {R : Slots}
    {outs : List String} {body : Lcmd} (h : regionImgB sl R outs body = true) :
    restoreB ((virtImg sl (cellBody sl body)).map Prod.fst) = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

/-- Under `regionImgB`, no observed name is a frame-array name. -/
theorem not_fa_of_regionImgB {sl : String → Option (String × Nat)} {R : Slots}
    {outs : List String} {body : Lcmd} (h : regionImgB sl R outs body = true) :
    ∀ r ∈ outs, faB r = false := by
  have h2 := (Bool.and_eq_true_iff.mp h).2
  simpa using h2

/-- **On a body with no cell access, at no cell array, `regionImgB` is the gate of the
    printed class of the body**: the class `printedAddrWB` with `imgGateCW` and `retOutsB` at
    the frame marks of the body, with the restoration check on the image of the body. -/
theorem regionImgB_of_cellFreeB (sl : String → Option (String × Nat)) (outs : List String)
    {body : Lcmd} (h : cellFreeB body = true) :
    regionImgB sl [] outs body
      = (printedAddrWB body && imgGateCW (frameMark (frameNames body)) sl body
          && retOutsB (frameMark (frameNames body)) body outs
        && restoreB ((virtImg sl body).map Prod.fst) && outs.all (fun r => !faB r)) := by
  unfold regionImgB regionImgCoreB
  rw [cellBody_of_cellFreeB sl h, cellAccB_of_cellFreeB sl [] h, cellNoSlotB_of_cellFreeB sl h]
  simp only [Bool.and_true]
  rfl

/-- A body that passes `regionImgB` is in the covered class `regionPrintedB`. -/
theorem regionPrintedB_of_regionImgB {sl : String → Option (String × Nat)} {R : Slots}
    {outs : List String} {body : Lcmd} (h : regionImgB sl R outs body = true) :
    regionPrintedB body = true := by
  have h := regionImgCoreB_of_regionImgB h
  simp only [regionImgCoreB, Bool.and_eq_true] at h
  exact h.1.1.1.1

/-- **The narrow branch of the gate is contained in the gate**: a body of `printedAddrB` with no
    cell access that passes `imgGateB` at the frame marks of the body, and whose indexed stores
    `STOREIDX d, (b, x, 8), v` have destinations `d` that are no frame-array names, passes
    `regionImgCoreB` at no cell array, at every list of observed names. The width analysis of
    such a body is empty (`ImageAddrCallW.oneBitAt_nil_of_narrowB`), every other name of the
    body is a general-purpose name or a frame slot (`ImageAddrCallW.faB_names_of_narrowB`),
    which gives `imgGateBW` (`ImageAddrCallW.imgGateBW_of_imgGateB`), hence `imgGateCW`, and
    `retOutsB` (`ImageAddrCallW.retOutsB_of_narrowB`). -/
theorem regionImgCoreB_of_narrowB (sl : String → Option (String × Nat)) (outs : List String)
    {body : Lcmd} (hcls : printedAddrB body = true) (hcf : cellFreeB body = true)
    (hgate : imgGateB (frameMark (frameNames body)) sl body = true)
    (hstx : ∀ i ∈ body, ∀ d b x v,
      i.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b x 8, .reg v] → faB d = false) :
    regionImgCoreB sl [] outs body = true := by
  unfold regionImgCoreB
  rw [cellBody_of_cellFreeB sl hcf, cellAccB_of_cellFreeB sl [] hcf,
    cellNoSlotB_of_cellFreeB sl hcf]
  have hfm : frameMarkC [] body = frameMark (frameNames body) := rfl
  rw [hfm, X86Backend.ImageAddrCallW.printedAddrWB_of_printedAddrB hcls,
    X86Backend.ImageAddrCallW.retOutsB_of_narrowB hcls hgate,
    X86Backend.ImageAddrCidx.imgGateCW_of_imgGateBW
      (X86Backend.ImageAddrCallW.imgGateBW_of_imgGateB hcls hgate hstx)]
  rfl

/-! ### The image check at a table -/

/-- **Every call of a body names a symbol of a list**: the symbol of every `call` instruction
    of `body` is in `ns`. At the empty list the body has no call
    (`callFreeB_of_callsTabB_nil`). -/
def callsTabB (ns : List String) (body : Lcmd) : Bool :=
  body.all fun i => match i.li_i with
    | .Lcall _ (f, _) => ns.contains f
    | _ => true

/-- **Soundness of `callsTabB`**: `callsTabB ns body` holds exactly when every call of `body`
    names a symbol of `ns`. -/
theorem callsTabB_iff {ns : List String} {body : Lcmd} :
    callsTabB ns body = true
      ↔ ∀ i ∈ body, ∀ ra f l, i.li_i = .Lcall ra (f, l) → f ∈ ns := by
  simp only [callsTabB, List.all_eq_true]
  refine ⟨fun h i hi ra f l hx => ?_, fun h i hi => ?_⟩
  · have := h i hi
    rw [hx] at this
    simpa using this
  · split
    · rename_i ra f l hx
      simpa using h i hi ra f l hx
    · rfl

/-- At the empty list `callsTabB` gives a body with no call. -/
theorem callFreeB_of_callsTabB_nil {body : Lcmd} (h : callsTabB [] body = true) :
    X86Backend.ImageAddrCall.callFreeB body = true := by
  simp only [X86Backend.ImageAddrCall.callFreeB, List.all_eq_true]
  intro i hi
  cases hx : i.li_i with
  | Lcall ra t => exact absurd (callsTabB_iff.mp h i hi ra t.1 t.2 hx) (by simp)
  | _ => rfl

/-- A body of `printedAddrWB` has no call. -/
theorem callsTabB_nil_of_printedAddrWB {body : Lcmd} (h : printedAddrWB body = true) :
    callsTabB [] body = true := by
  rw [callsTabB_iff]
  intro i hi ra f l hx
  simp only [printedAddrWB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, hlast⟩, hall⟩, -⟩, -⟩, -⟩ := h
  rcases List.eq_nil_or_concat body with rfl | ⟨L, b, rfl⟩
  · cases hi
  · simp only [List.concat_eq_append, List.dropLast_concat, List.getLast?_concat,
      Option.any_some, List.all_eq_true] at hlast hall
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · have := hall i hi
      rw [hx] at this
      simp [X86Backend.DecodePrintedAddrW.instrOKWB] at this
    · rw [hx] at hlast
      simp [X86Backend.DecodePrinted.isRetB] at hlast

/-- The frame conditions of the relocating encoder hold on a decodable body. -/
theorem relocFrameB_of_decodableLcmd {body : Lcmd}
    (h : X86Backend.DecodeLayout.decodableLcmd body = true) :
    X86Backend.ImageAddrCall.relocFrameB body = true := by
  simp only [X86Backend.DecodeLayout.decodableLcmd, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, hs⟩, hF0⟩, hF⟩, -⟩, -⟩ := h
  simp only [X86Backend.ImageAddrCall.relocFrameB, hs, Bool.true_and, Bool.and_eq_true]
  simp only [X86Backend.LprogBytesDecode.Params.ofBody, X86Backend.SailX86Decoder.dispOk32,
    decide_eq_true_eq, bne_iff_ne, ne_eq, Int.ofNat_eq_natCast] at hF0 hF ⊢
  have := of_decide_eq_true hF
  omega

/-- A call-free body has no call of a named symbol. -/
theorem remoteCallB_of_callFreeB {body : Lcmd}
    (h : X86Backend.ImageAddrCall.callFreeB body = true) {i : Linstr} (hi : i ∈ body) :
    X86Backend.ImageAddrCall.remoteCallB i.li_i = false := by
  simp only [X86Backend.ImageAddrCall.callFreeB, List.all_eq_true] at h
  have := h i hi
  cases hx : i.li_i <;> simp_all [X86Backend.ImageAddrCall.remoteCallB,
    X86Backend.ImageAddrCall.isCallB]

/-- **The class `printedAddrWB` is the calling class at no call**: a body is in
    `printedAddrWB` exactly when it has no call, is decodable and is in
    `ImageAddrCallW.printedAddrCWB` at any frame `G`. -/
theorem printedAddrWB_eq (G : Nat) (body : Lcmd) :
    printedAddrWB body = (callsTabB [] body && X86Backend.DecodeLayout.decodableLcmd body
      && X86Backend.ImageAddrCallW.printedAddrCWB G body) := by
  cases hc : callsTabB [] body
  · cases hp : printedAddrWB body
    · rfl
    · rw [callsTabB_nil_of_printedAddrWB hp] at hc
      cases hc
  · have hcf := callFreeB_of_callsTabB_nil hc
    have hnr := fun i (hi : i ∈ body) => remoteCallB_of_callFreeB hcf hi
    apply Bool.eq_iff_iff.mpr
    simp only [printedAddrWB, X86Backend.ImageAddrCallW.printedAddrCWB, Bool.and_eq_true,
      Bool.true_and, List.all_eq_true, hcf, Bool.true_or, Bool.and_true]
    constructor
    · rintro ⟨⟨⟨⟨⟨hd, hl⟩, ho⟩, h1⟩, h2⟩, h3⟩
      refine ⟨hd, ⟨⟨relocFrameB_of_decodableLcmd hd, hl⟩, fun i hi => ?_⟩, fun k hk => ?_⟩
      · simp [ho i hi]
      · simp [h1 k hk, h2 k hk, h3 k hk]
    · rintro ⟨hd, ⟨⟨-, hl⟩, ho⟩, h⟩
      refine ⟨⟨⟨⟨⟨hd, hl⟩, fun i hi => ?_⟩, fun k hk => (h k hk).1.1⟩,
        fun k hk => (h k hk).1.2⟩, fun k hk => (h k hk).2⟩
      have := ho i hi
      rwa [hnr i (List.mem_of_mem_dropLast hi), Bool.false_or] at this

/-- The cell body of a call-free body is call-free. -/
theorem callFreeB_cellBody (sl : String → Option (String × Nat)) {body : Lcmd}
    (h : X86Backend.ImageAddrCall.callFreeB body = true) :
    X86Backend.ImageAddrCall.callFreeB (cellBody sl body) = true := by
  simp only [X86Backend.ImageAddrCall.callFreeB, List.all_eq_true] at h ⊢
  intro i hi
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
  rw [cellBody_getElem?] at hk
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hk
  have := h j (List.mem_of_getElem? hj)
  unfold X86Backend.ImageAddrCells.cellMove
  split
  · split
    · rfl
    · exact this
  · split
    · rfl
    · exact this
  · exact this

/-- On a call-free body the gate of a calling body is `imgGateCW`. -/
theorem imgGateCBW_of_callFreeB (frame : String → Option (BitVec 64))
    (sl : String → Option (String × Nat)) {body : Lcmd}
    (h : X86Backend.ImageAddrCall.callFreeB body = true) :
    X86Backend.ImageAddrCallW.imgGateCBW frame sl body = imgGateCW frame sl body := by
  have hk : ∀ k, (body[k]?).all (fun i => X86Backend.ImageAddrCall.remoteCallB i.li_i
      || X86Backend.ImageAddrCidx.gateCW frame sl body k i.li_i)
      = (body[k]?).all (fun i => X86Backend.ImageAddrCidx.gateCW frame sl body k i.li_i) := by
    intro k
    cases hk : body[k]? with
    | none => rfl
    | some i => simp [remoteCallB_of_callFreeB h (List.mem_of_getElem? hk)]
  unfold X86Backend.ImageAddrCallW.imgGateCBW imgGateCW
  simp only [hk]

/-- **The image check of a body at a table**, at the frame `G` and the symbols `ns` of the
    table and the wire `w` of the image of the cell body: every call of the body names a
    symbol of `ns` (`callsTabB`), the body is decodable and in the calling class
    `ImageAddrCallW.printedAddrCWB` at `G`, its cell accesses pass `cellAccB` and
    `cellNoSlotB`, its cell body passes the gate of a calling body `ImageAddrCallW.imgGateCBW`
    and `retOutsB` at the frame marks with the cells, the wire passes the restoration check,
    and no observed name is a frame-array name. At no symbol and the wire of the image
    `virtImg` it is `regionImgB` (`regionImgCB_nil`). -/
def regionImgCB (G : Nat) (ns : List String) (w : List LinstrR)
    (sl : String → Option (String × Nat)) (R : Slots) (outs : List String) (body : Lcmd) :
    Bool :=
  callsTabB ns body && X86Backend.DecodeLayout.decodableLcmd body
    && X86Backend.ImageAddrCallW.printedAddrCWB G body
    && cellAccB sl R body && cellNoSlotB sl body
    && X86Backend.ImageAddrCallW.imgGateCBW (frameMarkC R body) sl (cellBody sl body)
    && retOutsB (frameMarkC R body) (cellBody sl body) outs
    && restoreB w && outs.all (fun r => !faB r)

/-- **At no symbol the image check is `regionImgB`**, at every frame, on the wire of the image
    `virtImg` of the cell body. -/
theorem regionImgCB_nil (G : Nat) (sl : String → Option (String × Nat)) (R : Slots)
    (outs : List String) (body : Lcmd) :
    regionImgCB G [] ((virtImg sl (cellBody sl body)).map Prod.fst) sl R outs body
      = regionImgB sl R outs body := by
  unfold regionImgCB regionImgB regionImgCoreB
  rw [printedAddrWB_eq G body]
  cases hc : callsTabB [] body
  · simp
  · rw [imgGateCBW_of_callFreeB _ _ (callFreeB_cellBody sl (callFreeB_of_callsTabB_nil hc))]

/-- **A halting run of a decoded program has one final state.** -/
theorem halts_det {prog : List X86Backend.LprogBytesDecode.RInstr} {pc : Nat}
    {sa s₁ s₂ : AState} (h₁ : Halts aMachine prog pc sa s₁) (h₂ : Halts aMachine prog pc sa s₂) :
    s₁ = s₂ := by
  obtain ⟨t₁, r₁⟩ := X86Backend.DecodedCT.halts_runL CT.DoitRegime.doitm h₁
  obtain ⟨t₂, r₂⟩ := X86Backend.DecodedCT.halts_runL CT.DoitRegime.doitm h₂
  exact (X86Backend.DecodePrintedAddrLeak.runL_det r₁ r₂).2

/-- The bytes of a word whose address is in `S` are memory locations of `wordsLocs S`. -/
theorem mem_wordsLocs {S : Set (BitVec 64)} {a x : BitVec 64} (ha : a ∈ S)
    (hx : x ∈ (⟨a, 8⟩ : SepLogic.Rng 64)) : SepLogic.X86.Loc.mem x ∈ wordsLocs S :=
  Set.mem_iUnion₂.mpr ⟨a, ha, x, hx, rfl⟩

/-- The red-zone word of the frame address of a printed body is at the offset
    `cmovRedZone - frame` from the entry stack register. -/
theorem redW_frameRsp (body : Lcmd) (sa : AState) :
    X86Backend.DecodePrintedAddr.redW (X86Backend.DecodePrintedCFG.frameRsp body sa)
      = sa.regs "%rsp" + BitVec.ofInt 64 (X86Backend.LprogBytes.cmovRedZone
        - (X86Backend.LprogBytesDecode.Params.ofBody body).frame) := by
  simp only [X86Backend.DecodePrintedAddr.redW, X86Backend.DecodePrintedCFG.frameRsp,
    BitVec.add_assoc, ← BitVec.ofInt_add]
  congr 2
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Under the frame check the red-zone word of a printed body is a stack word of the
    layout. -/
theorem redW_mem_frameWords {σ : AbiLayout} {body : Lcmd} (hfr : frameOkB σ body = true)
    (sa : AState) :
    X86Backend.DecodePrintedAddr.redW (X86Backend.DecodePrintedCFG.frameRsp body sa)
      ∈ frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi := by
  rw [redW_frameRsp]
  exact ⟨_, (X86Backend.ImageAddrFrame.frameOkB_red hfr).1,
    (X86Backend.ImageAddrFrame.frameOkB_red hfr).2, rfl⟩

/-- A cell of an accepted region at the entry bases is a word of a pointer region of the
    layout. -/
theorem cellAt_mem_regions {σ : AbiLayout} (hrs : X86Backend.DecodeGenNode.rsOK σ (rsOf σ) = true)
    {A : String} {j : Nat} (hk : X86Backend.DecodeGenMem.regK (rsOf σ) A j) (sa : AState) :
    ∃ p ∈ σ.regions, cellAt (abiBase (abiReg σ) sa A) j ∈ regionWords (sa.regs p.1) p.2 := by
  obtain ⟨g, -, hg, rfl, hj⟩ := X86Backend.DecodeGenNode.regK_region hk
  obtain ⟨a, -, hreg, -, hb⟩ := X86Backend.DecodeGenNode.rsOK_region hrs hg sa
  exact ⟨(a.reg, g.len), hreg, j, hj, by rw [hb]⟩

/-- The bytes of the stack words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and of the words of
    each pointer region of `σ`, at the registers of `sa`. -/
def layoutMem (σ : AbiLayout) (sa : AState) : Set (BitVec 64) :=
  {x | SepLogic.X86.Loc.mem x ∈ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi)
    ∨ ∃ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∈ wordsLocs (regionWords (sa.regs p.1) p.2)}

/-- **The accesses of the image simulation lie in the stack words and the pointer regions.**
    Under the frame check, the entry facts and the cell-region facts of the image check
    `renImageB`, the set `imgStores` of the stores and loads of the image simulation at the
    frame map with the cells, the renamed slot map with the cells and the entry bases of `sa`
    is contained in `layoutMem σ sa`. -/
theorem imgStores_export {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {body : Lcmd} {sa : AState} (hfr : frameOkB σ body = true)
    (E : EntryFacts σ nm (frameE body sa))
    (hlen : ∀ p ∈ R, X86Backend.DecodeGenMem.regLen (rsOf σ) (unren ps p.1) = p.2
      ∧ renOf ps (unren ps p.1) = p.1)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) :
    imgStores (frameC (baseR σ sa ps) R (frameE body sa))
      (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) (baseR σ sa ps) ⊆ layoutMem σ sa := by
  intro x hx
  show SepLogic.X86.Loc.mem x ∈ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi)
    ∨ ∃ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∈ wordsLocs (regionWords (sa.regs p.1) p.2)
  obtain ⟨a, ha, hxa⟩ := hx
  have hcell : ∀ A j, X86Backend.DecodeGenMem.regK (rsOf σ) A j →
      a = cellAt (abiBase (abiReg σ) sa A) j →
      ∃ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∈ wordsLocs (regionWords (sa.regs p.1) p.2) := by
    intro A j hk he
    obtain ⟨p, hp, hw⟩ := cellAt_mem_regions E.rs hk sa
    exact ⟨p, hp, mem_wordsLocs (he ▸ hw) hxa⟩
  rcases ha with ⟨q, hq⟩ | ⟨q, A, n, j, hq, hj, rfl⟩
  · simp only [frameC] at hq
    cases hc : cellIdx R q with
    | some Aj =>
        obtain ⟨A, j⟩ := Aj
        rw [hc] at hq
        obtain ⟨n, hn, hj, -⟩ := X86Backend.ImageStraightCells.cellIdx_spec hc
        refine Or.inr (hcell (unren ps A) j ?_ (Option.some.inj hq).symm)
        unfold X86Backend.DecodeGenMem.regK
        rw [(hlen _ hn).1]
        exact hj
    | none =>
        rw [hc] at hq
        obtain ⟨hq', o, ho, rfl⟩ := X86Backend.ImageAddrFrame.frameIn_some hq
        have h := X86Backend.ImageAddrFrame.frameOkB_range hfr hq' ho
        exact Or.inl (mem_wordsLocs ⟨_, h.1, h.2, rfl⟩ hxa)
  · obtain ⟨m', hsr, hcase⟩ := X86Backend.ImageStraightCells.slotArrC_some hq
    have hnm : n = m' := by
      rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · omega
      · rfl
    subst hnm
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hsr
    have hun : unren ps (renOf ps A0) = A0 := by
      obtain ⟨j', a', hj', -, rfl, -⟩ := slotArrOf_some hq0
      exact hU j' (List.getElem?_eq_some_iff.mp hj').1
    refine Or.inr (hcell A0 j ?_ ?_)
    · unfold X86Backend.DecodeGenMem.regK
      rw [E.len q A0 n hq0]
      exact hj
    · show cellAt (abiBase (abiReg σ) sa (unren ps (renOf ps A0))) j = _
      rw [hun]

/-- **The image of a printed body of the covered classes on its decoded bytes.** Let the
    cell body of the printed body `body` pass `physImgB` at the slot map `sl`, let `body`
    pass `regionImgB` at `sl`, the cell arrays `R` and the observed names `outs`, and let
    the frame map `frameC base R (frameE body sa)` of `body` with the cells of `R`, at the
    machine state `sa`, be separated, where no cell name is a general-purpose name or a
    name of `body` and every cell is disjoint from the red-zone word. A halting checked
    run of the image of the cell body from a state related by `ImageAddrSim.ImgRel` to the
    entry state `entryA σ sa` is matched by a halting run of the decoded bytes of `body`
    from `sa` and an address state `s'`: the final state of the image agrees with `s'` on
    every observed name without a frame word, every array of the slot map is the words of `s'` at
    its base, every observed name with a frame word holds the word of `s'` at it, every
    observed general-purpose name holds in `s'` the 64-bit value of its machine register,
    and the memory of `s'` is that of the machine outside the red zone. The final machine
    state `sa'` has the stack register of `sa` and every callee-saved register of
    `calleeSavedRegs` at its value in `sa`, and its memory agrees with that of `sa` at
    every byte outside the red-zone word and outside the frame words and array words
    `imgStores` of the image simulation; the run of the address machine on `body` from
    `entryA σ sa` at the frame map with the cells halts and stores to and loads from
    `imgStores` only.

    The callee-saved registers hold their entry values at the halt of the image by
    `restoreB_sound`, and the relation of the image with the address machine and of the
    address machine with the machine carries them to `sa'`.

    The body runs by `DecodePrintedAddrW.printedAddr_simW`, with
    `ImageAddrStore.image_addr_simCW'_access` under `imgGateCW`, from the invariant of the
    window at the entry (`ImageAddrCidx.CidxInv.of_lpc_zero`), where the step at a
    conditional branch is `ImageAddrCellsLoop.imgStepWCond_of_gateCW` and the width `64` of
    an observed name at the halt is `ImageAddrCidx.not_mem_oneBitAt_of_haltedCW`. A byte outside
    the accesses keeps its value through the run of the address machine
    (`SepLogic.Addr.runA_keep_mem`). -/
theorem regionImg_sim {σ : AbiLayout} {sl : String → Option (String × Nat)}
    {base : String → BitVec 64} {R : Slots} {outs : List String} {body : Lcmd} {sa : AState}
    (hphys : physImgB sl (cellBody sl body) = true) (hgate : regionImgB sl R outs body = true)
    (hsep : X86Backend.ImageAddrSim.ImgSep (frameC base R (frameE body sa)) sl base
      (X86Backend.DecodePrintedCFG.frameRsp body sa))
    (hgpC : ∀ q, (cellIdx R q).isSome = true → gpOk q = false)
    (hbody : ∀ q ∈ X86Backend.ImageAddrFrame.bodyNamesI body, cellIdx R q = none)
    (hred : ∀ A j, cellIdx R (memName A (8 * j)) = some (A, j) →
      Ascent.AddrMem.Disjoint8 (X86Backend.DecodePrintedAddr.redW
        (X86Backend.DecodePrintedCFG.frameRsp body sa)) (cellAt (base A) j))
    (fn : String) (f' : Nat) (b t' : LstateMF) (hfn : b.prog.lfn = fn)
    (hrel : X86Backend.ImageAddrSim.ImgRel (frameC base R (frameE body sa)) sl base
      (cellBody sl body) b (entryA σ sa) false)
    (hr' : JasminLsemMemChecked.lsemFuelMemFk true
      (singletonProgM fn (virtImg sl (cellBody sl body))) f' b = some t') :
    ∃ prog sa', ∃ s' : JasminLsemAddrMem.LstateA,
      decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ (∀ x, x ∈ outs → frameC base R (frameE body sa) x = none →
        t'.prog.base.reg.lvm x = s'.reg.lvm x)
      ∧ (∀ q A n, sl q = some (A, n) → ∃ arr, t'.prog.base.getArr A 64 n = some arr ∧
        ∀ j (hj : j < n), read64 s'.mem (cellAt (base A) j) = arr ⟨j, hj⟩)
      ∧ (∀ q a, q ∈ outs → frameC base R (frameE body sa) q = some a →
        t'.prog.base.reg.lvm q = ⟨64, read64 s'.mem a⟩)
      ∧ (∀ r, r ∈ outs → gpOk r = true → s'.reg.getW r 64 = some (sa'.regs (phys r)))
      ∧ (∀ x, ¬ Ascent.AddrMem.InRange8 (X86Backend.DecodePrintedAddr.redW
          (X86Backend.DecodePrintedCFG.frameRsp body sa)) x → s'.mem x = sa'.mem x)
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x ∈ X86Backend.LprogAsmPrinter.calleeSavedRegs, sa'.regs (phys x) = sa.regs (phys x))
      ∧ (∀ x, ¬ Ascent.AddrMem.InRange8 (X86Backend.DecodePrintedAddr.redW
          (X86Backend.DecodePrintedCFG.frameRsp body sa)) x →
        x ∉ imgStores (frameC base R (frameE body sa)) sl base → sa'.mem x = sa.mem x)
      ∧ ∃ fuel s zf, runA (frameC base R (frameE body sa)) body fuel (entryA σ sa) false
          = some (s, zf)
        ∧ RunSafe (frameC base R (frameE body sa)) body
          (AccessIn (imgStores (frameC base R (frameE body sa)) sl base)
            (frameC base R (frameE body sa)) body) fuel (entryA σ sa) false := by
  have hentA : ∀ r, gpOk r = true →
      (entryA σ sa).reg.getW r 64 = some (sa.regs (phys r)) := fun r hr => by
    have hl : (entryA σ sa).reg.lvm r = ⟨64, sa.regs (phys r)⟩ := by
      simp only [entryA, hr, ite_true]
    unfold LstateN.getW
    rw [hl]
    simp
  have hcsT : ∀ x ∈ X86Backend.LprogAsmPrinter.calleeSavedRegs, gpOk x = true
      ∧ t'.prog.base.reg.lvm x = ⟨64, sa.regs (phys x)⟩ := by
    intro x hx
    have hgp : gpOk x = true := by
      simp only [X86Backend.LprogAsmPrinter.calleeSavedRegs, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    refine ⟨hgp, ?_⟩
    rw [restoreB_sound (restoreB_of_regionImgB hgate) hfn hrel.pc.symm hr' x hx,
      hrel.regs x (hsep.gp x hgp)]
    simp only [entryA, hgp, ite_true]
  have hfinA : ∀ (s' : JasminLsemAddrMem.LstateA) (sa' : AState) (x : String),
      s'.reg.lvm x = ⟨64, sa.regs (phys x)⟩ →
      (s'.reg.getW x 64 = some (sa'.regs (phys x))
        ∨ (∃ b : BitVec 1, s'.reg.lvm x = ⟨1, b⟩ ∧ sa'.regs (phys x) = b.setWidth 64)
        ∨ X86Backend.DecodePrintedAddrW.NarrowCell (s'.reg.lvm x) (sa'.regs (phys x))) →
      sa'.regs (phys x) = sa.regs (phys x) := by
    intro s' sa' x hl h
    rcases h with h | ⟨b1, hb, -⟩ | hn
    · unfold LstateN.getW at h
      rw [hl] at h
      simp only [dite_true, Option.some.injEq] at h
      exact h.symm
    · rw [hl] at hb
      simp at hb
    · rcases hn.width with h | h <;> simp [hl] at h
  have hofa := not_fa_of_regionImgB hgate
  replace hgate := regionImgCoreB_of_regionImgB hgate
  unfold regionImgCoreB at hgate
  simp only [Bool.and_eq_true] at hgate
  obtain ⟨⟨⟨⟨hprW, hacc⟩, hns⟩, hg0⟩, hro0⟩ := hgate
  have hsome : ∀ q, (frameC base R (frameE body sa) q).isSome = (frameMarkC R body q).isSome :=
    X86Backend.ImageStraightCells.frameC_isSome base R body sa
  have hgpN : ∀ r, gpOk r = true → cellIdx R r = none := by
    intro r hr
    cases hc : cellIdx R r with
    | none => rfl
    | some _ =>
        have := hgpC r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hfr : ∀ q ∈ X86Backend.ImageAddrFrame.bodyNamesI body,
      frameC base R (frameE body sa) q
        = X86Backend.DecodePrintedAddr.frameP (X86Backend.LprogBytesDecode.Params.ofBody body)
          (X86Backend.DecodePrintedCFG.frameRsp body sa) q := by
    intro q hq
    simp only [frameC, hbody q hq]
    show X86Backend.ImageAddrFrame.frameIn body _ q = _
    unfold X86Backend.ImageAddrFrame.frameIn
    rw [ite_eq_left hq]
  have hN := X86Backend.ImageStraightCells.cellNoSlotB_spec hns
  have hF := X86Backend.ImageStraightCells.cellFrames_of (base := base)
    (rsp := X86Backend.DecodePrintedCFG.frameRsp body sa) (fr := frameE body sa) hacc hgpC
    (fun r hr => by
      have := hsep.gp r hr
      simp only [frameC, hgpN r hr] at this
      exact this) hred
  have hg : X86Backend.ImageAddrCidx.imgGateCW (frameC base R (frameE body sa)) sl
      (cellBody sl body) = true := by
    rw [X86Backend.ImageAddrCidx.imgGateCW_congr hsome]
    exact hg0
  have hro : retOutsB (frameC base R (frameE body sa)) (cellBody sl body) outs = true := by
    rw [X86Backend.ImageAddrSimW.retOutsB_congr hsome]
    exact hro0
  obtain ⟨fuel', s', zf', hrA, hrel', -, hsafe, hacc⟩ :=
    X86Backend.ImageAddrStore.image_addr_simCW'_access (body := body) hsep hphys hg hN hF fn
      (X86Backend.ImageAddrCellsLoop.imgStepWCond_of_gateCW _ hphys hg fn) f' b t'
      (entryA σ sa) false hfn (X86Backend.ImageAddrSimW.imgRelW_of hrel)
      (X86Backend.ImageAddrCidx.CidxInv.of_lpc_zero (by rw [← hrel.pc]; rfl)) hr'
  have hkeep : ∀ x, x ∉ imgStores (frameC base R (frameE body sa)) sl base →
      s'.mem x = sa.mem x :=
    fun x hx => SepLogic.Addr.runA_keep_mem hrA (hacc.mono fun _ h => h.1) hx
  have hA := (⟨fuel', s', zf', hrA, hacc⟩ : ∃ fuel s zf,
    runA (frameC base R (frameE body sa)) body fuel (entryA σ sa) false = some (s, zf)
    ∧ RunSafe (frameC base R (frameE body sa)) body
      (AccessIn (imgStores (frameC base R (frameE body sa)) sl base)
        (frameC base R (frameE body sa)) body) fuel (entryA σ sa) false)
  have hhalt : JasminLsemAddrRun.haltedA (cellBody sl body) s' = true := by
    rw [X86Backend.ImageAddrCells.haltedA_cellBody]
    exact JasminLsemAddrRun.haltedA_of_runA _ body fuel' (entryA σ sa) false (s', zf') hrA
  rw [X86Backend.ImageAddrFrame.runA_congr hfr] at hrA
  rw [X86Backend.ImageAddrFrame.runSafe_congr hfr] at hsafe
  obtain ⟨prog, sa', hdec, hh, hsp, hregs, hm'⟩ :=
    X86Backend.DecodePrintedAddrW.printedAddr_simW body hprW sa (entryA σ sa) false rfl
      (fun r hr => Or.inl (hentA r hr)) rfl fuel' (s', zf') hrA hsafe
  refine ⟨prog, sa', s', hdec, hh, fun x hxo hx => (hrel'.regs x hx).eq
      (X86Backend.ImageAddrCidx.not_mem_oneBitAt_of_haltedCW hg hhalt
        (X86Backend.ImageAddrSimW.not_mem_of_retOutsB hro hxo)),
    hrel'.cells, fun q a hq ha => ?_, fun r hRo hr => ?_, hm', hsp,
    fun x hx => ?_,
    fun x hx hs => (hm' x hx).symm.trans (hkeep x hs), hA⟩
  rotate_left 2
  · obtain ⟨hgp, ht⟩ := hcsT x hx
    have hv := hrel'.regs x (hsep.gp x hgp)
    rw [ht] at hv
    refine hfinA s' sa' x ?_ (hregs x hgp)
    rcases hv with h | ⟨-, -, b1, hb, -⟩
    · exact h.symm
    · simp at hb
  · rw [← X86Backend.ImageAddrSim.frameVal_of_not_fa (hofa q hq)]
    exact (hrel'.slots q a ha).word
      (X86Backend.ImageAddrCidx.not_mem_oneBitAt_of_haltedCW hg hhalt
        (X86Backend.ImageAddrSimW.not_mem_of_retOutsB hro hq))
  · have hw := hrel'.wid r hr (X86Backend.ImageAddrCidx.not_mem_oneBitAt_of_haltedCW hg hhalt
      (X86Backend.ImageAddrSimW.not_mem_of_retOutsB hro hRo))
    rcases hregs r hr with h | ⟨b1, hb, -⟩ | hn
    · exact h
    · rw [hb] at hw
      cases hw
    · rcases hn.width with h | h <;> rw [hw] at h <;> cases h

/-- **Restoration of the callee-saved registers on the decoded bytes.** Under the hypotheses
    of `regionImg_sim`, the bytes of `body` decode to a program that halts from `sa`, and
    every halting run of it from `sa` ends with the stack register and every register of
    `DecodedCT.calleeSaved` at its value in `sa`. -/
theorem regionImg_restore {σ : AbiLayout} {sl : String → Option (String × Nat)}
    {base : String → BitVec 64} {R : Slots} {outs : List String} {body : Lcmd} {sa : AState}
    (hphys : physImgB sl (cellBody sl body) = true) (hgate : regionImgB sl R outs body = true)
    (hsep : X86Backend.ImageAddrSim.ImgSep (frameC base R (frameE body sa)) sl base
      (X86Backend.DecodePrintedCFG.frameRsp body sa))
    (hgpC : ∀ q, (cellIdx R q).isSome = true → gpOk q = false)
    (hbody : ∀ q ∈ X86Backend.ImageAddrFrame.bodyNamesI body, cellIdx R q = none)
    (hred : ∀ A j, cellIdx R (memName A (8 * j)) = some (A, j) →
      Ascent.AddrMem.Disjoint8 (X86Backend.DecodePrintedAddr.redW
        (X86Backend.DecodePrintedCFG.frameRsp body sa)) (cellAt (base A) j))
    (fn : String) (f' : Nat) (b t' : LstateMF) (hfn : b.prog.lfn = fn)
    (hrel : X86Backend.ImageAddrSim.ImgRel (frameC base R (frameE body sa)) sl base
      (cellBody sl body) b (entryA σ sa) false)
    (hr' : JasminLsemMemChecked.lsemFuelMemFk true
      (singletonProgM fn (virtImg sl (cellBody sl body))) f' b = some t') :
    ∃ prog, decodeLprog (encodeLfundefBytes body) = some prog
      ∧ (∃ sa', Halts aMachine prog 0 sa sa')
      ∧ ∀ sa', Halts aMachine prog 0 sa sa' →
        sa'.regs "%rsp" = sa.regs "%rsp"
          ∧ ∀ x ∈ X86Backend.DecodedCT.calleeSaved, sa'.regs x = sa.regs x := by
  obtain ⟨prog, sa', -, hdec, hh, -, -, -, -, -, hsp, hcs, -⟩ :=
    regionImg_sim (σ := σ) hphys hgate hsep hgpC hbody hred fn f' b t' hfn hrel hr'
  refine ⟨prog, hdec, ⟨sa', hh⟩, fun sa'' hh'' => ?_⟩
  obtain rfl := halts_det hh'' hh
  have hmap : X86Backend.DecodedCT.calleeSaved
      = X86Backend.LprogAsmPrinter.calleeSavedRegs.map phys := by decide
  refine ⟨hsp, fun x hx => ?_⟩
  rw [hmap, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hcs y hy

/-! ## 2. The virtual body of a region export -/

/-- **The run of the virtual body of a region export.** Let `p` be a program of
    `RegionExportable` with the export `r`, and let the frame map `fr` satisfy the facts of
    the entry check. At a valuation `V` the layout `σ` reads off the machine state `sa`, if
    `p` denotes `v` at `V` then the copies of the parameter registers, the code of `r` and
    the register copy `ret` (when there is one), run by `lsemFuelMemF` from the entry state
    `entryV` at a map `un` of array names that fixes the argument names, halt in a state
    `t`. The state `t0` before the copy agrees with the returned
    operands at `v`; without a copy `t` is `t0`, and after the copy of `x` into `y` the cell
    of `y` in `t` is the cell of `x` in `t0`. The fuel of the run is at most the number of
    copies of parameter registers plus `tripFactor fuel p` times the length of the code of
    `r` plus one. -/
theorem regionVirt_run (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ret : Option (String × String))
    {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (hden : p.denote fuel V = some v) :
    ∃ (k : Nat) (t t0 : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) k
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some t
      ∧ ResAgrees Γ.length r.depth t0.prog.base r.res v
      ∧ (ret = none → t = t0)
      ∧ (∀ x y, ret = some (x, y) → t.prog.base.reg.lvm y = t0.prog.base.reg.lvm x)
      ∧ k ≤ (argBind σ nm).length + tripFactor fuel p * r.code.length + 1 := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) :=
    entryV_abiEntry E.argF E.argG hU
  have hag0 := storeAgreesM_of_abi hV habi
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := un) E.argF E.argG hS false
  have hag1 : StoreAgreesM Γ.length Γ.length
      ({ entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } } : LstateM) V :=
    StoreAgreesM.of_regionFrame (n := 0) rfl hag0
      ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  have hlen : (argBind σ nm).length = σ.args.length := by
    simp [argBind, movesOf_length, argPairs]
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨k, t0, hs, hat, hres, -, hle⟩ := exportR_sim Γ.length fn hp Γ.length 0 r hr rfl le_rfl
    (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) (argBind σ nm)
    (movesOf ret.toList) rfl rfl
    (fun l _ => (findLabelMem_eq_none_iff l _).mpr (by rw [labelsOf_of_isLopn hlop]; simp))
    fuel V v
    { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
        lpc := σ.args.length } }, lfn := fn }, zf := false }
    hden ⟨rfl, hlen.symm⟩ hag1
  obtain ⟨n, t, hst, hhalt, h1, h2, hn⟩ : ∃ (n : Nat) (t : LstateMF),
      Steps x86Isa (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) n
        { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } }, lfn := fn }, zf := false } t
      ∧ Halted (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) t
      ∧ (ret = none → t = t0)
      ∧ (∀ x y, ret = some (x, y) → t.prog.base.reg.lvm y = t0.prog.base.reg.lvm x)
      ∧ n ≤ k + 1 := by
    cases ret with
    | none =>
        exact ⟨k, t0, hs, halted_of_atPc hat (by simp [singletonProgM, movesOf]),
          fun _ => rfl, fun _ _ h => (by cases h), Nat.le_succ k⟩
    | some q =>
        obtain ⟨x, y⟩ := q
        obtain ⟨t1, hs1, hat1, -, hl⟩ := steps_movReg (dst := y) (src := x) hat (by
          show (argBind σ nm ++ r.code ++ movesOf [(x, y)])[_]? = _
          rw [← List.length_append, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl)
        refine ⟨k + 1, t1, hs.trans hs1,
          halted_of_atPc hat1 (by simp [singletonProgM, movesOf, Nat.add_assoc]), nofun,
          fun x' y' h => ?_, Nat.le_refl _⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rw [hl, ite_eq_left rfl]
  have hfin := lsemFuelMemF_of_steps x86Isa _ hst hhalt 0
  rw [X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hfin
  refine ⟨(argBind σ nm).length + (n + 0), t, t0, ?_, hres, h1, h2, by omega⟩
  rw [lsemFuelMemF_segF _ fn rfl (argBind σ nm) (entryV σ fr sa un) false (n + 0) hlop
    (fun j hj => by
      show (argBind σ nm ++ r.code ++ movesOf ret.toList)[0 + j]? = _
      rw [Nat.zero_add, List.append_assoc, List.getElem?_append_left hj]), hpre,
    Option.bind_some]
  exact hfin

/-! ## 2a. The result copy of an array result -/

/-- The `j`-th version of the result buffer `D` in the result copy: `D` at `0`, and the name
    `D ++ "#c" ++ toString j` after `j` words. -/
def copyName (D : String) (j : Nat) : String :=
  if j = 0 then D else D ++ "#c" ++ toString j

/-- The index register of the result copy. -/
def copyIdx : String := "rcopy.i"

/-- The scratch register of the result copy. -/
def copyTmp : String := "rcopy.t"

/-- **One word of the result copy** of the `m`-word array `src` into the result buffer `D`,
    at the index `j`: the move of `j` into the index register `copyIdx`, the load of the
    word of `src` at that index into the scratch register `copyTmp`, and the store of that
    word at the same index of the version `copyName D j`, which writes the version
    `copyName D (j + 1)`. -/
def resCopyStep (src D : String) (m j : Nat) : List LinstrRM :=
  [ movImmI copyIdx j
  , (.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m)
  , (.Lopn [.reg (copyName D (j + 1))] "STOREIDX"
      [.arrIdx (copyName D j) copyIdx 8, .reg copyTmp], .store 64 m) ]

/-- **The result copy** of the `m`-word array `src` into the result buffer `D`: the words at
    the indices `0, …, m - 1` in order (`resCopyStep`). After it the version
    `copyName D m` holds the array of `src`. -/
def resCopyCode (src D : String) (m : Nat) : List LinstrRM :=
  (List.range m).flatMap (resCopyStep src D m)

/-- At an index below the length `m < 2 ^ 64`, `stackGet` at the index read back from its
    `64`-bit word is the entry of the array. -/
theorem stackGet_ofNat_lt {m : Nat} (a : Fin m → BitVec 64) {j : Nat} (hj : j < m)
    (hm : m < 2 ^ 64) : stackGet a (BitVec.ofNat 64 j).toNat = a ⟨j, hj⟩ := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  match m, a, hj with
  | k + 1, a, hj => show a ⟨j % (k + 1), _⟩ = _; simp [Nat.mod_eq_of_lt hj]

/-- At an index below the length `m < 2 ^ 64`, `stackSet` at the index read back from its
    `64`-bit word writes the entry at that index and keeps every other entry. -/
theorem stackSet_ofNat_apply {m : Nat} (a : Fin m → BitVec 64) {j : Nat} (hj : j < m)
    (hm : m < 2 ^ 64) (v : BitVec 64) (i : Fin m) :
    stackSet a (BitVec.ofNat 64 j).toNat v i = if i.val = j then v else a i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  match m, a, hj, i with
  | k + 1, a, hj, i =>
      show (if i = ⟨j % (k + 1), _⟩ then v else a i) = _
      simp [Nat.mod_eq_of_lt hj, Fin.ext_iff]

/-- The events of the first `k` words of the result copy of `src` into `D`: at each index
    `j < k`, the address event of the load of `src` and of the store into `copyName D j`,
    both at the offset `8 * j`. -/
def resCopyLeak (src D : String) (k : Nat) : List CT.CTLeak :=
  (List.range k).flatMap fun j =>
    [.addr src (Int.ofNat (8 * j)), .addr (copyName D j) (Int.ofNat (8 * j))]

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (instrLeakF_of_lopn instrLeakB
  opLeakF idxVal) in
/-- **The first `k` words of the result copy.** Let the body of `P` hold the first `k ≤ m`
    words of the result copy of `src` into `D` behind `pre`, the state `s` be at the end of
    `pre`, `src` hold the array `arr` and `D` an array, both of `m < 2 ^ 64` words, and no
    version `copyName D (j + 1)`, `j < m`, be `src`. Then `3 * k` steps with the events
    `resCopyLeak src D k` lead to a state at the end of those words in which `src` still
    holds `arr` and the version `copyName D k` holds an array whose entries below `k` are
    those of `arr`. -/
theorem steps_resCopy_aux {P : JasminLsemMemLoop.LprogM} {src D : String} {m : Nat}
    (hm : m < 2 ^ 64) (pre : List LinstrRM) (s : LstateMF) (hat : atPc P pre.length s)
    {arr : Fin m → BitVec 64} (hsrc : s.prog.base.getArr src 64 m = some arr)
    {a0 : Fin m → BitVec 64} (hD : s.prog.base.getArr D 64 m = some a0)
    (hfr : ∀ j, j < m → src ≠ copyName D (j + 1)) :
    ∀ k, k ≤ m → ∀ post : List LinstrRM,
      P.body = pre ++ (List.range k).flatMap (resCopyStep src D m) ++ post →
      ∃ u, StepsL P (3 * k) s u (resCopyLeak src D k) ∧ atPc P (pre.length + 3 * k) u
        ∧ u.prog.base.getArr src 64 m = some arr
        ∧ ∃ b : Fin m → BitVec 64, u.prog.base.getArr (copyName D k) 64 m = some b
          ∧ ∀ i (hi : i < m), i < k → b ⟨i, hi⟩ = arr ⟨i, hi⟩ := by
  intro k
  induction k with
  | zero =>
      intro _ _ _
      exact ⟨s, ⟨Steps.refl x86Isa P s, rfl⟩, hat, hsrc, a0, by simpa [copyName] using hD,
        fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
      intro hk post hbody
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton] at hbody
      obtain ⟨u, hs, hatu, hsu, b, hb, hbv⟩ := ih (by omega) (resCopyStep src D m k ++ post)
        (by rw [hbody]; simp only [List.append_assoc])
      have hpos : (pre ++ (List.range k).flatMap (resCopyStep src D m)).length
          = pre.length + 3 * k := by
        simp [List.length_flatMap, resCopyStep]; omega
      have hb' : P.body = (pre ++ (List.range k).flatMap (resCopyStep src D m)) ++
          resCopyStep src D m k ++ post := by rw [hbody]; simp only [List.append_assoc]
      generalize pre ++ (List.range k).flatMap (resCopyStep src D m) = X at hpos hb'
      rw [← hpos] at hatu
      have hk' : k < m := by omega
      have hk64 : k < 2 ^ 64 := by omega
      generalize hL : ((.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m)
        : LinstrRM) = L at hb'
      generalize hS : ((.Lopn [.reg (copyName D (k + 1))] "STOREIDX"
        [.arrIdx (copyName D k) copyIdx 8, .reg copyTmp], .store 64 m) : LinstrRM) = S at hb'
      have hb1 : P.body = X ++ movImmI copyIdx k :: L :: S :: post := by
        rw [hb', ← hL, ← hS]; simp [resCopyStep]
      have hb2 : P.body = (X ++ [movImmI copyIdx k]) ++ L :: S :: post := by
        rw [hb1]; simp
      have hb3 : P.body = (X ++ [movImmI copyIdx k, L]) ++ S :: post := by
        rw [hb1]; simp
      -- The move of the index.
      obtain ⟨u1, hs1, hat1, hl1, hr1⟩ := steps_movImm (dst := copyIdx) (c := k) hatu
        (fetch_of_body hb1 rfl)
      have hsL1 := stepsL_one hatu (fetch_of_body hb1 rfl) hs1
      rw [instrLeakF_of_lopn ⟨_, _, _, rfl⟩] at hsL1
      have hsrc1 : u1.prog.base.getArr src 64 m = some arr := by
        unfold LstateM.getArr; rw [hl1]; exact hsu
      have hb1' : u1.prog.base.getArr (copyName D k) 64 m = some b := by
        unfold LstateM.getArr; rw [hl1]; exact hb
      have hzl1 : u1.prog.base.reg.lvm copyIdx = ⟨64, BitVec.ofNat 64 k⟩ := by
        rw [hr1, ite_eq_left rfl]
      have hz1 : u1.prog.base.reg.getW copyIdx 64 = some (BitVec.ofNat 64 k) :=
        getW_of_lvm _ _ _ hzl1
      -- The load of the word.
      have h2 := JasminLsemMemSourceTieUncond.lsemStepMem_loadIdx copyTmp src copyIdx 8 arr _
        u1.prog.base hsrc1 hz1
      have hlk2 : instrLeakB u1.prog.base.reg L = [.addr src (Int.ofNat (8 * k))] := by
        rw [← hL]; simp [instrLeakB, opLeakF, idxVal]; rw [hzl1]; simpa using hk64
      rw [hL] at h2
      obtain ⟨hs2, hat2⟩ := x86_steps_mem hat1 (fetch_of_body hb2 (by simp))
        (by rw [← hL]; exact ⟨_, _, _, rfl⟩) (by rw [← hL]; rfl) (by rw [← hL]; rfl) h2
      have hsL2 := stepsL_one hat1 (fetch_of_body hb2 (by simp)) hs2
      rw [instrLeakF_of_lopn (by rw [← hL]; exact ⟨_, _, _, rfl⟩), hlk2] at hsL2
      generalize hu2 : setBase u1 (JasminLsemMemFlagGuard.withALUFlags L u1.prog.base _)
        = u2 at hs2 hat2 hsL2
      have hl2 : u2.prog.base.larr = u1.prog.base.larr := by
        rw [← hu2, setBase_base, JasminLsemMemFlagGuard.withALUFlags_larr]; rfl
      have hr2 : ∀ r, u2.prog.base.reg.lvm r = if r = copyTmp
          then ⟨64, stackGet arr (BitVec.ofNat 64 k).toNat⟩ else u1.prog.base.reg.lvm r := by
        intro r
        rw [← hu2, setBase_base, JasminLsemMemFlagGuard.withALUFlags_reg]
        simp only [LstateM.nextPc, LstateM.setReg, LstateN.lvm_nextPc, LstateN.lvm_setReg]
      have hb2' : u2.prog.base.getArr (copyName D k) 64 m = some b := by
        unfold LstateM.getArr; rw [hl2]; exact hb1'
      have hzl2 : u2.prog.base.reg.lvm copyIdx = ⟨64, BitVec.ofNat 64 k⟩ := by
        rw [hr2, ite_eq_right (by decide), hzl1]
      have hz2 : u2.prog.base.reg.getW copyIdx 64 = some (BitVec.ofNat 64 k) :=
        getW_of_lvm _ _ _ hzl2
      have hv2 : u2.prog.base.reg.getW copyTmp 64
          = some (stackGet arr (BitVec.ofNat 64 k).toNat) := by
        apply getW_of_lvm; rw [hr2, ite_eq_left rfl]
      -- The store of the word.
      have h3 := JasminLsemMemSourceTieUncond.lsemStepMem_storeIdx (copyName D (k + 1))
        (copyName D k) copyIdx copyTmp 8 b _ _ u2.prog.base hb2' hz2 hv2
      have hlk3 : instrLeakB u2.prog.base.reg S
          = [.addr (copyName D k) (Int.ofNat (8 * k))] := by
        rw [← hS]; simp [instrLeakB, opLeakF, idxVal]; rw [hzl2]; simpa using hk64
      rw [hS] at h3
      obtain ⟨hs3, hat3⟩ := x86_steps_mem hat2 (fetch_of_body hb3 (by simp))
        (by rw [← hS]; exact ⟨_, _, _, rfl⟩)
        (by rw [← hS]; unfold JasminLsemMemFlagGuard.cmpArgs?; exact ite_eq_right (by decide))
        (by rw [← hS]; rfl) h3
      have hsL3 := stepsL_one hat2 (fetch_of_body hb3 (by simp)) hs3
      rw [instrLeakF_of_lopn (by rw [← hS]; exact ⟨_, _, _, rfl⟩), hlk3] at hsL3
      generalize hnb : stackSet b (BitVec.ofNat 64 k).toNat
        (stackGet arr (BitVec.ofNat 64 k).toNat) = nb at hs3 hat3 hsL3
      generalize hu3 : setBase u2 (JasminLsemMemFlagGuard.withALUFlags S u2.prog.base _)
        = u3 at hs3 hat3 hsL3
      have hl3 : u3.prog.base.larr = (u2.prog.base.setArr (copyName D (k + 1)) nb).larr := by
        rw [← hu3, setBase_base, JasminLsemMemFlagGuard.withALUFlags_larr]; rfl
      have hmv : instrLeakB u.prog.base.reg (movImmI copyIdx k) = [] := by
        simp [instrLeakB, movImmI, ExportRegions.movI, opLeakF]
      rw [hmv] at hsL1
      refine ⟨u3, ?_, ?_, ?_, nb, ?_, fun i hi hik => ?_⟩
      · have := hs.trans (hsL1.trans (hsL2.trans hsL3))
        rw [show 3 * k + (1 + (1 + 1)) = 3 * (k + 1) by omega] at this
        refine this.cast ?_
        simp [resCopyLeak, List.range_succ, List.flatMap_append]
      · rw [hpos] at hat3
        rwa [show pre.length + 3 * k + 1 + 1 + 1 = pre.length + 3 * (k + 1) by omega] at hat3
      · rw [getArr_of_larr_eq (s' := u2.prog.base.setArr (copyName D (k + 1)) nb) (r' := src)
          64 m (by rw [hl3]), LstateM.getArr_setArr_other _ _ _ _ _ _ (hfr k hk')]
        unfold LstateM.getArr; rw [hl2, hl1]; exact hsu
      · rw [getArr_of_larr_eq (s' := u2.prog.base.setArr (copyName D (k + 1)) nb)
          (r' := copyName D (k + 1)) 64 m (by rw [hl3]), LstateM.getArr_setArr_same]
      · rw [← hnb, stackSet_ofNat_apply b hk' hm, stackGet_ofNat_lt arr hk' hm]
        by_cases h : i = k
        · subst h; simp
        · simp only [h, ite_false]; exact hbv i hi (by omega)

/-- **The result copy** of the `m`-word array `src` into `D`, behind `pre` in the body of
    `P`, from a state at the end of `pre` in which `src` holds `arr` and `D` an array of `m`
    words, with `m < 2 ^ 64` and no version `copyName D (j + 1)`, `j < m`, equal to `src`:
    `3 * m` steps with the events `resCopyLeak src D m` lead to a state at the end of the
    copy in which `copyName D m` holds `arr`. -/
theorem steps_resCopy {P : JasminLsemMemLoop.LprogM} {src D : String} {m : Nat}
    (hm : m < 2 ^ 64) (pre post : List LinstrRM) (s : LstateMF)
    (hbody : P.body = pre ++ resCopyCode src D m ++ post) (hat : atPc P pre.length s)
    {arr : Fin m → BitVec 64} (hsrc : s.prog.base.getArr src 64 m = some arr)
    {a0 : Fin m → BitVec 64} (hD : s.prog.base.getArr D 64 m = some a0)
    (hfr : ∀ j, j < m → src ≠ copyName D (j + 1)) :
    ∃ u, StepsL P (3 * m) s u (resCopyLeak src D m) ∧ atPc P (pre.length + 3 * m) u
      ∧ u.prog.base.getArr (copyName D m) 64 m = some arr := by
  obtain ⟨u, hs, hat', -, b, hb, hbv⟩ :=
    steps_resCopy_aux hm pre s hat hsrc hD hfr m le_rfl post hbody
  refine ⟨u, hs, hat', ?_⟩
  rw [hb]
  congr 1
  funext i
  exact hbv i.1 i.2 i.2

/-- **The run of the virtual body of a region export with a result copy.** Let `p` be a
    program of `RegionExportable` with a result of `m < 2 ^ 64` words and the export `r`,
    whose returned operand names the array `src`; let `D` be the argument name of a
    parameter of `σ` of `m` words; and let no version `copyName D (j + 1)`, `j < m`, be
    `src`. Under the hypotheses of `regionVirt_run`, the copies of the parameter registers,
    the code of `r` and the result copy `resCopyCode src D m`, run by `lsemFuelMemF` from the
    entry state `entryV`, halt in a state in which `copyName D m` holds the source value of
    the result. -/
theorem regionVirt_run_copy (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) [.stackArr 64 m])
    (hden : p.denote fuel V = some v) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m)) k
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some t
      ∧ t.prog.base.getArr (copyName D m) 64 m
        = some (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr 64 m])
          (t := .stackArr 64 m) .here v) := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) :=
    entryV_abiEntry E.argF E.argG hU
  have hag0 := storeAgreesM_of_abi hV habi
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := un) E.argF E.argG hS false
  have hag1 : StoreAgreesM Γ.length Γ.length
      ({ entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } } : LstateM) V :=
    StoreAgreesM.of_regionFrame (n := 0) rfl hag0
      ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  have hlen : (argBind σ nm).length = σ.args.length := by
    simp [argBind, movesOf_length, argPairs]
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨k, t0, hs, hat, hres, hfrm, -⟩ := exportR_sim Γ.length fn hp Γ.length 0 r hr rfl
    le_rfl (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m)) (argBind σ nm)
    (resCopyCode src D m) rfl rfl
    (fun l _ => (findLabelMem_eq_none_iff l _).mpr (by rw [labelsOf_of_isLopn hlop]; simp))
    fuel V v
    { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
        lpc := σ.args.length } }, lfn := fn }, zf := false }
    hden ⟨rfl, hlen.symm⟩ hag1
  obtain ⟨op, hop, harr⟩ := hres.decodeArrM_single
  have harr' : t0.prog.base.getArr src 64 m = some (Ctxt.Var.lookup (d := jasminDialect)
      (Γ := [.stackArr 64 m]) (t := .stackArr 64 m) .here v) := by
    rw [← hsrc op hop]; exact harr
  -- The result buffer holds its entry array.
  obtain ⟨a0, hD0⟩ : ∃ a0, t0.prog.base.getArr D 64 m = some a0 := by
    obtain ⟨j, a, hj, hk, rfl⟩ := hD
    rw [hfrm.2 (argName j) 64 m (fun i _ => (JasminLsemSimulation.regName_ne_argName i j).symm)
      (fun l _ => (JasminLsemExportTransfer.loopCtr_ne_argName l j).symm)]
    exact ⟨_, habi.arr j a m hj hk⟩
  obtain ⟨u, hsu, hatu, hu⟩ := steps_resCopy
    (P := singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m)) hm
    (argBind σ nm ++ r.code) [] t0 (by simp [singletonProgM])
    (by rw [List.length_append]; exact hat) harr' hD0 hfr
  have hhalt := halted_of_atPc hatu (by
    simp [singletonProgM, resCopyCode, List.length_flatMap, resCopyStep]; omega)
  have hfin := lsemFuelMemF_of_steps x86Isa _ (hs.trans hsu.1) hhalt 0
  rw [X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hfin
  refine ⟨(argBind σ nm).length + (k + 3 * m + 0), u, ?_, hu⟩
  rw [lsemFuelMemF_segF _ fn rfl (argBind σ nm) (entryV σ fr sa un) false (k + 3 * m + 0) hlop
    (fun i hi => by
      show (argBind σ nm ++ r.code ++ resCopyCode src D m)[0 + i]? = _
      rw [Nat.zero_add, List.append_assoc, List.getElem?_append_left hi]), hpre,
    Option.bind_some]
  exact hfin

/-! ## 3. The coalesced and renamed reference -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK shiftS
  lsemFuelMemF_of_prefix lsemFuelMemF_prepend)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (clsB fuseMulHiRM fuseOKL
  fuseLo fuseLoPre KeptN fuseMulHi_lsemFuelMemF_pre)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (mulxFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrReads arrWrite CoRel
  chainAlias chainAliasO aliasTab aliasTabRes chainAliasRes zeroDst? aliasTabRes_eq_of_noZero
  chainAliasRes_eq_of_noZero)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (canonMemrefName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (coCfgB renArr ctlOK_renArr
  lsemFuelMemF_coalesce)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (cfgOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (SOut Tbl runsOf blockRuns)

/-- **The result of a linked function**: a word in the register of the name `r`, or the `n`
    words of its argument at the position `k`, the destination array, which the function
    writes at the pointer it receives in the register of that argument. -/
inductive CalleeRes where
  /-- A word in the register of the name `r`. -/
  | reg (r : String)
  /-- The `n` words of the destination array, the argument at the position `k`. -/
  | out (n k : Nat)
  deriving DecidableEq, Repr

/-- The result register of a word result; `none` for an out result. -/
def CalleeRes.reg? : CalleeRes → Option String
  | .reg r => some r
  | .out _ _ => none

/-- **The linked function a calling body calls**, as the data the back half reads: the
    symbol `name`; the names `args` of the argument registers at a call site; its result
    `res`, a result register or the destination array of one of its arguments; the machine
    registers `clob` the code may change; the size `frame` in bytes of its stack frame; its
    machine code `bytes`; and its machine contract: the precondition `pre`, the footprint
    `foot`, the postcondition `post` and the public relation `pub`. -/
structure CalleeData where
  /-- The symbol of the function. -/
  name : String
  /-- The names of the argument registers, in order. -/
  args : List String
  /-- The result: a result register, or the destination array of an argument. -/
  res : CalleeRes
  /-- The machine registers the code may change. -/
  clob : List String
  /-- The size in bytes of the stack frame. -/
  frame : Nat
  /-- The machine code. -/
  bytes : List (BitVec 8)
  /-- The precondition on the state at the entry of the function. -/
  pre : CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState → Prop
  /-- The addresses the function may write, from the state at its entry. -/
  foot : CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState → BitVec 64 → Prop
  /-- The relation between the entry state and the return state. -/
  post : CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState →
    CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState → Prop
  /-- The relation between two entry states that agree on the public arguments. -/
  pub : CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState →
    CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState → Prop
  /-- The machine registers of the public arguments. -/
  pubRegs : List String
  /-- The length in words of the array argument at a position; `none` at a word
      argument. -/
  arrArgs : Nat → Option Nat := fun _ => none
  /-- The store policy of the code: the red zone below its frame and the out windows it may
      store to; the frame alone by default. -/
  pol : X86Backend.Callee.StorePol := .frame

/-- **The shape of a call of a linked function on common names**: its array positions, and
    an out result at an out result of the function. -/
def CalleeData.shape (c : CalleeData) : LprogCallCut.CallShape where
  arrArgs := c.arrArgs
  out := match c.res with
    | .reg _ => false
    | .out _ _ => true

/-- **The register a call of a linked function returns in**: the result register of a word
    result, and the register of the argument at the destination position `k`, the
    destination, of an out result `.out n k` (the pointer at which the function writes the
    result). -/
def CalleeData.resReg (c : CalleeData) : String :=
  match c.res with
  | .reg r => r
  | .out _ k => c.args.getD k ""

/-- **The destination of a call of a linked function**: `none` at a word result, and at an
    out result `.out n k` the machine register `phys c.resReg` of the destination pointer with
    the length `n` in words of the destination. -/
def CalleeData.outDst? (c : CalleeData) : Option (String × Nat) :=
  match c.res with
  | .reg _ => none
  | .out n _ => some (phys c.resReg, n)

/-- The interface `Callee.CalleeSig` of a linked function: its argument names, its result
    register (none for an out result), its clobber set, and its precondition, footprint,
    postcondition and public relation. The checks of the gate read the first three
    fields. -/
def CalleeData.sig (c : CalleeData) : X86Backend.Callee.CalleeSig where
  args := c.args
  res := c.res.reg?
  clob := fun r => c.clob.contains r
  pre := c.pre
  foot := c.foot
  post := c.post
  pub := c.pub

/-- **A table of linked functions**: the functions a calling body may call, each found by its
    symbol. -/
structure CalleeTab where
  /-- The linked functions. -/
  fns : List CalleeData

/-- The table of one linked function. -/
def CalleeTab.one (c : CalleeData) : CalleeTab := ⟨[c]⟩

/-- The linked function of a table at a symbol: the first with that symbol. -/
def CalleeTab.lookup (T : CalleeTab) (g : String) : Option CalleeData :=
  T.fns.find? (·.name == g)

/-- The table of one linked function holds it at its symbol and nothing elsewhere. -/
@[simp] theorem CalleeTab.lookup_one (c : CalleeData) (g : String) :
    (CalleeTab.one c).lookup g = if g = c.name then some c else none := by
  by_cases h : g = c.name
  · simp [CalleeTab.lookup, CalleeTab.one, h]
  · have h' : ¬ c.name = g := fun e => h e.symm
    simp [CalleeTab.lookup, CalleeTab.one, h, h']

/-- The function of a table at a symbol is a function of the table with that symbol. -/
theorem CalleeTab.lookup_spec {T : CalleeTab} {g : String} {c : CalleeData}
    (h : T.lookup g = some c) : c ∈ T.fns ∧ c.name = g := by
  unfold CalleeTab.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The symbols of a table, in order. -/
def CalleeTab.names (T : CalleeTab) : List String := T.fns.map (·.name)

/-- The symbols of the table of one linked function. -/
@[simp] theorem CalleeTab.names_one (c : CalleeData) : (CalleeTab.one c).names = [c.name] := by
  simp [CalleeTab.names, CalleeTab.one]

/-- The table of procedures with the symbols of a table of linked functions, each at its
    number of arguments and the summary that refuses every argument list. The cut checks read
    which symbols the table holds. -/
def CalleeTab.tab (T : CalleeTab) : LprogIsa.ProcTable := fun g =>
  (T.lookup g).map fun c => { arity := c.args.length, run := fun _ => none }

/-- The table of procedures of one linked function holds its symbol only. -/
@[simp] theorem CalleeTab.tab_one (c : CalleeData) (g : String) :
    (CalleeTab.one c).tab g
      = if g = c.name then some { arity := c.args.length, run := fun _ => none } else none := by
  by_cases h : g = c.name <;> simp [CalleeTab.tab, h]

/-- The frame of a table: the largest frame of its functions, in bytes. -/
def CalleeTab.frame (T : CalleeTab) : Nat := T.fns.foldr (fun c m => max c.frame m) 0

/-- The frame of the table of one linked function is its frame. -/
@[simp] theorem CalleeTab.frame_one (c : CalleeData) : (CalleeTab.one c).frame = c.frame := by
  simp [CalleeTab.frame, CalleeTab.one]

/-- The frame of each function of a table is at most the frame of the table. -/
theorem CalleeTab.frame_le {T : CalleeTab} {c : CalleeData} (hc : c ∈ T.fns) :
    c.frame ≤ T.frame := by
  obtain ⟨fns⟩ := T
  simp only [CalleeTab.frame] at hc ⊢
  induction fns with
  | nil => cases hc
  | cons d l ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hc with rfl | hl
      · exact le_max_left _ _
      · exact le_trans (ih hl) (le_max_right _ _)

/-- The allocation pool of a caller of the functions of a table: `Callee.keepPoolT` at their
    interfaces. -/
def CalleeTab.pool (T : CalleeTab) : List String :=
  X86Backend.Callee.keepPoolT (T.fns.map (·.sig))

/-- The pool of the table of one linked function is the pool of its interface. -/
@[simp] theorem CalleeTab.pool_one (c : CalleeData) :
    (CalleeTab.one c).pool = X86Backend.Callee.keepPool c.sig :=
  X86Backend.Callee.keepPoolT_singleton c.sig

/-- The check of each interface of a table accepts the pool of the table. -/
theorem CalleeTab.keepPoolB_pool {T : CalleeTab} {c : CalleeData} (hc : c ∈ T.fns) :
    X86Backend.Callee.keepPoolB c.sig T.pool = true :=
  X86Backend.Callee.keepPoolB_keepPoolT (List.mem_map_of_mem hc)

/-- **The out symbols of a table**: the symbol of each function with an out result
    `.out n k`, paired with its destination position `k`. -/
def CalleeTab.outs (T : CalleeTab) : List (String × Nat) :=
  T.fns.filterMap fun c => match c.res with
    | .out _ k => some (c.name, k)
    | .reg _ => none

/-- The out symbols of the table of one linked function. -/
@[simp] theorem CalleeTab.outs_one (c : CalleeData) :
    (CalleeTab.one c).outs = match c.res with
      | .out _ k => [(c.name, k)]
      | .reg _ => [] := by
  cases hr : c.res <;> simp [CalleeTab.outs, CalleeTab.one, hr]

/-- **The common names of a table**, in the form of `LprogCallCut.commonCallsT?`: at a symbol
    of the table the shape of the calls of its function, the argument names and the result
    register. -/
def CalleeTab.common (T : CalleeTab) :
    String → Option (LprogCallCut.CallShape × List String × String) := fun g =>
  (T.lookup g).map fun c => (c.shape, c.args, c.resReg)

/-- The common names of the table of one linked function are `LprogCallCut.tabOne`. -/
@[simp] theorem CalleeTab.common_one (c : CalleeData) :
    (CalleeTab.one c).common = LprogCallCut.tabOne c.shape c.name c.args c.resReg := by
  funext g
  by_cases h : g = c.name <;> simp [CalleeTab.common, LprogCallCut.tabOne, h]

/-- **The interface of a table at a symbol**: that of its function, and at a symbol outside
    the table the interface that clobbers nothing and has no behaviour. -/
def CalleeTab.sigOf (T : CalleeTab) (g : String) : X86Backend.Callee.CalleeSig :=
  match T.lookup g with
  | some c => c.sig
  | none =>
      { args := [], res := none, clob := fun _ => false, pre := fun _ => False,
        foot := fun _ _ => False, post := fun _ _ => False, pub := fun _ _ => False }

/-- **The result kind of a table at a symbol**: `true` for a function with an out result. -/
def CalleeTab.outOf (T : CalleeTab) (g : String) : Bool :=
  (T.lookup g).any fun c => match c.res with
    | .out _ _ => true
    | .reg _ => false

/-- The table of procedures of a table holds exactly the symbols of the table. -/
theorem CalleeTab.lookup_isSome (T : CalleeTab) :
    (fun g => (T.lookup g).isSome) = fun g => T.names.contains g := by
  funext g
  obtain ⟨fns⟩ := T
  simp only [CalleeTab.lookup, CalleeTab.names]
  rw [Bool.eq_iff_iff]
  grind

/-- The table of procedures with the one symbol of the linked function, at its number of
    arguments and the summary that refuses every argument list: `CalleeTab.tab` at the table
    of that function. -/
def CalleeData.tab (c : CalleeData) : LprogIsa.ProcTable := (CalleeTab.one c).tab

/-- The table of procedures of a linked function holds its symbol only. -/
theorem CalleeData.tab_apply (c : CalleeData) (g : String) :
    c.tab g = if g = c.name then some { arity := c.args.length, run := fun _ => none } else none :=
  CalleeTab.tab_one c g

/-- **The parameters of a linked function**: each argument name with its kind, an array of
    `m` words at an array position of length `m` and a scalar at every other position. -/
def CalleeData.ins (c : CalleeData) : List (String × ArgKind) :=
  c.args.mapIdx fun i a => (a, match c.arrArgs i with
    | some m => .words m
    | none => .scalar)

/-- The names of the parameters of a linked function are its argument names. -/
theorem CalleeData.ins_map_fst (c : CalleeData) : c.ins.map (·.1) = c.args := by
  unfold CalleeData.ins; apply List.ext_getElem <;> simp

/-- **The operands of a call of `c` at the position `p` of a printed body** at the slot map
    `sl`: for a scalar parameter its name, and for an array parameter the array of the frame
    slot whose word the register of the parameter holds before position `p` (`accArr`), or
    the name of the parameter when there is none. -/
def CalleeData.siteArgs (c : CalleeData) (sl : String → Option (String × Nat)) (body : Lcmd)
    (p : Nat) : List String :=
  c.ins.map fun q => match q.2 with
    | .scalar => q.1
    | .words _ => ((VIR.JasminLsemAddrImage.accArr sl body p q.1).map Prod.fst).getD q.1

/-- The operands of a call of `c` at a position have one per parameter of `c`. -/
theorem CalleeData.siteArgs_length (c : CalleeData) (sl : String → Option (String × Nat))
    (body : Lcmd) (p : Nat) : (c.siteArgs sl body p).length = c.ins.length := by
  simp [CalleeData.siteArgs]

/-- **The call site of `c` at the position `p` of a printed body** at the slot map `sl`: the
    destination name and the operand names of the shadow instruction of the call at `p` in
    the image. The operands are `CalleeData.siteArgs` at `p`; the destination is the result
    register for a word result and the operand at the destination position `k`, the
    destination array, for an out result `.out n k`. -/
def calleeSiteAt (c : CalleeData) (sl : String → Option (String × Nat)) (body : Lcmd)
    (p : Nat) : String × List String :=
  match c.res with
  | .reg _ => (c.resReg, c.siteArgs sl body p)
  | .out _ k =>
      let ops := c.siteArgs sl body p
      (ops.getD k "", ops)

/-- The operands of the call site of `c` at `p` are `CalleeData.siteArgs` at `p`. -/
theorem calleeSiteAt_snd (c : CalleeData) (sl : String → Option (String × Nat)) (body : Lcmd)
    (p : Nat) : (calleeSiteAt c sl body p).2 = c.siteArgs sl body p := by
  unfold calleeSiteAt; split <;> rfl

/-- At a word result and scalar parameters the call site at every position is the result
    register and the argument names. -/
theorem calleeSiteAt_of_reg {c : CalleeData} {r : String} (h : c.res = .reg r)
    (haa : c.arrArgs = fun _ => none)
    (sl : String → Option (String × Nat)) (body : Lcmd) :
    calleeSiteAt c sl body = fun _ => (c.resReg, c.args) := by
  funext p
  simp only [calleeSiteAt, h, CalleeData.siteArgs, CalleeData.ins, haa, Prod.mk.injEq,
    true_and]
  apply List.ext_getElem <;> simp

/-- **A call site of a calling body**: the position `pos` of the call, the symbol `sym` it
    calls, and the destination name `dst` and the operand names `ops` of its shadow
    instruction in the image. -/
structure CallSite where
  /-- The position of the call in the body. -/
  pos : Nat
  /-- The symbol the call names. -/
  sym : String
  /-- The destination name of the shadow instruction. -/
  dst : String
  /-- The operand names of the shadow instruction. -/
  ops : List String

/-- The destination, the symbol and the operands of the shadow instruction of a call site,
    in the form of `LprogIsa.shadowCall?`. -/
def CallSite.shadow (s : CallSite) : String × String × List LOperand :=
  (s.dst, s.sym, s.ops.map LOperand.reg)

/-- **The table of one linked function**: `c` at its symbol and `none` at every other
    symbol. -/
def CalleeData.lookup (c : CalleeData) (g : String) : Option CalleeData :=
  (CalleeTab.one c).lookup g

/-- The table of one linked function holds exactly its symbol. -/
theorem CalleeData.lookup_isSome (c : CalleeData) :
    (fun g => (c.lookup g).isSome) = (· == c.name) := by
  funext g
  by_cases h : g = c.name <;> simp [CalleeData.lookup, h]

/-- The symbol of the call at the position `p` of a body, `none` when `p` holds no call. -/
def callSymAt (body : Lcmd) (p : Nat) : Option String :=
  body[p]?.bind fun bi => match bi.li_i with
    | .Lcall _ (f, _) => some f
    | _ => none

/-- `callSymAt body p` is `f` exactly when `p` holds a call of `f`. -/
theorem callSymAt_eq_some {body : Lcmd} {p : Nat} {f : String} :
    callSymAt body p = some f ↔
      ∃ bi ra l, body[p]? = some bi ∧ bi.li_i = .Lcall ra (f, l) := by
  constructor
  · intro h
    obtain ⟨bi, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ii, li⟩ := bi
    cases li with
    | Lcall ra t =>
        obtain ⟨g, l⟩ := t
        simp only [Option.some.injEq] at h
        exact ⟨_, ra, l, hb, by simp [h]⟩
    | _ => simp at h
  · rintro ⟨bi, ra, l, hb, hbi⟩
    simp [callSymAt, hb, hbi]

/-- **The decode of a calling body into its call sites** at the table of callees `cs` and the
    slot map `sl`: at each position `p` of `ImageAddrCall.callPos body`, the symbol `f` of the
    call and the destination and operands `calleeSiteAt c sl body p` of its callee
    `cs f = some c`; `none` when a call names a symbol outside `cs`. -/
def decodeSites (cs : String → Option CalleeData) (sl : String → Option (String × Nat))
    (body : Lcmd) : Option (List CallSite) :=
  (X86Backend.ImageAddrCall.callPos body).mapM fun p => do
    let f ← callSymAt body p
    let c ← cs f
    let s := calleeSiteAt c sl body p
    pure ⟨p, f, s.1, s.2⟩

/-- **The site function of a body with several callees**: at a call of a symbol `f` with the
    callee `cs f = some c`, the call site `calleeSiteAt c sl body p`; elsewhere the empty
    destination and no operands. -/
def siteFn (cs : String → Option CalleeData) (sl : String → Option (String × Nat))
    (body : Lcmd) (p : Nat) : String × List String :=
  match (callSymAt body p).bind cs with
  | some c => calleeSiteAt c sl body p
  | none => ("", [])

/-- At a call of a symbol `f` whose callee in `cs` is `c`, the site function is the call
    site of `c`. -/
theorem siteFn_of_callSym {cs : String → Option CalleeData}
    {sl : String → Option (String × Nat)} {body : Lcmd} {p : Nat} {f : String}
    {c : CalleeData} (hs : callSymAt body p = some f) (hc : cs f = some c) :
    siteFn cs sl body p = calleeSiteAt c sl body p := by
  simp [siteFn, hs, hc]

/-- **Soundness of `decodeSites`**: the positions of the decoded sites are
    `ImageAddrCall.callPos body`, and each site is a call of its symbol in the body, whose
    callee in `cs` gives its destination and operands. -/
theorem decodeSites_spec {cs : String → Option CalleeData}
    {sl : String → Option (String × Nat)} {body : Lcmd} {ss : List CallSite}
    (h : decodeSites cs sl body = some ss) :
    ss.map CallSite.pos = X86Backend.ImageAddrCall.callPos body ∧
      ∀ s ∈ ss, ∃ bi ra l c, body[s.pos]? = some bi ∧ bi.li_i = .Lcall ra (s.sym, l) ∧
        cs s.sym = some c ∧ calleeSiteAt c sl body s.pos = (s.dst, s.ops) := by
  unfold decodeSites at h
  generalize X86Backend.ImageAddrCall.callPos body = l at h ⊢
  induction l generalizing ss with
  | nil =>
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      simp
  | cons p l ih =>
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ss', hss, hss'⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some_inj.mp hss'
      obtain ⟨f, hf, hs⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨bi, ra, l', hb, hbi⟩ := callSymAt_eq_some.mp hf
      obtain ⟨ih1, ih2⟩ := ih hss
      simp only [Option.some.injEq] at hs
      subst hs
      refine ⟨by simp [ih1], ?_⟩
      rintro s (_ | ⟨_, hs⟩)
      · exact ⟨bi, ra, l', c, hb, hbi, hc, rfl⟩
      · exact ih2 s hs

/-- **Completeness of `decodeSites`**: when every call of the body names a symbol of `cs`,
    the decode succeeds. -/
theorem decodeSites_isSome {cs : String → Option CalleeData}
    {sl : String → Option (String × Nat)} {body : Lcmd}
    (hsym : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => (cs g).isSome) body = true) :
    (decodeSites cs sl body).isSome = true := by
  have key : ∀ (F : Nat → Option CallSite) (l : List Nat),
      (∀ p ∈ l, (F p).isSome = true) → (l.mapM F).isSome = true := by
    intro F l
    induction l with
    | nil => simp
    | cons p l ih =>
        intro hl
        obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hl p List.mem_cons_self)
        obtain ⟨ss, hss⟩ := Option.isSome_iff_exists.mp
          (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
        simp [List.mapM_cons, hs, hss]
  apply key
  intro p hp
  obtain ⟨hlt, hany⟩ := X86Backend.ImageAddrCall.mem_callPos.mp hp
  cases hb : body[p]? with
  | none => rw [hb] at hany; cases hany
  | some bi =>
      rw [hb, Option.any_some] at hany
      obtain ⟨ra, f, l, e⟩ := X86Backend.ImageAddrCall.exists_lcall_of_isCallB hany
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
        (X86Backend.ImageAddrCall.bodyCallSymsB_spec hsym hb hlt e)
      simp [callSymAt_eq_some.mpr ⟨bi, ra, l, hb, e⟩, hc]

/-- **The calls of a decoded body name symbols of `cs`.** -/
theorem bodyCallSymsB_of_decodeSites {cs : String → Option CalleeData}
    {sl : String → Option (String × Nat)} {body : Lcmd}
    (hd : (decodeSites cs sl body).isSome = true) :
    X86Backend.ImageAddrCall.bodyCallSymsB (fun g => (cs g).isSome) body = true := by
  obtain ⟨ss, hss⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨hpos, hsite⟩ := decodeSites_spec hss
  simp only [X86Backend.ImageAddrCall.bodyCallSymsB, List.all_eq_true, List.mem_range]
  intro p hp
  cases hb : body[p]? with
  | none => rfl
  | some bi =>
      rw [Option.all_some]
      cases hx : bi.li_i with
      | Lcall ra t =>
          obtain ⟨f, l⟩ := t
          have hmem : p ∈ X86Backend.ImageAddrCall.callPos body :=
            X86Backend.ImageAddrCall.mem_callPos.mpr
              ⟨hp, by simp [hb, hx, X86Backend.ImageAddrCall.isCallB]⟩
          rw [← hpos] at hmem
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
          obtain ⟨bi', ra', l', c, hb', hbi', hc, -⟩ := hsite s hs
          rw [hb, Option.some_inj] at hb'
          subst hb'
          rw [hx, LinstrR.Lcall.injEq] at hbi'
          obtain ⟨-, hf⟩ := hbi'
          simp only [Prod.mk.injEq] at hf
          simp [hf.1, hc]
      | _ => rfl

/-- **The site function at the table of one callee** is its call site at every call: when
    the decode at `c.lookup` succeeds, `siteFn c.lookup sl body` agrees with
    `calleeSiteAt c sl body` at the positions `ImageAddrCall.callPos body`. -/
theorem siteFn_lookup {c : CalleeData} {sl : String → Option (String × Nat)} {body : Lcmd}
    (hd : (decodeSites c.lookup sl body).isSome = true) {p : Nat}
    (hp : p ∈ X86Backend.ImageAddrCall.callPos body) :
    siteFn c.lookup sl body p = calleeSiteAt c sl body p := by
  obtain ⟨hlt, hany⟩ := X86Backend.ImageAddrCall.mem_callPos.mp hp
  cases hb : body[p]? with
  | none => rw [hb] at hany; cases hany
  | some bi =>
      rw [hb, Option.any_some] at hany
      obtain ⟨ra, f, l, e⟩ := X86Backend.ImageAddrCall.exists_lcall_of_isCallB hany
      have hf : (c.lookup f).isSome = true :=
        X86Backend.ImageAddrCall.bodyCallSymsB_spec (bodyCallSymsB_of_decodeSites hd) hb hlt e
      have hfc : f = c.name := by
        by_contra hne
        simp [CalleeData.lookup, hne] at hf
      subst hfc
      simp [siteFn, callSymAt_eq_some.mpr ⟨bi, ra, l, hb, e⟩, CalleeData.lookup]

/-- **The image at the site function of one callee** is the image at its call sites. -/
theorem callImg_siteFn_lookup {c : CalleeData} {sl : String → Option (String × Nat)}
    {body : Lcmd} (hd : (decodeSites c.lookup sl body).isSome = true) :
    X86Backend.ImageAddrCall.callImg sl (siteFn c.lookup sl body) body
      = X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body :=
  X86Backend.ImageAddrCall.callImg_congr_site sl fun _ hp => siteFn_lookup hd hp

/-- **The decode lists the shadow instructions of the image, in order**: under
    `ImageAddrCall.callSitesB`, with every call of the body naming a symbol of `T`, the
    shadow instructions at the positions `LprogCallCut.sites T` of the image at the site
    function `siteFn cs sl body` are the shadows of the decoded sites. -/
theorem shadows_callImg {T : LprogIsa.ProcTable} {cs : String → Option CalleeData}
    {sl : String → Option (String × Nat)} {body : Lcmd} {ss : List CallSite}
    (hd : decodeSites cs sl body = some ss)
    (hcs : X86Backend.ImageAddrCall.callSitesB sl body = true)
    (hsym : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => (T g).isSome) body = true) :
    (LprogCallCut.sites T (X86Backend.ImageAddrCall.callImg sl (siteFn cs sl body) body)).map
        (X86Backend.CalleeSegCheck.shadowAt
          (X86Backend.ImageAddrCall.callImg sl (siteFn cs sl body) body))
      = ss.map (some ∘ CallSite.shadow) := by
  obtain ⟨hpos, hsite⟩ := decodeSites_spec hd
  rw [X86Backend.ImageAddrCall.sites_callImg _ hcs hsym, ← hpos, List.map_map]
  apply List.map_congr_left
  intro s hs
  obtain ⟨bi, ra, l, c, hb, hbi, hc, hsc⟩ := hsite s hs
  have hmem : s.pos ∈ X86Backend.ImageAddrCall.callPos body := hpos ▸ List.mem_map_of_mem hs
  obtain ⟨bi', f, l', hb', hbi', himg⟩ :=
    X86Backend.ImageAddrCall.callImg_getElem?_of_mem_callPos (siteFn cs sl body) hcs hmem
  rw [hb, Option.some_inj] at hb'
  subst hb'
  rw [hbi] at hbi'
  simp only [LinstrR.Lcall.injEq, Prod.mk.injEq] at hbi'
  obtain ⟨-, rfl, -⟩ := hbi'
  have hsf : siteFn cs sl body s.pos = (s.dst, s.ops) := by
    simp [siteFn, callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩, hc, hsc]
  simp [X86Backend.CalleeSegCheck.shadowAt, himg, hsf, LprogIsa.shadowCall?_callShadow,
    CallSite.shadow]

/-- **The decode accepts every body whose image has the shape of one callee**: under
    `ImageAddrCall.callSitesB`, if the image at a site function `site` passes
    `ImageAddrCall.siteShapeB c.name site`, the decode at `c.lookup` succeeds. -/
theorem decodeSites_lookup_of_siteShapeB {c : CalleeData}
    {sl : String → Option (String × Nat)} {body : Lcmd} {site : Nat → String × List String}
    (hcs : X86Backend.ImageAddrCall.callSitesB sl body = true)
    (hsh : X86Backend.ImageAddrCall.siteShapeB c.name site
      (X86Backend.ImageAddrCall.callImg sl site body) = true) :
    (decodeSites c.lookup sl body).isSome = true := by
  apply decodeSites_isSome
  rw [CalleeData.lookup_isSome]
  simp only [X86Backend.ImageAddrCall.bodyCallSymsB, List.all_eq_true, List.mem_range]
  intro p hp
  cases hb : body[p]? with
  | none => rfl
  | some bi =>
      rw [Option.all_some]
      cases hx : bi.li_i with
      | Lcall ra t =>
          obtain ⟨f, l⟩ := t
          have hmem : p ∈ X86Backend.ImageAddrCall.callPos body :=
            X86Backend.ImageAddrCall.mem_callPos.mpr
              ⟨hp, by simp [hb, hx, X86Backend.ImageAddrCall.isCallB]⟩
          obtain ⟨bi', f', l', hb', hbi', himg⟩ :=
            X86Backend.ImageAddrCall.callImg_getElem?_of_mem_callPos site hcs hmem
          rw [hb, Option.some_inj] at hb'
          subst hb'
          rw [hx] at hbi'
          simp only [LinstrR.Lcall.injEq, Prod.mk.injEq] at hbi'
          obtain ⟨-, rfl, -⟩ := hbi'
          have hm := List.all_eq_true.mp hsh p
            (List.mem_range.mpr (by rw [X86Backend.ImageAddrCall.callImg_length]; exact hp))
          rw [himg, Option.all_some, LprogIsa.shadowCall?_callShadow] at hm
          simpa using hm
      | _ => rfl

/-- **The check of the operand `x` of the parameter `q` at the position `p`** of a printed
    body: the name of `q` is a general-purpose name; a scalar parameter is the operand
    itself; the register of an array parameter of `m` words reloads, before `p`, the frame
    slot of the array `x` of the slot map `sl`, of length `m` (`accArr`). -/
def paramAtB (sl : String → Option (String × Nat)) (body : Lcmd) (p : Nat)
    (q : String × ArgKind) (x : String) : Bool :=
  X86Backend.DecodePrinted.gpOk q.1 && match q.2 with
    | .scalar => q.1 == x
    | .words m => VIR.JasminLsemAddrImage.accArr sl body p q.1 == some (x, m)

/-- **The check that the destination operand of an out callee is no other array operand**:
    for an out result `.out n k` of `c` whose parameter at the destination position `k` has
    the name `po`, the operand of every array parameter of another name differs from the
    operand of every parameter named `po`; `true` for a word result. -/
def outDestB (c : CalleeData) (ops : List String) : Bool :=
  match c.res with
  | .reg _ => true
  | .out _ k =>
      match c.ins[k]? with
      | none => true
      | some q0 => (c.ins.zip ops).all fun q =>
          q.1.2 == .scalar || q.1.1 == q0.1
            || (c.ins.zip ops).all fun q' => q'.1.1 != q0.1 || q.2 != q'.2

/-- **The check that the destination operand of an out callee is no other array operand,
    decided.** For an out result `.out n k` of `c` whose parameter at `k` is `q0`, `outDestB`
    holds exactly when the operand `x` of every array parameter `p` not named `q0.1`
    differs from the operand `x'` of every parameter `p'` named `q0.1`. -/
theorem outDestB_iff {c : CalleeData} {ops : List String} {n k : Nat} (hr : c.res = .out n k)
    {q0 : String × ArgKind} (hq0 : c.ins[k]? = some q0) :
    outDestB c ops = true ↔ ∀ p x, (p, x) ∈ c.ins.zip ops → p.2 ≠ .scalar → p.1 ≠ q0.1 →
      ∀ p' x', (p', x') ∈ c.ins.zip ops → p'.1 = q0.1 → x ≠ x' := by
  simp only [outDestB, hr, hq0, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq]
  constructor
  · intro h p x hpx hs hp p' x' hpx' hp' heq
    rcases h (p, x) hpx with (h1 | h1) | h1
    · exact hs h1
    · exact hp h1
    · rcases h1 (p', x') hpx' with h2 | h2
      · exact h2 hp'
      · exact h2 heq
  · intro h q hq
    by_cases hs : q.1.2 = .scalar
    · exact .inl (.inl hs)
    by_cases hp : q.1.1 = q0.1
    · exact .inl (.inr hp)
    refine .inr fun q' hq' => ?_
    by_cases hp' : q'.1.1 = q0.1
    · exact .inr (h q.1 q.2 hq hs hp q'.1 q'.2 hq' hp')
    · exact .inl hp'

/-- A word result passes `outDestB` at every operands. -/
theorem outDestB_of_reg {c : CalleeData} {r : String} (hr : c.res = .reg r)
    (ops : List String) : outDestB c ops = true := by
  simp only [outDestB, hr]

/-- **The check of the operands of a call of `c` at the position `p`**: every parameter of `c`
    and its operand among `c.siteArgs sl body p` pass `paramAtB`, and the destination operand
    of an out result is no other array operand (`outDestB`). -/
def callParamsAtB (c : CalleeData) (sl : String → Option (String × Nat)) (body : Lcmd)
    (p : Nat) : Bool :=
  (c.ins.zip (c.siteArgs sl body p)).all (fun q => paramAtB sl body p q.1 q.2)
    && outDestB c (c.siteArgs sl body p)

/-- **The check of the operands at the calls of a printed body**, at the callee `sel p` of the
    call at each position `p`: `callParamsAtB`, and nothing at a position without a callee. -/
def callParamsSelB (sel : Nat → Option CalleeData) (sl : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range body.length).all fun p => (body[p]?).all fun bi =>
    !X86Backend.ImageAddrCall.isCallB bi.li_i
      || (sel p).all fun c => callParamsAtB c sl body p

/-- `callParamsSelB` reads the callee at the calls only. -/
theorem callParamsSelB_congr {sel sel' : Nat → Option CalleeData}
    {sl : String → Option (String × Nat)} {body : Lcmd}
    (h : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → sel p = sel' p) :
    callParamsSelB sel sl body = callParamsSelB sel' sl body := by
  unfold callParamsSelB
  apply List.all_congr rfl
  intro p
  cases hb : body[p]? with
  | none => rfl
  | some bi =>
      simp only [Option.all_some]
      cases hc : X86Backend.ImageAddrCall.isCallB bi.li_i with
      | false => simp
      | true =>
          obtain ⟨ra, f, l, e⟩ := X86Backend.ImageAddrCall.exists_lcall_of_isCallB hc
          rw [h p bi ra (f, l) hb e]

/-- **The check of the operands at the calls of a printed body against `c`**: at each call
    instruction, at the position `p`, `callParamsAtB c`. -/
def callParamsB (c : CalleeData) (sl : String → Option (String × Nat)) (body : Lcmd) :
    Bool :=
  callParamsSelB (fun _ => some c) sl body

/-- **The check of the operands at the calls of a printed body against a table**: at each call
    of a symbol of the table `T`, `callParamsAtB` at the function of that symbol. -/
def callParamsBT (T : CalleeTab) (sl : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  callParamsSelB (fun p => (callSymAt body p).bind T.lookup) sl body

/-- **`callParamsBT` at a call**: the operands of a call of a symbol of the table pass
    `callParamsAtB` at the function of that symbol. -/
theorem callParamsAtB_of_tab {T : CalleeTab} {sl : String → Option (String × Nat)}
    {body : Lcmd} (h : callParamsBT T sl body = true) {p : Nat} {bi : Linstr}
    (hb : body[p]? = some bi) {ra : Option String} {f : String} {l : LLabel}
    (hbi : bi.li_i = .Lcall ra (f, l)) {c : CalleeData} (hc : T.lookup f = some c) :
    callParamsAtB c sl body p = true := by
  simp only [callParamsBT, callParamsSelB, List.all_eq_true, List.mem_range] at h
  have hp := h p (List.getElem?_eq_some_iff.mp hb).1
  have hs : callSymAt body p = some f := by simp [callSymAt, hb, hbi]
  rw [hb] at hp
  simp only [Option.all_some, hbi, X86Backend.ImageAddrCall.isCallB, Bool.not_true,
    Bool.false_or, hs, Option.bind_some, hc] at hp
  exact hp

/-- **`callParamsAtB` at a position**: the parameters and the operands at the position `p`
    pass `paramAtB`, and the operands pass `outDestB`. -/
theorem callParamsAtB_spec {c : CalleeData} {sl : String → Option (String × Nat)}
    {body : Lcmd} {p : Nat} (h : callParamsAtB c sl body p = true) :
    (∀ q ∈ c.ins.zip (c.siteArgs sl body p), paramAtB sl body p q.1 q.2 = true)
      ∧ outDestB c (c.siteArgs sl body p) = true := by
  simp only [callParamsAtB, Bool.and_eq_true, List.all_eq_true] at h
  exact h

/-- **`callParamsB` at a call instruction**: the parameters and the operands at the position
    `p` of a call pass `paramAtB`, and the operands pass `outDestB`. -/
theorem callParamsB_spec {c : CalleeData} {sl : String → Option (String × Nat)}
    {body : Lcmd} (h : callParamsB c sl body = true) {p : Nat} {bi : Linstr}
    (hb : body[p]? = some bi) {ra : Option String} {t : String × LLabel}
    (hbi : bi.li_i = .Lcall ra t) :
    (∀ q ∈ c.ins.zip (c.siteArgs sl body p), paramAtB sl body p q.1 q.2 = true)
      ∧ outDestB c (c.siteArgs sl body p) = true := by
  simp only [callParamsB, callParamsSelB, List.all_eq_true, List.mem_range] at h
  have hp := h p (List.getElem?_eq_some_iff.mp hb).1
  rw [hb] at hp
  simp only [Option.all_some, hbi, X86Backend.ImageAddrCall.isCallB, Bool.not_true,
    Bool.false_or, callParamsAtB, Bool.and_eq_true, List.all_eq_true] at hp
  exact hp

/-- The operands of a call that pass `callParamsB` pass `outDestB`. -/
theorem outDestB_of_callParamsB {c : CalleeData} {sl : String → Option (String × Nat)}
    {body : Lcmd} (h : callParamsB c sl body = true) {p : Nat} {bi : Linstr}
    (hb : body[p]? = some bi) {ra : Option String} {t : String × LLabel}
    (hbi : bi.li_i = .Lcall ra t) : outDestB c (c.siteArgs sl body p) = true :=
  (callParamsB_spec h hb hbi).2

/-- **The check of the dead names at the calls of a printed body against `c`**, at the slot
    map `sl` and the dead names `E`: for a word result `ImageAddrCall.callDeadB` at the
    interface of `c` and the call sites `calleeSiteAt`, for an out result
    `ImageAddrCallOutChain.callDeadOutB` at the call sites, and the operands pass
    `callParamsB`. -/
def calleeDeadB (c : CalleeData) (sl : String → Option (String × Nat)) (E : Nat → List String)
    (body : Lcmd) : Bool :=
  match c.res with
  | .reg _ => X86Backend.ImageAddrCall.callDeadB c.sig (calleeSiteAt c sl body) E body
      && callParamsB c sl body
  | .out _ _ =>
      X86Backend.ImageAddrCallOutChain.callDeadOutB c.sig (calleeSiteAt c sl body) E body
      && callParamsB c sl body

/-- At a word result and scalar parameters the check of the dead names is
    `ImageAddrCall.callDeadB` at the interface of `c` and the constant site of the result
    register and the argument names, and the operands pass `callParamsB`. -/
theorem calleeDeadB_of_reg {c : CalleeData} {r : String} (h : c.res = .reg r)
    (haa : c.arrArgs = fun _ => none)
    (sl : String → Option (String × Nat)) (E : Nat → List String) (body : Lcmd) :
    calleeDeadB c sl E body = (X86Backend.ImageAddrCall.callDeadB c.sig
      (fun _ => (c.resReg, c.args)) E body && callParamsB c sl body) := by
  simp only [calleeDeadB, h, calleeSiteAt_of_reg h haa]

/-- **The calls of a body with a closing return name `c`**: the decode at the table of `c`
    covers every call before the last position, and the last instruction is the return. -/
theorem callsName_of_decode {c : CalleeData} {sl : String → Option (String × Nat)} {body : Lcmd}
    (hd : (decodeSites c.lookup sl body).isSome = true)
    (hl : body.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true)
    {p : Nat} {bi : Linstr} {ra : Option String} {t : String × LLabel}
    (hb : body[p]? = some bi) (hbi : bi.li_i = .Lcall ra t) : t.1 = c.name := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hb
  by_cases hp : p < body.length - 1
  · have hf : (c.lookup t.1).isSome = true :=
      X86Backend.ImageAddrCall.bodyCallSymsB_spec (bodyCallSymsB_of_decodeSites hd) hb hp hbi
    by_contra hne
    simp [CalleeData.lookup, hne] at hf
  · have hpl : p = body.length - 1 := by omega
    subst hpl
    simp [List.getLast?_eq_getElem?, hb, hbi, X86Backend.DecodePrinted.isRetB] at hl

/-- At the table of one linked function the callee of a call that names it is that function. -/
theorem callSym_lookup_one {c : CalleeData} {body : Lcmd} {p : Nat} {bi : Linstr}
    {ra : Option String} {t : String × LLabel} (hb : body[p]? = some bi)
    (hbi : bi.li_i = .Lcall ra t) (ht : t.1 = c.name) :
    (callSymAt body p).bind (CalleeTab.one c).lookup = some c := by
  have hs : callSymAt body p = some t.1 := by
    obtain ⟨f, l⟩ := t
    exact callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩
  simp [hs, ht]

/-- **`callParamsBT` at the table of one linked function** is `callParamsB`, on a body whose
    calls name that function. -/
theorem callParamsBT_one {c : CalleeData} {sl : String → Option (String × Nat)} {body : Lcmd}
    (hsym : ∀ {p : Nat} {bi : Linstr} {ra : Option String} {t : String × LLabel},
      body[p]? = some bi → bi.li_i = .Lcall ra t → t.1 = c.name) :
    callParamsBT (CalleeTab.one c) sl body = callParamsB c sl body :=
  callParamsSelB_congr fun _ _ _ _ hb hbi => callSym_lookup_one hb hbi (hsym hb hbi)

/-- `ImageAddrCall.callDeadSymB` reads, at the calls only, the exempted names
    `ImageAddrCall.exemptC` of the interface, the kind and the site. -/
theorem callDeadSymB_congr_exempt {sig sig' : String → X86Backend.Callee.CalleeSig}
    {out out' : String → Bool} {site site' : Nat → String × List String}
    {E : Nat → List String} {body : Lcmd}
    (h : ∀ p bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      X86Backend.ImageAddrCall.exemptC (sig f) = X86Backend.ImageAddrCall.exemptC (sig' f)
        ∧ out f = out' f ∧ site p = site' p) :
    X86Backend.ImageAddrCall.callDeadSymB sig out site E body
      = X86Backend.ImageAddrCall.callDeadSymB sig' out' site' E body := by
  unfold X86Backend.ImageAddrCall.callDeadSymB
  apply List.all_congr rfl
  intro p
  cases hb : body[p]? with
  | none => rfl
  | some bi =>
      simp only [Option.all_some]
      obtain ⟨ii, li⟩ := bi
      cases li with
      | Lcall ra t =>
          obtain ⟨f, l⟩ := t
          obtain ⟨h1, h2, h3⟩ := h p _ ra f l hb rfl
          simp only [X86Backend.ImageAddrCall.deadOut, h1, h2, h3]
      | _ => rfl

/-- `ImageAddrCall.callDeadSymB` reads the interface, the kind and the site at the calls
    only. -/
theorem callDeadSymB_congr {sig sig' : String → X86Backend.Callee.CalleeSig}
    {out out' : String → Bool} {site site' : Nat → String × List String}
    {E : Nat → List String} {body : Lcmd}
    (h : ∀ p bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      sig f = sig' f ∧ out f = out' f ∧ site p = site' p) :
    X86Backend.ImageAddrCall.callDeadSymB sig out site E body
      = X86Backend.ImageAddrCall.callDeadSymB sig' out' site' E body :=
  callDeadSymB_congr_exempt fun p bi ra f l hb hbi => by
    obtain ⟨h1, h2, h3⟩ := h p bi ra f l hb hbi
    exact ⟨by rw [h1], h2, h3⟩

/-- **The check of the dead names at the calls of a printed body against a table**, at the slot
    map `sl` and the dead names `E`: `ImageAddrCall.callDeadSymB` at the interface and the
    result kind of the function of each called symbol and the site function
    `siteFn T.lookup`, and the operands pass `callParamsBT`. -/
def calleeDeadBT (T : CalleeTab) (sl : String → Option (String × Nat)) (E : Nat → List String)
    (body : Lcmd) : Bool :=
  X86Backend.ImageAddrCall.callDeadSymB T.sigOf T.outOf (siteFn T.lookup sl body) E body
    && callParamsBT T sl body

/-- **`calleeDeadBT` at the table of one linked function** is `calleeDeadB`, on a body whose
    calls name that function. -/
theorem calleeDeadBT_one {c : CalleeData} {sl : String → Option (String × Nat)}
    {E : Nat → List String} {body : Lcmd}
    (hsym : ∀ {p : Nat} {bi : Linstr} {ra : Option String} {t : String × LLabel},
      body[p]? = some bi → bi.li_i = .Lcall ra t → t.1 = c.name) :
    calleeDeadBT (CalleeTab.one c) sl E body = calleeDeadB c sl E body := by
  have hsite : ∀ (p : Nat) (bi : Linstr) (ra : Option String) (f : String) (l : LLabel),
      body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      siteFn (CalleeTab.one c).lookup sl body p = calleeSiteAt c sl body p := by
    intro p bi ra f l hb hbi
    simp only [siteFn, callSym_lookup_one hb hbi (hsym hb hbi)]
  have hsig : ∀ (p : Nat) (bi : Linstr) (ra : Option String) (f : String) (l : LLabel),
      body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      (CalleeTab.one c).sigOf f = c.sig := by
    intro p bi ra f l hb hbi
    have hf : f = c.name := hsym hb hbi
    simp [CalleeTab.sigOf, hf]
  have hout : ∀ (p : Nat) (bi : Linstr) (ra : Option String) (f : String) (l : LLabel),
      body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      (CalleeTab.one c).outOf f = match c.res with | .out _ _ => true | .reg _ => false := by
    intro p bi ra f l hb hbi
    have hf : f = c.name := hsym hb hbi
    simp [CalleeTab.outOf, hf]
  simp only [calleeDeadBT, calleeDeadB, callParamsBT_one hsym]
  cases hr : c.res with
  | reg r =>
      simp only [hr] at hout
      rw [callDeadSymB_congr (sig' := fun _ => c.sig) (out' := fun _ => false)
        (site' := calleeSiteAt c sl body) fun p bi ra f l hb hbi =>
          ⟨hsig p bi ra f l hb hbi, hout p bi ra f l hb hbi, hsite p bi ra f l hb hbi⟩]
  | out n k =>
      simp only [hr] at hout
      rw [callDeadSymB_congr (sig' := fun _ => c.sig) (out' := fun _ => true)
        (site' := calleeSiteAt c sl body) fun p bi ra f l hb hbi =>
          ⟨hsig p bi ra f l hb hbi, hout p bi ra f l hb hbi, hsite p bi ra f l hb hbi⟩]

/-- **The image of a printed body at an optional table**: the image `virtImg` without a table,
    and with one the image `ImageAddrCall.callImg` of a calling body, with the shadow
    instruction of each call on its call site at the function of its symbol
    (`siteFn T.lookup`). -/
def calleeImgT (callee : Option CalleeTab) (sl : String → Option (String × Nat))
    (body : Lcmd) : List LinstrRM :=
  match callee with
  | none => virtImg sl body
  | some T => X86Backend.ImageAddrCall.callImg sl (siteFn T.lookup sl body) body

/-- **The image of a printed body at an optional callee**: the image `virtImg` without a
    callee, and the image `ImageAddrCall.callImg` of a calling body, with the shadow
    instruction of each call on the call site `calleeSiteAt` of the callee, with one. -/
def calleeImg (callee : Option CalleeData) (sl : String → Option (String × Nat))
    (body : Lcmd) : List LinstrRM :=
  match callee with
  | none => virtImg sl body
  | some c => X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body

/-- Without a callee the image of a printed body is `virtImg`. -/
@[simp] theorem calleeImg_none (sl : String → Option (String × Nat)) (body : Lcmd) :
    calleeImg none sl body = virtImg sl body := rfl

/-- Without a table the image of a printed body is `virtImg`. -/
@[simp] theorem calleeImgT_none (sl : String → Option (String × Nat)) (body : Lcmd) :
    calleeImgT none sl body = virtImg sl body := rfl

/-- **`calleeImgT` at the table of one linked function** is the image at its call sites, on a
    body that decodes at that table. -/
theorem calleeImgT_one {c : CalleeData} {sl : String → Option (String × Nat)} {body : Lcmd}
    (hd : (decodeSites c.lookup sl body).isSome = true) :
    calleeImgT (some (CalleeTab.one c)) sl body = calleeImg (some c) sl body :=
  callImg_siteFn_lookup hd

/-- **The exported code on the common names of an optional table**: the code itself without a
    table, and with one its rewriting `LprogCallCut.commonCallsT?` onto the common names of each
    called symbol (the code itself when the rewriting refuses, which the gate excludes). -/
def calleeCodeT (callee : Option CalleeTab) (code : List LinstrRM) : List LinstrRM :=
  match callee with
  | none => code
  | some T => (LprogCallCut.commonCallsT? T.common code).getD code

/-- **The exported code on the common names of an optional callee**: the code itself
    without a callee, and its rewriting `LprogCallCut.commonCalls?` onto the argument names
    and the result name of the callee, at the shape `CalleeData.shape` of its calls, with
    one (the code itself when the rewriting refuses, which the gate `regionCoB`
    excludes). -/
def calleeCode (callee : Option CalleeData) (code : List LinstrRM) : List LinstrRM :=
  match callee with
  | none => code
  | some c => (LprogCallCut.commonCalls? c.shape c.name c.args c.resReg code).getD code

/-- Without a callee the exported code is unchanged. -/
@[simp] theorem calleeCode_none (code : List LinstrRM) : calleeCode none code = code := rfl

/-- Without a table the exported code is unchanged. -/
@[simp] theorem calleeCodeT_none (code : List LinstrRM) : calleeCodeT none code = code := rfl

/-- `calleeCodeT` at the table of one linked function is `calleeCode` at that function. -/
theorem calleeCodeT_one (c : CalleeData) (code : List LinstrRM) :
    calleeCodeT (some (CalleeTab.one c)) code = calleeCode (some c) code := by
  simp only [calleeCodeT, calleeCode, CalleeTab.common_one, LprogCallCut.commonCallsT?_one]

/-- **The array positions of the called symbols at an optional table**: the array positions
    `arrArgs` of the function of a symbol of the table, and none elsewhere. -/
def calleeAAT (callee : Option CalleeTab) (f : String) : Nat → Option Nat :=
  match callee.bind (·.lookup f) with
  | some c => c.arrArgs
  | none => fun _ => none

/-- **The array positions of the called symbols at an optional callee**: `calleeAAT` at the
    table of the callee. -/
def calleeAA (callee : Option CalleeData) (f : String) : Nat → Option Nat :=
  calleeAAT (callee.map CalleeTab.one) f

/-- **`calleeAAT` at the table of one linked function**: its array positions at its symbol, and
    none elsewhere. -/
@[simp] theorem calleeAAT_one (c : CalleeData) (f : String) :
    calleeAAT (some (CalleeTab.one c)) f = if f = c.name then c.arrArgs else fun _ => none := by
  by_cases h : f = c.name <;> simp [calleeAAT, h]

/-- Without a table no symbol has an array position. -/
@[simp] theorem calleeAAT_none (f : String) : calleeAAT none f = fun _ => none := rfl

/-- **The result lengths of the called symbols at an optional table**: the length `n` of an out
    result `.out n k` of the function of a symbol of the table, and none elsewhere. -/
def calleeAOT (callee : Option CalleeTab) (f : String) : Option Nat :=
  (callee.bind (·.lookup f)).bind fun c => match c.res with
    | .out n _ => some n
    | .reg _ => none

/-- **The result lengths of the called symbols at an optional callee**: `calleeAOT` at the
    table of the callee. -/
def calleeAO (callee : Option CalleeData) (f : String) : Option Nat :=
  calleeAOT (callee.map CalleeTab.one) f

/-- **`calleeAOT` at the table of one linked function**: the length of its out result at its
    symbol, and none elsewhere. -/
@[simp] theorem calleeAOT_one (c : CalleeData) (f : String) :
    calleeAOT (some (CalleeTab.one c)) f
      = if f = c.name then (match c.res with | .out n _ => some n | .reg _ => none)
        else none := by
  by_cases h : f = c.name <;> simp [calleeAOT, h]

/-- Without a table no symbol has a result length. -/
@[simp] theorem calleeAOT_none (f : String) : calleeAOT none f = none := rfl

/-- **The out symbols of an optional table**: `CalleeTab.outs`, and none without a table. The
    coalescing renaming `chainAliasO` at these symbols sends the destination of each of their
    calls to the root of its operand at the destination position. -/
def calleeOutsT (callee : Option CalleeTab) : List (String × Nat) :=
  match callee with
  | some T => T.outs
  | none => []

/-- **The out symbols of an optional callee**: `calleeOutsT` at the table of the callee, the
    symbol of a callee with an out result `.out n k`, paired with its destination position
    `k`, and no symbol otherwise. -/
def calleeOuts (callee : Option CalleeData) : List (String × Nat) :=
  calleeOutsT (callee.map CalleeTab.one)

/-- `calleeOutsT` at a table is the out symbols of the table. -/
@[simp] theorem calleeOutsT_some (T : CalleeTab) : calleeOutsT (some T) = T.outs := rfl

/-- Without a table there is no out symbol. -/
@[simp] theorem calleeOutsT_none : calleeOutsT none = [] := rfl

/-- **The image check of a body at an optional table**: the one image check
    `regionImgCB` of both routes, at the frame of the table below the return word, the
    symbols of the table and the wire of the image `calleeImgT` of the cell body at the table,
    and at the frame `0`, no symbol and the wire of `virtImg` without a table. Without a
    table it is `regionImgB` (`calleeImgBT_none`); at a table it gives the calling class and
    the gate of a calling body (`calleeImgBT_some`). -/
def calleeImgBT (callee : Option CalleeTab) (sl : String → Option (String × Nat))
    (R : Slots) (outs : List String) (body : Lcmd) : Bool :=
  regionImgCB ((callee.map CalleeTab.frame).getD 0) ((callee.map CalleeTab.names).getD [])
    ((calleeImgT callee sl (cellBody sl body)).map Prod.fst) sl R outs body

/-- Without a table the image check is `regionImgB`. -/
@[simp] theorem calleeImgBT_none (sl : String → Option (String × Nat)) (R : Slots)
    (outs : List String) (body : Lcmd) :
    calleeImgBT none sl R outs body = regionImgB sl R outs body :=
  regionImgCB_nil 0 sl R outs body

/-- **The image check at a table**: every call of the body names a symbol of the table, the
    body is decodable and in the class `ImageAddrCallW.printedAddrCWB` at the frame of the
    table, and its cell body passes the gate `ImageAddrCallW.imgGateCBW` at the frame marks
    with the cells. -/
theorem calleeImgBT_some {T : CalleeTab} {sl : String → Option (String × Nat)} {R : Slots}
    {outs : List String} {body : Lcmd} (h : calleeImgBT (some T) sl R outs body = true) :
    callsTabB T.names body = true ∧ X86Backend.DecodeLayout.decodableLcmd body = true
      ∧ X86Backend.ImageAddrCallW.printedAddrCWB T.frame body = true
      ∧ X86Backend.ImageAddrCallW.imgGateCBW (frameMarkC R body) sl (cellBody sl body)
        = true := by
  simp only [calleeImgBT, Option.map_some, Option.getD_some, regionImgCB,
    Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.2⟩

/-- **The image check at an optional callee**: `calleeImgBT` at the table of the callee. -/
def calleeImgB (callee : Option CalleeData) (sl : String → Option (String × Nat))
    (R : Slots) (outs : List String) (body : Lcmd) : Bool :=
  calleeImgBT (callee.map CalleeTab.one) sl R outs body

/-- Without a callee the image check is `regionImgB`. -/
@[simp] theorem calleeImgB_none (sl : String → Option (String × Nat)) (R : Slots)
    (outs : List String) (body : Lcmd) :
    calleeImgB none sl R outs body = regionImgB sl R outs body :=
  calleeImgBT_none sl R outs body

/-- The names of the register operands of a call at the array positions `a`, from the
    argument position `j`. -/
def callArrOps (a : Nat → Option Nat) : Nat → List LOperand → List String
  | _, [] => []
  | j, o :: os =>
      (match o with
        | .reg x => if (a j).isSome then [x] else []
        | _ => []) ++ callArrOps a (j + 1) os

/-- The array names the instruction `i` at position `k` of `body` needs live before it,
    from the table `A` of the names live before each position, for the array positions
    `aa` and the result lengths `ao` of the called symbols: for a jump the names at the
    position after its label, for a conditional jump those and the names at `k + 1`, for a
    shadow instruction of a call its array operands and the names at `k + 1` other than
    its destination at an array result, for every other operation the names it reads and
    the names at `k + 1` other than the name it writes, and the names at `k + 1` for every
    other instruction. When `feas` holds, a constant-taken guard
    (`ConstGuard.constTakenB`) needs only the names at the position after its label: no run
    from the entry falls through it. The webs read the table without `feas`, since their
    definite-assignment theorems are stated over every edge of `ArrWebs.webSuccs`. -/
def liveArrNeed (body : List LinstrRM) (A : Array (List String)) (k : Nat) (i : LinstrRM)
    (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) (feas : Bool := true) : List String :=
  let tgt := fun (l : LLabel) => match findLabelMem l body with
    | some p => A.getD (p + 1) []
    | none => []
  match i.1 with
  | .Lgoto (_, l) => tgt l
  | .Lcond _ l =>
      (if feas && X86Backend.ConstGuard.constTakenB body k then [] else A.getD (k + 1) [])
        ++ tgt l
  | .Lopn _ _ _ =>
      match LprogIsa.shadowCall? i.1 with
      | some (dst, f, srcs) =>
          callArrOps (aa f) 0 srcs
            ++ (A.getD (k + 1) []).filter fun r => (ao f).isNone || r != dst
      | none => arrReads i ++ (A.getD (k + 1) []).filter fun r => some r != arrWrite i
  | _ => A.getD (k + 1) []

/-- One backward pass over `body`: each position's list is extended by `liveArrNeed`. -/
def liveArrPass (body : List LinstrRM) (A : Array (List String))
    (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) (feas : Bool := true) : Array (List String) :=
  (List.range body.length).foldr (fun k A =>
    match body[k]? with
    | some i =>
        A.setIfInBounds k (A.getD k [] ++ liveArrNeed body A k i aa ao feas).eraseDups
    | none => A) A

/-- `liveArrPass` reading the instructions off the array of the body. -/
def liveArrPassImpl (body : List LinstrRM) (A : Array (List String))
    (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) (feas : Bool := true) : Array (List String) :=
  let a := body.toArray
  (List.range a.size).foldr (fun k A =>
    match a[k]? with
    | some i =>
        A.setIfInBounds k (A.getD k [] ++ liveArrNeed body A k i aa ao feas).eraseDups
    | none => A) A

/-- The pass `liveArrPass` is evaluated as `liveArrPassImpl`. -/
@[csimp] theorem liveArrPass_eq_impl : @liveArrPass = @liveArrPassImpl := by
  funext body A aa ao feas
  simp only [liveArrPass, liveArrPassImpl, List.size_toArray, List.getElem?_toArray]

/-- Backward passes until no list grows, at most `fuel` of them. -/
def liveArrIter (body : List LinstrRM) (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) (fuel : Nat) (A : Array (List String))
    (feas : Bool := true) : Array (List String) :=
  match fuel with
  | 0 => A
  | fuel + 1 =>
      let A' := liveArrPass body A aa ao feas
      if A'.toList.map List.length == A.toList.map List.length then A
      else liveArrIter body aa ao fuel A' feas

/-- The list of the table `A` at position `k`; the empty list outside the table. -/
def tabAt (A : Array (List String)) (k : Nat) : List String := A.getD k []

/-- The array names `liveArrNeed` can place in a table over `body` started from `obs`: the
    names `obs`, the names each operation reads and the array operands of each call, at the
    array positions `aa` of the called symbols. -/
def liveArrNames (body : List LinstrRM) (obs : List String)
    (aa : String → Nat → Option Nat := fun _ _ => none) : List String :=
  (obs ++ body.flatMap fun i =>
    match LprogIsa.shadowCall? i.1 with
    | some (_, f, srcs) => callArrOps (aa f) 0 srcs
    | none => arrReads i).eraseDups

/-- **The liveness table of a body**: for each position, the array names read at or after
    it before they are written, when the names `obs` are read after the body, for the
    array positions `aa` and the result lengths `ao` of the called symbols; the limit of
    the backward passes from `obs` at the end. Each pass that changes the table adds a name
    of `liveArrNames` to the list of a position before the end, so the fuel
    `(body.length + 1) * (liveArrNames body obs aa).length + 2` reaches the fixpoint. With
    `feas`, the fall-through of a constant-taken guard is no edge (`liveArrNeed`). -/
def liveArrTab (body : List LinstrRM) (obs : List String)
    (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) (feas : Bool := true) : Array (List String) :=
  liveArrIter body aa ao ((body.length + 1) * (liveArrNames body obs aa).length + 2)
    ((Array.replicate (body.length + 1) []).setIfInBounds body.length obs) feas

/-- **The liveness certificate of a body**: the table `liveArrTab` read by `tabAt`.
    `coCfgB` checks the result. -/
def liveArrCert (body : List LinstrRM) (obs : List String) : Nat → List String :=
  tabAt (liveArrTab body obs)

/-! ## 4a. The webs of the exported code -/

/-- The array names read after the exported code `r`: the names of its returned operands
    and the names `ex`. -/
def regionWebsObs (ex : List String) (r : Exported) : List String :=
  r.res.map operandName ++ ex

/-- **The webs of the exported code** `r`, at the names `ex` read after it and the array
    positions `aa` and result lengths `ao` of the called symbols: the code renamed by the
    position map `ArrWebs.webMap` of the liveness table `liveArrTab` of the code from the
    names `regionWebsObs ex r`, when the check `ArrWebs.webB` accepts that map and the
    renamed code keeps the events of the code (`ArrWebsLeak.webLeakB`); `r` otherwise. The
    second check makes the events of the webs those of the export renamed position by
    position, so that constant time of the export carries to the webs
    (`regionWebsLeak_of_regionExp`). -/
def regionWebs (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : Exported :=
  if X86Backend.ArrWebs.webB
      (X86Backend.ArrWebs.webLook (X86Backend.ArrWebs.webTab ao
        (tabAt (liveArrTab r.code (regionWebsObs ex r) aa ao false)) (regionWebsObs ex r) r.code))
      r.code (tabAt (liveArrTab r.code (regionWebsObs ex r) aa ao false)) (regionWebsObs ex r)
      aa ao
    && X86Backend.ArrWebsLeak.webLeakB
      (X86Backend.ArrWebs.webLook (X86Backend.ArrWebs.webTab ao
        (tabAt (liveArrTab r.code (regionWebsObs ex r) aa ao false)) (regionWebsObs ex r) r.code))
      ao r.code then
    { r with
      code := X86Backend.ArrWebs.webRen
        (X86Backend.ArrWebs.webLook (X86Backend.ArrWebs.webTab ao
          (tabAt (liveArrTab r.code (regionWebsObs ex r) aa ao false)) (regionWebsObs ex r) r.code))
        ao r.code }
  else r

/-- The webs keep the returned operands. -/
@[simp] theorem regionWebs_res (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    (regionWebs ex r aa ao).res = r.res := by
  unfold regionWebs
  split <;> rfl

/-- The webs keep the depth. -/
@[simp] theorem regionWebs_depth (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    (regionWebs ex r aa ao).depth = r.depth := by
  unfold regionWebs
  split <;> rfl

/-- The webs keep the length of the code. -/
@[simp] theorem regionWebs_length (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    (regionWebs ex r aa ao).code.length = r.code.length := by
  unfold regionWebs
  split
  · simp [X86Backend.ArrWebs.webRen]
  · rfl

/-- **The run of the webbed code.** At an instruction set `I` whose steps beyond `x86Isa`
    are local calls at the array positions `aa` and result lengths `ao` and stay in the
    function, a halting run of the exported code `r` from a state `s` of the function `fn`
    at position `0` to a state `t` at the end of the code is matched, with the same fuel, by
    a halting run of the code of the webs `regionWebs ex r aa ao` from `s`, into a state of
    `fn` at the end of the code with the variable registers of `t` and the arrays of `t` at
    the names `regionWebsObs ex r`. -/
theorem regionWebs_run {I : LprogIsa.Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hS : LprogCallCut.FnStable I) (ex : List String) (r : Exported) {fn : String}
    (fuel : Nat) {s t : LstateMF} (hf : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (h : I.lsemFuelMemF (singletonProgM fn r.code) fuel s = some t)
    (ht : t.prog.base.lpc = r.code.length) :
    ∃ t' : LstateMF,
      I.lsemFuelMemF (singletonProgM fn (regionWebs ex r aa ao).code) fuel s = some t'
      ∧ t'.prog.base.lpc = r.code.length ∧ t'.prog.lfn = fn
      ∧ t'.prog.base.reg.lvm = t.prog.base.reg.lvm
      ∧ ∀ x ∈ regionWebsObs ex r, t'.prog.base.larr x = t.prog.base.larr x := by
  unfold regionWebs
  split
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    obtain ⟨t', ht', hRt, -, -⟩ := X86Backend.ArrWebs.lsemFuelMemF_webs_entry hle hcl hc.1
      fuel hf hpc ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ rfl rfl h
    exact ⟨t', ht', by rw [X86Backend.ImageCoalesceCfg.coRel_lpc hRt, ht],
      (hS.lsemFuelMemF_lfn _ _ _ _ ht').trans hf, by rw [hRt.reg], fun x hx => hRt.arr x hx⟩
  · exact ⟨t, h, ht, (hS.lsemFuelMemF_lfn _ _ _ _ h).trans hf, rfl, fun _ _ => rfl⟩

/-- **The two shapes of the webs**: `regionWebs ex r aa ao` is `r`, or `r` with its code
    renamed by `ArrWebs.webRen w ao` at some position map `w`. -/
theorem regionWebs_cases (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    regionWebs ex r aa ao = r
      ∨ ∃ w, regionWebs ex r aa ao = { r with code := X86Backend.ArrWebs.webRen w ao r.code } := by
  unfold regionWebs
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-- **Facts closed under renaming hold on the webs.** A predicate on instructions that every
    renaming `renArr σ` keeps and that holds on every instruction of the code of `r` holds on
    every instruction of the code of `regionWebs ex r aa ao`. -/
theorem forall_mem_regionWebs {P : LinstrRM → Prop}
    (hP : ∀ σ i, P i → P (X86Backend.ImageCoalesceCfg.renArr σ i)) (ex : List String)
    (r : Exported) (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (h : ∀ i ∈ r.code, P i) : ∀ j ∈ (regionWebs ex r aa ao).code, P j := by
  rcases regionWebs_cases ex r aa ao with he | ⟨w, he⟩ <;> rw [he]
  · exact h
  · exact X86Backend.ArrWebs.forall_mem_webRen hP w ao h

/-- The webs keep the label positions of the code. -/
@[simp] theorem findLabelMem_regionWebs (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) (l : LLabel) :
    VIR.JasminLsemMemLoop.findLabelMem l (regionWebs ex r aa ao).code
      = VIR.JasminLsemMemLoop.findLabelMem l r.code := by
  rcases regionWebs_cases ex r aa ao with he | ⟨w, he⟩ <;> rw [he]
  exact X86Backend.ArrWebs.findLabelMem_webRen w ao l r.code

/-- The webs keep the labels the code declares. -/
@[simp] theorem labelsOf_regionWebs (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    labelsOf (regionWebs ex r aa ao).code = labelsOf r.code := by
  have key : ∀ (σ : String → String) (i : LinstrRM),
      labelOf? (X86Backend.ImageCoalesceCfg.renArr σ i).1 = labelOf? i.1 := by
    intro σ ⟨w, tag⟩
    have h := fun l => X86Backend.ImageCoalesceCfg.isLabel_renArr (σ := σ) l (w, tag)
    revert h
    generalize (X86Backend.ImageCoalesceCfg.renArr σ (w, tag)).1 = v
    cases v <;> cases w <;> simp [labelOf?, JasminLsemLabeled.isLabel]
  rcases regionWebs_cases ex r aa ao with he | ⟨w, he⟩ <;> rw [he]
  unfold labelsOf X86Backend.ArrWebs.webRen
  dsimp only
  generalize r.code = c
  induction c using List.reverseRecOn with
  | nil => rfl
  | append_singleton c a ih =>
      rw [List.mapIdx_append, List.filterMap_append, List.filterMap_append, ih]
      simp only [List.mapIdx_cons, List.mapIdx_nil, List.filterMap_cons, List.filterMap_nil, key]

/-- **The exported code of a program or its webs**: `r` is the export `r0` of `p` from the
    function `fn` with its arguments in scope, or the webs `regionWebs ex r0` of that export
    at the names `ex` read after it. -/
def RegionExp (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) (r : Exported) : Prop :=
  ∃ r0, exportR Γ.length fn p Γ.length 0 = some r0 ∧ (r = r0 ∨ r = regionWebs ex r0)

/-- The export of a program is an exported code of it. -/
theorem regionExp_of_exportR {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (ex : List String) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) : RegionExp fn p ex r :=
  ⟨r, hr, Or.inl rfl⟩

/-- The webs of the export of a program are an exported code of it. -/
theorem regionExp_webs {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (ex : List String) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) :
    RegionExp fn p ex (regionWebs ex r) :=
  ⟨r, hr, Or.inr rfl⟩

/-- An exported code returns the operands of the export. -/
theorem RegionExp.res {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r r0 : Exported}
    (h : RegionExp fn p ex r) (hr0 : exportR Γ.length fn p Γ.length 0 = some r0) :
    r.res = r0.res := by
  obtain ⟨r1, h1, rfl | rfl⟩ := h <;> (rw [h1] at hr0; cases hr0) <;> simp

/-- An exported code has the depth of the export. -/
theorem RegionExp.depth {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r r0 : Exported}
    (h : RegionExp fn p ex r) (hr0 : exportR Γ.length fn p Γ.length 0 = some r0) :
    r.depth = r0.depth := by
  obtain ⟨r1, h1, rfl | rfl⟩ := h <;> (rw [h1] at hr0; cases hr0) <;> simp

/-- An exported code has the code length of the export. -/
theorem RegionExp.length {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r r0 : Exported}
    (h : RegionExp fn p ex r) (hr0 : exportR Γ.length fn p Γ.length 0 = some r0) :
    r.code.length = r0.code.length := by
  obtain ⟨r1, h1, rfl | rfl⟩ := h <;> (rw [h1] at hr0; cases hr0) <;> simp

/-! ## 4b. The virtual body of the webs -/

/-- The entry state `entryV` shifted by the copies of the parameter registers is the entry
    state at the counter `σ.args.length`. -/
theorem shiftPc_argBind_entryV {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState} {un : String → String} {fn : String}
    (habi : AbiEntryM σ sa (entryV σ fr sa un)) :
    Ascent.IsaCall.shiftPc (argBind σ nm).length
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false }
      = { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } }, lfn := fn }, zf := false } := by
  unfold Ascent.IsaCall.shiftPc
  rw [habi.pc]
  simp [argBind, movesOf_length, argPairs]
  rfl

/-- **The steps of the webs of a region export behind the parameter copies.** Let `p` be a
    program of `RegionExportable` with the export `r`, and let the frame map `fr` satisfy
    the facts of the entry check. If `p` denotes `v` at a valuation `V` the layout `σ` reads
    off `sa`, then in the body `argBind σ nm ++ (regionWebs ex r).code ++ post` the state
    after the copies of the parameter registers steps, in at most `tripFactor fuel p` times
    the length of the code of `r` steps, to a state `t0` at the end of the webs. A state
    `t1` within the region frame of `entryV` agrees with the returned operands at `v`, and
    `t0` has the variable registers of `t1` and its arrays at the names
    `regionWebsObs ex r`. -/
theorem regionVirt_steps_webs (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ex : List String)
    (post : List LinstrRM) {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V)
    (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (hden : p.denote fuel V = some v) :
    ∃ (n : Nat) (t0 t1 : LstateMF),
      Steps x86Isa (singletonProgM fn (argBind σ nm ++ (regionWebs ex r).code ++ post)) n
        { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } }, lfn := fn }, zf := false } t0
      ∧ atPc (singletonProgM fn (argBind σ nm ++ (regionWebs ex r).code ++ post))
          (argBind σ nm ++ (regionWebs ex r).code).length t0
      ∧ ResAgrees Γ.length r.depth t1.prog.base r.res v
      ∧ RegionFrame Γ.length 0 (entryV σ fr sa un) t1.prog.base
      ∧ (∀ x, t0.prog.base.reg.lvm x = t1.prog.base.reg.lvm x)
      ∧ (∀ x ∈ regionWebsObs ex r, t0.prog.base.larr x = t1.prog.base.larr x)
      ∧ n ≤ tripFactor fuel p * r.code.length := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) :=
    entryV_abiEntry E.argF E.argG hU
  have hag0 := storeAgreesM_of_abi hV habi
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨k, t1, hrun1, hat1, hres, hfrm, hle⟩ := exportRSim_lsemFuelMemF
    (exportR_sim Γ.length fn hp) hr rfl le_rfl fuel V v hden (entryV σ fr sa un) false
    habi.pc hag0
  obtain ⟨t', hw, hwpc, hwfn, hwreg, hwarr⟩ := regionWebs_run (LprogIsa.Isa.StepLe.refl x86Isa)
    (LprogIsa.Isa.CallLocal.refl x86Isa (fun _ _ => none)) LprogCallCut.fnStable_x86Isa ex r k
    (s := { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false }) rfl habi.pc
    (by rw [X86Backend.X86Isa.x86Isa_lsemFuelMemF]; simpa using hrun1 0) hat1.2
  obtain ⟨n0, hn0, hst0, -⟩ := Ascent.IsaCall.steps_of_lsemFuelMemF x86Isa _ k _ t' hw
  have hst := Ascent.IsaCall.steps_relocate x86Isa fn post
    (Ascent.IsaCall.x86_stepRelocates fn _ _ _)
    (fun l _ _ => (findLabelMem_eq_none_iff l _).mpr (by rw [labelsOf_of_isLopn hlop]; simp))
    hst0
  rw [shiftPc_argBind_entryV habi] at hst
  exact ⟨n0, _, t1, hst, ⟨hwfn, by simp [hwpc]⟩, hres, hfrm, congrFun hwreg, hwarr,
    by omega⟩

/-- **The run of the virtual body of the webs of a region export.** Under the hypotheses of
    `regionVirt_run`, the copies of the parameter registers, the code of the webs
    `regionWebs ex r` and the register copy `ret` (when there is one), run by `lsemFuelMemF`
    from the entry state `entryV`, halt in a state `t`. A state `t1` agrees with the
    returned operands at `v`, and the state `t0` before the copy has the variable registers
    of `t1` and its arrays at the names `regionWebsObs ex r`; without a copy `t` is `t0`,
    and after the copy of `x` into `y` the cell of `y` in `t` is the cell of `x` in `t0`.
    The fuel bound is that of `regionVirt_run`. -/
theorem regionVirt_run_webs (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ex : List String)
    (ret : Option (String × String)) {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (hden : p.denote fuel V = some v) :
    ∃ (k : Nat) (t t0 t1 : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (argBind σ nm ++ (regionWebs ex r).code ++ movesOf ret.toList)) k
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some t
      ∧ ResAgrees Γ.length r.depth t1.prog.base r.res v
      ∧ (∀ x, t0.prog.base.reg.lvm x = t1.prog.base.reg.lvm x)
      ∧ (∀ x ∈ regionWebsObs ex r, t0.prog.base.larr x = t1.prog.base.larr x)
      ∧ (ret = none → t = t0)
      ∧ (∀ x y, ret = some (x, y) → t.prog.base.reg.lvm y = t0.prog.base.reg.lvm x)
      ∧ k ≤ (argBind σ nm).length + tripFactor fuel p * r.code.length + 1 := by
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := un) E.argF E.argG hS false
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨n0, t0, t1, hst, hat, hres, -, hlvm0, harr0, hle⟩ := regionVirt_steps_webs σ nm fn
    hp hr ex (movesOf ret.toList) E un hU sa V hV fuel v hden
  obtain ⟨n, t, hst2, hhalt, h1, h2, hn⟩ : ∃ (n : Nat) (t : LstateMF),
      Steps x86Isa (singletonProgM fn
          (argBind σ nm ++ (regionWebs ex r).code ++ movesOf ret.toList)) n
        { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } }, lfn := fn }, zf := false } t
      ∧ Halted (singletonProgM fn
          (argBind σ nm ++ (regionWebs ex r).code ++ movesOf ret.toList)) t
      ∧ (ret = none → t = t0)
      ∧ (∀ x y, ret = some (x, y) → t.prog.base.reg.lvm y = t0.prog.base.reg.lvm x)
      ∧ n ≤ n0 + 1 := by
    cases ret with
    | none =>
        exact ⟨n0, t0, hst, halted_of_atPc hat (by simp [singletonProgM, movesOf]),
          fun _ => rfl, fun _ _ h => (by cases h), Nat.le_succ n0⟩
    | some q =>
        obtain ⟨x, y⟩ := q
        obtain ⟨t2, hs1, hat1, -, hl⟩ := steps_movReg (dst := y) (src := x) hat (by
          show (argBind σ nm ++ (regionWebs ex r).code ++ movesOf [(x, y)])[_]? = _
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl)
        refine ⟨n0 + 1, t2, hst.trans hs1,
          halted_of_atPc hat1 (by simp [singletonProgM, movesOf, Nat.add_assoc]), nofun,
          fun x' y' h => ?_, Nat.le_refl _⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rw [hl, ite_eq_left rfl]
  have hfin := lsemFuelMemF_of_steps x86Isa _ hst2 hhalt 0
  rw [X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hfin
  refine ⟨(argBind σ nm).length + (n + 0), t, t0, t1, ?_, hres, hlvm0, harr0, h1, h2,
    by omega⟩
  rw [lsemFuelMemF_segF _ fn rfl (argBind σ nm) (entryV σ fr sa un) false (n + 0) hlop
    (fun j hj => by
      show (argBind σ nm ++ (regionWebs ex r).code ++ movesOf ret.toList)[0 + j]? = _
      rw [Nat.zero_add, List.append_assoc, List.getElem?_append_left hj]), hpre,
    Option.bind_some]
  exact hfin

/-- **The run of the virtual body of the webs of a region export with a result copy.**
    Under the hypotheses of `regionVirt_run_copy`, with the result buffer `D` among the
    names `ex`, the copies of the parameter registers, the code of the webs
    `regionWebs ex r` and the result copy `resCopyCode src D m`, run by `lsemFuelMemF` from
    the entry state `entryV`, halt in a state in which `copyName D m` holds the source value
    of the result. -/
theorem regionVirt_run_copy_webs (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ex : List String)
    {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) [.stackArr 64 m])
    (hden : p.denote fuel V = some v) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j) (hDex : D ∈ ex)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (argBind σ nm ++ (regionWebs ex r).code ++ resCopyCode src D m)) k
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some t
      ∧ t.prog.base.getArr (copyName D m) 64 m
        = some (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr 64 m])
          (t := .stackArr 64 m) .here v) := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) :=
    entryV_abiEntry E.argF E.argG hU
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := un) E.argF E.argG hS false
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨n0, t0, t1, hst, hat, hres, hfrm, -, harr0, -⟩ := regionVirt_steps_webs σ nm fn
    hp hr ex (resCopyCode src D m) E un hU sa V hV fuel v hden
  obtain ⟨op, hop, harr⟩ := hres.decodeArrM_single
  have hsrcO : src ∈ regionWebsObs ex r := by
    rw [← hsrc op hop]
    simp [regionWebsObs, hop]
  have harr' : t0.prog.base.getArr src 64 m = some (Ctxt.Var.lookup (d := jasminDialect)
      (Γ := [.stackArr 64 m]) (t := .stackArr 64 m) .here v) := by
    have h1 : t1.prog.base.getArr src 64 m = some (Ctxt.Var.lookup (d := jasminDialect)
        (Γ := [.stackArr 64 m]) (t := .stackArr 64 m) .here v) := by
      rw [← hsrc op hop]; exact harr
    unfold LstateM.getArr at h1 ⊢
    rw [harr0 src hsrcO]
    exact h1
  -- The result buffer holds its entry array.
  obtain ⟨a0, hD0⟩ : ∃ a0, t0.prog.base.getArr D 64 m = some a0 := by
    have hD1 : ∃ a0, t1.prog.base.getArr D 64 m = some a0 := by
      obtain ⟨j, a, hj, hk, rfl⟩ := hD
      rw [hfrm.2 (argName j) 64 m (fun i _ => (JasminLsemSimulation.regName_ne_argName i j).symm)
        (fun l _ => (JasminLsemExportTransfer.loopCtr_ne_argName l j).symm)]
      exact ⟨_, habi.arr j a m hj hk⟩
    obtain ⟨a0, h1⟩ := hD1
    refine ⟨a0, ?_⟩
    unfold LstateM.getArr at h1 ⊢
    rw [harr0 D (List.mem_append_right _ hDex)]
    exact h1
  obtain ⟨u, hsu, hatu, hu⟩ := steps_resCopy
    (P := singletonProgM fn (argBind σ nm ++ (regionWebs ex r).code ++ resCopyCode src D m)) hm
    (argBind σ nm ++ (regionWebs ex r).code) [] t0 (by simp [singletonProgM]) hat harr' hD0 hfr
  have hhalt := halted_of_atPc hatu (by
    simp [singletonProgM, resCopyCode, List.length_flatMap, resCopyStep]; omega)
  have hfin := lsemFuelMemF_of_steps x86Isa _ (hst.trans hsu.1) hhalt 0
  rw [X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hfin
  refine ⟨(argBind σ nm).length + (n0 + 3 * m + 0), u, ?_, hu⟩
  rw [lsemFuelMemF_segF _ fn rfl (argBind σ nm) (entryV σ fr sa un) false (n0 + 3 * m + 0) hlop
    (fun i hi => by
      show (argBind σ nm ++ (regionWebs ex r).code ++ resCopyCode src D m)[0 + i]? = _
      rw [Nat.zero_add, List.append_assoc, List.getElem?_append_left hi]), hpre,
    Option.bind_some]
  exact hfin

/-- **The run of the virtual body of an exported code** `r` of `RegionExp fn p ex r`: the
    statement of `regionVirt_run_webs` at the code of `r`. For the export itself it is
    `regionVirt_run` with `t1 = t0`. -/
theorem regionVirt_run_of_regionExp (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) (ret : Option (String × String))
    {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) ts)
    (hden : p.denote fuel V = some v) :
    ∃ (k : Nat) (t t0 t1 : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) k
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some t
      ∧ ResAgrees Γ.length r.depth t1.prog.base r.res v
      ∧ (∀ x, t0.prog.base.reg.lvm x = t1.prog.base.reg.lvm x)
      ∧ (∀ x ∈ regionWebsObs ex r, t0.prog.base.larr x = t1.prog.base.larr x)
      ∧ (ret = none → t = t0)
      ∧ (∀ x y, ret = some (x, y) → t.prog.base.reg.lvm y = t0.prog.base.reg.lvm x)
      ∧ k ≤ (argBind σ nm).length + tripFactor fuel p * r.code.length + 1 := by
  obtain ⟨r0, hr0, rfl | rfl⟩ := hr
  · obtain ⟨k, t, t0, hrun, hag, hnone, hmv, hk⟩ :=
      regionVirt_run σ nm fn hp hr0 ret E un hU sa V hV hS fuel v hden
    exact ⟨k, t, t0, t0, hrun, hag, fun _ => rfl, fun _ _ => rfl, hnone, hmv, hk⟩
  · have hobs : regionWebsObs ex (regionWebs ex r0) = regionWebsObs ex r0 := by
      simp [regionWebsObs]
    rw [hobs, regionWebs_res, regionWebs_depth, regionWebs_length]
    exact regionVirt_run_webs σ nm fn hp hr0 ex ret E un hU sa V hV hS fuel v hden

/-- **The run of the virtual body of an exported code with a result copy**: the statement
    of `regionVirt_run_copy_webs` at the code of an exported code `r` of
    `RegionExp fn p ex r`. -/
theorem regionVirt_run_copy_of_regionExp (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) [.stackArr 64 m])
    (hden : p.denote fuel V = some v) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j) (hDex : D ∈ ex)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m)) k
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some t
      ∧ t.prog.base.getArr (copyName D m) 64 m
        = some (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr 64 m])
          (t := .stackArr 64 m) .here v) := by
  obtain ⟨r0, hr0, rfl | rfl⟩ := hr
  · exact regionVirt_run_copy σ nm fn hp hr0 E un hU sa V hV hS fuel v hden hsrc hD hm hfr
  · rw [regionWebs_res] at hsrc
    exact regionVirt_run_copy_webs σ nm fn hp hr0 ex E un hU sa V hV hS fuel v hden hsrc hD
      hDex hm hfr

/-- The names an instruction reads as registers: its register sources and the indices of
    its indexed operands. -/
def regReads : LinstrR → List String
  | .Lopn ds _ ss =>
      ss.flatMap (fun | .reg n => [n] | .arrIdx _ i _ => [i] | _ => [])
        ++ ds.flatMap (fun | .arrIdx _ i _ => [i] | _ => [])
  | _ => []

/-- The register destinations of an instruction. -/
def regWrites : LinstrR → List String
  | .Lopn ds _ _ => ds.flatMap (fun | .reg d => [d] | _ => [])
  | _ => []

/-- The names a list of instructions reads as registers before it writes them. -/
def regExposed (is : List LinstrR) : List String :=
  (is.foldl (fun (acc : List String × List String) i =>
    (acc.1 ++ ((regReads i).filter fun x => !acc.2.contains x && !acc.1.contains x).eraseDups,
      acc.2 ++ regWrites i)) ([], [])).1

/-- **The image check of a virtual body under a renaming** `ps`, of the virtual body `B`
    against the printed body `body`, under the layout `σ` with register names `nm`, the
    cell arrays `R` and the observed names `outs`. The slot map is `slotArrOf σ nm` with its
    array names renamed by `renOf ps` and the arrays of `R` at length `0` (`slotArrC`), and
    the printed body is read through its cell body `ImageAddrCells.cellBody` at that slot
    map: the register allocation check `ownedCheckMC` of `B` against the image of the cell
    body, observing `outs`, the bounds invariant of `B` from the register bounds, the cell
    body in the image class, the printed class of the body with the gate of its image
    simulation (`regionImgB`), the frame check, the entry check, the check `cellNamesRB` of
    the cell names of `R`, and each array of `R` a region of its length under `unren ps`
    whose name `renOf ps` restores. At a table the image is the image `calleeImgT` of a
    calling body and the class and the gate are those of `calleeImgBT`. On a body with no
    cell access, at no cell array, the check is the check at the slot map
    `slotRen (slotArrOf σ nm) (renOf ps)` and the body (`renImageB_of_cellFreeB`). -/
def renImageB (σ : AbiLayout) (nm : String → String) (ps : List (String × String))
    (R : Slots) (outs : List String) (body : Lcmd) (B : List LinstrRM)
    (callee : Option CalleeTab := none) : Bool :=
  let sl := slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))
  ownedCheckMC outs B (calleeImgT callee sl (cellBody sl body))
    && idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B
    && physImgB sl (cellBody sl body)
    && calleeImgBT callee sl R outs body
    && frameOkB σ body && entryB σ nm body
    && cellNamesRB R σ body
    && R.all (fun p => X86Backend.DecodeGenMem.regLen (rsOf σ) (unren ps p.1) == p.2
      && renOf ps (unren ps p.1) == p.1)

/-- **On a body with no cell access, at no cell array, the image check is the check at the
    renamed slot map and the body.** -/
theorem renImageB_of_cellFreeB (σ : AbiLayout) (nm : String → String)
    (ps : List (String × String)) (outs : List String) {body : Lcmd} (B : List LinstrRM)
    (callee : Option CalleeTab) (h : cellFreeB body = true) :
    renImageB σ nm ps [] outs body B callee
      = (ownedCheckMC outs B (calleeImgT callee (slotRen (slotArrOf σ nm) (renOf ps)) body)
        && idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B
        && physImgB (slotRen (slotArrOf σ nm) (renOf ps)) body
        && calleeImgBT callee (slotRen (slotArrOf σ nm) (renOf ps)) [] outs body
        && frameOkB σ body && entryB σ nm body) := by
  unfold renImageB
  have hN : cellNamesRB [] σ body = true := rfl
  simp only [slotArrC_nil, fun sl => cellBody_of_cellFreeB sl h, hN, List.all_nil,
    Bool.and_true]

/-- The entry check is a conjunct of the image check under a renaming. -/
theorem renImageB_entryB {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    {callee : Option CalleeTab}
    (h : renImageB σ nm ps R outs body B callee = true) : entryB σ nm body = true := by
  simp only [renImageB, Bool.and_eq_true] at h
  exact h.1.1.2

/-- **The entry state of a virtual body with cells**: the entry state `entryV` at the frame
    map of the printed body with the cells of the cell arrays `R`, at the bases the names
    have under `unren ps`, with the arrays of `R` emptied. At no cell array it is the entry
    state `entryV` at the frame map of the printed body. -/
abbrev emptiedEntry (σ : AbiLayout) (ps : List (String × String)) (R : Slots) (body : Lcmd)
    (sa : AState) : LstateM :=
  emptyArrs R (entryV σ (frameC (baseR σ sa ps) R (frameE body sa)) sa (unren ps))

/-- **The entry facts of a virtual body under a renaming.** Let the virtual body `B` pass
    `renImageB` at the pairs `ps`, the cell arrays `R` and a callee `callee` against the
    printed body `body`, and let `unren ps` undo `renOf ps` on the argument names. At every
    machine state `sa` satisfying `σ.Regions`, with the frame map
    `frameC (baseR σ sa ps) R (frameE body sa)` of the printed body with the cells of `R` and
    the slot map `slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))`: the frame and slot maps
    are separated at the entry bases `baseR σ sa ps` and the frame address `frameRsp body sa`;
    the entry state `emptiedEntry` of every function name is related by
    `ImageAddrSim.ImgRel` to the address state `entryA σ sa` on the cell body; and the
    registers of `emptiedEntry` satisfy the register bounds `boundFacts σ nm`. -/
theorem renImage_entry {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    {callee : Option CalleeTab}
    (hg : renImageB σ nm ps R outs body B callee = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) :
    X86Backend.ImageAddrSim.ImgSep (frameC (baseR σ sa ps) R (frameE body sa))
        (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) (baseR σ sa ps)
        (X86Backend.DecodePrintedCFG.frameRsp body sa)
      ∧ X86Backend.ImageAddrSim.ImgRel (frameC (baseR σ sa ps) R (frameE body sa))
        (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) (baseR σ sa ps)
        (cellBody (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body)
        { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false }
        (entryA σ sa) false
      ∧ ∀ (A : String → ArrCell), ∀ f ∈ boundFacts σ nm,
          f.holds (emptiedEntry σ ps R body sa).reg.lvm A := by
  simp only [renImageB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hfr⟩, hent⟩, hN⟩, hlen⟩ := hg
  have E := entryB_spec hent sa
  have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hN
  have hgpN : ∀ r, gpOk r = true → cellIdx R r = none := by
    intro r hr
    cases hc : cellIdx R r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hents := boundFacts_entryV (nm := nm) (fr := frameC (baseR σ sa ps) R (frameE body sa))
    (un := unren ps) hreg fun b hb => by
      obtain ⟨h1, h2, h3⟩ := E.bnds b hb
      refine ⟨h1, h2, ?_⟩
      simp only [frameC, hgpN _ h1]
      exact h3
  have hun : ∀ q A n, slotArrOf σ nm q = some (A, n) → unren ps (renOf ps A) = A := by
    intro q A n h
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
    exact hU j (List.getElem?_eq_some_iff.mp hj).1
  have hS0 := imgSep_slotRen (ren := renOf ps)
    (X86Backend.ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot
      X86Backend.ImageAddrRoute.slotArrOf_not_fa) hun
  have hword : ∀ q a, frameE body sa q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o := by
    intro q a ha
    obtain ⟨hq, o, ho, rfl⟩ := X86Backend.ImageAddrFrame.frameIn_some ha
    have := X86Backend.ImageAddrFrame.frameOkB_range hfr hq ho
    exact ⟨_, this.1, this.2, rfl⟩
  have hsl : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      X86Backend.DecodeGenMem.regLen (rsOf σ) (unren ps A) = n := by
    intro q A n hq'
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hq'
    rw [hun q A0 n hq0]
    exact E.len q A0 n hq0
  have hrenS : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      renOf ps (unren ps A) = A := by
    intro q A n hq'
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hq'
    rw [hun q A0 n hq0]
  have hslC : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      cellIdx R q = none := by
    intro q A n hq'
    obtain ⟨A0, hq0, -⟩ := slotRen_some hq'
    obtain ⟨a, ha⟩ := E.slot q A0 n hq0
    exact N.body q (X86Backend.ImageAddrFrame.frameIn_some ha).1
  have hsep := X86Backend.ImageAddrRouteW.imgSep_cellsU (ren := renOf ps) E.rs hreg hS0 hword
    hsl (fun p hp => (hlen p hp).1) (fun p hp => (hlen p hp).2) hrenS N.gp hslC
  have hrel0 := imgRel_entryV (σ := σ) (nm := nm) (fr := frameC (baseR σ sa ps) R (frameE body sa))
    (sa := sa) (body := cellBody (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body)
    (fn := fn) (ren := renOf ps) (un := unren ps)
    ((E.argSrc hreg.stackIn).congr (fun x hx => by simp only [frameC, hgpN _ hx])
      (fun x => by simp only [frameC, X86Backend.ImageStraightCells.cellIdx_slotOfReg]))
    (fun _ _ hs => X86Backend.ImageStraightCells.cellBody_save hent hs) hU
  exact ⟨hsep, X86Backend.ImageStraightCells.imgRel_cellArrs (R := R) hrel0, hents⟩

/-- **The entry correspondence after the prologue.** After the prologue
    `leaFrame (-frame)` of the printed body `body` from the machine state `sa`, the machine
    state and the address state `entryA σ sa` are related by `DecodePrintedAddr.ACorr` at
    the frame address `frameRsp body sa`. -/
theorem entryA_acorr (σ : AbiLayout) (body : Lcmd) (sa : AState) :
    X86Backend.DecodePrintedAddr.ACorr (X86Backend.DecodePrintedCFG.frameRsp body sa)
      (Ascent.AddrMem.evalInstrA sa (X86Backend.PhysAbiShape.leaFrame
        (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody body).frame))))
      (entryA σ sa) := by
  obtain ⟨hl1, hm1⟩ := X86Backend.DecodePrinted.evalInstrA_leaFrame sa
    (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody body).frame))
  refine ⟨fun r hr => ?_, ?_, fun x _ => ?_⟩
  · have hl : (entryA σ sa).reg.lvm r = ⟨64, sa.regs (phys r)⟩ := by
      simp only [entryA, hr, ite_true]
    unfold LstateN.getW
    rw [hl, hl1, ite_eq_right (fun e => (X86Backend.DecodePrinted.gpFacts hr).physNe e)]
    simp
  · rw [hl1, ite_eq_left rfl]
    rfl
  · rw [hm1]
    rfl

/-- **The entry facts of a virtual body under a renaming, at no cell array, in the form of the
    image call step.** Let the virtual body `B` pass `renImageB` at the pairs `ps`, no cell
    array and a callee `callee` against the printed body `body`, and let `unren ps` undo
    `renOf ps` on the argument names. At every machine state `sa` satisfying `σ.Regions`,
    with the frame map `frameE body sa`, the slot map `sl := slotRen (slotArrOf σ nm) (renOf ps)`
    and the entry bases `baseR σ sa ps`: the maps are separated at the frame address
    `frameRsp body sa`; at every list `X` of names the entry state `entryV` at `unren ps` of
    every function name is related by `ImageAddrCall.ImgRelF` to the address state
    `entryA σ sa` on the cell body `cellBody sl body`; the machine state after the prologue
    and `entryA σ sa` are related by `ACorr`; the address state is at position `0`; and the
    registers of the entry state satisfy the register bounds `boundFacts σ nm`. These are the
    entry hypotheses of `CheckedIsaCall.haltsC_of_linkedChecksKW`. -/
theorem renImage_entry_nil {σ : AbiLayout} {nm : String → String}
    {ps : List (String × String)} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    {callee : Option CalleeTab}
    (hg : renImageB σ nm ps [] outs body B callee = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) (X : List String) :
    X86Backend.ImageAddrSim.ImgSep (frameE body sa) (slotRen (slotArrOf σ nm) (renOf ps))
        (baseR σ sa ps) (X86Backend.DecodePrintedCFG.frameRsp body sa)
      ∧ X86Backend.ImageAddrCall.ImgRelF (frameE body sa) (slotRen (slotArrOf σ nm) (renOf ps))
        (baseR σ sa ps) (cellBody (slotRen (slotArrOf σ nm) (renOf ps)) body) X
        { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
        (entryA σ sa)
      ∧ X86Backend.DecodePrintedAddr.ACorr (X86Backend.DecodePrintedCFG.frameRsp body sa)
        (Ascent.AddrMem.evalInstrA sa (X86Backend.PhysAbiShape.leaFrame
          (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody body).frame))))
        (entryA σ sa)
      ∧ (entryA σ sa).reg.lpc = 0
      ∧ ∀ f ∈ boundFacts σ nm, f.holds (entryV σ (frameE body sa) sa (unren ps)).reg.lvm
          (entryV σ (frameE body sa) sa (unren ps)).larr := by
  obtain ⟨hsep, hrel, hb⟩ := renImage_entry hg hU sa hreg fn
  rw [X86Backend.ImageAddrRouteW.slotArrC_nil] at hsep hrel
  exact ⟨hsep, X86Backend.ImageAddrCall.imgRelF_of_imgRel X hrel, entryA_acorr σ body sa, rfl,
    hb _⟩

/-- **A virtual body on the decoded bytes of its printed body, under a renaming.** Let the
    virtual body `B` pass `renImageB` at the pairs `ps` and the cell arrays `R` against the
    printed body `body`, and let `unren ps` undo `renOf ps` on the argument names. From
    every machine state `sa` satisfying `σ.Regions`, every halting run of `B` from the
    entry state `emptiedEntry` is matched by a halting run of the decoded bytes of the
    printed body from `sa`, at the end of which: the words at the entry base of each array
    parameter `A` whose renamed name is no cell array are the array of the name
    `renOf ps A` at the end of the run of `B`; each observed cell name of a cell array
    holds at the end of the run of `B` the word of the cell at the entry base of the array;
    every observed general-purpose name without a frame word holds at the end of the
    run of `B` the value of its machine register; the stack register holds its value in
    `sa`; and the memory agrees with that of `sa` at every byte outside the stack words
    `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and outside the words of each pointer region of
    `σ`, at the registers of `sa`. Some run of the address machine on `body` from
    `entryA σ sa` halts and stores to and loads from `layoutMem σ sa` only: the accesses of
    the image simulation lie in these words (`imgStores_export`), and so does the red-zone
    word (`redW_mem_frameWords`). -/
theorem renImage_bytes {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    (hg : renImageB σ nm ps R outs body B = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel
      { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some t) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (∀ q A n, slotArrOf σ nm q = some (A, n) → isArrB R (renOf ps A) = false →
        ∃ arr, t.prog.base.getArr (renOf ps A) 64 n = some arr
        ∧ ∀ j (hj : j < n),
          read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩)
      ∧ (∀ p ∈ R, ∀ j, j < p.2 → memName p.1 (8 * j) ∈ outs →
        t.prog.base.reg.lvm (memName p.1 (8 * j))
          = ⟨64, read64 sa'.mem (cellAt (abiBase (abiReg σ) sa (unren ps p.1)) j)⟩)
      ∧ (∀ r, r ∈ outs → gpOk r = true → (frameMark (frameNames body) r).isNone = true →
        t.prog.base.reg.getW r 64 = some (sa'.regs (phys r)))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  obtain ⟨hsep, hrel, hents⟩ := renImage_entry hg hU sa hreg fn
  simp only [renImageB, calleeImgT_none, calleeImgBT_none, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨hck, hidx⟩, hphys⟩, hgate⟩, hfr⟩, hent⟩, hN⟩, hlen⟩ := hg
  have E := entryB_spec hent sa
  have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hN
  have hgpN : ∀ r, gpOk r = true → cellIdx R r = none := by
    intro r hr
    cases hc : cellIdx R r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hok := runIdxOk_of_idxInvCheckB hidx fn
    { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } t rfl rfl
    (hents _) fuel hrun
  have hun : ∀ q A n, slotArrOf σ nm q = some (A, n) → unren ps (renOf ps A) = A := by
    intro q A n h
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
    exact hU j (List.getElem?_eq_some_iff.mp hj).1
  have hred : ∀ A j, cellIdx R (memName A (8 * j)) = some (A, j) →
      Ascent.AddrMem.Disjoint8 (X86Backend.DecodePrintedAddr.redW
        (X86Backend.DecodePrintedCFG.frameRsp body sa)) (cellAt (baseR σ sa ps A) j) := by
    intro A j hc
    obtain ⟨n, hn, hj, -⟩ := X86Backend.ImageStraightCells.cellIdx_spec hc
    have hk : X86Backend.DecodeGenMem.regK (rsOf σ) (unren ps A) j := by
      unfold X86Backend.DecodeGenMem.regK
      rw [(hlen _ hn).1]
      exact hj
    rw [redW_frameRsp]
    have h2 := X86Backend.ImageAddrFrame.frameOkB_red hfr
    exact X86Backend.DecodeGenNode.frameSep_of_regions E.rs hreg (unren ps A) j hk _ h2.1 h2.2
  have hck' := JasminLsemMemChecked.lsemFuelMemFk_of_runIdxOk true _ fuel _ t hrun hok
  obtain ⟨f', t', hr', hobs⟩ :=
    X86Backend.OwnedLprogTVChecked.ownedCheckMC_sound hck fn _ t rfl rfl fuel hck'
  obtain ⟨prog, sa', s', hdec, hh, hrelR, hrelC, hslots, hregs, hm', hsp, -, hkeep, fA, sA,
      zA, hrA, hacc⟩ :=
    regionImg_sim (σ := σ) (base := baseR σ sa ps) hphys hgate hsep N.gp N.body hred fn f' _ t'
      rfl hrel hr'
  have hsub := imgStores_export (nm := nm) hfr E hlen hU
  refine ⟨prog, sa', hdec, hh, fun q A n hq hA => ?_, fun p hp j hj hmem => ?_,
    fun r hR hgp hfR => ?_, hsp, fun x hxF hxR => hkeep x ?_ ?_, _, fA, sA, zA, hrA,
    hacc.mono fun _ h => ⟨fun x hx => hsub (h.1 x hx), fun x hx => hsub (h.2 x hx)⟩⟩
  · have hq' : slotArrC R (slotRen (slotArrOf σ nm) (renOf ps)) q = some (renOf ps A, n) := by
      simp [slotArrC, slotRen, hq, hA]
    obtain ⟨arr, h1, h2⟩ := hrelC q (renOf ps A) n hq'
    refine ⟨arr, ?_, fun j hj => ?_⟩
    · rw [X86Backend.ImageAddrSim.getArr_congr hobs.2.1.symm]
      exact h1
    · have h2' := h2 j hj
      have hr := X86Backend.DecodePrintedAddr.read64_eq_of_agree hm'
        (hsep.red q (renOf ps A) n j hq' hj)
      simp only [baseR, hun q A n hq] at h2' hr
      rw [← h2']
      exact hr.symm
  · have hc := X86Backend.ImageStraightCells.cellIdx_memName N.dist hp hj
    have hfc : frameC (baseR σ sa ps) R (frameE body sa) (memName p.1 (8 * j))
        = some (cellAt (baseR σ sa ps p.1) j) := by
      simp only [frameC, hc]
    have h1 := hslots (memName p.1 (8 * j)) _ hmem hfc
    rw [hobs.1 _ hmem] at h1
    rw [h1, X86Backend.DecodePrintedAddr.read64_eq_of_agree hm' (hred _ j hc)]
  · have h1 : t'.prog.base.reg.lvm r = t.prog.base.reg.lvm r := hobs.1 r hR
    have h2 : t'.prog.base.reg.lvm r = s'.reg.lvm r := hrelR r hR (by
      simp only [frameC, hgpN r hgp]
      exact frameE_none sa hfR)
    rw [← hregs r hR hgp]
    exact X86Backend.ImageStraightRoute.getW_congr 64 (h1.symm.trans h2)
  · exact fun hin => hxF (mem_wordsLocs (redW_mem_frameWords hfr sa) hin)
  · intro hs
    rcases hsub hs with h | ⟨p, hp, h⟩
    · exact hxF h
    · exact hxR p hp h

/-- **The run of the coalesced and renamed reference at an instruction set with local
    calls.** Let the code `C` behind the copies of the parameter registers be in the covered
    instruction classes and pass the coalescing check `coCfgB` of the alias map `ρ` at a
    liveness certificate `L` whose names at the entry `ρ` fixes, and at the array positions
    `aa` and the result lengths `ao` of the called symbols, and let the pairs `ps` meet the
    facts of the renaming check on the coalesced code. For an instruction set `I` whose steps
    contain those of `x86Isa` and whose further steps are local calls at `aa` and `ao`, every
    halting run of `I` on `argBind σ nm ++ C` from the entry state `entryV` at `unren ps` is
    matched by a halting run of `I` on the copies, the copies of `ps` and the coalesced code
    renamed by `renOf ps`, at the end of which the array of the name `renOf ps (ρ A)` is the
    array `A` of the first run for every observed name `A` whose alias is a name of the
    coalesced code, and the register `renOf ps y` holds the value of `y` in the first run for
    every name `y` of the coalesced code. -/
theorem regionRef_run_calls {I : LprogIsa.Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    {σ : AbiLayout} {nm : String → String} {fn : String}
    {C : List LinstrRM} {ρ : String → String} {L : Nat → List String} {obs : List String}
    {ps : List (String × String)} {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (sa : AState) (hS : ArgSrc σ nm fr sa) (hcls : ∀ i ∈ C, CtlOK i)
    (hco : coCfgB ρ C L obs aa ao = true) (hfix : ∀ r ∈ L 0, ρ r = r)
    (R : RenFacts σ nm [] (C.map (renArr ρ)) ps) (k : Nat) (t : LstateMF)
    (hrun : I.lsemFuelMemF (singletonProgM fn (argBind σ nm ++ C)) k
      { prog := { base := entryV σ fr sa (unren ps), lfn := fn }, zf := false } = some t) :
    ∃ (k' : Nat) (t' : LstateMF),
      I.lsemFuelMemF (singletonProgM fn (argBind σ nm ++ movesOf ps
          ++ (C.map (renArr ρ)).map (renRM (renOf ps)))) k'
        { prog := { base := entryV σ fr sa (unren ps), lfn := fn }, zf := false } = some t'
      ∧ (∀ A ∈ obs, ρ A ∈ loopNames (C.map (renArr ρ)) → ∀ w n,
          t'.prog.base.getArr (renOf ps (ρ A)) w n = t.prog.base.getArr A w n)
      ∧ ∀ y, y ∈ loopNames (C.map (renArr ρ)) →
          t'.prog.base.reg.lvm (renOf ps y) = t.prog.base.reg.lvm y := by
  have hlop : ∀ i ∈ argBind σ nm, IsLopn i := movesOf_isLopn _
  have hag : ∀ i ∈ argBind σ nm, ∀ (Q : JasminLsemMemLoop.LprogM) (s : LstateMF),
      I.step Q i s = x86Isa.step Q i s :=
    X86Backend.ImageAddrSrcFuel.movesOf_agree hle hcl _
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := unren ps) E.argF E.argG hS false
  have hlen : (argBind σ nm).length = σ.args.length := by
    simp [argBind, movesOf_length, argPairs]
  have hpos : ∀ j, j < (argBind σ nm).length →
      (singletonProgM fn (argBind σ nm ++ C)).body[(entryV σ fr sa (unren ps)).lpc + j]?
        = (argBind σ nm)[j]? := fun j hj => by
    show (argBind σ nm ++ C)[0 + j]? = _
    rw [Nat.zero_add, List.getElem?_append_left hj]
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le
    (JasminLsemRenameLoop.lsemFuelMemF_seg_fuel_calls hcl _ fn rfl (argBind σ nm) _
      false k t
      hlop hpos hrun)
  rw [JasminLsemMemFlagNestJoin.lsemFuelMemF_segF_agree _ fn rfl (argBind σ nm) _ false f hlop
    hag hpos, hpre, Option.bind_some] at hrun
  have hsh : shiftS (argBind σ nm).length
        { prog := { base := entryV σ fr sa (unren ps), lfn := fn }, zf := false }
      = { prog := { base := (entryV σ fr sa (unren ps)).setLpc σ.args.length, lfn := fn },
          zf := false } := by
    rw [hlen]
    exact congrArg (fun n => (⟨⟨(entryV σ fr sa (unren ps)).setLpc n, fn⟩, false⟩ : LstateMF))
      (Nat.zero_add _)
  replace hrun : I.lsemFuelMemF (singletonProgM fn (argBind σ nm ++ C)) f
      (shiftS (argBind σ nm).length
        { prog := { base := entryV σ fr sa (unren ps), lfn := fn }, zf := false })
      = some t := by
    rw [hsh]
    exact hrun
  obtain ⟨tl, htl, rfl⟩ :=
    JasminLsemMemFlagPrefix.lsemFuelMemF_of_prefix_calls hle hcl fn _ C hlop hcls f _
      t hrun
  obtain ⟨tl1, htl1, hco1, -⟩ := X86Backend.ImageCoalesceCfg.lsemFuelMemF_coalesce_calls hle hcl
    hco f
    (s' := { prog := { base := entryV σ fr sa (unren ps), lfn := fn }, zf := false }) rfl
    (Nat.zero_le _) (X86Backend.ConstGuard.guardInv_zero _ rfl)
    ⟨rfl, rfl, rfl, rfl, fun r hr => by rw [hfix r hr]⟩ rfl rfl htl
  have hcls1 : ∀ i ∈ C.map (renArr ρ), CtlOK i := fun i hi => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact ctlOK_renArr _ (hcls j hj)
  obtain ⟨t1, ht1, hs1⟩ := JasminLsemMemFlagPrefix.lsemFuelMemF_prepend_calls hle
    hcl fn
    (argBind σ nm) (C.map (renArr ρ)) hlop hcls1
    (entryV σ fr sa (unren ps)) _ false false rfl hpre f tl1 htl1
  have hst : (argBind σ nm).all noStoreB = true := by
    have := R.store
    rwa [List.append_nil] at this
  have hA : ∀ b1 z1, JasminLsemMemFlagNestJoin.runStraightF (argBind σ nm) (entryV σ fr sa (unren ps)) false
        = some (b1, z1) →
      ∀ r, r ∈ loopNames (C.map (renArr ρ)) → b1.larr (renOf ps r) = b1.larr r := by
    intro b1 z1 hb1 r _
    rw [runStraightF_larr hst hb1]
    rcases renOf_cases ps r with he | ⟨p, hp, rfl, he⟩
    · rw [he]
    · rw [he]
      show (X86Backend.ExportCertEntry.abiEntryM σ sa).larr (unren ps p.2)
        = (X86Backend.ExportCertEntry.abiEntryM σ sa).larr (unren ps p.1)
      rw [unren_target R.nd hp, unren_of_not_target fun q hq => R.ts p hp q hq]
  obtain ⟨t', ht', tl2, tl', h2, rfl, hR⟩ :=
    X86Backend.ImageAddrSrcFuel.renameLoop_sim_fuel_calls hle hcl fn
    (argBind σ nm) (C.map (renArr ρ)) ps (· ∈ loopNames (C.map (renArr ρ))) hlop hag R.ctl
    R.cond R.ren R.names R.nd R.ts R.tgt R.fresh (entryV σ fr sa (unren ps)) false rfl hA _ t1
    ht1
  rw [hs1.eq_shiftS] at h2
  have hl : tl1.prog.base.larr = tl2.prog.base.larr :=
    have := congrArg (fun s : LstateMF => s.prog.base.larr) h2
    this
  have hv : tl1.prog.base.reg.lvm = tl2.prog.base.reg.lvm :=
    have := congrArg (fun s : LstateMF => s.prog.base.reg.lvm) h2
    this
  clear h2
  refine ⟨_, _, ht', fun A hA' hN w n => ?_, fun y hy => ?_⟩
  · show tl'.prog.base.getArr (renOf ps (ρ A)) w n = tl.prog.base.getArr A w n
    unfold LstateM.getArr
    rw [hR.1.2.1 (ρ A) hN, ← hl, hco1.arr A hA']
  · show tl'.prog.base.reg.lvm (renOf ps y) = tl.prog.base.reg.lvm y
    rw [hR.1.1.2 y hy, ← hv, hco1.reg]

/-- **The run of the coalesced and renamed reference.** Let the code `C` behind the copies
    of the parameter registers be in the covered instruction classes and pass the
    coalescing check `coCfgB` of the alias map `ρ` at a liveness certificate `L` whose
    names at the entry `ρ` fixes, and let the pairs `ps` meet the facts of the renaming
    check on the coalesced code. Every halting run of `argBind σ nm ++ C` from the entry
    state `entryV` at `unren ps` is matched by a halting run of the copies, the copies of
    `ps` and the coalesced code renamed by `renOf ps`, at the end of which the array of
    the name `renOf ps (ρ A)` is the array `A` of the first run for every observed name
    `A` whose alias is a name of the coalesced code, and the register `renOf ps y` holds
    the value of `y` in the first run for every name `y` of the coalesced code. -/
theorem regionRef_run {σ : AbiLayout} {nm : String → String} {fn : String}
    {C : List LinstrRM} {ρ : String → String} {L : Nat → List String} {obs : List String}
    {ps : List (String × String)} {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (sa : AState) (hS : ArgSrc σ nm fr sa) (hcls : ∀ i ∈ C, CtlOK i)
    (hco : coCfgB ρ C L obs = true) (hfix : ∀ r ∈ L 0, ρ r = r)
    (R : RenFacts σ nm [] (C.map (renArr ρ)) ps) (k : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (argBind σ nm ++ C)) k
      { prog := { base := entryV σ fr sa (unren ps), lfn := fn }, zf := false } = some t) :
    ∃ (k' : Nat) (t' : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ movesOf ps
          ++ (C.map (renArr ρ)).map (renRM (renOf ps)))) k'
        { prog := { base := entryV σ fr sa (unren ps), lfn := fn }, zf := false } = some t'
      ∧ (∀ A ∈ obs, ρ A ∈ loopNames (C.map (renArr ρ)) → ∀ w n,
          t'.prog.base.getArr (renOf ps (ρ A)) w n = t.prog.base.getArr A w n)
      ∧ ∀ y, y ∈ loopNames (C.map (renArr ρ)) →
          t'.prog.base.reg.lvm (renOf ps y) = t.prog.base.reg.lvm y := by
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hrun ⊢
  exact regionRef_run_calls (LprogIsa.Isa.StepLe.refl x86Isa)
    (LprogIsa.Isa.CallLocal.refl x86Isa (fun _ _ => none)) E sa hS hcls hco hfix R k t hrun

/-! ## 4. The register merge -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames regDefs arrDefs
  arrUse? jumpLabel? Keeps LiveCert RelF2 lsemFuelMemF_live)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (CondOK
  findLabelMem_map_renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (flagCondCC? evalInstrPMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (evalInstrPMemL evalJumpMem
  findInstrMem LprogM LstatePM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_lpc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (findLabelMem_prefix)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (lsemFuelMemF_seg_fuel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (renRM_id)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (subB subB_spec)

-- The three lemmas on the function name and `lsemFuelMemF_length_le` are about the flag
-- machine only; their place is beside `evalInstrPMemF` in `JasminLsemMemFlagGuard`.

/-- A jump keeps the function name. -/
theorem evalJumpMem_lfn {P : LprogM} {l : LLabel} {p q : LstatePM}
    (h : evalJumpMem P l p = some q) : q.lfn = p.lfn := by
  unfold evalJumpMem at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- A step of the control-transfer arm keeps the function name. -/
theorem evalInstrPMemL_lfn {P : LprogM} {i : LinstrRM} {p q : LstatePM}
    (h : evalInstrPMemL P i p = some q) : q.lfn = p.lfn := by
  unfold evalInstrPMemL at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; rfl)
      | exact evalJumpMem_lfn h
      | (rw [Option.map_eq_some_iff] at h
         obtain ⟨b, -, rfl⟩ := h
         rfl)
      | simp at h

/-- A step of the flag machine keeps the function name. -/
theorem evalInstrPMemF_lfn {P : LprogM} {i : LinstrRM} {s t : LstateMF}
    (h : evalInstrPMemF P i s = some t) : t.prog.lfn = s.prog.lfn := by
  unfold evalInstrPMemF at h
  repeat' split at h
  all_goals
    first
      | (obtain rfl := Option.some.inj h; rfl)
      | (rw [Option.map_eq_some_iff] at h
         obtain ⟨p, hp, rfl⟩ := h
         first
           | exact evalJumpMem_lfn hp
           | rfl)
      | (simp at h; done)
      | (obtain rfl := Option.some.inj h
         rename_i p hp
         show p.lfn = s.prog.lfn
         exact evalInstrPMemL_lfn hp)

/-- A halting run of an instruction set whose steps beyond `x86Isa` are local calls, on a
    one-function program from a state of that function, ends at a position at or after the
    end of the body. -/
theorem lsemFuelMemF_length_le_calls {I : LprogIsa.Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hcl : I.CallLocal x86Isa aa ao) {fn : String}
    {B : List LinstrRM} :
    ∀ (fuel : Nat) {s t : LstateMF}, s.prog.lfn = fn →
      I.lsemFuelMemF (singletonProgM fn B) fuel s = some t → B.length ≤ t.prog.base.lpc := by
  have hhalt : ∀ {s : LstateMF}, s.prog.lfn = fn →
      findInstrMem (singletonProgM fn B) s.prog = none → B.length ≤ s.prog.base.lpc := by
    intro s hf hn
    unfold findInstrMem at hn
    rw [ite_eq_left (show s.prog.lfn = (singletonProgM fn B).lfn from hf)] at hn
    exact List.getElem?_eq_none_iff.mp hn
  have hlfn : ∀ {P : LprogM} {i : LinstrRM} {s u : LstateMF}, I.step P i s = some u →
      u.prog.lfn = s.prog.lfn := by
    intro P i s u hu
    rcases hcl P i s u hu with hx | ⟨_, _, _, _, -, rfl, -⟩
    · exact evalInstrPMemF_lfn hx
    · exact LprogIsa.lfn_retRes _ _ _
  intro fuel
  induction fuel with
  | zero =>
      intro s t hf h
      unfold LprogIsa.Isa.lsemFuelMemF at h
      split at h
      · next hn =>
        obtain rfl := Option.some.inj h
        exact hhalt hf hn
      · cases h
  | succ n ih =>
      intro s t hf h
      unfold LprogIsa.Isa.lsemFuelMemF at h
      split at h
      · next hn =>
        obtain rfl := Option.some.inj h
        exact hhalt hf hn
      · split at h
        · next u hu => exact ih ((hlfn hu).trans hf) h
        · cases h

/-- A halting run of a one-function program from a state of that function ends at a
    position at or after the end of the body. -/
theorem lsemFuelMemF_length_le {fn : String} {B : List LinstrRM} :
    ∀ (fuel : Nat) {s t : LstateMF}, s.prog.lfn = fn →
      lsemFuelMemF (singletonProgM fn B) fuel s = some t → B.length ≤ t.prog.base.lpc := by
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF]
  exact lsemFuelMemF_length_le_calls (LprogIsa.Isa.CallLocal.refl x86Isa (fun _ _ => none))

/-- The conditionals of `i` read the zero flag and `i` reads no implicit register, as a
    Boolean. -/
def condOKB (i : LinstrRM) : Bool :=
  (match i.1 with
    | .Lcond _ _ => (flagCondCC? i).isSome
    | _ => true) && mulxFree i

theorem condOKB_spec {i : LinstrRM} (h : condOKB i = true) : CondOK i := by
  simp only [condOKB, Bool.and_eq_true] at h
  refine ⟨fun c l hi hn => ?_, h.2⟩
  have h1 := h.1
  rw [hi] at h1
  simp only [hn, Option.isSome_none] at h1
  cases h1

/-- The write condition `Keeps τ (· ∈ N) (· ∈ M) ds` as a Boolean: every name of `M` is the
    single name of `ds`, or it is in `N` and its image under `τ` differs from the image of
    every name of `ds`. -/
def keepsB (τ : String → String) (N M ds : List String) : Bool :=
  M.all fun r => ds == [r] || (N.contains r && ds.all fun d => τ r != τ d)

theorem keepsB_spec {τ : String → String} {N M ds : List String}
    (h : keepsB τ N M ds = true) : Keeps τ (· ∈ N) (· ∈ M) ds := by
  intro r hr
  have := List.all_eq_true.mp h r hr
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.contains_eq_mem,
    decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at this
  exact this

/-- The register names of a liveness table `L` at position `k` of a body of length `n`: the
    empty name and the names of `L` at `k`, at `n` for every position after the body. -/
def liveAt (L : Nat → List String) (n k : Nat) : List String := "" :: L (min k n)

/-- The check of the operands of a call from the argument position `j`, for the array
    positions `a`: an array operand that is a register names an array of `AN`. -/
def regCallOpsB (a : Nat → Option Nat) (AN : List String) : Nat → List LOperand → Bool
  | _, [] => true
  | j, o :: os =>
      (match a j, o with
        | some _, .reg x => AN.contains x
        | _, _ => true)
      && regCallOpsB a AN (j + 1) os

theorem regCallOpsB_spec {a : Nat → Option Nat} {AN : List String} :
    ∀ (j : Nat) (srcs : List LOperand), regCallOpsB a AN j srcs = true →
      ∀ (m n : Nat) (A : String), a (j + m) = some n → srcs[m]? = some (.reg A) → A ∈ AN
  | _, [], _, _, _, _, _, h2 => by simp at h2
  | j, o :: os, h, m, n, A, h1, h2 => by
      simp only [regCallOpsB, Bool.and_eq_true] at h
      cases m with
      | zero =>
          obtain rfl : o = .reg A := by simpa using h2
          have h0 := h.1
          rw [Nat.add_zero] at h1
          simp only [h1] at h0
          simpa using h0
      | succ m =>
          exact regCallOpsB_spec (j + 1) os h.2 m n A (by rw [← h1]; congr 1; omega)
            (by simpa using h2)

/-- **The check of a call** at position `k` for a merge `τ` of register names, at the array
    positions `aa` and the result lengths `ao` of the called symbols: at a shadow
    instruction `callShadow dst f srcs`, the operands pass `regCallOpsB` at the array names
    `AN`, and at a symbol with a word-array result the destination is live before the call
    and the names `AN` pass `keepsB` at the destination. Every other instruction passes. -/
def regCallB (τ : String → String) (Lr : Nat → List String) (AN : List String)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) (k : Nat) (i : LinstrRM) :
    Bool :=
  match LprogIsa.shadowCall? i.1 with
  | some (dst, f, srcs) =>
      regCallOpsB (aa f) AN 0 srcs
        && match ao f with
          | some _ => (Lr k).contains dst && keepsB τ AN AN [dst]
          | none => true
  | none => true

theorem regCallB_spec {τ : String → String} {Lr : Nat → List String} {AN : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {k : Nat} {i : LinstrRM}
    (h : regCallB τ Lr AN aa ao k i = true) {dst f : String} {srcs : List LOperand}
    (hi : i.1 = LprogIsa.callShadow dst f srcs) :
    (∀ (j n : Nat) (A : String), aa f j = some n → srcs[j]? = some (.reg A) → A ∈ AN)
      ∧ ∀ n, ao f = some n → dst ∈ Lr k ∧ Keeps τ (· ∈ AN) (· ∈ AN) [dst] := by
  simp only [regCallB, hi, LprogIsa.shadowCall?_callShadow, Bool.and_eq_true] at h
  refine ⟨fun j n A h1 h2 => regCallOpsB_spec 0 srcs h.1 j n A (by simpa using h1) h2,
    fun n hn => ?_⟩
  have h2 := h.2
  simp only [hn, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h2
  exact ⟨h2.1, keepsB_spec h2.2⟩

/-- **The check of the instruction `i` at position `k`** for a merge `τ` of register names,
    against the register names `Lr` live before each position and the array names `AN`,
    at the array positions `aa` and the result lengths `ao` of the called symbols: `i`
    passes `condOKB`; the names it reads are live before it and the array it reads is in
    `AN`; the names live after it and the names `AN` pass `keepsB` at the register names
    and at the array names it writes; the names live after the label of a jump are live at
    the jump; and `i` passes the call check `regCallB`. -/
def regCoInstrB (τ : String → String) (body : List LinstrRM) (Lr : Nat → List String)
    (AN : List String) (k : Nat) (i : LinstrRM) (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : Bool :=
  (condOKB i && subB (useNames i.1) (Lr k) && (arrUse? i).all AN.contains
    && keepsB τ (Lr k) (Lr (k + 1)) (regDefs i) && keepsB τ AN AN (arrDefs i)
    && match jumpLabel? i.1 with
      | some l =>
          match findLabelMem l body with
          | some pc => subB (Lr (pc + 1)) (Lr k)
          | none => true
      | none => true)
    && regCallB τ Lr AN aa ao k i

/-- **The check of a merge of register names** `τ` on the code `C` behind the prefix `pre`,
    against a liveness certificate `L` (for each position of `pre ++ C`, a list containing
    the register names live before it) and the array names `AN`, at the array positions
    `aa` and the result lengths `ao` of the called symbols: `τ` fixes the empty name, the
    names of `AN` and the names live at the first position of `C`, and the instruction at
    every position of `C` passes `regCoInstrB`. Two names with one image are accepted when
    neither is live across a write of the other. The certificate is not trusted. -/
def regCoB (τ : String → String) (pre C : List LinstrRM) (L : Nat → List String)
    (AN : List String) (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : Bool :=
  τ "" == "" && AN.all (fun a => τ a == a)
    && (liveAt L (pre ++ C).length pre.length).all (fun r => τ r == r)
    && (List.range C.length).all fun j =>
      match C[j]? with
      | some i =>
          regCoInstrB τ (pre ++ C) (liveAt L (pre ++ C).length) AN (pre.length + j) i aa ao
      | none => true

/-- The instruction at a position of `C` behind the prefix passes `regCoInstrB`. -/
theorem regCoB_instr {τ : String → String} {pre C : List LinstrRM} {L : Nat → List String}
    {AN : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : regCoB τ pre C L AN aa ao = true) {k : Nat} {i : LinstrRM} (hk : pre.length ≤ k)
    (hi : (pre ++ C)[k]? = some i) :
    regCoInstrB τ (pre ++ C) (liveAt L (pre ++ C).length) AN k i aa ao = true := by
  simp only [regCoB, Bool.and_eq_true] at h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hi
  have hj : j < C.length := (List.getElem?_eq_some_iff.mp hi).1
  have := List.all_eq_true.mp h.2 j (List.mem_range.mpr hj)
  rw [hi] at this
  exact this

/-- **A checked merge is a liveness certificate.** For a prefix `pre` of operations and code
    `C` accepted by `regCoB τ pre C L AN`, the program `pre ++ C` and the program
    `pre ++ C.map (renRM τ)` have the certificate `LiveCert` of `τ` from the first position
    of `C`, at the register names `liveAt L` and the array names `AN`. -/
theorem liveCert_of_regCoB {τ : String → String} {pre C : List LinstrRM}
    {L : Nat → List String} {AN : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (fn : String) (hpre : ∀ i ∈ pre, IsLopn i)
    (h : regCoB τ pre C L AN aa ao = true) :
    LiveCert τ pre.length (singletonProgM fn (pre ++ C))
      (singletonProgM fn (pre ++ C.map (renRM τ)))
      (fun k r => r ∈ liveAt L (pre ++ C).length k) (fun _ r => r ∈ AN) := by
  have hins := @regCoB_instr _ _ _ _ _ _ _ h
  simp only [regCoB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hfix, -⟩, -⟩, -⟩ := h
  have hI : ∀ k i, pre.length ≤ k → (pre ++ C)[k]? = some i →
      condOKB i = true ∧ subB (useNames i.1) (liveAt L (pre ++ C).length k) = true
        ∧ (arrUse? i).all AN.contains = true
        ∧ keepsB τ (liveAt L (pre ++ C).length k) (liveAt L (pre ++ C).length (k + 1))
          (regDefs i) = true
        ∧ keepsB τ AN AN (arrDefs i) = true
        ∧ (match jumpLabel? i.1 with
          | some l =>
              match findLabelMem l (pre ++ C) with
              | some pc => subB (liveAt L (pre ++ C).length (pc + 1))
                  (liveAt L (pre ++ C).length k)
              | none => true
          | none => true) = true := by
    intro k i hk hi
    have := hins hk hi
    unfold regCoInstrB at this
    simpa only [Bool.and_eq_true, and_assoc] using (Bool.and_eq_true_iff.mp this).1
  exact
    { lfn := rfl
      lbl := fun l => by
        show findLabelMem l (pre ++ C.map (renRM τ)) = findLabelMem l (pre ++ C)
        rw [findLabelMem_prefix l _ _ hpre, findLabelMem_prefix l _ _ hpre,
          findLabelMem_map_renRM]
      body := fun k hk => by
        show (pre ++ C.map (renRM τ))[k]? = ((pre ++ C)[k]?).map (renRM τ)
        rw [List.getElem?_append_right hk, List.getElem?_append_right hk, List.getElem?_map]
      cond := fun k i hk hi => condOKB_spec (hI k i hk hi).1
      jmp := fun l pc hl => by
        have hl' : findLabelMem l (pre ++ C) = some pc := hl
        rw [findLabelMem_prefix l _ _ hpre] at hl'
        obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hl'
        omega
      emp := fun k => List.mem_cons_self
      fix := hfix
      uses := fun k i hk hi n hn => subB_spec (hI k i hk hi).2.1 n hn
      arrUse := fun k i hk hi b hb => by
        have := (hI k i hk hi).2.2.1
        rw [hb] at this
        simpa using this
      fallR := fun k i hk hi => keepsB_spec (hI k i hk hi).2.2.2.1
      fallA := fun k i hk hi => keepsB_spec (hI k i hk hi).2.2.2.2.1
      jumpR := fun k i l pc hk hi hl hf r hr => by
        have := (hI k i hk hi).2.2.2.2.2
        have hf' : findLabelMem l (pre ++ C) = some pc := hf
        simp only [hl, hf'] at this
        exact subB_spec this r hr
      jumpA := fun _ _ _ _ _ _ _ _ _ hr => hr }

/-- **A checked merge meets the call condition.** For a prefix `pre` of operations and code
    `C` accepted by `regCoB τ pre C L AN aa ao`, the program `pre ++ C` meets the call
    condition `LiveCalls` of `τ` from the first position of `C`, at the register names
    `liveAt L`, the array names `AN`, the array positions `aa` and the result lengths
    `ao`. -/
theorem liveCalls_of_regCoB {τ : String → String} {pre C : List LinstrRM}
    {L : Nat → List String} {AN : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (fn : String) (h : regCoB τ pre C L AN aa ao = true) :
    JasminLsemExportRegAlloc.LiveCalls τ pre.length (singletonProgM fn (pre ++ C))
      (fun k r => r ∈ liveAt L (pre ++ C).length k) (fun _ r => r ∈ AN) aa ao := by
  intro k i dst f srcs hk hi hsh
  have := regCoB_instr h hk hi
  unfold regCoInstrB at this
  exact regCallB_spec (Bool.and_eq_true_iff.mp this).2 hsh

/-- **The run of merged code at an instruction set with local calls.** The statement of
    `regCo_run` for the runs of an instruction set `I` whose steps contain those of `x86Isa`
    and whose further steps are local calls at the array positions `aa` and the result
    lengths `ao` checked by `regCoB`, for a prefix `pre` at whose instructions the step of
    `I` is the step of `x86Isa`. -/
theorem regCo_run_calls {I : LprogIsa.Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa aa ao) {τ : String → String} {pre C : List LinstrRM}
    {L : Nat → List String} {AN : List String} {fn : String} (hpre : ∀ i ∈ pre, IsLopn i)
    (hag : ∀ i ∈ pre, ∀ (Q : LprogM) (s : LstateMF), I.step Q i s = x86Isa.step Q i s)
    (h : regCoB τ pre C L AN aa ao = true) (b0 : LstateM) (hb0 : b0.lpc = 0) (zf : Bool)
    (k : Nat)
    (t : LstateMF)
    (hrun : I.lsemFuelMemF (singletonProgM fn (pre ++ C)) k
      { prog := { base := b0, lfn := fn }, zf := zf } = some t) :
    ∃ t' : LstateMF,
      I.lsemFuelMemF (singletonProgM fn (pre ++ C.map (renRM τ))) k
        { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ (∀ y ∈ L (pre ++ C).length,
        t'.prog.base.reg.lvm (τ y) = t.prog.base.reg.lvm y)
      ∧ ∀ a ∈ AN, t'.prog.base.larr a = t.prog.base.larr a := by
  have hC := liveCert_of_regCoB fn hpre h
  have hK := liveCalls_of_regCoB fn h
  simp only [regCoB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hAN⟩, hent⟩, -⟩ := h
  have hpos : ∀ (X : List LinstrRM) j, j < pre.length →
      (singletonProgM fn (pre ++ X)).body[b0.lpc + j]? = pre[j]? := fun X j hj => by
    show (pre ++ X)[b0.lpc + j]? = _
    rw [hb0, Nat.zero_add, List.getElem?_append_left hj]
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le
    (JasminLsemRenameLoop.lsemFuelMemF_seg_fuel_calls hcl _ fn rfl pre b0 zf k t hpre
      (hpos C) hrun)
  rw [JasminLsemMemFlagNestJoin.lsemFuelMemF_segF_agree _ fn rfl pre b0 zf f hpre hag
    (hpos C)] at hrun
  rw [JasminLsemMemFlagNestJoin.lsemFuelMemF_segF_agree _ fn rfl pre b0 zf f hpre hag
    (hpos _)]
  cases hrs : runStraightF pre b0 zf with
  | none => simp [hrs] at hrun
  | some bz =>
      rw [hrs, Option.bind_some] at hrun
      rw [Option.bind_some]
      have hpc : bz.1.lpc = pre.length := by
        rw [runStraightF_lpc pre b0 zf bz.1 bz.2 hrs, hb0, Nat.zero_add]
      have hR : RelF2 τ (fun r => r ∈ liveAt L (pre ++ C).length bz.1.lpc) (fun r => r ∈ AN)
          { prog := { base := bz.1, lfn := fn }, zf := bz.2 }
          { prog := { base := bz.1, lfn := fn }, zf := bz.2 } := by
        rw [hpc]
        refine ⟨⟨⟨rfl, fun r hr => ?_⟩, fun r hr => ?_, rfl⟩, rfl, rfl, rfl, rfl⟩
        · rw [show τ r = r by simpa using List.all_eq_true.mp hent r hr]
        · rw [show τ r = r by simpa using List.all_eq_true.mp hAN r hr]
      obtain ⟨t', ht', hRt⟩ := JasminLsemExportRegAlloc.lsemFuelMemF_live_calls hle
        hcl hC hK f hR (Nat.le_of_eq hpc.symm) hrun
      have hfin : (pre ++ C).length ≤ t.prog.base.lpc :=
        lsemFuelMemF_length_le_calls hcl (fn := fn) (B := pre ++ C) f (Eq.refl fn) hrun
      refine ⟨t', ht', fun y hy => hRt.1.1.2 y ?_, fun a ha => ?_⟩
      · show y ∈ liveAt L (pre ++ C).length t.prog.base.lpc
        rw [liveAt, Nat.min_eq_right hfin]
        exact List.mem_cons_of_mem _ hy
      · have := hRt.1.2.1 a ha
        rwa [show τ a = a by simpa using List.all_eq_true.mp hAN a ha] at this

/-- **The run of merged code.** For a prefix `pre` of operations and code `C` accepted by
    `regCoB τ pre C L AN`, every halting run of `pre ++ C` from a state at position `0` is
    matched, with the same fuel, by a halting run of `pre ++ C.map (renRM τ)` from that
    state, at the end of which the register `τ y` holds the value of `y` in the first run
    for every name `y` the certificate gives the end of the body, and every array of `AN`
    is the array of the first run. -/
theorem regCo_run {τ : String → String} {pre C : List LinstrRM} {L : Nat → List String}
    {AN : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    {fn : String} (hpre : ∀ i ∈ pre, IsLopn i)
    (h : regCoB τ pre C L AN aa ao = true) (b0 : LstateM) (hb0 : b0.lpc = 0) (zf : Bool) (k : Nat)
    (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (pre ++ C)) k
      { prog := { base := b0, lfn := fn }, zf := zf } = some t) :
    ∃ t' : LstateMF,
      lsemFuelMemF (singletonProgM fn (pre ++ C.map (renRM τ))) k
        { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ (∀ y ∈ L (pre ++ C).length,
        t'.prog.base.reg.lvm (τ y) = t.prog.base.reg.lvm y)
      ∧ ∀ a ∈ AN, t'.prog.base.larr a = t.prog.base.larr a := by
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hrun ⊢
  exact regCo_run_calls (LprogIsa.Isa.StepLe.refl x86Isa)
    (LprogIsa.Isa.CallLocal.refl x86Isa aa ao) hpre (fun _ _ _ _ => rfl) h b0 hb0
    zf k t hrun

/-- The register names the instruction `i` at position `k` of `body` needs live before it,
    from the table `A` of the names live before each position: for a jump the names at the
    position after its label, for a conditional jump those and the names at `k + 1`, for an
    operation the names it reads and the names at `k + 1` it does not write, and the names
    at `k + 1` for every other instruction. -/
def liveRegNeed (body : List LinstrRM) (A : Array (List String)) (k : Nat) (i : LinstrRM) :
    List String :=
  let tgt := fun (l : LLabel) => match findLabelMem l body with
    | some p => A.getD (p + 1) []
    | none => []
  match i.1 with
  | .Lgoto (_, l) => tgt l
  | .Lcond _ l => A.getD (k + 1) [] ++ tgt l
  | .Lopn _ _ _ => useNames i.1 ++ (A.getD (k + 1) []).filter fun r => !(regDefs i).contains r
  | _ => A.getD (k + 1) []

/-- One backward pass over `body`: each position's list is extended by `liveRegNeed`. -/
def liveRegPass (body : List LinstrRM) (A : Array (List String)) : Array (List String) :=
  (List.range body.length).foldr (fun k A =>
    match body[k]? with
    | some i => A.setIfInBounds k (A.getD k [] ++ liveRegNeed body A k i).eraseDups
    | none => A) A

/-- `liveRegPass` reading the instructions off the array of the body. -/
def liveRegPassImpl (body : List LinstrRM) (A : Array (List String)) : Array (List String) :=
  let a := body.toArray
  (List.range a.size).foldr (fun k A =>
    match a[k]? with
    | some i => A.setIfInBounds k (A.getD k [] ++ liveRegNeed body A k i).eraseDups
    | none => A) A

/-- The pass `liveRegPass` is evaluated as `liveRegPassImpl`. -/
@[csimp] theorem liveRegPass_eq_impl : @liveRegPass = @liveRegPassImpl := by
  funext body A
  simp only [liveRegPass, liveRegPassImpl, List.size_toArray, List.getElem?_toArray]

/-- Backward passes until no list grows, at most `fuel` of them. -/
def liveRegIter (body : List LinstrRM) : Nat → Array (List String) → Array (List String)
  | 0, A => A
  | fuel + 1, A =>
      let A' := liveRegPass body A
      if A'.toList.map List.length == A.toList.map List.length then A
      else liveRegIter body fuel A'

/-- **The register liveness table of a body**: for each position, the names read as
    registers at or after it before they are written, when the names `outs` are read after
    the body; the limit of the backward passes from `outs` at the end. `regCoB` checks the
    table read by `tabAt`. -/
def liveRegTab (body : List LinstrRM) (outs : List String) : Array (List String) :=
  liveRegIter body (body.length + 2)
    ((Array.replicate (body.length + 1) []).setIfInBounds body.length outs)

/-- The array names the instructions of `C` read or write. -/
def arrNames (C : List LinstrRM) : List String :=
  (C.flatMap fun i => (arrUse? i).toList ++ arrDefs i).eraseDups

/-- The array names of the calls of `C`, at the array positions `aa` and the result lengths
    `ao` of the called symbols: the register operands at the array positions, and the
    destination of a call with a word-array result. -/
def callArrNames (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (C : List LinstrRM) : List String :=
  (C.flatMap fun i => match LprogIsa.shadowCall? i.1 with
    | some (dst, f, srcs) =>
        ((List.range srcs.length).filterMap fun j => match aa f j, srcs[j]? with
          | some _, some (.reg A) => some A
          | _, _ => none)
        ++ (match ao f with
          | some _ => [dst]
          | none => [])
    | none => []).eraseDups

/-- The renaming of no pair leaves a body unchanged. -/
theorem map_renRM_renOf_nil (C : List LinstrRM) : C.map (renRM (renOf [])) = C := by
  have : renOf [] = id := rfl
  rw [this]
  exact (List.map_congr_left fun i _ => renRM_id i).trans (List.map_id C)

/-! ## 5. The array self-moves of a reference -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (evalInstrPMemF_live)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (cmpArgs? movRegArgs?
  aluFlagOp? withALUFlags carryArgs? wideArgs? lsemFuelMemF_halt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
  (stackSet_stackGet_self)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (evalInstrPMemF_movReg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (evalInstrPMemF_congr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel findLabel_sound isLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (NextPc
  evalInstrPMemF_next)

/-- The pair `i`, `j` is an array move of an array onto itself: the load
    `LOADIDX t, a[z]` followed by the store `STOREIDX a, a[z], t` of the loaded word at the
    same index, scale and shape. -/
def selfMoveB (i j : LinstrRM) : Bool :=
  match i, j with
  | (.Lopn [.reg t] o [.arrIdx a z s], .load w n),
    (.Lopn [.reg a'] o' [.arrIdx a'' z' s', .reg t'], .store w' n') =>
      o == "LOADIDX" && o' == "STOREIDX" && a == a' && a == a'' && z == z' && s == s'
        && t == t' && w == w' && n == n'
  | _, _ => false

/-- A pair of `selfMoveB` is a load and a store of the stated forms. -/
theorem selfMoveB_shape {i j : LinstrRM} (h : selfMoveB i j = true) :
    ∃ t a z sc w n, i = (.Lopn [.reg t] "LOADIDX" [.arrIdx a z sc], .load w n)
      ∧ j = (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t], .store w n) := by
  unfold selfMoveB at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
    exact ⟨_, _, _, _, _, _, rfl, rfl⟩
  · cases h

/-- **The two steps of an array self-move.** The load `LOADIDX t, a[z]` followed by the
    store `STOREIDX a, a[z], t`, with the index register `z` other than `t`, leaves every
    array, the word memory, every register other than `t`, the function name and the flags
    unchanged, and advances the program counter by two. -/
theorem selfMove_steps {P : LprogM} (t a z : String) (sc w n : Nat) (hzt : z ≠ t)
    {s s1 s2 : LstateMF}
    (h1 : evalInstrPMemF P (.Lopn [.reg t] "LOADIDX" [.arrIdx a z sc], .load w n) s = some s1)
    (h2 : evalInstrPMemF P (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t], .store w n) s1
      = some s2) :
    s2.prog.base.larr = s.prog.base.larr ∧ s2.prog.base.lmem = s.prog.base.lmem
      ∧ (∀ x, x ≠ t → s2.prog.base.reg.lvm x = s.prog.base.reg.lvm x)
      ∧ s2.prog.base.lpc = s.prog.base.lpc + 2 ∧ s2.prog.lfn = s.prog.lfn ∧ s2.zf = s.zf
      ∧ s2.prog.base.cf = s.prog.base.cf ∧ s2.prog.base.of = s.prog.base.of := by
  have c2 : cmpArgs? (LinstrR.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t],
      MemTag.store w n) = none := by
    unfold cmpArgs?; exact ite_eq_right (by decide)
  have a2 : aluFlagOp? (LinstrR.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t],
      MemTag.store w n) = none := by
    unfold aluFlagOp?
    simp only
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide)]
  simp only [evalInstrPMemF, cmpArgs?, movRegArgs?, flagCondCC?, evalInstrPMemL, lsemStepMem,
    loadStruct?, ite_true, withALUFlags, aluFlagOp?] at h1
  cases hA : s.prog.base.getArr a w n with
  | none => simp [hA, carryArgs?, wideArgs?] at h1
  | some arr =>
    cases hZ : s.prog.base.reg.getW z 64 with
    | none => simp [hA, hZ, carryArgs?, wideArgs?] at h1
    | some vi =>
      simp only [hA, hZ, Option.map_some] at h1
      obtain rfl := Option.some.inj h1
      have hA' : (s.prog.base.setReg t (stackGet arr vi.toNat)).nextPc.getArr a w n
          = some arr := hA
      have hl : (s.prog.base.setReg t (stackGet arr vi.toNat)).nextPc.reg.lvm z
          = s.prog.base.reg.lvm z := by
        simp [LstateM.nextPc, LstateM.setReg, hzt]
      have hZ' : (s.prog.base.setReg t (stackGet arr vi.toNat)).nextPc.reg.getW z 64
          = some vi := by
        unfold LstateN.getW at hZ ⊢
        rw [hl]
        exact hZ
      have hT : (s.prog.base.setReg t (stackGet arr vi.toNat)).nextPc.reg.getW t w
          = some (stackGet arr vi.toNat) :=
        LstateN.getW_setReg_same s.prog.base.reg t _
      simp only [evalInstrPMemF, c2, movRegArgs?, flagCondCC?, evalInstrPMemL, lsemStepMem,
        storeStruct?, ite_true, withALUFlags, a2, hA', hZ', hT, Option.map_some,
        stackSet_stackGet_self] at h2
      obtain rfl := Option.some.inj h2
      refine ⟨?_, rfl, fun x hx => ?_, ?_, rfl, rfl, rfl, rfl⟩
      · funext r
        simp only [LstateM.nextPc, LstateM.setArr, LstateM.setReg]
        split
        · next hr => rw [hr, larr_eq_of_getArr hA]
        · rfl
      · simp [LstateM.nextPc, LstateM.setArr, LstateM.setReg, hx]
      · simp [LstateM.nextPc, LstateM.setArr, LstateM.setReg, LstateM.lpc]

/-- The replacement of an instruction of an array self-move: the copy `MOV:64 z, z` of the
    index register `z` of its indexed operand onto itself; every other instruction is
    kept. -/
def selfNopI (i : LinstrRM) : LinstrRM :=
  match i.1 with
  | .Lopn _ _ (.arrIdx _ z _ :: _) => (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none)
  | _ => i

/-- The scratch register `t` of the load `i` at position `k` is other than its index
    register, and every name of the table `Lr` at position `k + 2` is other than `t` and a
    name of `Lr` at position `k`. -/
def selfDeadB (Lr : Nat → List String) (k : Nat) (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn [.reg t] _ [.arrIdx _ z _] =>
      z != t && (Lr (k + 2)).all fun x => x != t && (Lr k).contains x
  | _ => false

/-- Position `k ≥ k0` of `B` is the load of an array self-move `selfMoveB` whose scratch
    register passes `selfDeadB` at the table `Lr`. -/
def selfPairB (k0 : Nat) (Lr : Nat → List String) (B : List LinstrRM) (k : Nat) : Bool :=
  decide (k0 ≤ k) && match B[k]?, B[k + 1]? with
    | some i, some j => selfMoveB i j && selfDeadB Lr k i
    | _, _ => false

/-- **The code without the effect of its array self-moves**: each instruction of a pair of
    `selfPairB` is replaced, in place, by the copy `selfNopI` of its index register onto
    itself. Positions and labels are those of `B`, and the result has no access to an array
    at a replaced position. -/
def selfNop (k0 : Nat) (Lr : Nat → List String) (B : List LinstrRM) : List LinstrRM :=
  B.mapIdx fun k i =>
    if selfPairB k0 Lr B k || (decide (0 < k) && selfPairB k0 Lr B (k - 1)) then selfNopI i
    else i

/-- `selfPairB` over code held as an array. -/
def selfPairBA (k0 : Nat) (Lr : Nat → List String) (B : Array LinstrRM) (k : Nat) : Bool :=
  decide (k0 ≤ k) && match B[k]?, B[k + 1]? with
    | some i, some j => selfMoveB i j && selfDeadB Lr k i
    | _, _ => false

/-- `selfPairBA` at the array of the code is `selfPairB`. -/
theorem selfPairBA_toArray (k0 : Nat) (Lr : Nat → List String) (B : List LinstrRM) :
    selfPairBA k0 Lr B.toArray = selfPairB k0 Lr B := by
  funext k
  simp only [selfPairBA, selfPairB, List.getElem?_toArray]

/-- `selfNop` with the pairs `selfPairB` read off the array of the code, built once. -/
def selfNopImpl (k0 : Nat) (Lr : Nat → List String) (B : List LinstrRM) : List LinstrRM :=
  let a := B.toArray
  B.mapIdx fun k i =>
    if selfPairBA k0 Lr a k || (decide (0 < k) && selfPairBA k0 Lr a (k - 1)) then selfNopI i
    else i

/-- `selfNop` is evaluated as `selfNopImpl`. -/
@[csimp] theorem selfNop_eq_impl : @selfNop = @selfNopImpl := by
  funext k0 Lr B
  simp only [selfNop, selfNopImpl, selfPairBA_toArray]

/-- The first `k0` instructions of `selfNop k0 Lr B` are those of `B`. -/
theorem selfNop_take (k0 : Nat) (Lr : Nat → List String) (B : List LinstrRM) :
    (selfNop k0 Lr B).take k0 = B.take k0 := by
  apply List.ext_getElem?
  intro k
  simp only [selfNop, List.getElem?_take, List.getElem?_mapIdx]
  split
  · next hk =>
    cases B[k]? with
    | none => rfl
    | some i =>
        have h1 : selfPairB k0 Lr B k = false := by
          simp only [selfPairB, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Or.inl (by omega)
        have h2 : selfPairB k0 Lr B (k - 1) = false := by
          simp only [selfPairB, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Or.inl (by omega)
        simp [h1, h2]
  · rfl

/-- A position of `selfPairB` holds a load and the next position the matching store, the
    index register is other than the scratch register, and the names of the table two
    positions later are names of the table at the load other than the scratch register. -/
theorem selfPairB_spec {k0 : Nat} {Lr : Nat → List String} {B : List LinstrRM} {k : Nat}
    (h : selfPairB k0 Lr B k = true) :
    ∃ t a z sc w n, B[k]? = some (.Lopn [.reg t] "LOADIDX" [.arrIdx a z sc], .load w n)
      ∧ B[k + 1]? = some (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t], .store w n)
      ∧ z ≠ t ∧ ∀ x ∈ Lr (k + 2), x ≠ t ∧ x ∈ Lr k := by
  unfold selfPairB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  split at h
  · next i j hi hj =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨hm, hd⟩ := h
    obtain ⟨t, a, z, sc, w, n, rfl, rfl⟩ := selfMoveB_shape hm
    simp only [selfDeadB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
      List.contains_eq_mem, decide_eq_true_eq] at hd
    exact ⟨t, a, z, sc, w, n, hi, hj, hd.1, hd.2⟩
  · cases h

theorem isLabel_selfNopI (l : LLabel) (i : LinstrRM) :
    isLabel l (selfNopI i).1 = isLabel l i.1 := by
  unfold selfNopI
  split
  · next h => rw [h]; rfl
  · rfl

/-- The labels of `selfNop k0 Lr B` are at the positions they have in `B`. -/
theorem findLabelMem_selfNop (k0 : Nat) (Lr : Nat → List String) (B : List LinstrRM)
    (l : LLabel) : findLabelMem l (selfNop k0 Lr B) = findLabelMem l B := by
  unfold findLabelMem findLabel
  rw [List.findIdx?_map, List.findIdx?_map]
  have hm : ∀ (p : LinstrRM → Bool) (xs : List LinstrRM),
      xs.findIdx? p = (xs.map p).findIdx? id := fun p xs => by
    rw [List.findIdx?_map]; rfl
  rw [hm, hm _ B]
  congr 1
  apply List.ext_getElem?
  intro k
  simp only [selfNop, List.getElem?_map, List.getElem?_mapIdx]
  cases B[k]? with
  | none => rfl
  | some i =>
      simp only [Option.map_some, Function.comp]
      split
      · rw [isLabel_selfNopI]
      · rfl

/-- The copy of a register onto itself is a step that changes the program counter only. -/
theorem selfNop_step (P : LprogM) (z : String) (s : LstateMF) :
    ∃ u, evalInstrPMemF P (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) s = some u
      ∧ u.prog.base.reg.lvm = s.prog.base.reg.lvm ∧ u.prog.base.larr = s.prog.base.larr
      ∧ u.prog.base.lmem = s.prog.base.lmem ∧ u.prog.base.lpc = s.prog.base.lpc + 1
      ∧ u.prog.lfn = s.prog.lfn ∧ u.zf = s.zf ∧ u.prog.base.cf = s.prog.base.cf
      ∧ u.prog.base.of = s.prog.base.of := by
  refine ⟨_, evalInstrPMemF_movReg P z z _ s, ?_, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  · funext x
    simp only [LstateM.nextPc, LstateM.setReg, LstateN.lvm_nextPc, LstateN.lvm_setReg]
    split
    · next h => rw [h]
    · rfl
  · simp [LstateM.nextPc, LstateM.setReg, LstateM.lpc]

/-- The position after a step from a position that is not the load of a pair of
    `selfPairB` is not the store of such a pair: it is the next position or the position
    after a label. -/
theorem selfPairB_next {k0 : Nat} {Lr : Nat → List String} {B : List LinstrRM} {i : LinstrR}
    {pc pc' : Nat} (hn : NextPc (B.map Prod.fst) i pc pc') (hp : selfPairB k0 Lr B pc = false) :
    (decide (0 < pc') && selfPairB k0 Lr B (pc' - 1)) = false := by
  have hlab : ∀ l q, findLabel l (B.map Prod.fst) = some q → selfPairB k0 Lr B q = false := by
    intro l q hq
    obtain ⟨x, hx, hl⟩ := findLabel_sound l _ q hq
    by_contra hc
    obtain ⟨t, a, z, sc, w, n, hi, -⟩ := selfPairB_spec (Bool.eq_true_of_not_eq_false hc)
    rw [List.getElem?_map, hi] at hx
    cases Option.some.inj hx
    simp [isLabel] at hl
  have hs : ∀ q, selfPairB k0 Lr B q = false →
      (decide (0 < q + 1) && selfPairB k0 Lr B (q + 1 - 1)) = false := fun q h => by
    simp [h]
  cases i with
  | Lgoto tg =>
      obtain ⟨q, hq, rfl⟩ := hn
      exact hs q (hlab _ q hq)
  | Lcond c l =>
      rcases hn with rfl | ⟨q, hq, rfl⟩
      · exact hs pc hp
      · exact hs q (hlab _ q hq)
  | Lret => exact hn.elim
  | _ => obtain rfl := hn; exact hs pc hp

/-- An instruction set whose steps contain those of `x86Isa` and whose further steps are local
    calls takes, at two programs of the same function name and the same label positions, the
    same steps. -/
theorem step_congr_calls {I : LprogIsa.Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    {P P' : LprogM}
    (hfn : P.lfn = P'.lfn) (hl : ∀ l, findLabelMem l P.body = findLabelMem l P'.body)
    (i : LinstrRM) {s t : LstateMF} (h : I.step P i s = some t) : I.step P' i s = some t := by
  rcases hcl P i s t h with hx | ⟨dst, f, srcs, x, hi, rfl, hfwd, -⟩
  · exact hle _ _ _ _
      ((evalInstrPMemF_congr hfn hl i s).symm.trans hx : evalInstrPMemF P' i s = some t)
  · obtain ⟨w, tag⟩ := i
    simp only at hi
    subst hi
    exact hfwd P' tag dst srcs s rfl rfl

/-- A step of an instruction set whose steps beyond `x86Isa` are local calls keeps the
    function name and reaches a position allowed by `NextPc`. -/
theorem step_next_calls {I : LprogIsa.Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hcl : I.CallLocal x86Isa aa ao) (P : LprogM) (i : LinstrRM)
    (s t : LstateMF)
    (h : I.step P i s = some t) :
    t.prog.lfn = s.prog.lfn ∧
      NextPc (P.body.map Prod.fst) i.1 s.prog.base.lpc t.prog.base.lpc := by
  rcases hcl P i s t h with hx | ⟨dst, f, srcs, x, hi, rfl, -⟩
  · exact evalInstrPMemF_next P i s t hx
  · refine ⟨LprogIsa.lfn_retRes dst x s, ?_⟩
    rw [hi]
    exact LprogIsa.lpc_retRes dst x s

/-- **The flag machine on code without its array self-moves, at an instruction set with
    local calls.** The statement of `lsemFuelMemF_selfNop` for the runs of an instruction
    set `I` whose steps contain those of `x86Isa` and whose further steps are local calls at
    the array positions `aa` and the result lengths `ao`, under the call condition
    `LiveCalls`. -/
theorem lsemFuelMemF_selfNop_calls {I : LprogIsa.Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa aa ao) {fn : String} {B : List LinstrRM} {k0 : Nat}
    {Lr : Nat → List String} {AN : List String} {P₁ : LprogM}
    (hC : LiveCert id k0 (singletonProgM fn B) P₁ (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN))
    (hK : JasminLsemExportRegAlloc.LiveCalls id k0 (singletonProgM fn B) (fun k r => r ∈ Lr k)
      (fun _ r => r ∈ AN) aa ao) :
    ∀ (fuel : Nat) {s s' t : LstateMF},
      RelF2 id (· ∈ Lr s.prog.base.lpc) (· ∈ AN) s s' → k0 ≤ s.prog.base.lpc →
      (decide (0 < s.prog.base.lpc) && selfPairB k0 Lr B (s.prog.base.lpc - 1)) = false →
      I.lsemFuelMemF (singletonProgM fn B) fuel s = some t →
      ∃ t', I.lsemFuelMemF (singletonProgM fn (selfNop k0 Lr B)) fuel s' = some t'
        ∧ RelF2 id (· ∈ Lr t.prog.base.lpc) (· ∈ AN) t t' := by
  have hfi : ∀ (X : List LinstrRM) (x : LstatePM), findInstrMem (singletonProgM fn X) x
      = if x.lfn = fn then X[x.base.lpc]? else none := fun _ _ => rfl
  have hcg : ∀ (i : LinstrRM) {x y : LstateMF}, I.step P₁ i x = some y →
      I.step (singletonProgM fn (selfNop k0 Lr B)) i x = some y :=
    fun i _ _ hxy => step_congr_calls hle hcl (P := P₁)
      (P' := singletonProgM fn (selfNop k0 Lr B))
      hC.lfn (fun l => (hC.lbl l).trans (findLabelMem_selfNop k0 Lr B l).symm) i hxy
  have hx86 : ∀ (P : LprogM) (i : LinstrRM) (x : LstateMF),
      LprogIsa.shadowCall? i.1 = none → I.step P i x = evalInstrPMemF P i x :=
    fun P i x hi => LprogIsa.Isa.CallLocal.step_eq I hle hcl P hi x
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro s s' t hR hk hsec h
  have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
  have hlfn : s'.prog.lfn = s.prog.lfn := hR.2.1
  cases hf : findInstrMem (singletonProgM fn B) s.prog with
  | none =>
      have hf' : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog = none := by
        rw [hfi] at hf ⊢
        rw [hlfn, hpc]
        split at hf
        · next hfn =>
          rw [ite_eq_left hfn, selfNop, List.getElem?_mapIdx, hf]
          rfl
        · next hfn => rw [ite_eq_right hfn]
      rw [I.lsemFuelMemF_halt _ _ _ hf] at h
      obtain rfl := Option.some.inj h
      exact ⟨s', I.lsemFuelMemF_halt _ _ _ hf', hR⟩
  | some i =>
      have hfn : s.prog.lfn = fn := by
        rw [hfi] at hf
        by_contra hc
        rw [ite_eq_right hc] at hf
        cases hf
      have hget : B[s.prog.base.lpc]? = some i := by
        rw [hfi, ite_eq_left hfn] at hf
        exact hf
      cases fuel with
      | zero => simp [LprogIsa.Isa.lsemFuelMemF, hf] at h
      | succ n =>
      cases he : I.step (singletonProgM fn B) i s with
      | none => simp [LprogIsa.Isa.lsemFuelMemF, hf, he] at h
      | some u =>
      have hnx := step_next_calls hcl _ i s u he
      have hu : I.lsemFuelMemF (singletonProgM fn B) n u = some t := by
        simpa [LprogIsa.Isa.lsemFuelMemF, hf, he] using h
      by_cases hp : selfPairB k0 Lr B s.prog.base.lpc = true
      · obtain ⟨t0, a, z, sc, w, m, hi, hj, hzt, hdead⟩ := selfPairB_spec hp
        obtain rfl : i = _ := Option.some.inj (hget.symm.trans hi)
        rw [hx86 _ _ _ (by simp only [LprogIsa.shadowCall?]; rfl)] at he
        have hupc : u.prog.base.lpc = s.prog.base.lpc + 1 := hnx.2
        have hf2 : findInstrMem (singletonProgM fn B) u.prog
            = some (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t0], .store w m) := by
          rw [hfi, ite_eq_left (hnx.1.trans hfn), hupc]
          exact hj
        cases n with
        | zero => simp [LprogIsa.Isa.lsemFuelMemF, hf2] at hu
        | succ m' =>
        cases he2 : I.step (singletonProgM fn B)
            (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t0], .store w m) u with
        | none => simp [LprogIsa.Isa.lsemFuelMemF, hf2, he2] at hu
        | some u2 =>
        have hu2 : I.lsemFuelMemF (singletonProgM fn B) m' u2 = some t := by
          simpa [LprogIsa.Isa.lsemFuelMemF, hf2, he2] using hu
        rw [hx86 _ _ _ (by simp only [LprogIsa.shadowCall?]; rfl)] at he2
        obtain ⟨hla, hlm, hlv, hpc2, hfn2, hzf2, hcf2, hof2⟩ :=
          selfMove_steps t0 a z sc w m hzt he he2
        have hmov : ∀ (x : LstateMF),
            I.step (singletonProgM fn (selfNop k0 Lr B))
                (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) x
              = evalInstrPMemF (singletonProgM fn (selfNop k0 Lr B))
                (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) x :=
          fun x => hx86 _ _ _ (by simp only [LprogIsa.shadowCall?]; rfl)
        obtain ⟨v1, hv1, v1lv, v1la, v1lm, v1pc, v1fn, v1zf, v1cf, v1of⟩ :=
          selfNop_step (singletonProgM fn (selfNop k0 Lr B)) z s'
        obtain ⟨v2, hv2, v2lv, v2la, v2lm, v2pc, v2fn, v2zf, v2cf, v2of⟩ :=
          selfNop_step (singletonProgM fn (selfNop k0 Lr B)) z v1
        rw [← hmov] at hv1 hv2
        have hg1 : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog
            = some (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) := by
          rw [hfi, ite_eq_left (hlfn.trans hfn), hpc, selfNop, List.getElem?_mapIdx, hi]
          simp [hp, selfNopI]
        have hg2 : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) v1.prog
            = some (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) := by
          rw [hfi, ite_eq_left (v1fn.trans (hlfn.trans hfn)), v1pc, hpc, selfNop,
            List.getElem?_mapIdx, hj]
          simp [hp, selfNopI]
        have hR2 : RelF2 id (· ∈ Lr u2.prog.base.lpc) (· ∈ AN) u2 v2 := by
          refine ⟨⟨⟨?_, fun r hr => ?_⟩, fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · show v2.prog.base.lpc = u2.prog.base.lpc
            rw [v2pc, v1pc, hpc, hpc2]
          · rw [hpc2] at hr
            obtain ⟨hne, hin⟩ := hdead r hr
            rw [hlv r hne, v2lv, v1lv]
            exact hR.1.1.2 r hin
          · rw [hla, v2la, v1la]
            exact hR.1.2.1 r hr
          · rw [hlm, v2lm, v1lm]
            exact hR.1.2.2
          · rw [hfn2, v2fn, v1fn]
            exact hlfn
          · rw [hzf2, v2zf, v1zf]
            exact hR.2.2.1
          · rw [hcf2, v2cf, v1cf]
            exact hR.2.2.2.1
          · rw [hof2, v2of, v1of]
            exact hR.2.2.2.2
        have hsec2 : (decide (0 < u2.prog.base.lpc)
            && selfPairB k0 Lr B (u2.prog.base.lpc - 1)) = false := by
          rw [hpc2, show s.prog.base.lpc + 2 - 1 = s.prog.base.lpc + 1 from rfl,
            Bool.and_eq_false_iff]
          right
          by_contra hc
          obtain ⟨t1, a1, z1, sc1, w1, m1, hi1, -⟩ :=
            selfPairB_spec (Bool.eq_true_of_not_eq_false hc)
          rw [hj] at hi1
          cases congrArg Prod.snd (Option.some.inj hi1)
        obtain ⟨t', ht', hRt⟩ := ih m' (by omega) hR2 (by omega) hsec2 hu2
        refine ⟨t', ?_, hRt⟩
        simp [LprogIsa.Isa.lsemFuelMemF, hg1, hv1, hg2, hv2, ht']
      · have hp' : selfPairB k0 Lr B s.prog.base.lpc = false := Bool.eq_false_of_not_eq_true hp
        obtain ⟨u', hu', hRu, hku⟩ :=
          JasminLsemExportRegAlloc.step_live_calls hle hcl hC hK i hk hget hR he
        rw [renRM_id] at hu'
        replace hu' := hcg i hu'
        have hg : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog = some i := by
          rw [hfi, ite_eq_left (hlfn.trans hfn), hpc, selfNop, List.getElem?_mapIdx, hget]
          simp [hp', hsec]
        obtain ⟨t', ht', hRt⟩ := ih n (by omega) hRu hku (selfPairB_next hnx.2 hp') hu
        refine ⟨t', ?_, hRt⟩
        simp [LprogIsa.Isa.lsemFuelMemF, hg, hu', ht']

/-- **The flag machine on code without its array self-moves.** For a body `B` with a
    liveness certificate `LiveCert` of the identity renaming from `k0` on, at the register
    names `Lr` and the array names `AN`: every halting run of `B` from a position `k ≥ k0`
    that is not the store of a pair of `selfPairB` is matched, with the same fuel, by a
    halting run of `selfNop k0 Lr B` from a state that agrees on the register names of `Lr`
    at `k`, the arrays of `AN`, the word memory and the flags, into a state that agrees
    with the final state on the register names of `Lr` at the final position, the arrays of
    `AN`, the word memory and the flags. -/
theorem lsemFuelMemF_selfNop {fn : String} {B : List LinstrRM} {k0 : Nat}
    {Lr : Nat → List String} {AN : List String} {P₁ : LprogM}
    (hC : LiveCert id k0 (singletonProgM fn B) P₁ (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN)) :
    ∀ (fuel : Nat) {s s' t : LstateMF},
      RelF2 id (· ∈ Lr s.prog.base.lpc) (· ∈ AN) s s' → k0 ≤ s.prog.base.lpc →
      (decide (0 < s.prog.base.lpc) && selfPairB k0 Lr B (s.prog.base.lpc - 1)) = false →
      lsemFuelMemF (singletonProgM fn B) fuel s = some t →
      ∃ t', lsemFuelMemF (singletonProgM fn (selfNop k0 Lr B)) fuel s' = some t'
        ∧ RelF2 id (· ∈ Lr t.prog.base.lpc) (· ∈ AN) t t' := by
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF]
  exact lsemFuelMemF_selfNop_calls (LprogIsa.Isa.StepLe.refl x86Isa)
    (LprogIsa.Isa.CallLocal.refl x86Isa (fun _ _ => none)) hC
    JasminLsemExportRegAlloc.liveCalls_none

/-- **The run of code without its array self-moves.** For a prefix `pre` of operations and
    code `C` accepted by `regCoB id pre C L AN aa ao`, every halting run of `pre ++ C` from
    a state at position `0` is matched, with the same fuel, by a halting run from that state
    of `selfNop` of `pre ++ C` at the table `liveAt L`, at the end of which every register
    name the certificate gives the end of the body holds the value of the first run and
    every array of `AN` is the array of the first run. The statement is for the runs of an
    instruction set `I` whose steps contain those of `x86Isa` and whose further steps are
    local calls at the array positions `aa` and the result lengths `ao`, for a prefix `pre`
    at whose instructions the step of `I` is the step of `x86Isa`. -/
theorem selfNop_run_calls {I : LprogIsa.Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa aa ao) {pre C : List LinstrRM}
    {L : Nat → List String} {AN : List String}
    {fn : String} (hpre : ∀ i ∈ pre, IsLopn i)
    (hag : ∀ i ∈ pre, ∀ (Q : LprogM) (s : LstateMF), I.step Q i s = x86Isa.step Q i s)
    (h : regCoB id pre C L AN aa ao = true)
    (b0 : LstateM) (hb0 : b0.lpc = 0) (zf : Bool) (k : Nat) (t : LstateMF)
    (hrun : I.lsemFuelMemF (singletonProgM fn (pre ++ C)) k
      { prog := { base := b0, lfn := fn }, zf := zf } = some t) :
    ∃ t' : LstateMF,
      I.lsemFuelMemF (singletonProgM fn
          (selfNop pre.length (liveAt L (pre ++ C).length) (pre ++ C))) k
        { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ (∀ y ∈ L (pre ++ C).length, t'.prog.base.reg.lvm y = t.prog.base.reg.lvm y)
      ∧ ∀ a ∈ AN, t'.prog.base.larr a = t.prog.base.larr a := by
  have hC := liveCert_of_regCoB fn hpre h
  have hlow : ∀ j, j < pre.length →
      selfPairB pre.length (liveAt L (pre ++ C).length) (pre ++ C) j = false := fun j hj => by
    simp [selfPairB, Nat.not_le.mpr hj]
  have hposC : ∀ j, j < pre.length →
      (singletonProgM fn (pre ++ C)).body[b0.lpc + j]? = pre[j]? := fun j hj => by
    show (pre ++ C)[b0.lpc + j]? = _
    rw [hb0, Nat.zero_add, List.getElem?_append_left hj]
  have hposN : ∀ j, j < pre.length →
      (singletonProgM fn (selfNop pre.length (liveAt L (pre ++ C).length)
        (pre ++ C))).body[b0.lpc + j]? = pre[j]? := fun j hj => by
    show (selfNop pre.length (liveAt L (pre ++ C).length) (pre ++ C))[b0.lpc + j]? = _
    rw [hb0, Nat.zero_add, selfNop, List.getElem?_mapIdx, List.getElem?_append_left hj,
      hlow j hj]
    have h1 : (decide (0 < j) && selfPairB pre.length (liveAt L (pre ++ C).length)
        (pre ++ C) (j - 1)) = false := by
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rfl
      · rw [hlow (j - 1) (by omega), Bool.and_false]
    rw [h1]
    cases pre[j]? <;> rfl
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le
    (JasminLsemRenameLoop.lsemFuelMemF_seg_fuel_calls hcl _ fn rfl pre b0 zf k t hpre
      hposC hrun)
  rw [JasminLsemMemFlagNestJoin.lsemFuelMemF_segF_agree _ fn rfl pre b0 zf f hpre hag
    hposC] at hrun
  rw [JasminLsemMemFlagNestJoin.lsemFuelMemF_segF_agree _ fn rfl pre b0 zf f hpre hag hposN]
  cases hrs : runStraightF pre b0 zf with
  | none => simp [hrs] at hrun
  | some bz =>
      rw [hrs, Option.bind_some] at hrun
      rw [Option.bind_some]
      have hpc : bz.1.lpc = pre.length := by
        rw [runStraightF_lpc pre b0 zf bz.1 bz.2 hrs, hb0, Nat.zero_add]
      have hsec : (decide (0 < pre.length) && selfPairB pre.length
          (liveAt L (pre ++ C).length) (pre ++ C) (pre.length - 1)) = false := by
        rcases Nat.eq_zero_or_pos pre.length with h0 | h0
        · rw [h0]; rfl
        · rw [hlow (pre.length - 1) (by omega), Bool.and_false]
      obtain ⟨t', ht', hRt⟩ := lsemFuelMemF_selfNop_calls hle hcl hC
        (liveCalls_of_regCoB fn h) f
        (s := { prog := { base := bz.1, lfn := fn }, zf := bz.2 })
        (s' := { prog := { base := bz.1, lfn := fn }, zf := bz.2 })
        ⟨⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
        (Nat.le_of_eq hpc.symm)
        (by
          show (decide (0 < bz.1.lpc) && selfPairB pre.length (liveAt L (pre ++ C).length)
            (pre ++ C) (bz.1.lpc - 1)) = false
          rw [hpc]
          exact hsec) hrun
      have hfin : (pre ++ C).length ≤ t.prog.base.lpc :=
        lsemFuelMemF_length_le_calls hcl (fn := fn) (B := pre ++ C) f (Eq.refl fn) hrun
      refine ⟨t', ht', fun y hy => hRt.1.1.2 y ?_, fun a ha => hRt.1.2.1 a ha⟩
      show y ∈ liveAt L (pre ++ C).length t.prog.base.lpc
      rw [liveAt, Nat.min_eq_right hfin]
      exact List.mem_cons_of_mem _ hy

/-- **The run of code without its array self-moves.** For a prefix `pre` of operations and
    code `C` accepted by `regCoB id pre C L AN`, every halting run of `pre ++ C` from a
    state at position `0` is matched, with the same fuel, by a halting run from that state
    of `selfNop` of `pre ++ C` at the table `liveAt L`, at the end of which every register
    name the certificate gives the end of the body holds the value of the first run and
    every array of `AN` is the array of the first run. -/
theorem selfNop_run {pre C : List LinstrRM} {L : Nat → List String} {AN : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    {fn : String} (hpre : ∀ i ∈ pre, IsLopn i) (h : regCoB id pre C L AN aa ao = true)
    (b0 : LstateM) (hb0 : b0.lpc = 0) (zf : Bool) (k : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (pre ++ C)) k
      { prog := { base := b0, lfn := fn }, zf := zf } = some t) :
    ∃ t' : LstateMF,
      lsemFuelMemF (singletonProgM fn
          (selfNop pre.length (liveAt L (pre ++ C).length) (pre ++ C))) k
        { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ (∀ y ∈ L (pre ++ C).length, t'.prog.base.reg.lvm y = t.prog.base.reg.lvm y)
      ∧ ∀ a ∈ AN, t'.prog.base.larr a = t.prog.base.larr a := by
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hrun ⊢
  exact selfNop_run_calls (LprogIsa.Isa.StepLe.refl x86Isa)
    (LprogIsa.Isa.CallLocal.refl x86Isa aa ao) hpre (fun _ _ _ _ => rfl) h b0 hb0
    zf k t hrun

/-! ## 6. The back half -/

/-- One pass of the flag analysis of `deadTab` over the body `B`, on the pair of the
    zero-flag table and the carry-flag table: each instruction lowers the entries of the
    positions it leads to. A label and a conditional jump pass their entries to the next
    position, a jump and a conditional jump to the position after the target label; a
    shadow instruction of a call clears the entries of the next position; every other
    instruction with a symbolic step passes `ImageAddrCall.zNext` and
    `ImageAddrCall.cNext` of its entries. -/
def flagPass (B : List LinstrRM) (F : Array Bool × Array Bool) : Array Bool × Array Bool :=
  (List.range B.length).foldl (fun (F : Array Bool × Array Bool) k =>
    match B[k]? with
    | none => F
    | some i =>
      let z := F.1.getD k false
      let c := F.2.getD k false
      let low := fun (F : Array Bool × Array Bool) (j : Nat) (zj cj : Bool) =>
        (F.1.setIfInBounds j (F.1.getD j false && zj),
          F.2.setIfInBounds j (F.2.getD j false && cj))
      match i.fst with
      | .Llabel _ _ => low F (k + 1) z c
      | .Lcond _ l =>
          let F := low F (k + 1) z c
          match findLabelMem l B with
          | some q => low F (q + 1) z c
          | none => F
      | .Lgoto (_, l) =>
          match findLabelMem l B with
          | some q => low F (q + 1) z c
          | none => F
      | j =>
          if (LprogIsa.shadowCall? j).isSome then low F (k + 1) false false
          else
            match X86Backend.OwnedLprogTV.symStep i X86Backend.OwnedLprogTV.SSt.start with
            | .ok ss _ =>
                low F (k + 1) (X86Backend.ImageAddrCall.zNext z c ss.zf)
                  (X86Backend.ImageAddrCall.cNext c ss)
            | _ => F) F

/-- The passes `flagPass` over `B`, at most `n` of them, until a pass changes no entry. -/
def flagIter (B : List LinstrRM) : Nat → Array Bool × Array Bool → Array Bool × Array Bool
  | 0, F => F
  | n + 1, F =>
      let F' := flagPass B F
      if F' == F then F else flagIter B n F'

/-- **The table of dead names and live flags of a body** `B` with the names `outs` read
    after it (`ImageAddrCall.DeadTab`). The dead names at a position are the names of the
    instructions of `B` and the general-purpose names that the register liveness table
    `liveRegTab` does not hold there. The flag tables are the result of `flagIter` from
    the tables that hold `false` at the position `0` and `true` elsewhere. The checks of
    `calleeBodyB` check the table; its construction carries no trust. -/
def deadTab (B : List LinstrRM) (outs : List String) : X86Backend.ImageAddrCall.DeadTab :=
  let live := liveRegTab B outs
  let N := ((B.flatMap fun i => LprogCallCut.instrNames i.fst)
    ++ X86Backend.DecodePrinted.gpList).eraseDups
  let F0 : Array Bool := (Array.replicate (B.length + 1) true).setIfInBounds 0 false
  let F := flagIter B (2 * B.length + 3) (F0, F0)
  { dead := fun k => N.filter fun x => !(tabAt live k).contains x
    z := fun k => F.1.getD k false
    c := fun k => F.2.getD k false }

/-- A label above every label declared in `B`. -/
def freshLabel (B : List LinstrRM) : LLabel :=
  B.foldl (fun m i =>
    match i.fst with
    | .Llabel _ l => max m (l + 1)
    | _ => m) 0

/-- **The cut checks at a procedure table** `T`: the cut programs `LprogCallCut.cutAt` of
    `B`, at the empty function name and the label `fin`, pass `LprogCallCut.cutOkB` at `T`
    and, for every entry and every exit, the reverse check `LprogCallCut.isCutRevB` at
    `T`. -/
def calleeCutB (T : LprogIsa.ProcTable) (fin : LLabel) (B : List LinstrRM) : Bool :=
  let es := none :: (LprogCallCut.sites T B).map some
  LprogCallCut.cutOkB T "" fin B
    && es.all fun e => es.all fun x =>
      LprogCallCut.isCutRevB T B x (LprogCallCut.cutAt "" fin B e x)
        (LprogCallCut.cutPos B e)

/-- A label a member of `B` declares is below `freshLabel B`. -/
theorem lt_freshLabel {B : List LinstrRM} {i : LinstrRM} (hi : i ∈ B) {l : LLabel}
    (hl : JasminLsemLabeled.isLabel l i.fst = true) : l < freshLabel B := by
  unfold freshLabel
  suffices h : ∀ (A : List LinstrRM) (m : LLabel),
      m ≤ A.foldl (fun m i =>
        match i.fst with
        | .Llabel _ l => max m (l + 1)
        | _ => m) m ∧
      (i ∈ A → l < A.foldl (fun m i =>
        match i.fst with
        | .Llabel _ l => max m (l + 1)
        | _ => m) m) from (h B 0).2 hi
  intro A
  induction A with
  | nil => exact fun m => ⟨le_refl _, fun h => absurd h List.not_mem_nil⟩
  | cons j A ih =>
      intro m
      simp only [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := ih (match j.fst with
        | .Llabel _ l => max m (l + 1)
        | _ => m)
      refine ⟨le_trans ?_ ih1, fun hm => ?_⟩
      · split <;> simp
      · rcases List.mem_cons.mp hm with rfl | hm
        · refine lt_of_lt_of_le ?_ ih1
          obtain ⟨ir, tag⟩ := i
          cases ir <;> simp only [JasminLsemLabeled.isLabel, Bool.false_eq_true] at hl
          rename_i l'
          obtain rfl : l = l' := by simpa using hl
          exact lt_of_lt_of_le (Nat.lt_succ_self l) (le_max_right _ _)
        · exact ih2 hm

/-- A body whose instructions are instructions of `A` declares no label `freshLabel A`. -/
theorem findLabelMem_freshLabel {A B : List LinstrRM} (h : ∀ i ∈ B, i ∈ A) :
    JasminLsemMemLoop.findLabelMem (freshLabel A) B = none := by
  cases hq : JasminLsemMemLoop.findLabelMem (freshLabel A) B with
  | none => rfl
  | some q =>
      exfalso
      unfold JasminLsemMemLoop.findLabelMem at hq
      obtain ⟨ins, hk, hlab⟩ := JasminLsemLabeled.findLabel_sound _ _ q hq
      rw [List.getElem?_map] at hk
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hk
      exact lt_irrefl _ (lt_freshLabel (h i (List.mem_of_getElem? hi)) hlab)

/-- **The cut checks at the empty function name give the soundness of the validation by
    segments at every function name.** If the cut programs of `ref` and of `img` pass
    `calleeCutB T` at the label `freshLabel (ref ++ img)`, then for every function name `fn`
    and every list `outs` of observed registers, `LprogCallCut.CutCheckSoundI` holds on the
    bounds-checked x86 instruction set `CheckedIsaCall.x86IsaK` at the table `T`, for the
    cut programs `LprogCallCut.cutAt` of `ref` and of `img` at `fn`. -/
theorem calleeCutB_soundK {T : LprogIsa.ProcTable} {ref img : List LinstrRM}
    (href : calleeCutB T (freshLabel (ref ++ img)) ref = true)
    (himg : calleeCutB T (freshLabel (ref ++ img)) img = true) (outs : List String)
    (fn : String) :
    LprogCallCut.CutCheckSoundI X86Backend.CheckedIsaCall.x86IsaK T outs fn ref img
      (LprogCallCut.cutAt fn (freshLabel (ref ++ img)) ref)
      (LprogCallCut.cutAt fn (freshLabel (ref ++ img)) img) := by
  have hcut : ∀ {B : List LinstrRM}, (∀ i ∈ B, i ∈ ref ++ img) →
      calleeCutB T (freshLabel (ref ++ img)) B = true →
      ∀ e x, LprogCallCut.IsSite T B e → LprogCallCut.IsSite T B x →
        LprogCallCut.IsCut T fn B e x
            (LprogCallCut.cutAt fn (freshLabel (ref ++ img)) B e x) (LprogCallCut.cutPos B e)
          ∧ LprogCallCut.IsCutRev T B x
            (LprogCallCut.cutAt fn (freshLabel (ref ++ img)) B e x)
            (LprogCallCut.cutPos B e) := by
    intro B hsub h e x he hx
    simp only [calleeCutB, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hok, hrev⟩ := h
    have hB := LprogCallCut.jumpLabel_ne_of_isCutRev
      (LprogCallCut.isCutRev_of_isCutRevB
        (hrev none List.mem_cons_self none List.mem_cons_self))
      (findLabelMem_freshLabel hsub)
    exact ⟨LprogCallCut.isCut_cutAt_of_cutOkB hok hB fn he hx,
      LprogCallCut.isCutRev_cutAt_rename hB
        (hrev e (LprogCallCut.mem_of_isSite he) x (LprogCallCut.mem_of_isSite hx))⟩
  exact X86Backend.CheckedIsaCall.cutCheck_soundK
    (fun e x he hx => (hcut (fun i hi => List.mem_append_left _ hi) href e x he hx).1)
    (hcut (fun i hi => List.mem_append_right _ hi) himg)

/-- **The entry sets of the segments of a body** `B` with the names `outs` read after it: at
    the entry `e`, the names the register liveness table `liveRegTab B outs` holds at the
    entry position of `e`. The name of an array can be among them: the operands of a later
    call are read as registers, and registers and arrays are separate name spaces, so a
    register merged onto the name of an array is a register like any other.
    `X86Backend.CalleeSegCheck.calleeSegB` checks them. -/
def insTab (B : List LinstrRM) (outs : List String) : Option Nat → List String :=
  fun e => tabAt (liveRegTab B outs) (LprogCallCut.entryPos e)

/-- **The check of the code of a callee** `c` at the calls of a printed body `body` at the
    slot map `sl`: when the code of `c` decodes (a scalar callee), the decoded block passes
    `Callee.keepCheckAtB` at the clobber set, the frame and the store policy of `c`: the keep
    check at the frame of the code (`Callee.blockFrame`) and the declared policy, with that
    frame and the red zone of the policy within the frame of `c`; when it does not decode (a
    vector kernel, whose contract is a hypothesis of its link theorem), the operands
    `c.siteArgs sl body p` of the call at each position `p` are pairwise distinct. -/
def calleeCodeB (c : CalleeData) (sl : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  match decodeLprog c.bytes with
  | some q => X86Backend.Callee.keepCheckAtB q c.sig.clob c.frame c.pol
  | none => (List.range body.length).all fun p => (body[p]?).all fun bi =>
      !X86Backend.ImageAddrCall.isCallB bi.li_i || decide (c.siteArgs sl body p).Nodup

/-- **The check of the code of the functions of a table** at the calls of a printed body: the
    decoded block of each function whose code decodes passes `Callee.keepCheckAtB` at its
    clobber set, its frame and its store policy, and at each call of a function whose code
    does not decode the operands of the call are pairwise distinct. -/
def calleeCodeBT (T : CalleeTab) (sl : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  T.fns.all (fun c => (decodeLprog c.bytes).all fun q =>
      X86Backend.Callee.keepCheckAtB q c.sig.clob c.frame c.pol)
    && (List.range body.length).all fun p => (body[p]?).all fun bi =>
      !X86Backend.ImageAddrCall.isCallB bi.li_i
        || ((callSymAt body p).bind T.lookup).all fun c =>
          (decodeLprog c.bytes).isSome || decide (c.siteArgs sl body p).Nodup

/-- **`calleeCodeBT` at the table of one linked function** is `calleeCodeB`, on a body whose
    calls name that function. -/
theorem calleeCodeBT_one {c : CalleeData} {sl : String → Option (String × Nat)} {body : Lcmd}
    (hsym : ∀ {p : Nat} {bi : Linstr} {ra : Option String} {t : String × LLabel},
      body[p]? = some bi → bi.li_i = .Lcall ra t → t.1 = c.name) :
    calleeCodeBT (CalleeTab.one c) sl body = calleeCodeB c sl body := by
  have hcall : ∀ p, (body[p]?).all (fun bi => !X86Backend.ImageAddrCall.isCallB bi.li_i
        || ((callSymAt body p).bind (CalleeTab.one c).lookup).all fun d =>
          (decodeLprog d.bytes).isSome || decide (d.siteArgs sl body p).Nodup)
      = (body[p]?).all (fun bi => !X86Backend.ImageAddrCall.isCallB bi.li_i
        || ((decodeLprog c.bytes).isSome || decide (c.siteArgs sl body p).Nodup)) := by
    intro p
    cases hb : body[p]? with
    | none => rfl
    | some bi =>
        simp only [Option.all_some]
        cases hc : X86Backend.ImageAddrCall.isCallB bi.li_i with
        | false => simp
        | true =>
            obtain ⟨ra, f, l, e⟩ := X86Backend.ImageAddrCall.exists_lcall_of_isCallB hc
            simp only [callSym_lookup_one hb e (hsym hb e), Option.all_some]
  have hall : (CalleeTab.one c).fns.all (fun d => (decodeLprog d.bytes).all fun q =>
        X86Backend.Callee.keepCheckAtB q d.sig.clob d.frame d.pol)
      = (decodeLprog c.bytes).all fun q =>
          X86Backend.Callee.keepCheckAtB q c.sig.clob c.frame c.pol := by
    simp [CalleeTab.one]
  simp only [calleeCodeBT, calleeCodeB, hall, hcall]
  cases hq : decodeLprog c.bytes <;> simp

/-- The block the code of a function of a table decodes to passes `Callee.keepCheckAtB` at the
    clobber set, the frame and the store policy of the function, under `calleeCodeBT`. -/
theorem calleeCodeBT_keep {T : CalleeTab} {sl : String → Option (String × Nat)} {body : Lcmd}
    (h : calleeCodeBT T sl body = true) {c : CalleeData} (hc : c ∈ T.fns)
    {q : List X86Backend.LprogBytesDecode.RInstr} (hq : decodeLprog c.bytes = some q) :
    X86Backend.Callee.keepCheckAtB q c.sig.clob c.frame c.pol = true := by
  simp only [calleeCodeBT, Bool.and_eq_true, List.all_eq_true] at h
  have hkc := h.1 c hc
  simp only [hq, Option.all_some] at hkc
  exact hkc

/-- **Soundness of the code check of a table.** Under `calleeCodeBT`, the block that the code
    of a function `c` of the table decodes to holds no `call`, and every leaky run of it from
    its first index to its `ret`, from an entry state whose out windows of the store policy of
    `c` are disjoint from the frame of `c` below its stack register, restores the stack
    register, keeps every register outside the clobber set of `c`, and keeps every byte outside
    that frame and those out windows (`Callee.keepCheckAtB_sound`). -/
theorem calleeCodeBT_sound {T : CalleeTab} {sl : String → Option (String × Nat)} {body : Lcmd}
    (h : calleeCodeBT T sl body = true) {c : CalleeData} (hc : c ∈ T.fns)
    {q : List X86Backend.LprogBytesDecode.RInstr} (hq : decodeLprog c.bytes = some q) :
    (∀ tg, X86Backend.LprogBytesDecode.RInstr.call tg ∉ q)
      ∧ ∀ {r ok s t s'}, X86Backend.DecodedCT.RunL r ok q 0 s t s' →
        X86Backend.Callee.WinSep c.pol c.frame s.regs →
        s'.regs "%rsp" = s.regs "%rsp" ∧ (∀ r', c.sig.clob r' = false → s'.regs r' = s.regs r')
          ∧ ∀ x, ¬ X86Backend.Callee.KeepFoot ⟨0, c.pol.wins⟩ c.frame s.regs x →
            s'.mem x = s.mem x :=
  X86Backend.Callee.keepCheckAtB_sound (calleeCodeBT_keep h hc hq)

/-- **The operands of each call of a function of a table whose code does not decode are
    distinct**: under `calleeCodeBT`, at a call of a symbol `f` whose function `c` has code
    that does not decode, the operands `CalleeData.siteArgs` of the call are pairwise
    distinct. -/
theorem calleeCodeBT_nodup {T : CalleeTab} {sl : String → Option (String × Nat)} {body : Lcmd}
    (h : calleeCodeBT T sl body = true) {p : Nat} {bi : Linstr} (hb : body[p]? = some bi)
    {ra : Option String} {f : String} {l : LLabel} (hbi : bi.li_i = .Lcall ra (f, l))
    {c : CalleeData} (hc : T.lookup f = some c) (hd : decodeLprog c.bytes = none) :
    (c.siteArgs sl body p).Nodup := by
  simp only [calleeCodeBT, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hp := h.2 p (List.getElem?_eq_some_iff.mp hb).1
  have hs : callSymAt body p = some f := by simp [callSymAt, hb, hbi]
  rw [hb] at hp
  simpa [hbi, X86Backend.ImageAddrCall.isCallB, hs, hc, hd] using hp

/-- **The checks of a calling body**, of the printed body `body` at the slot map `sl`, with the
    reference `ref` of the image check, the observed names `outs` and the function name `fn`,
    against the data the callees give: the Boolean `keep` of their pools, the Boolean `codeOk`
    of their code, the predicate `syms` of their symbols, the Boolean `decodeOk` of the decode
    of `body` into call sites, the table of procedures `P`, the image `img` of `body`, the
    check `dead` of the dead names at the calls and the frame `G` below the return word. With
    `D := deadTab img outs`:

    * `keep` and `codeOk` hold;
    * every shadow instruction of `ref` calls a symbol of `syms`
      (`CalleeSegCheck.callSymsB`), and `decodeOk` holds, so that every call of `body` names a
      callee;
    * the cut programs of `ref` and of `img` pass `calleeCutB` at `P` and a label above their
      labels;
    * `body` passes `ImageAddrCall.callSitesB`;
    * the table `D` passes `dead`, `ImageAddrCall.callFlagsB`, `ImageAddrCall.condLiveB` and
      `ImageAddrCall.deadSegB`, and holds no live flag at the position `0`;
    * `ref` passes the bounds check with calls `CheckedIsaCall.idxInvCheckPB` at `P`, from the
      entry facts `boundFacts σ nm` of the layout, at the annotation
      `CheckedIsaCall.idxAnnotP`;
    * the segments of `ref` and of `img` pass `CalleeSegCheck.calleeSegB` at `P`, the function
      name `fn`, the label of the cut checks and the entry sets `insTab ref outs`;
    * the frame range of `σ` covers the return word of the call and `G` bytes below it
      (`CalleeStackRoom.stackRoomB`), and the frame offsets of `body` pass
      `ImageAddrCall.frameNonnegB` at `G`;
    * the width analysis at the frame names of `body` is dead at each call and at the return
      (`ImageAddrCallW.bitsDeadB`).

    These are the Boolean hypotheses of `ImageAddrCallW.haltsO_of_deadChecksS`, of
    `calleeCutB_soundK`, of `CheckedIsaCall.refRun_checked` and of
    `CalleeSegCheck.calleeSegB_soundK` (`calleeBody_imgRun`), and of
    `CalleeStackRoom.callerSep_of_regions` (`calleeBody_callerSep`). -/
def calleeChecksB (σ : AbiLayout) (nm : String → String) (keep codeOk : Bool)
    (syms : String → Bool) (decodeOk : Bool) (P : LprogIsa.ProcTable) (img : List LinstrRM)
    (dead : (Nat → List String) → Bool) (G : Nat)
    (sl : String → Option (String × Nat)) (outs : List String) (body : Lcmd)
    (ref : List LinstrRM) (fn : String) : Bool :=
  let D := deadTab img outs
  let fin := freshLabel (ref ++ img)
  keep
    && codeOk
    && X86Backend.CalleeSegCheck.callSymsB syms ref
    && decodeOk
    && calleeCutB P fin ref && calleeCutB P fin img
    && X86Backend.ImageAddrCall.callSitesB sl body
    && dead D.dead
    && X86Backend.ImageAddrCall.callFlagsB D body
    && X86Backend.ImageAddrCall.condLiveB D body
    && X86Backend.ImageAddrCall.deadSegB D img
    && !D.live 0
    && X86Backend.CheckedIsaCall.idxInvCheckPB P (boundFacts σ nm)
      (X86Backend.CheckedIsaCall.idxAnnotP P (boundFacts σ nm) ref) ref
    && X86Backend.CalleeSegCheck.calleeSegB P fn fin (insTab ref outs) outs ref img
    && X86Backend.CalleeStackRoom.stackRoomB σ body G
    && X86Backend.ImageAddrCall.frameNonnegB body G
    && X86Backend.ImageAddrCallW.bitsDeadB (frameMark (frameNames body)) D body

/-- **The checks of a calling body, as propositions**: the conjuncts of `calleeChecksB`, at the
    dead table `deadTab img outs` and the label `freshLabel (ref ++ img)` of the cut checks. -/
structure CalleeChecksOK (σ : AbiLayout) (nm : String → String) (keep codeOk : Bool)
    (syms : String → Bool) (decodeOk : Bool) (P : LprogIsa.ProcTable) (img : List LinstrRM)
    (dead : (Nat → List String) → Bool) (G : Nat)
    (sl : String → Option (String × Nat)) (outs : List String) (body : Lcmd)
    (ref : List LinstrRM) (fn : String) : Prop where
  /-- The pools of the callees pass `Callee.keepPoolB`. -/
  keepPool : keep = true
  /-- The code of the callees passes its check at the calls of `body`. -/
  code : codeOk = true
  /-- Every shadow instruction of `ref` calls a symbol of a callee. -/
  symsRef : X86Backend.CalleeSegCheck.callSymsB syms ref = true
  /-- `body` decodes into its call sites at the callees. -/
  decode : decodeOk = true
  /-- The cut program of `ref` passes `calleeCutB`. -/
  cutRef : calleeCutB P (freshLabel (ref ++ img)) ref = true
  /-- The cut program of the image passes `calleeCutB`. -/
  cutImg : calleeCutB P (freshLabel (ref ++ img)) img = true
  /-- `body` passes `ImageAddrCall.callSitesB`. -/
  callSites : X86Backend.ImageAddrCall.callSitesB sl body = true
  /-- The dead names of the image pass the check of the dead names at the calls. -/
  dead : dead (deadTab img outs).dead = true
  /-- The dead table of the image passes `ImageAddrCall.callFlagsB`. -/
  flags : X86Backend.ImageAddrCall.callFlagsB (deadTab img outs) body = true
  /-- The dead table of the image passes `ImageAddrCall.condLiveB`. -/
  condLive : X86Backend.ImageAddrCall.condLiveB (deadTab img outs) body = true
  /-- The dead table of the image passes `ImageAddrCall.deadSegB`. -/
  deadSeg : X86Backend.ImageAddrCall.deadSegB (deadTab img outs) img = true
  /-- The dead table of the image holds no live flag at the position `0`. -/
  live0 : (deadTab img outs).live 0 = false
  /-- `ref` passes the bounds check with calls. -/
  idx : X86Backend.CheckedIsaCall.idxInvCheckPB P (boundFacts σ nm)
    (X86Backend.CheckedIsaCall.idxAnnotP P (boundFacts σ nm) ref) ref = true
  /-- The segments of `ref` and of the image pass `CalleeSegCheck.calleeSegB`. -/
  seg : X86Backend.CalleeSegCheck.calleeSegB P fn (freshLabel (ref ++ img))
    (insTab ref outs) outs ref img = true
  /-- The frame range of `σ` covers the return word and the frame of the callees. -/
  stackRoom : X86Backend.CalleeStackRoom.stackRoomB σ body G = true
  /-- The frame offsets of `body` pass `ImageAddrCall.frameNonnegB`. -/
  frameNonneg : X86Backend.ImageAddrCall.frameNonnegB body G = true
  /-- The width analysis is dead at each call and at the return. -/
  bitsDead : X86Backend.ImageAddrCallW.bitsDeadB (frameMark (frameNames body))
    (deadTab img outs) body = true

/-- **The checks `calleeChecksB` are the fields of `CalleeChecksOK`.** -/
theorem calleeChecksB_spec {σ : AbiLayout} {nm : String → String} {keep codeOk : Bool}
    {syms : String → Bool} {decodeOk : Bool} {P : LprogIsa.ProcTable} {img : List LinstrRM}
    {dead : (Nat → List String) → Bool} {G : Nat}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} :
    calleeChecksB σ nm keep codeOk syms decodeOk P img dead G sl outs body ref fn = true
      ↔ CalleeChecksOK σ nm keep codeOk syms decodeOk P img dead G sl outs body ref fn := by
  simp only [calleeChecksB, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
      h14⟩, h15⟩, h16⟩, h17⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
      h14⟩, h15⟩, h16⟩, h17⟩

/-- **The checks of a calling body against the callee `c`**: `calleeChecksB` at the pool
    `Callee.keepPool` of `c`, `calleeCodeB`, the symbol of `c`, the decode at the table
    `c.lookup` of `c` (`decodeSites`), the table `c.tab`, the image `ImageAddrCall.callImg` of
    `body` at the call sites `calleeSiteAt c sl body`, `calleeDeadB` and the frame of `c`. -/
def calleeBodyB (σ : AbiLayout) (nm : String → String) (c : CalleeData)
    (sl : String → Option (String × Nat)) (outs : List String) (body : Lcmd)
    (ref : List LinstrRM) (fn : String) : Bool :=
  calleeChecksB σ nm (X86Backend.Callee.keepPoolB c.sig (X86Backend.Callee.keepPool c.sig))
    (calleeCodeB c sl body) (· == c.name) (decodeSites c.lookup sl body).isSome c.tab
    (X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body)
    (fun E => calleeDeadB c sl E body) c.frame sl outs body ref fn

/-- **The checks of a calling body against `c`, as propositions**: `CalleeChecksOK` at the data
    of `calleeBodyB`. The shape of the shadow instructions of the image is then
    `CalleeBodyOK.shapeImg`. -/
abbrev CalleeBodyOK (σ : AbiLayout) (nm : String → String) (c : CalleeData)
    (sl : String → Option (String × Nat)) (outs : List String) (body : Lcmd)
    (ref : List LinstrRM) (fn : String) : Prop :=
  CalleeChecksOK σ nm (X86Backend.Callee.keepPoolB c.sig (X86Backend.Callee.keepPool c.sig))
    (calleeCodeB c sl body) (· == c.name) (decodeSites c.lookup sl body).isSome c.tab
    (X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body)
    (fun E => calleeDeadB c sl E body) c.frame sl outs body ref fn

/-- **The checks `calleeBodyB` are the fields of `CalleeBodyOK`.** -/
theorem calleeBodyB_spec {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} :
    calleeBodyB σ nm c sl outs body ref fn = true ↔ CalleeBodyOK σ nm c sl outs body ref fn :=
  calleeChecksB_spec

/-- **The checks of a calling body against a table**: `calleeChecksB` at the pool
    `CalleeTab.pool`, which passes `Callee.keepPoolB` at each interface, with the symbols of the
    table pairwise distinct; `calleeCodeBT`; the symbols of the table; the decode at the table;
    the table `CalleeTab.tab`; the image `ImageAddrCall.callImg` of `body` at the site function
    `siteFn T.lookup`; `calleeDeadBT` and the frame `CalleeTab.frame`. -/
def calleeBodyBT (σ : AbiLayout) (nm : String → String) (T : CalleeTab)
    (sl : String → Option (String × Nat)) (outs : List String) (body : Lcmd)
    (ref : List LinstrRM) (fn : String) : Bool :=
  calleeChecksB σ nm
    (decide T.names.Nodup && T.fns.all fun c => X86Backend.Callee.keepPoolB c.sig T.pool)
    (calleeCodeBT T sl body) (fun g => T.names.contains g)
    (decodeSites T.lookup sl body).isSome T.tab
    (X86Backend.ImageAddrCall.callImg sl (siteFn T.lookup sl body) body)
    (fun E => calleeDeadBT T sl E body) T.frame sl outs body ref fn

/-- **The checks of a calling body against a table, as propositions**: `CalleeChecksOK` at the
    data of `calleeBodyBT`. -/
abbrev CalleeBodyOKT (σ : AbiLayout) (nm : String → String) (T : CalleeTab)
    (sl : String → Option (String × Nat)) (outs : List String) (body : Lcmd)
    (ref : List LinstrRM) (fn : String) : Prop :=
  CalleeChecksOK σ nm
    (decide T.names.Nodup && T.fns.all fun c => X86Backend.Callee.keepPoolB c.sig T.pool)
    (calleeCodeBT T sl body) (fun g => T.names.contains g)
    (decodeSites T.lookup sl body).isSome T.tab
    (X86Backend.ImageAddrCall.callImg sl (siteFn T.lookup sl body) body)
    (fun E => calleeDeadBT T sl E body) T.frame sl outs body ref fn

/-- **The checks `calleeBodyBT` are the fields of `CalleeBodyOKT`.** -/
theorem calleeBodyBT_spec {σ : AbiLayout} {nm : String → String} {T : CalleeTab}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} :
    calleeBodyBT σ nm T sl outs body ref fn = true ↔ CalleeBodyOKT σ nm T sl outs body ref fn :=
  calleeChecksB_spec

/-- **`calleeBodyBT` at the table of one linked function** is `calleeBodyB`, on a body that
    decodes at the table of the function and ends in the return. -/
theorem calleeBodyBT_one {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} (hd : (decodeSites c.lookup sl body).isSome = true)
    (hl : body.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true) :
    calleeBodyBT σ nm (CalleeTab.one c) sl outs body ref fn
      = calleeBodyB σ nm c sl outs body ref fn := by
  have hsym : ∀ {p : Nat} {bi : Linstr} {ra : Option String} {t : String × LLabel},
      body[p]? = some bi → bi.li_i = .Lcall ra t → t.1 = c.name :=
    fun hb hbi => callsName_of_decode hd hl hb hbi
  have hkeep : (decide (CalleeTab.one c).names.Nodup && (CalleeTab.one c).fns.all fun d =>
        X86Backend.Callee.keepPoolB d.sig (CalleeTab.one c).pool)
      = X86Backend.Callee.keepPoolB c.sig (X86Backend.Callee.keepPool c.sig) := by
    have hf : (CalleeTab.one c).fns = [c] := rfl
    rw [CalleeTab.names_one, hf, CalleeTab.pool_one]
    simp
  have hsyms : (fun g => (CalleeTab.one c).names.contains g) = (· == c.name) := by
    funext g
    by_cases h : g = c.name <;> simp [h]
  have hdead : (fun E => calleeDeadBT (CalleeTab.one c) sl E body)
      = fun E => calleeDeadB c sl E body := by
    funext E
    exact calleeDeadBT_one hsym
  have him : X86Backend.ImageAddrCall.callImg sl (siteFn (CalleeTab.one c).lookup sl body) body
      = X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body :=
    callImg_siteFn_lookup hd
  unfold calleeBodyBT calleeBodyB
  rw [hkeep, calleeCodeBT_one hsym, hsyms, him, hdead, CalleeTab.frame_one]
  rfl

/-- A body that passes the table checks at the table of one linked function and ends in the
    return passes the checks against that function. -/
theorem calleeBodyB_of_one {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String}
    (h : calleeBodyBT σ nm (CalleeTab.one c) sl outs body ref fn = true)
    (hl : body.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true) :
    calleeBodyB σ nm c sl outs body ref fn = true :=
  calleeBodyBT_one (calleeBodyBT_spec.mp h).decode hl ▸ h

/-- **Every shadow instruction of the image is the call of `c` at its call site**: under the
    checks `calleeBodyB`, the image of `body` at the call sites `calleeSiteAt c sl body`
    passes `ImageAddrCall.siteShapeB c.name` (`ImageAddrCall.siteShapeB_callImg`). -/
theorem CalleeBodyOK.shapeImg {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} (h : CalleeBodyOK σ nm c sl outs body ref fn) :
    X86Backend.ImageAddrCall.siteShapeB c.name (calleeSiteAt c sl body)
      (X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body) = true :=
  X86Backend.ImageAddrCall.siteShapeB_callImg _ h.callSites
    (CalleeData.lookup_isSome c ▸ bodyCallSymsB_of_decodeSites h.decode)

/-- **The operands of each call of a callee whose code does not decode are distinct**: under
    the checks `calleeBodyB`, if the code of `c` does not decode, the operands of the call
    site `calleeSiteAt c sl body p` of the call at each position `p` are pairwise distinct
    (`calleeCodeB`). -/
theorem calleeBodyB_nodup {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} (h : calleeBodyB σ nm c sl outs body ref fn = true)
    (hd : decodeLprog c.bytes = none) {p : Nat} {bi : Linstr} (hb : body[p]? = some bi)
    {ra : Option String} {t : String × LLabel} (hbi : bi.li_i = .Lcall ra t) :
    (calleeSiteAt c sl body p).2.Nodup := by
  have hk := (calleeBodyB_spec.mp h).code
  simp only [calleeCodeB, hd, List.all_eq_true, List.mem_range] at hk
  have hp := hk p (List.getElem?_eq_some_iff.mp hb).1
  rw [hb] at hp
  simp only [Option.all_some, hbi, X86Backend.ImageAddrCall.isCallB, Bool.not_true,
    Bool.false_or, decide_eq_true_eq] at hp
  rw [calleeSiteAt_snd]
  exact hp

/-- **The image run of a calling body.** If the printed body `body` passes the checks
    `calleeBodyB` against the reference `ref` at the function name `fn`, every halting run of
    `x86Isa.withProcs` at the table of `c` on `ref`, from a state of `fn` at pc `0` whose
    registers satisfy the entry facts `boundFacts σ nm`, is matched by a halting run of the
    bounds-checked instruction set `CheckedIsaCall.x86IsaK` with that table on the image
    `ImageAddrCall.callImg` of `body` from the same state, the end states agreeing on the
    registers `outs`, the arrays and the word memory. -/
theorem calleeBody_imgRun {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} (h : calleeBodyB σ nm c sl outs body ref fn = true)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ boundFacts σ nm, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : (X86Backend.X86Isa.x86Isa.withProcs c.tab).lsemFuelMemF (singletonProgM fn ref)
      fuel s = some t) :
    ∃ fuel' t', (X86Backend.CheckedIsaCall.x86IsaK.withProcs c.tab).lsemFuelMemF
        (singletonProgM fn
          (X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body))
        fuel' s = some t'
      ∧ X86Backend.OwnedLprogTV.Obs outs t t' := by
  have hok := calleeBodyB_spec.mp h
  exact X86Backend.CalleeSegCheck.calleeSegB_soundK hok.seg
    (calleeCutB_soundK hok.cutRef hok.cutImg outs fn) s t hfn hpc fuel
    (X86Backend.CheckedIsaCall.refRun_checked hok.idx fn s t hfn hpc hent fuel hrun)
    (fun _ _ _ _ _ _ hf => .inl (by
      grind [CalleeData.tab_apply, LprogIsa.ProcSummary.RetWord]))

/-- **The stack room of a calling body.** A printed body `body` that passes the checks
    `calleeBodyB` against the callee `c` passes the stack room check
    `CalleeStackRoom.stackRoomB` of the layout `σ` and the frame check
    `ImageAddrCall.frameNonnegB`, both at the frame of `c`. -/
theorem calleeBody_stackRoom {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} (h : calleeBodyB σ nm c sl outs body ref fn = true) :
    X86Backend.CalleeStackRoom.stackRoomB σ body c.frame = true
      ∧ X86Backend.ImageAddrCall.frameNonnegB body c.frame = true := by
  have hok := calleeBodyB_spec.mp h
  exact ⟨hok.stackRoom, hok.frameNonneg⟩

/-- **The caller separation of a calling body.** Let the printed body `body` pass the checks
    `calleeBodyB` against the callee `c` at the slot map `sl`, let the regions `rs` pass
    `rsOK` at the layout `σ`, let the entry state `sa0` satisfy `σ.Regions`, and let every
    array of `sl` be a region at its length. Then the restricted frame of `body`, the slot
    map `sl` and the entry bases of `σ` are separated (`ImageAddrCall.CallerSep`) from the
    return word of a call at the stack register after the prologue and the frame of `c`
    below it. -/
theorem calleeBody_callerSep {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} (h : calleeBodyB σ nm c sl outs body ref fn = true)
    {rs : List X86Backend.DecodeGenMem.Region} (hrs : X86Backend.DecodeGenNode.rsOK σ rs = true)
    {sa0 : CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState} (hreg : σ.Regions sa0)
    (hsl : ∀ q A n, sl q = some (A, n) → X86Backend.DecodeGenMem.regLen rs A = n) :
    X86Backend.ImageAddrCall.CallerSep
      (X86Backend.ImageAddrFrame.frameIn body
        (X86Backend.DecodePrintedAddr.frameP (X86Backend.LprogBytesDecode.Params.ofBody body)
          (X86Backend.DecodePrintedCFG.frameRsp body sa0)))
      sl (X86Backend.DecodeGenNode.abiBase (X86Backend.DecodeGenNode.abiReg σ) sa0)
      (X86Backend.DecodePrintedCFG.frameRsp body sa0) c.frame :=
  have hr := calleeBody_stackRoom h
  X86Backend.CalleeStackRoom.callerSep_of_regions hrs hreg hr.1 hr.2 hsl

/-- **The destination of an out call at a position is an array of the slot map.** If the
    operands at the position `p` pass `callParamsAtB` against `c` with an out result
    `.out n' k`, and the parameter of `c` at the destination position `k` is an array of `n`
    words, the destination of the call site `calleeSiteAt` at `p` is an array of the slot map
    `sl` of length `n`. -/
theorem calleeSite_destAt {c : CalleeData} {sl : String → Option (String × Nat)}
    {body : Lcmd} {n' k : Nat} (hr : c.res = .out n' k) {p : Nat}
    (h : callParamsAtB c sl body p = true) {po : String}
    {n : Nat} (hd : c.ins[k]? = some (po, .words n)) :
    ∃ q, sl q = some ((calleeSiteAt c sl body p).1, n) := by
  have hp := (callParamsAtB_spec h).1
  obtain ⟨hk, hik⟩ := List.getElem?_eq_some_iff.mp hd
  simp only [calleeSiteAt, hr]
  have hlen := c.siteArgs_length sl body p
  have hk' : k < (c.siteArgs sl body p).length := hlen ▸ hk
  have hmem : (c.ins[k], (c.siteArgs sl body p)[k]) ∈ c.ins.zip (c.siteArgs sl body p) := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp [hlen, hk], by simp⟩
  have hh := hp _ hmem
  rw [hik] at hh
  simp only [paramAtB, Bool.and_eq_true, beq_iff_eq] at hh
  obtain ⟨q, -, hq⟩ := Option.bind_eq_some_iff.mp hh.2
  refine ⟨q, ?_⟩
  rw [hq, List.getD_eq_getElem _ _ hk']

/-- **The destination of an out call is an array of the slot map.** If the dead names of a
    printed body pass `calleeDeadB` against `c` with an out result `.out n' k`, and the
    parameter of `c` at the destination position `k` is an array of `n` words, then at a
    call at the position `p` the destination of the call site `calleeSiteAt` at `p` is an
    array of the slot map `sl` of length `n` (`calleeSite_destAt`). -/
theorem calleeSite_dest {c : CalleeData} {sl : String → Option (String × Nat)}
    {E : Nat → List String} {body : Lcmd} {n' k : Nat} (hr : c.res = .out n' k)
    (h : calleeDeadB c sl E body = true) {p : Nat} {bi : Linstr} (hb : body[p]? = some bi)
    {ra : Option String} {t : String × LLabel} (hbi : bi.li_i = .Lcall ra t) {po : String}
    {n : Nat} (hd : c.ins[k]? = some (po, .words n)) :
    ∃ q, sl q = some ((calleeSiteAt c sl body p).1, n) := by
  simp only [calleeDeadB, hr, Bool.and_eq_true] at h
  refine calleeSite_destAt hr ?_ hd
  simp only [callParamsB, callParamsSelB, List.all_eq_true, List.mem_range] at h
  have hp := h.2 p (List.getElem?_eq_some_iff.mp hb).1
  rw [hb] at hp
  simpa [hbi, X86Backend.ImageAddrCall.isCallB] using hp

/-- **The footprint bound of a callee whose footprint is its frame.** A callee `c` whose
    footprint is the `c.frame` bytes below the entry stack register satisfies
    `ImageAddrCall.FootBelow` at its frame. -/
theorem CalleeData.footBelow_frame {c : CalleeData}
    (h : c.foot = fun s x => X86Backend.Callee.InFrame (s.regs "%rsp") c.frame x) :
    X86Backend.ImageAddrCall.FootBelow c.sig c.frame :=
  X86Backend.CalleeStackRoom.footBelow_inFrame h

/-- **The result copy** of a region export of result type `t`: for a register result under
    a layout whose result is the register `RA`, the returned register paired with the
    export name of `RA`; `none` for every other result. -/
def regionRet (σ : AbiLayout) (nm : String → String) (t : JasminTy) (res : List LOperand) :
    Option (String × String) :=
  match t with
  | .reg _ =>
      match σ.result, res with
      | .reg RA, [op] => some (operandName op, nm RA)
      | _, _ => none
  | _ => none

/-- **The result check** at the result type `t`, against the printed body `body`.

    For `stackArr w m`: `w` is `64`, the layout's result is the `m` words at the register
    `RA`, the export returns one operand, the array it names is the parameter of the
    register `RA`, and the slot of `RA` holds that array at length `m`.

    For `reg w`: `w` is `64`, the layout's result is the register `RA`, the export returns
    one operand, and the export name of `RA` is a general-purpose name with machine register
    `RA` and no frame word in `body`. -/
def regionResultB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (res : List LOperand) : Bool :=
  match t with
  | .stackArr w m =>
      match σ.result, res with
      | .words RA k, [op] =>
          w == 64 && k == m && abiReg σ (operandName op) == some RA
            && slotArrOf σ nm (slotOfReg (nm RA)) == some (operandName op, m)
      | _, _ => false
  | .reg w =>
      match σ.result, res with
      | .reg RA, [_] =>
          w == 64 && gpOk (nm RA) && phys (nm RA) == RA
            && (frameMark (frameNames body) (nm RA)).isNone
      | _, _ => false
  | _ => false

/-- **The result buffer** of the layout `σ` under the export names `nm`: for a result of
    words at the register `RA`, the array parameter of the slot of `RA` with its length
    (`slotArrOf`); `none` for every other result. -/
def regionResBuf (σ : AbiLayout) (nm : String → String) : Option (String × Nat) :=
  match σ.result with
  | .words RA _ => slotArrOf σ nm (slotOfReg (nm RA))
  | _ => none

/-- The names read after the exported code of a region export besides its returned
    operands: the result buffer `regionResBuf σ nm`, when the layout has one. -/
def regionWebsEx (σ : AbiLayout) (nm : String → String) : List String :=
  (regionResBuf σ nm).toList.map Prod.fst

/-- **The exported code at an optional table**: the webs `regionWebs ex r` of the export `r`
    at the array positions `calleeAAT` and the result lengths `calleeAOT` of the table. Both
    arms of `regionBack` take this stage; without a table no symbol has an array position or
    a result length, and the webs are `regionWebs ex r` at its defaults. -/
def regionWebsAt (ex : List String) (callee : Option CalleeTab) (r : Exported) : Exported :=
  regionWebs ex r (calleeAAT callee) (calleeAOT callee)

@[simp] theorem regionWebsAt_none (ex : List String) (r : Exported) :
    regionWebsAt ex none r = regionWebs ex r := rfl

@[simp] theorem regionWebsAt_some (ex : List String) (T : CalleeTab) (r : Exported) :
    regionWebsAt ex (some T) r = regionWebs ex r (calleeAAT (some T)) (calleeAOT (some T)) :=
  rfl

/-- **The result alias of a region export**: without a callee, at a result buffer `D` that is
    a name and one result of array type returned in one operand naming the array `src`, the
    pair `(D, src)`; `none` otherwise. The alias table `resAliasTab` sends the result root of
    `src` to `D`. -/
def resAliasOf (callee : Option CalleeTab) (D : Option String) (ts : List JasminTy)
    (res : List LOperand) : Option (String × String) :=
  match callee, D, ts, res with
  | none, some D, [.stackArr _ _], [op] => if D = "" then none else some (D, operandName op)
  | _, _, _, _ => none

/-- **The alias table at an optional result alias**: the alias table with the result root
    `aliasTabRes outs D src C` at a result alias `(D, src)`, and `aliasTab outs C` without
    one. -/
def resAliasTab (outs : List (String × Nat)) (rr : Option (String × String))
    (C : List LinstrRM) : Std.HashMap String String :=
  match rr with
  | some (D, src) => aliasTabRes outs D src C
  | none => aliasTab outs C

/-- Without a result alias the alias table is `aliasTab` (unfolding lemma of
    `resAliasTab`). -/
@[simp] theorem resAliasTab_none (outs : List (String × Nat)) (C : List LinstrRM) :
    resAliasTab outs none C = aliasTab outs C := rfl

/-- **Code without a zeroing keeps its alias table** at every result alias. -/
theorem resAliasTab_eq_of_noZero (outs : List (String × Nat)) (rr : Option (String × String))
    {C : List LinstrRM} (h : ∀ i ∈ C, zeroDst? i = none) :
    resAliasTab outs rr C = aliasTab outs C := by
  cases rr with
  | none => rfl
  | some p => exact aliasTabRes_eq_of_noZero outs p.1 p.2 h

/-- At a callee there is no result alias (unfolding lemma of `resAliasOf`). -/
@[simp] theorem resAliasOf_some_callee (T : CalleeTab) (D : Option String)
    (ts : List JasminTy) (res : List LOperand) : resAliasOf (some T) D ts res = none := rfl

/-- **The decision of the array result copy** into the result buffer `D`, on the code `code`
    and the returned operands `res` at the result type `t`: for a result of `m < 2 ^ 64`
    words of `64` bits returned in one operand naming the array `src`, when `D` is a name,
    the alias of `src` under the coalescing renaming with the result root
    `chainAliasRes [] D src code` is not `D`, and no version `copyName D (j + 1)`, `j < m`, is
    `src`, the triple `(src, D, m)` of the copy `resCopyCode src D m`; `none` otherwise. At a
    result root of `src` the alias of `src` is `D` (`chainAliasRes_src`), and no copy is
    taken. -/
def resCopyOf (D : String) (t : JasminTy) (code : List LinstrRM) (res : List LOperand) :
    Option (String × String × Nat) :=
  match t, res with
  | .stackArr w m, [op] =>
      if w == 64 && D != ""
          && chainAliasRes [] D (operandName op) code (operandName op) != D
          && decide (m < 2 ^ 64)
          && (List.range m).all (fun j => operandName op != copyName D (j + 1))
      then some (operandName op, D, m) else none
  | _, _ => none

/-- **On code without a zeroing the copy decision reads the coalescing renaming
    `chainAlias code`.** -/
theorem resCopyOf_eq_of_noZero (D : String) (t : JasminTy) {code : List LinstrRM}
    (res : List LOperand) (h : ∀ i ∈ code, zeroDst? i = none) :
    resCopyOf D t code res =
      match t, res with
      | .stackArr w m, [op] =>
          if w == 64 && D != "" && chainAlias code (operandName op) != D
              && decide (m < 2 ^ 64)
              && (List.range m).all (fun j => operandName op != copyName D (j + 1))
          then some (operandName op, D, m) else none
      | _, _ => none := by
  unfold resCopyOf
  split
  · rw [chainAliasRes_eq_of_noZero [] D _ h]; rfl
  · rfl

/-- **The array result copy of a region export**: without a callee, the decision `resCopyOf`
    at the result buffer `regionResBuf σ nm` when its length is that of the copy; `none` at a
    callee and when the layout has no result buffer. -/
def regionCopy (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (callee : Option CalleeTab) (code : List LinstrRM) (res : List LOperand) :
    Option (String × String × Nat) :=
  match callee, regionResBuf σ nm with
  | none, some (D, n) => (resCopyOf D t code res).filter fun c => c.2.2 == n
  | _, _ => none

/-- At a callee there is no array result copy. -/
@[simp] theorem regionCopy_some_callee (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (T : CalleeTab) (code : List LinstrRM) (res : List LOperand) :
    regionCopy σ nm t (some T) code res = none := rfl

/-- **The facts of an array result copy.** A copy `(src, D, m)` chosen by `regionCopy` is
    taken without a callee, at a result type of `m < 2 ^ 64` words of `64` bits returned in
    one operand naming `src`; `D` is the argument name of a parameter of `m` words of `σ`,
    and no version `copyName D (j + 1)`, `j < m`, is `src`. -/
theorem regionCopy_some {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {callee : Option CalleeTab} {code : List LinstrRM} {res : List LOperand}
    {src D : String} {m : Nat} (h : regionCopy σ nm t callee code res = some (src, D, m)) :
    callee = none ∧ t = .stackArr 64 m ∧ (∃ op, res = [op] ∧ operandName op = src)
      ∧ (∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j)
      ∧ m < 2 ^ 64 ∧ (∀ i, i < m → src ≠ copyName D (i + 1)) := by
  unfold regionCopy at h
  split at h
  · rename_i D' n hb
    simp only [Option.filter_eq_some_iff, beq_iff_eq] at h
    obtain ⟨hc, hn⟩ := h
    unfold resCopyOf at hc
    split at hc
    · rename_i w m' op
      split at hc
      · rename_i hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
          List.mem_range, bne_iff_ne, ne_eq] at hcond
        obtain ⟨⟨⟨⟨rfl, -⟩, -⟩, hm⟩, hfr⟩ := hcond
        refine ⟨rfl, rfl, ⟨op, rfl, rfl⟩, ?_, hm, fun i hi => hfr i hi⟩
        unfold regionResBuf at hb
        split at hb
        · obtain ⟨j, a, hj, hk, hA, -⟩ := slotArrOf_some hb
          subst hn
          exact ⟨j, a, hj, hk, hA⟩
        · cases hb
      · cases hc
    · cases hc
  · cases h

/-- The result buffer `D` of an array result copy `(src, D, m)` chosen by `regionCopy` is
    among the names `regionWebsEx σ nm`. -/
theorem regionCopy_mem_regionWebsEx {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {callee : Option CalleeTab} {code : List LinstrRM} {res : List LOperand}
    {src D : String} {m : Nat} (h : regionCopy σ nm t callee code res = some (src, D, m)) :
    D ∈ regionWebsEx σ nm := by
  unfold regionCopy at h
  split at h
  · rename_i D' n hb
    simp only [Option.filter_eq_some_iff] at h
    obtain ⟨hc, -⟩ := h
    unfold resCopyOf at hc
    split at hc
    · split at hc
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨-, rfl, -⟩ := hc
        simp [regionWebsEx, hb]
      · cases hc
    · cases hc
  · cases h

/-- The returned operands after the array result copy `cp`: the operand of the last version
    `copyName D m` of the result buffer after a copy `(src, D, m)`, and `res` without a
    copy. -/
def regionOut : Option (String × String × Nat) → List LOperand → List LOperand
  | none, res => res
  | some (_, D, m), _ => [.reg (copyName D m)]

/-- The exported code followed by the result copy `regionRet` and, at an array result copy
    `cp`, the copy `resCopyCode`. -/
def regionCoCode (σ : AbiLayout) (nm : String → String) (t : JasminTy) (code : List LinstrRM)
    (res : List LOperand) (cp : Option (String × String × Nat) := none) : List LinstrRM :=
  match cp with
  | none => code ++ movesOf (regionRet σ nm t res).toList
  | some (src, D, m) => code ++ movesOf (regionRet σ nm t res).toList ++ resCopyCode src D m

/-- The array names read after the code: the returned names of an array result. -/
def regionCoObs (t : JasminTy) (res : List LOperand) : List String :=
  match t with
  | .stackArr _ _ => res.map operandName
  | _ => []

/-- **The alias table of a region export** on the code `C`: `resAliasTab` at the out symbols
    `calleeOutsT` of the optional table and the result alias `resAliasOf` of the result
    buffer `regionResBuf σ nm` and the returned operands `res` at the result type `t`. -/
def regionAliasTab (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (callee : Option CalleeTab) (res : List LOperand) (C : List LinstrRM) :
    Std.HashMap String String :=
  resAliasTab (calleeOutsT callee) (resAliasOf callee ((regionResBuf σ nm).map Prod.fst) [t] res) C

/-- The coalescing renaming of a region export without a callee: the lookup in
    `regionAliasTab`. On code without a zeroing it is `chainAlias C`
    (`regionAliasN_eq_of_noZero`). -/
abbrev regionAliasN (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (res : List LOperand) (C : List LinstrRM) : String → String :=
  canonMemrefName (regionAliasTab σ nm t none res C)

/-- At a table the alias table of a region export is `aliasTab` at the out symbols of the
    table. -/
@[simp] theorem regionAliasTab_some (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (T : CalleeTab) (res : List LOperand) (C : List LinstrRM) :
    regionAliasTab σ nm t (some T) res C = aliasTab (calleeOutsT (some T)) C := rfl

/-- **Code without a zeroing keeps its alias table** in a region export. -/
theorem regionAliasTab_eq_of_noZero (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (callee : Option CalleeTab) (res : List LOperand) {C : List LinstrRM}
    (h : ∀ i ∈ C, zeroDst? i = none) :
    regionAliasTab σ nm t callee res C = aliasTab (calleeOutsT callee) C :=
  resAliasTab_eq_of_noZero _ _ h

/-- On code without a zeroing the coalescing renaming of a region export is `chainAlias`. -/
theorem regionAliasN_eq_of_noZero (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (res : List LOperand) {C : List LinstrRM} (h : ∀ i ∈ C, zeroDst? i = none) :
    regionAliasN σ nm t res C = chainAlias C := by
  rw [regionAliasN, regionAliasTab_eq_of_noZero σ nm t none res h]; rfl

/-- The coalesced code: `regionCoCode` with its array versions merged by the alias table
    `regionAliasTab`, applied at the array positions of each instruction (`renArr`): the
    alias map `chainAliasO` at the out symbols `calleeOutsT` of the optional table, which
    without a table also sends the result root of the returned array to the result buffer.
    The code carries the array result copy `regionCopy`. -/
def regionCoBody (σ : AbiLayout) (nm : String → String) (t : JasminTy) (code : List LinstrRM)
    (res : List LOperand) (callee : Option CalleeTab := none) : List LinstrRM :=
  (regionCoCode σ nm t code res (regionCopy σ nm t callee code res)).map
    (renArr (canonMemrefName (regionAliasTab σ nm t callee res
      (regionCoCode σ nm t code res (regionCopy σ nm t callee code res)))))

/-- The result copies of a region export add no zeroing: every zeroing of the code with the
    result copies `regionCoCode` is one of the exported code. -/
theorem regionCoCode_noZero (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    {code : List LinstrRM} (res : List LOperand) (cp : Option (String × String × Nat))
    (h : ∀ i ∈ code, zeroDst? i = none) :
    ∀ i ∈ regionCoCode σ nm t code res cp, zeroDst? i = none := by
  have hmv : ∀ ps : List (String × String), ∀ i ∈ movesOf ps, zeroDst? i = none := by
    intro ps i hi; obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi; rfl
  have hcp : ∀ src D m, ∀ i ∈ resCopyCode src D m, zeroDst? i = none := by
    intro src D m i hi
    simp only [resCopyCode, List.mem_flatMap] at hi
    obtain ⟨j, -, hj⟩ := hi
    simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> rfl
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · simp only [List.mem_append] at hi
    rcases hi with hi | hi
    · exact h i hi
    · exact hmv _ i hi
  · simp only [List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact h i hi
    · exact hmv _ i hi
    · exact hcp _ _ _ i hi

/-- **On code without a zeroing the coalesced code is renamed by the alias table
    `aliasTab`** at the out symbols of the optional callee. -/
theorem regionCoBody_eq_of_noZero (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    {code : List LinstrRM} (res : List LOperand) (callee : Option CalleeTab)
    (h : ∀ i ∈ code, zeroDst? i = none) :
    regionCoBody σ nm t code res callee =
      (regionCoCode σ nm t code res (regionCopy σ nm t callee code res)).map
        (renArr (canonMemrefName (aliasTab (calleeOutsT callee)
          (regionCoCode σ nm t code res (regionCopy σ nm t callee code res))))) := by
  rw [regionCoBody, regionAliasTab_eq_of_noZero σ nm t callee res
    (regionCoCode_noZero σ nm t res _ h)]

/-- The code has a site of the multiplication fusion: `fuseLo` assigns a low destination
    to one of its positions, a high multiplication `MULXHI` after a low multiplication of
    the same second source. -/
def fuseSites (L : List LinstrRM) : Bool := (fuseLo L).any Option.isSome

/-- **The multiplication fusion as a step of the reference**: `fuseMulHiRM` on code with a
    site of the fusion (`fuseSites`); code without a site is unchanged. -/
def regionFuse (L : List LinstrRM) : List LinstrRM :=
  if fuseSites L then fuseMulHiRM L else L

/-- The name `x` is the argument name `argName j` of a parameter `j` of the layout `σ`. -/
def isArgNameB (σ : AbiLayout) (x : String) : Bool :=
  (List.range σ.args.length).any fun j => argName j == x

/-- **The pairs of the renaming from an allocation certificate**: the pairs of `cert` whose
    first component is an argument name `argName j` of the layout, the names that
    `argBind` binds at the entry. -/
def certArgs (σ : AbiLayout) (cert : List (String × String)) : List (String × String) :=
  cert.filter fun p => isArgNameB σ p.1

/-- **The pieces of a list of instructions between the calls**: each piece ends at a shadow
    instruction of a call (`LprogIsa.shadowCall?`), and the last piece holds the instructions
    after the last call. -/
def callPieces (l : List LinstrRM) : List (List LinstrRM) :=
  l.foldr (fun i acc =>
    if (LprogIsa.shadowCall? i.1).isSome then [i] :: acc
    else match acc with
      | p :: ps => (i :: p) :: ps
      | [] => [[i]]) [[]]

/-- A list of instructions without a call is one piece. -/
theorem callPieces_of_noCall {l : List LinstrRM}
    (h : ∀ i ∈ l, LprogIsa.shadowCall? i.1 = none) : callPieces l = [l] := by
  induction l with
  | nil => rfl
  | cons i t ih =>
      have ht := ih fun j hj => h j (List.mem_cons_of_mem i hj)
      unfold callPieces at ht ⊢
      simp [List.foldr_cons, ht, h i List.mem_cons_self]

/-- **The names whose location an image check compares at a boundary**: the names some piece
    `callPieces` of a block of `src` reads as registers before it writes them. A block
    boundary and a call are the boundaries: the check of a calling body compares the names
    live at a call at the end of one segment and the start of the next. -/
def crossNames (src : List LinstrRM) : List String :=
  match cfgOf (src.map Prod.fst) with
  | some G =>
      ((List.range G.blocks.size).flatMap fun k =>
        (callPieces ((src.drop (G.blk k).start).take
          ((G.blk k).stop - (G.blk k).start))).flatMap fun p =>
            regExposed (p.map Prod.fst)).eraseDups
  | none => []

/-- **The merge pairs from an allocation certificate**: the pairs of `cert` whose first
    component is a name of `X`, no argument name, no hardware register name
    (`isHwRegName`), no frame-slot name (`isFrameSlotName`), not the liveness pseudo-name
    `%livepin` and no name of the array names `arrs`. At `X := crossNames` of the
    reference these are the names some block reads before it writes them, the names whose
    location the image check compares at a block boundary. -/
def certMerge (σ : AbiLayout) (arrs X : List String) (cert : List (String × String)) :
    List (String × String) :=
  cert.filter fun p => X.contains p.1 && !isArgNameB σ p.1 && !isHwRegName p.1
    && !isFrameSlotName p.1 && p.1 != "%livepin" && !arrs.contains p.1

/-- **The cell arrays of a region export** against the printed body `body`, at the pairs
    `ps` and the code `code` behind the prefix of the reference. With
    `c := cellArrsOf (slotArrOf σ nm) (cellArrs σ) body`, the word-array parameters of the
    layout whose cells the printed body accesses: no array when `c` is empty, and otherwise
    each word-array parameter `p` of the layout that is in `c`, or that `code` names under
    the pairs and that the cell fold `CellFoldLReg.cellFoldLR` at `p` alone accepts on
    `code` (`code` accesses `p` at known indices only), under the name renamed by `ps`. An
    array of the second kind is one whose accesses the allocated program has removed, the
    loads of an operand that the code reads and never uses. -/
def regionCells (σ : AbiLayout) (nm : String → String) (ps : List (String × String))
    (body : Lcmd) (code : List LinstrRM) : Slots :=
  let c := cellArrsOf (slotArrOf σ nm) (X86Backend.ImageStraightCells.cellArrs σ) body
  if c.isEmpty then []
  else ((X86Backend.ImageStraightCells.cellArrs σ).filter fun p =>
      c.contains p || ((arrNames code).contains (renOf ps p.1)
        && (cellFoldLR [(renOf ps p.1, p.2)] [] code).isSome)).map
      fun p => (renOf ps p.1, p.2)

/-- On a printed body with no cell access there is no cell array. -/
theorem regionCells_of_cellFreeB (σ : AbiLayout) (nm : String → String)
    (ps : List (String × String)) {body : Lcmd} (code : List LinstrRM)
    (h : cellFreeB body = true) : regionCells σ nm ps body code = [] := by
  unfold regionCells
  rw [cellArrsOf_of_cellFreeB _ _ h]
  rfl

/-- The cell arrays are among the cell arrays of the layout under the renaming by the
    pairs. -/
theorem regionCells_sub (σ : AbiLayout) (nm : String → String) (ps : List (String × String))
    (body : Lcmd) (code : List LinstrRM) :
    ∀ p ∈ regionCells σ nm ps body code, p ∈ cellArrsR σ ps := by
  intro p hp
  unfold regionCells at hp
  dsimp only at hp
  split_ifs at hp
  · cases hp
  · obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
    exact List.mem_map.mpr ⟨p0, (List.mem_filter.mp hp0).1, rfl⟩

/-- **The parts of the reference of a region export** against a printed body: the targets
    `outs` of the result copy; the pairs `ps` of the renaming; the prefix `pre`, the copies
    of the parameter registers and of the pairs; the coalesced code `ren` renamed by the
    pairs; the renamed aliases `obs` of the returned array names; the register liveness
    table `live` of `pre ++ ren` and the array names `arrs` of the register merge; the
    merge pairs `tau`; the code `merged`, `ren` with
    its register names merged by `tau`; the register liveness table `liveM` of
    `pre ++ merged` with its array names `arrsM`; the code `nop`, `pre ++ merged` without
    the effect of its array self-moves; the flag `sites`, whether the code of `nop` behind
    the prefix has a site of the multiplication fusion; the code `fused`, `nop` with that
    code fused when `sites` holds; the cell arrays `cells` of the printed body under the
    renamed names; the cell names `cellOuts` of the returned arrays among them; and the
    reference `ref` of the image check, `fused` with the code behind the prefix folded onto
    the cells of `cells` when there is a cell array. -/
structure CoParts where
  /-- The targets of the result copy. -/
  outs : List String
  /-- The pairs of the renaming. -/
  ps : List (String × String)
  /-- The copies of the parameter registers and of the pairs. -/
  pre : List LinstrRM
  /-- The coalesced code renamed by the pairs. -/
  ren : List LinstrRM
  /-- The renamed aliases of the returned array names. -/
  obs : List String
  /-- The register liveness table of `pre ++ ren`. -/
  live : Array (List String)
  /-- The array names of the register merge. -/
  arrs : List String
  /-- The merge pairs. -/
  tau : List (String × String)
  /-- The renamed code with its register names merged. -/
  merged : List LinstrRM
  /-- The register liveness table of `pre ++ merged`. -/
  liveM : Array (List String)
  /-- The array names of `merged`. -/
  arrsM : List String
  /-- The code `pre ++ merged` without the effect of its array self-moves. -/
  nop : List LinstrRM
  /-- The code of `nop` behind the prefix has a site of the multiplication fusion. -/
  sites : Bool
  /-- The code `nop` with its code behind the prefix fused at the sites. -/
  fused : List LinstrRM
  /-- The cell arrays of the printed body, under the renamed names. -/
  cells : Slots
  /-- The cell names of the returned arrays that are cell arrays. -/
  cellOuts : List String
  /-- The reference of the image check. -/
  ref : List LinstrRM
  /-- The array positions of the called symbols. -/
  aa : String → Nat → Option Nat := fun _ _ => none
  /-- The result lengths of the called symbols. -/
  ao : String → Option Nat := fun _ => none

/-- **The parts of the reference** of a region export with the code `code` and the returned
    operands `res`, at the result type `t`, against the printed body `body`, at the
    allocation certificate `cert`, the pairs of a name of the allocated code and its
    location. The pairs are `certArgs σ cert`, the certificate at the argument names; the
    prefix is the copies of the parameter registers and of the pairs; the renamed code is
    the coalesced code `regionCoBody` under the pairs. The liveness tables are
    `liveRegTab` with the targets of the result copy read after the body. The array names
    are those of the code (`arrNames`), those of its calls (`callArrNames`) at the array
    positions `calleeAAT callee` and the result lengths `calleeAOT callee`, which the parts
    record, and the renamed alias of each returned array name. The merge pairs are
    `certMerge σ arrs (crossNames (pre ++ ren)) cert`, the certificate at the other names
    that some block of `pre ++ ren` reads before it writes them, without the array names;
    the check `regionMergeB` checks them by `regCoB`. A name that every block writes before
    it reads it keeps its name: within a block the image check compares values, not
    locations, and the allocation input has the liveness instructions of `pinSelfMoves` at
    the positions of the array self-moves that the reference keeps until `selfNop`. An
    allocation that gives one machine
    register to two names of the export with disjoint live ranges is a merge of the two
    names into that register.

    The code `nop` is `selfNop` of `pre ++ merged` behind the prefix, at the table `liveM`:
    the export moves a carried array at the entry and the exit of a region; after the
    coalescing such a move is a load and a store of one word of one array, and the
    allocation input has liveness instructions in their place (`pinSelfMoves`). The code
    `fused` is `nop` when its code
    behind the prefix has no site of the multiplication fusion (`fuseSites`), and otherwise
    the prefix followed by the fusion `fuseMulHiRM` of that code: a high multiplication
    `MULXHI` has no bytes of its own, and the allocated program carries the two-output
    `MULX` of the post-pass `regionPostFuse` in its place.

    The cell arrays `cells` are `regionCells` at the code of `fused` behind the prefix: the
    word-array parameters of the layout whose cells the printed body accesses
    (`cellArrsOf`), and, when there is one, the parameters that code accesses at known
    indices only, under the names renamed by the pairs: the owned back end prints an access
    of an array at a literal index as an access of a cell at a constant displacement
    (`ConstIndexFold.foldIndexedLprog`) and removes a load whose value is never used. The
    reference `ref` is `fused` when there is no cell array, and otherwise the prefix followed by the cell fold
    `CellFoldLReg.cellFoldLR` of the code of `fused` behind the prefix, which reads and
    writes an array of `cells` at a known index through its cell name; the code itself
    where the fold refuses, which the check `regionFoldB` excludes. The fold covers an
    array that is accessed at literal indices only: it refuses an access of a cell array at
    an index that is not a known constant, so a body that indexes one array by a loop
    counter and at literal indices is refused. The names `cellOuts` are the cell names of
    the arrays of `cells` among the renamed aliases of the returned array names.

    At a table, `code` is the exported code on the common names of the table
    (`calleeCodeT`). -/
def regionCoParts (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab := none) : CoParts :=
  let outs := (regionRet σ nm t res).toList.map Prod.snd
  let ps := certArgs σ cert
  let pre := argBind σ nm ++ movesOf ps
  let ren := (regionCoBody σ nm t code res callee).map (renRM (renOf ps))
  let cp := regionCopy σ nm t callee code res
  let ρ := canonMemrefName (regionAliasTab σ nm t callee res (regionCoCode σ nm t code res cp))
  let obsA := (regionCoObs t (regionOut cp res)).map fun A => renOf ps (ρ A)
  let live := liveRegTab (pre ++ ren) outs
  let aa := calleeAAT callee
  let ao := calleeAOT callee
  let arrs := arrNames ren ++ callArrNames aa ao ren ++ obsA
  let tau := certMerge σ arrs (crossNames (pre ++ ren)) cert
  let merged := ren.map (renRM (renOf tau))
  let liveM := liveRegTab (pre ++ merged) outs
  let nop := selfNop pre.length (liveAt (tabAt liveM) (pre ++ merged).length) (pre ++ merged)
  let sites := fuseSites (nop.drop pre.length)
  let fused := if sites then pre ++ fuseMulHiRM (nop.drop pre.length) else nop
  let cells : Slots := regionCells σ nm ps body (fused.drop pre.length)
  { outs := outs, ps := ps, pre := pre, ren := ren, obs := obsA, live := live, arrs := arrs,
    tau := tau, merged := merged, liveM := liveM,
    arrsM := arrNames merged ++ callArrNames aa ao merged ++ obsA, nop := nop, sites := sites, fused := fused,
    cells := cells,
    cellOuts := cells.flatMap fun p =>
      if obsA.contains p.1 then X86Backend.ImageAddrRouteW.outCells p.1 p.2 else [],
    ref := if cells.isEmpty then fused
      else pre ++ (cellFoldLR cells [] (fused.drop pre.length)).getD (fused.drop pre.length),
    aa := aa, ao := ao }

/-- **On a printed body with no cell access the parts have no cell array**, no observed
    cell name, and the reference is the code `fused`. -/
theorem regionCoParts_of_cellFreeB (σ : AbiLayout) (nm : String → String) {body : Lcmd}
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab)
    (h : cellFreeB body = true) :
    (regionCoParts σ nm body t code res cert callee).cells = []
      ∧ (regionCoParts σ nm body t code res cert callee).cellOuts = []
      ∧ (regionCoParts σ nm body t code res cert callee).ref
        = (regionCoParts σ nm body t code res cert callee).fused := by
  have hc : (regionCoParts σ nm body t code res cert callee).cells = [] := by
    exact regionCells_of_cellFreeB σ nm _ _ h
  refine ⟨hc, ?_, ?_⟩
  · show ((regionCoParts σ nm body t code res cert callee).cells.flatMap _) = []
    rw [hc]
    rfl
  · show (if (regionCoParts σ nm body t code res cert callee).cells.isEmpty then _ else _) = _
    rw [hc]
    rfl

/-- The cell arrays of the parts are among the cell arrays of the layout under the
    renaming by the pairs. -/
theorem regionCoParts_cells_sub (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab) :
    ∀ p ∈ (regionCoParts σ nm body t code res cert callee).cells,
      p ∈ cellArrsR σ (regionCoParts σ nm body t code res cert callee).ps :=
  regionCells_sub σ nm _ body _

/-- **The check of the cell fold** of the parts `d`: there is no cell array, or the code
    of `d.fused` behind the prefix has a cell fold `CellFoldLReg.cellFoldLR` at the cell
    arrays `d.cells`, and no source or target of the pairs is a cell name. -/
def regionFoldB (d : CoParts) : Bool :=
  d.cells.isEmpty
    || ((cellFoldLR d.cells [] (d.fused.drop d.pre.length)).isSome
      && d.ps.all fun p => !isCellB d.cells p.1 && !isCellB d.cells p.2)

/-- **The check of the register merge** of the parts `d`: there is no merge pair, or the
    merge `d.tau` passes `regCoB` at the table `d.live`, the array names `d.arrs` and the
    calls `d.aa`, `d.ao`, and each target of the result copy is live at the end of the body and fixed by the
    merge. -/
def regionMergeB (d : CoParts) : Bool :=
  d.tau == []
    || (regCoB (renOf d.tau) d.pre d.ren (tabAt d.live) d.arrs d.aa d.ao
      && d.outs.all fun y =>
        (tabAt d.live (d.pre ++ d.ren).length).contains y && renOf d.tau y == y)

/-- **The coalesced, renamed and merged code** of the parts `d`: the prefix followed by
    the merged code. -/
def regionCoRef (d : CoParts) : List LinstrRM := d.pre ++ d.merged

/-- **The check of the liveness table of `regionCoRef`**: the identity merge passes
    `regCoB` on the merged code behind the prefix at the table `d.liveM`, the array names
    `d.arrsM` and the calls `d.aa`, `d.ao`, and each target of the result copy is live at the end of the body. -/
def regionNopB (d : CoParts) : Bool :=
  regCoB id d.pre d.merged (tabAt d.liveM) d.arrsM d.aa d.ao
    && d.outs.all fun y => (tabAt d.liveM (d.pre ++ d.merged).length).contains y

/-- **The check of the multiplication fusion** of the parts `d`, with the registers `E` of
    width `64` at the entry: the code of `d.nop` behind the prefix has no site of the
    fusion, or the code passes the fusion check `fuseOKL` with the fusion behind the
    prefix, and the renamed alias of each returned array name and each target of the
    result copy is a name other than `R15`, which the fused code changes. -/
def regionSitesB (E : List String) (d : CoParts) : Bool :=
  !d.sites
    || (fuseOKL E (fuseLoPre d.pre (d.nop.drop d.pre.length))
        (d.pre ++ d.nop.drop d.pre.length)
      && d.obs.all (fun A => A != "R15") && d.outs.all (fun y => y != "R15"))

/-- **The check of the reference** of a region export with the code `code` and the
    returned operands `res`, at the result type `t`, against the printed body `body`. With
    `C := regionCoCode`, the alias map `ρ` of the alias table `regionAliasTab` (the map
    `chainAliasO (calleeOutsT callee) C`, which without a table also sends the result root
    of the returned array to the result buffer), the liveness certificate
    `liveArrCert C` of the returned array names and the pairs `ps := certArgs σ cert` of
    the allocation certificate `cert`: `C` is in
    the covered instruction classes; `C` passes the coalescing check `coCfgB` of `ρ`, and
    `ρ` fixes the array names live at the entry; the pairs pass the renaming check `renB`
    on the coalesced code; the alias of each returned array name is a name of the coalesced
    code; the target of the result copy is a name of the coalesced code that `ps` fixes;
    the returned operands under `ρ` pass `regionResultB`; the register merge of the parts
    `d := regionCoParts` passes `regionMergeB`; the liveness table of the merged code
    passes `regionNopB`; the multiplication fusion passes `regionSitesB` at the registers
    `fuseRegs`; the cell fold passes `regionFoldB`; and, under `ps`, at the cell arrays
    `d.cells` and observing the target of the result copy and the cell names `d.cellOuts`,
    the image check `renImageB` accepts the reference `d.ref`. The array liveness table and
    the parts are computed once, the parts after the first three conjuncts. On a printed
    body with no cell access there is no cell array, and the gate is its conjuncts without
    the cell fold (`regionCoB_of_cellFreeB`).

    At a table `T` the code of every conjunct above is the exported code on the common
    names of `T` (`calleeCodeT`), the parts and the image check are taken at the image
    `calleeImgT` of a calling body, and two conjuncts are added: the symbols of `T` are
    distinct, the rewriting `LprogCallCut.commonCallsT?` accepts the exported code and the code
    with the result copy passes `LprogCallCut.commonFreshT` at the names of `T`; and the printed
    body
    passes the checks `calleeBodyBT` of a calling body against the reference at the function
    name `fn` and has no cell array. Each is of the form `callee.all _`, which holds without
    a table, at every `fn`. A body that passes the gate at a table is covered by no
    correctness theorem: `regionCo_bytes` is stated without a table.

    The code `C` carries the array result copy `cp := regionCopy`, and the returned names
    are those after it (`regionOut`): with a copy into the result buffer, the last version
    of the buffer. -/
def regionCoB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab := none) (fn : String := "") : Bool :=
  let codeC := calleeCodeT callee code
  let cp := regionCopy σ nm t callee codeC res
  let C := regionCoCode σ nm t codeC res cp
  let ρ := canonMemrefName (regionAliasTab σ nm t callee res C)
  let obs := regionCoObs t (regionOut cp res)
  let LA := liveArrTab C obs (calleeAAT callee) (calleeAOT callee)
  callee.all (fun T => decide T.names.Nodup
      && (LprogCallCut.commonCallsT? T.common code).isSome
      && LprogCallCut.commonFreshT T.common T.names (regionCoCode σ nm t code res))
    && C.all (fun i => clsB i && mulxFree i)
    && coCfgB ρ C (tabAt LA) obs (calleeAAT callee) (calleeAOT callee)
    && (tabAt LA 0).all (fun x => ρ x == x)
    && (let d := regionCoParts σ nm body t codeC res cert callee
      callee.all (fun T =>
          calleeBodyBT σ nm T (slotRen (slotArrOf σ nm) (renOf d.ps)) d.outs body d.ref fn
            && d.cells.isEmpty)
        && renB σ nm [] (regionCoBody σ nm t codeC res callee) d.ps
        && obs.all (fun A => (loopNames (regionCoBody σ nm t codeC res callee)).contains
          (ρ A))
        && (regionRet σ nm t res).toList.all (fun p =>
          (loopNames (regionCoBody σ nm t codeC res callee)).contains p.2
            && renOf d.ps p.2 == p.2)
        && regionResultB σ nm body t ((regionOut cp res).map fun op =>
          .reg (ρ (operandName op)))
        && regionMergeB d
        && regionNopB d
        && regionSitesB (fuseRegs σ nm) d
        && regionFoldB d
        && renImageB σ nm d.ps d.cells (d.outs ++ d.cellOuts) body d.ref callee)

/-- The code with the result copies of a region export without a callee: `regionCoCode` at
    the array result copy `regionCopy`. -/
abbrev regionCoCodeN (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) : List LinstrRM :=
  regionCoCode σ nm t code res (regionCopy σ nm t none code res)

/-- The coalesced code of a region export without a callee at the array result copy `cp`:
    `regionCoCode` at `cp` renamed at its array positions by its alias map `regionAliasN`.
    Without a callee `regionCoBody` is this code at `regionCopy`. -/
abbrev regionCoBodyC (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cp : Option (String × String × Nat)) :
    List LinstrRM :=
  (regionCoCode σ nm t code res cp).map
    (renArr (regionAliasN σ nm t res (regionCoCode σ nm t code res cp)))

/-- The returned operands after the array result copy of a region export without a callee. -/
abbrev regionOutN (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) : List LOperand :=
  regionOut (regionCopy σ nm t none code res) res

/-- **Without a callee the gate is the conjunction of its conjuncts on the exported
    code**, with the image check at the image `virtImg`. -/
theorem regionCoB_none (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String)) :
    regionCoB σ nm body t code res cert =
      ((regionCoCodeN σ nm t code res).all (fun i => clsB i && mulxFree i)
        && coCfgB (regionAliasN σ nm t res (regionCoCodeN σ nm t code res)) (regionCoCodeN σ nm t code res)
          (tabAt (liveArrTab (regionCoCodeN σ nm t code res)
            (regionCoObs t (regionOutN σ nm t code res))))
          (regionCoObs t (regionOutN σ nm t code res))
        && (tabAt (liveArrTab (regionCoCodeN σ nm t code res)
            (regionCoObs t (regionOutN σ nm t code res))) 0).all
          (fun x => regionAliasN σ nm t res (regionCoCodeN σ nm t code res) x == x)
        && (renB σ nm [] (regionCoBody σ nm t code res) (regionCoParts σ nm body t code res cert).ps
          && (regionCoObs t (regionOutN σ nm t code res)).all (fun A =>
            (loopNames (regionCoBody σ nm t code res)).contains
              (regionAliasN σ nm t res (regionCoCodeN σ nm t code res) A))
          && (regionRet σ nm t res).toList.all (fun p =>
            (loopNames (regionCoBody σ nm t code res)).contains p.2
              && renOf (regionCoParts σ nm body t code res cert).ps p.2 == p.2)
          && regionResultB σ nm body t ((regionOutN σ nm t code res).map fun op =>
            .reg (regionAliasN σ nm t res (regionCoCodeN σ nm t code res) (operandName op)))
          && regionMergeB (regionCoParts σ nm body t code res cert)
          && regionNopB (regionCoParts σ nm body t code res cert)
          && regionSitesB (fuseRegs σ nm) (regionCoParts σ nm body t code res cert)
          && regionFoldB (regionCoParts σ nm body t code res cert)
          && renImageB σ nm (regionCoParts σ nm body t code res cert).ps
            (regionCoParts σ nm body t code res cert).cells
            ((regionCoParts σ nm body t code res cert).outs
              ++ (regionCoParts σ nm body t code res cert).cellOuts) body
            (regionCoParts σ nm body t code res cert).ref)) := rfl

/-- **Without a callee the gate does not read the function name.** -/
theorem regionCoB_none_fn (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String)) (fn : String) :
    regionCoB σ nm body t code res cert none fn = regionCoB σ nm body t code res cert := by
  simp only [regionCoB, Option.all]

/-- **On a printed body with no cell access the gate is the conjunction of its conjuncts
    without the cell fold**: the image check is taken at the renamed slot map, the printed
    body and the targets of the result copy, at no cell array, where the reference is the
    code `fused` of the parts (`regionCoParts_of_cellFreeB`). -/
theorem regionCoB_of_cellFreeB (σ : AbiLayout) (nm : String → String) {body : Lcmd}
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (h : cellFreeB body = true) :
    regionCoB σ nm body t code res cert =
      ((regionCoCodeN σ nm t code res).all (fun i => clsB i && mulxFree i)
        && coCfgB (regionAliasN σ nm t res (regionCoCodeN σ nm t code res)) (regionCoCodeN σ nm t code res)
          (tabAt (liveArrTab (regionCoCodeN σ nm t code res)
            (regionCoObs t (regionOutN σ nm t code res))))
          (regionCoObs t (regionOutN σ nm t code res))
        && (tabAt (liveArrTab (regionCoCodeN σ nm t code res)
            (regionCoObs t (regionOutN σ nm t code res))) 0).all
          (fun x => regionAliasN σ nm t res (regionCoCodeN σ nm t code res) x == x)
        && (renB σ nm [] (regionCoBody σ nm t code res) (regionCoParts σ nm body t code res cert).ps
          && (regionCoObs t (regionOutN σ nm t code res)).all (fun A =>
            (loopNames (regionCoBody σ nm t code res)).contains
              (regionAliasN σ nm t res (regionCoCodeN σ nm t code res) A))
          && (regionRet σ nm t res).toList.all (fun p =>
            (loopNames (regionCoBody σ nm t code res)).contains p.2
              && renOf (regionCoParts σ nm body t code res cert).ps p.2 == p.2)
          && regionResultB σ nm body t ((regionOutN σ nm t code res).map fun op =>
            .reg (regionAliasN σ nm t res (regionCoCodeN σ nm t code res) (operandName op)))
          && regionMergeB (regionCoParts σ nm body t code res cert)
          && regionNopB (regionCoParts σ nm body t code res cert)
          && regionSitesB (fuseRegs σ nm) (regionCoParts σ nm body t code res cert)
          && (ownedCheckMC (regionCoParts σ nm body t code res cert).outs
              (regionCoParts σ nm body t code res cert).ref
              (virtImg (slotRen (slotArrOf σ nm)
                (renOf (regionCoParts σ nm body t code res cert).ps)) body)
            && idxInvCheckB (boundFacts σ nm)
              (idxAnnot (boundFacts σ nm) (regionCoParts σ nm body t code res cert).ref)
              (regionCoParts σ nm body t code res cert).ref
            && physImgB (slotRen (slotArrOf σ nm)
              (renOf (regionCoParts σ nm body t code res cert).ps)) body
            && regionImgB (slotRen (slotArrOf σ nm)
              (renOf (regionCoParts σ nm body t code res cert).ps)) []
              (regionCoParts σ nm body t code res cert).outs body
            && frameOkB σ body && entryB σ nm body))) := by
  obtain ⟨hc, ho, -⟩ := regionCoParts_of_cellFreeB σ nm t code res cert none h
  have hf : regionFoldB (regionCoParts σ nm body t code res cert) = true := by
    unfold regionFoldB
    rw [hc]
    rfl
  rw [regionCoB_none, hf, hc, ho, List.append_nil, renImageB_of_cellFreeB σ nm _ _ _ none h,
    calleeImgBT_none, Bool.and_true]
  rfl

/-- The first conjunct of `regionCoB σ nm body t code res cert` that is `false`, in the order of
    its definition with `renImageB` at the reference `d.ref` split into its conjuncts, or
    `none` when all hold. The stage of `regionMergeB` is `regMerge`; the stages of
    `regionSitesB` are `fuseOKL` for the fusion check and `fuseResultName` for the two
    conditions on `R15`. A body outside the class `regionPrintedB`, which `regionImgB`
    refuses, has the stage `regionPrintedB`. The stage of the cell fold is `regionFoldB`,
    and the stages of the two conjuncts of `renImageB` on the cell arrays are `cellNamesRB`
    and `cellRegions`. At a table the stages of the two added
    conjuncts are `commonCalls` and `calleeBodyB` (at the function name `fn`), the stage
    `regionPrintedB` is skipped, and the stage `regionImgB` is that of `calleeImgBT`. -/
def regionCoStage (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab := none) (fn : String := "") : Option String :=
  let codeC := calleeCodeT callee code
  let cp := regionCopy σ nm t callee codeC res
  let C := regionCoCode σ nm t codeC res cp
  let ρ := canonMemrefName (regionAliasTab σ nm t callee res C)
  let obs := regionCoObs t (regionOut cp res)
  let LA := liveArrTab C obs (calleeAAT callee) (calleeAOT callee)
  if callee.all (fun T => decide T.names.Nodup
      && (LprogCallCut.commonCallsT? T.common code).isSome
      && LprogCallCut.commonFreshT T.common T.names (regionCoCode σ nm t code res))
        = false then
    some "commonCalls"
  else if C.all (fun i => clsB i && mulxFree i) = false then some "coClass"
  else if coCfgB ρ C (tabAt LA) obs (calleeAAT callee) (calleeAOT callee) = false then
    some "coCfgB"
  else if (tabAt LA 0).all (fun x => ρ x == x) = false then some "coEntryFix"
  else
  let C1 := regionCoBody σ nm t codeC res callee
  let d := regionCoParts σ nm body t codeC res cert callee
  let ps := d.ps
  let sl := slotArrC d.cells (slotRen (slotArrOf σ nm) (renOf ps))
  let cb := cellBody sl body
  let outs := d.outs ++ d.cellOuts
  let B := d.ref
  if callee.all (fun T =>
      calleeBodyBT σ nm T (slotRen (slotArrOf σ nm) (renOf ps)) d.outs body B fn
        && d.cells.isEmpty) = false then some "calleeBodyB"
  else if renB σ nm [] C1 ps = false then some "renB"
  else if obs.all (fun A => (loopNames C1).contains (ρ A)) = false then some "coResultName"
  else if (regionRet σ nm t res).toList.all (fun p =>
      (loopNames C1).contains p.2 && renOf ps p.2 == p.2) = false then some "coResultCopy"
  else if regionResultB σ nm body t ((regionOut cp res).map fun op =>
      .reg (ρ (operandName op))) = false then
    some "regionResultB"
  else if regionMergeB d = false then some "regMerge"
  else if regionNopB d = false then some "regionNopB"
  else if (!d.sites || fuseOKL (fuseRegs σ nm) (fuseLoPre d.pre (d.nop.drop d.pre.length))
      (d.pre ++ d.nop.drop d.pre.length)) = false then some "fuseOKL"
  else if regionSitesB (fuseRegs σ nm) d = false then some "fuseResultName"
  else if regionFoldB d = false then some "regionFoldB"
  else if ownedCheckMC outs B (calleeImgT callee sl cb) = false then some "ownedCheckMC"
  else if idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B = false then
    some "idxInvCheckB"
  else if (callee.isSome || regionPrintedB body) = false then some "regionPrintedB"
  else if physImgB sl cb = false then some "physImgB"
  else if calleeImgBT callee sl d.cells outs body = false then some "regionImgB"
  else if frameOkB σ body = false then some "frameOkB"
  else if entryB σ nm body = false then some "entryB"
  else if cellNamesRB d.cells σ body = false then some "cellNamesRB"
  else if d.cells.all (fun p =>
      X86Backend.DecodeGenMem.regLen (rsOf σ) (unren ps p.1) == p.2
        && renOf ps (unren ps p.1) == p.1) = false then some "cellRegions"
  else none

/-- **The virtual run behind a final machine state**: some halting run of the virtual body
    `B` from the entry state `emptiedEntry σ ps R body sa` ends in a state that holds, at the
    renamed name of each slot array `A` of `σ` that is no cell array, the words of `sa'` at the
    cells of the entry base of `A`. -/
def RegionVirtCells (σ : AbiLayout) (nm : String → String) (ps : List (String × String))
    (R : Slots) (body : Lcmd) (B : List LinstrRM) (fn : String) (sa sa' : AState) : Prop :=
  ∃ fuel t, lsemFuelMemF (singletonProgM fn B) fuel
      { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some t
    ∧ ∀ q A n, slotArrOf σ nm q = some (A, n) → isArrB R (renOf ps A) = false →
      ∃ arr, t.prog.base.getArr (renOf ps A) 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩

/-- **`coRef_bytes_of_regionExp` at an array result copy.** Under the hypotheses of
    `coRef_bytes_of_regionExp` at the array result copy `cp = some (src, D, m)` of
    `regionCopy`, the decoded bytes of `body` halt on the machine from `sa` in a state from
    which `σ` reads back the source value of the result, with the further facts of
    `renImage_bytes` on the stack register, the memory and the run of the address machine,
    and with the run of `B` behind the final state (`RegionVirtCells`): the virtual run is `regionVirt_run_copy_of_regionExp`, after which the last version
    `copyName D m` of the result buffer holds the result, and the rest is the array case of
    `coRef_bytes_of_regionExp` at that name. -/
theorem coRef_bytes_copy_of_regionExp {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r : Exported}
    (hr : RegionExp fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {ps : List (String × String)} {R : Slots} {outs : List String} {B : List LinstrRM}
    {cp : Option (String × String × Nat)} (hcp : regionCopy σ nm t none r.code r.res = cp)
    {src D : String} {m : Nat} (hcs : cp = some (src, D, m))
    (hcl : (regionCoCode σ nm t r.code r.res cp).all (fun i => clsB i && mulxFree i) = true)
    (hco : coCfgB (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp))
      (regionCoCode σ nm t r.code r.res cp)
      (liveArrCert (regionCoCode σ nm t r.code r.res cp) (regionCoObs t (regionOut cp r.res)))
      (regionCoObs t (regionOut cp r.res)) = true)
    (hfix : (liveArrCert (regionCoCode σ nm t r.code r.res cp)
      (regionCoObs t (regionOut cp r.res)) 0).all
      (fun x => regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) x == x) = true)
    (hren : renB σ nm [] (regionCoBodyC σ nm t r.code r.res cp) ps = true)
    (hobs : (regionCoObs t (regionOut cp r.res)).all (fun A =>
      (loopNames (regionCoBodyC σ nm t r.code r.res cp)).contains
        (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) = true)
    (hres : regionResultB σ nm body t ((regionOut cp r.res).map fun op =>
      .reg (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) (operandName op))) = true)
    (himg : renImageB σ nm ps R outs body B = true)
    (houtC : ∀ A ∈ regionCoObs t (regionOut cp r.res), ∀ p ∈ R,
      p.1 = renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A) →
      ∀ j, j < p.2 → memName p.1 (8 * j) ∈ outs)
    (hB : ∀ (sa : AState), σ.Regions sa → ∀ (k : Nat) (s : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ movesOf ps
          ++ (regionCoBodyC σ nm t r.code r.res cp).map (renRM (renOf ps)))) k
        { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
          = some s →
      ∃ (k' : Nat) (s' : LstateMF),
        lsemFuelMemF (singletonProgM fn B) k'
          { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some s'
        ∧ (∀ A ∈ regionCoObs t (regionOut cp r.res),
          isArrB R (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) = false →
          ∀ w n, s'.prog.base.getArr
              (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) w n
            = s.prog.base.getArr
              (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) w n)
        ∧ (∀ A ∈ regionCoObs t (regionOut cp r.res), ∀ p ∈ R,
          p.1 = renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A) →
          ∃ arr : Fin p.2 → BitVec 64, s.prog.base.getArr p.1 64 p.2 = some arr
            ∧ ∀ j (hj : j < p.2),
              s'.prog.base.reg.lvm (memName p.1 (8 * j)) = ⟨64, arr ⟨j, hj⟩⟩)
        ∧ ∀ y ∈ (regionRet σ nm t r.res).toList.map Prod.snd, isCellB R y = false →
          s'.prog.base.reg.lvm y = s.prog.base.reg.lvm y)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ RegionVirtCells σ nm ps R body B fn sa sa'
      ∧ ∃ frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  subst hcs
  obtain ⟨-, rfl, ⟨op, hop, hsrc⟩, hD, hm, hfr⟩ := regionCopy_some hcp
  have RF := renB_spec hren
  have E := entryB_spec (renImageB_entryB himg) sa
  have hI := himg
  simp only [renImageB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hI
  have hlen := hI.2
  have hS := E.argSrc hreg.stackIn
  obtain ⟨k, s, hrun, harr⟩ := regionVirt_run_copy_of_regionExp σ nm fn hp hr E (unren ps)
    (fun j hj => (RF.unr j hj).1) sa V hV hS fuel v hv
    (fun op' h => by rw [hop] at h; obtain rfl := (List.cons.inj h).1; exact hsrc) hD
    (regionCopy_mem_regionWebsEx hcp) hm hfr
  have hrun0 : lsemFuelMemF (singletonProgM fn (argBind σ nm
      ++ regionCoCode σ nm (.stackArr 64 m) r.code r.res (some (src, D, m)))) k
      { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
        = some s := by
    simpa [regionCoCode, regionRet, movesOf, List.append_assoc] using hrun
  set C := regionCoCode σ nm (.stackArr 64 m) r.code r.res (some (src, D, m)) with hC
  obtain ⟨k1, s1, hrun1, harrs, -⟩ := regionRef_run (C := C)
    E sa hS (fun i hi => (clsB_ctl_cond (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcl i hi)).1
      (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcl i hi)).2).1) hco
    (fun x hx => by simpa using List.all_eq_true.mp hfix x hx) RF k s hrun0
  obtain ⟨k', s', hrun', hA2, hC2, -⟩ := hB sa hreg k1 s1 hrun1
  obtain ⟨prog, sa', hd, hh, hcells, hcellR, -, hsp, hkeep, hA⟩ := renImage_bytes himg
    (fun j hj => (RF.unr j hj).2) sa hreg fn k' s' hrun'
  refine ⟨prog, sa', hd, hh, ?_, hsp, hkeep, ⟨k', s', hrun', hcells⟩, hA⟩
  have hmem : copyName D m ∈ regionCoObs (.stackArr 64 m) (regionOut (some (src, D, m)) r.res) :=
    List.mem_singleton_self _
  have hN := List.all_eq_true.mp hobs _ hmem
  rw [List.contains_eq_mem, decide_eq_true_eq] at hN
  simp only [regionResultB, regionOut, List.map] at hres
  split at hres
  · rename_i RA k'' op' hσ hop'
    obtain rfl := (List.cons.inj hop').1
    simp only [Bool.and_eq_true, beq_iff_eq] at hres
    obtain ⟨⟨⟨-, hk⟩, hA⟩, hslot⟩ := hres
    have hunA : unren ps (renOf ps (regionAliasN σ nm (.stackArr 64 m) r.res C (copyName D m)))
        = regionAliasN σ nm (.stackArr 64 m) r.res C (copyName D m) := by
      obtain ⟨j, a, hj, -, he, -⟩ := slotArrOf_some hslot
      have he' : regionAliasN σ nm (.stackArr 64 m) r.res C (copyName D m) = argName j := he
      rw [he']
      exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
    have h2 := harr
    have hw : ∀ j (hj : j < m), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa
        (regionAliasN σ nm (.stackArr 64 m) r.res C (copyName D m))) j)
          = (Ctxt.Var.lookup (d := jasminDialect) (Γ := [JasminTy.stackArr 64 m])
            (t := JasminTy.stackArr 64 m) .here v) ⟨j, hj⟩ := by
      cases hAR : isArrB R (renOf ps (regionAliasN σ nm (.stackArr 64 m) r.res C (copyName D m))) with
      | false =>
          obtain ⟨arr, harr', hw⟩ := hcells _ _ _ hslot hAR
          have hgo := (hA2 _ hmem hAR 64 m).trans (harrs _ hmem hN 64 m)
          rw [← hgo] at h2
          obtain rfl := Option.some.inj (harr'.symm.trans h2)
          exact hw
      | true =>
          obtain ⟨p, hpR, hpe⟩ := List.any_eq_true.mp hAR
          have hpe' : p.1 = renOf ps (regionAliasN σ nm (.stackArr 64 m) r.res C (copyName D m)) := by
            simpa using hpe
          have hpl : p.2 = m := by
            rw [← (hlen p hpR).1, hpe', hunA]
            exact E.len _ _ _ hslot
          obtain ⟨pA, pn⟩ := p
          obtain rfl : pA = _ := hpe'
          obtain rfl : pn = m := hpl
          obtain ⟨arr, harr', hcl⟩ := hC2 _ hmem _ hpR rfl
          obtain rfl := Option.some.inj
            (harr'.symm.trans ((harrs _ hmem hN 64 _).trans h2))
          intro j hj
          have h4 := (hcl j hj).symm.trans
            (hcellR _ hpR j hj (houtC _ hmem _ hpR rfl j hj))
          have h5 := eq_of_heq (Sigma.mk.inj h4).2
          simp only [hunA] at h5
          exact h5.symm
    have hbase : abiBase (abiReg σ) sa (regionAliasN σ nm (.stackArr 64 m) r.res C (copyName D m)) = sa.regs RA := by
      have hA' : abiReg σ (regionAliasN σ nm (.stackArr 64 m) r.res C (copyName D m)) = some RA := hA
      simp [abiBase, hA']
    have hw' : ∀ j (hj : j < m), read64 sa'.mem (cellAt (sa.regs RA) j)
        = (Ctxt.Var.lookup (d := jasminDialect) (Γ := [JasminTy.stackArr 64 m])
          (t := JasminTy.stackArr 64 m) .here v) ⟨j, hj⟩ :=
      fun j hj => by rw [← hbase]; exact hw j hj
    exact resultOf_words (σ := σ) (sa' := sa') (by rw [hσ, hk]) hw'
  · cases hres

/-- **`coRef_bytes` at an array result copy**: `coRef_bytes_copy_of_regionExp` at the export
    `r` of `p`. -/
theorem coRef_bytes_copy {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {body : Lcmd}
    {ps : List (String × String)} {R : Slots} {outs : List String} {B : List LinstrRM}
    {cp : Option (String × String × Nat)} (hcp : regionCopy σ nm t none r.code r.res = cp)
    {src D : String} {m : Nat} (hcs : cp = some (src, D, m))
    (hcl : (regionCoCode σ nm t r.code r.res cp).all (fun i => clsB i && mulxFree i) = true)
    (hco : coCfgB (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp))
      (regionCoCode σ nm t r.code r.res cp)
      (liveArrCert (regionCoCode σ nm t r.code r.res cp) (regionCoObs t (regionOut cp r.res)))
      (regionCoObs t (regionOut cp r.res)) = true)
    (hfix : (liveArrCert (regionCoCode σ nm t r.code r.res cp)
      (regionCoObs t (regionOut cp r.res)) 0).all
      (fun x => regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) x == x) = true)
    (hren : renB σ nm [] (regionCoBodyC σ nm t r.code r.res cp) ps = true)
    (hobs : (regionCoObs t (regionOut cp r.res)).all (fun A =>
      (loopNames (regionCoBodyC σ nm t r.code r.res cp)).contains
        (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) = true)
    (hres : regionResultB σ nm body t ((regionOut cp r.res).map fun op =>
      .reg (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) (operandName op))) = true)
    (himg : renImageB σ nm ps R outs body B = true)
    (houtC : ∀ A ∈ regionCoObs t (regionOut cp r.res), ∀ p ∈ R,
      p.1 = renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A) →
      ∀ j, j < p.2 → memName p.1 (8 * j) ∈ outs)
    (hB : ∀ (sa : AState), σ.Regions sa → ∀ (k : Nat) (s : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ movesOf ps
          ++ (regionCoBodyC σ nm t r.code r.res cp).map (renRM (renOf ps)))) k
        { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
          = some s →
      ∃ (k' : Nat) (s' : LstateMF),
        lsemFuelMemF (singletonProgM fn B) k'
          { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some s'
        ∧ (∀ A ∈ regionCoObs t (regionOut cp r.res),
          isArrB R (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) = false →
          ∀ w n, s'.prog.base.getArr
              (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) w n
            = s.prog.base.getArr
              (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) w n)
        ∧ (∀ A ∈ regionCoObs t (regionOut cp r.res), ∀ p ∈ R,
          p.1 = renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A) →
          ∃ arr : Fin p.2 → BitVec 64, s.prog.base.getArr p.1 64 p.2 = some arr
            ∧ ∀ j (hj : j < p.2),
              s'.prog.base.reg.lvm (memName p.1 (8 * j)) = ⟨64, arr ⟨j, hj⟩⟩)
        ∧ ∀ y ∈ (regionRet σ nm t r.res).toList.map Prod.snd, isCellB R y = false →
          s'.prog.base.reg.lvm y = s.prog.base.reg.lvm y)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ RegionVirtCells σ nm ps R body B fn sa sa'
      ∧ ∃ frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false :=
  coRef_bytes_copy_of_regionExp hp (regionExp_of_exportR _ hr) hcp hcs hcl hco hfix hren hobs
    hres himg houtC hB sa V hV hreg fuel hv

/-- **A region export on the decoded bytes through a reference behind the coalesced and
    renamed one.** Let `p` be a program of `RegionExportable` with an exported code `r` of
    `RegionExp fn p (regionWebsEx σ nm) r` (its export or the webs of its export), and let
    its code and returned operands pass the conjuncts of `regionCoB` on the exported code at
    pairs `ps`. Let the virtual body `B` pass the image check `renImageB` under `ps`, at
    cell arrays `R` and observed names `outs`, against the printed body `body`, where `outs`
    holds the target of the result copy and the cell names of each returned array that is a
    cell array. Let every halting run of the coalesced and renamed reference at `ps` from
    the entry state `entryV` of a machine state satisfying `σ.Regions` be matched by a
    halting run of `B` from the state `emptiedEntry`, at the end of which the renamed alias of each returned array name holds
    the same array when it is no cell array, the cell names of a returned cell array hold
    the words of the array, and the target of the result copy holds the same value when it
    is no cell name. From every entry state `sa`
    satisfying `σ.Regions`, at every valuation `V` that `σ` reads off `sa` at which `p`
    denotes `v` at some fuel, the decoded bytes of `body` halt on the machine from `sa` in
    a state from which `σ` reads back the source value of the result, with the stack
    register, the memory outside the stack words and the pointer regions, and the run of
    the address machine of `renImage_bytes`, and the final machine state is the end of a run
    of `B` from `emptiedEntry` (`RegionVirtCells`). -/
theorem coRef_bytes_of_regionExp {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r : Exported}
    (hr : RegionExp fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {ps : List (String × String)} {R : Slots} {outs : List String} {B : List LinstrRM}
    {cp : Option (String × String × Nat)} (hcp : regionCopy σ nm t none r.code r.res = cp)
    (hcl : (regionCoCode σ nm t r.code r.res cp).all (fun i => clsB i && mulxFree i) = true)
    (hco : coCfgB (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp))
      (regionCoCode σ nm t r.code r.res cp)
      (liveArrCert (regionCoCode σ nm t r.code r.res cp) (regionCoObs t (regionOut cp r.res)))
      (regionCoObs t (regionOut cp r.res)) = true)
    (hfix : (liveArrCert (regionCoCode σ nm t r.code r.res cp)
      (regionCoObs t (regionOut cp r.res)) 0).all
      (fun x => regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) x == x) = true)
    (hren : renB σ nm [] (regionCoBodyC σ nm t r.code r.res cp) ps = true)
    (hobs : (regionCoObs t (regionOut cp r.res)).all (fun A =>
      (loopNames (regionCoBodyC σ nm t r.code r.res cp)).contains
        (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) = true)
    (hret : (regionRet σ nm t r.res).toList.all (fun q =>
      (loopNames (regionCoBodyC σ nm t r.code r.res cp)).contains q.2
        && renOf ps q.2 == q.2) = true)
    (hres : regionResultB σ nm body t ((regionOut cp r.res).map fun op =>
      .reg (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) (operandName op))) = true)
    (himg : renImageB σ nm ps R outs body B = true)
    (houtR : ∀ y ∈ (regionRet σ nm t r.res).toList.map Prod.snd, y ∈ outs)
    (houtC : ∀ A ∈ regionCoObs t (regionOut cp r.res), ∀ p ∈ R,
      p.1 = renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A) →
      ∀ j, j < p.2 → memName p.1 (8 * j) ∈ outs)
    (hB : ∀ (sa : AState), σ.Regions sa → ∀ (k : Nat) (s : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ movesOf ps
          ++ (regionCoBodyC σ nm t r.code r.res cp).map (renRM (renOf ps)))) k
        { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
          = some s →
      ∃ (k' : Nat) (s' : LstateMF),
        lsemFuelMemF (singletonProgM fn B) k'
          { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some s'
        ∧ (∀ A ∈ regionCoObs t (regionOut cp r.res),
          isArrB R (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) = false →
          ∀ w n, s'.prog.base.getArr
              (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) w n
            = s.prog.base.getArr
              (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) w n)
        ∧ (∀ A ∈ regionCoObs t (regionOut cp r.res), ∀ p ∈ R,
          p.1 = renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A) →
          ∃ arr : Fin p.2 → BitVec 64, s.prog.base.getArr p.1 64 p.2 = some arr
            ∧ ∀ j (hj : j < p.2),
              s'.prog.base.reg.lvm (memName p.1 (8 * j)) = ⟨64, arr ⟨j, hj⟩⟩)
        ∧ ∀ y ∈ (regionRet σ nm t r.res).toList.map Prod.snd, isCellB R y = false →
          s'.prog.base.reg.lvm y = s.prog.base.reg.lvm y)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ RegionVirtCells σ nm ps R body B fn sa sa'
      ∧ ∃ frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  have RF := renB_spec hren
  have E := entryB_spec (renImageB_entryB himg) sa
  have hI := himg
  simp only [renImageB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hI
  have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hI.1.2
  have hlen := hI.2
  rcases cp with _ | ⟨src, D, m⟩
  swap
  · exact coRef_bytes_copy_of_regionExp hp hr hcp rfl hcl hco hfix hren hobs hres himg houtC hB
      sa V hV hreg fuel hv
  simp only [regionOut] at hco hfix hobs hres houtC hB
  have hS := E.argSrc hreg.stackIn
  obtain ⟨k, s, s0, su, hrun, hag, hlvm, harr1, hnone, hmv, -⟩ :=
    regionVirt_run_of_regionExp σ nm fn hp hr (regionRet σ nm t r.res) E (unren ps)
      (fun j hj => (RF.unr j hj).1) sa V hV hS fuel v hv
  rw [List.append_assoc] at hrun
  obtain ⟨k1, s1, hrun1, harrs, hregs'⟩ := regionRef_run (C := regionCoCode σ nm t r.code r.res)
    E sa hS (fun i hi => (clsB_ctl_cond (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcl i hi)).1
      (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcl i hi)).2).1) hco
    (fun x hx => by simpa using List.all_eq_true.mp hfix x hx) RF k s hrun
  obtain ⟨k', s', hrun', hA2, hC2, hR2⟩ := hB sa hreg k1 s1 hrun1
  obtain ⟨prog, sa', hd, hh, hcells, hcellR, hregs, hsp, hkeep, hA⟩ := renImage_bytes himg
    (fun j hj => (RF.unr j hj).2) sa hreg fn k' s' hrun'
  refine ⟨prog, sa', hd, hh, ?_, hsp, hkeep, ⟨k', s', hrun', hcells⟩, hA⟩
  cases t with
  | stackArr w m =>
      obtain rfl : s = s0 := hnone rfl
      obtain ⟨op, hop, harr⟩ := hag.decodeArrM_single
      have hmem : operandName op ∈ regionCoObs (.stackArr w m) r.res := by
        simp [regionCoObs, hop]
      have hN := List.all_eq_true.mp hobs _ hmem
      rw [List.contains_eq_mem, decide_eq_true_eq] at hN
      set ρ := regionAliasN σ nm (.stackArr w m) r.res
        (regionCoCode σ nm (.stackArr w m) r.code r.res) with hρ
      rw [hop] at hres
      simp only [regionResultB, List.map] at hres
      split at hres
      · rename_i RA k' op' hσ hop'
        obtain rfl := (List.cons.inj hop').1
        simp only [Bool.and_eq_true, beq_iff_eq] at hres
        obtain ⟨⟨⟨rfl, hk⟩, hA⟩, hslot⟩ := hres
        have hunA : unren ps (renOf ps
            (regionAliasN σ nm (.stackArr 64 m) r.res (regionCoCode σ nm (.stackArr 64 m) r.code r.res) (operandName op)))
              = regionAliasN σ nm (.stackArr 64 m) r.res (regionCoCode σ nm (.stackArr 64 m) r.code r.res)
                (operandName op) := by
          obtain ⟨j, a, hj, -, he, -⟩ := slotArrOf_some hslot
          have he' : regionAliasN σ nm (.stackArr 64 m) r.res (regionCoCode σ nm (.stackArr 64 m) r.code r.res)
              (operandName op) = argName j := he
          rw [he']
          exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
        have h2 : s.prog.base.getArr (operandName op) 64 m
            = some (Ctxt.Var.lookup (d := jasminDialect) (Γ := [JasminTy.stackArr 64 m])
              (t := JasminTy.stackArr 64 m) .here v) := by
          have h1 : su.prog.base.getArr (operandName op) 64 m
              = some (Ctxt.Var.lookup (d := jasminDialect) (Γ := [JasminTy.stackArr 64 m])
                (t := JasminTy.stackArr 64 m) .here v) := harr
          unfold LstateM.getArr at h1 ⊢
          rw [harr1 _ (by simp [regionWebsObs, hop])]
          exact h1
        have hw : ∀ j (hj : j < m), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa
            (regionAliasN σ nm (.stackArr 64 m) r.res (regionCoCode σ nm (.stackArr 64 m) r.code r.res) (operandName op))) j)
              = (Ctxt.Var.lookup (d := jasminDialect) (Γ := [JasminTy.stackArr 64 m])
                (t := JasminTy.stackArr 64 m) .here v) ⟨j, hj⟩ := by
          cases hAR : isArrB R (renOf ps
              (regionAliasN σ nm (.stackArr 64 m) r.res (regionCoCode σ nm (.stackArr 64 m) r.code r.res) (operandName op))) with
          | false =>
              obtain ⟨arr, harr', hw⟩ := hcells _ _ _ hslot hAR
              have hgo := (hA2 _ hmem hAR 64 m).trans (harrs _ hmem hN 64 m)
              rw [← hgo] at h2
              obtain rfl := Option.some.inj (harr'.symm.trans h2)
              exact hw
          | true =>
              obtain ⟨p, hpR, hpe⟩ := List.any_eq_true.mp hAR
              have hpe' : p.1 = renOf ps (regionAliasN σ nm (.stackArr 64 m) r.res
                  (regionCoCode σ nm (.stackArr 64 m) r.code r.res) (operandName op)) := by
                simpa using hpe
              have hpl : p.2 = m := by
                rw [← (hlen p hpR).1, hpe', hunA]
                exact E.len _ _ _ hslot
              obtain ⟨pA, pn⟩ := p
              obtain rfl : pA = _ := hpe'
              obtain rfl : pn = m := hpl
              obtain ⟨arr, harr', hcl⟩ := hC2 _ hmem _ hpR rfl
              obtain rfl := Option.some.inj
                (harr'.symm.trans ((harrs _ hmem hN 64 _).trans h2))
              intro j hj
              have h4 := (hcl j hj).symm.trans
                (hcellR _ hpR j hj (houtC _ hmem _ hpR rfl j hj))
              have h5 := eq_of_heq (Sigma.mk.inj h4).2
              simp only [hunA] at h5
              exact h5.symm
        have hbase : abiBase (abiReg σ) sa
            (regionAliasN σ nm (.stackArr 64 m) r.res (regionCoCode σ nm (.stackArr 64 m) r.code r.res) (operandName op))
              = sa.regs RA := by
          have hA' : abiReg σ
              (regionAliasN σ nm (.stackArr 64 m) r.res (regionCoCode σ nm (.stackArr 64 m) r.code r.res) (operandName op))
                = some RA := hA
          simp [abiBase, hA']
        have hw' : ∀ j (hj : j < m), read64 sa'.mem (cellAt (sa.regs RA) j)
            = (Ctxt.Var.lookup (d := jasminDialect) (Γ := [JasminTy.stackArr 64 m])
              (t := JasminTy.stackArr 64 m) .here v) ⟨j, hj⟩ :=
          fun j hj => by rw [← hbase]; exact hw j hj
        exact resultOf_words (σ := σ) (sa' := sa') (by rw [hσ, hk]) hw'
      · cases hres
  | reg w =>
      obtain ⟨op, hop, hval⟩ := hag.getW_single
      rw [hop] at hres
      simp only [regionResultB, List.map] at hres
      split at hres
      · rename_i RA op' hσ hop'
        simp only [Bool.and_eq_true, beq_iff_eq] at hres
        obtain ⟨⟨⟨rfl, hgp⟩, hph⟩, hfr⟩ := hres
        have hret' : regionRet σ nm (JasminTy.reg 64) r.res
            = some (operandName op, nm RA) := by
          simp only [regionRet, hσ, hop]
        rw [hret'] at hret houtR hR2
        simp only [Option.toList_some, List.all_cons, List.all_nil, Bool.and_true,
          Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hret
        have hnc : isCellB R (nm RA) = false := by
          rw [X86Backend.ImageStraightCells.isCellB_eq]
          cases hc : cellIdx R (nm RA) with
          | none => rfl
          | some _ =>
              have := N.gp (nm RA) (by rw [hc]; rfl)
              rw [hgp] at this
              cases this
        have hR := hregs (nm RA) (houtR (nm RA) (by simp)) hgp hfr
        have hlv := hregs' (nm RA) hret.1
        rw [hret.2] at hlv
        have hlv2 := hR2 (nm RA) (by simp) hnc
        unfold LstateN.getW at hR hval
        rw [← hlvm] at hval
        rw [hlv2, hlv, hmv (operandName op) (nm RA) hret', hval, hph] at hR
        unfold AbiLayout.ResultOf
        rw [hσ]
        simp only [Haxc.ResultKind.read, ← Option.some.inj hR]
        rfl
      · cases hres
  | _ => simp [regionResultB] at hres

/-- **A region export on the decoded bytes through a reference behind the coalesced and
    renamed one**: `coRef_bytes_of_regionExp` at the export `r` of `p`. -/
theorem coRef_bytes {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {body : Lcmd}
    {ps : List (String × String)} {R : Slots} {outs : List String} {B : List LinstrRM}
    {cp : Option (String × String × Nat)} (hcp : regionCopy σ nm t none r.code r.res = cp)
    (hcl : (regionCoCode σ nm t r.code r.res cp).all (fun i => clsB i && mulxFree i) = true)
    (hco : coCfgB (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp))
      (regionCoCode σ nm t r.code r.res cp)
      (liveArrCert (regionCoCode σ nm t r.code r.res cp) (regionCoObs t (regionOut cp r.res)))
      (regionCoObs t (regionOut cp r.res)) = true)
    (hfix : (liveArrCert (regionCoCode σ nm t r.code r.res cp)
      (regionCoObs t (regionOut cp r.res)) 0).all
      (fun x => regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) x == x) = true)
    (hren : renB σ nm [] (regionCoBodyC σ nm t r.code r.res cp) ps = true)
    (hobs : (regionCoObs t (regionOut cp r.res)).all (fun A =>
      (loopNames (regionCoBodyC σ nm t r.code r.res cp)).contains
        (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) = true)
    (hret : (regionRet σ nm t r.res).toList.all (fun q =>
      (loopNames (regionCoBodyC σ nm t r.code r.res cp)).contains q.2
        && renOf ps q.2 == q.2) = true)
    (hres : regionResultB σ nm body t ((regionOut cp r.res).map fun op =>
      .reg (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) (operandName op))) = true)
    (himg : renImageB σ nm ps R outs body B = true)
    (houtR : ∀ y ∈ (regionRet σ nm t r.res).toList.map Prod.snd, y ∈ outs)
    (houtC : ∀ A ∈ regionCoObs t (regionOut cp r.res), ∀ p ∈ R,
      p.1 = renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A) →
      ∀ j, j < p.2 → memName p.1 (8 * j) ∈ outs)
    (hB : ∀ (sa : AState), σ.Regions sa → ∀ (k : Nat) (s : LstateMF),
      lsemFuelMemF (singletonProgM fn (argBind σ nm ++ movesOf ps
          ++ (regionCoBodyC σ nm t r.code r.res cp).map (renRM (renOf ps)))) k
        { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
          = some s →
      ∃ (k' : Nat) (s' : LstateMF),
        lsemFuelMemF (singletonProgM fn B) k'
          { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some s'
        ∧ (∀ A ∈ regionCoObs t (regionOut cp r.res),
          isArrB R (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) = false →
          ∀ w n, s'.prog.base.getArr
              (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) w n
            = s.prog.base.getArr
              (renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A)) w n)
        ∧ (∀ A ∈ regionCoObs t (regionOut cp r.res), ∀ p ∈ R,
          p.1 = renOf ps (regionAliasN σ nm t r.res (regionCoCode σ nm t r.code r.res cp) A) →
          ∃ arr : Fin p.2 → BitVec 64, s.prog.base.getArr p.1 64 p.2 = some arr
            ∧ ∀ j (hj : j < p.2),
              s'.prog.base.reg.lvm (memName p.1 (8 * j)) = ⟨64, arr ⟨j, hj⟩⟩)
        ∧ ∀ y ∈ (regionRet σ nm t r.res).toList.map Prod.snd, isCellB R y = false →
          s'.prog.base.reg.lvm y = s.prog.base.reg.lvm y)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ RegionVirtCells σ nm ps R body B fn sa sa'
      ∧ ∃ frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false :=
  coRef_bytes_of_regionExp hp (regionExp_of_exportR _ hr) hcp hcl hco hfix hren hobs hret hres
    himg houtR houtC hB sa V hV hreg fuel hv

/-- **A region export on the decoded bytes through the reference of the gate.**
    For a program `p` of `RegionExportable` with an exported code `r` of
    `RegionExp fn p (regionWebsEx σ nm) r` whose code and returned
    operands pass `regionCoB` against the printed body `body`: from every entry state `sa`
    satisfying `σ.Regions`, at every valuation `V` that `σ` reads off `sa` at which `p`
    denotes `v` at some fuel, the decoded bytes of `body` halt on the machine from `sa` in
    a state from which `σ` reads back the source value of the result, whose stack register
    holds its value in `sa`, and whose memory agrees with that of `sa` at every byte outside
    the stack words and the pointer regions of `σ`; some run of the address machine on
    `body` from `entryA σ sa` halts and stores to and loads from `layoutMem σ sa` only
    (`coRef_bytes_of_regionExp`). A run of the coalesced and renamed reference is carried to
    the merged code by `regCo_run`, to the code `nop` of the parts by `selfNop_run`, and,
    when that code has a site of the multiplication fusion, to the fused reference by
    `JasminLsemFuseMulHi.fuseMulHi_lsemFuelMemF_pre`, whose final states agree on every
    register and array other than `R15`. The final machine state is the end of a run of the
    reference `ref` of the parts of the gate (`RegionVirtCells`). -/
theorem regionCo_bytes_of_regionExp_virt {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r : Exported}
    (hr : RegionExp fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ RegionVirtCells σ nm (regionCoParts σ nm body t r.code r.res cert).ps
          (regionCoParts σ nm body t r.code r.res cert).cells body
          (regionCoParts σ nm body t r.code r.res cert).ref fn sa sa'
      ∧ ∃ frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  rw [regionCoB_none] at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨⟨hcl, hco⟩, hfix⟩,
    ⟨⟨⟨⟨⟨⟨⟨hren, hobs⟩, hret⟩, hres⟩, hmg⟩, hnop⟩, hsite⟩, hfold⟩, himg⟩ := hg
  have hcellsSub := regionCoParts_cells_sub σ nm body t r.code r.res cert none
  generalize hd : regionCoParts σ nm body t r.code r.res cert = d
    at hren hret hmg hnop hsite hfold himg hcellsSub ⊢
  have hnopE : d.nop = selfNop d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) := by
    rw [← hd]; rfl
  have hfusedE : d.fused
      = if d.sites then d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length) else d.nop := by
    rw [← hd]; rfl
  have hrefE : d.ref = if d.cells.isEmpty then d.fused
      else d.pre ++ (cellFoldLR d.cells [] (d.fused.drop d.pre.length)).getD
        (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hcellOuts : d.cellOuts = d.cells.flatMap fun p =>
      if d.obs.contains p.1 then X86Backend.ImageAddrRouteW.outCells p.1 p.2 else [] := by
    rw [← hd]; rfl
  have hobsE : d.obs = (regionCoObs t (regionOutN σ nm t r.code r.res)).map fun A =>
      renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A) := by
    rw [← hd]; rfl
  have hpre : d.pre = argBind σ nm ++ movesOf d.ps := by rw [← hd]; rfl
  have hren' : d.ren = (regionCoBody σ nm t r.code r.res).map (renRM (renOf d.ps)) := by
    rw [← hd]; rfl
  have hmerged : d.merged = d.ren.map (renRM (renOf d.tau)) := by rw [← hd]; rfl
  have houts : d.outs = (regionRet σ nm t r.res).toList.map Prod.snd := by rw [← hd]; rfl
  have harrs : ∀ A ∈ regionCoObs t (regionOutN σ nm t r.code r.res),
      renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A) ∈ d.arrs
        ∧ renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A) ∈ d.arrsM := by
    intro A hA
    rw [← hd]
    exact ⟨List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩),
      List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩)⟩
  have hlop : ∀ i ∈ d.pre, IsLopn i := fun i hi => by
    rw [hpre] at hi
    exact (List.mem_append.mp hi).elim (movesOf_isLopn _ i) (movesOf_isLopn _ i)
  have hsplit : d.nop = d.pre ++ d.nop.drop d.pre.length := by
    conv_lhs => rw [← List.take_append_drop d.pre.length d.nop]
    rw [hnopE, selfNop_take, List.take_left']
    rfl
  refine coRef_bytes_of_regionExp hp hr rfl hcl hco hfix hren hobs hret hres himg
    (fun y hy => List.mem_append_left _ (by rw [houts]; exact hy))
    (fun A hA p hp hpe j hj => List.mem_append_right _ (by
      rw [hcellOuts]
      refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
      have hin : d.obs.contains p.1 = true := by
        rw [List.contains_eq_mem, decide_eq_true_eq, hpe, hobsE]
        exact List.mem_map.mpr ⟨A, hA, rfl⟩
      rw [ite_eq_left hin]
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    (fun sa1 hreg1 k s h => ?_) sa V hV hreg fuel hv
  rw [← hpre] at h
  replace h : lsemFuelMemF (singletonProgM fn (d.pre ++ d.ren)) k
      { prog := { base := entryV σ (frameE body sa1) sa1 (unren d.ps), lfn := fn },
        zf := false } = some s := by
    rw [hren']
    exact h
  have hrun : ∃ s' : LstateMF,
      lsemFuelMemF (singletonProgM fn (d.pre ++ d.merged)) k
        { prog := { base := (entryV σ (frameE body sa1) sa1 (unren d.ps)), lfn := fn },
          zf := false } = some s'
      ∧ (∀ a ∈ d.arrs, s'.prog.base.larr a = s.prog.base.larr a)
      ∧ ∀ y ∈ d.outs, s'.prog.base.reg.lvm y = s.prog.base.reg.lvm y := by
    simp only [regionMergeB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hmg
    rcases hmg with hnil | ⟨hck, hout⟩
    · refine ⟨s, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
      rw [hmerged, hnil, map_renRM_renOf_nil]
      exact h
    · obtain ⟨s', hs', hrg, har⟩ := regCo_run (fn := fn) hlop hck _ rfl false k s h
      rw [← hmerged] at hs'
      refine ⟨s', hs', har, fun y hy => ?_⟩
      have hy' := List.all_eq_true.mp hout y hy
      simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, beq_iff_eq] at hy'
      have := hrg y hy'.1
      rwa [hy'.2] at this
  obtain ⟨s', hs', har, hrg⟩ := hrun
  simp only [regionNopB, Bool.and_eq_true] at hnop
  obtain ⟨hck, hout⟩ := hnop
  obtain ⟨s'', hs'', hrg2, har2⟩ := selfNop_run (fn := fn) hlop hck _ rfl false k s' hs'
  rw [← hnopE] at hs''
  have hA2 : ∀ A ∈ regionCoObs t (regionOutN σ nm t r.code r.res), ∀ w n,
      s''.prog.base.getArr (renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A)) w n
        = s.prog.base.getArr
          (renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A)) w n := by
    intro A hA w n
    unfold LstateM.getArr
    rw [har2 _ (harrs A hA).2, har _ (harrs A hA).1]
  have hY2 : ∀ y ∈ d.outs, s''.prog.base.reg.lvm y = s.prog.base.reg.lvm y := by
    intro y hy
    have hy' := List.all_eq_true.mp hout y hy
    rw [List.contains_eq_mem, decide_eq_true_eq] at hy'
    rw [hrg2 y hy', hrg y hy]
  have RF := renB_spec hren
  have E := entryB_spec (renImageB_entryB himg) sa1
  have hS1 := E.argSrc hreg1.stackIn
  have hF : ∃ (kF : Nat) (u : LstateMF),
      lsemFuelMemF (singletonProgM fn d.fused) kF
        { prog := { base := entryV σ (frameE body sa1) sa1 (unren d.ps), lfn := fn },
          zf := false } = some u
      ∧ (∀ A ∈ regionCoObs t (regionOutN σ nm t r.code r.res), ∀ w n,
        u.prog.base.getArr (renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A)) w n
          = s.prog.base.getArr
            (renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A)) w n)
      ∧ ∀ y ∈ d.outs, u.prog.base.reg.lvm y = s.prog.base.reg.lvm y := by
    rw [hfusedE]
    cases hS : d.sites with
    | false => exact ⟨k, s'', hs'', hA2, hY2⟩
    | true =>
        simp only [regionSitesB, hS, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hsite
        obtain ⟨⟨hfuse, hk1⟩, hk2⟩ := hsite
        rw [hsplit] at hs''
        have habi := entryV_abiEntry (sa := sa1) (un := unren d.ps) E.argF E.argG
          fun j hj => (RF.unr j hj).1
        obtain ⟨k', u, -, hrun', hag, -, -⟩ := fuseMulHi_lsemFuelMemF_pre hfuse fn _ s'' rfl
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact e64_of_abiEntryM habi x hx
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              exact congrArg (·.1) (entryV_srcOf (un := unren d.ps) hS1 ha)) k hs''
        refine ⟨k', u, hrun', fun A hA w n => ?_, fun y hy => ?_⟩
        · have hkept :
              KeptN (renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A)) := by
            have hm : renOf d.ps (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) A)
                ∈ d.obs := by
              rw [hobsE]
              exact List.mem_map.mpr ⟨A, hA, rfl⟩
            simpa [KeptN] using List.all_eq_true.mp hk1 _ hm
          rw [← hA2 A hA w n]
          unfold LstateM.getArr
          rw [hag.arr _ hkept]
        · rw [← hY2 y hy]
          exact hag.reg y (by simpa [KeptN] using List.all_eq_true.mp hk2 y hy)
  obtain ⟨kF, u, hu, hAF, hYF⟩ := hF
  by_cases hce : d.cells = []
  · rw [hrefE, hce]
    exact ⟨kF, u, hu, fun A hA _ w n => hAF A hA w n,
      fun A hA p hp => (List.not_mem_nil hp).elim, fun y hy _ => hYF y (houts ▸ hy)⟩
  · have hne : d.cells.isEmpty = false := by
      cases hc : d.cells with
      | nil => exact absurd hc hce
      | cons _ _ => rfl
    simp only [regionFoldB, hne, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at hfold
    obtain ⟨hfS, hpsC⟩ := hfold
    obtain ⟨L2, hL2⟩ := Option.isSome_iff_exists.mp hfS
    have hrefC : d.ref = d.pre ++ L2 := by
      rw [hrefE, hne, hL2]
      rfl
    have hsplitF : d.fused = d.pre ++ d.fused.drop d.pre.length := by
      rw [hfusedE]
      cases d.sites with
      | true =>
          show d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length)
            = d.pre ++ (d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length)).drop d.pre.length
          rw [List.drop_left']
          rfl
      | false => exact hsplit
    have hI := himg
    simp only [renImageB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hI
    have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hI.1.2
    have hXL := X86Backend.CellFoldLReg.ctlOK_of_cellFoldLR _ _ _ hL2
    rw [hsplitF] at hu
    obtain ⟨b1, z1, tX, hb1run, hXrun, rfl⟩ :=
      X86Backend.ImageAddrRouteW.strip_prefix fn _ _ hlop hXL.1 _ false rfl kF u hu
    obtain ⟨b1C, hb1C, hC1⟩ := X86Backend.ImageAddrRouteW.subCells_prefix (nm := nm)
      (seeds := []) hcellsSub E hS1 N (fun j hj => (RF.unr j hj).2) rfl hpsC
      (by rw [List.append_nil, ← hpre]; exact hb1run)
    rw [List.append_nil, ← hpre] at hb1C
    have hCF : X86Backend.CellFoldL.CellRelF d.cells []
        { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 }
        { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 } :=
      ⟨X86Backend.CellFoldL.cellRel_setLpc hC1 0, rfl, rfl⟩
    obtain ⟨t2, ht2, hCt⟩ := X86Backend.CellFoldLReg.lsemFuelMemF_cellFoldLR N.slots N.dist hL2
      fn kF (s := { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 })
      (s' := { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 }) hCF hXrun
    obtain ⟨t2', ht2', hSh⟩ := lsemFuelMemF_prepend fn d.pre L2 hlop hXL.2
      (emptiedEntry σ d.ps d.cells body sa1) b1C false z1 rfl hb1C kF t2 ht2
    have hlv2 : ∀ x, t2'.prog.base.reg.lvm x = t2.prog.base.reg.lvm x := fun x => by
      rw [hSh.base]
      rfl
    have hla2 : ∀ x, t2'.prog.base.larr x = t2.prog.base.larr x := fun x => by
      rw [hSh.base]
      rfl
    rw [hrefC]
    refine ⟨_, t2', ht2', fun A hA hnA w n => ?_, fun A hA p hp hpe => ?_,
      fun y hy hny => ?_⟩
    · rw [← hAF A hA w n]
      unfold LstateM.getArr
      rw [hla2, hCt.base.arr _ hnA]
      rfl
    · obtain ⟨arr, ha, hcl⟩ := hCt.base.cells p hp
      refine ⟨arr, ?_, fun j hj => by rw [hlv2]; exact hcl j hj⟩
      have h1 := hAF A hA 64 p.2
      rw [← hpe] at h1
      rw [← h1]
      exact ha
    · rw [hlv2, hCt.base.reg y hny, ← hYF y (houts ▸ hy)]
      rfl

/-- **A region export on the decoded bytes through the reference of the gate.**
    `regionCo_bytes_of_regionExp_virt` without the virtual run. -/
theorem regionCo_bytes_of_regionExp {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r : Exported}
    (hr : RegionExp fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -, hA⟩ :=
    regionCo_bytes_of_regionExp_virt hp hr hg sa V hV hreg fuel hv
  exact ⟨prog, sa', hd, hh, hR, hsp, hkeep, hA⟩

/-- **The image check behind `regionCoB`**: a code that passes `regionCoB` has its reference
    `ref` of the parts of the gate pass `renImageB` at the pairs and the cell arrays of the
    parts, at some observed names, and the pairs of the parts undo their renaming on every
    argument name of `σ`. -/
theorem regionCoB_renImage {σ : AbiLayout} {nm : String → String} {body : Lcmd} {t : JasminTy}
    {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    (hg : regionCoB σ nm body t code res cert = true) :
    (∃ outs, renImageB σ nm (regionCoParts σ nm body t code res cert).ps
      (regionCoParts σ nm body t code res cert).cells outs body
      (regionCoParts σ nm body t code res cert).ref = true)
    ∧ ∀ j, j < σ.args.length → unren (regionCoParts σ nm body t code res cert).ps
      (renOf (regionCoParts σ nm body t code res cert).ps (argName j)) = argName j := by
  rw [regionCoB_none] at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨hren, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩ := hg
  exact ⟨⟨_, himg⟩, fun j hj => ((renB_spec hren).unr j hj).2⟩

/-- **A region export on the decoded bytes through the reference of the gate**:
    `regionCo_bytes_of_regionExp` at the export `r` of `p`. -/
theorem regionCo_bytes {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false :=
  regionCo_bytes_of_regionExp hp (regionExp_of_exportR _ hr) hg sa V hV hreg fuel hv

/-! ## 7. The fusion post-pass of the allocation -/

/-- The dead-write elimination on a body that is straight-line up to a final return:
    `OwnedLprogTV.dropDeadWriteBody` on the instructions before the `Lret` when each of
    them passes `OwnedLprogTV.straightR`; every other body unchanged. -/
-- The definition `BackHalf.dropDeadWriteRet`; `BackHalf` imports this module, and the place
-- of one shared definition is `Haxc/BackHalfBase.lean`.
def deadWriteRet (body : Lcmd) : Lcmd :=
  match body.getLast? with
  | some r =>
      if r.li_i == .Lret && body.dropLast.all (fun i => X86Backend.OwnedLprogTV.straightR i.li_i)
      then X86Backend.OwnedLprogTV.dropDeadWriteBody body.dropLast ++ [r]
      else body
  | none => body

/-- **The fusion post-pass on an allocated program**: the high-product fusion
    `FuseMulHi.fuseMulHiLprog` in the mode that saves `RDX` in `R15`, followed by
    `deadWriteRet` on every function body. -/
def regionPostFuse (P : Lprog) : Lprog :=
  X86Backend.LprogOptPipeline.mapBodies deadWriteRet
    (X86Backend.FuseMulHi.fuseMulHiLprog P (saveRdx := true))

/-! ## 8. The allocation and the stages -/

/-- The liveness instruction at the position of the load `LOADIDX t, a[z]` of an array
    self-move: the pseudo-operation `LIVEPIN` writing the scratch register `t` and reading
    the array base `a` and the index register `z`. -/
def selfPinLoad (t a z : String) : LinstrRM :=
  (.Lopn [.reg t] "LIVEPIN" [.reg a, .reg z], .reg none)

/-- The liveness instruction at the position of the store `STOREIDX a, a[z], t` of an array
    self-move: the pseudo-operation `LIVEPIN` reading the array base `a`, the index register
    `z` and the scratch register `t`. -/
def selfPinStore (a z t : String) : LinstrRM :=
  (.Lopn [.reg "%livepin"] "LIVEPIN" [.reg a, .reg z, .reg t], .reg none)

/-- The liveness instructions of the pair of an array self-move whose load is `i`: for the
    load `LOADIDX t, a[z]`, `selfPinLoad t a z` followed by `selfPinStore a z t`. -/
def selfPinPair : LinstrRM → List LinstrRM
  | (.Lopn [.reg t] _ [.arrIdx a z _], _) => [selfPinLoad t a z, selfPinStore a z t]
  | i => [i]

/-- The code with each adjacent pair of `selfMoveB`, the load `LOADIDX t, a[z]` and the
    store `STOREIDX a, a[z], t`, replaced in place by the liveness instructions
    `selfPinLoad t a z` and `selfPinStore a z t`; every other instruction is kept. Positions
    and labels are those of the code. The allocation removes every `LIVEPIN` from its output;
    the scratch register `t` is written at the position of the load and read at the
    position of the store, as in the code, and the array base `a` and the index register `z`
    are read at both, as in the code. -/
def pinSelfMoves : List LinstrRM → List LinstrRM
  | [] => []
  | [i] => [i]
  | i :: j :: rest =>
      if selfMoveB i j then selfPinPair i ++ pinSelfMoves rest else i :: pinSelfMoves (j :: rest)

theorem pinSelfMoves_pair (t a z : String) (sc w n : Nat) (rest : List LinstrRM) :
    pinSelfMoves ((.Lopn [.reg t] "LOADIDX" [.arrIdx a z sc], .load w n)
        :: (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t], .store w n) :: rest)
      = selfPinLoad t a z :: selfPinStore a z t :: pinSelfMoves rest := by
  simp [pinSelfMoves, selfMoveB, selfPinPair]

theorem pinSelfMoves_cons {i j : LinstrRM} (h : selfMoveB i j = false) (rest : List LinstrRM) :
    pinSelfMoves (i :: j :: rest) = i :: pinSelfMoves (j :: rest) := by
  simp [pinSelfMoves, h]

/-- **The positions of the code with its self-moves pinned.** Each position of
    `pinSelfMoves l` holds the instruction of `l` there, or the liveness instruction of the
    load or of the store of a self-move there. -/
theorem getElem?_pinSelfMoves : ∀ (l : List LinstrRM) (k : Nat) (i' : LinstrRM),
    (pinSelfMoves l)[k]? = some i' → ∃ i, l[k]? = some i ∧ (i' = i ∨ ∃ t a z sc w n,
      (i = (.Lopn [.reg t] "LOADIDX" [.arrIdx a z sc], .load w n) ∧ i' = selfPinLoad t a z)
      ∨ (i = (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t], .store w n)
          ∧ i' = selfPinStore a z t))
  | [], k, i', h => by simp [pinSelfMoves] at h
  | [i], k, i', h => ⟨i', h, Or.inl rfl⟩
  | i :: j :: rest, k, i', h => by
      by_cases hs : selfMoveB i j = true
      · obtain ⟨t, a, z, sc, w, n, rfl, rfl⟩ := selfMoveB_shape hs
        rw [pinSelfMoves_pair] at h
        match k, h with
        | 0, h => exact ⟨_, rfl, Or.inr ⟨t, a, z, sc, w, n, Or.inl ⟨rfl, (Option.some.inj h).symm⟩⟩⟩
        | 1, h =>
            exact ⟨_, rfl, Or.inr ⟨t, a, z, sc, w, n, Or.inr ⟨rfl, (Option.some.inj h).symm⟩⟩⟩
        | k + 2, h => exact getElem?_pinSelfMoves rest k i' h
      · rw [pinSelfMoves_cons (Bool.eq_false_iff.mpr hs)] at h
        match k, h with
        | 0, h => exact ⟨i, rfl, Or.inl (Option.some.inj h).symm⟩
        | k + 1, h => exact getElem?_pinSelfMoves (j :: rest) k i' h

/-- `pinSelfMoves` keeps the length. -/
theorem length_pinSelfMoves : ∀ l : List LinstrRM, (pinSelfMoves l).length = l.length
  | [] => rfl
  | [_] => rfl
  | i :: j :: rest => by
      by_cases hs : selfMoveB i j = true
      · obtain ⟨t, a, z, sc, w, n, rfl, rfl⟩ := selfMoveB_shape hs
        rw [pinSelfMoves_pair]
        simp [length_pinSelfMoves rest]
      · rw [pinSelfMoves_cons (Bool.eq_false_iff.mpr hs)]
        simp [length_pinSelfMoves (j :: rest)]

/-- An instruction of `pinSelfMoves l` is an instruction of `l`, or the liveness instruction
    of the load or of the store of a self-move of `l`. -/
theorem mem_pinSelfMoves {l : List LinstrRM} {i : LinstrRM} (h : i ∈ pinSelfMoves l) :
    i ∈ l ∨ ∃ t a z sc w n,
      ((.Lopn [.reg t] "LOADIDX" [.arrIdx a z sc], .load w n) ∈ l ∧ i = selfPinLoad t a z)
      ∨ ((.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t], .store w n) ∈ l
          ∧ i = selfPinStore a z t) := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
  obtain ⟨j, hj, h⟩ := getElem?_pinSelfMoves l k i hk
  rcases h with rfl | ⟨t, a, z, sc, w, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact Or.inl (List.mem_of_getElem? hj)
  · exact Or.inr ⟨t, a, z, sc, w, n, Or.inl ⟨List.mem_of_getElem? hj, rfl⟩⟩
  · exact Or.inr ⟨t, a, z, sc, w, n, Or.inr ⟨List.mem_of_getElem? hj, rfl⟩⟩

/-- The names the liveness instruction of a jump at position `k` of `C` to a label at the
    position `p` reads, at the register liveness table `T` of `C`: the names the
    instructions from `p` to the jump read as registers before writing them
    (`regExposed`), followed by the other names of the table at `p`. -/
def backEdgePinNames (T : Array (List String)) (C : List LinstrRM) (p k : Nat) :
    List String :=
  let ns := regExposed (((C.drop p).take (k - p)).map Prod.fst)
  ns ++ (tabAt T p).filter fun x => !ns.contains x

/-- The liveness instruction before a jump at position `k` of `C` to the label `l`, at
    the register liveness table `T` of `C`: when `l` is at an earlier position `p`, the
    pseudo-operation `LIVEPIN` reading `backEdgePinNames T C p k` if that list is not
    empty; no instruction otherwise. -/
def backEdgePin (T : Array (List String)) (C : List LinstrRM) (k : Nat) (l : LLabel) :
    List LinstrRM :=
  match findLabelMem l C with
  | some p =>
      let ns := backEdgePinNames T C p k
      if p < k && !ns.isEmpty then
        [(.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg), .reg none)]
      else []
  | none => []

/-- The code with a liveness instruction `backEdgePin` before each jump to a label at an
    earlier position `p`, at the register liveness table `liveRegTab C []`: the instruction
    reads every name of the table at `p` and every name the instructions from `p` to the
    jump read as registers before writing them. The allocation removes every `LIVEPIN`
    from its output; its linear scan follows the order of the text, and the instruction
    keeps the register of each such name until the jump. -/
def backEdgePins (C : List LinstrRM) : List LinstrRM :=
  let T := liveRegTab C []
  C.zipIdx.flatMap fun (i, k) =>
    match i.1 with
    | .Lcond _ l => backEdgePin T C k l ++ [i]
    | .Lgoto (_, l) => backEdgePin T C k l ++ [i]
    | _ => [i]

/-- **The liveness instruction at a back edge holds the live-in names of its target**: for
    a jump at position `k` of `C` to a label at an earlier position `p`, the instruction
    `backEdgePin` before it at the table `liveRegTab C []` is one `LIVEPIN` whose names
    contain every name of that table at `p`. -/
theorem backEdgePins_live (C : List LinstrRM) {k p : Nat} {l : LLabel}
    (hl : findLabelMem l C = some p) (hpk : p < k) {x : String}
    (hx : x ∈ tabAt (liveRegTab C []) p) :
    ∃ ns : List String,
      backEdgePin (liveRegTab C []) C k l
        = [(.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg), .reg none)]
      ∧ x ∈ ns := by
  have hmem : x ∈ backEdgePinNames (liveRegTab C []) C p k := by
    unfold backEdgePinNames
    by_cases h : (regExposed (((C.drop p).take (k - p)).map Prod.fst)).contains x
    · exact List.mem_append_left _ (by simpa using h)
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hx, by simpa using h⟩)
  refine ⟨_, ?_, hmem⟩
  have hne : (backEdgePinNames (liveRegTab C []) C p k).isEmpty = false :=
    List.isEmpty_eq_false_iff_exists_mem.mpr ⟨x, hmem⟩
  simp only [backEdgePin, hl, hpk, decide_true, hne, Bool.not_false, Bool.and_self,
    ite_true]

/-- The code given to the allocation: the exported code with the alias map of the alias
    table `resAliasTab` at the out symbols `outs` and the result alias `rr` applied at its
    array positions (`renArr`), with liveness instructions in place of the array moves of an
    array onto itself (`pinSelfMoves`) and the liveness instructions `backEdgePins`. On code
    with no such move and no jump to an earlier label it is the renamed code. -/
def regionAllocCode (code : List LinstrRM) (outs : List (String × Nat) := [])
    (rr : Option (String × String) := none) : List LinstrRM :=
  backEdgePins (pinSelfMoves (code.map (renArr (canonMemrefName (resAliasTab outs rr code)))))

/-- **On code without a zeroing the code given to the allocation does not depend on the
    result alias.** -/
theorem regionAllocCode_eq_of_noZero {code : List LinstrRM} (outs : List (String × Nat))
    (rr : Option (String × String)) (h : ∀ i ∈ code, zeroDst? i = none) :
    regionAllocCode code outs rr = regionAllocCode code outs := by
  rw [regionAllocCode, regionAllocCode, resAliasTab_eq_of_noZero outs rr h]; rfl

/-- The split configuration that splits no interval. -/
def noSplit (_ : Lcmd) : Option SplitCfg := none

/-- **The physical-ABI allocation of the array-result path at an optional table, with its
    allocation certificate**, with `64`-bit arguments and each array base paired with the
    register of its own argument slot: `lfundefPhysAbiOfVirtCert` without a table, and
    the allocation `ImageAddrCall.lfundefPhysAbiOfVirtPoolCert` of a virtual function that
    calls the functions of the table with one, at the pool `CalleeTab.pool` and the out symbols
    `CalleeTab.outs`, whose calls copy no result register. Without a table the allocation
    splits the intervals of its body under the configuration `splitCfg` of the body (by default
    `bodySplitOpt`: the split of `bodySplitCfg` on a body without a call). -/
def calleeAllocCert (callee : Option CalleeTab) (fd : Lfundef) (outArg : String)
    (inArgs abiArgs : List String) (splitCfg : Lcmd → Option SplitCfg := bodySplitOpt) :
    Lfundef × List (String × String) :=
  match callee with
  | none =>
      lfundefPhysAbiOfVirtCert fd outArg inArgs [] (abiArgs := abiArgs)
        (abiTyin := abiArgs.map fun _ => 64) (posBind := true)
        (splitCfg := splitCfg)
  | some T =>
      X86Backend.ImageAddrCall.lfundefPhysAbiOfVirtPoolCert T.pool fd outArg inArgs [] abiArgs
        (abiArgs.map fun _ => 64) true (T.outs.map Prod.fst)

/-- **The physical-ABI allocation of the array-result path at an optional table**: the
    function of `calleeAllocCert`, `lfundefPhysAbiOfVirt` without a table and
    `ImageAddrCall.lfundefPhysAbiOfVirtPool` with one. -/
def calleeAlloc (callee : Option CalleeTab) (fd : Lfundef) (outArg : String)
    (inArgs abiArgs : List String) (splitCfg : Lcmd → Option SplitCfg := bodySplitOpt) :
    Lfundef :=
  (calleeAllocCert callee fd outArg inArgs abiArgs splitCfg).1

/-- The function of `calleeAllocCert` is `calleeAlloc`. -/
theorem calleeAllocCert_fst (callee : Option CalleeTab) (fd : Lfundef) (outArg : String)
    (inArgs abiArgs : List String) (splitCfg : Lcmd → Option SplitCfg) :
    (calleeAllocCert callee fd outArg inArgs abiArgs splitCfg).1
      = calleeAlloc callee fd outArg inArgs abiArgs splitCfg := rfl

/-- **The allocation at the table of one linked function** is
    `ImageAddrCall.lfundefPhysAbiOfVirtCCert` at its interface. -/
theorem calleeAllocCert_one (c : CalleeData) (fd : Lfundef) (outArg : String)
    (inArgs abiArgs : List String) :
    calleeAllocCert (some (CalleeTab.one c)) fd outArg inArgs abiArgs
      = X86Backend.ImageAddrCall.lfundefPhysAbiOfVirtCCert c.sig fd outArg inArgs [] abiArgs
          (abiArgs.map fun _ => 64) true ((CalleeTab.one c).outs.map Prod.fst) := by
  simp only [calleeAllocCert, CalleeTab.pool_one,
    X86Backend.ImageAddrCall.lfundefPhysAbiOfVirtCCert]

/-- Without a callee the allocation of the array-result path is `lfundefPhysAbiOfVirt`. -/
@[simp] theorem calleeAlloc_none (fd : Lfundef) (outArg : String)
    (inArgs abiArgs : List String) (splitCfg : Lcmd → Option SplitCfg) :
    calleeAlloc none fd outArg inArgs abiArgs splitCfg =
      lfundefPhysAbiOfVirt fd outArg inArgs [] (abiArgs := abiArgs)
        (abiTyin := abiArgs.map fun _ => 64) (posBind := true) (splitCfg := splitCfg) := rfl

/-- The names the liveness instruction at entry reads, for the names `a` and the code `C`
    given to the allocation: the array base names of `a` that the allocation pairs with an
    argument register (`argBasePairsPos`) when there are two or more, followed by the other
    argument names `argName j`, `j < a.abiArgs.length`, of the register liveness table
    `liveRegTab C []` at entry. -/
def entryPinNames (a : AbiNames) (C : List LinstrRM) : List String :=
  let ns := (argBasePairsPos (a.outArg :: a.inArgs) a.abiArgs).map Prod.fst
  let bs := if 2 ≤ ns.length then ns else []
  let live := tabAt (liveRegTab C []) 0
  bs ++ ((List.range a.abiArgs.length).map argName).filter
    fun x => live.contains x && !bs.contains x

/-- **The liveness instruction at entry**: the pseudo-operation `LIVEPIN` reading
    `entryPinNames a C` when that list is not empty, and no instruction otherwise. The
    allocation removes every `LIVEPIN` from its output. The array bases are live together
    from entry, so the allocation gives distinct array bases distinct registers, and its
    reload map of the array bases, keyed on the register, names one argument slot per
    register; an argument name live at entry keeps its register from entry, where
    `buildArgPtrMaterialize` writes it. -/
def arrBasePins (a : AbiNames) (C : List LinstrRM) : Lcmd :=
  let ns := entryPinNames a C
  if ns.isEmpty then [] else [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg)⟩]

/-- **The liveness instruction at entry holds the argument names live at entry**: every
    argument name `argName j`, `j < a.abiArgs.length`, of the register liveness table
    `liveRegTab C []` at entry is read by the one `LIVEPIN` of `arrBasePins a C`. -/
theorem entryPins_live (a : AbiNames) (C : List LinstrRM) {j : Nat}
    (hj : j < a.abiArgs.length) (hx : argName j ∈ tabAt (liveRegTab C []) 0) :
    arrBasePins a C
        = [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" ((entryPinNames a C).map LOperand.reg)⟩]
      ∧ argName j ∈ entryPinNames a C := by
  have hmem : argName j ∈ entryPinNames a C := by
    have key : ∀ bs : List String, argName j ∈ bs ++ ((List.range a.abiArgs.length).map
        argName).filter fun x => (tabAt (liveRegTab C []) 0).contains x && !bs.contains x := by
      intro bs
      by_cases h : bs.contains (argName j)
      · exact List.mem_append_left _ (by simpa using h)
      · refine List.mem_append_right _ (List.mem_filter.mpr
          ⟨List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩)
        simp only [h, Bool.not_false, Bool.and_true]
        simpa using hx
    exact key _
  refine ⟨?_, hmem⟩
  have hne : (entryPinNames a C).isEmpty = false :=
    List.isEmpty_eq_false_iff_exists_mem.mpr ⟨_, hmem⟩
  simp only [arrBasePins, hne, Bool.false_eq_true, ite_false]

/-- **The array result copy of the allocated program**: without a callee and at one result
    of type `t`, the copy `resCopyCode` of the decision `resCopyOf` into the output array
    `a.outArg`; no instruction otherwise. -/
def regionLprogCopy (a : AbiNames) (callee : Option CalleeTab) (ts : List JasminTy)
    (code : List LinstrRM) (res : List LOperand) : List LinstrRM :=
  match callee, ts with
  | none, [t] =>
      match resCopyOf a.outArg t code res with
      | some (src, D, m) => resCopyCode src D m
      | none => []
  | _, _ => []

/-- **The allocation stage of a region export**: the export `exportR`, its webs
    `regionWebsAt`, and the one-function program whose function is a physical-ABI allocation
    of the virtual
    function `exportRLfundef` under the table's names, with `64`-bit arguments; `none` on a
    program with a `call`. The body of the virtual function is `regionAllocCode` of the
    exported code, followed by a return. For one register result the allocation is
    `comToLfundefPhysAbiFromVirt` with the argument registers pinned live and the result
    moved into `RAX`; for every other result it is `lfundefPhysAbiOfVirt` with each array
    base paired with the register of its own argument slot, on the body preceded by
    `arrBasePins`. The gate `regionCoB` of
    `regionBack` checks the printed body against the reference `CoParts.ref`, in which
    `selfNop` has replaced the array moves and the high multiplications are fused as in
    the post-pass.

    At a table the allocation of the array-result path is `calleeAlloc`: the allocation
    pool is the pool `CalleeTab.pool` of the names the functions of the table keep, the shadow
    instruction of a call stays in the input of the allocation, and the call is expanded on
    the allocated body. The code given to the allocation is renamed at the out symbols
    `calleeOutsT` of the table, so that the destination of an out call is the array of its
    operand at the destination position.
    The register-result path expands the shadow instructions before it allocates
    (`comToLfundefPhysAbiFromVirt`), and `regionBack` refuses a calling body with a
    register result.

    Without a table, the exported code is followed by the array result copy
    `regionLprogCopy` into the output array `a.outArg`, the copy the gate takes at the result
    buffer of the layout (`regionCopy`). At a table the exported code is its webs
    (`regionWebsAt` at the names `ex` read after it).

    The program `regionAllocC` returns is the one-function program before the post-pass,
    with the allocation certificate. The array-result path without a table splits the
    intervals of its body under `splitCfg` (`calleeAllocCert`). -/
def regionAllocC (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (callee : Option CalleeTab := none)
    (ex : List String := []) (splitCfg : Lcmd → Option SplitCfg := bodySplitOpt) :
    Option (Lprog × List (String × String)) :=
  (exportR Γ.length a.fname p Γ.length 0).bind fun r0 =>
  let r := regionWebsAt ex callee r0
  (exportRLfundef a.fname p).map fun fd0 =>
    let ac := regionAllocCode (r.code ++ regionLprogCopy a callee ts r.code r.res)
      (calleeOutsT callee) (resAliasOf callee (some a.outArg) ts r.res)
    let fd : Lfundef := { fd0 with
      lfd_body := ac.map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩] }
    let fc : Lfundef × List (String × String) :=
      match ts with
      | [.reg _] =>
          comToLfundefPhysAbiFromVirtCert fd (abiArgs := a.abiArgs)
            (abiTyin := a.abiArgs.map fun _ => 64) (forceLivePin := true)
            (retToRax := true)
      | _ =>
          calleeAllocCert callee { fd with lfd_body := arrBasePins a ac ++ fd.lfd_body }
            a.outArg a.inArgs a.abiArgs splitCfg
    (({ lp_rip := VIR.LprogIsa.x86ExportData.ip
        lp_rsp := X86Backend.LprogAsmPrinter.x86Abi.sp
        lp_globs := []
        lp_glob_names := []
        lp_funcs := [(a.fname, fc.1)] } : Lprog), fc.2)

/-- **The allocated program of a region export with its allocation certificate**: the
    fusion post-pass `regionPostFuse` of the program of the allocation stage `regionAllocC`,
    with the certificate of that stage. -/
def regionLprogC (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (callee : Option CalleeTab := none)
    (ex : List String := []) (splitCfg : Lcmd → Option SplitCfg := bodySplitOpt) :
    Option (Lprog × List (String × String)) :=
  (regionAllocC a p callee ex splitCfg).map fun x => (regionPostFuse x.1, x.2)

/-- **The allocated program of a region export**: the program of `regionLprogC`, without
    its allocation certificate. -/
def regionLprog (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (callee : Option CalleeTab := none)
    (ex : List String := []) : Option Lprog :=
  (regionLprogC a p callee ex).map (·.1)

/-- The program of `regionLprogC` is `regionLprog`. -/
theorem regionLprogC_fst (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (callee : Option CalleeTab) (ex : List String) :
    (regionLprogC a p callee ex).map (·.1) = regionLprog a p callee ex := rfl

/-- **The code of a table**: the codes of its functions, in order. -/
def CalleeTab.bytes (T : CalleeTab) : List (BitVec 8) := T.fns.flatMap (·.bytes)

/-- The code of the table of one linked function is its code. -/
@[simp] theorem CalleeTab.bytes_one (c : CalleeData) : (CalleeTab.one c).bytes = c.bytes := by
  simp [CalleeTab.bytes, CalleeTab.one]

/-- **The position of a symbol in a table**: that of its first function, and `0` at a symbol
    outside the table, which the gate of a calling body excludes (`calleeBodyBT`). -/
def CalleeTab.symPos (T : CalleeTab) (g : String) : Nat :=
  (T.fns.findIdx? (·.name == g)).getD 0

/-- In the table of one linked function every symbol has position `0`. -/
@[simp] theorem CalleeTab.symPos_one (c : CalleeData) (g : String) :
    (CalleeTab.one c).symPos g = 0 := by
  by_cases h : c.name = g <;> simp [CalleeTab.symPos, CalleeTab.one, List.findIdx?_cons, h]

/-- **The byte offset of the entry of the function at position `i`** in the code
    `CalleeTab.bytes`: the length of the codes of the functions before it. -/
def CalleeTab.entryOff (T : CalleeTab) (i : Nat) : Nat :=
  ((T.fns.take i).flatMap (·.bytes)).length

/-- The first function has its entry at byte offset `0`. -/
@[simp] theorem CalleeTab.entryOff_zero (T : CalleeTab) : T.entryOff 0 = 0 := by
  simp [CalleeTab.entryOff]

/-- **The instruction index of the entry of the function at position `i`** in the decoded code
    `CalleeTab.bytes`: `0` at the first function, without decoding, and otherwise the index of
    the instruction of the decoded layout at the byte offset `CalleeTab.entryOff T i` (`0` when
    the code does not decode or has no instruction there). The index at each function is the
    entry index of `LprogBytesLinkReloc.RegionDecode`. -/
def CalleeTab.entryIdx (T : CalleeTab) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      ((X86Backend.LprogBytesDecode.decodeAt T.bytes.length 0 T.bytes).bind fun xs =>
        xs.findIdx? fun z => decide (z.1 = T.entryOff (i + 1))).getD 0

/-- The first function has its entry at instruction index `0`. -/
@[simp] theorem CalleeTab.entryIdx_zero (T : CalleeTab) : T.entryIdx 0 = 0 := rfl

/-- **The target map of the symbols of a table behind a caller** of `n` instructions and `L`
    bytes: a symbol goes to the instruction index and the byte offset of the entry of its
    function in the code `CalleeTab.bytes`. A symbol outside the table has position `0`. -/
def CalleeTab.linkMap (T : CalleeTab) (n L : Nat) (g : String) : Option (Nat × Nat) :=
  some (n + T.entryIdx (T.symPos g), L + T.entryOff (T.symPos g))

/-- At the table of one linked function every symbol goes to the first instruction and the
    first byte behind the caller. -/
@[simp] theorem CalleeTab.linkMap_one (c : CalleeData) (n L : Nat) (g : String) :
    (CalleeTab.one c).linkMap n L g = some (n, L) := by
  simp [CalleeTab.linkMap]

/-- **The region check of a table**: the entry of each function after the first, at the byte
    offset `CalleeTab.entryOff`, starts an instruction of the one decode of the code
    `CalleeTab.bytes`, so that `CalleeTab.entryIdx` is the index of that instruction. A table
    of one function has no such entry; its code is a region of one block
    (`LprogBytesLinkReloc.regionBlocks_one`). -/
def CalleeTab.regionB (T : CalleeTab) : Bool :=
  (List.range (T.fns.length - 1)).all fun i =>
    ((X86Backend.LprogBytesDecode.decodeAt T.bytes.length 0 T.bytes).bind fun xs =>
      xs.findIdx? fun z => decide (z.1 = T.entryOff (i + 1))).isSome

/-- The table of one linked function passes the region check. -/
@[simp] theorem CalleeTab.regionB_one (c : CalleeData) : (CalleeTab.one c).regionB = true := by
  simp [CalleeTab.regionB, CalleeTab.one]

/-- **Soundness of the region check**: in a table that passes `CalleeTab.regionB`, the entry of
    the function at each position `i > 0` is the instruction of index `CalleeTab.entryIdx T i`
    in the decoded layout of the code of the table. -/
theorem CalleeTab.regionB_spec {T : CalleeTab} (h : T.regionB = true) {i : Nat} (h0 : 0 < i)
    (hi : i < T.fns.length) :
    ∃ xs, X86Backend.LprogBytesDecode.decodeAt T.bytes.length 0 T.bytes = some xs
      ∧ xs.findIdx? (fun z => decide (z.1 = T.entryOff i)) = some (T.entryIdx i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj := List.all_eq_true.mp h j (List.mem_range.mpr (by omega))
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hj
  obtain ⟨xs, hxs, hf⟩ := Option.bind_eq_some_iff.mp hk
  have he : T.entryIdx (j + 1) = k := by simp only [CalleeTab.entryIdx, hk, Option.getD_some]
  exact ⟨xs, hxs, he ▸ hf⟩

/-- **The blocks of a table as the entries of a callee region**: the symbol, the code and the
    program `q c` of each function `c`, in order. -/
def CalleeTab.regionEntries (T : CalleeTab)
    (q : CalleeData → List X86Backend.LprogBytesDecode.RInstr) :
    List X86Backend.LprogBytesLinkReloc.CalleeBlock :=
  T.fns.map fun c => ⟨c.name, c.bytes, q c⟩

/-- The bytes of the entries of a table are the code of the table. -/
theorem CalleeTab.flatMap_regionEntries (T : CalleeTab)
    (q : CalleeData → List X86Backend.LprogBytesDecode.RInstr) :
    (T.regionEntries q).flatMap (·.bytes) = T.bytes := by
  simp [CalleeTab.regionEntries, CalleeTab.bytes, List.flatMap_map]

/-- The byte offset of the first function with the symbol `f` among `fns` is the offset of the
    block of `f` in the region of their entries. -/
theorem regionOffset_entries (q : CalleeData → List X86Backend.LprogBytesDecode.RInstr) :
    ∀ (fns : List CalleeData) (f : String), f ∈ fns.map (·.name) →
      ((fns.take ((fns.findIdx? (·.name == f)).getD 0)).flatMap (·.bytes)).length
        = X86Backend.LprogBytesLinkReloc.regionOffset
            (fns.map fun c => (⟨c.name, c.bytes, q c⟩ :
              X86Backend.LprogBytesLinkReloc.CalleeBlock)) f
  | [], _, h => by simp at h
  | [c], f, h => by
      have hc : c.name = f := by simpa [eq_comm] using h
      simp [List.findIdx?_cons, hc, X86Backend.LprogBytesLinkReloc.regionOffset]
  | c :: c' :: cs, f, h => by
      by_cases hc : c.name = f
      · simp [List.findIdx?_cons, hc, X86Backend.LprogBytesLinkReloc.regionOffset]
      · have h' : f ∈ (c' :: cs).map (·.name) := by
          simp only [List.map_cons, List.mem_cons] at h ⊢
          rcases h with h | h
          · exact absurd h.symm hc
          · exact h
        have ih := regionOffset_entries q (c' :: cs) f h'
        obtain ⟨i, hi⟩ : ∃ i, (c' :: cs).findIdx? (·.name == f) = some i := by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h'
          apply Option.isSome_iff_exists.mp
          rw [List.findIdx?_isSome]
          exact List.any_eq_true.mpr ⟨d, hd, by simp⟩
        rw [hi, Option.getD_some] at ih
        have hcf : (c.name == f) = false := by simpa using hc
        simp only [List.findIdx?_cons, hcf, Bool.false_eq_true, ↓reduceIte, hi, Option.map_some,
          Option.getD_some, List.take_succ_cons, List.flatMap_cons, List.length_append,
          List.map_cons, X86Backend.LprogBytesLinkReloc.regionOffset, hc]
        simp only [List.map_cons] at ih
        rw [← ih]

/-- The function of the symbol `f` (`CalleeTab.lookup`) has the block of `f` in the region of
    the entries of a list of functions. -/
theorem regionCode_entries (q : CalleeData → List X86Backend.LprogBytesDecode.RInstr) :
    ∀ (fns : List CalleeData) (f : String) (c : CalleeData),
      fns.find? (·.name == f) = some c →
      X86Backend.LprogBytesLinkReloc.regionCode
          (fns.map fun c => (⟨c.name, c.bytes, q c⟩ :
            X86Backend.LprogBytesLinkReloc.CalleeBlock)) f = q c
  | [], _, _, h => by simp at h
  | [d], f, c, h => by
      simp only [List.find?_cons, List.find?_nil] at h
      split at h
      · obtain rfl := Option.some.inj h
        simp [X86Backend.LprogBytesLinkReloc.regionCode]
      · cases h
  | d :: d' :: ds, f, c, h => by
      simp only [List.find?_cons] at h
      by_cases hd : d.name = f
      · simp only [hd, beq_self_eq_true, Option.some.injEq] at h
        subst h
        simp [X86Backend.LprogBytesLinkReloc.regionCode, hd]
      · have hdf : (d.name == f) = false := by simpa using hd
        rw [hdf] at h
        have ih := regionCode_entries q (d' :: ds) f c (by simpa [List.find?_cons] using h)
        simp only [List.map_cons, X86Backend.LprogBytesLinkReloc.regionCode, hd, ↓reduceIte]
        simpa using ih

/-- **The region of the code of a table.** Let each function of a nonempty table `T` have
    nonempty code that decodes to the program `q c` without `call`. For symbols `fs` of the
    table, the code `CalleeTab.bytes` is a region with the block of `f` at the byte offset
    `CalleeTab.entryOff` and the index `CalleeTab.entryIdx` of the first function of `f`
    (`LprogBytesLinkReloc.regionBlocks_of_decodes`); the block of `f` is the program of that
    function (`regionCode_entries`). -/
theorem CalleeTab.regionBlocks (T : CalleeTab) (hT : T.fns ≠ [])
    (q : CalleeData → List X86Backend.LprogBytesDecode.RInstr)
    (hdec : ∀ c ∈ T.fns, decodeLprog c.bytes = some (q c))
    (hne : ∀ c ∈ T.fns, c.bytes ≠ [])
    (hq : ∀ c ∈ T.fns, ∀ tg, X86Backend.LprogBytesDecode.RInstr.call tg ∉ q c)
    (fs : List String) (hfs : ∀ f ∈ fs, f ∈ T.names) :
    X86Backend.LprogBytesLinkReloc.RegionBlocks T.bytes fs (fun g => T.entryOff (T.symPos g))
      (fun g => T.entryIdx (T.symPos g))
      (X86Backend.LprogBytesLinkReloc.regionCode (T.regionEntries q))
      (X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries q)) := by
  have R := X86Backend.LprogBytesLinkReloc.regionBlocks_of_decodes fs (T.regionEntries q)
    (by simpa [CalleeTab.regionEntries] using hT)
    (fun e he => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
      exact hdec c hc)
    (fun e he => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
      exact hne c hc)
    (fun e he => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
      exact hq c hc)
  rw [CalleeTab.flatMap_regionEntries] at R
  have hO : ∀ f ∈ fs, T.entryOff (T.symPos f)
      = X86Backend.LprogBytesLinkReloc.regionOffset (T.regionEntries q) f := fun f hf =>
    regionOffset_entries q T.fns f (hfs f hf)
  obtain ⟨xs₂, hd, hr, hidx⟩ := R.decode
  have hK : ∀ f ∈ fs, T.entryIdx (T.symPos f)
      = X86Backend.LprogBytesLinkReloc.regionIndex (T.regionEntries q) f := by
    intro f hf
    cases hs : T.symPos f with
    | zero =>
        -- The first function has the symbol `f`.
        obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hT
        have hc : c.name = f := by
          have hmem := hfs f hf
          simp only [CalleeTab.names, hcs, List.map_cons, List.mem_cons] at hmem
          simp only [CalleeTab.symPos, hcs, List.findIdx?_cons] at hs
          by_contra hne'
          have hcf : (c.name == f) = false := by simpa using hne'
          simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hs
          rcases hmem with h | h
          · exact hne' h.symm
          · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
            have hsome : (cs.findIdx? (·.name == d.name)).isSome = true := by
              rw [List.findIdx?_isSome]
              exact List.any_eq_true.mpr ⟨d, hd, by simp⟩
            obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
            simp [hi] at hs
        simp only [CalleeTab.entryIdx_zero, CalleeTab.regionEntries, hcs, List.map_cons]
        cases cs with
        | nil => simp [X86Backend.LprogBytesLinkReloc.regionIndex]
        | cons _ _ => simp [X86Backend.LprogBytesLinkReloc.regionIndex, hc]
    | succ i =>
        have h1 := hO f hf
        rw [hs] at h1
        simp only [CalleeTab.entryIdx, hd, Option.bind_some, h1, hidx f hf, Option.getD_some]
  exact ⟨⟨xs₂, hd, hr, fun f hf => by simp only [hO f hf, hK f hf]; exact hidx f hf⟩,
    fun f hf => by rw [hK f hf]; exact R.block f hf, R.callFree⟩

/-- The block of a symbol of a table in the region of its entries is the program of the
    function of that symbol. -/
theorem CalleeTab.regionCode_lookup (T : CalleeTab)
    (q : CalleeData → List X86Backend.LprogBytesDecode.RInstr) {f : String} {c : CalleeData}
    (h : T.lookup f = some c) :
    X86Backend.LprogBytesLinkReloc.regionCode (T.regionEntries q) f = q c :=
  regionCode_entries q T.fns f c h

/-- **The symbol map of a caller of the functions of `T` with the printed body `b`**: a symbol
    of `T` at the byte length of the function of `b` and the offset `CalleeTab.entryOff` of the
    entry of its function, less the bytes `LprogBytes.prologueLen` in front of the body, and no
    other symbol. The relocating encoder counts a symbol base from the first byte of the body,
    and its bytes have the same length at every symbol map, so the base is the entry of the
    function in the code `CalleeTab.bytes` appended behind the caller
    (`LprogBytesLinkReloc.relocDisp_lands`). -/
def calleeSym (T : CalleeTab) (b : Lcmd) : String → Option Int := fun g =>
  if T.names.contains g then
    some (Int.ofNat ((X86Backend.LprogBytes.encodeLfundefBytesReloc (fun _ => none) b).length
        + T.entryOff (T.symPos g))
      - Int.ofNat (X86Backend.LprogBytes.prologueLen b))
  else none

/-- The symbol map at the table of one linked function: its symbol at the byte length of the
    function of `b` less the bytes in front of the body, and no other symbol. -/
theorem calleeSym_one (c : CalleeData) (b : Lcmd) (g : String) :
    calleeSym (CalleeTab.one c) b g =
      if g = c.name then
        some (Int.ofNat (X86Backend.LprogBytes.encodeLfundefBytesReloc (fun _ => none) b).length
          - Int.ofNat (X86Backend.LprogBytes.prologueLen b))
      else none := by
  by_cases h : g = c.name <;> simp [calleeSym, h]

/-- **The checks of the relocating encoder** on the printed body `b` of a caller of the
    functions of `T`: the code of each function is nonempty; the entries of the functions are
    instructions of the decoded code of the table (`CalleeTab.regionB`); the instructions of
    `b` have shapes (`DecodeGen.shapesOf`); and the items
    `LprogBytesLinkReloc.fundefItemsRelocL` of `b` at the shapes and the symbol map `calleeSym`
    pass `LprogBytesLinkReloc.branchOKRelocMap` and denote a program
    (`LprogBytesLinkReloc.expectedRelocMap`) under the target map `CalleeTab.linkMap` at the
    instruction count and the byte length of the function. -/
def calleeLinkB (T : CalleeTab) (b : Lcmd) : Bool :=
  T.fns.all (fun c => !c.bytes.isEmpty) && T.regionB &&
    match X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b with
    | none => false
    | some ds =>
        let items := X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym T b)
          (X86Backend.LprogBytesDecode.Params.ofBody b) b ds
        let m := X86Backend.LprogBytesLinkReloc.symTgt
          (T.linkMap (X86Backend.LprogBytesDecode.decCount items)
            (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym T b) b).length)
        X86Backend.LprogBytesLinkReloc.branchOKRelocMap items m 0 items
          && (X86Backend.LprogBytesLinkReloc.expectedRelocMap items m items).isSome

/-- At the table of one linked function the target map of the symbols gives each call of the
    items of a relocated function the first instruction and the first byte behind the
    caller. -/
theorem symTgt_linkMap_one (c : CalleeData) (symBase : String → Option Int)
    (P : X86Backend.LprogBytesDecode.Params) (b : Lcmd) (ds : List X86Backend.PhysAbiShape.DShape)
    (hs : X86Backend.DecodeGen.shapesOf P b = some ds) (n L : Nat) :
    ∀ it ∈ X86Backend.LprogBytesLinkReloc.fundefItemsRelocL symBase P b ds, it.target = none →
      ∀ d, it.dec = some (.call d) →
        X86Backend.LprogBytesLinkReloc.symTgt ((CalleeTab.one c).linkMap n L) it
          = (fun _ => some (n, L)) it := by
  intro it hit ht d hd
  obtain ⟨f, hf, -⟩ := X86Backend.LprogBytesLinkReloc.fundefItemsRelocL_sym symBase P b ds hs it
    hit ht d hd
  simp [X86Backend.LprogBytesLinkReloc.symTgt, hf]

/-- **`calleeLinkB` at the table of one linked function**: the code of the function is nonempty,
    the instructions of `b` have shapes, and the items pass `LprogBytesLinkReloc.branchOKReloc`
    and denote a program (`LprogBytesLinkReloc.expectedReloc`) at the instruction count and the
    byte length of the function. These are the Boolean hypotheses of
    `LprogBytesLinkReloc.decodeLprog_fundefRelocL_append`. -/
theorem calleeLinkB_one (c : CalleeData) (b : Lcmd) :
    calleeLinkB (CalleeTab.one c) b = (!c.bytes.isEmpty &&
      match X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b with
      | none => false
      | some ds =>
          let items := X86Backend.LprogBytesLinkReloc.fundefItemsRelocL
            (calleeSym (CalleeTab.one c) b) (X86Backend.LprogBytesDecode.Params.ofBody b) b ds
          let L := (X86Backend.LprogBytes.encodeLfundefBytesReloc
            (calleeSym (CalleeTab.one c) b) b).length
          X86Backend.LprogBytesLinkReloc.branchOKReloc items
              (X86Backend.LprogBytesDecode.decCount items) L 0 items
            && (X86Backend.LprogBytesLinkReloc.expectedReloc items
              (X86Backend.LprogBytesDecode.decCount items) L items).isSome) := by
  unfold calleeLinkB
  have hall : (CalleeTab.one c).fns.all (fun d => !d.bytes.isEmpty) = !c.bytes.isEmpty := by
    simp [CalleeTab.one]
  rw [hall, CalleeTab.regionB_one, Bool.and_true]
  cases hss : X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b with
  | none => rfl
  | some ds =>
      dsimp only
      rw [X86Backend.LprogBytesLinkReloc.branchOKRelocMap_congr _ _
          (symTgt_linkMap_one c _ _ b ds hss _ _),
        X86Backend.LprogBytesLinkReloc.expectedRelocMap_congr _ _
          (symTgt_linkMap_one c _ _ b ds hss _ _)]

/-- **The program of the function of a caller of the functions of `T`** with the printed body
    `b`: the program that the items `LprogBytesLinkReloc.fundefItemsRelocL` of `b` at its shapes
    and the symbol map `calleeSym` denote (`LprogBytesLinkReloc.expectedRelocMap`) under the
    target map `CalleeTab.linkMap` at the instruction count and the byte length of the function,
    in which a call of a function of `T` is a call of the index of its entry behind the last
    instruction; `none` when an instruction of `b` has no shape or the items denote no
    program. -/
def calleeProg (T : CalleeTab) (b : Lcmd) :
    Option (List X86Backend.LprogBytesDecode.RInstr) :=
  match X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b with
  | none => none
  | some ds =>
      let items := X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym T b)
        (X86Backend.LprogBytesDecode.Params.ofBody b) b ds
      X86Backend.LprogBytesLinkReloc.expectedRelocMap items
        (X86Backend.LprogBytesLinkReloc.symTgt
          (T.linkMap (X86Backend.LprogBytesDecode.decCount items)
            (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym T b) b).length))
        items

/-- **`calleeProg` at the table of one linked function**: the program that the items denote
    (`LprogBytesLinkReloc.expectedReloc`) at the instruction count and the byte length of the
    function. Under the checks `calleeLinkB`, the bytes `calleeBytes` decode to this program
    followed by the code of the function (`calleeBytes_decode`). -/
theorem calleeProg_one (c : CalleeData) (b : Lcmd) :
    calleeProg (CalleeTab.one c) b =
      match X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b with
      | none => none
      | some ds =>
          let items := X86Backend.LprogBytesLinkReloc.fundefItemsRelocL
            (calleeSym (CalleeTab.one c) b) (X86Backend.LprogBytesDecode.Params.ofBody b) b ds
          X86Backend.LprogBytesLinkReloc.expectedReloc items
            (X86Backend.LprogBytesDecode.decCount items)
            (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym (CalleeTab.one c) b) b).length
            items := by
  unfold calleeProg
  cases hss : X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b with
  | none => rfl
  | some ds =>
      dsimp only
      rw [X86Backend.LprogBytesLinkReloc.expectedRelocMap_congr _ _
        (symTgt_linkMap_one c _ _ b ds hss _ _)]

/-- **The bytes of a printed body at an optional table**: the gated encoder
    `encodeLfundefBytesChecked` without a table; with a table `T`, on a body the checks
    `calleeLinkB` accept, the bytes of the relocating
    encoder `encodeLfundefBytesReloc` at the symbol map `calleeSym`, followed by the code
    `CalleeTab.bytes` of `T`. On a body without remote symbol the relocating encoder is the
    encoder of the first case (`LprogBytesLinkReloc.encodeLfundefBytesReloc_of_local`). -/
def calleeBytes (callee : Option CalleeTab) (b : Lcmd) : Option (List (BitVec 8)) :=
  match callee with
  | none => X86Backend.LprogBytes.encodeLfundefBytesChecked b
  | some T =>
      if calleeLinkB T b then
        some (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym T b) b ++ T.bytes)
      else none

/-- Without a table the bytes are those of the gated encoder. -/
@[simp] theorem calleeBytes_none (b : Lcmd) :
    calleeBytes none b = X86Backend.LprogBytes.encodeLfundefBytesChecked b := rfl

/-- **The stages after the allocation** on an allocated program `P` with the gate `gate` on
    the printed body: the printed program `printedLprog`, the gated encoder on its first
    function body and the gate; the printed program and the bytes, or
    `none`. At a table the bytes are `calleeBytes`, the function followed by the code of
    the table. -/
def regionEncode (P : Lprog) (gate : Lcmd → Bool)
    (callee : Option CalleeTab := none) : Option (Lprog × List (BitVec 8)) :=
  match firstBody (printedLprog P) with
  | some b =>
      match calleeBytes callee b with
      | some bs => if gate b then some (printedLprog P, bs) else none
      | none => none
  | none => none

/-- A result of `regionEncode` has a printed body whose gated encoder's bytes are the
    result's bytes and that passes the gate. -/
theorem regionEncode_spec {P : Lprog} {gate : Lcmd → Bool}
    {out : Lprog × List (BitVec 8)} (h : regionEncode P gate = some out) :
    ∃ b, X86Backend.LprogBytes.encodeLfundefBytesChecked b = some out.2
      ∧ gate b = true := by
  unfold regionEncode at h
  split at h
  · rename_i b hb
    split at h
    · rename_i bs hbs
      split at h
      · rename_i hg
        obtain rfl := Option.some.inj h
        exact ⟨b, hbs, hg⟩
      · cases h
    · cases h
  · cases h

/-- **The symbols the shadow instructions of the exported code `code` call**, each once, in the
    order of their first call. -/
def codeCallSyms (code : List LinstrRM) : List String :=
  (code.filterMap fun i => (LprogIsa.shadowCall? i.fst).map (·.2.1)).eraseDups

/-- **The callee table of a structured program** `p` with the exported code `code`, among the
    linked functions `linked`: no table for a program without `call` (`NFProg.callFree`); for
    a program with a `call` and a word-array result, the table of the linked functions whose
    symbols the shadow instructions call (`codeCallSyms`), in the order of `linked`. The outer
    `none` is a refusal, in two cases.

    * The result is a register: the register-result allocation
      `comToLfundefPhysAbiFromVirt` expands the shadow instructions before it allocates,
      which gives a value live across the call a register the callee may change.
    * A called symbol is the symbol of no linked function. -/
def regionCallee (linked : List CalleeData) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (code : List LinstrRM) : Option (Option CalleeTab) :=
  if p.callFree = true then some none
  else
    match t, codeCallSyms code with
    | .stackArr _ _, f :: fs =>
        if (f :: fs).all fun g => linked.any (·.name == g) then
          some (some ⟨linked.filter fun c => (f :: fs).contains c.name⟩)
        else none
    | _, _ => none

/-- A program without `call` has no callee, at every list of linked functions. -/
theorem regionCallee_of_callFree {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : p.callFree = true) (linked : List CalleeData)
    (code : List LinstrRM) : regionCallee linked p code = some none := by
  unfold regionCallee
  rw [ite_eq_left h]

/-- **The table `regionCallee` finds**: the called symbols of the code are nonempty, each is the
    symbol of a linked function, and the table holds the linked functions with these symbols,
    in the order of `linked`. -/
theorem regionCallee_tab {linked : List CalleeData} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {code : List LinstrRM} {T : CalleeTab}
    (h : regionCallee linked p code = some (some T)) :
    p.callFree = false ∧ codeCallSyms code ≠ []
      ∧ (∀ f ∈ codeCallSyms code, ∃ c ∈ linked, c.name = f)
      ∧ T = ⟨linked.filter fun c => (codeCallSyms code).contains c.name⟩ := by
  unfold regionCallee at h
  split at h
  · cases h
  · rename_i hcf
    split at h
    · rename_i f fs hfs
      split at h
      · rename_i hall
        obtain rfl := (Option.some.inj (Option.some.inj h)).symm
        refine ⟨by simpa using hcf, by simp [hfs], fun g hg => ?_, by rw [hfs]⟩
        rw [hfs] at hg
        obtain ⟨c, hc, hcg⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall g hg)
        exact ⟨c, hc, beq_iff_eq.mp hcg⟩
      · cases h
    · cases h

/-- A program for which `regionCallee` finds a callee table has a word-array result. -/
theorem regionCallee_some_stackArr {linked : List CalleeData} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {code : List LinstrRM}
    {T : CalleeTab} (h : regionCallee linked p code = some (some T)) :
    ∃ w m, t = .stackArr w m := by
  unfold regionCallee at h
  split at h
  · cases h
  · split at h
    · exact ⟨_, _, rfl⟩
    · cases h

/-- The functions of the table `regionCallee` finds are a sublist of the linked functions. -/
theorem regionCallee_sublist {linked : List CalleeData} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {code : List LinstrRM} {T : CalleeTab}
    (h : regionCallee linked p code = some (some T)) : T.fns.Sublist linked := by
  obtain ⟨-, -, -, rfl⟩ := regionCallee_tab h
  exact List.filter_sublist

/-- **The table `regionCallee` finds is its own table**: at the functions of the table found
    among `linked`, `regionCallee` finds the same table. -/
theorem regionCallee_self {linked : List CalleeData} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {code : List LinstrRM} {T : CalleeTab}
    (h : regionCallee linked p code = some (some T)) :
    regionCallee T.fns p code = some (some T) := by
  obtain ⟨w, m, rfl⟩ := regionCallee_some_stackArr h
  obtain ⟨hcf, hne, hall, rfl⟩ := regionCallee_tab h
  unfold regionCallee
  rw [ite_eq_right (by simp [hcf])]
  obtain ⟨f, fs, hfs⟩ := List.exists_cons_of_ne_nil hne
  simp only [hfs]
  rw [ite_eq_left]
  · simp only [List.filter_filter, Bool.and_self]
  · refine List.all_eq_true.mpr fun g hg => ?_
    obtain ⟨c, hc, rfl⟩ := hall g (hfs ▸ hg)
    refine List.any_eq_true.mpr ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, beq_self_eq_true _⟩
    simpa [hfs] using hg

/-- At one linked function the table `regionCallee` finds is the table of that function. -/
theorem regionCallee_singleton {c : CalleeData} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {code : List LinstrRM} {T : CalleeTab}
    (h : regionCallee [c] p code = some (some T)) : T = CalleeTab.one c := by
  obtain ⟨-, hne, hall, rfl⟩ := regionCallee_tab h
  obtain ⟨f, fs, hfs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨d, hd, hdf⟩ := hall f (by simp [hfs])
  obtain rfl := List.mem_singleton.mp hd
  simp [CalleeTab.one, hfs, hdf]

/-- Without linked functions a program has no callee. -/
theorem regionCallee_nil {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {code : List LinstrRM} {c : Option CalleeTab}
    (h : regionCallee [] p code = some c) : c = none := by
  cases c with
  | none => rfl
  | some T =>
      obtain ⟨-, hne, hall, -⟩ := regionCallee_tab h
      obtain ⟨f, fs, hfs⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨d, hd, -⟩ := hall f (by simp [hfs])
      cases hd

/-! ## 8. The leakage of the virtual body and of the reference -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (FRun MemFCT fRun_unique
  lsemFuelMemFLeak instrLeakF instrLeakB instrLeakF_of_lopn instrLeakB_quiet
  lsemFuelMemFLeak_step lsemFuelMemFLeak_halt lsemFuelMemFLeak_fst)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (straightLeakFF_quiet
  lsemFuelMemFLeak_segF renEv)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAllocLeak (LeakCert
  instrLeakF_live SimPub EntryAt lsemFuelMemFLeak_prefix_split)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (movesOf_quiet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (evCountF instrLeakF_length)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-- **The events of the virtual body of a region export.** Let `p` be a program of
    `RegionExportable` without a `call`, with the export `r`, and let the frame map `fr`
    satisfy the facts of the entry check. At a valuation `V` the layout `σ` reads off the
    machine state `sa`, if the run `machRun` of `p` with the machine events of its export
    returns the events `μ` at `V`, then every terminating traced run of the copies of the
    parameter registers, the code of `r` and the register copy `ret` (when there is one)
    from the entry state `entryV`, at a map `un` of array names that fixes the argument
    names, has the trace `μ`: the copies emit no event. -/
theorem regionVirt_leak (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ret : Option (String × String))
    {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    {fuel : Nat} {v : Ctxt.Valuation (d := jasminDialect) ts} {μ : List CTLeak}
    (hm : machRun Pj Γ.length fn fuel p Γ.length 0 V = some (v, μ)) {ℓ : List CTLeak}
    (hrun : FRun (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList))
      { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } ℓ) :
    ℓ = μ := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) :=
    entryV_abiEntry E.argF E.argG hU
  have hag0 := storeAgreesM_of_abi hV habi
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := un) E.argF E.argG hS false
  have hag1 : StoreAgreesM Γ.length Γ.length
      ({ entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } } : LstateM) V :=
    StoreAgreesM.of_regionFrame (n := 0) rfl hag0
      ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  have hlen : (argBind σ nm).length = σ.args.length := by
    simp [argBind, movesOf_length, argPairs]
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨k, t0, hs, hat, -, -⟩ := exportR_leakSim Pj Γ.length fn hp hc Γ.length 0 r hr rfl
    le_rfl (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) (argBind σ nm)
    (movesOf ret.toList) rfl rfl
    (fun l _ => (findLabelMem_eq_none_iff l _).mpr (by rw [labelsOf_of_isLopn hlop]; simp))
    fuel V v μ
    { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
        lpc := σ.args.length } }, lfn := fn }, zf := false }
    hm ⟨rfl, hlen.symm⟩ hag1
  have hF : FRun (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList))
      { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
        lpc := σ.args.length } }, lfn := fn }, zf := false } μ := by
    cases ret with
    | none => exact fRun_of_stepsL hs (halted_of_atPc hat (by simp [singletonProgM, movesOf]))
    | some q =>
        obtain ⟨x, y⟩ := q
        have hmem : ExportRegions.movI y (.reg x) ∈ movesOf [(x, y)] :=
          List.mem_of_getElem? (i := 0) rfl
        have hi : (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf [(x, y)])).body[
            (argBind σ nm).length + r.code.length]? = some (ExportRegions.movI y (.reg x)) := by
          show (argBind σ nm ++ r.code ++ movesOf [(x, y)])[_]? = _
          rw [← List.length_append, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        obtain ⟨t1, hs1, hat1, -, -⟩ := steps_movReg (dst := y) (src := x) hat hi
        have h1 := stepsL_one hat hi hs1
        rw [instrLeakF_of_lopn (movesOf_isLopn _ _ hmem), movesOf_quiet _ _ hmem] at h1
        have := fRun_of_stepsL (hs.trans h1)
          (halted_of_atPc hat1 (by simp [singletonProgM, movesOf, Nat.add_assoc]))
        rwa [List.append_nil] at this
  obtain ⟨f, t, hf⟩ := hF
  refine fRun_unique hrun ⟨(argBind σ nm).length + f, t, ?_⟩
  rw [lsemFuelMemFLeak_segF _ fn rfl (argBind σ nm) (entryV σ fr sa un) false f _ hlop
    (fun j hj => by
      show (argBind σ nm ++ r.code ++ movesOf ret.toList)[0 + j]? = _
      rw [Nat.zero_add, List.append_assoc, List.getElem?_append_left hj]) hpre, hf,
    straightLeakFF_quiet (argBind σ nm) (movesOf_quiet _)]
  rfl

/-- **A halting traced run is a traced run of steps.** A run of the traced flag machine on
    `P` from `s` that returns the state `t` with the trace `ℓ` is a run of some number of
    steps from `s` to `t` that emits `ℓ`. -/
theorem stepsL_of_lsemFuelMemFLeak (P : LprogM) :
    ∀ (f : Nat) {s t : LstateMF} {ℓ : List CTLeak},
      lsemFuelMemFLeak P f s = some (t, ℓ) → ∃ n, StepsL P n s t ℓ := by
  intro f
  induction f with
  | zero =>
      intro s t ℓ h
      cases hf : findInstrMem P s.prog with
      | none =>
          rw [lsemFuelMemFLeak_halt P 0 s hf] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨0, StepsL.refl P s⟩
      | some i => simp [lsemFuelMemFLeak, hf] at h
  | succ f ih =>
      intro s t ℓ h
      cases hf : findInstrMem P s.prog with
      | none =>
          rw [lsemFuelMemFLeak_halt P _ s hf] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨0, StepsL.refl P s⟩
      | some i =>
          cases hu : evalInstrPMemF P i s with
          | none => simp [lsemFuelMemFLeak, hf, hu] at h
          | some u =>
              rw [lsemFuelMemFLeak_step P f i s u hf hu] at h
              obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
              obtain ⟨n, hn⟩ := ih hq
              exact ⟨n + 1, steps_succ_iff.mpr ⟨i, u, hf, hu, hn.1⟩,
                by rw [stepsLeak_succ hf hu, hn.2]⟩

/-- The events of an instruction do not depend on the program counter. -/
theorem instrLeakF_shiftPc (k : Nat) (i : LinstrRM) (s : LstateMF) :
    instrLeakF i (Ascent.IsaCall.shiftPc k s) = instrLeakF i s := by
  unfold instrLeakF
  split
  · rfl
  · exact X86Backend.ImageAddrLeak.instrLeakB_lpc _ _ i

/-- **Relocation of a traced run of steps.** When no label of `B` is declared in `pre`, a
    run of steps of `B` from `s` to `t` that emits `ℓ` is a run of as many steps of
    `pre ++ B ++ post` from `shiftPc pre.length s` to `shiftPc pre.length t` that emits
    `ℓ`. -/
theorem stepsL_relocate (fn : String) {pre B : List LinstrRM} (post : List LinstrRM)
    (hfresh : Ascent.IsaCall.LabelsFresh pre B) :
    ∀ {n : Nat} {s t : LstateMF} {ℓ : List CTLeak}, StepsL (singletonProgM fn B) n s t ℓ →
      StepsL (singletonProgM fn (pre ++ B ++ post)) n (Ascent.IsaCall.shiftPc pre.length s)
        (Ascent.IsaCall.shiftPc pre.length t) ℓ := by
  intro n
  induction n with
  | zero =>
      intro s t ℓ h
      obtain rfl := steps_zero_iff.mp h.1
      obtain rfl : [] = ℓ := h.2
      exact StepsL.refl _ _
  | succ n ih =>
      intro s t ℓ h
      obtain ⟨i, u, hf, hu, h'⟩ := steps_succ_iff.mp h.1
      obtain ⟨hn, hl⟩ := ih ⟨h', rfl⟩
      have hfB : B[s.prog.base.lpc]? = some i ∧ s.prog.lfn = fn := by
        unfold findInstrMem at hf
        split at hf
        · next hl => exact ⟨hf, hl⟩
        · cases hf
      have hf' : findInstrMem (singletonProgM fn (pre ++ B ++ post))
          (Ascent.IsaCall.shiftPc pre.length s).prog = some i := by
        unfold findInstrMem
        rw [ite_eq_left (show (Ascent.IsaCall.shiftPc pre.length s).prog.lfn
          = (singletonProgM fn (pre ++ B ++ post)).lfn from hfB.2)]
        exact Ascent.IsaCall.getElem?_relocate post hfB.1
      have hu' : evalInstrPMemF (singletonProgM fn (pre ++ B ++ post)) i
          (Ascent.IsaCall.shiftPc pre.length s) = some (Ascent.IsaCall.shiftPc pre.length u) := by
        have := Ascent.IsaCall.step_relocate x86Isa fn post
          (Ascent.IsaCall.x86_stepRelocates fn pre B post) hfresh i
          (List.mem_of_getElem? hfB.1) (s := s) (u := u)
          (by rw [X86Backend.X86Isa.x86Isa_step]; exact hu)
        rwa [X86Backend.X86Isa.x86Isa_step] at this
      refine ⟨steps_succ_iff.mpr ⟨i, _, hf', hu', hn⟩, ?_⟩
      rw [stepsLeak_succ hf' hu', hl, ← h.2, stepsLeak_succ hf hu, instrLeakF_shiftPc]

/-- **The traced steps of the webs of a region export behind the parameter copies.** Let `p`
    be a program of `RegionExportable` without a `call`, with the export `r`, let the frame
    map `fr` satisfy the facts of the entry check, and let the code of `r` pass `webB` at the
    position map `w`, the liveness table `Lw` and the names `obs`, and `webLeakB`. If
    `machRun` of `p` returns `v` with the events `μ` at a valuation `V` the layout `σ` reads
    off `sa`, then the code of `r` alone has a halting traced run from `entryV` with the
    trace `μ` into a state `t` that agrees with the returned operands at `v` within the
    region frame of `entryV`; the trace `g` computed by `webG` along that run is the trace of
    a run of steps of `argBind σ nm ++ webRen w ao r.code ++ post` from the state after the
    copies of the parameter registers to a state `t'` at the end of the renamed code, whose
    arrays at the names `obs` are those of `t`. -/
theorem regionVirt_stepsL_webs (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String)
    (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (post : List LinstrRM)
    {fr : String → Option (BitVec 64)} (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V)
    {fuel : Nat} {v : Ctxt.Valuation (d := jasminDialect) ts} {μ : List CTLeak}
    (hm : machRun Pj Γ.length fn fuel p Γ.length 0 V = some (v, μ))
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {w : Nat → String → String}
    {Lw : Nat → List String} {obs : List String}
    (hw : X86Backend.ArrWebs.webB w r.code Lw obs aa ao = true)
    (hx : X86Backend.ArrWebsLeak.webLeakB w ao r.code = true) :
    ∃ (f n : Nat) (t t' : LstateMF) (g : List CTLeak),
      lsemFuelMemFLeak (singletonProgM fn r.code) f
          { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some (t, μ)
      ∧ X86Backend.ImageLoopWLeak.GTr (X86Backend.ArrWebsLeak.webG w ao r.code)
          (singletonProgM fn r.code)
          { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } g
      ∧ StepsL (singletonProgM fn (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ post))
          n { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
            lpc := σ.args.length } }, lfn := fn }, zf := false } t' g
      ∧ atPc (singletonProgM fn (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ post))
          (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code).length t'
      ∧ ResAgrees Γ.length r.depth t.prog.base r.res v
      ∧ RegionFrame Γ.length 0 (entryV σ fr sa un) t.prog.base
      ∧ ∀ x ∈ obs, t'.prog.base.larr x = t.prog.base.larr x := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) :=
    entryV_abiEntry E.argF E.argG hU
  have hag0 := storeAgreesM_of_abi hV habi
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨k, t, hs, hat, hres, hfrm⟩ := exportR_leakSim Pj Γ.length fn hp hc Γ.length 0 r hr
    rfl le_rfl (singletonProgM fn r.code) [] [] rfl (by simp [singletonProgM])
    (fun l _ => rfl) fuel V v μ { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false }
    hm ⟨rfl, habi.pc⟩ hag0
  have ht : lsemFuelMemFLeak (singletonProgM fn r.code) (k + 0)
      { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some (t, μ) := by
    rw [lsemFuelMemFLeak_stepsL 0 hs, lsemFuelMemFLeak_halt _ 0 t
      (halted_of_atPc hat (by simp [singletonProgM]))]
    simp
  obtain ⟨t'', g, hw', hG, hRt, -, hlt⟩ := X86Backend.ArrWebsLeak.lsemFuelMemFLeak_webs_entry
    (fn := fn) (s := { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false })
    (s' := { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false })
    hw hx (k + 0) rfl habi.pc ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ rfl rfl ht
  obtain ⟨n, hn⟩ := stepsL_of_lsemFuelMemFLeak _ _ hw'
  have hrel := stepsL_relocate fn (pre := argBind σ nm) post
    (fun l _ _ => (findLabelMem_eq_none_iff l _).mpr (by rw [labelsOf_of_isLopn hlop]; simp)) hn
  rw [shiftPc_argBind_entryV habi] at hrel
  have hfn : t''.prog.lfn = fn := LprogCallCut.fnStable_x86Isa.lsemFuelMemF_lfn _ _ _ _
    (by rw [X86Backend.X86Isa.x86Isa_lsemFuelMemF, ← lsemFuelMemFLeak_fst, hw']; rfl)
  have hpc : t''.prog.base.lpc = (X86Backend.ArrWebs.webRen w ao r.code).length := by
    rw [X86Backend.ImageCoalesceCfg.coRel_lpc hRt, hlt]; simp [X86Backend.ArrWebs.webRen]
  exact ⟨k + 0, n, t, _, g, ht, hG, hrel,
    ⟨hfn, by rw [Ascent.IsaCall.shiftPc_lpc, hpc, List.length_append]⟩, hres, hfrm,
    fun x hx => hRt.arr x hx⟩

/-- **The events of the virtual body of the webs of a region export.** Under the hypotheses
    of `regionVirt_leak`, with the code of `r` accepted by `webB` and `webLeakB` at the
    position map `w`, every terminating traced run of the copies of the parameter registers,
    the renamed code `webRen w ao r.code` and the register copy `ret` from the entry state
    `entryV` has the trace computed by `webG` along a halting traced run of the code of `r`
    from `entryV` with the trace `μ`. -/
theorem regionVirt_leak_webs (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String)
    (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ret : Option (String × String))
    {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    {fuel : Nat} {v : Ctxt.Valuation (d := jasminDialect) ts} {μ : List CTLeak}
    (hm : machRun Pj Γ.length fn fuel p Γ.length 0 V = some (v, μ))
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {w : Nat → String → String}
    {Lw : Nat → List String} {obs : List String}
    (hw : X86Backend.ArrWebs.webB w r.code Lw obs aa ao = true)
    (hx : X86Backend.ArrWebsLeak.webLeakB w ao r.code = true) {ℓ : List CTLeak}
    (hrun : FRun (singletonProgM fn
        (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ movesOf ret.toList))
      { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } ℓ) :
    ∃ (f : Nat) (t : LstateMF),
      lsemFuelMemFLeak (singletonProgM fn r.code) f
          { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some (t, μ)
      ∧ X86Backend.ImageLoopWLeak.GTr (X86Backend.ArrWebsLeak.webG w ao r.code)
          (singletonProgM fn r.code)
          { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } ℓ := by
  obtain ⟨f, n, t, t', g, ht, hG, hs, hat, -, -, -⟩ := regionVirt_stepsL_webs Pj σ nm fn hp hc
    hr (movesOf ret.toList) E un hU sa V hV hm hw hx
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := un) E.argF E.argG hS false
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  have hF : FRun (singletonProgM fn
        (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ movesOf ret.toList))
      { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
        lpc := σ.args.length } }, lfn := fn }, zf := false } g := by
    cases ret with
    | none => exact fRun_of_stepsL hs (halted_of_atPc hat (by simp [singletonProgM, movesOf]))
    | some q =>
        obtain ⟨x, y⟩ := q
        have hmem : ExportRegions.movI y (.reg x) ∈ movesOf [(x, y)] :=
          List.mem_of_getElem? (i := 0) rfl
        have hi : (singletonProgM fn (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code
            ++ movesOf [(x, y)])).body[
              (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code).length]?
            = some (ExportRegions.movI y (.reg x)) := by
          show (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ movesOf [(x, y)])[_]? = _
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        obtain ⟨t1, hs1, hat1, -, -⟩ := steps_movReg (dst := y) (src := x) hat hi
        have h1 := stepsL_one hat hi hs1
        rw [instrLeakF_of_lopn (movesOf_isLopn _ _ hmem), movesOf_quiet _ _ hmem] at h1
        have := fRun_of_stepsL (hs.trans h1)
          (halted_of_atPc hat1 (by simp [singletonProgM, movesOf]; omega))
        rwa [List.append_nil] at this
  obtain ⟨f', u, hf⟩ := hF
  refine ⟨f, t, ht, ?_⟩
  rw [fRun_unique hrun ⟨(argBind σ nm).length + f', u, ?_⟩]
  · exact hG
  rw [lsemFuelMemFLeak_segF _ fn rfl (argBind σ nm) (entryV σ fr sa un) false f' _ hlop
    (fun j hj => by
      show (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ movesOf ret.toList)[0 + j]?
        = _
      rw [Nat.zero_add, List.append_assoc, List.getElem?_append_left hj]) hpre, hf,
    straightLeakFF_quiet (argBind σ nm) (movesOf_quiet _)]
  rfl

/-- **Constant time of the source events of a program on the valuations of a layout.**
    Under the precondition `Pre` on machine states, the restriction of `NFCT` to valuations
    the layout `σ` reads off a machine state that satisfies `σ.Regions` and `Pre`: such
    valuations that are equal on the positions `L` marks public give the same events. Total
    constant time `NFCT` gives it at every precondition. -/
theorem nfCT_restrict (Pj : JLeakParams) (σ : AbiLayout) (Pre : AState → Prop) {fuel : Nat}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {L : Labels Γ} (h : NFCT (jLeakModel Pj) L fuel p) :
    ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd :=
  fun V₁ V₂ _ _ hpub => h V₁ V₂ hpub

/-- **The entry relation of the virtual body of a region export.** Two states are related
    when they are the entry states `entryV`, at the frame maps `fr sa₁` and `fr sa₂` and the
    map `un` of array names, of two machine states `sa₁` and `sa₂` at which the layout `σ`
    reads off valuations that are equal on the positions `L` marks public, both frame maps
    satisfy the facts of the entry check and give the sources of the parameters (`ArgSrc`),
    both machine states satisfy `σ.Regions` and the precondition `Pre`, and the program `p`
    denotes within `fuel` at the first valuation in the empty call environment. -/
def RegionVirtPub (σ : AbiLayout) (nm : String → String) (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (L : Labels Γ) (Pre : AState → Prop) (fr : AState → String → Option (BitVec 64))
    (un : String → String) (s₁ s₂ : LstateMF) : Prop :=
  ∃ (sa₁ sa₂ : AState) (V₁ V₂ : Ctxt.Valuation Γ),
    PubEqV L V₁ V₂ ∧ AbiValOf σ sa₁ V₁ ∧ AbiValOf σ sa₂ V₂
      ∧ EntryFacts σ nm (fr sa₁) ∧ EntryFacts σ nm (fr sa₂)
      ∧ ArgSrc σ nm (fr sa₁) sa₁ ∧ ArgSrc σ nm (fr sa₂) sa₂
      ∧ σ.Regions sa₁ ∧ σ.Regions sa₂ ∧ Pre sa₁ ∧ Pre sa₂
      ∧ s₁ = { prog := { base := entryV σ (fr sa₁) sa₁ un, lfn := fn }, zf := false }
      ∧ s₂ = { prog := { base := entryV σ (fr sa₂) sa₂ un, lfn := fn }, zf := false }
      ∧ (p.denoteAt CallEnv.empty fuel V₁).isSome = true

/-- **The event check of the webs of an exported code** `r`: the check
    `ArrWebsLeak.webLeakB` of the code of `r` at the position map of `regionWebs ex r aa ao`.
    -/
def regionWebsLeakB (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : Bool :=
  X86Backend.ArrWebsLeak.webLeakB
    (X86Backend.ArrWebs.webLook (X86Backend.ArrWebs.webTab ao
      (tabAt (liveArrTab r.code (regionWebsObs ex r) aa ao false)) (regionWebsObs ex r) r.code))
    ao r.code

/-- **The event check of an exported code**: an exported code `r` of `p` that differs from
    the export `r0` of `p` is the webs of `r0`, and `r0` passes `regionWebsLeakB ex`. -/
def RegionWebsLeak (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) (r : Exported) : Prop :=
  ∀ r0, exportR Γ.length fn p Γ.length 0 = some r0 → r ≠ r0 → regionWebsLeakB ex r0 = true

/-- The export of a program passes the event check `RegionWebsLeak`. -/
theorem regionWebsLeak_of_exportR {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (ex : List String) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) : RegionWebsLeak fn p ex r := by
  intro r0 hr0 hne
  rw [hr] at hr0
  exact absurd (Option.some.inj hr0) hne

/-- **Every exported code passes the event check**: the webs rename the code only when the
    renamed code keeps its events (`regionWebs`). -/
theorem regionWebsLeak_of_regionExp {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) : RegionWebsLeak fn p ex r := by
  intro r0 hr0 hne
  obtain ⟨r1, h1, h⟩ := hr
  obtain rfl := Option.some.inj (h1.symm.trans hr0)
  rcases h with rfl | rfl
  · exact absurd rfl hne
  · unfold regionWebs at hne
    unfold regionWebsLeakB
    split at hne
    · next hc => exact ((Bool.and_eq_true _ _).mp hc).2
    · exact absurd rfl hne

/-- **The two shapes of an exported code that passes the event check.** An exported code `r`
    of `RegionExp fn p ex r` with `RegionWebsLeak fn p ex r` is the export `r0` of `p`, or
    `r0` with its code renamed by `ArrWebs.webRen w` at a position map `w` at which the code
    of `r0` passes `webB` at the names `regionWebsObs ex r0` and `webLeakB`. -/
theorem regionExp_webs_cases {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) (hx : RegionWebsLeak fn p ex r) :
    ∃ r0, exportR Γ.length fn p Γ.length 0 = some r0
      ∧ (r = r0 ∨ ∃ (w : Nat → String → String) (Lw : Nat → List String),
        X86Backend.ArrWebs.webB w r0.code Lw (regionWebsObs ex r0) (fun _ _ => none)
            (fun _ => none) = true
          ∧ X86Backend.ArrWebsLeak.webLeakB w (fun _ => none) r0.code = true
          ∧ r = { r0 with code := X86Backend.ArrWebs.webRen w (fun _ => none) r0.code }) := by
  obtain ⟨r0, hr0, h⟩ := hr
  refine ⟨r0, hr0, ?_⟩
  by_cases hrr : r = r0
  · exact Or.inl hrr
  · have hw := h.resolve_left hrr
    have hl := hx r0 hr0 hrr
    unfold regionWebs at hw
    split at hw
    · next hc => exact Or.inr ⟨_, _, ((Bool.and_eq_true _ _).mp hc).1, hl, hw⟩
    · exact absurd hw hrr

/-- **Constant time of the virtual body of a region export.** A program of
    `RegionExportable` without a `call` that is constant time at the source events for the
    entry labels `L` at `fuel`, on the valuations the layout `σ` reads off machine states
    that satisfy `σ.Regions` and the precondition `Pre`, has a virtual body, the copies of
    the parameter registers, the exported code and the register copy `ret`, that is constant
    time on the traced flag machine between the entry states of `RegionVirtPub`. -/
theorem regionVirt_memFCT (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String)
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ret : Option (String × String))
    (fr : AState → String → Option (BitVec 64)) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) :
    MemFCT (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList))
      (RegionVirtPub σ nm fn fuel p L Pre fr un) := by
  rintro s₁ s₂ ℓ₁ ℓ₂
    ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl, hden⟩ r₁ r₂
  obtain ⟨⟨v₁, t₁⟩, h₁⟩ := leakRun_eq_some_of_denote Pj fuel p V₁ hden
  have hnf := hct V₁ V₂ ⟨sa₁, R₁, P₁, hV₁⟩ ⟨sa₂, R₂, P₂, hV₂⟩ hpub
  rw [h₁] at hnf
  cases h₂ : NFProg.leakRun (jLeakModel Pj) fuel p V₂ with
  | none => rw [h₂] at hnf; cases hnf
  | some x₂ =>
      obtain ⟨v₂, t₂⟩ := x₂
      rw [h₂] at hnf
      obtain rfl : t₁ = t₂ := Option.some.inj hnf
      obtain ⟨-, -, μ, m₁, m₂⟩ :=
        machRun_of_leakRun Pj Γ.length fn fuel hp hc Γ.length 0 V₁ V₂ v₁ v₂ t₁ t₁ [] [] h₁ h₂
          rfl
      rw [regionVirt_leak Pj σ nm fn hp hc hr ret E₁ un hU sa₁ V₁ hV₁ S₁ m₁ r₁,
        regionVirt_leak Pj σ nm fn hp hc hr ret E₂ un hU sa₂ V₂ hV₂ S₂ m₂ r₂]

/-- **Constant time of the virtual body of an exported code.** Under the hypotheses of
    `regionVirt_memFCT`, at an exported code `r` of `RegionExp fn p ex r` that passes the
    event check `RegionWebsLeak`, the virtual body of `r` is constant time on the traced flag
    machine between the entry states of `RegionVirtPub`. For the export it is
    `regionVirt_memFCT`; for its webs both traces are computed by `webG` along runs of the
    code of the export with the source events (`regionVirt_leak_webs`), and are equal by
    `ImageLoopWLeak.gTr_eq`. -/
theorem regionVirt_memFCT_of_regionExp (Pj : JLeakParams) (σ : AbiLayout)
    (nm : String → String) (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) (hx : RegionWebsLeak fn p ex r) (ret : Option (String × String))
    (fr : AState → String → Option (BitVec 64)) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) :
    MemFCT (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList))
      (RegionVirtPub σ nm fn fuel p L Pre fr un) := by
  obtain ⟨r0, hr0, rfl | ⟨w, Lw, hw, hwx, rfl⟩⟩ := regionExp_webs_cases hr hx
  · exact regionVirt_memFCT Pj σ nm fn fuel hp hc hct hr0 ret fr un hU
  rintro s₁ s₂ ℓ₁ ℓ₂
    ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl, hden⟩ r₁ r₂
  obtain ⟨⟨v₁, t₁⟩, h₁⟩ := leakRun_eq_some_of_denote Pj fuel p V₁ hden
  have hnf := hct V₁ V₂ ⟨sa₁, R₁, P₁, hV₁⟩ ⟨sa₂, R₂, P₂, hV₂⟩ hpub
  rw [h₁] at hnf
  cases h₂ : NFProg.leakRun (jLeakModel Pj) fuel p V₂ with
  | none => rw [h₂] at hnf; cases hnf
  | some x₂ =>
      obtain ⟨v₂, t₂⟩ := x₂
      rw [h₂] at hnf
      obtain rfl : t₁ = t₂ := Option.some.inj hnf
      obtain ⟨-, -, μ, m₁, m₂⟩ :=
        machRun_of_leakRun Pj Γ.length fn fuel hp hc Γ.length 0 V₁ V₂ v₁ v₂ t₁ t₁ [] [] h₁ h₂
          rfl
      obtain ⟨f₁, u₁, k₁, hG₁⟩ :=
        regionVirt_leak_webs Pj σ nm fn hp hc hr0 ret E₁ un hU sa₁ V₁ hV₁ S₁ m₁ hw hwx r₁
      obtain ⟨f₂, u₂, k₂, hG₂⟩ :=
        regionVirt_leak_webs Pj σ nm fn hp hc hr0 ret E₂ un hU sa₂ V₂ hV₂ S₂ m₂ hw hwx r₂
      exact X86Backend.ImageLoopWLeak.gTr_eq _ fn _ f₁ _ u₁ _ k₁ f₂ _ u₂ k₂ rfl rfl
        ((entryV_abiEntry E₁.argF E₁.argG hU).pc.trans
          (entryV_abiEntry E₂.argF E₂.argG hU).pc.symm) _ _ hG₁ hG₂

/-- **The entry states of `RegionVirtPub` have terminating runs.** For a program of
    `RegionExportable` that is constant time at the source events for the entry labels `L`
    at `fuel` on the valuations the layout `σ` reads off machine states that satisfy
    `σ.Regions` and the precondition `Pre`, and an exported code `r` of
    `RegionExp fn p ex r`, two states related by `RegionVirtPub` are states of the function
    `fn` at position `0` from each of which the virtual body of `r` has a terminating traced
    run: the program denotes at the second valuation because its source events there are
    those at the first. -/
theorem regionVirtPub_simPub_of_regionExp (Pj : JLeakParams) (σ : AbiLayout)
    (nm : String → String) (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) (ret : Option (String × String))
    (fr : AState → String → Option (BitVec 64)) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) {s₁ s₂ : LstateMF}
    (h : RegionVirtPub σ nm fn fuel p L Pre fr un s₁ s₂) :
    SimPub (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) (EntryAt fn)
      (RegionVirtPub σ nm fn fuel p L Pre fr un) s₁ s₂ := by
  have hrun : ∀ (sa : AState) (V : Ctxt.Valuation Γ), AbiValOf σ sa V →
      EntryFacts σ nm (fr sa) → ArgSrc σ nm (fr sa) sa →
      (p.denoteAt CallEnv.empty fuel V).isSome = true →
      ∃ ℓ, FRun (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList))
        { prog := { base := entryV σ (fr sa) sa un, lfn := fn }, zf := false } ℓ := by
    intro sa V hV E hS hden
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hden
    obtain ⟨k, t, -, -, hk, -⟩ :=
      regionVirt_run_of_regionExp σ nm fn hp hr ret E un hU sa V hV hS fuel v hv
    have hfst := lsemFuelMemFLeak_fst
      (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) k
      { prog := { base := entryV σ (fr sa) sa un, lfn := fn }, zf := false }
    rw [hk] at hfst
    obtain ⟨q, hq, -⟩ := Option.map_eq_some_iff.mp hfst
    exact ⟨q.2, k, q.1, hq⟩
  obtain ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl, hden⟩ := h
  have hden₂ : (p.denoteAt CallEnv.empty fuel V₂).isSome = true := by
    obtain ⟨x, h₁⟩ := leakRun_eq_some_of_denote Pj fuel p V₁ hden
    have hnf := hct V₁ V₂ ⟨sa₁, R₁, P₁, hV₁⟩ ⟨sa₂, R₂, P₂, hV₂⟩ hpub
    rw [h₁] at hnf
    rw [← NFProg.leakRun_fst (jLeakModel Pj) fuel p V₂]
    cases h₂ : NFProg.leakRun (jLeakModel Pj) fuel p V₂ with
    | none => rw [h₂] at hnf; cases hnf
    | some y => rfl
  exact ⟨⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl, hden⟩,
    ⟨rfl, (entryV_abiEntry E₁.argF E₁.argG hU).pc⟩,
    ⟨rfl, (entryV_abiEntry E₂.argF E₂.argG hU).pc⟩,
    hrun sa₁ V₁ hV₁ E₁ S₁ hden, hrun sa₂ V₂ hV₂ E₂ S₂ hden₂⟩

/-- **The entry states of `RegionVirtPub` have terminating runs** of the virtual body of the
    export `r` of `p`: `regionVirtPub_simPub_of_regionExp` at `r`. -/
theorem regionVirtPub_simPub (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String)
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ret : Option (String × String))
    (fr : AState → String → Option (BitVec 64)) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) {s₁ s₂ : LstateMF}
    (h : RegionVirtPub σ nm fn fuel p L Pre fr un s₁ s₂) :
    SimPub (singletonProgM fn (argBind σ nm ++ r.code ++ movesOf ret.toList)) (EntryAt fn)
      (RegionVirtPub σ nm fn fuel p L Pre fr un) s₁ s₂ :=
  regionVirtPub_simPub_of_regionExp Pj σ nm fn fuel hp hct (regionExp_of_exportR [] hr) ret fr
    un hU h

/-- **The events of the virtual body of a region export with a result copy.** Under the
    hypotheses of `regionVirt_leak` on a program without a `call` with a result of
    `m < 2 ^ 64` words, and those of `regionVirt_run_copy` on the result copy of `src` into
    `D`, every terminating traced run of the copies of the parameter registers, the code of
    `r` and the result copy `resCopyCode src D m` from the entry state `entryV` emits the
    events `μ` of the source machine run followed by `resCopyLeak src D m`. -/
theorem regionVirt_leak_copy (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String)
    (fn : String) {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    {fuel : Nat} {v : Ctxt.Valuation (d := jasminDialect) [.stackArr 64 m]} {μ : List CTLeak}
    (hmr : machRun Pj Γ.length fn fuel p Γ.length 0 V = some (v, μ)) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1)) {ℓ : List CTLeak}
    (hrun : FRun (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m))
      { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } ℓ) :
    ℓ = μ ++ resCopyLeak src D m := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) :=
    entryV_abiEntry E.argF E.argG hU
  have hag0 := storeAgreesM_of_abi hV habi
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := un) E.argF E.argG hS false
  have hag1 : StoreAgreesM Γ.length Γ.length
      ({ entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } } : LstateM) V :=
    StoreAgreesM.of_regionFrame (n := 0) rfl hag0
      ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  have hlen : (argBind σ nm).length = σ.args.length := by
    simp [argBind, movesOf_length, argPairs]
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨k, t0, hs, hat, hres, hfrm⟩ := exportR_leakSim Pj Γ.length fn hp hc Γ.length 0 r hr
    rfl le_rfl (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m))
    (argBind σ nm) (resCopyCode src D m) rfl rfl
    (fun l _ => (findLabelMem_eq_none_iff l _).mpr (by rw [labelsOf_of_isLopn hlop]; simp))
    fuel V v μ
    { prog := { base := { entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
        lpc := σ.args.length } }, lfn := fn }, zf := false }
    hmr ⟨rfl, hlen.symm⟩ hag1
  obtain ⟨op, hop, harr⟩ := hres.decodeArrM_single
  have harr' : t0.prog.base.getArr src 64 m = some (Ctxt.Var.lookup (d := jasminDialect)
      (Γ := [.stackArr 64 m]) (t := .stackArr 64 m) .here v) := by
    rw [← hsrc op hop]; exact harr
  obtain ⟨a0, hD0⟩ : ∃ a0, t0.prog.base.getArr D 64 m = some a0 := by
    obtain ⟨j, a, hj, hk, rfl⟩ := hD
    rw [hfrm.2 (argName j) 64 m (fun i _ => (JasminLsemSimulation.regName_ne_argName i j).symm)
      (fun l _ => (JasminLsemExportTransfer.loopCtr_ne_argName l j).symm)]
    exact ⟨_, habi.arr j a m hj hk⟩
  obtain ⟨u, hsu, hatu, -⟩ := steps_resCopy
    (P := singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m)) hm
    (argBind σ nm ++ r.code) [] t0 (by simp [singletonProgM])
    (by rw [List.length_append]; exact hat) harr' hD0 hfr
  have hF := fRun_of_stepsL (hs.trans hsu) (halted_of_atPc hatu (by
    simp [singletonProgM, resCopyCode, List.length_flatMap, resCopyStep]; omega))
  obtain ⟨f, t, hf⟩ := hF
  refine fRun_unique hrun ⟨(argBind σ nm).length + f, t, ?_⟩
  rw [lsemFuelMemFLeak_segF _ fn rfl (argBind σ nm) (entryV σ fr sa un) false f _ hlop
    (fun j hj => by
      show (argBind σ nm ++ r.code ++ resCopyCode src D m)[0 + j]? = _
      rw [Nat.zero_add, List.append_assoc, List.getElem?_append_left hj]) hpre, hf,
    straightLeakFF_quiet (argBind σ nm) (movesOf_quiet _)]
  rfl

/-- **The events of the virtual body of the webs of a region export with a result copy.**
    Under the hypotheses of `regionVirt_leak_copy`, with the code of `r` accepted by `webB`
    at the names `obs` and by `webLeakB` at the position map `w`, where `obs` holds the name
    of the returned operand and the target `D` of the copy, every terminating traced run of
    the copies of the parameter registers, the renamed code `webRen w ao r.code` and the
    result copy `resCopyCode src D m` from the entry state `entryV` has the trace computed by
    `webG` along a halting traced run of the code of `r` from `entryV` with the trace `μ`,
    followed by `resCopyLeak src D m`. -/
theorem regionVirt_leak_copy_webs (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String)
    (fn : String) {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {fr : String → Option (BitVec 64)}
    (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hS : ArgSrc σ nm fr sa)
    {fuel : Nat} {v : Ctxt.Valuation (d := jasminDialect) [.stackArr 64 m]} {μ : List CTLeak}
    (hmr : machRun Pj Γ.length fn fuel p Γ.length 0 V = some (v, μ)) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1))
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {w : Nat → String → String}
    {Lw : Nat → List String} {obs : List String}
    (hw : X86Backend.ArrWebs.webB w r.code Lw obs aa ao = true)
    (hx : X86Backend.ArrWebsLeak.webLeakB w ao r.code = true)
    (hsO : ∀ op, r.res = [op] → operandName op ∈ obs) (hDO : D ∈ obs) {ℓ : List CTLeak}
    (hrun : FRun (singletonProgM fn
        (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ resCopyCode src D m))
      { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } ℓ) :
    ∃ (f : Nat) (t : LstateMF) (g : List CTLeak),
      lsemFuelMemFLeak (singletonProgM fn r.code) f
          { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some (t, μ)
      ∧ X86Backend.ImageLoopWLeak.GTr (X86Backend.ArrWebsLeak.webG w ao r.code)
          (singletonProgM fn r.code)
          { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } g
      ∧ ℓ = g ++ resCopyLeak src D m := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) :=
    entryV_abiEntry E.argF E.argG hU
  have hpre := argBind_entryV (nm := nm) (sa := sa) (un := un) E.argF E.argG hS false
  have hlop : ∀ i ∈ argBind σ nm, JasminLsemMemLoop.IsLopn i := movesOf_isLopn _
  obtain ⟨f, n, t, t0, g, ht, hG, hs, hat, hres, hfrm, harrO⟩ := regionVirt_stepsL_webs Pj σ nm
    fn hp hc hr (resCopyCode src D m) E un hU sa V hV hmr hw hx
  obtain ⟨op, hop, harr⟩ := hres.decodeArrM_single
  have hget : ∀ x ∈ obs, ∀ w' n', t0.prog.base.getArr x w' n' = t.prog.base.getArr x w' n' := by
    intro x hx w' n'
    unfold JasminLsemMem.LstateM.getArr
    rw [harrO x hx]
  have harr' : t0.prog.base.getArr src 64 m = some (Ctxt.Var.lookup (d := jasminDialect)
      (Γ := [.stackArr 64 m]) (t := .stackArr 64 m) .here v) := by
    rw [← hsrc op hop, hget _ (hsO op hop)]; exact harr
  obtain ⟨a0, hD0⟩ : ∃ a0, t0.prog.base.getArr D 64 m = some a0 := by
    rw [hget D hDO]
    obtain ⟨j, a, hj, hk, rfl⟩ := hD
    rw [hfrm.2 (argName j) 64 m (fun i _ => (JasminLsemSimulation.regName_ne_argName i j).symm)
      (fun l _ => (JasminLsemExportTransfer.loopCtr_ne_argName l j).symm)]
    exact ⟨_, habi.arr j a m hj hk⟩
  obtain ⟨u, hsu, hatu, -⟩ := steps_resCopy
    (P := singletonProgM fn
      (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ resCopyCode src D m)) hm
    (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code) [] t0 (by simp [singletonProgM])
    hat harr' hD0 hfr
  have hF := fRun_of_stepsL (hs.trans hsu) (halted_of_atPc hatu (by
    simp [singletonProgM, resCopyCode, List.length_flatMap, resCopyStep]; omega))
  obtain ⟨f', u', hf⟩ := hF
  refine ⟨f, t, g, ht, hG, fRun_unique hrun ⟨(argBind σ nm).length + f', u', ?_⟩⟩
  rw [lsemFuelMemFLeak_segF _ fn rfl (argBind σ nm) (entryV σ fr sa un) false f' _ hlop
    (fun j hj => by
      show (argBind σ nm ++ X86Backend.ArrWebs.webRen w ao r.code ++ resCopyCode src D m)[0 + j]?
        = _
      rw [Nat.zero_add, List.append_assoc, List.getElem?_append_left hj]) hpre, hf,
    straightLeakFF_quiet (argBind σ nm) (movesOf_quiet _)]
  rfl

/-- **Constant time of the virtual body of a region export with a result copy.** Under the
    hypotheses of `regionVirt_memFCT` on a program with a result of `m < 2 ^ 64` words, with
    the result copy of `src` into `D` of `regionVirt_run_copy`, the copies of the parameter
    registers, the exported code and the result copy are constant time on the traced flag
    machine between the entry states of `RegionVirtPub`: both traces are the source events
    followed by `resCopyLeak src D m` (`regionVirt_leak_copy`). -/
theorem regionVirt_memFCT_copy (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String)
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r)
    (fr : AState → String → Option (BitVec 64)) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1)) :
    MemFCT (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m))
      (RegionVirtPub σ nm fn fuel p L Pre fr un) := by
  rintro s₁ s₂ ℓ₁ ℓ₂
    ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl, hden⟩ r₁ r₂
  obtain ⟨⟨v₁, t₁⟩, h₁⟩ := leakRun_eq_some_of_denote Pj fuel p V₁ hden
  have hnf := hct V₁ V₂ ⟨sa₁, R₁, P₁, hV₁⟩ ⟨sa₂, R₂, P₂, hV₂⟩ hpub
  rw [h₁] at hnf
  cases h₂ : NFProg.leakRun (jLeakModel Pj) fuel p V₂ with
  | none => rw [h₂] at hnf; cases hnf
  | some x₂ =>
      obtain ⟨v₂, t₂⟩ := x₂
      rw [h₂] at hnf
      obtain rfl : t₁ = t₂ := Option.some.inj hnf
      obtain ⟨-, -, μ, m₁, m₂⟩ :=
        machRun_of_leakRun Pj Γ.length fn fuel hp hc Γ.length 0 V₁ V₂ v₁ v₂ t₁ t₁ [] [] h₁ h₂
          rfl
      rw [regionVirt_leak_copy Pj σ nm fn hp hc hr E₁ un hU sa₁ V₁ hV₁ S₁ m₁ hsrc hD hm hfr r₁,
        regionVirt_leak_copy Pj σ nm fn hp hc hr E₂ un hU sa₂ V₂ hV₂ S₂ m₂ hsrc hD hm hfr r₂]

/-- **Constant time of the virtual body of an exported code with a result copy.** Under the
    hypotheses of `regionVirt_memFCT_copy`, at an exported code `r` of `RegionExp fn p ex r`
    that passes the event check `RegionWebsLeak`, with the target `D` of the copy among the
    names `ex`, the copies of the parameter registers, the code of `r` and the result copy
    are constant time on the traced flag machine between the entry states of
    `RegionVirtPub`. For the export it is `regionVirt_memFCT_copy`; for its webs both traces
    are the traces computed by `webG` along runs with the source events followed by
    `resCopyLeak src D m` (`regionVirt_leak_copy_webs`, `ImageLoopWLeak.gTr_eq`). -/
theorem regionVirt_memFCT_copy_of_regionExp (Pj : JLeakParams) (σ : AbiLayout)
    (nm : String → String) (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r) (hx : RegionWebsLeak fn p ex r)
    (fr : AState → String → Option (BitVec 64)) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j) (hDex : D ∈ ex)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1)) :
    MemFCT (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m))
      (RegionVirtPub σ nm fn fuel p L Pre fr un) := by
  obtain ⟨r0, hr0, rfl | ⟨w, Lw, hw, hwx, rfl⟩⟩ := regionExp_webs_cases hr hx
  · exact regionVirt_memFCT_copy Pj σ nm fn fuel hp hc hct hr0 fr un hU hsrc hD hm hfr
  have hsO : ∀ op, r0.res = [op] → operandName op ∈ regionWebsObs ex r0 := fun op h => by
    simp [regionWebsObs, h]
  have hDO : D ∈ regionWebsObs ex r0 := List.mem_append_right _ hDex
  rintro s₁ s₂ ℓ₁ ℓ₂
    ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl, hden⟩ r₁ r₂
  obtain ⟨⟨v₁, t₁⟩, h₁⟩ := leakRun_eq_some_of_denote Pj fuel p V₁ hden
  have hnf := hct V₁ V₂ ⟨sa₁, R₁, P₁, hV₁⟩ ⟨sa₂, R₂, P₂, hV₂⟩ hpub
  rw [h₁] at hnf
  cases h₂ : NFProg.leakRun (jLeakModel Pj) fuel p V₂ with
  | none => rw [h₂] at hnf; cases hnf
  | some x₂ =>
      obtain ⟨v₂, t₂⟩ := x₂
      rw [h₂] at hnf
      obtain rfl : t₁ = t₂ := Option.some.inj hnf
      obtain ⟨-, -, μ, m₁, m₂⟩ :=
        machRun_of_leakRun Pj Γ.length fn fuel hp hc Γ.length 0 V₁ V₂ v₁ v₂ t₁ t₁ [] [] h₁ h₂
          rfl
      obtain ⟨f₁, u₁, g₁, k₁, hG₁, rfl⟩ := regionVirt_leak_copy_webs Pj σ nm fn hp hc hr0 E₁ un
        hU sa₁ V₁ hV₁ S₁ m₁ hsrc hD hm hfr hw hwx hsO hDO r₁
      obtain ⟨f₂, u₂, g₂, k₂, hG₂, rfl⟩ := regionVirt_leak_copy_webs Pj σ nm fn hp hc hr0 E₂ un
        hU sa₂ V₂ hV₂ S₂ m₂ hsrc hD hm hfr hw hwx hsO hDO r₂
      rw [X86Backend.ImageLoopWLeak.gTr_eq _ fn _ f₁ _ u₁ _ k₁ f₂ _ u₂ k₂ rfl rfl
        ((entryV_abiEntry E₁.argF E₁.argG hU).pc.trans
          (entryV_abiEntry E₂.argF E₂.argG hU).pc.symm) _ _ hG₁ hG₂]

/-- **The entry states of `RegionVirtPub` have terminating runs with a result copy.** Under
    the hypotheses of `regionVirtPub_simPub` on a program with a result of `m < 2 ^ 64`
    words, with the result copy of `src` into `D` of `regionVirt_run_copy`, two states
    related by `RegionVirtPub` are states of `fn` at position `0` from each of which the
    copies of the parameter registers, the code of an exported code `r` of
    `RegionExp fn p ex r` and the result copy have a terminating traced run, when the
    target `D` of the copy is among the names `ex`. -/
theorem regionVirtPub_simPub_copy_of_regionExp (Pj : JLeakParams) (σ : AbiLayout)
    (nm : String → String) (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {ex : List String} {r : Exported}
    (hr : RegionExp fn p ex r)
    (fr : AState → String → Option (BitVec 64)) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j) (hDex : D ∈ ex)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1)) {s₁ s₂ : LstateMF}
    (h : RegionVirtPub σ nm fn fuel p L Pre fr un s₁ s₂) :
    SimPub (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m)) (EntryAt fn)
      (RegionVirtPub σ nm fn fuel p L Pre fr un) s₁ s₂ := by
  have hrun : ∀ (sa : AState) (V : Ctxt.Valuation Γ), AbiValOf σ sa V →
      EntryFacts σ nm (fr sa) → ArgSrc σ nm (fr sa) sa →
      (p.denoteAt CallEnv.empty fuel V).isSome = true →
      ∃ ℓ, FRun (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m))
        { prog := { base := entryV σ (fr sa) sa un, lfn := fn }, zf := false } ℓ := by
    intro sa V hV E hS hden
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hden
    obtain ⟨k, t, hk, -⟩ := regionVirt_run_copy_of_regionExp σ nm fn hp hr E un hU sa V hV hS
      fuel v hv hsrc hD hDex hm hfr
    have hfst := lsemFuelMemFLeak_fst
      (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m)) k
      { prog := { base := entryV σ (fr sa) sa un, lfn := fn }, zf := false }
    rw [hk] at hfst
    obtain ⟨q, hq, -⟩ := Option.map_eq_some_iff.mp hfst
    exact ⟨q.2, k, q.1, hq⟩
  obtain ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl, hden⟩ := h
  have hden₂ : (p.denoteAt CallEnv.empty fuel V₂).isSome = true := by
    obtain ⟨x, h₁⟩ := leakRun_eq_some_of_denote Pj fuel p V₁ hden
    have hnf := hct V₁ V₂ ⟨sa₁, R₁, P₁, hV₁⟩ ⟨sa₂, R₂, P₂, hV₂⟩ hpub
    rw [h₁] at hnf
    rw [← NFProg.leakRun_fst (jLeakModel Pj) fuel p V₂]
    cases h₂ : NFProg.leakRun (jLeakModel Pj) fuel p V₂ with
    | none => rw [h₂] at hnf; cases hnf
    | some y => rfl
  exact ⟨⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl, hden⟩,
    ⟨rfl, (entryV_abiEntry E₁.argF E₁.argG hU).pc⟩,
    ⟨rfl, (entryV_abiEntry E₂.argF E₂.argG hU).pc⟩,
    hrun sa₁ V₁ hV₁ E₁ S₁ hden, hrun sa₂ V₂ hV₂ E₂ S₂ hden₂⟩

/-- **The entry states of `RegionVirtPub` have terminating runs with a result copy** of the
    virtual body of the export `r` of `p`: `regionVirtPub_simPub_copy_of_regionExp` at `r`.
    -/
theorem regionVirtPub_simPub_copy (Pj : JLeakParams) (σ : AbiLayout) (nm : String → String)
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {m : Nat} {p : NFProg jasminDialect Γ [.stackArr 64 m]}
    (hp : RegionExportable p) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r)
    (fr : AState → String → Option (BitVec 64)) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) {src D : String}
    (hsrc : ∀ op, r.res = [op] → operandName op = src)
    (hD : ∃ j a, σ.args[j]? = some a ∧ a.kind = .words m ∧ D = argName j)
    (hm : m < 2 ^ 64) (hfr : ∀ i, i < m → src ≠ copyName D (i + 1)) {s₁ s₂ : LstateMF}
    (h : RegionVirtPub σ nm fn fuel p L Pre fr un s₁ s₂) :
    SimPub (singletonProgM fn (argBind σ nm ++ r.code ++ resCopyCode src D m)) (EntryAt fn)
      (RegionVirtPub σ nm fn fuel p L Pre fr un) s₁ s₂ :=
  regionVirtPub_simPub_copy_of_regionExp Pj σ nm fn fuel hp hct (regionExp_of_exportR [D] hr)
    fr un hU hsrc hD (List.mem_singleton_self D) hm hfr h

/-- **The entry state meets the array condition of the renaming by pairs.** For pairs `ps`
    with the facts of the renaming check on code `X`, the entry state `entryV` at the map
    `unren ps` of array names meets `RenStart` behind the copies of the parameter registers,
    at the names of `X`: the copies write no array, and the array of the target of a pair
    is at the entry the array of its source. -/
theorem renStart_entryV {σ : AbiLayout} {nm : String → String} (fn : String)
    {X : List LinstrRM} {ps : List (String × String)} (fr : String → Option (BitVec 64))
    (R : RenFacts σ nm [] X ps) (sa : AState) :
    JasminLsemExportRegAllocLeak.RenStart (argBind σ nm) ps (· ∈ loopNames X)
      { prog := { base := entryV σ fr sa (unren ps), lfn := fn }, zf := false } := by
  have hst : (argBind σ nm).all noStoreB = true := by
    have := R.store
    rwa [List.append_nil] at this
  intro b1 z1 hb1 r _
  rw [runStraightF_larr hst hb1]
  rcases renOf_cases ps r with he | ⟨p, hp, rfl, he⟩
  · rw [he]
  · rw [he]
    show (X86Backend.ExportCertEntry.abiEntryM σ sa).larr (unren ps p.2)
      = (X86Backend.ExportCertEntry.abiEntryM σ sa).larr (unren ps p.1)
    rw [unren_target R.nd hp, unren_of_not_target fun q hq => R.ts p hp q hq]

/-- The copy of a register onto itself emits no event. -/
theorem selfNop_quiet (z : String) (s : LstateMF) :
    instrLeakF (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) s = [] := by
  rw [instrLeakF_of_lopn ⟨_, _, _, rfl⟩]
  exact instrLeakB_quiet _ z _ [.reg z] _ fun o ho => by
    rw [List.mem_singleton.mp ho]
    rfl

/-- **One step of the traced flag machine on code without its array self-moves.** For a
    body `B` with the certificates `LiveCert` and `LeakCert` of the identity renaming from
    `k0` on, a halting traced run of `B` with fuel `n + 1` from a position `k ≥ k0` that
    holds an instruction and is not the store of a pair of `selfPairB` splits into events
    `e` and a halting run with fuel `m ≤ n` from a state `u`. From a state `s'` that agrees
    with the entry state on the register names of `Lr` at `k`, the arrays of `AN`, the word
    memory and the flags, a halting run of `selfNop k0 Lr B` with fuel `m` from a state
    `u'` in the same agreement with `u` extends to one with fuel `n + 1` from `s'` that
    emits `e'` first. At the load of a pair of `selfPairB`, `u` is two positions later, `e'`
    is empty and `e` has the number of events of the load and the store; at every other
    position `u` is the state after the step, and `e` and `e'` are the events of the
    instruction. -/
theorem selfNop_leak_step {fn : String} {B : List LinstrRM} {k0 : Nat}
    {Lr : Nat → List String} {AN : List String} {P₁ : LprogM}
    (hC : LiveCert id k0 (singletonProgM fn B) P₁ (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN))
    (hX : LeakCert id k0 (singletonProgM fn B) (fun k r => r ∈ Lr k))
    {n : Nat} {s s' t : LstateMF} {ℓ : List CTLeak} {i : LinstrRM}
    (hR : RelF2 id (· ∈ Lr s.prog.base.lpc) (· ∈ AN) s s') (hk : k0 ≤ s.prog.base.lpc)
    (hsec : (decide (0 < s.prog.base.lpc) && selfPairB k0 Lr B (s.prog.base.lpc - 1)) = false)
    (hfn : s.prog.lfn = fn) (hget : B[s.prog.base.lpc]? = some i)
    (hrun : lsemFuelMemFLeak (singletonProgM fn B) (n + 1) s = some (t, ℓ)) :
    ∃ (m : Nat) (u u' : LstateMF) (e e' r : List CTLeak),
      m ≤ n ∧ lsemFuelMemFLeak (singletonProgM fn B) m u = some (t, r) ∧ ℓ = e ++ r
      ∧ (∀ x, lsemFuelMemFLeak (singletonProgM fn (selfNop k0 Lr B)) m u' = some x →
          lsemFuelMemFLeak (singletonProgM fn (selfNop k0 Lr B)) (n + 1) s'
            = some (x.1, e' ++ x.2))
      ∧ RelF2 id (· ∈ Lr u.prog.base.lpc) (· ∈ AN) u u' ∧ k0 ≤ u.prog.base.lpc
      ∧ (decide (0 < u.prog.base.lpc) && selfPairB k0 Lr B (u.prog.base.lpc - 1)) = false
      ∧ u.prog.lfn = fn
      ∧ ((selfPairB k0 Lr B s.prog.base.lpc = true ∧ e' = []
            ∧ u.prog.base.lpc = s.prog.base.lpc + 2
            ∧ ∃ j, B[s.prog.base.lpc + 1]? = some j ∧ e.length = evCountF i + evCountF j)
        ∨ (selfPairB k0 Lr B s.prog.base.lpc = false ∧ e' = e ∧ e = instrLeakF i s
            ∧ evalInstrPMemF (singletonProgM fn B) i s = some u)) := by
  have hfi : ∀ (X : List LinstrRM) (x : LstatePM), findInstrMem (singletonProgM fn X) x
      = if x.lfn = fn then X[x.base.lpc]? else none := fun _ _ => rfl
  have hcg : ∀ (i : LinstrRM) (x : LstateMF),
      evalInstrPMemF P₁ i x = evalInstrPMemF (singletonProgM fn (selfNop k0 Lr B)) i x :=
    fun i x => evalInstrPMemF_congr (P := P₁) (P' := singletonProgM fn (selfNop k0 Lr B))
      hC.lfn (fun l => (hC.lbl l).trans (findLabelMem_selfNop k0 Lr B l).symm) i x
  have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
  have hlfn : s'.prog.lfn = s.prog.lfn := hR.2.1
  have hf : findInstrMem (singletonProgM fn B) s.prog = some i := by
    rw [hfi, ite_eq_left hfn]
    exact hget
  cases he : evalInstrPMemF (singletonProgM fn B) i s with
  | none => simp [lsemFuelMemFLeak, hf, he] at hrun
  | some u =>
  have hnx := evalInstrPMemF_next _ i s u he
  rw [lsemFuelMemFLeak_step _ n i s u hf he] at hrun
  obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
  by_cases hp : selfPairB k0 Lr B s.prog.base.lpc = true
  · obtain ⟨t0, a, z, sc, w, m, hi, hj, hzt, hdead⟩ := selfPairB_spec hp
    obtain rfl : i = _ := Option.some.inj (hget.symm.trans hi)
    have hupc : u.prog.base.lpc = s.prog.base.lpc + 1 := hnx.2
    have hf2 : findInstrMem (singletonProgM fn B) u.prog
        = some (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t0], .store w m) := by
      rw [hfi, ite_eq_left (hnx.1.trans hfn), hupc]
      exact hj
    cases n with
    | zero => simp [lsemFuelMemFLeak, hf2] at hq
    | succ m' =>
    cases he2 : evalInstrPMemF (singletonProgM fn B)
        (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t0], .store w m) u with
    | none => simp [lsemFuelMemFLeak, hf2, he2] at hq
    | some u2 =>
    rw [lsemFuelMemFLeak_step _ m' _ u u2 hf2 he2] at hq
    obtain ⟨q2, hq2, rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨hla, hlm, hlv, hpc2, hfn2, hzf2, hcf2, hof2⟩ :=
      selfMove_steps t0 a z sc w m hzt he he2
    obtain ⟨v1, hv1, v1lv, v1la, v1lm, v1pc, v1fn, v1zf, v1cf, v1of⟩ :=
      selfNop_step (singletonProgM fn (selfNop k0 Lr B)) z s'
    obtain ⟨v2, hv2, v2lv, v2la, v2lm, v2pc, v2fn, v2zf, v2cf, v2of⟩ :=
      selfNop_step (singletonProgM fn (selfNop k0 Lr B)) z v1
    have hg1 : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog
        = some (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) := by
      rw [hfi, ite_eq_left (hlfn.trans hfn), hpc, selfNop, List.getElem?_mapIdx, hi]
      simp [hp, selfNopI]
    have hg2 : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) v1.prog
        = some (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) := by
      rw [hfi, ite_eq_left (v1fn.trans (hlfn.trans hfn)), v1pc, hpc, selfNop,
        List.getElem?_mapIdx, hj]
      simp [hp, selfNopI]
    have hR2 : RelF2 id (· ∈ Lr u2.prog.base.lpc) (· ∈ AN) u2 v2 := by
      refine ⟨⟨⟨?_, fun r hr => ?_⟩, fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · show v2.prog.base.lpc = u2.prog.base.lpc
        rw [v2pc, v1pc, hpc, hpc2]
      · rw [hpc2] at hr
        obtain ⟨hne, hin⟩ := hdead r hr
        rw [hlv r hne, v2lv, v1lv]
        exact hR.1.1.2 r hin
      · rw [hla, v2la, v1la]
        exact hR.1.2.1 r hr
      · rw [hlm, v2lm, v1lm]
        exact hR.1.2.2
      · rw [hfn2, v2fn, v1fn]
        exact hlfn
      · rw [hzf2, v2zf, v1zf]
        exact hR.2.2.1
      · rw [hcf2, v2cf, v1cf]
        exact hR.2.2.2.1
      · rw [hof2, v2of, v1of]
        exact hR.2.2.2.2
    have hsec2 : (decide (0 < u2.prog.base.lpc)
        && selfPairB k0 Lr B (u2.prog.base.lpc - 1)) = false := by
      rw [hpc2, show s.prog.base.lpc + 2 - 1 = s.prog.base.lpc + 1 from rfl,
        Bool.and_eq_false_iff]
      right
      by_contra hc
      obtain ⟨t1, a1, z1, sc1, w1, m1, hi1, -⟩ :=
        selfPairB_spec (Bool.eq_true_of_not_eq_false hc)
      rw [hj] at hi1
      cases congrArg Prod.snd (Option.some.inj hi1)
    refine ⟨m', u2, v2, _ ++ _, [], q2.2, Nat.le_succ _, hq2, (List.append_assoc _ _ _).symm,
      fun x hx => ?_, hR2, by omega, hsec2, hfn2.trans hfn,
      Or.inl ⟨hp, rfl, hpc2, _, hj, by
        rw [List.length_append, instrLeakF_length, instrLeakF_length]⟩⟩
    rw [lsemFuelMemFLeak_step _ (m' + 1) _ s' v1 hg1 hv1,
      lsemFuelMemFLeak_step _ m' _ v1 v2 hg2 hv2, hx, selfNop_quiet, selfNop_quiet]
    rfl
  · have hp' : selfPairB k0 Lr B s.prog.base.lpc = false := Bool.eq_false_of_not_eq_true hp
    obtain ⟨u', hu', hRu, hku⟩ := evalInstrPMemF_live hC i hk hget hR he
    rw [renRM_id, hcg] at hu'
    have hg : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog = some i := by
      rw [hfi, ite_eq_left (hlfn.trans hfn), hpc, selfNop, List.getElem?_mapIdx, hget]
      simp [hp', hsec]
    have hev : instrLeakF i s' = instrLeakF i s := by
      have h := instrLeakF_live (σ := id) i (hC.cond _ i hk hget) (hX.idx _ i hk hget)
        (hX.fix _ i hk hget) hR
      rw [renRM_id] at h
      rw [h]
      exact (List.map_congr_left fun e _ => by cases e <;> rfl).trans (List.map_id _)
    refine ⟨n, u, u', instrLeakF i s, instrLeakF i s, q.2, Nat.le_refl _, hq, rfl,
      fun x hx => ?_, hRu, hku, selfPairB_next hnx.2 hp', hnx.1.trans hfn,
      Or.inr ⟨hp', rfl, rfl, rfl⟩⟩
    rw [lsemFuelMemFLeak_step _ n i s' u' hg hu', hx, hev]
    rfl

/-- **The traced flag machine on code without its array self-moves.** For a body `B` with
    the certificates `LiveCert` and `LeakCert` of the identity renaming from `k0` on, at the
    register names `Lr` and the array names `AN`: two halting traced runs of `B` with one
    trace, from one position `k ≥ k0` of one function that is not the store of a pair of
    `selfPairB`, are matched, with the same fuels, by halting traced runs of
    `selfNop k0 Lr B` with one trace, from states that agree with the two entry states on
    the register names of `Lr` at `k`, the arrays of `AN`, the word memory and the flags.
    The two runs of `B` take the same path: equal events at a conditional are equal
    decisions (`ImageLoopWLeak.evalInstrPMemF_pc_det`), and the number of events of an
    instruction does not depend on the state. -/
theorem lsemFuelMemFLeak_selfNop {fn : String} {B : List LinstrRM} {k0 : Nat}
    {Lr : Nat → List String} {AN : List String} {P₁ : LprogM}
    (hC : LiveCert id k0 (singletonProgM fn B) P₁ (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN))
    (hX : LeakCert id k0 (singletonProgM fn B) (fun k r => r ∈ Lr k)) :
    ∀ (f₁ f₂ : Nat) {s₁ s₂ s₁' s₂' t₁ t₂ : LstateMF} {ℓ : List CTLeak},
      s₁.prog.base.lpc = s₂.prog.base.lpc → s₁.prog.lfn = s₂.prog.lfn →
      RelF2 id (· ∈ Lr s₁.prog.base.lpc) (· ∈ AN) s₁ s₁' →
      RelF2 id (· ∈ Lr s₂.prog.base.lpc) (· ∈ AN) s₂ s₂' → k0 ≤ s₁.prog.base.lpc →
      (decide (0 < s₁.prog.base.lpc) && selfPairB k0 Lr B (s₁.prog.base.lpc - 1)) = false →
      lsemFuelMemFLeak (singletonProgM fn B) f₁ s₁ = some (t₁, ℓ) →
      lsemFuelMemFLeak (singletonProgM fn B) f₂ s₂ = some (t₂, ℓ) →
      ∃ t₁' t₂' ℓ',
        lsemFuelMemFLeak (singletonProgM fn (selfNop k0 Lr B)) f₁ s₁' = some (t₁', ℓ')
        ∧ lsemFuelMemFLeak (singletonProgM fn (selfNop k0 Lr B)) f₂ s₂' = some (t₂', ℓ') := by
  have hfi : ∀ (X : List LinstrRM) (x : LstatePM), findInstrMem (singletonProgM fn X) x
      = if x.lfn = fn then X[x.base.lpc]? else none := fun _ _ => rfl
  have hhalt : ∀ {s s' : LstateMF}, RelF2 id (· ∈ Lr s.prog.base.lpc) (· ∈ AN) s s' →
      findInstrMem (singletonProgM fn B) s.prog = none →
      findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog = none := by
    intro s s' hR hf
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
    rw [hfi] at hf ⊢
    rw [hR.2.1, hpc]
    split at hf
    · next hfn =>
      rw [ite_eq_left hfn, selfNop, List.getElem?_mapIdx, hf]
      rfl
    · next hfn => rw [ite_eq_right hfn]
  intro f₁
  induction f₁ using Nat.strong_induction_on with
  | _ f₁ ih =>
  intro f₂ s₁ s₂ s₁' s₂' t₁ t₂ ℓ hpc hlfn hR₁ hR₂ hk hsec h₁ h₂
  have hfe : findInstrMem (singletonProgM fn B) s₂.prog
      = findInstrMem (singletonProgM fn B) s₁.prog := by
    rw [hfi, hfi, hlfn, hpc]
  cases hf : findInstrMem (singletonProgM fn B) s₁.prog with
  | none =>
      exact ⟨s₁', s₂', [], lsemFuelMemFLeak_halt _ _ _ (hhalt hR₁ hf),
        lsemFuelMemFLeak_halt _ _ _ (hhalt hR₂ (hfe.trans hf))⟩
  | some i =>
      have hfn : s₁.prog.lfn = fn := by
        rw [hfi] at hf
        by_contra hc
        rw [ite_eq_right hc] at hf
        cases hf
      have hget : B[s₁.prog.base.lpc]? = some i := by
        rw [hfi, ite_eq_left hfn] at hf
        exact hf
      cases f₁ with
      | zero => simp [lsemFuelMemFLeak, hf] at h₁
      | succ n₁ =>
      cases f₂ with
      | zero => simp [lsemFuelMemFLeak, hfe.trans hf] at h₂
      | succ n₂ =>
      obtain ⟨m₁, u₁, u₁', e₁, e₁', r₁, hm₁, hq₁, hℓ₁, hP₁, hRu₁, hku₁, hsec₁, hfn₁, hcase₁⟩ :=
        selfNop_leak_step hC hX hR₁ hk hsec hfn hget h₁
      obtain ⟨m₂, u₂, u₂', e₂, e₂', r₂, -, hq₂, hℓ₂, hP₂, hRu₂, -, -, hfn₂, hcase₂⟩ :=
        selfNop_leak_step hC hX hR₂ (by rw [← hpc]; exact hk) (by rw [← hpc]; exact hsec)
          (hlfn.symm.trans hfn) (by rw [← hpc]; exact hget) h₂
      have key : e₁ = e₂ ∧ r₁ = r₂ ∧ e₁' = e₂'
          ∧ u₁.prog.base.lpc = u₂.prog.base.lpc := by
        rcases hcase₁ with ⟨hp1, he1, hu1, j1, hj1, hl1⟩ | ⟨hp1, he1, hi1, hs1⟩
        · rcases hcase₂ with ⟨hp2, he2, hu2, j2, hj2, hl2⟩ | ⟨hp2, -, -, -⟩
          · rw [← hpc, hj1] at hj2
            obtain rfl := Option.some.inj hj2
            obtain ⟨h1, h2⟩ := List.append_inj (hℓ₁.symm.trans hℓ₂) (hl1.trans hl2.symm)
            exact ⟨h1, h2, he1.trans he2.symm, by rw [hu1, hu2, hpc]⟩
          · rw [← hpc, hp1] at hp2
            cases hp2
        · rcases hcase₂ with ⟨hp2, -, -, -⟩ | ⟨hp2, he2, hi2, hs2⟩
          · rw [← hpc, hp1] at hp2
            cases hp2
          · obtain ⟨h1, h2⟩ := List.append_inj (hℓ₁.symm.trans hℓ₂)
              (by rw [hi1, hi2, instrLeakF_length, instrLeakF_length])
            refine ⟨h1, h2, by rw [he1, he2, h1], ?_⟩
            exact X86Backend.ImageLoopWLeak.evalInstrPMemF_pc_det _ i hpc hs1 hs2
              (by rw [← hi1, ← hi2, h1])
      obtain ⟨rfl, rfl, rfl, hupc⟩ := key
      obtain ⟨t₁', t₂', ℓ', ha, hb⟩ := ih m₁ (by omega) m₂ hupc (hfn₁.trans hfn₂.symm) hRu₁
        hRu₂ hku₁ hsec₁ hq₁ hq₂
      exact ⟨t₁', t₂', e₁' ++ ℓ', hP₁ _ ha, hP₂ _ hb⟩

/-- **Constant time of code without its array self-moves.** For a prefix `pre` of operations
    that emit no event and code `C` accepted by `regCoB id pre C L AN`, with the certificate
    `LeakCert` of the identity renaming at the table `liveAt L` behind the prefix, constant
    time of `pre ++ C` at `pubEq` gives constant time of `selfNop` of `pre ++ C` at the
    table `liveAt L`, between `pubEq`-related states of the function `fn` at position `0`
    from each of which `pre ++ C` has a terminating run. -/
theorem selfNop_memFCT {pre C : List LinstrRM} {L : Nat → List String} {AN : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    {fn : String} (hpre : ∀ i ∈ pre, IsLopn i) (hq : ∀ i ∈ pre, ∀ r, instrLeakB r i = [])
    (h : regCoB id pre C L AN aa ao = true)
    (hX : LeakCert id pre.length (singletonProgM fn (pre ++ C))
      (fun k r => r ∈ liveAt L (pre ++ C).length k))
    {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (pre ++ C)) pubEq) :
    MemFCT (singletonProgM fn (selfNop pre.length (liveAt L (pre ++ C).length) (pre ++ C)))
      (SimPub (singletonProgM fn (pre ++ C)) (EntryAt fn) pubEq) := by
  have hC := liveCert_of_regCoB fn hpre h
  have hlow : ∀ j, j < pre.length →
      selfPairB pre.length (liveAt L (pre ++ C).length) (pre ++ C) j = false := fun j hj => by
    simp [selfPairB, Nat.not_le.mpr hj]
  have hposN : ∀ (b0 : LstateM), b0.lpc = 0 → ∀ j, j < pre.length →
      (singletonProgM fn (selfNop pre.length (liveAt L (pre ++ C).length)
        (pre ++ C))).body[b0.lpc + j]? = pre[j]? := fun b0 hb0 j hj => by
    show (selfNop pre.length (liveAt L (pre ++ C).length) (pre ++ C))[b0.lpc + j]? = _
    rw [hb0, Nat.zero_add, selfNop, List.getElem?_mapIdx, List.getElem?_append_left hj,
      hlow j hj]
    have h1 : (decide (0 < j) && selfPairB pre.length (liveAt L (pre ++ C).length)
        (pre ++ C) (j - 1)) = false := by
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rfl
      · rw [hlow (j - 1) (by omega), Bool.and_false]
    rw [h1]
    cases pre[j]? <;> rfl
  have hsec : (decide (0 < pre.length) && selfPairB pre.length
      (liveAt L (pre ++ C).length) (pre ++ C) (pre.length - 1)) = false := by
    rcases Nat.eq_zero_or_pos pre.length with h0 | h0
    · rw [h0]; rfl
    · rw [hlow (pre.length - 1) (by omega), Bool.and_false]
  have hjoin : ∀ (b : LstateM) (zf : Bool) (c : LstateM) (z : Bool) (g : Nat) (t' : LstateMF)
      (ℓ' : List CTLeak), b.lpc = 0 → runStraightF pre b zf = some (c, z) →
      lsemFuelMemFLeak (singletonProgM fn (selfNop pre.length (liveAt L (pre ++ C).length)
        (pre ++ C))) g { prog := { base := c, lfn := fn }, zf := z } = some (t', ℓ') →
      FRun (singletonProgM fn (selfNop pre.length (liveAt L (pre ++ C).length) (pre ++ C)))
        { prog := { base := b, lfn := fn }, zf := zf } ℓ' := by
    intro b zf c z g t' ℓ' hb hrs hg
    refine ⟨pre.length + g, t', ?_⟩
    rw [lsemFuelMemFLeak_segF _ fn rfl pre b zf g (c, z) hpre (hposN b hb) hrs, hg,
      straightLeakFF_quiet pre hq]
    rfl
  rintro ⟨⟨b₁, lfn₁⟩, zf₁⟩ ⟨⟨b₂, lfn₂⟩, zf₂⟩ ℓ₁' ℓ₂'
    ⟨hp, ⟨rfl, h0₁⟩, ⟨rfl, h0₂⟩, ⟨v₁, f₁, t₁, r₁⟩, ⟨v₂, f₂, t₂, r₂⟩⟩ hr₁ hr₂
  obtain rfl := hct _ _ v₁ v₂ hp ⟨f₁, t₁, r₁⟩ ⟨f₂, t₂, r₂⟩
  obtain ⟨g₁, c₁, z₁, T₁, hs₁, hpc₁, hT₁, hq₁⟩ :=
    lsemFuelMemFLeak_prefix_split _ pre C hpre b₁ zf₁ h0₁ f₁ t₁ _ r₁
  obtain ⟨g₂, c₂, z₂, T₂, hs₂, hpc₂, hT₂, hq₂⟩ :=
    lsemFuelMemFLeak_prefix_split _ pre C hpre b₂ zf₂ h0₂ f₂ t₂ _ r₂
  rw [straightLeakFF_quiet pre hq, List.nil_append] at hT₁ hT₂
  subst hT₁
  subst hT₂
  obtain ⟨t₁', t₂', ℓ', ha, hb⟩ := lsemFuelMemFLeak_selfNop hC hX g₁ g₂
    (s₁ := { prog := { base := c₁, lfn := _ }, zf := z₁ })
    (s₂ := { prog := { base := c₂, lfn := _ }, zf := z₂ })
    (s₁' := { prog := { base := c₁, lfn := _ }, zf := z₁ })
    (s₂' := { prog := { base := c₂, lfn := _ }, zf := z₂ })
    (hpc₁.trans hpc₂.symm) rfl
    ⟨⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
    ⟨⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
    (Nat.le_of_eq hpc₁.symm)
    (by
      show (decide (0 < c₁.lpc) && selfPairB pre.length (liveAt L (pre ++ C).length)
        (pre ++ C) (c₁.lpc - 1)) = false
      rw [hpc₁]
      exact hsec) hq₁ hq₂
  rw [fRun_unique hr₁ (hjoin b₁ zf₁ c₁ z₁ g₁ t₁' ℓ' h0₁ hs₁ ha),
    fRun_unique hr₂ (hjoin b₂ zf₂ c₂ z₂ g₂ t₂' ℓ' h0₂ hs₂ hb)]

/-! ## 9. Constant time of the reference of the gate -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAllocLeak (fRun_coalesce_prefix
  memFCT_coalesce_prefix fRun_renameLoop memFCT_renameLoop fRun_live_prefix memFCT_live_prefix
  memFCT_of_fRun_map leakLiveB leakCert_of_leakLiveB RenStart)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak (leakFixCfgB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (NoCArr
  fuseMulHi_lsemFuelMemFLeak_pre)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (E64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML
  memFCT_of_ownedCheckML TVPub)

/-- Constant time at a relation is constant time at every relation it contains. -/
theorem memFCT_mono {P : LprogM} {r r' : LstateMF → LstateMF → Prop}
    (h : ∀ s₁ s₂, r s₁ s₂ → r' s₁ s₂) (hct : MemFCT P r') : MemFCT P r :=
  fun s₁ s₂ ℓ₁ ℓ₂ hp => hct s₁ s₂ ℓ₁ ℓ₂ (h s₁ s₂ hp)

/-- The program `P` has a terminating traced run from each of two states related by `r`. -/
def HasRuns (P : LprogM) (r : LstateMF → LstateMF → Prop) : Prop :=
  ∀ s₁ s₂, r s₁ s₂ → (∃ ℓ, FRun P s₁ ℓ) ∧ ∃ ℓ, FRun P s₂ ℓ

/-- **One step of a chain of programs at one entry relation.** Let the states related by `r`
    lie in `G`, let every state of `G` with a terminating run of `P` have a terminating run
    of `P'`, and let constant time of `P` at `r` give constant time of `P'` at
    `SimPub P G r`. Constant time of `P` at `r` with terminating runs from the states `r`
    relates gives the same for `P'`, at the relation `r`. -/
theorem memFCT_step {P P' : LprogM} {G : LstateMF → Prop} {r : LstateMF → LstateMF → Prop}
    (hG : ∀ s₁ s₂, r s₁ s₂ → G s₁ ∧ G s₂)
    (hsim : ∀ s, G s → (∃ ℓ, FRun P s ℓ) → ∃ ℓ, FRun P' s ℓ)
    (hstep : MemFCT P r → MemFCT P' (SimPub P G r))
    (h : MemFCT P r ∧ HasRuns P r) : MemFCT P' r ∧ HasRuns P' r :=
  ⟨memFCT_mono (fun s₁ s₂ hp => ⟨hp, (hG s₁ s₂ hp).1, (hG s₁ s₂ hp).2, (h.2 s₁ s₂ hp).1,
      (h.2 s₁ s₂ hp).2⟩) (hstep h.1),
    fun s₁ s₂ hp => ⟨hsim s₁ (hG s₁ s₂ hp).1 (h.2 s₁ s₂ hp).1,
      hsim s₂ (hG s₁ s₂ hp).2 (h.2 s₁ s₂ hp).2⟩⟩

/-- A halting run of the flag machine has a terminating traced run. -/
theorem fRun_of_lsemFuelMemF {P : LprogM} {k : Nat} {s t : LstateMF}
    (h : lsemFuelMemF P k s = some t) : ∃ ℓ, FRun P s ℓ := by
  have hfst := lsemFuelMemFLeak_fst P k s
  rw [h] at hfst
  obtain ⟨q, hq, -⟩ := Option.map_eq_some_iff.mp hfst
  exact ⟨q.2, k, q.1, hq⟩

/-- A terminating traced run is a halting run of the flag machine. -/
theorem lsemFuelMemF_of_fRun {P : LprogM} {s : LstateMF} {ℓ : List CTLeak}
    (h : FRun P s ℓ) : ∃ k t, lsemFuelMemF P k s = some t := by
  obtain ⟨k, t, h⟩ := h
  refine ⟨k, t, ?_⟩
  rw [← lsemFuelMemFLeak_fst, h]
  rfl

/-- The instruction has no compile-time array operand, as a Boolean. -/
def constArrFreeB (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn ds _ ss => (ds ++ ss).all fun o =>
      match o with
      | .arr _ _ => false
      | _ => true
  | _ => true

theorem noCArr_of_constArrFreeB {i : LinstrRM} (h : constArrFreeB i = true) : NoCArr i.1 := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o ss =>
      intro x hx b k he
      have := List.all_eq_true.mp h x hx
      rw [he] at this
      cases this
  | _ => trivial

/-- **The check of the events of code behind a prefix** for a merge `τ` of register names,
    against a liveness certificate `L`: the instruction at every position of `C` passes
    `leakLiveB` at the register names `liveAt L` of its position in `pre ++ C`. -/
def regLeakB (τ : String → String) (pre C : List LinstrRM) (L : Nat → List String) : Bool :=
  (List.range C.length).all fun j =>
    match C[j]? with
    | some i => leakLiveB τ (liveAt L (pre ++ C).length (pre.length + j)) i
    | none => true

/-- Code accepted by `regLeakB` has the certificate `LeakCert` from its first position, at
    the register names `liveAt L`. -/
theorem leakCert_of_regLeakB {τ : String → String} {pre C : List LinstrRM}
    {L : Nat → List String} (fn : String) (h : regLeakB τ pre C L = true) :
    LeakCert τ pre.length (singletonProgM fn (pre ++ C))
      (fun k r => r ∈ liveAt L (pre ++ C).length k) :=
  leakCert_of_leakLiveB fun k i hk hi => by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hi' : (pre ++ C)[pre.length + j]? = some i := hi
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hi'
    have hj : j < C.length := (List.getElem?_eq_some_iff.mp hi').1
    have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    rw [hi'] at this
    exact this

/-- **The slot map of the image of a region export** at the parts `d`: the slot map of the
    layout with its array names renamed by the pairs `d.ps` and the cell arrays `d.cells` at
    length `0` (`slotArrC`). The image check `renImageB` of the gate `regionCoB` reads the
    printed body at this slot map. -/
abbrev regionSl (σ : AbiLayout) (nm : String → String) (d : CoParts) :
    String → Option (String × Nat) :=
  slotArrC d.cells (slotRen (slotArrOf σ nm) (renOf d.ps))

/-- **The check of the events of the reference of a region export** with the code `code` and
    the returned operands `res`, at the result type `t`, against the printed body `body`.
    With `C := regionCoCode` and the parts `d := regionCoParts`: the alias map
    `regionAliasN σ nm t res C` fixes the array bases of the events of `C` (`leakFixCfgB`); the coalesced code has no
    compile-time array operand; when there is a merge pair, the renamed code passes
    `regLeakB` of the merge at the table `d.live`; the merged code passes `regLeakB` of the
    identity at the table `d.liveM`; and the check on traced runs `ownedCheckML`, observing
    the targets of the result copy, accepts the reference `d.ref` against the image of the
    cell body `ImageAddrCells.cellBody` of `body` at the slot map `regionSl σ nm d`, the
    image that the gate `regionCoB` compares with `d.ref`. -/
def regionLeakB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String)) : Bool :=
  let C := regionCoCodeN σ nm t code res
  let d := regionCoParts σ nm body t code res cert
  let sl := regionSl σ nm d
  leakFixCfgB (regionAliasN σ nm t res C) C
    && (regionCoBody σ nm t code res).all constArrFreeB
    && (d.tau == [] || regLeakB (renOf d.tau) d.pre d.ren (tabAt d.live))
    && regLeakB id d.pre d.merged (tabAt d.liveM)
    && ownedCheckML d.outs d.ref (virtImg sl (cellBody sl body))

/-- An entry state `entryV` of the function `fn`, at the frame map `fr sa` of a machine
    state `sa` and the map `un` of array names, whose frame map satisfies the facts of the
    entry check and gives the sources of the parameters. -/
def RegionVirtEntry (σ : AbiLayout) (nm : String → String) (fn : String)
    (fr : AState → String → Option (BitVec 64)) (un : String → String) (s : LstateMF) : Prop :=
  ∃ sa, EntryFacts σ nm (fr sa) ∧ ArgSrc σ nm (fr sa) sa
    ∧ s = { prog := { base := entryV σ (fr sa) sa un, lfn := fn }, zf := false }

/-- The states `RegionVirtPub` relates are entry states of `RegionVirtEntry`. -/
theorem regionVirtPub_entry {σ : AbiLayout} {nm : String → String} {fn : String} {fuel : Nat}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {L : Labels Γ} {Pre : AState → Prop} {fr : AState → String → Option (BitVec 64)}
    {un : String → String}
    {s₁ s₂ : LstateMF} (h : RegionVirtPub σ nm fn fuel p L Pre fr un s₁ s₂) :
    RegionVirtEntry σ nm fn fr un s₁ ∧ RegionVirtEntry σ nm fn fr un s₂ := by
  obtain ⟨sa₁, sa₂, -, -, -, -, -, E₁, E₂, S₁, S₂, -, -, -, -, h₁, h₂, -⟩ := h
  exact ⟨⟨sa₁, E₁, S₁, h₁⟩, ⟨sa₂, E₂, S₂, h₂⟩⟩

/-- **Constant time of the fused code of the gate.** Let `p` be a program of
    `RegionExportable` without a `call`, with the export `r`, that is constant time at the
    source events for the entry labels `L` at `fuel` on the valuations the layout `σ` reads
    off machine states that satisfy `σ.Regions` and the precondition `Pre`, and let its code
    and returned operands
    pass the gate `regionCoB` and the check of the events `regionLeakB` against the printed
    body `body`. The code `d.fused` of the parts `d := regionCoParts` is constant time on
    the traced flag machine between the entry states of `RegionVirtPub` at the frame of
    `body` and the map `unren d.ps` of array names, and it has a terminating traced run from
    each of them. The steps are those of the gate: the coalescing
    (`memFCT_coalesce_prefix`), the pairs (`memFCT_renameLoop`), the register merge
    (`memFCT_live_prefix`), the array self-moves (`selfNop_memFCT`) and the multiplication
    fusion (`fuseMulHi_lsemFuelMemFLeak_pre`). The code `r` is an exported code of
    `RegionExp fn p (regionWebsEx σ nm) r` that passes the event check `RegionWebsLeak`. -/
theorem regionFused_memFCT_of_regionExp (Pj : JLeakParams) {σ : AbiLayout}
    {nm : String → String} (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported} (hr : RegionExp fn p (regionWebsEx σ nm) r)
    (hx : RegionWebsLeak fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true) :
    MemFCT (singletonProgM fn (regionCoParts σ nm body t r.code r.res cert).fused)
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body)
          (unren (regionCoParts σ nm body t r.code r.res cert).ps))
      ∧ HasRuns (singletonProgM fn (regionCoParts σ nm body t r.code r.res cert).fused)
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body)
          (unren (regionCoParts σ nm body t r.code r.res cert).ps)) := by
  rw [regionCoB_none] at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨⟨hcl, hco⟩, hfix⟩, ⟨⟨⟨⟨⟨⟨⟨⟨hren, -⟩, -⟩, -⟩, hmg⟩, hnop⟩, hsite⟩, -⟩, -⟩⟩ := hg
  simp only [regionLeakB, Bool.and_eq_true] at hlk
  obtain ⟨⟨⟨⟨hlfix, hna⟩, hl1⟩, hl2⟩, -⟩ := hlk
  generalize hd : regionCoParts σ nm body t r.code r.res cert = d
    at hren hmg hnop hsite hl1 hl2 ⊢
  have hnopE : d.nop = selfNop d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) := by
    rw [← hd]; rfl
  have href : d.fused
      = if d.sites then d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length) else d.nop := by
    rw [← hd]; rfl
  have hpre : d.pre = argBind σ nm ++ movesOf d.ps := by rw [← hd]; rfl
  have hren' : d.ren = (regionCoBody σ nm t r.code r.res).map (renRM (renOf d.ps)) := by
    rw [← hd]; rfl
  have hmerged : d.merged = d.ren.map (renRM (renOf d.tau)) := by rw [← hd]; rfl
  have RF := renB_spec hren
  have hU : ∀ j, j < σ.args.length → unren d.ps (argName j) = argName j :=
    fun j hj => (RF.unr j hj).1
  have hlopA : ∀ i ∈ argBind σ nm, IsLopn i := movesOf_isLopn _
  have hqA : ∀ i ∈ argBind σ nm, ∀ x, instrLeakB x i = [] := movesOf_quiet _
  have hlop : ∀ i ∈ d.pre, IsLopn i := fun i hi => by
    rw [hpre] at hi
    exact (List.mem_append.mp hi).elim (movesOf_isLopn _ i) (movesOf_isLopn _ i)
  have hq : ∀ i ∈ d.pre, ∀ x, instrLeakB x i = [] := fun i hi => by
    rw [hpre] at hi
    exact (List.mem_append.mp hi).elim (movesOf_quiet _ i) (movesOf_quiet _ i)
  have hE : ∀ s, RegionVirtEntry σ nm fn (frameE body) (unren d.ps) s →
      (EntryAt fn s ∧ RenStart (argBind σ nm) d.ps
          (· ∈ loopNames (regionCoBody σ nm t r.code r.res)) s)
        ∧ E64 (fuseRegs σ nm) s.prog.base := by
    rintro _ ⟨sa, E, hS, rfl⟩
    have habi := entryV_abiEntry (sa := sa) (un := unren d.ps) E.argF E.argG hU
    refine ⟨⟨⟨rfl, habi.pc⟩, renStart_entryV fn (frameE body sa) RF sa⟩, fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact e64_of_abiEntryM habi x hx
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact congrArg (·.1) (entryV_srcOf (un := unren d.ps) hS ha)
  have hG : ∀ s₁ s₂, RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps) s₁ s₂ →
      EntryAt fn s₁ ∧ EntryAt fn s₂ := fun s₁ s₂ h =>
    ⟨(hE _ (regionVirtPub_entry h).1).1.1, (hE _ (regionVirtPub_entry h).2).1.1⟩
  have h0 : MemFCT (singletonProgM fn (argBind σ nm ++ regionCoCodeN σ nm t r.code r.res))
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps))
      ∧ HasRuns (singletonProgM fn (argBind σ nm ++ regionCoCodeN σ nm t r.code r.res))
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps)) := by
    cases hcp : regionCopy σ nm t none r.code r.res with
    | none =>
        have e0 : argBind σ nm ++ regionCoCodeN σ nm t r.code r.res
            = argBind σ nm ++ r.code ++ movesOf (regionRet σ nm t r.res).toList := by
          simp only [regionCoCodeN, hcp, regionCoCode, List.append_assoc]
        rw [e0]
        exact ⟨regionVirt_memFCT_of_regionExp Pj σ nm fn fuel hp hc hct hr hx _ _ _ hU,
          fun s₁ s₂ h =>
            (regionVirtPub_simPub_of_regionExp Pj σ nm fn fuel hp hct hr _ _ _ hU h).2.2.2⟩
    | some c =>
        obtain ⟨src, D, m⟩ := c
        obtain ⟨-, ht, ⟨op, hop, hsrc⟩, hD, hm, hfr⟩ := regionCopy_some hcp
        subst ht
        have e0 : argBind σ nm ++ regionCoCodeN σ nm (.stackArr 64 m) r.code r.res
            = argBind σ nm ++ r.code ++ resCopyCode src D m := by
          simp only [regionCoCodeN, hcp, regionCoCode, regionRet, Option.toList, movesOf,
            List.map_nil, List.append_nil, List.append_assoc]
        have hsrc' : ∀ op', r.res = [op'] → operandName op' = src := fun op' h => by
          rw [hop] at h; obtain rfl := (List.cons.inj h).1; exact hsrc
        rw [e0]
        have hDex := regionCopy_mem_regionWebsEx hcp
        exact ⟨regionVirt_memFCT_copy_of_regionExp Pj σ nm fn fuel hp hc hct hr hx _ _ hU hsrc'
            hD hDex hm hfr,
          fun s₁ s₂ h => (regionVirtPub_simPub_copy_of_regionExp Pj σ nm fn fuel hp hct hr _ _
            hU hsrc' hD hDex hm hfr h).2.2.2⟩
  have hcls : ∀ i ∈ regionCoCodeN σ nm t r.code r.res, CtlOK i := fun i hi =>
    (clsB_ctl_cond (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcl i hi)).1
      (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcl i hi)).2).1
  have hfix' : ∀ x ∈ tabAt (liveArrTab (regionCoCodeN σ nm t r.code r.res)
      (regionCoObs t (regionOutN σ nm t r.code r.res))) 0,
      regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res) x = x :=
    fun x hx => by simpa using List.all_eq_true.mp hfix x hx
  have h1 : MemFCT (singletonProgM fn (argBind σ nm ++ regionCoBody σ nm t r.code r.res))
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps))
      ∧ HasRuns (singletonProgM fn (argBind σ nm ++ regionCoBody σ nm t r.code r.res))
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps)) :=
    memFCT_step (G := EntryAt fn) hG
      (fun s hs hrun => by
        obtain ⟨⟨b0, lfn⟩, zf⟩ := s
        obtain ⟨rfl, h0'⟩ := hs
        obtain ⟨ℓ, hℓ⟩ := hrun
        obtain ⟨T, -, hT⟩ := fRun_coalesce_prefix hlopA hcls hco hlfix hfix' b0 zf h0' hℓ
        exact ⟨_, hT⟩)
      (memFCT_coalesce_prefix hlopA hqA hcls hco hlfix hfix') h0
  have hNA : ∀ i ∈ regionCoBody σ nm t r.code r.res, NoCArr i.1 := fun i hi =>
    noCArr_of_constArrFreeB (List.all_eq_true.mp hna i hi)
  have h2 : MemFCT (singletonProgM fn (d.pre ++ d.ren))
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps))
      ∧ HasRuns (singletonProgM fn (d.pre ++ d.ren))
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps)) := by
    rw [hpre, hren']
    exact memFCT_step
      (G := fun s => EntryAt fn s ∧ RenStart (argBind σ nm) d.ps
        (· ∈ loopNames (regionCoBody σ nm t r.code r.res)) s)
      (fun s₁ s₂ h => ⟨(hE _ (regionVirtPub_entry h).1).1, (hE _ (regionVirtPub_entry h).2).1⟩)
      (fun s hs hrun => by
        obtain ⟨ℓ, hℓ⟩ := hrun
        exact ⟨_, fRun_renameLoop fn _ _ d.ps _ hlopA hqA RF.ctl RF.cond RF.ren RF.names RF.nd
          RF.ts RF.tgt RF.fresh hNA hs.1 hs.2 hℓ⟩)
      (memFCT_renameLoop fn _ _ d.ps _ hlopA hqA RF.ctl RF.cond RF.ren RF.names RF.nd RF.ts
        RF.tgt RF.fresh hNA) h1
  have h3 : MemFCT (singletonProgM fn (d.pre ++ d.merged))
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps))
      ∧ HasRuns (singletonProgM fn (d.pre ++ d.merged))
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps)) := by
    simp only [regionMergeB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hmg
    by_cases hnil : d.tau = []
    · rw [hmerged, hnil, map_renRM_renOf_nil]
      exact h2
    · have hck := (hmg.resolve_left hnil).1
      have hl1' : regLeakB (renOf d.tau) d.pre d.ren (tabAt d.live) = true := by
        rcases Bool.or_eq_true_iff.mp hl1 with h | h
        · exact absurd (beq_iff_eq.mp h) hnil
        · exact h
      have hC := liveCert_of_regCoB fn hlop hck
      have hX := leakCert_of_regLeakB fn hl1'
      have hck' := hck
      simp only [regCoB, Bool.and_eq_true, beq_iff_eq] at hck'
      obtain ⟨⟨⟨-, hAN⟩, hentL⟩, -⟩ := hck'
      have hr' : ∀ x, x ∈ liveAt (tabAt d.live) (d.pre ++ d.ren).length d.pre.length →
          renOf d.tau x = x := fun x hx => by simpa using List.all_eq_true.mp hentL x hx
      have ha' : ∀ x, x ∈ d.arrs → renOf d.tau x = x := fun x hx => by
        simpa using List.all_eq_true.mp hAN x hx
      rw [hmerged]
      exact memFCT_step (G := EntryAt fn) hG
        (fun s hs hrun => by
          obtain ⟨⟨b0, lfn⟩, zf⟩ := s
          obtain ⟨rfl, h0'⟩ := hs
          obtain ⟨ℓ, hℓ⟩ := hrun
          obtain ⟨T, -, hT⟩ := fRun_live_prefix hlop hC hX hr' ha' b0 zf h0' hℓ
          exact ⟨_, hT⟩)
        (memFCT_live_prefix hlop hq hC hX hr' ha') h2
  simp only [regionNopB, Bool.and_eq_true] at hnop
  have h4 : MemFCT (singletonProgM fn d.nop)
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps))
      ∧ HasRuns (singletonProgM fn d.nop)
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps)) := by
    rw [hnopE]
    exact memFCT_step (G := EntryAt fn) hG
      (fun s hs hrun => by
        obtain ⟨⟨b0, lfn⟩, zf⟩ := s
        obtain ⟨rfl, h0'⟩ := hs
        obtain ⟨ℓ, hℓ⟩ := hrun
        obtain ⟨k, t', hk⟩ := lsemFuelMemF_of_fRun hℓ
        obtain ⟨t'', ht'', -⟩ := selfNop_run (fn := lfn) hlop hnop.1 b0 h0' zf k t' hk
        exact fRun_of_lsemFuelMemF ht'')
      (selfNop_memFCT hlop hq hnop.1 (leakCert_of_regLeakB fn hl2)) h3
  rw [href]
  cases hS : d.sites with
  | false => exact h4
  | true =>
      simp only [regionSitesB, hS, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hsite
      obtain ⟨⟨hfuse, -⟩, -⟩ := hsite
      have hsplit : d.nop = d.pre ++ d.nop.drop d.pre.length := by
        conv_lhs => rw [← List.take_append_drop d.pre.length d.nop]
        rw [hnopE, selfNop_take, List.take_left']
        rfl
      rw [hsplit] at h4
      exact memFCT_step (G := fun s => EntryAt fn s ∧ E64 (fuseRegs σ nm) s.prog.base)
        (fun s₁ s₂ h => ⟨⟨(hE _ (regionVirtPub_entry h).1).1.1, (hE _ (regionVirtPub_entry h).1).2⟩,
          ⟨(hE _ (regionVirtPub_entry h).2).1.1, (hE _ (regionVirtPub_entry h).2).2⟩⟩)
        (fun s hs hrun => by
          obtain ⟨ℓ, k, t', hk⟩ := hrun
          obtain ⟨k', t'', h'⟩ :=
            fuseMulHi_lsemFuelMemFLeak_pre hfuse fn s hs.1.2 hs.2 k _ hk
          exact ⟨_, k', t'', h'⟩)
        (memFCT_of_fRun_map id fun s ℓ hs hrun => by
          obtain ⟨k, t', hk⟩ := hrun
          obtain ⟨k', t'', h'⟩ :=
            fuseMulHi_lsemFuelMemFLeak_pre hfuse fn s hs.1.2 hs.2 k _ hk
          exact ⟨k', t'', h'⟩) h4

/-- **Constant time of the fused code of the gate** at the export `r` of `p`:
    `regionFused_memFCT_of_regionExp` at `r`. -/
theorem regionFused_memFCT (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true) :
    MemFCT (singletonProgM fn (regionCoParts σ nm body t r.code r.res cert).fused)
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body)
          (unren (regionCoParts σ nm body t r.code r.res cert).ps))
      ∧ HasRuns (singletonProgM fn (regionCoParts σ nm body t r.code r.res cert).fused)
        (RegionVirtPub σ nm fn fuel p L Pre (frameE body)
          (unren (regionCoParts σ nm body t r.code r.res cert).ps)) :=
  regionFused_memFCT_of_regionExp Pj fn fuel hp hc hct (regionExp_of_exportR _ hr)
    (regionWebsLeak_of_exportR _ hr) hg hlk

section Fold

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_lpc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (slotsOkB cellsDistinctB
  CellRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL (CellRelF cellRel_setLpc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopWLeak (GTr foldG gTr_eq
  cellFoldLR_gtr)

/-- **The trace of a quiet prefix followed by a cell fold.** Let the prefix `pre` be
    instructions `Lopn` that emit no event, and let the cell fold `cellFoldLR` at slot
    arrays `R` that pass `slotsOkB` and `cellsDistinctB` take the code `X` to `L2`. Let every
    straight run of the prefix from `b0` be matched by a straight run from `b0C` into a
    cell-related state. A terminating traced run of `pre ++ X` from `b0` with the trace `ℓ`
    gives a state `sX` of `fn` at position `0` from which `X` has a terminating traced run
    with the trace `ℓ`, and a trace `g`, computed along the run of `X` from `sX` by
    `foldG L2`, of a terminating traced run of `pre ++ L2` from `b0C`. -/
theorem prefixFold_gtr {R : Slots} (hR : slotsOkB R = true) (hD : cellsDistinctB R = true)
    {pre X L2 : List LinstrRM} (hpre : ∀ i ∈ pre, IsLopn i)
    (hq : ∀ i ∈ pre, ∀ x, instrLeakB x i = [])
    (hfold : cellFoldLR R [] X = some L2) (fn : String) {b0 b0C : LstateM} {zf : Bool}
    (h0 : b0.lpc = 0) (h0C : b0C.lpc = 0)
    (hC : ∀ b1 z1, runStraightF pre b0 zf = some (b1, z1) →
      ∃ b1C, runStraightF pre b0C zf = some (b1C, z1) ∧ CellRel R [] b1 b1C)
    {f : Nat} {t : LstateMF} {ℓ : List CTLeak}
    (hrun : lsemFuelMemFLeak (singletonProgM fn (pre ++ X)) f
      { prog := { base := b0, lfn := fn }, zf := zf } = some (t, ℓ)) :
    ∃ (sX : LstateMF) (g : List CTLeak), sX.prog.lfn = fn ∧ sX.prog.base.lpc = 0
      ∧ FRun (singletonProgM fn X) sX ℓ ∧ GTr (foldG L2) (singletonProgM fn X) sX g
      ∧ FRun (singletonProgM fn (pre ++ L2))
        { prog := { base := b0C, lfn := fn }, zf := zf } g := by
  have hXL := X86Backend.CellFoldLReg.ctlOK_of_cellFoldLR _ _ _ hfold
  have hu : lsemFuelMemF (singletonProgM fn (pre ++ X)) f
      { prog := { base := b0, lfn := fn }, zf := zf } = some t := by
    rw [← lsemFuelMemFLeak_fst, hrun]
    rfl
  have hpos : ∀ j, j < pre.length →
      (singletonProgM fn (pre ++ X)).body[b0.lpc + j]? = pre[j]? := fun j hj => by
    simp only [singletonProgM, h0, Nat.zero_add]
    exact List.getElem?_append_left hj
  obtain ⟨f', rfl⟩ := Nat.exists_eq_add_of_le
    (lsemFuelMemF_seg_fuel _ fn rfl _ _ zf _ t hpre hpos hu)
  obtain ⟨b1, z1, -, hb1run, -, -⟩ :=
    X86Backend.ImageAddrRouteW.strip_prefix fn _ _ hpre hXL.1 _ zf h0 _ t hu
  rw [lsemFuelMemFLeak_segF _ fn rfl _ _ zf f' (b1, z1) hpre hpos hb1run] at hrun
  obtain ⟨q, hq', hqe⟩ := Option.map_eq_some_iff.mp hrun
  have hpc1 : b1.lpc = pre.length := by
    rw [runStraightF_lpc _ _ zf b1 z1 hb1run, h0, Nat.zero_add]
  have hsh : ({ prog := { base := b1, lfn := fn }, zf := z1 } : LstateMF)
      = shiftS pre.length { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } := by
    simp only [shiftS, JasminLsemMemLoop.LstateM.lpc_setLpc, Nat.zero_add, ← hpc1]
    rfl
  rw [hsh, X86Backend.ImageAddrLeak.lsemFuelMemFLeak_prefix_eq fn _ _ hpre hXL.1] at hq'
  obtain ⟨ql, hql, rfl⟩ := Option.map_eq_some_iff.mp hq'
  have hT : ql.2 = ℓ := by
    have h2 : JasminLsemMemFLeakLoop.straightLeakFF pre b0 zf ++ ql.2 = ℓ :=
      congrArg Prod.snd hqe
    rw [straightLeakFF_quiet _ hq] at h2
    exact h2
  obtain ⟨b1C, hb1C, hC1⟩ := hC b1 z1 hb1run
  have hCF : CellRelF R []
      { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 }
      { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 } :=
    ⟨cellRel_setLpc hC1 0, rfl, rfl⟩
  have hXrun : lsemFuelMemF (singletonProgM fn X) f'
      { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } = some ql.1 := by
    rw [← lsemFuelMemFLeak_fst, hql]
    rfl
  obtain ⟨t2, g, ht2, hG⟩ := cellFoldLR_gtr hR hD hfold fn f'
    (s := { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 })
    (s' := { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 }) hCF hXrun
  have hposC : ∀ j, j < pre.length →
      (singletonProgM fn (pre ++ L2)).body[b0C.lpc + j]? = pre[j]? := fun j hj => by
    simp only [singletonProgM, h0C, Nat.zero_add]
    exact List.getElem?_append_left hj
  have hpc1C : b1C.lpc = pre.length := by
    rw [runStraightF_lpc _ _ zf b1C z1 hb1C, h0C, Nat.zero_add]
  have hshC : ({ prog := { base := b1C, lfn := fn }, zf := z1 } : LstateMF)
      = shiftS pre.length { prog := { base := b1C.setLpc 0, lfn := fn }, zf := z1 } := by
    simp only [shiftS, JasminLsemMemLoop.LstateM.lpc_setLpc, Nat.zero_add, ← hpc1C]
    rfl
  refine ⟨{ prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 }, g, rfl, rfl,
    ⟨f', ql.1, by rw [hql, ← hT]⟩, hG, pre.length + f', shiftS pre.length t2, ?_⟩
  rw [lsemFuelMemFLeak_segF _ fn rfl _ b0C zf f' (b1C, z1) hpre hposC hb1C, hshC,
    X86Backend.ImageAddrLeak.lsemFuelMemFLeak_prefix_eq fn _ L2 hpre hXL.2, ht2,
    straightLeakFF_quiet _ hq]
  rfl

/-- **The entry relation of the reference and the image of a region export.** Two
    flag-machine states that are the entry states `emptiedEntry` at the pairs `ps` and the
    cell arrays `R` of two machine states `sa₁` and `sa₂` that satisfy `σ.Regions` and the
    precondition `Pre`, at which the layout `σ` reads off valuations that are equal on the
    positions `L` marks public, whose frame maps of `body` satisfy the facts of the entry
    check, and such that the program `p` denotes within `fuel` at the first valuation in the
    empty call environment. At no cell array the entry states are those of `RegionVirtPub`
    at the frame of `body` and the map `unren ps`. -/
def RegionImgPub (σ : AbiLayout) (nm : String → String) (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (L : Labels Γ) (Pre : AState → Prop) (body : Lcmd) (ps : List (String × String))
    (R : Slots) (s₁ s₂ : LstateMF) : Prop :=
  ∃ (sa₁ sa₂ : AState) (V₁ V₂ : Ctxt.Valuation Γ),
    PubEqV L V₁ V₂ ∧ AbiValOf σ sa₁ V₁ ∧ AbiValOf σ sa₂ V₂
      ∧ EntryFacts σ nm (frameE body sa₁) ∧ EntryFacts σ nm (frameE body sa₂)
      ∧ σ.Regions sa₁ ∧ σ.Regions sa₂ ∧ Pre sa₁ ∧ Pre sa₂
      ∧ s₁ = { prog := { base := emptiedEntry σ ps R body sa₁, lfn := fn }, zf := false }
      ∧ s₂ = { prog := { base := emptiedEntry σ ps R body sa₂, lfn := fn }, zf := false }
      ∧ (p.denoteAt CallEnv.empty fuel V₁).isSome = true

/-- **Constant time of the reference of the gate.** Under the hypotheses of
    `regionFused_memFCT`, the reference `d.ref` of the parts `d := regionCoParts` is constant
    time on the traced flag machine between the entry states of `RegionImgPub` at the pairs
    `d.ps` and the cell arrays `d.cells`, and it has a terminating traced run from each of
    them. Without a cell array the reference is the code `d.fused` and the entry states are
    those of `RegionVirtPub`. With cell arrays the reference is the prefix followed by the
    cell fold of the code of `d.fused` behind the prefix: the trace of a run of the
    reference is computed along the run of that code (`prefixFold_gtr`), whose traces from
    public-equal entries are equal by `regionFused_memFCT`, and two traces computed along
    runs with equal events are equal (`ImageLoopWLeak.gTr_eq`). The code `r` is an exported
    code of `RegionExp fn p (regionWebsEx σ nm) r` that passes the event check
    `RegionWebsLeak`. -/
theorem regionRef_memFCT_of_regionExp (Pj : JLeakParams) {σ : AbiLayout}
    {nm : String → String} (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported} (hr : RegionExp fn p (regionWebsEx σ nm) r)
    (hx : RegionWebsLeak fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true) :
    MemFCT (singletonProgM fn (regionCoParts σ nm body t r.code r.res cert).ref)
        (RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
          (regionCoParts σ nm body t r.code r.res cert).cells)
      ∧ HasRuns (singletonProgM fn (regionCoParts σ nm body t r.code r.res cert).ref)
        (RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
          (regionCoParts σ nm body t r.code r.res cert).cells) := by
  obtain ⟨hFct, hFruns⟩ := regionFused_memFCT_of_regionExp Pj fn fuel hp hc hct hr hx hg hlk
  rw [regionCoB_none] at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨hren, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hfold⟩, himg⟩⟩ := hg
  have hcellsSub := regionCoParts_cells_sub σ nm body t r.code r.res cert none
  generalize hd : regionCoParts σ nm body t r.code r.res cert = d
    at hFct hFruns hren hfold himg hcellsSub ⊢
  have hrefE : d.ref = if d.cells.isEmpty then d.fused
      else d.pre ++ (cellFoldLR d.cells [] (d.fused.drop d.pre.length)).getD
        (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hV : ∀ s₁ s₂, RegionImgPub σ nm fn fuel p L Pre body d.ps d.cells s₁ s₂ →
      ∃ sa₁ sa₂, RegionVirtPub σ nm fn fuel p L Pre (frameE body) (unren d.ps)
          { prog := { base := entryV σ (frameE body sa₁) sa₁ (unren d.ps), lfn := fn },
            zf := false }
          { prog := { base := entryV σ (frameE body sa₂) sa₂ (unren d.ps), lfn := fn },
            zf := false }
        ∧ EntryFacts σ nm (frameE body sa₁) ∧ EntryFacts σ nm (frameE body sa₂)
        ∧ ArgSrc σ nm (frameE body sa₁) sa₁ ∧ ArgSrc σ nm (frameE body sa₂) sa₂
        ∧ s₁ =
          { prog := { base := emptiedEntry σ d.ps d.cells body sa₁, lfn := fn }, zf := false }
        ∧ s₂ =
          { prog := { base := emptiedEntry σ d.ps d.cells body sa₂, lfn := fn }, zf := false } := by
    rintro s₁ s₂ ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, R₁, R₂, P₁, P₂, h₁, h₂, hden⟩
    have S₁ := E₁.argSrc R₁.stackIn
    have S₂ := E₂.argSrc R₂.stackIn
    exact ⟨sa₁, sa₂, ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, S₁, S₂, R₁, R₂, P₁, P₂, rfl, rfl,
      hden⟩, E₁, E₂, S₁, S₂, h₁, h₂⟩
  by_cases hce : d.cells = []
  · have hrefF : d.ref = d.fused := by
      rw [hrefE, hce]
      rfl
    have hent : ∀ sa, emptiedEntry σ d.ps d.cells body sa
        = entryV σ (frameE body sa) sa (unren d.ps) := by
      intro sa
      rw [hce]
      rfl
    rw [hrefF]
    refine ⟨fun s₁ s₂ ℓ₁ ℓ₂ h => ?_, fun s₁ s₂ h => ?_⟩
    · obtain ⟨sa₁, sa₂, hv, -, -, -, -, rfl, rfl⟩ := hV s₁ s₂ h
      rw [hent, hent]
      exact hFct _ _ ℓ₁ ℓ₂ hv
    · obtain ⟨sa₁, sa₂, hv, -, -, -, -, rfl, rfl⟩ := hV s₁ s₂ h
      rw [hent, hent]
      exact hFruns _ _ hv
  · have hne : d.cells.isEmpty = false := by
      cases hc : d.cells with
      | nil => exact absurd hc hce
      | cons _ _ => rfl
    simp only [regionFoldB, hne, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at hfold
    obtain ⟨hfS, hpsC⟩ := hfold
    obtain ⟨L2, hL2⟩ := Option.isSome_iff_exists.mp hfS
    have hrefC : d.ref = d.pre ++ L2 := by
      rw [hrefE, hne, hL2]
      rfl
    have hpre : d.pre = argBind σ nm ++ movesOf d.ps := by rw [← hd]; rfl
    have hnopE : d.nop = selfNop d.pre.length
        (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) := by
      rw [← hd]; rfl
    have hfusedE : d.fused
        = if d.sites then d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length) else d.nop := by
      rw [← hd]; rfl
    have hsplit : d.nop = d.pre ++ d.nop.drop d.pre.length := by
      conv_lhs => rw [← List.take_append_drop d.pre.length d.nop]
      rw [hnopE, selfNop_take, List.take_left']
      rfl
    have hsplitF : d.fused = d.pre ++ d.fused.drop d.pre.length := by
      rw [hfusedE]
      cases d.sites with
      | true =>
          show d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length)
            = d.pre ++ (d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length)).drop d.pre.length
          rw [List.drop_left']
          rfl
      | false => exact hsplit
    have hI := himg
    simp only [renImageB, Bool.and_eq_true] at hI
    have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hI.1.2
    have RF := renB_spec hren
    have hlop : ∀ i ∈ d.pre, IsLopn i := fun i hi => by
      rw [hpre] at hi
      exact (List.mem_append.mp hi).elim (movesOf_isLopn _ i) (movesOf_isLopn _ i)
    have hq : ∀ i ∈ d.pre, ∀ x, instrLeakB x i = [] := fun i hi => by
      rw [hpre] at hi
      exact (List.mem_append.mp hi).elim (movesOf_quiet _ i) (movesOf_quiet _ i)
    have key : ∀ sa, EntryFacts σ nm (frameE body sa) → ArgSrc σ nm (frameE body sa) sa →
        ∀ (f : Nat) (tF : LstateMF) (ℓ : List CTLeak),
        lsemFuelMemFLeak (singletonProgM fn d.fused) f
          { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn },
            zf := false } = some (tF, ℓ) →
        ∃ (sX : LstateMF) (g : List CTLeak), sX.prog.lfn = fn ∧ sX.prog.base.lpc = 0
          ∧ FRun (singletonProgM fn (d.fused.drop d.pre.length)) sX ℓ
          ∧ GTr (foldG L2) (singletonProgM fn (d.fused.drop d.pre.length)) sX g
          ∧ FRun (singletonProgM fn d.ref)
            { prog := { base := emptiedEntry σ d.ps d.cells body sa, lfn := fn },
              zf := false } g := by
      intro sa E hS f tF ℓ h
      rw [hsplitF] at h
      rw [hrefC]
      refine prefixFold_gtr N.slots N.dist hlop hq hL2 fn rfl rfl (fun b1 z1 hb1 => ?_) h
      obtain ⟨b1C, hb1C, hC1⟩ := X86Backend.ImageAddrRouteW.subCells_prefix (nm := nm)
        (seeds := []) hcellsSub E hS N (fun j hj => (RF.unr j hj).2) rfl hpsC
        (by rw [List.append_nil, ← hpre]; exact hb1)
      rw [List.append_nil, ← hpre] at hb1C
      exact ⟨b1C, hb1C, hC1⟩
    refine ⟨fun s₁ s₂ ℓ₁ ℓ₂ h hr₁ hr₂ => ?_, fun s₁ s₂ h => ?_⟩
    · obtain ⟨sa₁, sa₂, hv, E₁, E₂, S₁, S₂, rfl, rfl⟩ := hV s₁ s₂ h
      obtain ⟨⟨ℓF₁, fF₁, tF₁, hF₁⟩, ⟨ℓF₂, fF₂, tF₂, hF₂⟩⟩ := hFruns _ _ hv
      obtain rfl : ℓF₁ = ℓF₂ := hFct _ _ _ _ hv ⟨fF₁, tF₁, hF₁⟩ ⟨fF₂, tF₂, hF₂⟩
      obtain ⟨sX₁, g₁, hfn₁, hpc₁, ⟨fX₁, tX₁, hX₁⟩, hG₁, hR₁⟩ := key sa₁ E₁ S₁ _ _ _ hF₁
      obtain ⟨sX₂, g₂, hfn₂, hpc₂, ⟨fX₂, tX₂, hX₂⟩, hG₂, hR₂⟩ := key sa₂ E₂ S₂ _ _ _ hF₂
      rw [fRun_unique hr₁ hR₁, fRun_unique hr₂ hR₂]
      exact gTr_eq _ fn _ fX₁ sX₁ tX₁ _ hX₁ fX₂ sX₂ tX₂ hX₂ hfn₁ hfn₂
        (hpc₁.trans hpc₂.symm) g₁ g₂ hG₁ hG₂
    · obtain ⟨sa₁, sa₂, hv, E₁, E₂, S₁, S₂, rfl, rfl⟩ := hV s₁ s₂ h
      obtain ⟨⟨ℓF₁, fF₁, tF₁, hF₁⟩, ⟨ℓF₂, fF₂, tF₂, hF₂⟩⟩ := hFruns _ _ hv
      obtain ⟨-, g₁, -, -, -, -, hR₁⟩ := key sa₁ E₁ S₁ _ _ _ hF₁
      obtain ⟨-, g₂, -, -, -, -, hR₂⟩ := key sa₂ E₂ S₂ _ _ _ hF₂
      exact ⟨⟨g₁, hR₁⟩, ⟨g₂, hR₂⟩⟩

/-- **Constant time of the reference of the gate** at the export `r` of `p`:
    `regionRef_memFCT_of_regionExp` at `r`. -/
theorem regionRef_memFCT (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true) :
    MemFCT (singletonProgM fn (regionCoParts σ nm body t r.code r.res cert).ref)
        (RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
          (regionCoParts σ nm body t r.code r.res cert).cells)
      ∧ HasRuns (singletonProgM fn (regionCoParts σ nm body t r.code r.res cert).ref)
        (RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
          (regionCoParts σ nm body t r.code r.res cert).cells) :=
  regionRef_memFCT_of_regionExp Pj fn fuel hp hc hct (regionExp_of_exportR _ hr)
    (regionWebsLeak_of_exportR _ hr) hg hlk

end Fold

/-- **The states `RegionImgPub` relates are public-equal entry states of the reference
    with halting checked runs.** Under the hypotheses of `regionRef_memFCT`, two states
    related by `RegionImgPub` are related by `OwnedTVLeak.TVPub` of the reference `d.ref`
    at `RegionImgPub`: the run of the reference from an entry state of a machine state in
    `σ.Regions` is in bounds by the bounds invariant of the gate (`idxInvCheckB`). The code
    `r` is an exported code of `RegionExp fn p (regionWebsEx σ nm) r` that passes the event
    check `RegionWebsLeak`. -/
theorem regionImgPub_tvPub_of_regionExp (Pj : JLeakParams) {σ : AbiLayout}
    {nm : String → String} (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported} (hr : RegionExp fn p (regionWebsEx σ nm) r)
    (hx : RegionWebsLeak fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true)
    {s₁ s₂ : LstateMF}
    (h : RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
      (regionCoParts σ nm body t r.code r.res cert).cells s₁ s₂) :
    TVPub fn (regionCoParts σ nm body t r.code r.res cert).ref
      (RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
        (regionCoParts σ nm body t r.code r.res cert).cells) s₁ s₂ := by
  obtain ⟨-, hruns⟩ := regionRef_memFCT_of_regionExp Pj fn fuel hp hc hct hr hx hg hlk
  rw [regionCoB_none] at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨-, ⟨-, himg⟩⟩ := hg
  generalize regionCoParts σ nm body t r.code r.res cert = d at hruns himg h ⊢
  simp only [renImageB, Bool.and_eq_true] at himg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hidx⟩, -⟩, -⟩, -⟩, -⟩, hN⟩, -⟩ := himg
  have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hN
  have hgpN : ∀ x, gpOk x = true → cellIdx d.cells x = none := by
    intro x hx
    cases hcx : cellIdx d.cells x with
    | none => rfl
    | some _ =>
        have := N.gp x (by rw [hcx]; rfl)
        rw [hx] at this
        cases this
  have hck : ∀ sa, EntryFacts σ nm (frameE body sa) → σ.Regions sa →
      (∃ ℓ, FRun (singletonProgM fn d.ref)
        { prog := { base := emptiedEntry σ d.ps d.cells body sa, lfn := fn }, zf := false }
        ℓ) →
      ∃ f u, JasminLsemMemChecked.lsemFuelMemFk true (singletonProgM fn d.ref) f
        { prog := { base := emptiedEntry σ d.ps d.cells body sa, lfn := fn }, zf := false }
          = some u := by
    rintro sa E hreg ⟨ℓ, hℓ⟩
    obtain ⟨k, u, hk⟩ := lsemFuelMemF_of_fRun hℓ
    have hents := boundFacts_entryV (nm := nm)
      (fr := frameC (baseR σ sa d.ps) d.cells (frameE body sa)) (un := unren d.ps) hreg
      fun b hb => by
        obtain ⟨h1, h2, h3⟩ := E.bnds b hb
        refine ⟨h1, h2, ?_⟩
        simp only [frameC, hgpN _ h1]
        exact h3
    exact ⟨k, u, JasminLsemMemChecked.lsemFuelMemFk_of_runIdxOk true _ k _ u hk
      (runIdxOk_of_idxInvCheckB hidx fn _ u rfl rfl (hents _) k hk)⟩
  have h' := h
  obtain ⟨sa₁, sa₂, -, -, -, -, -, E₁, E₂, hR₁, hR₂, -, -, rfl, rfl, -⟩ := h'
  exact ⟨h, rfl, rfl, rfl, rfl, hck sa₁ E₁ hR₁ (hruns _ _ h).1, hck sa₂ E₂ hR₂ (hruns _ _ h).2⟩

/-- **The states `RegionImgPub` relates are public-equal entry states of the reference
    with halting checked runs** at the export `r` of `p`: `regionImgPub_tvPub_of_regionExp`
    at `r`. -/
theorem regionImgPub_tvPub (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true)
    {s₁ s₂ : LstateMF}
    (h : RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
      (regionCoParts σ nm body t r.code r.res cert).cells s₁ s₂) :
    TVPub fn (regionCoParts σ nm body t r.code r.res cert).ref
      (RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
        (regionCoParts σ nm body t r.code r.res cert).cells) s₁ s₂ :=
  regionImgPub_tvPub_of_regionExp Pj fn fuel hp hc hct (regionExp_of_exportR _ hr)
    (regionWebsLeak_of_exportR _ hr) hg hlk h

/-- **Constant time of the image of the cell body of a region export.** Under the
    hypotheses of `regionRef_memFCT`, the image of the cell body of the printed body `body`
    at the slot map `regionSl σ nm d` of the parts `d` is constant time on the traced flag
    machine between the entry states of `RegionImgPub`: the check on traced runs
    `ownedCheckML` of `regionLeakB` carries the constant time of the reference to the image
    (`OwnedTVLeak.memFCT_of_ownedCheckML`). The code `r` is an exported code of
    `RegionExp fn p (regionWebsEx σ nm) r` that passes the event check `RegionWebsLeak`. -/
theorem regionImage_memFCT_of_regionExp (Pj : JLeakParams) {σ : AbiLayout}
    {nm : String → String} (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported} (hr : RegionExp fn p (regionWebsEx σ nm) r)
    (hx : RegionWebsLeak fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true) :
    MemFCT (singletonProgM fn (virtImg (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert))
        (cellBody (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert)) body)))
      (RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
        (regionCoParts σ nm body t r.code r.res cert).cells) := by
  have hml : ownedCheckML (regionCoParts σ nm body t r.code r.res cert).outs
      (regionCoParts σ nm body t r.code r.res cert).ref
      (virtImg (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert))
        (cellBody (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert)) body)) = true := by
    have h := hlk
    simp only [regionLeakB, Bool.and_eq_true] at h
    exact h.2
  exact memFCT_mono
    (fun s₁ s₂ h => regionImgPub_tvPub_of_regionExp Pj fn fuel hp hc hct hr hx hg hlk h)
    (memFCT_of_ownedCheckML hml fn
      (regionRef_memFCT_of_regionExp Pj fn fuel hp hc hct hr hx hg hlk).1)

/-- **Constant time of the image of the cell body of a region export** at the export `r` of
    `p`: `regionImage_memFCT_of_regionExp` at `r`. -/
theorem regionImage_memFCT (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true) :
    MemFCT (singletonProgM fn (virtImg (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert))
        (cellBody (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert)) body)))
      (RegionImgPub σ nm fn fuel p L Pre body (regionCoParts σ nm body t r.code r.res cert).ps
        (regionCoParts σ nm body t r.code r.res cert).cells) :=
  regionImage_memFCT_of_regionExp Pj fn fuel hp hc hct (regionExp_of_exportR _ hr)
    (regionWebsLeak_of_exportR _ hr) hg hlk

/-! ## 10. Constant time of the decoded bytes under the gate with carry chains -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (LstateA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (AddrPub ARun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak (SafeHaltW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)

/-- **Public-equal entry machine states of a region export.** The layout `σ` reads off the
    two states valuations that are equal on the positions `L` marks public; both states
    satisfy `σ.Regions` and the precondition `Pre`; the stack registers are equal; the
    register of every array parameter, its base address, is equal; and the program `p`
    denotes within `fuel` at the first valuation in the empty call environment. -/
def RegionBytePub (σ : AbiLayout) (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (L : Labels Γ) (Pre : AState → Prop)
    (sa₁ sa₂ : AState) : Prop :=
  ∃ V₁ V₂ : Ctxt.Valuation Γ, PubEqV L V₁ V₂ ∧ AbiValOf σ sa₁ V₁ ∧ AbiValOf σ sa₂ V₂
    ∧ σ.Regions sa₁ ∧ σ.Regions sa₂ ∧ Pre sa₁ ∧ Pre sa₂ ∧ sa₁.regs "%rsp" = sa₂.regs "%rsp"
    ∧ (∀ a ∈ σ.args, ∀ n, a.kind = .words n → sa₁.regs a.reg = sa₂.regs a.reg)
    ∧ (p.denoteAt CallEnv.empty fuel V₁).isSome = true

/-- **The facts of the image simulation at the entry of a region export with cells.** Let
    the reference `B` pass the image check `renImageB` at the pairs `ps`, the cell arrays `R`
    and the observed names `outs` against the printed body `body`, let `unren ps` undo
    `renOf ps` on the argument names, and let the cell body pass `imgGateCW` at the frame
    marks with the cells `frameMarkC R body`. At every machine state `sa` that satisfies
    `σ.Regions`, at the frame map `frameC (baseR σ sa ps) R (frameE body sa)`, the slot map
    `sl := slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))` and the bases `baseR σ sa ps`:
    the separation `ImgSep`; no frame-word move of a cell names an array slot
    (`CellNoSlot`); the cell frames `CellFrames`; the gate `imgGateCW` of the cell body; the
    frame map is the frame `frameP` of the body at the names of the body; and the relation
    `ImgRel` of the entry state `emptiedEntry` with the entry `entryA σ sa`. The printed
    class of `regionImgB` gives `CellNoSlot` and `CellFrames` from `cellNoSlotB` and
    `cellAccB`. -/
theorem regionCell_entry {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    (hg : renImageB σ nm ps R outs body B = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j)
    (hgW : imgGateCW (frameMarkC R body) (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps)))
      (cellBody (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body) = true)
    (sa : AState) (hreg : σ.Regions sa) (fn : String) :
    X86Backend.ImageAddrSim.ImgSep (frameC (baseR σ sa ps) R (frameE body sa))
        (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) (baseR σ sa ps) (frameRsp body sa)
      ∧ CellNoSlot (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body
      ∧ CellFrames (frameC (baseR σ sa ps) R (frameE body sa))
          (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) (baseR σ sa ps)
          (frameRsp body sa) body
      ∧ imgGateCW (frameC (baseR σ sa ps) R (frameE body sa))
          (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps)))
          (cellBody (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body) = true
      ∧ (∀ q ∈ X86Backend.ImageAddrFrame.bodyNamesI body,
          frameC (baseR σ sa ps) R (frameE body sa) q
            = frameP (Params.ofBody body) (frameRsp body sa) q)
      ∧ ImgRel (frameC (baseR σ sa ps) R (frameE body sa))
          (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) (baseR σ sa ps)
          (cellBody (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body)
          { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false }
          (entryA σ sa) false := by
  simp only [renImageB, calleeImgT_none, calleeImgBT_none, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hgate⟩, hfr⟩, hent⟩, hN⟩, hlen⟩ := hg
  have E := entryB_spec hent sa
  have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hN
  have hgpN : ∀ x, gpOk x = true → cellIdx R x = none := by
    intro x hx
    cases hc : cellIdx R x with
    | none => rfl
    | some _ =>
        have := N.gp x (by rw [hc]; rfl)
        rw [hx] at this
        cases this
  have hun : ∀ q A n, slotArrOf σ nm q = some (A, n) → unren ps (renOf ps A) = A := by
    intro q A n h
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
    exact hU j (List.getElem?_eq_some_iff.mp hj).1
  have hS0 := imgSep_slotRen (ren := renOf ps)
    (X86Backend.ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot
      X86Backend.ImageAddrRoute.slotArrOf_not_fa) hun
  have hword : ∀ q a, frameE body sa q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o := by
    intro q a ha
    obtain ⟨hq, o, ho, rfl⟩ := X86Backend.ImageAddrFrame.frameIn_some ha
    have := X86Backend.ImageAddrFrame.frameOkB_range hfr hq ho
    exact ⟨_, this.1, this.2, rfl⟩
  have hsl : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      X86Backend.DecodeGenMem.regLen (rsOf σ) (unren ps A) = n := by
    intro q A n hq'
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hq'
    rw [hun q A0 n hq0]
    exact E.len q A0 n hq0
  have hrenS : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      renOf ps (unren ps A) = A := by
    intro q A n hq'
    obtain ⟨A0, hq0, rfl⟩ := slotRen_some hq'
    rw [hun q A0 n hq0]
  have hslC : ∀ q A n, slotRen (slotArrOf σ nm) (renOf ps) q = some (A, n) →
      cellIdx R q = none := by
    intro q A n hq'
    obtain ⟨A0, hq0, -⟩ := slotRen_some hq'
    obtain ⟨a, ha⟩ := E.slot q A0 n hq0
    exact N.body q (X86Backend.ImageAddrFrame.frameIn_some ha).1
  have hsep := X86Backend.ImageAddrRouteW.imgSep_cellsU (ren := renOf ps) E.rs hreg hS0 hword
    hsl (fun p hp => (hlen p hp).1) (fun p hp => (hlen p hp).2) hrenS N.gp hslC
  have hred : ∀ A j, cellIdx R (memName A (8 * j)) = some (A, j) →
      Ascent.AddrMem.Disjoint8 (X86Backend.DecodePrintedAddr.redW (frameRsp body sa))
        (cellAt (baseR σ sa ps A) j) := by
    intro A j hc
    obtain ⟨n, hn, hj, -⟩ := X86Backend.ImageStraightCells.cellIdx_spec hc
    have hk : X86Backend.DecodeGenMem.regK (rsOf σ) (unren ps A) j := by
      unfold X86Backend.DecodeGenMem.regK
      rw [(hlen _ hn).1]
      exact hj
    have hr : X86Backend.DecodePrintedAddr.redW (frameRsp body sa)
        = sa.regs "%rsp" + BitVec.ofInt 64 (X86Backend.LprogBytes.cmovRedZone
          - (Params.ofBody body).frame) := by
      simp only [X86Backend.DecodePrintedAddr.redW, frameRsp, BitVec.add_assoc,
        ← BitVec.ofInt_add]
      congr 2
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hr]
    have h2 := X86Backend.ImageAddrFrame.frameOkB_red hfr
    exact X86Backend.DecodeGenNode.frameSep_of_regions E.rs hreg (unren ps A) j hk _ h2.1 h2.2
  have hNF : CellNoSlot (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body
      ∧ CellFrames (frameC (baseR σ sa ps) R (frameE body sa))
          (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) (baseR σ sa ps)
          (frameRsp body sa) body := by
    have hgate := regionImgCoreB_of_regionImgB hgate
    simp only [regionImgCoreB, Bool.and_eq_true] at hgate
    obtain ⟨⟨⟨⟨-, hacc⟩, hns⟩, -⟩, -⟩ := hgate
    exact ⟨X86Backend.ImageStraightCells.cellNoSlotB_spec hns,
      X86Backend.ImageStraightCells.cellFrames_of hacc N.gp (fun x hx => hS0.gp x hx) hred⟩
  have hgate' : imgGateCW (frameC (baseR σ sa ps) R (frameE body sa))
      (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps)))
      (cellBody (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body) = true := by
    rw [X86Backend.ImageAddrCidx.imgGateCW_congr (frame' := frameMarkC R body)
      (X86Backend.ImageStraightCells.frameC_isSome _ _ body sa)]
    exact hgW
  have hfr' : ∀ q ∈ X86Backend.ImageAddrFrame.bodyNamesI body,
      frameC (baseR σ sa ps) R (frameE body sa) q
        = frameP (Params.ofBody body) (frameRsp body sa) q := by
    intro q hq'
    simp only [frameC, N.body q hq']
    show X86Backend.ImageAddrFrame.frameIn body _ q = _
    unfold X86Backend.ImageAddrFrame.frameIn
    rw [ite_eq_left hq']
  have hrel0 := imgRel_entryV (σ := σ) (nm := nm)
    (fr := frameC (baseR σ sa ps) R (frameE body sa)) (sa := sa)
    (body := cellBody (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps))) body)
    (fn := fn) (ren := renOf ps) (un := unren ps)
    ((E.argSrc hreg.stackIn).congr (fun x hx => by simp only [frameC, hgpN _ hx])
      (fun x => by simp only [frameC, X86Backend.ImageStraightCells.cellIdx_slotOfReg]))
    (fun _ _ hs => X86Backend.ImageStraightCells.cellBody_save hent hs) hU
  exact ⟨hsep, hNF.1, hNF.2, hgate', hfr',
    X86Backend.ImageStraightCells.imgRel_cellArrs (R := R) hrel0⟩

/-- **Constant time of the decoded bytes of a region export whose printed body passes the
    gate with carry chains.** Under the hypotheses of `regionRef_memFCT`, let the printed
    body `body` be in the class `printedAddrWB`, and let its cell body at the slot map
    `regionSl σ nm d` of the parts `d` pass the gate `imgGateCW` at the frame marks with the
    cells of `d.cells`. Every decoding of the function bytes of `body` is constant time
    under the regime `doitm` and any side condition between machine states related by
    `RegionBytePub`. The image of the cell body is constant time by `regionImage_memFCT`;
    the address machine on a body with cell accesses and conditional branches by
    `ImageLoopWLeak.cell_image_addr_ctCW'`, at the frame map with the cells and the invariant
    of the window at the entry (`ImageAddrCidx.CidxInv.of_lpc_zero`), whose cell
    addresses are fixed offsets from the array bases that `RegionBytePub` equates; the
    decoded bytes by `ImageStraightCellsCT.bytesTraceW_of_printedAddrWB`. The code `r` is
    an exported code of `RegionExp fn p (regionWebsEx σ nm) r` that passes the event check
    `RegionWebsLeak`. -/
theorem regionWide_bytes_ct_of_regionExp (Pj : JLeakParams) {σ : AbiLayout}
    {nm : String → String} (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported} (hr : RegionExp fn p (regionWebsEx σ nm) r)
    (hx : RegionWebsLeak fn p (regionWebsEx σ nm) r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true)
    (hprW : printedAddrWB body = true)
    (hgW : imgGateCW (frameMarkC (regionCoParts σ nm body t r.code r.res cert).cells body)
      (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert))
      (cellBody (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert)) body) = true)
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (RegionBytePub σ fuel p L Pre)
      (fun sa u => ∃ sa', RunL .doitm ok prog 0 sa u sa') := by
  have himgCT := regionImage_memFCT_of_regionExp Pj fn fuel hp hc hct hr hx hg hlk
  have htv : ∀ s₁ s₂, RegionImgPub σ nm fn fuel p L Pre body
      (regionCoParts σ nm body t r.code r.res cert).ps (regionCoParts σ nm body t r.code r.res cert).cells
      s₁ s₂ → _ :=
    fun s₁ s₂ h => regionImgPub_tvPub_of_regionExp Pj fn fuel hp hc hct hr hx hg hlk h
  have hcellsSub := regionCoParts_cells_sub σ nm body t r.code r.res cert none
  rw [regionCoB_none] at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨hren, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg
  generalize regionCoParts σ nm body t r.code r.res cert = d
    at himgCT htv hren himg hgW hcellsSub
  have RF := renB_spec hren
  have hUR : ∀ j, j < σ.args.length → unren d.ps (renOf d.ps (argName j)) = argName j :=
    fun j hj => (RF.unr j hj).2
  have hI := himg
  simp only [renImageB, calleeImgT_none, Bool.and_eq_true] at hI
  obtain ⟨⟨⟨⟨⟨⟨⟨hck, -⟩, hphys⟩, -⟩, -⟩, hent⟩, -⟩, -⟩ := hI
  rintro sa₁ sa₂ u₁ u₂ ⟨V₁, V₂, hpub, hV₁, hV₂, hreg₁, hreg₂, hP₁, hP₂, hrspE, hbases, hden⟩
    ⟨sa₁', hb₁⟩ ⟨sa₂', hb₂⟩
  have E₁ := entryB_spec hent sa₁
  have E₂ := entryB_spec hent sa₂
  obtain ⟨hsep, hN, hF, hgate, hfr, hrel₁⟩ := regionCell_entry himg hUR hgW sa₁ hreg₁ fn
  obtain ⟨-, -, -, -, -, hrel₂⟩ := regionCell_entry himg hUR hgW sa₂ hreg₂ fn
  have hrsp : frameRsp body sa₂ = frameRsp body sa₁ := by
    unfold frameRsp
    rw [hrspE]
  have hfrE : frameE body sa₂ = frameE body sa₁ := by
    unfold frameE
    rw [hrsp]
  have hbJ : ∀ j a, σ.args[j]? = some a → ∀ n, a.kind = .words n →
      baseR σ sa₂ d.ps (renOf d.ps (argName j)) = baseR σ sa₁ d.ps (renOf d.ps (argName j)) := by
    intro j a hj n hk
    show abiBase (abiReg σ) sa₂ (unren d.ps (renOf d.ps (argName j)))
      = abiBase (abiReg σ) sa₁ (unren d.ps (renOf d.ps (argName j)))
    rw [hUR j (List.getElem?_eq_some_iff.mp hj).1, abiBase_argName hj, abiBase_argName hj]
    exact (hbases a (List.mem_of_getElem? hj) n hk).symm
  have hbA : ∀ q ∈ d.cells, baseR σ sa₂ d.ps q.1 = baseR σ sa₁ d.ps q.1 := by
    intro q hq
    obtain ⟨j, a, hj, hk, he⟩ := X86Backend.ImageAddrRouteW.cellArrsR_mem (hcellsSub q hq)
    rw [he]
    exact hbJ j a hj q.2 hk
  have hfrC : frameC (baseR σ sa₂ d.ps) d.cells (frameE body sa₂)
      = frameC (baseR σ sa₁ d.ps) d.cells (frameE body sa₁) := by
    funext q
    unfold frameC
    cases hcq : cellIdx d.cells q with
    | none =>
        simp only
        rw [hfrE]
    | some Aj =>
        obtain ⟨A, j⟩ := Aj
        obtain ⟨n, hn, -, -⟩ := X86Backend.ImageStraightCells.cellIdx_spec hcq
        simp only
        rw [hbA _ hn]
  have hbase : ∀ q A n, regionSl σ nm d q = some (A, n) →
      baseR σ sa₂ d.ps A = baseR σ sa₁ d.ps A := by
    intro q A n hq
    obtain ⟨m', hq', -⟩ := X86Backend.ImageStraightCells.slotArrC_some hq
    obtain ⟨A0, hA0, rfl⟩ := slotRen_some hq'
    obtain ⟨j, a0, hj, hkind, rfl, -⟩ := slotArrOf_some hA0
    exact hbJ j a0 hj _ hkind
  have hrel₂' : ImgRel (frameC (baseR σ sa₁ d.ps) d.cells (frameE body sa₁)) (regionSl σ nm d)
      (baseR σ sa₁ d.ps) (cellBody (regionSl σ nm d) body)
      { prog := { base := emptiedEntry σ d.ps d.cells body sa₂, lfn := fn }, zf := false }
      (entryA σ sa₂) false := by
    have key : ∀ fr : String → Option (BitVec 64),
        fr = frameC (baseR σ sa₁ d.ps) d.cells (frameE body sa₁) →
        ImgRel fr (regionSl σ nm d) (baseR σ sa₁ d.ps) (cellBody (regionSl σ nm d) body)
          { prog := { base := emptiedEntry σ d.ps d.cells body sa₂, lfn := fn }, zf := false }
          (entryA σ sa₂) false →
        ImgRel (frameC (baseR σ sa₁ d.ps) d.cells (frameE body sa₁)) (regionSl σ nm d)
          (baseR σ sa₁ d.ps) (cellBody (regionSl σ nm d) body)
          { prog := { base := emptiedEntry σ d.ps d.cells body sa₂, lfn := fn }, zf := false }
          (entryA σ sa₂) false := by
      rintro _ rfl h
      exact h
    exact key _ hfrC (X86Backend.ImageStraightLeak.imgRel_of_base_eq hbase hrel₂)
  have hpubS : RegionImgPub σ nm fn fuel p L Pre body d.ps d.cells
      { prog := { base := emptiedEntry σ d.ps d.cells body sa₁, lfn := fn }, zf := false }
      { prog := { base := emptiedEntry σ d.ps d.cells body sa₂, lfn := fn }, zf := false } :=
    ⟨sa₁, sa₂, V₁, V₂, hpub, hV₁, hV₂, E₁, E₂, hreg₁, hreg₂, hP₁, hP₂, rfl, rfl, hden⟩
  obtain ⟨-, -, -, -, -, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩ := htv _ _ hpubS
  obtain ⟨g₁, w₁, hi₁, -⟩ :=
    X86Backend.OwnedLprogTVChecked.ownedCheckMC_sound hck fn _ t₁ rfl rfl f₁ hk₁
  obtain ⟨g₂, w₂, hi₂, -⟩ :=
    X86Backend.OwnedLprogTVChecked.ownedCheckMC_sound hck fn _ t₂ rfl rfl f₂ hk₂
  have hA := X86Backend.ImageLoopWLeak.cell_image_addr_ctCW' hsep hphys hgate hN hF fn himgCT
  have hsafe : ∀ (s u : LstateMF) (a : LstateA) (f : Nat), s.prog.lfn = fn →
      ImgRel (frameC (baseR σ sa₁ d.ps) d.cells (frameE body sa₁)) (regionSl σ nm d)
        (baseR σ sa₁ d.ps) (cellBody (regionSl σ nm d) body) s a false →
      X86Backend.ImageAddrCidx.CidxInv (regionSl σ nm d) (baseR σ sa₁ d.ps)
        (cellBody (regionSl σ nm d) body) s →
      lsemFuelMemFk true (singletonProgM fn
        (virtImg (regionSl σ nm d) (cellBody (regionSl σ nm d) body))) f s = some u →
      SafeHaltW (frameC (baseR σ sa₁ d.ps) d.cells (frameE body sa₁)) (frameRsp body sa₁) body
        (a, false) := by
    intro s u a f hfn hrl hinv hk
    obtain ⟨fA, sA, zA, h1, -, -, h3⟩ :=
      X86Backend.ImageAddrCellsLoop.image_addr_simCW' (body := body) hsep hphys hgate hN hF fn
        (X86Backend.ImageAddrCellsLoop.imgStepWCond_of_gateCW _ hphys hgate fn) f s u a false hfn
        (X86Backend.ImageAddrSimW.imgRelW_of hrl) hinv hk
    exact ⟨fA, _, h1, h3⟩
  have hinv₁ : X86Backend.ImageAddrCidx.CidxInv (regionSl σ nm d) (baseR σ sa₁ d.ps)
      (cellBody (regionSl σ nm d) body)
      { prog := { base := emptiedEntry σ d.ps d.cells body sa₁, lfn := fn }, zf := false } :=
    X86Backend.ImageAddrCidx.CidxInv.of_lpc_zero (by rw [← hrel₁.pc]; rfl)
  have hinv₂ : X86Backend.ImageAddrCidx.CidxInv (regionSl σ nm d) (baseR σ sa₁ d.ps)
      (cellBody (regionSl σ nm d) body)
      { prog := { base := emptiedEntry σ d.ps d.cells body sa₂, lfn := fn }, zf := false } :=
    X86Backend.ImageAddrCidx.CidxInv.of_lpc_zero (by rw [← hrel₂'.pc]; rfl)
  obtain ⟨m₁, r₁, hrA₁, hs₁⟩ := hsafe _ w₁ _ g₁ rfl hrel₁ hinv₁ hi₁
  obtain ⟨m₂, r₂, hrA₂, hs₂⟩ := hsafe _ w₂ _ g₂ rfl hrel₂' hinv₂ hi₂
  rw [X86Backend.ImageAddrFrame.runA_congr hfr] at hrA₁ hrA₂
  rw [X86Backend.ImageAddrFrame.runSafe_congr hfr] at hs₁ hs₂
  have hentA : ∀ sa : AState, X86Backend.DecodePrintedAddrLeak.Entry sa (entryA σ sa) :=
    fun sa => ⟨rfl, fun R hR => by
      have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (phys R)⟩ := by
        simp only [entryA, hR, ite_true]
      unfold LstateN.getW
      rw [hl]
      simp, rfl⟩
  have hAP : X86Backend.ImageLoopWLeak.AddrPubC
      (frameC (baseR σ sa₁ d.ps) d.cells (frameE body sa₁)) (regionSl σ nm d)
      (baseR σ sa₁ d.ps) (cellBody (regionSl σ nm d) body) fn
      (RegionImgPub σ nm fn fuel p L Pre body d.ps d.cells)
      (entryA σ sa₁, false) (entryA σ sa₂, false) :=
    ⟨_, _, hpubS, rfl, rfl, rfl, hrel₁, hrel₂', hinv₁, hinv₂, ⟨g₁, w₁, hi₁⟩, ⟨g₂, w₂, hi₂⟩⟩
  exact X86Backend.ImageStraightCellsCT.bytesTraceW_of_printedAddrWB hprW prog hdec
    (frameRsp body sa₁) sa₁ sa₂ rfl hrsp (entryA σ sa₁, false) (entryA σ sa₂, false)
    (hentA sa₁) (hentA sa₂) ⟨m₁, r₁, hrA₁, hs₁⟩ ⟨m₂, r₂, hrA₂, hs₂⟩
    (fun ℓ₁ ℓ₂ h₁ h₂ => hA _ _ ℓ₁ ℓ₂ hAP
      (by simpa only [ARun, X86Backend.DecodePrintedAddrLeak.runALeak_congr hfr] using h₁)
      (by simpa only [ARun, X86Backend.DecodePrintedAddrLeak.runALeak_congr hfr] using h₂))
    ok ok u₁ u₂ sa₁' sa₂' hb₁ hb₂

/-- **Constant time of the decoded bytes of a region export whose printed body passes the
    gate with carry chains** at the export `r` of `p`: `regionWide_bytes_ct_of_regionExp`
    at `r`. -/
theorem regionWide_bytes_ct (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    (fn : String) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) (hc : p.callFree = true) {L : Labels Γ} {Pre : AState → Prop}
    (hct : ∀ V₁ V₂ : Ctxt.Valuation Γ,
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₁) →
      (∃ sa, σ.Regions sa ∧ Pre sa ∧ AbiValOf σ sa V₂) → PubEqV L V₁ V₂ →
      (NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd
        = (NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd)
    {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) {body : Lcmd}
    {cert : List (String × String)} (hg : regionCoB σ nm body t r.code r.res cert = true)
    (hlk : regionLeakB σ nm body t r.code r.res cert = true)
    (hprW : printedAddrWB body = true)
    (hgW : imgGateCW (frameMarkC (regionCoParts σ nm body t r.code r.res cert).cells body)
      (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert))
      (cellBody (regionSl σ nm (regionCoParts σ nm body t r.code r.res cert)) body) = true)
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (RegionBytePub σ fuel p L Pre)
      (fun sa u => ∃ sa', RunL .doitm ok prog 0 sa u sa') :=
  regionWide_bytes_ct_of_regionExp Pj fn fuel hp hc hct (regionExp_of_exportR _ hr)
    (regionWebsLeak_of_exportR _ hr) hg hlk hprW hgW ok hdec

/-! ## 11. The back half -/

/-- **The constant-time check of a printed body** `body` against the export with the code
    `code` and the result operands `res`: the check of the events `regionLeakB`, the printed
    class `printedAddrWB`, and the image gate with carry chains and indexed stores through a
    cell `imgGateCW` of the cell body
    at the frame marks with the cells of the parts `d` (`frameMarkC`) and the slot map
    `regionSl σ nm d`. These are the hypotheses of `regionWide_bytes_ct` beside the gate
    `regionCoB`. -/
def regionCtB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String)) : Bool :=
  regionLeakB σ nm body t code res cert && printedAddrWB body
    && imgGateCW (frameMarkC (regionCoParts σ nm body t code res cert).cells body)
      (regionSl σ nm (regionCoParts σ nm body t code res cert))
      (cellBody (regionSl σ nm (regionCoParts σ nm body t code res cert)) body)

/-- The three conjuncts of `regionCtB`. -/
theorem regionCtB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd} {t : JasminTy}
    {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    (h : regionCtB σ nm body t code res cert = true) :
    regionLeakB σ nm body t code res cert = true ∧ printedAddrWB body = true
      ∧ imgGateCW (frameMarkC (regionCoParts σ nm body t code res cert).cells body)
          (regionSl σ nm (regionCoParts σ nm body t code res cert))
          (cellBody (regionSl σ nm (regionCoParts σ nm body t code res cert)) body) = true := by
  simp only [regionCtB, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The position of the function entered at a call target** behind a caller of `n`
    instructions: the first position `i` of `T` whose entry `n + T.entryIdx i` is the target,
    and `none` at a target that is the entry of no function of `T`. -/
def CalleeTab.tgtPos? (T : CalleeTab) (n tg : Nat) : Option Nat :=
  (List.range T.fns.length).find? fun i => n + T.entryIdx i == tg

/-- **The public argument registers at the call targets of a table** behind a caller of `n`
    instructions (the map `ext` of `AbiLayout.ctCheckRXT`): at the entry of a function of `T`
    the registers of its public arguments, and `none` at every other target, where the
    decision refuses a call. -/
def CalleeTab.ctIfc (T : CalleeTab) (n : Nat) : Nat → Option (List String) :=
  fun tg => (T.tgtPos? n tg).bind fun i => T.fns[i]?.map (·.pubRegs)

/-- **The destinations at the call targets of a table** behind a caller of `n` instructions
    (the map `w` of `AbiLayout.ctCheckRXT`): at the entry of a function of `T` the destination
    `CalleeData.outDst?` of that function, and at every other target that of the first
    function, as `CalleeTab.symPos` places a symbol outside the table at the first function. -/
def CalleeTab.ctDst (T : CalleeTab) (n : Nat) : Nat → Option (String × Nat) :=
  fun tg => T.fns[(T.tgtPos? n tg).getD 0]?.bind (·.outDst?)

/-- **The clobber set of a table**: the registers that some function of `T` clobbers. -/
def CalleeTab.clobB (T : CalleeTab) (x : String) : Bool :=
  T.fns.any fun c => c.clob.contains x

/-- At the table of one function the call target `n` is its entry and every other target is
    no entry. -/
theorem CalleeTab.tgtPos?_one (c : CalleeData) (n tg : Nat) :
    (CalleeTab.one c).tgtPos? n tg = if tg = n then some 0 else none := by
  by_cases h : tg = n
  · simp [CalleeTab.tgtPos?, CalleeTab.one, h]
  · simp [CalleeTab.tgtPos?, CalleeTab.one, h, Ne.symm h]

/-- The public argument registers at the call targets of the table of one function are those
    of the one external entry `n`. -/
theorem CalleeTab.ctIfc_one (c : CalleeData) (n : Nat) :
    (CalleeTab.one c).ctIfc n = X86Backend.DecodedCTCall.extOne n c.pubRegs := by
  funext tg
  simp only [CalleeTab.ctIfc, CalleeTab.tgtPos?_one, X86Backend.DecodedCTCall.extOne]
  by_cases h : tg = n <;> simp [h, CalleeTab.one]

/-- The destinations at the call targets of the table of one function are its
    destination. -/
theorem CalleeTab.ctDst_one (c : CalleeData) (n : Nat) :
    (CalleeTab.one c).ctDst n = fun _ => c.outDst? := by
  funext tg
  simp only [CalleeTab.ctDst, CalleeTab.tgtPos?_one]
  by_cases h : tg = n <;> simp [h, CalleeTab.one]

/-- The clobber set of the table of one function is its clobber set. -/
theorem CalleeTab.clobB_one (c : CalleeData) :
    (CalleeTab.one c).clobB = fun x => c.clob.contains x := by
  funext x
  simp [CalleeTab.clobB, CalleeTab.one]

/-- The function a table finds at a symbol sits at the position of the symbol. -/
theorem CalleeTab.lookup_symPos {T : CalleeTab} {g : String} {c : CalleeData}
    (h : T.lookup g = some c) : T.fns[T.symPos g]? = some c := by
  have key : ∀ (l : List CalleeData), l.find? (·.name == g) = some c →
      ∃ i, l.findIdx? (·.name == g) = some i ∧ l[i]? = some c := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons a l ih =>
      by_cases ha : (a.name == g) = true
      · simp only [List.find?_cons, ha] at hl
        cases hl
        exact ⟨0, by simp [List.findIdx?_cons, ha], rfl⟩
      · simp only [List.find?_cons, ha] at hl
        obtain ⟨i, hi, hc⟩ := ih hl
        exact ⟨i + 1, by simp [List.findIdx?_cons, ha, hi], by simpa using hc⟩
  obtain ⟨i, hi, hc⟩ := key T.fns h
  simp [CalleeTab.symPos, hi, hc]

/-- A symbol of a table has a function, at the position of the symbol. -/
theorem CalleeTab.lookup_of_mem {T : CalleeTab} {g : String} (h : g ∈ T.names) :
    ∃ c, T.lookup g = some c := by
  have h1 := congrFun T.lookup_isSome g
  exact Option.isSome_iff_exists.mp (by rw [h1]; simpa using h)

/-- In a table with distinct symbols, the position of the symbol of the function at position
    `i` is `i`. -/
theorem CalleeTab.symPos_getElem {T : CalleeTab} (hnd : T.names.Nodup) {i : Nat}
    (hi : i < T.fns.length) : T.symPos T.fns[i].name = i := by
  obtain ⟨c, hc⟩ := T.lookup_of_mem (List.mem_map_of_mem (List.getElem_mem hi))
  have h1 := CalleeTab.lookup_symPos hc
  obtain ⟨hcm, hcn⟩ := CalleeTab.lookup_spec hc
  have hj : T.symPos T.fns[i].name < T.fns.length := (List.getElem?_eq_some_iff.mp h1).1
  have h2 : T.fns[T.symPos T.fns[i].name].name = T.fns[i].name := by
    rw [List.getElem?_eq_some_iff] at h1
    rw [h1.2, hcn]
  have hnd' : (T.fns.map (·.name)).Nodup := hnd
  refine (List.Nodup.getElem_inj_iff hnd' (hi := by simpa using hj)
    (hj := by simpa using hi)).mp ?_
  rw [List.getElem_map, List.getElem_map]
  exact h2

/-- With nonempty codes, the entry offsets of a table grow strictly with the position. -/
theorem CalleeTab.entryOff_lt {T : CalleeTab} (hne : ∀ c ∈ T.fns, c.bytes ≠ []) {i j : Nat}
    (hij : i < j) (hj : j ≤ T.fns.length) : T.entryOff i < T.entryOff j := by
  unfold CalleeTab.entryOff
  obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
  have hi : i < T.fns.length := by omega
  rw [List.take_add, List.flatMap_append, List.length_append,
    List.drop_eq_getElem_cons hi, List.take_succ_cons, List.flatMap_cons, List.length_append]
  have := List.length_pos_of_ne_nil (hne T.fns[i] (List.getElem_mem hi))
  omega

/-- With nonempty codes, distinct positions of a table have distinct entry offsets. -/
theorem CalleeTab.entryOff_inj {T : CalleeTab} (hne : ∀ c ∈ T.fns, c.bytes ≠ []) {i j : Nat}
    (hi : i ≤ T.fns.length) (hj : j ≤ T.fns.length) (h : T.entryOff i = T.entryOff j) :
    i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd h (Nat.ne_of_lt (T.entryOff_lt hne hij hj))
  · exact hij
  · exact absurd h.symm (Nat.ne_of_lt (T.entryOff_lt hne hij hi))

/-- **The entry indices of a table are distinct.** In a table with distinct symbols and
    nonempty codes whose code decodes as a region at its entry offsets and indices
    (`LprogBytesLinkReloc.RegionDecode`), distinct positions have distinct entry indices. -/
theorem CalleeTab.entryIdx_inj {T : CalleeTab} (hnd : T.names.Nodup)
    (hne : ∀ c ∈ T.fns, c.bytes ≠ []) {Q : List X86Backend.LprogBytesDecode.RInstr}
    (hR : X86Backend.LprogBytesLinkReloc.RegionDecode T.bytes T.names
      (fun g => T.entryOff (T.symPos g)) (fun g => T.entryIdx (T.symPos g)) Q)
    {i j : Nat} (hi : i < T.fns.length) (hj : j < T.fns.length)
    (h : T.entryIdx i = T.entryIdx j) : i = j := by
  have hpos : ∀ g ∈ T.names, T.symPos g < T.fns.length ∧ ∃ c, T.lookup g = some c
      ∧ T.fns[T.symPos g]? = some c := fun g hg => by
    obtain ⟨c, hc⟩ := T.lookup_of_mem hg
    have h1 := CalleeTab.lookup_symPos hc
    exact ⟨(List.getElem?_eq_some_iff.mp h1).1, c, hc, h1⟩
  have key := X86Backend.LprogBytesLinkReloc.regionDecode_inj hR (fun f hf g hg ho => by
    obtain ⟨hf1, c, hc, hc'⟩ := hpos f hf
    obtain ⟨hg1, d, hd, hd'⟩ := hpos g hg
    have he := T.entryOff_inj hne hf1.le hg1.le ho
    rw [he, hd'] at hc'
    cases hc'
    exact (CalleeTab.lookup_spec hc).2.symm.trans (CalleeTab.lookup_spec hd).2)
  have hmi : T.fns[i].name ∈ T.names := List.mem_map_of_mem (List.getElem_mem hi)
  have hmj : T.fns[j].name ∈ T.names := List.mem_map_of_mem (List.getElem_mem hj)
  have hn := key _ hmi _ hmj (by
    simp only [CalleeTab.symPos_getElem hnd hi, CalleeTab.symPos_getElem hnd hj]
    exact h)
  have hnd' : (T.fns.map (·.name)).Nodup := hnd
  refine (List.Nodup.getElem_inj_iff hnd' (hi := by simpa using hi)
    (hj := by simpa using hj)).mp ?_
  rw [List.getElem_map, List.getElem_map]
  exact hn

/-- At distinct entry indices, the call target behind a caller of `n` instructions at the
    entry of the function at position `i` is that position. -/
theorem CalleeTab.tgtPos?_entry {T : CalleeTab}
    (hinj : ∀ i < T.fns.length, ∀ j < T.fns.length, T.entryIdx i = T.entryIdx j → i = j)
    (n : Nat) {i : Nat} (hi : i < T.fns.length) : T.tgtPos? n (n + T.entryIdx i) = some i := by
  unfold CalleeTab.tgtPos?
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, by simpa using hi, by simp, fun j hj => ?_⟩
  have hjl : j < T.fns.length := by omega
  rw [Bool.not_eq_true', beq_eq_false_iff_ne]
  intro h
  exact absurd (hinj j hjl i hi (by simpa using h)) (by omega)

/-- At distinct entry indices, the public argument registers at the entry of the function of a
    symbol are those of the function. -/
theorem CalleeTab.ctIfc_entry {T : CalleeTab}
    (hinj : ∀ i < T.fns.length, ∀ j < T.fns.length, T.entryIdx i = T.entryIdx j → i = j)
    (n : Nat) {g : String} {c : CalleeData} (hc : T.lookup g = some c) :
    T.ctIfc n (n + T.entryIdx (T.symPos g)) = some c.pubRegs := by
  have h1 := CalleeTab.lookup_symPos hc
  have hlt := (List.getElem?_eq_some_iff.mp h1).1
  simp [CalleeTab.ctIfc, T.tgtPos?_entry hinj n hlt, h1]

/-- At distinct entry indices, the destination at the entry of the function of a symbol is
    that of the function. -/
theorem CalleeTab.ctDst_entry {T : CalleeTab}
    (hinj : ∀ i < T.fns.length, ∀ j < T.fns.length, T.entryIdx i = T.entryIdx j → i = j)
    (n : Nat) {g : String} {c : CalleeData} (hc : T.lookup g = some c) :
    T.ctDst n (n + T.entryIdx (T.symPos g)) = c.outDst? := by
  have h1 := CalleeTab.lookup_symPos hc
  have hlt := (List.getElem?_eq_some_iff.mp h1).1
  simp [CalleeTab.ctDst, T.tgtPos?_entry hinj n hlt, h1]

/-- A register outside the clobber set of a table is outside the clobber set of each of its
    functions. -/
theorem CalleeTab.clob_of_clobB {T : CalleeTab} {c : CalleeData} (hc : c ∈ T.fns) {x : String}
    (h : T.clobB x = false) : c.clob.contains x = false := by
  simp only [CalleeTab.clobB, List.any_eq_false] at h
  simpa using h c hc

/-- The interface of a table at the symbol of one of its functions is that of the function. -/
theorem CalleeTab.sigOf_lookup {T : CalleeTab} {g : String} {c : CalleeData}
    (hc : T.lookup g = some c) : T.sigOf g = c.sig := by
  simp [CalleeTab.sigOf, hc]

/-- **The constant-time check at an optional table**: `regionCtB` without a table. At a table
    `T`, the constant-time decision with calls of linked callees `AbiLayout.ctCheckRXT` on the
    program `calleeProg T body` of the function, at the clobber set `T.clobB`, the public
    argument registers `T.ctIfc` and the destinations `T.ctDst` at the call targets behind the
    program, and the frame `T.frame`; at the table of one function this is
    `AbiLayout.ctCheckRXO` at the data of that function (`calleeCtB_one`). `false` when the
    function has no program. -/
def calleeCtB (σ : AbiLayout) (nm : String → String) (callee : Option CalleeTab)
    (body : Lcmd) (t : JasminTy) (code : List LinstrRM) (res : List LOperand)
    (cert : List (String × String)) : Bool :=
  match callee with
  | none => regionCtB σ nm body t code res cert
  | some T =>
      match calleeProg T body with
      | some p => σ.ctCheckRXT T.clobB (T.ctIfc p.length) T.frame (T.ctDst p.length) p
      | none => false

/-- Without a table the constant-time check is `regionCtB`. -/
@[simp] theorem calleeCtB_none (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String)) :
    calleeCtB σ nm none body t code res cert = regionCtB σ nm body t code res cert := rfl

/-- **The constant-time check at the table of one linked function** is the decision at the data
    of that function: the interface of the table is that of the function
    (`CalleeTab.clobB_one`, `CalleeTab.ctIfc_one`, `CalleeTab.ctDst_one`). -/
theorem calleeCtB_one (σ : AbiLayout) (nm : String → String) (c : CalleeData) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String)) :
    calleeCtB σ nm (some (CalleeTab.one c)) body t code res cert =
      match calleeProg (CalleeTab.one c) body with
      | some p => σ.ctCheckRXO (fun x => c.clob.contains x) c.pubRegs c.frame c.outDst? p
      | none => false := by
  dsimp only [calleeCtB]
  cases calleeProg (CalleeTab.one c) body with
  | none => rfl
  | some p =>
      dsimp only
      rw [CalleeTab.clobB_one, CalleeTab.ctIfc_one, CalleeTab.ctDst_one, CalleeTab.frame_one]

/-- **The constant-time check at a table**: a table at which the check holds gives the program
    of the function, which passes `AbiLayout.ctCheckRXT` at the interface of the table. -/
theorem calleeCtB_tab {σ : AbiLayout} {nm : String → String} {T : CalleeTab} {body : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    (h : calleeCtB σ nm (some T) body t code res cert = true) :
    ∃ p, calleeProg T body = some p
      ∧ σ.ctCheckRXT T.clobB (T.ctIfc p.length) T.frame (T.ctDst p.length) p = true := by
  simp only [calleeCtB] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

/-- **The stages of the back half after the narrow-word stages**, on a program with one
    result, a word array or a
    register: the region legalisation `legalizeRegion`, then, on the legalised program, the test
    `regionExportableB` on a program without `call` (`NFProg.callFree`),
    the export `exportR`, its webs `regionWebsAt` at the result buffer
    `regionWebsEx σ exportReg`, the allocated program with its allocation certificate
    `regionLprogC`, the printed program `printedLprog`, the two-address gate on its first
    function body, the gated encoder, and the gate on the printed body: the check
    `regionCoB` of the reference of the webs against it at the certificate and the
    constant-time check `regionCtB`; the printed program and the bytes, or `none` when a
    stage declines or a check refuses.

    A program with a `call` is compiled when `regionCallee` finds its callee among the
    linked functions `linked`: every stage is then taken at that callee (the webs at the
    array positions and result lengths of its symbols, the allocation `calleeAlloc`, the gate
    `regionCoB` with its two conjuncts on a calling body, the bytes `calleeBytes` of the
    function followed by the code of the callee, and `calleeCtB`, the constant-time decision
    with a call on the program of the function). The two arms run the same stages; without a
    callee each stage is taken at no table. The result of a calling body is gated and is
    covered by no correctness theorem: `regionBack_spec` and `regionBack_correct` are
    stated at no linked function, where the program has no `call`. Without linked functions,
    and on every program without `call` (`regionBack_of_callFree`), the stages are those of
    the first paragraph. -/
def regionBack (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (linked : List CalleeData := []) :
    Option (Lprog × List (BitVec 8)) :=
  if regionExportableB (legalizeRegion p) = true then
    match exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 with
    | some r0 =>
        match regionCallee linked (legalizeRegion p) r0.code with
        | some callee =>
            let r := regionWebsAt (regionWebsEx σ exportReg) callee r0
            match regionLprogC a (legalizeRegion p) callee (regionWebsEx σ exportReg) with
            | some (P, cert) =>
                regionEncode P (fun b =>
                    regionCoB σ exportReg b t r.code r.res cert callee a.fname
                      && calleeCtB σ exportReg callee b t r.code r.res cert)
                  callee
            | none => none
        | none => none
    | none => none
  else none

/-- The public relation of the bytes of the legalised program is that of the program. -/
theorem regionBytePub_legalizeRegion (σ : AbiLayout) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) (L : Labels Γ) (Pre : AState → Prop) :
    RegionBytePub σ fuel (legalizeRegion p) L Pre = RegionBytePub σ fuel p L Pre := by
  unfold RegionBytePub
  simp only [legalizeRegion_denoteAt]

/-- **On a program without `call` the back half does not read the linked functions.** -/
theorem regionBack_of_callFree (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} (h : p.callFree = true)
    (linked : List CalleeData) : regionBack σ a p linked = regionBack σ a p := by
  unfold regionBack
  simp only [regionCallee_of_callFree (legalizeRegion_callFree h)]

/-- Every result of `regionBack` on `p` comes from a legalised program `legalizeRegion p`
    that passes `regionExportableB`, with an export `r0`, its webs `r` at the result buffer
    `regionWebsEx σ exportReg`, and a printed body whose gated encoder's bytes are the
    result's bytes, and an allocation certificate `cert` of `regionLprogC`, such that the
    webs pass `regionCoB` against the printed body at `cert` and the printed body passes the
    constant-time check `regionCtB` at `cert`. -/
theorem regionBack_spec {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p = some (P, bytes)) :
    regionExportableB (legalizeRegion p) = true ∧ ∃ r0 r b cert,
      exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 = some r0
      ∧ r = regionWebsAt (regionWebsEx σ exportReg) none r0
      ∧ X86Backend.LprogBytes.encodeLfundefBytesChecked b = some bytes
      ∧ regionCoB σ exportReg b t r.code r.res cert = true
      ∧ regionCtB σ exportReg b t r.code r.res cert = true
      ∧ ∃ P0, regionLprogC a (legalizeRegion p) none (regionWebsEx σ exportReg)
        = some (P0, cert) := by
  unfold regionBack at h
  split at h
  · rename_i hB
    split at h
    · rename_i r hr
      split at h
      · rename_i callee hc
        obtain rfl := regionCallee_nil hc
        split at h
        · rename_i P0 cert hP
          obtain ⟨b, hbs, hg⟩ := regionEncode_spec h
          rw [Bool.and_eq_true] at hg
          refine ⟨hB, r, _, b, cert, hr, rfl, hbs, ?_, hg.2, P0, hP⟩
          rw [← regionCoB_none_fn σ exportReg b t _ _ cert a.fname]
          exact hg.1
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Correctness of the back half on a region-exported program.** For a result
    `(P, bytes)` of `regionBack σ a p`: from every entry state `sa` satisfying
    `σ.Regions`, at every valuation `V` that `σ` reads off `sa` at which `p` denotes `v` at
    some fuel, the bytes decode to a program that halts on the machine from `sa` in a state
    `sa'` from which `σ` reads back the source value of the result, a word array or a
    register. The stack register of `sa'` holds its value in `sa`, and the memory of `sa'`
    agrees with that of `sa` at every byte outside the stack words `%rsp + o`,
    `frameLo ≤ o ≤ frameHi`, and outside the words of each pointer region of `σ`, at the
    registers of `sa`; some run of the address machine on a body from `entryA σ sa` halts
    and stores to and loads from `layoutMem σ sa` only. -/
theorem regionBack_correct {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p = some (P, bytes))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  obtain ⟨hB, r0, r, b, cert, hr, rfl, hb, hco, -⟩ := regionBack_spec h
  rw [← legalizeRegion_denote] at hv
  obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, hA⟩ :=
    regionCo_bytes_of_regionExp (regionExportableB_sound hB) (regionExp_webs _ hr) hco sa V hV
      hreg fuel hv
  exact ⟨prog, sa', by rw [X86Backend.LprogBytes.encodeLfundefBytesChecked_eq hb]; exact hd,
    hh, hR, hsp, hkeep, b, hA⟩

/-! ## 11b. The narrow-word stages and the region back half -/

/-- The array types of narrow words: a stack array of `8`-, `16`- or `32`-bit words. -/
def narrowArrB : JasminTy → Bool
  | .stackArr w _ => VIR.NarrowWords.narrowB w
  | _ => false

/-- **The value of a widened result is the value of the result** at every type other than an
    array of narrow words: a register keeps its natural number under zero extension, and the
    widening fixes every other type. -/
theorem denVal_wideTy_transTy {t : JasminTy} (ht : narrowArrB t = false) (x : ⟦t⟧) :
    denVal (VIR.NarrowWords.wideTy t) (VIR.NarrowWords.transTy x) = denVal t x := by
  cases t with
  | reg w =>
      simp only [VIR.NarrowWords.wideTy, VIR.NarrowWords.transTy, denVal, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right (by decide) (VIR.NarrowWords.le_wideW w)))]
  | stackArr w n =>
      have hw : VIR.NarrowWords.wideW w = w := VIR.NarrowWords.wideW_of_not ht
      have he : VIR.NarrowWords.wideTy (.stackArr w n) = .stackArr w n := by
        show JasminTy.stackArr (VIR.NarrowWords.wideW w) n = _
        rw [hw]
      have key : ∀ (t' : JasminTy) (e : t' = .stackArr w n) (y : ⟦t'⟧), y ≍ x →
          denVal t' y = denVal (.stackArr w n) x := by
        intro t' e
        subst e
        intro y hy
        obtain rfl := eq_of_heq hy
        rfl
      exact key _ he _ (VIR.NarrowWords.transTy_heq_of_wide he x)
  | inlineInt => rfl
  | bool => rfl

/-- The parameter index of a variable is that of the variable under one more binding. -/
private theorem exportCertArgIdx_there {Γ : Ctxt jasminDialect} {s t : JasminTy}
    (v : Ctxt.Var Γ t) :
    X86Backend.ExportCertEntry.argIdx (Ctxt.Var.there (s := s) v) =
      X86Backend.ExportCertEntry.argIdx v := by
  have := VIR.JasminLsemSimulation.varIndex_lt v
  simp only [X86Backend.ExportCertEntry.argIdx, List.length_cons, varIndex] at this ⊢
  omega

/-- The ABI reading of a valuation of a longer context reads its tail. -/
theorem abiValOf_tail {σ : AbiLayout} {sa : AState} {Γ : Ctxt jasminDialect} {s : JasminTy}
    {x : ⟦s⟧} {V : Ctxt.Valuation Γ}
    (h : AbiValOf σ sa (Γ := s :: Γ) (.cons x V)) : AbiValOf σ sa V :=
  ⟨fun v => by
      have hv := h.arg (Ctxt.Var.there (s := s) v)
      rw [exportCertArgIdx_there] at hv
      exact hv,
    fun v => by
      have hv := h.reg (Ctxt.Var.there (s := s) v)
      rw [exportCertArgIdx_there] at hv
      exact hv,
    fun v => by
      have hv := h.arr (Ctxt.Var.there (s := s) v)
      rw [exportCertArgIdx_there] at hv
      exact hv⟩

/-- **A context the layout reads holds 64-bit words only**: the widening fixes it. -/
theorem map_wideTy_of_abiValOf {σ : AbiLayout} {sa : AState} :
    {Γ : Ctxt jasminDialect} → (V : Ctxt.Valuation Γ) → AbiValOf σ sa V →
      Γ.map VIR.NarrowWords.wideTy = Γ
  | [], _, _ => rfl
  | s :: Γ, .cons x V, h => by
      have ht : VIR.NarrowWords.wideTy s = s := by
        cases s with
        | reg w =>
            obtain ⟨_, -, -, rfl, -⟩ := h.reg (Ctxt.Var.here (Γ := Γ))
            rfl
        | stackArr w n =>
            obtain ⟨_, -, -, rfl, -⟩ := h.arr (Ctxt.Var.here (Γ := Γ))
            rfl
        | inlineInt => rfl
        | bool => rfl
      show VIR.NarrowWords.wideTy s :: Γ.map VIR.NarrowWords.wideTy = s :: Γ
      rw [ht, map_wideTy_of_abiValOf V (abiValOf_tail h)]

/-- **The ABI reading of the widened valuation.** A valuation the layout reads off a state is
    a valuation of 64-bit words, so its widening is read off the same state. -/
theorem abiValOf_widen {σ : AbiLayout} {sa : AState} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} (h : AbiValOf σ sa V) : AbiValOf σ sa (VIR.NarrowWords.mapVal V) := by
  have hΓ := map_wideTy_of_abiValOf V h
  have key : ∀ {Γ' : Ctxt jasminDialect} (_ : Γ' = Γ) (W : Ctxt.Valuation Γ'), W ≍ V →
      AbiValOf σ sa W := by
    intro Γ' e
    subst e
    intro W hW
    obtain rfl := eq_of_heq hW
    exact h
  exact key hΓ _ (VIR.NarrowWords.mapVal_heq_of_wide hΓ V)

/-- **The region back half** on a structured program with one result: the gate
    `regionExportableB` on the program; the narrow-word stages `narrowPrep`, which hold every
    word of a width `8`, `16` or `32` zero extended in a 64-bit register or a 64-bit array
    slot (`widenJ`), remove the masks whose value reaches only width-insensitive operations
    (`maskElim`) and the dead bindings (`NFProg.dce`); then the stages `regionBack` on the
    widened program, over the context `Γ.map wideTy`, at the linked functions `linked`.
    `none` when a stage declines or a check refuses. A caller passes a narrow argument in a
    64-bit slot with zero high bits: the valuation it provides is `mapVal V`. -/
def compileRegion (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (linked : List CalleeData := []) :
    Option (Lprog × List (BitVec 8)) :=
  if regionExportableB p = true then
    (VIR.NarrowWords.narrowPrep p).bind fun q => regionBack σ a q linked
  else none

/-- A result of `compileRegion` is a result of `regionBack` on the widened program of a
    program that passes the gate. -/
theorem compileRegion_eq_some {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData}
    {out : Lprog × List (BitVec 8)} :
    compileRegion σ a p linked = some out ↔ regionExportableB p = true ∧
      ∃ q, VIR.NarrowWords.narrowPrep p = some q ∧ regionBack σ a q linked = some out := by
  unfold compileRegion
  by_cases h : regionExportableB p = true
  · simp only [h, ite_true, true_and, Option.bind_eq_some_iff]
  · simp only [h, Bool.false_eq_true, ite_false, reduceCtorEq, false_and]

/-- **On a program without `call` the back half does not read the linked functions.** -/
theorem compileRegion_of_callFree (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} (h : p.callFree = true)
    (linked : List CalleeData) : compileRegion σ a p linked = compileRegion σ a p := by
  unfold compileRegion
  split
  · cases hq : VIR.NarrowWords.narrowPrep p with
    | none => rfl
    | some q =>
        simp only [Option.bind_some]
        exact regionBack_of_callFree σ a ((VIR.NarrowWords.callFree_narrowPrep hq).trans h)
          linked
  · rfl

/-- **The specification of the back half**: every result of `compileRegion` on `p` comes from
    a program that passes `regionExportableB`, whose narrow-word stages return a program `q`
    over `Γ.map wideTy` on which the stages of `regionBack` run as `regionBack_spec` states:
    `q` passes `regionExportableB`, with an export `r0`, its webs `r`, a printed body whose
    gated encoder's bytes are the result's bytes, and an allocation certificate `cert`, the
    webs passing `regionCoB` and the body passing `regionCtB` at `cert`. -/
theorem compileRegion_spec {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p = some (P, bytes)) :
    regionExportableB p = true ∧ ∃ q, VIR.NarrowWords.narrowPrep p = some q
      ∧ regionExportableB (legalizeRegion q) = true ∧ ∃ r0 r b cert,
        exportR Γ.length a.fname (legalizeRegion q) Γ.length 0 = some r0
        ∧ r = regionWebsAt (regionWebsEx σ exportReg) none r0
        ∧ X86Backend.LprogBytes.encodeLfundefBytesChecked b = some bytes
        ∧ regionCoB σ exportReg b (VIR.NarrowWords.wideTy t) r.code r.res cert = true
        ∧ regionCtB σ exportReg b (VIR.NarrowWords.wideTy t) r.code r.res cert = true
        ∧ ∃ P0, regionLprogC a (legalizeRegion q) none (regionWebsEx σ exportReg)
          = some (P0, cert) := by
  obtain ⟨hB, q, hq, hb⟩ := compileRegion_eq_some.mp h
  have hs := regionBack_spec hb
  rw [List.length_map] at hs
  exact ⟨hB, q, hq, hs⟩

/-- **Correctness of the back half.** For a result `(P, bytes)` of `compileRegion σ a p`: from
    every entry state `sa` satisfying `σ.Regions` at which `σ` reads the widened valuation
    `mapVal V` (each narrow argument in a 64-bit slot with zero high bits), at every `V` at
    which `p` denotes `v` at some fuel, the bytes decode to a program that halts on the
    machine from `sa` in a state `sa'` from which `σ` reads back the widened result. The stack
    register of `sa'` holds its value in `sa`, and the memory of `sa'` agrees with that of
    `sa` at every byte outside the stack words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and outside
    the words of each pointer region of `σ`, at the registers of `sa`; some run of the address
    machine on a body from `entryA σ sa` halts and stores to and loads from `layoutMem σ sa`
    only. -/
theorem compileRegion_correct {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p = some (P, bytes))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa (VIR.NarrowWords.mapVal V))
    (hreg : σ.Regions sa) (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal (VIR.NarrowWords.wideTy t) (VIR.NarrowWords.transTy
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  obtain ⟨-, q, hq, hb⟩ := compileRegion_eq_some.mp h
  have hw := VIR.NarrowWords.narrowPrep_denote hq hv
  cases v with
  | cons x xs =>
      cases xs
      exact regionBack_correct hb sa (VIR.NarrowWords.mapVal V) hV hreg fuel hw

/-- **Correctness of the back half on 64-bit arguments**, the statement of `regionBack_correct`
    for `compileRegion`: at a valuation `V` that `σ` reads off `sa` (whose context then holds
    64-bit words only, `abiValOf_widen`) and a result type other than an array of narrow
    words (`denVal_wideTy_transTy`), `σ` reads back the source value of the result. -/
theorem compileRegion_correct_wide {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p = some (P, bytes))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) (hn : narrowArrB t = false := by decide) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  rw [← denVal_wideTy_transTy hn]
  exact compileRegion_correct h sa V (abiValOf_widen hV) hreg fuel hv

/-- **Over a context and result type of 64-bit words, the back half runs on a program that
    denotes as the source.** When `wideTy` fixes the context and the result type of `p`, a
    result of `compileRegion` on `p` is a result of `regionBack` on the widened program carried
    back to them, `castProg hΓ ht q`, which denotes what `p` denotes
    (`NarrowWords.narrowPrep_cast_denote`), is constant time where `p` is
    (`NarrowWords.narrowPrep_cast_nfct`) and has the calls of `p`
    (`NarrowWords.narrowPrep_cast_callFree`). -/
theorem compileRegion_wide {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData}
    {out : Lprog × List (BitVec 8)} (hΓ : Γ.map VIR.NarrowWords.wideTy = Γ)
    (ht : [t].map VIR.NarrowWords.wideTy = [t]) (h : compileRegion σ a p linked = some out) :
    regionExportableB p = true ∧ ∃ q, VIR.NarrowWords.narrowPrep p = some q
      ∧ regionBack σ a (VIR.NarrowWords.castProg hΓ ht q) linked = some out := by
  obtain ⟨hB, q, hq, hb⟩ := compileRegion_eq_some.mp h
  refine ⟨hB, q, hq, ?_⟩
  have key : ∀ {Γ' : Ctxt jasminDialect} {t' : JasminTy} (e₁ : Γ' = Γ) (e₂ : [t'] = [t])
      (r : NFProg jasminDialect Γ' [t']),
      regionBack σ a (VIR.NarrowWords.castProg e₁ e₂ r) linked = regionBack σ a r linked := by
    intro Γ' t' e₁ e₂ r
    subst e₁
    obtain rfl : t' = t := (List.cons.inj e₂).1
    rfl
  rw [key hΓ ht q]
  exact hb

/-- **Over a context of 64-bit words, the back half runs on a program that denotes the widened
    source.** When `wideTy` fixes the context of `p`, a result of `compileRegion` on `p` is a
    result of `regionBack` on the widened program carried back to the context of `p`,
    `castProg hΓ rfl q`, which has the calls of `p` and denotes, at every call environment, the
    widened denotation of `p` (`NarrowWords.narrowPrep_castCtx_denoteAt`). -/
theorem compileRegion_ctx {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData}
    {out : Lprog × List (BitVec 8)} (hΓ : Γ.map VIR.NarrowWords.wideTy = Γ)
    (h : compileRegion σ a p linked = some out) :
    regionExportableB p = true ∧ ∃ q, VIR.NarrowWords.narrowPrep p = some q
      ∧ regionBack σ a (VIR.NarrowWords.castProg hΓ rfl q) linked = some out
      ∧ (VIR.NarrowWords.castProg hΓ rfl q).callFree = p.callFree
      ∧ ∀ (E : CallEnv jasminDialect) (fuel : Nat) (V : Ctxt.Valuation Γ),
        (VIR.NarrowWords.castProg hΓ rfl q).denoteAt E fuel V = (p.denoteAt E fuel V).map
          (BlockLoweringExtend.transArgs VIR.NarrowWords.wideTy
            (fun x => VIR.NarrowWords.transTy x)) := by
  obtain ⟨hB, q, hq, hb⟩ := compileRegion_eq_some.mp h
  have key : ∀ {Γ' : Ctxt jasminDialect} {t' : JasminTy} (e₁ : Γ' = Γ)
      (r : NFProg jasminDialect Γ' [t']),
      regionBack σ a (VIR.NarrowWords.castProg e₁ rfl r) linked = regionBack σ a r linked ∧
        (VIR.NarrowWords.castProg e₁ rfl r).callFree = r.callFree := by
    intro Γ' t' e₁ r
    subst e₁
    exact ⟨rfl, rfl⟩
  refine ⟨hB, q, hq, (key hΓ q).1.trans hb,
    (key hΓ q).2.trans (VIR.NarrowWords.callFree_narrowPrep hq), fun E fuel V =>
    VIR.NarrowWords.narrowPrep_castCtx_denoteAt E hΓ hB hq fuel V⟩

/-! ## 12. The bytes of a calling body -/

/-- The functions of the table `regionCallee` finds are among the linked functions. -/
theorem regionCallee_mem {linked : List CalleeData} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {code : List LinstrRM} {T : CalleeTab}
    (h : regionCallee linked p code = some (some T)) : ∀ c ∈ T.fns, c ∈ linked :=
  fun _ hc => (regionCallee_sublist h).subset hc

/-- A program for which `regionCallee` finds no callee has no `call`. -/
theorem regionCallee_callFree {linked : List CalleeData} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {code : List LinstrRM}
    (h : regionCallee linked p code = some none) : p.callFree = true := by
  unfold regionCallee at h
  split at h
  · assumption
  · split at h
    · split at h
      · simp at h
      · cases h
    · cases h

/-- A result of `regionEncode` at an optional table has a printed body whose bytes at that
    table (`calleeBytes`) are the result's bytes and that passes the gate. -/
theorem regionEncode_spec_callee {P : Lprog} {gate : Lcmd → Bool}
    {callee : Option CalleeTab} {out : Lprog × List (BitVec 8)}
    (h : regionEncode P gate callee = some out) :
    ∃ b, calleeBytes callee b = some out.2 ∧ gate b = true := by
  unfold regionEncode at h
  split at h
  · split at h
    · rename_i hbs
      split at h
      · rename_i hg
        obtain rfl := Option.some.inj h
        exact ⟨_, hbs, hg⟩
      · cases h
    · cases h
  · cases h

/-- **Two conjuncts of the gate at a table**: a body that passes `regionCoB` at a table
    `T` is of the class `ImageAddrCallW.printedAddrCWB` at the frame of `T`, and a block the
    code of a function of `T` decodes to has no `call`. -/
theorem regionCoB_callee {σ : AbiLayout} {nm : String → String} {body : Lcmd} {t : JasminTy}
    {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    {T : CalleeTab} {fn : String} (h : regionCoB σ nm body t code res cert (some T) fn = true) :
    X86Backend.ImageAddrCallW.printedAddrCWB T.frame body = true
      ∧ ∀ c ∈ T.fns, ∀ q, decodeLprog c.bytes = some q →
        ∀ tg, X86Backend.LprogBytesDecode.RInstr.call tg ∉ q := by
  simp only [regionCoB, renImageB, Option.all_some, Bool.and_eq_true] at h
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, himg⟩, -⟩, -⟩, -⟩, -⟩⟩⟩ := h
  exact ⟨(calleeImgBT_some himg).2.2.1, fun c hc q hq =>
    (X86Backend.Callee.keepCheckAtB_sound (calleeCodeBT_keep (calleeBodyBT_spec.mp hb).code hc
      hq)).1⟩

/-- **The target map of the symbols of a table as the target map of a region**: at each call of
    the items of a relocated function `b` whose remote symbols lie in `fs`, the target map
    `CalleeTab.linkMap` is the target map `LprogBytesLinkReloc.regionTgt` of the region of
    `fs` at the entry offsets and indices of the functions of the table. -/
theorem symTgt_linkMap_regionTgt (T : CalleeTab) (symBase : String → Option Int)
    (P : X86Backend.LprogBytesDecode.Params) (b : Lcmd) (ds : List X86Backend.PhysAbiShape.DShape)
    {fs : List String} (hs : X86Backend.DecodeGen.shapesOf P b = some ds)
    (hfs : ∀ i ∈ b, ∀ f, X86Backend.LprogBytes.remoteSym i.li_i = some f → f ∈ fs)
    (n L : Nat) :
    ∀ it ∈ X86Backend.LprogBytesLinkReloc.fundefItemsRelocL symBase P b ds, it.target = none →
      ∀ d, it.dec = some (.call d) →
        X86Backend.LprogBytesLinkReloc.symTgt (T.linkMap n L) it
          = X86Backend.LprogBytesLinkReloc.symTgt (X86Backend.LprogBytesLinkReloc.regionTgt fs
              n L (fun g => T.entryOff (T.symPos g)) (fun g => T.entryIdx (T.symPos g))) it := by
  intro it hit ht d hd
  obtain ⟨f, hf, i, hi, hr⟩ :=
    X86Backend.LprogBytesLinkReloc.fundefItemsRelocL_sym symBase P b ds hs it hit ht d hd
  simp [X86Backend.LprogBytesLinkReloc.symTgt, hf, X86Backend.LprogBytesLinkReloc.regionTgt,
    hfs i hi f hr, CalleeTab.linkMap]

/-- **The bytes of a calling body at a table.** Let the bytes `calleeBytes` at the table `T` of
    a body `b` of the class `ImageAddrCallW.printedAddrCWB` at the frame of `T` be `bytes`, let
    every remote symbol of `b` lie in `fs`, and let the code of `T` decode in one pass to `Q`
    with the entry of each symbol of `fs` at the byte offset and the index of the entry of its
    function (`LprogBytesLinkReloc.RegionDecode`). Then the bytes decode to the program
    `calleeProg T b` of the function followed by `Q` with its targets raised by the length of
    the program (`LprogBytesLinkReloc.linkedProg_of_bytesSymL`). -/
theorem calleeBytes_decode {T : CalleeTab} {b : Lcmd} {bytes : List (BitVec 8)}
    (h : calleeBytes (some T) b = some bytes)
    (hpr : X86Backend.ImageAddrCallW.printedAddrCWB T.frame b = true) {fs : List String}
    (hfs : ∀ i ∈ b, ∀ f, X86Backend.LprogBytes.remoteSym i.li_i = some f → f ∈ fs)
    {Q : List X86Backend.LprogBytesDecode.RInstr}
    (hR : X86Backend.LprogBytesLinkReloc.RegionDecode T.bytes fs
      (fun g => T.entryOff (T.symPos g)) (fun g => T.entryIdx (T.symPos g)) Q) :
    ∃ pr, calleeProg T b = some pr
      ∧ decodeLprog bytes = some (pr ++ X86Backend.LprogBytesLink.shiftProg pr.length Q) := by
  simp only [calleeBytes] at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    simp only [calleeLinkB, Bool.and_eq_true] at hc
    obtain ⟨-, hm⟩ := hc
    unfold calleeProg
    cases hss : X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b with
    | none => simp only [hss] at hm; cases hm
    | some ds =>
      simp only [hss, Bool.and_eq_true] at hm ⊢
      obtain ⟨hbr, hP⟩ := hm
      obtain ⟨pr, hpr'⟩ := Option.isSome_iff_exists.mp hP
      refine ⟨pr, hpr', ?_⟩
      have hag := symTgt_linkMap_regionTgt T (calleeSym T b)
        (X86Backend.LprogBytesDecode.Params.ofBody b) b ds hss hfs
      rw [X86Backend.LprogBytesLinkReloc.branchOKRelocMap_congr _ _ (hag _ _)] at hbr
      rw [X86Backend.LprogBytesLinkReloc.expectedRelocMap_congr _ _ (hag _ _)] at hpr'
      obtain ⟨hsaves, hF0, hFr⟩ := X86Backend.ImageAddrCallW.printedAddrCWB_reloc hpr
      exact (X86Backend.LprogBytesLinkReloc.linkedProg_of_bytesSymL (calleeSym T b)
        (X86Backend.ImageAddrCallW.callFacts_of_printedAddrCWB hpr hss).toLinkFacts T.bytes fs
        _ _ Q pr hsaves hF0 hFr hR hbr hpr').1
  · cases h

/-- **The bytes of a calling body at one linked function.** The bytes `calleeBytes` at the table
    of one linked function `c` of a body `b` of the class `ImageAddrCallW.printedAddrCWB`
    decode to the program `calleeProg (CalleeTab.one c) b` of the function followed by the
    code `q` of `c` with its targets raised by the length of the program: `calleeBytes_decode`
    at the region of one block (`LprogBytesLinkReloc.regionDecode_one`). -/
theorem calleeBytes_decode_one {c : CalleeData} {b : Lcmd} {bytes : List (BitVec 8)}
    (h : calleeBytes (some (CalleeTab.one c)) b = some bytes)
    (hpr : X86Backend.ImageAddrCallW.printedAddrCWB c.frame b = true)
    {q : List X86Backend.LprogBytesDecode.RInstr} (hq : decodeLprog c.bytes = some q) :
    ∃ pr, calleeProg (CalleeTab.one c) b = some pr
      ∧ decodeLprog bytes = some (pr ++ X86Backend.LprogBytesLink.shiftProg pr.length q) := by
  have hne : c.bytes ≠ [] := by
    simp only [calleeBytes] at h
    split at h
    · rename_i hc
      simp only [calleeLinkB_one, Bool.and_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff] at hc
      exact hc.1
    · cases h
  have hR := X86Backend.LprogBytesLinkReloc.regionDecode_one c.bytes q
    (b.filterMap fun i => X86Backend.LprogBytes.remoteSym i.li_i) hq hne
  exact calleeBytes_decode h (by rwa [CalleeTab.frame_one])
    (fun i hi f hf => List.mem_filterMap.mpr ⟨i, hi, hf⟩)
    (by simpa [CalleeTab.bytes_one] using hR)

end CatCrypt.Crypto.SecureCompilation.Haxc
