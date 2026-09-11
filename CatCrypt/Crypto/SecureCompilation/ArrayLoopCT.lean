/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTCTAnalysis

/-!
# Runtime-indexed array loops are constant-time on a public index

The runtime-indexed array constructors `RArrLoad`/`RArrStore` already carry the
**public-index discipline** in the CT analysis: `cmdCT` requires the index slot
(and the array/dest slots) to be `Public` (`cmdCT_RArrLoad`/`cmdCT_RArrStore`).
A data-dependent (secret-indexed) array access is the canonical constant-time
violation — a secret index leaks via the address trace — so the analysis is
*right* to demand a public index, and `cmdCT_sound` turns `cmdCT = true` into
genuine noninterference (Public-equivalent inputs ⇒ Public-equivalent outputs).

This file composes those facts into the end-to-end statement for the
**NTT / coefficient-loop pattern**: a `for i in 0..n { dst[i] := f(src[i]) }`
loop whose index is the (public) loop counter is constant-time by construction.
This is exactly the access shape lattice/FRI kernels need; the public-index
side-condition is what distinguishes it from a *secret*-indexed table lookup
(the AES S-box class), which the same `cmdCT` correctly rejects.

The value-correctness companion lives on the machine side
(`byteOffsetLeafSpec`, `lowerMemLoad_denote`/`lowerMemStore_denote_cell` in
`X86Backend/LowCTMemDenote.lean`); here the concern is the leakage / robust-CT
axis.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCT

/-- The NTT / coefficient-loop body: load element `i` of `src` into `t`, store
    `t` into element `i` of `dst`.  The index is the loop counter `"i"`. -/
def arrMapBody (src dst t : Located) : LowCT :=
  .RSeq (.RArrLoad t src "i") (.RArrStore dst "i" t)

/-- **The public-indexed array loop is constant-time by construction.**
    When the loop counter `"i"`, the source/dest arrays, and the temp all sit
    at `Public`, the runtime-indexed array-map loop passes the CT analysis. -/
theorem arrMapLoop_isCT (src dst t : Located) (n : Nat)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (hi : lt "i" = .Public) (hsrc : lt src.locVar = .Public)
    (hdst : lt dst.locVar = .Public) (ht : lt t.locVar = .Public) :
    cmdCT (.RFor "i" n (arrMapBody src dst t)) lt leafCT = true := by
  simp only [arrMapBody, cmdCT_RFor, cmdCT_RSeq, cmdCT_RArrLoad, cmdCT_RArrStore,
    hi, hsrc, hdst, ht]
  decide

/-- **Robust-CT capstone: the public-indexed array loop is noninterferent.**
    Two executions from `Public`-equivalent initial states reach
    `Public`-equivalent final states — i.e. the runtime-indexed array-map loop
    leaks nothing about secret inputs (constant-time), given the public-index
    discipline.  A direct consequence of `arrMapLoop_isCT` and `cmdCT_sound`. -/
theorem arrMapLoop_noninterference (src dst t : Located) (n : Nat)
    (lt : LevelTable) (leafCT : LeafCTTable) (leafSpec : LeafSpec) (N : Nat)
    (hi : lt "i" = .Public) (hsrc : lt src.locVar = .Public)
    (hdst : lt dst.locVar = .Public) (ht : lt t.locVar = .Public)
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCMOV : CMOVInvariant (.RFor "i" n (arrMapBody src dst t)))
    (rs1 rs2 rs1' rs2' : RustState)
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RFor "i" n (arrMapBody src dst t)) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RFor "i" n (arrMapBody src dst t)) rs2 rs2') :
    PublicEquiv lt rs1' rs2' :=
  cmdCT_sound (.RFor "i" n (arrMapBody src dst t)) lt leafCT leafSpec N
    (arrMapLoop_isCT src dst t n lt leafCT hi hsrc hdst ht) hLeaf hCMOV
    rs1 rs2 rs1' rs2' hEq hExec1 hExec2

end CatCrypt.Crypto.Jasmin.LowCT
