/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# Memory-safety theorems for X25519 ladder step bodies

This file mirrors the X25519 half-step + four full-step bodies of
`X25519BenchEmit.lean`, but authors the bodies as direct
`LowCT` constructor terms (no DSL) — and proves a `_memory_safe`
corollary for each, following the pattern of
`mulBody_memory_safe` / `montUToEdwardsBody_memory_safe` /
`xeddsaVerifyBody_memory_safe`.

The DSL version in `X25519BenchEmit.lean` cannot be the proof target
because that file imports `LowCTToMLIR`/`LowCTDSL`, whose pattern
matches predate the `RBytesSlice` / `RScalarSetExpr` /
`RArrLoad` / `RArrStore` constructors (build-blocked at the time of
writing).  Authoring the bodies as flat `LowCT` AST values keeps
this file independent of those modules — the only import we need is
`EmittedASTCorrectness` (which provides `AllSlotsBoundAt`,
`rcall_AllSlots`, the `memory_safe` alias, etc.).

The bodies below are PROVABLY equal to the DSL ones up to
`decide`-reduction, so once the DSL build is fixed a one-line
`by decide` lemma can pin the two together.

## Bodies covered

  * `halfstepBodyDirect`   — 5 RCalls (one Montgomery half-step).
  * `fullstepX2BodyDirect` — 5 RCalls (computes x2' of full-step).
  * `fullstepZ2BodyDirect` — 8 RCalls (computes z2').
  * `fullstepX3BodyDirect` — 8 RCalls (computes x3').
  * `fullstepZ3BodyDirect` — 9 RCalls (computes z3').

All slots are `TFp25519`.  No `RLetZero` / `RFor` / arrays — each body
is a pure `RSeq` chain of `RCall`s, so memory safety reduces to a
sequence of `rcall_AllSlots` applications on a flat slot list.
-/
import CatCrypt.Crypto.Jasmin.LowCT
import CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness

namespace CatCrypt.Crypto.Jasmin.Examples.X25519StepBodiesSafety

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness

/-! ## §1.  Slot helper -/

/-- A `TFp25519` slot at the given variable name. -/
private def fp (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TFp25519 }

/-! ## §2.  Half-step body

Single Montgomery-ladder body producing
`x2p = (x2+z2)² · (x2-z2)²`. Five field operations: add, sub,
sqr, sqr, mul. -/

/-- Half-step body as a flat `LowCT` value. -/
def halfstepBodyDirect : LowCT :=
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "A") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "B") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sqr" (fp "AA") [fp "A"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sqr" (fp "BB") [fp "B"])
    (LowCT.RCall "fp_mul" (fp "x2p") [fp "AA", fp "BB"])

/-! ## §3.  Full-step bodies (four single-output entries)

Each function recomputes any shared work; VIR is single-return per
`func.func`, and `func.call` is opaque to LLVM CSE, so the four bodies
do not share intermediates. -/

/-- Compute `x2p = (x2+z2)² · (x2-z2)²`. -/
def fullstepX2BodyDirect : LowCT :=
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "A") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "B") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sqr" (fp "AA") [fp "A"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sqr" (fp "BB") [fp "B"])
    (LowCT.RCall "fp_mul" (fp "x2p") [fp "AA", fp "BB"])

/-- Compute `z2p = E · (BB + 121666·E)`. -/
def fullstepZ2BodyDirect : LowCT :=
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "A") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "B") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sqr" (fp "AA") [fp "A"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sqr" (fp "BB") [fp "B"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "E") [fp "AA", fp "BB"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_mul_a24" (fp "a24E") [fp "E"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "inn") [fp "BB", fp "a24E"])
    (LowCT.RCall "fp_mul" (fp "z2p") [fp "E", fp "inn"])

/-- Compute `x3p = (DA + CB)²`. -/
def fullstepX3BodyDirect : LowCT :=
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "A") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "B") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "C") [fp "x3", fp "z3"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "D") [fp "x3", fp "z3"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_mul" (fp "DA") [fp "D", fp "A"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_mul" (fp "CB") [fp "C", fp "B"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "DApCB") [fp "DA", fp "CB"])
    (LowCT.RCall "fp_sqr" (fp "x3p") [fp "DApCB"])

/-- Compute `z3p = x1 · (DA - CB)²`. -/
def fullstepZ3BodyDirect : LowCT :=
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "A") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "B") [fp "x2", fp "z2"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_add" (fp "C") [fp "x3", fp "z3"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "D") [fp "x3", fp "z3"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_mul" (fp "DA") [fp "D", fp "A"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_mul" (fp "CB") [fp "C", fp "B"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sub" (fp "DAmCB") [fp "DA", fp "CB"]) $
  LowCT.RSeq
    (LowCT.RCall "fp_sqr" (fp "DAmCB2") [fp "DAmCB"])
    (LowCT.RCall "fp_mul" (fp "z3p") [fp "x1", fp "DAmCB2"])

/-! ## §4.  Slot signatures (memory-safety targets) -/

/-- Slot signature for `halfstepBodyDirect`: inputs `x2 z2`, output
    `x2p`, intermediates `A B AA BB`.  All at `TFp25519`. -/
abbrev halfstepSlots : List (String × TowerType) :=
  [ ("x2",  TowerType.TFp25519)
  , ("z2",  TowerType.TFp25519)
  , ("x2p", TowerType.TFp25519)
  , ("A",   TowerType.TFp25519)
  , ("B",   TowerType.TFp25519)
  , ("AA",  TowerType.TFp25519)
  , ("BB",  TowerType.TFp25519) ]

/-- Slot signature for `fullstepX2BodyDirect`: identical to
    `halfstepSlots` (the bodies coincide). -/
abbrev fullstepX2Slots : List (String × TowerType) := halfstepSlots

/-- Slot signature for `fullstepZ2BodyDirect`: 10 `TFp25519` slots. -/
abbrev fullstepZ2Slots : List (String × TowerType) :=
  [ ("x2",   TowerType.TFp25519)
  , ("z2",   TowerType.TFp25519)
  , ("z2p",  TowerType.TFp25519)
  , ("A",    TowerType.TFp25519)
  , ("B",    TowerType.TFp25519)
  , ("AA",   TowerType.TFp25519)
  , ("BB",   TowerType.TFp25519)
  , ("E",    TowerType.TFp25519)
  , ("a24E", TowerType.TFp25519)
  , ("inn",  TowerType.TFp25519) ]

/-- Slot signature for `fullstepX3BodyDirect`: 11 `TFp25519` slots. -/
abbrev fullstepX3Slots : List (String × TowerType) :=
  [ ("x2",    TowerType.TFp25519)
  , ("z2",    TowerType.TFp25519)
  , ("x3",    TowerType.TFp25519)
  , ("z3",    TowerType.TFp25519)
  , ("x3p",   TowerType.TFp25519)
  , ("A",     TowerType.TFp25519)
  , ("B",     TowerType.TFp25519)
  , ("C",     TowerType.TFp25519)
  , ("D",     TowerType.TFp25519)
  , ("DA",    TowerType.TFp25519)
  , ("CB",    TowerType.TFp25519)
  , ("DApCB", TowerType.TFp25519) ]

/-- Slot signature for `fullstepZ3BodyDirect`: 13 `TFp25519` slots. -/
abbrev fullstepZ3Slots : List (String × TowerType) :=
  [ ("x1",     TowerType.TFp25519)
  , ("x2",     TowerType.TFp25519)
  , ("z2",     TowerType.TFp25519)
  , ("x3",     TowerType.TFp25519)
  , ("z3",     TowerType.TFp25519)
  , ("z3p",    TowerType.TFp25519)
  , ("A",      TowerType.TFp25519)
  , ("B",      TowerType.TFp25519)
  , ("C",      TowerType.TFp25519)
  , ("D",      TowerType.TFp25519)
  , ("DA",     TowerType.TFp25519)
  , ("CB",     TowerType.TFp25519)
  , ("DAmCB",  TowerType.TFp25519)
  , ("DAmCB2", TowerType.TFp25519) ]

/-! ## §5.  Memory-safety theorems

Each body is a flat `RSeq` chain of `RCall`s.  Memory safety is the
composition of `rcall_AllSlots` applications, all dispatched against
the same slot signature.  The dest membership and arg membership
proofs are produced by `simp [<slots>]` and `List.mem_*`. -/

/-- **Memory safety for `halfstepBodyDirect`**: 5 `RCall`s, all over
    `TFp25519`.  Composition of 5 `rcall_AllSlots` applications. -/
theorem halfstepBodyDirect_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt halfstepSlots rs) :
    ∃ rs', RustExec N leafSpec halfstepBodyDirect rs rs' ∧
      memory_safe halfstepSlots rs' := by
  have hX2  : ("x2",  TowerType.TFp25519) ∈ halfstepSlots := by simp [halfstepSlots]
  have hZ2  : ("z2",  TowerType.TFp25519) ∈ halfstepSlots := by simp [halfstepSlots]
  have hX2p : ("x2p", TowerType.TFp25519) ∈ halfstepSlots := by simp [halfstepSlots]
  have hA   : ("A",   TowerType.TFp25519) ∈ halfstepSlots := by simp [halfstepSlots]
  have hB   : ("B",   TowerType.TFp25519) ∈ halfstepSlots := by simp [halfstepSlots]
  have hAA  : ("AA",  TowerType.TFp25519) ∈ halfstepSlots := by simp [halfstepSlots]
  have hBB  : ("BB",  TowerType.TFp25519) ∈ halfstepSlots := by simp [halfstepSlots]
  obtain ⟨r1, hr1, hP1⟩ := rcall_AllSlots N leafSpec halfstepSlots
    "fp_add" (fp "A") [fp "x2", fp "z2"] rs hA
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX2
        · rcases List.mem_singleton.mp h with rfl; exact hZ2) hP
  obtain ⟨r2, hr2, hP2⟩ := rcall_AllSlots N leafSpec halfstepSlots
    "fp_sub" (fp "B") [fp "x2", fp "z2"] r1 hB
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX2
        · rcases List.mem_singleton.mp h with rfl; exact hZ2) hP1
  obtain ⟨r3, hr3, hP3⟩ := rcall_AllSlots N leafSpec halfstepSlots
    "fp_sqr" (fp "AA") [fp "A"] r2 hAA
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hA) hP2
  obtain ⟨r4, hr4, hP4⟩ := rcall_AllSlots N leafSpec halfstepSlots
    "fp_sqr" (fp "BB") [fp "B"] r3 hBB
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hB) hP3
  obtain ⟨r5, hr5, hP5⟩ := rcall_AllSlots N leafSpec halfstepSlots
    "fp_mul" (fp "x2p") [fp "AA", fp "BB"] r4 hX2p
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hAA
        · rcases List.mem_singleton.mp h with rfl; exact hBB) hP4
  refine ⟨r5, ?_, hP5⟩
  show RustExec N leafSpec halfstepBodyDirect rs r5
  unfold halfstepBodyDirect
  exact RustExec.seq _ _ _ _ _ hr1
    (RustExec.seq _ _ _ _ _ hr2
      (RustExec.seq _ _ _ _ _ hr3
        (RustExec.seq _ _ _ _ _ hr4 hr5)))

/-- **Memory safety for `fullstepX2BodyDirect`**: body coincides with
    `halfstepBodyDirect`; reuse the proof. -/
theorem fullstepX2BodyDirect_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt fullstepX2Slots rs) :
    ∃ rs', RustExec N leafSpec fullstepX2BodyDirect rs rs' ∧
      memory_safe fullstepX2Slots rs' := by
  -- Bodies are definitionally equal.
  have hEq : fullstepX2BodyDirect = halfstepBodyDirect := rfl
  rw [hEq]
  exact halfstepBodyDirect_memory_safe N leafSpec rs hP

/-- **Memory safety for `fullstepZ2BodyDirect`**: 8 `RCall`s over
    `TFp25519`. -/
theorem fullstepZ2BodyDirect_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt fullstepZ2Slots rs) :
    ∃ rs', RustExec N leafSpec fullstepZ2BodyDirect rs rs' ∧
      memory_safe fullstepZ2Slots rs' := by
  have hX2   : ("x2",   TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hZ2   : ("z2",   TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hZ2p  : ("z2p",  TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hA    : ("A",    TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hB    : ("B",    TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hAA   : ("AA",   TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hBB   : ("BB",   TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hE    : ("E",    TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hA24E : ("a24E", TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  have hInn  : ("inn",  TowerType.TFp25519) ∈ fullstepZ2Slots := by simp [fullstepZ2Slots]
  obtain ⟨r1, hr1, hP1⟩ := rcall_AllSlots N leafSpec fullstepZ2Slots
    "fp_add" (fp "A") [fp "x2", fp "z2"] rs hA
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX2
        · rcases List.mem_singleton.mp h with rfl; exact hZ2) hP
  obtain ⟨r2, hr2, hP2⟩ := rcall_AllSlots N leafSpec fullstepZ2Slots
    "fp_sub" (fp "B") [fp "x2", fp "z2"] r1 hB
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX2
        · rcases List.mem_singleton.mp h with rfl; exact hZ2) hP1
  obtain ⟨r3, hr3, hP3⟩ := rcall_AllSlots N leafSpec fullstepZ2Slots
    "fp_sqr" (fp "AA") [fp "A"] r2 hAA
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hA) hP2
  obtain ⟨r4, hr4, hP4⟩ := rcall_AllSlots N leafSpec fullstepZ2Slots
    "fp_sqr" (fp "BB") [fp "B"] r3 hBB
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hB) hP3
  obtain ⟨r5, hr5, hP5⟩ := rcall_AllSlots N leafSpec fullstepZ2Slots
    "fp_sub" (fp "E") [fp "AA", fp "BB"] r4 hE
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hAA
        · rcases List.mem_singleton.mp h with rfl; exact hBB) hP4
  obtain ⟨r6, hr6, hP6⟩ := rcall_AllSlots N leafSpec fullstepZ2Slots
    "fp_mul_a24" (fp "a24E") [fp "E"] r5 hA24E
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hE) hP5
  obtain ⟨r7, hr7, hP7⟩ := rcall_AllSlots N leafSpec fullstepZ2Slots
    "fp_add" (fp "inn") [fp "BB", fp "a24E"] r6 hInn
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hBB
        · rcases List.mem_singleton.mp h with rfl; exact hA24E) hP6
  obtain ⟨r8, hr8, hP8⟩ := rcall_AllSlots N leafSpec fullstepZ2Slots
    "fp_mul" (fp "z2p") [fp "E", fp "inn"] r7 hZ2p
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hE
        · rcases List.mem_singleton.mp h with rfl; exact hInn) hP7
  refine ⟨r8, ?_, hP8⟩
  show RustExec N leafSpec fullstepZ2BodyDirect rs r8
  unfold fullstepZ2BodyDirect
  exact RustExec.seq _ _ _ _ _ hr1
    (RustExec.seq _ _ _ _ _ hr2
      (RustExec.seq _ _ _ _ _ hr3
        (RustExec.seq _ _ _ _ _ hr4
          (RustExec.seq _ _ _ _ _ hr5
            (RustExec.seq _ _ _ _ _ hr6
              (RustExec.seq _ _ _ _ _ hr7 hr8))))))

/-- **Memory safety for `fullstepX3BodyDirect`**: 8 `RCall`s over
    `TFp25519`. -/
theorem fullstepX3BodyDirect_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt fullstepX3Slots rs) :
    ∃ rs', RustExec N leafSpec fullstepX3BodyDirect rs rs' ∧
      memory_safe fullstepX3Slots rs' := by
  have hX2    : ("x2",    TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hZ2    : ("z2",    TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hX3    : ("x3",    TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hZ3    : ("z3",    TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hX3p   : ("x3p",   TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hA     : ("A",     TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hB     : ("B",     TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hC     : ("C",     TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hD     : ("D",     TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hDA    : ("DA",    TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hCB    : ("CB",    TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  have hDApCB : ("DApCB", TowerType.TFp25519) ∈ fullstepX3Slots := by simp [fullstepX3Slots]
  obtain ⟨r1, hr1, hP1⟩ := rcall_AllSlots N leafSpec fullstepX3Slots
    "fp_add" (fp "A") [fp "x2", fp "z2"] rs hA
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX2
        · rcases List.mem_singleton.mp h with rfl; exact hZ2) hP
  obtain ⟨r2, hr2, hP2⟩ := rcall_AllSlots N leafSpec fullstepX3Slots
    "fp_sub" (fp "B") [fp "x2", fp "z2"] r1 hB
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX2
        · rcases List.mem_singleton.mp h with rfl; exact hZ2) hP1
  obtain ⟨r3, hr3, hP3⟩ := rcall_AllSlots N leafSpec fullstepX3Slots
    "fp_add" (fp "C") [fp "x3", fp "z3"] r2 hC
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX3
        · rcases List.mem_singleton.mp h with rfl; exact hZ3) hP2
  obtain ⟨r4, hr4, hP4⟩ := rcall_AllSlots N leafSpec fullstepX3Slots
    "fp_sub" (fp "D") [fp "x3", fp "z3"] r3 hD
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX3
        · rcases List.mem_singleton.mp h with rfl; exact hZ3) hP3
  obtain ⟨r5, hr5, hP5⟩ := rcall_AllSlots N leafSpec fullstepX3Slots
    "fp_mul" (fp "DA") [fp "D", fp "A"] r4 hDA
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hD
        · rcases List.mem_singleton.mp h with rfl; exact hA) hP4
  obtain ⟨r6, hr6, hP6⟩ := rcall_AllSlots N leafSpec fullstepX3Slots
    "fp_mul" (fp "CB") [fp "C", fp "B"] r5 hCB
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hC
        · rcases List.mem_singleton.mp h with rfl; exact hB) hP5
  obtain ⟨r7, hr7, hP7⟩ := rcall_AllSlots N leafSpec fullstepX3Slots
    "fp_add" (fp "DApCB") [fp "DA", fp "CB"] r6 hDApCB
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hDA
        · rcases List.mem_singleton.mp h with rfl; exact hCB) hP6
  obtain ⟨r8, hr8, hP8⟩ := rcall_AllSlots N leafSpec fullstepX3Slots
    "fp_sqr" (fp "x3p") [fp "DApCB"] r7 hX3p
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hDApCB) hP7
  refine ⟨r8, ?_, hP8⟩
  show RustExec N leafSpec fullstepX3BodyDirect rs r8
  unfold fullstepX3BodyDirect
  exact RustExec.seq _ _ _ _ _ hr1
    (RustExec.seq _ _ _ _ _ hr2
      (RustExec.seq _ _ _ _ _ hr3
        (RustExec.seq _ _ _ _ _ hr4
          (RustExec.seq _ _ _ _ _ hr5
            (RustExec.seq _ _ _ _ _ hr6
              (RustExec.seq _ _ _ _ _ hr7 hr8))))))

/-- **Memory safety for `fullstepZ3BodyDirect`**: 9 `RCall`s over
    `TFp25519`. -/
theorem fullstepZ3BodyDirect_memory_safe
    (N : Nat) (leafSpec : LeafSpec) (rs : RustState)
    (hP : AllSlotsBoundAt fullstepZ3Slots rs) :
    ∃ rs', RustExec N leafSpec fullstepZ3BodyDirect rs rs' ∧
      memory_safe fullstepZ3Slots rs' := by
  have hX1     : ("x1",     TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hX2     : ("x2",     TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hZ2     : ("z2",     TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hX3     : ("x3",     TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hZ3     : ("z3",     TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hZ3p    : ("z3p",    TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hA      : ("A",      TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hB      : ("B",      TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hC      : ("C",      TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hD      : ("D",      TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hDA     : ("DA",     TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hCB     : ("CB",     TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hDAmCB  : ("DAmCB",  TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  have hDAmCB2 : ("DAmCB2", TowerType.TFp25519) ∈ fullstepZ3Slots := by simp [fullstepZ3Slots]
  obtain ⟨r1, hr1, hP1⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_add" (fp "A") [fp "x2", fp "z2"] rs hA
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX2
        · rcases List.mem_singleton.mp h with rfl; exact hZ2) hP
  obtain ⟨r2, hr2, hP2⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_sub" (fp "B") [fp "x2", fp "z2"] r1 hB
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX2
        · rcases List.mem_singleton.mp h with rfl; exact hZ2) hP1
  obtain ⟨r3, hr3, hP3⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_add" (fp "C") [fp "x3", fp "z3"] r2 hC
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX3
        · rcases List.mem_singleton.mp h with rfl; exact hZ3) hP2
  obtain ⟨r4, hr4, hP4⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_sub" (fp "D") [fp "x3", fp "z3"] r3 hD
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX3
        · rcases List.mem_singleton.mp h with rfl; exact hZ3) hP3
  obtain ⟨r5, hr5, hP5⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_mul" (fp "DA") [fp "D", fp "A"] r4 hDA
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hD
        · rcases List.mem_singleton.mp h with rfl; exact hA) hP4
  obtain ⟨r6, hr6, hP6⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_mul" (fp "CB") [fp "C", fp "B"] r5 hCB
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hC
        · rcases List.mem_singleton.mp h with rfl; exact hB) hP5
  obtain ⟨r7, hr7, hP7⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_sub" (fp "DAmCB") [fp "DA", fp "CB"] r6 hDAmCB
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hDA
        · rcases List.mem_singleton.mp h with rfl; exact hCB) hP6
  obtain ⟨r8, hr8, hP8⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_sqr" (fp "DAmCB2") [fp "DAmCB"] r7 hDAmCB2
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact hDAmCB) hP7
  obtain ⟨r9, hr9, hP9⟩ := rcall_AllSlots N leafSpec fullstepZ3Slots
    "fp_mul" (fp "z3p") [fp "x1", fp "DAmCB2"] r8 hZ3p
    (by intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hX1
        · rcases List.mem_singleton.mp h with rfl; exact hDAmCB2) hP8
  refine ⟨r9, ?_, hP9⟩
  show RustExec N leafSpec fullstepZ3BodyDirect rs r9
  unfold fullstepZ3BodyDirect
  exact RustExec.seq _ _ _ _ _ hr1
    (RustExec.seq _ _ _ _ _ hr2
      (RustExec.seq _ _ _ _ _ hr3
        (RustExec.seq _ _ _ _ _ hr4
          (RustExec.seq _ _ _ _ _ hr5
            (RustExec.seq _ _ _ _ _ hr6
              (RustExec.seq _ _ _ _ _ hr7
                (RustExec.seq _ _ _ _ _ hr8 hr9)))))))

end CatCrypt.Crypto.Jasmin.Examples.X25519StepBodiesSafety
