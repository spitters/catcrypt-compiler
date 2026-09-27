/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# Memory-safety theorem for `xeddsaVerifySplitBody`

Companion to `XEdDSAVerify.lean`'s `xeddsaVerifyBody_memory_safe`.  The
split variant splits a 64-byte signature into two 32-byte locals
(`r_part` and `s_part`) before the Mont→Edwards conversion and the
Ed25519 verify.

Each of the four steps is a leaf call, so the whole body composes out
of `rcall_AllSlots` and `rseq_AllSlots` from
`EmittedASTCorrectness.lean` under three `RLetZero` binders.

## Audit context (2026-05-13)

After this file lands, the IR-emitted bodies with `_memory_safe` Qed
proofs are:

  * `EmittedASTCorrectness.lean`     — 9 bodies (Scalar25519Ops × 6,
                                       fe25519Invert, combTableInitArrV2,
                                       montUToEdwards)
  * `XEdDSAVerify.lean`              — 1 (xeddsaVerifyBody)
  * `X25519StepBodiesSafety.lean`    — 5 (halfstep + 4 fullstep direct)
  * `XEdDSAVerifySplitSafety.lean`   — 1 (xeddsaVerifySplitBody; this file)

Total: 16 IR bodies with mechanised memory-safety witnesses.
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec
public import CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness
public import CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify


@[expose] public section
namespace CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerifySplitSafety

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness
open CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify

variable (N : Nat) (leafSpec : LeafSpec)

/-! ## §1.  Slot signature for `xeddsaVerifySplitBody`

The split variant has the same external inputs/outputs as
`xeddsaVerifyBody`, so the slot signature reuses `xeddsaVerifySlots`.
The three locals introduced by `RLetZero` (`edwards_pk`, `r_part`,
`s_part`) are added inside via successive `rletZero_AllSlots_extend`
applications. -/

/-- `TBytes 32` slot helper (mirrors the private one in `XEdDSAVerify`). -/
def bytes32 (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TBytes 32 }

/-- `TBytes 64` slot helper. -/
def bytes64 (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TBytes 64 }

/-- `TU64` slot helper. -/
def u64slot (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TU64 }

/-! ## §2.  Strong panic-freeness + memory safety -/

/-- **Strong panic-freeness for `xeddsaVerifySplitBody`** — existence
    of a post-state PLUS preservation of `AllSlotsBoundAt
    xeddsaVerifySlots`.  Same composition as
    `xeddsaVerifyBody_panic_free_strong` but with three `RLetZero`
    binders (for `edwards_pk`, `r_part`, `s_part`) and two
    `bytes_slice` calls (to split the signature) inserted before the
    two other leaf calls. -/
theorem xeddsaVerifySplitBody_panic_free_strong
    (rs : RustState)
    (hP : AllSlotsBoundAt xeddsaVerifySlots rs) :
    ∃ rs', RustExec N leafSpec xeddsaVerifySplitBody rs rs' ∧
      AllSlotsBoundAt xeddsaVerifySlots rs' := by
  -- Extend the slot list with the three local bindings, in order.
  let ext1 : List (String × TowerType) :=
    ("edwards_pk", TowerType.TBytes 32) :: xeddsaVerifySlots
  let ext2 : List (String × TowerType) :=
    ("r_part",     TowerType.TBytes 32) :: ext1
  let ext3 : List (String × TowerType) :=
    ("s_part",     TowerType.TBytes 32) :: ext2
  -- §1 Freshness conditions: each new name is absent from the prior list.
  have hFresh1 : ∀ s ∈ xeddsaVerifySlots, s.1 ≠ "edwards_pk" := by
    rintro ⟨sN, sT⟩ hs
    simp only [xeddsaVerifySlots, List.mem_cons, List.not_mem_nil,
               or_false, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals decide
  have hFresh2 : ∀ s ∈ ext1, s.1 ≠ "r_part" := by
    rintro ⟨sN, sT⟩ hs
    simp only [ext1, xeddsaVerifySlots, List.mem_cons, List.not_mem_nil,
               or_false, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals decide
  have hFresh3 : ∀ s ∈ ext2, s.1 ≠ "s_part" := by
    rintro ⟨sN, sT⟩ hs
    simp only [ext2, ext1, xeddsaVerifySlots, List.mem_cons, List.not_mem_nil,
               or_false, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals decide
  -- §2 Slot-membership lemmas in the fully-extended list `ext3`.
  have hEd_in  : ("edwards_pk", TowerType.TBytes 32) ∈ ext3 := by
    simp [ext3, ext2, ext1]
  have hR_in   : ("r_part",     TowerType.TBytes 32) ∈ ext3 := by
    simp [ext3, ext2, ext1]
  have hS_in   : ("s_part",     TowerType.TBytes 32) ∈ ext3 := by
    simp [ext3, ext2, ext1]
  have hPk_in  : ("pubkey",      TowerType.TBytes 32) ∈ ext3 := by
    simp [ext3, ext2, ext1, xeddsaVerifySlots]
  have hSig_in : ("signature",   TowerType.TBytes 64) ∈ ext3 := by
    simp [ext3, ext2, ext1, xeddsaVerifySlots]
  have hMsg_in : ("message_buf", TowerType.TBytes 32) ∈ ext3 := by
    simp [ext3, ext2, ext1, xeddsaVerifySlots]
  have hVer_in : ("verified",    TowerType.TU64) ∈ ext3 := by
    simp [ext3, ext2, ext1, xeddsaVerifySlots]
  -- §3 Walk through the three RLetZero binders.
  refine rletZero_AllSlots_extend N leafSpec xeddsaVerifySlots
    "edwards_pk" (TowerType.TBytes 32) hFresh1 ?_ rs hP
  intro rs0 hP0
  refine rletZero_AllSlots_extend N leafSpec ext1
    "r_part" (TowerType.TBytes 32) hFresh2 ?_ rs0 hP0
  intro rs1 hP1
  refine rletZero_AllSlots_extend N leafSpec ext2
    "s_part" (TowerType.TBytes 32) hFresh3 ?_ rs1 hP1
  intro rs2 hP2
  -- §4 Inside the binders: the two slices, then the two other leaf calls.
  -- Slice 1: r_part := signature[0..32].
  refine rseq_AllSlots N leafSpec ext3 ?_ ?_ rs2 hP2
  · intro rs3 hP3
    exact rcall_AllSlots N leafSpec ext3
      "bytes_slice_0_32"
      (bytes32 "r_part") [bytes64 "signature"] rs3 hR_in
      (by intro a ha
          rcases List.mem_singleton.mp ha with rfl
          exact hSig_in)
      hP3
  · intro rs4 hP4
    -- Slice 2: s_part := signature[32..64].
    refine rseq_AllSlots N leafSpec ext3 ?_ ?_ rs4 hP4
    · intro rs5 hP5
      exact rcall_AllSlots N leafSpec ext3
        "bytes_slice_32_32"
        (bytes32 "s_part") [bytes64 "signature"] rs5 hS_in
        (by intro a ha
            rcases List.mem_singleton.mp ha with rfl
            exact hSig_in)
        hP5
    · intro rs6 hP6
      -- Call 1: mont_u_to_edwards_compressed_zero (edwards_pk) [pubkey].
      refine rseq_AllSlots N leafSpec ext3 ?_ ?_ rs6 hP6
      · intro rs7 hP7
        exact rcall_AllSlots N leafSpec ext3
          "mont_u_to_edwards_compressed_zero"
          (bytes32 "edwards_pk") [bytes32 "pubkey"] rs7 hEd_in
          (by intro a ha
              rcases List.mem_singleton.mp ha with rfl
              exact hPk_in)
          hP7
      · intro rs8 hP8
        -- Call 2: ed25519_verify (verified) [signature, edwards_pk, message_buf].
        exact rcall_AllSlots N leafSpec ext3
          "ed25519_verify"
          (u64slot "verified")
          [bytes64 "signature", bytes32 "edwards_pk", bytes32 "message_buf"]
          rs8 hVer_in
          (by intro a ha
              rcases List.mem_cons.mp ha with rfl | h
              · exact hSig_in
              · rcases List.mem_cons.mp h with rfl | h'
                · exact hEd_in
                · rcases List.mem_singleton.mp h' with rfl; exact hMsg_in)
          hP8

/-- **Memory safety for `xeddsaVerifySplitBody`**: every memory-safe
    input state yields at least one execution whose post-state has
    every tracked slot bound at its declared tower type.  Corollary
    of `xeddsaVerifySplitBody_panic_free_strong` via the
    `memory_safe = AllSlotsBoundAt` alias. -/
theorem xeddsaVerifySplitBody_memory_safe
    (rs : RustState)
    (hP : memory_safe xeddsaVerifySlots rs) :
    ∃ rs', RustExec N leafSpec xeddsaVerifySplitBody rs rs' ∧
      memory_safe xeddsaVerifySlots rs' :=
  xeddsaVerifySplitBody_panic_free_strong N leafSpec rs hP

end CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerifySplitSafety
