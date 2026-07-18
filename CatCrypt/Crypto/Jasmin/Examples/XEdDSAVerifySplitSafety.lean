/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# Memory-safety theorem for `xeddsaVerifySplitBody`

Companion to `XEdDSAVerify.lean`'s `xeddsaVerifyBody_memory_safe`.  The
split variant exercises the new `RBytesSlice` IR constructor by
splitting a 64-byte signature into two 32-byte locals (`r_part` and
`s_part`) before the Mont→Edwards conversion and the Ed25519 verify.

`RBytesSlice` did not have a `_panic_free` / `_AllSlots` helper in
`EmittedASTCorrectness.lean` (that file was authored before the
constructor landed), so this file provides the missing helpers along
with the body-level memory-safety theorem.  The structural shape is
identical to `RArrLoad`: both write only `dst` and require `dst` and
`src` to be tower-bound at their declared types.

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
import CatCrypt.Crypto.Jasmin.LowCT
import CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness
import CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify

namespace CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerifySplitSafety

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness
open CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify

variable (N : Nat) (leafSpec : LeafSpec)

/-! ## §1.  `RBytesSlice` panic-freeness and frame helpers

These mirror `rarrLoad_panic_free` / `rarrLoad_post_bindings` /
`rarrLoad_AllSlots` in `EmittedASTCorrectness.lean`.  The constructor
shape is the same: read `dst` (for `oldV`), read `src` (for `srcV`),
write back into `dst` only. -/

/-- `RBytesSlice` requires `dst` and `src` slots bound at their
    declared tower types.  Returns the existence of a post-state. -/
lemma rbytesSlice_panic_free
    (dst src : Located) (start len : Nat)
    (rs : RustState)
    (hDst : ∃ v, rs.rsTower dst.locVar = some ⟨dst.locDst, v⟩)
    (hSrc : ∃ v, rs.rsTower src.locVar = some ⟨src.locDst, v⟩) :
    ∃ rs', RustExec N leafSpec (LowCT.RBytesSlice dst src start len) rs rs' := by
  obtain ⟨dstV, hDstV⟩ := hDst
  obtain ⟨srcV, hSrcV⟩ := hSrc
  have hDstLookup : locatedLookup rs dst = some dstV := by
    show (match rs.rsTower dst.locVar with
          | some ⟨t, v⟩ => if h : t = dst.locDst then some (h ▸ v) else none
          | none => none) = some dstV
    rw [hDstV]; simp
  have hSrcLookup : locatedLookup rs src = some srcV := by
    show (match rs.rsTower src.locVar with
          | some ⟨t, v⟩ => if h : t = src.locDst then some (h ▸ v) else none
          | none => none) = some srcV
    rw [hSrcV]; simp
  refine ⟨_, RustExec.bytesSlice dst src start len rs dstV srcV
    hDstLookup hSrcLookup⟩

/-- Post-state of `RBytesSlice` execution: `dst` is bound at its
    declared tower type, all other slots unchanged. -/
lemma rbytesSlice_post_bindings
    {N : Nat} {leafSpec : LeafSpec}
    {dst src : Located} {start len : Nat}
    {rs rs' : RustState}
    (hExec : RustExec N leafSpec (LowCT.RBytesSlice dst src start len) rs rs') :
    (∃ v, rs'.rsTower dst.locVar = some ⟨dst.locDst, v⟩) ∧
    (∀ name : String, name ≠ dst.locVar →
        rs'.rsTower name = rs.rsTower name) := by
  cases hExec with
  | bytesSlice _ _ _ _ _ _ _ _ _ =>
    refine ⟨⟨_, locatedUpdate_dest _ _ _⟩, ?_⟩
    intro name hne
    show (rsSetTower rs dst.locVar _).rsTower name = rs.rsTower name
    exact rsSetTower_other rs dst.locVar name _ (Ne.symm hne)

/-- `RBytesSlice dst src start len` preserves `AllSlotsBoundAt`
    provided `dst` and `src` are both tracked at their declared types. -/
lemma rbytesSlice_AllSlots
    (N : Nat) (leafSpec : LeafSpec) (slots : List (String × TowerType))
    (dst src : Located) (start len : Nat) (rs : RustState)
    (hDstIn : (dst.locVar, dst.locDst) ∈ slots)
    (hSrcIn : (src.locVar, src.locDst) ∈ slots)
    (hP : AllSlotsBoundAt slots rs) :
    ∃ rs', RustExec N leafSpec (LowCT.RBytesSlice dst src start len) rs rs' ∧
      AllSlotsBoundAt slots rs' := by
  have hDst : ∃ v, rs.rsTower dst.locVar = some ⟨dst.locDst, v⟩ :=
    hP (dst.locVar, dst.locDst) hDstIn
  have hSrc : ∃ v, rs.rsTower src.locVar = some ⟨src.locDst, v⟩ :=
    hP (src.locVar, src.locDst) hSrcIn
  obtain ⟨rs', hExec⟩ := rbytesSlice_panic_free N leafSpec dst src start len rs hDst hSrc
  refine ⟨rs', hExec, ?_⟩
  have ⟨⟨v', hDst'⟩, hPres⟩ := rbytesSlice_post_bindings hExec
  rintro ⟨sName, sTy⟩ hs
  by_cases hsd : sName = dst.locVar
  · obtain ⟨v0, hv0⟩ := hP (sName, sTy) hs
    obtain ⟨v1, hv1⟩ := hDst
    have hrs_eq : sTy = dst.locDst := by
      simp only at hv0
      rw [hsd] at hv0
      rw [hv0] at hv1
      exact (Sigma.mk.injEq _ _ _ _).mp (Option.some_inj.mp hv1) |>.1
    subst hsd
    subst hrs_eq
    exact ⟨v', hDst'⟩
  · obtain ⟨v0, hv0⟩ := hP (sName, sTy) hs
    refine ⟨v0, ?_⟩
    show rs'.rsTower sName = _
    rw [hPres sName hsd]
    exact hv0

/-! ## §2.  Slot signature for `xeddsaVerifySplitBody`

The split variant has the same external inputs/outputs as
`xeddsaVerifyBody`, so the slot signature reuses `xeddsaVerifySlots`.
The three locals introduced by `RLetZero` (`edwards_pk`, `r_part`,
`s_part`) are added inside via successive `rletZero_AllSlots_extend`
applications. -/

/-- `TBytes 32` slot helper (mirrors the private one in `XEdDSAVerify`). -/
private def bytes32 (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TBytes 32 }

/-- `TBytes 64` slot helper. -/
private def bytes64 (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TBytes 64 }

/-- `TU64` slot helper. -/
private def u64slot (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TU64 }

/-! ## §3.  Strong panic-freeness + memory safety -/

/-- **Strong panic-freeness for `xeddsaVerifySplitBody`** — existence
    of a post-state PLUS preservation of `AllSlotsBoundAt
    xeddsaVerifySlots`.  Same composition as
    `xeddsaVerifyBody_panic_free_strong` but with three `RLetZero`
    binders (for `edwards_pk`, `r_part`, `s_part`) and two
    `RBytesSlice` calls (to split the signature) inserted before the
    two leaf calls. -/
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
  -- §4 Inside the binders: RSeq of (RBytesSlice r_part) ; RBytesSlice s_part ;
  --     RSeq Call1 Call2.
  -- Slice 1: r_part := signature[0..32].
  refine rseq_AllSlots N leafSpec ext3 ?_ ?_ rs2 hP2
  · intro rs3 hP3
    exact rbytesSlice_AllSlots N leafSpec ext3
      (bytes32 "r_part") (bytes64 "signature") 0 32 rs3 hR_in hSig_in hP3
  · intro rs4 hP4
    -- Slice 2: s_part := signature[32..64].
    refine rseq_AllSlots N leafSpec ext3 ?_ ?_ rs4 hP4
    · intro rs5 hP5
      exact rbytesSlice_AllSlots N leafSpec ext3
        (bytes32 "s_part") (bytes64 "signature") 32 32 rs5 hS_in hSig_in hP5
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
