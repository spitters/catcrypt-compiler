/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardSatisfiable
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Proof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Bytes
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Framed

/-!
# Guard-satisfiability of the `bignum_montmul_p384` correspondences

Every CLOSED `CorresJ`/`BytesCorresJ` theorem in the `S2nMontmulP384` family —
the entry-to-exit results `s2nMontmulP384_corresJ` / `s2nMontmulP384Framed_corresJ`
and their byte-level counterparts, and the per-segment steps `corresJ_seg01`,
`corresJ_seg02`, `corresJ_final` — has a state relation and guard that share a
witness. Each result here pairs one such theorem with
`GuardSatisfiable.corresJ_guardSat` / `bytesCorresJ_guardSat` and a joint witness
(`srm_stage0_satisfiable`, `srm_stage1_satisfiable`, `srm_stage13_satisfiable`,
`srAlloc_stage0_satisfiable`, `frameRel_srm_stage0_satisfiable`,
`srAlloc_frameRel_stage0_satisfiable`), so the pairing is checked by Lean's own
unifier against each theorem's elaborated `SR`/`P`, not reparsed from source.

`corresJ_row` and `corresJ_redc` are not paired here: both take the stage index
`k` as an explicit parameter, so their guard is not a fixed closed term until a
caller instantiates `k` — there is nothing concrete to witness at the generic
lemma itself.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384

open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame
open CatCrypt.Crypto.Optimizer
open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
open CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated

/-- `s2nMontmulP384_corresJ`'s state relation `SRm` and guard
    `fun a => a.stage = 0 ∧ a.x < 2 ^ 384` share the witness `srm_stage0_satisfiable`. -/
theorem s2nMontmulP384_corresJ_guardSat :
    ∃ st a, SRm st a ∧ (a.stage = 0 ∧ a.x < 2 ^ 384) :=
  corresJ_guardSat s2nMontmulP384_corresJ srm_stage0_satisfiable

/-- `corresJ_seg01`'s guard is the same `fun a => a.stage = 0 ∧ a.x < 2 ^ 384` as
    `s2nMontmulP384_corresJ`'s. -/
theorem corresJ_seg01_guardSat :
    ∃ st a, SRm st a ∧ (a.stage = 0 ∧ a.x < 2 ^ 384) :=
  corresJ_guardSat corresJ_seg01 srm_stage0_satisfiable

/-- `corresJ_seg02`'s state relation `SRm` and guard
    `fun a => a.stage = 1 ∧ a.x < 2 ^ 384` share the witness `srm_stage1_satisfiable`. -/
theorem corresJ_seg02_guardSat :
    ∃ st a, SRm st a ∧ (a.stage = 1 ∧ a.x < 2 ^ 384) :=
  corresJ_guardSat corresJ_seg02 srm_stage1_satisfiable

/-- `corresJ_final`'s state relation `SRm` and guard
    `fun a => a.stage = 13 ∧ a.x < 2 ^ 384 ∧ a.acc < 2 ^ 384 + p384` share the
    witness `srm_stage13_satisfiable`. -/
theorem corresJ_final_guardSat :
    ∃ st a, SRm st a ∧ (a.stage = 13 ∧ a.x < 2 ^ 384 ∧ a.acc < 2 ^ 384 + p384) :=
  corresJ_guardSat corresJ_final srm_stage13_satisfiable

/-- `s2nMontmulP384_bytesCorresJ`'s pulled-back state relation and guard share the
    witness `srAlloc_stage0_satisfiable`. -/
theorem s2nMontmulP384_bytesCorresJ_guardSat :
    ∃ st a, SRalloc (blockNamesXsym s2nMontmulP384Block) (nameOf s2nAlloc) SRm st a ∧
      (a.stage = 0 ∧ a.x < 2 ^ 384) :=
  bytesCorresJ_guardSat s2nMontmulP384_bytesCorresJ srAlloc_stage0_satisfiable

/-- `s2nMontmulP384Framed_corresJ`'s state relation `FrameRel SRm` and guard
    `fun p => p.1.stage = 0 ∧ p.1.x < 2 ^ 384` share the witness
    `frameRel_srm_stage0_satisfiable`. -/
theorem s2nMontmulP384Framed_corresJ_guardSat :
    ∃ st p, FrameRel SRm st p ∧ (p.1.stage = 0 ∧ p.1.x < 2 ^ 384) :=
  corresJ_guardSat s2nMontmulP384Framed_corresJ frameRel_srm_stage0_satisfiable

/-- `s2nMontmulP384Framed_bytesCorresJ`'s pulled-back state relation and guard
    share the witness `srAlloc_frameRel_stage0_satisfiable`. -/
theorem s2nMontmulP384Framed_bytesCorresJ_guardSat :
    ∃ st p, SRalloc (blockNamesXsym s2nMontmulP384FramedBlock) (nameOf s2nAlloc)
        (FrameRel SRm) st p ∧ (p.1.stage = 0 ∧ p.1.x < 2 ^ 384) :=
  bytesCorresJ_guardSat s2nMontmulP384Framed_bytesCorresJ srAlloc_frameRel_stage0_satisfiable

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
