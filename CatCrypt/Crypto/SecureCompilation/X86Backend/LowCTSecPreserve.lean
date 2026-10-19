/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
public import CatCrypt.Crypto.SDist

/-!
# Transfer of an `sdist` bound along an equality of `srcDenote`

For call-free scalar-arith programs (`List ArithSrc`), the `SPComp` interpretation of the
ITree denotation is the pure computation `SPComp.pure (srcDenote ps rs)`
(`interpSP_callfree`). Two programs with equal `srcDenote` on a state therefore have equal
`SPComp` interpretations, and an `sdist` bound to an ideal computation holds for one exactly
when it holds for the other.

The programs are arbitrary lists of `ArithSrc`; no theorem here relates either of them to the
output of a compiler.

## Main results

* `spDenote_eq_preserves_sdist` — equal `SPComp` computations have the same `sdist` bound to
  an ideal computation.
* `interpSP_progEquiv` — two call-free programs with equal `srcDenote` have equal `interpSP`
  interpretations.
* `sdist_transfer_of_srcDenote_eq` — an `sdist ≤ ε` bound to an ideal computation transfers
  from `srcP` to `tgtP` when `srcDenote srcP rs = srcDenote tgtP rs`.

The import closure contains `LowCTITreePRHL` and `CatCrypt.Crypto.SDist` and nothing under
`Bridges/` or `IrisBridge/`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
open scoped ENNReal

/-! ## 1. Equal computations have the same `sdist` bound -/

/-- If two `SPComp` computations `c`, `c'` are equal, then an `sdist` bound to an ideal
    computation transfers from `c` to `c'`. -/
theorem spDenote_eq_preserves_sdist {α β : Type}
    {c c' ideal : SPComp β} {ε : ℝ≥0∞}
    (h_eq : c = c')
    (h_sec : sdist (fun _ : α => c) (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => c') (fun _ : α => ideal) ≤ ε :=
  h_eq ▸ h_sec

/-! ## 2. Equal `srcDenote` gives equal `interpSP` interpretations -/

/-- If two call-free scalar-arith programs `ps`, `qs` have equal big-step semantics on the
    given states (`srcDenote ps rs₁ = srcDenote qs rs₂`), then their `interpSP`
    interpretations are equal `SPComp` computations. Proved by rewriting both sides with
    `interpSP_callfree`. -/
theorem interpSP_progEquiv
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ps qs : List ArithSrc) (rs₁ rs₂ : RustState)
    (hsrc : srcDenote ps rs₁ = srcDenote qs rs₂) :
    interpSP h (itreeDenoteArith ps rs₁) = interpSP h (itreeDenoteArith qs rs₂) := by
  rw [interpSP_callfree, interpSP_callfree, hsrc]

/-! ## 3. Transfer of an `sdist` bound -/

/-- **An `sdist` bound transfers along an equality of `srcDenote`.** For call-free
    scalar-arith programs `srcP`, `tgtP` with `srcDenote srcP rs = srcDenote tgtP rs`, if the
    `SPComp` interpretation of `srcP` is within `sdist ≤ ε` of `ideal`, so is that of `tgtP`.
    It composes `interpSP_progEquiv` with `spDenote_eq_preserves_sdist`. -/
theorem sdist_transfer_of_srcDenote_eq {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (srcP tgtP : List ArithSrc) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hcc : srcDenote srcP rs = srcDenote tgtP rs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenoteArith srcP rs))
                  (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => interpSP h (itreeDenoteArith tgtP rs))
          (fun _ : α => ideal) ≤ ε :=
  spDenote_eq_preserves_sdist
    (interpSP_progEquiv h srcP tgtP rs rs hcc) hsec

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
