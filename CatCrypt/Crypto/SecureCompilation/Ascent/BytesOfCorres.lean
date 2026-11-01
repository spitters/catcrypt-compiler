/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.FnCorresUnique
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaX86Mov

/-!
# A kernel corresponding to a specification, at the machine code of every extracted function

A kernel is a compiled program together with a proof that it computes a specification
function `g`. An extracted function is an `ImpExpr` body `e` with entry environment `entry`
and guard `G`; a function correspondence `FnCorres bi e entry G f` states that its runs
return `enc (f a)`. When the specification `g` also corresponds to `e`, every function `f`
corresponding to `e` has the encoded value of `g` on the guard (`fnCorres_enc_unique`), so
the kernel computes `f`. This module states that transfer at two levels.

* At the block level: a `runBlock` correspondence `CorresJ (SR g) P fa c` of a block `c`
  with the specification gives `CorresJ (SR f) P fa c`, for a relation family `SR` that
  reads the function only at the argument `π s` of the abstract state.
* At the x86 instruction set: the same, composed with the transport
  `corresIsa_x86_of_corresJ_mov` of a block of `InMovRegSubset` instructions.

## Main results

* `corresJ_of_fnCorres`: the block-level transfer.
* `corresIsa_x86_mov_of_fnCorres`: the transfer at `x86Isa`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.BytesOfCorres

open _root_.Hax _root_.Hax.Ascent
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent (CorresJ CorresIsa liftSR
  corresIsa_x86_of_corresJ_mov)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg (jToRMMov
  InMovRegSubset)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

variable {A β S : Type} [HaxEnc β] {bi : Builtins} {e : ImpExpr} {entry : A → Env}
  {G : A → Prop}

/-- **The block-level transfer.** Let `SR f` relate a machine state to an abstract state `s`
    through the value of `f` at the argument `π s` only, let the precondition `P` imply the
    guard at `π s`, and let `fa` keep the argument. A `runBlock` correspondence of `c` with
    the specification `g`, where `g` corresponds to the extracted body, is a correspondence
    with every function `f` corresponding to the extracted body. -/
theorem corresJ_of_fnCorres {g f : A → β} (SR : (A → β) → JState 64 → S → Prop) (π : S → A)
    (P : S → Prop) (fa : S → S) (c : List (JInstr 64)) (hP : ∀ s, P s → G (π s))
    (hfa : ∀ s, π (fa s) = π s)
    (hSR : ∀ (f g : A → β) (st : JState 64) (s : S), enc (f (π s)) = enc (g (π s)) →
      SR g st s → SR f st s)
    (hk : CorresJ (SR g) P fa c) (hg : FnCorres bi e entry G g)
    (hf : FnCorres bi e entry G f) : CorresJ (SR f) P fa c := by
  intro st s hs hPs
  have he : enc (f (π s)) = enc (g (π s)) := fnCorres_enc_unique hf hg (hP s hPs)
  have h := hk st s (hSR g f st s he.symm hs) hPs
  exact hSR f g _ _ (by rw [hfa]; exact he) h

/-- **The transfer at the x86 instruction set.** Under the hypotheses of
    `corresJ_of_fnCorres`, for a block `c` of `InMovRegSubset` instructions, the lowered
    single-function program `singletonProgM fn (c.map jToRMMov)` corresponds under `x86Isa`,
    with fuel its length, to every function `f` corresponding to the extracted body. -/
theorem corresIsa_x86_mov_of_fnCorres {g f : A → β} (SR : (A → β) → JState 64 → S → Prop)
    (π : S → A) (P : S → Prop) (fa : S → S) (c : List (JInstr 64)) (fn : String)
    (hc : ∀ i ∈ c, InMovRegSubset i) (hP : ∀ s, P s → G (π s)) (hfa : ∀ s, π (fa s) = π s)
    (hSR : ∀ (f g : A → β) (st : JState 64) (s : S), enc (f (π s)) = enc (g (π s)) →
      SR g st s → SR f st s)
    (hk : CorresJ (SR g) P fa c) (hg : FnCorres bi e entry G g)
    (hf : FnCorres bi e entry G f) :
    CorresIsa x86Isa (singletonProgM fn (c.map jToRMMov)) (liftSR fn (SR f))
      (fun a => P a.1 ∧ a.2 = 0) (fun a => (fa a.1, (c.map jToRMMov).length))
      (c.map jToRMMov).length :=
  corresIsa_x86_of_corresJ_mov (SR f) P fa c fn hc
    (corresJ_of_fnCorres SR π P fa c hP hfa hSR hk hg hf)

end CatCrypt.Crypto.SecureCompilation.Ascent.BytesOfCorres
