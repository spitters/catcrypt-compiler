/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts

/-!
# The order of the statements of R3

Four statements relate, for a module compiled by `compileA`, the source call tree of the entry to
the target call trees of the decoded calling body; they share the decoding of the bytes and the
quantification over entry states and source environments, and differ in four places.

* `R3Statement` (`TargetCallTree`): `Rutt` at `contractRE` and `contractRA`, at one target fuel.
  Every source event is matched by a target event.
* `R3StatementC` (`RegionLinkContract`): `RuttS` at the source handler `linkHandler m` (a source
  event may be answered by the meaning of the linked function without a target event), at
  `contractRE` and the answer relation of the separation contracts `contractRAC`, at one target
  fuel.
* `R3StatementF` (`NFProgCallTreeCalls`): `RuttF`, the relation of `R3StatementC` with the target
  fuel chosen per segment of the target family.
* `R3StatementFG` (`NFProgCallTreeContracts`): `R3StatementF` at `contractREG`, which asks the
  precondition of a linked function at a matched call only where its meaning is defined on the
  arguments.

Each statement implies the next, and none of the converses is proved: `contractRAC` relates
fewer answers than `contractRA` (it adds the separation contract), so `Rutt` at `contractRA`
relates continuations at more answer pairs; `Rutt` is `RuttS` without skipped events; a relation
at one fuel is a relation at a fuel per segment; and `contractRE` implies `contractREG`. The
weakest, `R3StatementFG`, is the statement the front and the back half establish
(`NFProgCallTreeModule.r3FG_of_front`); its consequence under a handler meeting the separation
contracts is `NFProgCallTreeContracts.r3fg_consequence`.

## Main results

* `RuttS.anti_ra`: a relation by `RuttS` holds at every smaller answer relation.
* `r3StatementC_of_r3Statement`: `R3Statement` implies `R3StatementC`.
* `r3StatementFG_of_r3StatementC`, `r3StatementFG_of_r3Statement`: `R3StatementC` and
  `R3Statement` imply `R3StatementFG`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeStatements

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract

/-- **Antitonicity in the answer relation**: trees related by `RuttS` at `RA` are related at
    every answer relation contained in `RA`. -/
theorem RuttS.anti_ra {E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA RA' : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (hA : ∀ e₁ e₂ a₁ a₂, RA' e₁ e₂ a₁ a₂ → RA e₁ e₂ a₁ a₂) {t₁ : CallTree E₁ R₁}
    {t₂ : CallTree E₂ R₂} (h : RuttS h₁ RE RA RR Fail t₁ t₂) : RuttS h₁ RE RA' RR Fail t₁ t₂ := by
  induction h with
  | ret h => exact .ret h
  | fail h => exact .fail h
  | vis he _ ih => exact .vis he fun a₁ a₂ ha => ih a₁ a₂ (hA _ _ _ _ ha)
  | skip _ ih => exact .skip ih

/-- **`R3Statement` implies `R3StatementC`**: `Rutt` is `RuttS` without skipped events, and
    `contractRAC` implies `contractRA`. -/
theorem r3StatementC_of_r3Statement (h : R3Statement) : R3StatementC := by
  intro m σ fname P bytes hc hnd hk
  obtain ⟨pc, Q, sym, hd, hrel⟩ := h m σ fname P bytes hc hnd hk
  refine ⟨pc, Q, sym, hd, fun sa hreg env henv fuelC fuel => ?_⟩
  obtain ⟨fuelT, hr⟩ := hrel sa hreg env henv fuelC fuel
  exact ⟨fuelT, RuttS.anti_ra (fun _ _ _ _ ha => contractRA_of_contractRAC ha) (RuttS.of_rutt hr)⟩

/-- **`R3StatementC` implies `R3StatementFG`**, through `R3StatementF`. -/
theorem r3StatementFG_of_r3StatementC (h : R3StatementC) :
    NFProgCallTreeContracts.R3StatementFG :=
  NFProgCallTreeContracts.r3StatementFG_of_r3StatementF
    (NFProgCallTreeCalls.r3StatementF_of_r3StatementC h)

/-- **`R3Statement` implies `R3StatementFG`.** -/
theorem r3StatementFG_of_r3Statement (h : R3Statement) : NFProgCallTreeContracts.R3StatementFG :=
  r3StatementFG_of_r3StatementC (r3StatementC_of_r3Statement h)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeStatements
