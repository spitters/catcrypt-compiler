/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-!
# The leakage run of an embedded straight-line program

A straight-line program `c : Com d Γ t` embeds into normal form as `NFProg.ofCom c`. Its
leakage run is the denotation of `c` with the events `Com.ctLeak M c`, so a straight-line
program whose events do not depend on the valuation is constant time in the sense of `NFCT`,
at every labels and fuel. The hash templates (`HashTemplate.Sha2`, `HashTemplate.Blake2`,
`HashTemplate.Keccak`) prove their events fixed and reach `NFCT` through this module.

## Main statements

* `NFProg.leakRun_ofCom`: the leakage run of `NFProg.ofCom c` returns the denotation of `c`
  and its events `Com.ctLeak M c`.
* `nfct_ofCom_of_fixed`: fixed events of `c` give `NFCT M L fuel (NFProg.ofCom c)` for every
  `L` and `fuel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open Ctxt (Valuation)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- **The leakage run of an embedded straight-line program** returns its denotation and its
    events `Com.ctLeak`. -/
theorem NFProg.leakRun_ofCom (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) (V : Valuation Γ) :
    NFProg.leakRun M fuel (NFProg.ofCom c) V = some (.cons (c.denote V) .nil, Com.ctLeak M c V) := by
  induction c with
  | ret v => rfl
  | var e k ih =>
    simp only [NFProg.ofCom, NFProg.leakRun, ih, Option.map_some, Com.ctLeak]
    rfl

/-- **An embedded straight-line program with fixed events is constant time** at every
    labels and fuel. -/
theorem nfct_ofCom_of_fixed (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (h : ∀ V₁ V₂ : Valuation Γ, Com.ctLeak M c V₁ = Com.ctLeak M c V₂) :
    ∀ (L : Labels Γ) (fuel : Nat), NFCT M L fuel (NFProg.ofCom c) := by
  intro L fuel V₁ V₂ _
  rw [NFProg.leakRun_ofCom, NFProg.leakRun_ofCom, Option.map_some, Option.map_some, h V₁ V₂]

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
