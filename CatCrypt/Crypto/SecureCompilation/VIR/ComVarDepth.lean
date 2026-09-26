/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# The de Bruijn index of a context variable

`varDepth v` is the de Bruijn index of `v : Ctxt.Var Γ t`: `.here` has index `0` and each
`.there` adds one. It is the number of binders between the use and its binding, and the
position of the variable's type in `Γ` counted from the head.

## Main definitions

* `varDepth`: the de Bruijn index of a variable, over every dialect.

## Main results

* `varDepth_lt`: the index is below the length of the context.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

/-- The de Bruijn index of a variable: `.here` is `0`, each `.there` adds one. -/
def varDepth {d : Dialect} : {Γ : Ctxt d} → {t : d.Ty} → Ctxt.Var Γ t → Nat
  | _, _, .here => 0
  | _, _, .there v => varDepth v + 1

/-- The head variable has index `0`. -/
@[simp]
theorem varDepth_here {d : Dialect} {Γ : Ctxt d} {t : d.Ty} :
    varDepth (Ctxt.Var.here : Ctxt.Var (t :: Γ) t) = 0 := rfl

/-- A shifted variable's index is one more than the variable's. -/
@[simp]
theorem varDepth_there {d : Dialect} {Γ : Ctxt d} {t s : d.Ty} (v : Ctxt.Var Γ t) :
    varDepth (Ctxt.Var.there (s := s) v) = varDepth v + 1 := rfl

/-- The de Bruijn index of a variable is below the length of its context. -/
theorem varDepth_lt {d : Dialect} : ∀ {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t),
    varDepth v < Γ.length
  | _, _, .here => by simp
  | _, _, .there v => by have := varDepth_lt v; simp; omega

end CatCrypt.Crypto.SecureCompilation.VIR
