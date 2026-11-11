/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
public import CatCrypt.Crypto.SecureCompilation.Haxc.Consts

/-!
# The constants of a layout at the level of call trees

The translation `haxToNF` of the front reads the entry of a module with the constants of the
layout bound in front of it (`bindConsts σ.consts`). A binding of a constant to a literal performs
no event, and from an environment that already binds the constant to its value it leaves the
environment unchanged, so the call tree of the bound extraction is the call tree of the
extraction, at every tree table and fuel (`nfTree_bindConsts`), and at a layout from every source
environment the layout reads off an entry state (`nfTree_bindConsts_of_envOf`).

## Main results

* `nfTree_bindConsts`: the call tree of `bindConsts cs te` from an environment binding the
  constants of `cs` is the call tree of `te`.
* `nfTree_bindConsts_of_envOf`: the same from a source environment of a layout.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeConsts

open _root_.Hax
open _root_.Hax.InlineLocalClosures
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree

variable {E : EventSig}

/-- **The call tree of the bound extraction is the call tree of the extraction.** From an
    environment binding every constant of `cs` to its value, the call tree of
    `bindConsts cs te` at every tree table and fuel is the call tree of `te`. -/
theorem nfTree_bindConsts (bt : TreeTable E) (fuel : Nat) (te : TExpr) :
    ∀ (cs : List (String × Value)) (env : Env), (∀ c ∈ cs, env c.1 = some c.2) →
      nfTree bt fuel (bindConsts cs te).erase env = nfTree bt fuel te.erase env
  | [], _, _ => rfl
  | (k, v) :: cs, env, hc => by
    have ih := nfTree_bindConsts bt fuel te cs env fun c hc' => hc c (List.mem_cons_of_mem _ hc')
    simp only [bindConsts]
    split
    · rename_i l hl
      have hk : env k = some v := hc (k, v) List.mem_cons_self
      rw [TExpr.erase, TExpr.erase]
      show denoteSpineT bt fuel (.letBind k (.lit l) (bindConsts cs te).erase) env = _
      rw [denoteSpineT]
      · unfold constLit at hl
        split at hl <;> cases hl <;> rw [denoteT]
        · show denoteSpineT bt fuel (bindConsts cs te).erase (env.extend k (.int _)) = _
          rw [extend_of_eq hk]
          exact ih
        · show denoteSpineT bt fuel (bindConsts cs te).erase (env.extend k (.bool _)) = _
          rw [extend_of_eq hk]
          exact ih
      · intro _ _ h
        cases h
    · exact ih

/-- **The call tree of the bound extraction at a layout.** From a source environment the layout
    `σ` reads off an entry state, the call tree of `bindConsts σ.consts te` is the call tree of
    `te`. -/
theorem nfTree_bindConsts_of_envOf (bt : TreeTable E) (fuel : Nat) (te : TExpr)
    {σ : AbiLayout} {sa : CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.AState} {env : Env}
    (h : σ.EnvOf sa env) :
    nfTree bt fuel (bindConsts σ.consts te).erase env = nfTree bt fuel te.erase env :=
  nfTree_bindConsts bt fuel te σ.consts env h.2.1

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeConsts
