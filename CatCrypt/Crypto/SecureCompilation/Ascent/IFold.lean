/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# The index-folded iterate `ifold`

`ifold fa N = fa (N-1) ∘ … ∘ fa 1 ∘ fa 0` is the `N`-fold application of an
index-dependent step `fa : Nat → A → A`, peeling the last application. It is the
abstract side of the counted-loop rules over `semScalar` (`MlkemPolyFoldCorres`) and
over the `RustM` square (`RustMSquareLoop`). The module uses only Lean core.

## Main definitions

* `ifold` — the index-dependent iterate
* `ifold_invariant` — a predicate preserved by every step is preserved by `ifold`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-- `N`-fold application of the index-dependent step `fa`, peeling the last
    trip (`n+1 ↦ fa n ∘ ifold fa n`). -/
def ifold {A : Type} (fa : Nat → A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => fa n (ifold fa n a)

/-- The index-folded iterate preserves any predicate preserved by every step. -/
theorem ifold_invariant {A : Type} {fa : Nat → A → A} {P : A → Prop}
    (hinv : ∀ n a, P a → P (fa n a)) : ∀ (N : Nat) (a : A), P a → P (ifold fa N a) := by
  intro N
  induction N with
  | zero => intro a ha; exact ha
  | succ n ih => intro a ha; exact hinv n _ (ih a ha)

end CatCrypt.Crypto.SecureCompilation.Ascent
