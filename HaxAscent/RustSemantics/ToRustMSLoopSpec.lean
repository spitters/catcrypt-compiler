/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMS

/-!
# The invariant rule of the counted loop of the state-passing reading

`loopS step k i ρ` runs `step` on the `k` indices from `i`. `loopS_triple` is its `Std.Do`
rule for an invariant indexed by the loop index: a step that takes the invariant at an index
`i` in `[lo, hi)` to the invariant at `i + 1` gives the invariant at `i + k` after `k` steps
from `i`. The rule is applied by `mvcgen` after it is specialised to the bounds, the invariant
and the step of the loop at hand:

```
have hloop := fun ρ h => loopS_triple (lo := 0) (hi := n) (Inv := I) (step := s) hstep n 0 ρ
  (Nat.zero_le 0) (by omega) h
mvcgen [hloop]
```

`loopS_triple_const` is the instance at an invariant that does not depend on the index.

The leaf equations rewrite a call of the reading `appRt` of the runtime operations on
values in constructor form, which is the form a `simp` call that steps a loop body meets:
`index` and `array_update` to `appIndex` and `appUpdate`, these on an array, a loop index
below the length and a word to the entry and to the updated array, and a tagged binary word
operation on two words of its width to the Aeneas operation. The name of a tagged operation
is a string literal in an extracted program, and `appRt_wordOp` takes the routing of the
name as a hypothesis that `rfl` proves at a literal:
`appRt_wordOp (f := "BitXor#64") rfl`.

## Main results

* `loopS_triple`, `loopS_triple_const`
* `usize_ofNat_val`, `appRt_index`, `appRt_array_update`, `appIndex_arr_ctr`,
  `appUpdate_arr_ctr`
* `appRt_wordOp`, `appWord_w`, `appRt_wordOp_w`
-/

@[expose] public section

set_option autoImplicit false
set_option mvcgen.warning false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std Aeneas.Std.WP Std.Do

/-! ## The loop rule -/

/-- **The invariant rule of `loopS`.** A step that takes the invariant at an index `i` in
    `[lo, hi)` to the invariant at `i + 1` gives the invariant at `i + k` after `k` steps
    from `i`, when `lo ≤ i` and `i + k ≤ hi`. -/
theorem loopS_triple {step : Nat → AEnv → RustM AEnv} {Inv : Nat → AEnv → Prop}
    {lo hi : Nat}
    (hstep : ∀ (i : Nat) (ρ : AEnv), lo ≤ i → i < hi → Inv i ρ →
      ⦃⌜True⌝⦄ step i ρ ⦃⇓ ρ' => ⌜Inv (i + 1) ρ'⌝⦄) :
    ∀ (k i : Nat) (ρ : AEnv), lo ≤ i → i + k ≤ hi → Inv i ρ →
      ⦃⌜True⌝⦄ loopS step k i ρ ⦃⇓ ρ' => ⌜Inv (i + k) ρ'⌝⦄
  | 0, i, ρ, _, _, h => by
    simp only [loopS]
    mvcgen
  | k + 1, i, ρ, hl, hk, h => by
    have h1 := hstep i ρ hl (by omega) h
    have ih := fun ρ' h' => loopS_triple hstep k (i + 1) ρ' (by omega) (by omega) h'
    simp only [loopS]
    mvcgen [h1, ih]
    all_goals grind

/-- The invariant rule of `loopS` at an invariant that does not depend on the index. -/
theorem loopS_triple_const {step : Nat → AEnv → RustM AEnv} {Q : AEnv → Prop} {lo hi : Nat}
    (hstep : ∀ (i : Nat) (ρ : AEnv), lo ≤ i → i < hi → Q ρ →
      ⦃⌜True⌝⦄ step i ρ ⦃⇓ ρ' => ⌜Q ρ'⌝⦄)
    (k i : Nat) (ρ : AEnv) (hl : lo ≤ i) (hk : i + k ≤ hi) (h : Q ρ) :
    ⦃⌜True⌝⦄ loopS step k i ρ ⦃⇓ ρ' => ⌜Q ρ'⌝⦄ :=
  loopS_triple (Inv := fun _ => Q) hstep k i ρ hl hk h

/-! ## The leaf equations of `appRt` -/

/-- The `usize` word of a natural number below `2 ^ w`, for `w` the width of `usize`. -/
theorem usize_ofNat_val {i : Nat} (hi : i < 2 ^ UScalarTy.Usize.numBits) :
    (⟨BitVec.ofNat UScalarTy.Usize.numBits i⟩ : UScalar .Usize).val = i := by
  simp only [UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hi

@[simp] theorem appRt_index (a i : AVal) : appRt "index" [a, i] = appIndex a i := by
  rfl

@[simp] theorem appRt_array_update (a i v : AVal) :
    appRt "array_update" [a, i, v] = appUpdate a i v := by
  rfl

/-- `index` of an array at a loop index below its length returns the entry. -/
theorem appIndex_arr_ctr {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n)
    {i : Nat} (hi : i < n.val) :
    appIndex (.arr ty n a) (ctr i) = .ok (.w ty a.val[i]!) := by
  have hn := n.hBounds
  have hl : a.val.length = n.val := a.property
  simp [appIndex, ctr, AVal.asW, Aeneas.Std.Array.index_usize,
    usize_ofNat_val (Nat.lt_trans hi hn), hl, hi]

/-- `array_update` of an array at a loop index below its length by a word of its width
    returns the array with that entry set. -/
theorem appUpdate_arr_ctr {ty : UScalarTy} {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n)
    {i : Nat} (hi : i < n.val) (x : UScalar ty) :
    appUpdate (.arr ty n a) (ctr i) (.w ty x) =
      .ok (.arr ty n (a.set ⟨BitVec.ofNat UScalarTy.Usize.numBits i⟩ x)) := by
  have hn := n.hBounds
  have hl : a.val.length = n.val := a.property
  simp [appUpdate, ctr, AVal.asW, Aeneas.Std.Array.update, Aeneas.Std.Array.set,
    usize_ofNat_val (Nat.lt_trans hi hn), hl, hi]
  rfl

/-- A name that `wordOpAt?` routes to the operation `o` at the width `ty` is read by
    `appRt` as `appWord ty o`. -/
theorem appRt_wordOp {f : String} {ty : UScalarTy} {o : WordOp}
    (hf : wordOpAt? f = some (ty, o)) (a b : AVal) : appRt f [a, b] = appWord ty o a b := by
  simp only [appRt, hf]

/-- A tagged binary word operation on two words of its width is the Aeneas operation. -/
@[simp] theorem appWord_w (ty : UScalarTy) (o : WordOp) (x y : UScalar ty) :
    appWord ty o (.w ty x) (.w ty y) = (o.aen x y >>= fun r => RustM.ok (.w ty r)) := by
  simp [appWord, AVal.asW]

/-- A name that `wordOpAt?` routes to `o` at `ty` is read by `appRt`, on two words of the
    width `ty`, as the Aeneas operation. -/
theorem appRt_wordOp_w {f : String} {ty : UScalarTy} {o : WordOp}
    (hf : wordOpAt? f = some (ty, o)) (x y : UScalar ty) :
    appRt f [.w ty x, .w ty y] = (o.aen x y >>= fun r => RustM.ok (.w ty r)) := by
  rw [appRt_wordOp hf, appWord_w]

end CatCrypt.Hax.RustSemantics
