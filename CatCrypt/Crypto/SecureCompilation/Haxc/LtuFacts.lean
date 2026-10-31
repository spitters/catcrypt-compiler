/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.WordResult
public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteProg
public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteFrame
public import CatCrypt.Crypto.SecureCompilation.Haxc.Consts
public import CatCrypt.Crypto.Hax.HaxFrontTResultWords

@[expose] public section

set_option autoImplicit false

/-!
# The source facts of `ltu`

`ltu` (from `mpn-hax`) is the branch-free unsigned comparison of two words `x` and `y`. It reads
the crate constant `ONES` (all bits set), which its System V layout `ltuAbi` binds in the source
environment; `ltuK` is the extraction with that constant bound at its head (`bindConsts`).

Under the word interpretation `WordTy`, `ltuK` is typed at `u64` with no escapes
(`ltuK_wordTy`), so every source run from an environment the layout reads off an entry state
returns an integer (`ltu_wordScalResult`), the source condition of the word route.

## Main results

* `ltuAbi`, `ltuK` — the layout of `ltu` and its extraction with `ONES` bound.
* `ltuK_erase` — the reading of `ltuK` is `let ONES = 2^64 - 1` around that of `ltu`.
* `ltuTyEnv`, `ltuK_wordTy` — the parameter types and the typing of `ltuK`.
* `envW_ltu`, `ltu_wordScalResult` — the source condition of the word route.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Hax.TExprTyping (TyEnv TyEnv.extend)
open CatCrypt.Hax.TExprTypingSpine
open CatCrypt.Crypto.Hax.ResultType (WordTy WordSig u64WordOps le_extend_new le_extend_same
  wordTy_noCF hax64WExit_respectWord spine_noEsc)
open _root_.Hax (Value Env ImpExpr ImpLit)

/-- The System V layout of `ltu`: `x` in `%rdi`, `y` in `%rsi`, the constant `ONES` as the
    word with all bits set, the result in `%rax`, the stack words from `-256` to `-8` below
    the entry stack pointer. -/
def ltuAbi : AbiLayout where
  args := [⟨"x", "%rdi", .scalar⟩, ⟨"y", "%rsi", .scalar⟩]
  consts := [("ONES", .int (2 ^ 64 - 1))]
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8

/-- The extraction of `ltu` with the constants of `ltuAbi` bound at its head. -/
def ltuK : _root_.Hax.TExpr := bindConsts ltuAbi.consts Mpn.ltu_texpr

theorem ltuK_erase :
    ltuK.erase = .letBind "ONES" (.lit (.int (2 ^ 64 - 1))) Mpn.ltu_impExpr := rfl

/-- The parameter types of `ltu`: the words `x` and `y`. -/
def ltuTyEnv : TyEnv :=
  TyEnv.extend (TyEnv.extend (fun _ => none) "x" Mpn.ty_7) "y" Mpn.ty_7

/-- **`ltuK` is typed at `u64`** under the word interpretation, with no escapes. -/
theorem ltuK_wordTy :
    SpTy WordTy WordSig ltuTyEnv (fun _ => False) ltuK.erase Mpn.ty_7 := by
  rw [ltuK_erase]
  have hop : ∀ f, f ∈ u64WordOps → WordSig f [.uint .w64, .uint .w64] (.uint .w64) :=
    fun _ hf => .binop hf
  refine .letBind (τ₁ := Mpn.ty_7) (.lit (.int rfl)) (le_extend_new rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (τ₁ := Mpn.ty_7) (.app (hop _ (by simp [u64WordOps]))
    (.cons (.app (hop _ (by simp [u64WordOps])) (.cons (.var rfl) (.cons (.var rfl) .nil)))
      (.cons (.var rfl) .nil))) (le_extend_new rfl) ?_
  refine .letBind (τ₁ := Mpn.ty_7) (.app (hop _ (by simp [u64WordOps]))
    (.cons (.app (hop _ (by simp [u64WordOps]))
        (.cons (.app (hop _ (by simp [u64WordOps])) (.cons (.var rfl) (.cons (.var rfl) .nil)))
          (.cons (.var rfl) .nil)))
      (.cons (.app (hop _ (by simp [u64WordOps])) (.cons (.var rfl) (.cons (.var rfl) .nil)))
        .nil))) (le_extend_new rfl) ?_
  exact .app (hop _ (by simp [u64WordOps]))
    (.cons (.app (hop _ (by simp [u64WordOps]))
        (.cons (.app (hop _ (by simp [u64WordOps])) (.cons (.var rfl) (.cons (.var rfl) .nil)))
          (.cons (.app (hop _ (by simp [u64WordOps])) (.cons (.var rfl) (.cons (.var rfl) .nil)))
            .nil)))
      (.cons (.lit (.int rfl)) .nil))

/-- An environment `ltuAbi` reads off an entry state is typed by `ltuTyEnv` under the word
    interpretation. -/
theorem envW_ltu {sa : AState} {env : Env} (henv : ltuAbi.EnvOf sa env) :
    EnvW WordTy ltuTyEnv env := by
  have hx := henv.1 ⟨"x", "%rdi", .scalar⟩ (by simp [ltuAbi])
  have hy := henv.1 ⟨"y", "%rsi", .scalar⟩ (by simp [ltuAbi])
  intro n τ hn
  simp only [ltuTyEnv, TyEnv.extend] at hn
  split_ifs at hn with h1 h2
  · cases hn; rw [eq_of_beq h1]; exact ⟨_, hy, .int rfl⟩
  · cases hn; rw [eq_of_beq h2]; exact ⟨_, hx, .int rfl⟩

/-- **The source condition of `ltu`**: every run of `ltuK` from an environment `ltuAbi` reads
    off an entry state returns an integer. -/
theorem ltu_wordScalResult : WordScalResult ltuAbi ltuK := by
  intro sa env fuel v env' _ henv hrun
  exact (spine_noEsc wordTy_noCF hax64WExit_respectWord ltuK_wordTy (envW_ltu henv) hrun).int_inv
    rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect
