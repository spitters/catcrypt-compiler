/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxFrontTResultType
public import HaxLean.ScalarOp

/-!
# Integer word results of the `u64` table

A refinement of `ResultType.Hax64Ty` for code over `u64` words and word arrays: `WordTy`
interprets an integer type by the integer values `Value.int`, `unit` by `Value.unit`, and
`array t n` by arrays of `n` values of type `t`. The table `hax64WExit` represents words by
`Value.int`, so `index` and `array_update` at an integer index and the word operations of
`u64WordOps` respect the signature `WordSig` (`hax64WExit_respectWord`).

A function body typed under `WordTy` with no escaping control flow therefore returns, from an
environment typed by `WordTy`, a value of its declared type (`spine_noEsc`). For `mpn_and_n`
this is an array of four `Value.int` words (`mpn_and_n_words`); the source value then has the
form the ABI read-back `wordsAt` produces, with no `Value.uint` or early-return tag.

## Main definitions

* `intTyB` — the integer types.
* `WordTy`, `WordSig` — the value interpretation and the signature.
* `u64WordOps` — the word operations of the signature.

## Main results

* `wordTy_noCF`, `hax64WExit_respectWord` — the conditions of `SpTy.sound`.
* `spine_noEsc` — a body typed with no escapes returns a value of its type.
* `mpn_and_n_wordTy`, `mpn_and_n_words` — `mpn_and_n` returns an array of four integers.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ResultType

open _root_.Hax (ImpExpr ImpType Value Env Outcome Builtins hax64Builtins hax64WordOps
  widthArrayOps u64BinOp)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Hax.TExprTyping (TyEnv TyEnv.extend TyEnv.Le)
open CatCrypt.Hax.TExprTypingSpine

/-! ## The value interpretation and the signature -/

/-- The integer types: `int` and the unsigned and signed word types. -/
def intTyB : ImpType → Bool
  | .int => true
  | .uint _ => true
  | .sint _ => true
  | _ => false

/-- **The word interpretation.** An integer type holds the values `Value.int`; `unit` holds
    `Value.unit`; `array t n` holds arrays of `n` values of type `t`. -/
inductive WordTy : ImpType → Value → Prop where
  | int {τ : ImpType} {k : Int} : intTyB τ = true → WordTy τ (.int k)
  | unit : WordTy .unit .unit
  | array {t : ImpType} {n : Nat} {vs : List Value} :
      (∀ x ∈ vs, WordTy t x) → vs.length = n → WordTy (.array t n) (.array vs)

theorem wordTy_noCF : NoCF WordTy := by
  intro τ v h
  cases h <;> rfl

theorem WordTy.int_inv {τ : ImpType} {v : Value} (h : WordTy τ v) (hτ : intTyB τ = true) :
    ∃ k, v = .int k := by
  cases h with
  | int _ => exact ⟨_, rfl⟩
  | unit => simp [intTyB] at hτ
  | array _ _ => simp [intTyB] at hτ

theorem WordTy.array_inv {t : ImpType} {n : Nat} {v : Value} (h : WordTy (.array t n) v) :
    ∃ vs, v = .array vs ∧ vs.length = n ∧ ∀ x ∈ vs, WordTy t x := by
  cases h with
  | int hτ => simp [intTyB] at hτ
  | array hx hl => exact ⟨_, rfl, hl, hx⟩

/-- The word operations of `WordSig`: the binary `u64` operations of `hax64WordOps` that
    return an integer word. -/
def u64WordOps : List String :=
  ["BitAnd#64", "BitXor#64", "wrapping_add#64", "wrapping_sub#64", "wrapping_mul#64", "Shr#64",
    "mulhi#64"]

/-- The checked additions and subtractions of `hax64WordOps` on unsigned words: the untagged
    `Add`, `Sub` and their unsigned tags `64`, `size`, `8`, `16` and `32`. -/
def checkedWordOps : List String :=
  ["Add", "Add#64", "Add#size", "Sub", "Sub#64", "Sub#size", "Add#8", "Add#16", "Add#32",
    "Sub#8", "Sub#16", "Sub#32"]

/-- The unsigned word types of a checked operation: `u64` and `usize` for the untagged
    operations and the tags `64` and `size`, and for the tags `8`, `16`, `32` the type of the
    tag. -/
def checkedWidthOk (f : String) : _root_.Hax.IntWidth → Bool
  | .w64 | .wsize => f ∈ ["Add", "Add#64", "Add#size", "Sub", "Sub#64", "Sub#size"]
  | .w128 => false
  | w => f == "Add#" ++ w.tag || f == "Sub#" ++ w.tag

/-- **The signature of the word interpretation.** `index` on an array of `t` and an integer
    index gives a `t`; `array_update` on an array of `t`, an integer index and a `t` gives the
    array type; a word operation of `u64WordOps` takes two `u64` words to a `u64` word; a
    checked addition or subtraction of `checkedWordOps` takes two unsigned words of a type
    `checkedWidthOk` admits to a word of the same type. -/
inductive WordSig : String → List ImpType → ImpType → Prop where
  | index {t τi : ImpType} {n : Nat} : intTyB τi = true → WordSig "index" [.array t n, τi] t
  | update {t τi : ImpType} {n : Nat} :
      intTyB τi = true → WordSig "array_update" [.array t n, τi, t] (.array t n)
  | binop {f : String} : f ∈ u64WordOps → WordSig f [.uint .w64, .uint .w64] (.uint .w64)
  | addSize {f : String} {w : _root_.Hax.IntWidth} (hf : f ∈ checkedWordOps := by decide)
      (hw : checkedWidthOk f w = true := by decide) : WordSig f [.uint w, .uint w] (.uint w)

theorem u64BinOp_int {a b : Int} {g : Nat → Nat → Option Nat} {v : Value}
    (h : u64BinOp a b g = some v) : ∃ k, v = .int k := by
  unfold u64BinOp at h
  split at h
  · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
  · cases h

theorem hax64Builtins_wordOp {f : String} (hf : f ∈ u64WordOps) (a b : Int) {v : Value}
    (h : hax64Builtins f [.int a, .int b] = some v) : ∃ k, v = .int k := by
  have hw : ∃ g, hax64WordOps f [.int a, .int b] = u64BinOp a b g := by
    simp only [u64WordOps, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, _root_.Hax.hax64WordOps_bitAnd a b⟩
    · exact ⟨_, _root_.Hax.hax64WordOps_bitXor a b⟩
    · exact ⟨_, _root_.Hax.hax64WordOps_wrapping_add a b⟩
    · exact ⟨_, _root_.Hax.hax64WordOps_wrapping_sub a b⟩
    · exact ⟨_, _root_.Hax.hax64WordOps_wrapping_mul a b⟩
    · exact ⟨_, _root_.Hax.hax64WordOps_shr (a := a) (b := b)⟩
    · exact ⟨_, _root_.Hax.hax64WordOps_mulhi a b⟩
  obtain ⟨g, hg⟩ := hw
  cases hu : u64BinOp a b g with
  | some r =>
    have e : hax64Builtins f [.int a, .int b] = some r := by
      unfold hax64Builtins; rw [hg, hu]; rfl
    rw [e] at h
    cases h
    exact u64BinOp_int hu
  | none =>
    have hwa : widthArrayOps f [.int a, .int b] = none := by
      simp only [u64WordOps, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have e : hax64Builtins f [.int a, .int b] = none := by
      unfold hax64Builtins; rw [hg, hu, hwa]; rfl
    rw [e] at h
    cases h

/-- A call whose arm in `hax64WordOps` on two integers is a `u64BinOp` and which
    `widthArrayOps` does not define returns an integer in the table. -/
theorem hax64Builtins_u64BinOp_int {f : String} {a b : Int} {g : Nat → Nat → Option Nat}
    {v : Value} (hg : hax64WordOps f [.int a, .int b] = u64BinOp a b g)
    (hwa : widthArrayOps f [.int a, .int b] = none)
    (h : hax64Builtins f [.int a, .int b] = some v) : ∃ k, v = .int k := by
  cases hu : u64BinOp a b g with
  | some r =>
    have e : hax64Builtins f [.int a, .int b] = some r := by
      unfold hax64Builtins; rw [hg, hu]; rfl
    rw [e] at h
    cases h
    exact u64BinOp_int hu
  | none =>
    have e : hax64Builtins f [.int a, .int b] = none := by
      unfold hax64Builtins; rw [hg, hu, hwa]; rfl
    rw [e] at h
    cases h

/-- A checked addition or subtraction of `checkedWordOps` on two integers returns an integer
    in the table. -/
theorem hax64Builtins_checkedWordOp {f : String} (hf : f ∈ checkedWordOps) (a b : Int)
    {v : Value} (h : hax64Builtins f [.int a, .int b] = some v) : ∃ k, v = .int k := by
  simp only [checkedWordOps, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_left 6
  iterate 6
    unfold hax64Builtins at h
    first
      | change (_root_.Hax.uintAddOp _ a b <|> none) = some v at h
      | change (_root_.Hax.uintSubOp _ a b <|> none) = some v at h
    simp only [_root_.Hax.uintAddOp, _root_.Hax.uintSubOp] at h
    split at h
    · exact ⟨_, (Option.some.inj h).symm⟩
    · cases h
  · exact hax64Builtins_u64BinOp_int (_root_.Hax.hax64WordOps_add a b) rfl h
  · exact hax64Builtins_u64BinOp_int
      ((_root_.Hax.hax64WordOps_add64_eq_Add (a := a) (b := b)).trans
        (_root_.Hax.hax64WordOps_add a b)) rfl h
  · exact hax64Builtins_u64BinOp_int
      ((_root_.Hax.hax64WordOps_addSize_eq_Add (a := a) (b := b)).trans
        (_root_.Hax.hax64WordOps_add a b)) rfl h
  · exact hax64Builtins_u64BinOp_int (_root_.Hax.hax64WordOps_Sub a b) rfl h
  · exact hax64Builtins_u64BinOp_int
      ((_root_.Hax.hax64WordOps_sub64_eq_Sub (a := a) (b := b)).trans
        (_root_.Hax.hax64WordOps_Sub a b)) rfl h
  · exact hax64Builtins_u64BinOp_int
      ((_root_.Hax.hax64WordOps_subSize_eq_Sub (a := a) (b := b)).trans
        (_root_.Hax.hax64WordOps_Sub a b)) rfl h

/-- **`hax64WExit` respects `WordSig`** under the word interpretation. -/
theorem hax64WExit_respectWord : RespectW WordTy WordSig hax64WExit := by
  intro f ts r hS vs hvs v hv
  cases hS with
  | @index _ τi n hτ =>
    match vs, hvs, hv with
    | [a, i], hvs, hv =>
      obtain ⟨xs, rfl, -, hxs⟩ := (hvs.1 : WordTy (.array r n) a).array_inv
      obtain ⟨k, rfl⟩ := (hvs.2.1 : WordTy τi i).int_inv hτ
      exact hxs v (hax64Builtins_index_mem (hax64WExit_sub hv))
    | [], h, _ => exact h.elim
    | [_], h, _ => exact h.2.elim
    | _ :: _ :: _ :: _, h, _ => exact h.2.2.elim
  | @update t τi n hτ =>
    match vs, hvs, hv with
    | [a, i, u], hvs, hv =>
      obtain ⟨xs, rfl, hl, hxs⟩ := (hvs.1 : WordTy (.array t n) a).array_inv
      obtain ⟨k, rfl⟩ := (hvs.2.1 : WordTy τi i).int_inv hτ
      have hu : WordTy t u := hvs.2.2.1
      obtain ⟨ys, rfl, hyl, hys⟩ := hax64Builtins_update (hax64WExit_sub hv)
      refine .array (fun y hy => ?_) (hyl.trans hl)
      rcases hys y hy with hy | rfl
      · exact hxs y hy
      · exact hu
    | [], h, _ => exact h.elim
    | [_], h, _ => exact h.2.elim
    | [_, _], h, _ => exact h.2.2.elim
    | _ :: _ :: _ :: _ :: _, h, _ => exact h.2.2.2.elim
  | @binop f hf =>
    match vs, hvs, hv with
    | [a, b], hvs, hv =>
      obtain ⟨ka, rfl⟩ := (hvs.1 : WordTy (.uint .w64) a).int_inv rfl
      obtain ⟨kb, rfl⟩ := (hvs.2.1 : WordTy (.uint .w64) b).int_inv rfl
      obtain ⟨k, rfl⟩ := hax64Builtins_wordOp hf ka kb (hax64WExit_sub hv)
      exact .int rfl
    | [], h, _ => exact h.elim
    | [_], h, _ => exact h.2.elim
    | _ :: _ :: _ :: _, h, _ => exact h.2.2.elim
  | @addSize f w hf _ =>
    match vs, hvs, hv with
    | [a, b], hvs, hv =>
      obtain ⟨ka, rfl⟩ := (hvs.1 : WordTy (.uint w) a).int_inv rfl
      obtain ⟨kb, rfl⟩ := (hvs.2.1 : WordTy (.uint w) b).int_inv rfl
      obtain ⟨k, rfl⟩ := hax64Builtins_checkedWordOp hf ka kb (hax64WExit_sub hv)
      exact .int rfl
    | [], h, _ => exact h.elim
    | [_], h, _ => exact h.2.elim
    | _ :: _ :: _ :: _, h, _ => exact h.2.2.elim

/-! ## Bodies with no escapes -/

/-- **A body typed with no escapes returns a value of its type.** Under an interpretation
    with no control-flow values and a table respecting the signature, a run of `denoteSpine`
    of an expression typed at `T` with no admitted escapes, from an environment typed by `Γ`,
    to a value `v` gives `W T v`. -/
theorem spine_noEsc {W : ValTy} {S : RSig} {bi : Builtins} (hW : NoCF W)
    (hbi : RespectW W S bi) {Γ : TyEnv} {T : ImpType} {e : ImpExpr}
    (h : SpTy W S Γ (fun _ => False) e T) {fuel : Nat} {env env' : Env} {v : Value}
    (henv : EnvW W Γ env) (hrun : (denoteSpine bi fuel e).run env = (.val v, env')) :
    W T v := by
  have h1 := SpTy.sound hW hbi h fuel env henv
  rw [← SpTy.denoteSpine_eq h bi fuel] at h1
  have hr : denoteSpine bi fuel e env = (.val v, env') := hrun
  rw [hr] at h1
  rcases h1.1 with ho | ⟨-, ho⟩
  · exact ho
  · exact ho.elim

/-! ## `mpn_and_n` -/

/-- **`mpn_and_n` is typed under the word interpretation** at its declared result type, with
    no escapes. -/
theorem mpn_and_n_wordTy :
    SpTy WordTy WordSig andTyEnv (fun _ => False) Mpn.mpn_and_n_texpr.erase
      Mpn.mpn_and_n_texpr.ty := by
  show SpTy WordTy WordSig andTyEnv (fun _ => False) Mpn.mpn_and_n_impExpr Mpn.ty_1
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .letBind (.var rfl) (le_extend_same rfl) ?_
  refine .seq (σ := .unit) ?_ (.var rfl)
  refine .forFold (σ₁ := Mpn.ty_8) (σ₂ := Mpn.ty_8) (τi := Mpn.ty_8) (σb := .unit)
    (.lit (.int rfl)) (.var rfl) (fun k => .int rfl) (le_extend_new rfl) ?_ .unit
  refine .letBind (τ₁ := Mpn.ty_7)
    (.app (.index (n := 4) rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))
    (le_extend_new rfl) ?_
  refine .letBind (τ₁ := Mpn.ty_7)
    (.app (.index (n := 4) rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))
    (le_extend_new rfl) ?_
  refine .seq (σ := .unit) (.seq (σ := Mpn.ty_1) ?_ (.unitVal .unit)) (.unitVal .unit)
  refine .letBind (τ₁ := Mpn.ty_1) ?_ (le_extend_same rfl) (.var rfl)
  refine .app (.update (n := 4) (τi := Mpn.ty_8) rfl)
    (.cons (.var rfl) (.cons (.var rfl) (.cons ?_ .nil)))
  exact .app (.binop (by simp [u64WordOps])) (.cons (.var rfl) (.cons (.var rfl) .nil))

/-- **`mpn_and_n` returns four integer words.** From every environment typed by `andTyEnv`
    under the word interpretation, a run of `denoteSpine hax64WExit` on `mpn_and_n`'s
    extraction to a value `v` gives an array of four `Value.int` words. -/
theorem mpn_and_n_words {fuel : Nat} {env env' : Env} {v : Value}
    (henv : EnvW WordTy andTyEnv env)
    (hrun : (denoteSpine hax64WExit fuel Mpn.mpn_and_n_texpr.erase).run env = (.val v, env')) :
    ∃ zs : List Int, v = .array (zs.map .int) ∧ zs.length = 4 := by
  obtain ⟨vs, rfl, hl, hx⟩ :=
    (spine_noEsc wordTy_noCF hax64WExit_respectWord mpn_and_n_wordTy henv hrun).array_inv
  have hint : ∀ x ∈ vs, ∃ k, x = .int k := fun x hx' => (hx x hx').int_inv rfl
  refine ⟨vs.map fun x => match x with | .int k => k | _ => 0, ?_, by simpa using hl⟩
  congr 1
  rw [List.map_map]
  conv_lhs => rw [← List.map_id vs]
  refine List.map_congr_left fun x hx' => ?_
  obtain ⟨k, rfl⟩ := hint x hx'
  rfl

end CatCrypt.Crypto.Hax.ResultType
