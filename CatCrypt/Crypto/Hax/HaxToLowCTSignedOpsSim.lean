/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxRuntimeWordBuiltins
public import CatCrypt.Crypto.Hax.HaxToLowCTSignedOps

/-!
# Straight-line simulation of the signed word operations in `semScalar`

The per-binding simulation of the signed bindings `scalarizeSignedIn` lowers, between
the hax semantics `denote` and the value semantics `semScalar`.  A signed value is
related as a hax `.int z` with `z ∈ [-2^63, 2^63)` against the `.sword 64` slot
`BitVec.ofInt 64 z` (`IntAt`); `EnvRelS` extends the word and array relation `EnvRelW`
by a list of such names.  A name related as a word below `2^64` holds
`BitVec.ofNat 64 n = BitVec.ofInt 64 n`, so the operands of a signed operation or
conversion may be words or signed values (`EnvRelS.read`).

## Main definitions

* `IntAt`, `EnvRelS` — the signed values and the environment relation.
* `SignedBuiltins` — the facts a builtin table evaluates the signed operations,
  conversions and comparisons by.

## Main results

* `EnvRelS.read`, `EnvRelS.readInt`, `EnvRelS.update_int`, `EnvRelS.update_word`,
  `EnvRelS.preserve` — reading an operand and updating the relation.
* `semStep_setExpr` — a scalar assignment `semLowerSExpr` accepts runs, binding only its
  destination outside the temporaries.
* `step_signed`, `step_signedCast`, `step_residueCast`, `step_signedCmp` — one binding
  of a signed operation, a signed conversion, a residue conversion or a signed comparison
  preserves `EnvRelS`, with the hax run and the `semScalar` run each reduced to the run
  of the continuation.
* `hax64Builtins_signedBuiltins` — `SignedBuiltins Hax.hax64Builtins`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.WordOpsSim

open _root_.Hax (ImpExpr Value Env Builtins denote hax64Builtins hax64WordOps sintShlOp
  sintShrOp hax64WordOps_Lt hax64WordOps_Gt hax64WordOps_Le hax64WordOps_Ge)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar semScalar envReader envReadU64 isTmpName)
open CatCrypt.Crypto.SecureCompilation.Ascent (sextSExpr asrSExpr sltSExpr signMaskSExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt (ltExpr carryExpr)
open CatCrypt.Crypto.Hax (SignedOp signedOpOf signedOpOf_width SignedOp.int_range
  signedCastOf signedCastOf_width residueCastOf residueCastOf_width SignedCmp signedCmpOf
  evalBV_signedCast toNat_residueCast)

/-! ### The environment relation -/

/-- `x` holds a signed value: `.int z` with `z ∈ [-2^63, 2^63)` in hax and its two's
    complement `BitVec.ofInt 64 z` at `.sword 64` in the scalar environment. -/
def IntAt (env : Env) (σ : SEnvScalar) (x : String) : Prop :=
  ∃ z : Int, -2 ^ 63 ≤ z ∧ z < 2 ^ 63 ∧ env x = some (.int z) ∧
    σ x = some ⟨.sword 64, (BitVec.ofInt 64 z : BitVec 64)⟩

/-- The hax environment `env` and the scalar environment `σ` agree on the words `S` and
    the arrays `A` (`EnvRelW`) and on the signed values `I`, none of which is a
    temporary of the scalar-expression lowering. -/
structure EnvRelS (env : Env) (σ : SEnvScalar) (S I : List String)
    (A : List (String × Nat)) : Prop where
  rel : EnvRelW env σ S A
  int : ∀ x ∈ I, IntAt env σ x
  intClean : ∀ x ∈ I, ¬ isTmpName x

/-- A name related as a word or as a signed value holds the two's complement of its
    integer. -/
theorem EnvRelS.read {env : Env} {σ : SEnvScalar} {S I : List String}
    {A : List (String × Nat)} (h : EnvRelS env σ S I A) {a : String} (ha : a ∈ S ∨ a ∈ I) :
    ∃ z : Int, env a = some (.int z) ∧ envReadU64 σ a = some (BitVec.ofInt 64 z) ∧
      ¬ isTmpName a := by
  rcases ha with ha | ha
  · obtain ⟨n, _, he, hs⟩ := h.rel.word a ha
    exact ⟨n, he, by simp only [envReadU64, hs, BitVec.ofInt_natCast], h.rel.wordClean a ha⟩
  · obtain ⟨z, _, _, he, hs⟩ := h.int a ha
    exact ⟨z, he, by simp only [envReadU64, hs], h.intClean a ha⟩

/-- A name related as a signed value holds the two's complement of an `i64` value. -/
theorem EnvRelS.readInt {env : Env} {σ : SEnvScalar} {S I : List String}
    {A : List (String × Nat)} (h : EnvRelS env σ S I A) {a : String} (ha : a ∈ I) :
    ∃ z : Int, -2 ^ 63 ≤ z ∧ z < 2 ^ 63 ∧ env a = some (.int z) ∧
      envReadU64 σ a = some (BitVec.ofInt 64 z) ∧ ¬ isTmpName a := by
  obtain ⟨z, h1, h2, he, hs⟩ := h.int a ha
  exact ⟨z, h1, h2, he, by simp only [envReadU64, hs], h.intClean a ha⟩

/-- Writing a slot `x` outside the words `S` and the arrays `A` preserves the word and
    array relation. -/
theorem EnvRelW.preserve {env env' : Env} {σ σ' : SEnvScalar} {S : List String}
    {A : List (String × Nat)} (h : EnvRelW env σ S A) (x : String) (hxS : x ∉ S)
    (hxA : ∀ p ∈ A, p.1 ≠ x) (henv : ∀ y, y ≠ x → env' y = env y)
    (hσ : ∀ y, y ≠ x → ¬ isTmpName y → σ' y = σ y) : EnvRelW env' σ' S A where
  word y hy := by
    have hyx : y ≠ x := fun e => hxS (e ▸ hy)
    obtain ⟨n, hn, he, hs⟩ := h.word y hy
    exact ⟨n, hn, by rw [henv y hyx, he], by rw [hσ y hyx (h.wordClean y hy), hs]⟩
  arr p hp := by
    obtain ⟨vs, a, he, hs, hl, hc⟩ := h.arr p hp
    exact ⟨vs, a, by rw [henv _ (hxA p hp), he], by rw [hσ _ (hxA p hp) (h.arrClean p hp), hs],
      hl, hc⟩
  wordClean := h.wordClean
  arrClean := h.arrClean

/-- Writing a slot `x` outside the words `S`, the signed values `I` and the arrays `A`
    preserves the relation. -/
theorem EnvRelS.preserve {env env' : Env} {σ σ' : SEnvScalar} {S I : List String}
    {A : List (String × Nat)} (h : EnvRelS env σ S I A) (x : String) (hxS : x ∉ S)
    (hxI : x ∉ I) (hxA : ∀ p ∈ A, p.1 ≠ x) (henv : ∀ y, y ≠ x → env' y = env y)
    (hσ : ∀ y, y ≠ x → ¬ isTmpName y → σ' y = σ y) : EnvRelS env' σ' S I A where
  rel := h.rel.preserve x hxS hxA henv hσ
  int y hy := by
    have hyx : y ≠ x := fun e => hxI (e ▸ hy)
    obtain ⟨z, h1, h2, he, hs⟩ := h.int y hy
    exact ⟨z, h1, h2, by rw [henv y hyx, he], by rw [hσ y hyx (h.intClean y hy), hs]⟩
  intClean := h.intClean

/-- Writing a slot `x` outside the words `S` and the arrays `A` with a signed value adds
    `x` to the signed values. -/
theorem EnvRelS.update_int {env env' : Env} {σ σ' : SEnvScalar} {S I : List String}
    {A : List (String × Nat)} (h : EnvRelS env σ S I A) (x : String) (hxT : ¬ isTmpName x)
    (hxS : x ∉ S) (hxA : ∀ p ∈ A, p.1 ≠ x) (henv : ∀ y, y ≠ x → env' y = env y)
    (hσ : ∀ y, y ≠ x → ¬ isTmpName y → σ' y = σ y) (hnew : IntAt env' σ' x) :
    EnvRelS env' σ' S (x :: I) A where
  rel := h.rel.preserve x hxS hxA henv hσ
  int y hy := by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hnew
    · by_cases hyx : y = x
      · subst hyx; exact hnew
      · obtain ⟨z, h1, h2, he, hs⟩ := h.int y hy
        exact ⟨z, h1, h2, by rw [henv y hyx, he], by rw [hσ y hyx (h.intClean y hy), hs]⟩
  intClean y hy := by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxT
    · exact h.intClean y hy

/-- Writing a slot `x` outside the signed values `I` and the arrays `A` with a word
    adds `x` to the words. -/
theorem EnvRelS.update_word {env env' : Env} {σ σ' : SEnvScalar} {S I : List String}
    {A : List (String × Nat)} (h : EnvRelS env σ S I A) (x : String) (hxT : ¬ isTmpName x)
    (hxI : x ∉ I) (hxA : ∀ p ∈ A, p.1 ≠ x) (henv : ∀ y, y ≠ x → env' y = env y)
    (hσ : ∀ y, y ≠ x → ¬ isTmpName y → σ' y = σ y) (hnew : WordAt env' σ' x) :
    EnvRelS env' σ' (x :: S) I A where
  rel := h.rel.update x hxT hxA henv hσ hnew
  int y hy := by
    have hyx : y ≠ x := fun e => hxI (e ▸ hy)
    obtain ⟨z, h1, h2, he, hs⟩ := h.int y hy
    exact ⟨z, h1, h2, by rw [henv y hyx, he], by rw [hσ y hyx (h.intClean y hy), hs]⟩
  intClean := h.intClean

/-! ### The scalar assignment -/

/-- **Scalar assignment.** `RLetU64Zero x (RSeq (RScalarSetExpr x se) _)` with `se`
    accepted by the lowering and of value `v` runs in `semScalar` to a scalar environment
    binding `x` to `v` and agreeing with `σ` outside `x` and the temporaries. -/
theorem semStep_setExpr {σ : SEnvScalar} {x : String} {se : SExpr}
    (hlow : LowersIn (σ.upd x (t := .sword 64) (0 : BitVec 64)) se) {v : BitVec 64}
    (hval : se.evalBV (envReader (σ.upd x (t := .sword 64) (0 : BitVec 64))) = v)
    (bodyC : LowCT) :
    ∃ σ', semScalar (.RLetU64Zero x (.RSeq (.RScalarSetExpr x se) bodyC)) σ =
        semScalar bodyC σ' ∧ σ' x = some ⟨.sword 64, v⟩ ∧
        ∀ y, y ≠ x → ¬ isTmpName y → σ' y = σ y := by
  obtain ⟨σ₂, _, _, hlow', _, hot, _, _⟩ := semLowerSExpr_of_lowersIn se _ 0 hlow
  refine ⟨σ₂.upd x (t := .sword 64) v, ?_, upd_self _, fun y hy hyT => ?_⟩
  · simp only [semScalar, hlow', hval, Option.bind_some]
  · rw [upd_ne _ hy, hot y (Or.inl hyT), upd_ne _ hy]

/-- An operand holding the two's complement of `z`, other than `x`, is a variable the
    lowering accepts after `x` is bound, of value `BitVec.ofInt 64 z`. -/
theorem lowersIn_intVar {σ : SEnvScalar} {x a : String} {z : Int}
    (hr : envReadU64 σ a = some (BitVec.ofInt 64 z)) (haT : ¬ isTmpName a) (hax : a ≠ x) :
    LowersIn (σ.upd x (t := .sword 64) (0 : BitVec 64)) (.SVar a) ∧
      (SExpr.SVar a).evalBV (envReader (σ.upd x (t := .sword 64) (0 : BitVec 64))) =
        BitVec.ofInt 64 z := by
  have hτ : envReadU64 (σ.upd x (t := .sword 64) (0 : BitVec 64)) a =
      some (BitVec.ofInt 64 z) := by rw [envReadU64_upd_ne _ hax, hr]
  exact ⟨⟨haT, by rw [hτ]; rfl⟩, by simp only [SExpr.evalBV, envReader_of_envReadU64 hτ]⟩

/-- Sign extension of an accepted scalar expression is accepted. -/
theorem lowersIn_sextSExpr {σ : SEnvScalar} (w : Nat) {e : SExpr} (he : LowersIn σ e) :
    LowersIn σ (sextSExpr w e) := by
  unfold sextSExpr
  split
  · exact he
  · exact ⟨⟨⟨he, trivial⟩, trivial⟩, trivial⟩

/-- The arithmetic shift of accepted scalar expressions is accepted. -/
theorem lowersIn_asrSExpr {σ : SEnvScalar} {a k : SExpr} (ha : LowersIn σ a)
    (hk : LowersIn σ k) : LowersIn σ (asrSExpr a k) :=
  ⟨⟨⟨ha, trivial, ha, trivial⟩, hk⟩, trivial, ha, trivial⟩

/-- The signed comparison of accepted scalar expressions is accepted. -/
theorem lowersIn_sltSExpr {σ : SEnvScalar} {a b : SExpr} (ha : LowersIn σ a)
    (hb : LowersIn σ b) : LowersIn σ (sltSExpr a b) := by
  simp only [sltSExpr, ltExpr, carryExpr, LowersIn, and_true, true_and]
  exact ⟨⟨hb, ha⟩, hb, ha⟩

/-- The scalar expression of a signed operation on accepted operands is accepted. -/
theorem SignedOp.lowersIn_sexpr {σ : SEnvScalar} (w : Nat) (op : SignedOp) {ea eb : SExpr}
    (ha : LowersIn σ ea) (hb : LowersIn σ eb) : LowersIn σ (op.sexpr w ea eb) := by
  cases op
  case shr => exact lowersIn_asrSExpr ha hb
  all_goals exact lowersIn_sextSExpr w ⟨ha, hb⟩

/-- The scalar expression of a signed comparison on accepted operands is accepted. -/
theorem SignedCmp.lowersIn_sexpr {σ : SEnvScalar} (c : SignedCmp) {ea eb : SExpr}
    (ha : LowersIn σ ea) (hb : LowersIn σ eb) : LowersIn σ (c.sexpr ea eb) := by
  cases c
  · exact lowersIn_sltSExpr ha hb
  · exact lowersIn_sltSExpr hb ha
  · exact ⟨lowersIn_sltSExpr hb ha, trivial⟩
  · exact ⟨lowersIn_sltSExpr ha hb, trivial⟩

/-! ### The builtin table -/

/-- The facts a builtin table evaluates the signed calls by: a signed operation of
    `signedOpOf` as `SignedOp.int` where it is defined, a signed conversion as the
    residue in `[-2^(w-1), 2^(w-1))`, a residue conversion as the residue in `[0, 2^w)`,
    and a comparison of `signedCmpOf` as the integer comparison. -/
structure SignedBuiltins (bi : Builtins) : Prop where
  op : ∀ (f : String) (w : Nat) (op : SignedOp), signedOpOf f = some (w, op) →
    ∀ a b r : Int, op.int w a b = some r → bi f [.int a, .int b] = some (.int r)
  cast : ∀ (f : String) (w : Nat), signedCastOf f = some w → ∀ a : Int,
    bi f [.int a] = some (.int (a.bmod (2 ^ w)))
  residue : ∀ (f : String) (w : Nat), residueCastOf f = some w → ∀ a : Int,
    bi f [.int a] = some (.int (a % 2 ^ w))
  cmp : ∀ (f : String) (c : SignedCmp), signedCmpOf f = some c → ∀ a b : Int,
    bi f [.int a, .int b] = some (.bool (c.bool a b))

/-! ### The step lemmas -/

/-- **Signed-operation binding.** `let x = f(a, b)` for a signed operation `f` of width
    `w` on two related operands runs in hax to the binding of `x` to the operation's value
    `r`, and its lowering to a scalar environment related to it with `x` added to the
    signed values. -/
theorem step_signed {bi : Builtins} (hbi : SignedBuiltins bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S I : List String} {A : List (String × Nat)}
    (h : EnvRelS env σ S I A) {x f a b : String} {w : Nat} {op : SignedOp}
    (hf : signedOpOf f = some (w, op)) (ha : a ∈ S ∨ a ∈ I) (hb : b ∈ S ∨ b ∈ I)
    (hax : a ≠ x) (hbx : b ≠ x) (hxT : ¬ isTmpName x) (hxS : x ∉ S)
    (hxA : ∀ p ∈ A, p.1 ≠ x) {za zb r : Int} (hza : env a = some (.int za))
    (hzb : env b = some (.int zb)) (hr : op.int w za zb = some r) (body : ImpExpr)
    (bodyC : LowCT) :
    (denote bi fuel (.letBind x (.app f [.var a, .var b]) body)).run env =
        (denote bi fuel body).run (env.extend x (.int r)) ∧
      ∃ σ', semScalar (.RLetU64Zero x (.RSeq (.RScalarSetExpr x
          (op.sexpr w (.SVar a) (.SVar b))) bodyC)) σ = semScalar bodyC σ' ∧
        EnvRelS (env.extend x (.int r)) σ' S (x :: I) A := by
  obtain ⟨za', hea, hra, haT⟩ := h.read ha
  obtain ⟨zb', heb, hrb, hbT⟩ := h.read hb
  rw [hza] at hea
  rw [hzb] at heb
  cases hea
  cases heb
  obtain ⟨hla, hva⟩ := lowersIn_intVar hra haT hax
  obtain ⟨hlb, hvb⟩ := lowersIn_intVar hrb hbT hbx
  have hw := signedOpOf_width hf
  have hval := CatCrypt.Crypto.Hax.SignedOp.sexpr_evalBV hw op _ hva hvb hr
  refine ⟨denote_letBind_app_run bi fuel x f [a, b] [.int za, .int zb] _ body env
      (by simp [hza, hzb]) (hbi.op f w op hf _ _ _ hr), ?_⟩
  obtain ⟨σ', hrun, hx, hag⟩ :=
    semStep_setExpr (SignedOp.lowersIn_sexpr w op hla hlb) hval bodyC
  obtain ⟨hr1, hr2⟩ := SignedOp.int_range hw op hr
  exact ⟨σ', hrun, h.update_int x hxT hxS hxA (fun y hy => extend_ne _ hy) hag
    ⟨r, hr1, hr2, extend_self _, hx⟩⟩

/-- **Signed-conversion binding.** `let x = f(a)` for a signed conversion `f` to `w` bits
    of a related operand runs in hax to the binding of `x` to the residue of its value in
    `[-2^(w-1), 2^(w-1))`, and its lowering to a scalar environment related to it with `x`
    added to the signed values. -/
theorem step_signedCast {bi : Builtins} (hbi : SignedBuiltins bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S I : List String} {A : List (String × Nat)}
    (h : EnvRelS env σ S I A) {x f a : String} {w : Nat} (hf : signedCastOf f = some w)
    (ha : a ∈ S ∨ a ∈ I) (hax : a ≠ x) (hxT : ¬ isTmpName x) (hxS : x ∉ S)
    (hxA : ∀ p ∈ A, p.1 ≠ x) {z : Int} (hz : env a = some (.int z)) (body : ImpExpr)
    (bodyC : LowCT) :
    (denote bi fuel (.letBind x (.app f [.var a]) body)).run env =
        (denote bi fuel body).run (env.extend x (.int (z.bmod (2 ^ w)))) ∧
      ∃ σ', semScalar (.RLetU64Zero x (.RSeq (.RScalarSetExpr x (sextSExpr w (.SVar a)))
          bodyC)) σ = semScalar bodyC σ' ∧
        EnvRelS (env.extend x (.int (z.bmod (2 ^ w)))) σ' S (x :: I) A := by
  obtain ⟨z', hea, hra, haT⟩ := h.read ha
  rw [hz] at hea
  cases hea
  obtain ⟨hla, hva⟩ := lowersIn_intVar hra haT hax
  have hw := signedCastOf_width hf
  have hval := evalBV_signedCast hw (envReader (σ.upd x (t := .sword 64) (0 : BitVec 64)))
    (a := a) (z := z) (by simpa only [SExpr.evalBV] using hva)
  refine ⟨denote_letBind_app_run bi fuel x f [a] [.int z] _ body env (by simp [hz])
      (hbi.cast f w hf _), ?_⟩
  obtain ⟨σ', hrun, hx, hag⟩ := semStep_setExpr (lowersIn_sextSExpr w hla) hval bodyC
  obtain ⟨hr1, hr2⟩ := CatCrypt.Crypto.Hax.bmod_range z (w := w) (by omega) (by omega)
  exact ⟨σ', hrun, h.update_int x hxT hxS hxA (fun y hy => extend_ne _ hy) hag
    ⟨_, hr1, hr2, extend_self _, hx⟩⟩

/-- **Residue-conversion binding.** `let x = f(a)` for a residue conversion `f` to `w`
    bits of a related operand runs in hax to the binding of `x` to the residue of its
    value in `[0, 2^w)`, and its lowering to a scalar environment related to it with `x`
    added to the words. -/
theorem step_residueCast {bi : Builtins} (hbi : SignedBuiltins bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S I : List String} {A : List (String × Nat)}
    (h : EnvRelS env σ S I A) {x f a : String} {w : Nat} (hf : residueCastOf f = some w)
    (ha : a ∈ S ∨ a ∈ I) (hax : a ≠ x) (hxT : ¬ isTmpName x) (hxI : x ∉ I)
    (hxA : ∀ p ∈ A, p.1 ≠ x) {z : Int} (hz : env a = some (.int z)) (body : ImpExpr)
    (bodyC : LowCT) :
    (denote bi fuel (.letBind x (.app f [.var a]) body)).run env =
        (denote bi fuel body).run (env.extend x (.int (z % 2 ^ w))) ∧
      ∃ σ', semScalar (.RLetU64Zero x (.RSeq (.RScalarSetExpr x
          (.SAnd (.SVar a) (.SLit (2 ^ w - 1)))) bodyC)) σ = semScalar bodyC σ' ∧
        EnvRelS (env.extend x (.int (z % 2 ^ w))) σ' (x :: S) I A := by
  obtain ⟨z', hea, hra, haT⟩ := h.read ha
  rw [hz] at hea
  cases hea
  obtain ⟨hla, hva⟩ := lowersIn_intVar hra haT hax
  have hw := residueCastOf_width hf
  have hw64 : w ≤ 64 := by omega
  have hnn : 0 ≤ z % 2 ^ w := Int.emod_nonneg _ (by positivity)
  have hlt : z % 2 ^ w < 2 ^ w := Int.emod_lt_of_pos _ (by positivity)
  have hval := toNat_residueCast hw64 (envReader (σ.upd x (t := .sword 64) (0 : BitVec 64)))
    (a := a) (z := z) (by simpa only [SExpr.evalBV] using hva)
  refine ⟨denote_letBind_app_run bi fuel x f [a] [.int z] _ body env (by simp [hz])
      (hbi.residue f w hf _), ?_⟩
  obtain ⟨σ', hrun, hx, hag⟩ := semStep_setExpr (se := .SAnd (.SVar a) (.SLit (2 ^ w - 1)))
    ⟨hla, trivial⟩ rfl bodyC
  have hn : (z % 2 ^ w).toNat < 2 ^ 64 := by
    have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw64
    have h2 : ((z % 2 ^ w).toNat : Int) < 2 ^ w := by rw [Int.toNat_of_nonneg hnn]; exact hlt
    have h3 : ((z % 2 ^ w).toNat : Int) < ((2 ^ 64 : Nat) : Int) :=
      lt_of_lt_of_le h2 (by exact_mod_cast this)
    exact_mod_cast h3
  have hbv : (SExpr.SAnd (.SVar a) (.SLit (2 ^ w - 1))).evalBV
      (envReader (σ.upd x (t := .sword 64) (0 : BitVec 64))) =
      BitVec.ofNat 64 (z % 2 ^ w).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [hval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine ⟨σ', hrun, h.update_word x hxT hxI hxA (fun y hy => extend_ne _ hy) hag
    ⟨(z % 2 ^ w).toNat, hn, ?_, by rw [hx, hbv]⟩⟩
  rw [extend_self, Int.toNat_of_nonneg hnn]

/-- **Signed-comparison binding.** `let x = f(a, b)` for a comparison `f` of two related
    signed values runs in hax to the binding of `x` to the Boolean of the integer
    comparison, and its lowering to a scalar environment binding `x` to `1` or `0` as that
    Boolean, related to the hax environment on the other names. -/
theorem step_signedCmp {bi : Builtins} (hbi : SignedBuiltins bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S I : List String} {A : List (String × Nat)}
    (h : EnvRelS env σ S I A) {x f a b : String} {c : SignedCmp}
    (hf : signedCmpOf f = some c) (ha : a ∈ I) (hb : b ∈ I) (hax : a ≠ x) (hbx : b ≠ x)
    (hxS : x ∉ S) (hxI : x ∉ I) (hxA : ∀ p ∈ A, p.1 ≠ x) {za zb : Int}
    (hza : env a = some (.int za)) (hzb : env b = some (.int zb)) (body : ImpExpr)
    (bodyC : LowCT) :
    (denote bi fuel (.letBind x (.app f [.var a, .var b]) body)).run env =
        (denote bi fuel body).run (env.extend x (.bool (c.bool za zb))) ∧
      ∃ σ', semScalar (.RLetU64Zero x (.RSeq (.RScalarSetExpr x
          (c.sexpr (.SVar a) (.SVar b))) bodyC)) σ = semScalar bodyC σ' ∧
        σ' x = some ⟨.sword 64, (if c.bool za zb then 1 else 0 : BitVec 64)⟩ ∧
        EnvRelS (env.extend x (.bool (c.bool za zb))) σ' S I A := by
  obtain ⟨za', ha1, ha2, hea, hra, haT⟩ := h.readInt ha
  obtain ⟨zb', hb1, hb2, heb, hrb, hbT⟩ := h.readInt hb
  rw [hza] at hea
  rw [hzb] at heb
  cases hea
  cases heb
  obtain ⟨hla, hva⟩ := lowersIn_intVar hra haT hax
  obtain ⟨hlb, hvb⟩ := lowersIn_intVar hrb hbT hbx
  have hval := CatCrypt.Crypto.Hax.SignedCmp.sexpr_evalBV c _ ha1 ha2 hb1 hb2 hva hvb
  refine ⟨denote_letBind_app_run bi fuel x f [a, b] [.int za, .int zb] _ body env
      (by simp [hza, hzb]) (hbi.cmp f c hf _ _), ?_⟩
  obtain ⟨σ', hrun, hx, hag⟩ := semStep_setExpr (SignedCmp.lowersIn_sexpr c hla hlb) hval bodyC
  exact ⟨σ', hrun, hx, h.preserve x hxS hxI hxA (fun y hy => extend_ne _ hy) hag⟩

/-! ### hax-lean's table -/

/-- Each signed operation of `signedOpOf` runs in `hax64Builtins` as `SignedOp.int`. -/
theorem hax64Builtins_signedOp (f : String) (w : Nat) (op : SignedOp)
    (hf : signedOpOf f = some (w, op)) (a b r : Int) (hr : op.int w a b = some r) :
    hax64Builtins f [.int a, .int b] = some (.int r) := by
  unfold signedOpOf at hf
  split at hf <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hf
  all_goals
    obtain ⟨rfl, rfl⟩ := hf
    apply hax64Builtins_of_some
    simp only [SignedOp.int] at hr
  all_goals first
    | (simp only [Option.some.injEq] at hr; subst hr; rfl)
    | (show sintShlOp _ a b = _
       unfold sintShlOp
       split at hr <;> simp_all)
    | (show sintShrOp _ a b = _
       unfold sintShrOp
       split at hr <;> simp_all)

/-- Each signed conversion of `signedCastOf` runs in `hax64Builtins` as the residue in
    `[-2^(w-1), 2^(w-1))`. -/
theorem hax64Builtins_signedCast (f : String) (w : Nat) (hf : signedCastOf f = some w)
    (a : Int) : hax64Builtins f [.int a] = some (.int (a.bmod (2 ^ w))) := by
  unfold signedCastOf at hf
  split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf
  all_goals (subst hf; apply hax64Builtins_of_some; rfl)

/-- Each residue conversion of `residueCastOf` runs in `hax64Builtins` as the residue in
    `[0, 2^w)`. -/
theorem hax64Builtins_residueCast (f : String) (w : Nat) (hf : residueCastOf f = some w)
    (a : Int) : hax64Builtins f [.int a] = some (.int (a % 2 ^ w)) := by
  unfold residueCastOf at hf
  split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf
  all_goals (subst hf; apply hax64Builtins_of_some; rfl)

/-- Each comparison of `signedCmpOf` runs in `hax64Builtins` as the integer
    comparison. -/
theorem hax64Builtins_signedCmp (f : String) (c : SignedCmp) (hf : signedCmpOf f = some c)
    (a b : Int) : hax64Builtins f [.int a, .int b] = some (.bool (c.bool a b)) := by
  unfold signedCmpOf at hf
  split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf
  all_goals (subst hf; apply hax64Builtins_of_some)
  · exact hax64WordOps_Lt a b
  · exact hax64WordOps_Gt a b
  · exact hax64WordOps_Le a b
  · exact hax64WordOps_Ge a b

/-- **hax-lean's table meets the signed contract.** -/
theorem hax64Builtins_signedBuiltins : SignedBuiltins hax64Builtins where
  op := hax64Builtins_signedOp
  cast := hax64Builtins_signedCast
  residue := hax64Builtins_residueCast
  cmp := hax64Builtins_signedCmp

end CatCrypt.Crypto.Hax.WordOpsSim
