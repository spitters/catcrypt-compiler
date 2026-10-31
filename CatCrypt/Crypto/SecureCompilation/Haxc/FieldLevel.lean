/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFInline
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakM
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow
public import HaxLean.SemanticsMontCalls

/-!
# The field level: modulus-tagged field calls as an inlining library

A call of a method of the prime-field interface at a concrete field reaches `NFProg nfDialect`
as a leaf call `NfOp.call (fieldHead m p) m.sig (.word 64)`, whose head `fieldHead m p` is the
method name, `#p`, and the modulus `p` in decimal (`mul#p2013265921`). An element is one
64-bit word holding its canonical representative.

`FieldCalls bi` states that the builtin table `bi` answers each head `fieldTag?` reads as a
method `m` at a modulus `p` below `2⁶⁴` by the arm `fieldArm m p`, defined when the
arguments are below `p`, with the value `fieldVal m p` (`FieldCalls.canon`), and each head
`fieldTagM?` reads as a method at an odd modulus below `2⁶⁴` and a radix `2 ^ k` by the arm
`fieldArmMont m p k` (`FieldCalls.mont`). `FieldCallsWide bi` states that at a modulus `p ≥ 2⁶⁴`
every value of `bi` at a tagged head is the value of the `u64` table, and `FieldCallsWideEq bi`
that `bi` is the `u64` table there.

`fieldLib` is the inlining library of the tagged heads. A head has a body when `fieldTag?`
reads a method and a modulus off it, the narrow certificate selects a fold count at the
modulus (`FieldRouteNarrow.narrowFoldsOf`), and the call has the argument types of the method
and the result type `.word 64`. The body `fieldBody m p n` is the single-word template in word
operations of `nfDialect`: the sum, difference or product, `n` folds
`x ↦ (x >>> 31) · (2³¹ − p) + (x & (2³¹ − 1))` after a product, and one branch-free
conditional subtract. Every other operation has no body.

Under `FieldCalls bi` the library is sound at the leaf table of `bi`, at every fuel
(`fieldLib_sound`), and `fieldStep`, one round of inlining at `fieldLib`, has the certificate
`fieldCert` with equality as input and output relation.

`InlineLib.union L₁ L₂` is the library that reads a body from `L₁` and, where `L₁` has none,
from `L₂`; it is sound when both are (`InlineLib.Sound.union`, `InlineLib.SoundStep.union`).
The union of the library of the functions of a crate and `fieldLib` is sound from the call
depth `m + 1` to the call depth `m` (`crateFieldLib_soundStep`), when no function of the
crate has a field head (`Hax.FieldTag.fieldHeadB`) as its name.

The bodies bind constants and the operations `add`, `sub`, `mul`, `and`, `lshr` at 64 bits.
For a leakage model in which these are quiet (`QuietWordOps`), the level checker
`NFProg.levelCheck'` accepts every body at every labelling of its arguments
(`fieldBody_levelCheck'`), so a body is constant time with all arguments secret
(`fieldBody_nfCTRel`).

## Main definitions

* `FieldCalls` — the condition on a builtin table. The tagged methods, their heads, the
  reading of a head (`Hax.FieldTag.fieldTag?`), the value of a method and the arm of a tagged
  head are those of the `u64` table (`Hax.FieldTag`).
* `fieldWord`, `fieldBody` — the word function of a method, and its program over `nfDialect`.
* `fieldOp`, `fieldLib`, `fieldStep`, `fieldCert` — the library, the step and its certificate.
* `InlineLib.union` — the union of two inlining libraries.
* `QuietWordOps` — the leakage models in which the word operations of the bodies are quiet.

## Main results

* `fieldTag?_babyBear`, `fieldTag?_koalaBear`, `fieldTag?_mersenne31`,
  `fieldHead_mul_babyBear` — the reading of the heads at the three single-word moduli, and
  the head of the multiplication at BabyBear as a string.
* `fieldCalls_hax64Builtins` — the `u64` table answers the tagged heads by their arms.
* `FieldCallsWide`, `fieldCallsWide_hax64Builtins` — the condition on a builtin table at the
  wide tagged heads, and the `u64` table satisfies it.
* `FieldCallsWideEq`, `fieldCallsWideEq_hax64Builtins` — the equation of a builtin table with
  the `u64` table at the wide tagged heads, and the `u64` table satisfies it.
* `fieldWord_toNat` — under the narrow certificate, the word function of a method on
  canonical representatives is `fieldVal`.
* `fieldBody_denote` — a body denotes its word function at every leaf table.
* `fieldOp_sound`, `fieldLib_sound`, `fieldLib_soundStep` — soundness of the library.
* `fieldOp_babyBear`, `fieldOp_koalaBear`, `fieldOp_mersenne31` — the bodies at the three
  single-word moduli.
* `InlineLib.Sound.union`, `InlineLib.SoundStep.union`, `FieldCalls.crateBi`,
  `crateFieldLib_soundStep` — soundness of a union, and of the union with the library of a
  crate.
* `fieldBody_levelCheck'`, `fieldOp_levelCheck'`, `fieldBody_nfCTRel` — the level check and
  constant time of the bodies.
-/

@[expose] public section

set_option autoImplicit false

/-! ## 1. The union of two inlining libraries -/

namespace CatCrypt.Crypto.SecureCompilation.VIR

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **The union of two inlining libraries**: the body of `L₁` where it has one, and the body
    of `L₂` otherwise. -/
def InlineLib.union (L₁ L₂ : InlineLib d) : InlineLib d where
  op o := (L₁.op o).orElse fun _ => L₂.op o
  call f as rs := (L₁.call f as rs).orElse fun _ => L₂.call f as rs

/-- A body of the union is a body of one of the two libraries. -/
theorem InlineLib.union_op {L₁ L₂ : InlineLib d} {o : d.Op}
    {b : NFProg d (DialectSignature.sig o) [DialectSignature.ret o]}
    (h : (L₁.union L₂).op o = some b) : L₁.op o = some b ∨ L₂.op o = some b := by
  simp only [InlineLib.union] at h
  cases h₁ : L₁.op o with
  | some b₁ =>
      rw [h₁] at h
      exact Or.inl h
  | none =>
      rw [h₁] at h
      exact Or.inr h

/-- A body of a symbol in the union is a body of one of the two libraries. -/
theorem InlineLib.union_call {L₁ L₂ : InlineLib d} {f : String} {as rs : List d.Ty}
    {b : NFProg d as rs} (h : (L₁.union L₂).call f as rs = some b) :
    L₁.call f as rs = some b ∨ L₂.call f as rs = some b := by
  simp only [InlineLib.union] at h
  cases h₁ : L₁.call f as rs with
  | some b₁ =>
      rw [h₁] at h
      exact Or.inl h
  | none =>
      rw [h₁] at h
      exact Or.inr h

/-- **The union of two sound libraries is sound.** -/
theorem InlineLib.Sound.union [DialectDenoteM d Option] [CallDenote d] {L₁ L₂ : InlineLib d}
    {fuel : Nat} (h₁ : L₁.Sound fuel) (h₂ : L₂.Sound fuel) : (L₁.union L₂).Sound fuel where
  op o b hb := (InlineLib.union_op hb).elim (h₁.op o b) (h₂.op o b)
  call f as rs b hb := (InlineLib.union_call hb).elim (h₁.call f as rs b) (h₂.call f as rs b)

/-- **The union of two libraries sound from one denotation to another is sound between
    them**, for the kept operations of the first. -/
theorem InlineLib.SoundStep.union [CallDenote d] {L₁ L₂ : InlineLib d}
    {D₁ D₂ : DialectDenoteM d Option} {P P₂ : d.Op → Bool} {fuel : Nat}
    (h₁ : L₁.SoundStep D₁ D₂ P fuel) (h₂ : L₂.SoundStep D₁ D₂ P₂ fuel) :
    (L₁.union L₂).SoundStep D₁ D₂ P fuel where
  op o b hb := (InlineLib.union_op hb).elim (h₁.op o b) (h₂.op o b)
  keep := h₁.keep
  call f as rs b hb := (InlineLib.union_call hb).elim (h₁.call f as rs b) (h₂.call f as rs b)

end CatCrypt.Crypto.SecureCompilation.VIR

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldLevel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (nfSem inlineStep inlineCert)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (csubW csubW_toNat foldW)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow (foldsOk foldsOk_spec narrowCert
  narrowFoldsOf narrowCert_of_narrowFoldsOf narrowCert_bounds narrowFoldsOf_babyBear
  narrowFoldsOf_koalaBear narrowFoldsOf_mersenne31)
open CatCrypt.Crypto.Hax.ImpToNF (tableOf enc dec dec_sound encAll mkE CrateFn crateBi
  crateBi_of_find_none TypedCalls hax64SigOf RepeatCalls)
open CatCrypt.Crypto.Hax.NFInline (crateLib crateCallOp crateLib_soundStep)
open _root_.Hax (Builtins Value)
open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag? fieldVal fieldArgs fieldArm fieldTagM?
  fieldArmMont)
open Ctxt (Var Valuation)

/-! ## 2. Tagged heads -/

/-- The 64-bit word, the type of a field element. -/
abbrev W : NfTy := .word 64

/-- The reading of the heads at BabyBear, `p = 2³¹ − 2²⁷ + 1`. -/
theorem fieldTag?_babyBear (m : FieldMethod) :
    fieldTag? (fieldHead m 2013265921) = some (m, 2013265921) := by
  simp only [fieldTag?, fieldHead, String.toList_ofList]
  cases m <;> decide

/-- The reading of the heads at KoalaBear, `p = 2³¹ − 2²⁴ + 1`. -/
theorem fieldTag?_koalaBear (m : FieldMethod) :
    fieldTag? (fieldHead m 2130706433) = some (m, 2130706433) := by
  simp only [fieldTag?, fieldHead, String.toList_ofList]
  cases m <;> decide

/-- The reading of the heads at Mersenne-31, `p = 2³¹ − 1`. -/
theorem fieldTag?_mersenne31 (m : FieldMethod) :
    fieldTag? (fieldHead m 2147483647) = some (m, 2147483647) := by
  simp only [fieldTag?, fieldHead, String.toList_ofList]
  cases m <;> decide

/-- The head of the multiplication at BabyBear is `mul#p2013265921`. -/
theorem fieldHead_mul_babyBear : fieldHead .mul 2013265921 = "mul#p2013265921" := by
  rfl

/-! ## 3. The arms of the builtin table -/

/-- **The builtin table `bi` answers the narrow field heads by their arms.** -/
structure FieldCalls (bi : Builtins) : Prop where
  /-- At every head `fieldTag?` reads as a method `m` at a modulus `p` below `2⁶⁴`, a call on
      the numbers `a` and `b` is `fieldArm m p a b`. -/
  canon : ∀ (f : String) (m : FieldMethod) (p : Nat), fieldTag? f = some (m, p) →
    p < 2 ^ 64 → ∀ a b : Nat, bi f (fieldArgs m a b) = fieldArm m p a b
  /-- At every head `fieldTagM?` reads as a method `m` at an odd modulus `p` below `2⁶⁴` and
      the radix `2 ^ k`, a call on the numbers `a` and `b` is `fieldArmMont m p k a b`. -/
  mont : ∀ (f : String) (m : FieldMethod) (p k : Nat), fieldTagM? f = some (m, p, k) →
    p % 2 = 1 → p < 2 ^ 64 → ∀ a b : Nat, bi f (fieldArgs m a b) = fieldArmMont m p k a b

/-- **The `u64` table answers the narrow field heads by their arms.** -/
theorem fieldCalls_hax64Builtins : FieldCalls _root_.Hax.hax64Builtins :=
  ⟨fun _ _ _ ht hp a b => _root_.Hax.hax64Builtins_fieldArgs ht hp a b,
    fun _ _ _ _ ht hodd hp a b => _root_.Hax.hax64Builtins_fieldArgsMont ht hodd hp a b⟩

/-- **The builtin table `bi` answers the wide tagged heads as the `u64` table does**: at every
    head `fieldTag?` reads as a method at a modulus `p ≥ 2⁶⁴`, a value of `bi` is the value of
    `Hax.hax64Builtins`, which on the limbs of numbers below `p` is the array of the limbs of
    `fieldVal` (`Hax.hax64Builtins_fieldArgsWide`). -/
def FieldCallsWide (bi : Builtins) : Prop :=
  ∀ (f : String) (m : FieldMethod) (p : Nat), fieldTag? f = some (m, p) → 2 ^ 64 ≤ p →
    ∀ (args : List _root_.Hax.Value) (v : _root_.Hax.Value), bi f args = some v →
      _root_.Hax.hax64Builtins f args = some v

/-- **The `u64` table answers the wide tagged heads as itself.** -/
theorem fieldCallsWide_hax64Builtins : FieldCallsWide _root_.Hax.hax64Builtins :=
  fun _ _ _ _ _ _ _ h => h

/-- **The builtin table `bi` is the `u64` table at the wide tagged heads**: at every head
    `fieldTag?` reads as a method at a modulus `p ≥ 2⁶⁴`, `bi` and `Hax.hax64Builtins` have the
    same value on every argument list. -/
def FieldCallsWideEq (bi : Builtins) : Prop :=
  ∀ (f : String) (m : FieldMethod) (p : Nat), fieldTag? f = some (m, p) → 2 ^ 64 ≤ p →
    ∀ args : List _root_.Hax.Value, bi f args = _root_.Hax.hax64Builtins f args

/-- A table equal to the `u64` table at the wide tagged heads answers them as the `u64`
    table. -/
theorem FieldCallsWideEq.fieldCallsWide {bi : Builtins} (h : FieldCallsWideEq bi) :
    FieldCallsWide bi :=
  fun f m p ht hp args _ hv => (h f m p ht hp args) ▸ hv

/-- **The `u64` table is itself at the wide tagged heads.** -/
theorem fieldCallsWideEq_hax64Builtins : FieldCallsWideEq _root_.Hax.hax64Builtins :=
  fun _ _ _ _ _ _ => rfl

/-! ## 4. The word functions -/

/-- **The word function of a method** at the modulus `p` with `n` folds: the sum, difference
    or product, `n` folds by `2³¹ − p` after a product, and one conditional subtract. -/
def fieldWord (m : FieldMethod) (p n : Nat) (a b : BitVec 64) : BitVec 64 :=
  match m with
  | .add => csubW p (a + b)
  | .sub => csubW p (a + (BitVec.ofNat 64 p - b))
  | .mul => csubW p ((foldW (2 ^ 31 - p))^[n] (a * b))
  | .neg => csubW p (BitVec.ofNat 64 p - a)
  | .square => csubW p ((foldW (2 ^ 31 - p))^[n] (a * a))
  | .double => csubW p (a + a)

/-- Under the certificate, the folds of a product of two words below `p` and the conditional
    subtract give the product modulo `p`. -/
theorem csubW_folds_mul {p n : Nat} (h : narrowCert p n = true) (a b : BitVec 64)
    (ha : a.toNat < p) (hb : b.toNat < p) :
    (csubW p ((foldW (2 ^ 31 - p))^[n] (a * b))).toNat = (a.toNat * b.toNat) % p := by
  simp only [narrowCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp1, hp⟩, hf⟩ := h
  have hc : 2 ^ 31 - p < 2 ^ 31 := by omega
  have hP : 2 ^ 31 - (2 ^ 31 - p) = p := by omega
  have hf' : foldsOk (2 ^ 31 - p) (2 ^ 31 - (2 ^ 31 - p)) n ((p - 1) * (p - 1) + 1) = true := by
    rwa [hP]
  have hle : a.toNat * b.toNat ≤ (p - 1) * (p - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hlt : a.toNat * b.toNat < 2 ^ 62 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (le_trans (Nat.mul_le_mul hp hp) (by norm_num))
  have hprod : (a * b).toNat = a.toNat * b.toNat := by
    rw [BitVec.toNat_mul]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨h1, h2⟩ := foldsOk_spec _ hc n _ (a * b) hf' (by rw [hprod]; omega)
  rw [hP] at h1 h2
  rw [csubW_toNat p (by omega) _ h1, h2, hprod]

/-- **The word function of a method on canonical representatives is its value.** Under the
    certificate `narrowCert p n`, for words `a` and `b` below `p`. -/
theorem fieldWord_toNat {p n : Nat} (h : narrowCert p n = true) (m : FieldMethod)
    (a b : BitVec 64) (ha : a.toNat < p) (hb : b.toNat < p) :
    (fieldWord m p n a b).toNat = fieldVal m p a.toNat b.toNat := by
  obtain ⟨hp1, hp⟩ := narrowCert_bounds h
  have h2p : 2 * p ≤ 2 ^ 63 := by omega
  have hPt : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hsubP : ∀ x : BitVec 64, x.toNat < p → (BitVec.ofNat 64 p - x).toNat = p - x.toNat := by
    intro x hx
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hPt]; omega), hPt]
  cases m
  · have hs : (a + b).toNat = a.toNat + b.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [fieldWord, fieldVal]
    rw [csubW_toNat p h2p _ (by omega), hs]
  · have hs : (a + (BitVec.ofNat 64 p - b)).toNat = a.toNat + (p - b.toNat) := by
      rw [BitVec.toNat_add, hsubP b hb]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [fieldWord, fieldVal]
    rw [csubW_toNat p h2p _ (by omega), hs]
    congr 1
    omega
  · exact csubW_folds_mul h a b ha hb
  · simp only [fieldWord, fieldVal]
    rw [csubW_toNat p h2p _ (by rw [hsubP a ha]; omega), hsubP a ha]
  · exact csubW_folds_mul h a a ha ha
  · have hs : (a + a).toNat = a.toNat + a.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [fieldWord, fieldVal]
    rw [csubW_toNat p h2p _ (by omega), hs, Nat.two_mul]

/-! ## 5. The bodies -/

/-- The conditional subtract of `P` on the word `x`, returned:
    `(x − P) + (P & (0 − ((x − P) >>> 63)))`. -/
def csubK {Γ : Ctxt nfDialect} (P : Nat) (x : Var Γ W) : NFProg nfDialect Γ [W] :=
  .var (mkE (.const 64 (BitVec.ofNat 64 P)) .nil) <|
  .var (mkE (.bin .sub 64) (.cons x.there (.cons .here .nil))) <|
  .var (mkE (.const 64 63) .nil) <|
  .var (mkE (.bin .lshr 64) (.cons (.there .here) (.cons .here .nil))) <|
  .var (mkE (.const 64 0) .nil) <|
  .var (mkE (.bin .sub 64) (.cons .here (.cons (.there .here) .nil))) <|
  .var (mkE (.bin .and 64)
    (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))) <|
  .var (mkE (.bin .add 64)
    (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))) <|
  .ret (.cons .here .nil)

/-- `n` folds by `c` of the word `x`, `x ↦ (x >>> 31) · c + (x & (2³¹ − 1))`, followed by the
    conditional subtract of `P`. -/
def reduceK (c P : Nat) : Nat → {Γ : Ctxt nfDialect} → Var Γ W → NFProg nfDialect Γ [W]
  | 0, _, x => csubK P x
  | n + 1, _, x =>
      .var (mkE (.const 64 31) .nil) <|
      .var (mkE (.bin .lshr 64) (.cons x.there (.cons .here .nil))) <|
      .var (mkE (.const 64 (BitVec.ofNat 64 c)) .nil) <|
      .var (mkE (.bin .mul 64) (.cons (.there .here) (.cons .here .nil))) <|
      .var (mkE (.const 64 2147483647) .nil) <|
      .var (mkE (.bin .and 64)
        (.cons x.there.there.there.there.there (.cons .here .nil))) <|
      .var (mkE (.bin .add 64) (.cons (.there (.there .here)) (.cons .here .nil))) <|
      reduceK c P n .here

/-- **The body of a method** at the modulus `p` with `n` folds, over the arguments of the
    method. -/
def fieldBody (m : FieldMethod) (p n : Nat) : NFProg nfDialect m.sig [W] :=
  match m with
  | .add =>
      .var (mkE (.bin .add 64) (.cons .here (.cons (.there .here) .nil))) <| csubK p .here
  | .sub =>
      .var (mkE (.const 64 (BitVec.ofNat 64 p)) .nil) <|
      .var (mkE (.bin .sub 64) (.cons .here (.cons (.there (.there .here)) .nil))) <|
      .var (mkE (.bin .add 64) (.cons (.there (.there .here)) (.cons .here .nil))) <|
      csubK p .here
  | .mul =>
      .var (mkE (.bin .mul 64) (.cons .here (.cons (.there .here) .nil))) <|
      reduceK (2 ^ 31 - p) p n .here
  | .neg =>
      .var (mkE (.const 64 (BitVec.ofNat 64 p)) .nil) <|
      .var (mkE (.bin .sub 64) (.cons .here (.cons (.there .here) .nil))) <| csubK p .here
  | .square =>
      .var (mkE (.bin .mul 64) (.cons .here (.cons .here .nil))) <|
      reduceK (2 ^ 31 - p) p n .here
  | .double =>
      .var (mkE (.bin .add 64) (.cons .here (.cons .here .nil))) <| csubK p .here

/-- The denotation of a program of `nfDialect` at the leaf table `T`. -/
abbrev denT (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (V : Valuation Γ) : Option (Valuation (d := nfDialect) ts) :=
  @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel _ _ p V

/-- A binding of a constant extends the valuation by the constant. -/
theorem denT_const (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (v : BitVec 64) (k : NFProg nfDialect (W :: Γ) ts) (V : Valuation Γ) :
    denT T fuel (.var (mkE (.const 64 v) .nil) k) V = denT T fuel k (V.extend v) := rfl

/-- A binding of a binary word operation extends the valuation by its value. -/
theorem denT_bin (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (o : NfBinOp) (a b : Var Γ W) (k : NFProg nfDialect (W :: Γ) ts) (V : Valuation Γ) :
    denT T fuel (.var (mkE (.bin o 64) (.cons a (.cons b .nil))) k) V =
      (o.denote 64 (a.lookup V) (b.lookup V)).bind fun y => denT T fuel k (V.extend y) := rfl

/-- The return of a variable is its value. -/
theorem denT_ret (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} (a : Var Γ W)
    (V : Valuation Γ) :
    denT T fuel (.ret (.cons a .nil)) V = some (.cons (a.lookup V) .nil) := rfl

/-- The conditional subtract denotes `csubW`. -/
theorem csubK_denote (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} (P : Nat)
    (x : Var Γ W) (V : Valuation Γ) :
    denT T fuel (csubK P x) V = some (.cons (csubW P (x.lookup V)) .nil) := by
  unfold csubK
  rfl

/-- The folds followed by the conditional subtract denote the iterated `foldW` followed by
    `csubW`. -/
theorem reduceK_denote (T : NfLeafTable) (fuel : Nat) (c P : Nat) :
    ∀ (n : Nat) {Γ : Ctxt nfDialect} (x : Var Γ W) (V : Valuation Γ),
      denT T fuel (reduceK c P n x) V =
        some (.cons (csubW P ((foldW c)^[n] (x.lookup V))) .nil)
  | 0, _, x, V => csubK_denote T fuel P x V
  | n + 1, _, x, V => by
      rw [Function.iterate_succ_apply]
      exact reduceK_denote T fuel c P n .here _

/-- The first argument of a call of a method. -/
def arg₀ : (m : FieldMethod) → HVector NfTy.denote m.sig → BitVec 64
  | .add, x | .sub, x | .mul, x | .neg, x | .square, x | .double, x => x.head

/-- The second argument of a call of a method, and the first for a method with one. -/
def arg₁ : (m : FieldMethod) → HVector NfTy.denote m.sig → BitVec 64
  | .add, x | .sub, x | .mul, x => x.tail.head
  | .neg, x | .square, x | .double, x => x.head

/-- **A body denotes its word function**, at every leaf table and fuel. -/
theorem fieldBody_denote (T : NfLeafTable) (fuel : Nat) (m : FieldMethod) (p n : Nat)
    (x : HVector NfTy.denote m.sig) :
    denT T fuel (fieldBody m p n) x =
      some (.cons (fieldWord m p n (arg₀ m x) (arg₁ m x)) .nil) := by
  cases m
  all_goals rcases x with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · exact (denT_bin T fuel .add _ _ _ _).trans (csubK_denote T fuel p .here _)
  · exact (denT_const T fuel _ _ _).trans ((denT_bin T fuel .sub _ _ _ _).trans
      ((denT_bin T fuel .add _ _ _ _).trans (csubK_denote T fuel p .here _)))
  · exact (denT_bin T fuel .mul _ _ _ _).trans (reduceK_denote T fuel _ p n .here _)
  · exact (denT_const T fuel _ _ _).trans ((denT_bin T fuel .sub _ _ _ _).trans
      (csubK_denote T fuel p .here _))
  · exact (denT_bin T fuel .mul _ _ _ _).trans (reduceK_denote T fuel _ p n .here _)
  · exact (denT_bin T fuel .add _ _ _ _).trans (csubK_denote T fuel p .here _)

/-! ## 6. The library -/

/-- **The body of an operation in the library of the tagged heads**: a leaf call of a head
    `fieldTag?` reads as the method `m` at the modulus `p`, at the argument types of `m` and
    the result type `.word 64`, has the body `fieldBody m p n` for the fold count `n` the
    narrow certificate selects at `p`; a named operation has the body of the operation; no
    other operation has a body. -/
def fieldOp : (o : NfOp) → Option (NFProg nfDialect o.sig [o.ret])
  | .call f as r =>
      (fieldTag? f).bind fun mp => (narrowFoldsOf mp.2).bind fun n =>
        if h : mp.1.sig = as ∧ W = r then
          some (cast (congrArg₂ (NFProg nfDialect) h.1 (congrArg (fun x => [x]) h.2))
            (fieldBody mp.1 mp.2 n))
        else none
  | .named _ o => fieldOp o
  | _ => none

/-- **The library of the tagged field calls**: the operations of `fieldOp`; no `call` node
    has a body. -/
def fieldLib : InlineLib nfDialect where
  op := fieldOp
  call _ _ _ := none

/-- The body of the head of `m` at a modulus `p` at which `fieldTag?` reads the head and the
    narrow certificate selects `n` folds. -/
theorem fieldOp_of_tag {f : String} {m : FieldMethod} {p n : Nat}
    (ht : fieldTag? f = some (m, p)) (hn : narrowFoldsOf p = some n) :
    fieldOp (.call f m.sig W) = some (fieldBody m p n) := by
  simp [fieldOp, ht, hn]

/-- The bodies at BabyBear: eight folds. -/
theorem fieldOp_babyBear (m : FieldMethod) :
    fieldOp (.call (fieldHead m 2013265921) m.sig W) = some (fieldBody m 2013265921 8) :=
  fieldOp_of_tag (fieldTag?_babyBear m) narrowFoldsOf_babyBear

/-- The body of the multiplication at BabyBear, at its head `mul#p2013265921`. -/
theorem fieldOp_mul_babyBear :
    fieldOp (.call "mul#p2013265921" [W, W] W) = some (fieldBody .mul 2013265921 8) :=
  fieldHead_mul_babyBear ▸ fieldOp_babyBear .mul

/-- The bodies at KoalaBear: five folds. -/
theorem fieldOp_koalaBear (m : FieldMethod) :
    fieldOp (.call (fieldHead m 2130706433) m.sig W) = some (fieldBody m 2130706433 5) :=
  fieldOp_of_tag (fieldTag?_koalaBear m) narrowFoldsOf_koalaBear

/-- The bodies at Mersenne-31: one fold. -/
theorem fieldOp_mersenne31 (m : FieldMethod) :
    fieldOp (.call (fieldHead m 2147483647) m.sig W) = some (fieldBody m 2147483647 1) :=
  fieldOp_of_tag (fieldTag?_mersenne31 m) narrowFoldsOf_mersenne31

/-- The encodings of the arguments of a call of a method are its argument values. -/
theorem encAll_sig (m : FieldMethod) (x : HVector NfTy.denote m.sig) :
    encAll m.sig x = fieldArgs m (arg₀ m x).toNat (arg₁ m x).toNat := by
  cases m
  all_goals
    rcases x with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    rfl

/-- **A successful call of a tagged head is a run of its body.** Under `FieldCalls bi`, a
    successful run at the leaf table of `bi` of an operation `fieldOp` has a body for is a run
    of the body at every leaf table `T` and fuel, with the same result. -/
theorem fieldOp_sound {bi : Builtins} (hF : FieldCalls bi) (T : NfLeafTable) (fuel : Nat) :
    ∀ (o : NfOp) (b : NFProg nfDialect o.sig [o.ret]), fieldOp o = some b → ∀ x y,
      nfDenoteOp (tableOf bi) o x = some y → denT T fuel b x = some (.cons y .nil) := by
  intro o
  induction o with
  | call f as r =>
      intro b hb x y hy
      simp only [fieldOp, Option.bind_eq_some_iff] at hb
      obtain ⟨⟨m, p⟩, ht, n, hn, hb⟩ := hb
      split at hb
      · rename_i hty
        cases hb
        obtain ⟨rfl, rfl⟩ := hty
        have hc := narrowCert_of_narrowFoldsOf hn
        obtain ⟨hp1, hp⟩ := narrowCert_bounds hc
        simp only at hp1 hp hc
        simp only [nfDenoteOp, tableOf, Option.bind_eq_some_iff] at hy
        obtain ⟨v, hv, hy⟩ := hy
        simp only [encAll_sig, hF.canon f m p ht (by omega), fieldArm] at hv
        split at hv
        · rename_i hlt
          cases hv
          have hb' : (arg₁ m x).toNat < p := by
            cases m
            · exact hlt.2 rfl
            · exact hlt.2 rfl
            · exact hlt.2 rfl
            · exact hlt.1
            · exact hlt.1
            · exact hlt.1
          have he := dec_sound _ _ _ hy
          simp only [enc, Value.int.injEq, Int.natCast_inj] at he
          show denT T fuel (fieldBody m p n) x = _
          rw [fieldBody_denote]
          have hw : fieldWord m p n (arg₀ m x) (arg₁ m x) = y :=
            BitVec.eq_of_toNat_eq (by rw [fieldWord_toNat hc m _ _ hlt.1 hb', he])
          rw [hw]
        · cases hv
      · cases hb
  | named _ o ih =>
      intro b hb x y hy
      exact ih b hb x y hy
  | _ =>
      intro b hb
      cases hb

/-- **The library of the tagged field calls is sound** at the leaf table of a builtin table
    that answers the tagged heads by their arms, at every fuel. -/
theorem fieldLib_sound {bi : Builtins} (hF : FieldCalls bi) (tf : Nat) :
    @InlineLib.Sound nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ fieldLib tf :=
  @InlineLib.Sound.mk nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ fieldLib tf
    (fieldOp_sound hF (tableOf bi) tf) (fun _ _ _ _ hb => by cases hb)

/-- **The library of the tagged field calls is sound from the leaf table of `bi` to every
    leaf table**, with no kept operation. -/
theorem fieldLib_soundStep {bi : Builtins} (hF : FieldCalls bi) (T : NfLeafTable) (tf : Nat) :
    fieldLib.SoundStep (nfDenote (tableOf bi)) (nfDenote T) (fun _ => false) tf where
  op := fieldOp_sound hF T tf
  keep _ h := by cases h
  call _ _ _ _ hb := by cases hb

/-- **The field step**: one round of inlining at the library of the tagged field calls. -/
def fieldStep (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.Step (NFProg nfDialect Γ ts) (NFProg nfDialect Γ ts) :=
  inlineStep fieldLib 1 Γ ts

/-- **The certificate of the field step**, at the leaf table of a builtin table that answers
    the tagged heads by their arms: `inlineCert` at `fieldLib_sound`. -/
def fieldCert {bi : Builtins} (hF : FieldCalls bi) (tf : Nat) (Γ : Ctxt nfDialect)
    (ts : List NfTy) :
    PassChain.StepCert (fieldStep Γ ts).run
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ Γ ts)
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ Γ ts) :=
  @inlineCert nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ fieldLib tf (fieldLib_sound hF tf) 1
    Γ ts

/-- The input relation of the certificate of the field step is equality. -/
theorem fieldCert_relIn {bi : Builtins} (hF : FieldCalls bi) (tf : Nat) (Γ : Ctxt nfDialect)
    (ts : List NfTy) : (fieldCert hF tf Γ ts).relIn = Eq := rfl

/-- The output relation of the certificate of the field step is equality. -/
theorem fieldCert_relOut {bi : Builtins} (hF : FieldCalls bi) (tf : Nat) (Γ : Ctxt nfDialect)
    (ts : List NfTy) : (fieldCert hF tf Γ ts).relOut = Eq := rfl

/-! ## 7. The union with the library of a crate -/

/-- The builtins with the functions of a crate answer the narrow field heads by their arms
    when `bi` does and no function of the crate has a field head as its name. -/
theorem FieldCalls.crateBi {bi : Builtins} (hF : FieldCalls bi) (fs : List CrateFn)
    (hfs : ∀ f, _root_.Hax.FieldTag.fieldHeadB f = true → fs.find? (·.name == f) = none)
    (fuelC n : Nat) : FieldCalls (crateBi fs bi fuelC n) := by
  refine ⟨fun f m p ht hp a b => ?_, fun f m p k ht hodd hp a b => ?_⟩
  · rw [crateBi_of_find_none fs bi fuelC n
      (hfs f (_root_.Hax.FieldTag.fieldHeadB_of_fieldTag? ht))]
    exact hF.canon f m p ht hp a b
  · rw [crateBi_of_find_none fs bi fuelC n
      (hfs f (_root_.Hax.FieldTag.fieldHeadB_of_fieldTagM? ht))]
    exact hF.mont f m p k ht hodd hp a b

/-- **The union of the library of a crate and the library of the tagged field calls is sound
    from the call depth `m + 1` to the call depth `m`**, for the operations that call no
    function of the crate, under the typing of the builtins `bi` and `RepeatCalls bi`, when
    `bi` answers the narrow field heads by their arms and no function of the crate has a field
    head or `repeat` as its name. -/
theorem crateFieldLib_soundStep (fs : List CrateFn) (bi : Builtins)
    (hT : TypedCalls bi hax64SigOf) (hR : RepeatCalls bi) (hF : FieldCalls bi)
    (hfs : ∀ f, _root_.Hax.FieldTag.fieldHeadB f = true → fs.find? (·.name == f) = none)
    (hfR : fs.find? (·.name == "repeat") = none) (fuelC m tf : Nat) :
    ((crateLib fs).union fieldLib).SoundStep (nfDenote (tableOf (crateBi fs bi fuelC (m + 1))))
      (nfDenote (tableOf (crateBi fs bi fuelC m))) (fun o => !crateCallOp fs o) tf :=
  (crateLib_soundStep fs bi hT hR hfR fuelC m tf).union
    (fieldLib_soundStep (hF.crateBi fs hfs fuelC (m + 1)) _ tf)

/-! ## 8. Leakage of the bodies -/

/-- **The leakage models in which the word operations of the bodies are quiet**: constants
    and the operations `add`, `sub`, `mul`, `and`, `lshr` at 64 bits emit no event. -/
structure QuietWordOps (M : LeakModel nfDialect) : Prop where
  /-- A constant emits no event. -/
  const : ∀ v : BitVec 64, M.kind (.const 64 v) = .quiet
  /-- An addition emits no event. -/
  add : M.kind (.bin .add 64) = .quiet
  /-- A subtraction emits no event. -/
  sub : M.kind (.bin .sub 64) = .quiet
  /-- A multiplication emits no event. -/
  mul : M.kind (.bin .mul 64) = .quiet
  /-- A conjunction emits no event. -/
  and : M.kind (.bin .and 64) = .quiet
  /-- A logical shift right emits no event. -/
  lshr : M.kind (.bin .lshr 64) = .quiet

variable {M : LeakModel nfDialect}

/-- The level checker accepts the conditional subtract at every labelling. -/
theorem csubK_levelCheck' (hM : QuietWordOps M) {Γ : Ctxt nfDialect} (P : Nat) (x : Var Γ W)
    (L : Labels Γ) : (NFProg.levelCheck' M (csubK P x) L).isSome := by
  simp [csubK, mkE, NFProg.levelCheck', opAccepts, hM.const, hM.add, hM.sub, hM.and, hM.lshr]

/-- The level checker accepts the folds followed by the conditional subtract at every
    labelling. -/
theorem reduceK_levelCheck' (hM : QuietWordOps M) (c P : Nat) :
    ∀ (n : Nat) {Γ : Ctxt nfDialect} (x : Var Γ W) (L : Labels Γ),
      (NFProg.levelCheck' M (reduceK c P n x) L).isSome
  | 0, _, x, L => csubK_levelCheck' hM P x L
  | n + 1, _, x, L => by
      simp only [reduceK, mkE, NFProg.levelCheck', opAccepts, hM.const, hM.add, hM.mul, hM.and,
        hM.lshr, ite_true]
      exact reduceK_levelCheck' hM c P n .here _

/-- **The level checker accepts every body at every labelling of its arguments**, for a
    leakage model in which the word operations of the bodies are quiet. -/
theorem fieldBody_levelCheck' (hM : QuietWordOps M) (m : FieldMethod) (p n : Nat)
    (L : Labels (d := nfDialect) m.sig) :
    (NFProg.levelCheck' M (fieldBody m p n) L).isSome := by
  cases m <;>
    simp only [fieldBody, mkE, NFProg.levelCheck', opAccepts, hM.const, hM.add, hM.sub, hM.mul,
      ite_true] <;>
    first
      | exact csubK_levelCheck' hM _ _ _
      | exact reduceK_levelCheck' hM _ _ _ _ _

/-- **The level checker accepts every body of the library at every labelling of its
    arguments.** -/
theorem fieldOp_levelCheck' (hM : QuietWordOps M) :
    ∀ (o : NfOp) (b : NFProg nfDialect o.sig [o.ret]), fieldOp o = some b →
      ∀ L : Labels (d := nfDialect) o.sig, (NFProg.levelCheck' M b L).isSome := by
  intro o
  induction o with
  | call f as r =>
      intro b hb L
      simp only [fieldOp, Option.bind_eq_some_iff] at hb
      obtain ⟨⟨m, p⟩, -, n, -, hb⟩ := hb
      split at hb
      · rename_i hty
        cases hb
        obtain ⟨rfl, rfl⟩ := hty
        exact fieldBody_levelCheck' hM m p n L
      · cases hb
  | named _ o ih =>
      intro b hb L
      exact ih b hb L
  | _ =>
      intro b hb
      cases hb

/-- **A body is constant time with all arguments secret**: at every leaf table and fuel, for
    a leakage model in which the word operations of the bodies are quiet, two successful runs
    of a body emit equal events. -/
theorem fieldBody_nfCTRel (hM : QuietWordOps M) (T : NfLeafTable) (fuel : Nat)
    (m : FieldMethod) (p n : Nat) :
    @NFCTRel nfDialect _ _ _ _ (nfDenote T) M _ _ (allSecret m.sig) fuel (fieldBody m p n) :=
  @NFProg.nfCTRel_of_levelCheck' nfDialect _ _ _ _ (nfDenote T) M fuel _ _ _ _
    (fieldBody_levelCheck' hM m p n _)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldLevel
