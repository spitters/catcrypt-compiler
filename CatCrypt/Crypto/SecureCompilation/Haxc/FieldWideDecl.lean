/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline

/-!
# Declarations and bodies of the wide tagged field calls

A tagged field call `Hax.FieldTag.fieldHead m p` at a modulus `p ≥ 2^64` takes and returns
arrays of `n = Hax.FieldTag.fieldLimbs p` `64`-bit words holding the canonical limbs of the
field elements (`Hax.FieldTag.limbsOf`). This module gives such a call a declaration for the
translation `nfToCatExt` and a body for the inlining at the wide templates of
`FieldWideInline`; the call environment `tableEnv` of the builtin table answers the call at
its word-array result.

`wideDecl f m p` declares the head `f` at the argument types of `m` on word arrays of
`fieldLimbs p` limbs, with the function of the `u64` table. `wideBody f as rs` is the body
`wideBlockOf W m` of a head at a modulus with a wide template `W = wideTemplateOf p`, and
the body `montWordBlockOf P m` on registers of a head at an odd modulus `1 < p < 2^64` with
the one-limb record `P = montWordOf p`.

## Main definitions

* `wideDecl` — the declaration of a wide tagged head.
* `wideBody` — the body of a tagged head at a wide template or a one-limb record.

## Main results

* `wideDecl_inTable` — a table equal to the `u64` table at the wide tagged heads
  (`FieldLevel.FieldCallsWideEq`) has the declaration of a wide tagged head.
* `wideDecl_implementedBy` — the declaration is implemented by
  `catEnvOf (tableEnv Hax.hax64Builtins)`.
* `dec_wordsOf` — `dec` reads the source values of a word array back as the array.
* `hax64Builtins_wide` — a value of the `u64` table at a wide tagged head on word arrays is the
  array of the limbs of `fieldVal` of the numbers the arrays hold, below the modulus.
* `tableEnv_word` — a value of the `u64` table at a tagged head on registers is the word of
  `fieldVal` of the numbers the registers hold, below the modulus.
* `wideBody_sound` — a body of `wideBody` returns, at every call environment and fuel, the
  value `tableEnv Hax.hax64Builtins` gives the head.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideDecl

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy arrLimbs)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (dec encAll tableOf)
open Ctxt (Var Valuation)
open _root_.Hax (Value Builtins)
open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldLimbs limbsOf limbsDec fieldVal)

/-! ## 1. The declaration of a wide tagged head -/

/-- **The declaration of the wide tagged head `f` of the method `m` at the modulus `p`**: at
    the argument types of `m` on arrays of `fieldLimbs p` `64`-bit words and the result type
    of such arrays, with the function of the `u64` table. -/
def wideDecl (f : String) (m : FieldMethod) (p : Nat) : ExtDecl :=
  ⟨f, m.sigAt (.arr (fieldLimbs p) (.word 64)), .arr (fieldLimbs p) (.word 64),
    (tableOf _root_.Hax.hax64Builtins).call f (m.sigAt (.arr (fieldLimbs p) (.word 64)))
      (.arr (fieldLimbs p) (.word 64))⟩

/-- The argument types of a method on word arrays are types of word arrays. -/
theorem wordArrTy_sigAt (m : FieldMethod) (n : Nat) :
    ∀ t ∈ m.sigAt (.arr n (.word 64)), wordArrTy t = true := by
  cases m <;> simp [FieldMethod.sigAt, FieldMethod.binary, wordArrTy]

/-- The declaration of a wide tagged head has a signature of word arrays. -/
theorem wideDecl_wordSig (f : String) (m : FieldMethod) (p : Nat) :
    (wideDecl f m p).wordSig = true := by
  simp only [ExtDecl.wordSig, wordArrSig, wideDecl, Bool.and_eq_true, List.all_eq_true]
  exact ⟨wordArrTy_sigAt m _, rfl⟩

/-- **A table equal to the `u64` table at the wide tagged heads has the declaration of a wide
    tagged head.** -/
theorem wideDecl_inTable {bi : Builtins} (hW : FieldLevel.FieldCallsWideEq bi) {f : String}
    {m : FieldMethod} {p : Nat} (ht : fieldTag? f = some (m, p)) (hp : 2 ^ 64 ≤ p) :
    (wideDecl f m p).InTable bi := by
  intro xs
  change (bi f (encAll _ xs)).bind _ = (_root_.Hax.hax64Builtins f (encAll _ xs)).bind _
  rw [hW f m p ht hp]
  rfl

/-- **The declaration of a wide tagged head is implemented by the environment read off the
    `u64` table**, which answers word-array results. -/
theorem wideDecl_implementedBy (f : String) (m : FieldMethod) (p : Nat) :
    (wideDecl f m p).ImplementedBy (catEnvOf (tableEnv _root_.Hax.hax64Builtins)) := by
  refine implementedBy_catEnvOf _ _ fun xs ws y hws hy => ?_
  obtain ⟨v, hv, hd⟩ := Option.bind_eq_some_iff.mp hy
  refine ⟨y, ?_, fun _ => rfl⟩
  change ((_root_.Hax.hax64Builtins f (denVals (transArgs mapTy (fun x => ctTransTy x) ws))).bind
    fun v => (dec (.arr (fieldLimbs p) (.word 64)) v).map fun y =>
      (HVector.cons y .nil : Valuation (d := jasminDialect) [.stackArr 64 (fieldLimbs p)])) = _
  have h1 := denVals_transArgs _ (wordArrTy_sigAt m (fieldLimbs p)) xs ws hws
  exact Option.bind_eq_some_iff.mpr ⟨v, h1 ▸ hv, by rw [hd]; rfl⟩

/-! ## 3. The body of a wide tagged head -/

/-- The source value of a word array is the array of its source values `wordsOf`. -/
theorem arrVal_eq_wordsOf {n : Nat} (a : Fin n → BitVec 64) :
    arrVal a = .array (wordsOf a) := by
  rw [wordsOf, limbWords_arrLimbs a n 0]
  simp only [arrVal, Nat.zero_add]

/-- **`dec` reads the source values of a word array back as the array.** -/
theorem dec_wordsOf {n : Nat} (a : Fin n → BitVec 64) :
    dec (.arr n (.word 64)) (.array (wordsOf a)) = some a := by
  have hm : ∀ l : List Nat, (l.map fun i => Value.int ((stackGet a i).toNat : Int)).mapM
      (dec (.word 64)) = some (l.map (stackGet a)) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
        have hl := (stackGet a i).isLt
        have hd : dec (.word 64) (.int ((stackGet a i).toNat : Int)) = some (stackGet a i) := by
          simp only [dec]
          rw [ite_eq_left (by omega)]
          simp
        simp only [List.map_cons, List.mapM_cons, hd, ih]
        rfl
  rw [wordsOf, limbWords_arrLimbs a n 0]
  simp only [Nat.zero_add]
  change ((((List.range n).map fun i => Value.int ((stackGet a i).toNat : Int)).mapM
    (dec (.word 64))).bind fun ys =>
      if h : ys.length = n then some fun i => ys[i.1]'(h ▸ i.2) else none) = some a
  rw [hm, Option.bind_some, dite_eq_left (by simp)]
  refine congrArg some (funext fun i => ?_)
  simp only [List.getElem_map, List.getElem_range]
  obtain ⟨i, hi⟩ := i
  cases n with
  | zero => omega
  | succ k => exact congrArg a (Fin.ext (Nat.mod_eq_of_lt hi))

/-- **The `u64` table at a wide tagged head on word arrays.** A value of `Hax.hax64Builtins` at
    a head of the method `m` at the modulus `p`, on the source values of arrays at the signature
    `wideSig` of `m`, is the array of the limbs of `fieldVal m p a b`, where `limbsDec` reads
    the first array as `a < p` and, for a method with two arguments, the second as `b < p`. -/
theorem hax64Builtins_wide {f : String} {m : FieldMethod} {p : Nat}
    (ht : fieldTag? f = some (m, p))
    (x : Valuation (d := jasminDialect) (wideSig (fieldLimbs p) m)) {v : Value}
    (hv : _root_.Hax.hax64Builtins f (denVals x) = some v) :
    ∃ a b : Nat, limbsDec (wordsOf (wideArrs m x).1) = some a ∧ a < p ∧
      (m.binary = true → limbsDec (wordsOf (wideArrs m x).2) = some b ∧ b < p) ∧
      v = .array (limbsOf (fieldLimbs p) (fieldVal m p a b)) := by
  have hc := _root_.Hax.hax64Builtins_of_fieldTag? ht hv
  have two : ∀ xs ys : List Value,
      _root_.Hax.FieldTag.fieldCall m p [.array xs, .array ys] = some v →
      ∃ a b : Nat, limbsDec xs = some a ∧ limbsDec ys = some b ∧ a < p ∧
        (m.binary = true → b < p) ∧ v = .array (limbsOf (fieldLimbs p) (fieldVal m p a b)) := by
    intro xs ys h
    simp only [_root_.Hax.FieldTag.fieldCall] at h
    split at h
    · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      unfold _root_.Hax.FieldTag.fieldArmWide at h
      split at h
      · rename_i hl
        cases h
        exact ⟨a, b, ha, hb, hl.1, hl.2, rfl⟩
      · cases h
    · cases h
  have one : ∀ xs : List Value, _root_.Hax.FieldTag.fieldCall m p [.array xs] = some v →
      ∃ a : Nat, limbsDec xs = some a ∧ a < p ∧
        v = .array (limbsOf (fieldLimbs p) (fieldVal m p a 0)) := by
    intro xs h
    simp only [_root_.Hax.FieldTag.fieldCall] at h
    split at h
    · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      unfold _root_.Hax.FieldTag.fieldArmWide at h
      split at h
      · rename_i hl
        cases h
        exact ⟨a, ha, hl.1, rfl⟩
      · cases h
    · cases h
  cases m <;> rcases x with _ | ⟨A, _ | ⟨B, _ | _⟩⟩ <;>
    change _root_.Hax.FieldTag.fieldCall _ p (denVals _) = some v at hc
  all_goals first
    | (change _root_.Hax.FieldTag.fieldCall _ p [arrVal A, arrVal B] = some v at hc
       rw [arrVal_eq_wordsOf A, arrVal_eq_wordsOf B] at hc
       obtain ⟨a, b, ha, hb, hap, hbp, rfl⟩ := two _ _ hc
       exact ⟨a, b, ha, hap, fun h => ⟨hb, hbp h⟩, rfl⟩)
    | (change _root_.Hax.FieldTag.fieldCall _ p [arrVal A] = some v at hc
       rw [arrVal_eq_wordsOf A] at hc
       obtain ⟨a, ha, hap, rfl⟩ := one _ hc
       exact ⟨a, 0, ha, hap, fun h => absurd h (by decide), rfl⟩)

/-! ## 4. The body of a tagged head over one limb -/

/-- **The `u64` table at a tagged head on registers.** When the call environment read off
    the `u64` table answers the tagged head of `m` at `p < 2^64` on a valuation at the
    signature `wordSig` of `m`, the numbers of the valuation are below `p` and the result is
    the word of `fieldVal m p` of the numbers. -/
theorem tableEnv_word {p : Nat} (hp : p < 2 ^ 64) {f : String} {m : FieldMethod}
    (ht : fieldTag? f = some (m, p)) (x : Valuation (d := jasminDialect) (wordSig m))
    (y : Valuation (d := jasminDialect) [.reg 64])
    (hy : (tableEnv _root_.Hax.hax64Builtins).call f (wordSig m) [.reg 64] x = some y) :
    (wordNats m x).1 < p ∧ (m.binary = true → (wordNats m x).2 < p) ∧
      y = .cons (BitVec.ofNat 64 (fieldVal m p (wordNats m x).1 (wordNats m x).2)) .nil := by
  change ((_root_.Hax.hax64Builtins f (denVals x)).bind fun v =>
      (dec (.word 64) v).map fun z =>
        (HVector.cons z .nil : Valuation (d := jasminDialect) [.reg 64])) = some y at hy
  have hd : denVals x = _root_.Hax.FieldTag.fieldArgs m (wordNats m x).1 (wordNats m x).2 := by
    cases m <;> rcases x with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl
  rw [hd, _root_.Hax.hax64Builtins_fieldArgs ht hp] at hy
  unfold _root_.Hax.FieldTag.fieldArm at hy
  split at hy
  · rename_i hc
    refine ⟨hc.1, hc.2, ?_⟩
    have hv := _root_.Hax.FieldTag.fieldVal_lt m (by omega : 0 < p) (wordNats m x).1
      (wordNats m x).2
    have hdec : dec (.word 64) (.int ((fieldVal m p (wordNats m x).1 (wordNats m x).2 : Nat)
        : Int)) = some (BitVec.ofNat 64 (fieldVal m p (wordNats m x).1 (wordNats m x).2)) := by
      simp only [dec]
      rw [ite_eq_left (by omega)]
      simp
    rw [Option.bind_some, hdec, Option.map_some] at hy
    cases hy
    rfl
  · cases hy

/-- **The body of a wide tagged head** at the signature `as → rs`: for a head of the method
    `m` at a modulus `p` with a wide template `W` (`wideTemplateOf p`), at the signature
    `wideSig` of `m` with one word-array result, the body `wideBlockOf W m`; at a modulus
    with a one-limb Montgomery record `P` (`montWordOf p`), at the signature `wordSig` of
    `m` with one `64`-bit result, the body `montWordBlockOf P m`; `none` otherwise. -/
def wideBody (f : String) (as rs : List JasminTy) : Option (NFProg jasminDialect as rs) :=
  match fieldTag? f with
  | some (m, p) =>
      match wideTemplateOf p with
      | some W =>
          if hs : as = wideSig (fieldLimbs p) m ∧ rs = [arrTy (fieldLimbs p)] then
            some (hs.1 ▸ hs.2 ▸ wideBlockOf W m)
          else none
      | none =>
          match montWordOf p with
          | some P =>
              if hs : as = wordSig m ∧ rs = [.reg 64] then
                some (hs.1 ▸ hs.2 ▸ montWordBlockOf P m)
              else none
          | none => none
  | none => none

/-- **A body of a wide tagged head returns the value of the `u64` table.** When
    `tableEnv Hax.hax64Builtins` answers the head `f` at the signature `as → rs` on `x`
    by `y`, the body `wideBody f as rs` returns `y` on `x`, at every call environment and
    fuel: the table is defined on arrays or registers whose numbers are below the modulus
    only, and on them the body returns the limbs of the value of the method
    (`hax64Builtins_wide`, `wideBlock_denoteAt`, `tableEnv_word`,
    `montWordBlock_denoteAt`). -/
theorem wideBody_sound (E : CallEnv jasminDialect) (fuel : Nat) {f : String}
    {as rs : List JasminTy} {b : NFProg jasminDialect as rs} (hb : wideBody f as rs = some b)
    (x : Valuation (d := jasminDialect) as) (y : Valuation (d := jasminDialect) rs)
    (hy : (tableEnv _root_.Hax.hax64Builtins).call f as rs x = some y) :
    b.denoteAt E fuel x = some y := by
  unfold wideBody at hb
  split at hb
  · rename_i m p ht
    split at hb
    · rename_i W _
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        change ((_root_.Hax.hax64Builtins f (denVals x)).bind fun v =>
          (dec (.arr (fieldLimbs p) (.word 64)) v).map fun z =>
            (HVector.cons z .nil : Valuation (d := jasminDialect) [arrTy (fieldLimbs p)]))
              = some y at hy
        obtain ⟨v, hv, hd⟩ := Option.bind_eq_some_iff.mp hy
        obtain ⟨a, c, ha, hap, hc, rfl⟩ := hax64Builtins_wide ht x hv
        obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hd
        obtain ⟨y', hy', hw⟩ := wideBlock_denoteAt W x ha hap hc E fuel
        rw [← hw, dec_wordsOf] at hz
        cases hz
        exact hy'
      · cases hb
    · split at hb
      · rename_i P hP
        split at hb
        · rename_i hs
          obtain ⟨rfl, rfl⟩ := hs
          cases hb
          obtain rfl := montWordOf_p hP
          have hp64 : P.p < 2 ^ 64 := by simpa using P.p_lt
          obtain ⟨ha, hb', rfl⟩ := tableEnv_word hp64 ht x y hy
          exact montWordBlock_denoteAt P x ha hb' E fuel
        · cases hb
      · cases hb
  · cases hb

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideDecl
