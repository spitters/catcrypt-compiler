/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFFrontDesugar
public import CatCrypt.Hax.ReifyField
public import HaxLean.DenoteTotal

/-!
# Compiled bytes of a reified Lean function over `ZMod p`

A Lean function `f` over `ZMod p` is read by `reifyField%` as an `ImpExpr` literal whose
field operations are calls of the tagged heads `fieldHead m p`, and `ascend_reified` proves
that the literal denotes `f` (`FnCorres`). This module states the facts that connect such a
literal with the compiler `compileA`.

* The table `hax64WExit` of the compiler answers a tagged head at a modulus below `2^64` on
  encoded elements by the encoding of the field operation, as `Hax.hax64Builtins` does
  (`fieldCalls_hax64WExit`, `FieldLevel.fieldCalls_hax64Builtins`).
* A numeral of `ZMod p` is read by `reifyField%` as an integer literal `k`, which the ascent
  generator types as `enc (k : ℤ)`. The encoding of `(k : ZMod p)` is that literal for
  `0 ≤ k < p` (`enc_intCast_zmod`), and the call leaves with a literal operand
  (`hax64WExit_zmod_mul_litL` and its siblings) state the table at such a call in the form
  the generator matches.
* The canonical environment of a layout without constants is `bindParams` of its
  parameters and the values their registers denote (`canonEnv_eq_bindParams`).
* `leanFront_correct`: an ascent result under `hax64WExit` from an entry environment
  `bindParams` that is the canonical environment of the entry state gives the decoded bytes
  of `compileA` halting with the encoding of `f a`.
* At a modulus `p ≥ 2^64` an element of `ZMod p` is encoded as the array of the limbs of its
  canonical representative (`enc_zmod_wide`), the operands and results of a wide tagged head.
  `leanFront_correct_field2` and `leanFront_correct_field1` state `leanFront_correct` for one
  field operation under a layout with an output buffer at `%rdi`, as the multi-limb templates
  of the chain compile it, with the result read back as limbs.

## Main results

* `hax64WExit_zmod_add`, `_sub`, `_mul`, `_neg`, `_square`, `_double` — the table
  `hax64WExit` at the tagged heads on encoded elements.
* `enc_natCast_zmod`, `enc_intCast_zmod` — the encoding of a numeral of `ZMod p`.
* `hax64WExit_zmod_add_litL` and the other literal leaves — a call with an integer literal
  operand.
* `hax64WExit_babyBear_mul` and the other BabyBear leaves — the leaves at the BabyBear heads,
  in the form `ascend_reified` indexes.
* `affine_fnCorres` — `ascend_reified` on a literal with numerals, under `hax64WExit`.
* `canonEnv_eq_bindParams_read`, `canonEnv_eq_bindParams`, `canonEnv_eq_bindParams_words` —
  the canonical environment of a layout without constants.
* `leanFront_correct`, `leanFront_correct_scalar`, `leanFront_correct_words` — the decoded
  bytes of `compileA` compute the function of an ascent result under `hax64WExit`.
* `hax64WExit_zmod_add_wide`, `_sub_wide`, `_mul_wide`, `_neg_wide` — the table `hax64WExit` at
  the tagged heads at a modulus `p ≥ 2^64`, on limb arrays.
* `fnCorres_fieldOp2`, `fnCorres_fieldOp1` — the literal of one field operation corresponds to
  it, from an entry environment with an output buffer.
* `leanFront_correct_field2`, `leanFront_correct_field1` — the decoded bytes of `compileA` on
  the literal of a function over a wide prime field, under a layout with an output buffer at
  `%rdi`, write the limbs of its value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax (hax64WExit spineLamFree)
open _root_.Hax (TExpr Value Env denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open _root_.Hax.Ascent (FnCorres HaxEnc enc bindParams)
open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldArgs fieldVal fieldLimbs limbsOf)
open CatCrypt.Hax.ReifyField (enc_zmod enc_zmod_wide)

/-! ## The table `hax64WExit` at the tagged heads -/

section Leaves

variable {p : ℕ} [NeZero p] {f : String}

omit [NeZero p] in
/-- At a tagged head of a method with two arguments at a modulus below `2^64`, the table
    `hax64WExit` on encoded elements is the table `Hax.hax64Builtins`. -/
theorem hax64WExit_zmod_eq_binary {m : FieldMethod} (ht : fieldTag? f = some (m, p))
    (hp : p < 2 ^ 64) (hm : m.binary = true) (x y : ZMod p) :
    hax64WExit f [enc x, enc y] = _root_.Hax.hax64Builtins f [enc x, enc y] := by
  have h := (fieldCalls_hax64WExit.canon f m p ht hp x.val y.val).trans
    (FieldLevel.fieldCalls_hax64Builtins.canon f m p ht hp x.val y.val).symm
  simp only [fieldArgs, hm, ite_true] at h
  rw [enc_zmod hp, enc_zmod hp]
  exact h

omit [NeZero p] in
/-- At a tagged head of a method with one argument at a modulus below `2^64`, the table
    `hax64WExit` on an encoded element is the table `Hax.hax64Builtins`. -/
theorem hax64WExit_zmod_eq_unary {m : FieldMethod} (ht : fieldTag? f = some (m, p))
    (hp : p < 2 ^ 64) (hm : m.binary = false) (x : ZMod p) :
    hax64WExit f [enc x] = _root_.Hax.hax64Builtins f [enc x] := by
  have h := (fieldCalls_hax64WExit.canon f m p ht hp x.val 0).trans
    (FieldLevel.fieldCalls_hax64Builtins.canon f m p ht hp x.val 0).symm
  simp only [fieldArgs, hm, Bool.false_eq_true, ite_false] at h
  rw [enc_zmod hp]
  exact h

/-- The table `hax64WExit` answers the tagged head of `add` by the encoding of the sum. -/
theorem hax64WExit_zmod_add (ht : fieldTag? f = some (.add, p)) (hp : p < 2 ^ 64)
    (x y : ZMod p) : hax64WExit f [enc x, enc y] = some (enc (x + y)) := by
  rw [hax64WExit_zmod_eq_binary ht hp rfl]
  exact CatCrypt.Hax.ReifyField.hax64Builtins_zmod_add ht hp x y

/-- The table `hax64WExit` answers the tagged head of `sub` by the encoding of the
    difference. -/
theorem hax64WExit_zmod_sub (ht : fieldTag? f = some (.sub, p)) (hp : p < 2 ^ 64)
    (x y : ZMod p) : hax64WExit f [enc x, enc y] = some (enc (x - y)) := by
  rw [hax64WExit_zmod_eq_binary ht hp rfl]
  exact CatCrypt.Hax.ReifyField.hax64Builtins_zmod_sub ht hp x y

/-- The table `hax64WExit` answers the tagged head of `mul` by the encoding of the
    product. -/
theorem hax64WExit_zmod_mul (ht : fieldTag? f = some (.mul, p)) (hp : p < 2 ^ 64)
    (x y : ZMod p) : hax64WExit f [enc x, enc y] = some (enc (x * y)) := by
  rw [hax64WExit_zmod_eq_binary ht hp rfl]
  exact CatCrypt.Hax.ReifyField.hax64Builtins_zmod_mul ht hp x y

/-- The table `hax64WExit` answers the tagged head of `neg` by the encoding of the
    negation. -/
theorem hax64WExit_zmod_neg (ht : fieldTag? f = some (.neg, p)) (hp : p < 2 ^ 64)
    (x : ZMod p) : hax64WExit f [enc x] = some (enc (-x)) := by
  rw [hax64WExit_zmod_eq_unary ht hp rfl]
  exact CatCrypt.Hax.ReifyField.hax64Builtins_zmod_neg ht hp x

/-- The table `hax64WExit` answers the tagged head of `square` by the encoding of the
    square. -/
theorem hax64WExit_zmod_square (ht : fieldTag? f = some (.square, p)) (hp : p < 2 ^ 64)
    (x : ZMod p) : hax64WExit f [enc x] = some (enc (x * x)) := by
  rw [hax64WExit_zmod_eq_unary ht hp rfl,
    CatCrypt.Hax.ReifyField.hax64Builtins_zmod_unary ht hp rfl, enc_zmod hp, ZMod.val_mul]
  rfl

/-- The table `hax64WExit` answers the tagged head of `double` by the encoding of the
    double. -/
theorem hax64WExit_zmod_double (ht : fieldTag? f = some (.double, p)) (hp : p < 2 ^ 64)
    (x : ZMod p) : hax64WExit f [enc x] = some (enc (x + x)) := by
  rw [hax64WExit_zmod_eq_unary ht hp rfl,
    CatCrypt.Hax.ReifyField.hax64Builtins_zmod_unary ht hp rfl, enc_zmod hp, ZMod.val_add,
    ← two_mul]
  rfl

end Leaves

/-! ## The table `hax64WExit` at the wide tagged heads -/

section WideLeaves

variable {p : ℕ} [NeZero p] {f : String}

/-- At a modulus `p ≥ 2^64` the table `hax64WExit` answers the tagged head of `add` on limb
    arrays by the encoding of the sum. -/
theorem hax64WExit_zmod_add_wide (ht : fieldTag? f = some (.add, p)) (hp : 2 ^ 64 ≤ p)
    (x y : ZMod p) : hax64WExit f [enc x, enc y] = some (enc (x + y)) := by
  rw [CatCrypt.Crypto.Hax.hax64WExit_wide ⟨_, _, ht, hp⟩]
  exact CatCrypt.Hax.ReifyField.hax64Builtins_zmod_add_wide ht hp x y

/-- At a modulus `p ≥ 2^64` the table `hax64WExit` answers the tagged head of `sub` on limb
    arrays by the encoding of the difference. -/
theorem hax64WExit_zmod_sub_wide (ht : fieldTag? f = some (.sub, p)) (hp : 2 ^ 64 ≤ p)
    (x y : ZMod p) : hax64WExit f [enc x, enc y] = some (enc (x - y)) := by
  rw [CatCrypt.Crypto.Hax.hax64WExit_wide ⟨_, _, ht, hp⟩]
  exact CatCrypt.Hax.ReifyField.hax64Builtins_zmod_sub_wide ht hp x y

/-- At a modulus `p ≥ 2^64` the table `hax64WExit` answers the tagged head of `mul` on limb
    arrays by the encoding of the product. -/
theorem hax64WExit_zmod_mul_wide (ht : fieldTag? f = some (.mul, p)) (hp : 2 ^ 64 ≤ p)
    (x y : ZMod p) : hax64WExit f [enc x, enc y] = some (enc (x * y)) := by
  rw [CatCrypt.Crypto.Hax.hax64WExit_wide ⟨_, _, ht, hp⟩]
  exact CatCrypt.Hax.ReifyField.hax64Builtins_zmod_mul_wide ht hp x y

/-- At a modulus `p ≥ 2^64` the table `hax64WExit` answers the tagged head of `neg` on a limb
    array by the encoding of the negation. -/
theorem hax64WExit_zmod_neg_wide (ht : fieldTag? f = some (.neg, p)) (hp : 2 ^ 64 ≤ p)
    (x : ZMod p) : hax64WExit f [enc x] = some (enc (-x)) := by
  rw [CatCrypt.Crypto.Hax.hax64WExit_wide ⟨_, _, ht, hp⟩]
  exact CatCrypt.Hax.ReifyField.hax64Builtins_zmod_neg_wide ht hp x

end WideLeaves

/-! ## Numerals -/

section Numerals

variable {p : ℕ} [NeZero p] {f : String}

omit [NeZero p] in
/-- The encoding of the numeral `(k : ZMod p)`, `k < p`, at a modulus below `2^64` is the
    integer `k`. -/
theorem enc_natCast_zmod (hp : p < 2 ^ 64) {k : ℕ} (hk : k < p) :
    enc (k : ZMod p) = .int k := by
  rw [enc_zmod hp, ZMod.val_natCast_of_lt hk]

omit [NeZero p] in
/-- The encoding of the integer literal `k`, `0 ≤ k < p`, at a modulus below `2^64` is the
    encoding of `(k : ZMod p)`: the value the ascent generator assigns to the literal
    `.lit (.int k)` that `reifyField%` reads off a numeral of `ZMod p` is the encoding of that
    numeral. -/
theorem enc_intCast_zmod (hp : p < 2 ^ 64) {k : ℤ} (h0 : 0 ≤ k) (hk : k < p) :
    (enc k : Value) = enc (k : ZMod p) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hn : n < p := by exact_mod_cast hk
  rw [Int.cast_natCast, enc_natCast_zmod hp hn]
  rfl

/-- The tagged head of `add` with an integer literal as left operand. -/
theorem hax64WExit_zmod_add_litL (ht : fieldTag? f = some (.add, p)) (hp : p < 2 ^ 64)
    (k : ℤ) (y : ZMod p) (h0 : 0 ≤ k) (hk : k < p) :
    hax64WExit f [enc k, enc y] = some (enc ((k : ZMod p) + y)) := by
  rw [enc_intCast_zmod hp h0 hk]; exact hax64WExit_zmod_add ht hp _ _

/-- The tagged head of `add` with an integer literal as right operand. -/
theorem hax64WExit_zmod_add_litR (ht : fieldTag? f = some (.add, p)) (hp : p < 2 ^ 64)
    (x : ZMod p) (k : ℤ) (h0 : 0 ≤ k) (hk : k < p) :
    hax64WExit f [enc x, enc k] = some (enc (x + (k : ZMod p))) := by
  rw [enc_intCast_zmod hp h0 hk]; exact hax64WExit_zmod_add ht hp _ _

/-- The tagged head of `sub` with an integer literal as left operand. -/
theorem hax64WExit_zmod_sub_litL (ht : fieldTag? f = some (.sub, p)) (hp : p < 2 ^ 64)
    (k : ℤ) (y : ZMod p) (h0 : 0 ≤ k) (hk : k < p) :
    hax64WExit f [enc k, enc y] = some (enc ((k : ZMod p) - y)) := by
  rw [enc_intCast_zmod hp h0 hk]; exact hax64WExit_zmod_sub ht hp _ _

/-- The tagged head of `sub` with an integer literal as right operand. -/
theorem hax64WExit_zmod_sub_litR (ht : fieldTag? f = some (.sub, p)) (hp : p < 2 ^ 64)
    (x : ZMod p) (k : ℤ) (h0 : 0 ≤ k) (hk : k < p) :
    hax64WExit f [enc x, enc k] = some (enc (x - (k : ZMod p))) := by
  rw [enc_intCast_zmod hp h0 hk]; exact hax64WExit_zmod_sub ht hp _ _

/-- The tagged head of `mul` with an integer literal as left operand. -/
theorem hax64WExit_zmod_mul_litL (ht : fieldTag? f = some (.mul, p)) (hp : p < 2 ^ 64)
    (k : ℤ) (y : ZMod p) (h0 : 0 ≤ k) (hk : k < p) :
    hax64WExit f [enc k, enc y] = some (enc ((k : ZMod p) * y)) := by
  rw [enc_intCast_zmod hp h0 hk]; exact hax64WExit_zmod_mul ht hp _ _

/-- The tagged head of `mul` with an integer literal as right operand. -/
theorem hax64WExit_zmod_mul_litR (ht : fieldTag? f = some (.mul, p)) (hp : p < 2 ^ 64)
    (x : ZMod p) (k : ℤ) (h0 : 0 ≤ k) (hk : k < p) :
    hax64WExit f [enc x, enc k] = some (enc (x * (k : ZMod p))) := by
  rw [enc_intCast_zmod hp h0 hk]; exact hax64WExit_zmod_mul ht hp _ _

end Numerals

/-! ## The leaves at the BabyBear heads -/

section BabyBear

open CatCrypt.Hax.ReifyField (affineLean affineImp)

/-- The table `hax64WExit` answers the BabyBear head of `add` by the encoding of the sum. -/
theorem hax64WExit_babyBear_add (x y : ZMod 2013265921) :
    hax64WExit "add#p2013265921" [enc x, enc y] = some (enc (x + y)) :=
  hax64WExit_zmod_add (by decide) (by norm_num) x y

/-- The table `hax64WExit` answers the BabyBear head of `sub` by the encoding of the
    difference. -/
theorem hax64WExit_babyBear_sub (x y : ZMod 2013265921) :
    hax64WExit "sub#p2013265921" [enc x, enc y] = some (enc (x - y)) :=
  hax64WExit_zmod_sub (by decide) (by norm_num) x y

/-- The table `hax64WExit` answers the BabyBear head of `mul` by the encoding of the
    product. -/
theorem hax64WExit_babyBear_mul (x y : ZMod 2013265921) :
    hax64WExit "mul#p2013265921" [enc x, enc y] = some (enc (x * y)) :=
  hax64WExit_zmod_mul (by decide) (by norm_num) x y

/-- The table `hax64WExit` answers the BabyBear head of `neg` by the encoding of the
    negation. -/
theorem hax64WExit_babyBear_neg (x : ZMod 2013265921) :
    hax64WExit "neg#p2013265921" [enc x] = some (enc (-x)) :=
  hax64WExit_zmod_neg (by decide) (by norm_num) x

/-- The BabyBear head of `add` with an integer literal as left operand. -/
theorem hax64WExit_babyBear_add_litL (k : ℤ) (y : ZMod 2013265921) (h0 : 0 ≤ k)
    (hk : k < 2013265921) :
    hax64WExit "add#p2013265921" [enc k, enc y] = some (enc ((k : ZMod 2013265921) + y)) :=
  hax64WExit_zmod_add_litL (by decide) (by norm_num) k y h0 (by exact_mod_cast hk)

/-- The BabyBear head of `add` with an integer literal as right operand. -/
theorem hax64WExit_babyBear_add_litR (x : ZMod 2013265921) (k : ℤ) (h0 : 0 ≤ k)
    (hk : k < 2013265921) :
    hax64WExit "add#p2013265921" [enc x, enc k] = some (enc (x + (k : ZMod 2013265921))) :=
  hax64WExit_zmod_add_litR (by decide) (by norm_num) x k h0 (by exact_mod_cast hk)

/-- The BabyBear head of `sub` with an integer literal as left operand. -/
theorem hax64WExit_babyBear_sub_litL (k : ℤ) (y : ZMod 2013265921) (h0 : 0 ≤ k)
    (hk : k < 2013265921) :
    hax64WExit "sub#p2013265921" [enc k, enc y] = some (enc ((k : ZMod 2013265921) - y)) :=
  hax64WExit_zmod_sub_litL (by decide) (by norm_num) k y h0 (by exact_mod_cast hk)

/-- The BabyBear head of `sub` with an integer literal as right operand. -/
theorem hax64WExit_babyBear_sub_litR (x : ZMod 2013265921) (k : ℤ) (h0 : 0 ≤ k)
    (hk : k < 2013265921) :
    hax64WExit "sub#p2013265921" [enc x, enc k] = some (enc (x - (k : ZMod 2013265921))) :=
  hax64WExit_zmod_sub_litR (by decide) (by norm_num) x k h0 (by exact_mod_cast hk)

/-- The BabyBear head of `mul` with an integer literal as left operand. -/
theorem hax64WExit_babyBear_mul_litL (k : ℤ) (y : ZMod 2013265921) (h0 : 0 ≤ k)
    (hk : k < 2013265921) :
    hax64WExit "mul#p2013265921" [enc k, enc y] = some (enc ((k : ZMod 2013265921) * y)) :=
  hax64WExit_zmod_mul_litL (by decide) (by norm_num) k y h0 (by exact_mod_cast hk)

/-- The BabyBear head of `mul` with an integer literal as right operand. -/
theorem hax64WExit_babyBear_mul_litR (x : ZMod 2013265921) (k : ℤ) (h0 : 0 ≤ k)
    (hk : k < 2013265921) :
    hax64WExit "mul#p2013265921" [enc x, enc k] = some (enc (x * (k : ZMod 2013265921))) :=
  hax64WExit_zmod_mul_litR (by decide) (by norm_num) x k h0 (by exact_mod_cast hk)

/-- From the entry environment binding `x`, the literal `affineImp`, which carries the
    numeral `3` of BabyBear as an integer literal, returns the encoding of `affineLean`
    under the table `hax64WExit`. -/
theorem affine_fnCorres :
    FnCorres hax64WExit affineImp (A := ZMod 2013265921 × Unit)
      (fun a => bindParams [("x", enc a.1)]) (fun _ => True) (fun a => affineLean a.1) := by
  ascend_reified affineLean using [hax64WExit_babyBear_mul_litL, hax64WExit_babyBear_add_litR,
    hax64WExit_babyBear_neg, hax64WExit_babyBear_sub]

end BabyBear

/-! ## The canonical environment of a layout without constants -/

/-- The environment of the first parameter named `y` of a list, bound to the value its
    register denotes, is `bindParams` of the parameters and their values. -/
theorem find_read_eq_bindParams (sa : AState) : ∀ l : List AbiArg,
    (fun y => match l.find? (·.name == y) with
      | some a => some (a.read sa)
      | none => none) = bindParams (l.map fun a => (a.name, a.read sa))
  | [] => by funext y; rfl
  | a :: l => by
    funext y
    have ih := congrFun (find_read_eq_bindParams sa l) y
    simp only [List.find?_cons, List.map_cons, bindParams, Env.extend] at ih ⊢
    by_cases h : a.name = y
    · subst h; simp
    · have h' : (y == a.name) = false := by simpa using Ne.symm h
      have h'' : (a.name == y) = false := by simpa using h
      simp only [h', h'', Bool.false_eq_true, ite_false]
      exact ih

/-- **The canonical environment of a layout without constants** binds each parameter to the
    value its register denotes, the first parameter of a name shadowing the rest. -/
theorem canonEnv_eq_bindParams_read (σ : AbiLayout) (hc : σ.consts = []) (sa : AState) :
    σ.canonEnv sa = bindParams (σ.args.map fun a => (a.name, a.read sa)) := by
  rw [← find_read_eq_bindParams sa σ.args]
  funext y
  cases h : σ.args.find? (·.name == y) <;> simp [AbiLayout.canonEnv, hc, h]

/-- **The canonical environment of a scalar layout**: when every parameter is a `u64`
    scalar and the layout binds no constant, the canonical environment binds each parameter
    to the integer of its register. -/
theorem canonEnv_eq_bindParams (σ : AbiLayout) (hs : ∀ a ∈ σ.args, a.kind = .scalar)
    (hc : σ.consts = []) (sa : AState) :
    σ.canonEnv sa =
      bindParams (σ.args.map fun a => (a.name, .int (sa.regs a.reg).toNat)) := by
  rw [canonEnv_eq_bindParams_read σ hc sa]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  simp only [AbiArg.read, hs a ha]

/-- **The canonical environment of a word-array layout**: when every parameter `a` is an
    array of `sz a` words and the layout binds no constant, the canonical environment binds
    each parameter to the array of the integer words its region holds. -/
theorem canonEnv_eq_bindParams_words (σ : AbiLayout) (sz : AbiArg → Nat)
    (hw : ∀ a ∈ σ.args, a.kind = .words (sz a)) (hc : σ.consts = []) (sa : AState) :
    σ.canonEnv sa = bindParams (σ.args.map fun a =>
      (a.name, .array (wordsAt sa.mem (sa.regs a.reg) (sz a)))) := by
  rw [canonEnv_eq_bindParams_read σ hc sa]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  simp only [AbiArg.read, hw a ha]

/-! ## Compiled bytes of a reified function -/

/-- **Compiled bytes compute the function of an ascent result under `hax64WExit`.** Let
    `compileA` return `(P, bytes)` on the typed extraction `te` under the layout `σ`, whose
    names are pairwise distinct, let the statement spine of `te.erase` bind no closure, and
    let `te.erase` from the entry environment `bindParams (ps a)` return the encoding of
    `f a` under the table `hax64WExit` for every argument `a` in the guard. Then from every
    entry state `sa` satisfying `σ.Regions` whose canonical environment is
    `bindParams (ps a)` for an argument `a` in the guard, the bytes decode to a program that
    halts in a state from which `σ` reads back the encoding of `f a`, on a layout whose narrow
    parameters are not cut to their widths (`hn`). -/
theorem leanFront_correct {A β : Type} [HaxEnc β] [HaxEnc.Plain β] (te : TExpr)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA te σ fname = some (P, bytes)) (hsp : spineLamFree te.erase = true)
    (ps : A → List (String × Value)) (G : A → Prop) (f : A → β)
    (hf : FnCorres hax64WExit te.erase (fun a => bindParams (ps a)) G f)
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (a : A) (hG : G a)
    (hcanon : σ.canonEnv sa = bindParams (ps a)) (hn : narrowOk te σ = false := by rfl) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (enc (f a)) := by
  have he : narrowEntry te σ sa = sa := by simp [narrowEntry, hn]
  obtain ⟨fuel, hr⟩ := hf a hG
  have hrun : (denoteSpine hax64WExit fuel te.erase).run (bindParams (ps a)) =
      (.val (enc (f a)), (denote' hax64WExit fuel te.erase (bindParams (ps a))).2) := by
    rw [denoteSpine_eq_denote' _ _ _ hsp]
    exact Prod.ext (hr fuel (Nat.le_refl fuel)) rfl
  have henv : σ.EnvOf sa (bindParams (ps a)) := hcanon ▸ σ.envOf_canonEnv hnd sa
  obtain ⟨x, hx, hback⟩ := haxRuns_pairStage ((haxRuns_single σ te sa _).mpr
    ⟨_, fuel, _, by rw [he]; exact henv, hrun, HaxEnc.Plain.not_cf (f a)⟩)
  obtain ⟨prog, sa', hd, hh, hR, -⟩ := haxEntry.compileR_correct
    (pairStage (te : CatCrypt.Crypto.Hax.HaxModule) σ).1 (pairStage te σ).2 fname P bytes
    ((linkedNil_compileARegion_eq (pairStage_linked _ σ) _ _).symm.trans hc) sa
    ((pairStage_regions _ σ sa).2 hsep) _ hx
  exact ⟨prog, sa', hd, hh, hback _ hR⟩

/-- **Compiled bytes compute the function of an ascent result, scalar layout.** The
    statement of `leanFront_correct` for a layout whose parameters are `u64` scalars and
    which binds no constant: the hypothesis on the canonical environment is that the
    parameter names with the integers of their registers are the bindings `ps a`. -/
theorem leanFront_correct_scalar {A β : Type} [HaxEnc β] [HaxEnc.Plain β] (te : TExpr)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA te σ fname = some (P, bytes)) (hsp : spineLamFree te.erase = true)
    (ps : A → List (String × Value)) (G : A → Prop) (f : A → β)
    (hf : FnCorres hax64WExit te.erase (fun a => bindParams (ps a)) G f)
    (hs : ∀ a ∈ σ.args, a.kind = .scalar) (hconsts : σ.consts = [])
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (a : A) (hG : G a)
    (hregs : σ.args.map (fun x => (x.name, Value.int (sa.regs x.reg).toNat)) = ps a)
    (hn : narrowOk te σ = false := by rfl) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (enc (f a)) :=
  leanFront_correct te σ fname P bytes hc hsp ps G f hf hnd sa hsep a hG
    (by rw [canonEnv_eq_bindParams σ hs hconsts sa, hregs]) hn

/-- **Compiled bytes compute the function on two word arrays.** The statement of
    `leanFront_correct` for a layout with two word-array parameters `xn` (`n₁` words at the
    address in `rx`) and `yn` (`n₂` words at the address in `ry`), no constant, and the
    result read back as the `N` words at the entry address in `%rdi`. The function `f` is
    taken on the argument tuple of `ascend_reified`, with the entry environment binding the
    two parameters to the encoded arrays. For all arrays `x`, `y` whose encodings are the
    words the two regions hold at the entry state, in the guard, the bytes decode to a
    program that halts in a state whose `N` result words are the encoding of `f (x, y, ())`. -/
theorem leanFront_correct_words {α β : Type} [HaxEnc α] [HaxEnc β] [HaxEnc.Plain β]
    (te : TExpr) (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA te σ fname = some (P, bytes)) (hsp : spineLamFree te.erase = true)
    (xn yn rx ry : String) (n₁ n₂ N : Nat)
    (hargs : σ.args = [⟨xn, rx, .words n₁⟩, ⟨yn, ry, .words n₂⟩]) (hconsts : σ.consts = [])
    (hres : σ.result = .words "%rdi" N)
    (G : Array α × (Array α × Unit) → Prop) (f : Array α × (Array α × Unit) → β)
    (hf : FnCorres hax64WExit te.erase
      (fun a => bindParams [(xn, enc a.1), (yn, enc a.2.1)]) G f)
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (x y : Array α)
    (hx : wordsAt sa.mem (sa.regs rx) n₁ = x.toList.map enc)
    (hy : wordsAt sa.mem (sa.regs ry) n₂ = y.toList.map enc) (hG : G (x, y, ()))
    (hn : narrowOk te σ = false := by rfl) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ enc (f (x, y, ())) = .array (wordsAt sa'.mem (sa.regs "%rdi") N) := by
  obtain ⟨prog, sa', hd, hh, hR⟩ := leanFront_correct te σ fname P bytes hc hsp
    (fun a => [(xn, enc a.1), (yn, enc a.2.1)]) G f hf hnd sa hsep (x, y, ()) hG (by
      rw [canonEnv_eq_bindParams_read σ hconsts sa, hargs]
      simp only [List.map_cons, List.map_nil, AbiArg.read, hx, hy]
      rfl) hn
  refine ⟨prog, sa', hd, hh, ?_⟩
  unfold AbiLayout.ResultOf at hR
  rw [hR, hres]
  rfl

/-! ## One field operation over a wide prime -/

section FieldOp

variable {p : ℕ}

/-- **The literal of a binary field operation corresponds to it**: `let t := g(x, y); t`, the
    literal `reifyField%` reads off `fun x y => x ∘ y` with `∘` at the tagged head `g`, returns
    the encoding of `op x y` from an entry environment that binds `x` and `y` to the encodings
    of the operands and an output buffer `out` to any array, when the table answers `g` on
    encoded elements by the encoding of `op`. -/
theorem fnCorres_fieldOp2 (g tn : String) (op : ZMod p → ZMod p → ZMod p)
    (hop : ∀ x y : ZMod p, hax64WExit g [enc x, enc y] = some (enc (op x y))) :
    FnCorres hax64WExit (.letBind tn (.app g [.var "x", .var "y"]) (.var tn))
      (A := ZMod p × ZMod p × List Value)
      (fun a => bindParams [("out", .array a.2.2), ("y", enc a.2.1), ("x", enc a.1)])
      (fun _ => True) (fun a => op a.1 a.2.1) := by
  intro a _
  refine ⟨0, fun fuel _ => ?_⟩
  set E := bindParams [("out", .array a.2.2), ("y", enc a.2.1), ("x", enc a.1)] with hE
  have hx : denote' hax64WExit fuel (.var "x") E = (.val (enc a.1), E) := by
    rw [_root_.Hax.denote'_var_run]; simp [hE, bindParams, Env.extend]
  have hy : denote' hax64WExit fuel (.var "y") E = (.val (enc a.2.1), E) := by
    rw [_root_.Hax.denote'_var_run]; simp [hE, bindParams, Env.extend]
  have hargs : _root_.Hax.denoteArgs' hax64WExit fuel [.var "x", .var "y"] E =
      (some [enc a.1, enc a.2.1], E) :=
    _root_.Hax.Total.denoteArgs'_cons_of_val hx (HaxEnc.Plain.not_cf _)
      (_root_.Hax.Total.denoteArgs'_cons_of_val hy (HaxEnc.Plain.not_cf _)
        (_root_.Hax.Total.denoteArgs'_nil_run _ _ _))
  rw [_root_.Hax.Total.denote'_letBind_of_val
    (_root_.Hax.Total.denote'_app_of_args hargs (hop a.1 a.2.1)) (HaxEnc.Plain.not_cf _),
    _root_.Hax.denote'_var_run]
  simp [Env.extend]

/-- **The literal of a field operation on one operand taken twice corresponds to it**:
    `let t := g(x, x); t`, the literal `reifyField%` reads off `fun x => x ∘ x`, returns the
    encoding of `op x x` from an entry environment that binds `x` to the encoding of the operand
    and an output buffer `out` to any array. -/
theorem fnCorres_fieldOp1 (g tn : String) (op : ZMod p → ZMod p → ZMod p)
    (hop : ∀ x y : ZMod p, hax64WExit g [enc x, enc y] = some (enc (op x y))) :
    FnCorres hax64WExit (.letBind tn (.app g [.var "x", .var "x"]) (.var tn))
      (A := ZMod p × List Value)
      (fun a => bindParams [("out", .array a.2), ("x", enc a.1)])
      (fun _ => True) (fun a => op a.1 a.1) := by
  intro a _
  refine ⟨0, fun fuel _ => ?_⟩
  set E := bindParams [("out", .array a.2), ("x", enc a.1)] with hE
  have hx : denote' hax64WExit fuel (.var "x") E = (.val (enc a.1), E) := by
    rw [_root_.Hax.denote'_var_run]; simp [hE, bindParams, Env.extend]
  have hargs : _root_.Hax.denoteArgs' hax64WExit fuel [.var "x", .var "x"] E =
      (some [enc a.1, enc a.1], E) :=
    _root_.Hax.Total.denoteArgs'_cons_of_val hx (HaxEnc.Plain.not_cf _)
      (_root_.Hax.Total.denoteArgs'_cons_of_val hx (HaxEnc.Plain.not_cf _)
        (_root_.Hax.Total.denoteArgs'_nil_run _ _ _))
  rw [_root_.Hax.Total.denote'_letBind_of_val
    (_root_.Hax.Total.denote'_app_of_args hargs (hop a.1 a.1)) (HaxEnc.Plain.not_cf _),
    _root_.Hax.denote'_var_run]
  simp [Env.extend]

/-- **Compiled bytes compute a function of two elements of a wide prime field.** Let `compileA`
    return `(P, bytes)` on the typed literal `te` under a layout `σ` whose parameters are an
    output buffer `out` at `%rdi` and the operands `y` and `x`, each an array of
    `fieldLimbs p` words, with the result the `fieldLimbs p` words at the entry `%rdi`, and let
    `te.erase` correspond to `f` (`FnCorres`, from an entry environment that binds the output
    buffer to any array). From every entry state `sa` satisfying `σ.Regions` whose operand
    regions hold the limbs of `x` and `y`, the bytes decode to a program that halts in a state
    whose result words are the limbs of `f x y`. -/
theorem leanFront_correct_field2 (hp : 2 ^ 64 ≤ p) (te : TExpr) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA te σ fname = some (P, bytes)) (hsp : spineLamFree te.erase = true)
    (ry rx : String)
    (hargs : σ.args = [⟨"out", "%rdi", .words (fieldLimbs p)⟩, ⟨"y", ry, .words (fieldLimbs p)⟩,
      ⟨"x", rx, .words (fieldLimbs p)⟩])
    (hconsts : σ.consts = []) (hres : σ.result = .words "%rdi" (fieldLimbs p))
    (f : ZMod p → ZMod p → ZMod p)
    (hf : FnCorres hax64WExit te.erase (A := ZMod p × ZMod p × List Value)
      (fun a => bindParams [("out", .array a.2.2), ("y", enc a.2.1), ("x", enc a.1)])
      (fun _ => True) (fun a => f a.1 a.2.1))
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (x y : ZMod p)
    (hx : wordsAt sa.mem (sa.regs rx) (fieldLimbs p) = limbsOf (fieldLimbs p) x.val)
    (hy : wordsAt sa.mem (sa.regs ry) (fieldLimbs p) = limbsOf (fieldLimbs p) y.val)
    (hn : narrowOk te σ = false := by rfl) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") (fieldLimbs p) = limbsOf (fieldLimbs p) (f x y).val := by
  obtain ⟨prog, sa', hd, hh, hR⟩ := leanFront_correct te σ fname P bytes hc hsp
    (fun a => [("out", .array a.2.2), ("y", enc a.2.1), ("x", enc a.1)]) (fun _ => True)
    (fun a => f a.1 a.2.1) hf hnd sa hsep (x, y, wordsAt sa.mem (sa.regs "%rdi") (fieldLimbs p))
    trivial (by
      rw [canonEnv_eq_bindParams_read σ hconsts sa, hargs]
      simp only [List.map_cons, List.map_nil, AbiArg.read, hx, hy, enc_zmod_wide hp]) hn
  refine ⟨prog, sa', hd, hh, ?_⟩
  have h : enc (f x y) = .array (wordsAt sa'.mem (sa.regs "%rdi") (fieldLimbs p)) := by
    unfold AbiLayout.ResultOf at hR
    rw [hR, hres]
    rfl
  rw [enc_zmod_wide hp] at h
  exact (Value.array.inj h).symm

/-- **Compiled bytes compute a function of one element of a wide prime field.** The statement
    of `leanFront_correct_field2` for a layout whose parameters are the output buffer `out` at
    `%rdi` and one operand `x`. -/
theorem leanFront_correct_field1 (hp : 2 ^ 64 ≤ p) (te : TExpr) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA te σ fname = some (P, bytes)) (hsp : spineLamFree te.erase = true)
    (rx : String)
    (hargs : σ.args = [⟨"out", "%rdi", .words (fieldLimbs p)⟩, ⟨"x", rx, .words (fieldLimbs p)⟩])
    (hconsts : σ.consts = []) (hres : σ.result = .words "%rdi" (fieldLimbs p))
    (f : ZMod p → ZMod p)
    (hf : FnCorres hax64WExit te.erase (A := ZMod p × List Value)
      (fun a => bindParams [("out", .array a.2), ("x", enc a.1)]) (fun _ => True)
      (fun a => f a.1))
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (x : ZMod p)
    (hx : wordsAt sa.mem (sa.regs rx) (fieldLimbs p) = limbsOf (fieldLimbs p) x.val)
    (hn : narrowOk te σ = false := by rfl) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") (fieldLimbs p) = limbsOf (fieldLimbs p) (f x).val := by
  obtain ⟨prog, sa', hd, hh, hR⟩ := leanFront_correct te σ fname P bytes hc hsp
    (fun a => [("out", .array a.2), ("x", enc a.1)]) (fun _ => True)
    (fun a => f a.1) hf hnd sa hsep (x, wordsAt sa.mem (sa.regs "%rdi") (fieldLimbs p))
    trivial (by
      rw [canonEnv_eq_bindParams_read σ hconsts sa, hargs]
      simp only [List.map_cons, List.map_nil, AbiArg.read, hx, enc_zmod_wide hp]) hn
  refine ⟨prog, sa', hd, hh, ?_⟩
  have h : enc (f x) = .array (wordsAt sa'.mem (sa.regs "%rdi") (fieldLimbs p)) := by
    unfold AbiLayout.ResultOf at hR
    rw [hR, hres]
    rfl
  rw [enc_zmod_wide hp] at h
  exact (Value.array.inj h).symm

end FieldOp

end CatCrypt.Crypto.SecureCompilation.Haxc
