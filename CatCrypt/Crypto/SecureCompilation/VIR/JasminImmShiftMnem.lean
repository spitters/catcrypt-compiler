/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

@[expose] public section

set_option autoImplicit false

/-!
# Decoding the count-in-mnemonic immediate shift

`opToLinstrR` exports an immediate shift `shrImm w k` / `shlImm w k` /
`sarImm w k` as the one-source instruction
`Lopn [.reg dst] (withWidthTag w ("SHR:" ++ toString k)) [src]`, carrying the
compile-time count in the mnemonic. This module decodes that mnemonic back into
its base and its count, and states the decoder's agreement with the exporter's
rendering for every count.

## Contents

* **§1** the decimal atoms: `natOfDigits?_toString` and `charsToNat?_toString`
  (the digit list of `toString k` evaluates to `k` under either reader),
  `toString_no_colon` (a decimal rendering carries no `:`) and
  `hasSuffix_countTag_eq_false` (a count-tagged mnemonic ends in `:64` only at
  count `64`), over Lean's `Nat.toDigits`.
* **§2** `immShiftMnem?`, the mnemonic decoder, and
  `immShiftMnem?_withWidthTag`, its agreement with `withWidthTag w (m ++ ":" ++
  toString k)`.
* **§3** the parse equations of the exporter's `parseImmShiftMnem` on the
  exported mnemonic: `parseImmShiftMnem_tag64`, `parseImmShiftMnem_untagged`
  and `parseImmShiftMnem_withWidthTag`.
* **§4** `immShiftWire?`, the instruction-level recogniser, and its agreement
  with `opToLinstrR` on the three immediate-shift ops.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. The decimal atoms -/

/-- One decimal-digit peel: for `n ≥ 10`, the digits of `n` are the digits of
    `n / 10` followed by the units digit. -/
theorem toDigits_rec (n : Nat) (hn : 10 ≤ n) :
    Nat.toDigits 10 n = Nat.toDigits 10 (n / 10) ++ [(n % 10).digitChar] := by
  have h1 : 0 < n / 10 := Nat.div_pos hn (by decide)
  have h2 : n % 10 < 10 := Nat.mod_lt _ (by decide)
  have hkey := Nat.toDigits_append_toDigits (b := 10) (n := n / 10) (d := n % 10)
    (by decide) h1 h2
  rw [Nat.toDigits_of_lt_base h2] at hkey
  rw [hkey]; congr 1; omega

/-- The decimal rendering of any `Nat` is non-empty. -/
theorem toDigits_ne_nil (k : Nat) : Nat.toDigits 10 k ≠ [] := by
  by_cases hk : k < 10
  · rw [Nat.toDigits_of_lt_base hk]; simp
  · rw [toDigits_rec k (by omega)]; simp

/-- The accumulator step of `natOfDigits?`. -/
def dstep : Option Nat → Char → Option Nat := fun acc c =>
  match acc with
  | some k => if '0' ≤ c && c ≤ '9' then some (k * 10 + (c.toNat - '0'.toNat)) else none
  | none => none

/-- On a non-empty character list, `natOfDigits?` is the fold of `dstep`. -/
theorem natOfDigits?_eq (cs : List Char) (h : cs ≠ []) :
    natOfDigits? cs = cs.foldl dstep (some 0) := by
  unfold natOfDigits?
  cases cs with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- A base-10 digit character passes the digit test and has the digit's value. -/
theorem digitChar_ok : ∀ d < 10, ('0' ≤ Nat.digitChar d && Nat.digitChar d ≤ '9') = true
    ∧ (Nat.digitChar d).toNat - '0'.toNat = d := by decide

/-- Folding `dstep` over the digits of `k` from an accumulator `a` scales `a` by
    the digit count and adds `k`. -/
theorem foldl_toDigits : ∀ (k a : Nat),
    (Nat.toDigits 10 k).foldl dstep (some a)
      = some (a * 10 ^ (Nat.toDigits 10 k).length + k) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a
    by_cases hk : k < 10
    · rw [Nat.toDigits_of_lt_base hk]
      obtain ⟨hd, hv⟩ := digitChar_ok k hk
      simp only [List.foldl_cons, List.foldl_nil, dstep, hd, if_true, hv,
        List.length_cons, List.length_nil]
    · rw [toDigits_rec k (by omega), List.foldl_append, ih (k / 10) (by omega) a]
      obtain ⟨hd, hv⟩ := digitChar_ok (k % 10) (Nat.mod_lt _ (by decide))
      simp only [List.foldl_cons, List.foldl_nil, dstep, hd, if_true,
        List.length_append, List.length_cons, List.length_nil, Nat.pow_succ]
      generalize (10 : Nat) ^ (Nat.toDigits 10 (k / 10)).length = P
      congr 1
      have hm : a * (P * 10) = a * P * 10 := (Nat.mul_assoc a P 10).symm
      omega

/-- **The decimal round-trip.** The character list of `toString k` evaluates to
    `k` under `natOfDigits?`. -/
theorem natOfDigits?_toString (k : Nat) : natOfDigits? (toString k).toList = some k := by
  show natOfDigits? (String.ofList (Nat.toDigits 10 k)).toList = some k
  rw [String.toList_ofList, natOfDigits?_eq _ (toDigits_ne_nil k), foldl_toDigits k 0]
  simp

/-- No base-10 digit character is the separator `:`. -/
theorem digitChar_ne_colon : ∀ d < 10, Nat.digitChar d ≠ ':' := by decide

/-- A decimal digit list carries no `:`. -/
theorem toDigits_no_colon (k : Nat) : ∀ c ∈ Nat.toDigits 10 k, c ≠ ':' := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k < 10
    · rw [Nat.toDigits_of_lt_base hk]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact digitChar_ne_colon k hk
    · rw [toDigits_rec k (by omega)]
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact ih (k / 10) (by omega) c h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        exact digitChar_ne_colon _ (Nat.mod_lt k (by decide))

/-- A decimal rendering carries no `:`, so it is one `splitCharsAt` group. -/
theorem toString_no_colon (k : Nat) : ∀ c ∈ (toString k).toList, c ≠ ':' := by
  show ∀ c ∈ (String.ofList (Nat.toDigits 10 k)).toList, c ≠ ':'
  rw [String.toList_ofList]
  exact toDigits_no_colon k

/-- A separator-free list is a single `splitChars` group. -/
theorem splitChars_no_sep (L : List Char) (h : ∀ c ∈ L, c ≠ ':') :
    splitChars ':' L = [L] := by
  induction L with
  | nil => rfl
  | cons a _ ih => rw [splitChars, if_neg (h a (by simp)), ih (fun c hc => h c (by simp [hc]))]

/-- A separator-free prefix followed by a separator is the first `splitChars`
    group. -/
theorem splitChars_cons_sep (L R : List Char) (h : ∀ c ∈ L, c ≠ ':') :
    splitChars ':' (L ++ ':' :: R) = L :: splitChars ':' R := by
  induction L with
  | nil => simp [splitChars]
  | cons a _ ih =>
      simp only [List.cons_append]
      rw [splitChars, if_neg (h a (by simp)), ih (fun c hc => h c (by simp [hc]))]

/-- A base-10 digit character passes `Char.isDigit`. -/
theorem digitChar_isDigit : ∀ d < 10, (Nat.digitChar d).isDigit = true := by
  decide +kernel

/-- Every character of a decimal digit list passes `Char.isDigit`. -/
theorem toDigits_isDigit (k : Nat) : ∀ c ∈ Nat.toDigits 10 k, c.isDigit = true := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k < 10
    · rw [Nat.toDigits_of_lt_base hk]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact digitChar_isDigit k hk
    · rw [toDigits_rec k (by omega)]
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact ih (k / 10) (by omega) c h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        exact digitChar_isDigit _ (Nat.mod_lt k (by decide))

/-- The `charsIsNat` scan over a digit list from a clean state ends in the
    digit state, and leaves an empty list's state alone. -/
theorem charsIsNatStep_digits (L : List Char) (hL : ∀ c ∈ L, c.isDigit = true) (b : Bool) :
    charsIsNatStep L (none, b) = if L = [] then (none, b) else (none, true) := by
  induction L generalizing b with
  | nil => rfl
  | cons c rest ih =>
    have hc := hL c (by simp)
    have hne : c ≠ '_' := by
      intro h; subst h; simp [Char.isDigit] at hc
    rw [charsIsNatStep, if_neg hne, if_pos hc, ih (fun c hc => hL c (by simp [hc]))]
    by_cases h : rest = [] <;> simp [h]

/-- A non-empty digit list passes `charsIsNat`. -/
theorem charsIsNat_digits (L : List Char) (hL : ∀ c ∈ L, c.isDigit = true) (hne : L ≠ []) :
    charsIsNat L = true := by
  unfold charsIsNat
  rw [charsIsNatStep_digits L hL false, if_neg hne]
  rfl

/-- The accumulator step of the `charsToNat?` fold. -/
def cstep : Nat → Char → Nat := fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)

/-- A digit character is not the `_` separator. -/
theorem digitChar_ne_underscore (d : Nat) (hd : d < 10) : Nat.digitChar d ≠ '_' := by
  intro h
  have := digitChar_isDigit d hd
  rw [h] at this
  simp [Char.isDigit] at this

/-- Folding `cstep` over the digits of `k` from an accumulator `a` scales `a` by
    the digit count and adds `k`. -/
theorem foldl_toDigits_cstep : ∀ (k a : Nat),
    (Nat.toDigits 10 k).foldl cstep a = a * 10 ^ (Nat.toDigits 10 k).length + k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a
    by_cases hk : k < 10
    · rw [Nat.toDigits_of_lt_base hk]
      obtain ⟨_, hv⟩ := digitChar_ok k hk
      simp only [List.foldl_cons, List.foldl_nil, cstep, if_neg (digitChar_ne_underscore k hk), hv,
        List.length_cons, List.length_nil]
    · rw [toDigits_rec k (by omega), List.foldl_append, ih (k / 10) (by omega) a]
      obtain ⟨_, hv⟩ := digitChar_ok (k % 10) (Nat.mod_lt _ (by decide))
      simp only [List.foldl_cons, List.foldl_nil, cstep,
        if_neg (digitChar_ne_underscore (k % 10) (Nat.mod_lt _ (by decide))), hv,
        List.length_append, List.length_cons, List.length_nil, Nat.pow_succ]
      generalize (10 : Nat) ^ (Nat.toDigits 10 (k / 10)).length = P
      have hm : a * (P * 10) = a * P * 10 := (Nat.mul_assoc a P 10).symm
      omega

/-- **The decimal round-trip for `charsToNat?`.** The character list of
    `toString k` evaluates to `k` under `charsToNat?`. -/
theorem charsToNat?_toString (k : Nat) : charsToNat? (toString k).toList = some k := by
  show charsToNat? (String.ofList (Nat.toDigits 10 k)).toList = some k
  rw [String.toList_ofList, charsToNat?,
    if_pos (charsIsNat_digits _ (toDigits_isDigit k) (toDigits_ne_nil k))]
  show some ((Nat.toDigits 10 k).foldl cstep 0) = some k
  rw [foldl_toDigits_cstep k 0]
  simp

/-- A string ends with any suffix it was appended with. -/
theorem hasSuffix_append (s pat : String) : hasSuffix (s ++ pat) pat = true := by
  unfold hasSuffix
  rw [String.toList_append, List.isSuffixOf_iff_suffix]
  exact List.suffix_append _ _

/-- `stripWidthTag` removes the appended `:64` width tag exactly. -/
theorem stripWidthTag_append64 (s : String) : stripWidthTag (s ++ ":64") = s := by
  unfold stripWidthTag
  rw [if_pos (hasSuffix_append s ":64"), String.toList_append,
    show (":64" : String).toList = [':', '6', '4'] from by decide]
  simp

/-! ## 2. The mnemonic decoder -/

/-- The base mnemonic and the compile-time count of a count-in-mnemonic
    immediate-shift mnemonic (`SHL:<k>`, `SHR:<k>`, `SAR:<k>`, with or without
    the `:64` width tag); `none` for any other mnemonic. -/
def immShiftMnem? (opn : String) : Option (String × Nat) :=
  let core := if hasSuffix opn ":64" then stripWidthTag opn else opn
  match splitChars ':' core.toList with
  | [mn, ds] =>
      let m := String.ofList mn
      if m == "SHL" || m == "SHR" || m == "SAR" then (natOfDigits? ds).map (fun k => (m, k))
      else none
  | _ => none

/-- The character list of a shift base, the separator and a decimal count. -/
theorem toList_mnem (m : String) (k : Nat) :
    (m ++ ":" ++ toString k).toList = m.toList ++ ':' :: (toString k).toList := by
  rw [String.toList_append, String.toList_append,
    show (":" : String).toList = [':'] from by decide]
  simp

/-- A shift base carries no separator. -/
theorem base_no_colon {m : String} (hm : m = "SHL" ∨ m = "SHR" ∨ m = "SAR") :
    ∀ c ∈ m.toList, c ≠ ':' := by
  rcases hm with rfl | rfl | rfl <;> decide

/-- **The decoder agrees with the width-64 rendering.** For a shift base `m` and
    any count `k`, `immShiftMnem?` recovers `(m, k)` from the exported
    mnemonic. -/
theorem immShiftMnem?_withWidthTag64 {m : String}
    (hm : m = "SHL" ∨ m = "SHR" ∨ m = "SAR") (k : Nat) :
    immShiftMnem? (withWidthTag 64 (m ++ ":" ++ toString k)) = some (m, k) := by
  have hw : withWidthTag 64 (m ++ ":" ++ toString k) = (m ++ ":" ++ toString k) ++ ":64" := rfl
  unfold immShiftMnem?
  rw [hw, if_pos (hasSuffix_append _ ":64"), stripWidthTag_append64]
  simp only [toList_mnem, splitChars_cons_sep _ _ (base_no_colon hm),
    splitChars_no_sep _ (toString_no_colon k), String.ofList_toList, natOfDigits?_toString]
  rcases hm with rfl | rfl | rfl <;> rfl

/-- **The decoder agrees with an untagged rendering.** At a width other than
    `64` the exported mnemonic carries no width tag, and the decoder recovers
    `(m, k)` whenever the rendering does not itself end in `:64`. -/
theorem immShiftMnem?_untagged {m : String}
    (hm : m = "SHL" ∨ m = "SHR" ∨ m = "SAR") (k : Nat)
    (hk : hasSuffix (m ++ ":" ++ toString k) ":64" = false) :
    immShiftMnem? (m ++ ":" ++ toString k) = some (m, k) := by
  unfold immShiftMnem?
  rw [if_neg (by rw [hk]; exact Bool.false_ne_true)]
  simp only [toList_mnem, splitChars_cons_sep _ _ (base_no_colon hm),
    splitChars_no_sep _ (toString_no_colon k), String.ofList_toList, natOfDigits?_toString]
  rcases hm with rfl | rfl | rfl <;> rfl

/-! ## 3. The parse equations of `parseImmShiftMnem`

`parseImmShiftMnem` is the parser `JasminLsem.applyOpn` runs on a one-source
mnemonic. On the exported mnemonic `m ++ ":" ++ toString n`, with or without the
`:64` width tag, it returns the AT&T direction `immShiftAtt m.toList` of the
base, the count `n` and the width, for every base without a `:` and every
count. -/

/-- A decimal rendering whose character list is `['6', '4']` renders `64`. -/
theorem toString_eq_64 {n : Nat} (h : (toString n).toList = ['6', '4']) : n = 64 := by
  have h1 := natOfDigits?_toString n
  rw [h] at h1
  have h2 : natOfDigits? ['6', '4'] = some 64 := by decide
  rw [h2] at h1
  exact (Option.some.inj h1).symm

/-- A count-tagged mnemonic ends in `:64` only when its count is `64`. -/
theorem hasSuffix_countTag_eq_false (m : String) {n : Nat} (hn : n ≠ 64) :
    hasSuffix (m ++ ":" ++ toString n) ":64" = false := by
  apply Bool.eq_false_iff.mpr
  intro hsuf
  unfold hasSuffix at hsuf
  rw [List.isSuffixOf_iff_suffix, toList_mnem,
    show (":64" : String).toList = [':', '6', '4'] from by decide] at hsuf
  obtain ⟨t, ht⟩ := hsuf
  have hrev := congrArg List.reverse ht
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.append_assoc] at hrev
  have hnc := toString_no_colon n
  apply hn
  apply toString_eq_64
  have hnil : (toString n).toList ≠ [] := by
    intro h
    have h1 := natOfDigits?_toString n
    rw [h] at h1
    cases h1
  rcases hds : (toString n).toList.reverse with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hds) hnil
  · rw [hds] at hrev
    simp at hrev
  · rw [hds] at hrev
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrev
    obtain ⟨rfl, rfl, _⟩ := hrev
    have := congrArg List.reverse hds
    simpa using this
  · rw [hds] at hrev
    simp only [List.cons_append, List.cons.injEq] at hrev
    obtain ⟨_, _, hc, _⟩ := hrev
    exfalso
    apply hnc c _ hc.symm
    have : c ∈ (toString n).toList.reverse := by rw [hds]; simp
    exact List.mem_reverse.mp this

/-- **The parser on the width-64 rendering.** For a base `m` without `:` and any
    count `n`, `parseImmShiftMnem` reads the direction of `m`, the count `n` and
    the width `64` off `m ++ ":" ++ toString n ++ ":64"`. -/
theorem parseImmShiftMnem_tag64 (m : String) (hm : ∀ c ∈ m.toList, c ≠ ':') (n : Nat) :
    parseImmShiftMnem ((m ++ ":" ++ toString n) ++ ":64")
      = (immShiftAtt m.toList).map (fun a => (a, n, 64)) := by
  unfold parseImmShiftMnem
  dsimp only
  simp only [hasSuffix_append, if_true, stripWidthTag_append64, toList_mnem,
    splitChars_cons_sep _ _ hm, splitChars_no_sep _ (toString_no_colon n), charsToNat?_toString]
  cases immShiftAtt m.toList <;> rfl

/-- **The parser on an untagged rendering.** For a base `m` without `:` and a
    count `n` whose rendering does not end in `:64`, `parseImmShiftMnem` reads
    the direction of `m`, the count `n` and the width `32` off
    `m ++ ":" ++ toString n`. -/
theorem parseImmShiftMnem_untagged (m : String) (hm : ∀ c ∈ m.toList, c ≠ ':') (n : Nat)
    (hk : hasSuffix (m ++ ":" ++ toString n) ":64" = false) :
    parseImmShiftMnem (m ++ ":" ++ toString n)
      = (immShiftAtt m.toList).map (fun a => (a, n, 32)) := by
  unfold parseImmShiftMnem
  dsimp only
  simp only [hk, Bool.false_eq_true, if_false, toList_mnem, splitChars_cons_sep _ _ hm,
    splitChars_no_sep _ (toString_no_colon n), charsToNat?_toString]
  cases immShiftAtt m.toList <;> rfl

/-- **The parser on the exported mnemonic.** At every width `w` and every count
    `n ≠ 64`, `parseImmShiftMnem` reads the direction of the base, the count
    and the op width (`64` iff `w = 64`) off `withWidthTag w (m ++ ":" ++
    toString n)`. -/
theorem parseImmShiftMnem_withWidthTag (m : String) (hm : ∀ c ∈ m.toList, c ≠ ':')
    (w : Nat) {n : Nat} (hn : n ≠ 64) :
    parseImmShiftMnem (withWidthTag w (m ++ ":" ++ toString n))
      = (immShiftAtt m.toList).map (fun a => (a, n, if w = 64 then 64 else 32)) := by
  unfold withWidthTag
  split
  · exact parseImmShiftMnem_tag64 m hm n
  · exact parseImmShiftMnem_untagged m hm n (hasSuffix_countTag_eq_false m hn)

/-! ## 4. The instruction-level recogniser -/

/-- Recognise a one-source count-in-mnemonic immediate shift
    `Lopn [.reg dst] opn [.reg src]` and return the destination, the source, the
    base mnemonic and the count; `none` for anything else. -/
def immShiftWire? (i : LinstrR) : Option (String × String × String × Nat) :=
  match i with
  | .Lopn [.reg dst] opn [.reg src] =>
      (immShiftMnem? opn).map (fun p => (dst, src, p.1, p.2))
  | _ => none

/-- The `SHR` export string, associated as the decoder reads it. -/
theorem shr_mnem (k : Nat) : ("SHR:" ++ toString k) = "SHR" ++ ":" ++ toString k := rfl

/-- The `SHL` export string, associated as the decoder reads it. -/
theorem shl_mnem (k : Nat) : ("SHL:" ++ toString k) = "SHL" ++ ":" ++ toString k := rfl

/-- The `SAR` export string, associated as the decoder reads it. -/
theorem sar_mnem (k : Nat) : ("SAR:" ++ toString k) = "SAR" ++ ":" ++ toString k := rfl

/-- **The recogniser reads back a width-64 `shrImm` export.** -/
theorem immShiftWire?_shrImm (k : Nat) (dst src : String) :
    immShiftWire? (opToLinstrR (JasminOp.shrImm 64 k) dst [.reg src])
      = some (dst, src, "SHR", k) := by
  simp only [opToLinstrR, immShiftWire?, shr_mnem,
    immShiftMnem?_withWidthTag64 (m := "SHR") (Or.inr (Or.inl rfl)) k, Option.map_some]

/-- **The recogniser reads back a width-64 `shlImm` export.** -/
theorem immShiftWire?_shlImm (k : Nat) (dst src : String) :
    immShiftWire? (opToLinstrR (JasminOp.shlImm 64 k) dst [.reg src])
      = some (dst, src, "SHL", k) := by
  simp only [opToLinstrR, immShiftWire?, shl_mnem,
    immShiftMnem?_withWidthTag64 (m := "SHL") (Or.inl rfl) k, Option.map_some]

/-- **The recogniser reads back a width-64 `sarImm` export.** -/
theorem immShiftWire?_sarImm (k : Nat) (dst src : String) :
    immShiftWire? (opToLinstrR (JasminOp.sarImm 64 k) dst [.reg src])
      = some (dst, src, "SAR", k) := by
  simp only [opToLinstrR, immShiftWire?, sar_mnem,
    immShiftMnem?_withWidthTag64 (m := "SAR") (Or.inr (Or.inr rfl)) k, Option.map_some]

/-- The recogniser declines an instruction that is not a one-source register
    `Lopn`. -/
theorem immShiftWire?_of_not_unary {i : LinstrR}
    (h : ∀ dst opn src, i ≠ .Lopn [.reg dst] opn [.reg src]) : immShiftWire? i = none := by
  unfold immShiftWire?
  split
  · next dst opn src => exact absurd rfl (h dst opn src)
  · rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem
