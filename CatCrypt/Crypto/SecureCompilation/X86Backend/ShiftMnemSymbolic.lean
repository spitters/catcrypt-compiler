/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended

/-!
# Symbolic-`n` immediate-shift `isSome`: routing prefix detection through `List Char`

`ComLegalityToGatherFull` / `ComLegalityShiftBridge` closed the immediate-shift
`isSome` bridge only for **concrete** shift counts: for a closed `n` the export
mnemonic `"SHR:" ++ toString n ++ ":64"` is a closed string, so the kernel
reduces the `Slice`/UTF-8-backed `String.startsWith "SHR:"` gate inside
`parseShiftMnem` and `decide +kernel` closes `(parseShiftMnem _).isSome`. For a
**symbolic** `n` that route fails: `String.startsWith` (Lean 4.29.1) is
`Slice`-pattern / byte-iterator-backed (`memcmpSlice` over UTF-8 offsets) and
will neither `decide` nor reduce by def-eq over `_ ++ toString n`.

The observation that unblocks the symbolic case: `(parseShiftMnem _).isSome` does
**not** need the decimal `toString n` / `toNat?` round-trip (that is computed
*inside* the `some (...)` and does not affect `isSome`); it needs only the
`startsWith "SHR:"` / `startsWith "SHL:"` **prefix detection** to fire. We route
that fact through the `List Char` / `String.Slice.copy` view — as `shiftCountOf`
already does for the count — by:

1. reconstructing the (non-`public`) stdlib characterisation
   `String.Slice.Pattern.ForwardSliceSearcher.startsWith pat s ↔
    ∃ t, s.copy = pat.copy ++ t` from the public memcmp / UTF-8-validity lemmas
   (`startsWith_iff'`), lifting it to the elementary String-level statement
   `s.startsWith q = true ↔ ∃ t, s = q ++ t` (`sw_iff`) and the corollaries
   `sw_append_self` / `sw_mono`; and
2. characterising `stripWidthTag` over the `:64` tag via `String.toList` /
   `List.dropLast` (`stripWidthTag_startsWith_of_startsWith`), avoiding the
   (template-less) backward-pattern `endsWith` characterisation by discharging
   *both* `if`-branches of `stripWidthTag` — each preserves the prefix.

These give `parseShiftMnem ("SHR:" ++ toString n ++ ":64") = some (false, _)`
(and the `SHL` analogue) for **every** `n`, hence the symbolic-`n`
`(lowerShiftImmJ _ _ _).isSome = true` and `(lowerLinstrExt2 _).isSome = true`
that the concrete-amount lemmas only gave pointwise.

No `decide` on a symbolic string, no `native_decide`, no axioms.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ShiftMnemSymbolic

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (stripWidthTag)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended

/-! ## 1. `String.startsWith` over append — the crux

Lean 4.29.1's `String.startsWith` reduces (`rfl`) to
`String.Slice.Pattern.ForwardSliceSearcher.startsWith q.toSlice s.toSlice`,
whose only characterisation lemma in the toolchain
(`…ForwardSliceSearcher.startsWith_iff`) is **not** exported (`module` system, no
`public` marker). We reconstruct it from the public memcmp / UTF-8-validity
lemmas it is built on, then lift it to the elementary String-level form. -/

open String String.Slice String.Slice.Pattern in
/-- Reconstruction of the stdlib (non-`public`) `ForwardSliceSearcher.startsWith`
    characterisation: a slice `s` starts with pattern `pat` iff `s.copy` is
    `pat.copy` followed by some suffix. Ported verbatim from
    `Init.Data.String.Lemmas.Pattern.String.ForwardPattern`'s private
    `startsWith_iff`, using only public memcmp / UTF-8 lemmas. -/
theorem startsWith_iff' {pat s : Slice} :
    ForwardSliceSearcher.startsWith pat s = true ↔ ∃ t, s.copy = pat.copy ++ t := by
  rw [ForwardSliceSearcher.startsWith]
  simp [Internal.memcmpSlice_eq_true_iff, utf8ByteSize_eq_size_toByteArray_copy,
    -String.size_toByteArray]
  generalize pat.copy = pat
  generalize s.copy = s
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · suffices pat.rawEndPos.IsValid s by
      have h₁ : (s.sliceTo (s.pos _ this)).copy = pat := by
        simpa [← String.toByteArray_inj, String.copy_toByteArray_sliceTo]
      have := (s.pos _ this).splits
      rw [h₁] at this
      refine ⟨_, this.eq_append⟩
    rw [String.Pos.Raw.isValid_iff_isValidUTF8_extract_zero]
    refine ⟨by simpa using h₁, ?_⟩
    simp only [String.size_toByteArray] at h₂
    simpa [h₂] using pat.isValidUTF8
  · rintro ⟨t, rfl⟩
    simp [-String.size_toByteArray, ByteArray.extract_append]

open String String.Slice.Pattern in
/-- The String-pattern `startsWith` is the slice forward-searcher `startsWith` on
    the two strings' slices. -/
theorem startsWith_eq_searcher (q s : String) :
    s.startsWith q = ForwardSliceSearcher.startsWith q.toSlice s.toSlice := rfl

open String in
/-- **String-level prefix characterisation.** `s.startsWith q = true` iff `s` is
    `q` followed by some suffix. The elementary `List Char`/`copy`-view form of
    the `Slice`-backed `String.startsWith` that the symbolic shift bridge needs
    (`String.startsWith` itself does not `decide`/reduce over a symbolic
    append). -/
theorem sw_iff (q s : String) : s.startsWith q = true ↔ ∃ t, s = q ++ t := by
  rw [startsWith_eq_searcher, startsWith_iff']
  simp only [String.copy_toSlice]

open String in
/-- A string starts with any of its own prefixes: `(p ++ t).startsWith p`. -/
theorem sw_append_self (p t : String) : (p ++ t).startsWith p = true := by
  rw [sw_iff]; exact ⟨t, rfl⟩

open String in
/-- `startsWith` is stable under appending on the right of the haystack. -/
theorem sw_mono (p r q : String) (h : p.startsWith q = true) :
    (p ++ r).startsWith q = true := by
  rw [sw_iff] at h ⊢
  obtain ⟨u, hu⟩ := h
  exact ⟨u ++ r, by rw [hu, String.append_assoc]⟩

/-! ## 2. `stripWidthTag` preserves the shift prefix over the `:64` tag

`stripWidthTag mnem` drops a `":64"` suffix (3 chars) via `endsWith ":64"` plus
three `dropLast`s. We do **not** reconstruct the (template-less) backward-pattern
`endsWith` characterisation; instead we discharge *both* `if`-branches of
`stripWidthTag`, each of which preserves the prefix when the un-tagged base
starts with the prefix:

* strip branch: `String.ofList ((p ++ ":64").toList.dropLast³) = p`
  (the `:64` chars are removed exactly), and `p` starts with the prefix;
* no-strip branch: the result is `p ++ ":64"`, which starts with the prefix by
  `sw_mono` since `p` does. -/

/-- Three `dropLast`s strip the `[':','6','4']` (`":64"`) tail off a char list. -/
private theorem dropLast3_append_64 (L : List Char) :
    (L ++ [':', '6', '4']).dropLast.dropLast.dropLast = L := by
  simp

/-- `stripWidthTag (p ++ ":64")` starts with `q` whenever `p` does — for either
    branch of `stripWidthTag`'s `endsWith` test. -/
theorem stripWidthTag_startsWith_of_startsWith (p q : String)
    (h : p.startsWith q = true) :
    (stripWidthTag (p ++ ":64")).startsWith q = true := by
  unfold stripWidthTag
  split
  · -- strip branch: the result is exactly `p`.
    have h64 : (":64" : String).toList = [':', '6', '4'] := by decide
    rw [String.toList_append, h64, dropLast3_append_64, String.ofList_toList]
    exact h
  · -- no-strip branch: the result is `p ++ ":64"`.
    exact sw_mono p ":64" q h

/-! ## 3. `parseShiftMnem` accepts the symbolic-`n` export string

`parseShiftMnem opn = let bare := stripWidthTag opn; if bare.startsWith "SHL:"
then some (true, _) else if bare.startsWith "SHR:" then some (false, _) else
none`. For `isSome` we need only that the relevant `startsWith` fires — whichever
of the two `if`-arms is taken, the result is `some`; only the trailing `none`
would break `isSome`, and the prefix fact rules it out. -/

/-- For symbolic `n`, the `SHR` export mnemonic parses (the `SHR:` arm fires,
    so `parseShiftMnem` is `some`). -/
theorem parseShiftMnem_isSome_shr (n : Nat) :
    (parseShiftMnem ("SHR:" ++ toString n ++ ":64")).isSome = true := by
  -- `bare := stripWidthTag` of the export `= ("SHR:" ++ toString n) ++ ":64"`
  -- (left-assoc `++`) starts with `"SHR:"`.
  have hSHR : (stripWidthTag ("SHR:" ++ toString n ++ ":64")).startsWith "SHR:" = true :=
    stripWidthTag_startsWith_of_startsWith _ _ (sw_append_self "SHR:" (toString n))
  unfold parseShiftMnem
  -- whichever `if`-arm fires, the result is `some`.
  by_cases hSHL : (stripWidthTag ("SHR:" ++ toString n ++ ":64")).startsWith "SHL:" = true
  · simp only [hSHL, if_true, Option.isSome_some]
  · simp only [Bool.not_eq_true] at hSHL
    simp only [hSHL, hSHR, Bool.false_eq_true, if_false, if_true, Option.isSome_some]

/-- For symbolic `n`, the `SHL` export mnemonic parses. -/
theorem parseShiftMnem_isSome_shl (n : Nat) :
    (parseShiftMnem ("SHL:" ++ toString n ++ ":64")).isSome = true := by
  have hSHL : (stripWidthTag ("SHL:" ++ toString n ++ ":64")).startsWith "SHL:" = true :=
    stripWidthTag_startsWith_of_startsWith _ _ (sw_append_self "SHL:" (toString n))
  unfold parseShiftMnem
  simp only [hSHL, if_true, Option.isSome_some]

/-! ## 4. Symbolic-`n` `lowerShiftImmJ` / `lowerLinstrExt2` `isSome`

With `parseShiftMnem` accepting the export string for every `n`, both the
shift-lowering helper and the full single-instruction lowering succeed for
symbolic shift counts — the symbolic-`n` upgrade of the prior step's
concrete-only lemmas. -/

/-- `lowerShiftImmJ` succeeds on the symbolic-`n` `SHR` export mnemonic. -/
theorem lowerShiftImmJ_isSome_shr (n : Nat) (dst : String) (src : Jasmin.JOperand) :
    (lowerShiftImmJ dst ("SHR:" ++ toString n ++ ":64") src).isSome = true := by
  unfold lowerShiftImmJ
  rw [Option.isSome_map]
  exact parseShiftMnem_isSome_shr n

/-- `lowerShiftImmJ` succeeds on the symbolic-`n` `SHL` export mnemonic. -/
theorem lowerShiftImmJ_isSome_shl (n : Nat) (dst : String) (src : Jasmin.JOperand) :
    (lowerShiftImmJ dst ("SHL:" ++ toString n ++ ":64") src).isSome = true := by
  unfold lowerShiftImmJ
  rw [Option.isSome_map]
  exact parseShiftMnem_isSome_shl n

/-! ## 5. The shift export mnemonics are not the `"LOAD"` prior arm

The shift-bridge core (`ComLegalityShiftBridge.lowerLinstrExt2_isSome_shift_mnem`)
rules out the matcher's `"LOAD"` arm via `m ≠ "LOAD"`. For symbolic `n` this is
not a closed-string `decide`; it follows because the export starts with the
shift prefix while `"LOAD"` does not (a `decide +kernel` on the *closed*
`"LOAD".startsWith "SHR:"`). -/

/-- The symbolic-`n` `SHR` export mnemonic is never `"LOAD"`. -/
theorem shr_export_ne_LOAD (n : Nat) :
    ("SHR:" ++ toString n ++ ":64") ≠ "LOAD" := by
  intro h
  have hp := sw_append_self "SHR:" (toString n ++ ":64")
  rw [show ("SHR:" ++ (toString n ++ ":64")) = ("SHR:" ++ toString n ++ ":64") from rfl, h] at hp
  exact absurd hp (by decide +kernel)

/-- The symbolic-`n` `SHL` export mnemonic is never `"LOAD"`. -/
theorem shl_export_ne_LOAD (n : Nat) :
    ("SHL:" ++ toString n ++ ":64") ≠ "LOAD" := by
  intro h
  have hp := sw_append_self "SHL:" (toString n ++ ":64")
  rw [show ("SHL:" ++ (toString n ++ ":64")) = ("SHL:" ++ toString n ++ ":64") from rfl, h] at hp
  exact absurd hp (by decide +kernel)

end CatCrypt.Crypto.SecureCompilation.X86Backend.ShiftMnemSymbolic
