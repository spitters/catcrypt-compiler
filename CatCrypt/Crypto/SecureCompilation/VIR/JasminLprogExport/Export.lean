/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.SarCount
public import CatCrypt.Crypto.SecureCompilation.VIR.SarCount
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Std.Data.HashMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Types
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Types

/-!
# Straight-line export of a `Com jasminDialect` to `Linear.lprog`

The lowering of a `JasminOp` to a linear instruction, the walk over a `Com`
term that assigns stable register names, the export to a one-function `Lprog`,
and the textual serialization read by the OCaml side.

## Main definitions

* `comToBody`: the linear body of a `Com` term.
* `Com.toLprog`, `Com.toLprogWithRodata`: the export to `Lprog`.
* `Lprog.toText`, `Com.toLprogText`, `Com.toLprogBytes`: the textual IR.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 2. Lowering a `JasminOp` to a `linstr_r`

Each `Com` binding is a `JasminOp` applied to de-Bruijn argument vars. We name
the binding result `r{depth}` (the SSA index from the let-nesting depth) and the
argument vars by the depth at which they were bound. This collapses the typed
De Bruijn structure to flat register names, which is what the linear IR uses. -/

/-- The register name for the SSA binding at let-depth `d` (counting from the
    program root). -/
def regName (d : Nat) : String := "r" ++ toString d

/-- Map a `JasminBinOp` to a textual jasmin opcode base name (no width). -/
def binOpName : JasminBinOp → String
  | .add => "ADD"
  | .sub => "SUB"
  | .mul => "MUL"
  | .and => "AND"
  | .or  => "OR"
  | .xor => "XOR"
  | .shl => "SHL"
  | .shr => "SHR"
  -- BMI1 `andn` (`d := (~a) & b`). The owned-x86 printer matches
  -- `stripWidthTag opn == "ANDN"` (so `withWidthTag 64 "ANDN" = "ANDN:64"`
  -- round-trips) and renders the non-destructive 3-operand `andn b, a, d`.
  | .andn => "ANDN"

/-- Map a `JasminCmp` condition code to the base mnemonic of its materialised
    comparison `Lopn [d] SET<cc> [a, b]` (`d := a <cc> b ? 1 : 0`); the suffix is
    the x86 condition-code name. -/
def cmpName : JasminCmp → String
  | .eq => "SETE"
  | .ne => "SETNE"
  | .ult => "SETB"
  | .ule => "SETBE"
  | .ugt => "SETA"
  | .uge => "SETAE"

/-- Append the width tag of an op of width `w` to a body mnemonic: `":64"` at
    width `64` and `"^" ++ toString w` at every other width. `read_linear`
    materialises a `:64`-tagged op at U64 and every other op at its
    `default_ws = U32`. The `^` separator occurs in no other mnemonic grammar,
    external-call names included (they use `@`, as in `slice@256`), so a tag at a width other than `64` cannot be
    read as a shift count (`SHR:16`), a vector count (`VPSLLD:8`) or an ABI
    narrow move (`MOV:16`, `MOV:8`). -/
def withWidthTag (w : Nat) (mnem : String) : String :=
  if w = 64 then mnem ++ ":64" else mnem ++ "^" ++ toString w

/-- Suffix test over the character list. The tag recognizers below are computed
    through by `decide` in the fidelity proofs, and `String.endsWith` does not
    reduce inside a module, so they are stated over `List.isSuffixOf`. -/
def hasSuffix (s pat : String) : Bool := List.isSuffixOf pat.toList s.toList

/-- Prefix test over the character list, for the same reason as `hasSuffix`. -/
def hasPrefix (s pat : String) : Bool := List.isPrefixOf pat.toList s.toList

/-- Drop the first `k` characters of a string, over the character list. `String.drop`
    iterates over `String.Pos` and does not reduce inside a module; the operand-name
    parsers are computed through by `decide`. -/
def strDrop (s : String) (k : Nat) : String := String.ofList (s.toList.drop k)

/-- Split a character list at every occurrence of `sep`, keeping the empty groups:
    a list with `n` occurrences of `sep` yields `n + 1` groups and the separators
    are dropped. -/
def splitChars (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
      if c = sep then [] :: splitChars sep rest
      else match splitChars sep rest with
        | [] => [[c]]
        | g :: gs => (c :: g) :: gs

/-- Split a string at every occurrence of one separator character, over the
    character list. -/
def splitOnChar (sep : Char) (s : String) : List String :=
  (splitChars sep s.toList).map String.ofList

/-- Read a decimal digit list. `String.toNat?` does not reduce inside a module,
    and the operand-name parsers are computed through by `decide`. -/
def natOfDigits? (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | _ => cs.foldl (fun acc c =>
      match acc with
      | some k => if '0' ≤ c && c ≤ '9' then some (k * 10 + (c.toNat - '0'.toNat)) else none
      | none => none) (some 0)

/-- The scan state of `String.Slice.isNat` after a character list: the first
    component is the early `false` answer once a character rejects the string,
    the second records whether the previous character was a digit. -/
def charsIsNatStep : List Char → (Option Bool × Bool) → (Option Bool × Bool)
  | [], st => st
  | c :: rest, st =>
      if c = '_' then
        (if (!st.2) = true then (some false, st.2)
         else charsIsNatStep rest ((none : Option Bool), false))
      else if c.isDigit = true then charsIsNatStep rest ((none : Option Bool), true)
      else (some false, st.2)

/-- `String.Slice.isNat` on a character list. -/
def charsIsNat (l : List Char) : Bool :=
  let st := charsIsNatStep l ((none : Option Bool), false)
  st.1.getD st.2

/-- `String.Slice.toNat?` on a character list: the decimal value with `_`
    separators ignored when `charsIsNat` accepts the list, and `none`
    otherwise. -/
def charsToNat? (cs : List Char) : Option Nat :=
  if charsIsNat cs then
    some (cs.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

/-- `(s.drop k).toNat?`, the decimal suffix of a name after its `k`-character
    prefix. `String.Slice.isNat` and `String.Slice.foldl` iterate over
    `String.Pos` and have no normal form in the kernel; this parse recurses on
    `List Char` and reduces. -/
def strDropToNat? (s : String) (k : Nat) : Option Nat := charsToNat? (s.toList.drop k)

/-- `String.toNat?` over the character list, so that a closed application
    reduces in the kernel. -/
def strToNat? (s : String) : Option Nat := charsToNat? s.toList

/-- Strip the width tag from a body mnemonic, recovering the base opcode for the
    `isBinop` / `isShift` recognizers: everything from the first `^` on when the
    mnemonic contains an `^`, otherwise a trailing `":64"`. -/
def stripWidthTag (mnem : String) : String :=
  if mnem.toList.contains '^' then
    String.ofList (mnem.toList.takeWhile (· != '^'))
  else if hasSuffix mnem ":64" then
    String.ofList (mnem.toList.dropLast.dropLast.dropLast)
  else mnem

/-- The AT&T direction of an immediate shift or rotate base (`ROR`, `ROL`, `SHL`,
    `SHR`, `SAR`), read from the base's character list; `none` for any other
    list. -/
def immShiftAtt : List Char → Option String
  | ['R', 'O', 'R'] => some "ror"
  | ['R', 'O', 'L'] => some "rol"
  | ['S', 'H', 'L'] => some "shl"
  | ['S', 'H', 'R'] => some "shr"
  | ['S', 'A', 'R'] => some "sar"
  | _ => none

/-- The AT&T direction, the count and the width `w` of an immediate shift whose
    base is the character list `mn` and whose decimal count is `ds`; `none` when
    `mn` is not a shift base or `ds` is not a decimal. -/
def immShiftParts (mn ds : List Char) (w : Nat) : Option (String × Nat × Nat) :=
  match immShiftAtt mn, charsToNat? ds with
  | some a, some n => some (a, n, w)
  | _, _ => none

/-- Parse a count-tagged immediate shift/rotate mnemonic (`SHL:0`, `SHR:32`,
    `SAR:k`, `ROL:k`, `ROR:k`) into the AT&T direction, the compile-time count,
    and the op width. Three forms are read: the untagged two-part `B:k` at width
    `32`, the three-part `B:k:64` at width `64`, and `B:k^w` at width `w`. `none`
    for any other mnemonic.

    The count separator is `:`, the character of the ABI narrow-move tags
    `:8`/`:16` and of the `:64` width tag, so the count is read from the raw
    `opn` by splitting it into its `:`-separated parts, never from a
    `stripWidthTag`-ed base.

    The split (`splitChars`) and the count read (`charsToNat?`) run over the
    character list, so a closed application reduces in the kernel;
    `String.splitOn` has no normal form there. -/
def parseImmShiftMnem (opn : String) : Option (String × Nat × Nat) :=
  let l := opn.toList
  if l.contains '^' then
    match charsToNat? (l.dropWhile (· != '^')).tail with
    | some w =>
        match splitChars ':' (l.takeWhile (· != '^')) with
        | [mn, ds] => immShiftParts mn ds w
        | _ => none
    | none => none
  else
    match splitChars ':' l with
    | [mn, ds] => immShiftParts mn ds 32
    | [mn, ds, ['6', '4']] => immShiftParts mn ds 64
    | _ => none

/-- The width a body mnemonic's tag carries: the decimal after the first `^`, or
    `64` for a mnemonic without `^` ending in `":64"`; `none` for an untagged
    mnemonic. -/
def wireWidth? (mnem : String) : Option Nat :=
  let l := mnem.toList
  if l.contains '^' then charsToNat? (l.dropWhile (· != '^')).tail
  else if hasSuffix mnem ":64" then some 64 else none

/-- A body mnemonic carries neither of the width-tag separators `:` and `^`. -/
def tagSepFree (s : String) : Bool := !(s.toList.contains ':') && !(s.toList.contains '^')

/-! ### The width-tag grammar

The lemmas of this section read a tagged mnemonic through its separator only. The
decimal rendering of a width enters through the two facts `toString_toList_isDigit`
and `charsToNat?_toString_toList`. -/

/-- The character list of the decimal rendering of a `Nat`. -/
theorem toString_toList_eq (k : Nat) : (toString k).toList = Nat.toDigits 10 k := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]

/-- Every character of the decimal rendering of a `Nat` is a digit. -/
theorem toString_toList_isDigit (k : Nat) : ∀ c ∈ (toString k).toList, c.isDigit = true := by
  rw [toString_toList_eq]
  intro c hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

/-- The `charsIsNat` scan over a digit list from a clean state ends in the digit
    state, and leaves an empty list's state alone. -/
theorem charsIsNatStep_of_isDigit (L : List Char) (hL : ∀ c ∈ L, c.isDigit = true)
    (b : Bool) : charsIsNatStep L (none, b) = if L = [] then (none, b) else (none, true) := by
  induction L generalizing b with
  | nil => rfl
  | cons c rest ih =>
    have hc := hL c (by simp)
    have hne : c ≠ '_' := by
      intro h; subst h; simp [Char.isDigit] at hc
    rw [charsIsNatStep, ite_eq_right hne, ite_eq_left hc, ih (fun c hc => hL c (by simp [hc]))]
    by_cases h : rest = [] <;> simp [h]

/-- The `charsToNat?` fold over the decimal digits of `k` from an accumulator `a`
    scales `a` by the digit count and adds `k`. -/
theorem foldl_toDigits_ten : ∀ (k a : Nat),
    (Nat.toDigits 10 k).foldl
        (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) a
      = a * 10 ^ (Nat.toDigits 10 k).length + k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a
    by_cases hk : k < 10
    · grind only [Nat.toDigits_eq_if, List.foldl_cons, = List.length_cons,
        Nat.toNat_digitChar_sub_48_of_lt_ten, List.foldl_nil, = List.length_nil]
    · rw [Nat.toDigits_of_base_le (by decide) (by omega), List.foldl_append, ih (k / 10) (by omega) a]
      have hlt : k % 10 < 10 := Nat.mod_lt _ (by decide)
      have hd : (k % 10).digitChar ≠ '_' := by
        intro h
        have := Nat.isDigit_digitChar (n := k % 10)
        rw [h] at this
        simp [hlt] at this
      simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons,
        List.length_nil, Nat.pow_succ]
      rw [ite_eq_right hd, show '0'.toNat = 48 from rfl, Nat.toNat_digitChar_sub_48_of_lt_ten hlt]
      generalize (10 : Nat) ^ (Nat.toDigits 10 (k / 10)).length = P
      have hm : a * (P * 10) = a * P * 10 := (Nat.mul_assoc a P 10).symm
      omega

/-- The decimal rendering of a `Nat` evaluates back to it under `charsToNat?`. -/
theorem charsToNat?_toString_toList (k : Nat) : charsToNat? (toString k).toList = some k := by
  have hd := toString_toList_isDigit k
  rw [toString_toList_eq] at hd ⊢
  unfold charsToNat? charsIsNat
  rw [charsIsNatStep_of_isDigit _ hd, ite_eq_right Nat.toDigits_ne_nil]
  grind only [Option.getD_none, foldl_toDigits_ten]

/-- A digit is neither width-tag separator. -/
theorem sep_not_mem_toString (k : Nat) :
    ':' ∉ (toString k).toList ∧ '^' ∉ (toString k).toList := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := toString_toList_isDigit k _ h
    revert this; decide
  · have := toString_toList_isDigit k _ h
    revert this; decide

/-- The width-tag separators of a separator-free mnemonic. -/
theorem tagSepFree_iff (s : String) :
    tagSepFree s = true ↔ ':' ∉ s.toList ∧ '^' ∉ s.toList := by
  simp [tagSepFree]

/-- A character list without `sep` is one `splitChars` group. -/
theorem splitChars_of_not_mem (sep : Char) (L : List Char) (h : sep ∉ L) :
    splitChars sep L = [L] := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    have ha : a ≠ sep := fun e => h (e ▸ List.mem_cons_self)
    rw [splitChars, ite_eq_right ha, ih (fun ht => h (List.mem_cons_of_mem _ ht))]

/-- A prefix without `sep` followed by `sep` is the first `splitChars` group. -/
theorem splitChars_append_cons (sep : Char) (L R : List Char) (h : sep ∉ L) :
    splitChars sep (L ++ sep :: R) = L :: splitChars sep R := by
  induction L with
  | nil => simp [splitChars]
  | cons a t ih =>
    have ha : a ≠ sep := fun e => h (e ▸ List.mem_cons_self)
    simp only [List.cons_append]
    rw [splitChars, ite_eq_right ha, ih (fun ht => h (List.mem_cons_of_mem _ ht))]

/-- The character list of a width-64 tagged mnemonic. -/
theorem toList_withWidthTag_64 (m : String) :
    (withWidthTag 64 m).toList = m.toList ++ [':', '6', '4'] := by
  grind only [withWidthTag.eq_def, String.toList_append]

/-- The character list of a mnemonic tagged at a width other than `64`. -/
theorem toList_withWidthTag_of_ne {w : Nat} (hw : w ≠ 64) (m : String) :
    (withWidthTag w m).toList = m.toList ++ '^' :: (toString w).toList := by
  grind only [withWidthTag.eq_def, String.toList_append, usr List.append_assoc, = List.cons_append]

/-- A tagged mnemonic contains a width-tag separator. -/
theorem tagSepFree_withWidthTag (w : Nat) (m : String) :
    tagSepFree (withWidthTag w m) = false := by
  by_cases hw : w = 64
  · subst hw
    simp [tagSepFree, toList_withWidthTag_64]
  · simp [tagSepFree, toList_withWidthTag_of_ne hw]

/-- A tagged mnemonic differs from every mnemonic without a width-tag separator. -/
theorem withWidthTag_ne_of_tagSepFree (w : Nat) (m : String) {s : String}
    (hs : tagSepFree s = true) : withWidthTag w m ≠ s := by
  grind only [tagSepFree_withWidthTag]

/-- `width_tag_ne` closes `withWidthTag w m ≠ s` and `s ≠ withWidthTag w m` for a
    literal `s` without a width-tag separator. -/
macro "width_tag_ne" : tactic =>
  `(tactic| first
    | exact withWidthTag_ne_of_tagSepFree _ _ (by decide +kernel)
    | exact (withWidthTag_ne_of_tagSepFree _ _ (by decide +kernel)).symm)

/-- A width-64 tagged mnemonic ends in `":64"`. -/
theorem hasSuffix_withWidthTag_64 (m : String) : hasSuffix (withWidthTag 64 m) ":64" = true := by
  unfold hasSuffix
  rw [toList_withWidthTag_64, show (":64" : String).toList = [':', '6', '4'] from by decide,
    List.isSuffixOf_iff_suffix]
  exact List.suffix_append _ _

/-- Every character of a list without `^` passes the test `· != '^'`. -/
theorem bne_at_of_not_mem {L : List Char} (h : '^' ∉ L) : ∀ c ∈ L, (c != '^') = true := by
  intro c hc
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  exact h hc

/-- **The strip inverts the tag.** For a mnemonic without a width-tag separator,
    `stripWidthTag` removes the tag of every width. -/
theorem stripWidthTag_withWidthTag (w : Nat) {m : String} (hm : tagSepFree m = true) :
    stripWidthTag (withWidthTag w m) = m := by
  have hat := ((tagSepFree_iff m).mp hm).2
  by_cases hw : w = 64
  · subst hw
    unfold stripWidthTag
    rw [ite_eq_right (by rw [toList_withWidthTag_64]; simp [hat]), ite_eq_left (hasSuffix_withWidthTag_64 m),
      toList_withWidthTag_64]
    simp
  · unfold stripWidthTag
    rw [ite_eq_left (by rw [toList_withWidthTag_of_ne hw]; simp), toList_withWidthTag_of_ne hw,
      List.takeWhile_append_of_pos (bne_at_of_not_mem hat)]
    simp

/-- **The tag carries its width.** -/
theorem wireWidth?_withWidthTag (w : Nat) {m : String} (hm : tagSepFree m = true) :
    wireWidth? (withWidthTag w m) = some w := by
  have hat := ((tagSepFree_iff m).mp hm).2
  by_cases hw : w = 64
  · subst hw
    unfold wireWidth?
    dsimp only
    rw [ite_eq_right (by rw [toList_withWidthTag_64]; simp [hat]), ite_eq_left (hasSuffix_withWidthTag_64 m)]
  · unfold wireWidth?
    dsimp only
    rw [toList_withWidthTag_of_ne hw, ite_eq_left (by simp),
      List.dropWhile_append_of_pos (bne_at_of_not_mem hat)]
    simpa [toString_toList_eq] using charsToNat?_toString_toList w

/-- `immShiftParts` on a decimal rendering. -/
theorem immShiftParts_toString (mn : List Char) (n w : Nat) :
    immShiftParts mn (toString n).toList w = (immShiftAtt mn).map (fun a => (a, n, w)) := by
  unfold immShiftParts
  rw [charsToNat?_toString_toList]
  cases immShiftAtt mn <;> rfl

/-- **The shift parser on a tagged mnemonic.** For a base `m` without a width-tag
    separator, every count `n` and every width `w`, `parseImmShiftMnem` reads the
    direction of `m`, the count `n` and the width `w` off
    `withWidthTag w (m ++ ":" ++ toString n)`. -/
theorem parseImmShiftMnem_withWidthTag {m : String} (hm : tagSepFree m = true)
    (w n : Nat) :
    parseImmShiftMnem (withWidthTag w (m ++ ":" ++ toString n))
      = (immShiftAtt m.toList).map (fun a => (a, n, w)) := by
  obtain ⟨hcm, hat⟩ := (tagSepFree_iff m).mp hm
  obtain ⟨hcs, has⟩ := sep_not_mem_toString n
  have has' : '^' ∉ Nat.toDigits 10 n := by rwa [toString_toList_eq] at has
  have hB : (m ++ ":" ++ toString n).toList = m.toList ++ ':' :: (toString n).toList := by
    simp
  have hatB : '^' ∉ m.toList ++ ':' :: (toString n).toList := by simp [hat, has']
  by_cases hw : w = 64
  · subst hw
    unfold parseImmShiftMnem
    dsimp only
    rw [toList_withWidthTag_64, hB, ite_eq_right (by simp [hat, has'])]
    simp only [List.append_assoc, List.cons_append]
    rw [splitChars_append_cons _ _ _ hcm, splitChars_append_cons _ _ _ hcs,
      splitChars_of_not_mem _ _ (by decide)]
    exact immShiftParts_toString _ _ _
  · unfold parseImmShiftMnem
    dsimp only
    rw [toList_withWidthTag_of_ne hw, hB, ite_eq_left (by simp),
      List.dropWhile_append_of_pos (bne_at_of_not_mem hatB),
      List.takeWhile_append_of_pos (bne_at_of_not_mem hatB)]
    simp only [List.dropWhile_cons, List.takeWhile_cons, bne_self_eq_false, Bool.false_eq_true,
      ite_false, List.tail_cons, List.append_nil, charsToNat?_toString_toList]
    rw [splitChars_append_cons _ _ _ hcm, splitChars_of_not_mem _ _ hcs]
    exact immShiftParts_toString _ _ _

/-- The shift parser on an untagged mnemonic reads the width `32`. -/
theorem parseImmShiftMnem_untagged {m : String} (hm : tagSepFree m = true) (n : Nat) :
    parseImmShiftMnem (m ++ ":" ++ toString n)
      = (immShiftAtt m.toList).map (fun a => (a, n, 32)) := by
  obtain ⟨hcm, hat⟩ := (tagSepFree_iff m).mp hm
  obtain ⟨hcs, has⟩ := sep_not_mem_toString n
  have has' : '^' ∉ Nat.toDigits 10 n := by rwa [toString_toList_eq] at has
  have hB : (m ++ ":" ++ toString n).toList = m.toList ++ ':' :: (toString n).toList := by
    simp
  unfold parseImmShiftMnem
  dsimp only
  rw [hB, ite_eq_right (by simp [hat, has']), splitChars_append_cons _ _ _ hcm,
    splitChars_of_not_mem _ _ hcs]
  exact immShiftParts_toString _ _ _

/-- The body is a prefix of its tagged mnemonic. -/
theorem toList_prefix_withWidthTag (w : Nat) (m : String) :
    m.toList <+: (withWidthTag w m).toList := by
  by_cases hw : w = 64
  · subst hw
    rw [toList_withWidthTag_64]
    exact List.prefix_append _ _
  · rw [toList_withWidthTag_of_ne hw]
    exact List.prefix_append _ _

/-- **Prefix tests on a tagged mnemonic.** For a body `m` and a word `q` without a
    width-tag separator and `m ≠ q`, the tagged mnemonic does not start with
    `q ++ ":"` (the shape of the `"CALL:"` test). -/
theorem hasPrefix_withWidthTag_colon_eq_false (w : Nat) {m q : String}
    (hm : tagSepFree m = true) (hq : tagSepFree q = true) (hne : m ≠ q) :
    hasPrefix (withWidthTag w m) (q ++ ":") = false := by
  obtain ⟨hcm, hat⟩ := (tagSepFree_iff m).mp hm
  obtain ⟨hcq, haq⟩ := (tagSepFree_iff q).mp hq
  have hne' : m.toList ≠ q.toList := fun h => hne (String.toList_inj.mp h)
  unfold hasPrefix
  rw [Bool.eq_false_iff]
  intro hp
  rw [List.isPrefixOf_iff_prefix, String.toList_append,
    show (":" : String).toList = [':'] from by decide] at hp
  obtain ⟨u, hu⟩ := hp
  have key : ∀ T : List Char, (T.head? = some ':' ∨ T.head? = some '^') →
      q.toList ++ ':' :: u ≠ m.toList ++ T := by
    intro T hT he
    rcases List.append_eq_append_iff.mp he with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · cases a' with
      | nil => exact hne' (by simpa using h1)
      | cons x xs =>
        simp only [List.cons_append, List.cons.injEq] at h2
        exact hcm (by rw [h1, ← h2.1]; simp)
    · cases c' with
      | nil => exact hne' (by simpa using h1.symm)
      | cons x xs =>
        simp only [List.cons_append] at h2
        rw [h2] at hT
        simp only [List.head?_cons, Option.some.injEq] at hT
        rcases hT with rfl | rfl
        · exact hcq (by rw [h1]; simp)
        · exact haq (by rw [h1]; simp)
  by_cases hw : w = 64
  · subst hw
    rw [toList_withWidthTag_64] at hu
    exact key [':', '6', '4'] (Or.inl rfl) (by simpa using hu)
  · rw [toList_withWidthTag_of_ne hw] at hu
    exact key ('^' :: (toString w).toList) (Or.inr rfl) (by simpa using hu)

/-- **Prefixes survive the strip.** A prefix without `^` followed by at least
    three more characters is a prefix of the stripped mnemonic. -/
theorem stripWidthTag_toList_prefix {s : String} {p r : List Char} (hp : '^' ∉ p)
    (hr : 3 ≤ r.length) (h : s.toList = p ++ r) :
    ∃ r', (stripWidthTag s).toList = p ++ r' := by
  unfold stripWidthTag
  split
  · rw [String.toList_ofList, h, List.takeWhile_append_of_pos (bne_at_of_not_mem hp)]
    exact ⟨_, rfl⟩
  · split
    · rw [String.toList_ofList, h]
      have h1 : r ≠ [] := by intro e; simp [e] at hr
      have h2 : r.dropLast ≠ [] := by
        intro e; have := congrArg List.length e; simp at this; omega
      have h3 : r.dropLast.dropLast ≠ [] := by
        intro e; have := congrArg List.length e; simp at this; omega
      exact ⟨_, by rw [List.dropLast_append_of_ne_nil h1, List.dropLast_append_of_ne_nil h2,
        List.dropLast_append_of_ne_nil h3]⟩
    · exact ⟨r, h⟩

/-- The width-carrying mnemonic of a `castW w w'` between 16-, 32- and 64-bit GP
    registers. The two widths are separated by `_`, not `:`, so the `:8`/`:16`/
    `:64` width tags that `mnemWidth` / `stripAbiTag` / `parseImmShiftMnem` read
    cannot collide with a carried width. A width other than `64` and `16` is read
    as `32`; `castWCarriesWidths` restricts the mnemonic to the three widths. -/
def castWMnem (w w' : Nat) : String :=
  if w == 64 then
    (if w' == 64 then "CASTW_64_64" else if w' == 16 then "CASTW_64_16" else "CASTW_64_32")
  else if w == 16 then
    (if w' == 64 then "CASTW_16_64" else if w' == 16 then "CASTW_16_16" else "CASTW_16_32")
  else
    (if w' == 64 then "CASTW_32_64" else if w' == 16 then "CASTW_32_16" else "CASTW_32_32")

/-- Read the source and destination widths off a `castWMnem` mnemonic; `none`
    for every other mnemonic, including the width-erased `ZEROEXT` / `TRUNC`. -/
def parseCastWMnem (opn : String) : Option (Nat × Nat) :=
  match opn.splitOn "_" with
  | [tag, wStr, wDstStr] =>
      if tag == "CASTW" then
        match strToNat? wStr, strToNat? wDstStr with
        | some w, some w' => some (w, w')
        | _, _ => none
      else none
  | _ => none

/-- Does a `castW w w'` carry its widths in the mnemonic? True exactly when both
    widths are `16`, `32` or `64`, the pairs the printer's `CASTW_` arm renders.
    Every other pair keeps the width-erased `ZEROEXT` / `TRUNC`: the byte-boundary
    casts `castW _ 8` / `castW 8 _`, which the printer renders as a byte
    zero-extension, and `castW 64 128`. -/
def castWCarriesWidths (w w' : Nat) : Bool :=
  (w == 16 || w == 32 || w == 64) && (w' == 16 || w' == 32 || w' == 64)

/-- The reserved `extCall` name prefix that designates a `.rodata` symbol-base
    load (`leaq sym(%rip), %dst`). An `extCall` whose `name` is
    `loadSymPrefix ++ sym` carries the link-time symbol `sym` in its name (the
    only `JasminOp` payload that can name a global), and `opToLinstrR` exports it
    as the `"LOADSYM"` mnemonic instead of `CALL:`. The prefix is deliberately
    `__`-leading so it can never collide with a real external-function name. -/
def loadSymPrefix : String := "__loadsym:"

/-- Recognise a reserved symbol-load `extCall` name and return the symbol it
    carries: `loadSymTarget? (loadSymPrefix ++ sym) = some sym`, and `none` for
    any other name (every real external call). This is the seam that lets the
    opaque `extCall` op carry a `.rodata` symbol without a new `JasminOp`
    constructor. -/
def loadSymTarget? (name : String) : Option String :=
  -- Match on the character lists (not `String.startsWith`/`drop`): the
  -- `String.toList`/`List.isPrefixOf` form **kernel-reduces** on string
  -- literals (the `Substring`/`utf8Encode`-based `String.startsWith` does not),
  -- so the recogniser, the exporter arm, and the lowering all close by
  -- `rfl`/`decide` on the concrete reserved name.
  let pfx := loadSymPrefix.toList
  let ns := name.toList
  if pfx.isPrefixOf ns then some (String.ofList (ns.drop pfx.length)) else none

/-- The bit-width an `extCall`/`callN` argument or result marshals at across the
    System V AMD64 boundary. A `reg w` marshals at `w`: `w ≤ 64` in a GP register
    (`RDI…R9` / `RAX`), `w = 128` in an SSE (xmm) register. Every other type — a
    stack array (passed as a *pointer*, 64-bit GP), an inline int, a bool —
    marshals in a 64-bit GP register. The single width source of truth for the
    call ABI class, read off the op's declared `argTys`/`retTy`. -/
def callMarshalWidth : JasminTy → Nat
  | .reg w => w
  | _ => 64

/-- Encode a leaf call's per-argument + result marshal widths into the shadow
    mnemonic so the downstream `expandCallShadows` / loop-body expansion can
    dispatch each argument to the correct SysV register class **by type**. Shape
    `<pfx><retW>;<w0,w1,…>;<name>` (e.g. `CALLW:128;128;bf128_mul`). Only emitted
    when some width is non-GP (`> 64`); an all-`reg 64` call keeps the plain
    `CALL:`/`CALLN:` shadow, so every existing kernel's bytes are unchanged. -/
def encodeCallW (pfx name : String) (retW : Nat) (argWs : List Nat) : String :=
  pfx ++ toString retW ++ ";"
    ++ String.intercalate "," (argWs.map toString) ++ ";" ++ name

/-- Does any of `retW :: argWs` marshal in a non-GP (SSE, `> 64`) register? Gates
    the `CALLW:`/`CALLNW:` widened shadow: `false` ⇒ the call is all-GP and keeps
    the byte-identical `CALL:`/`CALLN:` shadow. -/
def callHasWide (retW : Nat) (argWs : List Nat) : Bool :=
  retW > 64 || argWs.any (· > 64)

/-- Map a single `JasminOp` (with its source operand names and destination
    register name) to the corresponding `linstr_r`. Every op lowers to an
    `Lopn` (the word-level two-address fragment is straight-line). -/
def opToLinstrR (op : JasminOp) (dst : String) (srcs : List LOperand) : LinstrR :=
  match op with
  | .regArith bop w => .Lopn [.reg dst] (withWidthTag w (binOpName bop)) srcs
  | .select w => .Lopn [.reg dst] (withWidthTag w "CMOV") srcs
  -- `stackLoad w n`: sources are `[arr, idx]` (the array operand and the
  -- *runtime* index register). When the index resolves to a register, fold the
  -- two into one register-indexed (SIB) memory operand `base[idx*scale]` with
  -- `scale = w/8` (the element stride in bytes) — the x86
  -- `(%base,%idx,scale)` effective address. The single `arrIdx` source replaces
  -- the `[arr, idx]` pair, so the reader emits a base+index*scale load directly
  -- instead of decomposing it into an address computation. Compile-time / non-
  -- register shapes (`.arr` element, immediate index) keep the scalar `LOAD`.
  | .stackLoad w _ =>
      match srcs with
      | [.reg base, .reg idx] => .Lopn [.reg dst] "LOADIDX" [.arrIdx base idx (w / 8)]
      | _ => .Lopn [.reg dst] "LOAD" srcs
  -- `stackStore w n`: sources are `[arr, idx, val]`. The runtime-indexed image
  -- routes the (array, index) pair into a SIB destination `base[idx*scale]` and
  -- keeps the stored value as the lone source. The result register `dst` names
  -- the functionally-updated array (the dialect's `stackStore` returns the new
  -- array), so it is still the `Lopn` destination for the slot trace.
  | .stackStore w _ =>
      match srcs with
      | [.reg base, .reg idx, val] =>
          .Lopn [.reg dst] "STOREIDX" [.arrIdx base idx (w / 8), val]
      | _ => .Lopn [.reg dst] "STORE" srcs
  -- A cast between 16-, 32- and 64-bit registers carries both widths in the
  -- mnemonic (`castWMnem`, whose `_` separator cannot be read as a `:64` width
  -- tag), because the printer's `ZEROEXT`/`TRUNC` arm assumes the cast crosses the
  -- byte boundary and renders a byte mask. Every other cast keeps that mnemonic.
  | .castW w w' =>
      if castWCarriesWidths w w' then .Lopn [.reg dst] (castWMnem w w') srcs
      else .Lopn [.reg dst] (if w' ≥ w then "ZEROEXT" else "TRUNC") srcs
  -- `extCall` is the opaque external-leaf op. Its `name` String is the only
  -- payload that can carry a *link-time symbol*, so the reserved name shape
  -- `loadSymPrefix ++ sym` (`"__loadsym:" ++ sym`) designates the `.rodata`
  -- symbol-base load (`leaq sym(%rip), %dst`, the NTT twiddle-table base): on it
  -- the exporter emits the `"LOADSYM"` mnemonic that `lowerLinstrExtCovMS`
  -- lowers to `JInstr.loadSym` and `LprogAsmPrinter` renders, with the symbol
  -- name carried as a `.reg` operand (a link-time constant, not a runtime
  -- register). Every NON-reserved `extCall` name keeps the original `CALL:`
  -- mnemonic byte-for-byte, so existing kernels' exported bytes are unchanged.
  | .extCall name argTys retTy =>
      match loadSymTarget? name with
      | some sym => .Lopn [.reg dst] "LOADSYM" [.reg sym]
      | none =>
          -- Type-driven marshalling class: an argument or result wider than a GP
          -- word (`reg 128`) is passed/returned in an SSE (xmm) register, so its
          -- width must reach `expandCallShadows`. When any width is non-GP the
          -- shadow is the widened `CALLW:<retW>;<argWs>;<name>`; an all-`reg 64`
          -- call keeps the plain `CALL:<name>` shadow byte-for-byte.
          let argWs := argTys.map callMarshalWidth
          let retW := callMarshalWidth retTy
          if callHasWide retW argWs then
            .Lopn [.reg dst] (encodeCallW "CALLW:" name retW argWs) srcs
          else .Lopn [.reg dst] ("CALL:" ++ name) srcs
  -- A `regConst w n` materialises the literal `n` into `dst`. We render it as an
  -- immediate-MOV (`MOV[:w] dst, #n`) so the patched jasmin `read_linear` reuses
  -- its existing immediate-MOV path (`movabs` for `n ≥ 2^31` via
  -- `materializeWideImm`); no `CONST` mnemonic / reader extension is needed. The
  -- nullary `regConst` carries no source operand, so the immediate is the sole
  -- source. (Width-tagged at the binding's `w` so U64 constants land at U64.)
  | .regConst w n => .Lopn [.reg dst] (withWidthTag w "MOV") [.imm n]
  | .vpackZMM bop => .Lopn [.reg dst] ("VPACK8u64:" ++ binOpName bop) srcs
  | .vpackZMMd bop => .Lopn [.reg dst] ("VPACKD:" ++ binOpName bop) srcs
  | .vprordZMM n => .Lopn [.reg dst] ("VPRORD:" ++ toString n) srcs
  | .vpslldq n => .Lopn [.reg dst] ("VPSLLDQ:" ++ toString n) srcs
  | .vpsrldq n => .Lopn [.reg dst] ("VPSRLDQ:" ++ toString n) srcs
  | .vsimd op => .Lopn [.reg dst] op.mnemonic srcs
  | .vymm op => .Lopn [.reg dst] op.jasminMnemonic srcs
  -- Widening-multiply + carry-chain ops. `mulhi`/`addCarryLo`/
  -- `addCarryHi` are single-output `Com` ops, but `MULX` / `ADCX` / `ADOX`
  -- are two-output / flag-coupled at the asm level. The textual mnemonic
  -- names the *role* the binding plays; `read_linear` reassembles each into
  -- the corresponding jasmin `sopn` (synthesizing the second destination /
  -- the CF/OF flag operand the descriptor requires).
  --
  --  * `MULXHI` — the high-word binding of a `MULX`; the matching low-word
  --    binding is the producer's `regArith .mul` over the same two sources.
  --  * `ADCX` / `ADOX` — the data binding (`dst := dst + src + cin`) of a
  --    carry-chain add. The third source is the carry-in `reg 1`; the reader
  --    routes it through the CF (`ADCX`) resp. OF (`ADOX`) flag.
  --  * `ADCXHI` / `ADOXHI` — the carry-out (`reg 1`) binding of the same add;
  --    it reads the post-add CF/OF and is materialised as a `SETcc`-style
  --    flag read (kept on the value path as a distinct mnemonic so the carry
  --    thread is explicit in the IR).
  | .mulhi w => .Lopn [.reg dst] (withWidthTag w "MULXHI") srcs
  | .addCarryLo w => .Lopn [.reg dst] (withWidthTag w "ADCX") srcs
  | .addCarryHi w => .Lopn [.reg dst] (withWidthTag w "ADCXHI") srcs
  -- Native right-rotate: the single-op image of the `shr; shl; or`
  -- rotate idiom. `ROR:<n>` carries the compile-time rotate amount in the
  -- mnemonic; the single source is the rotated register. `read_linear` maps
  -- it to the x86 `#ROR_w` (flag-clobbering) resp. BMI2 `#RORX_w` (flag-free)
  -- sopn. One linstr replaces the three the shift-or form produced.
  | .rorImm w n => .Lopn [.reg dst] (withWidthTag w ("ROR:" ++ toString n)) srcs
  -- Native immediate shifts: `SHR:<n>` / `SHL:<n>` carry the compile-time
  -- shift amount in the mnemonic; the single source is the shifted register.
  -- `read_linear` maps each to the x86 `SHR`/`SHL r, imm` sopn (one linstr).
  | .shrImm w n => .Lopn [.reg dst] (withWidthTag w ("SHR:" ++ toString n)) srcs
  -- Native immediate arithmetic right-shift: `SAR:<k>` carries the clamped
  -- count `k = sarCount w n < w`; `read_linear` maps it to the x86 `SAR r, imm`.
  | .sarImm w n => .Lopn [.reg dst] (withWidthTag w ("SAR:" ++ toString (sarCount w n))) srcs
  | .shlImm w n => .Lopn [.reg dst] (withWidthTag w ("SHL:" ++ toString n)) srcs
  -- Multi-result external call (`func.call` lowering target). At this
  -- single-output linstr layer it names its head result slot, mirroring the
  -- single-result `extCall` `CALL:` mnemonic with a `CALLN:` tag.
  | .callN name argTys retTys =>
      -- `retTys` is the full multi-result list; the single-output linstr layer
      -- names the *head* result (mirroring the plain `CALLN:` mnemonic), so the
      -- return width is the head result's width.
      let argWs := argTys.map callMarshalWidth
      let retW := callMarshalWidth (retTys.headD (.reg 0))
      if callHasWide retW argWs then
        .Lopn [.reg dst] (encodeCallW "CALLNW:" name retW argWs) srcs
      else .Lopn [.reg dst] ("CALLN:" ++ name) srcs
  -- Scalar comparison: `SET<cc>` over the two compared operands, width-tagged at
  -- the operand width. The destination receives `1` or `0`. The immediate form
  -- carries its constant as a second, immediate source, so both forms share one
  -- mnemonic family and one machine-model arm.
  | .cmp c w => .Lopn [.reg dst] (withWidthTag w (cmpName c)) srcs
  | .cmpImm c w n => .Lopn [.reg dst] (withWidthTag w (cmpName c)) (srcs ++ [.imm n])
  -- Fresh zero array: the single pseudo-instruction `ZEROARR` whose two immediate
  -- sources are the element count `n` and the element width `w`. The nullary
  -- operation has no other source. The printer and the encoder have no `ZEROARR`
  -- arm and refuse it.
  | .stackZero w n => .Lopn [.reg dst] "ZEROARR" [.imm n, .imm w]
  -- Constant-index store: the single pseudo-instruction `STOREIMM` whose sources are
  -- the array operand, the stored value and the immediate index `i`. The
  -- destination register `dst` names the updated array, as for `STOREIDX`. The
  -- printer and the encoder have no `STOREIMM` arm and refuse it.
  | .stackStoreImm _ _ i => .Lopn [.reg dst] "STOREIMM" (srcs ++ [.imm i])

/-! ### The operand widths of a general-purpose operation

`opToLinstrR` writes the operand width of a general-purpose operation into its mnemonic
(`withWidthTag`: `:64` at width `64`, `^w` at every other width) and, for a cast, the
widths `16`, `32` and `64` (`castWMnem`). The printer and the encoder read a mnemonic
without the `:64` tag at 32 bits, so the text of an operation wider than a
general-purpose register does not compute its value.
`opWidthOk` is the condition on an operation under which that reading is defined, and
`comWidthsOk` is the condition on a program. -/

/-- The operand widths of the general-purpose operations: the arithmetic, shift, carry,
    multiply-high and compare operations and both widths of a cast. A constant
    (`regConst`) and a select are not listed, because a 128- or 256-bit constant is a
    vector constant with its own rendering. -/
def opGpWidths : JasminOp → List Nat
  | .regArith _ w => [w]
  | .castW w w' => [w, w']
  | .mulhi w => [w]
  | .addCarryLo w => [w]
  | .addCarryHi w => [w]
  | .rorImm w _ => [w]
  | .shrImm w _ => [w]
  | .sarImm w _ => [w]
  | .shlImm w _ => [w]
  | .cmp _ w => [w]
  | .cmpImm _ w _ => [w]
  | _ => []

/-- Every operand width of a general-purpose operation is at most `64`. -/
def opWidthOk (op : JasminOp) : Bool := (opGpWidths op).all (· ≤ 64)

/-- Every binding of the program satisfies `opWidthOk`. -/
def comWidthsOk : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opWidthOk e.op && comWidthsOk body

/-- An arithmetic operation at a width above `64` fails `opWidthOk`. -/
theorem opWidthOk_regArith (bop : JasminBinOp) (w : Nat) :
    opWidthOk (.regArith bop w) = decide (w ≤ 64) := by
  simp [opWidthOk, opGpWidths]

/-- A 128-bit arithmetic operation fails `opWidthOk`. -/
theorem opWidthOk_regArith_128 (bop : JasminBinOp) :
    opWidthOk (.regArith bop 128) = false := by
  simp [opWidthOk, opGpWidths]

/-- A program whose first binding fails `opWidthOk` fails `comWidthsOk`. -/
theorem comWidthsOk_var_false {Γ : Ctxt jasminDialect} {t τ : JasminTy}
    (e : Expr jasminDialect Γ τ) (body : Com jasminDialect (Γ.cons τ) t)
    (h : opWidthOk e.op = false) : comWidthsOk (.var e body) = false := by
  simp [comWidthsOk, h]

/-! ## 3. Walking the `Com` term

`Com jasminDialect Γ t` is an A-normal-form let-chain. We accumulate `linstr`s
top-down, tracking the current let-depth so that each binding's result and each
variable reference resolve to a stable register name.

A `Var Γ τ` is a De Bruijn index into `Γ`. At the point a binding is emitted the
context `Γ` has `curDepth` entries, all introduced by enclosing `.var`s plus the
`nArgs` initial arguments. We map a `Var` to the register name of the binder that
introduced it: `regName (curDepth - 1 - deBruijn)` for let-bound vars, falling
back to argument names for the initial context tail. -/

/-- De Bruijn index of a `Var` (distance from the most recent binder). -/
def varIndex {Γ : Ctxt jasminDialect} {τ : JasminTy} : Ctxt.Var Γ τ → Nat
  | .here => 0
  | .there v => varIndex v + 1

/-- A producer-level **immediate slot map**: maps an argument *slot* index `j`
    (program-root order, 0-based, corresponding to `argName j` / `a{j}`) to the
    literal value of the input when that input is a known compile-time constant.

    A `Var` whose resolved slot lies in `[0, nArgs)` and is covered by this map
    is rendered as an `LOperand.imm` *at producer time* (before `physBody`
    re-lowering), so the physical export sees the constant as `#v` directly
    instead of trying to allocate a physical register for it. The default
    `fun _ => none` keeps every argument as a register (the original behaviour);
    a producer that knows its constant inputs supplies the concrete map
    (e.g. ChaCha's `a32 … a38 ↦ 16,12,8,7,20,24,25`). -/
abbrev ImmSlotMap := Nat → Option Nat

/-- Resolve a `Var` to an `LOperand` given the current context depth and the
    initial-argument names. De Bruijn index `i` refers to the binder
    `curDepth - 1 - i` from the root; if that lands in the argument prefix
    (`< nArgs`) it names an argument, otherwise an SSA register `r{slot}`.

    An `immSlotMap` (default `fun _ => none`) lets a producer mark constant
    argument inputs: when `slot < nArgs` and `immSlotMap slot = some v` the
    variable is rendered as `.imm v` instead of `.reg (argNames slot)`. This is
    the slot-based analogue of `ChaChaEmit.chachaInName`'s `i ≥ 32 ⇒
    toString (shiftConstNat (i - 32))` for the textual jazz printer. -/
def resolveVar (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) : LOperand :=
  let i := varIndex v
  -- slot counted from the program root (0 = first thing bound)
  let slot := curDepth - 1 - i
  if slot < nArgs then
    match immSlotMap slot with
    | some v => .imm v
    | none => .reg (argNames slot)
  else .reg (regName slot)

/-- Collect the argument operands of an `Expr` as a `List LOperand`. -/
def exprArgs (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest => resolveVar curDepth nArgs argNames immSlotMap v :: go rest
  go e.args

/-- Resolve an `HVector` of in-scope variables (not an `Expr`) to a `List
    LOperand` against the enclosing context. The `forLoopN` node's invariant
    seeds (`invs : HVector (Var Γ) invTys`) are resolved with this — the
    `exprArgs` body specialised to a bare variable vector. -/
def exprArgsHV (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) {Γ : Ctxt jasminDialect} :
    {tys : Ctxt jasminDialect} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    List LOperand
  | [], _ => []
  | _ :: _, .cons v rest =>
      resolveVar curDepth nArgs argNames immSlotMap v
        :: exprArgsHV curDepth nArgs argNames immSlotMap rest

/-- Walk the `Com`, producing the list of `linstr`s in program order. `curDepth`
    is the number of bindings already in scope (= argument count + lets emitted
    so far). The terminal `.ret` becomes an `Lret` (the result register is the
    function's `lfd_res`).

    The `immSlotMap` (default: none) is consulted by `resolveVar`/`exprArgs` to
    substitute constant argument inputs with `.imm` operands at producer time
    (see `ImmSlotMap`). -/
def comToBody (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Lcmd
  | _, _, .ret _, _ => [⟨0, .Lret⟩]
  | _, _, .var e body, curDepth =>
      let srcs := exprArgs curDepth nArgs argNames immSlotMap e
      let instr : Linstr := ⟨0, opToLinstrR e.op (regName curDepth) srcs⟩
      instr :: comToBody nArgs argNames immSlotMap body (curDepth + 1)

/-- The register name of the final return value of a `Com` (the binder the
    terminal `.ret` points at). The return slot is always rendered as a real
    name (no `immSlotMap` lookup) — a function cannot return an immediate. -/
def comRetReg (nArgs : Nat) (argNames : Nat → String) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → String
  | _, _, .ret v, curDepth =>
      match resolveVar curDepth nArgs argNames (fun _ => none) v with
      | .reg n => n
      | .arr b i => b ++ "[" ++ toString i ++ "]"
      | .imm n => toString n
      | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]"
  | _, _, .var _ body, curDepth => comRetReg nArgs argNames body (curDepth + 1)

/-- Bit width of a `JasminTy` as an `ltype` `U w` width (0 for non-word). -/
def tyWidth : JasminTy → Nat
  | .reg w => w
  | .stackArr w _ => w
  | .inlineInt => 0
  | .bool => 1

/-! ## 4. The export: `Com → Lprog`

The argument context `Γ` becomes the function's `lfd_arg`/`lfd_tyin`: argument
`j` (counted from the program root, i.e. the *tail* of `Γ`) is named `a{j}` and
typed by its `JasminTy` width. -/

/-- The argument register name for argument slot `j` (program-root order). -/
def argName (j : Nat) : String := "a" ++ toString j

/-- Build the `lfundef` for a `Com` over argument context `Γ`.
    `immSlotMap` (default: none) substitutes constant argument inputs with
    `.imm` operands at producer time (see `ImmSlotMap`). -/
def comToLfundef {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lfundef :=
  let nArgs := Γ.length
  -- `Γ` lists most-recent binder first; argument slot `j` (root order) is
  -- entry `nArgs - 1 - j`, whose width we read off the type list.
  let argTys := Γ.reverse.map tyWidth
  { lfd_info := 0
    lfd_align := 1
    lfd_tyin := argTys
    lfd_arg := (List.range nArgs).map argName
    lfd_body := comToBody nArgs argName immSlotMap com nArgs
    lfd_tyout := [tyWidth t]
    lfd_res := [comRetReg nArgs argName com nArgs]
    lfd_export := true
    lfd_callee_saved := []
    lfd_stk_max := 0
    lfd_frame_size := 0
    lfd_align_args := [] }

/-- Export a `Com jasminDialect` to a value-level `Lprog` with the given function
    name. Uses the conventional `lp_rip="RIP"`/`lp_rsp="RSP"` and empty globals
    (the ChaCha20-block case carries no read-only data section). -/
def Com.toLprog {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs := [(fname, comToLfundef com immSlotMap)] }

/-! ### `.rodata` global-table population (the symbol-load companion)

`Com.toLprog` leaves `lp_globs`/`lp_glob_names` empty (no read-only data
section), which is what every kernel without a global table wants. A kernel that
*does* read a `.rodata` table (the NTT twiddle gather, via the `"LOADSYM"`
export arm above) must additionally declare that table in the `Lprog`'s globals,
so `LprogAsmPrinter.lprogRodata` (gated on `lp_globs ≠ []`) renders a
`.section .rodata` + `<sym>:` + `.quad` block the `leaq sym(%rip)` resolves
against. `withRodataTable` fills both global fields for one named u64 table:

* `lp_glob_names` gets one `(sym, 8, v.toNat)` entry per table word (the
  `lprogRodata` reader groups consecutive same-name entries into one `.quad`
  table, preserving order);
* `lp_globs` gets the table's flat little-endian u8 blob (Jasmin's `seq u8`
  global image), which is what trips the `lprogRodata` non-empty guard and what a
  Marshal-path reader would materialise.

It is additive over an existing `Lprog`: the table is appended, so a program
that already declared globals keeps them and the new table's words follow. -/

/-- The 8 little-endian u8 bytes of a `BitVec 64` word. -/
def word64Bytes (w : BitVec 64) : List Nat :=
  (List.range 8).map (fun i => ((w >>> (8 * i)).toNat) % 256)

/-- Attach a named u64 `.rodata` table `(sym, table)` to an `Lprog`'s globals so
    the `.rodata`-rendering seam (`LprogAsmPrinter.lprogRodata`, gated on
    `lp_globs ≠ []`) emits it. Each table word becomes one `(sym, 8, value)`
    `lp_glob_names` entry and its 8 little-endian bytes are appended to the flat
    `lp_globs` u8 blob. Additive: existing globals are preserved, the new table's
    entries/bytes follow. -/
def Lprog.withRodataTable (p : Lprog) (sym : String) (table : List (BitVec 64)) :
    Lprog :=
  { p with
    lp_globs := p.lp_globs ++ table.flatMap word64Bytes
    lp_glob_names := p.lp_glob_names ++ table.map (fun w => (sym, 8, w.toNat)) }

/-- Export a `Com` and attach one `.rodata` symbol table in one step: the
    `"LOADSYM"`-emitting companion of `Com.toLprog`. The exported program reads
    the table `sym` (declared in `lp_globs`/`lp_glob_names`) via any
    `extCall (loadSymPrefix ++ sym)` binding in the `Com`. -/
def Com.toLprogWithRodata {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname sym : String) (table : List (BitVec 64))
    (immSlotMap : ImmSlotMap := fun _ => none) : Lprog :=
  (Com.toLprog com fname immSlotMap).withRodataTable sym table

/-! ## 5. Textual serialization

A line-oriented textual representation mirroring the structure (the wire format,
since the OCaml `Marshal` representation is not Lean-reproducible — see header).
Format: every `lprog`/`lfundef` field on its own keyed line, the body as one
`instr` line per `linstr`. Deterministic, so it round-trips structurally. -/

/-- Render an `LOperand`. -/
def LOperand.toText : LOperand → String
  | .reg n => n
  | .arr b i => b ++ "[" ++ toString i ++ "]"
  | .imm v => "#" ++ toString v
  -- Register-indexed SIB element `base[idx*scale]`: the reader parses the
  -- `*scale` suffix as the x86 index scale, distinguishing it from the
  -- compile-time `.arr` form `base[const]`.
  | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]"

/-- Render a `LinstrR` as a single text line. -/
def LinstrR.toText : LinstrR → String
  | .Lopn dsts opn srcs =>
      "Lopn [" ++ String.intercalate "," (dsts.map LOperand.toText) ++ "] " ++
        opn ++ " [" ++ String.intercalate "," (srcs.map LOperand.toText) ++ "]"
  | .Lsyscall n => "Lsyscall " ++ n
  | .Lcall ra (f, l) => "Lcall " ++ (ra.getD "-") ++ " " ++ f ++ ":" ++ toString l
  | .Lret => "Lret"
  | .Lalign => "Lalign"
  | .Llabel k l =>
      "Llabel " ++ (match k with | .internal => "int" | .external => "ext") ++
        " " ++ toString l
  | .Lgoto (f, l) => "Lgoto " ++ f ++ ":" ++ toString l
  | .Ligoto o => "Ligoto " ++ o.toText
  | .LstoreLabel d l => "LstoreLabel " ++ d ++ " " ++ toString l
  | .Lcond c l => "Lcond " ++ c.toText ++ " " ++ toString l

/-- Render an `Lfundef`. -/
def Lfundef.toText (name : String) (f : Lfundef) : String :=
  let nats (xs : List Nat) := String.intercalate "," (xs.map toString)
  let strs (xs : List String) := String.intercalate "," xs
  String.intercalate "\n"
    ([ "lfundef " ++ name
     , "  lfd_info " ++ toString f.lfd_info
     , "  lfd_align " ++ toString f.lfd_align
     , "  lfd_tyin " ++ nats f.lfd_tyin
     , "  lfd_arg " ++ strs f.lfd_arg
     , "  lfd_tyout " ++ nats f.lfd_tyout
     , "  lfd_res " ++ strs f.lfd_res
     , "  lfd_export " ++ (if f.lfd_export then "true" else "false")
     , "  lfd_callee_saved " ++ strs f.lfd_callee_saved
     , "  lfd_stk_max " ++ toString f.lfd_stk_max
     , "  lfd_frame_size " ++ toString f.lfd_frame_size
     , "  lfd_align_args " ++ nats f.lfd_align_args
     , "  lfd_body " ++ toString f.lfd_body.length ]
     ++ f.lfd_body.map (fun i => "    instr " ++ toString i.li_ii ++ " " ++ i.li_i.toText))

/-- Render a `Lprog`. -/
def Lprog.toText (p : Lprog) : String :=
  let globNames :=
    String.intercalate ";" (p.lp_glob_names.map (fun (n, w, z) =>
      n ++ ":" ++ toString w ++ ":" ++ toString z))
  String.intercalate "\n"
    ([ "lprog"
     , "lp_rip " ++ p.lp_rip
     , "lp_rsp " ++ p.lp_rsp
     , "lp_globs " ++ String.intercalate "," (p.lp_globs.map toString)
     , "lp_glob_names " ++ globNames
     , "lp_funcs " ++ toString p.lp_funcs.length ]
     ++ p.lp_funcs.map (fun (n, f) => f.toText n))

/-- The OCaml-side magic header, prefixed to the serialized blob. Matches
    `Read_linear.magic` exactly (`patches/jasmin/read_linear.ml.patch`). -/
def magic : String := "JASMIN-LPROG-MARSHAL-v1\n"

/-- Serialize a `Com` to the textual lprog representation (magic + text). -/
def Com.toLprogText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : String :=
  magic ++ (Com.toLprog com fname).toText ++ "\n"

/-- The serialized bytes of a `Com` as an lprog blob. -/
def Com.toLprogBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : ByteArray :=
  (Com.toLprogText com fname).toUTF8

/-- Write the textual lprog blob for a `Com` to a file. The OCaml reader as
    shipped expects the `Marshal` path; this textual blob is the seam
    where the textual reader (or an OCaml `Marshal` FFI) must close link 2/7. -/
def Com.writeLprogFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (path : System.FilePath) :
    IO Unit :=
  IO.FS.writeBinFile path (Com.toLprogBytes com fname)

/-! ## 6. Value-level export correctness

The structural well-formedness obligations are discharged here; semantic
preservation under jasmin's `lsem` is the named hypothesis below. -/

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
