/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.OpenQASMImport
public import Transfer.Combinators.ParamArrow
public import Transfer.Combinators.ParamData
import all Init.Data.String.Legacy
import all Init.Data.String.TakeDrop
import all Init.Data.String.Slice

/-!
# Importing OpenQASM files from their bytes

The importer `OpenQASMImport.importQASM` reads a file as a `String`, splits it into
lines and parses each line as a list of characters. This module computes the same
function on the bytes of the file: a line is a span `⟨bs, lo, hi⟩` of byte indices,
found by scanning for the newline byte, and each parsing combinator reads the bytes
of a span by index.

The byte and character views are related by the representation relation
`paramChars : Param .map3 .map0 ByteSpan (List Char)`, the graph of `ByteSpan.chars`,
which reads each byte as the character with that code point. Each byte combinator
has a square against its list counterpart, stated as the Trocq arrow relation
`R_arrow paramChars _`: related inputs give related (for `Option` and `Bool`
results, equal) outputs. The importer's equation is assembled from these squares and
from the facts relating the `String` operations of the list importer (`splitOn`,
`trimAsciiStart`, `startsWith`, `==`) to list operations on `String.toList`, which
hold for every string whose characters are ASCII.

The angle text of a gate (between its parentheses) and the digits of an `rz`
operand are decoded to characters and read by `OpenQASMImport.angleOf` and
`String.toNat?`, and the operation name of a line that `OpenQASMParser.parseLine`
does not read is decoded before the name dispatch.

## Main definitions

* `ByteSpan`, `ByteSpan.chars`, `paramChars` — byte spans and the relation to the
  characters they denote.
* `dropWhileB`, `takeWhileB`, `hasPrefixB`, `eqLitB`, `natOfDigitsB`, `splitB`,
  `bracketB`, `parenArgB`, `parseAnglesB` — the byte combinators.
* `parseLineB`, `parseQB`, `parseOpsB`, `importQB`, `importGatesB`, `importQASMB` — the byte
  importer.

## Main results

* `dropWhileB_square`, `takeWhileB_square`, `hasPrefixB_square`, `natOfDigitsB_square`,
  `splitB_square`, `parseLineB_square`, `parseQB_square`, `parseOpsB_square` — the
  squares.
* `splitOn_ascii`, `trimAsciiStart_copy` — the `String` operations as list operations.
* `importQASMB_eq` — on the UTF-8 bytes of an ASCII source, the byte importer returns
  what `OpenQASMImport.importQASM` returns.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.OpenQASMBytes

open CatCrypt.Quantum.QCircuit Transfer Transfer.Param

/-! ## Byte spans -/

/-- The character whose code point is the byte `b`. -/
@[inline] def byteChar (b : UInt8) : Char := Char.ofNat b.toNat

/-- The bytes `bs[lo], …, bs[hi - 1]` of a byte array. -/
structure ByteSpan where
  /-- The underlying bytes. -/
  bs : ByteArray
  /-- The first index of the span. -/
  lo : ℕ
  /-- One past the last index of the span. -/
  hi : ℕ

namespace ByteSpan

/-- The character at index `k` of the underlying bytes. -/
@[inline] def charAt (s : ByteSpan) (k : ℕ) : Char := byteChar s.bs[k]!

/-- The characters a span denotes, one per byte. -/
def chars (s : ByteSpan) : List Char :=
  (List.range' s.lo (s.hi - s.lo)).map s.charAt

theorem chars_of_le {s : ByteSpan} (h : s.hi ≤ s.lo) : s.chars = [] := by
  simp [chars, Nat.sub_eq_zero_of_le h]

theorem chars_of_lt (bs : ByteArray) {lo hi : ℕ} (h : lo < hi) :
    (⟨bs, lo, hi⟩ : ByteSpan).chars = byteChar bs[lo]! :: (⟨bs, lo + 1, hi⟩ : ByteSpan).chars := by
  simp only [chars]
  rw [show hi - lo = (hi - (lo + 1)) + 1 by omega, List.range'_succ]
  rfl

theorem chars_snoc (bs : ByteArray) {lo hi : ℕ} (h : lo ≤ hi) :
    (⟨bs, lo, hi + 1⟩ : ByteSpan).chars =
      (⟨bs, lo, hi⟩ : ByteSpan).chars ++ [byteChar bs[hi]!] := by
  simp only [chars]
  rw [show hi + 1 - lo = (hi - lo) + 1 by omega, List.range'_concat]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [show lo + 1 * (hi - lo) = hi by omega]
  rfl

theorem length_chars (s : ByteSpan) : s.chars.length = s.hi - s.lo := by
  simp [chars]

end ByteSpan

open ByteSpan

/-- The relation of a byte span to the characters it denotes: the graph of
`ByteSpan.chars`, at the level `map3` forward. -/
def paramChars : Param .map3 .map0 ByteSpan (List Char) where
  R s cs := s.chars = cs
  fwd := ⟨ByteSpan.chars, fun _ _ h => h, fun _ _ h => h⟩
  bwd := ⟨⟩

/-! ## Scanning -/

/-- The first index `j ≥ k` below `hi` whose character fails `p`, or `max k hi`. -/
def scanWhile (p : Char → Bool) (bs : ByteArray) (hi : ℕ) (k : ℕ) : ℕ :=
  if k < hi then
    if p (byteChar bs[k]!) then scanWhile p bs hi (k + 1) else k
  else k
termination_by hi - k

theorem le_scanWhile (p : Char → Bool) (bs : ByteArray) (hi : ℕ) (k : ℕ) :
    k ≤ scanWhile p bs hi k := by
  fun_induction scanWhile p bs hi k <;> omega

/-- The span without its leading characters satisfying `p`. -/
@[inline] def dropWhileB (p : Char → Bool) (s : ByteSpan) : ByteSpan :=
  ⟨s.bs, scanWhile p s.bs s.hi s.lo, s.hi⟩

/-- The leading characters of the span satisfying `p`. -/
@[inline] def takeWhileB (p : Char → Bool) (s : ByteSpan) : ByteSpan :=
  ⟨s.bs, s.lo, scanWhile p s.bs s.hi s.lo⟩

theorem chars_dropWhileB (p : Char → Bool) (s : ByteSpan) :
    (dropWhileB p s).chars = s.chars.dropWhile p := by
  obtain ⟨bs, lo, hi⟩ := s
  simp only [dropWhileB]
  fun_induction scanWhile p bs hi lo with
  | case1 k hk hp ih => rw [ih, chars_of_lt bs hk, List.dropWhile_cons_of_pos hp]
  | case2 k hk hp => rw [chars_of_lt bs hk, List.dropWhile_cons_of_neg (by simpa using hp)]
  | case3 k hk => rw [chars_of_le (by simp; omega)]; rfl

theorem chars_takeWhileB (p : Char → Bool) (s : ByteSpan) :
    (takeWhileB p s).chars = s.chars.takeWhile p := by
  obtain ⟨bs, lo, hi⟩ := s
  simp only [takeWhileB]
  fun_induction scanWhile p bs hi lo with
  | case1 k hk hp ih =>
    rw [chars_of_lt bs hk, List.takeWhile_cons_of_pos hp, ← ih,
      chars_of_lt bs (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_scanWhile p bs hi (k + 1)))]
  | case2 k hk hp =>
    rw [chars_of_lt bs hk, List.takeWhile_cons_of_neg (by simpa using hp), chars_of_le le_rfl]
  | case3 k hk => rw [chars_of_le le_rfl, chars_of_le (by simp; omega)]; rfl

/-- **Square.** `dropWhileB p` realizes `List.dropWhile p`. -/
theorem dropWhileB_square (p : Char → Bool) :
    R_arrow paramChars paramChars (dropWhileB p) (List.dropWhile p) := by
  rintro s _ rfl
  exact chars_dropWhileB p s

/-- **Square.** `takeWhileB p` realizes `List.takeWhile p`. -/
theorem takeWhileB_square (p : Char → Bool) :
    R_arrow paramChars paramChars (takeWhileB p) (List.takeWhile p) := by
  rintro s _ rfl
  exact chars_takeWhileB p s

/-- The span without its first `k` bytes. -/
@[inline] def dropB (k : ℕ) (s : ByteSpan) : ByteSpan := ⟨s.bs, s.lo + k, s.hi⟩

theorem chars_dropB (k : ℕ) (s : ByteSpan) : (dropB k s).chars = s.chars.drop k := by
  obtain ⟨bs, lo, hi⟩ := s
  simp only [chars, dropB, ← List.map_drop, List.drop_range']
  rw [show lo + k * 1 = lo + k by omega, show hi - lo - k = hi - (lo + k) by omega]
  rfl

/-- Whether the span is empty. -/
@[inline] def isEmptyB (s : ByteSpan) : Bool := decide (s.hi ≤ s.lo)

theorem isEmptyB_eq (s : ByteSpan) : isEmptyB s = s.chars.isEmpty := by
  have := length_chars s
  cases h : s.chars <;> simp_all [isEmptyB] <;> omega

/-- The first character of the span, if any. -/
@[inline] def headB? (s : ByteSpan) : Option Char :=
  if s.lo < s.hi then some (s.charAt s.lo) else none

theorem headB?_eq (s : ByteSpan) : headB? s = s.chars.head? := by
  obtain ⟨bs, lo, hi⟩ := s
  by_cases h : lo < hi
  · simp [headB?, h, chars_of_lt bs h, charAt]
  · simp [headB?, h, chars_of_le (s := ⟨bs, lo, hi⟩) (by simp; omega)]

/-! ## Prefixes and literals -/

/-- Whether the characters from index `k` below `hi` begin with `l`. -/
def prefixAt (bs : ByteArray) (hi : ℕ) : ℕ → List Char → Bool
  | _, [] => true
  | k, c :: cs => decide (k < hi) && (c == byteChar bs[k]!) && prefixAt bs hi (k + 1) cs

theorem prefixAt_eq (bs : ByteArray) (hi : ℕ) (k : ℕ) (l : List Char) :
    prefixAt bs hi k l = l.isPrefixOf (⟨bs, k, hi⟩ : ByteSpan).chars := by
  induction l generalizing k with
  | nil => simp [prefixAt, List.isPrefixOf]
  | cons c cs ih =>
    by_cases h : k < hi
    · simp [prefixAt, h, ih, chars_of_lt bs h, List.isPrefixOf]
    · simp [prefixAt, h, chars_of_le (s := ⟨bs, k, hi⟩) (by simp; omega)]

/-- Whether the span begins with the characters `l`. -/
@[inline] def hasPrefixB (s : ByteSpan) (l : List Char) : Bool := prefixAt s.bs s.hi s.lo l

/-- **Square.** `hasPrefixB · l` realizes `l.isPrefixOf`. -/
theorem hasPrefixB_square (l : List Char) :
    R_arrow paramChars (paramEqCod Bool) (hasPrefixB · l) l.isPrefixOf := by
  rintro s _ rfl
  exact prefixAt_eq s.bs s.hi s.lo l

theorem hasPrefixB_eq (s : ByteSpan) (l : List Char) : hasPrefixB s l = l.isPrefixOf s.chars :=
  hasPrefixB_square l rfl

/-- Whether the span denotes exactly the characters `l`. -/
@[inline] def eqLitB (s : ByteSpan) (l : List Char) : Bool :=
  hasPrefixB s l && (s.hi - s.lo == l.length)

theorem eqLitB_eq (s : ByteSpan) (l : List Char) : eqLitB s l = (s.chars == l) := by
  rw [eqLitB, hasPrefixB_eq, ← length_chars]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, List.isPrefixOf_iff_prefix, beq_iff_eq]
  exact ⟨fun ⟨hp, hl⟩ => (hp.eq_of_length hl.symm).symm, fun h => by subst h; simp⟩

/-! ## Folds and numbers -/

/-- The left fold of `f` over the characters from index `k` below `hi`. -/
def foldlB {β : Type} (f : β → Char → β) (bs : ByteArray) (hi : ℕ) (k : ℕ) (b : β) : β :=
  if k < hi then foldlB f bs hi (k + 1) (f b (byteChar bs[k]!)) else b
termination_by hi - k

theorem foldlB_eq {β : Type} (f : β → Char → β) (bs : ByteArray) (hi : ℕ) (k : ℕ) (b : β) :
    foldlB f bs hi k b = (⟨bs, k, hi⟩ : ByteSpan).chars.foldl f b := by
  fun_induction foldlB f bs hi k b with
  | case1 k b hk ih => rw [ih, chars_of_lt bs hk, List.foldl_cons]
  | case2 k b hk => rw [chars_of_le (by simp; omega)]; rfl

/-- Whether every character of the span satisfies `p`. -/
@[inline] def allB (p : Char → Bool) (s : ByteSpan) : Bool := isEmptyB (dropWhileB p s)

theorem allB_eq (p : Char → Bool) (s : ByteSpan) : allB p s = s.chars.all p := by
  rw [allB, isEmptyB_eq, chars_dropWhileB]
  apply Bool.eq_iff_iff.mpr
  simp only [List.isEmpty_iff, List.all_eq_true]
  induction s.chars with
  | nil => simp
  | cons a t ih => by_cases h : p a <;> simp [h, ih]

/-- The natural number a nonempty run of decimal digits denotes, read by index. -/
def natOfDigitsB (s : ByteSpan) : Option ℕ :=
  if !isEmptyB s && allB Char.isDigit s then
    some (foldlB (fun a c => 10 * a + (c.toNat - '0'.toNat)) s.bs s.hi s.lo 0)
  else none

/-- **Square.** `natOfDigitsB` realizes `OpenQASMParser.natOfDigits`. -/
theorem natOfDigitsB_square :
    R_arrow paramChars (paramEqCod (Option ℕ)) natOfDigitsB OpenQASMParser.natOfDigits := by
  rintro s _ rfl
  change natOfDigitsB s = OpenQASMParser.natOfDigits s.chars
  rw [natOfDigitsB, OpenQASMParser.natOfDigits, isEmptyB_eq, allB_eq, foldlB_eq]

theorem natOfDigitsB_eq (s : ByteSpan) : natOfDigitsB s = OpenQASMParser.natOfDigits s.chars :=
  natOfDigitsB_square rfl

/-! ## Splitting -/

/-- The spans between occurrences of `c` from index `k` below `hi`, the current one
starting at `start`, after the spans `acc` (in reverse order). -/
def splitGo (c : Char) (bs : ByteArray) (hi : ℕ) (start k : ℕ) (acc : List ByteSpan) :
    List ByteSpan :=
  if k < hi then
    if byteChar bs[k]! == c then splitGo c bs hi (k + 1) (k + 1) (⟨bs, start, k⟩ :: acc)
    else splitGo c bs hi start (k + 1) acc
  else (⟨bs, start, hi⟩ :: acc).reverse
termination_by hi - k

theorem splitGo_eq (c : Char) (bs : ByteArray) (hi : ℕ) (start k : ℕ) (acc : List ByteSpan)
    (hsk : start ≤ k) (hk : k ≤ hi ∨ start = k) :
    (splitGo c bs hi start k acc).map ByteSpan.chars =
      acc.reverse.map ByteSpan.chars ++
        List.splitOnPPrepend (· == c) (⟨bs, k, hi⟩ : ByteSpan).chars
          (⟨bs, start, k⟩ : ByteSpan).chars.reverse := by
  fun_induction splitGo c bs hi start k acc with
  | case1 start k acc hlt hc ih =>
    rw [ih le_rfl (Or.inl hlt), chars_of_lt bs hlt,
      List.splitOnPPrepend_cons_pos (p := (· == c)) hc,
      chars_of_le (s := ⟨bs, k + 1, k + 1⟩) le_rfl]
    simp
  | case2 start k acc hlt hc ih =>
    rw [ih (by omega) (Or.inl hlt), chars_of_lt bs hlt,
      List.splitOnPPrepend_cons_neg (p := (· == c)) (by simpa using hc), chars_snoc bs hsk]
    simp
  | case3 start k acc hlt =>
    rw [chars_of_le (s := ⟨bs, k, hi⟩) (by simp; omega)]
    have : (⟨bs, start, hi⟩ : ByteSpan).chars = (⟨bs, start, k⟩ : ByteSpan).chars := by
      rcases hk with hk | hk
      · rw [show k = hi by omega]
      · subst hk; rw [chars_of_le (s := ⟨bs, start, start⟩) le_rfl,
          chars_of_le (s := ⟨bs, start, hi⟩) (by simp; omega)]
    simp [this]

/-- The spans between the occurrences of the character `c` in a span. -/
@[inline] def splitB (c : Char) (s : ByteSpan) : List ByteSpan := splitGo c s.bs s.hi s.lo s.lo []

theorem chars_splitB (c : Char) (s : ByteSpan) :
    (splitB c s).map ByteSpan.chars = s.chars.splitOn c := by
  obtain ⟨bs, lo, hi⟩ := s
  rw [splitB, splitGo_eq c bs hi lo lo [] le_rfl (Or.inr rfl),
    chars_of_le (s := ⟨bs, lo, lo⟩) le_rfl, List.splitOn_eq_splitOnP]
  simp only [List.reverse_nil, List.map_nil, List.nil_append]
  rw [List.splitOnP_eq_splitOnPPrepend]

/-- **Square.** `splitB c` realizes `List.splitOn c`, along the list lift of
`paramChars`. -/
theorem splitB_square (c : Char) (s : ByteSpan) (cs : List Char) (h : paramChars.R s cs) :
    List.Forall₂ paramChars.R (splitB c s) (cs.splitOn c) := by
  change s.chars = cs at h
  subst h
  rw [← chars_splitB]
  simp only [List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun _ _ => rfl

/-! ## ASCII strings -/

/-- Every character of `l` is below `128`. -/
def IsAsciiList (l : List Char) : Prop := ∀ c ∈ l, c.toNat < 128

/-- Every byte of `bs`, read by `getElem!`, is below `128`. -/
def AsciiBytes (bs : ByteArray) : Prop := ∀ k : ℕ, (bs[k]!).toNat < 128

theorem utf8Size_of_lt {c : Char} (h : c.toNat < 128) : c.utf8Size = 1 :=
  Char.utf8Size_eq_one_iff.mpr (by
    rw [UInt32.le_iff_toNat_le]
    change c.toNat ≤ 127
    omega)

theorem toNat_byteChar (b : UInt8) : (byteChar b).toNat = b.toNat := by
  have := b.toNat_lt
  unfold byteChar Char.ofNat
  rw [dite_eq_left_of_eq_true (eq_true (Or.inl (by omega)))]
  rfl

theorem isAsciiList_chars {s : ByteSpan} (h : AsciiBytes s.bs) : IsAsciiList s.chars := by
  intro c hc
  simp only [chars, List.mem_map] at hc
  obtain ⟨k, -, rfl⟩ := hc
  rw [charAt, toNat_byteChar]
  exact h k

theorem IsAsciiList.of_mem_drop {l : List Char} (h : IsAsciiList l) (b : ℕ) :
    IsAsciiList (l.drop b) := fun c hc => h c (List.mem_of_mem_drop hc)

/-! ## The `String` operations as list operations -/

theorem dropWhile_of_append {p : Char → Bool} {t d : List Char} (ht : t.all p = true)
    (hd : d.head?.any p = false) : (t ++ d).dropWhile p = d := by
  induction t with
  | nil =>
    cases d with
    | nil => rfl
    | cons a d => simp_all
  | cons a t ih => simp_all

/-- `trimAsciiStart` drops the leading whitespace characters. -/
theorem trimAsciiStart_copy (s : String) :
    s.trimAsciiStart.copy = String.ofList (s.toList.dropWhile Char.isWhitespace) := by
  have h1 := String.Slice.takeWhile_append_dropWhile (pat := Char.isWhitespace) (s := s.toSlice)
  have h2 := String.Slice.all_takeWhile (pat := Char.isWhitespace) (s := s.toSlice)
  have h3 := String.Slice.startsWith_dropWhile (pat := Char.isWhitespace) (s := s.toSlice)
  rw [String.Slice.all_bool_eq] at h2
  rw [String.Slice.startsWith_bool_eq_head?] at h3
  have h4 := congrArg String.toList h1
  rw [String.toList_append] at h4
  simp only [String.copy_toSlice] at h4
  rw [String.trimAsciiStart, String.Slice.trimAsciiStart, ← h4, dropWhile_of_append h2 h3,
    String.ofList_toList]

/-- `startsWith` by a string is `isPrefixOf` on the characters. -/
theorem startsWith_eq (s t : String) : s.startsWith t = t.toList.isPrefixOf s.toList :=
  Bool.eq_iff_iff.mpr (by simp [List.isPrefixOf_iff_prefix])

theorem ofList_beq (l : List Char) (t : String) : (String.ofList l == t) = (l == t.toList) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

theorem flatMap_utf8EncodeChar {l : List Char} (h : IsAsciiList l) :
    l.flatMap String.utf8EncodeChar = l.map fun c => c.val.toUInt8 := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.flatMap_cons, List.map_cons,
      String.utf8EncodeChar_eq_singleton (utf8Size_of_lt (h c (by simp))),
      ih (fun d hd => h d (by simp [hd]))]
    rfl

theorem toByteArray_ascii {s : String} (h : IsAsciiList s.toList) :
    s.toByteArray = (s.toList.map fun c => c.val.toUInt8).toByteArray := by
  rw [← String.utf8Encode_toList, List.utf8Encode, flatMap_utf8EncodeChar h]

section Raw

variable {s : String} (hs : IsAsciiList s.toList)
include hs

omit hs in
theorem utf8GetAux_ascii (l : List Char) (hl : IsAsciiList l) (j k : ℕ) :
    String.Pos.Raw.utf8GetAux l ⟨j⟩ ⟨j + k⟩ = l.getD k default := by
  induction l generalizing j k with
  | nil => simp [String.Pos.Raw.utf8GetAux]
  | cons c cs ih =>
    have hc := utf8Size_of_lt (hl c (by simp))
    cases k with
    | zero => simp [String.Pos.Raw.utf8GetAux]
    | succ k =>
      rw [String.Pos.Raw.utf8GetAux, ite_eq_right (by rw [String.Pos.Raw.mk.injEq]; omega),
        String.Pos.Raw.add_char_eq, hc, show j + (k + 1) = (j + 1) + k by omega,
        ih (fun d hd => hl d (by simp [hd]))]
      simp

theorem get_ascii (i : ℕ) : String.Pos.Raw.get s ⟨i⟩ = s.toList.getD i default := by
  rw [String.Pos.Raw.get]
  simpa using utf8GetAux_ascii s.toList hs 0 i

theorem next_ascii (i : ℕ) : String.Pos.Raw.next s ⟨i⟩ = ⟨i + 1⟩ := by
  rw [String.Pos.Raw.next, get_ascii hs, String.Pos.Raw.add_char_eq]
  congr 2
  rw [List.getD_eq_getElem?_getD]
  cases h : s.toList[i]? with
  | none => rfl
  | some c => exact utf8Size_of_lt (hs c (List.mem_of_getElem? h))

theorem utf8ByteSize_ascii : s.utf8ByteSize = s.toList.length := by
  rw [← String.size_toByteArray, toByteArray_ascii hs, List.size_toByteArray, List.length_map]

theorem atEnd_ascii (i : ℕ) : String.Pos.Raw.atEnd s ⟨i⟩ = decide (s.toList.length ≤ i) := by
  rw [String.Pos.Raw.atEnd, utf8ByteSize_ascii hs]

omit hs in
theorem extract_go₂_ascii (l : List Char) (hl : IsAsciiList l) (j k : ℕ) :
    String.Pos.Raw.extract.go₂ l ⟨j⟩ ⟨j + k⟩ = l.take k := by
  induction l generalizing j k with
  | nil => simp [String.Pos.Raw.extract.go₂]
  | cons c cs ih =>
    have hc := utf8Size_of_lt (hl c (by simp))
    cases k with
    | zero => simp [String.Pos.Raw.extract.go₂]
    | succ k =>
      rw [String.Pos.Raw.extract.go₂, ite_eq_right (by rw [String.Pos.Raw.mk.injEq]; omega),
        String.Pos.Raw.add_char_eq, hc, show j + (k + 1) = (j + 1) + k by omega,
        ih (fun d hd => hl d (by simp [hd]))]
      simp

omit hs in
theorem extract_go₁_ascii (l : List Char) (hl : IsAsciiList l) (j b : ℕ) (e : String.Pos.Raw) :
    String.Pos.Raw.extract.go₁ l ⟨j⟩ ⟨j + b⟩ e =
      String.Pos.Raw.extract.go₂ (l.drop b) ⟨j + b⟩ e := by
  induction l generalizing j b with
  | nil => simp [String.Pos.Raw.extract.go₁, String.Pos.Raw.extract.go₂]
  | cons c cs ih =>
    have hc := utf8Size_of_lt (hl c (by simp))
    cases b with
    | zero => simp [String.Pos.Raw.extract.go₁]
    | succ b =>
      rw [String.Pos.Raw.extract.go₁, ite_eq_right (by rw [String.Pos.Raw.mk.injEq]; omega),
        String.Pos.Raw.add_char_eq, hc, show j + (b + 1) = (j + 1) + b by omega,
        ih (fun d hd => hl d (by simp [hd]))]
      simp

theorem extract_ascii (b e : ℕ) (hbe : b ≤ e) :
    String.Pos.Raw.extract s ⟨b⟩ ⟨e⟩ = String.ofList ((s.toList.drop b).take (e - b)) := by
  rw [String.Pos.Raw.extract]
  split_ifs with h
  · simp at h
    rw [show e - b = 0 by omega]
    simp
  · have h1 := extract_go₁_ascii s.toList hs 0 b ⟨e⟩
    have h2 := extract_go₂_ascii (s.toList.drop b) (hs.of_mem_drop b) b (e - b)
    rw [Nat.add_sub_cancel' hbe] at h2
    rw [Nat.zero_add] at h1
    rw [show (0 : String.Pos.Raw) = ⟨0⟩ from rfl, h1, h2]

theorem splitOnAux_ascii {sep : String} {c : Char} (hsep : sep.toList = [c])
    (hc : c.toNat < 128) (k : ℕ) :
    ∀ (b i : ℕ) (r : List String), s.toList.length - i = k → b ≤ i →
      i ≤ s.toList.length →
      (String.splitOnAux s sep ⟨b⟩ ⟨i⟩ 0 r).map String.toList =
        r.reverse.map String.toList ++
          List.splitOnPPrepend (· == c) (s.toList.drop i)
            ((s.toList.drop b).take (i - b)).reverse := by
  have hsa : IsAsciiList sep.toList := by
    rw [hsep]
    simpa [IsAsciiList] using hc
  have g0 : String.Pos.Raw.get sep 0 = c := by
    have := get_ascii hsa 0
    rw [hsep] at this
    simpa using this
  have n0 : String.Pos.Raw.next sep 0 = ⟨1⟩ := next_ascii hsa 0
  have e1 : String.Pos.Raw.atEnd sep ⟨1⟩ = true := by
    rw [atEnd_ascii hsa, hsep]
    rfl
  induction k with
  | zero =>
    intro b i r hk hbi hil
    have hi : i = s.toList.length := by omega
    rw [String.splitOnAux, ite_eq_left (by rw [atEnd_ascii hs]; simp; omega)]
    subst hi
    simp [extract_ascii hs b _ hbi]
  | succ k ih =>
    intro b i r hk hbi hil
    have hlt : i < s.toList.length := by omega
    rw [String.splitOnAux, ite_eq_right (by rw [atEnd_ascii hs]; simp; omega)]
    rw [get_ascii hs, g0, List.drop_eq_getElem_cons hlt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt, Option.getD_some]
    by_cases hch : (s.toList[i] == c) = true
    · rw [ite_eq_left hch, next_ascii hs, n0, ite_eq_left e1]
      have := ih (i + 1) (i + 1)
        (String.Pos.Raw.extract s ⟨b⟩ (String.Pos.Raw.unoffsetBy ⟨i + 1⟩ ⟨1⟩) :: r)
        (by omega) le_rfl hlt
      rw [this, List.splitOnPPrepend_cons_pos (p := (· == c)) hch]
      simp [String.Pos.Raw.unoffsetBy, extract_ascii hs b i hbi]
    · rw [ite_eq_right hch, String.Pos.Raw.unoffsetBy]
      rw [next_ascii hs, show String.Pos.Raw.byteIdx 0 = 0 from rfl, Nat.sub_zero,
        ih b (i + 1) r (by omega) (by omega) hlt,
        List.splitOnPPrepend_cons_neg (p := (· == c)) (by simpa using hch)]
      congr 2
      rw [show i + 1 - b = (i - b) + 1 by omega, List.take_add_one]
      simp [Nat.add_sub_cancel' hbi, List.getElem?_eq_getElem hlt]

/-- **`splitOn` on ASCII strings.** Splitting an ASCII string on a one-character ASCII
separator is `List.splitOn` on its characters. -/
theorem splitOn_ascii {sep : String} {c : Char} (hsep : sep.toList = [c]) (hc : c.toNat < 128) :
    (s.splitOn sep).map String.toList = s.toList.splitOn c := by
  have hne : (sep == "") = false := by
    cases h : sep == ""
    · rfl
    · have := congrArg String.toList (beq_iff_eq.mp h)
      simp_all
  rw [String.splitOn, hne, ite_eq_right (by simp)]
  have := splitOnAux_ascii hs hsep hc _ 0 0 [] rfl le_rfl (Nat.zero_le _)
  simp only [List.drop_zero, Nat.sub_zero, List.take_zero, List.reverse_nil, List.map_nil,
    List.nil_append] at this
  rw [List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend]
  exact this

end Raw

/-! ## The bytes of an ASCII source -/

theorem getElem!_toByteArray (l : List UInt8) (k : ℕ) : l.toByteArray[k]! = l[k]?.getD 0 := by
  by_cases h : k < l.length
  · rw [getElem!_pos l.toByteArray k (by simpa [List.size_toByteArray] using h)]
    simp [List.getElem_toByteArray, h]
  · rw [getElem!_neg l.toByteArray k (by simpa [List.size_toByteArray] using h)]
    simp [List.getElem?_eq_none (Nat.le_of_not_lt h)]
    rfl

theorem byteChar_toUInt8 {c : Char} (h : c.toNat < 128) : byteChar c.val.toUInt8 = c := by
  apply Char.ext
  apply UInt32.toNat_inj.mp
  have := toNat_byteChar c.val.toUInt8
  simp only [Char.toNat, UInt32.toNat_toUInt8] at this h
  rw [this, Nat.mod_eq_of_lt (by omega)]

/-- The span of all bytes of `bs`. -/
def fullSpan (bs : ByteArray) : ByteSpan := ⟨bs, 0, bs.size⟩

theorem chars_fullSpan {s : String} (h : IsAsciiList s.toList) :
    (fullSpan s.toUTF8).chars = s.toList := by
  apply List.ext_getElem
  · simp [length_chars, fullSpan, toByteArray_ascii h, List.size_toByteArray]
  · intro i _ h2
    simp only [chars, fullSpan, List.getElem_map, List.getElem_range', charAt]
    rw [String.toUTF8_eq_toByteArray, toByteArray_ascii h, getElem!_toByteArray]
    simp only [Nat.zero_add, Nat.one_mul]
    rw [List.getElem?_map, List.getElem?_eq_getElem h2, Option.map_some, Option.getD_some]
    exact byteChar_toUInt8 (h _ (List.getElem_mem h2))

theorem asciiBytes_toUTF8 {s : String} (h : IsAsciiList s.toList) : AsciiBytes s.toUTF8 := by
  intro k
  rw [String.toUTF8_eq_toByteArray, toByteArray_ascii h, getElem!_toByteArray,
    List.getElem?_map]
  cases hk : s.toList[k]? with
  | none => simp
  | some c =>
    have := h c (List.mem_of_getElem? hk)
    simp only [Option.map_some, Option.getD_some, UInt32.toNat_toUInt8]
    simp only [Char.toNat] at this
    omega

/-! ## Lines -/

theorem breakAt_eq (c : Char) (l : List Char) :
    DQASM.breakAt c l = (l.takeWhile (· != c), l.dropWhile (· != c)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => by_cases h : x = c <;> simp [DQASM.breakAt, h, ih]

/-- The number between the first `[` of a span and the next `]`. -/
def extractIndexB (s : ByteSpan) : Option ℕ :=
  let d := dropWhileB (· != '[') s
  if headB? d = some '[' then natOfDigitsB (takeWhileB (· != ']') (dropB 1 d)) else none

theorem extractIndexB_eq (s : ByteSpan) :
    extractIndexB s = OpenQASMParser.extractIndex (String.ofList s.chars) := by
  simp only [extractIndexB, OpenQASMParser.extractIndex, String.toList_ofList, headB?_eq,
    natOfDigitsB_eq, chars_takeWhileB, chars_dropB, chars_dropWhileB]
  generalize s.chars.dropWhile (· != '[') = l
  rcases l with _ | ⟨c, t⟩
  · simp
  · by_cases hc : c = '['
    · subst hc
      simp
    · simp [hc]

/-- The two bracketed numbers of a span with one `,`. -/
def extractTwoIndicesB (s : ByteSpan) : Option (ℕ × ℕ) :=
  match splitB ',' s with
  | [p1, p2] => do
    let i1 ← extractIndexB p1
    let i2 ← extractIndexB p2
    some (i1, i2)
  | _ => none

theorem splitOn_ofList_chars (c : Char) (hc : c.toNat < 128) (sep : String)
    (hsep : sep.toList = [c]) (s : ByteSpan) (h : AsciiBytes s.bs) :
    (String.ofList s.chars).splitOn sep = (splitB c s).map (String.ofList ∘ ByteSpan.chars) := by
  have := splitOn_ascii (s := String.ofList s.chars) (by simpa using isAsciiList_chars h)
    hsep hc
  rw [String.toList_ofList, ← chars_splitB] at this
  have := congrArg (List.map String.ofList) this
  simpa [List.map_map, Function.comp_def] using this

theorem extractTwoIndicesB_eq (s : ByteSpan) (h : AsciiBytes s.bs) :
    extractTwoIndicesB s = OpenQASMParser.extractTwoIndices (String.ofList s.chars) := by
  rw [OpenQASMParser.extractTwoIndices, splitOn_ofList_chars ',' (by decide) "," rfl s h,
    extractTwoIndicesB]
  rcases splitB ',' s with _ | ⟨a, _ | ⟨b, _ | ⟨x, t⟩⟩⟩ <;> simp [extractIndexB_eq]

/-- An operand `q[i]` with `i < n` at the head of a span, and the rest. The digits
are read by `String.toNat?`. -/
def parseQubitB (n : ℕ) (s : ByteSpan) : Option (Fin n × ByteSpan) :=
  if hasPrefixB s ['q', '['] then
    let rest := dropB 2 s
    let r := dropWhileB (· != ']') rest
    if headB? r = some ']' then
      match (String.ofList (takeWhileB (· != ']') rest).chars).toNat? with
      | some i => if h : i < n then some (⟨i, h⟩, dropB 1 r) else none
      | none => none
    else none
  else none

theorem parseQubitB_eq (n : ℕ) (s : ByteSpan) :
    (parseQubitB n s).map (Prod.map id ByteSpan.chars) = DQASM.parseQubit n s.chars := by
  simp only [parseQubitB, hasPrefixB_eq, headB?_eq, chars_dropWhileB, chars_takeWhileB,
    chars_dropB]
  rcases hl : s.chars with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [DQASM.parseQubit, List.isPrefixOf]
  · simp [DQASM.parseQubit, List.isPrefixOf]
  · by_cases hab : a = 'q' ∧ b = '['
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [List.isPrefixOf, BEq.rfl, Bool.and_self, ↓reduceIte, List.drop_succ_cons,
        List.drop_zero, DQASM.parseQubit, breakAt_eq]
      rcases hr : rest.dropWhile (· != ']') with _ | ⟨x, r⟩
      · simp
      · by_cases hx : x = ']'
        · subst hx
          simp only [List.head?_cons, ↓reduceIte]
          cases hn : (String.ofList (rest.takeWhile (· != ']'))).toNat? with
          | none => simp
          | some i =>
            by_cases hi : i < n
            · simp [hi, chars_dropB, chars_dropWhileB, hl, hr]
            · simp [hi]
        · simp [hx]
    · have hL : ['q', '['].isPrefixOf (a :: b :: rest) = false := by
        simp only [List.isPrefixOf]
        grind
      rw [hL]
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
      unfold DQASM.parseQubit
      split <;> simp_all

/-- The text after `rz(` of an `rz` statement: the angle text before `)` is decoded and
read by `OpenQASMParser.rzGateOf`, the operand by `parseQubitB`. -/
def parseRzB (n : ℕ) (s : ByteSpan) : Option (Gate n) :=
  let r := dropWhileB (· != ')') s
  if headB? r = some ')' then
    match parseQubitB n (dropWhileB (· == ' ') (dropB 1 r)) with
    | some (i, rest) =>
      if headB? rest = some ';' then OpenQASMParser.rzGateOf i (takeWhileB (· != ')') s).chars
      else none
    | none => none
  else none

theorem parseRzB_eq (n : ℕ) (s : ByteSpan) :
    parseRzB n s = OpenQASMParser.parseRz n s.chars := by
  have hq := parseQubitB_eq n (dropWhileB (· == ' ') (dropB 1 (dropWhileB (· != ')') s)))
  rw [chars_dropWhileB, chars_dropB, chars_dropWhileB] at hq
  simp only [parseRzB, OpenQASMParser.parseRz, breakAt_eq, headB?_eq, chars_dropWhileB,
    chars_takeWhileB]
  generalize parseQubitB n (dropWhileB (· == ' ') (dropB 1 (dropWhileB (· != ')') s))) = o at hq ⊢
  rcases hr : s.chars.dropWhile (· != ')') with _ | ⟨x, r⟩
  · simp
  · rw [hr] at hq
    by_cases hx : x = ')'
    · subst hx
      simp only [List.head?_cons, ↓reduceIte]
      simp only [List.drop_succ_cons, List.drop_zero] at hq
      rw [← hq]
      rcases o with _ | ⟨i, rest⟩
      · simp
      · simp only [Option.map_some, Prod.map, id]
        rcases rest.chars with _ | ⟨y, t⟩
        · simp
        · by_cases hy : y = ';'
          · subst hy
            simp
          · simp [hy]
    · simp [hx]

/-- One gate statement, read as `OpenQASMParser.parseLine` reads it. -/
def parseLineB (n : ℕ) (line : ByteSpan) : Option (Gate n) :=
  let s := dropWhileB (fun c => c == ' ' || c == '\t') line
  if isEmptyB s then none
  else if hasPrefixB s "OPENQASM".toList then none
  else if hasPrefixB s "include".toList then none
  else if hasPrefixB s "qubit".toList then none
  else if hasPrefixB s "//".toList then none
  else if hasPrefixB s "h ".toList || hasPrefixB s "h\t".toList then do
    let idx ← extractIndexB s
    if h : idx < n then some (.H ⟨idx, h⟩) else none
  else if hasPrefixB s "x ".toList || hasPrefixB s "x\t".toList then do
    let idx ← extractIndexB s
    if h : idx < n then some (.X ⟨idx, h⟩) else none
  else if hasPrefixB s "y ".toList || hasPrefixB s "y\t".toList then do
    let idx ← extractIndexB s
    if h : idx < n then some (.Y ⟨idx, h⟩) else none
  else if hasPrefixB s "z ".toList || hasPrefixB s "z\t".toList then do
    let idx ← extractIndexB s
    if h : idx < n then some (.Z ⟨idx, h⟩) else none
  else if hasPrefixB s "s ".toList || hasPrefixB s "s\t".toList then do
    let idx ← extractIndexB s
    if h : idx < n then some (.S ⟨idx, h⟩) else none
  else if hasPrefixB s "tdg ".toList || hasPrefixB s "tdg\t".toList then do
    let idx ← extractIndexB s
    if h : idx < n then some (.Tdg ⟨idx, h⟩) else none
  else if hasPrefixB s "t ".toList || hasPrefixB s "t\t".toList then do
    let idx ← extractIndexB s
    if h : idx < n then some (.T ⟨idx, h⟩) else none
  else if hasPrefixB s "cx ".toList || hasPrefixB s "cx\t".toList then do
    let (c, t) ← extractTwoIndicesB s
    if hc : c < n then
      if ht : t < n then some (.CNOT ⟨c, hc⟩ ⟨t, ht⟩)
      else none
    else none
  else if hasPrefixB s "cz ".toList || hasPrefixB s "cz\t".toList then do
    let (c, t) ← extractTwoIndicesB s
    if hc : c < n then
      if ht : t < n then some (.CZ ⟨c, hc⟩ ⟨t, ht⟩)
      else none
    else none
  else if hasPrefixB s "rz(".toList then parseRzB n (dropB 3 s)
  else none

/-- **Square.** On a span over ASCII bytes, `parseLineB` returns what
`OpenQASMParser.parseLine` returns on the string of its characters. -/
theorem parseLineB_eq (n : ℕ) (line : ByteSpan) (h : AsciiBytes line.bs) :
    parseLineB n line = OpenQASMParser.parseLine n (String.ofList line.chars) := by
  simp only [parseLineB, OpenQASMParser.parseLine, OpenQASMParser.stripLeading,
    OpenQASMParser.hasPrefix, hasPrefixB_eq, isEmptyB_eq, String.toList_ofList,
    extractIndexB_eq, extractTwoIndicesB_eq (dropWhileB (fun c => c == ' ' || c == '\t') line) h,
    parseRzB_eq, chars_dropB, chars_dropWhileB]

/-- Whether a span is one of the names `OpenQASMImport.isSkipped` skips. -/
def isSkippedB (nm : ByteSpan) : Bool :=
  eqLitB nm "OPENQASM".toList || eqLitB nm "include".toList || eqLitB nm "qreg".toList ||
    eqLitB nm "creg".toList || eqLitB nm "qubit".toList || eqLitB nm "bit".toList ||
    eqLitB nm "barrier".toList || eqLitB nm "measure".toList || eqLitB nm "gate".toList ||
    eqLitB nm "opaque".toList || eqLitB nm "".toList

theorem isSkippedB_eq (nm : ByteSpan) :
    isSkippedB nm = OpenQASMImport.isSkipped (String.ofList nm.chars) := by
  simp only [isSkippedB, OpenQASMImport.isSkipped, eqLitB_eq, ofList_beq]

/-- Every bracketed natural number from index `k` below `hi`, in the state `cur`
(the digits read since the last `[`) after the numbers `acc` (in reverse order). -/
def bracketGo (bs : ByteArray) (hi : ℕ) (k : ℕ) (cur : Option ℕ) (acc : List ℕ) : List ℕ :=
  if k < hi then
    let c := byteChar bs[k]!
    if c = '[' then bracketGo bs hi (k + 1) (some 0) acc
    else match cur with
      | none => bracketGo bs hi (k + 1) none acc
      | some v =>
        if c.isDigit then bracketGo bs hi (k + 1) (some (v * 10 + (c.toNat - '0'.toNat))) acc
        else if c = ']' then bracketGo bs hi (k + 1) none (v :: acc)
        else bracketGo bs hi (k + 1) none acc
  else acc.reverse
termination_by hi - k

theorem bracketGo_eq (bs : ByteArray) (hi k : ℕ) (cur : Option ℕ) (acc : List ℕ) :
    bracketGo bs hi k cur acc =
      OpenQASMImport.bracketIndices.go (⟨bs, k, hi⟩ : ByteSpan).chars cur acc := by
  fun_induction bracketGo bs hi k cur acc with
  | case6 k cur acc hk =>
    rw [chars_of_le (s := ⟨bs, k, hi⟩) (by simp; omega)]
    rfl
  | _ =>
    rw [chars_of_lt bs ‹_›, OpenQASMImport.bracketIndices.go.eq_def]
    simp_all +zetaDelta

/-- Every bracketed natural number of a span, left to right. -/
@[inline] def bracketB (s : ByteSpan) : List ℕ := bracketGo s.bs s.hi s.lo none []

theorem bracketB_eq (s : ByteSpan) :
    bracketB s = OpenQASMImport.bracketIndices (String.ofList s.chars) := by
  rw [bracketB, OpenQASMImport.bracketIndices, String.toList_ofList, bracketGo_eq]

/-- The span between the first `(` and the next `)`. -/
def parenArgB (s : ByteSpan) : Option ByteSpan :=
  let d := dropWhileB (· != '(') s
  if isEmptyB d then none else some (takeWhileB (· != ')') (dropB 1 d))

theorem parenArgB_eq (s : ByteSpan) :
    (parenArgB s).map ByteSpan.chars = OpenQASMImport.parenArg (String.ofList s.chars) := by
  simp only [parenArgB, OpenQASMImport.parenArg, String.toList_ofList, isEmptyB_eq,
    chars_dropWhileB]
  rcases hl : s.chars.dropWhile (· != '(') with _ | ⟨c, t⟩
  · simp
  · simp [chars_takeWhileB, chars_dropB, chars_dropWhileB, hl]

theorem splitCommas_go_eq (cs cur : List Char) (acc : List (List Char)) :
    OpenQASMImport.splitCommas.go cs cur acc =
      acc.reverse ++ List.splitOnPPrepend (· == ',') cs cur := by
  induction cs generalizing cur acc with
  | nil => simp [OpenQASMImport.splitCommas.go]
  | cons c rest ih =>
    by_cases hc : c = ','
    · subst hc
      simp [OpenQASMImport.splitCommas.go, ih, List.splitOnPPrepend_cons_pos]
    · simp [OpenQASMImport.splitCommas.go, hc, ih,
        List.splitOnPPrepend_cons_neg (p := (· == ',')) (by simpa using hc)]

theorem splitCommas_eq (cs : List Char) : OpenQASMImport.splitCommas cs = cs.splitOn ',' := by
  rw [OpenQASMImport.splitCommas, splitCommas_go_eq, List.splitOn_eq_splitOnP,
    List.splitOnP_eq_splitOnPPrepend]
  simp

theorem mapM_map {α β γ : Type} (f : α → β) (g : β → Option γ) (l : List α) :
    (l.map f).mapM g = l.mapM (g ∘ f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, ih]

/-- **The list lift of a square through `mapM`.** Lists related pointwise by `R`, and
functions sending `R`-related elements to equal results, have equal `mapM`. -/
theorem mapM_forall₂ {α β γ : Type} {R : α → β → Prop} {f : α → Option γ} {g : β → Option γ}
    (hfg : ∀ a b, R a b → f a = g b) {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) : as.mapM f = bs.mapM g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [List.mapM_cons, hfg _ _ hab, ih]

/-- The angles of a parenthesised argument list, the fields split by `,` by bytes and
each field decoded and read by `OpenQASMImport.angleOf`. -/
def parseAnglesB (s : ByteSpan) : Option (List PiLin) :=
  (parenArgB s).bind fun a => (splitB ',' a).mapM fun f => OpenQASMImport.angleOf f.chars

theorem parseAnglesB_eq (s : ByteSpan) :
    parseAnglesB s = OpenQASMImport.parseAngles (String.ofList s.chars) := by
  rw [parseAnglesB, OpenQASMImport.parseAngles, ← parenArgB_eq, Option.bind_map]
  congr 1
  funext a
  rw [Function.comp_apply, splitCommas_eq, ← chars_splitB, mapM_map]
  rfl

/-! ## Statements -/

/-- The statements of a line, read from its bytes as `OpenQASMImport.parseQ` reads the
line. The operation name is decoded only for a line `parseLineB` does not read. -/
def parseQB (n : ℕ) (line : ByteSpan) : Option (List (OpenQASMImport.QGate n)) :=
  let s := dropWhileB Char.isWhitespace line
  if hasPrefixB s "//".toList then some []
  else
    let nm := takeWhileB Char.isAlphanum (dropWhileB Char.isWhitespace s)
    if isSkippedB nm then some []
    else match parseLineB n s with
    | some g => (OpenQASMImport.ofGate? g).map ([·])
    | none =>
      (OpenQASMImport.parseQRest n (String.ofList nm.chars) (bracketB s)
        ((parenArgB s).map ByteSpan.chars) (parseAnglesB s)).map ([·])

/-- The gates a line denotes, read from its bytes: the lowering of `parseQB`. -/
def parseOpsB (n : ℕ) (line : ByteSpan) : Option (List (Gate n)) :=
  (parseQB n line).map (·.flatMap OpenQASMImport.lowerQ)

/-- The relation of a span over ASCII bytes to the string of its characters. -/
def paramLine : Param .map0 .map0 ByteSpan String where
  R s str := AsciiBytes s.bs ∧ String.ofList s.chars = str
  fwd := ⟨⟩
  bwd := ⟨⟩

/-- **Square.** `parseQB` realizes `OpenQASMImport.parseQ` along `paramLine`. -/
theorem parseQB_square (n : ℕ) :
    R_arrow paramLine (paramEqCod (Option (List (OpenQASMImport.QGate n)))) (parseQB n)
      (OpenQASMImport.parseQ n) := by
  rintro t _ ⟨h, rfl⟩
  change parseQB n t = OpenQASMImport.parseQ n (String.ofList t.chars)
  simp only [parseQB, OpenQASMImport.parseQ, OpenQASMImport.opName, trimAsciiStart_copy,
    String.toList_ofList, startsWith_eq, hasPrefixB_eq, chars_dropWhileB, chars_takeWhileB,
    isSkippedB_eq, parseLineB_eq n (dropWhileB Char.isWhitespace t) h, bracketB_eq,
    parenArgB_eq, parseAnglesB_eq]
  generalize String.ofList (List.takeWhile Char.isAlphanum
    (List.dropWhile Char.isWhitespace (List.dropWhile Char.isWhitespace t.chars))) = name
  generalize OpenQASMImport.bracketIndices
    (String.ofList (List.dropWhile Char.isWhitespace t.chars)) = idx
  generalize OpenQASMImport.parenArg
    (String.ofList (List.dropWhile Char.isWhitespace t.chars)) = arg
  generalize OpenQASMImport.parseAngles
    (String.ofList (List.dropWhile Char.isWhitespace t.chars)) = angs
  rfl

/-- **Square.** `parseOpsB` realizes `OpenQASMImport.parseOps` along `paramLine`. -/
theorem parseOpsB_square (n : ℕ) :
    R_arrow paramLine (paramEqCod (Option (List (Gate n)))) (parseOpsB n)
      (OpenQASMImport.parseOps n) := by
  rintro t _ ht
  change parseOpsB n t = OpenQASMImport.parseOps n _
  rw [parseOpsB, OpenQASMImport.parseOps, parseQB_square n ht]

/-- The relation of a byte array to the ASCII string it is the UTF-8 encoding of. -/
def paramSource : Param .map0 .map0 ByteArray String where
  R bs src := IsAsciiList src.toList ∧ bs = src.toUTF8
  fwd := ⟨⟩
  bwd := ⟨⟩

theorem bs_of_mem_splitGo (c : Char) (bs : ByteArray) (hi start k : ℕ) (acc : List ByteSpan)
    (hacc : ∀ x ∈ acc, x.bs = bs) : ∀ x ∈ splitGo c bs hi start k acc, x.bs = bs := by
  fun_induction splitGo c bs hi start k acc with
  | case1 start k acc _ _ ih => exact ih (by simp_all)
  | case2 start k acc _ _ ih => exact ih hacc
  | case3 start k acc _ =>
    intro x hx
    rw [List.mem_reverse, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact hacc x hx

/-- **Square.** The lines of a source, split by scanning for the newline byte, are
related by `paramLine` to the lines `String.splitOn` returns. -/
theorem linesB_square (bs : ByteArray) (src : String) (h : paramSource.R bs src) :
    List.Forall₂ paramLine.R (splitB '\n' (fullSpan bs)) (src.splitOn "\n") := by
  obtain ⟨ha, rfl⟩ := h
  have hb := asciiBytes_toUTF8 ha
  have hl := splitOn_ascii ha (sep := "\n") (c := '\n') rfl (by decide)
  rw [← chars_fullSpan ha, ← chars_splitB] at hl
  have hs : src.splitOn "\n" =
      (splitB '\n' (fullSpan src.toUTF8)).map (String.ofList ∘ ByteSpan.chars) := by
    have := congrArg (List.map String.ofList) hl
    simpa [List.map_map, Function.comp_def] using this
  rw [hs, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun x hx => ⟨?_, rfl⟩
  rw [bs_of_mem_splitGo '\n' _ _ _ _ [] (by simp) x hx]
  exact hb

/-- The gates of a whole file read from its bytes, `none` if any line is unrecognised. -/
def importGatesB (n : ℕ) (bs : ByteArray) : Option (List (Gate n)) :=
  ((splitB '\n' (fullSpan bs)).mapM (parseOpsB n)).map List.flatten

/-- **The circuit a file denotes**, read from its bytes; `none` if any line is
unrecognised. -/
def importQASMB (n : ℕ) (bs : ByteArray) : Option (Circuit n) :=
  (importGatesB n bs).map Circuit.ofList

/-- **Square.** `importGatesB` realizes `OpenQASMImport.importGates` along `paramSource`. -/
theorem importGatesB_square (n : ℕ) :
    R_arrow paramSource (paramEqCod (Option (List (Gate n)))) (importGatesB n)
      (OpenQASMImport.importGates n) := by
  intro bs src h
  change importGatesB n bs = OpenQASMImport.importGates n src
  rw [importGatesB, OpenQASMImport.importGates,
    mapM_forall₂ (parseOpsB_square n) (linesB_square bs src h)]

/-- The statements of a whole file read from its bytes, `none` if any line is
unrecognised. -/
def importQB (n : ℕ) (bs : ByteArray) : Option (List (OpenQASMImport.QGate n)) :=
  ((splitB '\n' (fullSpan bs)).mapM (parseQB n)).map List.flatten

/-- **Square.** `importQB` realizes `OpenQASMImport.importQ` along `paramSource`. -/
theorem importQB_square (n : ℕ) :
    R_arrow paramSource (paramEqCod (Option (List (OpenQASMImport.QGate n)))) (importQB n)
      (OpenQASMImport.importQ n) := by
  intro bs src h
  change importQB n bs = OpenQASMImport.importQ n src
  rw [importQB, OpenQASMImport.importQ,
    mapM_forall₂ (parseQB_square n) (linesB_square bs src h)]

/-- **Square.** `importQASMB` realizes `OpenQASMImport.importQASM` along `paramSource`. -/
theorem importQASMB_square (n : ℕ) :
    R_arrow paramSource (paramEqCod (Option (Circuit n))) (importQASMB n)
      (OpenQASMImport.importQASM n) := by
  intro bs src h
  change importQASMB n bs = OpenQASMImport.importQASM n src
  rw [importQASMB, OpenQASMImport.importQASM, importGatesB_square n h]

/-- **The byte importer is the importer.** On the UTF-8 bytes of a source whose
characters are ASCII, `importQASMB` returns what `OpenQASMImport.importQASM` returns. -/
theorem importQASMB_eq (n : ℕ) (src : String) (h : ∀ c ∈ src.toList, c.toNat < 128) :
    importQASMB n src.toUTF8 = OpenQASMImport.importQASM n src :=
  importQASMB_square n ⟨h, rfl⟩

/-- On the UTF-8 bytes of a source whose characters are ASCII, `importQB` returns the
statements `OpenQASMImport.importQ` reads. -/
theorem importQB_eq (n : ℕ) (src : String) (h : ∀ c ∈ src.toList, c.toNat < 128) :
    importQB n src.toUTF8 = OpenQASMImport.importQ n src :=
  importQB_square n ⟨h, rfl⟩

end CatCrypt.Quantum.OpenQASMBytes
