/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QrunchBasis
public import CatCrypt.Quantum.OpenQASMBytes
public import CatCrypt.Quantum.OpenQASMDiscrete

/-!
# OpenQASM 2 export of gate lists

`exportQASM l` is the OpenQASM 2 program of a gate list `l : List (Gate n)` over the basis
`{rx, ry, cx, p}` of `qelib1.inc`, with exact angles: the statements `QrunchBasis.toQelib`
translates `l` into, printed by `QrunchBasis.printQelib`. `exportPhase l` is the exact global
phase of the translation.

The OpenQASM 2 reader `OpenQASMImport.importQ` reads the printed text back as the same
statements (`importQ_printQelib`), so the `qelib1.inc` matrix of what is read is the matrix
of `l` up to the exact phase.

`exportChecked` returns the text and the phase for a list without the real-angle `Rz`, and
`none` otherwise.

## Main results

* `qelibListMatrix_exportQ` — the statements of the export realise `listMatrix l` up to
  `exp (i · exportPhase l)`.
* `importQ_printQelib` — reading a printed list of `rx`, `ry`, `cx`, `p` statements returns
  that list.
* `importQ_exportQASM`, `qelibListMatrix_importQ_exportQASM` — reading the exported text
  gives the statements of the export, whose `qelib1.inc` matrix is
  `exp (i · exportPhase l) • listMatrix l`.
* `listMatrix_importGates_exportQASM` — the gate list the importer lowers the exported text
  to has the matrix `exp (i · (listPhase + exportPhase l)) • listMatrix l`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.Qelib
open CatCrypt.Quantum.QrunchBasis
open CatCrypt.Quantum.OpenQASMBytes
open CatCrypt.Quantum.QFT (listMatrix)

namespace CatCrypt.Quantum.QrunchExport

variable {n : ℕ}

/-! ## The export -/

/-- The statements of the export of a gate list: `toQelib`'s translation. -/
def exportQ (l : List (Gate n)) : List (QGate n) := (toQelib l).1

/-- The exact global phase of the export of a gate list. -/
def exportPhase (l : List (Gate n)) : PiLin := (toQelib l).2

/-- The OpenQASM 2 program of a gate list over `{rx, ry, cx, p}`. -/
def exportQASM (l : List (Gate n)) : String := printQelib n (exportQ l)

instance : DecidablePred (NoRz (n := n)) := fun g => by
  cases g <;> unfold NoRz <;> infer_instance

/-- The text and phase of the export of a gate list without the real-angle `Rz`; `none` for a
    list with one, which `toQelib` does not translate. -/
def exportChecked (l : List (Gate n)) : Option (String × PiLin) :=
  if l.all (fun g => decide (NoRz g)) then some (exportQASM l, exportPhase l) else none

/-- The statements of the export realise the gate list up to the exact phase. -/
theorem qelibListMatrix_exportQ (l : List (Gate n)) (hl : ∀ g ∈ l, NoRz g) :
    qelibListMatrix (exportQ l) = Complex.exp (Complex.I * (exportPhase l).toReal) • listMatrix l :=
  qelibListMatrix_toQelib l hl

/-! ## The statements `toQelib` emits -/

/-- A statement of the basis `{rx, ry, cx, p}`. -/
def Emitted : QGate n → Prop
  | .rx _ _ | .ry _ _ | .cx _ _ | .p _ _ => True
  | _ => False

/-- `gateQ` emits statements of the basis. -/
theorem emitted_gateQ (g : Gate n) : ∀ s ∈ (gateQ g).1, Emitted s := by
  cases g <;> simp only [gateQ] <;> grind [Emitted]

/-- `toQelib` emits statements of the basis. -/
theorem emitted_toQelib (l : List (Gate n)) : ∀ s ∈ (toQelib l).1, Emitted s := by
  fun_induction toQelib l with
  | case1 => simp
  | case2 => grind [Emitted]
  | case3 => grind [emitted_gateQ]
  | case4 => grind [Emitted]
  | case5 => grind [emitted_gateQ]
  | case6 => grind [emitted_gateQ]

/-! ## Characters of a printed statement -/

/-- A decimal digit is an ASCII character. -/
theorem ascii_of_isDigit {c : Char} (h : c.isDigit = true) : c.toNat < 128 := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  grind only [usr Char.valid, Char.toNat_val, Char.le_def]

/-- The characters of a printed natural number are ASCII. -/
theorem ascii_toDigits (k : ℕ) : ∀ c ∈ Nat.toDigits 10 k, c.toNat < 128 := fun _ hc =>
  ascii_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

/-- The characters of a printed exact angle are ASCII. -/
theorem ascii_piLin (p : PiLin) : ∀ c ∈ p.toQASM.toList, c.toNat < 128 := by
  intro c hc
  by_contra h
  have hne : ∀ d : Char, d.toNat < 128 → c ≠ d := fun d hd hcd => h (hcd ▸ hd)
  have hd : c.isDigit = false := by
    cases hc' : c.isDigit
    · rfl
    · exact absurd (ascii_of_isDigit hc') h
  exact DQASM.not_mem_piLin p c hd (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide))
    (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) hc

/-- The characters of a printed exact angle are digits and `-`, `*`, `p`, `i`, `/`, `+`. -/
theorem mem_piLin (p : PiLin) {c : Char} (hc : c ∈ p.toQASM.toList) :
    c.isDigit = true ∨ c ∈ ['-', '*', 'p', 'i', '/', '+'] := by
  by_contra h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, Bool.not_eq_true] at h
  obtain ⟨hd, h1, h2, h3, h4, h5, h6⟩ := h
  exact DQASM.not_mem_piLin p c hd h1 h2 h3 h4 h5 h6 hc

/-- A character other than a digit and `-`, `*`, `p`, `i`, `/`, `+` is not in a printed
    exact angle. -/
theorem not_mem_piLin_of (p : PiLin) (c : Char)
    (h : ¬ (c.isDigit = true ∨ c ∈ ['-', '*', 'p', 'i', '/', '+'])) : c ∉ p.toQASM.toList :=
  fun hc => h (mem_piLin p hc)

/-- A character that is not a digit is not in a printed natural number. -/
theorem not_mem_toDigits_of (k : ℕ) (c : Char) (h : c.isDigit = false) :
    c ∉ Nat.toDigits 10 k := fun hc => by
  simp [Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc] at h

/-- The characters of a printed `p` statement. -/
theorem toList_toQASM_p (q : Fin n) (a : PiLin) :
    (QrunchBasis.QGate.toQASM (.p q a)).toList =
      'p' :: '(' :: (a.toQASM.toList ++ ')' :: ' ' :: 'q' :: '[' ::
        (Nat.toDigits 10 q.val ++ [']', ';'])) := by
  simp [QrunchBasis.QGate.toQASM, toString, Nat.repr_eq_ofList_toDigits]

/-- The characters of a printed `cx` statement. -/
theorem toList_toQASM_cx (c t : Fin n) :
    (QrunchBasis.QGate.toQASM (.cx c t)).toList =
      'c' :: 'x' :: ' ' :: 'q' :: '[' :: (Nat.toDigits 10 c.val ++ ']' :: ',' :: 'q' :: '[' ::
        (Nat.toDigits 10 t.val ++ [']', ';'])) := by
  simp [QrunchBasis.QGate.toQASM, toString, Nat.repr_eq_ofList_toDigits]

/-- The characters of a printed `rx` statement. -/
theorem toList_toQASM_rx (q : Fin n) (a : PiLin) :
    (QrunchBasis.QGate.toQASM (.rx q a)).toList =
      'r' :: 'x' :: '(' :: (a.toQASM.toList ++ ')' :: ' ' :: 'q' :: '[' ::
        (Nat.toDigits 10 q.val ++ [']', ';'])) := by
  simp [QrunchBasis.QGate.toQASM, toString, Nat.repr_eq_ofList_toDigits]

/-- The characters of a printed `ry` statement. -/
theorem toList_toQASM_ry (q : Fin n) (a : PiLin) :
    (QrunchBasis.QGate.toQASM (.ry q a)).toList =
      'r' :: 'y' :: '(' :: (a.toQASM.toList ++ ')' :: ' ' :: 'q' :: '[' ::
        (Nat.toDigits 10 q.val ++ [']', ';'])) := by
  simp [QrunchBasis.QGate.toQASM, toString, Nat.repr_eq_ofList_toDigits]

/-! ## Reading a line -/

/-- A string whose first character is not whitespace is its own `trimAsciiStart`. -/
theorem trimAsciiStart_copy_of_cons {s : String} {c : Char} {r : List Char}
    (h : s.toList = c :: r) (hc : c.isWhitespace = false) : s.trimAsciiStart.copy = s := by
  rw [trimAsciiStart_copy, h, List.dropWhile_cons_of_neg (by simp [hc]), ← h,
    String.ofList_toList]

/-- `bracketIndices` passes over a text without `[` outside brackets. -/
theorem bracketIndices_go_skip (t r : List Char) (acc : List ℕ) (ht : '[' ∉ t) :
    bracketIndices.go (t ++ r) none acc = bracketIndices.go r none acc := by
  induction t with
  | nil => rfl
  | cons c t ih => grind [bracketIndices.go]

/-- `bracketIndices` reads the digits of a bracket. -/
theorem bracketIndices_go_digits (ds r : List Char) (v : ℕ) (acc : List ℕ)
    (hd : ∀ c ∈ ds, c.isDigit = true) :
    bracketIndices.go (ds ++ ']' :: r) (some v) acc =
      bracketIndices.go r none
        (ds.foldl (fun v c => v * 10 + (c.toNat - '0'.toNat)) v :: acc) := by
  induction ds generalizing v with
  | nil => simp [bracketIndices.go]
  | cons c ds ih =>
    have hc := hd c (by simp)
    have hc' : c ≠ '[' := by rintro rfl; simp at hc
    simp only [List.cons_append, bracketIndices.go, hc', ↓reduceIte, hc, List.foldl_cons]
    exact ih _ (fun d h => hd d (by simp [h]))

/-- The digits of a printed natural number fold back to it. -/
theorem foldl_toDigits (k : ℕ) :
    (Nat.toDigits 10 k).foldl (fun v c => v * 10 + (c.toNat - '0'.toNat)) 0 = k := by
  have hv := Nat.ofDigitChars_ten_toDigits (n := k)
  rw [Nat.ofDigitChars_eq_foldl] at hv
  simpa [mul_comm] using hv

/-- The bracketed index of a one-qubit statement with an angle. -/
theorem bracketIndices_angle (pre : List Char) (a : PiLin) (k : ℕ) (hpre : '[' ∉ pre) :
    bracketIndices.go (pre ++ (a.toQASM.toList ++ ')' :: ' ' :: 'q' :: '[' ::
        (Nat.toDigits 10 k ++ [']', ';']))) none [] = [k] := by
  have ha : '[' ∉ a.toQASM.toList := not_mem_piLin_of a '[' (by decide)
  rw [bracketIndices_go_skip _ _ _ hpre, bracketIndices_go_skip _ _ _ ha]
  simp only [bracketIndices.go]
  rw [bracketIndices_go_digits _ _ _ _
    (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc), foldl_toDigits]
  rfl

/-- The angle text of a one-qubit statement. -/
theorem parenArg_angle (s : String) (pre : List Char) (a : PiLin) (k : ℕ)
    (hs : s.toList = pre ++ '(' :: (a.toQASM.toList ++ ')' :: ' ' :: 'q' :: '[' ::
        (Nat.toDigits 10 k ++ [']', ';'])))
    (hpre : '(' ∉ pre) : parenArg s = some a.toQASM.toList := by
  have ha : ')' ∉ a.toQASM.toList := not_mem_piLin_of a ')' (by decide)
  have hp : ∀ c ∈ pre, (c != '(') = true := fun c hc =>
    bne_iff_ne.mpr (fun h => hpre (h ▸ hc))
  have hq : ∀ c ∈ a.toQASM.toList, (c != ')') = true := fun c hc =>
    bne_iff_ne.mpr (fun h => ha (h ▸ hc))
  rw [parenArg, hs, List.dropWhile_append_of_pos hp]
  simp [List.takeWhile_append_of_pos hq]

/-- A printed exact angle reads back as that angle. -/
theorem angleOf_toQASM (a : PiLin) : angleOf a.toQASM.toList = some a := by
  have hf : a.toQASM.toList.filter (· != ' ') = a.toQASM.toList :=
    List.filter_eq_self.mpr fun c hc => by
      rcases mem_piLin a hc with h | h
      · exact bne_iff_ne.mpr (by rintro rfl; simp at h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp [angleOf, hf, OpenQASMParser.parseAngleLin, DQASM.parseAngle_toQASM]

/-- A printed `p` statement reads back as itself. -/
theorem parseQ_p (q : Fin n) (a : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.p q a)) = some [.p q a] := by
  have hl := toList_toQASM_p q a
  have ht := trimAsciiStart_copy_of_cons hl (by decide)
  have hname : opName (QrunchBasis.QGate.toQASM (.p q a)) = "p" := by
    rw [opName, ht, hl, List.takeWhile_cons_of_pos (by decide),
      List.takeWhile_cons_of_neg (by decide)]
  have hline : OpenQASMParser.parseLine n (QrunchBasis.QGate.toQASM (.p q a)) = none := by
    simp [OpenQASMParser.parseLine, OpenQASMParser.stripLeading, OpenQASMParser.hasPrefix, hl]
  have hidx : bracketIndices (QrunchBasis.QGate.toQASM (.p q a)) = [q.val] := by
    rw [bracketIndices, hl]
    exact bracketIndices_angle ['p', '('] a q.val (by decide)
  have harg := parenArg_angle _ ['p'] a q.val hl (by decide)
  simp only [parseQ, ht, startsWith_eq, hl, hname, hline, hidx, harg]
  simp [isSkipped, parseQRest, angleOf_toQASM]

/-- A field list without `,` is one field. -/
theorem splitCommas_go_of_not_mem (cs cur : List Char) (acc : List (List Char))
    (h : ',' ∉ cs) : splitCommas.go cs cur acc = ((cur.reverse ++ cs) :: acc).reverse := by
  induction cs generalizing cur with
  | nil => simp [splitCommas.go]
  | cons c cs ih => grind [splitCommas.go]

/-- The angle list of a one-qubit statement with one angle. -/
theorem parseAngles_angle (s : String) (pre : List Char) (a : PiLin) (k : ℕ)
    (hs : s.toList = pre ++ '(' :: (a.toQASM.toList ++ ')' :: ' ' :: 'q' :: '[' ::
        (Nat.toDigits 10 k ++ [']', ';'])))
    (hpre : '(' ∉ pre) : parseAngles s = some [a] := by
  have hc : ',' ∉ a.toQASM.toList := not_mem_piLin_of a ',' (by decide)
  simp [parseAngles, parenArg_angle s pre a k hs hpre, splitCommas,
    splitCommas_go_of_not_mem _ _ _ hc, angleOf_toQASM]

/-- A printed `rx` statement reads back as itself. -/
theorem parseQ_rx (q : Fin n) (a : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.rx q a)) = some [.rx q a] := by
  have hl := toList_toQASM_rx q a
  have ht := trimAsciiStart_copy_of_cons hl (by decide)
  have hname : opName (QrunchBasis.QGate.toQASM (.rx q a)) = "rx" := by
    rw [opName, ht, hl, List.takeWhile_cons_of_pos (by decide),
      List.takeWhile_cons_of_pos (by decide), List.takeWhile_cons_of_neg (by decide)]
  have hline : OpenQASMParser.parseLine n (QrunchBasis.QGate.toQASM (.rx q a)) = none := by
    simp [OpenQASMParser.parseLine, OpenQASMParser.stripLeading, OpenQASMParser.hasPrefix, hl]
  have hidx : bracketIndices (QrunchBasis.QGate.toQASM (.rx q a)) = [q.val] := by
    rw [bracketIndices, hl]
    exact bracketIndices_angle ['r', 'x', '('] a q.val (by decide)
  have harg := parenArg_angle _ ['r', 'x'] a q.val hl (by decide)
  have hangs := parseAngles_angle _ ['r', 'x'] a q.val hl (by decide)
  simp only [parseQ, ht, startsWith_eq, hl, hname, hline, hidx, harg, hangs]
  simp [isSkipped, parseQRest]

/-- A printed `ry` statement reads back as itself. -/
theorem parseQ_ry (q : Fin n) (a : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.ry q a)) = some [.ry q a] := by
  have hl := toList_toQASM_ry q a
  have ht := trimAsciiStart_copy_of_cons hl (by decide)
  have hname : opName (QrunchBasis.QGate.toQASM (.ry q a)) = "ry" := by
    rw [opName, ht, hl, List.takeWhile_cons_of_pos (by decide),
      List.takeWhile_cons_of_pos (by decide), List.takeWhile_cons_of_neg (by decide)]
  have hline : OpenQASMParser.parseLine n (QrunchBasis.QGate.toQASM (.ry q a)) = none := by
    simp [OpenQASMParser.parseLine, OpenQASMParser.stripLeading, OpenQASMParser.hasPrefix, hl]
  have hidx : bracketIndices (QrunchBasis.QGate.toQASM (.ry q a)) = [q.val] := by
    rw [bracketIndices, hl]
    exact bracketIndices_angle ['r', 'y', '('] a q.val (by decide)
  have harg := parenArg_angle _ ['r', 'y'] a q.val hl (by decide)
  have hangs := parseAngles_angle _ ['r', 'y'] a q.val hl (by decide)
  simp only [parseQ, ht, startsWith_eq, hl, hname, hline, hidx, harg, hangs]
  simp [isSkipped, parseQRest]

/-- The index of a bracket `[k]` at the head of a text. -/
theorem extractIndex_ofList (pre r : List Char) (k : ℕ) (hpre : '[' ∉ pre) :
    OpenQASMParser.extractIndex (String.ofList (pre ++ '[' :: (Nat.toDigits 10 k ++ ']' :: r)))
      = some k := by
  have hp : ∀ c ∈ pre, (c != '[') = true := fun c hc =>
    bne_iff_ne.mpr (fun h => hpre (h ▸ hc))
  have hd : ∀ c ∈ Nat.toDigits 10 k, (c != ']') = true := fun c hc =>
    bne_iff_ne.mpr (fun h => not_mem_toDigits_of k ']' (by decide) (h ▸ hc))
  rw [OpenQASMParser.extractIndex, String.toList_ofList, List.dropWhile_append_of_pos hp]
  simp [List.takeWhile_append_of_pos hd, OpenQASMParser.natOfDigits_toDigits]

/-- A printed `cx` statement reads back as itself. -/
theorem parseQ_cx (c t : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.cx c t)) = some [.cx c t] := by
  have hl := toList_toQASM_cx c t
  have ht := trimAsciiStart_copy_of_cons hl (by decide)
  have hname : opName (QrunchBasis.QGate.toQASM (.cx c t)) = "cx" := by
    rw [opName, ht, hl, List.takeWhile_cons_of_pos (by decide),
      List.takeWhile_cons_of_pos (by decide), List.takeWhile_cons_of_neg (by decide)]
  have hstrip : OpenQASMParser.stripLeading (QrunchBasis.QGate.toQASM (.cx c t)) =
      QrunchBasis.QGate.toQASM (.cx c t) := by
    rw [OpenQASMParser.stripLeading, hl, List.dropWhile_cons_of_neg (by decide), ← hl,
      String.ofList_toList]
  have hascii : IsAsciiList (QrunchBasis.QGate.toQASM (.cx c t)).toList := by
    rw [hl]
    intro x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | hx | rfl | rfl | rfl | rfl | hx | rfl | rfl
    all_goals first | decide | exact ascii_toDigits _ _ hx
  have hcomma : ',' ∉ Nat.toDigits 10 c.val ∧ ',' ∉ Nat.toDigits 10 t.val :=
    ⟨not_mem_toDigits_of _ ',' (by decide), not_mem_toDigits_of _ ',' (by decide)⟩
  have hsplit : (QrunchBasis.QGate.toQASM (.cx c t)).splitOn "," =
      [String.ofList ('c' :: 'x' :: ' ' :: 'q' :: '[' :: (Nat.toDigits 10 c.val ++ [']'])),
        String.ofList ('q' :: '[' :: (Nat.toDigits 10 t.val ++ [']', ';']))] := by
    have h := congrArg (List.map String.ofList) (splitOn_ascii hascii (sep := ",") (c := ',')
      rfl (by decide))
    simp only [List.map_map, Function.comp_def, String.ofList_toList, List.map_id'] at h
    rw [h, hl, show 'c' :: 'x' :: ' ' :: 'q' :: '[' :: (Nat.toDigits 10 c.val ++ ']' :: ',' ::
        'q' :: '[' :: (Nat.toDigits 10 t.val ++ [']', ';'])) =
        ('c' :: 'x' :: ' ' :: 'q' :: '[' :: (Nat.toDigits 10 c.val ++ [']'])) ++ ',' ::
          ('q' :: '[' :: (Nat.toDigits 10 t.val ++ [']', ';'])) by simp,
      List.splitOn_append_cons_self_of_not_mem (by simp [hcomma.1]),
      List.splitOn_eq_singleton (by simp [hcomma.2])]
    rfl
  have hext : OpenQASMParser.extractTwoIndices (QrunchBasis.QGate.toQASM (.cx c t)) =
      some (c.val, t.val) := by
    rw [OpenQASMParser.extractTwoIndices, hsplit]
    have h1 := extractIndex_ofList ['c', 'x', ' ', 'q'] [] c.val (by decide)
    have h2 := extractIndex_ofList ['q'] [';'] t.val (by decide)
    simp only [List.cons_append, List.nil_append] at h1 h2
    simp only [h1, h2]
    rfl
  have hline : OpenQASMParser.parseLine n (QrunchBasis.QGate.toQASM (.cx c t)) =
      some (.CNOT c t) := by
    simp only [OpenQASMParser.parseLine, hstrip]
    simp [OpenQASMParser.hasPrefix, hl, hext]
  simp only [parseQ, ht, startsWith_eq, hl, hname, hline]
  simp [isSkipped, ofGate?]

/-- A printed statement of the basis reads back as itself. -/
theorem parseQ_toQASM (g : QGate n) (hg : Emitted g) :
    parseQ n (QrunchBasis.QGate.toQASM g) = some [g] := by
  cases g <;> simp only [Emitted] at hg
  · exact parseQ_rx _ _
  · exact parseQ_ry _ _
  · exact parseQ_p _ _
  · exact parseQ_cx _ _

/-- The characters of a printed statement of the basis are ASCII and not a newline. -/
theorem ascii_toQASM (g : QGate n) (hg : Emitted g) :
    ∀ c ∈ (QrunchBasis.QGate.toQASM g).toList, c.toNat < 128 ∧ c ≠ '\n' := by
  have hpi : ∀ a : PiLin, ∀ c ∈ a.toQASM.toList, c.toNat < 128 ∧ c ≠ '\n' := fun a c hc =>
    ⟨ascii_piLin a c hc, fun h => not_mem_piLin_of a '\n' (by decide) (h ▸ hc)⟩
  have hdig : ∀ k : ℕ, ∀ c ∈ Nat.toDigits 10 k, c.toNat < 128 ∧ c ≠ '\n' := fun k c hc =>
    ⟨ascii_toDigits k c hc, fun h => not_mem_toDigits_of k '\n' (by decide) (h ▸ hc)⟩
  cases g <;> simp only [Emitted] at hg
  all_goals simp only [toList_toQASM_rx, toList_toQASM_ry, toList_toQASM_p, toList_toQASM_cx,
    List.forall_mem_cons, List.forall_mem_append]
  all_goals and_intros
  all_goals first
    | decide
    | exact hpi _
    | exact hdig _

/-- The header lines of `printQelib`. -/
def headerLines (n : ℕ) : List String :=
  ["OPENQASM 2.0;", "include \"qelib1.inc\";", s!"qreg q[{n}];"]

/-- The header lines carry no statement. -/
theorem mapM_parseQ_header :
    (headerLines n).mapM (parseQ n) = some [[], [], []] := by
  simp [headerLines, parseQ, opName, isSkipped, trimAsciiStart_copy, startsWith_eq, toString,
    Nat.repr_eq_ofList_toDigits]

/-- The characters of a header line are ASCII and not a newline. -/
theorem ascii_headerLines : ∀ s ∈ headerLines n, ∀ c ∈ s.toList, c.toNat < 128 ∧ c ≠ '\n' := by
  have hdig : ∀ c ∈ Nat.toDigits 10 n, c.toNat < 128 ∧ c ≠ '\n' := fun c hc =>
    ⟨ascii_toDigits n c hc, fun h => not_mem_toDigits_of n '\n' (by decide) (h ▸ hc)⟩
  simp only [headerLines, List.forall_mem_cons]
  refine ⟨by decide, by decide, ?_, fun _ h => absurd h List.not_mem_nil⟩
  simp only [toString, Nat.repr_eq_ofList_toDigits, String.toList_append, String.toList_ofList,
    List.forall_mem_append]
  exact ⟨⟨by decide, hdig⟩, by decide⟩

/-- Appending the separator to an intercalation is intercalating one more, empty, element. -/
theorem intercalate_append_sep {α : Type} (sep : List α) (ls : List (List α)) (h : ls ≠ []) :
    sep.intercalate ls ++ sep = sep.intercalate (ls ++ [[]]) := by
  induction ls with
  | nil => simp at h
  | cons x xs ih => cases xs <;> simp_all [List.intercalate]

/-- An element of an intercalation is in the separator or in one of the lists. -/
theorem mem_intercalate_of {α : Type} {sep : List α} {ls : List (List α)} {x : α}
    (h : x ∈ sep.intercalate ls) : x ∈ sep ∨ ∃ l ∈ ls, x ∈ l := by
  induction ls with
  | nil => simp at h
  | cons a ls ih =>
    cases ls with
    | nil => simp_all
    | cons b ls =>
      rw [List.intercalate_cons_cons] at h
      grind

/-- The lines of a printed statement list of the basis. -/
theorem splitOn_printQelib (l : List (QGate n)) (hl : ∀ g ∈ l, Emitted g) :
    (printQelib n l).splitOn "\n" = headerLines n ++ l.map QrunchBasis.QGate.toQASM ++ [""] := by
  have hlines : ∀ s ∈ headerLines n ++ l.map QrunchBasis.QGate.toQASM,
      ∀ c ∈ s.toList, c.toNat < 128 ∧ c ≠ '\n' := by
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact ascii_headerLines s h
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
      exact ascii_toQASM g (hl g hg)
  have hto : (printQelib n l).toList =
      ['\n'].intercalate ((headerLines n ++ l.map QrunchBasis.QGate.toQASM ++ [""]).map
        String.toList) := by
    rw [printQelib, String.toList_append, String.toList_intercalate,
      intercalate_append_sep _ _ (by simp)]
    simp [headerLines]
  have hall : ∀ s ∈ headerLines n ++ l.map QrunchBasis.QGate.toQASM ++ [""],
      ∀ c ∈ s.toList, c.toNat < 128 ∧ c ≠ '\n' := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hlines s hs
    · rw [List.mem_singleton.mp hs]
      simp
  have hascii : IsAsciiList (printQelib n l).toList := by
    rw [hto]
    intro c hc
    rcases mem_intercalate_of hc with h | ⟨w, hw, hc⟩
    · rw [List.mem_singleton.mp h]
      decide
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
      exact (hall s hs c hc).1
  have h := congrArg (List.map String.ofList) (splitOn_ascii hascii (sep := "\n") (c := '\n')
    rfl (by decide))
  simp only [List.map_map, Function.comp_def, String.ofList_toList, List.map_id'] at h
  rw [h, hto, List.splitOn_intercalate]
  · simp
  · intro w hw hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
    exact (hall s hs _ hc).2 rfl
  · simp

/-- **Reading a printed statement list** of the basis `{rx, ry, cx, p}` returns that list. -/
theorem importQ_printQelib (l : List (QGate n)) (hl : ∀ g ∈ l, Emitted g) :
    importQ n (printQelib n l) = some l := by
  have hs : (l.map QrunchBasis.QGate.toQASM).mapM (parseQ n) = some (l.map ([·])) := by
    induction l with
    | nil => rfl
    | cons g l ih =>
      simp [List.mapM_cons, parseQ_toQASM g (hl g (by simp)), ih (fun g h => hl g (by simp [h]))]
  have he : ([""] : List String).mapM (parseQ n) = some [[]] := by
    simp [parseQ, opName, isSkipped, trimAsciiStart_copy, startsWith_eq]
  rw [importQ, splitOn_printQelib l hl, List.mapM_append, List.mapM_append, mapM_parseQ_header,
    hs, he]
  have hf : (l.map fun x => [x]).flatten = l := by
    clear hl hs
    induction l <;> simp_all
  simp [hf]

/-! ## Reading the export -/

/-- Reading the exported text returns the statements of the export. -/
theorem importQ_exportQASM (l : List (Gate n)) : importQ n (exportQASM l) = some (exportQ l) :=
  importQ_printQelib _ (emitted_toQelib l)

/-- **The exported text realises the gate list**: the `qelib1.inc` matrix of the statements read
    back from `exportQASM l` is `exp (i · exportPhase l) • listMatrix l`. -/
theorem qelibListMatrix_importQ_exportQASM (l : List (Gate n)) (hl : ∀ g ∈ l, NoRz g) :
    (importQ n (exportQASM l)).map qelibListMatrix
      = some (Complex.exp (Complex.I * (exportPhase l).toReal) • listMatrix l) := by
  rw [importQ_exportQASM, Option.map_some, qelibListMatrix_exportQ l hl]

/-- A statement of the basis has distinct operands in the sense of `Qelib.Distinct`. -/
theorem distinct_of_emitted (g : QGate n) (hg : Emitted g) : Distinct g := by
  cases g <;> simp_all [Emitted, Distinct]

/-- **The gates the importer reads from the exported text** have the matrix of the gate list up
    to the exact phase `listPhase (exportQ l) + exportPhase l`. -/
theorem listMatrix_importGates_exportQASM (l : List (Gate n)) (hl : ∀ g ∈ l, NoRz g) :
    (importGates n (exportQASM l)).map listMatrix
      = some (Complex.exp (Complex.I * (listPhase (exportQ l) + exportPhase l).toReal)
          • listMatrix l) := by
  rw [importGates_eq_importQ, importQ_exportQASM, Option.map_some, Option.map_some,
    listMatrix_flatMap_lowerQ (exportQ l)
      (fun g hg => distinct_of_emitted g (emitted_toQelib l g hg)),
    qelibListMatrix_exportQ l hl, smul_smul, ← Complex.exp_add, PiLin.toReal_add]
  congr 3
  push_cast
  ring

end CatCrypt.Quantum.QrunchExport
