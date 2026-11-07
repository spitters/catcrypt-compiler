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
* `parseQ_toQASM` — every printed statement of `qelib1.inc` reads back as itself
  (`parseQ_h`, …, `parseQ_ccz` for each statement).
* `parseQ_trailing` — a printed statement with text that is not whitespace after its last
  operand reads as `none`.
* `importQ_printAll` — the header and the printed statements of any statement list,
  separated by any whitespace, read back as that list.
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

/-- A string whose first character is not whitespace is its own text after leading
    whitespace. -/
theorem ofList_dropWhile_of_cons {s : String} {c : Char} {r : List Char}
    (h : s.toList = c :: r) (hc : c.isWhitespace = false) :
    String.ofList (s.toList.dropWhile Char.isWhitespace) = s := by
  rw [h, List.dropWhile_cons_of_neg (by simp [hc]), ← h, String.ofList_toList]

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

/-! ## Reading a printed statement

`printParts g` is the operation name, angles and operand indices of a statement as
`QrunchBasis.QGate.toQASM` prints it, and `toList_toQASM_parts` writes the printed text in the
shape of `OpenQASMImport.parseQL_shape`. -/

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

/-- The characters of the operand `q[k]`. -/
def qOperand (k : ℕ) : List Char := 'q' :: '[' :: (Nat.toDigits 10 k ++ [']'])

/-- The operand fields `q[k]` of the indices `ks`, the text `t` after the last one. -/
def operandFieldsGo : List ℕ → List Char → List (List Char)
  | [], _ => []
  | [k], t => [qOperand k ++ t]
  | k :: k' :: ks, t => qOperand k :: operandFieldsGo (k' :: ks) t

/-- The operand fields of a printed statement: `operandFieldsGo` with a space before the
    first operand. -/
def operandFields (ks : List ℕ) (t : List Char) : List (List Char) :=
  match operandFieldsGo ks t with
  | [] => []
  | f :: fs => (' ' :: f) :: fs

/-- The printed angle list of a statement, none for a statement without angles. -/
def angleArg (as : List PiLin) : Option (List Char) :=
  if as = [] then none else some ([','].intercalate (as.map fun a => a.toQASM.toList))

/-- The operation name, angles and operand indices of a statement as `QGate.toQASM` prints
    it. -/
def printParts : QGate n → String × List PiLin × List ℕ
  | .h q => ("h", [], [q.val])
  | .x q => ("x", [], [q.val])
  | .y q => ("y", [], [q.val])
  | .z q => ("z", [], [q.val])
  | .s q => ("s", [], [q.val])
  | .sdg q => ("sdg", [], [q.val])
  | .t q => ("t", [], [q.val])
  | .tdg q => ("tdg", [], [q.val])
  | .sx q => ("sx", [], [q.val])
  | .sxdg q => ("sxdg", [], [q.val])
  | .rx q a => ("rx", [a], [q.val])
  | .ry q a => ("ry", [a], [q.val])
  | .rz q a => ("rz", [a], [q.val])
  | .p q a => ("p", [a], [q.val])
  | .u q a b c => ("u3", [a, b, c], [q.val])
  | .u2 q a b => ("u2", [a, b], [q.val])
  | .cx c t => ("cx", [], [c.val, t.val])
  | .cz c t => ("cz", [], [c.val, t.val])
  | .swap a b => ("swap", [], [a.val, b.val])
  | .cp c t a => ("cp", [a], [c.val, t.val])
  | .ccx a b t => ("ccx", [], [a.val, b.val, t.val])
  | .ccz a b t => ("ccz", [], [a.val, b.val, t.val])

/-- The characters of a printed statement, from its parts. -/
theorem toList_toQASM_parts (g : QGate n) :
    (QrunchBasis.QGate.toQASM g).toList = (printParts g).1.toList ++
      argText (angleArg (printParts g).2.1) ++
      [','].intercalate (operandFields (printParts g).2.2 []) ++ [';'] := by
  cases g <;> simp [QrunchBasis.QGate.toQASM, printParts, argText, angleArg,
    operandFields, operandFieldsGo, qOperand, toString, Nat.repr_eq_ofList_toDigits]

/-- The characters of an operand are `q`, `[`, `]` and digits. -/
theorem mem_qOperand {k : ℕ} {c : Char} (hc : c ∈ qOperand k) :
    c = 'q' ∨ c = '[' ∨ c = ']' ∨ c.isDigit = true := by
  simp only [qOperand, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h)))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Operand fields of a nonempty index list are nonempty. -/
theorem operandFieldsGo_ne_nil (ks : List ℕ) (t : List Char) (h : ks ≠ []) :
    operandFieldsGo ks t ≠ [] := by
  match ks, h with
  | [_], _ => simp [operandFieldsGo]
  | _ :: _ :: _, _ => simp [operandFieldsGo]

/-- The characters of the operand fields are those of operands and of the text after them. -/
theorem mem_operandFieldsGo (ks : List ℕ) (t : List Char) :
    ∀ f ∈ operandFieldsGo ks t, ∀ c ∈ f,
      c = 'q' ∨ c = '[' ∨ c = ']' ∨ c.isDigit = true ∨ c ∈ t := by
  fun_induction operandFieldsGo ks t with
  | case1 => simp
  | case2 k t =>
    intro f hf c hc
    simp only [List.mem_singleton] at hf
    subst hf
    rcases List.mem_append.mp hc with h | h
    · rcases mem_qOperand h with h | h | h | h <;> simp [h]
    · simp [h]
  | case3 k k' ks t ih =>
    intro f hf c hc
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases mem_qOperand hc with h | h | h | h <;> simp [h]
    · exact ih f hf c hc

/-- Appending a text to the operand fields appends it to the last one. -/
theorem intercalate_operandFieldsGo_append (ks : List ℕ) (t : List Char) (h : ks ≠ []) :
    [','].intercalate (operandFieldsGo ks []) ++ t = [','].intercalate (operandFieldsGo ks t) := by
  fun_induction operandFieldsGo ks t with
  | case1 => exact absurd rfl h
  | case2 k t => simp [operandFieldsGo]
  | case3 k k' ks t ih =>
    simp only [operandFieldsGo]
    rw [List.intercalate_cons_of_ne_nil (operandFieldsGo_ne_nil _ _ (by simp)),
      List.intercalate_cons_of_ne_nil (operandFieldsGo_ne_nil _ _ (by simp)),
      List.append_assoc, ih (by simp)]

/-- The printed operand text is a space and the operand fields. -/
theorem intercalate_operandFields (ks : List ℕ) (t : List Char) (h : ks ≠ []) :
    [','].intercalate (operandFields ks t) = ' ' :: [','].intercalate (operandFieldsGo ks t) := by
  obtain ⟨f, fs, hf⟩ := List.exists_cons_of_ne_nil (operandFieldsGo_ne_nil ks t h)
  simp only [operandFields, hf]
  cases fs <;> simp [List.intercalate_cons_cons]

/-- Appending a text to the printed operands appends it to the last operand field. -/
theorem operandFields_append (ks : List ℕ) (t : List Char) (h : ks ≠ []) :
    [','].intercalate (operandFields ks []) ++ t = [','].intercalate (operandFields ks t) := by
  rw [intercalate_operandFields ks [] h, intercalate_operandFields ks t h, List.cons_append,
    intercalate_operandFieldsGo_append ks t h]

/-- The characters of the printed operand fields. -/
theorem mem_operandFields (ks : List ℕ) (t : List Char) :
    ∀ f ∈ operandFields ks t, ∀ c ∈ f,
      c = ' ' ∨ c = 'q' ∨ c = '[' ∨ c = ']' ∨ c.isDigit = true ∨ c ∈ t := by
  intro f hf c hc
  unfold operandFields at hf
  split at hf
  · simp at hf
  · rename_i g gs hg
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases List.mem_cons.mp hc with h | hc
      · exact Or.inl h
      · exact Or.inr (mem_operandFieldsGo ks t g (by simp [hg]) c hc)
    · exact Or.inr (mem_operandFieldsGo ks t f (by simp [hg, hf]) c hc)

/-- The operand fields read back as their indices when the text after them is whitespace. -/
theorem mapM_operandFieldsGo (ks : List ℕ) (t : List Char) (h : ks ≠ []) :
    (operandFieldsGo ks t).mapM parseOperand =
      if t.all Char.isWhitespace then some ks else none := by
  fun_induction operandFieldsGo ks t with
  | case1 => exact absurd rfl h
  | case2 k t =>
    have hk := parseOperand_q [] t k (by simp)
    simp only [List.nil_append] at hk
    simp only [qOperand, List.cons_append, List.append_assoc, List.mapM_cons, List.mapM_nil,
      List.nil_append]
    rw [hk]
    split <;> simp
  | case3 k k' ks t ih =>
    have hk := parseOperand_q [] [] k (by simp)
    simp only [List.nil_append, List.all_nil, ite_true] at hk
    rw [List.mapM_cons, ih (by simp)]
    simp only [qOperand, hk]
    split <;> simp

/-- The printed operand fields read back as their indices when the text after them is
    whitespace. -/
theorem mapM_operandFields (ks : List ℕ) (t : List Char) (h : ks ≠ []) :
    (operandFields ks t).mapM parseOperand =
      if t.all Char.isWhitespace then some ks else none := by
  have hg := mapM_operandFieldsGo ks t h
  obtain ⟨f, fs, hf⟩ := List.exists_cons_of_ne_nil (operandFieldsGo_ne_nil ks t h)
  rw [hf] at hg
  simpa only [operandFields, hf, List.mapM_cons, parseOperand_cons_ws ' ' f (by decide)]
    using hg

/-- A character other than `,`, a digit and `-`, `*`, `p`, `i`, `/`, `+` is not in a printed
    angle list. -/
theorem not_mem_angleArg (as : List PiLin) (c : Char) (h1 : c ≠ ',')
    (h2 : ¬ (c.isDigit = true ∨ c ∈ ['-', '*', 'p', 'i', '/', '+'])) :
    ∀ a ∈ angleArg as, c ∉ a := by
  intro a ha hc
  unfold angleArg at ha
  split at ha
  · simp at ha
  · simp only [Option.mem_def, Option.some.injEq] at ha
    subst ha
    rcases mem_intercalate_of hc with h | ⟨l, hl, hc⟩
    · exact h1 (List.mem_singleton.mp h)
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hl
      exact not_mem_piLin_of b c h2 hc

/-- A printed angle list has no `)`. -/
theorem angleArg_noParen (as : List PiLin) : ∀ a ∈ angleArg as, ')' ∉ a :=
  not_mem_angleArg as ')' (by decide) (by decide)

/-- A printed angle list reads back as its angles. -/
theorem mapM_angleOf_angleArg (as : List PiLin) (h : as ≠ []) :
    (splitCommas ([','].intercalate (as.map fun a => a.toQASM.toList))).mapM angleOf =
      some as := by
  rw [splitCommas_intercalate _ (by simpa using h) (fun g hg => ?_)]
  · clear h
    induction as <;> simp_all [List.mapM_cons, angleOf_toQASM]
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hg
    exact not_mem_piLin_of a ',' (by decide)

/-- The operation name of a printed statement is not empty. -/
theorem printParts_name_ne_nil (g : QGate n) : (printParts g).1.toList ≠ [] := by
  cases g <;> simp [printParts]

/-- The operation name of a printed statement is letters and digits. -/
theorem printParts_name_alnum (g : QGate n) :
    ∀ c ∈ (printParts g).1.toList, c.isAlphanum = true := by
  cases g <;> simp only [printParts] <;> decide

/-- The operation name of a printed statement is not skipped. -/
theorem printParts_name_not_skipped (g : QGate n) :
    isSkipped (String.ofList (printParts g).1.toList) = false := by
  rw [String.ofList_toList]
  cases g <;> simp only [printParts] <;> decide

/-- A printed statement has operands. -/
theorem printParts_ops_ne_nil (g : QGate n) : (printParts g).2.2 ≠ [] := by
  cases g <;> simp [printParts]

/-- **A printed statement followed by a text.** The text of a printed statement with a text
    `t` without `,` after its last operand reads as the statement when `t` is whitespace, and
    as `none` otherwise. -/
theorem parseQL_printParts (g : QGate n) (t : List Char) (ht : ',' ∉ t) :
    parseQL n ((printParts g).1.toList ++ argText (angleArg (printParts g).2.1) ++
      [','].intercalate (operandFields (printParts g).2.2 t) ++ [';']) =
    if t.all Char.isWhitespace then
      (parseStmt n (printParts g).1 (printParts g).2.2
        (if (printParts g).2.1 = [] then none else some (printParts g).2.1)).map ([·])
    else none := by
  have hks := printParts_ops_ne_nil g
  have hfc : ∀ f ∈ operandFields (printParts g).2.2 t, ',' ∉ f := fun f hf hc => by
    rcases mem_operandFields _ t f hf ',' hc with h | h | h | h | h | h
    all_goals first | exact absurd h (by decide) | exact ht h
  have hhd : ∀ c ∈ ([','].intercalate (operandFields (printParts g).2.2 t)).head?,
      c.isAlphanum = false ∧ c ≠ '(' := by
    rw [intercalate_operandFields _ t hks]
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
    decide
  have hne : operandFields (printParts g).2.2 t ≠ [] := by
    obtain ⟨f, fs, hf⟩ := List.exists_cons_of_ne_nil (operandFieldsGo_ne_nil _ t hks)
    simp [operandFields, hf]
  rw [parseQL_shape n _ _ _ (printParts_name_ne_nil g) (printParts_name_alnum g)
    (printParts_name_not_skipped g) (angleArg_noParen _) hne hfc hhd,
    mapM_operandFields _ t hks, String.ofList_toList]
  split
  · simp only [Option.bind_some]
    by_cases has : (printParts g).2.1 = []
    · simp [angleArg, has]
    · simp [angleArg, has, mapM_angleOf_angleArg _ has]
  · rfl

/-- **A printed statement reads back as itself**, for every statement of `qelib1.inc`. -/
theorem parseQ_toQASM (g : QGate n) : parseQ n (QrunchBasis.QGate.toQASM g) = some [g] := by
  rw [parseQ, toList_toQASM_parts, parseQL_printParts g [] (by simp)]
  cases g <;> simp [printParts, parseStmt]

/-- **Text after the operands is refused.** A printed statement with a text `t` without `,`
    that is not whitespace between its last operand and its `;` reads as `none`. -/
theorem parseQ_trailing (g : QGate n) (t : List Char) (ht : ',' ∉ t)
    (hne : ∃ c ∈ t, c.isWhitespace = false) :
    parseQ n (String.ofList ((QrunchBasis.QGate.toQASM g).toList.dropLast ++ t ++ [';'])) =
      none := by
  have hall : t.all Char.isWhitespace = false := by
    obtain ⟨c, hc, hw⟩ := hne
    simp only [List.all_eq_false, Bool.not_eq_true]
    exact ⟨c, hc, hw⟩
  rw [parseQ, String.toList_ofList, toList_toQASM_parts, List.dropLast_concat,
    List.append_assoc _ _ t, operandFields_append _ t (printParts_ops_ne_nil g),
    parseQL_printParts g t ht, hall]
  rfl

/-! ### The statements, one by one -/

/-- A printed `h` statement reads back as itself. -/
theorem parseQ_h (q : Fin n) : parseQ n (QrunchBasis.QGate.toQASM (.h q)) = some [.h q] :=
  parseQ_toQASM _

/-- A printed `x` statement reads back as itself. -/
theorem parseQ_x (q : Fin n) : parseQ n (QrunchBasis.QGate.toQASM (.x q)) = some [.x q] :=
  parseQ_toQASM _

/-- A printed `y` statement reads back as itself. -/
theorem parseQ_y (q : Fin n) : parseQ n (QrunchBasis.QGate.toQASM (.y q)) = some [.y q] :=
  parseQ_toQASM _

/-- A printed `z` statement reads back as itself. -/
theorem parseQ_z (q : Fin n) : parseQ n (QrunchBasis.QGate.toQASM (.z q)) = some [.z q] :=
  parseQ_toQASM _

/-- A printed `s` statement reads back as itself. -/
theorem parseQ_s (q : Fin n) : parseQ n (QrunchBasis.QGate.toQASM (.s q)) = some [.s q] :=
  parseQ_toQASM _

/-- A printed `sdg` statement reads back as itself. -/
theorem parseQ_sdg (q : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.sdg q)) = some [.sdg q] :=
  parseQ_toQASM _

/-- A printed `t` statement reads back as itself. -/
theorem parseQ_t (q : Fin n) : parseQ n (QrunchBasis.QGate.toQASM (.t q)) = some [.t q] :=
  parseQ_toQASM _

/-- A printed `tdg` statement reads back as itself. -/
theorem parseQ_tdg (q : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.tdg q)) = some [.tdg q] :=
  parseQ_toQASM _

/-- A printed `sx` statement reads back as itself. -/
theorem parseQ_sx (q : Fin n) : parseQ n (QrunchBasis.QGate.toQASM (.sx q)) = some [.sx q] :=
  parseQ_toQASM _

/-- A printed `sxdg` statement reads back as itself. -/
theorem parseQ_sxdg (q : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.sxdg q)) = some [.sxdg q] :=
  parseQ_toQASM _

/-- A printed `rx` statement reads back as itself. -/
theorem parseQ_rx (q : Fin n) (a : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.rx q a)) = some [.rx q a] :=
  parseQ_toQASM _

/-- A printed `ry` statement reads back as itself. -/
theorem parseQ_ry (q : Fin n) (a : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.ry q a)) = some [.ry q a] :=
  parseQ_toQASM _

/-- A printed `rz` statement reads back as itself. -/
theorem parseQ_rz (q : Fin n) (a : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.rz q a)) = some [.rz q a] :=
  parseQ_toQASM _

/-- A printed `p` statement reads back as itself. -/
theorem parseQ_p (q : Fin n) (a : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.p q a)) = some [.p q a] :=
  parseQ_toQASM _

/-- A printed `u3` statement reads back as itself. -/
theorem parseQ_u (q : Fin n) (a b c : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.u q a b c)) = some [.u q a b c] :=
  parseQ_toQASM _

/-- A printed `u2` statement reads back as itself. -/
theorem parseQ_u2 (q : Fin n) (a b : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.u2 q a b)) = some [.u2 q a b] :=
  parseQ_toQASM _

/-- A printed `cx` statement reads back as itself. -/
theorem parseQ_cx (c t : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.cx c t)) = some [.cx c t] :=
  parseQ_toQASM _

/-- A printed `cz` statement reads back as itself. -/
theorem parseQ_cz (c t : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.cz c t)) = some [.cz c t] :=
  parseQ_toQASM _

/-- A printed `swap` statement reads back as itself. -/
theorem parseQ_swap (a b : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.swap a b)) = some [.swap a b] :=
  parseQ_toQASM _

/-- A printed `cp` statement reads back as itself. -/
theorem parseQ_cp (c t : Fin n) (a : PiLin) :
    parseQ n (QrunchBasis.QGate.toQASM (.cp c t a)) = some [.cp c t a] :=
  parseQ_toQASM _

/-- A printed `ccx` statement reads back as itself. -/
theorem parseQ_ccx (a b t : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.ccx a b t)) = some [.ccx a b t] :=
  parseQ_toQASM _

/-- A printed `ccz` statement reads back as itself. -/
theorem parseQ_ccz (a b t : Fin n) :
    parseQ n (QrunchBasis.QGate.toQASM (.ccz a b t)) = some [.ccz a b t] :=
  parseQ_toQASM _

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
  simp [headerLines, parseQ, parseQL, isSkipped, toString, Nat.repr_eq_ofList_toDigits]

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

/-- A header line is one statement text. -/
theorem isStmtText_header : ∀ s ∈ headerLines n, IsStmtText s.toList := by
  have hdig : ';' ∉ Nat.toDigits 10 n := not_mem_toDigits_of n ';' (by decide)
  simp only [headerLines, List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl | rfl)
  · exact ⟨'O', "PENQASM 2.0".toList, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨'i', "nclude \"qelib1.inc\"".toList, by decide, by decide, by decide, by decide,
      by decide⟩
  · refine ⟨'q', "reg q[".toList ++ Nat.toDigits 10 n ++ [']'], ?_, by decide, by decide,
      by decide, by simp [hdig]⟩
    simp [toString, Nat.repr_eq_ofList_toDigits]

/-- A printed statement is one statement text. -/
theorem isStmtText_toQASM (g : QGate n) : IsStmtText (QrunchBasis.QGate.toQASM g).toList := by
  obtain ⟨c, nm', hnm⟩ := List.exists_cons_of_ne_nil (printParts_name_ne_nil g)
  have hal := printParts_name_alnum g
  rw [hnm] at hal
  have hc := hal c (by simp)
  have hsemi : ';' ∉ nm' ++ argText (angleArg (printParts g).2.1) ++
      [','].intercalate (operandFields (printParts g).2.2 []) := by
    simp only [List.mem_append, not_or]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · have := hal ';' (by simp [h])
      revert this
      decide
    · cases ha : angleArg (printParts g).2.1 with
      | none => simp [ha, argText] at h
      | some a =>
        simp only [ha, argText, List.mem_cons, List.mem_append] at h
        rcases h with h | h | h
        · exact absurd h (by decide)
        · exact not_mem_angleArg _ ';' (by decide) (by decide) a ha h
        · exact absurd h (by decide)
    · rcases mem_intercalate_of h with h | ⟨l, hl, h⟩
      · exact absurd (List.mem_singleton.mp h) (by decide)
      · rcases mem_operandFields _ [] l hl ';' h with h | h | h | h | h | h
        all_goals exact absurd h (by decide)
  refine ⟨c, nm' ++ argText (angleArg (printParts g).2.1) ++
    [','].intercalate (operandFields (printParts g).2.2 []), ?_, isWhitespace_of_isAlphanum hc,
    ?_, ?_, hsemi⟩
  · rw [toList_toQASM_parts, hnm]
    simp
  · rintro rfl
    revert hc
    decide
  · rintro rfl
    revert hc
    decide

/-- Printed statements read back as themselves, one statement each. -/
theorem mapM_parseQ_toQASM (l : List (QGate n)) :
    (l.map QrunchBasis.QGate.toQASM).mapM (parseQ n) = some (l.map ([·])) := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [List.mapM_cons, parseQ_toQASM g, ih]

/-- **Completeness for printed statements.** The header lines and the printed statements of
    any statement list, in order, each preceded by any whitespace and followed at the end by
    any whitespace, read back as that list: one statement a line, several a line, or any other
    whitespace between them. -/
theorem importQ_printAll (l : List (QGate n)) (ps : List (List Char × String))
    (last : List Char)
    (hps : ps.map Prod.snd = headerLines n ++ l.map QrunchBasis.QGate.toQASM)
    (hw : ∀ p ∈ ps, ∀ c ∈ p.1, c.isWhitespace = true)
    (hlast : ∀ c ∈ last, c.isWhitespace = true) :
    importQ n (String.ofList (ps.flatMap (fun p => p.1 ++ p.2.toList) ++ last)) = some l := by
  have hflat : (ps.flatMap fun p => p.1 ++ p.2.toList) =
      (ps.map fun p => (p.1, p.2.toList)).flatMap (fun p => p.1 ++ p.2) := by
    simp [List.flatMap_map]
  have ht : ∀ p ∈ ps.map (fun p => (p.1, p.2.toList)), IsStmtText p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hm : q.2 ∈ headerLines n ++ l.map QrunchBasis.QGate.toQASM :=
      hps ▸ List.mem_map_of_mem hq
    rcases List.mem_append.mp hm with h | h
    · exact isStmtText_header _ h
    · obtain ⟨g, -, hgq⟩ := List.mem_map.mp h
      change IsStmtText q.2.toList
      rw [← hgq]
      exact isStmtText_toQASM g
  have hm : (ps.map fun p => (p.1, p.2.toList)).mapM (fun p => parseQ n (String.ofList p.2)) =
      (ps.map Prod.snd).mapM (parseQ n) := by
    rw [mapM_map, mapM_map]
    exact congrArg (fun f => List.mapM f ps) (funext fun p => by simp)
  have hw' : ∀ p ∈ ps.map (fun p => (p.1, p.2.toList)), ∀ c ∈ p.1, c.isWhitespace = true := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hw q hq
  rw [hflat, importQ_join n _ last hw' hlast ht, hm, hps, List.mapM_append,
    mapM_parseQ_header, mapM_parseQ_toQASM l]
  have hf : ∀ l' : List (QGate n), (l'.map fun x => [x]).flatten = l' := fun l' => by
    induction l' <;> simp_all
  simp [hf l]

/-- **Completeness for printed statements of the basis.** The header lines and the printed
    statements of a list of the basis `{rx, ry, cx, p}`, in order, each preceded by any
    whitespace and followed at the end by any whitespace, read back as that list
    (`importQ_printAll`). -/
theorem importQ_printWs (l : List (QGate n)) (_hl : ∀ g ∈ l, Emitted g)
    (ps : List (List Char × String)) (last : List Char)
    (hps : ps.map Prod.snd = headerLines n ++ l.map QrunchBasis.QGate.toQASM)
    (hw : ∀ p ∈ ps, ∀ c ∈ p.1, c.isWhitespace = true)
    (hlast : ∀ c ∈ last, c.isWhitespace = true) :
    importQ n (String.ofList (ps.flatMap (fun p => p.1 ++ p.2.toList) ++ last)) = some l :=
  importQ_printAll l ps last hps hw hlast

/-- The characters of an intercalation by a one-character separator. -/
theorem intercalate_singleton_cons {α : Type} (a : α) (x : List α) (ys : List (List α)) :
    [a].intercalate (x :: ys) = x ++ ys.flatMap (a :: ·) := by
  induction ys generalizing x with
  | nil => simp
  | cons y ys ih => rw [List.intercalate_cons_cons, ih]; simp

/-- **Reading a printed statement list** of the basis `{rx, ry, cx, p}` returns that list. -/
theorem importQ_printQelib (l : List (QGate n)) (hl : ∀ g ∈ l, Emitted g) :
    importQ n (printQelib n l) = some l := by
  have hp : printQelib n l = String.ofList
      ((([], "OPENQASM 2.0;") ::
        ((headerLines n).tail ++ l.map QrunchBasis.QGate.toQASM).map (fun s => (['\n'], s))
        ).flatMap (fun p => p.1 ++ p.2.toList) ++ ['\n']) := by
    refine String.ofList_toList.symm.trans ?_
    congr 1
    rw [printQelib, String.toList_append, String.toList_intercalate]
    simp [headerLines, intercalate_singleton_cons, List.flatMap_map]
  rw [hp]
  refine importQ_printWs l hl _ _ (by simp [headerLines]) ?_ (by simp)
  intro p hp c hc
  rcases List.mem_cons.mp hp with rfl | hp
  · simp at hc
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_singleton] at hc
    subst hc
    decide

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
