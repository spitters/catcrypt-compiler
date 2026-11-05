/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.OpenQASM
public import CatCrypt.Quantum.GateUnitarity
public import Mathlib.Data.List.ReduceOption
public import Mathlib.Data.Rat.Lemmas
public import Std.Data.String.ToNat
public import Std.Data.String.ToInt
public meta import CatCrypt.Quantum.QCircuit
public meta import CatCrypt.Quantum.OpenQASM

/-!
# Lossless OpenQASM 3.0 I/O for the exact gate set

`emitDQASM` (in `CatCrypt.Quantum.OpenQASM`) prints a list of exact gates
`DGate n`, whose `Rz` angle is an exact angle `a + b·π` (`PiLin`). This module gives the
parser `parseDFixed` and proves that it inverts the printer on every gate list,
with the denotation of a discrete gate list through the real `Gate` semantics.

* `parseDFixed` — parse an OpenQASM 3.0 program into a list of exact gates; a
  line that is neither a header, a comment, blank, nor a statement of the exact
  gate set (a `measure` statement included) makes the whole parse `none`.
* `parseDFixed_emitDQASM` — `parseDFixed n (emitDQASM n gs) = some gs` for every
  gate list.
* `parseDFixed_toQASMStr` — the same round trip for the program `toQASMStr c` of
  a circuit over the exact gate set.
* `DGate.toGate`, `dDenote` — a discrete gate at the real-angle semantics (`Rz`
  via `PiLin.toReal`) and the denotation of a discrete gate list.
* `dDenote_emit_parse` — emitting then parsing preserves the denotation.

The parser reads each line as a list of characters: an operand is `q[i]`. An
angle is a rational part `k` or `k/d`, a `π` part `0`, `pi`, `-pi`, `k*pi`, each
optionally followed by `/d`, or the sum `r+B` of a rational part and a `π` part
(`DQASM.parseAngle`).

## Main results

* `DQASM.parseDFixed` — the parser of an OpenQASM 3.0 program into a list of exact gates.
* `DQASM.parseDFixed_emitDQASM` — parsing the printed program of a gate list returns that
  gate list.
* `DQASM.parseDFixed_toQASMStr` — parsing the program of a circuit over the exact gate set
  returns its gate list.
* `DQASM.parseAngle_toQASM` — parsing the printed form of an exact angle returns that angle.
* `dDenote` — the unitary-channel denotation of a list of exact gates.
* `dDenote_emit_parse` — emitting then parsing a gate list preserves its denotation.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.OpenQASM
open CatCrypt.Quantum.GateUnitarity

namespace CatCrypt.Quantum

variable {n : ℕ}

namespace DGate

/-- Interpret a discrete gate at the real-angle semantics. -/
noncomputable def toGate : DGate n → Gate n
  | .H i => .H i
  | .X i => .X i
  | .Y i => .Y i
  | .Z i => .Z i
  | .T i => .T i
  | .Tdg i => .Tdg i
  | .S i => .S i
  | .CNOT c t => .CNOT c t
  | .CZ c t => .CZ c t
  | .Rz i q => .Rz i (PiLin.toReal q)

end DGate

namespace DQASM

/-! ## Character-level parser -/

/-- Whitespace that may surround a statement. -/
def isBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

/-- A line without leading and trailing whitespace. -/
def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile isBlank).reverse.dropWhile isBlank).reverse

/-- Split a list at the first occurrence of `c`; the second part starts with `c`
when `c` occurs. -/
def breakAt (c : Char) : List Char → List Char × List Char
  | [] => ([], [])
  | x :: xs => if x = c then ([], x :: xs) else (x :: (breakAt c xs).1, (breakAt c xs).2)

/-- The coefficient `k` of an angle numerator `pi`, `-pi` or `k*pi`. -/
def parseNumPi (a : List Char) : Option ℤ :=
  if a = ['p', 'i'] then some 1
  else if a = ['-', 'p', 'i'] then some (-1)
  else match a.reverse with
    | 'i' :: 'p' :: '*' :: r => (String.ofList r.reverse).toInt?
    | _ => none

/-- An OpenQASM 3.0 angle literal `0`, `kπ` or `kπ/d` as a `QasmAngle`. -/
def parsePiAngle (cs : List Char) : Option QasmAngle :=
  match cs.splitOn '/' with
  | [a] => if a = ['0'] then some 0 else (parseNumPi a).map (fun k => (k : ℚ))
  | [a, b] =>
    match parseNumPi a, (String.ofList b).toNat? with
    | some k, some d => if d = 0 then none else some ((k : ℚ) / (d : ℚ))
    | _, _ => none
  | _ => none

/-- A rational literal `k` or `k/d` with an integer `k` and a natural `d ≠ 0`. -/
def parseRat (cs : List Char) : Option ℚ :=
  match cs.splitOn '/' with
  | [a] => (String.ofList a).toInt?.map (fun k => (k : ℚ))
  | [a, b] =>
    match (String.ofList a).toInt?, (String.ofList b).toNat? with
    | some k, some d => if d = 0 then none else some ((k : ℚ) / (d : ℚ))
    | _, _ => none
  | _ => none

/-- An OpenQASM 3.0 angle expression as an exact angle `a + b·π`: a multiple of
`π` read by `parsePiAngle` (a summand containing `p`), a rational read by
`parseRat`, or the sum `r+B` of a rational `r` and a multiple `B` of `π`. -/
def parseAngle (cs : List Char) : Option PiLin :=
  match cs.splitOn '+' with
  | [x] =>
    if 'p' ∈ x then (parsePiAngle x).map PiLin.ofPi else (parseRat x).map fun a => ⟨a, 0⟩
  | [x, y] =>
    match parseRat x, parsePiAngle y with
    | some a, some b => some ⟨a, b⟩
    | _, _ => none
  | _ => none

/-- An operand `q[i]` with `i < n` at the head of a line, and the rest. -/
def parseQubit (n : ℕ) : List Char → Option (Fin n × List Char)
  | 'q' :: '[' :: rest =>
    match breakAt ']' rest with
    | (ds, ']' :: r) =>
      match (String.ofList ds).toNat? with
      | some i => if h : i < n then some (⟨i, h⟩, r) else none
      | none => none
    | _ => none
  | _ => none

/-- The operand part `q[i];` of a one-qubit statement. -/
def parseOneQ (n : ℕ) (mk : Fin n → DGate n) (cs : List Char) : Option (DGate n) :=
  match parseQubit n cs with
  | some (i, [';']) => some (mk i)
  | _ => none

/-- The operand part `q[c], q[t];` of a two-qubit statement. -/
def parseTwoQ (n : ℕ) (mk : Fin n → Fin n → DGate n) (cs : List Char) :
    Option (DGate n) :=
  match parseQubit n cs with
  | some (c, ',' :: ' ' :: r) =>
    match parseQubit n r with
    | some (t, [';']) => some (mk c t)
    | _ => none
  | _ => none

/-- A statement of the exact gate set. -/
def parseGate (n : ℕ) : List Char → Option (DGate n)
  | 'h' :: ' ' :: r => parseOneQ n .H r
  | 'x' :: ' ' :: r => parseOneQ n .X r
  | 'y' :: ' ' :: r => parseOneQ n .Y r
  | 'z' :: ' ' :: r => parseOneQ n .Z r
  | 't' :: ' ' :: r => parseOneQ n .T r
  | 't' :: 'd' :: 'g' :: ' ' :: r => parseOneQ n .Tdg r
  | 's' :: ' ' :: r => parseOneQ n .S r
  | 'c' :: 'x' :: ' ' :: r => parseTwoQ n .CNOT r
  | 'c' :: 'z' :: ' ' :: r => parseTwoQ n .CZ r
  | 'r' :: 'z' :: '(' :: r =>
    match breakAt ')' r with
    | (a, ')' :: ' ' :: r') =>
      match parseAngle a with
      | some q => parseOneQ n (fun i => .Rz i q) r'
      | none => none
    | _ => none
  | _ => none

/-- A blank line, a comment, or a header line (`OPENQASM`, `include`, `qubit`). -/
def isSkipLine (cs : List Char) : Bool :=
  cs.isEmpty || "OPENQASM".toList.isPrefixOf cs || "include".toList.isPrefixOf cs ||
    "qubit".toList.isPrefixOf cs || "//".toList.isPrefixOf cs

/-- One line: `some none` for a line skipped by `isSkipLine`, `some (some g)` for a
statement of the exact gate set, `none` otherwise. -/
def parseLine (n : ℕ) (cs : List Char) : Option (Option (DGate n)) :=
  let t := trimChars cs
  if isSkipLine t then some none else (parseGate n t).map some

end DQASM

/-- Parse a full OpenQASM 3.0 program into a list of exact gates (known `n`).
A line that is neither skipped nor a statement of the exact gate set, a
`measure` statement included, makes the result `none`. -/
def parseDFixed (n : ℕ) (s : String) : Option (List (DGate n)) :=
  ((s.toList.splitOn '\n').mapM (DQASM.parseLine n)).map List.reduceOption

/-! ## Round trip -/

namespace DQASM

theorem breakAt_append (c : Char) (a b : List Char) (ha : c ∉ a) :
    breakAt c (a ++ c :: b) = (a, c :: b) := by
  induction a with
  | nil => simp [breakAt]
  | cons x xs ih => simp_all [breakAt]; grind

private theorem not_mem_toDigits (c : Char) (hc : c.isDigit = false) (k : ℕ) :
    c ∉ Nat.toDigits 10 k :=
  fun h => by simp [Nat.isDigit_of_mem_toDigits (by decide) (by decide) h] at hc

private theorem toNat?_ofList_toDigits (k : ℕ) :
    (String.ofList (Nat.toDigits 10 k)).toNat? = some k := by
  rw [← Nat.repr_eq_ofList_toDigits]; exact Nat.toNat?_repr k

private theorem not_mem_int_repr (k : ℤ) (c : Char) (hc : c.isDigit = false)
    (h2 : c ≠ '-') : c ∉ k.repr.toList := by
  rw [Int.repr_eq_ite]
  split <;> simp [not_mem_toDigits c hc, h2]

/-- A character that is not a digit and not one of `-`, `*`, `p`, `i`, `/` does
not occur in a printed angle. -/
theorem not_mem_angle (q : QasmAngle) (c : Char) (hc : c.isDigit = false) (h1 : c ≠ '-')
    (h2 : c ≠ '*') (h3 : c ≠ 'p') (h4 : c ≠ 'i') (h5 : c ≠ '/') :
    c ∉ (QasmAngle.toQASM q).toList := by
  have h0 : c ≠ '0' := by rintro rfl; simp at hc
  have hn : ∀ k : ℤ, c ∉ (QasmAngle.numPiToString k).toList := by
    intro k
    unfold QasmAngle.numPiToString
    split_ifs <;> simp [toString, not_mem_int_repr _ c hc h1, *]
  unfold QasmAngle.toQASM
  split_ifs <;> simp [toString, not_mem_toDigits c hc, *]

theorem parseNumPi_numPiToString (k : ℤ) :
    parseNumPi (QasmAngle.numPiToString k).toList = some k := by
  unfold QasmAngle.numPiToString
  split_ifs with h1 h2
  · subst h1; rfl
  · subst h2; rfl
  · have e1 : (k.repr.toList ++ ['*', 'p', 'i']) ≠ ['p', 'i'] := by
      intro h; have := congrArg List.length h; simp at this
    have e2 : (k.repr.toList ++ ['*', 'p', 'i']) ≠ ['-', 'p', 'i'] := by
      intro h; have := congrArg List.reverse h; simp at this
    simp only [toString, String.toList_append]
    simp [parseNumPi, e1, e2]

/-- The parser of multiples of `π` inverts `QasmAngle.toQASM`. -/
theorem parsePiAngle_toQASM (q : QasmAngle) :
    parsePiAngle (QasmAngle.toQASM q).toList = some q := by
  have hs : ∀ k : ℤ, '/' ∉ (QasmAngle.numPiToString k).toList := by
    intro k; unfold QasmAngle.numPiToString
    split_ifs <;> simp [toString, not_mem_int_repr k '/' (by decide) (by decide)]
  unfold QasmAngle.toQASM
  split_ifs with h0 h1
  · simp [parsePiAngle, Rat.num_eq_zero.mp h0, List.splitOn_eq_singleton]
  · have hne : (QasmAngle.numPiToString q.num).toList ≠ ['0'] := by
      intro h
      have := parseNumPi_numPiToString q.num
      rw [h] at this
      simp [parseNumPi] at this
    simpa [parsePiAngle, List.splitOn_eq_singleton (hs _), hne, parseNumPi_numPiToString]
      using Rat.coe_int_num_of_den_eq_one h1
  · simp only [toString, String.toList_append]
    simp [parsePiAngle, List.splitOn_append_cons_self_of_not_mem (hs _),
      List.splitOn_eq_singleton (not_mem_toDigits '/' (by decide) _), parseNumPi_numPiToString,
      toNat?_ofList_toDigits, Rat.num_div_den]

/-- A character that is not a digit and not one of `-`, `/` does not occur in a
printed rational. -/
theorem not_mem_rat (a : ℚ) (c : Char) (hc : c.isDigit = false) (h1 : c ≠ '-')
    (h5 : c ≠ '/') : c ∉ (toString a).toList := by
  change c ∉ (if a.den = 1 then toString a.num else s!"{a.num}/{a.den}").toList
  split_ifs <;> simp [toString, not_mem_int_repr _ c hc h1, not_mem_toDigits c hc, h5]

/-- The rational parser inverts the printer `toString` of `ℚ`. -/
theorem parseRat_toString (a : ℚ) : parseRat (toString a).toList = some a := by
  have hs := not_mem_int_repr a.num '/' (by decide) (by decide)
  change parseRat (if a.den = 1 then toString a.num else s!"{a.num}/{a.den}").toList = some a
  split_ifs with h1
  · simpa [parseRat, toString, List.splitOn_eq_singleton hs] using
      Rat.coe_int_num_of_den_eq_one h1
  · simp only [toString, String.toList_append]
    simp [parseRat, List.splitOn_append_cons_self_of_not_mem hs,
      List.splitOn_eq_singleton (not_mem_toDigits '/' (by decide) _), toNat?_ofList_toDigits,
      Rat.num_div_den]

theorem p_mem_numPiToString (k : ℤ) : 'p' ∈ (QasmAngle.numPiToString k).toList := by
  unfold QasmAngle.numPiToString; split_ifs <;> simp [toString]

/-- The characters of a printed angle with nonzero rational and `π` parts: the
rational part, `+`, the `π` part. -/
theorem toList_toQASM_of_ne {p : PiLin} (ha : p.a ≠ 0) (hb : p.b ≠ 0) :
    p.toQASM.toList = (toString p.a).toList ++ '+' :: (QasmAngle.toQASM p.b).toList := by
  simp only [PiLin.toQASM, ha, hb, ite_false, String.toList_append, List.append_assoc]
  rfl

/-- A character that is not a digit and not one of `-`, `*`, `p`, `i`, `/`, `+`
does not occur in a printed exact angle. -/
theorem not_mem_piLin (p : PiLin) (c : Char) (hc : c.isDigit = false) (h1 : c ≠ '-')
    (h2 : c ≠ '*') (h3 : c ≠ 'p') (h4 : c ≠ 'i') (h5 : c ≠ '/') (h6 : c ≠ '+') :
    c ∉ p.toQASM.toList := by
  by_cases ha : p.a = 0
  · simpa [PiLin.toQASM, ha] using not_mem_angle p.b c hc h1 h2 h3 h4 h5
  by_cases hb : p.b = 0
  · simpa [PiLin.toQASM, ha, hb] using not_mem_rat p.a c hc h1 h5
  rw [toList_toQASM_of_ne ha hb]
  simp [not_mem_rat p.a c hc h1 h5, not_mem_angle p.b c hc h1 h2 h3 h4 h5, h6]

/-- The angle parser inverts `PiLin.toQASM`. -/
theorem parseAngle_toQASM (p : PiLin) : parseAngle p.toQASM.toList = some p := by
  have hplus : ∀ q : QasmAngle, '+' ∉ (QasmAngle.toQASM q).toList := fun q =>
    not_mem_angle q '+' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrp : ∀ a : ℚ, '+' ∉ (toString a).toList := fun a =>
    not_mem_rat a '+' (by decide) (by decide) (by decide)
  have hrq : ∀ a : ℚ, parseAngle (toString a).toList = some ⟨a, 0⟩ := fun a => by
    have hp : 'p' ∉ (toString a).toList :=
      not_mem_rat a 'p' (by decide) (by decide) (by decide)
    simp [parseAngle, List.splitOn_eq_singleton (hrp a), hp, parseRat_toString]
  by_cases ha : p.a = 0
  · obtain ⟨a, b⟩ := p
    dsimp only at ha
    subst ha
    by_cases hb0 : b.num = 0
    · obtain rfl : b = 0 := Rat.num_eq_zero.mp hb0
      rw [show ((⟨0, 0⟩ : PiLin).toQASM).toList = (toString (0 : ℚ)).toList by
        simp [PiLin.toQASM, QasmAngle.toQASM, toString, Int.repr_eq_ite]]
      exact hrq 0
    · have hp : 'p' ∈ (QasmAngle.toQASM b).toList := by
        unfold QasmAngle.toQASM
        split_ifs <;> simp [toString, p_mem_numPiToString]
      simp [PiLin.toQASM, parseAngle, List.splitOn_eq_singleton (hplus b), hp,
        parsePiAngle_toQASM, PiLin.ofPi]
  by_cases hb : p.b = 0
  · obtain ⟨a, b⟩ := p
    dsimp only at ha hb
    subst hb
    simpa [PiLin.toQASM, ha] using hrq a
  rw [toList_toQASM_of_ne ha hb]
  simp [parseAngle, List.splitOn_append_cons_self_of_not_mem (hrp p.a),
    List.splitOn_eq_singleton (hplus p.b), parseRat_toString, parsePiAngle_toQASM]

theorem parseQubit_emit (i : Fin n) (r : List Char) :
    parseQubit n ('q' :: '[' :: (Nat.toDigits 10 i.val ++ ']' :: r)) = some (i, r) := by
  simp [parseQubit, breakAt_append _ _ _ (not_mem_toDigits ']' (by decide) _),
    toNat?_ofList_toDigits]

/-- The line parser inverts `DGate.toQASM`. -/
theorem parseLine_toQASM (g : DGate n) :
    parseLine n (g.toQASM).toList = some (some g) := by
  have hz : ∀ q : PiLin, ')' ∉ q.toQASM.toList := fun q =>
    not_mem_piLin q ')' (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  cases g with
  | H i => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseOneQ, parseQubit_emit]
  | X i => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseOneQ, parseQubit_emit]
  | Y i => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseOneQ, parseQubit_emit]
  | Z i => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseOneQ, parseQubit_emit]
  | T i => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseOneQ, parseQubit_emit]
  | Tdg i => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseOneQ, parseQubit_emit]
  | S i => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseOneQ, parseQubit_emit]
  | CNOT c t => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseTwoQ, parseQubit_emit]
  | CZ c t => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseTwoQ, parseQubit_emit]
  | Rz i q => simp [DGate.toQASM, toString, parseLine, trimChars, isBlank, isSkipLine,
      parseGate, parseOneQ, parseQubit_emit, breakAt_append _ _ _ (hz q), parseAngle_toQASM]

theorem newline_not_mem_toQASM (g : DGate n) : '\n' ∉ (g.toQASM).toList := by
  have hz : ∀ q : PiLin, '\n' ∉ q.toQASM.toList := fun q =>
    not_mem_piLin q '\n' (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  cases g <;> simp [DGate.toQASM, toString, not_mem_toDigits '\n' (by decide), hz]

end DQASM

/-- **Round trip.** Parsing the printed program of an exact gate list returns that
gate list. -/
theorem parseDFixed_emitDQASM (n : ℕ) (gs : List (DGate n)) :
    parseDFixed n (emitDQASM n gs) = some gs := by
  have hgs : (gs.map fun g => (g.toQASM).toList).mapM (DQASM.parseLine n) =
      some (gs.map some) := by
    induction gs with
    | nil => rfl
    | cons g gs ih => simp [List.mapM_cons, DQASM.parseLine_toQASM, ih]
  have hhd : ((qasmHeaderLines n).map String.toList).mapM (DQASM.parseLine n) =
      some [none, none, none] := by
    simp [qasmHeaderLines, toString, DQASM.parseLine, DQASM.trimChars, DQASM.isBlank,
      DQASM.isSkipLine]
  have hsplit : (emitDQASM n gs).toList.splitOn '\n' =
      (qasmHeaderLines n).map String.toList ++ gs.map fun g => (g.toQASM).toList := by
    simp only [emitDQASM, joinLines, String.toList_intercalate]
    rw [show ("\n" : String).toList = ['\n'] from rfl, List.splitOn_intercalate]
    · simp
    · simp [qasmHeaderLines, toString, DQASM.not_mem_toDigits '\n' (by decide),
        DQASM.newline_not_mem_toQASM]
    · simp [qasmHeaderLines]
  simp [parseDFixed, hsplit, List.mapM_append, hhd, hgs, List.reduceOption,
    List.filterMap_map]

/-- Round trip for a circuit over the exact gate set: its printed program parses
back to its exact gate list. -/
theorem parseDFixed_toQASMStr (c : Circuit n) (ds : List (DGate n))
    (h : toDGateList c = some ds) :
    (toQASMStr c).bind (parseDFixed n) = some ds := by
  simp [toQASMStr, h, parseDFixed_emitDQASM]

-- A circuit with the angles `π/4` and `-1/3 + π/2` prints and parses back.
#guard (toQASMStr (Circuit.gate (Gate.RzQ (0 : Fin 1) ⟨0, 1 / 4⟩)
    (Circuit.gate (Gate.RzQ 0 ⟨-1 / 3, 1 / 2⟩) .empty))).bind (parseDFixed 1) =
  some [.Rz 0 ⟨0, 1 / 4⟩, .Rz 0 ⟨-1 / 3, 1 / 2⟩]

-- A rational angle without a `π` part prints and parses back.
#guard (toQASMStr (Circuit.gate (Gate.RzQ (0 : Fin 1) ⟨1 / 4, 0⟩) .empty)).bind
    (parseDFixed 1) = some [.Rz 0 ⟨1 / 4, 0⟩]

/-! ## Semantics and adequacy -/

/-- Denotation of a discrete gate list through the real `unitaryDenote`. -/
noncomputable def dDenote (gs : List (DGate n)) : QComp (2 ^ n) Unit :=
  unitaryDenote (Circuit.ofList (gs.map DGate.toGate))

/-- **Adequacy.** Emitting then parsing a discrete gate list preserves its
denotation; in particular the `Rz` angle survives. -/
theorem dDenote_emit_parse (gs : List (DGate n)) :
    (parseDFixed n (emitDQASM n gs)).map dDenote = some (dDenote gs) := by
  rw [parseDFixed_emitDQASM, Option.map_some]

end CatCrypt.Quantum
