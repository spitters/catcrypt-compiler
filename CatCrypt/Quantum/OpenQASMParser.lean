/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.OpenQASM
public import CatCrypt.Quantum.OpenQASMDiscrete

/-!
# OpenQASM 3.0 Parser

Parses OpenQASM 3.0 text into the `Circuit n` type, the inverse of `toQASMStr`.

## Design

A line-oriented parser that splits the QASM string by newlines and matches
each line against known gate patterns. Qubit indices are extracted by
locating `[` and `]` delimiters.

## Main definitions

* `natOfDigits`    — the natural number a run of decimal digits denotes
* `parseLine`      — parse one gate statement
* `parseQASM`      — parse full QASM program, returning `Σ n, Circuit n`
* `parseQASMFixed` — parse with known qubit count
* `parseDecimal`   — a decimal literal (sign, fraction, exponent) as an exact rational
* `printDecimal`, `parseDecimal_printDecimal` — a rational whose denominator is
  `2 ^ x · 5 ^ y` printed as a literal `m e-k`, and the round trip back to it
* `parseAngleLin`  — an angle as `PiLin`: the exact form `r+B` that
  `DQASM.parseAngle` reads, a decimal in radians, or a sum `a+B` of a decimal and
  a multiple of `π`
* `parseRz`        — an `rz` statement: `RzQ` with the angle `parseAngleLin` reads
* `parseLine_rz`, `parseLine_toQASM_rz` — the angle read from `rz(k*pi/m)` and from
  the exact emitter's `rz` statement
* `parseBell_gateCount`        — Bell circuit gate count (proved)
* `parseGHZ3_gateCount`        — GHZ-3 circuit gate count (proved)
* `parseTGate_gateCount`       — T-gate circuit gate count (proved)

## References

* Cross et al. — *OpenQASM 3: A Broader and Deeper Quantum Assembly Language*,
  ACM Transactions on Quantum Computing 3(3), 2022
-/

@[expose] public section

set_option autoImplicit true

namespace CatCrypt.Quantum.OpenQASMParser

open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.OpenQASM

/-! ## Line-Based Parsing -/

/-- The natural number a nonempty run of decimal digits denotes. -/
def natOfDigits (ds : List Char) : Option ℕ :=
  if !ds.isEmpty && ds.all Char.isDigit then
    some (ds.foldl (fun a c => 10 * a + (c.toNat - '0'.toNat)) 0)
  else none

/-- Extract a natural number from a string between `[` and `]`.
    Returns `none` if no brackets found or content is not a number. -/
def extractIndex (s : String) : Option Nat :=
  match s.toList.dropWhile (· != '[') with
  | '[' :: rest => natOfDigits (rest.takeWhile (· != ']'))
  | _ => none

/-- Extract two qubit indices from a two-qubit gate line like "cx q[0], q[1];".
    Splits on `,` and extracts indices from each part. -/
def extractTwoIndices (s : String) : Option (Nat × Nat) := do
  let parts := s.splitOn ","
  match parts with
  | [p1, p2] =>
    let i1 ← extractIndex p1
    let i2 ← extractIndex p2
    some (i1, i2)
  | _ => none

/-- Strip leading whitespace from a string. -/
def stripLeading (s : String) : String :=
  String.ofList (s.toList.dropWhile (fun c => c == ' ' || c == '\t'))

/-- Check if a string starts with a given prefix. -/
def hasPrefix (s : String) (pfx : String) : Bool :=
  pfx.toList.isPrefixOf s.toList

/-- An unsigned decimal literal `d`, `d.f` or `.f` as an exact rational. -/
def parseUDecimal (cs : List Char) : Option ℚ :=
  match DQASM.breakAt '.' cs with
  | (ip, []) => (natOfDigits ip).map fun k => (k : ℚ)
  | (ip, '.' :: fp) =>
    match (if ip.isEmpty then some 0 else natOfDigits ip), natOfDigits fp with
    | some k, some f => some ((k : ℚ) + (f : ℚ) / 10 ^ fp.length)
    | _, _ => none
  | _ => none

/-- An exponent `k`, `+k` or `-k` with `k` a run of decimal digits. -/
def parseExp : List Char → Option ℤ
  | '-' :: ds => (natOfDigits ds).map fun k => -(k : ℤ)
  | '+' :: ds => (natOfDigits ds).map fun k => (k : ℤ)
  | ds => (natOfDigits ds).map fun k => (k : ℤ)

/-- `E` read as `e`, so that one exponent marker is matched. -/
def lowerE (c : Char) : Char := if c = 'E' then 'e' else c

/-- An unsigned decimal literal `m` or `m e x` (marker `e` or `E`), where `m` is read
by `parseUDecimal` and `x` by `parseExp`, as the exact rational `m · 10 ^ x`. -/
def parseUSci (cs : List Char) : Option ℚ :=
  match DQASM.breakAt 'e' (cs.map lowerE) with
  | (m, []) => parseUDecimal m
  | (m, _ :: ex) =>
    match parseUDecimal m, parseExp ex with
    | some x, some k => some (x * 10 ^ k)
    | _, _ => none

/-- A decimal literal with an optional sign `-` or `+`, digits with an optional
fractional part, and an optional exponent `e`/`E`, as an exact rational. -/
def parseDecimal : List Char → Option ℚ
  | '-' :: cs => (parseUSci cs).map (- ·)
  | '+' :: cs => parseUSci cs
  | cs => parseUSci cs

/-- The literal `m e-k`, which denotes `m / 10 ^ k`. -/
def printSci (m : ℤ) (k : ℕ) : String := toString m ++ "e-" ++ toString k

/-- The least `k ≤ q.den` with `q.den ∣ 10 ^ k`, when there is one. -/
def decimalExp (q : ℚ) : Option ℕ :=
  (List.range (q.den + 1)).find? fun k => 10 ^ k % q.den == 0

/-- A rational as a decimal literal `m e-k` with the least such `k`, when its
denominator divides a power of ten (that is, it is `2 ^ x · 5 ^ y`); `none` otherwise. -/
def printDecimal (q : ℚ) : Option String :=
  (decimalExp q).map fun k => printSci (q.num * ((10 ^ k / q.den : ℕ) : ℤ)) k

/-- An angle text read exactly as `a + b·π`: the angle `DQASM.parseAngle` reads (a
rational `num/den`, a multiple of `π`, or their sum), else a decimal literal `a`
(radians) as `⟨a, 0⟩`, else a sum `a+B` of a decimal literal and a multiple of `π`
as `⟨a, b⟩`; `none` otherwise. -/
def parseAngleLin (t : List Char) : Option PiLin :=
  match DQASM.parseAngle t with
  | some p => some p
  | none =>
    match parseDecimal t with
    | some x => some ⟨x, 0⟩
    | none =>
      match t.splitOn '+' with
      | [a, b] =>
        match parseDecimal a, DQASM.parsePiAngle b with
        | some x, some q => some ⟨x, q⟩
        | _, _ => none
      | _ => none

/-- The `rz` gate on qubit `i` with angle text `a`: `RzQ` with the angle
`parseAngleLin` reads, `none` when it reads none. Spaces in `a` are ignored. -/
def rzGateOf (i : Fin n) (a : List Char) : Option (Gate n) :=
  (parseAngleLin (a.filter (· != ' '))).map (.RzQ i)

/-- The text after `rz(` of an `rz` statement: an angle, `)`, an operand `q[i]` with
`i < n`, and `;`. -/
def parseRz (n : ℕ) (cs : List Char) : Option (Gate n) :=
  match DQASM.breakAt ')' cs with
  | (a, ')' :: r) =>
    match DQASM.parseQubit n (r.dropWhile (· == ' ')) with
    | some (i, ';' :: _) => rzGateOf i a
    | _ => none
  | _ => none

/-- A `measure` statement. Measurement is not a unitary gate, so a program
    containing one is not parsed into a `Circuit`. -/
def isMeasureLine (line : String) : Bool :=
  let s := stripLeading line
  hasPrefix s "measure " || hasPrefix s "measure\t"

/-- Parse a single QASM line into a gate for a circuit with `n` qubits.
    Returns `none` for header/comment lines and for a `measure` statement. -/
def parseLine (n : ℕ) (line : String) : Option (Gate n) :=
  let s := stripLeading line
  if s.toList.isEmpty then none
  else if hasPrefix s "OPENQASM" then none
  else if hasPrefix s "include" then none
  else if hasPrefix s "qubit" then none
  else if hasPrefix s "//" then none
  else if hasPrefix s "h " || hasPrefix s "h\t" then do
    let idx ← extractIndex s
    if h : idx < n then some (.H ⟨idx, h⟩) else none
  else if hasPrefix s "x " || hasPrefix s "x\t" then do
    let idx ← extractIndex s
    if h : idx < n then some (.X ⟨idx, h⟩) else none
  else if hasPrefix s "y " || hasPrefix s "y\t" then do
    let idx ← extractIndex s
    if h : idx < n then some (.Y ⟨idx, h⟩) else none
  else if hasPrefix s "z " || hasPrefix s "z\t" then do
    let idx ← extractIndex s
    if h : idx < n then some (.Z ⟨idx, h⟩) else none
  else if hasPrefix s "s " || hasPrefix s "s\t" then do
    let idx ← extractIndex s
    if h : idx < n then some (.S ⟨idx, h⟩) else none
  else if hasPrefix s "tdg " || hasPrefix s "tdg\t" then do
    let idx ← extractIndex s
    if h : idx < n then some (.Tdg ⟨idx, h⟩) else none
  else if hasPrefix s "t " || hasPrefix s "t\t" then do
    let idx ← extractIndex s
    if h : idx < n then some (.T ⟨idx, h⟩) else none
  else if hasPrefix s "cx " || hasPrefix s "cx\t" then do
    let (c, t) ← extractTwoIndices s
    if hc : c < n then
      if ht : t < n then some (.CNOT ⟨c, hc⟩ ⟨t, ht⟩)
      else none
    else none
  else if hasPrefix s "cz " || hasPrefix s "cz\t" then do
    let (c, t) ← extractTwoIndices s
    if hc : c < n then
      if ht : t < n then some (.CZ ⟨c, hc⟩ ⟨t, ht⟩)
      else none
    else none
  else if hasPrefix s "rz(" then parseRz n (s.toList.drop 3)
  else none

/-- Extract qubit count from a "qubit[n] q;" line. -/
def extractQubitCount (line : String) : Option Nat :=
  let s := stripLeading line
  if hasPrefix s "qubit" then extractIndex s
  else none

/-- Find the qubit declaration line and return the qubit count. -/
def findQubitCount (lines : List String) : Option Nat :=
  lines.findSome? extractQubitCount

/-! ## Full QASM Parsing -/

/-- Build a circuit from a list of gates (applied left to right). -/
def buildCircuit (gates : List (Gate n)) : Circuit n :=
  gates.foldr (fun g c => .gate g c) .empty

/-- Parse a full QASM program, returning the qubit count and circuit.
    Extracts qubit count from the `qubit[n] q;` declaration, then
    parses each line as a gate instruction. A program containing a `measure`
    statement returns `none`. -/
def parseQASM (s : String) : Option (Σ n : Nat, Circuit n) :=
  let lines := s.splitOn "\n"
  if lines.any isMeasureLine then none
  else match findQubitCount lines with
  | none => none
  | some n =>
    let gates := lines.filterMap (parseLine n)
    some ⟨n, buildCircuit gates⟩

/-- Parse a QASM program with a known qubit count `n`.
    Ignores the qubit declaration and parses gates assuming `n` qubits.
    A program containing a `measure` statement returns `none`. -/
def parseQASMFixed (n : ℕ) (s : String) : Option (Circuit n) :=
  let lines := s.splitOn "\n"
  if lines.any isMeasureLine then none
  else some (buildCircuit (lines.filterMap (parseLine n)))

/-! ## The `rz` angle -/

private theorem not_mem_digits (c : Char) (hc : c.isDigit = false) (k : ℕ) :
    c ∉ Nat.toDigits 10 k :=
  fun h => by simp [Nat.isDigit_of_mem_toDigits (by decide) (by decide) h] at hc

private theorem not_mem_intRepr (k : ℤ) (c : Char) (hc : c.isDigit = false)
    (h2 : c ≠ '-') : c ∉ k.repr.toList := by
  rw [Int.repr_eq_ite]
  split <;> simp [not_mem_digits c hc, h2]

/-! ## Decimal literals -/

/-- A run of decimal digits printed by `Nat.toDigits` reads back as its value. -/
theorem natOfDigits_toDigits (k : ℕ) : natOfDigits (Nat.toDigits 10 k) = some k := by
  have hd : (Nat.toDigits 10 k).all Char.isDigit = true :=
    List.all_eq_true.mpr fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  have hv := Nat.ofDigitChars_ten_toDigits (n := k)
  rw [Nat.ofDigitChars_eq_foldl] at hv
  have hne : (Nat.toDigits 10 k).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr Nat.toDigits_ne_nil
  simp only [natOfDigits, hd, hne, hv, Bool.not_false, Bool.and_self, ↓reduceIte]

private theorem breakAt_of_not_mem (c : Char) (a : List Char) (h : c ∉ a) :
    DQASM.breakAt c a = (a, []) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp_all [DQASM.breakAt]; grind

private theorem map_lowerE_toDigits (k : ℕ) :
    (Nat.toDigits 10 k).map lowerE = Nat.toDigits 10 k := by
  conv_rhs => rw [← List.map_id (Nat.toDigits 10 k)]
  refine List.map_congr_left fun c hc => ?_
  have hE : c ≠ 'E' := fun h => by
    have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
    simp [h] at this
  simp [lowerE, hE]

private theorem parseDecimal_of_digit_head (d : Char) (cs : List Char) (hd : d.isDigit) :
    parseDecimal (d :: cs) = parseUSci (d :: cs) := by
  have h1 : d ≠ '-' := by rintro rfl; simp at hd
  have h2 : d ≠ '+' := by rintro rfl; simp at hd
  unfold parseDecimal
  split <;> simp_all

private theorem parseUSci_printSci (u k : ℕ) :
    parseUSci (Nat.toDigits 10 u ++ 'e' :: '-' :: Nat.toDigits 10 k) =
      some ((u : ℚ) / 10 ^ k) := by
  simp only [parseUSci, List.map_append, List.map_cons, map_lowerE_toDigits]
  have he : lowerE 'e' = 'e' := by decide
  have hm : lowerE '-' = '-' := by decide
  rw [he, hm, DQASM.breakAt_append _ _ _ (not_mem_digits 'e' (by decide) u)]
  simp [parseUDecimal, breakAt_of_not_mem _ _ (not_mem_digits '.' (by decide) u),
    natOfDigits_toDigits, parseExp, zpow_neg, div_eq_mul_inv]

/-- **Decimal round trip.** The literal `m e-k` printed by `printSci` reads back as
`m / 10 ^ k`. -/
theorem parseDecimal_printSci (m : ℤ) (k : ℕ) :
    parseDecimal (printSci m k).toList = some ((m : ℚ) / 10 ^ k) := by
  simp only [printSci, toString, String.toList_append]
  rw [Int.repr_eq_ite]
  split_ifs with h
  · obtain ⟨d, ds, hds⟩ :=
      List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (b := 10) (n := m.toNat))
    have hmem : d ∈ Nat.toDigits 10 m.toNat := by rw [hds]; exact List.mem_cons_self
    have hd : d.isDigit := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hmem
    have hm : ((m.toNat : ℕ) : ℚ) = (m : ℚ) := by exact_mod_cast Int.toNat_of_nonneg h
    simp only [Nat.toList_repr]
    rw [show ("e-" : String).toList = ['e', '-'] from rfl, List.append_assoc,
      List.cons_append, List.cons_append, List.nil_append, hds, List.cons_append,
      parseDecimal_of_digit_head d _ hd, ← List.cons_append, ← hds, parseUSci_printSci, hm]
  · have hm : (((-m).toNat : ℕ) : ℚ) = -(m : ℚ) := by
      rw [show (((-m).toNat : ℕ) : ℚ) = (((-m).toNat : ℤ) : ℚ) by norm_cast,
        Int.toNat_of_nonneg (by omega)]
      push_cast; ring
    simp only [Nat.toList_repr, String.toList_append]
    rw [show ("e-" : String).toList = ['e', '-'] from rfl,
      show ("-" : String).toList = ['-'] from rfl]
    simp only [List.cons_append, List.nil_append, List.append_assoc, parseDecimal]
    rw [parseUSci_printSci, Option.map_some, hm, neg_div, neg_neg]

/-- **Decimal round trip.** A decimal literal printed by `printDecimal` reads back as
the rational it was printed from. -/
theorem parseDecimal_printDecimal {q : ℚ} {s : String} (h : printDecimal q = some s) :
    parseDecimal s.toList = some q := by
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  have hdvd : q.den ∣ 10 ^ k := by
    have := List.find?_some hk
    exact Nat.dvd_of_mod_eq_zero (by simpa using this)
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : (c : ℚ) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  have hc' : (10 : ℚ) ^ k = (q.den : ℚ) * c := by exact_mod_cast hc
  rw [parseDecimal_printSci, hc, Nat.mul_div_cancel_left _ q.den_pos]
  push_cast
  rw [hc', mul_div_mul_right _ _ hc0, Rat.num_div_den]

/-- `printDecimal` prints every rational whose denominator is `2 ^ x · 5 ^ y`. -/
theorem printDecimal_isSome {q : ℚ} {x y : ℕ} (h : q.den = 2 ^ x * 5 ^ y) :
    (printDecimal q).isSome := by
  have hx : x < 2 ^ x := Nat.lt_two_pow_self
  have hy : y < 5 ^ y := Nat.lt_pow_self (by norm_num)
  have h2 : 0 < 2 ^ x := by positivity
  have h5 : 0 < 5 ^ y := by positivity
  have hdvd : 2 ^ x * 5 ^ y ∣ 10 ^ max x y := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, mul_pow]
    exact mul_dvd_mul (Nat.pow_dvd_pow 2 (le_max_left x y)) (Nat.pow_dvd_pow 5 (le_max_right x y))
  simp only [printDecimal, decimalExp, Option.isSome_map, List.find?_isSome]
  refine ⟨max x y, ?_, ?_⟩
  · simp only [List.mem_range, h]
    have : 2 ^ x ≤ 2 ^ x * 5 ^ y := Nat.le_mul_of_pos_right _ h5
    have : 5 ^ y ≤ 2 ^ x * 5 ^ y := Nat.le_mul_of_pos_left _ h2
    omega
  · simpa [h] using Nat.mod_eq_zero_of_dvd hdvd

/-- The statement `rz(k*pi/m) q[i];` with `m ≠ 0` is the rotation `RzQ` on qubit `i` by
the angle `k/m` (in units of `π`). -/
theorem parseLine_rz (k : ℤ) (m : ℕ) (hm : m ≠ 0) (i : Fin n) :
    parseLine n ("rz(" ++ toString k ++ "*pi/" ++ toString m ++ ") q[" ++ toString i.val ++
      "];") = some (.RzQ i ((k : ℚ) / m)) := by
  have h1 : '/' ∉ k.repr.toList := not_mem_intRepr k '/' (by decide) (by decide)
  have h2 : ')' ∉ k.repr.toList := not_mem_intRepr k ')' (by decide) (by decide)
  have h3 : ' ' ∉ k.repr.toList := not_mem_intRepr k ' ' (by decide) (by decide)
  have h4 : '/' ∉ Nat.toDigits 10 m := not_mem_digits '/' (by decide) m
  have h5 : ')' ∉ Nat.toDigits 10 m := not_mem_digits ')' (by decide) m
  have h6 : ' ' ∉ Nat.toDigits 10 m := not_mem_digits ' ' (by decide) m
  set a := k.repr.toList ++ '*' :: 'p' :: 'i' :: '/' :: Nat.toDigits 10 m with ha
  have hb (r : List Char) : DQASM.breakAt ')' (a ++ ')' :: r) = (a, ')' :: r) :=
    DQASM.breakAt_append ')' a r (by simp [ha, h2, h5])
  have hf : a.filter (· != ' ') = a := List.filter_eq_self.mpr (by grind)
  have hpl : a.splitOn '+' = [a] := List.splitOn_eq_singleton (by
    simp [ha, not_mem_intRepr k '+' (by decide) (by decide), not_mem_digits '+' (by decide) m])
  have hpm : 'p' ∈ a := by simp [ha]
  have hs : a.splitOn '/' = [k.repr.toList ++ ['*', 'p', 'i'], Nat.toDigits 10 m] := by
    rw [ha, show k.repr.toList ++ '*' :: 'p' :: 'i' :: '/' :: Nat.toDigits 10 m =
        (k.repr.toList ++ ['*', 'p', 'i']) ++ '/' :: Nat.toDigits 10 m by simp,
      List.splitOn_append_cons_self_of_not_mem (by simp [h1]), List.splitOn_eq_singleton h4]
  have e1 : (k.repr.toList ++ ['*', 'p', 'i']) ≠ ['p', 'i'] := by
    intro h; have := congrArg List.length h; simp at this
  have e2 : (k.repr.toList ++ ['*', 'p', 'i']) ≠ ['-', 'p', 'i'] := by
    intro h; have := congrArg List.reverse h; simp at this
  have hm' : (String.ofList (Nat.toDigits 10 m)).toNat? = some m := by
    rw [← Nat.repr_eq_ofList_toDigits]; exact Nat.toNat?_repr m
  have hl : ("rz(" ++ toString k ++ "*pi/" ++ toString m ++ ") q[" ++ toString i.val ++
      "];").toList = 'r' :: 'z' :: '(' :: (a ++ ')' :: ' ' :: 'q' :: '[' ::
        (Nat.toDigits 10 i.val ++ [']', ';'])) := by
    simp [ha, toString, Nat.repr_eq_ofList_toDigits]
  clear_value a
  simp only [parseLine, stripLeading, hasPrefix, String.toList_ofList, hl]
  clear ha hl
  simp [parseRz, hb, DQASM.parseQubit_emit, rzGateOf,
    hf, hpl, hpm, hs, parseAngleLin, DQASM.parseAngle, DQASM.parsePiAngle, DQASM.parseNumPi,
    e1, e2, hm', hm]

/-- The `rz` statement `DGate.toQASM` prints parses back to `RzQ` with the same angle. -/
theorem parseLine_toQASM_rz (i : Fin n) (q : PiLin) :
    parseLine n (DGate.toQASM (.Rz i q)) = some (.RzQ i q) := by
  have hz : ')' ∉ q.toQASM.toList :=
    DQASM.not_mem_piLin q ')' (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hsp : ' ' ∉ q.toQASM.toList :=
    DQASM.not_mem_piLin q ' ' (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hf : q.toQASM.toList.filter (· != ' ') = q.toQASM.toList :=
    List.filter_eq_self.mpr (by grind)
  simp [DGate.toQASM, toString, parseLine, stripLeading, hasPrefix, parseRz,
    DQASM.breakAt_append _ _ _ hz, DQASM.parseQubit_emit, rzGateOf, hf,
    parseAngleLin, DQASM.parseAngle_toQASM]

end CatCrypt.Quantum.OpenQASMParser
