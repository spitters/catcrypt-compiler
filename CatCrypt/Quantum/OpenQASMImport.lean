/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public meta import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.OpenQASMParser
public meta import CatCrypt.Quantum.OpenQASMParser

/-!
# Importing OpenQASM benchmark files

A source is split into statement texts, each ending at its `;` (`stmtsGo`), so a line
may carry several statements and a statement may span lines. A `//` between statements
begins a comment to the end of its line. Non-blank text after the last `;` fails the
import. A statement is either a declaration the importer skips by name, or a gate it
knows, or the import returns `none`; an unsupported gate fails the import rather than
being dropped. The skipped names are the OpenQASM 2.0 and 3.0 headers, register
declarations, `barrier` and `measure` — `barrier` and `measure` are the identity on
`unitaryDenote`, and the benchmark suites' published gate counts exclude them.

A gate statement is read by `OpenQASMParser.parseLine` first, which covers the
single-gate statements `h`, `x`, `y`, `z`, `s`, `t`, `tdg`, `cx`, `cz` and `rz`.
The statements that denote a list of gates (`sdg`, `cu1`, `cp`, `u1`, `p`, `sx`,
`sxdg`, `swap`, `rx`, `ry`, `U`/`u`/`u3`, `u2`, `ccx`, `ccz`) and `rz` on a
register not named `q` are read here. Every angle is read exactly as a `PiLin`
`a + b·π` by `OpenQASMParser.parseAngleLin`: a multiple of `π`, a decimal in radians,
or their sum.

Together with `include_str` this reads a `.qasm` file at elaboration time, so a
benchmark enters the development as its own source rather than as a hand
transcription.

## Main definitions

* `swapCnotGates`, `sxGates`, `sxdgGates`, `rxGates`, `ryGates`, `uGates` — the
  gate lists of `swap`, `sx`, `sxdg`, `rx`, `ry` and `U`; `OpenQASMImportGates`
  gives their matrices.
* `QGate`, `lowerQ` — the `qelib1.inc` gate statements and the gate list of each;
  `Qelib` gives their matrices.
* `parseAngles` — the angles of a parenthesised argument list.
* `stmtsGo`, `statements` — the statement texts of a source.
* `parseQ` — one statement text to its statements, `none` if unrecognised.
* `parseOps` — one statement text to the gates it denotes, the lowering of `parseQ`.
* `importQ`, `importGates_eq_importQ` — the statements of a whole file, whose lowering
  is the gate list `importGates` reads.
* `importQASM` — a whole file, `none` if any statement text is unrecognised.
* `importQ_join` — completeness: whitespace-separated statement texts read as the
  statements of the texts.
* `qregSize` — the qubit count of the first `qreg` declaration.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.OpenQASMImport

open CatCrypt.Quantum.QCircuit

/-! ## Lexing -/

/-- Every bracketed natural number in a line, left to right: the qubit indices
    of `cx q[0],q[1];` are `[0, 1]`. -/
def bracketIndices (s : String) : List ℕ :=
  let rec go (cs : List Char) (cur : Option ℕ) (acc : List ℕ) : List ℕ :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if c = '[' then go rest (some 0) acc
      else match cur with
        | none => go rest none acc
        | some v =>
          if c.isDigit then go rest (some (v * 10 + (c.toNat - '0'.toNat))) acc
          else if c = ']' then go rest none (v :: acc)
          else go rest none acc
  go s.toList none []

/-- The operation name: the leading run of letters and digits. -/
def opName (s : String) : String :=
  String.ofList (s.trimAsciiStart.copy.toList.takeWhile (fun c => c.isAlphanum))

/-! ## Toffoli-class gates

`ccx` and `ccz` are not `Gate` constructors, so importing one is a choice of
decomposition rather than a read. This is the standard seven-`T` decomposition,
the same one `GateDecomposition.toffoliDecomp` fixes to wires `0,1,2` and the
one VOQC and Nam et al. count against, so a T-count comparison with their
published numbers is like for like. Gate counts are not: the `ccz` form here
conjugates the `ccx` one by two Hadamards rather than cancelling them, so it
costs two gates more than the minimal sequence and the same seven `T`s. -/

/-- The standard seven-`T` Toffoli on three wires. -/
def ccxGates {n : ℕ} (a b t : Fin n) : List (Gate n) :=
  [.H t, .CNOT b t, .Tdg t, .CNOT a t, .T t, .CNOT b t, .Tdg t, .CNOT a t,
   .T b, .T t, .CNOT a b, .H t, .T a, .Tdg b, .CNOT a b]

/-- `CCZ = H_t · CCX · H_t`. -/
def cczGates {n : ℕ} (a b t : Fin n) : List (Gate n) :=
  (Gate.H t :: ccxGates a b t) ++ [Gate.H t]

/-! ## Controlled phase

`cu1(θ)` is the controlled phase `diag(1, 1, 1, e^{iθ})`, which is not a `Gate`
constructor. Writing `R(φ)` for `Gate.RzQ`'s matrix `diag(1, e^{iφ})`, the
phase the sequence below puts on `|c t⟩` is `(θ/2)(c + t − (c ⊕ t))`: zero on
`01` and `10`, and `θ` on `11`. So the decomposition is exact — no global
phase, unlike the `ccx` one above. -/

/-- The controlled phase by the angle `a` between a control and a target. -/
def cphaseGates {n : ℕ} (c t : Fin n) (a : PiLin) : List (Gate n) :=
  [Gate.CNOT c t, Gate.RzQ t (-(a / 2)), Gate.CNOT c t,
   Gate.RzQ c (a / 2), Gate.RzQ t (a / 2)]

/-! ## Swap and single-qubit rotations

None of `swap`, `sx`, `sxdg`, `rx`, `ry` and `U` is a `Gate` constructor. Writing
`P(φ)` for `Gate.RzQ`'s matrix `diag(1, e^{iφ})` and `S†` for `T†;T†`:

* `swap` is three `CNOT`s;
* `sx = H·S·H` and `sxdg = H·S†·H`, exactly;
* `rx(θ)` is `H·P(θ)·H`, which is `e^{iθ/2}·Rx(θ)`, since `H·Z·H = X`;
* `ry(θ)` is `S·H·P(θ)·H·S†`, which is `e^{iθ/2}·Ry(θ)`, since `S·X·S† = Y`;
* `U(θ,φ,λ) = P(φ)·Ry(θ)·P(λ)`, so its list is `e^{iθ/2}·U(θ,φ,λ)`.

`OpenQASMImportGates` proves each matrix statement. -/

/-- The swap of two qubits as three `CNOT`s. -/
def swapCnotGates {n : ℕ} (a b : Fin n) : List (Gate n) :=
  [Gate.CNOT a b, Gate.CNOT b a, Gate.CNOT a b]

/-- `S† = T†·T†` on one qubit. -/
def sdgGates {n : ℕ} (q : Fin n) : List (Gate n) :=
  [Gate.Tdg q, Gate.Tdg q]

/-- `sx = H·S·H`. -/
def sxGates {n : ℕ} (q : Fin n) : List (Gate n) :=
  [Gate.H q, Gate.S q, Gate.H q]

/-- `sxdg = H·S†·H`. -/
def sxdgGates {n : ℕ} (q : Fin n) : List (Gate n) :=
  Gate.H q :: sdgGates q ++ [Gate.H q]

/-- `H·P(a)·H`, the X-rotation by `a` times `e^{i a / 2}`. -/
def rxGates {n : ℕ} (q : Fin n) (a : PiLin) : List (Gate n) :=
  [Gate.H q, Gate.RzQ q a, Gate.H q]

/-- `S·H·P(a)·H·S†`, the Y-rotation by `a` times `e^{i a / 2}`. -/
def ryGates {n : ℕ} (q : Fin n) (a : PiLin) : List (Gate n) :=
  sdgGates q ++ [Gate.H q, Gate.RzQ q a, Gate.H q, Gate.S q]

/-- `P(φ)·(S·H·P(θ)·H·S†)·P(λ)`, OpenQASM's `U(θ, φ, λ)` times `e^{i θ / 2}`. -/
def uGates {n : ℕ} (q : Fin n) (θ φ l : PiLin) : List (Gate n) :=
  Gate.RzQ q l :: ryGates q θ ++ [Gate.RzQ q φ]

/-! ## OpenQASM 2 statements

`QGate n` is a gate statement of `qelib1.inc` on `n` qubits, with exact angles. The
aliases are identified: `u1` is `p`, `cu1` is `cp`, and `U`, `u`, `u3` are `u`.
`lowerQ` is the gate list the importer builds for a statement; `Qelib` states the
`qelib1.inc` matrix of each statement and the global phase of its list. -/

/-- A gate statement of OpenQASM 2's `qelib1.inc`, with exact angles `a + b·π`. -/
inductive QGate (n : ℕ) : Type where
  | h : Fin n → QGate n
  | x : Fin n → QGate n
  | y : Fin n → QGate n
  | z : Fin n → QGate n
  | s : Fin n → QGate n
  | sdg : Fin n → QGate n
  | t : Fin n → QGate n
  | tdg : Fin n → QGate n
  | sx : Fin n → QGate n
  | sxdg : Fin n → QGate n
  | rx : Fin n → PiLin → QGate n
  | ry : Fin n → PiLin → QGate n
  | rz : Fin n → PiLin → QGate n
  | p : Fin n → PiLin → QGate n
  | u : Fin n → PiLin → PiLin → PiLin → QGate n
  | u2 : Fin n → PiLin → PiLin → QGate n
  | cx : Fin n → Fin n → QGate n
  | cz : Fin n → Fin n → QGate n
  | swap : Fin n → Fin n → QGate n
  | cp : Fin n → Fin n → PiLin → QGate n
  | ccx : Fin n → Fin n → Fin n → QGate n
  | ccz : Fin n → Fin n → Fin n → QGate n
  deriving DecidableEq, Repr

/-- The gate list the importer builds for a statement. -/
def lowerQ {n : ℕ} : QGate n → List (Gate n)
  | .h q => [.H q]
  | .x q => [.X q]
  | .y q => [.Y q]
  | .z q => [.Z q]
  | .s q => [.S q]
  | .sdg q => sdgGates q
  | .t q => [.T q]
  | .tdg q => [.Tdg q]
  | .sx q => sxGates q
  | .sxdg q => sxdgGates q
  | .rx q θ => rxGates q θ
  | .ry q θ => ryGates q θ
  | .rz q θ => [.RzQ q θ]
  | .p q θ => [.RzQ q θ]
  | .u q θ φ l => uGates q θ φ l
  | .u2 q φ l => uGates q (1 / 2) φ l
  | .cx c t => [.CNOT c t]
  | .cz c t => [.CZ c t]
  | .swap a b => swapCnotGates a b
  | .cp c t θ => cphaseGates c t θ
  | .ccx a b t => ccxGates a b t
  | .ccz a b t => cczGates a b t

/-- The statement a gate of `OpenQASMParser.parseLine` is read as: `RzQ` is `rz`, the
    other constructors are their namesakes, and the real-angle `Rz` has none. -/
def ofGate? {n : ℕ} : Gate n → Option (QGate n)
  | .H q => some (.h q)
  | .X q => some (.x q)
  | .Y q => some (.y q)
  | .Z q => some (.z q)
  | .T q => some (.t q)
  | .Tdg q => some (.tdg q)
  | .S q => some (.s q)
  | .CNOT c t => some (.cx c t)
  | .CZ c t => some (.cz c t)
  | .RzQ q a => some (.rz q a)
  | .Rz _ _ => none

/-- A statement read from a gate lowers back to that gate. -/
theorem lowerQ_of_ofGate? {n : ℕ} {g : Gate n} {q : QGate n} (h : ofGate? g = some q) :
    lowerQ q = [g] := by
  cases g <;> simp only [ofGate?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-! ## Angles

The parser works on character lists throughout: `String.toNat?` and its
neighbours do not reduce inside a module, so a `#guard` over them would not
evaluate. -/

/-- The text between the first `(` and the next `)`. -/
def parenArg (s : String) : Option (List Char) :=
  match s.toList.dropWhile (fun c => c != '(') with
  | [] => none
  | _ :: rest => some (rest.takeWhile (fun c => c != ')'))

/-- The angle an argument denotes, exactly as `a + b·π`: `OpenQASMParser.parseAngleLin`
    on the argument without its spaces. It reads `0`, `pi`, `-pi`, `k*pi` and each of
    the last three divided by a nonzero natural, a decimal literal in radians, and the
    sum of the two; anything else is `none`, so an angle it cannot read fails the
    import. -/
def angleOf (arg : List Char) : Option PiLin :=
  OpenQASMParser.parseAngleLin (arg.filter (· != ' '))

private theorem space_not_mem_toDigits (d : ℕ) : ' ' ∉ Nat.toDigits 10 d := fun h => by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this; decide

private theorem slash_not_mem_toDigits (d : ℕ) : '/' ∉ Nat.toDigits 10 d := fun h => by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this; decide

private theorem toNat?_toDigits (d : ℕ) : (String.ofList (Nat.toDigits 10 d)).toNat? = some d := by
  rw [← Nat.repr_eq_ofList_toDigits]; exact Nat.toNat?_repr d

private theorem plus_not_mem_toDigits (d : ℕ) : '+' ∉ Nat.toDigits 10 d := fun h => by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this; decide

/-- A text without spaces and `+` that contains `p` is read as the multiple of `π`
that `DQASM.parsePiAngle` reads. -/
private theorem angleOf_of_parsePiAngle {t : List Char} {q : QasmAngle} (hsp : ' ' ∉ t)
    (hpl : '+' ∉ t) (hp : 'p' ∈ t) (h : DQASM.parsePiAngle t = some q) :
    angleOf t = some (PiLin.ofPi q) := by
  have hf : t.filter (· != ' ') = t := List.filter_eq_self.mpr (by grind)
  simp [angleOf, hf, OpenQASMParser.parseAngleLin, DQASM.parseAngle,
    List.splitOn_eq_singleton hpl, hp, h]

/-- `0` is the angle `0`. -/
theorem angleOf_zero : angleOf ['0'] = some 0 := by
  have h0 : (toString (0 : ℚ)).toList = ['0'] := by simp [toString, Int.repr_eq_ite]
  have hr : DQASM.parseRat ['0'] = some 0 := h0 ▸ DQASM.parseRat_toString 0
  simp [angleOf, OpenQASMParser.parseAngleLin, DQASM.parseAngle, List.splitOn_eq_singleton,
    hr, PiLin.ext_iff]

/-- `pi` is the angle `1` (in units of `π`). -/
theorem angleOf_pi : angleOf ['p', 'i'] = some 1 :=
  angleOf_of_parsePiAngle (by simp) (by simp) (by simp)
    (by simp [DQASM.parsePiAngle, DQASM.parseNumPi, List.splitOn_eq_singleton])

/-- `-pi` is the angle `-1` (in units of `π`). -/
theorem angleOf_neg_pi : angleOf ['-', 'p', 'i'] = some (-1) := by
  rw [angleOf_of_parsePiAngle (q := -1) (by simp) (by simp) (by simp)
    (by simp [DQASM.parsePiAngle, DQASM.parseNumPi, List.splitOn_eq_singleton])]
  simp

/-- `pi/d` with `d ≠ 0` is the angle `1/d` (in units of `π`). -/
theorem angleOf_pi_div (d : ℕ) (hd : d ≠ 0) :
    angleOf ('p' :: 'i' :: '/' :: Nat.toDigits 10 d) = some (PiLin.ofPi (1 / (d : QasmAngle))) := by
  have hs : ('p' :: 'i' :: '/' :: Nat.toDigits 10 d).splitOn '/' =
      [['p', 'i'], Nat.toDigits 10 d] := by
    rw [show 'p' :: 'i' :: '/' :: Nat.toDigits 10 d = ['p', 'i'] ++ '/' :: Nat.toDigits 10 d
        by simp, List.splitOn_append_cons_self_of_not_mem (by simp),
      List.splitOn_eq_singleton (slash_not_mem_toDigits d)]
  exact angleOf_of_parsePiAngle (by simp [space_not_mem_toDigits])
    (by simp [plus_not_mem_toDigits]) (by simp)
    (by simp [DQASM.parsePiAngle, hs, DQASM.parseNumPi, toNat?_toDigits, hd])

/-- `-pi/d` with `d ≠ 0` is the angle `-(1/d)` (in units of `π`). -/
theorem angleOf_neg_pi_div (d : ℕ) (hd : d ≠ 0) :
    angleOf ('-' :: 'p' :: 'i' :: '/' :: Nat.toDigits 10 d) =
      some (PiLin.ofPi (-(1 / (d : QasmAngle)))) := by
  have hs : ('-' :: 'p' :: 'i' :: '/' :: Nat.toDigits 10 d).splitOn '/' =
      [['-', 'p', 'i'], Nat.toDigits 10 d] := by
    rw [show '-' :: 'p' :: 'i' :: '/' :: Nat.toDigits 10 d =
        ['-', 'p', 'i'] ++ '/' :: Nat.toDigits 10 d by simp,
      List.splitOn_append_cons_self_of_not_mem (by simp),
      List.splitOn_eq_singleton (slash_not_mem_toDigits d)]
  exact angleOf_of_parsePiAngle (by simp [space_not_mem_toDigits])
    (by simp [plus_not_mem_toDigits]) (by simp)
    (by simp [DQASM.parsePiAngle, hs, DQASM.parseNumPi, toNat?_toDigits, hd, neg_div])

/-- The comma-separated fields of an argument list, left to right. -/
def splitCommas (cs : List Char) : List (List Char) :=
  let rec go (cs cur : List Char) (acc : List (List Char)) : List (List Char) :=
    match cs with
    | [] => (cur.reverse :: acc).reverse
    | c :: rest => if c = ',' then go rest [] (cur.reverse :: acc) else go rest (c :: cur) acc
  go cs [] []

/-- The angles of a parenthesised argument list, `none` if any field is
    unreadable. -/
def parseAngles (s : String) : Option (List PiLin) :=
  (parenArg s).bind fun arg => (splitCommas arg).mapM angleOf

#guard parseAngles "u3(pi/2, 0, -pi) q[0];" = some [1 / 2, 0, -1]
#guard parseAngles "u3(0.1,0.2,0.3) q[1];" = some [⟨1 / 10, 0⟩, ⟨1 / 5, 0⟩, ⟨3 / 10, 0⟩]
#guard parseAngles "rz(0.5+pi/4) q[0];" = some [⟨1 / 2, 1 / 4⟩]
#guard parseAngles "rx(-1.5E-1) q[0];" = some [⟨-3 / 20, 0⟩]

/-! ## Lines -/

/-- Declarations and annotations an import skips by name. `barrier` and
    `measure` are the identity on `unitaryDenote`. -/
def isSkipped (name : String) : Bool :=
  name == "OPENQASM" || name == "include" || name == "qreg" || name == "creg" ||
    name == "qubit" || name == "bit" || name == "barrier" || name == "measure" ||
    name == "gate" || name == "opaque"

/-- The statement of a line that `OpenQASMParser.parseLine` does not read, dispatched on
    the operation name `name` and the bracketed indices `idx`, with the parenthesised
    argument `arg` and the angles `angs`; `none` if it is not a statement. `u1` is read
    as `p`, `cu1` as `cp`, and `U`, `u3` as `u`. -/
def parseQRest (n : ℕ) (name : String) (idx : List ℕ) (arg : Option (List Char))
    (angs : Option (List PiLin)) : Option (QGate n) :=
  let fin? : ℕ → Option (Fin n) := fun i => if h : i < n then some ⟨i, h⟩ else none
  match name, idx with
  | "sdg", [a] => (fin? a).map .sdg
  | "cu1", [a, b] | "cp", [a, b] => do
      let c ← fin? a; let t ← fin? b
      let arg ← arg
      let ang ← angleOf arg
      some (.cp c t ang)
  | "rz", [a] => do
      let q ← fin? a
      let arg ← arg
      let ang ← angleOf arg
      some (.rz q ang)
  | "u1", [a] | "p", [a] => do
      let q ← fin? a
      let arg ← arg
      let ang ← angleOf arg
      some (.p q ang)
  | "sx", [a] => (fin? a).map .sx
  | "sxdg", [a] => (fin? a).map .sxdg
  | "swap", [a, b] => do let x ← fin? a; let y ← fin? b; some (.swap x y)
  | "rx", [a] => do
      let q ← fin? a
      match ← angs with
      | [θ] => some (.rx q θ)
      | _ => none
  | "ry", [a] => do
      let q ← fin? a
      match ← angs with
      | [θ] => some (.ry q θ)
      | _ => none
  | "U", [a] | "u", [a] | "u3", [a] => do
      let q ← fin? a
      match ← angs with
      | [θ, φ, l] => some (.u q θ φ l)
      | _ => none
  | "u2", [a] => do
      let q ← fin? a
      match ← angs with
      | [φ, l] => some (.u2 q φ l)
      | _ => none
  | "ccx", [a, b, t] => do
      let x ← fin? a; let y ← fin? b; let z ← fin? t; some (.ccx x y z)
  | "ccz", [a, b, t] => do
      let x ← fin? a; let y ← fin? b; let z ← fin? t; some (.ccz x y z)
  | _, _ => none

/-- The statements of one statement text (its leading whitespace dropped): `some []` for a
    declaration the importer skips by name, `some [g]` for a gate statement, `none` for a
    text this importer does not recognise. A text `OpenQASMParser.parseLine` reads is the
    statement of its gate (`ofGate?`); any other text is read by `parseQRest`. -/
def parseQ (n : ℕ) (line : String) : Option (List (QGate n)) :=
  let s := String.ofList (line.toList.dropWhile Char.isWhitespace)
  let name := opName s
  if isSkipped name then some []
  else match OpenQASMParser.parseLine n s with
  | some g => (ofGate? g).map ([·])
  | none =>
    (parseQRest n name (bracketIndices s) (parenArg s) (parseAngles s)).map ([·])

/-- `parseQ` reads a text after its leading whitespace. -/
theorem parseQ_append_ws (n : ℕ) (w t : List Char) (hw : ∀ c ∈ w, c.isWhitespace = true) :
    parseQ n (String.ofList (w ++ t)) = parseQ n (String.ofList t) := by
  have h : (w ++ t).dropWhile Char.isWhitespace = t.dropWhile Char.isWhitespace := by
    induction w with
    | nil => rfl
    | cons c w ih => grind [List.dropWhile_cons_of_pos]
  simp only [parseQ, String.toList_ofList, h]

/-- Every gate an optional result carries is the gate of a statement. -/
def StmtGates {n : ℕ} (o : Option (Gate n)) : Prop :=
  ∀ g, o = some g → (ofGate? g).isSome

/-- `none` carries no gate. -/
theorem stmtGates_none {n : ℕ} : StmtGates (none : Option (Gate n)) := by
  intro g h; cases h

/-- A conditional of two results whose gates are statement gates. -/
theorem stmtGates_ite {n : ℕ} {c : Prop} [Decidable c] {x y : Option (Gate n)}
    (hx : StmtGates x) (hy : StmtGates y) : StmtGates (if c then x else y) := by
  split <;> assumption

/-- A dependent conditional of two results whose gates are statement gates. -/
theorem stmtGates_dite {n : ℕ} {c : Prop} [Decidable c] {x : c → Option (Gate n)}
    {y : ¬c → Option (Gate n)} (hx : ∀ h, StmtGates (x h)) (hy : ∀ h, StmtGates (y h)) :
    StmtGates (if h : c then x h else y h) := by
  split
  · exact hx _
  · exact hy _

/-- A bind into results whose gates are statement gates. -/
theorem stmtGates_bind {n : ℕ} {α : Type} {o : Option α} {f : α → Option (Gate n)}
    (h : ∀ a, StmtGates (f a)) : StmtGates (o >>= f) := by
  intro g hg
  cases o with
  | none => cases hg
  | some a => exact h a g hg

/-- A single statement gate. -/
theorem stmtGates_some {n : ℕ} {g : Gate n} (h : (ofGate? g).isSome) : StmtGates (some g) := by
  intro g' hg; cases hg; exact h

/-- An optional `RzQ` gate is a statement gate (`rz`). -/
theorem stmtGates_map_rzQ {n : ℕ} (i : Fin n) (o : Option PiLin) :
    StmtGates (o.map (Gate.RzQ i)) := by
  intro g hg
  cases o with
  | none => cases hg
  | some a => cases hg; rfl

/-- Every gate `OpenQASMParser.parseLine` reads is the gate of a statement: it never reads
    the real-angle `Rz`. -/
theorem stmtGates_parseLine (n : ℕ) (s : String) :
    StmtGates (OpenQASMParser.parseLine n s) := by
  unfold OpenQASMParser.parseLine OpenQASMParser.parseRz OpenQASMParser.rzGateOf
  dsimp only
  repeat' first
    | with_reducible apply stmtGates_ite
    | (with_reducible apply stmtGates_dite <;> intro)
    | (with_reducible apply stmtGates_bind; intro)
    | with_reducible exact stmtGates_none
    | with_reducible exact stmtGates_map_rzQ _ _
    | split
  all_goals exact stmtGates_some rfl

/-- The gates a line denotes: the lowering (`lowerQ`) of its statements, `none` for a
    line this importer does not recognise. `sdg` has no `Gate` constructor and is the
    two-gate `T†;T†`, and `u2(φ,λ)` is `U(π/2,φ,λ)`. -/
def parseOps (n : ℕ) (line : String) : Option (List (Gate n)) :=
  (parseQ n line).map (·.flatMap lowerQ)

/-! ## Files -/

/-- The statement texts of the characters `cs`, given the texts `acc` read before (in
    reverse order), the current text `cur` (reversed) and whether `cur` is blank. A text
    ends at its `;`, which it keeps. A `//` where the current text is blank begins a
    comment: the comment, up to the end of its line, and the blank text before it are
    dropped. The second component is whether the text after the last `;` is blank. -/
def stmtsGo (cs cur : List Char) (blank : Bool) (acc : List (List Char)) :
    List (List Char) × Bool :=
  match cs with
  | [] => (acc.reverse, blank)
  | c :: rest =>
    if c = ';' then stmtsGo rest [] true ((c :: cur).reverse :: acc)
    else if blank = true ∧ c = '/' ∧ rest.head? = some '/' then
      stmtsGo (rest.dropWhile (· != '\n')) [] true acc
    else stmtsGo rest (c :: cur) (blank && c.isWhitespace) acc
termination_by cs.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals grind [List.dropWhile_suffix, List.IsSuffix.length_le]

/-- The statement texts of a source, each with its `;` and without comments; `none` if
    non-blank text follows the last `;`. -/
def statements (cs : List Char) : Option (List (List Char)) :=
  let r := stmtsGo cs [] true []
  if r.2 then some r.1 else none

/-- The statements of a whole file, `none` if any statement text is unrecognised or
    non-blank text follows the last `;`. -/
def importQ (n : ℕ) (src : String) : Option (List (QGate n)) :=
  (statements src.toList).bind fun ss =>
    (ss.mapM fun s => parseQ n (String.ofList s)).map List.flatten

/-- **`parseOps` dispatched by statement.** A skipped declaration carries no gate, a text
    `OpenQASMParser.parseLine` reads is its one gate, and any other text is the lowering of
    the statement `parseQRest` reads. -/
theorem parseOps_eq (n : ℕ) (line : String) :
    let s := String.ofList (line.toList.dropWhile Char.isWhitespace)
    parseOps n line =
      if isSkipped (opName s) then some []
      else match OpenQASMParser.parseLine n s with
      | some g => some [g]
      | none => (parseQRest n (opName s) (bracketIndices s) (parenArg s)
          (parseAngles s)).map lowerQ := by
  intro s
  unfold parseOps parseQ
  dsimp only
  split_ifs
  · rfl
  · cases h : OpenQASMParser.parseLine n s with
    | none => simp [s, Option.map_map, Function.comp_def]
    | some g =>
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (stmtGates_parseLine n _ g h)
      simp [hq, lowerQ_of_ofGate? hq]

/-- The gates of a whole file, `none` if any statement text is unrecognised or non-blank
    text follows the last `;`: the gates of each statement, concatenated once (linear in
    the file, where appending statement by statement is quadratic). -/
def importGates (n : ℕ) (src : String) : Option (List (Gate n)) :=
  (statements src.toList).bind fun ss =>
    (ss.mapM fun s => parseOps n (String.ofList s)).map List.flatten

/-- The gates of a file are the lowering of its statements. -/
theorem importGates_eq_importQ (n : ℕ) (src : String) :
    importGates n src = (importQ n src).map (·.flatMap lowerQ) := by
  unfold importGates importQ parseOps
  cases statements src.toList with
  | none => rfl
  | some ls =>
  simp only [Option.bind_some]
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    cases h : parseQ n (String.ofList l) <;>
      cases h' : ls.mapM (fun s => parseQ n (String.ofList s)) <;>
      simp_all [List.mapM_cons, List.flatMap_append]
    obtain ⟨a, ha, ha'⟩ := ih
    simp [ha, ha']

/-- **The circuit a file denotes**, `none` if any statement text is unrecognised. -/
def importQASM (n : ℕ) (src : String) : Option (Circuit n) :=
  (importGates n src).map Circuit.ofList

/-- The size of the first `qreg` declaration, `qreg q[n];`, among the statement texts of
    the source: the qubit count `importQASM` is called with. -/
def qregSize (src : String) : Option ℕ := do
  let l ← (stmtsGo src.toList [] true []).1.find?
    (fun l => (l.dropWhile Char.isWhitespace).take 4 == "qreg".toList)
  let inner := ((l.dropWhile (· != '[')).drop 1).takeWhile (· != ']')
  OpenQASMParser.natOfDigits (inner.filter (fun c => !c.isWhitespace))

/-! ## Completeness

A source made of statement texts, each preceded by whitespace, with whitespace at its end,
is split into exactly those texts with their preceding whitespace. A statement text
(`IsStmtText`) starts with a character that is not whitespace, `/` or `;`, and has exactly
one `;`, at its end. -/

/-- A text the scanner `stmtsGo` reads as one statement: a first character that is not
    whitespace, `/` or `;`, then text without `;`, then `;`. -/
def IsStmtText (t : List Char) : Prop :=
  ∃ c u, t = c :: (u ++ [';']) ∧ c.isWhitespace = false ∧ c ≠ '/' ∧ c ≠ ';' ∧ ';' ∉ u

/-- The scanner adds whitespace in a blank state to the current text. -/
theorem stmtsGo_ws (w r cur : List Char) (acc : List (List Char))
    (hw : ∀ c ∈ w, c.isWhitespace = true) :
    stmtsGo (w ++ r) cur true acc = stmtsGo r (w.reverse ++ cur) true acc := by
  induction w generalizing cur with
  | nil => rfl
  | cons c w ih =>
    have hc := hw c (by simp)
    have h1 : c ≠ ';' := by rintro rfl; simp at hc
    have h2 : c ≠ '/' := by rintro rfl; simp at hc
    rw [List.cons_append, stmtsGo]
    simp only [h1, h2, hc, false_and, and_false, ite_false, Bool.and_self]
    rw [ih _ (fun d hd => hw d (by simp [hd]))]
    simp

/-- The scanner reads the rest of a statement text in a non-blank state. -/
theorem stmtsGo_body (u r cur : List Char) (acc : List (List Char)) (hu : ';' ∉ u) :
    stmtsGo (u ++ ';' :: r) cur false acc =
      stmtsGo r [] true ((cur.reverse ++ u ++ [';']) :: acc) := by
  induction u generalizing cur with
  | nil => simp [stmtsGo]
  | cons c u ih =>
    have h1 : c ≠ ';' := by rintro rfl; simp at hu
    rw [List.cons_append, stmtsGo]
    simp only [h1, Bool.false_eq_true, false_and, ite_false, Bool.false_and]
    rw [ih _ (fun h => hu (by simp [h]))]
    simp

/-- The scanner reads a statement text after whitespace as one statement. -/
theorem stmtsGo_stmt (w t r : List Char) (acc : List (List Char))
    (hw : ∀ c ∈ w, c.isWhitespace = true) (ht : IsStmtText t) :
    stmtsGo (w ++ t ++ r) [] true acc = stmtsGo r [] true ((w ++ t) :: acc) := by
  obtain ⟨c, u, rfl, hc, h1, h2, hu⟩ := ht
  rw [List.append_assoc, stmtsGo_ws _ _ _ _ hw, List.cons_append, stmtsGo]
  simp only [h1, h2, hc, false_and, and_false, ite_false, Bool.true_and]
  rw [List.append_assoc, List.singleton_append, stmtsGo_body _ _ _ _ hu]
  simp

/-- The scanner splits whitespace-separated statement texts into those texts. -/
theorem stmtsGo_join (ps : List (List Char × List Char)) (last : List Char)
    (acc : List (List Char))
    (hw : ∀ p ∈ ps, ∀ c ∈ p.1, c.isWhitespace = true)
    (hlast : ∀ c ∈ last, c.isWhitespace = true) (ht : ∀ p ∈ ps, IsStmtText p.2) :
    stmtsGo (ps.flatMap (fun p => p.1 ++ p.2) ++ last) [] true acc =
      (acc.reverse ++ ps.map (fun p => p.1 ++ p.2), true) := by
  induction ps generalizing acc with
  | nil =>
    rw [List.flatMap_nil, List.nil_append, ← List.append_nil last, stmtsGo_ws _ _ _ _ hlast]
    simp [stmtsGo]
  | cons p ps ih =>
    rw [List.flatMap_cons, List.append_assoc,
      stmtsGo_stmt _ _ _ _ (hw p (by simp)) (ht p (by simp)),
      ih _ (fun q hq => hw q (by simp [hq])) (fun q hq => ht q (by simp [hq]))]
    simp

/-- **Completeness of the reader.** A source made of statement texts, each preceded by
    whitespace, and whitespace at its end, reads as the statements `parseQ` reads from
    the texts, in order: one statement a line, several a line and any other whitespace
    between them. -/
theorem importQ_join (n : ℕ) (ps : List (List Char × List Char)) (last : List Char)
    (hw : ∀ p ∈ ps, ∀ c ∈ p.1, c.isWhitespace = true)
    (hlast : ∀ c ∈ last, c.isWhitespace = true) (ht : ∀ p ∈ ps, IsStmtText p.2) :
    importQ n (String.ofList (ps.flatMap (fun p => p.1 ++ p.2) ++ last)) =
      (ps.mapM fun p => parseQ n (String.ofList p.2)).map List.flatten := by
  rw [importQ, statements, String.toList_ofList, stmtsGo_join ps last [] hw hlast ht]
  simp only [List.reverse_nil, List.nil_append, ite_true, Option.bind_some]
  congr 1
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [parseQ_append_ws n _ _ (hw p (by simp)),
      ih (fun q hq => hw q (by simp [hq])) (fun q hq => ht q (by simp [hq]))]

/-- The circuit a file denotes, or the empty circuit. Used where the import is
    pinned by a `#guard` on the gate count, so a failure is visible. -/
def importQASM! (n : ℕ) (src : String) : Circuit n :=
  (importQASM n src).getD .empty

/-! ## The importer reads what it is given -/

private def bellSrc : String :=
  "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[2];\ncreg c[2];\nh q[0];\ncx q[0],q[1];\nmeasure q[0] -> c[0];"

#guard (importQASM 2 bellSrc).map Circuit.gateCount = some 2

private def decimalSrc : String :=
  "OPENQASM 2.0;\nqreg q[2];\nh q[0];\nu3(0.1,0.2,0.3) q[1];"

-- Decimal angles are read exactly: 1 + 8 gates.
#guard (importQASM 2 decimalSrc).map Circuit.gateCount = some 9

private def rzDecimalSrc : String :=
  "OPENQASM 3.0;\nqubit[1] q;\nrz(0.25) q[0];\nrz(-0.25) q[0];"

/-- The angle of an `RzQ` gate, `none` for any other gate. -/
def rzQAngle? {n : ℕ} : Gate n → Option PiLin
  | .RzQ _ a => some a
  | _ => none

-- Two `RzQ` gates with the radian angles `1/4` and `-1/4`.
#guard (importGates 1 rzDecimalSrc).map (·.map rzQAngle?) =
  some [some ⟨1 / 4, 0⟩, some ⟨-1 / 4, 0⟩]

private def unknownSrc : String :=
  "OPENQASM 2.0;\nqreg q[2];\nh q[0];\nu3(theta,0,0) q[1];"

-- An angle the importer cannot read is a failed import, not a dropped line.
#guard (importQASM 2 unknownSrc).isNone

private def rotSrc : String :=
  "OPENQASM 2.0;\nqreg q[2];\nsx q[0];\nsxdg q[1];\nswap q[0],q[1];\nry(pi/4) q[0];\nu3(pi/2,0,pi) q[1];\nu2(0,pi) q[0];"

-- 3 + 4 + 3 + 6 + 8 + 8 gates.
#guard (importQASM 2 rotSrc).map Circuit.gateCount = some 32

private def rxPhaseSrc : String :=
  "OPENQASM 2.0;\nqreg q[2];\nrx(pi/4) q[0];\np(pi/2) q[1];"

-- 3 + 1 gates.
#guard (importQASM 2 rxPhaseSrc).map Circuit.gateCount = some 4

end CatCrypt.Quantum.OpenQASMImport
