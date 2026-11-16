/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.KAKFloat
public import CatCrypt.Quantum.PiLin
public import Std.Data.HashSet

/-!
# A `Float` Dawson–Nielsen generator of words over `H`, `T`, `T†`

Executable `Float` numerics that propose, for a one-qubit gate, a word over `H`, `T`, `T†`
and a global phase. The output is untrusted: it is certified, gate by gate, by
`GateBall.checkRun`, and a proposal whose certificate exceeds the threshold of the checked pass
is rejected there. Nothing here is proved.

The algorithm is the Solovay–Kitaev recursion in the form of Dawson and Nielsen. Matrices are
normalised to `SU(2)` (`su2`) and handled as `2 × 2` complex `Float` matrices (`KAKFloat.M2`).

* The base net is every reduced word over `H`, `T`, `T†` of length at most `L₀` (no `H H`, no
  `T T†`, no `T⁸`), enumerated by breadth first search and deduplicated modulo global phase
  (`buildNet`). `nearest` is a linear scan by the overlap `|Re tr(A† B)|`.
* One recursion step approximates `U` by `Ũ` at the previous level, writes the residual
  `Δ = U Ũ†` as a balanced group commutator `V W V† W†` of two rotations by the same angle
  `φ` with `sin(θ/2) = 2 sin²(φ/2) √(1 - sin⁴(φ/2))` (`balancedCommutator`), conjugated to
  the axis of `Δ`, and approximates `V` and `W` at the previous level (`sk`). The step is kept
  only when it brings the approximation closer to `U`.
* The global phase is `arg tr(U† M(w))` for the matrix `M(w)` of the word `w`, rounded to a
  dyadic rational (`skGenWith`).

Words list gates in application order, the head first, as `listMatrix` does. `X`, `Y`, `Z`, `S`
have fixed words (`S = T T`, `Z = T⁴`, `X = H Z H`, `Y = -i X Z` up to the phase `-π/2`).

## Main definitions

* `Net`, `buildNet` — the deduplicated table of short words.
* `balancedCommutator` — the pair `(V', W')` with `V' W' V'† W'† = Δ` up to sign.
* `distUpToPhase` — the `Float` operator distance of two unitaries up to global phase.
* `sk` — the recursion to a given depth.
* `skGenFloat` — the generator, of type `Gate 1 → Option (List (Gate 1) × PiLin)`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Synthesis.KAKFloat

namespace CatCrypt.Quantum.Synthesis.SK

/-! ## Conversions -/

/-- The nearest integer of a `Float`, saturating beyond the range of `UInt64`. -/
def floatToInt (x : Float) : Int :=
  let y := x.round
  if y < 0 then -(Int.ofNat (-y).toUInt64.toNat) else Int.ofNat y.toUInt64.toNat

/-- A `Float` approximation of a rational. -/
def ratToFloat (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- The nearest rational with denominator `2 ^ bits`. -/
def floatToDyadic (x : Float) (bits : Nat) : ℚ :=
  (floatToInt (x * Float.ofNat (2 ^ bits)) : ℚ) / ((2 ^ bits : Nat) : ℚ)

/-- The angle `a + b π` of a `PiLin` as a `Float`. -/
def piLinToFloat (p : PiLin) : Float := ratToFloat p.a + ratToFloat p.b * piF

/-! ## Matrices of letters and words -/

/-- The conjugate transpose. -/
def dag (A : M2) : M2 := ⟨A.a00.conj, A.a10.conj, A.a01.conj, A.a11.conj⟩

/-- The matrix of a letter: `0` is `H`, `1` is `T`, `2` is `T†`. -/
def letterMat : Nat → M2
  | 0 => M2.had
  | 1 => M2.rz (piF / 4)
  | _ => M2.rz (-(piF / 4))

/-- The inverse letter: `H` is its own inverse, `T` and `T†` are exchanged. -/
def invLetter : Nat → Nat
  | 0 => 0
  | 1 => 2
  | _ => 1

/-- The inverse word: the letters inverted and reversed. -/
def invWord (w : List Nat) : List Nat := (w.map invLetter).reverse

/-- The matrix of a word whose head is applied first. -/
def wordMat (w : List Nat) : M2 := w.foldl (fun acc x => letterMat x * acc) M2.id

/-- The gate of a letter on qubit `0`. -/
def letterGate : Nat → Gate 1
  | 0 => .H 0
  | 1 => .T 0
  | _ => .Tdg 0

/-- The word as a list of one-qubit gates. -/
def wordGates (w : List Nat) : List (Gate 1) := w.map letterGate

/-! ## `SU(2)` as quaternions -/

/-- The element `w I - i (x σx + y σy + z σz)` of `U(2)`; unit quaternions are `SU(2)`. -/
structure Quat where
  /-- The scalar part. -/
  w : Float
  /-- The `σx` coefficient. -/
  x : Float
  /-- The `σy` coefficient. -/
  y : Float
  /-- The `σz` coefficient. -/
  z : Float
  deriving Inhabited, Repr

namespace Quat

/-- The coefficients of a matrix of the form `w I - i (x σx + y σy + z σz)`. -/
def ofM2 (A : M2) : Quat :=
  ⟨(A.a00.re + A.a11.re) / 2, -(A.a01.im + A.a10.im) / 2, -(A.a01.re - A.a10.re) / 2,
    -(A.a00.im - A.a11.im) / 2⟩

/-- The matrix `w I - i (x σx + y σy + z σz)`. -/
def toM2 (q : Quat) : M2 := ⟨⟨q.w, -q.z⟩, ⟨-q.y, -q.x⟩, ⟨q.y, -q.x⟩, ⟨q.w, q.z⟩⟩

/-- The length of the vector part. -/
def vnorm (q : Quat) : Float := Float.sqrt (q.x * q.x + q.y * q.y + q.z * q.z)

end Quat

/-- The matrix divided by a square root of its determinant, an element of `SU(2)` when the
matrix is unitary. -/
def su2 (A : M2) : M2 := M2.smul (C.inv (C.sqrt A.det)) A

/-- The matrix or its negative, with nonnegative scalar part. -/
def posScalar (A : M2) : M2 :=
  if (Quat.ofM2 A).w < 0 then M2.smul (C.ofReal (-1)) A else A

/-- The rotation by `φ` about the `x` axis. -/
def rotX (φ : Float) : M2 := Quat.toM2 ⟨Float.cos (φ / 2), Float.sin (φ / 2), 0, 0⟩

/-- The rotation by `φ` about the `y` axis. -/
def rotY (φ : Float) : M2 := Quat.toM2 ⟨Float.cos (φ / 2), 0, Float.sin (φ / 2), 0⟩

/-- An element of `SU(2)` that conjugates the axis `a` onto the axis `b`, both unit vectors. -/
def alignAxes (a b : Float × Float × Float) : M2 :=
  let d := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
  if d < -1 + 1e-12 then
    -- opposite axes: rotate by `π` about a vector orthogonal to `a`
    let e : Float × Float × Float :=
      if Float.abs a.1 < 0.9 then (1, 0, 0) else (0, 1, 0)
    let p : Float × Float × Float :=
      (a.2.1 * e.2.2 - a.2.2 * e.2.1, a.2.2 * e.1 - a.1 * e.2.2, a.1 * e.2.1 - a.2.1 * e.1)
    let n := Float.sqrt (p.1 * p.1 + p.2.1 * p.2.1 + p.2.2 * p.2.2)
    Quat.toM2 ⟨0, p.1 / n, p.2.1 / n, p.2.2 / n⟩
  else
    let cx := a.2.1 * b.2.2 - a.2.2 * b.2.1
    let cy := a.2.2 * b.1 - a.1 * b.2.2
    let cz := a.1 * b.2.1 - a.2.1 * b.1
    let n := Float.sqrt ((1 + d) * (1 + d) + cx * cx + cy * cy + cz * cz)
    Quat.toM2 ⟨(1 + d) / n, cx / n, cy / n, cz / n⟩

/-- The balanced group commutator of Dawson–Nielsen. For `Δ` in `SU(2)` that is a rotation by
`θ > 0`, returns `(V', W')` in `SU(2)` with `V' W' V'† W'† = ±Δ`, where `V'`, `W'` are
conjugates of the rotations by the same angle `φ` about the `x` and `y` axes, with
`sin (φ/2)² = sin (θ/4)`. Returns `none` when `Δ` is the identity up to sign. -/
def balancedCommutator (Δ : M2) : Option (M2 × M2) :=
  let q := Quat.ofM2 (posScalar Δ)
  let r := q.vnorm
  if r < 1e-15 then none
  else
    let θ := 2 * Float.atan2 r q.w
    let φ := 2 * Float.asin (Float.sqrt (Float.sin (θ / 4)))
    let V := rotX φ
    let W := rotY φ
    let c := Quat.ofM2 (posScalar (V * W * dag V * dag W))
    let cr := c.vnorm
    if cr < 1e-15 then none
    else
      let S := alignAxes (c.x / cr, c.y / cr, c.z / cr) (q.x / r, q.y / r, q.z / r)
      some (S * V * dag S, S * W * dag S)

/-! ## The base net -/

/-- A table of words (letters in application order) with their `SU(2)` matrices. -/
abbrev Net := Array (List Nat × M2)

/-- A key identifying a matrix modulo global phase up to rounding: the quaternion of its
`SU(2)` normalisation, with the sign fixed by the first coefficient of modulus above `10⁻³`,
rounded to the grid `10⁻⁵`. -/
def phaseKey (A : M2) : List Int :=
  let q := Quat.ofM2 (su2 A)
  let v := [q.w, q.x, q.y, q.z]
  let s : Float :=
    match v.find? (fun t => Float.abs t > 1e-3) with
    | some t => if t < 0 then -1 else 1
    | none => 1
  v.map fun t => floatToInt (s * t * 1e5)

/-- The number of leading entries of a list equal to `x`. -/
def leadRun (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: r => if y == x then leadRun x r + 1 else 0

/-- The letter `x` may extend the reversed word `r` (last letter first) to a reduced word:
no `H H`, no `T T†`, no `T†T`, no `T⁸`, no `T†⁸`. -/
def extendable (r : List Nat) (x : Nat) : Bool :=
  match x with
  | 0 => r.head? != some 0
  | 1 => r.head? != some 2 && leadRun 1 r < 7
  | _ => r.head? != some 1 && leadRun 2 r < 7

/-- The reduced words over `H`, `T`, `T†` of length at most `L₀`, deduplicated modulo global
phase by `phaseKey`, shortest first. -/
def buildNet (L₀ : Nat) : Net := Id.run do
  let mut seen : Std.HashSet (List Int) := (∅ : Std.HashSet (List Int)).insert (phaseKey M2.id)
  let mut net : Net := #[([], su2 M2.id)]
  let mut frontier : Array (List Nat × M2) := #[([], M2.id)]
  for _ in [0:L₀] do
    let mut next : Array (List Nat × M2) := #[]
    for (r, m) in frontier do
      for x in [0, 1, 2] do
        if extendable r x then
          let m' := letterMat x * m
          let k := phaseKey m'
          if !seen.contains k then
            seen := seen.insert k
            next := next.push (x :: r, m')
            net := net.push ((x :: r).reverse, su2 m')
    frontier := next
  return net

/-- The overlap `|Re tr(A† B)|` of two matrices of `SU(2)`; it is `2` exactly when they agree
up to sign. -/
def overlap (A B : M2) : Float :=
  let t := A.a00.re * B.a00.re + A.a00.im * B.a00.im + A.a01.re * B.a01.re
    + A.a01.im * B.a01.im + A.a10.re * B.a10.re + A.a10.im * B.a10.im
    + A.a11.re * B.a11.re + A.a11.im * B.a11.im
  Float.abs t

/-- The operator-norm distance `min_φ ‖A − e^{iφ} B‖` of two unitary matrices up to global
phase, `√(2 − |Re tr(A'† B')|)` for their `SU(2)` normalisations `A'`, `B'`. -/
def distUpToPhase (A B : M2) : Float :=
  Float.sqrt (max 0 (2 - overlap (su2 A) (su2 B)))

/-- The entry of the net with the largest overlap with `U`. -/
def nearest (net : Net) (U : M2) : List Nat × M2 :=
  let init : List Nat × M2 × Float := ([], M2.id, -1)
  let best := net.foldl (init := init) fun acc e =>
    let o := overlap e.2 U
    if o > acc.2.2 then (e.1, e.2, o) else acc
  (best.1, best.2.1)

/-! ## The recursion -/

/-- The Dawson–Nielsen recursion to depth `n` for `U` in `SU(2)`: the word, in application
order, and its `SU(2)` matrix. Depth `0` is the nearest entry of the net. A step whose
commutator correction has no larger overlap with `U` than the approximation of the previous
level returns that approximation, so the distance to `U` does not increase with the depth. -/
def sk (net : Net) : Nat → M2 → List Nat × M2
  | 0, U => nearest net U
  | n + 1, U =>
    let (wU, MU) := sk net n U
    match balancedCommutator (U * dag MU) with
    | none => (wU, MU)
    | some (V', W') =>
      let (wV, MV) := sk net n V'
      let (wW, MW) := sk net n W'
      let M := MV * MW * dag MV * dag MW * MU
      if overlap M U > overlap MU U then
        (wU ++ invWord wW ++ invWord wV ++ wW ++ wV, M)
      else (wU, MU)

/-! ## The generator -/

/-- The matrix of a one-qubit gate, `none` for the real-angle `Rz` and two-qubit gates. -/
def gateMatF : Gate 1 → Option M2
  | .H _ => some M2.had
  | .T _ => some (M2.rz (piF / 4))
  | .Tdg _ => some (M2.rz (-(piF / 4)))
  | .S _ => some (M2.rz (piF / 2))
  | .Z _ => some (M2.rz piF)
  | .X _ => some ⟨C.zero, C.one, C.one, C.zero⟩
  | .Y _ => some ⟨C.zero, ⟨0, -1⟩, ⟨0, 1⟩, C.zero⟩
  | .RzQ _ a => some (M2.rz (piLinToFloat a))
  | _ => none

/-- The phase `φ` with `M ≈ e^{iφ} U`, from `arg tr(U† M)`, as a dyadic angle. -/
def phaseOf (U M : M2) : PiLin :=
  let t := (dag U * M)
  ⟨floatToDyadic (C.arg (t.a00 + t.a11)) 40, 0⟩

/-- The generator over a given net, to a given recursion depth. `X`, `Y`, `Z`, `S` have fixed
words, `RzQ` is approximated by `sk`, and the other gates give `none` (`H`, `T`, `T†` give
themselves). -/
def skGenWith (net : Net) (depth : Nat) : Gate 1 → Option (List (Gate 1) × PiLin)
  | .H i => some ([.H i], 0)
  | .T i => some ([.T i], 0)
  | .Tdg i => some ([.Tdg i], 0)
  | .S _ => some (wordGates [1, 1], 0)
  | .Z _ => some (wordGates [1, 1, 1, 1], 0)
  | .X _ => some (wordGates [0, 1, 1, 1, 1, 0], 0)
  | .Y _ => some (wordGates ([1, 1, 1, 1] ++ [0, 1, 1, 1, 1, 0]), ⟨0, -1 / 2⟩)
  | g@(.RzQ _ _) =>
    match gateMatF g with
    | none => none
    | some U =>
      let (w, _) := sk net depth (su2 U)
      some (wordGates w, phaseOf U (wordMat w))
  | _ => none

/-- The Float Dawson–Nielsen generator: the net of the reduced words of length at most `L₀`
(built once per application to `L₀`), recursion depth `depth`. It has the type of a word
generator of the checked pass, `Gate 1 → Option (List (Gate 1) × PiLin)`; its output is
certified by `GateBall.checkRun`. -/
def skGenFloat (L₀ depth : Nat) : Gate 1 → Option (List (Gate 1) × PiLin) :=
  skGenWith (buildNet L₀) depth

end CatCrypt.Quantum.Synthesis.SK
