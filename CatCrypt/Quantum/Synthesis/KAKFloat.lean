/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.PiLin

/-!
# Floating-point angles for the two-qubit KAK templates

Executable `Float` numerics that fit the angles of the templates `kak0`, `kak1`, `kak2`
(`KAKSmall.lean`) and `kak3` (`KAK.lean`) to a two-qubit unitary. The algorithm is the
construction of the proofs of `kak{k}_exists`: in the magic basis `M` the unitary `U` is
`c · O₁ · diag f · Pᵀ` with `O₁, P ∈ SO(4)` (`canonical`); the class of `U` is the smallest
`k` for which a vector of the Weyl orbit of `f` satisfies `KAKSmall.classPhase k` within a
tolerance (`classify`); each local factor `M O M†` is split as `A ⊗ B` (`kronFactor`) and
each of `A, B` as a ZYZ product (`zyz`).

The output carries no proof: its check is `phaseDist U (templateMatF k θ)`, the Frobenius
distance of `U` from the template up to the best global phase. Existence of exact angles
is `kakPassSmall_correct` (`KAKPassSmall.lean`).

Conventions: a `4 × 4` index is `2 · (bit of qubit i) + (bit of qubit j)`, qubit `i` high;
`A ⊗ B` puts `A` on the high bit; a gate list acts head first (`blockMatF`).

## Main definitions

* `C`, `M2`, `M4` — complex `Float` numbers and `2 × 2`, `4 × 4` complex matrices.
* `blockMatF` — the `4 × 4` matrix of a gate list on a qubit pair (`KAKPass.blockMat`).
* `jacobiEig` — eigenvalues and eigenvectors of a real symmetric `4 × 4` matrix.
* `canonical` — the decomposition `M† U M = c · O₁ · diag f · Pᵀ`.
* `classify` — the smallest template class `k` of a two-qubit unitary.
* `fitK` — the global phase and the angles of `kak{k}` for a unitary of class `k`.
* `templateMatF` — the `Float` matrix of `kak{k} θ`.
* `phaseDist` — `‖U − e^{iφ} V‖_F` at `φ = arg tr(V† U)`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit

namespace CatCrypt.Quantum.Synthesis.KAKFloat

/-- `π` as a `Float`. -/
def piF : Float := 3.141592653589793

/-! ## Complex numbers -/

/-- A complex number with `Float` parts. -/
structure C where
  /-- The real part. -/
  re : Float
  /-- The imaginary part. -/
  im : Float
  deriving Inhabited, Repr

namespace C

/-- The complex number `0`. -/
def zero : C := ⟨0, 0⟩

/-- The complex number `1`. -/
def one : C := ⟨1, 0⟩

/-- The real number `x` as a complex number. -/
def ofReal (x : Float) : C := ⟨x, 0⟩

instance : Add C := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Sub C := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Neg C := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Mul C := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

/-- The complex conjugate. -/
def conj (z : C) : C := ⟨z.re, -z.im⟩

/-- The product of a real number and a complex number. -/
def scale (x : Float) (z : C) : C := ⟨x * z.re, x * z.im⟩

/-- The modulus. -/
def abs (z : C) : Float := Float.sqrt (z.re * z.re + z.im * z.im)

/-- The argument in `[-π, π]`. -/
def arg (z : C) : Float := Float.atan2 z.im z.re

/-- The complex number of modulus `r` and argument `t`. -/
def polar (r t : Float) : C := ⟨r * Float.cos t, r * Float.sin t⟩

/-- `e^{it}`. -/
def expI (t : Float) : C := polar 1 t

/-- The inverse `1 / z`. -/
def inv (z : C) : C :=
  let d := z.re * z.re + z.im * z.im
  ⟨z.re / d, -z.im / d⟩

/-- The principal square root. -/
def sqrt (z : C) : C := polar (Float.sqrt z.abs) (z.arg / 2)

/-- The principal power `z ^ p` for a real exponent `p`. -/
def rpow (z : C) (p : Float) : C := polar (Float.pow z.abs p) (p * z.arg)

end C

/-! ## Matrices -/

/-- A `2 × 2` complex matrix, row major. -/
structure M2 where
  /-- Entry `(0, 0)`. -/
  a00 : C
  /-- Entry `(0, 1)`. -/
  a01 : C
  /-- Entry `(1, 0)`. -/
  a10 : C
  /-- Entry `(1, 1)`. -/
  a11 : C
  deriving Inhabited, Repr

namespace M2

/-- The entry `(r, c)`, for `r, c < 2`. -/
def get (A : M2) (r c : Nat) : C :=
  if r == 0 then (if c == 0 then A.a00 else A.a01) else (if c == 0 then A.a10 else A.a11)

/-- The matrix product. -/
def mul (A B : M2) : M2 :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10, A.a00 * B.a01 + A.a01 * B.a11,
   A.a10 * B.a00 + A.a11 * B.a10, A.a10 * B.a01 + A.a11 * B.a11⟩

instance : Mul M2 := ⟨mul⟩

/-- The determinant. -/
def det (A : M2) : C := A.a00 * A.a11 - A.a01 * A.a10

/-- The product of a complex scalar and a matrix. -/
def smul (z : C) (A : M2) : M2 := ⟨z * A.a00, z * A.a01, z * A.a10, z * A.a11⟩

/-- The identity. -/
def id : M2 := ⟨C.one, C.zero, C.zero, C.one⟩

/-- The diagonal matrix `diag(1, e^{it})` (`rzGate t`). -/
def rz (t : Float) : M2 := ⟨C.one, C.zero, C.zero, C.expI t⟩

/-- `ryMatrix t = [[cos t/2, -sin t/2], [sin t/2, cos t/2]]`. -/
def ry (t : Float) : M2 :=
  let c := Float.cos (t / 2)
  let s := Float.sin (t / 2)
  ⟨C.ofReal c, C.ofReal (-s), C.ofReal s, C.ofReal c⟩

/-- `rxMatrix t = [[cos t/2, -i sin t/2], [-i sin t/2, cos t/2]]`. -/
def rx (t : Float) : M2 :=
  let c := Float.cos (t / 2)
  let s := Float.sin (t / 2)
  ⟨C.ofReal c, ⟨0, -s⟩, ⟨0, -s⟩, C.ofReal c⟩

/-- The Hadamard matrix. -/
def had : M2 :=
  let h := 1 / Float.sqrt 2
  ⟨C.ofReal h, C.ofReal h, C.ofReal h, C.ofReal (-h)⟩

/-- `zyz b g d = rz b · ry g · rz d`. -/
def zyz (b g d : Float) : M2 := rz b * ry g * rz d

end M2

/-- A `4 × 4` complex matrix: 32 floats, entry `(r, c)` at `8r + 2c` (real part) and
`8r + 2c + 1` (imaginary part). -/
structure M4 where
  /-- The interleaved real and imaginary parts, row major. -/
  data : FloatArray

namespace M4

/-- The entry `(r, c)`. -/
def get (A : M4) (r c : Nat) : C := ⟨A.data[8 * r + 2 * c]!, A.data[8 * r + 2 * c + 1]!⟩

/-- The matrix with entries `f r c`. -/
def ofFn (f : Nat → Nat → C) : M4 := Id.run do
  let mut a := FloatArray.emptyWithCapacity 32
  for r in [0:4] do
    for c in [0:4] do
      let z := f r c
      a := (a.push z.re).push z.im
  return ⟨a⟩

/-- The matrix product, accumulated in unboxed float locals (no `C` is allocated). -/
def mul (A B : M4) : M4 := Id.run do
  let a := A.data
  let b := B.data
  let mut out := FloatArray.emptyWithCapacity 32
  for r in [0:4] do
    for c in [0:4] do
      let mut re : Float := 0
      let mut im : Float := 0
      for k in [0:4] do
        let ar := a[8 * r + 2 * k]!
        let ai := a[8 * r + 2 * k + 1]!
        let br := b[8 * k + 2 * c]!
        let bi := b[8 * k + 2 * c + 1]!
        re := re + (ar * br - ai * bi)
        im := im + (ar * bi + ai * br)
      out := (out.push re).push im
  return ⟨out⟩

instance : Mul M4 := ⟨mul⟩

/-- The entrywise difference. -/
def sub (A B : M4) : M4 := ofFn fun r c => A.get r c - B.get r c

/-- The product of a complex scalar and a matrix. -/
def smul (z : C) (A : M4) : M4 := ofFn fun r c => z * A.get r c

/-- The conjugate transpose. -/
def adjoint (A : M4) : M4 := ofFn fun r c => (A.get c r).conj

/-- The transpose. -/
def transpose (A : M4) : M4 := ofFn fun r c => A.get c r

/-- The entrywise real part. -/
def realPart (A : M4) : M4 := ofFn fun r c => C.ofReal (A.get r c).re

/-- The matrix with column `c` negated. -/
def negCol (A : M4) (c : Nat) : M4 := ofFn fun r k => if k == c then -A.get r k else A.get r k

/-- The trace. -/
def trace (A : M4) : C := A.get 0 0 + A.get 1 1 + A.get 2 2 + A.get 3 3

/-- The determinant, by the Laplace expansion along the first two rows. -/
def det (A : M4) : C :=
  let m (i j : Nat) := A.get 0 i * A.get 1 j - A.get 0 j * A.get 1 i
  let w (i j : Nat) := A.get 2 i * A.get 3 j - A.get 2 j * A.get 3 i
  m 0 1 * w 2 3 - m 0 2 * w 1 3 + m 0 3 * w 1 2 + m 1 2 * w 0 3 - m 1 3 * w 0 2 + m 2 3 * w 0 1

/-- The Frobenius norm. -/
def frob (A : M4) : Float := Id.run do
  let mut s := 0
  for x in A.data do
    s := s + x * x
  return Float.sqrt s

/-- The diagonal matrix with diagonal `d`. -/
def diag (d : Array C) : M4 := ofFn fun r c => if r == c then d[r]! else C.zero

/-- The diagonal entries. -/
def diagonal (A : M4) : Array C := #[A.get 0 0, A.get 1 1, A.get 2 2, A.get 3 3]

/-- The identity. -/
def id : M4 := ofFn fun r c => if r == c then C.one else C.zero

/-- The Kronecker product `A ⊗ B`, `A` on the high bit. -/
def kron (A B : M2) : M4 := ofFn fun r c => A.get (r / 2) (c / 2) * B.get (r % 2) (c % 2)

/-- The real `4 × 4` matrix with rows `rows`. -/
def ofReal (rows : Array (Array Float)) : M4 := ofFn fun r c => C.ofReal (rows[r]!)[c]!

/-- `cnot`, control on the high bit. -/
def cnot : M4 := ofReal #[#[1, 0, 0, 0], #[0, 1, 0, 0], #[0, 0, 0, 1], #[0, 0, 1, 0]]

/-- `cnotRev`, control on the low bit. -/
def cnotRev : M4 := ofReal #[#[1, 0, 0, 0], #[0, 0, 0, 1], #[0, 0, 1, 0], #[0, 1, 0, 0]]

/-- `czGate = diag(1, 1, 1, -1)`. -/
def cz : M4 := ofReal #[#[1, 0, 0, 0], #[0, 1, 0, 0], #[0, 0, 1, 0], #[0, 0, 0, -1]]

/-- The magic basis `M = (1/√2)[[1, i, 0, 0], [0, 0, i, 1], [0, 0, i, -1], [1, -i, 0, 0]]`. -/
def magic : M4 :=
  let h := 1 / Float.sqrt 2
  let e : Array (Array C) :=
    #[#[⟨h, 0⟩, ⟨0, h⟩, C.zero, C.zero], #[C.zero, C.zero, ⟨0, h⟩, ⟨h, 0⟩],
      #[C.zero, C.zero, ⟨0, h⟩, ⟨-h, 0⟩], #[⟨h, 0⟩, ⟨0, -h⟩, C.zero, C.zero]]
  ofFn fun r c => (e[r]!)[c]!

end M4

/-! ## Gates on a pair -/

/-- The real angle `a + b·π` of an exact angle, in `Float`. -/
def piLinF (p : CatCrypt.Quantum.PiLin) : Float :=
  Float.ofInt p.a.num / Float.ofNat p.a.den +
    Float.ofInt p.b.num / Float.ofNat p.b.den * piF

/-- A one-qubit matrix on qubit `q ∈ {i, j}` as a `4 × 4` matrix on the pair `(i, j)`
(`KAKPass.side`). -/
def sideF {n : Nat} (i q : Fin n) (A : M2) : M4 :=
  if q = i then M4.kron A M2.id else M4.kron M2.id A

/-- The `Float` matrix of a gate on the pair `(i, j)` (`KAKPass.pairMat`); `none` for
`Gate.Rz`, whose angle is a real number. -/
def pairMatF {n : Nat} (i _j : Fin n) : Gate n → Option M4
  | .H q => some (sideF i q M2.had)
  | .X q => some (sideF i q ⟨C.zero, C.one, C.one, C.zero⟩)
  | .Y q => some (sideF i q ⟨C.zero, ⟨0, -1⟩, ⟨0, 1⟩, C.zero⟩)
  | .Z q => some (sideF i q ⟨C.one, C.zero, C.zero, C.ofReal (-1)⟩)
  | .T q => some (sideF i q (M2.rz (piF / 4)))
  | .Tdg q => some (sideF i q (M2.rz (-(piF / 4))))
  | .S q => some (sideF i q ⟨C.one, C.zero, C.zero, ⟨0, 1⟩⟩)
  | .Rz _ _ => none
  | .RzQ q a => some (sideF i q (M2.rz (piLinF a)))
  | .CNOT a b => some (if a = b then M4.id else if a = i then M4.cnot else M4.cnotRev)
  | .CZ a b => some (if a = b then M4.id else M4.cz)

/-- Rows `r0` and `r1` of `A` replaced by `m · (row r0, row r1)`, in place when `A` is
unshared; the left product of `A` by a one-qubit matrix acting on that pair of rows. -/
def rowMix (A : FloatArray) (r0 r1 : Nat) (m : M2) : FloatArray := Id.run do
  let (ar, ai, br, bi) := (m.a00.re, m.a00.im, m.a01.re, m.a01.im)
  let (cr, ci, dr, di) := (m.a10.re, m.a10.im, m.a11.re, m.a11.im)
  let mut A := A
  for c in [0:4] do
    let p := 8 * r0 + 2 * c
    let q := 8 * r1 + 2 * c
    let (xr, xi, yr, yi) := (A[p]!, A[p + 1]!, A[q]!, A[q + 1]!)
    A := A.set! p (ar * xr - ai * xi + (br * yr - bi * yi))
    A := A.set! (p + 1) (ar * xi + ai * xr + (br * yi + bi * yr))
    A := A.set! q (cr * xr - ci * xi + (dr * yr - di * yi))
    A := A.set! (q + 1) (cr * xi + ci * xr + (dr * yi + di * yr))
  return A

/-- Rows `r0` and `r1` of `A` exchanged. -/
def rowSwap (A : FloatArray) (r0 r1 : Nat) : FloatArray := Id.run do
  let mut A := A
  for k in [0:8] do
    let x := A[8 * r0 + k]!
    A := A.set! (8 * r0 + k) A[8 * r1 + k]!
    A := A.set! (8 * r1 + k) x
  return A

/-- Row `r` of `A` negated. -/
def rowNeg (A : FloatArray) (r : Nat) : FloatArray := Id.run do
  let mut A := A
  for k in [0:8] do
    A := A.set! (8 * r + k) (-A[8 * r + k]!)
  return A

/-- The one-qubit matrix of a one-qubit gate, `none` for the other gates and `Gate.Rz`. -/
def gate1F {n : Nat} : Gate n → Option (Fin n × M2)
  | .H q => some (q, M2.had)
  | .X q => some (q, ⟨C.zero, C.one, C.one, C.zero⟩)
  | .Y q => some (q, ⟨C.zero, ⟨0, -1⟩, ⟨0, 1⟩, C.zero⟩)
  | .Z q => some (q, ⟨C.one, C.zero, C.zero, C.ofReal (-1)⟩)
  | .T q => some (q, M2.rz (piF / 4))
  | .Tdg q => some (q, M2.rz (-(piF / 4)))
  | .S q => some (q, ⟨C.one, C.zero, C.zero, ⟨0, 1⟩⟩)
  | .RzQ q a => some (q, M2.rz (piLinF a))
  | _ => none

/-- `pairMatF i j g * A`, computed by row operations on `A` (`rowMix`, `rowSwap`, `rowNeg`)
instead of a matrix product; `none` for `Gate.Rz`. Row `2h + l` carries the bit `h` of `i`
and the bit `l` of the other qubit. -/
def applyGateF {n : Nat} (i : Fin n) (A : FloatArray) : Gate n → Option FloatArray
  | .Rz _ _ => none
  | .CNOT a b => some (if a = b then A else if a = i then rowSwap A 2 3 else rowSwap A 1 3)
  | .CZ a b => some (if a = b then A else rowNeg A 3)
  | g => (gate1F g).map fun (q, m) =>
      if q = i then rowMix (rowMix A 0 2 m) 1 3 m else rowMix (rowMix A 0 1 m) 2 3 m

/-- The `Float` matrix of a gate list on the pair `(i, j)`, head gate first
(`KAKPass.blockMat`, the product of the `pairMatF` of its gates); `none` when the list holds a
`Gate.Rz`. Each gate is applied to the accumulated matrix by row operations. -/
def blockMatF {n : Nat} (i _j : Fin n) (gs : List (Gate n)) : Option M4 :=
  (gs.foldlM (applyGateF i) M4.id.data).map M4.mk

/-! ## Real symmetric eigenproblem -/

/-- Entry `(r, c)` of a real `4 × 4` matrix stored row major in 16 floats. -/
def rget (A : FloatArray) (r c : Nat) : Float := A[4 * r + c]!

/-- The real `4 × 4` matrix with entries `f r c`. -/
def rofFn (f : Nat → Nat → Float) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity 16
  for r in [0:4] do
    for c in [0:4] do
      a := a.push (f r c)
  return a

/-- The product of real `4 × 4` matrices. -/
def rmul (A B : FloatArray) : FloatArray := rofFn fun r c =>
  rget A r 0 * rget B 0 c + rget A r 1 * rget B 1 c + rget A r 2 * rget B 2 c +
    rget A r 3 * rget B 3 c

/-- The Frobenius norm of the off-diagonal part of a real `4 × 4` matrix. -/
def offNorm (A : FloatArray) : Float := Id.run do
  let mut s := 0
  for r in [0:4] do
    for c in [0:4] do
      if r != c then s := s + rget A r c * rget A r c
  return Float.sqrt s

/-- `A · J` for the rotation `J` with `J p p = J q q = c`, `J p q = s`, `J q p = -s`: columns
`p, q` become `c · A_p - s · A_q` and `s · A_p + c · A_q`. -/
def rotCols (A : FloatArray) (p q : Nat) (c s : Float) : FloatArray := Id.run do
  let mut B := A
  for r in [0:4] do
    let x := rget A r p
    let y := rget A r q
    B := (B.set! (4 * r + p) (c * x - s * y)).set! (4 * r + q) (s * x + c * y)
  return B

/-- `Jᵀ · A` for the rotation `J` of `rotCols`: rows `p, q` become `c · A_p - s · A_q` and
`s · A_p + c · A_q`. -/
def rotRows (A : FloatArray) (p q : Nat) (c s : Float) : FloatArray := Id.run do
  let mut B := A
  for k in [0:4] do
    let x := rget A p k
    let y := rget A q k
    B := (B.set! (4 * p + k) (c * x - s * y)).set! (4 * q + k) (s * x + c * y)
  return B

/-- The index pairs `p < q` of a cyclic Jacobi sweep. -/
def jacobiPairs : Array (Nat × Nat) := #[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Eigenvalues (ascending) and orthogonal eigenvector matrix (eigenvectors as columns) of a
real symmetric `4 × 4` matrix, by cyclic Jacobi rotations until the off-diagonal norm is
below `1e-15` or after 60 sweeps. -/
def jacobiEig (A0 : FloatArray) : Array Float × FloatArray := Id.run do
  let mut A := A0
  let mut V := rofFn fun r c => if r == c then 1 else 0
  for _ in [0:60] do
    if offNorm A < 1e-15 then break
    for (p, q) in jacobiPairs do
      let apq := rget A p q
      if apq.abs > 1e-300 then
        let th := (rget A q q - rget A p p) / (2 * apq)
        let t := (if th >= 0 then 1 else -1) / (th.abs + Float.sqrt (th * th + 1))
        let c := 1 / Float.sqrt (t * t + 1)
        let s := t * c
        A := rotRows (rotCols A p q c s) p q c s
        V := rotCols V p q c s
  let ev := #[rget A 0 0, rget A 1 1, rget A 2 2, rget A 3 3]
  let ord := (#[0, 1, 2, 3] : Array Nat).qsort fun x y => ev[x]! < ev[y]!
  return (ord.map fun x => ev[x]!, rofFn fun r c => rget V r ord[c]!)

/-- The fixed sequence of mixing coefficients `r` tried by `symmetricUnitaryDiag`. -/
def mixCoeffs : Array Float :=
  #[0.5772156649, -0.3183098862, 0.7071067812, -0.6180339887, 0.2718281828, -0.8862269255,
    0.1414213562, -0.4342944819, 0.9189385332, -0.2236067977, 0.3678794412, -0.7853981634,
    0.6931471806, -0.1732050808, 0.8414709848, -0.5403023059, 0.4142135624, -0.9659258263,
    0.0523359562, -0.3090169944]

/-- A real orthogonal `P` and the diagonal `d` of `Pᵀ S P`, for `S` symmetric unitary, when
`Pᵀ S P` is diagonal within `1e-13`: `P` diagonalises `Re S + r · Im S` for the first `r` of
`mixCoeffs` that succeeds. -/
def symmetricUnitaryDiag (S : M4) : Option (M4 × Array C) := Id.run do
  for r in mixCoeffs do
    let (_, Pr) := jacobiEig (rofFn fun a b => (S.get a b).re + r * (S.get a b).im)
    let P := M4.ofFn fun a b => C.ofReal (rget Pr a b)
    let D := P.transpose * S * P
    let mut off : Float := 0
    for a in [0:4] do
      for b in [0:4] do
        if a != b then off := max off (D.get a b).abs
    if off < 1e-13 then return some (P, D.diagonal)
  return none

/-! ## Canonical decomposition and classes -/

/-- `(O₁, f, P)` with `O₁, P ∈ SO(4)` and `M† U M = c · O₁ · diag f · Pᵀ` for a unit scalar `c`
(`exists_local_diagonal_local`); `none` when the simultaneous diagonalisation fails. -/
def canonical (U : M4) : Option (M4 × Array C × M4) := do
  let Ub0 := M4.magic.adjoint * U * M4.magic
  let Ub := M4.smul (Ub0.det.rpow 0.25).inv Ub0
  let (P0, d) ← symmetricUnitaryDiag (Ub.transpose * Ub)
  let P := if P0.det.re < 0 then P0.negCol 0 else P0
  let f0 := d.map C.sqrt
  let O0 := (Ub * P * M4.diag (f0.map C.inv)).realPart
  if O0.det.re < 0 then
    return (O0.negCol 0, f0.set! 0 (-f0[0]!), P)
  else
    return (O0, f0, P)

/-- The 24 permutations of `{0, 1, 2, 3}` in lexicographic order. -/
def perms4 : Array (Array Nat) :=
  #[#[0, 1, 2, 3], #[0, 1, 3, 2], #[0, 2, 1, 3], #[0, 2, 3, 1], #[0, 3, 1, 2], #[0, 3, 2, 1],
    #[1, 0, 2, 3], #[1, 0, 3, 2], #[1, 2, 0, 3], #[1, 2, 3, 0], #[1, 3, 0, 2], #[1, 3, 2, 0],
    #[2, 0, 1, 3], #[2, 0, 3, 1], #[2, 1, 0, 3], #[2, 1, 3, 0], #[2, 3, 0, 1], #[2, 3, 1, 0],
    #[3, 0, 1, 2], #[3, 0, 2, 1], #[3, 1, 0, 2], #[3, 1, 2, 0], #[3, 2, 0, 1], #[3, 2, 1, 0]]

/-- The 8 sign vectors in `{1, -1}⁴` with an even number of `-1`, in lexicographic order
with `1` before `-1`. -/
def signs4 : Array (Array Float) :=
  #[#[1, 1, 1, 1], #[1, 1, -1, -1], #[1, -1, 1, -1], #[1, -1, -1, 1], #[-1, 1, 1, -1],
    #[-1, 1, -1, 1], #[-1, -1, 1, 1], #[-1, -1, -1, -1]]

/-- Deviation of the vector `g` from `KAKSmall.classPhase k` (`0` when it holds). -/
def classDev (k : Nat) (g : Array C) : Float :=
  let iC : C := ⟨0, 1⟩
  match k with
  | 0 => max (g[1]! - g[0]!).abs (max (g[2]! - g[0]!).abs (g[3]! - g[0]!).abs)
  | 1 => max (g[1]! - g[0]!).abs (max (g[2]! - iC * g[0]!).abs (g[3]! - iC * g[0]!).abs)
  | 2 => (g[0]! * g[3]! - g[1]! * g[2]!).abs
  | _ => 0

/-- The vector `ε · (f ∘ σ)` for a permutation `σ` and a sign vector `ε`. -/
def frameVec (f : Array C) (sg : Array Nat) (e : Array Float) : Array C :=
  #[C.scale e[0]! f[sg[0]!]!, C.scale e[1]! f[sg[1]!]!, C.scale e[2]! f[sg[2]!]!,
    C.scale e[3]! f[sg[3]!]!]

/-- `(deviation, σ, ε)` minimising the deviation of `ε · (f ∘ σ)` from class `k`, the first
minimiser in the order of `perms4` and `signs4`. -/
def bestFrame (k : Nat) (f : Array C) : Float × Array Nat × Array Float := Id.run do
  let mut best : Float × Array Nat × Array Float := (classDev k f, perms4[0]!, signs4[0]!)
  for sg in perms4 do
    for e in signs4 do
      let dev := classDev k (frameVec f sg e)
      if dev < best.1 then best := (dev, sg, e)
  return best

/-- The class of `f`: the smallest `k ∈ {0, 1, 2}` whose best frame deviates by less than
`tol`, else `3`. -/
def classOf (f : Array C) (tol : Float) : Fin 4 :=
  if (bestFrame 0 f).1 < tol then 0
  else if (bestFrame 1 f).1 < tol then 1
  else if (bestFrame 2 f).1 < tol then 2 else 3

/-- The smallest `k` such that a phase vector of `U` in the Weyl orbit of `canonical`
satisfies `classPhase k` within `tol` (default `1e-7`): the numeric test for `InClass k U`. -/
def classify (U : M4) (tol : Float := 1e-7) : Option (Fin 4) :=
  (fun (_, f, _) => classOf f tol) <$> canonical U

/-- The number of inversions of a permutation is odd. -/
def oddPerm (sg : Array Nat) : Bool := Id.run do
  let mut odd := false
  for a in [0:4] do
    for b in [a + 1:4] do
      if sg[a]! > sg[b]! then odd := !odd
  return odd

/-- `(W₁, g, W₂)` with `U = c · W₁ · (M diag g M†) · W₂`, `W₁, W₂` local and `g` the vector
of the Weyl orbit closest to class `k`, from the canonical form `(O₁, f, P)` of `U`. -/
def locals (can : M4 × Array C × M4) (k : Nat) : M4 × Array C × M4 :=
  let (O1, f, P) := can
  let (_, sg, e) := bestFrame k f
  let Pi := M4.ofFn fun r c => if c == sg[r]! then C.one else C.zero
  let R1a := Pi.transpose * M4.diag (e.map C.ofReal)
  let D := M4.diag #[C.ofReal (-1), C.one, C.one, C.one]
  let (R1, R2) := if oddPerm sg then (R1a * D, D * Pi) else (R1a, Pi)
  let M := M4.magic
  (M * O1 * R1 * M.adjoint, frameVec f sg e, M * R2 * P.transpose * M.adjoint)

/-! ## Local factors -/

/-- `(A, B)` in `SU(2)` up to sign with `K = A ⊗ B` up to a scalar: the rank-one extraction
of the rearranged matrix `R[2a+c, 2b+d] = K[2a+b, 2c+d]` at its entry of largest modulus. -/
def kronFactor (K : M4) : M2 × M2 := Id.run do
  let R (x y : Nat) : C := K.get (2 * (x / 2) + y / 2) (2 * (x % 2) + y % 2)
  let mut p := 0
  let mut q := 0
  let mut m : Float := -1
  for x in [0:4] do
    for y in [0:4] do
      if (R x y).abs > m then
        m := (R x y).abs
        p := x
        q := y
  let A : M2 := ⟨R 0 q, R 1 q, R 2 q, R 3 q⟩
  let s := (R p q).inv
  let B : M2 := ⟨s * R p 0, s * R p 1, s * R p 2, s * R p 3⟩
  return (M2.smul (A.det.sqrt).inv A, M2.smul (B.det.sqrt).inv B)

/-- `(β, γ, δ)` with `A = e^{iα} · rz β · ry γ · rz δ` for some `α`; each angle is read from
the entries of the larger modulus. -/
def zyz (A : M2) : Array Float :=
  let c := A.a00.abs
  let s := A.a10.abs
  let alpha := if c > 1e-15 then A.a00.arg else 0
  let beta := if s > 1e-15 then A.a10.arg - alpha else 0
  let delta := if c >= s then A.a11.arg - alpha - beta else (-A.a01).arg - alpha
  #[beta, 2 * Float.atan2 s c, delta]

/-- The ZYZ angles of the high and the low factor of a local `4 × 4` matrix. -/
def zyzPair (W : M4) : Array Float :=
  let (A, B) := kronFactor W
  zyz A ++ zyz B

/-! ## Templates and the fit -/

/-- The layer `zyz θ[k..k+2] ⊗ zyz θ[k+3..k+5]`. -/
def layerF (θ : Array Float) (k : Nat) : M4 :=
  M4.kron (M2.zyz θ[k]! θ[k + 1]! θ[k + 2]!) (M2.zyz θ[k + 3]! θ[k + 4]! θ[k + 5]!)

/-- `vwCore a b c` of `KAK.lean`. -/
def vwCoreF (a b c : Float) : M4 :=
  M4.kron (M2.rz (-(piF / 2))) M2.id * M4.cnotRev * M4.kron M2.id (M2.ry c) * M4.cnot *
    M4.kron (M2.rz a) (M2.ry b) * M4.cnotRev * M4.kron M2.id (M2.rz (piF / 2))

/-- `core2 s t = cnot · (rx s ⊗ rz t) · cnot` of `KAKSmall.lean`. -/
def core2F (s t : Float) : M4 := M4.cnot * M4.kron (M2.rx s) (M2.rz t) * M4.cnot

/-- The `Float` matrix of `kak{k} θ` (`KAKSmall.kak0`, `kak1`, `kak2`, `KAK.kak3`). -/
def templateMatF (k : Fin 4) (θ : Array Float) : M4 :=
  match k with
  | 0 => layerF θ 0
  | 1 => layerF θ 0 * M4.cnot * layerF θ 6
  | 2 => layerF θ 0 * core2F θ[12]! θ[13]! * layerF θ 6
  | 3 => layerF θ 0 * vwCoreF θ[12]! θ[13]! θ[14]! * layerF θ 6

/-- The global phase `arg tr(V† U)` that brings `V` closest to `U`. -/
def bestPhase (U V : M4) : Float := (V.adjoint * U).trace.arg

/-- `‖U − e^{iφ} V‖_F` at `φ = arg tr(V† U)`. -/
def phaseDist (U V : M4) : Float := (M4.sub U (M4.smul (C.expI (bestPhase U V)) V)).frob

/-- The result of a fit: `U ≈ e^{i phase} · kak{k} angles`. -/
structure KFit where
  /-- The global phase `φ`. -/
  phase : Float
  /-- The template angles, in the index order of `kak{k}Gates`. -/
  angles : Array Float
  /-- `‖U − e^{iφ} kak{k} θ‖_F`. -/
  phaseDist : Float
  deriving Inhabited, Repr

/-- The angles of `kak3` (`exists_vwCore` on the canonical phases), from the canonical form
`(O₁, f, P)`. -/
def angles3 (can : M4 × Array C × M4) : Array Float :=
  let (O1, f, P) := can
  let t := f.map C.arg
  let phi0 := (t[0]! + t[1]!) / 2
  let a := (t[2]! + (t[3]! - piF)) / 2 - phi0
  let b := ((t[1]! - t[0]!) + (t[3]! - piF - t[2]!)) / 2
  let c := ((t[1]! - t[0]!) - (t[3]! - piF - t[2]!)) / 2
  let M := M4.magic
  zyzPair (M * O1 * M.adjoint) ++ zyzPair (M * P.transpose * M.adjoint) ++ #[a, b, c]

/-- The angles of `kak{k}` for `k ≤ 2`, by the proof of `kak{k}_exists`, from the canonical
form. -/
def anglesSmall (can : M4 × Array C × M4) (k : Nat) : Array Float :=
  let (W1, g, W2) := locals can k
  match k with
  | 0 => zyzPair (W1 * W2)
  | 1 =>
    let IH := M4.kron M2.id M2.had
    let S2 : M2 := ⟨C.one, C.zero, C.zero, ⟨0, 1⟩⟩
    zyzPair (W1 * IH) ++ zyzPair (IH * M4.kron S2 S2 * W2)
  | _ =>
    let a := g.map C.arg
    zyzPair W1 ++ zyzPair W2 ++ #[a[1]! - a[0]!, a[2]! - a[0]!]

/-- The angles of `kak{k}` from the canonical form of the unitary: `θ` of length 6, 12, 14,
15 for `k = 0, 1, 2, 3`. -/
def anglesK (can : M4 × Array C × M4) (k : Fin 4) : Array Float :=
  if k = 3 then angles3 can else anglesSmall can k.val

/-- `(φ, θ, d)` with `U ≈ e^{iφ} · kak{k} θ` and `d` the Frobenius distance `phaseDist`. For
`U` outside class `k`, `d` is the distance reached. -/
def fitK (U : M4) (k : Fin 4) : Option KFit := do
  let θ := anglesK (← canonical U) k
  let V := templateMatF k θ
  return ⟨bestPhase U V, θ, phaseDist U V⟩

end CatCrypt.Quantum.Synthesis.KAKFloat
