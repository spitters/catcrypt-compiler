/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.KAKFloat
public import CatCrypt.Quantum.Synthesis.ApproxEmit
public import CatCrypt.Quantum.QrunchFuse

/-!
# The fits of the Qrunch resynthesis

The resynthesis level (`Optimization.ResynthLevel`) replaces two-qubit blocks by KAK
templates (`KAKPassSmall.kakEmit`) and one-qubit runs by ZYZ or XYX templates
(`ZYZPass.zyzEmit`) at fitted angles. This module holds the computable fits it runs.

The block fit `qrunchFit` is floating point (`KAKFloat`): the class of the block's matrix, the
template angles of `fitK`, as exact multiples of `π/4` when they are within `10⁻¹²` of one and
else rounded to decimals with 15 fractional digits (`snapQ`, `roundQ`), and the
Frobenius distance `phaseDist` of the matrix of the emitted gates (`blockMatF` of
`tmplGatesQ`) from the block, below `1e-9`. It tries the classes from `classify` up to one below the block's CNOT count and
returns the first that passes. The run fit `qrunchZFitAt` fits a one-qubit run that prints as
more than three statements in the Qrunch basis (`qrunchCost`) in the form `runAxes` chooses
from the two-qubit gates around it. Both fits are unverified proposals; the level runs them
behind the verified checker of `ApproxEmit` (`qrunchFitChecked`, `qrunchZFitChecked`), which
keeps a proposal only when it bounds the distance of the block or run from its template,
at the phase `phaseQ`, by at most `checkBound` in the `ℓ²` operator norm.

## Main definitions

* `roundQ` — a float as the rational with 15 fractional digits nearest to it.
* `snapQ` — a fitted angle as an exact multiple of `π/4` when it is one to `10⁻¹²`, else `roundQ`.
* `qrunchFit` — the floating-point block fit, a `KAKPassSmall.BlockFit`.
* `qrunchZFitAt`, `runAxes`, `qrunchZFit` — the floating-point fit of a one-qubit run in the
  ZYZ or XYX form, chosen from the two-qubit gates around the run.
* `qrunchCost` — the number of statements a gate list prints as in the Qrunch basis.
* `qrunchFitChecked`, `qrunchZFitChecked` — the fits behind the verified checker.

## Main results

* `listMatrix_kakEmit_qrunchFitChecked`, `listMatrix_zyzEmit_qrunchZFitChecked` — the
  checked passes at these fits, from `listMatrix_kakEmit_checkedFit` and
  `listMatrix_zyzEmit_checkedZFit`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.Synthesis.QrunchFit

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.Synthesis.KAKPass (cnotCount collectBlocks)
open CatCrypt.Quantum.Synthesis.KAKPassSmall (BlockFit kakEmit tmplGatesQ)
open CatCrypt.Quantum.Synthesis.KAKFloat

/-- The scale of the decimal rounding of fitted angles: 15 fractional digits. -/
def angleScale : ℕ := 10 ^ 15

/-- A float as the rational with 15 fractional digits nearest to it. -/
def roundQ (x : Float) : ℚ :=
  mkRat (Float.round (x * angleScale.toFloat)).toInt64.toInt angleScale

/-- A fitted angle as an exact angle: the multiple `kπ/4` when the float is within `10⁻¹²` of
it (so that the exact passes after the fit, `QrunchFuse.fuseQ` and `QrunchFuse.pauliQ`, see the
rotations by multiples of `π` and `π/2`), else `roundQ` of it, in radians. -/
def snapQ (x : Float) : PiLin :=
  let k := Float.round (x / (piF / 4))
  if Float.abs (x - k * (piF / 4)) < 1e-12 then PiLin.ofPi (mkRat k.toInt64.toInt 4)
  else ⟨roundQ x, 0⟩

/-- The fitted angles as exact angles (`snapQ`), padded with zeros to 15. -/
def anglesQ (θ : Array Float) : Fin 15 → PiLin :=
  fun x => if h : x.val < θ.size then snapQ θ[x.val] else 0

/-- The distance bound of a replaced block: the matrix of the emitted gates against the
    block's matrix, up to global phase, in the Frobenius norm. -/
def phaseDistBound : Float := 1e-9

/-- The fit of one class `k` to a block on `(i, j)` with matrix `U` and canonical form `can`:
    the rounded angles of `anglesK` and the phase `ψ` with `U ≈ e^{iψ} V` for the matrix `V`
    of the emitted gates, when they pass the distance bound. -/
def fitClass {n : ℕ} (i j : Fin n) (U : M4) (can : M4 × Array C × M4) (k : Fin 4) :
    Option ((Fin 15 → PiLin) × Float) := do
  let θ := anglesQ (anglesK can k)
  let V ← blockMatF i j (tmplGatesQ k i j θ)
  if phaseDist U V < phaseDistBound then some (θ, bestPhase U V) else none

/-- **The floating-point block fit.** A block with at least two CNOTs and a matrix
    (`blockMatF`) gets the first class `k`, from its class (`classOf` of the canonical form,
    as `classify`) up to one below its CNOT count, whose rounded angles pass the distance
    bound; the payload is the phase `ψ` of the block against its template. The canonical
    form is computed once per block. -/
def qrunchFit {n : ℕ} : BlockFit n Float := fun i j gs =>
  let c := cnotCount gs
  if c < 2 then none else do
    let U ← blockMatF i j gs
    let can ← canonical U
    let k0 := classOf can.2.1 1e-7
    let ks := (List.range (min c 4)).filter (k0.val ≤ ·)
    ks.firstM fun k =>
      if hk : k < 4 then (fitClass i j U can ⟨k, hk⟩).map fun (θ, ψ) => (⟨k, hk⟩, θ, ψ)
      else none

/-- The `Float` matrix of a list of one-qubit gates, head gate first; `none` when a gate is
    not a one-qubit gate with a `Float` matrix (`gate1F`). -/
def runMatF {n : ℕ} (gs : List (Gate n)) : Option M2 :=
  gs.foldlM (fun acc g => (gate1F g).map fun (_, m) => m * acc) M2.id

/-- The number of statements a gate list prints as in the Qrunch basis, after fusion. -/
def qrunchCost {n : ℕ} (gs : List (Gate n)) : ℕ :=
  (QrunchFuse.fuseQ (QrunchBasis.toQelib gs).1).length

/-- **The floating-point fit of a one-qubit run** on `q` in the form `ax`, for a run that prints
    as more than three statements in the Qrunch basis (`qrunchCost`; its ZYZ form prints as
    `p ry p`, its XYX form as `rx ry rx`): the Euler angles of its matrix (`KAKFloat.zyz`, of the
    matrix conjugated by `H` for XYX), made exact as `snapQ`, when the emitted
    `ZYZPass.runTemplate` gates pass the distance bound against the run (both as matrices on the
    pair `(q, q)`, `blockMatF`); the payload is the phase of the run against the emitted gates. -/
def qrunchZFitAt {n : ℕ} (ax : ZYZPass.Axis) (q : Fin n) (gs : List (Gate n)) :
    Option (ZYZPass.Axis × (Fin 3 → PiLin) × Float) := do
  guard (3 < qrunchCost gs)
  let A ← runMatF gs
  -- XYX: H·A·H = e^{iα} rz β · ry γ · rz δ gives A = e^{iα} rx β · ry (-γ) · rx δ.
  let a := match ax with
    | .zyz => zyz A
    | .xyx => let b := zyz (M2.had * A * M2.had); #[b[0]!, -b[1]!, b[2]!]
  let θ : Fin 3 → PiLin := fun x => snapQ a[x.val]!
  let U ← blockMatF q q gs
  let V ← blockMatF q q (ZYZPass.runTemplate ax q θ)
  if phaseDist U V < phaseDistBound then some (ax, θ, bestPhase U V) else none

/-- The role of qubit `q` in a segment: `some true` for the target of a CNOT, `some false`
    for its control or either qubit of a CZ, `none` when the segment does not touch `q` as a
    two-qubit gate. -/
def roleOf {n : ℕ} (q : ℕ) : ZYZPass.Seg n → Option Bool
  | .gate (.CNOT c t) => if t.val = q then some true else if c.val = q then some false else none
  | .gate (.CZ c t) => if t.val = q ∨ c.val = q then some false else none
  | _ => none

/-- The qubits a two-qubit segment touches. -/
def segQubits {n : ℕ} : ZYZPass.Seg n → List ℕ
  | .gate (.CNOT c t) => [c.val, t.val]
  | .gate (.CZ c t) => [c.val, t.val]
  | _ => []

/-- The axis of the template for each segment of `segs`: `xyx` for a run when the
    two-qubit gates before and after it that touch its qubit are CNOTs with that qubit as
    target (rx statements then pass them in `fuseQ`; a missing side counts as a target, both
    missing as `zyz`), `zyz` otherwise. One forward and one backward scan with the last role
    per qubit. -/
def runAxes {n : ℕ} (segs : Array (ZYZPass.Seg n)) :
    Array ZYZPass.Axis := Id.run do
  let mut last : Array (Option Bool) := Array.replicate n none
  let mut before : Array (Option Bool) := Array.replicate segs.size none
  let indexed := segs.toList.zipIdx
  for (s, i) in indexed do
    match s with
    | .run q _ => before := before.set! i last[q.val]!
    | s => for q in segQubits s do last := last.set! q (roleOf q s)
  last := Array.replicate n none
  let mut out : Array ZYZPass.Axis := Array.replicate segs.size .zyz
  for (s, i) in indexed.reverse do
    match s with
    | .run q _ =>
      let b := before[i]!
      let a := last[q.val]!
      if b.getD true && a.getD true && (b.isSome || a.isSome) then out := out.set! i .xyx
    | s => for q in segQubits s do last := last.set! q (roleOf q s)
  return out

/-- The run fit of the segments of `collectRuns l` with the axes `axes` of `runAxes`: the
    segment at position `i` is fitted in the form `axes[i]`, `zyz` past the end. -/
def qrunchZFit {n : ℕ} (axes : Array ZYZPass.Axis) :
    ZYZPass.ZFit n Float :=
  fun i q gs => qrunchZFitAt (axes[i]?.getD .zyz) q gs

/-- The bound of the verified checker on a replaced block or run: `10⁻⁹` in the `ℓ²`
    operator norm. -/
def checkBound : ℚ := 1 / 10 ^ 9

/-- The exact phase `φ = -ψ` of a payload `ψ`, rounded as `roundQ`: the template is
    `e^{iφ}` times the block. -/
def phaseQ (ψ : Float) : PiLin := ⟨-roundQ ψ, 0⟩

/-- `qrunchFit` behind the verified block checker. -/
def qrunchFitChecked {n : ℕ} : BlockFit n (Float × PiLin × ℚ) :=
  IntervalArith.checkedFit qrunchFit phaseQ checkBound

/-- `qrunchZFit axes` behind the verified run checker. -/
def qrunchZFitChecked {n : ℕ} (axes : Array ZYZPass.Axis) :
    ZYZPass.ZFit n (Float × PiLin × ℚ) :=
  IntervalArith.checkedZFit (qrunchZFit axes) phaseQ checkBound

/-- `qrunchFit` without the checker, with the payload of `qrunchFitChecked` at bound `0`: it
replaces the blocks `qrunchFitChecked` replaces and also those whose fit the checker refuses.
The level run at it carries no error bound. -/
def qrunchFitUnchecked {n : ℕ} : BlockFit n (Float × PiLin × ℚ) := fun i j gs =>
  (qrunchFit i j gs).map fun (k, θ, b) => (k, θ, (b, phaseQ b, 0))

/-- `qrunchZFit axes` without the checker, with the payload of `qrunchZFitChecked` at bound
`0`. -/
def qrunchZFitUnchecked {n : ℕ} (axes : Array ZYZPass.Axis) :
    ZYZPass.ZFit n (Float × PiLin × ℚ) := fun i q gs =>
  (qrunchZFit axes i q gs).map fun (a, θ, b) => (a, θ, (b, phaseQ b, 0))


open _root_.Complex
open CatCrypt.Quantum.QFT (listMatrix)
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

/-- **The checked KAK pass at `qrunchFit`.** The gates of `kakEmit qrunchFitChecked l` are
within the sum of the recorded bounds of `l`, up to the sum of the recorded phases. -/
theorem listMatrix_kakEmit_qrunchFitChecked (l : List (Gate n)) :
    ‖listMatrix (kakEmit qrunchFitChecked l).1 -
        exp (I * ((((kakEmit qrunchFitChecked l).2.map
          fun b => PiLin.toReal b.2.1).sum : ℝ) : ℂ)) • listMatrix l‖ ≤
      ((kakEmit qrunchFitChecked l).2.map fun b => (b.2.2 : ℝ)).sum :=
  IntervalArith.listMatrix_kakEmit_checkedFit qrunchFit phaseQ checkBound l

/-- **The checked ZYZ pass at `qrunchZFit axes`.** The gates of
`zyzEmit (qrunchZFitChecked axes) l` are within the sum of the recorded bounds of `l`, up to
the sum of the recorded phases. -/
theorem listMatrix_zyzEmit_qrunchZFitChecked (axes : Array ZYZPass.Axis)
    (l : List (Gate n)) :
    ‖listMatrix (ZYZPass.zyzEmit (qrunchZFitChecked axes) l).1 -
        exp (I * ((((ZYZPass.zyzEmit (qrunchZFitChecked axes) l).2.map
          fun b => PiLin.toReal b.2.1).sum : ℝ) : ℂ)) • listMatrix l‖ ≤
      ((ZYZPass.zyzEmit (qrunchZFitChecked axes) l).2.map fun b => (b.2.2 : ℝ)).sum :=
  IntervalArith.listMatrix_zyzEmit_checkedZFit (qrunchZFit axes) phaseQ checkBound l

end CatCrypt.Quantum.Synthesis.QrunchFit
