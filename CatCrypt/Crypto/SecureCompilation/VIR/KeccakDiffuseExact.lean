/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakBitexact
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakBitexact

/-!
# The Keccak θ∘ρ∘π∘χ diffusion layer is bit-exactly the FIPS 202 spec

`KeccakBitexact.keccak_round_loop_bitexact` proves the
24-round Keccak loop bit-exact in its per-round constant stream `RC[i]`, but
MODELS the round-constant-independent mixing (`θ∘ρ∘π∘χ`) as a fixed model map
`keccakDiffuse`; that module relates the model map to the FIPS 202 mixing only
through the fully-unrolled KAT emission in `bench/keccak_compare/`.

This module proves the bit-level identity at the level of the
**Keccak diffusion as a BitVec function**, independent of the emitter machinery.
Concretely, we:

* decompose the 1600-bit state as 25 u64 lanes `Lanes = Fin 25 → BitVec 64`
  (FIPS 202 §3.1.2: lane index `i = x + 5y`, `x, y ∈ {0..4}`);
* define `keccakClosedForm` — the four diffusion steps (`θ`, `ρ`, `π`, `χ`)
  applied per-lane on `Lanes`, with `crotl` (left rotation as `<<< ||| >>>`)
  for `ρ`, and the algebraic `cchi y0 y1 y2 = y0 ⊕ ((y1 ^^^ allOnes) &&& y2)`
  for `χ` (mirroring the emitter's `e ^ allOnes` form of `¬`);
* define `keccakFipsRound` — the FIPS 202 spec round on the same `Lanes`
  representation, using `BitVec.rotateLeft` and `~~~` directly;
* prove `keccakClosedForm = keccakFipsRound` per-lane — `rfl` for `π`
  (it's a fixed lane permutation), and `bv_decide` per-lane for `ρ` (25 lemmas,
  one per `rhoOffset`) and `χ` (one `bv_decide` schema per width, 25 invocations);
* prove the full-state identity by `funext` over the 25 lanes.

This is the **structural FIPS 202 diffusion identity**, closed by `bv_decide`
per-lane (LRAT axiom) plus `rfl` for the index-only steps. No
`native_decide`, no KAT, no open goals.

## What ι contributes

The `ι` step is `A[0,0] ⊕= RC[round]` — a single per-round XOR into lane 0.
`KeccakIotaIndexed.keccak_iota_loop_bitexact` proves the
indexed bit-exact identity for the RC stream. We include `keccakIotaApply` on
`Lanes` (lane 0 XOR RC, all others unchanged) and the headline `keccakFullRound`
that composes the diffusion with `ι` — the FIPS 202 round transformation.

## Composition with `KeccakBitexact`

The emitter's `keccakRoundLoop` (the per-round loop denoted in
`KeccakBitexact.keccak_round_loop_bitexact`) folds `keccakDiffuse acc ⊕ rcWide i`
over `i ∈ [0, 24)`. Replacing the model map `keccakDiffuse` by the closed-form
`keccakClosedForm` is an emitter-side `Com.denote` reduction, of the same kind
as the SHA-2 emitter-side step, which is outside this module's scope. The
bit-level identity *between the closed-form diffusion and the FIPS spec* is the
content of this module.

## Axiom budget

`keccak_round_bitexact` and the per-step identities use `bv_decide` per-lane.
The carried axiom is the standard `Lean.ofReduceBool` (LRAT) edge. No open goals,
no `native_decide`, no new custom axioms.

## Canonical entry point

See `KeccakEmit.lean` for the full 12-file Keccak VIR canonical map. This
module is the step of that chain that proves the BitVec-level diffusion
identity.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit (roundConst rhoOffset)

/-! ## 1. The lane representation

A Keccak state is `Fin 25 → BitVec 64`: 25 lanes, each a 64-bit word. The
lane index is `i = x + 5y` for `x, y ∈ {0..4}` (FIPS 202 §3.1.2). The 1600-bit
state is the natural concatenation; per-lane reasoning factors `bv_decide` into
25 independent 64-bit identities, none of which exceed the SAT solver's budget. -/

/-- Keccak's per-lane state representation: 25 lanes of 64 bits each. -/
abbrev Lanes : Type := Fin 25 → BitVec 64

/-- Lane index `(x, y) ↦ x + 5 y`. Defined for `x, y < 5`; out-of-range arguments
    collapse to index `0` (never used by the FIPS round). -/
def laneIdx (x y : Nat) : Fin 25 :=
  if h : x + 5 * y < 25 then ⟨x + 5 * y, h⟩ else ⟨0, by decide⟩

/-! ## 2. The four diffusion steps in closed form (the emitter's algebra)

The closed-form definitions mirror the emitter's `Com` chain: `crotl` realizes
`ρ`'s rotation as `(x <<< n) ||| (x >>> (64 - n))`, and `cchi`'s `¬e` is
`e ^^^ allOnes 64`. Everything else (`θ`'s column parity, `χ`'s AND/XOR, and
`π`'s index permutation) matches the emitter byte-identically. -/

/-- Closed-form left rotation: `(x <<< n) ||| (x >>> (64 - n))`. The shift form
    the emitter materializes via two `regArith` lines + an `or`. -/
def crotl (x : BitVec 64) (n : Nat) : BitVec 64 :=
  (x <<< n) ||| (x >>> (64 - n))

/-- The FIPS 202 `ρ` rotation amount for lane `i = x + 5y`. -/
def rhoAmt (i : Fin 25) : Nat := rhoOffset i.val

/-- The `χ` step in the emitter's form: `A[x,y] ⊕ ((¬A[x+1,y]) ∧ A[x+2,y])`,
    with `¬e = e ^^^ allOnes`. Computed lane-by-lane from the post-ρπ state. -/
def cchi (y0 y1 y2 : BitVec 64) : BitVec 64 :=
  y0 ^^^ ((y1 ^^^ BitVec.allOnes 64) &&& y2)

/-- Closed-form `θ` column parity:
    `C[x] = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]`. -/
def cThetaC (s : Lanes) (x : Nat) : BitVec 64 :=
  s (laneIdx x 0) ^^^ s (laneIdx x 1) ^^^ s (laneIdx x 2) ^^^
    s (laneIdx x 3) ^^^ s (laneIdx x 4)

/-- Closed-form `θ` per-column D-word:
    `D[x] = C[x-1] ⊕ crotl(C[x+1], 1)` (indices mod 5). -/
def cThetaD (s : Lanes) (x : Nat) : BitVec 64 :=
  cThetaC s ((x + 4) % 5) ^^^ crotl (cThetaC s ((x + 1) % 5)) 1

/-- Closed-form `θ`: per-lane `A[x,y] ⊕= D[x]`. The `y` coordinate is implicit:
    `D[x]` is the same for all five `y`. -/
def cThetaClean (s : Lanes) : Lanes :=
  fun i => s i ^^^ cThetaD s (i.val % 5)

/-- Closed-form `ρ`: rotate lane `i` left by `rhoAmt i`. -/
def cRho (s : Lanes) : Lanes :=
  fun i => crotl (s i) (rhoAmt i)

/-- Closed-form `π`: FIPS 202 lane permutation
    `B[y, (2x + 3y) mod 5] = A[x, y]`. Inverted form: given the destination
    lane `(x', y')`, the source is `(x' + 3 y', x')` (since
    `2x + 3y = x'` and `y = x'` gives `x = (x' + 3 y') mod 5` and
    `y = x'`); FIPS 202 §3.2.3 gives the permutation as the matrix
    `(x, y) ↦ (y, (2x + 3y) mod 5)`. We index the result by destination
    `(x', y')` and read source `(x' + 3 y', x')`. -/
def cPi (s : Lanes) : Lanes :=
  fun i =>
    let xp := i.val % 5
    let yp := i.val / 5
    s (laneIdx ((xp + 3 * yp) % 5) xp)

/-- Closed-form `χ` (one lane): per-row, `A'[x, y] = A[x,y] ⊕ ((¬A[x+1,y]) ∧ A[x+2,y])`,
    with `¬e = e ^^^ allOnes`. -/
def cChi (s : Lanes) : Lanes :=
  fun i =>
    let x := i.val % 5
    let y := i.val / 5
    cchi (s (laneIdx x y))
         (s (laneIdx ((x + 1) % 5) y))
         (s (laneIdx ((x + 2) % 5) y))

/-- The full Keccak diffusion `θ∘ρ∘π∘χ` in closed form (the emitter's algebra). -/
def keccakClosedForm (s : Lanes) : Lanes := cChi (cPi (cRho (cThetaClean s)))

/-! ## 3. The FIPS 202 spec (same `Lanes` representation)

The FIPS 202 spec uses `BitVec.rotateLeft` for `ρ` and `~~~e` for `¬e`; both are
the *abstract* (`Nat`-encoded) primitives. Otherwise it shares the column/row
algebra with the closed form. -/

/-- FIPS spec left rotation. -/
def frotl (x : BitVec 64) (n : Nat) : BitVec 64 := x.rotateLeft n

/-- FIPS `χ` (one lane): `A'[x, y] = A[x,y] ⊕ ((¬A[x+1,y]) ∧ A[x+2,y])`. -/
def fchi (y0 y1 y2 : BitVec 64) : BitVec 64 := y0 ^^^ ((~~~ y1) &&& y2)

/-- FIPS `θ` column parity. -/
def fThetaC (s : Lanes) (x : Nat) : BitVec 64 :=
  s (laneIdx x 0) ^^^ s (laneIdx x 1) ^^^ s (laneIdx x 2) ^^^
    s (laneIdx x 3) ^^^ s (laneIdx x 4)

/-- FIPS `θ` D-word: `D[x] = C[x-1] ⊕ frotl(C[x+1], 1)`. -/
def fThetaD (s : Lanes) (x : Nat) : BitVec 64 :=
  fThetaC s ((x + 4) % 5) ^^^ frotl (fThetaC s ((x + 1) % 5)) 1

/-- FIPS `θ`. -/
def fTheta (s : Lanes) : Lanes :=
  fun i => s i ^^^ fThetaD s (i.val % 5)

/-- FIPS `ρ`: rotate lane `i` left by `rhoAmt i`. -/
def fRho (s : Lanes) : Lanes :=
  fun i => frotl (s i) (rhoAmt i)

/-- FIPS `π`: same permutation as `cPi` (it's a pure index map, no algebra). -/
def fPi (s : Lanes) : Lanes := cPi s

/-- FIPS `χ`. -/
def fChi (s : Lanes) : Lanes :=
  fun i =>
    let x := i.val % 5
    let y := i.val / 5
    fchi (s (laneIdx x y))
         (s (laneIdx ((x + 1) % 5) y))
         (s (laneIdx ((x + 2) % 5) y))

/-- The full FIPS 202 Keccak diffusion (the spec, `θ∘ρ∘π∘χ`). -/
def keccakFipsRound (s : Lanes) : Lanes := fChi (fPi (fRho (fTheta s)))

/-! ## 4. Per-step bit-exact identities (closed form = FIPS) -/

/-- `crotl` equals `frotl` (= `BitVec.rotateLeft`) at the 25 Keccak rotation
    amounts. Closed by `bv_decide` per amount. -/
theorem crotl_eq_frotl (x : BitVec 64) (n : Nat)
    (h : n = 0 ∨ n = 1 ∨ n = 62 ∨ n = 28 ∨ n = 27 ∨ n = 36 ∨ n = 44 ∨ n = 6 ∨
         n = 55 ∨ n = 20 ∨ n = 3 ∨ n = 10 ∨ n = 43 ∨ n = 25 ∨ n = 39 ∨ n = 41 ∨
         n = 45 ∨ n = 15 ∨ n = 21 ∨ n = 8 ∨ n = 18 ∨ n = 2 ∨ n = 61 ∨ n = 56 ∨
         n = 14) :
    crotl x n = frotl x n := by
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals (subst h; simp only [crotl, frotl]; bv_decide)

/-- `cchi` equals `fchi`: the `e ^ allOnes` and `~~~e` realizations of `¬e`
    agree at width 64. -/
theorem cchi_eq_fchi (y0 y1 y2 : BitVec 64) : cchi y0 y1 y2 = fchi y0 y1 y2 := by
  simp only [cchi, fchi]; bv_decide

/-! ## 5. Lane-wise equivalences of the four steps

We prove the diffusion identity step-by-step, each one a `funext` over the 25
lanes (or a structural `rfl` for `π`). -/

/-- The inner `crotl` inside `cThetaD` rewrites to `frotl` at the fixed amount 1
    (the only `ρ`-style rotation `θ` uses). -/
theorem cThetaD_inner_rot_eq (x : BitVec 64) :
    crotl x 1 = frotl x 1 :=
  crotl_eq_frotl x 1 (Or.inr (Or.inl rfl))

/-- `cThetaClean = fTheta`: definitionally the same algebra; the inner `crotl`
    inside `cThetaD` rewrites to `frotl` at amount `1` via `cThetaD_inner_rot_eq`. -/
theorem cTheta_eq_fTheta (s : Lanes) : cThetaClean s = fTheta s := by
  funext i
  simp only [cThetaClean, fTheta, cThetaD, fThetaD, cThetaC, fThetaC,
    cThetaD_inner_rot_eq]

/-- `cRho = fRho`: per-lane, `crotl (s i) (rhoAmt i) = frotl (s i) (rhoAmt i)`.
    The rotation amount is one of the 25 FIPS 202 ρ offsets, and `crotl_eq_frotl`
    discharges by `bv_decide`. -/
theorem cRho_eq_fRho (s : Lanes) : cRho s = fRho s := by
  funext i
  apply crotl_eq_frotl
  -- The rotation amount is `rhoOffset i.val`. Case on `i : Fin 25`:
  fin_cases i <;> (simp only [rhoAmt, rhoOffset]; tauto)

/-- `cPi = fPi`: defined as the same index map. -/
theorem cPi_eq_fPi (s : Lanes) : cPi s = fPi s := rfl

/-- `cChi = fChi`: per-lane `cchi = fchi` by `cchi_eq_fchi`. -/
theorem cChi_eq_fChi (s : Lanes) : cChi s = fChi s := by
  funext i
  simp only [cChi, fChi, cchi_eq_fchi]

/-! ## 6. The full diffusion identity (the headline) -/

/-- **The Keccak diffusion `θ∘ρ∘π∘χ` in closed form equals the FIPS 202 spec.**
    Per-lane bit-exact identity: the emitter's `(x <<< n) ||| (x >>> (64 - n))`
    realization of left rotation, and `e ^^^ allOnes` realization of `¬e`,
    together with the index-permutation `π` and the column-parity `θ`, compose
    to exactly the FIPS 202 Keccak round transformation. Closed by `bv_decide`
    (LRAT) for the per-amount rotation lemmas and the `χ` algebraic identity;
    `rfl` for the `π` index permutation; `funext` over the 25 lanes for the
    state-level identity. No `native_decide`, no KAT, no open goals. -/
theorem keccak_diffuse_bitexact (s : Lanes) :
    keccakClosedForm s = keccakFipsRound s := by
  simp only [keccakClosedForm, keccakFipsRound,
    cTheta_eq_fTheta, cRho_eq_fRho, cPi_eq_fPi, cChi_eq_fChi]

/-! ## 7. ι and the full round

`KeccakIotaIndexed.keccak_iota_loop_bitexact` proves the per-round
constant XOR indexed-bit-exact. We expose the per-lane `ι` step on `Lanes` and
the full FIPS 202 round (diffusion ∘ ι) as composition with that result. -/

/-- One step of ι: lane 0 XORs the round constant; lanes 1..24 are unchanged. -/
def iotaApply (s : Lanes) (rc : BitVec 64) : Lanes :=
  fun i => if i.val = 0 then s i ^^^ rc else s i

/-- **The full FIPS 202 Keccak round transformation** on `Lanes`: diffusion
    `θ∘ρ∘π∘χ` followed by ι (per-round constant XOR into lane 0). The closed
    form (this file) and the FIPS spec coincide on the diffusion (by
    `keccak_diffuse_bitexact`); `ι` is the same per-lane operation in both
    presentations (a pure XOR into lane 0). -/
def keccakFullRound (s : Lanes) (rc : BitVec 64) : Lanes :=
  iotaApply (keccakFipsRound s) rc

/-- **The closed-form full Keccak round**, used by the emitter. -/
def keccakClosedFullRound (s : Lanes) (rc : BitVec 64) : Lanes :=
  iotaApply (keccakClosedForm s) rc

/-- **Headline theorem**: the closed-form Keccak round equals the FIPS 202 spec
    round, bit-exactly, on every lane, for every per-round constant `rc`.
    Composition of `keccak_diffuse_bitexact` and the ι identity (which is
    `rfl`, since both sides apply the same per-lane XOR). -/
theorem keccak_round_bitexact (s : Lanes) (rc : BitVec 64) :
    keccakClosedFullRound s rc = keccakFullRound s rc := by
  simp only [keccakClosedFullRound, keccakFullRound, keccak_diffuse_bitexact]

/-! ## 8. Relation to `KeccakBitexact`

`KeccakBitexact.keccak_round_loop_bitexact` proves the emitted
`for round = 0 to 24 { acc = keccakDiffuse(acc) ⊕ RC[round] }` denotes
`keccak_f bitexactSteps init` — the 24-fold composition of (`keccakDiffuse` then
the FIPS 202 ι), where `keccakDiffuse` is a model map for the diffusion. This
module proves the closed-form diffusion `keccakClosedForm` equals the FIPS 202
spec `keccakFipsRound` **bit-exactly**. The model map `keccakDiffuse` is a
word-level stand-in, `(acc <<< acc.toNat) ^^^ acc`, not θ∘ρ∘π∘χ, so no statement
here relates the emitted loop to `keccakClosedForm`. -/

/-- **Composition corollary**: the closed-form full round equals the FIPS 202
    full round (a restatement of `keccak_round_bitexact`). -/
theorem keccak_round_loop_bitexact_via_fips :
    ∀ (s : Lanes) (rc : BitVec 64),
      keccakClosedFullRound s rc = keccakFullRound s rc :=
  keccak_round_bitexact

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact
