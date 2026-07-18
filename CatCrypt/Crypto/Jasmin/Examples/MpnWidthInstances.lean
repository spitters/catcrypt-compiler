/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnGenericWidth
import CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnSubPrototype

set_option autoImplicit false

/-!
# Width instances of the generic mpn core + concrete↔generic bridge

**EXPERIMENTAL FILE.** This file cashes in the width-parametric payoff of
`MpnGenericWidth`: it instantiates the *one* generic carry-chain core
`mpnAddNW` at the two widths the limb-width fork demanded — `w = 32`
(Lean's fallback seam) and `w = 64` (real GMP) — and re-derives each
width's functional spec by **direct instantiation** of the single generic
proof `mpnAddNW_spec`. No new induction is run; the `∀ w` theorem already
covers both.

It then bridges the generic core back to the *pre-existing* concrete
64-bit kernel `MpnAddPrototype.mpnAddN`: the bridge theorems state that the
concrete kernel **is** the generic core specialized at `w = 64`, i.e.

* `MpnAddPrototype.toNat   = MpnGenericWidth.toNatW 64`
* `MpnAddPrototype.adcStep = MpnGenericWidth.adcStepW 64`
* `MpnAddPrototype.mpnAddN = MpnGenericWidth.mpnAddNW 64`

These hold **pointwise-definitionally** — agreement on every input, with
each leaf step closing by `rfl` — but *not* by a single `rfl` on the
unapplied functions. The reason is purely the equation compiler: each
width-generic definition carries an explicit `w` parameter and is compiled
to its own match auxiliary, distinct from the concrete kernel's, so the
closed functions do not unfold to one another. The proofs are therefore
`funext` + a structural induction whose every branch is `rfl`
(`adcStep`/`carryNat`, the non-recursive ones, even close directly). No
arithmetic side goal ever appears — the only "work" is the recursion
shuffle. This is the justification for eventually re-deriving the concrete
kernels as generic instances **without** an invasive refactor: they compute
the same function on every input, so the refactor is a renaming backed by a
one-line `funext`, not a re-proof of the carry chain.

No existing file is edited; this file only imports and reuses.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnWidthInstances

open CatCrypt.Crypto.Jasmin.Examples

/-! ## §1  Instantiate the generic core at `w = 32` and `w = 64`

`mpnAdd32`/`mpnAdd64` are the generic carry-chain core `mpnAddNW`
specialized to the two machine widths. Both come from the *same*
definition; only the width numeral differs. -/

/-- Width-32 limb addition: the generic core at the fallback seam. -/
def mpnAdd32 : List (BitVec 32) → List (BitVec 32) → Bool →
    (List (BitVec 32) × Bool) :=
  MpnGenericWidth.mpnAddNW 32

/-- Width-64 limb addition: the generic core at the real-GMP width. -/
def mpnAdd64 : List (BitVec 64) → List (BitVec 64) → Bool →
    (List (BitVec 64) × Bool) :=
  MpnGenericWidth.mpnAddNW 64

/-! ## §2  Per-width specs, by direct instantiation of `mpnAddNW_spec`

Each spec is `mpnAddNW_spec` with `w` fixed; the proof is a one-liner that
unfolds the width instance and applies the generic theorem. No new
induction. -/

/-- **Width-32 functional spec**, obtained by instantiating the single
    generic proof `mpnAddNW_spec` at `w = 32`. This is the spec the
    fallback (32-bit) seam needs. -/
theorem mpnAdd32_spec (a b : List (BitVec 32)) (hlen : a.length = b.length)
    (cin : Bool) :
    MpnGenericWidth.toNatW 32 (mpnAdd32 a b cin).1
      + (2 ^ 32) ^ a.length * MpnGenericWidth.carryNat (mpnAdd32 a b cin).2
    = MpnGenericWidth.toNatW 32 a + MpnGenericWidth.toNatW 32 b
      + MpnGenericWidth.carryNat cin := by
  unfold mpnAdd32
  exact MpnGenericWidth.mpnAddNW_spec 32 a b hlen cin

/-- **Width-64 functional spec**, obtained by instantiating the single
    generic proof `mpnAddNW_spec` at `w = 64`. This matches (denotationally)
    the concrete kernel's `mpnAddN_spec`; §3 shows it is in fact the same
    statement on the nose. -/
theorem mpnAdd64_spec (a b : List (BitVec 64)) (hlen : a.length = b.length)
    (cin : Bool) :
    MpnGenericWidth.toNatW 64 (mpnAdd64 a b cin).1
      + (2 ^ 64) ^ a.length * MpnGenericWidth.carryNat (mpnAdd64 a b cin).2
    = MpnGenericWidth.toNatW 64 a + MpnGenericWidth.toNatW 64 b
      + MpnGenericWidth.carryNat cin := by
  unfold mpnAdd64
  exact MpnGenericWidth.mpnAddNW_spec 64 a b hlen cin

/-- Carry-in-`false` entry point at `w = 32`, from
    `mpnAddNW_spec_carryIn_false`. -/
theorem mpnAdd32_spec_carryIn_false (a b : List (BitVec 32))
    (hlen : a.length = b.length) :
    MpnGenericWidth.toNatW 32 (mpnAdd32 a b false).1
      + (2 ^ 32) ^ a.length * MpnGenericWidth.carryNat (mpnAdd32 a b false).2
    = MpnGenericWidth.toNatW 32 a + MpnGenericWidth.toNatW 32 b := by
  unfold mpnAdd32
  exact MpnGenericWidth.mpnAddNW_spec_carryIn_false 32 a b hlen

/-- Carry-in-`false` entry point at `w = 64`. -/
theorem mpnAdd64_spec_carryIn_false (a b : List (BitVec 64))
    (hlen : a.length = b.length) :
    MpnGenericWidth.toNatW 64 (mpnAdd64 a b false).1
      + (2 ^ 64) ^ a.length * MpnGenericWidth.carryNat (mpnAdd64 a b false).2
    = MpnGenericWidth.toNatW 64 a + MpnGenericWidth.toNatW 64 b := by
  unfold mpnAdd64
  exact MpnGenericWidth.mpnAddNW_spec_carryIn_false 64 a b hlen

/-! ## §3  Concrete ↔ generic bridge: the 64-bit kernel IS the generic core

The pre-existing concrete kernel in `MpnAddPrototype` is, function for
function, the generic core specialized at `w = 64`. The bridges are *not*
closed by a single `rfl` on the unapplied functions: each width-generic
definition (`toNatW`, `adcStepW`, `mpnAddNW`) carries an explicit `w`
parameter and is compiled by the equation compiler to its own match
auxiliary, distinct from the concrete kernel's. They do, however, agree
**pointwise** on every input — and that pointwise agreement is itself
*definitional* (the bodies coincide after substituting the numeral `64` for
`w` and unfolding the equation lemmas). So:

* the recursive denotation/carry-chain bridges close by `funext` +
  induction with the generated equation lemmas (`simp [toNat, toNatW]`,
  resp. `simp [mpnAddN, mpnAddNW]`), where every leaf step is `rfl`;
* the non-recursive `adcStep` bridge closes pointwise by `rfl` (after
  `funext`, the `let`-bodies are syntactically identical at `w = 64`).

The honest verdict (see §6) is therefore: **pointwise-definitional, not
`rfl`-on-the-functions** — but the only "real" work is the structural
recursion shuffle, never an arithmetic side goal. -/

/-- **Denotation bridge (applied).** The concrete little-endian denotation
    is the generic one at `w = 64` on every limb list. Each induction step
    is `rfl` via the equation lemmas. -/
theorem toNat_apply_eq (xs : List (BitVec 64)) :
    MpnAddPrototype.toNat xs = MpnGenericWidth.toNatW 64 xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [MpnAddPrototype.toNat, MpnGenericWidth.toNatW, ih]

/-- **Denotation bridge (unapplied).** `funext` lifts the pointwise bridge
    to the functions. -/
theorem toNat_eq_toNatW64 :
    MpnAddPrototype.toNat = MpnGenericWidth.toNatW 64 := by
  funext xs; exact toNat_apply_eq xs

/-- **ADC-step bridge (applied).** The concrete single-limb ADC step is the
    generic one at `w = 64`. Pointwise `rfl`: the `let`-bodies coincide once
    `w` is the numeral `64`. -/
theorem adcStep_apply_eq (a b : BitVec 64) (cin : Bool) :
    MpnAddPrototype.adcStep a b cin = MpnGenericWidth.adcStepW 64 a b cin := rfl

/-- **ADC-step bridge (unapplied).** -/
theorem adcStep_eq_adcStepW64 :
    MpnAddPrototype.adcStep = MpnGenericWidth.adcStepW 64 := by
  funext a b cin; exact adcStep_apply_eq a b cin

/-- **Carry-chain bridge (applied).** The concrete multi-limb add reference
    is the generic core at `w = 64` on every input. The two-limb-list
    recursion is shuffled by induction; each step reduces to the shared ADC
    step (`adcStep_apply_eq`) by `rfl`. -/
theorem mpnAddN_apply_eq :
    ∀ (a b : List (BitVec 64)) (cin : Bool),
      MpnAddPrototype.mpnAddN a b cin = MpnGenericWidth.mpnAddNW 64 a b cin := by
  intro a
  induction a with
  | nil => intro b cin; cases b <;> rfl
  | cons x xs ih =>
    intro b cin
    cases b with
    | nil => rfl
    | cons y ys =>
      -- Both sides peel one ADC step (definitionally the same step) and
      -- recurse on the tails; the tail equality is the IH.
      simp only [MpnAddPrototype.mpnAddN, MpnGenericWidth.mpnAddNW,
                 MpnAddPrototype.adcStep, MpnGenericWidth.adcStepW, ih]

/-- **Carry-chain bridge (unapplied).** The concrete kernel *is* the generic
    core at `w = 64`. -/
theorem mpnAddN_eq_mpnAddNW64 :
    MpnAddPrototype.mpnAddN = MpnGenericWidth.mpnAddNW 64 := by
  funext a b cin; exact mpnAddN_apply_eq a b cin

/-- The concrete carry-bit-to-`Nat` map is the generic one. This one *is*
    `rfl` on the functions: both are the non-recursive `fun c => if c then 1
    else 0`. -/
theorem carryNat_eq :
    MpnAddPrototype.carryNat = MpnGenericWidth.carryNat := rfl

/-- The concrete kernel coincides with the width-64 instance defined in §1,
    via `mpnAddN_eq_mpnAddNW64`. -/
theorem mpnAddN_eq_mpnAdd64 :
    MpnAddPrototype.mpnAddN = mpnAdd64 := mpnAddN_eq_mpnAddNW64

/-! ## §4  The concrete kernel's spec, re-derived through the bridge

`MpnAddPrototype.mpnAddN_spec` is now visibly an instance of the generic
`mpnAddNW_spec`: rewriting the concrete kernel to `mpnAddNW 64` (the `rfl`
bridge) turns the concrete statement into the generic one at `w = 64`. We
record this to witness that the eventual refactor (re-deriving the concrete
spec from the generic one) needs no new proof. -/

/-- The concrete kernel's functional spec follows from the generic spec via
    the pointwise bridges — no separate induction. Rewriting each concrete
    symbol to its generic counterpart at `w = 64` turns the goal into
    `mpnAddNW_spec 64`. -/
theorem mpnAddN_spec_via_generic (a b : List (BitVec 64))
    (hlen : a.length = b.length) (cin : Bool) :
    MpnAddPrototype.toNat (MpnAddPrototype.mpnAddN a b cin).1
      + (2 ^ 64) ^ a.length
          * MpnAddPrototype.carryNat (MpnAddPrototype.mpnAddN a b cin).2
    = MpnAddPrototype.toNat a + MpnAddPrototype.toNat b
      + MpnAddPrototype.carryNat cin := by
  -- `carryNat` is `rfl`-equal across namespaces, so only the recursive
  -- symbols need rewriting; afterwards the goal is literally `mpnAddNW_spec`.
  rw [mpnAddN_apply_eq, toNat_apply_eq, toNat_apply_eq, toNat_apply_eq]
  exact MpnGenericWidth.mpnAddNW_spec 64 a b hlen cin

/-! ## §5  Concrete sanity checks at both widths from the instances -/

-- w = 64 overflow, through the named instance.
example : mpnAdd64 [(-1 : BitVec 64)] [1] false = ([0], true) := by native_decide
-- w = 32 overflow at the fallback width, through the named instance.
example : mpnAdd32 [(-1 : BitVec 32)] [1] false = ([0], true) := by native_decide
-- The concrete kernel agrees with the width-64 instance on every input
-- (here a sample), via the bridge.
example :
    MpnAddPrototype.mpnAddN [(-1 : BitVec 64), 0] [1, 0] false
      = mpnAdd64 [(-1 : BitVec 64), 0] [1, 0] false := by
  rw [mpnAddN_eq_mpnAdd64]

/-! ## §6  Honest verdict (calibrating the eventual refactor)

* **Instances + specs (§1–§2):** `mpnAdd32`/`mpnAdd64` are the *one* generic
  core `mpnAddNW` at two widths; their specs are `mpnAddNW_spec` instantiated
  at `w = 32` / `w = 64`, each a one-line `exact`. No new induction runs —
  the width-parametric proof already covers both seams. This is the payoff.

* **Concrete ↔ generic bridge (§3):** the verdict on
  `mpnAddN ≡ mpnAddNW 64` (and `toNat`/`adcStep`) is
  **pointwise-definitional, not `rfl`-on-the-functions**:
  - `carryNat_eq` *is* a bare `rfl` (non-recursive, identical bodies).
  - `adcStep_apply_eq` is a pointwise `rfl` (after `funext`, the `let`-bodies
    coincide at the numeral `64`).
  - `toNat`/`mpnAddN` need `funext` + a structural induction, but **every
    leaf step closes by `rfl`** (`simp only` with the generated equation
    lemmas); no arithmetic goal ever appears.
  The obstruction to a single function-level `rfl` is *only* the equation
  compiler: the generic defs carry an explicit `w` parameter and compile to
  distinct match auxiliaries.

* **Refactor calibration:** because the agreement is definitional on every
  input, re-deriving the concrete kernels as `mpnAddNW 64` instances is a
  *renaming*, not a re-proof. The carry-chain spec transfers with a
  three-rewrite bridge (`mpnAddN_spec_via_generic`), so the eventual
  refactor costs a `funext` + the equation-lemma `simp`, never a new
  induction over the limb list.
-/

/-! ## §7  Sub instances of the generic core at `w = 32` and `w = 64`

Mirror of §1–§3 for SBB / `mpnSubNW`. The same payoff: one width-parametric
sub spec covers both fallback (32) and real-GMP (64) widths; the concrete
64-bit kernel `MpnSubPrototype.mpnSubN` is the generic core at `w = 64`
pointwise (definitionally). -/

/-- Width-32 limb subtraction: the generic core at the fallback seam.
    Mirror of `mpnAdd32`. -/
def mpnSub32 : List (BitVec 32) → List (BitVec 32) → Bool →
    (List (BitVec 32) × Bool) :=
  MpnGenericWidth.mpnSubNW 32

/-- Width-64 limb subtraction: the generic core at the real-GMP width.
    Mirror of `mpnAdd64`. -/
def mpnSub64 : List (BitVec 64) → List (BitVec 64) → Bool →
    (List (BitVec 64) × Bool) :=
  MpnGenericWidth.mpnSubNW 64

/-- **Tie-in lemma.** `mpnSub32` is the width-parametric `mpnSubNW`
    specialized at `w = 32`. Closes by `rfl` because §7 *defines*
    `mpnSub32` to be that specialization. This is the one-line lemma the
    follow-up `MpnSub32Refines` cleanup will use to drop its local
    `mpnSubN32` clone in favor of the generic core. -/
theorem mpnSub32_eq_generic :
    mpnSub32 = MpnGenericWidth.mpnSubNW 32 := rfl

/-- Tie-in lemma at `w = 64`. -/
theorem mpnSub64_eq_generic :
    mpnSub64 = MpnGenericWidth.mpnSubNW 64 := rfl

/-! ## §8  Per-width sub specs, by direct instantiation of `mpnSubNW_toNat`

Mirror of §2 for SBB. No new induction. -/

/-- **Width-32 functional sub spec**, by instantiating `mpnSubNW_toNat` at
    `w = 32`. -/
theorem mpnSub32_spec (a b : List (BitVec 32)) (hlen : a.length = b.length)
    (bin : Bool) :
    MpnGenericWidth.toNatW 32 (mpnSub32 a b bin).1
      + MpnGenericWidth.toNatW 32 b
      + MpnGenericWidth.borrowNat bin
    = MpnGenericWidth.toNatW 32 a
      + (2 ^ 32) ^ a.length
          * MpnGenericWidth.borrowNat (mpnSub32 a b bin).2 := by
  unfold mpnSub32
  exact MpnGenericWidth.mpnSubNW_toNat 32 a b hlen bin

/-- **Width-64 functional sub spec**, by instantiating `mpnSubNW_toNat` at
    `w = 64`. -/
theorem mpnSub64_spec (a b : List (BitVec 64)) (hlen : a.length = b.length)
    (bin : Bool) :
    MpnGenericWidth.toNatW 64 (mpnSub64 a b bin).1
      + MpnGenericWidth.toNatW 64 b
      + MpnGenericWidth.borrowNat bin
    = MpnGenericWidth.toNatW 64 a
      + (2 ^ 64) ^ a.length
          * MpnGenericWidth.borrowNat (mpnSub64 a b bin).2 := by
  unfold mpnSub64
  exact MpnGenericWidth.mpnSubNW_toNat 64 a b hlen bin

/-! ## §9  Concrete ↔ generic sub bridge: the 64-bit kernel IS the generic core

Mirror of §3 for SBB. `MpnSubPrototype.sbbStep`/`mpnSubN`/`borrowNat`
agree pointwise-definitionally with the generic versions at `w = 64`. -/

/-- **SBB-step bridge (applied).** The concrete single-limb SBB step is
    the generic one at `w = 64`. Pointwise `rfl`: the `let`-bodies coincide
    once `w` is the numeral `64`. -/
theorem sbbStep_apply_eq (a b : BitVec 64) (bin : Bool) :
    MpnSubPrototype.sbbStep a b bin = MpnGenericWidth.sbbStepW 64 a b bin := rfl

/-- **SBB-step bridge (unapplied).** -/
theorem sbbStep_eq_sbbStepW64 :
    MpnSubPrototype.sbbStep = MpnGenericWidth.sbbStepW 64 := by
  funext a b bin; exact sbbStep_apply_eq a b bin

/-- **Borrow-chain bridge (applied).** The concrete 64-bit `mpnSubN` is the
    generic core at `w = 64` on every input. Mirror of `mpnAddN_apply_eq`. -/
theorem mpnSubN_apply_eq :
    ∀ (a b : List (BitVec 64)) (bin : Bool),
      MpnSubPrototype.mpnSubN a b bin = MpnGenericWidth.mpnSubNW 64 a b bin := by
  intro a
  induction a with
  | nil => intro b bin; cases b <;> rfl
  | cons x xs ih =>
    intro b bin
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [MpnSubPrototype.mpnSubN, MpnGenericWidth.mpnSubNW,
                 MpnSubPrototype.sbbStep, MpnGenericWidth.sbbStepW, ih]

/-- **Borrow-chain bridge (unapplied).** The concrete kernel *is* the
    generic core at `w = 64`. -/
theorem mpnSubN_eq_mpnSubNW64 :
    MpnSubPrototype.mpnSubN = MpnGenericWidth.mpnSubNW 64 := by
  funext a b bin; exact mpnSubN_apply_eq a b bin

/-- The concrete borrow-bit-to-`Nat` map is the generic one. `rfl` on the
    functions: both are the non-recursive `fun b => if b then 1 else 0`. -/
theorem borrowNat_eq :
    MpnSubPrototype.borrowNat = MpnGenericWidth.borrowNat := rfl

/-- The concrete 64-bit kernel coincides with the width-64 sub instance
    defined in §7, via `mpnSubN_eq_mpnSubNW64`. -/
theorem mpnSubN_eq_mpnSub64 :
    MpnSubPrototype.mpnSubN = mpnSub64 := mpnSubN_eq_mpnSubNW64

/-! ## §10  Concrete sanity checks at both widths from the sub instances -/

-- w = 64: `[0] - [1]` underflows.
example : mpnSub64 [(0 : BitVec 64)] [1] false = ([-1], true) := by native_decide
-- w = 32: same underflow at the fallback width.
example : mpnSub32 [(0 : BitVec 32)] [1] false = ([-1], true) := by native_decide
-- The concrete 64-bit kernel agrees with the width-64 sub instance.
example :
    MpnSubPrototype.mpnSubN [(0 : BitVec 64), 1] [1, 0] false
      = mpnSub64 [(0 : BitVec 64), 1] [1, 0] false := by
  rw [mpnSubN_eq_mpnSub64]

/-! ## §11  Divrem / divexact instances of the generic core at `w = 32` / `w = 64`

Mirror of §1 / §7 for the width-parametric divrem and exact-division cores
in `MpnGenericWidth`. The same payoff: one width-parametric reference covers
both fallback (32) and real-GMP (64) widths; the instances are one-line
specializations, and the tie-ins are `rfl`. -/

/-- Width-32 multi-precision divrem: the generic core at the fallback seam.
    Mirror of `mpnAdd32` / `mpnSub32`. -/
noncomputable def mpnDivRem32 :
    List (BitVec 32) → List (BitVec 32) → List (BitVec 32) × List (BitVec 32) :=
  MpnGenericWidth.mpnDivRemNW 32

/-- Width-64 multi-precision divrem: the generic core at the real-GMP width.
    Mirror of `mpnAdd64` / `mpnSub64`. -/
noncomputable def mpnDivRem64 :
    List (BitVec 64) → List (BitVec 64) → List (BitVec 64) × List (BitVec 64) :=
  MpnGenericWidth.mpnDivRemNW 64

/-- Width-32 exact division: the generic core at the fallback seam. -/
noncomputable def mpnDivExact32 :
    List (BitVec 32) → List (BitVec 32) → List (BitVec 32) :=
  MpnGenericWidth.mpnDivExactW 32

/-- Width-64 exact division: the generic core at the real-GMP width. -/
noncomputable def mpnDivExact64 :
    List (BitVec 64) → List (BitVec 64) → List (BitVec 64) :=
  MpnGenericWidth.mpnDivExactW 64

/-- **Tie-in lemma.** `mpnDivRem32` is the width-parametric `mpnDivRemNW`
    specialized at `w = 32`. Closes by `rfl` because §11 *defines*
    `mpnDivRem32` to be that specialization. Mirror of
    `mpnSub32_eq_generic`. -/
theorem mpnDivRem32_eq_generic :
    mpnDivRem32 = MpnGenericWidth.mpnDivRemNW 32 := rfl

/-- Tie-in lemma at `w = 64`. -/
theorem mpnDivRem64_eq_generic :
    mpnDivRem64 = MpnGenericWidth.mpnDivRemNW 64 := rfl

/-- Tie-in lemma for `mpnDivExact32`. -/
theorem mpnDivExact32_eq_generic :
    mpnDivExact32 = MpnGenericWidth.mpnDivExactW 32 := rfl

/-- Tie-in lemma for `mpnDivExact64`. -/
theorem mpnDivExact64_eq_generic :
    mpnDivExact64 = MpnGenericWidth.mpnDivExactW 64 := rfl

/-! ## §12  Per-width divrem / divexact specs, by direct instantiation

Each spec is `mpnDivRemNW_toNat` / `mpnDivExactW_toNat` with `w` fixed; the
proof is a one-liner. No new induction. -/

/-- **Width-32 Euclidean divrem spec**, by instantiating
    `mpnDivRemNW_toNat` at `w = 32`. -/
theorem mpnDivRem32_spec (a b : List (BitVec 32))
    (hd : MpnGenericWidth.toNatW 32 b ≠ 0) :
    MpnGenericWidth.toNatW 32 a
      = MpnGenericWidth.toNatW 32 (mpnDivRem32 a b).1
          * MpnGenericWidth.toNatW 32 b
        + MpnGenericWidth.toNatW 32 (mpnDivRem32 a b).2
    ∧ MpnGenericWidth.toNatW 32 (mpnDivRem32 a b).2
        < MpnGenericWidth.toNatW 32 b := by
  unfold mpnDivRem32
  exact MpnGenericWidth.mpnDivRemNW_toNat 32 a b hd

/-- **Width-64 Euclidean divrem spec**, by instantiating
    `mpnDivRemNW_toNat` at `w = 64`. -/
theorem mpnDivRem64_spec (a b : List (BitVec 64))
    (hd : MpnGenericWidth.toNatW 64 b ≠ 0) :
    MpnGenericWidth.toNatW 64 a
      = MpnGenericWidth.toNatW 64 (mpnDivRem64 a b).1
          * MpnGenericWidth.toNatW 64 b
        + MpnGenericWidth.toNatW 64 (mpnDivRem64 a b).2
    ∧ MpnGenericWidth.toNatW 64 (mpnDivRem64 a b).2
        < MpnGenericWidth.toNatW 64 b := by
  unfold mpnDivRem64
  exact MpnGenericWidth.mpnDivRemNW_toNat 64 a b hd

/-- **Width-32 exact-division spec**, by instantiating `mpnDivExactW_toNat`
    at `w = 32`. -/
theorem mpnDivExact32_spec (a b : List (BitVec 32))
    (hd : MpnGenericWidth.toNatW 32 b ≠ 0) :
    MpnGenericWidth.toNatW 32 (mpnDivExact32 a b)
      = MpnGenericWidth.toNatW 32 a / MpnGenericWidth.toNatW 32 b := by
  unfold mpnDivExact32
  exact MpnGenericWidth.mpnDivExactW_toNat 32 a b hd

/-- **Width-64 exact-division spec**, by instantiating `mpnDivExactW_toNat`
    at `w = 64`. -/
theorem mpnDivExact64_spec (a b : List (BitVec 64))
    (hd : MpnGenericWidth.toNatW 64 b ≠ 0) :
    MpnGenericWidth.toNatW 64 (mpnDivExact64 a b)
      = MpnGenericWidth.toNatW 64 a / MpnGenericWidth.toNatW 64 b := by
  unfold mpnDivExact64
  exact MpnGenericWidth.mpnDivExactW_toNat 64 a b hd

end CatCrypt.Crypto.Jasmin.Examples.MpnWidthInstances
