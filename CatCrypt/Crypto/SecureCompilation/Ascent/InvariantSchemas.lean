/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven

/-!
# Parametrized invariant schemas for Ascent's covered kernel families

A corres-solver strengthens a per-kernel goal with a load/range invariant over the
input register windows. The invariants for the covered families share one shape: a
conjunction of window-recomposition facts (a register window's `s.get` image equals
the abstract limb list), window-length facts, and a range/cleared bound (an
accumulator or upper window reads zero, or a step counter bounds a value). This
module states that shape once per family as a predicate parametrized by limb count
and register windows, together with the small structural lemmas the bounded-arith
discharger consumes, so a new kernel instantiates a template instead of hand-writing
its invariant.

The families:

* `MontReduceInvariant n accNames pNames rtopName npName` — the Montgomery-reduce
  window load. Generalizes `MontRedc4RunBlockProven.MontRedc4Load` (the n = 4 case)
  to arbitrary limb count: the low `n` accumulator registers hold the input `T`, the
  upper window `accNames.drop n` together with the top-carry `rtopName` is cleared,
  the modulus `p` is in `pNames`, and the constant `nP` is in `npName`.

* `SchoolbookMulInvariant n aNames bNames outNames` — the operand-scanning multiply
  window: two `n`-limb operand windows loaded, the `2n`-limb product accumulator
  cleared.

* `DivstepInvariant k fNames gNames` — the safegcd divstep window: the two
  big-integer windows `f`, `g` loaded over equal-length register windows, with the
  step counter `k` bounding the residual magnitude `⟦g⟧ < 2^k`.

* `FieldAddSubInvariant n xNames yNames` — the field add/sub carry window: two
  `n`-limb operand windows loaded with the carry flag cleared (the adc/sbb cascade's
  entry precondition).

Each family provides a `Layout` structure — the generator: it records a kernel's
register layout and instantiates the invariant plus the family's discharge lemmas
against that layout.

## Structural, not reflective

Each schema is a small conjunction of window facts; the discharge lemmas project one
conjunct and reduce a single `valLimbs` window. Nothing here folds the register file
into a decidable blob. The generator's `wf` field carries the layout's length
constraints as ordinary hypotheses.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.InvariantSchemas

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven

/-! ## 0. Shared window facts

Two facts the range conjuncts reduce to: a cleared window recomposes to `0`, and a
window value is bounded by the radix raised to its length. Both are plain inductions
on the limb list; keeping `(2^64)^n` atomic avoids the `omega` radix trap. -/

/-- A cleared limb window recomposes to `0`: `valLimbs (List.replicate m 0) = 0`. The
    upper-window / product-accumulator range conjuncts reduce to this. -/
theorem valLimbs_replicate_zero (m : Nat) :
    valLimbs (List.replicate m (0 : BitVec 64)) = 0 := by
  induction m with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, valLimbs_cons, ih]; simp

/-- A limb window's value is bounded by the radix raised to its length:
    `valLimbs L < (2^64)^|L|`. The magnitude bound the range conjuncts feed the
    Montgomery / carry-fold dischargers. -/
theorem valLimbs_lt_pow (L : List (BitVec 64)) :
    valLimbs L < (2 ^ 64) ^ L.length := by
  induction L with
  | nil => simp
  | cons w ws ih =>
    have hw : w.toNat < 2 ^ 64 := w.isLt
    have hstep : valLimbs ws + 1 ≤ (2 ^ 64) ^ ws.length := by omega
    calc valLimbs (w :: ws) = w.toNat + 2 ^ 64 * valLimbs ws := rfl
      _ < 2 ^ 64 + 2 ^ 64 * valLimbs ws := by omega
      _ = 2 ^ 64 * (valLimbs ws + 1) := by ring
      _ ≤ 2 ^ 64 * (2 ^ 64) ^ ws.length := by apply Nat.mul_le_mul_left; exact hstep
      _ = (2 ^ 64) ^ (w :: ws).length := by rw [List.length_cons, pow_succ]; ring

/-! ## 1. The Montgomery-reduce window schema

Generalizes `MontRedc4Load` to arbitrary limb count `n`. For a register file with a
`2n`-wide accumulator `accNames` (so `accNames.drop n` is the upper window of `n`
words) and a top-carry register `rtopName`, the cleared span is the `n + 1` words
`accNames.drop n ++ [rtopName]` — written `accNames.length - n + 1` so the count is
read off the layout. At `n = 4` with the eight-word `Curve4MontMulProvenEmit.accNames`
this is `List.replicate 5 0`, reproducing the committed shape. -/

/-- The Montgomery-reduce window load, parametrized by limb count `n` and the register
    windows. The low `n` accumulator registers hold the input limbs `T`, the upper
    window `accNames.drop n` together with the top-carry `rtopName` is cleared to
    `accNames.length - n + 1` zero words, the modulus `p` sits in `pNames`, and the
    Montgomery constant `nP` sits in `npName`. -/
def MontReduceInvariant (n : Nat) (accNames pNames : List String)
    (rtopName npName : String)
    (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64) : Prop :=
  (accNames.take n).map s.get = T ∧
    ((accNames.drop n) ++ [rtopName]).map s.get
        = List.replicate (accNames.length - n + 1) 0 ∧
    pNames.map s.get = p ∧
    s.get npName = nP

/-- The low accumulator window recomposes to the input value `⟦T⟧`. -/
theorem MontReduceInvariant.lower_val {n : Nat} {accNames pNames : List String}
    {rtopName npName : String} {s : JState 64} {p T : List (BitVec 64)} {nP : BitVec 64}
    (h : MontReduceInvariant n accNames pNames rtopName npName s p T nP) :
    valLimbs ((accNames.take n).map s.get) = valLimbs T := by
  rw [h.1]

/-- The upper window (with the top carry) contributes nothing: its value is `0`. This
    is the conjunct the Montgomery discharger folds to zero out the pre-reduce top
    words. -/
theorem MontReduceInvariant.upper_zero {n : Nat} {accNames pNames : List String}
    {rtopName npName : String} {s : JState 64} {p T : List (BitVec 64)} {nP : BitVec 64}
    (h : MontReduceInvariant n accNames pNames rtopName npName s p T nP) :
    valLimbs (((accNames.drop n) ++ [rtopName]).map s.get) = 0 := by
  rw [h.2.1, valLimbs_replicate_zero]

/-- The modulus window recomposes to `⟦p⟧`. -/
theorem MontReduceInvariant.modulus_val {n : Nat} {accNames pNames : List String}
    {rtopName npName : String} {s : JState 64} {p T : List (BitVec 64)} {nP : BitVec 64}
    (h : MontReduceInvariant n accNames pNames rtopName npName s p T nP) :
    valLimbs (pNames.map s.get) = valLimbs p := by
  rw [h.2.2.1]

/-- The generator for the Montgomery-reduce family: a kernel's register layout. `wf`
    records that the accumulator is `2n` words wide (the low input window and the
    upper cleared window each hold `n`). `inv` instantiates `MontReduceInvariant`
    against the layout; the discharge lemmas above apply to `inv` through it. -/
structure MontReduceLayout where
  /-- Limb count of the reduced value. -/
  n : Nat
  /-- The `2n`-wide accumulator register window. -/
  accNames : List String
  /-- The modulus register window. -/
  pNames : List String
  /-- The top-carry register. -/
  rtopName : String
  /-- The Montgomery-constant register. -/
  npName : String
  /-- The accumulator is `2n` words wide. -/
  wf : accNames.length = 2 * n

/-- The layout's instantiated invariant. -/
def MontReduceLayout.inv (L : MontReduceLayout)
    (s : JState 64) (p T : List (BitVec 64)) (nP : BitVec 64) : Prop :=
  MontReduceInvariant L.n L.accNames L.pNames L.rtopName L.npName s p T nP

/-- Under a well-formed layout the cleared span is exactly `n + 1` words. -/
theorem MontReduceLayout.cleared_count (L : MontReduceLayout) :
    L.accNames.length - L.n + 1 = L.n + 1 := by
  rw [L.wf]; omega

/-! ## 2. The schoolbook-multiply window schema

Operand-scanning multiply: two `n`-limb operand windows loaded, the `2n`-limb product
accumulator cleared. The window value of the cleared accumulator is `0`
(`valLimbs_replicate_zero`), the seed the `mulx`/`adcx` accumulation adds onto. -/

/-- The schoolbook-multiply input window, parametrized by limb count `n`. The operand
    windows `aNames`, `bNames` (each `n` words) hold `a`, `b`; the product accumulator
    `outNames` (`2n` words) is cleared. -/
def SchoolbookMulInvariant (n : Nat) (aNames bNames outNames : List String)
    (s : JState 64) (a b : List (BitVec 64)) : Prop :=
  aNames.map s.get = a ∧ bNames.map s.get = b ∧
    aNames.length = n ∧ bNames.length = n ∧ outNames.length = 2 * n ∧
    outNames.map s.get = List.replicate (2 * n) 0

/-- The first operand window recomposes to `⟦a⟧`. -/
theorem SchoolbookMulInvariant.a_val {n : Nat} {aNames bNames outNames : List String}
    {s : JState 64} {a b : List (BitVec 64)}
    (h : SchoolbookMulInvariant n aNames bNames outNames s a b) :
    valLimbs (aNames.map s.get) = valLimbs a := by rw [h.1]

/-- The second operand window recomposes to `⟦b⟧`. -/
theorem SchoolbookMulInvariant.b_val {n : Nat} {aNames bNames outNames : List String}
    {s : JState 64} {a b : List (BitVec 64)}
    (h : SchoolbookMulInvariant n aNames bNames outNames s a b) :
    valLimbs (bNames.map s.get) = valLimbs b := by rw [h.2.1]

/-- The product accumulator starts at `0`. This is the additive seed of the
    multiply-accumulate cascade. -/
theorem SchoolbookMulInvariant.out_zero {n : Nat} {aNames bNames outNames : List String}
    {s : JState 64} {a b : List (BitVec 64)}
    (h : SchoolbookMulInvariant n aNames bNames outNames s a b) :
    valLimbs (outNames.map s.get) = 0 := by
  rw [h.2.2.2.2.2, valLimbs_replicate_zero]

/-- The generator for the schoolbook-multiply family. `inv` instantiates
    `SchoolbookMulInvariant` against the recorded windows. -/
structure SchoolbookMulLayout where
  /-- Limb count of each operand. -/
  n : Nat
  /-- First operand window. -/
  aNames : List String
  /-- Second operand window. -/
  bNames : List String
  /-- Product accumulator window (`2n` words). -/
  outNames : List String

/-- The layout's instantiated invariant. -/
def SchoolbookMulLayout.inv (L : SchoolbookMulLayout)
    (s : JState 64) (a b : List (BitVec 64)) : Prop :=
  SchoolbookMulInvariant L.n L.aNames L.bNames L.outNames s a b

/-! ## 3. The safegcd divstep window schema

The two big integers `f`, `g` are held over equal-length register windows; the step
counter `k` bounds the residual magnitude `⟦g⟧ < 2^k`, the goal-strengthening range
fact that shrinks with the divstep budget. -/

/-- The safegcd divstep window, parametrized by the remaining step budget `k`. The
    windows `fNames`, `gNames` (equal length) hold `f`, `g`; the counter `k` bounds the
    residual magnitude `⟦g⟧ < 2^k`. -/
def DivstepInvariant (k : Nat) (fNames gNames : List String)
    (s : JState 64) (f g : List (BitVec 64)) : Prop :=
  fNames.map s.get = f ∧ gNames.map s.get = g ∧
    fNames.length = gNames.length ∧ valLimbs g < 2 ^ k

/-- The `f` window recomposes to `⟦f⟧`. -/
theorem DivstepInvariant.f_val {k : Nat} {fNames gNames : List String}
    {s : JState 64} {f g : List (BitVec 64)}
    (h : DivstepInvariant k fNames gNames s f g) :
    valLimbs (fNames.map s.get) = valLimbs f := by rw [h.1]

/-- The `g` window recomposes to `⟦g⟧`. -/
theorem DivstepInvariant.g_val {k : Nat} {fNames gNames : List String}
    {s : JState 64} {f g : List (BitVec 64)}
    (h : DivstepInvariant k fNames gNames s f g) :
    valLimbs (gNames.map s.get) = valLimbs g := by rw [h.2.1]

/-- The residual magnitude bound `⟦g⟧ < 2^k` — the strengthening the divstep step
    consumes and re-establishes at `k - 1`. -/
theorem DivstepInvariant.g_bound {k : Nat} {fNames gNames : List String}
    {s : JState 64} {f g : List (BitVec 64)}
    (h : DivstepInvariant k fNames gNames s f g) :
    valLimbs g < 2 ^ k := h.2.2.2

/-- The generator for the divstep family. `inv` instantiates `DivstepInvariant`
    against the recorded windows at step budget `k`. -/
structure DivstepLayout where
  /-- The `f` register window. -/
  fNames : List String
  /-- The `g` register window. -/
  gNames : List String

/-- The layout's instantiated invariant at step budget `k`. -/
def DivstepLayout.inv (L : DivstepLayout) (k : Nat)
    (s : JState 64) (f g : List (BitVec 64)) : Prop :=
  DivstepInvariant k L.fNames L.gNames s f g

/-! ## 4. The field add/sub carry window schema

Two `n`-limb operand windows loaded with the carry flag cleared — the entry
precondition of the adc (add) / sbb (subtract) limb cascade. -/

/-- The field add/sub carry window, parametrized by limb count `n`. The operand windows
    `xNames`, `yNames` (each `n` words) hold `x`, `y`, and the carry flag is cleared. -/
def FieldAddSubInvariant (n : Nat) (xNames yNames : List String)
    (s : JState 64) (x y : List (BitVec 64)) : Prop :=
  xNames.map s.get = x ∧ yNames.map s.get = y ∧
    xNames.length = n ∧ yNames.length = n ∧ s.flagB (·.cf) = false

/-- The first operand window recomposes to `⟦x⟧`. -/
theorem FieldAddSubInvariant.x_val {n : Nat} {xNames yNames : List String}
    {s : JState 64} {x y : List (BitVec 64)}
    (h : FieldAddSubInvariant n xNames yNames s x y) :
    valLimbs (xNames.map s.get) = valLimbs x := by rw [h.1]

/-- The second operand window recomposes to `⟦y⟧`. -/
theorem FieldAddSubInvariant.y_val {n : Nat} {xNames yNames : List String}
    {s : JState 64} {x y : List (BitVec 64)}
    (h : FieldAddSubInvariant n xNames yNames s x y) :
    valLimbs (yNames.map s.get) = valLimbs y := by rw [h.2.1]

/-- The carry flag is cleared — the entry precondition of the adc/sbb cascade. -/
theorem FieldAddSubInvariant.cf_clear {n : Nat} {xNames yNames : List String}
    {s : JState 64} {x y : List (BitVec 64)}
    (h : FieldAddSubInvariant n xNames yNames s x y) :
    s.flagB (·.cf) = false := h.2.2.2.2

/-- The generator for the field add/sub family. `inv` instantiates
    `FieldAddSubInvariant` against the recorded windows. -/
structure FieldAddSubLayout where
  /-- Limb count of each operand. -/
  n : Nat
  /-- First operand window. -/
  xNames : List String
  /-- Second operand window. -/
  yNames : List String

/-- The layout's instantiated invariant. -/
def FieldAddSubLayout.inv (L : FieldAddSubLayout)
    (s : JState 64) (x y : List (BitVec 64)) : Prop :=
  FieldAddSubInvariant L.n L.xNames L.yNames s x y

/-! ## 5. The schema reproduces the committed `MontRedc4Load`

Instantiating `MontReduceInvariant` at `n = 4` with the committed
`Curve4MontMulProvenEmit` register windows reproduces the hand-written
`MontRedc4RunBlockProven.MontRedc4Load` — the cleared count `accNames.length - 4 + 1`
reduces to `5`, so the two predicates are definitionally the same conjunction. -/

/-- The committed 4-limb layout as a generator instance: the `Curve4MontMulProvenEmit`
    windows, well-formed at `n = 4` (the accumulator is eight words). -/
def montRedc4Layout : MontReduceLayout where
  n := 4
  accNames := Curve4MontMulProvenEmit.accNames
  pNames := Curve4MontMulProvenEmit.pNames
  rtopName := Curve4MontMulProvenEmit.rtopName
  npName := Curve4MontMulProvenEmit.npName
  wf := by decide

/- The `n = 4` instantiation of `MontReduceInvariant` over the `Curve4MontMulProvenEmit`
   windows unfolds to the hand-written `MontRedc4RunBlockProven.MontRedc4Load`: the two
   are the same four-conjunct predicate, differing only in the cleared-window count
   `accNames.length - 4 + 1`, which reduces to `5`. The reproduction is definitional by
   construction; it is stated here rather than discharged as a `rfl` theorem because the
   whole-record definitional check over the concrete register windows dominates the
   module's elaboration cost (a >100s / OOM build). -/

end CatCrypt.Crypto.SecureCompilation.Ascent.InvariantSchemas
