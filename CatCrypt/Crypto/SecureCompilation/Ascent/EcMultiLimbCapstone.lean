/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The multi-limb EC subtract capstone over the ascent `CorresJ` runBlock layer

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`)._

`RunBlockCorres.lean` supplies the flag-carrying forward simulation `CorresJ` over
the total machine fold `runBlock`, its structural core
(`corresJ_nil`/`corresJ_append`/`corresJ_weaken`/`corresJ_loop`), the single
subtract-with-borrow flag leaf `corresJ_sbb`, and the multi-limb value relation
`SRcarryLimbs` with its recomposition bridge `srcarryLimbs_recompose`.

This module assembles those pieces into a **multi-limb field-subtract capstone**.
It supplies the limb arithmetic the EC field-sub kernels need:

* `sbbLimbs`, the little-endian limbwise subtract-with-borrow, and its clean
  integer specification `sbbLimbs_spec` — the recomposed output value minus the
  top borrow weight equals the true multi-precision difference. This is the fact
  a whole `feSub` block is correct *about*, stated over `ℤ` with the borrow-out as
  an honest underflow bit.
* `sbbChain`/`corresJ_sbbChain`, an arbitrary-length chain of `sbb` instructions
  refining the composed abstract borrow fold through `corresJ_append` — the
  emit-block leg.
* `feSub4_capstone`, a concrete four-limb (`2^256`) field-subtract value capstone
  routed through `SRcarryLimbs`: from a machine state whose designated limb window
  recomposes to an abstract multi-precision value, the four-limb `sbbLimbs`
  computes exactly that value minus the subtrahend.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The residue of a subtract-with-borrow word

The single arithmetic fact under everything: `sub_borrow x y c` (defined as
`BitVec.ofInt 64 (x − y − c)`) reads back as the integer residue
`(x − y − c) % 2^64`. Extracted once so the borrow-chain lemmas can hand it to
`omega`. -/

/-- `sub_borrow x y c` recomposes to the non-negative integer residue
    `(x − y − c) % 2^64`. -/
theorem sub_borrow_toNat_residue (x y : BitVec 64) (c : Nat) :
    ((sub_borrow x y c).toNat : Int)
      = ((x.toNat : Int) - y.toNat - c) % ((2 ^ 64 : Nat) : Int) := by
  rw [sub_borrow, BitVec.toNat_ofInt, Int.toNat_of_nonneg]
  exact Int.emod_nonneg _ (by decide)

/-! ## The limbwise subtract-with-borrow and its integer specification -/

/-- The borrow-out of one subtract-with-borrow limb: the true signed difference
    `x − y − b` underflowed. -/
def sbbBorrow (x y : BitVec 64) (b : Bool) : Bool :=
  decide (((x.toNat : Int) - y.toNat - (if b then 1 else 0)) < 0)

/-- Little-endian limbwise subtract-with-borrow. Limb 0 is least significant; the
    borrow of limb `i` (`sbbBorrow`) feeds the borrow-in of limb `i+1`. Returns the
    limb list of the difference together with the final borrow-out. -/
def sbbLimbs : List (BitVec 64) → List (BitVec 64) → Bool → List (BitVec 64) × Bool
  | [], _, b => ([], b)
  | _ :: _, [], b => ([], b)
  | x :: xs, y :: ys, b =>
      (sub_borrow x y (if b then 1 else 0) :: (sbbLimbs xs ys (sbbBorrow x y b)).1,
       (sbbLimbs xs ys (sbbBorrow x y b)).2)

/-- **One-limb borrow identity.** The recomposed output word of a single
    subtract-with-borrow limb, minus its borrow-out weighted by `2^64`, equals the
    true integer difference `x − y − b`. The base cancellation the inductive step
    of `sbbLimbs_spec` reduces to. -/
theorem sub_borrow_carry_id (x y : BitVec 64) (b : Bool) :
    ((sub_borrow x y (if b then 1 else 0)).toNat : Int)
      - 2 ^ 64 * (if sbbBorrow x y b then (1 : Int) else 0)
      = (x.toNat : Int) - y.toNat - (if b then 1 else 0) := by
  have hres := sub_borrow_toNat_residue x y (if b then 1 else 0)
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hy : y.toNat < 2 ^ 64 := y.isLt
  have hcast : ((if b then (1 : Nat) else 0 : Nat) : Int) = (if b then (1 : Int) else 0) := by
    cases b <;> simp
  have hb1 : (if b then (1 : Int) else 0) ≤ 1 := by cases b <;> simp
  have hb0 : (0 : Int) ≤ (if b then (1 : Int) else 0) := by cases b <;> simp
  simp only [sbbBorrow, decide_eq_true_eq]
  rw [hcast] at hres
  omega

/-- **The multi-limb subtract-with-borrow specification** (the crux). For equal-length
    limb lists, the recomposed difference value minus the final borrow-out weighted by
    `2^(64·n)` equals the true multi-precision difference `⟦xs⟧ − ⟦ys⟧ − b`. Proved by
    induction: each step peels the low limb via `sub_borrow_carry_id` and folds the
    high limbs through the induction hypothesis. -/
theorem sbbLimbs_spec : ∀ (xs ys : List (BitVec 64)) (b : Bool), xs.length = ys.length →
    (limbVal (sbbLimbs xs ys b).1 : Int)
        - (2 : Int) ^ (64 * xs.length) * (if (sbbLimbs xs ys b).2 then (1 : Int) else 0)
      = (limbVal xs : Int) - limbVal ys - (if b then 1 else 0) := by
  intro xs
  induction xs with
  | nil =>
    intro ys b h
    cases ys with
    | nil => cases b <;> rfl
    | cons y ys' => simp at h
  | cons x xs' ih =>
    intro ys b h
    cases ys with
    | nil => simp at h
    | cons y ys' =>
      have h' : xs'.length = ys'.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using h
      have hih := ih ys' (sbbBorrow x y b) h'
      rw [sbbLimbs]
      set rec := sbbLimbs xs' ys' (sbbBorrow x y b) with hrec
      simp only [limbVal, List.length_cons]
      have hpow : (2 : Int) ^ (64 * (xs'.length + 1))
          = (2 : Int) ^ (64 * xs'.length) * 2 ^ 64 := by
        rw [Nat.mul_succ, pow_add]
      rw [hpow]
      push_cast
      have hid := sub_borrow_carry_id x y b
      linear_combination (2 : Int) ^ 64 * hih + hid

/-! ## The `sbb`-chain emit block and its `CorresJ` refinement -/

/-- The concrete emit block for a limb chain: one `sbb dst src` per `(dst, src)`
    register pair, in order (limb 0 first). -/
def sbbBlock : List (String × String) → List (JInstr 64)
  | [] => []
  | (d, s) :: ps => .sbb d (.reg s) :: sbbBlock ps

/-- The abstract borrow fold matching `sbbBlock`'s execution order: `sbbStep` per
    pair, limb 0 applied innermost. -/
def sbbAbs : List (String × String) → ACarry → ACarry
  | [], a => a
  | (d, s) :: ps, a => sbbAbs ps (sbbStep d s a)

/-- **The `sbb`-chain refinement.** An arbitrary-length chain of `sbb` instructions
    refines the composed abstract borrow fold `sbbAbs` through the carry-tracking
    relation `SRcarry`: the concrete `CF` written by each limb is exactly the `CF`
    the next limb reads. Assembled from `corresJ_sbb` through `corresJ_append` by
    induction on the pair list. -/
theorem corresJ_sbbChain (pairs : List (String × String)) :
    CorresJ SRcarry (fun _ => True) (sbbAbs pairs) (sbbBlock pairs) := by
  induction pairs with
  | nil => exact corresJ_weaken SRcarry (corresJ_nil SRcarry) (fun _ _ => trivial)
  | cons p ps ih =>
    obtain ⟨d, s⟩ := p
    show CorresJ SRcarry (fun _ => True) (fun a => sbbAbs ps (sbbStep d s a))
      ([.sbb d (.reg s)] ++ sbbBlock ps)
    exact corresJ_append SRcarry (corresJ_sbb d s) ih (fun _ _ => trivial)

/-! ## The concrete four-limb field-subtract value capstone

Routing the `2^256` (four-limb) instance of `sbbLimbs_spec` through the multi-limb
value relation `SRcarryLimbs`: from a machine state whose designated four-register
limb window recomposes to the abstract multi-precision value `a.val`, the four-limb
`sbbLimbs` on those abstract limbs computes exactly `a.val − ⟦ys⟧`, with the top
borrow accounting for underflow at `2^256`. -/

/-- **The four-limb field-subtract capstone.** From a `JState` whose limb window
    `[n0, n1, n2, n3]` recomposes (via `SRcarryLimbs`) to the abstract value `a.val`,
    the four-limb `sbbLimbs` on the abstract minuend limbs, corrected by its top
    borrow-out at weight `2^256`, equals `a.val` minus the recomposed subtrahend
    `[y0, y1, y2, y3]`. Combines `srcarryLimbs_recompose` (the value bridge) with the
    four-limb instance of `sbbLimbs_spec` (the borrow-chain correctness). -/
theorem feSub4_capstone (n0 n1 n2 n3 : String) (st : JState 64) (a : ACarryLimbs)
    (h : SRcarryLimbs [n0, n1, n2, n3] st a) (y0 y1 y2 y3 : BitVec 64) :
    (limbVal (sbbLimbs [a.regs n0, a.regs n1, a.regs n2, a.regs n3]
          [y0, y1, y2, y3] false).1 : Int)
        - (2 : Int) ^ (64 * 4)
          * (if (sbbLimbs [a.regs n0, a.regs n1, a.regs n2, a.regs n3]
              [y0, y1, y2, y3] false).2 then (1 : Int) else 0)
      = (a.val : Int) - limbVal [y0, y1, y2, y3] := by
  have hrec : limbVal [a.regs n0, a.regs n1, a.regs n2, a.regs n3] = a.val := by
    have hr := srcarryLimbs_recompose [n0, n1, n2, n3] st a h
    simpa using hr
  have hlen : ([a.regs n0, a.regs n1, a.regs n2, a.regs n3]).length = 4 := rfl
  have hspec := sbbLimbs_spec [a.regs n0, a.regs n1, a.regs n2, a.regs n3]
    [y0, y1, y2, y3] false rfl
  rw [hlen] at hspec
  rw [hrec] at hspec
  rw [hspec]
  simp

end CatCrypt.Crypto.SecureCompilation.Ascent
