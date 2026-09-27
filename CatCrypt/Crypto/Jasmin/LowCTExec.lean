/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCTSyntax

/-!
# `LowCT` big-step semantics

The runtime layer of `LowCT` (`CatCrypt.Crypto.Jasmin.LowCT` re-exports it):
the leaf oracles `LeafSpec`, the runtime state `RustState` with its update
lemmas, the tower-aware evaluators `SExpr.evalState` and `SExpr.evalStateBV`,
and the big-step relation `RustExec` with the `RFor` invariant rule.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

/-! ## §4  Runtime state -/

/-- Specification of a single leaf-function call.
    `f dt argTs oldDest args` = new value of dest after calling `f`. -/
def CallSpec :=
  String →
  ∀ (dt : TowerType) (argTs : List TowerType),
    RustVal dt → List (Σ t : TowerType, RustVal t) → RustVal dt

/-- Specification of a limb-store operation (abstract oracle analogous to
    Rocq's `asm_correct` for `Oasm` operators).

    `spec loc oldV idx v` = new tower value for `loc` after writing the u64
    word `v` into limb index `idx` of the previous value `oldV`. -/
def LimbStoreSpec :=
  ∀ (loc : Located), RustVal loc.locDst → Nat → BitVec 64 → RustVal loc.locDst

/-- **TupleLoad oracle.**  Specification
    of `RTupleLoad dst src idx`: reads the `idx`-th component of
    src and produces a new dst value carrying that component.  The
    dependent pair carries src's TowerType, for the heterogeneous
    binary-product case. -/
def TupleLoadSpec :=
  ∀ (dst : Located), RustVal dst.locDst →
    (Σ t : TowerType, RustVal t) → Nat → RustVal dst.locDst

/-- **Array-element store oracle.**
    Specification of `RArrStore arr idxVar src`: given the array
    slot's old value, a runtime index, and the source value (with
    its dependent tower type), returns the new array value with
    element `idx` overwritten.  Concrete instances slice the array
    at byte offset `idx * elemSize` and overwrite; abstract
    reasoning treats it as opaque. -/
def ArrStoreSpec :=
  ∀ (arr : Located), RustVal arr.locDst → Nat →
    (Σ t : TowerType, RustVal t) → RustVal arr.locDst

/-- **Array-element load oracle.**
    Reads element `idx` of `arr` into `dst`. -/
def ArrLoadSpec :=
  ∀ (dst : Located), RustVal dst.locDst →
    (Σ t : TowerType, RustVal t) → Nat → RustVal dst.locDst

/-- **Byte-offset arithmetic for tuple
    components.**  For `t = TTuple a b`:
    * Component 0 occupies bytes `[0, a.storageBytes)`.
    * Component 1 occupies bytes `[a.storageBytes, a.storageBytes + b.storageBytes)`.

    For larger nests `TTuple a (TTuple b c)`, the inner TTuple
    contributes its full `storageBytes` to the index-1 slot.

    Returns 0 for non-TTuple types or out-of-range indices. -/
def TowerType.tupleComponentByteOffset : TowerType → Nat → Nat
  | .TTuple _ _, 0     => 0
  | .TTuple a _, _     => a.storageBytes
  | _,           _     => 0

/-- Component byte width at index `idx`.  Returns 0 for non-TTuple
    types or out-of-range indices. -/
def TowerType.tupleComponentByteSize : TowerType → Nat → Nat
  | .TTuple a _, 0     => a.storageBytes
  | .TTuple _ b, _     => b.storageBytes
  | _,           _     => 0

/-- The component TowerType at index `idx`.  For `TTuple a b`,
    idx 0 → a, idx 1 → b.  Returns the original type for non-TTuple
    or out-of-range. -/
def TowerType.tupleComponentType : TowerType → Nat → TowerType
  | .TTuple a _, 0 => a
  | .TTuple _ b, _ => b
  | t,           _ => t

/-- **Bundled oracle record** (Rocq-style): leaf-call behaviour plus
    machine-instruction behaviour. Treating these as oracles mirrors Rocq
    `jasmin_translate.v`'s use of `handled_program` (for calls) and
    `asm_correct` (for `Oasm` operators).

    A `LeafSpec.mk call limbStore` literal is complete: every
    later field carries a `default`. -/
structure LeafSpec where
  call      : CallSpec
  limbStore : LimbStoreSpec
  /-- Tuple-load oracle.  Defaults to identity. -/
  tupleLoad  : TupleLoadSpec := fun _ oldV _ _ => oldV
  /-- Array-element store oracle.  Defaults to identity. -/
  arrStore   : ArrStoreSpec := fun _ oldV _ _ => oldV
  /-- Array-element load oracle.  Defaults to identity. -/
  arrLoad    : ArrLoadSpec := fun _ oldV _ _ => oldV

/-- Runtime state: a tower-variable heap and a scalar heap.  `rsScalar`'s `Nat`
    carrier is the MEMORY-SAFETY layer's convenience (frame reasoning is easier
    over `Nat`, and monus-vs-wrap is irrelevant to aliasing) — it is NOT the
    `u64` value semantics (see `SExpr.eval` / `SExpr.evalBV`). -/
structure RustState where
  rsTower  : String → Option (Σ t : TowerType, RustVal t)
  rsScalar : String → Nat   -- default 0

instance : Inhabited RustState where
  default := { rsTower := fun _ => none, rsScalar := fun _ => 0 }

/-- Set a tower variable. -/
def rsSetTower (rs : RustState) (x : String)
    (v : Σ t : TowerType, RustVal t) : RustState :=
  { rs with rsTower := fun y => if y == x then some v else rs.rsTower y }

/-- Set a scalar variable. -/
def rsSetScalar (rs : RustState) (x : String) (v : Nat) : RustState :=
  { rs with rsScalar := fun y => if y == x then v else rs.rsScalar y }

/-- Remove a tower variable (used after `RLetZero` body exits scope). -/
def rsRemoveTower (rs : RustState) (x : String) : RustState :=
  { rs with rsTower := fun y => if y == x then none else rs.rsTower y }

/-! ### Tower-limb read

The AUCurves `sexpr_ed` constructor `SLimb v i` reads limb `i` (a `u64`) of
the limb-bearing tower slot `v`.  On the CatCrypt side a tower value is a
byte array (`RustVal t = JArray t.storageBytes = Fin _ → BitVec 8`); limb `i`
is the little-endian `u64` stored at byte offset `i * 8`.  We read it with a
total helper (`towerLimb`) that defaults out-of-range bytes to `0`, matching
AUCurves' `None → 0` collapse when the limb-read sees a missing / short slot. -/

/-- Read the byte at Nat index `j` of a `RustVal t` byte array, defaulting to
    `0` when `j` is out of range.  Total (no `Fin` proof obligation). -/
def rustValByte {t : TowerType} (v : RustVal t) (j : Nat) : BitVec 8 :=
  if h : j < t.storageBytes then v ⟨j, h⟩ else 0

/-- Read limb `i` (a little-endian `u64`) of the tower value `v` as a `Nat`:
    the 8 bytes at offsets `i*8 .. i*8+7`, low byte first.  Out-of-range bytes
    read as `0`.  This is the CatCrypt image of AUCurves'
    `List.nth_error limbs i` masked through `mask64` — both yield the
    `u64`-bounded limb word (here in `[0, 2^64)` by construction). -/
def towerLimb {t : TowerType} (v : RustVal t) (i : Nat) : Nat :=
  let b : Nat → Nat := fun k => (rustValByte v (i * 8 + k)).toNat
  b 0 + b 1 * 2 ^ 8 + b 2 * 2 ^ 16 + b 3 * 2 ^ 24
    + b 4 * 2 ^ 32 + b 5 * 2 ^ 40 + b 6 * 2 ^ 48 + b 7 * 2 ^ 56

/-- Read limb `i` of the tower slot named `x` in `rs`, or `0` when the slot is
    absent.  Faithful image of AUCurves' `rs_get_tower_ed rs x` followed by
    the `List.nth_error limbs i` limb projection. -/
def rsTowerLimb (rs : RustState) (x : String) (i : Nat) : Nat :=
  match rs.rsTower x with
  | some ⟨_, v⟩ => towerLimb v i
  | none        => 0

/-- **Tower-aware `SExpr` evaluator.**  Sibling of the scalar-only
    `SExpr.eval`: it evaluates against the full `RustState`, so the new
    `SLimb v i` constructor reads limb `i` of tower slot `v` from `rs.rsTower`
    (via `rsTowerLimb`).  Every non-`SLimb` arm reads only `rs.rsScalar`,
    exactly as `SExpr.eval`; consequently `evalState rs e = eval rs.rsScalar e`
    on any `SLimb`-free expression (see `SExpr.evalState_eq_eval_of_limbFree`).

    This is the faithful image of AUCurves' `eval_sexpr_ed`: the field-op
    bodies (`fe25519_add_body`'s `SAdd (SLimb a i) (SLimb b i)`) evaluate
    through `evalState`, while the scalar-fragment runtime stores keep using
    `eval`.  Defined separately from `eval` precisely so `eval`'s signature
    stays `(String → Nat) → SExpr → Nat` for the modules that depend on it. -/
def SExpr.evalState (rs : RustState) : SExpr → Nat
  | .SVar x   => rs.rsScalar x
  | .SLit n   => n
  | .SAdd a b => a.evalState rs + b.evalState rs
  | .SSub a b => a.evalState rs - b.evalState rs
  | .SMul a b => a.evalState rs * b.evalState rs
  | .SShr a b => a.evalState rs >>> b.evalState rs
  | .SShl a b => a.evalState rs <<< b.evalState rs
  | .SAnd a b => a.evalState rs &&& b.evalState rs
  | .SXor a b => a.evalState rs ^^^ b.evalState rs
  | .SLt  a b => if a.evalState rs < b.evalState rs then 1 else 0
  | .SAsr a b =>
      sexprOfSignedInt64 (sexprToSignedInt64 (a.evalState rs) >>> (b.evalState rs : Nat))
  | .SMulS a b =>
      sexprOfSignedInt64 (sexprToSignedInt64 (a.evalState rs) * sexprToSignedInt64 (b.evalState rs))
  | .SMulHiU a b => sexprMulHiU (a.evalState rs) (b.evalState rs)
  | .SMulHiS a b => sexprMulHiS (a.evalState rs) (b.evalState rs)
  -- The point of the tower-aware evaluator: read the limb from the heap.
  | .SLimb v i => rsTowerLimb rs v i

/-- `e` contains no `SLimb` node anywhere (so its value does not depend on the
    tower heap).  The whole-expression analogue of "scalar-only `SExpr`". -/
def SExpr.limbFree : SExpr → Prop
  | .SVar _   => True
  | .SLit _   => True
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b
  | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b | .SMulHiS a b =>
      a.limbFree ∧ b.limbFree
  | .SLimb _ _ => False

/-- On a `limbFree` expression, the tower-aware evaluator agrees with the
    scalar `eval` against `rs.rsScalar`: the two evaluators differ ONLY on the
    `SLimb` arm, and every other arm reads `rsScalar` identically.  This is the
    formal sense in which `evalState` *extends* (rather than replaces) `eval`. -/
theorem SExpr.evalState_eq_eval (rs : RustState) :
    ∀ e : SExpr, e.limbFree → e.evalState rs = e.eval rs.rsScalar := by
  intro e
  induction e with
  | SVar x => intro _; rfl
  | SLit n => intro _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SShr a b iha ihb
  | SShl a b iha ihb | SAnd a b iha ihb | SXor a b iha ihb | SLt a b iha ihb
  | SAsr a b iha ihb | SMulS a b iha ihb | SMulHiU a b iha ihb | SMulHiS a b iha ihb =>
      intro h
      simp only [SExpr.evalState, SExpr.eval, iha h.1, ihb h.2]
  | SLimb v i => intro h; exact absurd h (by simp [SExpr.limbFree])

/-! ### Tower-aware wrapping-`u64` reconciliation (runtime layer)

The scalar bridge of `LowCTSExpr` (`SExpr.evalBV` / `inRange` / `evalBV_eq_ofNat_eval`)
reconciles the Nat-model **scalar** `SExpr.eval` with the wrapping-`u64`
hardware.  But the runtime relation `RustExec` (below) stores a runtime
`SExpr` via the **tower-aware** `SExpr.evalState` — `RustExec.limbStoreExpr`
writes `BitVec.ofNat 64 (e.evalState rs)`, i.e. the *unbounded-Nat*
`evalState` truncated **only at the final store**.  The jasmin / x86 target,
by contrast, wraps mod `2^64` at **every intermediate** node, *and* an
`SSub` that underflows **wraps** there (whereas `evalState`, over `Nat`,
**saturates at 0**).  So the runtime store value can disagree with the
hardware exactly when an intermediate overflows or an `SSub` underflows.

`SExpr.evalStateBV` is the tower-aware, intermediate-wrapping evaluator: the
faithful image of what the emitted code computes.  The `SLimb v i` arm reads
the same limb as `evalState` but already in `BitVec 64` form — `towerLimb`
returns a value `< 2^64` by construction (`towerLimb_lt`), so the limb read
needs no truncation.  `inRangeState` is the tower-aware side-condition under
which the saturating-then-truncate store coincides with the
intermediate-wrapping hardware; `evalStateBV_eq_ofNat_evalState` is the
bridge (the runtime-layer reconciliation): the value `RustExec`
records is provably the hardware value precisely on `inRangeState` inputs. -/

/-- `towerLimb` is a little-endian assembly of 8 bytes, so it is `< 2^64` by
    construction — the limb read is always representable in `u64`. -/
theorem towerLimb_lt {t : TowerType} (v : RustVal t) (i : Nat) :
    towerLimb v i < 2 ^ 64 := by
  unfold towerLimb
  have hb : ∀ k, (rustValByte v (i * 8 + k)).toNat < 2 ^ 8 := fun k =>
    (rustValByte v (i * 8 + k)).isLt
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  simp only at *
  omega

/-- `rsTowerLimb` is `< 2^64`: it is either a `towerLimb` (bounded above) or
    the default `0`. -/
theorem rsTowerLimb_lt (rs : RustState) (x : String) (i : Nat) :
    rsTowerLimb rs x i < 2 ^ 64 := by
  unfold rsTowerLimb
  match h : rs.rsTower x with
  | some ⟨_, v⟩ => exact towerLimb_lt v i
  | none => positivity

/-- **Tower-aware wrapping-`u64` evaluator (runtime layer).**  The
    intermediate-wrapping sibling of `SExpr.evalState`: every arithmetic node
    truncates to `BitVec 64` immediately, mirroring the hardware.  The
    `SLimb v i` arm reads the same `u64` limb as `evalState` (already
    `< 2^64`), so it needs only `BitVec.ofNat` packaging.  This is the
    runtime-state analogue of `SExpr.evalBV`. -/
def SExpr.evalStateBV (rs : RustState) : SExpr → BitVec 64
  | .SVar x   => BitVec.ofNat 64 (rs.rsScalar x)
  | .SLit n   => BitVec.ofNat 64 n
  | .SAdd a b => a.evalStateBV rs + b.evalStateBV rs
  | .SSub a b => a.evalStateBV rs - b.evalStateBV rs
  | .SMul a b => a.evalStateBV rs * b.evalStateBV rs
  | .SShr a b => (a.evalStateBV rs) >>> (b.evalStateBV rs).toNat
  | .SShl a b => (a.evalStateBV rs) <<< (b.evalStateBV rs).toNat
  | .SAnd a b => a.evalStateBV rs &&& b.evalStateBV rs
  | .SXor a b => a.evalStateBV rs ^^^ b.evalStateBV rs
  | .SLt  a b => if (a.evalStateBV rs).toNat < (b.evalStateBV rs).toNat then 1 else 0
  | .SAsr a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64 (sexprToSignedInt64 (a.evalStateBV rs).toNat >>> ((b.evalStateBV rs).toNat : Nat)))
  | .SMulS a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64 (sexprToSignedInt64 (a.evalStateBV rs).toNat * sexprToSignedInt64 (b.evalStateBV rs).toNat))
  | .SMulHiU a b => BitVec.ofNat 64 (sexprMulHiU (a.evalStateBV rs).toNat (b.evalStateBV rs).toNat)
  | .SMulHiS a b => BitVec.ofNat 64 (sexprMulHiS (a.evalStateBV rs).toNat (b.evalStateBV rs).toNat)
  | .SLimb v i => BitVec.ofNat 64 (rsTowerLimb rs v i)

/-- Tower-aware in-range side-condition (runtime layer): the counterpart of
    `SExpr.inRange` for `evalState`.  Under it, the saturating-then-truncate
    runtime store equals the intermediate-wrapping hardware value.  The
    `SLimb` arm needs no condition — the limb read is always `< 2^64`. -/
def SExpr.inRangeState (rs : RustState) : SExpr → Prop
  | .SVar x   => rs.rsScalar x < 2 ^ 64
  | .SLit n   => n < 2 ^ 64
  | .SAdd a b => a.inRangeState rs ∧ b.inRangeState rs ∧ a.evalState rs + b.evalState rs < 2 ^ 64
  | .SSub a b => a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs ≤ a.evalState rs
  | .SMul a b => a.inRangeState rs ∧ b.inRangeState rs ∧ a.evalState rs * b.evalState rs < 2 ^ 64
  | .SShr a b => a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs < 64
  | .SShl a b => a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs < 64 ∧ a.evalState rs <<< b.evalState rs < 2 ^ 64
  | .SAnd a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SXor a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SLt  a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SAsr a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SMulS a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SMulHiU a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SMulHiS a b => a.inRangeState rs ∧ b.inRangeState rs
  | .SLimb _ _ => True

/-- Under `inRangeState`, the tower-aware Nat value is `< 2^64`: no overflow
    occurs (tower-aware analogue of `eval_lt_of_inRange`). -/
theorem SExpr.evalState_lt_of_inRangeState (rs : RustState) :
    ∀ e : SExpr, e.inRangeState rs → e.evalState rs < 2 ^ 64 := by
  intro e
  induction e with
  | SVar x => intro h; exact h
  | SLit n => intro h; exact h
  | SAdd a b _ _ => intro h; exact h.2.2
  | SSub a b iha _ => intro h; exact lt_of_le_of_lt (Nat.sub_le _ _) (iha h.1)
  | SMul a b _ _ => intro h; exact h.2.2
  | SShr a b iha _ =>
      intro h; exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (iha h.1)
  | SShl a b _ _ => intro h; exact h.2.2.2
  | SAnd a b iha _ => intro h; exact lt_of_le_of_lt Nat.and_le_left (iha h.1)
  | SXor a b iha ihb =>
      intro h
      exact Nat.xor_lt_two_pow (n := 64) (iha h.1) (ihb h.2)
  | SLt a b _ _ => intro _; simp only [SExpr.evalState]; split <;> norm_num
  | SAsr a b _ _ => intro _; exact sexprOfSignedInt64_lt _
  | SMulS a b _ _ => intro _; exact sexprOfSignedInt64_lt _
  | SMulHiU a b _ _ => intro _; exact sexprMulHiU_lt _ _
  | SMulHiS a b _ _ => intro _; exact sexprMulHiS_lt _ _
  | SLimb v i => intro _; exact rsTowerLimb_lt rs v i

/-- **Tower-aware wrapping ⇔ Nat-model bridge (runtime layer, `.toNat`
    form).**  Under `inRangeState`, the `Nat` read back out of the
    intermediate-wrapping evaluator equals the tower-aware Nat-model value: no
    wrap occurs, so `SExpr.evalState` faithfully predicts the hardware. -/
theorem SExpr.toNat_evalStateBV_of_inRangeState (rs : RustState) :
    ∀ e : SExpr, e.inRangeState rs →
      (e.evalStateBV rs).toNat = e.evalState rs := by
  intro e
  induction e with
  | SVar x =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h
  | SLit n =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h
  | SAdd a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_add, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2
  | SSub a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_sub, iha h.1, ihb h.2.1]
      have hba : evalState rs b ≤ evalState rs a := h.2.2
      have hlt : evalState rs a < 2 ^ 64 := SExpr.evalState_lt_of_inRangeState rs a h.1
      have heq : 2 ^ 64 - evalState rs b + evalState rs a
          = 2 ^ 64 + (evalState rs a - evalState rs b) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  | SMul a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_mul, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2
  | SShr a b iha ihb =>
      intro h
      rw [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ushiftRight, iha h.1, ihb h.2.1]
  | SShl a b iha ihb =>
      intro h
      rw [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_shiftLeft, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2.2
  | SAnd a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_and, iha h.1, ihb h.2]
  | SXor a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_xor, iha h.1, ihb h.2]
  | SLt a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, iha h.1, ihb h.2]
      split <;> simp
  | SAsr a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprOfSignedInt64_lt _)
  | SMulS a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprOfSignedInt64_lt _)
  | SMulHiU a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprMulHiU_lt _ _)
  | SMulHiS a b iha ihb =>
      intro h
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprMulHiS_lt _ _)
  | SLimb v i =>
      intro _
      simp only [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (rsTowerLimb_lt rs v i)

/-- **Tower-aware wrapping ⇔ Nat-model bridge (runtime layer, `BitVec`
    form).**  On `inRangeState` inputs the intermediate-wrapping evaluator *is*
    the truncation of the tower-aware Nat model.  `RustExec.limbStoreExpr`
    records `BitVec.ofNat 64 (e.evalState rs)`, so on `inRangeState` the runtime
    relation agrees with the hardware exactly. -/
theorem SExpr.evalStateBV_eq_ofNat_evalState (rs : RustState) (e : SExpr)
    (h : e.inRangeState rs) :
    e.evalStateBV rs = BitVec.ofNat 64 (e.evalState rs) := by
  apply BitVec.eq_of_toNat_eq
  rw [SExpr.toNat_evalStateBV_of_inRangeState rs e h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (SExpr.evalState_lt_of_inRangeState rs e h)]

/-- Look up a tower variable, checking the stored type matches `loc.locDst`. -/
def locatedLookup (rs : RustState) (loc : Located) :
    Option (RustVal loc.locDst) :=
  match rs.rsTower loc.locVar with
  | some ⟨t, v⟩ => if h : t = loc.locDst then some (h ▸ v) else none
  | none         => none

/-- Write a new value to the destination of `loc`. -/
def locatedUpdate (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) : RustState :=
  rsSetTower rs loc.locVar ⟨loc.locDst, v⟩

/-! ## §5  Key state-update lemmas -/

theorem rsSetTower_same (rs : RustState) (x : String) (v : Σ t, RustVal t) :
    (rsSetTower rs x v).rsTower x = some v := by
  simp [rsSetTower]

theorem rsSetTower_other (rs : RustState) (x y : String)
    (v : Σ t, RustVal t) (h : x ≠ y) :
    (rsSetTower rs x v).rsTower y = rs.rsTower y := by
  unfold rsSetTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

theorem rsRemoveTower_other (rs : RustState) (x y : String) (h : x ≠ y) :
    (rsRemoveTower rs x).rsTower y = rs.rsTower y := by
  unfold rsRemoveTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Setting one tower var leaves a different located's lookup unchanged. -/
theorem locatedLookup_rsSetTower_other (rs : RustState) (x : String)
    (v : Σ t, RustVal t) (loc : Located) (h : x ≠ loc.locVar) :
    locatedLookup (rsSetTower rs x v) loc = locatedLookup rs loc := by
  unfold locatedLookup rsSetTower; simp only []
  have : (loc.locVar == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Removing one tower var leaves a different located's lookup unchanged. -/
theorem locatedLookup_rsRemoveTower_other (rs : RustState) (x : String)
    (loc : Located) (h : x ≠ loc.locVar) :
    locatedLookup (rsRemoveTower rs x) loc = locatedLookup rs loc := by
  unfold locatedLookup rsRemoveTower; simp only []
  have : (loc.locVar == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Setting scalar leaves tower lookups unchanged. -/
theorem locatedLookup_rsSetScalar (rs : RustState) (x : String) (v : Nat)
    (loc : Located) :
    locatedLookup (rsSetScalar rs x v) loc = locatedLookup rs loc := by
  unfold locatedLookup rsSetScalar; simp only []

/-- `locatedUpdate` writes to the correct variable. -/
theorem locatedUpdate_dest (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) :
    (locatedUpdate rs loc v).rsTower loc.locVar = some ⟨loc.locDst, v⟩ := by
  unfold locatedUpdate rsSetTower
  simp

/-- `locatedUpdate` leaves other variables unchanged. -/
theorem locatedUpdate_other (rs : RustState) (loc1 loc2 : Located)
    (v : RustVal loc1.locDst)
    (h : loc1.locVar ≠ loc2.locVar) :
    locatedLookup (locatedUpdate rs loc1 v) loc2 = locatedLookup rs loc2 := by
  apply locatedLookup_rsSetTower_other
  exact h

/-! ## §6  Big-step semantics -/

/-- Leaf name for output `i` of the multi-output call to `f`.

    An `Expr` in the `Com` framework has exactly one return type, so a
    multi-output call is carried as one single-output call per output, named
    apart by its index. `RCallN f dests args` therefore reads output `i`
    through the ordinary `LeafSpec.call` oracle at `callNLeafName f i`, and a
    leaf supplying an `n`-output primitive registers `n` names. This is the
    same monomorphisation `Optimizer.SplitBytesSlice` performs on the
    size-varying `bytes_slice` wrapper. -/
def callNLeafName (f : String) (i : Nat) : String :=
  "callN:" ++ f ++ "#" ++ toString i

/-- Write each destination of an N-output call, left to right: destination `i`
    receives output `i` of `f` on the argument values `argList`.

    `argList` and `argTs` are read once from the pre-state by the `callN` rule,
    so every destination sees the same inputs — the borrow checker keeps
    `dests` distinct and disjoint from `args`, so no destination write can
    reach a later destination's arguments. -/
def callNUpdate (leafSpec : LeafSpec) (f : String) (argTs : List TowerType)
    (argList : List (Σ t : TowerType, RustVal t)) :
    Nat → List Located → RustState → RustState
  | _, [], rs => rs
  | i, d :: rest, rs =>
      callNUpdate leafSpec f argTs argList (i + 1) rest
        (locatedUpdate rs d
          (leafSpec.call (callNLeafName f i) d.locDst argTs
            ((locatedLookup rs d).getD default) argList))

/-- A slot whose name is none of the destinations is untouched by the fold:
    the write-set of `RCallN f dests args` is exactly `dests`. -/
theorem locatedLookup_callNUpdate_other (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState) (loc : Located),
      loc.locVar ∉ dests.map (·.locVar) →
      locatedLookup (callNUpdate leafSpec f argTs argList i dests rs) loc
        = locatedLookup rs loc := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _; rfl
  | cons d rest ih =>
    intro i rs loc hNotIn
    simp only [List.map_cons, List.mem_cons, not_or] at hNotIn
    obtain ⟨hd, hrest⟩ := hNotIn
    show locatedLookup
      (callNUpdate leafSpec f argTs argList (i + 1) rest (locatedUpdate rs d _)) loc = _
    rw [ih (i + 1) _ loc (by simpa using hrest)]
    exact locatedUpdate_other _ _ _ _ (Ne.symm hd)

/-- The `rsTower`-level counterpart of `locatedLookup_callNUpdate_other`.
    `locatedLookup` equality does not imply `rsTower` equality — it forgets a
    type mismatch — so a frame stated at the raw heap needs this one. -/
theorem rsTower_callNUpdate_other (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState) (y : String),
      y ∉ dests.map (·.locVar) →
      (callNUpdate leafSpec f argTs argList i dests rs).rsTower y = rs.rsTower y := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _; rfl
  | cons d rest ih =>
    intro i rs y hNotIn
    simp only [List.map_cons, List.mem_cons, not_or] at hNotIn
    obtain ⟨hd, hrest⟩ := hNotIn
    show (callNUpdate leafSpec f argTs argList (i + 1) rest
            (locatedUpdate rs d _)).rsTower y = _
    rw [ih (i + 1) _ y (by simpa using hrest)]
    unfold locatedUpdate
    exact rsSetTower_other _ _ _ _ (Ne.symm hd)

/-- The fold writes tower slots only, so the scalar heap is untouched. -/
theorem callNUpdate_rsScalar (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState),
      (callNUpdate leafSpec f argTs argList i dests rs).rsScalar = rs.rsScalar := by
  intro dests
  induction dests with
  | nil => intro _ _; rfl
  | cons d rest ih =>
    intro i rs
    show (callNUpdate leafSpec f argTs argList (i + 1) rest (locatedUpdate rs d _)).rsScalar = _
    rw [ih (i + 1)]
    rfl

/-- The `j`-th destination reads back its own write: after the fold started at
    index `i`, the slot named by `dests[j]` holds output `i + j` of `f`, applied
    to the pre-state's old value at that slot.

    Distinctness of the destination *names* is what makes this hold — with a
    repeated name the later write shadows the earlier one, and the slot carries
    only the last output written to it. -/
theorem rsTower_callNUpdate_nth (leafSpec : LeafSpec) (f : String)
    (argTs : List TowerType) (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ (dests : List Located) (i j : Nat) (rs : RustState) (d : Located),
      (dests.map (·.locVar)).Nodup →
      dests[j]? = some d →
      (callNUpdate leafSpec f argTs argList i dests rs).rsTower d.locVar
        = some ⟨d.locDst,
            leafSpec.call (callNLeafName f (i + j)) d.locDst argTs
              ((locatedLookup rs d).getD default) argList⟩ := by
  intro dests
  induction dests with
  | nil => intro _ _ _ _ _ hj; simp at hj
  | cons d' rest ih =>
    intro i j rs d hNodup hj
    simp only [List.map_cons, List.nodup_cons] at hNodup
    obtain ⟨hHead, hRest⟩ := hNodup
    cases j with
    | zero =>
      have hd : d = d' := by simpa using hj.symm
      subst hd
      show (callNUpdate leafSpec f argTs argList (i + 1) rest
              (locatedUpdate rs d _)).rsTower d.locVar = _
      rw [rsTower_callNUpdate_other leafSpec f argTs argList rest (i + 1) _
            d.locVar hHead, locatedUpdate_dest]
      simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at hj
      have hmem : d ∈ rest := List.mem_of_getElem? hj
      have hne : d'.locVar ≠ d.locVar := by
        intro hEq
        exact hHead (hEq ▸ List.mem_map_of_mem hmem)
      show (callNUpdate leafSpec f argTs argList (i + 1) rest
              (locatedUpdate rs d' _)).rsTower d.locVar = _
      rw [ih (i + 1) k _ d hRest hj, locatedUpdate_other _ _ _ _ hne]
      have hidx : i + 1 + k = i + (k + 1) := by omega
      rw [hidx]

/-- Big-step execution relation for `LowCT`.

    `RustExec N leafSpec c rs rs'` means: running `c` from state `rs`
    with fuel bound `N` and leaf specification `leafSpec` terminates in `rs'`.

    `N` bounds `RWhileNz` loop iterations (via the `while_true` case's
    induction structure — the bound appears implicitly in the finite derivation
    tree).

    `RFnCall` and `RFnDef` have no rule. Giving `RFnCall` its meaning
    requires a function environment — a map from name to `FnSpec`, threaded
    through this relation's indices, so the rule can run the callee's body
    on the argument slots and write back to `dests`. This relation is
    indexed only by `N` and `leafSpec`, so that is a change to its type.
    Until then the relation is unsatisfiable at those two nodes: a
    hypothesis `RustExec … c rs rs'` for a program containing one cannot be
    discharged, rather than being discharged by a rule that moves no state.
    `toJasminCmd` still lowers `RFnCall` to a `Ccall`, so such a program
    compiles; what it does not have is an operational claim at this
    layer. `TranslateDialectFnCall`'s `fnCallD`/`fnDefD` are the dialect-side
    shape a future rule would mirror.

    Scalar semantics. `scalarSetExpr`, `limbStoreExpr` and the `forRuntime` trip
    count evaluate by `SExpr.evalState`, over unbounded naturals with saturating
    `SSub`; guards test `rsScalar x ≠ 0` on naturals. `RustExec` is therefore the
    referent for Rust `saturating_sub`, counters, indices and values that stay
    below `2^64`, and not for wrapping kernels, whose referent is `semScalar`
    (`SExpr.evalBV`). Wrapping operations routed as leaf calls (`wrapping_*#w`,
    `rotate_*#w`, `cast#w`) wrap in the leaf oracle and are unaffected.

    Bridges from `RustExec` to `semScalar` and their in-range hypotheses:
    `RustExec_limbStoreExpr_stored_eq_evalStateBV` (`inRangeState`);
    `RustExecSemScalarBridge.rustExec_semScalar_agree` and
    `rustExec_semScalar_agree_arr` (`IsCoveredAdeqS`: `srcClean` and
    `∀ σ, (∀ y, σ y < 2^64) → e.inRange σ` at every `RScalarSetExpr`, together
    with `ScalarInRange` at entry); `GuardedAgree.rustExec_semScalarGuarded_agree`
    (the per-run `InRangeG`); `RustExecSimulatesUnified.rustExec_semU_agree`
    (`IsCoveredAdeqU`). -/
inductive RustExec (N : Nat) (leafSpec : LeafSpec) :
    LowCT → RustState → RustState → Prop where
  | skip   : ∀ rs, RustExec N leafSpec .RSkip rs rs
  | seq    : ∀ c1 c2 rs r1 rs',
      RustExec N leafSpec c1 rs r1 →
      RustExec N leafSpec c2 r1 rs' →
      RustExec N leafSpec (.RSeq c1 c2) rs rs'
  | letZero : ∀ x t body rs rs',
      RustExec N leafSpec body (rsSetTower rs x ⟨t, default⟩) rs' →
      RustExec N leafSpec (.RLetZero x t body) rs rs'
  | letU64Zero : ∀ x body rs rs',
      RustExec N leafSpec body (rsSetScalar rs x 0) rs' →
      RustExec N leafSpec (.RLetU64Zero x body) rs rs'
  | scalarSet : ∀ x v rs,
      RustExec N leafSpec (.RScalarSet x v) rs (rsSetScalar rs x v)
  | ifTrue  : ∀ e ct cf rs rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec ct rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | ifFalse : ∀ e ct cf rs rs',
      rs.rsScalar e = 0 →
      RustExec N leafSpec cf rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | whileFalse : ∀ e body rs,
      rs.rsScalar e = 0 →
      RustExec N leafSpec (.RWhileNz e body) rs rs
  | whileTrue : ∀ e body rs r1 rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec body rs r1 →
      RustExec N leafSpec (.RWhileNz e body) r1 rs' →
      RustExec N leafSpec (.RWhileNz e body) rs rs'
  /-- `RFor x 0 body` is a no-op. -/
  | forZero : ∀ x body rs,
      RustExec N leafSpec (.RFor x 0 body) rs rs
  /-- `RFor x (n+1) body` runs `RFor x n body` (iterations 0..n-1), then
      sets the scalar `x` to `n` and runs `body` once more. -/
  | forSucc : ∀ x n body rs r1 rs',
      RustExec N leafSpec (.RFor x n body) rs r1 →
      RustExec N leafSpec body (rsSetScalar r1 x n) rs' →
      RustExec N leafSpec (.RFor x (n+1) body) rs rs'
  /-- Runtime-bound for-loop: delegate to `RFor` at the trip count obtained by
      evaluating `bound` in the entry state `rs`. -/
  | forRuntime : ∀ x bound body rs rs',
      RustExec N leafSpec (.RFor x (bound.evalState rs) body) rs rs' →
      RustExec N leafSpec (.RForRuntime x bound body) rs rs'
  | call : ∀ f dest args rs oldDestV argList,
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      -- Per-arg type-recovery (Option A): args[i].locDst matches the
      -- stored Sigma type at args[i].locVar. Required for determinism.
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExec N leafSpec (.RCall f dest args) rs
        (locatedUpdate rs dest
          (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  /-- The clone binding stays in the tower on exit, matching Jasmin, where a
      call introduces no scope to leave.  The AUCurves rule this is imported
      from drops it (`XR_clone_call` ends in `remove_var`), so on this
      constructor the relation is not a conservative extension of that one:
      a post-state here binds `cloneVar`, and there it does not. -/
  | cloneCall : ∀ cloneVar cloneTy oldDest innerF dest args
                   rs rsClone rs',
      rsClone = rsSetTower rs cloneVar
                  (rs.rsTower oldDest.locVar |>.getD ⟨cloneTy, default⟩) →
      RustExec N leafSpec (.RCall innerF dest args) rsClone rs' →
      RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
        rs rs'
  /-- 2-output cswap-shape leaf.  Semantically: two sequential 1-out
      calls in Jasmin: `f(dest1, args); f(dest2, args)`.  borrowOk for
      `RCallSwap` forbids `dest1 = dest2` and either dest in args. -/
  | callSwap : ∀ f dest1 dest2 args rs rs1 rs',
      RustExec N leafSpec (.RCall f dest1 args) rs rs1 →
      RustExec N leafSpec (.RCall f dest2 args) rs1 rs' →
      RustExec N leafSpec (.RCallSwap f dest1 dest2 args) rs rs'
  | limbStore : ∀ loc idx v rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExec N leafSpec (.RLimbStore loc idx v) rs
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  /-- **Runtime-valued limb store (tower-aware).**
      Evaluates `e` against the current *full* state via
      `SExpr.evalState`, truncates the resulting `Nat` to a `BitVec 64`,
      and writes it into limb `idx` of `loc` via the same
      `leafSpec.limbStore` oracle as `limbStore`.

      `evalState` reads the **tower heap** (by byte offset `j*8`, per
      `rsTowerLimb`/`towerLimb`) for any `SLimb v j` node, so an
      `SLimb`-valued store carries its runtime effect: the two
      Fp2 / tower halves share one slot rather than reading as
      independent ones.  On `SLimb`-free expressions `evalState rs e = eval
      rs.rsScalar e` (see `SExpr.evalState_eq_eval`), so the
      scalar-fragment stores are unchanged (see
      `SExpr.evalState_eq_eval`); the literal-valued
      `RLimbStore loc idx v` still coincides with
      `RLimbStoreExpr loc idx (.SLit v.toNat)`. -/
  | limbStoreExpr : ∀ loc idx e rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExec N leafSpec (.RLimbStoreExpr loc idx e) rs
        (locatedUpdate rs loc
          (leafSpec.limbStore loc oldDestV idx (BitVec.ofNat 64 (e.evalState rs))))
  /-- **N-output leaf call.**  Reads the argument values
      from the pre-state, then writes each destination in turn: destination
      `i` receives `leafSpec.call (callNLeafName f i)` on those arguments.
      Naming the outputs apart by index is what distinguishes destinations of
      the same tower type — the `(carry, sum)` of an add-with-carry shape are
      both `TU64`, and a single leaf name would give them one value. -/
  | callN : ∀ f dests args rs argList,
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      (∀ d ∈ dests, ∃ v, rs.rsTower d.locVar = some ⟨d.locDst, v⟩) →
      RustExec N leafSpec (.RCallN f dests args) rs
        (callNUpdate leafSpec f (args.map (·.locDst)) argList 0 dests rs)
  /-- **CT-safe conditional move.**  Reads the
      scalar `sel`; if zero, copies `src0`'s tower value into `dst`;
      else copies `src1`.  Hardware analogue: a `CMOV` chain at the
      asm level.  Both source values are read regardless of `sel`'s
      value — that's what makes this CT-safe.

      The type side conditions `src0.locDst = dst.locDst` and
      `src1.locDst = dst.locDst` reflect the borrow-checker invariant
      that cmov requires same-typed source / dest slots. -/
  | selectFalse : ∀ dst sel src0 src1 rs (h : src0.locDst = dst.locDst) srcV,
      rs.rsScalar sel = 0 →
      locatedLookup rs src0 = some srcV →
      RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV))
  | selectTrue : ∀ dst sel src0 src1 rs (h : src1.locDst = dst.locDst) v srcV,
      rs.rsScalar sel = v → v ≠ 0 →
      locatedLookup rs src1 = some srcV →
      RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV))
  /-- **Zero-cost contract.**  No state change. -/
  | assert : ∀ label rs,
      RustExec N leafSpec (.RAssert label) rs rs
  /-- **Scoped block.**  Identical to running
      the body; the "scope" boundary is meaningful only at the
      lowering level (stack reuse) and the Hoare level
      (locally-bound vars dropped from the post-context). -/
  | block : ∀ body rs rs',
      RustExec N leafSpec body rs rs' →
      RustExec N leafSpec (.RBlock body) rs rs'
  /-- **Tuple component load.**  Reads the `idx`-th
      component of `src` into `dst` via `leafSpec.tupleLoad`. -/
  | tupleLoad : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RTupleLoad dst src idx) rs
        (locatedUpdate rs dst (leafSpec.tupleLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Array element store.**  Looks up runtime index
      `rs.rsScalar idxVar`, reads `arr`'s old value, reads `src`'s
      value (with dependent tower type), and writes via
      `leafSpec.arrStore`.  Concrete instances slice arr's byte
      array at offset `idx * src.locDst.storageBytes` to overwrite. -/
  | arrStore : ∀ arr idxVar src rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrStore arr idxVar src) rs
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  /-- **Array element load.**  Looks up runtime index
      `rs.rsScalar idxVar` and reads element `idx` of `src` into
      `dst` via `leafSpec.arrLoad`. -/
  | arrLoad : ∀ dst src idxVar rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrLoad dst src idxVar) rs
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Literal-index array store.**  Same
      shape as `arrStore` but the index is the compile-time literal
      `idx : Nat` from the AST (no `rsScalar` lookup). -/
  | arrStoreLit : ∀ arr idx src rs oldV srcV,
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrStoreLit arr idx src) rs
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  /-- **Literal-index array load.**  Same
      shape as `arrLoad` but the index is the compile-time literal
      `idx : Nat` from the AST. -/
  | arrLoadLit : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrLoadLit dst src idx) rs
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Set scalar slot to an `SExpr` value.**  Evaluates the
      expression with the tower-aware `SExpr.evalState`, so that
      `RScalarSetExpr x (SLimb v i)` reads limb `i` of tower slot `v`, and
      writes the result.  On an `SLimb`-free expression the value is
      `e.eval rs.rsScalar` (`SExpr.evalState_eq_eval`). -/
  | scalarSetExpr : ∀ x e rs,
      RustExec N leafSpec (.RScalarSetExpr x e) rs
        (rsSetScalar rs x (e.evalState rs))
  /-- **Destination-threaded leaf call.**  Single
      output, shape-compatible with `call`, but the destination slot is
      threaded as the first call argument *and* the receiving lvalue:
      `dst = f(dst, args)`.  We read `dst`'s old value, build the argument
      list from `dst :: args` (so the leaf sees the prior destination
      contents as its first input), pass the corresponding dst-types, and
      write the single result back via `leafSpec.call`.  Mirrors `call`'s
      per-arg type-recovery side condition over `dst :: args`. -/
  | callDstThreaded : ∀ f dst args rs oldDestV argList,
      locatedLookup rs dst = some oldDestV →
      argList = (dst :: args).filterMap (fun a => rs.rsTower a.locVar) →
      (∀ a ∈ dst :: args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExec N leafSpec (.RCallDstThreaded f dst args) rs
        (locatedUpdate rs dst
          (leafSpec.call f dst.locDst ((dst :: args).map (·.locDst)) oldDestV argList))

/-- **Runtime-store reconciliation.**  The word
    that `RustExec.limbStoreExpr` records — `BitVec.ofNat 64 (e.evalState rs)`,
    i.e. the saturating-then-truncate-at-storage Nat model — equals the
    intermediate-wrapping hardware value `e.evalStateBV rs` **exactly** under
    the in-range side-condition `inRangeState`.  This is what makes the runtime
    relation a faithful predictor of the emitted code: off the side-condition
    (intermediate overflow, or an `SSub` that underflows — where Nat saturates
    at 0 but hardware wraps) the two can disagree, and the side-condition is
    discharged per kernel by the no-overflow argument in that kernel's
    correctness proof (`fe25519_add` etc. operate on `< 2^51`-bounded limbs, so
    each `SAdd`/`SSub` stays in `u64` range).  Together with
    `RustExec.limbStoreExpr` this closes the model/emit wrapping gap at the
    runtime layer: the stored value is the hardware value on in-range inputs. -/
theorem RustExec_limbStoreExpr_stored_eq_evalStateBV
    (rs : RustState) (e : SExpr) (h : e.inRangeState rs) :
    BitVec.ofNat 64 (e.evalState rs) = e.evalStateBV rs :=
  (SExpr.evalStateBV_eq_ofNat_evalState rs e h).symm

/-! ## §7  `RFor` smoke tests and Hoare-style rule

The Hoare-style rule for `RFor` says: if a state-indexed invariant `I i`
is preserved by one execution of `body` (with the counter set to `i`),
and `I 0` holds initially, then `I n` holds after `RFor x n body`.
This is the standard structural rule for bounded for-loops; it's the
key reason to add `RFor` (vs. open-coding everything as `RWhileNz`):
the rule needs no termination side condition and the loop bound becomes
a free invariant. -/

namespace RustExec

/-- **RFor structural induction rule**: if `I 0 rs` and `body` preserves
    `I` across one iteration with the counter set to `i`, then `I n` holds
    at the post-state. Schematic; `I` ranges over arbitrary state predicates.

    This is Bedrock2's `compile_for` rule stated at the
    semantic level — same shape minus the program-counter bookkeeping. -/
theorem rfor_invariant
    {N : Nat} {leafSpec : LeafSpec} {x : String} {body : LowCT}
    {I : Nat → RustState → Prop}
    (hStep : ∀ (i : Nat) (rs r' : RustState),
        I i rs →
        RustExec N leafSpec body (rsSetScalar rs x i) r' →
        I (i + 1) r') :
    ∀ (n : Nat) (rs r' : RustState),
      I 0 rs →
      RustExec N leafSpec (.RFor x n body) rs r' →
      I n r' := by
  intro n
  induction n with
  | zero =>
    intro rs r' hI hExec
    cases hExec
    exact hI
  | succ k ih =>
    intro rs r' hI hExec
    cases hExec with
    | forSucc _ _ _ _ r1 _ hInner hBody =>
      have hk : I k r1 := ih rs r1 hI hInner
      exact hStep k r1 r' hk hBody

/-- Smoke test: a 3-iteration for-loop with an `RSkip` body executes to
    the explicit scalar-set chain. -/
example (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    RustExec N leafSpec (.RFor "i" 3 .RSkip) rs
      (rsSetScalar (rsSetScalar (rsSetScalar rs "i" 0) "i" 1) "i" 2) := by
  apply forSucc -- iter 2 (n=2 in forSucc, so x ↦ 2 + skip)
  · apply forSucc -- iter 1
    · apply forSucc -- iter 0
      · exact forZero ..
      · exact skip _
    · exact skip _
  · exact skip _

/-- Smoke test of the structural rule: counting iterations. After
    `RFor "i" n RSkip`, the invariant "we ran n iterations" is established. -/
example (N : Nat) (leafSpec : LeafSpec) (n : Nat) (rs r' : RustState)
    (h : RustExec N leafSpec (.RFor "i" n .RSkip) rs r') :
    True :=  -- the statement is `True`; the example checks that `rfor_invariant` applies
  rfor_invariant (I := fun _ _ => True)
    (hStep := fun _ _ _ _ _ => trivial)
    n rs r' trivial h

end RustExec

end CatCrypt.Crypto.Jasmin.LowCT
