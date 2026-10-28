/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCTTypes
public import CatCrypt.Crypto.Jasmin.LowCTSExpr

/-!
# `LowCT` runtime state

The state layer of the `LowCT` big-step semantics (`LowCTExec` re-exports it):
the leaf oracles `LeafSpec`, the runtime state `RustState` with its update
lemmas, the limb read `towerLimb`, the tower-aware evaluators
`SExpr.evalState` and `SExpr.evalStateBV`, and the typed lookup
`locatedLookup`. The module depends on the tower types and on `SExpr`, not on
the command syntax.

## Main results

* `SExpr.evalState_eq_eval`: on an expression without limb reads, the tower-aware
  evaluator is `SExpr.eval` at the scalar state.
* `towerLimb_lt`, `rsTowerLimb_lt`: a limb read is below `2 ^ 64`.
* `SExpr.evalStateBV_eq_ofNat_evalState`: on an expression in range, the bit-vector
  evaluator is the natural-number evaluator read as a 64-bit word.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

/-! ## §4  Runtime state -/

/-- Specification of a single leaf-function call.
    `f dt argTs oldDest args` = new value of dest after calling `f`. -/
def CallSpec :=
  String →
  ∀ (dt : TowerType) (_argTs : List TowerType),
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
  call : CallSpec
  limbStore : LimbStoreSpec
  /-- Tuple-load oracle.  Defaults to identity. -/
  tupleLoad : TupleLoadSpec := fun _ oldV _ _ => oldV
  /-- Array-element store oracle.  Defaults to identity. -/
  arrStore : ArrStoreSpec := fun _ oldV _ _ => oldV
  /-- Array-element load oracle.  Defaults to identity. -/
  arrLoad : ArrLoadSpec := fun _ oldV _ _ => oldV

/-- Runtime state: a tower-variable heap and a scalar heap.  `rsScalar`'s `Nat`
    carrier is the MEMORY-SAFETY layer's convenience (frame reasoning is easier
    over `Nat`, and monus-vs-wrap is irrelevant to aliasing) — it is NOT the
    `u64` value semantics (see `SExpr.eval` / `SExpr.evalBV`). -/
structure RustState where
  rsTower : String → Option (Σ t : TowerType, RustVal t)
  rsScalar : String → Nat -- default 0

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
      sexprOfSignedInt64
        (sexprToSignedInt64 (a.evalState rs) * sexprToSignedInt64 (b.evalState rs))
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
hardware.  But the runtime relation `RustExec` (in `LowCTExec`) stores a runtime
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
  | .SShr a b =>
      (a.evalStateBV rs) >>> SecureCompilation.VIR.shiftMask 64 (b.evalStateBV rs).toNat
  | .SShl a b =>
      (a.evalStateBV rs) <<< SecureCompilation.VIR.shiftMask 64 (b.evalStateBV rs).toNat
  | .SAnd a b => a.evalStateBV rs &&& b.evalStateBV rs
  | .SXor a b => a.evalStateBV rs ^^^ b.evalStateBV rs
  | .SLt  a b => if (a.evalStateBV rs).toNat < (b.evalStateBV rs).toNat then 1 else 0
  | .SAsr a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64
          (sexprToSignedInt64 (a.evalStateBV rs).toNat >>> ((b.evalStateBV rs).toNat : Nat)))
  | .SMulS a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64
          (sexprToSignedInt64 (a.evalStateBV rs).toNat
            * sexprToSignedInt64 (b.evalStateBV rs).toNat))
  | .SMulHiU a b =>
      BitVec.ofNat 64 (sexprMulHiU (a.evalStateBV rs).toNat (b.evalStateBV rs).toNat)
  | .SMulHiS a b =>
      BitVec.ofNat 64 (sexprMulHiS (a.evalStateBV rs).toNat (b.evalStateBV rs).toNat)
  | .SLimb v i => BitVec.ofNat 64 (rsTowerLimb rs v i)

/-- Tower-aware in-range side-condition (runtime layer): the counterpart of
    `SExpr.inRange` for `evalState`.  Under it, the saturating-then-truncate
    runtime store equals the intermediate-wrapping hardware value.  The
    `SLimb` arm needs no condition — the limb read is always `< 2^64`. -/
def SExpr.inRangeState (rs : RustState) : SExpr → Prop
  | .SVar x   => rs.rsScalar x < 2 ^ 64
  | .SLit n   => n < 2 ^ 64
  | .SAdd a b =>
      a.inRangeState rs ∧ b.inRangeState rs ∧ a.evalState rs + b.evalState rs < 2 ^ 64
  | .SSub a b => a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs ≤ a.evalState rs
  | .SMul a b =>
      a.inRangeState rs ∧ b.inRangeState rs ∧ a.evalState rs * b.evalState rs < 2 ^ 64
  | .SShr a b => a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs < 64
  | .SShl a b =>
      a.inRangeState rs ∧ b.inRangeState rs ∧ b.evalState rs < 64 ∧
        a.evalState rs <<< b.evalState rs < 2 ^ 64
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
      rw [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_ushiftRight, iha h.1, ihb h.2.1,
        SecureCompilation.VIR.shiftMask_of_lt h.2.2]
  | SShl a b iha ihb =>
      intro h
      rw [SExpr.evalStateBV, SExpr.evalState, BitVec.toNat_shiftLeft, iha h.1, ihb h.2.1,
        SecureCompilation.VIR.shiftMask_of_lt h.2.2.1]
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

/-- `rsSetTower` writes the given value at its variable. -/
theorem rsSetTower_same (rs : RustState) (x : String) (v : Σ t, RustVal t) :
    (rsSetTower rs x v).rsTower x = some v := by
  simp [rsSetTower]

/-- `rsSetTower` leaves every other tower variable unchanged. -/
theorem rsSetTower_other (rs : RustState) (x y : String)
    (v : Σ t, RustVal t) (h : x ≠ y) :
    (rsSetTower rs x v).rsTower y = rs.rsTower y := by
  unfold rsSetTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- `rsRemoveTower` leaves every other tower variable unchanged. -/
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

end CatCrypt.Crypto.Jasmin.LowCT
