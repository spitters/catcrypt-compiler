/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Mpn.Sub32Emit
import CatCrypt.Crypto.Jasmin.Mpn.Add32Refines

set_option autoImplicit false

/-!
# `mpn_sub_n` Jasmin refinement at **U32 limb width**

The U32 SBB mirror of `Mpn.Add32Refines.MpnAdd32JasminRefines`: the emitted
U32 open-coded `mpn_sub_n_oc_32` Jasmin kernel
(`Mpn.Sub32Emit.mpnSubN32Fd`, body `Mpn.Sub32Emit.body32`) refines the U32
functional spec `mpnSubN32` (the U32 specialization of
`Mpn.SubPrototype.mpnSubN`) over byte memory at 4-byte stride.

Same proof skeleton as the U32 add bridge: two `#SUB_32` + `Olor` mirror
`subBorrowIn32`; the per-iteration step lemma reads off the state
update; the loop induction walks the limb list; the final bridge zeroes
the U32 borrow register `cf` and runs the loop.

## Specification

`mpnGenericWidth`/`mpnWidthInstances` does **not** define a width-parametric
`mpnSubNW` (only `mpnAddNW`).  We therefore work against the U32-specific
`sbbStep32` / `mpnSubN32`, defined inline in this file as exact mirrors of
`Mpn.SubPrototype.sbbStep` / `mpnSubN` at limb width 32.

## Reused U32 leaves (from `MpnAdd32Refines`)

* `w64` / `w64_mask` / `w64_add_sum` — `BitVec 32 → BitVec 64` encoding
* `u32_load_roundtrip`, `resolveAddr_vr64` — memory and address plumbing
* `memHoldsLimbs32`, `memHoldsLimbs32_store32_range_frame` — limb-list
  memory predicate and its frame lemma

## Reused stride-parametric helpers (from `MpnAddPrototype`)

* `regAddr_advance_at`, `range_op_head_tail_disjoint_4`,
  `bignumExecFuel_loop_step_generic`, `bignumExecFuel_loop_exit_generic`,
  `evalPExpr_neq_zero_true`, `evalPExpr_neq_zero_false`,
  `ofNat64_succ_ne_zero`, `ofNat64_succ_sub_one`, `disjoint_range_lt`,
  `disjoint_mono`, `storeMem32_mem_proj`, `storeMem32_regs_proj`
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Sub32Refines

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.Sub32Emit
open CatCrypt.Crypto.Jasmin.Mpn.Add32Refines

/-! ## §0  Local copies of the `private` U32-encoding helpers from `MpnAdd32Refines`

`Mpn.Add32Refines.w64` / `w64_mask` are declared `private`, so we redeclare
them here.  Same bodies. -/

/-- Promote a `BitVec 32` value `w` to a `BitVec 64` by `BitVec.ofNat 64 w.toNat`. -/
private def w64 (w : BitVec 32) : BitVec 64 := BitVec.ofNat 64 w.toNat

set_option linter.unusedSimpArgs false in
/-- A `w64`-encoded `BitVec 32` value masked to the low 32 bits is itself. -/
private theorem w64_mask (w : BitVec 32) : w64 w &&& mask32 = w64 w := by
  unfold w64 mask32
  have hzx : (BitVec.ofNat 64 w.toNat) = BitVec.setWidth 64 w := by
    apply BitVec.eq_of_toNat_eq
    have hw : w.toNat < 2 ^ 32 := w.isLt
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
               Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 64),
               Nat.mod_eq_of_lt hw]
  rw [hzx]
  bv_decide

/-- Loading a `BitVec 32` limb from memory and decoding through
    `BitVec.ofNat 64 _.toNat` recovers `w64 w`. -/
private theorem u32_load_roundtrip (w : BitVec 32) :
    BitVec.ofNat 64 (UInt64.ofNat w.toNat).toNat = w64 w := by
  have hw : w.toNat < 2 ^ 32 := w.isLt
  apply BitVec.eq_of_toNat_eq
  unfold w64
  simp only [BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  omega

/-! ## §1  Directly provable facts about the emitted U32 kernel -/

/-- The emitted U32 `mpn_sub_n_oc_32` body is constant-time-shaped: the
    `Cwhile` guard reads only the public length `n`. -/
theorem body32_isCT : isCT_Cmd body32 = true := by decide

/-- The U32 `FunDecl`'s body is *literally* `body32`. -/
theorem mpnSubN32Fd_body : mpnSubN32Fd.body = body32 := rfl

/-! ## §2  U32 functional spec — `sbbStep32` and `mpnSubN32`

Mirror of `Mpn.SubPrototype.sbbStep` / `mpnSubN` at limb width 32.  Stated
locally because `MpnGenericWidth` does not define a width-parametric
`mpnSubNW`. -/

/-- Boolean borrow as a `Nat` (0 or 1).  Local alias to avoid the U64
    `Mpn.SubPrototype.borrowNat` name. -/
def borrowNat (c : Bool) : Nat := if c then 1 else 0

/-- One SBB step on `BitVec 32`: returns `(diff, borrow-out)`.
    `diff = (a - b - bin) mod 2^32`, `borrow-out = (a < b + bin)`. -/
def sbbStep32 (a b : BitVec 32) (bin : Bool) : BitVec 32 × Bool :=
  let d : Nat := b.toNat + (if bin then 1 else 0)
  (BitVec.ofNat 32 ((a.toNat + 2 ^ 32 - d) % 2 ^ 32), decide (a.toNat < d))

/-- Pure reference for U32 `mpn_sub_n`: subtract two `BitVec 32` limb
    lists with a borrow chain. -/
def mpnSubN32 : List (BitVec 32) → List (BitVec 32) → Bool →
    (List (BitVec 32) × Bool)
  | a :: as, b :: bs, bin =>
      let (r, bout) := sbbStep32 a b bin
      let (rs, fbout) := mpnSubN32 as bs bout
      (r :: rs, fbout)
  | _, _, bin => ([], bin)

/-! ## §3  U32 SBB-with-borrow-in bridges — `subBorrowIn32` matches `sbbStep32`

Mirror of `Mpn.Add32Refines.addCarryIn32_sum_uint64` / `_carry` at sub. -/

/-- 32-bit SUB-with-borrow-in.  Returns `(bf, r)` with `r = (a - b - cin) mod
    2^32` (masked) and `bf = 1` iff the masked subtraction wrapped.  Defined
    locally as the U32 mirror of `BignumExec.subBorrowIn` / `addCarryIn32`. -/
def subBorrowIn32 (a b bin : BitVec 64) : BitVec 64 × BitVec 64 :=
  let am := a &&& mask32
  let bm := b &&& mask32
  let bin1 := bin &&& 1
  let r := (am - bm - bin1) &&& mask32
  let bf : BitVec 64 := if am.ult (bm + bin1) then 1 else 0
  (bf, r)

/-- SBB diff bridge at U32, on `UInt64.ofNat _.toNat` shapes: the
    diff that the loop stores at the output pointer equals
    `UInt64.ofNat (sbbStep32 a b cin).1.toNat`.

    Strategy: reduce LHS to `BitVec.ofNat 64 ((a.toNat - b.toNat - cin01) mod 2^32).toNat`
    via the masks `w64_mask`/`hcin_mask`, then push both sides through `toNat`
    and discharge by `omega` on the underflow case split. -/
theorem subBorrowIn32_diff_uint64 (a b : BitVec 32) (c : Bool) :
    UInt64.ofNat
      (subBorrowIn32 (w64 a) (w64 b)
        (BitVec.ofNat 64 (if c then 1 else 0))).2.toNat
      = UInt64.ofNat (sbbStep32 a b c).1.toNat := by
  set cin01 : Nat := if c then 1 else 0 with hcin01
  have hc : cin01 ≤ 1 := by rw [hcin01]; cases c <;> simp
  have hmask_a : (w64 a) &&& mask32 = w64 a := w64_mask a
  have hmask_b : (w64 b) &&& mask32 = w64 b := w64_mask b
  have hcin_mask : (BitVec.ofNat 64 cin01) &&& 1 = BitVec.ofNat 64 cin01 := by
    rw [hcin01]; cases c <;> bv_decide
  -- The LHS reduces to `(w64 a - w64 b - BitVec.ofNat 64 cin01) &&& mask32`,
  -- as a `BitVec 64` value.  Push to a Nat equation via `apply UInt64.toNat.inj`.
  have hlhs_eq : (subBorrowIn32 (w64 a) (w64 b) (BitVec.ofNat 64 cin01)).2
      = (w64 a - w64 b - BitVec.ofNat 64 cin01) &&& mask32 := by
    unfold subBorrowIn32
    simp only [hmask_a, hmask_b, hcin_mask]
  apply UInt64.toNat.inj
  rw [hlhs_eq]
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have hcin64 : cin01 < 2 ^ 64 := by omega
  have hcin1 : (BitVec.ofNat 64 cin01).toNat = cin01 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hcin64
  have hwa : (w64 a).toNat = a.toNat := by
    unfold w64; simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hwb : (w64 b).toNat = b.toNat := by
    unfold w64; simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  unfold sbbStep32
  -- LHS toNat after normalization (see comments below).
  -- RHS toNat: `(BitVec.ofNat 32 ((a.toNat + 2^32 - d) % 2^32)).toNat % 2^64`
  --   where `d = b.toNat + cin01`.
  -- Both sides equal `(a.toNat - b.toNat - cin01) mod 2^32`.
  simp only [UInt64.toNat_ofNat', BitVec.toNat_and, mask32,
             show (0xFFFFFFFF : BitVec 64).toNat = (2 ^ 32 - 1) from by decide,
             BitVec.toNat_sub, BitVec.toNat_ofNat,
             hwa, hwb, hcin1]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 32]
  -- The goal looks like:
  --   ((2^64 - cin01 + (2^64 - b.toNat + a.toNat) % 2^64) % 2^64) % 2^32 % 2^64
  --     = (a.toNat + 2^32 - (b.toNat + cin01)) % 2^32 % 2^64
  -- (modulo Lean's particular reorganization).
  --
  -- Reduce the inner mod first.  `(2^64 - b.toNat + a.toNat) % 2^64 < 2^64`,
  -- and it equals `2^64 - b.toNat + a.toNat` since `2^64 - b.toNat + a.toNat
  -- ≤ 2^64 + a.toNat - 1 < 2 * 2^64`, with the cases depending on
  -- `a.toNat ≥ b.toNat`.
  --
  -- Approach: identify the unique `0 ≤ d < 2^32` such that LHS = d % 2^64
  -- and RHS = d % 2^64, where `d = (a.toNat - b.toNat - cin01) mod 2^32`
  -- in the wrap-aware Nat sense.  Use `omega` after the case-split.
  by_cases hab : a.toNat ≥ b.toNat
  · -- a ≥ b.
    have hinner_mod : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 = a.toNat - b.toNat := by
      have hrew : 2 ^ 64 - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ 64 := by omega
      rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hinner_mod]
    by_cases habc : a.toNat ≥ b.toNat + cin01
    · -- a ≥ b + cin01.  Value `(a - b - cin01)`.
      have houter : (2 ^ 64 - cin01 + (a.toNat - b.toNat)) % 2 ^ 64
          = a.toNat - b.toNat - cin01 := by
        have : 2 ^ 64 - cin01 + (a.toNat - b.toNat) = (a.toNat - b.toNat - cin01) + 2 ^ 64 := by
          omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [houter]
      have hrhs : a.toNat + 2 ^ 32 - (b.toNat + cin01) = (a.toNat - b.toNat - cin01) + 2 ^ 32 := by
        omega
      rw [hrhs, Nat.add_mod_right]
      -- Now both sides have outer `% 2^64` / `% 2^32` wrappers around a value
      -- strictly less than `2^32`.  Close uniformly.
      omega
    · -- a ≥ b but a < b + cin01 ⇒ a = b, cin01 = 1.  Both sides = 2^32 - 1.
      have heq : a.toNat = b.toNat := by omega
      have hc1 : cin01 = 1 := by omega
      have houter : (2 ^ 64 - cin01 + (a.toNat - b.toNat)) % 2 ^ 64 = 2 ^ 64 - 1 := by
        rw [heq, Nat.sub_self, Nat.add_zero, hc1, Nat.mod_eq_of_lt (by omega)]
      rw [houter]
      have hrhs : a.toNat + 2 ^ 32 - (b.toNat + cin01) = 2 ^ 32 - 1 := by omega
      rw [hrhs]
      have hlhs_mod32 : (2 ^ 64 - 1) % 2 ^ 32 = 2 ^ 32 - 1 := by
        have h64 : (2 : Nat) ^ 64 - 1 = (2 ^ 32 - 1) + 2 ^ 32 * (2 ^ 32 - 1) := by
          have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
          have h64' : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
          omega
        rw [h64, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hlhs_mod32]
      omega
  · -- a < b.  Then a < b + cin01.
    have hab' : a.toNat < b.toNat := by omega
    have habc : a.toNat < b.toNat + cin01 := by omega
    have hinner_mod : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64
        = 2 ^ 64 - b.toNat + a.toNat := by
      apply Nat.mod_eq_of_lt; omega
    rw [hinner_mod]
    -- 2^64 - cin01 + (2^64 - b + a) = 2^64 + (2^64 - ((b + cin01) - a))
    -- where (b+cin01) - a ≥ 1 and ≤ 2^32.
    have hsum1 : 2 ^ 64 - cin01 + (2 ^ 64 - b.toNat + a.toNat)
        = 2 ^ 64 + (2 ^ 64 - ((b.toNat + cin01) - a.toNat)) := by omega
    rw [hsum1, Nat.add_mod_left]
    have hinner2_lt : 2 ^ 64 - ((b.toNat + cin01) - a.toNat) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hinner2_lt]
    -- (2^64 - ((b + cin01) - a)) mod 2^32 = 2^32 - ((b + cin01) - a).
    have hgap_pos : 0 < (b.toNat + cin01) - a.toNat := by omega
    have hgap_le : (b.toNat + cin01) - a.toNat ≤ 2 ^ 32 := by omega
    have hreshape : 2 ^ 64 - ((b.toNat + cin01) - a.toNat)
        = (2 ^ 32 - ((b.toNat + cin01) - a.toNat)) + 2 ^ 32 * (2 ^ 32 - 1) := by
      have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
      have h64' : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
      omega
    rw [hreshape, Nat.add_mul_mod_self_left]
    -- RHS: (a + 2^32 - (b + cin01)) % 2^32 = 2^32 - ((b + cin01) - a).
    have hrhs : a.toNat + 2 ^ 32 - (b.toNat + cin01)
        = 2 ^ 32 - ((b.toNat + cin01) - a.toNat) := by omega
    rw [hrhs]
    -- Both sides equal `2^32 - ((b+cin01) - a)` after the outer mods reduce.
    omega

/-- SBB borrow bridge at U32: the borrow-out flag of `subBorrowIn32` equals
    `BitVec.ofNat 64 (borrowNat (sbbStep32 a b c).2)`. -/
theorem subBorrowIn32_borrow (a b : BitVec 32) (c : Bool) :
    (subBorrowIn32 (w64 a) (w64 b)
        (BitVec.ofNat 64 (if c then 1 else 0))).1
      = BitVec.ofNat 64 (borrowNat (sbbStep32 a b c).2) := by
  set cin01 : Nat := if c then 1 else 0 with hcin01
  have hc : cin01 ≤ 1 := by rw [hcin01]; cases c <;> simp
  have hmask_a : (w64 a) &&& mask32 = w64 a := w64_mask a
  have hmask_b : (w64 b) &&& mask32 = w64 b := w64_mask b
  have hcin_mask : (BitVec.ofNat 64 cin01) &&& 1 = BitVec.ofNat 64 cin01 := by
    rw [hcin01]; cases c <;> bv_decide
  -- Compute LHS via `show`: unfold the `subBorrowIn32` body, exploit the masks.
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have hwa : (w64 a).toNat = a.toNat := by
    unfold w64; simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hwb : (w64 b).toNat = b.toNat := by
    unfold w64; simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hcin64 : cin01 < 2 ^ 64 := by omega
  have hcin1 : (BitVec.ofNat 64 cin01).toNat = cin01 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hcin64
  have hadd : (w64 b + BitVec.ofNat 64 cin01).toNat = b.toNat + cin01 := by
    simp only [BitVec.toNat_add, hwb, hcin1]
    apply Nat.mod_eq_of_lt; omega
  -- LHS = `if (w64 a &&& mask32).ult (w64 b &&& mask32 + BitVec.ofNat 64 cin01 &&& 1) then 1 else 0`.
  have hlhs_eq : (subBorrowIn32 (w64 a) (w64 b) (BitVec.ofNat 64 cin01)).1
      = (if (w64 a).ult (w64 b + BitVec.ofNat 64 cin01) then 1 else 0) := by
    unfold subBorrowIn32
    simp only [hmask_a, hmask_b, hcin_mask]
  rw [hlhs_eq]
  -- The `ult` condition matches `a.toNat < b.toNat + cin01` via the `hadd`/`hwa` toNat identities.
  have hult : (w64 a).ult (w64 b + BitVec.ofNat 64 cin01) = decide (a.toNat < b.toNat + cin01) := by
    simp only [BitVec.ult, hwa, hadd]
  rw [hult]
  -- RHS: `BitVec.ofNat 64 (borrowNat (sbbStep32 a b c).2)`.
  -- `(sbbStep32 a b c).2 = decide (a.toNat < b.toNat + cin01)`.
  have hrhs : (sbbStep32 a b c).2 = decide (a.toNat < b.toNat + cin01) := by
    unfold sbbStep32; simp [hcin01]
  rw [hrhs]
  unfold borrowNat
  by_cases hlt : a.toNat < b.toNat + cin01
  · simp only [hlt, decide_true, if_true]; rfl
  · simp only [hlt, decide_false]; rfl

/-! ## §4  U32 open-coded body bridge — two `#SUB_32` + `Olor`

The U32 loop body composes two `subBorrow32` (each `#SUB_32` writes
`writeSubBundle`'s `[cf, dst]`) plus a `Olor` of the two borrows.  This
matches `subBorrowIn32` exactly when the threaded borrow is already a
low bit. -/

/-- `subBorrow32 a b = (bf, r)` with `r = (a - b) masked to 32 bits` and
    `bf = 1` iff `(a &&& mask32).ult (b &&& mask32)`.  Definitional unfold. -/
theorem subBorrow32_eq (a b : BitVec 64) :
    subBorrow32 a b =
      ((if ((a &&& mask32).ult (b &&& mask32)) then 1 else 0),
       ((a &&& mask32) - (b &&& mask32)) &&& mask32) := rfl

/-- **Open-coded U32 composition = `subBorrowIn32`.**  Composing
    `subBorrow32 t s` (giving `(bf1, r0)`) with `subBorrow32 r0 cf`
    (giving `(bf2, r)`) and taking the new borrow as `bf1 ||| bf2`
    yields exactly `subBorrowIn32 t s cf` — provided the threaded borrow
    `cf` is already a low bit (`cf &&& 1 = cf`).  Pure `BitVec`, closed
    by `bv_decide`. -/
theorem openBody32_eq_subBorrowIn32 (t s cf : BitVec 64) (hcf : cf &&& 1 = cf) :
    ((subBorrow32 t s).1 ||| (subBorrow32 (subBorrow32 t s).2 cf).1,
      (subBorrow32 (subBorrow32 t s).2 cf).2)
      = subBorrowIn32 t s cf := by
  unfold subBorrow32 subBorrowIn32 mask32
  refine Prod.ext ?_ ?_ <;> bv_decide

/-! ## §5  U32 per-iteration step lemma

The U32 SBB analogue of `Mpn.Add32Refines.bignumExec_loopBody32_step`. -/

/-- `subBorrowIn32`'s result is already masked to 32 bits; the masked-by-
    `0xFFFFFFFF` reduction on the stored value is the identity. -/
theorem subBorrowIn32_lo32 (a b cin : BitVec 64) :
    (subBorrowIn32 a b cin).2 &&& 0xFFFFFFFF = (subBorrowIn32 a b cin).2 := by
  unfold subBorrowIn32 mask32
  bv_decide

/-- The `loopBody32` is straight-line (`Cassgn` / `Copn` only). -/
theorem loopBody32_straightLine : InstrR.bodyIsStraightLine loopBody32 := by
  simp only [loopBody32, load32At0, subCopn32, store32At0, ptrImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBody32` is non-control. -/
theorem loopBody32_nonControl : ∀ i ∈ loopBody32, i.isNonControl := by
  intro i hi
  simp only [loopBody32, load32At0, subCopn32, store32At0, ptrImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem bignumExec_loopBody32_sub_step (s : BignumState) (a b : BitVec 32) (bin : Bool)
    (hcf : s.regs "cf" = BitVec.ofNat 64 (if bin then 1 else 0))
    (ha : load32Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load32Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBody32 s = some s' ∧
      s'.mem = Mem.store32 s.mem (regAddr s "op")
        (UInt64.ofNat (sbbStep32 a b bin).1.toNat) ∧
      s'.regs "cf" = BitVec.ofNat 64 (borrowNat (sbbStep32 a b bin).2) ∧
      s'.regs "ap" = s.regs "ap" + 4 ∧
      s'.regs "bp" = s.regs "bp" + 4 ∧
      s'.regs "op" = s.regs "op" + 4 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Unfold the body, the semantic dispatchers, and the projection simp lemmas.
  -- Mirror the U32 add step exactly, swapping `addCopn32`/`addCarry32`/`addCarryIn32`
  -- for `subCopn32`/`subBorrow32`/`subBorrowIn32`.
  simp only [loopBody32, load32At0, subCopn32, store32At0, ptrImm,
             bignumExec, execInstr, evalPExpr, pv32, pv64,
             resolveAddr_vr64, vr32, vr64,
             setReg_mem, setReg_regs, storeMem32_mem_proj, storeMem32_regs_proj,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem32_regs_proj, storeMem32_mem_proj,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, hb, Option.bind_some, bind, Option.bind] at *
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [Option.bind_some, bind, Option.bind]
  rw [show (setReg s "t" (BitVec.ofNat 64 (UInt64.ofNat a.toNat).toNat)).regs "bp" + 0
        = s.regs "bp" from by simp only [setReg_regs]; bv_decide, setReg_mem, hb]
  simp only [Option.bind_some, bind, Option.bind]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [setReg_regs, setReg_mem, storeMem32_mem_proj, storeMem32_regs_proj,
               regAddr, String.reduceEq, ↓reduceIte, reduceIte, hcf,
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 4 = (4 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]
  · -- Memory: stored value `(subBorrow32 (subBorrow32 t s).2 cf).2`
    -- equals `UInt64.ofNat (sbbStep32 a b bin).1.toNat` via
    -- `openBody32_eq_subBorrowIn32` + `subBorrowIn32_diff_uint64`.
    have hmask : (BitVec.ofNat 64 (if bin then 1 else 0) : BitVec 64) &&& 1
        = BitVec.ofNat 64 (if bin then 1 else 0) := by cases bin <;> bv_decide
    have hopen := openBody32_eq_subBorrowIn32 (w64 a) (w64 b)
      (BitVec.ofNat 64 (if bin then 1 else 0)) hmask
    have hopen2 := congrArg Prod.snd hopen
    simp only at hopen2
    rw [u32_load_roundtrip a, u32_load_roundtrip b]
    rw [hopen2]
    congr 1
    exact subBorrowIn32_diff_uint64 a b bin
  · -- Borrow register: `(subBorrow32 t s).1 ||| (subBorrow32 r0 cf).1` =
    -- `BitVec.ofNat 64 (borrowNat (sbbStep32 a b bin).2)`.
    have hmask : (BitVec.ofNat 64 (if bin then 1 else 0) : BitVec 64) &&& 1
        = BitVec.ofNat 64 (if bin then 1 else 0) := by cases bin <;> bv_decide
    have hopen := openBody32_eq_subBorrowIn32 (w64 a) (w64 b)
      (BitVec.ofNat 64 (if bin then 1 else 0)) hmask
    have hopen1 := congrArg Prod.fst hopen
    simp only at hopen1
    rw [u32_load_roundtrip a, u32_load_roundtrip b, hopen1,
        subBorrowIn32_borrow a b bin]

/-! ## §6  The U32 loop, by induction on the limb list -/

theorem mpnSubN32_openLoop :
    ∀ (as bs : List (BitVec 32)) (s : BignumState) (bin : Bool) (extra : Nat),
      as.length = bs.length →
      s.regs "cf" = BitVec.ofNat 64 (if bin then 1 else 0) →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs32 s.mem (regAddr s "ap") as →
      memHoldsLimbs32 s.mem (regAddr s "bp") bs →
      MemoryModel.Disjoint (range (regAddr s "op") (4 * as.length))
        (range (regAddr s "ap") (4 * as.length)) →
      MemoryModel.Disjoint (range (regAddr s "op") (4 * as.length))
        (range (regAddr s "bp") (4 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBody32] s
              = some s' ∧
        memHoldsLimbs32 s'.mem (regAddr s "op") (mpnSubN32 as bs bin).1 ∧
        s'.regs "cf" = BitVec.ofNat 64 (borrowNat (mpnSubN32 as bs bin).2) ∧
        (∀ b, MemoryModel.Disjoint (range b 4)
              (range (regAddr s "op") (4 * as.length)) →
            load32Mem s'.mem b = load32Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s bin extra _ hcf hn _ _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 32)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 0 :=
        evalPExpr_neq_zero_false s (pv64 "n")
          (by simp only [pv64, vr64, evalPExpr]; rw [hn0])
      exact bignumExecFuel_loop_exit_generic emptyRegistry extra _ loopBody32 s hcond
    · simp [mpnSubN32]
    · simpa [mpnSubN32, borrowNat] using hcf
    · intro b _; rfl
  | cons a as ih =>
    intro bs s bin extra hlen hcf hn hap hbp hdoa hdob
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have hsize : 4 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (4 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨hbp_head, hbp_tail⟩ := hbp
      -- One U32 SBB iteration.
      obtain ⟨s1, hs1, hs1_mem, hs1_cf, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_loopBody32_sub_step s a b bin hcf hap_head hbp_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hadv : ∀ (bv : BitVec 64),
          UInt64.ofNat (bv + 4).toNat = UInt64.ofNat bv.toNat + 4 := by
        intro bv
        have h := regAddr_advance_at bv 4
        rw [show (BitVec.ofNat 64 4 : BitVec 64) = 4 from rfl,
            show (UInt64.ofNat 4 : UInt64) = 4 from rfl] at h
        exact h
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 4 := by
        simp only [regAddr, hs1_ap]; exact hadv _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 4 := by
        simp only [regAddr, hs1_bp]; exact hadv _
      have hra_op : regAddr s1 "op" = op0 + 4 := by
        simp only [regAddr, hs1_op, hop0]; exact hadv _
      have hmem1 : s1.mem = Mem.store32 s.mem op0
          (UInt64.ofNat (sbbStep32 a b bin).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      -- Frame the tail of `ap`/`bp` across the head store at `op0`.
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 4) (range (regAddr s "ap" + 4) (4 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hdob_store_bptail :
          MemoryModel.Disjoint (range op0 4) (range (regAddr s "bp" + 4) (4 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hap1 : memHoldsLimbs32 s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs32_store32_range_frame s.mem (regAddr s "ap" + 4) op0 _ as
          hdoa_store_aptail hap_tail
      have hbp1 : memHoldsLimbs32 s1.mem (regAddr s1 "bp") bs := by
        rw [hra_bp, hmem1]
        exact memHoldsLimbs32_store32_range_frame s.mem (regAddr s "bp" + 4) op0 _ bs
          (by rw [hlen'] at hdob_store_bptail; exact hdob_store_bptail) hbp_tail
      -- Disjointness for the IH.
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (4 * as.length))
          (range (regAddr s1 "ap") (4 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hdob1 : MemoryModel.Disjoint (range (regAddr s1 "op") (4 * as.length))
          (range (regAddr s1 "bp") (4 * as.length)) := by
        rw [hra_op, hra_bp]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hcf1 : s1.regs "cf" = BitVec.ofNat 64
          (if (sbbStep32 a b bin).2 then 1 else 0) := by
        rw [hs1_cf]; simp [borrowNat]
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_mem, hs'_cf, hs'_frame⟩ :=
        ih bs s1 (sbbStep32 a b bin).2 extra hlen' hcf1 hn1 hap1 hbp1 hdoa1 hdob1
      refine ⟨s', ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 1 :=
          evalPExpr_neq_zero_true s (pv64 "n") (s.regs "n")
            (by simp only [pv64, vr64, evalPExpr]) hn_ne
        refine bignumExecFuel_loop_step_generic emptyRegistry
          (2 * as.length + 2 + extra) _ loopBody32 loopBody32_straightLine
          loopBody32_nonControl s s1 s' hcond hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- Memory at op: head at `op0`, tail by IH.
        rw [hmem1] at hs'_frame
        have hsep : MemoryModel.Disjoint (range op0 4) (range (op0 + 4) (4 * as.length)) :=
          range_op_head_tail_disjoint_4 op0 as.length (by omega)
        refine ⟨?_, ?_⟩
        · rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
          have hread := load32Mem_store32_same s.mem op0
            (UInt64.ofNat (sbbStep32 a b bin).1.toNat)
          rw [hread]
          have hsum : (sbbStep32 a b bin).1.toNat < 2 ^ 32 :=
            (sbbStep32 a b bin).1.isLt
          have hmask : (UInt64.ofNat (sbbStep32 a b bin).1.toNat
              &&& 0xFFFFFFFF : UInt64)
              = UInt64.ofNat (sbbStep32 a b bin).1.toNat := by
            apply UInt64.toNat.inj
            simp only [UInt64.toNat_and, UInt64.toNat_ofNat',
                       show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from by decide]
            rw [Nat.mod_eq_of_lt (by omega : (sbbStep32 a b bin).1.toNat < 2 ^ 64),
                Nat.and_two_pow_sub_one_eq_mod _ 32, Nat.mod_eq_of_lt hsum]
          rw [hmask]
          rfl
        · have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · rw [hs'_cf]; simp only [mpnSubN32]
      · intro bb hbb
        rw [hmem1] at hs'_frame
        have hbb_tail : MemoryModel.Disjoint (range bb 4)
            (range (regAddr s1 "op") (4 * as.length)) := by
          rw [hra_op]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        rw [hs'_frame bb hbb_tail]
        have hbb_head : MemoryModel.Disjoint (range bb 4) (range (regAddr s "op") 4) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        rw [load32Mem_store32_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-! ## §7  The full U32 SBB bridge -/

/-- **The U32 SBB Jasmin refinement obligation.**  Starting from a state
    whose memory holds `as : List (BitVec 32)` at `ap`, `bs : List (BitVec 32)`
    at `bp`, with `n = |as|`, with the U32 `op` output region disjoint from
    the two U32 input regions, running `body32` lands a state whose memory
    at `op` holds `(mpnSubN32 as bs false).1` and whose `cf` register holds
    the final borrow encoded as `BitVec 64 (borrowNat …)`. -/
def mpnSub32_outer_loop_obligation : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 32)) (fuel : Nat),
    as.length = bs.length →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (4 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (4 * as.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (4 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (4 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel body32 s = some s' ∧
      memHoldsLimbs32 s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnSubN32 as bs false).1 ∧
      s'.regs "cf" = BitVec.ofNat 64 (borrowNat (mpnSubN32 as bs false).2)

/-- Bridge `Prop` abbrev (mirror of `MpnAdd32JasminRefinesProp`). -/
abbrev MpnSub32JasminRefinesProp : Prop := mpnSub32_outer_loop_obligation

theorem MpnSub32JasminRefines_proof : mpnSub32_outer_loop_obligation := by
  intro s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  set s0 : BignumState := setReg s "cf" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr32 "cf" }) .AT_none (.sword .U32) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr32, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcf0 : s0.regs "cf" = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "cf" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cf" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hap0 : memHoldsLimbs32 s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]
    simp only [regAddr]
    exact hap
  have hbp0 : memHoldsLimbs32 s0.mem (regAddr s0 "bp") bs := by
    rw [hmem0, hra0 "bp" (by decide)]
    simp only [regAddr]
    exact hbp
  have hdoa0 : MemoryModel.Disjoint (range (regAddr s0 "op") (4 * as.length))
      (range (regAddr s0 "ap") (4 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]
    simp only [regAddr]
    exact hdoa
  have hdob0 : MemoryModel.Disjoint (range (regAddr s0 "op") (4 * as.length))
      (range (regAddr s0 "bp") (4 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "bp" (by decide)]
    simp only [regAddr]
    exact hdob
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cf, _⟩ :=
    mpnSubN32_openLoop as bs s0 false extra hlen hcf0 hn0' hap0 hbp0 hdoa0 hdob0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) body32 s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBody32] s0 := by
      conv_lhs => rw [body32]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    simp only [regAddr] at hs'_mem
    exact hs'_mem
  · exact hs'_cf

/-- **The U32 SBB Jasmin refinement, fully proved.**  The emitted U32
    `mpn_sub_n_oc_32` Jasmin kernel refines `mpnSubN32` over byte memory
    at 4-byte stride.  Mirror of `MpnAdd32JasminRefines`. -/
theorem MpnSub32JasminRefines : MpnSub32JasminRefinesProp :=
  MpnSub32JasminRefines_proof

/-! ## §8  Axiom audit -/

#print axioms body32_isCT
#print axioms mpnSubN32Fd_body
#print axioms MpnSub32JasminRefines

end CatCrypt.Crypto.Jasmin.Mpn.Sub32Refines
