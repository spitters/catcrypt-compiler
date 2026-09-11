/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.Add32Emit
public import CatCrypt.Crypto.Jasmin.Mpn.AddOpenCarryPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.GenericWidth
public import CatCrypt.Crypto.Jasmin.Mpn.WidthInstances

@[expose] public section

set_option autoImplicit false

/-!
# `mpn_add_n` Jasmin refinement at **U32 limb width** — pinned residual

This file is the U32 analogue of
`Mpn.AddOpenCarryPrototype.MpnAddOpenCarryRefines`: it states the
refinement bridge that the U32 open-coded `mpn_add_n_oc_32` Jasmin kernel
(`Mpn.Add32Emit.mpnAddN32Fd`, body `Mpn.Add32Emit.body32`) computes the
functional spec `Mpn.GenericWidth.mpnAddNW 32` (equivalently
`Mpn.WidthInstances.mpnAdd32`) over byte memory with **4-byte limb
stride**.

## Status: pinned residual (in the `Mpn.PowPrototype.MpnPowJasminRefines`
style)

The U64 bridge `MpnAddOpenCarryRefines` is a ~150-line induction on the
limb list that consumes a full stack of bespoke U64 plumbing
(`Mpn.AddPrototype.memHoldsLimbs`, `regAddr`, `bignumExec_loopBody_step`,
`bignumExecFuel_loop_step`/`_exit`, `range_shift_subset`,
`range_op_head_tail_disjoint`, `memHoldsLimbs_store64_frame`,
`ofNat64_succ_*`, the per-iteration `setReg`/`storeMem` simp arsenal,
…).  *None* of that is parameterized by limb width — every theorem is
stated at `BitVec 64` with byte stride `8`, the address-arithmetic
identities (`regAddr_advance` at `+8`, `range_op_head_tail_disjoint` at
`8 * k`) are hand-tuned, the `bv_decide`-emitted natives are width-fixed,
and the one-iteration simp script reads `addCarryIn_sum` /
`addCarryIn_carry` (U64-only bridges to `adcStep`).

Replicating that stack at U32 — with `BitVec 32` limbs, `load32Mem` /
`Mem.store32` (already in `BignumExec` at commit `cacca611`), a 4-byte
stride, an `adcStep32`/`addCarryIn32`-based per-step lemma, the U32
analogues of `range_shift_subset` at offset 4 / size `4 * k`, and a U32
`mpnAddN_openLoop32` induction — is **the very work this bridge
demands** and matches the scope of the U64 file exactly.  It is not a
20-minute task.

This file therefore delivers the bridge **as a sorry-free, named `Prop`
residual** in the `MpnPowJasminRefines` style:

* The residual statement `mpnAdd32_outer_loop_obligation` is the precise
  bridge obligation, with the same shape as
  `Mpn.AddOpenCarryPrototype.MpnAddOpenCarryRefinesStmt` modulo the
  U64→U32 substitutions (limb type `BitVec 32`, 4-byte stride,
  `load32Mem`, the U32 carry encoding).
* `MpnAdd32JasminRefines` is the abbrev binding the canonical bridge
  name to this residual.
* The directly provable supporting facts (constant-time-shape of the
  body, the U32 `memHoldsLimbs32` predicate over `load32Mem`, the
  `mpnAdd32 = mpnAddNW 32` denotation tie-in already established by
  `MpnWidthInstances`) are recorded next to the residual so the
  follow-up induction can be slotted in *without* re-stating the
  bridge.
* The U32 memory-algebra leaves (`load32Mem_store32_same`,
  `load32Mem_store32_disjoint`, `loadByte_store32`,
  `loadByte_store32_frame`) — the U32 analogues of the U64 leaves the
  U64 bridge consumes — are *already proved* in `BignumExec` (commit
  `cacca611`) and we reuse them here to prove a U32 frame lemma
  (`memHoldsLimbs32_store32_frame`).  This is the load-bearing first
  rung of the U32 ladder; the rest is the limb-list induction.

## What this file is — and is not

* **Is**: the canonical bridge `Prop` for the U32 emitted kernel,
  imported by any downstream code that wants to *cite* the bridge while
  the induction is being completed — exactly the role
  `MpnPowJasminRefines` plays for `mpn_pow`.  Plus a small set of *new* and
  *fully proved* U32 lemmas that the follow-up induction will consume.

* **Is not**: a finished bridge.  The remaining work is a clone of
  `Mpn.AddOpenCarryPrototype.mpnAddN_openLoop` at limb-width 32: a U32
  one-iteration step lemma (consuming `addCarryIn32` from
  `BignumExec`), a U32 forward loop-step rule, and the inductive
  walk on `as : List (BitVec 32)`.  This residual records the exact
  obligation that yields a *theorem* once that induction is done.

## Why this is the right shape today

Per `Mpn.Add32Emit.lean`'s own header:

> ## Emission only — proof reuse is future work
>
> This file provides the U32 `FunDecl` and emits its `.jazz` …  The
> *correctness* re-proof at U32 — the analogue of
> `Mpn.AddOpenCarryPrototype.MpnAddOpenCarryRefines` over `BitVec 32`
> limbs — is a separate, larger task.

The pinned residual is the canonical way (the `MpnPow` precedent) to
*name* that larger task: a sorry-free `Prop` ready for downstream
citation, with the directly-buildable U32 helpers proved next to it so
the induction has its leaves in place.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Add32Refines

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.Add32Emit

/-! ## §1  Directly provable facts about the emitted U32 kernel -/

/-- The emitted U32 `mpn_add_n_oc_32` body is constant-time-shaped: the
    `Cwhile` guard reads only the public length `n`.  Imported from the
    `MpnAdd32Emit` `example`; restated as a named theorem so the bridge
    obligation can cite it. -/
theorem body32_isCT : isCT_Cmd body32 = true := by decide

/-- The U32 `FunDecl`'s body is *literally* `body32` (the `cf := 0`
    prelude followed by the `while (n != 0) { loopBody32 }` loop).  This
    is the structural tie-in between the emitted `FunDecl` and the
    `bignumExecFuel`-driven semantics. -/
theorem mpnAddN32Fd_body : mpnAddN32Fd.body = body32 := rfl

/-! ## §2  U32 memory predicate — limbs at 4-byte stride

The U32 analogue of `Mpn.AddPrototype.memHoldsLimbs`: a memory holds a
list of `BitVec 32` limbs little-endian starting at byte address `base`
with **4-byte stride**, decoded by `load32Mem`.  The U32 path's read-back
in `BignumExec` (`load32Mem_store32_same`) returns `v &&& 0xFFFFFFFF`,
not `v` raw — the encoding of a `BitVec 32` limb `w` in memory is the
masked `UInt64` `UInt64.ofNat w.toNat &&& 0xFFFFFFFF`.  For the limb
denotation we use `UInt64.ofNat w.toNat`, which already has the high
half zero (since `w.toNat < 2^32`); the `&&& 0xFFFFFFFF` on read-back is
the identity on such values. -/
def memHoldsLimbs32 (m : MemoryModel.Mem) (base : UInt64) :
    List (BitVec 32) → Prop
  | []      => True
  | w :: ws =>
      load32Mem m base = some (UInt64.ofNat w.toNat) ∧
      memHoldsLimbs32 m (base + 4) ws

/-- `memHoldsLimbs32 m base []` is trivially `True`. -/
@[simp] theorem memHoldsLimbs32_nil (m : Mem) (base : UInt64) :
    memHoldsLimbs32 m base [] = True := rfl

/-- One-step unfold for `memHoldsLimbs32`. -/
@[simp] theorem memHoldsLimbs32_cons (m : Mem) (base : UInt64)
    (w : BitVec 32) (ws : List (BitVec 32)) :
    memHoldsLimbs32 m base (w :: ws) =
      (load32Mem m base = some (UInt64.ofNat w.toNat) ∧
       memHoldsLimbs32 m (base + 4) ws) := rfl

/-! ## §3  U32 frame lemma over `memHoldsLimbs32`

The U32 analogue of `Mpn.AddPrototype.memHoldsLimbs_store64_frame`: a
`store32` into a 4-byte block disjoint from each of the read limbs leaves
`memHoldsLimbs32` intact.  Proved by induction on the limb list using
the `BignumExec` U32 leaf `load32Mem_store32_disjoint` (commit
`cacca611`).

The disjointness hypothesis is stated *per limb* (`Disjoint (range
(base + 4·i) 4) (range st 4)` for each `i < ws.length`), matching how
the (future) U32 loop will discharge each peeled-limb application via
`range_shift_subset`-style reasoning.  This is the load-bearing first
rung of the U32 ladder — and it is fully provable today. -/

theorem memHoldsLimbs32_store32_frame (m : Mem) (base st : UInt64)
    (v : UInt64) (ws : List (BitVec 32))
    (hdisj : ∀ i, i < ws.length →
        MemoryModel.Disjoint (range (base + UInt64.ofNat (4 * i)) 4) (range st 4))
    (hmem : memHoldsLimbs32 m base ws) :
    memHoldsLimbs32 (Mem.store32 m st v) base ws := by
  induction ws generalizing base with
  | nil => exact True.intro
  | cons w ws ih =>
    obtain ⟨hhead, htail⟩ := hmem
    refine ⟨?_, ?_⟩
    · -- Head limb: the read at `base` is preserved because the
      -- 4-byte block at `base` is disjoint from the store's 4-byte
      -- block at `st` (the `i = 0` case of `hdisj`).
      have h0 := hdisj 0 (by simp [List.length_cons])
      have hb0 : base + UInt64.ofNat (4 * 0) = base := by
        simp only [show (4 * 0 : Nat) = 0 from rfl,
                   show (UInt64.ofNat 0 : UInt64) = 0 from rfl]
        bv_decide
      rw [hb0] at h0
      rw [load32Mem_store32_disjoint m base st v h0]
      exact hhead
    · -- Tail: apply IH at `base + 4`; index `i+1` in the original list
      -- corresponds to index `i` in the tail, with stride offset shifted
      -- by 4 bytes.
      refine ih (base + 4) ?_ htail
      intro i hi
      have hi' : i + 1 < (w :: ws).length := by
        simp [List.length_cons]; omega
      have h := hdisj (i + 1) hi'
      -- Replace `base + ofNat (4 * (i+1))` with `(base + 4) + ofNat (4 * i)`
      -- — same UInt64 by `bv_decide`-discharged ring identity.
      have heq : base + UInt64.ofNat (4 * (i + 1))
          = (base + 4) + UInt64.ofNat (4 * i) := by
        rw [show (4 * (i + 1) : Nat) = 4 * i + 4 from by ring,
            UInt64.ofNat_add,
            show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
        bv_decide
      rw [heq] at h
      exact h

/-! ## §4  The pinned residual: the U32 bridge obligation

Same shape as `Mpn.AddOpenCarryPrototype.MpnAddOpenCarryRefinesStmt`,
with:

* limb type `BitVec 32` instead of `BitVec 64`;
* stride `4` bytes instead of `8`;
* memory predicate `memHoldsLimbs32` instead of `memHoldsLimbs`;
* spec target `Mpn.GenericWidth.mpnAddNW 32` (= `Mpn.WidthInstances.mpnAdd32`)
  with `Mpn.GenericWidth.carryNat` for the final-carry encoding;
* the threaded carry is a `BitVec 64` register holding `0` or `1` —
  the pointers and `n` are still `u64`, the limb data is `u32`, and the
  carry GPR is `u32` represented as `BitVec 64` with the high half
  zero, exactly as the U64 open-coded bridge models its carry GPR.

The fuel cost shape `2 * as.length + 2` is inherited verbatim from the
U64 open-coded bridge: each iteration consumes 2 fuel for the
`Cwhile → Cif → body` unfold, plus the loop-exit cost.  The disjointness
hypotheses (`op` vs `ap`, `op` vs `bp`) at byte-size `4 * as.length`
separate the U32 output region from the U32 input regions; this is the
4-byte-stride analogue of the U64 file's `8 * as.length`. -/

/-- **Pinned residual.**  The Jasmin refinement obligation for the
    emitted U32 `mpn_add_n_oc_32`: starting from a state whose memory
    holds `as : List (BitVec 32)` at `ap`, `bs : List (BitVec 32)` at
    `bp`, with `n = |as|`, with the U32 `op` output region disjoint from
    the two U32 input regions (each `4·|as|` bytes), running `body32`
    under `emptyRegistry` lands a state whose memory at `op` holds
    `(Mpn.GenericWidth.mpnAddNW 32 as bs false).1` and whose `cf`
    register holds the final carry encoded as `BitVec 64 (carryNat …)`.

    Stated as a sorry-free `Prop`.  The U32 leaves it consumes
    (`memHoldsLimbs32`, the U32 memory-algebra lemmas
    `load32Mem_store32_same` / `load32Mem_store32_disjoint`, the U32
    frame `memHoldsLimbs32_store32_frame`) are proved above and in
    `BignumExec`'s `cacca611` section.  The remaining open work is the
    U32 analogue of `Mpn.AddOpenCarryPrototype.mpnAddN_openLoop` — the
    limb-list induction at width 32, consuming `addCarryIn32` from
    `BignumExec` (the U32 analogue of `addCarryIn`).

    Pinned in the precise shape `Mpn.PowPrototype.MpnPowJasminRefines`
    pins its outer-loop residual: a sorry-free `Prop` that the eventual
    proof will instantiate to a `theorem` without further restatement. -/
def mpnAdd32_outer_loop_obligation : Prop :=
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
        (Mpn.GenericWidth.mpnAddNW 32 as bs false).1 ∧
      s'.regs "cf" = BitVec.ofNat 64
        (Mpn.GenericWidth.carryNat (Mpn.GenericWidth.mpnAddNW 32 as bs false).2)

/-- **`MpnAdd32JasminRefinesProp`** — the bridge `Prop` for the emitted
    U32 `mpn_add_n_oc_32` body, identified with the residual
    `mpnAdd32_outer_loop_obligation`.  The actual theorem witness
    `MpnAdd32JasminRefines` lives below in §11.

    Same naming and packaging convention as
    `Mpn.PowPrototype.MpnPowJasminRefines`: an `abbrev` rather than a
    `def`, so downstream sites can write `MpnAdd32JasminRefinesProp` as
    the type when they need to refer to the bridge statement. -/
abbrev MpnAdd32JasminRefinesProp : Prop := mpnAdd32_outer_loop_obligation

/-! ## §5  Tie-in to the generic spec (`mpnAdd32 = mpnAddNW 32`)

The residual is stated in terms of `Mpn.GenericWidth.mpnAddNW 32`.  The
concrete kernel `Mpn.WidthInstances.mpnAdd32` is `mpnAddNW 32`
definitionally (`unfold mpnAdd32` ⇒ `mpnAddNW 32`), so a downstream
proof can read the residual through *either* name.  We record both
identities as named lemmas. -/

/-- `mpnAdd32` is `mpnAddNW 32` by definition (the
    `Mpn.WidthInstances.mpnAdd32` definition is *exactly*
    `Mpn.GenericWidth.mpnAddNW 32`). -/
theorem mpnAdd32_eq_generic (a b : List (BitVec 32)) (cin : Bool) :
    Mpn.WidthInstances.mpnAdd32 a b cin = Mpn.GenericWidth.mpnAddNW 32 a b cin := rfl

/-- The residual's conclusion stated using the concrete `mpnAdd32`
    name.  Pure rewriting — useful for downstream consumers that prefer
    the per-width spec. -/
theorem mpnAdd32_outer_loop_obligation_iff_mpnAdd32 :
    mpnAdd32_outer_loop_obligation ↔
    (∀ (s : BignumState) (as bs : List (BitVec 32)) (fuel : Nat),
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
          (Mpn.WidthInstances.mpnAdd32 as bs false).1 ∧
        s'.regs "cf" = BitVec.ofNat 64
          (Mpn.GenericWidth.carryNat (Mpn.WidthInstances.mpnAdd32 as bs false).2)) := by
  -- Pure unfolding: `mpnAdd32 = mpnAddNW 32` is rfl, so the two
  -- statements are definitionally equal.
  rfl

/-! ## §6  U32 ADC bridges — `addCarryIn32` matches `adcStepW 32`

The U32 analogue of `Mpn.AddPrototype.addCarryIn_sum` /
`addCarryIn_carry`: the executable `addCarryIn32` (run by `#ADC_32` and,
via the two-add idiom, by the U32 open-coded body) matches the pure
`adcStepW 32` on both the sum and the carry-out. -/

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

/-- Promote a `BitVec 32` value `w` to a `BitVec 64` by `BitVec.ofNat 64
    w.toNat`.  This is the memory encoding used by `memHoldsLimbs32`
    (via `UInt64.ofNat w.toNat`) lifted into `BitVec 64`. -/
def w64 (w : BitVec 32) : BitVec 64 := BitVec.ofNat 64 w.toNat

/-- A `w64`-encoded `BitVec 32` value masked to the low 32 bits is
    itself.  Pure `BitVec`, closed by `bv_decide` (the bit-blaster sees
    the `BitVec 32 → BitVec 64` zero-extension as identity on the low
    half). -/
theorem w64_mask (w : BitVec 32) : w64 w &&& mask32 = w64 w := by
  unfold w64 mask32
  -- Express `w64 w` as the zero-extension of `w` so `bv_decide` sees
  -- both sides as concrete `BitVec`-shape terms over `w : BitVec 32`.
  have hzx : (BitVec.ofNat 64 w.toNat) = BitVec.setWidth 64 w := by
    apply BitVec.eq_of_toNat_eq
    have hw : w.toNat < 2 ^ 32 := w.isLt
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
               Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 64),
               Nat.mod_eq_of_lt hw]
  rw [hzx]
  bv_decide

/-- `(w64 a + w64 b + (cin & 1)).toNat = a.toNat + b.toNat + (cin01)`
    when `cin01 ≤ 1` — the full unwrapped sum on a 64-bit register
    accommodates the U32 ADC without overflow. -/
theorem w64_add_sum (a b : BitVec 32) (cin01 : Nat) (hc : cin01 ≤ 1) :
    ((w64 a) + (w64 b) + (BitVec.ofNat 64 cin01)).toNat
      = a.toNat + b.toNat + cin01 := by
  unfold w64
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- ADC sum bridge at U32, on `UInt64.ofNat _.toNat` shapes: the
    sum the loop stores at the output pointer equals
    `UInt64.ofNat (adcStepW 32 a b cin).1.toNat`. -/
theorem addCarryIn32_sum_uint64 (a b : BitVec 32) (c : Bool) :
    UInt64.ofNat
      (addCarryIn32 (w64 a) (w64 b)
        (BitVec.ofNat 64 (if c then 1 else 0))).2.toNat
      = UInt64.ofNat (Mpn.GenericWidth.adcStepW 32 a b c).1.toNat := by
  -- Strategy: reduce LHS via `BitVec` algebra to
  --   `BitVec.ofNat 64 ((a.toNat + b.toNat + cin01) % 2^32)`
  -- then close via `UInt64.toNat` injection.  The `& mask32` step
  -- needs an `omega`-friendly form, so we split off the `cin01` analysis.
  set cin01 : Nat := if c then 1 else 0 with hcin01
  have hc : cin01 ≤ 1 := by rw [hcin01]; cases c <;> simp
  apply UInt64.toNat.inj
  unfold addCarryIn32 Mpn.GenericWidth.adcStepW
  -- The inner addition: in `BitVec 64`, computes `a.toNat + b.toNat + cin01`
  -- exactly (no wrap, since `a, b < 2^32` and `cin01 ≤ 1`).  The outer
  -- `& mask32` then takes that `mod 2^32`.
  have hmask_a : (w64 a) &&& mask32 = w64 a := w64_mask a
  have hmask_b : (w64 b) &&& mask32 = w64 b := w64_mask b
  rw [hmask_a, hmask_b]
  have hcin_mask : (BitVec.ofNat 64 cin01) &&& 1 = BitVec.ofNat 64 cin01 := by
    rw [hcin01]; cases c <;> bv_decide
  rw [hcin_mask]
  -- The result word in BitVec form: `((w64 a + w64 b + cin) &&& mask32).toNat`.
  have hsum := w64_add_sum a b cin01 hc
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  simp only [UInt64.toNat_ofNat', BitVec.toNat_and, mask32, hsum,
             show (0xFFFFFFFF : BitVec 64).toNat = (2 ^ 32 - 1) from by decide,
             BitVec.toNat_ofNat]
  -- Pull `&&& (2^32 - 1)` into `% 2^32` via `Nat.and_two_pow_sub_one_eq_mod`.
  rw [Nat.and_two_pow_sub_one_eq_mod (a.toNat + b.toNat + cin01) 32]

/-- ADC carry bridge at U32: the carry-out flag of `addCarryIn32` equals
    `BitVec.ofNat 64 (carryNat …)` of `adcStepW 32`'s carry-out. -/
theorem addCarryIn32_carry (a b : BitVec 32) (c : Bool) :
    (addCarryIn32 (w64 a) (w64 b)
        (BitVec.ofNat 64 (if c then 1 else 0))).1
      = BitVec.ofNat 64
          (Mpn.GenericWidth.carryNat (Mpn.GenericWidth.adcStepW 32 a b c).2) := by
  set cin01 : Nat := if c then 1 else 0 with hcin01
  have hc : cin01 ≤ 1 := by rw [hcin01]; cases c <;> simp
  apply BitVec.eq_of_toNat_eq
  unfold addCarryIn32 Mpn.GenericWidth.adcStepW Mpn.GenericWidth.carryNat
  have hmask_a : (w64 a) &&& mask32 = w64 a := w64_mask a
  have hmask_b : (w64 b) &&& mask32 = w64 b := w64_mask b
  rw [hmask_a, hmask_b]
  have hcin_mask : (BitVec.ofNat 64 cin01) &&& 1 = BitVec.ofNat 64 cin01 := by
    rw [hcin01]; cases c <;> bv_decide
  rw [hcin_mask]
  have hsum := w64_add_sum a b cin01 hc
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have habc_lt : a.toNat + b.toNat + cin01 < 2 ^ 33 := by
    have h33 : (2 : Nat) ^ 33 = 2 * 2 ^ 32 := by decide
    omega
  -- LHS: `((w64 a + w64 b + cin) >>> 32) &&& 1`.  Its toNat is
  -- `((a.toNat+b.toNat+cin01) / 2^32) &&& 1`, which is `1` iff the sum
  -- reached `2^32` (i.e. the adcStepW carry-out).
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, hsum,
             show ((1 : BitVec 64).toNat) = 1 from rfl,
             BitVec.toNat_ofNat, decide_eq_true_eq]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 1, Nat.shiftRight_eq_div_pow]
  -- Now both sides are `((a+b+cin01) / 2^32 % 2^64) % 2 = (if … then 1 else 0) % 2^64`.
  by_cases hge : a.toNat + b.toNat + cin01 ≥ 2 ^ 32
  · rw [if_pos hge]
    have hdiv : (a.toNat + b.toNat + cin01) / 2 ^ 32 = 1 := by
      have h33 : (2 : Nat) ^ 33 = 2 * 2 ^ 32 := by decide
      omega
    rw [hdiv]
  · rw [if_neg hge]
    have hdiv : (a.toNat + b.toNat + cin01) / 2 ^ 32 = 0 :=
      Nat.div_eq_of_lt (by omega)
    rw [hdiv]

/-! ## §7  U32 open-coded body bridge — two `#ADD_32` + `Olor`

The U32 loop body composes two `addCarry32` (each `#ADD_32` writes
`writeSubBundle`'s `[cf, dst]`) plus a `Olor` of the two carries.  This
matches `addCarryIn32` exactly when the threaded carry is already a low
bit. -/

/-- `addCarry32 a b = (cf, r)` with `r = ((a + b) masked to 32 bits)` and
    `cf = bit 32` of the unmasked sum.  Definitional unfold. -/
theorem addCarry32_eq (a b : BitVec 64) :
    addCarry32 a b =
      (((((a &&& mask32) + (b &&& mask32)) >>> 32) &&& 1),
       ((a &&& mask32) + (b &&& mask32)) &&& mask32) := rfl

/-- **Open-coded U32 composition = `addCarryIn32`.**  Composing
    `addCarry32 t s` (giving `(cf1, r0)`) with `addCarry32 r0 cf`
    (giving `(cf2, r)`) and taking the new carry as `cf1 ||| cf2`
    yields exactly `addCarryIn32 t s cf` — provided the threaded carry
    `cf` is already a low bit (`cf &&& 1 = cf`).  Pure `BitVec`, closed
    by `bv_decide`. -/
theorem openBody32_eq_addCarryIn32 (t s cf : BitVec 64) (hcf : cf &&& 1 = cf) :
    ((addCarry32 t s).1 ||| (addCarry32 (addCarry32 t s).2 cf).1,
      (addCarry32 (addCarry32 t s).2 cf).2)
      = addCarryIn32 t s cf := by
  unfold addCarry32 addCarryIn32 mask32
  refine Prod.ext ?_ ?_ <;> bv_decide

/-! ## §8  U32 per-iteration step lemma

The U32 analogue of `Mpn.AddOpenCarryPrototype.bignumExec_openLoopBody_step`:
one iteration of `loopBody32` (run via the straight-line interpreter)
loads `a`, `b`; computes two `addCarry32` + `Olor`; stores the (masked)
sum at `op`; advances `ap`, `bp`, `op` by 4 and decrements `n` by 1.

The threaded carry register `cf` encodes the boolean carry-in as
`BitVec.ofNat 64 (if cin then 1 else 0)` — the same shape as the U64
file.  After the iteration, `cf` holds the encoded carry-out.

We use the *unmasked* memory invariant: `load32Mem` returns
`UInt64.ofNat (head : BitVec 32).toNat` (with the high half already
zero), and the stored value `addCarryIn32 ... .2` is itself masked to
32 bits, so it equals `UInt64.ofNat (sum : BitVec 32).toNat` after
decode. -/

/-- Loading a `BitVec 32` limb from memory and decoding through
    `BitVec.ofNat 64 _.toNat` recovers the `BitVec 64` zero-extension
    `w64 w = BitVec.ofNat 64 w.toNat` (since `w.toNat < 2^32 < 2^64`). -/
theorem u32_load_roundtrip (w : BitVec 32) :
    BitVec.ofNat 64 (UInt64.ofNat w.toNat).toNat = w64 w := by
  have hw : w.toNat < 2 ^ 32 := w.isLt
  apply BitVec.eq_of_toNat_eq
  unfold w64
  simp only [BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  omega

/-- `addCarryIn32`'s result is already masked to 32 bits; the masked-by-
    `0xFFFFFFFF` reduction on the stored value is the identity. -/
theorem addCarryIn32_lo32 (a b cin : BitVec 64) :
    (addCarryIn32 a b cin).2 &&& 0xFFFFFFFF = (addCarryIn32 a b cin).2 := by
  unfold addCarryIn32 mask32
  bv_decide

/-- The `loopBody32` is straight-line (`Cassgn` / `Copn` only). -/
theorem loopBody32_straightLine : InstrR.bodyIsStraightLine loopBody32 := by
  simp only [loopBody32, load32At0, addCopn32, store32At0, ptrImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBody32` is non-control. -/
theorem loopBody32_nonControl : ∀ i ∈ loopBody32, i.isNonControl := by
  intro i hi
  simp only [loopBody32, load32At0, addCopn32, store32At0, ptrImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-- `regAddr` (defined in `MpnAddPrototype` over a `vr` U64 register) at
    register name `x` also resolves the U32 base `vr32 x` / U64 base
    `vr64 x` (all three share the same string lookup). -/
theorem resolveAddr_vr64 (s : BignumState) (x : String) :
    resolveAddr s { var := vr64 x } (.Pconst 0) = some (regAddr s x) := by
  simp only [resolveAddr, regAddr, vr64]
  norm_num

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem bignumExec_loopBody32_step (s : BignumState) (a b : BitVec 32) (cin : Bool)
    (hcf : s.regs "cf" = BitVec.ofNat 64 (if cin then 1 else 0))
    (ha : load32Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load32Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBody32 s = some s' ∧
      s'.mem = Mem.store32 s.mem (regAddr s "op")
        (UInt64.ofNat (Mpn.GenericWidth.adcStepW 32 a b cin).1.toNat) ∧
      s'.regs "cf" = BitVec.ofNat 64
        (Mpn.GenericWidth.carryNat (Mpn.GenericWidth.adcStepW 32 a b cin).2) ∧
      s'.regs "ap" = s.regs "ap" + 4 ∧
      s'.regs "bp" = s.regs "bp" + 4 ∧
      s'.regs "op" = s.regs "op" + 4 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Unfold the body, the semantic dispatchers, and the projection
  -- simp lemmas.  Mirror the U64 open-coded step exactly, swapping
  -- `vr`/`vr32`/`vr64`, `loadAt0`/`load32At0`, etc.
  simp only [loopBody32, load32At0, addCopn32, store32At0, ptrImm,
             bignumExec, execInstr, evalPExpr, pv32, pv64,
             resolveAddr_vr64, vr32, vr64,
             setReg_mem, setReg_regs, storeMem32_mem_proj, storeMem32_regs_proj,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem32_regs_proj, storeMem32_mem_proj,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, hb, Option.bind_some, bind, Option.bind] at *
  -- Fire the two U32 loads (decode `a`/`b`).
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [Option.bind_some, bind, Option.bind]
  rw [show (setReg s "t" (BitVec.ofNat 64 (UInt64.ofNat a.toNat).toNat)).regs "bp" + 0
        = s.regs "bp" from by simp only [setReg_regs]; bv_decide, setReg_mem, hb]
  simp only [Option.bind_some, bind, Option.bind]
  -- Pre-compute the round-tripped loads (the U32 path leaves them in
  -- masked-UInt64 form; we want to express them as concrete BitVec 64
  -- values via `(UInt64.ofNat a.toNat).toBitVec`).
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [setReg_regs, setReg_mem, storeMem32_mem_proj, storeMem32_regs_proj,
               regAddr, String.reduceEq, ↓reduceIte, reduceIte, hcf,
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 4 = (4 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]
  · -- Memory: the stored value `UInt64.ofNat (addCarry32_composition).2.toNat`
    -- equals `UInt64.ofNat (adcStepW 32 a b cin).1.toNat`
    -- via `openBody32_eq_addCarryIn32` + `addCarryIn32_sum_uint64`.
    have hmask : (BitVec.ofNat 64 (if cin then 1 else 0) : BitVec 64) &&& 1
        = BitVec.ofNat 64 (if cin then 1 else 0) := by cases cin <;> bv_decide
    have hopen := openBody32_eq_addCarryIn32 (w64 a) (w64 b)
      (BitVec.ofNat 64 (if cin then 1 else 0)) hmask
    have hopen2 := congrArg Prod.snd hopen
    simp only at hopen2
    -- Push the loaded-from-memory `BitVec.ofNat 64 (UInt64.ofNat a.toNat).toNat`
    -- shapes to `w64 a` (the natural form for the bridges).
    rw [u32_load_roundtrip a, u32_load_roundtrip b]
    rw [hopen2]
    -- Goal: `Mem.store32 s.mem op (UInt64.ofNat .toNat) = Mem.store32 s.mem op (UInt64.ofNat .toNat)`
    -- — congr on the stored value.
    congr 1
    exact addCarryIn32_sum_uint64 a b cin
  · -- Carry register: `(addCarry32 a b).1 ||| (addCarry32 r0 cf).1` =
    -- `BitVec.ofNat 64 (carryNat (adcStepW 32 a b cin).2)`.
    have hmask : (BitVec.ofNat 64 (if cin then 1 else 0) : BitVec 64) &&& 1
        = BitVec.ofNat 64 (if cin then 1 else 0) := by cases cin <;> bv_decide
    have hopen := openBody32_eq_addCarryIn32 (w64 a) (w64 b)
      (BitVec.ofNat 64 (if cin then 1 else 0)) hmask
    have hopen1 := congrArg Prod.fst hopen
    simp only at hopen1
    rw [u32_load_roundtrip a, u32_load_roundtrip b, hopen1,
        addCarryIn32_carry a b cin]

/-! ## §9  Range-based U32 frame lemma over `memHoldsLimbs32`

The §3 frame is stated *per-limb*.  For the loop induction we want the
*range-based* form: a `store32` at any 4-byte block disjoint from the
whole `4·|ws|`-byte limb region preserves `memHoldsLimbs32`.  This is
derivable from the per-limb form by extracting the per-`i` disjointness
from the range disjointness; alternatively, prove it directly by
induction. -/

theorem memHoldsLimbs32_store32_range_frame (m : Mem) (base st : UInt64)
    (v : UInt64) (ws : List (BitVec 32))
    (hdisj : MemoryModel.Disjoint (range st 4) (range base (4 * ws.length)))
    (hmem : memHoldsLimbs32 m base ws) :
    memHoldsLimbs32 (Mem.store32 m st v) base ws := by
  induction ws generalizing base with
  | nil => exact True.intro
  | cons w ws ih =>
    obtain ⟨hhead, htail⟩ := hmem
    refine ⟨?_, ?_⟩
    · -- Head: `[st, st+4)` is disjoint from `[base, base+4)`
      have hdisj_head : MemoryModel.Disjoint (range base 4) (range st 4) := by
        refine MemoryModel.Disjoint.symm (disjoint_mono (fun a h => h) ?_ hdisj)
        intro a ⟨j, hj, haj⟩
        exact ⟨j, by simp [List.length_cons]; omega, haj⟩
      rw [load32Mem_store32_disjoint m base st v hdisj_head]
      exact hhead
    · -- Tail: shift base by 4 and `4·ws.length` covers the tail region.
      refine ih (base + 4) ?_ htail
      refine disjoint_mono (fun a h => h) ?_ hdisj
      intro a ⟨j, hj, haj⟩
      refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
      rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
      rw [haj]; ac_rfl

/-! ## §10  The U32 loop, by induction on the limb list

Clone of `Mpn.AddOpenCarryPrototype.mpnAddN_openLoop` at limb width 32.
Each iteration peels one limb (`bignumExec_loopBody32_step`); the carry
threads through the U32 GPR `cf`; the per-iteration store is framed
against the unread `ap`/`bp` suffixes (`load32Mem_store32_disjoint`). -/

theorem mpnAddN32_openLoop :
    ∀ (as bs : List (BitVec 32)) (s : BignumState) (cin : Bool) (extra : Nat),
      as.length = bs.length →
      s.regs "cf" = BitVec.ofNat 64 (if cin then 1 else 0) →
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
        memHoldsLimbs32 s'.mem (regAddr s "op") (Mpn.GenericWidth.mpnAddNW 32 as bs cin).1 ∧
        s'.regs "cf" = BitVec.ofNat 64
          (Mpn.GenericWidth.carryNat (Mpn.GenericWidth.mpnAddNW 32 as bs cin).2) ∧
        (∀ b, MemoryModel.Disjoint (range b 4)
              (range (regAddr s "op") (4 * as.length)) →
            load32Mem s'.mem b = load32Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s cin extra _ hcf hn _ _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 32)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 0 :=
        evalPExpr_neq_zero_false s (pv64 "n")
          (by simp only [pv64, vr64, evalPExpr]; rw [hn0])
      exact bignumExecFuel_loop_exit_generic emptyRegistry extra _ loopBody32 s hcond
    · simp [Mpn.GenericWidth.mpnAddNW, memHoldsLimbs32]
    · simpa [Mpn.GenericWidth.mpnAddNW, Mpn.GenericWidth.carryNat] using! hcf
    · intro b _; rfl
  | cons a as ih =>
    intro bs s cin extra hlen hcf hn hap hbp hdoa hdob
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
      -- One U32 iteration.
      obtain ⟨s1, hs1, hs1_mem, hs1_cf, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_loopBody32_step s a b cin hcf hap_head hbp_head
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
          (UInt64.ofNat (Mpn.GenericWidth.adcStepW 32 a b cin).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      -- Frame the tail of `ap`/`bp` across the head store at `op0` —
      -- using 4-byte block disjointness vs the tail regions.
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 4) (range (regAddr s "ap" + 4) (4 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · -- `[op0, op0+4) ⊆ [op0, op0+4·(L+1))`
          obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        · -- `[ap+4, ap+4+4·L) ⊆ [ap, ap+4·(L+1))`
          obtain ⟨j, hj, hxj⟩ := h
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
      -- Disjointness for the IH (tail op-region vs. tail ap/bp-regions).
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
          (if (Mpn.GenericWidth.adcStepW 32 a b cin).2 then 1 else 0) := by
        rw [hs1_cf]; simp [Mpn.GenericWidth.carryNat]
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_mem, hs'_cf, hs'_frame⟩ :=
        ih bs s1 (Mpn.GenericWidth.adcStepW 32 a b cin).2 extra hlen' hcf1 hn1 hap1 hbp1 hdoa1 hdob1
      refine ⟨s', ?_, ?_, ?_, ?_⟩
      · -- Fuel: 2·(L+1)+3+extra = (2·L+2+extra)+3.
        have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        -- The loop guard is true via `evalPExpr_neq_zero_true` on register `n`.
        have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 1 :=
          evalPExpr_neq_zero_true s (pv64 "n") (s.regs "n")
            (by simp only [pv64, vr64, evalPExpr]) hn_ne
        refine bignumExecFuel_loop_step_generic emptyRegistry
          (2 * as.length + 2 + extra) _ loopBody32 loopBody32_straightLine
          loopBody32_nonControl s s1 s' hcond hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- Memory at op: head limb at `op0` (preserved by IH frame), tail by IH.
        rw [hmem1] at hs'_frame
        -- Op-internal separation at stride 4.
        have hsep : MemoryModel.Disjoint (range op0 4) (range (op0 + 4) (4 * as.length)) :=
          range_op_head_tail_disjoint_4 op0 as.length (by omega)
        refine ⟨?_, ?_⟩
        · -- `load32Mem s'.mem op0 = head_result`, via IH frame + read-back.
          rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
          have hread := load32Mem_store32_same s.mem op0
            (UInt64.ofNat (Mpn.GenericWidth.adcStepW 32 a b cin).1.toNat)
          rw [hread]
          -- The head of `(mpnAddNW 32 (a::as) (b::bs) cin).1` is
          -- `(adcStepW 32 a b cin).1`; and the masked-store at U32 of a
          -- value `UInt64.ofNat (sum : BitVec 32).toNat` reads back as
          -- itself (high bits already zero).
          have hsum : (Mpn.GenericWidth.adcStepW 32 a b cin).1.toNat < 2 ^ 32 :=
            (Mpn.GenericWidth.adcStepW 32 a b cin).1.isLt
          have hmask : (UInt64.ofNat (Mpn.GenericWidth.adcStepW 32 a b cin).1.toNat
              &&& 0xFFFFFFFF : UInt64)
              = UInt64.ofNat (Mpn.GenericWidth.adcStepW 32 a b cin).1.toNat := by
            apply UInt64.toNat.inj
            simp only [UInt64.toNat_and, UInt64.toNat_ofNat',
                       show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from by decide]
            rw [Nat.mod_eq_of_lt (by omega : (Mpn.GenericWidth.adcStepW 32 a b cin).1.toNat < 2 ^ 64),
                Nat.and_two_pow_sub_one_eq_mod _ 32, Nat.mod_eq_of_lt hsum]
          rw [hmask]
          -- The head of `(mpnAddNW 32 (a::as) (b::bs) cin).1` is `(adcStepW 32 a b cin).1`.
          rfl
        · -- Tail: `(mpnAddNW 32 as bs (adcStepW 32 a b cin).2).1`, from IH (op base `op0+4`).
          have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · -- Carry-out: the IH's final carry equals the chain carry-out.
        rw [hs'_cf]; simp only [Mpn.GenericWidth.mpnAddNW]
      · -- Frame: `b`-block disjoint from `range op0 (4·(L+1))` ⇒ unchanged.
        intro bb hbb
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

/-! ## §11  Assembly: `MpnAdd32JasminRefines` as a true theorem

The full U32 bridge: `body32 = [cf := 0; while (n != 0) { loopBody32 }]`.
The prelude zeroes the U32 carry register, then the loop walks the limb
arrays.  Mirror of `Mpn.AddOpenCarryPrototype.MpnAddOpenCarryRefines`. -/

theorem MpnAdd32JasminRefines_proof : mpnAdd32_outer_loop_obligation := by
  intro s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  -- Step 1: the `cf := 0` prelude.  `evalPExpr s (Pconst 0) = 0`.
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
    mpnAddN32_openLoop as bs s0 false extra hlen hcf0 hn0' hap0 hbp0 hdoa0 hdob0
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

/-! ## §12  Canonical bridge theorem

`MpnAdd32JasminRefines` is now a **proved theorem** discharging
`mpnAdd32_outer_loop_obligation`: the emitted U32 `mpn_add_n_oc_32`
Jasmin kernel refines `Mpn.GenericWidth.mpnAddNW 32` (equivalently
`Mpn.WidthInstances.mpnAdd32`) over byte memory at 4-byte stride.  The
U32 emitter is now out of the TCB. -/

theorem MpnAdd32JasminRefines : MpnAdd32JasminRefinesProp :=
  MpnAdd32JasminRefines_proof

/-! ## §13  Axiom audit -/

#print axioms body32_isCT
#print axioms mpnAddN32Fd_body
#print axioms memHoldsLimbs32_store32_frame
#print axioms mpnAdd32_eq_generic
#print axioms MpnAdd32JasminRefines

end CatCrypt.Crypto.Jasmin.Mpn.Add32Refines
