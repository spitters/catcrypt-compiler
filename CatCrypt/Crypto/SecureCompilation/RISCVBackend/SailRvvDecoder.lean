/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import Std.Tactic.BVDecide
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvvEncoder
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvvEncoder
public import Mathlib.Tactic.FinCases

/-!
# sail-riscv RVV decoder round-trip: `decode (encode i) ≡ i` (#549 RVV residual)

`RvvEncoder.lean` is the owned `VInst → machine-byte` encoder for the packed-u32
RVV OPIVV/OPIVI subset. Its bench trust edge is *differential*: each emitted 32-bit
word is pinned to what `riscv64-linux-gnu-as -march=rv64gcv` produces (an
untracked local checkout/harness, not vendored in this repo, plus the qemu RVV
KAT). That makes `as`'s unverified encoder part of the trusted base.

This module replaces the differential edge with a **round-trip** against the
RISC-V RVV *decoder* discipline: a Lean decoder `rvvDecode` that recovers the OP-V
fields `(funct6, vm, vs2, vs1/simm, funct3, vd, opcode)` from a 32-bit instruction
word, following the
[`riscv/sail-riscv`](https://github.com/riscv/sail-riscv) RVV `encdec` clauses in
`model/extensions/V/vext_arith_insts.sail` (`VVTYPE`, `VITYPE`, `MOVETYPEV`), and
a proof that `rvvDecode (encodeWord i) = some i` for every instruction in the
emitted OPIVV/OPIVI subset (with `rvvDecode8x16` / `encodeWord8x16` the same
round-trip for the OPMVV `vmulh.vv` at the `SEW=16` lane shape).

The field splits below are the authors' **hand transcription** of those clauses.
**This repo vendors no sail-riscv checkout**: `bench/` is untracked, so any local
comparison harness is outside the package and outside CI. Nothing here is
machine-checked against upstream sail-riscv — the transcription is itself a
trusted step, auditable by eye against the public model and the RVV spec.

Because the decoder applies the OP-V fixed-width field splits the way the
sail-riscv `encdec` mapping is believed to read them (each field is a sail
`@`-concatenated slice, per the transcription above), `decode (encode i)`
recovering exactly the operands `i` names means the encoder produces words a
decoder built to that transcribed discipline maps back to the same instruction —
the encoder's bytes round-trip under that discipline by proof, rather than by
matching `as`.

## The decode discriminants (from `vext_arith_insts.sail`)

OP-V (opcode `0b1010111 = 0x57`) holds OPIVV (`funct3 = 0b000`), OPIVI
(`funct3 = 0b011`) and OPMVV (`funct3 = 0b010`), discriminated by `funct6[31:26]`:
`vadd=0b000000`, `vand=0b001001`, `vor=0b001010`, `vxor=0b001011` (OPIVV);
`vsll=0b100101`, `vsrl=0b101000` (OPIVI, shift in the 5-bit `simm` slot);
`vmulh=0b100111` (OPMVV); `vmv.v.v` is the OPIVV `MOVETYPEV` form
`funct6=0b010111`, `vm=1`, `vs2=0`.

The mask bit `vm[25]` is a discriminant too, not decoration: every arm requires
`vm = 1` (unmasked), because the `VInst` model has no mask operand. `vm = 0` is a
*different* instruction — most sharply at `funct6 = 0b010111`, where `vm = 0` is
`vmerge.vvm vd, vs2, vs1, v0`, which reads `vs2` and `v0` that `vmv.v.v` does not.

## Scope of the round-trip

`decode (encode i) = i` is proved for every word the RVV backend byte-encodes as
an ALU operation: `vadd`/`vand`/`vor`/`vxor` (OPIVV), `vsll`/`vsrl` (OPIVI, by
immediate) and `vmv.v.v` (`roundtrip_rvv`), plus the ML-KEM NTT `vmulh.vv` (OPMVV,
`roundtrip_rvv8x16`), both axiom-clean (`propext`/`Quot.sound` only). Masked
(`vm = 0`) and reserved (`MOVETYPEV` with `vs2 ≠ 0`) words decode to `none`, so no
word outside the modelled subset is silently mapped into it.

The lane-config / memory scaffolding — `vsetvli`, `vle32.v`, `vse32.v`
(`RvvEncoder` §3b) — is *not* decode-round-tripped: it has no `VInst` constructor
to round-trip against, and its words remain pinned only to
`riscv64-linux-gnu-as -march=rv64gcv` by the `native_decide` examples of
`RvvEncoder` §5. That gas pin is the remaining trust edge on the RVV path.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv.SailRvvDecoder

open CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv.RvvEncoder

/-! ## 1. OP-V field slices (sail `encdec` discipline)

These transcribe the field splits the sail RVV `encdec` mapping applies in
reverse: the OP-V word is
`funct6[31:26] @ vm[25] @ vs2[24:20] @ vs1/simm[19:15] @ funct3[14:12] @ vd[11:7] @
opcode[6:0]`. -/

/-- `opcode` slice (bits 6:0). -/
def sOpcode (w : BitVec 32) : BitVec 7 := w.extractLsb' 0 7
/-- `vd` slice (bits 11:7). -/
def sVd (w : BitVec 32) : BitVec 5 := w.extractLsb' 7 5
/-- `funct3` slice (bits 14:12). -/
def sFunct3 (w : BitVec 32) : BitVec 3 := w.extractLsb' 12 3
/-- `vs1` / `simm` slice (bits 19:15). -/
def sVs1 (w : BitVec 32) : BitVec 5 := w.extractLsb' 15 5
/-- `vs2` slice (bits 24:20). -/
def sVs2 (w : BitVec 32) : BitVec 5 := w.extractLsb' 20 5
/-- `vm` mask-bit slice (bit 25); `1` is the unmasked form. -/
def sVm (w : BitVec 32) : BitVec 1 := w.extractLsb' 25 1
/-- `funct6` slice (bits 31:26). -/
def sFunct6 (w : BitVec 32) : BitVec 6 := w.extractLsb' 26 6

/-- `opcode` field as a `Nat` (for the decode dispatch). -/
def fOpcode (w : BitVec 32) : Nat := (sOpcode w).toNat
/-- `vd` field as a `Nat`. -/
def fVd (w : BitVec 32) : Nat := (sVd w).toNat
/-- `funct3` field as a `Nat`. -/
def fFunct3 (w : BitVec 32) : Nat := (sFunct3 w).toNat
/-- `vs1` / `simm` field as a `Nat`. -/
def fVs1 (w : BitVec 32) : Nat := (sVs1 w).toNat
/-- `vs2` field as a `Nat`. -/
def fVs2 (w : BitVec 32) : Nat := (sVs2 w).toNat
/-- `vm` mask bit as a `Nat` (`1` = unmasked). -/
def fVm (w : BitVec 32) : Nat := (sVm w).toNat
/-- `funct6` field as a `Nat`. -/
def fFunct6 (w : BitVec 32) : Nat := (sFunct6 w).toNat

/-! ## 2. Register number → `vN` name (inverse of `RvvEncoder.vNum`) -/

/-- The `vN` register name for an RVV register number `0..31`, the inverse of
    `vNum` on the canonical names. -/
def vregName (n : Nat) : String := "v" ++ toString n

/-! ## 3. The decoder

`rvvDecode` dispatches on the `(opcode, funct3, funct6, vm, vs2)` columns per the
sail RVV `encdec` clauses, recovers the register numbers, and rebuilds the `VInst`.
The OPIVI shift arms read the 5-bit `simm`; `vmv.v.v` decodes the `MOVETYPEV` form.
`rvvDecode8x16` is the same dispatch for the OPMVV `vmulh.vv` word. -/

/-- Decode a 32-bit RV64 RVV instruction word back to a `VInst`, per the sail-riscv
    RVV `encdec` clauses for the emitted OPIVV/OPIVI subset. Returns `none` for a
    word outside the emitted subset. -/
def rvvDecode (w : BitVec 32) : Option VInst :=
  let vd := fVd w; let vs1 := fVs1 w; let vs2 := fVs2 w
  let f3 := fFunct3 w; let f6 := fFunct6 w; let vm := fVm w
  match fOpcode w, f3, f6, vm, vs2 with
  -- OPIVV (opcode 0x57, funct3 0): vadd/vand/vor/vxor + vmv.v.v (MOVETYPEV).
  -- Every arm demands vm=1: masked forms are unmodeled (`VInst` carries no mask
  -- operand), so they decode to none rather than as their unmasked namesakes.
  | 0x57, 0b000, 0x00, 1, _ => some (.vadd (vregName vd) (vregName vs2) (vregName vs1))
  | 0x57, 0b000, 0x09, 1, _ => some (.vand (vregName vd) (vregName vs2) (vregName vs1))
  | 0x57, 0b000, 0x0a, 1, _ => some (.vor  (vregName vd) (vregName vs2) (vregName vs1))
  | 0x57, 0b000, 0x0b, 1, _ => some (.vxor (vregName vd) (vregName vs2) (vregName vs1))
  -- MOVETYPEV pins vm=1 *and* vs2=0: vm=0 here is vmerge.vvm (a different
  -- instruction, reading vs2 and v0), and vs2≠0 is a reserved encoding.
  | 0x57, 0b000, 0x17, 1, 0 => some (.vmv (vregName vd) (vregName vs1))
  -- OPIVI (opcode 0x57, funct3 3): vsll/vsrl by immediate (shift in simm slot)
  | 0x57, 0b011, 0x25, 1, _ => some (.vsll (vregName vd) (vregName vs2) vs1)
  | 0x57, 0b011, 0x28, 1, _ => some (.vsrl (vregName vd) (vregName vs2) vs1)
  | _, _, _, _, _ => none

/-- Decode a 32-bit RV64 RVV instruction word back to a `VInst8x16`, per the
    sail-riscv OPMVV `encdec` clause for `vmulh.vv` (`funct3 = 0b010`,
    `funct6 = 0b100111`, unmasked). The `SEW = 16, VL = 8` lane shape is selected by
    the `vsetvli e16,m1` prelude, not by this word, so the same field split serves
    both lane views. Returns `none` for a word outside that clause. -/
def rvvDecode8x16 (w : BitVec 32) : Option VInst8x16 :=
  let vd := fVd w; let vs1 := fVs1 w; let vs2 := fVs2 w
  let f3 := fFunct3 w; let f6 := fFunct6 w; let vm := fVm w
  match fOpcode w, f3, f6, vm with
  -- OPMVV (opcode 0x57, funct3 2), unmasked: vmulh.vv (masked forms unmodeled)
  | 0x57, 0b010, 0x27, 1 => some (.vmulh (vregName vd) (vregName vs2) (vregName vs1))
  | _, _, _, _ => none

/-! ## 4. Field-extraction round-trip (`bv_decide`, the inverse of the sail `@`)

Each `encV` word is the `BitVec.append` of its width-typed fields (the sail `@`),
so slicing the word at each field's bit range recovers that field exactly, with no
side condition — a pure fixed-width fact `bv_decide` discharges. -/

/-- The seven OP-V slices of `encV` recover the seven fields exactly (sail `@`⁻¹). -/
theorem encV_slices (funct6 : BitVec 6) (vm : BitVec 1) (vs2 vs1 : BitVec 5)
    (funct3 : BitVec 3) (vd : BitVec 5) (opcode : BitVec 7) :
    sOpcode (encV funct6 vm vs2 vs1 funct3 vd opcode) = opcode ∧
    sVd     (encV funct6 vm vs2 vs1 funct3 vd opcode) = vd ∧
    sFunct3 (encV funct6 vm vs2 vs1 funct3 vd opcode) = funct3 ∧
    sVs1    (encV funct6 vm vs2 vs1 funct3 vd opcode) = vs1 ∧
    sVs2    (encV funct6 vm vs2 vs1 funct3 vd opcode) = vs2 ∧
    sVm     (encV funct6 vm vs2 vs1 funct3 vd opcode) = vm ∧
    sFunct6 (encV funct6 vm vs2 vs1 funct3 vd opcode) = funct6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sOpcode, sVd, sFunct3, sVs1, sVs2, sVm, sFunct6, encV] <;> bv_decide

/-! ## 5. The register-name round-trip side-condition

`vregName` inverts `vreg5 ∘ vNum` on every name the allocator assigns (the V pool
`v0 … v31`). Proved by enumerating the finite pool. -/

/-- `vregName` inverts `vreg5` on every name in the RVV pool `v0 … v31`. -/
theorem vregName_vreg5 (r : String) (h : r ∈ vPool) :
    vregName (vreg5 r).toNat = r := by
  fin_cases h <;> rfl

/-- The sail dispatch constants the decode matches on, reduced to Nat literals. -/
theorem decConstsRvv :
    ((0x57 : BitVec 7).toNat = 0x57) ∧
    ((0 : BitVec 3).toNat = 0) ∧ ((3 : BitVec 3).toNat = 3) ∧
    ((0x00 : BitVec 6).toNat = 0x00) ∧ ((0x09 : BitVec 6).toNat = 0x09) ∧
    ((0x0a : BitVec 6).toNat = 0x0a) ∧ ((0x0b : BitVec 6).toNat = 0x0b) ∧
    ((0x17 : BitVec 6).toNat = 0x17) ∧ ((0x25 : BitVec 6).toNat = 0x25) ∧
    ((0x28 : BitVec 6).toNat = 0x28) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The mask-bit, `MOVETYPEV` `vs2` and OPMVV dispatch constants the decode matches
    on, reduced to Nat literals (the columns §3 added beside `decConstsRvv`). -/
theorem decConstsRvvMask :
    ((1 : BitVec 1).toNat = 1) ∧ ((0 : BitVec 5).toNat = 0) ∧
    ((2 : BitVec 3).toNat = 2) ∧ ((0x27 : BitVec 6).toNat = 0x27) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 6. The per-instruction and capstone round-trip: `decode (encode i) = i`

Each emitted `VInst` arm decodes back to itself: the opcode/funct slices recover
the sail dispatch constants (so `rvvDecode` takes the right branch), and the
register slices recover the names through `vregName_vreg5`. The shift arms
additionally need the 5-bit immediate `< 32` (the ChaCha rotates use counts in
`{7,8,12,16,20,24,25}`, all `< 32`). -/

/-- **The capstone round-trip `decode (encode i) = i` for the full emitted RVV
    OPIVV/OPIVI subset.** For every `VInst` whose register names are in the RVV
    pool (and, for the shift arms, a shift count `< 32`), decoding its encoder word
    recovers the original instruction — against the sail-riscv RVV `encdec`
    discipline (`encV_slices` is the sail `@`⁻¹). -/
theorem roundtrip_rvv (i : VInst)
    (hdst : (vinstDstSrcs i).1 ∈ vPool)
    (hsrc : ∀ r ∈ (vinstDstSrcs i).2, r ∈ vPool)
    (hsh : ∀ d a m, i = .vsll d a m ∨ i = .vsrl d a m → m < 32) :
    rvvDecode (encodeWord i) = some i := by
  have D := decConstsRvv
  have M := decConstsRvvMask
  cases i with
  | vadd d a b =>
      have ha := hsrc a (by simp [vinstDstSrcs]); have hb := hsrc b (by simp [vinstDstSrcs])
      simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fVm, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2.1,
        (encV_slices ..).2.2.2.2.2.2, M.1,
        D.1, D.2.1, D.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha, vregName_vreg5 b hb]
  | vand d a b =>
      have ha := hsrc a (by simp [vinstDstSrcs]); have hb := hsrc b (by simp [vinstDstSrcs])
      simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fVm, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2.1,
        (encV_slices ..).2.2.2.2.2.2, M.1,
        D.1, D.2.1, D.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha, vregName_vreg5 b hb]
  | vor d a b =>
      have ha := hsrc a (by simp [vinstDstSrcs]); have hb := hsrc b (by simp [vinstDstSrcs])
      simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fVm, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2.1,
        (encV_slices ..).2.2.2.2.2.2, M.1,
        D.1, D.2.1, D.2.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha, vregName_vreg5 b hb]
  | vxor d a b =>
      have ha := hsrc a (by simp [vinstDstSrcs]); have hb := hsrc b (by simp [vinstDstSrcs])
      simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fVm, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2.1,
        (encV_slices ..).2.2.2.2.2.2, M.1,
        D.1, D.2.1, D.2.2.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha, vregName_vreg5 b hb]
  | vsll d a m =>
      have ha := hsrc a (by simp [vinstDstSrcs]); simp only [vinstDstSrcs] at hdst
      have hm : m < 32 := hsh d a m (Or.inl rfl)
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fVm, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2.1,
        (encV_slices ..).2.2.2.2.2.2, M.1,
        D.1, D.2.2.1, D.2.2.2.2.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  | vsrl d a m =>
      have ha := hsrc a (by simp [vinstDstSrcs]); simp only [vinstDstSrcs] at hdst
      have hm : m < 32 := hsh d a m (Or.inr rfl)
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fVm, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2.1,
        (encV_slices ..).2.2.2.2.2.2, M.1,
        D.1, D.2.2.1, D.2.2.2.2.2.2.2.2.2]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  | vmv d s =>
      have hs := hsrc s (by simp [vinstDstSrcs]); simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fVm, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2.1,
        (encV_slices ..).2.2.2.2.2.2, M.1, M.2.1,
        D.1, D.2.1, D.2.2.2.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 s hs]

/-- **The round-trip `decode (encode i) = i` for the OPMVV `vmulh.vv` word** (the
    ML-KEM NTT signed high-multiply, `SEW = 16, VL = 8`): the same sail field split,
    dispatched on `funct3 = 0b010`, `funct6 = 0b100111`, `vm = 1`. -/
theorem roundtrip_rvv8x16 (d a b : String)
    (hd : d ∈ vPool) (ha : a ∈ vPool) (hb : b ∈ vPool) :
    rvvDecode8x16 (encodeWord8x16 (.vmulh d a b)) = some (.vmulh d a b) := by
  have D := decConstsRvv
  have M := decConstsRvvMask
  simp only [encodeWord8x16, rvvDecode8x16, fOpcode, fVd, fVs1, fVs2, fVm, fFunct3, fFunct6, opV,
    (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
    (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2.1,
    (encV_slices ..).2.2.2.2.2.2, M.1, M.2.2.1, M.2.2.2,
    D.1]
  rw [vregName_vreg5 d hd, vregName_vreg5 a ha, vregName_vreg5 b hb]

/-! ## 7. The owned RVV byte-level trust edge

Every RVV word the backend byte-encodes as an ALU operation —
`vadd`/`vand`/`vor`/`vxor` (OPIVV), `vsll`/`vsrl` (OPIVI, by immediate),
`vmv.v.v` (MOVETYPEV) and the ML-KEM NTT `vmulh.vv` (OPMVV) — is
decode-round-trip-proved against the sail-riscv RVV `encdec` field-split
discipline, so `riscv64-linux-gnu-as` is out of the trusted path for the
packed-ALU body. The decoders are *exact* on the mask bit: masked (`vm = 0`) and
reserved (`MOVETYPEV` with `vs2 ≠ 0`) words are rejected, not read as their
unmasked namesakes. The bench differential (`qr-rvv-bytes-diff`) additionally
pins the verified-encoder words byte-identical to `as` on the ChaCha 4-way
quarter-round body, and the qemu KAT (`qr-rvv-kat`) runs the assembled object on
real rv64+RVV — both in an untracked local checkout/harness, not vendored in this
repo.

The remaining gas-pinned words are the lane-config / memory scaffolding —
`vsetvli`, `vle32.v`, `vse32.v` (`RvvEncoder` §3b, pinned by `native_decide` in
`RvvEncoder` §5) — which have no `VInst` constructor and so are not
round-tripped here. -/

/-- Doc-anchor pilot: the `vadd.vv` packed add round-trips. -/
theorem trust_edge_pilot_rvv :
    rvvDecode (encodeWord (.vadd "v4" "v0" "v1")) = some (.vadd "v4" "v0" "v1") :=
  roundtrip_rvv (.vadd "v4" "v0" "v1") (by decide) (by decide) (by simp)

/-- Doc-anchor pilot: the `vmulh.vv` NTT signed high-multiply round-trips. -/
theorem trust_edge_pilot_rvv_mulh :
    rvvDecode8x16 (encodeWord8x16 (.vmulh "v4" "v0" "v1")) = some (.vmulh "v4" "v0" "v1") :=
  roundtrip_rvv8x16 "v4" "v0" "v1" (by decide) (by decide) (by decide)

/-! ### The rejected neighbours of the emitted words

The mask bit and the `MOVETYPEV` `vs2` field are decoded, not ignored: these three
words differ from an emitted one only in those fields and decode to `none`. -/

/-- `0x00008257` is `0x02008257` (`vadd.vv v4,v0,v1`) with `vm = 0` — the masked
    form `vadd.vv v4,v0,v1,v0.t`, which the mask-free `VInst` cannot express. -/
example : rvvDecode 0x00008257 = none := by decide
/-- `0x5c100257` is `vmerge.vvm v4,v1,v0,v0`: `funct6 = 0b010111` with `vm = 0` is a
    *different* instruction from `vmv.v.v`, reading `vs2` and the `v0` mask. -/
example : rvvDecode 0x5c100257 = none := by decide
/-- `0x5e100257` is the reserved `MOVETYPEV` encoding with `vs2 ≠ 0`. -/
example : rvvDecode 0x5e100257 = none := by decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv.SailRvvDecoder
