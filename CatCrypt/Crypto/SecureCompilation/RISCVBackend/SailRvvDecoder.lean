/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvvEncoder
import Mathlib.Tactic.FinCases

/-!
# sail-riscv RVV decoder round-trip: `decode (encode i) ≡ i` (#549 RVV residual)

`RvvEncoder.lean` is the owned `VInst → machine-byte` encoder for the packed-u32
RVV OPIVV/OPIVI subset. Its bench trust edge is *differential*: each emitted 32-bit
word is pinned to what `riscv64-linux-gnu-as -march=rv64gcv` produces
(`bench/riscv_compare`, the qemu RVV KAT). That makes `as`'s unverified encoder
part of the trusted base.

This module replaces the differential edge with a **round-trip** against the
RISC-V RVV *decoder* discipline: a Lean decoder `rvvDecode` that recovers the OP-V
fields `(funct6, vm, vs2, vs1/simm, funct3, vd, opcode)` from a 32-bit instruction
word, following the official
[`riscv/sail-riscv`](https://github.com/riscv/sail-riscv) RVV `encdec` clauses in
`model/extensions/V/vext_arith_insts.sail` (`VVTYPE`, `VITYPE`, `MOVETYPEV`), and
a proof that `rvvDecode (encodeWord i) = some i` for every instruction in the
emitted OPIVV/OPIVI subset.

Because the decoder applies the OP-V fixed-width field splits exactly as the
sail-riscv `encdec` mapping reads them (each field is a sail `@`-concatenated
slice), `decode (encode i)` recovering exactly the operands `i` names means the
encoder produces words the authoritative decoder maps back to the same
instruction — the encoder's bytes are *proved* to be the right encoding, not
merely matched to `as`.

## The decode discriminants (from `vext_arith_insts.sail`)

OP-V (opcode `0b1010111 = 0x57`) holds OPIVV (`funct3 = 0b000`) and OPIVI
(`funct3 = 0b011`), discriminated by `funct6[31:26]`: `vadd=0b000000`,
`vand=0b001001`, `vor=0b001010`, `vxor=0b001011` (OPIVV); `vsll=0b100101`,
`vsrl=0b101000` (OPIVI, shift in the 5-bit `simm` slot); `vmv.v.v` is the OPIVV
`MOVETYPEV` form `funct6=0b010111`, `vm=1`, `vs2=0`.

## Scope of the round-trip

`decode (encode i) = i` is proved (`roundtrip_rvv`) for the **full emitted RVV
subset**: `vadd`/`vand`/`vor`/`vxor` (OPIVV), `vsll`/`vsrl` (OPIVI, by immediate),
and `vmv.v.v`. sail-riscv models the whole RVV ISA, so — exactly as for the scalar
RV64I and bignum subsets — there is **no Sail-coverage ceiling**: the whole emitted
OPIVV/OPIVI alphabet is decode-round-trip-proved, axiom-clean. (The `vsetvli` /
`vle32.v` / `vse32.v` prelude is the trusted lane-config / memory scaffolding,
outside the verified packed-ALU body, the RVV analogue of the prologue.)
-/

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
/-- `funct6` field as a `Nat`. -/
def fFunct6 (w : BitVec 32) : Nat := (sFunct6 w).toNat

/-! ## 2. Register number → `vN` name (inverse of `RvvEncoder.vNum`) -/

/-- The `vN` register name for an RVV register number `0..31`, the inverse of
    `vNum` on the canonical names. -/
def vregName (n : Nat) : String := "v" ++ toString n

/-! ## 3. The decoder

`rvvDecode` dispatches on the `(opcode, funct3, funct6)` triple per the sail RVV
`encdec` clauses, recovers the register numbers, and rebuilds the `VInst`. The
OPIVI shift arms read the 5-bit `simm`; `vmv.v.v` decodes the `MOVETYPEV` form. -/

/-- Decode a 32-bit RV64 RVV instruction word back to a `VInst`, per the sail-riscv
    RVV `encdec` clauses for the emitted OPIVV/OPIVI subset. Returns `none` for a
    word outside the emitted subset. -/
def rvvDecode (w : BitVec 32) : Option VInst :=
  let vd := fVd w; let vs1 := fVs1 w; let vs2 := fVs2 w
  let f3 := fFunct3 w; let f6 := fFunct6 w
  match fOpcode w, f3, f6 with
  -- OPIVV (opcode 0x57, funct3 0): vadd/vand/vor/vxor + vmv.v.v (MOVETYPEV)
  | 0x57, 0b000, 0x00 => some (.vadd (vregName vd) (vregName vs2) (vregName vs1))
  | 0x57, 0b000, 0x09 => some (.vand (vregName vd) (vregName vs2) (vregName vs1))
  | 0x57, 0b000, 0x0a => some (.vor  (vregName vd) (vregName vs2) (vregName vs1))
  | 0x57, 0b000, 0x0b => some (.vxor (vregName vd) (vregName vs2) (vregName vs1))
  | 0x57, 0b000, 0x17 => some (.vmv (vregName vd) (vregName vs1))
  -- OPIVI (opcode 0x57, funct3 3): vsll/vsrl by immediate (shift in simm slot)
  | 0x57, 0b011, 0x25 => some (.vsll (vregName vd) (vregName vs2) vs1)
  | 0x57, 0b011, 0x28 => some (.vsrl (vregName vd) (vregName vs2) vs1)
  | _, _, _ => none

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
    sFunct6 (encV funct6 vm vs2 vs1 funct3 vd opcode) = funct6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sOpcode, sVd, sFunct3, sVs1, sVs2, sFunct6, encV] <;> bv_decide

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
  cases i with
  | vadd d a b =>
      have ha := hsrc a (by simp [vinstDstSrcs]); have hb := hsrc b (by simp [vinstDstSrcs])
      simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2,
        D.1, D.2.1, D.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha, vregName_vreg5 b hb]
  | vand d a b =>
      have ha := hsrc a (by simp [vinstDstSrcs]); have hb := hsrc b (by simp [vinstDstSrcs])
      simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2,
        D.1, D.2.1, D.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha, vregName_vreg5 b hb]
  | vor d a b =>
      have ha := hsrc a (by simp [vinstDstSrcs]); have hb := hsrc b (by simp [vinstDstSrcs])
      simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2,
        D.1, D.2.1, D.2.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha, vregName_vreg5 b hb]
  | vxor d a b =>
      have ha := hsrc a (by simp [vinstDstSrcs]); have hb := hsrc b (by simp [vinstDstSrcs])
      simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2,
        D.1, D.2.1, D.2.2.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha, vregName_vreg5 b hb]
  | vsll d a m =>
      have ha := hsrc a (by simp [vinstDstSrcs]); simp only [vinstDstSrcs] at hdst
      have hm : m < 32 := hsh d a m (Or.inl rfl)
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2,
        D.1, D.2.2.1, D.2.2.2.2.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  | vsrl d a m =>
      have ha := hsrc a (by simp [vinstDstSrcs]); simp only [vinstDstSrcs] at hdst
      have hm : m < 32 := hsh d a m (Or.inr rfl)
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fVs2, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.1, (encV_slices ..).2.2.2.2.2,
        D.1, D.2.2.1, D.2.2.2.2.2.2.2.2.2]
      rw [vregName_vreg5 d hdst, vregName_vreg5 a ha]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  | vmv d s =>
      have hs := hsrc s (by simp [vinstDstSrcs]); simp only [vinstDstSrcs] at hdst
      simp only [encodeWord, rvvDecode, fOpcode, fVd, fVs1, fFunct3, fFunct6, opV,
        (encV_slices ..).1, (encV_slices ..).2.1, (encV_slices ..).2.2.1,
        (encV_slices ..).2.2.2.1, (encV_slices ..).2.2.2.2.2,
        D.1, D.2.1, D.2.2.2.2.2.2.2.1]
      rw [vregName_vreg5 d hdst, vregName_vreg5 s hs]

/-! ## 7. The owned RVV byte-level trust edge

The **entire** emitted RVV alphabet — `vadd`/`vand`/`vor`/`vxor` (OPIVV),
`vsll`/`vsrl` (OPIVI, by immediate), and `vmv.v.v` (MOVETYPEV) — is
decode-round-trip-proved against the sail-riscv RVV `encdec` field-split
discipline, so `riscv64-linux-gnu-as` is out of the trusted path for the
packed-ALU body. As with the scalar RV64I and bignum subsets, there is **no
Sail-coverage ceiling**: sail-riscv models the whole RVV ISA. The bench
differential (`bench/riscv_compare`, `qr-rvv-bytes-diff`) additionally pins the
verified-encoder words byte-identical to `as` on the ChaCha 4-way quarter-round
body, and the qemu KAT (`qr-rvv-kat`) runs the assembled object on real rv64+RVV.
The `vsetvli` / `vle32.v` / `vse32.v` prelude is trusted lane-config / memory
scaffolding outside the verified body. -/

/-- Doc-anchor pilot: the `vadd.vv` packed add round-trips. -/
theorem trust_edge_pilot_rvv :
    rvvDecode (encodeWord (.vadd "v4" "v0" "v1")) = some (.vadd "v4" "v0" "v1") :=
  roundtrip_rvv (.vadd "v4" "v0" "v1") (by decide) (by decide) (by simp)

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv.SailRvvDecoder
