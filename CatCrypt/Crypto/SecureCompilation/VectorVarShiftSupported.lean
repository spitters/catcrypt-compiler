/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
public meta import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
public import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction

/-!
# The per-lane vector variable shift `VPSLLVQ` / `VPSRLVQ` on the owned emit path

A *per-lane* vector variable shift shifts each lane of its data operand by that
lane's own count, taken from the corresponding lane of a second vector operand.
On the 128-bit XMM carrier at a 64-bit lane these are `VPSLLVQ` and `VPSRLVQ`,
the `jasminDialect` ops `vsimd (.varShift .shl 64)` / `vsimd (.varShift .shr 64)`
with denotation `JasminDialect.simdVarShiftW`.

This is the vector counterpart of the *scalar* register-amount shift studied in
`VarShiftGoldenPath.lean`, and the two sit on different emit routes:

* the scalar `regArith .shr 64` / `.shl 64` rides the `ScalarLinDeBruijn`
  flattening front, whose legality predicate is
  `ScalarLinDeBruijn.SupportedOp` over `reg 64` expressions — the variable
  scalar shifts are excluded from it (`VarShift.varShr_not_supported` /
  `varShl_not_supported`), and this file does not change that;
* the vector `vsimd (.varShift bop 64)` returns `reg 128`, so it lies outside
  the scalar front's type domain entirely. Its emit route is the owned vsimd
  route `VsimdAsmPrint.renderVsimdInstr` (AT&T text) and
  `VsimdByteEncoder.encodeVsimdInst` (VEX machine bytes). Sections 3 and 4
  below are the membership statements for that route.

## Constant-time classification

The count operand of `VPSLLVQ`/`VPSRLVQ` is classified **public** here, in two
independent senses, both machine-checked below:

1. *Op classification.* `JasminCTByConstruction.jasminOpAddrSurface` is `false`
   on `vsimd (.varShift bop laneW)` (`varShift_no_addr_surface`): the op is
   straight-line dataflow, with no data-indexed memory access, so a `Com`
   binding it is admitted into the index-free CT-by-construction fragment
   (`vpsllvqXmmCom_ct`, `vpsrlvqXmmCom_ct`).
2. *Operand classification.* The kernels of §2b take their count vector from a
   `regConst 128 n` binding — a materialised compile-time immediate. The shift
   amount is therefore public **by construction**: it is a program constant, not
   derived from any input (`vpsllvqImmCom_denote`, `vpsllvqImmCom_ct`). This is
   the form the `vpsrlvq | vpsllvq | vporq` rotate decomposition takes wherever
   this repository uses it, where the two counts are the cipher's fixed rotation
   distance `k` and `64 - k`.

Sense 1 is the weaker, unconditional statement; sense 2 is the discipline the
kernels follow, and is what a reviewer should check when a count vector is
computed rather than materialised.

## Main results

* `simdVarShift64_lane` — lane `k` of `simdVarShiftW bop 64 a b` is `bop.apply`
  of lane `k` of `a` and lane `k` of `b`: each lane shifts by its own count.
* `vpsllvqXmmCom_denote` / `vpsrlvqXmmCom_denote` — the one-op `Com`s denote
  `simdVarShiftW .shl 64` / `.shr 64`.
* `vpsllvqXmmCom_lane` / `vpsrlvqXmmCom_lane` — lane `k` of the kernel's
  denotation is the 64-bit shift of lane `k` of the data by lane `k` of the
  counts.
* `vpsllvqImmCom_denote` — the public-amount kernel denotes the per-lane shift
  by the materialised immediate.
* `vpsllvq_mnemonic` / `vpsrlvq_mnemonic` and `vpsllvq_att_line` /
  `vpsrlvq_att_line` — the printer arm: the op renders as the three-operand
  AT&T line `vpsllvq %xmmB, %xmmA, %xmmD`.
* `vpsllvq_bytes` / `vpsrlvq_bytes` — the encoder arm: the op encodes as
  `VEX.128.66.0F38.W1 47 /r` and `… 45 /r`.
* `varShift_no_addr_surface`, `vpsllvqXmmCom_ct`, `vpsrlvqXmmCom_ct`,
  `vpsllvqImmCom_ct` — the CT classification above.
* `simdVarShift32_lane` — the four-lane 32-bit counterpart of
  `simdVarShift64_lane`.
* `vpsllvd_mnemonic` / `vpsrlvd_mnemonic` and `vpsllvd_att_line` /
  `vpsrlvd_att_line` — the printer arm for the 32-bit lane: `vpsllvd` /
  `vpsrlvd`.
* `vpsllvd_bytes` / `vpsrlvd_bytes` — the encoder arm for the 32-bit lane,
  `VEX.128.66.0F38.W0 47 /r` / `… 45 /r`, the `VEX.W = 0` counterpart of the
  64-bit arm.

The `#guard`s pin the concrete rendered lines and byte strings of the kernels.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VectorVarShift

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt (encVex3)
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction

/-! ## 1. Per-lane semantics of the 64-bit-lane variable shift

`simdVarShiftW bop 64` splits both operands into two 64-bit lanes and applies
`bop` lane-wise, the second lane operand being that lane's shift count. The
theorem below is the extraction law: reading lane `k` back off the packed result
gives exactly the lane-wise operation. -/

/-- **Per-lane law.** Lane `k` (the `[64k, 64k+64)` slice) of the 128-bit
    two-lane variable shift `simdVarShiftW bop 64 a b` is `bop.apply` of lane `k`
    of `a` and lane `k` of `b`. For `bop = .shl` / `.shr` this says each 64-bit
    lane is shifted by its own count, which is what distinguishes `VPSLLVQ` /
    `VPSRLVQ` from the uniform-count packed shift. The lane operation is left
    abstract, so the OR-of-shifted-chunks packing is the only thing reduced. -/
theorem simdVarShift64_lane (bop : JasminBinOp) (a b : BitVec 128) (k : Fin 2) :
    BitVec.extractLsb' (64 * k.val) 64 (simdVarShiftW bop 64 a b)
      = bop.apply (BitVec.extractLsb' (64 * k.val) 64 a)
                  (BitVec.extractLsb' (64 * k.val) 64 b) := by
  fin_cases k <;> cases bop <;>
    simp only [simdVarShiftW, List.range, List.range.loop, List.foldl, JasminBinOp.apply] <;>
    bv_decide

/-- Lane `k` of `VPSLLVQ`: lane `k` of the data shifted left by the `.toNat` of
    lane `k` of the counts. -/
theorem simdVarShift64_shl_lane (a b : BitVec 128) (k : Fin 2) :
    BitVec.extractLsb' (64 * k.val) 64 (simdVarShiftW .shl 64 a b)
      = BitVec.extractLsb' (64 * k.val) 64 a
          <<< (BitVec.extractLsb' (64 * k.val) 64 b).toNat :=
  simdVarShift64_lane .shl a b k

/-- Lane `k` of `VPSRLVQ`: lane `k` of the data shifted right by the `.toNat` of
    lane `k` of the counts. -/
theorem simdVarShift64_shr_lane (a b : BitVec 128) (k : Fin 2) :
    BitVec.extractLsb' (64 * k.val) 64 (simdVarShiftW .shr 64 a b)
      = BitVec.extractLsb' (64 * k.val) 64 a
          >>> (BitVec.extractLsb' (64 * k.val) 64 b).toNat :=
  simdVarShift64_lane .shr a b k

/-! ## 2. The `Com jasminDialect` kernels

Two one-op programs over the context `[data, counts]`, each a single
`vsimd (.varShift _ 64)` binding on the 128-bit XMM carrier. -/

/-- The variable-shift input context: `[data, counts]`, each `reg 128`. The data
    register is `#0`, the per-lane count register is `#1`. -/
abbrev varShiftCtx : Ctxt jasminDialect := [JasminTy.reg 128, JasminTy.reg 128]

/-- A valuation of `varShiftCtx` from a data vector and a count vector. -/
def varShiftVal (a b : BitVec 128) : Ctxt.Valuation varShiftCtx :=
  .cons a (.cons b .nil)

/-- `VPSLLVQ`: the single-op `Com` `out := vpsllvq(data, counts)` on the 128-bit
    XMM carrier at a 64-bit lane. -/
def vpsllvqXmmCom : Com jasminDialect varShiftCtx (JasminTy.reg 128) :=
  .var (.mk (.vsimd (.varShift .shl 64)) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- `VPSRLVQ`: the single-op `Com` `out := vpsrlvq(data, counts)` on the 128-bit
    XMM carrier at a 64-bit lane. -/
def vpsrlvqXmmCom : Com jasminDialect varShiftCtx (JasminTy.reg 128) :=
  .var (.mk (.vsimd (.varShift .shr 64)) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- **Denotation pin.** `vpsllvqXmmCom` on `[a, b]` denotes
    `simdVarShiftW .shl 64 a b`. -/
theorem vpsllvqXmmCom_denote (a b : BitVec 128) :
    vpsllvqXmmCom.denote (varShiftVal a b) = simdVarShiftW .shl 64 a b := rfl

/-- **Denotation pin.** `vpsrlvqXmmCom` on `[a, b]` denotes
    `simdVarShiftW .shr 64 a b`. -/
theorem vpsrlvqXmmCom_denote (a b : BitVec 128) :
    vpsrlvqXmmCom.denote (varShiftVal a b) = simdVarShiftW .shr 64 a b := rfl

/-- **The `VPSLLVQ` kernel, per lane.** Lane `k` of the kernel's denotation is
    lane `k` of the data shifted left by lane `k` of the counts. -/
theorem vpsllvqXmmCom_lane (a b : BitVec 128) (k : Fin 2) :
    BitVec.extractLsb' (64 * k.val) 64 (vpsllvqXmmCom.denote (varShiftVal a b))
      = BitVec.extractLsb' (64 * k.val) 64 a
          <<< (BitVec.extractLsb' (64 * k.val) 64 b).toNat := by
  rw [vpsllvqXmmCom_denote]; exact simdVarShift64_shl_lane a b k

/-- **The `VPSRLVQ` kernel, per lane.** Lane `k` of the kernel's denotation is
    lane `k` of the data shifted right by lane `k` of the counts. -/
theorem vpsrlvqXmmCom_lane (a b : BitVec 128) (k : Fin 2) :
    BitVec.extractLsb' (64 * k.val) 64 (vpsrlvqXmmCom.denote (varShiftVal a b))
      = BitVec.extractLsb' (64 * k.val) 64 a
          >>> (BitVec.extractLsb' (64 * k.val) 64 b).toNat := by
  rw [vpsrlvqXmmCom_denote]; exact simdVarShift64_shr_lane a b k

/-! ## 2b. The public-amount kernels: the count vector is a materialised immediate

The count operand is a program constant here: a `regConst 128 n` binding
supplies the whole count vector, so the shift amount depends on no input. This
is the operand-level CT classification of §"Constant-time classification". -/

/-- `VPSLLVQ` with a materialised count vector: `counts := const n` followed by
    `out := vpsllvq(data, counts)`, over the single-input context `[data]`. -/
def vpsllvqImmCom (n : Nat) : Com jasminDialect [JasminTy.reg 128] (JasminTy.reg 128) :=
  .var (.mk (.regConst 128 n) rfl .nil)
    (.var (.mk (.vsimd (.varShift .shl 64)) rfl (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- `VPSRLVQ` with a materialised count vector. -/
def vpsrlvqImmCom (n : Nat) : Com jasminDialect [JasminTy.reg 128] (JasminTy.reg 128) :=
  .var (.mk (.regConst 128 n) rfl .nil)
    (.var (.mk (.vsimd (.varShift .shr 64)) rfl (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- **Public-amount denotation pin.** `vpsllvqImmCom n` on `[a]` denotes the
    per-lane left shift of `a` by the lanes of the constant `BitVec.ofNat 128 n`.
    The amount is a compile-time constant, hence public by construction. -/
theorem vpsllvqImmCom_denote (n : Nat) (a : BitVec 128) :
    (vpsllvqImmCom n).denote (.cons a .nil)
      = simdVarShiftW .shl 64 a (BitVec.ofNat 128 n) := rfl

/-- **Public-amount denotation pin.** `vpsrlvqImmCom n` on `[a]` denotes the
    per-lane right shift of `a` by the lanes of the constant
    `BitVec.ofNat 128 n`. -/
theorem vpsrlvqImmCom_denote (n : Nat) (a : BitVec 128) :
    (vpsrlvqImmCom n).denote (.cons a .nil)
      = simdVarShiftW .shr 64 a (BitVec.ofNat 128 n) := rfl

/-! ## 3. Printer membership: the owned AT&T arm

`VsimdAsmPrint.SimdOp.attMnemonic` and `renderVsimdInstr` carry the per-lane
variable shifts. The theorems below are the membership statements — the printer
produces a real three-operand VEX line, not the fragment-boundary
`# <unsupported …>` comment. -/

/-- The AT&T mnemonic of the 64-bit-lane per-lane left shift is `vpsllvq`. -/
theorem vpsllvq_mnemonic : SimdOp.attMnemonic (.varShift .shl 64) = "vpsllvq" := rfl

/-- The AT&T mnemonic of the 64-bit-lane per-lane right shift is `vpsrlvq`. -/
theorem vpsrlvq_mnemonic : SimdOp.attMnemonic (.varShift .shr 64) = "vpsrlvq" := rfl

/-- **`VPSLLVQ` printer arm.** The op takes the three-operand VEX form, rendered
    in AT&T operand order `op src2, src1, dst`, for any register assignment —
    it is not routed to the fragment-boundary comment. -/
theorem vpsllvq_att_line (alloc : XAlloc) (dst a b : String) :
    renderVsimdInstr alloc (.varShift .shl 64) dst a b
      = "\t" ++ SimdOp.attMnemonic (.varShift .shl 64) ++ " " ++ xmmReg alloc b
          ++ ", " ++ xmmReg alloc a ++ ", " ++ xmmReg alloc dst := rfl

/-- **`VPSRLVQ` printer arm.** The op takes the three-operand VEX form, rendered
    in AT&T operand order `op src2, src1, dst`. -/
theorem vpsrlvq_att_line (alloc : XAlloc) (dst a b : String) :
    renderVsimdInstr alloc (.varShift .shr 64) dst a b
      = "\t" ++ SimdOp.attMnemonic (.varShift .shr 64) ++ " " ++ xmmReg alloc b
          ++ ", " ++ xmmReg alloc a ++ ", " ++ xmmReg alloc dst := rfl

/-- A three-register assignment for the pins below: data in `%xmm0`, counts in
    `%xmm1`, destination in `%xmm2`. -/
def demoAlloc : XAlloc := [("d", "%xmm2"), ("a", "%xmm0"), ("b", "%xmm1")]

-- The two per-lane variable shifts print as real three-operand AT&T lines.
#guard renderVsimdInstr demoAlloc (.varShift .shl 64) "d" "a" "b"
    == "\tvpsllvq %xmm1, %xmm0, %xmm2"

#guard renderVsimdInstr demoAlloc (.varShift .shr 64) "d" "a" "b"
    == "\tvpsrlvq %xmm1, %xmm0, %xmm2"

-- The rendered body of the two kernels under the general XMM linear-scan
-- allocator: the two params pin to `%xmm0`/`%xmm1` and the result draws `%xmm2`.
#guard (renderVsimdComAuto vpsllvqXmmCom).1 == ["\tvpsllvq %xmm1, %xmm0, %xmm2"]

#guard (renderVsimdComAuto vpsrlvqXmmCom).1 == ["\tvpsrlvq %xmm1, %xmm0, %xmm2"]

/-! ## 4. Encoder membership: the VEX byte arm

`VsimdByteEncoder.encodeVsimdInst` carries the per-lane variable shifts at
`VEX.128.66.0F38`: opcode `0x47` for the left shift, `0x45` for the right shift,
with `VEX.W = 1` selecting the 64-bit lane (`W = 0` is the 32-bit-lane
`VPSLLVD`/`VPSRLVD`). -/

/-- **`VPSLLVQ` encoder arm.** `VEX.128.66.0F38.W1 47 /r` — the three-operand
    VEX form with the destination in `reg`, the data operand in `vvvv`, and the
    count operand in `rm`. -/
theorem vpsllvq_bytes (d a b : Nat) :
    encodeVsimdInst (.varShift .shl 64) d a b
      = encVex3 0b00010 0b01 1 0 0x47 d a b none := rfl

/-- **`VPSRLVQ` encoder arm.** `VEX.128.66.0F38.W1 45 /r`. -/
theorem vpsrlvq_bytes (d a b : Nat) :
    encodeVsimdInst (.varShift .shr 64) d a b
      = encVex3 0b00010 0b01 1 0 0x45 d a b none := rfl

-- `vpsllvq %xmm1, %xmm0, %xmm2` and `vpsrlvq %xmm1, %xmm0, %xmm2`: the 3-byte
-- VEX prefix `c4 e2 f9` (map `0F38`, `pp = 66`, `W = 1`, `L = 0`, `vvvv = xmm0`),
-- the opcode, and the register-direct ModRM `d1` (`reg = 2`, `rm = 1`).
#guard (encodeVsimdInst (.varShift .shl 64) 2 0 1).map (·.toNat)
    == [0xc4, 0xe2, 0xf9, 0x47, 0xd1]

#guard (encodeVsimdInst (.varShift .shr 64) 2 0 1).map (·.toNat)
    == [0xc4, 0xe2, 0xf9, 0x45, 0xd1]

/-! ## 5. Constant-time classification

The op is not an addressing surface, so both kernels lie in the index-free
CT-by-construction fragment of `Com jasminDialect`. -/

/-- **The count operand is not an addressing surface.** A per-lane variable
    shift performs no data-indexed memory access at any lane width, so
    `jasminOpAddrSurface` classifies it as straight-line dataflow — the same
    classification the branchless `select` gets. -/
theorem varShift_no_addr_surface (bop : JasminBinOp) (laneW : Nat) :
    jasminOpAddrSurface (.vsimd (.varShift bop laneW)) = false := rfl

/-- The `VPSLLVQ` kernel is in the index-free CT-by-construction fragment. -/
theorem vpsllvqXmmCom_ct : ComJasminCTByConstruction vpsllvqXmmCom := by
  exact ⟨rfl, trivial⟩

/-- The `VPSRLVQ` kernel is in the index-free CT-by-construction fragment. -/
theorem vpsrlvqXmmCom_ct : ComJasminCTByConstruction vpsrlvqXmmCom := by
  exact ⟨rfl, trivial⟩

/-- The public-amount `VPSLLVQ` kernel is in the index-free CT-by-construction
    fragment: both the materialised count vector and the shift are index-free. -/
theorem vpsllvqImmCom_ct (n : Nat) : ComJasminCTByConstruction (vpsllvqImmCom n) := by
  exact ⟨rfl, rfl, trivial⟩

/-- The public-amount `VPSRLVQ` kernel is in the index-free CT-by-construction
    fragment. -/
theorem vpsrlvqImmCom_ct (n : Nat) : ComJasminCTByConstruction (vpsrlvqImmCom n) := by
  exact ⟨rfl, rfl, trivial⟩

/-! ## 6. The 32-bit-lane arm `VPSLLVD` / `VPSRLVD` (VEX.W = 0)

The same per-lane variable shift on the 128-bit XMM carrier at a 32-bit lane:
four lanes, each shifted by its own count. The encoder selects this arm with
`VEX.W = 0` — the same opcodes `0x47` / `0x45` as the 64-bit arm, with the W bit
distinguishing the lane width — and the printer emits `vpsllvd` / `vpsrlvd`. -/

/-- **Per-lane law, 32-bit lane.** Lane `k` (the `[32k, 32k+32)` slice) of the
    four-lane variable shift `simdVarShiftW bop 32 a b` is `bop.apply` of lane
    `k` of `a` and lane `k` of `b`. For `bop = .shl` / `.shr` each 32-bit lane is
    shifted by its own count, which is what distinguishes `VPSLLVD` / `VPSRLVD`
    from the uniform-count packed shift. The four-lane counterpart of
    `simdVarShift64_lane`. -/
theorem simdVarShift32_lane (bop : JasminBinOp) (a b : BitVec 128) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (simdVarShiftW bop 32 a b)
      = bop.apply (BitVec.extractLsb' (32 * k.val) 32 a)
                  (BitVec.extractLsb' (32 * k.val) 32 b) := by
  fin_cases k <;> cases bop <;>
    simp only [simdVarShiftW, List.range, List.range.loop, List.foldl, JasminBinOp.apply] <;>
    bv_decide

/-- The AT&T mnemonic of the 32-bit-lane per-lane left shift is `vpsllvd`. -/
theorem vpsllvd_mnemonic : SimdOp.attMnemonic (.varShift .shl 32) = "vpsllvd" := rfl

/-- The AT&T mnemonic of the 32-bit-lane per-lane right shift is `vpsrlvd`. -/
theorem vpsrlvd_mnemonic : SimdOp.attMnemonic (.varShift .shr 32) = "vpsrlvd" := rfl

/-- **`VPSLLVD` printer arm.** The op takes the three-operand VEX form, rendered
    in AT&T operand order `op src2, src1, dst`, for any register assignment. -/
theorem vpsllvd_att_line (alloc : XAlloc) (dst a b : String) :
    renderVsimdInstr alloc (.varShift .shl 32) dst a b
      = "\t" ++ SimdOp.attMnemonic (.varShift .shl 32) ++ " " ++ xmmReg alloc b
          ++ ", " ++ xmmReg alloc a ++ ", " ++ xmmReg alloc dst := rfl

/-- **`VPSRLVD` printer arm.** The op takes the three-operand VEX form, rendered
    in AT&T operand order `op src2, src1, dst`. -/
theorem vpsrlvd_att_line (alloc : XAlloc) (dst a b : String) :
    renderVsimdInstr alloc (.varShift .shr 32) dst a b
      = "\t" ++ SimdOp.attMnemonic (.varShift .shr 32) ++ " " ++ xmmReg alloc b
          ++ ", " ++ xmmReg alloc a ++ ", " ++ xmmReg alloc dst := rfl

-- The two 32-bit-lane variable shifts print as real three-operand AT&T lines.
#guard renderVsimdInstr demoAlloc (.varShift .shl 32) "d" "a" "b"
    == "\tvpsllvd %xmm1, %xmm0, %xmm2"

#guard renderVsimdInstr demoAlloc (.varShift .shr 32) "d" "a" "b"
    == "\tvpsrlvd %xmm1, %xmm0, %xmm2"

/-- **`VPSLLVD` encoder arm.** `VEX.128.66.0F38.W0 47 /r` — the `W = 0`
    counterpart of `VPSLLVQ`, selecting the 32-bit lane; the destination is in
    `reg`, the data operand in `vvvv`, the count operand in `rm`. -/
theorem vpsllvd_bytes (d a b : Nat) :
    encodeVsimdInst (.varShift .shl 32) d a b
      = encVex3 0b00010 0b01 0 0 0x47 d a b none := rfl

/-- **`VPSRLVD` encoder arm.** `VEX.128.66.0F38.W0 45 /r`. -/
theorem vpsrlvd_bytes (d a b : Nat) :
    encodeVsimdInst (.varShift .shr 32) d a b
      = encVex3 0b00010 0b01 0 0 0x45 d a b none := rfl

-- `vpsllvd %xmm1, %xmm0, %xmm2` and `vpsrlvd %xmm1, %xmm0, %xmm2`: the 3-byte
-- VEX prefix `c4 e2 79 (map 0F38, pp = 66, W = 0, L = 0, vvvv = xmm0), the
-- opcode, and the register-direct ModRM `d1` (reg = 2, rm = 1).
#guard (encodeVsimdInst (.varShift .shl 32) 2 0 1).map (·.toNat)
    == [0xc4, 0xe2, 0x79, 0x47, 0xd1]

#guard (encodeVsimdInst (.varShift .shr 32) 2 0 1).map (·.toNat)
    == [0xc4, 0xe2, 0x79, 0x45, 0xd1]

end CatCrypt.Crypto.SecureCompilation.VectorVarShift
