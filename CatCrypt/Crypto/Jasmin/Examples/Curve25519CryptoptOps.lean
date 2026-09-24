/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.Jasmin.BignumExec


@[expose] public section
set_option autoImplicit false

/-!
# Operational semantics for the new x86 opcodes used by `Curve25519CryptoptPort`

The CryptOpt-tuned `carry_mul` / `carry_square` asms use seven BMI1/BMI2
opcodes that are not yet in `BignumExec.lean`'s dispatcher. This file
provides:

1. **Pure functions** — `bzhi`, `shrdImm`, `imulImm`, `shlx`, `and64`,
   `xor64`, `test64` — each computing the BitVec arithmetic of one
   intrinsic per Intel SDM Vol. 2 / 2B.
2. **A wrapper interpreter** — `execInstrPlus` — that dispatches the new
   opcodes and falls back to the base `BignumExec.execInstr` for the
   pre-existing repertoire (`ADD_64`, `ADC_64`, `MULX`, `ADCX`, `ADOX`,
   `XOR_64`, `SUB_64`, `SBB_64`, plus all `Cassgn` shapes). Then
   `bignumExecPlus` threads it over a body, identically to
   `bignumExec`.

The wrapper avoids touching `BignumExec.lean` directly (which the
active Lean terminal hot-lists). Folding these opcodes into the main
dispatcher is mechanical and can happen when the active terminal
releases the file — at which point this wrapper becomes redundant.

## Audit boundary moved (vs the leaf-only commit `c73b2182`)

With these semantics:
- `mulBody` / `sqrBody` from `Curve25519CryptoptPort.lean` become
  *operationally interpretable* in Lean (modulo the spill-slot encoding
  as synthetic locals, which is structural, not semantic).
- An eventual proof of `bignumExecPlus mulBody ⊆ fiat_25519_carry_mul`
  / `… sqrBody ⊆ fiat_25519_carry_square` would close the audit
  boundary inside Lean — replacing "trust CryptOpt + linker" with
  "trust the seven SDM-spec'd helpers below".
- Such a proof (165 / 111 instructions of carry-chain reasoning) is
  outside the scope of this module.
-/

namespace CatCrypt.Crypto.Jasmin.Curve25519CryptoptOps

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec

/-! ## §1. Pure intrinsic semantics

Each function here mirrors one Intel SDM operation as a closed-form
BitVec computation. -/

/-- `BZHI dst, src, ctrl` — clear bits at index ≥ `ctrl[7:0]` in `src`.
    SDM Vol. 2A: the count is taken from the low 8 bits of `ctrl`; if
    that count is `≥ 64` the result is `src` unchanged (operand size
    handling). For our `carry_mul` chain, `ctrl` is always `51` so the
    index-clear branch is the live one. -/
def bzhi (a ctrl : BitVec 64) : BitVec 64 :=
  let n := ctrl.toNat % 256
  if n ≥ 64 then a
  else a &&& BitVec.ofNat 64 ((1 <<< n) - 1)

/-- `SHRD dst, src, count` (immediate count form) — shift the
    destination register right by `count` bits, with the high `count`
    positions of the new `dst` filled from the low `count` bits of
    `src`. SDM Vol. 2B: the count is masked to 6 bits.

    Equivalent expression for the low 64 bits of the conceptual
    128-bit shift `((src ## dst) >> count)`:
    `(dst >>> n) ||| (src <<< (64 − n))` for `n = count mod 64`.
    When `n = 0` the result is `dst` unchanged. -/
def shrdImm (dst src : BitVec 64) (count : Nat) : BitVec 64 :=
  let n := count % 64
  if n = 0 then dst
  else (dst >>> n) ||| (src <<< (64 - n))

/-- `IMUL dst, src, imm` (3-operand form) — signed multiply with an
    immediate. We expose the low 64 bits of the product, which coincide
    with the unsigned product low bits for any operand. The `carry_mul`
    chain only ever multiplies by small positive constants (`0x13`,
    `0x26`), so signedness does not matter. -/
def imulImm (a : BitVec 64) (imm : Int) : BitVec 64 :=
  a * BitVec.ofInt 64 imm

/-- `SHLX dst, src, count` — variable shift-left, no flags. SDM:
    count is masked to 6 bits. -/
def shlx (a count : BitVec 64) : BitVec 64 :=
  a <<< (count.toNat % 64)

/-- `AND dst, src` — bitwise AND. CF=0, OF=0 (we discard those). -/
def and64 (a b : BitVec 64) : BitVec 64 := a &&& b

/-- `XOR dst, src` — bitwise XOR. CF=0, OF=0 (we discard those). -/
def xor64 (a b : BitVec 64) : BitVec 64 := a ^^^ b

/-- `TEST a, b` — sets ZF/SF/PF from `a & b`; clears CF and OF.
    For our use (`test al, al` initialising an ADCX/ADOX chain) only
    the CF=0 / OF=0 reset matters. Returns `(of, cf) = (0, 0)`. -/
def test64 (_a _b : BitVec 64) : BitVec 64 × BitVec 64 :=
  (0, 0)

/-! ## §2. LVal write helpers for the new bundles

Each new opcode has a specific LVal output shape. The base
`BignumExec`'s `writeSubBundle` / `writeXorBundle` cover the existing
6-LVal flag-bundle shape; the helpers below cover the smaller bundles
(1-LVal for BZHI/SHRD/SHLX, 2-LVal for TEST). -/

def setReg' (s : BignumState) (n : String) (v : BitVec 64) :
    BignumState :=
  setReg s n v

/-- Write a single-LVal bundle (BZHI, SHRD, SHLX). -/
def writeSingleVar (s : BignumState) (lvs : List LVal) (r : BitVec 64) :
    Option BignumState :=
  match lvs with
  | [.Lvar v] => some (setReg' s v.var.vname r)
  | _ => none

/-- Write a 2-LVal `[of, cf]` bundle (TEST). -/
def writeTestBundle (s : BignumState) (lvs : List LVal) (of cf : BitVec 64) :
    Option BignumState :=
  match lvs with
  | [.Lvar ofV, .Lvar cfV] =>
    some (setReg' (setReg' s ofV.var.vname of) cfV.var.vname cf)
  | _ => none

/-! ## §3. Wrapper interpreter

`execInstrPlus` first tries the new opcodes; if none match, it falls
through to the base `BignumExec.execInstr`. -/

/-- Extended Cassgn handler covering the `Papp2` shapes the asm uses
    that the base `evalPExpr` doesn't (yet): `Olsr` (right shift),
    `Olsl` (left shift), and `Oadd` with a nested `Omul` immediate
    (the `lea dst, [a + scale * b]` pattern). -/
def evalCassgnPlus (s : BignumState) (rhs : PExpr) :
    Option (BitVec 64) :=
  match rhs with
  | .Papp2 (.Olsr _) (.Pvar v) (.Pconst k) =>
      some ((s.regs v.gv.var.vname) >>> (k.toNat % 64))
  | .Papp2 (.Olsl _) (.Pvar v) (.Pconst k) =>
      some ((s.regs v.gv.var.vname) <<< (k.toNat % 64))
  | .Papp2 (.Oadd _) (.Pvar a)
      (.Papp2 (.Omul _) (.Pconst k) (.Pvar b)) =>
      let va := s.regs a.gv.var.vname
      let vb := s.regs b.gv.var.vname
      some (va + BitVec.ofInt 64 k * vb)
  | _ => none

def execInstrPlus (s : BignumState) : InstrR → Option BignumState
  -- Cassgn into Lvar with a Papp2 shape the base doesn't handle.
  | .Cassgn (.Lvar v) _ _ rhs@(.Papp2 _ _ _) =>
    match evalCassgnPlus s rhs with
    | some w => some (setReg' s v.var.vname w)
    | none   => execInstr s (.Cassgn (.Lvar v) .AT_none (.sword .U64) rhs)
  | .Copn lvs _ (.Oasm op) args =>
    match op.name, args with
    | "BZHI_64", [ea, eb] => do
        let a ← evalPExpr s ea
        let c ← evalPExpr s eb
        writeSingleVar s lvs (bzhi a c)
    | "SHRD_64_imm", [ea, eb, .Pconst k] => do
        let dst ← evalPExpr s ea
        let src ← evalPExpr s eb
        writeSingleVar s lvs (shrdImm dst src k.toNat)
    | "IMUL_imm_64", [ea, .Pconst k] => do
        let a ← evalPExpr s ea
        -- 6-LVal bundle: discard flags, write to dst.
        match lvs with
        | [.Lnone _ _, .Lnone _ _, .Lnone _ _, .Lnone _ _,
           .Lnone _ _, .Lvar rV] =>
          some (setReg' s rV.var.vname (imulImm a k))
        | _ => none
    | "SHLX_64", [ea, eb] => do
        let a ← evalPExpr s ea
        let c ← evalPExpr s eb
        writeSingleVar s lvs (shlx a c)
    | "AND_64", [ea, eb] => do
        let a ← evalPExpr s ea
        let b ← evalPExpr s eb
        -- 6-LVal bundle as for ADD_64; flags are zeroed by AND but we
        -- discard them.
        match lvs with
        | [.Lnone _ _, .Lnone _ _, .Lnone _ _, .Lnone _ _,
           .Lnone _ _, .Lvar rV] =>
          some (setReg' s rV.var.vname (and64 a b))
        | _ => none
    | "TEST_64", [ea, eb] => do
        let a ← evalPExpr s ea
        let b ← evalPExpr s eb
        let (of, cf) := test64 a b
        writeTestBundle s lvs of cf
    | _, _ =>
        -- Fall through to the base interpreter for the existing repertoire.
        execInstr s (.Copn lvs .AT_none (.Oasm op) args)
  | i => execInstr s i

/-- Body interpreter — same shape as `BignumExec.bignumExec`. -/
def bignumExecPlus : List InstrR → BignumState → Option BignumState
  | [],      s => some s
  | i :: is, s =>
    match execInstrPlus s i with
    | some s' => bignumExecPlus is s'
    | none    => none

/-! ## §4. Sanity examples

A few `decide`-checked unit tests pinning down specific BitVec
identities the chain depends on. -/

example : bzhi 0xFFFFFFFFFFFFFFFF 51 = 0x7FFFFFFFFFFFF := by native_decide

-- BZHI saturates: ctrl ≥ 64 returns the input unchanged.
example : bzhi 0xFFFFFFFFFFFFFFFF 64 = 0xFFFFFFFFFFFFFFFF := by native_decide
example : bzhi 0xFFFFFFFFFFFFFFFF 100 = 0xFFFFFFFFFFFFFFFF := by native_decide

-- SHRD with count=0 leaves dst unchanged.
example : shrdImm 0xDEADBEEF 0xFFFF 0 = 0xDEADBEEF := by native_decide

-- SHRD with count=1: dst >>= 1, top bit fills from src's bit 0.
example : shrdImm 0 1 1 = (BitVec.ofNat 64 1 <<< 63) := by native_decide

example : imulImm (BitVec.ofNat 64 19) 19 = BitVec.ofNat 64 361 := by
  native_decide

-- imul by the canonical Curve25519 reduction constant (0x13 = 19).
example : imulImm (BitVec.ofNat 64 100) 0x13 = BitVec.ofNat 64 1900 := by
  native_decide

example : shlx (BitVec.ofNat 64 1) 1 = BitVec.ofNat 64 2 := by native_decide

example : (and64 0xF0F0F0F0 0x0F0F0F0F : BitVec 64) = 0 := by native_decide

example : (xor64 0x12345678 0x87654321 : BitVec 64) = 0x95511559 := by
  native_decide

-- TEST always returns (0, 0) for the (of, cf) bundle.
example : test64 0xDEADBEEF 0xCAFEBABE = (0, 0) := by native_decide
example : test64 0 0 = (0, 0) := by native_decide

end CatCrypt.Crypto.Jasmin.Curve25519CryptoptOps
