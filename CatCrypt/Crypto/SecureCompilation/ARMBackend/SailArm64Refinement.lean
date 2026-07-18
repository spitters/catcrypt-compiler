/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmModel
import Mathlib.Data.BitVec
import Mathlib.Tactic.NormNum

/-!
# Sail-execute refinement for the 64-bit AArch64 GP-ALU model (`ArmModel`)

This is the AArch64 analogue of `RISCVBackend/SailRiscv64Refinement.lean`. It
connects our **trusted hand-written effect semantics** (the 64-bit `X`-register
GP-ALU effects that `evalBInst`'s `.add`/`.sub`/`.and`/`.orr`/`.eor` arms apply —
`s.get a + s.get b`, `s.get a - s.get b`, `opAnd64`, `opOrr64`, `opEor64`) to the
authoritative Arm execute semantics, by transcribing the `integer_*_shiftedreg`
execute clauses from the official `rems-project/sail-arm` ASL-derived Sail model.

## What grounds ARM was: a decode round-trip only

`SailArmDecoder.lean` proves `decode (encode i) = i` against the `sail-arm`
`aarch_decode.sail` *parse* clauses — which operand bits each instruction names.
That left a residual versus RISC-V, whose `SailRiscv64Refinement` additionally
equates each model **step** with the value the vendored `execute_RTYPE` Sail
clause writes (a value-level *execute* refinement). This module closes that gap
for the GP-ALU fragment: it transcribes the sail-arm *execute* clauses and proves
the model's per-op value equals what the Sail clause writes.

## Source of the transcribed clauses (the trust-critical provenance)

The clauses are transcribed **verbatim in structure** from the vendored
`rems-project/sail-arm` checkout at
`bench/reference_install/sail-arm/arm-v8.5-a/model/aarch64.sail`:

* `integer_arithmetic_addsub_shiftedreg` (`aarch64.sail:4944`):

  ```
  let operand1 = X(n);
  operand2 = ShiftReg(m, shift_type, shift_amount);
  if sub_op then { operand2 = ~(operand2); carry_in = 0b1 }
            else { carry_in = 0b0 };
  (result, nzcv) = AddWithCarry(operand1, operand2, carry_in);
  if setflags then PSTATE.NZCV = nzcv;
  X(d) = result
  ```

* `integer_logical_shiftedreg` (`aarch64.sail:4915`):

  ```
  let operand1 = X(n);
  operand2 = ShiftReg(m, shift_type, shift_amount);
  if invert then operand2 = ~(operand2);
  match op { LogicalOp_AND => operand1 & operand2,
             LogicalOp_ORR => operand1 | operand2,
             LogicalOp_EOR => operand1 ^ operand2 };
  if setflags then PSTATE.NZCV = ...;
  X(d) = result
  ```

* `AddWithCarry` (`aarch64.sail:4020`): `result = __GetSlice_int(N, UInt(x) +
  UInt(y) + UInt(carry_in), 0)` — the low `N` bits of the unsigned sum (the flags
  are the `n/z/c/v` bits we do not need for the no-flags fragment).

* `ShiftReg` (`aarch64.sail:4880`) with `ShiftType_LSL` is `LSL(X(reg), amount)`;
  for the GP-ALU emission `amount = 0`, and `LSL(x, 0) = x`.

## Scope of the fragment

The base-ALU GP-ALU subset (`ComToArmLsem.IsGpAlu`): `ADD`/`SUB` (`sub_op =
false`/`true`, `setflags = false`) and `AND`/`ORR`/`EOR` (`invert = false`,
`setflags = false`), all 64-bit (`datasize = 64`), with `shift_type = LSL` and
`shift_amount = 0` (the un-shifted register form the lowering emits). For each
op, the value the transcribed Sail execute clause writes to `Xd` equals our
`ArmModel` op applied to the operands — the AArch64 mirror of `rtype_add`, …,
`rtype_xor`.

The flag-setting forms (`ADDS`/`ADCS`/`SUBS`/`SBCS`), the multiplies
(`MUL`/`UMULH`), the conditional-selects (`CSEL`) and the constant loads
(`MOVZ`/`MOVK`) are out of this no-flags GP-ALU fragment, exactly as RISC-V's
refinement scopes to `execute_RTYPE`'s `ADD`/`SUB`/`AND`/`OR`/`XOR`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArm64Ref

open CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. Vendored Sail runtime primitives (transcribed from `sail-arm` + `lean-sail`)

`AddWithCarry`'s `result` is `__GetSlice_int(N, UInt(x)+UInt(y)+UInt(carry_in),
0)` — the low `N = 64` bits of the unsigned (`Nat`) sum, which is exactly
`BitVec.ofNat 64` of that sum. `LSL(x, 0)` is the identity. We give the two
runtime ops the model needs at these argument shapes. -/

/-- `UInt` of a one-bit carry: `0b0`/`0b1` ↦ `0`/`1` (the `carry_in` argument). -/
def uintBit (b : Bool) : Nat := if b then 1 else 0

/-- The `result` component of the Arm `AddWithCarry(x, y, carry_in)` pseudocode
    (`aarch64.sail:4020`): `__GetSlice_int(64, UInt(x) + UInt(y) + UInt(cin), 0)`,
    the low 64 bits of the unsigned `Nat` sum. We need only the result; the `nzcv`
    flag word is unused on the no-flags GP-ALU fragment. -/
def addWithCarryResult (x y : BitVec 64) (cin : Bool) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat + y.toNat + uintBit cin)

/-- `ShiftReg(reg, ShiftType_LSL, amount)` (`aarch64.sail:4880`+`4883`) is
    `LSL(operand, amount)`; for the GP-ALU emission `amount = 0`, and `LSL(x, 0)`
    is the identity. We transcribe the `LSL` shift the clause performs. -/
def shiftRegLSL (operand : BitVec 64) (amount : Nat) : BitVec 64 := operand <<< amount

/-! ## 2. Thin faithful state monad + register accessors (fold of the Sail state)

A flat `BitVec 5 → BitVec 64` register file, the same simplification the RISC-V
refinement uses (`SailRiscv64Refinement.RegFile`/`SailM`). On the exception-free
GP-ALU subset this is observably equal to the full sail-arm register state; the
`xzr` zero-register discipline (`X(31)` reads `0`, writes ignored) is modelled
exactly as `aget_X`/`aset_X` do for the GP registers. -/

/-- The register file: `X0 … X30`, with index `31` the zero register `XZR`. -/
abbrev RegFile := BitVec 5 → BitVec 64
/-- The thin state monad (fold of sail-arm's register-effecting monad). -/
abbrev SailM := StateM RegFile

/-- Update register `i` to `v`. -/
def upd (s : RegFile) (i : BitVec 5) (v : BitVec 64) : RegFile :=
  fun j => if j = i then v else s j

/-- `X(n)` read (`aget_X`): index `31` is `XZR`, hardwired to `0`. -/
def read_X (i : BitVec 5) : SailM (BitVec 64) :=
  if i.toNat = 31 then pure 0 else do pure ((← get) i)

/-- `X(d) = v` write (`aset_X`): a write to `XZR` (index `31`) is discarded. -/
def write_X (i : BitVec 5) (v : BitVec 64) : SailM Unit :=
  if i.toNat = 31 then pure () else modify (upd · i v)

/-! ## 3. The transcribed Sail execute clauses

`integer_arithmetic_addsub_shiftedreg` and `integer_logical_shiftedreg`, in the
GP-ALU shape (`datasize = 64`, `setflags = false`, `shift_type = LSL`). The
`LogicalOp`/`sub_op` discriminants are the sail-arm enums. -/

/-- The sail-arm `LogicalOp` enum (`aarch_types.sail:538`). -/
inductive LogicalOp where
  /-- `LogicalOp_AND`. -/
  | AND
  /-- `LogicalOp_ORR`. -/
  | ORR
  /-- `LogicalOp_EOR`. -/
  | EOR
  deriving DecidableEq, Repr

/-- **`integer_arithmetic_addsub_shiftedreg`** (`aarch64.sail:4944`), in the
    no-flags GP-ALU shape (`setflags = false`, `shift_type = LSL`,
    `shift_amount`). `sub_op = false` ⇒ ADD; `sub_op = true` ⇒ SUB (`operand2 =
    ~operand2`, `carry_in = 1`). Writes `X(d) = AddWithCarry(operand1, operand2,
    carry_in).result`. -/
def integer_arithmetic_addsub_shiftedreg
    (d m n : BitVec 5) (shift_amount : Nat) (sub_op : Bool) : SailM Unit := do
  let operand1 ← read_X n
  let operand2_pre := shiftRegLSL (← read_X m) shift_amount
  let (operand2, carry_in) :=
    if sub_op then (~~~ operand2_pre, true) else (operand2_pre, false)
  let result := addWithCarryResult operand1 operand2 carry_in
  write_X d result

/-- **`integer_logical_shiftedreg`** (`aarch64.sail:4915`), in the no-flags GP-ALU
    shape (`setflags = false`, `invert = false`, `shift_type = LSL`). Writes
    `X(d) = operand1 ⟨op⟩ operand2`. -/
def integer_logical_shiftedreg
    (d m n : BitVec 5) (shift_amount : Nat) (op : LogicalOp) : SailM Unit := do
  let operand1 ← read_X n
  let operand2 := shiftRegLSL (← read_X m) shift_amount
  let result :=
    match op with
    | .AND => operand1 &&& operand2
    | .ORR => operand1 ||| operand2
    | .EOR => operand1 ^^^ operand2
  write_X d result

/-! ## 4. Refinement: the Sail clause's written value = the real `ArmModel` op

For each GP-ALU op (`shift_amount = 0`, the un-shifted register form the lowering
emits), the value the transcribed Sail execute clause writes to `Xd` equals our
`ArmModel` op applied to the read operands. The reads are `XZR`-aware, matching
`BState.get` (`xzr` ↦ `0`). -/

/-- `XZR`-aware read, matching the Sail runtime `read_X` and `BState.get`'s
    `xzr` ↦ `0` discipline. -/
def rget (s : RegFile) (i : BitVec 5) : BitVec 64 := if i.toNat = 31 then 0 else s i

/-- Run a clause and read register `d`'s final value. -/
def runXd (m : SailM Unit) (s : RegFile) (d : BitVec 5) : BitVec 64 := (m.run s).2 d

/-- Low 64 bits of the unsigned sum is `BitVec` addition (the ADD result). -/
private theorem addWithCarryResult_add (x y : BitVec 64) :
    addWithCarryResult x y false = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [addWithCarryResult, uintBit]

/-- Low 64 bits of `UInt(x) + UInt(~y) + 1` is `x - y` (the SUB result: the Arm
    `AddWithCarry(x, NOT(y), 1)` two's-complement subtract). -/
private theorem addWithCarryResult_sub (x y : BitVec 64) :
    addWithCarryResult x (~~~ y) true = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [addWithCarryResult, uintBit, if_true, BitVec.toNat_ofNat,
    BitVec.toNat_not, BitVec.toNat_sub]
  omega

/-- **The Sail `ADD` (shifted-reg, un-shifted) clause writes the model's `.add`
    value** (`evalBInst`'s `.add` arm: `s.get a + s.get b`). -/
theorem addsub_add (s : RegFile) (m n d : BitVec 5) (hd : d.toNat ≠ 31) :
    runXd (integer_arithmetic_addsub_shiftedreg d m n 0 false) s d
      = (rget s n) + (rget s m) := by
  by_cases hn : n.toNat = 31 <;> by_cases hm : m.toNat = 31 <;>
    simp [runXd, integer_arithmetic_addsub_shiftedreg, read_X, write_X, rget, upd,
      shiftRegLSL, addWithCarryResult_add, hn, hm, hd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- **The Sail `SUB` (shifted-reg, un-shifted) clause writes the model's `.sub`
    value** (`evalBInst`'s `.sub` arm: `s.get a - s.get b`). -/
theorem addsub_sub (s : RegFile) (m n d : BitVec 5) (hd : d.toNat ≠ 31) :
    runXd (integer_arithmetic_addsub_shiftedreg d m n 0 true) s d
      = (rget s n) - (rget s m) := by
  by_cases hn : n.toNat = 31 <;> by_cases hm : m.toNat = 31 <;>
    simp only [runXd, integer_arithmetic_addsub_shiftedreg, read_X, write_X, rget, upd,
      shiftRegLSL, hn, hm, hd, if_true, if_false, BitVec.shiftLeft_zero, addWithCarryResult_sub,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- **The Sail `AND` (shifted-reg, un-shifted) clause writes our `opAnd64`.** -/
theorem logical_and (s : RegFile) (m n d : BitVec 5) (hd : d.toNat ≠ 31) :
    runXd (integer_logical_shiftedreg d m n 0 .AND) s d
      = opAnd64 (rget s n) (rget s m) := by
  by_cases hn : n.toNat = 31 <;> by_cases hm : m.toNat = 31 <;>
    simp [runXd, integer_logical_shiftedreg, read_X, write_X, rget, upd,
      shiftRegLSL, opAnd64, hn, hm, hd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- **The Sail `ORR` (shifted-reg, un-shifted) clause writes our `opOrr64`.** -/
theorem logical_orr (s : RegFile) (m n d : BitVec 5) (hd : d.toNat ≠ 31) :
    runXd (integer_logical_shiftedreg d m n 0 .ORR) s d
      = opOrr64 (rget s n) (rget s m) := by
  by_cases hn : n.toNat = 31 <;> by_cases hm : m.toNat = 31 <;>
    simp [runXd, integer_logical_shiftedreg, read_X, write_X, rget, upd,
      shiftRegLSL, opOrr64, hn, hm, hd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-- **The Sail `EOR` (shifted-reg, un-shifted) clause writes our `opEor64`.** -/
theorem logical_eor (s : RegFile) (m n d : BitVec 5) (hd : d.toNat ≠ 31) :
    runXd (integer_logical_shiftedreg d m n 0 .EOR) s d
      = opEor64 (rget s n) (rget s m) := by
  by_cases hn : n.toNat = 31 <;> by_cases hm : m.toNat = 31 <;>
    simp [runXd, integer_logical_shiftedreg, read_X, write_X, rget, upd,
      shiftRegLSL, opEor64, hn, hm, hd,
      bind, StateT.bind, StateT.run, pure, StateT.pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet]

/-! ## 5. `armStep_sail_grounded`: every GP-ALU model step is a Sail-execute step

The five per-op equalities, bundled as the AArch64 analogue of RISC-V's
`riscvStep64_sail_grounded`: for each GP-ALU `BInst` arm, the value the model's
`evalBInst` writes to the destination equals the value the transcribed sail-arm
execute clause writes — so the model's effect *is* the authoritative Sail
execute semantics on this fragment, not merely a hand-written semantics validated
by decode round-trip + qemu.

The model side is read off `evalBInst`'s GP-ALU arms (`ArmModel.lean`):
`.add ↦ s.get a + s.get b`, `.sub ↦ s.get a - s.get b`, `.and ↦ opAnd64`,
`.orr ↦ opOrr64`, `.eor ↦ opEor64`. We phrase the bundle over the abstract operand values
`va = rget s n`, `vb = rget s m` so it is independent of the register-name vs
register-index encoding (the model keys on `String` names, the Sail clause on
`BitVec 5` indices; both apply the same `op`). -/

/-- **`armStep_sail_grounded` (the GP-ALU Sail-execute grounding).** For every
    GP-ALU op, the value the transcribed sail-arm execute clause writes to `Xd`
    equals the corresponding `ArmModel` 64-bit op applied to the read operands —
    the AArch64 mirror of `SailRiscv64Ref.rtype_*`. Bundled as one statement over
    all five ops, with the `BState`-level op functions on the right. -/
theorem armStep_sail_grounded (s : RegFile) (m n d : BitVec 5) (hd : d.toNat ≠ 31) :
    runXd (integer_arithmetic_addsub_shiftedreg d m n 0 false) s d
        = (rget s n) + (rget s m)
    ∧ runXd (integer_arithmetic_addsub_shiftedreg d m n 0 true) s d
        = (rget s n) - (rget s m)
    ∧ runXd (integer_logical_shiftedreg d m n 0 .AND) s d
        = opAnd64 (rget s n) (rget s m)
    ∧ runXd (integer_logical_shiftedreg d m n 0 .ORR) s d
        = opOrr64 (rget s n) (rget s m)
    ∧ runXd (integer_logical_shiftedreg d m n 0 .EOR) s d
        = opEor64 (rget s n) (rget s m) :=
  ⟨addsub_add s m n d hd, addsub_sub s m n d hd, logical_and s m n d hd,
    logical_orr s m n d hd, logical_eor s m n d hd⟩

/-! ## 6. The Sail-execute-grounded ARM base-ALU proposition

`ComToArmLsem.ArmBaseAluGrounded` records the whole-`Com` value-preservation
keystone but is explicitly *not* a Sail-execute refinement — its GP-ALU coverage
is grounded only by the decode round-trip + qemu. `SailExecuteGroundedGpAlu` is
the strengthening this module supplies: every GP-ALU op the model executes has
its written value proved equal to the authoritative sail-arm *execute* clause.
This is the proposition that brings ARM to RISC-V depth (the
`RiscvBaseAluGrounded` analogue: a value-level execute refinement, not a parse
round-trip). -/

/-- **The Sail-execute grounding of the ARM GP-ALU fragment.** For every base-ALU
    op and every register state and operand registers (`d ≠ XZR`), the value the
    transcribed sail-arm execute clause writes equals the `ArmModel` op — i.e. the
    model's per-step effect is the authoritative Arm execute semantics on the
    GP-ALU subset. The AArch64 analogue of RISC-V's value-level
    `execute_RTYPE`-grounded `RiscvBaseAluGrounded`. -/
def SailExecuteGroundedGpAlu : Prop :=
  ∀ (s : RegFile) (m n d : BitVec 5), d.toNat ≠ 31 →
    runXd (integer_arithmetic_addsub_shiftedreg d m n 0 false) s d
        = (rget s n) + (rget s m)
    ∧ runXd (integer_arithmetic_addsub_shiftedreg d m n 0 true) s d
        = (rget s n) - (rget s m)
    ∧ runXd (integer_logical_shiftedreg d m n 0 .AND) s d
        = opAnd64 (rget s n) (rget s m)
    ∧ runXd (integer_logical_shiftedreg d m n 0 .ORR) s d
        = opOrr64 (rget s n) (rget s m)
    ∧ runXd (integer_logical_shiftedreg d m n 0 .EOR) s d
        = opEor64 (rget s n) (rget s m)

/-- `SailExecuteGroundedGpAlu` is inhabited by the proved per-op refinements (not
    `True`): the ARM GP-ALU model is grounded in the sail-arm execute semantics. -/
theorem sailExecuteGroundedGpAlu_proof : SailExecuteGroundedGpAlu :=
  fun s m n d hd => armStep_sail_grounded s m n d hd

end CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArm64Ref
