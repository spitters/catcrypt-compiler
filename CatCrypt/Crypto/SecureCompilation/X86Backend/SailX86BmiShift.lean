/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# Intel-specification anchor for the BMI2 variable shifts `SHLX` / `SHRX` / `SARX`

The ACL2-derived Sail model that `SailX86Lean.lean` anchors the GP-ALU and ADX
instructions against carries no BMI2 variable shift: its `shifts_spec.sail`
defines only the flag-writing legacy `SAL`/`SHL`/`SHR`/`SAR`. The external
specification used here for `SHLX`, `SHRX` and `SARX` is Intel's executable
instruction specification, in the Intel ISA Specification Language, published at
[`intel/SDM`](https://github.com/intel/SDM), file
`xml92/SARX-SHLX-SHRX-Shift-Without-Affecting-Flags.xml`. Each `<operation>`
element of that file is quoted verbatim in the docstring of the Lean function
transcribing it.

Two properties are stated per instruction at 64-bit operand size:

* the data word written by the owned model's `evalInstr` equals the
  transcription of Intel's `<operation>` body, for all operand values;
* the owned model writes no flag, which on the Intel side is the absence of any
  `rflags` entry in the `<operation>` element's callee list.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend

namespace SailX86BmiShift

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## Transcriptions of the Intel `<operation>` bodies -/

/-- Intel `<operation name="SHLX" variant_kind="Standard variant" mnemonic="SHLX">`:

```
let count := if operand_size == 64 then Unsigned(src2[5:0]) else Unsigned(src2[4:0]);
let result := Shift_Left_Logical(src1, count);
```

at `operand_size == 64`. `Unsigned(src2[5:0])` is the low six bits of the count
operand read as a natural number, and `Shift_Left_Logical` is the logical left
shift. The callee list of the element is
`Std::Integer::Eq`, `Std::Integer::Lt`, `Std::Integer::Subtract`,
`Std::Bits::Unsigned`, `Std::Bits::Shift_Left_Logical`; it contains no `rflags`
function. -/
def intelShlx64 (src1 src2 : BitVec 64) : BitVec 64 :=
  let count : Nat := (src2.extractLsb' 0 6).toNat
  src1 <<< count

/-- Intel `<operation name="SHRX" variant_kind="Standard variant" mnemonic="SHRX">`:

```
let count := if operand_size == 64 then Unsigned(src2[5:0]) else Unsigned(src2[4:0]);
let result := Shift_Right_Logical(src1, count);
```

at `operand_size == 64`. The callee list is `Std::Integer::Eq`,
`Std::Integer::Lt`, `Std::Integer::Subtract`, `Std::Bits::Unsigned`,
`Std::Bits::Shift_Right_Logical`; it contains no `rflags` function. -/
def intelShrx64 (src1 src2 : BitVec 64) : BitVec 64 :=
  let count : Nat := (src2.extractLsb' 0 6).toNat
  src1 >>> count

/-- Intel `<operation name="SARX" variant_kind="Standard variant" mnemonic="SARX">`:

```
let count := if operand_size == 64 then Unsigned(src2[5:0]) else Unsigned(src2[4:0]);
let result := Shift_Right_Arithmetic(src1, count);
```

at `operand_size == 64`. The callee list is `Std::Integer::Eq`,
`Std::Integer::Lt`, `Std::Integer::Subtract`, `Std::Bits::Unsigned`,
`Std::Bits::Shift_Right_Arithmetic`; it contains no `rflags` function. -/
def intelSarx64 (src1 src2 : BitVec 64) : BitVec 64 :=
  let count : Nat := (src2.extractLsb' 0 6).toNat
  BitVec.sshiftRight src1 count

/-! ## The count mask -/

/-- The owned model's `shiftCount` at width 64 is Intel's `Unsigned(src2[5:0])`:
    both are the count operand's low six bits as a natural number. -/
theorem shiftCount_eq_intel_count (c : BitVec 64) :
    shiftCount c = (c.extractLsb' 0 6).toNat := by
  simp [shiftCount, BitVec.extractLsb']

/-- A count reduced modulo the word width is below it, so the clamp to the width
    in `wshl`/`wshr`/`wsar` is inert. -/
@[simp] theorem min_intel_count (n : Nat) : min 64 (n % 64) = n % 64 := by omega

/-! ## Machine states -/

/-- Faithful state with a value register `"v" := x` and a count register
    `"c" := y`; every other register reads as `0` and no flag is set. -/
def jstShift (x y : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "v" then x else if r = "c" then y else 0 }

/-! ## Data-word agreement -/

/-- `evalInstr` at `.shlx` writes Intel's `SHLX` result word, for all operand
    values. -/
theorem shlx_eq_intel (x y : BitVec 64) :
    (evalInstr (jstShift x y) (.shlx "d" "v" "c")).get "d" = intelShlx64 x y := by
  simp [evalInstr, x86_SHLX, wshl, jstShift, JState.get, JState.setReg,
    intelShlx64, shiftCount_eq_intel_count, min_intel_count]

/-- `evalInstr` at `.shrx` writes Intel's `SHRX` result word, for all operand
    values. -/
theorem shrx_eq_intel (x y : BitVec 64) :
    (evalInstr (jstShift x y) (.shrx "d" "v" "c")).get "d" = intelShrx64 x y := by
  simp [evalInstr, x86_SHRX, wshr, jstShift, JState.get, JState.setReg,
    intelShrx64, shiftCount_eq_intel_count, min_intel_count]

/-- `evalInstr` at `.sarx` writes Intel's `SARX` result word, for all operand
    values. -/
theorem sarx_eq_intel (x y : BitVec 64) :
    (evalInstr (jstShift x y) (.sarx "d" "v" "c")).get "d" = intelSarx64 x y := by
  simp [evalInstr, x86_SARX, wsar, jstShift, JState.get, JState.setReg,
    intelSarx64, shiftCount_eq_intel_count, min_intel_count]

/-! ## Absence of a flag write -/

/-- `evalInstr` at `.shlx` leaves the whole flag record unchanged, for any state
    and any operand registers. -/
theorem shlx_flags (s : JState 64) (d v c : String) :
    (evalInstr s (.shlx d v c)).flags = s.flags := rfl

/-- `evalInstr` at `.shrx` leaves the whole flag record unchanged, for any state
    and any operand registers. -/
theorem shrx_flags (s : JState 64) (d v c : String) :
    (evalInstr s (.shrx d v c)).flags = s.flags := rfl

/-- `evalInstr` at `.sarx` leaves the whole flag record unchanged, for any state
    and any operand registers. -/
theorem sarx_flags (s : JState 64) (d v c : String) :
    (evalInstr s (.sarx d v c)).flags = s.flags := rfl

end SailX86BmiShift

end CatCrypt.Crypto.SecureCompilation.X86Backend
