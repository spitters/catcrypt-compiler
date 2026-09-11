/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
public import Std.Tactic.BVDecide

/-!
# Golden path: branchless subtract-with-borrow as `Com jasminDialect`

The **subtract** companion to `FieldEmitGoldenPath`'s add-with-carry capstone
(`fieldAddCom` + `fieldAddCarryCom` + `fieldAdd_carry_reconstruct`). A single-limb
subtract has two halves: the low word `a - b` (`fieldSubCom`, one `regArith .sub`)
and the **borrow-out** bit (`fieldBorrowCom`). Both ride the shared all-`reg 64`
pipeline — `com_arm_e2e`/`com_riscv_e2e` emit to AArch64 and RISC-V with no new
dialect op, and the x86 owned-emit leg goes through the same `compileComToElf`.

The borrow-out is **branchless in the existing `reg 64` alphabet**: for `r = a - b`,

```
borrow = ((~a & b) | (~(a ^ b) & (a - b))) >>> 63
```

— `regConst`/`xor` (for `~`), `and`/`or`/`sub`/`shrImm`, every one in `SupportedOp`.
This is the standard Hacker's-Delight borrow-out identity; its correctness — that it
equals `if a < b then 1 else 0` — is the `bv_decide` oracle below.

The value step `r.toNat + b.toNat = a.toNat + borrow · 2^64` (`field_sub_borrow_reconstruct`,
the subtract-analogue of `fieldAdd_carry_reconstruct`) threads the borrow through the
borrow spec and `BitVec.toNat_sub` + `omega`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldSubBorrow

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-! ## The low word: `a - b` -/

/-- **The field subtract source.** The modular-subtract core `a - b` as a one-op
    `Com jasminDialect` over args `[a, b]` — `v2 := a - b; ret v2`. The compiler
    generates the machine code. Mirrors `fieldAddCom`, op swapped to `.sub`. -/
def fieldSubCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .sub 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- The kernel is in the supported straight-line fragment (mechanical). -/
theorem fieldSubCom_ok : ComOK fieldSubCom :=
  ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof, once, at the source level.** The source `Com.denote` is
    the field-subtract value `a - b`. A cheap `rfl`. -/
theorem fieldSubCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldSubCom (.cons x0 (.cons x1 .nil)) = x1 - x0 := rfl

/-- **The emitted AArch64 block computes the subtract.** Discharged by `com_arm_e2e`
    via the single `comToReg_faithful` — no hand-written `JInstr`. -/
theorem fieldSubCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldSubCom 2))).regs)
        (comRetName fieldSubCom 2)
      = Com.denote fieldSubCom V :=
  com_arm_e2e fieldSubCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The same source emits to RISC-V** — one source, two backends, both verified. -/
theorem fieldSubCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldSubCom 2))).regs)
        (comRetName fieldSubCom 2)
      = Com.denote fieldSubCom V :=
  com_riscv_e2e fieldSubCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier, as `fieldAddCom_x86_elf`): the same
    source to ELF `.o` bytes via the generic driver. -/
def fieldSubCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldSubCom "field_sub"

/-! ## The borrow chain on the golden path: branchless subtract-with-borrow-out

The companion to `fieldSubCom` (the low word `a - b`) is the **borrow-out** bit —
the other half of a single-limb subtract, and the primitive every multi-limb
subtract / Montgomery reduction threads. It is **branchless in the existing
`reg 64` alphabet** — `regConst`/`xor`/`and`/`or`/`sub`/`shrImm`, every one in
`SupportedOp`. So the borrow rides `com_arm_e2e`/`com_riscv_e2e` with no new
dialect op, no `RegStmt` primitive, no backend change. (On real silicon
ARM `subs`/`sbcs` or RISC-V `sub;sltu` are fewer instructions; this is the
portable, flag-free form the shared all-`reg 64` pipeline emits to both as-is.)

The value step `r.toNat + b.toNat = a.toNat + borrow · 2^64`
(`field_sub_borrow_reconstruct`, the subtract-analogue of
`fieldAdd_carry_reconstruct`) is the borrow-formula correctness: the bit-twiddle
equals `if a < b then 1 else 0`, by `bv_decide`. -/

/-- Borrow-out of `a - b` as a branchless `reg 64` 0/1 value, over args `[a, b]`
    (`a = x1`, `b = x0`):
    `ones := 2^64-1 ; na := a ^ ones (= ~a) ; axb := a ^ b ; naxb := axb ^ ones (= ~(a^b)) ;
     d := a - b ; l := na & b ; rr := naxb & d ; ((na&b) | (naxb&d)) >>> 63`. -/
def fieldBorrowCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- ones = 2^64-1
  .var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- na = a ^ ones   (= ~a)   ;  a = x1 = .there.there.here, ones = .here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there .here)) (.cons .here .nil) }
  -- axb = a ^ b      ;  a = .there.there.there.here, b = .there.there.here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here)))
                    (.cons (.there (.there .here)) .nil) }
  -- naxb = axb ^ ones (= ~(a^b))  ;  axb = .here, ones = .there.there.here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there .here)) .nil) }
  -- d = a - b        ;  a = .there.there.there.there.there.here, b = .there.there.there.there.here
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here)))))
                    (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- l = na & b       ;  na = .there.there.there.here, b = (.there)^5.here
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here)))
                    (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- rr = naxb & d    ;  naxb = .there.there.here, d = .there.here
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there .here)) (.cons (.there .here) .nil) }
  -- u = l | rr       ;  l = .there.here, rr = .here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- borrow = u >>> 63
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
    (.ret .here)))))))))

/-- `fieldBorrowCom` is in the supported straight-line fragment (9 ops, all
    `regConst`/`xor`/`sub`/`and`/`or`/`shrImm`). -/
theorem fieldBorrowCom_ok : ComOK fieldBorrowCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))))))

/-- **Step 2 — value proof, cheap `rfl`.** The borrow source denotes the
    branchless borrow-out expression (all-ALU; the `~x` is `x ^ 0xFF…FF`). -/
theorem fieldBorrowCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldBorrowCom (.cons x0 (.cons x1 .nil))
      = (((x1 ^^^ BitVec.ofNat 64 18446744073709551615) &&& x0)
          ||| (((x1 ^^^ x0) ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x1 - x0)))
          >>> 63 := rfl

/-- **The borrow-out spec.** The branchless borrow expression equals the
    recognizable predicate `if x1 < x0 then 1 else 0` (`a = x1`, `b = x0`),
    by `bv_decide`. This is the correctness oracle for the bit-twiddle. -/
theorem fieldBorrowCom_spec (x0 x1 : BitVec 64) :
    Com.denote fieldBorrowCom (.cons x0 (.cons x1 .nil))
      = (if x1.toNat < x0.toNat then (1 : BitVec 64) else 0) := by
  rw [fieldBorrowCom_denote]
  -- the bit-twiddle equals the unsigned-`<` indicator; `bv_decide` is the oracle.
  -- stated with the BitVec order `x1 < x0` (bv_decide abstracts the Nat-`toNat` `if`),
  -- then converted to the `.toNat` predicate via `BitVec.lt_def`.
  have key : (((x1 ^^^ BitVec.ofNat 64 18446744073709551615) &&& x0)
        ||| (((x1 ^^^ x0) ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x1 - x0)))
        >>> 63 = (if x1 < x0 then (1 : BitVec 64) else 0) := by bv_decide
  rw [key]; simp [BitVec.lt_def]

/-- **The subtract value step that closes the borrow chain**: the low word
    `fieldSubCom` and the borrow-out `fieldBorrowCom` reconstruct the exact
    integer subtraction, `r.toNat + b.toNat = a.toNat + borrow · 2^64`
    (as naturals). The subtract-analogue of `fieldAdd_carry_reconstruct`; the
    borrow-formula correctness is `fieldBorrowCom_spec` (via `bv_decide`). -/
theorem field_sub_borrow_reconstruct (x0 x1 : BitVec 64) :
    (Com.denote fieldSubCom (.cons x0 (.cons x1 .nil))).toNat
      + x0.toNat
      = x1.toNat
      + (Com.denote fieldBorrowCom (.cons x0 (.cons x1 .nil))).toNat * 2 ^ 64 := by
  rw [fieldSubCom_denote, fieldBorrowCom_spec, BitVec.toNat_sub]
  have hx0 : x0.toNat < 2 ^ 64 := x0.isLt
  have hx1 : x1.toNat < 2 ^ 64 := x1.isLt
  split <;> simp_all <;> omega

/-- **The borrow-out emits to AArch64**, discharged by `com_arm_e2e` via the single
    `comToReg_faithful` — branchless borrow over the supported ALU alphabet. -/
theorem fieldBorrowCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldBorrowCom 2))).regs)
        (comRetName fieldBorrowCom 2)
      = Com.denote fieldBorrowCom V :=
  com_arm_e2e fieldBorrowCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The borrow-out emits to RISC-V**, same source, same `comToReg_faithful`. -/
theorem fieldBorrowCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldBorrowCom 2))).regs)
        (comRetName fieldBorrowCom 2)
      = Com.denote fieldBorrowCom V :=
  com_riscv_e2e fieldBorrowCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** for the borrow-out (KAT-gated tier). -/
def fieldBorrowCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldBorrowCom "field_sub_borrow"

end CatCrypt.Crypto.SecureCompilation.FieldSubBorrow
