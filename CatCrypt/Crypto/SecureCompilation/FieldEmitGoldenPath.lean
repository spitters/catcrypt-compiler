/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
import CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo
import Std.Tactic.BVDecide

/-!
# Golden path: field arithmetic as `Com jasminDialect`, emitted by the verified compiler

**This is the canonical pattern for emitting field-arithmetic kernels.** A field
operation is written ONCE as a `Com jasminDialect` source program, proven ONCE against
its value spec, and the verified compiler emits the machine code — to AArch64 *and*
RISC-V — with **no per-kernel backend proof** (`comToReg_faithful` discharges it) and
constant-time by construction.

Contrast the hand-authored leaf approach (`BignumAddEmit`, `Bignum4CondSubEmit`, …),
which hand-writes `List (JInstr 64)` blocks and proves each `runBlock` directly: those
bypass the compiler and are prototypes / KAT oracles only. The canonical artifact is
*generated*, as here.

The recipe (one source → both backends), shown on the field-add core `a + b`:
1. write the op as a `Com jasminDialect Γ (.reg 64)` over the `regArith`/`mulhi`/
   `regConst`/`shrImm` alphabet;
2. `ComOK` (mechanical — one constructor per op) + prove `Com.denote = <spec value>`
   (cheap for the ALU/logic ops the conditional-subtract reduction is built from);
3. `ScalarLinNeutralDemo.com_arm_e2e` / `MultiBackendDemo.com_riscv_e2e` emit the
   verified backend block — both discharged by Step 1's `comToReg_faithful`.

Richer field ops follow the same recipe; only the kernel body changes. Three are
worked below: the conditional-subtract reduction `bCondSub` (all-ALU); the widening
multiply (`mul`/`mulhi` — the high word `mulHiW`, with the integer-product value step
from the `mulx_reconstruct` widening law); and the branchless add-with-carry-out (the
carry chain, in the supported `reg 64` alphabet, with the sum-reconstruction value
step from `BitVec.uaddOverflow`). All lower through the *same* `comToReg_faithful` —
so the field-arithmetic primitives a multi-limb Montgomery multiply needs (widening
product + carry accumulation) all emit to both backends with no new machinery.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

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

/-- **The field-op source.** The modular-add core `a + b` as a one-op
    `Com jasminDialect` over args `[a, b]` — `v2 := a + b; ret v2`. This is the
    *source*; the compiler generates the machine code. -/
def fieldAddCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- The kernel is in the supported straight-line fragment (mechanical). -/
theorem fieldAddCom_ok : ComOK fieldAddCom :=
  ComOK.var (by supported_op) (ComOK.ret _)

/-- The two-input context is all-`reg 64`. -/
theorem allReg64_two : AllReg64 ([.reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu; rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · exact absurd h List.not_mem_nil

/-- **Step 2 — the value proof, once, at the source level.** The source `Com.denote` is
    the field-add value `a + b`. A cheap `rfl` (the ALU/logic ops reduce structurally —
    unlike a brute-force reduction through the whole MLIR machinery). -/
theorem fieldAddCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldAddCom (.cons x0 (.cons x1 .nil)) = x1 + x0 := rfl

/-- **The emitted AArch64 block computes the field op.** Run from a matching machine
    state, the compiler-generated AArch64 code reads back `Com.denote` — no hand-written
    `JInstr`, no per-kernel backend proof (`com_arm_e2e` discharges it via
    `comToReg_faithful`). -/
theorem fieldAddCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldAddCom 2))).regs)
        (comRetName fieldAddCom 2)
      = Com.denote fieldAddCom V :=
  com_arm_e2e fieldAddCom_ok allReg64_two V s hs

/-- **The same source emits to RISC-V** — one source, two backends, both verified, both
    discharged by the single `comToReg_faithful`. -/
theorem fieldAddCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldAddCom 2))).regs)
        (comRetName fieldAddCom 2)
      = Com.denote fieldAddCom V :=
  com_riscv_e2e fieldAddCom_ok allReg64_two V s hs

/-- **The dominant x86 owned-emit leg** — the *same* `Com` source compiled to ELF `.o`
    bytes via the generic driver `compileComToElf` (`Com.toLprogPhysAbi` → encoder; the
    path `bench/{ascon,chacha,keccak}_compare` and `Bignum4AddArrAbiDemo` use).

    **Honest proof tier** (see `EMIT_PROVENANCE.md` / `ARCHITECTURE.md`): unlike the
    AArch64/RISC-V legs above — which carry the `comToReg_faithful` *denote = spec*
    lowering theorem — this x86 leg is **KAT-gated** (`decode ∘ encode = id` against the
    Jasmin x86 model + KAT vs reference), NOT yet carried by a `Com → x86` faithfulness
    theorem. It is the shipped/benchmarked scalar path; its correctness rests on the
    encoder round-trip + the external KAT, not a per-kernel denotation proof. -/
def fieldAddCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldAddCom "field_add"

/-! ## A richer golden field op: the branchless GF(251) conditional-subtract reduce

`bCondSub251 a = (a ≥ 251 ? a - 251 : a)` for `a ∈ [0, 501]` — the all-ALU reduction
tail the Solinas GF(251) multiply ends with (MQOM/SDitH). Branch-free via the
conditional-add-back mask `t := a - 251 ; m := 0 - (t >>> 63) ; r := t + (251 & m)`:
`regConst`/`regArith {sub, and, add}`/`shrImm`, all in `SupportedOp`, so the source
denote reduces by cheap `rfl` (no `mul`) and `com_arm_e2e`/`com_riscv_e2e` emit both
backends from the one source. The same recipe as `fieldAddCom`, only the body grows. -/

/-- `c251 := 251 ; t := a - c251 ; bit := t >>> 63 ; c0 := 0 ; m := c0 - bit ;
    masked := m & c251 ; r := t + masked ; ret r` over arg `[a]`. -/
def fieldCondSub251Com : Com jasminDialect [.reg 64] (.reg 64) :=
  .var { op := .regConst 64 251, retTy_eq := rfl, args := .nil }
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }              -- a - c251
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }  -- t >>> 63
  (.var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }              -- c0 - bit
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here
            (.cons (.there (.there (.there (.there .here)))) .nil) }     -- m & c251
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
            (.cons .here .nil) }                                         -- t + masked
    (.ret .here)))))))

/-- The single-input context is all-`reg 64`. -/
theorem allReg64_one : AllReg64 ([.reg 64] : Ctxt jasminDialect) := by
  intro u hu; rcases List.mem_cons.mp hu with h | h
  · exact h
  · exact absurd h List.not_mem_nil

/-- `fieldCondSub251Com` is in the supported straight-line fragment (one constructor
    per op: regConst, sub, shrImm, regConst, sub, and, add). -/
theorem fieldCondSub251Com_ok : ComOK fieldCondSub251Com := by
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  refine ComOK.var (by supported_op) ?_
  exact ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof at the source, cheap `rfl`** (all-ALU, no `mul`). -/
theorem fieldCondSub251Com_denote (a : BitVec 64) :
    Com.denote fieldCondSub251Com (.cons a .nil)
      = (a - (251 : BitVec 64))
          + (((0 : BitVec 64) - ((a - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64)) := rfl

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem fieldCondSub251Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldCondSub251Com 1))).regs)
        (comRetName fieldCondSub251Com 1)
      = Com.denote fieldCondSub251Com V :=
  com_arm_e2e fieldCondSub251Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, discharged by the same `comToReg_faithful`. -/
theorem fieldCondSub251Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldCondSub251Com 1))).regs)
        (comRetName fieldCondSub251Com 1)
      = Com.denote fieldCondSub251Com V :=
  com_riscv_e2e fieldCondSub251Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier, as `fieldAddCom_x86_elf`): the same
    source to ELF `.o` bytes via the generic driver. -/
def fieldCondSub251Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldCondSub251Com "field_condsub251"

/-! ## A `mul`-based golden field op: the widening 64×64→128 multiply

The carry-free ALU alphabet (`add`/`sub`/`and`/…) cannot express a multi-limb
multiply: the widening product needs the **high** word `mulhi` alongside the
**low** word `mul` (the `MULX`/`UMULH` pair). Both are in `SupportedOp`, so both
lower — to AArch64 (`mul`/`umulh`) and RISC-V (`mul`/`mulhu`) — through the same
`comToReg_faithful`, exactly as the ALU ops do.

Two things matter for the `mul` case that are trivial for the ALU case:

* **the denote step is still a cheap `rfl`** — `mulhi`'s denotation is `mulHiW`
  (the high word of `a * b`), and `Com.denote` reduces structurally to it; the
  `a.toNat * b.toNat / 2^w` arithmetic is *not* forced (it stays symbolic), so
  there is no `whnf` blow-up;
* **the value step** — that the two emitted words reassemble to the exact
  integer product — is the `MontMulFragmentDemo.mulx_reconstruct` widening law
  over `mulHiW`, the carry-propagation fact #474 could not state with the
  carry-free alphabet. This closes the golden path for `mul`, not just ALU. -/

/-- Low word of `a * b` (the `MUL`/`mullo`), as a one-op `Com` over `[a, b]`. -/
def fieldMulLoCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .mul 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- High word of `a * b` (the `UMULH`/`mulhu`), as a one-op `Com` over `[a, b]`. -/
def fieldMulHiCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .mulhi 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)

/-- Both kernels are in the supported straight-line fragment (`mul`, `mulhi`). -/
theorem fieldMulLoCom_ok : ComOK fieldMulLoCom :=
  ComOK.var (by supported_op) (ComOK.ret _)

theorem fieldMulHiCom_ok : ComOK fieldMulHiCom :=
  ComOK.var (by supported_op) (ComOK.ret _)

/-- **Step 2 — value proof, cheap `rfl`.** The low-word source denotes `a * b`. -/
theorem fieldMulLoCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldMulLoCom (.cons x0 (.cons x1 .nil)) = x1 * x0 := rfl

/-- **Step 2 — value proof, cheap `rfl`.** The high-word source denotes
    `mulHiW a b` — `mulhi` reduces structurally; the `/2^w` stays symbolic. -/
theorem fieldMulHiCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldMulHiCom (.cons x0 (.cons x1 .nil)) = mulHiW x1 x0 := rfl

/-- **The `mul` value step that closes the golden path**: the low and high
    output words of the two emitted Coms reassemble to the exact 128-bit integer
    product, `lo + hi · 2^64 = a · b` (as naturals). This is the widening law
    `MontMulFragmentDemo.mulx_reconstruct` over `mulHiW` — the carry-propagation
    correctness fact the carry-free alphabet could not state. -/
theorem fieldMul_widening (x0 x1 : BitVec 64) :
    (Com.denote fieldMulLoCom (.cons x0 (.cons x1 .nil))).toNat
      + (Com.denote fieldMulHiCom (.cons x0 (.cons x1 .nil))).toNat * 2 ^ 64
      = x1.toNat * x0.toNat := by
  rw [fieldMulLoCom_denote, fieldMulHiCom_denote]
  exact MontMulFragmentDemo.mulx_reconstruct x1 x0

/-- **The widening-`mul` low word emits to AArch64** (`mul`), discharged by
    `com_arm_e2e` via the single `comToReg_faithful`. -/
theorem fieldMulLoCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldMulLoCom 2))).regs)
        (comRetName fieldMulLoCom 2)
      = Com.denote fieldMulLoCom V :=
  com_arm_e2e fieldMulLoCom_ok allReg64_two V s hs

/-- **The widening-`mul` low word emits to RISC-V** (`mul`), same source, same
    `comToReg_faithful`. -/
theorem fieldMulLoCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldMulLoCom 2))).regs)
        (comRetName fieldMulLoCom 2)
      = Com.denote fieldMulLoCom V :=
  com_riscv_e2e fieldMulLoCom_ok allReg64_two V s hs

/-- **The widening-`mul` high word emits to AArch64** (`umulh`), discharged by
    `com_arm_e2e` — the high-multiply op lowers like any other `SupportedOp`. -/
theorem fieldMulHiCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldMulHiCom 2))).regs)
        (comRetName fieldMulHiCom 2)
      = Com.denote fieldMulHiCom V :=
  com_arm_e2e fieldMulHiCom_ok allReg64_two V s hs

/-- **The widening-`mul` high word emits to RISC-V** (`mulhu`), same source. -/
theorem fieldMulHiCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldMulHiCom 2))).regs)
        (comRetName fieldMulHiCom 2)
      = Com.denote fieldMulHiCom V :=
  com_riscv_e2e fieldMulHiCom_ok allReg64_two V s hs

/-- **The x86 owned-emit leg** for the widening multiply (KAT-gated tier): the
    same `mul`/`mulhi` sources to ELF `.o` bytes via the generic driver. -/
def fieldMulLoCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldMulLoCom "field_mul_lo"

def fieldMulHiCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldMulHiCom "field_mul_hi"

/-! ## The carry chain on the golden path: branchless add-with-carry-out

The companion to `fieldAddCom` (the low word `a + b`) is the **carry-out** bit —
the other half of a single-limb add, and the primitive every multi-limb add/
Montgomery accumulation threads. The dialect *does* have flag-style carry ops
(`addCarryLo`/`addCarryHi`), but they take a `reg 1` carry and so fall outside
`SupportedOp`/`ComOK` (which is all-`reg 64`). They are not needed: the carry-out
is **branchless in the existing `reg 64` alphabet** —

```
s := a + b ;  ones := 0xFFFF…FF ;  ns := s ^ ones (= ~s) ;
cout := ((a & b) | ((a | b) & ns)) >>> 63
```

— `add`/`xor`/`and`/`or`/`shrImm`/`regConst`, every one in `SupportedOp`. So the
carry rides `com_arm_e2e`/`com_riscv_e2e` with **no new dialect op, no `RegStmt`
primitive, no backend change, no faithfulness generalisation**. (On real silicon
ARM `adcs` / RISC-V `add;sltu` are fewer instructions; this is the portable,
flag-free form that the shared all-`reg 64` pipeline emits to both backends as-is.)

The value step `lo + cout · 2^64 = a + b` (`fieldAdd_carry_reconstruct`, the
add-analogue of `fieldMul_widening`) is the carry-formula correctness: the
bit-twiddle equals `uaddOverflow`, by `bv_decide`. -/

/-- Carry-out of `a + b` as a branchless `reg 64` 0/1 value, over args `[a, b]`:
    `s := a+b ; ones := 2^64-1 ; ns := s ^ ones ; ((a&b) | ((a|b)&ns)) >>> 63`. -/
def fieldAddCarryCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- s = x1 + x0
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }
  -- ones = 2^64-1
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- ns = s ^ ones   (= ~s)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- ab_and = x1 & x0
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- ab_or = x1 | x0
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here)))))
                    (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- t = ab_or & ns
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there .here)) .nil) }
  -- u = ab_and | t
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there (.there .here)) (.cons .here .nil) }
  -- cout = u >>> 63
  (.var { op := .shrImm 64 63, retTy_eq := rfl, args := .cons .here .nil }
    (.ret .here))))))))

/-- `fieldAddCarryCom` is in the supported straight-line fragment (8 ops, all
    `add`/`xor`/`and`/`or`/`shrImm`/`regConst`). -/
theorem fieldAddCarryCom_ok : ComOK fieldAddCarryCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))

/-- **Step 2 — value proof, cheap `rfl`.** The carry source denotes the
    branchless carry-out expression (all-ALU; the `~s` is `s ^ 0xFF…FF`). -/
theorem fieldAddCarryCom_denote (x0 x1 : BitVec 64) :
    Com.denote fieldAddCarryCom (.cons x0 (.cons x1 .nil))
      = ((x1 &&& x0) ||| ((x1 ||| x0) &&& ((x1 + x0) ^^^ BitVec.ofNat 64 18446744073709551615)))
          >>> 63 := rfl

/-- **The add value step that closes the carry chain**: the low word `fieldAddCom`
    and the carry-out `fieldAddCarryCom` reassemble to the exact integer sum,
    `lo + cout · 2^64 = a + b` (as naturals). The add-analogue of
    `fieldMul_widening`; the carry-formula correctness is `bv_decide` (the
    bit-twiddle equals `BitVec.uaddOverflow`). -/
theorem fieldAdd_carry_reconstruct (x0 x1 : BitVec 64) :
    (Com.denote fieldAddCom (.cons x0 (.cons x1 .nil))).toNat
      + (Com.denote fieldAddCarryCom (.cons x0 (.cons x1 .nil))).toNat * 2 ^ 64
      = x1.toNat + x0.toNat := by
  rw [fieldAddCom_denote, fieldAddCarryCom_denote]
  have h : (((x1 &&& x0) ||| ((x1 ||| x0) &&& ((x1 + x0) ^^^ BitVec.ofNat 64 18446744073709551615)))
        >>> 63)
      = (if x1.uaddOverflow x0 then (1 : BitVec 64) else 0) := by bv_decide
  have ho := BitVec.uaddOverflow.eq_1 x1 x0
  rw [BitVec.toNat_add, h]
  split <;> simp_all
  omega

/-- **The carry-out emits to AArch64**, discharged by `com_arm_e2e` via the single
    `comToReg_faithful` — branchless carry over the supported ALU alphabet. -/
theorem fieldAddCarryCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldAddCarryCom 2))).regs)
        (comRetName fieldAddCarryCom 2)
      = Com.denote fieldAddCarryCom V :=
  com_arm_e2e fieldAddCarryCom_ok allReg64_two V s hs

/-- **The carry-out emits to RISC-V**, same source, same `comToReg_faithful`. -/
theorem fieldAddCarryCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldAddCarryCom 2))).regs)
        (comRetName fieldAddCarryCom 2)
      = Com.denote fieldAddCarryCom V :=
  com_riscv_e2e fieldAddCarryCom_ok allReg64_two V s hs

/-- **The x86 owned-emit leg** for the carry-out (KAT-gated tier). -/
def fieldAddCarryCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldAddCarryCom "field_add_carry"

/-! ## The capstone: a multi-limb add composed from the emitted primitives

The single-limb primitives above compose into multi-limb arithmetic with **no new
machinery** — only more `Com`s. The add-with-carry-*in* low word `r := a + b + cin`
(`fieldAdcCom`) is the iterated step of every multi-limb adder; together with
`fieldAddCom` (low word) and `fieldAddCarryCom` (carry-out) it gives a complete limb.
`field_two_limb_add` then shows the three emitted Coms reconstruct a 2-limb integer
sum, the carry from limb 0 threading into limb 1 through the emitted `fieldAdcCom`. -/

/-- The 3-input context `[a, b, cin]` is all-`reg 64`. -/
theorem allReg64_three : AllReg64 ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu
  rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact h
      · exact absurd h List.not_mem_nil

/-- **Add-with-carry-in, low word**: `r := a + b + cin` over `[a, b, cin]` (cin a
    reg64 0/1). Two `add`s — the iterated step of a multi-limb adder. -/
def fieldAdcCom : Com jasminDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- t = a + b      (a = .here, b = .there.here)
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
  -- r = t + cin    (t = .here, cin = .there.there.there.here)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
    (.ret .here))

theorem fieldAdcCom_ok : ComOK fieldAdcCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))

/-- **Step 2 — value proof, cheap `rfl`.** `fieldAdcCom` denotes `(a + b) + cin`. -/
theorem fieldAdcCom_denote (a b cin : BitVec 64) :
    Com.denote fieldAdcCom (.cons a (.cons b (.cons cin .nil))) = (a + b) + cin := rfl

/-- **`fieldAdcCom` emits to AArch64** (two `add`s), via `com_arm_e2e`. -/
theorem fieldAdcCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldAdcCom 3))).regs)
        (comRetName fieldAdcCom 3)
      = Com.denote fieldAdcCom V :=
  com_arm_e2e fieldAdcCom_ok allReg64_three V s hs

/-- **`fieldAdcCom` emits to RISC-V**, same source, same `comToReg_faithful`. -/
theorem fieldAdcCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldAdcCom 3))).regs)
        (comRetName fieldAdcCom 3)
      = Com.denote fieldAdcCom V :=
  com_riscv_e2e fieldAdcCom_ok allReg64_three V s hs

/-- **The x86 owned-emit leg** for add-with-carry-in (KAT-gated tier). -/
def fieldAdcCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldAdcCom "field_adc"

/-- **The 2-limb add capstone.** For `a = a0 + a1·2^64`, `b = b0 + b1·2^64`, the three
    EMITTED primitives reconstruct the exact integer sum: low word `r0` from
    `fieldAddCom`, carry `c0` from `fieldAddCarryCom`, carried limb `r1` from the emitted
    `fieldAdcCom` (so the limb-0 carry threads into limb 1 *through emitted code*), and the
    final carry the high half of `a1+b1+c0`. Closes by the limb-0 reconstruction law
    `fieldAdd_carry_reconstruct` and the carry-propagation arithmetic (`omega`). The
    primitives compose into multi-limb arithmetic with no new compiler machinery. -/
theorem field_two_limb_add (a0 a1 b0 b1 : BitVec 64) :
    let r0 := Com.denote fieldAddCom (.cons b0 (.cons a0 .nil))
    let c0 := Com.denote fieldAddCarryCom (.cons b0 (.cons a0 .nil))
    let r1 := Com.denote fieldAdcCom (.cons a1 (.cons b1 (.cons c0 .nil)))
    (a0.toNat + a1.toNat * 2 ^ 64) + (b0.toNat + b1.toNat * 2 ^ 64)
      = r0.toNat + r1.toNat * 2 ^ 64
          + ((a1.toNat + b1.toNat + c0.toNat) / 2 ^ 64) * 2 ^ 128 := by
  intro r0 c0 r1
  have hrec0 : r0.toNat + c0.toNat * 2 ^ 64 = a0.toNat + b0.toNat :=
    fieldAdd_carry_reconstruct b0 a0
  have hr1 : r1.toNat = (a1.toNat + b1.toNat + c0.toNat) % 2 ^ 64 := by
    show (Com.denote fieldAdcCom _).toNat = _
    rw [fieldAdcCom_denote, BitVec.toNat_add, BitVec.toNat_add]
    omega
  omega

end CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
