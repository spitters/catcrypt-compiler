/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
public import CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
public import CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo

/-!
# Golden path, step 1: GF(251) add-with-reduce `(a + b) mod 251` as `Com jasminDialect`

The all-ALU GF(251) modular add `(a + b) mod 251` for `a, b ∈ [0, 250]`, written
ONCE as a `Com jasminDialect` source over args `[a, b]` and emitted by the verified
compiler to AArch64 *and* RISC-V (denote = spec via `comToReg_faithful`, no per-kernel
backend proof) plus the x86 ELF leg via `compileComToElf`.

This composes the field-add core `s := a + b` (one `regArith .add`) with the exact
branchless GF(251) conditional-subtract-251 reduction from
`FieldEmitGoldenPath.fieldCondSub251Com`:

```
s      := a + b
c251   := 251
t      := s - c251
bit    := t >>> 63
c0     := 0
m      := c0 - bit
masked := m & c251
r      := t + masked        -- r = (a + b) mod 251 for a, b ∈ [0, 250]
ret r
```

Because the input `s` of the reduction tail sits in the *same* relative de-Bruijn
slot that the standalone `fieldCondSub251Com`'s input `a` sat in (one binding below
`c251`), the condsub chain's de-Bruijn indices are *identical* to that template —
only the leading `s := a + b` binding is new. Eight bindings total, all in the
straight-line `SupportedOp` fragment, so the denote is a cheap `rfl` and
`com_arm_e2e`/`com_riscv_e2e` emit both backends from the one source.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenAddMod

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

/-- **The GF(251) modular-add source.** `s := a + b` (one `regArith .add`) followed by
    the branchless conditional-subtract-251 reduction applied to `s` — `(a + b) mod 251`
    for `a, b ∈ [0, 250]`, as a `Com jasminDialect` over args `[a, b]`. Eight bindings.

    `s := a + b ; c251 := 251 ; t := s - c251 ; bit := t >>> 63 ; c0 := 0 ;
     m := c0 - bit ; masked := m & c251 ; r := t + masked ; ret r`. -/
def fieldAddMod251Com : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there .here) (.cons .here .nil) }               -- s := a + b
  (.var { op := .regConst 64 251, retTy_eq := rfl, args := .nil }
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }              -- s - c251
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
    (.ret .here))))))))

/-- The two-input context is all-`reg 64`. -/
theorem allReg64_two : AllReg64 ([.reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu; rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · exact absurd h List.not_mem_nil

/-- `fieldAddMod251Com` is in the supported straight-line fragment (one constructor
    per op: add, regConst, sub, shrImm, regConst, sub, and, add). -/
theorem fieldAddMod251Com_ok : ComOK fieldAddMod251Com := by
  refine ComOK.var (Or.inl ⟨.add, rfl, Or.inl rfl⟩) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inr ⟨251, rfl⟩))) ?_
  refine ComOK.var (Or.inl ⟨.sub, rfl, Or.inr (Or.inl rfl)⟩) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inl ⟨63, Or.inl rfl⟩))) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inr ⟨0, rfl⟩))) ?_
  refine ComOK.var (Or.inl ⟨.sub, rfl, Or.inr (Or.inl rfl)⟩) ?_
  refine ComOK.var (Or.inl ⟨.and, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩) ?_
  exact ComOK.var (Or.inl ⟨.add, rfl, Or.inl rfl⟩) (ComOK.ret _)

/-- **Step 2 — value proof at the source, cheap `rfl`** (all-ALU, no `mul`). The source
    denotes the conditional-subtract reduction of `s := b + a`. -/
theorem fieldAddMod251Com_denote (x0 x1 : BitVec 64) :
    Com.denote fieldAddMod251Com (.cons x0 (.cons x1 .nil))
      = ((x1 + x0) - (251 : BitVec 64))
          + (((0 : BitVec 64) - (((x1 + x0) - (251 : BitVec 64)) >>> 63))
              &&& (251 : BitVec 64)) := rfl

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem fieldAddMod251Com_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fieldAddMod251Com 2))).regs)
        (comRetName fieldAddMod251Com 2)
      = Com.denote fieldAddMod251Com V :=
  com_arm_e2e fieldAddMod251Com_ok allReg64_two V s hs

/-- **Emitted RISC-V** — same source, discharged by the same `comToReg_faithful`. -/
theorem fieldAddMod251Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fieldAddMod251Com 2))).regs)
        (comRetName fieldAddMod251Com 2)
      = Com.denote fieldAddMod251Com V :=
  com_riscv_e2e fieldAddMod251Com_ok allReg64_two V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier, as in `FieldEmitGoldenPath`): the same
    source to ELF `.o` bytes via the generic driver `compileComToElf`. -/
def fieldAddMod251Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 fieldAddMod251Com "field_addmod251"

end CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenAddMod
