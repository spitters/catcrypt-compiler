/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFront
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontInstances
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontGf256
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenAddMod
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenGf256

/-!
# The relational front, all the way to the emitted machine code

`RelationalFront.lean` ties an abstract crypto operation `op` to a byte-level
realization `bop` (the `EndoOpRealization` commuting square) and to an emitted
`Com jasminDialect` whose denotation **is** `bop` (the `RealizedKernel.com_denotes_bop`
IR seam). The golden-path modules carry the **machine** half: the emitted AArch64 /
RISC-V code's result register holds `Com.denote com V` — `fieldAddCom_arm_e2e`,
`fieldAddMod251Com_arm_e2e`, `gf256MulBuilt_arm_e2e` (and the `_riscv_e2e`
analogues), all discharged by the single `comToReg_faithful`.

This module **closes the loop**: it threads the relational tie through the IR seam
*and through the verified backend*, so the abstract source operation is computed,
register-for-register, by the EMITTED machine bytes:

```
  op a b            (abstract source, e.g. a field/group law)
   │  enc
   ▼
  bop (enc a) (enc b)          R.realization.commutes        ── relational tie
   │
   ▼
  Com.denote R.com …           R.com_denotes_bop             ── IR seam
   │
   ▼
  <emitted AArch64 / RISC-V result register>
                               <com>_arm_e2e / <com>_riscv_e2e
                                                             ── verified backend
```

## What this connects (and the conditioned scope)

The end-to-end statement holds **exactly for `RealizedKernel`s whose `com` is
backed by a golden-path machine-emit theorem** (`com_arm_e2e`/`com_riscv_e2e` via
`comToReg_faithful`). The generic bridge `RealizedKernel.mres_computes_bop` /
`mres_computes_source` is parametric in *any* such backend machine-result
function; the three worked kernels take the same chain on their concrete
backends:

* `fieldAddRealizedKernel` — `BitVec 64` add, `enc = id` (golden `fieldAddCom`);
* `addMod251RealizedKernel` — `ZMod 251` add, injective-not-onto residue encoding
  (golden `fieldAddMod251Com`);
* `gf256MulRealizedKernel` — `GF(2^8)` (Rijndael) byte multiply, injective-not-onto
  byte zero-extension (golden 91-binding `gf256MulBuilt`).

So **both** a prime-field add and a characteristic-2 field multiply (the
AES/FAEST structure), through genuine injective-not-surjective serializations,
run register-for-register to the emitted AArch64 *and* RISC-V code.

It does **not** hold for a `RealizedKernel` whose `com` lacks a
`comToReg_faithful`-backed `*_e2e` theorem — there is then no machine theorem to
thread. The relational front-end and the IR seam (`RealizedKernel`,
`spec_eq_transfers_to_emit`) apply to *any* realized kernel; the **machine**
corollary applies to the golden-path-backed ones (which, for the worked
instances, is all of them).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenAddMod
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenGf256
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-! ## The generic relational→machine bridge

Every golden-path `*_arm_e2e` / `*_riscv_e2e` theorem has the same shape: from a
machine state whose registers hold the valuation, the result register reads back
`Com.denote com V`. We abstract that as a *machine-result function*
`mres : Valuation → BitVec 64` with `h_emit : ∀ V, mres V = Com.denote R.com V`,
and thread it through the `com_denotes_bop` IR seam and the `realization.commutes`
tie (`mres_computes_bop` / `mres_computes_source`) — reusable, backend-agnostic
infrastructure. The per-kernel, per-backend corollaries below take the same chain
directly on each concrete backend's `runOps …` expression (`*_arm_e2e`/`*_riscv_e2e`
supplying `h_emit`).

The valuation `.cons (enc b) (.cons (enc a) .nil)` feeds the encoded operands in the
order `(enc b, enc a)`: the seam `com_denotes_bop x0 x1 = bop x1 x0` flips operand
order, so this orientation yields `bop (enc a) (enc b)`. -/

namespace RealizedKernel
variable {A : Type}

/-- **Relational tie threaded through the IR seam.** Running the EMITTED `Com` on
    the encoded operands `(enc b, enc a)` computes the realization's `bop` applied
    to the encoded inputs in source order, `bop (enc a) (enc b)`. This is
    `com_denotes_bop` specialized to the encoded valuation. -/
theorem denote_at_enc {op : A → A → A}
    (R : RealizedKernel op) (a b : A) :
    Com.denote R.com
        (.cons (R.realization.enc b) (.cons (R.realization.enc a) .nil))
      = R.bop (R.realization.enc a) (R.realization.enc b) :=
  R.com_denotes_bop _ _

/-- **The generic relational source → emitted machine corollary (operator form).**
    Given any machine-result function `mres` that the backend proves equal to
    `Com.denote R.com` (the golden-path `*_e2e` shape), `mres` run on the encoded
    operands `(enc b, enc a)` computes the realization's `bop` on the encoded source
    operands. Threads `h_emit` (the backend `comToReg_faithful` lowering) with
    `denote_at_enc` (the IR seam). -/
theorem mres_computes_bop {op : A → A → A}
    (R : RealizedKernel op)
    (mres : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect) → BitVec 64)
    (h_emit : ∀ V, mres V = Com.denote R.com V)
    (a b : A) :
    mres (.cons (R.realization.enc b) (.cons (R.realization.enc a) .nil))
      = R.bop (R.realization.enc a) (R.realization.enc b) := by
  rw [h_emit, R.denote_at_enc]

/-- **The end-to-end capstone (source form).** The encoding of the abstract source
    result `op a b` equals the value the emitted machine code computes on the
    encoded operands. Composes the realization's commuting square
    `enc (op a b) = bop (enc a) (enc b)` with `mres_computes_bop`. This is the
    abstract source operation, run through the verified compiler to machine code. -/
theorem mres_computes_source {op : A → A → A}
    (R : RealizedKernel op)
    (mres : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect) → BitVec 64)
    (h_emit : ∀ V, mres V = Com.denote R.com V)
    (a b : A) :
    R.realization.enc (op a b)
      = mres (.cons (R.realization.enc b) (.cons (R.realization.enc a) .nil)) := by
  rw [R.realization.commutes, R.mres_computes_bop mres h_emit]

end RealizedKernel

/-! ## Instantiation 1: `BitVec 64` add (`fieldAddRealizedKernel`, `enc = id`)

The emitted machine code is the golden-path `fieldAddCom`. The backend equality is
`fieldAddCom_arm_e2e` / `fieldAddCom_riscv_e2e`; threading it through `denote_at_enc`
gives the operator form, and through `realization.commutes` the source form. -/

/-- **`fieldAdd` source → emitted AArch64 (end-to-end).** The encoded source result
    `a + b` (here `enc = id`) equals the result register of the COMPILER-EMITTED
    AArch64 block run on the encoded operands `(enc b, enc a)`. -/
theorem fieldAdd_source_eq_arm (a b : BitVec 64)
    (s : BState) (hs : s.regs = envOf 2
      ((.cons (fieldAddRealizedKernel.realization.enc b)
        (.cons (fieldAddRealizedKernel.realization.enc a) .nil) :
          Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)))) :
    fieldAddRealizedKernel.realization.enc ((fun x y : BitVec 64 => x + y) a b)
      = ((ComToArm.armTarget.runOps s
          (ComToArm.armTarget.compile (comToRegProg fieldAddCom 2))).regs)
          (comRetName fieldAddCom 2) := by
  rw [fieldAddRealizedKernel.realization.commutes]
  exact ((fieldAddCom_arm_e2e _ s hs).trans (fieldAddCom_denote _ _)).symm

/-- **`fieldAdd` source → emitted RISC-V (end-to-end).** RISC-V analogue. -/
theorem fieldAdd_source_eq_riscv (a b : BitVec 64)
    (s : RState64) (hs : s.regs = envOf 2
      ((.cons (fieldAddRealizedKernel.realization.enc b)
        (.cons (fieldAddRealizedKernel.realization.enc a) .nil) :
          Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)))) :
    fieldAddRealizedKernel.realization.enc ((fun x y : BitVec 64 => x + y) a b)
      = ((RegToRiscv.rvTarget.runOps s
          (RegToRiscv.rvTarget.compile (comToRegProg fieldAddCom 2))).regs)
          (comRetName fieldAddCom 2) := by
  rw [fieldAddRealizedKernel.realization.commutes]
  exact ((fieldAddCom_riscv_e2e _ s hs).trans (fieldAddCom_denote _ _)).symm

/-! ## Instantiation 2: `ZMod 251` add (`addMod251RealizedKernel`)

A genuine **prime-field** kernel: `op = (· + ·)` on `ZMod 251` with an
injective-not-surjective residue encoding, emitted as `fieldAddMod251Com`. The
machine theorems are `fieldAddMod251Com_arm_e2e` / `_riscv_e2e`. -/

/-- **`F_251` add source → emitted AArch64 (end-to-end).** The encoded abstract
    `ZMod 251` sum equals the result register of the emitted AArch64 block — the
    prime-field add, run through the verified compiler. -/
theorem addMod251_source_eq_arm (a b : ZMod 251)
    (s : BState) (hs : s.regs = envOf 2
      ((.cons (addMod251RealizedKernel.realization.enc b)
        (.cons (addMod251RealizedKernel.realization.enc a) .nil) :
          Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)))) :
    addMod251RealizedKernel.realization.enc ((fun x y : ZMod 251 => x + y) a b)
      = ((ComToArm.armTarget.runOps s
          (ComToArm.armTarget.compile (comToRegProg fieldAddMod251Com 2))).regs)
          (comRetName fieldAddMod251Com 2) := by
  rw [addMod251RealizedKernel.realization.commutes]
  exact ((FieldEmitGoldenAddMod.fieldAddMod251Com_arm_e2e _ s hs).trans
    (fieldAddMod251Com_denote _ _)).symm

/-- **`F_251` add source → emitted RISC-V (end-to-end).** RISC-V analogue. -/
theorem addMod251_source_eq_riscv (a b : ZMod 251)
    (s : RState64) (hs : s.regs = envOf 2
      ((.cons (addMod251RealizedKernel.realization.enc b)
        (.cons (addMod251RealizedKernel.realization.enc a) .nil) :
          Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)))) :
    addMod251RealizedKernel.realization.enc ((fun x y : ZMod 251 => x + y) a b)
      = ((RegToRiscv.rvTarget.runOps s
          (RegToRiscv.rvTarget.compile (comToRegProg fieldAddMod251Com 2))).regs)
          (comRetName fieldAddMod251Com 2) := by
  rw [addMod251RealizedKernel.realization.commutes]
  exact ((FieldEmitGoldenAddMod.fieldAddMod251Com_riscv_e2e _ s hs).trans
    (fieldAddMod251Com_denote _ _)).symm

/-! ## Instantiation 3: `GF(2⁸)` multiply (`gf256MulRealizedKernel`)

The **characteristic-2** customer — the AES/FAEST Rijndael field byte multiply,
emitted as the 91-binding `gf256MulBuilt`, with an injective-not-surjective byte
zero-extension encoding. The machine theorems are `gf256MulBuilt_arm_e2e` /
`_riscv_e2e`. This shows the relational→machine loop closes over a *binary* field
multiply, not just additions. -/

/-- **`GF(2^8)` multiply source → emitted AArch64 (end-to-end).** The zero-extended
    abstract Rijndael byte product equals the result register of the emitted 91-binding
    AArch64 block — a characteristic-2 field multiply, run through the verified
    compiler to machine code. -/
theorem gf256Mul_source_eq_arm (a b : BitVec 8)
    (s : BState) (hs : s.regs = envOf 2
      ((.cons (gf256MulRealizedKernel.realization.enc b)
        (.cons (gf256MulRealizedKernel.realization.enc a) .nil) :
          Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)))) :
    gf256MulRealizedKernel.realization.enc (gf256MulByte a b)
      = ((ComToArm.armTarget.runOps s
          (ComToArm.armTarget.compile (comToRegProg gf256MulBuilt 2))).regs)
          (comRetName gf256MulBuilt 2) := by
  rw [gf256MulRealizedKernel.realization.commutes]
  exact ((gf256MulBuilt_arm_e2e _ s hs).trans (gf256MulBuilt_denote_gf256Ref _ _)).symm

/-- **`GF(2^8)` multiply source → emitted RISC-V (end-to-end).** RISC-V analogue. -/
theorem gf256Mul_source_eq_riscv (a b : BitVec 8)
    (s : RState64) (hs : s.regs = envOf 2
      ((.cons (gf256MulRealizedKernel.realization.enc b)
        (.cons (gf256MulRealizedKernel.realization.enc a) .nil) :
          Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)))) :
    gf256MulRealizedKernel.realization.enc (gf256MulByte a b)
      = ((RegToRiscv.rvTarget.runOps s
          (RegToRiscv.rvTarget.compile (comToRegProg gf256MulBuilt 2))).regs)
          (comRetName gf256MulBuilt 2) := by
  rw [gf256MulRealizedKernel.realization.commutes]
  exact ((gf256MulBuilt_riscv_e2e _ s hs).trans (gf256MulBuilt_denote_gf256Ref _ _)).symm

end CatCrypt.Crypto.SecureCompilation.RelationalFront
