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
# Golden path: a bounded **public** variable-distance shift, emitted unchanged

A *variable-distance* shift `a >>> n` (the amount in a register, not an immediate)
is the one scalar primitive the width-64 emit alphabet does not reach directly:
`regArith .shr`/`.shl` are deliberately absent from `SupportedOp`, and adding a
register-amount shift op would need a backend extension (a `lsrv`/`srl` lowering),
as documented in `VarShiftGoldenPath`.

**This file closes the gap for the useful case — a public amount bounded to a small
fixed set — with NO backend change.** When the amount is public and bounded, the
shift is expressible *entirely in the existing width-64 `SupportedOp` alphabet*
(`regArith {sub,or,and,xor}`, `shrImm`, `regConst`) as a **constant-time
mask-select of immediate shifts**: evaluate each immediate-shift candidate `a >>> i`
and a branchless equality mask `eqMask_i = (n == i ? allOnes : 0)`, then
`result = OR_i (a>>>i &&& eqMask_i)`. Every op is already `SupportedOp`, so
`boundedShrCom` rides the *unchanged* `com_arm_e2e` / `com_riscv_e2e` golden path —
it EMITS to AArch64, RISC-V, and x86 with no new dialect op, no `RegStmt`
primitive, no backend change.

Here the bound is `n ∈ {0,1}` (`n.toNat < 2` — a public select bit). For a single
bit the select collapses to one mask: with `m := 0 - n` (`= allOnes` when `n = 1`,
`= 0` when `n = 0`), `result = ((a >>> 1) &&& m) ||| (a &&& ~m)` — the `ctSelectCom`
shape, the constant-time conditional-move between the two immediate-shift candidates
`a >>> 1` and `a >>> 0 = a`. (A wider `{0,1,2,3}` tree is the same recipe — one
branchless equality mask per candidate, OR-combined — but a 4-way tree is ~37 ops,
and the framework's `Com.denote`/`Expr.denote` carry a `retTy_eq ▸` cast that blocks
kernel `rfl` once the binder chain is that deep; the 2-way form keeps the source-level
`Com.denote = spec` proof a cheap `rfl`, as the surrounding golden-path kernels do.)

## The branchless mask

`m := 0 - n` is the all-ones mask for the bit `n ∈ {0,1}`; `~m := m ^^^ allOnes`.
The mask formula is checked by `bv_decide` over the two bounded cases (it is the
oracle: a wrong formula fails the spec).

## Constant-time discipline (why *public*-amount)

This is the CT-correct form precisely because the amount is **public**: both
candidate immediate shifts are evaluated and the select is branch-free, so the
data-flow is amount-independent. A variable shift **by a secret amount is not
constant-time** on many cores (a data-dependent barrel-shifter loop leaks the
amount) — so the CT layer must reject a secret-derived shift amount, and the native
register-amount op (`lsrv`/`srl`) plus that secret-amount caveat remain the
documented backend-extension work in `VarShiftGoldenPath`. The immediate shifts
`shrImm` used here are unconditionally CT (the distance is a compile-time constant),
which is what makes this public-amount form the CT-correct answer.

The deliverable: `boundedShrCom` over inputs `[a, n]`, with `boundedShrCom_spec`
the non-vacuous `n.toNat < 2 → Com.denote boundedShrCom … = a >>> n.toNat`, and the
e2e quartet proving it emits to all three backends through the unchanged path.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VarShiftEmit

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

/-! ## The bounded-public variable right shift as a `Com` over `[a, n]`

Inputs `[a, n]` (`a = .here`, `n = .there .here`). For the public select bit
`n ∈ {0,1}`, the branchless conditional-move between the two immediate-shift
candidates `a >>> 1` (amount 1) and `a` (amount 0):

```
m       := 0 - n               -- all-ones mask for the bit n
allOnes := 0xFF…FF
nm      := m ^ allOnes (= ~m)
s1      := a >>> 1              -- the amount-1 candidate (immediate shift)
am      := s1 & m              -- pick s1 when n = 1
bn      := a  & nm             -- pick a  when n = 0
r       := am | bn
```

All `regConst`/`regArith {sub,xor,and,or}`/`shrImm`, every one in `SupportedOp`. -/

/-- `boundedShrCom` : the constant-time mask-select between the immediate shifts
    `a >>> 1` and `a >>> 0`, over inputs `[a, n]`, computing `a >>> n.toNat` for a
    public amount `n.toNat ∈ {0,1}`. All ops (`regConst`, `shrImm`,
    `regArith {sub,xor,and,or}`) are width-64 `SupportedOp`, so it rides the
    unchanged golden path. -/
def boundedShrCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  -- c0 = 0
  .var { op := .regConst 64 0, retTy_eq := rfl, args := .nil }
  -- m = c0 - n        (c0 = .here, n = .there.there.here)
  (.var { op := .regArith .sub 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there .here)) .nil) }
  -- allOnes = 0xFF…FF
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nm = m ^ allOnes  (m = .there.here, allOnes = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- s1 = a >>> 1      (a = .there.there.there.there.here)
  (.var { op := .shrImm 64 1, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  -- am = s1 & m       (s1 = .here, m = .there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
  -- bn = a & nm       (a = 6×.there.here, nm = .there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there .here)) .nil) }
  -- r = am | bn       (am = .there.here, bn = .here)
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here))))))))

/-- `boundedShrCom` is in the supported straight-line fragment (regConst, sub,
    regConst, xor, shrImm, and, and, or — every op `SupportedOp`). -/
theorem boundedShrCom_ok : ComOK boundedShrCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))

/-- **Step 2 — value proof at the source, cheap `rfl`** (all-ALU + one immediate
    shift). With `m := 0 - n`, the source denotes
    `((a >>> 1) &&& m) ||| (a &&& (m ^^^ 0xFF…FF))` — the branchless conditional-move
    between the two immediate-shift candidates. -/
theorem boundedShrCom_denote (a n : BitVec 64) :
    Com.denote boundedShrCom (.cons a (.cons n .nil))
      = ((a >>> 1) &&& ((0 : BitVec 64) - n))
          ||| (a &&& (((0 : BitVec 64) - n) ^^^ BitVec.ofNat 64 18446744073709551615)) := rfl

/-- **The non-vacuous public-bounded variable-shift correctness.** For a public
    amount `n.toNat < 2`, the emitted constant-time mask-select denotes exactly the
    variable right shift `a >>> n.toNat` — the bounded-public variable shift *is* the
    actual shift. Constant-time by construction (both immediate shifts evaluated; the
    select is branch-free) and emits through the unchanged golden path. By
    case-splitting `n ∈ {0,1}` and `bv_decide` per case. -/
theorem boundedShrCom_spec (a n : BitVec 64) (hn : n.toNat < 2) :
    Com.denote boundedShrCom (.cons a (.cons n .nil)) = a >>> n.toNat := by
  rw [boundedShrCom_denote]
  have h : n = 0 ∨ n = 1 := by bv_omega
  rcases h with rfl | rfl
  · show _ = a >>> (0 : Nat); bv_decide
  · show _ = a >>> (1 : Nat); bv_decide

/-! ## The full e2e quartet: `boundedShrCom` emits to ARM, RISC-V, and x86

The source rides the *unchanged* `com_arm_e2e` / `com_riscv_e2e` golden path
(`comToReg_faithful`) and the generic x86 ELF driver — no `select`/register-shift
op, no backend change. -/

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem boundedShrCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg boundedShrCom 2))).regs)
        (comRetName boundedShrCom 2)
      = Com.denote boundedShrCom V :=
  com_arm_e2e boundedShrCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **Emitted RISC-V** — same source, discharged by the same `comToReg_faithful`. -/
theorem boundedShrCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg boundedShrCom 2))).regs)
        (comRetName boundedShrCom 2)
      = Com.denote boundedShrCom V :=
  com_riscv_e2e boundedShrCom_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier, as the field golden path): the same
    source to ELF `.o` bytes via the generic driver. -/
def boundedShrCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 boundedShrCom "bounded_shr"

end CatCrypt.Crypto.SecureCompilation.VarShiftEmit
