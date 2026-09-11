/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull

/-!
# Golden path: the Ascon S-box as `Com jasminDialect`, emitted by the verified compiler

**This is the canonical pattern for emitting the Ascon permutation's nonlinear layer.**
The Ascon 5-bit S-box (NIST SP 800-232), applied bitsliced across the five 64-bit lanes
`x0 … x4`, is the χ-layer of one Ascon round; it pairs with `AsconLinearGoldenPath`
(the linear diffusion layer) to form a full round. Each of the five output lanes
`y0 … y4` is written ONCE as a `Com jasminDialect` source program over the all-`reg 64`
`regArith` / `regConst` alphabet (`and`/`or`/`xor` plus the all-ones constant for `~~~`),
proven ONCE against its standard-`BitVec`-operator spec, and the verified compiler emits
the machine code — to AArch64 *and* RISC-V — with **no per-kernel backend proof**
(`comToReg_faithful` discharges it) and constant-time by construction. The same recipe
as `FieldEmitGoldenPath` / `Sha512BitFuncsGoldenPath`; only the kernel body changes.

The recipe (one source → both backends):
1. write the lane as a `Com jasminDialect Γ (.reg 64)` over `[x0,x1,x2,x3,x4]` in the
   `regArith {and, or, xor}` / `regConst` alphabet;
2. `ComOK` (mechanical — one constructor per op) + prove `Com.denote = <in-Com expr>`
   by cheap `rfl`, AND a recognizable-spec theorem `Com.denote = <standard BitVec
   operators in circuit form>` (using `~~~`, `&&&`, `^^^`) by rewriting with
   `xor_ones64_eq_not` — the independent check tying the source to the textbook
   S-box circuit;
3. `ScalarLinNeutralDemo.com_arm_e2e` / `MultiBackendDemo.com_riscv_e2e` emit the
   verified backend block — both discharged by Step 1's `comToReg_faithful`.

The standard bitsliced circuit (inputs `x0 x1 x2 x3 x4`):
```
x0 ^= x4;  x4 ^= x3;  x2 ^= x1;
t0 = (~x0)&x1;  t1 = (~x1)&x2;  t2 = (~x2)&x3;  t3 = (~x3)&x4;  t4 = (~x4)&x0;
x0 ^= t1;  x1 ^= t2;  x2 ^= t3;  x3 ^= t4;  x4 ^= t0;
x1 ^= x0;  x0 ^= x4;  x3 ^= x2;  x2 = ~x2;
```
Writing the intermediates in terms of the *original* inputs:
`x0a := x0^x4`, `x4a := x4^x3`, `x2a := x2^x1`, then
`x0b := x0a ^ ((~x1)&x2a)`, `x1b := x1 ^ ((~x2a)&x3)`, `x2b := x2a ^ ((~x3)&x4a)`,
`x3b := x3 ^ ((~x4a)&x0a)`, `x4b := x4a ^ ((~x0a)&x1)`, and the five outputs are
`y4 = x4b`, `y0 = x0b ^ x4b`, `y1 = x1b ^ x0b`, `y3 = x3b ^ x2b`, `y2 = ~x2b`.

Logical-not (`~~~`) is not a `SupportedOp`; it is expressed as `e ^^^ 0xFFFF…FFFF` via a
`regConst` all-ones binding (decimal literal `18446744073709551615`; the `2^64 - 1` form
breaks the denote `rfl`), exactly as in `shaChCom`. `xor_ones64_eq_not` discharges that
realization once for all five lanes. All five lanes emit to both backends with no new
compiler machinery.

Elaboration sits above the one-second module ceiling. Two per-lane costs account for
it. The `Com.denote` `rfl` reduces the lane's binding chain, so it grows with the
lane's length; a structural rewrite through the `Com.denote` equations in place of the
`rfl` is a possible cheaper form and has not been tried. The `com_arm_e2e` and
`com_riscv_e2e` instantiations cost roughly 25 ms per binding and do not respond to
supplying their implicit arguments; those two lemmas are themselves the shared form,
and what remains is one instantiation per lane per backend. -/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AsconSbox

open CatCrypt.Crypto.SecureCompilation.VIR
  CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
  CatCrypt.Crypto.SecureCompilation.ScalarLin
  CatCrypt.Crypto.SecureCompilation.ScalarLinFront
  CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
  CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
  CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
  CatCrypt.Crypto.SecureCompilation.ARMBackend
  CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
  CatCrypt.Crypto.SecureCompilation.RISCVBackend
  CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
  CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-- The all-ones `regConst` realizes logical-not at width 64:
    `x ^^^ 0xFFFF_FFFF_FFFF_FFFF = ~~~x`. The decimal literal is definitionally
    `BitVec.allOnes 64`, so the identity is `BitVec.xor_allOnes`. -/
theorem xor_ones64_eq_not (x : BitVec 64) :
    x ^^^ BitVec.ofNat 64 18446744073709551615 = ~~~x := by
  rw [show BitVec.ofNat 64 18446744073709551615 = BitVec.allOnes 64 from rfl,
    BitVec.xor_allOnes]

/-- The five-input context `[x0,x1,x2,x3,x4]` is all-`reg 64`. -/
theorem allReg64_five :
    AllReg64 ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu
  rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact h
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · exact absurd h List.not_mem_nil

/-! ## `y4 = x4a ^ ((~x0a) & x1)` where `x0a = x0^x4`, `x4a = x4^x3`

The fifth output lane. Body:
`x4a := x4^x3 ; x0a := x0^x4 ; ones := 0xFF… ; nx0a := x0a^ones ; t0 := nx0a & x1 ;
 y4 := x4a ^ t0`. -/

/-- `y4 = x4a ^ ((~x0a) & x1)` over `[x0,x1,x2,x3,x4]`. -/
def asconY4Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- x4a = x4 ^ x3
  .var { op := .regArith .xor 64, retTy_eq := rfl,
         args := .cons (.there (.there (.there (.there .here))))
                   (.cons (.there (.there (.there .here))) .nil) }
  -- x0a = x0 ^ x4
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here)
                    (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- ones = 0xFFFF…FFFF
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nx0a = x0a ^ ones
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t0 = nx0a & x1   (nx0a = .here, x1 = .there^5.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here
                    (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- y4 = x4a ^ t0    (x4a = .there^4.here after 5 bindings, t0 = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) (.cons .here .nil) }
    (.ret .here))))))

/-- `asconY4Com` is in the supported straight-line fragment (xor, xor, regConst, xor,
    and, xor). -/
theorem asconY4Com_ok : ComOK asconY4Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`** (the `~` is `^ 0xFF…FF`). -/
theorem asconY4Com_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY4Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x4 ^^^ x3) ^^^ (((x0 ^^^ x4) ^^^ BitVec.ofNat 64 18446744073709551615) &&& x1) := by
  rfl

/-- **Step 2 — recognizable-spec proof, via `xor_ones64_eq_not`.** Ties the source to the
    textbook S-box circuit lane `y4 = (x4^x3) ^ ((~(x0^x4)) & x1)` with the textbook `~~~`. -/
theorem asconY4Com_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY4Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x4 ^^^ x3) ^^^ ((~~~(x0 ^^^ x4)) &&& x1) := by
  rw [asconY4Com_denote]; simp only [xor_ones64_eq_not]

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem asconY4Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconY4Com 5))).regs)
        (comRetName asconY4Com 5)
      = Com.denote asconY4Com V :=
  com_arm_e2e asconY4Com_ok allReg64_five V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconY4Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconY4Com 5))).regs)
        (comRetName asconY4Com 5)
      = Com.denote asconY4Com V :=
  com_riscv_e2e asconY4Com_ok allReg64_five V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/ascon_compare/`, not byte identity with `compileComToElf`. -/
def asconY4Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf asconY4Com "ascon_sbox_y4"

/-! ## `y0 = x0b ^ x4b` where `x0b = x0a ^ ((~x1)&x2a)`, `x4b = x4a ^ ((~x0a)&x1)`

The zeroth output lane (`x0a=x0^x4`, `x2a=x2^x1`, `x4a=x4^x3`). Body:
`x0a := x0^x4 ; x2a := x2^x1 ; x4a := x4^x3 ; ones := 0xFF… ; nx1 := x1^ones ;
 nx0a := x0a^ones ; t1 := nx1 & x2a ; t4 := nx0a & x1 ; x0b := x0a ^ t1 ;
 x4b := x4a ^ t4 ; y0 := x0b ^ x4b`. -/

/-- `y0 = (x0a ^ ((~x1)&x2a)) ^ (x4a ^ ((~x0a)&x1))` over `[x0,x1,x2,x3,x4]`. -/
def asconY0Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- x0a = x0 ^ x4
  .var { op := .regArith .xor 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- x2a = x2 ^ x1
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil) }
  -- x4a = x4 ^ x3
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- ones = 0xFFFF…FFFF
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nx1 = x1 ^ ones   (x1 = .there^5.here, ones = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil) }
  -- nx0a = x0a ^ ones   (x0a = .there^4.here, ones = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil) }
  -- t1 = nx1 & x2a   (nx1 = .there.here, x2a = .there^4.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- t4 = nx0a & x1   (nx0a = .there.here, x1 = .there^8.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here)
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) }
  -- x0b = x0a ^ t1   (x0a = .there^7.here, t1 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                    (.cons (.there .here) .nil) }
  -- x4b = x4a ^ t4   (x4a = .there^6.here, t4 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there .here) .nil) }
  -- y0 = x0b ^ x4b   (x0b = .there.here, x4b = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))))))))))

/-- `asconY0Com` is in the supported straight-line fragment. -/
theorem asconY0Com_ok : ComOK asconY0Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem asconY0Com_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY0Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = ((x0 ^^^ x4) ^^^ ((x1 ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x2 ^^^ x1)))
          ^^^ ((x4 ^^^ x3)
                ^^^ (((x0 ^^^ x4) ^^^ BitVec.ofNat 64 18446744073709551615) &&& x1)) := by
  rfl

/-- **Step 2 — recognizable-spec proof, via `xor_ones64_eq_not`.** -/
theorem asconY0Com_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY0Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = ((x0 ^^^ x4) ^^^ ((~~~x1) &&& (x2 ^^^ x1)))
          ^^^ ((x4 ^^^ x3) ^^^ ((~~~(x0 ^^^ x4)) &&& x1)) := by
  rw [asconY0Com_denote]; simp only [xor_ones64_eq_not]

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem asconY0Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconY0Com 5))).regs)
        (comRetName asconY0Com 5)
      = Com.denote asconY0Com V :=
  com_arm_e2e asconY0Com_ok allReg64_five V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconY0Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconY0Com 5))).regs)
        (comRetName asconY0Com 5)
      = Com.denote asconY0Com V :=
  com_riscv_e2e asconY0Com_ok allReg64_five V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/ascon_compare/`, not byte identity with `compileComToElf`. -/
def asconY0Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf asconY0Com "ascon_sbox_y0"

/-! ## `y1 = x1b ^ x0b` where `x1b = x1 ^ ((~x2a)&x3)`, `x0b = x0a ^ ((~x1)&x2a)`

The first output lane (`x0a=x0^x4`, `x2a=x2^x1`). Body:
`x0a := x0^x4 ; x2a := x2^x1 ; ones := 0xFF… ; nx2a := x2a^ones ; nx1 := x1^ones ;
 t2 := nx2a & x3 ; t1 := nx1 & x2a ; x1b := x1 ^ t2 ; x0b := x0a ^ t1 ; y1 := x1b ^ x0b`. -/

/-- `y1 = (x1 ^ ((~x2a)&x3)) ^ (x0a ^ ((~x1)&x2a))` over `[x0,x1,x2,x3,x4]`. -/
def asconY1Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- x0a = x0 ^ x4
  .var { op := .regArith .xor 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- x2a = x2 ^ x1
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil) }
  -- ones = 0xFFFF…FFFF
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nx2a = x2a ^ ones   (x2a = .there.here, ones = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- nx1 = x1 ^ ones   (x1 = .there^5.here, ones = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here))))) (.cons (.there .here) .nil) }
  -- t2 = nx2a & x3   (nx2a = .there.here, x3 = .there^8.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here)
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) }
  -- t1 = nx1 & x2a   (nx1 = .there.here, x2a = .there^4.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- x1b = x1 ^ t2   (x1 = .there^8.here, t2 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                    (.cons (.there .here) .nil) }
  -- x0b = x0a ^ t1   (x0a = .there^7.here, t1 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                    (.cons (.there .here) .nil) }
  -- y1 = x1b ^ x0b   (x1b = .there.here, x0b = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here))))))))))

/-- `asconY1Com` is in the supported straight-line fragment. -/
theorem asconY1Com_ok : ComOK asconY1Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem asconY1Com_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY1Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x1 ^^^ (((x2 ^^^ x1) ^^^ BitVec.ofNat 64 18446744073709551615) &&& x3))
          ^^^ ((x0 ^^^ x4)
                ^^^ ((x1 ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x2 ^^^ x1))) := by
  rfl

/-- **Step 2 — recognizable-spec proof, via `xor_ones64_eq_not`.** -/
theorem asconY1Com_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY1Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x1 ^^^ ((~~~(x2 ^^^ x1)) &&& x3))
          ^^^ ((x0 ^^^ x4) ^^^ ((~~~x1) &&& (x2 ^^^ x1))) := by
  rw [asconY1Com_denote]; simp only [xor_ones64_eq_not]

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem asconY1Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconY1Com 5))).regs)
        (comRetName asconY1Com 5)
      = Com.denote asconY1Com V :=
  com_arm_e2e asconY1Com_ok allReg64_five V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconY1Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconY1Com 5))).regs)
        (comRetName asconY1Com 5)
      = Com.denote asconY1Com V :=
  com_riscv_e2e asconY1Com_ok allReg64_five V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/ascon_compare/`, not byte identity with `compileComToElf`. -/
def asconY1Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf asconY1Com "ascon_sbox_y1"

/-! ## `y3 = x3b ^ x2b` where `x3b = x3 ^ ((~x4a)&x0a)`, `x2b = x2a ^ ((~x3)&x4a)`

The third output lane (`x0a=x0^x4`, `x4a=x4^x3`, `x2a=x2^x1`). Body:
`x0a := x0^x4 ; x4a := x4^x3 ; x2a := x2^x1 ; ones := 0xFF… ; nx4a := x4a^ones ;
 nx3 := x3^ones ; t4 := nx4a & x0a ; t3 := nx3 & x4a ; x3b := x3 ^ t4 ;
 x2b := x2a ^ t3 ; y3 := x3b ^ x2b`. -/

/-- `y3 = (x3 ^ ((~x4a)&x0a)) ^ (x2a ^ ((~x3)&x4a))` over `[x0,x1,x2,x3,x4]`. -/
def asconY3Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- x0a = x0 ^ x4
  .var { op := .regArith .xor 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- x4a = x4 ^ x3
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here)))))
                    (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- x2a = x2 ^ x1
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- ones = 0xFFFF…FFFF
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nx4a = x4a ^ ones   (x4a = .there^2.here, ones = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there .here)) (.cons .here .nil) }
  -- nx3 = x3 ^ ones   (x3 = .there^8.here, ones = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                    (.cons (.there .here) .nil) }
  -- t4 = nx4a & x0a   (nx4a = .there.here, x0a = .there^5.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- t3 = nx3 & x4a   (nx3 = .there.here, x4a = .there^5.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- x3b = x3 ^ t4   (x3 = .there^11.here, t4 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                    (.cons (.there .here) .nil) }
  -- x2b = x2a ^ t3   (x2a = .there^6.here, t3 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there .here) .nil) }
  -- y3 = x3b ^ x2b   (x3b = .there.here, x2b = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))))))))))

/-- `asconY3Com` is in the supported straight-line fragment. -/
theorem asconY3Com_ok : ComOK asconY3Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem asconY3Com_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY3Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x3 ^^^ (((x4 ^^^ x3) ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x0 ^^^ x4)))
          ^^^ ((x2 ^^^ x1)
                ^^^ ((x3 ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x4 ^^^ x3))) := by
  rfl

/-- **Step 2 — recognizable-spec proof, via `xor_ones64_eq_not`.** -/
theorem asconY3Com_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY3Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = (x3 ^^^ ((~~~(x4 ^^^ x3)) &&& (x0 ^^^ x4)))
          ^^^ ((x2 ^^^ x1) ^^^ ((~~~x3) &&& (x4 ^^^ x3))) := by
  rw [asconY3Com_denote]; simp only [xor_ones64_eq_not]

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem asconY3Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconY3Com 5))).regs)
        (comRetName asconY3Com 5)
      = Com.denote asconY3Com V :=
  com_arm_e2e asconY3Com_ok allReg64_five V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconY3Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconY3Com 5))).regs)
        (comRetName asconY3Com 5)
      = Com.denote asconY3Com V :=
  com_riscv_e2e asconY3Com_ok allReg64_five V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/ascon_compare/`, not byte identity with `compileComToElf`. -/
def asconY3Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf asconY3Com "ascon_sbox_y3"

/-! ## `y2 = ~x2b` where `x2b = x2a ^ ((~x3)&x4a)`

The second output lane (the only one ending in a complement; `x2a=x2^x1`, `x4a=x4^x3`).
Body: `x2a := x2^x1 ; x4a := x4^x3 ; ones := 0xFF… ; nx3 := x3^ones ; t3 := nx3 & x4a ;
 x2b := x2a ^ t3 ; y2 := x2b ^ ones`. -/

/-- `y2 = ~(x2a ^ ((~x3)&x4a))` over `[x0,x1,x2,x3,x4]`. -/
def asconY2Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- x2a = x2 ^ x1
  .var { op := .regArith .xor 64, retTy_eq := rfl,
         args := .cons (.there (.there .here)) (.cons (.there .here) .nil) }
  -- x4a = x4 ^ x3
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here)))))
                    (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- ones = 0xFFFF…FFFF
  (.var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- nx3 = x3 ^ ones   (x3 = .there^6.here, ones = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil) }
  -- t3 = nx3 & x4a   (nx3 = .here, x4a = .there^2.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there .here)) .nil) }
  -- x2b = x2a ^ t3   (x2a = .there^4.here, t3 = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) (.cons .here .nil) }
  -- y2 = x2b ^ ones   (x2b = .here, ones = .there^3.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
    (.ret .here)))))))

/-- `asconY2Com` is in the supported straight-line fragment (xor, xor, regConst, xor,
    and, xor, xor). -/
theorem asconY2Com_ok : ComOK asconY2Com :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem asconY2Com_denote (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY2Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = ((x2 ^^^ x1)
            ^^^ ((x3 ^^^ BitVec.ofNat 64 18446744073709551615) &&& (x4 ^^^ x3)))
          ^^^ BitVec.ofNat 64 18446744073709551615 := by
  rfl

/-- **Step 2 — recognizable-spec proof, via `xor_ones64_eq_not`.** Ties the source to the
    textbook S-box lane `y2 = ~(x2a ^ ((~x3)&x4a))` with the textbook `~~~`. -/
theorem asconY2Com_spec (x0 x1 x2 x3 x4 : BitVec 64) :
    Com.denote asconY2Com (.cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 .nil)))))
      = ~~~((x2 ^^^ x1) ^^^ ((~~~x3) &&& (x4 ^^^ x3))) := by
  rw [asconY2Com_denote]; simp only [xor_ones64_eq_not]

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem asconY2Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 5 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg asconY2Com 5))).regs)
        (comRetName asconY2Com 5)
      = Com.denote asconY2Com V :=
  com_arm_e2e asconY2Com_ok allReg64_five V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem asconY2Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 5 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg asconY2Com 5))).regs)
        (comRetName asconY2Com 5)
      = Com.denote asconY2Com V :=
  com_riscv_e2e asconY2Com_ok allReg64_five V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/ascon_compare/`, not byte identity with `compileComToElf`. -/
def asconY2Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf asconY2Com "ascon_sbox_y2"

end CatCrypt.Crypto.SecureCompilation.AsconSbox
