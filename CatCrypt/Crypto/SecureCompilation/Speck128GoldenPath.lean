/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
public import CatCrypt.Crypto.SecureCompilation.RotateSynth

/-!
# Golden path: the SPECK128 round function as `Com jasminDialect`, emitted by the verified compiler

**The same canonical pattern as `FieldEmitGoldenPath` and `ThreefishMixGoldenPath`, on the
SPECK128 round function** — the u64 ARX primitive at the core of the SPECK lightweight block
cipher (NSA). Each word is a `u64`; the round function is written ONCE as `Com jasminDialect`
source programs over the supported all-`reg 64` alphabet, proven ONCE against its value spec,
and the verified compiler emits the machine code — to AArch64 *and* RISC-V — with no
per-kernel backend proof (`comToReg_faithful` discharges it) and constant-time by construction.

The SPECK128 (key-schedule / encryption) round takes two data words `x`, `y` and a round key
`k`:
```
x' := (ROTR(x, 8) + y) ^^^ k       (rotate-RIGHT x by 8, add y, xor the key)
y' := ROTL(y, 3) ^^^ x'            (rotate-LEFT y by 3, xor with the new x')
```
The add (`x'`) and the two rotates are the only operations — the same ARX shape as
Threefish, here with SPECK's `α = 8` right-rotation and `β = 3` left-rotation. There is no
rotate `SupportedOp`, so each rotation is synthesised from the shift/or alphabet:
`ROTR(x, 8) = (x >>> 8) ||| (x <<< 56)` and `ROTL(y, 3) = (y <<< 3) ||| (y >>> 61)`
(`shrImm`/`shlImm`/`or`); the source denotes that explicit shift form by `rfl`, and the
shared `rotr_synth` / `rotl_synth` identities certify it equals `BitVec.rotateRight` /
`BitVec.rotateLeft`.

The round has two outputs over three inputs `[x, y, k]`, so each gives one single-output
`Com` — `speckXCom` (the new `x'`) and `speckYCom` (the new `y'`, which recomputes `x'`
inline, since single-output `Com`s cannot share intermediate values). Both lower through
the *same* `comToReg_faithful` as the field/Threefish ops — so the SPECK ARX words emit to
both backends with no new machinery, only a new kernel body. -/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Speck128

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
open CatCrypt.Crypto.SecureCompilation.RotateSynth

/-! ## The new `x'` word: `x' = (ROTR(x, 8) + y) ^^^ k`

`ROTR(x, 8) = (x >>> 8) ||| (x <<< 56)` (`64 - 8 = 56`), then `+ y`, then `^^^ k`. -/

/-- **SPECK128 round — the `x'` output**, over args `[x, y, k]`:
    `sh := x >>> 8 ; shl := x <<< 56 ; rot := sh | shl ; t := rot + y ; x' := t ^ k`.
    The right-rotate of `x` by 8 is `(x >>> 8) | (x <<< 56)`, added to `y`, xored with `k`. -/
def speckXCom : Com jasminDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- sh = x >>> 8 ;  x = .here
  .var { op := .shrImm 64 8, retTy_eq := rfl, args := .cons .here .nil }
  -- shl = x <<< 56 ;  x = .there .here  (64 - 8 = 56)
  (.var { op := .shlImm 64 56, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- rot = sh | shl ;  sh = .there .here, shl = .here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = rot + y ;  rot = .here, y = .there (.there (.there (.there .here)))
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- x' = t ^ k ;  t = .here, k = .there (.there (.there (.there (.there (.there .here)))))
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here
                    (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) }
    (.ret .here)))))

/-- `speckXCom` is in the supported straight-line fragment (shrImm, shlImm, or, add, xor). -/
theorem speckXCom_ok : ComOK speckXCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))

/-- **Step 2 — value proof at the source, cheap `rfl`** (the explicit shift-or rotate form). -/
theorem speckXCom_denote (x y k : BitVec 64) :
    Com.denote speckXCom (.cons x (.cons y (.cons k .nil)))
      = (((x >>> 8) ||| (x <<< 56)) + y) ^^^ k := rfl

/-- **The recognizable SPECK128 `x'` spec**: the emitted source computes
    `((x.rotateRight 8) + y) ^^^ k`. The shift-or rotate synthesis is certified by the
    shared `rotr_synth` identity (no `bv_decide`). -/
theorem speckXCom_spec (x y k : BitVec 64) :
    Com.denote speckXCom (.cons x (.cons y (.cons k .nil)))
      = ((x.rotateRight 8) + y) ^^^ k := by
  rw [speckXCom_denote, rotr_synth x 8 (by decide) (by decide)]

/-- **SPECK128 `x'` emits to AArch64**, discharged by `com_arm_e2e` via the single
    `comToReg_faithful`. -/
theorem speckXCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg speckXCom 3))).regs)
        (comRetName speckXCom 3)
      = Com.denote speckXCom V :=
  com_arm_e2e speckXCom_ok FieldEmitGoldenPath.allReg64_three V s hs

/-- **SPECK128 `x'` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem speckXCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg speckXCom 3))).regs)
        (comRetName speckXCom 3)
      = Com.denote speckXCom V :=
  com_riscv_e2e speckXCom_ok FieldEmitGoldenPath.allReg64_three V s hs

/-- **The x86 owned-emit leg** for SPECK128 `x'` (KAT-gated tier, as in
    `FieldEmitGoldenPath`): the same source to ELF `.o` bytes via the generic driver. -/
def speckXCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 speckXCom "speck128_x"

/-! ## The new `y'` word: `y' = ROTL(y, 3) ^^^ x'`

`ROTL(y, 3) = (y <<< 3) ||| (y >>> 61)` (`64 - 3 = 61`), xored with the new
`x' = (ROTR(x, 8) + y) ^^^ k`. Single-output `Com`s cannot share intermediates, so `x'`
is recomputed inline here. -/

/-- **SPECK128 round — the `y'` output**, over args `[x, y, k]`:
    `yl := y <<< 3 ; yr := y >>> 61 ; ry := yl | yr` (that is `ROTL(y, 3)`), then `x'` is
    recomputed as `xr := x >>> 8 ; xl := x <<< 56 ; rx := xr | xl ; t := rx + y ; xp := t ^ k`,
    and finally `y' := ry ^ xp`. -/
def speckYCom : Com jasminDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- yl = y <<< 3 ;  y = .there .here
  .var { op := .shlImm 64 3, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- yr = y >>> 61 ;  y = .there (.there .here)  (64 - 3 = 61)
  (.var { op := .shrImm 64 61, retTy_eq := rfl, args := .cons (.there (.there .here)) .nil }
  -- ry = yl | yr ;  yl = .there .here, yr = .here   (ry = ROTL(y, 3))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- xr = x >>> 8 ;  x = .there (.there (.there .here))
  (.var { op := .shrImm 64 8, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  -- xl = x <<< 56 ;  x = .there (.there (.there (.there .here)))
  (.var { op := .shlImm 64 56, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  -- rx = xr | xl ;  xr = .there .here, xl = .here   (rx = ROTR(x, 8))
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = rx + y ;  rx = .here, y = .there (.there (.there (.there (.there (.there (.there .here))))))
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons .here
                    (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                      .nil) }
  -- xp = t ^ k ;  t = .here, k = .there^9 .here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here
                    (.cons (.there (.there (.there (.there (.there (.there (.there
                      (.there (.there .here))))))))) .nil) }
  -- y' = ry ^ xp ;  ry = .there (.there (.there (.there (.there .here)))), xp = .here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here)))))
                    (.cons .here .nil) }
    (.ret .here)))))))))

/-- `speckYCom` is in the supported straight-line fragment (shlImm, shrImm, or, shrImm,
    shlImm, or, add, xor, xor). -/
theorem speckYCom_ok : ComOK speckYCom :=
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

/-- **Step 2 — value proof at the source** (the explicit shift-or rotate form). The
    nine-binding `y'` body overflows the default heartbeat budget for a brute whole-body
    `rfl`, so the binder chain is rewritten *structurally*: `simp only [Com.denote, …]`
    unfolds the `var`/`extend` skeleton, and the four local `rfl`-lemmas (`hh`/`ht` for
    `Var.lookup`'s head/shift cases, `hla0`/`hla1` for the `lookupArgs` recursion) resolve
    every de Bruijn lookup one constructor step at a time, without forcing the nested
    valuation tail — a size-linear rewrite the kernel checks cheaply. -/
theorem speckYCom_denote (x y k : BitVec 64) :
    Com.denote speckYCom (.cons x (.cons y (.cons k .nil)))
      = ((y <<< 3) ||| (y >>> 61))
          ^^^ ((((x >>> 8) ||| (x <<< 56)) + y) ^^^ k) := by
  have hh : ∀ {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (v : ⟦t⟧)
      (tl : Ctxt.Valuation Γ),
      (Ctxt.Var.here : Ctxt.Var (t :: Γ) t).lookup (.cons v tl) = v := fun _ _ => rfl
  have ht : ∀ {Γ : Ctxt jasminDialect} {t s : jasminDialect.Ty} (w : Ctxt.Var Γ t) (v : ⟦s⟧)
      (tl : Ctxt.Valuation Γ),
      (w.there : Ctxt.Var (s :: Γ) t).lookup (.cons v tl) = w.lookup tl := fun _ _ _ => rfl
  have hla0 : ∀ {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ),
      Expr.lookupArgs (d := jasminDialect) (tys := []) .nil V = .nil := fun _ => rfl
  have hla1 : ∀ {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} {ts : List jasminDialect.Ty}
      (vv : Ctxt.Var Γ t) (rest : HVector (fun ty => Ctxt.Var Γ ty) ts) (V : Ctxt.Valuation Γ),
      Expr.lookupArgs (.cons vv rest) V = .cons (vv.lookup V) (Expr.lookupArgs rest V) :=
    fun _ _ _ => rfl
  simp only [speckYCom, Com.denote, Expr.denote, Ctxt.Valuation.extend,
    DialectDenote.denote, JasminBinOp.apply, HVector.head, HVector.tail, hla0, hla1, hh, ht,
    VIR.shiftMask_64, Nat.reduceMod]

/-- **The recognizable SPECK128 `y'` spec**: the emitted source computes
    `(y.rotateLeft 3) ^^^ (((x.rotateRight 8) + y) ^^^ k)` — `ROTL(y, 3)` xored with the
    new `x'`. The shift-or rotate syntheses are certified by the shared `rotl_synth` /
    `rotr_synth` identities (no `bv_decide`). -/
theorem speckYCom_spec (x y k : BitVec 64) :
    Com.denote speckYCom (.cons x (.cons y (.cons k .nil)))
      = (y.rotateLeft 3) ^^^ (((x.rotateRight 8) + y) ^^^ k) := by
  rw [speckYCom_denote, rotl_synth y 3 (by decide) (by decide),
    rotr_synth x 8 (by decide) (by decide)]

/-- **SPECK128 `y'` emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem speckYCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg speckYCom 3))).regs)
        (comRetName speckYCom 3)
      = Com.denote speckYCom V :=
  com_arm_e2e speckYCom_ok FieldEmitGoldenPath.allReg64_three V s hs

/-- **SPECK128 `y'` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem speckYCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg speckYCom 3))).regs)
        (comRetName speckYCom 3)
      = Com.denote speckYCom V :=
  com_riscv_e2e speckYCom_ok FieldEmitGoldenPath.allReg64_three V s hs

/-- **The x86 owned-emit leg** for SPECK128 `y'` (KAT-gated tier). -/
def speckYCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 speckYCom "speck128_y"

end CatCrypt.Crypto.SecureCompilation.Speck128
