/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull

/-!
# Golden path: the SHA-512 bit functions as `Com jasminDialect`, emitted by the verified compiler

**This is the canonical pattern for emitting the SHA-512 round bit-functions.** Each of
the six FIPS 180-4 word functions (`Ch`, `Maj`, the big sigmas `Σ₀`/`Σ₁`, the small
sigmas `σ₀`/`σ₁`) is written ONCE as a `Com jasminDialect` source program over the
all-`reg 64` `regArith`/`shrImm`/`shlImm`/`regConst` alphabet, proven ONCE against its
standard-`BitVec`-operator spec, and the verified compiler emits the machine code — to
AArch64 *and* RISC-V — with **no per-kernel backend proof** (`comToReg_faithful`
discharges it) and constant-time by construction. The same recipe as
`FieldEmitGoldenPath`; only the kernel body changes.

The recipe (one source → both backends), as in `FieldEmitGoldenPath`:
1. write the function as a `Com jasminDialect Γ (.reg 64)` over the
   `regArith`/`shrImm`/`shlImm`/`regConst` alphabet;
2. `ComOK` (mechanical — one constructor per op) + prove `Com.denote = <in-Com expr>`
   by cheap `rfl`, AND a recognizable-spec theorem `Com.denote = <standard BitVec
   operators>` (using `~~~`, `.rotateRight`, `^^^`, `>>>`) by rewriting with
   `xor_ones64_eq_not` and `BitVec.rotateRight_def` — the independent check tying
   the source to the textbook definition;
3. `ScalarLinNeutralDemo.com_arm_e2e` / `MultiBackendDemo.com_riscv_e2e` emit the
   verified backend block — both discharged by Step 1's `comToReg_faithful`.

The rotate `ROTR^n x` is **branchless in the existing `reg 64` alphabet** as
`(x >>> n) ||| (x <<< (64 - n))` — `shrImm`/`shlImm`/`or`, every one in `SupportedOp`,
so it lowers through the same `comToReg_faithful` as the field ALU ops with no new
dialect machinery. Logical-not (`~~~e` in `Ch`) is not a `SupportedOp`; it is expressed
as `e ^^^ 0xFFFF…FFFF` via a `regConst` all-ones binding (decimal literal; the
`2^64 - 1` form breaks the denote `rfl`), discharged by `xor_ones64_eq_not`. The six
functions complete the round bit-twiddling SHA-512 needs, all emitting to both backends
with no new compiler machinery.

Elaboration sits above the one-second module ceiling. Two per-kernel costs account for
it. The `Com.denote` `rfl` reduces the kernel's binding chain, so it grows with the
kernel's length; a structural rewrite through the `Com.denote` equations in place of
the `rfl` is a possible cheaper form and has not been tried. The `com_arm_e2e` and
`com_riscv_e2e` instantiations cost roughly 25 ms per binding and do not respond to
supplying their implicit arguments; those two lemmas are themselves the shared form,
and what remains is one instantiation per kernel per backend. -/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Sha512BitFuncs

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

/-! ## `Ch e f g = (e & f) ^ ((~e) & g)`

Args `[e, f, g]`. The logical-not `~e` is `e ^ 0xFFFF…FFFF` (`regConst` all-ones,
decimal). Body:
`ones := 0xFF… ; ne := e ^ ones ; ef := e & f ; neg := ne & g ; r := ef ^ neg`. -/

/-- `Ch e f g = (e & f) ^ ((~e) & g)` over `[e, f, g]`. -/
def shaChCom : Com jasminDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- ones = 0xFFFF…FFFF
  .var { op := .regConst 64 18446744073709551615, retTy_eq := rfl, args := .nil }
  -- ne = e ^ ones        (e = .there.here after the regConst push)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- ef = e & f           (e = .there.there.here, f = .there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there .here))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- neg = ne & g         (ne = .there.here, g = .there.there.there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here)
                    (.cons (.there (.there (.there (.there (.there .here))))) .nil) }
  -- r = ef ^ neg         (ef = .there.here, neg = .here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))))

/-- `shaChCom` is in the supported straight-line fragment (regConst, xor, and, and, xor). -/
theorem shaChCom_ok : ComOK shaChCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem shaChCom_denote (e f g : BitVec 64) :
    Com.denote shaChCom (.cons e (.cons f (.cons g .nil)))
      = (e &&& f) ^^^ ((e ^^^ BitVec.ofNat 64 18446744073709551615) &&& g) := rfl

/-- **Step 2 — recognizable-spec proof, via `xor_ones64_eq_not`.** Ties the source to the
    standard `Ch e f g = (e & f) ^ ((~e) & g)` with the textbook `~~~`. -/
theorem shaChCom_spec (e f g : BitVec 64) :
    Com.denote shaChCom (.cons e (.cons f (.cons g .nil)))
      = (e &&& f) ^^^ ((~~~e) &&& g) := by
  rw [shaChCom_denote]; simp only [xor_ones64_eq_not]

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem shaChCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg shaChCom 3))).regs)
        (comRetName shaChCom 3)
      = Com.denote shaChCom V :=
  com_arm_e2e shaChCom_ok allReg64_three V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem shaChCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg shaChCom 3))).regs)
        (comRetName shaChCom 3)
      = Com.denote shaChCom V :=
  com_riscv_e2e shaChCom_ok allReg64_three V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier): the same source to ELF `.o` bytes. -/
def shaChCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 shaChCom "sha512_ch"

/-! ## `Maj a b c = (a & b) ^ (a & c) ^ (b & c)`

Args `[a, b, c]`. Body:
`ab := a & b ; ac := a & c ; bc := b & c ; t := ab ^ ac ; r := t ^ bc`. -/

/-- `Maj a b c = (a & b) ^ (a & c) ^ (b & c)` over `[a, b, c]`. -/
def shaMajCom : Com jasminDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- ab = a & b           (a = .here, b = .there.here)
  .var { op := .regArith .and 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
  -- ac = a & c           (a = .there.here, c = .there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons (.there (.there (.there .here))) .nil) }
  -- bc = b & c           (b = .there.there.there.here, c = .there.there.there.there.here)
  (.var { op := .regArith .and 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here)))
                    (.cons (.there (.there (.there (.there .here)))) .nil) }
  -- t = ab ^ ac          (ab = .there.there.here, ac = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there .here)) (.cons (.there .here) .nil) }
  -- r = t ^ bc           (t = .here, bc = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here)))))

/-- `shaMajCom` is in the supported straight-line fragment (and, and, and, xor, xor). -/
theorem shaMajCom_ok : ComOK shaMajCom :=
  ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _)))))

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem shaMajCom_denote (a b c : BitVec 64) :
    Com.denote shaMajCom (.cons a (.cons b (.cons c .nil)))
      = ((a &&& b) ^^^ (a &&& c)) ^^^ (b &&& c) := rfl

/-- **Step 2 — recognizable-spec proof.** The in-Com form is already the textbook
    circuit up to `^^^` association, so the denote lemma alone closes it. -/
theorem shaMajCom_spec (a b c : BitVec 64) :
    Com.denote shaMajCom (.cons a (.cons b (.cons c .nil)))
      = (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
  rw [shaMajCom_denote]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem shaMajCom_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 3 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg shaMajCom 3))).regs)
        (comRetName shaMajCom 3)
      = Com.denote shaMajCom V :=
  com_arm_e2e shaMajCom_ok allReg64_three V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem shaMajCom_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 3 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg shaMajCom 3))).regs)
        (comRetName shaMajCom 3)
      = Com.denote shaMajCom V :=
  com_riscv_e2e shaMajCom_ok allReg64_three V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def shaMajCom_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 shaMajCom "sha512_maj"

/-! ## `Σ₀ a = ROTR^28 a ^ ROTR^34 a ^ ROTR^39 a`

Args `[a]`. Each `ROTR^n a = (a >>> n) ||| (a <<< (64-n))`. Body:
`r28 := rot a 28 ; r34 := rot a 34 ; r39 := rot a 39 ; t := r28 ^ r34 ; r := t ^ r39`,
each `rot` being `(shr) | (shl)`. -/

/-- `Σ₀ a = ROTR^28 a ^ ROTR^34 a ^ ROTR^39 a` over `[a]`. -/
def shaBigSigma0Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r28: hi = a >>> 28 ; lo = a <<< 36 ; r28 = hi | lo
  .var { op := .shrImm 64 28, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 36, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r34: hi = a >>> 34 ; lo = a <<< 30 ; r34 = hi | lo   (a now = .there.there.there.here)
  (.var { op := .shrImm 64 34, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 30, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r39: hi = a >>> 39 ; lo = a <<< 25 ; r39 = hi | lo   (a now = .there^6.here)
  (.var { op := .shrImm 64 39, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here)))))) .nil }
  (.var { op := .shlImm 64 25, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = r28 ^ r34   (r28 = .there^6.here, r34 = .there^3.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- r = t ^ r39   (t = .here, r39 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here)))))))))))

/-- `shaBigSigma0Com` is in the supported straight-line fragment. -/
theorem shaBigSigma0Com_ok : ComOK shaBigSigma0Com :=
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

/-- **Step 2 — in-Com value proof, cheap `rfl`** (the rotate as `shr | shl`). -/
theorem shaBigSigma0Com_denote (a : BitVec 64) :
    Com.denote shaBigSigma0Com (.cons a .nil)
      = (((a >>> 28) ||| (a <<< 36)) ^^^ ((a >>> 34) ||| (a <<< 30)))
          ^^^ ((a >>> 39) ||| (a <<< 25)) := rfl

/-- **Step 2 — recognizable-spec proof, via `BitVec.rotateRight_def`.** Ties the
    `shr | shl` source to the textbook `ROTR` via `BitVec.rotateRight`. -/
theorem shaBigSigma0Com_spec (a : BitVec 64) :
    Com.denote shaBigSigma0Com (.cons a .nil)
      = a.rotateRight 28 ^^^ a.rotateRight 34 ^^^ a.rotateRight 39 := by
  rw [shaBigSigma0Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem shaBigSigma0Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg shaBigSigma0Com 1))).regs)
        (comRetName shaBigSigma0Com 1)
      = Com.denote shaBigSigma0Com V :=
  com_arm_e2e shaBigSigma0Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem shaBigSigma0Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg shaBigSigma0Com 1))).regs)
        (comRetName shaBigSigma0Com 1)
      = Com.denote shaBigSigma0Com V :=
  com_riscv_e2e shaBigSigma0Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def shaBigSigma0Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 shaBigSigma0Com "sha512_bigsigma0"

/-! ## `Σ₁ e = ROTR^14 e ^ ROTR^18 e ^ ROTR^41 e`

Args `[e]`. Same `shr | shl` rotate shape as `Σ₀`. -/

/-- `Σ₁ e = ROTR^14 e ^ ROTR^18 e ^ ROTR^41 e` over `[e]`. -/
def shaBigSigma1Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r14: e >>> 14 ; e <<< 50 ; |
  .var { op := .shrImm 64 14, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 50, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r18: e >>> 18 ; e <<< 46 ; |
  (.var { op := .shrImm 64 18, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 46, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r41: e >>> 41 ; e <<< 23 ; |
  (.var { op := .shrImm 64 41, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here)))))) .nil }
  (.var { op := .shlImm 64 23, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- t = r14 ^ r18
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- r = t ^ r41
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here)))))))))))

/-- `shaBigSigma1Com` is in the supported straight-line fragment. -/
theorem shaBigSigma1Com_ok : ComOK shaBigSigma1Com :=
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
theorem shaBigSigma1Com_denote (e : BitVec 64) :
    Com.denote shaBigSigma1Com (.cons e .nil)
      = (((e >>> 14) ||| (e <<< 50)) ^^^ ((e >>> 18) ||| (e <<< 46)))
          ^^^ ((e >>> 41) ||| (e <<< 23)) := rfl

/-- **Step 2 — recognizable-spec proof, via `BitVec.rotateRight_def`.** -/
theorem shaBigSigma1Com_spec (e : BitVec 64) :
    Com.denote shaBigSigma1Com (.cons e .nil)
      = e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41 := by
  rw [shaBigSigma1Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem shaBigSigma1Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg shaBigSigma1Com 1))).regs)
        (comRetName shaBigSigma1Com 1)
      = Com.denote shaBigSigma1Com V :=
  com_arm_e2e shaBigSigma1Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem shaBigSigma1Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg shaBigSigma1Com 1))).regs)
        (comRetName shaBigSigma1Com 1)
      = Com.denote shaBigSigma1Com V :=
  com_riscv_e2e shaBigSigma1Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg** (KAT-gated tier). -/
def shaBigSigma1Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 shaBigSigma1Com "sha512_bigsigma1"

/-! ## `σ₀ x = ROTR^1 x ^ ROTR^8 x ^ (x >>> 7)`

Args `[x]`. Two rotates plus a plain logical shift-right (no `<<<` for the last term). -/

/-- `σ₀ x = ROTR^1 x ^ ROTR^8 x ^ (x >>> 7)` over `[x]`. -/
def shaSmallSigma0Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r1: x >>> 1 ; x <<< 63 ; |
  .var { op := .shrImm 64 1, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 63, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r8: x >>> 8 ; x <<< 56 ; |
  (.var { op := .shrImm 64 8, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 56, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- sh = x >>> 7        (x now = .there^6.here)
  (.var { op := .shrImm 64 7, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here)))))) .nil }
  -- t = r1 ^ r8        (r1 = .there^4.here, r8 = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                    (.cons (.there .here) .nil) }
  -- r = t ^ sh        (t = .here, sh = .there.here)
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here)))))))))

/-- `shaSmallSigma0Com` is in the supported straight-line fragment. -/
theorem shaSmallSigma0Com_ok : ComOK shaSmallSigma0Com :=
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

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem shaSmallSigma0Com_denote (x : BitVec 64) :
    Com.denote shaSmallSigma0Com (.cons x .nil)
      = (((x >>> 1) ||| (x <<< 63)) ^^^ ((x >>> 8) ||| (x <<< 56))) ^^^ (x >>> 7) := rfl

/-- **Step 2 — recognizable-spec proof, via `BitVec.rotateRight_def`.** -/
theorem shaSmallSigma0Com_spec (x : BitVec 64) :
    Com.denote shaSmallSigma0Com (.cons x .nil)
      = x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7) := by
  rw [shaSmallSigma0Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem shaSmallSigma0Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg shaSmallSigma0Com 1))).regs)
        (comRetName shaSmallSigma0Com 1)
      = Com.denote shaSmallSigma0Com V :=
  com_arm_e2e shaSmallSigma0Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem shaSmallSigma0Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg shaSmallSigma0Com 1))).regs)
        (comRetName shaSmallSigma0Com 1)
      = Com.denote shaSmallSigma0Com V :=
  com_riscv_e2e shaSmallSigma0Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/sha2_compare/`, not byte identity with `compileComToElf`. -/
def shaSmallSigma0Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf shaSmallSigma0Com "sha512_smallsigma0"

/-! ## `σ₁ x = ROTR^19 x ^ ROTR^61 x ^ (x >>> 6)`

Args `[x]`. Same shape as `σ₀`, different offsets. -/

/-- `σ₁ x = ROTR^19 x ^ ROTR^61 x ^ (x >>> 6)` over `[x]`. -/
def shaSmallSigma1Com : Com jasminDialect [.reg 64] (.reg 64) :=
  -- r19: x >>> 19 ; x <<< 45 ; |
  .var { op := .shrImm 64 19, retTy_eq := rfl, args := .cons .here .nil }
  (.var { op := .shlImm 64 45, retTy_eq := rfl, args := .cons (.there .here) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- r61: x >>> 61 ; x <<< 3 ; |
  (.var { op := .shrImm 64 61, retTy_eq := rfl,
          args := .cons (.there (.there (.there .here))) .nil }
  (.var { op := .shlImm 64 3, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here)))) .nil }
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- sh = x >>> 6
  (.var { op := .shrImm 64 6, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here)))))) .nil }
  -- t = r19 ^ r61
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                    (.cons (.there .here) .nil) }
  -- r = t ^ sh
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
    (.ret .here)))))))))

/-- `shaSmallSigma1Com` is in the supported straight-line fragment. -/
theorem shaSmallSigma1Com_ok : ComOK shaSmallSigma1Com :=
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

/-- **Step 2 — in-Com value proof, cheap `rfl`.** -/
theorem shaSmallSigma1Com_denote (x : BitVec 64) :
    Com.denote shaSmallSigma1Com (.cons x .nil)
      = (((x >>> 19) ||| (x <<< 45)) ^^^ ((x >>> 61) ||| (x <<< 3))) ^^^ (x >>> 6) := rfl

/-- **Step 2 — recognizable-spec proof, via `BitVec.rotateRight_def`.** -/
theorem shaSmallSigma1Com_spec (x : BitVec 64) :
    Com.denote shaSmallSigma1Com (.cons x .nil)
      = x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6) := by
  rw [shaSmallSigma1Com_denote]; simp only [BitVec.rotateRight_def]

/-- **Emitted AArch64**, discharged by `com_arm_e2e`. -/
theorem shaSmallSigma1Com_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg shaSmallSigma1Com 1))).regs)
        (comRetName shaSmallSigma1Com 1)
      = Com.denote shaSmallSigma1Com V :=
  com_arm_e2e shaSmallSigma1Com_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem shaSmallSigma1Com_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg shaSmallSigma1Com 1))).regs)
        (comRetName shaSmallSigma1Com 1)
      = Com.denote shaSmallSigma1Com V :=
  com_riscv_e2e shaSmallSigma1Com_ok allReg64_one V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/sha2_compare/`, not byte identity with `compileComToElf`. -/
def shaSmallSigma1Com_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf shaSmallSigma1Com "sha512_smallsigma1"

end CatCrypt.Crypto.SecureCompilation.Sha512BitFuncs
