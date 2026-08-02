/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ComBuilder
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull
import CatCrypt.Crypto.SecureCompilation.VIR.MulDenoteErgonomics

/-!
# Golden path, generated: the GF(2⁸) bit-serial multiply via the `Com` builder

`gf256mul(a, b)` — the Russian-peasant bit-serial multiply over `GF(2^8)` with
reduction polynomial `x^8 + x^4 + x^3 + x + 1` (`0x11b`) — is the binary-field
building block of UOV / MAYO / SNOVA. It is **all-ALU**: shift / and / xor /
mask, with no integer multiply and no carry chain, so it routes cleanly through
the named-SSA → `Com jasminDialect` generator (`ComBuilder.build`) and out the
golden path (`com_arm_e2e` / `com_riscv_e2e` / `compileComToElf`).

The eight unrolled iterations `k = 0 … 7` each compute

```
bit_k  := (b >> k) & 1 ;  bmask := 0 - bit_k            -- all-ones iff bit set
acc    := acc ^ (a & bmask)                             -- conditional XOR of a
a      := a << 1
hi     := (a >> 8) & 1 ;  hmask := 0 - hi
a      := a ^ (0x11b & hmask)                            -- conditional reduce
```

starting from `acc = 0`; the result is `acc` after the eighth iteration, in
`[0, 255]`. Every op is in the builder's alphabet (`regArith {and, xor, sub}`,
`shlImm`, `shrImm`, `regConst`) — the `0 - x` mask is `regArith .sub` against a
`regConst 0`, no `mul`, no `mulhi`.

This is the demonstration that the generator scales to a real ~90-binding leaf:
the kernel is laid out by a per-iteration binding *generator* (so no de-Bruijn
level is hand-counted), `ComOK` is the **turnkey** `build_preserves_ComOK`
(generic builder lemma + a flat `SupportedOp` check — no per-binding `ComOK.var`
chain), and the generated `Com.denote` is validated against the authoritative
FIPS-197 GF(2⁸) test vectors by `native_decide` (the canonical closed-vector
validation — exercising the auto-resolved de-Bruijn resolution across all 91
bindings; the all-inputs symbolic `rfl` is impractical at this size).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenGf256

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ComBuilder
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-! ## 1. The per-iteration binding generator

The inputs are `a = level 0`, `b = level 1`. Three constants are materialised
once: `c1 = 1` (level 2), `c0 = 0` (level 3), `c11b = 0x11b = 283` (level 4).
The accumulator starts at `c0` (level 3); the running value `a` starts at the
input (level 0).

`gf256Iter accLvl aLvl base` emits the 11 bindings of one iteration `k` over
binding-base level `base` (`b` is read fixed at level 1; the shift amount `k` is
threaded as the immediate). Its result levels are:

| offset | binding | op |
|--------|---------|----|
| `base+0`  | `bsh   := b >> k`         | `shrImm 64 k` |
| `base+1`  | `bit   := bsh & c1`       | `and`         |
| `base+2`  | `bmask := c0 - bit`       | `sub`         |
| `base+3`  | `amasked := a & bmask`    | `and`         |
| `base+4`  | `acc'  := acc ^ amasked`  | `xor`         |
| `base+5`  | `ash   := a << 1`         | `shlImm 64 1` |
| `base+6`  | `hish  := ash >> 8`       | `shrImm 64 8` |
| `base+7`  | `hi    := hish & c1`      | `and`         |
| `base+8`  | `hmask := c0 - hi`        | `sub`         |
| `base+9`  | `redmask := c11b & hmask` | `and`         |
| `base+10` | `a'    := ash ^ redmask`  | `xor`         |

so the new accumulator level is `base+4` and the new `a` level is `base+10`. -/

/-- The 11 bindings of one bit-serial iteration `k`, given the current
    accumulator level `accLvl`, running-`a` level `aLvl`, and binding base level
    `base`. (Constants are at fixed levels: `c1 = 2`, `c0 = 3`, `c11b = 4`;
    `b = 1`.) -/
def gf256Iter (k accLvl aLvl base : Nat) : List Binding :=
  [ ⟨.shrImm 64 k, [1]⟩                       -- base+0 : bsh   := b >> k
  , ⟨.regArith .and 64, [base, 2]⟩            -- base+1 : bit   := bsh & c1
  , ⟨.regArith .sub 64, [3, base + 1]⟩        -- base+2 : bmask := c0 - bit
  , ⟨.regArith .and 64, [aLvl, base + 2]⟩     -- base+3 : amasked := a & bmask
  , ⟨.regArith .xor 64, [accLvl, base + 3]⟩   -- base+4 : acc'  := acc ^ amasked
  , ⟨.shlImm 64 1, [aLvl]⟩                    -- base+5 : ash   := a << 1
  , ⟨.shrImm 64 8, [base + 5]⟩                -- base+6 : hish  := ash >> 8
  , ⟨.regArith .and 64, [base + 6, 2]⟩        -- base+7 : hi    := hish & c1
  , ⟨.regArith .sub 64, [3, base + 7]⟩        -- base+8 : hmask := c0 - hi
  , ⟨.regArith .and 64, [4, base + 8]⟩        -- base+9 : redmask := c11b & hmask
  , ⟨.regArith .xor 64, [base + 5, base + 9]⟩ -- base+10: a'    := ash ^ redmask
  ]

/-- Unfold the eight iterations, threading `(accLvl, aLvl, base)`. -/
def gf256Iters : (count k accLvl aLvl base : Nat) → List Binding
  | 0, _, _, _, _ => []
  | (n + 1), k, accLvl, aLvl, base =>
      gf256Iter k accLvl aLvl base ++
        gf256Iters n (k + 1) (base + 4) (base + 10) (base + 11)

/-! ## 2. The named-SSA program -/

/-- The named-SSA description of the GF(2⁸) bit-serial multiply. Two inputs
    `a = 0`, `b = 1`; three constants (`c1 = 2`, `c0 = 3`, `c11b = 4`); then the
    eight iterations starting at base level `5`, with the initial accumulator at
    level `3` (`c0`) and the initial running-`a` at level `0`. After eight
    iterations the accumulator sits at level `5 + 7·11 + 4 = 86`. -/
def gf256MulSSA : NamedSSA where
  nInputs := 2
  bindings :=
    [ ⟨.regConst 64 1, []⟩    -- level 2 : c1   := 1
    , ⟨.regConst 64 0, []⟩    -- level 3 : c0   := 0
    , ⟨.regConst 64 283, []⟩  -- level 4 : c11b := 0x11b
    ] ++ gf256Iters 8 0 3 0 5
  retLevel := 86

/-! ## 3. Build the `Com` and prove `ComOK` turnkey -/

/-- The builder succeeds and produces a `Com` over the two-input context. -/
def gf256MulBuilt : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  (build gf256MulSSA).get (by decide)

/-- **Every binding of `gf256MulSSA` is `SupportedOp`** — the only per-kernel
    obligation the turnkey path leaves. The bindings are concrete after the
    generator unfolds, so a `decide` over the membership-resolved goal discharges
    the flat dispatch (three `regConst`, the eight iterations' `shrImm`/`shlImm`/
    `and`/`sub`/`xor`). No de-Bruijn structure appears. -/
theorem gf256MulSSA_allSupported : AllBindingsSupported gf256MulSSA.bindings := by
  intro b hb
  fin_cases hb <;> unfold SupportedOp <;> simp

/-- **The generated `Com` is `ComOK` — turnkey, via `build_preserves_ComOK`.**
    This is the payoff at ~90 bindings: no per-binding de-Bruijn `ComOK.var`
    chain, just the generic builder lemma fed the flat `SupportedOp` check and the
    `build … = some …` witness (`rfl`). `com_arm_e2e` / `com_riscv_e2e` apply
    directly to `gf256MulBuilt`. -/
theorem gf256MulBuilt_ok : ComOK gf256MulBuilt :=
  build_preserves_ComOK gf256MulSSA gf256MulBuilt gf256MulSSA_allSupported rfl

/-! ## 4. The denotation: the bit-serial GF(2⁸) product, by closed-vector KAT

The generated `Com.denote` is validated against the authoritative FIPS-197
GF(2⁸) test vectors by `native_decide`, alongside the same vectors on the
readable reference `gf256Ref`. Pinning both sides to the same vectors validates
that the auto-resolved de-Bruijn resolution across all 91 bindings is correct —
the generated kernel denotes the bit-serial multiply. -/

/-- One step of the reference bit-serial multiply on `BitVec 64` values, matching
    the `Com` exactly: `bit := (b >>> k) & 1 ; bmask := 0 - bit ;
    acc := acc ^ (a & bmask) ; ash := a << 1 ; hi := (ash >>> 8) & 1 ;
    hmask := 0 - hi ; a := ash ^ (0x11b & hmask)`. -/
def gf256Step (k : Nat) (acc a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let bmask := (0 : BitVec 64) - ((b >>> k) &&& (1 : BitVec 64))
  let acc' := acc ^^^ (a &&& bmask)
  let ash := a <<< (1 : Nat)
  let hmask := (0 : BitVec 64) - ((ash >>> (8 : Nat)) &&& (1 : BitVec 64))
  (acc', ash ^^^ ((283 : BitVec 64) &&& hmask))

/-- The reference value: thread `gf256Step` over `k = 0 … 7` from `acc = 0`,
    returning the final accumulator. -/
def gf256Ref (a b : BitVec 64) : BitVec 64 :=
  let s0 := gf256Step 0 (0 : BitVec 64) a b
  let s1 := gf256Step 1 s0.1 s0.2 b
  let s2 := gf256Step 2 s1.1 s1.2 b
  let s3 := gf256Step 3 s2.1 s2.2 b
  let s4 := gf256Step 4 s3.1 s3.2 b
  let s5 := gf256Step 5 s4.1 s4.2 b
  let s6 := gf256Step 6 s5.1 s5.2 b
  let s7 := gf256Step 7 s6.1 s6.2 b
  s7.1

/-- **Step 2 — value validation.** The reference `gf256Ref` matches the
    authoritative GF(2⁸) products (FIPS-197 / AES worked examples): `0x57·0x83 =
    0xc1`, `0x57·0x13 = 0xfe`, `0x53·0xca = 0x01`, `1·0xab = 0xab`. So `gf256Ref`
    is the bit-serial multiply. -/
theorem gf256Ref_kats :
    (gf256Ref 0x57 0x83).toNat = 0xc1 ∧ (gf256Ref 0x57 0x13).toNat = 0xfe
      ∧ (gf256Ref 0x53 0xca).toNat = 0x01 ∧ (gf256Ref 0x01 0xab).toNat = 0xab := by
  native_decide

/-- **The generated 91-binding `Com` computes the GF(2⁸) product.** Its
    `Com.denote` matches the same authoritative vectors — exercising the full
    `build` de-Bruijn resolution end-to-end. Together with `gf256Ref_kats` (both
    sides pinned to the same vectors) this validates that the generated kernel
    denotes the bit-serial multiply: the auto-resolved de-Bruijn indices across
    all 91 bindings are correct. Discharged by `native_decide` (the canonical
    closed-vector validation; the all-inputs symbolic `rfl` is impractical at
    91 bindings). -/
theorem gf256MulBuilt_kats :
    (Com.denote gf256MulBuilt (.cons (0x57 : BitVec 64) (.cons (0x83 : BitVec 64) .nil))).toNat = 0xc1
      ∧ (Com.denote gf256MulBuilt (.cons (0x57 : BitVec 64) (.cons (0x13 : BitVec 64) .nil))).toNat = 0xfe
      ∧ (Com.denote gf256MulBuilt (.cons (0x53 : BitVec 64) (.cons (0xca : BitVec 64) .nil))).toNat = 0x01
      ∧ (Com.denote gf256MulBuilt (.cons (0x01 : BitVec 64) (.cons (0xab : BitVec 64) .nil))).toNat = 0xab := by
  native_decide

/-! ## 5. The golden path: both backends + the x86 ELF leg -/

/-- **The emitted AArch64 block computes the GF(2⁸) product** — no hand-written
    `JInstr`, no per-kernel backend proof (`com_arm_e2e` discharges it via
    `comToReg_faithful`). -/
theorem gf256MulBuilt_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg gf256MulBuilt 2))).regs)
        (comRetName gf256MulBuilt 2)
      = Com.denote gf256MulBuilt V :=
  com_arm_e2e gf256MulBuilt_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The same source emits to RISC-V** — one source, two backends, both verified,
    both discharged by the single `comToReg_faithful`. -/
theorem gf256MulBuilt_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg gf256MulBuilt 2))).regs)
        (comRetName gf256MulBuilt 2)
      = Com.denote gf256MulBuilt V :=
  com_riscv_e2e gf256MulBuilt_ok FieldEmitGoldenPath.allReg64_two V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/sm2_compare/`, not byte identity with `compileComToElf`. -/
def gf256MulBuilt_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf gf256MulBuilt "gf256_mul"

end CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenGf256
