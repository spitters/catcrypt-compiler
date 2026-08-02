/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.RotateSynth

/-!
# Golden path: SipHash `SipRound` as `Com jasminDialect`, emitted by the verified compiler

**The same canonical pattern as `FieldEmitGoldenPath`, `KeccakBitGoldenPath`, and
`ThreefishMixGoldenPath`, on SipHash's `SipRound`** — the u64 ARX permutation at the
core of SipHash, a widely deployed keyed PRF / MAC (hash-table flooding defence, syncookies,
short-message authentication). Each of the four state words `v0..v3` is a `u64`; `SipRound`
is the ARX round

```
v0 += v1;  v1 = ROTL(v1,13);  v1 ^= v0;  v0 = ROTL(v0,32);
v2 += v3;  v3 = ROTL(v3,16);  v3 ^= v2;
v0 += v3;  v3 = ROTL(v3,21);  v3 ^= v0;
v2 += v1;  v1 = ROTL(v1,17);  v1 ^= v2;  v2 = ROTL(v2,32);
```

where `+` is modular add over `u64` and `ROTL` is rotate-left. Each of the four output
words `v0' v1' v2' v3'` is a function of the original `v0 v1 v2 v3`; here each is written
ONCE as a single-output `Com jasminDialect` source over the supported all-`reg 64`
alphabet (`add`/`xor`/`or` and `shlImm`/`shrImm` for the rotates — there is no rotate
`SupportedOp`, so `ROTL(x,n) = (x <<< n) ||| (x >>> (64-n))`). Single-output `Com`s
cannot share sub-results, so shared subterms (e.g. `v0+v1`, `v2+v3`, the intermediate
`v1''`, `v3''`) are recomputed inside each word's program — value-correct, if not
minimal. Each program is proven ONCE against its value spec (the recognizable
add/`rotateLeft`/xor formula, the shift-or rotate synthesis certified by the shared
`rotl_synth` identity),
and the verified compiler emits the machine code — AArch64 *and* RISC-V — with no
per-kernel backend proof (`comToReg_faithful` discharges it) and constant-time by
construction.

## Dataflow (intermediate single-static-assignment names)

```
a0 = v0 + v1                      d0 = ROTL(a0,32)
c1 = ROTL(v1,13) ^ a0            a2 = v2 + v3
c3 = ROTL(v3,16) ^ a2            e0 = d0 + c3            -- = v0'
e2 = a2 + c1                      g1 = ROTL(c1,17) ^ e2  -- = v1'
h2 = ROTL(e2,32)                                          -- = v2'
g3 = ROTL(c3,21) ^ e0                                     -- = v3'
```

So `v0' = ROTL(v0+v1,32) + (ROTL(v3,16) ^ (v2+v3))`, and the deeper words rebuild the
chain through `c1`, `c3`, `e2`, `e0`. The four programs lower through the *same*
`comToReg_faithful` as the field/Keccak/Threefish ops — so the SipHash ARX words emit to
both backends with no new machinery, only a new kernel body.

Elaboration sits above the one-second module ceiling. The recognizable-spec proofs are
not the cost — the shared `rotl_synth` closes each in under 20 ms. Two per-word costs
account for it, and both grow with the word's binding count, which is large here
because a single-output `Com` cannot share sub-results and each word rebuilds the whole
ARX chain. The `Com.denote` `rfl` reduces that chain; a structural rewrite through the
`Com.denote` equations in place of the `rfl` is a possible cheaper form and has not
been tried. The `com_arm_e2e` and `com_riscv_e2e` instantiations cost roughly 25 ms per
binding and do not respond to supplying their implicit arguments; those two lemmas are
themselves the shared form, and what remains is one instantiation per word per
backend. -/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SipHashRound

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
  CatCrypt.Crypto.SecureCompilation.RotateSynth

/-- The 4-input SipHash state context `[v0, v1, v2, v3]` is all-`reg 64`. -/
theorem allReg64_four : AllReg64 ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu
  rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact h
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · exact absurd h List.not_mem_nil

/-! ## `v0'` — the first output word

`v0' = ROTL(v0+v1, 32) ^^^ 0  ... ` no: `v0' = ROTL(v0+v1,32) + (ROTL(v3,16) ^^^ (v2+v3))`.

Program over `[v0,v1,v2,v3]` (`v0=.here`, `v1=.there.here`, `v2=.there².here`,
`v3=.there³.here`), building bottom-up:
```
a0   = v0 + v1
d0sh = a0 <<< 32      d0sr = a0 >>> 32      d0 = d0sh ||| d0sr      -- ROTL(a0,32)
a2   = v2 + v3
r3sh = v3 <<< 16      r3sr = v3 >>> 48      r3 = r3sh ||| r3sr      -- ROTL(v3,16)
c3   = r3 ^^^ a2
v0'  = d0 + c3
```
-/

/-- **`SipRound` output `v0'`** over `[v0,v1,v2,v3]`. -/
def sipV0Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- a0 = v0 + v1            v0 = .here, v1 = .there.here
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
  -- d0sh = a0 <<< 32        a0 = .here
  (.var { op := .shlImm 64 32, retTy_eq := rfl, args := .cons .here .nil }
  -- d0sr = a0 >>> 32        a0 = .there.here
  (.var { op := .shrImm 64 32, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- d0 = d0sh ||| d0sr      d0sh = .there.here, d0sr = .here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- a2 = v2 + v3            v2 = .there⁵.here (under a0,d0sh,d0sr,d0 = 4 binders), v3 = .there⁶.here
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) }
  -- r3sh = v3 <<< 16        v3 = .there⁷.here (now 5 binders above inputs)
  (.var { op := .shlImm 64 16, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil }
  -- r3sr = v3 >>> 48        v3 = .there⁸.here (6 binders above)
  (.var { op := .shrImm 64 48, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil }
  -- r3 = r3sh ||| r3sr      r3sh = .there.here, r3sr = .here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- c3 = r3 ^^^ a2          r3 = .here, a2 = .there.there.there.here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
  -- v0' = d0 + c3           d0 = .there⁵.here, c3 = .here
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil) }
    (.ret .here))))))))))

/-- `sipV0Com` is in the supported straight-line fragment. -/
theorem sipV0Com_ok : ComOK sipV0Com :=
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

/-- **Step 2 — value proof, cheap `rfl`** (explicit shift-or rotate form). -/
theorem sipV0Com_denote (v0 v1 v2 v3 : BitVec 64) :
    Com.denote sipV0Com (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (((v0 + v1) <<< 32) ||| ((v0 + v1) >>> 32))
          + (((v3 <<< 16) ||| (v3 >>> 48)) ^^^ (v2 + v3)) := by
  unfold sipV0Com
  rfl

/-- **The recognizable `SipRound` `v0'` spec**:
    `v0' = ROTL(v0+v1,32) + (ROTL(v3,16) ^^^ (v2+v3))`. The shift-or rotate synthesis is
    certified by the shared `rotl_synth` identity (no `bv_decide`). -/
theorem sipV0Com_spec (v0 v1 v2 v3 : BitVec 64) :
    Com.denote sipV0Com (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = ((v0 + v1).rotateLeft 32) + ((v3.rotateLeft 16) ^^^ (v2 + v3)) := by
  rw [sipV0Com_denote, rotl_synth (v0 + v1) 32 (by decide) (by decide),
    rotl_synth v3 16 (by decide) (by decide)]

/-- **`v0'` emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem sipV0Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg sipV0Com 4))).regs)
        (comRetName sipV0Com 4)
      = Com.denote sipV0Com V :=
  com_arm_e2e sipV0Com_ok allReg64_four V s hs

/-- **`v0'` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem sipV0Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg sipV0Com 4))).regs)
        (comRetName sipV0Com 4)
      = Com.denote sipV0Com V :=
  com_riscv_e2e sipV0Com_ok allReg64_four V s hs

/-- **The x86 owned-emit leg** for `v0'` (KAT-gated tier). -/
def sipV0Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 sipV0Com "siphash_round_v0"

/-! ## `v2'` — the third output word

`v2' = ROTL(e2, 32)` with `e2 = (v2+v3) + c1`, `c1 = ROTL(v1,13) ^^^ (v0+v1)`.
Program over `[v0,v1,v2,v3]`:
```
a0   = v0 + v1
r1sh = v1 <<< 13     r1sr = v1 >>> 51     r1 = r1sh ||| r1sr    -- ROTL(v1,13)
c1   = r1 ^^^ a0
a2   = v2 + v3
e2   = a2 + c1
e2sh = e2 <<< 32     e2sr = e2 >>> 32     v2' = e2sh ||| e2sr   -- ROTL(e2,32)
```
-/

/-- **`SipRound` output `v2'`** over `[v0,v1,v2,v3]`. -/
def sipV2Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- a0 = v0 + v1          v0=.here, v1=.there.here
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
  -- r1sh = v1 <<< 13      v1=.there.there.here
  (.var { op := .shlImm 64 13, retTy_eq := rfl, args := .cons (.there (.there .here)) .nil }
  -- r1sr = v1 >>> 51      v1=.there³.here  (64-13=51)
  (.var { op := .shrImm 64 51, retTy_eq := rfl, args := .cons (.there (.there (.there .here))) .nil }
  -- r1 = r1sh ||| r1sr    r1sh=.there.here, r1sr=.here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- c1 = r1 ^^^ a0        r1=.here, a0=.there³.here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
  -- a2 = v2 + v3          v2=.there⁷.here, v3=.there⁸.here
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) }
  -- e2 = a2 + c1          a2=.here, c1=.there.here
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- e2sh = e2 <<< 32      e2=.here
  (.var { op := .shlImm 64 32, retTy_eq := rfl, args := .cons .here .nil }
  -- e2sr = e2 >>> 32      e2=.there.here
  (.var { op := .shrImm 64 32, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- v2' = e2sh ||| e2sr   e2sh=.there.here, e2sr=.here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here))))))))))

/-- `sipV2Com` is in the supported straight-line fragment. -/
theorem sipV2Com_ok : ComOK sipV2Com :=
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

/-- **Step 2 — value proof** (explicit shift-or rotate form). -/
theorem sipV2Com_denote (v0 v1 v2 v3 : BitVec 64) :
    Com.denote sipV2Com (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c1 := ((v1 <<< 13) ||| (v1 >>> 51)) ^^^ (v0 + v1)
         let e2 := (v2 + v3) + c1
         (e2 <<< 32) ||| (e2 >>> 32)) := by
  unfold sipV2Com
  rfl

/-- **The recognizable `SipRound` `v2'` spec**:
    `v2' = ROTL((v2+v3) + (ROTL(v1,13) ^^^ (v0+v1)), 32)`. Certified by the shared
    `rotl_synth` identity (no `bv_decide`). -/
theorem sipV2Com_spec (v0 v1 v2 v3 : BitVec 64) :
    Com.denote sipV2Com (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (((v2 + v3) + ((v1.rotateLeft 13) ^^^ (v0 + v1))).rotateLeft 32) := by
  rw [sipV2Com_denote, rotl_synth v1 13 (by decide) (by decide),
    rotl_synth _ 32 (by decide) (by decide)]

/-- **`v2'` emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem sipV2Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg sipV2Com 4))).regs)
        (comRetName sipV2Com 4)
      = Com.denote sipV2Com V :=
  com_arm_e2e sipV2Com_ok allReg64_four V s hs

/-- **`v2'` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem sipV2Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg sipV2Com 4))).regs)
        (comRetName sipV2Com 4)
      = Com.denote sipV2Com V :=
  com_riscv_e2e sipV2Com_ok allReg64_four V s hs

/-- **The x86 owned-emit leg** for `v2'` (KAT-gated tier). -/
def sipV2Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 sipV2Com "siphash_round_v2"

/-! ## `v1'` — the second output word

`v1' = ROTL(c1, 17) ^^^ e2` with `c1 = ROTL(v1,13) ^^^ (v0+v1)`, `e2 = (v2+v3) + c1`.
Program shares the first seven ops with `sipV2Com` (through `e2`), then rotates `c1`:
```
... a0, r1, c1, a2, e2 as above ...
c1sh = c1 <<< 17     c1sr = c1 >>> 47     c1rot = c1sh ||| c1sr   -- ROTL(c1,17)
v1'  = c1rot ^^^ e2
```
-/

/-- **`SipRound` output `v1'`** over `[v0,v1,v2,v3]`. -/
def sipV1Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- a0 = v0 + v1
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
  -- r1sh = v1 <<< 13
  (.var { op := .shlImm 64 13, retTy_eq := rfl, args := .cons (.there (.there .here)) .nil }
  -- r1sr = v1 >>> 51
  (.var { op := .shrImm 64 51, retTy_eq := rfl, args := .cons (.there (.there (.there .here))) .nil }
  -- r1 = r1sh ||| r1sr
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- c1 = r1 ^^^ a0       r1=.here, a0=.there³.here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
  -- a2 = v2 + v3         v2=.there⁷.here, v3=.there⁸.here
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                    (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) }
  -- e2 = a2 + c1         a2=.here, c1=.there.here
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) }
  -- c1sh = c1 <<< 17     c1=.there.there.here  (ctxt [e2,a2,c1,...])
  (.var { op := .shlImm 64 17, retTy_eq := rfl, args := .cons (.there (.there .here)) .nil }
  -- c1sr = c1 >>> 47     c1=.there³.here       (64-17=47)
  (.var { op := .shrImm 64 47, retTy_eq := rfl, args := .cons (.there (.there (.there .here))) .nil }
  -- c1rot = c1sh ||| c1sr  c1sh=.there.here, c1sr=.here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- v1' = c1rot ^^^ e2   c1rot=.here, e2=.there³.here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
    (.ret .here)))))))))))

/-- `sipV1Com` is in the supported straight-line fragment. -/
theorem sipV1Com_ok : ComOK sipV1Com :=
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

/-- **Step 2 — value proof** (explicit shift-or rotate form). -/
theorem sipV1Com_denote (v0 v1 v2 v3 : BitVec 64) :
    Com.denote sipV1Com (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c1 := ((v1 <<< 13) ||| (v1 >>> 51)) ^^^ (v0 + v1)
         let e2 := (v2 + v3) + c1
         ((c1 <<< 17) ||| (c1 >>> 47)) ^^^ e2) := by
  unfold sipV1Com
  rfl

/-- **The recognizable `SipRound` `v1'` spec**:
    `v1' = ROTL(c1,17) ^^^ ((v2+v3)+c1)` with `c1 = ROTL(v1,13) ^^^ (v0+v1)`.
    Certified by the shared `rotl_synth` identity (no `bv_decide`). -/
theorem sipV1Com_spec (v0 v1 v2 v3 : BitVec 64) :
    Com.denote sipV1Com (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c1 := (v1.rotateLeft 13) ^^^ (v0 + v1)
         (c1.rotateLeft 17) ^^^ ((v2 + v3) + c1)) := by
  rw [sipV1Com_denote]; simp only [rotl_synth v1 13 (by decide) (by decide)]
  rw [rotl_synth _ 17 (by decide) (by decide)]

/-- **`v1'` emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem sipV1Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg sipV1Com 4))).regs)
        (comRetName sipV1Com 4)
      = Com.denote sipV1Com V :=
  com_arm_e2e sipV1Com_ok allReg64_four V s hs

/-- **`v1'` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem sipV1Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg sipV1Com 4))).regs)
        (comRetName sipV1Com 4)
      = Com.denote sipV1Com V :=
  com_riscv_e2e sipV1Com_ok allReg64_four V s hs

/-- **The x86 owned-emit leg** for `v1'` (KAT-gated tier). -/
def sipV1Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 sipV1Com "siphash_round_v1"

/-! ## `v3'` — the fourth (deepest) output word

`v3' = ROTL(c3, 21) ^^^ e0` with `c3 = ROTL(v3,16) ^^^ (v2+v3)`,
`e0 = v0' = ROTL(v0+v1,32) + c3`. Program shares the first ten ops with `sipV0Com`
(through `e0`), then rotates `c3` and xors with `e0`:
```
... a0, d0, a2, r3 (=ROTL(v3,16)), c3, e0 (=v0') as in sipV0Com ...
c3sh = c3 <<< 21     c3sr = c3 >>> 43     c3rot = c3sh ||| c3sr   -- ROTL(c3,21)
v3'  = c3rot ^^^ e0
```
-/

/-- **`SipRound` output `v3'`** over `[v0,v1,v2,v3]`. -/
def sipV3Com : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- a0 = v0 + v1
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons .here (.cons (.there .here) .nil) }
  -- d0sh = a0 <<< 32
  (.var { op := .shlImm 64 32, retTy_eq := rfl, args := .cons .here .nil }
  -- d0sr = a0 >>> 32
  (.var { op := .shrImm 64 32, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- d0 = d0sh ||| d0sr
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- a2 = v2 + v3        v2=.there⁵.here, v3=.there⁶.here
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there .here))))))
                    (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) }
  -- r3sh = v3 <<< 16    v3=.there⁷.here
  (.var { op := .shlImm 64 16, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil }
  -- r3sr = v3 >>> 48    v3=.there⁸.here
  (.var { op := .shrImm 64 48, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil }
  -- r3 = r3sh ||| r3sr  r3sh=.there.here, r3sr=.here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- c3 = r3 ^^^ a2      r3=.here, a2=.there³.here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
  -- e0 = d0 + c3        d0=.there⁵.here, c3=.here
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil) }
  -- c3sh = c3 <<< 21    c3=.there.here       (ctxt [e0,c3,r3,...])
  (.var { op := .shlImm 64 21, retTy_eq := rfl, args := .cons (.there .here) .nil }
  -- c3sr = c3 >>> 43    c3=.there.there.here  (64-21=43)
  (.var { op := .shrImm 64 43, retTy_eq := rfl, args := .cons (.there (.there .here)) .nil }
  -- c3rot = c3sh ||| c3sr  c3sh=.there.here, c3sr=.here
  (.var { op := .regArith .or 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
  -- v3' = c3rot ^^^ e0   c3rot=.here, e0=.there³.here
  (.var { op := .regArith .xor 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) }
    (.ret .here))))))))))))))

/-- `sipV3Com` is in the supported straight-line fragment. -/
theorem sipV3Com_ok : ComOK sipV3Com :=
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
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.var (by supported_op)
  (ComOK.ret _))))))))))))))

/-- **Step 2 — value proof** (explicit shift-or rotate form). -/
theorem sipV3Com_denote (v0 v1 v2 v3 : BitVec 64) :
    Com.denote sipV3Com (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c3 := ((v3 <<< 16) ||| (v3 >>> 48)) ^^^ (v2 + v3)
         let e0 := (((v0 + v1) <<< 32) ||| ((v0 + v1) >>> 32)) + c3
         ((c3 <<< 21) ||| (c3 >>> 43)) ^^^ e0) := by
  unfold sipV3Com
  rfl

/-- **The recognizable `SipRound` `v3'` spec**:
    `v3' = ROTL(c3,21) ^^^ e0` with `c3 = ROTL(v3,16) ^^^ (v2+v3)` and
    `e0 = ROTL(v0+v1,32) + c3` (the new `v0'`). Certified by the shared `rotl_synth`
    identity (no `bv_decide`). -/
theorem sipV3Com_spec (v0 v1 v2 v3 : BitVec 64) :
    Com.denote sipV3Com (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))))
      = (let c3 := (v3.rotateLeft 16) ^^^ (v2 + v3)
         (c3.rotateLeft 21) ^^^ (((v0 + v1).rotateLeft 32) + c3)) := by
  rw [sipV3Com_denote]
  simp only [rotl_synth v3 16 (by decide) (by decide),
    rotl_synth (v0 + v1) 32 (by decide) (by decide)]
  rw [rotl_synth _ 21 (by decide) (by decide)]

/-- **`v3'` emits to AArch64**, discharged by `com_arm_e2e`. -/
theorem sipV3Com_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg sipV3Com 4))).regs)
        (comRetName sipV3Com 4)
      = Com.denote sipV3Com V :=
  com_arm_e2e sipV3Com_ok allReg64_four V s hs

/-- **`v3'` emits to RISC-V** — same source, same `comToReg_faithful`. -/
theorem sipV3Com_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg sipV3Com 4))).regs)
        (comRetName sipV3Com 4)
      = Com.denote sipV3Com V :=
  com_riscv_e2e sipV3Com_ok allReg64_four V s hs

/-- **The x86 owned-emit leg** for `v3'` (KAT-gated tier). -/
def sipV3Com_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 sipV3Com "siphash_round_v3"

end CatCrypt.Crypto.SecureCompilation.SipHashRound
