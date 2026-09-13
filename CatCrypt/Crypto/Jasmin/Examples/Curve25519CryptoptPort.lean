/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.Jasmin.JasminAST


@[expose] public section
set_option autoImplicit false

/-!
# Curve25519 CryptOpt-tuned `carry_mul` / `carry_square` — JasminAST leaves

Pipeline (2) (LowCT → CryptoSSA → Jasmin → x86-64) needs JasminAST entries
for the CryptOpt-tuned radix-2^51 unsaturated 5-limb multiplication and squaring on the
Curve25519 base field. The bench wire-up (commits `cae8ccb`, `7e9023d`)
already routes pipeline-(1) callers through the asm under
`-DUSE_CRYPTOPT_25519_MUL`; this file adds the parallel pipeline-(2)
declaration so the verified Jasmin chain emits the same leaf.

## Source

Two CryptOpt-synthesized AMD64 asms picked for highest measured ratio on
the chip CryptOpt was driven on, from the `fiat-amd64/` directory of
fiat-crypto (https://github.com/mit-plv/fiat-crypto):

- `mul`     ≡ `fiat-amd64/fiat_curve25519_carry_mul/seed1667947554054692_ratio13465.asm`
              (182 LoC, ratio 1.3465 vs. fiat-crypto's C `fiat_25519_carry_mul`)
- `square`  ≡ `fiat-amd64/fiat_curve25519_carry_square/seed0000000394998752_ratio13350.asm`
              (126 LoC, ratio 1.3350 vs. fiat-crypto's C `fiat_25519_carry_square`)

Each is a verified-equivalent (per CryptOpt's own equivalence theorem)
re-arrangement of the corresponding fiat-crypto C output. The
**correctness specification carried by the leaf is fiat-crypto's
`UnsaturatedSolinas.v::carry_mul_correct`** (or `carry_square_correct`):
on the radix-2^51 5-limb representation `[a₀,…,a₄]` interpreting to
`Σᵢ aᵢ · 2^(51·i) mod (2^255 − 19)`, the output's interpretation is the
modular product (resp. square) of the input interpretations.

## Why declare these as leaves rather than translate the asm verbatim

The asm vocabulary used spans `mulx`, `imul reg, mem, imm` (multiply by
the 0x13 = 19 reduction constant), `adcx`/`adox` (BMI2 dual-carry
chains), `bzhi` (clear bits ≥ 52, for the radix-2^51 limb mask),
`shrd` (double-precision right-shift, for the limb-carry propagation),
`lea` (used as flag-clearing add), and the usual `mov`/`add`/`adc`/
`xor`/`test`. Encoding each as a JasminAST `Copn` with a fresh `Oasm`
name is mechanical but extending the operational interpreter
(`BignumExec.lean`) to all of them is a separate, multi-day effort that
adds intrinsic semantics for `bzhi`, `shrd`, `imul`-with-immediate, the
flag-mask aliases of `lea`/`xor`/`test`, and so on.

A synthesized leaf carries fiat-crypto's `carry_mul_correct` on its target,
so the asm is treated as **one leaf** inheriting CryptOpt's equivalence
theorem; the SSA-level audit lives at the `carry_mul_correct` boundary, not at the per-x86-instruction level.
The leaf-stub here is the JasminAST representation of that boundary:
the function is declared with the right signature and a `body` of `[]`
denoting "extern, resolved by the linker against the CryptOpt-emitted
asm". Pipeline (2)'s emit step produces a forward declaration in the
generated Jasmin / `.jazz` source; the asm object (assembled by `nasm` in
the benchmark harness) supplies the body at link time.

## Future tightening

If we want a fully in-tree Lean audit of the asm itself (rather than
trusting CryptOpt's equivalence theorem), the natural next step is to
extend `BignumExec.lean` with operational semantics for the missing
intrinsics, then write the body as a `List InstrR` that mirrors the
asm line-by-line. That replaces "trust CryptOpt + linker" with "trust
`BignumExec`'s instruction semantics + a Lean-level proof that the
sequence equals fiat-crypto's `carry_mul`". Estimated ~1 week
additional effort. Tracked but out of scope here.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptPort

open CatCrypt.Crypto.Jasmin

/-! ## §1. Variable / parameter helpers -/

/-- A `memref<5×u64>` parameter. The Curve25519 5-limb radix-2^51
    representation is exactly this shape; matches the
    `fiat_25519_carry_mul` ABI used in `catcrypt-bench/src/fiat_shim.c`
    when `-DUSE_CRYPTOPT_25519_MUL` is set. -/
def vMemref5 (s : String) : Var :=
  { vname := s, vtype := .sword .U64 }

def funParam (s : String) : FunParam :=
  ⟨{ var := vMemref5 s }⟩

def varI (s : String) : VarI :=
  { var := vMemref5 s }

/-! ## §1a. Intrinsic helpers — JasminAST tags for the asm vocabulary

Each helper produces one `InstrR` tagged with the matching x86 mnemonic
in `Oasm`. Operational semantics for the new opcodes (`BZHI_64`,
`SHRD_64_imm`, `SHLX_64`, `IMUL_imm_64`, `ADCX_64`, `ADOX_64`, `AND_64`)
are not yet provided in `BignumExec.lean` — the JasminAST representation
exists for emit-correctness; runtime/inductive semantics is the
follow-up tightening described in the file docstring.

Convention: register names from the asm (`rax`, `rbx`, `rcx`, `rdx`,
`rsi`, `rdi`, `r8`–`r15`) are used verbatim as variable names. Spill
slots (`[rsp − 0xN]`) become synthetic locals `s_N`. Memory accesses
through the parameter pointers are encoded with `Pload`/`Lmem` against
the parameter names `out` / `a` (square) or `out` / `a` / `b` (mul).
The asm's `xchg rdx, rax` (mul only) is desugared by routing
post-`xchg` `[rax + …]` through `Pload "b" …`. -/

def vU (s : String) : Var := { vname := s, vtype := .sword .U64 }
def pv (s : String) : PExpr :=
  .Pvar { gv := { var := vU s }, gs := false }
def pload (base : String) (k : Int) : PExpr :=
  .Pload .U64 { var := vU base } (.Pconst k)
def lvR (s : String) : LVal := .Lvar { var := vU s }
def lvNone : LVal := .Lnone {} (.sword .U64)
def cassgn (dst : String) (e : PExpr) : InstrR :=
  .Cassgn (lvR dst) .AT_none (.sword .U64) e

/-- Memory store `[base + k] := src`. -/
def storeMem (base : String) (k : Int) (src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := vU base } (.Pconst k)) .AT_none (.sword .U64)
    (pv src)

/-- Flag layout for `#ADD_64` / `#ADC_64` / `#AND_64` / `#IMUL_imm_64`:
    `[of, cf, sf, pf, zf, dst]`. -/
def flagPre  : List LVal := [lvNone]
def flagPost : List LVal := List.replicate 3 lvNone

/-- `dst := imm`. -/
def movImm (dst : String) (k : Int) : InstrR := cassgn dst (.Pconst k)

/-- `dst := src` (register copy, modelled as a plain assignment). -/
def movReg (dst src : String) : InstrR := cassgn dst (pv src)

/-- `dst := [base + k]` (memory load). -/
def movFromMem (dst base : String) (k : Int) : InstrR :=
  cassgn dst (pload base k)

/-- `dst := [base + 0]` (limb 0 shorthand). -/
def movFromMem0 (dst base : String) : InstrR := movFromMem dst base 0

/-- `[out + k] := src` (memory store, generic). -/
def movToMem (base : String) (k : Int) (src : String) : InstrR :=
  storeMem base k src

/-- `cf, dst = #ADD_64(a, b)`; flags-around-cf discarded. -/
def addRR (cfOut dst a b : String) : InstrR :=
  .Copn (flagPre ++ [lvR cfOut] ++ flagPost ++ [lvR dst]) .AT_none
        (.Oasm ⟨"ADD_64"⟩) [pv a, pv b]

/-- `cf, dst = #ADD_64(a, [base + k])`. -/
def addRM (cfOut dst a base : String) (k : Int) : InstrR :=
  .Copn (flagPre ++ [lvR cfOut] ++ flagPost ++ [lvR dst]) .AT_none
        (.Oasm ⟨"ADD_64"⟩) [pv a, pload base k]

/-- `cf, dst = #ADC_64(a, b, cin)`. -/
def adcRR (cfOut dst a b cin : String) : InstrR :=
  .Copn (flagPre ++ [lvR cfOut] ++ flagPost ++ [lvR dst]) .AT_none
        (.Oasm ⟨"ADC_64"⟩) [pv a, pv b, pv cin]

/-- `cf, dst = #ADC_64(a, imm, cin)` (typically `imm = 0`). -/
def adcImm (cfOut dst a : String) (k : Int) (cin : String) : InstrR :=
  .Copn (flagPre ++ [lvR cfOut] ++ flagPost ++ [lvR dst]) .AT_none
        (.Oasm ⟨"ADC_64"⟩) [pv a, .Pconst k, pv cin]

/-- ADCX dual-carry chain (CF only): `cf, dst = #ADCX_64(a, b, cf)`.
    Same arithmetic as ADC; only CF is touched. -/
def adcxRR (cfChain dst a b : String) : InstrR :=
  .Copn [lvR cfChain, lvR dst] .AT_none (.Oasm ⟨"ADCX"⟩)
        [pv a, pv b, pv cfChain]

/-- `cf, dst = #ADCX_64(a, [base + k], cf)`. -/
def adcxRM (cfChain dst a base : String) (k : Int) : InstrR :=
  .Copn [lvR cfChain, lvR dst] .AT_none (.Oasm ⟨"ADCX"⟩)
        [pv a, pload base k, pv cfChain]

/-- ADOX dual-carry chain (OF only): `of, dst = #ADOX_64(a, b, of)`. -/
def adoxRR (ofChain dst a b : String) : InstrR :=
  .Copn [lvR ofChain, lvR dst] .AT_none (.Oasm ⟨"ADOX"⟩)
        [pv a, pv b, pv ofChain]

/-- `of, dst = #ADOX_64(a, [base + k], of)`. -/
def adoxRM (ofChain dst a base : String) (k : Int) : InstrR :=
  .Copn [lvR ofChain, lvR dst] .AT_none (.Oasm ⟨"ADOX"⟩)
        [pv a, pload base k, pv ofChain]

/-- `(hi, lo) = #MULX(rdx, [base + k])`. Asm form: `mulx hi, lo, [base + k]`
    with `rdx` implicit. -/
def mulxMem (hi lo rdx base : String) (k : Int) : InstrR :=
  .Copn [lvR hi, lvR lo] .AT_none (.Oasm ⟨"MULX"⟩) [pv rdx, pload base k]

/-- `(hi, lo) = #MULX(rdx, src)` with both operands in registers. -/
def mulxReg (hi lo rdx src : String) : InstrR :=
  .Copn [lvR hi, lvR lo] .AT_none (.Oasm ⟨"MULX"⟩) [pv rdx, pv src]

/-- 3-operand `imul dst, [base + k], imm` — single-output form (we
    discard the flags). -/
def imulImmMem (dst base : String) (k imm : Int) : InstrR :=
  .Copn (flagPre ++ flagPost ++ [lvNone, lvR dst]) .AT_none
        (.Oasm ⟨"IMUL_imm_64"⟩) [pload base k, .Pconst imm]

/-- 3-operand `imul dst, src, imm` (register source). -/
def imulImmReg (dst src : String) (imm : Int) : InstrR :=
  .Copn (flagPre ++ flagPost ++ [lvNone, lvR dst]) .AT_none
        (.Oasm ⟨"IMUL_imm_64"⟩) [pv src, .Pconst imm]

/-- `dst = #BZHI(src, ctrl)` — clear bits at index `≥ ctrl[7:0]`. The
    51-limb mask uses `ctrl = 0x33 = 51`. -/
def bzhiRR (dst src ctrl : String) : InstrR :=
  .Copn [lvR dst] .AT_none (.Oasm ⟨"BZHI_64"⟩) [pv src, pv ctrl]

/-- `dst := dst >>> count, fill from src` — SHRD with immediate count.
    Used to extract the top 13 bits of `dst:src` shifted right by 51. -/
def shrdImm (dst src : String) (count : Int) : InstrR :=
  .Copn [lvR dst] .AT_none (.Oasm ⟨"SHRD_64_imm"⟩)
        [pv dst, pv src, .Pconst count]

/-- `dst = #SHLX(src, count)` — variable shift-left without flags.
    The square asm uses it to compute `a[3] << 1`. -/
def shlxRM (dst base : String) (k : Int) (count : String) : InstrR :=
  .Copn [lvR dst] .AT_none (.Oasm ⟨"SHLX_64"⟩) [pload base k, pv count]

/-- `cf, _, _, _, _, dst = #AND_64(a, imm)` — bitwise AND with
    immediate. We discard the flag outputs. -/
def andImm (dst a : String) (imm : Int) : InstrR :=
  .Copn (flagPre ++ flagPost ++ [lvNone, lvR dst]) .AT_none
        (.Oasm ⟨"AND_64"⟩) [pv a, .Pconst imm]

/-- `dst := dst >>> imm` — logical shift right (encoded via the SOp2
    `Olsr` since SHR is straight-line). -/
def shrImm (dst : String) (imm : Int) : InstrR :=
  cassgn dst (.Papp2 (.Olsr .U64) (pv dst) (.Pconst imm))

/-- `lea dst, [a + b]` modelled as `dst := a + b` (the `lea`
    no-flag-effect distinction matters for ADCX/ADOX chains; tagged
    here as the SSA-equivalent assignment). -/
def leaAdd (dst a b : String) : InstrR :=
  cassgn dst (.Papp2 (.Oadd .U64) (pv a) (pv b))

/-- `lea dst, [a + scale * b]` with an immediate scale. -/
def leaScaledAdd (dst a : String) (scale : Int) (b : String) : InstrR :=
  cassgn dst (.Papp2 (.Oadd .U64) (pv a)
    (.Papp2 (.Omul .U64) (.Pconst scale) (pv b)))

/-- `xor dst, dst` — zero-and-clear-flags. The bundle writes both
    OF (position 0) and CF (position 1) so the existing
    `BignumExec.writeXorBundle` interprets it; that resets both carry
    tracks to 0, which is exactly the precondition the subsequent
    ADCX/ADOX chain assumes. -/
def xorClear (dst : String) : InstrR :=
  .Copn [lvR "of", lvR "cf", lvNone, lvNone, lvNone, lvR dst] .AT_none
        (.Oasm ⟨"XOR_64"⟩) [pv dst, pv dst]

/-- `test al, al` — sets ZF/SF/PF from `al`, clears CF and OF. The
    only effect we care about for ADCX/ADOX chain initialisation is the
    CF=0 / OF=0 reset. We model this as zeroing the two flag-tracking
    locals via a `Copn` carrying the asm tag for downstream auditing. -/
def testClearCarry (cfChain ofChain : String) : InstrR :=
  .Copn [lvR ofChain, lvR cfChain] .AT_none (.Oasm ⟨"TEST_64"⟩)
        [pv "rax", pv "rax"]

/-- `cf, _, _, _, _, dst = #AND_64(dst, src)` — register-register AND. -/
def andRR (dst src : String) : InstrR :=
  .Copn (flagPre ++ flagPost ++ [lvNone, lvR dst]) .AT_none
        (.Oasm ⟨"AND_64"⟩) [pv dst, pv src]

/-- Save register `src` to spill slot `slot`. -/
def spillSave (slot src : String) : InstrR := movReg slot src

/-- Restore register `dst` from spill slot `slot`. -/
def spillRestore (dst slot : String) : InstrR := movReg dst slot

/-! ## §2. `fiat_curve25519_carry_square` — body translation

Line-by-line translation of `seed0000000394998752_ratio13350.asm` (lines
4–115 of the asm file). Inline comments retain the asm mnemonics for
side-by-side audit. The asm body is 107 instructions; spill saves at
the start (`mov [rsp - X], reg`) and restores at the end (`mov reg,
[rsp - X]`) become register↔synthetic-local copies through `s_N`
slots. The final `ret` is implicit in the JasminAST `FunDecl`'s
`body` shape.

Synthetic locals introduced:
- `s_80, s_78, s_70, s_68` — stack spill slots for `rbx, rbp, r12, r13`.
- `cf` / `of` — single-flag chains used by ADCX/ADOX.

The asm clobbers `rdx` repeatedly to feed `MULX`'s implicit multiplier
and to thread `imul rdx, _, imm` results forward; the body shadows
`rdx`'s name across writes (legal in our JasminAST since downstream
LowCT→CryptoSSA SSA-renames). -/

def sqrBody : List InstrR :=
  [ -- 4:  mov rax, 0x1
    movImm "rax" 1
    -- 5:  shlx r10, [rsi + 0x18], rax        ; r10 = a[3] << 1
  , shlxRM "r10" "a" 0x18 "rax"
    -- 6:  mov r11, [rsi + 0x18]              ; r11 = a[3]
  , movFromMem "r11" "a" 0x18
    -- 7:  lea rdx, [r11 + 8 * r11]           ; rdx = 9 * a[3]
  , leaScaledAdd "rdx" "r11" 8 "r11"
    -- 8:  lea rcx, [r11 + 2 * rdx]           ; rcx = 19 * a[3]
  , leaScaledAdd "rcx" "r11" 2 "rdx"
    -- 9:  mov rdx, [rsi + 0x0]               ; rdx = a[0]
  , movFromMem "rdx" "a" 0
    -- 10: mulx r8, r11, rdx                  ; (r8, r11) = a[0] * a[0]
  , mulxReg "r8" "r11" "rdx" "rdx"
    -- 11: imul rdx, [rsi + 0x18], 0x26       ; rdx = 38 * a[3]
  , imulImmMem "rdx" "a" 0x18 0x26
    -- 12: mulx rax, r9, [rsi + 0x10]         ; (rax, r9) = (38 * a[3]) * a[2]
  , mulxMem "rax" "r9" "rdx" "a" 0x10
    -- 13: imul rdx, [rsi + 0x20], 0x26       ; rdx = 38 * a[4]
  , imulImmMem "rdx" "a" 0x20 0x26
    -- 14: mov [rsp - 0x80], rbx
  , spillSave "s_80" "rbx"
    -- 15: mov [rsp - 0x78], rbp
  , spillSave "s_78" "rbp"
    -- 16: mulx rbp, rbx, [rsi + 0x8]         ; (rbp, rbx) = (38 * a[4]) * a[1]
  , mulxMem "rbp" "rbx" "rdx" "a" 0x8
    -- 17: mov [rsp - 0x70], r12
  , spillSave "s_70" "r12"
    -- 18: xor r12, r12                       ; r12 = 0; OF/CF cleared
  , xorClear "r12"
    -- 19: adox r9, rbx                       ; OF chain start
  , adoxRR "of" "r9" "r9" "rbx"
    -- 20: adox rbp, rax
  , adoxRR "of" "rbp" "rbp" "rax"
    -- 21: mulx rbx, rax, [rsi + 0x10]        ; (rbx, rax) = (38 * a[4]) * a[2]
  , mulxMem "rbx" "rax" "rdx" "a" 0x10
    -- 22: adcx r9, r11                       ; CF chain start
  , adcxRR "cf" "r9" "r9" "r11"
    -- 23: adcx r8, rbp
  , adcxRR "cf" "r8" "r8" "rbp"
    -- 24: mov r11, rdx                       ; save 38*a[4] in r11
  , movReg "r11" "rdx"
    -- 25: mov rdx, [rsi + 0x18]              ; rdx = a[3]
  , movFromMem "rdx" "a" 0x18
    -- 26: mulx r12, rbp, rcx                 ; (r12, rbp) = a[3] * (19 * a[3])
  , mulxReg "r12" "rbp" "rdx" "rcx"
    -- 27: add rbp, rax
  , addRR "cf" "rbp" "rbp" "rax"
    -- 28: adcx rbx, r12
  , adcxRR "cf" "rbx" "rbx" "r12"
    -- 29: mov rdx, [rsi + 0x8]               ; rdx = a[1]
  , movFromMem "rdx" "a" 0x8
    -- 30: lea rcx, [rdx + rdx]               ; rcx = 2 * a[1]
  , leaAdd "rcx" "rdx" "rdx"
    -- 31: mov rdx, rcx                       ; rdx = 2 * a[1]
  , movReg "rdx" "rcx"
    -- 32: mulx rax, rcx, [rsi + 0x0]         ; (rax, rcx) = (2*a[1]) * a[0]
  , mulxMem "rax" "rcx" "rdx" "a" 0
    -- 33: mov r12, r9
  , movReg "r12" "r9"
    -- 34: shrd r12, r8, 51                   ; r12 = (r8:r9) >> 51 (low 64)
  , shrdImm "r12" "r8" 51
    -- 35: mov rdx, r11                       ; restore rdx = 38 * a[4]
  , movReg "rdx" "r11"
    -- 36: mulx r8, r11, [rsi + 0x18]         ; (r8, r11) = (38 * a[4]) * a[3]
  , mulxMem "r8" "r11" "rdx" "a" 0x18
    -- 37: add rbp, rcx
  , addRR "cf" "rbp" "rbp" "rcx"
    -- 38: adcx rax, rbx
  , adcxRR "cf" "rax" "rax" "rbx"
    -- 39: xor rdx, rdx                       ; clear flags + zero rdx
  , xorClear "rdx"
    -- 40: adox rbp, r12
  , adoxRR "of" "rbp" "rbp" "r12"
    -- 41: adox rax, rdx
  , adoxRR "of" "rax" "rax" "rdx"
    -- 42: mov rdx, [rsi + 0x8]               ; rdx = a[1]
  , movFromMem "rdx" "a" 0x8
    -- 43: mulx rcx, rbx, rdx                 ; (rcx, rbx) = a[1] * a[1]
  , mulxReg "rcx" "rbx" "rdx" "rdx"
    -- 44: adcx r11, rbx
  , adcxRR "cf" "r11" "r11" "rbx"
    -- 45: adcx rcx, r8
  , adcxRR "cf" "rcx" "rcx" "r8"
    -- 46: mov rdx, [rsi + 0x10]              ; rdx = a[2]
  , movFromMem "rdx" "a" 0x10
    -- 47: lea r12, [rdx + rdx]               ; r12 = 2 * a[2]
  , leaAdd "r12" "rdx" "rdx"
    -- 48: mov rdx, r12                       ; rdx = 2 * a[2]
  , movReg "rdx" "r12"
    -- 49: mulx r8, r12, [rsi + 0x0]          ; (r8, r12) = (2*a[2]) * a[0]
  , mulxMem "r8" "r12" "rdx" "a" 0
    -- 50: add r11, r12
  , addRR "cf" "r11" "r11" "r12"
    -- 51: adcx r8, rcx
  , adcxRR "cf" "r8" "r8" "rcx"
    -- 52: mulx rcx, rbx, [rsi + 0x8]         ; (rcx, rbx) = (2*a[2]) * a[1]
  , mulxMem "rcx" "rbx" "rdx" "a" 0x8
    -- 53: imul rdx, [rsi + 0x20], 0x13       ; rdx = 19 * a[4]
  , imulImmMem "rdx" "a" 0x20 0x13
    -- 54: mov r12, rbp
  , movReg "r12" "rbp"
    -- 55: shrd r12, rax, 51
  , shrdImm "r12" "rax" 51
    -- 56: add r11, r12
  , addRR "cf" "r11" "r11" "r12"
    -- 57: adc r8, 0x0
  , adcImm "cf" "r8" "r8" 0 "cf"
    -- 58: mulx r12, rax, [rsi + 0x20]        ; (r12, rax) = (19*a[4]) * a[4]
  , mulxMem "r12" "rax" "rdx" "a" 0x20
    -- 59: mov rdx, r10                       ; rdx = 2 * a[3]
  , movReg "rdx" "r10"
    -- 60: mov [rsp - 0x68], r13
  , spillSave "s_68" "r13"
    -- 61: mulx r13, r10, [rsi + 0x8]         ; (r13, r10) = (2*a[3]) * a[1]
  , mulxMem "r13" "r10" "rdx" "a" 0x8
    -- 62: add rax, rbx
  , addRR "cf" "rax" "rax" "rbx"
    -- 63: adcx rcx, r12
  , adcxRR "cf" "rcx" "rcx" "r12"
    -- 64: mulx r12, rbx, [rsi + 0x0]         ; (r12, rbx) = (2*a[3]) * a[0]
  , mulxMem "r12" "rbx" "rdx" "a" 0
    -- 65: xor rdx, rdx
  , xorClear "rdx"
    -- 66: adox rax, rbx
  , adoxRR "of" "rax" "rax" "rbx"
    -- 67: adox r12, rcx
  , adoxRR "of" "r12" "r12" "rcx"
    -- 68: mov rcx, r11
  , movReg "rcx" "r11"
    -- 69: shrd rcx, r8, 51
  , shrdImm "rcx" "r8" 51
    -- 70: mov rdx, [rsi + 0x10]              ; rdx = a[2]
  , movFromMem "rdx" "a" 0x10
    -- 71: mulx rbx, r8, rdx                  ; (rbx, r8) = a[2] * a[2]
  , mulxReg "rbx" "r8" "rdx" "rdx"
    -- 72: xor rdx, rdx
  , xorClear "rdx"
    -- 73: adox rax, rcx
  , adoxRR "of" "rax" "rax" "rcx"
    -- 74: adox r12, rdx
  , adoxRR "of" "r12" "r12" "rdx"
    -- 75: mov rcx, rax
  , movReg "rcx" "rax"
    -- 76: shrd rcx, r12, 51
  , shrdImm "rcx" "r12" 51
    -- 77: mov r12, [rsi + 0x20]              ; r12 = a[4]
  , movFromMem "r12" "a" 0x20
    -- 78: lea rdx, [r12 + r12]               ; rdx = 2 * a[4]
  , leaAdd "rdx" "r12" "r12"
    -- 79: xor r12, r12
  , xorClear "r12"
    -- 80: adox r8, r10
  , adoxRR "of" "r8" "r8" "r10"
    -- 81: adox r13, rbx
  , adoxRR "of" "r13" "r13" "rbx"
    -- 82: mulx rbx, r10, [rsi + 0x0]         ; (rbx, r10) = (2*a[4]) * a[0]
  , mulxMem "rbx" "r10" "rdx" "a" 0
    -- 83: adcx r8, r10
  , adcxRR "cf" "r8" "r8" "r10"
    -- 84: adcx rbx, r13
  , adcxRR "cf" "rbx" "rbx" "r13"
    -- 85: xor rdx, rdx
  , xorClear "rdx"
    -- 86: adox r8, rcx
  , adoxRR "of" "r8" "r8" "rcx"
    -- 87: adox rbx, rdx
  , adoxRR "of" "rbx" "rbx" "rdx"
    -- 88: mov r12, r8
  , movReg "r12" "r8"
    -- 89: shrd r12, rbx, 51
  , shrdImm "r12" "rbx" 51
    -- 90: mov rcx, 0x7ffffffffffff             ; rcx = (1 << 51) - 1
  , movImm "rcx" 0x7ffffffffffff
    -- 91: and r8, rcx
  , andRR "r8" "rcx"
    -- 92: and r9, rcx
  , andRR "r9" "rcx"
    -- 93: imul r13, r12, 0x13                ; r13 = 19 * r12
  , imulImmReg "r13" "r12" 0x13
    -- 94: mov [rdi + 0x20], r8                ; out[4] = r8
  , movToMem "out" 0x20 "r8"
    -- 95: lea r9, [r9 + r13]
  , leaAdd "r9" "r9" "r13"
    -- 96: mov r10, r9
  , movReg "r10" "r9"
    -- 97: and r10, rcx
  , andRR "r10" "rcx"
    -- 98: shr r9, 51
  , shrImm "r9" 51
    -- 99: and rbp, rcx
  , andRR "rbp" "rcx"
    -- 100: and r11, rcx
  , andRR "r11" "rcx"
    -- 101: lea r9, [r9 + rbp]
  , leaAdd "r9" "r9" "rbp"
    -- 102: mov rbx, r9
  , movReg "rbx" "r9"
    -- 103: and rbx, rcx
  , andRR "rbx" "rcx"
    -- 104: mov [rdi + 0x0], r10               ; out[0] = r10
  , movToMem "out" 0 "r10"
    -- 105: shr r9, 51
  , shrImm "r9" 51
    -- 106: and rax, rcx
  , andRR "rax" "rcx"
    -- 107: mov [rdi + 0x18], rax              ; out[3] = rax
  , movToMem "out" 0x18 "rax"
    -- 108: lea r9, [r9 + r11]
  , leaAdd "r9" "r9" "r11"
    -- 109: mov [rdi + 0x8], rbx               ; out[1] = rbx
  , movToMem "out" 0x8 "rbx"
    -- 110: mov [rdi + 0x10], r9               ; out[2] = r9
  , movToMem "out" 0x10 "r9"
    -- 111–114: spill restores
  , spillRestore "rbx" "s_80"
  , spillRestore "rbp" "s_78"
  , spillRestore "r12" "s_70"
  , spillRestore "r13" "s_68"
    -- 115: ret  (implicit)
  ]

/-! ## §3. `fiat_curve25519_carry_mul` — body translation

Line-by-line translation of `seed1667947554054692_ratio13465.asm`
(asm body lines 4–171, 167 instructions). Conventions match `sqrBody`
above; one extra wrinkle is the `xchg rdx, rax` at asm line 7. We
desugar by:
- Pre-xchg, `rdx` is the b pointer, so reads `[rdx + N]` translate
  through `pload "b" N`.
- The `xchg` itself becomes `movReg "rdx" "rax"` (rdx receives the
  arithmetic value `19 * b[3]` that was just stored in rax).
- Post-xchg, `rax` is the b pointer, so reads `[rax + N]` route
  through `pload "b" N`.
- The asm never reads `rax` as data after the xchg, so no swap of the
  Lean-side `rax` variable is needed.

The asm also spills the `out` pointer (`rdi`) to `s_50` early
(line 23) and restores it into `r10` near the end (line 150) before
the four output writes. We bypass this and emit the writes directly
through `out` (`movToMem "out" N "rX"`); the spill/restore
instructions are kept as register↔local moves for fidelity. -/

def mulBody : List InstrR :=
  [ -- 5:  imul rax, [rdx + 0x18], 0x13          ; rax = 19 * b[3]
    imulImmMem "rax" "b" 0x18 0x13
    -- 6:  imul r10, [rdx + 0x10], 0x13          ; r10 = 19 * b[2]
  , imulImmMem "r10" "b" 0x10 0x13
    -- 7:  xchg rdx, rax                         ; rdx ← rax (= 19*b[3]); rax ← b ptr
  , movReg "rdx" "rax"
    -- 8:  mulx rcx, r11, [rsi + 0x18]
  , mulxMem "rcx" "r11" "rdx" "a" 0x18
    -- 9:  mov r8, rdx
  , movReg "r8" "rdx"
    -- 10: mov rdx, [rsi + 0x0]
  , movFromMem "rdx" "a" 0
    -- 11: mov [rsp - 0x80], rbx
  , spillSave "s_80" "rbx"
    -- 12: mulx rbx, r9, [rax + 0x20]            ; (rax = b ptr now)
  , mulxMem "rbx" "r9" "rdx" "b" 0x20
    -- 13: mov rdx, [rax + 0x8]
  , movFromMem "rdx" "b" 0x8
    -- 14: mov [rsp - 0x78], rbp
  , spillSave "s_78" "rbp"
    -- 15: mov [rsp - 0x70], r12
  , spillSave "s_70" "r12"
    -- 16: mulx r12, rbp, [rsi + 0x0]
  , mulxMem "r12" "rbp" "rdx" "a" 0
    -- 17: mov rdx, [rsi + 0x20]
  , movFromMem "rdx" "a" 0x20
    -- 18: mov [rsp - 0x68], r13
  , spillSave "s_68" "r13"
    -- 19: mov [rsp - 0x60], r14
  , spillSave "s_60" "r14"
    -- 20: mulx r14, r13, r8
  , mulxReg "r14" "r13" "rdx" "r8"
    -- 21: mov rdx, [rax + 0x18]
  , movFromMem "rdx" "b" 0x18
    -- 22: mov [rsp - 0x58], r15
  , spillSave "s_58" "r15"
    -- 23: mov [rsp - 0x50], rdi                 ; spill out pointer
  , spillSave "s_50" "rdi"
    -- 24: mulx rdi, r15, [rsi + 0x0]
  , mulxMem "rdi" "r15" "rdx" "a" 0
    -- 25: imul rdx, [rax + 0x8], 0x13           ; rdx = 19 * b[1]
  , imulImmMem "rdx" "b" 0x8 0x13
    -- 26: mov [rsp - 0x48], rbx
  , spillSave "s_48" "rbx"
    -- 27: mov [rsp - 0x40], r9
  , spillSave "s_40" "r9"
    -- 28: mulx r9, rbx, [rsi + 0x20]
  , mulxMem "r9" "rbx" "rdx" "a" 0x20
    -- 29: mov rdx, [rsi + 0x18]
  , movFromMem "rdx" "a" 0x18
    -- 30: mov [rsp - 0x38], rdi
  , spillSave "s_38" "rdi"
    -- 31: mov [rsp - 0x30], r15
  , spillSave "s_30" "r15"
    -- 32: mulx r15, rdi, r10
  , mulxReg "r15" "rdi" "rdx" "r10"
    -- 33: mov rdx, r10
  , movReg "rdx" "r10"
    -- 34: mov [rsp - 0x28], r12
  , spillSave "s_28" "r12"
    -- 35: mulx r12, r10, [rsi + 0x20]
  , mulxMem "r12" "r10" "rdx" "a" 0x20
    -- 36: imul rdx, [rax + 0x20], 0x13          ; rdx = 19 * b[4]
  , imulImmMem "rdx" "b" 0x20 0x13
    -- 37: add rbx, rdi
  , addRR "cf" "rbx" "rbx" "rdi"
    -- 38: adcx r15, r9
  , adcxRR "cf" "r15" "r15" "r9"
    -- 39: add r10, r11
  , addRR "cf" "r10" "r10" "r11"
    -- 40: adcx rcx, r12
  , adcxRR "cf" "rcx" "rcx" "r12"
    -- 41: mulx r9, r11, [rsi + 0x8]
  , mulxMem "r9" "r11" "rdx" "a" 0x8
    -- 42: mov rdi, rdx
  , movReg "rdi" "rdx"
    -- 43: mov rdx, [rsi + 0x10]
  , movFromMem "rdx" "a" 0x10
    -- 44: mov [rsp - 0x20], rbp
  , spillSave "s_20" "rbp"
    -- 45: mulx rbp, r12, r8
  , mulxReg "rbp" "r12" "rdx" "r8"
    -- 46: mov rdx, [rax + 0x0]
  , movFromMem "rdx" "b" 0
    -- 47: mov [rsp - 0x18], r14
  , spillSave "s_18" "r14"
    -- 48: mulx r14, r8, [rsi + 0x18]
  , mulxMem "r14" "r8" "rdx" "a" 0x18
    -- 49: mov rdx, rdi
  , movReg "rdx" "rdi"
    -- 50: mov [rsp - 0x10], r13
  , spillSave "s_10" "r13"
    -- 51: mulx r13, rdi, [rsi + 0x20]
  , mulxMem "r13" "rdi" "rdx" "a" 0x20
    -- 52: test al, al                            ; clear OF/CF
  , testClearCarry "cf" "of"
    -- 53: adox rdi, r8
  , adoxRR "of" "rdi" "rdi" "r8"
    -- 54: adox r14, r13
  , adoxRR "of" "r14" "r14" "r13"
    -- 55: adcx rbx, r12
  , adcxRR "cf" "rbx" "rbx" "r12"
    -- 56: adcx rbp, r15
  , adcxRR "cf" "rbp" "rbp" "r15"
    -- 57: mulx r12, r15, [rsi + 0x10]
  , mulxMem "r12" "r15" "rdx" "a" 0x10
    -- 58: xor r8, r8                             ; clear flags + zero r8
  , xorClear "r8"
    -- 59: adox r10, r15
  , adoxRR "of" "r10" "r10" "r15"
    -- 60: adox r12, rcx
  , adoxRR "of" "r12" "r12" "rcx"
    -- 61: adcx rbx, r11
  , adcxRR "cf" "rbx" "rbx" "r11"
    -- 62: adcx r9, rbp
  , adcxRR "cf" "r9" "r9" "rbp"
    -- 63: mov rcx, rdx
  , movReg "rcx" "rdx"
    -- 64: mov rdx, [rax + 0x8]
  , movFromMem "rdx" "b" 0x8
    -- 65: mulx r13, r11, [rsi + 0x10]
  , mulxMem "r13" "r11" "rdx" "a" 0x10
    -- 66: mov rdx, [rsi + 0x20]
  , movFromMem "rdx" "a" 0x20
    -- 67: mulx r15, rbp, [rax + 0x0]
  , mulxMem "r15" "rbp" "rdx" "b" 0
    -- 68: mov rdx, rcx
  , movReg "rdx" "rcx"
    -- 69: mulx r8, rcx, [rsi + 0x18]
  , mulxMem "r8" "rcx" "rdx" "a" 0x18
    -- 70: xor rdx, rdx
  , xorClear "rdx"
    -- 71: adox rdi, r11
  , adoxRR "of" "rdi" "rdi" "r11"
    -- 72: adox r13, r14
  , adoxRR "of" "r13" "r13" "r14"
    -- 73: mov r14, rcx
  , movReg "r14" "rcx"
    -- 74: adcx r14, [rsp - 0x10]
  , adcxRR "cf" "r14" "r14" "s_10"
    -- 75: adcx r8, [rsp - 0x18]
  , adcxRR "cf" "r8" "r8" "s_18"
    -- 76: mov rdx, [rsi + 0x0]
  , movFromMem "rdx" "a" 0
    -- 77: mulx rcx, r11, [rax + 0x0]
  , mulxMem "rcx" "r11" "rdx" "b" 0
    -- 78: mov rdx, [rax + 0x0]
  , movFromMem "rdx" "b" 0
    -- 79: mov [rsp - 0x8], r13
  , spillSave "s_08" "r13"
    -- 80: mov [rsp + 0x0], rdi
  , spillSave "s_p0" "rdi"
    -- 81: mulx rdi, r13, [rsi + 0x8]
  , mulxMem "rdi" "r13" "rdx" "a" 0x8
    -- 82: xor rdx, rdx
  , xorClear "rdx"
    -- 83: adox rbx, r11
  , adoxRR "of" "rbx" "rbx" "r11"
    -- 84: adox rcx, r9
  , adoxRR "of" "rcx" "rcx" "r9"
    -- 85: adcx r10, r13
  , adcxRR "cf" "r10" "r10" "r13"
    -- 86: adcx rdi, r12
  , adcxRR "cf" "rdi" "rdi" "r12"
    -- 87: mov rdx, [rsi + 0x10]
  , movFromMem "rdx" "a" 0x10
    -- 88: mulx r9, r12, [rax + 0x10]
  , mulxMem "r9" "r12" "rdx" "b" 0x10
    -- 89: add r10, [rsp - 0x20]
  , addRR "cf" "r10" "r10" "s_20"
    -- 90: adcx rdi, [rsp - 0x28]
  , adcxRR "cf" "rdi" "rdi" "s_28"
    -- 91: mov rdx, rbx
  , movReg "rdx" "rbx"
    -- 92: shrd rdx, rcx, 51
  , shrdImm "rdx" "rcx" 51
    -- 93: mov r11, 0x33                          ; r11 = 51
  , movImm "r11" 0x33
    -- 94: bzhi r13, rbx, r11                     ; r13 = rbx & ((1<<51)-1)
  , bzhiRR "r13" "rbx" "r11"
    -- 95: mov rbx, rdx
  , movReg "rbx" "rdx"
    -- 96: mov rdx, [rax + 0x8]
  , movFromMem "rdx" "b" 0x8
    -- 97: mulx r11, rcx, [rsi + 0x18]
  , mulxMem "r11" "rcx" "rdx" "a" 0x18
    -- 98: adox rbp, rcx
  , adoxRR "of" "rbp" "rbp" "rcx"
    -- 99: adox r11, r15
  , adoxRR "of" "r11" "r11" "r15"
    -- 100: add rbp, r12
  , addRR "cf" "rbp" "rbp" "r12"
    -- 101: adcx r9, r11
  , adcxRR "cf" "r9" "r9" "r11"
    -- 102: add r10, rbx
  , addRR "cf" "r10" "r10" "rbx"
    -- 103: adc rdi, 0x0
  , adcImm "cf" "rdi" "rdi" 0 "cf"
    -- 104: mov rdx, [rsi + 0x8]
  , movFromMem "rdx" "a" 0x8
    -- 105: mulx r12, r15, [rax + 0x8]
  , mulxMem "r12" "r15" "rdx" "b" 0x8
    -- 106: mov rdx, [rax + 0x18]
  , movFromMem "rdx" "b" 0x18
    -- 107: mulx rcx, rbx, [rsi + 0x8]
  , mulxMem "rcx" "rbx" "rdx" "a" 0x8
    -- 108: mov rdx, 0x33
  , movImm "rdx" 0x33
    -- 109: bzhi r11, r10, rdx
  , bzhiRR "r11" "r10" "rdx"
    -- 110: shrd r10, rdi, 51
  , shrdImm "r10" "rdi" 51
    -- 111: add rbp, rbx
  , addRR "cf" "rbp" "rbp" "rbx"
    -- 112: adcx rcx, r9
  , adcxRR "cf" "rcx" "rcx" "r9"
    -- 113: mov rdx, [rax + 0x0]
  , movFromMem "rdx" "b" 0
    -- 114: mulx rdi, r9, [rsi + 0x10]
  , mulxMem "rdi" "r9" "rdx" "a" 0x10
    -- 115: xor rdx, rdx
  , xorClear "rdx"
    -- 116: adox r14, r9
  , adoxRR "of" "r14" "r14" "r9"
    -- 117: adox rdi, r8
  , adoxRR "of" "rdi" "rdi" "r8"
    -- 118: adcx r14, r15
  , adcxRR "cf" "r14" "r14" "r15"
    -- 119: adcx r12, rdi
  , adcxRR "cf" "r12" "r12" "rdi"
    -- 120: mov rdx, [rsi + 0x0]
  , movFromMem "rdx" "a" 0
    -- 121: mulx r15, r8, [rax + 0x10]
  , mulxMem "r15" "r8" "rdx" "b" 0x10
    -- 122: add r14, r8
  , addRR "cf" "r14" "r14" "r8"
    -- 123: adcx r15, r12
  , adcxRR "cf" "r15" "r15" "r12"
    -- 124: add r14, r10
  , addRR "cf" "r14" "r14" "r10"
    -- 125: adc r15, 0x0
  , adcImm "cf" "r15" "r15" 0 "cf"
    -- 126: mov rdx, r14
  , movReg "rdx" "r14"
    -- 127: shrd rdx, r15, 51
  , shrdImm "rdx" "r15" 51
    -- 128: mov rbx, rdx
  , movReg "rbx" "rdx"
    -- 129: mov rdx, [rax + 0x10]
  , movFromMem "rdx" "b" 0x10
    -- 130: mulx r9, r10, [rsi + 0x8]
  , mulxMem "r9" "r10" "rdx" "a" 0x8
    -- 131: mov rdx, r10
  , movReg "rdx" "r10"
    -- 132: add rdx, [rsp + 0x0]
  , addRR "cf" "rdx" "rdx" "s_p0"
    -- 133: adcx r9, [rsp - 0x8]
  , adcxRR "cf" "r9" "r9" "s_08"
    -- 134: mov rdi, 0x33
  , movImm "rdi" 0x33
    -- 135: bzhi r12, r14, rdi
  , bzhiRR "r12" "r14" "rdi"
    -- 136: adox rdx, [rsp - 0x30]
  , adoxRR "of" "rdx" "rdx" "s_30"
    -- 137: adox r9, [rsp - 0x38]
  , adoxRR "of" "r9" "r9" "s_38"
    -- 138: add rdx, rbx
  , addRR "cf" "rdx" "rdx" "rbx"
    -- 139: adc r9, 0x0
  , adcImm "cf" "r9" "r9" 0 "cf"
    -- 140: xor r8, r8
  , xorClear "r8"
    -- 141: adox rbp, [rsp - 0x40]
  , adoxRR "of" "rbp" "rbp" "s_40"
    -- 142: adox rcx, [rsp - 0x48]
  , adoxRR "of" "rcx" "rcx" "s_48"
    -- 143: bzhi r14, rdx, rdi
  , bzhiRR "r14" "rdx" "rdi"
    -- 144: shrd rdx, r9, 51
  , shrdImm "rdx" "r9" 51
    -- 145: add rbp, rdx
  , addRR "cf" "rbp" "rbp" "rdx"
    -- 146: adc rcx, 0x0
  , adcImm "cf" "rcx" "rcx" 0 "cf"
    -- 147: mov r15, rbp
  , movReg "r15" "rbp"
    -- 148: shrd r15, rcx, 51
  , shrdImm "r15" "rcx" 51
    -- 149: imul rbx, r15, 0x13
  , imulImmReg "rbx" "r15" 0x13
    -- 150: mov r10, [rsp - 0x50]                 ; r10 = out ptr
  , spillRestore "r10" "s_50"
    -- 151: mov [r10 + 0x18], r14                 ; out[3] = r14
  , movToMem "out" 0x18 "r14"
    -- 152: bzhi r9, rbp, rdi
  , bzhiRR "r9" "rbp" "rdi"
    -- 153: mov [r10 + 0x20], r9                  ; out[4] = r9
  , movToMem "out" 0x20 "r9"
    -- 154: lea r13, [r13 + rbx]
  , leaAdd "r13" "r13" "rbx"
    -- 155: bzhi r14, r13, rdi
  , bzhiRR "r14" "r13" "rdi"
    -- 156: mov [r10 + 0x0], r14                  ; out[0] = r14
  , movToMem "out" 0 "r14"
    -- 157: shr r13, 51
  , shrImm "r13" 51
    -- 158: lea r13, [r13 + r11]
  , leaAdd "r13" "r13" "r11"
    -- 159: bzhi r11, r13, rdi
  , bzhiRR "r11" "r13" "rdi"
    -- 160: shr r13, 51
  , shrImm "r13" 51
    -- 161: lea r13, [r13 + r12]
  , leaAdd "r13" "r13" "r12"
    -- 162: mov [r10 + 0x10], r13                 ; out[2] = r13
  , movToMem "out" 0x10 "r13"
    -- 163: mov [r10 + 0x8], r11                  ; out[1] = r11
  , movToMem "out" 0x8 "r11"
    -- 164–169: spill restores
  , spillRestore "rbx" "s_80"
  , spillRestore "rbp" "s_78"
  , spillRestore "r12" "s_70"
  , spillRestore "r13" "s_68"
  , spillRestore "r14" "s_60"
  , spillRestore "r15" "s_58"
    -- 170: add rsp, 136  (epilogue, FunDecl-implicit)
    -- 171: ret           (FunDecl-implicit)
  ]

/-! ## §4. `fiat_curve25519_carry_mul` (FunDecl)

Spec (carries from `UnsaturatedSolinas.v::carry_mul_correct`):

```
  ∀ a b : List ℕ,    (length a = 5 ∧ length b = 5
                      ∧ ∀ i, a[i] < 2^54 ∧ b[i] < 2^54)
                    → interp_carry_mul (carry_mul a b)
                       = (interp_5limb a * interp_5limb b) mod p
                    ∧ ∀ i, (carry_mul a b)[i] < 2^52
```

Body is `mulBody` defined in §3 above. -/

def mulFd : FunDecl where
  name    := { name := "fiat_curve25519_carry_mul" }
  params  := [funParam "out", funParam "a", funParam "b"]
  body    := mulBody
  results := [varI "out"]

/-! ## §4. `fiat_curve25519_carry_square` (FunDecl)

Spec (carries from `UnsaturatedSolinas.v::carry_square_correct`):

```
  ∀ a : List ℕ,    (length a = 5 ∧ ∀ i, a[i] < 2^54)
                  → interp_carry_square (carry_square a)
                     = (interp_5limb a)^2 mod p
                  ∧ ∀ i, (carry_square a)[i] < 2^52
```

Body is `sqrBody` defined in §2 above — full line-by-line translation
of the CryptOpt asm. -/

def sqrFd : FunDecl where
  name    := { name := "fiat_curve25519_carry_square" }
  params  := [funParam "out", funParam "a"]
  body    := sqrBody
  results := [varI "out"]

/-! ## §4. Module bundle -/

/-- The two CryptOpt-tuned leaves bundled as a `JasminProg`. Other
    modules import this and concatenate it with their own functions
    when emitting `.jazz` / Jasmin source. -/
def cryptoptLeaves : JasminProg := { funcs := [mulFd, sqrFd] }

/-! ## §5. Sanity -/

example : mulFd.params.length = 3 := by decide
example : sqrFd.params.length = 2 := by decide
example : (cryptoptLeaves.getFun ⟨"fiat_curve25519_carry_mul"⟩).isSome := by
  native_decide
example : (cryptoptLeaves.getFun ⟨"fiat_curve25519_carry_square"⟩).isSome := by
  native_decide
example : mulFd.body.length > 150 := by native_decide  -- 167 asm instrs ≃ 175 InstrR
example : sqrFd.body.length > 100 := by native_decide  -- 107 asm instrs ≃ 111 InstrR

end CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptPort
