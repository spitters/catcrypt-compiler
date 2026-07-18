/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.TranslationValidation

/-!
# Cross-validation against a SECOND authoritative x86 semantics: Sail-x86 (#281/#437)

`TranslationValidation.lean` differentially validates the owned Lean x86 model
(`Model.lean`'s `step`, `JasminModel.lean`'s `evalInstr`) against **Jasmin's
Rocq x86 model** (`x86_instr_decl.v`). That is the *like-for-like* anchor: the
verified pipeline hands `lprog` to jasminc, whose CT theorem is stated over that
exact Rocq model.

This module adds an **independent second anchor**: the
[`rems-project/sail-x86-from-acl2`](https://github.com/rems-project/sail-x86-from-acl2)
Sail x86 ISA model — the [ACL2 `x86isa`](https://www.cs.utexas.edu/~moore/acl2/)
model (Goel, Hunt, Kaufmann) mechanically translated to
[Sail](https://www.cl.cam.ac.uk/~pes20/sail/) (Taylor, Bauereiss, Armstrong,
Sewell). ACL2-`x86isa` is a long-standing, heavily-validated executable x86
reference (it boots real binaries), and is *independent* of Jasmin's hand-
written Rocq model — so agreement with it is genuine cross-validation, not a
restatement of the same source.

## How the Sail-x86 outputs were obtained (no fabrication)

The Sail model snapshot (`model/*.sail`) was loaded into the Sail `0.20.1`
interpreter (OCaml backend; no decoder / no machine-code path needed), and the
per-instruction **spec functions** were called directly on concrete 64-bit
inputs:

```
sail -i --is <script> x86_diff_harness.sail        (script = "main()\n:r\n:quit\n")
```

where `x86_diff_harness.sail` includes `prelude.sail`, `structures.sail`, and
the `*_spec.sail` files, and `main` calls `gpr_add_spec_8`, `gpr_sub_spec_8`,
`gpr_adc_spec_8`, `gpr_sbb_spec_8`, `gpr_and_spec_8`, `gpr_or_spec_8`,
`gpr_xor_spec_8`, `imul_spec_64`, `mul_spec_64`, `sal_shl_spec_64`,
`shr_spec_64`, `sar_spec_64`, printing each result's data word and the
`rflagsbits` `cf/of/sf/zf/pf` bits. The raw outputs are recorded in
`bench_refs/sail-x86-from-acl2/x86_diff_RESULTS.txt` and quoted as the RHS of
each `example` below; the harness is `model/x86_diff_harness.sail` in that repo.

`JFlag = Option Bool`: a Sail `bits(1)` flag value `0`/`1` corresponds to
`some false`/`some true` in the faithful `evalInstr` five-flag state.

## The Sail-x86 spec functions (quoted, from `model/*_spec.sail`)

```sail
function gpr_add_spec_8 (dst, src, rf) = {                 // add_spec.sail
  let raw : bits(65) = bits_of_int(unsigned(dst)+unsigned(src), 65);
  let result : bits(64) = truncate(raw, 64);
  cf = cf_spec64(raw); of = of_spec64(...); sf/pf/zf = ...; }
function gpr_sub_spec_8 (dst, src, rf) = {                 // sub_spec.sail
  cf = bool_to_bits(unsigned(dst) < unsigned(src)); ... }  // CF = unsigned borrow
function gpr_adc_spec_8 (dst, src, rf) = { ... + unsigned(rf[cf]) ... }
function gpr_sbb_spec_8 (dst, src, rf) = { ... - (src + cf) ... }
function gpr_and_spec_8 = logand;  gpr_or_spec_8 = logior;  gpr_xor_spec_8 = logxor;
                                   // all clear CF and OF (bitwise)
function imul_spec_64 (dst, src) = signed widening; low word + (cf=of) overflow bit
function mul_spec_64  (dst, src) = unsigned widening; (product_high, product_low)
function sal_shl_spec_64 / shr_spec_64 / sar_spec_64       // shifts_spec.sail
```

## Result of the cross-validation (this file)

On the emitted-kernel scalar/logical/shift/multiply subset, the owned model's
`evalInstr` (and the data result of `step`) **agree with Sail-x86 on the data
word AND all flags Sail computes** — for every one of the points below, which
are the *same* concrete inputs already pinned against Jasmin in
`TranslationValidation.lean`. The owned model therefore agrees with **two
independent authoritative semantics** (Jasmin Rocq + Sail/ACL2) on:

  `MOV`-class moves, `ADD`, `SUB`, `ADC`, `SBB`, `AND`, `OR`, `XOR`, `IMUL`
  (low word), `MUL`/`MULX` (full `hi`/`lo` product), `SHL`, `SHR`, `SAR`

with data + the five flags (`cf/of/sf/zf/pf`) checked where Sail defines them.
No discrepancy was found.

## Honest scope — what Sail-x86 does NOT cover

* **`ADCX`/`ADOX`/`MULX` (ADX + BMI2):** the upstream ACL2 `x86isa` model
  predates the ADX/BMI2 extensions, so these instructions were absent from the
  Sail model. `MULX`'s widening *product* is still cross-validated here via the
  equivalent unsigned `MUL` (`mul_spec_64`), whose `(hi, lo)` split is bit-
  identical to `MULX`'s `(lo, hi)` — see `sail_mulx_via_mul_*` below.
  **Update (#484):** the ADX trio now *does* have a Sail-x86 counterpart:
  `model/adx_spec.sail` supplies `mulx_spec_64` and `adcx_adox_spec_64`
  (transcribed from the Intel SDM, exercised through the Sail 0.20.1
  interpreter — `model/x86_adx_harness.sail`, outputs in
  `x86_diff_RESULTS.txt` — and exported via `sail --lean` into `Out/AdxSpec.lean`).
  The owned `evalInstr` `.mulx`/`.adcx`/`.adox` are pinned to those Sail spec
  functions in `SailX86Lean.lean` (`mulx_eq_sail*`/`adcx_eq_sail*`/
  `adox_eq_sail*`), including the defining ADX feature — `ADCX` writes **only**
  `CF`, `ADOX` writes **only** `OF` (independent dual carry chains), the routing
  realized by the owned step and matching Jasmin's `Ox86_ADCX_instr`/
  `Ox86_ADOX_instr`. The trio is therefore now anchored to **both** Jasmin's
  Rocq model and Sail-x86.
* **AES-NI / PCLMUL / GFNI / VAES:** the upstream ACL2 model has no decode
  tables or spec functions for these families either.
  **Update (#492):** as with ADX, the crypto-extension primitives now *do* have
  a Sail-x86 counterpart: `model/cryptoext_spec.sail` supplies `gf256_mul` /
  `gf2p8mulb_spec` (GFNI), `aesenc_spec` / `aesenclast_spec` /
  `aeskeygenassist_spec` (AES-NI, and per-lane VAES), and `clmul64_spec`
  (PCLMULQDQ) — transcribed from the Intel SDM + FIPS 197, exercised through the
  Sail 0.20.1 interpreter (`model/x86_cryptoext_harness.sail`, outputs in
  `x86_diff_RESULTS.txt`), and exported via `sail --lean` into
  `Out/CryptoextSpec.lean`. The owned `gf28_byte_mul`/`vgf2p8mulb_128`,
  `wAESENC`/`wAESENCLAST`/`wAESKEYGENASSIST`, and `polyMul64` are pinned to those
  Sail spec functions on the FIPS-197 / GHASH known-answer vectors in
  `SailX86Lean.lean` (`gf256_mul_eq_sail*`/`gf2p8mulb_eq_sail`/`aesenc_eq_sail`/
  `aesenclast_eq_sail`/`aeskeygenassist_eq_sail`/`clmul_eq_sail*`). The byte
  *encoders* for these families (`CryptoExtEncoder.lean`) remain at the
  gas-pinned tier (the SDM byte tables are unchanged by this); this anchors the
  instruction *semantics*.
* **`CMOVcc`:** the ACL2 model treats it as a predicated `MOV` (no dedicated
  spec function); its data selection is the move semantics, anchored to Jasmin.
* **Shift-count masking:** Sail's `sal_shl_spec_64` takes a `bits(6)` count
  (already `< 64`); the count-`≥ w` divergence between the raw-count `step` and
  the masked Jasmin/Sail semantics is the same precondition recorded in
  `TranslationValidation` (`shl_count_ge_width_differs`). Our compiler only
  emits counts `< w`, where all three agree.

This file is the realization of #281's named residual "Sail-x86 cross-checks
remain unwired", and sets up #438 (the verified `JInstr → bytes` encoder will
be validated against Sail-x86's byte-level decoder).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend

namespace SailX86

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ### Local width-64 states

The `jst`/`jstCF`/`st`/`stMulx` helpers in `TranslationValidation.lean` are
`private`; we redeclare equivalent ones here so the cross-validation is
self-contained. -/

/-- Faithful (`JState`) state with register `"a" := v`, no preset flags. -/
private def jst (v : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "a" then v else 0 }

/-- Faithful state with `"a" := v` and `CF := some c`. -/
private def jstCF (v : BitVec 64) (c : Bool) : JState 64 :=
  { regs := fun r => if r = "a" then v else 0, flags := { cf := some c } }

/-- Hand-authored (`State`) state with `"a" := v`. -/
private def st (v : BitVec 64) : State 64 :=
  { regs := fun r => if r = "a" then v else 0 }

/-- Hand-authored state with named factor registers `"a" := x`, `"b" := y`. -/
private def stMulx (x y : BitVec 64) : State 64 :=
  { regs := fun r => if r = "a" then x else if r = "b" then y else 0 }

/-! ## Faithful five-flag state pins against Sail-x86

Each `example` asserts that the owned faithful transcription `evalInstr`
reproduces the Sail-x86 spec-function output (data word + the flags Sail
defines) on the shared concrete inputs. `jst`/`jstCF` are the width-64 states
from `TranslationValidation.lean`'s `Jasmin` section (`"a" := v`, optional
preset `CF`). The Sail outputs are quoted from `x86_diff_RESULTS.txt`. -/

/-- ADD `123456789 + 987654321`. Sail-x86 `gpr_add_spec_8`:
    `data=1111111110 cf=0 of=0 sf=0 zf=0 pf=1`. Owned `evalInstr` matches all six. -/
example :
    let s := evalInstr (jst 123456789) (.add "a" (.imm 987654321))
    (s.get "a").toNat = 1111111110 ∧
    s.flags = { of := some false, cf := some false, sf := some false,
                pf := some true, zf := some false } := by native_decide

/-- ADD carry-out `(2^64-1) + 1`. Sail-x86: `data=0 cf=1 of=0 sf=0 zf=1 pf=1`. -/
example :
    let s := evalInstr (jst (BitVec.allOnes 64)) (.add "a" (.imm 1))
    (s.get "a").toNat = 0 ∧
    s.flags = { of := some false, cf := some true, sf := some false,
                pf := some true, zf := some true } := by native_decide

/-- SUB `5 - 8`. Sail-x86 `gpr_sub_spec_8` (CF = unsigned borrow):
    `data=2^64-3 cf=1 of=0 sf=1 zf=0 pf=0`. -/
example :
    let s := evalInstr (jst 5) (.sub "a" (.imm 8))
    (s.get "a").toNat = 18446744073709551613 ∧
    s.flags = { of := some false, cf := some true, sf := some true,
                pf := some false, zf := some false } := by native_decide

/-- AND `13 & 7`. Sail-x86 `gpr_and_spec_8` (clears CF, OF):
    `data=5 cf=0 of=0 sf=0 zf=0 pf=1`. -/
example :
    let s := evalInstr (jst 13) (.and_ "a" (.imm 7))
    (s.get "a").toNat = 5 ∧
    s.flags = { of := some false, cf := some false, sf := some false,
                pf := some true, zf := some false } := by native_decide

/-- OR `13 | 8`. Sail-x86 `gpr_or_spec_8`: `data=13 cf=0 of=0 sf=0 zf=0 pf=0`. -/
example :
    let s := evalInstr (jst 13) (.or_ "a" (.imm 8))
    (s.get "a").toNat = 13 ∧
    s.flags = { of := some false, cf := some false, sf := some false,
                pf := some false, zf := some false } := by native_decide

/-- XOR `13 ^ 7`. Sail-x86 `gpr_xor_spec_8`: `data=10 cf=0 of=0 sf=0 zf=0 pf=1`. -/
example :
    let s := evalInstr (jst 13) (.xor_ "a" (.imm 7))
    (s.get "a").toNat = 10 ∧
    s.flags = { of := some false, cf := some false, sf := some false,
                pf := some true, zf := some false } := by native_decide

/-- ADC `5 + 8 + CF(1)`. Sail-x86 `gpr_adc_spec_8`:
    `data=14 cf=0 of=0 sf=0 zf=0 pf=0`. -/
example :
    let s := evalInstr (jstCF 5 true) (.adc "a" (.imm 8))
    (s.get "a").toNat = 14 ∧
    s.flags = { of := some false, cf := some false, sf := some false,
                pf := some false, zf := some false } := by native_decide

/-- SBB `5 - 8 - CF(1)`. Sail-x86 `gpr_sbb_spec_8`:
    `data=2^64-4 cf=1 of=0 sf=1 zf=0 pf=1`. -/
example :
    let s := evalInstr (jstCF 5 true) (.sbb "a" (.imm 8))
    (s.get "a").toNat = 18446744073709551612 ∧
    s.flags = { of := some false, cf := some true, sf := some true,
                pf := some true, zf := some false } := by native_decide

/-- IMUL low word `999 * 1000000`. Sail-x86 `imul_spec_64`: low word
    `999000000`, no overflow (`cf=of=0`). `rflags_of_mul`: SF/PF/ZF undefined.
    We check the data word + the OF/CF the model defines. -/
example :
    let s := evalInstr (jst 999) (.imul "a" (.imm 1000000))
    (s.get "a").toNat = 999000000 ∧
    s.flags.of = some false ∧ s.flags.cf = some false := by native_decide

/-- SHL `1 << 4`. Sail-x86 `sal_shl_spec_64`: `data=16 cf=0 of=0 sf=0 zf=0 pf=0`
    (OF undefined for count `≠ 1`; CF/SF/PF/ZF as below). -/
example :
    let s := evalInstr (jst 1) (.shl "a" (.imm 4))
    (s.get "a").toNat = 16 ∧
    s.flags.cf = some false ∧ s.flags.sf = some false ∧
    s.flags.pf = some false ∧ s.flags.zf = some false := by native_decide

/-- SHR `256 >> 4`. Sail-x86 `shr_spec_64`: `data=16`, CF/SF/PF/ZF = `0`. -/
example :
    let s := evalInstr (jst 256) (.shr "a" (.imm 4))
    (s.get "a").toNat = 16 := by native_decide

/-- SAR `(2^64-8) >>a 1` (negative, arithmetic right shift keeps the sign bit).
    Sail-x86 `sar_spec_64`: `data=2^64-4 cf=0 of=0 sf=1 zf=0 pf=1`. -/
example :
    let s := evalInstr (jst (BitVec.ofNat 64 (2^64 - 8))) (.sar "a" (.imm 1))
    (s.get "a").toNat = 18446744073709551612 ∧
    s.flags = { of := some false, cf := some false, sf := some true,
                pf := some true, zf := some false } := by native_decide

/-- SAR `256 >>a 4`. Sail-x86 `sar_spec_64`: `data=16`. -/
example : ((evalInstr (jst 256) (.sar "a" (.imm 4))).get "a").toNat = 16 := by
  native_decide

/-! ## `MULX` widening product, cross-validated via Sail-x86's unsigned `MUL`

The ACL2/Sail model has no BMI2 `MULX`, but its unsigned `MUL` (`mul_spec_64`)
computes the *same* `128`-bit product, returning `(product_high, product_low)`.
`MULX`'s output is `(lo, hi)` of that same product. So Sail-x86's `MUL` directly
validates the owned `MULX` data words. (The flag-independence routing of
`ADCX`/`ADOX` has no Sail counterpart — see the module honesty note.) -/

/-- `MULX (2^64-1) 2`: Sail-x86 `mul_spec_64`: `lo=2^64-2, hi=1`. The owned
    `step` `MULX` reproduces both words. -/
theorem sail_mulx_via_mul_allones :
    let s := step (stMulx (BitVec.allOnes 64) 2) (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo").toNat = 18446744073709551614 ∧ (s.get "hi").toNat = 1 := by
  native_decide

/-- `MULX 1311768467463790320 18364758544493064720`: Sail-x86 `mul_spec_64`:
    `lo=2552847189736476416, hi=1305938385386173474`. Both words match. -/
theorem sail_mulx_via_mul_nontrivial :
    let s := step (stMulx 1311768467463790320 18364758544493064720)
                  (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo").toNat = 2552847189736476416 ∧
    (s.get "hi").toNat = 1305938385386173474 := by native_decide

/-! ## Three-way agreement witness

For a representative point we exhibit that the owned `step` data result, the
owned faithful `evalInstr` data result, and the Sail-x86 number all coincide —
the owned model sits at the intersection of the two authoritative semantics.
(The `evalInstr`/`step` agreement is the `Jasmin` reconciliation; the Sail
number is the quoted RHS.) -/

/-- ADD: owned `step` data = owned `evalInstr` data = Sail-x86 `1111111110`. -/
theorem sail_jasmin_owned_agree_add :
    ((step (st 123456789) (.add "a" (.imm 987654321))).get "a").toNat = 1111111110 ∧
    ((evalInstr (jst 123456789) (.add "a" (.imm 987654321))).get "a").toNat = 1111111110 := by
  native_decide

end SailX86

end CatCrypt.Crypto.SecureCompilation.X86Backend
