/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Preservation
import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
import Std.Tactic.BVDecide

/-!
# Translation validation against Jasmin's Rocq x86 model (#281)

This module records the **correspondence** between our native-Lean x86 `step`
semantics (`Model.lean`) and Jasmin's authoritative Rocq x86 instruction
semantics, and pins our model's effect with machine-checked Lean `#guard`s.

## Why Jasmin's Rocq model is the anchor

The verified pipeline currently hands `lprog` to **jasminc**, the Coq-verified
Jasmin compiler, whose constant-time-preservation theorem
(`jasminc_preserves_ct`, arXiv:2511.11292) is stated over the x86 semantics in
`jasmin/proofs/compiler/x86_instr_decl.v` (the `x86_ADD`/`x86_ADC`/… semantic
functions) composed by `eval_op`/`eval_instr` in `arch/arch_sem.v`. Replacing
that backend like-for-like means our `step` must agree with *that* model — so
matching it **is** translation validation against the exact trust anchor the
existing story depends on. CT-CompCert / K-x86 / Sail-x86 are independent
cross-checks still to be added (see "Not yet wired" below).

## How the correspondence was validated (differential, via `rocq-mcp`)

Each `x86_*` value below was obtained by evaluating Jasmin's *compiled* Rocq
model (`x86_instr_decl.vo`) on concrete 64-bit inputs through `rocq-mcp`,
using the data-word projection of the result tuple

```coq
Definition dw {sz} (t : sem_ltuple (b5w_ty sz)) : Z :=
  word.wunsigned (snd (snd (snd (snd (snd t))))).   (* OF,CF,SF,PF,ZF,word *)
Definition cf {sz} (t : sem_ltuple (b5w_ty sz)) : option bool := fst (snd t).
```

and the same inputs were run through our Lean `step`. The Jasmin outputs are
quoted as comments; the Lean `#guard`s below assert our model reproduces them.
Each `#guard` checks a numeric output of `step` against the Jasmin value.

| instr | inputs (U64) | Jasmin `x86_*` data | our `step` | flag checked |
|---|---|---|---|---|
| `MOV`  | `4242`              | `4242`                  | ✓ | — |
| `ADD`  | `123456789,987654321` | `1111111110`          | ✓ | CF (carry-out) ✓ |
| `SUB`  | `5,8`               | `2^64-3`                | ✓ | — |
| `AND`  | `13,7`              | `5`                     | ✓ | — |
| `OR`   | `13,8`              | `13`                    | ✓ | — |
| `XOR`  | `13,7`              | `10`                    | ✓ | — |
| `IMULt`| `999,1000000`       | `999000000`             | ✓ | — |
| `SHL`  | `1` by `4`          | `16`                    | ✓ | — |
| `SHR`  | `256` by `4`        | `16`                    | ✓ | — |
| `ADC`  | `5,8,CF=1`          | `14`                    | ✓ | CF (carry-out) ✓ |
| `SBB`  | `5,8,CF=1`          | `2^64-4`                | ✓ | CF (borrow) `Some true` ✓ |
| `CMOV` | `b,111,222`         | `b ? 111 : 222`         | ✓ | — |
| `MULX` | `(2^64-1),2`        | `lo=2^64-2, hi=1`       | ✓ | none (MULX sets no flag) |
| `MULX` | `0x123…f0, 0xfed…10`| `lo=2552847189736476416, hi=1305938385386173474` | ✓ | none |
| `ADCX` | `(2^64-1),1,CF=1`   | `data=1, CF=Some true`  | ✓ | CF only ✓ |
| `ADCX` | `5,8,CF=1`          | `data=14, CF=Some false`| ✓ | CF only ✓ |
| `ADOX` | `(2^64-1),1,OF=1`   | `data=1, OF=Some true`  | ✓ | OF only ✓ |
| `MULX→ADCX→ADOX` | bignum step (below) | `lo=2^64-3,hi=2; r=7,CF; r=107,OF` | ✓ | CF then OF ✓ |
| `NOT`  | `0` / `13` / `2^64-1` | `2^64-1` / `2^64-14` / `0`   | ✓ | none (NOT sets no flag) |
| `NEG`  | `0` / `5` / `1`     | `0,CF=0` / `2^64-5,CF=1` / `2^64-1,CF=1` | ✓ | CF (= `w≠0`) ✓ |
| `CMOVE`  | `b=ZF,111,222`    | `b ? 111 : 222`         | ✓ | none (CMOVcc sets no flag) |
| `CMOVNE` | `b=¬ZF,111,222`   | `b ? 111 : 222`         | ✓ | none |
| `CMOVB`  | `b=CF,111,222`    | `b ? 111 : 222`         | ✓ | none |
| `MOV`-mem (`loadMem`/`storeMem`) | `123456789` | `123456789` (identity) | ✓ | none |
| `MULX`-mem (`mulxMem`) | `(2^64-1),[3]` / `0x123…,[0xfed…]` | `(lo,hi)=(2^64-3,2)` / `(2552…,1305…)` | ✓ | none |

## Validated vs. asserted-by-inspection vs. not wired

* **Differentially validated** (numeric match against Jasmin's Rocq `x86_*`,
  data and — for ADD/ADC/SBB/ADCX/ADOX — the carry flag): `MOV`, `ADD`, `SUB`,
  `AND`, `OR`, `XOR`, `IMULt` (low word), `SHL`, `SHR`, `ADC`, `SBB`, `CMOV`,
  and the ADX/BMI2 trio `MULX` (both `hi` and `lo` words), `ADCX` (data + CF),
  `ADOX` (data + OF), plus one composed `MULX → ADCX → ADOX` bignum step, and
  the easy-tier unary arms `NOT` (= `wnot`, no flag) and `NEG` (data `(-w)%w` +
  `CF = w≠0`), and the remaining emitted-kernel arms `CMOVE`/`CMOVNE`/`CMOVB`
  (`x86_CMOVcc`, selecting on `ZF`/`¬ZF`/`CF`, no flag written), `loadMem`/
  `storeMem` (`x86_MOV` = identity composed with `mem_read`/`mem_write`, no
  flag), and `mulxMem` (`x86_MULX_lo_hi` with the second factor read from
  memory, no flag) — the `#guard`s in this file plus the quoted `rocq-mcp`
  outputs. This covers the full `JInstr`-emitted instruction set of the owned
  backend's scalar/ADX kernels.
* **Asserted by inspection only** (the *general* word-level equation matching
  `wrepr`/`wand`/`wshl` over all inputs, beyond the sampled points): the
  preservation theorems in `Preservation.lean` carry the all-inputs proof for
  the `lprog` opcodes; for `ADC`/`SBB` the all-inputs equality to
  `add_carry`/`sub_borrow = wrepr (x±y±c)` is argued by reading the Rocq
  definitions (quoted below), not yet a ported all-inputs Lean theorem against
  a Lean model of `wrepr`.
* **Shift-count precondition (not papered over):** Jasmin `x86_SHL/SHR/SAR`
  mask the count by `& 63` (`U64`) before shifting; our `step` shifts by the
  raw `(src.eval).toNat`. They agree **iff count `< w`** — the only case our
  compiler emits. Counterexample at count `68`: Jasmin `SHL 1 68 = 16`, our
  model `1 <<< 68 = 0` (recorded in `shl_count_ge_width_differs`).
* **Sail-x86 / ACL2 cross-check (now wired, #437):** the owned model is also
  differentially validated against the *second, independent* authoritative
  semantics `rems-project/sail-x86-from-acl2` (the ACL2 `x86isa` model in Sail)
  in `SailX86Validation.lean`. The ADX/BMI2 trio is absent from that model and
  remains anchored only here, against Jasmin.
* **Not yet wired:** the SIMD/AVX subset, control flow, the byte encoder, the
  whole-block simulation against jasmin `lsem`, and the CT-CompCert / K-x86
  independent cross-checks.

## Quoted Jasmin Rocq definitions (x86_instr_decl.v)

```coq
Definition x86_MOV sz (x: word sz) : word sz := x.
Definition x86_ADD sz (v1 v2 : word sz) : tpl (b5w_ty sz) :=
  rflags_of_aluop_w (v1 + v2)%w
    (wunsigned v1 + wunsigned v2)%Z (wsigned v1 + wsigned v2)%Z.
Definition x86_SUB sz (v1 v2 : word sz) : tpl (b5w_ty sz) :=
  rflags_of_aluop_w (v1 - v2)%w ...
Definition add_carry sz (x y c: Z) : word sz := wrepr sz (x + y + c).
Definition x86_ADC sz (v1 v2 : word sz) (c: bool) : tpl (b5w_ty sz) :=
  let c := Z.b2z c in
  rflags_of_aluop_w (add_carry sz (wunsigned v1) (wunsigned v2) c) ...
Definition sub_borrow sz (x y c: Z) : word sz := wrepr sz (x - y - c).
Definition x86_SBB sz (v1 v2 : word sz) (c:bool) : tpl (b5w_ty sz) :=
  let c := Z.b2z c in
  rflags_of_aluop_w (sub_borrow sz (wunsigned v1) (wunsigned v2) c) ...
Definition x86_IMULt sz (v1 v2: word sz) : tpl (b5w_ty sz) :=
  let lo := (v1 * v2)%w in ... flags_w (rflags_of_mul ov) lo.   (* IMULr / IMULri form *)
Definition x86_AND sz (v1 v2: word sz) := rflags_of_bwop_w (wand v1 v2).
Definition x86_SHL sz (v: word sz) (i: u8) : tpl (b5w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in    (* & 63 at U64 *)
  if i == 0%w then rflags_None_w v else ... wshl v (wunsigned i).
Definition x86_CMOVcc sz (b:bool) (w2 w3: word sz) : tpl (w_ty sz) :=
  if b then w2 else w3.

(* ADX / BMI2 trio (x86_instr_decl.v + word.v) *)
Definition waddcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x + wunsigned y + Z.b2z c in
  (wbase sz <=? n, wrepr sz n).            (* (carry-out, low word) *)
Definition x86_ADCX sz (v1 v2: word sz) (c:bool) : tpl (bw_ty sz) :=
  let (c,w) := waddcarry v1 v2 c in (Some c, w).
Definition Ox86_ADCX_instr := mk_instr_w2b_bw "ADCX" x86_ADCX CF ...   (* flag = CF *)
Definition Ox86_ADOX_instr := mk_instr_w2b_bw "ADOX" x86_ADCX OF ...   (* flag = OF *)
(* mk_instr_w2b_bw ... flag ...  has input  [Ea 0; Eu 1; F flag]      *)
(*                                and output [F flag; Ea 0]            *)
(*   => ADCX reads/writes ONLY CF; ADOX reads/writes ONLY OF.         *)
Definition wumul sz (x y: word sz) :=
  let n := wunsigned x * wunsigned y in
  (high_bits sz n, wrepr sz n).            (* (hi, lo) *)
Definition x86_MULX_lo_hi sz (v1 v2: word sz) : tpl (w2_ty sz sz) :=
  let: (hi, lo) := wumul v1 v2 in (lo, hi).   (* result tuple is (lo, hi); no flag *)
```

The carry flag Jasmin records (`rflags_of_aluop`'s CF = `wunsigned w != vu`,
the word differing from the unbounded sum/difference) is exactly our
`addCarry`/`subBorrow` predicate (the result wrapped). For the ADX trio:
`waddcarry`'s `wbase <=? n` carry-out is exactly our `addCarry`, `wumul`'s
`high_bits sz n = wrepr sz (n >> w)` is our `mulHi` (`(a*b) / 2^w` truncated to
`w` bits), and the `Ox86_ADCX_instr`/`Ox86_ADOX_instr` flag argument (`CF`
resp. `OF`, appearing in both the input and output operand lists and nowhere
else) is the **only** flag each touches — the two-independent-carry-chain
property our `setCF`/`setOF` reproduce.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## Differential-validation pins

A fresh 64-bit state with two named registers, mirroring the `rocq-mcp`
`Compute` inputs. Each pin asserts the data result of our `step` equals
the numeric value Jasmin's `x86_*` produced (quoted in the table above). -/

/-- `dst := v` register state at width 64. -/
private def st (v : BitVec 64) : State 64 :=
  { regs := fun r => if r = "a" then v else 0 }

/-- `dst := v` with the carry flag preset (for ADC/SBB). -/
private def stCF (v : BitVec 64) (c : Bool) : State 64 :=
  { regs := fun r => if r = "a" then v else 0, flags := { cf := c } }

-- MOV: Jasmin `x86_MOV 4242 = 4242`.
#guard ((step (st 0) (.mov "a" (.imm 4242))).get "a").toNat == 4242

-- ADD: Jasmin `dw (x86_ADD 123456789 987654321) = 1111111110`.
#guard ((step (st 123456789) (.add "a" (.imm 987654321))).get "a").toNat
    == 1111111110

-- ADD carry-out: Jasmin `cf (x86_ADD (2^64-1) 1) = Some true`; our CF flips.
#guard (step (st (BitVec.allOnes 64)) (.add "a" (.imm 1))).flags.cf

-- SUB: Jasmin `dw (x86_SUB 5 8) = 2^64-3 = 18446744073709551613`.
#guard ((step (st 5) (.sub "a" (.imm 8))).get "a").toNat
    == 18446744073709551613

-- AND: Jasmin `dw (x86_AND 13 7) = 5`.
#guard ((step (st 13) (.and_ "a" (.imm 7))).get "a").toNat == 5

-- OR: Jasmin `dw (x86_OR 13 8) = 13`.
#guard ((step (st 13) (.or_ "a" (.imm 8))).get "a").toNat == 13

-- XOR: Jasmin `dw (x86_XOR 13 7) = 10`.
#guard ((step (st 13) (.xor_ "a" (.imm 7))).get "a").toNat == 10

-- IMUL (low word): Jasmin `dw (x86_IMULt 999 1000000) = 999000000`.
#guard ((step (st 999) (.mul "a" (.imm 1000000))).get "a").toNat
    == 999000000

-- SHL by 4: Jasmin `dw (x86_SHL 1 4) = 16`.
#guard ((step (st 1) (.shl "a" (.imm 4))).get "a").toNat == 16

-- SHR by 4: Jasmin `dw (x86_SHR 256 4) = 16`.
#guard ((step (st 256) (.shr "a" (.imm 4))).get "a").toNat == 16

-- ADC with CF=1: Jasmin `dw (x86_ADC 5 8 true) = 14`.
#guard ((step (stCF 5 true) (.adc "a" (.imm 8))).get "a").toNat == 14

-- SBB with CF=1: Jasmin `dw (x86_SBB 5 8 true) = 2^64-4 = 18446744073709551612`,
-- `cf = Some true`. Data and borrow flag both checked.
#guard ((step (stCF 5 true) (.sbb "a" (.imm 8))).get "a").toNat
    == 18446744073709551612

#guard (step (stCF 5 true) (.sbb "a" (.imm 8))).flags.cf

-- CMOV taken / not taken: Jasmin `x86_CMOVcc true 111 222 = 111`,
-- `x86_CMOVcc false 111 222 = 222`.
#guard
    ((step { regs := fun r => if r = "a" then (222 : BitVec 64) else 0,
             flags := { zf := true } } (.cmov .e "a" (.imm 111))).get "a").toNat
      == 111

#guard
    ((step { regs := fun r => if r = "a" then (222 : BitVec 64) else 0,
             flags := { zf := false } } (.cmov .e "a" (.imm 111))).get "a").toNat
      == 222

/-! ## The shift-count correspondence caveat, made explicit

Jasmin masks the shift count (`& 63` at U64); our `step` does not. For a count
`< w` they agree (validated above). For a count `≥ w` they differ — recorded
here so the gap is in the artifact, not just prose. -/

/-- Jasmin `x86_SHL 1 68 = 16` (count `68 & 63 = 4`), but our unmasked model
    gives `1 <<< 68 = 0`. The two disagree above the word width; our compiler
    only emits counts `< w`, where they agree. -/
theorem shl_count_ge_width_differs :
    ((step (st 1) (.shl "a" (.imm 68))).get "a").toNat = 0 := by native_decide

/-! ## Carry-flag effect: matching Jasmin's `rflags_of_aluop` CF, in general

Beyond the sampled points, the carry flag our `ADD`/`SUB` set is *by
definition* `addCarry`/`subBorrow`, which is the "result wrapped" predicate
Jasmin records as CF (`wunsigned w != (wunsigned v1 ± wunsigned v2)`). These
hold for all inputs (not just the differential samples). -/

/-- `ADD` sets CF to the unsigned carry-out, for all inputs. -/
theorem add_setsCF {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.add dst src)).flags.cf = addCarry (s.get dst) (src.eval s) false := by
  simp [step, State.setCF]

/-- `SUB` sets CF to the unsigned borrow, for all inputs. -/
theorem sub_setsCF {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.sub dst src)).flags.cf = subBorrow (s.get dst) (src.eval s) false := by
  simp [step, State.setCF]

/-- `ADC` reads the carry-in and sets CF to the new carry-out, for all inputs. -/
theorem adc_setsCF {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.adc dst src)).flags.cf
      = addCarry (s.get dst) (src.eval s) s.flags.cf := by
  simp [step, State.setCF]

/-- `ADC` data result is `dst + src + CF` (low word), for all inputs. The
    analogue of Jasmin `add_carry = wrepr (x + y + c)`. -/
theorem adc_data {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.adc dst src)).get dst
      = s.get dst + src.eval s + (if s.flags.cf then 1 else 0) := by
  simp [step, State.setCF, State.set, State.get]

/-- `SBB` data result is `dst - src - CF` (low word), for all inputs. The
    analogue of Jasmin `sub_borrow = wrepr (x - y - c)`. -/
theorem sbb_data {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.sbb dst src)).get dst
      = s.get dst - src.eval s - (if s.flags.cf then 1 else 0) := by
  simp [step, State.setCF, State.set, State.get]

/-! ## ADX / BMI2 trio: differential pins (`MULX`, `ADCX`, `ADOX`)

Each value below was obtained by evaluating Jasmin's compiled Rocq model
(`x86_instr_decl.vo`) on concrete U64 inputs through `rocq-mcp`, then run
through our Lean `step`. The Jasmin outputs are quoted in the comments. The
`hi`/`lo` ordering follows Jasmin: `x86_MULX_lo_hi` returns the tuple
`(lo, hi)`; in our `step` `dstLo` gets the low word and `dstHi` the high word.

The MULX state has two distinct destination registers (`"lo"`, `"hi"`) plus the
two factor registers (`"a"`, `"b"`); we read both result words back. -/

/-- A width-64 state with named factor registers, no preset flags. -/
private def stMulx (x y : BitVec 64) : State 64 :=
  { regs := fun r => if r = "a" then x else if r = "b" then y else 0 }

-- MULX, full-product split. Jasmin
-- `x86_MULX_lo_hi (2^64-1) 2 = (lo, hi) = (18446744073709551614, 1)`
-- (rocq-mcp `Compute`, both words checked).
#guard
    let s := step (stMulx (BitVec.allOnes 64) 2) (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo").toNat == 18446744073709551614 && (s.get "hi").toNat == 1

-- MULX, both words non-trivial. Jasmin
-- `x86_MULX_lo_hi 1311768467463790320 18364758544493064720
--   = (2552847189736476416, 1305938385386173474)` (rocq-mcp `Compute`).
#guard
    let s := step (stMulx 1311768467463790320 18364758544493064720)
                  (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo").toNat == 2552847189736476416 &&
    (s.get "hi").toNat == 1305938385386173474

-- MULX touches no flag. Jasmin `Ox86_MULX_lo_hi_instr` output list `[Eu 1; Eu 0]`
-- is registers only — neither CF nor OF appears.
#guard
    (step { regs := fun r => if r = "a" then (7 : BitVec 64) else if r = "b" then 9 else 0,
            flags := { cf := true, of := true } }
          (.mulx "hi" "lo" (.reg "a") (.reg "b"))).flags == { cf := true, of := true }

-- ADCX with CF=1, carry-out. Jasmin `x86_ADCX (2^64-1) 1 true = (Some true, 1)`
-- (rocq-mcp `Compute`). Data and CF both checked.
#guard
    let s := step (stCF (BitVec.allOnes 64) true) (.adcx "a" (.imm 1))
    (s.get "a").toNat == 1 && s.flags.cf

-- ADCX with CF=1, no carry-out. Jasmin `x86_ADCX 5 8 true = (Some false, 14)`.
#guard
    let s := step (stCF 5 true) (.adcx "a" (.imm 8))
    (s.get "a").toNat == 14 && s.flags.cf == false

-- ADCX leaves OF untouched (`Ox86_ADCX_instr` writes only CF). Here OF starts
-- `true` and survives the ADCX.
#guard
    (step { regs := fun r => if r = "a" then (5 : BitVec 64) else 0,
            flags := { cf := true, of := true } } (.adcx "a" (.imm 8))).flags.of

-- ADOX with OF=1, carry-out. Same `x86_ADCX` semantics as ADCX but the carry
-- is routed to OF: Jasmin `x86_ADCX (2^64-1) 1 true = (Some true, 1)` with
-- `Ox86_ADOX_instr` placing the bool in OF. Data and OF both checked.
#guard
    let s := step { regs := fun r => if r = "a" then BitVec.allOnes 64 else 0,
                    flags := { of := true } } (.adox "a" (.imm 1))
    (s.get "a").toNat == 1 && s.flags.of

-- ADOX leaves CF untouched (`Ox86_ADOX_instr` writes only OF). CF starts
-- `true` and survives.
#guard
    (step { regs := fun r => if r = "a" then (5 : BitVec 64) else 0,
            flags := { cf := true, of := true } } (.adox "a" (.imm 8))).flags.cf

/-! ### Composed bignum step: `MULX → ADCX → ADOX`

The two-independent-carry-chain idiom from the emitted kernels
(`bench/mpn_adxblk_carry_compare/mpn_addmul_1_adx_blk4_64.jazz`):

```
hi, lo = #MULX(b, t0);     // full product
cf, r  = #ADCX(r, lo, cf); // accumulate low word into the CF chain
of, r  = #ADOX(r, cy, of); // accumulate carry-word into the OF chain
```

Concrete step (`b = 2^64-1`, `t0 = 3`, `r = 10`, `cy = 100`, CF=OF=0), run
through Jasmin's compiled model in one `Compute`:

```
(wunsigned lo, wunsigned hi, cf1, wunsigned r1, of1, wunsigned r2)
  = (18446744073709551613, 2, Some true, 7, Some false, 107)
```

i.e. `lo = 2^64-3`, `hi = 2`; ADCX → `r = 7`, CF set; ADOX → `r = 107`, OF clear.
We replay the same three `step`s and assert each word and flag. -/
#guard
    let s0 : State 64 :=
      { regs := fun r => if r = "b" then BitVec.allOnes 64
                         else if r = "t0" then 3
                         else if r = "r" then 10
                         else if r = "cy" then 100 else 0 }
    let s1 := step s0 (.mulx "hi" "lo" (.reg "b") (.reg "t0"))
    let s2 := step s1 (.adcx "r" (.reg "lo"))
    let s3 := step s2 (.adox "r" (.reg "cy"))
    (s1.get "lo").toNat == 18446744073709551613 &&
    (s1.get "hi").toNat == 2 &&
    s2.flags.cf && (s2.get "r").toNat == 7 &&
    s3.flags.of == false && (s3.get "r").toNat == 107

/-! ## ADX trio: all-inputs effect theorems

Beyond the sampled points, the data and flag effects hold for all inputs (the
analogue of `adc_data`/`sbb_data` for the carry-free ops). -/

/-- `MULX` writes the low word `a * b` to `dstLo` (distinct destinations),
    matching Jasmin `wrepr sz (wunsigned a * wunsigned b)`. -/
theorem mulx_lo {w : Nat} (s : State w) (dstHi dstLo : Reg) (a b : Operand)
    (h : dstLo ≠ dstHi) :
    (step s (.mulx dstHi dstLo a b)).get dstLo = a.eval s * b.eval s := by
  simp only [step, State.get_setLoHi_lo s dstLo dstHi _ _ h]

/-- `MULX` writes the high word `mulHi a b` to `dstHi`, matching Jasmin
    `high_bits sz (wunsigned a * wunsigned b)`. -/
theorem mulx_hi {w : Nat} (s : State w) (dstHi dstLo : Reg) (a b : Operand) :
    (step s (.mulx dstHi dstLo a b)).get dstHi = mulHi (a.eval s) (b.eval s) := by
  simp [step, State.setLoHi, State.set, State.get]

/-- `MULX` touches no flag (Jasmin `Ox86_MULX_lo_hi_instr` output is registers
    only), for all inputs. -/
theorem mulx_flags {w : Nat} (s : State w) (dstHi dstLo : Reg) (a b : Operand) :
    (step s (.mulx dstHi dstLo a b)).flags = s.flags := by
  simp [step, State.setLoHi, State.set]

/-- `ADCX` data result is `dst + src + CF` (low word), for all inputs. -/
theorem adcx_data {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.adcx dst src)).get dst
      = s.get dst + src.eval s + (if s.flags.cf then 1 else 0) := by
  simp [step, State.setCF, State.set, State.get]

/-- `ADCX` sets CF to the new carry-out (= our `addCarry` = Jasmin
    `waddcarry`'s `wbase <=? n`), for all inputs. -/
theorem adcx_setsCF {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.adcx dst src)).flags.cf
      = addCarry (s.get dst) (src.eval s) s.flags.cf := by
  simp [step, State.setCF]

/-- `ADCX` leaves OF untouched (`Ox86_ADCX_instr` writes only CF), for all
    inputs. -/
theorem adcx_preservesOF {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.adcx dst src)).flags.of = s.flags.of := by
  simp only [step, State.setCF_flags_of]

/-- `ADOX` data result is `dst + src + OF` (low word), for all inputs — the
    same `waddcarry` data as ADCX, but with `OF` as the carry-in. -/
theorem adox_data {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.adox dst src)).get dst
      = s.get dst + src.eval s + (if s.flags.of then 1 else 0) := by
  simp [step, State.setOF, State.set, State.get]

/-- `ADOX` sets OF to the new carry-out, reading OF as carry-in, for all
    inputs. -/
theorem adox_setsOF {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.adox dst src)).flags.of
      = addCarry (s.get dst) (src.eval s) s.flags.of := by
  simp [step, State.setOF]

/-- `ADOX` leaves CF untouched (`Ox86_ADOX_instr` writes only OF), for all
    inputs — the independence of the two carry chains. -/
theorem adox_preservesCF {w : Nat} (s : State w) (dst : Reg) (src : Operand) :
    (step s (.adox dst src)).flags.cf = s.flags.cf := by
  simp only [step, State.setOF_flags_cf]

/-! ## Easy-tier unary arms: `NOT`, `NEG` (differential pins + all-inputs)

The `not`/`neg` the kernels emit (committed `.s`, e.g. the bignum conditional
negations). Both are unary GP-register ops with a direct Jasmin Rocq
counterpart and no `JasminBinOp` source op, so — like `ADC`/`SBB` and the ADX
trio — they are validated **directly against Jasmin's `x86_*`**, not via
`lprog`.

`NOT` (Jasmin `x86_NOT sz v = wnot v`, `Ox86_NOT_instr` output `[Eu 0]` =
register only, no flag) and `NEG` (Jasmin `x86_NEG sz w`: data `v = (-w)%w`,
`CF = Some (w != 0)`, the remaining `OF/SF/PF/ZF` outside our modeled flag set).
The concrete Jasmin outputs below were obtained by `vm_compute`ing the compiled
Rocq model through `rocq-mcp` on shared `U64` inputs; our `step` reproduces them. -/

-- NOT, all-zero → all-ones. Jasmin
-- `wunsigned (x86_NOT (wrepr U64 0)) = 18446744073709551615` (rocq-mcp
-- `vm_compute`).
#guard
    ((step (st 0) (.not_ "a")).get "a").toNat == 18446744073709551615

-- NOT, `13 ↦ 2^64-14`. Jasmin
-- `wunsigned (x86_NOT (wrepr U64 13)) = 18446744073709551602`.
#guard ((step (st 13) (.not_ "a")).get "a").toNat == 18446744073709551602

-- NOT, all-ones → zero. Jasmin
-- `wunsigned (x86_NOT (wrepr U64 (2^64-1))) = 0`.
#guard
    (step { regs := fun r => if r = "a" then BitVec.allOnes 64 else 0 } (.not_ "a")).get "a"
      == 0

-- NOT touches no flag (`Ox86_NOT_instr` output is the register only).
#guard
    (step { regs := fun _ => (13 : BitVec 64), flags := { cf := true, of := true } }
          (.not_ "a")).flags == { cf := true, of := true }

-- NEG of `0`: data `0`, `CF = false`. Jasmin `x86_NEG (wrepr U64 0)` →
-- `dw = 0`, `cf = Some false` (rocq-mcp `vm_compute`).
#guard
    let s := step (st 0) (.neg "a")
    (s.get "a").toNat == 0 && s.flags.cf == false

-- NEG of `5`: data `2^64-5`, `CF = true`. Jasmin `x86_NEG (wrepr U64 5)` →
-- `dw = 18446744073709551611`, `cf = Some true`.
#guard
    let s := step (st 5) (.neg "a")
    (s.get "a").toNat == 18446744073709551611 && s.flags.cf

-- NEG of `1`: data `2^64-1`, `CF = true`. Jasmin `x86_NEG (wrepr U64 1)` →
-- `dw = 18446744073709551615`, `cf = Some true`.
#guard
    let s := step (st 1) (.neg "a")
    (s.get "a").toNat == 18446744073709551615 && s.flags.cf

/-- `NOT` writes `~dst` to `dst`, for all inputs (Jasmin `wnot`). -/
theorem not_data {w : Nat} (s : State w) (dst : Reg) :
    (step s (.not_ dst)).get dst = ~~~ s.get dst := by
  simp [step, State.set, State.get]

/-- `NOT` touches no flag, for all inputs. -/
theorem not_flags {w : Nat} (s : State w) (dst : Reg) :
    (step s (.not_ dst)).flags = s.flags := by
  simp [step, State.set]

/-- `NEG` writes `-dst` (two's complement) to `dst`, for all inputs, matching
    Jasmin `x86_NEG`'s data `(-w)%w`. -/
theorem neg_data {w : Nat} (s : State w) (dst : Reg) :
    (step s (.neg dst)).get dst = 0 - s.get dst := by
  simp [step, State.setCF, State.set, State.get]

/-- `NEG` sets `CF` to `dst ≠ 0`, matching Jasmin `x86_NEG`'s `CF = Some (w != 0)`
    (the unsigned borrow of `0 - dst`), for all inputs. -/
theorem neg_setsCF {w : Nat} (s : State w) (dst : Reg) :
    (step s (.neg dst)).flags.cf = decide (s.get dst ≠ 0) := by
  simp [step, State.setCF]

/-- `NEG` leaves `OF` untouched (the modeled flag set tracks only `CF` for
    `NEG`; Jasmin's `OF` is outside our modeled set), for all inputs. -/
theorem neg_preservesOF {w : Nat} (s : State w) (dst : Reg) :
    (step s (.neg dst)).flags.of = s.flags.of := by
  simp only [step, State.setCF_flags_of]

/-! ## Signed wide-multiply via `#MULX` + branchless correction (#359)

The owned backend's signed `64×64 → 128` high word was `#IMUL`, which pins its
high word to RDX and clobbers CF/OF — so it cannot issue between two `#ADOX`s of
an ADX dual carry chain.  s2n-bignum's safegcd instead threads its chain through
the **unsigned, flag-free, arbitrary-GPR `#MULX`** and recovers the signed high
word with the branchless correction

```
  hi_s = hi_u − [a<0]·b − [b<0]·a       [a<0] = (a >>s 63)  (all-ones iff a<0)
```

so `[a<0]·b = (a >>s 63) & b`.  `CatCrypt/Crypto/Vale/SafegcdDivstep62Emit.lean`
`signedHi` emits exactly this (`#MULX` + `SAsr`/`SAnd`/`SXor`/`SAdd`), each
subtraction open-coded as a two's-complement add so the Lean `SExpr` model
(`Nat`-truncating `SSub`) stays faithful to the wrapping hardware `-`.

The identity is validated two ways, mirroring the trio differential pins above:
an **all-inputs** `bv_decide` proof at a tractable narrow width, and **64-bit
boundary pins** (`#guard`) across the sign/magnitude spread. -/

/-- All-inputs (width 8): the high `8` bits of the signed `8×8 → 16` product
    equal the unsigned high bits minus the branchless two-term correction.
    `bv_decide` over the full `2^16` input space. -/
theorem signed_hi_correction_w8 (a b : BitVec 8) :
    (((a.signExtend 16) * (b.signExtend 16)) >>> (8 : Nat)).truncate 8
      =
    (((a.zeroExtend 16) * (b.zeroExtend 16)) >>> (8 : Nat)).truncate 8
      - ((BitVec.sshiftRight a 7) &&& b)
      - ((BitVec.sshiftRight b 7) &&& a) := by
  bv_decide

/-- 64-bit signed high word, with the exact `signedHi` emit recipe modelled in
    the backend's `Nat`-eval-then-truncate form (`#MULX` hi, masks via `>>s 63`,
    two's-complement add for each subtraction).  `corrected64 a b` = the emitted
    `phi`; `mulHiS64 a b` = the faithful signed high word. -/
private def toI64 (n : Nat) : Int := (BitVec.ofNat 64 n).toInt
private def ofI64 (z : Int) : Nat := (BitVec.ofInt 64 z).toNat
private def mulHiU64 (a b : Nat) : Nat :=
  (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat * (BitVec.ofNat 64 b).toNat / 2 ^ 64)).toNat
private def mulHiS64 (a b : Nat) : Nat := ofI64 ((toI64 a * toI64 b) >>> 64)
private def asr63 (a : Nat) : Nat := ofI64 (toI64 a >>> 63)
private def t64 (n : Nat) : Nat := (BitVec.ofNat 64 n).toNat
private def corrected64 (a b : Nat) : Nat :=
  let dst0 := mulHiU64 a b
  let c1 := t64 (asr63 a &&& b)
  let dst1 := t64 (dst0 + t64 (c1 ^^^ 18446744073709551615))
  let c2 := t64 (asr63 b &&& a)
  let dst2 := t64 (dst1 + t64 (c2 ^^^ 18446744073709551615))
  t64 (dst2 + 2)

-- Boundary pin: small positive × small positive.
#guard corrected64 5 7 == mulHiS64 5 7
-- Boundary pin: negative × positive.
#guard corrected64 (ofI64 (-3)) 100 == mulHiS64 (ofI64 (-3)) 100
-- Boundary pin: positive × negative.
#guard corrected64 100 (ofI64 (-3)) == mulHiS64 100 (ofI64 (-3))
-- Boundary pin: `-1 × -1`.
#guard corrected64 (ofI64 (-1)) (ofI64 (-1)) == mulHiS64 (ofI64 (-1)) (ofI64 (-1))
-- Boundary pin: `0 × 0`.
#guard corrected64 0 0 == mulHiS64 0 0
-- Boundary pin: most-negative × most-negative (`-2^63`).
#guard
    corrected64 (ofI64 (-(2 ^ 63))) (ofI64 (-(2 ^ 63)))
      == mulHiS64 (ofI64 (-(2 ^ 63))) (ofI64 (-(2 ^ 63)))
-- Boundary pin: max-positive × max-positive (`2^63 − 1`).
#guard
    corrected64 (ofI64 (2 ^ 63 - 1)) (ofI64 (2 ^ 63 - 1))
      == mulHiS64 (ofI64 (2 ^ 63 - 1)) (ofI64 (2 ^ 63 - 1))

/-! # Part A — Faithful transcription validation (`JasminModel.lean`, #281)

`JasminModel.lean` is the line-for-line transcription of Jasmin's Rocq x86
semantics — full five-flag state (`CF, PF, ZF, SF, OF` as `JFlag = Option Bool`,
mirroring `rflagv`), the `x86_*` semantic functions copied from
`x86_instr_decl.v`, the word ops from `word.v`, and the `evalInstr`/`runBlock`
composition from `arch_sem.v`. The pins below confirm the transcription matches
Jasmin's compiled Rocq model on concrete U64 inputs — **data word AND all five
flags**, not just the data + carry of the prior hand-authored model.

Every quoted Jasmin value was obtained by evaluating the compiled
`x86_instr_decl.vo` through `rocq-mcp`, projecting the result tuple
`t = (OF, CF, SF, PF, ZF, w)`:

```coq
(* word *) wunsigned (snd (snd (snd (snd (snd t)))))
(* OF *)   fst t      (* CF *) fst (snd t)
(* SF *)   fst (snd (snd t))   (* PF *) fst (snd (snd (snd t)))
(* ZF *)   fst (snd (snd (snd (snd t))))
```

| instr | inputs (U64) | Jasmin word | Jasmin (OF,CF,SF,PF,ZF) | transcription |
|---|---|---|---|---|
| `ADD`  | `123456789,987654321` | `1111111110` | `(F,F,F,T,F)` | ✓ all 6 |
| `SUB`  | `5,8`        | `2^64-3`     | `(F,T,T,F,F)` | ✓ all 6 |
| `ADC`  | `5,8,c=1`    | `14`         | `(F,F,F,F,F)` | ✓ all 6 |
| `SBB`  | `5,8,c=1`    | `2^64-4`     | `(F,T,T,T,F)` | ✓ all 6 |
| `AND`  | `13,7`       | `5`          | `(F,F,F,T,F)` | ✓ all 6 |
| `IMULt`| `999,1000000`| `999000000`  | `(F,F,—,—,—)` | ✓ word+OF/CF, SF/PF/ZF=Undef |
| `SHL`  | `1` by `4`   | `16`         | `(—,F,F,F,F)` | ✓ word+flags, OF=Undef (i≠1) |
| `SAR`  | `-8` by `1`  | `2^64-4`     | `(F,F,T,T,F)` | ✓ word+flags (arith shift, sign kept) |
| `MULX` | `(2^64-1),2` | `lo=2^64-2,hi=1` | no flag | ✓ |
| `ADCX` | `(2^64-1),1,c=1` | `1`      | `CF=Some true` | ✓ |

These complement the data-only / data+carry pins above; together they validate
the transcription's *full* flag behaviour for the emitted subset.
-/

namespace Jasmin

/-- A width-64 state with register `"a" := v`, no preset flags. -/
private def jst (v : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "a" then v else 0 }

/-- A width-64 state with `"a" := v` and `CF := some c`. -/
private def jstCF (v : BitVec 64) (c : Bool) : JState 64 :=
  { regs := fun r => if r = "a" then v else 0, flags := { cf := some c } }

-- ADD, full tuple. Jasmin `x86_ADD 123456789 987654321`:
-- word `1111111110`, `(OF,CF,SF,PF,ZF) = (F,F,F,T,F)`.
#guard
    let s := evalInstr (jst 123456789) (.add "a" (.imm 987654321))
    (s.get "a").toNat == 1111111110 &&
    s.flags == { of := some false, cf := some false, sf := some false,
                 pf := some true, zf := some false }

-- SUB, full tuple. Jasmin `x86_SUB 5 8`:
-- word `2^64-3`, `(F,T,T,F,F)` (CF = borrow).
#guard
    let s := evalInstr (jst 5) (.sub "a" (.imm 8))
    (s.get "a").toNat == 18446744073709551613 &&
    s.flags == { of := some false, cf := some true, sf := some true,
                 pf := some false, zf := some false }

-- ADC with CF=1, full tuple. Jasmin `x86_ADC 5 8 true`:
-- word `14`, `(F,F,F,F,F)`.
#guard
    let s := evalInstr (jstCF 5 true) (.adc "a" (.imm 8))
    (s.get "a").toNat == 14 &&
    s.flags == { of := some false, cf := some false, sf := some false,
                 pf := some false, zf := some false }

-- SBB with CF=1, full tuple. Jasmin `x86_SBB 5 8 true`:
-- word `2^64-4`, `(F,T,T,T,F)`.
#guard
    let s := evalInstr (jstCF 5 true) (.sbb "a" (.imm 8))
    (s.get "a").toNat == 18446744073709551612 &&
    s.flags == { of := some false, cf := some true, sf := some true,
                 pf := some true, zf := some false }

-- AND, full tuple. Jasmin `x86_AND 13 7`: word `5`, `(F,F,F,T,F)`
-- (bitwise ops clear OF and CF).
#guard
    let s := evalInstr (jst 13) (.and_ "a" (.imm 7))
    (s.get "a").toNat == 5 &&
    s.flags == { of := some false, cf := some false, sf := some false,
                 pf := some true, zf := some false }

-- IMULt low word, full tuple. Jasmin `x86_IMULt 999 1000000`:
-- word `999000000`, `(F,F,None,None,None)` (`rflags_of_mul`: only OF/CF set).
#guard
    let s := evalInstr (jst 999) (.imul "a" (.imm 1000000))
    (s.get "a").toNat == 999000000 &&
    s.flags == { of := some false, cf := some false, sf := none,
                 pf := none, zf := none }

-- SHL by 4, full tuple. Jasmin `x86_SHL 1 4`: word `16`, `(None,F,F,F,F)`
-- (OF undefined because the count `i ≠ 1`).
#guard
    let s := evalInstr (jst 1) (.shl "a" (.imm 4))
    (s.get "a").toNat == 16 &&
    s.flags == { of := none, cf := some false, sf := some false,
                 pf := some false, zf := some false }

-- SAR of a negative word by 1, full tuple. Jasmin
-- `x86_SAR (2^64-8) 1 = 2^64-4` (arithmetic shift keeps the sign bit),
-- `(F,F,T,T,F)` (OF = `some false` since `i = 1`). This is the arm with **no
-- `lprog` source op** (the source IR carries only logical `shr`); it is
-- validated directly against Jasmin here.
#guard
    let s := evalInstr (jst (BitVec.ofNat 64 (2^64 - 8))) (.sar "a" (.imm 1))
    (s.get "a").toNat == 18446744073709551612 &&
    s.flags == { of := some false, cf := some false, sf := some true,
                 pf := some true, zf := some false }

-- SAR of a positive word: `x86_SAR 256 4 = 16`.
#guard ((evalInstr (jst 256) (.sar "a" (.imm 4))).get "a").toNat == 16

-- MULX, full product split, no flag. Jasmin
-- `x86_MULX_lo_hi (2^64-1) 2 = (lo, hi) = (2^64-2, 1)`.
#guard
    let s := evalInstr
      { regs := fun r => if r = "a" then BitVec.allOnes 64 else if r = "b" then 2 else 0 }
      (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo").toNat == 18446744073709551614 && (s.get "hi").toNat == 1

-- ADCX with CF=1, carry-out: Jasmin `x86_ADCX (2^64-1) 1 true = (Some true, 1)`,
-- routed to CF only.
#guard
    let s := evalInstr (jstCF (BitVec.allOnes 64) true) (.adcx "a" (.imm 1))
    (s.get "a").toNat == 1 && s.flags.cf == some true

-- ADCX leaves OF untouched (writes only CF).
#guard
    (evalInstr { regs := fun r => if r = "a" then (5 : BitVec 64) else 0,
                 flags := { cf := some true, of := some true } }
               (.adcx "a" (.imm 8))).flags.of == some true

-- ADOX with OF=1, carry-out: same `x86_ADCX` data, routed to OF only.
#guard
    let s := evalInstr { regs := fun r => if r = "a" then BitVec.allOnes 64 else 0,
                         flags := { of := some true } } (.adox "a" (.imm 1))
    (s.get "a").toNat == 1 && s.flags.of == some true

-- ADOX leaves CF untouched (writes only OF).
#guard
    (evalInstr { regs := fun r => if r = "a" then (5 : BitVec 64) else 0,
                 flags := { cf := some true, of := some true } }
               (.adox "a" (.imm 8))).flags.cf == some true

/-! ## Real emitted block: the `#MULX → #ADCX → #ADOX` carry chain

`bench/mpn_adxblk_carry_compare/mpn_addmul_1_adx_blk4_64.jazz`, lines 17–19
(the first multiply of the AVX/ADX `addmul_1` inner loop):

```
hi0, lo0 = #MULX(b, t0);     // full product b * t0
cf,  r0  = #ADCX(r0, lo0, cf); // accumulate low word into the CF chain
of,  r0  = #ADOX(r0, cy, of);  // accumulate carry word into the OF chain
```

Concrete step (`b = 2^64-1`, `t0 = 3`, `r0 = 10`, `cy = 100`, CF = OF = 0), run
through Jasmin's compiled model in one sequence evaluation:

```
(wunsigned lo0, wunsigned hi0, cf1, wunsigned r0', of1, wunsigned r0'')
  = (2^64-3, 2, Some true, 7, Some false, 107)
```

We replay the same three `evalInstr`s on the faithful state and assert each word
and flag — the `runBlock` analogue of jasmin's sequential `eval_instr`. -/

-- The emitted `MULX → ADCX → ADOX` block, validated against Jasmin's sequence
-- evaluation, on the faithful five-flag state.
#guard
    let s0 : JState 64 :=
      { regs := fun r => if r = "b" then BitVec.allOnes 64
                         else if r = "t0" then 3
                         else if r = "r0" then 10
                         else if r = "cy" then 100 else 0
        flags := { cf := some false, of := some false } }
    let i0 : JInstr 64 := .mulx "hi0" "lo0" (.reg "b") (.reg "t0")
    let i1 : JInstr 64 := .adcx "r0" (.reg "lo0")
    let i2 : JInstr 64 := .adox "r0" (.reg "cy")
    let s1 := evalInstr s0 i0
    let s := runBlock s0 [i0, i1, i2]
    (s1.get "lo0").toNat == 18446744073709551613 &&
    (s1.get "hi0").toNat == 2 &&
    s.flags.cf == some true &&
    s.flags.of == some false &&
    (s.get "r0").toNat == 107

/-! ## Shift-count mask, made explicit (faithful side)

The transcription's `shiftCount` applies Jasmin's `& (w-1)` mask (`x86_shift_mask
U64 = 63`); `Model.lean`'s `step` shifts by the raw count. For a count `< w` they
agree; above the width the transcription wraps (`68 & 63 = 4`) where the prior
model gave `0`. The transcription is the one that matches Jasmin. -/

-- Jasmin `x86_SHL 1 68 = 16` (`68 & 63 = 4`): the faithful transcription
-- reproduces the mask, where `Model.step` (`shl_count_ge_width_differs`) gave
-- `0`.
#guard ((evalInstr (jst 1) (.shl "a" (.imm 68))).get "a").toNat == 16

/-! ## Reconciliation with the prior hand-authored model

`Model.lean`'s `step` (`CF`/`OF` only) agrees with the faithful transcription on
the **data result** for the modeled subset, so `Preservation.lean`'s theorems
carry over unchanged. The data words are equal by definitional unfolding; we pin
the representatives by `#guard` on a shared state to avoid restating the
`step`/`evalInstr` defeqs. -/

-- `Model.step` and the faithful `evalInstr` produce the same destination word
-- for `ADD` on a shared input.
#guard
    (step (st 123456789) (.add "a" (.imm 987654321))).get "a"
      == (evalInstr (jst 123456789) (.add "a" (.imm 987654321))).get "a"

-- Same for `MULX` (both result words).
#guard
    let s := step (stMulx (BitVec.allOnes 64) 2) (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    let s' := evalInstr
      { regs := fun r => if r = "a" then BitVec.allOnes 64 else if r = "b" then 2 else 0 }
      (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    s.get "lo" == s'.get "lo" && s.get "hi" == s'.get "hi"

-- Same for `ADCX` data + the carry the prior model also tracked.
#guard
    (step (stCF (BitVec.allOnes 64) true) (.adcx "a" (.imm 1))).get "a"
      == (evalInstr (jstCF (BitVec.allOnes 64) true) (.adcx "a" (.imm 1))).get "a"

/-! ## The remaining emitted-kernel arms: `CMOVcc` variants, `MULX`-mem, `MOV`-mem (#281)

The session's owned-backend kernels (`Fe25519MulKernel`/`Fe25519OpsKernel`/
`P256FieldKernel`/`P384FieldKernel`/`Ed25519PointKernel`/`X25519MonoLadderKernel`)
emit five `JInstr` arms that the earlier pins did not cover directly:
`cmovne`/`cmovb` (the conditional-swap/conditional-subtract selects of the
constant-time field carry-fixups and the X25519 cswap), `mulxMem` (s2n-bignum's
fold of the multiplicand load into the `#MULX`), and `loadMem`/`storeMem` (the
reg-ptr ABI's argument-load / result-store `movq`). Each is grounded here
against Jasmin's compiled Rocq model exactly as the earlier arms were.

Each quoted Jasmin value was obtained by evaluating Jasmin's compiled Rocq model
(`Jasmin.x86_instr_decl`, the same `.vo` the earlier pins use) through `rocq-mcp`:

```coq
Require Import Jasmin.x86_instr_decl. Import word_ssrZ word utils.
Compute (wunsigned (@x86_CMOVcc U64 true  (@wrepr U64 111) (@wrepr U64 222))).  (* = 111 *)
Compute (wunsigned (@x86_CMOVcc U64 false (@wrepr U64 111) (@wrepr U64 222))).  (* = 222 *)
Compute (wunsigned (@x86_MOV U64 (@wrepr U64 123456789))).                      (* = 123456789 *)
Compute (let r := @x86_MULX_lo_hi U64 (@wrepr U64 18446744073709551615)
                                       (@wrepr U64 3) in
         (wunsigned (fst r), wunsigned (snd r))).                              (* = (lo,hi) = (2^64-3, 2) *)
```

All three condition wrappers (`Ox86_CMOVcc_instr`, output list `[:: Ea 1]`)
write the destination register **only** — no flag — and select with
`x86_CMOVcc b w2 w3 = if b then w2 else w3`, with the boolean `b` being the
flag the condition reads: `CMOVE → ZF`, `CMOVNE → ¬ZF`, `CMOVB → CF`. The
memory arms reuse the validated `x86_MOV` (= identity) and `x86_MULX_lo_hi`,
composed with `mem_read`/`mem_write` on the word-addressed memory — exactly how
`arch_sem.v` evaluates a `MOV`/`MULX` whose operand is an `Addr` rather than a
`Reg`. -/

/-- A width-64 state with `"a" := v` and a memory word `[base + off] := m`. -/
private def jstMem (v : BitVec 64) (base : String) (off : Int) (m : BitVec 64) :
    JState 64 :=
  { regs := fun r => if r = "a" then v else 0
    mem := fun b o => if b = base ∧ o = off then m else 0 }

-- CMOVE taken / not taken, against Jasmin `x86_CMOVcc (b = ZF) src dst`.
-- `ZF = true` selects the source (`111`); `ZF = false` keeps the dest (`222`).
-- Writes no flag (`Ox86_CMOVcc_instr` output is `[:: Ea 1]`).
#guard
    let s := evalInstr { regs := fun r => if r = "a" then (222 : BitVec 64) else 0,
                         flags := { zf := some true } } (.cmove "a" (.imm 111))
    (s.get "a").toNat == 111 && s.flags == { zf := some true }

#guard
    ((evalInstr { regs := fun r => if r = "a" then (222 : BitVec 64) else 0,
                  flags := { zf := some false } } (.cmove "a" (.imm 111))).get "a").toNat
      == 222

-- CMOVNE reads `¬ZF`: `ZF = false` selects the source (`111`), `ZF = true`
-- keeps the dest (`222`). Same `x86_CMOVcc` selector, complemented condition.
#guard
    let s := evalInstr { regs := fun r => if r = "a" then (222 : BitVec 64) else 0,
                         flags := { zf := some false } } (.cmovne "a" (.imm 111))
    (s.get "a").toNat == 111 && s.flags == { zf := some false }

#guard
    ((evalInstr { regs := fun r => if r = "a" then (222 : BitVec 64) else 0,
                  flags := { zf := some true } } (.cmovne "a" (.imm 111))).get "a").toNat
      == 222

-- CMOVB reads `CF`: `CF = true` selects the source (`111`), `CF = false`
-- keeps the dest (`222`). The conditional-subtract carry fixup of the field
-- kernels (`P256FieldKernel`/`X25519MonoLadderKernel`).
#guard
    let s := evalInstr { regs := fun r => if r = "a" then (222 : BitVec 64) else 0,
                         flags := { cf := some true } } (.cmovb "a" (.imm 111))
    (s.get "a").toNat == 111 && s.flags == { cf := some true }

#guard
    ((evalInstr { regs := fun r => if r = "a" then (222 : BitVec 64) else 0,
                  flags := { cf := some false } } (.cmovb "a" (.imm 111))).get "a").toNat
      == 222

-- `loadMem`: `dst := [base + off]`, the reg-ptr ABI argument-load.
-- Jasmin `x86_MOV` is identity, so the destination receives the memory word
-- verbatim (`123456789` here); no flag is written (`Ox86_MOV_instr`).
#guard
    let s := evalInstr (jstMem 0 "rp" 16 123456789) (.loadMem "a" "rp" 16)
    (s.get "a").toNat == 123456789 && s.flags == ({} : RFlags)

-- `storeMem`: `[base + off] := src`, the reg-ptr ABI result-store. The memory
-- word receives the source verbatim (Jasmin `x86_MOV` = identity); registers
-- and flags are untouched.
#guard
    let s := evalInstr { regs := fun r => if r = "a" then (123456789 : BitVec 64) else 0 }
                       (.storeMem "rp" 16 (.reg "a"))
    (s.load "rp" 16).toNat == 123456789 && s.flags == ({} : RFlags)

-- `mulxMem`: the full product split with the second factor read from memory,
-- against Jasmin `x86_MULX_lo_hi a [base + off]` — the **same** `wumul` as the
-- reg form (validated above), so on `a = 2^64-1`, `[base+off] = 3` it yields
-- `(lo, hi) = (2^64-3, 2) = (18446744073709551613, 2)`. No flag (s2n's
-- `mulxq off(%base), %lo, %hi`).
#guard
    let s := evalInstr (jstMem (BitVec.allOnes 64) "bp" 8 3)
                       (.mulxMem "hi" "lo" (.reg "a") "bp" 8)
    (s.get "lo").toNat == 18446744073709551613 &&
    (s.get "hi").toNat == 2 && s.flags == ({} : RFlags)

-- `mulxMem`, both result words non-trivial — the same factors as the reg-`mulx`
-- pin above, with the second read from memory. Jasmin
-- `x86_MULX_lo_hi 1311768467463790320 18364758544493064720
--   = (lo, hi) = (2552847189736476416, 1305938385386173474)`.
#guard
    let s := evalInstr (jstMem 1311768467463790320 "bp" 0 18364758544493064720)
                       (.mulxMem "hi" "lo" (.reg "a") "bp" 0)
    (s.get "lo").toNat == 2552847189736476416 &&
    (s.get "hi").toNat == 1305938385386173474

/-! ### All-inputs effect theorems for the five new arms

Beyond the sampled points, the data and flag effects hold for **all** inputs,
matching the corresponding Jasmin `x86_*` functions. These mirror the
`adc_data`/`mulx_lo`/`not_data` all-inputs theorems for the earlier arms. -/

/-- `CMOVE` selects on `ZF`, writes no flag, for all inputs. -/
theorem jcmove_spec {w : Nat} (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.cmove dst src)).get dst
      = (if s.flagB (·.zf) then src.eval s else s.get dst)
    ∧ (evalInstr s (.cmove dst src)).flags = s.flags := by
  refine ⟨?_, ?_⟩ <;> simp [evalInstr, x86_CMOVcc, JState.setReg, JState.get]

/-- `CMOVNE` selects on `¬ZF`, writes no flag, for all inputs. -/
theorem jcmovne_spec {w : Nat} (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.cmovne dst src)).get dst
      = (if s.flagB (·.zf) then s.get dst else src.eval s)
    ∧ (evalInstr s (.cmovne dst src)).flags = s.flags := by
  refine ⟨?_, ?_⟩
  · simp only [evalInstr, x86_CMOVcc, JState.setReg, JState.get]
    cases s.flagB (·.zf) <;> simp
  · simp [evalInstr, x86_CMOVcc, JState.setReg, JState.get]

/-- `CMOVB` selects on `CF`, writes no flag, for all inputs. -/
theorem jcmovb_spec {w : Nat} (s : JState w) (dst : String) (src : JOperand) :
    (evalInstr s (.cmovb dst src)).get dst
      = (if s.flagB (·.cf) then src.eval s else s.get dst)
    ∧ (evalInstr s (.cmovb dst src)).flags = s.flags := by
  refine ⟨?_, ?_⟩ <;> simp [evalInstr, x86_CMOVcc, JState.setReg, JState.get]

/-- `loadMem` reads `[base + off]` into `dst` (Jasmin `x86_MOV` = identity),
    writing no flag, for all inputs. -/
theorem jloadMem_spec {w : Nat} (s : JState w) (dst base : String) (off : Int) :
    (evalInstr s (.loadMem dst base off)).get dst = s.load base off
    ∧ (evalInstr s (.loadMem dst base off)).flags = s.flags := by
  refine ⟨?_, ?_⟩ <;> simp [evalInstr, x86_MOV, JState.setReg, JState.get, JState.load]

/-- `storeMem` writes `src` to `[base + off]` (Jasmin `x86_MOV` = identity),
    leaving registers and flags unchanged, for all inputs. -/
theorem jstoreMem_spec {w : Nat} (s : JState w) (base : String) (off : Int)
    (src : JOperand) :
    (evalInstr s (.storeMem base off src)).load base off = src.eval s
    ∧ (evalInstr s (.storeMem base off src)).flags = s.flags
    ∧ (evalInstr s (.storeMem base off src)).regs = s.regs := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [evalInstr, x86_MOV, JState.store, JState.load]

/-- `mulxMem` writes the low word `wrepr (a * [base+off])` to `dstLo` and the
    high word `high_bits` to `dstHi` — the reg-`mulx` `wumul`, with src2 read
    from memory — touching no flag, for all inputs (distinct destinations). The
    low word is stated in Jasmin's `wrepr`/`ofNat` form (= `a * [base+off]` as
    `BitVec.mul`). -/
theorem jmulxMem_spec {w : Nat} (s : JState w) (dstHi dstLo a base : String)
    (off : Int) (h : dstLo ≠ dstHi) :
    (evalInstr s (.mulxMem dstHi dstLo (.reg a) base off)).get dstLo
        = BitVec.ofNat w ((s.get a).toNat * (s.load base off).toNat)
    ∧ (evalInstr s (.mulxMem dstHi dstLo (.reg a) base off)).flags = s.flags := by
  refine ⟨?_, ?_⟩ <;>
    simp [evalInstr, x86_MULX_lo_hi, wumul, JState.setReg, JState.get, JState.load, h]

end Jasmin

end CatCrypt.Crypto.SecureCompilation.X86Backend
