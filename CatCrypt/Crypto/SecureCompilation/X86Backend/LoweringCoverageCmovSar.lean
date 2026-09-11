/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

/-!
# `Linstr → JInstr` coverage superset: immediate arithmetic right-shift and select

`LoweringExtendedCoverage.lean` builds `lowerLinstrExtCov`, the superset of
`lowerLinstrExt2` carrying the carry-chain ADX bindings (`ADCX:64`/`ADOX:64`/
`ADCXHI:64`/`ADOXHI:64`) and the register-indexed (SIB) memory ops
(`LOADIDX`/`STOREIDX`). It returns `none` on two exporter shapes:

* the **immediate arithmetic right-shift** `SAR:<n>:64` (the `sarImm` op) —
  `lowerLinstrExt2`'s single-source arm runs `parseShiftMnem`, which recognises
  only the `SHL:`/`SHR:` prefixes, and `SAR:<n>` is not an entry of the ALU
  table either;
* the **constant-time select** `CMOV:64` (the `select` op) — a three-source
  binding, which no arm below this level matches.

`lowerLinstrExtCov2` is the superset that lowers both and delegates every other
shape to `lowerLinstrExtCov` verbatim.

## The two exporter shapes

From `opToLinstrR` (`JasminLprogExport.lean`):

| op | export |
|---|---|
| `sarImm w n` | `Lopn [reg dst] (withWidthTag w ("SAR:" ++ toString n)) [src]` |
| `select w` | `Lopn [reg dst] (withWidthTag w "CMOV") [cond, t, f]` |

`withWidthTag` appends `":64"` at `w = 64` and leaves the mnemonic bare
otherwise, so the 64-bit exports are `"SAR:<n>:64"` and `"CMOV:64"`.

`select w` has type `[reg 1, reg w, reg w] → reg w` and denotes
`selectW cond t f = if cond = 1 then t else f` (`JasminDialect.lean`), with the
condition an explicit `reg 1` register value rather than a processor flag.

## Lowering the select without a `test` instruction

`JInstr`'s `cmove`/`cmovne` read `ZF`, so a lowering must first materialise the
condition register into `ZF`. `test r, r` does that and writes no register:
`x86_TEST v v = rflags_of_bwop (v &&& v)` sets `ZF = (v = 0)`, `OF = CF = false`
and `SF`/`PF` from `v`.

The lowered block mirrors `LprogAsmPrinter.renderLopn`'s `CMOV` arm branch for
branch, and uses the same instruction it renders:

| operand aliasing | block |
|---|---|
| `t = dst` | `test cn cn; cmove dst f` |
| `f = dst` | `test cn cn; cmovne dst t` |
| neither | `mov dst f; test cn cn; cmovne dst t` |

The `t = dst` branch selects on the complementary condition so the defaulting
`mov` never clobbers `t`. A binding whose condition register is the destination
(`cn = dst`) lowers to `none`: the general branch's `mov dst f` would clobber the
condition before `test cn cn` reads it. The exporter's argument-liveness pin
keeps the condition and the destination in distinct registers.

## Shift counts

The count `n` lives in the mnemonic suffix. `sarCountOf` recognises the tagged
mnemonic over the character list (`String.toList` plus `List.isPrefixOf`, the
form that reduces in the kernel) and reads the digits through a literal digit
table, so every witness is a kernel `rfl` — `String.toNat?` and the
`Substring`-based `String.startsWith` do not reduce there (`GatherImmForms §2a`
threads its shift counts as hypotheses for that reason).

`sarCountOf` accepts the `":64"`-tagged mnemonic only. `JInstr.sar` encodes with
`REX.W` (a 64-bit `sarq`), which is the operand size the tagged export names.
The untagged narrow export `SAR:31` is carried by its own literal arm and lowers
to the same 64-bit `sar`.

## Constant-time class

Both lowered blocks are `allDirect`: `mov`/`sar`/`test`/`cmove`/`cmovne` address
no memory, so `MachineConstantTime.instrLeak` is empty for each and the block's
leak trace is state-independent.

## Shapes this level still declines

* `CMOV` untagged (a narrow-width select) and a `CMOV:64` whose condition,
  true-value or false-value operand is not a register.
* `ROR:<n>` / `ZEROEXT` / `TRUNC` / `CALL:` / `CALLN:` / `VPACK8u64:` and every
  non-`Lopn` `LinstrR`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

/-! ## 1. The shift-count recogniser -/

/-- The value of a decimal digit character, `none` for any other character.
    A literal table rather than `Char.toNat` arithmetic, so it reduces in the
    kernel on a closed mnemonic. -/
def digitVal : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

/-- Fold a non-empty list of decimal digit characters into its value, `none` if
    any character is not a digit. -/
def digitsOf : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
      match digitVal c with
      | some v => digitsOf cs (acc * 10 + v)
      | none => none

/-- The shift count of a `":64"`-tagged immediate arithmetic-right-shift mnemonic
    `"SAR:<n>:64"`, `none` for every other mnemonic. Recognition is over the
    character list, so it reduces in the kernel on a closed mnemonic. -/
def sarCountOf (opn : String) : Option Nat :=
  let cs := opn.toList
  if [':', '6', '4'].isSuffixOf cs then
    let body := cs.take (cs.length - 3)
    if ['S', 'A', 'R', ':'].isPrefixOf body then
      match body.drop 4 with
      | [] => none
      | ds => digitsOf ds 0
    else none
  else none

/-! ## 2. The two lowered blocks -/

/-- Lower a native immediate arithmetic right-shift `dst := src >>ₐ n` to
    two-address form `[mov dst src, sar dst #n]` (`SAR r, imm`). -/
def lowerSarJ (dst : String) (n : Nat) (src : JOperand) : List (JInstr 64) :=
  [JInstr.mov dst src, JInstr.sar dst (JOperand.imm n)]

/-- Lower a constant-time select `dst := if cond ≠ 0 then t else f` over register
    operands, with `test cn cn` materialising the condition register into `ZF`
    and a `CMOVcc` selecting. The destination
    is defaulted to whichever of `t`/`f` it does not already hold, and the
    condition of the `CMOVcc` is chosen accordingly, so the defaulting `mov`
    never clobbers the value the conditional move reads. -/
def lowerCmovJ (dst cn tn fn : String) : List (JInstr 64) :=
  if tn == dst then
    [JInstr.test cn (.reg cn), JInstr.cmove dst (.reg fn)]
  else
    (if fn == dst then [] else [JInstr.mov dst (.reg fn)])
      ++ [JInstr.test cn (.reg cn), JInstr.cmovne dst (.reg tn)]

/-! ## 3. The coverage superset

`lowerLinstrExtCov2` intercepts the three-source `CMOV:64` binding and the
single-source shapes, lowering the latter when `sarCountOf` recognises the
mnemonic and delegating to `lowerLinstrExtCov` otherwise. No mnemonic
`lowerLinstrExtCov` accepts begins with `SAR:` or is `CMOV:64`, so on every shape
it already covers the delegation is verbatim. -/

/-- The coverage superset lowering. New arms over `lowerLinstrExtCov`: the
    `":64"`-tagged immediate arithmetic right-shifts `SAR:<n>:64`, the untagged
    narrow `SAR:31`, and the constant-time select `CMOV:64` over register
    operands. Every other shape delegates to `lowerLinstrExtCov`. -/
def lowerLinstrExtCov2 : LinstrR → Option (List (JInstr 64))
  -- constant-time select (`select w` export): three sources `[cond, t, f]`
  | .Lopn [.reg dst] "CMOV:64" [.reg cn, .reg tn, .reg fn] =>
      if cn == dst then none else some (lowerCmovJ dst cn tn fn)
  -- narrow-width (w ≠ 64, no `:64` tag), lowered to a 64-bit `sar`
  | .Lopn [.reg dst] "SAR:31" [src] => some (lowerSarJ dst 31 (lowerJOperand src))
  -- the tagged immediate arithmetic right-shifts, count read from the mnemonic
  | .Lopn [.reg dst] opn [src] =>
      match sarCountOf opn with
      | some n => some (lowerSarJ dst n (lowerJOperand src))
      | none   => lowerLinstrExtCov (.Lopn [.reg dst] opn [src])
  -- everything else: the ADX/SIB coverage superset verbatim
  | i => lowerLinstrExtCov i

/-- Lower a full `Linstr` (drops the position tag), coverage superset. -/
def lowerLinstrExtCov2L (i : Linstr) : Option (List (JInstr 64)) :=
  lowerLinstrExtCov2 i.li_i

/-! ## 4. Shift-count recogniser witnesses -/

/-- The recogniser reads the count out of a tagged mnemonic. -/
theorem sarCountOf_63 : sarCountOf "SAR:63:64" = some 63 := rfl

/-- A two-digit count whose digits differ. -/
theorem sarCountOf_23 : sarCountOf "SAR:23:64" = some 23 := rfl

/-- The ML-DSA `montgomery_reduce` count. -/
theorem sarCountOf_32 : sarCountOf "SAR:32:64" = some 32 := rfl

/-- A single-digit count. -/
theorem sarCountOf_1 : sarCountOf "SAR:1:64" = some 1 := rfl

/-- An untagged mnemonic is not recognised (the width the `JInstr 64` `sar`
    encodes is the tagged one). -/
theorem sarCountOf_untagged : sarCountOf "SAR:31" = none := rfl

/-- A logical right shift is not an arithmetic one. -/
theorem sarCountOf_shr : sarCountOf "SHR:32:64" = none := rfl

/-- An ALU mnemonic is not recognised. -/
theorem sarCountOf_add : sarCountOf "ADD:64" = none := rfl

/-- A `SAR:` mnemonic with no count is not recognised. -/
theorem sarCountOf_empty : sarCountOf "SAR::64" = none := rfl

/-! ## 5. Coverage witnesses (the shapes `lowerLinstrExtCov` drops) -/

/-- `SAR:63:64` arithmetic right-shift (the `>> 63` sign-extract in ML-DSA
    `decompose`/`use_hint`), lowered to `[mov dst src, sar dst #63]`. -/
theorem lowerLinstrExtCov2_sar63 (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "SAR:63:64" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 63)] := rfl

/-- `SAR:23:64` arithmetic right-shift (the `Rhs.sarImm 23` in ML-DSA
    `reduce32`). -/
theorem lowerLinstrExtCov2_sar23 (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "SAR:23:64" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 23)] := rfl

/-- `SAR:32:64` arithmetic right-shift (the `Rhs.sarImm 32` in ML-DSA
    `montgomery_reduce`). -/
theorem lowerLinstrExtCov2_sar32 (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "SAR:32:64" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 32)] := rfl

/-- The untagged narrow `SAR:31`, lowered to a 64-bit `sar`. -/
theorem lowerLinstrExtCov2_sar31_narrow (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "SAR:31" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 31)] := rfl

/-- `CMOV:64` over three distinct registers: the defaulting `mov`, the
    condition-to-`ZF` `test`, and the `cmovne`. -/
theorem lowerLinstrExtCov2_cmov64 (dst cn tn fn : String)
    (hc : (cn == dst) = false) (ht : (tn == dst) = false) (hf : (fn == dst) = false) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "CMOV:64" [.reg cn, .reg tn, .reg fn])
      = some [JInstr.mov dst (.reg fn), JInstr.test cn (.reg cn),
              JInstr.cmovne dst (.reg tn)] := by
  simp only [lowerLinstrExtCov2, lowerCmovJ, hc, ht, hf, if_false, Bool.false_eq_true,
    List.nil_append, List.cons_append]

/-- `CMOV:64` whose false-value operand is already the destination: no defaulting
    `mov`, two instructions. -/
theorem lowerLinstrExtCov2_cmov64_inPlace (dst cn tn : String)
    (hc : (cn == dst) = false) (ht : (tn == dst) = false) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "CMOV:64" [.reg cn, .reg tn, .reg dst])
      = some [JInstr.test cn (.reg cn), JInstr.cmovne dst (.reg tn)] := by
  simp only [lowerLinstrExtCov2, lowerCmovJ, hc, ht, if_false, Bool.false_eq_true,
    beq_self_eq_true, if_true, List.nil_append]

/-- `CMOV:64` whose true-value operand is already the destination: the
    complementary `cmove` on the false-value operand. -/
theorem lowerLinstrExtCov2_cmov64_trueInPlace (dst cn fn : String)
    (hc : (cn == dst) = false) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "CMOV:64" [.reg cn, .reg dst, .reg fn])
      = some [JInstr.test cn (.reg cn), JInstr.cmove dst (.reg fn)] := by
  simp only [lowerLinstrExtCov2, lowerCmovJ, hc, if_false, Bool.false_eq_true,
    beq_self_eq_true, if_true]

/-- A `CMOV:64` whose condition register is the destination lowers to `none`:
    the defaulting `mov` would clobber the condition. -/
theorem lowerLinstrExtCov2_cmov64_condIsDst (dst tn fn : String) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "CMOV:64" [.reg dst, .reg tn, .reg fn])
      = none := by
  simp only [lowerLinstrExtCov2, beq_self_eq_true, if_true]

/-! ## 6. Delegation

On every shape whose mnemonic is neither a tagged `SAR:<n>` nor `CMOV:64`,
`lowerLinstrExtCov2` reduces to `lowerLinstrExtCov` applied to the same
`LinstrR`, so it agrees verbatim. -/

/-- The superset agrees with `lowerLinstrExtCov` on a two-source ALU `ADD:64`
    binding. -/
theorem lowerLinstrExtCov2_delegates_add (dst : String) (s0 s1 : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "ADD:64" [s0, s1])
      = lowerLinstrExtCov (.Lopn [.reg dst] "ADD:64" [s0, s1]) := rfl

/-- And on the carry-chain `ADCX:64` data binding (three sources). -/
theorem lowerLinstrExtCov2_delegates_adcx (dst : String) (s0 s1 cin : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "ADCX:64" [s0, s1, cin])
      = lowerLinstrExtCov (.Lopn [.reg dst] "ADCX:64" [s0, s1, cin]) := rfl

/-- And on the register-indexed `LOADIDX` SIB gather. -/
theorem lowerLinstrExtCov2_delegates_loadidx (dst base idx : String) (scale : Nat) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx scale])
      = lowerLinstrExtCov (.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx scale]) := rfl

/-- And on a single-source `MOV:64`, which the ALU table lowers. -/
theorem lowerLinstrExtCov2_delegates_mov (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "MOV:64" [src])
      = lowerLinstrExtCov (.Lopn [.reg dst] "MOV:64" [src]) := rfl

/-- And on a single-source immediate logical shift `SHR:32:64`. -/
theorem lowerLinstrExtCov2_delegates_shr (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "SHR:32:64" [src])
      = lowerLinstrExtCov (.Lopn [.reg dst] "SHR:32:64" [src]) := rfl

/-! ## 7. Constant-time class of the new blocks -/

/-- The lowered `SAR` block is `allDirect`: the shift amount is a compile-time
    immediate and the operands are registers. -/
theorem lowerLinstrExtCov2_sar_allDirect (dst : String) (src : JOperand) (n : Nat) :
    allDirect [(JInstr.mov dst src : JInstr 64), JInstr.sar dst (JOperand.imm n)] = true := rfl

/-- The lowered select block is `allDirect` in each of its three branches. -/
theorem lowerLinstrExtCov2_cmov_allDirect (dst cn tn fn : String) :
    allDirect (lowerCmovJ dst cn tn fn) = true := by
  unfold lowerCmovJ
  split
  · rfl
  · split <;> rfl

/-! ## 8. Denotation of the new blocks against `runBlock` -/

/-- Running the lowered `SAR` block leaves `dst` holding the `x86_SAR`-shifted
    source word: the `.word` of `x86_SAR` applied to the post-`mov` destination
    word and the immediate count. -/
theorem lowerLinstrExtCov2_sar_denote (dst : String) (src : JOperand) (n : Nat)
    (s : JState 64) :
    (runBlock s [JInstr.mov dst src, JInstr.sar dst (JOperand.imm n)]).get dst
      = (x86_SAR ((s.setReg dst (x86_MOV (src.eval s))).get dst)
          ((JOperand.imm n).eval (s.setReg dst (x86_MOV (src.eval s))))).word := by
  simp only [runBlock, evalInstr, JState.get_writeB5W_same]

/-- `test r, r` leaves every register unchanged: it writes flags only. -/
theorem test_self_get {w : Nat} (s : JState w) (cn r : String) :
    (evalInstr s (JInstr.test cn (.reg cn))).get r = s.get r := rfl

/-- `test r, r` sets `ZF` from the tested register. -/
theorem test_self_zf {w : Nat} (s : JState w) (cn : String) :
    (evalInstr s (JInstr.test cn (.reg cn))).flagB (·.zf) = decide (s.get cn = 0#w) := by
  simp only [evalInstr, x86_TEST, rflags_of_bwop, JState.flagB, JState.writeB5_flags,
    Option.getD_some, ZF_of_word, BitVec.and_self, JOperand.eval]
  congr 1
  simp [BitVec.toNat_eq]

/-- Reading the destination of a `cmovne`. -/
theorem cmovne_get_dst {w : Nat} (s : JState w) (dst tn : String) :
    (evalInstr s (JInstr.cmovne dst (.reg tn))).get dst
      = x86_CMOVcc (! s.flagB (·.zf)) (s.get tn) (s.get dst) := by
  simp [evalInstr, JState.setReg, JState.get]

/-- Reading the destination of a register `mov`. -/
theorem mov_get_dst {w : Nat} (s : JState w) (dst fn : String) :
    (evalInstr s (JInstr.mov dst (.reg fn))).get dst = s.get fn := by
  simp [evalInstr, x86_MOV, JState.setReg, JState.get]

/-- Reading any other register across a `mov`. -/
theorem mov_get_other {w : Nat} (s : JState w) (dst fn r : String) (h : r ≠ dst) :
    (evalInstr s (JInstr.mov dst (.reg fn))).get r = s.get r := by
  simp [evalInstr, x86_MOV, JState.setReg, JState.get, h]

/-- **Select denotation.** With the condition, true-value and false-value
    registers all distinct from the destination, the lowered block leaves `dst`
    holding the true value when the condition register is nonzero and the false
    value otherwise — the data effect of `selectW` on a `0`/`1` condition. -/
theorem lowerCmovJ_denote (s : JState 64) (dst cn tn fn : String)
    (hc : cn ≠ dst) (ht : tn ≠ dst) (hf : fn ≠ dst) :
    (runBlock s (lowerCmovJ dst cn tn fn)).get dst
      = if s.get cn = 0#64 then s.get fn else s.get tn := by
  have ht' : (tn == dst) = false := by simp [ht]
  have hf' : (fn == dst) = false := by simp [hf]
  simp only [lowerCmovJ, ht', hf', if_false, Bool.false_eq_true, List.cons_append,
    List.nil_append, runBlock]
  -- after `mov dst fn` the destination holds `fn`; `test cn cn` changes no
  -- register and sets `ZF` from `cn`; the `cmovne` then selects.
  rw [cmovne_get_dst, test_self_zf, test_self_get, test_self_get,
    mov_get_other s dst fn cn hc, mov_get_other s dst fn tn ht, mov_get_dst]
  by_cases h : s.get cn = 0#64 <;> simp [x86_CMOVcc]

/-! ## 9. Worked shapes

`demoSar63` is the `>> 63` sign-extract binding an ML-DSA `decompose` emits
(`sarImm 64 63`); `demoCmov` is a `select 64` binding over three distinct
registers. `lowerLinstrExt`, `lowerLinstrExt2` and `lowerLinstrExtCov` all drop
both to `none`. -/

/-- An arithmetic-right-shift binding `t := v >>ₐ 63` (sign-extract). -/
def demoSar63 : LinstrR := .Lopn [.reg "t"] "SAR:63:64" [.reg "v"]

/-- The coverage superset lowers `demoSar63` to a two-address `mov; sar`. -/
theorem demoSar63_cov :
    lowerLinstrExtCov2 demoSar63
      = some [JInstr.mov "t" (.reg "v"), JInstr.sar "t" (JOperand.imm 63)] := rfl

/-- The demo `SAR` block is `allDirect`. -/
theorem demoSar63_allDirect :
    allDirect [JInstr.mov "t" (.reg "v"), (JInstr.sar "t" (JOperand.imm 63) : JInstr 64)] = true := by
  decide

/-- Running the lowered `demoSar63` from a state whose source `v` has its sign
    bit set (`v = 2^63`) leaves `t` holding the all-ones sign mask. -/
theorem demoSar63_effect :
    (runBlock ({ regs := fun x => if x = "v" then (1 <<< 63 : BitVec 64) else 0 }
        : JState 64) [JInstr.mov "t" (.reg "v"), JInstr.sar "t" (JOperand.imm 63)]).get "t"
      = (-1 : BitVec 64) := by
  decide

/-- A constant-time select binding `d := if c ≠ 0 then a else b`. -/
def demoCmov : LinstrR := .Lopn [.reg "d"] "CMOV:64" [.reg "c", .reg "a", .reg "b"]

/-- The coverage superset lowers `demoCmov` to `mov; and; cmovne`. -/
theorem demoCmov_cov :
    lowerLinstrExtCov2 demoCmov
      = some [JInstr.mov "d" (.reg "b"), JInstr.test "c" (.reg "c"),
              JInstr.cmovne "d" (.reg "a")] := rfl

/-- The demo select block is `allDirect`. -/
theorem demoCmov_allDirect :
    allDirect [JInstr.mov "d" (.reg "b"), JInstr.test "c" (.reg "c"),
               (JInstr.cmovne "d" (.reg "a") : JInstr 64)] = true := by
  decide

/-- Running the lowered `demoCmov` with the condition register set picks the
    true value. -/
theorem demoCmov_effect_true :
    (runBlock ({ regs := fun x => if x = "c" then 1 else if x = "a" then 7 else 9 }
        : JState 64) [JInstr.mov "d" (.reg "b"), JInstr.test "c" (.reg "c"),
                      JInstr.cmovne "d" (.reg "a")]).get "d" = 7 := by
  decide

/-- And with the condition register clear it picks the false value. -/
theorem demoCmov_effect_false :
    (runBlock ({ regs := fun x => if x = "c" then 0 else if x = "a" then 7 else 9 }
        : JState 64) [JInstr.mov "d" (.reg "b"), JInstr.test "c" (.reg "c"),
                      JInstr.cmovne "d" (.reg "a")]).get "d" = 9 := by
  decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar
