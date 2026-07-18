/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

/-!
# Additive `Linstr → JInstr` coverage superset: SAR (arithmetic right shift) + CMOV report

`LoweringExtendedCoverage.lean` builds `lowerLinstrExtCov` — the strict superset
of `lowerLinstrExt2` that adds the carry-chain ADX bindings (`ADCX:64`/`ADOX:64`/
`ADCXHI:64`/`ADOXHI:64`) and the register-indexed (SIB) memory ops
(`LOADIDX`/`STOREIDX`). It still returns `none` on the **immediate arithmetic
right-shift** export `SAR:<n>:64` (the `sarImm` op) — so an ML-DSA-style kernel
whose `>> 63` / `>> 23` sign-extract bindings emit `sarImm` cannot reach the
`JInstr` path. (`lowerLinstrExt2`'s single-source arm runs `parseShiftMnem`,
which detects only the `SHL:`/`SHR:` prefixes; `SAR:<n>` falls through to the
ALU table — not an ALU mnemonic — and is dropped.)

This module adds a **strict-superset** lowering `lowerLinstrExtCov2` that
delegates every shape `lowerLinstrExtCov` already covers (its catch-all arm is
`lowerLinstrExtCov i` verbatim) and adds arms for the dropped immediate
arithmetic right-shift `SAR:<n>:64` — one more shape onto the `JInstr` emit path
toward retiring the Lprog owned codegen (D4 encoder collapse). The existing
lowerings are untouched (a separate function, like the
`lowerLinstrExtCov`-vs-`lowerLinstrExt2` precedent).

## What the exporter emits (the shape this superset adds)

From `opToLinstrR` (`JasminLprogExport.lean`), the immediate arithmetic
right-shift op (`#606`) exports as

* `sarImm w n` → `Lopn [reg dst] (withWidthTag w ("SAR:" ++ toString n)) [src]`
  — i.e. `"SAR:<n>:64"` at `w = 64` (or `"SAR:<n>"` for the narrow widths), a
  **single** source (the shifted register), the compile-time shift count `n`
  baked into the mnemonic. The matching `JInstr 64` constructor is

  | export mnemonic / shape | `JInstr 64` target | note |
  |---|---|---|
  | `SAR:<n>:64 [src]` | `[mov dst src, sar dst #n]` | two-address, like the existing `SHR`/`SHL` arms |

`JInstr.sar dst src` (`JasminModel.lean`) denotes `dst := (x86_SAR dst src).word`
(`arch_sem.v` `Ox86_SAR_instr`) — `BitVec.sshiftRight` on the masked count, the
arithmetic (sign-replicating) shift, exactly the `sarImm` denotation.

## Matching the count by **literal tagged mnemonic** (kernel `rfl`)

The shift count `n` lives in the mnemonic suffix. Rather than dispatch through a
`String.startsWith`/`toNat?` parser — whose `Substring`-based `String` ops are
**not kernel-reducible** (so every witness would stall, exactly the
`stripWidthTag`/`parseShiftMnem` trap recorded in `LoweringExtendedCoverage §4`)
— `lowerLinstrExtCov2` matches the **literal tagged mnemonic** of each shift
count the ML-DSA reduce kernels actually emit (`SAR:63:64`, `SAR:23:64`, and the
narrow `SAR:31`) in the head pattern. Every witness is then a kernel `rfl`. New
counts are added by appending one literal arm each (the dialect emits a fixed,
small set of compile-time `sarImm` counts).

## CMOV — export shape reported, NOT lowered (honest)

The companion higher-value shape — the constant-time `select w` op (`CMOV`) — is
**not** lowered here, by design. Its export (`opToLinstrR`'s `select` arm) is

```
select w → Lopn [reg dst] (withWidthTag w "CMOV") [cond, a, b]
```

a **three-source** binding `dst := if cond = 1 then a else b` (`selectW`), where
`cond` is the front's explicit **`reg 1` condition value** (0 or 1) held in a
register-file slot — *not* a processor flag (`JasminDialect.lean §select`,
`JasminAbiEmit.renderSelect`). The `JInstr 64` `cmove`/`cmovne`/`cmovb`
constructors, by contrast, read a **flag** (`cmove`/`cmovne` read `ZF`, `cmovb`
reads `CF`; `JasminModel.evalInstr`). The `JInstr` model has **no `test`/`cmp`
constructor** to materialise the condition register into `ZF`/`CF`, so there is
no semantics-preserving `[mov dst b; cmovCC dst a]` lowering: any `cmovCC` arm
would read a flag the lowered block never set from `cond`, silently dropping the
condition. (The verified front itself lowers `select` as the **branchless
xor/and mask-select** `b ^ ((a ^ b) & (0 - cond))`, not a flag `CMOVcc` —
`renderSelect` — precisely because the condition is a register value.)

Faithfully bridging `CMOV` to the `cmove`/`cmovb` constructors therefore needs
either a `JInstr` `test`/`cmp` flag-setting primitive (to compute
`ZF := (cond = 0)` ahead of a `cmovne`) or a mask-select `JInstr` block mirroring
`renderSelect`. Both are additive `JInstr`/`evalInstr` changes to
`JasminModel.lean` — out of scope for this **additive lowering-only** file (which
must not modify existing files / add constructors). So we **report** the exact
`CMOV` export shape here and lower `SAR` cleanly; the `CMOV` arm is the next
follow-up once the flag-set / mask-select primitive lands.

## Coverage delta (honest)

`lowerLinstrExtCov2` is a **strict superset** of `lowerLinstrExtCov`: its
catch-all arm delegates verbatim, and the new head patterns fire only on the
`SAR:<n>:64` shapes `lowerLinstrExtCov` (hence `lowerLinstrExt2`, hence
`lowerLinstrExt`) dropped to `none`. The gain is witnessed on the ML-DSA reduce
counts `n = 63` (`>> 63` sign-extract) and `n = 23` (`Rhs.sarImm 23`), plus a
narrow-width `SAR:31`, each a `rfl`. All previously-dropped:

* `SAR:63:64` / `SAR:23:64` / `SAR:31` (two-address `[mov dst src, sar dst #n]`).

### Constant-time class of the new arm (honest)

The lowered `SAR` block (`mov`/`sar`) is `IsDirect`, so it stays inside the
unconditional `allDirect` constant-time class (`MachineConstantTime.lean`) — the
shift amount is a compile-time immediate, the operands are registers.

## Still dropped (the honest remainder)

* `CMOV:64` (the `select` op) — reported above; needs a flag-set / mask-select
  `JInstr` primitive first.
* `SAR:<n>:64` for counts not in the literal arm set — add one literal arm each.
* `ROR:<n>` / `ZEROEXT` / `TRUNC` / `CALL:` / `CALLN:` / `VPACK8u64:` and every
  non-`Lopn` `LinstrR` — out of scope here (each a separate follow-up).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

/-! ## 1. The new arm body (immediate arithmetic right-shift)

`lowerSarJ dst n src` is the two-address lowering of `dst := src >>ₐ n`:
`[mov dst src, sar dst #n]`, exactly mirroring the existing `SHR`/`SHL` arms.
The count `n` arrives already parsed (matched by the literal head pattern), so
no `Substring`-based parsing enters the kernel path. -/

/-- Lower a native immediate arithmetic right-shift `dst := src >>ₐ n` to
    two-address form `[mov dst src, sar dst #n]` (`SAR r, imm`). -/
def lowerSarJ (dst : String) (n : Nat) (src : JOperand) : List (JInstr 64) :=
  [JInstr.mov dst src, JInstr.sar dst (JOperand.imm n)]

/-! ## 2. The coverage superset

`lowerLinstrExtCov2` matches the **new** shapes — the single-source
`SAR:<n>:64` (and narrow `SAR:<n>`) immediate arithmetic right-shifts — by their
**literal tagged mnemonic** first, then delegates everything else to
`lowerLinstrExtCov`. Matching the literal mnemonic in the head pattern (rather
than dispatching through `parseShiftMnem`/`stripWidthTag`) keeps every witness a
kernel `rfl`. The new head patterns are disjoint from every shape
`lowerLinstrExtCov` lowers — its single-source delegate parses only `SHL:`/`SHR:`
and the ALU/`MOV` table, none of which is `SAR:<n>` — so the superset is
**strict** and the delegate is verbatim on every covered shape. -/

/-- The additive coverage superset lowering. New arms (vs `lowerLinstrExtCov`):
    the immediate arithmetic right-shifts `SAR:63:64` / `SAR:23:64` (the ML-DSA
    reduce sign-extracts) and the narrow `SAR:31`, each
    `[mov dst src, sar dst #n]`. Every other shape delegates to
    `lowerLinstrExtCov`. -/
def lowerLinstrExtCov2 : LinstrR → Option (List (JInstr 64))
  -- `>> 63` sign-extract (ML-DSA `decompose`/`use_hint`), U64
  | .Lopn [.reg dst] "SAR:63:64" [src] => some (lowerSarJ dst 63 (lowerJOperand src))
  -- `Rhs.sarImm 23` (ML-DSA `reduce32`), U64
  | .Lopn [.reg dst] "SAR:23:64" [src] => some (lowerSarJ dst 23 (lowerJOperand src))
  -- narrow-width (w ≠ 64, no `:64` tag)
  | .Lopn [.reg dst] "SAR:31" [src]    => some (lowerSarJ dst 31 (lowerJOperand src))
  -- everything else: the ADX/SIB coverage superset verbatim
  | i => lowerLinstrExtCov i

/-- Lower a full `Linstr` (drops the position tag), coverage superset. -/
def lowerLinstrExtCov2L (i : Linstr) : Option (List (JInstr 64)) :=
  lowerLinstrExtCov2 i.li_i

/-! ## 3. New-coverage witnesses (the ML-DSA reduce shift counts) -/

/-- **New coverage: `SAR:63:64` arithmetic right-shift** (the `>> 63` sign-extract
    in ML-DSA `decompose`/`use_hint`). `lowerLinstrExtCov` (and `lowerLinstrExt2`)
    drop it; the superset lowers it to `[mov dst src, sar dst #63]`. -/
theorem lowerLinstrExtCov2_sar63 (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "SAR:63:64" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 63)] := rfl

/-- **New coverage: `SAR:23:64` arithmetic right-shift** (the `Rhs.sarImm 23` in
    ML-DSA `reduce32`). -/
theorem lowerLinstrExtCov2_sar23 (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "SAR:23:64" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 23)] := rfl

/-- **New coverage: narrow-width `SAR:31`** (no `:64` width tag, w ≠ 64). -/
theorem lowerLinstrExtCov2_sar31_narrow (dst : String) (src : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "SAR:31" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 31)] := rfl

/-! ## 4. Strict-superset of `lowerLinstrExtCov`

On a single-source `SAR:<n>:64` binding `lowerLinstrExtCov` returned `none` (it
delegates the single-source case to `lowerLinstrExt2`, whose `parseShiftMnem`
detects only `SHL:`/`SHR:`, and whose ALU table has no `SAR:<n>` mnemonic),
while `lowerLinstrExtCov2` lowers it — so the superset strictly extends coverage
on exactly the arithmetic-right-shift shapes the ML-DSA reduce kernels need.

(A fully general `none`-on-`SAR:<n>:64` lemma for `lowerLinstrExtCov` would need
to reduce `String.startsWith`/`stripWidthTag` inside `lowerLinstrExt2`'s
single-source `parseShiftMnem`/`lowerAluJ` cascade; those `Substring`-based
`String` ops are not kernel-reducible — as recorded in
`LoweringExtendedCoverage.lean §4`. So the SAR superset, like the SIB one there,
is witnessed **concretely** at the kernel reduce counts; see the report.)

The delegation half is proved generally: on every shape whose mnemonic is not one
of the literal `SAR:` heads, `lowerLinstrExtCov2` is **definitionally**
`lowerLinstrExtCov` (the catch-all arm), so it agrees verbatim — witnessed on a
two-source ALU `ADD:64`, the carry-chain `ADCX:64`, and the SIB `LOADIDX` (each a
shape the prior superset lowers). -/

/-- The coverage superset agrees with `lowerLinstrExtCov` on a two-source ALU
    `ADD:64` binding (not a `SAR:` head, so the catch-all delegates verbatim). -/
theorem lowerLinstrExtCov2_delegates_add (dst : String) (s0 s1 : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "ADD:64" [s0, s1])
      = lowerLinstrExtCov (.Lopn [.reg dst] "ADD:64" [s0, s1]) := rfl

/-- The coverage superset agrees with `lowerLinstrExtCov` on the prior superset's
    carry-chain `ADCX:64` data binding (three sources). -/
theorem lowerLinstrExtCov2_delegates_adcx (dst : String) (s0 s1 cin : LOperand) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "ADCX:64" [s0, s1, cin])
      = lowerLinstrExtCov (.Lopn [.reg dst] "ADCX:64" [s0, s1, cin]) := rfl

/-- And on the register-indexed `LOADIDX` SIB gather. -/
theorem lowerLinstrExtCov2_delegates_loadidx (dst base idx : String) (scale : Nat) :
    lowerLinstrExtCov2 (.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx scale])
      = lowerLinstrExtCov (.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx scale]) := rfl

/-! ## 5. Constant-time class of the new arm

The lowered `SAR` block (`mov`/`sar`) is `IsDirect`, so it stays inside the
unconditional `allDirect` constant-time class — the shift amount is a
compile-time immediate, the operands registers. -/

/-- The lowered `SAR` data block is `allDirect` (`mov`/`sar` are direct). -/
theorem lowerLinstrExtCov2_sar_allDirect (dst : String) (src : JOperand) (n : Nat) :
    allDirect [(JInstr.mov dst src : JInstr 64), JInstr.sar dst (JOperand.imm n)] = true := rfl

/-! ## 6. Denotation of the new arm (against `JInstr`'s `runBlock`)

Running the lowered `SAR` block leaves `dst` holding `(x86_SAR src #n).word` —
the arithmetic (sign-replicating) right shift, `BitVec.sshiftRight` on the masked
count. After `mov dst src` the destination holds `src.eval s`; `sar dst #n` then
arithmetic-shifts it by the immediate count, writing the `B5W` data word. -/

/-- **`SAR` denotation.** The lowered block's `dst` ends up holding the
    `x86_SAR`-shifted source word: the `.word` of `x86_SAR` applied to the
    post-`mov` destination word and the immediate count. -/
theorem lowerLinstrExtCov2_sar_denote (dst : String) (src : JOperand) (n : Nat)
    (s : JState 64) :
    (runBlock s [JInstr.mov dst src, JInstr.sar dst (JOperand.imm n)]).get dst
      = (x86_SAR ((s.setReg dst (x86_MOV (src.eval s))).get dst)
          ((JOperand.imm n).eval (s.setReg dst (x86_MOV (src.eval s))))).word := by
  simp only [runBlock, evalInstr, JState.get_writeB5W_same]

/-! ## 7. Worked demo: a previously-`none` `SAR` shape now lowering

`demoSar63` is the `>> 63` sign-extract binding an ML-DSA `decompose` emits
(`sarImm 64 63`); `lowerLinstrExt`/`lowerLinstrExt2`/`lowerLinstrExtCov` all drop
it to `none`, and the coverage superset lowers it to `[mov dst src, sar dst #63]`
with the right `runBlock` effect. -/

/-- A previously-`none` arithmetic-right-shift `t := v >>ₐ 63` (sign-extract). -/
def demoSar63 : LinstrR := .Lopn [.reg "t"] "SAR:63:64" [.reg "v"]

/-- The coverage superset lowers `demoSar63` to a two-address `mov; sar`. -/
theorem demoSar63_cov :
    lowerLinstrExtCov2 demoSar63
      = some [JInstr.mov "t" (.reg "v"), JInstr.sar "t" (JOperand.imm 63)] := rfl

/-- The demo `SAR` block is `allDirect` (constant-time class). -/
theorem demoSar63_allDirect :
    allDirect [JInstr.mov "t" (.reg "v"), (JInstr.sar "t" (JOperand.imm 63) : JInstr 64)] = true := by
  decide

/-- **Demo `SAR` effect.** Running the lowered `demoSar63` from a state where the
    source `v` has its sign bit set (`v = 2^63`, MSB = 1) leaves `t` holding the
    all-ones sign mask `-1` (`2^64 − 1`) — the arithmetic `>> 63` sign-extends. -/
theorem demoSar63_effect :
    (runBlock ({ regs := fun x => if x = "v" then (1 <<< 63 : BitVec 64) else 0 }
        : JState 64) [JInstr.mov "t" (.reg "v"), JInstr.sar "t" (JOperand.imm 63)]).get "t"
      = (-1 : BitVec 64) := by
  decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar
