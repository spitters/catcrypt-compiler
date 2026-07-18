/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

/-!
# Additive `Linstr → JInstr` coverage superset: mem-folded `MULX` + `.rodata` symbol load

`LoweringExtendedCoverage.lean` builds `lowerLinstrExtCov`, the supported-op
superset that adds the carry-chain ADX bindings (`ADCX:64`/`ADOX:64`/…) and the
register-indexed (SIB) memory ops (`LOADIDX`/`STOREIDX`). Its honest remainder
(`§"Still dropped"`) listed two further shapes the `JInstr 64` model already has
constructors for but the lowering did **not** cover:

* `mulxMem` — the memory-folded `MULX` (`mulxq off(%base), %lo, %hi`), s2n-bignum's
  fold of the multiplicand load into the widening multiply;
* `loadSym` — the RIP-relative `.rodata` symbol-base load (`leaq sym(%rip), %dst`),
  the NTT twiddle-table base primitive.

This module adds `lowerLinstrExtCovMS`, a **strict superset** of
`lowerLinstrExtCov` (its catch-all arm delegates verbatim) with the two new
forward-compatible arms — the encoder-maturation step toward the `JInstr` path
covering the s2n-bignum / NTT kernels that fold a load into the multiply or read
a `.rodata` table (D4 encoder collapse). The existing lowerings are untouched.

## CRITICAL HONESTY: the exporter does NOT currently emit these as `Lopn`

The deliberate, verified finding (the point of this module): **`opToLinstrR`
(`JasminLprogExport.lean`) emits no `MULXMEM`/`LOADSYM`/`LEASYM` mnemonic, and
the `JasminOp` dialect (`JasminDialect.lean`) has no op that would produce one.**
Specifically:

* The widening multiply lives in the dialect only as `mulhi w` — a **register-
  register** high-word op (two `reg w` operands), exported as
  `Lopn [.reg dst] "MULXHI:64" [s0, s1]` (and already covered by
  `lowerLinstrExtCov` → reg-`mulx`). There is **no** `JasminOp` whose second
  source is a memory cell, so `opToLinstrR` never builds a mem-folded `MULX`
  `Lopn`. The exporter *splits* the multiplicand load (a separate `stackLoad` →
  `LOAD`/`LOADIDX`) from the reg-`MULX`.
* There is **no** `.rodata`-symbol / global-table `JasminOp` at all. `lp_globs`
  / `lp_glob_names` (the read-only data section) are emitted **empty** by
  `Com.toLprog`, and no op renders a `leaq sym(%rip)` shape. The symbol-base load
  has no `Lopn` source.

So for both shapes **there is currently no `Linstr` to lower** — the gap is
**dialect/exporter-side** (a missing `JasminOp` + its `opToLinstrR` arm), not
lowering-side. The `JInstr.mulxMem` / `JInstr.loadSym` constructors exist for the
day the exporter *folds* these; until then:

* `mulxMem`: the kernels that fold a load into the multiply **already swap onto
  the `JInstr` path via the split form** — `LOAD`/`LOADIDX` (covered:
  `lowerLinstrExt`'s `LOAD` arm / `lowerLinstrExtCov`'s `LOADIDX` arm) followed by
  the reg-`MULXHI:64` (covered). The mem-fold is a *peephole* (`load; mulx` →
  `mulxq mem`) that would tighten the emitted asm to match s2n-bignum's hand
  code, **not** a coverage gap: the split form is already fully `JInstr`-coverable.
* `loadSym`: there is no split-form fallback — a `.rodata` table read has no
  current `Com[jasminDialect]` image at all (no global-table op), so these
  kernels do **not** yet reach the `JInstr` path by any route. Closing it needs a
  new dialect op (a `globalBase`/`symLea` `JasminOp`) + its `opToLinstrR` arm +
  populated `lp_globs`, *then* this lowering arm fires.

## What this module provides

Even though the exporter does not yet emit them, the lowering arms are real and
exercised: they fire on the **forward-compatible** mnemonics `MULXMEM` /
`LOADSYM` that a future `opToLinstrR` arm would produce (the shapes documented
below), each witnessed by a kernel `rfl` and a `runBlock` denotation against the
`JInstr` semantics. So when the exporter learns to fold these, the `JInstr`
lowering is already in place and proven; the only remaining work is the dialect
op + exporter arm.

### Forward-compatible `Linstr` shapes this superset adds

| would-be export shape | `JInstr 64` target | note |
|---|---|---|
| `MULXMEM [a, .reg base, .imm off]`, dsts `[.reg dHi, .reg dLo]` | `mulxMem dHi dLo a base off` | mem-folded widening multiply |
| `LOADSYM [.reg sym]`, dsts `[.reg dst]`                          | `loadSym dst sym`           | `.rodata` symbol-base `lea`  |

Both are **disjoint** from every shape `lowerLinstrExtCov` lowers: the mem-folded
`MULX` is a **two-destination** `Lopn` (no covered shape has two `lexprs`), and
`LOADSYM` is its own (currently un-emitted) mnemonic. So the superset is strict
and the delegate is verbatim on every covered shape.

### Constant-time class (honest)

`mulxMem` reads a **compile-time-displacement** memory operand
(`off(%base)` — a fixed offset, like `loadMem`), so it is `IsDirect`: its address
is data-independent. `loadSym` reads a **fixed symbol address** (`sym(%rip)` — a
link-time constant), so it too is `IsDirect`. Both therefore stay inside the
unconditional `allDirect` constant-time class — unlike the SIB `LOADIDX`/
`STOREIDX` arms of `lowerLinstrExtCov`, whose register-indexed address is *not*
`IsDirect`. (A `loadMemIdx _ sym i scale` *gather* off a `loadSym` base would have
a register-dependent index; that is the SIB-CT story, separate from the symbol-
base `lea` itself.)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageMulxMemSym

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

/-! ## 1. The new arm bodies (mem-folded `MULX` + symbol-base load) -/

/-- Lower a mem-folded `MULX` `MULXMEM [a, .reg base, .imm off]` (dsts
    `[.reg dstHi, .reg dstLo]`), i.e. `mulxq off(%base), %dstLo, %dstHi`, to the
    `JInstr.mulxMem` constructor. `a` is the `%rdx`-pinned multiplier (lowered as a
    `JOperand`), `base`/`off` are the memory operand of the second multiplicand. -/
def lowerMulxMemJ (dstHi dstLo : String) (a : JOperand) (base : String) (off : Int) :
    JInstr 64 :=
  .mulxMem dstHi dstLo a base off

/-- Lower a `.rodata` symbol-base load `LOADSYM [.reg sym]` (dst `[.reg dst]`),
    i.e. `leaq sym(%rip), %dst`, to the `JInstr.loadSym` constructor. -/
def lowerLoadSymJ (dst sym : String) : JInstr 64 :=
  .loadSym dst sym

/-! ## 2. The coverage superset

`lowerLinstrExtCovMS` matches the two **new** shapes by their literal tagged
mnemonic (`MULXMEM` on a two-destination `Lopn`; `LOADSYM` on a single-symbol
source), then delegates everything else to `lowerLinstrExtCov`. Matching the
literal mnemonic in the head pattern keeps every witness a kernel `rfl`. The new
head patterns are disjoint from every shape `lowerLinstrExtCov` lowers (a
two-destination `Lopn` is matched by none of its arms — they all have a single
`[.reg dst]` destination — and `LOADSYM` is its own mnemonic), so the superset is
strict and the delegate is verbatim on every covered shape. -/

/-- The additive coverage superset lowering. New arms (vs `lowerLinstrExtCov`):
    the mem-folded widening multiply `MULXMEM` and the `.rodata` symbol-base load
    `LOADSYM`. Every other shape delegates to `lowerLinstrExtCov` (hence to the
    full `lowerLinstrExt2`/`lowerLinstrExt` chain). -/
def lowerLinstrExtCovMS : LinstrR → Option (List (JInstr 64))
  -- mem-folded widening multiply `mulxq off(%base), %dstLo, %dstHi`
  | .Lopn [.reg dstHi, .reg dstLo] "MULXMEM" [a, .reg base, .imm off] =>
      some [lowerMulxMemJ dstHi dstLo (lowerJOperand a) base (Int.ofNat off)]
  -- `.rodata` symbol-base load `leaq sym(%rip), %dst`
  | .Lopn [.reg dst] "LOADSYM" [.reg sym] =>
      some [lowerLoadSymJ dst sym]
  -- everything else: the carry-chain/SIB coverage superset verbatim
  | i => lowerLinstrExtCov i

/-- Lower a full `Linstr` (drops the position tag), coverage superset. -/
def lowerLinstrExtCovMSL (i : Linstr) : Option (List (JInstr 64)) :=
  lowerLinstrExtCovMS i.li_i

/-! ## 3. New-coverage witnesses -/

/-- **New coverage: mem-folded `MULXMEM`** → `mulxMem`. (`lowerLinstrExtCov`,
    `lowerLinstrExt2`, and `lowerLinstrExt` all drop the two-destination shape.) -/
theorem lowerLinstrExtCovMS_mulxmem (dstHi dstLo base : String) (a : LOperand)
    (off : Nat) :
    lowerLinstrExtCovMS (.Lopn [.reg dstHi, .reg dstLo] "MULXMEM"
        [a, .reg base, .imm off])
      = some [JInstr.mulxMem dstHi dstLo (lowerJOperand a) base (Int.ofNat off)] := rfl

/-- **New coverage: `.rodata` symbol-base `LOADSYM`** → `loadSym`. -/
theorem lowerLinstrExtCovMS_loadsym (dst sym : String) :
    lowerLinstrExtCovMS (.Lopn [.reg dst] "LOADSYM" [.reg sym])
      = some [JInstr.loadSym dst sym] := rfl

/-! ## 4. Strict-superset of `lowerLinstrExtCov`

The new head patterns never intercept a shape `lowerLinstrExtCov` already
lowered. The `MULXMEM` arm is witnessed **structurally**: a **two-destination**
`Lopn` matches none of `lowerLinstrExtCov`'s arms (every one of them — and every
arm of the delegated `lowerLinstrExt2`/`lowerLinstrExt` — has a single
`[.reg dst]` destination list), so it returned `none` there;
`covMS_two_dst_none` proves this by destination-list structure alone (no string
reduction). The `LOADSYM` shape is witnessed **concretely** by `demoLoadSym_cov`
(`rfl`): its literal-mnemonic head pattern matches before the delegate.

(A fully general `none`-on-`LOADSYM` lemma would need to reduce the
`Substring`-based `String.endsWith`/`startsWith` inside `lowerLinstrExtCov`'s
single-source arms; those `String` ops are not kernel-reducible — `decide`/`rfl`/
`simp` all get stuck — and `native_decide` is out of policy. So the `LOADSYM`
superset is stated concretely, the `MULXMEM` superset generally; cf. the SIB
treatment in `LoweringExtendedCoverage.lean §4`.) -/

/-- `lowerLinstrExtCov` drops **any** two-destination `Lopn` (regardless of
    mnemonic): its arms — and every arm of the `lowerLinstrExt2`/`lowerLinstrExt`
    chain it delegates to — match only a single-`[.reg dst]` destination list.
    Proved by destination-list structure — no string reduction. -/
theorem covMS_two_dst_none (d0 d1 : LOperand) (opn : String) (srcs : List LOperand) :
    lowerLinstrExtCov (.Lopn [d0, d1] opn srcs) = none := by
  simp only [lowerLinstrExtCov, lowerLinstrExt2, lowerLinstrExt]

/-- **Strict superset on the mem-folded `MULX` arm.** On a two-destination
    `MULXMEM` binding, `lowerLinstrExtCov` returned `none` (two destinations),
    while `lowerLinstrExtCovMS` lowers it — so the superset strictly extends
    coverage on exactly the mem-folded-multiply shape an s2n-bignum kernel would
    use. (The hypothesis is vacuous: `lowerLinstrExtCov` never lowers a
    two-destination shape.) -/
theorem lowerLinstrExtCovMS_strict_mulxmem (dstHi dstLo : String) (opn : String)
    (srcs : List LOperand) (b : List (JInstr 64))
    (h : lowerLinstrExtCov (.Lopn [.reg dstHi, .reg dstLo] opn srcs) = some b) :
    False := by
  rw [covMS_two_dst_none] at h; exact absurd h (by simp)

/-! ## 5. Constant-time class of the new arms

Both new arms have a **data-independent** effective address — `mulxMem`'s is a
fixed `off(%base)` displacement, `loadSym`'s is a fixed `sym(%rip)` link-time
address — so both are `IsDirect` and stay inside the unconditional `allDirect`
constant-time class (unlike the register-indexed SIB arms of
`lowerLinstrExtCov`). -/

/-- The lowered mem-folded `MULX` is `allDirect` (fixed-displacement address). -/
theorem lowerLinstrExtCovMS_mulxmem_allDirect (dstHi dstLo base : String)
    (a : JOperand) (off : Int) :
    allDirect [(JInstr.mulxMem dstHi dstLo a base off : JInstr 64)] = true := rfl

/-- The lowered symbol-base load is `allDirect` (fixed `.rodata` address). -/
theorem lowerLinstrExtCovMS_loadsym_allDirect (dst sym : String) :
    allDirect [(JInstr.loadSym dst sym : JInstr 64)] = true := rfl

/-! ## 6. Denotation of the new arms (against `JInstr`'s `runBlock`) -/

/-- **`MULXMEM` denotation.** Running the lowered mem-folded `MULX` leaves
    `dstLo`/`dstHi` holding the low/high words of the widening multiply
    `a * [base + off]`: the second multiplicand is read straight from memory
    (`s.load base off`), then the same `x86_MULX_lo_hi` as the reg form. We expose
    the low word on `dstLo` (assuming `dstHi ≠ dstLo`, the usual two-output
    register pair). -/
theorem lowerLinstrExtCovMS_mulxmem_denote_lo (dstHi dstLo base : String)
    (a : JOperand) (off : Int) (s : JState 64) (h : dstHi ≠ dstLo) :
    (runBlock s [JInstr.mulxMem dstHi dstLo a base off]).get dstLo
      = (x86_MULX_lo_hi (a.eval s) (s.load base off)).1 := by
  simp only [runBlock, evalInstr]
  rw [JState.get_setReg_other _ _ _ _ h.symm, JState.get_setReg_same]

/-- **`MULXMEM` denotation (high word).** `dstHi` holds the high word. -/
theorem lowerLinstrExtCovMS_mulxmem_denote_hi (dstHi dstLo base : String)
    (a : JOperand) (off : Int) (s : JState 64) :
    (runBlock s [JInstr.mulxMem dstHi dstLo a base off]).get dstHi
      = (x86_MULX_lo_hi (a.eval s) (s.load base off)).2 := by
  simp only [runBlock, evalInstr, JState.get_setReg_same]

/-- **`LOADSYM` denotation.** After `leaq sym(%rip), %dst`, a subsequent indexed
    gather keyed by the base register *name* `dst` reads the `.rodata` table
    `sym`: `loadIdx dst i scale` on the post-`loadSym` state equals `s.mem sym
    (scale·i)` — i.e. `sym[i]` (the model aliases `dst`'s memory bank onto
    `sym`'s). This is the table-access contract the NTT twiddle gather relies on. -/
theorem lowerLinstrExtCovMS_loadsym_denote (dst sym idx : String) (scale : Nat)
    (s : JState 64) (hne : idx ≠ dst) :
    (runBlock s [JInstr.loadSym dst sym]).loadIdx dst idx scale
      = s.mem sym (scale * (s.get idx).toNat) := by
  simp only [runBlock, evalInstr, JState.loadIdx, JState.load, JState.get, if_true]
  rw [if_neg hne]

/-! ## 7. Worked demo: forward-compatible shapes lowering

`demoMulxMem` is the mem-folded widening multiply `(hi, lo) := a * [b + 16]` an
s2n-bignum `mulxq 16(%rbx), %lo, %hi` would export to; `demoLoadSym` is the
`.rodata` table-base `leaq twiddles(%rip), %t` an NTT gather would export to.
Both are dropped by `lowerLinstrExtCov` (two destinations / un-emitted mnemonic);
`lowerLinstrExtCovMS` lowers them, with the right `runBlock` effect. The `_cov`
facts (each `rfl`) are the strict-superset witnesses. NOTE (honest): the exporter
does **not** currently emit either mnemonic (see the module header) — these demos
exercise the *forward-compatible* shapes a future `opToLinstrR` arm would
produce, so the `JInstr` lowering is already proven for when the dialect/exporter
learns to fold them. -/

/-- A forward-compatible mem-folded `MULX` `(hi, lo) := a * [b + 16]`. -/
def demoMulxMem : LinstrR :=
  .Lopn [.reg "hi", .reg "lo"] "MULXMEM" [.reg "a", .reg "b", .imm 16]

/-- A forward-compatible `.rodata` symbol-base load `t := &twiddles`. -/
def demoLoadSym : LinstrR := .Lopn [.reg "t"] "LOADSYM" [.reg "twiddles"]

/-- `lowerLinstrExtCov` drops `demoMulxMem` (the two-destination shape) to `none`;
    `lowerLinstrExtCovMS` lowers it — a concrete strict-superset witness. -/
theorem demoMulxMem_cov_none : lowerLinstrExtCov demoMulxMem = none :=
  covMS_two_dst_none (.reg "hi") (.reg "lo") "MULXMEM" [.reg "a", .reg "b", .imm 16]

/-- The coverage superset lowers `demoMulxMem` to a single `mulxMem`. -/
theorem demoMulxMem_cov :
    lowerLinstrExtCovMS demoMulxMem
      = some [JInstr.mulxMem "hi" "lo" (.reg "a") "b" (16 : Int)] := rfl

/-- The coverage superset lowers `demoLoadSym` to a single `loadSym`. -/
theorem demoLoadSym_cov :
    lowerLinstrExtCovMS demoLoadSym = some [JInstr.loadSym "t" "twiddles"] := rfl

/-- The demo mem-folded `MULX` block is `allDirect` (constant-time class). -/
theorem demoMulxMem_allDirect :
    allDirect [(JInstr.mulxMem "hi" "lo" (.reg "a") "b" (16 : Int) : JInstr 64)] = true := by
  decide

/-- **Demo mem-fold effect.** Running the lowered `demoMulxMem` from a state where
    `a = 6` and `[b + 16] = 7` leaves `lo` holding `42` (low word of `6 · 7`, no
    overflow at 64 bits) and `hi` holding `0`. -/
theorem demoMulxMem_effect :
    (runBlock ({ regs := fun x => if x = "a" then 6 else 0
                 , mem := fun bse o => if bse = "b" ∧ o = 16 then 7 else 0 }
        : JState 64) [JInstr.mulxMem "hi" "lo" (.reg "a") "b" (16 : Int)]).get "lo" = 42 := by
  simp [runBlock, evalInstr, x86_MULX_lo_hi, JState.get, JState.setReg, JState.load,
    JOperand.eval, wumul]

/-- **Demo symbol-table gather effect.** After `leaq twiddles(%rip), %t`, gathering
    `t[2]` (scale `8`, so offset `16`) where the `.rodata` table has
    `twiddles[16] = 9` reads `9`. The base register `t` aliases the `twiddles`
    bank, so the indexed load resolves the table value. -/
theorem demoLoadSym_effect :
    let s := runBlock ({ regs := fun x => if x = "idx" then 2 else 0
                         , mem := fun bse o => if bse = "twiddles" ∧ o = 16 then 9 else 0 }
        : JState 64) [JInstr.loadSym "t" "twiddles"]
    s.loadIdx "t" "idx" 8 = 9 := by
  simp [runBlock, evalInstr, JState.loadIdx, JState.load, JState.get]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageMulxMemSym
