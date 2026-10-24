/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended

/-!
# Additive `Linstr → JInstr` coverage superset: MULX/ADX + register-indexed memory

`LoweringExtended.lean` builds two `Linstr → Option (List (JInstr 64))` lowerings:
the POC `lowerLinstrExt` (ALU/`MOV` + constant-offset `LOAD`/`STORE`) and its
supported-op superset `lowerLinstrExt2` (which adds the two-source `regArith`
exports, `MULXHI:64`, and the immediate shifts `SHR:<n>`/`SHL:<n>`). Both
return `none` on the carry-chain ADX exports (`ADCX:64`/`ADCXHI:64`) and on the
register-indexed (SIB) memory exports (`LOADIDX`/`STOREIDX`) — so a real
bignum/field kernel that uses `addCarry`/`mulhi`-fed carry threads, or a
runtime-indexed `stackLoad`/`stackStore`, does not reach the `JInstr` path
through them.

This module adds a **strict-superset** lowering `lowerLinstrExtCov` that delegates
every shape `lowerLinstrExt2` already covers (its catch-all arm is
`lowerLinstrExt2 i` verbatim) and adds arms for the dropped high-value shapes, so
that the `JInstr` path covers more of the owned kernels. The two other
lowerings are separate functions (as `lowerLinstrExt2` is separate from
`lowerLinstrExt`).

## What the exporter actually emits (the shapes this superset adds)

From `opToLinstrR` (`JasminLprogExport.lean`), the carry-chain / widening-multiply
ops and the register-indexed memory ops export as:

* `mulhi w`      → `Lopn [reg dst] "MULXHI:64" [s0, s1]`   — high word of `MULX`
  (**already** covered by `lowerLinstrExt2` → `mulx`; re-delegated here);
* `addCarryLo w` → `Lopn [reg dst] "ADCX:64"  [s0, s1, cin]` — the **data** binding
  `dst := dst + src + cin` of a carry-chain add; `cin` is the carry-in `reg 1`;
* `addCarryHi w` → `Lopn [reg dst] "ADCXHI:64" [s0, s1, cin]` — the **carry-out**
  binding (`reg 1`) of the same add, a post-add CF read;
* `stackLoad w _`  (register index) → `Lopn [reg dst] "LOADIDX"  [arrIdx base idx (w/8)]`
  — `mov (%base,%idx,scale), %dst`;
* `stackStore w _` (register index) → `Lopn [reg dst] "STOREIDX" [arrIdx base idx (w/8), val]`
  — `mov %val, (%base,%idx,scale)`.

The new arms target the matching `JInstr 64` constructors (`JasminModel.lean`):

| export mnemonic / shape | `JInstr 64` target | note |
|---|---|---|
| `MULXHI:64 [s0,s1]`            | `mulx dst dst__mulxlo s0 s1` | via `lowerLinstrExt2` (re-delegated) |
| `ADCX:64  [s0,s1,cin]`         | `[mov dst s0, adcx dst s1]`  | carry-in is `CF` (implicit in the model) |
| `ADOX:64  [s0,s1,cin]`         | `[mov dst s0, adox dst s1]`  | carry-in is `OF` (forward-compat) |
| `ADCXHI:64 [_,_,_]`           | `setc dst`                   | carry-out = post-add `CF` (`SETB`+`MOVZBQ`) |
| `ADOXHI:64 [_,_,_]`           | `[setcc .o dst, movzx dst 8 dst]` | carry-out = post-add `OF` (`SETO`+`MOVZBQ`) |
| `LOADIDX  [arrIdx b i s]`     | `loadMemIdx dst b i s`       | SIB gather (**not** `IsDirect`) |
| `STOREIDX [arrIdx b i s, v]`  | `storeMemIdx b i s v`        | SIB scatter (**not** `IsDirect`) |

## Coverage delta (honest)

`lowerLinstrExtCov` is a **strict superset** of `lowerLinstrExt2`: its catch-all
arm delegates verbatim, and the new head patterns fire only on shapes
`lowerLinstrExt2` dropped. The ADX superset gain is proved generally
(`lowerLinstrExtCov_delegates_adx` + `ext2_three_src_none`); the SIB gain is
witnessed concretely (`demoLoadIdx_cov`/`demoStoreIdx_cov`, each `rfl`). The
**newly** covered shapes (all dropped to `none` by both `lowerLinstrExt` and
`lowerLinstrExt2`):

* the carry-chain ADX data bindings `ADCX:64`/`ADOX:64` (two-address `mov; adcx`);
* the carry-out flag reads `ADCXHI:64` (`setc`, the `CF` chain) and `ADOXHI:64`
  (`setcc .o` + `movzx`, the `OF` chain);
* the register-indexed (SIB) memory ops `LOADIDX`/`STOREIDX`
  (`loadMemIdx`/`storeMemIdx`).

### Constant-time class of the new arms (honest)

The ADX arms (`mov`/`adcx`/`adox`) are `IsDirect`, so they stay inside the
unconditional `allDirect` constant-time class (`MachineConstantTime.lean`). The
**SIB arms are deliberately NOT** `IsDirect`: `loadMemIdx`/`storeMemIdx` have a
register-dependent effective address, so their CT story is the `agreePub` /
`CTAddressed` (public-index) one of `LowCTMemCT.lean`, **not** `allDirect`. We do
**not** claim `allDirect` for the SIB blocks (that would be false); we only claim
it for the ADX blocks.

## Still dropped (the honest remainder)

* `mulxMem` (the memory-folded `MULX`, `mulxq off(%base), %lo, %hi`) — the export
  does not currently emit a mem-folded `MULX` mnemonic (it splits the load and the
  reg-`MULX`), so there is no `Linstr` shape to lower; the `JInstr.mulxMem`
  constructor exists for when the exporter folds the load.
* `loadSym` (`leaq sym(%rip), %dst`) — the `.rodata` symbol-base load; the export
  emits its `LEA`-of-symbol shape elsewhere (the `lp_globs` path), not as an
  `Lopn` mnemonic this lowering sees.
* **Spill / frame memory**: in this IR a spill is **not** a memory `Linstr`
  shape — `physRegName` renders an overflow slot as the dotted **register name**
  `k.N` (`JasminLprogExport.lean §7a`), which appears as an ordinary `.reg "k.N"`
  operand inside the existing ALU/`MOV` arms and is materialised RSP-relative by
  the reader. There is therefore **no separate frame `LinstrR` constructor** to
  add an arm for; the spill/frame case is already covered (as a register operand)
  by the delegated `lowerLinstrExt2` arms. See the report.
* `ROR:<n>`/`SAR:<n>`, `CMOV`, `ZEROEXT`/`TRUNC`, `CALL:`/`CALLN:`,
  `VPACK8u64:`, and every non-`Lopn` `LinstrR` (`Lsyscall`/…/`Lcond`) — out of
  scope here (each is a separate follow-up).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended

/-! ## 1. The new arm bodies (ADX carry-chain + register-indexed memory) -/

/-- Lower a register-indexed (SIB) `LOADIDX [arrIdx base idx scale]`
    (`mov (%base,%idx,scale), %dst`) to `loadMemIdx dst base idx scale`. -/
def lowerLoadIdxJ (dst base idx : String) (scale : Nat) : JInstr 64 :=
  .loadMemIdx dst base idx scale

/-- Lower a register-indexed (SIB) `STOREIDX [arrIdx base idx scale, val]`
    (`mov %val, (%base,%idx,scale)`) to `storeMemIdx base idx scale val`. -/
def lowerStoreIdxJ (base idx : String) (scale : Nat) (src : JOperand) : JInstr 64 :=
  .storeMemIdx base idx scale src

/-! ## 2. The coverage superset

`lowerLinstrExtCov` first matches the **new** shapes by their **literal tagged
mnemonic** (the carry-chain `ADCX:64`/`ADOX:64`/`ADCXHI:64`/`ADOXHI:64` on three
sources; the SIB `LOADIDX`/`STOREIDX` with an `arrIdx` operand), then delegates
everything else to `lowerLinstrExt2`. Matching the literal mnemonic in the head
pattern (rather than dispatching through `stripWidthTag`) keeps every witness a
kernel `rfl`. The new head patterns are disjoint from every shape
`lowerLinstrExt2` lowers — the three-source `ADCX:64`/… mnemonics are not in its
ALU table (its generic two/three-source arms returned `none` on them), and the
`LOADIDX`/`STOREIDX` mnemonics with an `arrIdx` operand are likewise outside it —
so the superset is **strict** and the delegate is verbatim on every covered
shape. -/

/-- The additive coverage superset lowering. New arms (vs `lowerLinstrExt2`): the
    carry-chain ADX data bindings `ADCX:64`/`ADOX:64`, the carry-out flag reads
    `ADCXHI:64`/`ADOXHI:64`, and the register-indexed memory ops
    `LOADIDX`/`STOREIDX`. Every other shape delegates to `lowerLinstrExt2`. -/
def lowerLinstrExtCov : LinstrR → Option (List (JInstr 64))
  -- register-indexed (SIB) gather
  | .Lopn [.reg dst] "LOADIDX" [.arrIdx base idx scale] =>
      some [lowerLoadIdxJ dst base idx scale]
  -- register-indexed (SIB) scatter
  | .Lopn [.reg _] "STOREIDX" [.arrIdx base idx scale, val] =>
      some [lowerStoreIdxJ base idx scale (lowerJOperand val)]
  -- carry-chain ADX data binding `dst := dst + src + cin` (CF/OF carry-in is
  -- implicit in the model; the explicit `_cin = reg 1` source is dropped)
  | .Lopn [.reg dst] "ADCX:64" [s0, s1, _cin] =>
      some [JInstr.mov dst (lowerJOperand s0), JInstr.adcx dst (lowerJOperand s1)]
  | .Lopn [.reg dst] "ADOX:64" [s0, s1, _cin] =>
      some [JInstr.mov dst (lowerJOperand s0), JInstr.adox dst (lowerJOperand s1)]
  -- carry-out flag read `ADCXHI:64` → `setc dst` (the `CF` chain)
  | .Lopn [.reg dst] "ADCXHI:64" [_s0, _s1, _cin] =>
      some [JInstr.setc dst]
  -- carry-out flag read `ADOXHI:64` → `setcc .o dst ; movzx dst 8 dst` (the `OF`
  -- chain: the byte write of the overflow flag, zero-extended over `dst`)
  | .Lopn [.reg dst] "ADOXHI:64" [_s0, _s1, _cin] =>
      some [JInstr.setcc .o dst, JInstr.movzx dst 8 dst]
  -- everything else: the supported-op superset verbatim
  | i => lowerLinstrExt2 i

/-- Lower a full `Linstr` (drops the position tag), coverage superset. -/
def lowerLinstrExtCovL (i : Linstr) : Option (List (JInstr 64)) :=
  lowerLinstrExtCov i.li_i

/-! ## 3. New-coverage witnesses -/

/-- **New coverage: `ADCX:64` data binding.** Both `lowerLinstrExt` and
    `lowerLinstrExt2` drop it; the superset lowers it to `[mov dst s0, adcx dst s1]`. -/
theorem lowerLinstrExtCov_adcx (dst : String) (s0 s1 cin : LOperand) :
    lowerLinstrExtCov (.Lopn [.reg dst] "ADCX:64" [s0, s1, cin])
      = some [JInstr.mov dst (lowerJOperand s0), JInstr.adcx dst (lowerJOperand s1)] := rfl

/-- **New coverage: `ADOX:64` data binding.** -/
theorem lowerLinstrExtCov_adox (dst : String) (s0 s1 cin : LOperand) :
    lowerLinstrExtCov (.Lopn [.reg dst] "ADOX:64" [s0, s1, cin])
      = some [JInstr.mov dst (lowerJOperand s0), JInstr.adox dst (lowerJOperand s1)] := rfl

/-- **New coverage: `ADCXHI:64` carry-out binding** → `setc`. -/
theorem lowerLinstrExtCov_adcxhi (dst : String) (s0 s1 cin : LOperand) :
    lowerLinstrExtCov (.Lopn [.reg dst] "ADCXHI:64" [s0, s1, cin])
      = some [JInstr.setc dst] := rfl

/-- **New coverage: `ADOXHI:64` carry-out binding** → `setcc .o` + `movzx`. -/
theorem lowerLinstrExtCov_adoxhi (dst : String) (s0 s1 cin : LOperand) :
    lowerLinstrExtCov (.Lopn [.reg dst] "ADOXHI:64" [s0, s1, cin])
      = some [JInstr.setcc .o dst, JInstr.movzx dst 8 dst] := rfl

/-- **New coverage: register-indexed `LOADIDX`** → `loadMemIdx`. -/
theorem lowerLinstrExtCov_loadidx (dst base idx : String) (scale : Nat) :
    lowerLinstrExtCov (.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx scale])
      = some [JInstr.loadMemIdx dst base idx scale] := rfl

/-- **New coverage: register-indexed `STOREIDX`** → `storeMemIdx`. -/
theorem lowerLinstrExtCov_storeidx (dst base idx : String) (scale : Nat) (val : LOperand) :
    lowerLinstrExtCov (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx scale, val])
      = some [JInstr.storeMemIdx base idx scale (lowerJOperand val)] := rfl

/-! ## 4. Strict-superset of `lowerLinstrExt2`

The new head patterns never intercept a shape `lowerLinstrExt2` already lowered.
The three-source ADX mnemonics (`ADCX:64`/`ADOX:64`/`ADCXHI:64`/`ADOXHI:64`) are
witnessed structurally: a **three-element** source list matches none of
`lowerLinstrExt2`'s arms (its ALU arms take one or two sources), so it returned
`none` there — `ext2_three_src_none` proves this by list structure alone (no
string reduction). The SIB `LOADIDX`/`STOREIDX` shapes are witnessed
**concretely** by the demo `…_cov` facts in §7 (`rfl`): the literal-mnemonic head
patterns of `lowerLinstrExtCov` match before the delegate, so the superset adds
their coverage.

(A fully general `none`-on-`LOADIDX`/`STOREIDX` lemma would need to reduce
`String.endsWith "LOADIDX" ":64"` / `String.startsWith` inside
`lowerLinstrExt2`'s single-source arm; those `Substring`-based `String` ops are
not kernel-reducible — `decide`/`rfl`/`simp` all get stuck — and `native_decide`
is out of policy here. So the SIB superset is stated concretely, the ADX
superset generally; see the report.) -/

/-- `lowerLinstrExt2` drops **any** three-source `Lopn` (regardless of mnemonic):
    its ALU arms take one or two sources, and the POC fragment it delegates to has
    no three-source `Lopn` arm. Proved by list structure — no string reduction. -/
theorem ext2_three_src_none (dst opn : String) (s0 s1 cin : LOperand) :
    lowerLinstrExt2 (.Lopn [.reg dst] opn [s0, s1, cin]) = none := by
  simp only [lowerLinstrExt2, lowerLinstrExt]

/-- **Strict superset on the carry-chain ADX arms.** On a three-source
    `ADCX:64`/`ADOX:64`/`ADCXHI:64`/`ADOXHI:64` binding, `lowerLinstrExt2` returned
    `none` (three sources), while `lowerLinstrExtCov` lowers it — so the superset
    strictly extends coverage on exactly the carry-chain shapes the bignum kernels
    need. (The hypothesis is vacuous: `lowerLinstrExt2` never lowers a three-source
    shape, so there is nothing to contradict.) -/
theorem lowerLinstrExtCov_delegates_adx (dst opn : String) (s0 s1 cin : LOperand)
    (b : List (JInstr 64)) (h : lowerLinstrExt2 (.Lopn [.reg dst] opn [s0, s1, cin]) = some b) :
    False := by
  rw [ext2_three_src_none] at h; exact absurd h (by simp)

/-! ## 5. Constant-time class of the new arms

The ADX data arms (`mov`/`adcx`/`adox`) are `IsDirect`, so they stay inside the
unconditional `allDirect` constant-time class. The SIB arms are NOT `IsDirect`
(register-dependent address) — we explicitly do **not** claim `allDirect` for
them. -/

/-- The lowered `ADCX` data block is `allDirect` (`mov`/`adcx` are direct). -/
theorem lowerLinstrExtCov_adcx_allDirect (dst : String) (s0 s1 : JOperand) :
    allDirect [(JInstr.mov dst s0 : JInstr 64), JInstr.adcx dst s1] = true := rfl

/-- The lowered `ADOX` data block is `allDirect`. -/
theorem lowerLinstrExtCov_adox_allDirect (dst : String) (s0 s1 : JOperand) :
    allDirect [(JInstr.mov dst s0 : JInstr 64), JInstr.adox dst s1] = true := rfl

/-- The carry-out block (`setc`) is `allDirect`. -/
theorem lowerLinstrExtCov_setc_allDirect (dst : String) :
    allDirect [(JInstr.setc dst : JInstr 64)] = true := rfl

/-- The overflow carry-out block (`setcc .o` + `movzx`) is `allDirect`. -/
theorem lowerLinstrExtCov_setcc_movzx_allDirect (dst : String) :
    allDirect [(JInstr.setcc .o dst : JInstr 64), JInstr.movzx dst 8 dst] = true := rfl

/-- **The SIB load is NOT `IsDirect`** — register-indexed addressing. Recorded so
    no caller mistakes the SIB arms for the unconditional `allDirect` class. -/
theorem lowerLinstrExtCov_loadidx_not_direct (dst base idx : String) (scale : Nat) :
    ¬ IsDirect (JInstr.loadMemIdx dst base idx scale : JInstr 64) := by
  simp [IsDirect]

/-- **The SIB store is NOT `IsDirect`.** -/
theorem lowerLinstrExtCov_storeidx_not_direct (base idx : String) (scale : Nat)
    (src : JOperand) :
    ¬ IsDirect (JInstr.storeMemIdx base idx scale src : JInstr 64) := by
  simp [IsDirect]

/-! ## 6. Denotation of the new arms (against `JInstr`'s `runBlock`) -/

/-- **`ADCX` denotation.** Running the lowered `ADCX` data block leaves `dst`
    holding the low word of `waddcarry s0 s1 CF` (`dst := s0 + s1 + CF`): after the
    `mov dst s0` the destination holds `s0.eval s`, and `adcx dst s1` then adds
    `s1` plus the carry-in `CF`, writing the data word. We expose the precise
    value `dst` ends up holding as the second component of `x86_ADCX` applied to
    the post-`mov` state's destination word, source, and `CF`. -/
theorem lowerLinstrExtCov_adcx_denote (dst : String) (s0 s1 : JOperand) (s : JState 64) :
    (runBlock s [JInstr.mov dst s0, JInstr.adcx dst s1]).get dst
      = (x86_ADCX ((s.setReg dst (x86_MOV (s0.eval s))).get dst)
          (s1.eval (s.setReg dst (x86_MOV (s0.eval s))))
          ((s.setReg dst (x86_MOV (s0.eval s))).flagB (·.cf))).2 := by
  simp only [runBlock, evalInstr, JState.get, ite_true]

/-- **`ADOXHI` denotation.** Running the lowered `ADOXHI` carry-out block writes
    the overflow flag into `dst` as the word `1`/`0`. This is the `OF` analogue of
    the `setc` arm of `evalInstr`, which writes `CF` the same way; the split into
    `SETcc` plus zero-extension is the one
    `JasminModel.evalInstr_setc_eq_setcc_movzx` states at condition `.b`. -/
theorem lowerLinstrExtCov_adoxhi_denote (dst : String) (s : JState 64) :
    runBlock s [JInstr.setcc .o dst, JInstr.movzx dst 8 dst]
      = s.setReg dst (if s.flagB (·.of) then 1 else 0) := by
  simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setRegMerge,
    JState.get_setReg_same, x86_MOVZX_wordExtendMerge]
  have hb : ∀ c : Bool, (x86_SETcc c).setWidth 64 = (if c then 1 else 0 : BitVec 64) := by
    intro c
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    cases c <;> simp [x86_SETcc]
  rw [hb]
  simp only [JState.setReg]
  congr 1
  funext r
  split <;> rfl

/-- **`LOADIDX` denotation.** The lowered SIB gather leaves `dst` holding the
    register-indexed memory word `[base + idx·scale]`. -/
theorem lowerLinstrExtCov_loadidx_denote (dst base idx : String) (scale : Nat)
    (s : JState 64) :
    (runBlock s [JInstr.loadMemIdx dst base idx scale]).get dst
      = s.loadIdx base idx scale := by
  simp only [runBlock, evalInstr, x86_MOV, JState.get_setReg_same]

/-- **`STOREIDX` denotation.** The lowered SIB scatter leaves the cell at the
    index register's effective offset holding the stored value. -/
theorem lowerLinstrExtCov_storeidx_denote (base idx : String) (scale : Nat)
    (src : JOperand) (s : JState 64) :
    (runBlock s [JInstr.storeMemIdx base idx scale src]).loadIdx base idx scale
      = x86_MOV (src.eval s) := by
  simp only [runBlock, evalInstr, JState.loadIdx_storeIdx_same]

/-! ## 7. Worked demo: shapes `lowerLinstrExt2` drops, lowered here

`demoAdcx` is the carry-chain data binding `r := r + a + carry` a bignum add
emits (`addCarryLo`); `demoLoadIdx`/`demoStoreIdx` are the runtime-indexed
gather/scatter `t := m[idx]` / `m[idx] := v` (`stackLoad`/`stackStore`). All
three are dropped to `none` by `lowerLinstrExt`/`lowerLinstrExt2`; the coverage
superset lowers them, with the right `runBlock` effect. The `_cov` facts (each
`rfl`) are the strict-superset witnesses: `lowerLinstrExtCov`'s literal-mnemonic
head patterns fire before the delegate, so each shape the older lowerings drop
lowers. (For `demoAdcx` the `lowerLinstrExt2 = none` side is also proved by
`demoAdcx_ext2_none`; for the SIB demos the `none` side needs unreducible
`String.endsWith` — see §4 — so only the `_cov` gain is stated.) -/

/-- A carry-chain data binding `r := r0 + a + carry`. -/
def demoAdcx : LinstrR := .Lopn [.reg "r"] "ADCX:64" [.reg "r0", .reg "a", .reg "c1"]

/-- A register-indexed gather `t := m[idx*8]`. -/
def demoLoadIdx : LinstrR := .Lopn [.reg "t"] "LOADIDX" [.arrIdx "m" "idx" 8]

/-- A register-indexed scatter `m[idx*8] := v`. -/
def demoStoreIdx : LinstrR := .Lopn [.reg "m'"] "STOREIDX" [.arrIdx "m" "idx" 8, .reg "v"]

/-- `lowerLinstrExt2` drops `demoAdcx` (the three-source ADX data binding) to
    `none`; `lowerLinstrExtCov` lowers it (`demoAdcx_cov`) — a concrete strict
    superset witness on the carry-chain shape. -/
theorem demoAdcx_ext2_none : lowerLinstrExt2 demoAdcx = none :=
  ext2_three_src_none "r" "ADCX:64" (.reg "r0") (.reg "a") (.reg "c1")

/-- The coverage superset lowers `demoAdcx` to a two-address `mov; adcx`. -/
theorem demoAdcx_cov :
    lowerLinstrExtCov demoAdcx
      = some [JInstr.mov "r" (.reg "r0"), JInstr.adcx "r" (.reg "a")] := rfl

/-- The coverage superset lowers `demoLoadIdx` to a single `loadMemIdx`. -/
theorem demoLoadIdx_cov :
    lowerLinstrExtCov demoLoadIdx = some [JInstr.loadMemIdx "t" "m" "idx" 8] := rfl

/-- The coverage superset lowers `demoStoreIdx` to a single `storeMemIdx`. -/
theorem demoStoreIdx_cov :
    lowerLinstrExtCov demoStoreIdx = some [JInstr.storeMemIdx "m" "idx" 8 (.reg "v")] := rfl

/-- The demo ADX block is `allDirect` (constant-time class). -/
theorem demoAdcx_allDirect :
    allDirect [JInstr.mov "r" (.reg "r0"), (JInstr.adcx "r" (.reg "a") : JInstr 64)] = true := by
  decide

/-- **Demo ADX effect.** Running the lowered `demoAdcx` from a state where `r0 = 5`,
    `a = 3`, `CF = false` leaves `r` holding `8`. -/
theorem demoAdcx_effect :
    (runBlock ({ regs := fun x => if x = "r0" then 5 else if x = "a" then 3 else 0 }
        : JState 64) [JInstr.mov "r" (.reg "r0"), JInstr.adcx "r" (.reg "a")]).get "r" = 8 := by
  simp [runBlock, evalInstr, x86_ADCX, waddcarry, JState.get, JState.setReg,
    JOperand.eval, JState.flagB, x86_MOV]

/-- **Demo SIB gather effect.** Running the lowered `demoLoadIdx` from a state
    where `idx = 2` and `m[16] = 9` (`scale·idx = 8·2 = 16`) leaves `t` holding `9`. -/
theorem demoLoadIdx_effect :
    (runBlock ({ regs := fun x => if x = "idx" then 2 else 0
                 , mem := fun b o => if b = "m" ∧ o = 16 then 9 else 0 }
        : JState 64) [JInstr.loadMemIdx "t" "m" "idx" 8]).get "t" = 9 := by
  simp [runBlock, evalInstr, x86_MOV, JState.get, JState.setReg, JState.loadIdx,
    JState.load]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
