/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CarryChainSelect

/-!
# Block-local flag-liveness for the MUL→MULX fusion (`fuseMulx`)

`CarryChainSelect.fuseMulx` coalesces a low `imul lo, b` immediately followed by a
widening `mulx hi, lo, a, b` into the single `mulx`, dropping the redundant low
`imul`.  `CarryChainSelect.fuseMulx_get_sound` proves the *data-word* result is
unchanged, but the dropped `imul` also **sets the x86 flags** (`CF`/`OF`, and
undefines `SF`/`PF`/`ZF`) that `mulx` does not.  Dropping it therefore changes the
flag state, so the coalesce is denotation-preserving only where those flags are
**dead** at that point.

This module supplies the missing side condition as a **computable backward
flag-liveness analysis** over `List (JInstr 64)` and a **guarded** fusion pass
whose `runBlock`-equivalence is unconditional.

## The analysis

`readsFlag` and `writesAllFlags` classify each `JInstr` constructor against
`JasminModel.evalInstr`:

* `readsFlag i` — `i` observes a flag: `adc`/`sbb`/`setc`/`cmovb`/`adcx`/`rcl`/`rcr`
  read `CF`, `adox` reads `OF`, `cmove`/`cmovne` read `ZF`, and `cmovcc`/`setcc`
  read the flags of their `Condt`.
* `writesAllFlags i` — `i` overwrites **all five** flags as a pure function of its
  register/immediate inputs (a `writeB5W`/`writeB5`/`writeB5W2`/`writeB5N` op that
  does not first read a flag): `add`/`sub`/`imul`/`imulri`/`neg`/`and_`/`or_`/`xor_`/
  `shl`/`shr`/`sar`/`shld`/`shrd`/`andn`, the widening `mul`/`imulWide`, and
  `test`/`testN`/`cmp`, whose only output is the five flags.

The rotates `rol`/`ror` are a **partial** flag write: they set `OF`/`CF` through
`JState.writeB2W` and leave `SF`/`PF`/`ZF` at their incoming values.  `inc`/`dec`
write `OF`/`SF`/`PF`/`ZF` and keep `CF` (`writeB4W`); `clc`, `stc`, `bt`, `btr` and
`bts` write `CF` alone.  These are neither flag reads nor full flag writes.  The scan
skips them, which is sound because their register and memory effect is a function of
the register file alone.  Every remaining constructor (`mov`, `xchg`, `mulx`,
`mulxMem`, the memory moves, `loadSym`, the BMI2 `rorx`/`shlx`/`shrx`/`sarx`, `not_`,
the extension moves and `lea`) touches no flag at all.  The two predicates are disjoint, and a constructor whose classification would be
ambiguous is treated as reading a flag (conservative).

`flagsDeadFrom instrs` scans the suffix straight-line: a leading flag **read**
makes the flags live (`false`); a leading full flag **write** re-establishes every
flag from the registers, so the earlier flag difference is unobservable (`true`);
any flag-neutral instruction is skipped; the empty suffix is `false` (the flags
would still differ at block end, so deadness is not provable).  `flagsDeadAfter
body n` is `flagsDeadFrom` of the suffix after index `n`.

The analysis is a sound over-approximation of deadness: it reports `true` only when
the flags provably reconverge before any read.

## The guarded pass

`fuseMulxGuarded` fires only where the recognised pair is followed by a suffix in
which the flags are dead and the multiplicand/multiplier registers are distinct
from the low destination (`a ≠ lo`, `b ≠ lo`).  `fuseMulxGuarded_runBlock` is then
an unconditional `runBlock`-equality (a no-op where the guard fails, sound where it
fires), and `fuseMulxGuarded_allDirect` carries the constant-time class.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFlagLiveness

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. Per-instruction flag classification -/

/-- `readsFlag i` is `true` when `evalInstr` reads a condition flag: `adc`, `sbb`,
    `setc`, `cmovb`, `adcx`, `adcxMem`, `rcl` and `rcr` read `CF`; `adox` and
    `adoxMem` read `OF`; `cmove`
    and `cmovne` read `ZF`; `cmovcc`, `cmovccMem` and `setcc` read the flags of their
    condition. Every other constructor reads no flag. -/
def readsFlag {w : Nat} : JInstr w → Bool
  | .adc _ _    => true
  | .sbb _ _    => true
  | .setc _     => true
  | .cmovb _ _  => true
  | .adcx _ _   => true
  | .adox _ _   => true
  | .cmove _ _  => true
  | .cmovne _ _ => true
  -- the rotates through carry read `CF`.
  | .rcl _ _    => true
  | .rcr _ _    => true
  -- the general conditional instructions read the flags of their condition
  -- (`x86_eval_cond`), at least one for every `Condt`.
  | .cmovcc _ _ _ => true
  | .cmovccMem _ _ _ _ => true
  | .setcc _ _  => true
  -- the memory-source carry additions read `CF` resp. `OF`.
  | .adcxMem _ _ _ => true
  | .adoxMem _ _ _ => true
  | _           => false

/-- `writesAllFlags i` is `true` when `evalInstr` overwrites all five flags as a
    pure function of the register/immediate inputs (a `writeB5W`/`writeB5`/
    `writeB5W2`/`writeB5N` op that does not first read a flag): `add`, `sub`, `imul`,
    `imulri`, `neg`, `and_`, `or_`, `xor_`, `shl`, `shr`, `sar`, `shld`, `shrd`,
    `andn`, `bzhi`, `mul`, `imulWide`, the memory-operand `addMem`/`addToMem`/`imulMem`/
    `imulriMem`, and `test`/`testN`/`cmp`/`cmpMem`, whose five flags are their
    only output.  The partial writes `adcx`/`adox`/`adcxMem`/`adoxMem`/`rol`/`ror`/`rcl`/`rcr`/`inc`/`dec`/
    `clc`/`stc`/`bt`/`btr`/`bts` and the flag-reading `adc`/`sbb` are excluded
    (`adcx`/`adox`/`adc`/`sbb`/`rcl`/`rcr` appear under `readsFlag`). -/
def writesAllFlags {w : Nat} : JInstr w → Bool
  | .test _ _ => true
  | .cmp _ _  => true
  | .add _ _  => true
  | .sub _ _  => true
  | .imul _ _ => true
  | .neg _    => true
  | .and_ _ _ => true
  | .or_ _ _  => true
  | .xor_ _ _ => true
  | .shl _ _  => true
  | .shr _ _  => true
  | .sar _ _  => true
  -- BMI1 `andn` writes the full `B5W` tuple: `OF`/`CF` cleared, `SF`/`ZF` from the
  -- result, `PF` undefined.  All five entries are a function of the sources, so the
  -- state after it is determined by the register file.
  | .andn _ _ _ => true
  -- The rotates write `OF`/`CF` only and preserve `SF`/`PF`/`ZF`, so they do not
  -- re-establish the whole flag map from the registers.
  | .rol _ _  => false
  | .ror _ _  => false
  -- `imulri`, the double shifts (`writeB5W`), the widening multiplies (`writeB5W2`)
  -- and the sized `testN` (`writeB5N`) write all five flags from their register and
  -- immediate inputs.
  | .imulri _ _ _ => true
  | .mul _ _ _ => true
  | .imulWide _ _ _ => true
  | .shld _ _ _ => true
  | .shrd _ _ _ => true
  | .testN _ _ _ => true
  -- `inc`/`dec` keep `CF`; `clc`, `stc`, `bt`, `btr` and `bts` write `CF` alone.
  | .inc _ | .dec _ | .clc | .stc | .bt _ _ | .btr _ _ | .bts _ _ => false
  -- The memory-operand `add` and `imul` forms write all five flags from their register,
  -- memory and immediate inputs; `adcxMem`/`adoxMem` write one flag.
  | .addMem _ _ _ | .addToMem _ _ _ | .imulMem _ _ _ | .imulriMem _ _ _ _ | .cmpMem _ _ _ => true
  | .adcxMem _ _ _ | .adoxMem _ _ _ => false
  -- BMI2 `bzhi` writes the full `B5W` tuple from its two register sources.
  | .bzhi _ _ _ => true
  | _         => false

/-! ## 2. The backward liveness scan -/

/-- `flagsDeadFrom instrs` is `true` when, along the straight-line suffix `instrs`,
    every flag the dropped `imul` sets is overwritten (by a full flag write) before
    any instruction reads a flag.  A leading flag read makes the flags live; a
    leading full flag write reconverges them; a flag-neutral instruction is skipped;
    the empty suffix is `false` (the flags would still differ at block end). -/
def flagsDeadFrom {w : Nat} : List (JInstr w) → Bool
  | [] => false
  | i :: rest => !readsFlag i && (writesAllFlags i || flagsDeadFrom rest)

/-- `flagsDeadAfter body n` is `true` when the flags are dead after the instruction
    at index `n` of `body`, i.e. the liveness scan of the suffix `body.drop (n+1)`
    succeeds. -/
def flagsDeadAfter (body : List (JInstr 64)) (n : Nat) : Bool :=
  flagsDeadFrom (body.drop (n + 1))

/-! ## 3. Congruence of `evalInstr` on states agreeing except in flags -/

/-- Operand evaluation depends only on the register file. -/
theorem JOperand.eval_congr {w : Nat} {s₁ s₂ : JState w} (hr : s₁.regs = s₂.regs)
    (o : JOperand) : o.eval s₁ = o.eval s₂ := by
  cases o <;> simp [JOperand.eval, JState.get, hr]

/-- A full-flag-write instruction lands in a state fully determined by the register
    file and memory (its `writeB5W` discards the incoming flags), so two states
    agreeing on registers and memory step to the **same** state. -/
theorem evalInstr_full_eq_of_writesAll {i : JInstr 64} (hw : writesAllFlags i = true)
    {s₁ s₂ : JState 64} (hr : s₁.regs = s₂.regs) (hm : s₁.mem = s₂.mem) :
    evalInstr s₁ i = evalInstr s₂ i := by
  cases i <;>
    simp_all [writesAllFlags, evalInstr, JState.writeB5W, JState.writeB5, JState.get,
      JState.writeB5W2, JState.writeB5N, JOperand.eval, JState.writeB5Mem, JState.store,
      JState.load]

/-- A flag-neutral instruction (neither reading nor fully writing flags) updates the
    register file and memory as a function of the register file and memory alone, so
    two states agreeing on registers and memory step to states that still agree on
    registers and memory. -/
theorem evalInstr_regsMem_congr {i : JInstr 64} (hnr : readsFlag i = false)
    (hnw : writesAllFlags i = false) {s₁ s₂ : JState 64} (hr : s₁.regs = s₂.regs)
    (hm : s₁.mem = s₂.mem) :
    (evalInstr s₁ i).regs = (evalInstr s₂ i).regs ∧
      (evalInstr s₁ i).mem = (evalInstr s₂ i).mem := by
  cases i <;>
    simp_all [readsFlag, writesAllFlags, evalInstr, JState.setReg, JState.writeB2W,
      JState.store, JState.storeIdx, JState.load, JState.loadIdx, JState.get,
      JState.writeB4W, JState.writeCFW, x86_XCHG, JOperand.eval]
  all_goals exact rfl

/-! ## 4. Liveness discharges the flag side condition -/

/-- **Liveness closes the flag gap.**  If the flags are dead along `block` and two
    start states agree on registers and memory (differing only in flags), then
    `runBlock` lands in the same final state.  Either a full flag write reconverges
    the states (then the tails are identical), or every flag-neutral step preserves
    register/memory agreement until such a write. -/
theorem runBlock_congr (block : List (JInstr 64)) :
    ∀ (s₁ s₂ : JState 64), flagsDeadFrom block = true →
      s₁.regs = s₂.regs → s₁.mem = s₂.mem → runBlock s₁ block = runBlock s₂ block := by
  induction block with
  | nil => intro s₁ s₂ hd; simp [flagsDeadFrom] at hd
  | cons i rest ih =>
    intro s₁ s₂ hd hr hm
    rw [runBlock_cons, runBlock_cons]
    by_cases hread : readsFlag i = true
    · rw [flagsDeadFrom, hread] at hd; simp at hd
    · have hnr : readsFlag i = false := by simpa using hread
      by_cases hw : writesAllFlags i = true
      · rw [evalInstr_full_eq_of_writesAll hw hr hm]
      · have hnw : writesAllFlags i = false := by simpa using hw
        have hdr : flagsDeadFrom rest = true := by
          rw [flagsDeadFrom, hnr, hnw] at hd; simpa using hd
        obtain ⟨hrr, hmm⟩ := evalInstr_regsMem_congr hnr hnw hr hm
        exact ih _ _ hdr hrr hmm

/-! ## 5. The recognised pair agrees on registers and memory after fusion -/

/-- **The fused pair matches the un-fused pair on registers and memory.**  Running
    `imul lo, b` then `mulx hi, lo, a, b` lands the same register file and memory as
    running the `mulx` alone, provided the multiplicand `a` and multiplier `b` are
    distinct from the low destination `lo` (so the dropped `imul`'s write to `lo` is
    the value `mulx` recomputes, and does not perturb the `mulx` inputs).  The two
    states differ only in the flags the dropped `imul` set. -/
theorem pair_agree (s : JState 64) (hi lo a b : String) (ha : a ≠ lo) (hb : b ≠ lo) :
    (evalInstr (evalInstr s (.imul lo (.reg b))) (.mulx hi lo (.reg a) (.reg b))).regs
        = (evalInstr s (.mulx hi lo (.reg a) (.reg b))).regs
    ∧ (evalInstr (evalInstr s (.imul lo (.reg b))) (.mulx hi lo (.reg a) (.reg b))).mem
        = (evalInstr s (.mulx hi lo (.reg a) (.reg b))).mem := by
  constructor
  · funext r
    simp only [evalInstr, JOperand.eval, JState.setReg, JState.writeB5W, JState.get,
      x86_MULX_lo_hi]
    rw [if_neg ha, if_neg hb]
    by_cases h1 : r = hi <;> by_cases h2 : r = lo <;> simp [h1, h2]
  · simp only [evalInstr, JOperand.eval, JState.setReg, JState.writeB5W, JState.get,
      x86_MULX_lo_hi]

/-! ## 6. The guarded fusion pass -/

/-- **The flag-liveness-guarded MUL→MULX selector.**  It fires exactly where the
    recognised pair `imul lo, b` / `mulx hi, lo, a, b` is followed by a suffix in
    which the flags are dead (`flagsDeadFrom rest`) and the fusion's freshness holds
    (`a ≠ lo`, `b ≠ lo`); there it drops the redundant low `imul`.  Everywhere else
    it passes the instruction through unchanged. -/
def fuseMulxGuarded : List (JInstr 64) → List (JInstr 64)
  | [] => []
  | i₁ :: i₂ :: rest =>
    match CarryChainSelect.isRedundantLowMul i₁, CarryChainSelect.isWideningMul i₂ with
    | some (lo, b), some (_hi, lo', a, b') =>
        if lo == lo' && b == b' && (a != lo) && (b != lo) && flagsDeadFrom rest then
          i₂ :: fuseMulxGuarded rest
        else i₁ :: fuseMulxGuarded (i₂ :: rest)
    | _, _ => i₁ :: fuseMulxGuarded (i₂ :: rest)
  | [i] => [i]

/-- Inversion of the low-`imul` recogniser. -/
theorem isRedundantLowMul_some {i : JInstr 64} {lo b : String}
    (h : CarryChainSelect.isRedundantLowMul i = some (lo, b)) :
    i = .imul lo (.reg b) := by
  unfold CarryChainSelect.isRedundantLowMul at h
  split at h <;> simp_all

/-- Inversion of the widening-`mulx` recogniser. -/
theorem isWideningMul_some {i : JInstr 64} {hi lo a b : String}
    (h : CarryChainSelect.isWideningMul i = some (hi, lo, a, b)) :
    i = .mulx hi lo (.reg a) (.reg b) := by
  unfold CarryChainSelect.isWideningMul at h
  split at h <;> simp_all

/-- **The pass introduces no new instructions.**  Every instruction of
    `fuseMulxGuarded body` already occurs in `body`. -/
theorem fuseMulxGuarded_mem_of_mem (body : List (JInstr 64)) :
    ∀ i ∈ fuseMulxGuarded body, i ∈ body := by
  fun_induction fuseMulxGuarded body with
  | case1 => intro i hi; simp at hi
  | case2 i₁ i₂ rest lo b hlo hi' lo' a b' hw hcond ih =>
      intro j hj
      rcases List.mem_cons.mp hj with h₂ | hr
      · subst h₂; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih j hr))
  | case3 i₁ i₂ rest lo b hlo hi' lo' a b' hw hcond ih =>
      intro j hj
      rcases List.mem_cons.mp hj with h₁ | hr
      · subst h₁; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih j hr)
  | case4 i₁ i₂ rest hmatch ih =>
      intro j hj
      rcases List.mem_cons.mp hj with h₁ | hr
      · subst h₁; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih j hr)
  | case5 i => intro j hj; exact hj

/-- **Unconditional `runBlock`-equality of the guarded pass.**  On every block and
    start state, `fuseMulxGuarded` preserves the machine semantics: where the guard
    fails the block is unchanged; where it fires, the dropped `imul`'s data word is
    recomputed by the `mulx` (registers/memory agree by `pair_agree`) and the
    flags it set are dead (`runBlock_congr`), so the tails coincide. -/
theorem fuseMulxGuarded_runBlock (body : List (JInstr 64)) :
    ∀ s : JState 64, runBlock s (fuseMulxGuarded body) = runBlock s body := by
  fun_induction fuseMulxGuarded body with
  | case1 => intro s; rfl
  | case2 i₁ i₂ rest lo b mHi mLo mA mB hWide hLow hcond ih =>
      intro s
      -- guard fired: extract the fusion facts
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcond
      obtain ⟨⟨⟨⟨hloeq, hbeq⟩, hane⟩, hbne⟩, hdead⟩ := hcond
      have hi₁ : i₁ = .imul lo (.reg b) := isRedundantLowMul_some hLow
      have hi₂ : i₂ = .mulx mHi lo (.reg mA) (.reg b) := by
        rw [isWideningMul_some hWide, ← hloeq, ← hbeq]
      subst hi₁; subst hi₂
      simp only [runBlock_cons]
      rw [ih (evalInstr s (.mulx mHi lo (.reg mA) (.reg b)))]
      obtain ⟨hrr, hmm⟩ := pair_agree s mHi lo mA b hane hbne
      exact (runBlock_congr rest _ _ hdead hrr hmm).symm
  | case3 i₁ i₂ rest lo b mHi mLo mA mB hWide hLow hcond ih =>
      intro s
      simp only [runBlock_cons]
      rw [ih (evalInstr s i₁)]
      simp only [runBlock_cons]
  | case4 i₁ i₂ rest hmatch ih =>
      intro s
      simp only [runBlock_cons]
      rw [ih (evalInstr s i₁)]
      simp only [runBlock_cons]
  | case5 i => intro s; rfl

/-! ## 7. Constant-time preservation -/

/-- Every instruction of `body` is `IsDirect` ⇒ `allDirect body = true`.  The
    converse of `ConstantTimeCoverage.allDirect_mem_isDirect`. -/
theorem allDirect_of_mem_isDirect (body : List (JInstr 64))
    (h : ∀ i ∈ body, IsDirect i) : allDirect body = true := by
  simp only [allDirect, List.all_eq_true, decide_eq_true_eq]
  exact fun i hi => h i hi

/-- **Constant-time preservation.**  If every instruction of `body` is `IsDirect`,
    so is every instruction of `fuseMulxGuarded body` (it only keeps existing
    instructions), hence `allDirect` is preserved. -/
theorem fuseMulxGuarded_allDirect (body : List (JInstr 64))
    (h : allDirect body = true) : allDirect (fuseMulxGuarded body) = true :=
  allDirect_of_mem_isDirect _ fun i hi =>
    allDirect_mem_isDirect body h i (fuseMulxGuarded_mem_of_mem body i hi)

end CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFlagLiveness
