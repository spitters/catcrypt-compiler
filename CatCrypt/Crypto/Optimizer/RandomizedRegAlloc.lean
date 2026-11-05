/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# Verified CryptOpt: randomized register allocation with in-Lean translation validation

This is the **register-allocation** companion to the schedule-search pass in
`RandomizedScheduleSearch.lean`. CryptOpt (Kuepper et al., PLDI'23) searches the
joint space of `{instruction schedule, register allocation}` by randomized local
search and certifies the chosen winner with an **external** equivalence checker.
The schedule half is the §1–§9 of the sibling file; this file is the RA half,
validated the same way — **in Lean**, replacing the external checker.

A register-allocation choice is a **renaming** `ρ : String → String` of the
SSA-style virtual register names a `JInstr` block uses (the names the backend's
`AsmPrinter.allocGp` later maps to physical `%rN`). Renaming is *exactly* the
degree of freedom regalloc has, and is what the `feMulBlock` null in
`RandomizedScheduleSearch.feMulBlock_legal_swaps` identified as the missing lever:
the schoolbook reuses the `hi`/`lo` mul-output names across every column product,
which serialises the schedule **by name**; unlocking the parallelism needs a
*renaming*, not a reschedule.

## The pass (Com→Com, owned optimisation layer)

`renameBlock ρ` rewrites every register name (including memory base pointers) of
a block by `ρ`. Composed with `X86Dialect.lowerBlock` it is a transform on the
backend `Com`. A **randomized** instance (`searchAssign`) draws a seeded LCG
permutation of the free-name → physical mapping; an **acceptance check**
(`accept`) keeps only renamings that (a) are injective on the block's live names
(no two virtuals collapse onto one physical) and (b) fit the GP pool
(`AsmPrinter.allocOverflow = none`, the overflow guard).

## Translation validation (the contribution)

The denotation-preservation theorem is **fully general** and proved for all
blocks / all states: for an injective renaming `ρ`,

  `runBlock (renameState ρ s) (renameBlock ρ block) = renameState ρ (runBlock s block)`

i.e. running the renamed block from the ρ-renamed state lands in the ρ-renamed
final state — the rename commutes through the whole machine semantics
(`evalInstr`/`runBlock`), so a renaming accepted by the pass is
denotation-preserving against the validated `JasminModel`. Lifted through
`X86Dialect.lowerBlock_denote_closed` this is equality of lowered-`Com`
denotations modulo the renaming, the in-Lean certificate that takes the place of
CryptOpt's external equivalence checker for the RA dimension.

The `renameState ρ`-on-both-sides shape is the right statement: a renaming is a
bijection of *which physical register holds which value*, so the post-states are
equal **up to** that bijection (read register `ρ n` of the renamed run = read
register `n` of the original). This is precisely soundness of register
allocation; there is no stronger all-states-literally-equal claim to make for a
rename (and claiming one would be false).

## Headroom

fe25519/s2n-class kernels have **zero** GP headroom (the analysis result is null:
`gpFreeSlots` is fully consumed and s2n itself reuses `%rax`). This pass therefore
targets kernels with slack. §6 records `AsmPrinter.gpFreeSlots`/`gpFreeNames`
for the suite's small straight-line kernels (`add2Block`,
`MpnLinearKernels.addBlock`): they sit far under the pool, so a renaming that
spreads the mul-output names across distinct physicals is *accepted* (overflow
stays `none`) — the structural prerequisite the schoolbook lacked. Whether a
spread renaming is a measured win is a CPU question deferred to a bench harness;
the verified pass + its acceptance check is the infrastructure deliverable.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. Renaming a block (the register-allocation transform) -/

/-- Rename the register name inside an operand (immediates are untouched). -/
def renameOperand (ρ : String → String) : JOperand → JOperand
  | .reg r => .reg (ρ r)
  | .imm v => .imm v

/-- Apply a register renaming `ρ` to one instruction: every register name — the
    destinations, the source operands, and any memory **base** pointer — is
    rewritten by `ρ`. This is the syntactic action of a register-allocation
    choice on the block. -/
def renameInstr (ρ : String → String) : JInstr 64 → JInstr 64
  | .mov d s   => .mov (ρ d) (renameOperand ρ s)
  | .add d s   => .add (ρ d) (renameOperand ρ s)
  | .sub d s   => .sub (ρ d) (renameOperand ρ s)
  | .adc d s   => .adc (ρ d) (renameOperand ρ s)
  | .sbb d s   => .sbb (ρ d) (renameOperand ρ s)
  | .imul d s  => .imul (ρ d) (renameOperand ρ s)
  | .neg d     => .neg (ρ d)
  | .setc d    => .setc (ρ d)
  | .and_ d s  => .and_ (ρ d) (renameOperand ρ s)
  -- `test a s` has no destination: both operands are reads, and both are renamed.
  | .test a s  => .test (ρ a) (renameOperand ρ s)
  -- `cmp a s` likewise has no destination.
  | .cmp a s   => .cmp (ρ a) (renameOperand ρ s)
  | .not_ d    => .not_ (ρ d)
  | .andn d a b => .andn (ρ d) (ρ a) (ρ b)
  | .rol d amt => .rol (ρ d) (renameOperand ρ amt)
  | .ror d amt => .ror (ρ d) (renameOperand ρ amt)
  | .rorx d src amt => .rorx (ρ d) (ρ src) (renameOperand ρ amt)
  | .shlx d src c => .shlx (ρ d) (ρ src) (ρ c)
  | .shrx d src c => .shrx (ρ d) (ρ src) (ρ c)
  | .sarx d src c => .sarx (ρ d) (ρ src) (ρ c)
  -- `srcW` is a width, not a name, so it is carried through unchanged.
  | .movzx d sw src => .movzx (ρ d) sw (ρ src)
  | .movsx d sw src => .movsx (ρ d) sw (ρ src)
  -- `lea` renames its destination and both address registers; the scale and the
  -- displacement are literals.
  | .lea d base idx scale off => .lea (ρ d) (ρ base) (ρ idx) scale off
  | .or_ d s   => .or_ (ρ d) (renameOperand ρ s)
  | .xor_ d s  => .xor_ (ρ d) (renameOperand ρ s)
  | .shl d s   => .shl (ρ d) (renameOperand ρ s)
  | .shr d s   => .shr (ρ d) (renameOperand ρ s)
  | .sar d s   => .sar (ρ d) (renameOperand ρ s)
  | .cmove d s  => .cmove (ρ d) (renameOperand ρ s)
  | .cmovne d s => .cmovne (ρ d) (renameOperand ρ s)
  | .cmovb d s  => .cmovb (ρ d) (renameOperand ρ s)
  | .mulx dh dl a b => .mulx (ρ dh) (ρ dl) (renameOperand ρ a) (renameOperand ρ b)
  | .mulxMem dh dl a base off => .mulxMem (ρ dh) (ρ dl) (renameOperand ρ a) (ρ base) off
  | .adcx d s  => .adcx (ρ d) (renameOperand ρ s)
  | .adox d s  => .adox (ρ d) (renameOperand ρ s)
  | .loadMem d base off  => .loadMem (ρ d) (ρ base) off
  | .storeMem base off s => .storeMem (ρ base) off (renameOperand ρ s)
  | .loadMemIdx d base idx scale  => .loadMemIdx (ρ d) (ρ base) (ρ idx) scale
  | .storeMemIdx base idx scale s =>
      .storeMemIdx (ρ base) (ρ idx) scale (renameOperand ρ s)
  -- `loadSym d sym` writes register `d` (renamed by `ρ`). In the `evalInstr`
  -- model the instruction also aliases base `d`'s memory bank onto base `sym`'s
  -- (the `.rodata` table), so for the renaming to commute through `MemRel` (which
  -- relates banks by `ρ`-renamed base name) the symbol base is carried through `ρ`
  -- too. A valid allocator `ρ` fixes every name outside the GP pool — in
  -- particular the `.rodata` label `sym` (`ρ sym = sym`) — so the *emitted* label
  -- is unchanged; renaming it here is what makes the simulation hold for an
  -- arbitrary injective `ρ`.
  | .loadSym d sym => .loadSym (ρ d) (ρ sym)
  | .inc d     => .inc (ρ d)
  | .dec d     => .dec (ρ d)
  | .clc       => .clc
  | .stc       => .stc
  | .xchg a b  => .xchg (ρ a) (ρ b)
  | .imulri d src imm => .imulri (ρ d) (ρ src) imm
  | .mul dh dl src => .mul (ρ dh) (ρ dl) (ρ src)
  | .imulWide dh dl src => .imulWide (ρ dh) (ρ dl) (ρ src)
  | .shld d src amt => .shld (ρ d) (ρ src) (renameOperand ρ amt)
  | .shrd d src amt => .shrd (ρ d) (ρ src) (renameOperand ρ amt)
  | .rcl d amt => .rcl (ρ d) (renameOperand ρ amt)
  | .rcr d amt => .rcr (ρ d) (renameOperand ρ amt)
  -- the condition and the `testN` operand size are not names and are carried through.
  | .cmovcc c d s => .cmovcc c (ρ d) (renameOperand ρ s)
  | .setcc c d => .setcc c (ρ d)
  | .testN sz a b => .testN sz (ρ a) (renameOperand ρ b)
  | .bt a b    => .bt (ρ a) (renameOperand ρ b)
  | .btr d b   => .btr (ρ d) (renameOperand ρ b)
  | .bts d b   => .bts (ρ d) (renameOperand ρ b)
  | .addMem d base off => .addMem (ρ d) (ρ base) off
  | .addToMem base off s => .addToMem (ρ base) off (renameOperand ρ s)
  | .adcxMem d base off => .adcxMem (ρ d) (ρ base) off
  | .adoxMem d base off => .adoxMem (ρ d) (ρ base) off
  | .imulMem d base off => .imulMem (ρ d) (ρ base) off
  | .imulriMem d base off imm => .imulriMem (ρ d) (ρ base) off imm
  | .cmpMem a base off => .cmpMem (ρ a) (ρ base) off
  | .cmovccMem c d base off => .cmovccMem c (ρ d) (ρ base) off
  | .aluMem op d base off => .aluMem op (ρ d) (ρ base) off
  | .andnMem d a base off => .andnMem (ρ d) (ρ a) (ρ base) off
  | .bzhi d src idx => .bzhi (ρ d) (ρ src) (ρ idx)

/-- Apply a register renaming to a whole block. -/
def renameBlock (ρ : String → String) (block : List (JInstr 64)) : List (JInstr 64) :=
  block.map (renameInstr ρ)

/-! ## 2. Renaming a machine state

`renameState ρ s` is the state in which physical register `ρ n` holds whatever
`s` held in `n`, *for an injective* `ρ`. Concretely: `(renameState ρ s).regs r`
returns `s.regs n` where `ρ n = r`, found by searching the live-name list. For an
injective `ρ` this is well-defined on the image of `ρ`; off the image the value
is irrelevant to the block (it never reads those names). We realise it directly
as a precomposition with a chosen left-inverse on the relevant names; the proof
below avoids needing the inverse explicitly by stating the simulation as a
pointwise agreement on register reads.

The clean carrier for the proof is the **simulation relation** `StateRel`: rather
than build `renameState` and reason about inverses, we relate two states by "the
renamed run's register `ρ n` agrees with the original run's register `n`", which
is what soundness of regalloc actually asserts and what lifts cleanly through the
backend. -/

/-- Memory is keyed by `(base, off)`; the base is a register name, so a renaming
    `ρ` acts on memory the same way it acts on registers. Two states' memories
    *correspond under `ρ`* when cell `(ρ b, o)` of the left equals cell `(b, o)`
    of the right for every base name `b` the block can mention. We over-approximate
    by quantifying over all base names — sound, and matches `evalInstr`'s
    by-name memory access. -/
def MemRel (ρ : String → String) {w : Nat} (sL sR : JState w) : Prop :=
  ∀ b o, sL.mem (ρ b) o = sR.mem b o

/-- The simulation relation a register renaming `ρ` induces: the renamed-run state
    `sL` and the original-run state `sR` agree on every register read up to `ρ`
    (`sL` at `ρ n` = `sR` at `n`), on all five flags, and on memory up to `ρ`. -/
structure StateRel (ρ : String → String) {w : Nat} (sL sR : JState w) : Prop where
  regs  : ∀ n, sL.regs (ρ n) = sR.regs n
  flags : sL.flags = sR.flags
  mem   : MemRel ρ sL sR

/-! ## 3. Operand evaluation respects the renaming -/

/-- An operand evaluated in the renamed state (after renaming the operand) equals
    the operand evaluated in the original state — provided the two states are in
    the `StateRel ρ` simulation. -/
theorem renameOperand_eval {w : Nat} {ρ : String → String} {sL sR : JState w}
    (h : StateRel ρ sL sR) (op : JOperand) :
    (renameOperand ρ op).eval sL = op.eval sR := by
  cases op with
  | reg r => simp [renameOperand, JOperand.eval, JState.get, h.regs r]
  | imm v => rfl

/-! ## 4. The one-step simulation lemma (the heart of the TV)

For an **injective** `ρ`, one `evalInstr` step preserves `StateRel`: running the
renamed instruction from the renamed state lands in the simulation with running
the original instruction from the original state. The injectivity is needed
exactly at the register/memory writes — `ρ n = ρ d ↔ n = d` lets the post-write
read at `ρ n` track the original post-write read at `n`. -/

/-- The register file after a `setReg`-style write commutes through `ρ`: if `sL`,
    `sR` register files are `ρ`-related, then writing `v` to `ρ d` in `sL` and to
    `d` in `sR` keeps them `ρ`-related (this is where injectivity is used). -/
theorem setReg_regs_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64}
    (hr : ∀ n, sL.regs (ρ n) = sR.regs n) (d : String) (v : BitVec 64) :
    ∀ n, (fun r' => if r' = ρ d then v else sL.regs r') (ρ n)
        = (fun r' => if r' = d then v else sR.regs r') n := by
  intro n
  by_cases hn : n = d
  · subst hn; simp
  · have hne : ρ n ≠ ρ d := fun he => hn (hρ he)
    simp [hne, hn, hr n]

/-- A `writeB5W` (data word + all five flags) commutes through `ρ`: register files
    stay `ρ`-related and the flag state is taken verbatim from the (value-equal)
    `B5W`, so the two written flag states are equal. -/
theorem writeB5W_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (d : String) (t : B5W 64) :
    StateRel ρ (sL.writeB5W (ρ d) t) (sR.writeB5W d t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.writeB5W] using setReg_regs_rel hρ h.regs d t.word
  · simp [JState.writeB5W]
  · intro b o; simpa [JState.writeB5W] using h.mem b o

/-- A `writeB5` (five flags, no data word) commutes through `ρ`: no register is
    written, so the register files stay `ρ`-related without any injectivity, and
    the two written flag states are equal because the `B5W` is. -/
theorem writeB5_rel {ρ : String → String} {sL sR : JState 64}
    (h : StateRel ρ sL sR) (t : B5W 64) :
    StateRel ρ (sL.writeB5 t) (sR.writeB5 t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n; simpa [JState.writeB5] using h.regs n
  · simp [JState.writeB5]
  · intro b o; simpa [JState.writeB5] using h.mem b o

/-- A `writeB2W` (data word + `OF`/`CF`, the other three flags kept) commutes
    through `ρ`: register files stay `ρ`-related, and the retained `SF`/`PF`/`ZF`
    agree because the pre-state flag states do. -/
theorem writeB2W_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (d : String) (t : B2W 64) :
    StateRel ρ (sL.writeB2W (ρ d) t) (sR.writeB2W d t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.writeB2W] using setReg_regs_rel hρ h.regs d t.word
  · simp [JState.writeB2W, h.flags]
  · intro b o; simpa [JState.writeB2W] using h.mem b o

/-- A `setReg` commutes through `ρ`. -/
theorem setReg_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (d : String) (v : BitVec 64) :
    StateRel ρ (sL.setReg (ρ d) v) (sR.setReg d v) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.setReg] using setReg_regs_rel hρ h.regs d v
  · simp [JState.setReg, h.flags]
  · intro b o; simpa [JState.setReg] using h.mem b o

/-- A double `setReg` (the `MULX` write of `(lo, hi)`) commutes through `ρ`. -/
theorem setReg2_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR)
    (dl dh : String) (lo hi : BitVec 64) :
    StateRel ρ ((sL.setReg (ρ dl) lo).setReg (ρ dh) hi)
      ((sR.setReg dl lo).setReg dh hi) :=
  setReg_rel hρ (setReg_rel hρ h dl lo) dh hi

/-- An `ADCX`/`ADOX`-style write of one data register plus one flag (CF or OF),
    captured by the explicit-record form `evalInstr` uses. The flag setter `setF`
    is applied to the (equal) two flag states, so the resulting flag states agree.
    Register files stay `ρ`-related; memory is untouched. -/
theorem adcWrite_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (d : String) (res : BitVec 64)
    (setF : RFlags → RFlags) :
    StateRel ρ
      { regs := fun r' => if r' = ρ d then res else sL.regs r'
        flags := setF sL.flags, mem := sL.mem }
      { regs := fun r' => if r' = d then res else sR.regs r'
        flags := setF sR.flags, mem := sR.mem } := by
  refine ⟨?_, ?_, ?_⟩
  · exact setReg_regs_rel hρ h.regs d res
  · simp [h.flags]
  · intro b o; exact h.mem b o

/-- A `writeB4W` (data word + `OF`/`SF`/`PF`/`ZF`, `CF` kept) commutes through `ρ`. -/
theorem writeB4W_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (d : String) (t : B4W 64) :
    StateRel ρ (sL.writeB4W (ρ d) t) (sR.writeB4W d t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.writeB4W] using setReg_regs_rel hρ h.regs d t.word
  · simp [JState.writeB4W, h.flags]
  · intro b o; simpa [JState.writeB4W] using h.mem b o

/-- A `writeCFW` (data word + `CF`, the other four flags kept) commutes through `ρ`. -/
theorem writeCFW_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (d : String) (t : JFlag × BitVec 64) :
    StateRel ρ (sL.writeCFW (ρ d) t) (sR.writeCFW d t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.writeCFW] using setReg_regs_rel hρ h.regs d t.2
  · simp [JState.writeCFW, h.flags]
  · intro b o; simpa [JState.writeCFW] using h.mem b o

/-- A `writeB5N` (five flags of an operand-size op, no register) commutes through
    `ρ` without injectivity. -/
theorem writeB5N_rel {ρ : String → String} {sL sR : JState 64} {sz : Nat}
    (h : StateRel ρ sL sR) (t : B5W sz) :
    StateRel ρ (sL.writeB5N t) (sR.writeB5N t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n; simpa [JState.writeB5N] using h.regs n
  · simp [JState.writeB5N]
  · intro b o; simpa [JState.writeB5N] using h.mem b o

/-- A flag-only update applied to the (equal) flag states commutes through `ρ`
    without injectivity: the `CLC`/`STC`/`BT` writes. -/
theorem flagsWrite_rel {ρ : String → String} {sL sR : JState 64}
    (h : StateRel ρ sL sR) (setF : RFlags → RFlags) :
    StateRel ρ { sL with flags := setF sL.flags } { sR with flags := setF sR.flags } := by
  refine ⟨?_, ?_, ?_⟩
  · exact h.regs
  · simp [h.flags]
  · intro b o; exact h.mem b o

/-- A `writeB5W2` (five flags, high word to `dh`, low word to `dl`) commutes through
    `ρ`; when the two destinations coincide both sides keep the low word. -/
theorem writeB5W2_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (dh dl : String) (t : B5W2 64) :
    StateRel ρ (sL.writeB5W2 (ρ dh) (ρ dl) t) (sR.writeB5W2 dh dl t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simp only [JState.writeB5W2]
    by_cases hl : n = dl
    · subst hl; simp
    · have hl' : ρ n ≠ ρ dl := fun he => hl (hρ he)
      by_cases hh : n = dh
      · subst hh; simp [hl, hl']
      · have hh' : ρ n ≠ ρ dh := fun he => hh (hρ he)
        simp [hl, hl', hh, hh', h.regs n]
  · simp [JState.writeB5W2]
  · intro b o; simpa [JState.writeB5W2] using h.mem b o

/-- A memory store at `(ρ base, off)` vs `(base, off)` commutes through `ρ` when
    the stored values agree: register files and flags are untouched; the new
    memory stays `ρ`-related because `ρ b = ρ base ↔ b = base` (injectivity). -/
theorem store_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (base : String) (off : Int)
    (v : BitVec 64) :
    StateRel ρ (sL.store (ρ base) off v) (sR.store base off v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n; simpa [JState.store] using h.regs n
  · simp [JState.store, h.flags]
  · intro b o
    simp only [JState.store]
    by_cases hb : b = base
    · subst hb; by_cases ho : o = off <;> simp [ho, h.mem b o]
    · have hne : ρ b ≠ ρ base := fun he => hb (hρ he)
      simp [hb, hne, h.mem b o]

/-- A memory **load** read agrees under `ρ`: reading `[ρ base + off]` in `sL`
    equals reading `[base + off]` in `sR`. -/
theorem load_rel {ρ : String → String} {sL sR : JState 64}
    (h : StateRel ρ sL sR) (base : String) (off : Int) :
    sL.load (ρ base) off = sR.load base off := h.mem base off

/-- **One-step regalloc simulation.** For injective `ρ`, if `sL` and `sR` are
    `StateRel ρ`-related, then so are `evalInstr sL (renameInstr ρ i)` and
    `evalInstr sR i`, for every instruction `i`. The renaming commutes through the
    whole `evalInstr` step — register writes, flag writes, memory loads/stores,
    and the `MULX`/`ADCX`/`ADOX` double/flag writes. -/
theorem evalInstr_renameInstr_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (i : JInstr 64) :
    StateRel ρ (evalInstr sL (renameInstr ρ i)) (evalInstr sR i) := by
  have hreg := h.regs
  have hget : ∀ d, sL.get (ρ d) = sR.get d := fun d => by
    simpa [JState.get] using hreg d
  have hop : ∀ s : JOperand, (renameOperand ρ s).eval sL = s.eval sR :=
    fun s => renameOperand_eval h s
  have hcf : sL.flagB (·.cf) = sR.flagB (·.cf) := by simp [JState.flagB, h.flags]
  have hof : sL.flagB (·.of) = sR.flagB (·.of) := by simp [JState.flagB, h.flags]
  have hcond : ∀ c, sL.condB c = sR.condB c := fun c => by
    simp only [JState.condB, JState.flagB, h.flags]
  cases i with
  | mov d s =>
    simp only [renameInstr, evalInstr, hop]; exact setReg_rel hρ h d _
  | add d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | sub d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | adc d s =>
    simp only [renameInstr, evalInstr, hop, hget, hcf]; exact writeB5W_rel hρ h d _
  | sbb d s =>
    simp only [renameInstr, evalInstr, hop, hget, hcf]; exact writeB5W_rel hρ h d _
  | imul d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | neg d =>
    simp only [renameInstr, evalInstr, hget]; exact writeB5W_rel hρ h d _
  | setc d =>
    -- `setc d := if CF then 1 else 0`: a `setReg` whose written value depends only
    -- on CF (equal in sL/sR by `hcf`), so the renaming commutes via `setReg_rel`.
    simp only [renameInstr, evalInstr, hcf]; exact setReg_rel hρ h d _
  | and_ d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | test a s =>
    -- flags only: `writeB5_rel` needs no destination and no injectivity.
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5_rel h _
  | cmp a s =>
    -- as `test`: the five flags of `a - s` and no register write.
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5_rel h _
  | not_ d =>
    simp only [renameInstr, evalInstr, hget]; exact setReg_rel hρ h d _
  | andn d a b =>
    simp only [renameInstr, evalInstr, hget]; exact writeB5W_rel hρ h d _
  | rol d amt =>
    -- `OF`/`CF` come from the `B2W`; `SF`/`PF`/`ZF` are inherited from the
    -- pre-state, which `writeB2W_rel` carries through `h.flags`.
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB2W_rel hρ h d _
  | ror d amt =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB2W_rel hρ h d _
  | rorx d src amt =>
    simp only [renameInstr, evalInstr, hop, hget]; exact setReg_rel hρ h d _
  | shlx d src c =>
    simp only [renameInstr, evalInstr, hget]; exact setReg_rel hρ h d _
  | shrx d src c =>
    simp only [renameInstr, evalInstr, hget]; exact setReg_rel hρ h d _
  | sarx d src c =>
    simp only [renameInstr, evalInstr, hget]; exact setReg_rel hρ h d _
  | movzx d sw src =>
    simp only [renameInstr, evalInstr, hget]; exact setReg_rel hρ h d _
  | movsx d sw src =>
    simp only [renameInstr, evalInstr, hget]; exact setReg_rel hρ h d _
  | lea d base idx scale off =>
    -- the address is computed from the two renamed base/index registers, whose
    -- values agree by `hget`; no memory is touched.
    simp only [renameInstr, evalInstr, hget]; exact setReg_rel hρ h d _
  | or_ d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | xor_ d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | shl d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | shr d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | sar d s =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | cmove d s =>
    simp only [renameInstr, evalInstr, hop, hget]
    rw [show sL.flagB (·.zf) = sR.flagB (·.zf) from by simp [JState.flagB, h.flags]]
    exact setReg_rel hρ h d _
  | cmovne d s =>
    simp only [renameInstr, evalInstr, hop, hget]
    rw [show sL.flagB (·.zf) = sR.flagB (·.zf) from by simp [JState.flagB, h.flags]]
    exact setReg_rel hρ h d _
  | cmovb d s =>
    simp only [renameInstr, evalInstr, hop, hget, hcf]; exact setReg_rel hρ h d _
  | mulx dh dl a b =>
    simp only [renameInstr, evalInstr, hop]
    exact setReg2_rel hρ h dl dh _ _
  | mulxMem dh dl a base off =>
    simp only [renameInstr, evalInstr, hop, load_rel h base off]
    exact setReg2_rel hρ h dl dh _ _
  | adcx d s =>
    simp only [renameInstr, evalInstr, hop, hget, hcf]
    exact adcWrite_rel hρ h d _ (fun fl => { fl with cf := _ })
  | adox d s =>
    simp only [renameInstr, evalInstr, hop, hget, hof]
    exact adcWrite_rel hρ h d _ (fun fl => { fl with of := _ })
  | loadMem d base off =>
    simp only [renameInstr, evalInstr, load_rel h base off]
    exact setReg_rel hρ h d _
  | storeMem base off s =>
    simp only [renameInstr, evalInstr, hop]
    exact store_rel hρ h base off _
  | loadMemIdx d base idx scale =>
    -- `loadIdx base idx scale = load base (scale·(get idx).toNat)`; the index
    -- register value agrees in sL/sR (`hget`), so the effective offsets agree and
    -- `load_rel` carries the read through the renaming.
    simp only [renameInstr, evalInstr, JState.loadIdx, hget idx,
      load_rel h base (scale * (sR.get idx).toNat)]
    exact setReg_rel hρ h d _
  | storeMemIdx base idx scale s =>
    simp only [renameInstr, evalInstr, JState.storeIdx, hop, hget idx]
    exact store_rel hρ h base (scale * (sR.get idx).toNat) _
  | loadSym d sym =>
    -- `loadSym (ρ d) (ρ sym)` vs `loadSym d sym`: both write a fixed marker into
    -- their dst register and re-alias dst's memory bank onto the symbol's. Flags
    -- are untouched; registers commute via injectivity; the memory aliasing tracks
    -- through `MemRel` because the symbol base is carried by `ρ` (so the aliased
    -- read `sL.mem (ρ sym) o = sR.mem sym o` is exactly `h.mem sym o`).
    simp only [renameInstr, evalInstr]
    refine ⟨?_, h.flags, ?_⟩
    · intro n
      by_cases hn : n = d
      · subst hn; simp
      · have hne : ρ n ≠ ρ d := fun he => hn (hρ he)
        simp [hne, hn, h.regs n]
    · intro b o
      by_cases hbd : b = d
      · -- the aliased base: both banks now read the symbol's table; `ρ b = ρ d`
        -- on the left, `b = d` on the right, and `sL.mem (ρ sym) o = sR.mem sym o`
        -- is `h.mem sym o`.
        subst hbd; simp [h.mem sym o]
      · have hne : ρ b ≠ ρ d := fun he => hbd (hρ he)
        simp [hne, hbd, h.mem b o]
  | inc d =>
    simp only [renameInstr, evalInstr, hget]; exact writeB4W_rel hρ h d _
  | dec d =>
    simp only [renameInstr, evalInstr, hget]; exact writeB4W_rel hρ h d _
  | clc =>
    simp only [renameInstr, evalInstr]; exact flagsWrite_rel h (fun fl => { fl with cf := _ })
  | stc =>
    simp only [renameInstr, evalInstr]; exact flagsWrite_rel h (fun fl => { fl with cf := _ })
  | xchg a b =>
    simp only [renameInstr, evalInstr, x86_XCHG, hget]; exact setReg2_rel hρ h a b _ _
  | imulri d src imm =>
    simp only [renameInstr, evalInstr, hget]; exact writeB5W_rel hρ h d _
  | mul dh dl src =>
    simp only [renameInstr, evalInstr, hget]; exact writeB5W2_rel hρ h dh dl _
  | imulWide dh dl src =>
    simp only [renameInstr, evalInstr, hget]; exact writeB5W2_rel hρ h dh dl _
  | shld d src amt =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | shrd d src amt =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5W_rel hρ h d _
  | rcl d amt =>
    simp only [renameInstr, evalInstr, hop, hget, hcf]; exact writeB2W_rel hρ h d _
  | rcr d amt =>
    simp only [renameInstr, evalInstr, hop, hget, hcf]; exact writeB2W_rel hρ h d _
  | cmovcc c d s =>
    simp only [renameInstr, evalInstr, hop, hget, hcond c]; exact setReg_rel hρ h d _
  | setcc c d =>
    simp only [renameInstr, evalInstr, JState.setRegMerge, hget, hcond c]
    exact setReg_rel hρ h d _
  | testN sz a b =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeB5N_rel h _
  | bt a b =>
    simp only [renameInstr, evalInstr, hop, hget]
    exact flagsWrite_rel h (fun fl => { fl with cf := _ })
  | btr d b =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeCFW_rel hρ h d _
  | bts d b =>
    simp only [renameInstr, evalInstr, hop, hget]; exact writeCFW_rel hρ h d _
  | addMem d base off =>
    simp only [renameInstr, evalInstr, hget, load_rel h base off]; exact writeB5W_rel hρ h d _
  | addToMem base off s =>
    simp only [renameInstr, evalInstr, JState.writeB5Mem, hop, load_rel h base off]
    exact store_rel hρ (writeB5_rel h _) base off _
  | adcxMem d base off =>
    simp only [renameInstr, evalInstr, hget, hcf, load_rel h base off]
    exact adcWrite_rel hρ h d _ (fun fl => { fl with cf := _ })
  | adoxMem d base off =>
    simp only [renameInstr, evalInstr, hget, hof, load_rel h base off]
    exact adcWrite_rel hρ h d _ (fun fl => { fl with of := _ })
  | imulMem d base off =>
    simp only [renameInstr, evalInstr, hget, load_rel h base off]; exact writeB5W_rel hρ h d _
  | imulriMem d base off imm =>
    simp only [renameInstr, evalInstr, load_rel h base off]; exact writeB5W_rel hρ h d _
  | cmpMem a base off =>
    simp only [renameInstr, evalInstr, hget, load_rel h base off]; exact writeB5_rel h _
  | cmovccMem c d base off =>
    simp only [renameInstr, evalInstr, hget, hcond c, load_rel h base off]
    exact setReg_rel hρ h d _
  | aluMem op d base off =>
    simp only [renameInstr, evalInstr, hget, load_rel h base off]; exact writeB5W_rel hρ h d _
  | andnMem d a base off =>
    simp only [renameInstr, evalInstr, hget, load_rel h base off]; exact writeB5W_rel hρ h d _
  | bzhi d src idx =>
    simp only [renameInstr, evalInstr, hget]; exact writeB5W_rel hρ h d _

/-! ## 5. The whole-block translation validation (the contribution)

By folding §4 over the block, an injective renaming `ρ` carries the
`StateRel ρ` simulation through `runBlock`: running the renamed block from any
`ρ`-related state lands `ρ`-related with the original run. This is the in-Lean
certificate that a register-allocation renaming preserves the machine semantics,
**replacing** CryptOpt's external equivalence checker for the RA dimension. It is
proved for **all** blocks and **all** related state pairs (not a concrete-block
check). -/

/-- **Block-level regalloc simulation.** For injective `ρ`, `StateRel ρ` is
    preserved by `runBlock` of the renamed block vs the original block. -/
theorem runBlock_renameBlock_rel {ρ : String → String} (hρ : Function.Injective ρ)
    {sL sR : JState 64} (h : StateRel ρ sL sR) (block : List (JInstr 64)) :
    StateRel ρ (runBlock sL (renameBlock ρ block)) (runBlock sR block) := by
  induction block generalizing sL sR with
  | nil => simpa [renameBlock] using h
  | cons i is ih =>
    simp only [renameBlock, List.map_cons, runBlock_cons]
    exact ih (evalInstr_renameInstr_rel hρ h i)

/-! ### The reflexive instance: `StateRel ρ (renameState ρ s) s`

To turn the simulation into a usable "feed the renamed state in, get the renamed
state out" statement we need a concrete `renameState ρ s` that is `StateRel ρ`-
related to `s`. For an injective `ρ` with a chosen left inverse `σ` (`σ (ρ n) =
n`), `renameState` precomposes the register file and memory base with `σ`. -/

/-- The renamed initial state for an injective `ρ` with left inverse `σ`
    (`σ ∘ ρ = id`): physical register `r` holds what the original held in `σ r`,
    so the value originally in `n` now sits in `ρ n`. Memory base names are mapped
    the same way; flags are copied verbatim. -/
def renameState (σ : String → String) {w : Nat} (s : JState w) : JState w :=
  { regs := fun r => s.regs (σ r)
    flags := s.flags
    mem := fun b o => s.mem (σ b) o }

/-- `renameState σ s` is `StateRel ρ`-related to `s` whenever `σ` is a left inverse
    of `ρ`. This is the canonical witness fed to the block-level theorem. -/
theorem stateRel_renameState {ρ σ : String → String}
    (hσ : Function.LeftInverse σ ρ) {w : Nat} (s : JState w) :
    StateRel ρ (renameState σ s) s := by
  refine ⟨?_, rfl, ?_⟩
  · intro n; simp [renameState, hσ n]
  · intro b o; simp [renameState, hσ b]

/-- **Regalloc TV (machine-state level).** For an injective renaming `ρ` with left
    inverse `σ`, running the renamed block from the `σ`-renamed initial state lands
    in the same simulation as running the original block: for every register name
    `n`, the renamed run's `ρ n` equals the original run's `n`, the flags are
    equal, and memory corresponds under `ρ`. The register allocation is sound —
    "which physical holds which value" is the bijection `ρ`, and the post-states
    agree up to it, for all inputs. -/
theorem regalloc_runBlock_sound {ρ σ : String → String}
    (hρ : Function.Injective ρ) (hσ : Function.LeftInverse σ ρ)
    (block : List (JInstr 64)) (s : JState 64) :
    StateRel ρ (runBlock (renameState σ s) (renameBlock ρ block)) (runBlock s block) :=
  runBlock_renameBlock_rel hρ (stateRel_renameState hσ s) block

/-! ## 6. Lifted to the dialect: equal `Com` denotation modulo the renaming

Through `X86Dialect.lowerBlock_denote_closed`, the machine-state simulation above
becomes a statement about the lowered `Com`s' denotations: the lowering of the
renamed block, denoted on the renamed initial state, is `StateRel ρ`-related to
the lowering of the original block on the original state. This is the
denotation-preserving statement for the RA dimension, the dialect-level form of
the in-Lean equivalence certificate. -/

/-- **Regalloc TV (dialect/`Com` level).** The lowered `Com` of the renamed block
    (denoted on the renamed state) and the lowered `Com` of the original block
    (denoted on the original state) are `StateRel ρ`-related on every input — the
    register-allocation renaming preserves denotation against the validated x86
    model, up to the physical-register bijection `ρ`. -/
theorem regalloc_lowering_sound {ρ σ : String → String}
    (hρ : Function.Injective ρ) (hσ : Function.LeftInverse σ ρ)
    (block : List (JInstr 64)) (s : JState 64) :
    StateRel ρ
      ((lowerBlock (Γ := []) (renameBlock ρ block)).denote (.cons (renameState σ s) .nil))
      ((lowerBlock (Γ := []) block).denote (.cons s .nil)) := by
  rw [lowerBlock_denote_closed (renameBlock ρ block) (renameState σ s),
      lowerBlock_denote_closed block s]
  exact regalloc_runBlock_sound hρ hσ block s

/-! ## 7. The randomized register-allocation pass

A register-allocation choice is a renaming of the block's live names. The
deterministic baseline `AsmPrinter.allocGp` is first-fit. The randomized pass
draws a seeded permutation of the free pool and assigns names to it, exactly the
CryptOpt RA search move; the **acceptance check** keeps only renamings that fit
the pool (no overflow / no two names collapsing).

A renaming here is realised as the function induced by an assignment association
list `assign : List (String × String)` (name → physical), defaulting to identity
off the list. The pass is `Com→Com` once composed with `lowerBlock`. -/

/-- A tiny LCG (Numerical Recipes constants) over `UInt32` — the same generator
    the schedule-search pass uses, for a shared randomness source. -/
def lcgNext (s : UInt32) : UInt32 := s * 1664525 + 1013904223

/-- Fisher–Yates-style seeded shuffle of a list, driven by the LCG. Returns the
    permuted list. (Used to randomise which free pool register each name gets.) -/
def shuffle {α : Type} (seed : UInt32) : List α → List α
  | [] => []
  | xs =>
    let rec go (s : UInt32) (acc rem : List α) (fuel : Nat) : List α :=
      match fuel, rem with
      | 0, _ => acc ++ rem
      | _, [] => acc
      | fuel+1, _ =>
        let s' := lcgNext s
        let k := s'.toNat % rem.length
        match rem[k]? with
        | none => acc ++ rem
        | some x => go s' (acc ++ [x]) (rem.eraseIdx k) fuel
    go seed [] xs xs.length

/-- The randomized register assignment: take the block's free (non-pinned) names,
    pair them with a **seeded shuffle** of the available GP pool. This is a
    randomized linear-scan with random physical-register tie-breaks — a CryptOpt RA
    move. `pinned` fixes ABI argument registers as in `AsmPrinter.allocGp`. -/
def searchAssign (pinned : GpAlloc) (block : List (JInstr 64)) (seed : UInt32) :
    GpAlloc :=
  let used := pinned.map Prod.snd
  let pool := gpPool.filter (fun r => ¬ used.contains r)
  let free := gpFreeNames pinned block
  pinned ++ (free.zip (shuffle seed pool))

/-- The renaming a `GpAlloc` induces: name ↦ assigned physical (`%rN`), identity
    off the assignment. This is what `renameBlock`/`renameState` act by. -/
def assignRenaming (assign : GpAlloc) (n : String) : String :=
  (assign.lookup n).getD n

/-- **Acceptance check** (the in-Lean gate replacing CryptOpt's external checker
    precondition). A candidate assignment is accepted iff:
    (a) it leaves no name unallocated / spilled — `allocOverflow = none` for the
        first-fit budget over the same block (the overflow guard), and
    (b) the assigned physicals are pairwise distinct on the block's names (the
        induced renaming is injective on the live set — no two virtuals collapse
        onto one physical, which would break the simulation).
    Only renamings passing this check are fed to the §5/§6 TV theorems. -/
def accept (pinned assign : GpAlloc) (block : List (JInstr 64)) : Bool :=
  (allocOverflow pinned block).isNone &&
  (let names := blockNames block
   let phys := names.map (assignRenaming assign)
   phys.Nodup)

/-! ## 8. Headroom: which suite kernels can the pass help?

A renaming can only spread mul-output names across
distinct physicals if there are free physicals to spread into — `gpFreeSlots`
beyond the names the block already needs (`gpFreeNames.length`). fe25519/s2n-class
kernels have **zero** such headroom. The small
straight-line kernels in the suite have ample headroom, recorded below.

`add2Block` (`Add2Kernel`): 4 live names `{a0,a1,b0,b1}`, no pinned regs, so 14
free GP slots — 10 spare. `MpnLinearKernels.addBlock` streams through a constant
5-name window `{r,a,b,t0,t1}` for any limb count, pinning the 3 pointers, leaving
ample slots for the 2 scratch names. Both admit an overflow-free randomized
renaming. -/

-- @bench-only: the `List (JInstr _)` blocks below are fixtures exercising this
-- randomized register-allocation pass; this module emits no deployed `.s` artifact.
/-- The two-limb add kernel (verbatim `Add2Kernel.add2Block`) — a headroom target. -/
def add2Block : List (JInstr 64) :=
  [ .add "a0" (.reg "b0")
  , .adc "a1" (.reg "b1") ]

/-- `add2Block` needs only its 4 live names; with no pinned registers the GP pool
    leaves 14 slots — 10 of headroom. The randomized renaming has room to place
    the names on any of the 14 physicals. -/
theorem add2_headroom :
    (gpFreeNames [] add2Block).length = 4 ∧ gpFreeSlots [] = 14 := by
  native_decide

/-- With that headroom, first-fit allocation does **not** overflow: the budget
    guard passes, so a randomized renaming over the same pool is acceptable. -/
theorem add2_no_overflow : allocOverflow [] add2Block = none := by native_decide

/-- A concrete randomized renaming of `add2Block` is **accepted** by the pass:
    the seeded shuffle assigns the four names four distinct physicals with no
    overflow. (Seed `0xC0FFEE` is arbitrary; the theorem pins one accepted draw.) -/
theorem add2_searchAssign_accepted :
    accept [] (searchAssign [] add2Block 0xC0FFEE) add2Block = true := by
  native_decide

/-- The renaming the accepted draw induces is injective on the block's live names
    (the precondition the §5 TV theorem consumes) — distinct names → distinct
    physicals, so `assignRenaming` restricted to the live set has no collisions. -/
theorem add2_searchAssign_nodup :
    ((blockNames add2Block).map
        (assignRenaming (searchAssign [] add2Block 0xC0FFEE))).Nodup := by
  native_decide

/-- The pinned-pointer streaming add kernel (`MpnLinearKernels.addStep`, one limb)
    as a standalone headroom probe: it pins the 3 pointer registers and uses 2
    scratch names, leaving 11 free slots — 9 of headroom. -/
def addStep (i : Nat) : List (JInstr 64) :=
  [ .loadMem "t0" "a" (8 * i)
  , .loadMem "t1" "b" (8 * i)
  , (if i = 0 then .add "t0" (.reg "t1") else .adc "t0" (.reg "t1"))
  , .storeMem "r" (8 * i) (.reg "t0") ]

/-- The System-V pointer pins for the streaming kernels (`r`→`%rdi`, `a`→`%rsi`,
    `b`→`%rdx`), mirroring `MpnLinearKernels.ptrPinned`. -/
def ptrPinned : GpAlloc := [("r", "%rdi"), ("a", "%rsi"), ("b", "%rdx")]

/-- The streaming add block uses exactly the 2 scratch names `{t0,t1}` beyond the
    3 pinned pointers, for any limb count — constant register pressure. Pinning the
    3 pointers leaves 11 free pool slots, so the 2 scratch names have 9 of headroom
    and the budget never overflows. Recorded at representative `n = 4` and
    `n = 16` (the pressure is `n`-independent — same 2 names at every limb). -/
theorem addStep_headroom :
    gpFreeSlots ptrPinned = 11
      ∧ (gpFreeNames ptrPinned ((List.range 4).flatMap addStep)).length = 2
      ∧ (gpFreeNames ptrPinned ((List.range 16).flatMap addStep)).length = 2 := by
  native_decide

/-- The streaming add block over 16 limbs allocates without overflow under the
    pointer pins — the budget guard passes, so a randomized scratch-name renaming
    is acceptable. -/
theorem addStep_no_overflow :
    allocOverflow ptrPinned ((List.range 16).flatMap addStep) = none := by native_decide
end CatCrypt.Crypto.Optimizer.RandomizedRegAlloc