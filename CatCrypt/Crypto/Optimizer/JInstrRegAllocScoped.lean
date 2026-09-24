/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated

/-!
# Name-scoped register-allocation simulation for the x86 (`JInstr`) backend

`RandomizedRegAlloc.evalInstr_renameInstr_rel` proves the `JState` register-rename
simulation assuming the renaming `ρ` is **globally** injective. The decidable
no-alias checker (`JInstrRegAllocValidated.noAliasX`) only ever establishes
injectivity on the **register names the block mentions** (`blockNamesX`). This
file re-proves the simulation in that scoped form — `RenInjOn ns ρ` in place of
`Function.Injective ρ`, with `∈ ns` side-conditions on the written/read names —
so the checker's certificate is exactly what the soundness theorem consumes. This
is the x86 analogue of the generic `GenericRegAlloc.renameBlock_runBlock_on`
theorem, carried through the x86 `StateRel` simulation (memory + flags +
`mulx`'s two destinations).

The scoped carrier is `StateRelOn ns ρ`: registers agree at `ρ n` with the source
at `n` for `n ∈ ns`, flags agree, and memory cell `(ρ b, o)` agrees with `(b, o)`
for `b ∈ ns`. Each helper lemma replaces global injectivity with `RenInjOn ns ρ`
and the relevant `∈ ns` membership facts; the 28-case step lemma derives those
memberships from `hsub : ∀ n ∈ bNamesX i, n ∈ ns` (the block's written++read
names, the same list `noAliasX` checks).

## The `loadSym` scope

`loadSym d sym` aliases `d`'s memory bank onto the `.rodata` label `sym`. Its
`SpillingRegAlloc.readNames` is `[]` — `sym` is a fixed link-time label, **not** a
program register name — so `sym ∉ bNamesX`. For the scoped *memory* relation to
carry through the aliasing read (`sL.mem (ρ sym) o = sR.mem sym o`) we need
`sym ∈ ns`; that fact lies outside the block-names certificate. The step
lemma therefore takes an explicit `loadSym`-only hypothesis (`hsym`) supplying it.
The block driver threads it via `bNamesXsym`, the block names *augmented with each
`loadSym`'s symbol*; the top theorem scopes to `blockNamesXsym block` and
`noAliasX` is strengthened to that set by `noAliasXsym`. Blocks without `loadSym`
have `blockNamesXsym = blockNamesX`, so nothing changes for them.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
open CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated

/-! ## 1. The name-scoped simulation relation -/

/-- The name-scoped register-rename simulation: like `StateRel`, but registers and
    memory are only required to agree on the names `ns`. Flags agree verbatim. -/
structure StateRelOn (ns : List String) (ρ : String → String) {w : Nat}
    (sL sR : JState w) : Prop where
  regsOn : ∀ n ∈ ns, sL.regs (ρ n) = sR.regs n
  flags  : sL.flags = sR.flags
  memOn  : ∀ b ∈ ns, ∀ o, sL.mem (ρ b) o = sR.mem b o

/-! ## 2. Operand evaluation respects the renaming, scoped -/

/-- An operand evaluated in the renamed state equals it evaluated in the source,
    provided the operand's read names lie in `ns` (so the register read agrees). -/
theorem renameOperand_eval_on {ns : List String} {ρ : String → String} {w : Nat}
    {sL sR : JState w} (h : StateRelOn ns ρ sL sR) (op : JOperand)
    (hsub : ∀ n ∈ srcNames op, n ∈ ns) :
    (renameOperand ρ op).eval sL = op.eval sR := by
  cases op with
  | reg r =>
    have hr : r ∈ ns := hsub r (by simp [srcNames])
    simp [renameOperand, JOperand.eval, JState.get, h.regsOn r hr]
  | imm v => rfl

/-! ## 3. The scoped write helpers (`RenInjOn` in place of global injectivity) -/

/-- The register file after a `setReg`-style write commutes through `ρ` on `ns`:
    if `sL`, `sR` register files are `ρ`-related on `ns` and `d ∈ ns`, then writing
    `v` to `ρ d` resp. `d` keeps them `ρ`-related on `ns`. Uses `RenInjOn` to get
    `ρ n ≠ ρ d` from `n ≠ d` with both in `ns`. -/
theorem setReg_regs_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64}
    (hr : ∀ n ∈ ns, sL.regs (ρ n) = sR.regs n) (d : String) (hd : d ∈ ns)
    (v : BitVec 64) :
    ∀ n ∈ ns, (fun r' => if r' = ρ d then v else sL.regs r') (ρ n)
        = (fun r' => if r' = d then v else sR.regs r') n := by
  intro n hn
  by_cases hnd : n = d
  · subst hnd; simp
  · have hne : ρ n ≠ ρ d := fun he => hnd (hinj n hn d hd he)
    simp [hne, hnd, hr n hn]

/-- A `writeB5W` commutes through `ρ` on `ns` (needs `d ∈ ns`). -/
theorem writeB5W_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (d : String) (hd : d ∈ ns) (t : B5W 64) :
    StateRelOn ns ρ (sL.writeB5W (ρ d) t) (sR.writeB5W d t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.writeB5W] using setReg_regs_rel_on hinj h.regsOn d hd t.word
  · simp [JState.writeB5W]
  · intro b hb o; simpa [JState.writeB5W] using h.memOn b hb o

/-- A `writeB5` commutes through `ρ` on `ns`. It writes only the five flags, so no
    name has to be in scope and no injectivity is needed. -/
theorem writeB5_rel_on {ns : List String} {ρ : String → String}
    {sL sR : JState 64} (h : StateRelOn ns ρ sL sR) (t : B5W 64) :
    StateRelOn ns ρ (sL.writeB5 t) (sR.writeB5 t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn; simpa [JState.writeB5] using h.regsOn n hn
  · simp [JState.writeB5]
  · intro b hb o; simpa [JState.writeB5] using h.memOn b hb o

/-- A `writeB2W` commutes through `ρ` on `ns` (needs `d ∈ ns`). The `SF`/`PF`/`ZF`
    the rotate keeps are inherited from the pre-states, which agree. -/
theorem writeB2W_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (d : String) (hd : d ∈ ns) (t : B2W 64) :
    StateRelOn ns ρ (sL.writeB2W (ρ d) t) (sR.writeB2W d t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.writeB2W] using setReg_regs_rel_on hinj h.regsOn d hd t.word
  · simp [JState.writeB2W, h.flags]
  · intro b hb o; simpa [JState.writeB2W] using h.memOn b hb o

/-- A `setReg` commutes through `ρ` on `ns` (needs `d ∈ ns`). -/
theorem setReg_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (d : String) (hd : d ∈ ns) (v : BitVec 64) :
    StateRelOn ns ρ (sL.setReg (ρ d) v) (sR.setReg d v) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.setReg] using setReg_regs_rel_on hinj h.regsOn d hd v
  · simp [JState.setReg, h.flags]
  · intro b hb o; simpa [JState.setReg] using h.memOn b hb o

/-- A double `setReg` (the `MULX` write of `(lo, hi)`) commutes through `ρ` on `ns`
    (needs both `dl, dh ∈ ns`). -/
theorem setReg2_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (dl dh : String) (hdl : dl ∈ ns) (hdh : dh ∈ ns) (lo hi : BitVec 64) :
    StateRelOn ns ρ ((sL.setReg (ρ dl) lo).setReg (ρ dh) hi)
      ((sR.setReg dl lo).setReg dh hi) :=
  setReg_rel_on hinj (setReg_rel_on hinj h dl hdl lo) dh hdh hi

/-- An `ADCX`/`ADOX`-style write of one data register plus one flag, scoped to `ns`
    (needs `d ∈ ns`). -/
theorem adcWrite_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (d : String) (hd : d ∈ ns) (res : BitVec 64) (setF : RFlags → RFlags) :
    StateRelOn ns ρ
      { regs := fun r' => if r' = ρ d then res else sL.regs r'
        flags := setF sL.flags, mem := sL.mem }
      { regs := fun r' => if r' = d then res else sR.regs r'
        flags := setF sR.flags, mem := sR.mem } := by
  refine ⟨?_, ?_, ?_⟩
  · exact setReg_regs_rel_on hinj h.regsOn d hd res
  · simp [h.flags]
  · intro b hb o; exact h.memOn b hb o

/-- A memory store at `(ρ base, off)` vs `(base, off)` commutes through `ρ` on `ns`
    (needs `base ∈ ns`); uses `RenInjOn` for the `b ≠ base` cell. -/
theorem store_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (base : String) (hbase : base ∈ ns) (off : Int) (v : BitVec 64) :
    StateRelOn ns ρ (sL.store (ρ base) off v) (sR.store base off v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn; simpa [JState.store] using h.regsOn n hn
  · simp [JState.store, h.flags]
  · intro b hb o
    simp only [JState.store]
    by_cases hbb : b = base
    · subst hbb; by_cases ho : o = off <;> simp [ho, h.memOn b hb o]
    · have hne : ρ b ≠ ρ base := fun he => hbb (hinj b hb base hbase he)
      simp [hbb, hne, h.memOn b hb o]

/-- A memory **load** read agrees under `ρ` on `ns` (needs `base ∈ ns`). -/
theorem load_rel_on {ns : List String} {ρ : String → String} {sL sR : JState 64}
    (h : StateRelOn ns ρ sL sR) (base : String) (hbase : base ∈ ns) (off : Int) :
    sL.load (ρ base) off = sR.load base off := h.memOn base hbase off

/-- A `writeB4W` (data word + `OF`/`SF`/`PF`/`ZF`, `CF` kept) commutes through `ρ` on
    `ns` (needs `d ∈ ns`). -/
theorem writeB4W_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (d : String) (hd : d ∈ ns) (t : B4W 64) :
    StateRelOn ns ρ (sL.writeB4W (ρ d) t) (sR.writeB4W d t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.writeB4W] using setReg_regs_rel_on hinj h.regsOn d hd t.word
  · simp [JState.writeB4W, h.flags]
  · intro b hb o; simpa [JState.writeB4W] using h.memOn b hb o

/-- A `writeCFW` (data word + `CF`, the other four flags kept) commutes through `ρ` on
    `ns` (needs `d ∈ ns`). -/
theorem writeCFW_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (d : String) (hd : d ∈ ns) (t : JFlag × BitVec 64) :
    StateRelOn ns ρ (sL.writeCFW (ρ d) t) (sR.writeCFW d t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [JState.writeCFW] using setReg_regs_rel_on hinj h.regsOn d hd t.2
  · simp [JState.writeCFW, h.flags]
  · intro b hb o; simpa [JState.writeCFW] using h.memOn b hb o

/-- A `writeB5N` (five flags of an operand-size op, no register) commutes through `ρ`
    on `ns` with no name in scope and no injectivity. -/
theorem writeB5N_rel_on {ns : List String} {ρ : String → String}
    {sL sR : JState 64} {sz : Nat} (h : StateRelOn ns ρ sL sR) (t : B5W sz) :
    StateRelOn ns ρ (sL.writeB5N t) (sR.writeB5N t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn; simpa [JState.writeB5N] using h.regsOn n hn
  · simp [JState.writeB5N]
  · intro b hb o; simpa [JState.writeB5N] using h.memOn b hb o

/-- A flag-only update applied to the (equal) flag states commutes through `ρ` on `ns`:
    the `clc`/`stc`/`bt` writes. -/
theorem flagsWrite_rel_on {ns : List String} {ρ : String → String}
    {sL sR : JState 64} (h : StateRelOn ns ρ sL sR) (setF : RFlags → RFlags) :
    StateRelOn ns ρ { sL with flags := setF sL.flags } { sR with flags := setF sR.flags } := by
  refine ⟨?_, ?_, ?_⟩
  · exact h.regsOn
  · simp [h.flags]
  · intro b hb o; exact h.memOn b hb o

/-- A `writeB5W2` (five flags, high word to `dh`, low word to `dl`) commutes through `ρ`
    on `ns` (needs `dh, dl ∈ ns`); when the two destinations coincide both sides keep
    the low word. -/
theorem writeB5W2_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (dh dl : String) (hdh : dh ∈ ns) (hdl : dl ∈ ns) (t : B5W2 64) :
    StateRelOn ns ρ (sL.writeB5W2 (ρ dh) (ρ dl) t) (sR.writeB5W2 dh dl t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    simp only [JState.writeB5W2]
    by_cases hl : n = dl
    · subst hl; simp
    · have hl' : ρ n ≠ ρ dl := fun he => hl (hinj n hn dl hdl he)
      by_cases hh : n = dh
      · subst hh; simp [hl, hl']
      · have hh' : ρ n ≠ ρ dh := fun he => hh (hinj n hn dh hdh he)
        simp [hl, hl', hh, hh', h.regsOn n hn]
  · simp [JState.writeB5W2]
  · intro b hb o; simpa [JState.writeB5W2] using h.memOn b hb o

/-! ## 4. The scoped names of an instruction / block

For every constructor except `loadSym`, the names the step lemma needs are exactly
`bNamesX i = writtenNames i ++ readNames i`. `loadSym d sym` additionally aliases
memory onto the label `sym`, whose memory cell the scoped relation must cover, so
we augment its name list with `sym`. -/

/-- The register/label names the *scoped simulation* needs for one instruction:
    `bNamesX i`, plus the `.rodata` label for a `loadSym` (whose memory bank is
    aliased and so must be in the scoped memory relation). -/
def bNamesXsym (i : JInstr 64) : List String :=
  match i with
  | .loadSym _ sym => sym :: bNamesX i
  | _ => bNamesX i

/-- `bNamesX i ⊆ bNamesXsym i` always. -/
theorem mem_bNamesXsym_of_bNamesX (i : JInstr 64) {n : String}
    (hn : n ∈ bNamesX i) : n ∈ bNamesXsym i := by
  cases i <;> simp_all [bNamesXsym]

/-- Every scoped name a block mentions. -/
def blockNamesXsym (block : List (JInstr 64)) : List String :=
  block.flatMap bNamesXsym

/-! ## 5. The one-step scoped simulation lemma (the heart) -/

/-- **One-step scoped regalloc simulation.** For `ρ` injective on `ns`, if `sL` and
    `sR` are `StateRelOn ns ρ`-related and every name `bNamesXsym i` mentions lies
    in `ns`, then `evalInstr sL (renameInstr ρ i)` and `evalInstr sR i` are
    `StateRelOn ns ρ`-related. Mirrors `evalInstr_renameInstr_rel`, deriving every
    `d ∈ ns` / `base ∈ ns` / read-name `∈ ns` from `hsub`. -/
theorem evalInstr_renameInstr_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (i : JInstr 64) (hsub : ∀ n ∈ bNamesXsym i, n ∈ ns) :
    StateRelOn ns ρ (evalInstr sL (renameInstr ρ i)) (evalInstr sR i) := by
  -- scoped read-register agreement: `sL.get (ρ d) = sR.get d` for `d ∈ ns`
  have hget_on : ∀ d ∈ ns, sL.get (ρ d) = sR.get d := fun d hd => by
    simpa [JState.get] using h.regsOn d hd
  -- scoped operand agreement, given the operand's source names are in `ns`
  have hop_on : ∀ s : JOperand, (∀ n ∈ srcNames s, n ∈ ns) →
      (renameOperand ρ s).eval sL = s.eval sR :=
    fun s hs => renameOperand_eval_on h s hs
  have hcf : sL.flagB (·.cf) = sR.flagB (·.cf) := by simp [JState.flagB, h.flags]
  have hof : sL.flagB (·.of) = sR.flagB (·.of) := by simp [JState.flagB, h.flags]
  have hzf : sL.flagB (·.zf) = sR.flagB (·.zf) := by simp [JState.flagB, h.flags]
  have hcond : ∀ c, sL.condB c = sR.condB c := fun c => by
    simp only [JState.condB, JState.flagB, h.flags]
  -- `hsub` specialised through `bNamesX` (for the non-loadSym cases)
  have hsubX : ∀ n ∈ bNamesX i, n ∈ ns :=
    fun n hn => hsub n (mem_bNamesXsym_of_bNamesX i hn)
  cases i with
  | mov d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs]; exact setReg_rel_on hinj h d hd _
  | add d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | sub d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | adc d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd, hcf]
    exact writeB5W_rel_on hinj h d hd _
  | sbb d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd, hcf]
    exact writeB5W_rel_on hinj h d hd _
  | imul d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | neg d =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    simp only [renameInstr, evalInstr, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | setc d =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    simp only [renameInstr, evalInstr, hcf]; exact setReg_rel_on hinj h d hd _
  | and_ d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | test a s =>
    -- `test` has no destination: `a` is a *read* name, and the write is flags only.
    have ha : a ∈ ns := hsubX a (by simp [bNamesX, SpillingRegAlloc.writtenNames,
      SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.writtenNames,
        SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on a ha]
    exact writeB5_rel_on h _
  | cmp a s =>
    -- as `test`: `a` is a read name and the write is flags only.
    have ha : a ∈ ns := hsubX a (by simp [bNamesX, SpillingRegAlloc.writtenNames,
      SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.writtenNames,
        SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on a ha]
    exact writeB5_rel_on h _
  | not_ d =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    simp only [renameInstr, evalInstr, hget_on d hd]
    exact setReg_rel_on hinj h d hd _
  | andn d a b | bzhi d a b =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have ha : a ∈ ns := hsubX a (by simp [bNamesX, SpillingRegAlloc.writtenNames,
      SpillingRegAlloc.readNames])
    have hb : b ∈ ns := hsubX b (by simp [bNamesX, SpillingRegAlloc.writtenNames,
      SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on a ha, hget_on b hb]
    exact writeB5W_rel_on hinj h d hd _
  | rol d amt =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames amt, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on amt hs, hget_on d hd]
    exact writeB2W_rel_on hinj h d hd _
  | ror d amt =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames amt, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on amt hs, hget_on d hd]
    exact writeB2W_rel_on hinj h d hd _
  | rorx d src amt =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames amt, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on amt hs, hget_on src hsrc]
    exact setReg_rel_on hinj h d hd _
  | shlx d src c =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    have hc : c ∈ ns := hsubX c (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on src hsrc, hget_on c hc]
    exact setReg_rel_on hinj h d hd _
  | shrx d src c =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    have hc : c ∈ ns := hsubX c (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on src hsrc, hget_on c hc]
    exact setReg_rel_on hinj h d hd _
  | sarx d src c =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    have hc : c ∈ ns := hsubX c (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on src hsrc, hget_on c hc]
    exact setReg_rel_on hinj h d hd _
  | movzx d sw src =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on src hsrc]
    exact setReg_rel_on hinj h d hd _
  | movsx d sw src =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on src hsrc]
    exact setReg_rel_on hinj h d hd _
  | lea d base idx scale off =>
    -- an address computation, not a memory access: the two address registers are
    -- reads and the destination is the only write.
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hbase : base ∈ ns := hsubX base (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    have hidx : idx ∈ ns := hsubX idx (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on base hbase, hget_on idx hidx]
    exact setReg_rel_on hinj h d hd _
  | or_ d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | xor_ d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | shl d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | shr d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | sar d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd]
    exact writeB5W_rel_on hinj h d hd _
  | cmove d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd, hzf]
    exact setReg_rel_on hinj h d hd _
  | cmovne d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd, hzf]
    exact setReg_rel_on hinj h d hd _
  | cmovb d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd, hcf]
    exact setReg_rel_on hinj h d hd _
  | mulx dh dl a b =>
    have hdh : dh ∈ ns := hsubX dh (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hdl : dl ∈ ns := hsubX dl (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have ha : ∀ n ∈ srcNames a, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, List.mem_append, hn])
    have hb : ∀ n ∈ srcNames b, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, List.mem_append, hn])
    simp only [renameInstr, evalInstr, hop_on a ha, hop_on b hb]
    exact setReg2_rel_on hinj h dl dh hdl hdh _ _
  | mulxMem dh dl a base off =>
    have hdh : dh ∈ ns := hsubX dh (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hdl : dl ∈ ns := hsubX dl (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    have ha : ∀ n ∈ srcNames a, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on a ha, load_rel_on h base hbase off]
    exact setReg2_rel_on hinj h dl dh hdl hdh _ _
  | adcx d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd, hcf]
    exact adcWrite_rel_on hinj h d hd _ (fun fl => { fl with cf := _ })
  | adox d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd, hof]
    exact adcWrite_rel_on hinj h d hd _ (fun fl => { fl with of := _ })
  | loadMem d base off =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, load_rel_on h base hbase off]
    exact setReg_rel_on hinj h d hd _
  | storeMem base off s =>
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs]
    exact store_rel_on hinj h base hbase off _
  | loadMemIdx d base idx scale =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    have hidx : idx ∈ ns := hsubX idx
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, JState.loadIdx, hget_on idx hidx,
      load_rel_on h base hbase (scale * (sR.get idx).toNat)]
    exact setReg_rel_on hinj h d hd _
  | storeMemIdx base idx scale s =>
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    have hidx : idx ∈ ns := hsubX idx
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, JState.storeIdx, hop_on s hs, hget_on idx hidx]
    exact store_rel_on hinj h base hbase (scale * (sR.get idx).toNat) _
  | loadSym d sym =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsym : sym ∈ ns := hsub sym (by simp [bNamesXsym])
    simp only [renameInstr, evalInstr]
    refine ⟨?_, h.flags, ?_⟩
    · intro n hn
      by_cases hnd : n = d
      · subst hnd; simp
      · have hne : ρ n ≠ ρ d := fun he => hnd (hinj n hn d hd he)
        simp [hne, hnd, h.regsOn n hn]
    · intro b hb o
      by_cases hbd : b = d
      · subst hbd; simp [h.memOn sym hsym o]
      · have hne : ρ b ≠ ρ d := fun he => hbd (hinj b hb d hd he)
        simp [hne, hbd, h.memOn b hb o]
  | inc d | dec d =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    simp only [renameInstr, evalInstr, hget_on d hd]
    exact writeB4W_rel_on hinj h d hd _
  | clc | stc =>
    simp only [renameInstr, evalInstr]
    exact flagsWrite_rel_on h (fun fl => { fl with cf := _ })
  | xchg a b =>
    have ha : a ∈ ns := hsubX a (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hb : b ∈ ns := hsubX b (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    simp only [renameInstr, evalInstr, x86_XCHG, hget_on a ha, hget_on b hb]
    exact setReg2_rel_on hinj h a b ha hb _ _
  | imulri d src imm =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on src hsrc]
    exact writeB5W_rel_on hinj h d hd _
  | mul dh dl src | imulWide dh dl src =>
    have hdh : dh ∈ ns := hsubX dh (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hdl : dl ∈ ns := hsubX dl (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on dl hdl, hget_on src hsrc]
    exact writeB5W2_rel_on hinj h dh dl hdh hdl _
  | shld d src amt | shrd d src amt =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hsrc : src ∈ ns := hsubX src (by simp [bNamesX,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames amt, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on amt hs, hget_on d hd, hget_on src hsrc]
    exact writeB5W_rel_on hinj h d hd _
  | rcl d amt | rcr d amt =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames amt, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on amt hs, hget_on d hd, hcf]
    exact writeB2W_rel_on hinj h d hd _
  | cmovcc c d s =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on s hs, hget_on d hd, hcond c]
    exact setReg_rel_on hinj h d hd _
  | setcc c d =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    simp only [renameInstr, evalInstr, JState.setRegMerge, hget_on d hd, hcond c]
    exact setReg_rel_on hinj h d hd _
  | testN sz a b =>
    have ha : a ∈ ns := hsubX a (by simp [bNamesX, SpillingRegAlloc.writtenNames,
      SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames b, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.writtenNames,
        SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on b hs, hget_on a ha]
    exact writeB5N_rel_on h _
  | bt a b =>
    have ha : a ∈ ns := hsubX a (by simp [bNamesX, SpillingRegAlloc.writtenNames,
      SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames b, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.writtenNames,
        SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on b hs, hget_on a ha]
    exact flagsWrite_rel_on h (fun fl => { fl with cf := _ })
  | btr d b | bts d b =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hs : ∀ n ∈ srcNames b, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, hop_on b hs, hget_on d hd]
    exact writeCFW_rel_on hinj h d hd _
  | addMem d base off | imulMem d base off =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on d hd, load_rel_on h base hbase off]
    exact writeB5W_rel_on hinj h d hd _
  | imulriMem d base off imm =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, load_rel_on h base hbase off]
    exact writeB5W_rel_on hinj h d hd _
  | adcxMem d base off =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on d hd, load_rel_on h base hbase off, hcf]
    exact adcWrite_rel_on hinj h d hd _ (fun fl => { fl with cf := _ })
  | adoxMem d base off =>
    have hd : d ∈ ns := hsubX d (by simp [bNamesX, SpillingRegAlloc.writtenNames])
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    simp only [renameInstr, evalInstr, hget_on d hd, load_rel_on h base hbase off, hof]
    exact adcWrite_rel_on hinj h d hd _ (fun fl => { fl with of := _ })
  | addToMem base off s =>
    have hbase : base ∈ ns := hsubX base
      (by simp [bNamesX, SpillingRegAlloc.readNames])
    have hs : ∀ n ∈ srcNames s, n ∈ ns := fun n hn =>
      hsubX n (by simp [bNamesX, SpillingRegAlloc.readNames, hn])
    simp only [renameInstr, evalInstr, JState.writeB5Mem, hop_on s hs,
      load_rel_on h base hbase off]
    exact store_rel_on hinj (writeB5_rel_on h _) base hbase off _

/-! ## 6. The whole-block scoped simulation -/

/-- **Block-level scoped regalloc simulation.** For `ρ` injective on `ns` covering
    every scoped name the block mentions, `StateRelOn ns ρ` is preserved by
    `runBlock` of the renamed block vs the original block. -/
theorem runBlock_renameBlock_rel_on {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) {sL sR : JState 64} (h : StateRelOn ns ρ sL sR)
    (block : List (JInstr 64)) (hsub : ∀ n ∈ blockNamesXsym block, n ∈ ns) :
    StateRelOn ns ρ (runBlock sL (renameBlock ρ block)) (runBlock sR block) := by
  induction block generalizing sL sR with
  | nil => simpa [RandomizedRegAlloc.renameBlock] using h
  | cons i is ih =>
    have hcons : blockNamesXsym (i :: is) = bNamesXsym i ++ blockNamesXsym is := by
      simp [blockNamesXsym, List.flatMap_cons]
    have hin : ∀ n ∈ bNamesXsym i, n ∈ ns := fun n hn =>
      hsub n (hcons ▸ List.mem_append.mpr (Or.inl hn))
    have his : ∀ n ∈ blockNamesXsym is, n ∈ ns := fun n hn =>
      hsub n (hcons ▸ List.mem_append.mpr (Or.inr hn))
    simp only [RandomizedRegAlloc.renameBlock, List.map_cons, runBlock_cons]
    exact ih (evalInstr_renameInstr_rel_on hinj h i hin) his

/-! ## 7. The top scoped theorem and its checked corollary -/

/-- **Scoped regalloc simulation (top).** Instantiating `ns := blockNamesXsym block`:
    a renaming injective on the block's scoped names preserves the `StateRelOn`
    simulation through the whole block — the no-alias-on-the-block-names hypothesis
    is all the soundness needs (weakening the global injectivity of
    `regalloc_runBlock_sound`). -/
theorem regalloc_runBlock_sound_on {ρ : String → String}
    (block : List (JInstr 64))
    (hinj : RenInjOn (blockNamesXsym block) ρ)
    (s t : JState 64)
    (h : StateRelOn (blockNamesXsym block) ρ s t) :
    StateRelOn (blockNamesXsym block) ρ
      (runBlock s (renameBlock ρ block)) (runBlock t block) :=
  runBlock_renameBlock_rel_on hinj h block (fun _ hn => hn)

/-- A scoped no-alias checker covering the `loadSym` symbol names too — the decidable
    certificate that discharges `regalloc_runBlock_sound_on`'s injectivity hypothesis. -/
def noAliasXsym (ρ : String → String) (block : List (JInstr 64)) : Bool :=
  decide (RenInjOn (blockNamesXsym block) ρ)

/-- The scoped checker is sound. -/
theorem noAliasXsym_sound (ρ : String → String) (block : List (JInstr 64))
    (h : noAliasXsym ρ block = true) : RenInjOn (blockNamesXsym block) ρ :=
  of_decide_eq_true h

/-- **Scoped regalloc simulation, checked.** With the scoped no-alias checker passing,
    a renaming preserves the `JState` semantics on the block's scoped names — the
    translation-validation statement with the *weakened*, decidably-checked
    on-block-names injectivity hypothesis (x86 X2). -/
theorem regalloc_runBlock_checked {ρ : String → String}
    (block : List (JInstr 64)) (hchk : noAliasXsym ρ block = true)
    (s t : JState 64)
    (h : StateRelOn (blockNamesXsym block) ρ s t) :
    StateRelOn (blockNamesXsym block) ρ
      (runBlock s (renameBlock ρ block)) (runBlock t block) :=
  regalloc_runBlock_sound_on block (noAliasXsym_sound ρ block hchk) s t h

end CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
