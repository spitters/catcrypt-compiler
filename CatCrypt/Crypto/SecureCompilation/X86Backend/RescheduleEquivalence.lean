/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachine
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# Verified reschedule-equivalence for `JInstr 64` basic blocks

This module proves that **adjacent transposition of independent instructions**
preserves `runBlock` on `JState 64`, and provides a certificate checker for
permutations decomposed as sequences of such swaps.

## Coverage of `indepJ`

`indepJ i1 i2` is a decidable independence predicate. It admits pairs where:
- Both instructions are in the `commClass` set `{mov, mulx, adcx, adox}`.
- Register WAW/WAR/RAW hazards are absent.
- Neither instruction touches memory (`touchesMem = false`).
- Flag writes/reads are pairwise disjoint (no flag WAW/WAR/RAW).

This covers exactly pairs drawn from `{mov, mulx, adcx, adox}` whose flag
writes are disjoint:
- `mov × mov`, `mov × mulx`, `mulx × mulx`: flag-free pairs (trivially disjoint).
- `mov × adcx`, `mov × adox`, `mulx × adcx`, `mulx × adox`: one side flag-free.
- `adcx × adox`: CF (adcx) and OF (adox) are disjoint flag sets — the ADX
  dual-carry case.
- `adcx × adcx`, `adox × adox`: rejected (CF–CF / OF–OF conflict).
- `loadMem`/`storeMem`/`mulxMem`/`loadSym`/`loadMemIdx`/`storeMemIdx`: excluded (touch memory).
- `add`/`sub`/`adc`/`sbb`/`imul`/`neg`/`and`/`or`/`xor`/`shl`/`shr`/`sar`/`test`/`cmp`/
  `andn`: excluded (write all 5 flags).
- `rol`/`ror`: excluded (write `OF`/`CF`, preserve `SF`/`PF`/`ZF`).
- `setc`/`cmov*`/`not_`/`rorx`/`shlx`/`shrx`/`sarx`/`movzx`/`movsx`/`lea`: excluded
  (not in commClass).

Every mixed-flag pair (`mov`/`mulx` × `adcx`/`adox`, and the `adcx × adox`
dual-carry case) is discharged by a standalone abstract-output lemma:
`evalInstr` is unfolded but `x86_MULX_lo_hi` / `x86_ADCX` are kept opaque, so the
proof reasons only about which register/flag receives each opaque value, never
the product or carry expression — sidestepping the `whnf`/`isDefEq` blow-up that
unfolding the carry arithmetic in `simp_all` produces. The symmetric (reversed)
arms reuse the same lemmas via `.symm`. The `adcx × adcx` / `adox × adox` cases
are vacuous (CF–CF / OF–OF flag write conflict rejected by `indepJ`).

## Key results

1. `evalInstr_comm`: the single-step commutation theorem.
2. `jinstr_bbSwap_exec`: adjacent-swap block equivalence.
3. `runBlock_perm_eq`: certificate checker soundness for swap sequences.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RescheduleEquivalence

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. Flag identifiers -/

/-- The five x86 condition flags tracked by `RFlags`. -/
inductive FlagId where
  | CF | PF | ZF | SF | OF
  deriving DecidableEq, Repr

/-! ## 2. Per-instruction metadata -/

/-- The flags an instruction **writes**. -/
def flagWrites : JInstr 64 → List FlagId
  | .add _ _  | .sub _ _  | .adc _ _  | .sbb _ _  | .imul _ _ | .neg _
  | .and_ _ _ | .or_ _ _  | .xor_ _ _ | .shl _ _  | .shr _ _  | .sar _ _
  | .test _ _ | .cmp _ _   | .andn _ _ _ =>
      [.CF, .PF, .ZF, .SF, .OF]
  | .adcx _ _ => [.CF]
  | .adox _ _ => [.OF]
  -- The rotates write `OF`/`CF` and preserve `SF`/`PF`/`ZF` (`JState.writeB2W`).
  | .rol _ _ | .ror _ _ => [.CF, .OF]
  | .mov _ _   | .setc _     | .cmove _ _  | .cmovne _ _ | .cmovb _ _
  | .mulx _ _ _ _ | .mulxMem _ _ _ _ _
  | .loadMem _ _ _ | .storeMem _ _ _ | .loadMemIdx _ _ _ _
  | .storeMemIdx _ _ _ _ | .loadSym _ _
  | .not_ _ | .rorx _ _ _ | .shlx _ _ _ | .shrx _ _ _ | .sarx _ _ _
  | .movzx _ _ _ | .movsx _ _ _ | .lea _ _ _ _ _ => []

/-- The flags an instruction **reads**. -/
def flagReads : JInstr 64 → List FlagId
  | .adc _ _  | .sbb _ _ | .adcx _ _ | .setc _  | .cmovb _ _ => [.CF]
  | .adox _ _ => [.OF]
  | .cmove _ _ | .cmovne _ _ => [.ZF]
  | _ => []

/-- Whether an instruction reads or writes memory (conservative). `lea` computes an
    address in the AGU and writes it to a register without dereferencing it, so it does
    not touch memory. -/
def touchesMem : JInstr 64 → Bool
  | .loadMem _ _ _  | .storeMem _ _ _  | .mulxMem _ _ _ _ _
  | .loadMemIdx _ _ _ _ | .storeMemIdx _ _ _ _ | .loadSym _ _ => true
  | .lea _ _ _ _ _ => false
  | _ => false

/-- The set of instructions whose pairwise commutativity we prove here.
    Exactly `{mov, mulx, adcx, adox}`. -/
def commClass : JInstr 64 → Bool
  | .mov _ _ | .mulx _ _ _ _ | .adcx _ _ | .adox _ _ => true
  | _ => false

/-! ## 3. Independence predicate -/

/-- `indepJ i1 i2`: both in `commClass`, register-disjoint, flag-disjoint
    (no flag WAW/WAR/RAW), and memory-free. -/
def indepJ (i1 i2 : JInstr 64) : Bool :=
  let w1 := writtenNames i1
  let w2 := writtenNames i2
  let r1 := readNames i1
  let r2 := readNames i2
  let reg_ok :=
    w1.all (fun r => !w2.contains r && !r2.contains r) &&
    w2.all (fun r => !w1.contains r && !r1.contains r)
  let flag_ok :=
    (flagWrites i1).all (fun f => !(flagWrites i2).contains f) &&
    (flagWrites i1).all (fun f => !(flagReads i2).contains f) &&
    (flagReads i1).all (fun f => !(flagWrites i2).contains f)
  let mem_ok := !touchesMem i1 && !touchesMem i2
  let class_ok := commClass i1 && commClass i2
  reg_ok && flag_ok && mem_ok && class_ok

/-! ## 4. Structural helpers -/

theorem JState.ext {w : Nat} {s t : JState w}
    (hr : s.regs = t.regs) (hf : s.flags = t.flags) (hm : s.mem = t.mem) : s = t := by
  cases s; cases t; simp_all

/-- `evalInstr` on a flag-free instruction preserves flags. -/
theorem evalInstr_flagsEq (s : JState 64) (i : JInstr 64)
    (h : (flagWrites i).isEmpty = true) : (evalInstr s i).flags = s.flags := by
  cases i <;> simp_all [flagWrites, evalInstr, JState.setReg]

/-- `evalInstr` on a `touchesMem = false` instruction preserves mem
    (no flag-free assumption needed: `adcx`/`adox` set `mem := s.mem` explicitly). -/
theorem evalInstr_memEq (s : JState 64) (i : JInstr 64)
    (hm : touchesMem i = false) :
    (evalInstr s i).mem = s.mem := by
  cases i <;>
    simp_all [touchesMem, evalInstr, JState.setReg, JState.writeB5, JState.writeB5W,
      JState.writeB2W]

/-- Operand eval is unchanged by `setReg r _` when `r ∉ srcNames src`. -/
theorem eval_setReg_notMem (s : JState 64) (src : JOperand)
    (r : String) (v : BitVec 64) (h : ¬ r ∈ AsmPrinter.srcNames src) :
    src.eval (s.setReg r v) = src.eval s := by
  cases src with
  | reg rr =>
    simp only [JOperand.eval, JState.get, JState.setReg]
    simp only [AsmPrinter.srcNames, List.mem_singleton] at h
    simp [Ne.symm h]
  | imm _ => rfl

/-- Operand eval in an `adcx`/`adox`-result record state — registers all of `s`
    except one (`dst`), the carry flag overwritten — equals operand eval in `s`,
    provided the operand does not read `dst`. The `adcx`/`adox` arms write a record
    literal `{ regs := …, flags := …, mem := s.mem }` (not a `setReg`), so this is
    the record-shaped analogue of `eval_setReg_notMem` used by the
    `mulx × adcx` / `mulx × adox` arms. The flag fields are universally quantified
    so the lemma covers both the `cf` (adcx) and `of` (adox) overwrite shapes. -/
theorem eval_adcxRecord_notMem (s : JState 64) (src : JOperand) (dst : String)
    (cf' pf' zf' sf' of' : JFlag) (res : BitVec 64)
    (h : ¬ dst ∈ AsmPrinter.srcNames src) :
    JOperand.eval
      { regs := fun r' => if r' = dst then res else s.regs r',
        flags := { cf := cf', pf := pf', zf := zf', sf := sf', of := of' },
        mem := s.mem } src = JOperand.eval s src := by
  cases src with
  | reg rr =>
    simp only [JOperand.eval, JState.get]
    simp only [AsmPrinter.srcNames, List.mem_singleton] at h
    simp [Ne.symm h]
  | imm _ => rfl

/-! ### Abstract-output mov × {adcx, adox} commutation lemmas

`mov` is flag-free and writes one register; `adcx`/`adox` read/write one flag
(CF/OF) and one register. The mov-result register write never feeds the adcx/adox
read (register-disjoint) and never changes the carry flag, so the carry output is
the same value in either order. Like the other ADX lemmas these keep `x86_ADCX`
**abstract**. A single proof body parametrised over the flag projection covers
both `adcx` (CF) and `adox` (OF) by passing the appropriate carry record. -/

/-- `mov d1 src1` commutes with `adcx dst2 src2` (abstract carry output). -/
theorem evalInstr_comm_mov_adcx (s : JState 64)
    (d1 : String) (src1 : JOperand) (dst2 : String) (src2 : JOperand)
    (hd12 : d1 ≠ dst2)
    (hsrc1_dst2 : ¬ dst2 ∈ AsmPrinter.srcNames src1)
    (hsrc2_d1 : ¬ d1 ∈ AsmPrinter.srcNames src2) :
    evalInstr (evalInstr s (.mov d1 src1)) (.adcx dst2 src2)
      = evalInstr (evalInstr s (.adcx dst2 src2)) (.mov d1 src1) := by
  simp only [evalInstr, x86_MOV]
  have hget2 : (s.setReg d1 (src1.eval s)).get dst2 = s.get dst2 := by
    simp [JState.get, JState.setReg, Ne.symm hd12]
  have hsrc2 : src2.eval (s.setReg d1 (src1.eval s)) = src2.eval s :=
    eval_setReg_notMem s src2 d1 _ hsrc2_d1
  have hcf : (s.setReg d1 (src1.eval s)).flagB (·.cf) = s.flagB (·.cf) := by
    simp [JState.flagB, JState.setReg]
  have hsrc1 : JOperand.eval
      { regs := fun r' => if r' = dst2
          then (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.cf))).2 else s.regs r',
        flags := { s.flags with cf := (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.cf))).1 },
        mem := s.mem } src1 = JOperand.eval s src1 := by
    have := eval_adcxRecord_notMem s src1 dst2
      (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.cf))).1 s.flags.pf s.flags.zf s.flags.sf
      s.flags.of (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.cf))).2 hsrc1_dst2
    simpa using this
  rw [hget2, hsrc2, hcf]
  apply JState.ext
  · funext r
    simp only [JState.get, JState.setReg, JState.flagB] at hsrc1 ⊢
    by_cases hr1 : r = d1 <;> by_cases hr2 : r = dst2 <;>
      simp_all [JState.get, JState.setReg, hsrc1, Ne.symm]
  · rfl
  · rfl

/-- `mov d1 src1` commutes with `adox dst2 src2` (abstract carry output). -/
theorem evalInstr_comm_mov_adox (s : JState 64)
    (d1 : String) (src1 : JOperand) (dst2 : String) (src2 : JOperand)
    (hd12 : d1 ≠ dst2)
    (hsrc1_dst2 : ¬ dst2 ∈ AsmPrinter.srcNames src1)
    (hsrc2_d1 : ¬ d1 ∈ AsmPrinter.srcNames src2) :
    evalInstr (evalInstr s (.mov d1 src1)) (.adox dst2 src2)
      = evalInstr (evalInstr s (.adox dst2 src2)) (.mov d1 src1) := by
  simp only [evalInstr, x86_MOV]
  have hget2 : (s.setReg d1 (src1.eval s)).get dst2 = s.get dst2 := by
    simp [JState.get, JState.setReg, Ne.symm hd12]
  have hsrc2 : src2.eval (s.setReg d1 (src1.eval s)) = src2.eval s :=
    eval_setReg_notMem s src2 d1 _ hsrc2_d1
  have hof : (s.setReg d1 (src1.eval s)).flagB (·.of) = s.flagB (·.of) := by
    simp [JState.flagB, JState.setReg]
  have hsrc1 : JOperand.eval
      { regs := fun r' => if r' = dst2
          then (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).2 else s.regs r',
        flags := { s.flags with of := (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).1 },
        mem := s.mem } src1 = JOperand.eval s src1 := by
    have := eval_adcxRecord_notMem s src1 dst2 s.flags.cf s.flags.pf s.flags.zf s.flags.sf
      (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).1
      (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).2 hsrc1_dst2
    simpa using this
  rw [hget2, hsrc2, hof]
  apply JState.ext
  · funext r
    simp only [JState.get, JState.setReg, JState.flagB] at hsrc1 ⊢
    by_cases hr1 : r = d1 <;> by_cases hr2 : r = dst2 <;>
      simp_all [JState.get, JState.setReg, hsrc1, Ne.symm]
  · rfl
  · rfl

/-! ### Abstract-output ADX × ADX dual-carry case (`adcx × adox`)

The `adcx × adox` reorder is the point of the ADX widening: `adcx` reads/writes
CF, `adox` reads/writes OF, and CF/OF are distinct `RFlags` fields, so the two
carry chains are independent. This standalone lemma keeps the `x86_ADCX` carry
outputs **abstract** — `evalInstr` is unfolded but `x86_ADCX`/`waddcarry` are
not — so the proof reasons only about which register/flag receives each opaque
value, sidestepping the `whnf`/`isDefEq` blow-up that unfolding the carry
arithmetic in `simp_all` produces. -/

/-- `adcx dst1 src1` commutes with `adox dst2 src2` (abstract carry outputs):
    the ADX dual-carry case. -/
theorem evalInstr_comm_adcx_adox (s : JState 64)
    (dst1 : String) (src1 : JOperand) (dst2 : String) (src2 : JOperand)
    (hd12 : dst1 ≠ dst2)
    (hsrc1_dst2 : ¬ dst2 ∈ AsmPrinter.srcNames src1)
    (hsrc2_dst1 : ¬ dst1 ∈ AsmPrinter.srcNames src2) :
    evalInstr (evalInstr s (.adcx dst1 src1)) (.adox dst2 src2)
      = evalInstr (evalInstr s (.adox dst2 src2)) (.adcx dst1 src1) := by
  simp only [evalInstr]
  -- The adcx result state (CF written); read of dst2 / src2 / OF collapse to `s`.
  have hget2 : (fun r' => if r' = dst1
        then (x86_ADCX (s.get dst1) (src1.eval s) (s.flagB (·.cf))).2 else s.regs r') dst2
      = s.regs dst2 := by simp [hd12.symm]
  have hsrc2 : JOperand.eval
      { regs := fun r' => if r' = dst1
          then (x86_ADCX (s.get dst1) (src1.eval s) (s.flagB (·.cf))).2 else s.regs r',
        flags := { s.flags with cf := (x86_ADCX (s.get dst1) (src1.eval s) (s.flagB (·.cf))).1 },
        mem := s.mem } src2 = JOperand.eval s src2 := by
    have := eval_adcxRecord_notMem s src2 dst1
      (x86_ADCX (s.get dst1) (src1.eval s) (s.flagB (·.cf))).1 s.flags.pf s.flags.zf s.flags.sf
      s.flags.of (x86_ADCX (s.get dst1) (src1.eval s) (s.flagB (·.cf))).2 hsrc2_dst1
    simpa using this
  -- The adox result state (OF written); read of dst1 / src1 / CF collapse to `s`.
  have hget1 : (fun r' => if r' = dst2
        then (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).2 else s.regs r') dst1
      = s.regs dst1 := by simp [hd12]
  have hsrc1 : JOperand.eval
      { regs := fun r' => if r' = dst2
          then (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).2 else s.regs r',
        flags := { s.flags with of := (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).1 },
        mem := s.mem } src1 = JOperand.eval s src1 := by
    have := eval_adcxRecord_notMem s src1 dst2 s.flags.cf s.flags.pf s.flags.zf s.flags.sf
      (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).1
      (x86_ADCX (s.get dst2) (src2.eval s) (s.flagB (·.of))).2 hsrc1_dst2
    simpa using this
  apply JState.ext
  · funext r
    simp only [JState.get, JState.flagB] at hget2 hsrc2 hget1 hsrc1 ⊢
    by_cases hr1 : r = dst1 <;> by_cases hr2 : r = dst2 <;>
      simp_all [JState.get]
  · -- flags: { {s.flags with cf := c} with of := o } = { {s.flags with of := o} with cf := c }
    -- collapse the cross-register reads (dst2 in the adcx state, dst1 in the adox state)
    -- and the cross-operand reads, then the two records are equal field-by-field.
    simp only [JState.flagB, JState.get] at hget2 hsrc2 hget1 hsrc1 ⊢
    rw [if_neg (Ne.symm hd12), if_neg hd12, hsrc2, hsrc1]
  · rfl

/-! ### Abstract-output ADX × mulx commutation lemmas

The four `mulx ↔ {adcx, adox}` arms are factored into standalone lemmas so each
gets a fresh elaboration budget. They keep `x86_MULX_lo_hi`/`x86_ADCX` opaque
(unfold only `evalInstr`): the `mulx` hi/lo products and the `adcx`/`adox` carry
results never appear as values, so the proof is pure register/flag bookkeeping.
The shared shape: collapse the second instruction's reads (evaluated in the
first's result state) back to reads in `s`, then `JState.ext`. -/

/-- `mulx dh1 dl1 a1 b1` commutes with `adcx dst2 src2` (abstract output). -/
theorem evalInstr_comm_mulx_adcx (s : JState 64)
    (dh1 dl1 : String) (a1 b1 : JOperand) (dst2 : String) (src2 : JOperand)
    (hdh1 : dh1 ≠ dst2) (hdl1 : dl1 ≠ dst2)
    (ha1 : ¬ dst2 ∈ AsmPrinter.srcNames a1) (hb1 : ¬ dst2 ∈ AsmPrinter.srcNames b1)
    (hsdh1 : ¬ dh1 ∈ AsmPrinter.srcNames src2) (hsdl1 : ¬ dl1 ∈ AsmPrinter.srcNames src2) :
    evalInstr (evalInstr s (.mulx dh1 dl1 a1 b1)) (.adcx dst2 src2)
      = evalInstr (evalInstr s (.adcx dst2 src2)) (.mulx dh1 dl1 a1 b1) := by
  simp only [evalInstr]
  have hget : (((s.setReg dl1 (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).fst).setReg dh1
        (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).snd).get dst2) = s.get dst2 := by
    simp [JState.get, JState.setReg, Ne.symm hdh1, Ne.symm hdl1]
  have hflag : (((s.setReg dl1 (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).fst).setReg dh1
        (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).snd).flagB (fun x => x.cf))
      = s.flagB (fun x => x.cf) := by simp [JState.flagB, JState.setReg]
  have hsrc : JOperand.eval
      ((s.setReg dl1 (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).fst).setReg dh1
        (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).snd) src2 = JOperand.eval s src2 :=
    (eval_setReg_notMem _ src2 dh1 _ hsdh1).trans (eval_setReg_notMem _ src2 dl1 _ hsdl1)
  have hea : ∀ co res, JOperand.eval
      { regs := fun r' => if r' = dst2 then res else s.regs r',
        flags := { cf := co, pf := s.flags.pf, zf := s.flags.zf,
                   sf := s.flags.sf, of := s.flags.of }, mem := s.mem } a1
      = JOperand.eval s a1 := fun co res => eval_adcxRecord_notMem s a1 dst2 _ _ _ _ _ res ha1
  have heb : ∀ co res, JOperand.eval
      { regs := fun r' => if r' = dst2 then res else s.regs r',
        flags := { cf := co, pf := s.flags.pf, zf := s.flags.zf,
                   sf := s.flags.sf, of := s.flags.of }, mem := s.mem } b1
      = JOperand.eval s b1 := fun co res => eval_adcxRecord_notMem s b1 dst2 _ _ _ _ _ res hb1
  rw [hget, hflag, hsrc, hea, heb]
  apply JState.ext
  · funext r
    clear hget hflag hsrc hea heb ha1 hb1 hsdh1 hsdl1
    by_cases hr_dh1 : r = dh1 <;> by_cases hr_dl1 : r = dl1 <;> by_cases hr_dst2 : r = dst2 <;>
      simp_all [JState.setReg, JState.get, Ne.symm]
  · simp [JState.setReg]
  · simp [JState.setReg]

/-- `mulx dh1 dl1 a1 b1` commutes with `adox dst2 src2` (abstract output). -/
theorem evalInstr_comm_mulx_adox (s : JState 64)
    (dh1 dl1 : String) (a1 b1 : JOperand) (dst2 : String) (src2 : JOperand)
    (hdh1 : dh1 ≠ dst2) (hdl1 : dl1 ≠ dst2)
    (ha1 : ¬ dst2 ∈ AsmPrinter.srcNames a1) (hb1 : ¬ dst2 ∈ AsmPrinter.srcNames b1)
    (hsdh1 : ¬ dh1 ∈ AsmPrinter.srcNames src2) (hsdl1 : ¬ dl1 ∈ AsmPrinter.srcNames src2) :
    evalInstr (evalInstr s (.mulx dh1 dl1 a1 b1)) (.adox dst2 src2)
      = evalInstr (evalInstr s (.adox dst2 src2)) (.mulx dh1 dl1 a1 b1) := by
  simp only [evalInstr]
  have hget : (((s.setReg dl1 (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).fst).setReg dh1
        (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).snd).get dst2) = s.get dst2 := by
    simp [JState.get, JState.setReg, Ne.symm hdh1, Ne.symm hdl1]
  have hflag : (((s.setReg dl1 (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).fst).setReg dh1
        (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).snd).flagB (fun x => x.of))
      = s.flagB (fun x => x.of) := by simp [JState.flagB, JState.setReg]
  have hsrc : JOperand.eval
      ((s.setReg dl1 (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).fst).setReg dh1
        (x86_MULX_lo_hi (a1.eval s) (b1.eval s)).snd) src2 = JOperand.eval s src2 :=
    (eval_setReg_notMem _ src2 dh1 _ hsdh1).trans (eval_setReg_notMem _ src2 dl1 _ hsdl1)
  have hea : ∀ co res, JOperand.eval
      { regs := fun r' => if r' = dst2 then res else s.regs r',
        flags := { cf := s.flags.cf, pf := s.flags.pf, zf := s.flags.zf,
                   sf := s.flags.sf, of := co }, mem := s.mem } a1
      = JOperand.eval s a1 := fun co res => eval_adcxRecord_notMem s a1 dst2 _ _ _ _ _ res ha1
  have heb : ∀ co res, JOperand.eval
      { regs := fun r' => if r' = dst2 then res else s.regs r',
        flags := { cf := s.flags.cf, pf := s.flags.pf, zf := s.flags.zf,
                   sf := s.flags.sf, of := co }, mem := s.mem } b1
      = JOperand.eval s b1 := fun co res => eval_adcxRecord_notMem s b1 dst2 _ _ _ _ _ res hb1
  rw [hget, hflag, hsrc, hea, heb]
  apply JState.ext
  · funext r
    clear hget hflag hsrc hea heb ha1 hb1 hsdh1 hsdl1
    by_cases hr_dh1 : r = dh1 <;> by_cases hr_dl1 : r = dl1 <;> by_cases hr_dst2 : r = dst2 <;>
      simp_all [JState.setReg, JState.get, Ne.symm]
  · simp [JState.setReg]
  · simp [JState.setReg]

/-! ## 5. The commutation theorem -/

/-- **The single-step commutation theorem**: when `indepJ i1 i2`, the two instructions
    commute on `JState 64`. Both must be in `commClass = {mov, mulx, adcx, adox}`.

    Proof: by exhaustive `cases i1 <;> cases i2` with:
    - non-`commClass` arms dismissed via contradiction with `class_ok`.
    - `{mov, mulx} × {adcx, adox}` arms: mov/mulx is flag-free, so the flag-read
      value for adcx/adox is unchanged; register and mem disjointness close the rest.
      The `mulx`-side products and the `adcx`/`adox`-side carry results are kept
      abstract (`x86_MULX_lo_hi` / `x86_ADCX` are not unfolded) so the goal stays
      a register/flag bookkeeping problem.
    - `adcx × adox`: CF vs OF are distinct `RFlags` fields; updating them in either
      order produces identical records (`rfl`). -/
theorem evalInstr_comm (s : JState 64) (i1 i2 : JInstr 64)
    (hind : indepJ i1 i2 = true) :
    evalInstr (evalInstr s i1) i2 = evalInstr (evalInstr s i2) i1 := by
  simp only [indepJ, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff,
             Bool.not_eq_false'] at hind
  obtain ⟨⟨⟨hreg, hflag⟩, hmem⟩, hclass⟩ := hind
  obtain ⟨hw1_all, hw2_all⟩ := hreg
  obtain ⟨⟨hfw1_fw2, hfw1_fr2⟩, hfr1_fw2⟩ := hflag
  obtain ⟨hm1, hm2⟩ := hmem
  obtain ⟨hcc1, hcc2⟩ := hclass
  -- Mem is preserved by both instructions
  have hm1' : (evalInstr s i1).mem = s.mem := evalInstr_memEq s i1 hm1
  have hm2' : (evalInstr s i2).mem = s.mem := evalInstr_memEq s i2 hm2
  cases i1 with
  | mov d1 src1 =>
    -- Flag-free: mov writes no flags
    have hf1 : (evalInstr s (JInstr.mov d1 src1)).flags = s.flags :=
      evalInstr_flagsEq s (.mov d1 src1) (by simp [flagWrites])
    cases i2 with
    | mov d2 src2 =>
      -- mov × mov
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false] at hw1_all hw2_all
      obtain ⟨hne_d1d2, hne_d1r2⟩ := hw1_all
      obtain ⟨hne_d2d1, hne_d2r1⟩ := hw2_all
      have hd12 : d1 ≠ d2 := by
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hne_d1d2; exact hne_d1d2
      have hne_src2_d1 : ¬ d1 ∈ AsmPrinter.srcNames src2 :=
        Bool.eq_false_iff.mp hne_d1r2 ∘ List.contains_iff_mem.mpr
      have hne_src1_d2 : ¬ d2 ∈ AsmPrinter.srcNames src1 :=
        Bool.eq_false_iff.mp hne_d2r1 ∘ List.contains_iff_mem.mpr
      simp only [evalInstr, JState.setReg]
      apply JState.ext
      · funext r
        rcases src1 with r1 | v1 <;> rcases src2 with r2 | v2 <;>
          (by_cases hr1 : r = d1 <;> by_cases hr2 : r = d2 <;>
            simp_all [AsmPrinter.srcNames, JOperand.eval, JState.get, JState.setReg,
                      x86_MOV, Ne.symm hd12]) <;>
          (intro h; simp_all [x86_MOV])
      · rfl
      · rfl
    | mulx dh2 dl2 a2 b2 =>
      -- mov × mulx
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, List.all_append,
                 Bool.or_eq_false_iff, beq_eq_false_iff_ne,
                 Bool.not_eq_true', List.contains_append] at hw1_all hw2_all
      obtain ⟨⟨hne_d1dh2, hne_d1dl2⟩, hne_d1r2⟩ := hw1_all
      obtain ⟨⟨hne_dh2d1, hne_src1_dh2⟩, hne_dl2d1, hne_src1_dl2⟩ := hw2_all
      have ha2_d1 : ¬ d1 ∈ AsmPrinter.srcNames a2 :=
        Bool.eq_false_iff.mp hne_d1r2.1 ∘ List.contains_iff_mem.mpr
      have hb2_d1 : ¬ d1 ∈ AsmPrinter.srcNames b2 :=
        Bool.eq_false_iff.mp hne_d1r2.2 ∘ List.contains_iff_mem.mpr
      have hsrc1_dh2 : ¬ dh2 ∈ AsmPrinter.srcNames src1 :=
        Bool.eq_false_iff.mp hne_src1_dh2 ∘ List.contains_iff_mem.mpr
      have hsrc1_dl2 : ¬ dl2 ∈ AsmPrinter.srcNames src1 :=
        Bool.eq_false_iff.mp hne_src1_dl2 ∘ List.contains_iff_mem.mpr
      simp only [evalInstr, x86_MULX_lo_hi, wumul, high_bits, JState.setReg,
                 JOperand.eval, JState.get]
      apply JState.ext
      · funext r
        -- Clear flag/class hyps before simp_all to avoid FlagId case-explosion
        clear hfw1_fw2 hfw1_fr2 hfr1_fw2 hcc1 hcc2 hm1 hm2 hm1' hm2' hf1
        rcases src1 with rs1 | vs1 <;> rcases a2 with ra2 | va2 <;> rcases b2 with rb2 | vb2 <;>
          by_cases hr_dl2 : r = dl2 <;> by_cases hr_dh2 : r = dh2 <;>
          by_cases hr_d1 : r = d1 <;>
          simp_all [JOperand.eval, JState.get, x86_MOV, Ne.symm,
                    AsmPrinter.srcNames, List.mem_singleton]
      · simp
      · simp
    | adcx dst2 src2 =>
      -- mov × adcx: discharged by the abstract-output lemma.
      -- `readNames (adcx dst2 src2) = dst2 :: srcNames src2`, so peel the leading `dst2`.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
                 beq_eq_false_iff_ne] at hw1_all hw2_all
      obtain ⟨hne_d1dst2, _, hne_d1src2⟩ := hw1_all
      obtain ⟨hne_dst2d1, hne_src1_dst2⟩ := hw2_all
      exact evalInstr_comm_mov_adcx s d1 src1 dst2 src2 hne_d1dst2
        (Bool.eq_false_iff.mp hne_src1_dst2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_d1src2 ∘ List.contains_iff_mem.mpr)
    | adox dst2 src2 =>
      -- mov × adox: discharged by the abstract-output lemma.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
                 beq_eq_false_iff_ne] at hw1_all hw2_all
      obtain ⟨hne_d1dst2, _, hne_d1src2⟩ := hw1_all
      obtain ⟨hne_dst2d1, hne_src1_dst2⟩ := hw2_all
      exact evalInstr_comm_mov_adox s d1 src1 dst2 src2 hne_d1dst2
        (Bool.eq_false_iff.mp hne_src1_dst2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_d1src2 ∘ List.contains_iff_mem.mpr)
    | _ => simp_all [commClass, flagWrites, flagReads]
  | mulx dh1 dl1 a1 b1 =>
    -- Flag-free: mulx writes no flags
    have hf1 : (evalInstr s (JInstr.mulx dh1 dl1 a1 b1)).flags = s.flags :=
      evalInstr_flagsEq s (.mulx dh1 dl1 a1 b1) (by simp [flagWrites])
    cases i2 with
    | mov d2 src2 =>
      -- mulx × mov: symmetric to mov × mulx
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, List.all_append,
                 Bool.or_eq_false_iff, beq_eq_false_iff_ne,
                 Bool.not_eq_true', List.contains_append] at hw1_all hw2_all
      obtain ⟨⟨hne_dh1_d2, hne_src2_dh1⟩, hne_dl1_d2, hne_src2_dl1⟩ := hw1_all
      obtain ⟨hne_d2_dh1, hne_d2_r1⟩ := hw2_all
      have ha1_d2 : ¬ d2 ∈ AsmPrinter.srcNames a1 :=
        Bool.eq_false_iff.mp hne_d2_r1.1 ∘ List.contains_iff_mem.mpr
      have hb1_d2 : ¬ d2 ∈ AsmPrinter.srcNames b1 :=
        Bool.eq_false_iff.mp hne_d2_r1.2 ∘ List.contains_iff_mem.mpr
      simp only [evalInstr, x86_MULX_lo_hi, wumul, high_bits, JState.setReg,
                 JOperand.eval, JState.get]
      apply JState.ext
      · funext r
        clear hfw1_fw2 hfw1_fr2 hfr1_fw2 hcc1 hcc2 hm1 hm2 hm1' hm2' hf1
        rcases src2 with rs2 | vs2 <;> rcases a1 with ra1 | va1 <;> rcases b1 with rb1 | vb1 <;>
          by_cases hr_dh1 : r = dh1 <;> by_cases hr_dl1 : r = dl1 <;>
          by_cases hr_d2 : r = d2 <;>
          simp_all [JOperand.eval, JState.get, x86_MOV, Ne.symm,
                    AsmPrinter.srcNames, List.mem_singleton]
      · simp
      · simp
    | mulx dh2 dl2 a2 b2 =>
      -- mulx × mulx
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, List.all_append,
                 Bool.or_eq_false_iff, beq_eq_false_iff_ne,
                 Bool.not_eq_true', List.contains_append] at hw1_all hw2_all
      obtain ⟨⟨hne_dh1_w2, hne_dh1_a2, hne_dh1_b2⟩, hne_dl1_w2, hne_dl1_a2, hne_dl1_b2⟩ := hw1_all
      obtain ⟨⟨hne_dh2_w1, hne_dh2_a1, hne_dh2_b1⟩, hne_dl2_w1, hne_dl2_a1, hne_dl2_b1⟩ := hw2_all
      have h11 : dh1 ≠ dh2 := hne_dh1_w2.1
      have h12 : dh1 ≠ dl2 := hne_dh1_w2.2
      have h21 : dl1 ≠ dh2 := hne_dl1_w2.1
      have h22 : dl1 ≠ dl2 := hne_dl1_w2.2
      have ha1_dh2 : ¬ dh2 ∈ AsmPrinter.srcNames a1 :=
        Bool.eq_false_iff.mp hne_dh2_a1 ∘ List.contains_iff_mem.mpr
      have hb1_dh2 : ¬ dh2 ∈ AsmPrinter.srcNames b1 :=
        Bool.eq_false_iff.mp hne_dh2_b1 ∘ List.contains_iff_mem.mpr
      have ha1_dl2 : ¬ dl2 ∈ AsmPrinter.srcNames a1 :=
        Bool.eq_false_iff.mp hne_dl2_a1 ∘ List.contains_iff_mem.mpr
      have hb1_dl2 : ¬ dl2 ∈ AsmPrinter.srcNames b1 :=
        Bool.eq_false_iff.mp hne_dl2_b1 ∘ List.contains_iff_mem.mpr
      have ha2_dh1 : ¬ dh1 ∈ AsmPrinter.srcNames a2 :=
        Bool.eq_false_iff.mp hne_dh1_a2 ∘ List.contains_iff_mem.mpr
      have hb2_dh1 : ¬ dh1 ∈ AsmPrinter.srcNames b2 :=
        Bool.eq_false_iff.mp hne_dh1_b2 ∘ List.contains_iff_mem.mpr
      have ha2_dl1 : ¬ dl1 ∈ AsmPrinter.srcNames a2 :=
        Bool.eq_false_iff.mp hne_dl1_a2 ∘ List.contains_iff_mem.mpr
      have hb2_dl1 : ¬ dl1 ∈ AsmPrinter.srcNames b2 :=
        Bool.eq_false_iff.mp hne_dl1_b2 ∘ List.contains_iff_mem.mpr
      -- eval helpers: operands of i1 unchanged after setReg dh2/dl2 (and vice versa)
      have ea1 : ∀ v1 v2 : BitVec 64,
          a1.eval ((s.setReg dl2 v1).setReg dh2 v2) = a1.eval s :=
        fun v1 v2 => (eval_setReg_notMem _ a1 dh2 v2 ha1_dh2).trans
                     (eval_setReg_notMem _ a1 dl2 v1 ha1_dl2)
      have eb1 : ∀ v1 v2 : BitVec 64,
          b1.eval ((s.setReg dl2 v1).setReg dh2 v2) = b1.eval s :=
        fun v1 v2 => (eval_setReg_notMem _ b1 dh2 v2 hb1_dh2).trans
                     (eval_setReg_notMem _ b1 dl2 v1 hb1_dl2)
      have ea2 : ∀ v1 v2 : BitVec 64,
          a2.eval ((s.setReg dl1 v1).setReg dh1 v2) = a2.eval s :=
        fun v1 v2 => (eval_setReg_notMem _ a2 dh1 v2 ha2_dh1).trans
                     (eval_setReg_notMem _ a2 dl1 v1 ha2_dl1)
      have eb2 : ∀ v1 v2 : BitVec 64,
          b2.eval ((s.setReg dl1 v1).setReg dh1 v2) = b2.eval s :=
        fun v1 v2 => (eval_setReg_notMem _ b2 dh1 v2 hb2_dh1).trans
                     (eval_setReg_notMem _ b2 dl1 v1 hb2_dl1)
      simp only [evalInstr, x86_MULX_lo_hi, wumul, high_bits, JState.setReg,
                 JOperand.eval, JState.get]
      apply JState.ext
      · funext r
        -- Clear flag/class/mem hyps before big simp to avoid elaboration blowup
        clear hfr1_fw2 hfw1_fw2 hfw1_fr2 hcc1 hcc2 hm1 hm1' hm2 hm2' hf1
        rcases a1 with ra1 | va1 <;> rcases b1 with rb1 | vb1 <;>
          rcases a2 with ra2 | va2 <;> rcases b2 with rb2 | vb2 <;>
          (simp only [AsmPrinter.srcNames, List.mem_singleton, List.mem_nil_iff,
                      List.contains_cons, List.contains_nil]
            at ha1_dh2 ha1_dl2 hb1_dh2 hb1_dl2 ha2_dh1 ha2_dl1 hb2_dh1 hb2_dl1
               hne_dh2_a1 hne_dh2_b1 hne_dl2_a1 hne_dl2_b1
               hne_dh1_a2 hne_dh1_b2 hne_dl1_a2 hne_dl1_b2 <;> try rfl) <;>
          by_cases hr_dh1 : r = dh1 <;> by_cases hr_dl1 : r = dl1 <;>
          by_cases hr_dh2 : r = dh2 <;> by_cases hr_dl2 : r = dl2 <;>
          (try exact absurd (hr_dl1.symm.trans hr_dh2) hne_dl1_w2.1) <;>
          (try exact absurd (hr_dl1.symm.trans hr_dl2) hne_dl1_w2.2) <;>
          (try exact absurd (hr_dh1.symm.trans hr_dh2) hne_dh1_w2.1) <;>
          (try exact absurd (hr_dh1.symm.trans hr_dl2) hne_dh1_w2.2) <;>
          (try simp only [ne_comm] at hb1_dh2 hb1_dl2 ha2_dh1 ha2_dl1
                                       hb2_dh1 hb2_dl1 ha1_dh2 ha1_dl2) <;>
          dsimp only [] <;>
          (try clear ea1 eb1 ea2 eb2 hne_dh1_w2 hne_dl1_w2 hne_dh2_w1 hne_dl2_w1 h11 h12 h21 h22 hne_dh2_a1 hne_dh2_b1 hne_dl2_a1 hne_dl2_b1 hne_dh1_a2 hne_dh1_b2 hne_dl1_a2 hne_dl1_b2) <;>
          simp_all [Ne.symm]
      · simp
      · simp
    | adcx dst2 src2 =>
      -- mulx × adcx: discharged by the abstract-output lemma.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons, List.contains_nil,
                 Bool.or_false, List.all_append, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
                 List.contains_append] at hw1_all hw2_all
      obtain ⟨⟨hne_dh1_dst2, hne_dh1_r2⟩, hne_dl1_dst2, hne_dl1_r2⟩ := hw1_all
      obtain ⟨⟨_hne_dst2_dh1, _hne_dst2_dl1⟩, hne_src2_dh1, hne_src2_dl1⟩ := hw2_all
      exact evalInstr_comm_mulx_adcx s dh1 dl1 a1 b1 dst2 src2 hne_dh1_dst2 hne_dl1_dst2
        (Bool.eq_false_iff.mp hne_src2_dh1 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_src2_dl1 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dh1_r2.2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dl1_r2.2 ∘ List.contains_iff_mem.mpr)
    | adox dst2 src2 =>
      -- mulx × adox: discharged by the abstract-output lemma.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons, List.contains_nil,
                 Bool.or_false, List.all_append, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
                 List.contains_append] at hw1_all hw2_all
      obtain ⟨⟨hne_dh1_dst2, hne_dh1_r2⟩, hne_dl1_dst2, hne_dl1_r2⟩ := hw1_all
      obtain ⟨⟨_hne_dst2_dh1, _hne_dst2_dl1⟩, hne_src2_dh1, hne_src2_dl1⟩ := hw2_all
      exact evalInstr_comm_mulx_adox s dh1 dl1 a1 b1 dst2 src2 hne_dh1_dst2 hne_dl1_dst2
        (Bool.eq_false_iff.mp hne_src2_dh1 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_src2_dl1 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dh1_r2.2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dl1_r2.2 ∘ List.contains_iff_mem.mpr)
    | _ => simp_all [commClass, flagWrites, flagReads]
  | adcx dst1 src1 =>
    cases i2 with
    | mov d2 src2 =>
      -- adcx × mov: `.symm` of the abstract-output `mov × adcx` lemma.
      -- `readNames (adcx dst1 src1) = dst1 :: srcNames src1`, so peel the leading `dst1`.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
                 beq_eq_false_iff_ne] at hw1_all hw2_all
      obtain ⟨hne_dst1_d2, hne_dst1_src2⟩ := hw1_all
      obtain ⟨hne_d2dst1, _, hne_d2src1⟩ := hw2_all
      exact (evalInstr_comm_mov_adcx s d2 src2 dst1 src1 (Ne.symm hne_dst1_d2)
        (Bool.eq_false_iff.mp hne_dst1_src2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_d2src1 ∘ List.contains_iff_mem.mpr)).symm
    | mulx dh2 dl2 a2 b2 =>
      -- adcx × mulx: `.symm` of the proven abstract-output `mulx × adcx` lemma.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons, List.contains_nil,
                 Bool.or_false, List.all_append, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
                 List.contains_append] at hw1_all hw2_all
      obtain ⟨⟨hne_dst1_dh2, hne_dst1_dl2⟩, hne_dst1_r2⟩ := hw1_all
      obtain ⟨⟨hne_dh2_dst1, hne_dh2_r1⟩, hne_dl2_dst1, hne_dl2_r1⟩ := hw2_all
      exact (evalInstr_comm_mulx_adcx s dh2 dl2 a2 b2 dst1 src1
        hne_dh2_dst1 hne_dl2_dst1
        (Bool.eq_false_iff.mp hne_dst1_r2.1 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dst1_r2.2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dh2_r1.2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dl2_r1.2 ∘ List.contains_iff_mem.mpr)).symm
    | adox dst2 src2 =>
      -- adcx × adox: the ADX dual-carry case — discharged by the abstract-output lemma.
      -- adcx reads/writes CF; adox reads/writes OF; CF ≠ OF so they don't conflict.
      -- `readNames` of both ADX ops leads with its destination, so peel via `or_eq_false_iff`.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
                 beq_eq_false_iff_ne] at hw1_all hw2_all
      obtain ⟨hne_dst1_dst2, _, hne_dst1_src2⟩ := hw1_all
      obtain ⟨hne_dst2_dst1, _, hne_dst2_src1⟩ := hw2_all
      exact evalInstr_comm_adcx_adox s dst1 src1 dst2 src2 hne_dst1_dst2
        (Bool.eq_false_iff.mp hne_dst2_src1 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dst1_src2 ∘ List.contains_iff_mem.mpr)
    | _ => simp_all [commClass, flagWrites, flagReads]
  | adox dst1 src1 =>
    cases i2 with
    | mov d2 src2 =>
      -- adox × mov: `.symm` of the abstract-output `mov × adox` lemma.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
                 beq_eq_false_iff_ne] at hw1_all hw2_all
      obtain ⟨hne_dst1_d2, hne_dst1_src2⟩ := hw1_all
      obtain ⟨hne_d2dst1, _, hne_d2src1⟩ := hw2_all
      exact (evalInstr_comm_mov_adox s d2 src2 dst1 src1 (Ne.symm hne_dst1_d2)
        (Bool.eq_false_iff.mp hne_dst1_src2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_d2src1 ∘ List.contains_iff_mem.mpr)).symm
    | mulx dh2 dl2 a2 b2 =>
      -- adox × mulx: `.symm` of the proven abstract-output `mulx × adox` lemma.
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons, List.contains_nil,
                 Bool.or_false, List.all_append, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
                 List.contains_append] at hw1_all hw2_all
      obtain ⟨⟨hne_dst1_dh2, hne_dst1_dl2⟩, hne_dst1_r2⟩ := hw1_all
      obtain ⟨⟨hne_dh2_dst1, hne_dh2_r1⟩, hne_dl2_dst1, hne_dl2_r1⟩ := hw2_all
      exact (evalInstr_comm_mulx_adox s dh2 dl2 a2 b2 dst1 src1
        hne_dh2_dst1 hne_dl2_dst1
        (Bool.eq_false_iff.mp hne_dst1_r2.1 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dst1_r2.2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dh2_r1.2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dl2_r1.2 ∘ List.contains_iff_mem.mpr)).symm
    | adcx dst2 src2 =>
      -- adox × adcx: `.symm` of the ADX dual-carry case (`adcx × adox`).
      simp only [writtenNames, readNames, List.all_cons, List.all_nil, Bool.and_true,
                 Bool.and_eq_true, Bool.not_eq_true', List.contains_cons,
                 List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
                 beq_eq_false_iff_ne] at hw1_all hw2_all
      obtain ⟨hne_dst1_dst2, _, hne_dst1_src2⟩ := hw1_all
      obtain ⟨hne_dst2_dst1, _, hne_dst2_src1⟩ := hw2_all
      exact (evalInstr_comm_adcx_adox s dst2 src2 dst1 src1 (Ne.symm hne_dst1_dst2)
        (Bool.eq_false_iff.mp hne_dst1_src2 ∘ List.contains_iff_mem.mpr)
        (Bool.eq_false_iff.mp hne_dst2_src1 ∘ List.contains_iff_mem.mpr)).symm
    | _ => simp_all [commClass, flagWrites, flagReads]
  | _ => simp_all [commClass]

/-! ## 6. Adjacent-swap block equivalence -/

theorem jinstr_bbSwap_exec (s : JState 64) (i1 i2 : JInstr 64) (rest : List (JInstr 64))
    (hind : indepJ i1 i2 = true) :
    runBlock s (i1 :: i2 :: rest) = runBlock s (i2 :: i1 :: rest) := by
  simp only [runBlock_cons]
  rw [evalInstr_comm s i1 i2 hind]

/-! ## 7. Certificate checker -/

/-- Apply a transposition at position `k` (swaps elements at indices `k` and `k+1`). -/
def applySwap : Nat → List (JInstr 64) → List (JInstr 64)
  | _,     []       => []
  | _,     [x]      => [x]
  | 0,     i1 :: i2 :: rest => i2 :: i1 :: rest
  | k + 1, x :: rest        => x :: applySwap k rest

/-- Apply a sequence of transpositions (left to right). -/
def applySwaps (swaps : List Nat) (block : List (JInstr 64)) : List (JInstr 64) :=
  swaps.foldl (fun b k => applySwap k b) block

/-- Check that a transposition at position `k` is `indepJ`-certified. -/
def checkSwap (k : Nat) (block : List (JInstr 64)) : Bool :=
  match k, block with
  | 0,     i1 :: i2 :: _ => indepJ i1 i2
  | k + 1, _ :: rest      => checkSwap k rest
  | _,     _              => false

/-- `runBlock` is preserved by one certified adjacent transposition. -/
theorem runBlock_applySwap_eq (s : JState 64) (k : Nat) (block : List (JInstr 64))
    (hcert : checkSwap k block = true) :
    runBlock s block = runBlock s (applySwap k block) := by
  induction k generalizing s block with
  | zero =>
    match block with
    | [] | [_] => simp [checkSwap] at hcert
    | i1 :: i2 :: rest =>
      simp only [checkSwap] at hcert
      exact jinstr_bbSwap_exec s i1 i2 rest hcert
  | succ k ih =>
    match block with
    | [] | [_] => simp [checkSwap] at hcert
    | x :: y :: rest =>
      simp only [checkSwap] at hcert
      -- applySwap (k+1) (x :: y :: rest) = x :: applySwap k (y :: rest)
      -- This holds definitionally by the last arm of applySwap.
      simp only [runBlock_cons]
      exact ih (evalInstr s x) (y :: rest) hcert

/-! ## 8. Permutation soundness -/

/-- Check a sequence of swaps against the evolving block. Returns `(ok, finalBlock)`. -/
def checkAndApply (swaps : List Nat) (block : List (JInstr 64)) :
    Bool × List (JInstr 64) :=
  swaps.foldl (fun (acc : Bool × List (JInstr 64)) k =>
    let (ok, b) := acc
    (ok && checkSwap k b, applySwap k b)) (true, block)

/-- `checkAdjTranspositions`: the full certificate checker. -/
def checkAdjTranspositions (swaps : List Nat) (block : List (JInstr 64)) : Bool :=
  (checkAndApply swaps block).1

/-- **Soundness of the certificate checker**: when `checkAdjTranspositions swaps block = true`,
    `runBlock s (applySwaps swaps block) = runBlock s block`. -/
theorem runBlock_perm_eq (s : JState 64) (swaps : List Nat) (block : List (JInstr 64))
    (hcert : checkAdjTranspositions swaps block = true) :
    runBlock s (applySwaps swaps block) = runBlock s block := by
  -- We prove the stronger invariant:
  -- if (checkAndApply swaps block).1 = true, then
  --   runBlock s (applySwaps swaps block) = runBlock s block
  -- by induction on swaps with the pair (ok, currentBlock) as state.
  suffices h : ∀ (swaps : List Nat) (b : List (JInstr 64)),
      (checkAndApply swaps b).1 = true →
      runBlock s (applySwaps swaps b) = runBlock s b from
    h swaps block hcert
  intro swaps'
  induction swaps' with
  | nil => intro b _; simp [checkAndApply, applySwaps]
  | cons k ks ih =>
    intro b hb
    have hk : checkSwap k b = true := by
      simp only [checkAndApply, List.foldl_cons] at hb
      cases hc : checkSwap k b with
      | true => rfl
      | false =>
        simp [hc] at hb
        have : ∀ ks' b', (List.foldl (fun acc k => (acc.1 && checkSwap k acc.2, applySwap k acc.2))
            (false, b') ks').1 = false := by
          intro ks'
          induction ks' with
          | nil => intro b'; rfl
          | cons k' ks'' ih' => intro b'; simp [List.foldl, ih']
        simp [this] at hb
    have hks : (checkAndApply ks (applySwap k b)).1 = true := by
      simp only [checkAndApply, List.foldl_cons] at hb
      simp only [hk, Bool.true_and] at hb
      exact hb
    have happly : applySwaps (k :: ks) b = applySwaps ks (applySwap k b) := rfl
    rw [happly, ih (applySwap k b) hks]
    exact (runBlock_applySwap_eq s k b hk).symm

end CatCrypt.Crypto.SecureCompilation.X86Backend.RescheduleEquivalence
