/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.BignumToJLoops
public import CatCrypt.Crypto.Jasmin.BignumToJ
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfg
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaX86Mov

/-!
# Structured Jasmin-source programs at the jump level of the x86 instruction set

`BignumToJLoops` translates an imported Jasmin body with `if` and `while` to a structured
program `SProg` over `JInstr 64` blocks and simulates `bignumExecFuel` by the structured run
`runS`. A structured program has no labels and no jumps. This module compiles `SProg` to
labelled `Lprog` code, proves that the run `Isa.lsemFuelMemF` of the x86 instruction set on
the compiled code simulates `runS`, and composes the two simulations into a `CorresIsa`
judgement whose abstract function is `bignumExecFuel`.

## The compilation

`compileS fn S n` returns the code of `S` in the function `fn` and the next unused label,
with the labels of the code taken from the counter `n`:

* a block is the list of the lowerings `jToRMMov` of its instructions;
* `seq p q` is the code of `p` followed by the code of `q`;
* `ite g t e` at the counter `n` is
  `cmp; jcc n; ⟨t⟩; goto n+1; n: ⟨e⟩; n+1:`, where `jcc` jumps when the guard fails;
* `loop pre g post` at the counter `n` is
  `n: ⟨pre⟩; cmp; jcc n+1; ⟨post⟩; goto n; n+1:`, with the guard at the top of each
  iteration and a back jump.

## The fragment

`compileS` is `none` outside the following fragment.

* Blocks: every instruction satisfies `regOnlyB`: `mov`, `add`, `sub`, `imul`, `and`, `or`,
  `xor` with a register or immediate source, `neg`, and `shl`, `shr`, `sar` by an immediate
  below `64`. Loads, stores, and the carry instructions `adc`, `sbb`, `adcx`, `setc`, `bt`
  are excluded.
* Guards (`compileG`): the block `test a, a` with the condition `ne`, and the block
  `cmp a, o` with the condition `ne` or `e`, for `o` a register or an immediate. These are
  the three shapes `BignumToJLoops.guardJ` produces. Each is lowered to the flag compare
  `CMP a, o` (`CMP a, 0` for `test`) followed by a conditional jump on the zero flag: `Z`
  for an `ne` guard and `NZ` for an `e` guard. A guard on any other condition code is
  outside the fragment.

The state relation `RegAgree sa m` states that every register of the address state `sa`
reads back at width `64` from the register file of the machine state `m`. Memory is not
related: the word memory of the `Lprog` state is keyed by a base name and a displacement,
and the memory of `AState` by an address, and the register-only fragment reads and writes
neither.

## Main results

* `compileS`, `compileG`, `regOnlyB`, `stepBound`: the compilation, its fragment and the
  step bound.
* `compileS_labels`: the labels of the compiled code lie between the two counters.
* `block_steps`, `guard_fall`, `guard_exit`: the runs of a block and of a guard with its
  conditional jump.
* `compileS_steps`: the simulation of `runS` by the steps of the compiled code placed
  anywhere in a program body, with at most `stepBound S N` steps.
* `compileS_run`: the run `x86Isa.lsemFuelMemF` of the compiled program at the fuel
  `stepBound S N` halts in a state related to the result of `runS S N`.
* `corresIsa_of_runS`: `CorresIsa x86Isa` of the compiled program against a function that
  agrees with `runS`.
* `corresIsa_of_bignumExec`: `CorresIsa x86Isa` of the compiled translation of a Jasmin
  body against `bignumExecFuel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.JasminJumpLevel

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.BignumToJ
open CatCrypt.Crypto.Jasmin.BignumToJLoops
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF fstepF_lpc_succ
  evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (decC ccPol)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg

/-- Closes an equation between sums of list lengths. -/
macro "len_tac" : tactic =>
  `(tactic| first
    | omega
    | (simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        List.length_singleton]; omega)
    | simp [List.length_append])

/-! ## Labels in a body -/

/-- The label `l`. -/
def lbl (l : LLabel) : LinstrRM := (.Llabel .internal l, .reg none)

/-- The conditional jump to `l` on the condition `c`. -/
def jcc (c : LOperand) (l : LLabel) : LinstrRM := (.Lcond c l, .reg none)

/-- The jump to the label `l` of the function `fn`. -/
def jmp (fn : String) (l : LLabel) : LinstrRM := (.Lgoto (fn, l), .reg none)

/-- The flag compare `CMP a, o`. -/
def cmpWire (a : String) (o : JOperand) : LinstrRM :=
  (.Lopn [.reg a] (withWidthTag 64 "CMP") [.reg a, toLOp o], .reg none)

theorem findLabelMem_nil (l : LLabel) : findLabelMem l [] = none := rfl

theorem findLabelMem_append (l : LLabel) (xs ys : List LinstrRM) :
    findLabelMem l (xs ++ ys) =
      (findLabelMem l xs).or ((findLabelMem l ys).map (· + xs.length)) := by
  simp [findLabelMem, findLabel, List.findIdx?_append]

theorem findLabelMem_append_none {l : LLabel} {xs ys : List LinstrRM} :
    findLabelMem l (xs ++ ys) = none ↔ findLabelMem l xs = none ∧ findLabelMem l ys = none := by
  rw [findLabelMem_append]
  cases findLabelMem l xs <;> cases findLabelMem l ys <;> simp

theorem findLabelMem_cons_none {l : LLabel} {x : LinstrRM} {xs : List LinstrRM} :
    findLabelMem l (x :: xs) = none ↔ isLabel l x.1 = false ∧ findLabelMem l xs = none := by
  simp only [findLabelMem, findLabel, List.map_cons, List.findIdx?_cons]
  cases isLabel l x.1 <;> cases List.findIdx? (isLabel l) (xs.map Prod.fst) <;> simp

/-- The first declaration of `l` in `xs ++ lbl l :: ys`, when `xs` does not declare `l`, is
    at the index `xs.length`. -/
theorem findLabelMem_at {l : LLabel} {body xs ys : List LinstrRM} {q : Nat}
    (hb : body = xs ++ lbl l :: ys) (hx : findLabelMem l xs = none) (hq : xs.length = q) :
    findLabelMem l body = some q := by
  subst hb hq
  rw [findLabelMem_append, hx]
  simp [findLabelMem, findLabel, lbl, isLabel, List.findIdx?_cons]

theorem fetch_at {body xs ys : List LinstrRM} {x : LinstrRM} {k : Nat}
    (hb : body = xs ++ x :: ys) (hk : xs.length = k) : body[k]? = some x := by
  subst hb hk
  simp

theorem isLabel_lbl (l k : Nat) : isLabel l (lbl k).1 = false ↔ ¬ l = k := by
  simp [isLabel, lbl]

@[simp] theorem isLabel_jcc (l k : LLabel) (c : LOperand) : isLabel l (jcc c k).1 = false := rfl

@[simp] theorem isLabel_jmp (l k : LLabel) (fn : String) : isLabel l (jmp fn k).1 = false := rfl

@[simp] theorem isLabel_cmpWire (l : LLabel) (a : String) (o : JOperand) :
    isLabel l (cmpWire a o).1 = false := rfl

/-- A body of `Lopn`s declares no label. -/
theorem findLabelMem_of_isLopn (l : LLabel) (xs : List LinstrRM) (h : ∀ i ∈ xs, IsLopn i) :
    findLabelMem l xs = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [findLabelMem_cons_none]
      refine ⟨?_, ih fun i hi => h i (List.mem_cons_of_mem x hi)⟩
      obtain ⟨d, o, s, hx⟩ := h x (List.mem_cons_self ..)
      rw [hx]
      rfl

/-! ## The fragment -/

/-- The register-only instructions: `mov`, the two-address arithmetic and logic, `neg`, and
    the shifts by an immediate below `64`. -/
def regOnlyB : JInstr 64 → Bool
  | .mov _ _ => true
  | .add _ _ => true
  | .sub _ _ => true
  | .imul _ _ => true
  | .and_ _ _ => true
  | .or_ _ _ => true
  | .xor_ _ _ => true
  | .neg _ => true
  | .shl _ (.imm n) => decide (n < 64)
  | .shr _ (.imm n) => decide (n < 64)
  | .sar _ (.imm n) => decide (n < 64)
  | _ => false

/-- A register-only instruction is accepted by `inMovRegSubsetB`. -/
theorem inMovRegSubsetB_of_regOnlyB (i : JInstr 64) (h : regOnlyB i = true) :
    inMovRegSubsetB i = true := by
  cases i
  case shl d s => cases s <;> simp_all [regOnlyB, inMovRegSubsetB]
  case shr d s => cases s <;> simp_all [regOnlyB, inMovRegSubsetB]
  case sar d s => cases s <;> simp_all [regOnlyB, inMovRegSubsetB]
  all_goals simp_all [regOnlyB, inMovRegSubsetB]

/-- The registers after a register-only instruction are a function of the registers. -/
theorem evalInstr_regs_congr (i : JInstr 64) (hi : regOnlyB i = true) {s t : JState 64}
    (h : s.regs = t.regs) : (evalInstr s i).regs = (evalInstr t i).regs := by
  cases i
  case shl d src =>
    cases src <;> simp_all [regOnlyB, evalInstr, JState.writeB5W]
  case shr d src =>
    cases src <;> simp_all [regOnlyB, evalInstr, JState.writeB5W]
  case sar d src =>
    cases src <;> simp_all [regOnlyB, evalInstr, JState.writeB5W]
  all_goals
    first
      | (simp [regOnlyB] at hi; done)
      | simp [evalInstr, JState.writeB5W, JState.setReg, h]

/-- The lowering of a guard: the flag compare, and the condition-code operand on which the
    conditional jump leaves when the guard fails. -/
def compileG (g : SGuard) : Option (LinstrRM × LOperand) :=
  match g.pre, g.cc with
  | [.test a (.reg b)], .ne => if a = b then some (cmpWire a (.imm 0), .reg "Z") else none
  | [.cmp a o], .ne => some (cmpWire a o, .reg "Z")
  | [.cmp a o], .e => some (cmpWire a o, .reg "NZ")
  | _, _ => none

/-- The compilation of a structured program to labelled code in the function `fn`, with
    labels from the counter; the result is the code and the next unused label. -/
def compileS (fn : String) : SProg → Nat → Option (List LinstrRM × Nat)
  | .block b, n => if b.all regOnlyB = true then some (b.map jToRMMov, n) else none
  | .seq p q, n =>
      (compileS fn p n).bind fun r1 =>
      (compileS fn q r1.2).bind fun r2 => some (r1.1 ++ r2.1, r2.2)
  | .ite g t e, n =>
      (compileG g).bind fun wc =>
      (compileS fn t (n + 2)).bind fun r1 =>
      (compileS fn e r1.2).bind fun r2 =>
        some (wc.1 :: jcc wc.2 n ::
          (r1.1 ++ jmp fn (n + 1) :: lbl n :: (r2.1 ++ [lbl (n + 1)])), r2.2)
  | .loop pre g post, n =>
      (compileG g).bind fun wc =>
      (compileS fn pre (n + 2)).bind fun r1 =>
      (compileS fn post r1.2).bind fun r2 =>
        some (lbl n ::
          (r1.1 ++ wc.1 :: jcc wc.2 (n + 1) :: (r2.1 ++ [jmp fn n, lbl (n + 1)])), r2.2)

/-- A bound on the number of steps of the compiled code of `S`, for a structured run at
    the fuel `N`: the length of a block, the sum for a sequence, the larger branch and
    three control steps for a conditional, and for a loop one label step and, per
    iteration, the two bodies and three control steps. -/
def stepBound : SProg → Nat → Nat
  | .block b, _ => b.length
  | .seq p q, N => stepBound p N + stepBound q N
  | .ite _ t e, N => max (stepBound t N) (stepBound e N) + 3
  | .loop pre _ post, N => N * (stepBound pre N + stepBound post N + 3) + 1

/-- A lowered guard is a flag compare. -/
theorem compileG_wire {g : SGuard} {w : LinstrRM} {c : LOperand}
    (h : compileG g = some (w, c)) : ∃ a o, w = cmpWire a o := by
  unfold compileG at h
  split at h
  · split at h
    · cases h; exact ⟨_, _, rfl⟩
    · cases h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

/-- **The labels of the compiled code** are those from the start counter up to the end
    counter. -/
theorem compileS_labels (fn : String) :
    ∀ (S : SProg) (n n' : Nat) (code : List LinstrRM), compileS fn S n = some (code, n') →
      n ≤ n' ∧ ∀ l, l < n ∨ n' ≤ l → findLabelMem l code = none := by
  intro S
  induction S with
  | block b =>
    intro n n' code h
    simp only [compileS] at h
    split at h
    · next hb =>
      cases h
      refine ⟨Nat.le_refl _, fun l _ => findLabelMem_of_isLopn l _ fun x hx => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact isLopn_jToRMMov i (inMovRegSubsetB_sound i
        (inMovRegSubsetB_of_regOnlyB i (List.all_eq_true.mp hb i hi)))
    · cases h
  | seq p q ihp ihq =>
    intro n n' code h
    simp only [compileS, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cp, n1⟩, hp, ⟨cq, n2⟩, hq, h⟩ := h
    dsimp only at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, l1⟩ := ihp _ _ _ hp
    obtain ⟨h2, l2⟩ := ihq _ _ _ hq
    refine ⟨by omega, fun l hl => ?_⟩
    rw [findLabelMem_append_none]
    exact ⟨l1 l (by omega), l2 l (by omega)⟩
  | ite g t e iht ihe =>
    intro n n' code h
    simp only [compileS, Option.bind_eq_some_iff] at h
    obtain ⟨⟨w, c⟩, hg, ⟨ct, n1⟩, ht, ⟨ce, n2⟩, he, h⟩ := h
    dsimp only at he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨a, o, rfl⟩ := compileG_wire hg
    obtain ⟨h1, l1⟩ := iht _ _ _ ht
    obtain ⟨h2, l2⟩ := ihe _ _ _ he
    refine ⟨by omega, fun l hl => ?_⟩
    simp only [findLabelMem_cons_none, findLabelMem_append_none, findLabelMem_nil,
      isLabel_cmpWire, isLabel_jcc, isLabel_jmp, isLabel_lbl, true_and,
      and_true]
    exact ⟨l1 l (by omega), by omega, l2 l (by omega), by omega⟩
  | loop p g q ihp ihq =>
    intro n n' code h
    simp only [compileS, Option.bind_eq_some_iff] at h
    obtain ⟨⟨w, c⟩, hg, ⟨cp, n1⟩, hp, ⟨cq, n2⟩, hq, h⟩ := h
    dsimp only at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨a, o, rfl⟩ := compileG_wire hg
    obtain ⟨h1, l1⟩ := ihp _ _ _ hp
    obtain ⟨h2, l2⟩ := ihq _ _ _ hq
    refine ⟨by omega, fun l hl => ?_⟩
    simp only [findLabelMem_cons_none, findLabelMem_append_none, findLabelMem_nil,
      isLabel_cmpWire, isLabel_jcc, isLabel_jmp, isLabel_lbl, true_and,
      and_true]
    exact ⟨by omega, l1 l (by omega), l2 l (by omega), by omega⟩

/-! ## The state relation -/

/-- Every register of the address state reads back at width `64` from the register file of
    the machine state. -/
def RegAgree (sa : AState) (m : LstateMF) : Prop :=
  ∀ r, m.prog.base.reg.getW r 64 = some (sa.regs r)

theorem getW_congr {s t : LstateN} (h : s.lvm = t.lvm) (r : String) (w : Nat) :
    s.getW r w = t.getW r w := by
  unfold LstateN.getW
  rw [h]

theorem RegAgree.congr {sa sa' : AState} {m m' : LstateMF} (h : RegAgree sa m)
    (hr : sa'.regs = sa.regs) (hm : m'.prog.base.reg.lvm = m.prog.base.reg.lvm) :
    RegAgree sa' m' := fun r => by
  rw [getW_congr hm, hr]
  exact h r

theorem RegAgree.next {sa : AState} {m : LstateMF} (h : RegAgree sa m) :
    RegAgree sa (next m) :=
  h.congr rfl rfl

theorem RegAgree.goto {sa : AState} {m : LstateMF} (h : RegAgree sa m) (k : Nat) :
    RegAgree sa (goto m k) :=
  h.congr rfl rfl

theorem atPc_cast {P : LprogM} {k k' : Nat} {m : LstateMF} (h : atPc P k m) (hk : k = k') :
    atPc P k' m :=
  hk ▸ h

/-! ## Blocks -/

/-- **The list run of a lowered block.** From a state whose registers agree with `sa`, the
    steps of the lowering of a register-only block succeed and end in a state whose
    registers agree with `runBlockA sa b`. -/
theorem block_runL (P : LprogM) :
    ∀ (b : List (JInstr 64)), b.all regOnlyB = true → ∀ (sa : AState) (m : LstateMF),
      RegAgree sa m →
      ∃ m', x86Isa.runL P (b.map jToRMMov) m = some m' ∧ RegAgree (runBlockA sa b) m' := by
  intro b
  induction b with
  | nil => intro _ sa m hc; exact ⟨m, rfl, hc⟩
  | cons i is ih =>
    intro hb sa m hc
    rw [List.all_cons, Bool.and_eq_true] at hb
    have hsub : InMovRegSubset i :=
      inMovRegSubsetB_sound i (inMovRegSubsetB_of_regOnlyB i hb.1)
    obtain ⟨b1, hstep, hcorr⟩ := fstepF_jToRMMov i hsub
      { regs := sa.regs, flags := sa.flags, mem := m.prog.base.lmem } m.prog.base m.zf
      ⟨hc, fun _ _ => rfl⟩
    have hev : x86Isa.step P (jToRMMov i) m
        = some { prog := { m.prog with base := b1 }, zf := m.zf } := by
      show evalInstrPMemF P (jToRMMov i) m = _
      rw [evalInstrPMemF_isLopn P _ m (isLopn_jToRMMov i hsub), hstep]
      rfl
    have hc1 : RegAgree (evalInstrA sa i) { prog := { m.prog with base := b1 }, zf := m.zf } := by
      intro r
      show b1.reg.getW r 64 = some ((evalInstr sa.view i).regs r)
      rw [hcorr.regAgree r, runBlock_cons, runBlock_nil]
      exact congrArg (fun f => some (f r)) (evalInstr_regs_congr i hb.1
        (s := { regs := sa.regs, flags := sa.flags, mem := m.prog.base.lmem }) (t := sa.view) rfl)
    obtain ⟨m', hrun, hc'⟩ := ih hb.2 _ _ hc1
    exact ⟨m', by simp only [List.map_cons, Isa.runL, hev, Option.bind_some, hrun], hc'⟩

/-- A step of an `Lopn` stays in the function and advances the counter by one. -/
theorem step_isLopn (P : LprogM) (i : LinstrRM) (hi : IsLopn i) (u u' : LstateMF)
    (h : x86Isa.step P i u = some u') :
    u'.prog.lfn = u.prog.lfn ∧ u'.prog.base.lpc = u.prog.base.lpc + 1 := by
  have h' : evalInstrPMemF P i u = some u' := h
  rw [evalInstrPMemF_isLopn P i u hi] at h'
  obtain ⟨⟨b, z⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h'
  exact ⟨rfl, fstepF_lpc_succ i u.prog.base b u.zf z hf⟩

/-- **A lowered block in a body.** When the body of `P` is `pre ++ b.map jToRMMov ++ post`
    for a register-only block `b`, a state at the counter `pre.length` whose registers agree
    with `sa` reaches, in `b.length` steps, the counter after the block in a state whose
    registers agree with `runBlockA sa b`. -/
theorem block_steps (P : LprogM) (b : List (JInstr 64)) (hb : b.all regOnlyB = true)
    (pre post : List LinstrRM) (hbody : P.body = pre ++ b.map jToRMMov ++ post)
    (sa : AState) (m : LstateMF) (hat : atPc P pre.length m) (hc : RegAgree sa m) :
    ∃ m', Steps x86Isa P b.length m m' ∧
      atPc P (pre.length + (b.map jToRMMov).length) m' ∧ RegAgree (runBlockA sa b) m' := by
  obtain ⟨m', hrun, hc'⟩ := block_runL P b hb sa m hc
  obtain ⟨hs, hat'⟩ := steps_of_runL x86Isa P (b.map jToRMMov) pre post m m' hbody hat
    (fun x hx u u' hu => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact step_isLopn P _ (isLopn_jToRMMov i (inMovRegSubsetB_sound i
        (inMovRegSubsetB_of_regOnlyB i (List.all_eq_true.mp hb i hi)))) u u' hu)
    hrun
  rw [List.length_map] at hs
  exact ⟨m', hs, hat', hc'⟩

/-! ## Guards -/

theorem evalOperandN_toLOp (o : JOperand) {sa : AState} {m : LstateMF} (hc : RegAgree sa m) :
    evalOperandN m.prog.base.reg 64 (toLOp o) = some (o.eval sa.view) := by
  cases o with
  | reg r => exact hc r
  | imm n => rfl

/-- The flag compare `CMP a, o` sets the zero flag to the equality of the operands and
    advances the counter. -/
theorem cmpWire_step (P : LprogM) (a : String) (o : JOperand) {sa : AState} {m : LstateMF}
    (hc : RegAgree sa m) :
    x86Isa.step P (cmpWire a o) m =
      some { prog := { m.prog with base := m.prog.base.nextPc },
             zf := sa.regs a == o.eval sa.view } := by
  show evalInstrPMemF P (cmpWire a o) m = _
  have hargs : cmpArgs? (cmpWire a o) = some (.reg a, toLOp o) := by
    simp [cmpArgs?, cmpWire]
  unfold evalInstrPMemF
  rw [hargs]
  simp only []
  rw [show evalOperandN m.prog.base.reg 64 (.reg a) = some (sa.regs a) from hc a,
    evalOperandN_toLOp o hc]

/-- **The step of a lowered guard.** The compare advances the counter and keeps the
    registers; the guard block keeps the registers; and the jump condition holds in the
    state after the compare exactly when the guard fails. -/
theorem compileG_step (P : LprogM) {g : SGuard} {w : LinstrRM} {c : LOperand}
    (hg : compileG g = some (w, c)) {sa : AState} {m : LstateMF} (hc : RegAgree sa m) :
    ∃ z, x86Isa.step P w m =
        some { prog := { m.prog with base := m.prog.base.nextPc }, zf := z } ∧
      x86Isa.condEval { prog := { m.prog with base := m.prog.base.nextPc }, zf := z } c
        = !g.holds sa ∧
      (g.run sa).regs = sa.regs := by
  obtain ⟨pre, cc⟩ := g
  unfold compileG at hg
  split at hg
  · next a b hpre hcc =>
    simp only at hpre hcc
    subst hpre hcc
    split at hg
    · next hab =>
      subst hab
      cases hg
      obtain ⟨h1, -, h3⟩ := test_view sa a
      refine ⟨_, cmpWire_step P a (.imm 0) hc, ?_, h1⟩
      show decC _ (.reg "Z") = !(evalInstrA sa (.test a (.reg a))).view.condB .ne
      rw [h3]
      simp [decC, ccPol, bne]
    · cases hg
  · next a o hpre hcc =>
    simp only at hpre hcc
    subst hpre hcc
    cases hg
    obtain ⟨h1, -, -, h4⟩ := cmp_view sa a o
    refine ⟨_, cmpWire_step P a o hc, ?_, h1⟩
    show decC _ (.reg "Z") = !(evalInstrA sa (.cmp a o)).view.condB .ne
    rw [h4]
    simp [decC, ccPol]
    rfl
  · next a o hpre hcc =>
    simp only at hpre hcc
    subst hpre hcc
    cases hg
    obtain ⟨h1, -, h3, -⟩ := cmp_view sa a o
    refine ⟨_, cmpWire_step P a o hc, ?_, h1⟩
    show decC _ (.reg "NZ") = !(evalInstrA sa (.cmp a o)).view.condB .e
    rw [h3]
    simp [decC, ccPol]
    rfl
  · cases hg

/-- **A guard that holds**: the compare and the conditional jump are two steps to the
    counter after the jump. -/
theorem guard_fall (P : LprogM) {g : SGuard} {w : LinstrRM} {c : LOperand} {l : LLabel}
    (hg : compileG g = some (w, c)) {sa : AState} {m : LstateMF} {k : Nat}
    (hc : RegAgree sa m) (hat : atPc P k m) (hw : P.body[k]? = some w)
    (hj : P.body[k + 1]? = some (jcc c l)) (hh : g.holds sa = true) :
    ∃ m', Steps x86Isa P 2 m m' ∧ atPc P (k + 2) m' ∧ RegAgree (g.run sa) m' := by
  obtain ⟨z, hstep, hcond, hregs⟩ := compileG_step P hg hc
  rw [hh] at hcond
  have hat1 : atPc P (k + 1)
      { prog := { m.prog with base := m.prog.base.nextPc }, zf := z } :=
    ⟨hat.1, by simp only [LstateM.lpc_nextPc, hat.2]⟩
  obtain ⟨hs2, hat2⟩ := steps_cond_not_taken x86Isa hat1 hj hcond
  exact ⟨_, (Steps.one (by rw [lsemStepPMemF_of_atPc x86Isa hat hw, hstep])).trans hs2, hat2,
    hc.congr hregs rfl⟩

/-- **A guard that fails**: the compare and the conditional jump are two steps to the
    counter after the label of the jump. -/
theorem guard_exit (P : LprogM) {g : SGuard} {w : LinstrRM} {c : LOperand} {l : LLabel}
    (hg : compileG g = some (w, c)) {sa : AState} {m : LstateMF} {k q : Nat}
    (hc : RegAgree sa m) (hat : atPc P k m) (hw : P.body[k]? = some w)
    (hj : P.body[k + 1]? = some (jcc c l)) (hl : findLabelMem l P.body = some q)
    (hh : g.holds sa = false) :
    ∃ m', Steps x86Isa P 2 m m' ∧ atPc P (q + 1) m' ∧ RegAgree (g.run sa) m' := by
  obtain ⟨z, hstep, hcond, hregs⟩ := compileG_step P hg hc
  rw [hh] at hcond
  have hat1 : atPc P (k + 1)
      { prog := { m.prog with base := m.prog.base.nextPc }, zf := z } :=
    ⟨hat.1, by simp only [LstateM.lpc_nextPc, hat.2]⟩
  obtain ⟨hs2, -⟩ := steps_cond_taken x86Isa hat1 hj hcond hl
  exact ⟨_, (Steps.one (by rw [lsemStepPMemF_of_atPc x86Isa hat hw, hstep])).trans hs2,
    atPc_goto (q + 1) hat1, hc.congr hregs rfl⟩

/-- A jump to a label of the body is one step to the counter after the label. -/
theorem goto_step (P : LprogM) {m : LstateMF} {k q : Nat} {l : LLabel} (hat : atPc P k m)
    (hi : P.body[k]? = some (jmp P.lfn l)) (hl : findLabelMem l P.body = some q) :
    Steps x86Isa P 1 m (goto m (q + 1)) ∧ atPc P (q + 1) (goto m (q + 1)) :=
  ⟨(steps_goto x86Isa hat hi hl).1, atPc_goto (q + 1) hat⟩

/-! ## The simulation -/

/-- **The simulation of the structured run by the compiled code.** Let `code` be the
    compiled code of `S` with labels from `n`, placed in the body of `P` after a prefix
    `pre` that declares no label from `n` on. If `runS S N` takes `sa` to `sa'`, then from a
    state at the counter `pre.length` whose registers agree with `sa`, at most
    `stepBound S N` steps of `P` reach the counter after the code in a state whose registers
    agree with `sa'`. -/
theorem compileS_steps (fn : String) (N : Nat) :
    ∀ (S : SProg) (n n' : Nat) (code : List LinstrRM), compileS fn S n = some (code, n') →
    ∀ (P : LprogM) (pre post : List LinstrRM), P.lfn = fn → P.body = pre ++ code ++ post →
      (∀ l, n ≤ l → findLabelMem l pre = none) →
      ∀ (sa sa' : AState) (m : LstateMF), runS S N sa = some sa' → atPc P pre.length m →
        RegAgree sa m →
        ∃ k m', k ≤ stepBound S N ∧ Steps x86Isa P k m m' ∧
          atPc P (pre.length + code.length) m' ∧ RegAgree sa' m' := by
  intro S
  induction S with
  | block b =>
    intro n n' code hcomp P pre post hfn hbody hpre sa sa' m hrun hat hc
    simp only [compileS] at hcomp
    split at hcomp
    · next hb =>
      cases hcomp
      simp only [runS, Option.some.injEq] at hrun
      subst hrun
      obtain ⟨m', hs, hat', hc'⟩ := block_steps P b hb pre post hbody sa m hat hc
      exact ⟨_, m', Nat.le_refl _, hs, hat', hc'⟩
    · cases hcomp
  | seq p q ihp ihq =>
    intro n n' code hcomp P pre post hfn hbody hpre sa sa' m hrun hat hc
    simp only [compileS, Option.bind_eq_some_iff] at hcomp
    obtain ⟨⟨cp, n1⟩, hp, ⟨cq, n2⟩, hq, hcode⟩ := hcomp
    simp only [Option.some.injEq, Prod.mk.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    simp only [runS, Option.bind_eq_some_iff] at hrun
    obtain ⟨sa1, hr1, hr2⟩ := hrun
    obtain ⟨hn1, hl1⟩ := compileS_labels fn p _ _ _ hp
    obtain ⟨k1, m1, hk1, hs1, hat1, hc1⟩ := ihp n n1 cp hp P pre (cq ++ post) hfn
      (by rw [hbody]; simp only [List.append_assoc]) hpre sa sa1 m hr1 hat hc
    obtain ⟨k2, m2, hk2, hs2, hat2, hc2⟩ := ihq n1 n2 cq hq P (pre ++ cp) post hfn
      (by rw [hbody]; simp only [List.append_assoc])
      (fun l hl => findLabelMem_append_none.mpr ⟨hpre l (by omega), hl1 l (Or.inr hl)⟩)
      sa1 sa' m1 hr2 (atPc_cast hat1 (by len_tac)) hc1
    exact ⟨k1 + k2, m2, by simp only [stepBound]; omega, hs1.trans hs2,
      atPc_cast hat2 (by len_tac), hc2⟩
  | ite g t e iht ihe =>
    intro n n' code hcomp P pre post hfn hbody hpre sa sa' m hrun hat hc
    simp only [compileS, Option.bind_eq_some_iff] at hcomp
    obtain ⟨⟨w, c⟩, hg, ⟨ct, n1⟩, ht, ⟨ce, n2⟩, he, hcode⟩ := hcomp
    dsimp only at he
    simp only [Option.some.injEq, Prod.mk.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    obtain ⟨hn1, hlt⟩ := compileS_labels fn t _ _ _ ht
    obtain ⟨hn2, hle⟩ := compileS_labels fn e _ _ _ he
    obtain ⟨a, o, rfl⟩ := compileG_wire hg
    subst hfn
    simp only [runS] at hrun
    have hw : P.body[pre.length]? = some (cmpWire a o) :=
      fetch_at (xs := pre)
        (ys := jcc c n :: (ct ++ jmp P.lfn (n + 1) :: lbl n :: (ce ++ lbl (n + 1) :: post)))
        (by rw [hbody]; simp) rfl
    have hj : P.body[pre.length + 1]? = some (jcc c n) :=
      fetch_at (xs := pre ++ [cmpWire a o])
        (ys := ct ++ jmp P.lfn (n + 1) :: lbl n :: (ce ++ lbl (n + 1) :: post))
        (by rw [hbody]; simp) (by len_tac)
    by_cases hh : g.holds sa = true
    · rw [if_pos hh] at hrun
      obtain ⟨m1, hs1, hat1, hc1⟩ := guard_fall P hg hc hat hw hj hh
      obtain ⟨k, m2, hk, hs2, hat2, hc2⟩ := iht (n + 2) n1 ct ht P
        (pre ++ [cmpWire a o, jcc c n])
        (jmp P.lfn (n + 1) :: lbl n :: (ce ++ lbl (n + 1) :: post)) rfl
        (by rw [hbody]; simp)
        (fun l hl => by
          simp only [findLabelMem_append_none, findLabelMem_cons_none, findLabelMem_nil,
            isLabel_cmpWire, isLabel_jcc, and_self, and_true]
          exact hpre l (by omega))
        _ sa' m1 hrun (atPc_cast hat1 (by len_tac)) hc1
      have hgo : P.body[pre.length + ct.length + 2]? = some (jmp P.lfn (n + 1)) :=
        fetch_at (xs := pre ++ cmpWire a o :: jcc c n :: ct)
          (ys := lbl n :: (ce ++ lbl (n + 1) :: post)) (by rw [hbody]; simp) (by len_tac)
      have hLend : findLabelMem (n + 1) P.body
          = some (pre.length + ct.length + ce.length + 4) :=
        findLabelMem_at
          (xs := pre ++ cmpWire a o :: jcc c n :: (ct ++ jmp P.lfn (n + 1) :: lbl n :: ce))
          (ys := post) (by rw [hbody]; simp)
          (by
            simp only [findLabelMem_append_none, findLabelMem_cons_none, isLabel_cmpWire,
              isLabel_jcc, isLabel_jmp, isLabel_lbl, true_and]
            exact ⟨hpre _ (by omega), hlt _ (by omega), by omega, hle _ (by omega)⟩)
          (by len_tac)
      obtain ⟨hs3, hat3⟩ := goto_step P (atPc_cast hat2 (by len_tac)) hgo hLend
      exact ⟨2 + k + 1, _,
        le_trans (by omega : 2 + k + 1 ≤ stepBound t N + 3)
          (Nat.add_le_add_right (Nat.le_max_left _ _) 3),
        (hs1.trans hs2).trans hs3, atPc_cast hat3 (by len_tac), hc2.goto _⟩
    · rw [if_neg hh] at hrun
      have hLelse : findLabelMem n P.body = some (pre.length + ct.length + 3) :=
        findLabelMem_at
          (xs := pre ++ cmpWire a o :: jcc c n :: (ct ++ [jmp P.lfn (n + 1)]))
          (ys := ce ++ lbl (n + 1) :: post) (by rw [hbody]; simp)
          (by
            simp only [findLabelMem_append_none, findLabelMem_cons_none, findLabelMem_nil,
              isLabel_cmpWire, isLabel_jcc, isLabel_jmp, true_and, and_true]
            exact ⟨hpre _ (Nat.le_refl _), hlt _ (by omega)⟩)
          (by len_tac)
      obtain ⟨m1, hs1, hat1, hc1⟩ :=
        guard_exit P hg hc hat hw hj hLelse (by simpa using hh)
      obtain ⟨k, m2, hk, hs2, hat2, hc2⟩ := ihe n1 n2 ce he P
        (pre ++ cmpWire a o :: jcc c n :: (ct ++ [jmp P.lfn (n + 1), lbl n]))
        (lbl (n + 1) :: post) rfl (by rw [hbody]; simp)
        (fun l hl => by
          simp only [findLabelMem_append_none, findLabelMem_cons_none, findLabelMem_nil,
            isLabel_cmpWire, isLabel_jcc, isLabel_jmp, isLabel_lbl,
            true_and, and_true]
          exact ⟨hpre l (by omega), hlt l (by omega), by omega⟩)
        _ sa' m1 hrun (atPc_cast hat1 (by len_tac)) hc1
      have hend : P.body[pre.length + ct.length + ce.length + 4]? = some (lbl (n + 1)) :=
        fetch_at
          (xs := pre ++ cmpWire a o :: jcc c n :: (ct ++ jmp P.lfn (n + 1) :: lbl n :: ce))
          (ys := post) (by rw [hbody]; simp) (by len_tac)
      obtain ⟨hs3, hat3⟩ := steps_label x86Isa (atPc_cast hat2 (by len_tac)) hend
      exact ⟨2 + k + 1, _,
        le_trans (by omega : 2 + k + 1 ≤ stepBound e N + 3)
          (Nat.add_le_add_right (Nat.le_max_right _ _) 3),
        (hs1.trans hs2).trans hs3, atPc_cast hat3 (by len_tac), hc2.next⟩
  | loop p g q ihp ihq =>
    intro n n' code hcomp P pre post hfn hbody hpre sa sa' m hrun hat hc
    simp only [compileS, Option.bind_eq_some_iff] at hcomp
    obtain ⟨⟨w, c⟩, hg, ⟨cp, n1⟩, hp, ⟨cq, n2⟩, hq, hcode⟩ := hcomp
    dsimp only at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    obtain ⟨hn1, hlp⟩ := compileS_labels fn p _ _ _ hp
    obtain ⟨hn2, hlq⟩ := compileS_labels fn q _ _ _ hq
    obtain ⟨a, o, rfl⟩ := compileG_wire hg
    subst hfn
    simp only [runS, Option.map_eq_some_iff] at hrun
    obtain ⟨cfin, hloop, rfl⟩ := hrun
    have hl0 : P.body[pre.length]? = some (lbl n) :=
      fetch_at (xs := pre)
        (ys := cp ++ cmpWire a o :: jcc c (n + 1) :: (cq ++ jmp P.lfn n :: lbl (n + 1) :: post))
        (by rw [hbody]; simp) rfl
    have hw : P.body[pre.length + cp.length + 1]? = some (cmpWire a o) :=
      fetch_at (xs := pre ++ lbl n :: cp)
        (ys := jcc c (n + 1) :: (cq ++ jmp P.lfn n :: lbl (n + 1) :: post))
        (by rw [hbody]; simp) (by len_tac)
    have hj : P.body[pre.length + cp.length + 1 + 1]? = some (jcc c (n + 1)) :=
      fetch_at (xs := pre ++ lbl n :: (cp ++ [cmpWire a o]))
        (ys := cq ++ jmp P.lfn n :: lbl (n + 1) :: post)
        (by rw [hbody]; simp) (by len_tac)
    have hgo : P.body[pre.length + cp.length + cq.length + 3]? = some (jmp P.lfn n) :=
      fetch_at (xs := pre ++ lbl n :: (cp ++ cmpWire a o :: jcc c (n + 1) :: cq))
        (ys := lbl (n + 1) :: post) (by rw [hbody]; simp) (by len_tac)
    have hLtop : findLabelMem n P.body = some pre.length :=
      findLabelMem_at (xs := pre)
        (ys := cp ++ cmpWire a o :: jcc c (n + 1) :: (cq ++ jmp P.lfn n :: lbl (n + 1) :: post))
        (by rw [hbody]; simp) (hpre _ (Nat.le_refl _)) rfl
    have hLend : findLabelMem (n + 1) P.body
        = some (pre.length + cp.length + cq.length + 4) :=
      findLabelMem_at
        (xs := pre ++ lbl n :: (cp ++ cmpWire a o :: jcc c (n + 1) :: (cq ++ [jmp P.lfn n])))
        (ys := post) (by rw [hbody]; simp)
        (by
          simp only [findLabelMem_append_none, findLabelMem_cons_none, findLabelMem_nil,
            isLabel_cmpWire, isLabel_jcc, isLabel_jmp, isLabel_lbl,
            true_and, and_true]
          exact ⟨hpre _ (by omega), by omega, hlp _ (by omega), hlq _ (by omega)⟩)
        (by len_tac)
    have key : ∀ (j : Nat) (sa : AState) (m : LstateMF) (cf : AState × Bool),
        BignumToJLoops.loopRun (BignumToJLoops.loopStep (runS p N) (runS q N) g) j (sa, false)
          = some cf →
        atPc P (pre.length + 1) m → RegAgree sa m →
        ∃ k m', k ≤ j * (stepBound p N + stepBound q N + 3) ∧ Steps x86Isa P k m m' ∧
          atPc P (pre.length + cp.length + cq.length + 5) m' ∧ RegAgree cf.1 m' := by
      intro j
      induction j with
      | zero => intro sa m cf h; simp [loopRun] at h
      | succ j ih =>
        intro sa m cf h hat hc
        simp only [loopRun, Bool.false_eq_true, if_false, Option.bind_eq_some_iff] at h
        obtain ⟨c1, hst, hrest⟩ := h
        simp only [BignumToJLoops.loopStep, Bool.false_eq_true, if_false,
          Option.bind_eq_some_iff] at hst
        obtain ⟨sa1, hpr, hst⟩ := hst
        obtain ⟨k1, m1, hk1, hs1, hat1, hc1⟩ := ihp (n + 2) n1 cp hp P (pre ++ [lbl n])
          (cmpWire a o :: jcc c (n + 1) :: (cq ++ jmp P.lfn n :: lbl (n + 1) :: post)) rfl
          (by rw [hbody]; simp)
          (fun l hl => by
            simp only [findLabelMem_append_none, findLabelMem_cons_none, findLabelMem_nil,
              isLabel_lbl, and_true]
            exact ⟨hpre l (by omega), by omega⟩)
          sa sa1 m hpr (atPc_cast hat (by len_tac)) hc
        by_cases hh : g.holds sa1 = true
        · rw [if_pos hh, Option.map_eq_some_iff] at hst
          obtain ⟨sa2, hqr, rfl⟩ := hst
          obtain ⟨m2, hs2, hat2, hc2⟩ :=
            guard_fall P hg hc1 (atPc_cast hat1 (by len_tac)) hw hj hh
          obtain ⟨k3, m3, hk3, hs3, hat3, hc3⟩ := ihq n1 n2 cq hq P
            (pre ++ lbl n :: (cp ++ [cmpWire a o, jcc c (n + 1)]))
            (jmp P.lfn n :: lbl (n + 1) :: post) rfl (by rw [hbody]; simp)
            (fun l hl => by
              simp only [findLabelMem_append_none, findLabelMem_cons_none, findLabelMem_nil,
                isLabel_cmpWire, isLabel_jcc, isLabel_lbl, and_true]
              exact ⟨hpre l (by omega), by omega, hlp l (by omega)⟩)
            _ sa2 m2 hqr (atPc_cast hat2 (by len_tac)) hc2
          obtain ⟨hs4, hat4⟩ := goto_step P (atPc_cast hat3 (by len_tac)) hgo hLtop
          obtain ⟨k5, m5, hk5, hs5, hat5, hc5⟩ := ih sa2 _ cf hrest hat4 (hc3.goto _)
          exact ⟨k1 + 2 + k3 + 1 + k5, m5, by rw [Nat.succ_mul]; omega,
            (((hs1.trans hs2).trans hs3).trans hs4).trans hs5, hat5, hc5⟩
        · rw [if_neg hh, Option.some.injEq] at hst
          subst hst
          rw [loopRun_exited _ _ _ rfl, Option.some.injEq] at hrest
          subst hrest
          obtain ⟨m2, hs2, hat2, hc2⟩ :=
            guard_exit P hg hc1 (atPc_cast hat1 (by len_tac)) hw hj hLend (by simpa using hh)
          exact ⟨k1 + 2, m2, by rw [Nat.succ_mul]; omega, hs1.trans hs2, hat2, hc2⟩
    obtain ⟨hs0, hat0⟩ := steps_label x86Isa hat hl0
    obtain ⟨k, m', hk, hs, hat', hc'⟩ := key N sa (next m) cfin hloop hat0 hc.next
    exact ⟨1 + k, m', by simp only [stepBound]; omega, hs0.trans hs,
      atPc_cast hat' (by len_tac), hc'⟩

/-- **The run of the compiled program.** If `runS S N` takes `sa` to `sa'`, the run of the
    x86 instruction set on the compiled program at the fuel `stepBound S N`, from a state at
    the counter `0` whose registers agree with `sa`, halts at the end of the code in a state
    whose registers agree with `sa'`. -/
theorem compileS_run (fn : String) (S : SProg) (n n' : Nat) (code : List LinstrRM)
    (hcomp : compileS fn S n = some (code, n')) (N : Nat) (sa sa' : AState) (m : LstateMF)
    (hrun : runS S N sa = some sa') (hat : atPc (singletonProgM fn code) 0 m)
    (hc : RegAgree sa m) :
    ∃ m', x86Isa.lsemFuelMemF (singletonProgM fn code) (stepBound S N) m = some m' ∧
      atPc (singletonProgM fn code) code.length m' ∧ RegAgree sa' m' := by
  obtain ⟨k, m', hk, hs, hat', hc'⟩ := compileS_steps fn N S n n' code hcomp
    (singletonProgM fn code) [] [] rfl (by simp [singletonProgM])
    (fun l _ => findLabelMem_nil l) sa sa' m hrun hat hc
  have hat'' : atPc (singletonProgM fn code) code.length m' := atPc_cast hat' (by simp)
  have hrun' := lsemFuelMemF_of_steps x86Isa _ hs (halted_of_atPc hat'' (Nat.le_refl _))
    (stepBound S N - k)
  rw [Nat.add_sub_cancel' hk] at hrun'
  exact ⟨m', hrun', hat'', hc'⟩

/-! ## The correspondence -/

/-- The side relation at the jump level: the machine state is in the function `fn` at the
    counter of the abstract pair, and its registers read back the registers `regs a` of the
    abstract state. -/
def RegSR {A : Type} (fn : String) (regs : A → String → BitVec 64) (m : LstateMF)
    (a : A × Nat) : Prop :=
  m.prog.lfn = fn ∧ m.prog.base.lpc = a.2 ∧
    ∀ r, m.prog.base.reg.getW r 64 = some (regs a.1 r)

/-- **`CorresIsa` of a compiled structured program.** If the abstract function `fa` agrees
    with the structured run on the states of `Pre` (`hfa`), the compiled program corresponds
    to `fa` at the fuel `stepBound S N`, from the counter `0` to the end of the code, under
    register agreement. -/
theorem corresIsa_of_runS (fn : String) (S : SProg) (n n' : Nat) (code : List LinstrRM)
    (hcomp : compileS fn S n = some (code, n')) (N : Nat) (Pre : AState → Prop)
    (fa : AState → AState) (hfa : ∀ sa, Pre sa → runS S N sa = some (fa sa)) :
    CorresIsa x86Isa (singletonProgM fn code) (RegSR fn AState.regs)
      (fun a => Pre a.1 ∧ a.2 = 0) (fun a => (fa a.1, code.length)) (stepBound S N) := by
  rintro m ⟨sa, k⟩ ⟨hfn, hpc, hreg⟩ ⟨hPre, hk⟩
  simp only at hpc hreg hPre hk
  subst hk
  obtain ⟨m', hrun, hat', hc'⟩ := compileS_run fn S n n' code hcomp N sa (fa sa) m
    (hfa sa hPre) ⟨hfn, hpc⟩ hreg
  exact ⟨m', hrun, hat'.1, hat'.2, hc'⟩

/-- An address state related to a `BignumState`: the same registers, and each defined byte
    at its address. -/
def aOf (s : BignumState) : AState where
  regs := s.regs
  mem := fun x => ((s.mem (UInt64.ofBitVec x)).getD 0).toBitVec

theorem bjCorr_aOf (s : BignumState) : BJCorr s (aOf s) := by
  refine ⟨rfl, fun a b h => ?_⟩
  show ((s.mem a).getD 0).toBitVec = b.toBitVec
  rw [h]
  rfl

/-- **`CorresIsa` of a Jasmin body at the jump level.** Let `body` be an imported Jasmin
    body with structured translation `S` (`toSB`) and compiled code `code` (`compileS`).
    The compiled program corresponds, under the x86 instruction set and register agreement,
    to the function `bignumExecFuel reg fuel body` on the states where that run is defined,
    at the fuel `stepBound S fuel`, from the counter `0` to the end of the code. -/
theorem corresIsa_of_bignumExec (reg : BignumRegistry) (fuel : Nat) (body : List InstrR)
    (S : SProg) (hS : toSB body = some S) (fn : String) (n n' : Nat) (code : List LinstrRM)
    (hcomp : compileS fn S n = some (code, n')) :
    CorresIsa x86Isa (singletonProgM fn code) (RegSR fn BignumState.regs)
      (fun a => (bignumExecFuel reg fuel body a.1).isSome = true ∧ a.2 = 0)
      (fun a => ((bignumExecFuel reg fuel body a.1).getD a.1, code.length))
      (stepBound S fuel) := by
  rintro m ⟨s, k⟩ ⟨hfn, hpc, hreg⟩ ⟨hdef, hk⟩
  simp only at hpc hreg hdef hk
  subst hk
  obtain ⟨s', he⟩ := Option.isSome_iff_exists.mp hdef
  obtain ⟨sa', hr, hc'⟩ :=
    bignumExecFuel_runS_sim reg fuel body S s s' (aOf s) hS (bjCorr_aOf s) he
  obtain ⟨m', hrun, hat', hreg'⟩ := compileS_run fn S n n' code hcomp fuel (aOf s) sa' m hr
    ⟨hfn, hpc⟩ hreg
  refine ⟨m', hrun, hat'.1, hat'.2, fun r => ?_⟩
  simp only [he, Option.getD_some]
  rw [hreg' r, hc'.1]

end CatCrypt.Crypto.SecureCompilation.Ascent.JasminJumpLevel
