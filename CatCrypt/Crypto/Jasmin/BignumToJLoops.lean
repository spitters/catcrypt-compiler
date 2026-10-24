/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.BignumToJCalls
public import HaxAscent.Calculus.CorresMCutPoint

@[expose] public section

set_option autoImplicit false

/-!
# Conditionals and `while` loops in the bignum-to-`JInstr 64` translation

`BignumToJ.toJBlock` translates a straight-line body, and the address machine `runBlockA`
runs straight-line code. A body that `bignumExecFuel` runs may also contain `Cif` and
`Cwhile`. This module translates such a body to a structured program `SProg` whose leaves
are translated blocks and whose `ite` and `loop` nodes are explicit, gives the structured
programs a run `runS` over the address machine, and proves that `runS` simulates
`bignumExecFuel`.

## Guards

`bignumExecFuel` evaluates the guard of a `Cif` or `Cwhile` with `evalPExpr` and takes the
branch when the value is not `0`. The translation `guardJ` of a guard is a pair `SGuard` of
a block that sets the flags and a condition code read through `JState.condB`:

* a variable `x` is `test x, x` with the condition `ne`;
* `x != e` and `x == e`, for `e` a constant or a variable, are `cmp x, e` with the
  conditions `ne` and `e`.

`test` and `cmp` write no register and no memory cell, so the state relation `BJCorr`
holds after the guard block with no scratch register, and no flag is live after the test
(`guardJ_sim`).

## The structured machine

`runS P n sa` runs `P` from the address state `sa`. A `block` is run by `runBlockA`; an
`ite` runs its guard block and continues in the branch its condition selects; a
`loop pre g post` is Jasmin's `while`: it runs `pre`, then the guard block, and either
exits or runs `post` and repeats. The loop is the interpreter `loopRun` with fuel over the
one-step function `loopStep` on configurations `AState × Bool`, the Boolean stating that
the loop has exited; the fuel `n` bounds the number of iterations of every loop of `P`.
`runS_mono` states that a result is the result at every larger fuel.

## The simulation

`bignumExecFuel_runS_sim`: if `toSB body = some P`, `BJCorr s sa` and
`bignumExecFuel reg fuel body s = some s'`, then `runS P fuel sa = some sa'` with
`BJCorr s' sa'`, at the same fuel. The proof is by induction on the fuel and the body. The
`Cwhile` case (`loop_sim`) instantiates the cut-point rule `CutPoint.sim_run_le` of
`HaxAscent/Calculus/CorresMCutPoint.lean` (the form of `CutPoint.sim_fuel_le` for an
interpreter with fuel): the machine is `loopRun` over `loopStep`, the one cut point is the
loop head, the abstract state is the pair of the fuel and the state with which
`bignumExecFuel` reaches the loop head, the invariant is `BJCorr` together with the
remaining run of the `Cwhile`, the exit relation is `BJCorr` at the final state, and the
measure is the fuel at the loop head less one. Each segment is one step of `loopStep`
(`B = 1`), and the fuel at the loop head drops by `2` per iteration (`while_inv`), so the
bound `μ + 1` of the rule is the fuel of the run.

A direct proof of the `Cwhile` case is the same strong induction on the fuel at the loop
head that `CutPoint.sim_fuel_le` contains, followed by the conversion of iterated steps to
a run that `CutPoint.run_of_iter` contains; the instance states the invariant and the
measure and omits both inductions.

## Source lemmas

`bignumExecFuel_append_same` splits a run of `b1 ++ b2` into runs of `b1` and `b2` at the
same fuel. `BignumExec.bignumExecFuel_append_split` leaves the fuel of `b2` unbounded,
which gives no measure for a loop. `while_inv` is the inversion of one `Cwhile` iteration.
Both are statements about `bignumExecFuel` alone and belong with it in `BignumExec.lean`.
Fuel monotonicity is `BignumExec.bignumExecFuel_mono`.

## Scope

`toSI` is `none` on `Cfor` and `Ccall`; `BignumToJCalls` expands those in a body without
`Cif` and `Cwhile`. The link from `runS` to the instruction-set interpreter is open: a
compilation of `SProg` to labelled code with a conditional jump on the condition code of
each guard, and a simulation of `runS` by the run of that code.

## Main definitions

* `SGuard`, `SProg`: structured programs over `JInstr 64` blocks.
* `loopStep`, `loopRun`, `runS`: the structured run.
* `guardJ`, `toSI`, `toSB`: the translation.

## Main results

* `bignumExecFuel_append_same`: a run of `b1 ++ b2` splits at the same fuel.
* `while_inv`: one iteration of a `Cwhile`.
* `while_exit`: a `Cwhile` exits in a state where its guard evaluates to `0`.
* `guardJ_sim`: a translated guard preserves `BJCorr` and tests the guard value.
* `runS_mono`: fuel monotonicity of the structured run.
* `loop_sim`: the `Cwhile` case, by the cut-point rule.
* `bignumExecFuel_runS_sim`: the simulation of `bignumExecFuel` by `runS`.
* `AddN.runS_sim`, `AddN.runS_n_eq_zero`: a limb-wise addition loop over `n` limbs.
-/

namespace CatCrypt.Crypto.Jasmin.BignumToJLoops

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.BignumToJ
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## Runs of `bignumExecFuel` -/

/-- A run of the empty body returns its start state. -/
theorem bignumExecFuel_nil {reg : BignumRegistry} {fuel : Nat} {s s' : BignumState}
    (h : bignumExecFuel reg fuel [] s = some s') : s' = s := by
  cases fuel with
  | zero => simp [bignumExecFuel] at h
  | succ f =>
    simp only [bignumExecFuel, Option.some.injEq] at h
    exact h.symm

/-- A successful run has positive fuel. -/
theorem fuel_pos_of_run {reg : BignumRegistry} {fuel : Nat} {body : List InstrR}
    {s s' : BignumState} (h : bignumExecFuel reg fuel body s = some s') :
    ∃ f, fuel = f + 1 := by
  cases fuel with
  | zero => simp [bignumExecFuel] at h
  | succ f => exact ⟨f, rfl⟩

/-- **Sequencing at one fuel.** A run of `b1 ++ b2` is a run of `b1` followed by a run of
    `b2`, both at the fuel of the whole run. -/
theorem bignumExecFuel_append_same (reg : BignumRegistry) :
    ∀ (fuel : Nat) (b1 b2 : List InstrR) (s s' : BignumState),
      bignumExecFuel reg fuel (b1 ++ b2) s = some s' →
      ∃ m, bignumExecFuel reg fuel b1 s = some m ∧ bignumExecFuel reg fuel b2 m = some s' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; simp [bignumExecFuel] at h
  | succ f ihf =>
    intro b1
    induction b1 with
    | nil =>
      intro b2 s s' h
      exact ⟨s, by simp only [bignumExecFuel], h⟩
    | cons i is ih =>
      intro b2 s s' h
      cases i with
      | Cassgn lv tg ty e =>
        simp only [List.cons_append, bignumExecFuel] at h ⊢
        split at h
        · next s1 h1 =>
          exact ih b2 s1 s' h
        · cases h
      | Copn lvs tg op es =>
        simp only [List.cons_append, bignumExecFuel] at h ⊢
        split at h
        · next s1 h1 =>
          exact ih b2 s1 s' h
        · cases h
      | Cif c ct ce =>
        simp only [List.cons_append, bignumExecFuel] at h ⊢
        split at h
        · cases h
        · next v hv =>
          split at h
          · cases h
          · next sb hsb =>
            exact ih b2 sb s' h
      | Cfor v r body =>
        simp only [List.cons_append, bignumExecFuel] at h ⊢
        rw [← List.append_assoc] at h
        obtain ⟨m, h1, h2⟩ := ihf _ b2 s s' h
        exact ⟨m, h1, bignumExecFuel_mono reg f 1 b2 m s' h2⟩
      | Cwhile cb c ca =>
        simp only [List.cons_append, bignumExecFuel] at h ⊢
        rw [← List.append_assoc] at h
        obtain ⟨m, h1, h2⟩ := ihf _ b2 s s' h
        exact ⟨m, h1, bignumExecFuel_mono reg f 1 b2 m s' h2⟩
      | Ccall ii lvs fn args =>
        simp only [List.cons_append, bignumExecFuel] at h ⊢
        split at h
        · cases h
        · next fd hfd =>
          split at h
          · cases h
          · next vs hvs =>
            split at h
            · cases h
            · next cf hcf =>
              split at h
              · next hl =>
                simp only [hl, ite_true]
                exact ih b2 _ s' h
              · next hl =>
                split at h
                · cases h
                · next s2 hs2 =>
                  rw [ite_eq_right hl]
                  exact ih b2 s2 s' h

/-- **One iteration of a `Cwhile`.** A run of `Cwhile cb c ca` at fuel `f + 2` runs `cb` at
    fuel `f + 1` and evaluates the guard; on `0` it returns, and otherwise it runs `ca` and
    then the `Cwhile` again, both at fuel `f`. -/
theorem while_inv {reg : BignumRegistry} {fuel : Nat} {cb ca : List InstrR} {c : PExpr}
    {s s' : BignumState} (h : bignumExecFuel reg fuel [.Cwhile cb c ca] s = some s') :
    ∃ (f : Nat) (m : BignumState) (v : BitVec 64), fuel = f + 2 ∧
      bignumExecFuel reg (f + 1) cb s = some m ∧ evalPExpr m c = some v ∧
      (((v != 0) = false ∧ s' = m) ∨ ((v != 0) = true ∧ ∃ m2,
        bignumExecFuel reg f ca m = some m2 ∧
        bignumExecFuel reg f [.Cwhile cb c ca] m2 = some s')) := by
  obtain ⟨f1, rfl⟩ := fuel_pos_of_run h
  simp only [bignumExecFuel, List.append_nil] at h
  obtain ⟨m, hcb, hif⟩ := bignumExecFuel_append_same reg f1 cb _ s s' h
  obtain ⟨f, rfl⟩ := fuel_pos_of_run hif
  refine ⟨f, m, ?_⟩
  simp only [bignumExecFuel] at hif
  split at hif
  · cases hif
  · next v hv =>
    refine ⟨v, rfl, hcb, hv, ?_⟩
    split at hif
    · cases hif
    · next sb hsb =>
      simp only [Option.some.injEq] at hif
      subst hif
      by_cases hz : (v != 0) = true
      · rw [ite_eq_left hz] at hsb
        obtain ⟨m2, h1, h2⟩ := bignumExecFuel_append_same reg f ca _ m sb hsb
        exact Or.inr ⟨hz, m2, h1, h2⟩
      · rw [ite_eq_right hz] at hsb
        exact Or.inl ⟨by simpa using hz, bignumExecFuel_nil hsb⟩

/-- A `Cwhile` exits in a state where its guard evaluates to `0`. -/
theorem while_exit (reg : BignumRegistry) {cb ca : List InstrR} {c : PExpr} :
    ∀ (fuel : Nat) (s s' : BignumState),
      bignumExecFuel reg fuel [.Cwhile cb c ca] s = some s' →
      ∃ v, evalPExpr s' c = some v ∧ (v != 0) = false := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro s s' h
    obtain ⟨f, m, v, rfl, -, hv, hcase⟩ := while_inv h
    rcases hcase with ⟨hz, rfl⟩ | ⟨-, m2, -, hw⟩
    · exact ⟨v, hv, hz⟩
    · exact ih f (by omega) m2 s' hw

/-! ## Structured programs -/

/-- A translated guard: a block that sets the flags, and the condition code tested after
    it. -/
structure SGuard where
  /-- The block that sets the flags. -/
  pre : List (JInstr 64)
  /-- The condition code read after the block. -/
  cc : Condt

/-- The state after the guard block. -/
def SGuard.run (g : SGuard) (sa : AState) : AState := runBlockA sa g.pre

/-- The condition code after the guard block. -/
def SGuard.holds (g : SGuard) (sa : AState) : Bool := (g.run sa).view.condB g.cc

/-- A structured program over the address machine: straight-line blocks, sequencing,
    conditionals, and Jasmin's `while` (`loop pre g post` runs `pre`, tests `g`, and either
    exits or runs `post` and repeats). -/
inductive SProg where
  | block (b : List (JInstr 64))
  | seq (p q : SProg)
  | ite (g : SGuard) (t e : SProg)
  | loop (pre : SProg) (g : SGuard) (post : SProg)

/-- One iteration of a loop on a configuration `(sa, exited)`: run `pre` and the guard
    block, then exit or run `post`. An exited configuration has no step. -/
def loopStep (pre post : AState → Option AState) (g : SGuard) (c : AState × Bool) :
    Option (AState × Bool) :=
  if c.2 then none
  else (pre c.1).bind fun sa1 =>
    if g.holds sa1 then (post (g.run sa1)).map fun sa2 => (sa2, false)
    else some (g.run sa1, true)

/-- The interpreter with fuel over a one-step function on loop configurations: an exited
    configuration is returned, and a step consumes one unit of fuel. -/
def loopRun (step : AState × Bool → Option (AState × Bool)) :
    Nat → AState × Bool → Option (AState × Bool)
  | 0, c => if c.2 then some c else none
  | n + 1, c => if c.2 then some c else (step c).bind (loopRun step n)

/-- The structured run. The fuel bounds the number of iterations of each loop. -/
def runS : SProg → Nat → AState → Option AState
  | .block b, _, sa => some (runBlockA sa b)
  | .seq p q, n, sa => (runS p n sa).bind (runS q n)
  | .ite g t e, n, sa => if g.holds sa then runS t n (g.run sa) else runS e n (g.run sa)
  | .loop pre g post, n, sa =>
    (loopRun (loopStep (runS pre n) (runS post n) g) n (sa, false)).map Prod.fst

theorem loopRun_exited (step : AState × Bool → Option (AState × Bool)) (n : Nat)
    (c : AState × Bool) (hc : c.2 = true) : loopRun step n c = some c := by
  cases n <;> simp [loopRun, hc]

theorem loopRun_step (step : AState × Bool → Option (AState × Bool)) (n : Nat)
    (c c' : AState × Bool) (hs : step c = some c') (hc : c.2 = false) :
    loopRun step (n + 1) c = loopRun step n c' := by
  simp [loopRun, hc, hs]

theorem loopStep_exited (pre post : AState → Option AState) (g : SGuard) (c : AState × Bool)
    (hc : c.2 = true) : loopStep pre post g c = none := by
  simp [loopStep, hc]

/-- `loopStep` is monotone in the runs of `pre` and `post`. -/
theorem loopStep_mono {pre pre' post post' : AState → Option AState} {g : SGuard}
    (hp : ∀ a b, pre a = some b → pre' a = some b)
    (hq : ∀ a b, post a = some b → post' a = some b) (c r : AState × Bool)
    (h : loopStep pre post g c = some r) : loopStep pre' post' g c = some r := by
  unfold loopStep at h ⊢
  split at h
  · cases h
  · next hb =>
    rw [ite_eq_right hb]
    obtain ⟨a1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rw [hp _ _ h1, Option.bind_some]
    split at h2
    · next hg =>
      rw [ite_eq_left hg]
      obtain ⟨a2, h3, rfl⟩ := Option.map_eq_some_iff.1 h2
      rw [hq _ _ h3]
      rfl
    · next hg =>
      rw [ite_eq_right hg]
      exact h2

/-- `loopRun` is monotone in the step function and in the fuel. -/
theorem loopRun_mono {step step' : AState × Bool → Option (AState × Bool)}
    (hs : ∀ c r, step c = some r → step' c = some r) :
    ∀ (n n' : Nat) (c r : AState × Bool), n ≤ n' → loopRun step n c = some r →
      loopRun step' n' c = some r := by
  intro n
  induction n with
  | zero =>
    intro n' c r _ h
    by_cases hc : c.2 = true
    · rw [loopRun_exited _ _ _ hc] at h ⊢
      exact h
    · simp [loopRun, hc] at h
  | succ n ih =>
    intro n' c r hle h
    by_cases hc : c.2 = true
    · rw [loopRun_exited _ _ _ hc] at h ⊢
      exact h
    · obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
      simp only [loopRun, hc, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨c1, h1, h2⟩ := h
      exact ⟨c1, hs _ _ h1, ih k c1 r (by omega) h2⟩

/-- **Fuel monotonicity of the structured run.** -/
theorem runS_mono : ∀ (P : SProg) (n n' : Nat) (sa r : AState), n ≤ n' →
    runS P n sa = some r → runS P n' sa = some r := by
  intro P
  induction P with
  | block b => intro n n' sa r _ h; exact h
  | seq p q ihp ihq =>
    intro n n' sa r hle h
    simp only [runS, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨m, h1, h2⟩ := h
    exact ⟨m, ihp _ _ _ _ hle h1, ihq _ _ _ _ hle h2⟩
  | ite g t e iht ihe =>
    intro n n' sa r hle h
    simp only [runS] at h ⊢
    by_cases hg : g.holds sa = true
    · rw [ite_eq_left hg] at h ⊢
      exact iht _ _ _ _ hle h
    · rw [ite_eq_right hg] at h ⊢
      exact ihe _ _ _ _ hle h
  | loop pre g post ihpre ihpost =>
    intro n n' sa r hle h
    simp only [runS, Option.map_eq_some_iff] at h ⊢
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨c, loopRun_mono (loopStep_mono (fun a b => ihpre n n' a b hle)
      (fun a b => ihpost n n' a b hle)) n n' _ _ hle hc, rfl⟩

/-! ## The translation -/

/-- The translation of a guard: `test x, x` for a variable, and `cmp x, e` for `x != e` and
    `x == e` with `e` a constant or a variable. -/
def guardJ : PExpr → Option SGuard
  | .Pvar a => some ⟨[.test a.gv.var.vname (.reg a.gv.var.vname)], .ne⟩
  | .Papp2 (.Oneq _) (.Pvar a) b => (opndJ b).map fun ob => ⟨[.cmp a.gv.var.vname ob], .ne⟩
  | .Papp2 (.Oeq _) (.Pvar a) b => (opndJ b).map fun ob => ⟨[.cmp a.gv.var.vname ob], .e⟩
  | _ => none

mutual
/-- The translation of one instruction: a `Cassgn` or `Copn` as the block `toJ` gives, a
    `Cif` as an `ite`, a `Cwhile` as a `loop`; `none` on `Cfor` and `Ccall`. -/
def toSI : InstrR → Option SProg
  | .Cassgn lv tg ty e => (toJ (.Cassgn lv tg ty e)).map .block
  | .Copn lvs tg op es => (toJ (.Copn lvs tg op es)).map .block
  | .Cif c ct ce => do
      let g ← guardJ c
      let t ← toSB ct
      let e ← toSB ce
      some (.ite g t e)
  | .Cwhile cb c ca => do
      let pre ← toSB cb
      let g ← guardJ c
      let post ← toSB ca
      some (.loop pre g post)
  | _ => none

/-- The translation of a body: the sequence of the instruction translations. -/
def toSB : List InstrR → Option SProg
  | [] => some (.block [])
  | i :: is => do
      let p ← toSI i
      let q ← toSB is
      some (.seq p q)
end

/-! ## Guards -/

/-- The zero flag of a word is the test that the word is `0`. -/
theorem zf_eq (x : BitVec 64) : ZF_of_word x = decide (x = 0) := by
  simp only [ZF_of_word, BitVec.toNat_eq]
  rfl

/-- The zero flag of a difference is the equality of the operands. -/
theorem zf_sub (x y : BitVec 64) : ZF_of_word (x - y) = decide (x = y) := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [ZF_of_word, BitVec.toNat_sub, BitVec.toNat_eq]
  apply decide_eq_decide.2
  omega

/-- The state after `test a, a`: registers and memory unchanged, and the condition `ne`
    is `a ≠ 0`. -/
theorem test_view (sa : AState) (a : String) :
    (evalInstrA sa (.test a (.reg a))).regs = sa.regs ∧
      (evalInstrA sa (.test a (.reg a))).mem = sa.mem ∧
      (evalInstrA sa (.test a (.reg a))).view.condB .ne = (sa.regs a != 0) := by
  refine ⟨rfl, rfl, ?_⟩
  simp [evalInstrA, evalInstr, AState.view, JState.condB, JState.flagB, x86_eval_cond,
    x86_TEST, rflags_of_bwop, JState.writeB5, zf_eq, bne]
  rfl

/-- The state after `cmp a, o`: registers and memory unchanged, and the condition `e` is
    the equality of the operands. -/
theorem cmp_view (sa : AState) (a : String) (o : JOperand) :
    (evalInstrA sa (.cmp a o)).regs = sa.regs ∧ (evalInstrA sa (.cmp a o)).mem = sa.mem ∧
      (evalInstrA sa (.cmp a o)).view.condB .e = decide (sa.regs a = o.eval sa.view) ∧
      (evalInstrA sa (.cmp a o)).view.condB .ne = !decide (sa.regs a = o.eval sa.view) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [evalInstrA, evalInstr, AState.view, JState.condB, JState.flagB, x86_eval_cond,
      x86_CMP, x86_SUB, JState.writeB5, zf_sub]
    rfl
  · simp [evalInstrA, evalInstr, AState.view, JState.condB, JState.flagB, x86_eval_cond,
      x86_CMP, x86_SUB, JState.writeB5, zf_sub]
    rfl

/-- **Guards.** The guard block preserves `BJCorr`, and the condition code after it is the
    test `v != 0` of the guard value. -/
theorem guardJ_sim {c : PExpr} {g : SGuard} (h : guardJ c = some g) {s : BignumState}
    {sa : AState} (hc : BJCorr s sa) {v : BitVec 64} (hv : evalPExpr s c = some v) :
    BJCorr s (g.run sa) ∧ g.holds sa = (v != 0) := by
  have hcmp : ∀ (a : String) (ob : JOperand),
      BJCorr s (evalInstrA sa (.cmp a ob)) := fun a ob =>
    ⟨hc.1.trans (cmp_view sa a ob).1.symm, by rw [(cmp_view sa a ob).2.1]; exact hc.2⟩
  unfold guardJ at h
  split at h
  · next a =>
    cases h
    simp only [evalPExpr, Option.some.injEq] at hv
    subst hv
    obtain ⟨h1, h2, h3⟩ := test_view sa a.gv.var.vname
    refine ⟨⟨hc.1.trans h1.symm, ?_⟩, ?_⟩
    · show BJMem s.mem (evalInstrA sa _).mem
      rw [h2]
      exact hc.2
    · show (evalInstrA sa _).view.condB .ne = _
      rw [h3, hc.1]
  · next ws a e =>
    obtain ⟨ob, hob, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨vb, hvb, hev⟩ := opndJ_spec hob s
    simp only [evalPExpr, hvb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hv
    subst hv
    have hob' : ob.eval sa.view = vb := hev sa.view fun y => by rw [hc.1]; rfl
    refine ⟨hcmp _ ob, ?_⟩
    show (evalInstrA sa _).view.condB .ne = _
    rw [(cmp_view sa _ ob).2.2.2, hob', ← hc.1]
    by_cases hab : s.regs a.gv.var.vname = vb <;> simp [hab]
  · next ws a e =>
    obtain ⟨ob, hob, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨vb, hvb, hev⟩ := opndJ_spec hob s
    simp only [evalPExpr, hvb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hv
    subst hv
    have hob' : ob.eval sa.view = vb := hev sa.view fun y => by rw [hc.1]; rfl
    refine ⟨hcmp _ ob, ?_⟩
    show (evalInstrA sa _).view.condB .e = _
    rw [(cmp_view sa _ ob).2.2.1, hob', ← hc.1]
    by_cases hab : s.regs a.gv.var.vname = vb <;> simp [hab]
  · cases h

/-! ## The `Cwhile` case, by the cut-point rule -/

/-- **The `Cwhile` case.** If `runS pre fuel` and `runS post fuel` simulate the runs of `cb`
    and `ca` at every smaller fuel, then `runS (loop pre g post) fuel` simulates the run of
    `Cwhile cb c ca` at `fuel`. The proof is `CutPoint.sim_run_le` at the interpreter
    `loopRun` over `loopStep`, with the loop head as the cut point, the fuel and state of
    `bignumExecFuel` at the loop head as the abstract state, and the fuel less one as the
    measure. -/
theorem loop_sim (reg : BignumRegistry) (fuel : Nat) {cb ca : List InstrR} {c : PExpr}
    {pre post : SProg} {g : SGuard} (hg : guardJ c = some g)
    (hpre : ∀ f, f < fuel → ∀ (s s' : BignumState) (sa : AState), BJCorr s sa →
      bignumExecFuel reg f cb s = some s' → ∃ sa', runS pre fuel sa = some sa' ∧ BJCorr s' sa')
    (hpost : ∀ f, f < fuel → ∀ (s s' : BignumState) (sa : AState), BJCorr s sa →
      bignumExecFuel reg f ca s = some s' →
      ∃ sa', runS post fuel sa = some sa' ∧ BJCorr s' sa')
    {s s' : BignumState} {sa : AState} (hc : BJCorr s sa)
    (he : bignumExecFuel reg fuel [.Cwhile cb c ca] s = some s') :
    ∃ sa', runS (.loop pre g post) fuel sa = some sa' ∧ BJCorr s' sa' := by
  obtain ⟨F, rfl⟩ := fuel_pos_of_run he
  have hseg : ∀ (_ : Unit) (m : AState × Bool) (a : Nat × BignumState),
      (m.2 = false ∧ a.1 ≤ F + 1 ∧ BJCorr a.2 m.1 ∧
        bignumExecFuel reg a.1 [.Cwhile cb c ca] a.2 = some s') →
      ∃ (n : Nat) (m' : AState × Bool) (a' : Nat × BignumState), n ≤ 1 ∧
        CutPoint.iter (loopStep (runS pre (F + 1)) (runS post (F + 1)) g) n m = some m' ∧
        True ∧
        ((∃ _ : Unit, m'.2 = true ∧ BJCorr s' m'.1) ∨
          ∃ _ : Unit, (m'.2 = false ∧ a'.1 ≤ F + 1 ∧ BJCorr a'.2 m'.1 ∧
            bignumExecFuel reg a'.1 [.Cwhile cb c ca] a'.2 = some s') ∧ a'.1 - 1 < a.1 - 1) := by
    rintro - ⟨sa0, e0⟩ ⟨f0, s0⟩ ⟨hb, hf, hc0, he0⟩
    simp only at hb hf hc0 he0
    subst hb
    obtain ⟨f, m, v, rfl, hcb, hv, hcase⟩ := while_inv he0
    obtain ⟨sa1, hr1, hc1⟩ := hpre (f + 1) (by omega) _ _ _ hc0 hcb
    obtain ⟨hc2, hgv⟩ := guardJ_sim hg hc1 hv
    rcases hcase with ⟨hz, rfl⟩ | ⟨hnz, m2, hca, hw⟩
    · refine ⟨1, (g.run sa1, true), (f + 2, s0), Nat.le_refl 1, ?_, trivial,
        Or.inl ⟨(), rfl, hc2⟩⟩
      rw [hz] at hgv
      simp [CutPoint.iter, loopStep, hr1, hgv]
    · obtain ⟨sa3, hr3, hc3⟩ := hpost f (by omega) _ _ _ hc2 hca
      refine ⟨1, (sa3, false), (f, m2), Nat.le_refl 1, ?_, trivial,
        Or.inr ⟨(), ⟨rfl, by simp only; omega, hc3, hw⟩, by simp only; omega⟩⟩
      rw [hnz] at hgv
      simp [CutPoint.iter, loopStep, hr1, hgv, hr3]
  obtain ⟨m', -, -, hrun, -, hm, hcorr⟩ :=
    CutPoint.sim_run_le (L := Unit) (E := Unit) (A := Nat × BignumState)
      (loopRun (loopStep (runS pre (F + 1)) (runS post (F + 1)) g))
      (loopStep (runS pre (F + 1)) (runS post (F + 1)) g) (fun m => m.2 = true)
      (fun n m hm => loopRun_exited _ n m hm)
      (fun n m m' hs => loopRun_step _ n m m' hs (by
        cases hb : m.2 with
        | false => rfl
        | true => rw [loopStep_exited _ _ _ _ hb] at hs; cases hs))
      (fun _ _ => True) (fun _ _ _ _ _ => trivial)
      (fun _ m a => m.2 = false ∧ a.1 ≤ F + 1 ∧ BJCorr a.2 m.1 ∧
        bignumExecFuel reg a.1 [.Cwhile cb c ca] a.2 = some s')
      (fun _ m _ => m.2 = true ∧ BJCorr s' m.1) (fun _ _ a => a.1 - 1) 1 hseg
      (fun _ _ _ h => h.1) () (sa, false) (F + 1, s) ⟨rfl, Nat.le_refl _, hc, he⟩ (F + 1)
      (by simp)
  exact ⟨m'.1, by simp only [runS, hrun, Option.map_some], hcorr⟩

/-! ## The simulation -/

/-- **Simulation of `bignumExecFuel` by the structured run.** A body with conditionals and
    `while` loops that runs from `s` to `s'` at `fuel` is simulated from every related
    address state by the structured run of its translation, at the same fuel. -/
theorem bignumExecFuel_runS_sim (reg : BignumRegistry) :
    ∀ (fuel : Nat) (body : List InstrR) (P : SProg) (s s' : BignumState) (sa : AState),
      toSB body = some P → BJCorr s sa → bignumExecFuel reg fuel body s = some s' →
      ∃ sa', runS P fuel sa = some sa' ∧ BJCorr s' sa' := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F ihF =>
    intro body
    induction body with
    | nil =>
      intro P s s' sa hP hc he
      simp only [toSB, Option.some.injEq] at hP
      subst hP
      rw [bignumExecFuel_nil he]
      exact ⟨sa, rfl, hc⟩
    | cons i is ih =>
      intro P s s' sa hP hc he
      simp only [toSB, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hP
      obtain ⟨p, hp, q, hq, rfl⟩ := hP
      obtain ⟨m, h1, h2⟩ := bignumExecFuel_append_same reg F [i] is s s' he
      suffices hI : ∃ sa1, runS p F sa = some sa1 ∧ BJCorr m sa1 by
        obtain ⟨sa1, hr1, hc1⟩ := hI
        obtain ⟨sa2, hr2, hc2⟩ := ih q m s' sa1 hq hc1 h2
        exact ⟨sa2, by simp only [runS, hr1, Option.bind_some, hr2], hc2⟩
      obtain ⟨f, rfl⟩ := fuel_pos_of_run he
      cases i with
      | Cassgn lv tg ty e =>
        simp only [toSI, Option.map_eq_some_iff] at hp
        obtain ⟨js, hjs, rfl⟩ := hp
        simp only [bignumExecFuel] at h1
        split at h1
        · next s1 hs1 =>
          simp only [Option.some.injEq] at h1
          subst h1
          exact ⟨_, rfl, toJ_sim hjs hc hs1⟩
        · cases h1
      | Copn lvs tg op es =>
        simp only [toSI, Option.map_eq_some_iff] at hp
        obtain ⟨js, hjs, rfl⟩ := hp
        simp only [bignumExecFuel] at h1
        split at h1
        · next s1 hs1 =>
          simp only [Option.some.injEq] at h1
          subst h1
          exact ⟨_, rfl, toJ_sim hjs hc hs1⟩
        · cases h1
      | Cif c ct ce =>
        simp only [toSI, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hp
        obtain ⟨g, hg, t, ht, e, he', rfl⟩ := hp
        simp only [bignumExecFuel] at h1
        split at h1
        · cases h1
        · next v hv =>
          split at h1
          · cases h1
          · next sb hsb =>
            simp only [Option.some.injEq] at h1
            subst h1
            obtain ⟨hc1, hgv⟩ := guardJ_sim hg hc hv
            by_cases hz : (v != 0) = true
            · rw [ite_eq_left hz] at hsb
              obtain ⟨sa1, hr, hc2⟩ := ihF f (by omega) ct t s sb _ ht hc1 hsb
              refine ⟨sa1, ?_, hc2⟩
              simp only [runS, hgv, hz, ite_true]
              exact runS_mono t f (f + 1) _ _ (by omega) hr
            · rw [ite_eq_right hz] at hsb
              obtain ⟨sa1, hr, hc2⟩ := ihF f (by omega) ce e s sb _ he' hc1 hsb
              refine ⟨sa1, ?_, hc2⟩
              simp only [runS, hgv, hz]
              exact runS_mono e f (f + 1) _ _ (by omega) hr
      | Cwhile cb c ca =>
        simp only [toSI, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hp
        obtain ⟨pre, hpre, g, hg, post, hpost, rfl⟩ := hp
        refine loop_sim reg (f + 1) hg (fun f' hf' s s' sa hc he => ?_)
          (fun f' hf' s s' sa hc he => ?_) hc h1
        · obtain ⟨sa', hr, hc'⟩ := ihF f' hf' cb pre s s' sa hpre hc he
          exact ⟨sa', runS_mono pre f' (f + 1) _ _ (by omega) hr, hc'⟩
        · obtain ⟨sa', hr, hc'⟩ := ihF f' hf' ca post s s' sa hpost hc he
          exact ⟨sa', runS_mono post f' (f + 1) _ _ (by omega) hr, hc'⟩
      | Cfor v r b => simp [toSI] at hp
      | Ccall ii lvs fn args => simp [toSI] at hp

/-! ## A limb-wise addition loop over `n` limbs -/

namespace AddN

open CatCrypt.Crypto.Jasmin.JazzToInstrR.RoundTrip

/-- `x = y op z;` at type `u64`. -/
def bin (op : SOp2) (x y z : String) : InstrR :=
  .Cassgn (lv (u x)) .AT_none (.sword .U64) (.Papp2 op (pv (u y)) (pv (u z)))

/-- The loop guard `n != 0`. -/
def guard : PExpr := .Papp2 (.Oneq .U64) (pv (u "n")) (.Pconst 0)

/-- The limb-wise addition of the `n` limbs at `ap` and `bp` into `rp`, with the carry in
    `cf`: each iteration loads a limb of each operand, adds them with the carry, stores the
    sum, advances the three pointers by `8` and decrements `n`. -/
def body : List InstrR :=
  [ .Cassgn (lv (u "one")) .AT_none (.sword .U64) (.Pconst 1)
  , .Cassgn (lv (u "eight")) .AT_none (.sword .U64) (.Pconst 8)
  , .Cassgn (lv (b "cf")) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] guard
      [ load "a" "ap" 0
      , load "t" "bp" 0
      , carry "ADC_64" "a" [pv (u "a"), pv (u "t"), pv (b "cf")]
      , store "rp" 0 "a"
      , bin (.Oadd .U64) "ap" "ap" "eight"
      , bin (.Oadd .U64) "bp" "bp" "eight"
      , bin (.Oadd .U64) "rp" "rp" "eight"
      , bin (.Osub .U64) "n" "n" "one" ] ]

theorem toSB_isSome : (toSB body).isSome = true := by decide

/-- The structured translation of the loop. -/
def prog : SProg := (toSB body).getD (.block [])

theorem toSB_eq : toSB body = some prog := by
  have h := toSB_isSome
  revert h
  unfold prog
  cases toSB body <;> simp

/-- The addition loop is simulated by the structured run of its translation. -/
theorem runS_sim (reg : BignumRegistry) (fuel : Nat) {s s' : BignumState} {sa : AState}
    (hc : BJCorr s sa) (he : bignumExecFuel reg fuel body s = some s') :
    ∃ sa', runS prog fuel sa = some sa' ∧ BJCorr s' sa' :=
  bignumExecFuel_runS_sim reg fuel body prog s s' sa toSB_eq hc he

/-- A run of the addition loop ends with `n = 0`. -/
theorem n_eq_zero (reg : BignumRegistry) (fuel : Nat) {s s' : BignumState}
    (he : bignumExecFuel reg fuel body s = some s') : s'.regs "n" = 0 := by
  obtain ⟨m, -, h2⟩ := bignumExecFuel_append_same reg fuel (body.take 3) (body.drop 3) s s' he
  obtain ⟨v, hv, hz⟩ := while_exit reg fuel m s' h2
  simp only [guard, evalPExpr, pv, u, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq] at hv
  subst hv
  simpa using hz

/-- The structured run of the translated loop ends with the register `n` at `0`: the exit
    property of the source loop, transported along the simulation. -/
theorem runS_n_eq_zero (reg : BignumRegistry) (fuel : Nat) {s s' : BignumState} {sa : AState}
    (hc : BJCorr s sa) (he : bignumExecFuel reg fuel body s = some s') :
    ∃ sa', runS prog fuel sa = some sa' ∧ BJCorr s' sa' ∧ sa'.regs "n" = 0 := by
  obtain ⟨sa', hr, hc'⟩ := runS_sim reg fuel hc he
  exact ⟨sa', hr, hc', by rw [← hc'.1]; exact n_eq_zero reg fuel he⟩

end AddN

end CatCrypt.Crypto.Jasmin.BignumToJLoops
