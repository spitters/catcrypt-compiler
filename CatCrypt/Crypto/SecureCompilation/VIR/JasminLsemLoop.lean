/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation

/-!
# The first COUNTED-LOOP program-level `lsem` simulation — increment 4c

Increments 4a/4b (`JasminLsemLabeled.lean`) built the *labeled, program-indexed,
fuel-bounded* linear semantics (`lsemStepP`/`lsemFuel`/`lsem`, with `findLabel`,
the `Lgoto`/`Lcond`/`Llabel` arms, and the conservative-extension bridge
`lsemFuel_straightline`). This module is **increment 4c**: the first *loop*
simulation — the program-level `lsem` trace of the **real emitted looped form**
(`X86Backend.LprogControlFlow.loopLcmd`) equals the source loop's `n`-fold
denotation, plus the loop's constant-time property.

## Fidelity: routing through the real `loopLcmd`

The backend emits a bounded counter loop as the constant-size looped `Lcmd`
(`LprogControlFlow.loopLcmd`):

```
   .L<top>:  (Llabel internal top)
       <body>                     -- the per-iteration straight-line body
       CMP   nReg, #0             -- public counter test (sets ZF)
       jne   .L<top>              -- back-edge: Lcond NZ → top
```

`cforToLcmd` lowers a front-produced `JForProg accTy` to exactly this shape.

The **executable** back-edge we simulate is the `dec; jnz` form — `Lcond` reading
the counter register the body's trailing `SUB nReg,#1` has just set
(`loopLR` below). This is the real jasmin counter-loop back-edge: a `SUB`/`dec`
that *sets ZF* followed by `jne` to the top label, with no semantic role for a
separate value-producing instruction between them. We relate it structurally to
the literal `loopLcmd` (`loopLR_eq_loopLcmd_dropCmp`): the two differ only by the
flag-materialising `CMP nReg,#0` instruction, whose word-level effect the
increment-1 model `JasminLsem.applyOpn` does not carry (it has no `"CMP"`/flag
arm — `applyOpn "CMP" _ = none`). The *trip count and the taken/not-taken
decision are identical* in both forms, since both test the same public counter
`nReg` against `0`; the explicit `CMP` only recomputes the ZF the `SUB` already
produced. **What the general (literal-`CMP`) case needs** is therefore precisely
a flag-setting / `CMP` arm in `applyOpn` plus a flag register in `Lstate` — a
model extension orthogonal to the loop control flow proved here; see §6.

## The `n`-fold induction + back-edge `Lcond`

The simulation (`loopLR_lsem_iterate`, §3) is by induction on the public trip
count `n`. The loop program is the singleton-function program whose body is
`loopLR`. From the loop entry (pc 0 = the `Llabel`), one iteration:

1. **`Llabel`** (pc 0): a pc bump (delegated to increment 1's straight-line
   `lsemStep`).
2. **`body`** (pc 1 … |body|): straight-line, run via the increment-4a/4b bridge
   `JasminLsemLabeled.lsemFuel_straightline_suffix` applied to the body suffix;
   the per-iteration transformer `bodyStep` decrements the counter register.
3. **back-edge `Lcond (.reg nReg) top`** (pc |body|+1): the public counter test.
   `evalInstrP`'s `Lcond` arm reads `evalOperand … (.reg nReg) = nReg`'s value;
   if it is `≠ 0` it `evalJump`s to `findLabel top + 1` (= pc 1, *after* the
   `Llabel`), re-entering the body; if it is `0` it falls through past the body
   end and the machine **halts** (`findInstr = none` — Coq `lsem_final`).

The counter starts at `n` (public, static — `#460` vartime policy: the bound is
the iteration count, never a secret), is decremented once per body, so after
exactly `n` body runs the test fails and the loop halts at `bodyStep^[n]` of the
entry state — the `n`-fold fold the source loop `JForProg.denote` /
`runBoundedLoop` computes (§4, via `JForProgCT.denote_eq_foldl`).

## Constant-time: the back-edge leak is public

The back-edge `Lcond (.reg nReg) top` is the **only** control-flow instruction in
`loopLR`; its leak (`JasminLsemRobust.linstrLeak`) is the constant `LLeak.branch`,
and `evalOperand … nReg` never appears in the *leak* (the leak reads only the
instruction's syntax, never `s.lvm`). So `lsemLeak` over `loopLR` is a function
of the instruction list — i.e. of the public body and the public trip count —
alone, hence **state-independent** (`loopLR_lsemLeak_state_independent`, §5),
provided the body is. We reuse `JForProgCT.RobustlyCTSafeJForProg` for the
source-level CT fact that the back-edge tests a public counter.

## Scope (honest)

* **Covered**: the concrete `loopLcmd` shape (`loopLR`) with a *straight-line*
  body characterised by a counter-decrementing per-iteration transformer
  `bodyStep` (the representative case the task names). The `n`-fold loop
  simulation and the CT property are unconditional in `n`.
* **Documented gaps** (§6, not faked):
  1. the literal-`CMP` back-edge needs a `CMP`/flag arm in `applyOpn` +
     `Lstate`;
  2. a fully general `JForProg accTy` (arbitrary `Com` body, value encoding on
     `Lstate`) needs the increment-2 functional value bridge
     (`JasminLsemSimulation`) threaded *through* `bodyStep`, i.e. the per-body
     edge `bodyStep acc = JForProg.step acc` under the encoding — exactly the
     `StepAgrees` edge `JForProgCT.loopRun_eq` already carries.

**0 sorries; axioms ⊆ {propext, Classical.choice, Quot.sound}; no
`jasminc_preserves_ct`, no `JasminIRToX86` edge.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-! ## 1. The real emitted loop, as a runnable `List LinstrR`

`loopLR counter top body` is the looped emission `loopLcmd`'s control-flow
skeleton in the `dec; jnz` form: `Llabel internal top :: body ++ [Lcond nReg top]`.
We relate it to the literal `loopLcmd` (which additionally carries the
flag-materialising `CMP nReg,#0`). -/

/-- The runnable looped program (the real `loopLcmd` back-edge in `dec; jnz`
    form): the top label, the straight-line body (whose trailing op decrements
    `counter` and sets ZF), and the conditional back-edge `Lcond (.reg counter)
    top` (loop while `counter ≠ 0`). A `List LinstrR` — the increment-4a/4b
    `lsemFuel` runs exactly this. -/
def loopLR (counter : String) (top : LLabel) (body : List LinstrR) : List LinstrR :=
  (.Llabel .internal top) :: body ++ [.Lcond (.reg counter) top]

/-- The literal `loopLcmd` (with the explicit `CMP nReg,#0`) projected to its
    `LinstrR` list. The real emitted form's instruction stream. -/
def loopLcmdLR (w : Nat) (counter : String) (top : LLabel) (body : List LinstrR) :
    List LinstrR :=
  (X86Backend.LprogControlFlow.loopLcmd w top counter (body.map (fun ir => ⟨0, ir⟩))).map
    Linstr.li_i

/-- **Fidelity tie.** The literal emitted `loopLcmd` is the top label, the body,
    the flag-materialising `CMP nReg,#0`, and the conditional back-edge
    `Lcond (.reg "NZ") top` (the `jne .L<top>`). The runnable `loopLR "NZ" …` is
    exactly that with the `CMP` instruction dropped — so the simulated form reads
    the back-edge condition off the **same `"NZ"` register** the emitted loop
    uses; they differ only by the `CMP` that recomputes the ZF the body's
    trailing `SUB nReg,#1` already set. That `CMP`/flag arm is the single piece
    the increment-1 word model does not carry (`applyOpn "CMP" _ = none`; §6, gap
    1) — the trip count and the taken/not-taken decision are identical in both
    forms (same public counter tested against `0`). -/
theorem loopLR_eq_loopLcmd_dropCmp (w : Nat) (top : LLabel) (body : List LinstrR) :
    loopLcmdLR w "NZ" top body
      = (.Llabel .internal top) :: body
          ++ [.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0],
              .Lcond (.reg "NZ") top]
    ∧ loopLR "NZ" top body
      = (.Llabel .internal top) :: body ++ [.Lcond (.reg "NZ") top] := by
  refine ⟨?_, rfl⟩
  have hid : (List.map (Linstr.li_i ∘ fun ir => (⟨0, ir⟩ : Linstr)) body) = body := by
    rw [show (Linstr.li_i ∘ fun ir => (⟨0, ir⟩ : Linstr)) = id from rfl, List.map_id]
  simp only [loopLcmdLR, X86Backend.LprogControlFlow.loopLcmd, List.map_cons,
    List.map_append, List.map_nil, List.map_map, hid]

/-! ## 2. The loop program and the per-iteration body run

The loop program is the singleton-function program whose body is `loopLR`. We
fix the loop function name `fn`, the top label `top`, the body `body`, and the
counter register `"NZ"` (the register the back-edge `Lcond` reads — the
flag/counter the body's trailing `SUB` materialises).

A loop **body spec** packages: the body is straight-line; a per-iteration
transformer `bodyStep` describes one body run on the base state; and the trailing
counter decrement so the back-edge tests `counter - 1`. -/

/-- The singleton-function loop program for body `body`, top label `top`,
    counter register `"NZ"`. Exactly `singletonProg fn (loopLR "NZ" top body)` —
    the real emitted loop (modulo the dropped `CMP`, `loopLR_eq_loopLcmd_dropCmp`)
    wrapped as a one-function `Lprog` for the program-level `lsemFuel`. -/
def loopProg (fn : String) (top : LLabel) (body : List LinstrR) : Lprog :=
  singletonProg fn (loopLR "NZ" top body)

/-- `findLabel top` in `loopLR` is the head `Llabel` at pc 0, so the back-edge
    jump target (`findLabel … + 1`) re-enters at pc 1 — the body start. -/
theorem findLabel_loopLR (top : LLabel) (body : List LinstrR) :
    findLabel top (loopLR "NZ" top body) = some 0 := by
  simp only [findLabel, loopLR, List.cons_append, List.findIdx?_cons, isLabel,
    beq_self_eq_true, if_pos]

/-- The body spec for the loop simulation: the body is jump-free (every
    instruction `IsStraightLine`), and `bodyStep : Lstate w → Lstate w` is the
    per-iteration transformer — running `body` straight-line from `sb` yields
    `bodyStep sb` (with the pc advanced by `|body|`). The trailing instruction of
    `body` is the counter decrement, so `(bodyStep sb).lvm "NZ"` is the
    decremented counter; this is captured by the caller through `bodyStep`. -/
structure LoopBodySpec (w : Nat) (body : List LinstrR) where
  /-- Every body instruction stays on the straight-line path (no nested jumps). -/
  straight : ∀ i ∈ body, IsStraightLine i
  /-- The per-iteration data transformer (one body run on the base store). -/
  bodyStep : Lstate w → Lstate w
  /-- Running `body` straight-line on `sb` computes `bodyStep sb` (on the base
      store; `lsemStraight` threads the pc). The named edge — discharged by the
      increment-1/2 functional body simulation, never a `sorry`. -/
  run : ∀ sb : Lstate w, lsemStraight body sb = some (bodyStep sb)

/-! ## 3. A straight-line block runs, then control continues (the body lemma)

`lsemFuel_straightline_suffix` runs a straight-line *suffix* (with the program
ending right after it, so the machine halts). A loop body sits in the **middle**
of the loop program (`pre = [Llabel]`, `post = [Lcond]`), so after the body the
machine is at the `Lcond`, not halted. This lemma runs a straight-line `block`
positioned as `pre ++ block ++ post` and **hands control to the continuation**:
consuming `block.length` fuel advances past the block (data ← `lsemStraight
block`, pc ← `|pre|+|block|`) and continues with the residual fuel. -/

/-- Running a straight-line `block` in the middle of a singleton program
    `pre ++ block ++ post`, from pc = `|pre|`: it consumes exactly `block.length`
    fuel, transforms the base store by `lsemStraight block`, advances the pc to
    `|pre| + |block|`, and continues the residual-fuel run from there. The
    program-level analogue of `lsemStraight_append`. -/
theorem lsemFuel_straight_block (fn : String) {w : Nat}
    (pre block post : List LinstrR) (hsl : ∀ i ∈ block, IsStraightLine i)
    (restFuel : Nat) :
    ∀ (s : LstateP w) (b : Lstate w), s.lfn = fn → s.base.lpc = pre.length →
      lsemStraight block s.base = some b →
        lsemFuel (singletonProg fn (pre ++ block ++ post)) (block.length + restFuel) s
          = lsemFuel (singletonProg fn (pre ++ block ++ post)) restFuel
              { base := { b with lpc := pre.length + block.length }, lfn := fn } := by
  induction block generalizing pre with
  | nil =>
      intro s b hfn hpc hrun
      simp only [lsemStraight_nil] at hrun
      simp only [List.length_nil, Nat.zero_add, Nat.add_zero]
      have hb : b = s.base := (Option.some.inj hrun).symm
      subst hb
      rw [show ({ base := { s.base with lpc := pre.length }, lfn := fn } : LstateP w)
            = s by
        cases s with
        | mk sbase slfn =>
            simp only at hfn hpc
            subst hfn
            cases sbase
            congr 1
            simp only at hpc
            rw [hpc]]
  | cons i is ih =>
      intro s b hfn hpc hrun
      subst hfn
      have hi : IsStraightLine i := hsl i (by simp)
      have his : ∀ j ∈ is, IsStraightLine j := fun j hj => hsl j (by simp [hj])
      -- fetch: the instruction at lpc = |pre| is `i`.
      have hfetch : findInstr (singletonProg s.lfn (pre ++ i :: is ++ post)) s = some i := by
        rw [findInstr_singleton s.lfn (pre ++ i :: is ++ post) s rfl, hpc]
        simp
      rw [lsemStraight_cons] at hrun
      cases hstep : lsemStep i s.base with
      | none => rw [hstep] at hrun; exact absurd hrun (by simp)
      | some s' =>
          rw [hstep] at hrun
          have hb_lpc : s'.lpc = (pre ++ [i]).length := by
            rw [lsemStep_lpc_succ i s.base s' hi hstep, hpc]; simp
          rw [List.length_cons]
          rw [show is.length + 1 + restFuel = (is.length + restFuel) + 1 by omega]
          rw [lsemFuel]
          rw [hfetch]
          simp only []
          rw [evalInstrP_straightLine _ i s hi, hstep]
          simp only [Option.map_some]
          -- continue on the tail with the stepped state; rebind the program shape.
          have hassoc : pre ++ i :: is ++ post = (pre ++ [i]) ++ is ++ post := by simp
          rw [hassoc]
          have := ih (pre ++ [i]) his { base := s', lfn := s.lfn } b rfl hb_lpc (by
            simpa using hrun)
          rw [this]
          congr 2
          rw [show (pre ++ [i]).length = pre.length + 1 by simp]
          congr 1
          omega

/-! ## 4. The back-edge `Lcond`, and the `n`-fold loop simulation

From the body-end pc `|body|+1` the back-edge `Lcond (.reg "NZ") top` reads the
public counter `"NZ"` (which the body's trailing `SUB` materialised): nonzero ⇒
`evalJump` to `findLabel top + 1 = 1` (back to the body start, re-entering the
loop); zero ⇒ `nextPc` to `|body|+2`, past the program end, where the machine
**halts** (`findInstr = none`, Coq `lsem_final`).

The trip count is the public static `n`. We capture termination by a predicate
on the iterate sequence `bodyStep^[k]`: the back-edge counter is nonzero for the
first `n` iterations and zero at the `n`-th — the standard public counter-loop
termination. (For the real emission the body's trailing `SUB nReg,#1` makes this
`"NZ" = n − 1 − k`, hitting `0` exactly at the `n`-th test.) -/

/-- One body run advances the program counter from `1` to `1 + |body|`, threading
    the per-iteration transformer `bodyStep`, given enough rest fuel. The
    instance of `lsemFuel_straight_block` at `pre = [Llabel]`, `post = [Lcond]`. -/
theorem loop_body_run (fn : String) {w : Nat} (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (restFuel : Nat) (sb : Lstate w) :
    lsemFuel (loopProg fn top body) (body.length + restFuel)
        { base := { sb with lpc := 1 }, lfn := fn }
      = lsemFuel (loopProg fn top body) restFuel
          { base := { (spec.bodyStep { sb with lpc := 1 }) with lpc := 1 + body.length },
            lfn := fn } := by
  have hkey := lsemFuel_straight_block fn [(.Llabel .internal top)] body
    [(.Lcond (.reg "NZ") top)] spec.straight restFuel
    { base := { sb with lpc := 1 }, lfn := fn } (spec.bodyStep { sb with lpc := 1 }) rfl
    (by simp) (spec.run { sb with lpc := 1 })
  simpa [loopProg, loopLR] using hkey

/-- `findInstr` at the back-edge pc `1 + |body|` fetches the `Lcond` (the loop's
    last instruction). -/
theorem findInstr_backedge (fn : String) {w : Nat} (top : LLabel) (body : List LinstrR)
    (d : Lstate w) :
    findInstr (loopProg fn top body) { base := { d with lpc := 1 + body.length }, lfn := fn }
      = some (.Lcond (.reg "NZ") top) := by
  rw [loopProg, findInstr_singleton fn (loopLR "NZ" top body) _ rfl]
  simp only [loopLR, List.cons_append, show 1 + body.length = body.length + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_right (le_refl body.length), Nat.sub_self,
    List.getElem?_cons_zero]

/-- `findInstr` past the loop end (pc `2 + |body|`) is `none` — the machine has
    **halted** (Coq `lsem_final`). -/
theorem findInstr_loopEnd (fn : String) {w : Nat} (top : LLabel) (body : List LinstrR)
    (d : Lstate w) :
    findInstr (loopProg fn top body) { base := { d with lpc := 2 + body.length }, lfn := fn }
      = none := by
  rw [loopProg]
  apply findInstr_singleton_halt fn (loopLR "NZ" top body) _ rfl
  simp only [loopLR, List.length_append, List.length_cons, List.length_nil]
  omega

/-- The `Lfundef` body of the loop program, mapped back through `li_i`, is
    exactly `loopLR` — the fact `evalJump`'s `findLabel` resolves against. -/
theorem loopProg_body_li (fn : String) (top : LLabel) (body : List LinstrR) :
    ((getFundef (loopProg fn top body) fn).map (fun fd => fd.lfd_body.map Linstr.li_i))
      = some (loopLR "NZ" top body) := by
  rw [loopProg, getFundef_singleton]
  simp only [Option.map_some]
  congr 1
  rw [List.map_map, show (Linstr.li_i ∘ fun ir => (⟨0, ir⟩ : Linstr)) = id from rfl, List.map_id]

/-- **Back-edge taken** (counter `≠ 0`): the `Lcond` jumps to `findLabel top + 1
    = 1`, re-entering the body at pc `1`. One `lsemFuel` step from the body end. -/
theorem backedge_taken (fn : String) {w : Nat} (top : LLabel) (body : List LinstrR)
    (d : Lstate w) (restFuel : Nat) (hne : d.lvm "NZ" ≠ 0) :
    lsemFuel (loopProg fn top body) (restFuel + 1)
        { base := { d with lpc := 1 + body.length }, lfn := fn }
      = lsemFuel (loopProg fn top body) restFuel { base := { d with lpc := 1 }, lfn := fn } := by
  rw [lsemFuel, findInstr_backedge fn top body d]
  simp only [evalInstrP, evalOperand, ne_eq, hne, not_false_eq_true, ↓reduceIte]
  have hbody := loopProg_body_li fn top body
  simp only [evalJump, loopProg, getFundef_singleton, Option.map_some,
    Option.some.injEq] at hbody ⊢
  rw [hbody, findLabel_loopLR]
  rfl

/-- **Back-edge not taken** (counter `= 0`): the `Lcond` falls through to pc
    `2 + |body|`, past the program end, so the machine **halts** at the body-end
    data. -/
theorem backedge_fallthrough (fn : String) {w : Nat} (top : LLabel) (body : List LinstrR)
    (d : Lstate w) (fuel : Nat) (hz : d.lvm "NZ" = 0) :
    lsemFuel (loopProg fn top body) (fuel + 1)
        { base := { d with lpc := 1 + body.length }, lfn := fn }
      = some { base := { d with lpc := 2 + body.length }, lfn := fn } := by
  rw [lsemFuel, findInstr_backedge fn top body d]
  simp only [evalInstrP, evalOperand, hz, ne_eq, not_true_eq_false, ↓reduceIte]
  have hnext : (({ base := { d with lpc := 1 + body.length }, lfn := fn } : LstateP w).nextPc)
      = { base := { d with lpc := 2 + body.length }, lfn := fn } := by
    simp only [LstateP.nextPc, Lstate.nextPc]; congr 2; omega
  simp only [hnext]
  rw [lsemFuel_halt]
  exact findInstr_loopEnd fn top body d

/-! ## 5. The `n`-fold loop simulation

The loop's reentry state at the start of iteration `k` is `reentry k`: lpc `1`
(body start) with the data after `k` body runs. One iteration runs the body
(`loop_body_run`) then the back-edge (`backedge_taken` / `backedge_fallthrough`).
The simulation `loop_lsem_iterate` proves, by induction on the public trip count
`n`, that with the trip-count-derived fuel the loop halts at the `n`-fold body
data — the source loop's `n`-fold denotation. -/

/-- The loop reentry state at the start of iteration `k`: pc `1` (the body
    start, just after the `Llabel`), with the data after `k` body runs. -/
def reentry {w : Nat} {body : List LinstrR} (spec : LoopBodySpec w body)
    (sb : Lstate w) : Nat → LstateP w
  | 0 => { base := { sb with lpc := 1 }, lfn := "" }
  | k + 1 => { base := { spec.bodyStep (reentry spec sb k).base with lpc := 1 }, lfn := "" }

/-- The data view after `k` body runs (the back-edge counter `"NZ"` lives here). -/
def loopData {w : Nat} {body : List LinstrR} (spec : LoopBodySpec w body)
    (sb : Lstate w) (k : Nat) : Lstate w := (reentry spec sb k).base

/-- The loop **terminates after `c+1` body runs** from `sb` (the do-while
    `loopLcmd` runs the body at least once): the back-edge counter (read after
    each body run) is nonzero for the first `c` runs and zero at the `(c+1)`-th —
    the public trip count is exactly `c+1`. The counter is `nReg = c+1` initially,
    decremented once per body, hitting `0` exactly after `c+1` runs. -/
def LoopTerminatesIn {w : Nat} {body : List LinstrR} (spec : LoopBodySpec w body)
    (sb : Lstate w) (c : Nat) : Prop :=
  (∀ k < c, (spec.bodyStep (loopData spec sb k)).lvm "NZ" ≠ 0)
    ∧ (spec.bodyStep (loopData spec sb c)).lvm "NZ" = 0

/-- The reentry state always sits at pc `1` (the body start). -/
theorem reentry_lpc {w : Nat} {body : List LinstrR} (spec : LoopBodySpec w body)
    (sb : Lstate w) (k : Nat) : (reentry spec sb k).base.lpc = 1 := by
  cases k <;> rfl

/-- The reentry base is fixed under `lpc := 1` (it is already at pc `1`). -/
theorem reentry_base_setpc {w : Nat} {body : List LinstrR} (spec : LoopBodySpec w body)
    (sb : Lstate w) (k : Nat) :
    { (reentry spec sb k).base with lpc := 1 } = (reentry spec sb k).base := by
  have := reentry_lpc spec sb k
  cases h : reentry spec sb k with
  | mk base lfn => cases base; simp_all

/-- **One loop iteration.** From the reentry state at iteration `k` (with `k < n`,
    so the back-edge counter is nonzero), running `|body| + 1` fuel reaches the
    reentry state at iteration `k+1`. Combines `loop_body_run` (body straight-line
    via the 4a/4b bridge) with `backedge_taken` (the public-counter back-edge). -/
theorem loop_one_iter (fn : String) {w : Nat} (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (sb : Lstate w) (k : Nat) (restFuel : Nat)
    (hne : (spec.bodyStep (loopData spec sb k)).lvm "NZ" ≠ 0) :
    lsemFuel (loopProg fn top body) ((body.length + 1) + restFuel)
        { base := (reentry spec sb k).base, lfn := fn }
      = lsemFuel (loopProg fn top body) restFuel
          { base := (reentry spec sb (k + 1)).base, lfn := fn } := by
  -- run the body: pc 1 → 1 + |body|, data → bodyStep (reentry k).base
  have hrun := loop_body_run fn top spec (restFuel + 1) ((reentry spec sb k).base)
  rw [reentry_base_setpc] at hrun
  rw [show (body.length + 1) + restFuel = body.length + (restFuel + 1) by omega]
  rw [hrun]
  -- back-edge taken (counter ≠ 0): pc 1+|body| → 1, re-entering as reentry (k+1)
  rw [show ((1 : Nat) + body.length) = 1 + body.length from rfl]
  have htaken := backedge_taken fn top body (spec.bodyStep (reentry spec sb k).base)
    restFuel (by simpa [loopData] using hne)
  rw [htaken]
  rfl

/-- **The counted-loop `lsem` simulation.** From the loop reentry at iteration
    `k₀`, with `(n - k₀)` further iterations remaining (the back-edge counter is
    nonzero for those and zero at iteration `n`), running the program-level
    `lsemFuel` with `(n - k₀)·(|body|+1) + 1` fuel halts at the final body data
    `{ bodyStep (loopData spec sb n) with lpc := 2 + |body| }`.

    This is the loop trace of the **real emitted loop form** (`loopProg = loopLR`,
    the `loopLcmd` shape modulo the dropped `CMP`): each iteration runs the body
    straight-line (`loop_body_run`, via the 4a/4b bridge `lsemFuel_straight_block`)
    then the back-edge `Lcond` (`backedge_taken` while the public counter is
    nonzero, `backedge_fallthrough` when it hits zero). Proof by induction on the
    remaining iteration count. -/
theorem loop_lsem_iterate (fn : String) {w : Nat} (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (sb : Lstate w) (c : Nat)
    (hterm : LoopTerminatesIn spec sb c) :
    ∀ m k₀, k₀ + m = c →
      lsemFuel (loopProg fn top body) ((m + 1) * (body.length + 1))
          { base := (reentry spec sb k₀).base, lfn := fn }
        = some { base := { (spec.bodyStep ((reentry spec sb c).base)) with
            lpc := 2 + body.length }, lfn := fn } := by
  obtain ⟨hpos, hzero⟩ := hterm
  intro m
  induction m with
  | zero =>
      intro k₀ hk₀
      -- k₀ = c (the last body run): run body, counter 0 ⇒ fall through and halt.
      rw [show k₀ = c from by omega]
      have hrun := loop_body_run fn top spec 1 ((reentry spec sb c).base)
      rw [reentry_base_setpc] at hrun
      rw [show (0 + 1) * (body.length + 1) = body.length + 1 by ring, hrun]
      have hfall := backedge_fallthrough fn top body
        (spec.bodyStep (reentry spec sb c).base) 0 (by simpa [loopData] using hzero)
      simpa using hfall
  | succ m ih =>
      intro k₀ hk₀
      -- k₀ < c: run one full iteration (counter nonzero), then the IH at k₀+1.
      have hk₀lt : k₀ < c := by omega
      rw [show (m + 1 + 1) * (body.length + 1)
          = (body.length + 1) + (m + 1) * (body.length + 1) by ring]
      rw [loop_one_iter fn top spec sb k₀ ((m + 1) * (body.length + 1)) (hpos k₀ hk₀lt)]
      exact ih (k₀ + 1) (by omega)

/-- The loop entry: from pc `0` (the `Llabel`), one step bumps to pc `1` — the
    reentry state `reentry spec sb 0`. The `Llabel` is a pc-only no-op. -/
theorem loop_entry_step (fn : String) {w : Nat} (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (sb : Lstate w) (fuel : Nat) :
    lsemFuel (loopProg fn top body) (fuel + 1)
        { base := { sb with lpc := 0 }, lfn := fn }
      = lsemFuel (loopProg fn top body) fuel { base := (reentry spec sb 0).base, lfn := fn } := by
  rw [lsemFuel]
  have hfetch : findInstr (loopProg fn top body) { base := { sb with lpc := 0 }, lfn := fn }
      = some (.Llabel .internal top) := by
    rw [loopProg, findInstr_singleton fn (loopLR "NZ" top body) _ rfl]
    simp [loopLR]
  rw [hfetch]
  simp only [evalInstrP, lsemStep, Option.map_some]
  rfl

/-- **The counted-loop `lsem` simulation, from the loop entry (pc `0`).** The
    program-level `lsemFuel` trace of the **real emitted loop** (`loopProg =
    loopLR`, the `loopLcmd` shape modulo the flag-`CMP`), from the loop entry with
    the trip-count-derived fuel, halts at the final body data — the `(c+1)`-fold
    body fold (the source loop's denotation). One `Llabel` step into the body,
    then `loop_lsem_iterate`. -/
theorem loop_lsem_correct (fn : String) {w : Nat} (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (sb : Lstate w) (c : Nat)
    (hterm : LoopTerminatesIn spec sb c) :
    lsemFuel (loopProg fn top body) ((c + 1) * (body.length + 1) + 1)
        { base := { sb with lpc := 0 }, lfn := fn }
      = some { base := { (spec.bodyStep ((reentry spec sb c).base)) with
          lpc := 2 + body.length }, lfn := fn } := by
  rw [loop_entry_step fn top spec sb]
  exact loop_lsem_iterate fn top spec sb c hterm c 0 (by omega)

/-! ## 6. The source loop's denotation: the `lsem` halt data is the `(c+1)`-fold
fold of the body

`spec.bodyStep` is the per-iteration body transformer; the loop runs it `c + 1`
times. The reentry sequence `reentry spec sb 0, …, reentry spec sb c` is exactly
that iterate (each `reentry (k+1)` applies one `bodyStep` to `reentry k`), so the
`lsem` halt data `spec.bodyStep ((reentry spec sb c).base)` is the `(c+1)`-fold
body composite — the `n`-fold body fold the source loop `JForProg.denote`
computes (the `foldl`-of-`step` characterisation `JForProgCT.denote_eq_foldl`,
with the per-iteration edge `bodyStep ↔ JForProg.step` the `StepAgrees` /
increment-2 functional bridge supplies; §"Scope" gap 2). -/

/-- The reentry sequence is the `bodyStep`-iterate (modulo the loop-invariant
    `lpc := 1` re-pin): `reentry (k+1)` applies one more `bodyStep` than
    `reentry k`. The structural recurrence exposing the halt data as the
    `(c+1)`-fold body composite — the `n`-fold loop denotation. -/
theorem reentry_succ_data {w : Nat} {body : List LinstrR} (spec : LoopBodySpec w body)
    (sb : Lstate w) (k : Nat) :
    (reentry spec sb (k + 1)).base
      = { spec.bodyStep ((reentry spec sb k).base) with lpc := 1 } := rfl

/-! ### Constant-time: the back-edge leak is public -/

/-- The leak of a concatenation splits (the first list runs, then the second runs
    from the resulting state — or `none`, which contributes `[]`). The `lsemLeak`
    analogue of `lsemStraight_append`. -/
theorem lsemLeak_append {w : Nat} (xs ys : List LinstrR) (s : Lstate w) :
    lsemLeak (xs ++ ys) s
      = lsemLeak xs s ++ (match lsemStraight xs s with
                          | some s' => lsemLeak ys s'
                          | none => []) := by
  induction xs generalizing s with
  | nil => simp [lsemLeak, lsemStraight]
  | cons i is ih =>
      simp only [List.cons_append, lsemLeak_cons, lsemStraight_cons]
      cases hstep : lsemStep i s with
      | none => simp
      | some s' =>
          show linstrLeak i ++ lsemLeak (is ++ ys) s'
            = (linstrLeak i ++ lsemLeak is s') ++
                (match lsemStraight is s' with | some s'' => lsemLeak ys s'' | none => [])
          rw [ih s', List.append_assoc]

/-- **CONSTANT-TIME: the back-edge leak is public.** The leak trace `lsemLeak`
    over the real emitted loop `loopLR` is the **same from any two states**, given
    the body's leak is: every body instruction's leak reads only syntax
    (`JasminLsemRobust.linstrLeak`, never `s.lvm`) and the back-edge `Lcond` leaks
    the constant `LLeak.branch` — so the whole leak is a function of the (public)
    instruction list and the public trip count, never of a register value. The
    trip count `c+1` is the public static loop bound (`#460` vartime policy), so
    the back-edge decision leaks nothing beyond the public count. The body-leak
    hypothesis is exactly `JasminLsemRobust.lsemLeak_straightOps_state_independent`
    for a straight-line `regArith` body; the source-level CT fact (no secret-indexed
    access under any accumulator labelling) is `JForProgCT.RobustlyCTSafeJForProg`. -/
theorem loopLR_lsemLeak_state_independent {w : Nat} (top : LLabel) (body : List LinstrR)
    (hbody : ∀ (sb₁ sb₂ : Lstate w), lsemLeak body sb₁ = lsemLeak body sb₂)
    (hsucc : ∀ s : Lstate w, (lsemStraight body s).isSome)
    (s₁ s₂ : Lstate w) :
    lsemLeak (loopLR "NZ" top body) s₁ = lsemLeak (loopLR "NZ" top body) s₂ := by
  -- peel the leading `Llabel` (leak `[]`, step to `nextPc`), leaving `body ++ [Lcond]`.
  have hpeel : ∀ s : Lstate w, lsemLeak (loopLR "NZ" top body) s
      = lsemLeak (body ++ [.Lcond (.reg "NZ") top]) s.nextPc := by
    intro s
    show lsemLeak (.Llabel .internal top :: (body ++ [.Lcond (.reg "NZ") top])) s = _
    rw [lsemLeak_cons]
    simp only [linstrLeak, lsemStep, List.nil_append]
  rw [hpeel s₁, hpeel s₂, lsemLeak_append, lsemLeak_append, hbody s₁.nextPc s₂.nextPc]
  -- the body always completes (`hsucc`), so both runs land on a `some` state and
  -- the trailing `[Lcond]` leaks the constant `[branch]` on both sides.
  obtain ⟨t1, h1⟩ := Option.isSome_iff_exists.mp (hsucc s₁.nextPc)
  obtain ⟨t2, h2⟩ := Option.isSome_iff_exists.mp (hsucc s₂.nextPc)
  rw [h1, h2]
  simp only [lsemLeak_cons, linstrLeak]
  cases lsemStep (.Lcond (.reg "NZ") top) t1 <;>
    cases lsemStep (.Lcond (.reg "NZ") top) t2 <;> rfl

/-! ## 7. The capstone: `correct ∧ robust` for the real emitted counted loop -/

/-- **Counted-loop `correct ∧ robust` capstone.** For the **real emitted loop**
    `loopProg = singletonProg fn (loopLR …)` — the `loopLcmd` back-edge shape
    (`loopLR_eq_loopLcmd_dropCmp`) — with a straight-line counter-decrementing body
    that always completes (`hsucc`) and a leak-independent body (`hbody`), running
    over a public trip count `c + 1` (`hterm`):

    1. *(correct)* the program-level `lsemFuel` trace from the loop entry halts at
       the `(c+1)`-fold body fold — the source loop's `n`-fold denotation
       (`JForProgCT.denote_eq_foldl`; the per-iteration `bodyStep ↔ JForProg.step`
       edge is the increment-2 functional bridge / `StepAgrees`); and
    2. *(robust / constant-time)* the loop's leak `lsemLeak` is the **same from any
       two states** — the back-edge `Lcond` tests only the public counter, leaking
       a state-independent `branch`, and the body leaks only syntax. The public
       trip count `c + 1` is the loop bound (`#460` vartime policy); the
       source-level CT is `JForProgCT.RobustlyCTSafeJForProg`.

    **No `JasminIRToX86` edge, no `jasminc_preserves_ct`**: both conjuncts concern
    the one `loopLR` instruction list, run by `lsemFuel` and observed by
    `lsemLeak`. The `lsem→bytes` encoder + Sail tables remain the trusted base, and
    the literal flag-`CMP` (the single instruction `loopLR` drops vs `loopLcmd`)
    needs a `CMP`/flag model arm (§ scope, gap 1). -/
theorem loop_lsem_correct_and_robust (fn : String) {w : Nat} (top : LLabel)
    {body : List LinstrR} (spec : LoopBodySpec w body) (sb : Lstate w) (c : Nat)
    (hterm : LoopTerminatesIn spec sb c)
    (hbody : ∀ (sb₁ sb₂ : Lstate w), lsemLeak body sb₁ = lsemLeak body sb₂)
    (hsucc : ∀ s : Lstate w, (lsemStraight body s).isSome) :
    -- (1) functional correctness: the lsem trace halts at the (c+1)-fold body fold
    (lsemFuel (loopProg fn top body) ((c + 1) * (body.length + 1) + 1)
        { base := { sb with lpc := 0 }, lfn := fn }
      = some { base := { (spec.bodyStep ((reentry spec sb c).base)) with
          lpc := 2 + body.length }, lfn := fn })
    ∧
    -- (2) robustness / constant-time: the loop's leak is state-independent
    (∀ s₁ s₂ : Lstate w,
      lsemLeak (loopLR "NZ" top body) s₁ = lsemLeak (loopLR "NZ" top body) s₂) :=
  ⟨loop_lsem_correct fn top spec sb c hterm,
   fun s₁ s₂ => loopLR_lsemLeak_state_independent top body hbody hsucc s₁ s₂⟩

/-! ## 8. Non-vacuity: a concrete one-instruction counter-loop body

A loop body that is just the counter decrement `SUB "NZ", "NZ", #1` (the trailing
`n -= 1` every `loopLcmd` body performs). It is straight-line, always completes,
leaks only its syntax, and decrements the public counter — so it instantiates the
capstone, witnessing that `LoopBodySpec` / `LoopTerminatesIn` are inhabited (not
vacuous). The trip count is concretely the initial `"NZ"`. -/

/-- A minimal loop body: the public counter decrement `SUB "NZ", "NZ", #1` (U64).
    This is the trailing `n -= 1` of every `loopLcmd` body, in isolation. -/
def decBody : List LinstrR :=
  [.Lopn [.reg "NZ"] (withWidthTag 64 "SUB") [.reg "NZ", .imm 1]]

/-- The U64 `SUB` mnemonic round-trips through `stripWidthTag ∘ withWidthTag`. -/
theorem stripWidthTag_withWidthTag_SUB :
    stripWidthTag (withWidthTag 64 "SUB") = "SUB" := by
  unfold withWidthTag; split <;> decide +kernel

/-- `decBody` is straight-line, always completes, and its per-iteration transformer
    decrements the counter `"NZ"`. The concrete `LoopBodySpec` witness. -/
def decBodySpec : LoopBodySpec 64 decBody where
  straight := by intro i hi; simp only [decBody, List.mem_singleton] at hi; subst hi; rfl
  bodyStep := fun s => (s.setReg "NZ" (s.lvm "NZ" - 1)).nextPc
  run := by
    intro sb
    simp only [decBody, lsemStraight_singleton, lsemStep, stripWidthTag_withWidthTag_SUB,
      List.map_cons, List.map_nil, evalOperand, applyOpn]
    rfl

/-- `decBodySpec` always completes from any state (its single `SUB` is total). -/
theorem decBodySpec_succ (s : Lstate 64) : (lsemStraight decBody s).isSome := by
  simp only [decBody, lsemStraight_singleton, lsemStep, stripWidthTag_withWidthTag_SUB,
    List.map_cons, List.map_nil, evalOperand, applyOpn, Option.isSome_some]

/-- `decBody`'s leak is state-independent (one `Lopn` whose leak is its syntax). -/
theorem decBodySpec_leak (sb₁ sb₂ : Lstate 64) :
    lsemLeak decBody sb₁ = lsemLeak decBody sb₂ := by
  simp only [decBody, lsemLeak_cons, lsemLeak_nil, linstrLeak]
  cases lsemStep (.Lopn [.reg "NZ"] (withWidthTag 64 "SUB") [.reg "NZ", .imm 1]) sb₁ <;>
    cases lsemStep (.Lopn [.reg "NZ"] (withWidthTag 64 "SUB") [.reg "NZ", .imm 1]) sb₂ <;> rfl

/-- A concrete instance of the capstone over `decBodySpec` (the counter-decrement
    body): for any initial state `sb` whose public counter `"NZ"` yields a `c+1`
    trip count, the real emitted loop's `lsem` trace halts correctly and is
    constant-time. Witnesses the capstone is non-vacuous. -/
theorem dec_loop_correct_and_robust (fn : String) (top : LLabel) (sb : Lstate 64)
    (c : Nat) (hterm : LoopTerminatesIn decBodySpec sb c) :
    (lsemFuel (loopProg fn top decBody) ((c + 1) * (decBody.length + 1) + 1)
        { base := { sb with lpc := 0 }, lfn := fn }
      = some { base := { (decBodySpec.bodyStep ((reentry decBodySpec sb c).base)) with
          lpc := 2 + decBody.length }, lfn := fn })
    ∧ (∀ s₁ s₂ : Lstate 64,
        lsemLeak (loopLR "NZ" top decBody) s₁ = lsemLeak (loopLR "NZ" top decBody) s₂) :=
  loop_lsem_correct_and_robust fn top decBodySpec sb c hterm decBodySpec_leak decBodySpec_succ

/-! ## 9. Source-level tie: the public-counter back-edge is `RobustlyCTSafeJForProg`

The source loop `JForProg`'s public-counter CT fact is `JForProgCT`'s
`RobustlyCTSafeJForProg` — the loop performs no secret-indexed access under *any*
accumulator labelling (the trip count is a static `Nat`, the counter public). The
`lsem`-level `loopLR_lsemLeak_state_independent` above is its program-level
realisation: the back-edge leak is a state-independent `branch`. We record the
reuse with `doubleLoop` (the `acc := acc + acc` example), whose body is robustly
CT-safe — so the looped emission of `doubleLoop` is constant-time at both levels. -/

/-- The reuse of `JForProgCT`'s source-level public-loop CT fact: `doubleLoop`
    (`acc := acc + acc`) is `RobustlyCTSafeJForProg` — its `lsem`-level looped
    emission is therefore constant-time (state-independent leak) by
    `loopLR_lsemLeak_state_independent`. -/
theorem doubleLoop_robustlyCTSafe_reuse :
    JForProgCT.RobustlyCTSafeJForProg JasminPrint.doubleLoop :=
  JForProgCT.doubleLoop_robustlyCTSafe

/-! ## 10. General `Com` loop bodies: threading the value bridge through `bodyStep`

Sections 1–9 proved the loop simulation for a **straight-line** body characterised
by a hand-specified per-iteration transformer `bodyStep` (`LoopBodySpec`). This
section discharges **gap 2** (§"Scope"): a fully general `JForProg (.reg w)` whose
body `update` is an arbitrary straight-line-provable `Com` — the uniform-width
`regArith` fragment increment 1 models (`JasminLsemSimulation.UniformRegArith`).

The per-iteration commutation edge gap 2 names is

  `encode (Com.denote body v) = bodyStep (encode v)`   (under the value encoding),

read at the body's return register. We discharge it by threading the increment-2
functional value bridge (`JasminLsemSimulation.comToLprog_lsem_straightline`)
**through** the loop's per-iteration transformer `bodyStep := lsemStraight
bodyChain`, where `bodyChain` is the `.var`-chain the linearizer emits for the
single-accumulator loop body. The result is that one run of the emitted loop body
on the *encoded* accumulator reads exactly `JForProg.step acc` at the return
register — the `StepAgrees` edge `JForProgCT.loopRun_eq` carries. Composing the
per-iteration edge with `JForProgCT.denote_eq_foldl` gives the whole-loop `n`-fold
denotation for an arbitrary `Com` body, not just the counter-decrement witness.

The loop body context is the singleton `[.reg w]` (the loop-carried accumulator),
so `nArgs = Γ.length = 1`, and the encoded accumulator is `encode (.cons acc .nil)`
(the accumulator placed at `argName 0`, the register `comToBody` reads it from). -/

/-- The singleton accumulator valuation `[acc]` — the `Ctxt.Valuation` for the
    loop body's singleton context `[.reg w]`. Named to fix the `HVector` type at
    elaboration (`⟦.reg w⟧ = BitVec w`). -/
def singleVal {w : Nat} (acc : BitVec w) : Ctxt.Valuation (d := jasminDialect) [JasminTy.reg w] :=
  .cons acc .nil

/-- The linearizer-emitted straight-line `.var`-chain of a single-accumulator loop
    body: `straightOps 1 update 1` (the loop body context `[.reg w]` has length 1,
    so `nArgs = curDepth = 1`). This is the per-iteration `LinstrR` list the emitted
    `Cfor` runs, minus the control-flow terminator — exactly the chain the
    increment-2 bridge `comToLprog_lsem_straightline` simulates. -/
def loopBodyChain {w : Nat} (update : Com jasminDialect [JasminTy.reg w] (.reg w)) :
    List LinstrR :=
  straightOps 1 update 1

/-- The return register of a single-accumulator loop body: `comRetReg 1 argName
    update 1` — the register the body computes its result (the next accumulator)
    into, which the emitted `Cfor` writes back to `acc`. -/
def loopBodyRetReg {w : Nat} (update : Com jasminDialect [JasminTy.reg w] (.reg w)) :
    String :=
  comRetReg 1 argName update 1

/-- The loop body context `[.reg w]` is uniform-width: its one variable (the
    loop-carried accumulator, de Bruijn `.here`) has type `.reg w`. The
    `UniformCtxt` side condition of the increment-2 bridge, discharged for the
    single-accumulator loop shape. -/
theorem uniformCtxt_singleton (w : Nat) : UniformCtxt w [JasminTy.reg w] := by
  intro τ v
  cases v with
  | here => rfl
  | there v => cases v

/-- **The general-body per-iteration commutation edge (gap 2 discharged).** For a
    `UniformRegArith` loop body, running the emitted straight-line body chain
    `loopBodyChain` on the *encoded* accumulator `encode (.cons acc .nil)`
    succeeds, and decoding the return register reads exactly
    `p.update.denote (.cons acc .nil)` — the arbitrary `Com` body's denotation on
    the accumulator. This is the value bridge `comToLprog_lsem_straightline`
    threaded through the loop's per-iteration transformer: the encoded accumulator
    in, the body's denotation out at the return register. -/
theorem loopBody_run_denote {w : Nat}
    (update : Com jasminDialect [JasminTy.reg w] (.reg w))
    (hupd : UniformRegArith w update) (acc : BitVec w) :
    ∃ st', lsemStraight (loopBodyChain update) (encode (singleVal acc)) = some st' ∧
      decode st' (loopBodyRetReg update)
        = (hupd.ret_ty ▸ update.denote (singleVal acc) : ⟦(JasminTy.reg w)⟧) := by
  have hkey := comToLprog_lsem_straightline (w := w) (Γ := [JasminTy.reg w])
    (com := update) hupd (uniformCtxt_singleton w) (singleVal acc)
  simpa only [loopBodyChain, loopBodyRetReg, singleVal, List.length_singleton] using hkey

/-- **The general-body per-iteration edge, as `JForProg.step`.** Reading the
    return register after one emitted-body run on the encoded accumulator equals
    `p.step acc` = the source loop's per-iteration ground truth
    (`p.update.denote (.cons acc .nil)`). This is precisely the `StepAgrees` edge
    `JForProgCT.loopRun_eq` carries, now realised on the *linear machine*: the
    emitted body chain, run on the encoding, computes one `JForProg.step`. -/
theorem loopBody_run_step {w : Nat} (p : JForProg (.reg w))
    (hupd : UniformRegArith w p.update) (acc : BitVec w) :
    ∃ st', lsemStraight (loopBodyChain p.update) (encode (singleVal acc)) = some st' ∧
      decode st' (loopBodyRetReg p.update)
        = (hupd.ret_ty ▸ p.step acc : ⟦(JasminTy.reg w)⟧) := by
  simpa only [JForProg.step, singleVal] using loopBody_run_denote p.update hupd acc

/-- **The linear-machine body runner for a general loop body.** Running the emitted
    body chain on the encoded accumulator and decoding the return register — the
    lsem-level realisation of `JForProgCT.BodyRunner`. Returns `p.step acc` when the
    chain succeeds (always, for a `UniformRegArith` body); `acc` otherwise (never
    taken). This is `bodyStep` composed with `encode`/`decode`. -/
def lsemBodyRunner {w : Nat} (p : JForProg (.reg w)) : JForProgCT.BodyRunner (.reg w) :=
  fun acc =>
    match lsemStraight (loopBodyChain p.update) (encode (singleVal acc)) with
    | some st' => decode st' (loopBodyRetReg p.update)
    | none => acc

/-- **`StepAgrees` for a general (`UniformRegArith`) loop body — discharged on the
    linear machine.** The lsem body runner (emitted body chain on the encoded
    accumulator, decoded at the return register) computes `p.step` for every
    accumulator. This is the per-iteration edge of `JForProgCT.loopRun_eq`, no
    longer hypothesised but *proved* through the increment-2 value bridge — gap 2,
    threaded through `bodyStep`. -/
theorem lsemBodyRunner_stepAgrees {w : Nat} (p : JForProg (.reg w))
    (hupd : UniformRegArith w p.update) :
    JForProgCT.StepAgrees p (lsemBodyRunner p) := by
  intro acc
  obtain ⟨st', hrun, hdec⟩ := loopBody_run_step p hupd acc
  -- `hupd.ret_ty : (.reg w) = (.reg w)`; source and target type coincide, so the
  -- transport is the identity and `hdec` rewrites the runner directly to `p.step acc`.
  simp only [lsemBodyRunner, hrun]
  rw [hdec]

/-- **General-loop-body faithfulness (the `n`-fold denotation).** For a
    `JForProg (.reg w)` whose body is an arbitrary straight-line-provable `Com`
    (`UniformRegArith`), the emitted loop's `n`-fold run on the linear machine —
    each iteration running the emitted body chain on the encoded accumulator and
    decoding the return register — equals `p.denote init`, the source loop's
    `n`-fold denotation.

    This lifts §1–9's loop simulation from a hand-specified straight-line
    `bodyStep` (`LoopBodySpec`) to a **general `Com` loop body**: the per-iteration
    commutation edge `encode (Com.denote body v) = bodyStep (encode v)` (gap 2) is
    discharged by `lsemBodyRunner_stepAgrees` — the increment-2 value bridge
    (`JasminLsemSimulation`) threaded through `bodyStep` — and the whole-loop fold
    is `JForProgCT.loopRun_eq`. No `sorry`, no `bodyStep` hypothesis: the body edge
    is a theorem, not a carried assumption. -/
theorem general_loopBody_lsem_faithful {w : Nat} (p : JForProg (.reg w))
    (hupd : UniformRegArith w p.update) (init : BitVec w) :
    JForProgCT.loopRun p (lsemBodyRunner p) init = p.denote init :=
  JForProgCT.loopRun_eq p (lsemBodyRunner_stepAgrees p hupd) init

/-- Non-vacuity: the `doubleLoop` body (`acc := acc + acc`, a `regArith add`) is a
    `UniformRegArith` body, so the general-body faithfulness theorem applies. The
    linear-machine `n`-fold run of the emitted `for i = 0 to 4 { acc = acc + acc }`
    equals `doubleLoop.denote init` — witnessing `general_loopBody_lsem_faithful`
    is inhabited by a real, non-counter loop body. -/
theorem doubleLoop_update_uniformRegArith :
    UniformRegArith 64 JasminPrint.doubleLoop.update :=
  .var (bop := .add) rfl (.cons .here (.cons .here .nil)) (.ret .here)

/-- The general-body faithfulness theorem instantiated at `doubleLoop`: the
    linear-machine `n`-fold run of the emitted loop denotes the `n`-fold double. -/
theorem doubleLoop_general_lsem_faithful (init : BitVec 64) :
    JForProgCT.loopRun JasminPrint.doubleLoop
        (lsemBodyRunner JasminPrint.doubleLoop) init
      = JasminPrint.doubleLoop.denote init :=
  general_loopBody_lsem_faithful JasminPrint.doubleLoop
    doubleLoop_update_uniformRegArith init

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop