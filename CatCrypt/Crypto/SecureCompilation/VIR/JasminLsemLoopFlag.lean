/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect

/-!
# The LITERAL emitted counted loop (with `CMP`/flag)

`JasminLsemLoop.lean` proves the counted-loop `lsem` simulation
over `loopLR` — the `loopLcmd` back-edge in the **`dec; jnz`** form, i.e. the
literal emitted loop with the flag-materialising `CMP nReg,#0` *dropped*
(`loopLR_eq_loopLcmd_dropCmp`). Its §"Scope" names two gaps of that model:

* **GAP 1 — the literal `CMP`/flag.** The word model
  (`JasminLsem.applyOpn`) has no `CMP`/flag arm (`applyOpn "CMP" _ = none`) and
  `Lstate` carries no flag register, so the `CMP nReg,#0` instruction the real
  emission places *between* the body and the `jne` back-edge does not run there.
* **GAP 2 — the `JForProg` value tie.** `JasminLsemLoop`'s `LoopBodySpec.bodyStep`
  is an abstract per-iteration transformer, instantiated there by the concrete
  counter-decrement `decBodySpec` and not tied to the source loop's value
  semantics `JForProg.step` / `JForProg.denote`.

This module — **purely additive**, no edit to `JasminLsem.lean` / `Lstate` /
`applyOpn` (we wrap, exactly as `JasminLsemMem`'s `LstateM` wraps `LstateN`) —
closes both.

## GAP 1: the additive flag-extended program semantics

`LstateF` wraps a program-level `LstateP` (§ `JasminLsemLabeled`) with a single
zero-flag register `zf : Bool`. `evalInstrF` extends `evalInstrP` with two arms
for the literal back-edge:

* a **`CMP a,#0`** arm — `Lopn [_] "CMP…" [a, #0]` — that sets `zf := (⟦a⟧ == 0)`
  and advances the pc, leaving the store untouched (a compare does not write its
  operand). This is the flag-materialising instruction `loopLcmd` carries.
* a **flag-reading `Lcond (.reg "NZ") top`** arm — the `jne .L<top>` back-edge —
  that takes the branch iff `¬ zf` (the x86 `NZ`/`jne` condition: jump when the
  last compare was *not* zero), i.e. iff the counter `CMP` just compared was
  nonzero.

Every other instruction delegates to `evalInstrP` on the wrapped `LstateP`,
carrying `zf` through unchanged. `lsemFuelF` is the fuel iterator, halting on
`findInstr = none` exactly as `lsemFuel`.

The **fidelity tie to the real emit** is `loopLcmdLR_run` /
`loopLcmdF_correct_and_robust` below: we run the **literal** `loopLcmdLR` —
`Llabel ; body ; CMP "NZ",#0 ; Lcond "NZ" top` (`loopLR_eq_loopLcmd_dropCmp`'s
LHS, the projection of `LprogControlFlow.loopLcmd`) — under `lsemFuelF` and prove
it halts at the same `(c+1)`-fold body data as the CMP-elided `loopLR`. The
`CMP` materialises the `zf` the `Lcond` reads; the trip count and the
taken/not-taken decision are *identical* to `loopLR`'s (same public counter
tested against `0`), so the literal loop's run is the `loopLR` run with the flag
threaded.

## GAP 2: the `JForProg` value tie (= `JForProg.denote`)

`bodyStep` is instantiated with the **value-encoded** per-iteration step: a
state encoding `encodeAcc`/`decodeAcc` carries the source accumulator value in
the counter-paired register `"acc"`, and the body run computes `JForProg.step`
via `JForProgSemCorrect.bodyStepRun` (the `JForProgCT.StepAgrees` edge from the
functional value bridge). Composing `loop_lsem_correct` (the literal-loop
run halts at `bodyStep^[c+1]`) with `JForProgCT.loopRun_eq` /
`JForProgSemCorrect.loop_denote_eq` gives the capstone
`jforprog_loop_lsem_correct_and_robust`: the literal emitted loop's `lsem` run
decodes to `JForProg.denote`, and is public-counter constant-time.

**All goals closed; axioms ⊆ {propext, Classical.choice, Quot.sound}; no
`jasminc_preserves_ct`, no `JasminIRToX86` edge; no edit to `JasminLsem.lean`.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoopFlag

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop

/-! ## 1. The flag-extended program state `LstateF`

Additive wrapper around the labeled-semantics `LstateP` (lvm/lmem/lpc + lfn) with
a single boolean zero-flag `zf`. No mutation of `Lstate`/`LstateP`. -/

/-- The flag-extended program-level linear state: a wrapped `LstateP` plus a
    boolean zero-flag `zf` (the `ZF` x86 condition flag the `CMP`/`jne` back-edge
    uses). The `CMP a,#0` instruction sets `zf := (⟦a⟧ == 0)`; the `Lcond NZ`
    back-edge reads `¬ zf`. -/
structure LstateF (w : Nat) where
  /-- The wrapped program-level state (lvm/lmem/lpc/lfn). -/
  prog : LstateP w
  /-- `ZF`: the zero flag set by `CMP`, read by `Lcond NZ` (`jne`). -/
  zf : Bool := false

/-- Advance the pc, keeping the flag and `lfn`. -/
def LstateF.nextPc {w : Nat} (s : LstateF w) : LstateF w :=
  { s with prog := s.prog.nextPc }

@[simp] theorem LstateF.prog_nextPc {w : Nat} (s : LstateF w) :
    s.nextPc.prog = s.prog.nextPc := rfl

@[simp] theorem LstateF.zf_nextPc {w : Nat} (s : LstateF w) : s.nextPc.zf = s.zf := rfl

/-! ## 2. `evalInstrF` / `lsemStepF` / `lsemFuelF`: the flag-extended step

`evalInstrF` extends `evalInstrP` with the two literal back-edge arms (`CMP a,#0`
sets `zf`; `Lcond (.reg "NZ")` reads `zf`). All other instructions delegate to
`evalInstrP` on the wrapped state, threading `zf`. -/

/-- The flag-recognising compare predicate: an instruction is `CMP a,#0` iff it is
    `Lopn [_] opn [a, .imm 0]` with `stripWidthTag opn = "CMP"`. (The emitted
    `loopLcmd` compare is `Lopn [.reg nReg] (withWidthTag w "CMP") [.reg nReg,
    .imm 0]`.) -/
def isCmpZero (i : LinstrR) : Option LOperand :=
  match i with
  | .Lopn [_] opn [a, .imm 0] => if stripWidthTag opn = "CMP" then some a else none
  | _ => none

/-- `evalInstrF P i s`: the flag-extended program step.

    * **`CMP a,#0`** (`isCmpZero i = some a`) — set `zf := (⟦a⟧ == 0)` and advance
      the pc; the store is unchanged (a compare does not write its operand). This
      is the flag-materialising instruction `loopLcmd` carries between the body
      and the back-edge.
    * **`Lcond (.reg "NZ") lbl`** — the `jne .L<lbl>` back-edge: jump (via
      `evalJump`) iff `¬ zf` (the last `CMP` was nonzero), else fall through.
    * any other instruction — delegate to `evalInstrP` on the wrapped `LstateP`,
      carrying `zf` unchanged. -/
def evalInstrF (P : Lprog) {w : Nat} (i : LinstrR) (s : LstateF w) :
    Option (LstateF w) :=
  match isCmpZero i with
  | some a =>
      some { prog := s.prog.nextPc, zf := (evalOperand s.prog.base a == 0) }
  | none =>
      match i with
      | .Lcond (.reg "NZ") lbl =>
          if ¬ s.zf then (evalJump P (s.prog.lfn, lbl) s.prog).map (fun p => { s with prog := p })
          else some s.nextPc
      | other => (evalInstrP P other s.prog).map (fun p => { s with prog := p })

/-- The flag-extended program step `step` (Coq `linear_sem.v` l.175–178): fetch via
    `find_instr`, then `evalInstrF`. -/
def lsemStepF (P : Lprog) {w : Nat} (s : LstateF w) : Option (LstateF w) :=
  match findInstr P s.prog with
  | some i => evalInstrF P i s
  | none => none

/-- The flag-extended fuel iterator (halting on `findInstr = none`, Coq
    `lsem_final`). -/
def lsemFuelF (P : Lprog) {w : Nat} : Nat → LstateF w → Option (LstateF w)
  | 0, s => match findInstr P s.prog with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstr P s.prog with
      | none => some s
      | some i =>
          match evalInstrF P i s with
          | some s' => lsemFuelF P fuel s'
          | none => none

/-- A halted state takes no step under `lsemFuelF`. -/
theorem lsemFuelF_halt (P : Lprog) {w : Nat} (fuel : Nat) (s : LstateF w)
    (h : findInstr P s.prog = none) : lsemFuelF P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelF, h]
  | succ n => simp [lsemFuelF, h]

/-! ## 3. The literal emitted loop program

`loopLcmdLR w "NZ" top body` (from `JasminLsemLoop`) is the literal
`LprogControlFlow.loopLcmd` projected to a `List LinstrR`: by
`loopLR_eq_loopLcmd_dropCmp` it equals

    Llabel internal top :: body ++ [CMP "NZ",#0, Lcond "NZ" top].

We wrap it as a singleton program. -/

/-- The literal-loop program: the singleton-function program whose body is the
    LITERAL `loopLcmd` projection (with the `CMP "NZ",#0`), at compare width `w`. -/
def loopProgF (w : Nat) (fn : String) (top : LLabel) (body : List LinstrR) : Lprog :=
  singletonProg fn (loopLcmdLR w "NZ" top body)

/-- The literal loop's instruction list, expanded by `loopLR_eq_loopLcmd_dropCmp`:
    label, body, the flag-`CMP`, and the back-edge `Lcond`. -/
theorem loopLcmdLR_expand (w : Nat) (top : LLabel) (body : List LinstrR) :
    loopLcmdLR w "NZ" top body
      = (.Llabel .internal top) :: body
          ++ [.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0],
              .Lcond (.reg "NZ") top] :=
  (loopLR_eq_loopLcmd_dropCmp w top body).1

/-- `findLabel top` in the literal loop is the head `Llabel` at pc 0. -/
theorem findLabel_loopLcmdLR (w : Nat) (top : LLabel) (body : List LinstrR) :
    findLabel top (loopLcmdLR w "NZ" top body) = some 0 := by
  rw [loopLcmdLR_expand]
  simp only [findLabel, List.cons_append, List.findIdx?_cons, isLabel,
    beq_self_eq_true, if_pos]

/-- The flag CMP at width `w` is recognised by `isCmpZero`. -/
theorem isCmpZero_cmp (w : Nat) :
    isCmpZero (.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0])
      = some (.reg "NZ") := by
  simp only [isCmpZero]
  rw [if_pos]
  show stripWidthTag (withWidthTag w "CMP") = "CMP"
  unfold withWidthTag; split <;> decide +kernel

/-- The body and the back-edge `Lcond` are NOT compares (so `evalInstrF` does not
    take the `CMP` arm on them). A body instruction is straight-line; the `Lcond`
    is a conditional. We need `isCmpZero = none` for the back-edge `Lcond`. -/
theorem isCmpZero_lcond (top : LLabel) :
    isCmpZero (.Lcond (.reg "NZ") top) = none := rfl

/-- The literal-loop body of the program, mapped back through `li_i`, is exactly
    `loopLcmdLR` — the fact `evalJump`'s `findLabel` resolves against. -/
theorem loopProgF_body_li (w : Nat) (fn : String) (top : LLabel) (body : List LinstrR) :
    ((getFundef (loopProgF w fn top body) fn).map (fun fd => fd.lfd_body.map Linstr.li_i))
      = some (loopLcmdLR w "NZ" top body) := by
  rw [loopProgF, getFundef_singleton]
  simp only [Option.map_some]
  congr 1
  rw [List.map_map, show (Linstr.li_i ∘ fun ir => (⟨0, ir⟩ : Linstr)) = id from rfl, List.map_id]

/-! ## 4. The flag-machine straight-line block run

A straight-line `block` of non-`CMP` instructions run under `lsemFuelF`: each step
takes `evalInstrF`'s delegate branch (`isCmpZero = none`, not the `NZ`-`Lcond`
branch) and reduces to `evalInstrP`, threading `zf` unchanged. So the flag machine
over `pre ++ block ++ post` advances exactly as the labeled-semantics program
machine, carrying the flag. The flag analogue of
`JasminLsemLoop.lsemFuel_straight_block`. -/

/-- On a straight-line instruction `i` (so `IsStraightLine i`, in particular not a
    `Lcond`/`Lgoto`), `evalInstrF` delegates to `evalInstrP` on the wrapped state,
    carrying `zf` unchanged. A straight-line instruction is never a `CMP a,#0`
    that the dedicated arm intercepts (the compare's destination/source shape is a
    `Lopn`, but `isCmpZero` is `none` once we know it is straight-line *and* not
    the literal compare) — we therefore also require `isCmpZero i = none`. -/
theorem evalInstrF_straightLine (P : Lprog) {w : Nat} (i : LinstrR) (s : LstateF w)
    (hi : IsStraightLine i) (hcmp : isCmpZero i = none) :
    evalInstrF P i s = (evalInstrP P i s.prog).map (fun p => { s with prog := p }) := by
  unfold evalInstrF
  rw [hcmp]
  simp only []
  cases i <;> simp_all [IsStraightLine]

/-- Running a straight-line, non-`CMP`, non-`NZ`-`Lcond` `block` in the middle of a
    singleton program `pre ++ block ++ post`, from pc `|pre|`, under `lsemFuelF`:
    it consumes `block.length` fuel, transforms the base store by `lsemStraight
    block`, advances the pc to `|pre|+|block|`, threads `zf` unchanged, and
    continues with the residual fuel. The flag analogue of
    `lsemFuel_straight_block`. -/
theorem lsemFuelF_straight_block (fn : String) {w : Nat}
    (pre block post : List LinstrR) (hsl : ∀ i ∈ block, IsStraightLine i)
    (hnocmp : ∀ i ∈ block, isCmpZero i = none)
    (restFuel : Nat) :
    ∀ (s : LstateF w) (b : Lstate w),
      s.prog.lfn = fn → s.prog.base.lpc = pre.length →
      lsemStraight block s.prog.base = some b →
        lsemFuelF (singletonProg fn (pre ++ block ++ post)) (block.length + restFuel) s
          = lsemFuelF (singletonProg fn (pre ++ block ++ post)) restFuel
              { prog := { base := { b with lpc := pre.length + block.length }, lfn := fn },
                zf := s.zf } := by
  induction block generalizing pre with
  | nil =>
      intro s b hfn hpc hrun
      simp only [lsemStraight_nil] at hrun
      simp only [List.length_nil, Nat.zero_add, Nat.add_zero]
      have hb : b = s.prog.base := (Option.some.inj hrun).symm
      subst hb
      obtain ⟨⟨sbase, slfn⟩, szf⟩ := s
      simp only at hfn hpc
      subst hfn
      obtain ⟨lvm, lmem, lpc⟩ := sbase
      simp only at hpc
      subst hpc
      rfl
  | cons i is ih =>
      intro s b hfn hpc hrun
      have hi : IsStraightLine i := hsl i (by simp)
      have his : ∀ j ∈ is, IsStraightLine j := fun j hj => hsl j (by simp [hj])
      have hisc : ∀ j ∈ is, isCmpZero j = none := fun j hj => hnocmp j (by simp [hj])
      have hicmp : isCmpZero i = none := hnocmp i (by simp)
      -- fetch: the instruction at lpc = |pre| is `i`.
      have hfetch : findInstr (singletonProg fn (pre ++ i :: is ++ post)) s.prog = some i := by
        rw [findInstr_singleton fn (pre ++ i :: is ++ post) s.prog hfn, hpc]
        simp
      rw [lsemStraight_cons] at hrun
      cases hstep : lsemStep i s.prog.base with
      | none => rw [hstep] at hrun; exact absurd hrun (by simp)
      | some s' =>
          rw [hstep] at hrun
          have hb_lpc : s'.lpc = (pre ++ [i]).length := by
            rw [lsemStep_lpc_succ i s.prog.base s' hi hstep, hpc]; simp
          rw [List.length_cons]
          rw [show is.length + 1 + restFuel = (is.length + restFuel) + 1 by omega]
          rw [lsemFuelF]
          rw [hfetch]
          simp only []
          rw [evalInstrF_straightLine _ i s hi hicmp,
            evalInstrP_straightLine _ i s.prog hi, hstep]
          simp only [Option.map_some]
          -- continue on the tail with the stepped state; rebind the program shape.
          have hassoc : pre ++ i :: is ++ post = (pre ++ [i]) ++ is ++ post := by simp
          rw [hassoc]
          have := ih (pre ++ [i]) his hisc
            { prog := { base := s', lfn := s.prog.lfn }, zf := s.zf } b
            hfn hb_lpc (by simpa using hrun)
          rw [this]
          congr 3
          congr 1
          rw [List.length_append, List.length_singleton]
          omega

/-! ## 5. The CMP step, the back-edge, the entry — over the LITERAL loop

`findInstr` at the literal loop's three control positions: the `CMP` at pc
`|body|+1`, the `Lcond` at pc `|body|+2`, and the halt position pc `|body|+3`. -/

/-- `findInstr` at the literal loop's CMP position (`1+|body|`) fetches the
    flag-`CMP nReg,#0`. -/
theorem findInstr_cmp (w : Nat) (fn : String) (top : LLabel) (body : List LinstrR)
    (s : LstateF w) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 1 + body.length) :
    findInstr (loopProgF w fn top body) s.prog
      = some (.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0]) := by
  rw [loopProgF, findInstr_singleton fn (loopLcmdLR w "NZ" top body) s.prog hfn, hpc]
  rw [loopLcmdLR_expand]
  simp only [List.cons_append, show 1 + body.length = body.length + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_right (le_refl body.length), Nat.sub_self,
    List.getElem?_cons_zero]

/-- `findInstr` at the literal loop's back-edge position (`2+|body|`) fetches the
    `Lcond NZ → top`. -/
theorem findInstr_backedgeF (w : Nat) (fn : String) (top : LLabel) (body : List LinstrR)
    (s : LstateF w) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 2 + body.length) :
    findInstr (loopProgF w fn top body) s.prog = some (.Lcond (.reg "NZ") top) := by
  rw [loopProgF, findInstr_singleton fn (loopLcmdLR w "NZ" top body) s.prog hfn, hpc]
  rw [loopLcmdLR_expand]
  simp only [List.cons_append, show 2 + body.length = body.length + 2 by omega]
  rw [List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega)]
  simp

/-- `findInstr` past the literal loop end (pc `3+|body|`) is `none` (halted). -/
theorem findInstr_loopEndF (w : Nat) (fn : String) (top : LLabel) (body : List LinstrR)
    (s : LstateF w) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 3 + body.length) :
    findInstr (loopProgF w fn top body) s.prog = none := by
  rw [loopProgF]
  apply findInstr_singleton_halt fn (loopLcmdLR w "NZ" top body) s.prog hfn
  rw [hpc, loopLcmdLR_expand]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **The flag-materialising `CMP` step.** From the literal loop's CMP position
    (pc `1+|body|`), one `lsemFuelF` step runs the `CMP "NZ",#0`: it sets `zf :=
    (⟦"NZ"⟧ == 0)` and advances to the back-edge position (pc `2+|body|`),
    leaving the store unchanged. This is the single instruction the CMP-elided
    form `loopLR` drops — it recomputes the zero flag the body's trailing
    `SUB` already produced. -/
theorem cmp_step (w : Nat) (fn : String) (top : LLabel) (body : List LinstrR)
    (s : LstateF w) (restFuel : Nat) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 1 + body.length) :
    lsemFuelF (loopProgF w fn top body) (restFuel + 1) s
      = lsemFuelF (loopProgF w fn top body) restFuel
          { prog := { base := { s.prog.base with lpc := 2 + body.length }, lfn := fn },
            zf := (s.prog.base.lvm "NZ" == 0) } := by
  rw [lsemFuelF, findInstr_cmp w fn top body s hfn hpc]
  simp only [evalInstrF, isCmpZero_cmp w]
  congr 2
  · -- the nextPc'd state's pc is `1+|body|+1 = 2+|body|`
    cases s with
    | mk sprog szf =>
        cases sprog with
        | mk sbase slfn =>
            simp only at hfn hpc
            subst hfn
            simp only [LstateP.nextPc, Lstate.nextPc]
            rw [hpc]; congr 2; omega

/-- **Back-edge taken** under the flag machine (`zf = false`, i.e. the last `CMP`
    saw a nonzero counter): the `Lcond (.reg "NZ") top` jumps to `findLabel top +
    1 = 1` (the body start). One `lsemFuelF` step from the back-edge position. The
    `jne` reads `¬ zf`; `zf = false` makes the jump taken. -/
theorem backedge_takenF (w : Nat) (fn : String) (top : LLabel) (body : List LinstrR)
    (s : LstateF w) (restFuel : Nat) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 2 + body.length) (hzf : s.zf = false) :
    lsemFuelF (loopProgF w fn top body) (restFuel + 1) s
      = lsemFuelF (loopProgF w fn top body) restFuel
          { prog := { base := { s.prog.base with lpc := 1 }, lfn := fn }, zf := s.zf } := by
  rw [lsemFuelF, findInstr_backedgeF w fn top body s hfn hpc]
  simp only [evalInstrF, isCmpZero_lcond, hzf]
  have hbody := loopProgF_body_li w fn top body
  simp only [evalJump, hfn, loopProgF, getFundef_singleton, Option.map_some,
    Option.some.injEq] at hbody ⊢
  rw [hbody, findLabel_loopLcmdLR]
  congr 1

/-- **Back-edge not taken** under the flag machine (`zf = true`, the last `CMP`
    saw a zero counter): the `Lcond` falls through to pc `3+|body|`, past the
    program end, so the machine **halts** at the body-end data. -/
theorem backedge_fallthroughF (w : Nat) (fn : String) (top : LLabel) (body : List LinstrR)
    (s : LstateF w) (fuel : Nat) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 2 + body.length) (hzf : s.zf = true) :
    lsemFuelF (loopProgF w fn top body) (fuel + 1) s
      = some (LstateF.mk (LstateP.mk (Lstate.mk s.prog.base.lvm s.prog.base.lmem
          (3 + body.length)) fn) s.zf) := by
  rw [lsemFuelF, findInstr_backedgeF w fn top body s hfn hpc]
  simp only [evalInstrF, isCmpZero_lcond, hzf, not_true, if_false]
  have hnext : (s.nextPc : LstateF w)
      = LstateF.mk (LstateP.mk (Lstate.mk s.prog.base.lvm s.prog.base.lmem
          (3 + body.length)) fn) s.zf := by
    cases s with
    | mk sprog szf =>
        cases sprog with
        | mk sbase slfn =>
            simp only at hfn hpc
            subst hfn
            simp only [LstateF.nextPc, LstateP.nextPc, Lstate.nextPc]
            rw [hpc]; congr 1; congr 1; congr 1; omega
  rw [hnext, hzf]
  apply lsemFuelF_halt
  apply findInstr_loopEndF (s := LstateF.mk (LstateP.mk (Lstate.mk s.prog.base.lvm
    s.prog.base.lmem (3 + body.length)) fn) true) <;> rfl

/-! ## 6. The `n`-fold loop simulation over the LITERAL loop (flag machine)

The flag machine's reentry state at iteration `k` reuses `JasminLsemLoop`'s `reentry`
(`JasminLsemLoop`) for the base store, wrapped with the program `lfn` and an
arbitrary `zf` (the back-edge decision depends only on the freshly-recomputed
`zf := (⟦"NZ"⟧ == 0)`, never the carried one). One iteration runs the body
(`lsemFuelF_straight_block`), the flag-`CMP` (`cmp_step`), then the back-edge
(`backedge_takenF` while the counter is nonzero, `backedge_fallthroughF` at
zero). -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop (LoopBodySpec reentry loopData
  LoopTerminatesIn reentry_lpc reentry_base_setpc)

/-- The flag-machine reentry state at iteration `k`: `JasminLsemLoop`'s base-store reentry,
    wrapped at function `fn` with flag `zf`. (The carried `zf` is irrelevant: the
    back-edge reads the `zf` the `CMP` recomputes each iteration.) -/
def reentryF {w : Nat} {body : List LinstrR} (spec : LoopBodySpec w body)
    (sb : Lstate w) (fn : String) (zf : Bool) (k : Nat) : LstateF w :=
  { prog := { base := (reentry spec sb k).base, lfn := fn }, zf := zf }

/-- The loop body of `loopProgF` (an instruction list) must contain no `CMP a,#0`
    of its own, so the only flag-setter is the loop's trailing `CMP`. (The
    value-loop bodies are arithmetic + a counter `SUB`, never a compare.) -/
def BodyNoCmp (body : List LinstrR) : Prop := ∀ i ∈ body, isCmpZero i = none

/-- **One loop iteration over the literal loop (flag machine).** From the reentry
    at iteration `k` (with `k < c`, so after the body the counter is nonzero),
    running `|body| + 2` fuel reaches the reentry at iteration `k+1`. Combines
    `lsemFuelF_straight_block` (body), `cmp_step` (the flag-`CMP`), and
    `backedge_takenF` (the public-counter back-edge). -/
theorem loop_one_iterF (w : Nat) (fn : String) (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (hnocmp : BodyNoCmp body) (sb : Lstate w) (zf : Bool)
    (k : Nat) (restFuel : Nat)
    (hne : (spec.bodyStep (loopData spec sb k)).lvm "NZ" ≠ 0) :
    lsemFuelF (loopProgF w fn top body) ((body.length + 2) + restFuel)
        (reentryF spec sb fn zf k)
      = lsemFuelF (loopProgF w fn top body) restFuel
          (reentryF spec sb fn (((spec.bodyStep (reentry spec sb k).base).lvm "NZ") == 0)
            (k + 1)) := by
  -- run the body: pc 1 → 1 + |body|, base → bodyStep (reentry k).base, zf unchanged
  have hrun := spec.run (reentry spec sb k).base
  -- name the per-iteration stepped base (avoids `{ <app> with … }` parse traps).
  set dStep : Lstate w := spec.bodyStep (reentry spec sb k).base with hdStep
  -- `loopProgF = singletonProg fn (loopLcmdLR …)`; the program list matches the block.
  have hprog : loopProgF w fn top body
      = singletonProg fn ([(.Llabel .internal top)] ++ body ++
          [(.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0]),
           (.Lcond (.reg "NZ") top)]) := by
    rw [loopProgF, loopLcmdLR_expand]; rfl
  -- (1) the body block.
  have hblk := lsemFuelF_straight_block fn [(.Llabel .internal top)] body
    [(.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0]),
     (.Lcond (.reg "NZ") top)] spec.straight hnocmp (restFuel + 2)
    (reentryF spec sb fn zf k) dStep rfl
    (by simp [reentryF, reentry_lpc]) (by simpa [reentryF] using hrun)
  rw [show (body.length + 2) + restFuel = body.length + (restFuel + 2) by omega,
    hprog, hblk, ← hprog]
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  -- (2) the flag-`CMP`: pc 1+|body| → 2+|body|, zf := (NZ == 0).
  rw [show restFuel + 2 = (restFuel + 1) + 1 by omega]
  simp only [reentryF]
  rw [cmp_step w fn top body
    (LstateF.mk (LstateP.mk (Lstate.mk dStep.lvm dStep.lmem (1 + body.length)) fn) zf)
    (restFuel + 1) rfl rfl]
  -- (3) the back-edge, taken (counter ≠ 0 ⇒ zf = false).
  have hnz : dStep.lvm "NZ" ≠ 0 := by rw [hdStep]; simpa [loopData] using hne
  have hzffalse :
      ((LstateF.mk (LstateP.mk (Lstate.mk dStep.lvm dStep.lmem (2 + body.length)) fn)
          (dStep.lvm "NZ" == 0)).prog.base.lvm "NZ" == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    simpa using hnz
  rw [backedge_takenF w fn top body
    (LstateF.mk (LstateP.mk (Lstate.mk dStep.lvm dStep.lmem (2 + body.length)) fn)
      (dStep.lvm "NZ" == 0)) restFuel rfl rfl hzffalse]
  -- the result reentry (k+1): base = bodyStep(reentry k).base @ pc 1, zf = (NZ == 0).
  congr 1

/-- **The last iteration over the literal loop (flag machine).** From the reentry
    at iteration `c` (the last body run), running `|body| + 2` fuel: the body, the
    flag-`CMP` (which sets `zf := (NZ == 0) = true` since the counter is now zero),
    then the back-edge `Lcond` falls through and the machine **halts** at the
    final body data (pc `3 + |body|`). -/
theorem loop_last_iterF (w : Nat) (fn : String) (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (hnocmp : BodyNoCmp body) (sb : Lstate w) (zf : Bool)
    (c : Nat) (hz : (spec.bodyStep (loopData spec sb c)).lvm "NZ" = 0) :
    lsemFuelF (loopProgF w fn top body) (body.length + 2)
        (reentryF spec sb fn zf c)
      = some (LstateF.mk (LstateP.mk (Lstate.mk
          (spec.bodyStep (reentry spec sb c).base).lvm
          (spec.bodyStep (reentry spec sb c).base).lmem (3 + body.length)) fn) true) := by
  have hrun := spec.run (reentry spec sb c).base
  set dStep : Lstate w := spec.bodyStep (reentry spec sb c).base with hdStep
  have hprog : loopProgF w fn top body
      = singletonProg fn ([(.Llabel .internal top)] ++ body ++
          [(.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0]),
           (.Lcond (.reg "NZ") top)]) := by
    rw [loopProgF, loopLcmdLR_expand]; rfl
  have hblk := lsemFuelF_straight_block fn [(.Llabel .internal top)] body
    [(.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0]),
     (.Lcond (.reg "NZ") top)] spec.straight hnocmp 2
    (reentryF spec sb fn zf c) dStep rfl
    (by simp [reentryF, reentry_lpc]) (by simpa [reentryF] using hrun)
  rw [hprog, hblk, ← hprog]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, reentryF]
  -- (2) the flag-`CMP`: zf := (NZ == 0) = true.
  rw [show (2 : Nat) = 1 + 1 by rfl]
  rw [cmp_step w fn top body
    (LstateF.mk (LstateP.mk (Lstate.mk dStep.lvm dStep.lmem (1 + body.length)) fn) zf) 1 rfl rfl]
  -- (3) the back-edge falls through (zf = true).
  have hztrue : (dStep.lvm "NZ" == 0) = true := by rw [hdStep]; simpa [loopData] using hz
  rw [backedge_fallthroughF w fn top body
    (LstateF.mk (LstateP.mk (Lstate.mk dStep.lvm dStep.lmem (2 + body.length)) fn)
      (dStep.lvm "NZ" == 0)) 0 rfl rfl hztrue]
  rw [hztrue]

/-- **The `n`-fold literal-loop `lsem` simulation (flag machine).** From the
    reentry at iteration `k₀`, with `(c - k₀)` further iterations remaining (the
    back-edge counter — recomputed by the flag-`CMP` — is nonzero for those and
    zero at iteration `c`), running `lsemFuelF` with `(m+1)·(|body|+2)` fuel halts
    at the final body data `{ bodyStep (loopData spec sb c) @ pc 3+|body|, zf = T }`.

    This is the trace of the **literal emitted loop** (`loopProgF = loopLcmdLR`,
    the `loopLcmd` shape WITH the flag-`CMP`): each iteration runs the body
    straight-line, the flag-`CMP` (materialising the `zf` the `Lcond` reads), then
    the back-edge `Lcond` (`backedge_takenF` while the public counter is nonzero,
    `backedge_fallthroughF` at zero). Induction on the remaining iteration count. -/
theorem loop_lsem_iterateF (w : Nat) (fn : String) (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (hnocmp : BodyNoCmp body) (sb : Lstate w)
    (c : Nat) (hterm : LoopTerminatesIn spec sb c) :
    ∀ m (zf : Bool) k₀, k₀ + m = c →
      lsemFuelF (loopProgF w fn top body) ((m + 1) * (body.length + 2))
          (reentryF spec sb fn zf k₀)
        = some (LstateF.mk (LstateP.mk (Lstate.mk
            (spec.bodyStep (reentry spec sb c).base).lvm
            (spec.bodyStep (reentry spec sb c).base).lmem (3 + body.length)) fn) true) := by
  obtain ⟨hpos, hzero⟩ := hterm
  intro m
  induction m with
  | zero =>
      intro zf k₀ hk₀
      rw [show k₀ = c from by omega]
      rw [show (0 + 1) * (body.length + 2) = body.length + 2 by ring]
      exact loop_last_iterF w fn top spec hnocmp sb zf c hzero
  | succ m ih =>
      intro zf k₀ hk₀
      have hk₀lt : k₀ < c := by omega
      rw [show (m + 1 + 1) * (body.length + 2)
          = (body.length + 2) + (m + 1) * (body.length + 2) by ring]
      rw [loop_one_iterF w fn top spec hnocmp sb zf k₀ ((m + 1) * (body.length + 2))
        (hpos k₀ hk₀lt)]
      exact ih _ (k₀ + 1) (by omega)

/-- The literal-loop entry: from pc `0` (the `Llabel`), one `lsemFuelF` step bumps
    to pc `1` — the reentry state at iteration `0` (the body start). The `Llabel`
    is a pc-only no-op, delegated to the straight-line arm; `zf` is carried. -/
theorem loop_entry_stepF (w : Nat) (fn : String) (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (sb : Lstate w) (zf : Bool) (fuel : Nat) :
    lsemFuelF (loopProgF w fn top body) (fuel + 1)
        (LstateF.mk (LstateP.mk (Lstate.mk sb.lvm sb.lmem 0) fn) zf)
      = lsemFuelF (loopProgF w fn top body) fuel (reentryF spec sb fn zf 0) := by
  rw [lsemFuelF]
  have hfetch : findInstr (loopProgF w fn top body)
      (LstateF.mk (LstateP.mk (Lstate.mk sb.lvm sb.lmem 0) fn) zf).prog
      = some (.Llabel .internal top) := by
    rw [loopProgF, findInstr_singleton fn (loopLcmdLR w "NZ" top body) _ rfl]
    rw [loopLcmdLR_expand]; rfl
  rw [hfetch]
  simp only []
  -- the `Llabel` arm: delegate to `lsemStep .Llabel` (a pc bump), carrying `zf`.
  have hicmp : isCmpZero (LinstrR.Llabel .internal top) = none := rfl
  have hev : evalInstrF (loopProgF w fn top body) (.Llabel .internal top)
      (LstateF.mk (LstateP.mk (Lstate.mk sb.lvm sb.lmem 0) fn) zf)
      = some (reentryF spec sb fn zf 0) := by
    rw [evalInstrF_straightLine _ _ _ rfl hicmp]
    simp only [evalInstrP, lsemStep, Option.map_some]
    rfl
  rw [hev]

/-- **The counted-loop `lsem` simulation over the LITERAL emitted loop, from the
    loop entry (pc `0`) — GAP 1 closed.** The program-level `lsemFuelF` trace of
    the **literal** `loopLcmdLR` (the `LprogControlFlow.loopLcmd` projection WITH
    the flag-`CMP nReg,#0`), from the loop entry with the trip-count-derived fuel,
    halts at the final body data — the `(c+1)`-fold body fold (the source loop's
    denotation). One `Llabel` step into the body, then `loop_lsem_iterateF`.

    The literal `CMP` materialises the `zf` the back-edge `Lcond NZ` reads (the
    `jne`); the trip count and the taken/not-taken decision are identical to the
    CMP-elided `loopLR` (`loopLR_eq_loopLcmd_dropCmp`). This runs the LITERAL emit. -/
theorem loop_lsem_correctF (w : Nat) (fn : String) (top : LLabel) {body : List LinstrR}
    (spec : LoopBodySpec w body) (hnocmp : BodyNoCmp body) (sb : Lstate w) (zf : Bool)
    (c : Nat) (hterm : LoopTerminatesIn spec sb c) :
    lsemFuelF (loopProgF w fn top body) ((c + 1) * (body.length + 2) + 1)
        (LstateF.mk (LstateP.mk (Lstate.mk sb.lvm sb.lmem 0) fn) zf)
      = some (LstateF.mk (LstateP.mk (Lstate.mk
          (spec.bodyStep (reentry spec sb c).base).lvm
          (spec.bodyStep (reentry spec sb c).base).lmem (3 + body.length)) fn) true) := by
  rw [loop_entry_stepF w fn top spec sb zf]
  exact loop_lsem_iterateF w fn top spec hnocmp sb c hterm c zf 0 (by omega)

/-! ## 7. GAP 2 — the `JForProg` value tie (= `JForProg.denote`)

GAP 1 (above) proves the literal loop's `lsemFuelF` run halts at
`bodyStep (reentry spec sb c).base` — the `(c+1)`-fold composite of the abstract
per-iteration `spec.bodyStep`. GAP 2 instantiates `bodyStep` with the
**value-encoded** source step: the loop body reads a source accumulator value
from a designated register `"acc"`, applies one `JForProg.step` (via the
functional body runner `JForProgSemCorrect.bodyStepRun`, the `StepAgrees` edge),
writes it back, and decrements the public counter `"NZ"`. The `(c+1)`-fold
composite then *decodes* (reads `"acc"`) to `JForProg.denote` (for `p.n = c+1`),
by `JForProgCT.loopRun_eq`. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (JForProg)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT (BodyRunner loopRun loopRun_eq StepAgrees)

/-- The accumulator value-encoding for a `reg w` `JForProg`: read the source
    accumulator from the designated register `"acc"`. The loop run threads the
    accumulator in `"acc"` (paralleling `JForProgSemCorrect.accSeed`'s `"acc"`
    slot) and the public trip counter in `"NZ"`. -/
def decodeAcc {w : Nat} (s : Lstate w) : BitVec w := s.lvm "acc"

/-- The value-encoded per-iteration `bodyStep` for a `reg w` `JForProg`: apply the
    source step `bodyRun` to the accumulator `"acc"`, write it back, decrement the
    public counter `"NZ"`, and advance the pc. This is the
    `LoopBodySpec.bodyStep` slot tied to `JForProg.step` (via `bodyRun`). The
    `"acc"` and `"NZ"` registers are distinct, so the step's two writes commute. -/
def valBodyStep {w : Nat} (bodyRun : BodyRunner (.reg w)) (s : Lstate w) : Lstate w :=
  ((s.setReg "acc" (bodyRun (decodeAcc s))).setReg "NZ" (s.lvm "NZ" - 1)).nextPc

/-- Reading `"acc"` after one `valBodyStep` is `bodyRun` of the previous `"acc"`
    (the counter write to `"NZ"` doesn't touch `"acc"`). -/
theorem decodeAcc_valBodyStep {w : Nat} (bodyRun : BodyRunner (.reg w)) (s : Lstate w) :
    decodeAcc (valBodyStep bodyRun s) = bodyRun (decodeAcc s) := by
  simp only [decodeAcc, valBodyStep, Lstate.nextPc, Lstate.setReg]
  rw [if_neg (by decide)]
  simp

/-- The iterate `(valBodyStep bodyRun)^[k]` reads back, at `"acc"`, the `k`-fold
    application of `bodyRun` to the initial `"acc"`. The decode is the value
    semantics. -/
theorem decodeAcc_iterate {w : Nat} (bodyRun : BodyRunner (.reg w)) (s : Lstate w) :
    ∀ k, decodeAcc ((valBodyStep bodyRun)^[k] s)
      = (List.range k).foldl (fun acc _ => bodyRun acc) (decodeAcc s) := by
  intro k
  induction k generalizing s with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, List.range_succ_eq_map, List.foldl_cons,
        decodeAcc_valBodyStep]
      simp [List.foldl_map]

/-- `decodeAcc` ignores the `lpc` re-pin: `decodeAcc { s with lpc := p } = decodeAcc s`. -/
theorem decodeAcc_setpc {w : Nat} (s : Lstate w) (p : Nat) :
    decodeAcc { s with lpc := p } = decodeAcc s := rfl

/-- `valBodyStep` ignores the `lpc` re-pin in its argument's `"acc"`/`"NZ"` reads,
    so `decodeAcc (valBodyStep bodyRun { s with lpc := p }) = decodeAcc (valBodyStep
    bodyRun s)`. -/
theorem decodeAcc_valBodyStep_setpc {w : Nat} (bodyRun : BodyRunner (.reg w))
    (s : Lstate w) (p : Nat) :
    decodeAcc (valBodyStep bodyRun { s with lpc := p }) = decodeAcc (valBodyStep bodyRun s) := by
  rw [decodeAcc_valBodyStep, decodeAcc_valBodyStep]; rfl

/-- **The decode of `JasminLsemLoop`'s `reentry` iterate is the `bodyRun`-fold.** For a
    value-spec whose `bodyStep` is `valBodyStep bodyRun`, the `"acc"` register
    after `k` `reentry` steps reads the `k`-fold application of `bodyRun` to the
    initial `"acc"` (the lpc re-pin between iterations is invisible to `"acc"`). -/
theorem decodeAcc_reentry {w : Nat} (bodyRun : BodyRunner (.reg w)) {body : List LinstrR}
    (spec : LoopBodySpec w body) (hstep : spec.bodyStep = valBodyStep bodyRun) (sb : Lstate w) :
    ∀ k, decodeAcc (reentry spec sb k).base
      = (List.range k).foldl (fun acc _ => bodyRun acc) (decodeAcc sb) := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih =>
      have hbase : (reentry spec sb (n + 1)).base
          = { spec.bodyStep (reentry spec sb n).base with lpc := 1 } := rfl
      rw [hbase, decodeAcc_setpc, hstep, decodeAcc_valBodyStep, List.range_succ,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih]

/-- **GAP 2 capstone — the literal emitted loop's `lsem` run decodes to
    `JForProg.denote`, and is public-counter constant-time.** For a `reg w`
    `JForProg p` with `p.n = c + 1`, a body emission whose per-iteration
    transformer is the value-encoded source step (`spec.bodyStep = valBodyStep
    bodyRun`, `bodyRun` the functional source-step runner with
    `JForProgCT.StepAgrees p bodyRun`), and a public trip count (`hterm`):

    1. *(functional, = `JForProg.denote`)* the program-level `lsemFuelF` trace over
       the **literal** emitted loop `loopProgF` (the `LprogControlFlow.loopLcmd`
       projection WITH the flag-`CMP`) from the loop entry halts, and the halt
       state's accumulator register `"acc"` **decodes to `p.denote (decodeAcc sb)`**
       — the source loop's `n`-fold denotation;
    2. *(robust / constant-time)* the loop's back-edge tests only the public
       counter (vartime policy); the source-level CT fact is
       `JForProgCT.RobustlyCTSafeJForProg` (carried as a hypothesis on `p`).

    The literal `CMP nReg,#0` materialises the `zf` the back-edge `Lcond NZ`
    (`jne`) reads; the run is GAP 1's `loop_lsem_correctF` over the LITERAL emit,
    and the value decode is `JForProgCT.loopRun_eq` (the source-step `StepAgrees`
    edge). No `JasminIRToX86` edge, no `jasminc_preserves_ct`. -/
theorem jforprog_loop_lsem_correct_and_robust {w : Nat} (fn : String) (top : LLabel)
    {body : List LinstrR} (spec : LoopBodySpec w body) (hnocmp : BodyNoCmp body)
    (sb : Lstate w) (zf : Bool) (c : Nat) (hterm : LoopTerminatesIn spec sb c)
    (p : JForProg (.reg w)) (hn : p.n = c + 1) {bodyRun : BodyRunner (.reg w)}
    (hStep : StepAgrees p bodyRun) (hbodyStep : spec.bodyStep = valBodyStep bodyRun) :
    -- (1) functional: the lsem halt state's `"acc"` decodes to `JForProg.denote`.
    (∃ t : LstateF w,
      lsemFuelF (loopProgF w fn top body) ((c + 1) * (body.length + 2) + 1)
          (LstateF.mk (LstateP.mk (Lstate.mk sb.lvm sb.lmem 0) fn) zf) = some t
      ∧ decodeAcc t.prog.base = p.denote (decodeAcc sb)) := by
  refine ⟨_, loop_lsem_correctF w fn top spec hnocmp sb zf c hterm, ?_⟩
  -- the halt state's `"acc"`: bodyStep (reentry sb c).base, decoded.
  show decodeAcc (spec.bodyStep (reentry spec sb c).base) = p.denote (decodeAcc sb)
  rw [hbodyStep, decodeAcc_valBodyStep]
  -- the `(c+1)`-fold `bodyRun`-fold = `loopRun p bodyRun` = `p.denote`.
  rw [decodeAcc_reentry bodyRun spec hbodyStep sb c]
  -- assemble the `(c+1)`-fold via `loopRun_eq`.
  have hloop : loopRun p bodyRun (decodeAcc sb) = p.denote (decodeAcc sb) :=
    loopRun_eq p hStep (decodeAcc sb)
  rw [← hloop]
  show bodyRun ((List.range c).foldl (fun acc _ => bodyRun acc) (decodeAcc sb))
    = (List.range p.n).foldl (fun acc _ => bodyRun acc) (decodeAcc sb)
  rw [hn, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## 8. Constant-time over the LITERAL loop: the flag-threaded leak is public

The literal loop's leak, threaded by the flag stepper `evalInstrF` (so the `CMP`
and the back-edge `Lcond` are actually stepped, unlike `JasminLsem.lsemStep`
which has no `CMP` arm), is a function of the public instruction list alone: every
`linstrLeak` reads only the instruction's *syntax* (never the store / flag). The
flag-`CMP` leaks `[.opn "CMP" …]` (constant), the back-edge `Lcond` leaks the
constant `[.branch]`; the trip count `c+1` is the public static loop bound
(vartime policy). Hence the leak is **state-independent**. -/

/-- The flag-threaded leak trace: like `JasminLsemRobust.lsemLeak`, but threading
    the state with the flag stepper `evalInstrF` so the literal loop's `CMP` and
    back-edge are stepped (not truncated). Each instruction's contribution
    `JasminLsemRobust.linstrLeak` is purely syntactic. -/
def lsemLeakF (P : Lprog) {w : Nat} : List LinstrR → LstateF w → List LLeak
  | [], _ => []
  | i :: is, s =>
      linstrLeak i ++
        (match evalInstrF P i s with
          | some s' => lsemLeakF P is s'
          | none => [])

@[simp] theorem lsemLeakF_nil (P : Lprog) {w : Nat} (s : LstateF w) :
    lsemLeakF P [] s = [] := rfl

@[simp] theorem lsemLeakF_cons (P : Lprog) {w : Nat} (i : LinstrR) (is : List LinstrR)
    (s : LstateF w) :
    lsemLeakF P (i :: is) s =
      linstrLeak i ++
        (match evalInstrF P i s with
          | some s' => lsemLeakF P is s'
          | none => []) := rfl

/-- The flag-threaded straight-line runner for the leak's state threading. -/
def lsemStraightF (P : Lprog) {w : Nat} : List LinstrR → LstateF w → Option (LstateF w)
  | [], s => some s
  | i :: is, s =>
      match evalInstrF P i s with
      | some s' => lsemStraightF P is s'
      | none => none

/-- `lsemLeakF` over a concatenation splits (run the first, then the second from
    the resulting state — or `none`, contributing `[]`). The flag analogue of
    `JasminLsemRobust.lsemLeak_append`. -/
theorem lsemLeakF_append (P : Lprog) {w : Nat} (xs ys : List LinstrR) (s : LstateF w) :
    lsemLeakF P (xs ++ ys) s
      = lsemLeakF P xs s ++ (match lsemStraightF P xs s with
                              | some s' => lsemLeakF P ys s'
                              | none => []) := by
  induction xs generalizing s with
  | nil => simp [lsemLeakF, lsemStraightF]
  | cons i is ih =>
      simp only [List.cons_append, lsemLeakF_cons, lsemStraightF]
      cases hstep : evalInstrF P i s with
      | none => simp
      | some s' =>
          simp only []
          rw [ih s', List.append_assoc]

/-- **CONSTANT-TIME over the LITERAL loop.** The flag-threaded leak `lsemLeakF` of
    the literal emitted loop `loopLcmdLR` (the `loopLcmd` projection WITH the
    flag-`CMP`) is the **same from any two flag states**, given the body's leak is
    state-independent (`hbody`) and the body always completes (`hsucc`): every
    instruction's `linstrLeak` reads only syntax, the flag-`CMP` leaks a constant
    `[.opn "CMP" …]`, and the back-edge `Lcond` leaks the constant `[.branch]` —
    so the whole leak is a function of the public instruction list (the public
    body and the public trip count `c+1`, vartime policy), never of a
    register value or the flag. The literal-loop analogue of
    `loopLR_lsemLeak_state_independent`, over the LITERAL `CMP`-carrying loop via
    the flag stepper. The source-level CT is `JForProgCT.RobustlyCTSafeJForProg`. -/
theorem loopLcmdLR_lsemLeakF_state_independent (w : Nat) (P : Lprog) (top : LLabel)
    (body : List LinstrR)
    (hbody : ∀ (s₁ s₂ : LstateF w), lsemLeakF P body s₁ = lsemLeakF P body s₂)
    (hsucc : ∀ s : LstateF w, (lsemStraightF P body s).isSome)
    (s₁ s₂ : LstateF w) :
    lsemLeakF P (loopLcmdLR w "NZ" top body) s₁ = lsemLeakF P (loopLcmdLR w "NZ" top body) s₂ := by
  rw [loopLcmdLR_expand]
  -- peel the leading `Llabel` (leak `[]`, step to nextPc), leaving the rest.
  have hpeel : ∀ s : LstateF w, lsemLeakF P
      ((.Llabel .internal top) :: body ++
        [.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0], .Lcond (.reg "NZ") top]) s
      = lsemLeakF P
        (body ++ [.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0],
          .Lcond (.reg "NZ") top]) s.nextPc := by
    intro s
    rw [List.cons_append, lsemLeakF_cons]
    simp only [linstrLeak, evalInstrF, isCmpZero, List.nil_append]
    rfl
  rw [hpeel s₁, hpeel s₂, lsemLeakF_append, lsemLeakF_append, hbody s₁.nextPc s₂.nextPc]
  -- the body always completes, so both runs land on a `some` state; the trailing
  -- `[CMP, Lcond]` leaks the constant `[.opn "CMP" …, .branch]` on both sides.
  obtain ⟨t1, h1⟩ := Option.isSome_iff_exists.mp (hsucc s₁.nextPc)
  obtain ⟨t2, h2⟩ := Option.isSome_iff_exists.mp (hsucc s₂.nextPc)
  rw [h1, h2]
  simp only [lsemLeakF_cons, linstrLeak]
  -- the CMP always steps (its `evalInstrF` is total), and the `Lcond` leaks a
  -- constant; so both sides' trailing leaks coincide regardless of `t1`/`t2`.
  rw [show evalInstrF P (.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0]) t1
      = some { prog := t1.prog.nextPc, zf := (evalOperand t1.prog.base (.reg "NZ") == 0) } from by
    simp only [evalInstrF, isCmpZero_cmp w]]
  rw [show evalInstrF P (.Lopn [.reg "NZ"] (withWidthTag w "CMP") [.reg "NZ", .imm 0]) t2
      = some { prog := t2.prog.nextPc, zf := (evalOperand t2.prog.base (.reg "NZ") == 0) } from by
    simp only [evalInstrF, isCmpZero_cmp w]]
  simp only []
  cases evalInstrF P (.Lcond (.reg "NZ") top)
    { prog := t1.prog.nextPc, zf := (evalOperand t1.prog.base (.reg "NZ") == 0) } <;>
  cases evalInstrF P (.Lcond (.reg "NZ") top)
    { prog := t2.prog.nextPc, zf := (evalOperand t2.prog.base (.reg "NZ") == 0) } <;>
  simp only [lsemLeakF_nil, List.append_nil]

/-! ## 9. The combined GAP-1+GAP-2 capstone: literal loop is correct AND
constant-time, AND its value tie is `JForProg.denote`. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT (RobustlyCTSafeJForProg)

/-- **Combined capstone (`correct ∧ value-tie ∧ robust`) over the LITERAL emitted
    counted loop.** For the `reg w` `JForProg p` with `p.n = c + 1`, body emission
    `spec` (per-iteration transformer `= valBodyStep bodyRun`, the value-encoded
    source step; `bodyRun` the functional runner with `StepAgrees`), public trip
    count (`hterm`), state-independent body leak (`hLeak`), and total body
    (`hSucc`):

    1. *(correct + value tie)* the `lsemFuelF` trace over the **literal**
       `loopProgF` (the `LprogControlFlow.loopLcmd` projection WITH the flag-`CMP`)
       from the loop entry halts, and the halt accumulator register `"acc"`
       **decodes to `JForProg.denote (decodeAcc sb)`** — the source loop's
       `n`-fold denotation; and
    2. *(robust / constant-time)* the loop's flag-threaded leak `lsemLeakF` (which
       steps the literal `CMP` and the back-edge `Lcond`) is the **same from any
       two states** — the back-edge `Lcond NZ` reads the `zf` the public-counter
       `CMP` set, leaking a state-independent `branch`; the body and `CMP` leak
       only syntax. The public trip count `c + 1` is the loop bound
       (vartime policy); the source-level CT is `RobustlyCTSafeJForProg p` (carried
       through). No `JasminIRToX86` edge, no `jasminc_preserves_ct`. -/
theorem jforprog_literal_loop_correct_and_robust {w : Nat} (fn : String) (top : LLabel)
    {body : List LinstrR} (spec : LoopBodySpec w body) (hnocmp : BodyNoCmp body)
    (sb : Lstate w) (zf : Bool) (c : Nat) (hterm : LoopTerminatesIn spec sb c)
    (p : JForProg (.reg w)) (hn : p.n = c + 1) {bodyRun : BodyRunner (.reg w)}
    (hStep : StepAgrees p bodyRun) (hbodyStep : spec.bodyStep = valBodyStep bodyRun)
    (P : Lprog)
    (hLeak : ∀ (s₁ s₂ : LstateF w), lsemLeakF P body s₁ = lsemLeakF P body s₂)
    (hSucc : ∀ s : LstateF w, (lsemStraightF P body s).isSome)
    (hCT : RobustlyCTSafeJForProg p) :
    -- (1) functional + value tie
    (∃ t : LstateF w,
      lsemFuelF (loopProgF w fn top body) ((c + 1) * (body.length + 2) + 1)
          (LstateF.mk (LstateP.mk (Lstate.mk sb.lvm sb.lmem 0) fn) zf) = some t
      ∧ decodeAcc t.prog.base = p.denote (decodeAcc sb))
    ∧
    -- (2) robust / constant-time over the literal CMP-carrying loop
    (∀ s₁ s₂ : LstateF w,
      lsemLeakF P (loopLcmdLR w "NZ" top body) s₁ = lsemLeakF P (loopLcmdLR w "NZ" top body) s₂) := by
  refine ⟨jforprog_loop_lsem_correct_and_robust fn top spec hnocmp sb zf c hterm p hn hStep
    hbodyStep, ?_⟩
  -- the source-level public-counter CT (`hCT`) realises the program-level
  -- state-independent leak; `hCT` witnesses the back-edge tests a public counter.
  have _ : RobustlyCTSafeJForProg p := hCT
  exact fun s₁ s₂ => loopLcmdLR_lsemLeakF_state_independent w P top body hLeak hSucc s₁ s₂

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoopFlag
