/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.VC.Core
public import CatCrypt.Crypto.SecureCompilation.SepLogic.AddrRunSafe

/-!
# The address machine in `RunM`

`AM := RunM (LstateA × Bool) (List Nat)` runs the address machine of
`JasminLsemAddrRun` with the trace of the program counters of the steps it takes.
`stepAM frame c` is the step `stepA` at the program counter and `runAM frame c n` the run
of at most `n` steps; `runAM_run` says that the state part of `runAM` is `runA`.

`execAM frame c k i` takes the step of the instruction `i` at the position `k` from a state
whose program counter is `k`, and `blockAM frame c k is` executes the instructions `is` from
the position `k` in turn. These programs carry the instruction in their syntax, so the
`@[spec]` triples of each instruction shape apply to them by `mvcgen`; `runAM_of_block`
turns a halting run of a block whose instructions are those of the body into a run of
`runAM`.

## Main definitions

* `VC.AM`, `VC.stepI`, `VC.stepAM`, `VC.runAM`, `VC.execAM`, `VC.blockAM`.

## Main results

* `VC.runAM_run`: the state part of a run of `runAM` is `runA`.
* `VC.appendOnly_runAM`: a run of `runAM` only appends to the trace.
* `VC.runAM_of_block`: a halting run of a block of the body is a run of `runAM`.
* `VC.execAM_mov64_spec`, `VC.execAM_store64_spec`, `VC.execAM_load64_spec`,
  `VC.execAM_label_spec`, `VC.execAM_cond_spec`: the `@[spec]` triples of the instruction
  shapes.
* `VC.runAM_spec_of_inv`: the triple of a run from an invariant that every step preserves,
  a step from every non-halted state of the invariant, and a variant that every step
  decreases.
* `VC.runA_storeMoveBody_frame_vc`, `VC.storeMoveBody_sContract`: the frame property of
  `storeMoveBody` from a triple proved by `mvcgen`, and the contract of its run.
-/

@[expose] public section

set_option autoImplicit false
set_option mvcgen.warning false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic.VC

open Std.Do
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct?)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AMem read64 write64 InRange8
  write64_of_not_inRange)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe runSafe_of_stepInv)
open Footprinted

/-- Runs of the address machine that accumulate the program counters of their steps. -/
abbrev AM : Type → Type := RunM (LstateA × Bool) (List Nat)

/-- The postconditions of `AM`. -/
abbrev AMPost (α : Type) : Type :=
  PostCond α (.arg ((LstateA × Bool) × List Nat) (.except PUnit .pure))

set_option linter.auxLemma false in
/-- The weakest precondition of an `AM` program at a state is its postcondition at the result
    of the run, and the failure postcondition when the run fails. -/
theorem wp_apply_run {α : Type} (x : AM α) (Q : AMPost α) (st : (LstateA × Bool) × List Nat) :
    wp⟦x⟧ Q st =
      (match x.run st with
        | some (a, st') => Q.1 a st'
        | none => Q.2.1 PUnit.unit) := by
  simp only [wp, PredTrans.apply_pushArg, PredTrans.apply_pushOption, OptionT.run,
    Option.instWP._aux_1, Id.run, StateT.run]
  rcases x st with _ | ⟨a, st'⟩ <;> rfl

/-! ## The step of an instruction -/

/-- The step of the instruction `i` at the position `k` of the body `c`: the arms of `stepA`
    at the instruction `i` and the program counter `k`. -/
def stepI (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat) (i : LinstrR)
    (s : LstateA) (zf : Bool) : Option (LstateA × Bool) :=
  match i with
  | .Lopn ds o ss => fstepA frame (normA (.Lopn ds o ss), tagAt c k (.Lopn ds o ss)) s zf
  | .Llabel _ _ => some (s.setLpc (k + 1), zf)
  | .Lcond (.reg cc) l =>
      match condPol cc with
      | some pol =>
          if zf = pol then (labelAt c l).map fun p => (s.setLpc p, zf)
          else some (s.setLpc (k + 1), zf)
      | none => none
  | _ => none

/-- The step of the address machine is the step of the instruction at the program counter. -/
theorem stepA_eq_stepI (frame : String → Option (BitVec 64)) (c : Lcmd) (s : LstateA)
    (zf : Bool) : stepA frame c s zf =
      match c[s.reg.lpc]? with
      | some li => stepI frame c s.reg.lpc li.li_i s zf
      | none => none := by
  rcases h : c[s.reg.lpc]? with _ | ⟨ii, i⟩ <;> simp only [stepA, stepI, h]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _⟩ <;> rfl

/-- The return instruction has no step. -/
theorem stepI_ret (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat) (s : LstateA)
    (zf : Bool) : stepI frame c k .Lret s zf = none := rfl

/-! ## The step and the run -/

/-- The step of the address machine at the program counter, appending the program counter to
    the trace. -/
def stepAM (frame : String → Option (BitVec 64)) (c : Lcmd) : AM Unit := fun st =>
  (stepA frame c st.1.1 st.1.2).map fun p => ((), (p, st.2 ++ [st.1.1.reg.lpc]))

/-- The run of at most `n` steps of the address machine on the body `c`, failing when it has
    not halted after them. -/
def runAM (frame : String → Option (BitVec 64)) (c : Lcmd) : Nat → AM Unit
  | 0 => fun st => if haltedA c st.1.1 then some ((), st) else none
  | n + 1 => fun st =>
      if haltedA c st.1.1 then some ((), st) else (stepAM frame c >>= fun _ => runAM frame c n) st

/-- **The run in `RunM` is the run of the address machine.** The state part of a run of
    `runAM` is `runA`. -/
theorem runAM_run (frame : String → Option (BitVec 64)) (c : Lcmd) (n : Nat) (s : LstateA)
    (zf : Bool) (t : List Nat) :
    ((runAM frame c n).run ((s, zf), t)).map (fun r => r.2.1) = runA frame c n s zf := by
  induction n generalizing s zf t with
  | zero => simp only [runAM, runA, StateT.run]; split <;> rfl
  | succ n ih =>
    simp only [runAM, runA, StateT.run]
    split
    · rfl
    · simp only [bind, StateT.bind, stepAM]
      cases stepA frame c s zf with
      | none => rfl
      | some p => simpa [StateT.run] using ih p.1 p.2 _

/-- The step only appends to the trace. -/
theorem appendOnly_stepAM (frame : String → Option (BitVec 64)) (c : Lcmd) :
    AppendOnly (stepAM frame c) := by
  intro s t₀ a s' t h
  simp only [stepAM, StateT.run] at h ⊢
  cases hs : stepA frame c s.1 s.2 <;> simp_all

/-- The run started on the trace `t₀ ++ t₁` prefixes `t₀` to the trace of the run started on
    `t₁`. -/
theorem runAM_run_append (frame : String → Option (BitVec 64)) (c : Lcmd) (n : Nat)
    (s : LstateA × Bool) (t₀ t₁ : List Nat) :
    (runAM frame c n).run (s, t₀ ++ t₁) =
      ((runAM frame c n).run (s, t₁)).map fun r => (r.1, (r.2.1, t₀ ++ r.2.2)) := by
  induction n generalizing s t₁ with
  | zero =>
    simp only [runAM, StateT.run]
    split <;> rfl
  | succ n ih =>
    simp only [runAM, StateT.run]
    split
    · rfl
    · simp only [bind, StateT.bind, stepAM]
      cases stepA frame c s.1 s.2 with
      | none => rfl
      | some p => simpa [StateT.run] using ih p (t₁ ++ [s.1.reg.lpc])

/-- The run only appends to the trace. -/
theorem appendOnly_runAM (frame : String → Option (BitVec 64)) (c : Lcmd) (n : Nat) :
    AppendOnly (runAM frame c n) := by
  intro s t₀ a s' t h
  rw [← List.append_nil t₀, runAM_run_append, List.append_nil]
  exact (congrArg (Option.map _) h).trans rfl

/-! ## Instructions at known positions -/

/-- The step of the instruction `i` at the position `k`, from a state whose program counter is
    `k`; it fails at every other program counter. -/
def execAM (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat) (i : LinstrR) :
    AM Unit := fun st =>
  if st.1.1.reg.lpc = k then
    (stepI frame c k i st.1.1 st.1.2).map fun p => ((), (p, st.2 ++ [k]))
  else none

/-- The instructions `is` executed in turn from the position `k`. -/
def blockAM (frame : String → Option (BitVec 64)) (c : Lcmd) : Nat → List LinstrR → AM Unit
  | _, [] => pure ()
  | k, i :: is => do execAM frame c k i; blockAM frame c (k + 1) is

/-- **Blocks are runs.** If the instructions `is` are those of the body `c` from the position
    `k`, a run of the block from `k` that ends in a halted state is a run of `runAM` with as
    many steps as the block has instructions. -/
theorem runAM_of_block (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (is : List LinstrR) (k : Nat) (st st' : (LstateA × Bool) × List Nat),
      (∀ j (h : j < is.length), (c[k + j]?).map Linstr.li_i = some is[j]) →
      (blockAM frame c k is).run st = some ((), st') → haltedA c st'.1.1 = true →
      (runAM frame c is.length).run st = some ((), st') := by
  intro is
  induction is with
  | nil =>
    intro k st st' _ h hh
    simp only [blockAM, StateT.run, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [runAM, StateT.run, hh]
  | cons i is ih =>
    intro k st st' hc h hh
    simp only [blockAM, bind, StateT.bind, StateT.run, execAM] at h
    split at h
    · rename_i hpc
      cases hs : stepI frame c k i st.1.1 st.1.2 with
      | none => simp [hs] at h
      | some p =>
        simp only [hs, Option.map_some] at h
        obtain ⟨li, hli, hlii⟩ : ∃ li, c[k]? = some li ∧ li.li_i = i := by
          have h0 := hc 0 (by simp)
          simp only [Nat.add_zero, Option.map_eq_some_iff, List.getElem_cons_zero] at h0
          exact h0
        have hstep : stepA frame c st.1.1 st.1.2 = some p := by
          rw [stepA_eq_stepI, hpc, hli]
          simpa [hlii] using hs
        have hnh : haltedA c st.1.1 = false := by
          unfold haltedA
          rw [hpc, hli]
          rcases li with ⟨ii, li⟩
          cases li <;> first | rfl | (subst hlii; rw [stepI_ret] at hs; cases hs)
        have hc' : ∀ j (hj : j < is.length), (c[k + 1 + j]?).map Linstr.li_i = some is[j] :=
          fun j hj => by
            have h1 := hc (j + 1) (by simp only [List.length_cons]; omega)
            rw [show k + (j + 1) = k + 1 + j by omega] at h1
            simpa using h1
        have := ih (k + 1) _ _ hc' h hh
        simp only [List.length_cons, runAM, StateT.run, hnh, bind, StateT.bind, stepAM, hstep,
          Option.map_some, hpc]
        simpa [StateT.run] using this
    · simp at h

/-! ## Instruction shapes -/

/-- A triple of `execAM` from a step of `stepI` with the result `f` at every state that
    satisfies `P`. -/
theorem execAM_spec_of {frame : String → Option (BitVec 64)} {c : Lcmd} {k : Nat}
    {i : LinstrR} (P : LstateA × Bool → Prop) (f : LstateA × Bool → LstateA × Bool)
    (h : ∀ s zf, s.reg.lpc = k → P (s, zf) → stepI frame c k i s zf = some (f (s, zf)))
    (Q : AMPost Unit) :
    ⦃spred(fun st => ⌜st.1.1.reg.lpc = k ∧ P st.1⌝ ∧ Q.1 () (f st.1, st.2 ++ [k]))⦄
      execAM frame c k i ⦃Q⦄ := by
  intro st hst
  rw [wp_apply_run]
  obtain ⟨⟨hk, hP⟩, hQ⟩ := hst
  simp only [StateT.run, execAM, hk, ite_true, h _ _ hk hP, Option.map_some]
  exact hQ

/-- The step of a register-tagged `Lopn` on two register operands whose mnemonic is `MOV:64`,
    `STORE:64` or `LOAD:64` is `fstepA` at the register tag. -/
theorem stepI_lopn_reg (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat) (d x o : String)
    (ho : o = "MOV:64" ∨ o = "STORE:64" ∨ o = "LOAD:64") (s : LstateA) (zf : Bool) :
    stepI frame c k (.Lopn [.reg d] o [.reg x]) s zf =
      fstepA frame (.Lopn [.reg d] o [.reg x], .reg none) s zf := by
  simp only [stepI]
  rw [tagAt_of_ne (by simp [movImmStruct?])]
  rcases ho with rfl | rfl | rfl <;>
    (rw [tagA_lopn (by decide) (by decide), normA_of_caret_free (by decide)]; simp +decide [castTagW])

/-- The shape of a 64-bit move `MOV:64 n, S`: a store of `S` when `n` is a cell, a load into
    `n` when `S` is a cell, a register move otherwise. -/
def movOk (frame : String → Option (BitVec 64)) (n S : String) (st : LstateA × Bool) : Prop :=
  match cellParts? n with
  | some (B, _) => (st.1.reg.getW B 64).isSome ∧ (st.1.reg.getW S 64).isSome
  | none =>
      match cellParts? S with
      | some (B, _) => (st.1.reg.getW B 64).isSome
      | none => frame n = none ∧ frame S = none

/-- The result of the 64-bit move `MOV:64 n, S` (`movOk`). -/
def movNext (n S : String) (st : LstateA × Bool) : LstateA × Bool :=
  match cellParts? n with
  | some (B, off) =>
      ({ st.1 with
          reg := st.1.reg.nextPc
          mem := write64 st.1.mem ((st.1.reg.getW B 64).getD 0 + BitVec.ofNat 64 off)
            ((st.1.reg.getW S 64).getD 0) }, st.2)
  | none =>
      match cellParts? S with
      | some (B, off) =>
          ({ st.1 with reg := (st.1.reg.setReg n
              (read64 st.1.mem ((st.1.reg.getW B 64).getD 0 + BitVec.ofNat 64 off))).nextPc },
            st.2)
      | none => ({ st.1 with reg := (st.1.reg.setReg n (st.1.reg.lvm S).2).nextPc }, st.2)

/-- The step of the 64-bit move `MOV:64 n, S`. -/
theorem stepI_mov64 (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat) (n S : String)
    (s : LstateA) (zf : Bool) (h : movOk frame n S (s, zf)) :
    stepI frame c k (.Lopn [.reg n] "MOV:64" [.reg S]) s zf = some (movNext n S (s, zf)) := by
  rw [stepI_lopn_reg frame c k n S _ (Or.inl rfl)]
  unfold movOk at h
  unfold movNext
  rcases hn : cellParts? n with _ | ⟨B, off⟩ <;> simp only [hn] at h ⊢
  · rcases hS : cellParts? S with _ | ⟨B, off⟩ <;> simp only [hS] at h ⊢
    · obtain ⟨hfn, hfS⟩ := h
      simp +decide [fstepA, slotMov?_mov64 hn hS, hfn, hfS, regStepA,
        VIR.JasminLsemMemFlagNestJoin.fstepF, VIR.JasminLsemMemFlagGuard.cmpArgs?,
        VIR.JasminLsemMemFlagGuard.movRegArgs?, readReg, LstateM.setReg, LstateM.nextPc]
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
      rw [fstepA_movLdm frame hS hn hp]
      simp [hp]
  · obtain ⟨hB, hV⟩ := h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hB
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hV
    rw [fstepA_movStm frame hn hp hv]
    simp [hp, hv]

/-- **The 64-bit move.** `MOV:64 n, S` stores `S` into the cell `n`, loads the cell `S` into
    `n`, or moves `S` into `n`. -/
@[spec]
theorem execAM_mov64_spec (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat)
    (n S : String) (Q : AMPost Unit) :
    ⦃spred(fun st => ⌜st.1.1.reg.lpc = k ∧ movOk frame n S st.1⌝ ∧
        Q.1 () (movNext n S st.1, st.2 ++ [k]))⦄
      execAM frame c k (.Lopn [.reg n] "MOV:64" [.reg S]) ⦃Q⦄ :=
  execAM_spec_of _ _ (fun s zf _ h => stepI_mov64 frame c k n S s zf h) Q

/-- The base register of the cell name `n` (`cellParts?`). -/
def cellBaseName (n : String) : String := ((cellParts? n).getD ("", 0)).1

/-- The offset of the cell name `n` (`cellParts?`). -/
def cellOff (n : String) : Nat := ((cellParts? n).getD ("", 0)).2

/-- **The cell store.** `STORE:64 n, S`, `n` the cell `[B + off]`, writes the value of `S` to
    the address in `B` plus `off`. -/
@[spec]
theorem execAM_store64_spec (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat)
    (n S : String) (Q : AMPost Unit) :
    ⦃spred(fun st => ⌜st.1.1.reg.lpc = k ∧ ((cellParts? n).isSome ∧
        (st.1.1.reg.getW (cellBaseName n) 64).isSome ∧ (st.1.1.reg.getW S 64).isSome)⌝ ∧
        Q.1 () (({ st.1.1 with
          reg := st.1.1.reg.nextPc
          mem := write64 st.1.1.mem
            ((st.1.1.reg.getW (cellBaseName n) 64).getD 0 + BitVec.ofNat 64 (cellOff n))
            ((st.1.1.reg.getW S 64).getD 0) }, st.1.2), st.2 ++ [k]))⦄
      execAM frame c k (.Lopn [.reg n] "STORE:64" [.reg S]) ⦃Q⦄ :=
  execAM_spec_of (fun st => (cellParts? n).isSome ∧ (st.1.reg.getW (cellBaseName n) 64).isSome ∧
      (st.1.reg.getW S 64).isSome)
    (fun st => ({ st.1 with
      reg := st.1.reg.nextPc
      mem := write64 st.1.mem ((st.1.reg.getW (cellBaseName n) 64).getD 0 +
        BitVec.ofNat 64 (cellOff n)) ((st.1.reg.getW S 64).getD 0) }, st.2))
    (fun s zf _ ⟨hn, hB, hS⟩ => by
    obtain ⟨⟨B, off⟩, hn⟩ := Option.isSome_iff_exists.1 hn
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hB
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hS
    have hb : cellBaseName n = B := by simp [cellBaseName, hn]
    have ho : cellOff n = off := by simp [cellOff, hn]
    rw [hb] at hp
    rw [stepI_lopn_reg frame c k n S _ (Or.inr (Or.inl rfl)), fstepA_stm frame hn hp hv]
    simp [hb, ho, hp, hv]) Q

/-- **The cell load.** `LOAD:64 D, n`, `n` the cell `[B + off]`, writes the word at the
    address in `B` plus `off` to `D`. -/
@[spec]
theorem execAM_load64_spec (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat)
    (D n : String) (Q : AMPost Unit) :
    ⦃spred(fun st => ⌜st.1.1.reg.lpc = k ∧ ((cellParts? n).isSome ∧
        (st.1.1.reg.getW (cellBaseName n) 64).isSome)⌝ ∧
        Q.1 () (({ st.1.1 with reg := (st.1.1.reg.setReg D (read64 st.1.1.mem
          ((st.1.1.reg.getW (cellBaseName n) 64).getD 0 + BitVec.ofNat 64 (cellOff n)))).nextPc },
          st.1.2), st.2 ++ [k]))⦄
      execAM frame c k (.Lopn [.reg D] "LOAD:64" [.reg n]) ⦃Q⦄ :=
  execAM_spec_of (fun st => (cellParts? n).isSome ∧ (st.1.reg.getW (cellBaseName n) 64).isSome)
    (fun st => ({ st.1 with reg := (st.1.reg.setReg D (read64 st.1.mem
      ((st.1.reg.getW (cellBaseName n) 64).getD 0 + BitVec.ofNat 64 (cellOff n)))).nextPc }, st.2))
    (fun s zf _ ⟨hn, hB⟩ => by
    obtain ⟨⟨B, off⟩, hn⟩ := Option.isSome_iff_exists.1 hn
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hB
    have hb : cellBaseName n = B := by simp [cellBaseName, hn]
    have ho : cellOff n = off := by simp [cellOff, hn]
    rw [hb] at hp
    rw [stepI_lopn_reg frame c k D n _ (Or.inr (Or.inr rfl)), fstepA_ldm frame hn hp]
    simp [hb, ho, hp]) Q

/-- **The label.** A label moves the program counter to the next instruction. -/
@[spec]
theorem execAM_label_spec (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat)
    (lk : LabelKind) (l : LLabel) (Q : AMPost Unit) :
    ⦃spred(fun st => ⌜st.1.1.reg.lpc = k⌝ ∧
        Q.1 () ((st.1.1.setLpc (k + 1), st.1.2), st.2 ++ [k]))⦄
      execAM frame c k (.Llabel lk l) ⦃Q⦄ := by
  intro st hst
  rw [wp_apply_run]
  obtain ⟨hk, hQ⟩ := hst
  simp only [StateT.run, execAM, stepI, Option.map_some]
  rw [ite_eq_left (show st.1.1.reg.lpc = k from hk)]
  exact hQ

/-- **The conditional jump.** `Lcond cc l` on the condition `Z` or `NZ` moves the program
    counter to the label `l` when the zero flag has the polarity of `cc`, and to the next
    instruction otherwise. -/
@[spec]
theorem execAM_cond_spec (frame : String → Option (BitVec 64)) (c : Lcmd) (k : Nat)
    (cc : String) (l : LLabel) (Q : AMPost Unit) :
    ⦃spred(fun st => ⌜st.1.1.reg.lpc = k ∧ (condPol cc).isSome ∧
        (st.1.2 = (condPol cc).getD false → (labelAt c l).isSome)⌝ ∧
        Q.1 () ((if st.1.2 = (condPol cc).getD false then
            st.1.1.setLpc ((labelAt c l).getD 0) else st.1.1.setLpc (k + 1), st.1.2),
          st.2 ++ [k]))⦄
      execAM frame c k (.Lcond (.reg cc) l) ⦃Q⦄ :=
  execAM_spec_of (fun st => (condPol cc).isSome ∧
      (st.2 = (condPol cc).getD false → (labelAt c l).isSome))
    (fun st => (if st.2 = (condPol cc).getD false then st.1.setLpc ((labelAt c l).getD 0)
      else st.1.setLpc (k + 1), st.2))
    (fun s zf _ ⟨hc, hl⟩ => by
    obtain ⟨pol, hpol⟩ := Option.isSome_iff_exists.1 hc
    simp only [stepI, hpol, Option.getD_some] at hl ⊢
    split_ifs with hz
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hl hz)
      simp [hq]
    · simp) Q

/-! ## Runs from a step invariant -/

/-- **Runs from a step invariant.** Let `I` be preserved by every step, let every state of
    `I` that has not halted step, and let the variant `V` decrease at every step from `I`.
    From a state `s₀` of `I` with `V s₀ ≤ n` the run of at most `n` steps halts in a state
    satisfying `Q`, and every state a run of at most `n` steps steps from satisfies `P`
    (`runSafe_of_stepInv`). -/
theorem runAM_spec_of_inv {frame : String → Option (BitVec 64)} {c : Lcmd}
    {I : LstateA → Bool → Prop} {P : LstateA → Prop} {Q : LstateA × Bool → Prop}
    (V : LstateA → Bool → Nat)
    (hI : ∀ s zf s' zf', I s zf → stepA frame c s zf = some (s', zf') → I s' zf')
    (hprog : ∀ s zf, I s zf → haltedA c s = false → (stepA frame c s zf).isSome)
    (hV : ∀ s zf s' zf', I s zf → haltedA c s = false →
      stepA frame c s zf = some (s', zf') → V s' zf' < V s zf)
    (hQ : ∀ s zf, I s zf → haltedA c s = true → Q (s, zf))
    (hP : ∀ s zf, I s zf → P s) (n : Nat) (s₀ : LstateA × Bool) :
    ⦃fun st => ⌜st.1 = s₀ ∧ I s₀.1 s₀.2 ∧ V s₀.1 s₀.2 ≤ n⌝⦄ runAM frame c n
      ⦃⇓ _ st => ⌜Q st.1 ∧ RunSafe frame c P n s₀.1 s₀.2⌝⦄ := by
  have H : ∀ (n : Nat) (s : LstateA) (zf : Bool) (t : List Nat), I s zf → V s zf ≤ n →
      ∃ st', (runAM frame c n).run ((s, zf), t) = some ((), st') ∧ Q st'.1 := by
    intro n
    induction n with
    | zero =>
      intro s zf t hIs hVs
      cases hh : haltedA c s
      · obtain ⟨⟨s', zf'⟩, hs⟩ := Option.isSome_iff_exists.1 (hprog s zf hIs hh)
        have := hV s zf s' zf' hIs hh hs
        omega
      · exact ⟨((s, zf), t), by simp [runAM, StateT.run, hh], hQ s zf hIs hh⟩
    | succ n ih =>
      intro s zf t hIs hVs
      cases hh : haltedA c s
      · obtain ⟨⟨s', zf'⟩, hs⟩ := Option.isSome_iff_exists.1 (hprog s zf hIs hh)
        have hlt := hV s zf s' zf' hIs hh hs
        obtain ⟨st', h1, h2⟩ :=
          ih s' zf' (t ++ [s.reg.lpc]) (hI s zf s' zf' hIs hs) (by omega)
        refine ⟨st', ?_, h2⟩
        simp only [runAM, StateT.run, hh, bind, StateT.bind, stepAM, hs, Option.map_some]
        simpa [StateT.run] using h1
      · exact ⟨((s, zf), t), by simp [runAM, StateT.run, hh], hQ s zf hIs hh⟩
  refine (triple_iff_run _ _ _).2 ?_
  rintro ⟨s, t⟩ ⟨rfl, hI0, hV0⟩
  obtain ⟨st', h1, h2⟩ := H n s.1 s.2 t hI0 hV0
  exact ⟨(), st', h1, h2, runSafe_of_stepInv hP hI hI0⟩

/-! ## The pilot: a cell store followed by a register move -/

/-- The instructions of `storeMoveBody`. -/
def storeMoveInstrs : List LinstrR :=
  [.Lopn [.reg "mem.B.0"] "MOV:64" [.reg "V"], .Lopn [.reg "D"] "MOV:64" [.reg "S"]]

/-- The locations that `storeMoveBody` writes from a state whose `B` holds `p`: the program
    counter, `D`, and the word at `p`. -/
def storeMoveWrites (p : BitVec 64) : Set Loc :=
  insert Loc.pc (insert (Loc.reg "D") (wordLocs (p + BitVec.ofNat 64 0)))

/-- The 64-bit move into a cell is a store. -/
theorem movNext_store {n S B : String} {off : Nat} (hn : cellParts? n = some (B, off))
    {st : LstateA × Bool} {p v : BitVec 64} (hB : st.1.reg.getW B 64 = some p)
    (hS : st.1.reg.getW S 64 = some v) :
    movNext n S st = ({ st.1 with
      reg := st.1.reg.nextPc
      mem := write64 st.1.mem (p + BitVec.ofNat 64 off) v }, st.2) := by
  simp [movNext, hn, hB, hS]

/-- The 64-bit move between names that are no cells is a register move. -/
theorem movNext_move {n S : String} (hn : cellParts? n = none) (hS : cellParts? S = none)
    (st : LstateA × Bool) :
    movNext n S st =
      ({ st.1 with reg := (st.1.reg.setReg n (st.1.reg.lvm S).2).nextPc }, st.2) := by
  simp [movNext, hn, hS]

/-- The store of `storeMoveBody` followed by its register move keeps every location outside
    `storeMoveWrites`. -/
theorem agreeOn_storeMove (s : LstateA) (zf : Bool) (p v : BitVec 64) :
    AgreeOn (storeMoveWrites p)ᶜ (s, zf)
      ({ reg := (s.reg.nextPc.setReg "D" (s.reg.nextPc.lvm "S").2).nextPc,
         mem := write64 s.mem (p + BitVec.ofNat 64 0) v, cf := s.cf, of := s.of }, zf) := by
  intro l hl
  simp only [storeMoveWrites, Set.mem_compl_iff, Set.mem_insert_iff, not_or] at hl
  obtain ⟨hpc, hD, hw⟩ := hl
  cases l with
  | reg r =>
    show s.reg.lvm r = (s.reg.nextPc.setReg "D" (s.reg.nextPc.lvm "S").2).nextPc.lvm r
    simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg]
    rw [ite_eq_right fun h : r = "D" => hD (h ▸ rfl)]
  | pc => exact absurd rfl hpc
  | flag f => cases f <;> rfl
  | mem x =>
    show s.mem x = write64 s.mem (p + BitVec.ofNat 64 0) v x
    exact (write64_of_not_inRange _ _ _ _ fun hx => hw ⟨x, hx, rfl⟩).symm

/-- **The block of `storeMoveBody` by `mvcgen`.** From the first instruction, with `B` and `V`
    holding words, the two instructions end at the program counter `2`, keep every location
    outside `storeMoveWrites`, and append `[0, 1]` to the trace. -/
theorem blockAM_storeMoveBody_triple {p v : BitVec 64} (st₀ : (LstateA × Bool) × List Nat) :
    ⦃fun st => ⌜st = st₀ ∧ st₀.1.1.reg.lpc = 0 ∧ st₀.1.1.reg.getW "B" 64 = some p ∧
        st₀.1.1.reg.getW "V" 64 = some v⌝⦄
      blockAM (fun _ => none) storeMoveBody 0 storeMoveInstrs
      ⦃⇓ _ st => ⌜st.1.1.reg.lpc = 2 ∧ AgreeOn (storeMoveWrites p)ᶜ st₀.1 st.1 ∧
        st.2 = st₀.2 ++ [0, 1]⌝⦄ := by
  have hn : cellParts? "mem.B.0" = some ("B", 0) := by decide
  have hD : cellParts? "D" = none := by decide
  have hS : cellParts? "S" = none := by decide
  mvcgen [blockAM, storeMoveInstrs]
  rename_i st h
  obtain ⟨rfl, hpc, hB, hV⟩ := h
  refine ⟨⟨hpc, by simp [movOk, hn, hB, hV]⟩, ?_⟩
  mvcgen
  refine ⟨⟨by simp [movNext, hn, hpc], by simp [movOk, hD, hS]⟩, ?_⟩
  mvcgen
  rw [movNext_store hn hB hV, movNext_move hD hS]
  exact ⟨by simp [hpc], agreeOn_storeMove _ _ _ _, by simp⟩

/-- The triple of the run of two steps of `storeMoveBody`. -/
theorem runAM_storeMoveBody_triple {p v : BitVec 64} (st₀ : (LstateA × Bool) × List Nat) :
    ⦃fun st => ⌜st = st₀ ∧ st₀.1.1.reg.lpc = 0 ∧ st₀.1.1.reg.getW "B" 64 = some p ∧
        st₀.1.1.reg.getW "V" 64 = some v⌝⦄
      runAM (fun _ => none) storeMoveBody 2
      ⦃⇓ _ st => ⌜st.1.1.reg.lpc = 2 ∧ AgreeOn (storeMoveWrites p)ᶜ st₀.1 st.1 ∧
        st.2 = st₀.2 ++ [0, 1]⌝⦄ := by
  refine (triple_iff_run _ _ _).2 fun st hst => ?_
  obtain ⟨⟨⟩, st', hr, hq⟩ :=
    (triple_iff_run _ _ _).1 (blockAM_storeMoveBody_triple (p := p) (v := v) st₀) st hst
  refine ⟨(), st', runAM_of_block _ _ storeMoveInstrs 0 st st' ?_ hr ?_, hq⟩
  · intro j hj
    simp only [storeMoveInstrs, List.length_cons, List.length_nil] at hj
    rcases j with _ | _ | j
    · rfl
    · rfl
    · omega
  · simp [haltedA, hq.1, storeMoveBody]

/-- An array of words disjoint from the word at `p` is kept between states that agree outside
    `storeMoveWrites p`. -/
theorem arrPts_of_storeMove {p a : BitVec 64} {xs : List (BitVec (8 * 8))}
    (hd : Disjoint (arrAt 8 a xs).fp (⟨p + BitVec.ofNat 64 0, 8⟩ : Rng 64).toSet)
    {s t : LstateA × Bool} (hag : AgreeOn (storeMoveWrites p)ᶜ s t)
    (hR : (arrPts 8 a xs).holds s) : (arrPts 8 a xs).holds t := by
  refine (arrPts 8 a xs).supp _ _ (agreeOn_anti ?_ hag) hR
  intro l hl hw
  obtain ⟨x, hx, rfl⟩ := hl
  simp only [storeMoveWrites, Set.mem_insert_iff] at hw
  rcases hw with h | h | ⟨y, hy, hxy⟩
  · exact Loc.noConfusion h
  · exact Loc.noConfusion h
  · cases hxy
    exact Set.disjoint_left.1 hd hx hy

/-- **The frame property of `storeMoveBody` by `mvcgen`.** Two steps of `storeMoveBody` from
    the first instruction halt, and an array of words disjoint from the stored word holds
    after them. -/
theorem runA_storeMoveBody_frame_vc {s : LstateA} (zf : Bool) (hpc : s.reg.lpc = 0)
    {p v : BitVec 64} (hB : s.reg.getW "B" 64 = some p) (hV : s.reg.getW "V" 64 = some v)
    {a : BitVec 64} {xs : List (BitVec (8 * 8))}
    (hd : Disjoint (arrAt 8 a xs).fp (⟨p + BitVec.ofNat 64 0, 8⟩ : Rng 64).toSet)
    (hR : (arrPts 8 a xs).holds (s, zf)) :
    ∃ q, runA (fun _ => none) storeMoveBody 2 s zf = some q ∧ (arrPts 8 a xs).holds q := by
  obtain ⟨⟨⟩, st', hr, -, hag, -⟩ := (triple_iff_run _ _ _).1
    (runAM_storeMoveBody_triple (p := p) (v := v) ((s, zf), [])) _ ⟨rfl, hpc, hB, hV⟩
  refine ⟨st'.1, ?_, arrPts_of_storeMove hd hag hR⟩
  have h := runAM_run (fun _ => none) storeMoveBody 2 s zf []
  rw [show ((runAM (fun _ => none) storeMoveBody 2).run ((s, zf), [])) = some ((), st')
    from hr] at h
  exact h.symm

/-- The precondition of the contract of `storeMoveBody` at the words `(p, v)` of `B` and `V`:
    the program counter is `0`, `B` holds `p`, `V` holds `v`, and the array `xs` at `a`,
    disjoint from the word at `p`, lies in memory. -/
def storeMovePre (a : BitVec 64) (xs : List (BitVec (8 * 8))) (pv : BitVec 64 × BitVec 64) :
    SAssert (LstateA × Bool) Loc :=
  SAssert.conj (SAssert.pure (Disjoint (arrAt 8 a xs).fp
      (⟨pv.1 + BitVec.ofNat 64 0, 8⟩ : Rng 64).toSet))
    (SAssert.conj (pcPts 0) (SAssert.conj (regPts "B" ⟨64, pv.1⟩)
      (SAssert.conj (regPts "V" ⟨64, pv.2⟩) (arrPts 8 a xs))))

/-- **The contract of `storeMoveBody`.** The run of two steps meets the contract with the
    precondition `storeMovePre`, the array as postcondition, the write set
    `storeMoveWrites`, and the trace `[0, 1]`. -/
theorem storeMoveBody_sContract (a : BitVec 64) (xs : List (BitVec (8 * 8))) :
    SContract (fun s => runRel (runAM (fun _ => none) storeMoveBody ((fun _ => 2) s)) s)
      ({ pre := storeMovePre a xs, post := fun _ => arrPts 8 a xs,
         writes := fun pv _ => storeMoveWrites pv.1,
         pub := fun s₁ s₂ => (fun _ => () : LstateA × Bool → Unit) s₁ =
           (fun _ => () : LstateA × Bool → Unit) s₂ } :
        ContractSpec (LstateA × Bool) Loc (BitVec 64 × BitVec 64)) := by
  refine sContract_of_triple (runAM (fun _ => none) storeMoveBody) (fun _ => 2)
    (fun _ => ()) (fun _ => [0, 1]) fun pv s₀ hpre => ?_
  obtain ⟨hd, hpc, hB, hV, hR⟩ := hpre
  have hB' : s₀.1.reg.getW "B" 64 = some pv.1 := by
    unfold LstateN.getW
    rw [show s₀.1.reg.lvm "B" = ⟨64, pv.1⟩ from hB]
    rfl
  have hV' : s₀.1.reg.getW "V" 64 = some pv.2 := by
    unfold LstateN.getW
    rw [show s₀.1.reg.lvm "V" = ⟨64, pv.2⟩ from hV]
    rfl
  refine (triple_iff_run _ _ _).2 fun st hst => ?_
  subst hst
  obtain ⟨⟨⟩, st', hr, -, hag, htr⟩ := (triple_iff_run _ _ _).1
    (runAM_storeMoveBody_triple (p := pv.1) (v := pv.2) (s₀, ∅)) _ ⟨rfl, hpc, hB', hV'⟩
  exact ⟨(), st', hr, arrPts_of_storeMove hd hag hR, hag, by simpa using htr⟩

end CatCrypt.Crypto.SecureCompilation.SepLogic.VC
