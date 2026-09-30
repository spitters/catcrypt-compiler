/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakCT
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-!
# Constant time across an `Lprog` rewrite, checked run by run

A rewrite of the function bodies of an `Lprog` preserves constant time from
function entry (`LprogLeak.EntryCT`) in the `CTLeak` model `LprogLeakCT.ctLeak`
when a checker accepts every pair of source and rewritten body. The checker cuts
both bodies into maximal runs of `Lopn`/`Lalign` instructions and single other
instructions (`splitR`), and pairs the pieces in order. A pair is accepted when it
is one and the same single instruction, or when both pieces are runs and a
symbolic execution of the two runs from one symbolic start state (`symRun`)
shows

* every event of the rewritten run is an event of the source run, as a symbolic
  term over the start state;
* the rewritten run stops (an instruction that does not step in `lsemStep`) no
  later than it ends, or both runs complete and their final symbolic states have
  equal registers and memory.

Two source runs with equal leakage give every source event term equal values, so
the rewritten runs emit equal events; runs that complete end in states with the
store of the matching source states.

## Main results

* `symRun_sound`: the symbolic run describes the events and the final state of
  the concrete run from every state it holds for.
* `segCheck`, `bodyCheck`: the checker on a pair of runs and on a pair of bodies.
* `lprogLeak_run`: the leakage over a straight-line run is the run's events
  followed by the leakage from the state after it.
* `entryCT_of_bodyCheck`: if the two programs have the same functions and the
  checker accepts every pair of bodies, `EntryCT (ctLeak w) P pub` implies
  `EntryCT (ctLeak w) P' pub`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakTV

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust (stateStore lsemStep_stateStore)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakCT

deriving instance DecidableEq for LinstrR

/-! ## 1. Symbolic words and memories -/

mutual
/-- A symbolic word over the store at the start of a run. -/
inductive STerm where
  /-- The value of a name at the start. -/
  | init (r : String)
  /-- An immediate. -/
  | imm (v : Nat)
  /-- A one-source operation, named by its stripped mnemonic. -/
  | op1 (opn : String) (a : STerm)
  /-- A two-source operation, named by its stripped mnemonic. -/
  | op2 (opn : String) (a b : STerm)
  /-- A three-source operation, named by its stripped mnemonic. -/
  | op3 (opn : String) (a b c : STerm)
  /-- The word of region `b` at offset `sc · x` of memory `m`. -/
  | rd (b : String) (sc : Nat) (x : STerm) (m : SMem)
  /-- The word of region `b` at the constant offset `i` of memory `m`. -/
  | rdC (b : String) (i : Nat) (m : SMem)

/-- A symbolic memory: the memory at the start, updated by stores. -/
inductive SMem where
  /-- The memory at the start. -/
  | init
  /-- `m` with the word of region `b` at offset `sc · x` set to `v`. -/
  | st (b : String) (sc : Nat) (x v : STerm) (m : SMem)
end

deriving instance DecidableEq for STerm, SMem

variable {w : Nat}

mutual
/-- The value of a symbolic word, for the start store `V`, `M`. -/
def STerm.eval (V : String → BitVec w) (M : String → Int → BitVec w) : STerm → BitVec w
  | .init r => V r
  | .imm v => BitVec.ofNat w v
  | .op1 opn a => (applyOpn opn [a.eval V M]).getD 0
  | .op2 opn a b => (applyOpn opn [a.eval V M, b.eval V M]).getD 0
  | .op3 opn a b c => (applyOpn opn [a.eval V M, b.eval V M, c.eval V M]).getD 0
  | .rd b sc x m => m.eval V M b (Int.ofNat (sc * (x.eval V M).toNat))
  | .rdC b i m => m.eval V M b (Int.ofNat i)

/-- The value of a symbolic memory, for the start store `V`, `M`. -/
def SMem.eval (V : String → BitVec w) (M : String → Int → BitVec w) :
    SMem → String → Int → BitVec w
  | .init => M
  | .st b sc x v m => fun b' o =>
      if b' = b then
        (if o = Int.ofNat (sc * (x.eval V M).toNat) then v.eval V M else m.eval V M b' o)
      else m.eval V M b' o
end

/-- The stores of `m` to region `b`. -/
def SMem.only (b : String) : SMem → SMem
  | .init => .init
  | .st b' sc x v m => if b' = b then .st b' sc x v (m.only b) else m.only b

/-- The regions `m` stores to. -/
def SMem.bases : SMem → List String
  | .init => []
  | .st b _ _ _ m => b :: m.bases

theorem SMem.eval_only (V : String → BitVec w) (M : String → Int → BitVec w) (b : String)
    (o : Int) : ∀ m : SMem, (m.only b).eval V M b o = m.eval V M b o
  | .init => rfl
  | .st b' sc x v m => by
      have ih := SMem.eval_only V M b o m
      by_cases h : b' = b
      · subst h
        simp only [SMem.only, if_true, SMem.eval, ih]
      · simp only [SMem.only, h, if_false, SMem.eval, ih, Ne.symm h]

theorem SMem.eval_of_not_mem (V : String → BitVec w) (M : String → Int → BitVec w)
    (b : String) (o : Int) : ∀ m : SMem, b ∉ m.bases → m.eval V M b o = M b o
  | .init, _ => rfl
  | .st b' sc x v m, h => by
      simp only [SMem.bases, List.mem_cons, not_or] at h
      simp only [SMem.eval, h.1, if_false]
      exact SMem.eval_of_not_mem V M b o m h.2

/-! ## 2. Symbolic states and one step -/

/-- A symbolic state: a symbolic word per name, a symbolic memory, and the names
    written so far. -/
structure SSt where
  /-- The symbolic word of each name. -/
  regs : String → STerm
  /-- The symbolic memory. -/
  mem : SMem
  /-- The names written. -/
  wr : List String

/-- The symbolic state at the start of a run. -/
def SSt.start : SSt := ⟨STerm.init, .init, []⟩

/-- `ss` with name `d` set to `t`. -/
def SSt.set (ss : SSt) (d : String) (t : STerm) : SSt :=
  { ss with regs := fun r => if r = d then t else ss.regs r, wr := d :: ss.wr }

/-- Every name that is not written holds its start value. -/
def SSt.Good (ss : SSt) : Prop := ∀ r, r ∉ ss.wr → ss.regs r = .init r

theorem SSt.good_start : SSt.start.Good := fun _ _ => rfl

theorem SSt.Good.set {ss : SSt} (h : ss.Good) (d : String) (t : STerm) : (ss.set d t).Good := by
  intro r hr
  simp only [SSt.set, List.mem_cons, not_or] at hr ⊢
  rw [if_neg hr.1]
  exact h r hr.2

/-- A concrete state is described by a symbolic state, for the start store `V`,
    `M`. -/
def Holds (V : String → BitVec w) (M : String → Int → BitVec w) (ss : SSt) (s : Lstate w) :
    Prop :=
  (∀ r, s.lvm r = (ss.regs r).eval V M) ∧ s.lmem = ss.mem.eval V M

theorem holds_start (s : Lstate w) : Holds s.lvm s.lmem SSt.start s :=
  ⟨fun _ => rfl, rfl⟩

/-- The symbolic word of an operand. -/
def symOp (ss : SSt) : LOperand → STerm
  | .reg r => ss.regs r
  | .imm v => .imm v
  | .arr b i => .rdC b i (ss.mem.only b)
  | .arrIdx b x sc => .rd b sc (ss.regs x) (ss.mem.only b)

theorem symOp_eval {V : String → BitVec w} {M : String → Int → BitVec w} {ss : SSt}
    {s : Lstate w} (h : Holds V M ss s) (o : LOperand) :
    (symOp ss o).eval V M = evalOperand s o := by
  cases o with
  | reg r => simp only [symOp, evalOperand, h.1]
  | imm v => rfl
  | arr b i => simp only [symOp, STerm.eval, SMem.eval_only, evalOperand, h.2]
  | arrIdx b x sc => simp only [symOp, STerm.eval, SMem.eval_only, evalOperand, h.1, h.2]

theorem Holds.set {V : String → BitVec w} {M : String → Int → BitVec w} {ss : SSt}
    {s : Lstate w} (h : Holds V M ss s) (d : String) (t : STerm) (v : BitVec w)
    (ht : t.eval V M = v) : Holds V M (ss.set d t) ((s.setReg d v).nextPc) := by
  refine ⟨fun r => ?_, h.2⟩
  simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, SSt.set]
  split
  · exact ht.symm
  · exact h.1 r

theorem applyOpn_MOV (a : BitVec w) : applyOpn "MOV" [a] = some a := rfl

theorem applyOpn_MOVQ (a : BitVec w) : applyOpn "MOVQ" [a] = some a := rfl

/-- The symbolic step of an operation `d := opn(args)`. A `MOV` or `MOVQ` copies
    its source's word. -/
def symGen (ss : SSt) (d opn : String) (args : List STerm) : Option SSt :=
  match args with
  | [a] =>
      if stripWidthTag opn = "MOV" ∨ stripWidthTag opn = "MOVQ" then some (ss.set d a)
      else some (ss.set d (.op1 (stripWidthTag opn) a))
  | [a, b] => some (ss.set d (.op2 (stripWidthTag opn) a b))
  | [a, b, c] => some (ss.set d (.op3 (stripWidthTag opn) a b c))
  | _ => none

theorem symGen_sound {V : String → BitVec w} {M : String → Int → BitVec w} {ss ss' : SSt}
    {s : Lstate w} (h : Holds V M ss s) (d opn : String) (args : List STerm)
    (vals : List (BitVec w)) (hvals : args.map (STerm.eval V M) = vals) (v : BitVec w)
    (happ : applyOpn (stripWidthTag opn) vals = some v)
    (hg : symGen ss d opn args = some ss') : Holds V M ss' ((s.setReg d v).nextPc) := by
  match args, hg with
  | [a], hg =>
      simp only [List.map_cons, List.map_nil] at hvals
      subst hvals
      simp only [symGen] at hg
      split at hg
      · rename_i hm
        simp only [Option.some.injEq] at hg
        subst hg
        refine h.set d a v ?_
        rcases hm with hm | hm
        · rw [hm, applyOpn_MOV] at happ
          exact Option.some.inj happ
        · rw [hm, applyOpn_MOVQ] at happ
          exact Option.some.inj happ
      · simp only [Option.some.injEq] at hg
        subst hg
        exact h.set d _ v (by simp only [STerm.eval, happ, Option.getD_some])
  | [a, b], hg =>
      simp only [List.map_cons, List.map_nil] at hvals
      subst hvals
      simp only [symGen, Option.some.injEq] at hg
      subst hg
      exact h.set d _ v (by simp only [STerm.eval, happ, Option.getD_some])
  | [a, b, c], hg =>
      simp only [List.map_cons, List.map_nil] at hvals
      subst hvals
      simp only [symGen, Option.some.injEq] at hg
      subst hg
      exact h.set d _ v (by simp only [STerm.eval, happ, Option.getD_some])
  | [], hg => simp [symGen] at hg
  | _ :: _ :: _ :: _ :: _, hg => simp [symGen] at hg

/-- A state of width `w`. -/
def dflt (w : Nat) : Lstate w := { lvm := fun _ => 0 }

/-- The symbolic step of one instruction: `some none` when the instruction does
    not step from any state, `some (some ss')` for a step, `none` for an
    instruction outside the symbolic fragment. -/
def symStep (w : Nat) (ss : SSt) (i : LinstrR) : Option (Option SSt) :=
  if (lsemStep i (dflt w)).isNone then some none
  else
    match i with
    | .Lopn [.reg d] opn srcs =>
        match srcs with
        | .arrIdx b x sc :: rest =>
            if opn = "LOADIDX" then some (some (ss.set d (.rd b sc (ss.regs x) (ss.mem.only b))))
            else if opn = "STOREIDX" then
              match rest with
              | [v] => some (some { ss with mem := .st b sc (ss.regs x) (symOp ss v) ss.mem })
              | _ => none
            else (symGen ss d opn (srcs.map (symOp ss))).map some
        | _ => (symGen ss d opn (srcs.map (symOp ss))).map some
    | .Llabel _ _ => some (some ss)
    | .Lalign => some (some ss)
    | _ => none

theorem symStep_halt {ss : SSt} {i : LinstrR} (h : symStep w ss i = some none) (s : Lstate w) :
    lsemStep i s = none := by
  unfold symStep at h
  split at h
  · rename_i hn
    have hc := lsemStep_isSome_congr i s (dflt w)
    rw [Option.isNone_iff_eq_none] at hn
    rw [hn] at hc
    simpa using hc
  · split at h
    · split at h
      · split at h
        · simp at h
        · split at h
          · split at h <;> simp at h
          · simp at h
      · simp at h
    · simp at h
    · simp at h
    · simp at h

theorem symGen_step_sound {V : String → BitVec w} {M : String → Int → BitVec w} {ss ss' : SSt}
    {s s' : Lstate w} (hH : Holds V M ss s) (d opn : String) (srcs : List LOperand)
    (hs' : (match applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
      | some v => some ((s.setReg d v).nextPc)
      | none => none) = some s')
    (h : (symGen ss d opn (srcs.map (symOp ss))).map some = some (some ss')) :
    Holds V M ss' s' := by
  cases happ : applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
  | none => rw [happ] at hs'; cases hs'
  | some v =>
      rw [happ] at hs'
      simp only [Option.some.injEq] at hs'
      subst hs'
      cases hg : symGen ss d opn (srcs.map (symOp ss)) with
      | none => rw [hg] at h; cases h
      | some g =>
          rw [hg] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact symGen_sound hH d opn _ _
            (by simp only [List.map_map, Function.comp_def, symOp_eval hH]) v happ hg

theorem symStep_sound {V : String → BitVec w} {M : String → Int → BitVec w} {ss ss' : SSt}
    {i : LinstrR} (h : symStep w ss i = some (some ss')) {s : Lstate w}
    (hH : Holds V M ss s) : ∃ s', lsemStep i s = some s' ∧ Holds V M ss' s' := by
  unfold symStep at h
  split at h
  · simp at h
  · rename_i hn
    have hsome : (lsemStep i s).isSome := by
      rw [lsemStep_isSome_congr i s (dflt w)]
      exact Option.ne_none_iff_isSome.mp (by simpa using hn)
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨s', hs', ?_⟩
    split at h
    · rename_i d opn srcs
      split at h
      · rename_i b x sc rest
        simp only [lsemStep] at hs'
        split at h
        · rename_i hL
          simp only [hL, if_true, Option.some.injEq] at hs' h
          subst hs' h
          exact hH.set d _ _ (by simp only [STerm.eval, SMem.eval_only, ← hH.1 x, ← hH.2])
        · rename_i hL
          split at h
          · rename_i hS
            rw [if_neg hL, if_pos hS] at hs'
            split at h
            · rename_i v
              simp only [Option.some.injEq] at hs' h
              subst hs' h
              refine ⟨fun r => hH.1 r, ?_⟩
              funext b' o
              simp only [Lstate.lmem_nextPc, SMem.eval, ← hH.1 x, symOp_eval hH, ← hH.2]
            · simp at h
          · rename_i hS
            simp only [hL, hS, if_false] at hs'
            exact symGen_step_sound hH d opn _ hs' h
      · rename_i hnot
        rw [lsemStep_reg_srcs d opn srcs s (fun b x sc rest heq => hnot b x sc rest heq)] at hs'
        exact symGen_step_sound hH d opn _ hs' h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [lsemStep, Option.some.injEq] at hs'
      subst hs'
      exact ⟨hH.1, hH.2⟩
    · simp only [Option.some.injEq] at h
      subst h
      simp only [lsemStep, Option.some.injEq] at hs'
      subst hs'
      exact ⟨hH.1, hH.2⟩
    · simp at h

theorem symGen_good {ss g : SSt} {d opn : String} {args : List STerm}
    (h : symGen ss d opn args = some g) (hg : ss.Good) : g.Good := by
  unfold symGen at h
  split at h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; exact hg.set _ _)
  · simp only [Option.some.injEq] at h; subst h; exact hg.set _ _
  · simp only [Option.some.injEq] at h; subst h; exact hg.set _ _
  · simp at h

theorem symStep_good {ss ss' : SSt} {i : LinstrR} (h : symStep w ss i = some (some ss'))
    (hg : ss.Good) : ss'.Good := by
  unfold symStep at h
  split at h
  · simp at h
  · split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact hg.set _ _
        · split at h
          · split at h
            · simp only [Option.some.injEq] at h; subst h; exact hg
            · simp at h
          · obtain ⟨g, hg', hgg⟩ := Option.map_eq_some_iff.1 h
            simp only [Option.some.injEq] at hgg
            subst hgg
            exact symGen_good hg' hg
      · obtain ⟨g, hg', hgg⟩ := Option.map_eq_some_iff.1 h
        simp only [Option.some.injEq] at hgg
        subst hgg
        exact symGen_good hg' hg
    · simp only [Option.some.injEq] at h; subst h; exact hg
    · simp only [Option.some.injEq] at h; subst h; exact hg
    · simp at h

/-! ## 3. Events and runs -/

/-- A symbolic `CTLeak` event. -/
inductive SEv where
  /-- A constant event. -/
  | c (e : CTLeak)
  /-- The access of region `b` at offset `sc · x`. -/
  | idx (b : String) (sc : Nat) (x : STerm)
  deriving DecidableEq

/-- The value of a symbolic event. -/
def SEv.eval (V : String → BitVec w) (M : String → Int → BitVec w) : SEv → CTLeak
  | .c e => e
  | .idx b sc x => .addr b (Int.ofNat (sc * (x.eval V M).toNat))

/-- The event of an indexed access, constant when the index is an immediate. -/
def mkIdx (w : Nat) (b : String) (sc : Nat) : STerm → SEv
  | .imm v => .c (.addr b (Int.ofNat (sc * (BitVec.ofNat w v).toNat)))
  | x => .idx b sc x

theorem mkIdx_eval (V : String → BitVec w) (M : String → Int → BitVec w) (b : String)
    (sc : Nat) (x : STerm) :
    (mkIdx w b sc x).eval V M = .addr b (Int.ofNat (sc * (x.eval V M).toNat)) := by
  cases x <;> rfl

/-- The symbolic events of an operand. -/
def opEv (w : Nat) (ss : SSt) : LOperand → List SEv
  | .arr b i => [.c (.addr b (Int.ofNat i))]
  | .arrIdx b x sc => [mkIdx w b sc (ss.regs x)]
  | _ => []

/-- The symbolic events of an instruction. -/
def instrEv (w : Nat) (ss : SSt) : LinstrR → List SEv
  | .Lopn ds _ srcs => (ds ++ srcs).flatMap (opEv w ss)
  | _ => []

/-- An instruction of a straight-line run: an `Lopn` or an `Lalign`. -/
def straightOk : LinstrR → Bool
  | .Lopn _ _ _ => true
  | .Lalign => true
  | _ => false

theorem instrEv_eval {V : String → BitVec w} {M : String → Int → BitVec w} {ss : SSt}
    {s : Lstate w} (h : Holds V M ss s) {i : LinstrR} (hi : straightOk i = true) :
    (ctLeak w).ev s i = (instrEv w ss i).map (SEv.eval V M) := by
  cases i with
  | Lopn ds opn srcs =>
      simp only [ctLeak, instrLeak, instrEv, List.map_flatMap]
      refine List.flatMap_congr (fun o _ => ?_)
      cases o with
      | arrIdx b x sc => simp only [opLeak, opEv, List.map_cons, List.map_nil, mkIdx_eval, ← h.1 x]
      | arr b i => rfl
      | reg _ => rfl
      | imm _ => rfl
  | Lalign => rfl
  | _ => simp [straightOk] at hi

/-- The events of each step of a straight-line run, up to and including a step
    that fails. -/
def runEvs {ε : Type} (L : LeakFn w ε) : List LinstrR → Lstate w → List (List ε)
  | [], _ => []
  | i :: is, s => L.ev s i :: (match lsemStep i s with
      | some s' => runEvs L is s'
      | none => [])

/-- The symbolic run of a list of instructions: the symbolic events of each step,
    and the final symbolic state, or `none` in the second component when an
    instruction does not step. `none` for a list outside the symbolic fragment. -/
def symRun (w : Nat) : SSt → List LinstrR → Option (List (List SEv) × Option SSt)
  | ss, [] => some ([], some ss)
  | ss, i :: is =>
      match symStep w ss i with
      | none => none
      | some none => some ([instrEv w ss i], none)
      | some (some ss') =>
          match symRun w ss' is with
          | none => none
          | some (es, fin) => some (instrEv w ss i :: es, fin)

/-- **The symbolic run describes the concrete run.** From a state the symbolic
    state holds for, the events of each step are the values of the symbolic
    events; the concrete run fails when the symbolic run stops, and ends in a state
    the final symbolic state holds for otherwise. -/
theorem symRun_sound {V : String → BitVec w} {M : String → Int → BitVec w} :
    ∀ (is : List LinstrR) (ss : SSt) (es : List (List SEv)) (fin : Option SSt) (s : Lstate w),
      symRun w ss is = some (es, fin) → Holds V M ss s → (∀ i ∈ is, straightOk i = true) →
      runEvs (ctLeak w) is s = es.map (List.map (SEv.eval V M)) ∧
      (fin = none → lsemStraight is s = none) ∧
      (∀ ss', fin = some ss' → ∃ s', lsemStraight is s = some s' ∧ Holds V M ss' s')
  | [], ss, es, fin, s, h, hH, _ => by
      simp only [symRun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, by simp, fun ss' h' => ?_⟩
      simp only [Option.some.injEq] at h'
      subst h'
      exact ⟨s, rfl, hH⟩
  | i :: is, ss, es, fin, s, h, hH, hst => by
      have hi := hst i (List.mem_cons_self ..)
      simp only [symRun] at h
      cases hstep : symStep w ss i with
      | none => rw [hstep] at h; cases h
      | some r =>
          cases r with
          | none =>
              rw [hstep] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hn := symStep_halt hstep s
              refine ⟨?_, fun _ => ?_, fun ss' h' => by cases h'⟩
              · simp only [runEvs, hn, List.map_cons, List.map_nil, instrEv_eval hH hi]
              · simp only [lsemStraight_cons, hn]
          | some ss1 =>
              simp only [hstep] at h
              obtain ⟨s1, hs1, hH1⟩ := symStep_sound hstep hH
              cases hrest : symRun w ss1 is with
              | none => rw [hrest] at h; cases h
              | some p =>
                  obtain ⟨es', fin'⟩ := p
                  rw [hrest] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨ih1, ih2, ih3⟩ := symRun_sound is ss1 es' fin' s1 hrest hH1
                    (fun j hj => hst j (List.mem_cons_of_mem _ hj))
                  refine ⟨?_, ?_, ?_⟩
                  · simp only [runEvs, hs1, ih1, List.map_cons, instrEv_eval hH hi]
                  · intro hf
                    simp only [lsemStraight_cons, hs1]
                    exact ih2 hf
                  · intro ss' hf
                    simp only [lsemStraight_cons, hs1]
                    exact ih3 ss' hf

theorem symRun_good : ∀ (is : List LinstrR) (ss ss' : SSt) (es : List (List SEv)),
    symRun w ss is = some (es, some ss') → ss.Good → ss'.Good
  | [], ss, ss', es, h, hg => by
      simp only [symRun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, h⟩ := h
      subst h
      exact hg
  | i :: is, ss, ss', es, h, hg => by
      simp only [symRun] at h
      cases hstep : symStep w ss i with
      | none => rw [hstep] at h; cases h
      | some r =>
          cases r with
          | none => rw [hstep] at h; simp at h
          | some ss1 =>
              simp only [hstep] at h
              cases hrest : symRun w ss1 is with
              | none => rw [hrest] at h; cases h
              | some p =>
                  obtain ⟨es', fin'⟩ := p
                  rw [hrest] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨_, rfl⟩ := h
                  exact symRun_good is ss1 ss' es' hrest (symStep_good hstep hg)

/-! ## 4. The checker -/

/-- The final symbolic states of two runs agree: equal words on every name either
    run writes, and equal stores to every region either run stores to. -/
def finalEq (a b : SSt) : Bool :=
  (a.wr ++ b.wr).all (fun r => decide (a.regs r = b.regs r)) &&
    (a.mem.bases ++ b.mem.bases).all (fun x => decide (a.mem.only x = b.mem.only x))

theorem finalEq_regs {a b : SSt} (ha : a.Good) (hb : b.Good) (h : finalEq a b = true)
    (r : String) : a.regs r = b.regs r := by
  simp only [finalEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  by_cases hr : r ∈ a.wr ++ b.wr
  · exact h.1 r hr
  · simp only [List.mem_append, not_or] at hr
    rw [ha r hr.1, hb r hr.2]

theorem finalEq_mem {a b : SSt} (h : finalEq a b = true) (V : String → BitVec w)
    (M : String → Int → BitVec w) : a.mem.eval V M = b.mem.eval V M := by
  simp only [finalEq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  funext x o
  by_cases hx : x ∈ a.mem.bases ++ b.mem.bases
  · rw [← SMem.eval_only V M x o a.mem, ← SMem.eval_only V M x o b.mem, h.2 x hx]
  · simp only [List.mem_append, not_or] at hx
    rw [SMem.eval_of_not_mem V M x o a.mem hx.1, SMem.eval_of_not_mem V M x o b.mem hx.2]

/-- **The checker on a pair of runs.** Both are straight-line; the symbolic runs
    from one start state exist; every event of the second is an event of the
    first; and when the second completes, the first completes with equal final
    words and stores. -/
def segCheck (w : Nat) (a b : List LinstrR) : Bool :=
  a.all straightOk && b.all straightOk &&
    match symRun w SSt.start a, symRun w SSt.start b with
    | some (ea, fa), some (eb, fb) =>
        eb.flatten.all (fun t => decide (t ∈ ea.flatten)) &&
          match fb, fa with
          | none, _ => true
          | some sb, some sa => finalEq sa sb
          | some _, none => false
    | _, _ => false

theorem segCheck_spec {a b : List LinstrR} (h : segCheck w a b = true) :
    (∀ i ∈ a, straightOk i = true) ∧ (∀ i ∈ b, straightOk i = true) ∧
      ∃ ea fa eb fb, symRun w SSt.start a = some (ea, fa) ∧
        symRun w SSt.start b = some (eb, fb) ∧ (∀ t ∈ eb.flatten, t ∈ ea.flatten) ∧
        ∀ sb, fb = some sb → ∃ sa, fa = some sa ∧ finalEq sa sb = true := by
  unfold segCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨ha, hb⟩, h⟩ := h
  refine ⟨ha, hb, ?_⟩
  split at h
  · rename_i ea fa eb fb hra hrb
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨ea, fa, eb, fb, hra, hrb, h.1, fun sb hsb => ?_⟩
    subst hsb
    obtain ⟨_, h2⟩ := h
    split at h2
    · rename_i hfb; cases hfb
    · simp only [Option.some.injEq] at *
      subst_vars
      exact ⟨_, rfl, h2⟩
    · simp at h2
  · simp at h

/-- The pieces of a body: maximal straight-line runs and single other
    instructions, in order. -/
def splitR : List LinstrR → List (List LinstrR)
  | [] => []
  | i :: is =>
      if straightOk i then
        match splitR is with
        | (j :: js) :: rest =>
            if straightOk j then (i :: j :: js) :: rest else [i] :: (j :: js) :: rest
        | rest => [i] :: rest
      else [i] :: splitR is

theorem splitR_flatten : ∀ l : List LinstrR, (splitR l).flatten = l
  | [] => rfl
  | i :: is => by
      have ih := splitR_flatten is
      unfold splitR
      split
      · split
        · rename_i j js rest hsp
          rw [hsp] at ih
          split <;> simp_all
        · simp_all
      · simp [ih]

/-- A pair of pieces is accepted: one and the same single instruction, or two
    runs that `segCheck` accepts. -/
def segOK (w : Nat) (a b : List LinstrR) : Bool :=
  (decide (a = b) && a.length == 1) || segCheck w a b

/-- **The checker on a pair of bodies.** The two bodies have the same number of
    pieces, and each pair of pieces in order is accepted. -/
def bodyCheck (w : Nat) (src tgt : List LinstrR) : Bool :=
  (splitR src).length == (splitR tgt).length &&
    ((splitR src).zip (splitR tgt)).all (fun p => segOK w p.1 p.2)

theorem bodyCheck_forall₂ {src tgt : List LinstrR} (h : bodyCheck w src tgt = true) :
    List.Forall₂ (fun a b => segOK w a b = true) (splitR src) (splitR tgt) := by
  simp only [bodyCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hl, hz⟩ := h
  generalize splitR src = A at hl hz
  generalize splitR tgt = B at hl hz
  induction A generalizing B with
  | nil =>
      cases B with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp at hl
  | cons a A ih =>
      cases B with
      | nil => simp at hl
      | cons b B =>
          refine List.Forall₂.cons (hz (a, b) (by simp)) (ih B (by simpa using hl) ?_)
          intro p hp
          exact hz p (List.mem_cons_of_mem _ hp)

theorem splitR_ne_nil : ∀ (l : List LinstrR), ∀ a ∈ splitR l, a ≠ []
  | [] => by simp [splitR]
  | i :: is => by
      have ih := splitR_ne_nil is
      unfold splitR
      split
      · split
        · rename_i j js rest hsp
          rw [hsp] at ih
          split
          · intro a ha
            rcases List.mem_cons.1 ha with rfl | ha
            · simp
            · exact ih a (List.mem_cons_of_mem _ ha)
          · intro a ha
            rcases List.mem_cons.1 ha with rfl | ha
            · simp
            · exact ih a ha
        · intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · simp
          · exact ih a ha
      · intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · simp
        · exact ih a ha

/-! ## 5. Positions, labels and runs -/

/-- The position of the start of piece `k`. -/
def bd (segs : List (List LinstrR)) (k : Nat) : Nat := ((segs.take k).flatten).length

@[simp] theorem bd_zero (segs : List (List LinstrR)) : bd segs 0 = 0 := by simp [bd]

theorem bd_cons_succ (a : List LinstrR) (segs : List (List LinstrR)) (k : Nat) :
    bd (a :: segs) (k + 1) = a.length + bd segs k := by
  simp [bd]

theorem bd_succ (segs : List (List LinstrR)) (k : Nat) (hk : k < segs.length) :
    bd segs (k + 1) = bd segs k + segs[k].length := by
  unfold bd
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.flatten_append,
    List.length_append]
  simp

theorem bd_length (segs : List (List LinstrR)) : bd segs segs.length = segs.flatten.length := by
  simp [bd]

theorem bd_lt (segs : List (List LinstrR)) (hne : ∀ a ∈ segs, a ≠ []) :
    ∀ k k', k < k' → k' ≤ segs.length → bd segs k < bd segs k' := by
  intro k k' hkk' hk'
  induction k' with
  | zero => omega
  | succ j ih =>
      have hj : j < segs.length := by omega
      rw [bd_succ segs j hj]
      have hpos : 0 < segs[j].length :=
        List.length_pos_iff.2 (hne _ (List.getElem_mem hj))
      rcases Nat.lt_or_ge k j with h | h
      · have := ih h (by omega); omega
      · have : k = j := by omega
        subst this; omega

theorem bd_inj (segs : List (List LinstrR)) (hne : ∀ a ∈ segs, a ≠ []) {k k' : Nat}
    (hk : k ≤ segs.length) (hk' : k' ≤ segs.length) (h : bd segs k = bd segs k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hl | he | hg
  · have := bd_lt segs hne k k' hl hk'; omega
  · exact he
  · have := bd_lt segs hne k' k hg hk; omega

theorem flatten_split (segs : List (List LinstrR)) (k : Nat) (hk : k < segs.length) :
    segs.flatten = (segs.take k).flatten ++ segs[k] ++ (segs.drop (k + 1)).flatten := by
  conv_lhs => rw [← List.take_append_drop k segs, List.drop_eq_getElem_cons hk]
  rw [List.flatten_append, List.flatten_cons, List.append_assoc]

/-- Pieces related for label resolution: one and the same single instruction, or
    two pieces without a label. -/
def SegL (a b : List LinstrR) : Prop :=
  (a = b ∧ a.length = 1) ∨
    ((∀ lbl, ∀ x ∈ a, isLabel lbl x = false) ∧ (∀ lbl, ∀ x ∈ b, isLabel lbl x = false))

theorem SegL.symm {a b : List LinstrR} (h : SegL a b) : SegL b a := by
  rcases h with ⟨rfl, h⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨hb, ha⟩

theorem isLabel_of_straightOk {x : LinstrR} (h : straightOk x = true) (lbl : LLabel) :
    isLabel lbl x = false := by
  cases x <;> simp_all [straightOk, isLabel]

theorem segL_of_segOK {a b : List LinstrR} (h : segOK w a b = true) : SegL a b := by
  simp only [segOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · obtain ⟨ha, hb, -⟩ := segCheck_spec h
    exact Or.inr ⟨fun lbl x hx => isLabel_of_straightOk (ha x hx) lbl,
      fun lbl x hx => isLabel_of_straightOk (hb x hx) lbl⟩

theorem forall₂_mono {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hRS _ _ h) (forall₂_mono hRS t)

theorem forall₂_swap {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ (fun b a => R a b) l₂ l₁
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h (forall₂_swap t)

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [forall₂_length t]

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ (k : Nat) (h₁ : k < l₁.length) (h₂ : k < l₂.length), R l₁[k] l₂[k]
  | _, _, .nil, k, h₁, _ => absurd h₁ (by simp)
  | _, _, .cons h t, 0, _, _ => h
  | _, _, .cons _ t, k + 1, h₁, h₂ =>
      forall₂_getElem t k (by simpa using h₁) (by simpa using h₂)

/-- **Label resolution through related pieces.** A label found in the
    concatenation of `A` is the single instruction of a piece `k`, and the
    concatenation of `B` resolves it to the start of its piece `k`. -/
theorem findLabel_segsL (lbl : LLabel) :
    ∀ (A B : List (List LinstrR)), List.Forall₂ SegL A B →
      ∀ pc, findLabel lbl A.flatten = some pc →
        ∃ k, k < A.length ∧ pc = bd A k ∧ findLabel lbl B.flatten = some (bd B k) ∧
          bd A (k + 1) = bd A k + 1 ∧ bd B (k + 1) = bd B k + 1 := by
  intro A B h
  induction h with
  | nil => intro pc hpc; simp [findLabel] at hpc
  | @cons a b A B hab _ ih =>
      intro pc hpc
      simp only [findLabel, List.flatten_cons, List.findIdx?_append] at hpc ⊢
      rcases hab with ⟨rfl, hlen⟩ | ⟨ha, hb⟩
      · obtain ⟨x, rfl⟩ : ∃ x, a = [x] := by
          match a, hlen with
          | [x], _ => exact ⟨x, rfl⟩
        by_cases hx : isLabel lbl x = true
        · simp only [List.findIdx?_singleton, hx, if_true, Option.some_or,
            Option.some.injEq] at hpc ⊢
          subst hpc
          exact ⟨0, by simp, by simp, by simp, by simp [bd_cons_succ], by simp [bd_cons_succ]⟩
        · simp only [Bool.not_eq_true] at hx
          simp only [List.findIdx?_singleton, hx, Bool.false_eq_true, if_false, Option.none_or,
            List.length_singleton] at hpc ⊢
          obtain ⟨pc', hpc', rfl⟩ := Option.map_eq_some_iff.1 hpc
          obtain ⟨k, hk, rfl, hB, hA1, hB1⟩ := ih pc' hpc'
          simp only [findLabel] at hB
          refine ⟨k + 1, by simpa using hk, by simp [bd_cons_succ]; omega, ?_, ?_, ?_⟩
          · rw [hB]; simp [bd_cons_succ]; omega
          · simp only [bd_cons_succ, List.length_singleton, hA1]; omega
          · simp only [bd_cons_succ, List.length_singleton, hB1]; omega
      · have hna : a.findIdx? (isLabel lbl) = none :=
          List.findIdx?_eq_none_iff.2 (by simpa using ha lbl)
        have hnb : b.findIdx? (isLabel lbl) = none :=
          List.findIdx?_eq_none_iff.2 (by simpa using hb lbl)
        rw [hna, Option.none_or] at hpc
        rw [hnb, Option.none_or]
        obtain ⟨pc', hpc', rfl⟩ := Option.map_eq_some_iff.1 hpc
        obtain ⟨k, hk, rfl, hB, hA1, hB1⟩ := ih pc' hpc'
        simp only [findLabel] at hB
        refine ⟨k + 1, by simpa using hk, by simp [bd_cons_succ]; omega, ?_, ?_, ?_⟩
        · rw [hB]; simp [bd_cons_succ]; omega
        · simp only [bd_cons_succ, hA1]; omega
        · simp only [bd_cons_succ, hB1]; omega

theorem runEvs_length_le {ε : Type} (L : LeakFn w ε) :
    ∀ (is : List LinstrR) (s : Lstate w), (runEvs L is s).length ≤ is.length
  | [], _ => le_refl _
  | i :: is, s => by
      simp only [runEvs, List.length_cons]
      split
      · have := runEvs_length_le L is ‹_›; omega
      · simp

theorem isStraightLine_of_straightOk {i : LinstrR} (h : straightOk i = true) :
    IsStraightLine i = true := by
  cases i <;> simp_all [straightOk, IsStraightLine]

/-- **The leakage over a straight-line run.** When the instructions at `pre, pre+1,
    …` of the body are the straight-line run `runR`, the leakage from the start of
    the run with fuel `n` is the events of its first `n` steps, followed, when the
    run completes, by the leakage from the state after it with the remaining fuel. -/
theorem lprogLeak_run {ε : Type} (L : LeakFn w ε) (P : Lprog) (fn : String)
    (bodyR : List LinstrR)
    (Hfetch : ∀ u : LstateP w, u.lfn = fn → findInstr P u = bodyR[u.base.lpc]?) :
    ∀ (runR pre post : List LinstrR), bodyR = pre ++ runR ++ post →
      (∀ i ∈ runR, straightOk i = true) →
      ∀ (s : LstateP w), s.lfn = fn → s.base.lpc = pre.length → ∀ n,
        lprogLeak L P n s = ((runEvs L runR s.base).take n).flatten ++
          (match lsemStraight runR s.base with
           | some b => lprogLeak L P (n - runR.length) ⟨b, fn⟩
           | none => []) := by
  intro runR
  induction runR with
  | nil =>
      intro pre post _ _ s hfn _ n
      obtain ⟨sb, sfn⟩ := s
      simp only at hfn
      subst hfn
      simp [runEvs]
  | cons i is ih =>
      intro pre post hbody hst s hfn hpc n
      have hi := hst i (List.mem_cons_self ..)
      have hfetch : findInstr P s = some i := by
        rw [Hfetch s hfn, hpc, hbody, List.append_assoc, List.getElem?_append_right (le_refl _)]
        simp
      cases n with
      | zero =>
          simp only [lprogLeak_zero, List.take_zero, List.flatten_nil, List.nil_append]
          split <;> simp
      | succ m =>
          rw [lprogLeak_succ_of_findInstr L P m hfetch,
            evalInstrP_straightLine P i s (isStraightLine_of_straightOk hi)]
          cases hs : lsemStep i s.base with
          | none =>
              simp [runEvs, hs, lsemStraight_cons]
          | some s1 =>
              have hpc1 : s1.lpc = (pre ++ [i]).length := by
                rw [lsemStep_lpc_succ i _ _ (isStraightLine_of_straightOk hi) hs, hpc]
                simp
              have key := ih (pre ++ [i]) post (by rw [hbody]; simp)
                (fun j hj => hst j (List.mem_cons_of_mem _ hj)) ⟨s1, fn⟩ rfl hpc1 m
              simp only [Option.map_some, runEvs, hs, List.take_succ_cons, List.flatten_cons,
                lsemStraight_cons, List.length_cons, List.append_assoc]
              have hs' : ({ s with base := s1 } : LstateP w) = ⟨s1, fn⟩ := by
                obtain ⟨sb, sfn⟩ := s
                simp only at hfn
                subst hfn
                rfl
              rw [hs', key]
              congr 2
              dsimp only
              cases lsemStraight is s1 <;> simp [Nat.add_sub_add_right]

/-! ## 6. The simulation -/

theorem store_parts {s t : Lstate w} (h : stateStore s = stateStore t) :
    s.lvm = t.lvm ∧ s.lmem = t.lmem := by
  simpa [stateStore] using h

theorem ev_store {s t : Lstate w} (h : stateStore s = stateStore t) (i : LinstrR) :
    (ctLeak w).ev s i = (ctLeak w).ev t i :=
  (ctLeak w).congr s t i (store_parts h).2 (fun x _ => congrFun (store_parts h).1 x)

theorem store_of_final {V : String → BitVec w} {M : String → Int → BitVec w} {sa sb : SSt}
    {x y : Lstate w} (hx : Holds V M sa x) (hy : Holds V M sb y) (ha : sa.Good) (hb : sb.Good)
    (h : finalEq sa sb = true) : stateStore x = stateStore y := by
  simp only [stateStore, Prod.mk.injEq]
  refine ⟨funext fun r => ?_, ?_⟩
  · rw [hx.1, hy.1, finalEq_regs ha hb h r]
  · rw [hx.2, hy.2, finalEq_mem h]

theorem piece_fetch (segs : List (List LinstrR)) (k : Nat) (hk : k < segs.length) (o : Nat)
    (ho : o < segs[k].length) : segs.flatten[bd segs k + o]? = segs[k][o]? := by
  rw [flatten_split segs k hk, List.append_assoc, bd,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left ho]

section Sim

variable (P P' : Lprog)

/-- A source state and a target state at the start of piece `k` of function `fn`,
    with the same store; the checker accepts the two bodies of `fn`. -/
def Pos (fn : String) (k : Nat) (σ τ : LstateP w) : Prop :=
  ∃ fd fd' : Lfundef, getFundef P fn = some fd ∧ getFundef P' fn = some fd' ∧
    bodyCheck w (fd.lfd_body.map Linstr.li_i) (fd'.lfd_body.map Linstr.li_i) = true ∧
    k ≤ (splitR (fd.lfd_body.map Linstr.li_i)).length ∧
    σ.lfn = fn ∧ τ.lfn = fn ∧
    σ.base.lpc = bd (splitR (fd.lfd_body.map Linstr.li_i)) k ∧
    τ.base.lpc = bd (splitR (fd'.lfd_body.map Linstr.li_i)) k ∧
    stateStore σ.base = stateStore τ.base

/-- Two target states at the start of piece `k` of `fn`, related by `Pos` to two
    source states with equal leakage for every fuel. -/
def TVAt (fn : String) (k : Nat) (τ₁ τ₂ : LstateP w) : Prop :=
  ∃ σ₁ σ₂ : LstateP w, Pos P P' fn k σ₁ τ₁ ∧ Pos P P' fn k σ₂ τ₂ ∧
    ∀ m, lprogLeak (ctLeak w) P m σ₁ = lprogLeak (ctLeak w) P m σ₂

variable {P P'}

theorem tvAt_of_pos {fnA fnB : String} {kA kB : Nat} {σ₁ σ₂ τ₁ τ₂ : LstateP w}
    (h₁ : Pos P P' fnA kA σ₁ τ₁) (h₂ : Pos P P' fnB kB σ₂ τ₂) (hfn : σ₁.lfn = σ₂.lfn)
    (hpc : σ₁.base.lpc = σ₂.base.lpc)
    (hEq : ∀ m, lprogLeak (ctLeak w) P m σ₁ = lprogLeak (ctLeak w) P m σ₂) :
    TVAt P P' fnA kA τ₁ τ₂ := by
  obtain ⟨fd, fd', hfd, hfd', hbc, hk, hσ1, hτ1, hσ1pc, hτ1pc, hst1⟩ := h₁
  obtain ⟨fd₂, fd₂', hfd2, hfd2', hbc2, hk2, hσ2, hτ2, hσ2pc, hτ2pc, hst2⟩ := h₂
  have hf : fnB = fnA := hσ2.symm.trans (hfn.symm.trans hσ1)
  subst hf
  rw [hfd] at hfd2
  cases hfd2
  rw [hfd'] at hfd2'
  cases hfd2'
  have hkk : kA = kB :=
    bd_inj _ (splitR_ne_nil _) hk hk2 (by rw [← hσ1pc, ← hσ2pc, hpc])
  subst hkk
  exact ⟨σ₁, σ₂, ⟨fd, fd', hfd, hfd', hbc, hk, hσ1, hτ1, hσ1pc, hτ1pc, hst1⟩,
    ⟨fd, fd', hfd, hfd', hbc2, hk2, hσ2, hτ2, hσ2pc, hτ2pc, hst2⟩, hEq⟩

/-- A jump from a source state and from a target state with the same store: both
    succeed or both fail, and on success they reach the start of one piece of the
    target function. -/
theorem jump_pos
    (hnone : ∀ fn, getFundef P fn = none → getFundef P' fn = none)
    (hchk : ∀ fn fd, getFundef P fn = some fd → ∃ fd', getFundef P' fn = some fd' ∧
      bodyCheck w (fd.lfd_body.map Linstr.li_i) (fd'.lfd_body.map Linstr.li_i) = true)
    (g : String) (l : LLabel) (σ τ : LstateP w) (hst : stateStore σ.base = stateStore τ.base) :
    (evalJump P (g, l) σ).isSome = (evalJump P' (g, l) τ).isSome ∧
      ∀ σ' τ', evalJump P (g, l) σ = some σ' → evalJump P' (g, l) τ = some τ' →
        ∃ k, Pos P P' g k σ' τ' := by
  cases hg : getFundef P g with
  | none =>
      have hg' := hnone g hg
      simp [evalJump, hg, hg']
  | some fd =>
      obtain ⟨fd', hg', hbc⟩ := hchk g fd hg
      have hF : List.Forall₂ SegL (splitR (fd.lfd_body.map Linstr.li_i))
          (splitR (fd'.lfd_body.map Linstr.li_i)) :=
        forall₂_mono (fun a b h => segL_of_segOK h) (bodyCheck_forall₂ hbc)
      simp only [evalJump, hg, hg']
      cases hfl : findLabel l (fd.lfd_body.map Linstr.li_i) with
      | none =>
          cases hfl' : findLabel l (fd'.lfd_body.map Linstr.li_i) with
          | none => simp
          | some pc' =>
              exfalso
              have hF' := forall₂_mono (fun a b h => SegL.symm h) (forall₂_swap hF)
              obtain ⟨k, -, -, hA, -, -⟩ := findLabel_segsL l _ _ hF' pc'
                (by rw [splitR_flatten]; exact hfl')
              rw [splitR_flatten, hfl] at hA
              cases hA
      | some pc =>
          obtain ⟨k, hk, hpc, hB, hA1, hB1⟩ := findLabel_segsL l _ _ hF pc
            (by rw [splitR_flatten]; exact hfl)
          rw [splitR_flatten] at hB
          rw [hB]
          refine ⟨rfl, fun σ' τ' h1 h2 => ⟨k + 1, ?_⟩⟩
          simp only [Option.some.injEq] at h1 h2
          subst h1 h2
          refine ⟨fd, fd', hg, hg', hbc, hk, rfl, rfl, ?_, ?_, ?_⟩
          · simp only [LstateP.base_setcpc, hA1, hpc]
          · simp only [LstateP.base_setcpc, hB1]
          · simpa [stateStore] using hst

/-- One step of one and the same single instruction from a source state and a
    target state at the start of its piece: both succeed or both fail, and on
    success they are again at the start of a piece with the same store. -/
theorem step_pos
    (hnone : ∀ fn, getFundef P fn = none → getFundef P' fn = none)
    (hchk : ∀ fn fd, getFundef P fn = some fd → ∃ fd', getFundef P' fn = some fd' ∧
      bodyCheck w (fd.lfd_body.map Linstr.li_i) (fd'.lfd_body.map Linstr.li_i) = true)
    {fn : String} {fd fd' : Lfundef} (hfd : getFundef P fn = some fd)
    (hfd' : getFundef P' fn = some fd')
    (hbc : bodyCheck w (fd.lfd_body.map Linstr.li_i) (fd'.lfd_body.map Linstr.li_i) = true)
    {k : Nat} (hkA : k < (splitR (fd.lfd_body.map Linstr.li_i)).length)
    (hkB : k < (splitR (fd'.lfd_body.map Linstr.li_i)).length) {c : LinstrR}
    (hA : (splitR (fd.lfd_body.map Linstr.li_i))[k] = [c])
    (hB : (splitR (fd'.lfd_body.map Linstr.li_i))[k] = [c])
    {σ τ : LstateP w} (hσ : σ.lfn = fn) (hτ : τ.lfn = fn)
    (hσpc : σ.base.lpc = bd (splitR (fd.lfd_body.map Linstr.li_i)) k)
    (hτpc : τ.base.lpc = bd (splitR (fd'.lfd_body.map Linstr.li_i)) k)
    (hst : stateStore σ.base = stateStore τ.base) :
    (evalInstrP P c σ).isSome = (evalInstrP P' c τ).isSome ∧
      ∀ σ' τ', evalInstrP P c σ = some σ' → evalInstrP P' c τ = some τ' →
        ∃ fn2 k2, Pos P P' fn2 k2 σ' τ' := by
  have hA1 : bd (splitR (fd.lfd_body.map Linstr.li_i)) (k + 1) =
      bd (splitR (fd.lfd_body.map Linstr.li_i)) k + 1 := by
    rw [bd_succ _ k hkA, hA]; rfl
  have hB1 : bd (splitR (fd'.lfd_body.map Linstr.li_i)) (k + 1) =
      bd (splitR (fd'.lfd_body.map Linstr.li_i)) k + 1 := by
    rw [bd_succ _ k hkB, hB]; rfl
  have next : ∀ σ' τ' : LstateP w, σ'.lfn = fn → τ'.lfn = fn →
      σ'.base.lpc = σ.base.lpc + 1 → τ'.base.lpc = τ.base.lpc + 1 →
      stateStore σ'.base = stateStore τ'.base → Pos P P' fn (k + 1) σ' τ' := by
    intro σ' τ' h1 h2 h3 h4 h5
    exact ⟨fd, fd', hfd, hfd', hbc, hkA, h1, h2, by rw [h3, hσpc, hA1], by rw [h4, hτpc, hB1], h5⟩
  have straight : IsStraightLine c = true →
      (evalInstrP P c σ).isSome = (evalInstrP P' c τ).isSome ∧
        ∀ σ' τ', evalInstrP P c σ = some σ' → evalInstrP P' c τ = some τ' →
          ∃ fn2 k2, Pos P P' fn2 k2 σ' τ' := by
    intro hsl
    rw [evalInstrP_straightLine P c σ hsl, evalInstrP_straightLine P' c τ hsl]
    have hss := lsemStep_stateStore c hst
    refine ⟨?_, fun σ' τ' h1 h2 => ?_⟩
    · cases h1 : lsemStep c σ.base <;> cases h2 : lsemStep c τ.base <;> simp_all
    · obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.1 h1
      obtain ⟨b2, hb2, rfl⟩ := Option.map_eq_some_iff.1 h2
      rw [hb1, hb2] at hss
      refine ⟨fn, k + 1, next _ _ hσ hτ ?_ ?_ (Option.some.inj hss)⟩
      · exact lsemStep_lpc_succ c _ _ hsl hb1
      · exact lsemStep_lpc_succ c _ _ hsl hb2
  cases c with
  | Lopn ds opn ss => exact straight rfl
  | Llabel kk ll => exact straight rfl
  | Lalign => exact straight rfl
  | Lgoto d =>
      obtain ⟨g, l⟩ := d
      obtain ⟨h1, h2⟩ := jump_pos hnone hchk g l σ τ hst
      refine ⟨h1, fun σ' τ' e1 e2 => ?_⟩
      obtain ⟨k2, hk2⟩ := h2 σ' τ' e1 e2
      exact ⟨g, k2, hk2⟩
  | Lcond cnd l =>
      have hev : evalOperand σ.base cnd = evalOperand τ.base cnd := by
        obtain ⟨hv, hm⟩ := store_parts hst
        cases cnd <;> simp [evalOperand, hv, hm]
      simp only [evalInstrP, hev, hσ, hτ]
      by_cases hc : evalOperand τ.base cnd ≠ 0
      · simp only [hc, if_true, ne_eq, not_false_eq_true]
        obtain ⟨h1, h2⟩ := jump_pos hnone hchk fn l σ τ hst
        refine ⟨h1, fun σ' τ' e1 e2 => ?_⟩
        obtain ⟨k2, hk2⟩ := h2 σ' τ' e1 e2
        exact ⟨fn, k2, hk2⟩
      · simp only [hc, if_false]
        refine ⟨rfl, fun σ' τ' e1 e2 => ?_⟩
        simp only [Option.some.injEq] at e1 e2
        subst e1 e2
        exact ⟨fn, k + 1, next _ _ hσ hτ rfl rfl (by simpa [stateStore] using hst)⟩
  | Ligoto _ => simp [evalInstrP]
  | Lcall _ _ => simp [evalInstrP]
  | Lret => simp [evalInstrP]
  | LstoreLabel _ _ => simp [evalInstrP]
  | Lsyscall _ => simp [evalInstrP]

theorem match_zero_nil {ε : Type} (L : LeakFn w ε) (Q : Lprog) (fn : String)
    (o : Option (Lstate w)) :
    (match o with
     | some b => lprogLeak L Q 0 ⟨b, fn⟩
     | none => []) = [] := by
  cases o <;> rfl

/-- The simulation at fuel `n`, given it at every smaller fuel, by induction on
    the number of pieces left in the current function. -/
theorem tv_inner
    (hnone : ∀ fn, getFundef P fn = none → getFundef P' fn = none)
    (hchk : ∀ fn fd, getFundef P fn = some fd → ∃ fd', getFundef P' fn = some fd' ∧
      bodyCheck w (fd.lfd_body.map Linstr.li_i) (fd'.lfd_body.map Linstr.li_i) = true)
    (n : Nat)
    (IH : ∀ m < n, ∀ (fn : String) (k : Nat) (τ₁ τ₂ : LstateP w), TVAt P P' fn k τ₁ τ₂ →
      lprogLeak (ctLeak w) P' m τ₁ = lprogLeak (ctLeak w) P' m τ₂) :
    ∀ (d : Nat) (fn : String) (k : Nat) (τ₁ τ₂ : LstateP w), TVAt P P' fn k τ₁ τ₂ →
      (∀ fd, getFundef P fn = some fd → (splitR (fd.lfd_body.map Linstr.li_i)).length - k = d) →
      lprogLeak (ctLeak w) P' n τ₁ = lprogLeak (ctLeak w) P' n τ₂ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IHd =>
  intro fn k τ₁ τ₂ hT hd
  obtain ⟨σ₁, σ₂, hp1, hp2, hEq⟩ := hT
  obtain ⟨fd, fd', hfd, hfd', hbc, hk, hσ1, hτ1, hσ1pc, hτ1pc, hst1⟩ := hp1
  obtain ⟨fd₂, fd₂', hfd2, hfd2', -, -, hσ2, hτ2, hσ2pc, hτ2pc, hst2⟩ := hp2
  rw [hfd] at hfd2
  cases hfd2
  rw [hfd'] at hfd2'
  cases hfd2'
  have hdk := hd fd hfd
  have hF := bodyCheck_forall₂ hbc
  have hlen := forall₂_length hF
  set A := splitR (fd.lfd_body.map Linstr.li_i) with hAdef
  set B := splitR (fd'.lfd_body.map Linstr.li_i) with hBdef
  have HfS : ∀ u : LstateP w, u.lfn = fn → findInstr P u = A.flatten[u.base.lpc]? := by
    intro u hu
    rw [hAdef, splitR_flatten]
    simp only [findInstr, hu, hfd, List.getElem?_map]
  have HfT : ∀ u : LstateP w, u.lfn = fn → findInstr P' u = B.flatten[u.base.lpc]? := by
    intro u hu
    rw [hBdef, splitR_flatten]
    simp only [findInstr, hu, hfd', List.getElem?_map]
  by_cases hkk : k < A.length
  swap
  · have hkA : k = B.length := by omega
    have e1 : findInstr P' τ₁ = none := by
      rw [HfT τ₁ hτ1, hτ1pc, hkA, bd_length]
      exact List.getElem?_eq_none (le_refl _)
    have e2 : findInstr P' τ₂ = none := by
      rw [HfT τ₂ hτ2, hτ2pc, hkA, bd_length]
      exact List.getElem?_eq_none (le_refl _)
    rw [lprogLeak_of_findInstr_none _ _ _ e1, lprogLeak_of_findInstr_none _ _ _ e2]
  have hkB : k < B.length := by omega
  have hab := forall₂_getElem hF k hkk hkB
  simp only [segOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hab
  rcases hab with ⟨heqab, hl1⟩ | hsc
  · -- one and the same single instruction
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 hl1
    have hcB : B[k] = [c] := heqab ▸ hc
    have hfS : ∀ σ : LstateP w, σ.lfn = fn → σ.base.lpc = bd A k → findInstr P σ = some c := by
      intro σ h1 h2
      rw [HfS σ h1, h2, ← Nat.add_zero (bd A k), piece_fetch A k hkk 0 (by rw [hc]; simp), hc]
      rfl
    have hfT : ∀ τ : LstateP w, τ.lfn = fn → τ.base.lpc = bd B k → findInstr P' τ = some c := by
      intro τ h1 h2
      rw [HfT τ h1, h2, ← Nat.add_zero (bd B k), piece_fetch B k hkB 0 (by rw [hcB]; simp), hcB]
      rfl
    cases n with
    | zero => rfl
    | succ m =>
        have hf1 := hfS σ₁ hσ1 hσ1pc
        have hf2 := hfS σ₂ hσ2 hσ2pc
        obtain ⟨hev, hsome, hnext⟩ :=
          lprogLeak_split (ctLeak w) P hEq (hσ1.trans hσ2.symm) hf1 hf2
        rw [lprogLeak_succ_of_findInstr _ _ m (hfT τ₁ hτ1 hτ1pc),
          lprogLeak_succ_of_findInstr _ _ m (hfT τ₂ hτ2 hτ2pc),
          ← ev_store hst1 c, ← ev_store hst2 c, hev]
        congr 1
        obtain ⟨hs1, hr1⟩ :=
          step_pos hnone hchk hfd hfd' hbc hkk hkB hc hcB hσ1 hτ1 hσ1pc hτ1pc hst1
        obtain ⟨hs2, hr2⟩ :=
          step_pos hnone hchk hfd hfd' hbc hkk hkB hc hcB hσ2 hτ2 hσ2pc hτ2pc hst2
        cases e1 : evalInstrP P' c τ₁ with
        | none =>
            have e2 : evalInstrP P' c τ₂ = none := by
              rw [e1] at hs1
              rw [← Option.not_isSome_iff_eq_none, ← hs2, ← hsome, hs1]
              simp
            rw [e2]
        | some τ₁' =>
            obtain ⟨σ₁', e1s⟩ : ∃ σ₁', evalInstrP P c σ₁ = some σ₁' :=
              Option.isSome_iff_exists.1 (by rw [hs1, e1]; rfl)
            obtain ⟨σ₂', e2s⟩ : ∃ σ₂', evalInstrP P c σ₂ = some σ₂' :=
              Option.isSome_iff_exists.1 (by rw [← hsome, e1s]; rfl)
            obtain ⟨τ₂', e2⟩ : ∃ τ₂', evalInstrP P' c τ₂ = some τ₂' :=
              Option.isSome_iff_exists.1 (by rw [← hs2, e2s]; rfl)
            rw [e2]
            dsimp only
            obtain ⟨fnA, kA, hpA⟩ := hr1 σ₁' τ₁' e1s e1
            obtain ⟨fnB, kB, hpB⟩ := hr2 σ₂' τ₂' e2s e2
            obtain ⟨hlfn, hlpc, hEq'⟩ := hnext σ₁' σ₂' e1s e2s
            exact IH m (Nat.lt_succ_self m) fnA kA τ₁' τ₂'
              (tvAt_of_pos hpA hpB hlfn (hlpc (hσ1pc.trans hσ2pc.symm)) hEq')
  · -- two runs accepted by the symbolic check
    obtain ⟨haS, hbS, ea, fa, eb, fb, hra, hrb, hsub, hfin⟩ := segCheck_spec hsc
    have hrunS := lprogLeak_run (ctLeak w) P fn A.flatten HfS A[k] _ _
      (flatten_split A k hkk) haS
    have hrunT := lprogLeak_run (ctLeak w) P' fn B.flatten HfT B[k] _ _
      (flatten_split B k hkB) hbS
    have hpcS1 : σ₁.base.lpc = ((A.take k).flatten).length := hσ1pc
    have hpcS2 : σ₂.base.lpc = ((A.take k).flatten).length := hσ2pc
    have hpcT1 : τ₁.base.lpc = ((B.take k).flatten).length := hτ1pc
    have hpcT2 : τ₂.base.lpc = ((B.take k).flatten).length := hτ2pc
    obtain ⟨hES1, -, hSS1⟩ := symRun_sound A[k] SSt.start ea fa σ₁.base hra (holds_start _) haS
    obtain ⟨hES2, -, hSS2⟩ := symRun_sound A[k] SSt.start ea fa σ₂.base hra (holds_start _) haS
    obtain ⟨hET1, hNT1, hST1⟩ :=
      symRun_sound B[k] SSt.start eb fb τ₁.base hrb (holds_start _) hbS
    obtain ⟨hET2, hNT2, hST2⟩ :=
      symRun_sound B[k] SSt.start eb fb τ₂.base hrb (holds_start _) hbS
    have hF12 : (runEvs (ctLeak w) A[k] σ₁.base).flatten =
        (runEvs (ctLeak w) A[k] σ₂.base).flatten := by
      have h := hEq A[k].length
      rw [hrunS σ₁ hσ1 hpcS1, hrunS σ₂ hσ2 hpcS2,
        List.take_of_length_le (runEvs_length_le _ _ _),
        List.take_of_length_le (runEvs_length_le _ _ _), Nat.sub_self,
        match_zero_nil, match_zero_nil, List.append_nil, List.append_nil] at h
      exact h
    have hpt : ∀ t ∈ ea.flatten,
        t.eval σ₁.base.lvm σ₁.base.lmem = t.eval σ₂.base.lvm σ₂.base.lmem := by
      have h := hF12
      rw [hES1, hES2, ← List.map_flatten, ← List.map_flatten] at h
      exact List.map_inj_left.1 h
    have hvm1 := store_parts hst1
    have hvm2 := store_parts hst2
    have hRT : runEvs (ctLeak w) B[k] τ₁.base = runEvs (ctLeak w) B[k] τ₂.base := by
      rw [hET1, hET2]
      refine List.map_congr_left (fun l hl => List.map_congr_left (fun t ht => ?_))
      have hta := hsub t (List.mem_flatten.2 ⟨l, hl, ht⟩)
      rw [← hvm1.1, ← hvm1.2, ← hvm2.1, ← hvm2.2]
      exact hpt t hta
    rw [hrunT τ₁ hτ1 hpcT1 n, hrunT τ₂ hτ2 hpcT2 n, hRT]
    congr 1
    cases fb with
    | none => rw [hNT1 rfl, hNT2 rfl]
    | some sb =>
        obtain ⟨sa, rfl, hfe⟩ := hfin sb rfl
        obtain ⟨x₁, hx₁, hHx₁⟩ := hSS1 sa rfl
        obtain ⟨x₂, hx₂, hHx₂⟩ := hSS2 sa rfl
        obtain ⟨y₁, hy₁, hHy₁⟩ := hST1 sb rfl
        obtain ⟨y₂, hy₂, hHy₂⟩ := hST2 sb rfl
        have hga := symRun_good A[k] SSt.start sa ea hra SSt.good_start
        have hgb := symRun_good B[k] SSt.start sb eb hrb SSt.good_start
        have hHy₁' : Holds σ₁.base.lvm σ₁.base.lmem sb y₁ := by
          rw [hvm1.1, hvm1.2]; exact hHy₁
        have hHy₂' : Holds σ₂.base.lvm σ₂.base.lmem sb y₂ := by
          rw [hvm2.1, hvm2.2]; exact hHy₂
        have hs1 := store_of_final hHx₁ hHy₁' hga hgb hfe
        have hs2 := store_of_final hHx₂ hHy₂' hga hgb hfe
        have hEqx : ∀ m, lprogLeak (ctLeak w) P m ⟨x₁, fn⟩ = lprogLeak (ctLeak w) P m ⟨x₂, fn⟩ := by
          intro m
          have h := hEq (m + A[k].length)
          have l1 := runEvs_length_le (ctLeak w) A[k] σ₁.base
          have l2 := runEvs_length_le (ctLeak w) A[k] σ₂.base
          rw [hrunS σ₁ hσ1 hpcS1, hrunS σ₂ hσ2 hpcS2, hx₁, hx₂,
            List.take_of_length_le (by omega), List.take_of_length_le (by omega),
            Nat.add_sub_cancel, hF12] at h
          exact List.append_cancel_left h
        have hlx : ∀ (x : Lstate w) (σ : LstateP w), lsemStraight A[k] σ.base = some x →
            σ.base.lpc = bd A k → x.lpc = bd A (k + 1) := by
          intro x σ hx hpc
          rw [lsemStraight_lpc A[k] σ.base x
            (fun i hi => isStraightLine_of_straightOk (haS i hi)) hx, hpc, bd_succ A k hkk]
        have hly : ∀ (y : Lstate w) (τ : LstateP w), lsemStraight B[k] τ.base = some y →
            τ.base.lpc = bd B k → y.lpc = bd B (k + 1) := by
          intro y τ hy hpc
          rw [lsemStraight_lpc B[k] τ.base y
            (fun i hi => isStraightLine_of_straightOk (hbS i hi)) hy, hpc, bd_succ B k hkB]
        have hP1 : Pos P P' fn (k + 1) ⟨x₁, fn⟩ ⟨y₁, fn⟩ :=
          ⟨fd, fd', hfd, hfd', hbc, hkk, rfl, rfl, hlx x₁ σ₁ hx₁ hσ1pc, hly y₁ τ₁ hy₁ hτ1pc, hs1⟩
        have hP2 : Pos P P' fn (k + 1) ⟨x₂, fn⟩ ⟨y₂, fn⟩ :=
          ⟨fd, fd', hfd, hfd', hbc, hkk, rfl, rfl, hlx x₂ σ₂ hx₂ hσ2pc, hly y₂ τ₂ hy₂ hτ2pc, hs2⟩
        have hT' : TVAt P P' fn (k + 1) ⟨y₁, fn⟩ ⟨y₂, fn⟩ := ⟨_, _, hP1, hP2, hEqx⟩
        rw [hy₁, hy₂]
        dsimp only
        by_cases hb0 : B[k].length = 0
        · rw [hb0, Nat.sub_zero]
          exact IHd (d - 1) (by omega) fn (k + 1) _ _ hT'
            (fun fd2 h2 => by
              rw [hfd] at h2
              cases h2
              show A.length - (k + 1) = d - 1
              omega)
        · cases n with
          | zero => simp
          | succ n' => exact IH _ (by omega) fn (k + 1) _ _ hT'

/-- **The simulation.** Two target states related by `TVAt` have equal leakage for
    every fuel. -/
theorem tv_sim
    (hnone : ∀ fn, getFundef P fn = none → getFundef P' fn = none)
    (hchk : ∀ fn fd, getFundef P fn = some fd → ∃ fd', getFundef P' fn = some fd' ∧
      bodyCheck w (fd.lfd_body.map Linstr.li_i) (fd'.lfd_body.map Linstr.li_i) = true) :
    ∀ (n : Nat) (fn : String) (k : Nat) (τ₁ τ₂ : LstateP w), TVAt P P' fn k τ₁ τ₂ →
      lprogLeak (ctLeak w) P' n τ₁ = lprogLeak (ctLeak w) P' n τ₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro fn k τ₁ τ₂ hT
  obtain ⟨_, _, ⟨fd, _, hfd, -⟩, -, -⟩ := id hT
  exact tv_inner hnone hchk n IH _ fn k τ₁ τ₂ hT
    (fun fd2 h2 => by rw [hfd] at h2; cases h2; rfl)

end Sim

/-- **Constant time across a checked rewrite.** If `P'` has a function exactly
    where `P` has one and the checker accepts every pair of bodies, constant time
    from function entry in the `CTLeak` model transfers from `P` to `P'`. -/
theorem entryCT_of_bodyCheck (P P' : Lprog) (pub : LstateP w → LstateP w → Prop)
    (hnone : ∀ fn, getFundef P fn = none → getFundef P' fn = none)
    (hchk : ∀ fn fd, getFundef P fn = some fd → ∃ fd', getFundef P' fn = some fd' ∧
      bodyCheck w (fd.lfd_body.map Linstr.li_i) (fd'.lfd_body.map Linstr.li_i) = true)
    (h : EntryCT (ctLeak w) P pub) : EntryCT (ctLeak w) P' pub := by
  intro s₁ s₂ hp hfn h1 h2 n
  cases hg : getFundef P s₁.lfn with
  | none =>
      have hg' := hnone _ hg
      have e1 : findInstr P' s₁ = none := by simp [findInstr, hg']
      have e2 : findInstr P' s₂ = none := by simp [findInstr, ← hfn, hg']
      rw [lprogLeak_of_findInstr_none _ _ _ e1, lprogLeak_of_findInstr_none _ _ _ e2]
  | some fd =>
      obtain ⟨fd', hg', hbc⟩ := hchk _ fd hg
      refine tv_sim hnone hchk n s₁.lfn 0 s₁ s₂ ⟨s₁, s₂, ?_, ?_, h s₁ s₂ hp hfn h1 h2⟩
      · exact ⟨fd, fd', hg, hg', hbc, Nat.zero_le _, rfl, rfl, by simp [h1], by simp [h1], rfl⟩
      · exact ⟨fd, fd', hg, hg', hbc, Nat.zero_le _, hfn.symm, hfn.symm, by simp [h2],
          by simp [h2], rfl⟩

/-- `entryCT_of_bodyCheck` for a program whose functions are those of `P` with
    each body replaced by its image under `T`. -/
theorem entryCT_of_mapped (P P' : Lprog) (T : Lcmd → Lcmd) (pub : LstateP w → LstateP w → Prop)
    (hP' : ∀ fn, getFundef P' fn =
      (getFundef P fn).map (fun fd => { fd with lfd_body := T fd.lfd_body }))
    (hchk : ∀ fn fd, getFundef P fn = some fd →
      bodyCheck w (fd.lfd_body.map Linstr.li_i) ((T fd.lfd_body).map Linstr.li_i) = true)
    (h : EntryCT (ctLeak w) P pub) : EntryCT (ctLeak w) P' pub :=
  entryCT_of_bodyCheck P P' pub (fun fn hg => by rw [hP', hg]; rfl)
    (fun fn fd hg => ⟨_, by rw [hP', hg]; rfl, hchk fn fd hg⟩) h

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakTV
