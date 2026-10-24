/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge

/-!
# Schedule soundness over the uniform-width run with flags

The scheduler `LprogScheduler.scheduleBody` transposes adjacent instructions that its
independence test `LprogScheduler.indep` accepts. The hazard footprints of `indep` carry the
flags as the token `flagsTok`, placed in the read and the write set of every instruction
with `touchesFlags`, so an independent pair has disjoint register footprints and at most one
instruction that touches the flags. This module proves that such a transposition preserves
the step `LsemBridge.lsemStepFlag`, the uniform-width step that carries the flags `cf`,
`of`, and hence that the schedule preserves the run `LsemBridge.lsemStraightFlag`.

One step of `lsemStepFlag` on an instruction without a runtime-indexed operand is described
by its effect relative to the incoming state: the registers named by the write tokens of
the instruction and, when the instruction touches the flags, the two flags are taken from
the result; every other register, the word memory and the program counter plus one are
taken from the incoming state (`mergeL`). The step from a state `t` that agrees with `s` on
the hazard tokens of the instruction, on the word memory, and on the flags when the
instruction touches them (`AgreeL`), is the step from `s` with its effect applied to `t`
(`lsemStepFlag_transport`). The flag effect of an instruction is therefore the
classification `touchesFlags`: an instruction that does not touch the flags neither reads
nor writes `cf`, `of` under `lsemStepFlag` (`lsemStepFlag_flags_of_not_touchesFlags`), and
every flag write of `withALUFlagsL` and every carry-family step lies in the class
`touchesFlags`.

## Main definitions

* `mergeL` — the effect of a step of `lsemStepFlag` applied to another state.
* `AgreeL` — agreement of two states on the hazard tokens of an instruction, on the word
  memory, and on the flags when the instruction touches them.

## Main results

* `lsemStepFlag_transport` — a step from an agreeing state is the effect of the step
  applied to that state.
* `lsemStepFlag_swap`, `lsemStraightFlag_swap` — two adjacent independent instructions
  commute under the step with flags.
* `scheduleBody_lsemStraightFlag`, `scheduleBodyTail_lsemStraightFlag` — the scheduled body,
  tagged by any tagging function, reaches the same state, flags included, as the input.
* `runIBF_scheduleBody` — the schedule preserves the in-bounds run with flags.
* `scheduleBody_lsemStraightMemF_F`, `scheduleBody_lsemFuelMemF_F` — schedule soundness on
  the flag machine for bodies of `fragFB`, through `lsemStraightMemF_transportF` and
  `lsemFuelMemF_transportF`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Scheduler

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksMemF
  (lstateN_ext touchesFlags_of_alu touchesFlags_of_carry keyStartsWith_MULX
    keyStartsWith_MULXMEM indep_write_not_mem indep_flags)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The effect of a step -/

theorem lstate_ext {s t : Lstate 64} (h1 : s.lvm = t.lvm) (h2 : s.lmem = t.lmem)
    (h3 : s.lpc = t.lpc) (h4 : s.cf = t.cf) (h5 : s.of = t.of) : s = t := by
  cases s; cases t; simp_all

/-- The state `t` with the effect of a step of `i` whose result is `s'`: the registers named
    by the write tokens of `i`, and the two flags when `i` touches the flags, are those of
    `s'`; every other register and the word memory are those of `t`; the program counter is
    that of `t` plus one. -/
def mergeL (i : LinstrR) (t s' : Lstate 64) : Lstate 64 where
  lvm := fun r => if r ∈ writeToks i then s'.lvm r else t.lvm r
  lmem := t.lmem
  lpc := t.lpc + 1
  cf := if touchesFlags i then s'.cf else t.cf
  of := if touchesFlags i then s'.of else t.of

/-- Two states agree on the registers named by the hazard read and write tokens of `i`, on
    the word memory, and, when `i` touches the flags, on the two flags. -/
structure AgreeL (i : LinstrR) (s t : Lstate 64) : Prop where
  /-- Agreement on the registers named by the hazard tokens. -/
  reg : ∀ r ∈ hazardReads i ++ hazardWrites i, s.lvm r = t.lvm r
  /-- Agreement on the word memory. -/
  mem : s.lmem = t.lmem
  /-- Agreement on the flags. -/
  flags : touchesFlags i = true → s.cf = t.cf ∧ s.of = t.of

theorem agreeL_refl (i : LinstrR) (s : Lstate 64) : AgreeL i s s :=
  ⟨fun _ _ => rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem AgreeL.read {i : LinstrR} {s t : Lstate 64} (h : AgreeL i s t) {r : String}
    (hr : r ∈ readToks i) : s.lvm r = t.lvm r :=
  h.reg r (by simp [hazardReads, mem_readToksSem_of_mem_readToks hr])

theorem AgreeL.write {i : LinstrR} {s t : Lstate 64} (h : AgreeL i s t) {r : String}
    (hr : r ∈ writeToks i) : s.lvm r = t.lvm r :=
  h.reg r (by simp [hazardWrites, hr])

/-- A register or immediate operand has the same value in two states that agree on the
    register its token names. -/
theorem evalRI_congr {s t : Lstate 64} (o : LOperand)
    (h : ∀ r, opTok o = some r → s.lvm r = t.lvm r) : evalRI t o = evalRI s o := by
  cases o <;> simp_all [evalRI, opTok]

/-- A source operand of an instruction has the same value in two agreeing states. -/
theorem AgreeL.evalRI {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    {s t : Lstate 64} (h : AgreeL (.Lopn dsts opn srcs) s t) {o : LOperand} (ho : o ∈ srcs) :
    evalRI t o = evalRI s o :=
  evalRI_congr o fun r hr =>
    h.read (by simp only [readToks, List.mem_filterMap]; exact ⟨o, ho, hr⟩)

/-- The flags of `t` are the flags `mergeL` gives a result that kept the flags of `s`. -/
theorem mergeL_cf {i : LinstrR} {s t b : Lstate 64} (h : AgreeL i s t) (hb : b.cf = s.cf) :
    (mergeL i t b).cf = t.cf := by
  simp only [mergeL, hb]
  split
  · exact (h.flags ‹_›).1
  · rfl

theorem mergeL_of {i : LinstrR} {s t b : Lstate 64} (h : AgreeL i s t) (hb : b.of = s.of) :
    (mergeL i t b).of = t.of := by
  simp only [mergeL, hb]
  split
  · exact (h.flags ‹_›).2
  · rfl

/-- A result with the registers of `s` has, under `mergeL`, the registers of `t`. -/
theorem mergeL_lvm0 {i : LinstrR} {s t b : Lstate 64} (h : AgreeL i s t)
    (hb : b.lvm = s.lvm) : (mergeL i t b).lvm = t.lvm := by
  funext r
  simp only [mergeL, hb]
  split_ifs with hr
  · exact h.write hr
  · rfl

/-- A write of `d` from `s`, applied to `t`, is the same write on `t`. -/
theorem mergeL_lvm1 {i : LinstrR} {s t b : Lstate 64} (h : AgreeL i s t) {d : String}
    (hd : d ∈ writeToks i) (v : BitVec 64) (hb : b.lvm = (s.setReg d v).lvm) :
    (mergeL i t b).lvm = (t.setReg d v).lvm := by
  funext r
  simp only [mergeL, hb, Lstate.lvm_setReg]
  by_cases hr : r = d
  · subst hr; simp [hd]
  · by_cases hrW : r ∈ writeToks i <;> simp [hr, hrW, h.write]

/-- Two writes from `s`, applied to `t`, are the same writes on `t`. -/
theorem mergeL_lvm2 {i : LinstrR} {s t b : Lstate 64} (h : AgreeL i s t) {d e : String}
    (hd : d ∈ writeToks i) (he : e ∈ writeToks i) (v v' : BitVec 64)
    (hb : b.lvm = ((s.setReg d v).setReg e v').lvm) :
    (mergeL i t b).lvm = ((t.setReg d v).setReg e v').lvm := by
  funext r
  simp only [mergeL, hb, Lstate.lvm_setReg]
  by_cases hre : r = e
  · subst hre; simp [he]
  · by_cases hr : r = d
    · subst hr; simp [hd, hre]
    · by_cases hrW : r ∈ writeToks i <;> simp [hr, hre, hrW, h.write]

/-! ## 2. Transport of a step -/

/-- The flag-oblivious step from an agreeing state is its effect applied to that state, with
    the flags of that state. -/
theorem lsemStep_transportL (i : LinstrR) (hai : hasArrIdx i = false) {s t : Lstate 64}
    (h : AgreeL i s t) :
    lsemStep i t = (lsemStep i s).map fun b => { mergeL i t b with cf := t.cf, of := t.of } := by
  rw [lsemStep_eq_applyEffU, lsemStep_eq_applyEffU,
    ← stepEffU_congr i s t h.mem hai (fun r hr => h.read hr), Option.map_map]
  rcases he : stepEffU i s with _ | e
  · rfl
  · simp only [Option.map_some, Function.comp_apply, Option.some.injEq]
    have hm := stepEffU_mem_none i s hai he
    obtain ⟨reg, mem⟩ := e
    simp only at hm
    subst hm
    rcases reg with _ | ⟨d, v⟩
    · exact lstate_ext (mergeL_lvm0 h rfl).symm rfl rfl rfl rfl
    · have hw : writeToks i = [d] := stepEffU_writeToks_of_effName hai he rfl
      exact lstate_ext (mergeL_lvm1 h (by simp [hw]) v rfl).symm rfl rfl rfl rfl

/-- Split a recognizer equation `X? i = some p` into the instruction's shape. -/
local macro "recog" hx:ident : tactic =>
  `(tactic| (repeat' split at $hx:ident) <;> (try simp only [Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq] at $hx:ident) <;> (try casesm* _ ∧ _) <;> subst_vars)

/-- The flags `withALUFlagsL` writes commute with the effect of the step. -/
theorem withALUFlagsL_transport (i : LinstrRM) {s t : Lstate 64} (h : AgreeL i.1 s t)
    (b : Lstate 64) (hc : b.cf = s.cf) (ho : b.of = s.of) :
    withALUFlagsL i t { mergeL i.1 t b with cf := t.cf, of := t.of }
      = mergeL i.1 t (withALUFlagsL i s b) := by
  obtain ⟨w, tag⟩ := i
  have keep : ({ mergeL w t b with cf := t.cf, of := t.of } : Lstate 64) = mergeL w t b :=
    lstate_ext rfl rfl rfl (mergeL_cf h hc).symm (mergeL_of h ho).symm
  unfold withALUFlagsL
  cases hx : aluFlagOp? (w, tag) with
  | none => exact keep
  | some p =>
    have ht := touchesFlags_of_alu hx
    obtain ⟨op, a, b'⟩ := p
    unfold aluFlagOp? at hx
    simp only at hx ht h keep ⊢
    recog hx
    all_goals
      rw [h.evalRI List.mem_cons_self, h.evalRI (List.mem_cons_of_mem _ List.mem_cons_self)]
      generalize evalRI s _ = ea
      generalize evalRI s _ = eb
      cases ea <;> cases eb <;> simp only
      all_goals first
        | exact keep
        | exact lstate_ext rfl rfl rfl (by simp [mergeL, ht]) (by simp [mergeL, ht])

/-- **Transport of a step with flags.** The step of an instruction without a
    runtime-indexed operand, from a state that agrees with `s` on its hazard tokens, on the
    word memory, and on the flags when it touches them, is the step from `s` with its effect
    applied to that state. -/
theorem lsemStepFlag_transport (i : LinstrRM) (hai : hasArrIdx i.1 = false) {s t : Lstate 64}
    (h : AgreeL i.1 s t) : lsemStepFlag i t = (lsemStepFlag i s).map (mergeL i.1 t) := by
  obtain ⟨w, tag⟩ := i
  simp only at hai h
  unfold lsemStepFlag
  simp only
  rw [lsemStep_transportL w hai h]
  cases hm : lsemStep w s with
  | some b =>
    obtain ⟨hc, ho⟩ := lsemStep_flags _ _ _ hm
    simp only [Option.map_some]
    exact congrArg some (withALUFlagsL_transport (w, tag) h b hc ho)
  | none =>
    simp only [Option.map_none]
    cases hk : carryArgs? (w, tag) with
    | some p =>
      have ht := touchesFlags_of_carry hk
      obtain ⟨hcf, hof⟩ := h.flags ht
      obtain ⟨op, d, a, b⟩ := p
      unfold carryArgs? at hk
      simp only at hk ht h ⊢
      recog hk
      all_goals
        simp only [carryStepL, ← hcf, ← hof]
        rw [h.evalRI List.mem_cons_self, h.evalRI (List.mem_cons_of_mem _ List.mem_cons_self)]
        generalize evalRI s _ = ea
        generalize evalRI s _ = eb
        cases ea <;> cases eb <;> simp only [Option.map_none, Option.map_some]
        all_goals first
          | rfl
          | exact congrArg some (lstate_ext
              (mergeL_lvm1 h (by simp [writeToks, opTok]) _ rfl).symm rfl rfl
              (by simp [mergeL, ht, hcf]) (by simp [mergeL, ht, hof]))
    | none =>
      simp only
      cases hw : wideArgs? (w, tag) with
      | none => rfl
      | some p =>
        unfold wideArgs? at hw
        simp only at hw h ⊢
        recog hw
        all_goals (try (casesm* _ ∨ _) <;> subst_vars)
        all_goals
          simp only [wideStepL]
          first
            | rw [h.evalRI (List.mem_cons_of_mem _ List.mem_cons_self)]
            | rw [h.evalRI List.mem_cons_self,
                ← h.reg mulxSrc (by simp [hazardReads, implicitReads, mulxSrc,
                  keyStartsWith_MULX, keyStartsWith_MULXMEM])]
          generalize evalRI s _ = eb
          cases eb <;> simp only [Option.map_none, Option.map_some]
          exact congrArg some (lstate_ext
            (by first
              | exact (mergeL_lvm1 h (by simp [writeToks, opTok]) _ rfl).symm
              | exact (mergeL_lvm2 h (by simp [writeToks, opTok]) (by simp [writeToks, opTok])
                  _ _ rfl).symm) rfl rfl
            (mergeL_cf h rfl).symm (mergeL_of h rfl).symm)

/-- A successful step is its own effect applied to its incoming state. -/
theorem lsemStepFlag_mergeL {i : LinstrRM} (hai : hasArrIdx i.1 = false) {s s' : Lstate 64}
    (h : lsemStepFlag i s = some s') : mergeL i.1 s s' = s' := by
  have := lsemStepFlag_transport i hai (agreeL_refl i.1 s)
  rw [h, Option.map_some, Option.some.injEq] at this
  exact this.symm

/-- **The flag effect of an instruction outside `touchesFlags`.** Such an instruction keeps
    both flags under `lsemStepFlag`. -/
theorem lsemStepFlag_flags_of_not_touchesFlags {i : LinstrRM} (hai : hasArrIdx i.1 = false)
    (ht : touchesFlags i.1 = false) {s s' : Lstate 64} (h : lsemStepFlag i s = some s') :
    s'.cf = s.cf ∧ s'.of = s.of := by
  rw [← lsemStepFlag_mergeL hai h]
  simp [mergeL, ht]

/-- A step with flags without a runtime-indexed operand keeps the word memory. -/
theorem lsemStepFlag_lmem {i : LinstrRM} (hai : hasArrIdx i.1 = false) {s s' : Lstate 64}
    (h : lsemStepFlag i s = some s') : s'.lmem = s.lmem := by
  rw [← lsemStepFlag_mergeL hai h]
  rfl

/-! ## 3. Independent instructions commute -/

/-- After a step of `i1`, the state agrees with the incoming one on the hazard tokens of an
    independent `i2`. -/
theorem agreeL_after {i1 i2 : LinstrR} (hind : indep i1 i2 = true) {s s1 : Lstate 64}
    (hs1 : mergeL i1 s s1 = s1) : AgreeL i2 s s1 := by
  refine ⟨fun r hr => ?_, ?_, fun ht => ?_⟩
  · rw [← hs1]
    have : r ∉ writeToks i1 := fun hw => indep_write_not_mem hind hw hr
    simp [mergeL, this]
  · rw [← hs1]
    rfl
  · rw [← hs1]
    have : touchesFlags i1 = false := by
      cases h1 : touchesFlags i1
      · rfl
      · exact absurd ⟨h1, ht⟩ (indep_flags hind)
    simp [mergeL, this]

/-- The effects of two independent instructions commute. -/
theorem mergeL_comm {i1 i2 : LinstrR} (hind : indep i1 i2 = true) (s a b : Lstate 64) :
    mergeL i2 (mergeL i1 s a) b = mergeL i1 (mergeL i2 s b) a := by
  have hw : ∀ r, r ∈ writeToks i1 → r ∉ writeToks i2 := fun r h1 h2 =>
    indep_write_not_mem hind h1 (List.mem_append_right _ (by simp [hazardWrites, h2]))
  have hfl := indep_flags hind
  refine lstate_ext ?_ rfl rfl ?_ ?_
  · funext r
    simp only [mergeL]
    by_cases h1 : r ∈ writeToks i1
    · simp [h1, hw r h1]
    · by_cases h2 : r ∈ writeToks i2 <;> simp [h1, h2]
  · simp only [mergeL]
    cases h1 : touchesFlags i1 <;> cases h2 : touchesFlags i2 <;> simp_all
  · simp only [mergeL]
    cases h1 : touchesFlags i1 <;> cases h2 : touchesFlags i2 <;> simp_all

/-- **Adjacent independent instructions commute under `lsemStepFlag`.** -/
theorem lsemStepFlag_swap (i1 i2 : LinstrRM) (s : Lstate 64) (h : indep i1.1 i2.1 = true) :
    (lsemStepFlag i1 s).bind (lsemStepFlag i2) = (lsemStepFlag i2 s).bind (lsemStepFlag i1) := by
  have h' : indep i2.1 i1.1 = true := by rw [indep_symm]; exact h
  have ha1 := indep_arrIdx_left h
  have ha2 := indep_arrIdx_right h
  rcases h1 : lsemStepFlag i1 s with _ | s1 <;> rcases h2 : lsemStepFlag i2 s with _ | s2
  · rfl
  · simp only [Option.bind_none, Option.bind_some]
    rw [lsemStepFlag_transport i1 ha1 (agreeL_after h' (lsemStepFlag_mergeL ha2 h2)), h1]
    rfl
  · simp only [Option.bind_none, Option.bind_some]
    rw [lsemStepFlag_transport i2 ha2 (agreeL_after h (lsemStepFlag_mergeL ha1 h1)), h2]
    rfl
  · simp only [Option.bind_some]
    rw [lsemStepFlag_transport i2 ha2 (agreeL_after h (lsemStepFlag_mergeL ha1 h1)), h2,
      lsemStepFlag_transport i1 ha1 (agreeL_after h' (lsemStepFlag_mergeL ha2 h2)), h1]
    simp only [Option.map_some, Option.some.injEq]
    calc mergeL i2.1 s1 s2 = mergeL i2.1 (mergeL i1.1 s s1) s2 := by
          rw [lsemStepFlag_mergeL ha1 h1]
      _ = mergeL i1.1 (mergeL i2.1 s s2) s1 := mergeL_comm h s s1 s2
      _ = mergeL i1.1 s2 s1 := by rw [lsemStepFlag_mergeL ha2 h2]

/-- **Adjacent-transposition commutation for `lsemStraightFlag`.** -/
theorem lsemStraightFlag_swap (i1 i2 : LinstrRM) (rest : List LinstrRM) (s : Lstate 64)
    (h : indep i1.1 i2.1 = true) :
    lsemStraightFlag (i1 :: i2 :: rest) s = lsemStraightFlag (i2 :: i1 :: rest) s := by
  have e : ∀ (j k : LinstrRM), lsemStraightFlag (j :: k :: rest) s
      = ((lsemStepFlag j s).bind (lsemStepFlag k)).bind (lsemStraightFlag rest) := by
    intro j k
    rw [lsemStraightFlag_cons, Option.bind_assoc]
    rfl
  rw [e, e, lsemStepFlag_swap i1 i2 s h]

/-! ## 4. Schedule soundness over the run with flags -/

/-- **Schedule soundness over the uniform-width run with flags.** For any tagging of the
    wire instructions by memory tags, the scheduled body run by `lsemStraightFlag` reaches
    the same state, flags included, as the input body. -/
theorem scheduleBody_lsemStraightFlag (tag : LinstrR → MemTag) (b : List Linstr)
    (l : Lstate 64) :
    lsemStraightFlag ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)) l
      = lsemStraightFlag (b.map fun i => (i.li_i, tag i.li_i)) l := by
  have := scheduleBody_run (run := fun l s => lsemStraightFlag (l.map fun i => (i, tag i)) s)
    (fun l1 l2 s => by simp only [List.map_append, lsemStraightFlag_append])
    (fun i1 i2 rest s hi => lsemStraightFlag_swap (i1, tag i1) (i2, tag i2) _ s hi) b l
  simpa [List.map_map, Function.comp_def] using this

/-- **Tail-preserving schedule soundness over the uniform-width run with flags.** -/
theorem scheduleBodyTail_lsemStraightFlag (tag : LinstrR → MemTag) (keepTail : Nat)
    (b : List Linstr) (l : Lstate 64) :
    lsemStraightFlag ((scheduleBodyTail keepTail b).map fun i => (i.li_i, tag i.li_i)) l
      = lsemStraightFlag (b.map fun i => (i.li_i, tag i.li_i)) l := by
  have := scheduleBodyTail_run
    (run := fun l s => lsemStraightFlag (l.map fun i => (i, tag i)) s)
    (fun l1 l2 s => by simp only [List.map_append, lsemStraightFlag_append])
    (fun i1 i2 rest s hi => lsemStraightFlag_swap (i1, tag i1) (i2, tag i2) _ s hi)
    keepTail b l
  simpa [List.map_map, Function.comp_def] using this

/-- Two adjacent independent instructions commute under the in-bounds run with flags. -/
theorem runIBF_swap (tag : LinstrR → MemTag) (i1 i2 : LinstrR) (rest : List LinstrR)
    (l : Lstate 64) (h : indep i1 i2 = true) :
    runIBF ((i1 :: i2 :: rest).map fun i => (i, tag i)) l
      = runIBF ((i2 :: i1 :: rest).map fun i => (i, tag i)) l := by
  have e : ∀ j k : LinstrR, hasArrIdx j = false → hasArrIdx k = false →
      runIBF ((j :: k :: rest).map fun i => (i, tag i)) l
        = ((lsemStepFlag (j, tag j) l).bind (lsemStepFlag (k, tag k))).bind
            (runIBF (rest.map fun i => (i, tag i))) := by
    intro j k hj hk
    simp only [List.map_cons, runIBF, stepIBF, inBoundsB_of_hasArrIdx hj,
      inBoundsB_of_hasArrIdx hk, ite_true, Option.bind_assoc]
  rw [e i1 i2 (indep_arrIdx_left h) (indep_arrIdx_right h),
    e i2 i1 (indep_arrIdx_right h) (indep_arrIdx_left h),
    lsemStepFlag_swap (i1, tag i1) (i2, tag i2) l h]

/-- The schedule preserves the in-bounds run with flags of a body tagged by a function of
    the wire. -/
theorem runIBF_scheduleBody (tag : LinstrR → MemTag) (b : List Linstr) (l : Lstate 64) :
    runIBF ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)) l
      = runIBF (b.map fun i => (i.li_i, tag i.li_i)) l := by
  have := scheduleBody_run (run := fun l s => runIBF (l.map fun i => (i, tag i)) s)
    (fun l1 l2 s => by simp only [List.map_append, runIBF_append])
    (fun i1 i2 rest s hi => runIBF_swap tag i1 i2 rest s hi) b l
  simpa [List.map_map, Function.comp_def] using this

/-! ## 5. Transport to the flag machine -/

/-- The scheduled body of a body of the fragment with flags is in the fragment. -/
theorem fragFB_scheduleBody {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true) :
    ∀ i ∈ (scheduleBody b).map (fun i => (i.li_i, tag i.li_i)), fragFB A i = true := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  exact hfrag j ((scheduleBody_perm b).mem_iff.1 hj)

/-- **Schedule soundness on the flag machine through the bridge with flags.** For a body of
    the fragment with flags whose in-bounds run succeeds, from a state related to `l` with
    its flags, the scheduled body and the input body run under `lsemStraightMemF` to states
    with the same register file, arrays, word memory and flags; both `lsemStraightFlag` runs
    from `l` reach one state `t`, whose flags are those of the two results. -/
theorem scheduleBody_lsemStraightMemF_F {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRelF A s l)
    (hib : (runIBF (b.map fun i => (i.li_i, tag i.li_i)) l).isSome) :
    ∃ u u' t,
      lsemStraightMemF ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)) s = some u ∧
      lsemStraightMemF (b.map fun i => (i.li_i, tag i.li_i)) s = some u' ∧
      lsemStraightFlag ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)) l = some t ∧
      lsemStraightFlag (b.map fun i => (i.li_i, tag i.li_i)) l = some t ∧
      u.reg = u'.reg ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem ∧
      u.cf = u'.cf ∧ u.of = u'.of ∧ u'.cf = t.cf ∧ u'.of = t.of := by
  have hB' : ∀ i ∈ b.map (fun i => (i.li_i, tag i.li_i)), fragFB A i = true := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hfrag j hj
  obtain ⟨u, u', t, t', hu, hu', ht, ht', hO, hA, hM, hc, ho, hc', ho'⟩ :=
    lsemStraightMemF_transportF (O := fun _ => True)
      (fragFB_scheduleBody tag b hfrag) hB' hr (by rw [runIBF_scheduleBody]; exact hib) hib
      (fun t t' ht ht' => by
        rw [scheduleBody_lsemStraightFlag, ht'] at ht
        cases ht
        exact ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩)
  have htt : t = t' := by
    rw [scheduleBody_lsemStraightFlag, ht'] at ht
    exact (Option.some.inj ht).symm
  subst htt
  refine ⟨u, u', t, hu, hu', ht, ht', lstateN_ext (funext fun r => hO r trivial) ?_, hA, hM,
    hc.trans hc'.symm, ho.trans ho'.symm, hc', ho'⟩
  have h1 := lsemStraightMemF_lpc _ s u hu
  have h2 := lsemStraightMemF_lpc _ s u' hu'
  simp only [LstateM.lpc, List.length_map, scheduleBody_length] at h1 h2
  rw [h1, h2]

/-- **Schedule soundness on the fuel machine through the bridge with flags.** Under the
    hypotheses of `scheduleBody_lsemStraightMemF_F` and from pc `0`, the singleton programs
    of the scheduled body and of the input body run under `lsemFuelMemF`, with fuel the
    body length, to halted states whose bases have the same register file, arrays, word
    memory and flags. -/
theorem scheduleBody_lsemFuelMemF_F {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRelF A s l)
    (hib : (runIBF (b.map fun i => (i.li_i, tag i.li_i)) l).isSome)
    (fn : String) (zf : Bool) (hpc : s.reg.lpc = 0) :
    ∃ u u',
      lsemFuelMemF (singletonProgM fn ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)))
          b.length { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := u, lfn := fn }, zf := zf } ∧
      lsemFuelMemF (singletonProgM fn (b.map fun i => (i.li_i, tag i.li_i)))
          b.length { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := u', lfn := fn }, zf := zf } ∧
      u.reg = u'.reg ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem ∧ u.cf = u'.cf ∧ u.of = u'.of := by
  have hB' : ∀ i ∈ b.map (fun i => (i.li_i, tag i.li_i)), fragFB A i = true := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hfrag j hj
  obtain ⟨u, u', t, hu, hu', -, -, hreg, hA, hM, hc, ho, -, -⟩ :=
    scheduleBody_lsemStraightMemF_F tag b hfrag hr hib
  have e1 := lsemFuelMemF_of_fragF (fragFB_scheduleBody tag b hfrag) fn zf hpc hu
  have e2 := lsemFuelMemF_of_fragF hB' fn zf hpc hu'
  simp only [List.length_map, scheduleBody_length] at e1 e2
  exact ⟨u, u', e1, e2, hreg, hA, hM, hc, ho⟩

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Scheduler
