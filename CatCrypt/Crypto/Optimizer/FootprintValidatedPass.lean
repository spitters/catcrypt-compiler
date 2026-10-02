/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.SpillReloadBlockSound
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed

/-!
# Footprint-relative semantic certificates for spilling passes

`X86OptPipelineComposed.ValidatedPass.sem_sound` asks for full `JState` equality:
`runBlock s (f b) = runBlock s b` on every register and every memory cell. A
spilling pass cannot meet it — `SpillReloadBlockSound.spillReloadBlock_store_residue`
shows the materialized block leaves its spill stores in the frame cells, so the
final memories differ exactly on those cells. This module states the weaker
certificate that such a pass can satisfy and that still licenses composition: the
outputs agree on the whole machine state **except on a fixed finite set of dead
spill/scratch cells**.

## Contents

* `agreeExcept D s t` — the two states have equal registers, equal flags, and equal
  memory at every cell outside the dead set `D`.
* `FootprintSound f chk D` — the footprint-relative soundness of a gated rewrite:
  when the certificate fires, `runBlock s (f b)` agrees with `runBlock s b` modulo
  `D`.
* `agreeExcept_evalInstr` / `agreeExcept_runBlock` — the separation frame rule:
  running a continuation that reads no cell in `D` preserves `agreeExcept D`, so
  the observable output (outside `D`) stays equal.
* the spill pass's witness footprint certificate (`witness_footprint`) and its
  packaging as a `FootprintValidatedPass`, alongside the demonstration that the
  full-state certificate is unprovable for the same rewrite
  (`spill_full_state_fails`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.FootprintValidated

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc
open CatCrypt.Crypto.Optimizer.SpillReloadBlockSound

/-! ## 1. Agreement modulo a dead cell-set -/

/-- `agreeExcept D s t`: the states have equal register files, equal flags, and
    equal memory at every cell `(base, off)` that is not in the dead set `D`. -/
def agreeExcept (D : List (String × Int)) (s t : JState 64) : Prop :=
  s.regs = t.regs ∧ s.flags = t.flags ∧ ∀ b o, (b, o) ∉ D → s.mem b o = t.mem b o

@[refl] theorem agreeExcept_refl (D : List (String × Int)) (s : JState 64) :
    agreeExcept D s s :=
  ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem agreeExcept_symm {D : List (String × Int)} {s t : JState 64}
    (h : agreeExcept D s t) : agreeExcept D t s :=
  ⟨h.1.symm, h.2.1.symm, fun b o hbo => (h.2.2 b o hbo).symm⟩

theorem agreeExcept_trans {D : List (String × Int)} {s t u : JState 64}
    (h₁ : agreeExcept D s t) (h₂ : agreeExcept D t u) : agreeExcept D s u :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
    fun b o hbo => (h₁.2.2 b o hbo).trans (h₂.2.2 b o hbo)⟩

/-! ## 2. The separation frame rule

The register names a memory-reading instruction uses as a base. An instruction
that reads no cell in `D` cannot let the `D`-only difference between two
`agreeExcept D` states leak into a register, so the relation is preserved. -/

/-- The base register names an instruction reads a memory cell through. -/
def memReadBases : JInstr 64 → List String
  | .loadMem _ base _ => [base]
  | .loadMemIdx _ base _ _ => [base]
  | .mulxMem _ _ _ base _ => [base]
  | .loadSym _ sym => [sym]
  -- the memory-operand arithmetic reads its cell through `base`.
  | .addMem _ base _ | .addToMem base _ _ | .adcxMem _ base _ | .adoxMem _ base _
  | .imulMem _ base _ | .imulriMem _ base _ _ | .cmpMem _ base _
  | .cmovccMem _ _ base _ => [base]
  -- `lea` computes `base + idx·scale + off` into a register and dereferences
  -- nothing, so it reads memory through no base.
  | .lea _ _ _ _ _ => []
  | _ => []

/-- `instrAvoids D i`: no base `i` reads memory through is the base of a cell in
    `D`. Sufficient for `agreeExcept D` to survive `evalInstr … i`. -/
def instrAvoids (D : List (String × Int)) (i : JInstr 64) : Prop :=
  ∀ base ∈ memReadBases i, base ∉ D.map Prod.fst

/-- `blockAvoids D k`: every instruction in `k` avoids `D` (decidable). -/
def blockAvoids (D : List (String × Int)) (k : List (JInstr 64)) : Bool :=
  k.all (fun i => (memReadBases i).all (fun base => ! (D.map Prod.fst).contains base))

/-- A cell whose base is not a `D`-base is not in `D`. -/
theorem pair_notin_of_base_notin {D : List (String × Int)} {base : String} (off : Int)
    (h : base ∉ D.map Prod.fst) : (base, off) ∉ D := fun hc =>
  h (List.mem_map.mpr ⟨(base, off), hc, rfl⟩)

/-- **The single-instruction frame rule.** If `s` and `t` agree modulo `D` and `i`
    reads no cell in `D`, then the post-states agree modulo `D`. -/
theorem agreeExcept_evalInstr {D : List (String × Int)} (i : JInstr 64)
    {s t : JState 64} (h : agreeExcept D s t) (hi : instrAvoids D i) :
    agreeExcept D (evalInstr s i) (evalInstr t i) := by
  obtain ⟨sr, sf, sm⟩ := s
  obtain ⟨tr, tf, tm⟩ := t
  obtain ⟨hr, hf, hm⟩ := h
  simp only at hr hf hm
  subst hr; subst hf
  -- After substitution both states share the register file `sr` and flags `sf`.
  cases i with
  | mov dst src =>
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.get, JOperand.eval]
    · intro b o hbo; simpa [evalInstr, JState.setReg] using hm b o hbo
  | add dst src | sub dst src | imul dst src | and_ dst src | or_ dst src
  | xor_ dst src | shl dst src | shr dst src | sar dst src =>
    refine ⟨?_, ?_, ?_⟩
    · simp [evalInstr, JState.writeB5W, JState.get, JOperand.eval]
    · simp [evalInstr, JState.writeB5W, JState.get, JOperand.eval]
    · intro b o hbo; simpa [evalInstr, JState.writeB5W] using hm b o hbo
  | test a src =>
    -- `test` writes only the five flags: the register files stay literally equal
    -- and memory is untouched.
    refine ⟨rfl, ?_, ?_⟩
    · simp [evalInstr, JState.writeB5, JState.get, JOperand.eval]
    · intro b o hbo; simpa [evalInstr, JState.writeB5] using hm b o hbo
  | cmp a src =>
    -- `cmp` writes only the five flags, exactly as `test` does.
    refine ⟨rfl, ?_, ?_⟩
    · simp [evalInstr, JState.writeB5, JState.get, JOperand.eval]
    · intro x y hxy; simpa [evalInstr, JState.writeB5] using hm x y hxy
  | not_ dst =>
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.get]
    · intro x y hxy; simpa [evalInstr, JState.setReg] using hm x y hxy
  | andn dst a c | bzhi dst a c =>
    refine ⟨?_, ?_, ?_⟩
    · simp [evalInstr, JState.writeB5W, JState.get]
    · simp [evalInstr, JState.writeB5W, JState.get]
    · intro x y hxy; simpa [evalInstr, JState.writeB5W] using hm x y hxy
  | rol dst amt | ror dst amt =>
    -- the rotates write `OF`/`CF` over the shared pre-state flags.
    refine ⟨?_, ?_, ?_⟩
    · simp [evalInstr, JState.writeB2W, JState.get, JOperand.eval]
    · simp [evalInstr, JState.writeB2W, JState.get, JOperand.eval]
    · intro x y hxy; simpa [evalInstr, JState.writeB2W] using hm x y hxy
  | rorx dst src amt =>
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.get, JOperand.eval]
    · intro x y hxy; simpa [evalInstr, JState.setReg] using hm x y hxy
  | shlx dst src cnt | shrx dst src cnt | sarx dst src cnt =>
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.get]
    · intro x y hxy; simpa [evalInstr, JState.setReg] using hm x y hxy
  | movzx dst sw src | movsx dst sw src =>
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.get]
    · intro x y hxy; simpa [evalInstr, JState.setReg] using hm x y hxy
  | lea dst bs ix sc dsp =>
    -- an address computation: no cell is read, so `hi` is not needed.
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.get]
    · intro x y hxy; simpa [evalInstr, JState.setReg] using hm x y hxy
  | adc dst src | sbb dst src =>
    refine ⟨?_, ?_, ?_⟩
    · simp [evalInstr, JState.writeB5W, JState.get, JOperand.eval, JState.flagB]
    · simp [evalInstr, JState.writeB5W, JState.get, JOperand.eval, JState.flagB]
    · intro b o hbo; simpa [evalInstr, JState.writeB5W] using hm b o hbo
  | neg dst =>
    refine ⟨?_, ?_, ?_⟩
    · simp [evalInstr, JState.writeB5W, JState.get]
    · simp [evalInstr, JState.writeB5W, JState.get]
    · intro b o hbo; simpa [evalInstr, JState.writeB5W] using hm b o hbo
  | setc dst =>
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.flagB]; rfl
    · intro b o hbo; simpa [evalInstr, JState.setReg] using hm b o hbo
  | cmove dst src | cmovne dst src | cmovb dst src =>
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.get, JOperand.eval, JState.flagB]
    · intro b o hbo; simpa [evalInstr, JState.setReg] using hm b o hbo
  | mulx dstHi dstLo a b =>
    refine ⟨?_, rfl, ?_⟩
    · simp [evalInstr, JState.setReg, JState.get, JOperand.eval]
    · intro b o hbo; simpa [evalInstr, JState.setReg] using hm b o hbo
  | adcx dst src | adox dst src =>
    refine ⟨?_, ?_, ?_⟩
    · simp [evalInstr, JState.get, JOperand.eval, JState.flagB]
    · simp [evalInstr, JState.get, JOperand.eval, JState.flagB]
    · intro b o hbo; simpa [evalInstr] using hm b o hbo
  | loadMem dst base off =>
    have hmb : ∀ o, sm base o = tm base o := fun o =>
      hm base o (pair_notin_of_base_notin o (hi base (by simp [memReadBases])))
    refine ⟨?_, rfl, ?_⟩
    · simp only [evalInstr, JState.setReg, JState.load, hmb]
    · intro b o hbo; simpa [evalInstr, JState.setReg] using hm b o hbo
  | mulxMem dstHi dstLo a base off =>
    have hmb : ∀ o, sm base o = tm base o := fun o =>
      hm base o (pair_notin_of_base_notin o (hi base (by simp [memReadBases])))
    refine ⟨?_, rfl, ?_⟩
    · simp only [evalInstr, JState.setReg, JState.get, JState.load, JOperand.eval, hmb]
    · intro b o hbo; simpa [evalInstr, JState.setReg] using hm b o hbo
  | loadMemIdx dst base idx scale =>
    have hmb : ∀ o, sm base o = tm base o := fun o =>
      hm base o (pair_notin_of_base_notin o (hi base (by simp [memReadBases])))
    refine ⟨?_, rfl, ?_⟩
    · simp only [evalInstr, JState.setReg, JState.get, JState.loadIdx, JState.load, hmb]
    · intro b o hbo; simpa [evalInstr, JState.setReg] using hm b o hbo
  | storeMem base off src =>
    refine ⟨rfl, rfl, ?_⟩
    intro b o hbo
    simp only [evalInstr, JState.store, JOperand.eval, JState.get, x86_MOV]
    by_cases hc : b = base ∧ o = off
    · simp [hc]
    · simp only [if_neg hc]; exact hm b o hbo
  | storeMemIdx base idx scale src =>
    refine ⟨rfl, rfl, ?_⟩
    intro b o hbo
    simp only [evalInstr, JState.storeIdx, JState.store, JOperand.eval, JState.get, x86_MOV]
    by_cases hc : b = base ∧ o = (scale : Int) * ((sr idx).toNat : Int)
    · simp only [hc, and_self, if_true]
    · simp only [hc, if_false]; exact hm b o hbo
  | loadSym dst sym =>
    have hb : ∀ o : Int, (sym, o) ∉ D := fun o =>
      pair_notin_of_base_notin o (hi sym (by simp [memReadBases]))
    refine ⟨rfl, rfl, ?_⟩
    intro b o hbo
    simp only [evalInstr]
    by_cases hc : b = dst
    · simp only [hc, if_pos]; exact hm sym o (hb o)
    · simp only [if_neg hc]; exact hm b o hbo
  -- The memory-source arithmetic reads a cell through a base outside `D`.
  | addMem dst base off | adcxMem dst base off | adoxMem dst base off | imulMem dst base off
  | imulriMem dst base off _ | cmpMem dst base off | cmovccMem _ dst base off =>
    have hmb : ∀ o, sm base o = tm base o := fun o =>
      hm base o (pair_notin_of_base_notin o (hi base (by simp [memReadBases])))
    refine ⟨?_, ?_, fun b o hbo => ?_⟩
    all_goals simp [evalInstr, JState.writeB5W, JState.writeB5, JState.setReg, JState.get,
      JState.load, JState.flagB, JState.condB, hmb]
    all_goals exact hm b o hbo
  -- `add [base + off], src` reads its cell through a base outside `D` and writes it back.
  | addToMem base off src =>
    have hmb : ∀ o, sm base o = tm base o := fun o =>
      hm base o (pair_notin_of_base_notin o (hi base (by simp [memReadBases])))
    have hsrc : src.eval ⟨sr, sf, sm⟩ = src.eval ⟨sr, sf, tm⟩ := by cases src <;> rfl
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.writeB5Mem, JState.writeB5, JState.store]
    · simp only [evalInstr, JState.writeB5Mem, JState.writeB5, JState.store, JState.load, hmb,
        hsrc]
    · intro b o hbo
      simp only [evalInstr, JState.writeB5Mem, JState.writeB5, JState.store, JState.load, hmb,
        hsrc]
      split
      · rfl
      · exact hm b o hbo
  -- These instructions read and write registers and flags only, never a memory cell.
  | inc _ | dec _ | clc | stc | xchg _ _ | imulri _ _ _ | mul _ _ _ | imulWide _ _ _
  | shld _ _ _ | shrd _ _ _ | rcl _ _ | rcr _ _ | cmovcc _ _ _ | setcc _ _
  | testN _ _ _ | bt _ _ | btr _ _ | bts _ _ =>
    refine ⟨?_, ?_, fun b o hbo => ?_⟩
    all_goals simp [evalInstr, JState.writeB4W, JState.writeB5W, JState.writeB5W2,
      JState.writeB5N, JState.writeB2W, JState.writeCFW, JState.setRegMerge, JState.setReg,
      JState.get, JOperand.eval, JState.flagB, JState.condB, x86_XCHG]
    all_goals exact hm b o hbo

/-- **The block frame rule.** Running a continuation `k` that reads no cell in `D`
    on two `agreeExcept D` states lands in `agreeExcept D` states — the observable
    output (every register, every flag, every cell outside `D`) is equal. -/
theorem agreeExcept_runBlock {D : List (String × Int)} (k : List (JInstr 64))
    {s t : JState 64} (h : agreeExcept D s t) (hk : ∀ i ∈ k, instrAvoids D i) :
    agreeExcept D (runBlock s k) (runBlock t k) := by
  induction k generalizing s t with
  | nil => simpa using h
  | cons i is ih =>
    rw [runBlock_cons, runBlock_cons]
    exact ih (agreeExcept_evalInstr i h (hk i (List.mem_cons.mpr (Or.inl rfl))))
      (fun j hj => hk j (List.mem_cons.mpr (Or.inr hj)))

/-- `blockAvoids D k = true` reflects into the `∀ i ∈ k, instrAvoids D i` the frame
    rule consumes. -/
theorem instrAvoids_of_blockAvoids {D : List (String × Int)} {k : List (JInstr 64)}
    (h : blockAvoids D k = true) : ∀ i ∈ k, instrAvoids D i := by
  intro i hi base hbase
  have hall := (List.all_eq_true.mp h) i hi
  have := (List.all_eq_true.mp hall) base hbase
  simpa [Bool.not_eq_true'] using this

/-! ## 3. Footprint-relative soundness of a gated rewrite -/

/-- **The footprint-relative certificate.** When `chk b` fires, the rewrite `f`
    lands in a state that agrees with the input modulo the dead cell-set `D` — the
    footprint relaxation of `ValidatedPass.sem_sound`. -/
def FootprintSound (f : List (JInstr 64) → List (JInstr 64))
    (chk : List (JInstr 64) → Bool) (D : List (String × Int)) : Prop :=
  ∀ b, chk b = true → ∀ s : JState 64,
    agreeExcept D (runBlock s (f b)) (runBlock s b)

/-- The dead spill cells a decision list occupies against `spillBase`: one cell per
    spilled byte-offset. This is the per-pass dead-set annotation a migration to the
    footprint certificate would attach. -/
def deadCells (spillBase : String) (decisions : List (String × Slot)) :
    List (String × Int) :=
  (spilledOffsets decisions).map (fun off => (spillBase, off))

/-! ## 4. The spill pass's footprint certificate on the witness block

`SpillReloadBlockSound.wfBlock` / `wfDecisions` is a `SpillWellFormed` single-spill
block. Full `runBlock` equality fails on it (`spillReloadBlock_store_residue`); the
footprint certificate holds with `D = deadCells "%rbp" wfDecisions`. -/

/-- **The spill pass is footprint-sound on the witness block.** The materialized
    block's spill store leaves `1` in the frame cell `("%rbp", 0)`; every register,
    every flag, and every memory cell outside that dead cell agrees with the
    original block's run. -/
theorem witness_footprint (s : JState 64) :
    agreeExcept (deadCells "%rbp" wfDecisions)
      (runBlock s (spillReloadBlock wfDecisions "%rbp" wfBlock))
      (runBlock s wfBlock) := by
  rw [wf_spillReloadBlock]
  simp only [wfBlock, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval, x86_MOV,
    JState.setReg, JState.get, JState.store]
  refine ⟨rfl, rfl, ?_⟩
  intro b o hbo
  simp only [deadCells, spilledOffsets, wfDecisions, List.filterMap_cons,
    List.filterMap_nil, List.map_cons, List.map_nil, List.mem_singleton] at hbo
  by_cases hc : b = "%rbp" ∧ o = 0
  · exact absurd (by rw [hc.1, hc.2]) hbo
  · simp only [if_neg hc]

/-- Packaged as a `FootprintSound` certificate: the spill rewrite gated to fire on
    the witness block carries the footprint certificate with dead set
    `deadCells "%rbp" wfDecisions`. -/
theorem spillReloadBlock_footprintSound :
    FootprintSound (spillReloadBlock wfDecisions "%rbp")
      (fun b => decide (b = wfBlock)) (deadCells "%rbp" wfDecisions) := by
  intro b hb s
  rw [show b = wfBlock from of_decide_eq_true hb]
  exact witness_footprint s

/-! ## 5. The footprint pass fires where the full-state gate cannot

`X86OptPipelineComposed.graphColorRAValidated` is currently wrapped behind the
no-op gate `noOpCert` because its rewrite is not full-`runBlock`-equal. On the
witness block the no-op gate rejects (the rewrite changes the block), and the
full-state `sem_sound` obligation is unprovable — but the footprint certificate
fires with the real spilled rewrite. -/

/-- A footprint-relative validated pass: an untrusted rewrite `f` with a decidable
    certificate `chk`, a dead cell-set `dead`, and the two soundness lemmas the
    certificate underwrites — agreement modulo `dead` and constant-time
    preservation. -/
structure FootprintValidatedPass where
  /-- The untrusted block rewrite. -/
  f : List (JInstr 64) → List (JInstr 64)
  /-- The decidable per-block certificate. -/
  chk : List (JInstr 64) → Bool
  /-- The dead spill/scratch cells the rewrite is permitted to disturb. -/
  dead : List (String × Int)
  /-- Footprint-relative semantic soundness. -/
  sem_sound_fp : ∀ b, chk b = true → ∀ s : JState 64,
    agreeExcept dead (runBlock s (f b)) (runBlock s b)
  /-- Constant-time preservation. -/
  ct_sound : ∀ b, chk b = true → allDirect b = true → allDirect (f b) = true

/-- **The spilling allocator as a footprint-validated pass.** The rewrite is the
    materialized spill block; the certificate fires on the witness; the dead set is
    the spill frame cell. Semantic soundness is `witness_footprint`. -/
def spillFootprintPass : FootprintValidatedPass where
  f := spillReloadBlock wfDecisions "%rbp"
  chk := fun b => decide (b = wfBlock)
  dead := deadCells "%rbp" wfDecisions
  sem_sound_fp := fun b hb s => by
    rw [show b = wfBlock from of_decide_eq_true hb]; exact witness_footprint s
  ct_sound := fun b hb _ => by
    rw [show b = wfBlock from of_decide_eq_true hb, wf_spillReloadBlock]; decide

/-- **The no-op gate rejects the spill rewrite on the witness.** The full-state
    fallback (`conservativeValidated`'s `noOpCert`, which `graphColorRAValidated`
    uses) fires only when the rewrite is the identity; here it is not, so the gated
    pass leaves the block unoptimized. -/
theorem spill_noOp_rejects :
    spillReloadBlock wfDecisions "%rbp" wfBlock ≠ wfBlock := by
  rw [wf_spillReloadBlock]; decide

/-- **The full-state semantic certificate is unprovable for the spill rewrite.**
    There is no `s`-uniform `runBlock`-equality between the spilled block and the
    original — exactly the obstruction `ValidatedPass.sem_sound` demands and
    `spillReloadBlock_store_residue` refutes. -/
theorem spill_full_state_fails :
    ¬ (∀ s : JState 64,
        runBlock s (spillReloadBlock wfDecisions "%rbp" wfBlock) = runBlock s wfBlock) := by
  intro hall
  exact spillReloadBlock_store_residue
    (congrArg (fun st : JState 64 => st.mem "%rbp" 0) (hall { regs := fun _ => 0 }))

end CatCrypt.Crypto.Optimizer.FootprintValidated
