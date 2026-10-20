/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSem

/-!
# Simulation of the region frames of the Jasmin lowering in the `psem.v` mirror

The code `nfToJasminBody` emits for a call-free region, translated by `translateCmdExt` and
typed by `typeC`, runs in the mirror's `Sem` from a state that agrees with the valuation of
the region to a state whose returned variables hold the denotation of the region
(`nfToJasminBody_sem_frames`). The region may contain the three frames of the lowering:

* a counted loop (`forCode`): the seeds of the carried block, the trip index and the
  counter, the mirror loop `while (ctr != 0)` over the body, the join moves and the
  advance, and the moves of the carried block one depth down;
* a branch (`ifCode`): `if (c != 0)` over the two arms, each followed by its join moves;
* an exit-flag loop (`whileCode`): the seeds, and `while { body; flag = bit; moves }
  (flag != 0)`.

## Invariant

The induction carries `RegionPost`: besides the agreement of the returned variables, the
code of a region writes only the names of `Writes` (scratch variables, bindings at depths
from the start depth, loop counters from the start loop number, and the arrays an in-place
store reaches), and keeps memory, syscall state and the sizes of arrays. Store agreement
across a frame follows from this frame property; store agreement of the body of a frame
and of its continuation extends the environment by a block of carried variables
(`storeAgrees_block`).

## Main results

* `sem_parMovesJ`, `sem_join`, `sem_shift`: the parallel and sequential moves of the frames.
* `semIr_while_count`, `semIr_while_flag`: the two mirror loops against an invariant.
* `Writes`, `RegionPost`, `Sim`: the written names, the state after a region, and the
  simulation property.
* `sim_for`, `sim_if`, `sim_while`: the frames simulate.
* `nfToJasminRegion_sim`, `nfToJasminBody_sem_frames`: call-free regions simulate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSemFrames

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (varIndex)
open CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem (gprB bmiB jazzOps jazzAsmSem
  JazzAsmAgrees opName)
open CatCrypt.Crypto.Jasmin.CoqSemMirror (Value Vm Estate OpSem AsmSem GlobDecls Prog Sem
  SemIr SemI SemFor JResult truncateVal evalAtype JArrayMirror MemModel semPexpr writeLval
  writeLvals setVar getVar mkLvar)

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## 1. Sequences of moves -/

section Moves
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- The assignments `p.1 = p.2` of the pairs `ps`, in order. -/
def movesOf (ps : List (JVar × JVar)) : List AInstrR := ps.map fun p => asgn p.1 (pv p.2)

/-- The source of every move holds a defined value of the type of its target. -/
def MovesTyped (vm : Vm) (ps : List (JVar × JVar)) : Prop :=
  ∀ p ∈ ps, OkV p.1 ∧ OkV p.2 ∧ p.1.vtype = p.2.vtype ∧ (vm (mvar p.2)).isDefined = true ∧
    (vm (mvar p.2)).typeOf = evalAtype (mvar p.1).vtype

/-- **Sequential moves.** The moves of `ps`, where no move reads a variable an earlier move
writes and the targets have distinct names, run to a state in which every target holds
the value its source held, and every variable whose name is no target is unchanged. -/
theorem sem_movesOf : ∀ {ps : List (JVar × JVar)},
    ps.Pairwise (fun p q => q.2.vname ≠ p.1.vname ∧ q.1.vname ≠ p.1.vname) →
    ∀ {c' : List MInstr}, translateCmdExt (movesOf ps) = some c' →
    ∀ {s : Estate SyscallState Mem}, MovesTyped s.evm ps →
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ s'.escs = s.escs ∧ s'.emem = s.emem ∧
      (∀ p ∈ ps, s'.evm (mvar p.1) = s.evm (mvar p.2)) ∧
      (∀ z : MVar, (∀ p ∈ ps, z.vname ≠ p.1.vname) → s'.evm z = s.evm z) ∧
      (VmArrTyped s.evm → VmArrTyped s'.evm)
  | [], _, c', hc, s, _ =>
      ⟨s, sem_nil_step aS opS gd prog hc s, rfl, rfl, by simp, fun _ _ => rfl, id⟩
  | (x, y) :: ps, hpw, c', hc, s, hty => by
      obtain ⟨hx, hy, hxy, hdef, htp⟩ := hty _ List.mem_cons_self
      rw [List.pairwise_cons] at hpw
      obtain ⟨hhd, htl⟩ := hpw
      let s1 : Estate SyscallState Mem := s.withVm (s.evm.set (mvar x) (s.evm (mvar y)))
      have hfr1 : ∀ z : MVar, z.vname ≠ x.vname → s1.evm z = s.evm z :=
        fun z hz => set_ne _ hz
      have hty1 : MovesTyped s1.evm ps := by
        intro p hp
        obtain ⟨h1, h2, h3, h4, h5⟩ := hty p (List.mem_cons_of_mem _ hp)
        have : s1.evm (mvar p.2) = s.evm (mvar p.2) := hfr1 _ (hhd p hp).1
        exact ⟨h1, h2, h3, this ▸ h4, this ▸ h5⟩
      obtain ⟨-, c'', -, hc'', -⟩ := translateCmdExt_cons_inv hc
      obtain ⟨s', hsem, hscs, hmem, hres, hfr, harr⟩ := sem_movesOf htl hc'' hty1
      refine ⟨s', sem_asgn_step aS opS gd prog hx (translatePExprExt_pv (translateVarIExt_mvi hy))
        hc (v := s.evm (mvar y)) (semPexpr_mpv opS gd (x := mvi y) rfl hdef) hdef htp
        (fun c3 h3 => by rw [hc''] at h3; cases h3; exact hsem), hscs, hmem, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · rw [hfr _ (fun q hq => (hhd q hq).2.symm)]
          simp [s1, Estate.withVm]
        · rw [hres p hp]
          exact hfr1 _ (hhd p hp).1
      · intro z hz
        rw [hfr z (fun q hq => hz q (List.mem_cons_of_mem _ hq))]
        exact hfr1 z (hz _ List.mem_cons_self)
      · intro h
        exact harr (arrTyped_set h hdef htp)

/-- A pairwise relation on a list indexed by `zipIdx` holds when it holds at every pair of
positions. -/
theorem pairwise_zipIdx_map {α β : Type} (l : List α) (f : α × Nat → β) (R : β → β → Prop)
    (h : ∀ i j (hi : i < l.length) (hj : j < l.length), i < j → R (f (l[i], i)) (f (l[j], j))) :
    ((l.zipIdx).map f).Pairwise R := by
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_zipIdx] at hi hj
  simpa using h i j hi hj hij

/-- The staging temporary of position `j` of the parallel moves from the depth `D`. -/
def stageV (D : Nat) (q : (JVar × JVar) × Nat) : JVar := mkV 'r' (D + q.2) q.1.1.vtype

/-- **Parallel moves.** The parallel assignment `parMovesJ D pairs`, whose targets have
distinct names and whose targets and sources are named apart from the temporaries from the
depth `D`, runs to a state in which every target holds the value its source held, and every
variable that is neither a target nor a temporary is unchanged. -/
theorem sem_parMovesJ (D : Nat) {pairs : List (JVar × JVar)}
    (hgood : ∀ p ∈ pairs, GoodV p.1 ∧ GoodV p.2)
    (hnd : (pairs.map fun p => p.1.vname).Nodup)
    (htgt : ∀ p ∈ pairs, ∀ j s, p.1.vname ≠ nameOf 'r' (D + j) s)
    (hsrc : ∀ p ∈ pairs, ∀ j s, p.2.vname ≠ nameOf 'r' (D + j) s)
    {c' : List MInstr} (hc : translateCmdExt (parMovesJ D pairs) = some c')
    {s : Estate SyscallState Mem} (hty : MovesTyped s.evm pairs) :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ s'.escs = s.escs ∧ s'.emem = s.emem ∧
      (∀ p ∈ pairs, s'.evm (mvar p.1) = s.evm (mvar p.2)) ∧
      (∀ z : MVar, (∀ p ∈ pairs, z.vname ≠ p.1.vname) →
        (∀ j < pairs.length, ∀ s, z.vname ≠ nameOf 'r' (D + j) s) → s'.evm z = s.evm z) ∧
      (VmArrTyped s.evm → VmArrTyped s'.evm) := by
  set ps := pairs.filter fun p => p.1 != p.2 with hps
  have hsub : ps.Sublist pairs := List.filter_sublist
  have hmem : ∀ p ∈ ps, p ∈ pairs := fun p hp => hsub.subset hp
  have hndps : (ps.map fun p => p.1.vname).Nodup := hnd.sublist (hsub.map _)
  have hinj := List.inj_on_of_nodup_map hnd
  -- a pair whose target is its source is left out, and no other pair writes its target
  have hfix : ∀ p ∈ pairs, p ∉ ps → p.1 = p.2 := by
    intro p hp hn
    by_contra hne
    exact hn (List.mem_filter.2 ⟨hp, by simpa using hne⟩)
  have hother : ∀ p ∈ pairs, p ∉ ps → ∀ q ∈ ps, p.1.vname ≠ q.1.vname := by
    intro p hp hn q hq he
    have := hinj hp (hmem q hq) he
    subst this
    exact hn hq
  -- the moves of the filtered pairs
  suffices h : ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ s'.escs = s.escs ∧
      s'.emem = s.emem ∧ (∀ p ∈ ps, s'.evm (mvar p.1) = s.evm (mvar p.2)) ∧
      (∀ z : MVar, (∀ p ∈ ps, z.vname ≠ p.1.vname) →
        (∀ j < ps.length, ∀ s, z.vname ≠ nameOf 'r' (D + j) s) → s'.evm z = s.evm z) ∧
      (VmArrTyped s.evm → VmArrTyped s'.evm) by
    obtain ⟨s', hsem, hscs, hmm, hres, hfr, harr⟩ := h
    refine ⟨s', hsem, hscs, hmm, fun p hp => ?_, fun z hz hzt => hfr z
      (fun p hp => hz p (hmem p hp))
      (fun j hj => hzt j (lt_of_lt_of_le hj (List.length_filter_le _ _))), harr⟩
    by_cases hin : p ∈ ps
    · exact hres p hin
    · rw [← hfix p hp hin]
      exact hfr _ (hother p hp hin) (fun j _ => htgt p hp j)
  have htyps : MovesTyped s.evm ps := fun p hp => hty p (hmem p hp)
  have hpwt : ps.Pairwise fun p q => q.1.vname ≠ p.1.vname := by
    have := List.pairwise_map.1 (List.nodup_iff_pairwise_ne.1 hndps)
    exact this.imp fun h => Ne.symm h
  unfold parMovesJ at hc
  rw [← hps] at hc
  dsimp only at hc
  split at hc
  · -- no source is a target: the moves in order
    rename_i hall
    have hpw : ps.Pairwise fun p q => q.2.vname ≠ p.1.vname ∧ q.1.vname ≠ p.1.vname := by
      refine hpwt.imp_of_mem fun {p q} hp hq h => ⟨?_, h⟩
      intro he
      have hq' := List.all_eq_true.1 (List.all_eq_true.1 hall q hq) p hp
      have hg := goodV_inj (hgood q (hmem q hq)).2 (hgood p (hmem p hp)).1 he
      simp [hg] at hq'
    obtain ⟨s', hsem, hscs, hmm, hres, hfr, harr⟩ :=
      sem_movesOf aS opS gd prog hpw (c' := c') hc htyps
    exact ⟨s', hsem, hscs, hmm, hres, fun z hz _ => hfr z hz, harr⟩
  · -- staged through the temporaries
    have hA : (ps.zipIdx.map fun q => asgn (mkV 'r' (D + q.2) q.1.1.vtype) (pv q.1.2)) =
        movesOf (ps.zipIdx.map fun q => (stageV D q, q.1.2)) := by
      simp [movesOf, stageV]
    have hB : (ps.zipIdx.map fun q => asgn q.1.1 (pv (mkV 'r' (D + q.2) q.1.1.vtype))) =
        movesOf (ps.zipIdx.map fun q => (q.1.1, stageV D q)) := by
      simp [movesOf, stageV]
    rw [hA, hB] at hc
    obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv hc
    have hq : ∀ q ∈ ps.zipIdx, q.1 ∈ ps := fun q hq =>
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hq)
    have hpq : ∀ p ∈ ps, ∃ i, (p, i) ∈ ps.zipIdx := fun p hp => by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
      exact ⟨i, List.mem_zipIdx_iff_getElem?.2 hi⟩
    have hsn : ∀ q, (stageV D q).vname = nameOf 'r' (D + q.2) q.1.1.vtype := fun _ => rfl
    have hpwA : (ps.zipIdx.map fun q => (stageV D q, q.1.2)).Pairwise
        fun p q => q.2.vname ≠ p.1.vname ∧ q.1.vname ≠ p.1.vname := by
      refine pairwise_zipIdx_map ps _ _ fun i j hi hj hij => ⟨?_, ?_⟩
      · exact hsrc _ (hmem _ (List.getElem_mem hj)) _ _
      · intro he
        have := (nameOf_inj (hsn _ ▸ hsn _ ▸ he)).2.1
        omega
    have htyA : MovesTyped s.evm (ps.zipIdx.map fun q => (stageV D q, q.1.2)) := by
      intro p hp
      obtain ⟨q, hqm, rfl⟩ := List.mem_map.1 hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := htyps _ (hq q hqm)
      exact ⟨h1, h2, h3, h4, by rw [h5]; rfl⟩
    obtain ⟨s1, hsem1, hscs1, hmm1, hres1, hfr1, harr1⟩ :=
      sem_movesOf aS opS gd prog hpwA ha' htyA
    have hpwt' := List.pairwise_iff_getElem.1 hpwt
    have hpwB : (ps.zipIdx.map fun q => (q.1.1, stageV D q)).Pairwise
        fun p q => q.2.vname ≠ p.1.vname ∧ q.1.vname ≠ p.1.vname := by
      refine pairwise_zipIdx_map ps _ _ fun i j hi hj hij => ⟨?_, hpwt' i j hi hj hij⟩
      exact fun he => htgt _ (hmem _ (List.getElem_mem hi)) j _ he.symm
    have hstage : ∀ q ∈ ps.zipIdx, s1.evm (mvar (stageV D q)) = s.evm (mvar q.1.2) :=
      fun q hqm => hres1 _ (List.mem_map.2 ⟨q, hqm, rfl⟩)
    have htyB : MovesTyped s1.evm (ps.zipIdx.map fun q => (q.1.1, stageV D q)) := by
      intro p hp
      obtain ⟨q, hqm, rfl⟩ := List.mem_map.1 hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := htyps _ (hq q hqm)
      exact ⟨h1, h1, rfl, by rw [hstage q hqm]; exact h4, by rw [hstage q hqm]; exact h5⟩
    obtain ⟨s2, hsem2, hscs2, hmm2, hres2, hfr2, harr2⟩ :=
      sem_movesOf aS opS gd prog hpwB hb' htyB
    refine ⟨s2, ?_, hscs2.trans hscs1, hmm2.trans hmm1, fun p hp => ?_, fun z hz hzt => ?_,
      fun h => harr2 (harr1 h)⟩
    · rw [typeC_append]
      exact ComJasminBridgeProgram.sem_append aS opS gd prog hsem1 hsem2
    · obtain ⟨i, hi⟩ := hpq p hp
      rw [hres2 _ (List.mem_map.2 ⟨(p, i), hi, rfl⟩)]
      exact hstage _ hi
    · rw [hfr2 z ?_, hfr1 z ?_]
      · intro p hp
        obtain ⟨q, hqm, rfl⟩ := List.mem_map.1 hp
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hqm)
        exact hzt _ hlt _
      · intro p hp
        obtain ⟨q, hqm, rfl⟩ := List.mem_map.1 hp
        exact hz q.1 (hq q hqm)
end Moves

/-! ## 2. Blocks of carried variables -/

/-- The block of `t :: cs` is the variable of `t` at the top depth followed by the block of
`cs`. -/
theorem blockVars_cons (base : Nat) (t : JasminTy) (cs : List JasminTy) :
    blockVars base (t :: cs) = mkV 'r' (base + cs.length) (styOf t) :: blockVars base cs := by
  simp only [blockVars, List.zipIdx_cons, List.map_cons, List.length_cons, Nat.add_sub_cancel,
    Nat.sub_zero, List.cons.injEq, true_and]
  rw [List.zipIdx_succ, List.map_map]
  congr 1
  funext q
  simp only [Function.comp_apply]
  congr 2
  omega

/-- The block of no types is empty. -/
@[simp] theorem blockVars_nil (base : Nat) : blockVars base [] = [] := rfl

/-- A block has one variable per type. -/
@[simp] theorem length_blockVars (base : Nat) (cs : List JasminTy) :
    (blockVars base cs).length = cs.length := by
  simp [blockVars]

/-- A variable of a block is a binding at a depth of the block. -/
theorem mem_blockVars {base : Nat} {cs : List JasminTy} {x : JVar} (h : x ∈ blockVars base cs) :
    ∃ k s, base ≤ k ∧ k < base + cs.length ∧ x = mkV 'r' k s := by
  induction cs with
  | nil => simp at h
  | cons t cs ih =>
      rw [blockVars_cons] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, _, by omega, by simp, rfl⟩
      · obtain ⟨k, s, h1, h2, rfl⟩ := ih h
        exact ⟨k, s, h1, by simp; omega, rfl⟩

/-- The variables of a block have distinct names. -/
theorem nodup_blockVars (base : Nat) (cs : List JasminTy) :
    ((blockVars base cs).map fun x => x.vname).Nodup := by
  induction cs with
  | nil => simp
  | cons t cs ih =>
      rw [blockVars_cons, List.map_cons, List.nodup_cons]
      refine ⟨fun h => ?_, ih⟩
      obtain ⟨x, hx, he⟩ := List.mem_map.1 h
      obtain ⟨k, s, -, hk, rfl⟩ := mem_blockVars hx
      have := (nameOf_inj he).2.1
      omega

/-- An argument or a binding below `d` is named apart from every binding at a depth from
`d`. -/
theorem envBelow_ne_ge {d : Nat} {v : JVar} (h : EnvBelow d v) {k : Nat} (hk : d ≤ k)
    (s0 : ASType) : v.vname ≠ nameOf 'r' k s0 := by
  rcases h with ⟨k', s, rfl⟩ | ⟨k', s, hk', rfl⟩
  · exact nameOf_ne (by decide) _ _ _ _
  · intro e
    have := (nameOf_inj e).2.1
    omega

/-! ## 3. Appended contexts -/

open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend inlHom inrHom
  lookup_inlHom lookup_inrHom)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (var_append_cases
  varIndex_inlHom varIndex_inrHom)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (varIndex_lt)

/-! ## 4. Agreement of blocks -/

omit [MemModel Mem] in
/-- A list of variables that agrees with a tuple agrees at every variable of its context. -/
theorem resAgrees_lookup {s : Estate SyscallState Mem} :
    ∀ {cs : List JasminTy} {xs : List JVar} {r : HVector (fun t => ⟦t⟧) cs},
      JazzResAgrees xs r s → ∀ {t : JasminTy} (u : Ctxt.Var cs t),
        JazzVarAgrees (xs.getD (varIndex u) dfltV) t (u.lookup r) s.evm
  | _ :: _, x :: xs, .cons a r, h, _, .here => h.1
  | _ :: _, x :: xs, .cons a r, h, _, .there u => by
      show JazzVarAgrees ((x :: xs).getD (varIndex u + 1) dfltV) _ (u.lookup r) s.evm
      simpa using resAgrees_lookup h.2 u
  | [], [], .nil, _, _, u => nomatch u

omit [MemModel Mem] in
/-- A list of variables that agrees with a tuple has its length. -/
theorem resAgrees_length {s : Estate SyscallState Mem} :
    ∀ {cs : List JasminTy} {xs : List JVar} {r : HVector (fun t => ⟦t⟧) cs},
      JazzResAgrees xs r s → xs.length = cs.length
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons _ _, h => by simp [resAgrees_length h.2]
  | [], _ :: _, .nil, h => h.elim
  | _ :: _, [], .cons _ _, h => h.elim

omit [MemModel Mem] in
/-- **Moves into a block.** When every variable of the block of `cs` holds, in `s'`, what
the variable of the same position of `xs` holds in `s`, the block agrees in `s'` with the
tuple `xs` agrees with in `s`. -/
theorem resAgrees_blockVars {s s' : Estate SyscallState Mem} (base : Nat) :
    ∀ {cs : List JasminTy} {xs : List JVar} {r : HVector (fun t => ⟦t⟧) cs},
      JazzResAgrees xs r s →
      (∀ p ∈ (blockVars base cs).zip xs, s'.evm (mvar p.1) = s.evm (mvar p.2)) →
      JazzResAgrees (blockVars base cs) r s'
  | [], [], .nil, _, _ => trivial
  | t :: cs, x :: xs, .cons a r, h, hm => by
      rw [blockVars_cons] at hm ⊢
      refine ⟨⟨rfl, ?_⟩, resAgrees_blockVars base h.2 fun p hp =>
        hm p (List.mem_cons_of_mem _ hp)⟩
      rw [hm _ List.mem_cons_self]
      exact h.1.2
  | [], _ :: _, .nil, h, _ => h.elim
  | _ :: _, [], .cons _ _, h, _ => h.elim

/-- A value that agrees with a dialect value of a type of `tyOkB` is defined and has the
mirror type of that type. -/
theorem valAgrees_typed {t : JasminTy} (ht : tyOkB t = true) {a : ⟦t⟧} {v : Value}
    (h : JazzValAgrees t a v) {x : JVar} (hx : x.vtype = styOf t) :
    v.isDefined = true ∧ v.typeOf = evalAtype (mvar x).vtype := by
  cases t with
  | reg w =>
      subst h
      rw [mvar_vtype_reg hx (ne_512_of_bitOk ht)]
      exact ⟨rfl, rfl⟩
  | stackArr w n =>
      obtain ⟨arr, rfl, -⟩ := h
      have hw : w ≠ 512 := by simp [tyOkB, widthOkB] at ht; omega
      rw [mvar_vtype_arr hx hw]
      exact ⟨rfl, rfl⟩
  | inlineInt =>
      subst h
      simp [mvar, hx, styOf, ptyOf, CatCrypt.Crypto.Jasmin.Jazz.PType.toSType, translateSTypeExt,
        translateSType, Value.isDefined, Value.typeOf, evalAtype]
  | bool =>
      subst h
      simp [mvar, hx, styOf, ptyOf, CatCrypt.Crypto.Jasmin.Jazz.PType.toSType, translateSTypeExt,
        translateSType, Value.isDefined, Value.typeOf, evalAtype]

omit [MemModel Mem] in
/-- The moves from the variables of a tuple of types of `tyOkB` into a block are typed. -/
theorem resAgrees_movesTyped {s : Estate SyscallState Mem} (base : Nat) :
    ∀ {cs : List JasminTy} {xs : List JVar} {r : HVector (fun t => ⟦t⟧) cs},
      cs.all tyOkB = true → JazzResAgrees xs r s →
      MovesTyped s.evm ((blockVars base cs).zip xs)
  | [], [], .nil, _, _ => by simp [MovesTyped]
  | t :: cs, x :: xs, .cons a r, hok, h => by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      rw [blockVars_cons, List.zip_cons_cons]
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · obtain ⟨hd, htp⟩ := valAgrees_typed hok.1 h.1.2 (x := mkV 'r' (base + cs.length) (styOf t)) rfl
        exact ⟨styOf_ne_U512 hok.1, by rw [OkV, h.1.1]; exact styOf_ne_U512 hok.1, h.1.1.symm,
          hd, htp⟩
      · exact resAgrees_movesTyped base hok.2 h.2 p hp
  | [], _ :: _, .nil, _, h => h.elim
  | _ :: _, [], .cons _ _, _, h => h.elim

/-- An entry of the left part of an appended environment. -/
theorem getD_append_lt {l l' : List JVar} {i : Nat} (h : i < l.length) :
    (l ++ l').getD i dfltV = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, List.getElem?_eq_getElem h]

/-- An entry of the right part of an appended environment. -/
theorem getD_append_ge {l l' : List JVar} {i : Nat} (h : l.length ≤ i) :
    (l ++ l').getD i dfltV = l'.getD (i - l.length) dfltV := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-! ## 5. Store agreement over frames -/

omit [MemModel Mem] in
/-- **Store agreement on a block.** A store that agrees with `V` at the depth `d`, and whose
block of `cs` at `d` agrees with `acc`, agrees with the appended valuation on the
environment extended by the block, at the depth past the block. -/
theorem storeAgrees_block {env : List JVar} {d : Nat} {L : Nat → Prop}
    {Γ : Ctxt jasminDialect} {V : Ctxt.Valuation Γ} {s : Estate SyscallState Mem}
    (hs : JazzStoreAgrees env d L V s) {cs : List JasminTy} {acc : HVector (fun t => ⟦t⟧) cs}
    (hacc : JazzResAgrees (blockVars d cs) acc s) {L' : Nat → Prop}
    (hL : ∀ i, L' i → cs.length ≤ i → L (i - cs.length)) :
    JazzStoreAgrees (blockVars d cs ++ env) (d + cs.length) L'
      (hvAppend (f := fun t => ⟦t⟧) acc V) s := by
  have hlen := length_blockVars d cs
  refine ⟨fun {t} v hl => ?_, fun i hl => ?_, fun i j hi hj he => ?_, hs.arrTyped⟩
  · rcases var_append_cases v with ⟨u, rfl⟩ | ⟨w, rfl⟩
    · rw [varIndex_inlHom, lookup_inlHom]
      have hu := varIndex_lt u
      rw [getD_append_lt (by omega)]
      have := resAgrees_lookup hacc u
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some] at this
    · rw [varIndex_inrHom, lookup_inrHom]
      rw [varIndex_inrHom] at hl
      rw [getD_append_ge (by omega), hlen, Nat.add_sub_cancel_left]
      have := hL _ hl (by omega)
      rw [Nat.add_sub_cancel_left] at this
      exact hs.agree w this
  · by_cases hi : i < cs.length
    · rw [getD_append_lt (by omega)]
      obtain ⟨k, s0, h1, h2, he⟩ := mem_blockVars (List.getElem_mem (l := blockVars d cs)
        (n := i) (by omega))
      rw [he]
      exact Or.inr ⟨k, s0, h2, rfl⟩
    · rw [getD_append_ge (by omega), hlen]
      exact (hs.below _ (hL i hl (by omega))).mono (by omega)
  · by_cases hi' : i < cs.length <;> by_cases hj' : j < cs.length
    · rw [getD_append_lt (by omega), getD_append_lt (by omega)] at he
      have hnd := nodup_blockVars d cs
      exact (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := by simp; omega)
        (hj := by simp; omega)).1 (by simpa using he)
    · rw [getD_append_lt (by omega), getD_append_ge (by omega)] at he
      simp only [hlen] at he
      obtain ⟨k, s0, h1, -, hk⟩ := mem_blockVars (List.getElem_mem (l := blockVars d cs)
        (n := i) (by omega))
      rw [hk] at he
      exact absurd he.symm (envBelow_ne_ge (hs.below _ (hL j hj (by omega))) h1 s0)
    · rw [getD_append_ge (by omega), getD_append_lt (by omega)] at he
      simp only [hlen] at he
      obtain ⟨k, s0, h1, -, hk⟩ := mem_blockVars (List.getElem_mem (l := blockVars d cs)
        (n := j) (by omega))
      rw [hk] at he
      exact absurd he (envBelow_ne_ge (hs.below _ (hL i hi (by omega))) h1 s0)
    · rw [getD_append_ge (by omega), getD_append_ge (by omega), hlen] at he
      have := hs.inj _ _ (hL i hi (by omega)) (hL j hj (by omega)) he
      omega

omit [MemModel Mem] in
/-- Store agreement carries over to a state that holds the same values at the live
variables and keeps arrays at their sizes, and to a smaller set of live indices. -/
theorem storeAgrees_frame {env : List JVar} {d : Nat} {L : Nat → Prop}
    {Γ : Ctxt jasminDialect} {V : Ctxt.Valuation Γ} {s s' : Estate SyscallState Mem}
    (hs : JazzStoreAgrees env d L V s) {L' : Nat → Prop} (hL : ∀ i, L' i → L i)
    (hfr : ∀ i, L' i → s'.evm (mvar (env.getD i dfltV)) = s.evm (mvar (env.getD i dfltV)))
    (harr : VmArrTyped s'.evm) : JazzStoreAgrees env d L' V s' :=
  ⟨fun v hl => by
      have := hs.agree v (hL _ hl)
      exact ⟨this.1, by rw [hfr _ hl]; exact this.2⟩,
    fun i hl => hs.below i (hL i hl), fun i j hi hj => hs.inj i j (hL i hi) (hL j hj), harr⟩

/-! ## 6. The two mirror loops -/

section Loops
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- **Counted mirror loop.** For the loop `while (e) { body }` and an invariant `Inv j` of
the states after `j` runs of the body: when `e` evaluates to `j < N` from every state of
`Inv j` with `j ≤ N`, and the body runs from every state of `Inv j` with `j < N` to a
state of `Inv (j + 1)`, the loop runs from a state of `Inv j` to a state of `Inv N`. -/
theorem semIr_while_count {al : CatCrypt.Crypto.Jasmin.CoqSemMirror.Align}
    {ii : CatCrypt.Crypto.Jasmin.CoqSemMirror.InstrInfo} {e : MPexpr} {bodyc : List MInstr}
    (N : Nat) (Inv : Nat → Estate SyscallState Mem → Prop)
    (hcond : ∀ j σ, j ≤ N → Inv j σ →
      semPexpr (Mem := Mem) true gd opS σ e = .ok (.Vbool (decide (j < N))))
    (hstep : ∀ j σ, j < N → Inv j σ → ∃ σ', Sem aS opS gd prog σ bodyc σ' ∧ Inv (j + 1) σ') :
    ∀ m j σ, j + m = N → Inv j σ →
      ∃ σ', SemIr aS opS gd prog σ (.Cwhile al [] e ii bodyc) σ' ∧ Inv N σ' := by
  intro m
  induction m with
  | zero =>
      intro j σ hj hinv
      subst hj
      refine ⟨σ, .Ewhile_false _ _ _ _ _ _ _ (.Eskip _) ?_, by simpa using hinv⟩
      rw [hcond _ _ (by omega) hinv]
      simp
  | succ m ih =>
      intro j σ hj hinv
      obtain ⟨σ1, hb, hinv1⟩ := hstep j σ (by omega) hinv
      obtain ⟨σ', hw, hinv'⟩ := ih (j + 1) σ1 (by omega) hinv1
      refine ⟨σ', .Ewhile_true _ _ _ _ _ _ _ _ _ (.Eskip _) ?_ hb hw, hinv'⟩
      rw [hcond _ _ (by omega) hinv]
      simp; omega

/-- **Exit-flag mirror loop.** For the loop `while { body } (e)` simulating the iteration
`step` of an exit-flag loop: when the body runs from every state of `Inv acc` at a tuple
`acc` of `P`, whenever `step acc = some r`, to a state of `Inv r.tail` at which `e`
evaluates to the bit of `r`, the loop runs from a state of `Inv acc` to a state of the
tuple the iteration returns, given `P` at every tuple the iteration reaches. -/
theorem semIr_while_flag {cs : List JasminTy}
    (step : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs)))
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (Inv : Ctxt.Valuation (d := jasminDialect) cs → Estate SyscallState Mem → Prop)
    {al : CatCrypt.Crypto.Jasmin.CoqSemMirror.Align}
    {ii : CatCrypt.Crypto.Jasmin.CoqSemMirror.InstrInfo} {e : MPexpr} {bodyc : List MInstr}
    (hstep : ∀ acc σ, Inv acc σ → P acc → ∀ r, step acc = some r →
      ∃ σ', Sem aS opS gd prog σ bodyc σ' ∧
        semPexpr (Mem := Mem) true gd opS σ' e =
          .ok (.Vbool (HasBoolBit.toBool (d := jasminDialect) r.head)) ∧ Inv r.tail σ') :
    ∀ fuel acc σ accF, NFProg.whileIter step fuel acc = some accF → Inv acc σ →
      (∀ n acc', whileStates step n acc = some acc' → P acc') →
      ∃ σ', SemIr aS opS gd prog σ (.Cwhile al bodyc e ii []) σ' ∧ Inv accF σ' := by
  intro fuel
  induction fuel with
  | zero => intro acc σ accF h; simp [NFProg.whileIter] at h
  | succ f ih =>
      intro acc σ accF h hinv hP
      simp only [NFProg.whileIter, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨r, hr, h⟩ := h
      obtain ⟨σ1, hb, hc, hinv1⟩ := hstep acc σ hinv (hP 0 acc rfl) r hr
      by_cases hbit : HasBoolBit.toBool (d := jasminDialect) r.head = true
      · rw [if_pos hbit] at h
        obtain ⟨σ', hw, hinv'⟩ := ih r.tail σ1 accF h hinv1 fun n acc' h' =>
          hP (n + 1) acc' (by simp [whileStates, hr, hbit, h'])
        exact ⟨σ', .Ewhile_true _ _ _ _ _ _ _ _ _ hb (by rw [hc, hbit]) (.Eskip _) hw, hinv'⟩
      · rw [if_neg hbit, Option.some.injEq] at h
        subst h
        refine ⟨σ1, .Ewhile_false _ _ _ _ _ _ _ hb ?_, hinv1⟩
        rw [hc]
        simp only [Bool.not_eq_true] at hbit
        rw [hbit]

end Loops

/-! ## 7. Depths, loop numbers and written variables -/

/-- The lowering of a region returns at a depth no lower than its start and leaves the
next loop number no lower than its start. -/
theorem nfToJasminBody_mono :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
      {env : List JVar} {d n : Nat} {out : JOut}, nfToJasminBody env p d n = some out →
      d ≤ out.depth ∧ n ≤ out.next := by
  intro Γ ts p
  induction p with
  | ret vs =>
      intro env d n out h
      simp only [nfToJasminBody, Option.some.injEq] at h
      subst h; exact ⟨le_refl _, le_refl _⟩
  | var e k ih =>
      intro env d n out h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨cx, -, rk, hrk, rfl⟩ := h
      have := ih hrk
      exact ⟨by simp [JOut.pre]; omega, by simp [JOut.pre]; omega⟩
  | forLoop count inits body k ihb ihk =>
      intro env d n out h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hrk, rfl⟩ := h
      have h1 := ihb hb
      have h2 := ihk hrk
      exact ⟨by simp [JOut.pre]; omega, by simp [JOut.pre]; omega⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro env d n out h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨bt, hbt, be, hbe, rk, hrk, rfl⟩ := h
      have h1 := iht hbt
      have h2 := ihe hbe
      have h3 := ihk hrk
      exact ⟨by simp [JOut.pre]; omega, by simp [JOut.pre]; omega⟩
  | whileLoop inits body k ihb ihk =>
      intro env d n out h
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hrk, rfl⟩ := h
      have h1 := ihb hb
      have h2 := ihk hrk
      exact ⟨by simp [JOut.pre]; omega, by simp [JOut.pre]; omega⟩
  | call f args k ih =>
      intro env d n out h
      simp only [nfToJasminBody] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨rk, hrk, rfl⟩ := h
        have := ih hrk
        exact ⟨by simp [JOut.pre]; omega, by simp [JOut.pre]; omega⟩
      · exact absurd h (by simp)

/-- An array type. -/
def IsArrTy (s : ASType) : Prop := ∃ m, s = .sarr m

/-- **Written names.** The names the code of a region lowered in the environment `env` at
the depth `d` with the loop numbers from `n`, whose in-place stores reach the `loc`
innermost variables, may write: the scratch variables, the bindings at depths from `d`,
the loop counters from `n`, and the array variables among the `loc` innermost variables of
`env`. -/
def Writes (env : List JVar) (loc d n : Nat) (nm : String) : Prop :=
  Scratch nm ∨ (∃ k s, d ≤ k ∧ nm = nameOf 'r' k s) ∨ (∃ m s, n ≤ m ∧ nm = nameOf 'c' m s) ∨
    ∃ i < loc, nm = (env.getD i dfltV).vname ∧ IsArrTy (env.getD i dfltV).vtype

/-- The state `s'` after the code of a region lowered to `out` from the state `s`: the
returned variables hold the values `r` and are arguments or bindings below the depth at the
return, the memory and syscall state are unchanged, every variable outside the written
names is unchanged, and array variables hold arrays of their sizes. -/
structure RegionPost (env : List JVar) (loc d n : Nat) (out : JOut) {ts : List JasminTy}
    (r : HVector (fun t => ⟦t⟧) ts) (s s' : Estate SyscallState Mem) : Prop where
  /-- The returned variables hold the returned values. -/
  res : JazzResAgrees out.res r s'
  /-- The returned variables are arguments or bindings below the depth at the return. -/
  resBelow : ∀ x ∈ out.res, EnvBelow out.depth x
  /-- The syscall state is unchanged. -/
  scs : s'.escs = s.escs
  /-- The memory is unchanged. -/
  mem : s'.emem = s.emem
  /-- Every variable outside the written names is unchanged. -/
  frame : ∀ z : MVar, ¬ Writes env loc d n z.vname → s'.evm z = s.evm z
  /-- Array variables hold arrays of their sizes. -/
  arr : VmArrTyped s'.evm

/-- The result of an in-place store is an array. -/
theorem storeSrc_arr {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    {a : Nat} (h : storeSrc? e.op (hvIdxs e.args) = some a) : IsArrTy (styOf t) := by
  obtain ⟨op, hret, args⟩ := e
  subst hret
  cases op <;> first | exact ⟨_, rfl⟩ | simp [storeSrc?] at h

/-- The written names of a region of the continuation of a construct, with the block of
`cs` in front of the environment, are written names of the construct. -/
theorem writes_of_block {env : List JVar} {cs : List JasminTy} {loc d n n' : Nat} {nm : String}
    (h : Writes (blockVars d cs ++ env) (loc + cs.length) (d + cs.length) n' nm)
    (hn : n ≤ n') : Writes env loc d n nm := by
  rcases h with h | ⟨k, s, hk, h⟩ | ⟨m, s, hm, h⟩ | ⟨i, hi, h, harr⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨k, s, by omega, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, s, by omega, h⟩))
  · by_cases hic : i < cs.length
    · rw [getD_append_lt (by simpa using hic)] at h
      obtain ⟨k, s, hk, -, he⟩ := mem_blockVars (List.getElem_mem (l := blockVars d cs)
        (n := i) (by simpa using hic))
      rw [he] at h
      exact Or.inr (Or.inl ⟨k, s, hk, h⟩)
    · rw [getD_append_ge (by simp; omega), length_blockVars] at h harr
      exact Or.inr (Or.inr (Or.inr ⟨i - cs.length, by omega, h, harr⟩))

/-- The written names of an inner region whose in-place stores reach only bindings at
depths from `d` are written names of the enclosing region at `d`. -/
theorem writes_of_inner {env env' : List JVar} {loc loc' d d' n n' : Nat} {nm : String}
    (h : Writes env' loc' d' n' nm) (hd : d ≤ d') (hn : n ≤ n')
    (hloc : ∀ i < loc', ∃ k s, d ≤ k ∧ (env'.getD i dfltV).vname = nameOf 'r' k s) :
    Writes env loc d n nm := by
  rcases h with h | ⟨k, s, hk, h⟩ | ⟨m, s, hm, h⟩ | ⟨i, hi, h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨k, s, by omega, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, s, by omega, h⟩))
  · obtain ⟨k, s, hk, he⟩ := hloc i hi
    exact Or.inr (Or.inl ⟨k, s, hk, h.trans he⟩)

/-- An argument or a binding below `d` is not a written name of a region at a depth from
`d` whose in-place stores reach only bindings at depths from `d`. -/
theorem not_writes_of_below {env : List JVar} {loc d d' n : Nat} {v : JVar}
    (h : EnvBelow d v) (hd : d ≤ d')
    (hloc : ∀ i < loc, ∃ k s, d ≤ k ∧ (env.getD i dfltV).vname = nameOf 'r' k s) :
    ¬ Writes env loc d' n v.vname := by
  rintro (h' | ⟨k, s, hk, h'⟩ | ⟨m, s, -, h'⟩ | ⟨i, hi, h', -⟩)
  · exact h.not_scratch h'
  · exact envBelow_ne_ge h (by omega) s h'
  · rcases h with ⟨k, s', rfl⟩ | ⟨k, s', -, rfl⟩ <;> exact nameOf_ne (by decide) _ _ _ _ h'
  · obtain ⟨k, s, hk, he⟩ := hloc i hi
    exact envBelow_ne_ge h hk s (h'.trans he)

/-- An argument or a binding is a well-formed variable. -/
theorem goodV_of_below {d : Nat} {v : JVar} (h : EnvBelow d v) : GoodV v := by
  rcases h with ⟨k, s, rfl⟩ | ⟨k, s, -, rfl⟩ <;> exact goodV_mkV _ _ _

/-- A variable of a block is a well-formed variable. -/
theorem goodV_of_block {base : Nat} {cs : List JasminTy} {x : JVar}
    (h : x ∈ blockVars base cs) : GoodV x := by
  obtain ⟨k, s, -, -, rfl⟩ := mem_blockVars h
  exact goodV_mkV _ _ _

/-- The translation of a branch. -/
theorem translateInstrRExt_cif_inv {c : APExpr} {t e : List AInstrR} {i' : MInstrR}
    (h : translateInstrRExt (.Cif c t e) = some i') :
    ∃ c' t' e', translatePExprExt c = some c' ∧ translateCmdExt t = some t' ∧
      translateCmdExt e = some e' ∧ i' = .Cif c' t' e' := by
  simp only [translateInstrRExt] at h
  split at h
  · rename_i c' t' e' h1 h2 h3
    exact ⟨c', t', e', h1, h2, h3, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- The translation of a loop. -/
theorem translateInstrRExt_cwhile_inv {b : List AInstrR} {c : APExpr} {a : List AInstrR}
    {i' : MInstrR} (h : translateInstrRExt (.Cwhile b c a) = some i') :
    ∃ b' c' a', translateCmdExt b = some b' ∧ translatePExprExt c = some c' ∧
      translateCmdExt a = some a' ∧ i' = .Cwhile .NoAlign b' c' () a' := by
  simp only [translateInstrRExt] at h
  split at h
  · rename_i b' c' a' h1 h2 h3
    exact ⟨b', c', a', h1, h2, h3, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- The typed condition `x != 0` over a `u64` variable holding `w`. -/
theorem sem_nz {opS : OpSem} {gd : GlobDecls} (hop : JazzOpAgrees opS)
    {s : Estate SyscallState Mem} {x : JVar}
    {w : BitVec 64} (hx : s.evm (mvar x) = .Vword .U64 w) :
    semPexpr (Mem := Mem) true gd opS s (typeE .abool (mnz (mvi x))) = .ok (.Vbool (w != 0)) := by
  have h0 : semPexpr (Mem := Mem) true gd opS s (.Papp1 (.Oword_of_int .U64) (.Pconst 0)) =
      .ok (.Vword .U64 (BitVec.ofInt 64 0)) := semPexpr_wconst opS gd hop (ws := .U64) rfl s 0
  rw [typeE_mnz, semPexpr_papp2 opS gd (semPexpr_mpv opS gd (x := mvi x) hx rfl) h0]
  exact (hop.neq .U64 rfl w _).trans rfl

/-- The `u64` word of a bit is nonzero exactly at the bit `1`. -/
theorem bit_ne_zero (b : BitVec 1) :
    (BitVec.ofNat 64 b.toNat != 0) = decide (b = 1#1) := by
  revert b; decide

/-- The counter `N - j` of a counted loop is nonzero exactly before the last trip. -/
theorem count_ne_zero {N j : Nat} (hN : N < 2 ^ 64) (hj : j ≤ N) :
    (BitVec.ofNat 64 (N - j) != 0) = decide (j < N) := by
  by_cases h : j < N
  · have h1 : (BitVec.ofNat 64 (N - j)).toNat ≠ 0 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    simp only [h, decide_true, bne_iff_ne, ne_eq]
    intro he; exact h1 (by rw [he]; rfl)
  · rw [show N - j = 0 by omega]
    simp [h]

/-- The variable of a `u64` type has the mirror type `u64`. -/
theorem mvar_u64 {x : JVar} (h : x.vtype = u64) : (mvar x).vtype = .aword .U64 := by
  simp [mvar, h, translateSTypeExt, translateSType, translateWSize]

/-- The prefix folds of a fold over `List.range N` that succeeds succeed, one trip at a
time. -/
theorem foldlM_range_step {α : Type} (F : α → Nat → Option α) {N j : Nat} {a aN aj : α}
    (hN : (List.range N).foldlM F a = some aN) (hj : j < N)
    (haj : (List.range j).foldlM F a = some aj) :
    ∃ a', F aj j = some a' ∧ (List.range (j + 1)).foldlM F a = some a' := by
  have hsplit : List.range N = List.range (j + 1) ++ (List.range (N - (j + 1))).map
      (j + 1 + ·) := by
    rw [← List.range_add]; congr 1; omega
  have hstep : (List.range (j + 1)).foldlM F a = F aj j := by
    rw [List.range_succ, List.foldlM_append, haj]; simp
  rw [hsplit, List.foldlM_append, hstep] at hN
  cases hF : F aj j with
  | none => rw [hF] at hN; exact absurd hN (by simp)
  | some a' => exact ⟨a', rfl, hstep.trans hF⟩

omit [MemModel Mem] in
/-- A list of variables agrees in a state that holds the same values at its variables. -/
theorem resAgrees_frame {s s' : Estate SyscallState Mem} :
    ∀ {cs : List JasminTy} {xs : List JVar} {r : HVector (fun t => ⟦t⟧) cs},
      JazzResAgrees xs r s → (∀ x ∈ xs, s'.evm (mvar x) = s.evm (mvar x)) →
      JazzResAgrees xs r s'
  | [], [], .nil, _, _ => trivial
  | _ :: _, x :: xs, .cons a r, h, hm =>
      ⟨⟨h.1.1, by rw [hm x List.mem_cons_self]; exact h.1.2⟩,
        resAgrees_frame h.2 fun y hy => hm y (List.mem_cons_of_mem _ hy)⟩
  | [], _ :: _, .nil, h, _ => h.elim
  | _ :: _, [], .cons _ _, h, _ => h.elim

/-- The moves from arguments and bindings below `base` into the block at `base` read no
target and write distinct targets. -/
theorem pairwise_zip_block {base : Nat} {cs : List JasminTy} {xs : List JVar}
    (hlen : xs.length = cs.length) (hxs : ∀ x ∈ xs, EnvBelow base x) :
    ((blockVars base cs).zip xs).Pairwise
      fun p q => q.2.vname ≠ p.1.vname ∧ q.1.vname ≠ p.1.vname := by
  have hnd : (((blockVars base cs).zip xs).map fun p => p.1.vname).Nodup := by
    have : (((blockVars base cs).zip xs).map fun p => p.1.vname) =
        ((((blockVars base cs).zip xs).map Prod.fst).map fun x => x.vname) := by
      rw [List.map_map]; rfl
    rw [this, List.map_fst_zip (by simp [hlen])]
    exact nodup_blockVars base cs
  refine (List.pairwise_map.1 (List.nodup_iff_pairwise_ne.1 hnd)).imp_of_mem
    fun {p q} hp hq h => ⟨fun he => ?_, Ne.symm h⟩
  obtain ⟨k, s, hk, -, hp1⟩ := mem_blockVars (List.of_mem_zip hp).1
  rw [hp1] at he
  exact envBelow_ne_ge (hxs _ (List.of_mem_zip hq).2) hk s he

/-! ## 8. The simulation of a region -/

section Sim
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
  (E : CallEnv jasminDialect) (fuel : Nat)

/-- Position `i` of the block at `base` is the binding at depth `base + (cs.length - 1 - i)`. -/
theorem getElem_blockVars (base : Nat) (cs : List JasminTy) (i : Nat)
    (hi : i < (blockVars base cs).length) :
    (blockVars base cs)[i] =
      mkV 'r' (base + (cs.length - 1 - i)) (styOf (cs[i]'(by simpa using hi))) := by
  simp [blockVars]

/-- **Block shift.** The moves of the block at `d + 1` down to the block at `d`, last
position first, run to a state in which the block at `d` agrees with what the block at
`d + 1` agreed with, and every variable that is not a binding at a depth from `d` is
unchanged. -/
theorem sem_shift {d : Nat} {cs : List JasminTy} {acc : HVector (fun t => ⟦t⟧) cs}
    {s : Estate SyscallState Mem} (hok : cs.all tyOkB = true)
    (hcar : JazzResAgrees (blockVars (d + 1) cs) acc s) {c' : List MInstr}
    (hc : translateCmdExt (seqMoves ((blockVars d cs).zip (blockVars (d + 1) cs)).reverse) =
      some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ JazzResAgrees (blockVars d cs) acc s' ∧
      s'.escs = s.escs ∧ s'.emem = s.emem ∧
      (∀ z : MVar, (∀ k s0, d ≤ k → z.vname ≠ nameOf 'r' k s0) → s'.evm z = s.evm z) ∧
      (VmArrTyped s.evm → VmArrTyped s'.evm) := by
  have hpw : ((blockVars d cs).zip (blockVars (d + 1) cs)).reverse.Pairwise
      fun p q => q.2.vname ≠ p.1.vname ∧ q.1.vname ≠ p.1.vname := by
    rw [List.pairwise_reverse, List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_zip, getElem_blockVars, List.length_zip, length_blockVars,
      Nat.min_self] at hi hj ⊢
    refine ⟨fun he => ?_, fun he => ?_⟩
    · have := (nameOf_inj he).2.1; omega
    · have := (nameOf_inj he).2.1; omega
  have hty := resAgrees_movesTyped d hok hcar
  obtain ⟨s', hsem, hscs, hmm, hres, hfr, harr⟩ := sem_movesOf aS opS gd prog hpw hc
    (fun p hp => hty p (List.mem_reverse.1 hp))
  refine ⟨s', hsem, resAgrees_blockVars d hcar fun p hp => hres p (List.mem_reverse.2 hp), hscs,
    hmm, fun z hz => hfr z fun p hp he => ?_, harr⟩
  obtain ⟨k, s0, hk, -, hp1⟩ := mem_blockVars (List.of_mem_zip (List.mem_reverse.1 hp)).1
  rw [hp1] at he
  exact hz k s0 hk he

/-- **Join moves.** The parallel moves from the variables `xs`, which agree with `r` and are
arguments or bindings below `D`, into the block of `cs` at `base` below `D`, run to a state
in which the block agrees with `r` and every variable that is not a binding at a depth from
`base` is unchanged. -/
theorem sem_join {base D : Nat} {cs : List JasminTy} {xs : List JVar}
    {r : HVector (fun t => ⟦t⟧) cs} {s : Estate SyscallState Mem} (hok : cs.all tyOkB = true)
    (hres : JazzResAgrees xs r s) (hxs : ∀ x ∈ xs, EnvBelow D x) (hD : base + cs.length ≤ D)
    {c' : List MInstr} (hc : translateCmdExt (parMovesJ D ((blockVars base cs).zip xs)) = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ JazzResAgrees (blockVars base cs) r s' ∧
      s'.escs = s.escs ∧ s'.emem = s.emem ∧
      (∀ z : MVar, (∀ k s0, base ≤ k → k < D + cs.length → z.vname ≠ nameOf 'r' k s0) →
        s'.evm z = s.evm z) ∧
      (VmArrTyped s.evm → VmArrTyped s'.evm) := by
  have hlen := resAgrees_length hres
  have hnd : (((blockVars base cs).zip xs).map fun p => p.1.vname).Nodup := by
    have : (((blockVars base cs).zip xs).map fun p => p.1.vname) =
        ((((blockVars base cs).zip xs).map Prod.fst).map fun x => x.vname) := by
      rw [List.map_map]; rfl
    rw [this, List.map_fst_zip (by simp [hlen])]
    exact nodup_blockVars base cs
  have htgt : ∀ p ∈ (blockVars base cs).zip xs, ∃ k s0, base ≤ k ∧ k < base + cs.length ∧
      p.1 = mkV 'r' k s0 := fun p hp => mem_blockVars (List.of_mem_zip hp).1
  obtain ⟨s', hsem, hscs, hmm, hres', hfr, harr⟩ := sem_parMovesJ aS opS gd prog D
    (fun p hp => ⟨goodV_of_block (List.of_mem_zip hp).1, goodV_of_below
      (hxs _ (List.of_mem_zip hp).2)⟩) hnd
    (fun p hp j s0 he => by
      obtain ⟨k, s1, -, hk, he'⟩ := htgt p hp
      rw [he'] at he
      have := (nameOf_inj he).2.1
      omega)
    (fun p hp j s0 => envBelow_ne_ge (hxs _ (List.of_mem_zip hp).2) (by omega) s0)
    hc (resAgrees_movesTyped base hok hres)
  refine ⟨s', hsem, resAgrees_blockVars base hres hres', hscs, hmm, fun z hz => hfr z ?_ ?_, harr⟩
  · intro p hp he
    obtain ⟨k, s1, hk, hk', he'⟩ := htgt p hp
    rw [he'] at he
    exact hz k _ hk (by omega) he
  · intro j hj s0
    simp only [List.length_zip, length_blockVars, hlen, Nat.min_self] at hj
    exact hz _ s0 (by omega) (by omega)

variable (SyscallState Mem) in
/-- **Region simulation.** The code `nfToJasminBody` emits for `p`, translated and typed,
runs from every state that agrees with `V` on the variables `p` reads, with the array
indices of the run of `p` in range, to a `RegionPost` state of the values `p` denotes. -/
def Sim {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) : Prop :=
  ∀ {loc : Nat} {env : List JVar} {d n : Nat} {out : JOut}, linGo p loc = true →
    nfToJasminBody env p d n = some out →
    ∀ {c' : List MInstr}, translateCmdExt out.code = some c' →
    ∀ {V : Ctxt.Valuation Γ} {r : HVector (fun t => ⟦t⟧) ts}, p.denoteAt E fuel V = some r →
    IdxInBounds E fuel p V →
    ∀ {s : Estate SyscallState Mem}, JazzStoreAgrees env d (fun i => usesIdx p i = true) V s →
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ RegionPost env loc d n out r s s'

/-- A return simulates its values. -/
theorem sim_ret {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (vs : HVector (fun t => Ctxt.Var Γ t) ts) :
    Sim SyscallState Mem aS opS gd prog E fuel (NFProg.ret vs) := by
  intro loc env d n out _ hout c' hc V r hden _ s hs
  simp only [nfToJasminBody, Option.some.injEq] at hout
  subst hout
  have hr : r = Expr.lookupArgs vs V := by
    simpa [NFProg.denoteAt, NFProg.denote] using hden.symm
  subst hr
  have hl : ∀ i ∈ hvIdxs vs, usesIdx (NFProg.ret vs) i = true := fun i hi => by
    simp [usesIdx, hi]
  refine ⟨s, sem_nil_step aS opS gd prog hc s, ⟨resAgrees_ret hs vs hl, fun x hx => ?_, rfl, rfl,
    fun _ _ => rfl, hs.arrTyped⟩⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact hs.below i (hl i hi)

/-- A binding simulates its operation and then its continuation. -/
theorem sim_var (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {ts : List JasminTy} (e : Expr jasminDialect Γ t)
    (k : NFProg jasminDialect (t :: Γ) ts) (ht : tyOkB t = true) (hok : opOkB e.op = true)
    (ih : Sim SyscallState Mem aS opS gd prog E fuel k) :
    Sim SyscallState Mem aS opS gd prog E fuel (NFProg.var e k) := by
  intro loc env d n out hlin hout c' hc V r hden hidx s hs
  simp only [linGo, Bool.and_eq_true] at hlin
  obtain ⟨hlin1, hlink⟩ := hlin
  simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hout
  obtain ⟨⟨cx, y⟩, hcx, rk, hrk, rfl⟩ := hout
  obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv hc
  obtain ⟨s1, hsem1, hp, hyt, hsrc⟩ := emitOp_sem aS opS gd prog haS hop e hok ht
    hs (fun i hi => by simp [usesIdx, hi]) hidx.1 hcx ha'
  have hden' : k.denoteAt E fuel (V.extend (e.denote V)) = some r := by
    simpa [NFProg.denoteAt, NFProg.denote] using hden
  have hai : ∀ {a}, storeSrc? e.op (hvIdxs e.args) = some a → a ∈ hvIdxs e.args := by
    intro a ha
    revert ha
    unfold storeSrc?
    split <;> simp_all
  -- the fresh or in-place variable is distinct from the other live variables
  have hne : ∀ i, usesIdx k (i + 1) = true → (env.getD i dfltV).vname ≠ y.vname := by
    intro i hi
    rcases hsrc with ⟨_, rfl⟩ | ⟨a, ha, rfl⟩
    · exact (hs.below i (by simp [usesIdx, hi])).ne_new _
    · rw [ha] at hlin1
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hlin1
      intro heq
      have := hs.inj i a (by simp [usesIdx, hi]) (by simp [usesIdx, hai ha]) heq
      subst this
      rw [hlin1.2] at hi
      exact Bool.false_ne_true hi
  have hyb : EnvBelow (d + 1) y := by
    rcases hsrc with ⟨_, rfl⟩ | ⟨a, ha, rfl⟩
    · exact Or.inr ⟨d, _, by omega, rfl⟩
    · exact (hs.below a (by simp [usesIdx, hai ha])).mono (by omega)
  have hs1 : JazzStoreAgrees (y :: env) (d + 1) (fun i => usesIdx k i = true)
      (V.extend (e.denote V)) s1 := by
    refine ⟨fun {t'} v hl => ?_, fun i hl => ?_, fun i j hi hj heq => ?_, hp.arr hs.arrTyped⟩
    · cases v with
      | here => exact ⟨hyt, hp.res⟩
      | there v =>
          have hl' : usesIdx (NFProg.var e k) (varIndex v) = true := by
            simp [usesIdx, show usesIdx k (varIndex v + 1) = true from hl]
          have ho := hs.agree v hl'
          refine ⟨ho.1, ?_⟩
          show JazzValAgrees t' (v.lookup V) (s1.evm (mvar (env.getD (varIndex v) dfltV)))
          rw [hp.frame _ (hne _ hl) (hs.below _ hl').not_scratch]
          exact ho.2
    · cases i with
      | zero => exact hyb
      | succ i =>
          exact (hs.below i (by simp [usesIdx, show usesIdx k (i + 1) = true from hl])).mono
            (by omega)
    · cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j => exact absurd heq.symm (hne j hj)
      | succ i =>
          cases j with
          | zero => exact absurd heq (hne i hi)
          | succ j =>
              exact congrArg (· + 1) (hs.inj i j
                (by simp [usesIdx, show usesIdx k (i + 1) = true from hi])
                (by simp [usesIdx, show usesIdx k (j + 1) = true from hj]) heq)
  obtain ⟨s2, hsem2, hpost⟩ := ih hlink hrk hb' hden' hidx.2 hs1
  -- the names the binding writes
  have hwr : ∀ nm, ¬ Writes env loc d n nm →
      ¬ Writes (y :: env) (loc + 1) (d + 1) n nm ∧ nm ≠ y.vname ∧ ¬ Scratch nm := by
    intro nm hn
    have hy : nm ≠ y.vname := by
      rintro rfl
      rcases hsrc with ⟨_, rfl⟩ | ⟨a, ha, rfl⟩
      · exact hn (Or.inr (Or.inl ⟨d, _, le_refl _, rfl⟩))
      · rw [ha] at hlin1
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlin1
        exact hn (Or.inr (Or.inr (Or.inr ⟨a, hlin1.1, rfl, hyt ▸ storeSrc_arr e ha⟩)))
    refine ⟨fun hw => ?_, hy, fun h => hn (Or.inl h)⟩
    rcases hw with h | ⟨k', s0, hk, h⟩ | h | ⟨i, hi, h, harr⟩
    · exact hn (Or.inl h)
    · exact hn (Or.inr (Or.inl ⟨k', s0, by omega, h⟩))
    · exact hn (Or.inr (Or.inr (Or.inl h)))
    · cases i with
      | zero => exact hy h
      | succ i => exact hn (Or.inr (Or.inr (Or.inr ⟨i, by omega, by simpa using h, by simpa using harr⟩)))
  refine ⟨s2, ?_, ⟨hpost.res, hpost.resBelow, hpost.scs.trans hp.scs, hpost.mem.trans hp.mem,
    fun z hz => ?_, hpost.arr⟩⟩
  · rw [typeC_append]
    exact ComJasminBridgeProgram.sem_append aS opS gd prog hsem1 hsem2
  · obtain ⟨h1, h2, h3⟩ := hwr _ hz
    rw [hpost.frame z h1]
    exact hp.frame z h2 h3

/-- **A branch and its join.** The code of a branch followed by the join moves into the
block of the results runs to a state in which the block agrees with the values of the
branch and every variable outside the written names of the branch is unchanged. -/
theorem branch_run {Γ : Ctxt jasminDialect} {rs : List JasminTy} (hok : rs.all tyOkB = true)
    {p : NFProg jasminDialect Γ rs} (ihp : Sim SyscallState Mem aS opS gd prog E fuel p)
    {env : List JVar} {d n0 : Nat} {bo : JOut} (hlin : linGo p 0 = true)
    (hbo : nfToJasminBody env p d n0 = some bo) {cb' : List MInstr}
    (hcb : translateCmdExt (bo.code ++ parMovesJ (bo.depth + rs.length)
      ((blockVars d rs).zip bo.res)) = some cb')
    {V : Ctxt.Valuation Γ} {rb : HVector (fun t => ⟦t⟧) rs} (hden : p.denoteAt E fuel V = some rb)
    (hidx : IdxInBounds E fuel p V) {s : Estate SyscallState Mem}
    (hs : JazzStoreAgrees env d (fun i => usesIdx p i = true) V s) :
    ∃ s2, Sem aS opS gd prog s (typeC cb') s2 ∧ JazzResAgrees (blockVars d rs) rb s2 ∧
      s2.escs = s.escs ∧ s2.emem = s.emem ∧
      (∀ z : MVar, ¬ Writes env 0 d n0 z.vname → s2.evm z = s.evm z) ∧ VmArrTyped s2.evm := by
  obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv hcb
  obtain ⟨s1, hsem1, hpost⟩ := ihp hlin hbo ha' hden hidx hs
  have hdep := (nfToJasminBody_mono p hbo).1
  obtain ⟨s2, hsem2, hres2, hscs2, hmm2, hfr2, harr2⟩ := sem_join aS opS gd prog hok hpost.res
    (fun x hx => (hpost.resBelow x hx).mono (by omega)) (by omega) hb'
  refine ⟨s2, ?_, hres2, hscs2.trans hpost.scs, hmm2.trans hpost.mem, fun z hz => ?_,
    harr2 hpost.arr⟩
  · rw [typeC_append]
    exact ComJasminBridgeProgram.sem_append aS opS gd prog hsem1 hsem2
  · rw [hfr2 z fun k s0 hk _ he => hz (Or.inr (Or.inl ⟨k, s0, hk, he⟩))]
    exact hpost.frame z hz

/-- A branch simulates the arm its bit selects, then its continuation. -/
theorem sim_if (hop : JazzOpAgrees opS) {Γ : Ctxt jasminDialect} {rs ts : List JasminTy}
    (cond : Ctxt.Var Γ (HasBitType.bit (d := jasminDialect)))
    (thn els : NFProg jasminDialect Γ rs) (k : NFProg jasminDialect (rs ++ Γ) ts)
    (hok : rs.all tyOkB = true)
    (iht : Sim SyscallState Mem aS opS gd prog E fuel thn)
    (ihe : Sim SyscallState Mem aS opS gd prog E fuel els)
    (ihk : Sim SyscallState Mem aS opS gd prog E fuel k) :
    Sim SyscallState Mem aS opS gd prog E fuel (NFProg.ifThenElse cond thn els k) := by
  intro loc env d n out hlin hout c' hc V r hden hidx s hs
  simp only [linGo, Bool.and_eq_true] at hlin
  obtain ⟨⟨hlt, hle⟩, hlk⟩ := hlin
  simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hout
  obtain ⟨bt, hbt, be, hbe, rk, hrk, rfl⟩ := hout
  obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv (a := [ifCode env d rs
    (varIndex cond) bt be]) hc
  obtain ⟨i', c0, hi', hc0, rfl⟩ := translateCmdExt_cons_inv ha'
  simp only [translateCmdExt, Option.some.injEq] at hc0
  subst hc0
  obtain ⟨cnd', t', e', hcnd, ht', he', rfl⟩ := translateInstrRExt_cif_inv hi'
  -- the condition
  have hlive : usesIdx (NFProg.ifThenElse cond thn els k) (varIndex cond) = true := by
    simp [usesIdx]
  have hcv := hs.agree cond hlive
  have hcok : OkV (env.getD (varIndex cond) dfltV) := by
    rw [OkV, hcv.1]; exact styOf_ne_U512 (t := .reg 1) rfl
  rw [translatePExprExt_nz (translateVarIExt_mvi hcok), Option.some.injEq] at hcnd
  subst hcnd
  have hcval : semPexpr (Mem := Mem) true gd opS s
      (typeE .abool (mnz (mvi (env.getD (varIndex cond) dfltV)))) =
      .ok (.Vbool (HasBoolBit.toBool (d := jasminDialect) (cond.lookup V))) := by
    rw [sem_nz hop hcv.2]
    exact congrArg (fun b => JResult.ok (Value.Vbool b)) (bit_ne_zero _)
  -- the denotation
  have hden' : ((if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then
      thn.denoteAt E fuel V else els.denoteAt E fuel V) >>= fun rb =>
        k.denoteAt E fuel (hvAppend rb V)) = some r := hden
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hden'
  obtain ⟨rb, hrb, hkden⟩ := hden'
  have hsub : ∀ {q : NFProg jasminDialect Γ rs}, (∀ i, usesIdx q i = true →
      usesIdx (NFProg.ifThenElse cond thn els k) i = true) →
      JazzStoreAgrees env d (fun i => usesIdx q i = true) V s :=
    fun hq => storeAgrees_frame hs (fun i hi => hq i hi) (fun _ _ => rfl) hs.arrTyped
  have hmt := nfToJasminBody_mono thn hbt
  have hme := nfToJasminBody_mono els hbe
  -- the branch
  have hstep : ∃ s2 n0, n ≤ n0 ∧ n0 ≤ be.next ∧
      SemIr aS opS gd prog s (typeI (.Cif (mnz (mvi (env.getD (varIndex cond) dfltV))) t' e')) s2 ∧
      JazzResAgrees (blockVars d rs) rb s2 ∧ s2.escs = s.escs ∧ s2.emem = s.emem ∧
      (∀ z : MVar, ¬ Writes env 0 d n0 z.vname → s2.evm z = s.evm z) ∧ VmArrTyped s2.evm := by
    by_cases hb : HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) = true
    · rw [if_pos hb] at hrb
      have hix := hidx.1
      rw [if_pos hb] at hix
      obtain ⟨s2, hsem, hres, hscs, hmm, hfr, harr⟩ := branch_run aS opS gd prog E fuel hok iht hlt
        hbt ht' hrb hix (hsub fun i hi => by simp [usesIdx, hi])
      exact ⟨s2, n, le_refl _, by omega, .Eif_true _ _ _ _ _ (by rw [hcval, hb]) hsem, hres, hscs,
        hmm, hfr, harr⟩
    · rw [if_neg hb] at hrb
      have hix := hidx.1
      rw [if_neg hb] at hix
      obtain ⟨s2, hsem, hres, hscs, hmm, hfr, harr⟩ := branch_run aS opS gd prog E fuel hok ihe hle
        hbe he' hrb hix (hsub fun i hi => by simp [usesIdx, hi])
      refine ⟨s2, bt.next, hmt.2, hme.2, .Eif_false _ _ _ _ _ ?_ hsem, hres, hscs, hmm, hfr, harr⟩
      rw [hcval]
      simp only [Bool.not_eq_true] at hb
      rw [hb]
  obtain ⟨s2, n0, hn0, hn0', hsem2, hres2, hscs2, hmm2, hfr2, harr2⟩ := hstep
  -- the continuation
  have hs2 : JazzStoreAgrees env d (fun i => usesIdx (NFProg.ifThenElse cond thn els k) i = true)
      V s2 :=
    storeAgrees_frame hs (fun _ h => h) (fun i hi => hfr2 _ (not_writes_of_below (hs.below i hi)
      (le_refl _) (fun _ h => absurd h (Nat.not_lt_zero _)))) harr2
  have hsk := storeAgrees_block hs2 hres2 (L' := fun i => usesIdx k i = true) fun i hi hle => by
    simp only [usesIdx, Bool.or_eq_true]
    exact Or.inr (by rw [Nat.sub_add_cancel hle]; exact hi)
  obtain ⟨s3, hsem3, hpost⟩ := ihk hlk hrk hb' hkden (hidx.2 rb hrb) hsk
  refine ⟨s3, sem_cons aS opS gd prog hsem2 hsem3, ⟨hpost.res, hpost.resBelow,
    hpost.scs.trans hscs2, hpost.mem.trans hmm2, fun z hz => ?_, hpost.arr⟩⟩
  rw [hpost.frame z fun h => hz (writes_of_block h (by omega))]
  exact hfr2 z fun h => hz (writes_of_inner h (le_refl _) hn0
    (fun _ h => absurd h (Nat.not_lt_zero _)))

/-- The typed assignment of a `u64` word to a `u64` variable. -/
theorem semIr_set_u64 {σ : Estate SyscallState Mem} {x : JVar} (hx : x.vtype = u64)
    {e : MPexpr} {w : BitVec 64}
    (he : semPexpr (Mem := Mem) true gd opS σ (typeE (.aword .U64) e) = .ok (.Vword .U64 w)) :
    SemIr aS opS gd prog σ (typeI (masgn (mvi x) e))
      (σ.withVm (σ.evm.set (mvar x) (.Vword .U64 w))) := by
  have hv : (mvi x).v_var.vtype = .aword .U64 := mvar_u64 hx
  show SemIr aS opS gd prog σ (masgn (mvi x) (typeE (mvi x).v_var.vtype e)) _
  rw [hv]
  exact semIr_masgn aS opS gd prog (x := mvi x) he rfl (by rw [hv]; rfl)

/-- The typed increment `x + 1` of a `u64` variable holding `j`. -/
theorem sem_incr (hop : JazzOpAgrees opS) {σ : Estate SyscallState Mem} {x : JVar} {j : Nat}
    (hx : σ.evm (mvar x) = .Vword .U64 (BitVec.ofNat 64 j)) :
    semPexpr (Mem := Mem) true gd opS σ
      (typeE (.aword .U64) (.Papp2 (.Oadd (.Op_w .U64)) (mpv (mvi x)) (.Pconst 1))) =
      .ok (.Vword .U64 (BitVec.ofNat 64 (j + 1))) := by
  have h1 : semPexpr (Mem := Mem) true gd opS σ (.Papp1 (.Oword_of_int .U64) (.Pconst 1)) =
      .ok (.Vword .U64 (BitVec.ofInt 64 1)) := semPexpr_wconst opS gd hop (ws := .U64) rfl σ 1
  show semPexpr (Mem := Mem) true gd opS σ (.Papp2 (.Oadd (.Op_w .U64)) (mpv (mvi x))
    (.Papp1 (.Oword_of_int .U64) (.Pconst 1))) = _
  rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd (x := mvi x) hx rfl) h1]
  refine (hop.add .U64 rfl (BitVec.ofNat 64 j) (BitVec.ofInt 64 1)).trans ?_
  congr 2
  rw [BitVec.ofNat_add]; rfl

/-- The typed decrement `x - 1` of a `u64` variable holding `a + 1`. -/
theorem sem_decr (hop : JazzOpAgrees opS) {σ : Estate SyscallState Mem} {x : JVar} {a : Nat}
    (hx : σ.evm (mvar x) = .Vword .U64 (BitVec.ofNat 64 (a + 1))) :
    semPexpr (Mem := Mem) true gd opS σ
      (typeE (.aword .U64) (.Papp2 (.Osub (.Op_w .U64)) (mpv (mvi x)) (.Pconst 1))) =
      .ok (.Vword .U64 (BitVec.ofNat 64 a)) := by
  have h1 : semPexpr (Mem := Mem) true gd opS σ (.Papp1 (.Oword_of_int .U64) (.Pconst 1)) =
      .ok (.Vword .U64 (BitVec.ofInt 64 1)) := semPexpr_wconst opS gd hop (ws := .U64) rfl σ 1
  show semPexpr (Mem := Mem) true gd opS σ (.Papp2 (.Osub (.Op_w .U64)) (mpv (mvi x))
    (.Papp1 (.Oword_of_int .U64) (.Pconst 1))) = _
  rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd (x := mvi x) hx rfl) h1]
  refine (hop.sub .U64 rfl (BitVec.ofNat 64 (a + 1)) (BitVec.ofInt 64 1)).trans ?_
  congr 2
  rw [BitVec.ofNat_add]
  show BitVec.ofNat 64 a + 1#64 - 1#64 = _
  simp

/-- The trip index of a counted loop at depth `d` is named apart from every written name
of its body other than its own, and is not an array. -/
theorem idx_not_writes_body {env : List JVar} {cs : List JasminTy} {d n : Nat} :
    ¬ Writes (blockVars (d + 1) cs ++ mkV 'r' d u64 :: env) (cs.length + 1)
      (d + 1 + cs.length) (n + 1) (mkV 'r' d u64).vname := by
  rintro (h | ⟨k, s0, hk, h⟩ | ⟨m, s0, -, h⟩ | ⟨i, hi, h, harr⟩)
  · exact not_scratch_new d u64 h
  · have := (nameOf_inj h).2.1; omega
  · exact nameOf_ne (by decide) _ _ _ _ h
  · by_cases hic : i < cs.length
    · rw [getD_append_lt (by simpa using hic)] at h
      obtain ⟨k, s0, hk, -, he⟩ := mem_blockVars (List.getElem_mem (l := blockVars (d + 1) cs)
        (n := i) (by simpa using hic))
      rw [he] at h
      have := (nameOf_inj h).2.1; omega
    · rw [getD_append_ge (by simp; omega), length_blockVars,
        show i - cs.length = 0 by omega] at harr
      obtain ⟨m, hm⟩ := harr
      exact absurd hm (by simp [mkV])

/-- The entries of the environment of a loop body that its in-place stores may reach are
bindings at depths from `d`. -/
theorem body_loc {env : List JVar} {cs : List JasminTy} {d : Nat} :
    ∀ i < cs.length + 1, ∃ k s, d ≤ k ∧
      ((blockVars (d + 1) cs ++ mkV 'r' d u64 :: env).getD i dfltV).vname = nameOf 'r' k s := by
  intro i hi
  by_cases hic : i < cs.length
  · rw [getD_append_lt (by simpa using hic)]
    obtain ⟨k, s0, hk, -, he⟩ := mem_blockVars (List.getElem_mem (l := blockVars (d + 1) cs)
      (n := i) (by simpa using hic))
    exact ⟨k, s0, by omega, by rw [he]; rfl⟩
  · rw [getD_append_ge (by simp; omega), length_blockVars, show i - cs.length = 0 by omega]
    exact ⟨d, u64, le_refl _, rfl⟩

/-- A counted loop simulates the fold of its body over the trip indices, then its
continuation. -/
theorem sim_for (hop : JazzOpAgrees opS) {Γ : Ctxt jasminDialect} {cs ts : List JasminTy}
    (count : Ctxt.Var Γ (HasWord64.word (d := jasminDialect)))
    (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts) (hok : cs.all tyOkB = true)
    (ihb : Sim SyscallState Mem aS opS gd prog E fuel body)
    (ihk : Sim SyscallState Mem aS opS gd prog E fuel k) :
    Sim SyscallState Mem aS opS gd prog E fuel (NFProg.forLoop count inits body k) := by
  intro loc env d n out hlin hout c' hc V r hden hidx s hs
  simp only [linGo, Bool.and_eq_true] at hlin
  obtain ⟨hlb, hlk⟩ := hlin
  simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hout
  obtain ⟨b, hb, rk, hrk, rfl⟩ := hout
  obtain ⟨fc', k', hfc, hk', rfl⟩ := translateCmdExt_append_inv
    (a := forCode env d n cs (resolveHV env inits) (varIndex count) b) hc
  unfold forCode at hfc
  dsimp only at hfc
  obtain ⟨x1, sh', hx1, hsh, rfl⟩ := translateCmdExt_append_inv hfc
  obtain ⟨sd', m', hsd, hm, rfl⟩ := translateCmdExt_append_inv hx1
  obtain ⟨i1, m1, hi1, hm1, rfl⟩ := translateCmdExt_cons_inv hm
  obtain ⟨i2, m2, hi2, hm2, rfl⟩ := translateCmdExt_cons_inv hm1
  obtain ⟨i3, m3, hi3, hm3, rfl⟩ := translateCmdExt_cons_inv hm2
  simp only [translateCmdExt, Option.some.injEq] at hm3
  subst hm3
  obtain ⟨b0, cnd', lb', hb0, hcnd, hlb', rfl⟩ := translateInstrRExt_cwhile_inv hi3
  simp only [translateCmdExt, Option.some.injEq] at hb0
  subst hb0
  -- the variables of the frame
  have hidxok : OkV (mkV 'r' d u64) := by simp [OkV, mkV]
  have hctrok : OkV (mkV 'c' n u64) := by simp [OkV, mkV]
  have hlive : usesIdx (NFProg.forLoop count inits body k) (varIndex count) = true := by
    simp [usesIdx]
  have hcntA := hs.agree count hlive
  have hcntok : OkV (env.getD (varIndex count) dfltV) := by
    rw [OkV, hcntA.1]; exact styOf_ne_U512 (t := .reg 64) rfl
  rw [translateInstrRExt_asgn (translateVarIExt_mvi hidxok) (translatePExprExt_cnst 0),
    Option.some.injEq] at hi1
  subst hi1
  rw [translateInstrRExt_asgn (translateVarIExt_mvi hctrok)
    (translatePExprExt_pv (translateVarIExt_mvi hcntok)), Option.some.injEq] at hi2
  subst hi2
  rw [translatePExprExt_nz (translateVarIExt_mvi hctrok), Option.some.injEq] at hcnd
  subst hcnd
  -- the code of one trip
  obtain ⟨y1, adv', hy1, hadv, rfl⟩ := translateCmdExt_append_inv hlb'
  obtain ⟨bc', pm', hbc, hpm, rfl⟩ := translateCmdExt_append_inv hy1
  obtain ⟨a1, ad1, ha1, had1, rfl⟩ := translateCmdExt_cons_inv hadv
  obtain ⟨a2, ad2, ha2, had2, rfl⟩ := translateCmdExt_cons_inv had1
  simp only [translateCmdExt, Option.some.injEq] at had2
  subst had2
  rw [translateInstrRExt_asgn (translateVarIExt_mvi hidxok) (translatePExprExt_papp2 rfl
    (translatePExprExt_pv (translateVarIExt_mvi hidxok)) (translatePExprExt_cnst 1)),
    Option.some.injEq] at ha1
  subst ha1
  rw [translateInstrRExt_asgn (translateVarIExt_mvi hctrok) (translatePExprExt_papp2 rfl
    (translatePExprExt_pv (translateVarIExt_mvi hctrok)) (translatePExprExt_cnst 1)),
    Option.some.injEq] at ha2
  subst ha2
  clear hc hfc hx1 hm hm1 hm2 hi3 hlb' hy1 hadv had1
  -- the denotation
  set idx := mkV 'r' d u64 with hidxdef
  set ctr := mkV 'c' n u64 with hctrdef
  set cnt := env.getD (varIndex count) dfltV with hcntdef
  set car := blockVars (d + 1) cs with hcardef
  set N := (count.lookup V : BitVec 64).toNat with hNdef
  have hN : N < 2 ^ 64 := BitVec.isLt _
  set F : Ctxt.Valuation (d := jasminDialect) cs → Nat →
      Option (Ctxt.Valuation (d := jasminDialect) cs) := fun acc i =>
    body.denoteAt E fuel (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V))
    with hFdef
  have hden' : ((List.range N).foldlM F (Expr.lookupArgs inits V) >>= fun acc =>
      k.denoteAt E fuel (hvAppend acc V)) = some r := hden
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hden'
  obtain ⟨accN, hfoldN, hkden⟩ := hden'
  -- names
  have hidxW : ∀ nm, ¬ Writes env 0 d n nm → nm ≠ idx.vname :=
    fun nm hn he => hn (Or.inr (Or.inl ⟨d, u64, le_refl _, he⟩))
  have hctrW : ∀ nm, ¬ Writes env 0 d n nm → nm ≠ ctr.vname :=
    fun nm hn he => hn (Or.inr (Or.inr (Or.inl ⟨n, u64, le_refl _, he⟩)))
  have hcarW : ∀ nm, ¬ Writes env 0 d n nm → ∀ x ∈ car, nm ≠ x.vname := by
    intro nm hn x hx he
    obtain ⟨k0, s0, hk0, -, rfl⟩ := mem_blockVars hx
    exact hn (Or.inr (Or.inl ⟨k0, s0, by omega, he⟩))
  have hcar_idx : ∀ x ∈ car, x.vname ≠ idx.vname := by
    intro x hx he
    obtain ⟨k0, s0, hk0, -, rfl⟩ := mem_blockVars hx
    have := (nameOf_inj he).2.1; omega
  have hcar_ctr : ∀ x ∈ car, x.vname ≠ ctr.vname := by
    intro x hx he
    obtain ⟨k0, s0, -, -, rfl⟩ := mem_blockVars hx
    exact nameOf_ne (by decide) _ _ _ _ he
  have hidx_ctr : idx.vname ≠ ctr.vname := nameOf_ne (by decide) _ _ _ _
  have hbelow : ∀ i, usesIdx (NFProg.forLoop count inits body k) i = true →
      ¬ Writes env 0 d n (env.getD i dfltV).vname := fun i hi =>
    not_writes_of_below (hs.below i hi) (le_refl _) (fun _ h => absurd h (Nat.not_lt_zero _))
  have hcntB : EnvBelow d cnt := hs.below _ hlive
  -- the seeds
  have hinitsA : JazzResAgrees (resolveHV env inits) (Expr.lookupArgs inits V) s :=
    resAgrees_ret hs inits fun i hi => by simp [usesIdx, hi]
  have hinitsB : ∀ x ∈ resolveHV env inits, EnvBelow (d + 1) x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact (hs.below i (by simp [usesIdx, hi])).mono (by omega)
  obtain ⟨σ0, hsem0, hscs0, hmm0, hres0, hfr0, harr0⟩ := sem_movesOf aS opS gd prog
    (pairwise_zip_block (resAgrees_length hinitsA) hinitsB) (c' := sd') hsd
    (resAgrees_movesTyped (d + 1) hok hinitsA)
  have hcar0 : JazzResAgrees car (Expr.lookupArgs inits V) σ0 :=
    resAgrees_blockVars (d + 1) hinitsA hres0
  have hcnt0 : σ0.evm (mvar cnt) = .Vword .U64 (count.lookup V) := by
    rw [hfr0 _ fun p hp he => ?_]
    · rw [hcntA.2]; exact vword_ofNat .U64 _
    · obtain ⟨k0, s0, hk0, -, hp1⟩ := mem_blockVars (List.of_mem_zip hp).1
      rw [hp1] at he
      exact envBelow_ne_ge hcntB (by omega) s0 he
  -- the trip index and the counter
  have hsem1 := semIr_set_u64 aS opS gd prog (σ := σ0) (x := idx) rfl (e := .Pconst 0)
    (semPexpr_wconst opS gd hop (ws := .U64) rfl σ0 0)
  set σ1 := σ0.withVm (σ0.evm.set (mvar idx) (.Vword .U64 (BitVec.ofInt 64 0))) with hσ1
  have hcnt1 : σ1.evm (mvar cnt) = .Vword .U64 (count.lookup V) := by
    rw [hσ1]; simp only [Estate.withVm]
    rw [set_ne _ (envBelow_ne_ge hcntB (le_refl _) u64)]; exact hcnt0
  have hsem2 := semIr_set_u64 aS opS gd prog (σ := σ1) (x := ctr) rfl
    (e := mpv (mvi cnt)) (semPexpr_mpv opS gd (x := mvi cnt) hcnt1 rfl)
  set σ2 := σ1.withVm (σ1.evm.set (mvar ctr) (.Vword .U64 (count.lookup V))) with hσ2
  -- the loop invariant
  set Inv : Nat → Estate SyscallState Mem → Prop := fun j σ =>
    (∃ acc, (List.range j).foldlM F (Expr.lookupArgs inits V) = some acc ∧
      JazzResAgrees car acc σ) ∧
    σ.evm (mvar idx) = .Vword .U64 (BitVec.ofNat 64 j) ∧
    σ.evm (mvar ctr) = .Vword .U64 (BitVec.ofNat 64 (N - j)) ∧
    σ.escs = s.escs ∧ σ.emem = s.emem ∧
    (∀ z : MVar, ¬ Writes env 0 d n z.vname → σ.evm z = s.evm z) ∧ VmArrTyped σ.evm
    with hInvdef
  have hInv0 : Inv 0 σ2 := by
    refine ⟨⟨_, rfl, resAgrees_frame hcar0 fun x hx => ?_⟩, ?_, ?_, ?_, ?_, fun z hz => ?_, ?_⟩
    · simp only [hσ2, hσ1, Estate.withVm]
      rw [set_ne _ (hcar_ctr x hx), set_ne _ (hcar_idx x hx)]
    · simp only [hσ2, hσ1, Estate.withVm]
      rw [set_ne _ hidx_ctr, set_same]; rfl
    · simp only [hσ2, Estate.withVm, set_same, Nat.sub_zero, hNdef]
      congr 1
      exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
    · exact hscs0
    · exact hmm0
    · simp only [hσ2, hσ1, Estate.withVm]
      rw [set_ne _ (hctrW _ hz), set_ne _ (hidxW _ hz)]
      exact hfr0 z fun p hp => hcarW _ hz _ (List.of_mem_zip hp).1
    · simp only [hσ2, hσ1, Estate.withVm]
      exact arrTyped_set (arrTyped_set (harr0 hs.arrTyped) rfl (by rw [mvar_u64 rfl]; rfl)) rfl
        (by rw [mvar_u64 rfl]; rfl)
  -- one trip
  have hbmono := nfToJasminBody_mono body hb
  have hctr_b : ¬ Writes (car ++ idx :: env) (cs.length + 1) (d + 1 + cs.length) (n + 1)
      ctr.vname := fun h => by
    rcases writes_of_inner (env := env) (loc := 0) (d := d) (n := n + 1) h (by omega) le_rfl
      body_loc with h | ⟨k0, s0, -, h⟩ | ⟨m, s0, hm, h⟩ | ⟨i, hi, -⟩
    · exact not_scratch_mkV (c := 'c') (by decide) (by decide) n u64 h
    · exact nameOf_ne (by decide) _ _ _ _ h
    · have := (nameOf_inj h).2.1; omega
    · omega
  have hstepL : ∀ j σ, j < N → Inv j σ → ∃ σ', Sem aS opS gd prog σ (typeC (bc' ++ pm' ++
      [.MkI () (masgn (mvi idx) (.Papp2 (.Oadd (.Op_w .U64)) (mpv (mvi idx)) (.Pconst 1))),
       .MkI () (masgn (mvi ctr) (.Papp2 (.Osub (.Op_w .U64)) (mpv (mvi ctr)) (.Pconst 1)))]))
        σ' ∧ Inv (j + 1) σ' := by
    intro j σ hj hinv
    obtain ⟨⟨acc, hfj, hcarj⟩, hidxv, hctrv, hscs, hmm, hfr, harr⟩ := hinv
    obtain ⟨acc', hF, hfj1⟩ := foldlM_range_step F hfoldN hj hfj
    have hsσ : JazzStoreAgrees env d
        (fun i => usesIdx (NFProg.forLoop count inits body k) i = true) V σ :=
      storeAgrees_frame hs (fun _ h => h) (fun i hi => hfr _ (hbelow i hi)) harr
    have hidxA : JazzResAgrees (blockVars d [JasminTy.reg 64])
        (HVector.cons (BitVec.ofNat 64 j) .nil : HVector (fun t => ⟦t⟧) [JasminTy.reg 64]) σ := by
      rw [blockVars_cons, blockVars_nil]
      refine ⟨⟨rfl, ?_⟩, trivial⟩
      show σ.evm (mvar idx) = _
      rw [hidxv]
      exact (vword_ofNat .U64 _).symm
    have hs1 := storeAgrees_block hsσ hidxA
      (L' := fun i => usesIdx body (i + cs.length) = true) fun i hi h1 => by
        simp only [List.length_singleton] at h1 ⊢
        have : i - 1 + cs.length + 1 = i + cs.length := by omega
        simp [usesIdx, this, hi]
    have hs2 := storeAgrees_block hs1 hcarj (L' := fun i => usesIdx body i = true)
      fun i hi h1 => by
        show usesIdx body (i - cs.length + cs.length) = true
        rw [Nat.sub_add_cancel h1]; exact hi
    have hs2' : JazzStoreAgrees (car ++ idx :: env) (d + 1 + cs.length)
        (fun i => usesIdx body i = true)
        (hvAppend (f := fun t => ⟦t⟧) acc (.cons (HasWord64.ofNat (d := jasminDialect) j) V)) σ :=
      hs2
    obtain ⟨σ1, hsemb, post1⟩ := ihb hlb hb hbc hF (hidx.1 j acc hj hfj) hs2'
    obtain ⟨σ2, hsemj, hcar2, hscs2, hmm2, hfr2, harr2⟩ := sem_join aS opS gd prog
      (base := d + 1) hok post1.res post1.resBelow (by omega) hpm
    have hidx2 : σ2.evm (mvar idx) = .Vword .U64 (BitVec.ofNat 64 j) := by
      rw [hfr2 _ fun k0 s0 hk _ he => by have := (nameOf_inj he).2.1; omega,
        post1.frame _ idx_not_writes_body, hidxv]
    have hctr2 : σ2.evm (mvar ctr) = .Vword .U64 (BitVec.ofNat 64 (N - (j + 1) + 1)) := by
      rw [hfr2 _ fun k0 s0 _ _ he => nameOf_ne (by decide) _ _ _ _ he, post1.frame _ hctr_b, hctrv,
        show N - (j + 1) + 1 = N - j by omega]
    have hsemI := semIr_set_u64 aS opS gd prog (σ := σ2) (x := idx) rfl
      (sem_incr opS gd hop hidx2)
    set σ3 := σ2.withVm (σ2.evm.set (mvar idx) (.Vword .U64 (BitVec.ofNat 64 (j + 1)))) with hσ3
    have hctr3 : σ3.evm (mvar ctr) = .Vword .U64 (BitVec.ofNat 64 (N - (j + 1) + 1)) := by
      rw [hσ3]; simp only [Estate.withVm]; rw [set_ne _ hidx_ctr.symm, hctr2]
    have hsemD := semIr_set_u64 aS opS gd prog (σ := σ3) (x := ctr) rfl
      (sem_decr opS gd hop hctr3)
    set σ4 := σ3.withVm (σ3.evm.set (mvar ctr) (.Vword .U64 (BitVec.ofNat 64 (N - (j + 1)))))
      with hσ4
    have h43 : ∀ z : MVar, z.vname ≠ idx.vname → z.vname ≠ ctr.vname → σ4.evm z = σ2.evm z := by
      intro z h1 h2
      rw [hσ4, hσ3]; simp only [Estate.withVm]
      rw [set_ne _ h2, set_ne _ h1]
    refine ⟨σ4, ?_, ⟨acc', hfj1, resAgrees_frame hcar2 fun x hx =>
      h43 _ (hcar_idx x hx) (hcar_ctr x hx)⟩, ?_, ?_, ?_, ?_, fun z hz => ?_, ?_⟩
    · rw [typeC_append, typeC_append]
      exact ComJasminBridgeProgram.sem_append aS opS gd prog
        (ComJasminBridgeProgram.sem_append aS opS gd prog hsemb hsemj)
        (sem_cons aS opS gd prog hsemI (sem_cons aS opS gd prog hsemD (.Eskip _)))
    · rw [hσ4]; simp only [Estate.withVm]
      rw [set_ne _ hidx_ctr, hσ3]; simp only [Estate.withVm, set_same]
    · rw [hσ4]; simp only [Estate.withVm, set_same]
    · exact hscs2.trans (post1.scs.trans hscs)
    · exact hmm2.trans (post1.mem.trans hmm)
    · rw [h43 z (hidxW _ hz) (hctrW _ hz),
        hfr2 z fun k0 s0 hk _ he => hz (Or.inr (Or.inl ⟨k0, s0, by omega, he⟩)),
        post1.frame z fun h => hz (writes_of_inner h (by omega) (by omega) body_loc)]
      exact hfr z hz
    · rw [hσ4, hσ3]; simp only [Estate.withVm]
      exact arrTyped_set (arrTyped_set (harr2 post1.arr) rfl (by rw [mvar_u64 rfl]; rfl)) rfl
        (by rw [mvar_u64 rfl]; rfl)
  -- the loop
  obtain ⟨σL, hsemL, hInvL⟩ := semIr_while_count aS opS gd prog
    (al := .NoAlign) (ii := ()) (e := typeE .abool (mnz (mvi ctr))) N Inv
    (fun j σ hj h => by rw [sem_nz hop h.2.2.1, count_ne_zero hN hj]) hstepL N 0 σ2 (by omega)
    hInv0
  obtain ⟨⟨accL, hfL, hcarL⟩, -, -, hscsL, hmmL, hfrL, harrL⟩ := hInvL
  rw [hfoldN, Option.some.injEq] at hfL
  subst hfL
  -- the block moves down and the continuation
  obtain ⟨σS, hsemS, hshift, hscsS, hmmS, hfrS, harrS⟩ := sem_shift aS opS gd prog hok hcarL hsh
  have hsO : JazzStoreAgrees env d
      (fun i => usesIdx (NFProg.forLoop count inits body k) i = true) V σS :=
    storeAgrees_frame hs (fun _ h => h) (fun i hi =>
      (hfrS _ fun k0 s0 hk he => envBelow_ne_ge (hs.below i hi) hk s0 he).trans
        (hfrL _ (hbelow i hi))) (harrS harrL)
  have hsk := storeAgrees_block hsO hshift (L' := fun i => usesIdx k i = true)
    fun i hi h1 => by simp [usesIdx, Nat.sub_add_cancel h1, hi]
  obtain ⟨s3, hsem3, hpost⟩ := ihk hlk hrk hk' hkden (hidx.2 accN hfoldN) hsk
  refine ⟨s3, ?_, ⟨hpost.res, hpost.resBelow, hpost.scs.trans (hscsS.trans hscsL),
    hpost.mem.trans (hmmS.trans hmmL), fun z hz => ?_, hpost.arr⟩⟩
  · rw [typeC_append, typeC_append, typeC_append]
    refine ComJasminBridgeProgram.sem_append aS opS gd prog
      (ComJasminBridgeProgram.sem_append aS opS gd prog
        (ComJasminBridgeProgram.sem_append aS opS gd prog hsem0 ?_) hsemS) hsem3
    exact sem_cons aS opS gd prog hsem1 (sem_cons aS opS gd prog hsem2
      (sem_cons aS opS gd prog hsemL (.Eskip _)))
  · rw [hpost.frame z fun h => hz (writes_of_block h (by omega)),
      hfrS z fun k0 s0 hk he => hz (Or.inr (Or.inl ⟨k0, s0, hk, he⟩))]
    exact hfrL z fun h => hz (writes_of_inner h le_rfl le_rfl
      fun _ h => absurd h (Nat.not_lt_zero _))

/-- The entries of a block in front of an environment are bindings at depths from the
block's base. -/
theorem block_loc {env : List JVar} {cs : List JasminTy} {d : Nat} :
    ∀ i < cs.length, ∃ k s, d ≤ k ∧
      ((blockVars d cs ++ env).getD i dfltV).vname = nameOf 'r' k s := by
  intro i hi
  rw [getD_append_lt (by simpa using hi)]
  obtain ⟨k, s0, hk, -, he⟩ := mem_blockVars (List.getElem_mem (l := blockVars d cs)
    (n := i) (by simpa using hi))
  exact ⟨k, s0, hk, by rw [he]; rfl⟩

/-- An exit-flag loop simulates the iteration of its body, then its continuation. -/
theorem sim_while (hop : JazzOpAgrees opS) {Γ : Ctxt jasminDialect} {cs ts : List JasminTy}
    (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs))
    (k : NFProg jasminDialect (cs ++ Γ) ts) (hok : cs.all tyOkB = true)
    (ihb : Sim SyscallState Mem aS opS gd prog E fuel body)
    (ihk : Sim SyscallState Mem aS opS gd prog E fuel k) :
    Sim SyscallState Mem aS opS gd prog E fuel (NFProg.whileLoop inits body k) := by
  intro loc env d n out hlin hout c' hc V r hden hidx s hs
  simp only [linGo, Bool.and_eq_true] at hlin
  obtain ⟨hlb, hlk⟩ := hlin
  simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hout
  obtain ⟨b, hb, rk, hrk, rfl⟩ := hout
  obtain ⟨fc', k', hfc, hk', rfl⟩ := translateCmdExt_append_inv
    (a := whileCode d cs (resolveHV env inits) b) hc
  unfold whileCode at hfc
  dsimp only at hfc
  obtain ⟨sd', m', hsd, hm, rfl⟩ := translateCmdExt_append_inv hfc
  obtain ⟨i1, m1, hi1, hm1, rfl⟩ := translateCmdExt_cons_inv hm
  simp only [translateCmdExt, Option.some.injEq] at hm1
  subst hm1
  obtain ⟨lb', cnd', a0, hlb', hcnd, ha0, rfl⟩ := translateInstrRExt_cwhile_inv hi1
  simp only [translateCmdExt, Option.some.injEq] at ha0
  subst ha0
  have hflagok : OkV (mkV 'r' (b.depth + cs.length) u64) := by simp [OkV, mkV]
  rw [translatePExprExt_nz (translateVarIExt_mvi hflagok), Option.some.injEq] at hcnd
  subst hcnd
  obtain ⟨bc', rest', hbc, hrest, rfl⟩ := translateCmdExt_append_inv hlb'
  obtain ⟨i2, pm', hi2, hpm, rfl⟩ := translateCmdExt_cons_inv hrest
  clear hc hfc hm hi1 hlb' hrest
  set flag := mkV 'r' (b.depth + cs.length) u64 with hflagdef
  set car := blockVars d cs with hcardef
  set step : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs)) :=
    fun acc => body.denoteAt E fuel (hvAppend acc V) with hstepdef
  have hden' : (NFProg.whileIter step fuel (Expr.lookupArgs inits V) >>= fun acc =>
      k.denoteAt E fuel (hvAppend acc V)) = some r := hden
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hden'
  obtain ⟨accF, hiter, hkden⟩ := hden'
  have hbelow : ∀ i, usesIdx (NFProg.whileLoop inits body k) i = true →
      ¬ Writes env 0 d n (env.getD i dfltV).vname := fun i hi =>
    not_writes_of_below (hs.below i hi) (le_refl _) (fun _ h => absurd h (Nat.not_lt_zero _))
  have hbmono := nfToJasminBody_mono body hb
  -- the seeds
  have hinitsA : JazzResAgrees (resolveHV env inits) (Expr.lookupArgs inits V) s :=
    resAgrees_ret hs inits fun i hi => by simp [usesIdx, hi]
  have hinitsB : ∀ x ∈ resolveHV env inits, EnvBelow d x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hs.below i (by simp [usesIdx, hi])
  obtain ⟨σ0, hsem0, hscs0, hmm0, hres0, hfr0, harr0⟩ := sem_movesOf aS opS gd prog
    (pairwise_zip_block (resAgrees_length hinitsA) hinitsB) (c' := sd') hsd
    (resAgrees_movesTyped d hok hinitsA)
  -- the loop invariant
  set Inv : Ctxt.Valuation (d := jasminDialect) cs → Estate SyscallState Mem → Prop :=
    fun acc σ => JazzResAgrees car acc σ ∧ σ.escs = s.escs ∧ σ.emem = s.emem ∧
      (∀ z : MVar, ¬ Writes env 0 d n z.vname → σ.evm z = s.evm z) ∧ VmArrTyped σ.evm
    with hInvdef
  have hInv0 : Inv (Expr.lookupArgs inits V) σ0 :=
    ⟨resAgrees_blockVars d hinitsA hres0, hscs0, hmm0, fun z hz => hfr0 z fun p hp he => by
      obtain ⟨k0, s0, hk0, -, hp1⟩ := mem_blockVars (List.of_mem_zip hp).1
      rw [hp1] at he
      exact hz (Or.inr (Or.inl ⟨k0, s0, hk0, he⟩)), harr0 hs.arrTyped⟩
  have hstepL : ∀ acc σ, Inv acc σ → IdxInBounds E fuel body (hvAppend acc V) →
      ∀ r', step acc = some r' → ∃ σ', Sem aS opS gd prog σ (typeC (bc' ++ .MkI () i2 :: pm'))
        σ' ∧ semPexpr (Mem := Mem) true gd opS σ' (typeE .abool (mnz (mvi flag))) =
          .ok (.Vbool (HasBoolBit.toBool (d := jasminDialect) r'.head)) ∧ Inv r'.tail σ' := by
    intro acc σ hinv hP r' hr
    obtain ⟨hcar, hscs, hmm, hfr, harr⟩ := hinv
    have hsσ : JazzStoreAgrees env d
        (fun i => usesIdx (NFProg.whileLoop inits body k) i = true) V σ :=
      storeAgrees_frame hs (fun _ h => h) (fun i hi => hfr _ (hbelow i hi)) harr
    have hsb := storeAgrees_block hsσ hcar (L' := fun i => usesIdx body i = true)
      fun i hi h1 => by simp [usesIdx, Nat.sub_add_cancel h1, hi]
    obtain ⟨σ1, hsemb, post1⟩ := ihb hlb hb hbc hr hP hsb
    have hlen := resAgrees_length post1.res
    obtain ⟨x0, xs, hbres⟩ : ∃ x0 xs, b.res = x0 :: xs := by
      cases h : b.res with
      | nil => rw [h] at hlen; simp at hlen
      | cons x0 xs => exact ⟨x0, xs, rfl⟩
    have hres1 := post1.res
    rw [hbres] at hres1 hi2 hpm
    have hxsB : ∀ x ∈ xs, EnvBelow b.depth x := fun x hx =>
      post1.resBelow x (by rw [hbres]; exact List.mem_cons_of_mem _ hx)
    cases r' with
    | cons h0 t0 =>
    obtain ⟨hx0, hxs⟩ := hres1
    have hx0ok : OkV x0 := by rw [OkV, hx0.1]; exact styOf_ne_U512 (t := .reg 1) rfl
    rw [List.headD_cons, translateInstrRExt_asgn (translateVarIExt_mvi hflagok)
      (translatePExprExt_pv (translateVarIExt_mvi hx0ok)), Option.some.injEq] at hi2
    subst hi2
    have hsemF := semIr_set_u64 aS opS gd prog (σ := σ1) (x := flag) rfl (e := mpv (mvi x0))
      (semPexpr_mpv opS gd (x := mvi x0) hx0.2 rfl)
    set σ2 := σ1.withVm (σ1.evm.set (mvar flag)
      (.Vword .U64 (BitVec.ofNat 64 (BitVec.toNat (w := 1) h0)))) with hσ2
    have hxs2 : JazzResAgrees xs t0 σ2 := resAgrees_frame hxs fun x hx => by
      rw [hσ2]; simp only [Estate.withVm]
      exact set_ne _ (envBelow_ne_ge (hxsB x hx) (by omega) u64)
    obtain ⟨σ3, hsemj, hcar3, hscs3, hmm3, hfr3, harr3⟩ := sem_join aS opS gd prog
      (base := d) hok hxs2 hxsB (by omega) (by simpa using hpm)
    have hflag3 : σ3.evm (mvar flag) =
        .Vword .U64 (BitVec.ofNat 64 (BitVec.toNat (w := 1) h0)) := by
      rw [hfr3 _ fun k0 s0 _ hk he => by have := (nameOf_inj he).2.1; omega, hσ2]
      simp only [Estate.withVm, set_same]
    refine ⟨σ3, ?_, ?_, hcar3, hscs3.trans (post1.scs.trans hscs),
      hmm3.trans (post1.mem.trans hmm), fun z hz => ?_, harr3 ?_⟩
    · rw [typeC_append]
      exact ComJasminBridgeProgram.sem_append aS opS gd prog hsemb
        (sem_cons aS opS gd prog hsemF hsemj)
    · rw [sem_nz hop hflag3]
      exact congrArg (fun b => JResult.ok (Value.Vbool b)) (bit_ne_zero _)
    · rw [hfr3 z fun k0 s0 hk _ he => hz (Or.inr (Or.inl ⟨k0, s0, hk, he⟩)), hσ2]
      simp only [Estate.withVm]
      rw [set_ne _ fun he => hz (Or.inr (Or.inl ⟨_, _, by omega, he⟩)),
        post1.frame z fun h => hz (writes_of_inner h (by omega) le_rfl block_loc)]
      exact hfr z hz
    · rw [hσ2]; simp only [Estate.withVm]
      exact arrTyped_set post1.arr rfl (by rw [mvar_u64 rfl]; rfl)
  -- the loop
  obtain ⟨σL, hsemL, hcarL, hscsL, hmmL, hfrL, harrL⟩ := semIr_while_flag aS opS gd prog step
    (fun acc => IdxInBounds E fuel body (hvAppend acc V)) Inv (al := .NoAlign) (ii := ())
    hstepL fuel _ σ0 accF hiter hInv0 hidx.1
  -- the continuation
  have hsO : JazzStoreAgrees env d
      (fun i => usesIdx (NFProg.whileLoop inits body k) i = true) V σL :=
    storeAgrees_frame hs (fun _ h => h) (fun i hi => hfrL _ (hbelow i hi)) harrL
  have hsk := storeAgrees_block hsO hcarL (L' := fun i => usesIdx k i = true)
    fun i hi h1 => by simp [usesIdx, Nat.sub_add_cancel h1, hi]
  obtain ⟨s3, hsem3, hpost⟩ := ihk hlk hrk hk' hkden (hidx.2 accF hiter) hsk
  refine ⟨s3, ?_, ⟨hpost.res, hpost.resBelow, hpost.scs.trans hscsL,
    hpost.mem.trans hmmL, fun z hz => ?_, hpost.arr⟩⟩
  · rw [typeC_append, typeC_append]
    exact ComJasminBridgeProgram.sem_append aS opS gd prog
      (ComJasminBridgeProgram.sem_append aS opS gd prog hsem0
        (sem_cons aS opS gd prog hsemL (.Eskip _))) hsem3
  · rw [hpost.frame z fun h => hz (writes_of_block h (by omega))]
    exact hfrL z fun h => hz (writes_of_inner h le_rfl le_rfl
      fun _ h => absurd h (Nat.not_lt_zero _))

/-! ## 9. Regions with frames -/

/-- **Region simulation with frames.** Every call-free region that `widthsGo` accepts
simulates its denotation (`Sim`): its bindings, counted loops, branches and exit-flag loops,
lowered by `nfToJasminBody` and translated and typed. -/
theorem nfToJasminRegion_sim (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts),
      p.callFree = true → widthsGo p = true →
      Sim SyscallState Mem aS opS gd prog E fuel p := by
  intro Γ ts p
  induction p with
  | ret vs => intro _ _; exact sim_ret aS opS gd prog E fuel vs
  | @var Γ t ts e k ih =>
      intro hcf hw
      simp only [widthsGo, Bool.and_eq_true] at hw
      obtain ⟨⟨ht, hok⟩, hwk⟩ := hw
      exact sim_var aS opS gd prog E fuel haS hop e k ht hok (ih hcf hwk)
  | forLoop count inits body k ihb ihk =>
      intro hcf hw
      simp only [NFProg.callFree, Bool.and_eq_true] at hcf
      simp only [widthsGo, Bool.and_eq_true] at hw
      exact sim_for aS opS gd prog E fuel hop count inits body k hw.1.1
        (ihb hcf.1 hw.1.2) (ihk hcf.2 hw.2)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro hcf hw
      simp only [NFProg.callFree, Bool.and_eq_true] at hcf
      simp only [widthsGo, Bool.and_eq_true] at hw
      exact sim_if aS opS gd prog E fuel hop cond thn els k hw.1.1.1
        (iht hcf.1.1 hw.1.1.2) (ihe hcf.1.2 hw.1.2) (ihk hcf.2 hw.2)
  | whileLoop inits body k ihb ihk =>
      intro hcf hw
      simp only [NFProg.callFree, Bool.and_eq_true] at hcf
      simp only [widthsGo, Bool.and_eq_true] at hw
      exact sim_while aS opS gd prog E fuel hop inits body k hw.1.1
        (ihb hcf.1 hw.1.2) (ihk hcf.2 hw.2)
  | call f args k _ => intro hcf; simp [NFProg.callFree] at hcf

/-- **Regions with frames.** A call-free region that `widthsGo` and the in-place
store check `linGo` accept, lowered by `nfToJasminBody` and translated and typed, runs from
a state that agrees with `V` on the variables the region reads, with its array indices in
range, to a state in which the returned variables hold the values the region denotes. -/
theorem nfToJasminBody_sem_frames (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts),
      p.callFree = true → widthsGo p = true →
      ∀ {loc : Nat} {env : List JVar} {d n : Nat} {out : JOut}, linGo p loc = true →
      nfToJasminBody env p d n = some out →
      ∀ {c' : List MInstr}, translateCmdExt out.code = some c' →
      ∀ {V : Ctxt.Valuation Γ} {r : HVector (fun t => ⟦t⟧) ts}, p.denoteAt E fuel V = some r →
      IdxInBounds E fuel p V →
      ∀ {s : Estate SyscallState Mem}, JazzStoreAgrees env d (fun i => usesIdx p i = true) V s →
      ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ JazzResAgrees out.res r s' := by
  intro Γ ts p hcf hw loc env d n out hlin hout c' hc V r hden hidx s hs
  obtain ⟨s', hsem, hpost⟩ :=
    nfToJasminRegion_sim aS opS gd prog E fuel haS hop p hcf hw hlin hout hc hden hidx hs
  exact ⟨s', hsem, hpost.res⟩

end Sim

end CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSemFrames
