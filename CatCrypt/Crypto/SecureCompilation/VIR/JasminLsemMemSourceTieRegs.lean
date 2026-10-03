/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoopsJ

@[expose] public section

set_option autoImplicit false

/-!
# The carried-register loop node against its source fold

`JasminLsemExportCanon.canonNodeRM_faithful` runs the canonicalised node of a loop that
carries one array. This module states the same for a counted loop that carries a tuple
`cs = stackArr w n :: rs`: the output array and registers of the types `rs`. The body is a
straight-line `MultiReturnCom` over `cs ++ reg 64 :: invTys`. Its model chain is
`straightOpsMem` of the single-return projection `MultiReturnCom.toComHead`, which keeps
every binding; the scalar results are read off the chain's final store agreement
(`mstraightOps_agree`, `mret_reg`). The carried registers are re-seeded on every trip by a
list of register moves (`movesRM`, `runStraightF_movesRM`), and the trip state is related
to the source tuple by a store agreement of its pullback along the canonicalisation
renaming at the trip valuation `tripValJ`, which covers the array at `out` and every
carried register at its name together.

## Main definitions

* `tripValJ` — the trip valuation `accs ++ [ofNat t] ++ invs`.
* `MRetAgree`, `canonRets` — the store agreement at a multi-result body's return, and the
  model operands of its returned variables.
* `movesRM` — a list of register moves.
* `CanonRenJ` — the hypotheses on the canonicalisation renaming of a carried-register node.
* `FeedOKJ`, `SeedOKJ` — the conditions on the feedback and seed segments: they write each
  carried register from its source and keep every other register cell.
* `canonBodyJ`, `canonNodeJ` — the canonicalised looped segment and node.
* `LoopRenJ` — the renaming from the model's trip-context names to the export walk's.

## Main results

* `runBoundedStraightF_rel`, `runBoundedLoopMem_rel` — the trip folds of the flag machine
  and of the counter-loop machine carry any relation that one trip preserves, to the
  source fold.
* `mstraightOps_agree` — the model chain of an `ArrMemN` body runs into a state that agrees
  with the body's final valuation.
* `mret_reg`, `mret_arr` — the returned operands read the multi-result denotation.
* `runStraightF_movesRM` — register moves with distinct targets, whose sources are no other
  move's target, act as a parallel assignment.
* `canonBodyJ_trip` — one trip of the canonicalised segment steps the tuple by the body.
* `canonNodeJ_faithful` — the canonicalised node halts with the array at `out` decoding to
  the array component of the source fold.
* `loopResolveVarR_eq_ren`, `loopBodyWalkR_rets` — the export walk resolves every variable,
  and returns every result, as the renamed model resolution.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieRegs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagInvTouch
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend inlHom inrHom hvToHom
  lookup_inlHom lookup_inrHom)
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
  (regName_ne_loopIdx regName_ne_loopCtr loopIdx_ne_loopCtr)

/-! ## 1. The relational trip folds -/

/-- **The flag-machine trip fold carries a relation.** If the start state relates to `a0` at
    trip `0` and one run of `body` from a state related at trip `t` to `a` lands, after the
    back-edge's `setLpc q`, in a state related at trip `t + 1` to `step t a`, then every
    trip count `m` has a fold state related at `m` to the `m`-fold of `step`. -/
theorem runBoundedStraightF_rel {α : Type} (body : List LinstrRM) (q : Nat)
    (R : Nat → LstateM → α → Prop) (step : Nat → α → α) (s0 : LstateM) (a0 : α)
    (h0 : R 0 s0 a0)
    (hstep : ∀ t s a, R t s a → ∃ s' zf', runStraightF body s false = some (s', zf')
      ∧ R (t + 1) (s'.setLpc q) (step t a)) :
    ∀ m, ∃ s, runBoundedStraightF body q m s0 = some s
      ∧ R m s ((List.range m).foldl (fun a t => step t a) a0) := by
  intro m
  induction m with
  | zero => exact ⟨s0, rfl, h0⟩
  | succ k ih =>
      obtain ⟨s, hs, hR⟩ := ih
      obtain ⟨s', zf', hrun, hR'⟩ := hstep k s _ hR
      refine ⟨s'.setLpc q, ?_, ?_⟩
      · rw [runBoundedStraightF_succ_right, hs, Option.bind_some, hrun]
        rfl
      · rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact hR'

/-- **The counter-loop trip fold carries a relation**: the relational form of
    `JasminLsemMemSourceTie.runBoundedLoopMem_decodes_denote`, for a relation between the
    machine state and any source value (the array at the output name together with the
    carried registers at their names). -/
theorem runBoundedLoopMem_rel {α : Type} (body : List LinstrRM)
    (R : Nat → LstateM → α → Prop) (step : Nat → α → α) (s0 : LstateM) (a0 : α)
    (h0 : R 0 s0 a0) :
    ∀ m : Nat,
      (∀ t, t < m → ∀ (bt : LstateM) (a : α), runBoundedLoopMem body t s0 = some bt →
        R t bt a → ∃ bt', lsemStraightMem body bt = some bt' ∧ R (t + 1) (bt'.setLpc 1)
          (step t a)) →
      ∀ bfin : LstateM, runBoundedLoopMem body m s0 = some bfin →
        R m bfin ((List.range m).foldl (fun a t => step t a) a0) := by
  intro m
  induction m with
  | zero =>
      intro _ bfin hrun
      rw [runBoundedLoopMem_zero] at hrun
      obtain rfl := Option.some.inj hrun
      exact h0
  | succ k ih =>
      intro hsim bfin hrun
      rw [runBoundedLoopMem_succ_right] at hrun
      cases hbk : runBoundedLoopMem body k s0 with
      | none => rw [hbk] at hrun; simp at hrun
      | some bk =>
          rw [hbk, Option.bind_some] at hrun
          have hdk := ih (fun t ht => hsim t (Nat.lt_succ_of_lt ht)) bk hbk
          obtain ⟨bt', hbt', hR'⟩ := hsim k (Nat.lt_succ_self k) bk _ hbk hdk
          rw [hbt', Option.map_some] at hrun
          obtain rfl := Option.some.inj hrun
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact hR'

/-! ## 2. Trip valuations and the agreement at the argument depth -/

/-- The trip valuation of a carried-register loop body: the carried tuple `accs`, the trip
    index `ofNat t`, the invariants `invs`. -/
def tripValJ {cs invTys : Ctxt jasminDialect} (accs : Ctxt.Valuation cs) (t : Nat)
    (invs : Ctxt.Valuation invTys) : Ctxt.Valuation (cs ++ JasminTy.reg 64 :: invTys) :=
  hvAppend accs (.cons (BitVec.ofNat 64 t) invs)

/-- At the argument depth a variable resolves to the argument name of its root slot. -/
theorem resolveVar_args {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) :
    resolveVar Γ.length Γ.length argName (fun _ => none) v
      = .reg (argName (Γ.length - 1 - varIndex v)) := by
  have := JasminLsemSimulation.varIndex_lt v
  simp only [resolveVar]
  rw [if_pos (by omega)]

/-- **Agreement at the argument depth from reads.** A state that reads every register
    variable and every array variable of `Γ` at the argument name of its root slot agrees
    with the valuation at the argument depth. -/
theorem storeAgreesM_args {Γ : Ctxt jasminDialect} {s : LstateM} {V : Ctxt.Valuation Γ}
    (hr : ∀ {w : Nat} (v : Ctxt.Var Γ (.reg w)),
      s.reg.getW (argName (Γ.length - 1 - varIndex v)) w = some (v.lookup V))
    (ha : ∀ {w n : Nat} (v : Ctxt.Var Γ (.stackArr w n)),
      s.getArr (argName (Γ.length - 1 - varIndex v)) w n = some (v.lookup V)) :
    StoreAgreesM Γ.length Γ.length s V := by
  refine ⟨fun {w} v => ?_, fun {w n} v => ?_⟩
  · rw [resolveVar_args, evalOperandN]
    exact hr v
  · rw [resolveVar_args]
    exact ha v

/-- The register reads of an agreement at the argument depth. -/
theorem storeAgreesM_args_reg {Γ : Ctxt jasminDialect} {s : LstateM} {V : Ctxt.Valuation Γ}
    (h : StoreAgreesM Γ.length Γ.length s V) {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
    s.reg.getW (argName (Γ.length - 1 - varIndex v)) w = some (v.lookup V) := by
  have := h.1 v
  rw [resolveVar_args, evalOperandN] at this
  exact this

/-- The array reads of an agreement at the argument depth. -/
theorem storeAgreesM_args_arr {Γ : Ctxt jasminDialect} {s : LstateM} {V : Ctxt.Valuation Γ}
    (h : StoreAgreesM Γ.length Γ.length s V) {w n : Nat} (v : Ctxt.Var Γ (.stackArr w n)) :
    s.getArr (argName (Γ.length - 1 - varIndex v)) w n = some (v.lookup V) := by
  have := h.2 v
  rw [resolveVar_args] at this
  exact this

/-- A variable of an appended context is the left or the right injection of a variable. -/
theorem var_append_cases {xs ys : Ctxt jasminDialect} {t : JasminTy} :
    ∀ v : Ctxt.Var (xs ++ ys) t,
      (∃ u : Ctxt.Var xs t, v = inlHom ys u) ∨ (∃ u : Ctxt.Var ys t, v = inrHom xs u) := by
  induction xs with
  | nil => intro v; exact Or.inr ⟨v, rfl⟩
  | cons x xs ih =>
      intro v
      cases v with
      | here => exact Or.inl ⟨.here, rfl⟩
      | there v =>
          rcases ih v with ⟨u, rfl⟩ | ⟨u, rfl⟩
          · exact Or.inl ⟨.there u, rfl⟩
          · exact Or.inr ⟨u, rfl⟩

theorem varIndex_inlHom {xs : Ctxt jasminDialect} (ys : Ctxt jasminDialect) {t : JasminTy} :
    ∀ u : Ctxt.Var xs t, varIndex (inlHom ys u) = varIndex u
  | .here => rfl
  | .there u => by
      show varIndex (inlHom ys u) + 1 = varIndex u + 1
      rw [varIndex_inlHom ys u]

theorem varIndex_inrHom : ∀ (xs : Ctxt jasminDialect) {ys : Ctxt jasminDialect} {t : JasminTy}
    (u : Ctxt.Var ys t), varIndex (inrHom xs u) = xs.length + varIndex u
  | [], _, _, u => by simp [inrHom]
  | _ :: xs, _, _, u => by
      show varIndex (inrHom xs u) + 1 = _
      rw [varIndex_inrHom xs u, List.length_cons]
      omega

/-- The type of a variable is a member of its context. -/
theorem var_mem {Γ : Ctxt jasminDialect} {t : JasminTy} : Ctxt.Var Γ t → t ∈ Γ
  | .here => List.mem_cons_self
  | .there v => List.mem_cons_of_mem _ (var_mem v)

/-! ## 3. The store agreement at a multi-result return -/

/-- The store agreement of a state with the final valuation of a multi-result body: at its
    return, the state agrees with the valuation extended by every binding. -/
def MRetAgree (nArgs : Nat) (st : LstateM) : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    MultiReturnCom jasminDialect Γ ts → Nat → Ctxt.Valuation Γ → Prop
  | _, _, .ret _, cd, V => StoreAgreesM nArgs cd st V
  | _, _, .var e body, cd, V => MRetAgree nArgs st body (cd + 1) (V.extend (e.denote V))

/-- The model operands of the returned variables of a multi-result body walked from depth
    `cd`. -/
def canonRets (nArgs : Nat) : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    MultiReturnCom jasminDialect Γ ts → Nat → List LOperand
  | _, _, .ret vs, cd => exprArgsHV cd nArgs argName (fun _ => none) vs
  | _, _, .var _ body, cd => canonRets nArgs body (cd + 1)

/-- The operand list of a variable vector at the position of a variable of its type list. -/
theorem exprArgsHV_getD {Γ : Ctxt jasminDialect} (cd nArgs : Nat) :
    ∀ {ts : List JasminTy} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts) {t : JasminTy}
      (u : Ctxt.Var ts t),
      (exprArgsHV cd nArgs argName (fun _ => none) vs).getD (varIndex u) (.imm 0)
        = resolveVar cd nArgs argName (fun _ => none) (hvToHom vs u)
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ rest, _, .there u => by
      show (exprArgsHV cd nArgs argName (fun _ => none) rest).getD (varIndex u) (.imm 0) = _
      exact exprArgsHV_getD cd nArgs rest u

/-- Looking up a returned position is looking up the returned variable. -/
theorem lookupVars_lookup {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    ∀ {ts : List JasminTy} (vs : HVector (fun ty => Ctxt.Var Γ ty) ts) {t : JasminTy}
      (u : Ctxt.Var ts t),
      u.lookup (MultiReturnCom.lookupVars vs V) = (hvToHom vs u).lookup V
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ rest, _, .there u => lookupVars_lookup V rest u

/-- **The returned registers read the denotation.** -/
theorem mret_reg {nArgs : Nat} {st : LstateM} :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (m : MultiReturnCom jasminDialect Γ ts)
      (cd : Nat) (V : Ctxt.Valuation Γ), MRetAgree nArgs st m cd V →
      ∀ {w : Nat} (u : Ctxt.Var ts (JasminTy.reg w)),
        evalOperandN st.reg w ((canonRets nArgs m cd).getD (varIndex u) (.imm 0))
          = some (u.lookup (m.denote V))
  | _, _, .ret vs, cd, V, h, _, u => by
      show evalOperandN st.reg _ ((exprArgsHV cd nArgs argName (fun _ => none) vs).getD _ _)
        = some (u.lookup (MultiReturnCom.lookupVars vs V))
      rw [exprArgsHV_getD, lookupVars_lookup]
      exact h.1 (hvToHom vs u)
  | _, _, .var e body, cd, V, h, _, u => mret_reg body (cd + 1) _ h u

/-- **The returned arrays read the denotation.** -/
theorem mret_arr {nArgs : Nat} {st : LstateM} :
    ∀ {Γ : Ctxt jasminDialect} {ts : Ctxt jasminDialect} (m : MultiReturnCom jasminDialect Γ ts)
      (cd : Nat) (V : Ctxt.Valuation Γ), MRetAgree nArgs st m cd V →
      ∀ {w n : Nat} (u : Ctxt.Var ts (JasminTy.stackArr w n)),
        st.getArr (operandName ((canonRets nArgs m cd).getD (varIndex u) (.imm 0))) w n
          = some (Ctxt.Var.lookup (d := jasminDialect) u (m.denote V))
  | _, _, .ret vs, cd, V, h, _, _, u => by
      have h1 : canonRets nArgs (MultiReturnCom.ret vs) cd
          = exprArgsHV cd nArgs argName (fun _ => none) vs := rfl
      have h2 : (MultiReturnCom.ret (d := jasminDialect) vs).denote V
          = MultiReturnCom.lookupVars vs V := rfl
      rw [h1, h2, exprArgsHV_getD, lookupVars_lookup]
      exact h.2 (hvToHom vs u)
  | _, _, .var e body, cd, V, h, _, _, u => mret_arr body (cd + 1) _ h u

/-- The single-return projection of a return. -/
theorem toComHead_ret {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (v : Ctxt.Var Γ t) (rest : HVector (fun ty => Ctxt.Var Γ ty) ts) :
    (MultiReturnCom.ret (d := jasminDialect) (.cons v rest)).toComHead = Com.ret v := by
  rw [MultiReturnCom.toComHead]

/-- The single-return projection of a binding. -/
theorem toComHead_var {Γ : Ctxt jasminDialect} {t t' : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t') (body : MultiReturnCom jasminDialect (t' :: Γ) (t :: ts)) :
    (MultiReturnCom.var e body).toComHead = Com.var e body.toComHead := by
  rw [MultiReturnCom.toComHead]

/-- **The model chain of a multi-result body.** From a state agreeing with `V`, the model
    chain `straightOpsMem` of the single-return projection of an `ArrMemN` body runs to
    completion, writes only the fresh `regName` block at depth `≥ cd`, and lands in a state
    that agrees with the body's final valuation at its return. -/
theorem mstraightOps_agree {w n : Nat} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (m : MultiReturnCom jasminDialect Γ (JasminTy.stackArr w n :: ts))
    (hm : ArrMemN m.toComHead) {nArgs cd : Nat} {st : LstateM} {V : Ctxt.Valuation Γ}
    (hlen : Γ.length = cd) (harg : nArgs ≤ cd) (hag : StoreAgreesM nArgs cd st V) :
    ∃ st', lsemStraightMem (straightOpsMem nArgs m.toComHead cd) st = some st'
      ∧ WriteFrame cd st st' ∧ MRetAgree nArgs st' m cd V :=
  match m, hm with
  | .ret (.cons _ _), _ => by
      refine ⟨st, ?_, WriteFrame.refl _ st, hag⟩
      rw [toComHead_ret]
      rfl
  | .var e body, hm => by
      have ih : ArrMemN body.toComHead → ∀ {cd' : Nat} {st' : LstateM}
          {V' : Ctxt.Valuation _}, List.length _ = cd' → nArgs ≤ cd' →
          StoreAgreesM nArgs cd' st' V' →
          ∃ st'', lsemStraightMem (straightOpsMem nArgs body.toComHead cd') st' = some st''
            ∧ WriteFrame cd' st' st'' ∧ MRetAgree nArgs st'' body cd' V' :=
        fun hb {cd'} {st'} {V'} h1 h2 h3 => mstraightOps_agree body hb h1 h2 h3
      rw [toComHead_var]
      have hm' : ArrMemN (Com.var e body.toComHead) := by rw [← toComHead_var]; exact hm
      cases hm' with
      | reg e he hbody =>
          obtain ⟨st1, hrun1, hAg1, hFr1⟩ :=
            lsemStraightMem_straightOps_store he (nArgs := nArgs) (curDepth := cd)
              hlen harg hag
          simp only [comLen, comDenoteLets] at hAg1
          obtain ⟨st2, hrun2, hFr2, hret2⟩ := ih hbody
            (cd' := cd + 1) (st' := st1) (V' := V.extend (e.denote V))
            (by simp [List.length_cons, hlen]) (by omega) hAg1
          refine ⟨st2, ?_, WriteFrame.comp hFr1 hFr2, hret2⟩
          rw [straightOpsMem_var_split, lsemStraightMem_append, hrun1, Option.bind_some]
          exact hrun2
      | store heq args hbody =>
          have hstep := lsemStepMem_store (V := V) (st := st) (nArgs := nArgs)
            (curDepth := cd) heq args hag
          have hagree' := StoreAgreesM.stepArr
            ((⟨JasminOp.stackStore _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
            hlen harg hag
          obtain ⟨st2, hrun2, hFr2, hret2⟩ := ih hbody
            (cd' := cd + 1) (by simp [List.length_cons, hlen]) (by omega) hagree'
          refine ⟨st2, ?_, WriteFrame.stepArr _ hFr2, hret2⟩
          rw [straightOpsMem_store, lsemStraightMem_cons, hstep]
          exact hrun2
termination_by sizeOf m

/-! ## 4. Register moves as a parallel assignment -/

/-- The register moves `MOV p.1, p.2`, one per pair. -/
def movesRM (ps : List (String × String)) : List LinstrRM :=
  ps.map fun p => (.Lopn [.reg p.1] (withWidthTag 64 "MOV") [.reg p.2], MemTag.reg none)

/-- **Register moves act as a parallel assignment.** For moves with pairwise distinct
    targets whose sources are no other move's target, the run writes at each target the
    cell its source held before the run, keeps every other register cell, the array
    carrier and the word memory, and keeps the flag. -/
theorem runStraightF_movesRM :
    ∀ (ps : List (String × String)), (ps.map Prod.fst).Nodup →
      (∀ p ∈ ps, ∀ q ∈ ps, p.2 = q.1 → p = q) →
      ∀ (s : LstateM) (zf : Bool), ∃ s', runStraightF (movesRM ps) s zf = some (s', zf)
        ∧ s'.larr = s.larr ∧ s'.lmem = s.lmem
        ∧ (∀ p ∈ ps, s'.reg.lvm p.1 = s.reg.lvm p.2)
        ∧ (∀ r, r ∉ ps.map Prod.fst → s'.reg.lvm r = s.reg.lvm r)
  | [], _, _, s, zf => ⟨s, rfl, rfl, rfl, by simp, fun _ _ => rfl⟩
  | p :: ps, hnd, hsrc, s, zf => by
      rw [List.map_cons, List.nodup_cons] at hnd
      set s1 := (s.setReg p.1 (s.reg.lvm p.2).2).nextPc with hs1
      have hsrc' : ∀ a ∈ ps, ∀ b ∈ ps, a.2 = b.1 → a = b := fun a ha b hb =>
        hsrc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
      obtain ⟨s', hrun, hl, hm, hps, hother⟩ := runStraightF_movesRM ps hnd.2 hsrc' s1 zf
      have hl1 : ∀ r, s1.reg.lvm r = if r = p.1 then s.reg.lvm p.2 else s.reg.lvm r := by
        intro r
        simp [hs1, LstateM.nextPc, LstateM.setReg, LstateN.setReg, LstateN.nextPc]
      refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
      · rw [movesRM, List.map_cons, runStraightF_cons, fstepF_movReg, Option.bind_some]
        exact hrun
      · rw [hl]; rfl
      · rw [hm]; rfl
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · rw [hother _ hnd.1, hl1, if_pos rfl]
        · rw [hps q hq', hl1, if_neg]
          intro he
          have hqp := hsrc q (List.mem_cons_of_mem _ hq') _ List.mem_cons_self he
          rw [hqp] at hq'
          exact hnd.1 (List.mem_map_of_mem (f := Prod.fst) hq')
      · intro r hr
        rw [List.map_cons, List.mem_cons, not_or] at hr
        rw [hother r hr.2, hl1, if_neg hr.1]

/-! ## 5. The trip agreement of a carried tuple -/

section Trip

variable {w n : Nat} {rs invTys : Ctxt jasminDialect}

/-- The argument count of a carried-register loop body over the tuple `stackArr w n :: rs`
    and the invariants `invTys`: the carried tuple, the index and the invariants. -/
abbrev nArgsJ (rs invTys : Ctxt jasminDialect) : Nat := rs.length + 2 + invTys.length

theorem length_ctxJ :
    (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys).length = nArgsJ rs invTys := by
  simp only [List.cons_append, List.length_cons, List.length_append, nArgsJ]
  omega

/-- **The trip agreement from reads.** A state agrees at the argument depth with the trip
    valuation `tripValJ accs t invs` when it holds the array of `accs` at the array argument,
    each carried register at its argument, the index and each invariant at theirs. -/
theorem tripAgreeJ_of (hNoArr : ∀ w' n', JasminTy.stackArr w' n' ∉ rs) {s : LstateM}
    {accs : Ctxt.Valuation (JasminTy.stackArr w n :: rs)} {t : Nat}
    {invs : Ctxt.Valuation invTys}
    (harr : s.getArr (argName (invTys.length + rs.length + 1)) w n
      = some ((Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup accs))
    (hcar : ∀ {w' : Nat} (u : Ctxt.Var rs (JasminTy.reg w')),
      s.reg.getW (argName (invTys.length + rs.length - varIndex u)) w'
        = some ((Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup accs))
    (hidx : s.reg.getW (argName invTys.length) 64 = some (BitVec.ofNat 64 t))
    (hinvR : ∀ {w' : Nat} (u : Ctxt.Var invTys (JasminTy.reg w')),
      s.reg.getW (argName (invTys.length - 1 - varIndex u)) w' = some (u.lookup invs))
    (hinvA : ∀ {w' n' : Nat} (u : Ctxt.Var invTys (JasminTy.stackArr w' n')),
      s.getArr (argName (invTys.length - 1 - varIndex u)) w' n' = some (u.lookup invs)) :
    StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) s (tripValJ accs t invs) := by
  have h := storeAgreesM_args (Γ := JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys)
    (s := s) (V := tripValJ accs t invs) ?_ ?_
  · rw [length_ctxJ] at h
    exact h
  · intro w' v
    rw [length_ctxJ]
    rcases var_append_cases v with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rw [tripValJ, lookup_inlHom, varIndex_inlHom]
      match u with
      | .there u =>
          have hu := JasminLsemSimulation.varIndex_lt u
          convert hcar u using 3
          simp only [varIndex, nArgsJ]
          omega
    · rw [tripValJ, lookup_inrHom, varIndex_inrHom]
      match u with
      | .here =>
          have e : nArgsJ rs invTys - 1 - ((JasminTy.stackArr w n :: rs).length
              + varIndex (Ctxt.Var.here : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
              = invTys.length := by
            simp only [varIndex, List.length_cons, nArgsJ]; omega
          rw [e]
          exact hidx
      | .there u =>
          have hu := JasminLsemSimulation.varIndex_lt u
          have e : nArgsJ rs invTys - 1 - ((JasminTy.stackArr w n :: rs).length
              + varIndex (Ctxt.Var.there u : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
              = invTys.length - 1 - varIndex u := by
            simp only [varIndex, List.length_cons, nArgsJ]; omega
          rw [e]
          exact hinvR u
  · intro w' n' v
    rw [length_ctxJ]
    rcases var_append_cases v with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rw [tripValJ, lookup_inlHom, varIndex_inlHom]
      match u with
      | .here =>
          convert harr using 3
          simp only [varIndex, nArgsJ]
          omega
      | .there u => exact absurd (var_mem u) (hNoArr _ _)
    · rw [tripValJ, lookup_inrHom, varIndex_inrHom]
      match u with
      | .there u =>
          have hu := JasminLsemSimulation.varIndex_lt u
          have e : nArgsJ rs invTys - 1 - ((JasminTy.stackArr w n :: rs).length
              + varIndex (Ctxt.Var.there u : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
              = invTys.length - 1 - varIndex u := by
            simp only [varIndex, List.length_cons, nArgsJ]; omega
          rw [e]
          exact hinvA u

/-- The reads of a trip agreement: the index and the invariants at their arguments. -/
theorem tripAgreeJ_reads {s : LstateM}
    {accs : Ctxt.Valuation (JasminTy.stackArr w n :: rs)} {t : Nat}
    {invs : Ctxt.Valuation invTys}
    (h : StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) s (tripValJ accs t invs)) :
    s.getArr (argName (invTys.length + rs.length + 1)) w n
        = some ((Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup accs)
    ∧ s.reg.getW (argName invTys.length) 64 = some (BitVec.ofNat 64 t)
    ∧ (∀ {w' : Nat} (u : Ctxt.Var invTys (JasminTy.reg w')),
        s.reg.getW (argName (invTys.length - 1 - varIndex u)) w' = some (u.lookup invs))
    ∧ (∀ {w' n' : Nat} (u : Ctxt.Var invTys (JasminTy.stackArr w' n')),
        s.getArr (argName (invTys.length - 1 - varIndex u)) w' n' = some (u.lookup invs)) := by
  rw [← length_ctxJ (w := w) (n := n)] at h
  refine ⟨?_, ?_, fun {w'} u => ?_, fun {w' n'} u => ?_⟩
  · have := storeAgreesM_args_arr h (inlHom (JasminTy.reg 64 :: invTys)
      (Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _))
    rw [tripValJ, lookup_inlHom, varIndex_inlHom, length_ctxJ] at this
    rw [show invTys.length + rs.length + 1 = nArgsJ rs invTys - 1 - varIndex
      (Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _) by
        simp only [varIndex, nArgsJ]; omega]
    exact this
  · have := storeAgreesM_args_reg h (inrHom (JasminTy.stackArr w n :: rs)
      (Ctxt.Var.here : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
    rw [tripValJ, lookup_inrHom, varIndex_inrHom, length_ctxJ] at this
    rw [show invTys.length = nArgsJ rs invTys - 1 - ((JasminTy.stackArr w n :: rs).length
      + varIndex (Ctxt.Var.here : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
      by simp only [varIndex, List.length_cons, nArgsJ]; omega]
    exact this
  · have hu := JasminLsemSimulation.varIndex_lt u
    have := storeAgreesM_args_reg h (inrHom (JasminTy.stackArr w n :: rs)
      (Ctxt.Var.there u : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
    rw [tripValJ, lookup_inrHom, varIndex_inrHom, length_ctxJ] at this
    rw [show invTys.length - 1 - varIndex u = nArgsJ rs invTys - 1
      - ((JasminTy.stackArr w n :: rs).length
        + varIndex (Ctxt.Var.there u : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
      by simp only [varIndex, List.length_cons, nArgsJ]; omega]
    exact this
  · have hu := JasminLsemSimulation.varIndex_lt u
    have := storeAgreesM_args_arr h (inrHom (JasminTy.stackArr w n :: rs)
      (Ctxt.Var.there u : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
    rw [tripValJ, lookup_inrHom, varIndex_inrHom, length_ctxJ] at this
    rw [show invTys.length - 1 - varIndex u = nArgsJ rs invTys - 1
      - ((JasminTy.stackArr w n :: rs).length
        + varIndex (Ctxt.Var.there u : Ctxt.Var (JasminTy.reg 64 :: invTys) _))
      by simp only [varIndex, List.length_cons, nArgsJ]; omega]
    exact this

end Trip

/-! ## 6. One trip of the canonicalised carried-register body -/

/-- The number of bindings of a multi-result body. -/
def mLen : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    MultiReturnCom jasminDialect Γ ts → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => mLen body + 1

/-- The model chain of a multi-result body has one instruction per binding. -/
theorem straightOpsMem_toComHead_length {t : JasminTy} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (nArgs : Nat) (m : MultiReturnCom jasminDialect Γ (t :: ts))
    (cd : Nat) : (straightOpsMem nArgs m.toComHead cd).length = mLen m :=
  match m with
  | .ret (.cons _ _) => by rw [toComHead_ret]; rfl
  | .var e body => by
      have ih := straightOpsMem_toComHead_length nArgs body (cd + 1)
      rw [toComHead_var]
      simp only [straightOpsMem, List.length_cons, ih, mLen]
termination_by sizeOf m

/-- A variable resolved at a depth `cd ≥ nArgs` over a context of length `cd` is a register
    the chain can read at `cd`. -/
theorem resolveVar_resolved {Γ : Ctxt jasminDialect} {t : JasminTy} {nArgs cd : Nat}
    (hlen : Γ.length = cd) (v : Ctxt.Var Γ t) :
    ∃ r, resolveVar cd nArgs argName (fun _ => none) v = .reg r ∧ Resolved nArgs cd r := by
  have hv := JasminLsemSimulation.varIndex_lt v
  simp only [resolveVar]
  by_cases h : cd - 1 - varIndex v < nArgs
  · rw [if_pos h]
    exact ⟨_, rfl, Or.inr (Or.inl ⟨_, h, rfl⟩)⟩
  · rw [if_neg h]
    exact ⟨_, rfl, Or.inr (Or.inr ⟨_, by omega, by omega, rfl⟩)⟩

/-- A returned operand of a multi-result body walked from `cd` is a register the chain can
    read at its final depth. -/
theorem canonRets_resolved {nArgs : Nat} :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (m : MultiReturnCom jasminDialect Γ ts)
      (cd : Nat), Γ.length = cd → ∀ {t : JasminTy} (u : Ctxt.Var ts t),
      ∃ r, (canonRets nArgs m cd).getD (varIndex u) (.imm 0) = .reg r
        ∧ Resolved nArgs (cd + mLen m) r
  | _, _, .ret vs, cd, hlen, _, u => by
      rw [show canonRets nArgs (MultiReturnCom.ret vs) cd
        = exprArgsHV cd nArgs argName (fun _ => none) vs from rfl, exprArgsHV_getD]
      exact resolveVar_resolved hlen _
  | _, _, .var _ body, cd, hlen, _, u => by
      obtain ⟨r, h1, h2⟩ := canonRets_resolved body (cd + 1) (by simp [hlen]) u
      refine ⟨r, h1, ?_⟩
      rw [show cd + mLen (MultiReturnCom.var _ body) = cd + 1 + mLen body by
        simp only [mLen]; omega]
      exact h2

/-- The hypotheses on the renaming `τ` from the model loop's names to the canonicalised
    carried-register node at depth `d`, with `nInv` invariants and `nR` carried registers
    besides the array: the thread hypotheses at `nR + 2 + nInv` arguments; the array argument
    goes to `out`, the carried register argument `argName (nInv + 1 + k)` to `regName (d + k)`,
    the index argument to the loop index; the counter name is fixed; and the images are
    pairwise distinct as the trip needs. -/
structure CanonRenJ (τ : String → String) (d nInv nR : Nat) (S : Nat → Prop) (out : String) :
    Prop extends ThreadRen τ d (nR + 2 + nInv) S out where
  /-- The array argument goes to `out`. -/
  acc : τ (argName (nInv + nR + 1)) = out
  /-- Each carried register argument goes to its register. -/
  car : ∀ k, k < nR → τ (argName (nInv + 1 + k)) = regName (d + k)
  /-- The index argument goes to the loop index. -/
  idx : τ (argName nInv) = loopIdx d
  /-- The counter name is fixed. -/
  ctr : τ (loopCtr d) = loopCtr d
  /-- No invariant argument goes to `out`. -/
  invOut : ∀ j, j < nInv → τ (argName j) ≠ out
  /-- No invariant argument goes to the loop index. -/
  invIdx : ∀ j, j < nInv → τ (argName j) ≠ loopIdx d
  /-- No invariant argument goes to the counter. -/
  invCtr : ∀ j, j < nInv → τ (argName j) ≠ loopCtr d
  /-- No invariant argument goes to a carried register. -/
  invCar : ∀ j, j < nInv → ∀ k, k < nR → τ (argName j) ≠ regName (d + k)
  /-- `out` is no carried register. -/
  carOut : ∀ k, k < nR → regName (d + k) ≠ out
  /-- `out` is not the loop index. -/
  outIdx : out ≠ loopIdx d
  /-- `out` is not the counter. -/
  outCtr : out ≠ loopCtr d
  /-- The counter is no body temporary. -/
  ctrL : ∀ k, loopCtr d ≠ loopReg d k

/-- The feedback condition of a carried-register node: the segment `F` runs from every
    state, keeps the array carrier, writes at each carried register `regName (d + k)` the
    cell the renamed returned operand of position `nR - k` held, and keeps every other
    register cell. -/
def FeedOKJ (τ : String → String) (d nR : Nat) (crets : List LOperand) (F : List LinstrRM) :
    Prop :=
  ∀ (x : LstateM) (zf : Bool), ∃ x' zf', runStraightF F x zf = some (x', zf')
    ∧ x'.larr = x.larr
    ∧ (∀ k, k < nR → x'.reg.lvm (regName (d + k))
        = x.reg.lvm (τ (operandName (crets.getD (nR - k) (.imm 0)))))
    ∧ (∀ r, (∀ k, k < nR → r ≠ regName (d + k)) → x'.reg.lvm r = x.reg.lvm r)

section Body

variable {w n : Nat} {rs invTys : Ctxt jasminDialect}

/-- The model chain of a carried-register body at its argument count. -/
abbrev chainJ (update : MultiReturnCom jasminDialect
    (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)) :
    List LinstrRM :=
  straightOpsMem (nArgsJ rs invTys) update.toComHead (nArgsJ rs invTys)

/-- The model operands of the returned tuple of a carried-register body. -/
abbrev retsJ (update : MultiReturnCom jasminDialect
    (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)) :
    List LOperand :=
  canonRets (nArgsJ rs invTys) update (nArgsJ rs invTys)

/-- The model name of the returned array: the final head of the store thread. -/
abbrev headJ (update : MultiReturnCom jasminDialect
    (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs)) :
    String :=
  operandName ((retsJ update).getD 0 (.imm 0))

/-- The canonicalised looped segment of a carried-register node: the model chain renamed by
    `τ`, the feedback segment `F`, the index and counter updates and the invariant touches. -/
def canonBodyJ (τ : String → String) (d : Nat)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (F : List LinstrRM) (regs : List String) : List LinstrRM :=
  (chainJ update).map (renRM τ) ++ (F ++ (loopAdvanceRM d ++ loopTouchRM d regs))

/-- **One trip of the canonicalised carried-register body.** Let `τ` satisfy `CanonRenJ`,
    let the model chain of an `ArrMemN` body carry a thread certificate from the array
    argument to the returned array, and let `F` satisfy the feedback condition. From a state
    whose pullback along `τ` agrees with the trip-`t` valuation at the tuple `accs`, whose
    invariant base registers read at width `64` and whose counter reads `vn`, the segment
    runs to a state whose pullback agrees with the trip-`(t+1)` valuation at the stepped
    tuple, with the invariant base registers readable and the counter decremented. -/
theorem canonBodyJ_trip {τ : String → String} {d : Nat} {S : Nat → Prop} {out : String}
    (hNoArr : ∀ w' n', JasminTy.stackArr w' n' ∉ rs)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (hupd : ArrMemN update.toComHead) (hτ : CanonRenJ τ d invTys.length rs.length S out)
    (hcert : ThreadCert τ (nArgsJ rs invTys) S out (chainJ update) (nArgsJ rs invTys)
      (argName (invTys.length + rs.length + 1)) (headJ update))
    (F : List LinstrRM) (hF : FeedOKJ τ d rs.length (retsJ update) F)
    (regs : List String) (hregs : ∀ r ∈ regs, ∃ j, j < invTys.length ∧ r = τ (argName j))
    (invs : Ctxt.Valuation invTys) (t : Nat)
    (accs : Ctxt.Valuation (JasminTy.stackArr w n :: rs)) (s' : LstateM)
    (hag : StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) (pullM τ s')
      (tripValJ accs t invs))
    (hinv : ∀ j, j < invTys.length → (s'.reg.getW (τ (argName j)) 64).isSome)
    (vn : BitVec 64) (hn : s'.reg.getW (loopCtr d) 64 = some vn) (zf : Bool) :
    ∃ s'' zf',
      runStraightF (canonBodyJ τ d update F regs) s' zf = some (s'', zf')
      ∧ StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) (pullM τ s'')
          (tripValJ (update.denote (tripValJ accs t invs)) (t + 1) invs)
      ∧ (∀ j, j < invTys.length → (s''.reg.getW (τ (argName j)) 64).isSome)
      ∧ s''.reg.getW (loopCtr d) 64 = some (vn - 1#64) := by
  set N := nArgsJ rs invTys with hN
  set V := tripValJ accs t invs with hV
  have hNv : N = rs.length + 2 + invTys.length := rfl
  obtain ⟨stc, hrunC, hFrC, hretC⟩ := mstraightOps_agree update hupd (nArgs := N) (cd := N)
    length_ctxJ le_rfl hag
  have hR0 : RelM2 τ (ThreadNr τ d N S N) (ThreadNa τ out (argName (invTys.length
      + rs.length + 1))) (pullM τ s') s' :=
    ⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl, rfl⟩
  have hacc : τ (argName (invTys.length + rs.length + 1)) = out := hτ.acc
  obtain ⟨t', hrun', hRt, hE⟩ := lsemStraightMem_thread hτ.toThreadRen _ _ _ _ le_rfl
    hacc hcert hR0 hrunC
  rw [straightOpsMem_toComHead_length] at hRt
  have hargN : ∀ j, j < N → ∀ cd, ThreadNr τ d N S cd (argName j) := fun j hj cd =>
    ThreadNr.of_resolved hτ.toThreadRen (Or.inr (Or.inl ⟨j, hj, rfl⟩))
  -- the argument registers after the chain
  have hreg : ∀ j, j < N → ∀ w',
      t'.reg.getW (τ (argName j)) w' = s'.reg.getW (τ (argName j)) w' := by
    intro j hj w'
    rw [hRt.1.getW (hargN j hj _) w',
      hFrC.1 (argName j) w' (fun k _ => (JasminLsemSimulation.regName_ne_argName k j).symm)]
    rfl
  have harr : ∀ j, j < N → τ (argName j) ≠ out → ∀ w' n',
      t'.getArr (τ (argName j)) w' n' = s'.getArr (τ (argName j)) w' n' := by
    intro j hj hne w' n'
    rw [hRt.getArr (fun he => absurd he hne) w' n',
      hFrC.2 (argName j) w' n' (fun k _ => (JasminLsemSimulation.regName_ne_argName k j).symm)]
    rfl
  -- the returned array at `out`
  have hout : t'.larr out = stc.larr (headJ update) := by
    rw [← hE]
    exact hRt.2.1 _ (fun _ => rfl)
  have hretArr := mret_arr update N V hretC
    (Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _)
  -- the counter and the index after the chain
  have hctr : t'.reg.getW (loopCtr d) 64 = some vn := by
    have h1 := hRt.1.getW (r := loopCtr d)
      (fun k _ _ _ he => absurd (hτ.ctr ▸ he) (hτ.ctrL k)) 64
    rw [hτ.ctr] at h1
    rw [h1, hFrC.1 (loopCtr d) 64 (fun k _ => loopCtr_ne_regName d k)]
    show s'.reg.getW (τ (loopCtr d)) 64 = some vn
    rw [hτ.ctr]
    exact hn
  obtain ⟨hagArr, hagIdx, hagInvR, hagInvA⟩ := tripAgreeJ_reads hag
  have hidx : t'.reg.getW (loopIdx d) 64 = some (BitVec.ofNat 64 t) := by
    have h1 := hreg invTys.length (by omega) 64
    rw [hτ.idx] at h1
    rw [h1, ← hτ.idx]
    exact hagIdx
  -- the chain on the flag machine
  obtain ⟨c, o, hFc⟩ := runStraightF_of_lsemStraightMem _
    (plainLopnBody_map_renRM τ
      (JasminLsemMemFlagArrLoop.arrMemN_straightOpsMem_plain hupd _ _)) s' t' zf hrun'
  set x : LstateM := { t' with cf := c, of := o } with hx
  obtain ⟨x', zf1, hFrun, hFl, hFcar, hFoth⟩ := hF x zf
  have hnotCar : ∀ r, (r = loopIdx d ∨ r = loopCtr d ∨ ∃ j, j < invTys.length
      ∧ r = τ (argName j)) → ∀ k, k < rs.length → r ≠ regName (d + k) := by
    intro r hr k hk
    rcases hr with rfl | rfl | ⟨j, hj, rfl⟩
    · exact fun he => regName_ne_loopIdx _ _ he.symm
    · exact fun he => regName_ne_loopCtr _ _ he.symm
    · exact hτ.invCar j hj k hk
  have hx'get : ∀ r, (∀ k, k < rs.length → r ≠ regName (d + k)) → ∀ w',
      x'.reg.getW r w' = t'.reg.getW r w' := by
    intro r hr w'
    exact getW_congr_cell (hFoth r hr) w'
  have hregs' : ∀ r ∈ regs, (x'.reg.getW r 64).isSome := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := hregs r hr
    rw [hx'get _ (hnotCar _ (Or.inr (Or.inr ⟨j, hj, rfl⟩))) 64, hreg j (by omega) 64]
    exact hinv j hj
  obtain ⟨u', zf', hrunT, hl0, hread0, hcell, hctr'⟩ := canonTail_run d out true regs
    x' zf1 (BitVec.ofNat 64 t) vn
    (by rw [hx'get _ (hnotCar _ (Or.inl rfl)) 64]; exact hidx)
    (by rw [hx'get _ (hnotCar _ (Or.inr (Or.inl rfl))) 64]; exact hctr)
    hregs' (loopIdx_ne_loopCtr d)
  have hul : u'.larr = t'.larr := by rw [hl0, hFl]
  -- reads of the final state off the invariant names
  have hinvRead : ∀ j, j < invTys.length → ∀ w',
      u'.reg.getW (τ (argName j)) w' = s'.reg.getW (τ (argName j)) w' := by
    intro j hj w'
    rw [hread0 _ w' (hτ.invIdx j hj) (hτ.invCtr j hj),
      hx'get _ (hnotCar _ (Or.inr (Or.inr ⟨j, hj, rfl⟩))) w', hreg j (by omega) w']
  refine ⟨u', zf', ?_, ?_, ?_, hctr'⟩
  · unfold canonBodyJ
    rw [runStraightF_append, hFc, Option.bind_some, runStraightF_append, hFrun,
      Option.bind_some]
    exact hrunT
  · refine tripAgreeJ_of hNoArr ?_ ?_ ?_ ?_ ?_
    · rw [pullM_getArr, hacc]
      rw [getArr_congr_cell (s2 := stc) (r2 := headJ update) (by rw [hul, hout]) w n]
      exact hretArr
    · intro w' u
      have hu := JasminLsemSimulation.varIndex_lt u
      have hk : rs.length - 1 - varIndex u < rs.length := by omega
      rw [pullM_getW, show invTys.length + rs.length - varIndex u
        = invTys.length + 1 + (rs.length - 1 - varIndex u) by omega,
        hτ.car _ hk,
        hread0 _ w' (regName_ne_loopIdx _ _) (regName_ne_loopCtr _ _)]
      obtain ⟨r, hr, hres⟩ := canonRets_resolved (nArgs := N) update N length_ctxJ
        (Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _)
      have hcarK := hFcar _ hk
      rw [show rs.length - (rs.length - 1 - varIndex u)
        = varIndex (Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _) by
          simp only [varIndex]; omega, hr] at hcarK
      rw [getW_congr_cell hcarK w']
      show t'.reg.getW (τ r) w' = _
      rw [hRt.1.getW (ThreadNr.of_resolved hτ.toThreadRen hres) w']
      have := mret_reg update N V hretC
        (Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _)
      rw [hr, evalOperandN] at this
      exact this
    · rw [pullM_getW, hτ.idx]
      unfold LstateN.getW
      rw [hcell]
      simp [BitVec.ofNat_add]
    · intro w' u
      have hu := JasminLsemSimulation.varIndex_lt u
      rw [pullM_getW, hinvRead _ (by omega) w']
      exact hagInvR u
    · intro w' n' u
      have hu := JasminLsemSimulation.varIndex_lt u
      rw [pullM_getArr, LstateM.getArr_congr_larr hul,
        harr _ (by omega) (hτ.invOut _ (by omega)) w' n']
      exact hagInvA u
  · intro j hj
    rw [hinvRead j hj 64]
    exact hinv j hj

/-- **The run of the canonicalised carried-register body with its counter.** From a seed
    whose pullback agrees with the trip-`0` valuation at `accs0`, with readable invariant
    base registers and a counter reading `v0`, every trip count `t` has a trip state whose
    pullback agrees with the source fold at `t` and whose counter reads `v0 - t`. -/
theorem canonBodyJ_run {τ : String → String} {d : Nat} {S : Nat → Prop} {out : String}
    (hNoArr : ∀ w' n', JasminTy.stackArr w' n' ∉ rs)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (hupd : ArrMemN update.toComHead) (hτ : CanonRenJ τ d invTys.length rs.length S out)
    (hcert : ThreadCert τ (nArgsJ rs invTys) S out (chainJ update) (nArgsJ rs invTys)
      (argName (invTys.length + rs.length + 1)) (headJ update))
    (F : List LinstrRM) (hF : FeedOKJ τ d rs.length (retsJ update) F)
    (regs : List String) (hregs : ∀ r ∈ regs, ∃ j, j < invTys.length ∧ r = τ (argName j))
    (invs : Ctxt.Valuation invTys) (q : Nat) (s0 : LstateM)
    (accs0 : Ctxt.Valuation (JasminTy.stackArr w n :: rs))
    (hseed : StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) (pullM τ s0)
      (tripValJ accs0 0 invs))
    (hinv : ∀ j, j < invTys.length → (s0.reg.getW (τ (argName j)) 64).isSome)
    (v0 : BitVec 64) (hv0 : s0.reg.getW (loopCtr d) 64 = some v0) :
    ∀ t, ∃ bt,
      runBoundedStraightF (canonBodyJ τ d update F regs) q t s0 = some bt
      ∧ StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) (pullM τ bt)
          (tripValJ ((List.range t).foldl
            (fun a i => update.denote (tripValJ a i invs)) accs0) t invs)
      ∧ (∀ j, j < invTys.length → (bt.reg.getW (τ (argName j)) 64).isSome)
      ∧ bt.reg.getW (loopCtr d) 64 = some (v0 - BitVec.ofNat 64 t) := by
  intro t
  obtain ⟨bt, hbt, hR⟩ := runBoundedStraightF_rel (canonBodyJ τ d update F regs) q
    (fun t s a => StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) (pullM τ s)
        (tripValJ a t invs)
      ∧ (∀ j, j < invTys.length → (s.reg.getW (τ (argName j)) 64).isSome)
      ∧ s.reg.getW (loopCtr d) 64 = some (v0 - BitVec.ofNat 64 t))
    (fun i a => update.denote (tripValJ a i invs)) s0 accs0
    ⟨hseed, hinv, by rw [hv0]; simp⟩
    (fun k s a ⟨hAg, hinvk, hnk⟩ => by
      obtain ⟨s'', zf', hrun, hAg', hinv', hn'⟩ := canonBodyJ_trip hNoArr update hupd hτ
        hcert F hF regs hregs invs k a s hAg hinvk _ hnk false
      refine ⟨s'', zf', hrun, ?_, ?_, ?_⟩
      · rw [pullM_setLpc]
        exact StoreAgreesM.setLpc hAg' q
      · intro j hj
        rw [getW_setLpc]
        exact hinv' j hj
      · rw [getW_setLpc, hn']
        congr 1
        rw [BitVec.sub_sub, BitVec.ofNat_add]) t
  exact ⟨bt, hbt, hR⟩

end Body

/-! ## 7. The canonicalised carried-register node -/

/-- The seed condition of a carried-register node: the segment `G` runs from every state,
    keeps the flag and the array carrier, writes at each carried register `regName (d + k)`
    the cell of its seed source `srcs k`, and keeps every other register cell. -/
def SeedOKJ (d nR : Nat) (srcs : Nat → String) (G : List LinstrRM) : Prop :=
  ∀ (x : LstateM) (zf : Bool), ∃ x', runStraightF G x zf = some (x', zf)
    ∧ x'.larr = x.larr
    ∧ (∀ k, k < nR → x'.reg.lvm (regName (d + k)) = x.reg.lvm (srcs k))
    ∧ (∀ r, (∀ k, k < nR → r ≠ regName (d + k)) → x'.reg.lvm r = x.reg.lvm r)

/-- The index and counter seeds `MOV Lidx, #0 ; MOV Lctr, c`. -/
def idxCtrSeedsRM (d : Nat) (c : String) : List LinstrRM :=
  [ (.Lopn [.reg (loopIdx d)] (withWidthTag 64 "MOV") [.imm 0], MemTag.reg none)
  , (.Lopn [.reg (loopCtr d)] (withWidthTag 64 "MOV") [.reg c], MemTag.reg none) ]

/-- **The index and counter seeds.** They keep the array carrier and every register other
    than the index and the counter; the index reads `0` and the counter reads what `c`
    read. -/
theorem idxCtrSeedsRM_run (d : Nat) (c : String) (hc : c ≠ loopIdx d) (b : LstateM)
    (zf : Bool) :
    ∃ b2, runStraightF (idxCtrSeedsRM d c) b zf = some (b2, zf)
      ∧ b2.larr = b.larr
      ∧ (∀ x w, x ≠ loopCtr d → x ≠ loopIdx d → b2.reg.getW x w = b.reg.getW x w)
      ∧ b2.reg.getW (loopIdx d) 64 = some (0#64)
      ∧ (∀ w, b2.reg.getW (loopCtr d) w = b.reg.getW c w) := by
  set b1 := (b.setReg (loopIdx d) (BitVec.ofNat 64 0)).nextPc with hb1
  set b2 := (b1.setReg (loopCtr d) (b1.reg.lvm c).2).nextPc with hb2
  refine ⟨b2, ?_, rfl, ?_, ?_, ?_⟩
  · unfold idxCtrSeedsRM
    rw [runStraightF_cons,
      fstepF_of_plain _ (by simp [cmpArgs?]) (by simp [movRegArgs?]),
      stepMemF_of_quiet rfl rfl rfl, lsemStepMem_movImm64, Option.map_some, Option.bind_some,
      runStraightF_cons, fstepF_movReg, Option.bind_some, runStraightF_nil]
  · intro x w hx hx'
    rw [hb2, LstateM.getW_setReg_nextPc_other _ _ _ _ _ hx, hb1,
      LstateM.getW_setReg_nextPc_other _ _ _ _ _ hx']
  · rw [hb2, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (loopIdx_ne_loopCtr d)]
    refine (getW_congr_cell (s2 := (b.setReg (loopIdx d) (0#64)).reg) (r2 := loopIdx d)
      ?_ 64).trans ?_
    · simp [hb1, LstateM.nextPc, LstateM.setReg]
    · rw [LstateM.reg_setReg, LstateN.getW_setReg_same]
  · intro w
    have h1 : b2.reg.getW (loopCtr d) w = b1.reg.getW c w := by
      refine getW_congr_cell ?_ w
      simp [hb2, LstateM.nextPc, LstateM.setReg]
    rw [h1, hb1, LstateM.getW_setReg_nextPc_other _ _ _ _ _ hc]

/-- Label positions behind a segment of `Lopn` instructions. -/
theorem findLabelMem_append_lopn (l : LLabel) :
    ∀ (pre rest : List LinstrRM), (∀ i ∈ pre, IsLopn i) →
      findLabelMem l (pre ++ rest) = (findLabelMem l rest).map (· + pre.length)
  | [], rest, _ => by simp
  | i :: pre, rest, h => by
      have ih := findLabelMem_append_lopn l pre rest (fun j hj => h j (List.mem_cons_of_mem _ hj))
      obtain ⟨dd, o, ss, hi⟩ := h i List.mem_cons_self
      unfold findLabelMem JasminLsemLabeled.findLabel at ih ⊢
      rw [List.cons_append, List.map_cons, List.findIdx?_cons, hi]
      simp only [JasminLsemLabeled.isLabel, Bool.false_eq_true, if_false]
      rw [ih, Option.map_map, List.length_cons]
      congr 1

section Node

variable {w n : Nat} {rs invTys : Ctxt jasminDialect}

/-- **The canonicalised carried-register node**: the carried seeds `G`, the index and counter
    seeds, then the zero-trip guarded flag loop over the canonicalised body. -/
def canonNodeJ (τ : String → String) (d : Nat) (c : String)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (G F : List LinstrRM) (regs : List String) : List LinstrRM :=
  (G ++ idxCtrSeedsRM d c)
    ++ guardedFlagLoopLinstrRM d (d + 0x40000000) (loopCtr d) (canonBodyJ τ d update F regs)

/-- Every instruction of the canonicalised body is an `Lopn`, when the feedback segment's
    are. -/
theorem canonBodyJ_isLopn (τ : String → String) (d : Nat)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (F : List LinstrRM) (hFl : ∀ i ∈ F, IsLopn i) (regs : List String) :
    ∀ i ∈ canonBodyJ τ d update F regs, IsLopn i := by
  intro i hi
  simp only [canonBodyJ, List.mem_append, List.mem_map] at hi
  rcases hi with ⟨j, hj, rfl⟩ | hi | hi | hi
  · obtain ⟨dd, o, ss, hd⟩ := JasminLsemMemSourceTie.straightOpsMem_isLopn _ _ _ j hj
    exact ⟨_, o, _, by show renLinstrR τ j.1 = _; rw [hd]; rfl⟩
  · exact hFl i hi
  · simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · simp only [loopTouchRM, List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact ⟨_, _, _, rfl⟩

/-- **The canonicalised carried-register node computes the source fold.** Let `τ` satisfy
    `CanonRenJ`, let the model chain of an `ArrMemN` body carry a thread certificate, let the
    feedback segment `F` and the seed segment `G` satisfy their conditions. Run the node on
    the flag machine from program counter `0`, from a state holding the seed array `accs0`
    at `out`, each carried seed at its source `srcs k`, each invariant at its renamed
    argument, readable invariant base registers, and the count `m < 2^64` at `c`. The run
    halts, and the array at `out` decodes to the array component of the source fold
    `(List.range m).foldl (fun a i => update.denote (tripValJ a i invs)) accs0`. -/
theorem canonNodeJ_faithful {τ : String → String} {d : Nat} {S : Nat → Prop} {out : String}
    (hNoArr : ∀ w' n', JasminTy.stackArr w' n' ∉ rs)
    (update : MultiReturnCom jasminDialect
      (JasminTy.stackArr w n :: rs ++ JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n :: rs))
    (hupd : ArrMemN update.toComHead) (hτ : CanonRenJ τ d invTys.length rs.length S out)
    (hcert : ThreadCert τ (nArgsJ rs invTys) S out (chainJ update) (nArgsJ rs invTys)
      (argName (invTys.length + rs.length + 1)) (headJ update))
    (F : List LinstrRM) (hF : FeedOKJ τ d rs.length (retsJ update) F)
    (hFl : ∀ i ∈ F, IsLopn i)
    (srcs : Nat → String) (G : List LinstrRM) (hG : SeedOKJ d rs.length srcs G)
    (hGl : ∀ i ∈ G, IsLopn i)
    (regs : List String) (hregs : ∀ r ∈ regs, ∃ j, j < invTys.length ∧ r = τ (argName j))
    (invs : Ctxt.Valuation invTys) (fn : String) (c : String) (hc : c ≠ loopIdx d)
    (hcC : ∀ k, k < rs.length → c ≠ regName (d + k))
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (accs0 : Ctxt.Valuation (JasminTy.stackArr w n :: rs))
    (harr0 : b0.getArr out w n
      = some ((Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup accs0))
    (hcar0 : ∀ {w' : Nat} (u : Ctxt.Var rs (JasminTy.reg w')),
      b0.reg.getW (srcs (rs.length - 1 - varIndex u)) w'
        = some ((Ctxt.Var.there u : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup accs0))
    (hinvR0 : ∀ {w' : Nat} (u : Ctxt.Var invTys (JasminTy.reg w')),
      b0.reg.getW (τ (argName (invTys.length - 1 - varIndex u))) w' = some (u.lookup invs))
    (hinvA0 : ∀ {w' n' : Nat} (u : Ctxt.Var invTys (JasminTy.stackArr w' n')),
      b0.getArr (τ (argName (invTys.length - 1 - varIndex u))) w' n' = some (u.lookup invs))
    (hinv : ∀ j, j < invTys.length → (b0.reg.getW (τ (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64) (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn (canonNodeJ τ d c update G F regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out w n
            = some ((Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup
                ((List.range m).foldl (fun a i => update.denote (tripValJ a i invs)) accs0)) := by
  have hBlopn := canonBodyJ_isLopn τ d update F hFl regs
  set B := canonBodyJ τ d update F regs with hB
  set SD := G ++ idxCtrSeedsRM d c with hSD
  have hSDl : ∀ i ∈ SD, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hGl i hi
    · simp only [idxCtrSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  set blks : List FBlock :=
    [.straight SD, .guarded d (d + 0x40000000) (loopCtr d) [.straight B]] with hblks
  have hflat : flatFL blks = canonNodeJ τ d c update G F regs := by
    simp [hblks, canonNodeJ, hB, hSD]
  have hok : FBlocksOK blks := by
    simp only [hblks, FBlocksOK_cons, FBlocksOK_nil, FBlockOK_guarded, FBlockOK_straight,
      and_true]
    exact ⟨hSDl, hBlopn⟩
  have hres : FBlocksResolve (singletonProgM fn (flatFL blks)) blks 0 := by
    rw [hflat]
    simp only [hblks, FBlocksResolve_cons, FBlocksResolve_nil, FBlockResolves_guarded,
      FBlockResolves_straight, and_true, true_and, fflat_straight, fflatFL_cons, fflatFL_nil,
      List.append_nil]
    show findLabelMem d (canonNodeJ τ d c update G F regs) = _
      ∧ findLabelMem (d + 0x40000000) (canonNodeJ τ d c update G F regs) = _
    unfold canonNodeJ
    rw [findLabelMem_append_lopn _ _ _ hSDl, findLabelMem_append_lopn _ _ _ hSDl,
      findLabelMem_guarded_top, findLabelMem_guarded_endL _ _ _ _ hBlopn
        (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide)))]
    refine ⟨?_, ?_⟩ <;> simp <;> omega
  -- the seeds
  obtain ⟨g1, hgrun, hgl, hgcar, hgoth⟩ := hG b0 zf
  obtain ⟨b3, hsrun, hsl, hsoth, hsidx, hsctr⟩ := idxCtrSeedsRM_run d c hc g1 zf
  have hseeds : runStraightF SD b0 zf = some (b3, zf) := by
    rw [hSD, runStraightF_append, hgrun, Option.bind_some]
    exact hsrun
  have hb3l : b3.larr = b0.larr := by rw [hsl, hgl]
  have hinvNe : ∀ j, j < invTys.length → (∀ k, k < rs.length → τ (argName j) ≠ regName (d + k))
      ∧ τ (argName j) ≠ loopCtr d ∧ τ (argName j) ≠ loopIdx d := fun j hj =>
    ⟨fun k hk => hτ.invCar j hj k hk, hτ.invCtr j hj, hτ.invIdx j hj⟩
  have hb3inv : ∀ j, j < invTys.length → ∀ w',
      b3.reg.getW (τ (argName j)) w' = b0.reg.getW (τ (argName j)) w' := by
    intro j hj w'
    obtain ⟨h1, h2, h3⟩ := hinvNe j hj
    rw [hsoth _ w' h2 h3]
    exact getW_congr_cell (hgoth _ h1) w'
  have hAg3 : StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) (pullM τ b3)
      (tripValJ accs0 0 invs) := by
    refine tripAgreeJ_of hNoArr ?_ ?_ ?_ ?_ ?_
    · rw [pullM_getArr, hτ.acc, LstateM.getArr_congr_larr hb3l]
      exact harr0
    · intro w' u
      have hu := JasminLsemSimulation.varIndex_lt u
      have hk : rs.length - 1 - varIndex u < rs.length := by omega
      rw [pullM_getW, show invTys.length + rs.length - varIndex u
        = invTys.length + 1 + (rs.length - 1 - varIndex u) by omega, hτ.car _ hk,
        hsoth _ w' (regName_ne_loopCtr _ _) (regName_ne_loopIdx _ _),
        getW_congr_cell (hgcar _ hk) w']
      exact hcar0 u
    · rw [pullM_getW, hτ.idx, hsidx]
    · intro w' u
      have hu := JasminLsemSimulation.varIndex_lt u
      rw [pullM_getW, hb3inv _ (by omega) w']
      exact hinvR0 u
    · intro w' n' u
      rw [pullM_getArr, LstateM.getArr_congr_larr hb3l]
      exact hinvA0 u
  have hinv3 : ∀ j, j < invTys.length → (b3.reg.getW (τ (argName j)) 64).isSome := by
    intro j hj
    rw [hb3inv j hj 64]
    exact hinv j hj
  have hv3 : b3.reg.getW (loopCtr d) 64 = some (BitVec.ofNat 64 m) := by
    rw [hsctr 64, ← hcnt]
    refine getW_congr_cell (hgoth _ hcC) 64
  have hout : ∀ (s : LstateM) (t : Nat) (a : Ctxt.Valuation (JasminTy.stackArr w n :: rs)),
      StoreAgreesM (nArgsJ rs invTys) (nArgsJ rs invTys) (pullM τ s) (tripValJ a t invs) →
      s.getArr out w n
        = some ((Ctxt.Var.here : Ctxt.Var (JasminTy.stackArr w n :: rs) _).lookup a) := by
    intro s t a h
    have h1 := (tripAgreeJ_reads h).1
    rw [pullM_getArr, hτ.acc] at h1
    exact h1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hrun : runFBsL 1 blks b0 zf
        = some (b3.setLpc (b3.lpc + (flatFL [FBlock.straight B]).length + 6), true) := by
      rw [hblks, runFBsL_cons, runFB_straight, hseeds, Option.bind_some, runFBsL_cons,
        runFB_guarded_zeroTrip 1 _ _ _ _ b3 zf (by simpa using hv3), Option.bind_some,
        runFBsL_nil]
    obtain ⟨k, hk⟩ := flagNest_closed fn blks 1 b0 zf _ _ hpc hok hres hrun
    rw [hflat] at hk
    exact ⟨k, _, hk, hout b3 0 accs0 hAg3⟩
  · have hrunB := canonBodyJ_run hNoArr update hupd hτ hcert F hF regs hregs invs (b3.lpc + 3)
      (b3.setLpc (b3.lpc + 3)) accs0
      (by rw [pullM_setLpc]; exact StoreAgreesM.setLpc hAg3 _)
      (fun j hj => by rw [getW_setLpc]; exact hinv3 j hj)
      (BitVec.ofNat 64 m) (by rw [getW_setLpc]; exact hv3)
    obtain ⟨bfin, hbfin, hAgfin, _, hzfin⟩ := hrunB m
    have hsched := runFRegionF_of_schedule (loopCtr d) [FBlock.straight B] (b3.lpc + 3) 0 m
      (b3.setLpc (b3.lpc + 3)) hm bfin
      (by rw [runBoundedFBs_straight]; exact hbfin)
      (fun i _ him bi hbi => by
        obtain ⟨bi', hbi', _, _, hni⟩ := hrunB i
        rw [runBoundedFBs_straight] at hbi
        rw [hbi] at hbi'
        obtain rfl := Option.some.inj hbi'
        rw [JasminLsemMemFlagArrLoop.condNZ_of_getW _ _ _ hni]
        exact decide_eq_true (JasminLsemMemFlagArrLoop.ofNat_sub_ofNat_ne_zero m i hm64 him))
      (by rw [hzfin]; simp)
    rw [Nat.zero_add] at hsched
    have hne0 : (BitVec.ofNat 64 m == 0#64) = false := by
      have := JasminLsemMemFlagArrLoop.ofNat_sub_ofNat_ne_zero m 0 hm64 hm
      simpa using this
    obtain ⟨bz, hbz, hbzl⟩ : ∃ bz,
        runFB m (.guarded d (d + 0x40000000) (loopCtr d) [.straight B]) b3 zf = some (bz, true)
          ∧ bz.larr = bfin.larr := by
      rw [runFB_guarded, hv3]
      simp only []
      rw [if_neg (by simp [hne0]), hsched]
      exact ⟨_, rfl, rfl⟩
    have hrun : runFBsL m blks b0 zf = some (bz, true) := by
      rw [hblks, runFBsL_cons, runFB_straight, hseeds, Option.bind_some, runFBsL_cons, hbz,
        Option.bind_some, runFBsL_nil]
    obtain ⟨k, hk⟩ := flagNest_closed fn blks m b0 zf _ _ hpc hok hres hrun
    rw [hflat] at hk
    refine ⟨k, _, hk, ?_⟩
    show bz.getArr out w n = _
    rw [LstateM.getArr_congr_larr hbzl]
    exact hout bfin m _ hAgfin

end Node

/-! ## 8. The export walk is the model chain under the loop renaming -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (ComOpsPlain OpPlain)

/-- The renaming hypotheses tying the model's trip-context names of a counted
    carried-register body to the export's names, with `nCar` carried binders and the
    invariant operands `invOps`: the carried argument `argName (nInv + 1 + k)` to
    `regName (d + k)`, the index argument to the loop index, each invariant argument to its
    operand, each chain register to the body temporary of its slot. -/
structure LoopRenJ (σ : String → String) (d nCar : Nat) (invOps : List LOperand) : Prop where
  /-- Each carried argument renames to its register. -/
  car : ∀ k, k < nCar → σ (argName (invOps.length + 1 + k)) = regName (d + k)
  /-- The index argument renames to the loop index. -/
  idx : σ (argName invOps.length) = loopIdx d
  /-- Each invariant argument renames to its operand. -/
  inv : ∀ j, j < invOps.length →
    invOps.getD (invOps.length - 1 - j) (.reg (loopReg d j)) = .reg (σ (argName j))
  /-- Each chain register renames to the body temporary of its slot. -/
  reg : ∀ k, σ (regName k) = loopReg d k

/-- **Resolution commutes with the renaming.** -/
theorem loopResolveVarR_eq_ren {σ : String → String} {d nCar : Nat} {invOps : List LOperand}
    (hσ : LoopRenJ σ d nCar invOps) (curDepth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    loopResolveVarR d d nCar (some (loopIdx d)) invOps curDepth v
      = renOperand σ (resolveVar curDepth (invOps.length + 1 + nCar) argName (fun _ => none)
          v) := by
  unfold loopResolveVarR resolveVar
  dsimp only
  generalize curDepth - 1 - varIndex v = slot
  by_cases h1 : slot < invOps.length
  · rw [if_pos h1, if_pos (by omega), hσ.inv slot h1]
    rfl
  · rw [if_neg h1]
    simp only [Option.isSome_some, if_true]
    by_cases h2 : slot = invOps.length
    · subst h2
      rw [if_pos rfl, if_pos (by omega)]
      simp [renOperand, hσ.idx]
    · rw [if_neg h2]
      by_cases h3 : slot < invOps.length + 1 + nCar
      · rw [if_pos h3, if_pos h3]
        simp only [renOperand]
        have := hσ.car (slot - invOps.length - 1) (by omega)
        rw [show invOps.length + 1 + (slot - invOps.length - 1) = slot by omega] at this
        rw [this]
      · rw [if_neg h3, if_neg h3]
        simp [renOperand, hσ.reg]

/-- The variable-vector walk resolves every variable to the renaming of the model's. -/
theorem loopVarsR_eq_ren {σ : String → String} {d nCar : Nat} {invOps : List LOperand}
    (hσ : LoopRenJ σ d nCar invOps) (curDepth : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      loopVarsR d d nCar (some (loopIdx d)) invOps curDepth hv
        = (exprArgsHV curDepth (invOps.length + 1 + nCar) argName (fun _ => none) hv).map
            (renOperand σ)
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show loopResolveVarR d d nCar (some (loopIdx d)) invOps curDepth v
          :: loopVarsR d d nCar (some (loopIdx d)) invOps curDepth rest = _
      rw [loopResolveVarR_eq_ren hσ, loopVarsR_eq_ren hσ curDepth rest]
      rfl

/-- `exprArgs.go` is `exprArgsHV`. -/
theorem exprArgs_go_eq_HV (curDepth nArgs : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      exprArgs.go curDepth nArgs argName (fun _ => none) hv
        = exprArgsHV curDepth nArgs argName (fun _ => none) hv
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show _ :: exprArgs.go curDepth nArgs argName (fun _ => none) rest = _ :: _
      rw [exprArgs_go_eq_HV curDepth nArgs rest]

/-- The returned operands of the export walk are the renamed model operands. -/
theorem loopBodyWalkR_rets {σ : String → String} {d nCar : Nat} {invOps : List LOperand}
    (hσ : LoopRenJ σ d nCar invOps) :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (m : MultiReturnCom jasminDialect Γ ts)
      (cd : Nat),
      (loopBodyWalkR d d nCar (some (loopIdx d)) invOps m cd).2.1
        = (canonRets (invOps.length + 1 + nCar) m cd).map (renOperand σ)
  | _, _, .ret vs, cd => loopVarsR_eq_ren hσ cd vs
  | _, _, .var _ body, cd => loopBodyWalkR_rets hσ body (cd + 1)

/-- The export walk ends at the depth after its bindings. -/
theorem loopBodyWalkR_depth (d base nCar : Nat) (idx : Option String) (invOps : List LOperand) :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (m : MultiReturnCom jasminDialect Γ ts)
      (cd : Nat), (loopBodyWalkR d base nCar idx invOps m cd).2.2 = cd + mLen m
  | _, _, .ret _, cd => rfl
  | _, _, .var _ body, cd => by
      show (loopBodyWalkR d base nCar idx invOps body (cd + 1)).2.2 = _
      rw [loopBodyWalkR_depth d base nCar idx invOps body (cd + 1)]
      simp only [mLen]
      omega

/-- The single-return projection keeps the plain-op condition of every binding. -/
theorem comOpsPlain_toComHead_var {Γ : Ctxt jasminDialect} {t t' : JasminTy}
    {ts : List JasminTy} (e : Expr jasminDialect Γ t')
    (body : MultiReturnCom jasminDialect (t' :: Γ) (t :: ts))
    (h : ComOpsPlain (MultiReturnCom.var e body).toComHead) :
    OpPlain e.op ∧ ComOpsPlain body.toComHead := by
  rw [toComHead_var] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieRegs
