/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSemFrames
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminSpill

/-!
# Calls and functions of the Jasmin lowering in the `psem.v` mirror

The code `nfToJasminBody` emits for a region with calls runs in the mirror's `Sem` when each
callee of the call environment is a function of the mirror program that computes the callee
on agreeing words and word arrays (`JazzCallsAgree`), and the function `nfToJasmin` builds
runs in the mirror's `SemCall` from arguments that agree with the valuation of the program to
a result that agrees with its denotation (`nfToJasmin_sem`). The run of the function after
the spill pass comes from the run before it by `JasminSpill.spillFn_sem`.

## Calls

A call `f(args)` of the lowering is the mirror instruction `Ccall [r] f args` whose result
variable `r` is the binding at the current depth. The mirror runs the callee from the
syscall state and the memory of the caller; `JazzCallsAgree` asks of each callee a run
that keeps both, as a callee of the dialect computes on words and word arrays held in
variables. The frame of `RegionPost` then holds across a call unchanged.

## Main results

* `JazzValsAgrees`, `JazzCallsAgree`: agreement of mirror values with a tuple, and of the
  functions of a mirror program with a call environment.
* `sim_call`, `nfToJasminRegion_sim_calls`: regions with calls simulate.
* `JazzArgsAgree`, `nfToJasmin_sem`: the function of `nfToJasmin` runs in `SemCall`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSemFn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSem
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSemFrames
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (varIndex)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (wordSig wordSig_iff
  callArgTy)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (varIndex_lt)
open CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem (JazzAsmAgrees)
open CatCrypt.Crypto.Jasmin.CoqSemMirror (Value Vm Estate OpSem AsmSem GlobDecls Prog Sem
  SemIr SemCall FunName JResult truncateVal evalAtype MemModel semPexpr writeLval writeLvals
  getFunDef)

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## 1. Agreement of calls -/

/-- The mirror values `vs` hold the tuple `a`, position by position. -/
def JazzValsAgrees : {ts : List JasminTy} → HVector (fun t => ⟦t⟧) ts → List Value → Prop
  | [], .nil, [] => True
  | t :: _, .cons a r, v :: vs => JazzValAgrees t a v ∧ JazzValsAgrees r vs
  | _, _, _ => False

variable (SyscallState Mem) in
/-- **Agreement of the callees.** For every symbol `f` whose callee in `E` at a signature of
words and word arrays (`wordSig`) returns `r` on the arguments `a`, the function `f` of the
mirror program `prog` runs, from every syscall state and memory, on mirror values that hold
`a` to the same syscall state and memory and to results that hold `r`. -/
def JazzCallsAgree (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (E : CallEnv jasminDialect) : Prop :=
  ∀ (f : String) (as rs : List JasminTy), wordSig as rs = true →
    ∀ (a : Ctxt.Valuation (d := jasminDialect) as) (r : Ctxt.Valuation (d := jasminDialect) rs),
      E.call f as rs a = some r →
    ∀ (vargs : List Value), JazzValsAgrees a vargs →
    ∀ (scs : SyscallState) (m : Mem), ∃ vres : List Value,
      SemCall aS opS gd prog scs m ⟨f⟩ vargs scs m vres ∧ JazzValsAgrees r vres

/-- No callee is asked of a mirror program in the environment in which every call refuses. -/
theorem jazzCallsAgree_empty (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) :
    JazzCallsAgree SyscallState Mem aS opS gd prog CallEnv.empty :=
  fun _ _ _ _ _ _ h => by cases h

/-- An argument type of a call has a register width of x86. -/
theorem tyOkB_of_callArgTy {t : JasminTy} (h : callArgTy t = true) : tyOkB t = true := by
  cases t <;> simp_all [callArgTy, tyOkB, widthOkB, bitOkB]

section Reads
variable (opS : OpSem) (gd : GlobDecls)

/-- The reads of variables that hold a tuple of types of `tyOkB` evaluate to the values of
the variables, and these hold the tuple. -/
theorem semPexprs_res {s : Estate SyscallState Mem} :
    ∀ {cs : List JasminTy} {xs : List JVar} {a : HVector (fun t => ⟦t⟧) cs},
      cs.all tyOkB = true → JazzResAgrees xs a s →
      CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprs (Mem := Mem) true gd opS s
          (xs.map fun v => mpv (mvi v)) = .ok (xs.map fun x => s.evm (mvar x)) ∧
        JazzValsAgrees a (xs.map fun x => s.evm (mvar x))
  | [], [], .nil, _, _ => ⟨semPexprs_nil opS gd s, trivial⟩
  | t :: cs, x :: xs, .cons a r, hok, h => by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      obtain ⟨hd, -⟩ := valAgrees_typed hok.1 h.1.2 h.1.1
      obtain ⟨ih1, ih2⟩ := semPexprs_res hok.2 h.2
      exact ⟨semPexprs_cons opS gd (semPexpr_mpv opS gd rfl hd) ih1, h.1.2, ih2⟩
  | [], _ :: _, .nil, _, h => h.elim
  | _ :: _, [], .cons _ _, _, h => h.elim

end Reads

omit [MemModel Mem] in
/-- The variables that hold a tuple of types of `tyOkB` translate. -/
theorem resAgrees_okV {s : Estate SyscallState Mem} :
    ∀ {cs : List JasminTy} {xs : List JVar} {a : HVector (fun t => ⟦t⟧) cs},
      cs.all tyOkB = true → JazzResAgrees xs a s → ∀ v ∈ xs, OkV v
  | [], [], .nil, _, _ => by simp
  | t :: cs, x :: xs, .cons a r, hok, h => by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · rw [OkV, h.1.1]; exact styOf_ne_U512 hok.1
      · exact resAgrees_okV hok.2 h.2 v hv
  | [], _ :: _, .nil, _, h => h.elim
  | _ :: _, [], .cons _ _, _, h => h.elim

/-! ## 2. The call arm of the region simulation -/

section Sim
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
  (E : CallEnv jasminDialect) (fuel : Nat)

/-- **A call simulates its callee and then its continuation**, when the callees of the
mirror program agree with `E` (`JazzCallsAgree`). -/
theorem sim_call (hE : JazzCallsAgree SyscallState Mem aS opS gd prog E)
    {Γ : Ctxt jasminDialect} {as rs ts : List JasminTy} (f : String)
    (args : HVector (fun t => Ctxt.Var Γ t) as) (k : NFProg jasminDialect (rs ++ Γ) ts)
    (ihk : Sim SyscallState Mem aS opS gd prog E fuel k) :
    Sim SyscallState Mem aS opS gd prog E fuel (NFProg.call f args k) := by
  intro loc env d n out hlin hout c' hc V r hden hidx s hs
  simp only [linGo] at hlin
  simp only [nfToJasminBody] at hout
  split at hout
  case isFalse => cases hout
  rename_i hws
  simp only [Option.map_eq_some_iff] at hout
  obtain ⟨rk, hrk, rfl⟩ := hout
  obtain ⟨hargTy, t, rfl⟩ : (∀ t ∈ as, callArgTy t = true) ∧ ∃ t, rs = [t] := by
    obtain ⟨h1, h2⟩ := wordSig_iff.1 hws
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | ⟨m, h2⟩ <;> exact ⟨_, h2⟩
  have htok : tyOkB t = true := by
    obtain ⟨-, h2⟩ := wordSig_iff.1 hws
    rcases h2 with h2 | ⟨m, h2⟩ <;> (simp only [List.cons.injEq, and_true] at h2; subst h2; rfl)
  have hasok : as.all tyOkB = true :=
    List.all_eq_true.2 fun t ht => tyOkB_of_callArgTy (hargTy t ht)
  -- the arguments
  have hl : ∀ i ∈ hvIdxs args, usesIdx (NFProg.call f args k) i = true := fun i hi => by
    simp [usesIdx, hi]
  have hxs := resAgrees_ret hs args hl
  obtain ⟨hsemArgs, hvargs⟩ := semPexprs_res opS gd hasok hxs
  have hxok : ∀ v ∈ resolveHV env args, OkV v := resAgrees_okV hasok hxs
  -- the result variable
  have hbv : blockVars d [t] = [mkV 'r' d (styOf t)] := by simp [blockVars_cons]
  have hyok : OkV (mkV 'r' d (styOf t)) := styOf_ne_U512 htok
  -- the translation
  obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv
    (a := [CatCrypt.Crypto.Jasmin.InstrR.Ccall .DoNotInline ((blockVars d [t]).map lvv) ⟨f⟩
      ((resolveHV env args).map pv)]) hc
  obtain ⟨i', c0, hi', hc0, rfl⟩ := translateCmdExt_cons_inv ha'
  simp only [translateCmdExt, Option.some.injEq] at hc0
  subst hc0
  rw [hbv] at hi'
  simp only [translateInstrRExt, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
    translateLValExt_lvv (translateVarIExt_mvi hyok), mapM_pv_mvi hxok] at hi'
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hi'
  subst hi'
  -- the denotation
  have hden' : (E.call f as [t] (Expr.lookupArgs args V) >>= fun r0 =>
      k.denoteAt E fuel (MultiBlockLowering.hvAppend r0 V)) = some r := hden
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hden'
  obtain ⟨r0, hcall, hkden⟩ := hden'
  obtain ⟨vres, hsc, hvres⟩ := hE f as [t] hws _ r0 hcall _ hvargs s.escs s.emem
  obtain ⟨x, hx0⟩ : ∃ x, r0 = .cons x .nil := by
    cases r0 with
    | cons x r1 => cases r1; exact ⟨x, rfl⟩
  subst hx0
  obtain ⟨w, rfl, hw⟩ : ∃ w, vres = [w] ∧ JazzValAgrees t x w := by
    match vres, hvres with
    | [], h => exact h.elim
    | [w], h => exact ⟨w, rfl, h.1⟩
    | _ :: _ :: _, h => exact h.2.elim
  obtain ⟨hdef, hty⟩ := valAgrees_typed htok hw (x := mkV 'r' d (styOf t)) rfl
  -- the call step
  have hwr : writeLvals (Mem := Mem) true gd opS { s with emem := s.emem, escs := s.escs }
      [.Lvar (mvi (mkV 'r' d (styOf t)))] [w] =
      .ok (s.withVm (s.evm.set (mvar (mkV 'r' d (styOf t))) w)) := by
    simp only [writeLvals, CatCrypt.Crypto.Jasmin.CoqSemMirror.JResult.fold2]
    rw [writeLval_lvar opS gd hdef hty]
    rfl
  have hstep : SemIr aS opS gd prog s (.Ccall [.Lvar (mvi (mkV 'r' d (styOf t)))] ⟨f⟩
      ((resolveHV env args).map fun v => mpv (mvi v)))
      (s.withVm (s.evm.set (mvar (mkV 'r' d (styOf t))) w)) :=
    .Ecall _ _ _ _ _ s.escs s.emem _ [w] hsemArgs hsc hwr
  -- the continuation
  have hres2 : JazzResAgrees (blockVars d [t]) (HVector.cons x .nil)
      (s.withVm (s.evm.set (mvar (mkV 'r' d (styOf t))) w)) := by
    rw [hbv]
    refine ⟨⟨rfl, ?_⟩, trivial⟩
    show JazzValAgrees t x ((s.evm.set (mvar (mkV 'r' d (styOf t))) w) (mvar (mkV 'r' d (styOf t))))
    rw [set_same]
    exact hw
  have hs2 : JazzStoreAgrees env d (fun i => usesIdx (NFProg.call f args k) i = true) V
      (s.withVm (s.evm.set (mvar (mkV 'r' d (styOf t))) w)) :=
    storeAgrees_frame hs (fun _ h => h) (fun i hi => set_ne w ((hs.below i hi).ne_new _))
      (arrTyped_set hs.arrTyped hdef hty)
  have hsk := storeAgrees_block hs2 hres2 (L' := fun i => usesIdx k i = true) fun i hi hle => by
    simp only [usesIdx, Bool.or_eq_true]
    exact Or.inr (by rw [Nat.sub_add_cancel hle]; exact hi)
  obtain ⟨s3, hsem3, hpost⟩ := ihk hlin hrk hb' hkden (hidx _ hcall) hsk
  refine ⟨s3, sem_cons aS opS gd prog hstep hsem3, ⟨hpost.res, hpost.resBelow, hpost.scs,
    hpost.mem, fun z hz => ?_, hpost.arr⟩⟩
  rw [hpost.frame z fun h => hz (writes_of_block h le_rfl)]
  exact set_ne w fun he => hz (Or.inr (Or.inl ⟨d, styOf t, le_rfl, he⟩))

/-- **Region simulation with frames and calls.** Every region that `widthsGo` accepts
simulates its denotation (`Sim`) when the callees of the mirror program agree with `E`: its
bindings, counted loops, branches, exit-flag loops and calls. -/
theorem nfToJasminRegion_sim_calls (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS)
    (hE : JazzCallsAgree SyscallState Mem aS opS gd prog E) :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts),
      widthsGo p = true → Sim SyscallState Mem aS opS gd prog E fuel p := by
  intro Γ ts p
  induction p with
  | ret vs => intro _; exact sim_ret aS opS gd prog E fuel vs
  | @var Γ t ts e k ih =>
      intro hw
      simp only [widthsGo, Bool.and_eq_true] at hw
      obtain ⟨⟨ht, hok⟩, hwk⟩ := hw
      exact sim_var aS opS gd prog E fuel haS hop e k ht hok (ih hwk)
  | forLoop count inits body k ihb ihk =>
      intro hw
      simp only [widthsGo, Bool.and_eq_true] at hw
      exact sim_for aS opS gd prog E fuel hop count inits body k hw.1.1 (ihb hw.1.2) (ihk hw.2)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro hw
      simp only [widthsGo, Bool.and_eq_true] at hw
      exact sim_if aS opS gd prog E fuel hop cond thn els k hw.1.1.1
        (iht hw.1.1.2) (ihe hw.1.2) (ihk hw.2)
  | whileLoop inits body k ihb ihk =>
      intro hw
      simp only [widthsGo, Bool.and_eq_true] at hw
      exact sim_while aS opS gd prog E fuel hop inits body k hw.1.1 (ihb hw.1.2) (ihk hw.2)
  | call f args k ih =>
      intro hw
      simp only [widthsGo, Bool.and_eq_true] at hw
      exact sim_call aS opS gd prog E fuel hE f args k (ih hw.2)

end Sim

/-! ## 3. Parameters -/

/-- A variable a program reads is a variable of its context. -/
theorem usesIdx_lt : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) {i : Nat}, usesIdx p i = true → i < Γ.length := by
  have hv : ∀ {Γ : Ctxt jasminDialect} {as : List JasminTy}
      (vs : HVector (fun t => Ctxt.Var Γ t) as) {i : Nat}, i ∈ hvIdxs vs → i < Γ.length := by
    intro Γ as vs i hi
    induction vs with
    | nil => simp [hvIdxs] at hi
    | cons v vs ih =>
        rcases List.mem_cons.1 hi with rfl | hi
        · exact varIndex_lt v
        · exact ih hi
  intro Γ ts p
  induction p with
  | ret vs => intro i h; simp only [usesIdx, List.contains_iff_mem] at h; exact hv vs h
  | var e k ih =>
      intro i h
      simp only [usesIdx, Bool.or_eq_true, List.contains_iff_mem] at h
      rcases h with h | h
      · exact hv _ h
      · have := ih h; simp at this; omega
  | forLoop count inits body k ihb ihk =>
      intro i h
      simp only [usesIdx, Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq] at h
      rcases h with ((h | h) | h) | h
      · exact h ▸ varIndex_lt count
      · exact hv _ h
      · have := ihb h; simp at this; omega
      · have := ihk h; simp at this; omega
  | ifThenElse cond thn els k iht ihe ihk =>
      intro i h
      simp only [usesIdx, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((h | h) | h) | h
      · exact h ▸ varIndex_lt cond
      · exact iht h
      · exact ihe h
      · have := ihk h; simp at this; omega
  | whileLoop inits body k ihb ihk =>
      intro i h
      simp only [usesIdx, Bool.or_eq_true, List.contains_iff_mem] at h
      rcases h with (h | h) | h
      · exact hv _ h
      · have := ihb h; simp at this; omega
      · have := ihk h; simp at this; omega
  | call f args k ih =>
      intro i h
      simp only [usesIdx, Bool.or_eq_true, List.contains_iff_mem] at h
      rcases h with h | h
      · exact hv _ h
      · have := ih h; simp at this; omega

/-- A mirror value of a defined value of the mirror type of `x`. -/
def TypedFor (x : JVar) (v : Value) : Prop :=
  v.isDefined = true ∧ v.typeOf = evalAtype (mvar x).vtype

/-- Values that hold a tuple of types of `tyOkB` are defined and of the mirror types of
variables of these types. -/
theorem valsAgrees_typed :
    ∀ {cs : List JasminTy} {xs : List JVar} {a : HVector (fun t => ⟦t⟧) cs} {vs : List Value},
      cs.all tyOkB = true → JazzValsAgrees a vs →
      List.Forall₂ (fun x t => x.vtype = styOf t) xs cs → List.Forall₂ TypedFor xs vs
  | [], [], .nil, [], _, _, _ => .nil
  | t :: cs, x :: xs, .cons a r, v :: vs, hok, h, .cons hx hxs => by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      exact .cons (valAgrees_typed hok.1 h.1 hx) (valsAgrees_typed hok.2 h.2 hxs)
  | [], _ :: _, .nil, _, _, _, h => by cases h
  | _ :: _, [], .cons _ _, _, _, _, h => by cases h
  | [], [], .nil, _ :: _, _, h, _ => h.elim
  | _ :: _, _ :: _, .cons _ _, [], _, h, _ => h.elim

omit [MemModel Mem] in
/-- Variables of the types of a tuple that hold values that hold the tuple hold the
tuple. -/
theorem resAgrees_of_vals {s : Estate SyscallState Mem} :
    ∀ {cs : List JasminTy} {xs : List JVar} {a : HVector (fun t => ⟦t⟧) cs} {vs : List Value},
      JazzValsAgrees a vs → List.Forall₂ (fun x t => x.vtype = styOf t) xs cs →
      List.Forall₂ (fun x v => s.evm (mvar x) = v) xs vs → JazzResAgrees xs a s
  | [], [], .nil, [], _, _, _ => trivial
  | t :: cs, x :: xs, .cons a r, v :: vs, h, .cons hx hxs, .cons hv hvs =>
      ⟨⟨hx, hv ▸ h.1⟩, resAgrees_of_vals h.2 hxs hvs⟩
  | [], _ :: _, .nil, _, _, h, _ => by cases h
  | _ :: _, [], .cons _ _, _, _, h, _ => by cases h
  | [], [], .nil, _ :: _, h, _, _ => h.elim
  | _ :: _, _ :: _, .cons _ _, [], h, _, _ => h.elim

section Write
variable (opS : OpSem) (gd : GlobDecls)

include opS gd in
/-- **Parameter binding.** Binding variables of distinct names to defined values of their
types succeeds, keeps the syscall state and the memory, binds each variable to its value,
keeps every variable of another name, and keeps arrays at their sizes. -/
theorem writeVars_typed : ∀ {xs : List JVar} {vs : List Value} (s : Estate SyscallState Mem),
    (xs.map fun x => x.vname).Nodup → List.Forall₂ TypedFor xs vs →
    ∃ s', CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVars (Mem := Mem) true (xs.map mvi) vs s =
        .ok s' ∧ s'.escs = s.escs ∧ s'.emem = s.emem ∧
      List.Forall₂ (fun x v => s'.evm (mvar x) = v) xs vs ∧
      (∀ z : MVar, (∀ x ∈ xs, z.vname ≠ x.vname) → s'.evm z = s.evm z) ∧
      (VmArrTyped s.evm → VmArrTyped s'.evm)
  | [], [], s, _, _ => ⟨s, rfl, rfl, rfl, .nil, fun _ _ => rfl, id⟩
  | x :: xs, v :: vs, s, hnd, .cons hx hxs => by
      rw [List.map_cons, List.nodup_cons] at hnd
      have hw : CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar (Mem := Mem) true (mvi x) v s =
          .ok (s.withVm (s.evm.set (mvar x) v)) := by
        have := writeLval_lvar (s := s) (x := mvi x) opS gd hx.1 hx.2
        exact this
      obtain ⟨s', hs', hscs, hmem, hag, hfr, harr⟩ :=
        writeVars_typed (xs := xs) (vs := vs) (s.withVm (s.evm.set (mvar x) v)) hnd.2 hxs
      refine ⟨s', ?_, hscs, hmem, .cons ?_ hag, fun z hz => ?_, fun h => harr ?_⟩
      · show (do
          let s1 ← CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar (Mem := Mem) true (mvi x) v s
          CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVars (Mem := Mem) true (xs.map mvi) vs s1) = _
        rw [hw]
        exact hs'
      · rw [hfr _ fun y hy he => hnd.1 (List.mem_map.2 ⟨y, hy, he ▸ rfl⟩)]
        exact set_same _ _ _
      · rw [hfr z fun y hy => hz y (List.mem_cons_of_mem _ hy)]
        exact set_ne v (hz x List.mem_cons_self)
      · exact arrTyped_set h hx.1 hx.2
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

end Write

/-- Every defined value of the initial variable map has the type of its variable. -/
theorem wT_init : JasminSpill.WT Vm.init := by
  intro v hv
  obtain ⟨vt, vn⟩ := v
  cases vt with
  | aword ws =>
      cases ws <;> simp_all [Vm.init, CatCrypt.Crypto.Jasmin.CoqSemMirror.undefAddr,
        CatCrypt.Crypto.Jasmin.CoqSemMirror.Value.typeOf,
        CatCrypt.Crypto.Jasmin.CoqSemMirror.Value.isDefined,
        CatCrypt.Crypto.Jasmin.CoqSemMirror.Ctype.isUndefT]
  | _ => simp_all [Vm.init, CatCrypt.Crypto.Jasmin.CoqSemMirror.undefAddr,
        CatCrypt.Crypto.Jasmin.CoqSemMirror.Value.typeOf,
        CatCrypt.Crypto.Jasmin.CoqSemMirror.Value.isDefined,
        CatCrypt.Crypto.Jasmin.CoqSemMirror.Ctype.isUndefT, evalAtype]

omit [MemModel Mem] in
/-- Binding variables keeps every defined value at the type of its variable. -/
theorem writeVars_WT : ∀ (xs : List MVarI) (vs : List Value) (s s' : Estate SyscallState Mem),
    CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVars true xs vs s = .ok s' →
    JasminSpill.WT s.evm → JasminSpill.WT s'.evm
  | [], [], s, s', h, hw => by
      simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVars, JResult.fold2] at h
      cases h; exact hw
  | x :: xs, v :: vs, s, s', h, hw => by
      simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVars, JResult.fold2] at h
      cases h1 : CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar true x v s with
      | ok s1 =>
          rw [h1] at h
          obtain ⟨rfl, ht, -, -⟩ := JasminSpill.writeVar_ok h1
          exact writeVars_WT xs vs _ s' h (hw.set ht)
      | _ => simp [h1] at h
  | [], _ :: _, s, s', h, _ => by
      simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVars, JResult.fold2] at h
  | _ :: _, [], s, s', h, _ => by
      simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVars, JResult.fold2] at h

/-- A variable of the lowering is not a fresh variable of the spill pass. -/
theorem isFreshName_mkV (c : Char) (hc : c ≠ 's') (k : Nat) (s : CatCrypt.Crypto.Jasmin.SType) :
    JasminSpill.isFreshName (mkV c k s).vname = false := by
  simp [JasminSpill.isFreshName, JasminSpill.pfx, mkV, nameOf, String.toList_append,
    List.isPrefixOf, hc.symm]

/-- Truncating defined values at their own types is the identity. -/
theorem truncate_typed : ∀ {xs : List JVar} {vs : List Value}, List.Forall₂ TypedFor xs vs →
    JResult.mapM (fun p : CatCrypt.Crypto.Jasmin.CoqSemMirror.Atype × Value =>
        truncateVal (evalAtype p.fst) p.snd)
      (((xs.map mvi).map fun x : CatCrypt.Crypto.Jasmin.CoqSemMirror.VarI => x.v_var.vtype).zip
        vs) = .ok vs
  | [], [], .nil => rfl
  | x :: xs, v :: vs, .cons hx hxs => by
      show (do
        let b ← truncateVal (evalAtype (mvar x).vtype) v
        let bs ← JResult.mapM (fun p : CatCrypt.Crypto.Jasmin.CoqSemMirror.Atype × Value =>
          truncateVal (evalAtype p.fst) p.snd)
          (((xs.map mvi).map fun x : CatCrypt.Crypto.Jasmin.CoqSemMirror.VarI =>
            x.v_var.vtype).zip vs)
        (.ok (b :: bs) : JResult (List Value))) = _
      rw [← hx.2, truncateVal_typeOf hx.1, truncate_typed hxs]
      rfl

/-- The initial variable map holds arrays of their sizes. -/
theorem vmArrTyped_init : VmArrTyped Vm.init := by
  intro y ws n hy
  refine ⟨CatCrypt.Crypto.Jasmin.CoqSemMirror.JArrayMirror.empty n, ?_⟩
  simp [Vm.init, hy, CatCrypt.Crypto.Jasmin.CoqSemMirror.undefAddr, Value.typeOf]

/-- **Agreement of the arguments.** The mirror values `vargs`, in parameter order, hold the
valuation `V` of the context, whose innermost variable is the last parameter. -/
def JazzArgsAgree {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (vargs : List Value) :
    Prop :=
  JazzValsAgrees V vargs.reverse

/-- The parameter variables of a signature. -/
def paramVars {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) : List JVar :=
  (paramPairs sig).map Prod.fst

/-- The parameter variables of a signature, position by position. -/
theorem paramVars_eq {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) :
    paramVars sig = (List.range Γ.length).map fun j =>
      mkV 'a' j ((sig.params[j]?).getD ("", .reg, .word .U64)).2.2.toSType := by
  simp [paramVars, paramPairs, sig.params_length]

/-- The parameter variables have distinct names. -/
theorem nodup_paramVars {Γ : Ctxt jasminDialect} {t : JasminTy} (sig : JazzSig Γ t) :
    ((paramVars sig).map fun x => x.vname).Nodup := by
  rw [paramVars_eq, List.map_map]
  refine (List.nodup_range).map_on fun i _ j _ h => ?_
  exact (nameOf_inj h).2.1

/-- A parameter variable is an argument. -/
theorem mem_paramVars {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t} {x : JVar}
    (h : x ∈ paramVars sig) : ∃ k s, x = mkV 'a' k s := by
  rw [paramVars_eq] at h
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
  exact ⟨_, _, rfl⟩

/-- The parameter variables of a signature that fits have the types of the context, in
argument order. -/
theorem paramVars_types {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t}
    (hf : sig.Fits) :
    List.Forall₂ (fun x t => x.vtype = styOf t) (paramVars sig) Γ.reverse := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [paramVars_eq], fun j h1 h2 => ?_⟩
  simp only [List.get_eq_getElem]
  have hj : j < sig.params.length := by rw [sig.params_length]; simpa using h2
  simp only [paramVars_eq, List.getElem_map, List.getElem_range, mkV]
  rw [List.getElem?_eq_getElem hj, Option.getD_some]
  exact hf.1 (sig.params[j], Γ.reverse[j]) (List.mem_iff_getElem.2
    ⟨j, by rw [List.length_zip]; omega, by simp⟩)

/-- The unit of one function translates to the program of the translation of that
function. -/
theorem translateUnit_mkUnit_map (fn : CatCrypt.Crypto.Jasmin.Jazz.JazzFn) :
    translateUnit (mkUnit fn) =
      (translateFn fn).map fun fd => { pFuncs := [fd], pGlobs := [] } := by
  cases h : translateFn fn with
  | none => simp [translateUnit, mkUnit, h]
  | some fd => exact translateUnit_mkUnit fn fd h

/-- Variables of types of `tyOkB` translate. -/
theorem forall₂_okV : ∀ {xs : List JVar} {cs : List JasminTy},
    List.Forall₂ (fun x t => x.vtype = styOf t) xs cs → cs.all tyOkB = true → ∀ y ∈ xs, OkV y
  | [], [], .nil, _ => by simp
  | x :: xs, t :: cs, .cons hx hxs, hok => by
      simp only [List.all_cons, Bool.and_eq_true] at hok
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [OkV, hx]; exact styOf_ne_U512 hok.1
      · exact forall₂_okV hxs hok.2 y hy

/-- The parameters of the function of a lowering translate to the mirror variables of the
parameter variables. -/
theorem mapM_params {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t}
    (h : ∀ y ∈ paramVars sig, OkV y) :
    ((paramPairs sig).map fun q => (⟨⟨q.1, vi0⟩⟩ : CatCrypt.Crypto.Jasmin.FunParam)).mapM
      (fun q => translateVarIExt q.var) = some ((paramVars sig).map mvi) := by
  have key : ∀ xs : List JVar, (∀ y ∈ xs, OkV y) →
      (xs.map fun x => (⟨⟨x, vi0⟩⟩ : CatCrypt.Crypto.Jasmin.FunParam)).mapM
        (fun q => translateVarIExt q.var) = some (xs.map mvi) := by
    intro xs hxs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map_cons, List.mapM_cons,
          translateVarIExt_mvi (hxs x List.mem_cons_self),
          ih fun y hy => hxs y (List.mem_cons_of_mem _ hy)]
        rfl
  have := key (paramVars sig) h
  simp only [paramVars, List.map_map] at this ⊢
  exact this

omit [MemModel Mem] in
/-- **Store agreement at entry.** The state after binding the parameter variables of a
signature that fits to arguments that agree with `V` agrees with `V` on the variables a
program over the context reads, in the environment of the parameters. -/
theorem storeAgrees_params {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t}
    (hf : sig.Fits) {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    {V : Ctxt.Valuation Γ} {vargs : List Value} (hargs : JazzArgsAgree V vargs)
    {s : Estate SyscallState Mem}
    (hval : List.Forall₂ (fun x v => s.evm (mvar x) = v) (paramVars sig) vargs)
    (harr : VmArrTyped s.evm) :
    JazzStoreAgrees (paramVars sig).reverse Γ.length (fun i => usesIdx p i = true) V s := by
  have hty : List.Forall₂ (fun x t => x.vtype = styOf t) (paramVars sig).reverse Γ := by
    simpa using List.forall₂_reverse_iff.2 (paramVars_types hf)
  have hres : JazzResAgrees (paramVars sig).reverse V s :=
    resAgrees_of_vals hargs hty (List.forall₂_reverse_iff.2 hval)
  have hlen : (paramVars sig).reverse.length = Γ.length := by simp [paramVars_eq]
  have hmem : ∀ i, usesIdx p i = true →
      (paramVars sig).reverse.getD i dfltV ∈ (paramVars sig).reverse := fun i hi => by
    have := usesIdx_lt p hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  refine ⟨fun v _ => resAgrees_lookup hres v, fun i hi => ?_, fun i j hi hj he => ?_, harr⟩
  · obtain ⟨k, s0, he⟩ := mem_paramVars (List.mem_reverse.1 (hmem i hi))
    exact Or.inl ⟨k, s0, he⟩
  · have hi' := usesIdx_lt p hi
    have hj' := usesIdx_lt p hj
    have hlen' : (paramVars sig).length = Γ.length := by simp [paramVars_eq]
    have hnd : ((paramVars sig).reverse.map fun x => x.vname).Nodup := by
      rw [List.map_reverse]; exact List.nodup_reverse.2 (nodup_paramVars sig)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at he
    exact (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := by simp; omega)
      (hj := by simp; omega)).1 (by simpa using he)

/-! ## 4. The function -/

section Fn
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)

/-- **The function of the lowering runs in the mirror.** Let `nfToJasmin` return the unit
`u` on the program `p` under the signature `sig`, let `u` translate to the mirror program
`prog`, and let `P` be a mirror program that defines `fname` as `prog` does and whose
callees agree with `E` (`JazzCallsAgree`). When `p` denotes `x` at `V` in `E`, with its
array indices in range, the function `fname` of `P` runs, from every syscall state and
memory and from arguments that agree with `V`, to the same syscall state and memory and to
one result that holds `x` (`JazzValAgrees`: a word for a register result, a byte array whose
little-endian words are the elements of `x` for an array result returned through its
`reg mut ptr` parameter). -/
theorem nfToJasmin_sem (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t}
    {fname : String} {p : NFProg jasminDialect Γ [t]}
    {u : CatCrypt.Crypto.Jasmin.Jazz.JazzUnit} (hu : nfToJasmin sig fname p = some u) {prog : Prog}
    (hprog : translateUnit u = some prog)
    {P : Prog} (hP : getFunDef P ⟨fname⟩ = getFunDef prog ⟨fname⟩)
    {E : CallEnv jasminDialect} (hE : JazzCallsAgree SyscallState Mem aS opS gd P E)
    {fuel : Nat} {V : Ctxt.Valuation Γ} {x : ⟦t⟧}
    (hden : p.denoteAt E fuel V = some (.cons x .nil)) (hidx : IdxInBounds E fuel p V)
    (scs : SyscallState) (m : Mem) {vargs : List Value} (hargs : JazzArgsAgree V vargs) :
    ∃ v, SemCall aS opS gd P scs m ⟨fname⟩ vargs scs m [v] ∧ JazzValAgrees t x v := by
  -- the checks of the lowering
  unfold nfToJasmin at hu
  split at hu
  case isFalse => cases hu
  rename_i hck
  simp only [Bool.and_eq_true] at hck
  obtain ⟨⟨hfit, hlin⟩, hwid⟩ := hck
  have hwB := hwid
  have hf := (JazzSig.fitsB_iff sig).1 hfit
  simp only [jasminWidthsB, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true]
    at hwid
  obtain ⟨⟨hΓ, htok⟩, hwg⟩ := hwid
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hu
  -- the arguments
  have hargTy : List.Forall₂ TypedFor (paramVars sig) vargs := by
    have := valsAgrees_typed hΓ hargs
      (by simpa using List.forall₂_reverse_iff.2 (paramVars_types hf))
    simpa using List.forall₂_reverse_iff.2 this
  obtain ⟨s1, hw1, hscs1, hmem1, hval1, -, harr1⟩ := writeVars_typed opS gd
    (⟨scs, m, Vm.init⟩ : Estate SyscallState Mem) (nodup_paramVars sig) hargTy
  have hs1 := storeAgrees_params hf p hargs hval1 (harr1 vmArrTyped_init)
  have hpok : ∀ y ∈ paramVars sig, OkV y :=
    forall₂_okV (paramVars_types hf) (by simpa using hΓ)
  -- the result variable `rr` and the move of the result of the body to it
  obtain ⟨rr, tail, rtys, hfin, hrrok, hrrty, hfresh, htail⟩ :
      ∃ (rr : JVar) (tail : CatCrypt.Crypto.Jasmin.Cmd)
        (rtys : List (CatCrypt.Crypto.Jasmin.Jazz.Storage × CatCrypt.Crypto.Jasmin.Jazz.PType)),
        finish sig fname r = mkFn fname (paramPairs sig) (r.code ++ tail) [rr] rtys ∧
        OkV rr ∧ rr.vtype = styOf t ∧ JasminSpill.isFreshName rr.vname = false ∧
        ∀ (rv : JVar), r.res.headD dfltV = rv → OkV rv → ∀ (s2 : Estate SyscallState Mem),
          (s2.evm (mvar rv)).isDefined = true →
          (s2.evm (mvar rv)).typeOf = evalAtype (mvar rr).vtype →
          ∀ b', translateCmdExt tail = some b' →
          ∃ s3 : Estate SyscallState Mem, Sem aS opS gd P s2 (typeC b') s3 ∧
            s3.evm (mvar rr) = s2.evm (mvar rv) ∧ s3.escs = s2.escs ∧ s3.emem = s2.emem := by
    have hres := hf.2
    cases hrp : sig.resultParam with
    | none =>
        rw [hrp] at hres
        obtain ⟨-, hrty⟩ := hres
        have hrrty : (mkV 'r' r.depth sig.result.2.toSType).vtype = styOf t := hrty
        have hrrok : OkV (mkV 'r' r.depth sig.result.2.toSType) := by
          rw [OkV, hrrty]; exact styOf_ne_U512 htok
        refine ⟨mkV 'r' r.depth sig.result.2.toSType,
          [asgn (mkV 'r' r.depth sig.result.2.toSType) (pv (r.res.headD dfltV))], [sig.result],
          by simp only [finish, hrp], hrrok, hrrty, isFreshName_mkV 'r' (by decide) _ _, ?_⟩
        intro rv hrv hrvok s2 hdef hty b' hb'
        subst hrv
        exact ⟨_, sem_asgn_step aS opS gd P hrrok
          (translatePExprExt_pv (translateVarIExt_mvi hrvok)) hb' (s := s2)
          (semPexpr_mpv opS gd rfl hdef) hdef hty
          (fun c'' hc'' => sem_nil_step aS opS gd P hc'' _), set_same _ _ _, rfl, rfl⟩
    | some j =>
        rw [hrp] at hres
        obtain ⟨q, hq, hqt, -⟩ := hres
        obtain ⟨pj, hpj⟩ : ∃ pj, ((paramPairs sig).map Prod.fst).getD j dfltV = pj := ⟨_, rfl⟩
        have hpjE : pj = mkV 'a' j q.2.2.toSType := by
          subst hpj
          rw [← paramVars, paramVars_eq]
          have hj := (List.getElem?_eq_some_iff.1 hq).1
          rw [sig.params_length] at hj
          simp [List.getD_eq_getElem?_getD, hj, hq]
        have hpjty : pj.vtype = styOf t := by rw [hpjE]; exact hqt
        have hpjok : OkV pj := by rw [OkV, hpjty]; exact styOf_ne_U512 htok
        refine ⟨pj, if pj == r.res.headD dfltV then [] else [asgn pj (pv (r.res.headD dfltV))],
          [(.regPtr true, ((paramPairs sig).map Prod.snd |>.getD j (.reg, .word .U64)).2)],
          by simp only [finish, hrp, hpj], hpjok, hpjty,
          by rw [hpjE]; exact isFreshName_mkV 'a' (by decide) _ _, ?_⟩
        intro rv hrv hrvok s2 hdef hty b' hb'
        subst hrv
        split at hb'
        · rename_i heq
          refine ⟨s2, sem_nil_step aS opS gd P hb' s2, ?_, rfl, rfl⟩
          rw [beq_iff_eq.1 heq]
        · exact ⟨_, sem_asgn_step aS opS gd P hpjok
            (translatePExprExt_pv (translateVarIExt_mvi hrvok)) hb' (s := s2)
            (semPexpr_mpv opS gd rfl hdef) hdef hty
            (fun c'' hc'' => sem_nil_step aS opS gd P hc'' _), set_same _ _ _, rfl, rfl⟩
  -- the function before the spill pass translates
  have hF0 := translateUnit_isSome_mkUnit_finish (fname := fname) hfit hwB hr
  rw [translateUnit_mkUnit_map, Option.isSome_map, hfin] at hF0
  obtain ⟨fd0, hfd0⟩ := Option.isSome_iff_exists.mp hF0
  have hps := mapM_params hpok
  have hrs : [(⟨rr, vi0⟩ : CatCrypt.Crypto.Jasmin.VarI)].mapM
      translateVarIExt = some [mvi rr] := by
    simp [translateVarIExt_mvi hrrok]
  obtain ⟨body', hb⟩ : ∃ body', translateCmdExt (r.code ++ tail) = some body' := by
    cases h : translateCmdExt (r.code ++ tail) with
    | none =>
        simp only [translateFn, mkFn] at hfd0
        rw [hps, h] at hfd0
        cases hfd0
    | some b => exact ⟨b, rfl⟩
  -- the region
  obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv hb
  obtain ⟨s2, hsem2, hpost⟩ := nfToJasminRegion_sim_calls aS opS gd P E fuel haS hop hE p hwg
    hlin hr ha' hden hidx hs1
  have hR := hpost.res
  obtain ⟨rv, hrv⟩ := List.length_eq_one_iff.1 (resAgrees_length hR)
  rw [hrv] at hR
  have hagr : JazzVarAgrees rv t x s2.evm := hR.1
  have hrvok : OkV rv := by rw [OkV, hagr.1]; exact styOf_ne_U512 htok
  obtain ⟨hdef, hty⟩ := valAgrees_typed htok hagr.2 hrrty
  -- the move to the result variable
  obtain ⟨s3, hsemA, hs3r, hs3scs, hs3mem⟩ :=
    htail rv (by rw [hrv]; rfl) hrvok s2 hdef hty b' hb'
  -- the body before the spill pass
  have hbody : Sem aS opS gd P s1 (typeC (a' ++ b')) s3 := by
    rw [typeC_append]; exact ComJasminBridgeProgram.sem_append aS opS gd P hsem2 hsemA
  -- the spill pass
  have hc0 : translateCmdExt (finish sig fname r).fd.body = some (a' ++ b') := by
    rw [hfin]; exact hb
  have hwt : JasminSpill.WT s1.evm := writeVars_WT _ _ _ _ hw1 wT_init
  have hresd : ∀ q ∈ (finish sig fname r).fd.results, ∀ q', translateVarIExt q = some q' →
      (s3.evm q'.v_var).isDefined = true := by
    intro q hq q' hq'
    rw [hfin] at hq
    simp only [mkFn, List.map_cons, List.map_nil, List.mem_singleton] at hq
    subst hq
    rw [translateVarIExt_mvi hrrok, Option.some.injEq] at hq'
    subst hq'
    change (s3.evm (mvar rr)).isDefined = true
    rw [hs3r]; exact hdef
  obtain ⟨c', t', hc', hsem', hmem', hscs', hagr'⟩ :=
    JasminSpill.spillFn_sem aS opS gd P (spillBudget (finish sig fname r)) (finish sig fname r)
      hc0 hbody hwt hresd
  have hpF : ∀ k, (JasminSpill.spillFn k (finish sig fname r)).fd.params =
      (finish sig fname r).fd.params := fun _ => by unfold JasminSpill.spillFn; split <;> rfl
  have hrF : ∀ k, (JasminSpill.spillFn k (finish sig fname r)).fd.results =
      (finish sig fname r).fd.results := fun _ => by unfold JasminSpill.spillFn; split <;> rfl
  have hnF : ∀ k, (JasminSpill.spillFn k (finish sig fname r)).fd.name =
      (finish sig fname r).fd.name := fun _ => by unfold JasminSpill.spillFn; split <;> rfl
  have hfd := translateFn_eq_some _ (by rw [hpF, hfin]; exact hps) hc' (by rw [hrF, hfin]; exact hrs)
  have hprogE : prog = { pFuncs := [({ name := fname },
      { tyin := ((paramVars sig).map mvi).map (·.v_var.vtype), params := (paramVars sig).map mvi,
        body := typeC c',
        tyout := [mvi rr].map (·.v_var.vtype), rets := [mvi rr] })], pGlobs := [] } := by
    have hname : (JasminSpill.spillFn (spillBudget (finish sig fname r))
        (finish sig fname r)).fd.name.name = fname := by
      rw [hnF, hfin]; rfl
    rw [hname] at hfd
    simp only [translateUnit, JasminSpill.spillUnit, mkUnit, List.map_cons, List.map_nil,
      List.mapM_cons, List.mapM_nil, hfd] at hprog
    simpa using hprog.symm
  subst hprogE
  -- the call
  have hget : getFunDef P ⟨fname⟩ = some
      { tyin := ((paramVars sig).map mvi).map (·.v_var.vtype), params := (paramVars sig).map mvi,
        body := typeC c',
        tyout := [mvi rr].map (·.v_var.vtype), rets := [mvi rr] } := by
    rw [hP]
    simp [getFunDef]
  have hrr : t'.evm (mvar rr) = s2.evm (mvar rv) := by
    rw [hagr' _ hfresh]
    exact hs3r
  have hgetv : CatCrypt.Crypto.Jasmin.CoqSemMirror.getVarIs true t'.evm
      [mvi rr] = .ok [s2.evm (mvar rv)] := by
    simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.getVarIs, JResult.mapM,
      CatCrypt.Crypto.Jasmin.CoqSemMirror.getVar, Vm.get, mvi, hrr, hdef]
  have hcall := SemCall.EcallRun (aS := aS) (opS := opS) (gd := gd) (prog := P) scs m ⟨fname⟩ _
    vargs vargs { escs := scs, emem := m, evm := Vm.init } s1 t'
    _ _ hget (truncate_typed hargTy) rfl hw1 hsem'
    hgetv (truncate_typed (xs := [rr]) (.cons ⟨hdef, hty⟩ .nil))
  have e1 : t'.escs = scs := hscs'.trans (hs3scs.trans (hpost.scs.trans hscs1))
  have e2 : t'.emem = m := hmem'.trans (hs3mem.trans (hpost.mem.trans hmem1))
  rw [e1, e2] at hcall
  exact ⟨_, hcall, hagr.2⟩

end Fn

end CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSemFn
