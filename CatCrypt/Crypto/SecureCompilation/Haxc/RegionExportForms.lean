/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete

@[expose] public section

set_option autoImplicit false

/-!
# The instruction forms of a region export

The region export `exportR` builds its code from a fixed set of instructions: the binding
instruction `bindOps` of each binding, register moves `movI`, labels `labelI`, the array
moves `arrMove`, the loop advance `advanceOps`, the widening `flagWord` of a bit, the guards
`IsaData.zeroTripGuard` and `IsaData.loopGuard` of the instruction set, and the shadow
instruction `callI` of a call. Every operand it reads from a variable is a register or an
immediate (`resolveVar` at the empty map of immediate slots). This module proves, once for
every predicate on instructions closed under these instructions, that the predicate holds
of every instruction of the export, and instantiates it at x86 with the forms `FormB`: an
`Lopn` with one register destination and plain sources, a register-indexed `LOADIDX` or
`STOREIDX` with its load or store tag, a label, or a conditional jump on the zero flag. The
forms are kept by the result copies of the gate and by the renaming of array positions
`renArr`, and they give five conjuncts of the back half on every export at x86: the class
stage `coClass` of the gate `regionCoB`, and the first four conjuncts of the event check
`regionLeakB`.

The third and fourth conjuncts of `regionLeakB` check the events of the renamed and of the
merged code (`regLeakB`) against the liveness tables `d.live` and `d.liveM` of the parts.
Both tables are computed by the gate (`liveRegTab`), and a computed table holds, before each
operation, the names the operation reads (`RegionAllocMapComplete.liveRegTab_closed`). An
operation of the forms reads its index registers as sources and has no compile-time array
operand, and renaming keeps both facts (`IdxSrc`), so the two conjuncts hold at every merge
and every certificate.

## Main definitions

* `plainOpB`: a register or an immediate operand.
* `ExportClosed`: the closure conditions of a predicate on instructions at an instruction
  set and a number of arguments.
* `FormB`: the forms of the instructions of an export at x86.

## Main results

* `exportR_forall`: a predicate of `ExportClosed` holds of every instruction of an export,
  and every returned operand of the export is plain.
* `opToLinstrR_form`, `bindOps_formB`: the wire of an operation on register sources, and
  the forms of the binding instructions.
* `exportClosed_formB`: the forms are closed under the instructions of the export at x86.
* `formB_renArr`: the forms are kept by `renArr`.
* `formB_regionCoCode`: every instruction of the code with the result copies of an export
  at x86 has the forms.
* `coClass_regionCoCode`, `regionCoStage_ne_coClass`: the class conjunct `clsB ∧ mulxFree`
  of the gate holds on that code, and `regionCoStage` is not `coClass` on the call-free arm.
* `leakFixCfgB_regionCoCode`, `constArrFreeB_regionCoBody`, `regionLeakB_fix_constArr`: the
  first two conjuncts of `regionLeakB` hold on every export at x86.
* `regLeakB_liveRegTab`: code whose index registers are sources and which has no
  compile-time array operand passes `regLeakB` at every merge against its computed liveness
  table.
* `regionLeakB_live`, `regionLeakB_four`: the third and fourth conjuncts, and the first four
  conjuncts, of `regionLeakB` hold on every export at x86.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportForms

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag straightOpsMem loadStruct?
  storeStruct? zeroStruct? storeImmStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData)

/-! ## 1. Plain operands -/

/-- A register or an immediate operand. -/
def plainOpB : LOperand → Bool
  | .reg _ => true
  | .imm _ => true
  | _ => false

/-- A variable resolves to a plain operand at the empty map of immediate slots. -/
theorem resolveVar_plain (d nArgs : Nat) (names : Nat → String) {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    plainOpB (resolveVar d nArgs names (fun _ => none) v) = true := by
  simp only [resolveVar]
  split_ifs <;> rfl

/-- A vector of variables resolves to plain operands at the empty map of immediate
    slots. -/
theorem exprArgsHV_plain (d nArgs : Nat) (names : Nat → String) {Γ : Ctxt jasminDialect} :
    ∀ {tys : Ctxt jasminDialect} (vs : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ exprArgsHV d nArgs names (fun _ => none) vs, plainOpB o = true
  | [], _, o, ho => by simp [exprArgsHV] at ho
  | _ :: _, .cons v rest, o, ho => by
      change o ∈ resolveVar d nArgs names (fun _ => none) v
        :: exprArgsHV d nArgs names (fun _ => none) rest at ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact resolveVar_plain d nArgs names v
      · exact exprArgsHV_plain d nArgs names rest o ho

/-! ## 2. The closure conditions -/

/-- **The closure conditions of a predicate `P` on instructions** at the instruction set
    `I` and `nArgs` arguments: `P` holds of the binding instructions `bindOps`, of a move of
    a plain operand, of every label, of the instructions of an array move, of the loop
    advance, of the widening of a plain operand, of the instructions of both guards of `I`,
    and of the shadow instruction of a call on plain operands. -/
structure ExportClosed (P : LinstrRM → Prop) (nArgs : Nat) (I : IsaData) : Prop where
  /-- The binding instructions. -/
  bind : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) (d : Nat),
    ∀ i ∈ bindOps nArgs e d, P i
  /-- A move of a plain operand. -/
  mov : ∀ (dst : String) (o : LOperand), plainOpB o = true → P (movI dst o)
  /-- A label. -/
  label : ∀ l, P (labelI l)
  /-- The instructions of an array move. -/
  arr : ∀ (z t : String) (a : ArrMove), ∀ i ∈ arrMove z t a, P i
  /-- The loop advance. -/
  adv : ∀ idx ctr : String, ∀ i ∈ advanceOps idx ctr, P i
  /-- The widening of a plain operand. -/
  flag : ∀ (r z : String) (o : LOperand), plainOpB o = true → ∀ i ∈ flagWord I r z o, P i
  /-- The zero-trip guard. -/
  zero : ∀ (ctr : String) (top endL : LLabel), ∀ g ∈ I.zeroTripGuard ctr top endL, P (guardI g)
  /-- The loop guard. -/
  loop : ∀ (ctr : String) (top : LLabel), ∀ g ∈ I.loopGuard ctr top, P (guardI g)
  /-- The shadow instruction of a call on plain operands. -/
  call : ∀ (dst f : String) (srcs : List LOperand), (∀ o ∈ srcs, plainOpB o = true) →
    P (callI dst f srcs)

namespace ExportClosed

variable {P : LinstrRM → Prop} {nArgs : Nat} {I : IsaData}

theorem seedMoves (h : ExportClosed P nArgs I) (car : List String) (ops : List LOperand)
    (hops : ∀ o ∈ ops, plainOpB o = true) : ∀ i ∈ seedMoves car ops, P i := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  exact h.mov _ _ (hops _ (List.of_mem_zip hp).2)

theorem parMoves (h : ExportClosed P nArgs I) (D : Nat) (tgts : List String)
    (ops : List LOperand) (hops : ∀ o ∈ ops, plainOpB o = true) :
    ∀ i ∈ parMoves D tgts ops, P i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hlt, heq⟩ := List.mem_zipIdx' hp
    exact h.mov _ _ (hops _ (heq ▸ List.getElem_mem hlt))
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact h.mov _ _ rfl

theorem arrMoves (h : ExportClosed P nArgs I) (z t : String) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, P i := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  exact h.arr z t a i hi

theorem typedMoves (h : ExportClosed P nArgs I) (z t : String)
    (tp : List (JasminTy × String × String)) : ∀ i ∈ typedMoves z t tp, P i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact h.arrMoves z t _ i hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact h.mov _ _ rfl

theorem arrParMoves (h : ExportClosed P nArgs I) (z t : String) (D : Nat)
    (mv : List ArrMove) : ∀ i ∈ arrParMoves z t D mv, P i := by
  intro i hi
  unfold ExportRegions.arrParMoves at hi
  split at hi
  · exact h.arrMoves z t _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact h.arrMoves z t _ i hi

theorem ifResMoves (h : ExportClosed P nArgs I) (rs : List JasminTy) (d D : Nat)
    (ops : List LOperand) : ∀ i ∈ ifResMoves rs d D ops, P i := by
  intro i hi
  unfold ExportRegions.ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · cases hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact h.mov _ _ rfl
      · exact h.arrParMoves _ _ _ _ i hi
  · refine h.parMoves _ _ _ ?_ i hi
    intro o ho
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
    rfl

theorem guards (h : ExportClosed P nArgs I) (ctr : String) (top endL : LLabel) :
    (∀ i ∈ (I.zeroTripGuard ctr top endL).map guardI, P i) ∧
      ∀ i ∈ (I.loopGuard ctr top).map guardI, P i := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
    exact h.zero ctr top endL g hg
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
    exact h.loop ctr top g hg

theorem forArrFrame (h : ExportClosed P nArgs I) (d n : Nat) (cs : List JasminTy)
    (initOps : List LOperand) (countOp : LOperand) (bodyC : List LinstrRM)
    (bodyOps : List LOperand) (bodyD : Nat) (hc : plainOpB countOp = true)
    (hb : ∀ i ∈ bodyC, P i) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD I, P i := by
  intro i hi
  simp only [ExportRegions.forArrFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with rfl | hi | hi | hi | rfl | hi | rfl | hi | hi | hi | hi | rfl | rfl | hi
  · exact h.mov _ _ rfl
  · exact h.typedMoves _ _ _ i hi
  · refine h.seedMoves _ _ ?_ i hi
    intro o ho
    rw [List.mem_singleton.mp ho]
    exact hc
  · exact (h.guards _ _ _).1 i hi
  · exact h.label _
  · exact hb i hi
  · exact h.mov _ _ rfl
  · exact h.arrParMoves _ _ _ _ i hi
  · refine h.parMoves _ _ _ ?_ i hi
    intro o ho
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
    rfl
  · exact h.adv _ _ i hi
  · exact (h.guards _ _ 0).2 i hi
  · exact h.label _
  · exact h.mov _ _ rfl
  · exact h.typedMoves _ _ _ i hi

theorem whileFrame (h : ExportClosed P nArgs I) (d n nCar : Nat) (initOps : List LOperand)
    (bodyC : List LinstrRM) (flagOp : LOperand) (bodyOps : List LOperand) (bodyD : Nat)
    (hi0 : ∀ o ∈ initOps, plainOpB o = true) (hf : plainOpB flagOp = true)
    (hbo : ∀ o ∈ bodyOps, plainOpB o = true) (hb : ∀ i ∈ bodyC, P i) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD I, P i := by
  intro i hi
  simp only [ExportRegions.whileFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with hi | rfl | hi | hi | hi | hi
  · exact h.seedMoves _ _ hi0 i hi
  · exact h.label _
  · exact hb i hi
  · exact h.flag _ _ _ hf i hi
  · exact h.parMoves _ _ _ hbo i hi
  · exact (h.guards _ _ 0).2 i hi

theorem ifFrame (h : ExportClosed P nArgs I) (fn : String) (d n : Nat) (rs : List JasminTy)
    (condOp : LOperand) (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat)
    (hc : plainOpB condOp = true) (ht : ∀ i ∈ thnC, P i) (he : ∀ i ∈ elsC, P i) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD I, P i := by
  intro i hi
  simp only [ExportRegions.ifFrame, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with hi | hi | rfl | hi | hi | rfl | hi | rfl | hi | hi | rfl
  · exact h.flag _ _ _ hc i hi
  · exact (h.guards _ _ _).1 i hi
  · exact h.label _
  · exact ht i hi
  · exact h.ifResMoves _ _ _ _ i hi
  · exact h.mov _ _ rfl
  · exact (h.guards _ _ 0).2 i hi
  · exact h.label _
  · exact he i hi
  · exact h.ifResMoves _ _ _ _ i hi
  · exact h.label _

end ExportClosed

/-! ## 3. The export -/

/-- **A predicate closed under the instructions of the export holds of every instruction of
    an export**, and every returned operand of an export is plain. -/
theorem exportR_forall {P : LinstrRM → Prop} {nArgs : Nat} {I : IsaData}
    (h : ExportClosed P nArgs I) (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r →
      (∀ i ∈ r.code, P i) ∧ ∀ o ∈ r.res, plainOpB o = true := by
  induction p with
  | ret vs =>
      intro d n r hr
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      exact ⟨fun _ hi => (nomatch hi), exprArgsHV_plain _ _ _ vs⟩
  | var e k ih =>
      intro d n r hr
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk, rfl⟩ := hr
      obtain ⟨hc, hres⟩ := ih _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · exact h.bind e d i hi
      · exact hc i hi
  | forLoop count inits body k ihb ihk =>
      intro d n r hr
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨b, hb, rk, hk, rfl⟩ := hr
      obtain ⟨hbc, -⟩ := ihb _ _ _ hb
      obtain ⟨hkc, hres⟩ := ihk _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · exact h.forArrFrame _ _ _ _ _ _ _ _ (resolveVar_plain _ _ _ _) hbc i hi
      · exact hkc i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r hr
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := hr
      obtain ⟨htc, -⟩ := iht _ _ _ ht
      obtain ⟨hec, -⟩ := ihe _ _ _ he
      obtain ⟨hkc, hres⟩ := ihk _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · exact h.ifFrame _ _ _ _ _ _ _ _ _ _ _ (resolveVar_plain _ _ _ _) htc hec i hi
      · exact hkc i hi
  | whileLoop inits body k ihb ihk =>
      intro d n r hr
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨b, hb, rk, hk, rfl⟩ := hr
      obtain ⟨hbc, hbr⟩ := ihb _ _ _ hb
      obtain ⟨hkc, hres⟩ := ihk _ _ _ hk
      have hhead : plainOpB (b.res.headD (.imm 0)) = true := by
        cases hbs : b.res with
        | nil => rfl
        | cons o os => exact hbr o (by simp [hbs])
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · exact h.whileFrame _ _ _ _ _ _ _ _ (exprArgsHV_plain _ _ _ _) hhead
          (fun o ho => hbr o (List.mem_of_mem_tail ho)) hbc i hi
      · exact hkc i hi
  | call f args k ih =>
      intro d n r hr
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp hr
      obtain ⟨hkc, hres⟩ := ih _ _ _ hk
      refine ⟨fun i hi => ?_, hres⟩
      rcases List.mem_append.mp hi with hi | hi
      · rw [List.mem_singleton.mp hi]
        exact h.call _ _ _ (exprArgsHV_plain _ _ _ _)
      · exact hkc i hi

/-! ## 4. The forms of the instructions -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data x86Data_loopGuard
  x86Data_zeroTripGuard)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (callShadow shadowCall?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr arrShapeB renLoad
  renStore renZero renStoreImm renCallW renOpA renOpR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak (leakFixB arrBasesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (clsB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (mulxFree)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (flagCondCC? wideArgs?)

/-- **The forms of the instructions of a region export**: an `Lopn` with one register
    destination and plain sources; a load-tagged `LOADIDX` and a store-tagged `STOREIDX` of a
    register value at a register-indexed array operand; a label; a conditional jump on the
    zero flag. -/
def FormB (i : LinstrRM) : Prop :=
  (∃ dst m ss, i.1 = .Lopn [.reg dst] m ss ∧ ∀ o ∈ ss, plainOpB o = true) ∨
    (∃ dst b x sc w n, i = (.Lopn [.reg dst] "LOADIDX" [.arrIdx b x sc], .load w n)) ∨
    (∃ dst b x sc v w n,
      i = (.Lopn [.reg dst] "STOREIDX" [.arrIdx b x sc, .reg v], .store w n)) ∨
    (∃ l, i.1 = .Llabel .internal l) ∨
    (∃ l, i.1 = .Lcond (.reg "Z") l ∨ i.1 = .Lcond (.reg "NZ") l)

theorem formB_lopn {dst m : String} {ss : List LOperand} (tag : MemTag)
    (h : ∀ o ∈ ss, plainOpB o = true) : FormB (.Lopn [.reg dst] m ss, tag) :=
  Or.inl ⟨dst, m, ss, rfl, h⟩

theorem exprArgs_go_reg (d nArgs : Nat) (names : Nat → String) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ exprArgs.go d nArgs names (fun _ => none) hv, ∃ x, o = .reg x
  | [], _, o, ho => by simp [exprArgs.go] at ho
  | _ :: _, .cons v rest, o, ho => by
      change o ∈ resolveVar d nArgs names (fun _ => none) v
        :: exprArgs.go d nArgs names (fun _ => none) rest at ho
      rcases List.mem_cons.mp ho with rfl | ho
      · simp only [resolveVar]
        split_ifs <;> exact ⟨_, rfl⟩
      · exact exprArgs_go_reg d nArgs names rest o ho

/-- A variable of an expression resolves to a register at the empty map of immediate
    slots. -/
theorem exprArgs_reg (d nArgs : Nat) (names : Nat → String) {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    ∀ o ∈ exprArgs d nArgs names (fun _ => none) e, ∃ x, o = .reg x :=
  exprArgs_go_reg d nArgs names e.args

theorem plain_of_reg {ss : List LOperand} (h : ∀ o ∈ ss, ∃ x, o = .reg x) :
    ∀ o ∈ ss, plainOpB o = true := by
  intro o ho
  obtain ⟨x, rfl⟩ := h o ho
  rfl

/-- The wire of an operation on register sources: an `Lopn` with the destination register and
    plain sources, or the register-indexed `LOADIDX` of a load, or the register-indexed
    `STOREIDX` of a store of a register. -/
theorem opToLinstrR_form (op : JasminOp) (dst : String) (srcs : List LOperand)
    (hs : ∀ o ∈ srcs, ∃ x, o = .reg x) :
    (∃ m ss, opToLinstrR op dst srcs = .Lopn [.reg dst] m ss ∧
        ∀ o ∈ ss, plainOpB o = true) ∨
      (∃ w n b x, op = .stackLoad w n ∧
        opToLinstrR op dst srcs = .Lopn [.reg dst] "LOADIDX" [.arrIdx b x (w / 8)]) ∨
      (∃ w n b x v, op = .stackStore w n ∧
        opToLinstrR op dst srcs = .Lopn [.reg dst] "STOREIDX" [.arrIdx b x (w / 8), .reg v]) := by
  have hp := plain_of_reg hs
  have happ : ∀ k, ∀ o ∈ srcs ++ [.imm k], plainOpB o = true := by
    intro k o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hp o ho
    · rw [List.mem_singleton.mp ho]; rfl
  have hone : ∀ o' : LOperand, plainOpB o' = true → ∀ o ∈ [o'], plainOpB o = true := by
    intro o' h' o ho
    rw [List.mem_singleton.mp ho]
    exact h'
  have himm : ∀ a b : Nat, ∀ o ∈ [LOperand.imm a, .imm b], plainOpB o = true := by
    intro a b o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  unfold opToLinstrR
  split
  all_goals (try split) <;> (try split)
  all_goals try first
    | exact Or.inl ⟨_, _, rfl, hp⟩
    | exact Or.inl ⟨_, _, rfl, happ _⟩
    | exact Or.inl ⟨_, _, rfl, hone _ rfl⟩
    | exact Or.inl ⟨_, _, rfl, himm _ _⟩
    | exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl⟩)
  · obtain ⟨v, hv⟩ := hs _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    subst hv
    exact Or.inr (Or.inr ⟨_, _, _, _, _, rfl, rfl⟩)
  all_goals
    dsimp only
    split
    · exact Or.inl ⟨_, _, rfl, hp⟩
    · exact Or.inl ⟨_, _, rfl, hp⟩

/-- An operation on register sources whose wire is not a register-indexed `LOADIDX` or
    `STOREIDX` has the form of an `Lopn` with plain sources, at every tag. -/
theorem formB_of_opToLinstrR {op : JasminOp} {dst : String} {srcs : List LOperand}
    (hs : ∀ o ∈ srcs, ∃ x, o = .reg x) (h1 : ∀ w n, op ≠ .stackLoad w n)
    (h2 : ∀ w n, op ≠ .stackStore w n) (tag : MemTag) :
    FormB (opToLinstrR op dst srcs, tag) := by
  rcases opToLinstrR_form op dst srcs hs with ⟨m, ss, he, hp⟩ | ⟨w, n, -, -, hop, -⟩ |
      ⟨w, n, -, -, -, hop, -⟩
  · rw [he]
    exact formB_lopn tag hp
  · exact absurd hop (h1 w n)
  · exact absurd hop (h2 w n)

/-- **The binding instructions have the forms `FormB`.** -/
theorem bindOps_formB (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : ∀ i ∈ bindOps nArgs e d, FormB i := by
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  have hs := exprArgs_reg d nArgs argName e
  split
  · rename_i w n hop
    rw [hop]
    rcases opToLinstrR_form (.stackLoad w n) (regName d) _ hs with ⟨m, ss, he, hp⟩ |
        ⟨w', n', b, x, hop', he⟩ | ⟨w', n', -, -, -, hop', -⟩
    · rw [he]
      exact formB_lopn _ hp
    · cases hop'
      rw [he]
      exact Or.inr (Or.inl ⟨_, _, _, _, _, _, rfl⟩)
    · cases hop'
  · rename_i w n hop
    rw [hop]
    rcases opToLinstrR_form (.stackStore w n) (regName d) _ hs with ⟨m, ss, he, hp⟩ |
        ⟨w', n', -, -, hop', -⟩ | ⟨w', n', b, x, v, hop', he⟩
    · rw [he]
      exact formB_lopn _ hp
    · cases hop'
    · cases hop'
      rw [he]
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))
  all_goals try
    (rename_i hop
     rw [hop]
     exact formB_of_opToLinstrR hs (fun _ _ h => by cases h) (fun _ _ h => by cases h) _)
  all_goals
    rename_i hL hS _ _ _ _
    split
    · rename_i s _ hsrc
      obtain ⟨x, rfl⟩ := hs s (by rw [hsrc]; exact List.mem_singleton_self _)
      exact formB_lopn _ (by simp [plainOpB])
    · rename_i s _ hsrc
      obtain ⟨x, rfl⟩ := hs s (by rw [hsrc]; exact List.mem_singleton_self _)
      exact formB_lopn _ (by simp [plainOpB])
    · rename_i s _ hsrc
      obtain ⟨x, rfl⟩ := hs s (by rw [hsrc]; exact List.mem_singleton_self _)
      exact formB_lopn _ (by simp [plainOpB])
    · exact formB_of_opToLinstrR hs hL hS _

theorem plain_pair {a b : LOperand} (ha : plainOpB a = true) (hb : plainOpB b = true) :
    ∀ o ∈ [a, b], plainOpB o = true := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact ha
  · exact hb

/-- **The forms `FormB` are closed under the instructions of the export** at x86. -/
theorem exportClosed_formB (nArgs : Nat) : ExportClosed FormB nArgs x86Data where
  bind := bindOps_formB nArgs
  mov dst o ho := formB_lopn _ fun o' h' => by rw [List.mem_singleton.mp h']; exact ho
  label l := Or.inr (Or.inr (Or.inr (Or.inl ⟨l, rfl⟩)))
  arr z t a := by
    intro i hi
    simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact Or.inr (Or.inl ⟨_, _, _, _, _, _, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))
  adv idx ctr := by
    intro i hi
    simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact formB_lopn _ (plain_pair rfl rfl)
  flag r z o ho := by
    intro i hi
    unfold flagWord at hi
    split at hi
    · rw [show x86Data.selectMnemonic = some "CMOV" from rfl] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact formB_lopn _ fun o' h' => by rw [List.mem_singleton.mp h']; rfl
      · exact formB_lopn _ fun o' h' => by rw [List.mem_singleton.mp h']; rfl
      · refine formB_lopn _ fun o' h' => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with rfl | rfl | rfl <;> rfl
    · rw [List.mem_singleton.mp hi]
      exact formB_lopn _ fun o' h' => by rw [List.mem_singleton.mp h']; exact ho
  zero ctr top endL := by
    intro g hg
    rw [x86Data_zeroTripGuard] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact formB_lopn _ (plain_pair rfl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, Or.inl rfl⟩)))
  loop ctr top := by
    intro g hg
    rw [x86Data_loopGuard] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact formB_lopn _ (plain_pair rfl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, Or.inr rfl⟩)))
  call dst f srcs hs := formB_lopn _ hs

/-! ## 5. The conjuncts of the forms -/

/-- An instruction of the forms `FormB` passes the check of its events `leakFixB` at every
    renaming: its array operands are those of a register-indexed `LOADIDX` or `STOREIDX`. -/
theorem leakFixB_of_formB (σ : String → String) {i : LinstrRM} (h : FormB i) :
    leakFixB σ i = true := by
  obtain ⟨wire, tag⟩ := i
  rcases h with ⟨dst, m, ss, hw, hp⟩ | ⟨dst, b, x, sc, w, n, he⟩ |
      ⟨dst, b, x, sc, v, w, n, he⟩ | ⟨l, hw⟩ | ⟨l, hw | hw⟩
  · dsimp only at hw
    subst hw
    unfold leakFixB
    simp only [Bool.or_eq_true]
    refine Or.inr (Or.inr ?_)
    simp only [List.all_eq_true, List.mem_append, List.mem_singleton]
    rintro o (rfl | ho)
    · simp [arrBasesOf]
    · have := hp o ho
      cases o <;> simp_all [plainOpB, arrBasesOf]
  · cases he
    simp [leakFixB, arrShapeB, loadStruct?]
  · cases he
    simp [leakFixB, arrShapeB, storeStruct?]
  all_goals
    dsimp only at hw
    subst hw
    cases tag <;> simp [leakFixB, arrShapeB, loadStruct?, storeStruct?, zeroStruct?,
      storeImmStruct?]

/-- An instruction of the forms `FormB` is in the classes of the simulation (`clsB`) and is
    no `MULX`. -/
theorem clsB_mulxFree_of_formB {i : LinstrRM} (h : FormB i) :
    clsB i = true ∧ mulxFree i = true := by
  obtain ⟨wire, tag⟩ := i
  rcases h with ⟨dst, m, ss, hw, -⟩ | ⟨dst, b, x, sc, w, n, he⟩ |
      ⟨dst, b, x, sc, v, w, n, he⟩ | ⟨l, hw⟩ | ⟨l, hw | hw⟩
  · dsimp only at hw
    subst hw
    exact ⟨rfl, JasminLsemExportRewrites.mulxFree_of_lopn1 ⟨_, _, _, rfl⟩⟩
  · cases he
    exact ⟨rfl, JasminLsemExportRewrites.mulxFree_of_lopn1 ⟨_, _, _, rfl⟩⟩
  · cases he
    exact ⟨rfl, JasminLsemExportRewrites.mulxFree_of_lopn1 ⟨_, _, _, rfl⟩⟩
  all_goals
    dsimp only at hw
    subst hw
    exact ⟨rfl, rfl⟩

/-! ## 6. The renaming of array positions -/

theorem plainOpB_renOpA (σ : String → String) {o : LOperand} (h : plainOpB o = true) :
    plainOpB (renOpA σ o) = true := by
  cases o <;> simp_all [plainOpB, renOpA]

theorem plainOpB_renOpR (σ : String → String) {o : LOperand} (h : plainOpB o = true) :
    plainOpB (renOpR σ o) = true := by
  cases o <;> simp_all [plainOpB, renOpR]

/-- An `Lopn` with a register destination and plain sources keeps its form under the renaming
    of a call shadow. -/
theorem formB_renCallW (σ : String → String) {dst m : String} {ss : List LOperand}
    (tag : MemTag) (hp : ∀ o ∈ ss, plainOpB o = true) :
    FormB (renCallW σ (.Lopn [.reg dst] m ss), tag) := by
  unfold renCallW
  split
  · rename_i d f srcs hc
    simp only [shadowCall?] at hc
    split_ifs at hc with hpre
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨-, -, rfl⟩ := hc
    exact formB_lopn tag fun o ho => by
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
      exact plainOpB_renOpR σ (hp o' ho')
  · exact formB_lopn tag hp

/-- **The forms `FormB` are kept by the renaming of array positions** `renArr`. -/
theorem formB_renArr (σ : String → String) {i : LinstrRM} (h : FormB i) :
    FormB (renArr σ i) := by
  obtain ⟨wire, tag⟩ := i
  rcases h with ⟨dst, m, ss, hw, hp⟩ | ⟨dst, b, x, sc, w, n, he⟩ |
      ⟨dst, b, x, sc, v, w, n, he⟩ | ⟨l, hw⟩ | ⟨l, hw | hw⟩
  · dsimp only at hw
    subst hw
    have hne1 : ∀ b x sc, ss ≠ [.arrIdx b x sc] := by
      rintro b x sc rfl
      simp [plainOpB] at hp
    have hne2 : ∀ b x sc v, ss ≠ [.arrIdx b x sc, .reg v] := by
      rintro b x sc v rfl
      simp [plainOpB] at hp
    cases tag with
    | load w n =>
        change FormB (renLoad σ (.Lopn [.reg dst] m ss), _)
        unfold renLoad
        split
        · rename_i hm
          simp only [LinstrR.Lopn.injEq] at hm
          exact absurd hm.2.2 (hne1 _ _ _)
        · exact formB_lopn _ hp
    | store w n =>
        change FormB (renStore σ (.Lopn [.reg dst] m ss), _)
        unfold renStore
        split
        · rename_i hm
          simp only [LinstrR.Lopn.injEq] at hm
          exact absurd hm.2.2 (hne2 _ _ _ _)
        · exact formB_lopn _ hp
    | zero w n =>
        change FormB (renZero σ (.Lopn [.reg dst] m ss), _)
        simp only [renZero]
        split_ifs
        · exact formB_lopn _ fun o ho => by
            obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
            exact plainOpB_renOpA σ (hp o' ho')
        · exact formB_lopn _ hp
    | storeImm w n =>
        change FormB (renStoreImm σ (.Lopn [.reg dst] m ss), _)
        unfold renStoreImm
        split
        · rename_i hm
          simp only [LinstrR.Lopn.injEq] at hm
          obtain ⟨-, rfl, rfl⟩ := hm
          split_ifs
          · exact formB_lopn _ fun o ho => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
              rcases ho with rfl | rfl | rfl <;> rfl
          · exact formB_lopn _ hp
        · exact formB_lopn _ hp
    | _ => exact formB_renCallW σ _ hp
  · cases he
    exact Or.inr (Or.inl ⟨dst, σ b, x, sc, w, n, by simp [renArr, renLoad]⟩)
  · cases he
    exact Or.inr (Or.inr (Or.inl ⟨σ dst, σ b, x, sc, v, w, n, by simp [renArr, renStore]⟩))
  all_goals
    dsimp only at hw
    subst hw
    cases tag <;> simp [renArr, renLoad, renStore, renZero, renStoreImm, renCallW, shadowCall?,
      FormB]

/-! ## 7. The code with the result copies -/

open CatCrypt.Crypto.SecureCompilation.Haxc (regionCoCode regionCoCodeN regionCoBody
  regionCopy regionAliasN constArrFreeB resCopyCode resCopyStep regionCoStage calleeCodeT)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak (leakFixCfgB)

theorem formB_movesOf (ps : List (String × String)) : ∀ i ∈ movesOf ps, FormB i := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact formB_lopn _ fun o ho => by rw [List.mem_singleton.mp ho]; rfl

theorem formB_resCopyCode (src D : String) (m : Nat) : ∀ i ∈ resCopyCode src D m, FormB i := by
  intro i hi
  obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact formB_lopn _ fun o ho => by rw [List.mem_singleton.mp ho]; rfl
  · exact Or.inr (Or.inl ⟨_, _, _, _, _, _, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl⟩))

/-- **Every instruction of the code with the result copies of an export at x86 has the forms
    `FormB`.** -/
theorem formB_regionCoCode {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (t : JasminTy) (cp : Option (String × String × Nat)) :
    ∀ i ∈ regionCoCode σ nm t r.code r.res cp, FormB i := by
  have hc := (exportR_forall (exportClosed_formB nArgs) fn p d n r hr).1
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact hc i hi
    · exact formB_movesOf _ i hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact hc i hi
      · exact formB_movesOf _ i hi
    · exact formB_resCopyCode _ _ _ i hi

/-- An instruction of the forms `FormB` has no compile-time array operand. -/
theorem constArrFreeB_of_formB {i : LinstrRM} (h : FormB i) : constArrFreeB i = true := by
  obtain ⟨wire, tag⟩ := i
  rcases h with ⟨dst, m, ss, hw, hp⟩ | ⟨dst, b, x, sc, w, n, he⟩ |
      ⟨dst, b, x, sc, v, w, n, he⟩ | ⟨l, hw⟩ | ⟨l, hw | hw⟩
  · dsimp only at hw
    subst hw
    simp only [constArrFreeB, List.all_eq_true, List.mem_append, List.mem_singleton]
    rintro o (rfl | ho)
    · rfl
    · have := hp o ho
      cases o <;> simp_all [plainOpB]
  · cases he
    rfl
  · cases he
    rfl
  all_goals
    dsimp only at hw
    subst hw
    rfl

/-! ## 8. The conjuncts of the gate and of the event check -/

/-- **The class conjunct of the gate holds on every export at x86** (stage `coClass` of
    `regionCoStage`): every instruction of the code with the result copies is in the classes
    of the simulation (`clsB`) and is no `MULX` (`mulxFree`). -/
theorem coClass_regionCoCode {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (t : JasminTy) (cp : Option (String × String × Nat)) :
    (regionCoCode σ nm t r.code r.res cp).all (fun i => clsB i && mulxFree i) = true := by
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨h1, h2⟩ := clsB_mulxFree_of_formB (formB_regionCoCode hr σ nm t cp i hi)
  rw [h1, h2]
  rfl

/-- **The first conjunct of the event check holds on every export at x86**: the code with
    the result copies passes `leakFixCfgB` at every renaming, the alias map of the gate among
    them. -/
theorem leakFixCfgB_regionCoCode {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (t : JasminTy) (cp : Option (String × String × Nat)) (ρ : String → String) :
    leakFixCfgB ρ (regionCoCode σ nm t r.code r.res cp) = true :=
  List.all_eq_true.mpr fun i hi => leakFixB_of_formB ρ (formB_regionCoCode hr σ nm t cp i hi)

/-- **The second conjunct of the event check holds on every export at x86**: the coalesced
    code `regionCoBody` has no compile-time array operand. -/
theorem constArrFreeB_regionCoBody {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (t : JasminTy) :
    (regionCoBody σ nm t r.code r.res).all constArrFreeB = true := by
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact constArrFreeB_of_formB (formB_renArr _ (formB_regionCoCode hr σ nm t _ j hj))

/-- **The first two conjuncts of `regionLeakB` hold on every export at x86**: the alias map
    `regionAliasN` fixes the array bases of the events of the code with the result copies
    (`leakFixCfgB`), and the coalesced code has no compile-time array operand. The remaining
    conjuncts are the liveness checks `regLeakB` of the merge and the check on traced runs
    `ownedCheckML`. -/
theorem regionLeakB_fix_constArr {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (t : JasminTy) :
    leakFixCfgB (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res))
        (regionCoCodeN σ nm t r.code r.res) = true ∧
      (regionCoBody σ nm t r.code r.res).all constArrFreeB = true :=
  ⟨leakFixCfgB_regionCoCode hr σ nm t _ _, constArrFreeB_regionCoBody hr σ nm t⟩

/-- **The gate does not refuse an export at x86 at the class stage**: on the call-free arm
    (no table of callees), `regionCoStage` on the code and the returned operands of an export
    at x86 is not `coClass`, at every printed body, result type, certificate and function
    name. -/
theorem regionCoStage_ne_coClass {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (body : Lcmd) (t : JasminTy) (cert : List (String × String)) (fn' : String) :
    regionCoStage σ nm body t r.code r.res cert none fn' ≠ some "coClass" := by
  have hc := coClass_regionCoCode hr σ nm t (regionCopy σ nm t none r.code r.res)
  unfold regionCoStage
  dsimp only
  simp only [calleeCodeT, Option.all_none, Bool.true_eq_false, ite_false]
  rw [hc]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-! ## 9. The liveness conjuncts of the event check -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAllocLeak (leakLiveB idxNames
  cArrBases idxNamesOf cArrBasesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR
  renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete (liveRegTab_closed
  liveRegTab_stable)

/-- **The event operands of an instruction are sources**: no destination operand of an `Lopn`
    is register-indexed, and no operand of it is a compile-time array element. Every other
    instruction has the property. -/
def IdxSrc : LinstrR → Prop
  | .Lopn ds _ ss =>
      (∀ o ∈ ds, idxNamesOf o = [] ∧ cArrBasesOf o = []) ∧ ∀ o ∈ ss, cArrBasesOf o = []
  | _ => True

theorem idxNamesOf_renOperand (σ : String → String) (o : LOperand) :
    idxNamesOf (renOperand σ o) = (idxNamesOf o).map σ := by
  cases o <;> rfl

theorem cArrBasesOf_renOperand (σ : String → String) (o : LOperand) :
    cArrBasesOf (renOperand σ o) = cArrBasesOf o := by
  cases o <;> rfl

/-- The index register of an operand is one of its names. -/
theorem mem_opNames_of_mem_idxNamesOf {o : LOperand} {x : String} (h : x ∈ idxNamesOf o) :
    x ∈ opNames o := by
  cases o <;> simp_all [idxNamesOf, opNames]

/-- Renaming keeps `IdxSrc`. -/
theorem idxSrc_renLinstrR (σ : String → String) {i : LinstrR} (h : IdxSrc i) :
    IdxSrc (renLinstrR σ i) := by
  cases i with
  | Lopn ds m ss =>
    obtain ⟨hd, hs⟩ := h
    refine ⟨fun o' ho' => ?_, fun o' ho' => ?_⟩
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
      rw [idxNamesOf_renOperand, cArrBasesOf_renOperand, (hd o ho).1, (hd o ho).2]
      exact ⟨rfl, rfl⟩
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
      rw [cArrBasesOf_renOperand]
      exact hs o ho
  | _ => trivial

/-- An instruction of the forms `FormB` has its event operands among its sources. -/
theorem idxSrc_of_formB {i : LinstrRM} (h : FormB i) : IdxSrc i.1 := by
  obtain ⟨wire, tag⟩ := i
  rcases h with ⟨dst, m, ss, hw, hp⟩ | ⟨dst, b, x, sc, w, n, he⟩ |
      ⟨dst, b, x, sc, v, w, n, he⟩ | ⟨l, hw⟩ | ⟨l, hw | hw⟩
  · dsimp only at hw
    subst hw
    refine ⟨fun o ho => ?_, fun o ho => ?_⟩
    · rw [List.mem_singleton.mp ho]
      exact ⟨rfl, rfl⟩
    · have := hp o ho
      cases o <;> simp_all [plainOpB, cArrBasesOf]
  · cases he
    exact ⟨fun o ho => by rw [List.mem_singleton.mp ho]; exact ⟨rfl, rfl⟩,
      fun o ho => by rw [List.mem_singleton.mp ho]; rfl⟩
  · cases he
    refine ⟨fun o ho => by rw [List.mem_singleton.mp ho]; exact ⟨rfl, rfl⟩, fun o ho => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rfl
  all_goals
    dsimp only at hw
    subst hw
    trivial

/-- **An instruction whose event operands are sources passes `leakLiveB`** at every merge and
    every list of names containing the names it reads. -/
theorem leakLiveB_of_idxSrc (τ : String → String) (N : List String) {i : LinstrRM}
    (h : IdxSrc i.1) (hu : ∀ x ∈ useNames i.1, x ∈ N) : leakLiveB τ N i = true := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds m ss =>
    obtain ⟨hd, hs⟩ := h
    have hc : cArrBases (.Lopn ds m ss) = [] := by
      change (if stripWidthTag m = "LEA" then [] else (ds ++ ss).flatMap cArrBasesOf) = []
      split
      · rfl
      · refine List.flatMap_eq_nil_iff.mpr fun o ho => ?_
        rcases List.mem_append.mp ho with ho | ho
        · exact (hd o ho).2
        · exact hs o ho
    have hx : ∀ x ∈ idxNames (.Lopn ds m ss), x ∈ N := by
      intro x hx
      change x ∈ (if stripWidthTag m = "LEA" then [] else (ds ++ ss).flatMap idxNamesOf) at hx
      split at hx
      · simp at hx
      · obtain ⟨o, ho, hxo⟩ := List.mem_flatMap.mp hx
        rcases List.mem_append.mp ho with ho | ho
        · rw [(hd o ho).1] at hxo
          simp at hxo
        · exact hu x (List.mem_flatMap.mpr ⟨o, ho, mem_opNames_of_mem_idxNamesOf hxo⟩)
    simp only [leakLiveB, hc, List.all_nil, Bool.and_true, List.all_eq_true]
    exact fun x hx' => by simpa using hx x hx'
  | _ => simp [leakLiveB, idxNames, cArrBases]

/-- A name an instruction reads is among the names `liveRegNeed` requires before it. -/
theorem mem_liveRegNeed_of_useNames {body : List LinstrRM} {A : Array (List String)} {k : Nat}
    {i : LinstrRM} {x : String} (hx : x ∈ useNames i.1) : x ∈ liveRegNeed body A k i := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds m ss =>
    simp only [liveRegNeed]
    exact List.mem_append_left _ hx
  | _ => simp [useNames] at hx

/-- **Code whose event operands are sources passes the liveness check of its events** at every
    merge `τ`, against the liveness table `liveRegTab` of the code behind the prefix `pre` with
    the names `outs` read after it. -/
theorem regLeakB_liveRegTab (τ : String → String) (pre C : List LinstrRM) (outs : List String)
    (h : ∀ i ∈ C, IdxSrc i.1) :
    regLeakB τ pre C (tabAt (liveRegTab (pre ++ C) outs)) = true := by
  unfold regLeakB
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  rw [List.getElem?_eq_getElem hj]
  have hi : (pre ++ C)[pre.length + j]? = some C[j] := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj]
  refine leakLiveB_of_idxSrc τ _ (h _ (List.getElem_mem hj)) fun x hx => ?_
  have hlt : pre.length + j < (pre ++ C).length := by
    rw [List.length_append]
    omega
  simp only [liveAt, Nat.min_eq_left hlt.le]
  exact List.mem_cons_of_mem _ (liveRegTab_closed (liveRegTab_stable _ _) hi x
    (mem_liveRegNeed_of_useNames hx))

/-- Every instruction of the coalesced code of an export at x86 has its event operands among
    its sources. -/
theorem idxSrc_regionCoBody {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (t : JasminTy) : ∀ i ∈ regionCoBody σ nm t r.code r.res, IdxSrc i.1 := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact idxSrc_of_formB (formB_renArr _ (formB_regionCoCode hr σ nm t _ j hj))

/-- **The third and fourth conjuncts of `regionLeakB` hold on every export at x86**: at every
    printed body, result type and certificate, the renamed code of the parts passes `regLeakB`
    of the merge at the table `d.live`, and the merged code passes `regLeakB` of the identity
    at the table `d.liveM`. -/
theorem regionLeakB_live {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (body : Lcmd) (t : JasminTy) (cert : List (String × String)) :
    ((regionCoParts σ nm body t r.code r.res cert).tau == []
        || regLeakB (renOf (regionCoParts σ nm body t r.code r.res cert).tau)
          (regionCoParts σ nm body t r.code r.res cert).pre
          (regionCoParts σ nm body t r.code r.res cert).ren
          (tabAt (regionCoParts σ nm body t r.code r.res cert).live)) = true ∧
      regLeakB id (regionCoParts σ nm body t r.code r.res cert).pre
        (regionCoParts σ nm body t r.code r.res cert).merged
        (tabAt (regionCoParts σ nm body t r.code r.res cert).liveM) = true := by
  have hren : ∀ i ∈ (regionCoParts σ nm body t r.code r.res cert).ren, IdxSrc i.1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact idxSrc_renLinstrR _ (idxSrc_regionCoBody hr σ nm t j hj)
  have hmer : ∀ i ∈ (regionCoParts σ nm body t r.code r.res cert).merged, IdxSrc i.1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact idxSrc_renLinstrR _ (hren j hj)
  refine ⟨Bool.or_eq_true_iff.mpr (Or.inr ?_), ?_⟩
  · exact regLeakB_liveRegTab _ _ _ _ hren
  · exact regLeakB_liveRegTab _ _ _ _ hmer

/-- **The first four conjuncts of `regionLeakB` hold on every export at x86**: the alias map
    fixes the array bases of the events of the code with the result copies, the coalesced code
    has no compile-time array operand, and the renamed and the merged code pass the liveness
    checks of their events. The remaining conjunct is the check on traced runs
    `ownedCheckML`. -/
theorem regionLeakB_four {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {r : Exported}
    (hr : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (body : Lcmd) (t : JasminTy) (cert : List (String × String)) :
    (leakFixCfgB (regionAliasN σ nm t r.res (regionCoCodeN σ nm t r.code r.res))
        (regionCoCodeN σ nm t r.code r.res)
      && (regionCoBody σ nm t r.code r.res).all constArrFreeB
      && ((regionCoParts σ nm body t r.code r.res cert).tau == []
        || regLeakB (renOf (regionCoParts σ nm body t r.code r.res cert).tau)
          (regionCoParts σ nm body t r.code r.res cert).pre
          (regionCoParts σ nm body t r.code r.res cert).ren
          (tabAt (regionCoParts σ nm body t r.code r.res cert).live))
      && regLeakB id (regionCoParts σ nm body t r.code r.res cert).pre
        (regionCoParts σ nm body t r.code r.res cert).merged
        (tabAt (regionCoParts σ nm body t r.code r.res cert).liveM)) = true := by
  obtain ⟨h1, h2⟩ := regionLeakB_fix_constArr hr σ nm t
  obtain ⟨h3, h4⟩ := regionLeakB_live hr σ nm body t cert
  rw [h1, h2, h3, h4]
  rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportForms
