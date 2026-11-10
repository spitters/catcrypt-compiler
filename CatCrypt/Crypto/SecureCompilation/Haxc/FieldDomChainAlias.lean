/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomChainClass

/-!
# The coalescing renaming of the export of one chain of stores

The coalescing renaming `chainAlias` of a body folds the alias steps `aliasStepO` over its
instructions: a store sends its destination to the root of its base, and every other
instruction of an export without callee leaves the table as it is. On the export of a program
of the shape `LoadsChain`, the exported binding of a memory-free operation and of a load keep
the table, and the exported store of the slot `regName d` inserts `regName d` with the root of
the current version. The fold therefore sends every written name to the root of the chain and
keeps every other name, and with the consumption facts of the chain the export has the whole
store-chain shape under `chainAlias`.

## Main definitions

* `AliasFacts`: from every table, the fold of the alias steps sends the written names to the
  image of the root and keeps the others.

## Main results

* `aliasStepO_nil_lopn`: an instruction with one register destination and no indexed source,
  whose mnemonic is not `STOREIMM`, leaves the table without out symbols as it is.
* `aliasStepO_bindOps_memFree`, `aliasStepO_bindOps_load`, `aliasStepO_bindOps_store`: the
  alias steps of the exported memory-free bindings, loads and stores.
* `chainTail_export_alias`, `loadsChain_export_consume_alias`: the alias facts of the export
  of a chain tail, and of a program of the shape `LoadsChain` together with its consumption
  facts.
* `loadsChain_export_chainShape_alias`: the store-chain shape of that export under its
  coalescing renaming `chainAlias`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO)

/-- **An instruction that stores nothing keeps the alias table**: one register destination, no
    indexed source and a mnemonic other than `STOREIMM`, at no out symbol. -/
theorem aliasStepO_nil_lopn (M : Std.HashMap String String)
    {dst opn : String} {srcs : List LOperand} (tag : JasminLsemMem.MemTag)
    (hs : ∀ o ∈ srcs, ∀ b x sc, o ≠ .arrIdx b x sc) (hst : opn ≠ "STOREIMM") :
    aliasStepO [] M (.Lopn [.reg dst] opn srcs, tag) = M := by
  unfold aliasStepO
  cases hc : LprogIsa.shadowCall? (.Lopn [.reg dst] opn srcs) with
  | some t =>
      obtain ⟨d', f, srcs'⟩ := t
      rfl
  | none =>
      dsimp only
      split
      · rename_i dst' opn' base x sc rest hw
        simp only [LinstrR.Lopn.injEq] at hw
        obtain ⟨-, -, rfl⟩ := hw
        exact absurd rfl (hs _ (List.mem_cons_self ..) base x sc)
      · rename_i dst' opn' base rest hw
        simp only [LinstrR.Lopn.injEq] at hw
        obtain ⟨-, rfl, -⟩ := hw
        simp [hst]
      · rfl

/-- An exported argument of a binding is no indexed operand. -/
theorem not_arrIdx_of_exprArgs {d nArgs : Nat} {Γ : Ctxt jasminDialect} {τ : JasminTy}
    {e : Expr jasminDialect Γ τ} {o : LOperand}
    (ho : o ∈ exprArgs d nArgs argName (fun _ => none) e) : ∀ b x sc, o ≠ .arrIdx b x sc := by
  obtain ⟨n, rfl⟩ := RegionExportForms.exprArgs_reg _ _ _ _ o ho
  intro b x sc h
  cases h

/-- A vector mnemonic is not `STOREIMM`. -/
theorem ne_storeImm_of_vector {opn : String} (h : AllocForm.VectorMnem opn) :
    opn ≠ "STOREIMM" := by
  rintro rfl
  simp [AllocForm.VectorMnem] at h

/-- **The exported memory-free binding keeps the alias table.** -/
theorem aliasStepO_bindOps_memFree (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : jMemFree e.op = true) :
    ∃ ins, bindOps nArgs e d = [ins] ∧ ∀ M, aliasStepO [] M ins = M := by
  obtain ⟨op, rfl, args⟩ := e
  refine ⟨_, rfl, fun M => ?_⟩
  cases op <;> simp only [jMemFree, Bool.false_eq_true] at he <;>
    dsimp only [bindOps, JasminLsemMem.straightOpsMem]
  all_goals try refine aliasStepO_nil_lopn _ _ ?_ ?_
  all_goals try first
    | exact fun o ho => not_arrIdx_of_exprArgs ho
    | (intro o ho
       rcases List.mem_append.mp ho with ho | ho
       · exact not_arrIdx_of_exprArgs ho
       · simp only [List.mem_singleton] at ho
         subst ho
         intro b x sc h
         cases h)
    | (intro o ho b x sc h
       simp only [List.mem_singleton] at ho
       subst ho
       cases h)
    | (simp [withWidthTag, String.ext_iff]; done)
    | (unfold withWidthTag
       split <;> (try unfold binOpName) <;> (try unfold cmpName) <;> (try split) <;>
         simp [String.ext_iff])
    | exact ne_storeImm_of_vector (AllocForm.simdMnemonic_vector _)
    | exact ne_storeImm_of_vector (AllocForm.ymmMnemonic_vector _)
  case castW =>
    simp only [opToLinstrR]
    split <;> refine aliasStepO_nil_lopn _ _ ?_ ?_
    all_goals first
      | exact fun o ho => not_arrIdx_of_exprArgs ho
      | (unfold castWMnem
         repeat' split
         all_goals simp [String.ext_iff])
      | (split <;> simp [String.ext_iff])
  case callN =>
    simp only [opToLinstrR]
    split <;> refine aliasStepO_nil_lopn _ _ ?_ ?_
    all_goals first
      | exact fun o ho => not_arrIdx_of_exprArgs ho
      | simp [encodeCallW, String.ext_iff]
  all_goals
    split
    all_goals refine aliasStepO_nil_lopn _ _ ?_ ?_
    all_goals first
      | exact fun o ho => not_arrIdx_of_exprArgs ho
      | (rename_i s hs
         intro o ho b x sc h
         simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
         rcases ho with rfl | rfl
         · exact not_arrIdx_of_exprArgs (by rw [hs]; simp) b x sc h
         · cases h)
      | (unfold withWidthTag
         split <;> simp [String.ext_iff])

/-- **The exported load keeps the alias table.** -/
theorem aliasStepO_bindOps_load (nArgs d : Nat) {Γ : Ctxt jasminDialect} {w m : Nat}
    (a : Ctxt.Var Γ (.stackArr w m)) (i : Ctxt.Var Γ (.reg 64)) :
    ∃ ins, bindOps nArgs (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ :
        Expr jasminDialect Γ (.reg w)) d = [ins] ∧ ∀ M, aliasStepO [] M ins = M := by
  have hgo : exprArgs.go d nArgs argName (fun _ => none)
      (HVector.cons a (HVector.cons i HVector.nil)) =
      [resolveVar d nArgs argName (fun _ => none) a,
        resolveVar d nArgs argName (fun _ => none) i] :=
    rfl
  refine ⟨_, rfl, fun M => ?_⟩
  simp only [exprArgs, hgo]
  rw [resolveVar_reg d nArgs a, resolveVar_reg d nArgs i]
  have hm : isMemStore "LOADIDX" = false := by decide
  simp [aliasStepO, opToLinstrR, LprogIsa.shadowCall?, hm]

/-- The name of a variable resolved at the depth `d`. -/
abbrev curNameAt (d nArgs : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    String :=
  JasminLsemWidthN.operandName (resolveVar d nArgs argName (fun _ => none) v)

/-- **The exported store of the slot `regName d` sends it to the root of its base.** -/
theorem aliasStepO_bindOps_store (nArgs d : Nat) {Γ : Ctxt jasminDialect} {w m : Nat}
    (v : Ctxt.Var Γ (.stackArr w m)) (i : Ctxt.Var Γ (.reg 64)) (x : Ctxt.Var Γ (.reg w)) :
    ∃ ins, bindOps nArgs (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
        Expr jasminDialect Γ (.stackArr w m)) d = [ins] ∧ ∀ M, aliasStepO [] M ins =
          M.insert (regName d) (M.getD (curNameAt d nArgs v) (curNameAt d nArgs v)) := by
  have hgo : exprArgs.go d nArgs argName (fun _ => none)
      (HVector.cons v (HVector.cons i (HVector.cons x HVector.nil))) =
      [resolveVar d nArgs argName (fun _ => none) v, resolveVar d nArgs argName (fun _ => none) i,
        resolveVar d nArgs argName (fun _ => none) x] := rfl
  refine ⟨_, rfl, fun M => ?_⟩
  simp only [exprArgs, hgo]
  rw [resolveVar_reg d nArgs v, resolveVar_reg d nArgs i, resolveVar_reg d nArgs x]
  have hm : isMemStore "STOREIDX" = true := by decide
  simp [aliasStepO, opToLinstrR, LprogIsa.shadowCall?, hm]

open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainConsume ChainShape chainShape₃_of_consume rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (regName_injective)

section ExportAlias

variable {nArgs : Nat} {fn : String} {aa : String → Nat → Option Nat}
  {ao : String → Option Nat}

/-- **The alias facts of one chain from the root `x`**: from every table, the fold of the
    alias steps sends every written name to the image of `x` and keeps every other name. -/
def AliasFacts (body : List JasminLsemMem.LinstrRM) (ao : String → Option Nat) (x : String) :
    Prop :=
  ∀ M : Std.HashMap String String,
    (∀ w n, WrAt body ao w n → (body.foldl (aliasStepO []) M).getD n n = M.getD x x)
      ∧ ∀ n, (∀ w, ¬ WrAt body ao w n) → (body.foldl (aliasStepO []) M).getD n n = M.getD n n

/-- The alias facts of a body with an instruction in front that keeps the table and writes
    no array. -/
theorem aliasFacts_cons_fix {ins : JasminLsemMem.LinstrRM} {body : List JasminLsemMem.LinstrRM}
    {x : String} (h : AliasFacts body ao x) (hins : ∀ M, aliasStepO [] M ins = M)
    (hw : wrArr ao ins = none) : AliasFacts (ins :: body) ao x := by
  intro M
  obtain ⟨h1, h2⟩ := h M
  rw [List.foldl_cons, hins]
  refine ⟨fun w n hwn => ?_, fun n hn => h2 n fun w hw' => hn (w + 1) (wrAt_cons_succ.mpr hw')⟩
  cases w with
  | zero => rw [wrAt_cons_zero, hw] at hwn; cases hwn
  | succ w => exact h1 w n (wrAt_cons_succ.mp hwn)

/-- The alias facts of a store in front of the rest of its chain: the store sends `y` to the
    root of `x`, and the rest is a chain from `y` that does not write `y`. -/
theorem aliasFacts_cons_store {ins : JasminLsemMem.LinstrRM} {body : List JasminLsemMem.LinstrRM}
    {x y : String} (h : AliasFacts body ao y)
    (hins : ∀ M, aliasStepO [] M ins = M.insert y (M.getD x x))
    (hwr : wrArr ao ins = some y) (hy : ∀ w, ¬ WrAt body ao w y) :
    AliasFacts (ins :: body) ao x := by
  intro M
  obtain ⟨h1, h2⟩ := h (M.insert y (M.getD x x))
  rw [List.foldl_cons, hins]
  refine ⟨fun w n hwn => ?_, fun n hn => ?_⟩
  · cases w with
    | zero =>
        rw [wrAt_cons_zero, hwr] at hwn
        cases hwn
        rw [h2 _ hy]
        simp
    | succ w =>
        rw [h1 w n (wrAt_cons_succ.mp hwn)]
        simp
  · have hne : y ≠ n := by
      rintro rfl
      exact hn 0 (wrAt_cons_zero.mpr hwr)
    rw [h2 n fun w hw' => hn (w + 1) (wrAt_cons_succ.mpr hw')]
    simp [Std.HashMap.getD_insert, hne]


/-- **The export of a chain tail has the alias facts of one chain** from the name of its
    current version. -/
theorem chainTail_export_alias (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy} {v : Ctxt.Var Γ (.stackArr w m)}
    {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) (hn : nArgs ≤ Γ.length) {n : Nat}
    {r : Exported} (hr : exportR nArgs fn k Γ.length n = some r) :
    AliasFacts r.code ao (curName nArgs v) := by
  induction h generalizing n r with
  | @free Γ w m t ts v e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hins⟩ := aliasStepO_bindOps_memFree nArgs Γ.length e he
      obtain ⟨ins', hb', -, hwr⟩ := bindOps_memFree nArgs Γ.length e he (fun _ _ => none) ao
        (fun _ _ => rfl) hao
      rw [hb] at hb'
      obtain rfl : ins = ins' := List.singleton_inj.mp hb'
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have := ih (by simp only [List.length_cons]; omega) hk'
      rw [curName, List.length_cons, resolveVar_there] at this
      exact aliasFacts_cons_fix this hins hwr
  | @store Γ w m ts v i x k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hins⟩ := aliasStepO_bindOps_store nArgs Γ.length v i x
      obtain ⟨ins', hb', hwr, -⟩ := bindOps_store nArgs Γ.length v i x (fun _ _ => none) ao
      rw [hb] at hb'
      obtain rfl : ins = ins' := List.singleton_inj.mp hb'
      have hrest := ih (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hrest
      obtain ⟨hF, -⟩ := chainTail_export (fn := fn) (aa := fun _ _ => none) (fun _ _ => rfl) hao hk
        (by simp only [List.length_cons]; omega) hk'
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      refine aliasFacts_cons_store hrest hins hwr fun w' hw' => ?_
      have h1 := hF.2.1 w' _ hw'
      have := regName_injective h1
      simp only [List.length_cons] at this
      omega
  | @ret Γ w m v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      intro M
      refine ⟨fun w n h => ?_, fun n _ => rfl⟩
      obtain ⟨_, h, -⟩ := h
      simp at h

/-- **The export of a program of the shape `LoadsChain` has the consumption and the alias
    facts of one chain**, from the same root. -/
theorem loadsChain_export_consume_alias (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) :
    ∃ x, ChainConsume r.code (fun _ _ => none) ao x ∧ AliasFacts r.code ao x := by
  induction h generalizing n r with
  | @free Γ t ts e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hins⟩ := aliasStepO_bindOps_memFree nArgs Γ.length e he
      obtain ⟨ins', hb', -, hwr⟩ := bindOps_memFree nArgs Γ.length e he (fun _ _ => none) ao
        (fun _ _ => rfl) hao
      rw [hb] at hb'
      obtain rfl : ins = ins' := List.singleton_inj.mp hb'
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      obtain ⟨x, hx, hA⟩ := ih (by simp only [List.length_cons]; omega) hk'
      exact ⟨x, chainConsume_cons_noWrite hx hwr, aliasFacts_cons_fix hA hins hwr⟩
  | @load Γ w m ts a i k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hins⟩ := aliasStepO_bindOps_load nArgs Γ.length a i
      obtain ⟨ins', hb', hwr, -⟩ := bindOps_load nArgs Γ.length a i (fun _ _ => none) ao
      rw [hb] at hb'
      obtain rfl : ins = ins' := List.singleton_inj.mp hb'
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackLoad w m, rfl,
          .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      obtain ⟨x, hx, hA⟩ := ih (by simp only [List.length_cons]; omega) hk'
      exact ⟨x, chainConsume_cons_noWrite hx hwr, aliasFacts_cons_fix hA hins hwr⟩
  | @store Γ w m ts v i x k hk =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hins⟩ := aliasStepO_bindOps_store nArgs Γ.length v i x
      obtain ⟨ins', hb', hwr, hrd⟩ := bindOps_store nArgs Γ.length v i x (fun _ _ => none) ao
      rw [hb] at hb'
      obtain rfl : ins = ins' := List.singleton_inj.mp hb'
      have hrest := chainTail_export_alias (fn := fn) hao hk
        (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hrest
      obtain ⟨hF, -⟩ := chainTail_export (fn := fn) (aa := fun _ _ => none) (fun _ _ => rfl) hao hk
        (by simp only [List.length_cons]; omega) hk'
      have hcons := chainTail_export_consume (fn := fn) (aa := fun _ _ => none) (fun _ _ => rfl)
        hao hk (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hcons
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have hv := inScope_resolveVar (nArgs := nArgs) v
      have hnw : ∀ w', ¬ WrAt rk.code ao w' (regName Γ.length) := fun w' hw' => by
        have h1 := hF.2.1 w' _ hw'
        have := regName_injective h1
        simp only [List.length_cons] at this
        omega
      refine ⟨curName nArgs v, chainConsume_cons_store hcons ?_ hwr
        (fun h => hv.ne_regName le_rfl h.symm) (fun w' hw' => ?_),
        aliasFacts_cons_store hrest hins hwr hnw⟩
      · rw [hrd]
        exact List.mem_singleton_self _
      · have h1 := hF.2.1 w' _ hw'
        exact hv.ne_regName (by simp only [List.length_cons]; omega) h1
  | @ret Γ ts vs =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      refine ⟨"", ⟨fun w h => ?_, fun k d h => ?_, fun w r k d _ h => ?_⟩,
        fun M => ⟨fun w n h => ?_, fun n _ => rfl⟩⟩ <;>
        · obtain ⟨_, h, -⟩ := h
          simp at h

/-- **The store-chain shape of the export of a program of the shape `LoadsChain` under its
    coalescing renaming** `chainAlias`: reads follow writes, consumed names are dead, and the
    class of a written name is the chain, whose earlier versions are consumed. -/
theorem loadsChain_export_chainShape_alias (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) :
    ChainShape (X86Backend.ImageStraightRoute.chainAlias r.code) r.code (fun _ _ => none) ao
      (r.res.map JasminLsemWidthN.operandName) := by
  obtain ⟨x, hC, hA⟩ := loadsChain_export_consume_alias (fn := fn) hao h hn hr
  obtain ⟨h1, h2⟩ := loadsChain_export_chainShape₁₂ (fn := fn) (aa := fun _ _ => none)
    (fun _ _ => rfl) hao h hn hr
  refine ⟨h1, h2, chainShape₃_of_consume hC (fun w y hw => ?_) (fun y hy => ?_)⟩
  · change (r.code.foldl (aliasStepO []) {}).getD y y = x
    rw [(hA {}).1 w y hw]
    simp
  · change (r.code.foldl (aliasStepO []) {}).getD y y = y
    rw [(hA {}).2 y hy]
    simp
end ExportAlias

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
