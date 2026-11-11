/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCallShape

/-!
# Loads, then a chain of at least one store, on the field domain

The shape `LoadsChain` admits a program that returns without a store. The shape `LoadsChainS`
has the free, load and store cases of `LoadsChain` and no return case: loads and memory-free
bindings, then a first store whose result starts a `ChainTail`. A program of the shape writes
an array.

The templates of the field domain store every limb of the result, and a modulus of at least
`2` has at least one limb, so the blocks of a registered wide template have a first store
(`wideBlockOf_loadsChainS`). The passes from the splice of these blocks to the export keep the
store: a renaming, dead-binding elimination, the forwarding of loads, the select lowering, the
range stage, mask elimination, the carry pairs, the e-graph pass and the widening each map a
store of the chain to a store, and map the bindings before it to bindings before it.

## Main definitions

* `LoadsChainS`: loads and memory-free bindings, then a first store starting a chain tail.
* `LoadsThenStoresS`: a multi-result program of loads and memory-free bindings ending in a
  chain of at least one store of limbs.

## Main results

* `LoadsChainS.loadsChain`: the shape is a case of `LoadsChain`.
* `wideBlockOf_loadsChainS`: the body of a wide tagged call at a modulus of at least `2` has
  the shape.
* `loadsChainS_rename?`, `loadsChainS_dce`, `loadsChainS_seq?`, `loadsChainS_narrowPrep`,
  `loadsChainS_afterSplice`: the passes keep the shape.
* `fieldBodyD_loadsChainS`, `fieldDialectStep_loadsChainS`, `extChain_loadsChainS`: the field
  dialect step and the chain produce the shape.
* `fieldDom_legalize_loadsChainS`: the program the export receives on a member of the field
  domain has the shape.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree)
open Ctxt (Var)

/-! ## 1. The shape -/

/-- **Loads, then a chain of at least one store**, on a structured program: loads and
    memory-free bindings, then a first store, whose result starts a `ChainTail`. -/
inductive LoadsChainS : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Prop
  /-- A memory-free binding. -/
  | free {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
      (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts) :
      jMemFree e.op = true → LoadsChainS k → LoadsChainS (.var e k)
  /-- A load. -/
  | load {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
      (a : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64))
      (k : NFProg jasminDialect (.reg w :: Γ) ts) :
      LoadsChainS k → LoadsChainS (.var ⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ k)
  /-- The first store, whose result starts the chain. -/
  | store {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
      (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w))
      (k : NFProg jasminDialect (.stackArr w m :: Γ) ts) :
      ChainTail .here k →
        LoadsChainS (.var ⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ k)

/-- **A program of the shape `LoadsChainS` has the shape `LoadsChain`.** -/
theorem LoadsChainS.loadsChain {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) : LoadsChain p := by
  induction h with
  | free e k he _ ih => exact .free _ _ he ih
  | load a i k _ ih => exact .load _ _ _ ih
  | store v i x k hk => exact .store _ _ _ _ hk

/-! ## 2. The templates -/

section Template

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 MC bindK)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy loadLimbs loadArgs
  storeLimbs eLoad eStore)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (MemFree PrefixClosed
  lowerR_q exprBlock_memFree solinasExprBlock_memFree twistOp_coveredArith)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline

variable {n : Nat}

/-- **Loads, then a chain of at least one store**: a multi-result program built of loads
    `eLoad` of limbs and of memory-free bindings, ending in the chain of stores
    `storeLimbs (m + 1) j o h` of at least one limb into the array `o`. -/
inductive LoadsThenStoresS : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → MC Γ ts → Prop
  /-- The chain of at least one store into `o`. -/
  | stores {Γ : Ctxt jasminDialect} (m j : Nat) (o : Var Γ (arrTy n))
      (h : Ctxt.Hom (Mont.Rn (m + 1)) Γ) : LoadsThenStoresS (storeLimbs (m + 1) j o h)
  /-- A memory-free binding in front. -/
  | free {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
      (e : Expr jasminDialect Γ t) (k : MC (t :: Γ) ts) :
      jMemFree e.op = true → LoadsThenStoresS k → LoadsThenStoresS (.var e k)
  /-- A load of a limb in front. -/
  | load {Γ : Ctxt jasminDialect} {ts : List JasminTy} (a : Var Γ (arrTy n)) (i : Var Γ w64)
      (k : MC (w64 :: Γ) ts) : LoadsThenStoresS k → LoadsThenStoresS (.var (eLoad a i) k)

/-- The shape `LoadsThenStoresS` is closed under a memory-free binding in front. -/
theorem loadsThenStoresS_prefixClosed :
    PrefixClosed (fun {Γ} {ts} m => LoadsThenStoresS (n := n) (Γ := Γ) (ts := ts) m) :=
  fun e k he hk => .free e k he hk

/-- **The loads of limbs keep the shape `LoadsThenStoresS` of every continuation.** -/
theorem loadLimbs_loadsThenStoresS {bs : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (a : Var Δ (arrTy n))
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Mont.Rn m) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h, LoadsThenStoresS (n := n) (k r h)) →
      LoadsThenStoresS (n := n) (loadLimbs m j a k)
  | _, 0, _, _, _, hk => by rw [loadLimbs]; exact hk _ _
  | _, m + 1, j, a, _, hk => by
      rw [loadLimbs, bindK, bindK]
      exact .free _ _ rfl (.load _ _ _
        (loadLimbs_loadsThenStoresS m (j + 1) _ fun _ _ => hk _ _))

/-- **The loads of the limbs of every array keep the shape `LoadsThenStoresS` of every
    continuation.** -/
theorem loadArgs_loadsThenStoresS {bs : List JasminTy} :
    ∀ (Γ : Ctxt fieldDialect) {Δ : Ctxt jasminDialect}
      (src : Ctxt.Hom (FieldToJasminLimbs.arrCtx n Γ) Δ)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (MultiBlockLowering.ctxFlat (FieldToJasminLimbs.mapTysL n) Γ) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h, LoadsThenStoresS (n := n) (k r h)) →
      LoadsThenStoresS (n := n) (loadArgs Γ src k)
  | [], _, _, _, hk => by rw [loadArgs]; exact hk _ _
  | _ :: Γ, _, _, _, hk => by
      rw [loadArgs]
      exact loadLimbs_loadsThenStoresS _ _ _ fun _ _ =>
        loadArgs_loadsThenStoresS Γ _ fun _ _ => hk _ _

/-- **The lowered field program over word arrays of at least one limb loads, then stores at
    least once**, for a covered program whose blocks are memory-free. -/
theorem fieldBodyOf_loadsThenStoresS (lo : FieldToJasminLimbs.LimbBlocks n) (hn : 0 < n)
    {Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop}
    (hB : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t), Good e →
      MemFree ((FieldToJasminLimbs.loweringOf lo).exprBlock e))
    {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t)
    (hc : BlockLoweringCPS.CoveredCom Good c) :
    LoadsThenStoresS (n := n) (FieldToJasminLimbs.fieldBodyOf lo c) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [FieldToJasminLimbs.fieldBodyOf]
  exact loadArgs_loadsThenStoresS Γ _ fun _ _ =>
    lowerR_q loadsThenStoresS_prefixClosed _ hB _ c hc fun _ _ => .stores _ _ _ _

/-- **The blocks of a wide template load, then store at least once**: the block of every
    operation of `arithOpB p` is the head projection of a program of the shape
    `LoadsThenStoresS`. -/
def WideLoadsThenStoresS {p m : Nat} (W : WideTemplate p m) : Prop :=
  ∀ op : fieldDialect.Op, FieldLower.arithOpB p op = true →
    ∃ body : MC (FieldToJasminLimbs.arrCtx m (DialectSignature.sig op) ++ [arrTy m]) [arrTy m],
      @FieldLower.FieldLowerTemplate.block W.α m W.inst W.P op = body.toComHead
        ∧ LoadsThenStoresS (n := m) body

/-- The canonical Montgomery template of a record of at least one limb loads, then stores at
    least once. -/
theorem ofMont_loadsThenStoresS (P : LimbParams n) (hn : n < 2 ^ 64) (h0 : 0 < n) :
    WideLoadsThenStoresS (WideTemplate.ofMont P hn) := fun op hop =>
  ⟨FieldToJasminLimbs.fieldBodyOf (FieldToJasminLimbs.lowerOpL P) (twistOp n op),
    rfl, fieldBodyOf_loadsThenStoresS _ h0 (exprBlock_memFree P) _
      (twistOp_coveredArith P op hop)⟩

theorem castN_loadsThenStoresS {p m : Nat} (h : n = m) {W : WideTemplate p n}
    (hW : WideLoadsThenStoresS W) : WideLoadsThenStoresS (W.castN h) := by
  subst h
  exact hW

theorem castP_loadsThenStoresS {p q : Nat} (h : p = q)
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (hW : WideLoadsThenStoresS W) :
    WideLoadsThenStoresS (W.castP h) := by
  subst h
  exact hW

/-- The Solinas template of a record of at least one limb loads, then stores at least once. -/
theorem ofSolinasAt_loadsThenStoresS (S : Solinas.SolinasParams n)
    (hn : n = _root_.Hax.FieldTag.fieldLimbs (Solinas.p S)) (h64 : n < 2 ^ 64) (h0 : 0 < n) :
    WideLoadsThenStoresS (WideTemplate.ofSolinasAt S hn h64) := by
  refine castN_loadsThenStoresS hn fun op hop => ⟨FieldToJasminLimbs.fieldBodyOf
    (FieldToJasminLimbsSolinas.lowerOpL S) (FieldLower.opCom op), rfl,
    fieldBodyOf_loadsThenStoresS _ h0 (solinasExprBlock_memFree S) _
      (FieldLower.coveredCom_opCom (fun h => h) op hop)⟩

/-- A modulus of at least `2` has at least one limb. -/
theorem fieldLimbs_pos {p : Nat} (hp : 2 ≤ p) : 0 < _root_.Hax.FieldTag.fieldLimbs p := by
  have h := _root_.Hax.FieldTag.le_pow_fieldLimbs p
  rcases Nat.eq_zero_or_pos (_root_.Hax.FieldTag.fieldLimbs p) with h0 | h0
  · rw [h0] at h
    simp at h
    omega
  · exact h0

/-- **The blocks of a registered wide template at a modulus of at least `2` load, then store
    at least once.** -/
theorem wideTemplateOf_loadsThenStoresS {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W)
    (hp : 2 ≤ p) : WideLoadsThenStoresS W := by
  rcases wideTemplateOf_cases h with ⟨_, S, hn, h64, hp', rfl⟩ | ⟨_, _, _, rfl⟩
  · refine castP_loadsThenStoresS hp' (ofSolinasAt_loadsThenStoresS S hn h64 ?_)
    rw [hn, hp']
    exact fieldLimbs_pos hp
  · exact ofMont_loadsThenStoresS _ _ (fieldLimbs_pos hp)

/-- The chain of at least one store `storeLimbs (m + 1)`, renamed and embedded, has the shape
    `LoadsChainS`. -/
theorem storeLimbs_loadsChainS {Δ Γ' : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy n))
    (h : Ctxt.Hom (Mont.Rn (m + 1)) Δ) (f : Ctxt.Hom Δ Γ') :
    LoadsChainS (NFProg.ofCom (Com.rename f (storeLimbs (m + 1) j o h).toComHead)) := by
  rw [storeLimbs, bindK, bindK, ofCom_rename_toComHead_var, ofCom_rename_toComHead_var]
  exact .free _ _ rfl (.store _ _ _ _
    (lift_here_chainTail _ (storeLimbs_chainTail m (j + 1) Var.here _
      (Ctxt.Hom.lift (Ctxt.Hom.lift f)))))

/-- **The head projection of a program that loads, then stores at least once, renamed and
    embedded as a structured program, has the shape `LoadsChainS`.** -/
theorem loadsChainS_of_loadsThenStoresS : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    {ts : List JasminTy} {body : MC Γ (t :: ts)}, LoadsThenStoresS (n := n) body →
    ∀ {Γ' : Ctxt jasminDialect} (f : Ctxt.Hom Γ Γ'),
      LoadsChainS (NFProg.ofCom (Com.rename f body.toComHead))
  | _, _, _, _, .stores m j o h, _, f => storeLimbs_loadsChainS m j o h f
  | _, _, _, _, .free _ _ he hk, _, f => by
      rw [ofCom_rename_toComHead_var]
      exact .free _ _ he (loadsChainS_of_loadsThenStoresS hk f.lift)
  | _, _, _, _, .load _ _ _ hk, _, f => by
      rw [ofCom_rename_toComHead_var]
      exact .load _ _ _ (loadsChainS_of_loadsThenStoresS hk f.lift)

/-- **The body of a wide tagged call at a modulus of at least `2` loads, then stores at least
    once**: `wideBlockOf W m` has the shape `LoadsChainS`. -/
theorem wideBlockOf_loadsChainS {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W)
    (hp : 2 ≤ p) (m : _root_.Hax.FieldTag.FieldMethod) : LoadsChainS (wideBlockOf W m) := by
  obtain ⟨body, hb, hs⟩ := wideTemplateOf_loadsThenStoresS h hp (fieldOpOf m p)
    (arithOpB_fieldOpOf m p)
  unfold wideBlockOf templateCall
  exact (congrArg (fun c => LoadsChainS (NFProg.ofCom (Com.rename _ c))) hb).mpr
    (loadsChainS_of_loadsThenStoresS hs _)

end Template

/-! ## 3. The passes -/

/-- **A partial renaming keeps the shape `LoadsChainS`.** -/
theorem loadsChainS_rename? {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) :
    ∀ {Δ : Ctxt jasminDialect} {f : PRen Γ Δ} {p' : NFProg jasminDialect Δ ts},
      NFProg.rename? f p = some p' → LoadsChainS p' := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ f p' hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      exact .free _ _ ((rename?_op he').symm ▸ he) (ih hk')
  | @load Γ w m ts a i k hk ih =>
      intro Δ f p' hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      obtain ⟨a', i', rfl⟩ := rename?_load f a i he'
      exact .load _ _ _ (ih hk')
  | @store Γ w m ts v i x k hk =>
      intro Δ f p' hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      obtain ⟨v', i', x', -, rfl⟩ := rename?_store f v i x he'
      exact .store _ _ _ _ (chainTail_rename? hk rfl hk')

/-- **Dead-binding elimination keeps the shape `LoadsChainS`.** -/
theorem loadsChainS_dce {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) : LoadsChainS (NFProg.dce p) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact loadsChainS_rename? ih hr
      · exact .free _ _ he ih
  | @load Γ w m ts a i k hk ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact loadsChainS_rename? ih hr
      · exact .load _ _ _ ih
  | @store Γ w m ts v i x k hk =>
      have hk' := chainTail_dce hk
      have hn : NFProg.rename? PRen.drop (NFProg.dce k) = none :=
        rename?_chainTail_none hk' (by simp [PRen.drop])
      simp only [NFProg.dce, hn]
      exact .store _ _ _ _ hk'

/-- **The forwarding of loads keeps the shape `LoadsChainS`**, at every facts and renaming. -/
theorem loadsChainS_fwdLoad1Go {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) :
    ∀ {Δ : Ctxt jasminDialect} (K : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ),
      LoadsChainS (NFFwdLoad1.fwdLoad1Go p K ren) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih _ _
        · exact .free _ _ he (ih _ _)
      · exact .free _ _ he (ih _ _)
  | @load Γ w m ts a i k hk ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih _ _
        · exact .load _ _ _ (ih _ _)
      · exact .load _ _ _ (ih _ _)
  | @store Γ w m ts v i x k hk =>
      intro Δ K ren
      exact .store _ _ _ _ (chainTail_fwdLoad1Go hk _ (Ctxt.Hom.lift ren))

/-- **The splice of a body of the shape `LoadsChainS` before a continuation that continues
    the chain of its result** has the shape `LoadsChainS`. -/
theorem loadsChainS_seq? : ∀ {Δ : Ctxt jasminDialect} {w m : Nat}
    {b : NFProg jasminDialect Δ [.stackArr w m]}, LoadsChainS b →
    ∀ {Γ₀ : Ctxt jasminDialect} {ts : List JasminTy}
      {k : NFProg jasminDialect (.stackArr w m :: Γ₀) ts}, ChainTail .here k →
    ∀ {Γ : Ctxt jasminDialect} {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg jasminDialect Γ ts},
      NFProg.seq? k b ρ θ = some q → LoadsChainS q
  | _, _, _, _, .free e b he hb, _, _, k, hk, _, ρ, θ, q, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      exact .free _ _ ((rename?_op he').symm ▸ he) (loadsChainS_seq? hb hk hq')
  | _, _, _, _, .load a i b hb, _, _, k, hk, _, ρ, θ, q, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain ⟨a', i', rfl⟩ := rename?_load ρ a i he'
      exact .load _ _ _ (loadsChainS_seq? hb hk hq')
  | _, _, _, _, .store v i x b hb, _, _, k, hk, _, ρ, θ, q, hq => by
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he', q', hq', rfl⟩ := hq
      obtain ⟨v', i', x', -, rfl⟩ := rename?_store ρ v i x he'
      exact .store _ _ _ _ (chainTail_seq? (v' := .here) hb hk rfl hq')

/-- **The select lowering keeps the shape `LoadsChainS`**, along every renaming. -/
theorem loadsChainS_lowerSel {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ), LoadsChainS (NFProg.lowerSel p ren) := by
  induction h with
  | free e k he hk ih => intro Δ ren; exact .free _ _ he (ih _)
  | load a i k hk ih => intro Δ ren; exact .load _ _ _ (ih _)
  | store v i x k hk =>
      intro Δ ren
      exact .store _ _ _ _ (chainTail_lowerSel hk (Ctxt.Hom.lift ren))

section Range

open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (rangeExpr)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop (carriedGo loopRange)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (AEnv)

/-- **The traversal of the range stage keeps the shape `LoadsChainS`**, at every
    annotation. -/
theorem loadsChainS_carriedGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) :
    ∀ (A : AEnv Γ) (len : Nat) (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn),
      LoadsChainS (carriedGo A len a p) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro A len a
      simp only [carriedGo]
      rcases rangeExpr_eq_or_memFree A len e with h | h
      · rw [h]
        exact .free _ _ he (ih _ _ _)
      · exact .free _ _ h (ih _ _ _)
  | @load Γ w m ts a i k hk ih =>
      intro A len an
      simp only [carriedGo]
      rcases rangeExpr_eq_or_memFree A len
        (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) with h | h
      · rw [h]
        exact .load _ _ _ (ih _ _ _)
      · exact .free _ _ h (ih _ _ _)
  | @store Γ w m ts v i x k hk =>
      intro A len a
      simp only [carriedGo]
      exact .store _ _ _ _ (chainTail_carriedGo hk _ _ _)

end Range

section Narrow

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

/-- **Mask elimination keeps the shape `LoadsChainS`**, at every facts and renaming. -/
theorem loadsChainS_maskElimGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ),
      LoadsChainS (maskElimGo p A ren) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ A ren
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _
        · exact .free _ _ he (ih _ _)
      · exact .free _ _ he (ih _ _)
  | @load Γ w m ts a i k hk ih =>
      intro Δ A ren
      exact .load _ _ _ (ih _ _)
  | @store Γ w m ts v i x k hk =>
      intro Δ A ren
      exact .store _ _ _ _ (chainTail_maskElimGo hk _ (Ctxt.Hom.lift ren) _ rfl)

/-- **The insertion of a data binding before a carry-out keeps the shape `LoadsChainS`.** -/
theorem loadsChainS_carryInsert {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {t : JasminTy} (w : Nat) (h : DialectSignature.ret (d := jasminDialect) (.addCarryHi w) = t)
    (args : HVector (fun t => Var Γ t)
      (DialectSignature.sig (d := jasminDialect) (.addCarryHi w)))
    {k : NFProg jasminDialect (t :: Γ) ts} (hk : LoadsChainS k) :
    LoadsChainS (carryInsert w h args k) := by
  unfold carryInsert
  split
  · rename_i e' k' he hk'
    exact .free _ _ rfl (.free _ _ ((rename?_op he).symm ▸ rfl) (loadsChainS_rename? hk hk'))
  · exact .free _ _ (by subst h; rfl) hk

/-- **The carry pairs keep the shape `LoadsChainS`**, at every key of the binding before. -/
theorem loadsChainS_carryPairGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) :
    ∀ prev : Option (Nat × List Nat), LoadsChainS (carryPairGo prev p) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro prev
      unfold carryPairGo
      split
      · split
        · exact .free _ _ he (ih _)
        · exact loadsChainS_carryInsert _ _ _ (ih _)
      · exact .free _ _ he (ih _)
  | @load Γ w m ts a i k hk ih =>
      intro prev
      exact .load _ _ _ (ih _)
  | @store Γ w m ts v i x k hk =>
      intro prev
      exact .store _ _ _ _ (chainTail_carryPairGo hk _)

end Narrow

section Aegraph

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (nfGo aegraphOptNF)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)

/-- The free and load cases of `loadsChainS_nfGo`. -/
theorem loadsChainS_nfGo_var {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom (t :: Γ) Δ) S,
      LoadsChainS (nfGo jasminRules ρ S k))
    (he : ∀ {Θ : Ctxt jasminDialect} (k' : NFProg jasminDialect (t :: Θ) ts) (ρ : Ctxt.Hom Γ Θ),
      LoadsChainS k' → LoadsChainS (.var (e.rename ρ) k'))
    (ρ : Ctxt.Hom Γ Δ) (S : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.Tbl jasminDialect ×
      CatCrypt.Crypto.Optimizer.Rewrite.Aegraph.Defs) :
    LoadsChainS (nfGo jasminRules ρ S (.var e k)) := by
  simp only [nfGo]
  have hc := choose_cases S (e.rename ρ)
  split
  · exact hk _ _
  · rename_i e2 he2
    rw [he2] at hc
    rcases hc with ⟨_, hc⟩ | hc | hc
    · cases hc
    · cases hc
      exact he _ _ (hk _ _)
    · exact .free _ _ hc (hk _ _)
  · rename_i e1 e2 he2
    rw [he2] at hc
    rcases hc with ⟨_, hc⟩ | hc | hc
    · cases hc
    · cases hc
    · exact .free _ _ hc.1 (.free _ _ hc.2 (hk _ _))

/-- **The e-graph traversal keeps the shape `LoadsChainS`**, along every renaming and
    state. -/
theorem loadsChainS_nfGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) :
    ∀ {Δ : Ctxt jasminDialect} (ρ : Ctxt.Hom Γ Δ) S, LoadsChainS (nfGo jasminRules ρ S p) := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ ρ S
      exact loadsChainS_nfGo_var e k ih (fun _ _ hk' => .free _ _ he hk') ρ S
  | @load Γ w m ts a i k hk ih =>
      intro Δ ρ S
      exact loadsChainS_nfGo_var ⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ k ih
        (fun _ ρ' hk' => .load (ρ' a) (ρ' i) _ hk') ρ S
  | @store Γ w m ts v i x k hk =>
      intro Δ ρ S
      simp only [nfGo]
      rw [show Expr.rename ρ (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
          Expr jasminDialect Γ (.stackArr w m)) =
          ⟨.stackStore w m, rfl, .cons (ρ v) (.cons (ρ i) (.cons (ρ x) .nil))⟩ from rfl,
        choose_store]
      exact .store _ _ _ _ (chainTail_nfGo hk (Ctxt.Hom.lift ρ) _ _ rfl)

end Aegraph

section Widen

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

/-- **The splice of a block of memory-free operations before continuations of the shape
    `LoadsChainS`** has the shape. -/
theorem loadsChainS_spliceNF? {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (K : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)),
      ComFree blk →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), K ren' res = some q' → LoadsChainS q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk K = some q → LoadsChainS q
  | _, _, .ret v, K, _, hK, _, h => hK _ v _ h
  | _, _, .var e blk, K, .var _ _ he hb, hK, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .free _ _ he (loadsChainS_spliceNF? blk _ hb
        (fun ren' res q'' hq => hK _ res q'' hq) hq')

/-- **The widening keeps the shape `LoadsChainS`**, along every renaming. -/
theorem loadsChainS_widen {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (widenP.mapCtx Γ) Δ)
      {q : NFProg jasminDialect Δ (ts.map widenP.mapTy)},
      NFProg.map? widenP widenP_regionTypes p ren = some q → LoadsChainS q := by
  induction h with
  | @free Γ t ts e k he hk ih =>
      intro Δ ren q hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      rcases e with ⟨op, rfl, args⟩
      exact loadsChainS_spliceNF? _ _ (comFree_rename (comFree_wideOpBlock? op args he hblk) ren)
        (fun ren' res q' hq' => ih _ hq') hq
  | @load Γ w m ts a i k hk ih =>
      intro Δ ren q hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.stackLoad (wideW w) m, rfl,
          .cons (mapVar a) (.cons (mapVar i) .nil)⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .load _ _ _ (ih _ hq')
  | @store Γ w m ts v i x k hk =>
      intro Δ ren q hq
      rw [NFProg.map?, Option.bind_eq_some_iff] at hq
      obtain ⟨blk, hblk, hq⟩ := hq
      obtain rfl : blk = one ⟨.stackStore (wideW w) m, rfl,
          .cons (mapVar v) (.cons (mapVar i) (.cons (mapVar x) .nil))⟩ :=
        Option.some.inj (hblk.symm.trans rfl)
      obtain ⟨q', hq', rfl⟩ :=
        Option.map_eq_some_iff.mp ((spliceNF?_rename_one ren _ _).symm.trans hq)
      exact .store _ _ _ _ (chainTail_widen hk _ .here rfl hq')

/-- **The narrow-word stages keep the shape `LoadsChainS`.** -/
theorem loadsChainS_narrowPrep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (h : LoadsChainS p) (hq : narrowPrep p = some q) : LoadsChainS q := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  exact loadsChainS_carryPairGo (loadsChainS_dce (loadsChainS_maskElimGo
    (loadsChainS_widen h _ h₀) _ _)) _

end Widen

section Steps

open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (lowerSelectsStep aegraphStep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)

/-- **The end of the lowering of a raised body keeps the shape `LoadsChainS`.** -/
theorem loadsChainS_lowerBodyTail {as rs : List JasminTy} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (hΓ : Γ = as) (hts : ts = rs) {r : NFProg jasminDialect Γ ts}
    (h : LoadsChainS r) :
    LoadsChainS (NFProg.dce (NFFwdLoad1.fwdLoad1 (FieldDialectStep.castNF hΓ hts r))) := by
  subst hΓ hts
  exact loadsChainS_dce (loadsChainS_fwdLoad1Go h _ _)

/-- **The steps after the field dialect step, the narrow-word stages and the legalisation keep
    the shape `LoadsChainS`.** -/
theorem loadsChainS_afterSplice {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p p₁ p₂ p₃ : NFProg jasminDialect Γ [t]}
    {q : NFProg jasminDialect (Γ.map NarrowWords.wideTy) [NarrowWords.wideTy t]}
    (h : LoadsChainS p) (h₁ : (lowerSelectsStep Γ [t]).run p = some p₁)
    (h₂ : (synRangeStep Γ [t]).run p₁ = some p₂)
    (h₃ : (aegraphStep jasminRules Γ [t]).run p₂ = some p₃)
    (hq : NarrowWords.narrowPrep p₃ = some q) : LoadsChainS (legalizeRegion q) := by
  cases h₁
  cases h₂
  cases h₃
  exact loadsChainS_narrowPrep (loadsChainS_nfGo (loadsChainS_carriedGo
    (loadsChainS_lowerSel h _) _ _ _) _ _) hq

end Steps

/-! ## 4. The splice of the template blocks -/

/-- **A renamed block whose embedding has the shape `LoadsChainS`** has the shape. -/
theorem loadsChainS_ofCom_rename : ∀ {Γ Γ' : Ctxt jasminDialect} {a : JasminTy}
    (c : Com jasminDialect Γ a) (f : Ctxt.Hom Γ Γ'),
    LoadsChainS (NFProg.ofCom c) → LoadsChainS (NFProg.ofCom (c.rename f))
  | _, _, _, .ret _, _, h => by
      change LoadsChainS (.ret _) at h
      cases h
  | _, _, _, .var e c, f, h => by
      change LoadsChainS (.var e (NFProg.ofCom c)) at h
      change LoadsChainS (.var (e.rename f) (NFProg.ofCom (c.rename f.lift)))
      have ih := fun h' => loadsChainS_ofCom_rename c f.lift h'
      cases h with
      | free _ _ he hb => exact .free _ _ he (ih hb)
      | load a i _ hb => exact .load (f a) (f i) _ (ih hb)
      | store _ i x _ hb =>
          have h2 := chainTail_ofCom_rename c .here f.lift hb
          exact .store _ (f i) (f x) _ (lift_here_chainTail f h2)

/-- **The splice of a block whose embedding has the shape `LoadsChainS`**, before
    continuations that continue the chain at the returned version, has the shape
    `LoadsChainS`. -/
theorem loadsChainS_spliceNF?_ofCom {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (K : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)),
      LoadsChainS (NFProg.ofCom blk) →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), K ren' res = some q' → ChainTailAt res q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk K = some q → LoadsChainS q
  | _, _, .ret _, _, h, _, _, _ => by
      change LoadsChainS (.ret _) at h
      cases h
  | _, _, .var e blk, K, h, hK, _, hq => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      change LoadsChainS (.var e (NFProg.ofCom blk)) at h
      have ih := fun h' => loadsChainS_spliceNF?_ofCom blk _ h'
        (fun ren' res q'' hq'' => hK _ res q'' hq'') hq'
      cases h with
      | free _ _ he hb => exact .free _ _ he (ih hb)
      | load a i _ hb => exact .load _ _ _ (ih hb)
      | store v i x _ hb =>
          have h2 : ChainTail .here q' := chainTail_spliceNF?_ofCom blk _ .here hb
            (fun ren' res q'' hq'' => hK _ res q'' hq'') hq'
          exact .store _ _ _ _ h2

section Template

open CatCrypt.Crypto.SecureCompilation.Algebraic (ModArithLimbTemplate)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.ModArithLimbs (canonTemplateOf ofWide optTy
  ofWordsBlock? toWordsBlock? bodyBlock?)
open _root_.Hax.FieldTag (fieldLimbs)

/-- **The block of a method of the wide template at a modulus of at least `2` has the shape
    `LoadsChainS`.** -/
theorem bodyBlock?_wide_loadsChainS {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    {hw : wideTemplateOf p = some W} (hp : 2 ≤ p) {Δ : Ctxt jasminDialect}
    (o : Option (ModArithLimbTemplate p .canon)) (ho : o = some (ofWide W hw))
    (m : _root_.Hax.FieldTag.FieldMethod)
    (args : HVector (fun t => Var Δ t)
      (Algebraic.ModArithLimbTemplate.limbSig (ModArithLimbs.optTy o) m))
    {blk : Com jasminDialect Δ (optTy o)} (hb : bodyBlock? o m args = some blk) :
    LoadsChainS (NFProg.ofCom blk) := by
  subst ho
  cases hb
  refine loadsChainS_ofCom_rename (ModArithLimbs.wideLimbBody W m) _ ?_
  rw [← ModArithLimbs.wideBlockOf_eq]
  exact wideBlockOf_loadsChainS hw hp m

set_option hygiene false in
/-- The splice of a cast block from words of the wide template. -/
local macro "cast_in_tacS" : tactic => `(tactic| (
  obtain ⟨b, hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  refine loadsChainS_spliceNF? _ _ (comFree_rename (ofWordsBlock?_wide_comFree _ hc _ _ _ hb) _)
    (fun ren' res q' hq' => ?_) hq'))

set_option hygiene false in
/-- The splice of the block of a method of the wide template before the cast to words and the
    return. -/
local macro "op_tail_tacS" : tactic => `(tactic| (
  obtain ⟨b, hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  have h3 : LoadsChainS (NFProg.ofCom b) := by
    simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?, Expr.rename,
      ModArithLimbs.limbOpBlock?, ModArithLimbs.modBlock?] at hb
    first
      | exact bodyBlock?_wide_loadsChainS hp _ hc _ _ hb
      | (split at hb <;> exact bodyBlock?_wide_loadsChainS hp _ hc _ _ hb)
  refine loadsChainS_spliceNF?_ofCom _ _ (loadsChainS_ofCom_rename _ _ h3)
    (fun ren' res q' hq' => ?_) hq'
  obtain ⟨b4, hb4, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?, Expr.rename,
    ModArithLimbs.limbOpBlock?, ModArithLimbs.limbCastBlock?] at hb4
  obtain ⟨h4, rfl⟩ := toWordsBlock?_wide_ret _ hc _ _ _ hb4
  simp only [Com.rename, NFProg.spliceNF?, Option.some.injEq] at hq'
  subst hq'
  exact chainTailAt_ret res _ h4 (hom_cast (ModArithLimbs.modArithLimbsJ.bodyHom _ _ res) h4 _)))

/-- **The raised body on arrays, lowered to `mod_arith` and to the wide template at a modulus
    of at least `2`, has the shape `LoadsChainS`.** -/
theorem lowerArr_loadsChainS {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) (hp : 2 ≤ p)
    (m : _root_.Hax.FieldTag.FieldMethod) {r₂ r₃}
    (h : NFProg.map? FieldToModArithChain.fieldToModArithJ FieldToModArithChain.regionTypes
      (FieldRaise.arrBody m p (fieldLimbs p)) (fun v => v) = some r₂)
    (h₃ : NFProg.map? ModArithLimbs.modArithLimbsJ ModArithLimbs.modArithLimbsJ_regionTypes r₂
      (fun v => v) = some r₃) : LoadsChainS r₃ := by
  have hc := canonTemplateOf_wide hn hw
  cases m <;>
  simp only [NFProg.map?, FieldRaise.arrBody, FieldRaise.arrBody2, FieldRaise.arrBody1,
    FieldToModArithChain.fieldToModArithJ,
    FieldToModArithChain.lowerBlock?, FieldToModArithChain.opBlock?, FieldRaise.fromE,
    FieldRaise.toE, FieldRaise.opE, FieldToModArithChain.castBlock?, FieldToModArithChain.pfBlock?,
    FieldChainDialect.FieldRepr.Admits, ↓reduceIte, Option.bind_some, FieldToModArithChain.opB,
    Com.rename, NFProg.spliceNF?, Option.map_some] at h <;>
  obtain rfl := Option.some.inj h <;>
  have hq' := h₃ <;>
  simp only [NFProg.map?] at hq'
  · cast_in_tacS; cast_in_tacS; op_tail_tacS
  · cast_in_tacS; cast_in_tacS; op_tail_tacS
  · cast_in_tacS; cast_in_tacS; op_tail_tacS
  · cast_in_tacS; op_tail_tacS
  · cast_in_tacS; op_tail_tacS
  · cast_in_tacS; op_tail_tacS

/-- **The lowered body of a tagged head at a modulus of at least `2` without a narrow
    representation and with a wide template has the shape `LoadsChainS`.** -/
theorem fieldBodyD_loadsChainS {f : String} {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : _root_.Hax.FieldTag.fieldTag? f = some (m, p))
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) (hp : 2 ≤ p)
    {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : FieldDialectStep.fieldBodyD f as rs = some b) :
    LoadsChainS b := by
  obtain ⟨-, r₁, hr₁, hb⟩ := FieldDialectStep.fieldBodyD_some hb
  unfold FieldRaise.raiseBody at hr₁
  rw [ht] at hr₁
  simp only [hn, hw] at hr₁
  unfold FieldRaise.raiseArr at hr₁
  split at hr₁
  · rename_i hs
    obtain ⟨has, hrs⟩ := hs
    obtain rfl := List.map_injective_iff.mpr Sum.inl_injective has
    obtain rfl : rs = [JasminTy.stackArr 64 (fieldLimbs p)] :=
      List.map_injective_iff.mpr Sum.inl_injective (hrs.trans rfl)
    cases hr₁
    obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact loadsChainS_lowerBodyTail _ _ (lowerArr_loadsChainS hn hw hp m hs₂ hs₃)
  · cases hr₁

end Template

/-! ## 5. The chain on the field domain -/

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.Hax.ImpToNF (entryEnv NfEnv)
open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag? fieldLimbs)
open CatCrypt.Crypto.Hax.NFToCat (quietCall TRd catOp)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps (callsLoopsAll)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (opsNB)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (lowerSelectsStep aegraphStep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Hax.NFToCat (catTy nfToCatExt nfToCatExt_calls)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag? fieldLimbs)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)

/-- **The field dialect step takes one call of a tagged head at a modulus of at least `2`
    without a narrow representation and with a wide template, returned, to a program of the
    shape `LoadsChainS`.** -/
theorem fieldDialectStep_loadsChainS {f : String} {m : FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : fieldTag? f = some (m, p))
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) (hp2 : 2 ≤ p)
    {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p₀ q : NFProg jasminDialect Γ [t]} (hp : CallRet f p₀)
    (hq : (FieldDialectStep.fieldDialectStep Γ [t]).run p₀ = some q) : LoadsChainS q := by
  obtain ⟨as, args, rfl⟩ := hp
  have hf := _root_.Hax.FieldTag.fieldHeadB_of_fieldTag? ht
  change (if fieldFree (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil))) then
      some (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil))) else
    (NFProg.inline? FieldDialectStep.fieldLibD
      (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil)))).bind fun q =>
        if fieldFree q then some q else none) = some q at hq
  simp only [fieldFree, hf, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hq
  obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hq
  simp only [NFProg.inline?, Option.bind_some] at hq0
  split at hq0
  · rename_i b hb
    have ht' := fieldBodyD_rs ht hn hw hb
    obtain rfl : t = .stackArr 64 (fieldLimbs p) := List.head_eq_of_cons_eq ht'
    have hbl := fieldBodyD_loadsChainS ht hn hw hp2 hb
    split at hif
    · cases hif
      exact loadsChainS_seq? hbl (.ret _) hq0
    · cases hif
  · cases hq0
    simp only [fieldFree, hf, Bool.not_true, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte] at hif
    cases hif

open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps (callsLoopsAll)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (opsNB)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (lowerSelectsStep aegraphStep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Hax.NFToCat (catTy nfToCatExt nfToCatExt_calls)

/-- **The chain takes one call of a tagged head at a modulus of at least `2 ^ 64` with a wide
    template, bound and returned, to a program of the shape `LoadsChainS`.** -/
theorem extChain_loadsChainS {Γ : Ctxt nfDialect} {m : FieldMethod} {p : Nat}
    (ht : fieldTag? (fieldHead m p) = some (m, p)) (h64 : 2 ^ 64 ≤ p)
    (hW : (wideTemplateOf p).isSome = true)
    {p₀ : NFProg nfDialect Γ [NfTy.arr (fieldLimbs p) (.word 64)]}
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy (NfTy.arr (fieldLimbs p) (.word 64)))]}
    (h : (extChain [] Γ (NfTy.arr (fieldLimbs p) (.word 64))).run p₀ = some q)
    (hp : opsNB wideOpB p₀ = true)
    (hs : OpRet (NfOp.named "t" (.call (fieldHead m p)
      [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)]
      (NfTy.arr (fieldLimbs p) (.word 64)))) p₀) : LoadsChainS q := by
  obtain ⟨W, hw⟩ := Option.isSome_iff_exists.mp hW
  have hn : narrowFieldOf p = none := by
    cases hN : narrowFieldOf p with
    | none => rfl
    | some F =>
        have := (narrowFieldOf_spec hN).2.1
        omega
  have htag : (fieldTag? (fieldHead m p)).isSome = true := by rw [ht]; rfl
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3, r, hr, r1, hr1, j, hj, j1, hj1, j2, hj2, j3, hj3,
    j4, hj4, j5, hj5, hq⟩ := h
  obtain rfl := Option.some.inj hq
  change some (NFProg.abortElim NfOp.isAbort p₀) = some p0 at hp0
  cases hp0
  change flatSame (NFProg.abortElim NfOp.isAbort p₀) = some p1 at hp1
  change (if outTyB (NfTy.arr (fieldLimbs p) (.word 64)) then some p1 else none) = some p2 at hp2
  change some (NFProg.dce p2) = some p3 at hp3
  change nfToCatExt (fieldDeclsFor [] p3) p3 TRd.id = some r at hr
  have hp2' : p1 = p2 := by split at hp2 <;> cases hp2; rfl
  subst hp2'
  cases hp3; cases hr1; cases hj1
  have hab : NFProg.abortFree NfOp.isAbort p₀ = true :=
    FrontComplete.abortFree_of_opsNB (fun o ho => by
      simp only [wideOpB, Bool.and_eq_true, Bool.not_eq_true'] at ho
      exact ho.1) p₀ hp
  rw [NFProg.abortElim_of_abortFree _ p₀ hab] at hp1
  -- the montify pass is the identity, as in `extChain_callFree_of_wide`
  have hf : opsNB (fun o => !NFFlattenTuples.opIsTuple o && wideOpB o) p1 = true :=
    FrontComplete.opsNB_flatSame (W := fun _ => false) (fun _ h => h) hp1
      (FrontComplete.opsNB_mono_loop (fun o h => by simp [h]) (fun _ h => h) _ hp)
  have hd : opsNB wideOpB p1.dce = true :=
    FrontComplete.opsNB_dce _ (FrontComplete.opsNB_mono_loop
      (fun o h => by simp only [Bool.and_eq_true] at h; exact h.2) (fun _ h => h) _ hf)
  have hD : ∀ d ∈ fieldDeclsFor [] p1.dce, wideTagB d.name = true := by
    intro d hd'
    simp only [fieldDeclsFor, List.filter_nil, List.nil_append] at hd'
    exact fieldDeclsOf_wide _ hd d hd'
  have h0 : callsLoopsAll (fun f _ _ => wideTagB f) (fun _ => true) r = true :=
    ExportChainOps.callsLoopsAll_of_loops _ _ r (ExportChainOps.callsLoopsAll_true r)
      fun f as rs hc => by
        obtain ⟨d, hd', rfl, -⟩ := nfToCatExt_calls _ _ TRd.id r hr f as rs hc
        exact hD d hd'
  have h1 := (ExportChainOps.callsLoopsAll_nfGo (d := CatCryptDialect.catCryptDialect) _ _
    catRules (Ctxt.Hom.id _) (∅, ∅) r).trans h0
  have h2 := ExportChainOps.callsLoopsAll_map? catToJasmin catToJasmin_regionTypes
    (fun f _ _ => wideTagB f) (fun _ => true) _ h1 _ hj
  have hm := montifyPass_of_wideTag (Γ := mapCtx (List.map catTy Γ))
    (ts := [mapTy (catTy (NfTy.arr (fieldLimbs p) (.word 64)))]) j h2
  rw [hm] at hj2
  -- the shape through the steps
  obtain ⟨hh, args, hpe⟩ := hs
  rw [hpe] at hp1
  have g1 := flatSame_callRet hp1
  have g2 := nfToCatExt_callRet _ htag (dce_opRet g1) hr
  have g3 := map?_catToJasmin_callRet (aegraphOptNF_callRet g2) _ hj
  have hp2 : 2 ≤ p := le_trans (Nat.one_lt_two_pow (by decide : (64 : Nat) ≠ 0)) h64
  have g4 := fieldDialectStep_loadsChainS ht hn hw hp2 g3 hj2
  cases hj3
  cases hj4
  cases hj5
  exact loadsChainS_nfGo (loadsChainS_carriedGo (loadsChainS_lowerSel g4 _) _ _ _) _ _

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

/-- **The output of the chain on a member of the field domain has the shape `LoadsChainS`.** -/
theorem fieldDom_chain_loadsChainS {e : _root_.Hax.TExpr} {σ : AbiLayout} {t : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t]} (h : fieldDomB e σ = true)
    (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t, q⟩) : LoadsChainS q := by
  obtain ⟨T, p0, hp, hops⟩ := fieldDom_haxToNF h
  obtain ⟨m, p, ht, h64, hW, hT, hs⟩ := fieldDom_haxToNF_opRet h hp
  subst hT
  simp only [NFEntry.chainNF, haxEntry, hp, Option.bind_some, Option.map_eq_some_iff] at hq
  obtain ⟨q', hq', heq⟩ := hq
  cases heq
  rw [linkedDecls_single] at hq'
  exact extChain_loadsChainS ht h64 hW hq' hops hs

/-- **The program the export receives on a member of the field domain has the shape
    `LoadsChainS`**: the narrow-word stages and the legalisation keep the shape of the output of
    the chain. -/
theorem fieldDom_legalize_loadsChainS {e : _root_.Hax.TExpr} {σ : AbiLayout} {t0 : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t0]}
    {q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]}
    (h : fieldDomB e σ = true) (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩)
    (hq' : NarrowWords.narrowPrep q = some q') : LoadsChainS (legalizeRegion q') :=
  loadsChainS_narrowPrep (fieldDom_chain_loadsChainS h hq) hq'

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
