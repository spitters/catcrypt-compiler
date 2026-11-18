/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFoldPosBack
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomInputAcc

/-!
# The tags and the scalar operands of the accesses on the field domain

The region code of a member of the field domain is the webs of the export of a program of the
shape `LoadsChainS` over the context `(nfCtx σ).map wideTy` of the field layout. Every entry of
that context is an array of `n` `64`-bit words, and the program binds no array of a new type: a
memory-free binding is of a register type (`memFree_bind`), and a store returns the type of the
array it stores into. The export takes the tag of a load or a store from the type of its array
variable (`bindOps_load_eq`, `bindOps_store_eq`), and the webs keep the tags (`renArr_snd`).

A variable resolves to a parameter name `argName j` only at a slot of the context of the
layout, so a variable of a register type resolves to no parameter name there
(`curName_ne_argName_of_reg`). The destination of an exported load is a slot name `regName d`,
and the index and the stored value are names of register variables; the webs rename only the
base of a load and the destination and the base of a store.

## Main definitions

* `ArrLen`: every array type of a context is of `n` `64`-bit words.
* `AccShape`: an access is at the tag of `n` `64`-bit words, and its scalar operands are no
  parameter names.

## Main results

* `curName_ne_argName_of_reg`: a variable of a register type resolves to no parameter name
  when the parameters of the context are arrays.
* `loadsChainS_export_accShape`: the export of a program of the shape `LoadsChainS` has the
  access shape.
* `fieldDom_accTag`: on the field domain, every load and store of the region code is at the tag
  of `n` `64`-bit words, `n` the length of the parameters of the layout.
* `fieldDom_accScalar`: on the field domain, the destination and the index of every load and
  the index and the value of every store of the region code are no parameter names.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (regName_ne_argName)
open Ctxt (Var)

/-! ## 1. The access shape -/

/-- **Every array type of the context is of `n` `64`-bit words.** -/
def ArrLen (n : Nat) (Γ : Ctxt jasminDialect) : Prop :=
  ∀ w m, JasminTy.stackArr w m ∈ Γ → w = 64 ∧ m = n

/-- **The access shape at `n` words**: a load or a store is at the tag of `n` `64`-bit words,
    the destination and the index of a load and the index and the value of a store are no
    parameter names. -/
def AccShape (n : Nat) (i : LinstrRM) : Prop :=
  (∀ w m, (i.2 = .load w m ∨ i.2 = .store w m) → w = 64 ∧ m = n) ∧
  (∀ d b x s w m, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load w m) →
    ∀ j, d ≠ argName j ∧ x ≠ argName j) ∧
  (∀ d b x s v w m, i = (.Lopn [.reg d] "STOREIDX" [.arrIdx b x s, .reg v], .store w m) →
    ∀ j, x ≠ argName j ∧ v ≠ argName j)

/-- A renamed load is a load of the same destination and index. -/
theorem renLoad_eq_load {ρ : String → String} {wi : LinstrR} {d b x : String} {s : Nat}
    (h : renLoad ρ wi = .Lopn [.reg d] "LOADIDX" [.arrIdx b x s]) :
    ∃ b', wi = .Lopn [.reg d] "LOADIDX" [.arrIdx b' x s] := by
  unfold renLoad at h
  split at h <;> grind

/-- A renamed store is a store of the same index and value. -/
theorem renStore_eq_store {ρ : String → String} {wi : LinstrR} {d b x v : String} {s : Nat}
    (h : renStore ρ wi = .Lopn [.reg d] "STOREIDX" [.arrIdx b x s, .reg v]) :
    ∃ d' b', wi = .Lopn [.reg d'] "STOREIDX" [.arrIdx b' x s, .reg v] := by
  unfold renStore at h
  split at h <;> grind

/-- **The renaming of the array positions keeps the access shape.** -/
theorem accShape_renArr (ρ : String → String) {n : Nat} {i : LinstrRM} (h : AccShape n i) :
    AccShape n (renArr ρ i) := by
  obtain ⟨wi, tag⟩ := i
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun w m hw => h1 w m (by rwa [renArr_snd] at hw), ?_, ?_⟩
  · intro d b x s w m he j
    have ht : tag = .load w m := by
      have := congrArg Prod.snd he
      rwa [renArr_snd] at this
    subst ht
    have hw : renLoad ρ wi = .Lopn [.reg d] "LOADIDX" [.arrIdx b x s] :=
      congrArg Prod.fst he
    obtain ⟨b', rfl⟩ := renLoad_eq_load hw
    exact h2 d b' x s w m rfl j
  · intro d b x s v w m he j
    have ht : tag = .store w m := by
      have := congrArg Prod.snd he
      rwa [renArr_snd] at this
    subst ht
    have hw : renStore ρ wi = .Lopn [.reg d] "STOREIDX" [.arrIdx b x s, .reg v] :=
      congrArg Prod.fst he
    obtain ⟨d', b', rfl⟩ := renStore_eq_store hw
    exact h3 d' b' x s v w m rfl j

/-- An instruction at a register tag has the access shape. -/
theorem accShape_reg (n : Nat) (wire : LinstrR) (c : Option Nat) : AccShape n (wire, .reg c) :=
  ⟨by grind, by grind, by grind⟩

/-! ## 2. Typed resolution of variables -/

/-- **A variable that resolves to a parameter name is of a type of the parameters**: in the
    context `Δ ++ B` at the depth of the context, with the `B.length` parameters `B`. -/
theorem resolveVar_argName_mem {B : Ctxt jasminDialect} :
    ∀ (Δ : Ctxt jasminDialect) {τ : JasminTy} (v : Var (Δ ++ B) τ) (j : Nat),
      curName B.length v = argName j → τ ∈ B
  | [], _, v, _, _ => mem_of_var v
  | t :: Δ, _, v, j, h => by
      cases v with
      | here =>
          have hn : B.length ≤ (Δ ++ B).length := by simp
          rw [curName_here hn] at h
          exact absurd h (regName_ne_argName _ j)
      | there v =>
          refine resolveVar_argName_mem Δ v j ?_
          rw [← h]
          exact congrArg operandName (resolveVar_there (nArgs := B.length) (Δ ++ B).length v).symm

/-- **A variable of a register type resolves to no parameter name** when the parameters of the
    context are arrays. -/
theorem curName_ne_argName_of_reg {B : Ctxt jasminDialect} {n : Nat}
    (hB : ∀ τ ∈ B, τ = .stackArr 64 n) {Γ : Ctxt jasminDialect} (hΓ : ∃ Δ, Γ = Δ ++ B)
    {w : Nat} (v : Var Γ (.reg w)) (j : Nat) : curName B.length v ≠ argName j := by
  obtain ⟨Δ, rfl⟩ := hΓ
  intro h
  cases hB _ (resolveVar_argName_mem Δ v j h)

/-! ## 3. The export -/

variable {nArgs : Nat} {fn : String}

/-- The export of a load over a context of arrays of `n` words has the access shape. -/
theorem accShape_bindOps_load {B : Ctxt jasminDialect} {n : Nat}
    (hB : ∀ τ ∈ B, τ = .stackArr 64 n) {Γ : Ctxt jasminDialect} (hΓ : ∃ Δ, Γ = Δ ++ B)
    (hA : ArrLen n Γ) {w m : Nat} (a : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) :
    ∀ ins ∈ bindOps B.length (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ :
        Expr jasminDialect Γ (.reg w)) Γ.length, AccShape n ins := by
  rw [bindOps_load_eq]
  intro ins hins
  rw [List.mem_singleton] at hins
  subst hins
  obtain ⟨rfl, rfl⟩ := hA _ _ (mem_of_var a)
  refine ⟨fun w' m' h => by grind, ?_, by grind⟩
  intro d b x s w' m' he j
  simp only [Prod.mk.injEq, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
    LOperand.arrIdx.injEq, and_true] at he
  obtain ⟨⟨rfl, -, -, rfl, -⟩, -⟩ := he
  exact ⟨regName_ne_argName _ j, curName_ne_argName_of_reg hB hΓ i j⟩

/-- The export of a store over a context of arrays of `n` words has the access shape. -/
theorem accShape_bindOps_store {B : Ctxt jasminDialect} {n : Nat}
    (hB : ∀ τ ∈ B, τ = .stackArr 64 n) {Γ : Ctxt jasminDialect} (hΓ : ∃ Δ, Γ = Δ ++ B)
    (hA : ArrLen n Γ) {w m : Nat} (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64))
    (x : Var Γ (.reg w)) :
    ∀ ins ∈ bindOps B.length (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
        Expr jasminDialect Γ (.stackArr w m)) Γ.length, AccShape n ins := by
  rw [bindOps_store_eq]
  intro ins hins
  rw [List.mem_singleton] at hins
  subst hins
  obtain ⟨rfl, rfl⟩ := hA _ _ (mem_of_var v)
  refine ⟨fun w' m' h => by grind, by grind, ?_⟩
  intro d b y s u w' m' he j
  simp only [Prod.mk.injEq, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
    LOperand.arrIdx.injEq, and_true] at he
  obtain ⟨⟨-, -, ⟨-, rfl, -⟩, rfl⟩, -⟩ := he
  exact ⟨curName_ne_argName_of_reg hB hΓ i j, curName_ne_argName_of_reg hB hΓ x j⟩

/-- The context after a memory-free binding the export accepts keeps the array types. -/
theorem arrLen_memFree {n : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : jMemFree e.op = true) (hb : bindMemNB e = true)
    (hA : ArrLen n Γ) : ArrLen n (t :: Γ) := by
  intro w m hm
  rcases List.mem_cons.mp hm with hm | hm
  · exact absurd hm.symm ((memFree_bind e he hb).2 w m)
  · exact hA w m hm

/-- The context after a binding of an array type of the context keeps the array types. -/
theorem arrLen_cons_of_mem {n : Nat} {Γ : Ctxt jasminDialect} {w m : Nat}
    (v : Var Γ (.stackArr w m)) (hA : ArrLen n Γ) : ArrLen n (.stackArr w m :: Γ) := by
  intro w' m' hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
    exact hA _ _ (mem_of_var v)
  · exact hA w' m' hm

/-- **The export of a chain tail over a context of arrays of `n` words has the access
    shape.** -/
theorem chainTail_export_accShape {B : Ctxt jasminDialect} {n : Nat}
    (hB : ∀ τ ∈ B, τ = .stackArr 64 n) {Γ : Ctxt jasminDialect} {w m : Nat}
    {v : Var Γ (.stackArr w m)} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : ChainTail v p) (hE : regionExportableB p = true) (hΓ : ∃ Δ, Γ = Δ ++ B)
    (hA : ArrLen n Γ) {k : Nat} {r : Exported}
    (hr : exportR B.length fn p Γ.length k = some r) : ∀ i ∈ r.code, AccShape n i := by
  induction h generalizing k r with
  | ret v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      intro i hi
      cases hi
  | free v e k' he _ ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨Δ, hΔ⟩ := hΓ
      intro i hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg B.length _ e he
        rw [hb, List.mem_singleton] at hi
        subst hi
        exact accShape_reg n wire c
      · exact ih hE.2 ⟨_ :: Δ, by rw [hΔ]; rfl⟩ (arrLen_memFree e he hE.1 hA) hk' i hi
  | store v i x k' _ ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨Δ, hΔ⟩ := hΓ
      intro ins hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · exact accShape_bindOps_store hB ⟨Δ, hΔ⟩ hA v i x ins hi
      · exact ih hE.2 ⟨_ :: Δ, by rw [hΔ]; rfl⟩ (arrLen_cons_of_mem v hA) hk' ins hi

/-- **The export of a program of the shape `LoadsChainS` over a context of arrays of `n` words
    has the access shape.** -/
theorem loadsChainS_export_accShape {B : Ctxt jasminDialect} {n : Nat}
    (hB : ∀ τ ∈ B, τ = .stackArr 64 n) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) (hE : regionExportableB p = true)
    (hΓ : ∃ Δ, Γ = Δ ++ B) (hA : ArrLen n Γ) {k : Nat} {r : Exported}
    (hr : exportR B.length fn p Γ.length k = some r) : ∀ i ∈ r.code, AccShape n i := by
  induction h generalizing k r with
  | free e k' he _ ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨Δ, hΔ⟩ := hΓ
      intro i hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg B.length _ e he
        rw [hb, List.mem_singleton] at hi
        subst hi
        exact accShape_reg n wire c
      · exact ih hE.2 ⟨_ :: Δ, by rw [hΔ]; rfl⟩ (arrLen_memFree e he hE.1 hA) hk' i hi
  | load a i k' _ ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨Δ, hΔ⟩ := hΓ
      intro ins hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · exact accShape_bindOps_load hB ⟨Δ, hΔ⟩ hA a i ins hi
      · refine ih hE.2 ⟨_ :: Δ, by rw [hΔ]; rfl⟩ (fun w' m' hm => ?_) hk' ins hi
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm
        · exact hA w' m' hm
  | store v i x k' hk =>
      simp only [regionExportableB, Bool.and_eq_true] at hE
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨Δ, hΔ⟩ := hΓ
      intro ins hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · exact accShape_bindOps_store hB ⟨Δ, hΔ⟩ hA v i x ins hi
      · exact chainTail_export_accShape hB hk hE.2 ⟨_ :: Δ, by rw [hΔ]; rfl⟩
          (arrLen_cons_of_mem v hA) hk' ins hi

/-! ## 4. The field domain -/

/-- **Every type of the widened context of the field layout is an array of `n` `64`-bit
    words.** -/
theorem nfCtx_fieldAbi {σ : AbiLayout} {k n : Nat}
    (ha : σ.args = (FieldRoute.fieldAbi k n).args) :
    ∀ τ ∈ (nfCtx σ).map NarrowWords.wideTy, τ = .stackArr 64 n := by
  intro τ hm
  simp only [nfCtx, CryptoToJasminCom.mapCtx, CatCrypt.Crypto.Hax.ImpToNF.entryCtx,
    NFToRoute.abiEntry, CatCrypt.Crypto.Hax.NFToCat.abiParamsArr, List.map_reverse, List.map_map,
    List.mem_reverse, List.mem_map, Function.comp_apply] at hm
  obtain ⟨a, haM, rfl⟩ := hm
  have hk : a.kind = .words n := by
    rw [ha] at haM
    simp only [FieldRoute.fieldAbi, List.mem_map] at haM
    obtain ⟨j, -, rfl⟩ := haM
    rfl
  simp [hk, CatCrypt.Crypto.Hax.NFToCat.abiKindArr, CatCrypt.Crypto.Hax.NFToCat.catTy,
    CryptoToJasminCom.mapTy, NarrowWords.wideTy, NarrowWords.wideW]

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The region code of a member of the field domain has the access shape** at the length `n`
    of the parameters of the layout. -/
theorem fieldDom_accShape (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    {k n : Nat} (ha : σ.args = (FieldRoute.fieldAbi k n).args) :
    ∀ i ∈ r.code, AccShape n i := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, -⟩ := hB
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hL := fieldDom_legalize_loadsChainS h hq hq'
  have hBc := nfCtx_fieldAbi ha
  have h0 := loadsChainS_export_accShape hBc hL hEx ⟨[], rfl⟩
    (fun w m hm => by
      have := hBc _ hm
      simp only [JasminTy.stackArr.injEq] at this
      exact this) hr0
  rw [regionWebsAt_none]
  exact forall_mem_regionWebs (P := AccShape n) (fun ρ i hi => accShape_renArr ρ hi) _ r0 _ _ h0

/-- **The tags of the accesses on the field domain.** Every load-tagged and every
    store-tagged instruction of the region code of a member of the field domain is at the tag
    `.load 64 n` or `.store 64 n`, `n` the length of the parameters of the layout. -/
theorem fieldDom_accTag (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    {k n : Nat} (ha : σ.args = (FieldRoute.fieldAbi k n).args) :
    ∀ i ∈ r.code, ∀ w m, (i.2 = .load w m ∨ i.2 = .store w m) → w = 64 ∧ m = n :=
  fun i hi => (fieldDom_accShape h hB ha i hi).1

/-- **The scalar operands of the accesses on the field domain.** In the region code of a
    member of the field domain, the destination and the index of every load and the index and
    the stored value of every store are no parameter names `argName j`. -/
theorem fieldDom_accScalar (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    ∀ i ∈ r.code, ∀ j,
      (∀ d b x s w m, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load w m) →
        d ≠ argName j ∧ x ≠ argName j) ∧
      (∀ d b x s v w m, i = (.Lopn [.reg d] "STOREIDX" [.arrIdx b x s, .reg v], .store w m) →
        x ≠ argName j ∧ v ≠ argName j) := by
  obtain ⟨k, n, -, ha, -⟩ := fieldDomB_layout h
  intro i hi j
  obtain ⟨-, h2, h3⟩ := fieldDom_accShape h hB ha i hi
  exact ⟨fun d b x s w m he => h2 d b x s w m he j,
    fun d b x s v w m he => h3 d b x s v w m he j⟩

/-- The names of the result copy are no parameter names. -/
theorem copyNames_ne_argName (j : Nat) : copyTmp ≠ argName j ∧ copyIdx ≠ argName j := by
  constructor <;> intro h <;> simpa [copyTmp, copyIdx, argName] using congrArg String.toList h

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
