/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPosShapeField

/-!
# No load directly followed by a store on the field domain

The theorem `fieldDom_foldPos_addSub_noLoadStore` takes as its hypothesis `hC` that no load of
the region code is directly followed by a store. The export of a program of the shape
`LoadsChainS` emits one instruction per binding: a register tag for a memory-free binding, a
`LOADIDX` for a load and a `STOREIDX` for a store, and the webs rename the array positions of
each instruction in place. So a load of the region code is directly followed by a store exactly
when a load binding of the program the export receives is directly followed by a store binding.
The shape `LoadsChainS` admits that pair; the shape `NoLoadStore` excludes it.

## Main definitions

* `StoreHead`: the program begins with a store binding.
* `NoLoadStore`: a program built of bindings in which no load binding is directly followed by a
  store binding.

## Main results

* `loadsChainS_export_noLoadStore`: the export of a program of the shapes `LoadsChainS` and
  `NoLoadStore` has no load directly followed by a store.
* `fieldDom_noLoadStore_code`: the hypothesis `hC` of `fieldDom_foldPos_addSub_noLoadStore`
  from the shape `NoLoadStore` of the program the export receives.
* `fieldDom_foldPos_addSub_of_noLoadStoreNF`: the fold positions of the sum and the difference
  from the shapes `LoadsChainK` and `NoLoadStore` of the program the export receives.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webRen)
open Ctxt (Var)

/-! ## 1. The shape -/

/-- **The program begins with a store binding.** -/
def StoreHead {Γ : Ctxt jasminDialect} {ts : List JasminTy} :
    NFProg jasminDialect Γ ts → Prop
  | .var e _ => ∃ w m, e.op = .stackStore w m
  | _ => False

/-- **No load directly followed by a store**: a program built of bindings in which no load
    binding is directly followed by a store binding. -/
inductive NoLoadStore : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Prop
  /-- The return. -/
  | ret {Γ : Ctxt jasminDialect} {ts : List JasminTy} (vs : HVector (fun t => Var Γ t) ts) :
      NoLoadStore (.ret vs)
  /-- A binding that is no load, or a load whose continuation does not begin with a store. -/
  | var {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
      (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts) :
      ((∃ w m, e.op = .stackLoad w m) → ¬ StoreHead k) → NoLoadStore k →
        NoLoadStore (.var e k)

/-- The inversion of `NoLoadStore` at a binding. -/
theorem NoLoadStore.var_inv {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    {e : Expr jasminDialect Γ t} {k : NFProg jasminDialect (t :: Γ) ts}
    (h : NoLoadStore (.var e k)) :
    ((∃ w m, e.op = .stackLoad w m) → ¬ StoreHead k) ∧ NoLoadStore k := by
  cases h
  exact ⟨‹_›, ‹_›⟩

/-! ## 2. The export -/

/-- An instruction at a register tag is no load. -/
theorem loadB_reg (wire : LinstrR) (c : Option Nat) : loadB (wire, .reg c) = false := by
  cases h : loadB (wire, .reg c)
  · rfl
  · obtain ⟨d, b, x, s, w, n, he⟩ := loadB_iff.mp h
    simp at he

/-- An instruction at a register tag is no store. -/
theorem storeB_reg (wire : LinstrR) (c : Option Nat) : storeB (wire, .reg c) = false := by
  cases h : storeB (wire, .reg c)
  · rfl
  · obtain ⟨d, b, x, s, v, w, n, he⟩ := storeB_iff.mp h
    simp at he

variable {nArgs : Nat} {fn : String}

/-- **The export of a chain tail has no load.** -/
theorem chainTail_export_loadB {Γ : Ctxt jasminDialect} {w m : Nat}
    {v : Var Γ (.stackArr w m)} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : ChainTail v p) {d c : Nat} {r : Exported} (hr : exportR nArgs fn p d c = some r) :
    ∀ i ∈ r.code, loadB i = false := by
  induction h generalizing d c r with
  | ret v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      intro i hi
      cases hi
  | free v e k' he _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro i hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg nArgs d e he
        rw [hb, List.mem_singleton] at hi
        subst hi
        exact loadB_reg wire c
      · exact ih hk' i hi
  | store v i x k' _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro ins hi
      simp only [Exported.prepend, List.mem_append] at hi
      rcases hi with hi | hi
      · rw [bindOps_store_eq, List.mem_singleton] at hi
        subst hi
        rfl
      · exact ih hk' ins hi

/-- **The first instruction of the export of a program of the shape `LoadsChainS` that does
    not begin with a store is no store.** -/
theorem loadsChainS_export_head {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) (hs : ¬ StoreHead p) {d c : Nat}
    {r : Exported} (hr : exportR nArgs fn p d c = some r) :
    ∀ j, r.code[0]? = some j → storeB j = false := by
  cases h with
  | free e k' he _ =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, -, rfl⟩ := hr
      obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg nArgs d e he
      intro j hj
      simp only [Exported.prepend, hb, List.cons_append, List.nil_append,
        List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact storeB_reg wire c
  | load a i k' _ =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, -, rfl⟩ := hr
      intro j hj
      simp only [Exported.prepend] at hj
      rw [bindOps_load_eq] at hj
      simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero,
        Option.some.injEq] at hj
      subst hj
      rfl
  | store v i x k' _ =>
      exact absurd ⟨_, _, rfl⟩ hs

/-- **The export of a program of the shapes `LoadsChainS` and `NoLoadStore` has no load
    directly followed by a store.** -/
theorem loadsChainS_export_noLoadStore {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) (hN : NoLoadStore p) {d c : Nat}
    {r : Exported} (hr : exportR nArgs fn p d c = some r) :
    ∀ (k : Nat) (i j : LinstrRM), r.code[k]? = some i → r.code[k + 1]? = some j →
      loadB i = true → storeB j = false := by
  induction h generalizing d c r with
  | free e k' he _ ih =>
      have hN' := hN.var_inv.2
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg nArgs d e he
      intro k i j hi hj hl
      simp only [Exported.prepend, hb, List.cons_append, List.nil_append] at hi hj
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          rw [loadB_reg] at hl
          cases hl
      | succ k =>
          simp only [List.getElem?_cons_succ] at hi hj
          exact ih hN' hk' k i j hi hj hl
  | load a i0 k' hk ih =>
      obtain ⟨hs, hN'⟩ := hN.var_inv
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro k i j hi hj hl
      simp only [Exported.prepend] at hi hj
      rw [bindOps_load_eq] at hi hj
      simp only [List.cons_append, List.nil_append] at hi hj
      cases k with
      | zero =>
          simp only [List.getElem?_cons_succ] at hj
          exact loadsChainS_export_head hk (hs ⟨_, _, rfl⟩) hk' j hj
      | succ k =>
          simp only [List.getElem?_cons_succ] at hi hj
          exact ih hN' hk' k i j hi hj hl
  | store v i0 x k' hk =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      intro k i j hi hj hl
      simp only [Exported.prepend] at hi hj
      rw [bindOps_store_eq] at hi hj
      simp only [List.cons_append, List.nil_append] at hi hj
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          cases hl
      | succ k =>
          simp only [List.getElem?_cons_succ] at hi
          rw [chainTail_export_loadB hk hk' i (List.mem_of_getElem? hi)] at hl
          cases hl

/-! ## 3. The field domain -/

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The hypothesis `hC` of `fieldDom_foldPos_addSub_noLoadStore`**: on the field domain, no
    load of the region code is directly followed by a store when the program the export
    receives has the shape `NoLoadStore`. -/
theorem fieldDom_noLoadStore_code (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hN : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → NoLoadStore (legalizeRegion q')) :
    ∀ (k : Nat) (i j : LinstrRM), r.code[k]? = some i → r.code[k + 1]? = some j →
      loadB i = true → storeB j = false := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, -⟩ := hB
  have h0 := loadsChainS_export_noLoadStore (fieldDom_legalize_loadsChainS h hq hq')
    (hN _ _ _ hq hq') hr0
  rcases regionWebsAt_cases (regionWebsEx σ exportReg) r0 with he | ⟨tab, L, -, he⟩
  · rw [he]
    exact h0
  · rw [he]
    intro k i j hi hj hl
    simp only [webRen, List.getElem?_mapIdx, Option.map_eq_some_iff] at hi hj
    obtain ⟨i0, hi0, rfl⟩ := hi
    obtain ⟨j0, hj0, rfl⟩ := hj
    have hj1 := h0 k i0 j0 hi0 hj0 (loadB_of_renArr hl)
    cases hs : storeB (X86Backend.ImageCoalesceCfg.renArr
        (X86Backend.ArrWebs.stepRen (X86Backend.ArrWebs.webLook tab) (fun _ => none) (k + 1) j0)
        j0)
    · rfl
    · have hs' := storeB_of_renArr hs
      grind

/-- **The fold positions of the sum and the difference of the field domain** from the shapes
    `LoadsChainK` and `NoLoadStore` of the program the export receives:
    `fieldDom_foldPos_addSub_noLoadStore` with its hypothesis `hC` proved by
    `fieldDom_noLoadStore_code`. -/
theorem fieldDom_foldPos_addSub_of_noLoadStoreNF (h : fieldDomB'' e σ = true)
    (hA : FieldAddSub e) (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q'))
    (hN : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → NoLoadStore (legalizeRegion q')) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i :=
  fieldDom_foldPos_addSub_noLoadStore h hA hB hL
    (fieldDom_noLoadStore_code (fieldDomB_of_fieldDomB'' h) hB hN)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
