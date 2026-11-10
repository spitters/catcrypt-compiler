/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomWriteKills

/-!
# The class condition of the store-chain shape on the export of one chain of stores

The third conjunct of `CoalesceComplete.ChainShape` asks, at every write of a name `d`, that
every other name of the class of `d` whose writes precede the write is consumed by then or not
read after it. On a body whose array writes form one chain from a root `x` (the root is never
written; every write is a store whose base is the previous version), and under an alias map
that sends every written name to `x` and fixes every other name, the class of a written name is
the chain: an earlier version is consumed by the store of the next version, and the root by the
first store.

The export of a program of the shape `LoadsChain` has such a chain: the root is the name of the
base of the first store, and each store reads the current version and writes the slot of its
binding.

## Main definitions

* `CoalesceComplete.ChainConsume`: the root is never written, it is consumed by the first
  write, and every written name is consumed by the time of every later write.

## Main results

* `CoalesceComplete.chainShape₃_of_consume`: the third conjunct of `ChainShape` from
  `ChainConsume` under an alias map that sends the written names to the root and fixes the
  others.
* `chainTail_export_consume`, `loadsChain_export_consume`: the export of a chain tail, and of a
  program of the shape `LoadsChain`, has the consumption facts of a chain.
* `loadsChain_export_chainShape`: the store-chain shape of that export under such an alias map.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)

/-- **The consumption facts of one chain of stores from the root `x`**: `x` is never written,
    it is consumed at or before every write, and a name written at `w` is consumed at or before
    every write after `w`. -/
def ChainConsume (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (x : String) : Prop :=
  (∀ w, ¬ WrAt body ao w x)
    ∧ (∀ k d, WrAt body ao k d → ∃ c, c ≤ k ∧ ConsumedAt body aa ao c x)
    ∧ ∀ w r k d, w < k → WrAt body ao w r → WrAt body ao k d →
      ∃ c, c ≤ k ∧ ConsumedAt body aa ao c r

/-- **The class condition from the consumption facts of one chain**: under an alias map that
    sends every written name to the root `x` and fixes every name that is never written, a
    name of the class of a written name `d` whose writes precede the write of `d` is consumed
    by then. -/
theorem chainShape₃_of_consume {σ : String → String} {body : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {obs : List String}
    {x : String} (hC : ChainConsume body aa ao x)
    (hw : ∀ w n, WrAt body ao w n → σ n = x) (hn : ∀ n, (∀ w, ¬ WrAt body ao w n) → σ n = n) :
    ∀ k d r, WrAt body ao k d → σ r = σ d → r ≠ d → (∀ w, WrAt body ao w r → w < k) →
      (∃ c, c ≤ k ∧ ConsumedAt body aa ao c r) ∨ ∀ j, k < j → ¬ ReadAt body aa obs j r := by
  obtain ⟨_, hroot, hnext⟩ := hC
  intro k d r hk hσ _ hbefore
  left
  by_cases hr : ∃ w, WrAt body ao w r
  · obtain ⟨w, hwr⟩ := hr
    exact hnext w r k d (hbefore w hwr) hwr hk
  · have hrx : r = x := by
      rw [← hn r (fun w h => hr ⟨w, h⟩), hσ, hw k d hk]
    subst hrx
    exact hroot k d hk

end CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainConsume ChainShape chainShape₃_of_consume rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (regName_injective)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open Ctxt (Var)

section ExportChain

variable {nArgs : Nat} {fn : String} {aa : String → Nat → Option Nat}
  {ao : String → Option Nat}

/-- The consumption facts of a body with one instruction in front that writes no array. -/
theorem chainConsume_cons_noWrite {ins : LinstrRM} {body : List LinstrRM} {x : String}
    (h : ChainConsume body aa ao x) (hw : wrArr ao ins = none) :
    ChainConsume (ins :: body) aa ao x := by
  obtain ⟨hx, hroot, hnext⟩ := h
  refine ⟨fun w hw' => ?_, fun k d hk => ?_, fun w r k d hwk hwr hkd => ?_⟩
  · cases w with
    | zero => rw [wrAt_cons_zero, hw] at hw'; cases hw'
    | succ w => exact hx w (wrAt_cons_succ.mp hw')
  · cases k with
    | zero => rw [wrAt_cons_zero, hw] at hk; cases hk
    | succ k =>
        obtain ⟨c, hc, hcx⟩ := hroot k d (wrAt_cons_succ.mp hk)
        exact ⟨c + 1, by omega, consumedAt_cons_succ.mpr hcx⟩
  · cases w with
    | zero => rw [wrAt_cons_zero, hw] at hwr; cases hwr
    | succ w =>
        cases k with
        | zero => omega
        | succ k =>
            obtain ⟨c, hc, hcr⟩ := hnext w r k d (by omega) (wrAt_cons_succ.mp hwr)
              (wrAt_cons_succ.mp hkd)
            exact ⟨c + 1, by omega, consumedAt_cons_succ.mpr hcr⟩

/-- The consumption facts of a store in front of the rest of its chain: the store reads the
    root `x` and writes `y`, the rest is a chain from `y`, and `x` is not written by the rest. -/
theorem chainConsume_cons_store {ins : LinstrRM} {body : List LinstrRM} {x y : String}
    (h : ChainConsume body aa ao y) (hrd : x ∈ rdArr aa ins) (hwr : wrArr ao ins = some y)
    (hxy : y ≠ x) (hx : ∀ w, ¬ WrAt body ao w x) :
    ChainConsume (ins :: body) aa ao x := by
  obtain ⟨-, hroot, hnext⟩ := h
  have hc0 : ConsumedAt (ins :: body) aa ao 0 x :=
    consumedAt_cons_zero.mpr ⟨hrd, y, hwr, hxy⟩
  refine ⟨fun w hw' => ?_, fun k d _ => ⟨0, Nat.zero_le _, hc0⟩, fun w r k d hwk hwr' hkd => ?_⟩
  · cases w with
    | zero => rw [wrAt_cons_zero, hwr] at hw'; exact hxy (Option.some.inj hw')
    | succ w => exact hx w (wrAt_cons_succ.mp hw')
  · cases k with
    | zero => omega
    | succ k =>
        cases w with
        | zero =>
            rw [wrAt_cons_zero, hwr] at hwr'
            cases hwr'
            obtain ⟨c, hc, hcr⟩ := hroot k d (wrAt_cons_succ.mp hkd)
            exact ⟨c + 1, by omega, consumedAt_cons_succ.mpr hcr⟩
        | succ w =>
            obtain ⟨c, hc, hcr⟩ := hnext w r k d (by omega) (wrAt_cons_succ.mp hwr')
              (wrAt_cons_succ.mp hkd)
            exact ⟨c + 1, by omega, consumedAt_cons_succ.mpr hcr⟩

/-- **The export of a chain tail has the consumption facts of one chain** from the name of its
    current version. -/
theorem chainTail_export_consume (haa : ∀ f j, aa f j = none) (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy} {v : Var Γ (.stackArr w m)}
    {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) (hn : nArgs ≤ Γ.length) {n : Nat}
    {r : Exported} (hr : exportR nArgs fn k Γ.length n = some r) :
    ChainConsume r.code aa ao (curName nArgs v) := by
  induction h generalizing n r with
  | @free Γ w m t ts v e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, -, hwr⟩ := bindOps_memFree nArgs Γ.length e he aa ao haa hao
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have := ih (by simp only [List.length_cons]; omega) hk'
      rw [curName, List.length_cons, resolveVar_there] at this
      exact chainConsume_cons_noWrite this hwr
  | @store Γ w m ts v i x k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hwr, hrd⟩ := bindOps_store nArgs Γ.length v i x aa ao
      have hrest := ih (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hrest
      obtain ⟨hF, -⟩ := chainTail_export (fn := fn) haa hao hk
        (by simp only [List.length_cons]; omega) hk'
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have hv := inScope_resolveVar (nArgs := nArgs) v
      refine chainConsume_cons_store hrest (by rw [hrd]; exact List.mem_singleton_self _) hwr
        (fun h => hv.ne_regName le_rfl h.symm) (fun w' hw' => ?_)
      have h1 := hF.2.1 w' _ hw'
      exact hv.ne_regName (by simp only [List.length_cons]; omega) h1
  | @ret Γ w m v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      refine ⟨fun w h => ?_, fun k d h => ?_, fun w r k d _ h => ?_⟩ <;>
        · obtain ⟨_, h, -⟩ := h
          simp at h

/-- **The export of a program of the shape `LoadsChain` has the consumption facts of one
    chain**, from some root. -/
theorem loadsChain_export_consume (haa : ∀ f j, aa f j = none) (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) :
    ∃ x, ChainConsume r.code aa ao x := by
  induction h generalizing n r with
  | @free Γ t ts e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, -, hwr⟩ := bindOps_memFree nArgs Γ.length e he aa ao haa hao
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      obtain ⟨x, hx⟩ := ih (by simp only [List.length_cons]; omega) hk'
      exact ⟨x, chainConsume_cons_noWrite hx hwr⟩
  | @load Γ w m ts a i k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hwr, -⟩ := bindOps_load nArgs Γ.length a i aa ao
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackLoad w m, rfl,
          .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      obtain ⟨x, hx⟩ := ih (by simp only [List.length_cons]; omega) hk'
      exact ⟨x, chainConsume_cons_noWrite hx hwr⟩
  | @store Γ w m ts v i x k hk =>
      have hr' : exportR nArgs fn (.var (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) k)
          Γ.length n = some r := hr
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hwr, hrd⟩ := bindOps_store nArgs Γ.length v i x aa ao
      have hrest := chainTail_export_consume (fn := fn) haa hao hk
        (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hrest
      obtain ⟨hF, -⟩ := chainTail_export (fn := fn) haa hao hk
        (by simp only [List.length_cons]; omega) hk'
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have hv := inScope_resolveVar (nArgs := nArgs) v
      refine ⟨_, chainConsume_cons_store hrest (by rw [hrd]; exact List.mem_singleton_self _) hwr
        (fun h => hv.ne_regName le_rfl h.symm) (fun w' hw' => ?_)⟩
      have h1 := hF.2.1 w' _ hw'
      exact hv.ne_regName (by simp only [List.length_cons]; omega) h1
  | @ret Γ ts vs =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      refine ⟨"", fun w h => ?_, fun k d h => ?_, fun w r k d _ h => ?_⟩ <;>
        · obtain ⟨_, h, -⟩ := h
          simp at h

/-- **The store-chain shape of the export of a program of the shape `LoadsChain`**, under every
    alias map that sends the names the code writes to the root of the chain and fixes the
    others. -/
theorem loadsChain_export_chainShape (haa : ∀ f j, aa f j = none) (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) :
    ∃ x, ∀ σ : String → String, (∀ w y, WrAt r.code ao w y → σ y = x) →
      (∀ y, (∀ w, ¬ WrAt r.code ao w y) → σ y = y) →
      ChainShape σ r.code aa ao (r.res.map operandName) := by
  obtain ⟨x, hx⟩ := loadsChain_export_consume (fn := fn) haa hao h hn hr
  obtain ⟨h1, h2⟩ := loadsChain_export_chainShape₁₂ (fn := fn) haa hao h hn hr
  exact ⟨x, fun σ hw hn' => ⟨h1, h2, chainShape₃_of_consume hx hw hn'⟩⟩

end ExportChain

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
