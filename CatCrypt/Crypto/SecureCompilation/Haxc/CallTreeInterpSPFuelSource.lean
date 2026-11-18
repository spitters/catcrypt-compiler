/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance
public import CatCryptCore.Prob.SDistrChain

/-!
# Robust compilation over the handlers of the linked functions, without source fuel

`HandlerRC` states robust compilation at every pair `(fuelC, fuel)` of source fuels, with a bound
`δ` of the failure weight of the source read-back at that pair. This module removes the source
fuel. The source call trees along the diagonal `fuelC = fuel = n` are increasing in `n`, with the
leaves whose read-back `srcRead` is undefined at the bottom: a run that reads back a value at `n`
reads back the same value at every larger `n`. Mapped by `srcRead`, the leaves of the diagonal
are therefore increasing in the fuel order `FuelLe`, whose bottom is the leaf `none`, and the
source interpretations form a chain of `SPComp`. The source interpretation `interpSrcω` is the
supremum of this chain. Its failure weight is the divergence mass of the source: the weight of
the runs that read back no value at any fuel. The chain is constant from some fuel on, so its
supremum is one of its elements, and `HandlerRC` at that fuel gives robust compilation at
`ε + δ`, with `δ` the divergence mass (`HandlerRC.toω`).

The monotonicity along the diagonal is the composition of the fuel and table monotonicity of the
reference reading `denoteSpine` (`denoteSpine_val_mono`) and the monotonicity of the reference
table of a module in its function fuel (`refBi_le_of_fuel_le`).

## Main definitions

* `srcChain`: the chain of the source interpretations along the diagonal of the fuels.
* `interpSrcω`, `srcDiv`: its supremum, and the divergence mass of the source.
* `HandlerRCω`: robust compilation over the handlers meeting the separation contracts, at every
  entry state of the domain and every source environment, at `ε + srcDiv`.

## Main results

* `denoteSpine_val_mono`: a value run of `denoteSpine` is the run at every larger table and fuel.
* `table_le_of_fuel_le`: the table of a module is increasing in its function fuel.
* `srcRead_diag_mono`: along the diagonal, a source read-back is the read-back at every larger
  fuel.
* `interpSrcω_eq`: the supremum is an element of the chain.
* `HandlerRC.toω`: `HandlerRC` implies `HandlerRCω`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuelSource

open OmegaCompletePartialOrder
open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.Hax (HaxModule ModFn hax64WExit refBi denote'_val_of_le closureTable_le
  denoteSpine_val_of_le)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance
open _root_.Hax (Builtins ImpExpr Value Env Outcome denote')
open _root_.Hax.InlineLocalClosures (denoteSpine closureTable)

/-! ## Fuel and table monotonicity of the reference reading -/

/-- **A value run of `denote'` is the run at every larger table and fuel.** -/
theorem denote'_val_mono_le {bi bi' : Builtins}
    (hsub : ∀ g vals v, bi g vals = some v → bi' g vals = some v) {e : ImpExpr}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') {env env' : Env} {v : Value}
    (h : denote' bi fuel e env = (.val v, env')) : denote' bi' fuel' e env = (.val v, env') := by
  have h' := denote'_val_of_le hsub h
  rw [Hax.Ascent.denote'_val_mono bi' (by rw [h']) hle, h']

/-- The table of a closure is increasing in the table and the fuel. -/
theorem closureTable_mono {bi bi' : Builtins}
    (hsub : ∀ g vals v, bi g vals = some v → bi' g vals = some v) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') (f : String) (ps : List String) (body : ImpExpr) (ρ : Env) :
    ∀ g vals v, closureTable bi fuel f ps body ρ g vals = some v →
      closureTable bi' fuel' f ps body ρ g vals = some v := by
  intro g vals v h
  unfold closureTable at h ⊢
  split at h
  · split at h
    · split at h
      · rename_i w hw
        cases h
        have hr : denote' bi fuel body (_root_.Hax.InlineLocalClosures.bindAll ρ ps vals) =
            (.val v, (denote' bi fuel body
              (_root_.Hax.InlineLocalClosures.bindAll ρ ps vals)).2) := Prod.ext hw rfl
        rw [ite_eq_left ‹_›, ite_eq_left ‹_›]
        simp only [StateT.run]
        rw [denote'_val_mono_le hsub hle hr]
      · cases h
    · cases h
  · rw [ite_eq_right ‹_›]
    exact hsub g vals v h

/-- **A value run of `denoteSpine` is the run at every larger table and fuel.** -/
theorem denoteSpine_val_mono (fuel : Nat) : ∀ (bi : Builtins) (e : ImpExpr) {bi' : Builtins}
    {fuel' : Nat}, (∀ g vals v, bi g vals = some v → bi' g vals = some v) → fuel ≤ fuel' →
    ∀ (env env' : Env) (v : Value), (denoteSpine bi fuel e).run env = (.val v, env') →
      (denoteSpine bi' fuel' e).run env = (.val v, env') := by
  intro bi e
  induction bi, e using _root_.Hax.InlineLocalClosures.denoteSpine.induct fuel <;>
    intro bi' fuel' hsub hle env env' v h
  case case1 bi f ps body cont hc ih =>
    simp only [denoteSpine, hc, ite_true] at h ⊢
    exact ih env (closureTable_mono hsub hle f ps body env) hle env env' v h
  case case2 bi f ps body cont hc =>
    simp only [denoteSpine, hc] at h ⊢
    exact denote'_val_mono_le hsub hle h
  case case3 bi x w cont hw ih =>
    rw [denoteSpine.eq_2 _ _ _ _ _ hw] at h ⊢
    rcases hr : denote' bi fuel w env with ⟨o, s⟩
    simp only [StateT.run, bind, StateT.bind, hr] at h
    rcases o with (u|u|u|_|u)
    case val =>
      simp only [StateT.run, bind, StateT.bind, denote'_val_mono_le hsub hle hr]
      cases u <;> first | exact h | exact ih hsub hle _ _ _ h
    all_goals cases h
  case case4 bi a b ih =>
    rw [denoteSpine.eq_3] at h ⊢
    rcases hr : denote' bi fuel a env with ⟨o, s⟩
    simp only [StateT.run, bind, StateT.bind, hr] at h
    rcases o with (u|u|u|_|u)
    case val =>
      simp only [StateT.run, bind, StateT.bind, denote'_val_mono_le hsub hle hr]
      cases u <;> first | exact h | exact ih hsub hle _ _ _ h
    all_goals cases h
  case case5 bi e h1 h2 h3 =>
    rw [denoteSpine.eq_4 _ _ _ h1 h2 h3] at h ⊢
    exact denote'_val_mono_le hsub hle h

/-- **The reference table is increasing in its function fuel**, at every depth. -/
theorem refBi_le_of_fuel_le (fs : List ModFn) (bi : Builtins) {fuelC fuelC' : Nat}
    (hle : fuelC ≤ fuelC') :
    ∀ (n : Nat) g vals v, refBi fs bi fuelC n g vals = some v →
      refBi fs bi fuelC' n g vals = some v := by
  intro n
  induction n with
  | zero => intro g vals v h; simpa only [refBi] using h
  | succ n ih =>
    intro g vals v h
    simp only [refBi] at h ⊢
    split at h
    · rename_i f _
      split at h
      · rename_i w hw
        rw [denoteSpine_val_mono fuelC _ _ ih hle _ _ w (Prod.ext hw rfl)]
        exact h
      · cases h
    · exact h

/-- **The table of a module is increasing in its function fuel.** -/
theorem table_le_of_fuel_le (m : HaxModule) (bi : Builtins) {fuelC fuelC' : Nat}
    (hle : fuelC ≤ fuelC') :
    ∀ g vals v, m.table bi fuelC g vals = some v → m.table bi fuelC' g vals = some v :=
  refBi_le_of_fuel_le m.fns (m.linkTable bi) hle m.depth

/-! ## The source trees along the diagonal of the fuels -/

/-- The source leaf of the module `m` from the environment `env` at the fuels `fuelC = fuel = n`:
    the interpretation of the source call tree under the handler of the linked functions. -/
def srcLeaf (m : HaxModule) (env : Env) (n : Nat) : Outcome × Env :=
  interp (linkHandler m) (nfTree (moduleTreeTable m hax64WExit n) n m.entry.erase env)

/-- **Along the diagonal, a source read-back is the read-back at every larger fuel.** -/
theorem srcRead_diag_mono (m : HaxModule) (env : Env) {n n' : Nat} (hle : n ≤ n') {v : Value}
    (h : srcRead (srcLeaf m env n) = some v) : srcRead (srcLeaf m env n') = some v := by
  unfold srcLeaf at h ⊢
  rw [interp_nfTree_table] at h ⊢
  rcases hr : (denoteSpine (m.table hax64WExit n) n m.entry.erase).run env with ⟨o, env'⟩
  rw [hr] at h
  cases o with
  | val w =>
    rw [denoteSpine_val_mono n _ _ (table_le_of_fuel_le m hax64WExit hle) hle _ _ _ hr]
    exact h
  | _ => simp [srcRead] at h

/-- The source leaves along the diagonal, mapped by `srcRead`, are increasing in the fuel
    order: the leaf `none` is at the bottom. -/
theorem fuelLe_srcRead_diag (m : HaxModule) (env : Env) {n n' : Nat} (hle : n ≤ n') :
    FuelLe (E := linkSig) (.ret (srcRead (srcLeaf m env n)))
      (.ret (srcRead (srcLeaf m env n'))) := by
  cases h : srcRead (srcLeaf m env n) with
  | none => exact .none _
  | some v => rw [srcRead_diag_mono m env hle h]; exact .ret _

/-- The source interpretation at the diagonal fuel `n`, read back by `srcRead`, is the
    interpretation of the leaf `srcRead (srcLeaf m env n)`. -/
theorem readBack_srcTree (m : HaxModule) (env : Env) (n : Nat) :
    readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
      (nfTree (moduleTreeTable m hax64WExit n) n m.entry.erase env)) =
      interpSPOpt (fun e => SPComp.pure (linkHandler m e))
        (.ret (srcRead (srcLeaf m env n))) := by
  rw [readBack, interpSP_pure, SPComp.pure_bind, interpSPOpt, interpSP_ret, SPComp.pure_bind]
  rfl

/-- **The chain of the source interpretations** along the diagonal of the fuels, read back by
    `srcRead`. -/
noncomputable def srcChain (m : HaxModule) (env : Env) : Chain (SPComp Value) :=
  ⟨fun n => readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
      (nfTree (moduleTreeTable m hax64WExit n) n m.entry.erase env)),
    fun n n' hle => by
      simp only [readBack_srcTree]
      exact interpSPOpt_mono _ (fuelLe_srcRead_diag m env hle)⟩

/-- **The source interpretation without fuel**: the supremum of the source interpretations along
    the diagonal of the fuels. -/
noncomputable def interpSrcω (m : HaxModule) (env : Env) : SPComp Value :=
  ωSup (srcChain m env)

/-- **The divergence mass of the source**: the failure weight of `interpSrcω`, the weight of the
    runs that read back no value at any fuel. -/
noncomputable def srcDiv (m : HaxModule) (env : Env) : ℝ≥0∞ :=
  ⨆ s, interpSrcω m env s none

/-- The supremum of a chain that is constant from `n` on is its element at `n`. -/
theorem ωSup_eq_of_const_from {α : Type} [OmegaCompletePartialOrder α] (c : Chain α) (n : Nat)
    (h : ∀ k, n ≤ k → c k = c n) : ωSup c = c n :=
  le_antisymm (ωSup_le _ _ fun k => by
    rcases Nat.le_total k n with hk | hk
    · exact c.monotone hk
    · exact (h k hk).le) (le_ωSup c n)

/-- **The supremum of the source chain is one of its elements.** -/
theorem interpSrcω_eq (m : HaxModule) (env : Env) : ∃ n, interpSrcω m env = srcChain m env n := by
  by_cases hex : ∃ n v, srcRead (srcLeaf m env n) = some v
  · obtain ⟨n, v, hv⟩ := hex
    refine ⟨n, ωSup_eq_of_const_from _ n fun k hk => ?_⟩
    change readBack _ _ = readBack _ _
    rw [readBack_srcTree, readBack_srcTree, srcRead_diag_mono m env hk hv, hv]
  · refine ⟨0, ωSup_eq_of_const_from _ 0 fun k _ => ?_⟩
    have hnone : ∀ k, srcRead (srcLeaf m env k) = none := fun k => by
      cases h : srcRead (srcLeaf m env k) with
      | none => rfl
      | some v => exact absurd ⟨k, v, h⟩ hex
    change readBack _ _ = readBack _ _
    rw [readBack_srcTree, readBack_srcTree, hnone k, hnone 0]

/-! ## Robust compilation without source fuel -/

/-- **Robust compilation over the handlers meeting the separation contracts, without source
    fuel.** At every entry state `sa` of the domain of `σ` and every source environment `env` of
    the narrowed entry, let `ε` bound the failure weight of the target interpretation under every
    handler coupled at equal heaps with the meanings of the linked functions of `m` on the
    separation contracts. Then replacing the value of the source interpretation without fuel
    `interpSrcω` by the value `σ` reads back from the return state of the calling body `pc` is
    robust compilation over this class of handlers at `ε` plus the divergence mass `srcDiv` of the
    source. -/
def HandlerRCω (m : HaxModule) (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String) : Prop :=
  ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env → ∀ ε : ℝ≥0∞,
    (∀ h₂, HandlerCoupledCG m eqPre h₂ → ∀ s, interpTargetω m pc sym sa h₂ s none ≤ ε) →
    RobustCompilationH (HandlerCoupledCG m eqPre) (ε + srcDiv m env)
      (fun h₂ (_ : Unit) => readBack (fun s' => some (σ.result.read sa s'))
        (interpTargetω m pc sym sa h₂))
      (fun _ (_ : Unit) => interpSrcω m env)

/-- **`HandlerRC` without source fuel.** Robust compilation at every pair of source fuels gives
    robust compilation for the source interpretation without fuel, at the bound of the failure
    weight of the target plus the divergence mass of the source. -/
theorem HandlerRC.toω {m : HaxModule} {σ : AbiLayout} {pc : List RInstr} {sym : Nat → String}
    (h : HandlerRC m σ pc sym) : HandlerRCω m σ pc sym := by
  intro sa hsa env henv ε hε
  obtain ⟨n, hn⟩ := interpSrcω_eq m env
  have hδ : ∀ s, readBack srcRead (interpSP (fun e => SPComp.pure (linkHandler m e))
      (nfTree (moduleTreeTable m hax64WExit n) n m.entry.erase env)) s none ≤ srcDiv m env :=
    fun s => by
      change srcChain m env n s none ≤ _
      rw [← hn]
      exact le_iSup (fun s => interpSrcω m env s none) s
  rw [hn]
  exact h sa hsa env henv n n ε (srcDiv m env) hε hδ

end CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuelSource
