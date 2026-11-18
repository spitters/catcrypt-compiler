/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuelSource

/-!
# Fuel monotonicity of the source call trees

The source call tree `nfTree` of a module at the fuels `(fuelC, fuel)` is increasing along the
diagonal `fuelC = fuel = n` in a fuel order on trees whose bottom is given by a predicate on the
leaves. The order `FuelLeB P` puts every leaf satisfying `P` below every tree, a leaf below
itself, and an event below the same event with continuations above pointwise. For the source
trees `P` is the error outcome: a reading at a larger table and a larger fuel replaces an error
leaf by a tree and keeps every other leaf and every event. The statement is about trees, so it
holds under every handler: the interpretation of a tree is monotone in the order, and the
read-backs of the source interpretations under any handler `h : ∀ e, SPComp (Resp e)` form a chain,
whose supremum `interpSrcωH h` is the source interpretation without fuel under `h`. At the point
masses of the handler of the linked functions it is `interpSrcω`.

The monotonicity of the reading is one induction over the thirteen readings of `denoteT`, in
the order `TMLe` on stateful tree computations, whose sequencing lemma `TMLe.bind` asks that a
bottom result continue with a bottom leaf.

## Main definitions

* `FuelLeB`: the fuel order with a bottom predicate on the leaves.
* `TMLe`, `TabLe`: the order on stateful tree computations and on tree tables.
* `srcTree`: the source call tree at a diagonal fuel, its leaves read back by `srcRead`.
* `interpSrcωH`, `srcDivH`: the source interpretation without fuel under a handler, and its
  failure weight.

## Main results

* `denoteT_mono_and`, `denoteSpineT_mono`, `nfTree_mono`: the readings and the call tree are
  monotone in the table and the fuel.
* `moduleTreeTable_mono`, `nfTree_diag_mono`: the tree table of a module is increasing in its
  function fuel, and the source call tree is increasing along the diagonal.
* `srcTree_fuelLe`, `readBack_srcTree_mono`: the read-back source trees are increasing in
  `FuelLe`, and their interpretations under every handler are increasing.
* `interpSrcωH_apply_some`, `readBack_le_interpSrcωH`, `interpSrcωH_linkHandler`: the weights
  of the supremum, the bound of each element, and the agreement with `interpSrcω`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFTreeFuelMono

open OmegaCompletePartialOrder
open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open _root_.Hax (Builtins ImpExpr Value Env Outcome)

/-! ## The fuel order with a bottom predicate -/

section Order

variable {E : EventSig}

/-- **The fuel order on call trees with a bottom predicate `P` on leaves**: a leaf satisfying `P`
    is below every tree, a leaf is below itself, and an event is below the same event with
    continuations above pointwise. -/
inductive FuelLeB {R : Type} (P : R → Prop) : CallTree E R → CallTree E R → Prop
  | bot {r : R} (hr : P r) (t : CallTree E R) : FuelLeB P (.ret r) t
  | ret (r : R) : FuelLeB P (.ret r) (.ret r)
  | vis (e : E.Event) {k k' : E.Resp e → CallTree E R} (h : ∀ a, FuelLeB P (k a) (k' a)) :
      FuelLeB P (.vis e k) (.vis e k')

/-- The fuel order is reflexive. -/
theorem FuelLeB.refl {R : Type} (P : R → Prop) : ∀ t : CallTree E R, FuelLeB P t t
  | .ret r => .ret r
  | .vis e k => .vis e fun a => FuelLeB.refl P (k a)

/-- **Sequencing is monotone in the fuel order**: a bottom leaf of the first tree continues with
    a bottom leaf, and the continuations are related at the other leaves. -/
theorem FuelLeB.bind {α β : Type} {P : α → Prop} {Q : β → Prop} {t t' : CallTree E α}
    {k k' : α → CallTree E β} (h : FuelLeB P t t')
    (hbot : ∀ a, P a → ∃ b, k a = .ret b ∧ Q b)
    (hk : ∀ a, ¬ P a → FuelLeB Q (k a) (k' a)) : FuelLeB Q (t.bind k) (t'.bind k') := by
  induction h with
  | bot hr t =>
    obtain ⟨b, hb, hq⟩ := hbot _ hr
    simp only [CallTree.bind, hb]
    exact .bot hq _
  | ret r =>
    by_cases hr : P r
    · obtain ⟨b, hb, hq⟩ := hbot _ hr
      simp only [CallTree.bind, hb]
      exact .bot hq _
    · exact hk r hr
  | vis e _ ih => exact .vis e fun a => ih a

/-- Mapping the leaves by a read-back that is undefined at the bottom leaves turns the fuel
    order with a bottom predicate into `FuelLe`. -/
theorem FuelLeB.map_fuelLe {R V : Type} {P : R → Prop} {rb : R → Option V}
    (hrb : ∀ r, P r → rb r = none) {t t' : CallTree E R} (h : FuelLeB P t t') :
    FuelLe (t.bind fun r => .ret (rb r)) (t'.bind fun r => .ret (rb r)) := by
  induction h with
  | bot hr t => simp only [CallTree.bind, hrb _ hr]; exact .none _
  | ret r => exact .ret _
  | vis e _ ih => exact .vis e fun a => ih a

end Order

/-! ## The order on stateful tree computations -/

section TM

variable {E : EventSig}

/-- The fuel order on stateful tree computations: at every environment, the trees are related
    with the bottom predicate `P` on the result. -/
def TMLe {α : Type} (P : α → Prop) (x x' : TM E α) : Prop :=
  ∀ env, FuelLeB (fun r : α × Env => P r.1) (x env) (x' env)

/-- A return is below itself. -/
theorem TMLe.pure {α : Type} (P : α → Prop) (a : α) :
    TMLe (E := E) P (Pure.pure a) (Pure.pure a) :=
  fun _ => .ret _

/-- A return of a bottom value is below every computation. -/
theorem TMLe.bot {α : Type} {P : α → Prop} {a : α} (ha : P a) (x' : TM E α) :
    TMLe P (Pure.pure a) x' :=
  fun env => FuelLeB.bot (P := fun r : α × Env => P r.1) (r := (a, env)) ha (x' env)

/-- **Sequencing of stateful tree computations is monotone.** -/
theorem TMLe.bind {α β : Type} {P : α → Prop} {Q : β → Prop} {x x' : TM E α}
    {f f' : α → TM E β} (hx : TMLe P x x')
    (hbot : ∀ a, P a → ∀ s, ∃ b, f a s = .ret b ∧ Q b.1)
    (hf : ∀ a, ¬ P a → TMLe Q (f a) (f' a)) : TMLe Q (x >>= f) (x' >>= f') := by
  intro env
  exact FuelLeB.bind (hx env) (fun r hr => hbot r.1 hr r.2) (fun r hr => hf r.1 hr r.2)

/-- Sequencing after the same computation on both sides is monotone in the continuation. -/
theorem TMLe.bind_refl {α β : Type} {Q : β → Prop} (x : TM E α) {f f' : α → TM E β}
    (hf : ∀ a, TMLe Q (f a) (f' a)) : TMLe Q (x >>= f) (x >>= f') :=
  TMLe.bind (P := fun _ => False) (fun _ => FuelLeB.refl _ _) (fun _ h => h.elim)
    (fun a _ => hf a)

/-- The bottom predicate of outcomes: the errors. -/
abbrev ErrO (o : Outcome) : Prop := ∃ m, o = .err m

/-- The bottom predicate of optional results: `none`. -/
abbrev NoneO {α : Type} (o : Option α) : Prop := o = none

/-- The fuel order on tree tables: at every call, the trees are related with the bottom leaf
    `none`. -/
def TabLe (bt bt' : TreeTable E) : Prop :=
  ∀ g vals, FuelLeB NoneO (bt g vals) (bt' g vals)

/-- A call of related tables, lifted to stateful computations, is monotone. -/
theorem TMLe.lift {bt bt' : TreeTable E} (hbt : TabLe bt bt') (g : String) (vals : List Value) :
    TMLe NoneO (StateT.lift (bt g vals) : TM E (Option Value)) (StateT.lift (bt' g vals)) := by
  intro env
  refine FuelLeB.bind (hbt g vals) ?_ ?_
  · rintro _ rfl
    exact ⟨_, rfl, rfl⟩
  · intro a _
    exact .ret _

end TM

/-! ## Fuel monotonicity of the reading at a tree table -/

section Reading

variable {E : EventSig}

/-- One step of the monotonicity proof: equal returns, a bottom return, an induction
    hypothesis, a sequence, or a case split. -/
local syntax "mono_step" : tactic

/-- The bottom leaves of a sequence continue with a bottom leaf. -/
local syntax "mono_bot" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| mono_bot) => `(tactic| first
      | (rintro _ ⟨_, rfl⟩ _; exact ⟨_, rfl, _, rfl⟩)
      | (rintro _ ⟨_, rfl⟩ _; exact ⟨_, rfl, rfl⟩)
      | (rintro _ rfl _; exact ⟨_, rfl, rfl⟩)
      | (rintro _ rfl _; exact ⟨_, rfl, _, rfl⟩)
      | (rintro _ ⟨m, rfl⟩ s; exact ⟨(.err m, s), by cases ‹Value› <;> rfl, m, rfl⟩))

macro_rules
  | `(tactic| mono_step) => `(tactic| first
      | exact TMLe.pure _ _
      | exact TMLe.bot ⟨_, rfl⟩ _
      | exact TMLe.bot rfl _
      | (apply_assumption <;> omega)
      | exact TMLe.lift ‹TabLe _ _› _ _
      | (refine TMLe.bind_refl _ fun _ => ?_; (try dsimp only); mono_step)
      | (apply TMLe.bind; mono_step; mono_bot; intro _ _; (try dsimp only); mono_step)
      | (exfalso; omega)
      | (split <;> (try (rename_i hq; rw [hq])) <;> mono_step)
      | (exfalso; grind))

/-- **Fuel monotonicity of the reading at a tree table**, for all thirteen readings at once:
    at a larger table and a larger fuel, the tree of a reading is above the tree at the smaller
    ones, with the error outcomes (for the arguments, the result `none`) at the bottom. -/
theorem denoteT_mono_and (bt bt' : TreeTable E) (hbt : TabLe bt bt') :
    (∀ fuel e, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteT bt fuel e) (denoteT bt' fuel' e)) ∧
    (∀ fuel c b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteWhileReturnT bt fuel c b) (denoteWhileReturnT bt' fuel' c b)) ∧
    (∀ fuel x lo hi b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteForLoopRevReturnT bt fuel x lo hi b)
        (denoteForLoopRevReturnT bt' fuel' x lo hi b)) ∧
    (∀ fuel x lo hi b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteForLoopReturnT bt fuel x lo hi b)
        (denoteForLoopReturnT bt' fuel' x lo hi b)) ∧
    (∀ fuel c b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteWhileT bt fuel c b) (denoteWhileT bt' fuel' c b)) ∧
    (∀ fuel x lo hi b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteForLoopRevT bt fuel x lo hi b) (denoteForLoopRevT bt' fuel' x lo hi b)) ∧
    (∀ fuel x lo hi b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteForLoopT bt fuel x lo hi b) (denoteForLoopT bt' fuel' x lo hi b)) ∧
    (∀ fuel c b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteWhileOrigT bt fuel c b) (denoteWhileOrigT bt' fuel' c b)) ∧
    (∀ fuel x lo hi b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteForLoopRevOrigT bt fuel x lo hi b)
        (denoteForLoopRevOrigT bt' fuel' x lo hi b)) ∧
    (∀ fuel x lo hi b, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteForLoopOrigT bt fuel x lo hi b)
        (denoteForLoopOrigT bt' fuel' x lo hi b)) ∧
    (∀ fuel v arms, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteMatchArmsT bt fuel v arms) (denoteMatchArmsT bt' fuel' v arms)) ∧
    (∀ fuel args, ∀ fuel', fuel ≤ fuel' →
      TMLe NoneO (denoteArgsT bt fuel args) (denoteArgsT bt' fuel' args)) ∧
    (∀ fuel f args, ∀ fuel', fuel ≤ fuel' →
      TMLe ErrO (denoteAppT bt fuel f args) (denoteAppT bt' fuel' f args)) := by
  apply denoteT.mutual_induct
  all_goals intros
  all_goals first
    | simp only [denoteT]
    | rw [denoteWhileReturnT.eq_1 bt', denoteWhileReturnT.eq_1 bt]
    | rw [denoteForLoopRevReturnT.eq_1 bt', denoteForLoopRevReturnT.eq_1 bt]
    | rw [denoteForLoopReturnT.eq_1 bt', denoteForLoopReturnT.eq_1 bt]
    | rw [denoteWhileT.eq_1 bt', denoteWhileT.eq_1 bt]
    | rw [denoteForLoopRevT.eq_1 bt', denoteForLoopRevT.eq_1 bt]
    | rw [denoteForLoopT.eq_1 bt', denoteForLoopT.eq_1 bt]
    | rw [denoteWhileOrigT.eq_1 bt', denoteWhileOrigT.eq_1 bt]
    | rw [denoteForLoopRevOrigT.eq_1 bt', denoteForLoopRevOrigT.eq_1 bt]
    | rw [denoteForLoopOrigT.eq_1 bt', denoteForLoopOrigT.eq_1 bt]
    | simp only [denoteMatchArmsT]
    | simp only [denoteArgsT]
    | rw [denoteAppT.eq_1 bt', denoteAppT.eq_1 bt]
  all_goals mono_step

/-- **Fuel monotonicity of `denoteT`** at a larger table and a larger fuel. -/
theorem denoteT_mono {bt bt' : TreeTable E} (hbt : TabLe bt bt') {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') (e : ImpExpr) : TMLe ErrO (denoteT bt fuel e) (denoteT bt' fuel' e) :=
  (denoteT_mono_and bt bt' hbt).1 fuel e fuel' hle

/-- The closure table is monotone in the table and the fuel. -/
theorem closureTableT_mono {bt bt' : TreeTable E} (hbt : TabLe bt bt') {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') (f : String) (ps : List String) (body : ImpExpr) (ρ : Env) :
    TabLe (closureTableT bt fuel f ps body ρ) (closureTableT bt' fuel' f ps body ρ) := by
  intro g vals
  unfold closureTableT
  split_ifs
  · refine FuelLeB.bind (denoteT_mono hbt hle body _) ?_ fun _ _ => FuelLeB.refl _ _
    rintro ⟨_, _⟩ ⟨m, rfl⟩
    exact ⟨_, rfl, rfl⟩
  · exact FuelLeB.refl _ _
  · exact hbt g vals

/-- **Fuel monotonicity of the spine reading** at a larger table and a larger fuel. -/
theorem denoteSpineT_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel') (e : ImpExpr) :
    ∀ {bt bt' : TreeTable E}, TabLe bt bt' →
      TMLe ErrO (denoteSpineT bt fuel e) (denoteSpineT bt' fuel' e) := by
  intro bt
  induction bt, e using denoteSpineT.induct fuel with
  | case1 bt f ps body cont hc ih =>
    intro bt' hbt
    simp only [denoteSpineT, hc, ↓reduceIte]
    exact TMLe.bind_refl _ fun ρ => ih ρ (closureTableT_mono hbt hle f ps body ρ)
  | case2 bt f ps body cont hc =>
    intro bt' hbt
    simp only [denoteSpineT, hc, Bool.false_eq_true, ↓reduceIte]
    exact denoteT_mono hbt hle _
  | case3 bt x v cont hv ih =>
    intro bt' hbt
    rw [denoteSpineT.eq_2 _ _ _ _ _ hv, denoteSpineT.eq_2 _ _ _ _ _ hv]
    apply TMLe.bind (denoteT_mono hbt hle v)
    · mono_bot
    · intro a _
      split
      all_goals first
        | exact TMLe.pure _ _
        | exact TMLe.bind_refl _ fun _ => ih hbt
  | case4 bt a b ih =>
    intro bt' hbt
    rw [denoteSpineT.eq_3, denoteSpineT.eq_3]
    apply TMLe.bind (denoteT_mono hbt hle a)
    · mono_bot
    · intro r _
      split
      all_goals first
        | exact TMLe.pure _ _
        | exact ih hbt
  | case5 bt e h1 h2 h3 =>
    intro bt' hbt
    rw [denoteSpineT.eq_4 _ _ _ h1 h2 h3, denoteSpineT.eq_4 _ _ _ h1 h2 h3]
    exact denoteT_mono hbt hle e

/-- **Fuel monotonicity of the call tree** at a larger table and a larger fuel, with the error
    outcomes at the bottom. -/
theorem nfTree_mono {bt bt' : TreeTable E} (hbt : TabLe bt bt') {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') (e : ImpExpr) (env : Env) :
    FuelLeB (fun r : Outcome × Env => ErrO r.1) (nfTree bt fuel e env)
      (nfTree bt' fuel' e env) :=
  denoteSpineT_mono hle e hbt env

end Reading

/-! ## The tree table of a module is increasing in its function fuel -/

section Module

open CatCrypt.Crypto.Hax (HaxModule ModFn hax64WExit)

/-- The table `refBiT` is monotone in the table and the function fuel, at every depth. -/
theorem refBiT_mono {E : EventSig} (fs : List ModFn) {bt bt' : TreeTable E} (hbt : TabLe bt bt')
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') :
    ∀ n, TabLe (refBiT fs bt fuel n) (refBiT fs bt' fuel' n) := by
  intro n
  induction n with
  | zero =>
    intro g vals
    simp only [refBiT]
    split
    · exact FuelLeB.refl _ _
    · exact hbt g vals
  | succ n ih =>
    intro g vals
    simp only [refBiT]
    split
    · refine FuelLeB.bind (nfTree_mono ih hle _ _) ?_ fun _ _ => FuelLeB.refl _ _
      rintro ⟨_, _⟩ ⟨m, rfl⟩
      exact ⟨_, rfl, rfl⟩
    · exact hbt g vals

/-- **The tree table of a module is increasing in its function fuel.** -/
theorem moduleTreeTable_mono (m : HaxModule) (bi : Builtins) {fuelC fuelC' : Nat}
    (hle : fuelC ≤ fuelC') : TabLe (moduleTreeTable m bi fuelC) (moduleTreeTable m bi fuelC') :=
  refBiT_mono m.fns (fun _ _ => FuelLeB.refl _ _) hle m.depth

/-- **Fuel monotonicity of the source call tree along the diagonal**: at `fuelC = fuel = n`,
    the call tree of the module is below the call tree at every larger `n`, with the error
    outcomes at the bottom. -/
theorem nfTree_diag_mono (m : HaxModule) (bi : Builtins) (e : ImpExpr) (env : Env) {n n' : Nat}
    (hle : n ≤ n') :
    FuelLeB (fun r : Outcome × Env => ErrO r.1) (nfTree (moduleTreeTable m bi n) n e env)
      (nfTree (moduleTreeTable m bi n') n' e env) :=
  nfTree_mono (moduleTreeTable_mono m bi hle) hle e env

end Module

/-! ## The source interpretation at a general handler -/

section Interp

open CatCrypt.Crypto.Hax (HaxModule hax64WExit)
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuelSource (srcChain interpSrcω)

/-- Interpretation in `SPComp` is a monad morphism: interpreting a sequence binds the
    interpretation of the continuation. -/
theorem interpSP_bind {E : EventSig} {α β : Type} (h : ∀ e : E.Event, SPComp (E.Resp e))
    (t : CallTree E α) (k : α → CallTree E β) :
    interpSP h (t.bind k) = (interpSP h t).bind fun a => interpSP h (k a) := by
  induction t with
  | ret a => simp only [CallTree.bind, interpSP_ret, SPComp.pure_bind]
  | vis e c ih => simp only [CallTree.bind, interpSP_vis, SPComp.bind_assoc, ih]

/-- The interpretation of a tree with its leaves mapped by a read-back, with the leaf `none`
    read as failure, is the read-back of the interpretation of the tree. -/
theorem interpSPOpt_bind_ret {E : EventSig} {α V : Type} (h : ∀ e : E.Event, SPComp (E.Resp e))
    (t : CallTree E α) (rb : α → Option V) :
    interpSPOpt h (t.bind fun r => .ret (rb r)) = readBack rb (interpSP h t) := by
  simp only [interpSPOpt, interpSP_bind, interpSP_ret, SPComp.bind_assoc, SPComp.pure_bind,
    readBack]

/-- The read-back of a source leaf with an error outcome is undefined. -/
theorem srcRead_of_err {r : Outcome × Env} (hr : ErrO r.1) : srcRead r = none := by
  obtain ⟨m, hm⟩ := hr
  simp [srcRead, hm]

/-- The source call tree of the module `m` from the environment `env` at the diagonal fuel `n`,
    its leaves read back by `srcRead`. -/
def srcTree (m : HaxModule) (env : Env) (n : Nat) : CallTree linkSig (Option Value) :=
  (nfTree (moduleTreeTable m hax64WExit n) n m.entry.erase env).bind fun r => .ret (srcRead r)

/-- **The source call trees along the diagonal are increasing in the fuel order.** -/
theorem srcTree_fuelLe (m : HaxModule) (env : Env) {n n' : Nat} (hle : n ≤ n') :
    FuelLe (srcTree m env n) (srcTree m env n') :=
  (nfTree_diag_mono m hax64WExit _ env hle).map_fuelLe fun _ => srcRead_of_err

/-- The source call trees along the diagonal form an increasing family. -/
theorem fuelMono_srcTree (m : HaxModule) (env : Env) : FuelMono (srcTree m env) :=
  fun n => srcTree_fuelLe m env n.le_succ

/-- **Monotonicity of the interpreted source leaf under every handler**: along the diagonal of
    the fuels, the read-back of the source interpretation under `h` is increasing. -/
theorem readBack_srcTree_mono (h : ∀ e : linkSig.Event, SPComp (linkSig.Resp e))
    (m : HaxModule) (env : Env) {n n' : Nat} (hle : n ≤ n') :
    readBack srcRead (interpSP h (nfTree (moduleTreeTable m hax64WExit n) n m.entry.erase env)) ≤
      readBack srcRead
        (interpSP h (nfTree (moduleTreeTable m hax64WExit n') n' m.entry.erase env)) := by
  rw [← interpSPOpt_bind_ret, ← interpSPOpt_bind_ret]
  exact interpSPOpt_mono h (srcTree_fuelLe m env hle)

/-- **The source interpretation without fuel under the handler `h`**: the supremum over the
    diagonal fuel of the read-backs of the source interpretations under `h`. -/
noncomputable def interpSrcωH (h : ∀ e : linkSig.Event, SPComp (linkSig.Resp e))
    (m : HaxModule) (env : Env) : SPComp Value :=
  interpSPω h (srcTree m env) (fuelMono_srcTree m env)

/-- **The divergence mass of the source under the handler `h`**: the failure weight of
    `interpSrcωH`. -/
noncomputable def srcDivH (h : ∀ e : linkSig.Event, SPComp (linkSig.Resp e)) (m : HaxModule)
    (env : Env) : ℝ≥0∞ :=
  ⨆ s, interpSrcωH h m env s none

/-- The weight of a value under `interpSrcωH` is the supremum over the diagonal fuel of its
    weights under the read-backs of the source interpretations. -/
theorem interpSrcωH_apply_some (h : ∀ e : linkSig.Event, SPComp (linkSig.Resp e))
    (m : HaxModule) (env : Env) (s : Heap) (p : Value × Heap) :
    interpSrcωH h m env s (some p) = ⨆ n, readBack srcRead
      (interpSP h (nfTree (moduleTreeTable m hax64WExit n) n m.entry.erase env)) s (some p) := by
  rw [interpSrcωH, interpSPω_apply_some]
  simp only [srcTree, interpSPOpt_bind_ret]

/-- The read-back of the source interpretation at every diagonal fuel is below `interpSrcωH`. -/
theorem readBack_le_interpSrcωH (h : ∀ e : linkSig.Event, SPComp (linkSig.Resp e))
    (m : HaxModule) (env : Env) (n : Nat) :
    readBack srcRead (interpSP h (nfTree (moduleTreeTable m hax64WExit n) n m.entry.erase env)) ≤
      interpSrcωH h m env := by
  rw [← interpSPOpt_bind_ret]
  exact le_ωSup (interpChain h (srcTree m env) (fuelMono_srcTree m env)) n

/-- At the point masses of the handler of the linked functions, `interpSrcωH` is the source
    interpretation without fuel `interpSrcω`. -/
theorem interpSrcωH_linkHandler (m : HaxModule) (env : Env) :
    interpSrcωH (fun e => SPComp.pure (linkHandler m e)) m env = interpSrcω m env := by
  unfold interpSrcωH interpSPω interpSrcω
  congr 1
  apply DFunLike.ext
  intro n
  change interpSPOpt _ (srcTree m env n) = readBack _ _
  rw [srcTree, interpSPOpt_bind_ret]

end Interp

end CatCrypt.Crypto.SecureCompilation.Haxc.NFTreeFuelMono
