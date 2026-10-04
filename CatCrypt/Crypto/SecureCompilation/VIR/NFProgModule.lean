/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel

/-!
# Modules of `NFProg` functions and the call-environment link theorems

A module is an ordered list of function definitions `FnDef d`, each a symbol name, a
signature `args → rets` and a body `NFProg d args rets`. The call environment of a module
over a base environment of external kernels is built by structural recursion on the list:
the body of an entry is denoted at the environment of the entries after it, so a symbol
cannot call itself or an earlier entry, and no call fuel is needed.

The link theorems compare the denotations of one program at two call environments.

* Congruence: environments that agree at every symbol and signature the program calls
  give equal denotations.
* Monotonicity: if every successful call of the first environment succeeds with the same
  result in the second, every successful run at the first environment is a run at the
  second. With the first environment a reference guarded by preconditions
  (`CallEnv.guard`), a caller that meets every precondition runs the same with any kernel
  agreeing with the reference on its precondition.
* The call constructor rules, in bisimulation and forward form, between two dialects.
* `TableRel`: across a multi-value lowering with a representation family, each graded call
  of the source environment is matched by a call of the target environment at the
  flattened signature with related results. `TableRel.update` replaces the target callee
  of one symbol by a kernel proved against the symbol's contract.

## Main definitions

* `CallEnv.extend` — the environment with one symbol and signature bound to a callee.
* `CallEnv.guard` — the environment refusing the calls outside a precondition.
* `FnDef`, `Module`, `Module.env` — function definitions, modules and their environment.
* `CallXfer` — the grade transfer of the symbols of a dialect.
* `TableRel` — the relation of two call environments across a multi-value lowering.
* `SymContract` — the contract of a target callee of one symbol.

## Main results

* `CallEnv.extend_call_self`, `CallEnv.extend_call_of_ne` — the equations of `extend`.
* `CallEnv.guard_call_eq_some` — a successful guarded call meets the precondition and is a
  call of the underlying environment.
* `Module.env_cons_call_self` — the head entry of a module denotes its body at the
  environment of the tail.
* `NFProg.denoteAt_call` — the equation of the call node at an explicit environment.
* `NFProg.denoteAt_congr` — environments agreeing at the calls of a program give equal
  denotations.
* `NFProg.denoteAt_mono` — a run at an environment is a run at every environment that
  extends it at the calls of the program.
* `NFProg.denoteAt_mono_guard` — the instance of `denoteAt_mono` at a guarded reference.
* `NFProg.denote_call_rel`, `NFProg.denote_call_rel_fwd` — the call constructor rules.
* `TableRel.update` — a kernel meeting the contract of a symbol replaces its target callee.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend MultiBlockLoweringData)
open MultiBlockLoweringRel (RepFamily FlatRel)

/-! ## 1. Extension and guarding of a call environment -/

namespace CallEnv

variable {d : Dialect.{0, 0}} [TyDenote d.Ty]

/-- The environment `E` with the symbol `f` at the signature `as → rs` bound to `sem`;
    every other symbol or signature is looked up in `E`. -/
def extend [DecidableEq d.Ty] (E : CallEnv d) (f : String) (as rs : List d.Ty)
    (sem : Valuation as → Option (Valuation rs)) : CallEnv d where
  call g as' rs' :=
    if h : g = f ∧ as' = as ∧ rs' = rs then fun x =>
      cast (congrArg (fun l => Option (Valuation l)) h.2.2.symm)
        (sem (cast (congrArg Valuation h.2.1) x))
    else E.call g as' rs'

/-- The extended symbol at its signature calls the bound callee. -/
@[simp] theorem extend_call_self [DecidableEq d.Ty] (E : CallEnv d) (f : String)
    (as rs : List d.Ty) (sem : Valuation as → Option (Valuation rs)) (x : Valuation as) :
    (E.extend f as rs sem).call f as rs x = sem x := by
  simp only [extend, and_self, dite_true]
  rfl

/-- Every other symbol or signature is looked up in the underlying environment. -/
theorem extend_call_of_ne [DecidableEq d.Ty] (E : CallEnv d) {f g : String}
    {as rs as' rs' : List d.Ty} (sem : Valuation as → Option (Valuation rs))
    (h : ¬(g = f ∧ as' = as ∧ rs' = rs)) (x : Valuation as') :
    (E.extend f as rs sem).call g as' rs' x = E.call g as' rs' x := by
  simp only [extend, dif_neg h]

/-- The environment `E` restricted to the calls satisfying `pre`: a call outside `pre`
    refuses. -/
noncomputable def guard (E : CallEnv d) (pre : (f : String) → (as : List d.Ty) →
    List d.Ty → Valuation as → Prop) : CallEnv d where
  call f as rs x := by
    classical
    exact if pre f as rs x then E.call f as rs x else none

/-- A successful guarded call meets the precondition and is a call of the underlying
    environment. -/
theorem guard_call_eq_some (E : CallEnv d)
    (pre : (f : String) → (as : List d.Ty) → List d.Ty → Valuation as → Prop) {f : String}
    {as rs : List d.Ty} {x : Valuation as} {y : Valuation rs}
    (h : (E.guard pre).call f as rs x = some y) : pre f as rs x ∧ E.call f as rs x = some y := by
  classical
  simp only [guard] at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-- A guarded call meeting the precondition is a call of the underlying environment. -/
theorem guard_call_of_pre (E : CallEnv d)
    (pre : (f : String) → (as : List d.Ty) → List d.Ty → Valuation as → Prop) {f : String}
    {as rs : List d.Ty} {x : Valuation as} (h : pre f as rs x) :
    (E.guard pre).call f as rs x = E.call f as rs x := by
  classical
  simp only [guard, if_pos h]

end CallEnv

/-! ## 2. Modules -/

section Module

variable (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- A function definition: a symbol name, a signature `args → rets` and a body. -/
structure FnDef where
  /-- The symbol name. -/
  name : String
  /-- The argument types. -/
  args : List d.Ty
  /-- The result types. -/
  rets : List d.Ty
  /-- The body, over the arguments. -/
  body : NFProg d args rets

/-- A module: an ordered list of function definitions. A body calls only the entries
    after it or the base environment. -/
abbrev Module : Type := List (FnDef d)

variable {d} [DialectDenoteM d Option] [DecidableEq d.Ty]

/-- The call environment of a module over the base environment `base` of external
    kernels: each entry is bound to the denotation of its body at the environment of the
    entries after it. -/
def Module.env (base : CallEnv d) (fuel : Nat) : Module d → CallEnv d
  | [] => base
  | fd :: M =>
      (Module.env base fuel M).extend fd.name fd.args fd.rets
        (fd.body.denoteAt (Module.env base fuel M) fuel)

/-- The head entry of a module denotes its body at the environment of the tail. -/
theorem Module.env_cons_call_self (base : CallEnv d) (fuel : Nat) (fd : FnDef d)
    (M : Module d) (x : Valuation fd.args) :
    (Module.env base fuel (fd :: M)).call fd.name fd.args fd.rets x =
      fd.body.denoteAt (Module.env base fuel M) fuel x :=
  CallEnv.extend_call_self _ _ _ _ _ x

/-- A symbol or signature other than the head entry's is looked up in the environment of
    the tail. -/
theorem Module.env_cons_call_of_ne (base : CallEnv d) (fuel : Nat) (fd : FnDef d)
    (M : Module d) {g : String} {as rs : List d.Ty}
    (h : ¬(g = fd.name ∧ as = fd.args ∧ rs = fd.rets)) (x : Valuation as) :
    (Module.env base fuel (fd :: M)).call g as rs x = (Module.env base fuel M).call g as rs x :=
  CallEnv.extend_call_of_ne _ _ h x

end Module

/-! ## 3. Congruence and monotonicity in the call environment -/

namespace NFProg

section Link

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option]

/-- A call denotes its callee in `E` at the looked-up arguments, then its continuation at
    the results. -/
theorem denoteAt_call (E : CallEnv d) {Γ : Ctxt d} {as rs ts : List d.Ty} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts) (fuel : Nat)
    (V : Valuation Γ) :
    (NFProg.call f args k).denoteAt E fuel V =
      E.call f as rs (Expr.lookupArgs args V) >>= fun r => k.denoteAt E fuel (hvAppend r V) :=
  rfl

/-- **Congruence.** Two call environments that agree at every symbol and signature the
    program calls give equal denotations. -/
theorem denoteAt_congr {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (E₁ E₂ : CallEnv d)
    (h : ∀ f as rs (x : Valuation as), p.Calls f as rs → E₁.call f as rs x = E₂.call f as rs x)
    (fuel : Nat) (V : Valuation Γ) :
    p.denoteAt E₁ fuel V = p.denoteAt E₂ fuel V := by
  unfold denoteAt
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [denote, ih h]
  | forLoop count inits body k ihb ihk =>
      simp only [denote, ihb (fun f as rs x hc => h f as rs x (Or.inl hc)),
        ihk (fun f as rs x hc => h f as rs x (Or.inr hc))]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [denote, iht (fun f as rs x hc => h f as rs x (Or.inl hc)),
        ihe (fun f as rs x hc => h f as rs x (Or.inr (Or.inl hc))),
        ihk (fun f as rs x hc => h f as rs x (Or.inr (Or.inr hc)))]
  | whileLoop inits body k ihb ihk =>
      simp only [denote, ihb (fun f as rs x hc => h f as rs x (Or.inl hc)),
        ihk (fun f as rs x hc => h f as rs x (Or.inr hc))]
  | call f args k ih =>
      simp only [denote, ih (fun f as rs x hc => h f as rs x (Or.inr hc))]
      rw [h f _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩)]

/-- **Monotonicity.** If every successful call of `E₁` at a symbol and signature the
    program calls succeeds with the same result in `E₂`, every successful run of the
    program at `E₁` is a run at `E₂` with the same result. -/
theorem denoteAt_mono {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (E₁ E₂ : CallEnv d)
    (h : ∀ f as rs (x : Valuation as) (y : Valuation rs), p.Calls f as rs →
      E₁.call f as rs x = some y → E₂.call f as rs x = some y)
    (fuel : Nat) (V : Valuation Γ) (out : Valuation ts)
    (hout : p.denoteAt E₁ fuel V = some out) : p.denoteAt E₂ fuel V = some out := by
  unfold denoteAt at hout ⊢
  induction p with
  | ret vs => exact hout
  | var e k ih =>
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hout ⊢
      obtain ⟨x, hx, hk⟩ := hout
      exact ⟨x, hx, ih h _ _ hk⟩
  | forLoop count inits body k ihb ihk =>
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hout ⊢
      obtain ⟨acc, hacc, hk⟩ := hout
      refine ⟨acc, ?_, ihk (fun f as rs x y hc => h f as rs x y (Or.inr hc)) _ _ hk⟩
      obtain ⟨acc', hacc', rfl⟩ := foldlM_rel_fwd (R := Eq) _
        (fun i _ a a' b hr hb => ⟨b, by
          subst hr
          exact ihb (fun f as rs x y hc => h f as rs x y (Or.inl hc)) _ _ hb, rfl⟩)
        _ _ acc rfl hacc
      exact hacc'
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hout ⊢
      obtain ⟨r, hr, hk⟩ := hout
      refine ⟨r, ?_, ihk (fun f as rs x y hc => h f as rs x y (Or.inr (Or.inr hc))) _ _ hk⟩
      split at hr
      · rw [if_pos ‹_›]
        exact iht (fun f as rs x y hc => h f as rs x y (Or.inl hc)) _ _ hr
      · rw [if_neg ‹_›]
        exact ihe (fun f as rs x y hc => h f as rs x y (Or.inr (Or.inl hc))) _ _ hr
  | whileLoop inits body k ihb ihk =>
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hout ⊢
      obtain ⟨acc, hacc, hk⟩ := hout
      refine ⟨acc, ?_, ihk (fun f as rs x y hc => h f as rs x y (Or.inr hc)) _ _ hk⟩
      obtain ⟨acc', hacc', rfl⟩ := whileIter_rel_fwd (R := Eq)
        (fun a a' r hr hb => ⟨r, by
          subst hr
          exact ihb (fun f as rs x y hc => h f as rs x y (Or.inl hc)) _ _ hb, rfl, rfl⟩)
        _ _ _ acc rfl hacc
      exact hacc'
  | call f args k ih =>
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hout ⊢
      obtain ⟨r, hr, hk⟩ := hout
      exact ⟨r, h f _ _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩) hr,
        ih (fun f as rs x y hc => h f as rs x y (Or.inr hc)) _ _ hk⟩

/-- **Monotonicity at a guarded reference.** A run of the program at the reference
    environment `Eref` guarded by `pre` is a run with the same result at every environment
    `E` that agrees with `Eref` on the successful calls meeting `pre`. -/
theorem denoteAt_mono_guard {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (Eref E : CallEnv d)
    (pre : (f : String) → (as : List d.Ty) → List d.Ty → Valuation as → Prop)
    (h : ∀ f as rs (x : Valuation as) (y : Valuation rs), p.Calls f as rs → pre f as rs x →
      Eref.call f as rs x = some y → E.call f as rs x = some y)
    (fuel : Nat) (V : Valuation Γ) (out : Valuation ts)
    (hout : p.denoteAt (Eref.guard pre) fuel V = some out) : p.denoteAt E fuel V = some out :=
  denoteAt_mono p _ E (fun f as rs x y hc hy =>
    let hg := CallEnv.guard_call_eq_some Eref pre hy
    h f as rs x y hc hg.1 hg.2) fuel V out hout

end Link

/-! ## 4. The call constructor between two dialects -/

section CallRel

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option] [DialectSignature d'] [TyDenote d'.Ty]
  [HasWord64 d'] [HasBoolBit d'] [DialectDenoteM d' Option]

/-- **The call constructor, bisimulation form.** Two calls over related valuations, with
    `Ra`-related looked-up arguments, callees that send `Ra`-related arguments to
    `Option.Rel Rr`-related results, and continuations that send `Rr`-related results to
    `S`-related results, denote `S`-related results. The environments, symbols and fuels of
    the two sides may differ. -/
theorem denote_call_rel (E : CallEnv d) (E' : CallEnv d') {Γ : Ctxt d} {as rs ts : List d.Ty}
    {Γ' : Ctxt d'} {as' rs' ts' : List d'.Ty} (fuel fuel' : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Ra : Valuation as → Valuation as' → Prop}
    {Rr : Valuation rs → Valuation rs' → Prop} {S : Valuation ts → Valuation ts' → Prop}
    (f : String) (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts)
    (f' : String) (args' : HVector (fun t => Var Γ' t) as') (k' : NFProg d' (rs' ++ Γ') ts')
    (hargs : ∀ V V', RΓ V V' → Ra (Expr.lookupArgs args V) (Expr.lookupArgs args' V'))
    (hcall : ∀ a a', Ra a a' → Option.Rel Rr (E.call f as rs a) (E'.call f' as' rs' a'))
    (hk : ∀ V V', RΓ V V' → ∀ r r', Rr r r' →
      Option.Rel S (k.denoteAt E fuel (hvAppend r V)) (k'.denoteAt E' fuel' (hvAppend r' V')))
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') :
    Option.Rel S ((NFProg.call f args k).denoteAt E fuel V)
      ((NFProg.call f' args' k').denoteAt E' fuel' V') := by
  rw [denoteAt_call, denoteAt_call]
  exact bind_rel (hcall _ _ (hargs V V' hV)) (hk V V' hV)

/-- **The call constructor, forward form.** -/
theorem denote_call_rel_fwd (E : CallEnv d) (E' : CallEnv d') {Γ : Ctxt d}
    {as rs ts : List d.Ty} {Γ' : Ctxt d'} {as' rs' ts' : List d'.Ty} (fuel fuel' : Nat)
    {RΓ : Valuation Γ → Valuation Γ' → Prop} {Ra : Valuation as → Valuation as' → Prop}
    {Rr : Valuation rs → Valuation rs' → Prop} {S : Valuation ts → Valuation ts' → Prop}
    (f : String) (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts)
    (f' : String) (args' : HVector (fun t => Var Γ' t) as') (k' : NFProg d' (rs' ++ Γ') ts')
    (hargs : ∀ V V', RΓ V V' → Ra (Expr.lookupArgs args V) (Expr.lookupArgs args' V'))
    (hcall : ∀ a a' r, Ra a a' → E.call f as rs a = some r →
      ∃ r', E'.call f' as' rs' a' = some r' ∧ Rr r r')
    (hk : ∀ V V', RΓ V V' → ∀ r r' b, Rr r r' → k.denoteAt E fuel (hvAppend r V) = some b →
      ∃ b', k'.denoteAt E' fuel' (hvAppend r' V') = some b' ∧ S b b')
    (V : Valuation Γ) (V' : Valuation Γ') (hV : RΓ V V') (out : Valuation ts)
    (h : (NFProg.call f args k).denoteAt E fuel V = some out) :
    ∃ out', (NFProg.call f' args' k').denoteAt E' fuel' V' = some out' ∧ S out out' := by
  rw [denoteAt_call] at h
  rw [denoteAt_call]
  exact bind_rel_fwd (fun r hr => hcall _ _ r (hargs V V' hV) hr) (hk V V' hV) out h

end CallRel

end NFProg

/-! ## 5. Call environments across a multi-value lowering -/

section Table

variable {d d' : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [TyDenote d'.Ty]
  [DialectSignature d']

/-- The grade transfer of the symbols of a dialect: for a symbol, a signature and the
    grades of the arguments, the grades of the results, or `none` where the symbol has no
    contract. -/
abbrev CallXfer (d : Dialect.{0, 0}) (G : d.Ty → Type) : Type :=
  (f : String) → (as rs : List d.Ty) → HVector G as → Option (HVector G rs)

/-- **The relation of two call environments across a multi-value lowering.** For every
    symbol and grades with a transfer `cx f as rs gs = some gs'`, a successful source call
    on arguments related at `gs` to flattened target arguments is matched by a successful
    target call at the flattened signature whose results are related at `gs'`. -/
def TableRel (L : MultiBlockLoweringData d d') (F : RepFamily L) (cx : CallXfer d F.G)
    (E : CallEnv d) (E' : CallEnv d') : Prop :=
  ∀ f as rs (gs : HVector F.G as) (gs' : HVector F.G rs), cx f as rs gs = some gs' →
    ∀ (x : Valuation as) (W : Valuation (L.mapCtx as)), FlatRel F gs x W →
      ∀ y, E.call f as rs x = some y →
        ∃ W', E'.call f (L.mapCtx as) (L.mapCtx rs) W = some W' ∧ FlatRel F gs' y W'

/-- **The contract of a target callee `K` of the symbol `f` at the signature `as → rs`.**
    On flattened arguments related at the grades `gs` to source arguments on which the
    source call succeeds, `K` succeeds with results related at the transferred grades. -/
def SymContract (L : MultiBlockLoweringData d d') (F : RepFamily L) (cx : CallXfer d F.G)
    (E : CallEnv d) (f : String) (as rs : List d.Ty)
    (K : Valuation (L.mapCtx as) → Option (Valuation (L.mapCtx rs))) : Prop :=
  ∀ (gs : HVector F.G as) (gs' : HVector F.G rs), cx f as rs gs = some gs' →
    ∀ (x : Valuation as) (W : Valuation (L.mapCtx as)), FlatRel F gs x W →
      ∀ y, E.call f as rs x = some y → ∃ W', K W = some W' ∧ FlatRel F gs' y W'

/-- **Kernel replacement.** If the transfer grades the symbol `f` only at the signature
    `as → rs`, a kernel `K` meeting the contract of `f` replaces the target callee of `f`
    at the flattened signature, and the environments stay related. -/
theorem TableRel.update [DecidableEq d'.Ty] {L : MultiBlockLoweringData d d'}
    {F : RepFamily L} {cx : CallXfer d F.G} {E : CallEnv d} {E' : CallEnv d'}
    (hT : TableRel L F cx E E') {f : String} {as rs : List d.Ty}
    {K : Valuation (L.mapCtx as) → Option (Valuation (L.mapCtx rs))}
    (hcx : ∀ as' rs' (gs : HVector F.G as') (gs' : HVector F.G rs'),
      cx f as' rs' gs = some gs' → as' = as ∧ rs' = rs)
    (hK : SymContract L F cx E f as rs K) :
    TableRel L F cx E (E'.extend f (L.mapCtx as) (L.mapCtx rs) K) := by
  intro g as' rs' gs gs' hg x W hW y hy
  by_cases hgf : g = f
  · subst hgf
    obtain ⟨rfl, rfl⟩ := hcx as' rs' gs gs' hg
    rw [CallEnv.extend_call_self]
    exact hK gs gs' hg x W hW y hy
  · rw [CallEnv.extend_call_of_ne _ _ (fun h => hgf h.1)]
    exact hT g as' rs' gs gs' hg x W hW y hy

end Table

end CatCrypt.Crypto.SecureCompilation.VIR
