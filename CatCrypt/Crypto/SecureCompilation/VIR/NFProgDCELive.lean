/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgDCE

/-!
# Dead-binding elimination by one liveness pass

`NFProg.dce` decides at each let-binding whether its continuation, after the removal inside
it, reads the bound variable, by renaming that continuation with the strengthening
`PRen.drop`: one traversal of the continuation per binding. `NFProg.dceLive` computes the
same program in two passes over the source. The backward pass `NFProg.live` computes, for each
binding, whether the bound variable is read by the eliminated continuation, together with the
de Bruijn indices of the variables the eliminated program reads, as a set without duplicates
(`LiveSet`). The forward pass `NFProg.prune` rebuilds the program along a partial renaming that
skips the removed bindings. The equation `NFProg.dce_eq_dceLive` is registered with
`@[csimp]`, so compiled code that calls `NFProg.dce` runs `NFProg.dceLive`; every theorem about
`NFProg.dce` is a theorem about the code that runs.

## Main definitions

* `Ctxt.Var.idx` — the de Bruijn index of a variable.
* `LiveSet`, `LiveSet.union`, `LiveSet.shift` — sets of indices as lists.
* `PRen.skip`, `PRen.comp` — the renaming that drops the newest binding and continues with
  `f`; the composition of partial renamings.
* `NFProg.LTree`, `NFProg.live` — the liveness pass.
* `NFProg.prune`, `NFProg.dceLive` — the rebuilding pass and the eliminated program.

## Main results

* `NFProg.rename?_comp` — renaming a renamed program is renaming along the composition.
* `NFProg.isSome_rename?_dce` — the renaming of the eliminated program succeeds exactly when
  the renaming keeps every index of its live set.
* `NFProg.prune_live` — the rebuilding pass at the tree of the liveness pass is the renaming
  of the eliminated program.
* `NFProg.dce_eq_dceLive` — `dce` is `dceLive` (`@[csimp]`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)

/-! ## 1. Indices and index sets -/

/-- The de Bruijn index of a variable. -/
def Ctxt.Var.idx {d : Dialect} {Γ : Ctxt d} {t : d.Ty} : Var Γ t → Nat
  | .here => 0
  | .there v => v.idx + 1

/-- Two variables of a context at the same index have the same type and are the same. -/
theorem Ctxt.Var.idx_heq {d : Dialect} : ∀ {Γ : Ctxt d} {t t' : d.Ty} (v : Var Γ t)
    (w : Var Γ t'), v.idx = w.idx → t = t' ∧ v ≍ w
  | _, _, _, .here, .here, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .here, .there _, h => by simp [Ctxt.Var.idx] at h
  | _, _, _, .there _, .here, h => by simp [Ctxt.Var.idx] at h
  | _, _, _, .there v, .there w, h => by
      obtain ⟨rfl, h'⟩ := Ctxt.Var.idx_heq v w (by simpa [Ctxt.Var.idx] using h)
      cases h'
      exact ⟨rfl, HEq.rfl⟩

/-- A set of de Bruijn indices, as a list; the operations keep a sorted list without
    duplicates sorted and without duplicates. -/
abbrev LiveSet : Type := List Nat

namespace LiveSet

/-- The union of two sets: the merge of two sorted lists, an index common to both heads taken
    once. -/
def union : LiveSet → LiveSet → LiveSet
  | [], b => b
  | a, [] => a
  | x :: a, y :: b =>
      if x < y then x :: union a (y :: b)
      else if y < x then y :: union (x :: a) b
      else x :: union a b
termination_by a b => a.length + b.length

/-- The indices at least `k`, lowered by `k`: the set seen from under `k` fewer bindings. -/
def shift (k : Nat) (s : LiveSet) : LiveSet :=
  s.filterMap fun i => if k ≤ i then some (i - k) else none

theorem mem_union : ∀ {a b : LiveSet} {i : Nat}, i ∈ union a b ↔ i ∈ a ∨ i ∈ b
  | [], b, i => by simp [union]
  | x :: a, [], i => by simp [union]
  | x :: a, y :: b, i => by
      rw [union]
      split
      · rw [List.mem_cons, mem_union]
        simp only [List.mem_cons]
        tauto
      · split
        · rw [List.mem_cons, mem_union]
          simp only [List.mem_cons]
          tauto
        · rw [List.mem_cons, mem_union]
          have : x = y := by omega
          subst this
          simp only [List.mem_cons]
          tauto
termination_by a b => a.length + b.length

theorem mem_shift {k i : Nat} {s : LiveSet} : i ∈ shift k s ↔ i + k ∈ s := by
  simp only [shift, List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, h⟩
    split at h
    · cases h
      rwa [Nat.sub_add_cancel ‹_›]
    · cases h
  · intro h
    exact ⟨i + k, h, by simp⟩

end LiveSet

/-! ## 2. Partial renamings: skipping, composing, keeping a set -/

namespace PRen

variable {d : Dialect}

/-- The renaming that drops the newest binding and sends every other variable along `f`. -/
def skip {Γ Δ : Ctxt d} {s : d.Ty} (f : PRen Γ Δ) : PRen (s :: Γ) Δ
  | _, .here => none
  | _, .there v => f v

/-- The composition of partial renamings: `g`, then `f`. -/
def comp {Γ Δ Θ : Ctxt d} (f : PRen Δ Θ) (g : PRen Γ Δ) : PRen Γ Θ :=
  fun v => (g v).bind f

/-- `f` keeps every variable whose index is in `s`. -/
def KeepsSet {Γ Δ : Ctxt d} (f : PRen Γ Δ) (s : LiveSet) : Prop :=
  ∀ {t : d.Ty} (v : Var Γ t), v.idx ∈ s → (f v).isSome

private theorem lift_congr_apply {Γ Δ : Ctxt d} {s : d.Ty} {f g : PRen Γ Δ}
    (h : ∀ {t : d.Ty} (v : Var Γ t), f v = g v) {t : d.Ty} (v : Var (s :: Γ) t) :
    lift f v = lift g v := by
  cases v with
  | here => rfl
  | there v => simp only [lift, h]

theorem comp_lift {Γ Δ Θ : Ctxt d} {s : d.Ty} (f : PRen Δ Θ) (g : PRen Γ Δ) {t : d.Ty}
    (v : Var (s :: Γ) t) : comp (lift f) (lift g) v = lift (comp f g) v := by
  cases v with
  | here => rfl
  | there v => cases hg : g v <;> simp [comp, lift, hg]

theorem comp_liftApp {Γ Δ Θ : Ctxt d} (f : PRen Δ Θ) (g : PRen Γ Δ) :
    ∀ (cs : List d.Ty) {t : d.Ty} (v : Var (cs ++ Γ) t),
      comp (liftApp cs f) (liftApp cs g) v = liftApp cs (comp f g) v
  | [], _, _ => rfl
  | _ :: cs, _, v => (comp_lift _ _ v).trans (lift_congr_apply (comp_liftApp f g cs) v)

theorem comp_drop {Γ Δ : Ctxt d} {s : d.Ty} (f : PRen Γ Δ) {t : d.Ty} (v : Var (s :: Γ) t) :
    comp f drop v = skip f v := by
  cases v <;> rfl

/-- `KeepsSet` reads its set through membership only. -/
theorem keepsSet_congr {Γ Δ : Ctxt d} {f : PRen Γ Δ} {S S' : LiveSet}
    (h : ∀ i, i ∈ S ↔ i ∈ S') : KeepsSet f S ↔ KeepsSet f S' :=
  ⟨fun hk _ v hv => hk v ((h _).mpr hv), fun hk _ v hv => hk v ((h _).mp hv)⟩

theorem keepsSet_lift {Γ Δ : Ctxt d} {s : d.Ty} {f : PRen Γ Δ} {S : LiveSet} :
    KeepsSet (lift (s := s) f) S ↔ KeepsSet f (LiveSet.shift 1 S) := by
  constructor
  · intro h t v hv
    have := h (.there v) (LiveSet.mem_shift.mp hv)
    simpa [lift] using this
  · intro h t v hv
    cases v with
    | here => rfl
    | there v =>
        simp only [lift, Option.isSome_map]
        exact h v (LiveSet.mem_shift.mpr hv)

theorem keepsSet_liftApp {Γ Δ : Ctxt d} {f : PRen Γ Δ} :
    ∀ (cs : List d.Ty) {S : LiveSet},
      KeepsSet (liftApp cs f) S ↔ KeepsSet f (LiveSet.shift cs.length S)
  | [], S => keepsSet_congr fun i => by simp [LiveSet.mem_shift]
  | c :: cs, S => by
      show KeepsSet (lift (liftApp cs f)) S ↔ _
      rw [keepsSet_lift, keepsSet_liftApp cs]
      exact keepsSet_congr fun i => by
        simp only [LiveSet.mem_shift, List.length_cons]
        rw [Nat.add_assoc, Nat.add_comm cs.length 1]

theorem keepsSet_skip {Γ Δ : Ctxt d} {s : d.Ty} {f : PRen Γ Δ} {S : LiveSet} :
    KeepsSet (skip (s := s) f) S ↔ 0 ∉ S ∧ KeepsSet f (LiveSet.shift 1 S) := by
  constructor
  · intro h
    refine ⟨fun h0 => by simpa [skip] using h (.here (Γ := Γ) (t := s)) h0, fun v hv => ?_⟩
    exact h (.there v) (LiveSet.mem_shift.mp hv)
  · rintro ⟨h0, h⟩ t v hv
    cases v with
    | here => exact absurd hv h0
    | there v => exact h v (LiveSet.mem_shift.mpr hv)

end PRen

/-! ## 3. Renaming along a composition -/

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]

/-- The indices of a vector of variables. -/
def varsSet {Γ : Ctxt d} : {ts : List d.Ty} → HVector (fun t => Var Γ t) ts → LiveSet
  | [], .nil => []
  | _ :: _, .cons v vs => LiveSet.union [v.idx] (varsSet vs)

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.vars?_congr {Γ Δ : Ctxt d} {f g : PRen Γ Δ}
    (h : ∀ {t : d.Ty} (v : Var Γ t), f v = g v) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) → PRen.vars? f vs = PRen.vars? g vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by simp only [PRen.vars?, h v, PRen.vars?_congr h vs]

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.vars?_comp {Γ Δ Θ : Ctxt d} (f : PRen Δ Θ) (g : PRen Γ Δ) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
      {ws : HVector (fun t => Var Δ t) ts} → PRen.vars? g vs = some ws →
      PRen.vars? f ws = PRen.vars? (PRen.comp f g) vs
  | [], .nil, _, h => by
      simp only [PRen.vars?, Option.some.injEq] at h
      subst h
      rfl
  | _ :: _, .cons v vs, _, h => by
      simp only [PRen.vars?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, ws, hws, rfl⟩ := h
      simp only [PRen.vars?, PRen.comp, hw, Option.bind_some, PRen.vars?_comp f g vs hws]

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.isSome_vars? {Γ Δ : Ctxt d} (f : PRen Γ Δ) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
      ((PRen.vars? f vs).isSome ↔ PRen.KeepsSet f (varsSet vs))
  | [], .nil => by
      simp only [PRen.vars?, Option.isSome_some, true_iff]
      intro t v hv
      simp [varsSet] at hv
  | _ :: _, .cons v vs => by
      rw [PRen.vars?]
      have ih := PRen.isSome_vars? f vs
      constructor
      · intro h t w hw
        simp only [varsSet, LiveSet.mem_union, List.mem_singleton] at hw
        cases hv : f v with
        | none => simp [hv] at h
        | some v' =>
            simp only [hv, Option.bind_some, Option.isSome_map] at h
            rcases hw with hw | hw
            · obtain ⟨rfl, h'⟩ := Ctxt.Var.idx_heq w v hw
              cases h'
              simp [hv]
            · exact ih.mp h w hw
      · intro h
        have hv : (f v).isSome := h v (by simp [varsSet, LiveSet.mem_union])
        have hvs : (PRen.vars? f vs).isSome := ih.mpr fun w hw =>
          h w (by simp [varsSet, LiveSet.mem_union, hw])
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp hv
        obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp hvs
        simp [hv', hws]

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.keepsSet_union {Γ Δ : Ctxt d} {f : PRen Γ Δ} {a b : LiveSet} :
    PRen.KeepsSet f (LiveSet.union a b) ↔ PRen.KeepsSet f a ∧ PRen.KeepsSet f b :=
  ⟨fun h => ⟨fun v hv => h v (LiveSet.mem_union.mpr (.inl hv)),
      fun v hv => h v (LiveSet.mem_union.mpr (.inr hv))⟩,
    fun h _ v hv => (LiveSet.mem_union.mp hv).elim (h.1 v) (h.2 v)⟩

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.keepsSet_single {Γ Δ : Ctxt d} {f : PRen Γ Δ} {t : d.Ty} (v : Var Γ t) :
    PRen.KeepsSet f [v.idx] ↔ (f v).isSome := by
  constructor
  · intro h
    exact h v (List.mem_singleton_self _)
  · intro h t' w hw
    obtain ⟨rfl, h'⟩ := Ctxt.Var.idx_heq w v (List.mem_singleton.mp hw)
    cases h'
    exact h

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.keepsSet_shift_shift {Γ Δ : Ctxt d} {f : PRen Γ Δ} {n : Nat} {S : LiveSet} :
    PRen.KeepsSet f (LiveSet.shift 1 (LiveSet.shift n S)) ↔
      PRen.KeepsSet f (LiveSet.shift (n + 1) S) :=
  PRen.keepsSet_congr fun i => by
    simp only [LiveSet.mem_shift]
    rw [Nat.add_assoc, Nat.add_comm 1 n]

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.keepsSet_drop {Γ : Ctxt d} {s : d.Ty} {S : LiveSet} :
    PRen.KeepsSet (PRen.drop (Γ := Γ) (s := s)) S ↔ 0 ∉ S := by
  constructor
  · intro h h0
    simpa [PRen.drop] using h (.here (Γ := Γ) (t := s)) h0
  · intro h0 t v hv
    cases v with
    | here => exact absurd hv h0
    | there v => rfl

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.liftApp_congr {Γ Δ : Ctxt d} {f g : PRen Γ Δ}
    (h : ∀ {t : d.Ty} (v : Var Γ t), f v = g v) :
    ∀ (cs : List d.Ty) {t : d.Ty} (v : Var (cs ++ Γ) t), PRen.liftApp cs f v = PRen.liftApp cs g v
  | [], _, v => h v
  | _ :: cs, _, v => PRen.lift_congr_apply (PRen.liftApp_congr h cs) v

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.lift_id {Γ : Ctxt d} {s : d.Ty} {t : d.Ty} (v : Var (s :: Γ) t) :
    PRen.lift (fun v => some v : PRen Γ Γ) v = some v := by
  cases v <;> rfl

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.liftApp_id {Γ : Ctxt d} :
    ∀ (cs : List d.Ty) {t : d.Ty} (v : Var (cs ++ Γ) t),
      PRen.liftApp cs (fun v => some v : PRen Γ Γ) v = some v
  | [], _, _ => rfl
  | _ :: cs, _, v => (PRen.lift_congr_apply (PRen.liftApp_id cs) v).trans (PRen.lift_id v)

omit [DialectSignature d] [TyDenote d.Ty] in
theorem PRen.vars?_id {Γ : Ctxt d} :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
      PRen.vars? (fun v => some v : PRen Γ Γ) vs = some vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by simp [PRen.vars?, PRen.vars?_id vs]

omit [TyDenote d.Ty] in
theorem Expr.rename?_congr {Γ Δ : Ctxt d} {t : d.Ty} {f g : PRen Γ Δ}
    (h : ∀ {t : d.Ty} (v : Var Γ t), f v = g v) (e : Expr d Γ t) :
    Expr.rename? f e = Expr.rename? g e := by
  simp only [Expr.rename?, PRen.vars?_congr h]

omit [TyDenote d.Ty] in
theorem Expr.rename?_comp {Γ Δ Θ : Ctxt d} {t : d.Ty} (f : PRen Δ Θ) (g : PRen Γ Δ)
    (e : Expr d Γ t) {e' : Expr d Δ t} (h : Expr.rename? g e = some e') :
    Expr.rename? f e' = Expr.rename? (PRen.comp f g) e := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at h
  obtain ⟨args, hargs, rfl⟩ := h
  simp only [Expr.rename?, PRen.vars?_comp f g e.args hargs]

omit [TyDenote d.Ty] in
theorem Expr.isSome_rename? {Γ Δ : Ctxt d} {t : d.Ty} (f : PRen Γ Δ) (e : Expr d Γ t) :
    (Expr.rename? f e).isSome ↔ PRen.KeepsSet f (varsSet e.args) := by
  simp only [Expr.rename?, Option.isSome_map, PRen.isSome_vars?]

omit [TyDenote d.Ty] in
theorem Expr.rename?_id {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) :
    Expr.rename? (fun v => some v : PRen Γ Γ) e = some e := by
  simp [Expr.rename?, PRen.vars?_id]

variable [HasWord64 d] [HasBoolBit d]

namespace NFProg

theorem rename?_congr {Γ : Ctxt d} {ts : List d.Ty} {Δ : Ctxt d} {f g : PRen Γ Δ}
    (h : ∀ {t : d.Ty} (v : Var Γ t), f v = g v) (p : NFProg d Γ ts) :
    rename? f p = rename? g p := by
  have hfg : (@f) = (@g) := by
    funext t v
    exact h v
  have : (fun {t} => @f t) = fun {t} => @g t := hfg
  rw [this]

/-- **Renaming a renamed program is renaming along the composition.** -/
theorem rename?_comp {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ Θ : Ctxt d} (f : PRen Δ Θ) (g : PRen Γ Δ) {q : NFProg d Δ ts},
      rename? g p = some q → rename? f q = rename? (PRen.comp f g) p := by
  induction p with
  | ret vs =>
      intro Δ Θ f g q h
      simp only [rename?, Option.map_eq_some_iff] at h
      obtain ⟨ws, hws, rfl⟩ := h
      simp only [rename?, PRen.vars?_comp f g vs hws]
  | var e k ih =>
      intro Δ Θ f g q h
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', he, k', hk, rfl⟩ := h
      simp only [rename?, Expr.rename?_comp f g e he, ih _ _ hk,
        rename?_congr (PRen.comp_lift f g)]
  | forLoop count inits body k ihb ihk =>
      intro Δ Θ f g q h
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨c', hc, i', hi, b', hb, k', hk, rfl⟩ := h
      have hc' : f c' = PRen.comp f g count := by simp [PRen.comp, hc]
      simp only [rename?, hc', PRen.vars?_comp f g inits hi, ihb _ _ hb, ihk _ _ hk,
        rename?_congr (PRen.comp_liftApp _ _ _),
        rename?_congr (PRen.liftApp_congr (PRen.comp_lift f g) _)]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ Θ f g q h
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨c', hc, t', ht, e', he, k', hk, rfl⟩ := h
      have hc' : f c' = PRen.comp f g cond := by simp [PRen.comp, hc]
      simp only [rename?, hc', iht _ _ ht, ihe _ _ he, ihk _ _ hk,
        rename?_congr (PRen.comp_liftApp _ _ _)]
  | whileLoop inits body k ihb ihk =>
      intro Δ Θ f g q h
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨i', hi, b', hb, k', hk, rfl⟩ := h
      simp only [rename?, PRen.vars?_comp f g inits hi, ihb _ _ hb, ihk _ _ hk,
        rename?_congr (PRen.comp_liftApp _ _ _)]
  | call fn args k ih =>
      intro Δ Θ f g q h
      simp only [rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a', ha, k', hk, rfl⟩ := h
      simp only [rename?, PRen.vars?_comp f g args ha, ih _ _ hk,
        rename?_congr (PRen.comp_liftApp _ _ _)]

/-- The identity renaming returns the program. -/
theorem rename?_id {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    rename? (fun v => some v : PRen Γ Γ) p = some p := by
  induction p with
  | ret vs => simp [rename?, PRen.vars?_id]
  | var e k ih => simp [rename?, Expr.rename?_id, rename?_congr PRen.lift_id, ih]
  | forLoop count inits body k ihb ihk =>
      simp [rename?, PRen.vars?_id, rename?_congr (PRen.liftApp_congr PRen.lift_id _),
        rename?_congr (PRen.liftApp_id _), ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp [rename?, iht, ihe, rename?_congr (PRen.liftApp_id _), ihk]
  | whileLoop inits body k ihb ihk =>
      simp [rename?, PRen.vars?_id, rename?_congr (PRen.liftApp_id _), ihb, ihk]
  | call fn args k ih => simp [rename?, PRen.vars?_id, rename?_congr (PRen.liftApp_id _), ih]

/-! ## 4. The liveness pass and the rebuilding pass -/

/-- The shape of a program with, at each let-binding and call, a flag: whether it is kept. -/
inductive LTree where
  | leaf
  | one (keep : Bool) (k : LTree)
  | two (a b : LTree)
  | three (a b c : LTree)

/-- **The liveness pass**: the tree of the bindings `dce` keeps, and the indices of the
    variables that `dce p` reads. A binding is kept when its variable, index `0` under it, is
    read by the eliminated continuation. -/
def live : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → LTree × LiveSet
  | _, _, .ret vs => (.leaf, varsSet vs)
  | _, _, .var e k =>
      let r := live k
      if 0 ∈ r.2 then (.one true r.1, LiveSet.union (varsSet e.args) (LiveSet.shift 1 r.2))
      else (.one false r.1, LiveSet.shift 1 r.2)
  | _, _, .forLoop (cs := cs) count inits body k =>
      let rb := live body
      let rk := live k
      (.two rb.1 rk.1, LiveSet.union [count.idx] (LiveSet.union (varsSet inits)
        (LiveSet.union (LiveSet.shift (cs.length + 1) rb.2) (LiveSet.shift cs.length rk.2))))
  | _, _, .ifThenElse (rs := rs) cond thn els k =>
      let rt := live thn
      let re := live els
      let rk := live k
      (.three rt.1 re.1 rk.1, LiveSet.union [cond.idx]
        (LiveSet.union rt.2 (LiveSet.union re.2 (LiveSet.shift rs.length rk.2))))
  | _, _, .whileLoop (cs := cs) inits body k =>
      let rb := live body
      let rk := live k
      (.two rb.1 rk.1, LiveSet.union (varsSet inits)
        (LiveSet.union (LiveSet.shift cs.length rb.2) (LiveSet.shift cs.length rk.2)))
  | _, _, .call (rs := rs) _ args k =>
      let rk := live k
      (.one true rk.1, LiveSet.union (varsSet args) (LiveSet.shift rs.length rk.2))

/-- **The rebuilding pass**: the program along the partial renaming `f`, each binding the tree
    marks as removed skipped (`PRen.skip`); at a tree of another shape, the renaming of the
    eliminated program. -/
def prune : {Γ Δ : Ctxt d} → {ts : List d.Ty} → LTree → PRen Γ Δ → NFProg d Γ ts →
    Option (NFProg d Δ ts)
  | _, _, _, _, f, .ret vs => (PRen.vars? f vs).map .ret
  | _, _, _, .one keep tk, f, .var e k =>
      if keep then (Expr.rename? f e).bind fun e' => (prune tk (PRen.lift f) k).map (.var e')
      else prune tk (PRen.skip f) k
  | _, _, _, .two tb tk, f, .forLoop (cs := cs) count inits body k =>
      (f count).bind fun c' => (PRen.vars? f inits).bind fun i' =>
        (prune tb (PRen.liftApp cs (PRen.lift f)) body).bind fun b' =>
          (prune tk (PRen.liftApp cs f) k).map fun k' => .forLoop c' i' b' k'
  | _, _, _, .three tt te tk, f, .ifThenElse (rs := rs) cond thn els k =>
      (f cond).bind fun c' => (prune tt f thn).bind fun t' => (prune te f els).bind fun e' =>
        (prune tk (PRen.liftApp rs f) k).map fun k' => .ifThenElse c' t' e' k'
  | _, _, _, .two tb tk, f, .whileLoop (cs := cs) inits body k =>
      (PRen.vars? f inits).bind fun i' => (prune tb (PRen.liftApp cs f) body).bind fun b' =>
        (prune tk (PRen.liftApp cs f) k).map fun k' => .whileLoop i' b' k'
  | _, _, _, .one _ tk, f, .call (rs := rs) fn args k =>
      (PRen.vars? f args).bind fun a' =>
        (prune tk (PRen.liftApp rs f) k).map (.call fn a')
  | _, _, _, _, f, p => rename? f (dce p)

/-- **Dead-binding elimination by one liveness pass**: the rebuilding pass at the tree of the
    liveness pass and the identity renaming. -/
def dceLive {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) : NFProg d Γ ts :=
  match prune (live p).1 (fun v => some v) p with
  | some q => q
  | none => dce p

theorem isSome_bind_iff {α β : Type} {o : Option α} {g : α → Option β} {P : Prop}
    (h : ∀ x, (g x).isSome ↔ P) : (o.bind g).isSome ↔ o.isSome ∧ P := by
  cases o <;> simp [h]

/-- **The renaming of the eliminated program succeeds exactly when the renaming keeps every
    index of the live set.** -/
theorem isSome_rename?_dce {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} (f : PRen Γ Δ), (rename? f (dce p)).isSome ↔ PRen.KeepsSet f (live p).2 := by
  induction p with
  | ret vs => intro Δ f; simp [dce, rename?, live, PRen.isSome_vars?]
  | var e k ih =>
      intro Δ f
      by_cases h0 : 0 ∈ (live k).2
      · have hn : rename? PRen.drop (dce k) = none := by
          rw [← Option.not_isSome_iff_eq_none, ih, PRen.keepsSet_drop]
          exact not_not.mpr h0
        simp only [dce, hn, live, h0, ite_true, rename?]
        rw [isSome_bind_iff (P := PRen.KeepsSet (PRen.lift f) (live k).2)
          (fun _ => by rw [Option.isSome_map, ih]), Expr.isSome_rename?, PRen.keepsSet_union,
          PRen.keepsSet_lift]
      · obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp
          ((ih PRen.drop).mpr (PRen.keepsSet_drop.mpr h0))
        simp only [dce, hk', live, h0, ite_false]
        rw [rename?_comp _ f PRen.drop hk', rename?_congr (PRen.comp_drop f), ih,
          PRen.keepsSet_skip]
        exact and_iff_right h0
  | forLoop count inits body k ihb ihk =>
      intro Δ f
      simp only [dce, rename?, live]
      rw [isSome_bind_iff (fun _ => isSome_bind_iff (fun _ => isSome_bind_iff
        (fun _ => by rw [Option.isSome_map, ihk]))), ihb, PRen.isSome_vars?,
        PRen.keepsSet_union, PRen.keepsSet_single, PRen.keepsSet_union, PRen.keepsSet_union,
        PRen.keepsSet_liftApp, PRen.keepsSet_lift, PRen.keepsSet_liftApp,
        PRen.keepsSet_shift_shift]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f
      simp only [dce, rename?, live]
      rw [isSome_bind_iff (fun _ => isSome_bind_iff (fun _ => isSome_bind_iff
        (fun _ => by rw [Option.isSome_map, ihk]))), iht, ihe,
        PRen.keepsSet_union, PRen.keepsSet_single, PRen.keepsSet_union, PRen.keepsSet_union,
        PRen.keepsSet_liftApp]
  | whileLoop inits body k ihb ihk =>
      intro Δ f
      simp only [dce, rename?, live]
      rw [isSome_bind_iff (fun _ => isSome_bind_iff
        (fun _ => by rw [Option.isSome_map, ihk])), ihb, PRen.isSome_vars?,
        PRen.keepsSet_union, PRen.keepsSet_union, PRen.keepsSet_liftApp, PRen.keepsSet_liftApp]
  | call fn args k ih =>
      intro Δ f
      simp only [dce, rename?, live]
      rw [isSome_bind_iff (fun _ => by rw [Option.isSome_map, ih]), PRen.isSome_vars?,
        PRen.keepsSet_union, PRen.keepsSet_liftApp]

/-- **The rebuilding pass at the tree of the liveness pass is the renaming of the eliminated
    program.** -/
theorem prune_live {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} (f : PRen Γ Δ), prune (live p).1 f p = rename? f (dce p) := by
  induction p with
  | ret vs => intro Δ f; rfl
  | var e k ih =>
      intro Δ f
      by_cases h0 : 0 ∈ (live k).2
      · have hn : rename? PRen.drop (dce k) = none := by
          rw [← Option.not_isSome_iff_eq_none, isSome_rename?_dce, PRen.keepsSet_drop]
          exact not_not.mpr h0
        simp only [live, h0, ite_true, prune, dce, hn, rename?, ih]
      · obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp
          ((isSome_rename?_dce k PRen.drop).mpr (PRen.keepsSet_drop.mpr h0))
        simp only [live, h0, ite_false, prune, Bool.false_eq_true, dce, hk']
        rw [rename?_comp _ f PRen.drop hk', rename?_congr (PRen.comp_drop f), ih]
  | forLoop count inits body k ihb ihk => intro Δ f; simp only [live, prune, dce, rename?, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f; simp only [live, prune, dce, rename?, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk => intro Δ f; simp only [live, prune, dce, rename?, ihb, ihk]
  | call fn args k ih => intro Δ f; simp only [live, prune, dce, rename?, ih]

/-- **`dce` is `dceLive`**: the compiled code of `dce` is the two passes. -/
@[csimp] theorem dce_eq_dceLive : @dce = @dceLive := by
  funext d _ _ _ _ Γ ts p
  unfold dceLive
  rw [prune_live, rename?_id]

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
