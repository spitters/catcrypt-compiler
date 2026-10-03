/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

/-!
# Rules of the acyclic e-graph from laws of operations

Rules of `AegraphGeneric.Rule` over every dialect, each built from a law of operations of the
dialect, stated as an equation on `DialectDenote.denote`. The soundness field of each rule is
proved once from its law, and its independence lemma once for every leakage model:

* `constFoldRule`: a pure operation whose arguments are all defined by constant-like nodes
  of the definition table is replaced by the constant its value reifies to (`ConstReify`, a
  nullary constant operation per value; `ConstLaw` gives its empty signature);
* `involutionRule`: `f (f x) = x` for the operations of an `Involution`;
* `idempotentRule`: `x ∘ x = x` for the binary operations of an `Idempotent`;
* `selfCancelRule`: `x ∘ x = c` for the binary operations of a `SelfCancel`, with `c` a
  nullary operation;
* `copyRule`: `f x = x` for the unary operations of a `CopyOp`.

The laws are read through the value evaluator `evalVals`, which evaluates an operation on a
list of typed values, and the bridge `evalKey_eq`, which equates it with the node evaluator
`evalKey` on levels.

## Main results

* `involutionRule`, `idempotentRule`, `selfCancelRule`, `copyRule`, `constFoldRule`: the
  rules, with their soundness as the `sound` field.
* `involutionRule_indep`, `idempotentRule_indep`, `selfCancelRule_indep`,
  `copyRule_indep`, `constFoldRule_indep`: the events of every alternative of each rule do
  not depend on the valuation, for every leakage model.
* `rulesIndep_of_forall`: `RulesIndep` of a rule set from the independence of each rule.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.TraitRules

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

/-! ## 1. Typed applications of a denotation -/

section Apps

variable {d : Dialect.{0, 0}} [TyDenote d.Ty]

/-- A function on argument vectors of the empty signature, applied. -/
def app0 : {tys : List d.Ty} → {r : d.Ty} → (HVector (fun t => ⟦t⟧) tys → ⟦r⟧) →
    tys = [] → ⟦r⟧
  | _, _, f, rfl => f .nil

/-- A function on argument vectors of the signature `[t]` with result type `t`, as a
    function `⟦t⟧ → ⟦t⟧`. -/
def un {t : d.Ty} : {tys : List d.Ty} → {r : d.Ty} → (HVector (fun t => ⟦t⟧) tys → ⟦r⟧) →
    tys = [t] → r = t → ⟦t⟧ → ⟦t⟧
  | _, _, f, rfl, rfl, x => f (.cons x .nil)

/-- A function on argument vectors of the signature `[t, t]` with result type `t`, as a
    function `⟦t⟧ → ⟦t⟧ → ⟦t⟧`. -/
def bin {t : d.Ty} : {tys : List d.Ty} → {r : d.Ty} → (HVector (fun t => ⟦t⟧) tys → ⟦r⟧) →
    tys = [t, t] → r = t → ⟦t⟧ → ⟦t⟧ → ⟦t⟧
  | _, _, f, rfl, rfl, x, y => f (.cons x (.cons y .nil))

/-- A function on argument vectors of the signature `[t, t]`, applied to two values. -/
def app2 {t : d.Ty} : {tys : List d.Ty} → {r : d.Ty} → (HVector (fun t => ⟦t⟧) tys → ⟦r⟧) →
    tys = [t, t] → ⟦t⟧ → ⟦t⟧ → ⟦r⟧
  | _, _, f, rfl, x, y => f (.cons x (.cons y .nil))

/-- The empty vector at a signature equal to `[]`. -/
def nilOf {α : d.Ty → Type} : {tys : List d.Ty} → tys = [] → HVector α tys
  | _, rfl => .nil

omit [TyDenote d.Ty] in
theorem argLvls_nilOf {Δ : Ctxt d} {tys : List d.Ty} (h : tys = []) :
    argLvls (nilOf (α := fun ty => Ctxt.Var Δ ty) h) = [] := by
  subst h
  rfl

omit [TyDenote d.Ty] in
theorem mem_varAlts [DecidableEq d.Ty] [DialectSignature d] {Δ : Ctxt d} {s : d.Ty}
    {l : Nat} {alt : Alt Δ s} (h : alt ∈ ((varOfLvl? Δ s l).map Alt.var).toList) :
    ∃ x, varOfLvl? Δ s l = some x ∧ alt = .var x := by
  cases hvx : varOfLvl? Δ s l with
  | none => simp [hvx] at h
  | some x =>
      simp only [hvx, Option.map_some, Option.toList_some, List.mem_singleton] at h
      exact ⟨x, rfl, h⟩

theorem sigma_eq_of_mk_eq {s : d.Ty} {x y : ⟦s⟧}
    (h : (⟨s, x⟩ : Σ t : d.Ty, ⟦t⟧) = ⟨s, y⟩) : x = y :=
  eq_of_heq (Sigma.mk.inj_iff.mp h).2

end Apps

/-! ## 2. Evaluation on typed values -/

section Vals

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty]

/-- The typed values `vs`, read at the types `tys`. -/
def gatherVals : (tys : List d.Ty) → List (Σ t : d.Ty, ⟦t⟧) →
    Option (HVector (fun t => ⟦t⟧) tys)
  | [], [] => some .nil
  | ty :: tys, v :: vs =>
      match castTo? v ty, gatherVals tys vs with
      | some x, some rest => some (.cons x rest)
      | _, _ => none
  | _, _ => none

/-- A function on argument vectors evaluated on typed values. -/
def mapF {tys : List d.Ty} {r : d.Ty} (f : HVector (fun t => ⟦t⟧) tys → ⟦r⟧)
    (vs : List (Σ t : d.Ty, ⟦t⟧)) : Option (Σ t : d.Ty, ⟦t⟧) :=
  (gatherVals tys vs).map fun a => ⟨r, f a⟩

theorem castTo?_eq_some {p : Σ t : d.Ty, ⟦t⟧} {ty : d.Ty} {x : ⟦ty⟧}
    (h : castTo? p ty = some x) : p = ⟨ty, x⟩ := by
  obtain ⟨t, y⟩ := p
  unfold castTo? at h
  split at h
  · rename_i hp
    cases h
    dsimp only at hp
    subst hp
    rfl
  · cases h

theorem mapF_nil {tys : List d.Ty} {r : d.Ty} (f : HVector (fun t => ⟦t⟧) tys → ⟦r⟧)
    (h : tys = []) : mapF f [] = some ⟨r, app0 f h⟩ := by
  subst h
  rfl

theorem mapF_one {tys : List d.Ty} {r t : d.Ty} (f : HVector (fun t => ⟦t⟧) tys → ⟦r⟧)
    (hs : tys = [t]) (hr : r = t) (v : Σ t : d.Ty, ⟦t⟧) :
    mapF f [v] = (castTo? v t).map fun x => ⟨t, un f hs hr x⟩ := by
  subst hs
  subst hr
  unfold mapF
  simp only [gatherVals]
  cases castTo? v r <;> rfl

theorem mapF_bin {tys : List d.Ty} {r t : d.Ty} (f : HVector (fun t => ⟦t⟧) tys → ⟦r⟧)
    (hs : tys = [t, t]) (hr : r = t) (v : Σ t : d.Ty, ⟦t⟧) :
    mapF f [v, v] = (castTo? v t).map fun x => ⟨t, bin f hs hr x x⟩ := by
  subst hs
  subst hr
  unfold mapF
  simp only [gatherVals]
  cases castTo? v r <;> rfl

theorem mapF_app2 {tys : List d.Ty} {r t : d.Ty} (f : HVector (fun t => ⟦t⟧) tys → ⟦r⟧)
    (hs : tys = [t, t]) (v : Σ t : d.Ty, ⟦t⟧) :
    mapF f [v, v] = (castTo? v t).map fun x => ⟨r, app2 f hs x x⟩ := by
  subst hs
  unfold mapF
  simp only [gatherVals]
  cases castTo? v t <;> rfl

variable [DialectSignature d] [DialectDenote d]

/-- The value of the operation `op` on the typed values `vs`, when they have its argument
    types. -/
def evalVals (op : d.Op) (vs : List (Σ t : d.Ty, ⟦t⟧)) : Option (Σ t : d.Ty, ⟦t⟧) :=
  mapF (DialectDenote.denote op) vs

/-- The values at the levels `ls` of a valuation. -/
def lvlVals {Γ : Ctxt d} (V : Ctxt.Valuation Γ) : List Nat → Option (List (Σ t : d.Ty, ⟦t⟧))
  | [] => some []
  | l :: ls =>
      match getLvl V l, lvlVals V ls with
      | some v, some vs => some (v :: vs)
      | _, _ => none

omit [DialectSignature d] [DialectDenote d] in
theorem gatherArgs_eq_gatherVals {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
    ∀ (tys : List d.Ty) (ls : List Nat) (vs : List (Σ t : d.Ty, ⟦t⟧)),
      lvlVals V ls = some vs → gatherArgs V tys ls = gatherVals tys vs
  | tys, [], vs, h => by
      simp only [lvlVals, Option.some.injEq] at h
      subst h
      cases tys <;> rfl
  | tys, l :: ls, vs, h => by
      simp only [lvlVals] at h
      split at h
      · rename_i v vs' hv hr
        cases h
        cases tys with
        | nil => rfl
        | cons ty tys =>
            simp only [gatherArgs, gatherVals, hv, Option.bind_some,
              gatherArgs_eq_gatherVals V tys ls vs' hr]
            rfl
      · cases h

omit [DialectSignature d] [DialectDenote d] in
theorem lvlVals_of_gatherArgs {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
    ∀ (tys : List d.Ty) (ls : List Nat) (a : HVector (fun t => ⟦t⟧) tys),
      gatherArgs V tys ls = some a → ∃ vs, lvlVals V ls = some vs
  | [], [], _, _ => ⟨[], rfl⟩
  | [], _ :: _, _, h => by simp [gatherArgs] at h
  | _ :: _, [], _, h => by simp [gatherArgs] at h
  | ty :: tys, l :: ls, a, h => by
      unfold gatherArgs at h
      rcases hg : getLvl V l with _ | v
      · simp [hg] at h
      · rcases hr : gatherArgs V tys ls with _ | rest
        · simp [hg, hr] at h
        · obtain ⟨vs, hvs⟩ := lvlVals_of_gatherArgs V tys ls rest hr
          exact ⟨v :: vs, by simp [lvlVals, hg, hvs]⟩

/-- **The node evaluator on values.** At levels holding the values `vs`, the node evaluator
    is the value evaluator. -/
theorem evalKey_eq {Γ : Ctxt d} (V : Ctxt.Valuation Γ) (op : d.Op) {ls : List Nat}
    {vs : List (Σ t : d.Ty, ⟦t⟧)} (h : lvlVals V ls = some vs) :
    evalKey V op ls = evalVals op vs := by
  unfold evalKey evalVals mapF
  rw [gatherArgs_eq_gatherVals V _ ls vs h]

theorem evalKey_nil {Γ : Ctxt d} (V : Ctxt.Valuation Γ) (op : d.Op) :
    evalKey V op [] = evalVals op [] :=
  evalKey_eq V op rfl

theorem evalKey_one {Γ : Ctxt d} {V : Ctxt.Valuation Γ} (op : d.Op) {l : Nat}
    {v : Σ t : d.Ty, ⟦t⟧} (h : getLvl V l = some v) :
    evalKey V op [l] = evalVals op [v] :=
  evalKey_eq V op (by simp [lvlVals, h])

theorem evalKey_self {Γ : Ctxt d} {V : Ctxt.Valuation Γ} (op : d.Op) {l : Nat}
    {v : Σ t : d.Ty, ⟦t⟧} (h : getLvl V l = some v) :
    evalKey V op [l, l] = evalVals op [v, v] :=
  evalKey_eq V op (by simp [lvlVals, h])

/-- The value of an expression whose operation has the empty signature is the value of its
    operation on no arguments. -/
theorem evalVals_nullary {Δ : Ctxt d} {s : d.Ty} (V : Ctxt.Valuation Δ) (op : d.Op)
    (hr : DialectSignature.ret op = s) (hs : DialectSignature.sig op = []) :
    evalVals op [] =
      some ⟨s, (⟨op, hr, nilOf hs⟩ : Expr d Δ s).denote V⟩ := by
  rw [← evalKey_nil V op]
  have h := evalKey_expr (⟨op, hr, nilOf hs⟩ : Expr d Δ s) V
  rwa [show argLvls (nilOf (α := fun ty => Ctxt.Var Δ ty) hs) = [] from argLvls_nilOf hs]
    at h

end Vals

/-! ## 3. Independence of a rule -/

section Indep

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d]

/-- The events of every alternative of the rule `r` are the same at every valuation. -/
def RuleIndep (L : LeakModel d) (r : Rule d) : Prop :=
  ∀ (D : Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s), ∀ alt ∈ r.apply D e, alt.Indep L

/-- A rule set whose rules are each independent is independent. -/
theorem rulesIndep_of_forall {L : LeakModel d} {R : RuleSet d}
    (h : ∀ r ∈ R.rules, RuleIndep L r) : RulesIndep L R := by
  intro D Δ s e alt ha
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  exact h r hr D e alt ha

/-- Every rule of an independent rule set is independent. -/
theorem ruleIndep_of_mem {L : LeakModel d} {R : RuleSet d} (hR : RulesIndep L R)
    {r : Rule d} (hr : r ∈ R.rules) : RuleIndep L r := by
  intro D Δ s e alt ha
  exact hR D e alt (List.mem_flatMap.mpr ⟨r, hr, ha⟩)

end Indep

/-! ## 4. Involutions -/

section Involution

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d]

/-- A family of involutive unary operations: each operation selected by `isInv` has the
    signature `[ty op]` and the result type `ty op`, and its denotation `f` satisfies
    `f (f x) = x`. -/
structure Involution (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] where
  /-- The selected operations. -/
  isInv : d.Op → Bool
  /-- The operand type of a selected operation. -/
  ty : d.Op → d.Ty
  sig_eq : ∀ op, isInv op = true → DialectSignature.sig op = [ty op]
  ret_eq : ∀ op, isInv op = true → DialectSignature.ret op = ty op
  /-- The involution law. -/
  law : ∀ op (h : isInv op = true) (x : ⟦ty op⟧),
    un (DialectDenote.denote op) (sig_eq op h) (ret_eq op h)
      (un (DialectDenote.denote op) (sig_eq op h) (ret_eq op h) x) = x

/-- The involution law on typed values. -/
theorem Involution.vals (I : Involution d) {op : d.Op} (h : I.isInv op = true)
    {v u : Σ t : d.Ty, ⟦t⟧} (hv : evalVals op [v] = some u) : evalVals op [u] = some v := by
  unfold evalVals at hv ⊢
  rw [mapF_one _ (I.sig_eq op h) (I.ret_eq op h)] at hv ⊢
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hv
  rw [castTo?_mk, Option.map_some, I.law op h x, castTo?_eq_some hx]

variable [DecidableEq d.Op]

/-- The alternatives of an involution: for `f a` with `a` defined by `f x`, the variable
    `x`. -/
def invApply (I : Involution d) (D : Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    List (Alt Δ s) :=
  if I.isInv e.op then
    match argLvls e.args with
    | [la] =>
        match D[la]? with
        | some (op', [l]) =>
            if op' = e.op then ((varOfLvl? Δ s l).map Alt.var).toList else []
        | _ => []
    | _ => []
  else []

theorem invApply_sound (I : Involution d) (D : Defs d) {Δ : Ctxt d} (V : Ctxt.Valuation Δ)
    (hD : DSound V D) {s : d.Ty} (e : Expr d Δ s) :
    ∀ alt ∈ invApply I D e, alt.denote V = e.denote V := by
  intro alt ha
  unfold invApply at ha
  split at ha
  · rename_i hinv
    split at ha
    · rename_i la hla
      split at ha
      · rename_i op' l hD'
        split at ha
        · rename_i hop
          subst hop
          obtain ⟨x, hx, rfl⟩ : ∃ x, varOfLvl? Δ s l = some x ∧ alt = .var x := by
            cases hvx : varOfLvl? Δ s l with
            | none => simp [hvx] at ha
            | some x => simp only [hvx, Option.map_some, Option.toList_some,
                List.mem_singleton] at ha; exact ⟨x, rfl, ha⟩
          have h1 := evalKey_expr e V
          rw [hla] at h1
          obtain ⟨y, h2, h3⟩ := hD la _ hD'
          rw [evalKey_one _ (varOfLvl?_lookup hx V)] at h2
          rw [evalKey_one _ h3, I.vals hinv h2] at h1
          exact sigma_eq_of_mk_eq (Option.some.inj h1)
        · simp at ha
      · simp at ha
    · simp at ha
  · simp at ha

/-- **The involution rule** `f (f x) = x`, sound by the law of `I`. -/
def involutionRule (I : Involution d) : Rule d where
  apply D _ _ e := invApply I D e
  sound D _ V hD _ e := invApply_sound I D V hD e

/-- The involution rule emits only variables. -/
theorem involutionRule_indep (L : LeakModel d) (I : Involution d) :
    RuleIndep L (involutionRule I) := by
  intro D Δ s e alt ha
  change alt ∈ invApply I D e at ha
  unfold invApply at ha
  split at ha
  · split at ha
    · split at ha
      · split at ha
        · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
          trivial
        · simp at ha
      · simp at ha
    · simp at ha
  · simp at ha

end Involution

/-! ## 5. Idempotent and copy operations -/

section Idempotent

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d]

/-- A family of idempotent binary operations: each operation selected by `isIdem` has the
    signature `[ty op, ty op]` and the result type `ty op`, and its denotation `f`
    satisfies `f x x = x`. -/
structure Idempotent (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] where
  /-- The selected operations. -/
  isIdem : d.Op → Bool
  /-- The operand type of a selected operation. -/
  ty : d.Op → d.Ty
  sig_eq : ∀ op, isIdem op = true → DialectSignature.sig op = [ty op, ty op]
  ret_eq : ∀ op, isIdem op = true → DialectSignature.ret op = ty op
  /-- The idempotence law. -/
  law : ∀ op (h : isIdem op = true) (x : ⟦ty op⟧),
    bin (DialectDenote.denote op) (sig_eq op h) (ret_eq op h) x x = x

/-- The idempotence law on typed values. -/
theorem Idempotent.vals (I : Idempotent d) {op : d.Op} (h : I.isIdem op = true)
    {v u : Σ t : d.Ty, ⟦t⟧} (hv : evalVals op [v, v] = some u) : u = v := by
  unfold evalVals at hv
  rw [mapF_bin _ (I.sig_eq op h) (I.ret_eq op h)] at hv
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hv
  rw [I.law op h x, castTo?_eq_some hx]

/-- The alternatives of an idempotent operation: for `a ∘ a`, the variable `a`. -/
def idemApply (I : Idempotent d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    List (Alt Δ s) :=
  if I.isIdem e.op then
    match argLvls e.args with
    | [la, lb] => if la = lb then ((varOfLvl? Δ s la).map Alt.var).toList else []
    | _ => []
  else []

theorem idemApply_sound (I : Idempotent d) {Δ : Ctxt d} (V : Ctxt.Valuation Δ) {s : d.Ty}
    (e : Expr d Δ s) : ∀ alt ∈ idemApply I e, alt.denote V = e.denote V := by
  intro alt ha
  unfold idemApply at ha
  split at ha
  · rename_i hidem
    split at ha
    · rename_i la lb hla
      split at ha
      · rename_i hab
        subst hab
        obtain ⟨x, hx, rfl⟩ : ∃ x, varOfLvl? Δ s la = some x ∧ alt = .var x := by
          cases hvx : varOfLvl? Δ s la with
          | none => simp [hvx] at ha
          | some x => simp only [hvx, Option.map_some, Option.toList_some,
              List.mem_singleton] at ha; exact ⟨x, rfl, ha⟩
        have h1 := evalKey_expr e V
        rw [hla, evalKey_self _ (varOfLvl?_lookup hx V)] at h1
        exact (sigma_eq_of_mk_eq (I.vals hidem h1)).symm
      · simp at ha
    · simp at ha
  · simp at ha

/-- **The idempotence rule** `x ∘ x = x`, sound by the law of `I`. -/
def idempotentRule (I : Idempotent d) : Rule d where
  apply _ _ _ e := idemApply I e
  sound _ _ V _ _ e := idemApply_sound I V e

/-- The idempotence rule emits only variables. -/
theorem idempotentRule_indep (L : LeakModel d) (I : Idempotent d) :
    RuleIndep L (idempotentRule I) := by
  intro D Δ s e alt ha
  change alt ∈ idemApply I e at ha
  unfold idemApply at ha
  split at ha
  · split at ha
    · split at ha
      · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
        trivial
      · simp at ha
    · simp at ha
  · simp at ha

/-- A family of copy operations: each operation selected by `isCopy` has the signature
    `[ty op]` and the result type `ty op`, and denotes the identity. -/
structure CopyOp (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] where
  /-- The selected operations. -/
  isCopy : d.Op → Bool
  /-- The operand type of a selected operation. -/
  ty : d.Op → d.Ty
  sig_eq : ∀ op, isCopy op = true → DialectSignature.sig op = [ty op]
  ret_eq : ∀ op, isCopy op = true → DialectSignature.ret op = ty op
  /-- The copy law. -/
  law : ∀ op (h : isCopy op = true) (x : ⟦ty op⟧),
    un (DialectDenote.denote op) (sig_eq op h) (ret_eq op h) x = x

/-- The copy law on typed values. -/
theorem CopyOp.vals (C : CopyOp d) {op : d.Op} (h : C.isCopy op = true)
    {v u : Σ t : d.Ty, ⟦t⟧} (hv : evalVals op [v] = some u) : u = v := by
  unfold evalVals at hv
  rw [mapF_one _ (C.sig_eq op h) (C.ret_eq op h)] at hv
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hv
  rw [C.law op h x, castTo?_eq_some hx]

/-- The alternatives of a copy: for `f a`, the variable `a`. -/
def copyApply (C : CopyOp d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) : List (Alt Δ s) :=
  if C.isCopy e.op then
    match argLvls e.args with
    | [la] => ((varOfLvl? Δ s la).map Alt.var).toList
    | _ => []
  else []

theorem copyApply_sound (C : CopyOp d) {Δ : Ctxt d} (V : Ctxt.Valuation Δ) {s : d.Ty}
    (e : Expr d Δ s) : ∀ alt ∈ copyApply C e, alt.denote V = e.denote V := by
  intro alt ha
  unfold copyApply at ha
  split at ha
  · rename_i hc
    split at ha
    · rename_i la hla
      obtain ⟨x, hx, rfl⟩ : ∃ x, varOfLvl? Δ s la = some x ∧ alt = .var x := by
        cases hvx : varOfLvl? Δ s la with
        | none => simp [hvx] at ha
        | some x => simp only [hvx, Option.map_some, Option.toList_some,
            List.mem_singleton] at ha; exact ⟨x, rfl, ha⟩
      have h1 := evalKey_expr e V
      rw [hla, evalKey_one _ (varOfLvl?_lookup hx V)] at h1
      exact (sigma_eq_of_mk_eq (C.vals hc h1)).symm
    · simp at ha
  · simp at ha

/-- **The copy rule** `f x = x`, sound by the law of `C`: the binding of a copy is replaced
    by its operand. -/
def copyRule (C : CopyOp d) : Rule d where
  apply _ _ _ e := copyApply C e
  sound _ _ V _ _ e := copyApply_sound C V e

/-- The copy rule emits only variables. -/
theorem copyRule_indep (L : LeakModel d) (C : CopyOp d) : RuleIndep L (copyRule C) := by
  intro D Δ s e alt ha
  change alt ∈ copyApply C e at ha
  unfold copyApply at ha
  split at ha
  · split at ha
    · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
      trivial
    · simp at ha
  · simp at ha

end Idempotent

/-! ## 6. Self-cancelling operations -/

section SelfCancel

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d]

/-- A family of self-cancelling binary operations: each operation selected by `isCancel`
    has the signature `[ty op, ty op]`, and `f x x` is the value of the nullary operation
    `zero op`, which has the result type of `op`. -/
structure SelfCancel (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] where
  /-- The selected operations. -/
  isCancel : d.Op → Bool
  /-- The operand type of a selected operation. -/
  ty : d.Op → d.Ty
  sig_eq : ∀ op, isCancel op = true → DialectSignature.sig op = [ty op, ty op]
  /-- The nullary operation whose value is `f x x`. -/
  zero : d.Op → d.Op
  zero_sig : ∀ op, isCancel op = true → DialectSignature.sig (zero op) = []
  zero_ret : ∀ op, isCancel op = true →
    DialectSignature.ret (zero op) = DialectSignature.ret op
  /-- The self-cancellation law. -/
  law : ∀ op (h : isCancel op = true) (x : ⟦ty op⟧),
    (⟨DialectSignature.ret op, app2 (DialectDenote.denote op) (sig_eq op h) x x⟩ :
        Σ t : d.Ty, ⟦t⟧) =
      ⟨DialectSignature.ret (zero op), app0 (DialectDenote.denote (zero op)) (zero_sig op h)⟩

/-- The self-cancellation law on typed values. -/
theorem SelfCancel.vals (I : SelfCancel d) {op : d.Op} (h : I.isCancel op = true)
    {v u : Σ t : d.Ty, ⟦t⟧} (hv : evalVals op [v, v] = some u) :
    evalVals (I.zero op) [] = some u := by
  unfold evalVals at hv ⊢
  rw [mapF_app2 _ (I.sig_eq op h)] at hv
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp hv
  rw [mapF_nil _ (I.zero_sig op h), I.law op h x]

/-- The alternatives of a self-cancelling operation: for `a ∘ a`, the nullary binding
    `zero op`. -/
def cancelApply (I : SelfCancel d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    List (Alt Δ s) :=
  if h : I.isCancel e.op = true then
    match argLvls e.args with
    | [la, lb] =>
        if la = lb then
          [.one ⟨I.zero e.op, (I.zero_ret e.op h).trans e.retTy_eq, nilOf (I.zero_sig e.op h)⟩]
        else []
    | _ => []
  else []

theorem cancelApply_sound (I : SelfCancel d) {Δ : Ctxt d} (V : Ctxt.Valuation Δ) {s : d.Ty}
    (e : Expr d Δ s) : ∀ alt ∈ cancelApply I e, alt.denote V = e.denote V := by
  intro alt ha
  unfold cancelApply at ha
  split at ha
  · rename_i hc
    split at ha
    · rename_i la lb hla
      split at ha
      · rename_i hab
        subst hab
        simp only [List.mem_singleton] at ha
        subst ha
        have h1 := evalKey_expr e V
        rw [hla] at h1
        obtain ⟨v, hv⟩ : ∃ v, getLvl V la = some v := by
          unfold evalKey at h1
          obtain ⟨a, ha', -⟩ := Option.map_eq_some_iff.mp h1
          obtain ⟨vs, hvs⟩ := lvlVals_of_gatherArgs V _ _ a ha'
          simp only [lvlVals] at hvs
          split at hvs
          · rename_i v _ hv _
            exact ⟨v, hv⟩
          · cases hvs
        rw [evalKey_self _ hv] at h1
        have h2 := I.vals hc h1
        rw [evalVals_nullary V (I.zero e.op) ((I.zero_ret e.op hc).trans e.retTy_eq)
          (I.zero_sig e.op hc)] at h2
        exact sigma_eq_of_mk_eq (Option.some.inj h2)
      · simp at ha
    · simp at ha
  · simp at ha

/-- **The self-cancellation rule** `x ∘ x = c`, sound by the law of `I`. -/
def selfCancelRule (I : SelfCancel d) : Rule d where
  apply _ _ _ e := cancelApply I e
  sound _ _ V _ _ e := cancelApply_sound I V e

/-- The self-cancellation rule emits only nullary bindings, whose events do not depend on
    the valuation. -/
theorem selfCancelRule_indep (L : LeakModel d) (I : SelfCancel d) :
    RuleIndep L (selfCancelRule I) := by
  intro D Δ s e alt ha
  change alt ∈ cancelApply I e at ha
  unfold cancelApply at ha
  split at ha
  · rename_i hc
    split at ha
    · split at ha
      · simp only [List.mem_singleton] at ha
        subst ha
        exact Expr.ctLeak_indep_of_nullary L _ (I.zero_sig e.op hc)
      · simp at ha
    · simp at ha
  · simp at ha

end SelfCancel

/-! ## 7. Constant folding -/

section ConstFold

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d]

/-- A reification of values as constants under the operation traits `T`: `reify t x`, when
    defined, is a constant-like operation of result type `t` whose value is `x`. The law
    `ConstLaw T` gives it the empty signature. -/
structure ConstReify (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] (T : OpTraits d) where
  /-- The constant operation denoting a value, when there is one. -/
  reify : (t : d.Ty) → ⟦t⟧ → Option d.Op
  /-- Constant-like operations of `T` have the empty signature. -/
  law : ConstLaw T
  const : ∀ t x op, reify t x = some op → T.constLike op = true
  ret_eq : ∀ t x op, reify t x = some op → DialectSignature.ret op = t
  /-- The reified operation denotes the value. -/
  denote_eq : ∀ t x op (h : reify t x = some op),
    (⟨DialectSignature.ret op, app0 (DialectDenote.denote op) (law op (const t x op h))⟩ :
      Σ t : d.Ty, ⟦t⟧) = ⟨t, x⟩

/-- The values of the nodes at the levels `ls`, when each is defined in `D` by a
    constant-like node of `T`. -/
def constVals (T : OpTraits d) (D : Defs d) : List Nat → Option (List (Σ t : d.Ty, ⟦t⟧))
  | [] => some []
  | l :: ls =>
      match D[l]?, constVals T D ls with
      | some (c, []), some vs => if T.constLike c then (evalVals c []).map (· :: vs) else none
      | _, _ => none

theorem constVals_sound (T : OpTraits d) {D : Defs d} {Γ : Ctxt d} {V : Ctxt.Valuation Γ}
    (hD : DSound V D) :
    ∀ (ls : List Nat) (vs : List (Σ t : d.Ty, ⟦t⟧)),
      constVals T D ls = some vs → lvlVals V ls = some vs
  | [], vs, h => h
  | l :: ls, vs, h => by
      simp only [constVals] at h
      split at h
      · rename_i c vs' hl hr
        split at h
        · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨y, h1, h2⟩ := hD l _ hl
          rw [evalKey_nil, hv] at h1
          cases h1
          simp [lvlVals, h2, constVals_sound T hD ls vs' hr]
        · cases h
      · cases h

/-- The alternatives of constant folding: for a pure, not constant-like operation selected
    by `sel`, with at least one argument and every argument defined by a constant-like
    node, the constant reifying its value. -/
def foldApply {T : OpTraits d} (R : ConstReify d T) (sel : d.Op → Bool) (D : Defs d)
    {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) : List (Alt Δ s) :=
  if sel e.op && T.pure e.op && !T.constLike e.op && !(argLvls e.args).isEmpty then
    match constVals T D (argLvls e.args) with
    | some vs =>
        match evalVals e.op vs with
        | some p =>
            match castTo? p s with
            | some x =>
                match h : R.reify s x with
                | some c =>
                    [.one ⟨c, R.ret_eq s x c h, nilOf (R.law c (R.const s x c h))⟩]
                | none => []
            | none => []
        | none => []
    | none => []
  else []

theorem foldApply_sound {T : OpTraits d} (R : ConstReify d T) (sel : d.Op → Bool)
    (D : Defs d) {Δ : Ctxt d} (V : Ctxt.Valuation Δ) (hD : DSound V D) {s : d.Ty}
    (e : Expr d Δ s) : ∀ alt ∈ foldApply R sel D e, alt.denote V = e.denote V := by
  intro alt ha
  unfold foldApply at ha
  split at ha
  · split at ha
    · rename_i vs hvs
      split at ha
      · rename_i p hp
        split at ha
        · rename_i x hx
          split at ha
          · rename_i c hc
            simp only [List.mem_singleton] at ha
            subst ha
            have h1 := evalKey_expr e V
            rw [evalKey_eq V _ (constVals_sound T hD _ vs hvs), hp] at h1
            rw [Option.some.inj h1, castTo?_mk] at hx
            cases hx
            have h2 := evalVals_nullary V c (R.ret_eq s _ c hc) (R.law c (R.const s _ c hc))
            unfold evalVals at h2
            rw [mapF_nil _ (R.law c (R.const s _ c hc)), R.denote_eq s _ c hc] at h2
            exact (sigma_eq_of_mk_eq (Option.some.inj h2)).symm
          · simp at ha
        · simp at ha
      · simp at ha
    · simp at ha
  · simp at ha

/-- **The constant-folding rule**: a pure operation selected by `sel` on constant
    arguments is replaced by the constant `R.reify` gives for its value. -/
def constFoldRule {T : OpTraits d} (R : ConstReify d T) (sel : d.Op → Bool) : Rule d where
  apply D _ _ e := foldApply R sel D e
  sound D _ V hD _ e := foldApply_sound R sel D V hD e

/-- Constant folding emits only constant-like bindings, whose events do not depend on the
    valuation under `ConstLaw`. -/
theorem constFoldRule_indep (L : LeakModel d) {T : OpTraits d} (R : ConstReify d T)
    (sel : d.Op → Bool) : RuleIndep L (constFoldRule R sel) := by
  intro D Δ s e alt ha
  change alt ∈ foldApply R sel D e at ha
  unfold foldApply at ha
  split at ha
  · split at ha
    · split at ha
      · split at ha
        · split at ha
          · rename_i c hc
            simp only [List.mem_singleton] at ha
            subst ha
            exact ConstLaw.ctLeak_indep R.law L _ (R.const _ _ c hc)
          · simp at ha
        · simp at ha
      · simp at ha
    · simp at ha
  · simp at ha

end ConstFold

end CatCrypt.Crypto.Optimizer.Rewrite.TraitRules
