/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFInline

/-!
# A typing judgement for the front `impToNF`

`FrontTy S Γ e t Γ'` is a syntactic typing judgement on the erased `ImpExpr`: from the
environment `Γ` of names to types, the expression `e` has the type `t` and leaves the
environment `Γ'`. The call typing is `S`. The judgement has one rule per arm of
`ImpToNF.impToNF`, and each side condition the arm checks is a premise of its rule:

* a variable bound in `Γ`, and a literal at the type `litTy` gives it;
* `unitVal`, `typeAscription`, `seq`, `letBind` and `assign`, compositionally;
* a call of a name other than `repeat`, its arguments typed left to right (`FrontTyArgs`) at
  the types `as`, with `S f as = some r`;
* a tuple of atoms (`AtomsTy`);
* a projection of a component of a value of a tuple type (`tupProjTy`);
* a counted loop `forFold` or `forFoldRev`: a lower bound `LoTy` accepts, an atom upper bound
  that `boundOk 0` or `litBoundOk 0` accepts, the body typed with the counter at the `64`-bit
  words in front of the carried names (`carriedTy`) and the names other than the counter, every
  carried name keeping its type (`KeepsTys`);
* a conditional `ifThenElse` with a condition of the bit type, both arms of one type, and
  every name of `condCarriedTy` keeping its type in both arms.

The environment of names `NfEnv Γ` of the front erases to an environment of types
(`tysOf`). A derivation from the erasure of `σ` gives an output of `impToNF` from `σ`, of the
derived type, whose environment erases to the derived one (`impToNF_out_of_frontTy`).

## Main definitions

* `TyEnv`, `tysOf` — environments of names to types, and the erasure of `NfEnv`.
* `litTy`, `AtomTy`, `AtomsTy`, `LoTy` — literals, atoms, lists of atoms and lower bounds.
* `carriedTy`, `condCarriedTy`, `condFreshTy`, `loopEnvTy`, `condEnvTy`, `KeepsTys` — the
  environments of loops and conditionals.
* `FrontTy`, `FrontTyArgs` — the judgement on expressions and on argument lists.

## Main results

* `impToNF_out_of_frontTy`, `impArgsNF_out_of_frontTyArgs` — a derivation gives an output at
  the derived type and environment.
* `impToNF_isSome_of_frontTy` — an expression with a derivation is translated.
* `crateBody_isSome_of_frontTy` — a callee body with a derivation at its parameters has a
  body in the library of the crate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.FrontTyping

open _root_.Hax (ImpExpr ImpLit)
open _root_.Hax.InlineLocalClosures (frameOk)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open Ctxt (Var)

/-! ## 1. Environments of types -/

/-- An environment of names to types; the first entry of a name is the current one. -/
abbrev TyEnv : Type := List (String × NfTy)

/-- The environment of types of an environment of names: each name with the type of its
    variable. -/
def tysOf {Γ : Ctxt nfDialect} (σ : NfEnv Γ) : TyEnv := σ.map fun p => (p.1, p.2.1)

@[simp] theorem tysOf_nil {Γ : Ctxt nfDialect} : tysOf ([] : NfEnv Γ) = [] := rfl

@[simp] theorem tysOf_cons {Γ : Ctxt nfDialect} (p : String × (Σ t : NfTy, Var Γ t))
    (σ : NfEnv Γ) : tysOf (p :: σ) = (p.1, p.2.1) :: tysOf σ := rfl

/-- The type of a name in the erasure is the type of its variable. -/
theorem lookup_tysOf {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (x : String) :
    (tysOf σ).lookup x = (σ.lookup x).map (·.1) := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
      obtain ⟨y, q⟩ := p
      by_cases h : y = x
      · subst h
        simp [NfEnv.lookup]
      · have h1 : (x == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
        have h2 : (y == x) = false := beq_eq_false_iff_ne.mpr h
        simp only [tysOf_cons, List.lookup_cons, NfEnv.lookup, List.find?_cons, h1, h2] at ih ⊢
        exact ih

@[simp] theorem tysOf_mapV {Γ Δ : Ctxt nfDialect} (f : ∀ {t : NfTy}, Var Γ t → Var Δ t)
    (σ : NfEnv Γ) : tysOf (NfEnv.mapV f σ) = tysOf σ := by
  simp [tysOf, NfEnv.mapV]

theorem tysOf_filter {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (i : String) :
    tysOf (σ.filter fun p => p.1 != i) = (tysOf σ).filter fun p => p.1 != i := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
      by_cases h : p.1 = i <;> simp [h, ih]

theorem tysOf_bindAll {Δ : Ctxt nfDialect} (xs : List String) :
    ∀ (as : List NfTy) (vs : HVector (fun t => Var Δ t) as) (σ : NfEnv Δ),
      tysOf (NfEnv.bindAll xs as vs σ) = xs.zip as ++ tysOf σ := by
  induction xs with
  | nil => intro as vs σ; cases vs <;> rfl
  | cons x xs ih =>
      intro as vs σ
      cases vs with
      | nil => rfl
      | cons v vs =>
          show tysOf ((x, ⟨_, v⟩) :: NfEnv.bindAll xs _ vs σ) = _
          rw [tysOf_cons, ih]
          rfl

theorem names_tysOf {Γ : Ctxt nfDialect} (σ : NfEnv Γ) :
    σ.map (·.1) = (tysOf σ).map (·.1) := by
  simp [tysOf]

theorem zip_map_fst_snd (ps : TyEnv) : (ps.map (·.1)).zip (ps.map (·.2)) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

theorem entriesVars_fst {Γ : Ctxt nfDialect} (W : List (String × (Σ t : NfTy, Var Γ t))) :
    (entriesVars W).1 = W.map (·.2.1) := by
  induction W with
  | nil => rfl
  | cons e W ih =>
      obtain ⟨x, t, v⟩ := e
      simp [entriesVars, ih]

/-- The names of `ps` read in `Γ'` at their types in `ps`. -/
def KeepsTys (Γ' ps : TyEnv) : Prop := ∀ p ∈ ps, Γ'.lookup p.1 = some p.2

/-- `varsAt` reads the names of `ps` at their types when the erasure keeps their types. -/
theorem varsAt_of_keeps {Δ : Ctxt nfDialect} (σ : NfEnv Δ) :
    ∀ (ps : TyEnv), KeepsTys (tysOf σ) ps →
      ∃ v, varsAt σ (ps.map (·.1)) (ps.map (·.2)) = some v
  | [], _ => ⟨_, rfl⟩
  | p :: ps, h => by
      have h1 := h p List.mem_cons_self
      rw [lookup_tysOf] at h1
      obtain ⟨q, hq, hq1⟩ := Option.map_eq_some_iff.mp h1
      obtain ⟨v, hv⟩ := varsAt_of_keeps σ ps (fun p hp => h p (List.mem_cons_of_mem _ hp))
      refine ⟨.cons (show Var Δ p.2 from hq1 ▸ q.2) v, ?_⟩
      show varsAt σ (p.1 :: ps.map (·.1)) (p.2 :: ps.map (·.2)) = _
      unfold varsAt
      rw [hq, Option.bind_some, dif_pos hq1, hv]
      rfl

/-- `varsAt_of_keeps` at names and types given as the projections of `ps`. -/
theorem varsAt_of_keeps' {Δ : Ctxt nfDialect} (σ : NfEnv Δ) (ps : TyEnv) (xs : List String)
    (cs : List NfTy) (hxs : xs = ps.map (·.1)) (hcs : cs = ps.map (·.2))
    (h : KeepsTys (tysOf σ) ps) : ∃ v, varsAt σ xs cs = some v := by
  subst hxs hcs
  exact varsAt_of_keeps σ ps h

/-! ## 2. Carried names -/

/-- The carried names of a loop over the environment `Γ` with the counter `i` and the body
    `b`, with their types: each name of `Γ` other than `i` that `b` may bind. -/
def carriedTy (Γ : TyEnv) (i : String) (b : ImpExpr) : TyEnv :=
  ((Γ.map (·.1)).eraseDups.filter fun x =>
      x != i && !frameOk (fun _ => true) (fun n => n != x) (fun _ => true) b).filterMap
    fun x => (Γ.lookup x).map fun t => (x, t)

/-- The carried names of a conditional over `Γ` with the arms `a` and `b`, with their types:
    each name of `Γ` that one of the arms may bind. -/
def condCarriedTy (Γ : TyEnv) (a b : ImpExpr) : TyEnv :=
  ((Γ.map (·.1)).eraseDups.filter fun x =>
      !(frameOk (fun _ => true) (fun n => n != x) (fun _ => true) a &&
        frameOk (fun _ => true) (fun n => n != x) (fun _ => true) b)).filterMap
    fun x => (Γ.lookup x).map fun t => (x, t)

/-- The names both arms of a conditional bind at one type and the environment `Γc` before it
    leaves unbound, from the environments `Γa`, `Γb` after the arms. -/
def condFreshTy (Γc Γa Γb : TyEnv) : TyEnv :=
  (Γa.map (·.1)).eraseDups.filterMap fun y =>
    if (Γc.lookup y).isNone then
      (Γa.lookup y).bind fun p => (Γb.lookup y).bind fun q =>
        if q = p then some (y, p) else none
    else none

/-- The environment of a loop body without its counter, and after the loop: the carried
    names in front of the names of `Γ` other than the counter `i`. -/
def loopEnvTy (Γ : TyEnv) (i : String) (b : ImpExpr) : TyEnv :=
  carriedTy Γ i b ++ Γ.filter fun p => p.1 != i

/-- The environment after a conditional: the carried names and the names both arms bind in
    front of the environment `Γc` after the condition. -/
def condEnvTy (Γc Γa Γb : TyEnv) (a b : ImpExpr) : TyEnv :=
  (condCarriedTy Γc a b ++ condFreshTy Γc Γa Γb) ++ Γc

theorem carried_tysOf {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (i : String) (b : ImpExpr) :
    (carried σ i b).map (fun e => (e.1, e.2.1)) = carriedTy (tysOf σ) i b := by
  unfold carried carriedTy
  rw [names_tysOf, List.map_filterMap]
  apply List.filterMap_congr
  intro x _
  rw [lookup_tysOf]
  cases σ.lookup x <;> rfl

theorem condCarried_tysOf {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (a b : ImpExpr) :
    (condCarried σ a b).map (fun e => (e.1, e.2.1)) = condCarriedTy (tysOf σ) a b := by
  unfold condCarried condCarriedTy
  rw [names_tysOf, List.map_filterMap]
  apply List.filterMap_congr
  intro x _
  rw [lookup_tysOf]
  cases σ.lookup x <;> rfl

theorem condFresh_tysOf {Γc Δa Δb : Ctxt nfDialect} (σc : NfEnv Γc) (σa : NfEnv Δa)
    (σb : NfEnv Δb) : condFresh σc σa σb = condFreshTy (tysOf σc) (tysOf σa) (tysOf σb) := by
  unfold condFresh condFreshTy
  rw [names_tysOf]
  apply List.filterMap_congr
  intro y _
  simp only [lookup_tysOf]
  cases σc.lookup y <;> cases σa.lookup y <;> cases σb.lookup y <;> simp

theorem condFreshTy_mem {Γc Γa Γb : TyEnv} {p : String × NfTy} (h : p ∈ condFreshTy Γc Γa Γb) :
    Γa.lookup p.1 = some p.2 ∧ Γb.lookup p.1 = some p.2 := by
  simp only [condFreshTy, List.mem_filterMap] at h
  obtain ⟨y, -, h⟩ := h
  split at h
  · cases ha : Γa.lookup y <;> cases hb : Γb.lookup y <;> simp_all
    obtain ⟨rfl, rfl⟩ := h
    simp_all
  · cases h

/-! ## 3. The judgement -/

/-- The type of a literal of the front: a bit, the unit value, and an integer literal at the
    type `litInt` gives it when `NfTy.ofLit?` accepts its value. -/
def litTy : ImpLit → Option NfTy
  | .bool _ => some .bit
  | .unit => some .unit
  | l => (litInt l).bind fun p => if (NfTy.ofLit? p.1 p.2).isSome then some p.1 else none

/-- An atom of the type `t`: a variable of `Γ` at `t`, or a literal at `t`. -/
inductive AtomTy (Γ : TyEnv) : ImpExpr → NfTy → Prop
  | var {x : String} {t : NfTy} : Γ.lookup x = some t → AtomTy Γ (.var x) t
  | lit {l : ImpLit} {t : NfTy} : litTy l = some t → AtomTy Γ (.lit l) t

/-- A list of atoms of the types `as`. -/
inductive AtomsTy (Γ : TyEnv) : List ImpExpr → List NfTy → Prop
  | nil : AtomsTy Γ [] []
  | cons {e : ImpExpr} {es : List ImpExpr} {a : NfTy} {as : List NfTy} :
      AtomTy Γ e a → AtomsTy Γ es as → AtomsTy Γ (e :: es) (a :: as)

/-- A lower bound of a counted loop: an integer literal in `[0, 2 ^ 64)`, or a variable of a
    type `loTyOk` accepts. -/
inductive LoTy (Γ : TyEnv) : ImpExpr → Prop
  | lit {n : Int} : 0 ≤ n ∧ n < 2 ^ 64 → LoTy Γ (.lit (.int n))
  | var {x : String} {t : NfTy} : Γ.lookup x = some t → loTyOk t = true → LoTy Γ (.var x)

/-- The type of the component `i` of a value of the tuple type `t`, and `none` when `t` is not a
    tuple type with more than `i` components. -/
def tupProjTy : NfTy → Nat → Option NfTy
  | .tcons h _, 0 => some h
  | .tcons _ t, i + 1 => tupProjTy t i
  | _, _ => none

mutual
/-- **The typing judgement of the front.** From the environment `Γ`, the expression has the
    type `t` and leaves the environment `Γ'`, at the call typing `S`. -/
inductive FrontTy (S : String → List NfTy → Option NfTy) :
    TyEnv → ImpExpr → NfTy → TyEnv → Prop
  | var {Γ : TyEnv} {x : String} {t : NfTy} : Γ.lookup x = some t → FrontTy S Γ (.var x) t Γ
  | lit {Γ : TyEnv} {l : ImpLit} {t : NfTy} : litTy l = some t → FrontTy S Γ (.lit l) t Γ
  | unitVal {Γ : TyEnv} : FrontTy S Γ .unitVal .unit Γ
  | typeAscription {Γ Γ' : TyEnv} {e : ImpExpr} {τ : String} {t : NfTy} :
      FrontTy S Γ e t Γ' → FrontTy S Γ (.typeAscription e τ) t Γ'
  | seq {Γ Γa Γ' : TyEnv} {a b : ImpExpr} {ta t : NfTy} :
      FrontTy S Γ a ta Γa → FrontTy S Γa b t Γ' → FrontTy S Γ (.seq a b) t Γ'
  | letBind {Γ Γv Γ' : TyEnv} {x : String} {v b : ImpExpr} {tv t : NfTy} :
      FrontTy S Γ v tv Γv → FrontTy S ((x, tv) :: Γv) b t Γ' →
      FrontTy S Γ (.letBind x v b) t Γ'
  | assign {Γ Γr : TyEnv} {x : String} {r : ImpExpr} {tr : NfTy} :
      FrontTy S Γ r tr Γr → FrontTy S Γ (.assign x r) .unit ((x, tr) :: Γr)
  | app {Γ Γa : TyEnv} {f : String} {args : List ImpExpr} {as : List NfTy} {r : NfTy} :
      f ≠ "repeat" → FrontTyArgs S Γ args as Γa → S f as = some r →
      FrontTy S Γ (.app f args) r Γa
  | tuple {Γ : TyEnv} {es : List ImpExpr} {as : List NfTy} :
      AtomsTy Γ es as → FrontTy S Γ (.tuple es) (tupTy as) Γ
  | proj {Γ Γ' : TyEnv} {e : ImpExpr} {i : Nat} {t h : NfTy} :
      FrontTy S Γ e t Γ' → tupProjTy t i = some h → FrontTy S Γ (.proj e i) h Γ'
  | forFold {Γ Γb : TyEnv} {i : String} {lo hi body : ImpExpr} {th tb : NfTy} :
      LoTy Γ lo → AtomTy Γ hi th → (boundOk 0 th || litBoundOk 0 hi) = true →
      FrontTy S ((i, .word 64) :: loopEnvTy Γ i body) body tb Γb →
      KeepsTys Γb (carriedTy Γ i body) →
      FrontTy S Γ (.forFold i lo hi body) .unit (loopEnvTy Γ i body)
  | forFoldRev {Γ Γb : TyEnv} {i : String} {lo hi body : ImpExpr} {th tb : NfTy} :
      LoTy Γ lo → AtomTy Γ hi th → (boundOk 0 th || litBoundOk 0 hi) = true →
      FrontTy S ((i, .word 64) :: loopEnvTy Γ i body) body tb Γb →
      KeepsTys Γb (carriedTy Γ i body) →
      FrontTy S Γ (.forFoldRev i lo hi body) .unit (loopEnvTy Γ i body)
  | ifThenElse {Γ Γc Γa Γb : TyEnv} {c a b : ImpExpr} {t : NfTy} :
      FrontTy S Γ c .bit Γc → FrontTy S Γc a t Γa → FrontTy S Γc b t Γb →
      KeepsTys Γa (condCarriedTy Γc a b) → KeepsTys Γb (condCarriedTy Γc a b) →
      FrontTy S Γ (.ifThenElse c a b) t (condEnvTy Γc Γa Γb a b)

/-- The arguments of a call, typed left to right, each from the environment the arguments
    before it leave. -/
inductive FrontTyArgs (S : String → List NfTy → Option NfTy) :
    TyEnv → List ImpExpr → List NfTy → TyEnv → Prop
  | nil {Γ : TyEnv} : FrontTyArgs S Γ [] [] Γ
  | cons {Γ Γ₁ Γ₂ : TyEnv} {e : ImpExpr} {es : List ImpExpr} {a : NfTy} {as : List NfTy} :
      FrontTy S Γ e a Γ₁ → FrontTyArgs S Γ₁ es as Γ₂ → FrontTyArgs S Γ (e :: es) (a :: as) Γ₂
end

/-! ## 4. Atoms, bounds, loops and conditionals -/

theorem litOut_of_litTy {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) {l : ImpLit}
    {t : NfTy} (h : litTy l = some t) :
    ∃ o, litOut tgt σ l = some o ∧ o.t = t ∧ tysOf o.σ = tysOf σ := by
  cases l with
  | bool b =>
      simp only [litTy, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, rfl, by simp [bind1N]⟩
  | unit =>
      simp only [litTy, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, rfl, by simp [bind1N]⟩
  | _ =>
      simp only [litTy, Option.bind_eq_some_iff] at h
      obtain ⟨⟨t', v⟩, hl, h⟩ := h
      split at h
      · rename_i hs
        simp only [Option.some.injEq] at h
        subst h
        simp only [litOut, hl, Option.bind_some, hs, if_true]
        exact ⟨_, rfl, rfl, by simp [bind1N]⟩
      · cases h

theorem atomOut_of_atomTy {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {e : ImpExpr} {t : NfTy}
    (h : AtomTy (tysOf σ) e t) :
    ∃ o, atomOut σ e = some o ∧ o.t = t ∧ tysOf o.σ = tysOf σ := by
  cases h with
  | var hx =>
      rw [lookup_tysOf] at hx
      obtain ⟨p, hp, hpt⟩ := Option.map_eq_some_iff.mp hx
      exact ⟨⟨Γ, p.1, .nil, σ, p.2⟩, by simp [atomOut, hp], hpt, rfl⟩
  | lit hl => exact litOut_of_litTy none σ hl

theorem argsOut_of_atomsTy {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {es : List ImpExpr}
    {as : List NfTy} (h : AtomsTy (tysOf σ) es as) :
    ∃ oa, argsOut σ es = some oa ∧ oa.as = as ∧ tysOf oa.σ = tysOf σ := by
  induction es generalizing Γ as with
  | nil =>
      cases h
      exact ⟨_, rfl, rfl, rfl⟩
  | cons e es ih =>
      cases h with
      | cons he hes =>
          obtain ⟨o, ho, hot, hoσ⟩ := atomOut_of_atomTy σ he
          obtain ⟨os, hos, hosa, hosσ⟩ := ih o.σ (hoσ ▸ hes)
          simp only [argsOut, ho, Option.bind_some, hos, Option.map_some]
          exact ⟨_, rfl, by simp [hot, hosa], hosσ.trans hoσ⟩

theorem loOut_of_loTy {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {lo : ImpExpr}
    (h : LoTy (tysOf σ) lo) : ∃ e, loOut σ lo = some e := by
  cases h with
  | @lit n hn => exact ⟨mkE (.ilit .int n) .nil, by simp only [loOut, if_pos hn]⟩
  | var hx ht =>
      rw [lookup_tysOf] at hx
      obtain ⟨p, hp, hpt⟩ := Option.map_eq_some_iff.mp hx
      subst hpt
      exact ⟨mkE (.boundInt p.1) (.cons p.2 .nil), by simp [loOut, hp, ht]⟩

theorem ctrOut_t {Γ₃ : Ctxt nfDialect} (cs : List NfTy) (i : String)
    (σB : NfEnv (cs ++ NfTy.word 64 :: Γ₃)) (loV : Var Γ₃ NfTy.int)
    (rev : Option (Var Γ₃ (NfTy.word 64))) : (ctrOut cs i σB loV rev).t = .word 64 := by
  cases rev <;> rfl

theorem ctrOut_tysOf {Γ₃ : Ctxt nfDialect} (cs : List NfTy) (i : String)
    (σB : NfEnv (cs ++ NfTy.word 64 :: Γ₃)) (loV : Var Γ₃ NfTy.int)
    (rev : Option (Var Γ₃ (NfTy.word 64))) :
    tysOf (ctrOut cs i σB loV rev).σ = tysOf σB := by
  cases rev <;> simp [ctrOut, bind1N, bind1, Out.comp]

/-- **The loop of the front from typed parts.** When the body, from an environment erasing
    to the counter in front of the carried names `ps` and the names other than the counter,
    gives an output whose environment keeps the types of `ps`, the loop gives an output of
    the unit type, whose environment erases to the carried names in front of the names other
    than the counter. -/
theorem loopOut_of_body {Γ Γ₃ : Ctxt nfDialect} (tgt : Option String)
    (pre₀ : NFPre nfDialect Γ Γ₃) (σ₃ : NfEnv Γ₃) (loV : Var Γ₃ NfTy.int)
    (tripV : Var Γ₃ (NfTy.word 64)) (rev : Option (Var Γ₃ (NfTy.word 64))) (i : String)
    (ps : TyEnv) (xs : List String) (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ)) (Γb : TyEnv)
    (hxs : xs = ps.map (·.1)) (hcs : cs = ps.map (·.2))
    (hrec : ∀ {Δ : Ctxt nfDialect} (σ : NfEnv Δ),
      tysOf σ = (i, .word 64) :: (ps ++ (tysOf σ₃).filter fun p => p.1 != i) →
        ∃ o, rec σ = some o ∧ tysOf o.σ = Γb)
    (hkeep : KeepsTys Γb ps) :
    ∃ o, loopOut tgt pre₀ σ₃ loV tripV rev i xs cs inits rec = some o ∧ o.t = .unit ∧
      tysOf o.σ = ps ++ (tysOf σ₃).filter fun p => p.1 != i := by
  subst hxs hcs
  obtain ⟨ob, hob, hσb⟩ := hrec
    ((i, ⟨(ctrOut (ps.map (·.2)) i (loopEnv σ₃ i (ps.map (·.1)) (ps.map (·.2))
        (headVars (ps.map (·.2))) fun v => Var.shiftApp (d := nfDialect) (ps.map (·.2)) v.there)
        loV rev).t, (ctrOut (ps.map (·.2)) i (loopEnv σ₃ i (ps.map (·.1)) (ps.map (·.2))
        (headVars (ps.map (·.2))) fun v => Var.shiftApp (d := nfDialect) (ps.map (·.2)) v.there)
        loV rev).res⟩) ::
      (ctrOut (ps.map (·.2)) i (loopEnv σ₃ i (ps.map (·.1)) (ps.map (·.2))
        (headVars (ps.map (·.2))) fun v => Var.shiftApp (d := nfDialect) (ps.map (·.2)) v.there)
        loV rev).σ)
    (by simp [ctrOut_t, ctrOut_tysOf, loopEnv, tysOf_bindAll, tysOf_filter, zip_map_fst_snd])
  obtain ⟨rets, hrets⟩ := varsAt_of_keeps ob.σ ps (hσb ▸ hkeep)
  simp only [loopOut, hob, Option.bind_some, hrets, Option.map_some]
  exact ⟨_, rfl, rfl, by simp [bind1N, loopEnv, tysOf_bindAll, tysOf_filter, zip_map_fst_snd]⟩

/-- `loopOut_of_body` at the carried entries `carried σ₃ i b` of the front. -/
theorem loopOut_of_carried {Γ Γ₃ : Ctxt nfDialect} (tgt : Option String)
    (pre₀ : NFPre nfDialect Γ Γ₃) (σ₃ : NfEnv Γ₃) (loV : Var Γ₃ NfTy.int)
    (tripV : Var Γ₃ (NfTy.word 64)) (rev : Option (Var Γ₃ (NfTy.word 64))) (i : String)
    (b : ImpExpr) (Γ₀ Γb : TyEnv) (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ))
    (hσ₃ : tysOf σ₃ = Γ₀)
    (hrec : ∀ {Δ : Ctxt nfDialect} (σ : NfEnv Δ),
      tysOf σ = (i, .word 64) :: loopEnvTy Γ₀ i b → ∃ o, rec σ = some o ∧ tysOf o.σ = Γb)
    (hkeep : KeepsTys Γb (carriedTy Γ₀ i b)) :
    ∃ o, loopOut tgt pre₀ σ₃ loV tripV rev i ((carried σ₃ i b).map (·.1))
        (entriesVars (carried σ₃ i b)).1 (entriesVars (carried σ₃ i b)).2 rec = some o ∧
      o.t = .unit ∧ tysOf o.σ = loopEnvTy Γ₀ i b := by
  subst hσ₃
  have hW := carried_tysOf σ₃ i b
  have hxs : (carried σ₃ i b).map (·.1) = (carriedTy (tysOf σ₃) i b).map (·.1) := by
    rw [← hW, List.map_map]
    rfl
  have hcs : (entriesVars (carried σ₃ i b)).1 = (carriedTy (tysOf σ₃) i b).map (·.2) := by
    rw [entriesVars_fst, ← hW, List.map_map]
    rfl
  exact loopOut_of_body tgt pre₀ σ₃ loV tripV rev i _ _ _ _ rec Γb hxs hcs hrec hkeep

theorem zip_fst_snd_append (ps qs : TyEnv) :
    (ps.map (·.1) ++ qs.map (·.1)).zip (ps.map (·.2) ++ qs.map (·.2)) = ps ++ qs := by
  rw [← List.map_append, ← List.map_append, zip_map_fst_snd]

/-- **The conditional of the front from typed arms.** When the arms give outputs of one type
    whose environments keep the types of the carried names `ps`, the conditional gives an
    output of that type, whose environment erases to the carried names and the names both
    arms bind in front of the environment after the condition. -/
theorem condOut_of_arms {Γ Γc : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γc) (σc : NfEnv Γc)
    (cV : Var Γc NfTy.bit) (ps : TyEnv) (xs : List String) (cs : List NfTy)
    (oa ob : Out Γc) (hxs : xs = ps.map (·.1)) (hcs : cs = ps.map (·.2)) (hab : ob.t = oa.t)
    (hka : KeepsTys (tysOf oa.σ) ps) (hkb : KeepsTys (tysOf ob.σ) ps) :
    ∃ o, condOut pre₀ σc cV xs cs (some oa) (some ob) = some o ∧ o.t = oa.t ∧
      tysOf o.σ = (ps ++ condFreshTy (tysOf σc) (tysOf oa.σ) (tysOf ob.σ)) ++ tysOf σc := by
  subst hxs hcs
  have hfa : KeepsTys (tysOf oa.σ) (ps ++ condFresh σc oa.σ ob.σ) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hka p hp
    · rw [condFresh_tysOf] at hp
      exact (condFreshTy_mem hp).1
  have hfb : KeepsTys (tysOf ob.σ) (ps ++ condFresh σc oa.σ ob.σ) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hkb p hp
    · rw [condFresh_tysOf] at hp
      exact (condFreshTy_mem hp).2
  obtain ⟨ra, hra⟩ := varsAt_of_keeps' oa.σ _ _ _ (List.map_append ..).symm
    (List.map_append ..).symm hfa
  obtain ⟨rb, hrb⟩ := varsAt_of_keeps' ob.σ _ _ _ (List.map_append ..).symm
    (List.map_append ..).symm hfb
  simp only [condOut, Option.bind_some]
  rw [dif_pos hab, hra, Option.bind_some, hrb, Option.map_some]
  split
  · rename_i hu
    exact ⟨_, rfl, hu.symm, by
      simp [bind1N, tysOf_bindAll, zip_fst_snd_append, condFresh_tysOf]⟩
  · exact ⟨_, rfl, rfl, by simp [condEnv, tysOf_bindAll, zip_fst_snd_append, condFresh_tysOf]⟩

/-- `condOut_of_arms` at the carried entries `condCarried σc a b` of the front. -/
theorem condOut_of_carried {Γ Γc : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γc)
    (σc : NfEnv Γc) (cV : Var Γc NfTy.bit) (a b : ImpExpr) (oa ob : Out Γc)
    (Γc₀ Γa₀ Γb₀ : TyEnv) (ta : NfTy) (hσc : tysOf σc = Γc₀) (hσa : tysOf oa.σ = Γa₀)
    (hσb : tysOf ob.σ = Γb₀) (hta : oa.t = ta) (htb : ob.t = ta)
    (hka : KeepsTys Γa₀ (condCarriedTy Γc₀ a b)) (hkb : KeepsTys Γb₀ (condCarriedTy Γc₀ a b)) :
    ∃ o, condOut pre₀ σc cV ((condCarried σc a b).map (·.1))
        (entriesVars (condCarried σc a b)).1 (some oa) (some ob) = some o ∧ o.t = ta ∧
      tysOf o.σ = condEnvTy Γc₀ Γa₀ Γb₀ a b := by
  subst hσc hσa hσb hta
  have hW := condCarried_tysOf σc a b
  have hxs : (condCarried σc a b).map (·.1) = (condCarriedTy (tysOf σc) a b).map (·.1) := by
    rw [← hW, List.map_map]
    rfl
  have hcs : (entriesVars (condCarried σc a b)).1 = (condCarriedTy (tysOf σc) a b).map (·.2) := by
    rw [entriesVars_fst, ← hW, List.map_map]
    rfl
  exact condOut_of_arms pre₀ σc cV _ _ _ oa ob hxs hcs htb hka hkb

/-! ## 5. A derivation gives an output -/

/-- A projection at a component type `tupProjTy` gives is translated by `projOut`, to an
    output of that type whose environment of names erases to the same environment. -/
theorem projOut_of_tupProjTy (tgt : Option String) (i : Nat) :
    ∀ (t : NfTy) {h : NfTy} {Δ : Ctxt nfDialect} (σ : NfEnv Δ) (x : Var Δ t),
      tupProjTy t i = some h →
      ∃ o, projOut tgt σ t x i = some o ∧ o.t = h ∧ tysOf o.σ = tysOf σ := by
  induction i with
  | zero =>
      intro t h Δ σ x hp
      cases t with
      | tcons h₀ t =>
          simp only [tupProjTy, Option.some.injEq] at hp
          subst hp
          exact ⟨_, rfl, rfl, by simp [bind1N]⟩
      | _ => simp [tupProjTy] at hp
  | succ i ih =>
      intro t h Δ σ x hp
      cases t with
      | tcons h₀ t =>
          simp only [tupProjTy] at hp
          obtain ⟨o, ho, hot, hoσ⟩ := ih t (bind1 σ (.ttail h₀ t) (.cons x .nil)).σ
            (bind1 σ (.ttail h₀ t) (.cons x .nil)).res hp
          refine ⟨(bind1 σ (.ttail h₀ t) (.cons x .nil)).comp o,
            by simp only [projOut, ho, Option.map_some], hot, ?_⟩
          simp only [Out.comp, hoσ, bind1, tysOf_mapV]
      | _ => simp [tupProjTy] at hp

mutual
/-- **A derivation gives an output of the front.** From an environment of names erasing to
    `Γ`, an expression with a derivation `FrontTy S Γ e t Γ'` is translated by `impToNF`, to an
    output of the type `t` whose environment of names erases to `Γ'`. -/
theorem impToNF_out_of_frontTy {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv}
    {e : ImpExpr} {t : NfTy} (h : FrontTy S Γ e t Γ') :
    ∀ (tgt : Option String) {Δ : Ctxt nfDialect} (σ : NfEnv Δ), tysOf σ = Γ →
      ∃ o, impToNF S tgt σ e = some o ∧ o.t = t ∧ tysOf o.σ = Γ' := by
  intro tgt Δ σ hσ
  match h with
  | .var hx =>
      subst hσ
      obtain ⟨o, ho, hot, hoσ⟩ := atomOut_of_atomTy σ (.var hx)
      exact ⟨o, by simpa [impToNF] using ho, hot, hoσ⟩
  | .lit hl =>
      subst hσ
      obtain ⟨o, ho, hot, hoσ⟩ := litOut_of_litTy tgt σ hl
      exact ⟨o, by simpa [impToNF] using ho, hot, hoσ⟩
  | .unitVal =>
      simp only [impToNF]
      exact ⟨_, rfl, rfl, by simp [bind1N, hσ]⟩
  | .typeAscription he =>
      obtain ⟨o, ho, hot, hoσ⟩ := impToNF_out_of_frontTy he tgt σ hσ
      exact ⟨o, by simpa [impToNF] using ho, hot, hoσ⟩
  | .seq ha hb =>
      obtain ⟨oa, hoa, -, hσa⟩ := impToNF_out_of_frontTy ha none σ hσ
      obtain ⟨ob, hob, htb, hσb⟩ := impToNF_out_of_frontTy hb tgt oa.σ hσa
      exact ⟨oa.comp ob, by simp only [impToNF, hoa, hob, Option.bind_some, Option.map_some],
        htb, hσb⟩
  | .letBind (x := x) hv hb =>
      obtain ⟨ov, hov, htv, hσv⟩ := impToNF_out_of_frontTy hv (some x) σ hσ
      obtain ⟨ob, hob, htb, hσb⟩ := impToNF_out_of_frontTy hb tgt
        ((x, ⟨ov.t, ov.res⟩) :: ov.σ) (by simp [htv, hσv])
      exact ⟨ov.comp ob, by simp only [impToNF, hov, hob, Option.bind_some, Option.map_some],
        htb, hσb⟩
  | .assign (x := x) hr =>
      obtain ⟨o, ho, hot, hoσ⟩ := impToNF_out_of_frontTy hr (some x) σ hσ
      simp only [impToNF, ho, Option.map_some]
      exact ⟨_, rfl, rfl, by simp [Out.comp, bind1N, hot, hoσ]⟩
  | .app (f := f) (r := r) hf hargs hS =>
      obtain ⟨oa, hoa, has, hσa⟩ := impArgsNF_out_of_frontTyArgs hargs σ hσ
      subst has
      rw [impToNF_app_call S tgt σ hf, hoa, Option.bind_some, hS, Option.map_some]
      exact ⟨_, rfl, rfl, by simp [hσa]⟩
  | .tuple hes =>
      subst hσ
      obtain ⟨oa, hoa, has, hσa⟩ := argsOut_of_atomsTy σ hes
      simp only [impToNF, hoa, Option.map_some]
      exact ⟨_, rfl, by simp [has], by simp [hσa]⟩
  | .proj he hp =>
      obtain ⟨oe, hoe, hot, hoσ⟩ := impToNF_out_of_frontTy he none σ hσ
      obtain ⟨op, hop, hpt, hpσ⟩ := projOut_of_tupProjTy tgt _ _ oe.σ oe.res
        (by rw [hot]; exact hp)
      exact ⟨oe.comp op, by simp only [impToNF, hoe, hop, Option.bind_some, Option.map_some],
        hpt, hpσ.trans hoσ⟩
  | .forFold (i := i) (body := body) (Γb := Γb) hlo hhi hb hbody hkeep =>
      subst hσ
      obtain ⟨eLo, hLo⟩ := loOut_of_loTy σ hlo
      obtain ⟨oHi, hHi, htHi, hσHi⟩ := atomOut_of_atomTy (loBind σ eLo).σ
        (by simpa [loBind] using hhi)
      have hc : (boundOk 0 oHi.t || litBoundOk 0 _) = true := htHi ▸ hb
      simp only [impToNF, hLo, Option.bind_some, hHi, hc, if_true]
      refine loopOut_of_carried tgt _ _ _ _ _ i body (tysOf σ) Γb _
        (by simp [bind1, hσHi, loBind]) (fun σB hσB => ?_) hkeep
      obtain ⟨o, ho, -, hoσ⟩ := impToNF_out_of_frontTy hbody none σB hσB
      exact ⟨o, ho, hoσ⟩
  | .forFoldRev (i := i) (body := body) (Γb := Γb) hlo hhi hb hbody hkeep =>
      subst hσ
      obtain ⟨eLo, hLo⟩ := loOut_of_loTy σ hlo
      obtain ⟨oHi, hHi, htHi, hσHi⟩ := atomOut_of_atomTy (loBind σ eLo).σ
        (by simpa [loBind] using hhi)
      have hc : (boundOk 0 oHi.t || litBoundOk 0 _) = true := htHi ▸ hb
      simp only [impToNF, hLo, Option.bind_some, hHi, hc, if_true]
      refine loopOut_of_carried tgt _ _ _ _ _ i body (tysOf σ) Γb _
        (by simp [bind1, hσHi, loBind]) (fun σB hσB => ?_) hkeep
      obtain ⟨o, ho, -, hoσ⟩ := impToNF_out_of_frontTy hbody none σB hσB
      exact ⟨o, ho, hoσ⟩
  | .ifThenElse (a := a) (b := b) hc ha hb hka hkb =>
      obtain ⟨oc, hoc, htc, hσc⟩ := impToNF_out_of_frontTy hc none σ hσ
      obtain ⟨oa, hoa, hta, hσa⟩ := impToNF_out_of_frontTy ha none oc.σ hσc
      obtain ⟨ob, hob, htb, hσb⟩ := impToNF_out_of_frontTy hb none oc.σ hσc
      simp only [impToNF, hoc, Option.bind_some]
      rw [dif_pos htc, hoa, hob]
      exact condOut_of_carried _ _ _ a b oa ob _ _ _ _ hσc hσa hσb hta htb hka hkb

/-- **A derivation of the arguments gives an output of `impArgsNF`**, at the derived types
    and environment. -/
theorem impArgsNF_out_of_frontTyArgs {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv}
    {args : List ImpExpr} {as : List NfTy} (h : FrontTyArgs S Γ args as Γ') :
    ∀ {Δ : Ctxt nfDialect} (σ : NfEnv Δ), tysOf σ = Γ →
      ∃ oa, impArgsNF S σ args = some oa ∧ oa.as = as ∧ tysOf oa.σ = Γ' := by
  intro Δ σ hσ
  match h with
  | .nil => exact ⟨_, rfl, rfl, hσ⟩
  | .cons he hes =>
      obtain ⟨o, ho, hot, hoσ⟩ := impToNF_out_of_frontTy he none σ hσ
      obtain ⟨os, hos, hosa, hosσ⟩ := impArgsNF_out_of_frontTyArgs hes o.σ hoσ
      simp only [impArgsNF, ho, Option.bind_some, hos, Option.map_some]
      exact ⟨_, rfl, by simp [hot, hosa], hosσ⟩
end

/-- **An expression with a derivation is translated**: from an environment of names erasing
    to `Γ`, `impToNF` returns an output on an expression with a derivation at `Γ`. -/
theorem impToNF_isSome_of_frontTy {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv}
    {e : ImpExpr} {t : NfTy} (h : FrontTy S Γ e t Γ') (tgt : Option String)
    {Δ : Ctxt nfDialect} (σ : NfEnv Δ) (hσ : tysOf σ = Γ) :
    (impToNF S tgt σ e).isSome := by
  obtain ⟨o, ho, -, -⟩ := impToNF_out_of_frontTy h tgt σ hσ
  simp [ho]

theorem tysOf_entryEnv : ∀ ps : List (String × NfTy), tysOf (entryEnv ps) = ps
  | [] => rfl
  | (x, t) :: ps => by
      simp only [entryEnv, tysOf_cons]
      erw [tysOf_mapV]
      exact congrArg _ (tysOf_entryEnv ps)

/-- An atom has no `whileFold`. -/
theorem whileFoldFree_of_atomTy {Γ : TyEnv} {e : ImpExpr} {t : NfTy} (h : AtomTy Γ e t) :
    whileFoldFree e = true := by
  cases h <;> simp [whileFoldFree]

/-- A list of atoms has no `whileFold`. -/
theorem whileFoldFree_of_atomsTy {Γ : TyEnv} {es : List ImpExpr} {as : List NfTy}
    (h : AtomsTy Γ es as) : whileFoldFree.freeList es = true := by
  induction h with
  | nil => rfl
  | cons ha _ ih => simp [whileFoldFree.freeList, whileFoldFree_of_atomTy ha, ih]

/-- A lower bound of a counted loop has no `whileFold`. -/
theorem whileFoldFree_of_loTy {Γ : TyEnv} {e : ImpExpr} (h : LoTy Γ e) :
    whileFoldFree e = true := by
  cases h <;> simp [whileFoldFree]

mutual
/-- **An expression with a derivation has no `whileFold`.** -/
theorem whileFoldFree_of_frontTy {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv}
    {e : ImpExpr} {t : NfTy} (h : FrontTy S Γ e t Γ') : whileFoldFree e = true :=
  match h with
  | .var _ => by simp [whileFoldFree]
  | .lit _ => by simp [whileFoldFree]
  | .unitVal => by simp [whileFoldFree]
  | .typeAscription h => by simpa [whileFoldFree] using whileFoldFree_of_frontTy h
  | .seq ha hb => by
      simp [whileFoldFree, whileFoldFree_of_frontTy ha, whileFoldFree_of_frontTy hb]
  | .letBind hv hb => by
      simp [whileFoldFree, whileFoldFree_of_frontTy hv, whileFoldFree_of_frontTy hb]
  | .assign hr => by simpa [whileFoldFree] using whileFoldFree_of_frontTy hr
  | .app _ ha _ => by simpa [whileFoldFree] using whileFoldFree_of_frontTyArgs ha
  | .tuple ha => by simpa [whileFoldFree] using whileFoldFree_of_atomsTy ha
  | .proj h _ => by simpa [whileFoldFree] using whileFoldFree_of_frontTy h
  | .forFold hlo hhi _ hb _ => by
      simp [whileFoldFree, whileFoldFree_of_loTy hlo, whileFoldFree_of_atomTy hhi,
        whileFoldFree_of_frontTy hb]
  | .forFoldRev hlo hhi _ hb _ => by
      simp [whileFoldFree, whileFoldFree_of_loTy hlo, whileFoldFree_of_atomTy hhi,
        whileFoldFree_of_frontTy hb]
  | .ifThenElse hc ha hb _ _ => by
      simp [whileFoldFree, whileFoldFree_of_frontTy hc, whileFoldFree_of_frontTy ha,
        whileFoldFree_of_frontTy hb]

/-- The arguments of a call with a derivation have no `whileFold`. -/
theorem whileFoldFree_of_frontTyArgs {S : String → List NfTy → Option NfTy} {Γ Γ' : TyEnv}
    {es : List ImpExpr} {as : List NfTy} (h : FrontTyArgs S Γ es as Γ') :
    whileFoldFree.freeList es = true :=
  match h with
  | .nil => rfl
  | .cons he hes => by
      simp [whileFoldFree.freeList, whileFoldFree_of_frontTy he, whileFoldFree_of_frontTyArgs hes]
end

/-- **A callee body with a derivation has a body**: when the body of the function `c` has a
    derivation from its parameters at the type `r`, at the call typing `crateSigOf fs base`,
    `crateBody` returns a program at the parameter types and `r`. -/
theorem crateBody_isSome_of_frontTy (fs : List CrateFn) (c : CrateFn) {as : List NfTy}
    {r : NfTy} (base : String → List NfTy → Option NfTy) {Γ' : TyEnv}
    (has : entryCtx c.params = as) (h : FrontTy (crateSigOf fs base) c.params c.body r Γ') :
    (NFInline.crateBody fs c as r base).isSome := by
  obtain ⟨o, ho, hot, -⟩ := impToNF_out_of_frontTy h none (entryEnv c.params)
    (tysOf_entryEnv _)
  simp only [NFInline.crateBody, whileFoldFree_of_frontTy h, if_true, ho, Option.bind_some]
  rw [dif_pos ⟨has, hot⟩]
  rfl

end CatCrypt.Crypto.Hax.FrontTyping
