/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AscendDecide
public import CatCrypt.Crypto.SecureCompilation.Ascent.Phases
public import CatCrypt.Crypto.SecureCompilation.Ascent.WhileTop

/-!
# Total abstraction with guards

`ascendG fuel c` abstracts every `LowCT` command `c` to a pure word transformer over
`AField = String → ZMod 2^64` together with a list of `Guard`s: the side conditions
the abstraction does not discharge on its own. The abstraction is total — every
constructor produces a transformer and a guard list — and `ascendG_sound` states
that under the guards the transformer is a `CorresU` correspondent of `c` at the
unified waist `semU fuel`, over the non-temp word relation `SRwordNT`.

The guards are of five kinds:

* `range x e` — the Nat-model side condition `SExpr.inRange` for an `RScalarSetExpr`
  whose expression is source-clean but outside the arithmetic fragment
  `IsArithClean`; the abstract value is the Nat-model `SExpr.eval`, and the guard
  says no wrap occurs on the current store;
* `loopHalts name fuel fb` — the abstract do-while on `name` with body step `fb`
  halts within `fuel`, the trip-count bound of an `RWhileNz`;
* `unsupported ctor` — the constructor `ctor` has no rule at this waist; the guard
  never holds, so the correspondence for that node is stated under an unsatisfiable
  precondition;
* `assert label` — an `RAssert` label, carried through for the proof context; the
  node reads nothing and the semantics is the identity, so the guard holds;
* the pull-backs `after`, `whenNz`, `everyTrip`, `loopBody` — a sub-program's guard
  transported through the abstract step that precedes it (the second half of a
  sequence, the body of a conditional, the trips of a counted loop, the trips of a
  while loop).

The value abstraction is the one of `ExprLeaf`: `RScalarSet` and arithmetic
`RScalarSetExpr` terminals go through `corres_setScalar_NT` and `corres_setExpr`
with no guard; the counted loop goes through the trip-indexed rule
`corresU_for_trips`, the guarded conditional through `corresU_cond`, the φ-merge
conditional through `corres_if_NT`, and the while loop through `corresU_whileNz`.

On the decidable straight-line fragments (`isAscendableB`, `isAscendableExprB`)
`ascendG` emits no guard and its transformer is `asemW` / `asemWExpr`
(`ascendG_isAscendableB`, `ascendG_isAscendableExprB`), so the existing `ascend!` /
`ascend_expr!` demos are instances of `ascendG_sound`.

## Main definitions

* `Guard`, `Guard.holds`, `guardsHold` — the guard language and its meaning on a store
* `ascendG` — the total abstraction
* `ascendG_sound` — soundness at the unified waist
* `ascendG_sound_scalar` — the same over `Corres` on loop-free commands
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA

/-! ## Store combinators -/

/-- The store update `x := n` by a literal. -/
def setLit (x : String) (n : Nat) (a : AField) : AField :=
  fun s => if s = x then (n : ZMod (2 ^ 64)) else a s

/-- The store update `x := v`. -/
def setVal (x : String) (v : ZMod (2 ^ 64)) (a : AField) : AField :=
  fun s => if s = x then v else a s

/-- The Nat-model view of a word store: each value read as its canonical residue. -/
def natStore (a : AField) : String → Nat := fun s => (a s).val

/-- The Nat-model value of an expression on a word store, cast back to the word ring. -/
def natEval (e : SExpr) (a : AField) : ZMod (2 ^ 64) := (e.eval (natStore a) : ZMod (2 ^ 64))

/-- The φ-merge select on the abstract store: `nv := if a name = 0 then ev else tv`. -/
def phiSet (name nv : String) (tv ev : Nat) (a : AField) : AField :=
  fun s => if s = nv then
      (if a name = 0 then (ev : ZMod (2 ^ 64)) else (tv : ZMod (2 ^ 64)))
    else a s

/-- The abstract guard of `RWhileNz name _` and of the guarded `RIfNz name _ RSkip`:
    the word at `name` is nonzero. -/
def nzB (name : String) (a : AField) : Bool := decide (a name ≠ 0)

/-! ## Abstract loops -/

/-- The counted-loop fold: trip `n` sets the counter by `setA n` and runs the body
    step `fb`; the last trip is peeled, as in `semRForD`. -/
def forFold {A : Type} (setA : Nat → A → A) (fb : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => fb (setA n (forFold setA fb n a))

/-- The abstract fuel-bounded do-while: run the body step, stop when the guard is
    false, else continue; at fuel `0` the store is returned unchanged (that run is
    excluded by `ahalts`). Mirrors `semScalarWhile`. -/
def awhile {A : Type} (g : A → Bool) (fb : A → A) : Nat → A → A
  | 0, a => a
  | k + 1, a => if g (fb a) then awhile g fb k (fb a) else fb a

/-- The abstract do-while halts within the fuel. -/
def ahalts {A : Type} (g : A → Bool) (fb : A → A) : Nat → A → Prop
  | 0, _ => False
  | k + 1, a => g (fb a) = true → ahalts g fb k (fb a)

/-- `Q` holds at the entry of every trip the abstract do-while runs within the fuel. -/
def atrips {A : Type} (Q : A → Prop) (g : A → Bool) (fb : A → A) : Nat → A → Prop
  | 0, _ => True
  | k + 1, a => Q a ∧ (g (fb a) = true → atrips Q g fb k (fb a))

instance ahalts.decidable {A : Type} (g : A → Bool) (fb : A → A) :
    ∀ (k : Nat) (a : A), Decidable (ahalts g fb k a)
  | 0, _ => isFalse (fun h => h)
  | k + 1, a =>
      haveI := ahalts.decidable g fb k (fb a)
      inferInstanceAs (Decidable (g (fb a) = true → ahalts g fb k (fb a)))

instance atrips.decidable {A : Type} (Q : A → Prop) [DecidablePred Q] (g : A → Bool)
    (fb : A → A) : ∀ (k : Nat) (a : A), Decidable (atrips Q g fb k a)
  | 0, _ => isTrue trivial
  | k + 1, a =>
      haveI := atrips.decidable Q g fb k (fb a)
      inferInstanceAs (Decidable (Q a ∧ (g (fb a) = true → atrips Q g fb k (fb a))))

/-! ## Deciding the expression side conditions -/

/-- `srcClean`, as a decision procedure (the `notTmpB` head-character test on
    variables, the `2 ^ 64` bound on literals). -/
def srcCleanB : SExpr → Bool
  | .SVar x => notTmpB x
  | .SLit n => litOkB n
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => srcCleanB a && srcCleanB b
  | _ => false

theorem srcCleanB_sound : ∀ (e : SExpr), srcCleanB e = true → srcClean e
  | .SVar x, h => notTmpB_sound x h
  | .SLit _, h => by simpa [srcClean, srcCleanB, litOkB] using h
  | .SAdd a b, h | .SSub a b, h | .SMul a b, h | .SAnd a b, h | .SXor a b, h
  | .SShl a b, h | .SShr a b, h | .SMulHiU a b, h => by
      simp only [srcCleanB, Bool.and_eq_true] at h
      exact ⟨srcCleanB_sound a h.1, srcCleanB_sound b h.2⟩

instance SExpr.decInRange (σ : String → Nat) : ∀ (e : SExpr), Decidable (e.inRange σ)
  | .SVar x => inferInstanceAs (Decidable (σ x < 2 ^ 64))
  | .SLit n => inferInstanceAs (Decidable (n < 2 ^ 64))
  | .SAdd a b =>
      haveI := SExpr.decInRange σ a; haveI := SExpr.decInRange σ b
      inferInstanceAs (Decidable (a.inRange σ ∧ b.inRange σ ∧ a.eval σ + b.eval σ < 2 ^ 64))
  | .SSub a b =>
      haveI := SExpr.decInRange σ a; haveI := SExpr.decInRange σ b
      inferInstanceAs (Decidable (a.inRange σ ∧ b.inRange σ ∧ b.eval σ ≤ a.eval σ))
  | .SMul a b =>
      haveI := SExpr.decInRange σ a; haveI := SExpr.decInRange σ b
      inferInstanceAs (Decidable (a.inRange σ ∧ b.inRange σ ∧ a.eval σ * b.eval σ < 2 ^ 64))
  | .SShr a b =>
      haveI := SExpr.decInRange σ a; haveI := SExpr.decInRange σ b
      inferInstanceAs (Decidable (a.inRange σ ∧ b.inRange σ ∧ b.eval σ < 64))
  | .SShl a b =>
      haveI := SExpr.decInRange σ a; haveI := SExpr.decInRange σ b
      inferInstanceAs (Decidable (a.inRange σ ∧ b.inRange σ ∧ b.eval σ < 64 ∧
        a.eval σ <<< b.eval σ < 2 ^ 64))
  | .SAnd a b | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b
  | .SMulHiS a b =>
      haveI := SExpr.decInRange σ a; haveI := SExpr.decInRange σ b
      inferInstanceAs (Decidable (a.inRange σ ∧ b.inRange σ))
  | .SLimb _ _ => isTrue trivial

/-! ## The guard language -/

/-- A side condition the abstraction leaves to the caller. -/
inductive Guard where
  /-- The Nat-model evaluation of `e`, assigned to `x`, stays in `u64` range on the
      store (`SExpr.inRange`): the abstract value is `SExpr.eval` and no wrap occurs. -/
  | range (x : String) (e : SExpr)
  /-- The abstract do-while on `name` with body step `fb` halts within `fuel` trips. -/
  | loopHalts (name : String) (fuel : Nat) (fb : AField → AField)
  /-- The constructor `ctor` has no rule at this waist. Never holds. -/
  | unsupported (ctor : String)
  /-- An `RAssert` label. The node is the identity on the store, so this holds. -/
  | assert (label : String)
  /-- `g` on the store after the abstract step `f`. -/
  | after (f : AField → AField) (g : Guard)
  /-- `g` when the word at `name` is nonzero. -/
  | whenNz (name : String) (g : Guard)
  /-- `g` at the entry of every trip `n < N` of the counted loop with counter `x` and
      body step `fb`, the counter set to `n`. -/
  | everyTrip (x : String) (N : Nat) (fb : AField → AField) (g : Guard)
  /-- `g` at the entry of every trip the do-while on `name` with body step `fb` runs
      within `fuel`. -/
  | loopBody (name : String) (fuel : Nat) (fb : AField → AField) (g : Guard)

/-- The meaning of a guard on a store. -/
def Guard.holds : Guard → AField → Prop
  | .range _ e, a => e.inRange (natStore a)
  | .loopHalts name fuel fb, a => ahalts (nzB name) fb fuel a
  | .unsupported _, _ => False
  | .assert _, _ => True
  | .after f g, a => g.holds (f a)
  | .whenNz name g, a => nzB name a = true → g.holds a
  | .everyTrip x N fb g, a => ∀ n, n < N → g.holds (setLit x n (forFold (setLit x) fb n a))
  | .loopBody name fuel fb g, a => atrips g.holds (nzB name) fb fuel a

instance Guard.decHolds : ∀ (g : Guard) (a : AField), Decidable (g.holds a)
  | .range _ e, a => SExpr.decInRange (natStore a) e
  | .loopHalts name fuel fb, a => ahalts.decidable (nzB name) fb fuel a
  | .unsupported _, _ => isFalse (fun h => h)
  | .assert _, _ => isTrue trivial
  | .after f g, a => Guard.decHolds g (f a)
  | .whenNz name g, a =>
      haveI := Guard.decHolds g a
      inferInstanceAs (Decidable (nzB name a = true → g.holds a))
  | .everyTrip x N fb g, a =>
      haveI : ∀ n, Decidable (g.holds (setLit x n (forFold (setLit x) fb n a))) :=
        fun n => Guard.decHolds g (setLit x n (forFold (setLit x) fb n a))
      inferInstanceAs (Decidable (∀ n, n < N → g.holds (setLit x n (forFold (setLit x) fb n a))))
  | .loopBody name fuel fb g, a =>
      haveI : DecidablePred g.holds := fun a => Guard.decHolds g a
      atrips.decidable g.holds (nzB name) fb fuel a

/-- Every guard of the list holds on the store. -/
def guardsHold (gs : List Guard) (a : AField) : Prop := ∀ g ∈ gs, g.holds a

instance (gs : List Guard) (a : AField) : Decidable (guardsHold gs a) :=
  inferInstanceAs (Decidable (∀ g ∈ gs, g.holds a))

theorem guardsHold_nil (a : AField) : guardsHold [] a := fun _ h => (List.not_mem_nil h).elim

theorem guardsHold_append {g₁ g₂ : List Guard} {a : AField} :
    guardsHold (g₁ ++ g₂) a ↔ guardsHold g₁ a ∧ guardsHold g₂ a := by
  simp only [guardsHold, List.mem_append, or_imp, forall_and]

theorem guardsHold_map_after {gs : List Guard} {f : AField → AField} {a : AField} :
    guardsHold (gs.map (Guard.after f)) a ↔ guardsHold gs (f a) := by
  simp only [guardsHold, List.forall_mem_map, Guard.holds]

theorem guardsHold_map_whenNz {gs : List Guard} {name : String} {a : AField} :
    guardsHold (gs.map (Guard.whenNz name)) a ↔ (nzB name a = true → guardsHold gs a) := by
  simp only [guardsHold, List.forall_mem_map, Guard.holds]
  exact ⟨fun h hnz g hg => h g hg hnz, fun h g hg hnz => h hnz g hg⟩

theorem guardsHold_map_everyTrip {gs : List Guard} {x : String} {N : Nat}
    {fb : AField → AField} {a : AField} :
    guardsHold (gs.map (Guard.everyTrip x N fb)) a ↔
      ∀ n, n < N → guardsHold gs (setLit x n (forFold (setLit x) fb n a)) := by
  simp only [guardsHold, List.forall_mem_map, Guard.holds]
  exact ⟨fun h n hn g hg => h g hg n hn, fun h g hg n hn => h n hn g hg⟩

/-- `atrips` distributes over a conjunction of predicates read off a guard list. -/
theorem atrips_guards {gs : List Guard} {g : AField → Bool} {fb : AField → AField} :
    ∀ (k : Nat) (a : AField),
      (∀ gd ∈ gs, atrips gd.holds g fb k a) ↔ atrips (guardsHold gs) g fb k a := by
  intro k
  induction k with
  | zero => intro a; simp [atrips]
  | succ k ih =>
      intro a
      simp only [atrips, guardsHold]
      constructor
      · intro h
        refine ⟨fun gd hgd => (h gd hgd).1, fun hg => (ih (fb a)).1 (fun gd hgd => (h gd hgd).2 hg)⟩
      · intro h gd hgd
        exact ⟨h.1 gd hgd, fun hg => (ih (fb a)).2 (h.2 hg) gd hgd⟩

theorem guardsHold_map_loopBody {gs : List Guard} {name : String} {fuel : Nat}
    {fb : AField → AField} {a : AField} :
    guardsHold (gs.map (Guard.loopBody name fuel fb)) a ↔
      atrips (guardsHold gs) (nzB name) fb fuel a := by
  simp only [guardsHold, List.forall_mem_map, Guard.holds]
  exact atrips_guards fuel a

/-! ## Loop-free commands: where the unified waist is `semScalar` -/

/-- No `RWhileNz` and no guarded conditional `RIfNz _ _ RSkip` below the spine: on
    such a command `semU fuel` is `semScalar` (`semU_eq_semScalar_of_loopFree`). -/
def loopFree : LowCT → Bool
  | .RSeq c₁ c₂ => loopFree c₁ && loopFree c₂
  | .RBlock body => loopFree body
  | .RFor _ _ body => loopFree body
  | .RLetU64Zero _ body => loopFree body
  | .RWhileNz _ _ => false
  | .RIfNz _ _ .RSkip => false
  | _ => true

/-- The `RSkip` test. -/
def isSkipB : LowCT → Bool
  | .RSkip => true
  | _ => false

theorem isSkipB_iff (c : LowCT) : isSkipB c = true ↔ c = .RSkip := by
  cases c <;> simp [isSkipB]

/-- A conditional whose else-branch is not `RSkip` is a leaf of the unified spine. -/
theorem isSeqLike_rIfNz_of_ne (name : String) (thenBr elseBr : LowCT) (h : elseBr ≠ .RSkip) :
    isSeqLike (.RIfNz name thenBr elseBr) = false := by
  cases elseBr <;> first | exact absurd rfl h | rfl

theorem semU_eq_semScalar_of_loopFree (fuel : Nat) :
    ∀ (c : LowCT), loopFree c = true → ∀ env, semU fuel c env = semScalar c env := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ =>
      intro h env
      simp only [loopFree, Bool.and_eq_true] at h
      simp only [semU, semScalar, ih₁ h.1, ih₂ h.2]
  | RBlock body ih =>
      intro h env
      simp only [semU, semScalar, ih h]
  | RFor x N body ih =>
      intro h env
      simp only [semU, semScalar, ih h]
  | RWhileNz name body _ => intro h; simp [loopFree] at h
  | RIfNz name thenBr elseBr _ _ =>
      intro h env
      have hne : elseBr ≠ .RSkip := by
        rintro rfl; simp [loopFree] at h
      exact semU_leaf fuel env (isSeqLike_rIfNz_of_ne name thenBr elseBr hne)
  | _ => intro _ env; exact semU_leaf fuel env rfl

/-! ## Structural rules at the unified waist -/

variable {AState : Type} (SR : SEnvScalar → AState → Prop)

theorem corresU_weaken {fuel : Nat} {P P' : AState → Prop} {fa : AState → AState}
    {c : LowCT} (h : CorresU fuel SR P fa c) (himp : ∀ a, P' a → P a) :
    CorresU fuel SR P' fa c := by
  intro env a hSR hP'; exact h env a hSR (himp a hP')

theorem corresU_block {fuel : Nat} {P : AState → Prop} {fa : AState → AState}
    {body : LowCT} (h : CorresU fuel SR P fa body) : CorresU fuel SR P fa (.RBlock body) := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := h env a hSR hP
  exact ⟨env', hstep, hSR'⟩

/-- A node carrying the `unsupported` guard: the precondition never holds. -/
theorem corresU_unsupported (SRf : SEnvScalar → AField → Prop) (fuel : Nat) (c : LowCT)
    (ctor : String) : CorresU fuel SRf (guardsHold [Guard.unsupported ctor]) id c :=
  fun _ _ _ h => (h _ (List.mem_singleton.mpr rfl)).elim

/-- `RAssert` is the identity on the env under `semScalar`. -/
theorem corres_assert (label : String) : Corres SR (fun _ => True) id (.RAssert label) := by
  intro env a hSR _; exact ⟨env, rfl, hSR⟩

/-- The guarded conditional `RIfNz name thenBlk RSkip` at the unified waist: when the
    concrete guard `guardNz name` is the abstract `g`, the node abstracts to
    `if g a then fb a else a`, the body's precondition required only when the guard
    is true. -/
theorem corresU_cond {fuel : Nat} {P : AState → Prop} {fb : AState → AState}
    {name : String} {thenBlk : LowCT} (g : AState → Bool)
    (hg : ∀ env a, SR env a → guardNz name env = g a)
    (hbody : CorresU fuel SR P fb thenBlk) :
    CorresU fuel SR (fun a => g a = true → P a) (fun a => if g a then fb a else a)
      (.RIfNz name thenBlk .RSkip) := by
  intro env a hSR hP
  have hgu : guardNz name env = g a := hg env a hSR
  show ∃ env', semScalarCond (fun e => semU fuel thenBlk e) (guardNz name) env = some env' ∧
    SR env' (if g a = true then fb a else a)
  by_cases hga : g a = true
  · obtain ⟨env', hstep, hSR'⟩ := hbody env a hSR (hP hga)
    refine ⟨env', ?_, ?_⟩
    · simp only [semScalarCond, hgu, hga, cond_true, hstep]
    · simp only [hga, if_true]; exact hSR'
  · simp only [Bool.not_eq_true] at hga
    refine ⟨env, ?_, ?_⟩
    · simp only [semScalarCond, hgu, hga, cond_false]
    · simp only [hga, Bool.false_eq_true, if_false]; exact hSR

/-- The do-while `RWhileNz name body` at the unified waist, trip by trip: under the
    abstract halting condition and the body precondition at every trip entry, the
    run halts with the store related to the abstract do-while. -/
theorem corresU_whileNz_aux {fuel : Nat} {Q : AState → Prop} {fb : AState → AState}
    {name : String} {body : LowCT} (g : AState → Bool)
    (hg : ∀ env a, SR env a → guardNz name env = g a)
    (hbody : CorresU fuel SR Q fb body) :
    ∀ (k : Nat) (env : SEnvScalar) (a : AState), SR env a → ahalts g fb k a →
      atrips Q g fb k a →
      ∃ env', semScalarWhile (fun e => semU fuel body e) (guardNz name) k env = some env' ∧
        SR env' (awhile g fb k a) := by
  intro k
  induction k with
  | zero => intro env a _ hh _; exact hh.elim
  | succ k ih =>
      intro env a hSR hh ht
      obtain ⟨env₁, hstep, hSR₁⟩ := hbody env a hSR ht.1
      by_cases hga : g (fb a) = true
      · obtain ⟨env', hrun, hSR'⟩ := ih env₁ (fb a) hSR₁ (hh hga) (ht.2 hga)
        refine ⟨env', ?_, ?_⟩
        · simp only [semScalarWhile, hstep, hg env₁ (fb a) hSR₁, hga, if_true, hrun]
        · simp only [awhile, hga, if_true]; exact hSR'
      · simp only [Bool.not_eq_true] at hga
        refine ⟨env₁, ?_, ?_⟩
        · simp only [semScalarWhile, hstep, hg env₁ (fb a) hSR₁, hga, Bool.false_eq_true,
            if_false]
        · simp only [awhile, hga, Bool.false_eq_true, if_false]; exact hSR₁

/-- The do-while rule at the unified waist: `RWhileNz name body` abstracts to
    `awhile g fb fuel` under the halting guard and the body precondition at every
    trip entry. -/
theorem corresU_whileNz {fuel : Nat} {Q : AState → Prop} {fb : AState → AState}
    {name : String} {body : LowCT} (g : AState → Bool)
    (hg : ∀ env a, SR env a → guardNz name env = g a)
    (hbody : CorresU fuel SR Q fb body) :
    CorresU fuel SR (fun a => ahalts g fb fuel a ∧ atrips Q g fb fuel a)
      (awhile g fb fuel) (.RWhileNz name body) := by
  intro env a hSR hP
  rw [semU_rWhileNz]
  exact corresU_whileNz_aux SR g hg hbody fuel env a hSR hP.1 hP.2

/-- The counted-loop rule at the unified waist, with a trip-indexed precondition:
    `RFor x N body` abstracts to `forFold setA fb N` when the body precondition holds
    at the entry of every trip (counter set), where `setA n` is the abstract image of
    the counter set `x := n`. -/
theorem corresU_for_trips {fuel : Nat} {Q : AState → Prop} {fb : AState → AState}
    {x : String} {body : LowCT} (setA : Nat → AState → AState)
    (hset : ∀ env a n, SR env a →
      SR (env.upd x (t := .sword 64) (BitVec.ofNat 64 n)) (setA n a))
    (hbody : CorresU fuel SR Q fb body) :
    ∀ N : Nat, CorresU fuel SR (fun a => ∀ n, n < N → Q (setA n (forFold setA fb n a)))
      (forFold setA fb N) (.RFor x N body) := by
  intro N
  induction N with
  | zero => intro env a hSR _; exact ⟨env, rfl, hSR⟩
  | succ n ih =>
      intro env a hSR hP
      obtain ⟨envPre, hPre, hSRPre⟩ := ih env a hSR (fun k hk => hP k (by omega))
      obtain ⟨env', hstep, hSR'⟩ :=
        hbody _ _ (hset envPre _ n hSRPre) (hP n (Nat.lt_succ_self n))
      refine ⟨env', ?_, hSR'⟩
      have hPre' : semRForD (fun e => semU fuel body e) x n env = some envPre := hPre
      show semRForD (fun e => semU fuel body e) x (n + 1) env = some env'
      simp only [semRForD, hPre', hstep]

/-! ## Leaves over `SRwordNT` -/

/-- The counter set `x := n` preserves `SRwordNT` against `setLit x n`. -/
theorem srwordNT_upd_lit {env : SEnvScalar} {a : AField} (x : String) (n : Nat)
    (hSR : SRwordNT env a) :
    SRwordNT (env.upd x (t := .sword 64) (BitVec.ofNat 64 n)) (setLit x n a) := by
  obtain ⟨env', hstep, hSR'⟩ := corres_setScalar_NT x n env a hSR trivial
  have h : env.upd x (t := .sword 64) (BitVec.ofNat 64 n) = env' := Option.some.inj hstep
  rw [h]; exact hSR'

/-- Under `SRwordNT`, the concrete guard `guardNz name` on a non-temp name is the
    abstract `nzB name`. -/
theorem guardNz_srwordNT {env : SEnvScalar} {a : AField} {name : String}
    (hname : ¬ isTmpName name) (hSR : SRwordNT env a) :
    guardNz name env = nzB name a := by
  obtain ⟨w, hw, hwe⟩ := hSR name hname
  simp only [guardNz, envReadU64, hw, Option.getD_some, nzB]
  rw [← hwe]
  exact Bool.decide_congr (not_congr (wEnc_eq_zero_iff w)).symm

/-- The φ-merge conditional over the non-temp relation, on a non-temp guard name:
    `corres_if` with `SRwordNT` in place of `SRword`. -/
theorem corres_if_NT (name nv : String) (tv ev : Nat) (hname : ¬ isTmpName name) :
    Corres SRwordNT (fun _ => True) (phiSet name nv tv ev)
      (.RIfNz name (.RScalarSet nv tv) (.RScalarSet nv ev)) := by
  intro env a hSR _
  obtain ⟨cw, hcw, hcwEnc⟩ := hSR name hname
  refine ⟨env.upd nv (t := .sword 64)
      (phiSelect (w := 64) cw (BitVec.ofNat 64 tv) (BitVec.ofNat 64 ev)), ?_, ?_⟩
  · simp only [semScalar, hcw, asSingleScalarSet, if_true]
  · intro s hs
    by_cases hsv : s = nv
    · subst hsv
      refine ⟨phiSelect (w := 64) cw (BitVec.ofNat 64 tv) (BitVec.ofNat 64 ev),
        by simp [SEnvScalar.upd], ?_⟩
      show wEnc _ = if s = s then (if a name = 0 then _ else _) else a s
      rw [if_pos rfl]
      by_cases hz : cw = 0#64
      · have haz : a name = 0 := hcwEnc ▸ (wEnc_eq_zero_iff cw).mpr hz
        simp only [phiSelect, if_pos hz, if_pos haz, wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]
      · have haz : ¬ a name = 0 := fun h => hz ((wEnc_eq_zero_iff cw).mp (hcwEnc ▸ h))
        simp only [phiSelect, if_neg hz, if_neg haz, wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]
    · obtain ⟨w, hw, hwn⟩ := hSR s hs
      exact ⟨w, by simp [SEnvScalar.upd, hsv, hw], by simp [phiSet, hsv, hwn]⟩

/-- The `u64` word read at a non-temp name is the canonical residue of the abstract
    value: `BitVec.ofNat 64 (a s).val` is the stored word. -/
theorem envReader_eq_liftEnv {env : SEnvScalar} {a : AField} (hSR : SRwordNT env a)
    (s : String) (hs : ¬ isTmpName s) :
    envReader env s = SExpr.liftEnv (natStore a) s := by
  obtain ⟨w, hw, hwe⟩ := hSR s hs
  simp only [envReader, hw, SExpr.liftEnv, natStore]
  rw [← hwe, wEnc, ZMod.val_natCast, Nat.mod_eq_of_lt w.isLt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt w.isLt).symm

/-- The range leaf: a source-clean `RScalarSetExpr x e` abstracts to the Nat-model
    value `natEval e` under the range guard `SExpr.inRange` on the current store. -/
theorem corres_setExprRange (x : String) (e : SExpr) (he : srcClean e) :
    Corres SRwordNT (fun a => e.inRange (natStore a))
      (fun a => setVal x (natEval e a) a) (.RScalarSetExpr x e) := by
  intro env a hSR hir
  set rs : RustState := ⟨fun _ => none, fun y => (envReader env y).toNat⟩ with hrs
  have hEB : EnvBoundOn rs env (fun _ => True) := by
    intro y _ hnt
    obtain ⟨w, hw, _⟩ := hSR y hnt
    have hr : envReader env y = w := by simp only [envReader, hw]
    have hround : BitVec.ofNat 64 w.toNat = w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt w.isLt
    show env y = some ⟨.sword 64, BitVec.ofNat 64 ((envReader env y).toNat)⟩
    rw [hr, hround]; exact hw
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ :=
    semLowerSExpr_ok' rs (fun _ => True) e env 0 hEB (varsBoundIn_true e) he
  have hval : wEnc (SExpr.evalBV (envReader env) e) = natEval e a := by
    rw [evalBV_congr_on (fun _ => True) (envReader env) (SExpr.liftEnv (natStore a)) e
      (fun s _ hs => envReader_eq_liftEnv hSR s hs) (varsBoundIn_true e) he]
    simp only [wEnc, natEval]
    rw [SExpr.toNat_evalBV_of_inRange (natStore a) e hir]
  refine ⟨env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e), ?_, ?_⟩
  · simp only [semScalar, hsem]
  · intro y hnt
    by_cases hyx : y = x
    · refine ⟨SExpr.evalBV (envReader env) e, ?_, ?_⟩
      · simp only [SEnvScalar.upd, if_pos hyx]
      · show wEnc (SExpr.evalBV (envReader env) e) = if y = x then natEval e a else a y
        rw [if_pos hyx]; exact hval
    · obtain ⟨w, hw, hwe⟩ := hSR y hnt
      refine ⟨w, ?_, ?_⟩
      · simp only [SEnvScalar.upd, if_neg hyx]
        rw [hotb y (Or.inl hnt)]; exact hw
      · show wEnc w = if y = x then natEval e a else a y
        rw [if_neg hyx]; exact hwe

/-! ## The total abstraction -/

/-- The unsupported-constructor abstraction: the identity under a guard that never
    holds. -/
def unsupportedAbs (ctor : String) : List Guard × (AField → AField) :=
  ([Guard.unsupported ctor], id)

/-- The abstraction of an `RScalarSetExpr` terminal: the `ZMod 2^64` evaluator on the
    arithmetic fragment with no guard, the Nat model under the range guard on the rest
    of the source-clean fragment, unsupported otherwise. -/
def ascendExpr (x : String) (e : SExpr) : List Guard × (AField → AField) :=
  if isArithCleanB e then ([], fun a => setVal x (evalZMod a e) a)
  else if srcCleanB e then ([Guard.range x e], fun a => setVal x (natEval e a) a)
  else unsupportedAbs "RScalarSetExpr"

/-- The abstraction of a conditional: the guarded `RIfNz name thenBlk RSkip` from the
    abstraction `rec` of its then-branch; the φ-merge on two literal sets of one name;
    unsupported otherwise. A temp guard name is unsupported, `SRwordNT` binding no
    temp. -/
def ascendIf (name : String) (thenBr elseBr : LowCT) (rec : List Guard × (AField → AField)) :
    List Guard × (AField → AField) :=
  if isSkipB elseBr then
    if notTmpB name then
      (rec.1.map (Guard.whenNz name), fun a => if nzB name a then rec.2 a else a)
    else unsupportedAbs "RIfNz"
  else
    match asSingleScalarSet thenBr, asSingleScalarSet elseBr with
    | some ts, some es =>
        if ts.name = es.name ∧ notTmpB name = true then ([], phiSet name ts.name ts.val es.val)
        else unsupportedAbs "RIfNz"
    | _, _ => unsupportedAbs "RIfNz"

/-- The total abstraction: every `LowCT` command to a word transformer over `AField`
    and the guards under which it is sound at the unified waist `semU fuel`. -/
def ascendG (fuel : Nat) : LowCT → List Guard × (AField → AField)
  | .RSkip => ([], id)
  | .RBlock body => ascendG fuel body
  | .RSeq c₁ c₂ =>
      ((ascendG fuel c₁).1 ++ (ascendG fuel c₂).1.map (Guard.after (ascendG fuel c₁).2),
        fun a => (ascendG fuel c₂).2 ((ascendG fuel c₁).2 a))
  | .RScalarSet x n => ([], setLit x n)
  | .RScalarSetExpr x e => ascendExpr x e
  | .RAssert label => ([Guard.assert label], id)
  | .RLetU64Zero x body =>
      if loopFree body then
        ((ascendG fuel body).1.map (Guard.after (setLit x 0)),
          fun a => (ascendG fuel body).2 (setLit x 0 a))
      else unsupportedAbs "RLetU64Zero"
  | .RIfNz name thenBr elseBr => ascendIf name thenBr elseBr (ascendG fuel thenBr)
  | .RWhileNz name body =>
      if notTmpB name then
        (Guard.loopHalts name fuel (ascendG fuel body).2 ::
            (ascendG fuel body).1.map (Guard.loopBody name fuel (ascendG fuel body).2),
          awhile (nzB name) (ascendG fuel body).2 fuel)
      else unsupportedAbs "RWhileNz"
  | .RFor x N body =>
      ((ascendG fuel body).1.map (Guard.everyTrip x N (ascendG fuel body).2),
        forFold (setLit x) (ascendG fuel body).2 N)
  | .RLetZero _ _ _ => unsupportedAbs "RLetZero"
  | .RCall _ _ _ => unsupportedAbs "RCall"
  | .RCallSwap _ _ _ _ => unsupportedAbs "RCallSwap"
  | .RCloneCall _ _ _ _ _ _ => unsupportedAbs "RCloneCall"
  | .RCallN _ _ _ => unsupportedAbs "RCallN"
  | .RSelect _ _ _ _ => unsupportedAbs "RSelect"
  | .RLimbStore _ _ _ => unsupportedAbs "RLimbStore"
  | .RLimbStoreExpr _ _ _ => unsupportedAbs "RLimbStoreExpr"
  | .RFnDef _ _ _ _ _ => unsupportedAbs "RFnDef"
  | .RFnCall _ _ _ => unsupportedAbs "RFnCall"
  | .RTupleLoad _ _ _ => unsupportedAbs "RTupleLoad"
  | .RArrStore _ _ _ => unsupportedAbs "RArrStore"
  | .RArrLoad _ _ _ => unsupportedAbs "RArrLoad"
  | .RArrStoreLit _ _ _ => unsupportedAbs "RArrStoreLit"
  | .RArrLoadLit _ _ _ => unsupportedAbs "RArrLoadLit"
  | .RCallDstThreaded _ _ _ => unsupportedAbs "RCallDstThreaded"
  | .RForRuntime _ _ _ => unsupportedAbs "RForRuntime"

/-! ## Soundness -/

theorem asSingleScalarSet_some {c : LowCT} {s : SingleScalarSet}
    (h : asSingleScalarSet c = some s) : c = .RScalarSet s.name s.val := by
  cases c <;> cases h
  rfl

/-- Soundness of the total abstraction at the unified waist: under its guards, the
    transformer `ascendG fuel c` is a `CorresU fuel SRwordNT` correspondent of `c`. -/
theorem ascendG_sound (fuel : Nat) :
    ∀ c : LowCT, CorresU fuel SRwordNT (guardsHold (ascendG fuel c).1) (ascendG fuel c).2 c := by
  intro c
  induction c
  case RSkip =>
    show CorresU fuel SRwordNT (guardsHold []) id .RSkip
    exact corresU_weaken SRwordNT (corresU_of_corres SRwordNT rfl (corres_skip SRwordNT))
      (fun _ _ => trivial)
  case RBlock body ih =>
    show CorresU fuel SRwordNT (guardsHold (ascendG fuel body).1) (ascendG fuel body).2 (.RBlock body)
    exact corresU_block SRwordNT ih
  case RSeq c₁ c₂ ih₁ ih₂ =>
    show CorresU fuel SRwordNT
      (guardsHold ((ascendG fuel c₁).1 ++ (ascendG fuel c₂).1.map (Guard.after (ascendG fuel c₁).2)))
      (fun a => (ascendG fuel c₂).2 ((ascendG fuel c₁).2 a)) (.RSeq c₁ c₂)
    refine corresU_seq SRwordNT
      (corresU_weaken SRwordNT ih₁ (fun a h => (guardsHold_append.mp h).1)) ih₂ (fun a h => ?_)
    exact guardsHold_map_after.mp (guardsHold_append.mp h).2
  case RScalarSet x n =>
    show CorresU fuel SRwordNT (guardsHold []) (setLit x n) (.RScalarSet x n)
    exact corresU_weaken SRwordNT (corresU_of_corres SRwordNT rfl (corres_setScalar_NT x n))
      (fun _ _ => trivial)
  case RScalarSetExpr x e =>
    show CorresU fuel SRwordNT (guardsHold (ascendExpr x e).1) (ascendExpr x e).2 (.RScalarSetExpr x e)
    unfold ascendExpr
    rcases h1 : isArithCleanB e
    · rcases h2 : srcCleanB e
      · simp only [Bool.false_eq_true, if_false]
        exact corresU_unsupported _ _ _ _
      · simp only [if_true, Bool.false_eq_true, if_false]
        exact corresU_weaken SRwordNT
          (corresU_of_corres SRwordNT rfl (corres_setExprRange x e (srcCleanB_sound e h2)))
          (fun a h => h _ (List.mem_singleton.mpr rfl))
    · simp only [if_true]
      exact corresU_weaken SRwordNT
        (corresU_of_corres SRwordNT rfl (corres_setExpr x e (isArithCleanB_sound e h1)))
        (fun _ _ => trivial)
  case RAssert label =>
    show CorresU fuel SRwordNT (guardsHold [Guard.assert label]) id (.RAssert label)
    exact corresU_weaken SRwordNT (corresU_of_corres SRwordNT rfl (corres_assert SRwordNT label))
      (fun _ _ => trivial)
  case RLetU64Zero x body ih =>
    simp only [ascendG]
    rcases hlf : loopFree body
    · simp only [Bool.false_eq_true, if_false]
      exact corresU_unsupported _ _ _ _
    · simp only [if_true]
      intro env a hSR hP
      obtain ⟨env', hstep, hSRf⟩ :=
        ih _ _ (srwordNT_upd_lit x 0 hSR) (guardsHold_map_after.mp hP)
      refine ⟨env', ?_, hSRf⟩
      show semScalar body (env.upd x (t := .sword 64) (0 : BitVec 64)) = some env'
      rw [← semU_eq_semScalar_of_loopFree fuel body hlf]
      exact hstep
  case RIfNz name thenBr elseBr ihT _ =>
    simp only [ascendG]
    unfold ascendIf
    rcases hsk : isSkipB elseBr
    · simp only [Bool.false_eq_true, if_false]
      have hne : elseBr ≠ .RSkip := fun h => by
        rw [h] at hsk; exact Bool.false_ne_true hsk.symm
      rcases ht : asSingleScalarSet thenBr with _ | ⟨nv, tv⟩
      · exact corresU_unsupported _ _ _ _
      · rcases he : asSingleScalarSet elseBr with _ | ⟨nv', ev⟩
        · exact corresU_unsupported _ _ _ _
        · dsimp only
          by_cases hc : nv = nv' ∧ notTmpB name = true
          · rw [if_pos hc]
            obtain ⟨hnv, hnt⟩ := hc
            subst hnv
            obtain rfl := asSingleScalarSet_some ht
            obtain rfl := asSingleScalarSet_some he
            exact corresU_weaken SRwordNT
              (corresU_of_corres SRwordNT (isSeqLike_rIfNz_of_ne _ _ _ hne)
                (corres_if_NT name nv tv ev (notTmpB_sound name hnt)))
              (fun _ _ => trivial)
          · rw [if_neg hc]
            exact corresU_unsupported _ _ _ _
    · obtain rfl := (isSkipB_iff elseBr).mp hsk
      simp only [if_true]
      rcases hnt : notTmpB name
      · simp only [Bool.false_eq_true, if_false]
        exact corresU_unsupported _ _ _ _
      · simp only [if_true]
        exact corresU_weaken SRwordNT
          (corresU_cond SRwordNT (nzB name)
            (fun env a hSR => guardNz_srwordNT (notTmpB_sound name hnt) hSR) ihT)
          (fun a h => guardsHold_map_whenNz.mp h)
  case RWhileNz name body ih =>
    simp only [ascendG]
    rcases hnt : notTmpB name
    · simp only [Bool.false_eq_true, if_false]
      exact corresU_unsupported _ _ _ _
    · simp only [if_true]
      refine corresU_weaken SRwordNT
        (corresU_whileNz SRwordNT (nzB name)
          (fun env a hSR => guardNz_srwordNT (notTmpB_sound name hnt) hSR) ih)
        (fun a h => ?_)
      refine ⟨h _ (List.mem_cons.mpr (Or.inl rfl)), guardsHold_map_loopBody.mp ?_⟩
      exact fun g hg => h g (List.mem_cons.mpr (Or.inr hg))
  case RFor x N body ih =>
    simp only [ascendG]
    exact corresU_weaken SRwordNT
      (corresU_for_trips SRwordNT (setLit x) (fun env a n hSR => srwordNT_upd_lit x n hSR) ih N)
      (fun a h => guardsHold_map_everyTrip.mp h)
  all_goals exact corresU_unsupported _ _ _ _

/-- On a loop-free command the unified waist is `semScalar`, so the abstraction is a
    `Corres` correspondent. -/
theorem ascendG_sound_scalar (fuel : Nat) (c : LowCT) (hlf : loopFree c = true) :
    Corres SRwordNT (guardsHold (ascendG fuel c).1) (ascendG fuel c).2 c := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := ascendG_sound fuel c env a hSR hP
  refine ⟨env', ?_, hSR'⟩
  rw [← semU_eq_semScalar_of_loopFree fuel c hlf]
  exact hstep

/-! ## The decidable straight-line fragments are guard-free instances -/

/-- On the literal fragment `IsAscendable`, `ascendG` emits no guard and its
    transformer is `asemW`. -/
theorem ascendG_isAscendable (fuel : Nat) {c : LowCT} (h : IsAscendable c) :
    (ascendG fuel c).1 = [] ∧ (ascendG fuel c).2 = asemW c := by
  induction h with
  | rSkip => exact ⟨rfl, rfl⟩
  | rBlock _ ih => exact ih
  | rSeq _ _ ih₁ ih₂ =>
      refine ⟨?_, ?_⟩
      · show (_ ++ List.map _ _) = []
        rw [ih₁.1, ih₂.1]; rfl
      · funext a
        show (ascendG fuel _).2 ((ascendG fuel _).2 a) = _
        rw [ih₁.2, ih₂.2]; rfl
  | rScalarSet name n => exact ⟨rfl, rfl⟩

/-- The literal fragment is loop-free. -/
theorem loopFree_of_isAscendable {c : LowCT} (h : IsAscendable c) : loopFree c = true := by
  induction h with
  | rSkip => rfl
  | rBlock _ ih => exact ih
  | rSeq _ _ ih₁ ih₂ => simp only [loopFree, ih₁, ih₂, Bool.and_self]
  | rScalarSet name n => rfl

/-- The `ascend` demos as instances of `ascendG_sound`: on the literal fragment the
    guard-free abstraction is `asemW c`, over the non-temp relation. -/
theorem ascend_sound_via_ascendG {c : LowCT} (h : IsAscendable c) :
    Corres SRwordNT (fun _ => True) (asemW c) c := by
  have hs := ascendG_sound_scalar 0 c (loopFree_of_isAscendable h)
  rw [(ascendG_isAscendable 0 h).1, (ascendG_isAscendable 0 h).2] at hs
  exact corres_weaken SRwordNT hs (fun a _ => guardsHold_nil a)

/-- On the decidable arithmetic-expression fragment `isAscendableExprB`, `ascendG`
    emits no guard and its transformer is `asemWExpr`. -/
theorem ascendG_isAscendableExprB (fuel : Nat) :
    ∀ c : LowCT, isAscendableExprB c = true →
      (ascendG fuel c).1 = [] ∧ (ascendG fuel c).2 = asemWExpr c := by
  intro c
  induction c
  case RSkip => intro _; exact ⟨rfl, rfl⟩
  case RBlock body ih => intro h; exact ih h
  case RSeq c₁ c₂ ih₁ ih₂ =>
    intro h
    simp only [isAscendableExprB, Bool.and_eq_true] at h
    refine ⟨?_, ?_⟩
    · show (_ ++ List.map _ _) = []
      rw [(ih₁ h.1).1, (ih₂ h.2).1]; rfl
    · funext a
      show (ascendG fuel c₂).2 ((ascendG fuel c₁).2 a) = _
      rw [(ih₁ h.1).2, (ih₂ h.2).2]; rfl
  case RScalarSet x n => intro _; exact ⟨rfl, rfl⟩
  case RScalarSetExpr x e =>
    intro h
    have h' : isArithCleanB e = true := h
    show (ascendExpr x e).1 = [] ∧ (ascendExpr x e).2 = _
    unfold ascendExpr
    rw [if_pos h']
    exact ⟨rfl, rfl⟩
  all_goals intro h; simp [isAscendableExprB] at h

/-- The decidable arithmetic-expression fragment is loop-free. -/
theorem loopFree_of_isAscendableExprB : ∀ c : LowCT, isAscendableExprB c = true → loopFree c = true := by
  intro c
  induction c
  case RSkip => intro _; rfl
  case RBlock body ih => intro h; exact ih h
  case RSeq c₁ c₂ ih₁ ih₂ =>
    intro h
    simp only [isAscendableExprB, Bool.and_eq_true] at h
    simp only [loopFree, ih₁ h.1, ih₂ h.2, Bool.and_self]
  case RScalarSet x n => intro _; rfl
  case RScalarSetExpr x e => intro _; rfl
  all_goals intro h; simp [isAscendableExprB] at h

/-- The `ascend_expr!` demos as instances of `ascendG_sound`: on the decidable
    arithmetic-expression fragment the guard-free abstraction is `asemWExpr c`. -/
theorem ascend_expr_sound_via_ascendG {c : LowCT} (h : isAscendableExprB c = true) :
    Corres SRwordNT (fun _ => True) (asemWExpr c) c := by
  have hs := ascendG_sound_scalar 0 c (loopFree_of_isAscendableExprB c h)
  rw [(ascendG_isAscendableExprB 0 c h).1, (ascendG_isAscendableExprB 0 c h).2] at hs
  exact corres_weaken SRwordNT hs (fun a _ => guardsHold_nil a)

/-! ## Two kernels closed through `ascendG_sound` alone

`avgK` assigns `r := (a + b) >>> 1`, an expression outside `IsArithClean` (the
shift), so its abstraction is the Nat model under a `range` guard: `a + b < 2 ^ 64`
and the shift amount below `64`, on the store after `b := 6`. On the concrete store
`avgStore` the guard is decided, and the abstract value at `r` is `53`.

`sumK` is the counted loop `for i in 0..4 { acc := acc + i }`; its body is
arithmetic, so the loop abstraction carries no guard, and the abstract value at
`acc` from `0` is `6`. -/

/-- `b := 6; r := (a + b) >>> 1`. -/
def avgK : LowCT :=
  .RSeq (.RScalarSet "b" 6)
    (.RScalarSetExpr "r" (.SShr (.SAdd (.SVar "a") (.SVar "b")) (.SLit 1)))

/-- The store with `a = 100` and every other name `0`. -/
def avgStore : AField := fun s => if s = "a" then 100 else 0

theorem avgK_guards :
    (ascendG 0 avgK).1 =
      [Guard.after (setLit "b" 6)
        (Guard.range "r" (.SShr (.SAdd (.SVar "a") (.SVar "b")) (.SLit 1)))] := rfl

theorem avgK_guards_hold : guardsHold (ascendG 0 avgK).1 avgStore := by decide

theorem avgK_corres : Corres SRwordNT (fun a => a = avgStore) (ascendG 0 avgK).2 avgK :=
  corres_weaken SRwordNT (ascendG_sound_scalar 0 avgK rfl)
    (fun _ ha => ha ▸ avgK_guards_hold)

theorem avgK_value : (ascendG 0 avgK).2 avgStore "r" = 53 := by decide

/-- `for i in 0..4 { acc := acc + i }`. -/
def sumK : LowCT :=
  .RFor "i" 4 (.RScalarSetExpr "acc" (.SAdd (.SVar "acc") (.SVar "i")))

/-- The all-zero store. -/
def zeroStore : AField := fun _ => 0

theorem sumK_guards_hold : guardsHold (ascendG 0 sumK).1 zeroStore := by decide

theorem sumK_corres : Corres SRwordNT (fun a => a = zeroStore) (ascendG 0 sumK).2 sumK :=
  corres_weaken SRwordNT (ascendG_sound_scalar 0 sumK rfl)
    (fun _ ha => ha ▸ sumK_guards_hold)

theorem sumK_value : (ascendG 0 sumK).2 zeroStore "acc" = 6 := by decide

end CatCrypt.Crypto.SecureCompilation.Ascent
