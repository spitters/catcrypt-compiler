/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AscendDecide
public import CatCrypt.Crypto.SecureCompilation.Ascent.ArrStoreLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.Phases
public import CatCrypt.Crypto.SecureCompilation.Ascent.WhileTop

/-!
# Total abstraction with guards

`ascendGL L fuel c` abstracts every `LowCT` command `c` to a pure word transformer over
`AField = String → ZMod 2^64` together with a list of `Guard`s: the side conditions
the abstraction does not discharge on its own. The abstraction is total — every
constructor produces a transformer and a guard list — and `ascendGL_sound` states
that under the guards the transformer is a `CorresU` correspondent of `c` at the
unified waist `semU fuel`, over the layout relation `SRwordL L`.

## Array layouts

An array layout `L : ArrLayout` lists the `.memref` slots of the concrete store with
their lengths. `SRwordL L` relates a store to an abstract word store: every non-temp
name the layout does not reserve holds a `u64` word encoded at that name, and element
`j` of a layout array `arr` is encoded at the name `elemKey arr j`. A layout reserves
its array names and, when it is not empty, every name beginning with the character
`\x01`, which every element name does (`arrKeyB`). Over the empty layout the relation
is `SRwordNT` (`srwordL_nil_iff`), and `ascendG` is `ascendGL []`: `ascendG_sound`
is the instance of `ascendGL_sound` at the empty layout.

## Guards

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

The static side conditions of a node — a written or read word name not reserved by
the layout, an array name with its length in the layout, the tower type of an array
slot — are decided by the abstraction itself, which returns the `unsupported` guard
when one fails.

## Value leaves

`RScalarSet` and arithmetic `RScalarSetExpr` terminals go through `corresL_setScalar`
and `corresL_setExprVal` with no guard; the counted loop goes through the trip-indexed
rule `corresU_for_trips`, the guarded conditional through `corresU_cond`, the φ-merge
conditional through `corresL_if`, and the while loop through `corresU_whileNz`. The
dynamic-index array read and write `RArrLoad` / `RArrStore` go through
`corresL_arrLoad` / `corresL_arrStore`, which read and write the element at the index
modulo the array length, as `memGetDyn` / `memSetDyn` do; the literal limb store
`RLimbStore` goes through `corresL_limbStore`, and the literal-index read and write
`RArrLoadLit` / `RArrStoreLit` go through `corresL_arrLoadLit` / `corresL_arrStoreLit`
on a `TArr _ .TU64` word array at an index below the array length. The constant-time word select `RSelect` goes
through `corresL_select`, which sets the destination to the first source when the
selector is zero and to the second otherwise, as `selectWord` does. These six nodes
carry no store guard.

On the decidable straight-line fragments (`isAscendableB`, `isAscendableExprB`)
`ascendG` emits no guard and its transformer is `asemW` / `asemWExpr`
(`ascendG_isAscendable`, `ascendG_isAscendableExprB`), so the existing `ascend!` /
`ascend_expr!` demos are instances of `ascendG_sound`.

## Main definitions

* `Guard`, `Guard.holds`, `guardsHold` — the guard language and its meaning on a store
* `ArrLayout`, `elemKey`, `arrKeyB`, `SRwordL` — array layouts and the layout relation
* `ascendGL`, `ascendG` — the total abstraction, and its instance at the empty layout
* `ascendGL_sound`, `ascendG_sound` — soundness at the unified waist
* `ascendGL_sound_scalar`, `ascendG_sound_scalar` — the same over `Corres` on
  loop-free commands
* `arrSelK` — a kernel with two array reads, a mask select and an array write, closed
  through `ascendGL_sound_scalar`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)

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

/-- The constant-time select on the abstract store:
    `dst := if a sel = 0 then a s0 else a s1`. -/
def selSet (sel dst s0 s1 : String) (a : AField) : AField :=
  setVal dst (if a sel = 0 then a s0 else a s1) a

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

section Structural

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

end Structural

/-! ## Array layouts and the layout relation -/

/-- An array layout: the names of the `.memref` slots of the concrete store, with their
    lengths. -/
abbrev ArrLayout := List (String × Nat)

/-- The abstract-store name of element `j` of the array `arr`: `j + 1` copies of the
    character `\x01`, the character `\x00`, then the array name. -/
def elemKey (arr : String) (j : Nat) : String :=
  String.ofList (List.replicate (j + 1) '\x01' ++ '\x00' :: arr.toList)

theorem replicate_sep_inj {c d : Char} (hcd : c ≠ d) :
    ∀ (j k : Nat) (l l' : List Char),
      List.replicate j c ++ d :: l = List.replicate k c ++ d :: l' → j = k ∧ l = l'
  | 0, 0, l, l', h => by simpa using h
  | 0, k + 1, l, l', h => by simp [List.replicate_succ] at h; exact absurd h.1.symm hcd
  | j + 1, 0, l, l', h => by simp [List.replicate_succ] at h; exact absurd h.1 hcd
  | j + 1, k + 1, l, l', h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hj, hl⟩ := replicate_sep_inj hcd j k l l' h
      exact ⟨by omega, hl⟩

/-- Element names are injective in the array name and the index. -/
theorem elemKey_inj {a b : String} {j k : Nat} (h : elemKey a j = elemKey b k) :
    a = b ∧ j = k := by
  have h' := congrArg String.toList h
  simp only [elemKey, String.toList_ofList] at h'
  obtain ⟨hj, hl⟩ := replicate_sep_inj (by decide) _ _ _ _ h'
  exact ⟨String.toList_inj.mp hl, by omega⟩

theorem elemKey_head (arr : String) (j : Nat) : (elemKey arr j).toList.head? = some '\x01' := by
  simp [elemKey, List.replicate_succ]

/-- The name is reserved by the layout: an array name, or, when the layout is not empty,
    a name beginning with `\x01`, as every element name does. -/
def arrKeyB (L : ArrLayout) (x : String) : Bool :=
  (L.map Prod.fst).contains x || (!L.isEmpty && x.toList.head? == some '\x01')

theorem arrKeyB_name {L : ArrLayout} {p : String × Nat} (hp : p ∈ L) : arrKeyB L p.1 = true := by
  simp only [arrKeyB, Bool.or_eq_true, List.contains_iff_mem, List.mem_map]
  exact Or.inl ⟨p, hp, rfl⟩

theorem arrKeyB_elemKey {L : ArrLayout} {p : String × Nat} (hp : p ∈ L) (s : String) (j : Nat) :
    arrKeyB L (elemKey s j) = true := by
  have hne : L.isEmpty = false := by
    cases L with
    | nil => exact absurd hp List.not_mem_nil
    | cons _ _ => rfl
  simp [arrKeyB, hne, elemKey_head]

theorem ne_of_arrKeyB {L : ArrLayout} {x y : String} (hx : arrKeyB L x = false)
    (hy : arrKeyB L y = true) : x ≠ y := by
  rintro rfl; rw [hx] at hy; exact Bool.false_ne_true hy

/-- The length the layout gives a name, reading the first entry for it. -/
def layoutSize : ArrLayout → String → Option Nat
  | [], _ => none
  | p :: L, s => if p.1 = s then some p.2 else layoutSize L s

theorem layoutSize_mem : ∀ {L : ArrLayout} {s : String} {n : Nat},
    layoutSize L s = some n → (s, n) ∈ L
  | [], _, _, h => by simp [layoutSize] at h
  | p :: L, s, n, h => by
      simp only [layoutSize] at h
      split at h
      · rename_i hp
        obtain rfl := Option.some.inj h
        exact List.mem_cons.mpr (Or.inl (by rw [← hp]))
      · exact List.mem_cons_of_mem _ (layoutSize_mem h)

/-- The state relation over a layout: every non-temp name the layout does not reserve
    holds a `.sword 64` whose `wEnc` encoding is the abstract value, and every layout
    entry `(arr, n)` is a non-temp name holding a `.memref n` whose element `j` is
    encoded at `elemKey arr j`. -/
def SRwordL (L : ArrLayout) (env : SEnvScalar) (a : AField) : Prop :=
  (∀ x, ¬ isTmpName x → arrKeyB L x = false →
      ∃ w : BitVec 64, env x = some ⟨.sword 64, w⟩ ∧ wEnc w = a x) ∧
  (∀ p ∈ L, ¬ isTmpName p.1 ∧ ∃ av : Fin p.2 → BitVec 64,
      env p.1 = some ⟨.memref p.2, av⟩ ∧ ∀ j : Fin p.2, wEnc (av j) = a (elemKey p.1 j))

/-- Over the empty layout the relation is `SRwordNT`. -/
theorem srwordL_nil_iff {env : SEnvScalar} {a : AField} : SRwordL [] env a ↔ SRwordNT env a :=
  ⟨fun h x hx => h.1 x hx rfl,
    fun h => ⟨fun x hx _ => h x hx, fun _ hp => absurd hp List.not_mem_nil⟩⟩

/-- A word write at an unreserved name that leaves every other non-temp name unchanged
    preserves the relation against `setVal`. -/
theorem srwordL_set {L : ArrLayout} {env env' : SEnvScalar} {a : AField} (x : String)
    (v : BitVec 64) (z : ZMod (2 ^ 64)) (hx : arrKeyB L x = false) (hz : wEnc v = z)
    (hSR : SRwordL L env a) (hxv : env' x = some ⟨.sword 64, v⟩)
    (hframe : ∀ y, ¬ isTmpName y → y ≠ x → env' y = env y) :
    SRwordL L env' (setVal x z a) := by
  refine ⟨fun y hy hyk => ?_, fun p hp => ?_⟩
  · by_cases hyx : y = x
    · subst hyx; exact ⟨v, hxv, by simp [setVal, hz]⟩
    · obtain ⟨w, hw, hwe⟩ := hSR.1 y hy hyk
      exact ⟨w, by rw [hframe y hy hyx, hw], by simp [setVal, hyx, hwe]⟩
  · obtain ⟨hnt, av, hav, havE⟩ := hSR.2 p hp
    have hpx : p.1 ≠ x := (ne_of_arrKeyB hx (arrKeyB_name hp)).symm
    refine ⟨hnt, av, by rw [hframe _ hnt hpx, hav], fun j => ?_⟩
    have hkx : elemKey p.1 j ≠ x := (ne_of_arrKeyB hx (arrKeyB_elemKey hp _ _)).symm
    simp [setVal, hkx, havE j]

/-- A write of element `k < n` of the layout array `s` preserves the relation against
    `setVal` at `elemKey s k`. -/
theorem srwordL_arrWrite {L : ArrLayout} {env env' : SEnvScalar} {a : AField} (s : String)
    (n k : Nat) (av av' : Fin n → BitVec 64) (v : BitVec 64) (z : ZMod (2 ^ 64))
    (hz : wEnc v = z) (hSR : SRwordL L env a) (hmem : (s, n) ∈ L)
    (hs : env s = some ⟨.memref n, av⟩)
    (hav' : ∀ j : Fin n, av' j = if j.val = k then v else av j)
    (henv' : ∀ y, env' y = if y = s then some ⟨.memref n, av'⟩ else env y) :
    SRwordL L env' (setVal (elemKey s k) z a) := by
  refine ⟨fun y hy hyk => ?_, fun p hp => ?_⟩
  · have hys : y ≠ s := ne_of_arrKeyB hyk (arrKeyB_name hmem)
    have hyk' : y ≠ elemKey s k := ne_of_arrKeyB hyk (arrKeyB_elemKey hmem _ _)
    obtain ⟨w, hw, hwe⟩ := hSR.1 y hy hyk
    exact ⟨w, by rw [henv', if_neg hys, hw], by simp [setVal, hyk', hwe]⟩
  · obtain ⟨hnt, bv, hbv, hbvE⟩ := hSR.2 p hp
    refine ⟨hnt, ?_⟩
    obtain ⟨p1, p2⟩ := p
    simp only at hnt hbv hbvE ⊢
    by_cases hps : p1 = s
    · subst hps
      rw [hs] at hbv
      simp only [Option.some.injEq, Sigma.mk.inj_iff, CryptoSSA.CryptoTy.memref.injEq] at hbv
      obtain ⟨rfl, hb⟩ := hbv
      obtain rfl := eq_of_heq hb
      refine ⟨av', by rw [henv', if_pos rfl], fun j => ?_⟩
      rw [hav' j]
      by_cases hj : j.val = k
      · simp [hj, setVal, hz]
      · have hne : elemKey p1 j ≠ elemKey p1 k := fun h => hj (elemKey_inj h).2
        simp [hj, setVal, hne, hbvE j]
    · refine ⟨bv, by rw [henv', if_neg hps, hbv], fun j => ?_⟩
      have hne : elemKey p1 j ≠ elemKey s k := fun h => hps (elemKey_inj h).1
      simp [setVal, hne, hbvE j]

/-! ## Leaves over a layout -/

/-- The counter set `x := n` on an unreserved name preserves `SRwordL` against
    `setLit x n`. -/
theorem srwordL_upd_lit {L : ArrLayout} {env : SEnvScalar} {a : AField} (x : String) (n : Nat)
    (hx : arrKeyB L x = false) (hSR : SRwordL L env a) :
    SRwordL L (env.upd x (t := .sword 64) (BitVec.ofNat 64 n)) (setLit x n a) :=
  srwordL_set x (BitVec.ofNat 64 n) (n : ZMod (2 ^ 64)) hx
    (by simp [wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]) hSR
    (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])

/-- The literal leaf over a layout. -/
theorem corresL_setScalar (L : ArrLayout) (x : String) (n : Nat) (hx : arrKeyB L x = false) :
    Corres (SRwordL L) (fun _ => True) (setLit x n) (.RScalarSet x n) :=
  fun _ _ hSR _ => ⟨_, rfl, srwordL_upd_lit x n hx hSR⟩

/-- Under `SRwordL`, the concrete guard `guardNz name` on a non-temp unreserved name is
    the abstract `nzB name`. -/
theorem guardNz_srwordL {L : ArrLayout} {env : SEnvScalar} {a : AField} {name : String}
    (hname : ¬ isTmpName name) (hk : arrKeyB L name = false) (hSR : SRwordL L env a) :
    guardNz name env = nzB name a := by
  obtain ⟨w, hw, hwe⟩ := hSR.1 name hname hk
  simp only [guardNz, envReadU64, hw, Option.getD_some, nzB]
  rw [← hwe]
  exact Bool.decide_congr (not_congr (wEnc_eq_zero_iff w)).symm

/-- The word read at a non-temp unreserved name is the canonical residue of the abstract
    value. -/
theorem envReader_eq_liftEnvL {L : ArrLayout} {env : SEnvScalar} {a : AField}
    (hSR : SRwordL L env a) (s : String) (hs : ¬ isTmpName s) (hk : arrKeyB L s = false) :
    envReader env s = SExpr.liftEnv (natStore a) s := by
  obtain ⟨w, hw, hwe⟩ := hSR.1 s hs hk
  simp only [envReader, hw, SExpr.liftEnv, natStore]
  rw [← hwe, wEnc, ZMod.val_natCast, Nat.mod_eq_of_lt w.isLt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt w.isLt).symm

/-- A predicate holding everywhere bounds the variables of every expression. -/
theorem varsBoundIn_of_forall {B : String → Prop} (hB : ∀ y, B y) : ∀ e, varsBoundIn B e := by
  intro e
  induction e with
  | SVar x => exact hB x
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      exact ⟨iha, ihb⟩
  | _ => trivial

/-- The variables of the expression are unreserved by the layout. -/
def varsWordB (L : ArrLayout) : SExpr → Bool
  | .SVar x => !arrKeyB L x
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => varsWordB L a && varsWordB L b
  | _ => true

/-- `varsWordB`, true without inspecting the expression on the empty layout. -/
def exprWordB (L : ArrLayout) (e : SExpr) : Bool := L.isEmpty || varsWordB L e

theorem varsWordB_sound (L : ArrLayout) :
    ∀ e, varsWordB L e = true → varsBoundIn (fun y => arrKeyB L y = false) e := by
  intro e
  induction e with
  | SVar x => intro h; simpa [varsWordB, varsBoundIn] using h
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro h
      simp only [varsWordB, Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | _ => intro _; trivial

theorem exprWordB_sound {L : ArrLayout} {e : SExpr} (h : exprWordB L e = true) :
    varsBoundIn (fun y => arrKeyB L y = false) e := by
  cases L with
  | nil => exact varsBoundIn_of_forall (fun _ => rfl) e
  | cons p L => exact varsWordB_sound _ e (by simpa [exprWordB] using h)

/-- The expression leaf over a layout: a source-clean `RScalarSetExpr x e` whose
    variables and destination are unreserved assigns `val a`, for any `val` that is the
    encoding of the word evaluation of `e` at the canonical residues of `a` under `P`. -/
theorem corresL_setExprVal (L : ArrLayout) (x : String) (e : SExpr) (hx : arrKeyB L x = false)
    (hvb : varsBoundIn (fun y => arrKeyB L y = false) e) (he : srcClean e)
    (P : AField → Prop) (val : AField → ZMod (2 ^ 64))
    (hval : ∀ a, P a → wEnc (SExpr.evalBV (SExpr.liftEnv (natStore a)) e) = val a) :
    Corres (SRwordL L) P (fun a => setVal x (val a) a) (.RScalarSetExpr x e) := by
  intro env a hSR hP
  set rs : RustState := ⟨fun _ => none, fun y => (envReader env y).toNat⟩ with hrs
  have hEB : EnvBoundOn rs env (fun y => arrKeyB L y = false) := by
    intro y hy hnt
    obtain ⟨w, hw, _⟩ := hSR.1 y hnt hy
    have hr : envReader env y = w := by simp only [envReader, hw]
    have hround : BitVec.ofNat 64 w.toNat = w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt w.isLt
    show env y = some ⟨.sword 64, BitVec.ofNat 64 ((envReader env y).toNat)⟩
    rw [hr, hround]; exact hw
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ :=
    semLowerSExpr_ok' rs (fun y => arrKeyB L y = false) e env 0 hEB hvb he
  have hcongr : SExpr.evalBV (envReader env) e = SExpr.evalBV (SExpr.liftEnv (natStore a)) e :=
    evalBV_congr_on _ _ _ e (fun s hs hnt => envReader_eq_liftEnvL hSR s hnt hs) hvb he
  refine ⟨env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e), ?_, ?_⟩
  · simp only [semScalar, hsem]
  · refine srwordL_set x (SExpr.evalBV (envReader env) e) (val a) hx
      (by rw [hcongr]; exact hval a hP) hSR (by simp [SEnvScalar.upd]) (fun y hy hyx => ?_)
    simp only [SEnvScalar.upd, if_neg hyx]
    exact hotb y (Or.inl hy)

/-- The `ZMod 2^64` value of an arithmetic expression at the canonical residues. -/
theorem wEnc_evalBV_liftEnv_arith (a : AField) (e : SExpr) (he : IsArithClean e) :
    wEnc (SExpr.evalBV (SExpr.liftEnv (natStore a)) e) = evalZMod a e := by
  refine wEnc_evalBV_evalZMod _ a (fun y _ => ?_) e he
  simp only [wEnc, SExpr.liftEnv, natStore, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (ZMod.val_lt (a y)), ZMod.natCast_zmod_val]

/-- The Nat-model value of an in-range expression at the canonical residues. -/
theorem wEnc_evalBV_liftEnv_range (a : AField) (e : SExpr) (hir : e.inRange (natStore a)) :
    wEnc (SExpr.evalBV (SExpr.liftEnv (natStore a)) e) = natEval e a := by
  simp only [wEnc, natEval]
  rw [SExpr.toNat_evalBV_of_inRange (natStore a) e hir]

/-- The φ-merge conditional over a layout, on a non-temp guard name, with guard and
    destination unreserved. -/
theorem corresL_if (L : ArrLayout) (name nv : String) (tv ev : Nat) (hname : ¬ isTmpName name)
    (hk : arrKeyB L name = false) (hnv : arrKeyB L nv = false) :
    Corres (SRwordL L) (fun _ => True) (phiSet name nv tv ev)
      (.RIfNz name (.RScalarSet nv tv) (.RScalarSet nv ev)) := by
  intro env a hSR _
  obtain ⟨cw, hcw, hcwEnc⟩ := hSR.1 name hname hk
  refine ⟨env.upd nv (t := .sword 64)
      (phiSelect (w := 64) cw (BitVec.ofNat 64 tv) (BitVec.ofNat 64 ev)), ?_, ?_⟩
  · simp only [semScalar, hcw, asSingleScalarSet, if_true]
  · refine srwordL_set nv (phiSelect (w := 64) cw (BitVec.ofNat 64 tv) (BitVec.ofNat 64 ev))
      (if a name = 0 then (ev : ZMod (2 ^ 64)) else (tv : ZMod (2 ^ 64)))
      hnv ?_ hSR (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
    by_cases hz : cw = 0#64
    · have haz : a name = 0 := hcwEnc ▸ (wEnc_eq_zero_iff cw).mpr hz
      simp only [phiSelect, if_pos hz, if_pos haz, wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]
    · have haz : ¬ a name = 0 := fun h => hz ((wEnc_eq_zero_iff cw).mp (hcwEnc ▸ h))
      simp only [phiSelect, if_neg hz, if_neg haz, wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]

/-- The residue of the abstract value at a word name is the stored word's `toNat`. -/
theorem val_of_wEnc {w : BitVec 64} {z : ZMod (2 ^ 64)} (h : wEnc w = z) : z.val = w.toNat := by
  rw [← h, wEnc, ZMod.val_natCast, Nat.mod_eq_of_lt w.isLt]

/-- The dynamic-index array read over a layout: `RArrLoad dst src idxVar` with `src` a
    layout array of length `m + 1` and `dst` a `u64` word reads the element at
    `elemKey src.locVar (idx % (m + 1))`. -/
theorem corresL_arrLoad (L : ArrLayout) (dst src : Located) (idxVar : String) (m : Nat)
    (hdst : dst.locSrc = .TU64) (hsz : (src.locVar, m + 1) ∈ L)
    (hdk : arrKeyB L dst.locVar = false) (hit : ¬ isTmpName idxVar)
    (hik : arrKeyB L idxVar = false) :
    Corres (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (a (elemKey src.locVar ((a idxVar).val % (m + 1)))) a)
      (.RArrLoad dst src idxVar) := by
  intro env a hSR _
  obtain ⟨_, av, hav, havE⟩ := hSR.2 _ hsz
  have hav' : env src.locVar = some ⟨.memref (m + 1), av⟩ := hav
  obtain ⟨iv, hiv, hivE⟩ := hSR.1 idxVar hit hik
  refine ⟨env.upd dst.locVar (t := .sword 64) (memGetDyn av iv.toNat), ?_, ?_⟩
  · simp only [semScalar, Located.locDst, hdst, hav', hiv]
  · refine srwordL_set dst.locVar (memGetDyn av iv.toNat) _ hdk ?_ hSR
      (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
    rw [val_of_wEnc hivE]
    exact havE ⟨iv.toNat % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

/-- The dynamic-index array write over a layout: `RArrStore arr idxVar src` with `arr` a
    layout array of length `m + 1`, typed `.memref (m + 1)`, stores the word at `src` at
    `elemKey arr.locVar (idx % (m + 1))`. -/
theorem corresL_arrStore (L : ArrLayout) (arr src : Located) (idxVar : String) (m : Nat)
    (harr : encodeTy arr.locSrc = .memref (m + 1)) (hsz : (arr.locVar, m + 1) ∈ L)
    (hit : ¬ isTmpName idxVar) (hik : arrKeyB L idxVar = false)
    (hst : ¬ isTmpName src.locVar) (hsk : arrKeyB L src.locVar = false) :
    Corres (SRwordL L) (fun _ => True)
      (fun a => setVal (elemKey arr.locVar ((a idxVar).val % (m + 1))) (a src.locVar) a)
      (.RArrStore arr idxVar src) := by
  intro env a hSR _
  obtain ⟨_, av, hav, _⟩ := hSR.2 _ hsz
  have hav' : env arr.locVar = some ⟨.memref (m + 1), av⟩ := hav
  obtain ⟨iv, hiv, hivE⟩ := hSR.1 idxVar hit hik
  obtain ⟨sv, hsv, hsvE⟩ := hSR.1 src.locVar hst hsk
  refine ⟨env.upd arr.locVar (t := encodeTy arr.locSrc) (harr.symm ▸ memSetDyn av iv.toNat sv),
    ?_, ?_⟩
  · simp only [semScalar, Located.locDst, hav', hiv, hsv, harr, dif_pos]
  · show SRwordL L _ (setVal (elemKey arr.locVar ((a idxVar).val % (m + 1))) (a src.locVar) a)
    rw [val_of_wEnc hivE]
    refine srwordL_arrWrite arr.locVar (m + 1) (iv.toNat % (m + 1)) av
      (memSetDyn av iv.toNat sv) sv _ hsvE hSR hsz hav' (fun j => ?_) (fun y => ?_)
    · by_cases h : j.val = iv.toNat % (m + 1) <;> simp [memSetDyn, h, Fin.ext_iff]
    · by_cases hy : y = arr.locVar
      · simp only [SEnvScalar.upd, if_pos hy]
        exact congrArg some (sigma_memref harr _)
      · simp [SEnvScalar.upd, hy]

/-- The literal limb store over a layout: `RLimbStore loc idx v` with `loc` a layout
    array of length above `idx` stores `v` at `elemKey loc.locVar idx`. -/
theorem corresL_limbStore (L : ArrLayout) (loc : Located) (idx : Nat) (v : BitVec 64) (n : Nat)
    (hsz : (loc.locVar, n) ∈ L) (hidx : idx < n) :
    Corres (SRwordL L) (fun _ => True) (setVal (elemKey loc.locVar idx) (wEnc v))
      (.RLimbStore loc idx v) := by
  intro env a hSR _
  obtain ⟨_, av, hav, _⟩ := hSR.2 _ hsz
  have hav' : env loc.locVar = some ⟨.memref n, av⟩ := hav
  refine ⟨env.upd loc.locVar (t := .memref n) (fun j => if j = ⟨idx, hidx⟩ then v else av j),
    ?_, ?_⟩
  · simp only [semScalar, hav', dif_pos hidx]
  · exact srwordL_arrWrite loc.locVar n idx av _ v _ rfl hSR hsz hav'
      (fun j => by by_cases h : j.val = idx <;> simp [h, Fin.ext_iff]) (fun y => rfl)

/-- A literal index below the array length and below `2 ^ 64`, taken as a 64-bit word
    and reduced modulo the length, is the index itself. -/
theorem litIdx_mod {idx m : Nat} (hidx : idx < m + 1) (hlit : idx < 2 ^ 64) :
    (BitVec.ofNat 64 idx).toNat % (m + 1) = idx := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlit, Nat.mod_eq_of_lt hidx]

/-- Whether a tower type is a `u64` word array `TArr k .TU64`, the array type on which
    `semScalar` reads and writes a literal-index element as a 64-bit word. -/
def isU64ArrB : TowerType → Bool
  | .TArr _ .TU64 => true
  | _ => false

/-- `isU64ArrB` holds exactly on `TArr k .TU64`. -/
theorem isU64ArrB_sound {t : TowerType} (h : isU64ArrB t = true) :
    ∃ k, t = .TArr k .TU64 := by
  unfold isU64ArrB at h
  split at h
  · exact ⟨_, rfl⟩
  · exact absurd h (by simp)

/-- The literal-index array read over a layout: `RArrLoadLit dst src idx` with `src` a
    `u64` word array (`TArr k .TU64`) in the layout of length `m + 1` above `idx` and
    `dst` an unreserved `u64` word reads the element at `elemKey src.locVar idx`. -/
theorem corresL_arrLoadLit (L : ArrLayout) (dst src : Located) (idx k m : Nat)
    (hdst : dst.locSrc = .TU64) (hsrc : src.locSrc = .TArr k .TU64)
    (hsz : (src.locVar, m + 1) ∈ L) (hidx : idx < m + 1)
    (hlit : idx < 2 ^ 64) (hdk : arrKeyB L dst.locVar = false) :
    Corres (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (a (elemKey src.locVar idx)) a)
      (.RArrLoadLit dst src idx) := by
  intro env a hSR _
  obtain ⟨_, av, hav, havE⟩ := hSR.2 _ hsz
  have hav' : env src.locVar = some ⟨.memref (m + 1), av⟩ := hav
  refine ⟨env.upd dst.locVar (t := .sword 64) (memGetDyn av (BitVec.ofNat 64 idx).toNat),
    semScalar_rArrLoadLit_word dst src idx env k (m + 1) av hdst hsrc hav', ?_⟩
  refine srwordL_set dst.locVar (memGetDyn av (BitVec.ofNat 64 idx).toNat) _ hdk ?_ hSR
    (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
  have hk : (⟨(BitVec.ofNat 64 idx).toNat % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ :
      Fin (m + 1)) = ⟨idx, hidx⟩ := Fin.ext (litIdx_mod hidx hlit)
  show wEnc (av ⟨(BitVec.ofNat 64 idx).toNat % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩) = _
  rw [hk]
  exact havE ⟨idx, hidx⟩

/-- The literal-index array write over a layout: `RArrStoreLit arr idx src` with `arr` a
    `u64` word array (`TArr k .TU64`) in the layout of length `m + 1` above `idx`
    stores the word at the non-temp unreserved name `src` at `elemKey arr.locVar idx`. -/
theorem corresL_arrStoreLit (L : ArrLayout) (arr src : Located) (idx k m : Nat)
    (harr : arr.locSrc = .TArr k .TU64)
    (hsz : (arr.locVar, m + 1) ∈ L) (hidx : idx < m + 1) (hlit : idx < 2 ^ 64)
    (hst : ¬ isTmpName src.locVar) (hsk : arrKeyB L src.locVar = false) :
    Corres (SRwordL L) (fun _ => True)
      (fun a => setVal (elemKey arr.locVar idx) (a src.locVar) a)
      (.RArrStoreLit arr idx src) := by
  intro env a hSR _
  obtain ⟨_, av, hav, _⟩ := hSR.2 _ hsz
  have hav' : env arr.locVar = some ⟨.memref (m + 1), av⟩ := hav
  obtain ⟨sv, hsv, hsvE⟩ := hSR.1 src.locVar hst hsk
  refine ⟨env.upd arr.locVar (t := .memref (m + 1))
      (memSetDyn av (BitVec.ofNat 64 idx).toNat sv),
    semScalar_rArrStoreLit_word arr src idx env k (m + 1) av sv harr hav' hsv, ?_⟩
  refine srwordL_arrWrite arr.locVar (m + 1) idx av
    (memSetDyn av (BitVec.ofNat 64 idx).toNat sv) sv _ hsvE hSR hsz hav' (fun j => ?_)
    (fun y => rfl)
  have hk := litIdx_mod hidx hlit
  show (if j = ⟨(BitVec.ofNat 64 idx).toNat % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
    then sv else av j) = _
  by_cases h : j.val = idx
  · rw [if_pos (Fin.ext (h.trans hk.symm)), if_pos h]
  · rw [if_neg (fun hj => h ((congrArg Fin.val hj).trans hk)), if_neg h]

/-- The constant-time word select over a layout: `RSelect dst sel src0 src1` with `dst`
    a `u64` word and the selector and both sources non-temp unreserved word names sets
    `dst` to the word at `src0` when the selector is zero and to the word at `src1`
    otherwise. -/
theorem corresL_select (L : ArrLayout) (dst : Located) (sel : String) (src0 src1 : Located)
    (hdst : dst.locSrc = .TU64) (hdk : arrKeyB L dst.locVar = false)
    (hst : ¬ isTmpName sel) (hsk : arrKeyB L sel = false)
    (h0t : ¬ isTmpName src0.locVar) (h0k : arrKeyB L src0.locVar = false)
    (h1t : ¬ isTmpName src1.locVar) (h1k : arrKeyB L src1.locVar = false) :
    Corres (SRwordL L) (fun _ => True) (selSet sel dst.locVar src0.locVar src1.locVar)
      (.RSelect dst sel src0 src1) := by
  intro env a hSR _
  obtain ⟨sw, hsw, hswE⟩ := hSR.1 sel hst hsk
  obtain ⟨aw, haw, hawE⟩ := hSR.1 src0.locVar h0t h0k
  obtain ⟨cw, hcw, hcwE⟩ := hSR.1 src1.locVar h1t h1k
  refine ⟨env.upd dst.locVar (t := .sword 64) (selectWord sw aw cw),
    semScalar_rSelect_word dst sel src0 src1 env sw aw cw hdst hsw haw hcw, ?_⟩
  refine srwordL_set dst.locVar (selectWord sw aw cw) _ hdk ?_ hSR
    (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
  by_cases hz : sw = 0#64
  · have haz : a sel = 0 := hswE ▸ (wEnc_eq_zero_iff sw).mpr hz
    rw [selectWord, if_pos hz, if_pos haz, hawE]
  · have haz : ¬ a sel = 0 := fun h => hz ((wEnc_eq_zero_iff sw).mp (hswE ▸ h))
    rw [selectWord, if_neg hz, if_neg haz, hcwE]

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

/-- `ascendExpr` when the destination and the variables of the expression are
    unreserved by the layout, unsupported otherwise. -/
def ascendExprL (L : ArrLayout) (x : String) (e : SExpr) : List Guard × (AField → AField) :=
  if arrKeyB L x || !exprWordB L e then unsupportedAbs "RScalarSetExpr" else ascendExpr x e

/-- The abstraction of a conditional: the guarded `RIfNz name thenBlk RSkip` from the
    abstraction `rec` of its then-branch; the φ-merge on two literal sets of one name;
    unsupported otherwise. A temp guard name is unsupported, the relation binding no
    temp, and so is a guard or destination name reserved by the layout. -/
def ascendIf (L : ArrLayout) (name : String) (thenBr elseBr : LowCT)
    (rec : List Guard × (AField → AField)) : List Guard × (AField → AField) :=
  if isSkipB elseBr then
    if arrKeyB L name then unsupportedAbs "RIfNz"
    else if notTmpB name then
      (rec.1.map (Guard.whenNz name), fun a => if nzB name a then rec.2 a else a)
    else unsupportedAbs "RIfNz"
  else
    match asSingleScalarSet thenBr, asSingleScalarSet elseBr with
    | some ts, some es =>
        if ts.name = es.name ∧ notTmpB name = true ∧ arrKeyB L name = false ∧
            arrKeyB L ts.name = false then
          ([], phiSet name ts.name ts.val es.val)
        else unsupportedAbs "RIfNz"
    | _, _ => unsupportedAbs "RIfNz"

/-- The abstraction of `RArrLoad dst src idxVar`: the read of element
    `idx % (m + 1)` of the layout array `src` of length `m + 1` into the `u64` word
    `dst`, the index a non-temp word name; unsupported otherwise. -/
def arrLoadAbs (L : ArrLayout) (dst src : Located) (idxVar : String) :
    List Guard × (AField → AField) :=
  match layoutSize L src.locVar with
  | some (m + 1) =>
      if dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧ notTmpB idxVar = true ∧
          arrKeyB L idxVar = false then
        ([], fun a => setVal dst.locVar (a (elemKey src.locVar ((a idxVar).val % (m + 1)))) a)
      else unsupportedAbs "RArrLoad"
  | _ => unsupportedAbs "RArrLoad"

/-- The abstraction of `RArrStore arr idxVar src`: the write of the word `src` to element
    `idx % (m + 1)` of the layout array `arr` of length `m + 1`, typed
    `.memref (m + 1)`, index and source non-temp word names; unsupported otherwise. -/
def arrStoreAbs (L : ArrLayout) (arr : Located) (idxVar : String) (src : Located) :
    List Guard × (AField → AField) :=
  match layoutSize L arr.locVar with
  | some (m + 1) =>
      if encodeTy arr.locSrc = .memref (m + 1) ∧ notTmpB idxVar = true ∧
          arrKeyB L idxVar = false ∧ notTmpB src.locVar = true ∧
          arrKeyB L src.locVar = false then
        ([], fun a => setVal (elemKey arr.locVar ((a idxVar).val % (m + 1))) (a src.locVar) a)
      else unsupportedAbs "RArrStore"
  | _ => unsupportedAbs "RArrStore"

/-- The abstraction of `RLimbStore loc idx v`: the write of `v` to element `idx` of the
    layout array `loc`, when `idx` is below its length; unsupported otherwise. -/
def limbStoreAbs (L : ArrLayout) (loc : Located) (idx : Nat) (v : BitVec 64) :
    List Guard × (AField → AField) :=
  match layoutSize L loc.locVar with
  | some n =>
      if idx < n then ([], setVal (elemKey loc.locVar idx) (wEnc v))
      else unsupportedAbs "RLimbStore"
  | none => unsupportedAbs "RLimbStore"

/-- The abstraction of `RArrLoadLit dst src idx`: the read of element `idx` of the
    layout array `src` of length `m + 1 > idx`, typed `TArr _ .TU64`, into the
    unreserved `u64` word `dst`, `idx < 2 ^ 64`; unsupported otherwise, a byte or `u32`
    array included. -/
def arrLoadLitAbs (L : ArrLayout) (dst src : Located) (idx : Nat) :
    List Guard × (AField → AField) :=
  match layoutSize L src.locVar with
  | some (m + 1) =>
      if dst.locSrc = .TU64 ∧ isU64ArrB src.locSrc = true ∧ arrKeyB L dst.locVar = false ∧
          idx < m + 1 ∧ idx < 2 ^ 64 then
        ([], fun a => setVal dst.locVar (a (elemKey src.locVar idx)) a)
      else unsupportedAbs "RArrLoadLit"
  | _ => unsupportedAbs "RArrLoadLit"

/-- The abstraction of `RArrStoreLit arr idx src`: the write of the word `src` to element
    `idx` of the layout array `arr` of length `m + 1 > idx`, typed `TArr _ .TU64`,
    `idx < 2 ^ 64`, the source a non-temp unreserved name; unsupported otherwise, a byte
    or `u32` array included. -/
def arrStoreLitAbs (L : ArrLayout) (arr : Located) (idx : Nat) (src : Located) :
    List Guard × (AField → AField) :=
  match layoutSize L arr.locVar with
  | some (m + 1) =>
      if isU64ArrB arr.locSrc = true ∧ idx < m + 1 ∧ idx < 2 ^ 64 ∧
          notTmpB src.locVar = true ∧ arrKeyB L src.locVar = false then
        ([], fun a => setVal (elemKey arr.locVar idx) (a src.locVar) a)
      else unsupportedAbs "RArrStoreLit"
  | _ => unsupportedAbs "RArrStoreLit"

/-- The abstraction of `RSelect dst sel src0 src1`: the select of the word `src0` or
    `src1` by the word `sel` into the `u64` word `dst`, all non-temp names unreserved by
    the layout; unsupported otherwise. -/
def selectAbs (L : ArrLayout) (dst : Located) (sel : String) (src0 src1 : Located) :
    List Guard × (AField → AField) :=
  if dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧ notTmpB sel = true ∧
      arrKeyB L sel = false ∧ notTmpB src0.locVar = true ∧ arrKeyB L src0.locVar = false ∧
      notTmpB src1.locVar = true ∧ arrKeyB L src1.locVar = false then
    ([], selSet sel dst.locVar src0.locVar src1.locVar)
  else unsupportedAbs "RSelect"

/-- The total abstraction over a layout: every `LowCT` command to a word transformer
    over `AField` and the guards under which it is sound at the unified waist
    `semU fuel`, over `SRwordL L`. -/
def ascendGL (L : ArrLayout) (fuel : Nat) : LowCT → List Guard × (AField → AField)
  | .RSkip => ([], id)
  | .RBlock body => ascendGL L fuel body
  | .RSeq c₁ c₂ =>
      ((ascendGL L fuel c₁).1 ++ (ascendGL L fuel c₂).1.map (Guard.after (ascendGL L fuel c₁).2),
        fun a => (ascendGL L fuel c₂).2 ((ascendGL L fuel c₁).2 a))
  | .RScalarSet x n => if arrKeyB L x then unsupportedAbs "RScalarSet" else ([], setLit x n)
  | .RScalarSetExpr x e => ascendExprL L x e
  | .RAssert label => ([Guard.assert label], id)
  | .RLetU64Zero x body =>
      if arrKeyB L x then unsupportedAbs "RLetU64Zero"
      else if loopFree body then
        ((ascendGL L fuel body).1.map (Guard.after (setLit x 0)),
          fun a => (ascendGL L fuel body).2 (setLit x 0 a))
      else unsupportedAbs "RLetU64Zero"
  | .RIfNz name thenBr elseBr => ascendIf L name thenBr elseBr (ascendGL L fuel thenBr)
  | .RWhileNz name body =>
      if arrKeyB L name then unsupportedAbs "RWhileNz"
      else if notTmpB name then
        (Guard.loopHalts name fuel (ascendGL L fuel body).2 ::
            (ascendGL L fuel body).1.map (Guard.loopBody name fuel (ascendGL L fuel body).2),
          awhile (nzB name) (ascendGL L fuel body).2 fuel)
      else unsupportedAbs "RWhileNz"
  | .RFor x N body =>
      if arrKeyB L x then unsupportedAbs "RFor"
      else
        ((ascendGL L fuel body).1.map (Guard.everyTrip x N (ascendGL L fuel body).2),
          forFold (setLit x) (ascendGL L fuel body).2 N)
  | .RArrLoad dst src idxVar => arrLoadAbs L dst src idxVar
  | .RArrStore arr idxVar src => arrStoreAbs L arr idxVar src
  | .RLimbStore loc idx v => limbStoreAbs L loc idx v
  | .RLetZero _ _ _ => unsupportedAbs "RLetZero"
  | .RCall _ _ _ => unsupportedAbs "RCall"
  | .RCallSwap _ _ _ _ => unsupportedAbs "RCallSwap"
  | .RCloneCall _ _ _ _ _ _ => unsupportedAbs "RCloneCall"
  | .RCallN _ _ _ => unsupportedAbs "RCallN"
  | .RSelect dst sel src0 src1 => selectAbs L dst sel src0 src1
  | .RLimbStoreExpr _ _ _ => unsupportedAbs "RLimbStoreExpr"
  | .RFnDef _ _ _ _ _ => unsupportedAbs "RFnDef"
  | .RFnCall _ _ _ => unsupportedAbs "RFnCall"
  | .RTupleLoad _ _ _ => unsupportedAbs "RTupleLoad"
  | .RArrStoreLit arr idx src => arrStoreLitAbs L arr idx src
  | .RArrLoadLit dst src idx => arrLoadLitAbs L dst src idx
  | .RCallDstThreaded _ _ _ => unsupportedAbs "RCallDstThreaded"
  | .RForRuntime _ _ _ => unsupportedAbs "RForRuntime"
  | .RCopy _ _ => unsupportedAbs "RCopy"

/-- The total abstraction over the empty layout, whose relation is `SRwordNT`. -/
abbrev ascendG (fuel : Nat) : LowCT → List Guard × (AField → AField) := ascendGL [] fuel

/-! ## Soundness -/

theorem asSingleScalarSet_some {c : LowCT} {s : SingleScalarSet}
    (h : asSingleScalarSet c = some s) : c = .RScalarSet s.name s.val := by
  cases c <;> cases h
  rfl

/-- Soundness of the total abstraction at the unified waist: under its guards, the
    transformer `ascendGL L fuel c` is a `CorresU fuel (SRwordL L)` correspondent of
    `c`. -/
theorem ascendGL_sound (L : ArrLayout) (fuel : Nat) :
    ∀ c : LowCT,
      CorresU fuel (SRwordL L) (guardsHold (ascendGL L fuel c).1) (ascendGL L fuel c).2 c := by
  intro c
  induction c
  case RSkip =>
    show CorresU fuel (SRwordL L) (guardsHold []) id .RSkip
    exact corresU_weaken _ (corresU_of_corres _ rfl (corres_skip _)) (fun _ _ => trivial)
  case RBlock body ih =>
    show CorresU fuel (SRwordL L) (guardsHold (ascendGL L fuel body).1) (ascendGL L fuel body).2
      (.RBlock body)
    exact corresU_block _ ih
  case RSeq c₁ c₂ ih₁ ih₂ =>
    show CorresU fuel (SRwordL L)
      (guardsHold ((ascendGL L fuel c₁).1 ++
        (ascendGL L fuel c₂).1.map (Guard.after (ascendGL L fuel c₁).2)))
      (fun a => (ascendGL L fuel c₂).2 ((ascendGL L fuel c₁).2 a)) (.RSeq c₁ c₂)
    refine corresU_seq _
      (corresU_weaken _ ih₁ (fun a h => (guardsHold_append.mp h).1)) ih₂ (fun a h => ?_)
    exact guardsHold_map_after.mp (guardsHold_append.mp h).2
  case RScalarSet x n =>
    simp only [ascendGL]
    rcases hk : arrKeyB L x
    · simp only [Bool.false_eq_true, if_false]
      exact corresU_weaken _ (corresU_of_corres _ rfl (corresL_setScalar L x n hk))
        (fun _ _ => trivial)
    · simp only [if_true]
      exact corresU_unsupported _ _ _ _
  case RScalarSetExpr x e =>
    show CorresU fuel (SRwordL L) (guardsHold (ascendExprL L x e).1) (ascendExprL L x e).2
      (.RScalarSetExpr x e)
    unfold ascendExprL
    rcases hx : arrKeyB L x
    · rcases hw : exprWordB L e
      · simp only [Bool.false_or, Bool.not_false, if_true]
        exact corresU_unsupported _ _ _ _
      · simp only [Bool.false_or, Bool.not_true, Bool.false_eq_true, if_false]
        have hvb := exprWordB_sound hw
        unfold ascendExpr
        rcases h1 : isArithCleanB e
        · rcases h2 : srcCleanB e
          · simp only [Bool.false_eq_true, if_false]
            exact corresU_unsupported _ _ _ _
          · simp only [if_true, Bool.false_eq_true, if_false]
            exact corresU_weaken _
              (corresU_of_corres _ rfl
                (corresL_setExprVal L x e hx hvb (srcCleanB_sound e h2)
                  (fun a => e.inRange (natStore a)) (natEval e)
                  (fun a hir => wEnc_evalBV_liftEnv_range a e hir)))
              (fun a h => h _ (List.mem_singleton.mpr rfl))
        · simp only [if_true]
          have he := isArithCleanB_sound e h1
          exact corresU_weaken _
            (corresU_of_corres _ rfl
              (corresL_setExprVal L x e hx hvb (isArithClean_srcClean e he) (fun _ => True)
                (fun a => evalZMod a e) (fun a _ => wEnc_evalBV_liftEnv_arith a e he)))
            (fun _ _ => trivial)
    · simp only [Bool.true_or, if_true]
      exact corresU_unsupported _ _ _ _
  case RAssert label =>
    show CorresU fuel (SRwordL L) (guardsHold [Guard.assert label]) id (.RAssert label)
    exact corresU_weaken _ (corresU_of_corres _ rfl (corres_assert _ label))
      (fun _ _ => trivial)
  case RLetU64Zero x body ih =>
    simp only [ascendGL]
    rcases hk : arrKeyB L x
    · rcases hlf : loopFree body
      · simp only [Bool.false_eq_true, if_false]
        exact corresU_unsupported _ _ _ _
      · simp only [Bool.false_eq_true, if_false, if_true]
        intro env a hSR hP
        obtain ⟨env', hstep, hSRf⟩ :=
          ih _ _ (srwordL_upd_lit x 0 hk hSR) (guardsHold_map_after.mp hP)
        refine ⟨env', ?_, hSRf⟩
        show semScalar body (env.upd x (t := .sword 64) (0 : BitVec 64)) = some env'
        rw [← semU_eq_semScalar_of_loopFree fuel body hlf]
        exact hstep
    · simp only [if_true]
      exact corresU_unsupported _ _ _ _
  case RIfNz name thenBr elseBr ihT _ =>
    simp only [ascendGL]
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
          by_cases hc : nv = nv' ∧ notTmpB name = true ∧ arrKeyB L name = false ∧
              arrKeyB L nv = false
          · rw [if_pos hc]
            obtain ⟨hnv, hnt, hk, hkv⟩ := hc
            subst hnv
            obtain rfl := asSingleScalarSet_some ht
            obtain rfl := asSingleScalarSet_some he
            exact corresU_weaken _
              (corresU_of_corres _ (isSeqLike_rIfNz_of_ne _ _ _ hne)
                (corresL_if L name nv tv ev (notTmpB_sound name hnt) hk hkv))
              (fun _ _ => trivial)
          · rw [if_neg hc]
            exact corresU_unsupported _ _ _ _
    · obtain rfl := (isSkipB_iff elseBr).mp hsk
      simp only [if_true]
      rcases hk : arrKeyB L name
      · simp only [Bool.false_eq_true, if_false]
        rcases hnt : notTmpB name
        · simp only [Bool.false_eq_true, if_false]
          exact corresU_unsupported _ _ _ _
        · simp only [if_true]
          exact corresU_weaken _
            (corresU_cond _ (nzB name)
              (fun env a hSR => guardNz_srwordL (notTmpB_sound name hnt) hk hSR) ihT)
            (fun a h => guardsHold_map_whenNz.mp h)
      · simp only [if_true]
        exact corresU_unsupported _ _ _ _
  case RWhileNz name body ih =>
    simp only [ascendGL]
    rcases hk : arrKeyB L name
    · rcases hnt : notTmpB name
      · simp only [Bool.false_eq_true, if_false]
        exact corresU_unsupported _ _ _ _
      · simp only [Bool.false_eq_true, if_false, if_true]
        refine corresU_weaken _
          (corresU_whileNz _ (nzB name)
            (fun env a hSR => guardNz_srwordL (notTmpB_sound name hnt) hk hSR) ih)
          (fun a h => ?_)
        refine ⟨h _ (List.mem_cons.mpr (Or.inl rfl)), guardsHold_map_loopBody.mp ?_⟩
        exact fun g hg => h g (List.mem_cons.mpr (Or.inr hg))
    · simp only [if_true]
      exact corresU_unsupported _ _ _ _
  case RFor x N body ih =>
    simp only [ascendGL]
    rcases hk : arrKeyB L x
    · simp only [Bool.false_eq_true, if_false]
      exact corresU_weaken _
        (corresU_for_trips _ (setLit x) (fun env a n hSR => srwordL_upd_lit x n hk hSR) ih N)
        (fun a h => guardsHold_map_everyTrip.mp h)
    · simp only [if_true]
      exact corresU_unsupported _ _ _ _
  case RArrLoad dst src idxVar =>
    show CorresU fuel (SRwordL L) (guardsHold (arrLoadAbs L dst src idxVar).1)
      (arrLoadAbs L dst src idxVar).2 (.RArrLoad dst src idxVar)
    unfold arrLoadAbs
    rcases hs : layoutSize L src.locVar with _ | _ | m
    · exact corresU_unsupported _ _ _ _
    · exact corresU_unsupported _ _ _ _
    · dsimp only
      by_cases hc : dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
          notTmpB idxVar = true ∧ arrKeyB L idxVar = false
      · rw [if_pos hc]
        obtain ⟨hdst, hdk, hit, hik⟩ := hc
        exact corresU_weaken _
          (corresU_of_corres _ rfl
            (corresL_arrLoad L dst src idxVar m hdst (layoutSize_mem hs) hdk
              (notTmpB_sound _ hit) hik))
          (fun _ _ => trivial)
      · rw [if_neg hc]
        exact corresU_unsupported _ _ _ _
  case RArrStore arr idxVar src =>
    show CorresU fuel (SRwordL L) (guardsHold (arrStoreAbs L arr idxVar src).1)
      (arrStoreAbs L arr idxVar src).2 (.RArrStore arr idxVar src)
    unfold arrStoreAbs
    rcases hs : layoutSize L arr.locVar with _ | _ | m
    · exact corresU_unsupported _ _ _ _
    · exact corresU_unsupported _ _ _ _
    · dsimp only
      by_cases hc : encodeTy arr.locSrc = .memref (m + 1) ∧ notTmpB idxVar = true ∧
          arrKeyB L idxVar = false ∧ notTmpB src.locVar = true ∧ arrKeyB L src.locVar = false
      · rw [if_pos hc]
        obtain ⟨harr, hit, hik, hst, hsk⟩ := hc
        exact corresU_weaken _
          (corresU_of_corres _ rfl
            (corresL_arrStore L arr src idxVar m harr (layoutSize_mem hs)
              (notTmpB_sound _ hit) hik (notTmpB_sound _ hst) hsk))
          (fun _ _ => trivial)
      · rw [if_neg hc]
        exact corresU_unsupported _ _ _ _
  case RLimbStore loc idx v =>
    show CorresU fuel (SRwordL L) (guardsHold (limbStoreAbs L loc idx v).1)
      (limbStoreAbs L loc idx v).2 (.RLimbStore loc idx v)
    unfold limbStoreAbs
    rcases hs : layoutSize L loc.locVar with _ | n
    · exact corresU_unsupported _ _ _ _
    · dsimp only
      by_cases hc : idx < n
      · rw [if_pos hc]
        exact corresU_weaken _
          (corresU_of_corres _ rfl (corresL_limbStore L loc idx v n (layoutSize_mem hs) hc))
          (fun _ _ => trivial)
      · rw [if_neg hc]
        exact corresU_unsupported _ _ _ _
  case RArrLoadLit dst src idx =>
    show CorresU fuel (SRwordL L) (guardsHold (arrLoadLitAbs L dst src idx).1)
      (arrLoadLitAbs L dst src idx).2 (.RArrLoadLit dst src idx)
    unfold arrLoadLitAbs
    rcases hs : layoutSize L src.locVar with _ | _ | m
    · exact corresU_unsupported _ _ _ _
    · exact corresU_unsupported _ _ _ _
    · dsimp only
      by_cases hc : dst.locSrc = .TU64 ∧ isU64ArrB src.locSrc = true ∧
          arrKeyB L dst.locVar = false ∧ idx < m + 1 ∧ idx < 2 ^ 64
      · rw [if_pos hc]
        obtain ⟨hdst, hu, hdk, hidx, hlit⟩ := hc
        obtain ⟨k, hsrc⟩ := isU64ArrB_sound hu
        exact corresU_weaken _
          (corresU_of_corres _ rfl
            (corresL_arrLoadLit L dst src idx k m hdst hsrc (layoutSize_mem hs) hidx hlit
              hdk))
          (fun _ _ => trivial)
      · rw [if_neg hc]
        exact corresU_unsupported _ _ _ _
  case RArrStoreLit arr idx src =>
    show CorresU fuel (SRwordL L) (guardsHold (arrStoreLitAbs L arr idx src).1)
      (arrStoreLitAbs L arr idx src).2 (.RArrStoreLit arr idx src)
    unfold arrStoreLitAbs
    rcases hs : layoutSize L arr.locVar with _ | _ | m
    · exact corresU_unsupported _ _ _ _
    · exact corresU_unsupported _ _ _ _
    · dsimp only
      by_cases hc : isU64ArrB arr.locSrc = true ∧ idx < m + 1 ∧ idx < 2 ^ 64 ∧
          notTmpB src.locVar = true ∧ arrKeyB L src.locVar = false
      · rw [if_pos hc]
        obtain ⟨hu, hidx, hlit, hst, hsk⟩ := hc
        obtain ⟨k, harr⟩ := isU64ArrB_sound hu
        exact corresU_weaken _
          (corresU_of_corres _ rfl
            (corresL_arrStoreLit L arr src idx k m harr (layoutSize_mem hs) hidx hlit
              (notTmpB_sound _ hst) hsk))
          (fun _ _ => trivial)
      · rw [if_neg hc]
        exact corresU_unsupported _ _ _ _
  case RSelect dst sel src0 src1 =>
    show CorresU fuel (SRwordL L) (guardsHold (selectAbs L dst sel src0 src1).1)
      (selectAbs L dst sel src0 src1).2 (.RSelect dst sel src0 src1)
    unfold selectAbs
    by_cases hc : dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧ notTmpB sel = true ∧
        arrKeyB L sel = false ∧ notTmpB src0.locVar = true ∧ arrKeyB L src0.locVar = false ∧
        notTmpB src1.locVar = true ∧ arrKeyB L src1.locVar = false
    · rw [if_pos hc]
      obtain ⟨hdst, hdk, hst, hsk, h0t, h0k, h1t, h1k⟩ := hc
      exact corresU_weaken _
        (corresU_of_corres _ rfl
          (corresL_select L dst sel src0 src1 hdst hdk (notTmpB_sound _ hst) hsk
            (notTmpB_sound _ h0t) h0k (notTmpB_sound _ h1t) h1k))
        (fun _ _ => trivial)
    · rw [if_neg hc]
      exact corresU_unsupported _ _ _ _
  all_goals exact corresU_unsupported _ _ _ _

/-- Soundness of `ascendG`: the instance of `ascendGL_sound` at the empty layout, over
    `SRwordNT`. -/
theorem ascendG_sound (fuel : Nat) :
    ∀ c : LowCT, CorresU fuel SRwordNT (guardsHold (ascendG fuel c).1) (ascendG fuel c).2 c := by
  intro c env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := ascendGL_sound [] fuel c env a (srwordL_nil_iff.mpr hSR) hP
  exact ⟨env', hstep, srwordL_nil_iff.mp hSR'⟩

/-- On a loop-free command the unified waist is `semScalar`, so the abstraction over a
    layout is a `Corres` correspondent. -/
theorem ascendGL_sound_scalar (L : ArrLayout) (fuel : Nat) (c : LowCT)
    (hlf : loopFree c = true) :
    Corres (SRwordL L) (guardsHold (ascendGL L fuel c).1) (ascendGL L fuel c).2 c := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := ascendGL_sound L fuel c env a hSR hP
  refine ⟨env', ?_, hSR'⟩
  rw [← semU_eq_semScalar_of_loopFree fuel c hlf]
  exact hstep

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

/-! ## An array kernel closed through `ascendGL_sound_scalar`

`arrSelK` reads `x := A[i]` and `y := A[j]` from a four-element array `A`, computes the
branchless mask select `r := y ^^^ ((x ^^^ y) &&& m)`, and writes `A[k] := r`. Over the
layout `[("A", 4)]` its abstraction carries one guard, the range condition of the
select, which holds on every store (`arrSelK_guardsHold`), and its transformer is
`arrSelKAbs` (`arrSelK_ascendGL_prog`). `arrSelK_srwordL` exhibits a store and an
abstract store related by `SRwordL [("A", 4)]`. -/

/-- The layout with one array `A` of four elements. -/
def arrSelLayout : ArrLayout := [("A", 4)]

/-- The mask-select expression `y ^^^ ((x ^^^ y) &&& m)`. -/
def arrSelE : SExpr := .SXor (.SVar "y") (.SAnd (.SXor (.SVar "x") (.SVar "y")) (.SVar "m"))

/-- `x := A[i]; y := A[j]; r := y ^^^ ((x ^^^ y) &&& m); A[k] := r`. -/
def arrSelK : LowCT :=
  .RSeq (.RArrLoad ⟨"x", .TU64⟩ ⟨"A", .TFp25519_64⟩ "i")
    (.RSeq (.RArrLoad ⟨"y", .TU64⟩ ⟨"A", .TFp25519_64⟩ "j")
      (.RSeq (.RScalarSetExpr "r" arrSelE)
        (.RArrStore ⟨"A", .TFp25519_64⟩ "k" ⟨"r", .TU64⟩)))

/-- The abstract program of `arrSelK`: the two reads at the indices modulo `4`, the
    Nat-model select, and the write at the index modulo `4`. -/
def arrSelKAbs (a : AField) : AField :=
  let a₁ := setVal "x" (a (elemKey "A" ((a "i").val % 4))) a
  let a₂ := setVal "y" (a₁ (elemKey "A" ((a₁ "j").val % 4))) a₁
  let a₃ := setVal "r" (natEval arrSelE a₂) a₂
  setVal (elemKey "A" ((a₃ "k").val % 4)) (a₃ "r") a₃

theorem arrSelK_ascendGL_prog (fuel : Nat) :
    (ascendGL arrSelLayout fuel arrSelK).2 = arrSelKAbs := rfl

theorem arrSelK_guards (fuel : Nat) :
    (ascendGL arrSelLayout fuel arrSelK).1 =
      [Guard.after (fun a => setVal "x" (a (elemKey "A" ((a "i").val % 4))) a)
        (Guard.after (fun a => setVal "y" (a (elemKey "A" ((a "j").val % 4))) a)
          (Guard.range "r" arrSelE))] := rfl

theorem arrSelK_guardsHold (fuel : Nat) (a : AField) :
    guardsHold (ascendGL arrSelLayout fuel arrSelK).1 a := by
  rw [arrSelK_guards]
  simp [guardsHold, Guard.holds, arrSelE, SExpr.inRange, natStore, ZMod.val_lt]

/-- `arrSelK` refines `arrSelKAbs` over `SRwordL arrSelLayout` on every store. -/
theorem arrSelK_corres : Corres (SRwordL arrSelLayout) (fun _ => True) arrSelKAbs arrSelK := by
  have h := ascendGL_sound_scalar arrSelLayout 0 arrSelK rfl
  rw [arrSelK_ascendGL_prog] at h
  exact corres_weaken _ h (fun a _ => arrSelK_guardsHold 0 a)

/-- The concrete store binding `A` to the zero array and every other name to the zero
    word. -/
def arrSelEnv : SEnvScalar :=
  fun s => if s = "A" then some ⟨.memref 4, fun _ => (0 : BitVec 64)⟩
    else some ⟨.sword 64, (0 : BitVec 64)⟩

/-- The relation of `arrSelK_corres` holds between `arrSelEnv` and the all-zero
    abstract store. -/
theorem arrSelK_srwordL : SRwordL arrSelLayout arrSelEnv zeroStore := by
  refine ⟨fun x _ hx => ?_, fun p hp => ?_⟩
  · have hxA : x ≠ "A" := by rintro rfl; exact absurd hx (by decide)
    exact ⟨0, by simp [arrSelEnv, hxA], by simp [wEnc, zeroStore]⟩
  · simp only [arrSelLayout, List.mem_singleton] at hp
    subst hp
    exact ⟨notTmpB_sound "A" rfl, fun _ => 0, by simp [arrSelEnv], fun _ => by
      simp [wEnc, zeroStore]⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
