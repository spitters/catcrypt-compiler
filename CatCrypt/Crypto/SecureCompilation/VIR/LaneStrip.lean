/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LaneStripKernel

/-!
# Strip-mining of counted loops with elementwise bodies

`stripMine l w` maps a counted loop `forLoop count inits body k` over `jasminDialect` whose
body `elemwise?` recognises at `2 ^ l` lanes of `w` bits to a program of `jasminTileMem` over
the same context and results at their scalar types:

* three bindings: the block count `count >>> l`, the number `(count >>> l) <<< l` of
  iterations in blocks, and the remainder count, their difference from `count`;
* the block loop, which at the block `b` binds the index `b <<< l` and runs the lane form of
  the body;
* the remainder loop, which at the trip `j` binds the index of the iterations in blocks plus
  `j` and runs the body, included by `incl` along a renaming;
* the continuation, included by `incl`.

The carried arrays keep their scalar types, so the relation of inputs and of results is the
scalar reading `unmapInl` of a valuation of the target.

The events of the strip-mined program are a function `stripEv (2 ^ l) c` of the events of the
loop, for the number `c` of events of one iteration: the trip count of the block loop, the
events of the first iteration of each block, the trip count of the remainder loop, and the
events of the remaining iterations and of the continuation.

## Main definitions

* `pickBlocks`, `stripEv` — the selection of events.
* `Ren`, `incl` — renamings into a target context and the inclusion of a scalar program along
  one.
* `stripLoops`, `stripProg`, `stripMine` — the two loops, the program and the pass.
* `IdxQuiet` — the leakage models in which the added index operations are quiet.
* `addrModel` — the leakage model in which only loads and stores emit.
* `memSem`, `memLeakSem`, `stripMineCert`, `stripMineLeakCert` — the semantics of programs of
  `jasminTileMem` and the step certificates.

## Main results

* `incl_leakRun` — the inclusion preserves results and events.
* `block_run`, `blocks_run` — `2 ^ l` scalar iterations from the index `B` run to the tuple
  one run of the lane form at `B` returns, for `B + 2 ^ l ≤ 2 ^ 64`, and likewise over a list
  of blocks.
* `stripMine_leakRun` — the loop and the strip-mined program both fail, or both succeed with
  the same results and the events of the second equal to `stripEv` of the events of the first.
* `stripMine_denote` — the scalar reading of the denotation of the strip-mined program is the
  denotation of the loop, at every fuel.
* `stripMineLeakCert_ct` — the output relation of the leakage certificate implies
  `PassChain.ctRel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneStrip

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.TileBridge
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF
open CatCrypt.Crypto.SecureCompilation.VIR.LaneStripKernel
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
  (hvAppend inlHom inrHom lookup_inlHom lookup_inrHom)
open Ctxt (Var Valuation)

attribute [local instance] jasminTileDenote jasminTileMemDenote

/-! ## 1. Trip indices and iterations -/

/-- The first `Q * L` trip indices are the indices `b * L + i`, `i < L`, of the blocks
    `b < Q` in order, and the next `R` are `Q * L + i`. -/
theorem range_blocks (L R : Nat) (Q : Nat) :
    List.range (Q * L + R) =
      (List.range Q).flatMap (fun b => (List.range L).map (b * L + ·)) ++
        (List.range R).map (Q * L + ·) := by
  have hmain : ∀ Q : Nat, List.range (Q * L) =
      (List.range Q).flatMap (fun b => (List.range L).map (b * L + ·)) := by
    intro Q
    induction Q with
    | zero =>
        rw [Nat.zero_mul]
        rfl
    | succ Q ih =>
        rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.range_add, hmain Q]

/-- The run of the iterations of two lists of indices in sequence. -/
theorem forIterLeak_append {d : Dialect.{0, 0}} [TyDenote d.Ty] {cs : List d.Ty}
    (step : Nat → Valuation cs → Option (Valuation cs × List CTLeak)) :
    ∀ (is₁ is₂ : List Nat) (a : Valuation cs),
      forIterLeak step (is₁ ++ is₂) a =
        (forIterLeak step is₁ a).bind fun r =>
          (forIterLeak step is₂ r.1).map fun q => (q.1, r.2 ++ q.2)
  | [], is₂, a => by
      show forIterLeak step is₂ a = (forIterLeak step is₂ a).map fun q => (q.1, [] ++ q.2)
      rcases forIterLeak step is₂ a with _ | q <;> rfl
  | i :: is₁, is₂, a => by
      show ((step i a).bind fun r =>
          (forIterLeak step (is₁ ++ is₂) r.1).map fun q => (q.1, r.2 ++ q.2)) =
        ((step i a).bind fun r =>
          (forIterLeak step is₁ r.1).map fun q => (q.1, r.2 ++ q.2)).bind _
      rcases step i a with _ | r
      · rfl
      · simp only [Option.bind_some]
        rw [forIterLeak_append step is₁ is₂ r.1]
        rcases forIterLeak step is₁ r.1 with _ | q1
        · rfl
        · simp only [Option.bind_some, Option.map_some]
          rcases forIterLeak step is₂ q1.1 with _ | q2
          · rfl
          · simp only [Option.map_some, List.append_assoc]

/-- The run over the images of a list of indices is the run of the reindexed step. -/
theorem forIterLeak_map {d : Dialect.{0, 0}} [TyDenote d.Ty] {cs : List d.Ty}
    (step : Nat → Valuation cs → Option (Valuation cs × List CTLeak)) (f : Nat → Nat) :
    ∀ (is : List Nat) (a : Valuation cs),
      forIterLeak step (is.map f) a = forIterLeak (fun i => step (f i)) is a
  | [], _ => rfl
  | i :: is, a => by
      show ((step (f i) a).bind fun r =>
          (forIterLeak step (is.map f) r.1).map fun q => (q.1, r.2 ++ q.2)) =
        ((step (f i) a).bind fun r =>
          (forIterLeak (fun i => step (f i)) is r.1).map fun q => (q.1, r.2 ++ q.2))
      simp only [forIterLeak_map step f is]

/-! ## 2. The selection of events -/

/-- The first `c` events of each of `q` consecutive groups of `L * c` events. -/
def pickBlocks (L c : Nat) : Nat → List CTLeak → List CTLeak
  | 0, _ => []
  | q + 1, evs => evs.take c ++ pickBlocks L c q (evs.drop (L * c))

/-- **The events of the strip-mined loop as a selection of the events of the loop.** For the
    events `trip N :: evs` of a counted loop of `N` trips with `c` events per iteration: the
    trip count `N / L` of the block loop, the events of the first iteration of each block,
    the trip count `N % L` of the remainder loop, and the events after the blocks. -/
def stripEv (L c : Nat) : List CTLeak → List CTLeak
  | .trip N :: evs =>
      .trip (N / L) ::
        (pickBlocks L c (N / L) evs ++ .trip (N % L) :: evs.drop (N / L * (L * c)))
  | evs => evs

/-- The runs of a remainder loop and a continuation after a block loop. For remainder runs
    `sr` and `tr` and continuations `kS` and `kT` that both fail or both succeed with the
    same results and events, block events `Em` and `E'`, and a selection `sel` that sends
    `trip N :: (Em ++ rest)` to `trip Q :: (E' ++ trip R :: rest)`: the two composed runs both
    fail, or both succeed with the same results and the events of the second equal to `sel`
    of the events of the first. -/
theorem strip_assemble {α α' β β' : Type} {T : α' → α} {T₂ : β' → β}
    (sr : Option (α × List CTLeak)) (tr : Option (α' × List CTLeak))
    (hrem : Option.Rel (fun r r' => r.1 = T r'.1 ∧ r.2 = r'.2) sr tr)
    (kS : α → Option (β × List CTLeak)) (kT : α' → Option (β' × List CTLeak))
    (hk : ∀ a', Option.Rel (fun r r' => r.1 = T₂ r'.1 ∧ r.2 = r'.2) (kS (T a')) (kT a'))
    (Em E' : List CTLeak) (N Q R : Nat) (sel : List CTLeak → List CTLeak)
    (hsel : ∀ rest, sel (.trip N :: (Em ++ rest)) = .trip Q :: (E' ++ .trip R :: rest)) :
    Option.Rel (fun a a' => a.1 = T₂ a'.1 ∧ a'.2 = sel a.2)
      ((sr.map fun q => (q.1, Em ++ q.2)).bind fun r =>
        (kS r.1).map fun q => (q.1, .trip N :: (r.2 ++ q.2)))
      ((tr.bind fun r => (kT r.1).map fun q => (q.1, .trip R :: (r.2 ++ q.2))).map fun q =>
        (q.1, .trip Q :: (E' ++ q.2))) := by
  cases hrem with
  | none => exact .none
  | some hr =>
      rename_i r r'
      obtain ⟨h1, h2⟩ := hr
      have hk' := hk r'.1
      rw [← h1] at hk'
      simp only [Option.map_some, Option.bind_some]
      generalize kS r.1 = x at hk' ⊢
      generalize kT r'.1 = y at hk' ⊢
      cases hk' with
      | none => exact .none
      | some hq =>
          rename_i q q'
          refine .some ⟨hq.1, ?_⟩
          show CTLeak.trip Q :: (E' ++ CTLeak.trip R :: (r'.2 ++ q'.2)) =
            sel (CTLeak.trip N :: ((Em ++ r.2) ++ q.2))
          rw [List.append_assoc, hsel, h2, hq.2]

/-! ## 3. The inclusion of scalar programs along a renaming -/

section Incl

/-- A renaming of the variables of a scalar context into a target context, at the scalar
    types. -/
abbrev Ren (Γ : Ctxt jasminDialect) (Δ : Ctxt jasminTileDialect) : Type :=
  ∀ t : JasminTy, Var Γ t → Var Δ (Sum.inl t)

variable {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}

/-- The renaming under a binding kept at its type. -/
def Ren.lift (ρ : Ren Γ Δ) (s : JasminTy) : Ren (s :: Γ) (Sum.inl s :: Δ)
  | _, .here => .here
  | _, .there v => .there (ρ _ v)

/-- The renaming under a tuple of bindings kept at their types. -/
def Ren.app (ρ : Ren Γ Δ) : (cs : List JasminTy) →
    Ren (cs ++ Γ) (cs.map (Sum.inl (β := TileTy)) ++ Δ)
  | [] => ρ
  | s :: cs => (Ren.app ρ cs).lift s

/-- The renaming of `cs ++ Γ` that is `f` on `cs` and `g` on `Γ`. -/
def Ren.split : (cs : List JasminTy) →
    (∀ t, Var (d := jasminDialect) cs t → Var Δ (Sum.inl t)) → Ren Γ Δ → Ren (cs ++ Γ) Δ
  | [], _, g => g
  | _ :: cs, f, g => fun
      | _, .here => f _ .here
      | _, .there v => Ren.split cs (fun t x => f t (.there x)) g _ v

/-- A renamed argument vector. -/
def renArgs (ρ : Ren Γ Δ) : {ts : List JasminTy} → HVector (fun t => Var Γ t) ts →
    HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy)))
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (ρ _ v) (renArgs ρ vs)

/-- **The inclusion of a scalar program along a renaming**: every operation in the scalar
    summand of `jasminTileDialect`, every region kept. -/
def incl : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
    {Δ : Ctxt jasminTileDialect} → Ren Γ Δ →
    NFProg jasminTileDialect Δ (ts.map (Sum.inl (β := TileTy)))
  | _, _, .ret vs, _, ρ => .ret (renArgs ρ vs)
  | _, _, .var e k, _, ρ =>
      .var ⟨.inl e.op, congrArg Sum.inl e.retTy_eq, renArgs ρ e.args⟩ (incl k (ρ.lift _))
  | _, _, .forLoop (cs := cs) count inits body k, _, ρ =>
      .forLoop (ρ _ count) (renArgs ρ inits) (incl body ((ρ.lift _).app cs)) (incl k (ρ.app cs))
  | _, _, .ifThenElse (rs := rs) cond thn els k, _, ρ =>
      .ifThenElse (ρ _ cond) (incl thn ρ) (incl els ρ) (incl k (ρ.app rs))
  | _, _, .whileLoop (cs := cs) inits body k, _, ρ =>
      .whileLoop (renArgs ρ inits) (incl body (ρ.app cs)) (incl k (ρ.app cs))
  | _, _, .call (rs := rs) f args k, _, ρ => .call f (renArgs ρ args) (incl k (ρ.app rs))

/-- A target valuation `W` reads the source valuation `V` along `ρ`. -/
def RenRel (ρ : Ren Γ Δ) (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  ∀ (t : JasminTy) (v : Var Γ t), (ρ t v).lookup W = v.lookup V

theorem RenRel.lift {ρ : Ren Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : RenRel ρ V W)
    (s : JasminTy) (x : ⟦s⟧) :
    RenRel (ρ.lift s) (V.extend x)
      (Valuation.extend (d := jasminTileDialect) (t := Sum.inl s) W x) := by
  intro t v
  cases v with
  | here => rfl
  | there v => exact h _ v

theorem RenRel.app {ρ : Ren Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : RenRel ρ V W) :
    (cs : List JasminTy) →
    (a : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))) →
    RenRel (ρ.app cs) (hvAppend (unmapInl (d := jasminDialect) (e := tileDialect) a) V)
      (hvAppend (d := jasminTileDialect) a W)
  | [], .nil => h
  | s :: cs, .cons x xs => RenRel.lift (RenRel.app h cs xs) s x

theorem RenRel.split {V : Valuation Γ} {W : Valuation Δ} : (cs : List JasminTy) →
    (f : ∀ t, Var (d := jasminDialect) cs t → Var Δ (Sum.inl t)) → (g : Ren Γ Δ) →
    (A : Valuation (d := jasminDialect) cs) →
    (∀ t (x : Var (d := jasminDialect) cs t), (f t x).lookup W = x.lookup A) →
    RenRel g V W → ∀ (t : JasminTy) (v : Var (d := jasminDialect) (cs ++ Γ) t),
      (Ren.split cs f g t v).lookup W = v.lookup (hvAppend (d := jasminDialect) A V)
  | [], _, _, .nil, _, hg, t, v => hg t v
  | _ :: _, _, _, .cons _ _, hf, _, _, .here => hf _ .here
  | _ :: cs, f, g, .cons _ A, hf, hg, _, .there v =>
      RenRel.split cs (fun t x => f t (.there x)) g A (fun t x => hf t (.there x)) hg _ v

/-- The renaming that sends the first variable to `x` and the others along `g`. -/
def Ren.cons {s : JasminTy} (x : Var Δ (Sum.inl s)) (g : Ren Γ Δ) : Ren (s :: Γ) Δ
  | _, .here => x
  | _, .there v => g _ v

/-- A target valuation reads a source valuation extended by `y` along the renaming that
    sends the first variable to a variable holding `y`. -/
theorem RenRel.head {s : JasminTy} {x : Var Δ (Sum.inl s)} {g : Ren Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (y : ⟦s⟧) (hx : x.lookup W = y) (hg : RenRel g V W) :
    ∀ (t : JasminTy) (v : Var (d := jasminDialect) (s :: Γ) t),
      (Ren.cons x g t v).lookup W = v.lookup (Valuation.extend (d := jasminDialect) V y)
  | _, .here => hx
  | _, .there v => hg _ v

theorem renArgs_sound {ρ : Ren Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : RenRel ρ V W) :
    {ts : List JasminTy} → (vs : HVector (fun t => Var Γ t) ts) →
    unmapInl (d := jasminDialect) (e := tileDialect) (Expr.lookupArgs (renArgs ρ vs) W) =
      Expr.lookupArgs vs V
  | [], .nil => rfl
  | _ :: _, .cons v vs => congrArg₂ HVector.cons (h _ v) (renArgs_sound h vs)

/-- **The inclusion preserves runs**: the scalar run and the run of the included program at
    a valuation that reads the scalar one both fail, or both succeed with the same results
    and events. -/
theorem incl_leakRun (M : LeakModel jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminTileDialect} (ρ : Ren Γ Δ) (V : Valuation Γ) (W : Valuation Δ),
      RenRel ρ V W →
      Option.Rel (fun a a' => a.1 = unmapInl (d := jasminDialect) (e := tileDialect) a'.1 ∧
          a.2 = a'.2)
        (NFProg.leakRunM M fuel p V)
        (NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel (incl p ρ) W) := by
  induction p with
  | ret vs =>
      intro Δ ρ V W hρ
      exact .some ⟨(renArgs_sound hρ vs).symm, rfl⟩
  | var e k ih =>
      intro Δ ρ V W hρ
      obtain ⟨op, rfl, args⟩ := e
      have hargs := renArgs_sound hρ args
      have hden : Expr.denoteM (M := Option)
          (⟨.inl op, rfl, renArgs ρ args⟩ : Expr jasminTileDialect Δ
            (Sum.inl (DialectSignature.ret (d := jasminDialect) op))) W =
          some (DialectDenote.denote op (Expr.lookupArgs args V)) := by
        rw [← hargs]
        rfl
      have hlk : Expr.ctLeak (scalarTileLeak jasminDialect M)
          (⟨.inl op, rfl, renArgs ρ args⟩ : Expr jasminTileDialect Δ
            (Sum.inl (DialectSignature.ret (d := jasminDialect) op))) W =
          Expr.ctLeak M (⟨op, rfl, args⟩ : Expr jasminDialect _ _) V := by
        show opLeak (scalarTileLeak jasminDialect M) (Sum.inl op) _ = opLeak M op _
        rw [scalarTile_opLeak_inl, hargs]
      simp only [incl, NFProg.leakRunM, Expr.denoteM_option_eq_some, Option.bind_some, hden, hlk]
      exact rel_map_ev (R := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
        _ (ih _ _ _ (hρ.lift _ _))
  | forLoop count inits body k ihb ihk =>
      intro Δ ρ V W hρ
      simp only [incl, NFProg.leakRunM]
      rw [show HasWord64.toNat (d := jasminTileDialect) ((ρ _ count).lookup W) =
        HasWord64.toNat (d := jasminDialect) (count.lookup V) from
          congrArg BitVec.toNat (hρ _ count)]
      exact rel_bind_map
        (RA := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
        (RB := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
        (c := fun a => NFProg.leakRunM M fuel k (hvAppend a V))
        (c' := fun a' => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel (incl k (ρ.app _))
          (hvAppend a' W))
        (fun a b => .trip _ :: (a ++ b))
        (NFProg.forIterLeak_rel_bisim
          (R := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
          (step := fun i acc => NFProg.leakRunM M fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)))
          (step' := fun i acc => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel
            (incl body ((ρ.lift _).app _))
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminTileDialect) i) W))) _
          (fun i _ a a' haa => by
            subst haa
            exact ihb _ _ _ ((hρ.lift (JasminTy.reg 64) (BitVec.ofNat 64 i)).app _ a')) _ _
          (renArgs_sound hρ inits).symm)
        (fun a a' haa => by
          subst haa
          exact ihk _ _ _ (hρ.app _ a'))
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ρ V W hρ
      simp only [incl, NFProg.leakRunM]
      rw [show HasBoolBit.toBool (d := jasminTileDialect) ((ρ _ cond).lookup W) =
        HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) from
          congrArg (fun b : BitVec 1 => decide (b = 1#1)) (hρ _ cond)]
      refine rel_bind_map
        (RA := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
        (RB := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
        (c := fun a => NFProg.leakRunM M fuel k (hvAppend a V))
        (c' := fun a' => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel (incl k (ρ.app _))
          (hvAppend a' W))
        (fun a b => .branch _ :: (a ++ b)) ?_
        (fun a a' haa => by
          subst haa
          exact ihk _ _ _ (hρ.app _ a'))
      split
      · exact iht _ _ _ hρ
      · exact ihe _ _ _ hρ
  | whileLoop inits body k ihb ihk =>
      intro Δ ρ V W hρ
      simp only [incl, NFProg.leakRunM]
      exact rel_bind_map
        (RA := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
        (RB := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
        (c := fun a => NFProg.leakRunM M fuel k (hvAppend a V))
        (c' := fun a' => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel (incl k (ρ.app _))
          (hvAppend a' W))
        (fun a b => a ++ b)
        (NFProg.whileIterLeak_rel_bisim
          (R := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
          (step := fun acc => NFProg.leakRunM M fuel body (hvAppend acc V))
          (step' := fun acc => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel
            (incl body (ρ.app _)) (hvAppend acc W))
          (fun a a' haa => by
            subst haa
            refine rel_mono ?_ (ihb _ _ _ (hρ.app _ a'))
            rintro r ⟨r1, e⟩ ⟨h1, h2⟩
            cases r1 with
            | cons x xs => exact ⟨by rw [h1]; rfl, by rw [h1]; rfl, h2⟩) fuel _ _
          (renArgs_sound hρ inits).symm)
        (fun a a' haa => by
          subst haa
          exact ihk _ _ _ (hρ.app _ a'))
  | call f args k ih =>
      intro Δ ρ V W hρ
      exact .none

end Incl

/-! ## 4. A block of iterations -/

section Block

variable {n : Nat}

/-- The array `S` after the scalar iterations of the lanes below `m` of the block at `B`: at a
    position with the residue of one of `B, …, B + m - 1` it has the element of the array `O'`
    the lane form returns, and at every other position the element of the entry array `A`. -/
def arrInv (B m : Nat) : (t : JasminTy) → ⟦t⟧ → ⟦t⟧ → ⟦t⟧ → Prop
  | .stackArr _ N, S, A, O' => ∀ k,
      ((∃ i, i < m ∧ (B + i) % N = k % N) → stackGet S k = stackGet O' k) ∧
      ((¬∃ i, i < m ∧ (B + i) % N = k % N) → stackGet S k = stackGet A k)
  | _, _, _, _ => True

theorem arrInv_zero (B : Nat) (t : JasminTy) (A O' : ⟦t⟧) : arrInv B 0 t A A O' := by
  cases t with
  | stackArr w' N =>
      exact fun k => ⟨fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | reg _ => trivial
  | inlineInt => trivial
  | bool => trivial

theorem arrInv_arrAt {B m : Nat} {t : JasminTy} {S A O' : ⟦t⟧} (hfit : laneFits n t)
    (hm : m < n) (h : arrInv B m t S A O') : arrAt (⟨m, hm⟩ : Fin n) B t S A := by
  cases t with
  | stackArr w' N =>
      refine (h (B + m)).2 ?_
      rintro ⟨i, hi, he⟩
      have h1 : (⟨i, Nat.lt_trans hi hm⟩ : Fin n) = ⟨m, hm⟩ := lane_residue_inj hfit B he
      exact absurd (congrArg Fin.val h1) (Nat.ne_of_lt hi)
  | reg _ => trivial
  | inlineInt => trivial
  | bool => trivial

theorem arrInv_step {B m : Nat} {t : JasminTy} {S A O' S₁ : ⟦t⟧} (hm : m < n)
    (h : arrInv B m t S A O') (hout : outOk (⟨m, hm⟩ : Fin n) B t S A S₁ O') :
    arrInv B (m + 1) t S₁ A O' := by
  cases t with
  | stackArr w' N =>
      obtain ⟨hf, hS, -⟩ := hout
      have hN : 0 < N := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hm) hf
      intro k
      by_cases hk : (B + m) % N = k % N
      · have e1 : stackGet S₁ k = stackGet O' k := by
          rw [hS, stackGet_congr_mod _ hk.symm, stackGet_stackSet_self hN]
          exact stackGet_congr_mod O' hk
        exact ⟨fun _ => e1, fun hne => absurd ⟨m, Nat.lt_succ_self m, hk⟩ hne⟩
      · have e2 : stackGet S₁ k = stackGet S k := by
          rw [hS]
          exact stackGet_stackSet_of_ne S (B + m) k _ (fun e => hk e.symm)
        refine ⟨?_, fun hne => e2.trans ((h k).2 ?_)⟩
        · rintro ⟨i, hi, he⟩
          exact e2.trans ((h k).1 ⟨i, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi)
            (fun e => hk (e ▸ he)), he⟩)
        · rintro ⟨i, hi, he⟩
          exact hne ⟨i, Nat.lt_succ_of_lt hi, he⟩
  | reg _ => trivial
  | inlineInt => trivial
  | bool => trivial

theorem arrInv_final {B : Nat} {t : JasminTy} {S A O' X Y : ⟦t⟧} {j : Fin n}
    (hfit : laneFits n t) (h : arrInv B n t S A O') (hout : outOk j B t X A Y O') :
    S = O' := by
  cases t with
  | stackArr w' N =>
      obtain ⟨-, -, hfr⟩ := hout
      refine stackArr_ext S O' fun k => ?_
      by_cases hk : ∃ i, i < n ∧ (B + i) % N = k % N
      · exact (h k).1 hk
      · exact ((h k).2 hk).trans (hfr k (fun i he => hk ⟨i.val, i.isLt, he⟩)).symm
  | reg _ => exact hfit.elim
  | inlineInt => exact hfit.elim
  | bool => exact hfit.elim

theorem outOk_fits {j : Fin n} {B : Nat} {t : JasminTy} {O O' S S' : ⟦t⟧}
    (h : outOk j B t O O' S S') : laneFits n t := by
  cases t with
  | stackArr w' N => exact h.1
  | reg _ => exact h.elim
  | inlineInt => exact h.elim
  | bool => exact h.elim

theorem arrAt_refl (j : Fin n) (B : Nat) (t : JasminTy) (x : ⟦t⟧) : arrAt j B t x x := by
  cases t with
  | stackArr w' N => exact rfl
  | reg _ => trivial
  | inlineInt => trivial
  | bool => trivial

/-- `TupRel` at each position of the tuple. -/
theorem tupRel_elim {j : Fin n} {B : Nat} : (ts : List JasminTy) →
    (o o' : ∀ t, Var (d := jasminDialect) ts t → ⟦t⟧) →
    (S : Valuation (d := jasminDialect) ts) →
    (S' : Valuation (d := jasminTileDialect) (ts.map (Sum.inl (β := TileTy)))) →
    TupRel j B ts o o' S S' → ∀ (t : JasminTy) (x : Var (d := jasminDialect) ts t),
      outOk j B t (o t x) (o' t x) (x.lookup S)
        (x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) S'))
  | _ :: _, _, _, .cons _ _, .cons _ _, h, _, .here => h.1
  | _ :: ts, o, o', .cons _ S, .cons _ S', h, _, .there x =>
      tupRel_elim ts (fun t x => o t (.there x)) (fun t x => o' t (.there x)) S S' h.2 _ x

/-- Two tuples with the same value at every position are equal. -/
theorem hv_ext : {cs : List JasminTy} → (S T : Valuation (d := jasminDialect) cs) →
    (∀ (t : JasminTy) (x : Var (d := jasminDialect) cs t), x.lookup S = x.lookup T) → S = T
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons _ S, .cons _ T, h =>
      congrArg₂ HVector.cons (h _ .here) (hv_ext S T fun t x => h t (.there x))

theorem arrAt_append {j : Fin n} {B : Nat} {Γ : Ctxt jasminDialect} (Vr : Valuation Γ) :
    (cs : List JasminTy) → (A A₂ : Valuation (d := jasminDialect) cs) →
    (∀ (t : JasminTy) (x : Var (d := jasminDialect) cs t),
      arrAt j B t (x.lookup A) (x.lookup A₂)) →
    ∀ (t : JasminTy) (v : Var (d := jasminDialect) (cs ++ Γ) t),
      arrAt j B t (v.lookup (hvAppend (d := jasminDialect) A Vr))
        (v.lookup (hvAppend (d := jasminDialect) A₂ Vr))
  | [], .nil, .nil, _, t, _ => arrAt_refl j B t _
  | _ :: _, .cons _ _, .cons _ _, h, _, .here => h _ .here
  | _ :: cs, .cons _ A, .cons _ A₂, h, _, .there v =>
      arrAt_append Vr cs A A₂ (fun t x => h t (.there x)) _ v

/-- **The block lemma.** For a body with the lane form `vbody`, a block at `B` with
    `B + n ≤ 2 ^ 64`, and a carried tuple `acc'`: the lane form at the index `B` runs, the `n`
    scalar iterations at the indices `B, …, B + n - 1` from the same tuple run to the tuple the
    lane form returns, their events number `n * evCount`, and the first `evCount` of them are
    the events of the lane form. -/
theorem block_run {w : Nat} (hn : 0 < n) (M : LeakModel jasminDialect) (hM : LaneQuiet w M)
    (hA : ArrAddr M) (fuel : Nat) {Γ : Ctxt jasminDialect} {cs : List JasminTy}
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    {Δ : Ctxt jasminTileDialect} (ren : Ren Γ Δ)
    (vbody : NFProg jasminTileMem
      (Sum.inl (JasminTy.reg 64) ::
        (cs.map (Sum.inl (β := TileTy)) ++ Sum.inl (JasminTy.reg 64) :: Δ))
      (cs.map (Sum.inl (β := TileTy))))
    (hv : laneBody n w body ren = some vbody) (V : Valuation Γ) (W : Valuation Δ)
    (hren : RenRel ren V W) (B : Nat) (hB : B + n ≤ 2 ^ 64)
    (acc' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy))))
    (blk : BitVec 64) :
    ∃ (o' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy))))
      (ev' evs : List CTLeak),
      tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel vbody
        (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
          (hvAppend (d := jasminTileDialect) acc'
            (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64)) W blk))
          (BitVec.ofNat 64 B)) = some (o', ev') ∧
      forIterLeak
        (fun i a => NFProg.leakRunM M fuel body
          (hvAppend a (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 i))))
        ((List.range n).map (B + ·))
        (unmapInl (d := jasminDialect) (e := tileDialect) acc') =
          some (unmapInl (d := jasminDialect) (e := tileDialect) o', evs) ∧
      evs.take (evCount M body) = ev' ∧ evs.length = n * evCount M body := by
  have key : ∀ (m : Nat) (hm : m < n) (S : Valuation (d := jasminDialect) cs),
      (∀ (t : JasminTy) (x : Var (d := jasminDialect) cs t),
        arrAt (⟨m, hm⟩ : Fin n) B t (x.lookup S)
          (x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) acc'))) →
      ∃ (o : Valuation (d := jasminDialect) cs) (ev : List CTLeak)
        (o' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy))))
        (ev' : List CTLeak),
        NFProg.leakRunM M fuel body
          (hvAppend S (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + m))))
          = some (o, ev) ∧
        tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel vbody
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
            (hvAppend (d := jasminTileDialect) acc'
              (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64)) W
                blk))
            (BitVec.ofNat 64 B)) = some (o', ev') ∧
        (∀ (t : JasminTy) (x : Var (d := jasminDialect) cs t),
          outOk (⟨m, hm⟩ : Fin n) B t (x.lookup S)
            (x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) acc')) (x.lookup o)
            (x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) o'))) ∧
        (m = 0 → ev = ev') ∧ ev.length = evCount M body := by
    intro m hm S hat
    obtain ⟨o, ev, o', ev', h1, h2, hT, hE, hl⟩ :=
      stripBody_lane M hM hA fuel (⟨m, hm⟩ : Fin n) B (show B + m < 2 ^ 64 by omega)
        (fun _ v => v.lookup (hvAppend S
          (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + m)))))
        (fun _ v => v.lookup (hvAppend (unmapInl (d := jasminDialect) (e := tileDialect) acc')
          (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + m)))))
        (arrAt_append _ cs S _ hat) body (bodyEnv n w cs ren) .here (fun _ x => inlHom _ x)
        vbody hv _ _ (bodyEnv_rel (⟨m, hm⟩ : Fin n) B cs ren V W hren S acc' (BitVec.ofNat 64 B)
          blk) rfl
    refine ⟨o, ev, o', ev', h1, h2, fun t x => ?_, hE, hl⟩
    have h3 := tupRel_elim cs _ _ o o' hT t x
    rw [lookup_inlHom, lookup_inlHom] at h3
    exact h3
  obtain ⟨o0, ev0, o', ev', -, h20, hT0, -, -⟩ :=
    key 0 hn (unmapInl (d := jasminDialect) (e := tileDialect) acc')
      (fun t x => arrAt_refl _ B t _)
  have hfit : ∀ (t : JasminTy), Var (d := jasminDialect) cs t → laneFits n t :=
    fun t x => outOk_fits (hT0 t x)
  have chain : ∀ m : Nat, m ≤ n → ∃ (S : Valuation (d := jasminDialect) cs)
      (evs : List CTLeak),
      forIterLeak
        (fun i a => NFProg.leakRunM M fuel body
          (hvAppend a (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 i))))
        ((List.range m).map (B + ·))
        (unmapInl (d := jasminDialect) (e := tileDialect) acc') = some (S, evs) ∧
      (∀ (t : JasminTy) (x : Var (d := jasminDialect) cs t),
        arrInv B m t (x.lookup S)
          (x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) acc'))
          (x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) o'))) ∧
      evs.length = m * evCount M body ∧ (0 < m → evs.take (evCount M body) = ev') := by
    intro m
    induction m with
    | zero =>
        intro _
        exact ⟨_, [], rfl, fun t x => arrInv_zero B t _ _, (Nat.zero_mul _).symm,
          fun h => absurd h (Nat.lt_irrefl 0)⟩
    | succ m ih =>
        intro hm
        obtain ⟨S, evs, hrun, hinv, hlen, htake⟩ := ih (Nat.le_of_succ_le hm)
        have hm' : m < n := hm
        obtain ⟨o, ev, o2, ev2, h1, h2, hT, hE, hl⟩ :=
          key m hm' S (fun t x => arrInv_arrAt (hfit t x) hm' (hinv t x))
        have e2 : (o2, ev2) = (o', ev') := Option.some.inj (h2.symm.trans h20)
        cases e2
        have single : forIterLeak
            (fun i a => NFProg.leakRunM M fuel body
              (hvAppend a (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 i))))
            [B + m] S = some (o, ev) := by
          show (NFProg.leakRunM M fuel body _).bind _ = _
          rw [h1]
          show some (o, ev ++ []) = _
          rw [List.append_nil]
        refine ⟨o, evs ++ ev, ?_, fun t x => arrInv_step hm' (hinv t x) (hT t x), ?_, fun _ => ?_⟩
        · rw [List.range_succ, List.map_append, forIterLeak_append, hrun]
          show Option.map _ (forIterLeak _ [B + m] S) = _
          rw [single]
          rfl
        · rw [List.length_append, hlen, hl, Nat.succ_mul]
        · rcases Nat.eq_zero_or_pos m with h0 | hpos
          · subst h0
            have hnil : evs = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, Nat.zero_mul])
            subst hnil
            rw [List.nil_append, ← hE rfl, ← hl, List.take_length]
          · rw [List.take_append_of_le_length
              (by rw [hlen]; exact Nat.le_mul_of_pos_left _ hpos)]
            exact htake hpos
  obtain ⟨S, evs, hrun, hinv, hlen, htake⟩ := chain n (Nat.le_refl n)
  have hS : S = unmapInl (d := jasminDialect) (e := tileDialect) o' :=
    hv_ext _ _ fun t x => arrInv_final (hfit t x) (hinv t x) (hT0 t x)
  subst hS
  exact ⟨o', ev', evs, h20, hrun, htake hn, hlen⟩

/-- **The block loop.** Over a list `bs` of blocks with `b * n + n ≤ 2 ^ 64`, the lane form
    run once per block and the scalar iterations of the indices of the blocks both run, to
    the same tuple; the scalar events number `n * evCount` per block, and the events of the
    lane forms are the first `evCount` of each block. -/
theorem blocks_run {w : Nat} (hn : 0 < n) (M : LeakModel jasminDialect) (hM : LaneQuiet w M)
    (hA : ArrAddr M) (fuel : Nat) {Γ : Ctxt jasminDialect} {cs : List JasminTy}
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    {Δ : Ctxt jasminTileDialect} (ren : Ren Γ Δ)
    (vbody : NFProg jasminTileMem
      (Sum.inl (JasminTy.reg 64) ::
        (cs.map (Sum.inl (β := TileTy)) ++ Sum.inl (JasminTy.reg 64) :: Δ))
      (cs.map (Sum.inl (β := TileTy))))
    (hv : laneBody n w body ren = some vbody) (V : Valuation Γ) (W : Valuation Δ)
    (hren : RenRel ren V W) (blk : Nat → BitVec 64) :
    ∀ (bs : List Nat), (∀ b ∈ bs, b * n + n ≤ 2 ^ 64) →
    ∀ (acc' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))),
    ∃ (o' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy))))
      (E' E : List CTLeak),
      forIterLeak (d := jasminTileDialect)
        (fun b a' => tileMemLeakRun jasminDialect
          (instDialectDenoteMOptionOfPure jasminDialect) M fuel vbody
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
            (hvAppend (d := jasminTileDialect) a'
              (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64)) W
                (blk b)))
            (BitVec.ofNat 64 (b * n))))
        bs acc' = some (o', E') ∧
      forIterLeak
        (fun i a => NFProg.leakRunM M fuel body
          (hvAppend a (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 i))))
        (bs.flatMap fun b => (List.range n).map (b * n + ·))
        (unmapInl (d := jasminDialect) (e := tileDialect) acc') =
          some (unmapInl (d := jasminDialect) (e := tileDialect) o', E) ∧
      E.length = bs.length * (n * evCount M body) ∧
      ∀ rest : List CTLeak, pickBlocks n (evCount M body) bs.length (E ++ rest) = E'
  | [], _, acc' => ⟨acc', [], [], rfl, rfl, (Nat.zero_mul _).symm, fun _ => rfl⟩
  | b :: bs, hbs, acc' => by
      obtain ⟨o1, ev1, evs1, hv1, hs1, ht1, hl1⟩ :=
        block_run hn M hM hA fuel body ren vbody hv V W hren (b * n)
          (hbs b List.mem_cons_self) acc' (blk b)
      obtain ⟨o', E', E, h1, h2, hlen, hpick⟩ :=
        blocks_run hn M hM hA fuel body ren vbody hv V W hren blk bs
          (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')) o1
      refine ⟨o', ev1 ++ E', evs1 ++ E, ?_, ?_, ?_, fun rest => ?_⟩
      · show Option.bind (tileMemLeakRun jasminDialect _ M fuel vbody _) _ = _
        rw [hv1]
        show Option.map _ (forIterLeak (d := jasminTileDialect) _ bs o1) = _
        rw [h1]
        rfl
      · rw [List.flatMap_cons, forIterLeak_append, hs1]
        show Option.map _ (forIterLeak _ _ _) = _
        rw [h2]
        rfl
      · rw [List.length_append, hl1, hlen, List.length_cons, Nat.succ_mul, Nat.add_comm]
      · show ((evs1 ++ E) ++ rest).take (evCount M body) ++
          pickBlocks n (evCount M body) bs.length (((evs1 ++ E) ++ rest).drop
            (n * evCount M body)) = ev1 ++ E'
        rw [List.append_assoc, List.take_append_of_le_length
          (by rw [hl1]; exact Nat.le_mul_of_pos_left _ hn), ht1, List.drop_left' hl1, hpick rest]

end Block

/-! ## 5. The strip-mined loop -/

section Program

/-- A variable of a scalar context in the context of the same types of
    `jasminTileDialect`. -/
def inlVar : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Var Γ t →
    Var (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy))) (Sum.inl t)
  | _, _, .here => .here
  | _, _, .there v => .there (inlVar v)

theorem lookup_inlVar : {Γ : Ctxt jasminDialect} → {t : JasminTy} → (v : Var Γ t) →
    (W : Valuation (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy)))) →
    (inlVar v).lookup W = v.lookup (unmapInl (d := jasminDialect) (e := tileDialect) W)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ W => lookup_inlVar v W

/-- A variable of a carried tuple in a target context that starts with the tuple. -/
def prefVar (Δ : Ctxt jasminTileDialect) : {cs : List JasminTy} → {t : JasminTy} →
    Var (d := jasminDialect) cs t →
    Var (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)) ++ Δ) (Sum.inl t)
  | _, _, .here => .here
  | _, _, .there v => .there (prefVar Δ v)

theorem lookup_prefVar {Δ : Ctxt jasminTileDialect} (W : Valuation Δ) :
    {cs : List JasminTy} → {t : JasminTy} → (x : Var (d := jasminDialect) cs t) →
    (A' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))) →
    (prefVar Δ x).lookup (hvAppend (d := jasminTileDialect) A' W) =
      x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) A')
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there x, .cons _ A' => lookup_prefVar W x A'

/-- The argument vector of the images of the variables of a tuple. -/
def tabVars {Δ : Ctxt jasminTileDialect} : (cs : List JasminTy) →
    (∀ t, Var (d := jasminDialect) cs t → Var Δ (Sum.inl t)) →
    HVector (fun t => Var Δ t) (cs.map (Sum.inl (β := TileTy)))
  | [], _ => .nil
  | _ :: cs, f => .cons (f _ .here) (tabVars cs fun t x => f t (.there x))

theorem lookupArgs_tabVars {Δ : Ctxt jasminTileDialect} (W : Valuation Δ) :
    (cs : List JasminTy) → (f : ∀ t, Var (d := jasminDialect) cs t → Var Δ (Sum.inl t)) →
    (A' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))) →
    (∀ t (x : Var (d := jasminDialect) cs t),
      (f t x).lookup W = x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) A')) →
    Expr.lookupArgs (tabVars cs f) W = A'
  | [], _, .nil, _ => rfl
  | _ :: cs, f, .cons _ A', h =>
      congrArg₂ HVector.cons (h _ .here)
        (lookupArgs_tabVars W cs (fun t x => f t (.there x)) A' fun t x => h t (.there x))

/-- The renaming of the context of a loop body into the context of the remainder loop's
    body: the carried tuple, the index at the head, and the loop-invariant variables along
    `ren` under the two carried tuples and the trip index. -/
def remRen {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (cs : List JasminTy)
    (ren : Ren Γ Δ) :
    Ren (cs ++ JasminTy.reg 64 :: Γ)
      (Sum.inl (JasminTy.reg 64) :: (cs.map (Sum.inl (β := TileTy)) ++
        Sum.inl (JasminTy.reg 64) :: (cs.map (Sum.inl (β := TileTy)) ++ Δ))) :=
  Ren.split cs (fun _ x => .there (prefVar _ x))
    (Ren.cons .here fun t v => .there (inrHom _ (.there (inrHom _ (ren t v)))))

/-- The renaming of the context of the continuation into the context after the remainder
    loop. -/
def contRen {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (cs : List JasminTy)
    (ren : Ren Γ Δ) :
    Ren (cs ++ Γ) (cs.map (Sum.inl (β := TileTy)) ++ (cs.map (Sum.inl (β := TileTy)) ++ Δ)) :=
  Ren.split cs (fun _ x => prefVar _ x) fun t v => inrHom _ (inrHom _ (ren t v))

/-- The context of the two loops: the remainder count, the number of iterations in blocks,
    the block count, and the scalar context. -/
abbrev loopCtx (Γ : Ctxt jasminDialect) : Ctxt jasminTileDialect :=
  Sum.inl (JasminTy.reg 64) :: Sum.inl (JasminTy.reg 64) :: Sum.inl (JasminTy.reg 64) ::
    Γ.map (Sum.inl (β := TileTy))

/-- The renaming of the scalar context into `loopCtx`. -/
def loopRen (Γ : Ctxt jasminDialect) : Ren Γ (loopCtx Γ) :=
  fun _ v => .there (.there (.there (inlVar v)))

/-- A scalar operation as an expression of `jasminTileMem`. -/
def opE {Δ : Ctxt jasminTileDialect} (op : JasminOp)
    (args : HVector (fun t => Var (d := jasminTileMem) Δ t)
      ((DialectSignature.sig (d := jasminDialect) op).map (Sum.inl (β := TileTy)))) :
    Expr jasminTileMem Δ (Sum.inl (DialectSignature.ret (d := jasminDialect) op)) :=
  ⟨.inl (.inl op), rfl, args⟩

/-- The run of a let-binding of a quiet scalar operation is the run of its continuation at
    the value of the operation. -/
theorem leakRun_opE {Δ : Ctxt jasminTileDialect} (M : LeakModel jasminDialect) (fuel : Nat)
    (op : JasminOp)
    (args : HVector (fun t => Var (d := jasminTileMem) Δ t)
      ((DialectSignature.sig (d := jasminDialect) op).map (Sum.inl (β := TileTy))))
    {ts : List jasminTileMem.Ty}
    (k : NFProg jasminTileMem (Sum.inl (DialectSignature.ret (d := jasminDialect) op) :: Δ) ts)
    (W : Valuation Δ) (hq : M.kind op = .quiet) :
    tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel
        (.var (opE op args) k) W =
      tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel k
        (Valuation.extend (d := jasminTileDialect)
          (t := Sum.inl (DialectSignature.ret (d := jasminDialect) op)) W
          (DialectDenote.denote op (unmapInl (d := jasminDialect) (e := tileDialect)
            (Expr.lookupArgs (d := jasminTileMem) args W)))) := by
  have hl : Expr.ctLeak (tileMemLeak jasminDialect M) (opE op args) W = [] := by
    refine (tileMem_opLeak_scalar jasminDialect M op
      (Expr.lookupArgs (d := jasminTileMem) args W)).trans ?_
    unfold opLeak
    rw [hq]
  have hid : ∀ {α : Type} (o : Option (α × List CTLeak)),
      o.map (fun r => (r.1, ([] : List CTLeak) ++ r.2)) = o := by
    intro α o
    rcases o with _ | r <;> rfl
  show Option.map (fun r : Valuation (d := jasminTileMem) ts × List CTLeak =>
    (r.1, Expr.ctLeak (tileMemLeak jasminDialect M) (opE op args) W ++ r.2)) _ = _
  rw [hl]
  exact hid _

/-- A left shift of a trip index by `l` is the index times `2 ^ l`. -/
theorem shl_ofNat (l b : Nat) : BitVec.ofNat 64 b <<< l = BitVec.ofNat 64 (b * 2 ^ l) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

variable (l w : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}

/-- The block loop and the remainder loop of a recognised loop, in `loopCtx`. The block loop
    runs the lane form of the body at the index `b <<< l`; the remainder loop runs the body
    at the index of the iterations in blocks plus its trip index; the continuation follows. -/
def stripLoops (cs : List JasminTy) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts)
    (vbody : NFProg jasminTileMem
      (Sum.inl (JasminTy.reg 64) ::
        (cs.map (Sum.inl (β := TileTy)) ++ Sum.inl (JasminTy.reg 64) :: loopCtx Γ))
      (cs.map (Sum.inl (β := TileTy)))) :
    NFProg jasminTileMem (loopCtx Γ) (ts.map (Sum.inl (β := TileTy))) :=
  .forLoop (d := jasminTileMem) (cs := cs.map (Sum.inl (β := TileTy)))
    (.there (.there .here)) (memArgs (renArgs (loopRen Γ) inits))
    (.var (opE (.shlImm 64 l) (.cons (memVar (inrHom _ .here)) .nil)) vbody)
    (.forLoop (d := jasminTileMem) (cs := cs.map (Sum.inl (β := TileTy)))
      (memVar (inrHom _ .here)) (memArgs (tabVars cs fun _ x => prefVar _ x))
      (.var (opE (.regArith .add 64)
          (.cons (memVar (inrHom _ (.there (inrHom _ (.there .here)))))
            (.cons (memVar (inrHom _ .here)) .nil)))
        (embed jasminDialect (incl body (remRen cs (loopRen Γ)))))
      (embed jasminDialect (incl k (contRen cs (loopRen Γ)))))

/-- The strip-mined program of a recognised loop: the block count `count >>> l`, the number
    of iterations in blocks, the remainder count, and the two loops. -/
def stripProg {p : NFProg jasminDialect Γ ts} (E : Elemwise (2 ^ l) w p (loopRen Γ)) :
    NFProg jasminTileMem (Γ.map (Sum.inl (β := TileTy))) (ts.map (Sum.inl (β := TileTy))) :=
  .var (opE (.shrImm 64 l) (.cons (memVar (inlVar E.count)) .nil)) <|
  .var (opE (.shlImm 64 l) (.cons .here .nil)) <|
  .var (opE (.regArith .sub 64)
    (.cons (.there (.there (memVar (inlVar E.count)))) (.cons .here .nil))) <|
  stripLoops l E.cs E.inits E.body E.k E.vbody

/-- **Strip-mining.** A counted loop whose body `elemwise?` recognises at `2 ^ l` lanes of
    `w` bits becomes a loop over blocks of `2 ^ l` iterations that runs the lane form of the
    body, a loop over the remaining iterations that runs the body, and the continuation, when
    the index shift `l` is below the 64-bit word width; `none` for every other program and for
    `l ≥ 64`. -/
def stripMine (p : NFProg jasminDialect Γ ts) :
    Option (NFProg jasminTileMem (Γ.map (Sum.inl (β := TileTy)))
      (ts.map (Sum.inl (β := TileTy)))) :=
  if l < 64 then (elemwise? (2 ^ l) w (loopRen Γ) p).map (stripProg l w) else none

end Program

/-! ## 6. Preservation of runs -/

section Main

/-- The run of a counted loop in terms of a step function, a trip count and an initial tuple
    that its body, count and initial values denote. -/
theorem leakRunM_forLoop_of {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt d} {cs ts : List d.Ty} (count : Var Γ (HasWord64.word (d := d)))
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (V : Valuation Γ) (step : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (hstep : ∀ i acc, NFProg.leakRunM M fuel body
      (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) = step i acc)
    (N : Nat) (hN : HasWord64.toNat (d := d) (count.lookup V) = N) (I : Valuation cs)
    (hI : Expr.lookupArgs inits V = I) :
    NFProg.leakRunM M fuel (.forLoop count inits body k) V =
      (forIterLeak step (List.range N) I).bind fun r =>
        (NFProg.leakRunM M fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .trip N :: (r.2 ++ q.2)) := by
  subst hN hI
  have hs : (fun i acc => NFProg.leakRunM M fuel body
      (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V))) = step :=
    funext fun i => funext fun acc => hstep i acc
  rw [← hs]
  rfl

/-- The leakage models in which the operations on trip indices that strip-mining adds are
    quiet: the two shifts by `l`, and the subtraction and the addition at 64 bits. -/
def IdxQuiet (l : Nat) (M : LeakModel jasminDialect) : Prop :=
  M.kind (.shrImm 64 l) = .quiet ∧ M.kind (.shlImm 64 l) = .quiet ∧
    M.kind (.regArith .sub 64) = .quiet ∧ M.kind (.regArith .add 64) = .quiet

variable {l w : Nat} {Γ : Ctxt jasminDialect} {ts : List JasminTy}

/-- The valuation of `loopCtx` over a valuation of the scalar context. -/
abbrev loopVal (W : Valuation (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy))))
    (qv qLv rv : BitVec 64) : Valuation (d := jasminTileDialect) (loopCtx Γ) :=
  Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
    (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
      (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64)) W qv) qLv) rv

/-- **The two loops preserve runs.** At a block count `qv`, a number `qLv` of iterations in
    blocks and a remainder count `rv` that are the quotient of the trip count by `2 ^ l`, its
    multiple and the remainder: the counted loop and `stripLoops` both fail, or both succeed
    with the same results and the events of `stripLoops` equal to `stripEv` of the events of
    the loop. -/
theorem loops_run (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (hA : ArrAddr M)
    (hI : IdxQuiet l M) (hl : l < 64) (fuel : Nat) (cs : List JasminTy) (count : Var Γ (JasminTy.reg 64))
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts)
    (vbody : NFProg jasminTileMem
      (Sum.inl (JasminTy.reg 64) ::
        (cs.map (Sum.inl (β := TileTy)) ++ Sum.inl (JasminTy.reg 64) :: loopCtx Γ))
      (cs.map (Sum.inl (β := TileTy))))
    (hv : laneBody (2 ^ l) w body (loopRen Γ) = some vbody)
    (W : Valuation (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy))))
    (V : Valuation Γ) (hV : V = unmapInl (d := jasminDialect) (e := tileDialect) W)
    (N : Nat) (hN : (count.lookup V).toNat = N) (qv qLv rv : BitVec 64)
    (hq : qv.toNat = N / 2 ^ l) (hqL : qLv = BitVec.ofNat 64 (N / 2 ^ l * 2 ^ l))
    (hr : rv.toNat = N % 2 ^ l) :
    Option.Rel
      (fun a a' => a.1 = unmapInl (d := jasminDialect) (e := tileDialect) a'.1 ∧
        a'.2 = stripEv (2 ^ l) (evCount M body) a.2)
      (NFProg.leakRunM M fuel (NFProg.forLoop count inits body k) V)
      (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel
        (stripLoops l cs inits body k vbody) (loopVal W qv qLv rv)) := by
  have hn : 0 < 2 ^ l := Nat.two_pow_pos l
  have hNlt : N < 2 ^ 64 := hN ▸ (count.lookup V).isLt
  have hren : RenRel (loopRen Γ) V (loopVal W qv qLv rv) := by
    intro t v
    rw [hV]
    exact lookup_inlVar v W
  -- the scalar loop
  have hsrc := leakRunM_forLoop_of M fuel count inits body k V
    (fun i a => NFProg.leakRunM M fuel body
      (hvAppend a (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 i))))
    (fun _ _ => rfl) N hN _ (renArgs_sound hren inits).symm
  -- the block loop
  have hblock : ∀ (b : Nat)
      (a' : Valuation (d := jasminTileMem) (cs.map (Sum.inl (β := TileTy)))),
      NFProg.leakRunM (tileMemLeak jasminDialect M) fuel
        (.var (opE (.shlImm 64 l) (.cons (memVar (inrHom _ .here)) .nil)) vbody)
        (hvAppend (d := jasminTileMem) a'
          (.cons (HasWord64.ofNat (d := jasminTileMem) b) (loopVal W qv qLv rv))) =
      tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel vbody
        (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
          (hvAppend (d := jasminTileDialect) a'
            (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
              (loopVal W qv qLv rv) (BitVec.ofNat 64 b)))
          (BitVec.ofNat 64 (b * 2 ^ l))) := by
    intro b a'
    refine (leakRun_opE M fuel _ _ vbody _ hI.2.1).trans ?_
    rw [hvAppend_tileMem]
    have hval : ((memVar (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
        (Var.here (d := jasminTileDialect) (Γ := loopCtx Γ)
          (t := Sum.inl (JasminTy.reg 64))))).lookup (d := jasminTileMem)
        (hvAppend (d := jasminTileDialect) a'
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
            (loopVal W qv qLv rv) (BitVec.ofNat 64 b))) : BitVec 64) = BitVec.ofNat 64 b := by
      rw [lookup_memVar, lookup_inrHom]
      rfl
    refine congrArg (fun x : BitVec 64 =>
      tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel vbody
        (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
          (hvAppend (d := jasminTileDialect) a'
            (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
              (loopVal W qv qLv rv) (BitVec.ofNat 64 b))) x)) ?_
    show BitVec.shiftLeft
      ((memVar (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
        (Var.here (d := jasminTileDialect) (Γ := loopCtx Γ)
          (t := Sum.inl (JasminTy.reg 64))))).lookup (d := jasminTileMem)
        (hvAppend (d := jasminTileDialect) a'
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
            (loopVal W qv qLv rv) (BitVec.ofNat 64 b)))) (shiftMask 64 l) = _
    rw [hval, shiftMask_of_lt hl]
    exact shl_ofNat l b
  have htgt := leakRunM_forLoop_of (d := jasminTileMem) (tileMemLeak jasminDialect M) fuel
    (Γ := loopCtx Γ) (cs := cs.map (Sum.inl (β := TileTy))) (.there (.there .here))
    (memArgs (renArgs (loopRen Γ) inits))
    (.var (opE (.shlImm 64 l) (.cons (memVar (inrHom _ .here)) .nil)) vbody)
    (.forLoop (d := jasminTileMem) (cs := cs.map (Sum.inl (β := TileTy)))
      (memVar (inrHom _ .here)) (memArgs (tabVars cs fun _ x => prefVar _ x))
      (.var (opE (.regArith .add 64)
          (.cons (memVar (inrHom _ (.there (inrHom _ (.there .here)))))
            (.cons (memVar (inrHom _ .here)) .nil)))
        (embed jasminDialect (incl body (remRen cs (loopRen Γ)))))
      (embed jasminDialect (incl k (contRen cs (loopRen Γ)))))
    (loopVal W qv qLv rv) _ hblock (N / 2 ^ l) hq
    (Expr.lookupArgs (d := jasminTileDialect) (renArgs (loopRen Γ) inits)
      (loopVal W qv qLv rv))
    (lookupArgs_memArgs (renArgs (loopRen Γ) inits) (loopVal W qv qLv rv))
  have hbs : ∀ b ∈ List.range (N / 2 ^ l), b * 2 ^ l + 2 ^ l ≤ 2 ^ 64 := by
    intro b hb
    have h1 : (b + 1) * 2 ^ l ≤ N / 2 ^ l * 2 ^ l :=
      Nat.mul_le_mul_right _ (List.mem_range.mp hb)
    rw [Nat.succ_mul] at h1
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.div_mul_le_self N _)) hNlt)
  obtain ⟨o1, E', Em, hmain', hmain, hlenm, hpick⟩ :=
    blocks_run hn M hM hA fuel body (loopRen Γ) vbody hv V (loopVal W qv qLv rv) hren
      (fun b => BitVec.ofNat 64 b) (List.range (N / 2 ^ l)) hbs
      (Expr.lookupArgs (d := jasminTileDialect) (renArgs (loopRen Γ) inits)
        (loopVal W qv qLv rv))
  rw [List.length_range] at hlenm hpick
  have hrange : List.range N =
      (List.range (N / 2 ^ l)).flatMap (fun b => (List.range (2 ^ l)).map (b * 2 ^ l + ·)) ++
        (List.range (N % 2 ^ l)).map (N / 2 ^ l * 2 ^ l + ·) :=
    (congrArg List.range (Nat.div_add_mod' N (2 ^ l)).symm).trans
      (range_blocks (2 ^ l) (N % 2 ^ l) (N / 2 ^ l))
  -- the remainder loop
  have hremstep : ∀ (j : Nat)
      (a' : Valuation (d := jasminTileMem) (cs.map (Sum.inl (β := TileTy)))),
      NFProg.leakRunM (tileMemLeak jasminDialect M) fuel
        (.var (opE (.regArith .add 64)
            (.cons (memVar (inrHom _ (.there (inrHom _ (.there .here)))))
              (.cons (memVar (inrHom _ .here)) .nil)))
          (embed jasminDialect (incl body (remRen cs (loopRen Γ)))))
        (hvAppend (d := jasminTileMem) a'
          (.cons (HasWord64.ofNat (d := jasminTileMem) j)
            (hvAppend (d := jasminTileMem) o1 (loopVal W qv qLv rv)))) =
      scalarTileLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel
        (incl body (remRen cs (loopRen Γ)))
        (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
          (hvAppend (d := jasminTileDialect) a'
            (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
              (hvAppend (d := jasminTileDialect) o1 (loopVal W qv qLv rv))
              (BitVec.ofNat 64 j)))
          (qLv + BitVec.ofNat 64 j)) := by
    intro j a'
    refine (leakRun_opE M fuel _ _ _ _ hI.2.2.2).trans ?_
    rw [hvAppend_tileMem, hvAppend_tileMem]
    refine (embed_leakRunM jasminDialect _ M fuel _ _).trans ?_
    have hq1 : ((memVar (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
        (Var.there (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
          (Var.there (Var.here (d := jasminTileDialect)
            (Γ := Sum.inl (JasminTy.reg 64) :: Γ.map (Sum.inl (β := TileTy)))
            (t := Sum.inl (JasminTy.reg 64))) :
              Var (d := jasminTileDialect) (loopCtx Γ) (Sum.inl (JasminTy.reg 64))))))).lookup
        (d := jasminTileMem)
        (hvAppend (d := jasminTileDialect) a'
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
            (hvAppend (d := jasminTileDialect) o1 (loopVal W qv qLv rv))
            (BitVec.ofNat 64 j))) : BitVec 64) = qLv := by
      rw [lookup_memVar, lookup_inrHom]
      exact lookup_inrHom (loopVal W qv qLv rv) o1 _
    have hq2 : ((memVar (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
        (Var.here (d := jasminTileDialect)
          (Γ := cs.map (Sum.inl (β := TileTy)) ++ loopCtx Γ)
          (t := Sum.inl (JasminTy.reg 64))))).lookup (d := jasminTileMem)
        (hvAppend (d := jasminTileDialect) a'
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
            (hvAppend (d := jasminTileDialect) o1 (loopVal W qv qLv rv))
            (BitVec.ofNat 64 j))) : BitVec 64) = BitVec.ofNat 64 j := by
      rw [lookup_memVar, lookup_inrHom]
      rfl
    refine congrArg (fun x : BitVec 64 =>
      scalarTileLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel
        (incl body (remRen cs (loopRen Γ)))
        (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
          (hvAppend (d := jasminTileDialect) a'
            (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
              (hvAppend (d := jasminTileDialect) o1 (loopVal W qv qLv rv))
              (BitVec.ofNat 64 j))) x)) ?_
    exact congrArg₂ (fun a b : BitVec 64 => a + b) hq1 hq2
  have htgt2 := leakRunM_forLoop_of (d := jasminTileMem) (tileMemLeak jasminDialect M) fuel
    (Γ := cs.map (Sum.inl (β := TileTy)) ++ loopCtx Γ) (cs := cs.map (Sum.inl (β := TileTy)))
    (memVar (inrHom _ .here)) (memArgs (tabVars cs fun _ x => prefVar _ x))
    (.var (opE (.regArith .add 64)
        (.cons (memVar (inrHom _ (.there (inrHom _ (.there .here)))))
          (.cons (memVar (inrHom _ .here)) .nil)))
      (embed jasminDialect (incl body (remRen cs (loopRen Γ)))))
    (embed jasminDialect (incl k (contRen cs (loopRen Γ))))
    (hvAppend (d := jasminTileMem) o1 (loopVal W qv qLv rv)) _ hremstep (N % 2 ^ l)
    (by
      rw [hvAppend_tileMem]
      show BitVec.toNat ((memVar (inrHom (d := jasminTileDialect)
        (cs.map (Sum.inl (β := TileTy))) (Var.here (d := jasminTileDialect)
          (Γ := Sum.inl (JasminTy.reg 64) :: Sum.inl (JasminTy.reg 64) ::
            Γ.map (Sum.inl (β := TileTy)))
          (t := Sum.inl (JasminTy.reg 64))))).lookup (d := jasminTileMem) _) = _
      rw [lookup_memVar, lookup_inrHom]
      exact hr)
    o1
    (by
      rw [hvAppend_tileMem, lookupArgs_memArgs]
      exact lookupArgs_tabVars _ cs _ o1 (fun t x => lookup_prefVar _ x o1))
  have hrem : Option.Rel
      (fun r r' => r.1 = unmapInl (d := jasminDialect) (e := tileDialect) r'.1 ∧ r.2 = r'.2)
      (forIterLeak
        (fun i a => NFProg.leakRunM M fuel body
          (hvAppend a (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 i))))
        ((List.range (N % 2 ^ l)).map (N / 2 ^ l * 2 ^ l + ·))
        (unmapInl (d := jasminDialect) (e := tileDialect) o1))
      (forIterLeak (d := jasminTileDialect)
        (fun j a' => scalarTileLeakRun jasminDialect
          (instDialectDenoteMOptionOfPure jasminDialect) M fuel
          (incl body (remRen cs (loopRen Γ)))
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
            (hvAppend (d := jasminTileDialect) a'
              (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
                (hvAppend (d := jasminTileDialect) o1 (loopVal W qv qLv rv))
                (BitVec.ofNat 64 j)))
            (qLv + BitVec.ofNat 64 j)))
        (List.range (N % 2 ^ l)) o1) := by
    rw [forIterLeak_map]
    refine NFProg.forIterLeak_rel_bisim
      (R := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
      (List.range (N % 2 ^ l)) (fun j _ a a' haa => ?_)
      (unmapInl (d := jasminDialect) (e := tileDialect) o1) o1 rfl
    subst haa
    refine incl_leakRun M fuel body (remRen cs (loopRen Γ)) _ _
      (RenRel.split cs _ _ _ (fun t x => lookup_prefVar _ x a')
        (RenRel.head (s := JasminTy.reg 64) (BitVec.ofNat 64 (N / 2 ^ l * 2 ^ l + j)) ?_
          (fun t v => ?_)))
    · show qLv + BitVec.ofNat 64 j = _
      rw [hqL, BitVec.ofNat_add]
    · show (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
        (Var.there (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
          (loopRen Γ t v)))).lookup
        (hvAppend (d := jasminTileDialect) a'
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
            (hvAppend (d := jasminTileDialect) o1 (loopVal W qv qLv rv))
            (BitVec.ofNat 64 j))) = _
      rw [lookup_inrHom]
      exact (lookup_inrHom (loopVal W qv qLv rv) o1 _).trans (hren t v)
  have hk : ∀ (a' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))),
      Option.Rel
        (fun r r' => r.1 = unmapInl (d := jasminDialect) (e := tileDialect) r'.1 ∧ r.2 = r'.2)
        (NFProg.leakRunM M fuel k
          (hvAppend (unmapInl (d := jasminDialect) (e := tileDialect) a') V))
        (NFProg.leakRunM (tileMemLeak jasminDialect M) fuel
          (embed jasminDialect (incl k (contRen cs (loopRen Γ))))
          (hvAppend (d := jasminTileMem) a'
            (hvAppend (d := jasminTileMem) o1 (loopVal W qv qLv rv)))) := by
    intro a'
    have e : NFProg.leakRunM (tileMemLeak jasminDialect M) fuel
        (embed jasminDialect (incl k (contRen cs (loopRen Γ))))
        (hvAppend (d := jasminTileMem) a'
          (hvAppend (d := jasminTileMem) o1 (loopVal W qv qLv rv))) =
        scalarTileLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel
          (incl k (contRen cs (loopRen Γ)))
          (hvAppend (d := jasminTileDialect) a'
            (hvAppend (d := jasminTileDialect) o1 (loopVal W qv qLv rv))) := by
      rw [hvAppend_tileMem, hvAppend_tileMem]
      exact embed_leakRunM jasminDialect _ M fuel _ _
    rw [e]
    refine incl_leakRun M fuel k (contRen cs (loopRen Γ)) _ _
      (RenRel.split cs _ _ _ (fun t x => lookup_prefVar _ x a') (fun t v => ?_))
    show (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
      (inrHom (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))
        (loopRen Γ t v))).lookup
      (hvAppend (d := jasminTileDialect) a'
        (hvAppend (d := jasminTileDialect) o1 (loopVal W qv qLv rv))) = _
    rw [lookup_inrHom, lookup_inrHom]
    exact hren t v
  unfold stripLoops
  rw [hsrc]
  show Option.Rel _ _ (NFProg.leakRunM (tileMemLeak jasminDialect M) fuel _ _)
  rw [htgt, hrange, forIterLeak_append, hmain, forIterLeak_tileMem, hmain']
  simp only [Option.bind_some]
  rw [htgt2, forIterLeak_tileMem]
  refine strip_assemble _ _ hrem
    (fun a => NFProg.leakRunM M fuel k (hvAppend a V))
    (fun a' => NFProg.leakRunM (tileMemLeak jasminDialect M) fuel
      (embed jasminDialect (incl k (contRen cs (loopRen Γ))))
      (hvAppend (d := jasminTileMem) a'
        (hvAppend (d := jasminTileMem) o1 (loopVal W qv qLv rv))))
    hk Em E' N (N / 2 ^ l) (N % 2 ^ l) (stripEv (2 ^ l) (evCount M body)) (fun rest => ?_)
  show CTLeak.trip (N / 2 ^ l) ::
    (pickBlocks (2 ^ l) (evCount M body) (N / 2 ^ l) (Em ++ rest) ++
      CTLeak.trip (N % 2 ^ l) :: (Em ++ rest).drop (N / 2 ^ l * (2 ^ l * evCount M body))) = _
  rw [hpick rest, List.drop_left' hlenm]

/-- The number of events of one iteration of a counted loop with a straight-line body. -/
def iterEvents (M : LeakModel jasminDialect) : NFProg jasminDialect Γ ts → Nat
  | .forLoop _ _ body _ => evCount M body
  | _ => 0

theorem rel_events {A A' : Type} {R : A → A' → Prop} {f : List CTLeak → List CTLeak}
    {o : Option (A × List CTLeak)} {o' : Option (A' × List CTLeak)}
    (h : Option.Rel (fun a a' => R a.1 a'.1 ∧ a'.2 = f a.2) o o') :
    o'.map Prod.snd = (o.map Prod.snd).map f := by
  cases h with
  | none => rfl
  | some hr => exact congrArg some hr.2

theorem rel_results {A A' : Type} {T : A' → A} {f : List CTLeak → List CTLeak}
    {o : Option (A × List CTLeak)} {o' : Option (A' × List CTLeak)}
    (h : Option.Rel (fun a a' => a.1 = T a'.1 ∧ a'.2 = f a.2) o o') :
    (o'.map Prod.fst).map T = o.map Prod.fst := by
  cases h with
  | none => rfl
  | some hr => exact congrArg some hr.1.symm

/-- **Strip-mining preserves runs.** For a program `stripMine` accepts, a leakage model in
    which the lifted operations and the added index operations are quiet and a load and a
    store emit their index, and a valuation `W` of the target context: the run of the program
    on the scalar reading of `W` and the run of the strip-mined program on `W` both fail, or
    both succeed with the same results, and the events of the strip-mined program are
    `stripEv` of the events of the program. -/
theorem stripMine_leakRun (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (hA : ArrAddr M)
    (hI : IdxQuiet l M) (fuel : Nat) (p : NFProg jasminDialect Γ ts)
    (q : NFProg jasminTileMem (Γ.map (Sum.inl (β := TileTy)))
      (ts.map (Sum.inl (β := TileTy))))
    (h : stripMine l w p = some q)
    (W : Valuation (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy)))) :
    Option.Rel
      (fun a a' => a.1 = unmapInl (d := jasminDialect) (e := tileDialect) a'.1 ∧
        a'.2 = stripEv (2 ^ l) (iterEvents M p) a.2)
      (NFProg.leakRunM M fuel p (unmapInl (d := jasminDialect) (e := tileDialect) W))
      (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel q
        W) := by
  have hl : l < 64 := by
    by_contra hl
    simp only [stripMine, hl, ite_false, reduceCtorEq] at h
  simp only [stripMine, hl, ite_true] at h
  obtain ⟨E, -, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨cs, count, inits, body, k, vbody, rfl, hv⟩ := E
  have hc : (memVar (inlVar count)).lookup (d := jasminTileMem) W =
      count.lookup (unmapInl (d := jasminDialect) (e := tileDialect) W) :=
    (lookup_memVar _ W).trans (lookup_inlVar count W)
  obtain ⟨cnt, hcnt⟩ : ∃ cnt : BitVec 64,
      count.lookup (unmapInl (d := jasminDialect) (e := tileDialect) W) = cnt := ⟨_, rfl⟩
  rw [hcnt] at hc
  have hlt : cnt.toNat < 2 ^ 64 := cnt.isLt
  have hle : cnt.toNat / 2 ^ l * 2 ^ l ≤ cnt.toNat := Nat.div_mul_le_self _ _
  have hX1 : (cnt >>> l).toNat = cnt.toNat / 2 ^ l := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hX2 : (cnt >>> l) <<< l = BitVec.ofNat 64 (cnt.toNat / 2 ^ l * 2 ^ l) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, hX1, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have ht : (BitVec.ofNat 64 (cnt.toNat / 2 ^ l * 2 ^ l)).toNat = cnt.toNat / 2 ^ l * 2 ^ l := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hlt)
  have hX3 : (cnt - (cnt >>> l) <<< l).toNat = cnt.toNat % 2 ^ l := by
    rw [hX2, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [ht]; exact hle)), ht]
    have h3 := Nat.div_add_mod' cnt.toNat (2 ^ l)
    omega
  show Option.Rel _ _ (tileMemLeakRun jasminDialect _ M fuel
    (.var (opE (.shrImm 64 l) (.cons (memVar (inlVar count)) .nil))
      (.var (opE (.shlImm 64 l) (.cons .here .nil))
        (.var (opE (.regArith .sub 64)
          (.cons (.there (.there (memVar (inlVar count)))) (.cons .here .nil)))
          (stripLoops l cs inits body k vbody)))) W)
  rw [leakRun_opE _ _ _ _ _ _ hI.1, leakRun_opE _ _ _ _ _ _ hI.2.1,
    leakRun_opE _ _ _ _ _ _ hI.2.2.1]
  refine loops_run M hM hA hI hl fuel cs count inits body k vbody hv W _ rfl cnt.toNat
    (congrArg BitVec.toNat hcnt) _ _ _ ?_ ?_ ?_
  · show (BitVec.ushiftRight (Var.lookup (d := jasminTileMem) (memVar (inlVar count)) W)
      (shiftMask 64 l)).toNat = _
    rw [hc, shiftMask_of_lt hl]
    exact hX1
  · show BitVec.shiftLeft
      (BitVec.ushiftRight (Var.lookup (d := jasminTileMem) (memVar (inlVar count)) W)
        (shiftMask 64 l)) (shiftMask 64 l) = _
    rw [hc, shiftMask_of_lt hl]
    exact hX2
  · show (BitVec.sub (Var.lookup (d := jasminTileMem) (memVar (inlVar count)) W)
      (BitVec.shiftLeft
        (BitVec.ushiftRight (Var.lookup (d := jasminTileMem) (memVar (inlVar count)) W)
          (shiftMask 64 l))
        (shiftMask 64 l))).toNat = _
    rw [hc, shiftMask_of_lt hl]
    exact hX3

/-- **The events of a strip-mined run** are `stripEv` of the events of the scalar run. -/
theorem stripMine_events (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (hA : ArrAddr M)
    (hI : IdxQuiet l M) (fuel : Nat) (p : NFProg jasminDialect Γ ts)
    (q : NFProg jasminTileMem (Γ.map (Sum.inl (β := TileTy)))
      (ts.map (Sum.inl (β := TileTy))))
    (h : stripMine l w p = some q)
    (W : Valuation (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy)))) :
    (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel q
        W).map Prod.snd =
      ((NFProg.leakRunM M fuel p
        (unmapInl (d := jasminDialect) (e := tileDialect) W)).map Prod.snd).map
        (stripEv (2 ^ l) (iterEvents M p)) :=
  rel_events (R := fun a a' => a = unmapInl (d := jasminDialect) (e := tileDialect) a')
    (stripMine_leakRun M hM hA hI fuel p q h W)

/-- The leakage model of `jasminDialect` in which a load and a store emit their index and
    every other operation is quiet. -/
def addrModel : LeakModel jasminDialect where
  kind
    | .stackLoad _ _ => .addrAt 1
    | .stackStore _ _ => .addrAt 1
    | _ => .quiet
  valNat := fun _ _ => 0

theorem addrModel_laneQuiet (w : Nat) : LaneQuiet w addrModel := by
  intro op h
  cases op <;> first | rfl | cases h

theorem addrModel_arrAddr : ArrAddr addrModel := fun _ _ => ⟨rfl, rfl⟩

theorem addrModel_idxQuiet (l : Nat) : IdxQuiet l addrModel := ⟨rfl, rfl, rfl, rfl⟩

/-- **Strip-mining preserves the denotation.** The scalar reading of the denotation of the
    strip-mined program on a valuation `W` is the denotation of the program on the scalar
    reading of `W`, at every fuel. -/
theorem stripMine_denote (fuel : Nat) (p : NFProg jasminDialect Γ ts)
    (q : NFProg jasminTileMem (Γ.map (Sum.inl (β := TileTy)))
      (ts.map (Sum.inl (β := TileTy))))
    (h : stripMine l w p = some q)
    (W : Valuation (d := jasminTileDialect) (Γ.map (Sum.inl (β := TileTy)))) :
    (tileMemDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) fuel q W).map
        (unmapInl (d := jasminDialect) (e := tileDialect)) =
      p.denote fuel (unmapInl (d := jasminDialect) (e := tileDialect) W) := by
  have h1 := stripMine_leakRun addrModel (addrModel_laneQuiet w) addrModel_arrAddr
    (addrModel_idxQuiet l) fuel p q h W
  have hs := NFProg.leakRunM_fst addrModel fuel p
    (unmapInl (d := jasminDialect) (e := tileDialect) W)
  have ht := NFProg.leakRunM_fst (tileMemLeak jasminDialect addrModel) fuel q W
  change _ = p.denote fuel _ at hs
  change _ = tileMemDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect)
    fuel q W at ht
  rw [← hs, ← ht]
  exact rel_results h1

/-! ## 7. The certificates -/

/-- The semantics of programs of `jasminTileMem` at the fuel `fuel`. -/
def memSem (fuel : Nat) (Δ : Ctxt jasminTileMem) (ts : List jasminTileMem.Ty) :
    PassChain.Sem (NFProg jasminTileMem Δ ts) where
  In := Valuation (d := jasminTileMem) Δ
  Out := Valuation (d := jasminTileMem) ts
  den := fun (q : NFProg jasminTileMem Δ ts) (W : Valuation (d := jasminTileMem) Δ) =>
    tileMemDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) fuel q W

/-- The leak semantics of programs of `jasminTileMem` at the model
    `tileMemLeak jasminDialect M`. -/
def memLeakSem (M : LeakModel jasminDialect) (fuel : Nat) (Δ : Ctxt jasminTileMem)
    (ts : List jasminTileMem.Ty) : PassChain.LeakSem (NFProg jasminTileMem Δ ts) where
  In := Valuation (d := jasminTileMem) Δ
  Ev := CTLeak
  leak q W := (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect)
    M fuel q W).map Prod.snd

open PassChain in
/-- **The certificate of strip-mining.** The step `stripMine l w` from the semantics
    `NFProg.denote fuel` of scalar programs to that of programs of `jasminTileMem`: the input
    relation holds of a scalar valuation and a target valuation when the first is the scalar
    reading of the second, and the output relation likewise of the result tuples. -/
def stripMineCert (l w fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (stripMine l w (Γ := Γ) (ts := ts)) (scalarSem fuel Γ ts)
      (memSem fuel (Γ.map (Sum.inl (β := TileTy))) (ts.map (Sum.inl (β := TileTy)))) where
  relIn V W := V = unmapInl (d := jasminDialect) (e := tileDialect) W
  relOut o o' := o = unmapInl (d := jasminDialect) (e := tileDialect) o'
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    have h1 := stripMine_denote fuel p q hf W
    rw [show p.denote fuel (unmapInl (d := jasminDialect) (e := tileDialect) W) = some o
      from hd] at h1
    obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.mp h1
    exact ⟨o', ho', rfl⟩

open PassChain in
/-- **The leakage certificate of strip-mining.** Between the two-run semantics of the two
    leak semantics: the input relation holds when each scalar valuation is the scalar reading
    of the target valuation, and the output relation holds of two pairs of event lists when,
    for one count `c` of events per iteration, each target list is `stripEv (2 ^ l) c` of the
    scalar list. -/
def stripMineLeakCert (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (hA : ArrAddr M)
    (hI : IdxQuiet l M) (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (stripMine l w (Γ := Γ) (ts := ts)) (scalarLeakSem M fuel Γ ts).twoRun
      (memLeakSem M fuel (Γ.map (Sum.inl (β := TileTy)))
        (ts.map (Sum.inl (β := TileTy)))).twoRun where
  relIn V W := V.1 = unmapInl (d := jasminDialect) (e := tileDialect) W.1 ∧
    V.2 = unmapInl (d := jasminDialect) (e := tileDialect) W.2
  relOut a b := ∃ c : Nat, b = (stripEv (2 ^ l) c a.1, stripEv (2 ^ l) c a.2)
  sound := by
    intro p q V W o hf hVW hd
    obtain ⟨V1, V2⟩ := V
    obtain ⟨W1, W2⟩ := W
    obtain ⟨h1, h2⟩ := hVW
    dsimp only at h1 h2
    subst h1 h2
    obtain ⟨hd1, hd2⟩ := (scalarLeakSem M fuel Γ ts).twoRun_den_eq_some hd
    have e1 := stripMine_events M hM hA hI fuel p q hf W1
    have e2 := stripMine_events M hM hA hI fuel p q hf W2
    refine ⟨(stripEv (2 ^ l) (iterEvents M p) o.1, stripEv (2 ^ l) (iterEvents M p) o.2),
      (memLeakSem M fuel _ _).twoRun_den q W1 W2 _ _ ?_ ?_, iterEvents M p, rfl⟩
    · show Option.map Prod.snd _ = _
      rw [e1]
      show Option.map _ ((scalarLeakSem M fuel Γ ts).leak p _) = _
      rw [hd1]
      rfl
    · show Option.map Prod.snd _ = _
      rw [e2]
      show Option.map _ ((scalarLeakSem M fuel Γ ts).leak p _) = _
      rw [hd2]
      rfl

/-- The output relation of `stripMineLeakCert` implies the constant-time relation. -/
theorem stripMineLeakCert_ct (M : LeakModel jasminDialect) (hM : LaneQuiet w M)
    (hA : ArrAddr M) (hI : IdxQuiet l M) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) :
    ∀ a b, (stripMineLeakCert M hM hA hI fuel Γ ts).relOut a b → PassChain.ctRel a b := by
  rintro a b ⟨c, rfl⟩ hab
  show stripEv (2 ^ l) c a.1 = stripEv (2 ^ l) c a.2
  rw [hab]

end Main

end CatCrypt.Crypto.SecureCompilation.VIR.LaneStrip
