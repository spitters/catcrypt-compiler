/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectCondDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectCondDenote


@[expose] public section
set_option autoImplicit false

/-!
# Unifying the five control-fragment coverages: one nesting predicate + one denote

The control-fragment coverage now spans five whole-program denote sidecars, each
proved SEPARATELY against `semScalar`/`translateDialectControl_denote_ctl`:

* `translateDialectControl_denote_ctl` — the base `IsCoveredSCtl` (straight-line
  + `RFor` + `RIfNz`-φ);
* `transCtlSeq_denote_seq` (`IsCoveredSCtlSeq`) — control-level `RSeq`, but only
  over `IsCoveredSCtl` children;
* `rWhileNz_whole_denote` (`IsCoveredSWhile`) — a data-dependent `RWhileNz` over
  an `IsCoveredSCtl` body;
* `rCond_whole_denote` (`IsCoveredSCond`) — a guarded do-once `RIfNz … RSkip`
  over an `IsCoveredSCtl` block.

These are FIVE separate predicates, and none nests inside another: `IsCoveredSCtlSeq`'s
`RSeq` only accepts `IsCoveredSCtl` children (not `RCond`/`RWhileNz`), and the
`while`/`cond` predicates are single-node. So a program that **sequences** a
guarded conditional, another conditional, and a runtime loop — the Plonky3
`DuplexChallenger` query sampler — sits OUTSIDE any single one of the five (it is
an `RSeq` whose children are `RCond`/`RWhileNz`, exactly what `IsCoveredSCtlSeq`
forbids).

This module unifies them:

* `IsCoveredSU` — one predicate closed under `{IsCoveredSCtl leaf, RSeq, RBlock,
  RCond (over an `IsCoveredSCtl` block), RWhileNz (over an `IsCoveredSCtl` body),
  RFor (over ANY `IsCoveredSU` body)}`.  Crucially the `RSeq`/`RBlock` closure
  accepts ANY `IsCoveredSU` children, so a sequence of conditionals and loops is
  covered — the closure `IsCoveredSCtlSeq` lacks — and the `rFor` closure descends
  its body through the unified engine, so a counted phase may contain a
  data-dependent `RWhileNz` sweep (MAYO's echelon shape).  Every closure —
  `rSeq`/`rBlock`/`rFor`/`rCond`/`rWhile` — now nests ANY `IsCoveredSU` body: the
  `rCond`/`rWhile` bodies were lifted from `IsCoveredSCtl` to full `IsCoveredSU`
  via the env-threaded `condSkipDEnv_denote`/`loopWhileDEnv`, so ALL shapes nest
  ALL shapes and `IsCoveredSU` is the complete nesting keystone
  (`RWhileNz`-over-`RWhileNz`, `RCond`-over-`RSeq`, …).
* `semU fuel` — the unified whole-program waist model. It is `semScalar` on the
  leaves, `bind` on `RSeq`, `semScalarCond` on the guarded conditional (NOT the
  φ-merge — the guarded block runs iff the guard holds), and `semScalarWhile
  fuel` on the runtime loop. The fuel bounds `while` termination.
* `transU fuel vm env` — the unified front descent, env-threaded (the guarded
  conditional selects its descent by the run-time guard value `guardNz name env`,
  the loop by the run-time trip count `scalarWhileTrips … fuel env`, and `RSeq`
  threads the intermediate env through `semU`). On the leaves it is
  `translateDialectControl`.
* `transU_denote` — the unified homomorphism, by induction on `IsCoveredSU`. It
  COMPOSES the landed lemmas: `translateDialectControl_denote_ctl` on the
  leaf, the `ComCont.comp` fold (the `transCtlSeq_denote_seq` `RSeq` pattern,
  re-applied over `semU`'s `bind`) on `RSeq`, `condSkipDEnv_denote` on the guarded
  conditional (with the coverage IH as the block homomorphism, so the block is any
  `IsCoveredSU` shape), and `loopWhileDEnv_denote` on the runtime loop (the
  env-threaded trip-index fold, with the coverage IH as the body homomorphism, so
  the loop body is any `IsCoveredSU` shape — a nested `RWhileNz` included).

`IsCoveredSU` is ADDITIVE: `IsCoveredSCtl`, `IsCoveredSCtlSeq`, `IsCoveredSWhile`,
`IsCoveredSCond` are all untouched, so their existing `*Covered` consumers keep
building.

## The guard model (a residual sub-wall the unification exposes)

The guard on the unified conditional/loop is `guardNz name` — "the bound word
`name` is nonzero". That covers the loop trip counter (`counter != 0` countdown)
and a boolean-flag conditional, but NOT the sampler's literal `inlen == 8` or the
disjunctive `inlen > 0 || outlen == 0` triggers: those need an equality/OR word
op the `SExpr` alphabet lacks (it carries `SLt` only). Modeling them as
`guardNz g` for a precomputed flag `g` requires an `SExpr` `==`/`||`. This is the
named residual — the unification and the sampler's `RSeq`-of-`RCond`/`RWhileNz`
CONTROL shape are delivered; the exact trigger predicates are the follow-on
`SExpr`-op gap.

**0 sorries; no axioms beyond the front's existing set.**
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The unified guard, semantics, and front descent -/

/-- The unified guard predicate: the bound word `name` is nonzero on the env
    (the `RWhileNz`/guarded-`RIfNz` `name != 0` guard, the same shape the landed
    `while`/`cond` witnesses use). -/
def guardNz (name : String) : SEnvScalar → Bool :=
  fun e => decide ((envReadU64 e name).getD 0 ≠ 0)

/-- Syntactic marker for the five combinator shapes `semU`/`transU` special-case
    (`RSeq`, `RBlock`, guarded `RIfNz … RSkip`, `RWhileNz`, and the rolled `RFor`).
    `IsCoveredSU.ofCtl` excludes these so an `IsCoveredSCtl` leaf routes to the
    `semScalar`/`translateDialectControl` fallback — never to the guarded
    `semScalarCond` (which is a DIFFERENT model: the leaf `RIfNz` is a φ-merge, the
    combinator `RIfNz … RSkip` is a genuine forward branch).  `RFor` is seq-like so
    the `rFor` closure descends its body through the unified engine (`semU`/`transU`
    per trip), opening a body that is itself `RWhileNz`/`RCond`/nested `RFor` —
    which the `ofCtl` leaf's `IsCoveredSCtl`-`RFor` cannot. -/
def isSeqLike : LowCT → Bool
  | .RSeq _ _ => true
  | .RBlock _ => true
  | .RIfNz _ _ .RSkip => true
  | .RWhileNz _ _ => true
  | .RFor _ _ _ => true
  | _ => false

/-- **The unified whole-program waist model.** `semScalar` on the leaves; `bind`
    on `RSeq`; `semScalarCond` (guarded do-once, NOT the φ-merge) on the guarded
    conditional; `semScalarWhile fuel` (fuel-bounded do-while) on the runtime
    loop.  The fuel bounds `while` termination. -/
def semU (fuel : Nat) : LowCT → SEnvScalar → Option SEnvScalar
  | .RSeq c₁ c₂, env => (semU fuel c₁ env).bind (fun e => semU fuel c₂ e)
  | .RBlock body, env => semU fuel body env
  | .RIfNz name thenBlk .RSkip, env =>
      semScalarCond (fun e => semU fuel thenBlk e) (guardNz name) env
  | .RWhileNz name body, env =>
      semScalarWhile (fun e => semU fuel body e) (guardNz name) fuel env
  | .RFor x N body, env =>
      semRForD (fun e => semU fuel body e) x N env
  | c, env => semScalar c env

/-- **The env-threaded counted-loop front** — the `loopRForD` twin that re-descends
    the body per trip through an *env-dependent* body translator `transBody`,
    threading the per-trip env through `semBody` (`semRForD`).  Because `loopRForD`
    reuses ONE env-independent body translation per trip, it cannot descend a body
    whose front depends on the run-time env (a data-dependent `RWhileNz` sweep
    whose unroll depth is the run-time trip count).  This twin passes the per-trip
    env `envPre.upd x n` into `transBody`, so each trip's descent is selected by
    that trip's env — the price is the meta-unroll's `N` body copies (as in
    `loopRForD`), not one rolled back-edge.  Per trip it binds the counter `x := n`
    (`bvConst`), exactly as `loopRForD`. -/
def loopRForDEnv {Γ : Ctx} (x : String)
    (transBody : ∀ {Γ'' : Ctx}, VarMap Γ'' → SEnvScalar → Option (DTransOut Γ''))
    (semBody : SEnvScalar → Option SEnvScalar)
    (vm : VarMap Γ) (env : SEnvScalar) :
    Nat → Option (DTransOut Γ)
  | 0 => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | n + 1 =>
      match loopRForDEnv x transBody semBody vm env n, semRForD semBody x n env with
      | some oPre, some envPre =>
          let eSet : Expr catCryptDialect oPre.Γ' (.sword 64) :=
            { op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil }
          match transBody (oPre.vm.bind x)
              (envPre.upd x (t := .sword 64) (BitVec.ofNat 64 n)) with
          | none => none
          | some oBody =>
              some { Γ' := oBody.Γ'
                     cont := ComCont.comp oPre.cont
                       (ComCont.comp (ComCont.varBind eSet) oBody.cont)
                     vm := oBody.vm }
      | _, _ => none

/-- **The env-threaded runtime-loop front** — the `loopWhileD` twin that
    re-descends the `while` body per trip through an *env-dependent* body
    translator `transBody`, threading the per-trip env through `semBody`
    (`semWhileIter`).  This is the exact `loopRForDEnv` technique applied to the
    data-dependent loop: `loopWhileD` reuses ONE env-independent body translation
    per trip and so cannot descend a body whose front depends on the run-time env
    (a body that is itself an `RWhileNz`/`RCond`/nested `RFor`), whereas this twin
    passes the per-trip env `semWhileIter semBody n env` into `transBody`, so each
    trip's descent is selected by that trip's env.  Unlike `loopRForDEnv` there is
    NO per-trip counter const bind (the `while` body reads/decrements its own
    counter). -/
def loopWhileDEnv {Γ : Ctx}
    (transBody : ∀ {Γ'' : Ctx}, VarMap Γ'' → SEnvScalar → Option (DTransOut Γ''))
    (semBody : SEnvScalar → Option SEnvScalar)
    (vm : VarMap Γ) (env : SEnvScalar) :
    Nat → Option (DTransOut Γ)
  | 0 => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | n + 1 =>
      match loopWhileDEnv transBody semBody vm env n, semWhileIter semBody n env with
      | some oPre, some envPre =>
          match transBody oPre.vm envPre with
          | none => none
          | some oBody =>
              some { Γ' := oBody.Γ'
                     cont := ComCont.comp oPre.cont oBody.cont
                     vm := oBody.vm }
      | _, _ => none

/-- **The unified front descent**, env-threaded.  On `RSeq` it composes the two
    child descents with `ComCont.comp`, threading the intermediate env through
    `semU`; on `RBlock` it passes through; on the guarded conditional it selects
    `condSkipD` by the run-time guard value `guardNz name env`; on the runtime
    loop it unrolls `loopWhileD` to the run-time trip count `scalarWhileTrips …
    fuel env`.  On the leaves it is `translateDialectControl`. -/
def transU (fuel : Nat) : {Γ : Ctx} → VarMap Γ → SEnvScalar → LowCT → Option (DTransOut Γ)
  | _, vm, env, .RSeq c₁ c₂ =>
      match transU fuel vm env c₁, semU fuel c₁ env with
      | some o₁, some env₁ =>
          match transU fuel o₁.vm env₁ c₂ with
          | some o₂ =>
              some { Γ' := o₂.Γ', cont := ComCont.comp o₁.cont o₂.cont, vm := o₂.vm }
          | none => none
      | _, _ => none
  | _, vm, env, .RBlock body => transU fuel vm env body
  | _, vm, env, .RIfNz name thenBlk .RSkip =>
      condSkipD (translateBody := fun vm' => transU fuel vm' env thenBlk)
        vm (guardNz name env)
  | _, vm, env, .RWhileNz name body =>
      loopWhileDEnv (fun vm' e => transU fuel vm' e body)
        (fun e => semU fuel body e) vm env
        (scalarWhileTrips (fun e => semU fuel body e) (guardNz name) fuel env)
  | _, vm, env, .RFor x N body =>
      loopRForDEnv x (fun vm' e => transU fuel vm' e body)
        (fun e => semU fuel body e) vm env N
  | _, vm, _env, c => translateDialectControl vm c

/-! ## 2. The unified coverage predicate -/

/-- **The unified control-coverage predicate.** Closed under the `IsCoveredSCtl`
    leaf (straight-line/`RFor`/`RIfNz`-φ), `RSeq`, `RBlock`, the guarded
    conditional (`RIfNz name thenBlk RSkip` over ANY `IsCoveredSU` block), the
    runtime loop (`RWhileNz name body` over ANY `IsCoveredSU` body), and the
    counted loop (`RFor x N body` over ANY `IsCoveredSU` body).  Unlike
    `IsCoveredSCtlSeq`, the `RSeq`/`RBlock` closure accepts ANY `IsCoveredSU`
    children — a sequence of conditionals and loops.  Unlike the `ofCtl` leaf's
    `IsCoveredSCtl`-`RFor` (whose body is straight-line/`RFor`/`RIfNz`-φ only), the
    `rFor` closure descends its body through the unified engine per trip, so the
    body may itself be an `RWhileNz`/`RCond`/nested `RFor` — the counted phase
    containing a data-dependent inner sweep (MAYO's echelon shape).  EVERY closure
    — `rSeq`/`rBlock`/`rFor`/`rCond`/`rWhile` — nests ANY `IsCoveredSU` body (the
    `rCond`/`rWhile` bodies lifted from `IsCoveredSCtl` to `IsCoveredSU` via the
    env-threaded `condSkipDEnv_denote`/`loopWhileDEnv`), so ALL shapes nest ALL
    shapes.  The `ofCtl` leaf is guarded
    `notSeqLike` so a leaf routes to the `semScalar` model, never the guarded
    `semScalarCond`. -/
inductive IsCoveredSU : LowCT → Prop
  | ofCtl {c : LowCT} : IsCoveredSCtl c → isSeqLike c = false → IsCoveredSU c
  | rSeq {c₁ c₂ : LowCT} :
      IsCoveredSU c₁ → IsCoveredSU c₂ → IsCoveredSU (.RSeq c₁ c₂)
  | rBlock {body : LowCT} : IsCoveredSU body → IsCoveredSU (.RBlock body)
  | rCond {name : String} {thenBlk : LowCT} :
      IsCoveredSU thenBlk → IsCoveredSU (.RIfNz name thenBlk .RSkip)
  | rWhile {name : String} {body : LowCT} :
      IsCoveredSU body → IsCoveredSU (.RWhileNz name body)
  | rFor {x : String} {N : Nat} {body : LowCT} :
      IsCoveredSU body → IsCoveredSU (.RFor x N body)

/-! ## 3. Leaf reduction lemmas (`ofCtl` routes to the `semScalar` model) -/

/-- On a `notSeqLike` node, the unified semantics is `semScalar` (the leaf
    fallback). -/
theorem semU_leaf (fuel : Nat) (env : SEnvScalar) {c : LowCT}
    (h : isSeqLike c = false) : semU fuel c env = semScalar c env := by
  unfold semU
  split <;> first | rfl | simp [isSeqLike] at h

/-- On a `notSeqLike` node, the unified front descent is `translateDialectControl`
    (the leaf fallback). -/
theorem transU_leaf (fuel : Nat) {Γ : Ctx} (vm : VarMap Γ) (env : SEnvScalar)
    {c : LowCT} (h : isSeqLike c = false) :
    transU fuel vm env c = translateDialectControl vm c := by
  unfold transU
  split <;> first | rfl | simp [isSeqLike] at h

/-! ## 4. The unified homomorphism (the deliverable) -/

/-- **Trip-index denote for the counted `RFor` region over a unified body** (the
    `loopRForD_denote` twin, env-threaded).  The `N`-trip env-threaded front descent
    (`loopRForDEnv`) denotes exactly the `N`-fold body iteration (`semRForD` over
    `semU`), by `Nat`-induction on the trip count `N`.  Each `n+1`-trip prefix is
    (trips `0..n-1`) ∘ (counter bind `x := n`) ∘ (body descent at the trip-`n` env),
    composed via `ComCont.comp` — the `loopRForD_denote` fold with the body IH
    `ihBody` (over `transU`/`semU`) in place of the fixed `translateDialectControl`
    homomorphism.  The entry `Γ`/`vm`/`V`/`env` stay FIXED across the induction (the
    recursion peels the LAST trip); only the output `o`/`env'` generalise. -/
theorem loopRForDEnv_denote (fuel : Nat) (x : String) (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      transU fuel vm env body = some o →
      semU fuel body env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V') :
    ∀ (N : Nat) {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      loopRForDEnv x (fun vm' e => transU fuel vm' e body) (fun e => semU fuel body e)
        vm env N = some o →
      semRForD (fun e => semU fuel body e) x N env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro N
  induction N with
  | zero =>
      intro Γ vm V env env' o hc htr hsem
      simp only [loopRForDEnv] at htr
      simp only [semRForD] at hsem
      obtain rfl := Option.some.inj htr
      obtain rfl := Option.some.inj hsem
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | succ n ihN =>
      intro Γ vm V env env' o hc htr hsem
      simp only [loopRForDEnv] at htr
      simp only [semRForD] at hsem
      rcases hpre : loopRForDEnv x (fun vm' e => transU fuel vm' e body)
          (fun e => semU fuel body e) vm env n with _ | oPre
      · rw [hpre] at htr; simp at htr
      · simp only [hpre] at htr
        rcases hspre : semRForD (fun e => semU fuel body e) x n env with _ | envPre
        · rw [hspre] at hsem; simp at hsem
        · simp only [hspre] at htr hsem
          rcases hbt : transU fuel (oPre.vm.bind x)
              (envPre.upd x (t := .sword 64) (BitVec.ofNat 64 n)) body with _ | oBody
          · rw [hbt] at htr; simp at htr
          · simp only [hbt, Option.some.injEq] at htr
            obtain rfl := htr
            obtain ⟨VPre, hcPre, hcontPre⟩ := ihN vm V env envPre oPre hc hpre hspre
            obtain ⟨hconsSet, hcontSet⟩ :=
              scalar_step oPre.vm VPre envPre hcPre x
                ({ op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil } :
                  Expr catCryptDialect oPre.Γ' (.sword 64))
            obtain ⟨Vb, hcB, hcontB⟩ :=
              ihBody (oPre.vm.bind x) (VPre.extend _) _ env' oBody hconsSet hbt hsem
            refine ⟨Vb, hcB, ?_⟩
            intro t tail
            obtain ⟨comB, hcomB, hdenB⟩ := hcontB tail
            obtain ⟨comS, hcomS, hdenS⟩ := hcontSet comB
            obtain ⟨com, hcom, hden⟩ := hcontPre comS
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp oPre.cont
                (ComCont.comp (ComCont.varBind _) oBody.cont) tail = some com
              simp only [ComCont.comp, hcomB, hcomS, hcom]
            · rw [hden, hdenS, hdenB]

/-- **Trip-index denote for the runtime `RWhileNz` region over a unified body**
    (the `loopWhileD_denote` twin, env-threaded).  The `N`-trip env-threaded front
    descent (`loopWhileDEnv`) denotes exactly the `N`-fold body iteration
    (`semWhileIter` over `semU`), by `Nat`-induction on the trip count `N`.  Each
    `n+1`-trip prefix is (trips `0..n-1`) ∘ (body descent at the trip-`n` env),
    composed via `ComCont.comp` — the `loopWhileD_denote` fold with the body IH
    `ihBody` (over `transU`/`semU`) in place of the fixed `translateDialectControl`
    homomorphism, and — unlike `loopRForDEnv_denote` — with NO per-trip counter
    bind.  The entry `Γ`/`vm`/`V`/`env` stay FIXED across the induction (the
    recursion peels the LAST trip); only the output `o`/`env'` generalise. -/
theorem loopWhileDEnv_denote (fuel : Nat) (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      transU fuel vm env body = some o →
      semU fuel body env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V') :
    ∀ (N : Nat) {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      loopWhileDEnv (fun vm' e => transU fuel vm' e body) (fun e => semU fuel body e)
        vm env N = some o →
      semWhileIter (fun e => semU fuel body e) N env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro N
  induction N with
  | zero =>
      intro Γ vm V env env' o hc htr hsem
      simp only [loopWhileDEnv] at htr
      simp only [semWhileIter] at hsem
      obtain rfl := Option.some.inj htr
      obtain rfl := Option.some.inj hsem
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | succ n ihN =>
      intro Γ vm V env env' o hc htr hsem
      simp only [loopWhileDEnv] at htr
      simp only [semWhileIter] at hsem
      rcases hpre : loopWhileDEnv (fun vm' e => transU fuel vm' e body)
          (fun e => semU fuel body e) vm env n with _ | oPre
      · rw [hpre] at htr; simp at htr
      · simp only [hpre] at htr
        rcases hspre : semWhileIter (fun e => semU fuel body e) n env with _ | envPre
        · rw [hspre] at hsem; simp at hsem
        · simp only [hspre] at htr hsem
          rcases hbt : transU fuel oPre.vm envPre body with _ | oBody
          · rw [hbt] at htr; simp at htr
          · simp only [hbt, Option.some.injEq] at htr
            obtain rfl := htr
            obtain ⟨VPre, hcPre, hcontPre⟩ := ihN vm V env envPre oPre hc hpre hspre
            obtain ⟨Vb, hcB, hcontB⟩ := ihBody oPre.vm VPre envPre env' oBody hcPre hbt hsem
            refine ⟨Vb, hcB, ?_⟩
            intro t tail
            obtain ⟨comB, hcomB, hdenB⟩ := hcontB tail
            obtain ⟨com, hcom, hden⟩ := hcontPre comB
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp oPre.cont oBody.cont tail = some com
              simp only [ComCont.comp, hcomB, hcom]
            · rw [hden, hdenB]

/-- **Unified whole-program denote.** For any `IsCoveredSU`-covered body — the
    five landed control fragments unified and NESTED (a sequence of conditionals
    and loops included) — the `transU`-emitted `Com`-prefix denotes exactly the
    body's `semU` waist.  Induction on `IsCoveredSU` COMPOSES the five landed
    lemmas:

    * `ofCtl` → `translateDialectControl_denote_ctl` (after the leaf reductions);
    * `rSeq` → the `ComCont.comp` fold (the `transCtlSeq_denote_seq` `RSeq`
      pattern, re-applied over `semU`'s `bind`);
    * `rBlock` → the pass-through IH;
    * `rCond` → `condSkipDEnv_denote` (the guard-case fold, with the coverage IH as
      the block homomorphism, so the guarded block may itself be an `RSeq`/loop);
    * `rWhile` → `loopWhileDEnv_denote` (the env-threaded runtime-loop fold, with
      the coverage IH as the body homomorphism, so the loop body may itself be a
      nested `RWhileNz`);
    * `rFor` → `loopRForDEnv_denote` (the env-threaded counted-loop fold, with the
      coverage IH as the body homomorphism — so the counted phase's body may itself
      be a data-dependent `RWhileNz` sweep). -/
theorem transU_denote (fuel : Nat) {c : LowCT} (hcov : IsCoveredSU c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      transU fuel vm env c = some o →
      semU fuel c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  induction hcov with
  | @ofCtl c hs hns =>
      intro Γ vm V env env' o hc htr hsem
      rw [transU_leaf fuel vm env hns] at htr
      rw [semU_leaf fuel env hns] at hsem
      exact translateDialectControl_denote_ctl hs vm V env env' o hc htr hsem
  | @rSeq c₁ c₂ _ _ ih1 ih2 =>
      intro Γ vm V env env' o hc htr hsem
      rcases ht1 : transU fuel vm env c₁ with _ | o₁
      · simp [transU, ht1] at htr
      · rcases hs1 : semU fuel c₁ env with _ | env₁
        · simp [transU, ht1, hs1] at htr
        · rcases ht2 : transU fuel o₁.vm env₁ c₂ with _ | o₂
          · simp [transU, ht1, hs1, ht2] at htr
          · simp only [transU, ht1, hs1, ht2, Option.some.injEq] at htr
            obtain rfl := htr
            simp only [semU, hs1, Option.bind_some] at hsem
            obtain ⟨V₁, hc₁, hcont₁⟩ := ih1 vm V env env₁ o₁ hc ht1 hs1
            obtain ⟨V₂, hc₂, hcont₂⟩ := ih2 o₁.vm V₁ env₁ env' o₂ hc₁ ht2 hsem
            refine ⟨V₂, hc₂, ?_⟩
            intro t tail
            obtain ⟨com₂, hcom₂, hden₂⟩ := hcont₂ tail
            obtain ⟨com, hcom, hden⟩ := hcont₁ com₂
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp o₁.cont o₂.cont tail = some com
              simp only [ComCont.comp, hcom₂, hcom]
            · rw [hden, hden₂]
  | @rBlock body _ ih =>
      intro Γ vm V env env' o hc htr hsem
      simp only [transU] at htr
      simp only [semU] at hsem
      exact ih vm V env env' o hc htr hsem
  | @rCond name thenBlk _hcovBlk ih =>
      intro Γ vm V env env' o hc htr hsem
      simp only [transU] at htr
      simp only [semU] at hsem
      exact condSkipDEnv_denote (fun vm' => transU fuel vm' env thenBlk)
        (fun e => semU fuel thenBlk e) vm V env hc
        (fun env' o ht hs => ih vm V env env' o hc ht hs)
        (guardNz name env) env' o htr
        (by simpa only [semScalarCond] using hsem)
  | @rWhile name body _hcovBody ih =>
      intro Γ vm V env env' o hc htr hsem
      simp only [transU] at htr
      simp only [semU] at hsem
      exact loopWhileDEnv_denote fuel body
        (fun vm V env env' o hc ht hs => ih vm V env env' o hc ht hs)
        (scalarWhileTrips (fun e => semU fuel body e) (guardNz name) fuel env)
        vm V env env' o hc htr
        (semScalarWhile_eq_iter (fun e => semU fuel body e) (guardNz name) fuel env env' hsem)
  | @rFor x N body _hcovBody ih =>
      intro Γ vm V env env' o hc htr hsem
      simp only [transU] at htr
      simp only [semU] at hsem
      exact loopRForDEnv_denote fuel x body
        (fun vm V env env' o hc ht hs => ih vm V env env' o hc ht hs)
        N vm V env env' o hc htr hsem

/-! ## 5. Worked witnesses (past every single-fragment boundary) -/

/-- A guarded conditional followed by a runtime loop — `RSeq (RCond) (RWhileNz)` —
    is NOT expressible in any single one of the five landed fragments
    (`IsCoveredSCtlSeq`'s `RSeq` forbids `RCond`/`RWhileNz` children; the `while`
    and `cond` predicates are single-node), yet is covered here. -/
example (name₁ name₂ : String) (blk body : LowCT)
    (hblk : IsCoveredSCtl blk) (hblkS : isSeqLike blk = false)
    (hbody : IsCoveredSCtl body) (hbodyS : isSeqLike body = false) :
    IsCoveredSU (.RSeq (.RIfNz name₁ blk .RSkip) (.RWhileNz name₂ body)) :=
  .rSeq (.rCond (.ofCtl hblk hblkS)) (.rWhile (.ofCtl hbody hbodyS))

/-- A conditional whose guarded block calls a leaf and stores — the observe/sample
    trigger `if g then { call duplex; store }` — sequenced with a second
    conditional and a loop.  The three-way sequence of two conditionals and a loop
    (the query-sampler control skeleton) is covered. -/
example (g₁ g₂ ctr : String) :
    IsCoveredSU
      (.RSeq (.RIfNz g₁ (.RCall "duplex" ⟨"st", .TU64⟩ []) .RSkip)
        (.RSeq (.RIfNz g₂ (.RCall "duplex_n" ⟨"st", .TU64⟩ []) .RSkip)
          (.RWhileNz ctr (.RScalarSet "acc" 5)))) :=
  .rSeq (.rCond (.ofCtl (.ofStraight (.rCall _ _ _)) rfl))
    (.rSeq (.rCond (.ofCtl (.ofStraight (.rCall _ _ _)) rfl))
      (.rWhile (.ofCtl (.ofStraight (.rScalarSet "acc" 5)) rfl)))

/-- A counted `RFor` now descends its body through the unified engine (the `rFor`
    closure), so its body may itself be a data-dependent runtime loop — the shape
    the `ofCtl` leaf's `IsCoveredSCtl`-`RFor` (straight-line body only) cannot
    express.  `RFor "pcol" N (RWhileNz "r" body)` is the MAYO echelon phase with its
    inner sweep opened as a genuine `RWhileNz`. -/
example (x r : String) (N : Nat) (body : LowCT)
    (hbody : IsCoveredSCtl body) (hbodyS : isSeqLike body = false) :
    IsCoveredSU (.RFor x N (.RWhileNz r body)) :=
  .rFor (.rWhile (.ofCtl hbody hbodyS))

/-- A straight-line counted loop is still covered (now via the `rFor` closure over
    an `ofCtl` body). -/
example (x : String) (N : Nat) : IsCoveredSU (.RFor x N .RSkip) :=
  .rFor (.ofCtl (.ofStraight .rSkip) rfl)

/-! ### The `rCond`/`rWhile` bodies now nest ANY `IsCoveredSU` shape -/

/-- **`RWhileNz`-over-`RWhileNz` — a nested data-dependent loop.**  The `rWhile`
    body is itself an `RWhileNz` (a second runtime loop), which the previous
    `IsCoveredSCtl`-bodied `rWhile` could NOT express (an `RWhileNz` is not an
    `IsCoveredSCtl` node).  The env-threaded `loopWhileDEnv` re-descends the inner
    loop per outer trip with that trip's env, so the whole nest descends with a
    single `transU_denote`. -/
example (n₁ n₂ : String) (body : LowCT)
    (hbody : IsCoveredSCtl body) (hbodyS : isSeqLike body = false) :
    IsCoveredSU (.RWhileNz n₁ (.RWhileNz n₂ body)) :=
  .rWhile (.rWhile (.ofCtl hbody hbodyS))

/-- **`RCond`-over-`RSeq` — a conditional guarding a multi-statement block.**  The
    `rCond` block is an `RSeq` of two stores, which the previous
    `IsCoveredSCtl`-bodied `rCond` could NOT express (an `RSeq` is not an
    `IsCoveredSCtl` node).  When the guard holds the whole block runs; when it does
    not, NEITHER store fires (the `condSkipDEnv_denote` false leg is the identity). -/
example (g : String) :
    IsCoveredSU (.RIfNz g (.RSeq (.RScalarSet "a" 1) (.RScalarSet "b" 2)) .RSkip) :=
  .rCond (.rSeq (.ofCtl (.ofStraight (.rScalarSet "a" 1)) rfl)
                (.ofCtl (.ofStraight (.rScalarSet "b" 2)) rfl))

/-- Non-vacuity of the nested loop: a concrete `RWhileNz`-over-`RWhileNz` where the
    OUTER guard `o != 0` and the INNER body decrements a counter `c`.  The inner
    loop actually iterates (its trip count is read off the run), so the nest is not
    a degenerate zero-trip shape.  Here the inner loop runs `2` trips from `c = 2`. -/
example :
    scalarWhileTrips
      (fun e => some (SEnvScalar.upd e "c" (t := .sword 64)
        (((envReadU64 e "c").getD 0) - 1)))
      (fun e => decide ((envReadU64 e "c").getD 0 ≠ 0))
      10 (SEnvScalar.upd (fun _ => none) "c" (t := .sword 64) (2 : BitVec 64)) = 2 := by
  native_decide

/-- Non-vacuity of the guarded multi-statement block: when the guard `g != 0` is
    FALSE, `semScalarCond` over the `RSeq` block is the IDENTITY — NEITHER store
    fires (the φ-merge would run both regardless; the guarded do-once does not). -/
example :
    semScalarCond
      (fun e => semU 10 (.RSeq (.RScalarSet "a" 1) (.RScalarSet "b" 2)) e)
      (fun e => decide ((envReadU64 e "g").getD 0 ≠ 0))
      (SEnvScalar.upd (fun _ => none) "g" (t := .sword 64) (0 : BitVec 64))
      = some (SEnvScalar.upd (fun _ => none) "g" (t := .sword 64) (0 : BitVec 64)) :=
  semScalarCond_false _ _ _ (by native_decide)

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
