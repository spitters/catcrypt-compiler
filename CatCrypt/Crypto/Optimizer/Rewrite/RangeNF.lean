/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNFLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses

/-!
# The range stage over structured programs

The lifting of the range stage `ComPipeline.comRangeOpt` from straight-line programs
`Com jasminDialect` to structured programs `NFProg jasminDialect`.

`rangeGo A len p` is the traversal `ComPipeline.rangeCom` extended by the region
constructors. A let-binding is rewritten by `ComPipeline.rangeExpr` under the abstract
environment `A`, and its continuation is traversed under `A` extended by the abstract value
`ComPipeline.stageAbs` of the binding. A counted loop, a branch, an exit-flag loop and a call
are kept. Every variable a region binds enters the abstract environment at the full lane
range of its type with no fact (`topApp`): the carried tuple and the trip index in a loop
body, the final carried tuple, the branch results and the call results in a continuation.
The full lane range holds of every value, so the environment of a loop body holds at every
iteration and no fixpoint is computed. The arms of a branch are traversed under the
environment of the branch. Levels count from the bottom of the context, so the facts of `A`
stay valid under the variables a region binds (`envOK_topApp`).

On a program without regions the traversal is `rangeCom` (`rangeGo_ofCom`), so `rangeNF`
restricted to `NFProg.ofCom` is `comRangeOpt` (`rangeNF_ofCom`).

## Main definitions

* `topCons`, `topApp` — an abstract environment extended by variables at the full lane range.
* `rangeGo` — the traversal of a structured program.
* `rangeNF` — the stage: the traversal from the full lane range of every input.
* `rangeNFStep`, `rangeNFCert` — the chain step of the range stage, with the certificate
  that the output has the denotation of the input.

## Main results

* `rangeGo_denote`, `rangeNF_denote` — the stage preserves the `NFProg` denotation at every
  fuel.
* `rangeGo_ofCom`, `rangeNF_ofCom` — on an embedded straight-line program the stage is
  `comRangeOpt`.
* `rangeGo_ctRel`, `rangeNF_ctRel` — under a leakage model whose `regArith` operations are
  quiet, two runs of the input with equal events give two runs of the output with equal
  events.
* `rangeNF_nfCT` — under such a model the stage keeps `NFCT`.
* `ifFree_rangeGo`, `ifFree_rangeNF` — the stage keeps a program branch-free.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.RangeNF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

/-! ## 1. Abstract environments under a prefix of bound variables -/

/-- The abstract environment `A` extended by one variable at the full lane range of its
    type, with no fact. -/
def topCons (t : JasminTy) {Γ : JCtxt} (A : AEnv Γ) : AEnv (t :: Γ) :=
  HVector.cons (f := fun _ => AVal) (tyTop t, .none) A

/-- The abstract environment `A` extended by the prefix `cs` of variables, each at the full
    lane range of its type with no fact. -/
def topApp : (cs : List JasminTy) → {Γ : JCtxt} → AEnv Γ → AEnv (cs ++ Γ)
  | [], _, A => A
  | t :: cs, _, A => topCons t (topApp cs A)

/-- An environment that holds of `V` holds, extended by `topCons`, of every extension of
    `V` by one value. -/
theorem envOK_topCons {Γ : JCtxt} {A : AEnv Γ} {V : Ctxt.Valuation Γ} (hA : EnvOK A V)
    {t : JasminTy} (x : ⟦t⟧) : EnvOK (topCons t A) (V.extend x) :=
  hA.cons (valOK_top V t x)

/-- An environment that holds of `V` holds, extended by `topApp`, of every extension of `V`
    by a prefix. -/
theorem envOK_topApp : ∀ (cs : List JasminTy) {Γ : JCtxt} {A : AEnv Γ}
    (X : Ctxt.Valuation (d := jasminDialect) cs) {V : Ctxt.Valuation Γ}, EnvOK A V →
    EnvOK (topApp cs A) (hvAppend X V : Ctxt.Valuation (d := jasminDialect) (cs ++ Γ))
  | [], _, _, .nil, _, h => h
  | _ :: cs, _, _, .cons x X, _, h => envOK_topCons (Γ := cs ++ _) (envOK_topApp cs X h) x

/-! ## 2. The traversal -/

/-- The range traversal of a structured program from the abstract environment `A` of a
    context of length `len`: each let-binding as in `rangeCom`; each region kept, its bodies
    and its continuation traversed with the variables the region binds at the full lane
    range. -/
def rangeGo : {Γ : JCtxt} → {ts : List JasminTy} → AEnv Γ → Nat →
    NFProg jasminDialect Γ ts → NFProg jasminDialect Γ ts
  | _, _, _, _, .ret vs => .ret vs
  | _, _, A, len, .var e k =>
      .var (rangeExpr A len e)
        (rangeGo (HVector.cons (f := fun _ => AVal) (stageAbs A e len) A) (len + 1) k)
  | _, _, A, len, .forLoop (cs := cs) count inits body k =>
      .forLoop count inits
        (rangeGo (topApp cs (topCons (HasWord64.word (d := jasminDialect)) A))
          (cs.length + (len + 1)) body)
        (rangeGo (topApp cs A) (cs.length + len) k)
  | _, _, A, len, .ifThenElse (rs := rs) cond thn els k =>
      .ifThenElse cond (rangeGo A len thn) (rangeGo A len els)
        (rangeGo (topApp rs A) (rs.length + len) k)
  | _, _, A, len, .whileLoop (cs := cs) inits body k =>
      .whileLoop inits (rangeGo (topApp cs A) (cs.length + len) body)
        (rangeGo (topApp cs A) (cs.length + len) k)
  | _, _, A, len, .call (rs := rs) f args k =>
      .call f args (rangeGo (topApp rs A) (rs.length + len) k)

/-- The length of a context under a prefix. -/
theorem length_app {Γ : JCtxt} {len : Nat} (cs : List JasminTy) (hlen : len = Γ.length) :
    cs.length + len = (cs ++ Γ).length := by
  rw [hlen, List.length_append]

/-- The length of the context of a loop body. -/
theorem length_body {Γ : JCtxt} {len : Nat} (cs : List JasminTy) (t : JasminTy)
    (hlen : len = Γ.length) : cs.length + (len + 1) = (cs ++ t :: Γ).length := by
  rw [hlen, List.length_append, List.length_cons]

section Denote

variable [CallDenote jasminDialect]

/-- **Denotation of the traversal.** Under an environment that holds of `V`, the output
    denotes the input at `V`, at every fuel. -/
theorem rangeGo_denote (fuel : Nat) : ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ)
    (len : Nat) (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ), len = Γ.length →
    EnvOK A V → (rangeGo A len p).denote fuel V = p.denote fuel V
  | _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, A, len, .var e k, V, hlen, hA => by
      simp only [rangeGo, NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      rw [rangeExpr_denote hA hlen e]
      exact rangeGo_denote fuel _ (len + 1) k _ (by simp [hlen])
        (hA.cons (stageAbs_sound hA hlen e))
  | _, _, A, len, .forLoop (cs := cs) count inits body k, V, hlen, hA => by
      have hb : ∀ (acc : Ctxt.Valuation (d := jasminDialect) cs) (i : Nat),
          (rangeGo (topApp cs (topCons (HasWord64.word (d := jasminDialect)) A))
              (cs.length + (len + 1)) body).denote fuel
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) =
            body.denote fuel
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun acc i => rangeGo_denote fuel _ _ body _ (length_body cs _ hlen)
          (envOK_topApp cs acc (envOK_topCons hA _))
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          (rangeGo (topApp cs A) (cs.length + len) k).denote fuel (hvAppend acc V) =
            k.denote fuel (hvAppend acc V) :=
        fun acc => rangeGo_denote fuel _ _ k _ (length_app cs hlen) (envOK_topApp cs acc hA)
      simp only [rangeGo, NFProg.denote, hb, hk]
  | _, _, A, len, .ifThenElse (rs := rs) cond thn els k, V, hlen, hA => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          (rangeGo (topApp rs A) (rs.length + len) k).denote fuel (hvAppend r V) =
            k.denote fuel (hvAppend r V) :=
        fun r => rangeGo_denote fuel _ _ k _ (length_app rs hlen) (envOK_topApp rs r hA)
      simp only [rangeGo, NFProg.denote, hk, rangeGo_denote fuel A len thn V hlen hA,
        rangeGo_denote fuel A len els V hlen hA]
  | _, _, A, len, .whileLoop (cs := cs) inits body k, V, hlen, hA => by
      have hb : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          (rangeGo (topApp cs A) (cs.length + len) body).denote fuel (hvAppend acc V) =
            body.denote fuel (hvAppend acc V) :=
        fun acc => rangeGo_denote fuel _ _ body _ (length_app cs hlen)
          (envOK_topApp cs acc hA)
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          (rangeGo (topApp cs A) (cs.length + len) k).denote fuel (hvAppend acc V) =
            k.denote fuel (hvAppend acc V) :=
        fun acc => rangeGo_denote fuel _ _ k _ (length_app cs hlen) (envOK_topApp cs acc hA)
      simp only [rangeGo, NFProg.denote, hb, hk]
  | _, _, A, len, .call (rs := rs) f args k, V, hlen, hA => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          (rangeGo (topApp rs A) (rs.length + len) k).denote fuel (hvAppend r V) =
            k.denote fuel (hvAppend r V) :=
        fun r => rangeGo_denote fuel _ _ k _ (length_app rs hlen) (envOK_topApp rs r hA)
      simp only [rangeGo, NFProg.denote, hk]

end Denote

/-- **The range stage on structured programs**: the traversal from the full lane range of
    every input. -/
def rangeNF {Γ : JCtxt} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    NFProg jasminDialect Γ ts :=
  rangeGo (topEnv Γ) Γ.length p

/-- **Denotation of the stage.** `rangeNF p` denotes the same function as `p` at every
    fuel. -/
theorem rangeNF_denote [CallDenote jasminDialect] {Γ : JCtxt} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (fuel : Nat) :
    (rangeNF p).denote fuel = p.denote fuel :=
  funext fun V => rangeGo_denote fuel _ _ p V rfl (envOK_topEnv V)

/-- On an embedded straight-line program the traversal is `rangeCom`. -/
theorem rangeGo_ofCom : ∀ {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ) (len : Nat)
    (c : Com jasminDialect Γ t),
    rangeGo A len (NFProg.ofCom c) = NFProg.ofCom (rangeCom A len c)
  | _, _, _, _, .ret _ => rfl
  | _, _, A, len, .var e body => by
      simp only [NFProg.ofCom, rangeGo, rangeCom, rangeGo_ofCom]

/-- On an embedded straight-line program the stage is `comRangeOpt`. -/
theorem rangeNF_ofCom {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) :
    rangeNF (NFProg.ofCom c) = NFProg.ofCom (comRangeOpt c) :=
  rangeGo_ofCom _ _ c

/-! ## 3. Leakage -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel LeakKind Expr.ctLeak Labels)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (forIterLeak_ctRel whileIterLeak_ctRel)
open CatCrypt.Crypto.Optimizer.Rewrite.ComGVN (opLeak_length)

/-- The results of the leakage run of the traversal are those of the source. -/
theorem rangeGo_leakRun_fst (M : LeakModel jasminDialect) (fuel : Nat) {Γ : JCtxt}
    {ts : List JasminTy} (A : AEnv Γ) (len : Nat) (p : NFProg jasminDialect Γ ts)
    (V : Ctxt.Valuation Γ) (hlen : len = Γ.length) (hA : EnvOK A V) :
    (NFProg.leakRun M fuel (rangeGo A len p) V).map Prod.fst =
      (NFProg.leakRun M fuel p V).map Prod.fst := by
  rw [NFProg.leakRun_fst, NFProg.leakRun_fst]
  let _ : CallDenote jasminDialect := ⟨CallEnv.empty⟩
  exact rangeGo_denote fuel A len p V hlen hA

/-- A run of the traversal and a run of the source have the same results. -/
theorem rangeGo_fst_eq (M : LeakModel jasminDialect) (fuel : Nat) {Γ : JCtxt}
    {ts : List JasminTy} {A : AEnv Γ} {len : Nat} {p : NFProg jasminDialect Γ ts}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V)
    {r s : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak}
    (h : NFProg.leakRun M fuel p V = some r)
    (h' : NFProg.leakRun M fuel (rangeGo A len p) V = some s) : s.1 = r.1 := by
  have := rangeGo_leakRun_fst M fuel A len p V hlen hA
  rw [h, h'] at this
  exact Option.some.inj this

variable {L : LeakModel jasminDialect}

/-- **Leakage of the traversal, two-run.** Under an environment that holds of `V₁` and of
    `V₂` and a leakage model whose `regArith` operations are quiet, two runs of the source
    with equal events give, for any two runs of the output, equal events. -/
theorem rangeGo_ctRel (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat) :
    ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat)
      (p : NFProg jasminDialect Γ ts) (V₁ V₂ : Ctxt.Valuation Γ), len = Γ.length →
      EnvOK A V₁ → EnvOK A V₂ →
      ∀ (r₁ r₂ s₁ s₂ : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak),
      NFProg.leakRun L fuel p V₁ = some r₁ → NFProg.leakRun L fuel p V₂ = some r₂ →
      NFProg.leakRun L fuel (rangeGo A len p) V₁ = some s₁ →
      NFProg.leakRun L fuel (rangeGo A len p) V₂ = some s₂ → r₁.2 = r₂.2 → s₁.2 = s₂.2
  | _, _, _, _, .ret vs, V₁, V₂, _, _, _, r₁, r₂, s₁, s₂, _, _, h₃, h₄, _ => by
      simp only [rangeGo, NFProg.leakRun, Option.some.injEq] at h₃ h₄
      subst h₃ h₄
      rfl
  | _, _, A, len, .var e k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂, s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨hE, hB⟩ := List.append_inj he (opLeak_length L e.op _ _)
      simp only [rangeGo, NFProg.leakRun] at h₃ h₄
      rw [rangeExpr_denote hA₁ hlen e] at h₃
      rw [rangeExpr_denote hA₂ hlen e] at h₄
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      have hE2 : Expr.ctLeak L (rangeExpr A len e) V₁ =
          Expr.ctLeak L (rangeExpr A len e) V₂ := by
        rcases rangeExpr_leak hq A len e with h' | h'
        · rw [h']
          exact hE
        · exact h' _ _
      show Expr.ctLeak L (rangeExpr A len e) V₁ ++ t₁.2 =
        Expr.ctLeak L (rangeExpr A len e) V₂ ++ t₂.2
      rw [hE2]
      congr 1
      exact rangeGo_ctRel hq fuel _ (len + 1) k _ _ (by simp [hlen])
        (hA₁.cons (stageAbs_sound hA₁ hlen e)) (hA₂.cons (stageAbs_sound hA₂ hlen e))
        u₁ u₂ t₁ t₂ hu₁ hu₂ ht₁ ht₂ hB
  | Γ, _, A, len, .forLoop (cs := cs) count inits body k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [rangeGo, NFProg.leakRun] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hn, he'⟩ := List.cons.inj he
      injection hn with hn
      rw [← hn] at hi₂ hj₂
      have hb : ∀ (V : Ctxt.Valuation Γ) (X : Ctxt.Valuation (d := jasminDialect) cs)
          (i : Nat), EnvOK A V →
          EnvOK (topApp cs (topCons (HasWord64.word (d := jasminDialect)) A))
            (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun V X i h => envOK_topApp cs X (envOK_topCons h _)
      have hlb := length_body cs (HasWord64.word (d := jasminDialect)) hlen
      obtain ⟨hi, hj, hji₁, hji₂⟩ := forIterLeak_ctRel
        (fun i X => NFProg.leakRun L fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₁)))
        (fun i X => NFProg.leakRun L fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₂)))
        (fun i X => NFProg.leakRun L fuel
          (rangeGo (topApp cs (topCons (HasWord64.word (d := jasminDialect)) A))
            (cs.length + (len + 1)) body)
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₁)))
        (fun i X => NFProg.leakRun L fuel
          (rangeGo (topApp cs (topCons (HasWord64.word (d := jasminDialect)) A))
            (cs.length + (len + 1)) body)
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₂)))
        (fun i X => rangeGo_leakRun_fst L fuel _ _ body _ hlb (hb V₁ X i hA₁))
        (fun i X => rangeGo_leakRun_fst L fuel _ _ body _ hlb (hb V₂ X i hA₂))
        (fun i X Y r r' x y h h' hxy =>
          NFProg.leakRun_prefix L fuel body _ _ r r' x y h h' hxy)
        (fun i X Y r r' s s' h h' g g' hr =>
          rangeGo_ctRel hq fuel _ _ body _ _ hlb (hb V₁ X i hA₁) (hb V₂ Y i hA₂) r r' s s'
            h h' g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 hi₁ hi₂ hj₁ hj₂ he'
      rw [hi] at he'
      have hqq := List.append_cancel_left he'
      have hk := rangeGo_ctRel hq fuel _ _ k _ _ (length_app cs hlen)
        (envOK_topApp cs j₁.1 hA₁) (envOK_topApp cs j₂.1 hA₂) q₁ q₂ t₁ t₂
        (by rw [hji₁]; exact hq₁) (by rw [hji₂]; exact hq₂) ht₁ ht₂ hqq
      show _ :: (j₁.2 ++ t₁.2) = _ :: (j₂.2 ++ t₂.2)
      rw [hj, hk, hn]
  | _, _, A, len, .ifThenElse (rs := rs) cond thn els k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [rangeGo, NFProg.leakRun] at h₃ h₄
      obtain ⟨a₁, ha₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨a₂, ha₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨b₁, hb₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨b₂, hb₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hc, he'⟩ := List.cons.inj he
      injection hc with hc
      rw [← hc] at ha₂ hb₂
      have harm : a₁.2 = a₂.2 ∧ b₁.2 = b₂.2 ∧ b₁.1 = a₁.1 ∧ b₂.1 = a₂.1 := by
        cases hcb : HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁) <;>
          simp only [hcb, if_true, if_false, Bool.false_eq_true] at ha₁ ha₂ hb₁ hb₂
        · have ha := NFProg.leakRun_prefix L fuel els _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, rangeGo_ctRel hq fuel A len els V₁ V₂ hlen hA₁ hA₂ a₁ a₂ b₁ b₂ ha₁ ha₂
            hb₁ hb₂ ha, rangeGo_fst_eq L fuel hlen hA₁ ha₁ hb₁,
            rangeGo_fst_eq L fuel hlen hA₂ ha₂ hb₂⟩
        · have ha := NFProg.leakRun_prefix L fuel thn _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, rangeGo_ctRel hq fuel A len thn V₁ V₂ hlen hA₁ hA₂ a₁ a₂ b₁ b₂ ha₁ ha₂
            hb₁ hb₂ ha, rangeGo_fst_eq L fuel hlen hA₁ ha₁ hb₁,
            rangeGo_fst_eq L fuel hlen hA₂ ha₂ hb₂⟩
      obtain ⟨ha, hb, hba₁, hba₂⟩ := harm
      rw [ha] at he'
      have hqq := List.append_cancel_left he'
      have hk := rangeGo_ctRel hq fuel _ _ k _ _ (length_app rs hlen)
        (envOK_topApp rs b₁.1 hA₁) (envOK_topApp rs b₂.1 hA₂) q₁ q₂ t₁ t₂
        (by rw [hba₁]; exact hq₁) (by rw [hba₂]; exact hq₂) ht₁ ht₂ hqq
      show _ :: (b₁.2 ++ t₁.2) = _ :: (b₂.2 ++ t₂.2)
      rw [hb, hk, hc]
  | _, _, A, len, .whileLoop (cs := cs) inits body k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [rangeGo, NFProg.leakRun] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      have hla := length_app cs hlen
      obtain ⟨hi, hj, hji₁, hji₂⟩ := whileIterLeak_ctRel
        (fun X => NFProg.leakRun L fuel body (hvAppend X V₁))
        (fun X => NFProg.leakRun L fuel body (hvAppend X V₂))
        (fun X => NFProg.leakRun L fuel (rangeGo (topApp cs A) (cs.length + len) body)
          (hvAppend X V₁))
        (fun X => NFProg.leakRun L fuel (rangeGo (topApp cs A) (cs.length + len) body)
          (hvAppend X V₂))
        (fun X => rangeGo_leakRun_fst L fuel _ _ body _ hla (envOK_topApp cs X hA₁))
        (fun X => rangeGo_leakRun_fst L fuel _ _ body _ hla (envOK_topApp cs X hA₂))
        (fun X Y r r' x y h h' hxy =>
          NFProg.leakRun_prefix L fuel body _ _ r r' x y h h' hxy)
        (fun X Y r r' s s' h h' g g' hr =>
          rangeGo_ctRel hq fuel _ _ body _ _ hla (envOK_topApp cs X hA₁)
            (envOK_topApp cs Y hA₂) r r' s s' h h' g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 hi₁ hi₂ hj₁ hj₂ he
      rw [hi] at he
      have hqq := List.append_cancel_left he
      have hk := rangeGo_ctRel hq fuel _ _ k _ _ hla
        (envOK_topApp cs j₁.1 hA₁) (envOK_topApp cs j₂.1 hA₂) q₁ q₂ t₁ t₂
        (by rw [hji₁]; exact hq₁) (by rw [hji₂]; exact hq₂) ht₁ ht₂ hqq
      show j₁.2 ++ t₁.2 = j₂.2 ++ t₂.2
      rw [hj, hk]
  | _, _, _, _, .call .., _, _, _, _, _, _, _, _, _, h₁, _, _, _, _ => by
      simp [NFProg.leakRun] at h₁

/-- **Leakage of the stage, two-run.** Under a leakage model whose `regArith` operations are
    quiet, two runs of `p` that succeed with equal events give two runs of `rangeNF p` that
    succeed, with the same results and equal events. -/
theorem rangeNF_ctRel (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : JCtxt} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (V₁ V₂ : Ctxt.Valuation Γ) (r₁ r₂ : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak)
    (h₁ : NFProg.leakRun L fuel p V₁ = some r₁) (h₂ : NFProg.leakRun L fuel p V₂ = some r₂)
    (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRun L fuel (rangeNF p) V₁ = some s₁ ∧
      NFProg.leakRun L fuel (rangeNF p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧
      s₁.2 = s₂.2 := by
  have f₁ := rangeGo_leakRun_fst L fuel (topEnv Γ) Γ.length p V₁ rfl (envOK_topEnv V₁)
  have f₂ := rangeGo_leakRun_fst L fuel (topEnv Γ) Γ.length p V₂ rfl (envOK_topEnv V₂)
  rw [h₁, Option.map_some] at f₁
  rw [h₂, Option.map_some] at f₂
  obtain ⟨s₁, hs₁, e₁⟩ := Option.map_eq_some_iff.mp f₁
  obtain ⟨s₂, hs₂, e₂⟩ := Option.map_eq_some_iff.mp f₂
  exact ⟨s₁, s₂, hs₁, hs₂, e₁, e₂,
    rangeGo_ctRel hq fuel _ _ p V₁ V₂ rfl (envOK_topEnv V₁) (envOK_topEnv V₂) r₁ r₂ s₁ s₂
      h₁ h₂ hs₁ hs₂ he⟩

/-- **Constant time of the stage.** Under a leakage model whose `regArith` operations are
    quiet, if `p` is constant time for the labels `Lb`, so is `rangeNF p`. -/
theorem rangeNF_nfCT (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : JCtxt} {ts : List JasminTy} (Lb : Labels Γ) (p : NFProg jasminDialect Γ ts)
    (hct : NFCT L Lb fuel p) : NFCT L Lb fuel (rangeNF p) := by
  intro V₁ V₂ hV
  have f₁ := rangeGo_leakRun_fst L fuel (topEnv Γ) Γ.length p V₁ rfl (envOK_topEnv V₁)
  have f₂ := rangeGo_leakRun_fst L fuel (topEnv Γ) Γ.length p V₂ rfl (envOK_topEnv V₂)
  have hp := hct V₁ V₂ hV
  change (NFProg.leakRun L fuel (rangeGo _ _ p) V₁).map Prod.snd =
    (NFProg.leakRun L fuel (rangeGo _ _ p) V₂).map Prod.snd
  rcases hr₁ : NFProg.leakRun L fuel p V₁ with _ | r₁ <;>
    rcases hr₂ : NFProg.leakRun L fuel p V₂ with _ | r₂ <;>
    rw [hr₁] at f₁ hp <;> rw [hr₂] at f₂ hp
  · rw [Option.map_eq_none_iff.mp f₁, Option.map_eq_none_iff.mp f₂]
  · cases hp
  · cases hp
  · obtain ⟨s₁, hs₁, _⟩ := Option.map_eq_some_iff.mp f₁
    obtain ⟨s₂, hs₂, _⟩ := Option.map_eq_some_iff.mp f₂
    rw [hs₁, hs₂, Option.map_some, Option.map_some,
      rangeGo_ctRel hq fuel _ _ p V₁ V₂ rfl (envOK_topEnv V₁) (envOK_topEnv V₂) r₁ r₂ s₁ s₂
        hr₁ hr₂ hs₁ hs₂ (Option.some.inj hp)]

end Leak

/-! ## 4. The stage keeps a program branch-free -/

/-- **The traversal keeps a program branch-free.** -/
theorem ifFree_rangeGo : ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat)
    (p : NFProg jasminDialect Γ ts),
    NFProg.ifFree p = true → NFProg.ifFree (rangeGo A len p) = true
  | _, _, _, _, .ret _, _ => rfl
  | _, _, A, len, .var e k, hp => by
      have hk : NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using hp
      simpa only [rangeGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using
        ifFree_rangeGo _ _ k hk
  | _, _, A, len, .forLoop _ _ body k, hp => by
      have hbk : NFProg.ifFree body = true ∧ NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true] using hp
      simp only [rangeGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true]
      exact ⟨ifFree_rangeGo _ _ body hbk.1, ifFree_rangeGo _ _ k hbk.2⟩
  | _, _, _, _, .ifThenElse .., hp => by
      simp [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] at hp
  | _, _, A, len, .whileLoop _ body k, hp => by
      have hbk : NFProg.ifFree body = true ∧ NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true] using hp
      simp only [rangeGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true]
      exact ⟨ifFree_rangeGo _ _ body hbk.1, ifFree_rangeGo _ _ k hbk.2⟩
  | _, _, A, len, .call _ _ k, hp => by
      have hk : NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] using hp
      simpa only [rangeGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] using
        ifFree_rangeGo _ _ k hk

/-- **The stage keeps a program branch-free.** -/
theorem ifFree_rangeNF {Γ : JCtxt} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hp : NFProg.ifFree p = true) : NFProg.ifFree (rangeNF p) = true :=
  ifFree_rangeGo _ _ p hp

/-! ## 5. The chain step of the range stage -/

open NFProgPasses (nfSem)

/-- The range stage `rangeNF` as a chain step. -/
def rangeNFStep (Γ : JCtxt) (ts : List JasminTy) :
    PassChain.Step (NFProg jasminDialect Γ ts) (NFProg jasminDialect Γ ts) :=
  ⟨"range", fun p => some (rangeNF p)⟩

/-- The certificate of the range stage: the rewritten program has the denotation of its
    input, from `rangeNF_denote`. -/
def rangeNFCert [CallDenote jasminDialect] (fuel : Nat) (Γ : JCtxt) (ts : List JasminTy) :
    PassChain.StepCert (rangeNFStep Γ ts).run (nfSem fuel jasminDialect Γ ts)
      (nfSem fuel jasminDialect Γ ts) :=
  PassChain.StepCert.ofDenoteEq _ fun p q hf => by
    cases hf
    exact rangeNF_denote p fuel

end CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
