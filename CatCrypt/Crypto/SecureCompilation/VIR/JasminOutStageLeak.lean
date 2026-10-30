/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminOutStage
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
public import CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate

/-!
# Constant time of a program staged with an input array and an output array

A straight-line program of `jasminDialect` all of whose operations the leakage model classes
quiet emits no event, so its events are fixed (`leakFixed_of_allOps_quiet`). The staged
program `stageInOuts ws nIn nOut c` binds the indices `0, …, nIn - 1` as constants, loads the
inputs at these indices, runs the bindings of `c` and stores the outputs at constant indices.
The loads emit the values of their indices, which are constants, so for such a `c` the staged
program is constant time at every labels and fuel (`nfct_stageInOuts`).

## Main definitions

* `quietB`: the operations the leakage model classes quiet.
* `comAllOps`: every operation of a straight-line program satisfies a test.
* `PubIn`: the labels mark public the variables in a range of indices.

## Main statements

* `ctLeak_of_allOps_quiet`, `leakFixed_of_allOps_quiet`: a program of quiet operations emits
  no event and has fixed events.
* `nfct_var`: a binding whose events and, at a public label, whose value agree on valuations
  that agree on the public positions, followed by a constant-time program, is constant time.
* `nfct_stageInOuts`: the staged program of a program of quiet operations is constant time at
  every labels and fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminOutStage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
  (LeakModel Labels lvlOf PubEqV Expr.ctLeak Com.ctLeak opLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jKind jLeakModel
  jKind_stackStoreImm)
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (varIndex)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. Programs of quiet operations -/

/-- The operations the leakage model at the parameters `Pj` classes quiet. -/
def quietB (Pj : JLeakParams) (op : JasminOp) : Bool :=
  match jKind Pj op with
  | .quiet => true
  | _ => false

theorem jKind_of_quietB {Pj : JLeakParams} {op : JasminOp} (h : quietB Pj op = true) :
    jKind Pj op = .quiet := by
  unfold quietB at h
  split at h
  · assumption
  · cases h

/-- Every operation of a binding of the straight-line program satisfies `P`. -/
def comAllOps (P : JasminOp → Bool) : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => P e.op && comAllOps P body

/-- A renamed program has the operations of the program. -/
theorem comAllOps_rename (P : JasminOp → Bool) : ∀ {Γ Γ' : Ctxt jasminDialect} {t : JasminTy}
    (h : Ctxt.Hom Γ Γ') (c : Com jasminDialect Γ t),
    comAllOps P (c.rename h) = comAllOps P c
  | _, _, _, _, .ret _ => rfl
  | _, _, _, h, .var _ body => by
      simp only [Com.rename, comAllOps, Expr.op_rename, comAllOps_rename P h.lift body]

/-- A quiet operation emits no event. -/
theorem expr_ctLeak_quiet (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (h : jKind Pj e.op = .quiet) (V : Ctxt.Valuation Γ) :
    Expr.ctLeak (jLeakModel Pj) e V = [] := by
  simp only [Expr.ctLeak, opLeak, jLeakModel, h]

/-- **A program of quiet operations emits no event.** -/
theorem ctLeak_of_allOps_quiet (Pj : JLeakParams) : ∀ {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t), comAllOps (quietB Pj) c = true →
    ∀ V, Com.ctLeak (jLeakModel Pj) c V = []
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, h, V => by
      simp only [comAllOps, Bool.and_eq_true] at h
      rw [Com.ctLeak, expr_ctLeak_quiet Pj e (jKind_of_quietB h.1),
        ctLeak_of_allOps_quiet Pj body h.2, List.append_nil]

/-- **A program of quiet operations has fixed events.** -/
theorem leakFixed_of_allOps_quiet (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t} (h : comAllOps (quietB Pj) c = true) :
    LeakFixed (jLeakModel Pj) c := by
  intro V₁ V₂
  rw [ctLeak_of_allOps_quiet Pj c h, ctLeak_of_allOps_quiet Pj c h]

/-! ## 2. The leakage run of a binding -/

section Var

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- The events of the leakage run of a binding: the events of its expression, then those of
    its continuation. -/
theorem leakRun_var_snd (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {u : d.Ty}
    {ts : List d.Ty} (e : Expr d Γ u) (k : NFProg d (u :: Γ) ts) (V : Ctxt.Valuation Γ) :
    (NFProg.leakRun M fuel (.var e k) V).map Prod.snd =
      ((NFProg.leakRun M fuel k (V.extend (e.denote V))).map Prod.snd).map
        (Expr.ctLeak M e V ++ ·) := by
  simp only [NFProg.leakRun, Option.map_map]
  rfl

/-- **Constant time of a binding**: when the events of the expression agree on valuations
    that agree on the positions `L` marks public, and so does its value when the level `l` of
    the binding is public, a constant-time continuation for the labels `l :: L` gives a
    constant-time binding for `L`. -/
theorem nfct_var (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {u : d.Ty} {ts : List d.Ty}
    (e : Expr d Γ u) (k : NFProg d (u :: Γ) ts) (L : Labels Γ) (l : SecretLevel)
    (he : ∀ V₁ V₂, PubEqV L V₁ V₂ → Expr.ctLeak M e V₁ = Expr.ctLeak M e V₂)
    (hd : l = .Public → ∀ V₁ V₂, PubEqV L V₁ V₂ → e.denote V₁ = e.denote V₂)
    (hk : NFCT M (.cons l L) fuel k) : NFCT M L fuel (.var e k) := by
  intro V₁ V₂ hV
  rw [leakRun_var_snd, leakRun_var_snd, he V₁ V₂ hV]
  exact congrArg _ (hk _ _ (pubEqV_cons hV l _ _ fun hl => hd hl V₁ V₂ hV))

/-- A program whose leakage run emits no event at every valuation is constant time. -/
theorem nfct_of_nil (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (h : ∀ V, (NFProg.leakRun M fuel p V).map Prod.snd = some [])
    (L : Labels Γ) : NFCT M L fuel p := by
  intro V₁ V₂ _
  rw [h V₁, h V₂]

end Var

/-! ## 3. The stages of `stageInOuts` -/

variable (Pj : JLeakParams) (fuel : Nat)

/-- The stores of the outputs emit no event when constant-index stores are quiet. -/
theorem storesGo_leakRun (hst : ∀ w n i, Pj.opVT (.stackStoreImm w n i) = none)
    (ws nOut : Nat) : ∀ (k j : Nat) {Δ : Ctxt jasminDialect}
    (arr : Ctxt.Var Δ (.stackArr ws nOut)) (s : NFProg jasminDialect Δ [.stackArr ws nOut]),
    storesGo ws nOut k j arr = some s →
    ∀ V, (NFProg.leakRun (jLeakModel Pj) fuel s V).map Prod.snd = some []
  | 0, _, _, _, s, h, V => by
      simp only [storesGo, Option.some.injEq] at h
      subst h
      rfl
  | k + 1, j, _, arr, s, h, V => by
      simp only [storesGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, -, r, hr, rfl⟩ := h
      rw [leakRun_var_snd, storesGo_leakRun hst ws nOut k (j + 1) _ r hr, Option.map_some,
        expr_ctLeak_quiet Pj _ (jKind_stackStoreImm Pj ws nOut j (hst ws nOut j))]
      rfl

/-- The bindings of a program of quiet operations followed by the stores of the outputs emit
    no event. -/
theorem stageGo_leakRun (hst : ∀ w n i, Pj.opVT (.stackStoreImm w n i) = none)
    (ws nOut : Nat) : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (q : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]),
    comAllOps (quietB Pj) c = true → stageGo ws nOut c = some q →
    ∀ V, (NFProg.leakRun (jLeakModel Pj) fuel q V).map Prod.snd = some []
  | Γ, _, .ret _, q, _, h, V => storesGo_leakRun Pj fuel hst ws nOut nOut 0 _ q h V
  | Γ, _, .var e body, q, hc, h, V => by
      simp only [stageGo, Option.map_eq_some_iff] at h
      obtain ⟨q', hq', rfl⟩ := h
      simp only [comAllOps, Bool.and_eq_true] at hc
      rw [leakRun_var_snd, stageGo_leakRun hst ws nOut body q' hc.2 hq', Option.map_some,
        expr_ctLeak_quiet Pj _ (by rw [Expr.op_rename]; exact jKind_of_quietB hc.1)]
      rfl

/-- The labels `L` mark public every variable of index at least `lo` and below `hi`. -/
def PubIn {Γ : Ctxt jasminDialect} (lo hi : Nat) (L : Labels Γ) : Prop :=
  ∀ {u : JasminTy} (v : Ctxt.Var Γ u), lo ≤ varIndex v → varIndex v < hi → lvlOf v L = .Public

/-- A load at an index of public level emits the same events at valuations that agree on the
    public positions. -/
theorem stackLoad_ctLeak_eq {ws n : Nat} {Γ : Ctxt jasminDialect} (L : Labels Γ)
    (a : Ctxt.Var Γ (.stackArr ws n)) (i : Ctxt.Var Γ (.reg 64)) (hi : lvlOf i L = .Public)
    (V₁ V₂ : Ctxt.Valuation Γ) (hV : PubEqV L V₁ V₂) :
    Expr.ctLeak (jLeakModel Pj) (⟨.stackLoad ws n, rfl, .cons a (.cons i .nil)⟩ :
      Expr jasminDialect Γ (.reg ws)) V₁ =
    Expr.ctLeak (jLeakModel Pj) (⟨.stackLoad ws n, rfl, .cons a (.cons i .nil)⟩ :
      Expr jasminDialect Γ (.reg ws)) V₂ := by
  have h := hV _ i hi
  change [CT.CTLeak.addr "" ((Dialects.JasminComLLeak.jValNat (.reg 64) (i.lookup V₁) : Nat) :
      Int)] = [CT.CTLeak.addr "" ((Dialects.JasminComLLeak.jValNat (.reg 64) (i.lookup V₂) :
      Nat) : Int)]
  rw [h]

/-- **The loads of the inputs keep constant time**: when the program `p` after the loads is
    constant time at every labels that mark the index registers public, the program with
    the loads is constant time at every labels that mark the index registers public. -/
theorem loadsGo_nfct (ws nIn nOut : Nat) : ∀ (k : Nat) {ts : List JasminTy}
    (p : NFProg jasminDialect ((List.replicate k (.reg ws) ++
      (idxCtx nIn ++ [.stackArr ws nIn])) ++ [.stackArr ws nOut]) ts)
    (r : NFProg jasminDialect ((idxCtx nIn ++ [.stackArr ws nIn]) ++ [.stackArr ws nOut]) ts),
    k ≤ nIn → loadsGo ws nIn nOut k p = some r →
    (∀ L, PubIn k (k + nIn) L → NFCT (jLeakModel Pj) L fuel p) →
    ∀ L, PubIn 0 nIn L → NFCT (jLeakModel Pj) L fuel r
  | 0, _, p, r, _, h, hp, L, hL => by
      simp only [loadsGo, Option.some.injEq] at h
      subst h
      exact hp L (by rw [Nat.zero_add]; exact hL)
  | k + 1, _, p, r, hk, h, hp, L, hL => by
      simp only [loadsGo, Option.bind_eq_some_iff] at h
      obtain ⟨i, hi, a, -, h⟩ := h
      refine loadsGo_nfct ws nIn nOut k _ r (by omega) h (fun L' hL' => ?_) L hL
      refine nfct_var _ fuel _ p L' .Secret (stackLoad_ctLeak_eq Pj L' a i ?_)
        (fun h => nomatch h) (hp _ ?_)
      · obtain ⟨hix, -⟩ := tyIdx?_spec hi
        exact hL' i (by omega) (by omega)
      · intro u v h1 h2
        cases v with
        | here => simp [varIndex] at h1
        | there w =>
            exact hL' w (by simp only [varIndex] at h1; omega)
              (by simp only [varIndex] at h2; omega)

/-- **The constants of the indices give constant time**: when the program `p` after the
    constants is constant time at every labels that mark the index registers public, the
    program with the constants is constant time at every labels. -/
theorem constsGo_nfct (ws nIn nOut : Nat) : ∀ (k : Nat) {ts : List JasminTy}
    (p : NFProg jasminDialect ((idxCtx k ++ [.stackArr ws nIn]) ++ [.stackArr ws nOut]) ts),
    (∀ L, PubIn 0 k L → NFCT (jLeakModel Pj) L fuel p) →
    ∀ L, NFCT (jLeakModel Pj) L fuel (constsGo ws nIn nOut k p)
  | 0, _, p, hp, L => hp L (fun _ _ h => absurd h (Nat.not_lt_zero _))
  | k + 1, _, p, hp, L => constsGo_nfct ws nIn nOut k _ (fun L' hL' =>
      nfct_var _ fuel _ p L' .Public (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (hp _ (by
        intro u v _ h2
        cases v with
        | here => rfl
        | there w => exact hL' w (Nat.zero_le _) (by simp only [varIndex] at h2; omega)))) L

/-- **The staged program of a program of quiet operations is constant time** at every labels
    and fuel, when constant-index stores are quiet: the loads read the inputs at the indices
    the program binds as constants, and every other binding is quiet. -/
theorem nfct_stageInOuts (hst : ∀ w n i, Pj.opVT (.stackStoreImm w n i) = none)
    {ws nIn nOut : Nat} {t : JasminTy} {c : Com jasminDialect (List.replicate nIn (.reg ws)) t}
    {p : NFProg jasminDialect [.stackArr ws nIn, .stackArr ws nOut] [.stackArr ws nOut]}
    (h : stageInOuts ws nIn nOut c = some p) (hc : comAllOps (quietB Pj) c = true)
    (L : Labels (d := jasminDialect) [.stackArr ws nIn, .stackArr ws nOut]) :
    NFCT (jLeakModel Pj) L fuel p := by
  obtain ⟨-, q, r, hq, hr, rfl⟩ := stageInOuts_eq_some h
  refine constsGo_nfct Pj fuel ws nIn nOut nIn r (fun L' hL' => ?_) L
  refine loadsGo_nfct Pj fuel ws nIn nOut nIn q r le_rfl hr (fun L'' _ => ?_) L' hL'
  exact nfct_of_nil _ fuel q (stageGo_leakRun Pj fuel hst ws nOut _ q
    (by rw [comAllOps_rename]; exact hc) hq) L''

end CatCrypt.Crypto.SecureCompilation.VIR.JasminOutStage
