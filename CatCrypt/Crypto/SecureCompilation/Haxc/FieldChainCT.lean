/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCT

/-!
# Constant time through the lane chains

`lanesChainViaCTCert` is a constant-time certificate (`PassChain.CTCert`) of the lane chain
`lanesChainVia opt` of `Haxc/NttRoute.lean`, from the events `MultiReturnCom.ctLeak` of the
lane program at the leakage parameters `Pj` of `jasminDialect` with no variable-time
operation, to the events `RouteProg.ctLeak` of the route program. `lanesChainCTCert` is the
certificate of the lane chain `lanesChain N pure` of `Haxc/FieldChain.lean`, which is
`lanesChainVia` at the value numbering `gvnStep pure`; its obligation is `gvnMR_ctLeak_eq`.
`lanesChainViaCTCert` has one leaf per step:

0. the optimisation step `opt`: its obligation `hopt`, that equal events of the input at
   two valuations give equal events of the output there (`lanesOptCTStep`);
1. the lane lowering `lanesStep`: the loads of the input words and the stores of the output
   words are at constant indices, and between them the lane program runs at the loaded
   words (`lanesCom_ctLeak_eq`, `lanesCTStep`);
2. the route wrapper `straightStep`: the events of `RouteProg.straight c` are those of `c`
   (`straightCTStep`).

## Main definitions

* `mrLeakSem`, `comLeakSem`, `routeProgLeakSem`: the leak semantics of multi-result
  programs, of straight-line programs and of route programs.
* `lanesOptCTStep`, `lanesCTStep`, `straightCTStep`: the step certificates.
* `lanesChainViaCTCert`: the constant-time certificate of the lane chain at `opt`.

## Main results

* `MultiReturnCom.ctLeak_rename_pullV`, `spliceMultiK_ctLeak_eq`: the events of a renamed
  multi-result program, and equal events of a multi-result splice.
* `loadLimbs_ctLeak_eq`, `lanesCom_ctLeak_eq`: equal events of the loads of limbs and of a
  lane program over word arrays.
* `lanesChainVia_ct`: constant time through the lane chain at `opt`.
* `gvnMRGo_ctLeak`, `gvnMR_ctLeak_eq`: the events of the value numbering of multi-result
  programs.
* `lanesChainCTCert`, `lanesChain_ct`: the constant-time certificate of the lane chain and
  constant time through it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (spliceMultiK hvToHom)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel opLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (MC Pres bindK eConst)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
  (arrTy arrLimbs loadLimbs storeLimbs eLoad consHom)
open CatCrypt.Crypto.SecureCompilation.Haxc (RouteProg stepCertOfLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute (lanesCtx lanesBody lanesCom)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (ctLeak_toComHead storeLimbs_evFix)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (opLeak_length)
open Ctxt (Var Valuation)

/-! ## 1. Leak semantics -/

section Sems

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-- The leak semantics of multi-result programs at the leakage model `M`: every run
    succeeds with the events `MultiReturnCom.ctLeak`. -/
def mrLeakSem (M : LeakModel d) (Γ : Ctxt d) (ts : List d.Ty) :
    LeakSem (MultiReturnCom d Γ ts) where
  In := Valuation Γ
  Ev := CTLeak
  leak m V := some (MultiReturnCom.ctLeak M m V)

/-- The leak semantics of straight-line programs at the leakage model `M`: every run
    succeeds with the events `Com.ctLeak`. -/
def comLeakSem (M : LeakModel d) (Γ : Ctxt d) (t : d.Ty) : LeakSem (Com d Γ t) where
  In := Valuation Γ
  Ev := CTLeak
  leak c V := some (ComLevelCheck.Com.ctLeak M c V)

end Sems

/-- The leak semantics of route programs at the leakage parameters `Pj`: every run succeeds
    with the events `RouteProg.ctLeak`. -/
def routeProgLeakSem (Pj : JLeakParams) (Γ : Ctxt jasminDialect) (t : JasminTy) :
    LeakSem (RouteProg Γ t) where
  In := Valuation Γ
  Ev := CTLeak
  leak rp V := some (RouteProg.ctLeak Pj rp V)

/-! ## 2. Events of renamed and spliced multi-result programs -/

section Splice

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-- A renamed multi-result program emits the events of the program at the pulled-back
    valuation. -/
theorem MultiReturnCom.ctLeak_rename_pullV (M : LeakModel d) {Γ Γ' : Ctxt d}
    {ts : List d.Ty} (h : Ctxt.Hom Γ Γ') (m : MultiReturnCom d Γ ts) (V : Valuation Γ') :
    MultiReturnCom.ctLeak M (MultiReturnCom.rename h m) V =
      MultiReturnCom.ctLeak M m (pullV h V) := by
  induction m generalizing Γ' with
  | ret vs => rfl
  | var e body ih =>
      change ComLevelCheck.Expr.ctLeak M (e.rename h) V ++
          MultiReturnCom.ctLeak M (MultiReturnCom.rename h.lift body)
            (V.extend ((e.rename h).denote V)) =
        ComLevelCheck.Expr.ctLeak M e (pullV h V) ++
          MultiReturnCom.ctLeak M body ((pullV h V).extend (e.denote (pullV h V)))
      rw [NFProg.Expr.ctLeak_rename_pullV, ih, FieldDialectBlockDescent.Expr.denote_rename h e V]
      congr 2
      change HVector.cons (e.denote (pullV h V))
          (pullV (fun v => (h v).there) (HVector.cons (e.denote (pullV h V)) V))
        = HVector.cons (e.denote (pullV h V)) (pullV h V)
      rw [FieldDialectBlockDescent.pullV_there h (e.denote (pullV h V)) V]

/-- **Equal events of a multi-result splice.** If the block emits equal events at `W₁` and
    `W₂`, and every continuation `k ren res` emits equal events at valuations to which `ren`
    preserves lookups from `W₁` and `W₂`, the splice emits equal events at `W₁` and `W₂`. -/
theorem spliceMultiK_ctLeak_eq (M : LeakModel d) : {Γ : Ctxt d} → {ts bs : List d.Ty} →
    (blk : MultiReturnCom d Γ ts) →
    (k : {Δ : Ctxt d} → Ctxt.Hom Γ Δ → HVector (fun u => Var Δ u) ts →
      MultiReturnCom d Δ bs) →
    (W₁ W₂ : Valuation Γ) →
    MultiReturnCom.ctLeak M blk W₁ = MultiReturnCom.ctLeak M blk W₂ →
    (∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (res : HVector (fun u => Var Δ u) ts)
        (W₁' W₂' : Valuation Δ),
        (∀ {s : d.Ty} (v : Var Γ s), (ren v).lookup W₁' = v.lookup W₁) →
        (∀ {s : d.Ty} (v : Var Γ s), (ren v).lookup W₂' = v.lookup W₂) →
        MultiReturnCom.ctLeak M (k ren res) W₁' = MultiReturnCom.ctLeak M (k ren res) W₂') →
    MultiReturnCom.ctLeak M (spliceMultiK blk k) W₁ =
      MultiReturnCom.ctLeak M (spliceMultiK blk k) W₂
  | _, _, _, .ret vs, _, W₁, W₂, _, hk =>
      hk (fun x => x) vs W₁ W₂ (fun _ => rfl) (fun _ => rfl)
  | _, _, _, .var e blk, k, W₁, W₂, h, hk => by
      obtain ⟨hE, hB⟩ := List.append_inj h (opLeak_length M e.op _ _)
      change ComLevelCheck.Expr.ctLeak M e W₁ ++
          MultiReturnCom.ctLeak M (spliceMultiK blk _) (W₁.extend (e.denote W₁)) =
        ComLevelCheck.Expr.ctLeak M e W₂ ++
          MultiReturnCom.ctLeak M (spliceMultiK blk _) (W₂.extend (e.denote W₂))
      rw [hE]
      congr 1
      exact spliceMultiK_ctLeak_eq M blk _ _ _ hB fun ren res W₁' W₂' h1 h2 =>
        hk _ res W₁' W₂' (fun v => h1 (.there v)) (fun v => h2 (.there v))

end Splice

/-! ## 3. Events of the lane program over word arrays -/

section Lanes

variable {N : Nat}

/-- **Equal events of a binding.** If `e` emits equal events at `W₁` and `W₂` and every
    continuation emits equal events at valuations that preserve the lookups and bind the
    value of `e`, `bindK e k` emits equal events at `W₁` and `W₂`. -/
theorem bindK_ctLeak_eq (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {ts : List JasminTy} (e : Expr jasminDialect Γ t)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ t → MC Δ ts)
    (W₁ W₂ : Valuation Γ)
    (he : ComLevelCheck.Expr.ctLeak M e W₁ = ComLevelCheck.Expr.ctLeak M e W₂)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (x : Var Δ t)
      (W₁' W₂' : Valuation Δ), Pres r W₁ W₁' → Pres r W₂ W₂' →
      x.lookup W₁' = e.denote W₁ → x.lookup W₂' = e.denote W₂ →
      MultiReturnCom.ctLeak M (k r x) W₁' = MultiReturnCom.ctLeak M (k r x) W₂') :
    MultiReturnCom.ctLeak M (bindK e k) W₁ = MultiReturnCom.ctLeak M (bindK e k) W₂ := by
  change ComLevelCheck.Expr.ctLeak M e W₁ ++ _ =ComLevelCheck.Expr.ctLeak M e W₂ ++ _
  rw [he]
  congr 1
  exact hk _ _ _ _ (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- A load of a word emits equal events at two valuations with the same index. -/
theorem eLoad_ctLeak_eq (Pj : JLeakParams) {n : Nat} {Δ : Ctxt jasminDialect}
    (a : Var Δ (arrTy n)) (i : Var Δ (.reg 64)) (W₁ W₂ : Valuation Δ)
    (hi : i.lookup W₁ = i.lookup W₂) :
    ComLevelCheck.Expr.ctLeak (jLeakModel Pj) (eLoad a i) W₁ =
      ComLevelCheck.Expr.ctLeak (jLeakModel Pj) (eLoad a i) W₂ := by
  simp only [ComLevelCheck.Expr.ctLeak, opLeak]
  rw [show (jLeakModel Pj).kind (eLoad (n := n) a i).op = .addrAt 1 from rfl]
  change [CTLeak.addr "" (((jLeakModel Pj).valNat _ (i.lookup W₁) : Nat) : Int)] =
    [CTLeak.addr "" (((jLeakModel Pj).valNat _ (i.lookup W₂) : Nat) : Int)]
  rw [hi]

/-- **Equal events of the loads of limbs.** The loads of `m` words of the array `a` from
    index `j` emit equal events at `W₁` and `W₂` when every continuation emits equal events
    at valuations that preserve the lookups and hold the loaded words. -/
theorem loadLimbs_ctLeak_eq (Pj : JLeakParams) {n : Nat} {bs : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (a : Var Δ (arrTy n))
      (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Rn m) Δ' → MC Δ' bs)
      (W₁ W₂ : Valuation Δ), j + m < 2 ^ 64 →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h : Ctxt.Hom (Rn m) Δ')
          (W₁' W₂' : Valuation Δ'), Pres r W₁ W₁' → Pres r W₂ W₂' →
          pullV h W₁' = arrLimbs (a.lookup W₁) m j →
          pullV h W₂' = arrLimbs (a.lookup W₂) m j →
          MultiReturnCom.ctLeak (jLeakModel Pj) (k r h) W₁' =
            MultiReturnCom.ctLeak (jLeakModel Pj) (k r h) W₂') →
      MultiReturnCom.ctLeak (jLeakModel Pj) (loadLimbs m j a k) W₁ =
        MultiReturnCom.ctLeak (jLeakModel Pj) (loadLimbs m j a k) W₂
  | _, 0, _, _, _, W₁, W₂, _, hk => hk (fun v => v) _ W₁ W₂ (Pres.id W₁) (Pres.id W₂) rfl rfl
  | _, m + 1, j, a, k, W₁, W₂, hj, hk => by
      rw [loadLimbs]
      refine bindK_ctLeak_eq _ _ _ W₁ W₂ rfl fun r₁ i U₁ U₂ hU₁ hU₂ hi₁ hi₂ => ?_
      refine bindK_ctLeak_eq _ _ _ U₁ U₂
        (eLoad_ctLeak_eq Pj _ _ U₁ U₂ (by rw [hi₁, hi₂]; rfl))
        fun r₂ x X₁ X₂ hX₁ hX₂ hx₁ hx₂ => ?_
      refine loadLimbs_ctLeak_eq Pj m (j + 1) _ _ X₁ X₂ (by omega)
        fun r₃ h Y₁ Y₂ hY₁ hY₂ hh₁ hh₂ => ?_
      have key : ∀ {W : Valuation _} {U : Valuation _} {X : Valuation _} {Y : Valuation _},
          Pres r₁ W U → i.lookup U = (eConst j).denote W → Pres r₂ U X →
          x.lookup X = (eLoad (r₁ a) i).denote U → Pres r₃ X Y →
          pullV h Y = arrLimbs ((r₂ (r₁ a)).lookup X) m (j + 1) →
          pullV (consHom (r₃ x) h) Y = arrLimbs (a.lookup W) (m + 1) j := by
        intro W U X Y h₁ hi h₂ hx h₃ hh
        have ha : (r₂ (r₁ a)).lookup X = a.lookup W := (h₂ _).trans (h₁ a)
        rw [ha] at hh
        change HVector.cons ((r₃ x).lookup Y) (pullV h Y) = _
        rw [hh, h₃ x, hx]
        have e : (eLoad (r₁ a) i).denote U
            = stackGet ((r₁ a).lookup U) (i.lookup U).toNat := rfl
        have e₀ : (i.lookup U).toNat = j % 2 ^ 64 := by
          rw [hi]
          exact BitVec.toNat_ofNat j 64
        rw [e, h₁ a, e₀, Nat.mod_eq_of_lt (by omega)]
        rfl
      exact hk _ _ Y₁ Y₂ (Pres.comp (Pres.comp hU₁ hX₁) hY₁) (Pres.comp (Pres.comp hU₂ hX₂) hY₂)
        (key hU₁ hi₁ hX₁ hx₁ hY₁ hh₁) (key hU₂ hi₂ hX₂ hx₂ hY₂ hh₂)

/-- **Equal events of a lane program over word arrays.** At leakage parameters with no
    variable-time operation, a lane program `m` that emits equal events at the words of the
    input arrays `a₁` and `a₂` gives a program `lanesCom m` that emits equal events at the
    input arrays `a₁`, `a₂` and arbitrary output arrays `o₁`, `o₂`. -/
theorem lanesCom_ctLeak_eq (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none)
    (hN : N < 2 ^ 64) (m : MultiReturnCom jasminDialect (Rn N) (Rn N))
    (a₁ o₁ a₂ o₂ : Fin N → BitVec 64)
    (h : MultiReturnCom.ctLeak (jLeakModel Pj) m (arrLimbs a₁ N 0) =
      MultiReturnCom.ctLeak (jLeakModel Pj) m (arrLimbs a₂ N 0)) :
    ComLevelCheck.Com.ctLeak (jLeakModel Pj) (lanesCom m) (.cons a₁ (.cons o₁ .nil)) =
      ComLevelCheck.Com.ctLeak (jLeakModel Pj) (lanesCom m) (.cons a₂ (.cons o₂ .nil)) := by
  rw [lanesCom, ctLeak_toComHead, ctLeak_toComHead, lanesBody]
  refine loadLimbs_ctLeak_eq Pj N 0 .here _ _ _ (by omega) fun _ _ W₁ W₂ _ _ hh₁ hh₂ => ?_
  refine spliceMultiK_ctLeak_eq _ _ _ W₁ W₂ ?_
    fun _ _ W₁' W₂' _ _ => storeLimbs_evFix hV _ _ _ _ W₁' W₂'
  rw [MultiReturnCom.ctLeak_rename_pullV, MultiReturnCom.ctLeak_rename_pullV, hh₁, hh₂]
  exact h

end Lanes

/-! ## 4. The constant-time certificate of the lane chain -/

variable {N : Nat}

/-- The constant-time step certificate of an optimisation step `opt` on lane programs whose
    output emits equal events at two valuations where its input does (`hopt`). -/
def lanesOptCTStep (Pj : JLeakParams)
    (opt : Step (MultiReturnCom jasminDialect (Rn N) (Rn N))
      (MultiReturnCom jasminDialect (Rn N) (Rn N)))
    (hopt : ∀ m q, opt.run m = some q → ∀ V₁ V₂,
      MultiReturnCom.ctLeak (jLeakModel Pj) m V₁ = MultiReturnCom.ctLeak (jLeakModel Pj) m V₂ →
      MultiReturnCom.ctLeak (jLeakModel Pj) q V₁ = MultiReturnCom.ctLeak (jLeakModel Pj) q V₂) :
    StepCert opt.run (mrLeakSem (jLeakModel Pj) (Rn N) (Rn N)).twoRun
      (mrLeakSem (jLeakModel Pj) (Rn N) (Rn N)).twoRun :=
  stepCertOfLeak _ _ Eq fun {m q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    obtain rfl := Option.some.inj h₁
    obtain rfl := Option.some.inj h₂
    exact ⟨_, _, rfl, rfl, hopt m q hf V₁ V₂⟩

/-- The constant-time step certificate of the lane lowering: the input relation says the
    input array holds the input words and the output array is arbitrary
    (`lanesCom_ctLeak_eq`). -/
def lanesCTStep (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (hN : N < 2 ^ 64) :
    StepCert (lanesStep N).run (mrLeakSem (jLeakModel Pj) (Rn N) (Rn N)).twoRun
      (comLeakSem (jLeakModel Pj) (lanesCtx N) (arrTy N)).twoRun :=
  stepCertOfLeak _ _ (fun V W => ∃ a o : Fin N → BitVec 64,
      @Eq (Valuation (lanesCtx N)) W (.cons a (.cons o .nil)) ∧ V = arrLimbs a N 0)
    fun {m q _ _ _ _ _ _} hf hR₁ hR₂ h₁ h₂ => by
      obtain ⟨a₁, o₁, rfl, rfl⟩ := hR₁
      obtain ⟨a₂, o₂, rfl, rfl⟩ := hR₂
      cases hf
      obtain rfl := Option.some.inj h₁
      obtain rfl := Option.some.inj h₂
      exact ⟨_, _, rfl, rfl, lanesCom_ctLeak_eq Pj hV hN m a₁ o₁ a₂ o₂⟩

/-- The constant-time step certificate of the route wrapper: the events of
    `RouteProg.straight c` are those of `c` (`RouteProg.ctLeak_straight`). -/
def straightCTStep (Pj : JLeakParams) (Γ : Ctxt jasminDialect) (t : JasminTy) :
    StepCert (straightStep Γ t).run (comLeakSem (jLeakModel Pj) Γ t).twoRun
      (routeProgLeakSem Pj Γ t).twoRun :=
  stepCertOfLeak _ _ Eq fun {c q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    cases hf
    obtain rfl := Option.some.inj h₁
    obtain rfl := Option.some.inj h₂
    refine ⟨_, _, rfl, rfl, fun he => ?_⟩
    exact (RouteProg.ctLeak_straight Pj c V₁).trans
      (he.trans (RouteProg.ctLeak_straight Pj c V₂).symm)

/-- **The constant-time certificate of the lane chain at the optimisation step `opt`**, at
    the leakage parameters `Pj` of `jasminDialect` with no variable-time operation, for a
    step `opt` whose output emits equal events at two valuations where its input does
    (`hopt`): one leaf per step of `lanesChainVia opt`. -/
def lanesChainViaCTCert (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (hN : N < 2 ^ 64)
    (opt : Step (MultiReturnCom jasminDialect (Rn N) (Rn N))
      (MultiReturnCom jasminDialect (Rn N) (Rn N)))
    (hopt : ∀ m q, opt.run m = some q → ∀ V₁ V₂,
      MultiReturnCom.ctLeak (jLeakModel Pj) m V₁ = MultiReturnCom.ctLeak (jLeakModel Pj) m V₂ →
      MultiReturnCom.ctLeak (jLeakModel Pj) q V₁ = MultiReturnCom.ctLeak (jLeakModel Pj) q V₂) :
    CTCert (lanesChainVia opt) (mrLeakSem (jLeakModel Pj) (Rn N) (Rn N))
      (routeProgLeakSem Pj (lanesCtx N) (arrTy N)) :=
  .cons (lanesOptCTStep Pj opt hopt) (fun _ _ h => h) <|
    .cons (lanesCTStep Pj hV hN) (fun _ _ h => h) <|
    .cons (straightCTStep Pj _ _) (fun _ _ h => h) <|
    .nil _

/-- **Constant time through the lane chain at `opt`.** A lane program `m` that emits equal
    events at the words of the input arrays `a₁` and `a₂` gives a route program
    `(lanesChainVia opt).run m` that emits equal events at the input arrays `a₁`, `a₂` and
    arbitrary output arrays `o₁`, `o₂`; this is `PassChain.CTCert.ct` at
    `lanesChainViaCTCert`. -/
theorem lanesChainVia_ct (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (hN : N < 2 ^ 64)
    (opt : Step (MultiReturnCom jasminDialect (Rn N) (Rn N))
      (MultiReturnCom jasminDialect (Rn N) (Rn N)))
    (hopt : ∀ m q, opt.run m = some q → ∀ V₁ V₂,
      MultiReturnCom.ctLeak (jLeakModel Pj) m V₁ = MultiReturnCom.ctLeak (jLeakModel Pj) m V₂ →
      MultiReturnCom.ctLeak (jLeakModel Pj) q V₁ = MultiReturnCom.ctLeak (jLeakModel Pj) q V₂)
    {m : MultiReturnCom jasminDialect (Rn N) (Rn N)} {rp : RouteProg (lanesCtx N) (arrTy N)}
    (hrun : (lanesChainVia opt).run m = some rp) (a₁ o₁ a₂ o₂ : Fin N → BitVec 64)
    (he : MultiReturnCom.ctLeak (jLeakModel Pj) m (arrLimbs a₁ N 0) =
      MultiReturnCom.ctLeak (jLeakModel Pj) m (arrLimbs a₂ N 0)) :
    RouteProg.ctLeak Pj rp (.cons a₁ (.cons o₁ .nil)) =
      RouteProg.ctLeak Pj rp (.cons a₂ (.cons o₂ .nil)) := by
  obtain ⟨m₁, m₂, h₁, h₂, hm⟩ := (lanesChainViaCTCert Pj hV hN opt hopt).ct
    (W₁ := .cons a₁ (.cons o₁ .nil)) (W₂ := .cons a₂ (.cons o₂ .nil)) hrun
    ⟨(arrLimbs a₁ N 0, arrLimbs a₂ N 0), ⟨rfl, rfl⟩,
      (.cons a₁ (.cons o₁ .nil), .cons a₂ (.cons o₂ .nil)),
      ⟨⟨a₁, o₁, rfl, rfl⟩, ⟨a₂, o₂, rfl, rfl⟩⟩,
      (.cons a₁ (.cons o₁ .nil), .cons a₂ (.cons o₂ .nil)), ⟨rfl, rfl⟩, rfl⟩
    rfl rfl he
  exact (Option.some.inj h₁).trans (hm.trans (Option.some.inj h₂).symm)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)

section GvnMultiLeak

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op]

/-- **Leakage of value numbering of multi-result programs.** Under tables sound for `V₁` and
    `V₂`, equal events of the input at the pulled-back valuations give equal events of the
    output. -/
theorem gvnMRGo_ctLeak (L : LeakModel d) (pure : d.Op → Bool) : ∀ {Γ Δ : Ctxt d}
    {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (M : Tbl d) (m : MultiReturnCom d Γ ts)
    (V₁ V₂ : Ctxt.Valuation Δ), Sound V₁ M → Sound V₂ M →
    MultiReturnCom.ctLeak L m (V₁.comap ρ) = MultiReturnCom.ctLeak L m (V₂.comap ρ) →
    MultiReturnCom.ctLeak L (gvnMRGo pure ρ M m) V₁ =
      MultiReturnCom.ctLeak L (gvnMRGo pure ρ M m) V₂
  | _, _, _, ρ, _, .ret vs, _, _, _, _, _ => rfl
  | _, Δ, _, ρ, M, .var (t := s) e body, V₁, V₂, h₁, h₂, h => by
      simp only [MultiReturnCom.ctLeak] at h
      obtain ⟨hE, hB⟩ := List.append_inj h (opLeak_length L e.op _ _)
      simp only [gvnMRGo]
      rcases hc : findVar pure Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [MultiReturnCom.ctLeak]
        rw [Expr.ctLeak_rename, Expr.ctLeak_rename, hE]
        congr 1
        refine gvnMRGo_ctLeak L pure ρ.lift _ body _ _ (sound_insertT h₁ (e.rename ρ))
          (sound_insertT h₂ (e.rename ρ)) ?_
        rw [Ctxt.Valuation.extend_comap_lift, Ctxt.Valuation.extend_comap_lift,
          Expr.denote_rename, Expr.denote_rename]
        exact hB
      · have hw : ∀ V : Ctxt.Valuation Δ, Sound V M → w.lookup V = e.denote (V.comap ρ) := by
          intro V hV
          rw [← Expr.denote_rename ρ e V]
          exact findVar_expr hV hc
        refine gvnMRGo_ctLeak L pure (consHom w ρ) M body V₁ V₂ h₁ h₂ ?_
        rw [comap_consHom, comap_consHom, hw V₁ h₁, hw V₂ h₂]
        exact hB

/-- **Leakage of value numbering of multi-result programs.** Equal events of `m` at two
    valuations give equal events of `gvnMR pure m` there. -/
theorem gvnMR_ctLeak_eq (L : LeakModel d) (pure : d.Op → Bool) {Γ : Ctxt d}
    {ts : List d.Ty} (m : MultiReturnCom d Γ ts) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : MultiReturnCom.ctLeak L m V₁ = MultiReturnCom.ctLeak L m V₂) :
    MultiReturnCom.ctLeak L (gvnMR pure m) V₁ = MultiReturnCom.ctLeak L (gvnMR pure m) V₂ :=
  gvnMRGo_ctLeak L pure _ _ m V₁ V₂ (sound_empty V₁) (sound_empty V₂)
    (by rw [Ctxt.Valuation.comap_id, Ctxt.Valuation.comap_id]; exact h)

end GvnMultiLeak

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy arrLimbs)
open CatCrypt.Crypto.SecureCompilation.Haxc (RouteProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute (lanesCtx)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (gvnMR_ctLeak_eq)

variable {N : Nat}

/-- The value numbering emits equal events at two valuations where its input does
    (`gvnMR_ctLeak_eq`). -/
theorem gvnStep_ctLeak (Pj : JLeakParams) (pure : jasminDialect.Op → Bool)
    (m q : MultiReturnCom jasminDialect (Rn N) (Rn N))
    (hf : (gvnStep pure (Rn N) (Rn N)).run m = some q) :
    ∀ V₁ V₂, MultiReturnCom.ctLeak (jLeakModel Pj) m V₁ =
      MultiReturnCom.ctLeak (jLeakModel Pj) m V₂ →
    MultiReturnCom.ctLeak (jLeakModel Pj) q V₁ = MultiReturnCom.ctLeak (jLeakModel Pj) q V₂ := by
  cases hf
  exact gvnMR_ctLeak_eq _ pure m

/-- **The constant-time certificate of the lane chain**, at the leakage parameters `Pj` of
    `jasminDialect` with no variable-time operation: `lanesChainViaCTCert` at the value
    numbering, with its obligation `gvnStep_ctLeak`. -/
def lanesChainCTCert (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (hN : N < 2 ^ 64)
    (pure : jasminDialect.Op → Bool) :
    CTCert (lanesChain N pure) (mrLeakSem (jLeakModel Pj) (Rn N) (Rn N))
      (routeProgLeakSem Pj (lanesCtx N) (arrTy N)) :=
  lanesChainViaCTCert Pj hV hN (gvnStep pure _ _) (gvnStep_ctLeak Pj pure)

/-- **Constant time through the lane chain.** A lane program `m` that emits equal events at
    the words of the input arrays `a₁` and `a₂` gives a route program
    `(lanesChain N pure).run m` that emits equal events at the input arrays `a₁`, `a₂` and
    arbitrary output arrays `o₁`, `o₂`; this is `PassChain.CTCert.ct` at
    `lanesChainCTCert`. -/
theorem lanesChain_ct (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (hN : N < 2 ^ 64)
    (pure : jasminDialect.Op → Bool)
    {m : MultiReturnCom jasminDialect (Rn N) (Rn N)} {rp : RouteProg (lanesCtx N) (arrTy N)}
    (hrun : (lanesChain N pure).run m = some rp) (a₁ o₁ a₂ o₂ : Fin N → BitVec 64)
    (he : MultiReturnCom.ctLeak (jLeakModel Pj) m (arrLimbs a₁ N 0) =
      MultiReturnCom.ctLeak (jLeakModel Pj) m (arrLimbs a₂ N 0)) :
    RouteProg.ctLeak Pj rp (.cons a₁ (.cons o₁ .nil)) =
      RouteProg.ctLeak Pj rp (.cons a₂ (.cons o₂ .nil)) := by
  obtain ⟨m₁, m₂, h₁, h₂, hm⟩ := (lanesChainCTCert Pj hV hN pure).ct
    (W₁ := .cons a₁ (.cons o₁ .nil)) (W₂ := .cons a₂ (.cons o₂ .nil)) hrun
    ⟨(arrLimbs a₁ N 0, arrLimbs a₂ N 0), ⟨rfl, rfl⟩,
      (.cons a₁ (.cons o₁ .nil), .cons a₂ (.cons o₂ .nil)),
      ⟨⟨a₁, o₁, rfl, rfl⟩, ⟨a₂, o₂, rfl, rfl⟩⟩,
      (.cons a₁ (.cons o₁ .nil), .cons a₂ (.cons o₂ .nil)), ⟨rfl, rfl⟩, rfl⟩
    rfl rfl he
  exact (Option.some.inj h₁).trans (hm.trans (Option.some.inj h₂).symm)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain
