/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak

/-!
# The leakage transformer of the lowering of `NFProg catCryptDialect` to `jasminDialect`

The lowering of a program of `NFProg catCryptDialect` with one result to `jasminDialect`
takes one of two forms: a straight-line program (`NFProg.toCom?`) lowered by
`cryptoDialectToJasminCom`, or a looped program `ComL` (`NFProgCatToJasmin.nfToComLVia`). In
both forms the lowered program, on the transported valuation `ctMapValD V`, leaks the events
of the source run `NFProg.leakRun` from `V`: the leakage transformer is the identity.

The transport `ctMapValD` is onto, with the section `ctBackV`. A leakage function of the
lowered program that factors through the source leakage is therefore constant time for the
transported labels `mapLabels L` whenever the source is constant time for `L`
(`constantTime_of_transport`).

## Main definitions

* `mapLabels` — the labels of the transported context.
* `ctBackTy`, `ctBackV` — the sections of `ctTransTy` and `ctMapValD`.

## Main results

* `NFProg.leakRun_of_toCom?` — a straight-line program runs to its denotation and its
  `Com.ctLeak` events.
* `comRestrict_ctLeak` — restriction to a selection of variables keeps the events.
* `ctLeak_comToComL` — the embedding `comToComL` of a straight-line program keeps the events.
* `NFLeakLower.jasminNFToComLAt_ctLeak` — the looped export of `NFProg jasminDialect`
  leaks the events of the program.
* `nfToComLVia_ctLeak` — the looped lowering leaks the source events.
* `toComJ_ctLeak` — the straight-line lowering leaks the source events.
* `constantTime_of_transport`, `comLCT_of_nfCT`, `comCT_of_nfCT` — constant time of the
  source for `L` gives constant time of the lowered program for `mapLabels L`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD ctMapValD_lookup
  ctMapValD_extend cryptoDialectToJasminCom_denote_eq')
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (jasminNFToComLAt jforNode
  nfToComLVia catToJasmin_map?_ctLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open MultiBlockLowering (hvAppend)

/-! ## Straight-line programs and restriction -/

section Generic

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- A program `toComAt` reads as the straight-line program `c` runs to the denotation of `c`
    and to the events of `c`. -/
theorem NFProg.leakRun_of_toComAt (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (t : d.Ty) (h : ts = [t]) {c : Com d Γ t}
    (hc : p.toComAt t h = some c) (V : Ctxt.Valuation Γ) :
    NFProg.leakRun M fuel p V = some (h ▸ .cons (c.denote V) .nil, Com.ctLeak M c V) := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      simp only [NFProg.toComAt, Option.some.injEq] at hc
      subst hc
      rfl
  | var e k ih =>
      simp only [NFProg.toComAt, Option.map_eq_some_iff] at hc
      obtain ⟨c', hk, rfl⟩ := hc
      subst h
      simp only [NFProg.leakRun, ih rfl hk, Option.map_some]
      rfl
  | forLoop => simp [NFProg.toComAt] at hc
  | ifThenElse => simp [NFProg.toComAt] at hc
  | whileLoop => simp [NFProg.toComAt] at hc
  | call => simp [NFProg.toComAt] at hc

/-- A program `toCom?` reads as the straight-line program `c` runs to the denotation of `c`
    and to the events of `c`. -/
theorem NFProg.leakRun_of_toCom? (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {t : d.Ty}
    (p : NFProg d Γ [t]) {c : Com d Γ t} (hc : p.toCom? = some c) (V : Ctxt.Valuation Γ) :
    NFProg.leakRun M fuel p V = some (.cons (c.denote V) .nil, Com.ctLeak M c V) :=
  NFProg.leakRun_of_toComAt M fuel p t rfl hc V

omit [HasWord64 d] [HasBoolBit d] in
/-- **Restriction keeps the events.** A program restricted along `f` leaks, at a valuation
    `f` relates, the events of the program. -/
theorem comRestrict_ctLeak (M : LeakModel d) : {Γ Γ' : Ctxt d} → {u : d.Ty} →
    (c : Com d Γ u) → (f : VMap Γ Γ') → (c' : Com d Γ' u) → comRestrict c f = some c' →
    (V : Ctxt.Valuation Γ) → (V' : Ctxt.Valuation Γ') → VMap.Agree f V V' →
    Com.ctLeak M c' V' = Com.ctLeak M c V
  | _, _, _, .ret v, f, c', h, V, V', _ => by
      obtain ⟨w, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
  | _, _, _, .var e k, f, c', h, V, V', hag => by
      obtain ⟨as, has, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      have hargs := VMap.lookupArgs_args hag e.args as has
      have he : (⟨e.op, e.retTy_eq, as⟩ : Expr d _ _).denote V' = e.denote V := by
        unfold Expr.denote
        rw [hargs]
      change Expr.ctLeak M (⟨e.op, e.retTy_eq, as⟩ : Expr d _ _) V' ++
          Com.ctLeak M k' (V'.extend ((⟨e.op, e.retTy_eq, as⟩ : Expr d _ _).denote V')) =
        Expr.ctLeak M e V ++ Com.ctLeak M k (V.extend (e.denote V))
      rw [he, comRestrict_ctLeak M k (VMap.lift f) k' hk' _ _ (VMap.agree_lift hag _)]
      unfold Expr.ctLeak
      rw [hargs]

end Generic

/-! ## The embedding of a straight-line program -/

/-- The events of the embedding `comToComL` of a straight-line program are the events of the
    program. -/
theorem ctLeak_comToComL (M : LeakModel jasminDialect) : {Γ : Ctxt jasminDialect} →
    {t : JasminTy} → (c : Com jasminDialect Γ t) → (V : Ctxt.Valuation Γ) →
    ComL.ctLeak M (comToComL c) V = Com.ctLeak M c V
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, V =>
      congrArg (Expr.ctLeak M e V ++ ·) (ctLeak_comToComL M body (V.extend (e.denote V)))

/-! ## The looped lowering -/

/-- **The leakage of the looped export.** When `jasminNFToComLAt p t h = some c`, the
    program `p` runs from `W` to some results and events, and `c` leaks those events. -/
protected theorem jasminNFToComLAt_ctLeak (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (t : JasminTy) (h : ts = [t]) (c : ComL Γ t) (hc : jasminNFToComLAt p t h = some c)
    (W : Ctxt.Valuation Γ) :
    ∃ r, NFProg.leakRun M fuel p W = some r ∧ ComL.ctLeak M c W = r.2 := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      have hr : jasminNFToComLAt (.ret (.cons v .nil)) t rfl = some (.ret v) := rfl
      rw [hr, Option.some.injEq] at hc
      subst hc
      exact ⟨_, rfl, rfl⟩
  | var e k ih =>
      subst h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hc
      obtain ⟨r, hr, hr'⟩ := ih rfl k' hk' (W.extend (e.denote W))
      refine ⟨(r.1, Expr.ctLeak M e W ++ r.2), ?_, ?_⟩
      · simp only [NFProg.leakRun, hr, Option.map_some]
      · change Expr.ctLeak M e W ++ ComL.ctLeak M k' (W.extend (e.denote W)) = _
        rw [hr']
  | forLoop count inits body k _ ihk =>
      obtain ⟨k', hk, hc⟩ := Option.bind_eq_some_iff.mp hc
      rcases inits with _ | ⟨init, _ | _⟩
      · simp [jforNode] at hc
      · obtain ⟨bc, hbc, hc⟩ := Option.bind_eq_some_iff.mp hc
        obtain ⟨bc', hr, rfl⟩ := Option.map_eq_some_iff.mp hc
        have hsel : ∀ (a : ⟦_⟧) (i : Nat),
            bc'.denote (.cons a (.cons (BitVec.ofNat 64 i) (Expr.lookupArgs (usedSel bc).2 W))) =
              bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)) := fun a i =>
          comRestrict_denote bc _ bc' hr _ _
            (VMap.agree_lift (VMap.agree_lift (findIn_agree W (usedSel bc).2) _) _)
        have hselL : ∀ (a : ⟦_⟧) (i : Nat),
            Com.ctLeak M bc'
                (.cons a (.cons (BitVec.ofNat 64 i) (Expr.lookupArgs (usedSel bc).2 W))) =
              Com.ctLeak M bc (.cons a (.cons (BitVec.ofNat 64 i) W)) := fun a i =>
          comRestrict_ctLeak _ bc _ bc' hr _ _
            (VMap.agree_lift (VMap.agree_lift (findIn_agree W (usedSel bc).2) _) _)
        have hiter := NFProg.forIterLeak_pure (fun a => .cons a .nil)
          (fun i acc => NFProg.leakRun M fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W)))
          (fun i a => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)))
          (fun i a => Com.ctLeak M bc (.cons a (.cons (BitVec.ofNat 64 i) W)))
          (iterLeak (fun i a => Com.ctLeak M bc (.cons a (.cons (BitVec.ofNat 64 i) W)))
            (fun i a => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W))))
          (fun _ => rfl) (fun _ _ _ => rfl)
          (fun i a => NFProg.leakRun_of_toCom? _ fuel body hbc _)
          (List.range (count.lookup W).toNat) (init.lookup W)
        obtain ⟨r, hrk, hrk'⟩ := ihk h k' hk
          (W.extend ((List.range (count.lookup W).toNat).foldl
            (fun a i => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W))) (init.lookup W)))
        refine ⟨(r.1, .trip (count.lookup W).toNat ::
          (iterLeak (fun i a => Com.ctLeak M bc (.cons a (.cons (BitVec.ofNat 64 i) W)))
            (fun i a => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)))
            (List.range (count.lookup W).toNat) (init.lookup W) ++ r.2)), ?_, ?_⟩
        · simp only [NFProg.leakRun]
          erw [hiter, Option.bind_some]
          change (NFProg.leakRun M fuel k (W.extend _)).map _ = _
          rw [hrk, Option.map_some]
          rfl
        · have hstep : ∀ (i : Nat) (a : ⟦_⟧),
              JLoopBodyN.stepC bc' (Expr.lookupArgs (usedSel bc).2 W) i a =
                bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)) := fun i a => hsel a i
          have hS : (fun i a => JLoopBodyN.stepC bc' (Expr.lookupArgs (usedSel bc).2 W) i a) =
              fun i a => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)) :=
            funext fun i => funext fun a => hstep i a
          have hL : (fun i a => Com.ctLeak M bc'
              (.cons a (.cons (BitVec.ofNat 64 i) (Expr.lookupArgs (usedSel bc).2 W)))) =
              fun i a => Com.ctLeak M bc (.cons a (.cons (BitVec.ofNat 64 i) W)) :=
            funext fun i => funext fun a => hselL a i
          have hX : (List.range (count.lookup W).toNat).foldl
              (fun acc i => JLoopBodyN.stepC bc' (Expr.lookupArgs (usedSel bc).2 W) i acc)
              (init.lookup W) =
              (List.range (count.lookup W).toNat).foldl
                (fun a i => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)))
                (init.lookup W) := by
            simp only [hstep]
          change .trip (count.lookup W).toNat ::
              (iterLeak _ _ (List.range (count.lookup W).toNat) (init.lookup W) ++
                ComL.ctLeak M k' (W.extend
                  ((List.range (count.lookup W).toNat).foldl
                    (fun acc i => JLoopBodyN.stepC bc' (Expr.lookupArgs (usedSel bc).2 W) i acc)
                    (init.lookup W)))) = _
          rw [hX, hrk', hL, hS]
      · simp [jforNode] at hc
  | ifThenElse => simp [jasminNFToComLAt] at hc
  | whileLoop => simp [jasminNFToComLAt] at hc
  | call => simp [jasminNFToComLAt] at hc

/-- **The leakage transformer of the looped lowering.** When `nfToComLVia p = some jcom`,
    the source program runs from `V` to some results and events, and the lowered program on
    the transported valuation leaks those events. -/
theorem nfToComLVia_ctLeak {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (fuel : Nat) {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    (jcom : ComL (mapCtx Γ) (mapTy t)) (hj : nfToComLVia p = some jcom)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ∃ r, NFProg.leakRun (catLeakModel P) fuel p V = some r ∧
      ComL.ctLeak (jLeakModel Pj) jcom (ctMapValD V) = r.2 := by
  obtain ⟨q, hq, hj⟩ := Option.bind_eq_some_iff.mp hj
  obtain ⟨r', hr', he⟩ :=
    NFLeakLower.jasminNFToComLAt_ctLeak (jLeakModel Pj) fuel q (mapTy t) rfl jcom hj (ctMapValD V)
  have hs := catToJasmin_map?_ctLeak hc fuel p q hq V
  erw [hr', Option.map_some] at hs
  rcases hp : NFProg.leakRun (catLeakModel P) fuel p V with _ | r
  · rw [hp] at hs
    cases hs
  · rw [hp, Option.map_some, Option.some.injEq] at hs
    exact ⟨r, rfl, he.trans hs⟩

/-- **The leakage transformer of the straight-line lowering.** A program `toCom?` reads as
    `c`, with `c` lowered to `jc`, runs from `V` to some results and events, and `jc` on the
    transported valuation leaks those events. -/
theorem toComJ_ctLeak {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (fuel : Nat) {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    {c : Com catCryptDialect Γ t} (hp : p.toCom? = some c)
    {jc : Com jasminDialect (mapCtx Γ) (mapTy t)} (hjc : cryptoDialectToJasminCom c = some jc)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ∃ r, NFProg.leakRun (catLeakModel P) fuel p V = some r ∧
      Com.ctLeak (jLeakModel Pj) jc (ctMapValD V) = r.2 :=
  ⟨_, NFProg.leakRun_of_toCom? _ fuel p hp V, cryptoDialectToJasminCom_ctLeak hc c jc hjc V⟩

/-! ## Constant time through the transport -/

/-- The labels of the transported context: each variable keeps its level. -/
def mapLabels : {Γ : Ctx} → Labels (d := catCryptDialect) Γ →
    Labels (d := jasminDialect) (mapCtx Γ)
  | [], .nil => .nil
  | _ :: _, .cons l L => .cons l (mapLabels L)

/-- The section of `ctTransTy`: the identity on words and arrays, the low bit of a bit, and
    the canonical value at the other types. -/
def ctBackTy : (t : CryptoTy) → ⟦mapTy t⟧ → CryptoTy.denote t
  | .sword _, x => x
  | .bit, x => x.getLsbD 0
  | .unit, _ => CryptoTy.default .unit
  | .memref _, x => x
  | .memrefW _ _, x => x
  | .pair a b, _ => CryptoTy.default (.pair a b)
  | .sum a b, _ => CryptoTy.default (.sum a b)

/-- `ctBackTy` is a section of `ctTransTy`. -/
theorem ctTransTy_ctBackTy : (t : CryptoTy) → (x : ⟦mapTy t⟧) → ctTransTy (ctBackTy t x) = x
  | .sword _, _ => rfl
  | .bit, x => by
      have hb : ∀ y : BitVec 1, BitVec.ofBool (y.getLsbD 0) = y := by decide
      exact hb x
  | .unit, x => by
      rw [ctBackTy, CryptoToJasminComCorrect.ctTransTy_default]
      exact BitVec.eq_of_toNat_eq (by have := x.isLt; simp at this ⊢; omega)
  | .memref _, _ => rfl
  | .memrefW _ _, _ => rfl
  | .pair a b, x => by
      rw [ctBackTy, CryptoToJasminComCorrect.ctTransTy_default]
      exact BitVec.eq_of_toNat_eq (by have := x.isLt; simp at this ⊢; omega)
  | .sum a b, x => by
      rw [ctBackTy, CryptoToJasminComCorrect.ctTransTy_default]
      exact BitVec.eq_of_toNat_eq (by have := x.isLt; simp at this ⊢; omega)

/-- The section of `ctMapValD`. -/
def ctBackV : {Γ : Ctx} → Ctxt.Valuation (d := jasminDialect) (mapCtx Γ) →
    Ctxt.Valuation (d := catCryptDialect) Γ
  | [], .nil => .nil
  | t :: _, .cons x W => .cons (ctBackTy t x) (ctBackV W)

/-- `ctBackV` is a section of `ctMapValD`. -/
theorem ctMapValD_ctBackV : {Γ : Ctx} → (W : Ctxt.Valuation (d := jasminDialect) (mapCtx Γ)) →
    ctMapValD (ctBackV W) = W
  | [], .nil => rfl
  | t :: _, .cons x W => by
      change HVector.cons (ctTransTy (ctBackTy t x)) (ctMapValD (ctBackV W)) = _
      rw [ctTransTy_ctBackTy, ctMapValD_ctBackV W]

/-- A variable reads in `ctBackV W` the section of what its lowering reads in `W`. -/
theorem lookup_ctBackV : {Γ : Ctx} → {s : CryptoTy} →
    (v : Ctxt.Var (d := catCryptDialect) Γ s) →
    (W : Ctxt.Valuation (d := jasminDialect) (mapCtx Γ)) →
    v.lookup (ctBackV W) = ctBackTy s ((toJVarD v).lookup W)
  | _ :: _, _, .here, .cons _ _ => rfl
  | _ :: _, _, .there v, .cons _ W => lookup_ctBackV v W

/-- A lowered variable has the level of the variable. -/
theorem lvlOf_mapLabels : {Γ : Ctx} → {s : CryptoTy} →
    (v : Ctxt.Var (d := catCryptDialect) Γ s) → (L : Labels (d := catCryptDialect) Γ) →
    lvlOf (toJVarD v) (mapLabels L) = lvlOf v L
  | _ :: _, _, .here, .cons _ _ => rfl
  | _ :: _, _, .there v, .cons _ L => lvlOf_mapLabels v L

/-- Valuations of the transported context that agree on the public positions of
    `mapLabels L` have sections that agree on the public positions of `L`. -/
theorem pubEqV_ctBackV {Γ : Ctx} {L : Labels (d := catCryptDialect) Γ}
    {W₁ W₂ : Ctxt.Valuation (d := jasminDialect) (mapCtx Γ)} (h : PubEqV (mapLabels L) W₁ W₂) :
    PubEqV L (ctBackV W₁) (ctBackV W₂) := by
  intro s v hv
  rw [lookup_ctBackV, lookup_ctBackV, h _ (toJVarD v) ((lvlOf_mapLabels v L).trans hv)]

/-- **Constant time through the transport.** A leakage function `f` of the transported
    context whose value at `ctMapValD V` is the trace of a run `g V` is constant time for
    `mapLabels L` when the traces of `g` are equal at valuations that agree on the public
    positions of `L`. -/
theorem constantTime_of_transport {Γ : Ctx} {α : Type} (L : Labels (d := catCryptDialect) Γ)
    (f : Ctxt.Valuation (d := jasminDialect) (mapCtx Γ) → List CTLeak)
    (g : Ctxt.Valuation (d := catCryptDialect) Γ → Option (α × List CTLeak))
    (hg : ∀ V₁ V₂, PubEqV L V₁ V₂ → (g V₁).map Prod.snd = (g V₂).map Prod.snd)
    (hf : ∀ V, ∃ r, g V = some r ∧ f (ctMapValD V) = r.2) :
    ConstantTime (PubEqV (mapLabels L)) f := by
  intro W₁ W₂ h
  rw [← ctMapValD_ctBackV W₁, ← ctMapValD_ctBackV W₂]
  obtain ⟨r₁, h₁, e₁⟩ := hf (ctBackV W₁)
  obtain ⟨r₂, h₂, e₂⟩ := hf (ctBackV W₂)
  have hs := hg _ _ (pubEqV_ctBackV h)
  rw [h₁, h₂, Option.map_some, Option.map_some, Option.some.injEq] at hs
  rw [e₁, e₂, hs]

/-- **Constant time of the looped lowering.** A program constant time for `L` lowers to a
    looped program constant time for `mapLabels L`. -/
theorem comLCT_of_nfCT {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (fuel : Nat) {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    (L : Labels (d := catCryptDialect) Γ) (hct : NFCT (catLeakModel P) L fuel p)
    (jcom : ComL (mapCtx Γ) (mapTy t)) (hj : nfToComLVia p = some jcom) :
    ComLCT (jLeakModel Pj) (mapLabels L) jcom :=
  constantTime_of_transport L _ _ hct (nfToComLVia_ctLeak hc fuel p jcom hj)

/-- **Constant time of the straight-line lowering.** A program constant time for `L` that
    reads as the straight-line program `c` lowers to a program constant time for
    `mapLabels L`. -/
theorem comCT_of_nfCT {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (fuel : Nat) {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    (L : Labels (d := catCryptDialect) Γ) (hct : NFCT (catLeakModel P) L fuel p)
    {c : Com catCryptDialect Γ t} (hp : p.toCom? = some c)
    {jc : Com jasminDialect (mapCtx Γ) (mapTy t)} (hjc : cryptoDialectToJasminCom c = some jc) :
    ComCT (jLeakModel Pj) (mapLabels L) jc :=
  constantTime_of_transport L _ _ hct (toComJ_ctLeak hc fuel p hp hjc)

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
