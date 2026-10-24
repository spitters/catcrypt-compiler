/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMapM
public import CatCrypt.Crypto.Hax.NFInline

/-!
# The events of the blocks of `map?`, and dead-binding elimination at call environments

A lowering `NFProg.map? P hT p ren` along a partial block lowering `P` replaces each binding
of an expression by the block `P` gives it. When the target dialect has operations whose
events are not those of the source, the leakage run of the lowered program is the run of the
source at the event function `blockEv P mapVal M'`, under which an expression emits the
events of its block at the transported valuation (`map?_leakRunMC_blockEv`). Two runs at an
event function `ev` that emits a number of events fixed by the expression are matched by runs
at an event function `ev'` that emits equal events where `ev` does, and equal `ev` events
give equal `ev'` events (`leakRunMC_prefix_ev`).

The call environments of the source and of the lowered program are required to agree along
the transport at the calls of the program only, as in `NFProg.map?_refinesAtM`.

Dead-binding elimination at call environments: a successful leakage run of `p` at `E` is
matched by a leakage run of `dce p` at every environment `E'` that agrees with `E` at the
calls of `p`, to the same results and with the events `NFProg.dceEraseC` keeps
(`NFProg.leakRunMC_dce`); equal source events give equal events after `dce`
(`NFProg.dce_ctRelC`).

## Main definitions

* `blockEv` — the events of the blocks of a lowering.
* `Com.ctLeakO`, `blockEvO` — the events of a block that may fail, and of the blocks of a
  lowering into a dialect that denotes in `Option`.
* `NFProg.dceEraseC` — the erasure of dead-binding elimination on traces of runs at a call
  environment.

## Main results

* `leakRunMC_prefix_ev` — runs at two event functions whose events agree on agreeing events.
* `map?_leakRunMC_blockEv` — the leakage run of `map?` at the events of the blocks.
* `spliceNF?_leakRunMCO`, `map?_leakRunMC_blockEvO` — the leakage runs of a splice and of
  `map?` into a dialect that denotes in `Option`.
* `NFProg.leakRunMC_dce` — the leakage transformer of `dce` at call environments.
* `NFProg.dce_ctRelC` — equal source events give equal events after `dce`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (ExprEv forIterLeak whileIterLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak.NFProg (leakRunMC)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)

/-! ## Runs at two event functions, and the events of `map?` -/

section BlockEv

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option]

/-- **Two event functions whose events agree on agreeing events.** Let `ev` emit a number
    of events fixed by the expression, and let `ev'` emit equal events at two valuations
    where `ev` does. Two runs at `E` with the events `ev` give two runs with the events
    `ev'` to the same results, and when the `ev` events of the two runs, each followed by a
    list, are equal, the `ev'` events of the two runs are equal and so are the two lists. -/
theorem leakRunMC_prefix_ev (ev ev' : ExprEv d)
    (hlen : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V₁ V₂ : Valuation Γ),
      (ev.ev _ _ e V₁).length = (ev.ev _ _ e V₂).length)
    (hfix : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V₁ V₂ : Valuation Γ),
      ev.ev _ _ e V₁ = ev.ev _ _ e V₂ → ev'.ev _ _ e V₁ = ev'.ev _ _ e V₂)
    (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {V₁ V₂ : Valuation Γ} {r₁ r₂ : Valuation ts × List CTLeak},
      leakRunMC ev E fuel p V₁ = some r₁ → leakRunMC ev E fuel p V₂ = some r₂ →
      ∃ l₁ l₂, leakRunMC ev' E fuel p V₁ = some (r₁.1, l₁) ∧
        leakRunMC ev' E fuel p V₂ = some (r₂.1, l₂) ∧
        ∀ s₁ s₂ : List CTLeak, r₁.2 ++ s₁ = r₂.2 ++ s₂ → l₁ = l₂ ∧ s₁ = s₂ := by
  induction p with
  | ret vs =>
      intro V₁ V₂ r₁ r₂ h₁ h₂
      simp only [leakRunMC, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨[], [], rfl, rfl, fun s₁ s₂ hs => ⟨rfl, by simpa using hs⟩⟩
  | var e k ih =>
      intro V₁ V₂ r₁ r₂ h₁ h₂
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨x₁, hx₁, u₁, hu₁, rfl⟩ := h₁
      obtain ⟨x₂, hx₂, u₂, hu₂, rfl⟩ := h₂
      obtain ⟨l₁, l₂, hl₁, hl₂, hl⟩ := ih hu₁ hu₂
      refine ⟨ev'.ev _ _ e V₁ ++ l₁, ev'.ev _ _ e V₂ ++ l₂, ?_, ?_, fun s₁ s₂ hs => ?_⟩
      · simp only [leakRunMC, hx₁, Option.bind_some, hl₁, Option.map_some]
      · simp only [leakRunMC, hx₂, Option.bind_some, hl₂, Option.map_some]
      · rw [List.append_assoc, List.append_assoc] at hs
        obtain ⟨he, hs⟩ := List.append_inj hs (hlen e V₁ V₂)
        obtain ⟨rfl, rfl⟩ := hl _ _ hs
        exact ⟨by rw [hfix e V₁ V₂ he], rfl⟩
  | forLoop count inits body k ihb ihk =>
      intro V₁ V₂ r₁ r₂ h₁ h₂
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨a₁, ha₁, u₁, hu₁, rfl⟩ := h₁
      obtain ⟨a₂, ha₂, u₂, hu₂, rfl⟩ := h₂
      have hit := fun (W₁ W₂ : Valuation _) =>
        NFProg.forIterLeak_prefix
          (fun i acc => leakRunMC ev E fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W₁)))
          (fun i acc => leakRunMC ev E fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W₂)))
          (fun i acc => leakRunMC ev' E fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W₁)))
          (fun i acc => leakRunMC ev' E fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W₂)))
          (fun i X₁ X₂ u₁ u₂ h₁ h₂ => ihb h₁ h₂)
      obtain ⟨m₁, -, hm₁, -, -⟩ := hit V₁ V₁ _ _ _ a₁ a₁ ha₁ ha₁
      obtain ⟨m₂, -, hm₂, -, -⟩ := hit V₂ V₂ _ _ _ a₂ a₂ ha₂ ha₂
      obtain ⟨n₁, n₂, hn₁, hn₂, hn⟩ := ihk hu₁ hu₂
      refine ⟨.trip (HasWord64.toNat (d := d) (count.lookup V₁)) :: (m₁ ++ n₁),
        .trip (HasWord64.toNat (d := d) (count.lookup V₂)) :: (m₂ ++ n₂), ?_, ?_,
        fun s₁ s₂ hs => ?_⟩
      · simp only [leakRunMC, hm₁, Option.bind_some, hn₁, Option.map_some]
      · simp only [leakRunMC, hm₂, Option.bind_some, hn₂, Option.map_some]
      · simp only [List.cons_append, List.append_assoc, List.cons.injEq,
          CTLeak.trip.injEq] at hs
        obtain ⟨hc, hs⟩ := hs
        rw [← hc] at ha₂
        obtain ⟨m₁', m₂', hm₁', hm₂', hm⟩ := hit V₁ V₂ _ _ _ a₁ a₂ ha₁ ha₂
        rw [hm₁, Option.some.injEq, Prod.mk.injEq] at hm₁'
        rw [hc, hm₂, Option.some.injEq, Prod.mk.injEq] at hm₂'
        obtain ⟨-, rfl⟩ := hm₁'
        obtain ⟨-, rfl⟩ := hm₂'
        obtain ⟨rfl, hs⟩ := hm _ _ hs
        obtain ⟨rfl, rfl⟩ := hn _ _ hs
        exact ⟨by rw [hc], rfl⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro V₁ V₂ r₁ r₂ h₁ h₂
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨a₁, ha₁, u₁, hu₁, rfl⟩ := h₁
      obtain ⟨a₂, ha₂, u₂, hu₂, rfl⟩ := h₂
      have hbr : ∀ (W₁ W₂ : Valuation _) (c : Bool) (b₁ b₂ : Valuation _ × List CTLeak),
          (if c then leakRunMC ev E fuel thn W₁ else leakRunMC ev E fuel els W₁) = some b₁ →
          (if c then leakRunMC ev E fuel thn W₂ else leakRunMC ev E fuel els W₂) = some b₂ →
          ∃ m₁ m₂, (if c then leakRunMC ev' E fuel thn W₁ else leakRunMC ev' E fuel els W₁) =
              some (b₁.1, m₁) ∧
            (if c then leakRunMC ev' E fuel thn W₂ else leakRunMC ev' E fuel els W₂) =
              some (b₂.1, m₂) ∧
            ∀ s₁ s₂ : List CTLeak, b₁.2 ++ s₁ = b₂.2 ++ s₂ → m₁ = m₂ ∧ s₁ = s₂ := by
        intro W₁ W₂ c b₁ b₂ h₁ h₂
        cases c
        · simp only [Bool.false_eq_true, ite_false] at h₁ h₂ ⊢
          exact ihe h₁ h₂
        · simp only [ite_true] at h₁ h₂ ⊢
          exact iht h₁ h₂
      obtain ⟨m₁, -, hm₁, -, -⟩ := hbr V₁ V₁ _ a₁ a₁ ha₁ ha₁
      obtain ⟨m₂, -, hm₂, -, -⟩ := hbr V₂ V₂ _ a₂ a₂ ha₂ ha₂
      obtain ⟨n₁, n₂, hn₁, hn₂, hn⟩ := ihk hu₁ hu₂
      refine ⟨.branch (HasBoolBit.toBool (d := d) (cond.lookup V₁)) :: (m₁ ++ n₁),
        .branch (HasBoolBit.toBool (d := d) (cond.lookup V₂)) :: (m₂ ++ n₂), ?_, ?_,
        fun s₁ s₂ hs => ?_⟩
      · simp only [leakRunMC, hm₁, Option.bind_some, hn₁, Option.map_some]
      · simp only [leakRunMC, hm₂, Option.bind_some, hn₂, Option.map_some]
      · simp only [List.cons_append, List.append_assoc, List.cons.injEq,
          CTLeak.branch.injEq] at hs
        obtain ⟨hc, hs⟩ := hs
        rw [← hc] at ha₂ hm₂
        obtain ⟨m₁', m₂', hm₁', hm₂', hm⟩ := hbr V₁ V₂ _ a₁ a₂ ha₁ ha₂
        rw [hm₁, Option.some.injEq, Prod.mk.injEq] at hm₁'
        rw [hm₂, Option.some.injEq, Prod.mk.injEq] at hm₂'
        obtain ⟨-, rfl⟩ := hm₁'
        obtain ⟨-, rfl⟩ := hm₂'
        obtain ⟨rfl, hs⟩ := hm _ _ hs
        obtain ⟨rfl, rfl⟩ := hn _ _ hs
        exact ⟨by rw [hc], rfl⟩
  | whileLoop inits body k ihb ihk =>
      intro V₁ V₂ r₁ r₂ h₁ h₂
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨a₁, ha₁, u₁, hu₁, rfl⟩ := h₁
      obtain ⟨a₂, ha₂, u₂, hu₂, rfl⟩ := h₂
      have hex : ∀ (W : Valuation _) X u, leakRunMC ev E fuel body (hvAppend X W) = some u →
          ∃ m, leakRunMC ev' E fuel body (hvAppend X W) = some (u.1, m) := fun W X u hu => by
        obtain ⟨m, -, hm, -, -⟩ := ihb hu hu
        exact ⟨m, hm⟩
      obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := NFProg.whileIterLeak_prefix
        (fun acc => leakRunMC ev E fuel body (hvAppend acc V₁))
        (fun acc => leakRunMC ev E fuel body (hvAppend acc V₂))
        (fun acc => leakRunMC ev' E fuel body (hvAppend acc V₁))
        (fun acc => leakRunMC ev' E fuel body (hvAppend acc V₂))
        (hex V₁) (hex V₂) (fun X₁ X₂ u₁ u₂ h₁ h₂ => ihb h₁ h₂) _ _ _ a₁ a₂ ha₁ ha₂
      obtain ⟨n₁, n₂, hn₁, hn₂, hn⟩ := ihk hu₁ hu₂
      refine ⟨m₁ ++ n₁, m₂ ++ n₂, ?_, ?_, fun s₁ s₂ hs => ?_⟩
      · simp only [leakRunMC, hm₁, Option.bind_some, hn₁, Option.map_some]
      · simp only [leakRunMC, hm₂, Option.bind_some, hn₂, Option.map_some]
      · simp only [List.append_assoc] at hs
        obtain ⟨rfl, hs⟩ := hm _ _ hs
        obtain ⟨rfl, rfl⟩ := hn _ _ hs
        exact ⟨rfl, rfl⟩
  | call f args k ih =>
      intro V₁ V₂ r₁ r₂ h₁ h₂
      simp only [leakRunMC, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨y₁, hy₁, hu₁⟩ := h₁
      obtain ⟨y₂, hy₂, hu₂⟩ := h₂
      obtain ⟨l₁, l₂, hl₁, hl₂, hl⟩ := ih hu₁ hu₂
      exact ⟨l₁, l₂, by simp only [leakRunMC, hy₁, Option.bind_some, hl₁],
        by simp only [leakRunMC, hy₂, Option.bind_some, hl₂], hl⟩

variable {d' : Dialect.{0, 0}} [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d']
  [HasBoolBit d'] [DialectDenote d']

/-- **The events of the blocks of a lowering**: an expression emits the events of its block
    at the transported valuation, and none when the lowering refuses it. -/
def blockEv (P : PartialBlockLowering d d') (mapVal : P.MapVal)
    (M' : LeakModel d') : ExprEv d :=
  ⟨fun _ _ e V => match P.lowerExprBlock? e with
    | some blk => ComLevelCheck.Com.ctLeak M' blk (mapVal V)
    | none => []⟩

/-- **The leakage run of `map?` at the events of the blocks**, forward form. Under the
    variable leaf, the forward block leaf, the binding-threading leaf, `RegionTransports`, and
    the agreement `hCall` of the call environments along the transport at the calls of `p`, a
    program `map?` returns, at a renaming reading back the transported `V`, runs at `E'` to
    the transported results and to the events of a successful source run at `E` with the
    events `blockEv P mapVal M'`. -/
theorem map?_leakRunMC_blockEv (P : PartialBlockLowering d d') (transTy : P.TransTy)
    (mapVal : P.MapVal) (M' : LeakModel d') (hT : P.RegionTypes)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) blk, P.lowerExprBlock? e = some blk →
      ∀ (V : Valuation Γ) (x : ⟦t⟧), e.denoteM (M := Option) V = some x →
      blk.denote (mapVal V) = transTy x)
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (E : CallEnv d) (E' : CallEnv d') (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts)
    (hCall : E.Transports E' (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x)
      p.Calls) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      NFProg.RenRel ren W (mapVal V) → ∀ q, NFProg.map? P hT p ren = some q →
      ∀ r, leakRunMC (blockEv P mapVal M') E fuel p V = some r →
      leakRunMC M' E' fuel q W = some (transArgs P.mapTy transTy r.1, r.2) := by
  induction p with
  | ret vs =>
      intro Δ ren V W hren q hq r hr
      cases hq
      simp only [leakRunMC, Option.some.injEq] at hr
      subst hr
      show some _ = some _
      rw [NFProg.lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren]
  | var e k ih =>
      intro Δ ren V W hren q hq r hr
      obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨x, hx, u, hu, rfl⟩ := hr
      have hpull : FieldDialectBlockDescent.pullV ren W = mapVal V :=
        BlockLoweringCPS.valuation_ext _ _ (fun v => by
          rw [BlockLoweringCPS.lookup_pullV]; exact hren v)
      rw [NFProg.spliceNF?_leakRunMC M' E' fuel _ _ W (some (transArgs P.mapTy transTy u.1, u.2))
        (fun ren' res W' h1 h2 q' hq' => ih hCall _ (V.extend x) W'
          (NFProg.renRel_bodyHom P transTy mapVal hExt ren ren' res V x W W' hren h1 (by
            rw [h2, FieldDialectBlockDescent.Com.denote_rename, hpull,
              hBlk e blk hblk V x hx])) q' hq' u hu) q hq,
        NFProg.Com.ctLeak_rename_pullV, hpull]
      simp only [Option.map_some, blockEv, hblk]
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W hren q hq r hr
      have hCb := hCall.mono fun _ _ _ h => Or.inl h
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      obtain ⟨a', ha', hra, hea⟩ := NFProg.forIterLeak_rel_fwd
        (R := fun c c' => c' = transArgs P.mapTy transTy c)
        (step' := fun i acc => leakRunMC M' E' fuel b
          (hvAppend acc (.cons (HasWord64.ofNat (d := d') i) W)))
        _ (fun i _ c c' s hc hs => by
          subst hc
          refine ⟨(transArgs P.mapTy transTy s.1, s.2), ?_, rfl, rfl⟩
          rw [← hR.ofNat_trans i]
          exact ihb hCb _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt _ _ _
            (NFProg.renRel_liftTo P transTy mapVal hExt _ ren V W _ _ hren rfl) _ c) b hbq s hs)
        _ _ a rfl ha
      simp only [leakRunMC]
      rw [NFProg.lookup_varTyCast, hren, hVar, hR.toNat_trans,
        NFProg.lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren, ha']
      simp only [Option.bind_some]
      rw [hra, ihk hCk _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ a.1) k'
        hkq u hu, hea]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W hren q hq r hr
      have hCt := hCall.mono fun _ _ _ h => Or.inl h
      have hCe := hCall.mono fun _ _ _ h => Or.inr (Or.inl h)
      have hCk := hCall.mono fun _ _ _ h => Or.inr (Or.inr h)
      obtain ⟨a', haq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      have harm : (if HasBoolBit.toBool (d := d) (cond.lookup V)
            then leakRunMC M' E' fuel a' W else leakRunMC M' E' fuel b' W) =
          some (transArgs P.mapTy transTy a.1, a.2) := by
        split
        · rename_i hc
          rw [ite_eq_left hc] at ha
          exact iht hCt ren V W hren a' haq a ha
        · rename_i hc
          rw [ite_eq_right hc] at ha
          exact ihe hCe ren V W hren b' hbq a ha
      simp only [leakRunMC]
      rw [NFProg.lookup_varTyCast, hren, hVar, hR.toBool_trans, harm]
      simp only [Option.bind_some]
      rw [ihk hCk _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ a.1) k' hkq
        u hu]
      rfl
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W hren q hq r hr
      have hCb := hCall.mono fun _ _ _ h => Or.inl h
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      obtain ⟨a', ha', hra, hea⟩ := NFProg.whileIterLeak_rel_fwd
        (R := fun c c' => c' = transArgs P.mapTy transTy c)
        (step' := fun acc => leakRunMC M' E' fuel (NFProg.castRetHead hT.bit_eq b)
          (hvAppend acc W))
        (fun c c' s hc hs => by
          subst hc
          rw [NFProg.leakRunMC_castRetHead, ihb hCb _ _ _
            (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ c) b hbq s hs]
          rcases s with ⟨_ | ⟨h0, t0⟩, ev0⟩
          exact ⟨_, rfl, rfl, (hR.toBool_trans h0).symm, rfl⟩)
        fuel _ _ a rfl ha
      simp only [leakRunMC]
      rw [NFProg.lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren, ha']
      simp only [Option.bind_some]
      rw [hra, ihk hCk _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ a.1) k'
        hkq u hu, hea]
      rfl
  | call f args k ih =>
      intro Δ ren V W hren q hq r hr
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff] at hr
      obtain ⟨y, hy, hu⟩ := hr
      simp only [leakRunMC]
      rw [NFProg.lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren,
        hCall f _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩), hy, Option.map_some, Option.bind_some]
      exact ih hCk _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ y) k' hkq r
        hu

end BlockEv

/-! ## The events of `map?` into a dialect that denotes in `Option` -/

section BlockEvO

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option]

/-- **The events of a block that may fail**, at the event function `ev`: each binding emits
    its `ev` events, and the bindings after a failing one emit none. -/
def Com.ctLeakO (ev : ExprEv d) : {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Valuation Γ →
    List CTLeak
  | _, _, .ret _, _ => []
  | _, _, .var e body, V => ev.ev _ _ e V ++
      match e.denoteM (M := Option) V with
      | some x => Com.ctLeakO ev body (V.extend x)
      | none => []

omit [HasWord64 d] [HasBoolBit d] in
/-- A renamed block emits, at a leakage model, the events of the block at a valuation the
    renaming reads back. -/
theorem Com.ctLeakO_rename_of (M : LeakModel d) : {Γ Δ : Ctxt d} → {t : d.Ty} →
    (ren : Ctxt.Hom Γ Δ) → (c : Com d Γ t) → (W : Valuation Δ) → (W₀ : Valuation Γ) →
    NFProg.RenRel ren W W₀ →
    Com.ctLeakO (M : ExprEv d) (Com.rename ren c) W = Com.ctLeakO (M : ExprEv d) c W₀
  | _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, ren, .var e body, W, W₀, h => by
      have he : ComLevelCheck.Expr.ctLeak M (e.rename ren) W =
          ComLevelCheck.Expr.ctLeak M e W₀ := by
        obtain ⟨op, rfl, args⟩ := e
        show ComLevelCheck.opLeak M op (Expr.lookupArgs (HVector.renameVars ren args) W) = _
        rw [NFProg.lookupArgs_renameVars_of h args]
        rfl
      show ComLevelCheck.Expr.ctLeak M (e.rename ren) W ++
          (match (e.rename ren).denoteM (M := Option) W with
            | some x => Com.ctLeakO (M : ExprEv d) (Com.rename ren.lift body) (W.extend x)
            | none => []) =
        ComLevelCheck.Expr.ctLeak M e W₀ ++
          (match e.denoteM (M := Option) W₀ with
            | some x => Com.ctLeakO (M : ExprEv d) body (W₀.extend x)
            | none => [])
      rw [he, NFProg.Expr.denoteM_rename_of h e]
      cases e.denoteM (M := Option) W₀ with
      | none => rfl
      | some x => exact congrArg _ (Com.ctLeakO_rename_of M _ body _ _ (h.lift x))

/-- The statement `NFProg.leakRunMC_castRetHead` at every event function. -/
theorem leakRunMC_castRetHead_ev (ev : ExprEv d) (E : CallEnv d) (fuel : Nat) {Δ : Ctxt d}
    {a b : d.Ty} {ts : List d.Ty} (h : a = b) (p : NFProg d Δ (a :: ts)) (W : Valuation Δ) :
    leakRunMC ev E fuel (NFProg.castRetHead h p) W =
      (leakRunMC ev E fuel p W).map
        (fun r => (.cons (NFProg.tyCast h r.1.head) r.1.tail, r.2)) := by
  subst h
  show leakRunMC ev E fuel p W = _
  cases leakRunMC ev E fuel p W with
  | none => rfl
  | some r =>
      obtain ⟨r1, l⟩ := r
      cases r1
      rfl

/-- **The leakage run of a splice of a block that may fail.** Let the block succeed with `y`
    at `W`, and let every program `k ren res` run to `G` whenever `ren` reads `W` back and
    `res` holds `y`. Every program the splice returns runs to `G` with the events of the block
    in front. -/
theorem spliceNF?_leakRunMCO (ev : ExprEv d) (E : CallEnv d) (fuel : Nat) {ts : List d.Ty} :
    {Δ : Ctxt d} → {a : d.Ty} → (blk : Com d Δ a) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d Δ' ts)) →
    (W : Valuation Δ) → (y : ⟦a⟧) → blk.denoteM (M := Option) W = some y →
    (G : Option (Valuation ts × List CTLeak)) →
    (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (W' : Valuation Δ'),
        NFProg.RenRel ren W' W → res.lookup W' = y →
        ∀ q, k ren res = some q → leakRunMC ev E fuel q W' = G) →
    ∀ q, NFProg.spliceNF? blk k = some q →
      leakRunMC ev E fuel q W = G.map fun r => (r.1, Com.ctLeakO ev blk W ++ r.2)
  | _, _, .ret v, k, W, y, hy, G, hk => by
      intro q hq
      cases hy
      rw [hk (fun x => x) v W (NFProg.renRel_id W) rfl q hq]
      cases G <;> rfl
  | _, _, .var e blk, k, W, y, hy, G, hk => by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      have hd : (Com.var e blk).denoteM (M := Option) W =
          e.denoteM W >>= fun x => blk.denoteM (W.extend x) := rfl
      cases he : e.denoteM (M := Option) W with
      | none =>
          rw [he] at hd
          rw [hd] at hy
          cases hy
      | some x =>
          rw [he] at hd
          have hy' : blk.denoteM (M := Option) (W.extend x) = some y := hd.symm.trans hy
          simp only [leakRunMC, he, Option.bind_some]
          rw [spliceNF?_leakRunMCO ev E fuel blk _ (W.extend x) y hy' G
            (fun ren res W' h1 h2 => hk (fun v => ren (.there v)) res W'
              (fun v => h1 (.there v)) h2) q' hq', Option.map_map]
          cases G with
          | none => rfl
          | some r =>
              show some _ = some _
              simp only [Function.comp, Com.ctLeakO, he, List.append_assoc]

variable {d' : Dialect.{0, 0}} [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d']
  [HasBoolBit d'] [DialectDenoteM d' Option]

/-- **The events of the blocks of a lowering into a dialect that denotes in `Option`**: an
    expression emits the events `Com.ctLeakO ev'` of its block at the transported valuation,
    and none when the lowering refuses it. -/
def blockEvO (P : PartialBlockLowering d d') (mapVal : P.MapVal) (ev' : ExprEv d') : ExprEv d :=
  ⟨fun _ _ e V => match P.lowerExprBlock? e with
    | some blk => Com.ctLeakO ev' blk (mapVal V)
    | none => []⟩

/-- **The leakage run of `map?` at the events of the blocks**, for a target dialect that
    denotes in `Option`. Under the variable leaf, the forward block leaf in the `Option`
    form, the binding-threading leaf, `RegionTransports`, and the agreement `hCall` of the
    call environments along the transport at the calls of `p`, a program `map?` returns, at a
    renaming reading back the transported `V`, runs at `E'` with the events of the leakage
    model `M'` to the transported results and to the events of a successful source run at `E`
    with the events `blockEvO P mapVal M'`. -/
theorem map?_leakRunMC_blockEvO (P : PartialBlockLowering d d') (transTy : P.TransTy)
    (mapVal : P.MapVal) (M' : LeakModel d') (hT : P.RegionTypes)
    (hVar : P.VarTransports transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) blk, P.lowerExprBlock? e = some blk →
      ∀ (V : Valuation Γ) (x : ⟦t⟧), e.denoteM (M := Option) V = some x →
      blk.denoteM (M := Option) (mapVal V) = some (transTy x))
    (hExt : P.MapValExtends transTy mapVal) (hR : P.RegionTransports hT transTy)
    (E : CallEnv d) (E' : CallEnv d') (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts)
    (hCall : E.Transports E' (fun as => as.map P.mapTy) (fun x => transArgs P.mapTy transTy x)
      p.Calls) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (V : Valuation Γ) (W : Valuation Δ),
      NFProg.RenRel ren W (mapVal V) → ∀ q, NFProg.map? P hT p ren = some q →
      ∀ r, leakRunMC (blockEvO P mapVal (M' : ExprEv d')) E fuel p V = some r →
      leakRunMC (M' : ExprEv d') E' fuel q W = some (transArgs P.mapTy transTy r.1, r.2) := by
  induction p with
  | ret vs =>
      intro Δ ren V W hren q hq r hr
      cases hq
      simp only [leakRunMC, Option.some.injEq] at hr
      subst hr
      show some _ = some _
      rw [NFProg.lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren]
  | var e k ih =>
      intro Δ ren V W hren q hq r hr
      obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨x, hx, u, hu, rfl⟩ := hr
      have hB : (Com.rename ren blk).denoteM (M := Option) W = some (transTy x) := by
        rw [NFProg.Com.denoteM_rename_of ren blk W (mapVal V) hren, hBlk e blk hblk V x hx]
      rw [spliceNF?_leakRunMCO (M' : ExprEv d') E' fuel _ _ W _ hB
        (some (transArgs P.mapTy transTy u.1, u.2))
        (fun ren' res W' h1 h2 q' hq' => ih hCall _ (V.extend x) W'
          (NFProg.renRel_bodyHom P transTy mapVal hExt ren ren' res V x W W' hren h1 h2)
          q' hq' u hu) q hq,
        Com.ctLeakO_rename_of M' ren blk W (mapVal V) hren]
      simp only [Option.map_some, blockEvO, hblk]
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W hren q hq r hr
      have hCb := hCall.mono fun _ _ _ h => Or.inl h
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      obtain ⟨a', ha', hra, hea⟩ := NFProg.forIterLeak_rel_fwd
        (R := fun c c' => c' = transArgs P.mapTy transTy c)
        (step' := fun i acc => leakRunMC (M' : ExprEv d') E' fuel b
          (hvAppend acc (.cons (HasWord64.ofNat (d := d') i) W)))
        _ (fun i _ c c' s hc hs => by
          subst hc
          refine ⟨(transArgs P.mapTy transTy s.1, s.2), ?_, rfl, rfl⟩
          rw [← hR.ofNat_trans i]
          exact ihb hCb _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt _ _ _
            (NFProg.renRel_liftTo P transTy mapVal hExt _ ren V W _ _ hren rfl) _ c) b hbq s hs)
        _ _ a rfl ha
      simp only [leakRunMC]
      rw [NFProg.lookup_varTyCast, hren, hVar, hR.toNat_trans,
        NFProg.lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren, ha']
      simp only [Option.bind_some]
      rw [hra, ihk hCk _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ a.1) k'
        hkq u hu, hea]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W hren q hq r hr
      have hCt := hCall.mono fun _ _ _ h => Or.inl h
      have hCe := hCall.mono fun _ _ _ h => Or.inr (Or.inl h)
      have hCk := hCall.mono fun _ _ _ h => Or.inr (Or.inr h)
      obtain ⟨a', haq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      have harm : (if HasBoolBit.toBool (d := d) (cond.lookup V)
            then leakRunMC (M' : ExprEv d') E' fuel a' W
            else leakRunMC (M' : ExprEv d') E' fuel b' W) =
          some (transArgs P.mapTy transTy a.1, a.2) := by
        split
        · rename_i hc
          rw [ite_eq_left hc] at ha
          exact iht hCt ren V W hren a' haq a ha
        · rename_i hc
          rw [ite_eq_right hc] at ha
          exact ihe hCe ren V W hren b' hbq a ha
      simp only [leakRunMC]
      rw [NFProg.lookup_varTyCast, hren, hVar, hR.toBool_trans, harm]
      simp only [Option.bind_some]
      rw [ihk hCk _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ a.1) k' hkq
        u hu]
      rfl
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W hren q hq r hr
      have hCb := hCall.mono fun _ _ _ h => Or.inl h
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨b, hbq, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      obtain ⟨a', ha', hra, hea⟩ := NFProg.whileIterLeak_rel_fwd
        (R := fun c c' => c' = transArgs P.mapTy transTy c)
        (step' := fun acc => leakRunMC (M' : ExprEv d') E' fuel
          (NFProg.castRetHead hT.bit_eq b) (hvAppend acc W))
        (fun c c' s hc hs => by
          subst hc
          rw [leakRunMC_castRetHead_ev, ihb hCb _ _ _
            (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ c) b hbq s hs]
          rcases s with ⟨_ | ⟨h0, t0⟩, ev0⟩
          exact ⟨_, rfl, rfl, (hR.toBool_trans h0).symm, rfl⟩)
        fuel _ _ a rfl ha
      simp only [leakRunMC]
      rw [NFProg.lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren, ha']
      simp only [Option.bind_some]
      rw [hra, ihk hCk _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ a.1) k'
        hkq u hu, hea]
      rfl
  | call f args k ih =>
      intro Δ ren V W hren q hq r hr
      have hCk := hCall.mono fun _ _ _ h => Or.inr h
      obtain ⟨k', hkq, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [leakRunMC, Option.bind_eq_some_iff] at hr
      obtain ⟨y, hy, hu⟩ := hr
      simp only [leakRunMC]
      rw [NFProg.lookupArgs_mapArgs_of P transTy mapVal hVar ren V W hren,
        hCall f _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩), hy, Option.map_some, Option.bind_some]
      exact ih hCk _ _ _ (NFProg.renRel_appHom P transTy mapVal hExt ren V W hren _ y) k' hkq r
        hu

end BlockEvO

end CatCrypt.Crypto.SecureCompilation.VIR

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## Dead-binding elimination at call environments -/

section DceCall

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **The erasure of dead-binding elimination on traces of runs at a call environment**: the
    reading of a trace along the structure of `p`, keeping the events of the bindings `dce`
    keeps; a `call` node emits no event and the reading continues with its continuation. It
    returns the kept events and the rest of the trace. -/
def NFProg.dceEraseC (M : LeakModel d) (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → List CTLeak →
    List CTLeak × List CTLeak
  | _, _, .ret _, tr => ([], tr)
  | _, _, .var e k, tr =>
      if (NFProg.rename? PRen.drop (NFProg.dce k)).isSome then
        NFProg.dceEraseC M fuel k (tr.drop (evCount (M.kind e.op)))
      else
        (tr.take (evCount (M.kind e.op)) ++
            (NFProg.dceEraseC M fuel k (tr.drop (evCount (M.kind e.op)))).1,
          (NFProg.dceEraseC M fuel k (tr.drop (evCount (M.kind e.op)))).2)
  | _, _, .forLoop _ _ body k, tr =>
      match tr with
      | .trip n :: tr' =>
          (.trip n :: ((iterErase (NFProg.dceEraseC M fuel body) n tr').1 ++
              (NFProg.dceEraseC M fuel k
                (iterErase (NFProg.dceEraseC M fuel body) n tr').2).1),
            (NFProg.dceEraseC M fuel k (iterErase (NFProg.dceEraseC M fuel body) n tr').2).2)
      | _ => ([], tr)
  | _, _, .ifThenElse _ thn els k, tr =>
      match tr with
      | .branch b :: tr' =>
          (.branch b :: ((if b then NFProg.dceEraseC M fuel thn tr'
              else NFProg.dceEraseC M fuel els tr').1 ++
              (NFProg.dceEraseC M fuel k (if b then NFProg.dceEraseC M fuel thn tr'
                else NFProg.dceEraseC M fuel els tr').2).1),
            (NFProg.dceEraseC M fuel k (if b then NFProg.dceEraseC M fuel thn tr'
              else NFProg.dceEraseC M fuel els tr').2).2)
      | _ => ([], tr)
  | _, _, .whileLoop _ body k, tr =>
      ((whileErase (NFProg.dceEraseC M fuel body) fuel tr).1 ++
          (NFProg.dceEraseC M fuel k (whileErase (NFProg.dceEraseC M fuel body) fuel tr).2).1,
        (NFProg.dceEraseC M fuel k (whileErase (NFProg.dceEraseC M fuel body) fuel tr).2).2)
  | _, _, .call _ _ k, tr => NFProg.dceEraseC M fuel k tr

variable [DialectDenoteM d Option]

/-- **The leakage transformer of dead-binding elimination at call environments.** Let `E'`
    agree with `E` at the calls of `p`. A leakage run of `p` at `E` that succeeds is matched
    by a leakage run of `dce p` at `E'` to the same results, whose events are the events
    `dceEraseC` keeps from the trace of `p`. -/
theorem NFProg.leakRunMC_dce (M : LeakModel d) (E E' : CallEnv d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts)
    (hCall : ∀ f as rs (x : Valuation as), p.Calls f as rs →
      E.call f as rs x = E'.call f as rs x) :
    ∀ (V : Valuation Γ) (r : Valuation ts × List CTLeak), NFProg.leakRunMC M E fuel p V = some r →
      ∃ l, NFProg.leakRunMC M E' fuel (NFProg.dce p) V = some (r.1, l) ∧
        ∀ rest, NFProg.dceEraseC M fuel p (r.2 ++ rest) = (l, rest) := by
  induction p with
  | ret vs =>
      intro V r h
      simp only [NFProg.leakRunMC, Option.some.injEq] at h
      subst h
      exact ⟨[], rfl, fun rest => rfl⟩
  | var e k ih =>
      intro V r h
      simp only [NFProg.leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, q, hq, rfl⟩ := h
      obtain ⟨l, hl, el⟩ := ih hCall _ q hq
      have hlen := Expr.ctLeak_length M e V
      have htake : ∀ rest, (Expr.ctLeak M e V ++ (q.2 ++ rest)).take
          (evCount (M.kind e.op)) = Expr.ctLeak M e V := by
        intro rest; rw [← hlen, List.take_left]
      have hdrop : ∀ rest, (Expr.ctLeak M e V ++ (q.2 ++ rest)).drop
          (evCount (M.kind e.op)) = q.2 ++ rest := by
        intro rest; rw [← hlen, List.drop_left]
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        refine ⟨l, ?_, fun rest => ?_⟩
        · rw [VIR.NFProg.leakRunMC_rename? M E' fuel _ hr (PRen.agrees_drop V x), hl]
        · simp only [NFProg.dceEraseC, hr, Option.isSome_some, ite_true, List.append_assoc]
          exact (congrArg (NFProg.dceEraseC M fuel k) (hdrop rest)).trans (el rest)
      · rename_i hr
        refine ⟨Expr.ctLeak M e V ++ l, ?_, fun rest => ?_⟩
        · simp only [NFProg.leakRunMC, hx, Option.bind_some, hl, Option.map_some]
        · have hn : (NFProg.rename? PRen.drop (NFProg.dce k)).isSome = false := by
            rw [hr]; rfl
          simp only [NFProg.dceEraseC, hn, Bool.false_eq_true, ite_false, List.append_assoc,
            htake, hdrop, el]
  | forLoop count inits body k ihb ihk =>
      intro V r h
      simp only [NFProg.leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨l₁, h₁, e₁⟩ := forIterLeak_erase _ _ (NFProg.dceEraseC M fuel body)
        (fun i X r hr => ihb (fun f as rs x hc => hCall f as rs x (Or.inl hc)) _ r hr) _ _ a ha
      obtain ⟨l₂, h₂, e₂⟩ := ihk (fun f as rs x hc => hCall f as rs x (Or.inr hc)) _ q hq
      refine ⟨.trip (HasWord64.toNat (d := d) (count.lookup V)) :: (l₁ ++ l₂), ?_,
        fun rest => ?_⟩
      · simp only [NFProg.dce, NFProg.leakRunMC, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [List.length_range] at e₁
        simp only [NFProg.dceEraseC, List.cons_append, List.append_assoc, e₁, e₂]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro V r h
      simp only [NFProg.leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨l₂, h₂, e₂⟩ := ihk (fun f as rs x hc => hCall f as rs x (Or.inr (Or.inr hc))) _ q hq
      have harm : ∃ l₁, (if HasBoolBit.toBool (d := d) (cond.lookup V) then
            NFProg.leakRunMC M E' fuel (NFProg.dce thn) V
          else NFProg.leakRunMC M E' fuel (NFProg.dce els) V) = some (a.1, l₁) ∧
          ∀ rest, (if HasBoolBit.toBool (d := d) (cond.lookup V) then
            NFProg.dceEraseC M fuel thn (a.2 ++ rest)
          else NFProg.dceEraseC M fuel els (a.2 ++ rest)) = (l₁, rest) := by
        split at ha
        · rename_i hb
          obtain ⟨l₁, h₁, e₁⟩ := iht (fun f as rs x hc => hCall f as rs x (Or.inl hc)) V a ha
          exact ⟨l₁, by rw [ite_eq_left hb]; exact h₁, fun rest => by rw [ite_eq_left hb]; exact e₁ rest⟩
        · rename_i hb
          obtain ⟨l₁, h₁, e₁⟩ :=
            ihe (fun f as rs x hc => hCall f as rs x (Or.inr (Or.inl hc))) V a ha
          exact ⟨l₁, by rw [ite_eq_right hb]; exact h₁, fun rest => by rw [ite_eq_right hb]; exact e₁ rest⟩
      obtain ⟨l₁, h₁, e₁⟩ := harm
      refine ⟨.branch (HasBoolBit.toBool (d := d) (cond.lookup V)) :: (l₁ ++ l₂), ?_,
        fun rest => ?_⟩
      · simp only [NFProg.dce, NFProg.leakRunMC, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [NFProg.dceEraseC, List.cons_append, List.append_assoc, e₁, e₂]
  | whileLoop inits body k ihb ihk =>
      intro V r h
      simp only [NFProg.leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, q, hq, rfl⟩ := h
      obtain ⟨l₁, h₁, e₁⟩ := whileIterLeak_erase _ _ (NFProg.dceEraseC M fuel body)
        (fun X r hr => ihb (fun f as rs x hc => hCall f as rs x (Or.inl hc)) _ r hr) _ _ a ha
      obtain ⟨l₂, h₂, e₂⟩ := ihk (fun f as rs x hc => hCall f as rs x (Or.inr hc)) _ q hq
      refine ⟨l₁ ++ l₂, ?_, fun rest => ?_⟩
      · simp only [NFProg.dce, NFProg.leakRunMC, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [NFProg.dceEraseC, List.append_assoc, e₁, e₂]
  | call f args k ih =>
      intro V r h
      simp only [NFProg.leakRunMC, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, hu⟩ := h
      obtain ⟨l, hl, el⟩ := ih (fun f as rs x hc => hCall f as rs x (Or.inr hc)) _ r hu
      refine ⟨l, ?_, fun rest => el rest⟩
      simp only [NFProg.dce, NFProg.leakRunMC]
      rw [← hCall f _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩), hy, Option.bind_some, hl]

/-- **Constant time through `dce` at call environments, relative to source runs.** Let `E'`
    agree with `E` at the calls of `p`. Two runs of `p` at `E` that succeed with equal events
    give two runs of `dce p` at `E'` that succeed with equal events. -/
theorem NFProg.dce_ctRelC (M : LeakModel d) (E E' : CallEnv d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts)
    (hCall : ∀ f as rs (x : Valuation as), p.Calls f as rs →
      E.call f as rs x = E'.call f as rs x)
    (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation ts × List CTLeak)
    (h₁ : NFProg.leakRunMC M E fuel p V₁ = some r₁)
    (h₂ : NFProg.leakRunMC M E fuel p V₂ = some r₂) (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRunMC M E' fuel (NFProg.dce p) V₁ = some s₁ ∧
      NFProg.leakRunMC M E' fuel (NFProg.dce p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧
      s₁.2 = s₂.2 := by
  obtain ⟨l₁, k₁, e₁⟩ := NFProg.leakRunMC_dce M E E' fuel p hCall V₁ r₁ h₁
  obtain ⟨l₂, k₂, e₂⟩ := NFProg.leakRunMC_dce M E E' fuel p hCall V₂ r₂ h₂
  refine ⟨_, _, k₁, k₂, rfl, rfl, ?_⟩
  have h1 := e₁ []
  have h2 := e₂ []
  rw [he] at h1
  rw [h1] at h2
  exact (Prod.mk.inj h2).1

end DceCall

end CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
