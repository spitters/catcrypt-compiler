/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ExitTyped
public import CatCrypt.Crypto.Hax.HaxToLowCTWordOps

/-!
# The typed exit front uses each name in the heap of its placement

`RustExec` keeps a scalar heap and a tower heap, and a name has a slot in each.
`placedUse A c` states that every name of `c` other than the reserved names of the front
(`exitReserved`) is used only in the heap that the placement `A` gives it: a name read or
written in the scalar heap (a scalar assignment, a guard, a loop counter, an index, a
variable of a scalar expression) is placed in the scalar heap (`exitSc`), and a tower slot
`⟨x, t⟩` (a binding, a call destination or argument, a copy, an element load or store, a
limb store) is placed by `A` at `t`.  A value moves between the heaps only through a
reserved slot: a limb of `exitCallName` or of an `Option` payload slot read into a scalar,
or a scalar stored into limb `0` of a reserved marshalling slot.

`noLetCall c` states that no binding `RLetZero x t b` of `c` has a body `b` that starts
with a call; on such programs the word lowerings `scalarizeWordOps` and
`scalarizeNarrowOps` are the identity.

## Main definitions

* `plSc`, `plLoc`, `plTw`, `sexprPlaced`, `placedUse`
* `notSeqCall`, `noLetCall`

## Main results

* `scalarizeWordOps_of_noLetCall`, `scalarizeNarrowIn_of_noLetCall`
* `haxToLowCTKT_placedUse`: every program of `haxToLowCTKT A` from a loop context satisfies
  `placedUse A` and `noLetCall`
* `haxToLowCTFnT_placedUse`
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr)
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## The placement discipline -/

/-- A scalar slot `x` under `A`: a reserved name, or a name placed in the scalar heap. -/
def plSc (A : ExitTowers) (x : String) : Bool := exitReserved x || exitSc A x

/-- A tower slot `l` under `A`: a reserved name, or a name placed at the type of `l`. -/
def plLoc (A : ExitTowers) (l : Located) : Bool :=
  exitReserved l.locVar || decide (A.lookup l.locVar = some l.locSrc)

/-- A tower slot `x` read by limb under `A`: a reserved name, or a name placed in a
    tower. -/
def plTw (A : ExitTowers) (x : String) : Bool := exitReserved x || (A.lookup x).isSome

/-- Every variable of a scalar expression is a scalar slot under `A` and every limb it
    reads is a tower slot under `A`. -/
def sexprPlaced (A : ExitTowers) : SExpr → Bool
  | .SVar x => plSc A x
  | .SLit _ => true
  | .SLimb x _ => plTw A x
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b | .SXor a b
  | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b | .SMulHiS a b =>
      sexprPlaced A a && sexprPlaced A b

/-- Every name of `c` is used in the heap of its placement under `A` (see the module
    docstring).  A constructor the typed exit front does not emit is refused. -/
def placedUse (A : ExitTowers) : LowCT → Bool
  | .RSkip => true
  | .RSeq a b => placedUse A a && placedUse A b
  | .RLetZero x t b => plLoc A ⟨x, t⟩ && placedUse A b
  | .RLetU64Zero x b => plSc A x && placedUse A b
  | .RScalarSet x _ => plSc A x
  | .RScalarSetExpr x e => plSc A x && sexprPlaced A e
  | .RCall _ d as => plLoc A d && as.all (plLoc A)
  | .RCallN _ ds as => ds.all (plLoc A) && as.all (plLoc A)
  | .RIfNz v a b => plSc A v && placedUse A a && placedUse A b
  | .RWhileNz v b => plSc A v && placedUse A b
  | .RFor i _ b => plSc A i && placedUse A b
  | .RForRuntime i e b => plSc A i && sexprPlaced A e && placedUse A b
  | .RLimbStoreExpr l _ e => plLoc A l && sexprPlaced A e
  | .RCopy d s => plLoc A d && plLoc A s
  | .RArrLoad d s i => plLoc A d && plLoc A s && plSc A i
  | .RArrStore a i s => plLoc A a && plSc A i && plLoc A s
  | _ => false

/-- `c` does not start with a call. -/
def notSeqCall : LowCT → Bool
  | .RSeq (.RCall _ _ _) _ => false
  | _ => true

/-- No binding `RLetZero x t b` of `c` has a body starting with a call. -/
def noLetCall : LowCT → Bool
  | .RSeq a b => noLetCall a && noLetCall b
  | .RLetZero _ _ b => notSeqCall b && noLetCall b
  | .RLetU64Zero _ b => noLetCall b
  | .RIfNz _ a b => noLetCall a && noLetCall b
  | .RWhileNz _ b => noLetCall b
  | .RFor _ _ b => noLetCall b
  | .RForRuntime _ _ b => noLetCall b
  | .RBlock b => noLetCall b
  | _ => true

/-! ## The word lowerings on programs without a call-headed binding -/

theorem scalarizeWordOps_letZero {x : String} {t : TowerType} {b : LowCT}
    (hb : notSeqCall b = true) :
    scalarizeWordOps (.RLetZero x t b) = .RLetZero x t (scalarizeWordOps b) := by
  rw [scalarizeWordOps.eq_def]
  split <;> simp_all [notSeqCall]

theorem scalarizeWordOps_of_noLetCall : ∀ c : LowCT, noLetCall c = true →
    scalarizeWordOps c = c
  | .RSeq a b, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    simp [scalarizeWordOps, scalarizeWordOps_of_noLetCall a h.1,
      scalarizeWordOps_of_noLetCall b h.2]
  | .RLetZero x t b, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    rw [scalarizeWordOps_letZero h.1, scalarizeWordOps_of_noLetCall b h.2]
  | .RLetU64Zero x b, h => by
    simp only [noLetCall] at h
    simp [scalarizeWordOps, scalarizeWordOps_of_noLetCall b h]
  | .RIfNz v a b, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    simp [scalarizeWordOps, scalarizeWordOps_of_noLetCall a h.1,
      scalarizeWordOps_of_noLetCall b h.2]
  | .RWhileNz v b, h => by
    simp only [noLetCall] at h
    simp [scalarizeWordOps, scalarizeWordOps_of_noLetCall b h]
  | .RFor i n b, h => by
    simp only [noLetCall] at h
    simp [scalarizeWordOps, scalarizeWordOps_of_noLetCall b h]
  | .RForRuntime i e b, h => by
    simp only [noLetCall] at h
    simp [scalarizeWordOps, scalarizeWordOps_of_noLetCall b h]
  | .RBlock b, h => by
    simp only [noLetCall] at h
    simp [scalarizeWordOps, scalarizeWordOps_of_noLetCall b h]
  | .RSkip, _ | .RScalarSet _ _, _ | .RCall _ _ _, _ | .RCallSwap _ _ _ _, _
  | .RCloneCall _ _ _ _ _ _, _ | .RLimbStore _ _ _, _ | .RLimbStoreExpr _ _ _, _
  | .RCallN _ _ _, _ | .RSelect _ _ _ _, _ | .RAssert _, _ | .RFnDef _ _ _ _ _, _
  | .RFnCall _ _ _, _ | .RTupleLoad _ _ _, _ | .RArrStore _ _ _, _ | .RArrLoad _ _ _, _
  | .RArrStoreLit _ _ _, _ | .RArrLoadLit _ _ _, _ | .RScalarSetExpr _ _, _
  | .RCallDstThreaded _ _ _, _ | .RCopy _ _, _ => by simp [scalarizeWordOps]

theorem narrowLetIn_of_notSeqCall {W : List String} {x : String} {t : TowerType} {b : LowCT}
    (hb : notSeqCall b = true) : narrowLetIn W x t b = .RLetZero x t b := by
  rw [narrowLetIn.eq_def]
  split <;> simp_all [notSeqCall]

theorem scalarizeNarrowIn_of_noLetCall : ∀ (c : LowCT) (W : List String), noLetCall c = true →
    scalarizeNarrowIn W c = c
  | .RSeq a b, W, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    simp [scalarizeNarrowIn, scalarizeNarrowIn_of_noLetCall a W h.1,
      scalarizeNarrowIn_of_noLetCall b W h.2]
  | .RLetZero x t b, W, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    rw [scalarizeNarrowIn, scalarizeNarrowIn_of_noLetCall b _ h.2,
      narrowLetIn_of_notSeqCall h.1]
  | .RLetU64Zero x b, W, h => by
    simp only [noLetCall] at h
    simp [scalarizeNarrowIn, scalarizeNarrowIn_of_noLetCall b _ h]
  | .RIfNz v a b, W, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    simp [scalarizeNarrowIn, scalarizeNarrowIn_of_noLetCall a W h.1,
      scalarizeNarrowIn_of_noLetCall b W h.2]
  | .RWhileNz v b, W, h => by
    simp only [noLetCall] at h
    simp [scalarizeNarrowIn, scalarizeNarrowIn_of_noLetCall b W h]
  | .RFor i n b, W, h => by
    simp only [noLetCall] at h
    simp [scalarizeNarrowIn, scalarizeNarrowIn_of_noLetCall b _ h]
  | .RForRuntime i e b, W, h => by
    simp only [noLetCall] at h
    simp [scalarizeNarrowIn, scalarizeNarrowIn_of_noLetCall b _ h]
  | .RBlock b, W, h => by
    simp only [noLetCall] at h
    simp [scalarizeNarrowIn, scalarizeNarrowIn_of_noLetCall b W h]
  | .RSkip, _, _ | .RScalarSet _ _, _, _ | .RCall _ _ _, _, _ | .RCallSwap _ _ _ _, _, _
  | .RCloneCall _ _ _ _ _ _, _, _ | .RLimbStore _ _ _, _, _ | .RLimbStoreExpr _ _ _, _, _
  | .RCallN _ _ _, _, _ | .RSelect _ _ _ _, _, _ | .RAssert _, _, _
  | .RFnDef _ _ _ _ _, _, _ | .RFnCall _ _ _, _, _ | .RTupleLoad _ _ _, _, _
  | .RArrStore _ _ _, _, _ | .RArrLoad _ _ _, _, _ | .RArrStoreLit _ _ _, _, _
  | .RArrLoadLit _ _ _, _, _ | .RScalarSetExpr _ _, _, _ | .RCallDstThreaded _ _ _, _, _
  | .RCopy _ _, _, _ => by simp [scalarizeNarrowIn]

/-- On a program without a call-headed binding the word lowerings `scalarizeNarrowOps` and
    `scalarizeWordOps` are the identity. -/
theorem scalarize_of_noLetCall {c : LowCT} (h : noLetCall c = true) :
    scalarizeWordOps (scalarizeNarrowOps c) = c := by
  rw [scalarizeNarrowOps, scalarizeNarrowIn_of_noLetCall c [] h,
    scalarizeWordOps_of_noLetCall c h]

/-! ## The reserved slots of the front -/

theorem plSc_of_sc {A : ExitTowers} {x : String} (h : A.lookup x = none) : plSc A x = true := by
  simp [plSc, exitSc, h]

theorem plSc_of_reserved {A : ExitTowers} {x : String} (h : exitReserved x = true) :
    plSc A x = true := by
  simp [plSc, h]

theorem plLoc_of_lookup {A : ExitTowers} {x : String} {t : TowerType}
    (h : A.lookup x = some t) : plLoc A ⟨x, t⟩ = true := by
  simp [plLoc, h]

theorem plLoc_of_reserved {A : ExitTowers} {l : Located} (h : exitReserved l.locVar = true) :
    plLoc A l = true := by
  simp [plLoc, h]

/-! ## The heads -/

/-- A context `k` of the front keeps `placedUse A` and `noLetCall` of the program it
    wraps. -/
def CtxPlaced (A : ExitTowers) (k : LowCT → LowCT) : Prop :=
  ∀ b, placedUse A b = true → noLetCall b = true →
    placedUse A (k b) = true ∧ noLetCall (k b) = true

theorem scalarOpExprT_placed {A : ExitTowers} {f : String} {a b se : SExpr}
    (h : scalarOpExprT f a b = some se) (ha : sexprPlaced A a = true)
    (hb : sexprPlaced A b = true) : sexprPlaced A se = true := by
  unfold scalarOpExprT at h
  split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h
       simp [sexprPlaced, orExprN, ha, hb])
    | (obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp h
       cases p.2 <;> simp [WidthOp.sexpr, widthMask, orExprN, widthAmt, sexprPlaced, ha, hb])

/-- The marshalling of call arguments: every argument slot is a tower slot under `A`, and
    the context keeps `placedUse A`, `noLetCall` and `notSeqCall`. -/
theorem callMarshal_placed {A : ExitTowers} {dt : TowerType} :
    ∀ {args : List ImpExpr} {ctx : LowCT → LowCT} {ls : List Located},
      callMarshal A dt args = some (ctx, ls) →
      (∀ l ∈ ls, plLoc A l = true) ∧
        ∀ c, placedUse A c = true → noLetCall c = true → notSeqCall c = true →
          placedUse A (ctx c) = true ∧ noLetCall (ctx c) = true ∧ notSeqCall (ctx c) = true
  | [], ctx, ls, h => by
    simp only [callMarshal, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, fun c h1 h2 h3 => ⟨h1, h2, h3⟩⟩
  | e :: as, ctx, ls, h => by
    cases e with
    | var x => ?_
    | _ => simp [callMarshal] at h
    simp only [callMarshal] at h
    rcases hm : callMarshal A dt as with _ | ⟨ctx', ls'⟩
    · simp [hm] at h
    obtain ⟨hls', hctx'⟩ := callMarshal_placed hm
    simp only [hm] at h
    rcases hx : A.lookup x with _ | t
    · simp only [hx] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, fun c h1 h2 h3 => ?_⟩
        · intro l hl
          simp only [List.mem_cons] at hl
          rcases hl with rfl | hl
          · exact plLoc_of_reserved (exitReserved_marshal x)
          · exact hls' l hl
        · obtain ⟨g1, g2, g3⟩ := hctx' c h1 h2 h3
          simp [placedUse, noLetCall, notSeqCall, plLoc_of_reserved (A := A)
            (l := ⟨exitMarshalName x, dt⟩) (exitReserved_marshal x), sexprPlaced,
            plSc_of_sc hx, g1, g2]
      · cases h
    · simp only [hx, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, hctx'⟩
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact plLoc_of_lookup hx
      · exact hls' l hl

theorem callHeadAt_placed {A : ExitTowers} {n f : String} {dt dr : TowerType}
    {args : List ImpExpr} {k : LowCT → LowCT} (h : callHeadAt A n f dt dr args = some k) :
    CtxPlaced A k := by
  unfold callHeadAt at h
  rcases hm : callMarshal A dt args with _ | ⟨ctx, ls⟩
  · simp [hm] at h
  obtain ⟨hls, hctx⟩ := callMarshal_placed hm
  have hcall : placedUse A (.RCall f ⟨exitCallName, dr⟩ ls) = true := by
    simp only [placedUse, Bool.and_eq_true, List.all_eq_true]
    exact ⟨plLoc_of_reserved exitReserved_call, hls⟩
  obtain ⟨g1, g2, g3⟩ := hctx _ hcall rfl rfl
  have hC : plLoc A ⟨exitCallName, dr⟩ = true := plLoc_of_reserved exitReserved_call
  simp only [hm] at h
  rcases hn : A.lookup n with _ | t
  · simp only [hn, Option.some.injEq] at h
    subst h
    intro b hb1 hb2
    simp [placedUse, noLetCall, sexprPlaced, plTw, exitReserved_call, plSc_of_sc hn, hC, g1, g2,
      g3, hb1, hb2]
  · simp only [hn] at h
    split at h
    · rename_i htd
      subst htd
      simp only [Option.some.injEq] at h
      subst h
      intro b hb1 hb2
      simp [placedUse, noLetCall, plLoc_of_lookup hn, hC, g1, g2, g3, hb1, hb2]
    · cases h

theorem callHeadT_placed {A : ExitTowers} {n f : String} {args : List ImpExpr}
    {k : LowCT → LowCT} (h : callHeadT A n f args = some k) : CtxPlaced A k := by
  unfold callHeadT at h
  split at h
  · split at h
    · exact callHeadAt_placed h
    · cases h
  · split at h
    · split at h
      · cases h
      · exact callHeadAt_placed h
    · split at h
      · split at h
        · cases h
        · exact callHeadAt_placed h
      · split at h
        · exact callHeadAt_placed h
        · cases h

theorem indexHeadT_placed {A : ExitTowers} {n : String} {args : List ImpExpr}
    {k : LowCT → LowCT} (h : indexHeadT A n args = some k) : CtxPlaced A k := by
  unfold indexHeadT at h
  split at h
  · rename_i arr idx
    rcases ha : A.lookup arr with _ | t
    · simp [ha] at h
    simp only [ha] at h
    split at h
    · rename_i hidx
      have hC : ∀ t', plLoc A ⟨exitCallName, t'⟩ = true :=
        fun _ => plLoc_of_reserved exitReserved_call
      split at h
      · split at h
        · rename_i hn
          simp only [Option.some.injEq] at h
          subst h
          intro b hb1 hb2
          simp [placedUse, noLetCall, notSeqCall, sexprPlaced, plTw, exitReserved_call, hC,
            plLoc_of_lookup ha, plSc_of_sc hidx, plSc_of_sc hn, hb1, hb2]
        · cases h
      · split at h
        · rename_i hn
          simp only [Option.some.injEq] at h
          subst h
          intro b hb1 hb2
          simp [placedUse, noLetCall, notSeqCall, hC, plLoc_of_lookup ha, plSc_of_sc hidx,
            plLoc_of_lookup hn, hb1, hb2]
        · cases h
    · cases h
  · cases h

theorem updateHeadT_placed {A : ExitTowers} {n : String} {args : List ImpExpr}
    {k : LowCT → LowCT} (h : updateHeadT A n args = some k) : CtxPlaced A k := by
  unfold updateHeadT at h
  split at h
  · rename_i arr idx src
    rcases ha : A.lookup arr with _ | t
    · simp [ha] at h
    simp only [ha] at h
    split at h
    · rename_i hc
      obtain ⟨-, hidx, -⟩ := hc
      split at h
      · rename_i ctx srcLoc hm
        obtain ⟨hls, hctx⟩ := callMarshal_placed hm
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          have hst : placedUse A (.RArrStore ⟨arr, t⟩ idx srcLoc) = true := by
            simp [placedUse, plLoc_of_lookup ha, plSc_of_sc hidx,
              hls srcLoc (by simp)]
          obtain ⟨g1, g2, -⟩ := hctx _ hst rfl rfl
          intro b hb1 hb2
          simp [placedUse, noLetCall, g1, g2, hb1, hb2]
        · cases h
      · cases h
    · cases h
  · cases h

theorem arrLitHeadN_placed {A : ExitTowers} {n : String} {args : List ImpExpr}
    {k : LowCT → LowCT} (h : arrLitHeadN A n args = some k) : CtxPlaced A k := by
  unfold arrLitHeadN at h
  split at h
  · split at h
    · exact callHeadAt_placed h
    · cases h
  · cases h

theorem repeatHeadT_placed {A : ExitTowers} {n : String} {args : List ImpExpr}
    {k : LowCT → LowCT} (h : repeatHeadT A n args = some k) : CtxPlaced A k := by
  unfold repeatHeadT at h
  split at h
  · split at h
    · split at h
      · exact callHeadAt_placed h
      · cases h
    · cases h
  · cases h

theorem appHeadT_placed {A : ExitTowers} {n f : String} {args : List ImpExpr}
    {k : LowCT → LowCT} (h : appHeadT A n f args = some k) : CtxPlaced A k := by
  unfold appHeadT at h
  rcases hs : scalarOpHeadT A n f args with _ | se
  · simp only [hs] at h
    split at h
    · exact indexHeadT_placed h
    split at h
    · exact updateHeadT_placed h
    split at h
    · exact arrLitHeadN_placed h
    split at h
    · exact repeatHeadT_placed h
    · exact callHeadT_placed h
  · simp only [hs, Option.some.injEq] at h
    subst h
    unfold scalarOpHeadT at hs
    split at hs
    · rename_i a b
      split at hs
      · rename_i hc
        obtain ⟨hn, ha, hb⟩ := hc
        have hse := scalarOpExprT_placed (A := A) hs (by simp [sexprPlaced, plSc_of_sc ha])
          (by simp [sexprPlaced, plSc_of_sc hb])
        intro b' hb1 hb2
        simp [placedUse, noLetCall, plSc_of_sc hn, hse, hb1, hb2]
      · cases hs
    · cases hs

theorem letHead_scalar_placed {A : ExitTowers} {n : String} {val : ImpExpr}
    {k : LowCT → LowCT} (hn : A.lookup n = none)
    (hv : ∀ s, val = .var s → A.lookup s = none)
    (hlit : (∃ l, val = .lit l) ∨ ∃ s, val = .var s) (h : letHead n val = some k) :
    CtxPlaced A k := by
  rcases hlit with ⟨l, rfl⟩ | ⟨s, rfl⟩
  · cases l <;> simp only [letHead] at h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h
         intro b hb1 hb2; simp [placedUse, noLetCall, plSc_of_sc hn, hb1, hb2])
      | (split at h
         · simp only [Option.some.injEq] at h; subst h
           intro b hb1 hb2; simp [placedUse, noLetCall, plSc_of_sc hn, hb1, hb2]
         · cases h)
      | cases h
  · simp only [letHead] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      intro b hb1 hb2; exact ⟨hb1, hb2⟩
    · simp only [Option.some.injEq] at h; subst h
      intro b hb1 hb2
      simp [placedUse, noLetCall, sexprPlaced, plSc_of_sc hn, plSc_of_sc (hv s rfl), hb1, hb2]

theorem letHeadT_placed {A : ExitTowers} {n : String} {val : ImpExpr}
    {k : LowCT → LowCT} (h : letHeadT A n val = some k) : CtxPlaced A k := by
  cases val with
  | lit l =>
    simp only [letHeadT] at h
    rcases hn : A.lookup n with _ | t
    · simp only [hn] at h
      exact letHead_scalar_placed hn (by simp) (Or.inl ⟨l, rfl⟩) h
    · simp only [hn] at h
      split at h
      · obtain ⟨kk, -, rfl⟩ := Option.map_eq_some_iff.mp h
        intro b hb1 hb2
        simp [placedUse, noLetCall, notSeqCall, sexprPlaced, plLoc_of_lookup hn, hb1, hb2]
      · cases h
  | var s =>
    simp only [letHeadT] at h
    rcases hn : A.lookup n with _ | t <;> rcases hs : A.lookup s with _ | t' <;>
      simp only [hn, hs] at h
    · exact letHead_scalar_placed hn (fun s' hs' => by cases hs'; exact hs)
        (Or.inr ⟨s, rfl⟩) h
    · cases h
    · cases h
    · split at h
      · rename_i htt
        subst htt
        split at h
        · simp only [Option.some.injEq] at h; subst h
          intro b hb1 hb2; exact ⟨hb1, hb2⟩
        · simp only [Option.some.injEq] at h; subst h
          intro b hb1 hb2
          simp [placedUse, noLetCall, plLoc_of_lookup hn, plLoc_of_lookup hs, hb1, hb2]
      · cases h
  | app f args => exact appHeadT_placed h
  | _ => simp [letHeadT] at h

theorem optHeadT_placed {A : ExitTowers} {f : String} {args : List ImpExpr} {p : String}
    {callC bindP : LowCT} (h : optHeadT A f args p = some (callC, bindP)) :
    placedUse A callC = true ∧ noLetCall callC = true ∧ placedUse A bindP = true ∧
      noLetCall bindP = true := by
  unfold optHeadT at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i t _
  split at h
  · cases h
  rename_i ctx ls hm
  obtain ⟨hls, hctx⟩ := callMarshal_placed hm
  have hcall : placedUse A (.RCallN f [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩] ls) =
      true := by
    simp only [placedUse, Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, hls⟩
    simp [plLoc_of_reserved (A := A) (l := ⟨exitOptTagName, .TU64⟩) exitReserved_optTag,
      plLoc_of_reserved (A := A) (l := ⟨exitOptPayName, t⟩) exitReserved_optPay]
  obtain ⟨g1, g2, g3⟩ := hctx _ hcall rfl rfl
  simp only [notSeqCall] at g3
  have hC : placedUse A (.RSeq (.RLetZero exitOptTagName .TU64 (.RLetZero exitOptPayName t
      (ctx (.RCallN f [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩] ls))))
      (.RScalarSetExpr exitOptTagS (.SLimb exitOptTagName 0))) = true ∧
      noLetCall (.RSeq (.RLetZero exitOptTagName .TU64 (.RLetZero exitOptPayName t
      (ctx (.RCallN f [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩] ls))))
      (.RScalarSetExpr exitOptTagS (.SLimb exitOptTagName 0))) = true := by
    simp [placedUse, noLetCall, notSeqCall, sexprPlaced, plTw, plSc_of_reserved,
      exitReserved_optTag, exitReserved_optTagS,
      plLoc_of_reserved (A := A) (l := ⟨exitOptTagName, .TU64⟩) exitReserved_optTag,
      plLoc_of_reserved (A := A) (l := ⟨exitOptPayName, t⟩) exitReserved_optPay, g1, g2, g3]
  split at h
  · split at h
    · rename_i hp _
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hC.1, hC.2, by simp [placedUse, sexprPlaced, plTw, exitReserved_optPay,
        plSc_of_sc hp], rfl⟩
    · cases h
  · split at h
    · rename_i tp hp hc
      obtain ⟨rfl, -⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hC.1, hC.2, by simp [placedUse, plLoc_of_lookup hp,
        plLoc_of_reserved (A := A) (l := ⟨exitOptPayName, tp⟩) exitReserved_optPay], rfl⟩
    · cases h

/-! ## The stores -/

theorem storeScalar_placed {A : ExitTowers} {slot : String} {e : ImpExpr} {s : LowCT}
    (hslot : exitReserved slot = true) (he : exitScE A e = true)
    (h : storeScalar slot e = some s) : placedUse A s = true ∧ noLetCall s = true := by
  cases e with
  | var x =>
    simp only [storeScalar, Option.some.injEq] at h
    subst h
    simp only [exitScE] at he
    simp [placedUse, noLetCall, sexprPlaced, plSc, hslot, he]
  | lit l =>
    cases l <;> simp only [storeScalar] at h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h; simp [placedUse, noLetCall, plSc, hslot])
      | (split at h
         · simp only [Option.some.injEq] at h; subst h; simp [placedUse, noLetCall, plSc, hslot]
         · cases h)
      | cases h
  | unitVal =>
    simp only [storeScalar, Option.some.injEq] at h
    subst h
    simp [placedUse, noLetCall, plSc, hslot]
  | _ => simp [storeScalar] at h

theorem exitStore_placed {A : ExitTowers} {e : ImpExpr} {s : LowCT}
    (he : exitScE A e = true) (h : exitStore e = some s) :
    placedUse A s = true ∧ noLetCall s = true := by
  unfold exitStore at h
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨g1, g2⟩ := storeScalar_placed exitReserved_val he hs'
  simp [placedUse, noLetCall, plSc, exitReserved_ret, g1, g2]

theorem tupleStoreT_placed {A : ExitTowers} :
    ∀ (i : Nat) {es : List ImpExpr} {s : LowCT}, tupleStoreT A i es = some s →
      placedUse A s = true ∧ noLetCall s = true
  | _, [], s, h => by
    simp only [tupleStoreT, Option.some.injEq] at h
    subst h; simp [placedUse, noLetCall]
  | i, e :: es, s, h => by
    cases e with
    | var x =>
      simp only [tupleStoreT] at h
      obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨g1, g2⟩ := tupleStoreT_placed (i + 1) hr
      rcases hx : A.lookup x with _ | t
      · simp [placedUse, noLetCall, sexprPlaced, plSc_of_reserved (exitReserved_resComp i),
          plSc_of_sc hx, g1, g2]
      · simp [placedUse, noLetCall, plLoc_of_lookup hx,
          plLoc_of_reserved (A := A) (l := ⟨exitResCompName i, t⟩) (exitReserved_resComp i),
          g1, g2]
    | _ => simp [tupleStoreT] at h

theorem resultStoreT_placed {A : ExitTowers} {e : ImpExpr} {s : LowCT}
    (h : resultStoreT A e = some s) : placedUse A s = true ∧ noLetCall s = true := by
  cases e with
  | var x =>
    rcases hx : A.lookup x with _ | t
    · simp only [resultStoreT, hx] at h
      exact storeScalar_placed exitReserved_res (by simp [exitScE, exitSc, hx]) h
    · simp only [resultStoreT, hx, Option.some.injEq] at h
      subst h
      simp [placedUse, noLetCall, plLoc_of_lookup hx,
        plLoc_of_reserved (A := A) (l := ⟨exitResName, t⟩) exitReserved_res]
  | tuple es => exact tupleStoreT_placed 0 h
  | app f args =>
    rcases resultStoreT_app_cases A h with ⟨-, -, rfl⟩ | ⟨x, -, -, rfl⟩ | h'
    · simp [placedUse, noLetCall, plSc_of_reserved exitReserved_res]
    · rcases hx : A.lookup x with _ | t
      · simp [placedUse, noLetCall, sexprPlaced, plSc_of_reserved (exitReserved_resComp 0),
          plSc_of_sc hx, plSc_of_reserved exitReserved_res]
      · simp [placedUse, noLetCall, plLoc_of_lookup hx, plSc_of_reserved exitReserved_res,
          plLoc_of_reserved (A := A) (l := ⟨exitResCompName 0, t⟩) (exitReserved_resComp 0)]
    · exact storeScalar_placed exitReserved_res rfl h'
  | _ =>
    simp only [resultStoreT] at h
    exact storeScalar_placed exitReserved_res rfl h

/-! ## The lowering -/

theorem runCtx_exitRunName {fl : Option String} (h : RunCtx fl) :
    RunCtx (some (exitRunName fl)) := by
  intro r hr
  cases hr
  exact Or.inl (runSlot_exitRunName h)

theorem exitReserved_runName {fl : Option String} (h : RunCtx fl) :
    exitReserved (exitRunName fl) = true :=
  exitReserved_of_runSlot (runSlot_exitRunName h)

/-- A loop bound of `boundSE A` reads only scalar slots under `A`. -/
theorem boundSE_placed {A : ExitTowers} (e : ImpExpr) :
    ∀ {se : SExpr}, boundSE A e = some se → sexprPlaced A se = true := by
  induction e using ImpExpr.ind
  case lit l =>
    intro se h
    simp only [boundSE] at h
    split at h
    · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
    · cases h
  case var x =>
    intro se h
    simp only [boundSE] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
      simp [sexprPlaced, plSc, hx.2]
    · cases h
  case app op args ih =>
    intro se h
    match args, ih, h with
    | [a, b], ih, h =>
      simp only [boundSE] at h
      rcases ha : boundSE A a with _ | sa
      · rw [ha] at h; cases h
      rcases hb : boundSE A b with _ | sb
      · rw [ha, hb] at h; cases h
      rw [ha, hb] at h
      exact scalarOpExprT_placed h (ih a (by simp) ha) (ih b (by simp) hb)
    | [], _, h => simp [boundSE] at h
    | [_], _, h => simp [boundSE] at h
    | _ :: _ :: _ :: _, _, h => simp [boundSE] at h
  all_goals (intro se h; simp [boundSE] at h)

/-- The bounds of `forBoundsV A` read only scalar slots under `A`. -/
theorem forBoundsV_placed {A : ExitTowers} {i : String} {body lo hi : ImpExpr}
    {loE hiE : SExpr} (h : forBoundsV A i body lo hi = some (loE, hiE)) :
    sexprPlaced A loE = true ∧ sexprPlaced A hiE = true := by
  obtain ⟨hl, hh⟩ := forBoundsV_some h
  exact ⟨boundSE_placed lo (loBoundSE_boundSE hl), boundSE_placed hi hh⟩

theorem haxToLowCTKT_placedUse (A : ExitTowers) (tl : Bool) (fl : Option String)
    (e : ImpExpr) : RunCtx fl → ∀ {c : LowCT} {x : Bool},
      haxToLowCTKT A tl fl e = some (c, x) → placedUse A c = true ∧ noLetCall c = true := by
  fun_induction haxToLowCTKT A tl fl e <;> intro hfl c x h
  all_goals first | (simp at h; done) | skip
  case case1 k bC xb hb hk ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨g1, g2⟩ := ih hfl hb
    exact letHeadT_placed hk _ g1 g2
  case case3 aC xa bC xb hb ha iha ihb =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨a1, a2⟩ := iha hfl ha
    obtain ⟨b1, b2⟩ := ihb hfl hb
    cases xa <;> simp [placedUse, noLetCall, exitGuard, plSc, exitReserved_ret, a1, a2, b1, b2]
  case case5 v _ _ hv tC xt eC xe he ht iht ihe =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨t1, t2⟩ := iht hfl ht
    obtain ⟨e1, e2⟩ := ihe hfl he
    simp [placedUse, noLetCall, plSc, hv, t1, t2, e1, e2]
  case case8 ih => exact ih hfl h
  case case9 callC bindP tC xt eC xe he ht ho iht ihe =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨o1, o2, o3, o4⟩ := optHeadT_placed ho
    obtain ⟨t1, t2⟩ := iht hfl ht
    obtain ⟨e1, e2⟩ := ihe hfl he
    simp [placedUse, noLetCall, plSc, exitReserved_optTagS, o1, o2, o3, o4, t1, t2, e1, e2]
  case case11 callC bindP tC xt eC xe he ht ho iht ihe =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨o1, o2, o3, o4⟩ := optHeadT_placed ho
    obtain ⟨t1, t2⟩ := iht hfl ht
    obtain ⟨e1, e2⟩ := ihe hfl he
    simp [placedUse, noLetCall, plSc, exitReserved_optTagS, o1, o2, o3, o4, t1, t2, e1, e2]
  case case13 fl v _ hv bC xb hb ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp [placedUse, noLetCall, sexprPlaced, exitLoop, plSc, exitReserved_ret, exitReserved_val,
      exitReserved_runName hfl, hv, b1, b2]
  case case16 fl i _ _ _ hi l hh bC xb hb hfb ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp only [Bool.and_eq_true] at hi
    simp [placedUse, noLetCall, sexprPlaced, exitForLoop, exitForTrip, exitGuard, plSc,
      exitReserved_ret, exitReserved_val, exitReserved_runName hfl, hi.1, b1, b2]
  case case17 fl i lo hi' _ hi l hh bC xb hb hrt hfb ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp only [Bool.and_eq_true] at hi
    have hh' : exitSc A hh = true := by simpa [exitScRt, hrt] using hi.2
    simp [placedUse, noLetCall, sexprPlaced, exitForLoopRt, exitForTrip, exitGuard, plSc,
      exitReserved_ret, exitReserved_val, exitReserved_runName hfl, hi.1, hh', b1, b2]
  case case18 fl i lo hi' body hi bC xb hb hrt hfb ih =>
    obtain ⟨⟨loE, hiE⟩, hV, hsx⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hsx
    obtain ⟨rfl, rfl⟩ := hsx
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp only [Bool.and_eq_true] at hi
    obtain ⟨p1, p2⟩ := forBoundsV_placed hV
    simp [placedUse, noLetCall, sexprPlaced, exitForLoopV, exitForTripV, exitGuard, plSc,
      exitReserved_ret, exitReserved_val, exitReserved_runName hfl, hi.1, p1, p2, b1, b2]
  case case21 fl i _ _ _ hi l hh bC xb hb hfb ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp [placedUse, noLetCall, sexprPlaced, exitForLoopRev, exitForTripRev, exitGuard, plSc,
      exitReserved_ret, exitReserved_val, exitReserved_runName hfl, hi, b1, b2]
  case case24 r i _ _ _ hi l hh bC xb hb hfb ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp only [Bool.and_eq_true] at hi
    simp [placedUse, noLetCall, sexprPlaced, breakLoop, exitForLoop, exitForTrip, exitGuard, plSc,
      exitReserved_ret, exitReserved_val, exitReserved_runName hfl, hi.1, b1, b2]
  case case25 r i lo hi' _ hi l hh bC xb hb hrt hfb ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp only [Bool.and_eq_true] at hi
    have hh' : exitSc A hh = true := by simpa [exitScRt, hrt] using hi.2
    simp [placedUse, noLetCall, sexprPlaced, breakLoop, exitForLoopRt, exitForTrip, exitGuard,
      plSc, exitReserved_ret, exitReserved_val, exitReserved_runName hfl, hi.1, hh', b1, b2]
  case case26 r i lo hi' body hi bC xb hb hrt hfb ih =>
    obtain ⟨⟨loE, hiE⟩, hV, hsx⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hsx
    obtain ⟨rfl, rfl⟩ := hsx
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp only [Bool.and_eq_true] at hi
    obtain ⟨p1, p2⟩ := forBoundsV_placed hV
    simp [placedUse, noLetCall, sexprPlaced, breakLoop, exitForLoopV, exitForTripV, exitGuard,
      plSc, exitReserved_ret, exitReserved_val, exitReserved_runName hfl, hi.1, p1, p2, b1, b2]
  case case29 r i _ _ _ hi l hh bC xb hb hfb ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp [placedUse, noLetCall, sexprPlaced, breakLoop, exitForLoopRev, exitForTripRev, exitGuard,
      plSc, exitReserved_ret, exitReserved_val, exitReserved_runName hfl, hi, b1, b2]
  case case32 r v _ hv bC xb hb ih =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨b1, b2⟩ := ih (runCtx_exitRunName hfl) hb
    simp [placedUse, noLetCall, sexprPlaced, breakLoop, exitLoop, plSc, exitReserved_ret,
      exitReserved_val, exitReserved_runName hfl, hv, b1, b2]
  case case35 hp =>
    obtain ⟨s, hs, hsx⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hsx
    obtain ⟨rfl, rfl⟩ := hsx
    exact exitStore_placed hp hs
  case case37 =>
    obtain ⟨s, hs, hsx⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hsx
    obtain ⟨rfl, rfl⟩ := hsx
    exact resultStoreT_placed hs
  case case38 e _ _ _ _ _ _ _ _ _ _ _ _ _ hs =>
    cases e <;> simp [exitStmtOk] at hs <;> simp [haxToLowCT] at h <;>
      (obtain ⟨rfl, rfl⟩ := h; simp [placedUse, noLetCall])

/-- **The typed exit front uses each name in the heap of its placement.**  A body lowered
    by `haxToLowCTFnT A` gives a program in which every non-reserved name is used only in
    the heap `A` places it in, at its placed tower type, and no binding starts with a
    call. -/
theorem haxToLowCTFnT_placedUse {A : ExitTowers} {e : ImpExpr} {c : LowCT}
    (h : haxToLowCTFnT A e = some c) : placedUse A c = true ∧ noLetCall c = true := by
  unfold haxToLowCTFnT at h
  obtain ⟨⟨c0, x⟩, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨g1, g2⟩ := haxToLowCTKT_placedUse A true (some exitFnSlot) e
    (fun r hr => Or.inr (Option.some.inj hr).symm) hk
  simp [exitFunction, placedUse, noLetCall, sexprPlaced, plSc, exitReserved_ret, exitReserved_res,
    exitReserved_val, g1, g2]

end CatCrypt.Crypto.Hax
